"""Private, allowlisted run summaries and retryable live-site publishing.
No model calls. A watcher also captures legacy harnesses, crashes and concurrent runs.
"""
import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import time
import urllib.request
import urllib.error
import urllib.parse
from solution_review import milestones, environment_snapshot, load_attestations
ROOT=Path(__file__).resolve().parent
LOCAL=ROOT/'.result-feed'
OUTCOMES={'regression_passed','regression_failed','running','proved','proved_unverified','not_proved','partial','budget_exhausted','budget_exhausted+partial','infrastructure_error','completed','stopped','unknown'}


def read_json(path, default=None):
    try:return json.loads(path.read_text())
    except (OSError,ValueError):return default


def atomic(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    tmp=path.with_name(path.name+f'.{os.getpid()}.tmp')
    tmp.write_text(json.dumps(value));tmp.replace(path)


def signature(run, root=ROOT):
    files=[run/n for n in ('state.json','log.jsonl','DONE','review-attestations.json')]
    files += [root/'result_feed.py']
    files += [root/'formal'/n for n in ('lean-toolchain','lake-manifest.json','lakefile.toml','lakefile.lean')]
    for record in load_attestations(run):
        if isinstance(record,dict) and isinstance(record.get('evidence'),str):files.append(Path(record['evidence']))
    return [(p.stat().st_mtime_ns if p.exists() else 0) for p in files]


def summarize(run, root=ROOT):
    state=read_json(run/'state.json',{})
    if not isinstance(state,dict):return None
    problem=state.get('problem_input') or {}
    pid=problem.get('id')
    if not str(pid).isdigit():
        m=re.search(r'erdos(\d+)',str(run.relative_to(root/'runs')));pid=m.group(1) if m else None
    if not str(pid).isdigit() or not 1<=int(pid)<=1217:return None
    last={}
    try:
        with (run/'log.jsonl').open('rb') as f:
            f.seek(max(0,f.seek(0,2)-65536));tail=f.read().decode(errors='replace').splitlines()
        for line in reversed(tail):
            try:last=json.loads(line);break
            except ValueError:continue
    except OSError:pass
    done=read_json(run/'DONE',{}) or {}
    times=signature(run,root);updated=max(times[:4]);revision=max(times)
    outcome=state.get('outcome','unknown')
    # A new invocation after DONE must not display an earlier terminal result as current.
    if times[1]>times[2] and last.get('event') not in ('end','fatal'):
        outcome='running'
    elif done.get('fatal') or last.get('event')=='fatal':outcome='infrastructure_error'
    elif outcome not in OUTCOMES:outcome='completed' if done else 'unknown'
    elif outcome=='unknown' and done:outcome='completed'
    review={}
    context=state.get('review_context')
    if context and isinstance(context.get('imports'),list):
        review=milestones(problem,state,context['imports'],environment_snapshot(root/'formal'),load_attestations(run))
    v=state.get('verify') or {};stage=review.get('stage')
    if not stage:stage='legacy_automated_verification' if v.get('all_clear') is True else 'candidate_solution' if state.get('proof') else 'no_candidate'
    direction=state.get('direction') or ''
    if direction not in ('','pos','neg','program'):direction=''
    phase=re.sub(r'[^a-zA-Z0-9_/-]','',str(last.get('stage',''))+'/'+str(last.get('event','')))[:80]
    return {'id':hashlib.sha256(str(run.resolve()).encode()).hexdigest(),'problem':int(pid),'revision':str(revision).zfill(20),
            'updatedAt':dt.datetime.fromtimestamp(updated/1e9,dt.timezone.utc).isoformat(timespec='milliseconds').replace('+00:00','Z'),
            'outcome':outcome,'phase':phase,'direction':direction,'stage':stage,
            'mechanical':review.get('mechanically_verified') is True,'faithful':v.get('faithful',{}).get('faithful') is True,
            'claimEligible':review.get('resolution_claim_eligible') is True,
            'partial':bool(state.get('partial') or (state.get('program') or {}).get('certified_any') or outcome=='partial' or (state.get('construct') or {}).get('status')=='certified'),
            'artifact':review.get('artifact_sha256')}


def export_run(run):
    """Local only; publishing outages must never interrupt a proof run."""
    try:
        row=summarize(run)
        if row:atomic(run/'result-summary.json',{'schemaVersion':1,'run':row})
    except (OSError,ValueError,TypeError,AttributeError):pass


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs):return None


def ranking_rows(root=ROOT):
    """Priority-score revisions to overlay on the site's baked snapshot.

    Only the manually reviewed set is published: those are exactly the problems whose score the harness has
    revised since the last build, they are few, and each carries the reasoning behind the revision. Scores
    come from rankings.json (post-ranker), so a newly verified proof or a recorded finding both show up.
    """
    ranked=read_json(root/'atlas-data'/'rankings.json')
    reviewed=read_json(root/'atlas-data'/'reviewed.json',{}) or {}
    # A plain-language brief is publishable on its own: a run can write one for a problem nobody has
    # manually reviewed, and it should reach the page on the same 30-second channel as a score revision.
    briefed={int(f.stem) for f in (root/'atlas-data'/'briefs').glob('*.md') if f.stem.isdigit()}
    if not ranked or not (reviewed or briefed):return []
    by_id={int(r['id']):r for r in ranked.get('problems',[])}
    stamp=dt.datetime.now(dt.timezone.utc)
    rows=[]
    for pid in sorted({int(k) for k in reviewed}|briefed):
        row=by_id.get(pid)
        if not row or not isinstance(row.get('score'),int) or not 1<=row['score']<=99:continue
        prose=lambda key:[s for s in (row.get(key) or []) if isinstance(s,str) and 0<len(s)<=600][:12]
        brief=row.get('brief') if isinstance(row.get('brief'),str) else None
        if brief and len(brief)>20000:brief=brief[:20000]
        rows.append({'problem':pid,
                     # Content-derived revision: republishing unchanged data cannot bump a row, and the
                     # server keeps the newer revision, so batches are idempotent and order-independent.
                     'revision':str(int(stamp.strftime('%Y%m%d%H%M%S'))*10**6+int(hashlib.sha256(
                         json.dumps([row['score'],prose('rationale'),prose('requirements'),
                                     (row.get('partial') or {}).get('score'),brief],sort_keys=True).encode()
                     ).hexdigest()[:6],16)%10**6).zfill(20),
                     'updatedAt':stamp.strftime('%Y-%m-%dT%H:%M:%S.')+f'{stamp.microsecond//1000:03d}Z',
                     'score':row['score'],'rationale':prose('rationale'),'requirements':prose('requirements'),
                     'partialScore':(row.get('partial') or {}).get('score'),'brief':brief})
    return rows


def post(config,body):
    url=config['url']
    if not url.startswith('https://') or urllib.parse.urlparse(url).hostname!=config['host']:raise ValueError('Publisher destination mismatch')
    req=urllib.request.Request(url,json.dumps(body).encode(),method='POST',headers={
        'Content-Type':'application/json','X-Results-Key':config['ingest_key'],
        'OAI-Sites-Authorization':'Bearer '+config['dispatch_token']})
    with urllib.request.build_opener(NoRedirect).open(req,timeout=20) as response:
        return json.load(response)


def upload(config,rows,rankings=()):
    """Publish run summaries, and score revisions when the deployed site understands them.

    A site built before live rankings rejects the extra field outright, so a 400 is treated as "not
    deployed yet": the runs go up on their own and rankings are retried later. That keeps run publishing
    working across the deploy, and score publishing starts by itself once the new build is live.
    """
    rankings=list(rankings)
    if rankings:
        try:
            result=post(config,{'schemaVersion':1,'runs':rows,'rankings':rankings})
            if result.get('accepted')!=len(rows) or result.get('rankings')!=len(rankings):raise ValueError('Unexpected acknowledgement')
            return True
        except urllib.error.HTTPError as e:
            if e.code!=400:raise
    result=post(config,{'schemaVersion':1,'runs':rows})
    if result.get('accepted')!=len(rows):raise ValueError('Unexpected acknowledgement')
    return not rankings


def sync(root=ROOT,local=LOCAL):
    config=read_json(local/'config.json')
    if not config:raise ValueError('Publisher not configured')
    ack=read_json(local/'ack.json',{}) or {};changed=[]
    for state in (root/'runs').rglob('state.json'):
        run=state.parent
        if state.is_symlink() or 'current' in run.parts or '.cache' in run.parts:continue
        key=str(run.resolve());sig=signature(run,root)
        if ack.get(key)==sig:continue
        try:row=summarize(run,root)
        except (ValueError,TypeError,AttributeError,OSError):continue
        if row:changed.append((key,sig,row))
    # Score revisions ride the same channel; only rows whose content changed are sent.
    published=ack.get('__rankings__',{}) if isinstance(ack.get('__rankings__'),dict) else {}
    revised=[r for r in ranking_rows(root) if published.get(str(r['problem']))!=r['revision'][-6:]]
    batches=[changed[i:i+100] for i in range(0,len(changed),100)] or [[]]
    accepted=0
    for i,batch in enumerate(batches):
        chunk=revised[:50] if i==0 else []
        took=upload(config,[x[2] for x in batch],chunk)
        for key,sig,row in batch:ack[key]=sig
        if chunk and took:
            for r in chunk:published[str(r['problem'])]=r['revision'][-6:]
            ack['__rankings__']=published;accepted+=len(chunk)
        atomic(local/'ack.json',ack)
    if accepted or not revised[:50]:
        for chunk in [revised[i:i+50] for i in range(50,len(revised),50)]:
            if not upload(config,[],chunk):break
            for r in chunk:published[str(r['problem'])]=r['revision'][-6:]
            ack['__rankings__']=published;accepted+=len(chunk);atomic(local/'ack.json',ack)
    atomic(local/'status.json',{'last_success':dt.datetime.now(dt.timezone.utc).isoformat(),'changed_runs':len(changed),
                                'revised_scores':accepted,'pending_scores':len(revised)-accepted,'error':None})
    return len(changed)


def main():
    p=argparse.ArgumentParser();p.add_argument('mode',choices=['sync','watch']);p.add_argument('--interval',type=int,default=30);a=p.parse_args()
    # One uploader owns the acknowledgements; concurrent harnesses only write their own states.
    import fcntl
    LOCAL.mkdir(exist_ok=True)
    lock=(LOCAL/'publisher.lock').open('w')
    try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:return
    code_mtime=Path(__file__).stat().st_mtime_ns
    while True:
        if Path(__file__).stat().st_mtime_ns != code_mtime:
            import sys
            os.execv(sys.executable,[sys.executable,str(Path(__file__).resolve()),*sys.argv[1:]])
        try:
            n=sync();revised=(read_json(LOCAL/'status.json',{}) or {}).get('revised_scores',0)
            print(f'Published {n} changed run summaries'+(f' and {revised} revised scores' if revised else ''),flush=True)
        except Exception as e:
            # Never print exception messages, response bodies, or request headers with credentials.
            atomic(LOCAL/'status.json',{'error':type(e).__name__,'http_status':getattr(e,'code',None),'at':dt.datetime.now(dt.timezone.utc).isoformat()})
            print('Publisher unavailable; results retained locally for retry',flush=True)
            if a.mode=='sync':raise SystemExit(1)
        if a.mode=='sync':break
        time.sleep(max(5,a.interval))

if __name__=='__main__':main()
