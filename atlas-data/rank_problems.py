"""Reproducible, evidence-aware triage of the complete catalogue. No LLM or solve calls.
Run from repository root. Exact metadata and parsed source snapshots are retained.
"""
import collections, csv, hashlib, json, re
from pathlib import Path
import sys
import yaml
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT))
from harness import known_search_floor,SEARCH_REACH   # one definition of "a witness is out of reach"
DATA=ROOT/'atlas-data'
def load(p): return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def harness_evidence():
    evidence={}
    for path in (ROOT/'runs').rglob('state.json'):
        if '.cache' in path.parts or 'current' in path.parts:continue
        try: s=load(path)
        except (ValueError,OSError):continue
        inp=s.get('problem_input') or {}; pid=inp.get('id') if isinstance(inp,dict) else None
        if not pid:
            m=re.search(r'erdos(\d+)',str(path.parent));pid=m.group(1) if m else None
        if not str(pid).isdigit():continue
        e=evidence.setdefault(int(pid),{'runs':0,'verified':0,'partial':False,'assessments':[],'failures':[]})
        e['runs']+=1
        e['verified']+=(s.get('verify') or s.get('verification') or {}).get('all_clear') is True
        e['partial']|=s.get('outcome')=='partial' or bool((s.get('program') or {}).get('certified_any'))
        if s.get('assessment'):e['assessments'].append(s['assessment'])
        if s.get('stop_reason'):e['failures'].append(str(s['stop_reason']))
    return evidence

# Library fit is a prior based on the current pipeline and recorded successes,
# not a judgment of a field's intrinsic mathematical difficulty.
AREA={
 'number theory':(5,'Arithmetic and divisibility match the existing successful proof corpus.','Use Mathlib arithmetic/factorization lemmas and exact certificates.'),
 'unit fractions':(7,'Rational identities and explicit denominators fit the harness’s witness workflow.','Search exact rational witnesses; prove positivity and distinctness separately.'),
 'factorials':(6,'Factorial identities have worked well with exact search and norm_num certificates.','Prefer small witnesses or a symbolic family; large numerical certificates can time out.'),
 'binomial coefficients':(5,'Finite sums and binomial identities have substantial library support.','Retrieve exact binomial identities before attempting broad tactic search.'),
 'divisors':(4,'Divisor and prime-factor APIs are represented in previous successful runs.','Resolve natural/integer coercions and retrieve factorization lemmas early.'),
 'polynomials':(3,'Polynomial identities have useful existing algebraic tactics.','Separate ring identities from analytic or root-distribution arguments.'),
 'combinatorics':(0,'Finite combinatorics fits decomposition, but set/cardinality bookkeeping is substantial.','Separate the combinatorial invariant from the final counting argument.'),
 'additive combinatorics':(-3,'Finite set machinery is available; global additive structure can demand deep theorems.','Identify whether an explicit finite construction settles the full quantifiers.'),
 'graph theory':(-7,'Graph encodings and extremal arguments are less represented in the harness’s verified corpus.','Build reusable graph encodings and isolate finite certificates from general graph theorems.'),
 'ramsey theory':(-9,'Ramsey statements often need nontrivial infinitary or extremal infrastructure.','Check for a matching Mathlib theorem before constructing a long combinatorial proof.'),
 'geometry':(-11,'Geometric incidence and configuration reasoning needs substantial formal setup.','Choose exact coordinates or a reusable geometric model before proof search.'),
 'analysis':(-13,'Limits, function spaces and analytic estimates create a larger formalization burden.','Freeze domains and convergence hypotheses and assemble the missing analytic lemmas.'),
 'set theory':(-18,'Set-theoretic independence and infinite-cardinal arguments do not fit the current arithmetic-heavy workflow.','Audit the foundational assumptions and relevant set-theory infrastructure first.'),
 'topology':(-15,'Topological constructions are outside the current demonstrated proof corpus.','Develop the topological definitions and reusable structural lemmas.'),
 'probability':(-9,'Probabilistic estimates need measure-theoretic setup and careful finite/infinite distinctions.','Formalize the probability space and isolate the concentration or expectation inequality.'),
 'group theory':(-5,'Algebraic structures are supported, but this harness has little direct benchmark evidence here.','Locate existing structural results and pin the exact group hypotheses.'),
}
HARD=[(r'riemann hypothesis|generalised riemann|generalized riemann','Riemann-hypothesis dependency',-16),
 (r'\babc conjecture\b|\bab[c] conjecture','abc-related dependency',-13),
 (r'szemer[eé]di|regularity lemma|hypergraph removal','Deep additive or extremal machinery',-7),
 (r'circle method|sieve method|sieve theory|exponential sum|character sum','Analytic-number-theory machinery',-9),
 (r'hausdorff|banach|hilbert space|lebesgue|measure theory','Analytic or geometric infrastructure',-7),
 (r'forcing|large cardinal|continuum hypothesis|\bzfc\b|undecidable','Foundational obstruction or dependence',-14)]
EASY=re.compile(r'(?:has|have|was|is|can be) (?:an? |quite |very |now |also |in fact )?(?:simple|easy|elementary|short|trivial) (?:proof|argument|solution|counterexample)|(?:easily|immediately) (?:follows|proved|disproved)|(?:proved|disproved|solved) (?:by |using )?(?:a |an )?(?:simple|easy|elementary|short|trivial)',re.I)

SPECIAL_CASE_RE=re.compile(r'proved (?:for|the case|when|in the case)|known (?:for|when|in the case)|verified for|'
                           r'special case|partial result|holds for all|settled for|case [a-z]\\s*=|for \\|A\\| ?[<=]',re.I)
CERTIFICATE_RE=re.compile(r'explicit (?:example|construction|witness|counterexample)|colou?ring|'
                          r'finite check|exact (?:computation|witness)|computer (?:search|verification)|brute force',re.I)

# Every problem page carries a reactions/metadata block ("Formalised statement? Yes", "Could be formalisable",
# "Working on formalising"). It is site furniture, not evidence of work, and it sits in the MIDDLE of the
# thread with real comments after it, so it is excised rather than truncated. The 'formalized' catalogue flag
# already pays for the statement existing; this block must not be allowed to pay for it a second time.
BOILERPLATE_RE=re.compile(r'When referring to this problem.*?red border\.\)',re.S)
BOILERPLATE_FIELD_RE=re.compile(r'(?:Formalised statement\?|Could be formalisable|Working on formalising)'
                                r'\s*\n\s*(?:Yes|No|None)?',re.I)

def strip_boilerplate(text):
    """Thread text with the site's own reactions/metadata furniture removed."""
    return BOILERPLATE_FIELD_RE.sub(' ',BOILERPLATE_RE.sub(' ',text or ''))

# A public formal artifact is the strongest available evidence that certified partial value is REACHABLE:
# somebody has already paid the encoding cost and the remaining gap is named. Measured 2026-09-11 over all
# 643 cached open threads, this is the signal the partial axis was missing entirely - #264 (a Formal
# Conjectures sorry that Aristotle has already used to settle two sub-cases), #20 (a Lean repo certifying
# f(1,3)..f(6,3)), #306 and #1054 (sorry-free formalizations naming their exact Mathlib gap) all sat 20-30
# points below problems whose +18 came from a regex hit on the word "partial result".
# An identified gap is what makes the artifact actionable: a sorry to fill, or a named missing Mathlib input.
FORMAL_GAP_RE=re.compile(r'sorry-free|sorries|fill in the sorry|\ba sorry\b|the sorry\b|'
                         r'axiom boundary|stated axioms?|remaining axioms?|'
                         r'not (?:yet )?(?:be )?(?:available|present|in) (?:in )?mathlib|'
                         r'do(?:es)? not appear to be available in mathlib|not yet in mathlib',re.I)


# Distinct KINDS of artifact evidence, counted separately: a problem with a repo link, a named prover run and
# a .lean file has more to build on than one that mentions Lean once. Counting kinds (not raw hits) keeps a
# single chatty commenter from outscoring a real artifact, and gives the tier a spread instead of a flat
# bonus - a flat +10 put eight problems in a new dead tie at the top of the partial axis.
ARTIFACT_KINDS=(
    ('repo',re.compile(r'github\.com/\S*lean|github\.com/\S*formal|anc/lean|\blake build\b',re.I)),
    ('project',re.compile(r'formal[- ]conjectures|formalconjectures',re.I)),
    ('prover',re.compile(r'alphaproof|aristotle',re.I)),
    ('file',re.compile(r'\blean file\b|\.lean\b|lean[- ]?4\b',re.I)),
    ('library',re.compile(r'\bmathlib\b',re.I)),
)


def formalization_evidence(text):
    """Graded evidence that a public formalization exists for this problem, and how actionable it is.

    Returns (label, points, why, requirement) or None. Scanned over boilerplate-stripped text so the site's
    own "Formalised statement? Yes" field cannot trigger it. Points scale with the number of distinct kinds
    of evidence present, and a NAMED remaining gap (an open sorry, a missing Mathlib input) is worth more
    than an artifact alone, because it is the part that says what to do next.
    """
    t=strip_boilerplate(text)
    kinds=[name for name,rx in ARTIFACT_KINDS if rx.search(t)]
    if not kinds:
        return None
    breadth=min(4,len(kinds))                 # 1..4
    kindly=f'{breadth} kind' if breadth==1 else f'{breadth} kinds'
    if FORMAL_GAP_RE.search(t):
        return (f'Public formalization with an identified gap ({kindly})',8+2*breadth,
                'A public formal artifact exists and its remaining gap is named (an open sorry, or a stated missing Mathlib input). The encoding cost is already paid and the next step is explicit.',
                'Read and build on the existing formalization; target its named gap rather than restating the problem.')
    return (f'Public formalization artifact ({kindly})',2+2*breadth,
            'A public Lean/Mathlib artifact or prover run is reported for this problem, so a faithful encoding already exists to build on.',
            'Locate the existing artifact before starting and reuse its statement; do not re-encode from the English sentence.')


def open_value(p,m,state,ctx,tags,resolved,area_points):
    """A second axis, for unsolved problems only: how much CERTIFIED PARTIAL value is reachable here?

    The main score answers "can the harness produce a complete proof", which for an open problem means new
    mathematics and is near zero for all of them. That collapses the open list into an undifferentiated tail
    and hides where the real work is. This scores what the harness can actually deliver on an open target:
    a formalized proved special case, a certifiable finite object, a reusable definition. It is a separate,
    heuristic estimate and is never added to the priority score.
    """
    if resolved or state in {'independent','not provable','not disprovable'}:
        return None
    points,notes=[],[]
    def add(label,value,why):
        points.append({'label':label,'points':value});notes.append(why)
    add('Base: certified partial results',20,'Partial value is judged on lemmas the harness could certify, not on resolving the problem.')
    if SPECIAL_CASE_RE.search(ctx):
        add('Proved special case available',18,'The discussion reports a proved special case or partial result; formalizing one is a complete, checkable contribution that does not overclaim.')
    if (m.get('formalized') or {}).get('state')=='yes':
        add('Faithful formal statement exists',8,'An external formal statement removes the encoding risk, so effort goes into the mathematics rather than the contract.')
    if CERTIFICATE_RE.search(ctx):
        add('Explicit object to certify',10,'The discussion points at an explicit construction or finite object; certifying one in Lean is small and self-contained.')
    evidence=formalization_evidence(ctx)
    if evidence:
        label,pts,why,_need=evidence
        add(label,pts,why)
    if state in {'falsifiable','verifiable','decidable'}:
        floor=known_search_floor(ctx)
        if floor and floor>SEARCH_REACH:
            add('Witness out of reach',-12,'The finite object the catalogue promises is already excluded below a bound far past any bounded search, so no certificate can be produced for it.')
        else:
            add('Reachable finite direction',8,'A finite certificate direction with no published check beyond our search range.')
    add('Library fit',max(-8,min(8,area_points)),'Reachable partial results still need the relevant Mathlib development.')
    if re.search(r'\bo\(|asymptot|density|\\lim|sufficiently large',ctx,re.I):
        add('Asymptotic core',-6,'The substance is asymptotic, so finite lemmas stay peripheral to the actual question.')
    total=max(1,min(80,sum(s['points'] for s in points)))
    return {'score':total,'signals':points,'rationale':notes}


CLAIM_RE=re.compile(r'full proof|counter-?example|refut|resolv|closes? this problem|solution to this problem',re.I)


def forum_text(pid):
    """Cached forum thread + proof-claims text for one problem, or ('','') when nothing was fetched."""
    try:
        record=json.loads((DATA/'forum'/f'{pid}.json').read_text())
    except (OSError,ValueError):
        return '',''
    return str(record.get('thread') or ''),str(record.get('claims') or '')


def assess(p,m,e,verified):
    state=p['page_status'].lower();resolved=state.startswith(('proved','disproved','solved'))
    independent=state=='independent';status='Solved' if resolved else 'Independent' if independent else 'Unsolved'
    thread,claims=forum_text(p['id'])
    # The forum carries what the main page does not: published exhaustive checks, refuted approaches, and
    # named experts calling a problem hard. It feeds the signals below; it is cached, so absent text is
    # simply an unfetched problem, never evidence of absence.
    stmt=p['statement'];ctx=p['discussion']+('\n'+thread if thread else '')
    txt=(stmt+' '+ctx).lower();tags=p['tags'];signals=[];why=[];req=[]
    def add(label,points,reason=None,need=None):
        signals.append({'label':label,'points':points})
        if reason:why.append(reason)
        if need:req.append(need)
    add('Base: known resolution' if resolved else 'Base: unresolved target',44 if resolved else 15,
        'A resolution is known; the task is to reconstruct a complete faithful formal proof.' if resolved else 'The full target remains unresolved in the catalogue; solving it requires new mathematics, not just translation.')
    if '(lean)' in state and resolved:add('External Lean proof exists',15,'The catalogue reports a Lean-verified resolution; this is external evidence, not a harness success.','Identify the reusable prerequisites without treating an external proof as an autonomous solve.')
    elif (m.get('formalized') or {}).get('state')=='yes':add('External formal statement exists',3,'An external formal statement is available; this does not establish a formal solution.')
    choices=[(t,AREA[t]) for t in tags if t in AREA]
    # Choose the most demanding main area; do not stack correlated category penalties.
    if choices:
        t,(pts,reason,need)=min(choices,key=lambda pair:pair[1][0]);add('Library fit: '+t,pts,reason,need)
    if state in {'falsifiable','verifiable','decidable'}:
        # Measured 2026-09-10: of the 15 problems in this class examined closely, ALL 15 were adjusted down,
        # mean -22. The flat bonus rewarded the existence of a finite witness while ignoring whether it is
        # reachable. It is now conditioned on the published exhaustive checks in the problem's own discussion.
        floor=known_search_floor(ctx)
        if floor and floor>SEARCH_REACH:
            add('Finite certificate proven out of reach',-14,
                f'The catalogue identifies a finite certificate direction, but the discussion already excludes any witness below ~{floor:.3g} — far past a bounded search, so the finite label promises an object that cannot be exhibited.',
                'Do not budget a counterexample search. Target a proved special case or a certificate route instead.')
        elif floor:
            add('Finite certificate, partially checked',4,
                f'The catalogue identifies a finite certificate direction and the discussion reports checks up to ~{floor:.3g}, which a bounded search can still pass.',
                'Start the search above the published check and record the range actually covered.')
        else:
            add('Catalogue finite-certificate class',9,'The catalogue identifies a finite certificate direction. It supplies no guarantee that a witness is small or within our search budget.','Set an explicit search bound and prove that any found certificate resolves the exact target.')
    if re.search(r'\binfinit|arbitrarily (?:large|long)|for all sufficiently|eventually',stmt,re.I):
        add('Unbounded quantifier',-5,'The statement involves an unbounded family or eventual behavior; finitely many checks cannot settle it.','Construct and verify a uniform argument or an infinite family.')
    if re.search(r'\\lim|\\gg|\\ll|\\sim|density|asymptot|order of magnitude|growth rate|almost all|\\to|\\infty|\bo\(',stmt,re.I):
        add('Asymptotic or density target',-9,'The target is an asymptotic/density claim; isolated examples or improved finite bounds are only partial results.','Prove the asymptotic statement with its full quantifiers and error control.')
    if re.search(r'determine|estimate|how large|how many|maximum|minimum|largest|smallest|size of|best possible',stmt,re.I):
        add('Optimality or full classification',-5,'An optimal bound or classification is requested; a single construction may cover only one direction.','Separate upper and lower bounds and check that they meet the requested precision.')
    if resolved and state.startswith('disproved') and not re.search(r'\\lim|\\gg|\\ll|density|asymptot|arbitrarily|infinit|sufficiently|almost all|\\to|\\infty|\bo\(',stmt,re.I):
        add('Potential finite counterexample',7,'A disproof may reduce to an exact counterexample; the quantifier structure still needs checking.','Extract the actual counterexample and certify every side condition.')
    if len(stmt)<180:add('Compact statement',2)
    elif len(stmt)>650:add('Long formal contract',-3,'The statement has several clauses; preserving all conditions increases formalization risk.','Audit each clause and quantifier against the original before accepting a proof.')
    easy=EASY.search(ctx)
    if resolved and easy:add('Explicit easy-proof signal',10,'The solution discussion explicitly describes an elementary or short proof route.','Check that the easy argument solves the full question, not merely a special case.')
    for pattern,label,points in HARD:
        if re.search(pattern,txt):add(label,points,'The statement or its discussion mentions '+label.lower()+'; that is a possible dependency to audit, not an assumed theorem requirement.')
    if not resolved and m.get('prize','no')!='no':add('Prize-bearing unresolved problem',-4,'An unresolved prize problem receives a conservative difficulty prior.')
    if state in {'independent','not provable','not disprovable'}:
        add('Foundational limit',-25,'The catalogue reports an independence or one-sided provability obstruction; the intended axioms are decisive.','Clarify the foundational setting. Do not claim a Lean proof of the original direction by adding an unapproved axiom.')
    if claims.strip() and CLAIM_RE.search(claims):
        add('Unverified resolution claim on the site',-8,
            'The problem carries a proof claim on its site claims page. The catalogue has not accepted it, but the target may already be settled, and the site warns that appearing there is no guarantee of correctness.',
            'Read and judge the existing claim before spending a run; if it stands, this is not an open target.')
    if not resolved and re.search(r'(?:tao|erd[oő]s|bloom|sawhney|green)\b[^.]{0,120}(?:difficult|hopeless|hard|no idea|not easy|do(?:es)? not see)',txt):
        add('Named expert reports difficulty',-6,
            'A named mathematician states in the discussion that the problem resists the obvious approaches; that is stronger evidence than a text-pattern estimate.',
            'Do not expect a short route; scope the attempt to a partial result.')
    if re.search(r'ambiguous|not clear|unclear|misstat|presumably|typo',ctx,re.I):
        add('Statement-interpretation risk',-3,'The discussion contains an ambiguity or correction signal; resolve the intended formulation before testing.','Freeze the corrected statement and record the scope choice.')
    area_points=min((AREA[x][0] for x in tags if x in AREA),default=0)
    partial=open_value(p,m,state,ctx,tags,resolved,area_points)
    harness='Verified' if p['id'] in verified else 'Partial result' if e.get('partial') or p['id']==201 else 'Attempted' if e else 'Untried'
    if e and harness!='Verified':why.append('Local activity exists, but no saved verified full solution is recorded. Triage, partial work and credit interruptions are not mathematical impossibility evidence.')
    score=max(1,min(94,sum(s['points'] for s in signals)))
    if not resolved:score=min(45,score)
    if independent:score=1
    adjustment=score-sum(s['points'] for s in signals)
    if adjustment:signals.append({'label':'Score floor / ceiling','points':adjustment})
    if harness=='Verified':
        score=99;signals=[{'label':'Saved, regression-checked full harness proof', 'points':99}]
        why=['A saved full proof passed the local Lean regression and standard-axiom audit.', 'This is demonstrated harness capability on its frozen formulation, not a calibrated probability of a fresh run.']
        req=['Replay the verified proof and preserve statement faithfulness when testing future harness changes.']
    formal='External Lean-verified resolution reported.' if '(lean)' in state and resolved else 'External formal statement reported; no completed external Lean resolution recorded.' if (m.get('formalized') or {}).get('state')=='yes' else 'No external Lean statement recorded in this metadata snapshot.'
    return {'id':p['id'],'statement':stmt,'status':status,'state':state,'tags':tags,'score':score,'harness':harness,'rationale':why,'requirements':list(dict.fromkeys(req)), 'formal':formal,'review':'Automated assessment from the complete statement, solution-context signals, catalogue metadata and available local results. Confidence is low for untested problems.','signals':signals,'partial':partial,'url':f'https://www.erdosproblems.com/{p["id"]}','manual':False,'prize':m.get('prize','no')}

def main():
    pages=load(DATA/'parsed.json');meta={int(m['number']):m for m in yaml.safe_load((DATA/'problems.yaml').read_text())}
    assert len(pages)==len(meta)==1217 and {p['id'] for p in pages}==set(meta)
    assert all(p['page_status'].lower()==meta[p['id']]['status']['state'].lower() for p in pages),'Source status mismatch; reconcile before publishing'
    evidence=harness_evidence()
    verified={int(p.stem[5:]) for p in (ROOT/'knowledge/solved').glob('Erdos*.lean') if p.with_suffix('.json').exists()}
    rows=[assess(p,meta[p['id']],evidence.get(p['id'],{}),verified) for p in pages]
    overrides=load(DATA/'reviewed.json') if (DATA/'reviewed.json').exists() else {}
    for r in rows:
        o=overrides.get(str(r['id']))
        if o:
            if r['harness']!='Verified' and 'score' in o:
                delta=o['score']-r['score'];r['signals'].append({'label':'Problem-specific manual review adjustment','points':delta});r['score']=o['score']
            r['rationale']=o.get('rationale',[])+r['rationale'];r['requirements']=o.get('requirements',[])+r['requirements'];r['manual']=True
            # The partial axis is the one that matters for an open problem (CLAUDE.md: two axes, never
            # summed), so it needs a manual-override path of its own rather than staying heuristic forever.
            if isinstance(o.get('partial'),int) and r.get('partial'):
                r['partial']=dict(r['partial'],score=o['partial'],
                                  signals=(r['partial'].get('signals') or [])+[{'label':'Manual partial-value review','points':o['partial']-r['partial'].get('score',0)}])
            # A score backed by an exact computation is a much stronger claim than a text-signal estimate,
            # so the evidence behind an override travels with it instead of being flattened into one number.
            r['assessed']={'on':o.get('assessed'),'sources':o.get('sources',[]),'searchFloor':o.get('search_floor')}
            r['review']=('Reviewed'+(f" on {o['assessed']}" if o.get('assessed') else '')
                         +' against the problem statement, source discussion'
                         +(' and recorded evidence' if o.get('sources') else '')
                         +'; this remains a tractability estimate, not a solve attempt.')
    # Plain-language brief: one markdown file per problem, written by a run (stage_brief) or by hand.
    # It travels with the row into rankings.json and the site's data.json, so the problem page can show a
    # human- and AI-readable account of what the problem asks and what we actually found.
    for r in rows:
        bf=DATA/'briefs'/f"{r['id']}.md"
        if bf.exists():
            try:r['brief']=bf.read_text()
            except OSError:pass
    rows.sort(key=lambda r:(-r['score'],r['id']))
    for i,r in enumerate(rows):
        r['rank']=i+1;r['tier']='Demonstrated' if r['harness']=='Verified' else 'Promising' if r['score']>=70 else 'Plausible' if r['score']>=50 else 'Difficult' if r['score']>=30 else 'Research' if r['score']>=15 else 'Frontier'
    result={'meta':{'total':len(rows),'snapshot':'2026-09-09','preview':False,'method':'v1: evidence-aware heuristic; scores are NOT probabilities; ties ordered by problem number.','manually_reviewed':len(overrides),'sources':[{'url':'https://www.erdosproblems.com/range/1-1217','sha256':sha(DATA/'all-problems.html')},{'url':'https://raw.githubusercontent.com/teorth/erdosproblems/main/data/problems.yaml','sha256':sha(DATA/'problems.yaml')}],'harness_sha256':sha(ROOT/'harness.py'),'scorer_sha256':sha(Path(__file__)),'manual_reviews_sha256':sha(DATA/'reviewed.json')},'problems':rows}
    (DATA/'rankings.json').write_text(json.dumps(result,ensure_ascii=False,indent=2))
    # Standalone private-site data contains no local paths, private transcripts or credentials.
    (ROOT/'erdos-atlas/app/data.json').write_text(json.dumps(result,ensure_ascii=False,separators=(',',':')))
    with (DATA/'rankings.csv').open('w',newline='') as f:
        w=csv.writer(f);w.writerow(['rank','problem','score','tier','catalogue_status','harness','categories','statement','rationale','requirements','source'])
        for r in rows:w.writerow([r['rank'],r['id'],r['score'],r['tier'],r['status'],r['harness'],'; '.join(r['tags']),r['statement'],' | '.join(r['rationale']),' | '.join(r['requirements']),r['url']])
    print(collections.Counter(r['status'] for r in rows));print(collections.Counter(r['tier'] for r in rows));print('Top new targets:')
    for r in [r for r in rows if r['harness']!='Verified'][:60]:print(r['rank'],r['id'],r['score'],r['status'],r['tags'],r['statement'][:160])
    print('OPEN:')
    for r in [r for r in rows if r['status']=='Unsolved'][:50]:print(r['rank'],r['id'],r['score'],r['statement'][:180])
if __name__=='__main__':main()
