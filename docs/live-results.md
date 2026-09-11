# Live results publication

The harness exports `result-summary.json` beside each saved state. A local background publisher watches all run state, log, completion, and review files every 30 seconds, including older harness versions and concurrent runs. Fast saved-proof regression tests now also emit per-problem records (pass/fail); they do not count as new autonomous solutions. Use `harness.py regress --only 399` to replay one saved proof. It sends only changed summaries to the private Atlas. Existing runs are backfilled once. Failed requests remain unacknowledged and retry automatically; successful batches are checkpointed locally. Duplicate or older updates cannot overwrite newer server records.

The site reads its persistent database every 30 seconds without rebuilding. It shows recent runs, total counts, outcome, last activity, review milestones, and candidate/partial/verified evidence. Old automatic checks are explicitly legacy evidence, never independent review. Catalogue status and priority estimates remain their dated assessment. A new failure does not remove prior successful evidence. Two minutes without publisher contact is visibly stale. A run labelled running means its last recorded state, not proof that its process is still alive.

Only allowlisted identifiers, timestamps, enums and evidence flags/hashes leave this machine. No statements, proofs, prompts, raw errors, local paths, reviewer names or credentials are included. The site's existing owner-private access remains unchanged. Writes additionally require a dedicated ingest secret. Local publisher credentials and acknowledgements live under `.result-feed/`, excluded from source control and restricted to this user. Authentication redirects are rejected to avoid forwarding credentials to another destination.

## Live priority scores

Catalogue status stays a dated snapshot, but priority scores no longer do. When a finding is recorded with
`atlas-data/record_finding.py`, the ranker regenerates `rankings.json` and the publisher sends every reviewed
problem's score, reasons and requirements alongside the run summaries. The page overlays them on the build's
baked data, re-sorts by score and recomputes tiers with the ranker's own thresholds, so one changed score
cannot desynchronize rank from score. Rank and tier are never published, only derived.

Only the manually reviewed set is sent: those are exactly the problems whose score has been revised since the
last build, they are few, and each carries its reasoning. Revisions are keyed by a content hash, so
republishing unchanged data is a no-op and the server keeps the newer revision, as it does for runs.

A site built before this feature rejects the extra field. The publisher treats that 400 as "not deployed
yet": run summaries still publish, score revisions stay queued, and `pending_scores` in
`.result-feed/status.json` reports how many are waiting. After the site is rebuilt and deployed, the next
poll sends them with no further action.

## Operation

`python3 result_feed.py sync` publishes once. `python3 result_feed.py watch` watches continuously. On this Mac a user LaunchAgent named `com.erdos-harness.results-publisher` starts at login and restarts the watcher if it exits. A single-process lock prevents overlapping publishers. `.result-feed/status.json` records last success or a sanitized error class/status. No model credits are used. Publisher code changes trigger a restart and resynchronization; publication format changes cannot be hidden by earlier acknowledgements.

The Mac must be awake, logged in and online for newly written local results to reach the site. The hosted site and earlier results remain available when it is offline; it catches up when the publisher returns. For runs produced elsewhere, run a separately configured publisher on that host with an authorized private-site credential. Git repository write tokens are not used for runtime publication. If site access credentials are revoked/rotated, update the local publisher credential; it will retain pending work and report a disconnected state meanwhile.

Stop with `launchctl bootout gui/$(id -u)/com.erdos-harness.results-publisher`; disable automatic restart by removing its matching LaunchAgent plist. No scheduled Codex/model task is involved. Do not commit `.result-feed`.

## Verification

Python tests exercise allowlisting, offline retry/acknowledgement, restart/crash handling, and rejection of non-catalogue IDs. Site tests exercise schema validation, candidate versus solved labels, preservation of historical success, and sublemma scope. Production verification includes authorized ingestion/readback and unauthorized write rejection. Run completion does not certify mathematical correctness beyond the explicit recorded milestones.
