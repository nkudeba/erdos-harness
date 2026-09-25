# Idea notes: time-split train items

These notes are the judge's reference for the idea-hit metric. Each `<n>.md` states the key idea of one problem's published resolution, so that a blind judge can score whether a run's notes found it.

They are evaluation-only and must never be shown to the harness under test. No prompt, stage, lesson store, lemma store or brief may read this directory.

They cover the 15 train items only. Dev and test solutions must not inform harness design, and a note on a dev or test item would carry its solution into every harness change gated on it.

Every note has these sections, in this order: `# <n>` with a one-line plain statement; `**Answer:**` true or false, taken from pool.json's answer field; `**Sources:**`; `**Key idea:**` (2–5 sentences); `**Main steps:**` (3–6 bullets); `**A hit looks like:**`; `**A partial hit looks like:**`; and `**Confidence:**` high, medium or low, with the reason.

Everything in them comes from the published record: pool.json, the cached problem page, the forum thread and proof-claims page, and the cited papers or write-ups. Nothing comes from the harness's own runs.

When a resolution's method cannot be found, the note says `route unknown` and lists what was checked. "Route unknown" beats a guess, because a wrong reference is worse than none. At present every item has a route, but 1179 is known only at the level of a citation: the method inside Erdős–Hall (1976) is route unknown.
