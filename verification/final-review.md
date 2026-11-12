# Final submission verification

The selected proof revision `e1e7e9155488dc5d868b5c4cd00e1929f261d7dc` passed a second full project build, explicit theorem-module checks, all six literal-statement and transitive-axiom audits, and another bundled-kernel replay in a fresh environment. Every command completed with exit code zero. The final axiom footprint contains only `propext`, `Classical.choice` and `Quot.sound`.

The [initial fresh-build report](report.md) records the earlier source rebuild with no project outputs present. The final run reused that checked build directory and repeated the project build and fresh kernel replay. [Final command results](release/run.json) record the exact times, source hashes, exit codes and log hashes. The mathematical source and pinned build configuration were unchanged throughout both runs.

The paper is supplied at revision `3cc60a9fa3b811c10732dcc435f7fe21e0d54cab`. That revision corrects the introduction's attribution of the 1979 logarithmic upper bound. Its nine-page PDF was re-rendered and checked. The formal proof remains pinned to the revision above.

## Final submission review

- The original prime-only question is fully covered, including a positive multiplier and zero remainder. The paper proves the two-sided exceptional-count estimate, and the formal lower bound establishes the complete negative answer.
- The current official rules were fetched again at awards revision `b1bfe454d37db2838ef76756830aeb23c40de95e`. The applicable process is the legacy catalog-reference PR.
- Only Current status, Lean proof, Attribution basis and Publication details change in the one JSP-000549 catalog entry. Eligibility and the index remain for maintainer review.
- Ghuffy1 is the authorized repository owner and submitting account. H0W4RD-dev, Ghuffy1, JENW1N and lkruer are all equally credited. The four public accounts exist. Individual authorship and identity confirmations remain part of JSP review.
- The source includes the complete paper, pinned dependency records, original-source notices, licenses, build instructions and AI disclosure.
- The earlier project-history scan checked 195 Git blobs and found no credential-pattern matches. The release evidence contains command output and source hashes.

## Related registrations

[PR #5156](https://github.com/TheJustinSunPrize/awards/pull/5156) was closed after the maintainer identified that its pinned source proves a statement about a double-star Ramsey problem numbered Erdős 549. It follows [PR #4285](https://github.com/TheJustinSunPrize/awards/pull/4285), also closed. [PR #3539](https://github.com/TheJustinSunPrize/awards/pull/3539) contains finite elementary arithmetic checks. All three were unmerged when reviewed. This submission addresses the full prime-square representation question recorded as JSP-000549 and Erdős 676.

## Review status

These are contributor self-checks. The bundled-kernel replay uses Lean's kernel. An independently implemented external checker has not been run. JSP mathematical acceptance, contribution attribution, identity, priority and award decisions remain pending.

Recorded at 2026-11-12T04:13:25.367372+00:00.
