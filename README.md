# Erdős 676 — a complete negative answer

This project contains the mathematical paper and a complete Lean proof of the prime-only representation question recorded as **Erdős problem 676** and **JSP-000549**.

For infinitely many natural numbers `n`, there are no natural numbers `a`, `p`, `b` with `p` prime, `1 ≤ a`, `b < p`, and `n = a * p² + b`. The formalization also proves a constant `c > 0` such that every sufficiently large integral dyadic interval `(X, 2X]` contains at least `c X / log X` exceptions. The paper proves the matching upper order as well.

## Paper and authors

[Read the paper](paper/erdos676.pdf). Its editable source is [paper/erdos676.tex](paper/erdos676.tex).

Will Howe (`H0W4RD-dev`), Grant Huffman (`Ghuffy1`), Jensen Kohlmeyer (`JENW1N`), and Liam Kruer (`lkruer`) receive equal contribution credit. The paper lists authors alphabetically by surname. Ghuffy1 is the intended repository owner and primary submission contact. [Authorship and AI assistance](AUTHORS.md).

## Exact targets

| Declaration | Location | Conclusion |
| --- | --- | --- |
| `Erdos676.erdos676_negative` | [ExactStatement.lean](Erdos676/ExactStatement.lean) | Negates the original eventual representation assertion, with the positive multiplier and zero-inclusive remainder range |
| `Erdos676.erdos676_infinite_exceptions` | [ExactStatement.lean](Erdos676/ExactStatement.lean) | The exceptional set is infinite |
| `Erdos676.full_quantitative_disproof` | [FullDisproof.lean](Erdos676/FullDisproof.lean) | At least `c X / log X` exceptions in every sufficiently large integral dyadic interval |
| `JSP000549.original_question_negative` | [SubmissionAudit.lean](audit/SubmissionAudit.lean) | An independent restatement of the exact JSP question is false |

[STATEMENT.md](STATEMENT.md) maps every condition of the original question to the formal statements. The all-integer-modulus variant and normalized-remainder questions are separate problems.

## Reproduce

Install the official Lean toolchain specified in [lean-toolchain](lean-toolchain). The project uses **Lean 4.34.0** and mathlib commit **5ed2965256430c3649e86755f9576b54eca72435**. All transitive package revisions are fixed in [lake-manifest.json](lake-manifest.json).

From a fresh checkout, run

```sh
lake exe cache get
lake build
lake build +Erdos676.ExactStatement +Erdos676.FullDisproof +SubmissionAudit
lake env lean audit/SubmissionAudit.lean
```

The default build includes every project proof module, the vendored prerequisites, and the statement audit. The mathematical source contains no incomplete proof placeholders or project-declared mathematical axioms. Target axiom audits must list only `propext`, `Classical.choice`, and `Quot.sound`.

For a logged build and target audit, run

```sh
python3 scripts/verify.py --output verification/local
```

To add the bundled kernel replay, run

```sh
python3 scripts/verify.py --output verification/local-replay --replay
```

The replay uses the same Lean kernel from a fresh environment. It is distinct from an independently implemented external checker. The full dependency replay can require substantially more memory and time than the source build. [REPRODUCIBILITY.md](REPRODUCIBILITY.md) describes the build, trust boundaries, and evidence policy.

## Dependencies and licenses

Original proof code is Apache-2.0. The paper and original prose are CC BY 4.0 upon authorized release. Third-party sources retain their original copyright and license notices. [NOTICE](NOTICE), [LICENSE](LICENSE), [LICENSE-PAPER](LICENSE-PAPER), and [provenance/vendor.json](provenance/vendor.json) record the details.

The Mertens development and its required LeanArchitect modules are vendored at fixed upstream revisions. The project does not require access to a contributor's local drive layout. The CI workflow runs the same public build commands.

## Submission status

This is the original proof repository for the combined mathematical-solution and formalization submission to JSP-000549. Ghuffy1 owns the repository and serves as primary submitting contact. All four authors receive equal credit, as recorded in [AUTHORS.md](AUTHORS.md).

The selected proof revision `e1e7e9155488dc5d868b5c4cd00e1929f261d7dc` passed a fresh source build, six target and statement-bridge axiom checks, and two fresh bundled-kernel replays. The [initial report](verification/report.md) and [final review](verification/final-review.md) retain the evidence and its exact scope.

JSP mathematical review, attribution, identity, priority and award decisions remain pending. Individual contributors complete their own claims and confirmations through the prize process.
