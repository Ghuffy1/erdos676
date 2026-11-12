# Reproducibility and trust

## Fixed inputs

The toolchain is `leanprover/lean4:v4.34.0`. The official release identifies Lean commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.

The fixed mathlib revision is `5ed2965256430c3649e86755f9576b54eca72435`. The package lock includes its eight transitive package revisions. Vendored prerequisites come from PrimeNumberTheoremAnd revision `c39a751132c88b6e8080b74c74023fd95b3d8be0` and LeanArchitect revision `468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`.

## Fresh source build

Use an empty checkout without project build outputs. `lake exe cache get` obtains the matching mathlib cache. `lake build` then elaborates all project and vendored source modules. The cache step does not supply compiled versions of this project's proof modules.

Use `lake env lean audit/SubmissionAudit.lean` to check the literal original-question bridge and print the target types and axioms. `Erdos676/Audit.lean` contains the broader collection of intermediate theorem axiom checks. Both are included in the default build.

On Windows, `python scripts/verify.py --lake PATH_TO_OFFICIAL_LAKE --output verification/local` supports a direct official Lake executable. The script captures complete command output, compiler and source hashes, the selected Git revision, and source immutability checks. Python is used for recording the verification evidence; mathematical proof checking is performed by Lean.

## Verification levels

1. **Statement review** compares every original quantifier and arithmetic condition against the literal audit target.
2. **Source elaboration** rebuilds the mathematical project and its vendored prerequisite sources under the pinned toolchain.
3. **Axiom inspection** checks transitive dependencies of the complete target and statement bridges. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
4. **Kernel replay**, when recorded as completed, uses `lake env leanchecker --fresh Erdos676.ExactStatement` to replay the target's imported declarations into a fresh environment using the bundled kernel.

An independently implemented external checker is an additional verification level. It is only claimed if its actual result is present in the evidence. A source build, a replay, and an external checker are distinct checks.

## Evidence and immutable revisions

A verification report identifies the full 40-character proof commit it checked. Reports committed later can describe that earlier proof revision without changing the selected proof. Recheck after any mathematical source, toolchain, or dependency change.

Local preparation can reuse a trusted matching dependency cache. The report records the actual dependency revisions and whether project outputs were absent before the build. Operating-system sandboxing and independent mathematical review are reported according to what was actually performed.

## Paper build

The paper source uses the standard `amsart` class and the `geometry`, `amsmath`, `amssymb`, `mathtools`, `microtype`, and `hyperref` packages. Build it with a current TeX distribution, or run `tectonic paper/erdos676.tex`. The checked PDF in `paper/` is the submitted mathematical exposition.
