# Trust and source audit

The final proof targets are checked for their transitive axiom dependencies. The intended result is the standard classical footprint `propext`, `Classical.choice`, and `Quot.sound`.

The original mathematical proof modules contain no uses of `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool`, or `debug.skipKernelTC`.

The vendored LeanArchitect package defines a `sorry_using` tactic and metadata-export helpers. Its `runEnvOfImports` helper sets `debug.skipKernelTC` while generating blueprint metadata. These are upstream tool definitions. The mathematical proof and its vendored Mertens development do not invoke `sorry_using`, `runEnvOfImports`, `latexOutputOfImportModule`, or `jsonOfImportModule`. The final transitive axiom audit and the recorded kernel checks determine the proof's actual trust footprint.

Vendored source bytes and upstream revisions are recorded in `provenance/vendor.json`. This package preserves those sources and licenses to make these facts inspectable.

The verification harness is automation for executing commands and collecting their outputs. Its success status is supporting evidence. The literal statement bridge, actual compiler results, and transitive axiom output remain the relevant mathematical checks.
