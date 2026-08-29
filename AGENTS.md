# AGENTS.md

## Lean Work Must Run On The NUC

All Lean work for this repository must happen on the NUC.

This includes:

- creating or editing Lean source files
- running `lean`, `lake`, `elan`, or any Lean-related scripts
- building the project or its dependencies
- running tests, checks, formatters, linters, or benchmarks
- generating, updating, or validating Lean-derived artifacts

Do not perform Lean work on the local machine, even for a quick check. Use the
repository checkout and Lean toolchain on the NUC. The local checkout may be
used only for non-Lean coordination or documentation work.

If the NUC is unavailable or its repository/toolchain is not ready, stop and
report that blocker instead of falling back to local Lean work.
