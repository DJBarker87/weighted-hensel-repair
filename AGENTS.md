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

## Reuse Existing Formal Work

Reuse as much mathematically relevant work from the existing Aspis Lean
development as possible. Copying and adapting generic definitions, theorem
statements, and proofs is preferred to reproving them from scratch. The new
repository must still import only Mathlib and must not depend on Aspis or carry
over its application-specific API, protocol assumptions, or oracle theorems.

## Resource Stop Gates

Build the smallest relevant Lean target and monitor it. Interrupt and refactor
early if a target makes no useful progress for about 90 seconds or a Lean
process approaches 8 GiB RSS. Split large declarations, reduce imports, or use
a cheaper equivalent formulation before retrying. Do not let an obviously hot
or stalled build continue merely in the hope that it will finish.
