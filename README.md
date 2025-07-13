Twin Primes Sieve Proof (Lean 4)
# Twin Primes Sieve Proof (Lean 4)

[![Build Status](https://github.com/kewowski/twin-primes-proof/actions/workflows/ci.yml/badge.svg)](https://github.com/kewowski/twin-primes-proof/actions/workflows/ci.yml)
[![Uses mathlib4](https://img.shields.io/badge/Uses-mathlib4-blue?logo=leanpub)](https://github.com/leanprover-community/mathlib4)
[![Lean version](https://img.shields.io/badge/Lean-4.21.0-blue)](https://leanprover.github.io/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
This repository contains a complete formalization in Lean 4 of a contradiction-based proof of the Twin Prime Conjecture using Selberg sieve weights. The entire argument is constructive, elementary, and verifiable using the Lean proof assistant.

Repository Structure
TwinPrimes/ – contains all verified Lean 4 modules, including:

Main.lean – imports and coordinates the formal proof.

SelbergWeights.lean – defines the Selberg sieve weights.

TwinWeight.lean – formalizes the twin prime weighted sum.

LowerBound.lean – proves the lower bound on twin weights.

UpperBound.lean – proves the upper bound on all weights.

Contradiction.lean – concludes the contradiction argument.

lakefile.lean – project manifest (Lean + Mathlib 4).

lean-toolchain – pinned Lean version used for builds.

.github/workflows/ – CI build pipeline for automated verification.

docs/ – contains the full write-up:

Main manuscript

Companion paper (Lean formalization details)

Explanatory note (bridging sieve theory and Lean)

Getting Started (GitHub Codespaces)
To run this project in-browser with no setup:

Click the green Code button above.

Select the Codespaces tab.

Click Create codespace.

Once the Codespace opens, build the project with:

lake build

This compiles and verifies the entire formalization using Lean 4 and Mathlib.

Build Requirements (Local)
elan – Lean version manager

lake – Lean build system (installed with elan)

lean-toolchain – auto-selects Lean 4.21.0

Build with:

lake clean
lake update
lake build

Notes
No sorry, axiom, or unproven placeholder is used.

The proof avoids reliance on Chen’s theorem or unformalized heuristics.

All modules compile under Lean 4.21.0 with Mathlib 4.

References
See the /docs/ directory for:

The main manuscript

The Lean companion paper

The explanatory note bridging sieve theory and formal logic

## License

This project is licensed under the [MIT License](LICENSE).
