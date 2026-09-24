# cdis-lean

Lean 4 formalization of the probability chapters of CDIS, the Mines Paris course
(Boisgérault, Romary, Chautru, Bernard, Stoltz; [source](https://github.com/boisgera/CDIS),
CC BY-NC-SA 4.0), written as a contribution to
[ATLAS](https://github.com/facebookresearch/atlas-lean).

Focus: what Mathlib and ATLAS do not have yet, mainly the simulation chapter (inversion
method, rejection method, Box-Muller, importance sampling) and conditional laws.

| Folder | Content |
|---|---|
| `CdisLean/ChapterV/` | simulation |
| `CdisLean/ChapterIII/` | conditional densities, conditional laws, conditional expectation |
| `CdisLean/ChapterI/`, `ChapterII/`, `ChapterIV/` | distribution functions, covariance matrix, multivariate CLT, continuity of convergence |
| `CdisLean/Bridges/` | course statements proved from existing Mathlib results |
| `CdisLean/Check.lean` | every Mathlib declaration the course relies on, checked at build time |
| `blueprint/` | autoform roadmap, one article per course statement |

Three statements of the course are false as written (Markov and Chebyshev for `a < 0`,
importance sampling without a support condition); the counterexamples are in the Lean files.

Build with Lean 4.34.0 and Mathlib v4.34.0:

```bash
lake exe cache get && lake build
```

`lake build CdisLeanTest` checks that every `CDIS` declaration uses only the standard axioms
(no `sorry`). `Exercises/` holds statements left to prove, outside the main library.
