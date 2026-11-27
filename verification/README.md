# Build record for the paper

Paper: J. C. Kerr, *A Gaussian form of Weil's positivity criterion for the Riemann hypothesis*,
DOI [10.5281/zenodo.24578253](https://doi.org/10.5281/zenodo.24578253).

| | |
|---|---|
| Lean sources | commit `a73eeae6e26c341676f0620ae16806063e2e8bf5` of this repository (the Lean files are unchanged since the first commit `2b40881`) |
| Lean | 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), official release, arm64 macOS |
| Mathlib | `v4.35.0`, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`; other dependencies as pinned in `lake-manifest.json` |
| Command | `lake build FleetPrimePoleBoundRH FleetHeatPositivityRH FleetTwoPointConvexity FleetPrimeOnlyRH` |
| Result | `Build completed successfully (9166 jobs)`, 2026-11-27 |

The project modules were compiled from source; Mathlib and the other dependencies were taken from
their prebuilt object files at the pinned revisions.

Files:

- `build.log` — full output of the command above.
- `PaperAxioms.lean` — prints the statement and the axioms of each theorem cited in the paper.
- `axioms.txt` — its output: every cited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

| Statement in the paper | Lean theorem |
|---|---|
| Explicit formula for Gaussians (1) | `FleetPrimePoleBoundRH.zero_trace_eq_rhs` |
| Theorem 1, zero side | `FleetHeatPositivityRH.RH_iff_heat_positivity` |
| Theorem 1, arithmetic side | `FleetHeatPositivityRH.RH_iff_rhs_positivity` |
| Corollary 2 | `FleetTwoPointConvexity.RH_iff_twoPoint` (the existence of a point with positive value is a hypothesis) |
| Theorem 3 | `FleetPrimeOnlyRH.RH_iff_primeOnly_bound` |

To reproduce:

```bash
lake exe cache get
lake build FleetPrimePoleBoundRH FleetHeatPositivityRH FleetTwoPointConvexity FleetPrimeOnlyRH
lake env lean verification/PaperAxioms.lean
```

## Licences

The Lean sources are licensed under Apache-2.0 and include third-party code listed in `NOTICE`.
The paper (`paper/`) is licensed under CC BY 4.0. Neither licence replaces the other.
