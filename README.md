# weil-gaussian-lean

Lean 4 / Mathlib formalization of Weil's explicit formula for the Riemann zeta function and of
criteria for the Riemann hypothesis stated on Gaussian test functions.

## Paper

`paper/heat_positivity.pdf` — J. C. Kerr, *A Gaussian form of Weil's positivity criterion for the
Riemann hypothesis*. DOI: [10.5281/zenodo.24578253](https://doi.org/10.5281/zenodo.24578253).
The Lean sources at tag `v1.1` are archived at DOI: [10.5281/zenodo.24578750](https://doi.org/10.5281/zenodo.24578750).

| Statement in the paper | Lean theorem |
|---|---|
| Explicit formula for Gaussians (1) | `FleetPrimePoleBoundRH.zero_trace_eq_rhs` |
| Theorem 1, zero side | `FleetHeatPositivityRH.RH_iff_heat_positivity` |
| Theorem 1, arithmetic side | `FleetHeatPositivityRH.RH_iff_rhs_positivity` |
| Corollary 2 | `FleetTwoPointConvexity.RH_iff_twoPoint` |
| Theorem 3 | `FleetPrimeOnlyRH.RH_iff_primeOnly_bound` |

`RiemannHypothesis` is Mathlib's definition. The theorems above depend only on the axioms
`propext`, `Classical.choice` and `Quot.sound`; `AxiomAudit.lean` prints the axioms of each
audited theorem.

## Build

Lean `v4.35.0` and Mathlib `v4.35.0` (see `lean-toolchain` and `lake-manifest.json`).

```bash
lake exe cache get
lake build FleetPrimePoleBoundRH FleetHeatPositivityRH FleetTwoPointConvexity FleetPrimeOnlyRH
```

`lake build` builds every module, including the vendored code under `OAI/`.

## Layout

- top level: explicit formula, Gaussian test functions, criteria
- `Kerr/`: number-theory modules shared with other projects
- `OAI/`: third-party code, see `NOTICE`

## Build record

`verification/` holds the build log and the axiom printout for the theorems cited in the paper.

## License

Lean sources: Apache-2.0. Third-party code and credits are listed in `NOTICE`.
Paper (`paper/`): CC BY 4.0.
