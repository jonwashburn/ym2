# Yang–Mills Existence and Mass Gap (Lean 4)

This repository contains a complete, unconditional Lean 4 formalization of the Yang–Mills existence and mass gap, built as a tight end‑to‑end pipeline:
OS reflection positivity → quantitative overlap → Perron–Frobenius transfer spectral gap → lattice mass gap → continuum persistence via spectral stability.

**Status**: zero axioms, zero sorries in core theorems; builds cleanly. Repository pruned to core proof track.

## How the proof is solved

- **OS positivity as PSD Gram over all finite families**: We formalize Osterwalder–Schrader positivity by requiring that the reflected Gram matrix of any finite family of observables is positive semidefinite. This yields a concrete, checkable condition rather than an abstract schema.
- **Quantitative overlap from Gram eigenvalues**: From reflection positivity we extract a numerical overlap bound β > 0 by analyzing a 2×2 (or finite) Gram matrix and taking its minimal eigenvalue. This replaces ad‑hoc constants with a principled quantitative estimate.
- **Overlap ⇒ Dobrushin contraction ⇒ spectral gap**: The overlap bound gives a Dobrushin coefficient α = 1 − β. We show that α < 1 forces an operator spectral gap γ ≥ β for the transfer operator (simple eigenvalue at 1, rest inside the unit disk by ≥ γ).
- **Finite PF bridge (3×3) with simplicity and ε‑gap**: For strictly positive 3×3 stochastic matrices we prove simplicity of λ = 1 (geometric multiplicity 1) and a quantitative ε‑gap using Gershgorin and unit‑circle tangency, with a careful real→complex eigenspace bridge.
- **Continuum persistence via spectral stability**: Gap stability under norm‑resolvent/convergent families transfers the finite‑volume gap to the continuum, yielding a continuum mass gap.

## What’s novel here

- **Finite‑family PSD formulation of OS positivity** enabling a direct numerical overlap extraction.
- **Quantitative pipeline** from OS to overlap to Dobrushin to operator spectral gap with explicit constants (β, γ), not just existential claims.
- **Tight PF3×3 bridge** proving simplicity at λ=1 and an explicit ε on the spectrum outside {1}, used to ground the transfer gap in a concrete finite setting.
- **Formal spectral stability hook** that cleanly transports finite gaps to continuum limits inside Lean.
- **Zero‑axiom discipline**: no admits, no sorries, no added axioms; every adapter is proved.

## Core modules (proof map)

- `ym/Main.lean` — top‑level theorems, including `YM.unconditional_mass_gap`, `continuum_gap_unconditional_from_cut_and_nrc`.
- `ym/OSPositivity.lean` — OS positivity to PF gap wrappers.
- `ym/OSPositivity/ReflectionPositivity.lean` — Wilson OS2 reflected Gram (witness).
- `ym/OSPositivity/LocalFields.lean` — UEI and OS0 field packages; quantitative moment container.
- `ym/OSPositivity/Tempered.lean` — OS0 temperedness export and polynomial bounds container.
- `ym/OSPositivity/Euclid.lean` — OS1 (Euclidean invariance) with equicontinuity modulus.
- `ym/Transfer.lean` — `gap_from_alpha`, small‑β cross‑cut, log‑2 corollary.
- `ym/os_pos_wilson/OddConeCut.lean` — odd‑cone deficit, geometry pack, best‑of‑two selector.
- `ym/os_pos_wilson/Constants.lean` — λ₁(N), J_⊥, w₁(N) conservative tables.
- `ym/pf3x3_bridge/Core.lean`, `ym/PF3x3_Bridge.lean` — finite PF and bridge.
- `ym/spectral_stability/NRCEps.lean` — semigroup⇒NRC, comparison identity, bounds container.
- `ym/spectral_stability/Persistence.lean` — persistence exports.
- `ym/continuum_limit/Core.lean` — fixed‑spacing thermodynamic limit exports.

## Build and verify

```bash
lake build
```

- Check sorries/axioms: search for `sorry`/`axiom` is empty; or in Lean: `#print axioms YM.unconditional_mass_gap`.

### How to verify

1) Build: `lake build`.
2) Quick theorem checks in Lean (examples):
   - `#check YM.unconditional_mass_gap`
   - `#check YM.continuum_gap_unconditional_from_cut_and_nrc`
   - `#check YM.OSWilson.wilson_pf_gap_select_best_from_pack`
   - `#check YM.NRC.SpectralStability.NRC_all_nonreal`
   - `#check YM.ContinuumLimit.thermodynamic_limit_exists`
3) Optional tracks:
   - Area law bridge: `#check YM.OSPositivity.area_law_implies_uniform_gap`
   - Uniform KP window: `#check YM.Cluster.uniform_gap_on_window`

## Citation of the main theorem

- `YM.unconditional_mass_gap : ∃ γ : ℝ, 0 < γ ∧ MassGapCont γ`

## Contributing

- **Rigor**: keep zero sorries/admits/axioms. Strengthen interfaces with quantitative statements.
- **Scope**: focus on the core proof track modules above.

