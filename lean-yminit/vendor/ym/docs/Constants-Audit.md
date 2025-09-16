# Constants Audit (Interface-Level)

This page lists constants used across the OS/NRC/gap pipeline, their intended provenance, and which Lean lemmas consume them. Values are conservative placeholders unless otherwise noted; all entries record independence from β and volume L, and monotonicity in the slab thickness a where relevant.

## SU(N) Heat Kernel and λ₁(N)
- File: `ym/os_pos_wilson/Constants.lean`
- Symbol: `lambda1_table(N)` with lemma `lambda1_table_pos` (N ≥ 2 ⇒ λ₁(N) > 0).
- Usage:
  - `ym/os_pos_wilson/OddConeCut.lean`: `c_cut_from_refresh(a, θ_*, t₀, λ₁) = -(1/a) log(1 - θ_* e^{-λ₁ t₀})`.
  - Gap export via `wilson_pf_gap_from_ledger_refresh_explicit` and `c_cut(G,a)`.
- Notes: λ₁(N) > 0 depends only on N and metric normalization; table is conservative (set to 1 for small N). Replace with audited values and citations when available.
  - Conservative numerics: for N=2,3 we take λ₁=1.

## Cross-Cut Geometry and J_⊥
- File: `ym/os_pos_wilson/Constants.lean`
- Symbols:
  - `CrossCutGeom`: `m_cut`, `n_cut`, `J_unit ≥ 0`.
  - `w1_table(N) ≥ 0`: conservative first nontrivial character weight.
  - `J_perp(G, N) = m_cut · w1_table(N)`; nonnegativity and β/volume independence lemmas.
- Usage:
  - Strong-coupling Dobrushin bound `α(β) ≤ 2 β J_⊥` in `ym/gap_strong_coupling/AlphaBeta.lean`.
  - Best-of-two selector in `ym/os_pos_wilson/OddConeCut.lean` via `wilson_pf_gap_select_best(_from_pack)`.
- Notes: `m_cut` counts slab-local interface elements; independent of volume L; monotone in region; bounded by `a ≤ a0`.
  - Conservative numerics: with nominal `(R_*, a0)` and local geometry count `m_cut`, taking `w₁(2)=1/4`, `w₁(3)=1/6` yields `J_⊥ = m_cut · w₁(N)`.
  - Then `γ_cut = 8 · c_cut(G,a)` and the best-of-two lattice gap is `max{1−2βJ_⊥, 8·c_cut}`.

## Area–Perimeter Constants (Optional)
- File: `ym/OSPositivity/AreaLawBridge.lean`
- Symbols: `AreaPerimeterConstants (T_*, C_*)`, `TubeGeometry (κ_*)`.
- Exports: `continuum_area_law_perimeter`, `area_law_implies_uniform_gap` (γ = T_* κ_*).

## Uniform KP Window (Optional)
- File: `ym/cluster/UniformKP.lean`
- Symbols: `UniformKPWindow (T_*, C_*, α_*)` with `α_* < 1`.
- Export: `uniform_gap_on_window` (PF gap γ = 1 − α_*).

## Monotonicity and Independence
- β-independence: `J_perp_beta_independent`, `J_perp_volume_independent` show independence from β and volume.
- Monotonicity in a: `c_cut(G,a)` increases as a decreases via prefactor 1/a; for `a ∈ (0, a0]`, positivity via `θ_* ∈ (0,1)`, `t₀ > 0`, `λ₁ > 0`.

## Consumers (Selected)
- OS2/Transfer: `ym/os_pos_wilson/ReflectionPositivity.lean`, `ym/Transfer.lean`.
- Odd-cone: `ym/os_pos_wilson/OddConeCut.lean` (`GeometryPack`, `c_cut`).
- NRC/Persistence: `ym/spectral_stability/NRCEps.lean`, `ym/spectral_stability/Persistence.lean`.
- Optional: `ym/OSPositivity/AreaLawBridge.lean`, `ym/cluster/UniformKP.lean`.

> Replace placeholder tables (`lambda1_table`, `w1_table`) with audited values and citations (e.g., heat kernel on SU(N), Peter–Weyl expansion) as available. Interface lemmas only require positivity/inequalities, so refinements are local.
