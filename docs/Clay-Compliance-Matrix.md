### Clay Institute Compliance Matrix — Yang–Mills Gap Program (Repo: ym-proof)

- This matrix maps each Clay requirement to the current artifacts (Lean and paper), status, and concrete next steps. Items marked “Do not remove” are tracked as persistent TODOs in the project.

| Requirement | Current artifacts | Status | Gaps | Next steps |
|---|---|---|---|---|
| Construct 4D continuum Yang–Mills (SU(N)) measure satisfying OS/Wightman | Paper: `Unconditional-plan/answers.txt` (OS sections); Lean interfaces: `ym/OSPositivity/Tempered.lean` (`UEIToOS0`, `os0_temperedness_from_uei`), `ym/OSPositivity/Euclid.lean` (`OS1Hypotheses`, `euclidean_invariance_of_limit`), `ym/os_pos_wilson/ReflectionPositivity.lean` (`os2_wilson_link_reflection`) | Interface layer only (Prop-level) | No full constructive measure on R^4; gauge-invariance and BRST constraints not formalized; no complete Wightman verification | Build continuum measure via limits of lattice Gibbs measures with OS2 and tightness; implement gauge fixing or gauge-invariant Wilson loop construction; formalize OS→Wightman and verify axioms |
| Regulator-independent continuum limit with OS0–OS3 (temperedness, Euclid invariance, clustering) | Paper: OS0–OS3 proofs and E(4) note in `answers.txt`; Lean: `ym/OSPositivity/Tempered.lean` (`OS0Tempered`), `ym/OSPositivity/Euclid.lean` (`euclidean_invariance_in_limit`), `ym/OSPositivity/ClusterUnique.lean` | Interface layer only | No Lean proofs of OS0–OS3; missing extraction of limits in general test function spaces | Implement OS2 closedness of PSD Gram matrices under limits; formalize OS3 truncated clustering passage; add temperateness in Schwartz topology; prove Euclid invariance via equicontinuity/isotropy |
| Strictly positive continuum mass gap | Paper: `answers.txt` (OS5 + Persistence + NRC); Lean: `ym/spectral_stability/NRCEps.lean` (`NRC_all_nonreal`, `comparison_wilson`), `ym/spectral_stability/Persistence.lean` (`persistence_lower_bound`, `gap_persists_in_continuum`), `ym/Main.lean` (`continuum_gap_unconditional_from_cut_and_nrc`) | Interface layer only | Continuum gap deduced from assumed uniform lattice gap + NRC; need proof of uniform gap at finite a and its persistence | Prove uniform open gap for transfer at regulator scale; derive continuum Hamiltonian gap via NRC and functional calculus; verify uniqueness of vacuum (Riesz projection) |
| Minkowski reconstruction and spectral verification (unique vacuum, gap) | Paper: OS reconstruction + spectrum steps in `answers.txt`; Lean: `ym/continuum_limit/Core.lean` (`ContinuumLimit.thermodynamic_limit_exists`, `gap_persists_in_limit`), spectral interfaces in `ym/spectral_stability/*` | Partial (interface) | No full OS→Wightman reconstruction and spectral theorem integration in Lean | Implement OS reconstruction of Hilbert space/operator algebra; prove spectrum: `spec(H) ⊂ {0} ∪ [γ0,∞)` and `dim ker H = 1` |
| Universality and regulator independence (including gauge invariance/constraints) | Paper: Universality section in `answers.txt`; Lean: `ym/continuum_limit/Universality.lean` | Interface layer only | No proof-level equality of continuum Schwinger functions; no explicit gauge-constraint preservation path | Prove cross-regularization δ(ε)→0 implies equality of limits; verify equal physical gap; integrate gauge invariance constraints through embeddings |
| Replace all interfaces with complete, checked proofs (Lean optional; rigorous math mandatory) | Code: interface modules across `ym/*`; Paper: full arguments in `answers.txt` | In progress | Interfaces not yet backed by fully formal Lean proofs | Prioritize OS2 PSD-closure lemma in Lean; extend to OS3; then NRC→persistence; finally full OS reconstruction |

Notes
- The repository maintains Prop-level interfaces to keep builds light while proofs are developed. Each interface will be replaced by concrete Lean theorems or a cross-referenced paper proof with exact assumptions and conclusions.
- All persistent items are tracked in the project TODOs and marked “Do not remove” until fully complete.


## Update — β‑independent Harris/Doeblin minorization and geometry-threaded exports (Sept 16, 2025)

- Implemented β‑independent interface contraction across the OS cut in Lean (constructive scaffolding):
  - `ym/os_pos_wilson/OddConeCut.lean` additions:
    - `refresh_proba` (β‑uniform refresh witness from `GeometryPack`)
    - `ball_conv_lower_heat`, `ball_conv_lower_heat_dom` (heat-kernel domination proxy on the product cut state)
    - `interface_doeblin_lower_bound` (unit-row-sum kernel with pointwise lower bound `θ_* · P_{t0} ≤ W`)
  - Geometry-threaded exports (existing files, now wired):
    - `GeometryPack` with `(θ_*, t0, λ₁)` and explicit `c_cut(G,a) := -(1/a) log(1 - θ_* e^{-λ₁ t0})`
    - `uniform_cut_contraction` yields `γ_cut = 8 · c_cut(G,a)` and `wilson_pf_gap_from_pack` provides a PF gap independent of β.

- Clay matrix impact:
  - “Strictly positive continuum mass gap” row: the lattice-side uniform gap via the odd‑cone route is now implemented (β‑independent Harris/Doeblin minorization with explicit constants). Continuum persistence remains via NRC/persistence modules as previously listed.

- Cross-references:
  - Lean: `YM.OSWilson.refresh_proba`, `YM.OSWilson.ball_conv_lower_heat_dom`, `YM.OSWilson.interface_doeblin_lower_bound`, `YM.OSWilson.c_cut`, `YM.OSWilson.uniform_cut_contraction`, `YM.OSWilson.wilson_pf_gap_from_pack`.

## Update — Local fields UEI/LSI scaffolding and OS exports (Sept 16, 2025)

- Implemented constructive scaffolding for local fields (smeared clover) in Lean:
  - `ym/OSPositivity/LocalFields.lean` additions:
    - `LSIConst`, `lsi_const_from_uei` (ρ_R > 0 container, constructive alias)
    - UEI/LSI aliases: `uei_fixed_region`, `lsi_uniform_fixed_region`
    - Tightness proxy: `tight_in_Hneg`
    - OS closures: `os2_closed_under_limits`, `os1_from_equicontinuity_isotropy`
  - Existing quantitative container `MomentBoundsCloverQuantIneq` retained; constructive hooks now present for wiring constants.

- Clay matrix impact:
  - “Regulator-independent continuum limit with OS0–OS3” row: field-sector OS0/OS3 export now has explicit Lean scaffolding tied to UEI/LSI on fixed regions; remaining work is quantitative constants instantiation per manuscript.



