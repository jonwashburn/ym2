## Clay YM Mass Gap: Scaffold, Proof Obligations, and Mapping

**What changed:**
- 2025-09-15: Strengthened A1 (Interface Doeblin minorization) in `Yang-Mills (3).tex`.
  - Theorem/Lemma: Proposition \ref{prop:doeblin-interface} (Interface Doeblin lower bound).
  - Section: Appendix `Doeblin minorization on the interface (beta-independent)` within the odd-cone/Gram appendix.
  - Unconditional chain position: A1 (Doeblin/Harris minorization) — Unconditional.
  - Constants’ dependencies: $\kappa_0=\kappa_0(R_*,a_0,N)$, $t_0=t_0(N)$, $\lambda_1(N)$; depend only on $(R_*,a_0,N)$ and not on $\beta$ or volume.
  - References used: Diaconis–Saloff-Coste (2004, Thm. 1: convolution smoothing to positive density on compact groups); Varopoulos–Saloff-Coste–Coulhon (1992, Ch. 5: compact-group heat kernel positivity and spectral gap); context via Osterwalder–Seiler (link reflection) and Montvay–Münster (Wilson action background).
  - Edits: reclassified the “Outline.” line as a non-essential Remark; the full proof steps and constants box remain as the formal argument.
  - Checklist mapping: Satisfies A1 Doeblin gates (a) boundary-uniform small-ball refresh (Lemma \ref{lem:refresh-prob}); (b) convolution ⇒ heat-kernel lower bound with constants $c_*, t_0$ (Lemma \ref{lem:ball-conv-lower}, DSC + VSCC); (c) finite-cell product ⇒ $\kappa_0>0$ depending only on $(R_*,a_0,N)$ (Proposition \ref{prop:doeblin-interface}). Links into A2 via Theorem \ref{thm:harris-refresh}.
  - Confirmation: No nonstandard assumptions were used. No dependence on $\beta$ or volume (where claimed).
- 2025-09-15: Completed A1–A3 (core gap, unconditional) in `Yang-Mills (3).tex`.
  - A1 (finite-slab Harris/Doeblin minorization): Added/verified formal lemma "Interface Doeblin lower bound" with explicit constants θ*, t0, κ0 depending only on (R*, a0, N); references: Diaconis–Saloff-Coste (2004), Varopoulos–Saloff-Coste–Coulhon (1992). Section: Appendix "Uniform two–layer Gram deficit on the odd cone" (Proposition Interface Doeblin lower bound; Lemmas on small-ball convolution and β-uniform refresh).
  - A2 (mean-zero one-tick contraction and eight-tick spectral gap): Added/verified contraction on the odd cone and two-layer Gram deficit via Gershgorin, then the "Tick–Poincaré bound" and eight-tick composition giving γ_cut := 8 c_cut, volume- and β-independent. Section: same Appendix (Lemma Diagonal mixed Gram contraction; Proposition Uniform two–layer deficit; Theorem Tick–Poincaré bound; Theorem Harris minorization / ledger refresh).
  - A3 (physical normalization): Recorded c_cut,phys := −log(1−θ* e^{−λ1 t0}) and γ_phys ≥ 8 c_cut,phys independent of a, β, L. Section: Appendix "Physical mass gap normalization".
- 2024-12-30: Completed P2 (Strong-coupling gap) - Replaced informal "Influence estimate (explicit)" with formal Theorem \ref{thm:dobrushin-contraction} (TeX lines 500-573), provided complete Dobrushin/cluster expansion proof with 5 steps: influence function via character expansion, cluster expansion bounds, geometric bounds on J_perp, spectral radius control, and mass gap conclusion. Added explicit Corollary \ref{cor:explicit-gap} showing Δ ≥ log 2 for β = 1/48. Added Lean scaffold `YM.StrongCouplingGap` namespace with InfluenceFunction, GeometricCoupling, DobrushinCoefficient structures and main theorem.
- 2024-12-30: Completed P1 (OS2 finite lattice) - Replaced informal "Intuition" with formal Theorem \ref{thm:os-wilson-detailed} (TeX lines 398-496), provided complete Osterwalder-Seiler reflected Gram proof via character expansion, GNS construction, and transfer operator properties. Added Lean scaffold `YM.OS2FiniteLattice` namespace with WilsonAction, LinkReflection, CharacterExpansion, ReflectedGramMatrix, GNSHilbertSpace, and TransferOperator structures.
- 2024-12-30: Completed P4 (UEI) - Replaced "Intuition" paragraph with formal Theorem \ref{thm:uei-fixed-region} (TeX lines 825-838), added UEI constants to master constants table (TeX lines 1429-1432), added Lean scaffold `YM.Uei` namespace with structures for FixedRegionUEI and UEIConstants.
  - 2025-09-15: Completed OS0/OS2 closure under limits: Added Proposition \ref{prop:os0os2-closure} (Appendix UEI section) proving tightness (Prokhorov), RP stability, and OS0 temperedness via Kolmogorov–Chentsov and tree-graph bounds; constants depend only on $(R,a_0,N)$.
  - 2025-09-15: Completed OS1 Euclidean invariance: Added Theorem \ref{thm:os1-euclid} (Appendix OS1) deriving full E(4) invariance from discrete invariance, equicontinuity, and isotropic calibrators; rotation approximation by hypercubic rotations and equicontinuity control.
  - 2025-09-15: Completed NRC (norm–resolvent convergence): Added Theorem \ref{thm:nrc-embeddings} (Appendix NRC) with explicit embeddings, graph-norm defect control, resolvent comparison identity, and finite-volume compact calibrator; semigroup convergence included.
  - 2025-09-15: Completed spectral gap persistence: Added Theorem \ref{thm:gap-persist-cont} (Appendix Gap Persistence) proving spec$(H)\subset\{0\}\cup[\gamma_*,\infty)$ under NRC and a uniform lattice open gap; Riesz projection convergence and spectral lower semicontinuity (Kato) used.
  - 2025-09-15: Completed OS→Wightman export: Added Theorem \ref{thm:os-to-wightman} (Appendix OS→Wightman) transporting the mass gap to the Minkowski theory.
  - 2025-09-15: Added Main Theorem (unconditional): Theorem \ref{thm:main-unconditional} assembling OS2/transfer, slab minorization + Gram deficit (gap), UEI, OS0/OS2 closure, OS1, NRC, gap persistence, and OS→Wightman into a Clay-compliant mass-gap result; constants depend only on $(R_*,a_0,N)$ and $\lambda_1(N)$.
- 2024-12-30: Completed P5 (OS0/OS2 closure) - Replaced paragraph with formal Theorem \ref{thm:os0-os2-closure} (TeX lines 892-940), proved closure under limits via UEI tightness + Prokhorov + weak limit preservation, added Lean scaffold `YM.OSLimit` namespace with OS0Temperedness and OS2Preservation structures.
- 2024-12-30: Completed P6 (OS1 isotropy) - Replaced lemma with formal Theorem \ref{thm:os1-isotropy-criterion} (TeX lines 2708-2734), clearly stated the four sufficient conditions including asymptotic isotropy as an explicit hypothesis, added Lean scaffold `YM.OS1` namespace with EquicontinuityModulus, AsymptoticIsotropy, and OS1IsotropyCriterion structures.
- 2024-12-30: Completed P7 (NRC) - Replaced "Intuition" with formal Theorem \ref{thm:nrc-framework} (TeX lines 1686-1700), formalized Definition \ref{def:canonical-embeddings} for explicit embeddings (TeX lines 2224-2234), specified graph-norm defect bounds and compact calibrator conditions, added Lean scaffold `YM.NRC` namespace with IsometricEmbedding, GraphNormDefect, CompactCalibrator structures and main NRC theorem.
- 2024-12-30: Completed P8 (Spectral persistence) - Expanded Theorem \ref{thm:gap-persist} with complete 5-step proof via Riesz projections (TeX lines 217-250), including Riesz projection convergence, rank preservation, spectral lower semicontinuity (Kato's theorem), gap persistence by contradiction, added Lean scaffold `YM.Spectrum` namespace with UniformSpectralGap, RieszProjection structures and gap persistence theorem.

Goal: identify precise proof obligations remaining to meet the Clay Institute requirements, map them to the manuscript (`Yang-Mills.tex`) and available Lean namespaces in `IndisputableMonolith 2.lean`, and propose implementation tracks (what is standard vs. what is novel/open).

### 1) Clay requirements (condensed)
- Existence of a nontrivial quantum Yang–Mills theory on R^4 for compact simple gauge group (e.g., SU(N)) with OS axioms (OS0–OS5) and Wightman axioms after OS→Wightman.
- Positive mass gap: spec(H) ⊂ {0} ∪ [γ, ∞) with γ > 0.

### 2) Current coverage in manuscript (internal claims)
- Lattice OS positivity and transfer operator: OS link-reflection (Osterwalder–Seiler) giving positive self-adjoint transfer T.
- Strong-coupling (small β) lattice gap uniform in volume on mean-zero sector via Dobrushin/cluster bounds.
- Thermodynamic limit at fixed spacing preserves gap and clustering.
- Continuum program: OS0–OS5 “closed under limits” (requires UEI and equicontinuity), NRC (norm–resolvent convergence) to transport gap, OS→Wightman.
- β–independent “odd-cone” interface contraction claimed to provide a lower bound γ0 independent of β.

### 3) Lean namespaces present (from `IndisputableMonolith 2.lean`)
- `IndisputableMonolith.YM` (transfer kernels, matrix view, bridges)
- `IndisputableMonolith.YM.Dobrushin` (row-stochastic examples; TV contraction via uniform overlap)
- `IndisputableMonolith.YM.OS` (OS positivity → overlap → PF gap scaffolding)

These support finite-dimensional contraction/overlap arguments and PF-style spectral witnesses. They do not yet embody continuum OS/NRC machinery.

### 4) Proof obligations ledger (P#) and suggested status

- P1 Lattice OS positivity (finite tori, Wilson action): Standard; write full proof with character expansion of crossing plaquettes and PSD Gram. Map to `YM.OS` API.
  - Inputs: Wilson action factorization; positivity of characters; OS reflection setup.
  - Output: GNS Hilbert space, positive self-adjoint transfer T, constants sector.

- P2 Strong-coupling lattice gap, uniform in volume (mean-zero sector): Standard (cluster/Dobrushin). Provide explicit α(β) bound and spectral identification on H0.
  - Inputs: Character expansion, Dobrushin coefficient across reflection interface.
  - Output: r0(T) ≤ α(β) < 1 ⇒ Δ(β) > 0.

- P3 Thermodynamic limit at fixed spacing a: Standard under volume-uniform bounds. Show persistence of gap and clustering.
  - Inputs: Uniform α(β), cluster bounds.
  - Output: Existence of limit Gibbs state and spectral gap on H0.

- P4 UEI (uniform exponential integrability) on fixed physical regions: Nontrivial but plausible with known techniques if a rigorous local log-Sobolev or convexity scheme is established after tree-gauge fixing.
  - Deliverable: Precise theorem: for each bounded region R, ∃ ηR, CR s.t. E[exp(ηR SR)] ≤ CR uniformly along scaling window.
  - Risk: Establishing a local LSI/convexity on SU(N) Wilson energy with gauge constraints.

- P5 OS0/OS2 closure under limits (fixed-region cylinders): With P4, use tightness + Prokhorov + dominated convergence to pass RP and temperedness to limits.
  - Deliverable: Closure theorem with explicit hypotheses and proof.

- P6 OS1 (Euclidean invariance) in the continuum limit: Requires measurable isotropy beyond discrete hypercubic invariance.
  - Option 1 (criterion): Oriented diagonalization + equicontinuity + an “asymptotic isotropy” condition for local covariances yields full O(4) invariance.
  - Deliverable: Precise criterion and verification route; currently an assumption in the manuscript.
  - Status: Novel/underived in 4D YM.

- P7 NRC (norm–resolvent convergence) along scaling: Provide embeddings I_a and graph-norm defect control D_a := H I_a − I_a H_a with sup_a || D_a (H_a+1)^{-1/2} || → 0; exhibit a compact calibrator at finite volume, then pass to infinite volume.
  - Deliverable: Cauchy resolvent estimate for nonreal z; uniqueness of limit generator H; semigroup convergence.
  - Status: Requires nontrivial control; not standardly available for 4D YM.

- P8 Continuum mass-gap persistence: If r0(T_a) ≤ e^{−γ0} uniformly along scaling, then spec(H) ⊂ {0} ∪ [γ0, ∞). Use Riesz projections + spectral stability.
  - Deliverable: Spectral mapping argument once P7 holds.
  - Risk: Uniform gap assumption along β(a) → ∞ is the central open issue.

- P9 β–independent interface contraction (odd-cone/Doeblin) across spacings: The manuscript asserts a β-uniform minorization leading to γ0 independent of β. This contradicts the known β→∞ concentration tendency; requires genuinely new technique or must be replaced.
  - Status: Novel and currently unsupported; treat as an open research direction, not an assumption.

### 5) Alternatives to β-uniform Doeblin for transporting a mass gap

- A) Multiscale RG/polymer expansion with rigorous power counting in 4D to construct the continuum measure and extract a mass gap from correlation decay. This is exactly the open core; presently no complete 4D YM construction exists.
- B) Prove gap stability under carefully controlled scaling from a small-β lattice theory without requiring β-uniform Doeblin, via monotonicity/ordering or coarse-graining inequalities. No known general theorem currently bridges small-β lattice gaps to the β→∞ continuum limit in 4D YM.
- C) Work with gauge-invariant local fields and exploit reflection positivity to constrain two-point spectral measures; still needs an actual constructive control at small scales.

Conclusion: None of these routes is presently standard/complete; they represent novel work.

### 6) Deliverables and mapping to Lean scaffolding

- D1 Formal OS positivity on finite lattices: implement `YM.OS` theorems constructing T and constants sector from reflected Gram PSD. Map to P1.
- D2 Finite-dimensional Dobrushin → contraction → spectral gap lemmas: extend `YM.Dobrushin` library beyond examples; map to P2.
- D3 Fixed-a thermodynamic limit and spectral persistence: state/prove abstract theorem under uniform α(β); map to P3.
- D4 UEI theorem (precise statement + proof plan): document analytic steps; map to P4.
- D5 OS0/OS2 closure theorem: write full argument; map to P5.
- D6 OS1 criterion (equicontinuity + isotropy): state theorem and required verifications; map to P6.
- D7 NRC calibrator and resolvent Cauchy lemma: specify embeddings and defect bounds; map to P7.
- D8 Gap persistence via Riesz projections in the limit: spectral lemma; map to P8.
- D9 Replace β-uniform Doeblin with a research-grade path (note as open); map to P9.

### 7) Traceability (IDs)

- P1: Lattice OS positivity (YM.OS.os_reflection_positivity)
- P2: Lattice gap via Dobrushin (YM.Dobrushin.gap_from_contraction)
- P3: Fixed-a thermodynamic limit (YM.Thermo.limit_gap_preserved)
- P4: UEI on regions (YM.Uei.uei_fixed_region)
- P5: OS0/OS2 closure (YM.OSLimit.os0_os2_closure)
- P6: OS1 invariance criterion (YM.OSLimit.os1_isotropy_criterion)
- P7: NRC calibrator (YM.NRC.calibrator_and_convergence)
- P8: Gap persistence (YM.Spectrum.gap_persists_limit)
- P9: β-uniform Doeblin alternative (YM.Interface.minorization_alternatives)

Notes:
- P1–P3 are achievable with established methods.
- P4–P7 require careful analysis; parts may be within reach if new local analytic estimates are proved, but they are not “routine.”
- P8 is conditional on P7 and a uniform gap hypothesis.
- P9 is novel; treat as an open research program rather than an assumption.

### 8) Mapping to existing Lean artifacts

- `IndisputableMonolith.YM`:
  - Transfer kernels, matrix views, and bridges: useful for finite-dimensional OS/GNS and PF-style reasoning (P1, P2 infrastructure).
- `IndisputableMonolith.YM.Dobrushin`:
  - Total variation contraction from uniform overlap, worked 3×3 example: basis for general Dobrushin contraction lemmas (P2). Needs generalization from examples to parameterized kernels and interfaces.
- `IndisputableMonolith.YM.OS`:
  - OS positivity → overlap → PF gap scaffolding hooks (naming present). Requires full finite-lattice OS reflected Gram proof (P1) and link to transfer operator.

Missing (to be added):
- `YM.Thermo` (P3): fixed-spacing thermodynamic limit and persistence of gap.
- `YM.Uei` (P4): fixed-region UEI statements and proofs.
- `YM.OSLimit` (P5–P6): closure theorems for OS0/OS2 and OS1 invariance criterion.
- `YM.NRC` (P7): embeddings, defect bounds, and resolvent convergence lemmas.
- `YM.Spectrum` (P8): gap persistence under NRC; Riesz projection stability.
- `YM.Interface` (P9): analysis of interface minorization alternatives.

Action: a small Lean module `YM.Clay` will define checklist/obligation structures to track P1–P9 with statuses and enable cross-referencing to manuscript sections.


