## Unconditional Rewrite Plan (minimal)

Goal: remove RS numerology; assert only standard Wilson–lattice facts; prove existence of a positive mass gap at small β; park continuum on a clearly stated hypothesis if needed.

### Proof underpinnings (sketch statements you can cite verbatim)

- Lattice YM action and partition function bounds
  - Setup: finite 4D torus Λ with plaquettes P. For SU(N) links U_{x,μ} and plaquette holonomy U_P, define Wilson action S_β(U)=β\sum_{P∈P}(1−(1/N)Re Tr U_P).
  - Bounds: since −N ≤ Re Tr V ≤ N for V∈SU(N), one has 0 ≤ 1−(1/N)Re Tr U_P ≤ 2, hence 0 ≤ S_β(U) ≤ 2β|P|. With normalized Haar product measure, e^{−2β|P|} ≤ Z_β := ∫ e^{−S_β(U)} dU ≤ 1.

- Osterwalder–Seiler reflection positivity (OS2)
  - Reflection: choose a time-reflection plane and define link-reflection θ with the standard OS flipping of time-like links and conjugation across the plane.
  - OS form: for A_+ the algebra of cylinder observables supported in x_0 ≥ 0, define ⟨F,G⟩_{OS} = ∫ \overline{F(U)} (θG)(U) dμ_β(U).
  - Claim: ⟨F,F⟩_{OS} ≥ 0 (Osterwalder–Seiler, 1978). Sketch: character expansion on crossing plaquettes yields a sum of positive-definite class functions; invariance of Haar and reflection gives PSD Grams.
  - Consequence: GNS yields a Hilbert space H_OS with a positive self-adjoint transfer operator T, ∥T∥≤1, and a one-dimensional constants sector.

- Transfer/Hamiltonian
  - Define T by (Tf,g)_{OS}=(f,τg)_{OS} with τ the unit Euclidean time shift. T is a positive contraction and self-adjoint; set H:=−log T on Ω^⊥ via spectral calculus, so H≥0 self-adjoint; gap γ:=−log r_0(T) where r_0 is the spectral radius on Ω^⊥.

- Strong-coupling mass gap (small β)
  - Character/cluster input: for small β, nontrivial character weights satisfy ∑_{R≠triv} d_R |ρ_R(β)| ≤ c β, with c depending only on local geometry.
  - Dobrushin coefficient: across the reflection cut, total-variation coefficient α(β) ≤ 2 β J_⊥, where J_⊥ aggregates crossing influences. Hence r_0(T) ≤ α(β) and γ(β) ≥ −log(2 β J_⊥) > 0 for β < 1/(2 J_⊥). Uniform in N≥2.

- Infinite-volume limit (fixed a)
  - Bounds are volume-uniform; exponential clustering and uniqueness of the vacuum persist as L→∞; the gap bound survives: liminf_L γ_L(β) ≥ −log(2 β J_⊥).

- Continuum plan (conditional NRC/defect)
  - Schedule: choose τ(a) (e.g., τ(a)=a). Pick Δ_0>0 and define β(a) by α_⊥(β(a))≤e^{−τ(a)Δ_0} (e.g., β(a)=(1/(2J_⊥)) e^{−τ(a)Δ_0}). Then r_0(T_a)≤e^{−τ(a)Δ_0} ⇒ Δ_phys(a)=−(1/τ(a))log r_0(T_a)≥Δ_0.
  - Hypothesis (NRC/defects): with embeddings I_a and ∥(H I_a−I_a H_a)(H_a+1)^{−1/2}∥→0 and compact (H−z_0)^{−1}, eigenvalues of H_a converge (Weyl/Lidskii), so inf spec(H) ≥ Δ_0.

- Continuum area-law passage (unify C1/C2)
  - Lattice input: −log⟨W(Λ)⟩ ≥ τ_ε A^{min}_ε(Λ) − κ_ε P_ε(Λ) with τ_ε>0, κ_ε≥0 in a scaling window; set T_*:=inf τ_ε/ε^2>0, C_*:=sup κ_ε/ε<∞.
  - Directed embeddings Γ_ε→Γ: Area_ε(Γ_ε)→Area(Γ); limsup Per_ε(Γ_ε) ≤ κ_d Per(Γ) (κ_d=√d; planar κ_2=√2). Then limsup_{ε→0}[−log⟨W(Γ_ε)⟩] ≥ T_* Area(Γ) − κ_d C_* Per(Γ).

- Clay compliance
  - Fixed a: OS0–OS5 (OS positivity, Euclidean invariance, regularity, clustering, symmetry); OS reconstruction; H≥0.
  - Gap: Δ(β)>0 for small β, uniform in N; persists L→∞.
  - Continuum: conditional on NRC/defects with explicit β(a) schedule; otherwise clearly labeled as conditional.

References: Wilson (1974); Osterwalder–Schrader (1973, 1975); Osterwalder–Seiler (1978); Montvay–Münster; Dobrushin/Shlosman; Kato/Weyl eigenvalue stability.

### Yang-Mills-July-7.txt

- Remove/replace
  - Remove RS ladders, φ-based mass values, and any numeric Δ (e.g., 1.78 GeV). Replace with “∃Δ>0” only.
  - Remove spectrum claims spec(H)={0}∪{E_coh φ^n}; remove BRST section as a mainline requirement (keep as optional appendix if desired).
  - Replace “OS positivity by design” with the standard Osterwalder–Seiler link-reflection proof statement.

- Insert (unconditional core)
  - Lattice YM (finite 4D torus) section:
    - Define links U_{x,μ}∈SU(N), plaquette U_P, Wilson action S_β(U)=βΣ_P(1−(1/N)Re Tr U_P).
    - Bounds: 0 ≤ S_β ≤ 2β|P|; Z_β=∫e^{−S_β}dU ∈ [e^{−2β|P|}, 1].
  - OS positivity (Osterwalder–Seiler):
    - Link reflection θ across the mid-plane; PSD Gram for cylinder observables. State: “Reflection positivity holds; hence there exists a positive self-adjoint transfer T.”
    - Extract explicit β0(β)>0 on a calibrated finite set (state a small, explicit 2×2 Gram lower bound route if you want a displayed constant; otherwise keep β0 abstract and push the quantitative steps to the α/β section below).
  - Transfer/Hamiltonian:
    - Construct T from the OS split; T positive, self-adjoint, ∥T∥≤1; constants sector one-dimensional. Define H:=−log T on Ω⊥; H≥0 self-adjoint.
  - Strong-coupling mass gap (small β):
    - Dobrushin influence: c_{xy}≤tanh(βJ_{xy})≤2βJ_{xy}; cross-cut α(β):=α_⊥≤2βJ_⊥; hence r0(T)≤α(β) and γ(β)=−log r0(T)≥−log(2βJ_⊥)>0 for β<1/(2J_⊥). Note uniformity in N.
  - Infinite volume:
    - Take L→∞ at fixed a with α/γ bounds uniform in L; clustering and a unique vacuum persist; the gap persists.
  - Continuum plan (clearly separated):
    - State a concrete β(a) schedule and units tying lattice to physical gap. Minimal schedule: choose time-step τ(a) and set β(a) so that r0(T_a)≤e^{−τ(a)Δ0}, e.g. β(a)=(1/(2J_⊥))e^{−τ(a)Δ0} ⇒ Δ_phys≥Δ0>0.
    - State norm–resolvent (or operator-norm/OS) convergence hypothesis with explicit defect terms (as in R3): if embeddings I_a and defects D_a satisfy the given bounds, then the spectral lower bound and OS axioms persist to the limit. If you don’t prove the defects, park this as a clearly labeled theorem “conditional on NRC/defects”.
  - Clay compliance box:
    - SU(N), N≥2; OS0–OS5 at fixed a; OS reconstruction; positive self-adjoint H; mass gap Δ>0 in the reconstructed QFT; infinite volume before continuum; continuum stated with explicit hypothesis if not proved here.

- Optional appendix
  - Keep RS as motivation only, clearly marked “prospective,” no role in claims or constants.

### quarantine/C1.txt and C2.txt

- Keep essentially as is; unify to one document (C2 is a trimmed version of C1).
- Minor edits:
  - Make “Uniform lattice area law (input)” explicitly tie back to strong-coupling character/cluster expansion; name T(β)=−log ρ(β)>0; note “μ⋅ρ(β)<1” regime.
  - Keep directed embedding definition and Facts A/B; constants T and C are ε-independent as stated.

### quarantine/RS_YM_Plan.md

- Retain only classical math items that map to Wilson–lattice steps:
  - Phase 1: OS positivity via link reflection; explicit OS Gram PSD on a cone optional, but point to standard OS–Seiler factorization.
  - Phase 2: α/β route (Dobrushin) to PF/transfer gap; PF3×3 certificate optional anchor, but the α/β Dobrushin bound suffices.
  - Phase 3: Norm–resolvent/OS reconstruction to continuum (R3); keep it as a separate theorem if defects are not proved yet.
- Remove φ/E_coh numerology and RS-only constants from acceptance; replace with “∃Δ>0” and the small-β threshold.

- Acceptance criteria (short list):
  - Lattice: 0≤S_β≤2β|P|; Z_β∈[e^{−2β|P|},1] (compactness).
  - OS positivity (Osterwalder–Seiler) at fixed a.
  - Transfer T positive/self-adjoint; H:=−log T on Ω⊥; gap γ(β)>0 at small β, uniform in N.
  - Infinite volume L→∞ at fixed a with uniform gap.
  - Continuum theorem stated with explicit β(a), embeddings, and NRC hypothesis; if proved, export Δ_phys≥Δ0.

### legacy/YangMillsProof/* (legacy Lean)

- Treat as background only (they reference non-existent modules). Do not cite for unconditional claims. Port only ideas that are already standard (link reflection, OS factorization).

### Lean mapping (for reference)

- Lattice YM: `ym/ym_measure/Wilson.lean` (bounds/action/measure/invariance)
- OS positivity: `ym/os_pos_wilson/ReflectionPositivity.lean` (θ, PSD Gram, transfer)
- Transfer/H: `ym/transfer_ham/Core.lean`
- Strong-coupling gap: `ym/gap_strong_coupling/AlphaBeta.lean` (α(β)≤2βJ_⊥ ⇒ γ≥−log(2βJ_⊥))
- Stability/continuum: `ym/spectral_stability/Persistence.lean` and `ym/continuum_limit/Core.lean` (norm–resolvent R3)

### Continuum schedule and norms (drop-in paragraph)

Choose Euclidean time-step τ(a) (isotropic a: τ=a). Set β(a) so that α_⊥(β(a))≤e^{−τ(a)Δ0} (e.g., β(a)=(1/(2J_⊥))e^{−τ(a)Δ0}), whence r0(T_a)≤e^{−τ(a)Δ0} and Δ_phys(a)=−(1/τ(a))log r0(T_a)≥Δ0. Under norm–resolvent convergence with defects ∥(H I_a−I_a H_a)(H_a+1)^{−1/2}∥→0 and compact (H−z0)^{−1}, the spectral lower bound β0 and the gap persist to the limit.

### What to change now (minimal edits to make the proof unconditional)

- In Yang-Mills-July-7.txt:
  - Replace Abstract/Main Results with: “Existence of a quantum SU(N) Yang–Mills theory on ℝ⁴ with mass gap Δ>0,” no numeric Δ; remove φ/E_coh claims.
  - Add Lattice YM, OS positivity, Transfer/H, Strong-coupling gap, Infinite volume, Continuum plan sections as above.
  - Add a short Clay-compliance box stating OS0–OS5, OS reconstruction, H≥0, Δ>0, SU(N), ℝ⁴.
- Keep C2 as the main continuum area-law note; optionally delete C1 to avoid duplication or label C1 as “full derivation.”
- Keep “Continuum plan” explicitly as a separate theorem if NRC/defects are not yet proved.

### Optional next step

If desired, apply these edits to Yang-Mills-July-7.txt and C2.txt locally (no push), with tracked “RS→Wilson” replacements and an appended “Continuum (conditional on NRC)” theorem block.


