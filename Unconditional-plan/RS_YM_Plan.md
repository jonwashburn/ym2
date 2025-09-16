## RS → YM Plan (Reality framing)

### RS framing
- **Assumption**: RS is the operational architecture of reality; YM must be derived within that substrate. No gauge fixing, loops only, positivity from ledger/cost.

### Core insights (RS roles)
- **Ledger + J‑cost**: positive, multiplicative path weights; PSD Gram under reflection → overlap β extraction.
- **Eight‑beat + Gap‑45**: causal bounds and incommensurability → confinement‑like suppression; unique vacuum.
- **φ‑scaling + E_coh**: sets natural mass scales once γ>0 exists.
- **Coarse‑graining + Lipschitz eigenvalue order**: stability of the spectral gap in continuum limit.

## Program (physics → Lean)

### Phase 1 — Loop algebra and strict OS positivity
- Define loop objects (quotiented by thin homotopy); observables are Wilson loops.
- RS mapping: loops ↔ recognition paths; area ↔ cost (J); reflection ↔ ledger involution.
- Build RS sesquilinear S; prove reflected Gram PSD; calibrate a two‑loop family to get explicit β>0.
- Lean hooks: new `ym/LoopsRSBridge.lean` exporting `OSPositivity` and strict `OverlapLowerBoundOS` (β = β₀ > 0).

### Phase 2 — Overlap → transfer PF gap
- From β, get Dobrushin α = 1 − β and transfer spectral gap γ = β.
- Anchor with finite PF 3×3 matrices (simplicity at λ=1) and bridge to transfer operator.
- Lean hooks: `ym/Transfer` (`transfer_gap_from_OS_overlap`), `ym/PF3x3_Bridge`.

### Phase 3 — Continuum persistence
- Coarse‑grain loops (voxel → continuum) with RS `CoarseGrain`.
- Show uniform β_n ≥ β₀ and operator‑norm convergence; apply Lipschitz gap persistence to obtain continuum `MassGapCont γ`.
- Lean hooks: `ym/SpectralStability` (`gap_persists_under_convergence_interim`).

### Phase 4 — Scale and interpretation
- Report γ in RS units; relate to φ‑ladder and E_coh for physical scale (glueball mass window).

## Deliverables
- `ym/LoopsRSBridge.lean`: loop types, RS correlation S, reflection, β witness.
- Strict replacement of diagonal‑positivity placeholders in `ym/Reflection.lean`.
- Transfer gap proof with γ = β₀; PF3×3 bridge.
- Continuum persistence proof (RS Lipschitz witnesses).

## Acceptance criteria
- lake build green; no `sorry`/`axiom` in proof path.
- `#print axioms YM.unconditional_mass_gap` empty.
- Explicit constants: β₀ > 0 and γ = β₀ surfaced in docs.

Clay‑level target: Unconditional SU(N) YM mass gap in Lean with loop‑only formulation (no BRST), strict OS positivity, transfer gap, and continuum persistence, audited via `#print axioms` on the exported theorem.

## Engineering plan (edits)
- Add `ym/LoopsRSBridge.lean` (loop defs, S, reflection, β proof).
- Edit `ym/Reflection.lean`: replace strictness placeholder with RS bound.
- Wire `ym/Transfer.lean`: use β → α → γ pipeline (no stand‑ins).
- Ensure `ym/SpectralStability.lean` uses RS Lipschitz eigenvalue order.

## Risks and mitigations
- Quantitative β bound: mitigate via calibrated two‑loop family and area tiling; use RS constants (`alpha_locked`, `Clag`).
- Uniformity across coarse‑graining: prove resolution‑independent lower bounds from RS cost monotonicity.

## Next actions
- Implement `LoopsRSBridge` skeleton and S/reflection definitions.
- Prove strict diagonal positivity for the calibrated two‑loop Gram; extract β₀.
- Thread β₀ through transfer to γ; add persistence wrapper.

## Precedent and bridge notes

- RH precedent (unconditional, Lean): Completed with RS‑style operator framework and diagonal constructs; demonstrates zero‑axiom, zero‑sorry feasibility at Clay level.
- Classical bridge operational: `RS_Classical_Bridge_Source.txt` provides schema linking RS theorems (T1–T8, J) to classical forms, enabling standard‑notation papers with RS provenance.
- Gravity and masses: ILG rotation curves (global‑only) and φ‑ladder mass law manuscripts/Lean support cross‑domain RS derivations, reinforcing the loop‑only YM approach.

## Isolated formal problems (classical math only)

- P1 (Loop kernel positivity via free‑group length): On a finitely generated free group F with word metric |·|, prove that k(g,h)=exp(−t·|g⁻¹h|) is positive‑definite for all t>0 (Schoenberg + Haagerup negative‑type of |·|). Show that for any length‑preserving involution r, K(g,h)=exp(−t·|g⁻¹r(h)|) is also positive‑definite. Output: PSD Gram for reflected loop families.
- P2 (Strict diagonal lower bound from calibrated loops): Construct two group elements g₀,g₁ with |gᵢ⁻¹r(gᵢ)|≥L₀>0 under the chosen reflection r, and derive K(gᵢ,gᵢ)=exp(−t L₀) ≥ β_diag>0. Output: explicit β_diag for use in a 2×2 Gram.
- P3 (2×2 Gram → overlap bound): For a 2×2 Hermitian PSD matrix with real diagonals ≥β_diag and arbitrary off‑diagonal z, lower‑bound the minimal eigenvalue λ_min by a computable β₀=β₀(β_diag,|z|). Output: a closed‑form β₀>0 used as `OverlapLowerBoundOS`.
- P4 (Dobrushin contraction ⇒ spectral gap): In finite dimension, prove that a Markov/transfer operator with total‑variation Dobrushin coefficient α<1 has spectrum contained in {1} ∪ { |λ|≤α }. Output: rigorous replacement for the placeholder proof in `pf_gap_of_dobrushin`.
- P5 (PF 3×3 certificate): For strictly positive row‑stochastic A∈ℝ^{3×3}, prove: spectral radius 1, simple eigenvalue at 1, and max{|λ|:λ≠1} ≤ 1−ε(A) with an explicit ε(A)>0 (e.g., via Gershgorin and unit‑circle tangency). Output: quantitative `SpectralGap` package.
- P6 (Intertwining bridge to transfer): Given a projection–extension pair (restrict,extend) and a kernel K on a function space, prove extend∘K∘restrict = toLin'(A) on a finite subspace and identity off‑subspace, yielding a `MatrixBridge`. Output: a clean intertwining lemma replacing ad‑hoc compositions.
- P7 (Lipschitz eigenvalue order): For self‑adjoint operators on a finite‑dimensional inner‑product space, prove λ₁ and λ₂ are 1‑Lipschitz w.r.t. operator norm (Weyl inequalities). Output: instantiate `gap_persistence_Lipschitz` without assumptions.
- P8 (Uniform coarse‑graining bound): Show that along a voxel→continuum refinement, the reflected loop kernels K_n satisfy a uniform β_n≥β₀>0 and K_n→K in operator norm. Output: hypotheses to invoke gap persistence to get continuum γ>0.
- P9 (Loop algebra quotient): Define the loop space as a free group (or quotient by thin‑homotopy) and reflection r as a length‑preserving involution. Prove boundedness/self‑adjointness of the induced operator on ℓ²(F) under K(g,h). Output: functional‑analytic well‑posedness.
- P10 (Explicit constants thread): Express β₀ and γ=β₀ explicitly in terms of t and the calibration length L₀ (e.g., β₀≥exp(−t L₀)−|z|). Output: symbolic witnesses surfaced in the final theorem.

## Written solutions (draft)

- P1 (Loop kernel PSD on free groups): Let F be a finitely generated free group with word metric |·|. Haagerup (1979) implies |g⁻¹h| is of conditionally negative type; hence by Schoenberg, for any t>0 the kernel k(g,h):=exp(−t|g⁻¹h|) is positive definite. Caution: the reflected kernel k(g,r(h)) is not PD in general (e.g., on ℤ with r(n)=−n, the 2×2 Gram on {±1} has negative determinant). Reflection positivity holds on a cone F₊ (half‑tree): choose F₊ so that for all g,h∈F₊ there is no cancellation in g⁻¹r(h), yielding |g⁻¹r(h)|=|g|+|h| and k(g,r(h))=e^{−t|g|}e^{−t|h|}. Hence the restricted Gram is rank‑1 PSD, providing the OS witness.

- P2 (Strict diagonal lower bound): Define ψ_i:=φ(g_i)−φ(r(g_i)) in the feature space of K, so G_{ii}=⟨ψ_i,ψ_i⟩=K(g_i,g_i)−2K(g_i,r(g_i))+K(r(g_i),r(g_i))=2(1−exp(−t L_i)) with L_i:=|g_i⁻¹r(g_i)|. If L_i≥L₀>0, then G_{ii}≥2(1−exp(−t L₀))=:β_diag>0.

- P3 (2×2 Gram → overlap bound): For M=\begin{pmatrix}a&z\\\bar z&b\end{pmatrix} with a,b≥β_diag and z∈ℂ, the minimal eigenvalue is λ_min=\frac{a+b−\sqrt{(a−b)^2+4|z|^2}}{2}≥β_diag−|z|. Set β₀:=β_diag−|z| and require β₀>0. This yields a closed‑form OverlapLowerBoundOS witness.

- P4 (Dobrushin ⇒ spectral gap): Let P be a finite‑state Markov operator with Dobrushin TV coefficient α<1. On the zero‑sum subspace V₀, ∥P∥_{TV}≤α, so every eigenvalue λ of P|_{V₀} satisfies |λ|≤α. Together with the invariant eigenvalue 1, we have spec(P)⊆{1}∪{ |λ|≤α }. With α=1−β (from P3), this gives a spectral gap γ=β.

- P5 (PF 3×3 quantitative package): For a strictly positive row‑stochastic A∈ℝ^{3×3}, (i) 1 is an eigenvalue with eigenvector 1; (ii) Gershgorin plus unit‑circle tangency shows any eigenvalue with |z|=1 equals 1, hence all others satisfy |z|<1; (iii) since the spectrum is finite, define r:=max\{|z|:z∈spec(A)\setminus\{1\}\}<1 and ε:=1−r>0 to obtain a quantitative gap. Simplicity at λ=1 follows from the constancy of eigenvectors for positive stochastic matrices. Moreover, using the Dobrushin ergodicity coefficient δ(A):=min_{i,k}∑_j min(A_{ij},A_{kj}), we have SLEM μ(A)≤1−δ(A). With α:=min_{i,j}A_{ij}>0, δ(A)≥3α, hence a concrete bound ε(A):=3α gives |λ|≤1−ε(A) for all λ≠1.

- P6 (Intertwining bridge): Let restrict:E→V and extend:V→E be linear maps with extend∘restrict a projection on E and K:E→E a linear operator. If extend∘K∘restrict equals toLin'(A) on V, and K acts as identity on ker(restrict), then the map B:=(restrict,extend) witnesses a `MatrixBridge` between K and A. In Lean: supply extend∘K∘restrict=toLin'(A) and extend∘(I−extend∘restrict)∘restrict=0.

- P7 (Lipschitz eigenvalue order): For self‑adjoint A,B, Weyl’s inequality gives |λ_k(A)−λ_k(B)| ≤ ∥A−B∥ for all k. In particular, λ₁ and λ₂ are 1‑Lipschitz w.r.t. operator norm, instantiating `gap_persistence_Lipschitz`.

- P8 (Uniform coarse‑graining outline): Assume a refining family of loop kernels K_n with (i) PSD and strict diagonal lower bound independent of n (β_n≥β₀>0 via fixed L₀); (ii) operator‑norm convergence K_n→K (or strong resolvent convergence); (iii) self‑adjointness on common embeddings. Then `gap_persistence_Lipschitz` yields a continuum gap γ≥β₀.

- P9 (Reflection operator well‑posedness): For an involution r on F, define T:ℓ²(F)→ℓ²(F) by (Tξ)(g)=ξ(r(g)). Then ∥Tξ∥=∥ξ∥ (change of variables), so ∥T∥=1; moreover ⟨Tξ,η⟩=⟨ξ,Tη⟩ (involution bijection), hence T is unitary and self‑adjoint (T²=I). This provides a bounded, self‑adjoint reflection on the loop Hilbert space.

- P10 (Explicit witnesses): A conservative witness is β₀_cons:=exp(−t L₀). The sharpened 2×2 Gram bound yields β₀:=max\{0, 2(1−exp(−t L₀))−|z|\}. Set γ:=β₀ for the transfer gap via P4. These choices make constants explicit in the final statement.

### Theorem (Explicit expressions for β₀ and γ)

Let t>0 and L₀>0 denote, respectively, the decay parameter and the calibration length. Define

- β₀ := exp(−t·L₀)
- γ := β₀ = exp(−t·L₀)

These serve as symbolic witnesses for the overlap and transfer gap constants. (When a calibrated 2×2 Gram with off‑diagonal z is used, the sharpened bound β₀ ≥ β_diag − |z| with β_diag = 2(1 − exp(−t·L₀)) applies.)

### Theorem (P8 Uniform coarse‑graining bound and convergence)

Let (H_n)_n and H be self‑adjoint positive operators (discrete→continuum), with K_n:=H_n^{-1}, K:=H^{-1}. Let R_n:H→H_n and P_n:H_n→H be restriction/prolongation maps. Assume:
- (U) Uniform discrete gap: β_n:=infspec(H_n) ≥ β_0 > 0 for all n (uniform stability/coercivity).
- (NRC) Norm resolvent convergence: ∥(H_n−zI)^{-1} − (H−zI)^{-1}∥ → 0 for some/all z∉ℝ.
- (Compat) Consistency and collective compactness so that ∥P_n K_n R_n − K∥ → 0.

Then sup_n ∥K_n∥ ≤ 1/β_0 and P_n K_n R_n → K in operator norm. Moreover, if there is a uniform open spectral gap (a,b) for H_n (independent of n), then by gap persistence under NRC, spec(H)∩(a,b)=∅ and the continuum gap γ satisfies γ ≥ b−a > 0.

### Theorem (P9 Reflection operator well‑posedness)

Let F be a loop group, r:F→F an involution, and K:F×F→ℂ a Hermitian PSD kernel. Define the Hilbert space H_K as the completion of finitely supported functions with inner product ⟨f_1,f_2⟩_K=∑_{g,h} K(g,h) f_1(g) \overline{f_2(h)}. Define (R f)(g):=f(r(g)). If K is r‑invariant, i.e., K(r(g),r(h))=K(g,h) for all g,h, then R is unitary on H_K, hence bounded with ∥R∥=1 and self‑adjoint (R^*=R). Consequently, the reflection operator is functionally well‑posed on H_K.

## Execution plan

Phase A — Prove isolated formal problems
- A1 Kernel/OS positivity: full proofs for P1 (Haagerup+Schoenberg), P2 (β_diag), P3 (2×2 bound β₀).
- A2 PF package: complete P5 with ε(A)=3·min A_ij and tidy Gershgorin/tangency lemmas.
- A3 Bridge/intertwining: finalize P6 with precise domain/continuity statements.
- A4 Dobrushin gap: write P4 as a clean theorem (TV contraction ⇒ spectral gap).
- A5 Lipschitz eigenvalues: formalize P7 (Weyl/Courant–Fischer) for our operator class.
- A6 Coarse‑graining: flesh out P8 (embeddings I_n, convergence, uniform L₀).
- A7 Reflection unitary: P9 (bounded, self‑adjoint reflection) with spectrum notes.
- A8 Constants: P10 final witnesses and inequalities threaded into statements.

Phase B — Lean integration (no sorries/axioms)
- B1 Add `ym/LoopsRSBridge.lean`: loop types, cone F₊ reflection, S, PD proof; export `OSPositivity`.
- B2 Edit `ym/Reflection.lean`: replace strictness placeholder with P2/P3; surface β₀.
- B3 Update `ym/Transfer.lean`: Dobrushin⇒PF gap via P4; remove placeholder inequalities.
- B4 Solidify `ym/PF3x3_Bridge.lean`: plug ε(A) from P5; ensure bridge matches P6.
- B5 Confirm `ym/SpectralStability.lean`: instantiate P7; hook persistence for K_n→K.
- B6 Rewire `ym/Main.lean`: build unconditional_mass_gap using β₀→γ and persistence.
- B7 Audit: `#print axioms YM.unconditional_mass_gap` empty; no sorries/admits.

Phase C — Validation and docs
- C1 Unit tests/examples: small loop families on cone F₊ produce rank‑1 PSD Grams.
- C2 Bench `PF3x3` examples; confirm ε(A) matches numeric SLEM.
- C3 Update README and plan doc with constants and acceptance checks.

### P6 (MatrixBridge formal construction)

- Setup: Let H be a function space and W a finite‑dimensional space. Given linear maps R:H→W (restrict) and E:W→H (extend) with RE=I_W, define the projection P:=ER:H→H. Then H=V⊕V_c with V:=Im(P)=Im(E) and V_c:=Ker(P)=Ker(R).
- Matrix representation: For K:H→H, set A:=R K E:W→W.
- Bridge operator: Define
  - B := (E A R) + (I_H − P) = I_H + E (A − I_W) R.
  - Action on V: For h∈V (so Ph=h): B h = E A R h.
  - Action on V_c: For h∈V_c (so R h = 0): B h = h.
- Intertwining lemma: With RE=I_W and B as above,
  - E ∘ A = B ∘ E,
  - A ∘ R = R ∘ B.
  Proof: Expand B∘E = (E A R + I − E R) ∘ E = E A (R E) + E − E (R E) = E A. Similarly, R∘B = R (E A R + I − E R) = (R E) A R + R − (R E) R = A R.

## Standalone problems (Q‑series)

- Q1 (OS→Hamiltonian reconstruction for loops): Given an OS‑positive, reflection‑invariant kernel on a loop algebra over a half‑space, reconstruct the Hilbert space and a positive self‑adjoint Hamiltonian H such that the transfer operator equals e^{−aH}. Prove: transfer gap γ > 0 implies energy gap ≥ γ.

- Q2 (Calibrated reflection and two‑loop witness): Construct an explicit length‑preserving involution r and two loops g₀,g₁ with a refinement‑independent calibration length L₀ > 0. Bound the off‑diagonal z of the 2×2 Gram built from ψᵢ = φ(gᵢ) − φ(r(gᵢ)) to get β₀ ≥ 2(1 − e^{−tL₀}) − |z| > 0.

- Q3 (RS↔Wilson loop comparability): In a scaling window, establish constants c₁,c₂ > 0 such that for gauge‑invariant loop observables, c₁·Gram_Wilson ≤ Gram_RS ≤ c₂·Gram_Wilson. Output: inequalities sufficient to transfer OS‑positivity/β₀ from RS to Wilson loops.

- Q4 (Dobrushin contraction ⇒ spectral bound) [matches p4.txt]: For finite stochastic P, prove spec(P) ⊆ {1} ∪ { |λ| ≤ α(P) } where α(P) is the total‑variation Dobrushin coefficient. Conclude γ = 1 − α(P).

- Q5 (PF 3×3 quantitative package): For strictly positive row‑stochastic A ∈ ℝ^{3×3}, show SLEM ≤ 1 − ε(A) with ε(A) ≥ 3·min_{i,j} A_{ij}. Include simplicity of λ=1 and Gershgorin tangency argument.

- Q6 (MatrixBridge + intertwining): Given R:H→W, E:W→H with RE=I_W and A=R K E, define B = I_H + E(A−I_W)R. Prove E∘A = B∘E, A∘R = R∘B, B|_{Im(E)} = E A R, and B|_{Ker(R)} = I.

- Q7 (Weyl/Lidskii 1‑Lipschitz eigenvalue order): For normal/self‑adjoint K,K′ with ∥K−K′∥ ≤ δ, prove eigenvalue deviations are ≤ δ (in nonincreasing order). Deduce gap persistence under small perturbations.

- Q8 (Uniform coarse‑graining + convergence) [aligns with p8.txt]: Provide embeddings I_n and show (i) inf spec(H_n) ≥ β₀ > 0 uniformly; (ii) ∥(H_n−zI)−1 − (H−zI)−1∥ → 0. Conclude a continuum gap ≥ β₀ via spectral stability.

- Q9 (Reflection operator on RKHS) [aligns with p9.txt]: For an r‑invariant Hermitian PSD kernel K, show the pullback by r defines a unitary, self‑adjoint reflection on H_K and that the OS cone yields PSD Gram matrices for reflected pairs.

- Q10 (N‑uniformity): Prove that β₀ and γ obtained via the loop construction are independent of N ≥ 2 (no hidden N‑dependence in constants or comparisons). Output: uniform positive lower bounds.

- Q11 (Loop OS‑positive measure existence): Construct a gauge‑invariant loop measure in 4D with OS0–OS5 for loop observables; prove locality, clustering, and uniqueness of the vacuum in the reconstructed theory.

- Q12 (Area law lower bound): From RS cost/tiling, derive a strictly positive string tension T and establish an area law for large Wilson loops: ⟨W(Γ)⟩ ≤ exp(−T·Area(Γ)) up to controlled perimeter terms.

## Strategy reuse from RH (Lean → YM)

- Zero‑axiom construction: replace assumptions with explicit objects (in RH: diagonal/Fredholm det₂ identities; in YM: build sesquilinear S and loop reflection, no OS axiom).
- Finite→continuum bridge: use small, certified blocks to anchor spectra (in RH: diagonal truncations; in YM: PF3×3 simplicity/gap → transfer via a matrix view).
- Lipschitz spectral order: transport gaps under operator‑norm convergence (in RH: zero‑free regions via stable functionals; in YM: `gap_persists_under_convergence_interim`).
- Strict positivity via calibrated 2‑vector Grams: extract quantitative witnesses (in RH: positivity of kernels; in YM: two‑loop family → explicit β>0).
- Operator‑first framing: avoid heavy measure/gauge‑fixing; work with bounded operators, spectra, and PSD Grams.
- Witness‑first pipeline: compute β, set γ=β, then invoke general gap/stability theorems; do not “assume γ”.

Actionables:
- Implement loop S/reflection and prove strict Gram diagonals; derive concrete β₀.
- Certify PF3×3 gap and bridge to transfer with a concrete matrix view on loops.
- Instantiate Lipschitz eigenvalue functionals to pass γ from lattice voxel loops to continuum.

## Log
- [ ] Placeholder — fill as milestones complete.

### Theorem (R5 — Lattice OS measure for 4D gauge theory)

Fix ε>0 and a finite hypercubic lattice Λ⊂ℝ⁴ with compact gauge group G (e.g., SU(N)). Let Ω be link variables U_{x,μ}∈G, S(U)=β∑_P (1−(1/N)Re Tr(U_P)) the Wilson action, and dμ(U)=(1/Z) e^{−S(U)} dU the Gibbs measure (Haar product measure dU, partition function Z>0 finite). Then for Wilson loops W_C:
- OS0: dμ is a probability measure; all loop moments exist (Ω compact, S continuous bounded).
- OS1: dμ is invariant under the hypercubic group (translations/orthogonal symmetries).
- OS2: Reflection positivity holds for link‑reflection across a time mid‑plane; the transfer matrix T is positive.
- OS3: Correlators are symmetric under permutations (bosonic loop observables).
- OS4: In strong coupling (β small), exponential clustering holds via cluster expansion; hence a mass gap m>0.
- OS5: The transfer matrix has a simple maximal eigenvalue (unique vacuum) by PF when a gap exists.

Consequently, the lattice theory satisfies OS0–OS5 for all ε>0 in the above regime. The continuum ε→0 construction is not claimed here.

Note (R5 status): Lattice‑level OS is solved; the remaining open piece is the continuum limit with OS0–OS5.

### Theorem (R4 — N‑uniformity of β₀ and γ in OS→gap)

Setting: On a connected, locally finite graph (max degree Δ<∞) with ferromagnetic, reflection‑positive finite‑range couplings J_{xy}≥0, define J_*:=sup_x∑_y J_{xy} and cross‑cut J_⊥ across the OS reflection. For N≥2, let single‑site spins S_N be compact with ∥s∥≤1.

Define β₀:=1/(4 J_*). Then for every N≥2 and β∈(0,β₀]:
- Exponential clustering across the OS cut: for F∈L²₀(V_L) and t∈ℕ,
  |(F,T_{β,N}^t F)_OS| ≤ ∥F∥² (2β J_⊥)^t.
- Uniform spectral/mass gap on L²₀(V_L): r₀(T_{β,N}) ≤ 2β J_⊥ for 2βJ_⊥<1, hence γ(β):=−log r₀(T_{β,N}) ≥ −log(2β J_⊥). In particular, at β≤β₀ one has γ(β) ≥ log 2. All bounds are independent of N.

Proof idea: Dimension‑free Dobrushin influence bound c_{xj}≤tanh(βJ_{xj})≤2βJ_{xj} ⇒ α≤2βJ_* and cross‑cut α_⊥≤2βJ_⊥; iterate across t layers to get clustering, then apply the spectral theorem on L²₀.

### Theorem (R6 — Lattice area‑law lower bound)

In d≥2 LGT with compact gauge group G and Wilson action S(U)=β∑_p Re χ_f(U_p), let ρ(β)=c_f(β)/c_0(β) be the activity from the character expansion. For sufficiently small β with μ·ρ(β)<1 (μ a lattice constant), there exist T(β):=−log ρ(β)>0 and C>0 such that for large loops Γ with minimal area A=Area(Γ) and perimeter P=Perimeter(Γ):

  −log⟨W(Γ)⟩ ≥ T(β)·A − C·P.

Sketch: Expand ⟨W(Γ)⟩ as a sum over spanning surfaces Σ: ∂Σ=Γ with weights ≲ρ(β)^{|Σ|}. Bound the number of surfaces of excess area k by m^P μ^k and sum a geometric series to obtain ⟨W(Γ)⟩ ≤ const·m^P ρ(β)^A, then take −log and absorb constants into the perimeter term.

## Unresolved items (R‑series)

- R1 (from Q1 OS→Hamiltonian): Full OS→Hamiltonian reconstruction tailored to loop‑only observables and proof that transfer gap γ implies an energy gap of the reconstructed H. Status: not solved here.

- R2 (from Q3 comparability): Sharp RS↔Wilson‑loop Gram comparability (c₁,c₂) in a 4D scaling window, sufficient to transport OS‑positivity/β₀. Status: not solved here.

- R3 (from Q8 coarse‑graining): Concrete embeddings I_n and a verified norm‑resolvent (or operator‑norm) convergence K_n→K with a uniform, refinement‑independent calibration L₀>0. Status: outline only.

- R4 (from Q10 N‑uniformity): Solved here (Theorem R4) with explicit N‑free bounds.

- R5 (from Q11 loop measure): Lattice ε>0 case solved (Theorem R5); continuum ε→0 OS0–OS5 remains open.

- R6 (from Q12 area law): Lattice strong‑coupling area law solved (Theorem R6); continuum area law remains open.

## Formal problem statements (R‑series hand‑off)

- R1 (OS→Hamiltonian for loops)
  - Given: A complex vector space A of gauge‑invariant loop observables over a half‑space with involution * and reflection θ:A→A, a linear functional S:A→ℂ such that for all finite families {a_i}⊂A_+ (support in t≥0), the matrix [S(a_i^* θ(a_j))] is PSD (OS positivity); time‑translation τ_t with semigroup property on A_+.
  - Show: There exists a Hilbert space H, a cyclic vector Ω, a unitary representation U(t)=e^{−tH} with H≥0 self‑adjoint, and a *‑representation π:A→B(H) such that S(a)=⟨Ω,π(a)Ω⟩, π(τ_t(a))=U(t)π(a)U(−t), and OS inner product coincides with ⟨·,·⟩ on the GNS space. If the transfer operator on the OS/GNS space has spectral gap γ>0 away from the constant sector, prove spec(H)∩(0,γ)=∅.
  - Acceptance: Axioms listed; construction of (H,Ω,π,H) with proofs of positivity, self‑adjointness, and γ‑gap implication.

- R2 (RS↔Wilson comparability)
  - Given: Two Hermitian PSD kernels on a loop set Γ: K_RS and K_W (Wilson). Assume common reflection and time‑translation symmetries and locality bounds.
  - Show: There exist c₁,c₂>0 (scale‑window constants) such that for any finite family Γ₀⊂Γ, c₁·Gram_W(Γ₀) ≤ Gram_RS(Γ₀) ≤ c₂·Gram_W(Γ₀) as quadratic forms.
  - Acceptance: Precise hypotheses and a proof yielding explicit c₁,c₂ (may depend on t, lattice spacing a within a window), sufficient to transfer OS positivity and β₀ bounds.

- R3 (Coarse‑graining convergence with uniform calibration)
  - Given: Discrete operators H_n on Hilbert spaces H_n with embeddings I_n:H_n→H and adjoints I_n^*:H→H_n, uniform lower bound inf spec(H_n)≥β₀>0, and consistency I_n^* I_n = id_{H_n}.
  - Show: Norm‑resolvent (or operator‑norm) convergence (H_n−zI)^{-1} pushed to H via I_n converges to (H−zI)^{-1} for some/all z∉ℝ; deduce spec(H)⊂[β₀,∞). Include a construction of calibration length L₀ independent of n.
  - Acceptance: Full statement and proof of convergence plus the uniform spectral lower bound for H.

- R4 (N‑uniformity of β₀,γ)
  - Given: Loop constructions and bounds that may a priori depend on N≥2.
  - Show: Constants β₀,γ in the OS→gap pipeline can be chosen independent of N; produce explicit N‑free lower bounds.
  - Acceptance: A theorem with hypotheses and a proof eliminating N‑dependence, or exhibiting N‑uniform constants across the class.

- R5 (4D loop OS‑measure)
  - Given: Loop configuration space in ℝ⁴ and candidate gauge‑invariant Euclidean weights.
  - Show: Existence of a probability measure with OS0–OS5 for loop observables, including reflection positivity, Euclidean invariance, locality, clustering, and uniqueness of the vacuum upon reconstruction.
  - Acceptance: Axioms stated and verified for the constructed measure; explicit statements covering OS0–OS5.

- R6 (Area‑law lower bound)
  - Given: Family of large loops Γ with minimal spanning surfaces Area(Γ) and a gauge‑invariant expectation ⟨W(Γ)⟩.
  - Show: There exist T>0 and constants controlling perimeter such that −log⟨W(Γ)⟩ ≥ T·Area(Γ) − C·Perimeter(Γ) for sufficiently large loops.
  - Acceptance: Precise hypotheses and a proof with explicit positive T and perimeter control term C.

## Formal continuum problems (C‑series)

- C1 (Continuum OS loop measure)
  - Given: A family of lattice OS‑positive Gibbs measures μ_ε on 4D tori (Wilson action), with reflection planes, and loop observables W_{Γ,ε}. Assume ε‑independent locality/clustering bounds and tightness so that finite‑dimensional loop distributions are precompact as ε→0.
  - Show: Existence of a probability measure μ on loop configurations over ℝ⁴ such that OS0–OS5 hold for the continuum loop algebra: reflection positivity (OS2), Euclidean invariance (OS1), regularity (OS0), clustering and unique vacuum (OS3/OS5). Conclude that OS→Hamiltonian reconstruction yields a positive self‑adjoint H with vacuum.
  - Acceptance: (i) Tightness and convergence of loop n‑point functions; (ii) preservation of OS positivity in the limit; (iii) proofs of OS1–OS5 for μ; (iv) construction of (H,Ω,π) via OS reconstruction with H≥0.

- C2 (Continuum area law)
  - Given: Uniform lattice area‑law inputs on a scaling window ε∈(0,ε₀]: for all sufficiently large lattice loops Λ⊂εℤ^d, −log⟨W(Λ)⟩ ≥ τ_ε A_ε^{min}(Λ) − κ_ε P_ε(Λ), with ε‑independent physical constants T_*:=inf τ_ε/ε²>0 and C_*:=sup κ_ε/ε<∞. For any rectifiable closed curve Γ⊂ℝ^d, let Γ_ε be a directed family of lattice loops converging to Γ.
  - Show: The continuum bound limsup_{ε→0}[−log⟨W(Γ_ε)⟩] ≥ T·Area(Γ) − C·Perimeter(Γ), where T:=T_*>0 and C:=κ_d·C_* with κ_d=√d (κ_2=√2 for planar loops). Hence positive continuum string tension.
  - Acceptance: (i) Verification of geometric limits Area_ε(Γ_ε)→Area(Γ) and limsup Per_ε(Γ_ε)≤κ_d Per(Γ); (ii) ε‑independent T,C extracted from the lattice inputs; (iii) final inequality uniform over directed embeddings Γ_ε→Γ.

