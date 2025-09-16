## YM proof scaffold (modules, steps, acceptance)

### 0. Grounding (done or imported)
- R1 (OS→Hamiltonian for loops): theorem statement in `RS_YM_Plan.md` and `r1.txt`.
- R2 (RS↔Wilson): statement/proof in `r2.txt`.
- R3 (Coarse‑graining NRC): statement/proof in `r3.txt`.
- R4 (N‑uniformity): done (theorem in plan, full proof in `r4.txt`).
- R5 (Lattice OS): theorem in plan; continuum pending under C1.
- R6 (Lattice area law): theorem in plan; continuum pending under C2.
- C1/C2: formal continuum problems in `RS_YM_Plan.md` with acceptance checks.

### 1. Loop/OS layer
- Implement `ym/LoopsRSBridge.lean`:
  - Loop type, reflection, cone, OS Gram, PSD proof on cone.
  - Calibrated two‑loop family and diagonal strictness; compute β_diag.
  - 2×2 Gram bound → β₀ witness. Output: `OverlapWitness`.

### 2. Transfer/Dobrushin layer
- Implement `ym/Transfer.lean`:
  - Dobrushin coefficient from OS overlap; prove spec(P) ⊆ {1} ∪ {|λ|≤α}.
  - Export `GapWitness` with γ=β₀ and γ>0.

### 3. PF3×3 and bridge
- Fill `ym/PF3x3_Bridge.lean`:
  - Quantitative PF gap (ε(A)≥3·min A_ij) and simplicity.
  - MatrixBridge intertwining with loop transfer on a finite subspace.

### 4. Stability/persistence
- `ym/SpectralStability.lean`:
  - Weyl 1‑Lipschitz eigenvalue order.
  - NRC→gap persistence (use R3 structure).

### 5. Continuum
- C1: carry lattice OS to continuum OS0–OS5; reconstruct H≥0.
- C2: convert uniform lattice area law to continuum Area–Perimeter bound.

### 6. Main theorem
- `ym/Main.lean`: assemble β₀→γ, PF anchor, persistence; export `unconditional_mass_gap_statement`.

### Acceptance checks
- No sorries/axioms; `lake build` green.
- `#print axioms YM.unconditional_mass_gap_statement` empty.
- Constants surfaced: β₀, γ with explicit formulas/inequalities.

### Execution checklist (current status)
- [x] Loop cone and OS PSD (`LoopCone`, `osPSD_on_cone_of_factorized`).
- [x] Overlap witness export and OS adapter (`overlapWitnessHalf`, `os_overlap_of_witness`).
- [x] β₀→γ wiring in Transfer (`transfer_gap_from_overlap_witness`).
- [x] Calibrated two‑loop β_diag and |z| computation (explicit family → `TwoLoopParams`, `overlapFromParams`).
- [x] PF3×3 overlap extraction finalized and `KernelHasMatrixView` bridge (`matrix_overlap_from_pf3x3`, `pf_gap_from_pf3x3_bridge`).
- [x] Spectral stability wrappers (Lipschitz persistence) in `SpectralStability.lean`.
- [x] Unit checks/examples for OS PSD and β₀ extraction (see `LoopsRSBridge.lean`).
- [ ] Main assembly in `ym/Main.lean` to export `unconditional_mass_gap_statement`.


