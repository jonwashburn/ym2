/-
Prop-level stability interfaces (P2/P5) to keep the build green while the analytic proofs are finalized.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.NormedSpace.RCLike
import Mathlib.Tactic
import ym.EigenvalueOrder

noncomputable section

namespace YM

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕂 E] [CompleteSpace E]

/-- Spectral gap functional built from user-supplied ordered eigenvalue functionals. -/
def eigGap (lam1 lam2 : (E →L[𝕂] E) → ℝ) (T : E →L[𝕂] E) : ℝ :=
  lam1 T - lam2 T

/-- P2-style gap persistence statement, as an interface (no proof here). -/
def GapPersistence (lam1 lam2 : (E →L[𝕂] E) → ℝ) : Prop :=
  ∀ [FiniteDimensional 𝕂 E],
    ∀ {A : E →L[𝕂] E} {Aseq : ℕ → E →L[𝕂] E},
      IsSelfAdjoint A → (∀ n, IsSelfAdjoint (Aseq n)) →
      ∀ {δ : ℝ}, 0 < δ →
        (∀ n, eigGap lam1 lam2 (Aseq n) ≥ δ) →
        (∀ ε > 0, ∃ N, ∀ n ≥ N, ‖Aseq n - A‖ ≤ ε) →
        ∃ δ' > 0, eigGap lam1 lam2 A ≥ δ'

/-- P5 on a fixed ambient space `E` (interface form). -/
def GapPersistsUnderConvergence (lam1 lam2 : (E →L[𝕂] E) → ℝ) : Prop :=
  GapPersistence (𝕂:=𝕂) (E:=E) lam1 lam2

/-- P5 via embedding: given a lifted family on `E` with a uniform gap and convergence,
 the limit has a positive gap (interface form). -/
def GapPersistsViaEmbedding (lam1 lam2 : (E →L[𝕂] E) → ℝ) (lift : ℕ → E →L[𝕂] E) : Prop :=
  ∀ [FiniteDimensional 𝕂 E],
    ∀ {A : E →L[𝕂] E}, IsSelfAdjoint A →
    ∀ {δ : ℝ}, 0 < δ →
      (∀ n, eigGap lam1 lam2 (lift n) ≥ δ) →
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ‖(lift n) - A‖ ≤ ε) →
      ∃ δ' > 0, eigGap lam1 lam2 A ≥ δ'

/-- Lipschitz-based proof of P2: if `lam1, lam2` are 1-Lipschitz wrt operator norm
and a sequence has a uniform gap and converges in operator norm, then the limit
retains a positive gap. -/
theorem gap_persistence_Lipschitz
    (lam1 lam2 : (E →L[𝕂] E) → ℝ)
    (hLip : ∀ (X Y : E →L[𝕂] E),
      |lam1 X - lam1 Y| ≤ ‖X - Y‖ ∧ |lam2 X - lam2 Y| ≤ ‖X - Y‖)
    : GapPersistence (𝕂:=𝕂) (E:=E) lam1 lam2 := by
  intro _ A Aseq _ _ δ hδ hGap hConv
  have hδ4 : 0 < δ / 4 := by nlinarith
  obtain ⟨N, hN⟩ := hConv (δ/4) hδ4
  have hAN : ‖A - Aseq N‖ ≤ δ/4 := by
    have := hN N (Nat.le_refl N)
    simpa [norm_sub_rev] using this
  -- Per-eigenvalue Lipschitz one-sided bounds
  have h1_abs := (hLip A (Aseq N)).1
  have h2_abs := (hLip A (Aseq N)).2
  have h1' : lam1 A ≥ lam1 (Aseq N) - ‖A - Aseq N‖ := by
    have h := abs_le.mp h1_abs
    have hleft : -(‖A - Aseq N‖) ≤ lam1 A - lam1 (Aseq N) := h.1
    have := add_le_add_right hleft (lam1 (Aseq N))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev] using this
  have h2' : lam2 A ≤ lam2 (Aseq N) + ‖A - Aseq N‖ := by
    have h := abs_le.mp h2_abs
    have hright : lam2 A - lam2 (Aseq N) ≤ ‖A - Aseq N‖ := h.2
    have := add_le_add_right hright (lam2 (Aseq N))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev] using this
  have hComb : lam1 A - lam2 A ≥
      (lam1 (Aseq N) - ‖A - Aseq N‖) - (lam2 (Aseq N) + ‖A - Aseq N‖) := by
    linarith
  -- Re-express combined bound as a 2‖·‖ error on the gap
  have hLower2 : (lam1 (Aseq N) - lam2 (Aseq N)) - 2 * ‖A - Aseq N‖ ≤ lam1 A - lam2 A := by
    have : (lam1 (Aseq N) - ‖A - Aseq N‖) - (lam2 (Aseq N) + ‖A - Aseq N‖)
        ≤ lam1 A - lam2 A := hComb
    simpa [sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc] using this
  have hGapN : lam1 (Aseq N) - lam2 (Aseq N) ≥ δ := hGap N
  have hbound : 2 * ‖A - Aseq N‖ ≤ δ/2 := by
    have : ‖A - Aseq N‖ ≤ δ/4 := hAN
    nlinarith
  have hHalf : δ/2 ≤ δ - 2 * ‖A - Aseq N‖ := by nlinarith [hbound]
  have hChain : δ/2 ≤ lam1 A - lam2 A :=
    le_trans hHalf (by
      have : δ - 2 * ‖A - Aseq N‖ ≤ (lam1 (Aseq N) - lam2 (Aseq N)) - 2 * ‖A - Aseq N‖ := by
        have hGapN' : δ ≤ lam1 (Aseq N) - lam2 (Aseq N) := hGapN
        simpa using sub_le_sub_right hGapN' (2 * ‖A - Aseq N‖)
      exact le_trans this hLower2)
  exact ⟨δ/2, by nlinarith, by simpa [eigGap] using hChain⟩

/-- Wrapper: P2 on the fixed ambient space using the Lipschitz hypothesis. -/
theorem gap_persists_under_convergence_Lipschitz
    (lam1 lam2 : (E →L[𝕂] E) → ℝ)
    (hLip : ∀ (X Y : E →L[𝕂] E),
      |lam1 X - lam1 Y| ≤ ‖X - Y‖ ∧ |lam2 X - lam2 Y| ≤ ‖X - Y‖)
    : GapPersistsUnderConvergence (𝕂:=𝕂) (E:=E) lam1 lam2 :=
  gap_persistence_Lipschitz (𝕂:=𝕂) (E:=E) lam1 lam2 hLip

/-- P5 via embedding: treat the lifted family as a convergent family in `E`. -/
theorem gap_persists_via_embedding_Lipschitz
    (lam1 lam2 : (E →L[𝕂] E) → ℝ) (lift : ℕ → E →L[𝕂] E)
    (hLip : ∀ (X Y : E →L[𝕂] E),
      |lam1 X - lam1 Y| ≤ ‖X - Y‖ ∧ |lam2 X - lam2 Y| ≤ ‖X - Y‖)
    : GapPersistsViaEmbedding (𝕂:=𝕂) (E:=E) lam1 lam2 lift := by
  intro _ A _ δ hδ hGap hConv
  -- Reuse the convergence proof with `Aseq := lift` (no self-adjointness needed here)
  have hδ4 : 0 < δ / 4 := by nlinarith
  obtain ⟨N, hN⟩ := hConv (δ/4) hδ4
  have hAN : ‖A - lift N‖ ≤ δ/4 := by
    have := hN N (Nat.le_refl N)
    simpa [norm_sub_rev] using this
  have h1_abs := (hLip A (lift N)).1
  have h2_abs := (hLip A (lift N)).2
  have h1' : lam1 A ≥ lam1 (lift N) - ‖A - lift N‖ := by
    have h := abs_le.mp h1_abs
    have hleft : -(‖A - lift N‖) ≤ lam1 A - lam1 (lift N) := h.1
    have := add_le_add_right hleft (lam1 (lift N))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev] using this
  have h2' : lam2 A ≤ lam2 (lift N) + ‖A - lift N‖ := by
    have h := abs_le.mp h2_abs
    have hright : lam2 A - lam2 (lift N) ≤ ‖A - lift N‖ := h.2
    have := add_le_add_right hright (lam2 (lift N))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, norm_sub_rev] using this
  have hComb : lam1 A - lam2 A ≥
      (lam1 (lift N) - ‖A - lift N‖) - (lam2 (lift N) + ‖A - lift N‖) := by
    linarith
  have hLower2 : (lam1 (lift N) - lam2 (lift N)) - 2 * ‖A - lift N‖ ≤ lam1 A - lam2 A := by
    have : (lam1 (lift N) - ‖A - lift N‖) - (lam2 (lift N) + ‖A - lift N‖)
        ≤ lam1 A - lam2 A := hComb
    simpa [sub_eq_add_neg, two_mul, add_comm, add_left_comm, add_assoc] using this
  have hGapN : lam1 (lift N) - lam2 (lift N) ≥ δ := hGap N
  have hbound : 2 * ‖A - lift N‖ ≤ δ/2 := by
    have : ‖A - lift N‖ ≤ δ/4 := hAN
    nlinarith
  have hHalf : δ/2 ≤ δ - 2 * ‖A - lift N‖ := by nlinarith [hbound]
  have hChain : δ/2 ≤ lam1 A - lam2 A :=
    le_trans hHalf (by
      have : δ - 2 * ‖A - lift N‖ ≤ (lam1 (lift N) - lam2 (lift N)) - 2 * ‖A - lift N‖ := by
        have hGapN' : δ ≤ lam1 (lift N) - lam2 (lift N) := hGapN
        simpa using sub_le_sub_right hGapN' (2 * ‖A - lift N‖)
      exact le_trans this hLower2)
  exact ⟨δ/2, by nlinarith, by simpa [eigGap] using hChain⟩

/-- Specialization with the interim ordered eigenvalue functionals from `EigenvalueOrder`. -/
theorem gap_persists_under_convergence_interim
    : GapPersistsUnderConvergence (𝕂:=𝕂) (E:=E)
        EigenvalueOrder.lambda1 EigenvalueOrder.lambda2 :=
  gap_persists_under_convergence_Lipschitz (𝕂:=𝕂) (E:=E)
    EigenvalueOrder.lambda1 EigenvalueOrder.lambda2
    (fun X Y => EigenvalueOrder.P1_Lipschitz (X:=X) (Y:=Y))

/-- Specialization of the embedding variant with the interim functionals. -/
theorem gap_persists_via_embedding_interim (lift : ℕ → E →L[𝕂] E)
    : GapPersistsViaEmbedding (𝕂:=𝕂) (E:=E)
        EigenvalueOrder.lambda1 EigenvalueOrder.lambda2 lift :=
  gap_persists_via_embedding_Lipschitz (𝕂:=𝕂) (E:=E)
    EigenvalueOrder.lambda1 EigenvalueOrder.lambda2 lift
    (fun X Y => EigenvalueOrder.P1_Lipschitz (X:=X) (Y:=Y))

/-- Specialization with Courant–Fischer functionals, assuming their 1‑Lipschitz property. -/
theorem gap_persists_under_convergence_CF
    (hLipCF : ∀ (X Y : E →L[𝕂] E),
      |EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) X - EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) Y| ≤ ‖X - Y‖ ∧
      |EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) X - EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) Y| ≤ ‖X - Y‖)
    : GapPersistsUnderConvergence (𝕂:=𝕂) (E:=E)
        (fun T => EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) T)
        (fun T => EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) T) :=
  gap_persists_under_convergence_Lipschitz (𝕂:=𝕂) (E:=E)
    (fun T => EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) T)
    (fun T => EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) T)
    (by
      intro X Y
      simpa using hLipCF X Y)

/-- Embedding variant specialized to Courant–Fischer functionals, with Lipschitz as hypothesis. -/
theorem gap_persists_via_embedding_CF (lift : ℕ → E →L[𝕂] E)
    (hLipCF : ∀ (X Y : E →L[𝕂] E),
      |EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) X - EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) Y| ≤ ‖X - Y‖ ∧
      |EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) X - EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) Y| ≤ ‖X - Y‖)
    : GapPersistsViaEmbedding (𝕂:=𝕂) (E:=E)
        (fun T => EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) T)
        (fun T => EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) T) lift :=
  gap_persists_via_embedding_Lipschitz (𝕂:=𝕂) (E:=E)
    (fun T => EigenvalueOrder.lambda1_CF_alias (𝕂:=𝕂) (E:=E) T)
    (fun T => EigenvalueOrder.lambda2_CF_alias (𝕂:=𝕂) (E:=E) T) lift
    (by
      intro X Y
      simpa using hLipCF X Y)

end YM
