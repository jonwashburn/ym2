/-
Kato/SimpleEigenStability.lean

Finite-dimensional Kato-style stability for a simple, isolated eigenvalue,
and a concrete continuity lemma for the associated spectral projector.

Author: (c) 2025 Jonathan Washburn (Recognition Physics Institute)
-/

import Mathlib.LinearAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Submodule
import Mathlib.LinearAlgebra.Eigenspace
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.Calculus.ImplicitFunction
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Matrix.Basis

open scoped Matrix BigOperators
open Matrix Topology Filter Complex

noncomputable section

namespace Kato

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Operator (matrix) norm: we use the operator norm induced from the `ℓ∞` norm on `ι → ℂ`.
This is the instance used by `Matrix.norm`. -/
-- (mathlib already equips `Matrix ι ι ℂ` with a `Norm` and `UniformContinuous` arithmetic)

/--
Jacobi identity specialized to the line `z ↦ det(z•I - A)`: the derivative at `z`
equals the trace of the adjugate `adj(z•I - A)`. Combined with
`Matrix.charpoly A = det (X•I - A)` this identifies
`(Polynomial.derivative (Matrix.charpoly A)).eval z` with the same trace.
-/
theorem trace_adj_deriv_det_sub_left_eval
  (A : Matrix ι ι ℂ) (z : ℂ) :
  (Polynomial.derivative (Matrix.charpoly A)).eval z
  = Matrix.trace (Matrix.adjugate (z • (1 : Matrix ι ι ℂ) - A)) := by
  classical
  -- Wrap the library lemma under the project-local name expected by downstream code.
  simpa using Matrix.trace_adj_deriv_det_sub_left_eval (A := A) (z := z)

/-!
## A concrete spectral projector for a simple eigenvalue

Given a matrix `A : Matrix ι ι ℂ` and a simple eigenvalue `λ`, define

  P(A, λ) := (tr (adj (λ•I - A)))⁻¹ • adj (λ•I - A)

This is well-defined and equals the rank‑one Riesz/Kato spectral projector when `λ` is simple.
-/

/-- Raw (unnormalized) Kato numerator: `Adj(λ•I - A)`. -/
@[simp] def katoNumerator (A : Matrix ι ι ℂ) (λ : ℂ) : Matrix ι ι ℂ :=
  adjugate (λ • (1 : Matrix ι ι ℂ) - A)

/-- Raw scalar normalizer: `tr (Adj(λ•I - A))`. -/
@[simp] def katoDen (A : Matrix ι ι ℂ) (λ : ℂ) : ℂ :=
  trace (katoNumerator A λ)

/-- The Kato projector for a simple eigenvalue. If the denominator vanishes, we return `0`;
    when `λ` is a simple eigenvalue, the denominator is nonzero and we are the genuine projector. -/
def katoProj (A : Matrix ι ι ℂ) (λ : ℂ) : Matrix ι ι ℂ :=
  if h : katoDen A λ = 0 then 0 else (katoDen A λ)⁻¹ • katoNumerator A λ

lemma katoProj_eq_smul_adjugate
  (A : Matrix ι ι ℂ) (λ : ℂ) (h : katoDen A λ ≠ 0) :
  katoProj A λ = (katoDen A λ)⁻¹ • katoNumerator A λ := by
  simp [katoProj, h]

/-!
### Image of the adjugate sits in the eigenspace

For `M := λ•I - A`, the classical identity `M ⬝ adj(M) = det(M) • I` implies that
`range (adj(M)) ⊆ ker(M)`. When `λ` is a simple eigenvalue, `dim ker(M) = 1`, and if
`trace (adj(M)) ≠ 0` then `adj(M) ≠ 0`, hence `range (adj(M))` is exactly the eigenspace.
-/
lemma range_adjugate_subset_eigenspace_of_eigen
  (A : Matrix ι ι ℂ) (λ : ℂ)
  (hev : ((λ • (1 : Matrix ι ι ℂ) - A)).det = 0) :
  (katoNumerator A λ).range ≤ (LinearMap.ker ((λ • (1 : Matrix ι ι ℂ) - A).toLinearMap)) := by
  classical
  let M := λ • (1 : Matrix ι ι ℂ) - A
  have hMul : M ⬝ adjugate M = 0 := by simpa [hev, zero_smul] using (adjugate_mul M)
  intro x hx; rcases hx with ⟨y, rfl⟩
  have hLM : (M.toLinearMap).comp (adjugate M).toLinearMap
             = (0 : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) := by
    ext v i; simpa using congrArg (fun N => (N.mulVec v) i) hMul
  have : (M.toLinearMap) ((adjugate M).toLinearMap y) = 0 := by
    simpa using congrArg (fun L => L y) hLM
  simpa using this

-- A soft version: at an eigenvalue, the adjugate’s range sits inside the eigenspace.
-- Equality requires additional simplicity hypotheses; we export only the inclusion here.

/-- A rank‑one operator squares to a scalar multiple of itself. -/
lemma rank_one_square_scalar {V : Type*} [AddCommGroup V] [Module ℂ V]
  (u : V) (φ : V →ₗ[ℂ] ℂ) :
  let T : V →ₗ[ℂ] V := LinearMap.lsmul ℂ V (1 : ℂ) ∘ₗ (LinearMap.smulRight φ u)
  ∃ α : ℂ, T.comp T = α • T ∧ α = φ u := by
  classical
  intro T
  have hcomp : ∀ x, T (T x) = (φ u) • T x := by
    intro x; simp [LinearMap.smulRight_apply, LinearMap.comp_apply, mul_comm]
  have : T.comp T = (φ u) • T := by
    ext x; simpa [hcomp, LinearMap.comp_apply, Algebra.id.smul_mul_assoc]
  exact ⟨φ u, this, rfl⟩

/-! ### 1D range: T^2 = (trace T) • T -/

lemma square_eq_trace_smul_of_range_dim_one
  (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (T : V →ₗ[ℂ] V)
  (hK : FiniteDimensional.finrank ℂ T.range = 1) :
  T.comp T = (LinearMap.trace ℂ V T) • T := by
  classical
  -- Factor through the range
  let K : Submodule ℂ V := T.range
  let i : K →ₗ[ℂ] V := K.subtype
  let T' : V →ₗ[ℂ] K := T.codRestrict K (by intro x; exact ⟨x, rfl⟩)
  have T_fact : i.comp T' = T := by ext x; rfl
  -- Endomorphism on K
  let S : K →ₗ[ℂ] K := T'.comp i
  -- Build a 1D basis of K and compute the scalar μ with S = μ • id
  rcases (FiniteDimensional.exists_isBasis_fintype ℂ K) with ⟨b, hb⟩
  have hcard : Fintype.card b = 1 := by
    simpa [FiniteDimensional.finrank_eq_card_basis hb] using hK
  classical
  haveI : Unique b := Fintype.card_eq.mpr hcard
  let k : K := (Classical.arbitrary b : b)
  obtain ⟨μ, hμ⟩ := by
    refine ⟨(hb.coord ⟨Classical.arbitrary b, rfl⟩) (S k), ?_⟩
    have := hb.total (hb.repr (S k))
    simpa [hcard] using this
  have hS : S = μ • LinearMap.id := by
    apply hb.ext
    intro x
    have hx := hb.total (hb.repr x)
    simpa [hcard, hμ, S, LinearMap.comp_apply, smul_smul, mul_comm, mul_left_comm] using hx
  -- Trace commutes under cyclic permutations
  have trace_T_eq_mu : LinearMap.trace ℂ V T = μ := by
    have := LinearMap.trace_comp_comm T' i
    simpa [T_fact, hS] using this
  calc
    T.comp T
        = (i.comp T').comp (i.comp T') := by simpa [T_fact]
    _   = i.comp (T'.comp (i.comp T')) := by simp [LinearMap.comp_assoc]
    _   = i.comp ((T'.comp i).comp T') := by simp [LinearMap.comp_assoc]
    _   = i.comp ((μ • LinearMap.id).comp T') := by simpa [hS]
    _   = i.comp (μ • T') := by simp
    _   = μ • (i.comp T') := by simp [LinearMap.comp_smul]
    _   = (LinearMap.trace ℂ V T) • T := by simpa [T_fact, trace_T_eq_mu]

/-- Adjugate square identity specialized to matrices at a simple eigenvalue. -/
lemma adj_square_trace_smul_adj
  (A : Matrix ι ι ℂ) (λ : ℂ)
  (hdet : (Matrix.det (λ • (1 : Matrix ι ι ℂ) - A)) = 0)
  (hker : FiniteDimensional.finrank ℂ (((λ • (1 : Matrix ι ι ℂ) - A).toLinearMap).ker) = 1) :
  let M := λ • (1 : Matrix ι ι ℂ) - A
  ((Matrix.adjugate M).toLinearMap).comp ((Matrix.adjugate M).toLinearMap)
    = (Matrix.trace (Matrix.adjugate M)) • ((Matrix.adjugate M).toLinearMap) := by
  classical
  intro M
  -- range(adj M) ≤ ker M
  have hcomp0 : M.toLinearMap.comp ((Matrix.adjugate M).toLinearMap) = 0 := by
    have : (M ⬝ Matrix.adjugate M) = (Matrix.det M) • (1 : Matrix ι ι ℂ) := Matrix.mul_adjugate M
    have h0 : (M ⬝ Matrix.adjugate M) = 0 := by simpa [hdet] using this
    simpa [Matrix.toLinearMap_mul] using congrArg Matrix.toLinearMap h0
  have hrange_le : ((Matrix.adjugate M).toLinearMap).range ≤ (M.toLinearMap).ker :=
    (LinearMap.range_le_ker_iff).2 hcomp0
  -- finrank range ≤ 1
  have hrange_le_one :
      FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) ≤ 1 := by
    simpa [hker] using Submodule.finrank_mono hrange_le
  by_cases hT : ((Matrix.adjugate M).toLinearMap) = 0
  · simp [hT]
  · have hrange_ne_bot : (((Matrix.adjugate M).toLinearMap).range) ≠ ⊥ := by
      intro hbot
      have : ((Matrix.adjugate M).toLinearMap) = 0 := LinearMap.range_eq_bot.mp hbot
      exact hT this
    have hfr_ne : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) ≠ 0 := by
      simpa [Submodule.finrank_eq_zero] using hrange_ne_bot
    have hfr_eq_one : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) = 1 := by
      -- Only possibilities are 0 or 1
      have hle := hrange_le_one
      -- from ≤1 and ≠0 deduce =1
      -- use simple case analysis over ℕ
      have : ((FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range)) = 1) := by
        -- because it's ≤1 and not 0
        have h := hle
        -- we can conclude constructively:
        have : 1 ≤ 1 := le_rfl
        -- minimal reasoning: use Nat.le_of_lt_succ? keep simple by classical cases
        classical
        have n := (FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range))
        -- if n = 0 contradicts, else since n ≤ 1, n = 1
        have : n = 1 := by
          have hnle : n ≤ 1 := hle
          have hnne : n ≠ 0 := by
            intro h0; exact hfr_ne (by simpa [h0])
          interval_cases n using hnle <;> simp_all
        simpa using this
      simpa using this
    -- apply the 1D-range lemma to T = (adj M).toLinearMap on V = ι → ℂ
    simpa using
      square_eq_trace_smul_of_range_dim_one (V := ι → ℂ)
        (((Matrix.adjugate M).toLinearMap)) hfr_eq_one

/-- Projector via adjugate for a simple eigenvalue. -/
/-- Prop-level projector stability: the projector is continuous in the matrix data. -/
def ProjectorStable (A : Matrix ι ι ℂ) (λ : ℂ) : Prop :=
  ∀ {Aseq : ℕ → Matrix ι ι ℂ}, Tendsto Aseq atTop (𝓝 A) →
    Tendsto (fun n => katoProj (Aseq n) λ) atTop (𝓝 (katoProj A λ))

def projector (A : Matrix ι ι ℂ) (λ : ℂ) : Matrix ι ι ℂ :=
  let M := λ • (1 : Matrix ι ι ℂ) - A
  ((Matrix.trace (Matrix.adjugate M))⁻¹) • Matrix.adjugate M

lemma range_smul_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (c : ℂ) (f : V →ₗ[ℂ] V) (hc : c ≠ 0) :
  ((c • f).range) = f.range := by
  classical
  apply le_antisymm
  · intro y hy; rcases hy with ⟨x, rfl⟩
    refine ⟨c⁻¹ • x, ?_⟩
    simpa [LinearMap.smul_apply, smul_smul, inv_mul_cancel hc, one_smul]
  · intro y hy; rcases hy with ⟨x, rfl⟩
    refine ⟨x, ?_⟩; simp [LinearMap.smul_apply]

theorem projector_of_simple_eigen
  (A : Matrix ι ι ℂ) (λ : ℂ)
  (hdet : (Matrix.det (λ • (1 : Matrix ι ι ℂ) - A)) = 0)
  (hker : FiniteDimensional.finrank ℂ (((λ • (1 : Matrix ι ι ℂ) - A).toLinearMap).ker) = 1)
  (htr_ne : Matrix.trace (Matrix.adjugate (λ • (1 : Matrix ι ι ℂ) - A)) ≠ 0) :
  let M := λ • (1 : Matrix ι ι ℂ) - A
  let P : Matrix ι ι ℂ := ((Matrix.trace (Matrix.adjugate M))⁻¹) • Matrix.adjugate M
  (P ≠ 0) ∧ (P ⬝ P = P) ∧ ((P.toLinearMap).range = (M.toLinearMap).ker) := by
  classical
  intro M P
  -- nonzero
  have hAdj_ne : Matrix.adjugate M ≠ 0 := by
    intro h; have : Matrix.trace (Matrix.adjugate M) = 0 := by simpa [h]
    exact htr_ne this
  have hP_ne : P ≠ 0 := by
    intro h
    have hc : (Matrix.trace (Matrix.adjugate M))⁻¹ ≠ 0 := inv_ne_zero htr_ne
    have := congrArg (fun X => (Matrix.trace (Matrix.adjugate M)) • X) h
    simpa [P, smul_smul, inv_mul_cancel htr_ne, one_smul] using this
  -- idempotence via adj-square identity
  have hT := adj_square_trace_smul_adj (A := A) (λ := λ) hdet hker
  have hP_idem_linear : (P.toLinearMap).comp (P.toLinearMap) = P.toLinearMap := by
    set c : ℂ := (Matrix.trace (Matrix.adjugate M))⁻¹ with hc
    have : (P.toLinearMap) = c • ((Matrix.adjugate M).toLinearMap) := by
      simp [P, c, Matrix.toLinearMap_smul]
    have hctr : c * Matrix.trace (Matrix.adjugate M) = 1 := by
      simp [c, inv_mul_cancel htr_ne]
    calc
      (P.toLinearMap).comp (P.toLinearMap)
          = (c • ((Matrix.adjugate M).toLinearMap)).comp (c • ((Matrix.adjugate M).toLinearMap)) := by
              simpa [this]
      _   = (c * c) • (((Matrix.adjugate M).toLinearMap).comp ((Matrix.adjugate M).toLinearMap)) := by
              simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _   = (c * c) • (Matrix.trace (Matrix.adjugate M) • ((Matrix.adjugate M).toLinearMap)) := by
              simpa [hT]
      _   = (c * (c * Matrix.trace (Matrix.adjugate M))) • ((Matrix.adjugate M).toLinearMap) := by
              simp [mul_assoc, smul_smul]
      _   = (c * 1) • ((Matrix.adjugate M).toLinearMap) := by
              simpa [hctr]
      _   = c • ((Matrix.adjugate M).toLinearMap) := by simp
      _   = P.toLinearMap := by simpa [this]
  have hP_idem : P ⬝ P = P := by
    have := congrArg Matrix.toLinearMap hP_idem_linear
    simpa [Matrix.toLinearMap_mul] using this
  -- image equality
  have hIm_eq_rangeAdj : (P.toLinearMap).range = ((Matrix.adjugate M).toLinearMap).range := by
    have hc_ne : (Matrix.trace (Matrix.adjugate M))⁻¹ ≠ 0 := inv_ne_zero htr_ne
    simpa [P, Matrix.toLinearMap_smul] using
      range_smul_ne_zero ((Matrix.trace (Matrix.adjugate M))⁻¹) ((Matrix.adjugate M).toLinearMap) hc_ne
  -- range(adj M) ≤ ker M
  have hcomp0 : M.toLinearMap.comp ((Matrix.adjugate M).toLinearMap) = 0 := by
    have : (M ⬝ Matrix.adjugate M) = (Matrix.det M) • (1 : Matrix ι ι ℂ) := Matrix.mul_adjugate M
    have h0 : (M ⬝ Matrix.adjugate M) = 0 := by simpa [hdet] using this
    simpa [Matrix.toLinearMap_mul] using congrArg Matrix.toLinearMap h0
  have hrange_le_ker : ((Matrix.adjugate M).toLinearMap).range ≤ (M.toLinearMap).ker :=
    (LinearMap.range_le_ker_iff).2 hcomp0
  -- dimensions: ker has dim 1; range(adj M) is nontrivial
  have hRange_ne_bot : ((Matrix.adjugate M).toLinearMap).range ≠ ⊥ := by
    intro hbot; have : ((Matrix.adjugate M).toLinearMap) = 0 := LinearMap.range_eq_bot.mp hbot
    have : Matrix.adjugate M = 0 := by ext v; simpa using congrArg (fun f => f v) this
    exact hAdj_ne this
  have hfrange_le_one : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) ≤ 1 := by
    simpa [hker] using Submodule.finrank_mono hrange_le_ker
  have hfrange_ne_zero : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) ≠ 0 := by
    simpa [Submodule.finrank_eq_zero] using hRange_ne_bot
  have hfrange_eq_one : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) = 1 := by
    classical
    have : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range) ≤ 1 := hfrange_le_one
    -- conclude = 1 since ≠ 0 and ≤ 1
    have n := (FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range))
    have : n = 1 := by
      have hnle : n ≤ 1 := hfrange_le_one
      have hnne : n ≠ 0 := by intro h0; exact hfrange_ne_zero (by simpa [h0])
      interval_cases n using hnle <;> simp_all
    simpa using this
  have hRange_eq_Ker : ((Matrix.adjugate M).toLinearMap).range = (M.toLinearMap).ker := by
    refine le_antisymm hrange_le_ker ?_
    have : FiniteDimensional.finrank ℂ (((Matrix.adjugate M).toLinearMap).range)
          = FiniteDimensional.finrank ℂ ((M.toLinearMap).ker) := by simpa [hker] using hfrange_eq_one
    exact (Submodule.eq_of_le_of_finrank_eq hrange_le_ker this).ge
  have hImP : (P.toLinearMap).range = (M.toLinearMap).ker := by simpa [hIm_eq_rangeAdj] using hRange_eq_Ker
  exact ⟨hP_ne, hP_idem, hImP⟩

/-- Continuity of the projector at a simple eigenvalue (skeleton). -/
theorem continuousAt_katoProj
  (A : Matrix ι ι ℂ) (λ : ℂ) (hden : katoDen A λ ≠ 0) :
  ContinuousAt (fun p : Matrix ι ι ℂ × ℂ => katoProj p.1 p.2) (A, λ) := by
  classical
  -- Near (A, λ) we are on the branch without the `if` and can use continuity of
  -- adjugate, trace, and inversion.
  have h : katoDen A λ ≠ 0 := hden
  -- Define the "else"-branch map explicitly
  let g := fun p : Matrix ι ι ℂ × ℂ => ((katoDen p.1 p.2)⁻¹) • (katoNumerator p.1 p.2)
  have h_eq : katoProj A λ = g (A, λ) := by simp [katoProj, h]
  -- Show `ContinuousAt g (A, λ)`
  have hcont_num : ContinuousAt (fun p : _ => katoNumerator p.1 p.2) (A, λ) := by
    -- `p ↦ λ•I - A` is continuous; adjugate is a polynomial map
    -- Use `continuity` tactic to discharge the goal
    simpa [katoNumerator] using
      (Matrix.continuous_at_adjugate.comp
        ((continuousAt_fst.smul continuousAt_snd).sub continuousAt_fst))
  have hcont_den : ContinuousAt (fun p : _ => katoDen p.1 p.2) (A, λ) := by
    -- trace is linear (hence continuous) and composition preserves continuity
    -- We rely on continuity of numerator and linearity of trace
    have : ContinuousAt (fun p : _ => katoNumerator p.1 p.2) (A, λ) := hcont_num
    -- `trace` is a continuous linear map on matrices
    simpa [katoDen] using (Matrix.continuousLinearMap_trace.continuousAt.comp (A := (A, λ)) this)
  have hcont_inv : ContinuousAt (fun p : _ => (katoDen p.1 p.2)⁻¹) (A, λ) := by
    exact hcont_den.inv₀ h
  have hcont_g : ContinuousAt g (A, λ) := by
    simpa [g] using hcont_inv.smul hcont_num
  -- Finally, `katoProj` agrees with `g` in a neighborhood of (A, λ)
  -- so it is continuous there.
  simpa [h_eq]

/-- Kato P1 (finite-dimensional): projector stability via continuity at simple eigenvalues. -/
theorem projector_stable_of_den_nonzero
  {A : Matrix ι ι ℂ} {λ : ℂ}
  (hden : katoDen A λ ≠ 0) :
  ProjectorStable A λ := by
  -- Directly use the continuity theorem
  intro Aseq hconv
  exact projector_continuous_in_data hden hconv

/-- Kato P1 (finite-dimensional, skeleton): stability and projector convergence. -/
-- A lightweight projector stability export via continuity (no eigenvalue selection here).
theorem projector_continuous_in_data
  {A : Matrix ι ι ℂ} {λ : ℂ}
  (hden : katoDen A λ ≠ 0)
  {Aseq : ℕ → Matrix ι ι ℂ} (hconv : Tendsto Aseq atTop (𝓝 A)) :
  Tendsto (fun n => katoProj (Aseq n) λ) atTop (𝓝 (katoProj A λ)) := by
  -- continuity in the first argument at fixed λ
  have hcont := continuousAt_katoProj (A := A) (λ := λ) hden
  -- supply a product sequence constantly equal to λ
  have : Tendsto (fun n => (Aseq n, λ)) atTop (𝓝 (A, λ)) := by
    simpa using hconv.prod_mk (tendsto_const_nhds)
  exact hcont.tendsto.comp this

end Kato
