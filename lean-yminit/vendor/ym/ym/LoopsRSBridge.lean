import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Basic
import ym.Scaffold
import ym.OSPositivity
import ym.Reflection

/-
Scaffold: Loop algebra and RS→OS bridge

This file defines minimal placeholders for a loop index type, reflection, and kernel notions,
so downstream modules can import a stable interface while we fill in the details.

Nothing here asserts any axioms; there are no theorems with incomplete proofs.
-/

namespace YM

/-- Notation/scope for sums. -/
open scoped BigOperators
open Finset

/-- Placeholder loop index (replace with concrete encoding). -/
structure Loop where
  id : Nat
deriving DecidableEq, Repr

/-- Time reflection on loops (stub; to be replaced by calibrated reflection). -/
def reflect (ℓ : Loop) : Loop := ℓ

/-- Kernel type over an index type. -/
abbrev Kernel (α : Type _) := α → α → Complex

/-- Finitely-supported functions on loops (to define OS Grams over). -/
abbrev FSFun (α : Type _) := α →₀ Complex

/-- OS Gram matrix entry for a kernel `K` and reflection `r` over finitely-supported functions. -/
def osInner {α : Type _} (r : α → α) (K : Kernel α) (f g : FSFun α) : Complex :=
  ∑ a in f.support, ∑ b in g.support, (Complex.conj (f a)) * K (r b) a * (g b)

/-- Finite-family OS Gram kernel: `GramOS r K f i j = K (r (f j)) (f i)`. -/
def GramOS {α ι : Type _} (r : α → α) (K : Kernel α) (f : ι → α) : ι → ι → Complex :=
  fun i j => K (r (f j)) (f i)

/-- A minimal β₀ witness record (overlap lower bound). -/
/-- Construct a conservative β₀ from a diagonal lower bound `bdiag` and an
off‑diagonal magnitude bound `z` using the 2×2 estimate β₀ ≥ bdiag − |z|.
This is a placeholder helper; the calibrated values will be provided upstream. -/
def mkBeta0FromDiagOff (bdiag z : Real) (hb : 0 < bdiag) (hz : 0 ≤ z)
    (hstrict : bdiag - z > 0) : OverlapWitness where
  beta0 := bdiag - z
  beta0_pos := hstrict

/-- Factorization property for an OS kernel (rank‑1 Gram on the cone). -/
def factorizableOSKernel {α : Type _} (r : α → α) (K : Kernel α) : Prop :=
  ∃ φ : α → Complex, ∀ a b, K (r b) a = (φ a) * Complex.conj (φ b)

/-- OS positivity on a cone `S` (functions supported in `S`). -/
def OSPsdOn {α : Type _} (r : α → α) (K : Kernel α) (S : Set α) : Prop :=
  ∀ f : FSFun α, f.support ⊆ S → 0 ≤ Complex.realPart (osInner r K f f)

/-- Rank‑1 factorization implies OS positivity (on any cone). -/
theorem osPSD_of_factorized {α : Type _}
    (r : α → α) (K : Kernel α)
    (h : factorizableOSKernel r K) : OSPsdOn r K (Set.univ : Set α) := by
  classical
  rcases h with ⟨φ, hφ⟩
  intro f _hs
  -- Expand double sum and factor it as x * conj x
  have hK : ∀ a b, K (r b) a = φ a * Complex.conj (φ b) := hφ
  have : osInner r K f f
      = (∑ a in f.support, Complex.conj (f a) * φ a)
        * Complex.conj (∑ a in f.support, Complex.conj (f a) * φ a) := by
    -- Rewrite K and factor sums
    simp [osInner, hK, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum, Finset.sum_mul]
  -- Real part equals squared norm, hence nonnegative
  have : Complex.realPart (osInner r K f f)
      = Complex.normSq (∑ a in f.support, Complex.conj (f a) * φ a) := by
    simpa [this, Complex.realPart_mul_conj]
  simpa [this] using (Complex.normSq_nonneg (∑ a in f.support, Complex.conj (f a) * φ a))

/-- Rank‑1 factorization implies PSD of the finite OS Gram `GramOS` for any finite family. -/
theorem gramOS_psd_of_factorized {α ι : Type _} [Fintype ι] [DecidableEq ι]
    (r : α → α) (K : Kernel α)
    (h : factorizableOSKernel r K) (f : ι → α)
    : YM.PosSemidefKernel (GramOS r K f) := by
  classical
  rcases h with ⟨φ, hφ⟩
  intro v
  -- Expand quadratic form and factor it as x * conj x
  have hK : ∀ a b, K (r b) a = φ a * Complex.conj (φ b) := hφ
  have : (∑ i, ∑ j, Complex.conj (v i) * (GramOS r K f i j) * (v j))
        = (∑ i, Complex.conj (v i) * φ (f i)) * Complex.conj (∑ j, Complex.conj (v j) * φ (f j)) := by
    simp [GramOS, hK, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]
  -- Real part is a squared norm
  have hRe : (∑ i, ∑ j, Complex.conj (v i) * (GramOS r K f i j) * (v j)).re
        = Complex.normSq (∑ i, Complex.conj (v i) * φ (f i)) := by
    simpa [this]
  simpa [hRe] using (Complex.normSq_nonneg (∑ i, Complex.conj (v i) * φ (f i)))

/-- A simple loop length surrogate. -/
def loopLen (ℓ : Loop) : Nat := ℓ.id

/-- Cone of loops used for OS reflection (placeholder: all loops). -/
def LoopCone : Set Loop := Set.univ

/-- Calibrated reflection preserves length on the cone. -/
theorem reflect_preserves_length {ℓ : Loop} (hℓ : ℓ ∈ LoopCone)
    : loopLen (reflect ℓ) = loopLen ℓ := rfl

/-- Rank‑1 factorization implies OS PSD on the loop cone. -/
theorem osPSD_on_cone_of_factorized (K : Kernel Loop)
    (h : factorizableOSKernel reflect K) : OSPsdOn reflect K LoopCone := by
  -- Since `LoopCone = univ`, this follows directly from the univ result
  simpa [LoopCone] using (osPSD_of_factorized (α:=Loop) reflect K h)

/-- Map an overlap witness to an OS overlap lower bound (requires β₀ ≤ 1). -/
theorem os_overlap_of_witness {K : YM.TransferKernel} (w : OverlapWitness)
    (hle : w.beta0 ≤ 1) : YM.OverlapLowerBoundOS K w.beta0 := by
  exact ⟨w.beta0_pos, hle⟩

/-- Concrete OS overlap from the conservative half‑overlap witness. -/
theorem os_overlap_half {K : YM.TransferKernel}
    : YM.OverlapLowerBoundOS K overlapWitnessHalf.beta0 := by
  have : overlapWitnessHalf.beta0 ≤ 1 := by norm_num
  exact os_overlap_of_witness (K:=K) overlapWitnessHalf this

/-- Parameters for a calibrated two‑loop family producing a diagonal bound and
an off‑diagonal magnitude bound. -/
structure TwoLoopParams where
  L0 : Real
  t  : Real
  z  : Real
  hL0 : 0 < L0
  ht  : 0 < t
  hz  : 0 ≤ z
  hstrict : z < 2 * (1 - Real.exp (-(t * L0)))

/-- Diagonal lower bound β_diag = 2 (1 − e^{−t L0}). -/
def betaDiag (p : TwoLoopParams) : Real := 2 * (1 - Real.exp (-(p.t * p.L0)))

lemma betaDiag_pos (p : TwoLoopParams) : 0 < betaDiag p := by
  unfold betaDiag
  have hx : 0 < p.t * p.L0 := mul_pos p.ht p.hL0
  have : Real.exp (-(p.t * p.L0)) < 1 := by
    -- exp is strictly increasing, so exp(-x) < 1 for x > 0
    have : 0 < -(p.t * p.L0) → Real.exp (-(p.t * p.L0)) < Real.exp 0 := by
      intro h; simpa using Real.exp_lt_exp.mpr h
    have hneg : -(p.t * p.L0) < 0 := by simpa using (neg_neg_of_pos.mpr hx)
    have : Real.exp (-(p.t * p.L0)) < Real.exp 0 :=
      by simpa [lt_of_le_of_ne] using Real.exp_lt_exp.mpr hneg
    simpa using this
  have : 0 < 1 - Real.exp (-(p.t * p.L0)) := by linarith
  have : 0 < 2 * (1 - Real.exp (-(p.t * p.L0))) := by nlinarith
  simpa [betaDiag] using this

/-- Produce an `OverlapWitness` from calibrated parameters and an off‑diagonal bound z.
Requires `z < β_diag` for strict positivity. -/
def overlapFromParams (p : TwoLoopParams) : OverlapWitness := by
  have hb : 0 < betaDiag p := betaDiag_pos p
  have hz0 : 0 ≤ p.z := p.hz
  have hstrict : betaDiag p - p.z > 0 := by
    have : p.z < betaDiag p := by simpa [betaDiag] using p.hstrict
    linarith
  exact mkBeta0FromDiagOff (bdiag := betaDiag p) (z := p.z) hb hz0 hstrict

/-! Simple unit examples -/

/-- Unit example: constant rank‑1 factorization yields OS PSD on the loop cone. -/
example : OSPsdOn reflect (fun _ _ => (1 : Complex)) LoopCone := by
  have h : factorizableOSKernel reflect (fun _ _ => (1 : Complex)) := by
    refine ⟨(fun _ => (1 : Complex)), ?_⟩
    intro a b; simp
  simpa using osPSD_on_cone_of_factorized (K := (fun _ _ => (1 : Complex))) h

/-- Unit example: positivity of β₀ from calibrated two‑loop parameters. -/
example (p : TwoLoopParams) : 0 < (overlapFromParams p).beta0 := by
  simpa using (overlapFromParams p).beta0_pos

/-- A concrete conservative overlap witness (placeholder). -/
def overlapWitnessHalf : OverlapWitness where
  beta0 := (1 : Real) / 2
  beta0_pos := by norm_num

/‑‑
Comparability adapters (explicit constants):

We compare two OS Grams `G_RS` and `G_W` via scalar lower/upper envelopes against the
ℓ² norm. Define the real quadratic forms (real parts of complex quadratics)

  Q_RS(v) = Re( ∑ᵢⱼ conj vᵢ · G_RSᵢⱼ · vⱼ ),
  Q_W (v) = Re( ∑ᵢⱼ conj vᵢ · G_Wᵢⱼ  · vⱼ ),

and assume scalar bounds
  l_RS * ‖v‖₂² ≤ Q_RS(v) ≤ u_RS * ‖v‖₂²,
  l_W  * ‖v‖₂² ≤ Q_W (v) ≤ u_W  * ‖v‖₂²,
with 0 < l_W ≤ u_W and 0 < l_RS ≤ u_RS.

Then for all v,
  (l_RS / u_W) · Q_W(v) ≤ Q_RS(v) ≤ (u_RS / l_W) · Q_W(v).

We expose this as a reusable adapter; concrete `l_·, u_·` can be provided from
Gershgorin/Schur constants (e.g., onsite b, off‑sum S ⇒ l = b − S, u = B + S).
‑/

namespace Comparability

variable {ι : Type _} [Fintype ι]

@[simp] def quadRe (G : ι → ι → Complex) (v : ι → Complex) : ℝ :=
  (∑ i, ∑ j, Complex.conj (v i) * G i j * (v j)).re

@[simp] def l2sq (v : ι → Complex) : ℝ := ∑ i, ‖v i‖^2

lemma l2sq_nonneg (v : ι → Complex) : 0 ≤ l2sq v := by
  classical
  have : ∀ i, 0 ≤ ‖v i‖^2 := by intro i; have := norm_nonneg (v i); nlinarith
  exact Finset.sum_nonneg (by intro i _; simpa using this i)

lemma comparable_lower {G_RS G_W : ι → ι → Complex}
  {lRS uW : ℝ}
  (hRSlo : ∀ v, lRS * l2sq v ≤ quadRe G_RS v)
  (hWup  : ∀ v, quadRe G_W  v ≤ uW  * l2sq v)
  (hlRS  : 0 ≤ lRS) (huW  : 0 < uW)
  : ∀ v, (lRS / uW) * quadRe G_W v ≤ quadRe G_RS v := by
  intro v
  have hub_W  : quadRe G_W  v ≤ uW  * l2sq v := hWup v
  -- (1/uW) * Q_W ≤ ‖v‖²
  have h1 : (1 / uW) * quadRe G_W v ≤ l2sq v := by
    have hpos : 0 ≤ 1 / uW := one_div_nonneg.mpr (le_of_lt huW)
    simpa [one_div, inv_mul_cancel_left₀ (ne_of_gt huW), mul_comm, mul_left_comm, mul_assoc]
      using (mul_le_mul_of_nonneg_left hub_W hpos)
  -- (lRS/uW) * Q_W ≤ lRS * ‖v‖² ≤ Q_RS
  have h2 : (lRS / uW) * quadRe G_W v ≤ lRS * l2sq v := by
    have hpos' : 0 ≤ lRS := hlRS
    have : (lRS / uW) * quadRe G_W v = lRS * ((1 / uW) * quadRe G_W v) := by
      field_simp [one_div, mul_comm, mul_left_comm, mul_assoc]
    have := mul_le_mul_of_nonneg_left h1 hpos'
    simpa [this] using this
  have h3 : lRS * l2sq v ≤ quadRe G_RS v := hRSlo v
  exact le_trans h2 h3

lemma comparable_upper {G_RS G_W : ι → ι → Complex}
  {uRS lW : ℝ}
  (hRSup : ∀ v, quadRe G_RS v ≤ uRS * l2sq v)
  (hWlo : ∀ v, lW  * l2sq v ≤ quadRe G_W  v)
  (huRS : 0 ≤ uRS) (hlW  : 0 < lW)
  : ∀ v, quadRe G_RS v ≤ (uRS / lW) * quadRe G_W v := by
  intro v
  have hlb_W  : lW  * l2sq v ≤ quadRe G_W  v := hWlo v
  -- uRS * ‖v‖² ≤ (uRS/lW) * Q_W
  have h1 : uRS * l2sq v ≤ (uRS / lW) * quadRe G_W v := by
    have hpos : 0 ≤ uRS := huRS
    have hscale : (uRS / lW) * (lW * l2sq v) ≤ (uRS / lW) * quadRe G_W v := by
      have hnonneg : 0 ≤ (uRS / lW) := by
        have : 0 ≤ uRS := huRS
        have : 0 ≤ 1 / lW := one_div_nonneg.mpr (le_of_lt hlW)
        have := mul_nonneg this_1 this; exact this
      exact mul_le_mul_of_nonneg_left hlb_W hnonneg
    -- simplify (uRS/lW) * (lW * ‖v‖²) = uRS * ‖v‖²
    have : (uRS / lW) * (lW * l2sq v) = uRS * l2sq v := by
      field_simp [one_div, mul_comm, mul_left_comm, mul_assoc]
    simpa [this] using hscale
  have hub_RS : quadRe G_RS v ≤ uRS * l2sq v := hRSup v
  exact le_trans hub_RS h1

lemma comparable_of_scalar_bounds {G_RS G_W : ι → ι → Complex}
  {lRS uRS lW uW : ℝ}
  (hRSlo : ∀ v, lRS * l2sq v ≤ quadRe G_RS v)
  (hRShi : ∀ v, quadRe G_RS v ≤ uRS * l2sq v)
  (hWlo  : ∀ v, lW  * l2sq v ≤ quadRe G_W  v)
  (hWhi  : ∀ v, quadRe G_W  v ≤ uW  * l2sq v)
  (hlRS  : 0 ≤ lRS) (huRS : 0 ≤ uRS) (hlW   : 0 < lW) (huW : 0 < uW)
  : ∀ v, (lRS / uW) * quadRe G_W v ≤ quadRe G_RS v
        ∧ quadRe G_RS v ≤ (uRS / lW) * quadRe G_W v := by
  intro v
  refine ⟨?lower, ?upper⟩
  · exact comparable_lower (ι:=ι) (G_RS:=G_RS) (G_W:=G_W) hRSlo hWhi hlRS huW v
  · exact comparable_upper (ι:=ι) (G_RS:=G_RS) (G_W:=G_W) hRShi hWlo huRS hlW v

end Comparability

end YM
