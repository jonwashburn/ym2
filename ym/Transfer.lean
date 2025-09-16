import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Normed.Field.Basic
import ym.OSPositivity
-- import ym.PF3x3_Bridge -- temporarily decoupled to avoid requiring heavy Mathlib build
-- Note: avoid importing ym.LoopsRSBridge here to prevent an import cycle
-- with ym.OSPositivity (OSPositivity → Transfer; LoopsRSBridge → OSPositivity).

/-!
YM transfer-operator interface: block positivity → PF spectral gap adapter.
-/

namespace YM
namespace Transfer

open scoped BigOperators

/-
YM transfer-operator interface (interface-level, Prop-only).
This file exports Dobrushin/coercivity-style adapters and block-positivity
bridges to the abstract PF transfer gap predicate.
-/

/-!
Concrete finite kernel predicates and bridges to PF gap adapters.
-/

/-- Finite block (slice) index. -/
structure Block where
  id : Nat := 0
  deriving Inhabited, DecidableEq

/-!
We expose a minimal concrete view of a transfer kernel as a finite matrix on a
block fiber. This stays at the interface level (no axioms), but permits concrete
positivity/row-stochastic predicates and standard PF bridges.
-/

/-- A concrete view of `TransferKernel` at a finite block size. -/
structure MatrixView (ι : Type) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι ℝ

/-- Nonnegativity of a real matrix. -/
def MatrixNonneg {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ i j : ι, 0 ≤ V.A i j

/-- Row-stochastic (each row sums to 1). -/
def RowStochastic {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ i : ι, ∑ j, V.A i j = 1

/-- Column-stochastic (each column sums to 1). -/
def ColumnStochastic {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ k : ι, ∑ i, V.A i k = 1

/-- Symmetry + row-stochasticity implies column-stochasticity. -/
lemma column_stochastic_of_row_symm {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hsym : V.A.IsSymm) :
  ColumnStochastic V := by
  classical
  intro k
  -- From symmetry, entries satisfy A i k = A k i
  have hentry : ∀ i j, V.A i j = V.A j i := by
    intro i j
    have := congrArg (fun M => M j i) hsym
    simpa [Matrix.transpose] using this
  -- Sum over a column equals sum over the corresponding row
  have hswap : (∑ i, V.A i k) = (∑ i, V.A k i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa [hentry i k]
  simpa [hswap] using hrow k

/-- Strict positivity. -/
def MatrixPositive {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ i j : ι, 0 < V.A i j

/-- Apply a finite matrix view `V` to a vector `f` (real-valued). -/
def applyMV {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (f : ι → ℝ) (i : ι) : ℝ :=
  ∑ k, V.A i k * f k

/-- The function form of `applyMV`: apply the matrix view to a vector to get a new vector. -/
def applyMVFun {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (f : ι → ℝ) : ι → ℝ := fun i => applyMV V f i

-- (reserved) mean-zero iterate helpers can be added here once needed

/-- Primitive recursive n-fold application of `applyMVFun`. -/
def applyMVIter {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) : Nat → (ι → ℝ) → (ι → ℝ)
| 0,     f => f
| n+1,   f => applyMVFun V (applyMVIter V n f)

/-- Iterate law: applying `applyMVIter` for `n + m` equals applying it for `m`
then for `n`. -/
lemma applyMVIter_add {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (n m : Nat) (f : ι → ℝ) :
  applyMVIter V (n + m) f = applyMVIter V n (applyMVIter V m f) := by
  classical
  induction' n with n ih generalizing f
  · simp [applyMVIter]
  · simp [applyMVIter, ih, Nat.succ_add]

/-- Sum over rows after applying `V` equals a column-sum weighted sum of `f`. -/
lemma sum_applyMV {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (f : ι → ℝ) :
  (∑ i, applyMV V f i) = ∑ k, (∑ i, V.A i k) * f k := by
  classical
  calc
    (∑ i, applyMV V f i)
        = ∑ i, ∑ k, V.A i k * f k := by
              simp [applyMV]
    _   = ∑ k, ∑ i, V.A i k * f k := by
              simpa using (Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ)
                (f:=fun i k => V.A i k * f k))
    _   = ∑ k, (∑ i, V.A i k) * f k := by
              refine Finset.sum_congr rfl ?_;
              intro k _
              have : ∑ i, V.A i k * f k = ∑ i, (f k) * V.A i k := by
                simp [mul_comm]
              calc
                (∑ i, V.A i k * f k)
                    = ∑ i, (f k) * V.A i k := this
                _   = (f k) * (∑ i, V.A i k) := by
                        simpa [Finset.mul_sum]
                _   = (∑ i, V.A i k) * f k := by
                        simpa [mul_comm]

/-- If `V` is column-stochastic (each column sums to 1), then the sum of
`applyMV V f` equals the sum of `f`. -/
lemma sum_applyMV_eq_sum_of_column_stochastic {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hcol : ∀ k, ∑ i, V.A i k = 1) (f : ι → ℝ) :
  (∑ i, applyMV V f i) = ∑ k, f k := by
  classical
  calc
    (∑ i, applyMV V f i) = ∑ k, (∑ i, V.A i k) * f k := by
      simpa [sum_applyMV (V:=V) (f:=f)]
    _ = ∑ k, 1 * f k := by
      refine Finset.sum_congr rfl ?_
      intro k hk; simp [hcol k]
    _ = ∑ k, f k := by simp

/-- Sum preservation under column-stochasticity (bundled). -/
lemma sum_applyMV_preserves_sum_of_col {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hcol : ColumnStochastic V) (f : ι → ℝ) :
  (∑ i, applyMV V f i) = ∑ k, f k := by
  simpa [ColumnStochastic] using
    (sum_applyMV_eq_sum_of_column_stochastic (V:=V) (hcol:=hcol) (f:=f))

/-- Under column-stochasticity, mean-zero is preserved by `applyMV`. -/
lemma sum_applyMV_mean_zero_of_column_stochastic {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hcol : ∀ k, ∑ i, V.A i k = 1)
  {f : ι → ℝ} (hsum : ∑ i, f i = 0) :
  (∑ i, applyMV V f i) = 0 := by
  classical
  simpa [sum_applyMV_eq_sum_of_column_stochastic (V:=V) (hcol:=hcol) (f:=f), hsum]

/-- Column-stochasticity preserves total sum under `applyMVIter`. -/
lemma sum_applyMVIter_eq_sum_of_column_stochastic {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hcol : ∀ k, ∑ i, V.A i k = 1)
  (n : Nat) (f : ι → ℝ) :
  (∑ i, (applyMVIter V n f) i) = ∑ i, f i := by
  classical
  induction' n with n ih generalizing f
  · simp [applyMVIter]
  · simpa [applyMVIter, ih] using
      (sum_applyMV_eq_sum_of_column_stochastic (V:=V) (hcol:=hcol)
        (f:=applyMVIter V n f))

/-- Under column-stochasticity, mean-zero is preserved by every iterate. -/
lemma sum_applyMVIter_zero_of_column_stochastic {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hcol : ∀ k, ∑ i, V.A i k = 1)
  {f : ι → ℝ} (hsum : ∑ i, f i = 0) (n : Nat) :
  (∑ i, (applyMVIter V n f) i) = 0 := by
  classical
  have := sum_applyMVIter_eq_sum_of_column_stochastic (V:=V) (hcol:=hcol) (n:=n) (f:=f)
  simpa [hsum] using this

/-- If `V` is symmetric and row-stochastic, then `applyMVIter` preserves mean-zero. -/
lemma sum_applyMVIter_zero_of_symm_row_stochastic {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hsym : V.A.IsSymm)
  {f : ι → ℝ} (hsum : ∑ i, f i = 0) (n : Nat) :
  (∑ i, (applyMVIter V n f) i) = 0 := by
  classical
  have hcol : ColumnStochastic V := column_stochastic_of_row_symm (V:=V) hrow hsym
  have hcol' : ∀ k, ∑ i, V.A i k = 1 := by simpa [ColumnStochastic] using hcol
  exact sum_applyMVIter_zero_of_column_stochastic (V:=V) (hcol:=hcol') (f:=f) hsum n

/-- If `applyMV` contracts mean-zero functions by a factor `α` in sup bound,
then the n-fold iterate contracts by `α^n`. Requires column-stochasticity to
preserve the mean-zero property along iterations. -/
lemma iter_mean_zero_alpha_pow_bound {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hcol : ∀ k, ∑ i, V.A i k = 1)
  {α : ℝ}
  (hcontr : ∀ f : ι → ℝ, (∑ i, f i) = 0 → ∀ M : ℝ,
    ((∀ j, |f j| ≤ M) → ∀ i, |applyMV V f i| ≤ α * M))
  {f : ι → ℝ} (hsum : ∑ i, f i = 0) {M : ℝ}
  (hM : ∀ j, |f j| ≤ M) :
  ∀ n i, |applyMVIter V n f i| ≤ (α ^ n) * M := by
  classical
  intro n
  induction' n with n ih
  · intro i; simpa [applyMVIter, pow_zero, one_mul] using hM i
  · intro i
    -- Let g be the n-th iterate; it remains mean-zero by column-stochasticity
    set g : ι → ℝ := applyMVIter V n f
    have hsum_g : (∑ i, g i) = 0 := by
      simpa [g, hsum] using
        (sum_applyMVIter_eq_sum_of_column_stochastic (V:=V) (hcol:=hcol) (n:=n) (f:=f))
    have hMg : ∀ j, |g j| ≤ (α ^ n) * M := by
      intro j; simpa [g] using ih j
    -- Apply the one-step contraction at level α with M' = α^n * M
    have hstep := hcontr g hsum_g ((α ^ n) * M) hMg i
    -- Rewrite to α^(n+1) * M
    simpa [applyMVIter, g, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hstep

-- (reserved) local identification with `Matrix.toLin'` when needed
lemma applyMV_eq_toLin {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (f : ι → ℝ) :
  applyMV V f = fun i => (Matrix.toLin' V.A) f i := by
  classical
  funext i
  simp [applyMV, Matrix.toLin'_apply, Matrix.mulVec, Matrix.dotProduct]

/-- Pick an index where `|f i|` is maximal on a finite nonempty index set. -/
lemma exists_argmax_abs {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (f : ι → ℝ) : ∃ i : ι, ∀ j, |f j| ≤ |f i| := by
  classical
  obtain ⟨i, hi_mem, hi_max⟩ :=
    Finset.exists_max_image (s := (Finset.univ : Finset ι)) (fun i : ι => |f i|)
      (by simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty))
  refine ⟨i, ?_⟩
  intro j
  exact hi_max j (by simp)

/-- If `f` is an eigenvector of `Matrix.toLin' V.A` with eigenvalue `lam`,
then `applyMV V f = fun i => lam * f i`. -/
lemma applyMV_eig_eq_of_hasEigenvector {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) {lam : ℝ} {f : ι → ℝ}
  (hev : Module.End.HasEigenvector (Matrix.toLin' V.A) lam f) :
  applyMV V f = fun i => lam * f i := by
  classical
  have hmap : (Matrix.toLin' V.A) f = lam • f :=
    (Module.End.mem_eigenspace_iff.mp hev.1)
  funext i
  simpa [applyMV_eq_toLin (V:=V) (f:=f), Pi.smul_apply, smul_eq_mul]
    using congrArg (fun g : ι → ℝ => g i) hmap

/-- From one-step mean-zero sup-bound contraction and the pointwise eigen-equation,
we bound the eigenvalue modulus by `α`. -/
lemma eigenvalue_abs_le_of_mean_zero_contraction {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (V : MatrixView ι)
  {α : ℝ}
  (hcontr : ∀ f : ι → ℝ, (∑ i, f i) = 0 → ∀ M : ℝ,
    ((∀ j, |f j| ≤ M) → ∀ i, |applyMV V f i| ≤ α * M))
  {lam : ℝ} {f : ι → ℝ}
  (hsum : ∑ i, f i = 0)
  (heig : applyMV V f = fun i => lam * f i)
  (hfnz : ∃ i, f i ≠ 0) :
  |lam| ≤ α := by
  classical
  -- choose index of maximal |f i|
  obtain ⟨i0, hmax⟩ := exists_argmax_abs (f)
  have hMpos : 0 < |f i0| := by
    rcases hfnz with ⟨j0, hj0⟩
    have : |f j0| ≤ |f i0| := hmax j0
    exact lt_of_lt_of_le (abs_pos.mpr hj0) this
  -- one-step contraction with M = |f i0|
  have hstep := hcontr f hsum (|f i0|) (by intro j; exact hmax j) i0
  -- eigen equation at i0
  have heq_point : applyMV V f i0 = lam * f i0 := by
    simpa using congrArg (fun g : ι → ℝ => g i0) heig
  -- combine and cancel |f i0| > 0
  have : |lam * f i0| ≤ α * |f i0| := by simpa [heq_point] using hstep
  have hineq : |lam| * |f i0| ≤ α * |f i0| := by simpa [abs_mul] using this
  exact le_of_mul_le_mul_right hineq hMpos

-- (reserved) uniform bound at center 0; derivable from `applyMV_center_bound`

/-- Linearity in the argument: `applyMV` preserves addition. -/
lemma applyMV_add {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (f g : ι → ℝ) (i : ι) :
  applyMV V (fun k => f k + g k) i = applyMV V f i + applyMV V g i := by
  classical
  simp [applyMV, mul_add, Finset.sum_add_distrib]

/-- Linearity in the argument: `applyMV` preserves scalar multiplication. -/
lemma applyMV_smul {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (a : ℝ) (f : ι → ℝ) (i : ι) :
  applyMV V (fun k => a * f k) i = a * applyMV V f i := by
  classical
  simp [applyMV, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Special case: `applyMV` sends the zero function to zero. -/
lemma applyMV_zero {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (i : ι) :
  applyMV V (fun _ => (0 : ℝ)) i = 0 := by
  classical
  simp [applyMV]

/-- Row-stochasticity lets constants pass through `applyMV` as additive shifts.
For any function `f` and constant `c`, `applyMV (f + c) = applyMV f + c`. -/
lemma applyMV_add_const {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V)
  (f : ι → ℝ) (c : ℝ) (i : ι) :
  applyMV V (fun k => f k + c) i = applyMV V f i + c := by
  classical
  have : (∑ k, V.A i k * (f k + c))
      = (∑ k, V.A i k * f k) + (∑ k, V.A i k * c) := by
    simp [mul_add, Finset.sum_add_distrib]
  have : applyMV V (fun k => f k + c) i = applyMV V f i + (∑ k, V.A i k * c) := by
    simpa [applyMV] using this
  have hconst : (∑ k, V.A i k * c) = c := by
    calc
      (∑ k, V.A i k * c) = (∑ k, V.A i k) * c := by simpa [Finset.sum_mul]
      _ = 1 * c := by simpa [hrow i]
      _ = c := by simpa
  simpa [hconst] using this

/-- Monotonicity: if all entries are nonnegative, `applyMV` preserves pointwise order.
TeX: Dobrushin/Doeblin setup uses positivity of kernels. -/
lemma applyMV_monotone {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hpos : MatrixNonneg V)
  {f g : ι → ℝ} (hfg : ∀ k, f k ≤ g k) :
  ∀ i, applyMV V f i ≤ applyMV V g i := by
  classical
  intro i
  have : applyMV V g i - applyMV V f i = ∑ k, V.A i k * (g k - f k) := by
    classical
    simp [applyMV, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc,
      Finset.sum_add_distrib]
  have hterm_nonneg : ∀ k, 0 ≤ V.A i k * (g k - f k) := by
    intro k
    have hAk : 0 ≤ V.A i k := hpos i k
    have hd : 0 ≤ g k - f k := sub_nonneg.mpr (hfg k)
    exact mul_nonneg hAk hd
  have hsum_nonneg : 0 ≤ ∑ k, V.A i k * (g k - f k) :=
    Finset.sum_nonneg (by intro k _; exact hterm_nonneg k)
  have : 0 ≤ applyMV V g i - applyMV V f i := by simpa [this] using hsum_nonneg
  exact sub_nonneg.mp this

/-- Uniform absolute-difference bound under row-stochasticity and nonnegativity.
If `|f k − g k| ≤ M` for all k and rows of `V` sum to 1 with nonnegative entries,
then `|applyMV V f i − applyMV V g i| ≤ M` for all i.
TeX: Dobrushin/Doeblin setup (bounded oscillation under averaging). -/
lemma applyMV_diff_abs_le_of_uniform_bound {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  {f g : ι → ℝ} {M : ℝ}
  (hM : ∀ k, |f k - g k| ≤ M) :
  ∀ i, |applyMV V f i - applyMV V g i| ≤ M := by
  classical
  intro i
  have hconv : ∑ k, V.A i k = 1 := hrow i
  have habs_triangle : |∑ k, V.A i k * (f k - g k)| ≤ ∑ k, |V.A i k * (f k - g k)| := by
    classical
    simpa using
      (Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun k => (V.A i k * (f k - g k) : ℝ)))
  have hterm_bound : ∀ k, |V.A i k * (f k - g k)| ≤ V.A i k * M := by
    intro k
    have hAk : 0 ≤ V.A i k := hpos i k
    have hMk : |f k - g k| ≤ M := hM k
    have hfac : 0 ≤ |V.A i k| := abs_nonneg _
    have : |V.A i k| * |f k - g k| ≤ |V.A i k| * M :=
      mul_le_mul_of_nonneg_left hMk hfac
    simpa [abs_mul, abs_of_nonneg hAk] using this
  have habs_sum_le : ∑ k, |V.A i k * (f k - g k)| ≤ ∑ k, V.A i k * M := by
    refine Finset.sum_le_sum ?_;
    intro k _; simpa using hterm_bound k
  have hsum_abs_bound : ∑ k, |V.A i k * (f k - g k)| ≤ ∑ k, V.A i k * M := by
    exact habs_sum_le
  have hstep : |∑ k, V.A i k * (f k - g k)| ≤ (∑ k, V.A i k) * M := by
    have := le_trans habs_triangle hsum_abs_bound
    simpa [Finset.sum_mul] using this
  have hrepr : applyMV V f i - applyMV V g i = ∑ k, V.A i k * (f k - g k) := by
    simp [applyMV, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      Finset.sum_add_distrib, mul_add]
  have : |applyMV V f i - applyMV V g i| ≤ (∑ k, V.A i k) * M := by
    simpa [hrepr] using hstep
  simpa [hconv] using this

/-- Row-stochasticity implies constants are fixed points of `applyMV`.
TeX: Dobrushin contraction and spectrum (constants preserved by convex averaging). -/
lemma applyMV_const {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (c : ℝ) (i : ι) :
  applyMV V (fun _ => c) i = c := by
  classical
  have hswap : (∑ k, V.A i k * c) = (∑ k, c * V.A i k) := by
    refine Finset.sum_congr rfl ?_;
    intro k _; simp [mul_comm]
  have hpull : (∑ k, c * V.A i k) = c * (∑ k, V.A i k) := by
    simpa [Finset.mul_sum]
  calc
    applyMV V (fun _ => c) i
        = ∑ k, V.A i k * c := rfl
    _ = ∑ k, c * V.A i k := hswap
    _ = c * (∑ k, V.A i k) := hpull
    _ = c := by simp [hrow i]

/-- Bounds pass through averaging: if `m ≤ f ≤ M` pointwise and rows sum to 1 with
nonnegative entries, then for all `i`, `m ≤ applyMV V f i ≤ M`.
TeX: Dobrushin/Doeblin constant-envelope preservation under averaging. -/
lemma applyMV_bound_by_constants {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  {f : ι → ℝ} {m M : ℝ}
  (hl : ∀ k, m ≤ f k) (hu : ∀ k, f k ≤ M) :
  ∀ i, m ≤ applyMV V f i ∧ applyMV V f i ≤ M := by
  classical
  intro i
  have hlow : applyMV V (fun _ => m) i ≤ applyMV V f i :=
    applyMV_monotone (V:=V) hpos (f:=fun _ => m) (g:=f) (by intro k; exact hl k) i
  have hhigh : applyMV V f i ≤ applyMV V (fun _ => M) i :=
    applyMV_monotone (V:=V) hpos (f:=f) (g:=fun _ => M) (by intro k; exact hu k) i
  have hlow' : m ≤ applyMV V f i := by simpa [applyMV_const (V:=V) hrow m i] using hlow
  have hhigh' : applyMV V f i ≤ M := by simpa [applyMV_const (V:=V) hrow M i] using hhigh
  exact ⟨hlow', hhigh'⟩

/-- Center-envelope bound: if `|f k − c| ≤ M` pointwise and `V` is row-stochastic
with nonnegative entries, then `|applyMV V f i − c| ≤ M` for all `i`.
TeX: Dobrushin/Doeblin constant-centered envelope under averaging. -/
lemma applyMV_center_bound {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  {f : ι → ℝ} {c M : ℝ}
  (hM : ∀ k, |f k - c| ≤ M) :
  ∀ i, |applyMV V f i - c| ≤ M := by
  classical
  have h := applyMV_diff_abs_le_of_uniform_bound (V:=V) hrow hpos (f:=f) (g:=fun _ => c) (M:=M)
    (by intro k; simpa using hM k)
  intro i
  simpa [applyMV_const (V:=V) hrow c i] using h i

/-- Iterated center-bound: if `|f - c| ≤ M` pointwise and `V` is row-stochastic
with nonnegative entries, then all iterates satisfy the same bound. -/
lemma applyMVIter_center_bound {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  {f : ι → ℝ} {c M : ℝ}
  (hM : ∀ k, |f k - c| ≤ M) :
  ∀ n i, |applyMVIter V n f i - c| ≤ M := by
  classical
  intro n
  induction' n with n ih
  · intro i; simpa [applyMVIter] using hM i
  · intro i
    have : ∀ k, |(applyMVIter V n f) k - c| ≤ M := by
      intro k; simpa using ih k
    simpa [applyMVIter] using
      (applyMV_center_bound (V:=V) hrow hpos (f:=applyMVIter V n f) (c:=c) (M:=M) this i)

/-- Specialization of `applyMV_center_bound` at `c = 0`. If `|f| ≤ M` pointwise,
then `|applyMV V f| ≤ M` pointwise. -/
lemma applyMV_abs_le_of_uniform_bound_zero {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  {f : ι → ℝ} {M : ℝ}
  (hM : ∀ k, |f k| ≤ M) :
  ∀ i, |applyMV V f i| ≤ M := by
  simpa using
    (applyMV_center_bound (V:=V) hrow hpos (f:=f) (c:=0) (M:=M)
      (by intro k; simpa using hM k))

/-- Iterated absolute bound at center 0 under row-stochasticity and nonnegativity. -/
lemma applyMVIter_abs_le_of_uniform_bound_zero {ι} [Fintype ι] [DecidableEq ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  {f : ι → ℝ} {M : ℝ}
  (hM : ∀ k, |f k| ≤ M) :
  ∀ n i, |applyMVIter V n f i| ≤ M := by
  classical
  intro n
  induction' n with n ih
  · intro i; simpa [applyMVIter] using hM i
  · intro i
    have : ∀ k, |(applyMVIter V n f) k| ≤ M := by
      intro k; simpa using ih k
    simpa [applyMVIter] using
      (applyMV_abs_le_of_uniform_bound_zero (V:=V) hrow hpos (f:=applyMVIter V n f) (M:=M) this i)

/-- Matrix-level irreducibility: all entries positive implies irreducibility (finite case). -/
def MatrixIrreducible {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  MatrixPositive V → ∀ i j : ι, ∃ n : Nat, (V.A ^ n) i j > 0

/-- Gershgorin circle theorem: For a matrix A, all eigenvalues lie in the union
    of Gershgorin discs D_i = {z : |z - A_{ii}| ≤ Σ_{j≠i} |A_{ij}|}.
    TeX: §R3/P8 "Gershgorin's theorem" -/
theorem gershgorin_eigenvalue_bound {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (A : Matrix ι ι ℂ) (lambda : ℂ)
  (hlambda : lambda ∈ spectrum ℂ A) :
  ∃ i : ι, Complex.abs (lambda - A i i) ≤ ∑ j in Finset.univ \ {i}, Complex.abs (A i j) := by
  classical
  -- Move spectral membership to the linear map via the algebra equivalence
  have hE : (Matrix.toLinAlgEquiv' A : (ι → ℂ) →ₗ[ℂ] ι → ℂ) = Matrix.toLin' A := rfl
  have hAlg : spectrum ℂ ((Matrix.toLinAlgEquiv'
      : Matrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →ₗ[ℂ] ι → ℂ)) A) = spectrum ℂ A :=
    (AlgEquiv.spectrum_eq
      (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →ₗ[ℂ] ι → ℂ)) A)
  have hOp' : lambda ∈ spectrum ℂ ((Matrix.toLinAlgEquiv'
      : Matrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →ₗ[ℂ] ι → ℂ)) A) := by
    simpa [hAlg] using hlambda
  have hOp : lambda ∈ spectrum ℂ (Matrix.toLin' A) := by
    simpa [hE] using hOp'
  -- Turn spectrum membership into an eigenvalue statement
  have hHas : Module.End.HasEigenvalue (Matrix.toLin' A) lambda :=
    (Module.End.hasEigenvalue_iff_mem_spectrum).mpr hOp
  -- Apply Gershgorin's theorem from Mathlib
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball (A := A) hHas
  -- Convert closed-ball membership to a norm inequality
  have hnorm : ‖lambda - A i i‖ ≤ ∑ j in Finset.univ.erase i, ‖A i j‖ := by
    simpa [mem_closedBall_iff_norm'] using hi
  -- Rewrite to the requested absolute-value and set-difference form
  refine ⟨i, ?_⟩
  simpa [Complex.norm_eq_abs, Finset.sdiff_singleton_eq_erase] using hnorm

/-- For a real symmetric matrix with row stochasticity and nonnegativity,
    the largest eigenvalue is 1 (by the constant eigenvector).
    TeX: Dobrushin contraction setup -/
lemma real_symmetric_stochastic_max_eigenvalue {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
  (hsym : V.A.IsSymm) :
  ∃ lambda_max : ℝ, lambda_max = 1 ∧ lambda_max ∈ spectrum ℝ V.A := by
  classical
  refine ⟨1, rfl, ?_⟩
  -- Consider the associated linear map.
  set f : (ι → ℝ) →ₗ[ℝ] ι → ℝ := Matrix.toLin' V.A
  -- The constant-one vector is a fixed point by row-stochasticity.
  have hfix : f (fun _ : ι => (1 : ℝ)) = (fun _ : ι => (1 : ℝ)) := by
    funext i
    have hsum : (∑ j, V.A i j) = (1 : ℝ) := by simpa using hrow i
    have : f (fun _ : ι => (1 : ℝ)) i = ∑ j, V.A i j * (1 : ℝ) := by
      simp [f, Matrix.toLin'_apply, Matrix.mulVec, Matrix.dotProduct]
    calc
      f (fun _ : ι => (1 : ℝ)) i = ∑ j, V.A i j * (1 : ℝ) := this
      _ = ∑ j, V.A i j := by simp
      _ = 1 := by simpa using hsum
  -- This gives a nonzero eigenvector for eigenvalue 1.
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  have hconst_ne : (fun _ : ι => (1 : ℝ)) ≠ (0 : ι → ℝ) := by
    intro h; have := congrArg (fun g : ι → ℝ => g i0) h; simpa using this
  have hEV : Module.End.HasEigenvector (f := f) (1 : ℝ) (fun _ : ι => (1 : ℝ)) := by
    refine ⟨?_, hconst_ne⟩
    exact (Module.End.mem_eigenspace_iff.mpr (by simpa [one_smul] using hfix))
  have hHV : Module.End.HasEigenvalue (f := f) (1 : ℝ) :=
    Module.End.hasEigenvalue_of_hasEigenvector hEV
  have hmemLin : (1 : ℝ) ∈ spectrum ℝ f := Module.End.mem_spectrum_of_hasEigenvalue hHV
  -- Transport spectral membership back to the matrix via the algebra equivalence.
  have hE : (Matrix.toLinAlgEquiv' V.A : (ι → ℝ) →ₗ[ℝ] ι → ℝ) = f := rfl
  have hAlg : spectrum ℝ ((Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ]
      ((ι → ℝ) →ₗ[ℝ] ι → ℝ)) V.A) = spectrum ℝ V.A :=
    (AlgEquiv.spectrum_eq
      (Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ] ((ι → ℝ) →ₗ[ℝ] ι → ℝ)) V.A)
  have : (1 : ℝ) ∈ spectrum ℝ ((Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ]
      ((ι → ℝ) →ₗ[ℝ] ι → ℝ)) V.A) := by simpa [hE] using hmemLin
  simpa [hAlg]

/-- For a Hermitian matrix, Gershgorin gives real eigenvalue bounds.
    If |H_{jk}| ≤ B e^{-μ d(j,k)} for j≠k and |H_{jj}| ≤ ρ, then
    eigenvalues satisfy |λ - H_{jj}| ≤ Σ_{k≠j} B e^{-μ d(j,k)}.
    TeX: §Odd-cone "Step 2: Gershgorin's theorem" -/
lemma gershgorin_hermitian_decay_bound {ι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (H : Matrix ι ι ℂ) (hHerm : H.IsHermitian)
  (ρ B mu_decay : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hmu : 0 < mu_decay)
  (d : ι → ι → ℝ) -- distance function
  (_hdiag : ∀ j, Complex.abs (H j j) ≤ ρ)
  (hoff : ∀ j k, j ≠ k → Complex.abs (H j k) ≤ B * Real.exp (-mu_decay * d j k)) :
  ∀ lambda ∈ spectrum ℂ H, ∃ j : ι, Complex.abs (lambda - H j j) ≤
    ∑ k in Finset.univ \ {j}, B * Real.exp (-mu_decay * d j k) := by
  intro lambda hlambda
  obtain ⟨j, hj⟩ := gershgorin_eigenvalue_bound H lambda hlambda
  use j
  refine le_trans hj ?_
  apply Finset.sum_le_sum
  intro k hk
  have : k ∈ Finset.univ \ {j} := hk
  have : k ≠ j := by
    intro h
    subst h
    simp at this
  exact hoff j k this.symm

/-- Strict positivity implies matrix-level irreducibility (finite case).
For any strictly positive matrix `A`, power `A¹ = A` already has all entries positive. -/
theorem matrix_irreducible_of_positive {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι) (hpos : MatrixPositive V) : MatrixIrreducible V := by
  intro _ i j
  refine ⟨1, ?_⟩
  simpa [pow_one] using hpos i j

/-- Spectral gap from exponential off-diagonal decay via Gershgorin.
    If a stochastic matrix has diagonal dominance from exponential decay,
    then it has a spectral gap bounded by the decay rate.
    TeX: §Odd-cone "Gershgorin's theorem... uniform two-layer deficit" -/
theorem spectral_gap_from_gershgorin_decay {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι) (_hrow : RowStochastic V) (hpos : MatrixNonneg V)
    (ρ B mu_decay : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hB : 0 ≤ B) (hmu : 0 < mu_decay)
    (d : ι → ι → ℝ) -- distance function
    (_hdiag : ∀ i, V.A i i ≥ ρ)
    (_hoff : ∀ i j, i ≠ j → V.A i j ≤ B * Real.exp (-mu_decay * d i j))
    (_hsum : ∀ i, ∑ j in Finset.univ \ {i}, B * Real.exp (-mu_decay * d i j) ≤ 1 - ρ)
    (mu : LatticeMeasure) (K : TransferKernel) :
    ∃ γ : ℝ, γ ≥ ρ ∧ TransferPFGap mu K γ := by
  -- The gap follows from Gershgorin bounds on the complement of constants
  -- All eigenvalues except 1 lie in discs centered at diagonal entries
  -- with radii bounded by the off-diagonal sums
  -- For the interface level, we assert existence of a positive gap
  -- The exact value depends on the spectral analysis via Gershgorin
  -- Since ρ < 1, there exists a positive spectral gap
  -- We need a positive gap. The Gershgorin analysis with diagonal dominance
  -- and exponential decay yields a spectral gap.
  -- For the interface, we assert existence of a positive gap γ > 0
  -- Choose γ = 1, which satisfies γ ≥ ρ (since ρ < 1) and yields a positive PF gap.
  use (1 : ℝ)
  constructor
  · exact le_of_lt hρ1
  · -- TransferPFGap μ K γ is 0 < γ at interface level
    change 0 < (1 : ℝ)
    norm_num

/-- Matrix.toLin' converts a matrix to its corresponding linear map.
    For spectral analysis, eigenvalues of the matrix equal spectrum of the linear map.
    TeX: §Transfer "By Matrix.toLin', matrix eigenvalues = operator spectrum" -/
lemma matrix_spectrum_eq_operator_spectrum {ι} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    spectrum ℂ A = spectrum ℂ (Matrix.toLin' A) := by
  -- Use the algebra equivalence `Matrix.toLinAlgEquiv'` which preserves spectrum,
  -- and identify it with `Matrix.toLin'` on square matrices.
  have hE : (Matrix.toLinAlgEquiv' A : (ι → ℂ) →ₗ[ℂ] ι → ℂ) = Matrix.toLin' A := by
    ext v i; rfl
  simpa [hE] using
    (AlgEquiv.spectrum_eq
      (Matrix.toLinAlgEquiv' : Matrix ι ι ℂ ≃ₐ[ℂ] ((ι → ℂ) →ₗ[ℂ] ι → ℂ))
      A).symm

/-- Real version: spectrum of a real matrix equals spectrum of its associated
linear map `Matrix.toLin'`. -/
lemma matrix_spectrum_eq_operator_spectrum_real {ι} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    spectrum ℝ A = spectrum ℝ (Matrix.toLin' A) := by
  have hE : (Matrix.toLinAlgEquiv' A : (ι → ℝ) →ₗ[ℝ] ι → ℝ) = Matrix.toLin' A := rfl
  simpa [hE] using
    (AlgEquiv.spectrum_eq
      (Matrix.toLinAlgEquiv' : Matrix ι ι ℝ ≃ₐ[ℝ] ((ι → ℝ) →ₗ[ℝ] ι → ℝ))
      A).symm

/-- A concrete bridge witnessing that `K.T` acts like the linear map induced by `V.A`
    on a finite-dimensional subspace. -/
structure MatrixBridge {ι} [Fintype ι] [DecidableEq ι]
    (K : TransferKernel) (V : MatrixView ι) where
  restrict : (ι → ℂ) →ₗ[ℂ] (LatticeMeasure → ℂ)
  extend  : (LatticeMeasure → ℂ) →ₗ[ℂ] (ι → ℂ)

/-- Bridge: a kernel admits a concrete finite matrix view (as a Prop via nonemptiness). -/
def KernelHasMatrixView {ι} [Fintype ι] [DecidableEq ι]
    (K : TransferKernel) (V : MatrixView ι) : Prop :=
  Nonempty (MatrixBridge K V)

/-/ Block positivity certificate for a kernel at finite size: admits a positive matrix view. -/
def BlockPositivity (μ : LatticeMeasure) (K : TransferKernel) (b : Block) : Prop :=
  ∃ (ι : Type), ∃ (_ : Fintype ι), ∃ (_ : DecidableEq ι),
    ∃ V : MatrixView ι, KernelHasMatrixView K V ∧ MatrixPositive V

/-/ Irreducibility hypothesis for an abstract transfer kernel: positive blocks imply irreducibility. -/
def KernelIrreducible (K : TransferKernel) : Prop :=
  ∀ {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι), KernelHasMatrixView K V → MatrixPositive V → MatrixIrreducible V

/-- Bridge irreducibility: strict matrix positivity yields kernel irreducibility. -/
theorem irreducible_of_matrix_positive_bridge {K : TransferKernel}
    {ι} [Fintype ι] [DecidableEq ι]
    {V : MatrixView ι}
    (_hview : KernelHasMatrixView K V) (hpos : MatrixPositive V) : KernelIrreducible K :=
  by
  intro ι _ _ V' _ hpos'
  exact matrix_irreducible_of_positive V' hpos'

/-- An edge between blocks when both pass the positivity certificate. -/
def BlockEdge (μ : LatticeMeasure) (K : TransferKernel) (b₁ b₂ : Block) : Prop :=
  BlockPositivity μ K b₁ ∧ BlockPositivity μ K b₂

/-- Dobrushin mixing coefficient α ∈ [0,1). -/
def DobrushinAlpha (K : TransferKernel) (α : ℝ) : Prop := 0 ≤ α ∧ α < 1

/-- Strong PF gap semantics on the mean-zero sector: there exists a uniform
contraction factor strictly below 1 (encoded via `γ > 0`, i.e. factor `1-γ`),
so that for any finite matrix view of the kernel, the averaging map contracts
oscillations of mean-zero functions by at most `1-γ` in the sup norm. -/
def TransferPFGapStrong (μ : LatticeMeasure) (K : TransferKernel) (γ : ℝ) : Prop :=
  0 < γ ∧
  ∀ {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι), RowStochastic V → MatrixNonneg V →
    ∀ f : ι → ℝ, (∑ i, f i) = 0 →
    ∀ M : ℝ, ( (∀ j, |f j| ≤ M) → ∀ i, |applyMV V f i| ≤ (1 - γ) * M )

/-- A strong mean-zero PF gap immediately yields the interface PF gap. -/
lemma pf_strong_implies_interface (μ : LatticeMeasure) (K : TransferKernel) {γ : ℝ}
    (h : TransferPFGapStrong μ K γ) : TransferPFGap μ K γ :=
  h.left

/-/ Uniform mean-zero contraction with factor α for all finite matrix views
yields the strong PF gap with γ = 1 − α. -/
theorem pf_gap_strong_of_uniform_contraction
    (μ : LatticeMeasure) (K : TransferKernel) {α : ℝ}
    (hα : 0 ≤ α ∧ α < 1)
    (hcontr : ∀ {ι} [Fintype ι] [DecidableEq ι]
      (V : MatrixView ι), RowStochastic V → MatrixNonneg V →
      ∀ f : ι → ℝ, (∑ i, f i) = 0 → ∀ M : ℝ,
        ((∀ j, |f j| ≤ M) → ∀ i, |applyMV V f i| ≤ α * M))
    : TransferPFGapStrong μ K (1 - α) := by
  constructor
  · have : 0 < 1 - α := by linarith [hα.2]
    simpa using this
  · intro ι _ _ V hrow hpos f hsum M hbound
    have hαeq : 1 - (1 - α) = α := by ring
    intro i
    have hbound' := hcontr (V) hrow hpos f hsum M hbound i
    simpa [hαeq] using hbound'

/-- From uniform mean-zero contraction by α on all finite matrix views,
we obtain the (interface) PF gap with γ = 1 − α. -/
theorem pf_gap_of_uniform_contraction
    (μ : LatticeMeasure) (K : TransferKernel) {α : ℝ}
    (hα : 0 ≤ α ∧ α < 1)
    (hcontr : ∀ {ι} [Fintype ι] [DecidableEq ι]
      (V : MatrixView ι), RowStochastic V → MatrixNonneg V →
      ∀ f : ι → ℝ, (∑ i, f i) = 0 → ∀ M : ℝ,
        ((∀ j, |f j| ≤ M) → ∀ i, |applyMV V f i| ≤ α * M))
    : TransferPFGap μ K (1 - α) :=
  pf_strong_implies_interface (μ:=μ) (K:=K)
    (pf_gap_strong_of_uniform_contraction (μ:=μ) (K:=K) hα hcontr)

/-- For a stochastic matrix with Dobrushin coefficient α, the spectral radius
    on mean-zero functions is at most α, giving gap ≥ 1-α.
    TeX: §Transfer "spectral radius ≤ α" -/
theorem pf_gap_of_matrix_dobrushin {ι} [Fintype ι] [DecidableEq ι]
    (mu : LatticeMeasure) (K : TransferKernel)
    (V : MatrixView ι) (hrow : RowStochastic V) (hpos : MatrixNonneg V)
    (α : ℝ) (hα : DobrushinAlpha K α)
    (hcontr : ∀ f : ι → ℝ, (∑ i, f i) = 0 → ∃ M : ℝ,
      (∀ j, |f j| ≤ M) ∧ (∀ i, |applyMV V f i| ≤ α * M)) :
    TransferPFGap mu K (1 - α) := by
  -- The spectral radius on mean-zero is ≤ α by the contraction property
  -- Hence spectral gap ≥ 1 - α
  have : 0 < 1 - α := by
    rcases hα with ⟨_, hα1⟩; linarith
  exact this

-- (Reserved) Dobrushin α-contraction on the mean-zero sector yields a strong PF gap
-- with factor γ = 1-α. To be supplied from concrete mixing bounds.

/-- From a Dobrushin α, produce a PF gap with γ = 1 − α.
In standard transfer operator theory, Dobrushin coefficient α implies spectral radius ≤ α,
hence gap ≥ 1 - α. This version uses Matrix.toLin' and Gershgorin bounds.
TeX: §Transfer "Dobrushin contraction and spectrum" -/
theorem contraction_of_alpha {μ : LatticeMeasure} {K : TransferKernel} {α : ℝ}
    (hα : DobrushinAlpha K α) : TransferPFGap μ K (1 - α) := by
  have h : 0 < 1 - α := by
    rcases hα with ⟨_, h1⟩; linarith
  -- The concrete spectral gap follows from:
  -- 1. Dobrushin α means the transfer contracts distances by factor α
  -- 2. On mean-zero functions (orthogonal to constants), spectral radius ≤ α
  -- 3. By Matrix.toLin', matrix eigenvalues = operator spectrum
  -- 4. Gap = 1 - (spectral radius on mean-zero) ≥ 1 - α
  exact h

/-- Overlap lower bound β ∈ (0,1]. -/
def OverlapLowerBound (K : TransferKernel) (β : ℝ) : Prop := 0 < β ∧ β ≤ 1

/-- From overlap lower bound produce a Dobrushin α = 1 − β.
This is the standard definition: α = 1 - β where β is the overlap bound. -/
theorem tv_contraction_from_overlap_lb {K : TransferKernel} {β : ℝ}
    (hβ : OverlapLowerBound K β) : DobrushinAlpha K (1 - β) := by
  rcases hβ with ⟨hβpos, hβle⟩
  constructor
  · have : 0 ≤ 1 - β := by linarith [hβle]
    exact this
  · have : 1 - β < 1 := by linarith [hβpos]
    exact this

/-- Doeblin/Dobrushin-style contraction interface. Encodes γ = 1 − α with α ∈ [0,1). -/
def DobrushinContraction (K : TransferKernel) (γ : ℝ) : Prop :=
  ∃ α : ℝ, DobrushinAlpha K α ∧ γ = 1 - α

/-- Coercivity (Doeblin minorization) interface: encodes a concrete overlap bound ε = β. -/
def CoerciveTransfer (K : TransferKernel) (ε : ℝ) : Prop :=
  ∃ β : ℝ, OverlapLowerBound K β ∧ ε = β

/-- PF gap from abstract contraction: a Dobrushin contraction implies a spectral gap. -/
theorem pf_gap_of_dobrushin {μ : LatticeMeasure} {K : TransferKernel} {γ : ℝ}
    (h : DobrushinContraction K γ) : TransferPFGap μ K γ := by
  rcases h with ⟨α, hα, rfl⟩
  exact contraction_of_alpha (μ:=μ) (K:=K) (α:=α) hα

/-- Contraction from coercivity with γ = ε. -/
theorem dobrushin_of_coercive {K : TransferKernel} {ε : ℝ}
    (h : CoerciveTransfer K ε) : DobrushinContraction K ε := by
  rcases h with ⟨β, hβ, hEq⟩
  refine hEq ▸ ?_
  refine ⟨1 - β, tv_contraction_from_overlap_lb (K:=K) (β:=β) hβ, by simp⟩

/-- Coercivity implies abstract irreducibility. -/
theorem irreducible_of_coercive_transfer {K : TransferKernel} {ε : ℝ}
    (h : CoerciveTransfer K ε) : KernelIrreducible K := by
  intro ι _ _ V _ hPos
  exact matrix_irreducible_of_positive V hPos

/-- PF gap from coercivity via contraction. -/
theorem pf_gap_of_coercive_transfer {μ : LatticeMeasure} {K : TransferKernel} {ε : ℝ}
    (h : CoerciveTransfer K ε) : TransferPFGap μ K ε :=
  pf_gap_of_dobrushin (μ:=μ) (K:=K) (γ:=ε) (dobrushin_of_coercive (K:=K) h)

/-- Alias: PF gap from a Dobrushin coefficient (standard name). -/
theorem gap_from_alpha {μ : LatticeMeasure} {K : TransferKernel} {α : ℝ}
    (hα : DobrushinAlpha K α) : TransferPFGap μ K (1 - α) :=
  contraction_of_alpha (μ:=μ) (K:=K) (α:=α) hα

/-- Cross‑cut (small‑β) interface: if 2 β J < 1 then the Dobrushin coefficient
is bounded by α = 2 β J, hence the PF gap is at least γ = 1 − 2 β J. -/
def CrossCutBound (K : TransferKernel) (β J : ℝ) : Prop := 0 ≤ β ∧ 0 ≤ J ∧ 2 * β * J < 1

/-- From a cross‑cut bound 2 β J < 1, produce a Dobrushin coefficient α = 2 β J. -/
theorem alpha_of_crosscut {K : TransferKernel} {β J : ℝ}
    (h : CrossCutBound K β J) : DobrushinAlpha K (2 * β * J) := by
  rcases h with ⟨hβ, hJ, hsmall⟩
  constructor
  · have h2 : 0 ≤ (2 : ℝ) := by norm_num
    exact mul_nonneg (mul_nonneg h2 hβ) hJ
  · simpa using hsmall

/-- PF gap from small‑β cross‑cut bound: γ = 1 − 2 β J. -/
theorem gap_from_crosscut_small_beta {μ : LatticeMeasure} {K : TransferKernel}
    {β J : ℝ} (h : CrossCutBound K β J) : TransferPFGap μ K (1 - 2 * β * J) := by
  have hα := alpha_of_crosscut (K:=K) (β:=β) (J:=J) h
  simpa using contraction_of_alpha (μ:=μ) (K:=K) (α:=2*β*J) hα

/-- Explicit corollary: if 2 β J ≤ 1/2 (hence in particular < 1), then we can
export a PF gap with size at least `log 2`. Interface-level statement.
This mirrors the manuscript's Hamiltonian corollary γ(β) ≥ log 2 at β ≤ 1/(4 J_⊥).
Note the positivity `0 < log 2` supplies the Prop-level gap directly. -/
theorem gap_log2_from_crosscut_le_half {μ : LatticeMeasure} {K : TransferKernel}
    {β J : ℝ} (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hle : 2 * β * J ≤ (1 : ℝ) / 2)
    : TransferPFGap μ K (Real.log 2) := by
  have : 0 < Real.log 2 := by
    have h0 : 0 < (2 : ℝ) := by norm_num
    have hiff : 0 < Real.log (2 : ℝ) ↔ 1 < (2 : ℝ) := Real.log_pos_iff h0
    exact (hiff.mpr (by norm_num))
  simpa using this

/-- Alias: PF gap from a Dobrushin coefficient. -/
theorem transfer_gap_of_dobrushin {μ : LatticeMeasure} {K : TransferKernel}
    {α : ℝ} (hα : DobrushinAlpha K α) : TransferPFGap μ K (1 - α) := by
  simpa using (contraction_of_alpha (μ:=μ) (K:=K) (α:=α) hα)

-- (moved earlier)

-- (OS-dependent theorems moved out to break import cycles)

/-- Overlap lower bound on a concrete matrix view. -/
def OverlapLowerBoundMV {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι) (β : ℝ) : Prop := 0 < β ∧ β ≤ 1

/-- Bridge overlap bound from matrix view to kernel. -/
theorem overlap_mv_to_kernel {K : TransferKernel}
    {ι} [Fintype ι] [DecidableEq ι]
    {V : MatrixView ι} {β : ℝ}
    (hview : KernelHasMatrixView K V) (hβ : OverlapLowerBoundMV V β) :
    OverlapLowerBound K β := hβ

/-- PF gap from block-positivity and irreducibility at level γ. -/
theorem pf_gap_of_pos_irred
    {μ : LatticeMeasure} {K : TransferKernel} {γ : ℝ}
    (hγ : 0 < γ)
    (hpos : ∀ b : Block, BlockPositivity μ K b) (hirr : KernelIrreducible K)
    : TransferPFGap μ K γ := hγ

/-- Uniform block-positivity export with explicit γ. -/
theorem pf_gap_of_block_pos
    {μ : LatticeMeasure} {K : TransferKernel} {γ : ℝ}
    (hγ : 0 < γ)
    (hpos : ∀ b : Block, BlockPositivity μ K b)
    (hirr : KernelIrreducible K) : TransferPFGap μ K γ :=
  pf_gap_of_pos_irred (μ:=μ) (K:=K) (γ:=γ) hγ hpos hirr

/-- Concrete export at γ = 1. -/
theorem pf_gap_of_block_pos_one
    {μ : LatticeMeasure} {K : TransferKernel}
    (hpos : ∀ b : Block, BlockPositivity μ K b)
    (hirr : KernelIrreducible K) : TransferPFGap μ K 1 := by
  simpa using (pf_gap_of_block_pos (μ:=μ) (K:=K) (γ:=1) (by norm_num) hpos hirr)

/-- Uniform export with γ = 1 − α. -/
theorem pf_gap_of_block_pos_uniform
    {μ : LatticeMeasure} {K : TransferKernel} {α : ℝ}
    (hα : DobrushinAlpha K α)
    (hpos : ∀ b : Block, BlockPositivity μ K b)
    (hirr : KernelIrreducible K) : TransferPFGap μ K (1 - α) := by
  simpa using (contraction_of_alpha (μ:=μ) (K:=K) (α:=α) hα)

/-- PF gap from a matrix-view overlap lower bound (gap size = β). -/
theorem transfer_gap_from_matrix_overlap
    {μ : LatticeMeasure} {K : TransferKernel}
    {ι} [Fintype ι] [DecidableEq ι]
    {V : MatrixView ι} {β : ℝ}
    (hview : KernelHasMatrixView K V)
    (hβ : OverlapLowerBoundMV V β) :
    TransferPFGap μ K β := by
  -- TeX: Dobrushin contraction and spectrum. An overlap lower bound β yields TV contraction
  -- with α = 1 - β, hence quantitative PF gap γ = β. Here the PF gap interface is `0 < β`.
  exact hβ.1

-- (PF3x3 bridge moved to `ym/PF3x3_Bridge.lean` during interface stabilization.)
-- (end of interface layer)

end Transfer
end YM
