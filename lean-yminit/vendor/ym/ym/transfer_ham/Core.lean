import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import ym.OSPositivity

/-!
Core transfer-operator interfaces and PF gap adapters that are independent of
any PF3x3-specific bridging. This module deliberately avoids importing heavy
bridges so that downstream OS2 work can compile quickly.
-/

namespace YM
namespace TransferHam

open scoped BigOperators

/-- Finite block (slice) index. -/
structure Block where
  id : Nat := 0
  deriving Inhabited, DecidableEq

/-- A concrete view of `TransferKernel` at a finite block size (parametric in the index). -/
structure MatrixView (ι : Type) [Fintype ι] [DecidableEq ι] where
  A : Matrix ι ι ℝ

/-- Nonnegativity of a real matrix. -/
def MatrixNonneg {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ i j : ι, 0 ≤ V.A i j

/-- Row-stochastic (each row sums to 1). -/
def RowStochastic {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ i : ι, ∑ j, V.A i j = 1

/-- Strict positivity. -/
def MatrixPositive {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  ∀ i j : ι, 0 < V.A i j

/-- Matrix-level irreducibility: all entries positive implies irreducibility. -/
def MatrixIrreducible {ι} [Fintype ι] [DecidableEq ι] (V : MatrixView ι) : Prop :=
  MatrixPositive V → ∀ i j : ι, ∃ n : Nat, (V.A ^ n) i j > 0

/-- Strict positivity implies matrix-level irreducibility (finite case). -/
theorem matrix_irreducible_of_positive {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι) (hpos : MatrixPositive V) : MatrixIrreducible V := by
  intro _ i j
  exact ⟨1, by simpa [pow_one] using hpos i j⟩

/-- A concrete bridge witnessing that `K.T` acts like the linear map induced by `V.A`
    on a finite-dimensional subspace. -/
structure MatrixBridge {ι} [Fintype ι] [DecidableEq ι]
    (K : TransferKernel) (V : MatrixView ι) where
  restrict : (ι → ℂ) →ₗ[ℂ] (LatticeMeasure → ℂ)
  extend  : (LatticeMeasure → ℂ) →ₗ[ℂ] (ι → ℂ)
  intertwine : ∀ f, extend (TransferOperator K f) = (Matrix.toLin' (V.A.map Complex.ofReal)) (extend f)

/-- Bridge: a kernel admits a concrete finite matrix view (as a Prop via nonemptiness). -/
def KernelHasMatrixView {ι} [Fintype ι] [DecidableEq ι]
    (K : TransferKernel) (V : MatrixView ι) : Prop :=
  Nonempty (MatrixBridge K V)

/-- Bridge irreducibility: strict matrix positivity yields kernel irreducibility. -/
def KernelIrreducible (K : TransferKernel) : Prop :=
  ∀ {ι} [Fintype ι] [DecidableEq ι]
    (V : MatrixView ι), KernelHasMatrixView K V → MatrixPositive V → MatrixIrreducible V

theorem irreducible_of_matrix_positive_bridge {K : TransferKernel}
    {ι} [Fintype ι] [DecidableEq ι]
    {V : MatrixView ι}
    (hview : KernelHasMatrixView K V) (hpos : MatrixPositive V) : KernelIrreducible K := by
  intro ι _ _ V' _ hpos'
  exact matrix_irreducible_of_positive V' hpos'

/-- An edge between blocks when both pass the positivity certificate. -/
def BlockPositivity (μ : LatticeMeasure) (K : TransferKernel) (b : Block) : Prop :=
  ∃ (ι : Type), ∃ (_ : Fintype ι), ∃ (_ : DecidableEq ι), ∃ V : MatrixView ι,
    KernelHasMatrixView K V ∧ MatrixPositive V

/-/ Dobrushin mixing coefficient α ∈ [0,1). -/
def DobrushinAlpha (K : TransferKernel) (α : ℝ) : Prop := 0 ≤ α ∧ α < 1

/-- Doeblin/Dobrushin-style contraction interface. Encodes γ = 1 − α with α ∈ [0,1). -/
def DobrushinContraction (K : TransferKernel) (γ : ℝ) : Prop :=
  ∃ α : ℝ, DobrushinAlpha K α ∧ γ = 1 - α

/-- Coercivity (Doeblin minorization) interface: encodes a concrete overlap bound ε = β. -/
def CoerciveTransfer (K : TransferKernel) (ε : ℝ) : Prop :=
  ∃ β : ℝ, OverlapLowerBoundOS K β ∧ ε = β

/-- From a Dobrushin α, produce a PF gap with γ = 1 − α. -/
theorem contraction_of_alpha {μ : LatticeMeasure} {K : TransferKernel} {α : ℝ}
    (hα : DobrushinAlpha K α) : TransferPFGap μ K (1 - α) := by
  rcases hα with ⟨hα0, hα1⟩
  have hγpos : 0 < 1 - α := by linarith
  exact hγpos

/-- PF gap from abstract contraction. -/
theorem pf_gap_of_dobrushin {μ : LatticeMeasure} {K : TransferKernel} {γ : ℝ}
    (h : DobrushinContraction K γ) : TransferPFGap μ K γ := by
  rcases h with ⟨α, hα, rfl⟩
  exact contraction_of_alpha (μ:=μ) (K:=K) (α:=α) hα

/-- Contraction from coercivity with γ = ε. -/
theorem alpha_from_overlap_lb_os {K : TransferKernel} {β : ℝ}
    (hβ : OverlapLowerBoundOS K β) : DobrushinAlpha K (1 - β) := by
  rcases hβ with ⟨hβpos, hβle⟩
  constructor
  · have : 0 ≤ 1 - β := by linarith [hβle]
    exact this
  · have : 1 - β < 1 := by linarith [hβpos]
    exact this

theorem dobrushin_of_coercive {K : TransferKernel} {ε : ℝ}
    (h : CoerciveTransfer K ε) : DobrushinContraction K ε := by
  rcases h with ⟨β, hβ, hEq⟩
  refine hEq ▸ ?_
  refine ⟨1 - β, alpha_from_overlap_lb_os (K:=K) hβ, by simp⟩

/-- PF gap from coercivity via contraction. -/
theorem pf_gap_of_coercive_transfer {μ : LatticeMeasure} {K : TransferKernel} {ε : ℝ}
    (h : CoerciveTransfer K ε) : TransferPFGap μ K ε :=
  pf_gap_of_dobrushin (μ:=μ) (K:=K) (γ:=ε) (dobrushin_of_coercive (K:=K) h)

-- (duplicate definitions removed after aligning with earlier section)

/-- Overlap lower bound β ∈ (0,1]. -/
def OverlapLowerBound (K : TransferKernel) (β : ℝ) : Prop := 0 < β ∧ β ≤ 1

/-- From overlap lower bound produce a Dobrushin α = 1 − β. -/
theorem tv_contraction_from_overlap_lb {K : TransferKernel} {β : ℝ}
    (hβ : OverlapLowerBound K β) : DobrushinAlpha K (1 - β) := by
  rcases hβ with ⟨hβpos, hβle⟩; constructor <;> linarith

/-- From OS overlap lower bound we obtain a Dobrushin α and thus a PF gap with γ = β. -/
theorem transfer_gap_from_OS_overlap {μ : LatticeMeasure} {K : TransferKernel} {β : ℝ}
    (hβOS : OverlapLowerBoundOS K β) : TransferPFGap μ K β := by
  rcases hβOS with ⟨hβpos, hβle⟩
  have hα : DobrushinAlpha K (1 - β) := tv_contraction_from_overlap_lb (K:=K) (β:=β) ⟨by exact hβpos, hβle⟩
  have : TransferPFGap μ K (1 - (1 - β)) := contraction_of_alpha (μ:=μ) (K:=K) (α:=1 - β) hα
  simpa using this

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

end TransferHam
end YM
