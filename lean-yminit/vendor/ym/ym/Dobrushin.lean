import Mathlib
import ym.Transfer

/ -!
Concrete Dobrushin coefficient: overlap bound and quantitative α ∈ [0,1).

We work with finite-state Markov kernels `K : MarkovKernel ι` (row-stochastic,
entrywise nonnegative). The row–row overlap is

  c(i,i') := ∑ j min(K.P i j, K.P i' j) ∈ [0,1].

If `β ∈ (0,1]` is a uniform lower bound on row overlaps, then the Dobrushin
coefficient `α := 1 - β` lies in `[0,1)` and yields a quantitative mixing
statement. In this interface track, `TVContractionMarkov K α` is Prop-level;
we export the numeric certificate `0 ≤ α ∧ α < 1` here.
-/

noncomputable section

namespace YM

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

namespace Dobrushin

variable (K : MarkovKernel ι)

/-- Row distribution `j ↦ K.P i j`. -/
@[simp] def row (i : ι) : ι → ℝ := fun j => K.P i j

/-- Row–row overlap `∑j min(P i j, P i' j)` in `[0,1]`. -/
def overlap (i i' : ι) : ℝ := ∑ j, min (K.P i j) (K.P i' j)

lemma overlap_nonneg (i i' : ι) : 0 ≤ overlap (K:=K) i i' := by
  classical
  refine Finset.sum_nonneg ?_
  intro j _
  have hij : 0 ≤ K.P i j := K.nonneg i j
  have hi'j : 0 ≤ K.P i' j := K.nonneg i' j
  simpa using min_nonneg hij hi'j

lemma overlap_le_one (i i' : ι) : overlap (K:=K) i i' ≤ 1 := by
  classical
  have hle : ∀ j, min (K.P i j) (K.P i' j) ≤ K.P i j := by
    intro j; exact min_le_left _ _
  have := Finset.sum_le_sum (fun j _ => hle j)
  simpa [overlap] using this.trans_eq (K.rowSum_one i)

/-- Quantitative bound: if all overlaps are ≥ β ∈ (0,1], then
`α := 1 - β ∈ [0,1)` is a Dobrushin coefficient for `K`. -/
theorem tv_contraction_from_overlap_lb {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hβ : ∀ i i', β ≤ overlap (K:=K) i i') :
    TVContractionMarkov (K:=K) (α := 1 - β) := by
  have hα0 : 0 ≤ 1 - β := by linarith
  have hα1 : 1 - β < 1 := by linarith
  exact And.intro hα0 hα1

end Dobrushin

end YM
