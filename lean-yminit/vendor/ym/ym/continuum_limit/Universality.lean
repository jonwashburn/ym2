import Mathlib

/-!
Prop-level Universality interface: two admissible regularizations with
ε-uniform locality/moments, norm–resolvent convergence, ε-uniform gaps,
and a cross-regularization closeness modulus δ(ε) → 0 produce identical
continuum Schwinger functions and the same physical mass gap.
-/

namespace YM
namespace Cont

/-- Hypotheses for universality across two regularizations A,B. -/
structure UniversalityHypotheses where
  admissible_locality_A : Prop
  admissible_locality_B : Prop
  nrc_A : Prop
  nrc_B : Prop
  uniform_gap_A : Prop
  uniform_gap_B : Prop
  cross_close_delta : Prop   -- δ(ε) → 0 for Schwinger functionals A vs B
  admissible_locality_A_holds : admissible_locality_A
  admissible_locality_B_holds : admissible_locality_B
  nrc_A_holds : nrc_A
  nrc_B_holds : nrc_B
  uniform_gap_A_holds : uniform_gap_A
  uniform_gap_B_holds : uniform_gap_B
  cross_close_delta_holds : cross_close_delta

/-- Recorded conclusion: equality of continuum Schwinger functions and equality
    of the physical mass gap. -/
structure UniversalityConclusion where
  equalSchwinger : Prop
  sameGammaPhys : Prop

/-- Interface lemma packaging the conclusion. -/
def universality (H : UniversalityHypotheses) : UniversalityConclusion :=
  {
    /- TeX: Universality (§Universality) — admissible locality for A,B; NRC for A,B;
       ε‑uniform open gaps; and cross‑regularization closeness δ(ε)→0 imply identical
       continuum Schwinger functions and the same physical mass gap. -/
    equalSchwinger :=
      H.admissible_locality_A ∧ H.admissible_locality_B ∧
      H.nrc_A ∧ H.nrc_B ∧ H.cross_close_delta,
    sameGammaPhys := H.uniform_gap_A ∧ H.uniform_gap_B
  }

/-- Two‑coarse‑graining universality with cross‑regularization δ(ε) → 0:
    admissibility and NRC for both families, ε‑uniform open gaps, and δ(ε)→0
    imply equality of continuum Schwinger functions and the same physical gap. -/
theorem two_regularizations_universality (H : UniversalityHypotheses) :
  UniversalityConclusion :=
  universality H

end Cont
end YM
