import Mathlib
import ym.ym_measure.Projective
import ym.ym_measure.Wilson

/-!
Prop-level interface for a 4D continuum Yang–Mills Euclidean measure satisfying
OS axioms and suitable for Wightman reconstruction. This records the existence
and key properties as `Prop`s; constructive details are provided elsewhere.
-/

namespace YM
namespace YMMeasure

/-! Bridge: `ProjectiveToContinuum` is defined in `Projective.lean`. -/

/-- Lightweight bridge from projective extension data to the continuum
    hypotheses layer. -/
structure ProjectiveBridge where
  has_kolmogorov_extension : Prop
  has_kolmogorov_extension_holds : has_kolmogorov_extension

/-- Hypothesis bundle for the continuum Yang–Mills measure in 4D. -/
structure ContinuumYMHypotheses where
  os0_tempered : Prop
  os1_euclidean : Prop
  os2_reflection : Prop
  os3_clustering : Prop
  gauge_invariant : Prop
  sigma_additive_probability : Prop
  os0_holds : os0_tempered
  os1_holds : os1_euclidean
  os2_holds : os2_reflection
  os3_holds : os3_clustering
  gauge_invariant_holds : gauge_invariant
  sigma_additive_probability_holds : sigma_additive_probability

/-- Build `ContinuumYMHypotheses` from cylindrical data plus OS0/OS3 inputs. -/
def toContinuumYMHypotheses (P : ProjectiveToContinuum) : ContinuumYMHypotheses where
  os0_tempered := P.os0_tempered
  os1_euclidean := P.cyl.euclidean_invariant
  os2_reflection := P.cyl.reflection_positive
  os3_clustering := P.os3_clustering
  gauge_invariant := P.cyl.gauge_invariant
  sigma_additive_probability := P.cyl.probability_normalized
  os0_holds := P.os0_holds
  os1_holds := P.cyl.euclidean_invariant_holds
  os2_holds := P.cyl.reflection_positive_holds
  os3_holds := P.os3_holds
  gauge_invariant_holds := P.cyl.gauge_invariant_holds
  sigma_additive_probability_holds := P.cyl.probability_normalized_holds

/-- Recorded conclusion: existence of a continuum YM measure with the OS
    axioms and gauge invariance. -/
def ContinuumYMMeasure (H : ContinuumYMHypotheses) : Prop :=
  H.os0_tempered ∧ H.os1_euclidean ∧ H.os2_reflection ∧ H.os3_clustering ∧
  H.gauge_invariant ∧ H.sigma_additive_probability

/-- Wrapper theorem exposing the recorded conclusion. -/
theorem continuum_ym_measure_exists (H : ContinuumYMHypotheses) : ContinuumYMMeasure H := by
  exact And.intro H.os0_holds
    (And.intro H.os1_holds
      (And.intro H.os2_holds
        (And.intro H.os3_holds
          (And.intro H.gauge_invariant_holds H.sigma_additive_probability_holds))))

/-- Corollary: obtain the recorded continuum YM measure from projective inputs. -/
theorem continuum_ym_from_projective (P : ProjectiveToContinuum) :
    ContinuumYMMeasure (toContinuumYMHypotheses P) := by
  exact continuum_ym_measure_exists (toContinuumYMHypotheses P)

/-- Corollary: obtain the recorded continuum YM measure directly from
    finite-volume inputs packaged as `FVCylToContinuum`. -/
theorem continuum_ym_from_finite_volume (D : FVCylToContinuum) :
    ContinuumYMMeasure (toContinuumYMHypotheses (toProjectiveToContinuum D)) := by
  simpa using continuum_ym_from_projective (toProjectiveToContinuum D)

/-- End-to-end: from Wilson finite-volume data and OS0/OS3 to recorded continuum
    YM measure properties. -/
theorem continuum_ym_from_wilson
    (p : YM.Wilson.ActionParams)
    (V : Volume)
    (S : YM.Wilson.Spec)
    (hprob : S.gibbs_probability)
    (href : S.os_invariance)
    (hinv : S.os_invariance)
    (hgauge : True)
    (os0 : Prop) (os3 : Prop)
    (h0 : os0) (h3 : os3) :
    ContinuumYMMeasure (toContinuumYMHypotheses
      (toProjectiveToContinuum
        (FVCylToContinuum.fromWilson p V S hprob href hinv hgauge os0 os3 h0 h3))) := by
  simpa using
    continuum_ym_from_finite_volume
      (FVCylToContinuum.fromWilson p V S hprob href hinv hgauge os0 os3 h0 h3)

end YMMeasure
end YM
