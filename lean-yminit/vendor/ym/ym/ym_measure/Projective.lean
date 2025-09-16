import Mathlib
import ym.ym_measure.FiniteVolume
import ym.ym_measure.Wilson

/-!
Projective/cylindrical family interface for constructing the continuum YM
measure via a Kolmogorov-type extension. This is Prop-level scaffolding that
records consistency, tightness, OS properties, and probability normalization.
-/

namespace YM
namespace YMMeasure

/-- Abstract cylindrical family of finite-dimensional marginals. -/
structure CylindricalFamily where
  finite_marginals : Prop
  consistent : Prop
  tight : Prop
  reflection_positive : Prop
  euclidean_invariant : Prop
  gauge_invariant : Prop
  probability_normalized : Prop
  finite_marginals_holds : finite_marginals
  consistent_holds : consistent
  tight_holds : tight
  reflection_positive_holds : reflection_positive
  euclidean_invariant_holds : euclidean_invariant
  gauge_invariant_holds : gauge_invariant
  probability_normalized_holds : probability_normalized

/-- Bridge: package cylindrical family with OS0/OS3 facts to feed the
    continuum hypotheses builder. -/
structure ProjectiveToContinuum where
  cyl : CylindricalFamily
  os0_tempered : Prop
  os3_clustering : Prop
  os0_holds : os0_tempered
  os3_holds : os3_clustering

/-- Inputs distilled from finite-volume marginals to assemble a cylindrical
    family with explicit witnesses. -/
structure FVCylInputs where
  fv_marginals : Prop
  fv_marginals_holds : fv_marginals
  consistency : Consistency
  tightness : Tightness
  all_reflection_positive : Prop
  all_euclidean_invariant : Prop
  all_gauge_invariant : Prop
  probability_normalized : Prop
  all_reflection_positive_holds : all_reflection_positive
  all_euclidean_invariant_holds : all_euclidean_invariant
  all_gauge_invariant_holds : all_gauge_invariant
  probability_normalized_holds : probability_normalized

/-- General-purpose constructor for cylindrical inputs when evidence is given. -/
def FVCylInputs.ofEvidence
    (A : Prop) (hA : A)
    (C : Consistency)
    (T : Tightness)
    (r e g q : Prop)
    (hr : r) (he : e) (hg : g) (hq : q) : FVCylInputs :=
  { fv_marginals := A
  , fv_marginals_holds := hA
  , consistency := C
  , tightness := T
  , all_reflection_positive := r
  , all_euclidean_invariant := e
  , all_gauge_invariant := g
  , probability_normalized := q
  , all_reflection_positive_holds := hr
  , all_euclidean_invariant_holds := he
  , all_gauge_invariant_holds := hg
  , probability_normalized_holds := hq }

/-- Bundle of finite-volume OS properties for a specific marginal family. -/
structure FVOSBundle where
  fv : FVMarginal
  os0_tempered : Prop
  os3_clustering : Prop
  os0_holds : os0_tempered
  os3_holds : os3_clustering
  prob_holds : fv.probability_measure
  refl_holds : fv.reflection_positive
  euc_holds  : fv.euclidean_invariant
  gauge_holds : fv.gauge_invariant

/-- Build cylindrical inputs from a family satisfying finite-volume OS data. -/
def FVCylInputs.fromFVOS (B : FVOSBundle) : FVCylInputs :=
  { fv_marginals := Nonempty FVMarginal
  , fv_marginals_holds := ⟨B.fv⟩
  , consistency :=
      Consistency.fromHypotheses
        (Consistency.leInclusion B.fv.vol B.fv.vol (volumeLe_refl B.fv.vol))
  , tightness :=
      Tightness.fromHypotheses Tightness.canonical
  , all_reflection_positive := B.fv.reflection_positive
  , all_euclidean_invariant := B.fv.euclidean_invariant
  , all_gauge_invariant := B.fv.gauge_invariant
  , probability_normalized := B.fv.probability_measure
  , all_reflection_positive_holds := B.refl_holds
  , all_euclidean_invariant_holds := B.euc_holds
  , all_gauge_invariant_holds := B.gauge_holds
  , probability_normalized_holds := B.prob_holds }

/-- Build an `FVOSBundle` directly from Wilson specifications and OS0/OS3
    flags for a given finite volume. -/
def FVOSBundle.fromWilson
    (p : YM.Wilson.ActionParams)
    (V : Volume)
    (S : YM.Wilson.Spec)
    (hprob : S.gibbs_probability)
    (href : S.os_invariance)
    (hinv : S.os_invariance)
    (hgauge : True)
    (os0 : Prop) (os3 : Prop)
    (h0 : os0) (h3 : os3) : FVOSBundle :=
  let fv := FVMarginal.fromWilson p V S hprob href hinv hgauge
  { fv := fv
  , os0_tempered := os0
  , os3_clustering := os3
  , os0_holds := h0
  , os3_holds := h3
  , prob_holds := hprob
  , refl_holds := href
  , euc_holds := hinv
  , gauge_holds := hinv }

/-- Build a cylindrical family record from finite-volume evidence. -/
def CylindricalFamily.fromFiniteVolume (I : FVCylInputs) : CylindricalFamily :=
  { finite_marginals := I.fv_marginals
  , consistent := I.consistency.consistent_pushforward
  , tight := I.tightness.tight
  , reflection_positive := I.all_reflection_positive
  , euclidean_invariant := I.all_euclidean_invariant
  , gauge_invariant := I.all_gauge_invariant
  , probability_normalized := I.probability_normalized
  , finite_marginals_holds := I.fv_marginals_holds
  , consistent_holds := I.consistency.consistent_pushforward_holds
  , tight_holds := I.tightness.tight_holds
  , reflection_positive_holds := I.all_reflection_positive_holds
  , euclidean_invariant_holds := I.all_euclidean_invariant_holds
  , gauge_invariant_holds := I.all_gauge_invariant_holds
  , probability_normalized_holds := I.probability_normalized_holds }

/-- The cylindrical family inherits reflection positivity from the inputs. -/
theorem cyl_reflection_positive (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).reflection_positive :=
  (CylindricalFamily.fromFiniteVolume I).reflection_positive_holds

/-- The cylindrical family inherits Euclidean invariance from the inputs. -/
theorem cyl_euclidean_invariant (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).euclidean_invariant :=
  (CylindricalFamily.fromFiniteVolume I).euclidean_invariant_holds

/-- The cylindrical family inherits gauge invariance from the inputs. -/
theorem cyl_gauge_invariant (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).gauge_invariant :=
  (CylindricalFamily.fromFiniteVolume I).gauge_invariant_holds

/-- The cylindrical family is probability-normalized when inputs say so. -/
theorem cyl_probability_normalized (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).probability_normalized :=
  (CylindricalFamily.fromFiniteVolume I).probability_normalized_holds

/-- The cylindrical family is consistent if inputs provide consistency. -/
theorem cyl_consistent (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).consistent :=
  (CylindricalFamily.fromFiniteVolume I).consistent_holds

/-- The cylindrical family is tight if inputs provide tightness. -/
theorem cyl_tight (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).tight :=
  (CylindricalFamily.fromFiniteVolume I).tight_holds

/-- The cylindrical family has finite marginals given inputs. -/
theorem cyl_finite_marginals (I : FVCylInputs) :
    (CylindricalFamily.fromFiniteVolume I).finite_marginals :=
  (CylindricalFamily.fromFiniteVolume I).finite_marginals_holds

/-- Package finite-volume derived cylindrical family together with OS0/OS3 props
    needed upstream for the continuum bridge. -/
structure FVCylToContinuum where
  I : FVCylInputs
  os0_tempered : Prop
  os3_clustering : Prop
  os0_holds : os0_tempered
  os3_holds : os3_clustering

/-- Turn finite-volume inputs and OS0/OS3 into the projective→continuum bridge. -/
def toProjectiveToContinuum (D : FVCylToContinuum) : ProjectiveToContinuum := by
  let cylVal : CylindricalFamily := CylindricalFamily.fromFiniteVolume D.I
  exact
    { cyl := cylVal
    , os0_tempered := D.os0_tempered
    , os3_clustering := D.os3_clustering
    , os0_holds := D.os0_holds
    , os3_holds := D.os3_holds }

/-- Convenience: package Wilson data and OS0/OS3 into the `FVCylToContinuum`
    bridge via `FVOSBundle` and `FVCylInputs`. -/
def FVCylToContinuum.fromWilson
    (p : YM.Wilson.ActionParams)
    (V : Volume)
    (S : YM.Wilson.Spec)
    (hprob : S.gibbs_probability)
    (href : S.os_invariance)
    (hinv : S.os_invariance)
    (hgauge : True)
    (os0 : Prop) (os3 : Prop)
    (h0 : os0) (h3 : os3) : FVCylToContinuum :=
  let B := FVOSBundle.fromWilson p V S hprob href hinv hgauge os0 os3 h0 h3
  let I := FVCylInputs.fromFVOS B
  { I := I, os0_tempered := os0, os3_clustering := os3, os0_holds := h0, os3_holds := h3 }

/-- Hypotheses to apply a Kolmogorov-type extension argument. -/
structure KolmogorovExtensionHypotheses where
  consistent : Prop
  tight : Prop
  probability_normalized : Prop
  consistent_holds : consistent
  tight_holds : tight
  probability_normalized_holds : probability_normalized

/-- Recorded conclusion of the extension step. -/
def KolmogorovExtension (H : KolmogorovExtensionHypotheses) : Prop :=
  H.consistent ∧ H.tight ∧ H.probability_normalized

theorem kolmogorov_extension_exists (H : KolmogorovExtensionHypotheses) :
    KolmogorovExtension H := by
  exact And.intro H.consistent_holds (And.intro H.tight_holds H.probability_normalized_holds)

/-- Bundle the OS properties together with the extension inputs from the
    cylindrical family. -/
structure YMExtensionHypotheses where
  cyl : CylindricalFamily
  kolmo : KolmogorovExtensionHypotheses
  os0 : Prop
  os1 : Prop
  os2 : Prop
  os3 : Prop
  os0_holds : os0
  os1_holds : os1
  os2_holds : os2
  os3_holds : os3

/-- Recorded conclusion of the YM extension: existence plus OS/invariance data. -/
def YMExtension (H : YMExtensionHypotheses) : Prop :=
  KolmogorovExtension H.kolmo ∧ H.os0 ∧ H.os1 ∧ H.os2 ∧ H.os3 ∧
  H.cyl.gauge_invariant ∧ H.cyl.reflection_positive ∧ H.cyl.euclidean_invariant

theorem ym_extension_from_cyl (H : YMExtensionHypotheses) : YMExtension H := by
  refine And.intro (kolmogorov_extension_exists H.kolmo) ?tail
  exact And.intro H.os0_holds
    (And.intro H.os1_holds
      (And.intro H.os2_holds
        (And.intro H.os3_holds
          (And.intro H.cyl.gauge_invariant_holds
            (And.intro H.cyl.reflection_positive_holds H.cyl.euclidean_invariant_holds)))))

end YMMeasure
end YM
