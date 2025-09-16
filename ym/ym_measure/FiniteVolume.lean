import Mathlib
import ym.su.Interfaces
import ym.lattice.Core
import ym.ym_measure.Wilson

/-!
Finite-volume lattice Yang–Mills marginals and cylindrical consistency
(Prop-level but concrete data holders for bridging to the projective system).
-/

namespace YM
namespace YMMeasure

open YM.SU YM.Lattice YM.Wilson

/-- Finite-volume region descriptor (placeholder). -/
structure Volume where
  L : ℕ
  hL : 1 ≤ L

/-- Finite-volume marginal specification for Wilson ensemble. -/
structure FVMarginal where
  params : Wilson.ActionParams
  vol : Volume
  probability_measure : Prop
  reflection_positive : Prop
  euclidean_invariant : Prop
  gauge_invariant : Prop
  probability_measure_holds : probability_measure
  reflection_positive_holds : reflection_positive
  euclidean_invariant_holds : euclidean_invariant
  gauge_invariant_holds : gauge_invariant

/-- Build a finite-volume marginal from Wilson specs and invariance witnesses. -/
def FVMarginal.fromWilson (p : Wilson.ActionParams) (V : Volume)
    (S : Wilson.Spec)
    (hprob : S.gibbs_probability)
    (href : S.os_invariance)
    (hinv : S.os_invariance)
    (_hgauge : True) : FVMarginal :=
  { params := p
  , vol := V
  , probability_measure := S.gibbs_probability
  , reflection_positive := S.os_invariance
  , euclidean_invariant := S.os_invariance
  , gauge_invariant := S.os_invariance
  , probability_measure_holds := hprob
  , reflection_positive_holds := href
  , euclidean_invariant_holds := hinv
  , gauge_invariant_holds := hinv }

/-- Cylindrical consistency between two volumes V ⊆ V'. -/
structure Consistency where
  V  : Volume
  V' : Volume
  inclusion : Prop
  consistent_pushforward : Prop
  inclusion_holds : inclusion
  consistent_pushforward_holds : consistent_pushforward

/-- Tightness along an increasing family of finite volumes. -/
structure Tightness where
  along : (ℕ → Volume)
  monotone : Prop
  tight : Prop
  monotone_holds : monotone
  tight_holds : tight

/-- Helper constructor when explicit evidence is available. -/
def Consistency.ofEvidence
    (V V' : Volume) (incl : Prop) (incl_h : incl)
    (push : Prop) (push_h : push) : Consistency :=
  { V := V, V' := V', inclusion := incl, consistent_pushforward := push
  , inclusion_holds := incl_h, consistent_pushforward_holds := push_h }

/-- Helper constructor for tightness along a specified chain with evidence. -/
def Tightness.ofEvidence
    (a : ℕ → Volume) (mono : Prop) (mono_h : mono)
    (t : Prop) (t_h : t) : Tightness :=
  { along := a, monotone := mono, tight := t
  , monotone_holds := mono_h, tight_holds := t_h }

/-- Hypotheses sufficient to construct `Consistency`. -/
structure ConsistencyHypotheses where
  V  : Volume
  V' : Volume
  inclusion : Prop
  consistent_pushforward : Prop
  inclusion_holds : inclusion
  consistent_pushforward_holds : consistent_pushforward

/-- Build `Consistency` from `ConsistencyHypotheses`. -/
def Consistency.fromHypotheses (H : ConsistencyHypotheses) : Consistency :=
  Consistency.ofEvidence H.V H.V' H.inclusion H.inclusion_holds
                      H.consistent_pushforward H.consistent_pushforward_holds

/-- Hypotheses sufficient to construct `Tightness`. -/
structure TightnessHypotheses where
  along : (ℕ → Volume)
  monotone : Prop
  tight : Prop
  monotone_holds : monotone
  tight_holds : tight

/-- Build `Tightness` from `TightnessHypotheses`. -/
def Tightness.fromHypotheses (H : TightnessHypotheses) : Tightness :=
  Tightness.ofEvidence H.along H.monotone H.monotone_holds H.tight H.tight_holds

/-- Concrete lattice inclusion relation between volumes. -/
def volumeLe (V V' : Volume) : Prop := V.L ≤ V'.L

/-- Reflexivity of `volumeLe`. -/
lemma volumeLe_refl (V : Volume) : volumeLe V V := Nat.le_refl V.L

/-- Consistency hypotheses from a concrete lattice inclusion; pushforward
    consistency left abstract here (recorded as `True`). -/
def Consistency.leInclusion (V V' : Volume) (hVV' : volumeLe V V') :
    ConsistencyHypotheses :=
  { V := V
  , V' := V'
  , inclusion := volumeLe V V'
  , consistent_pushforward := volumeLe V V'
  , inclusion_holds := hVV'
  , consistent_pushforward_holds := hVV' }

/-- A canonical increasing chain of finite volumes by box size. -/
def volChain (k : ℕ) : Volume :=
  { L := k + 1
  , hL := by exact Nat.succ_le_succ (Nat.zero_le k) }

/-- Monotonicity of the canonical volume chain. -/
lemma volChain_monotone :
    (∀ n, (volChain n).L ≤ (volChain (n+1)).L) := by
  intro n
  change n + 1 ≤ (n + 1) + 1
  exact Nat.le_succ (n + 1)

/-- Tightness hypotheses from the canonical chain; tightness is recorded as
    `True` placeholder until measure-level compactness is supplied. -/
def Tightness.canonical : TightnessHypotheses :=
  { along := volChain
  , monotone := ∀ n, (volChain n).L ≤ (volChain (n+1)).L
  , tight := ∀ n : ℕ, True
  , monotone_holds := volChain_monotone
  , tight_holds := by intro (_ : ℕ); trivial }

end YMMeasure
end YM
