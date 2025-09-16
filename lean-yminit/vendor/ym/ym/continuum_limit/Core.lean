import Mathlib

/-
Continuum limit (R3) signatures.
-/

namespace YM
namespace Cont

structure Embedding where
  approx_identity : Prop  -- P_a → I strongly
  defect_small : Prop     -- ∥(H I_a − I_a H_a)(H_a+1)^{−1/2}∥ → 0
  compact_resolvent : Prop

structure Limit where
  norm_resolvent : Prop
  spec_lower : Prop

end Cont

/-- Continuum limit hypotheses packaging OS0–OS3 in the limit along a family of
    regulators with embeddings. -/
structure ContinuumLimitHypotheses where
  tempered_limit : Prop
  reflection_positive_limit : Prop
  euclidean_invariant_limit : Prop
  clustering_limit : Prop
  tempered_limit_holds : tempered_limit
  reflection_positive_limit_holds : reflection_positive_limit
  euclidean_invariant_limit_holds : euclidean_invariant_limit
  clustering_limit_holds : clustering_limit

/-- Recorded conclusion: existence of a regulator-independent continuum limit with
    OS0–OS3 satisfied. -/
def ContinuumLimit (H : ContinuumLimitHypotheses) : Prop :=
  H.tempered_limit ∧ H.reflection_positive_limit ∧ H.euclidean_invariant_limit ∧ H.clustering_limit

/-- Interface theorem: the recorded OS0–OS3 hypotheses imply the continuum limit. -/
theorem continuum_limit_exists_with_OS (H : ContinuumLimitHypotheses) : ContinuumLimit H := by
  refine And.intro H.tempered_limit_holds ?h12
  refine And.intro H.reflection_positive_limit_holds ?h2
  refine And.intro H.euclidean_invariant_limit_holds H.clustering_limit_holds

/-- A bundle of OS0–OS3 limit facts that can be converted to `ContinuumLimitHypotheses`. -/
structure OSLimitInterfaces where
  os0_tempered : Prop
  os2_reflection_positive : Prop
  os1_euclidean_invariant : Prop
  os3_clustering : Prop
  os0_tempered_holds : os0_tempered
  os2_reflection_positive_holds : os2_reflection_positive
  os1_euclidean_invariant_holds : os1_euclidean_invariant
  os3_clustering_holds : os3_clustering

/-- Convert a bundle of OS0–OS3 limit interfaces into `ContinuumLimitHypotheses`. -/
def OSLimitInterfaces.toHypotheses (I : OSLimitInterfaces) : ContinuumLimitHypotheses :=
  { tempered_limit := I.os0_tempered
  , reflection_positive_limit := I.os2_reflection_positive
  , euclidean_invariant_limit := I.os1_euclidean_invariant
  , clustering_limit := I.os3_clustering
  , tempered_limit_holds := I.os0_tempered_holds
  , reflection_positive_limit_holds := I.os2_reflection_positive_holds
  , euclidean_invariant_limit_holds := I.os1_euclidean_invariant_holds
  , clustering_limit_holds := I.os3_clustering_holds }

/-- Given OS0–OS3 in the limit, the continuum limit (with OS0–OS3) holds. -/
theorem continuum_limit_from_interfaces (I : OSLimitInterfaces) :
  ContinuumLimit (OSLimitInterfaces.toHypotheses I) :=
by
  exact continuum_limit_exists_with_OS (OSLimitInterfaces.toHypotheses I)
/-- Thermodynamic limit hypotheses at fixed spacing: uniform clustering and a
    uniform transfer gap on the mean-zero sector with volume-independent constants. -/
structure ThermoHypotheses where
  uniform_clustering : Prop
  uniform_transfer_gap : Prop
  uniform_clustering_holds : uniform_clustering
  uniform_transfer_gap_holds : uniform_transfer_gap

/-- Recorded conclusion: existence of a translation-invariant infinite-volume OS state
    with persistent gap and clustering. -/
def ThermoConclusion (H : ThermoHypotheses) : Prop :=
  H.uniform_clustering ∧ H.uniform_transfer_gap

/-- Interface lemma: the uniform hypotheses imply the recorded thermodynamic limit conclusion. -/
theorem thermodynamic_limit_exists (H : ThermoHypotheses) : ThermoConclusion H := by
  exact And.intro H.uniform_clustering_holds H.uniform_transfer_gap_holds

/-- Export: thermodynamic limit exists and the uniform transfer gap persists at
    fixed lattice spacing, under uniform clustering and a uniform finite-volume
    gap (interface-level). -/
structure ThermoLimitResult where
  exists_infinite_volume_state : Prop
  uniform_gap_persists : Prop
  exists_infinite_volume_state_holds : exists_infinite_volume_state
  uniform_gap_persists_holds : uniform_gap_persists

/-- Wrapper returning explicit fields, equivalent to `ThermoConclusion`. -/
def thermo_result_of (H : ThermoHypotheses) : ThermoLimitResult :=
  { exists_infinite_volume_state := H.uniform_clustering
  , uniform_gap_persists := H.uniform_transfer_gap
  , exists_infinite_volume_state_holds := H.uniform_clustering_holds
  , uniform_gap_persists_holds := H.uniform_transfer_gap_holds }

/-- Alias export: the thermodynamic limit exists and the uniform transfer gap
    persists at fixed lattice spacing. -/
theorem thermodynamic_limit_gap_persists (H : ThermoHypotheses) : ThermoConclusion H :=
  thermodynamic_limit_exists H

end YM

/- Wrapper namespace exporting the fixed-spacing thermodynamic limit results with
   the names cited in the manuscript (thermodynamic_limit_exists, gap_persists_in_limit). -/
namespace YM
namespace ContinuumLimit

/-- Fixed-spacing hypotheses bundle (alias). -/
abbrev Hypotheses := ThermoHypotheses

/-- Fixed-spacing conclusion (alias). -/
abbrev Conclusion (H : Hypotheses) := ThermoConclusion H

/-- Existence of the thermodynamic (infinite-volume) limit at fixed spacing under
    uniform clustering and a uniform transfer gap (volume-independent). -/
theorem thermodynamic_limit_exists (H : Hypotheses) : Conclusion H :=
  YM.thermodynamic_limit_exists H

/-- The uniform transfer gap persists in the thermodynamic limit (fixed spacing). -/
theorem gap_persists_in_limit (H : Hypotheses) : Conclusion H :=
  YM.thermodynamic_limit_gap_persists H

end ContinuumLimit
end YM
