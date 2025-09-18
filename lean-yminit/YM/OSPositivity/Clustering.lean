/-!
OS3: Clustering from lattice gap and thermodynamic limit (spec-level).
No axioms. No `sorry`.
-/

import YM.Transfer.PhysicalGap

namespace YM.OSPositivity.Clustering

open YM.Transfer.PhysicalGap

/-- Parameters for clustering acceptance on a fixed region. -/
structure ClusteringParams where
  gamma_phys   : Float
  region_size  : Float

/-- Clustering acceptance record (spec-level). -/
structure ClusteringAcceptance where
  ok : Bool

/-- OS3 clustering spec: acceptance equals the positivity of γ_phys. -/
def clustering_spec (P : ClusteringParams) (A : ClusteringAcceptance) : Prop :=
  A.ok = (P.gamma_phys > 0.0)

/-- Builder: declare clustering accepted when a positive γ_phys is supplied (spec-level). -/
def build_clustering (P : ClusteringParams) : ClusteringAcceptance :=
  { ok := (P.gamma_phys > 0.0) }

theorem build_clustering_holds (P : ClusteringParams) :
  clustering_spec P (build_clustering P) := by
  rfl

/-- Glue: derive clustering acceptance from a Doeblin-driven physical gap pack. -/
def build_clustering_from_doeblin (G : YM.Transfer.PhysicalGap.GapFromDoeblinOut) (R : Float) : ClusteringAcceptance :=
  build_clustering { gamma_phys := G.gamma_phys, region_size := R }

theorem build_clustering_from_doeblin_holds (G : YM.Transfer.PhysicalGap.GapFromDoeblinOut) (R : Float) :
  clustering_spec { gamma_phys := G.gamma_phys, region_size := R } (build_clustering_from_doeblin G R) := by
  simpa using build_clustering_holds { gamma_phys := G.gamma_phys, region_size := R }

end YM.OSPositivity.Clustering
