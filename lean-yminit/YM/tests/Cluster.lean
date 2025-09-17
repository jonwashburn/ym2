/-!
Smoke checks for small-β character/cluster expansion (spec-level).
-/

import YM.OSWilson.Cluster

open YM.OSWilson.Cluster

namespace YM.Tests.Cluster

def P : SmallBeta := { β := 0.01, β_small := true }
def B : InfluenceBound := build_influence_bound P
def C : ClusterAcceptance := build_cluster_expansion P

#check influence_bound_spec P B
#check cluster_expansion_spec P C

theorem infl_ok : influence_bound_spec P B := by
  simpa using build_influence_bound_holds P

theorem clus_ok : cluster_expansion_spec P C := by
  simpa using build_cluster_expansion_holds P

-- Influence bound alias and PF gap from Dobrushin
#check influence_bound_alpha_le_2beta_Jperp P B
theorem infl_alias_ok : influence_bound_alpha_le_2beta_Jperp P B := by
  simpa using influence_bound_alpha_le_2beta_Jperp_holds P

def G := build_pf_gap_from_dobrushin B
#check pf_gap_from_dobrushin_spec B G
theorem pf_gap_ok : pf_gap_from_dobrushin_spec B G := by
  simpa using build_pf_gap_from_dobrushin_holds B

end YM.Tests.Cluster
