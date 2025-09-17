/-!
Smoke checks for OS0 UEI/LSI and moment bounds (spec-level).
-/

import YM.OSPositivity.UEI

open YM.OSPositivity.UEI

namespace YM.Tests.UEI

def A : UEIAggregateParams :=
  { region_size := 1.0, a0 := 1.0, N := 3, beta_min := 0.1, mean_bound := 10.0 }

def O := build_uei_aggregate A

#check uei_aggregate_exists A

theorem uei_ok :
  ∃ O : UEIAggregateOut,
    tree_gauge_local_spec { region_size := A.region_size, a0 := A.a0, N := A.N } (build_tree_gauge_local { region_size := A.region_size, a0 := A.a0, N := A.N }) ∧
    local_lsi_beta_spec { beta_min := A.beta_min, region_size := A.region_size, N := A.N } (build_local_lsi_beta { beta_min := A.beta_min, region_size := A.region_size, N := A.N }) ∧
    lipschitz_S_R_spec { a0 := A.a0, region_size := A.region_size, N := A.N } (build_lipschitz_S_R { a0 := A.a0, region_size := A.region_size, N := A.N }) ∧
    herbst_eta_spec { rho_R := (build_local_lsi_beta { beta_min := A.beta_min, region_size := A.region_size, N := A.N }).rho_R, G_R := (build_lipschitz_S_R { a0 := A.a0, region_size := A.region_size, N := A.N }).G_R } (build_herbst_eta { rho_R := (build_local_lsi_beta { beta_min := A.beta_min, region_size := A.region_size, N := A.N }).rho_R, G_R := (build_lipschitz_S_R { a0 := A.a0, region_size := A.region_size, N := A.N }).G_R }) ∧
    uei_fixed_region_spec { eta_R := (build_herbst_eta { rho_R := (build_local_lsi_beta { beta_min := A.beta_min, region_size := A.region_size, N := A.N }).rho_R, G_R := (build_lipschitz_S_R { a0 := A.a0, region_size := A.region_size, N := A.N }).G_R }).eta_R, mean_bound := A.mean_bound } (build_uei_fixed_region { eta_R := (build_herbst_eta { rho_R := (build_local_lsi_beta { beta_min := A.beta_min, region_size := A.region_size, N := A.N }).rho_R, G_R := (build_lipschitz_S_R { a0 := A.a0, region_size := A.region_size, N := A.N }).G_R }).eta_R, mean_bound := A.mean_bound }) := by
  simpa using uei_aggregate_exists A

end YM.Tests.UEI
