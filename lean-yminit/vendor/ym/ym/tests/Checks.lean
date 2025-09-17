import ym.Main

/-!
Quick verification checks (build-time smoke tests).
- No logic changes here; these help ensure the pipeline names are resolvable
  and core theorems have no axioms.
-/

#check YM.unconditional_mass_gap

#print axioms YM.unconditional_mass_gap

#check YM.unconditional_mass_gap_spectral_export_if_real_pf
#print axioms YM.unconditional_mass_gap_spectral_export_if_real_pf

#check YM.YMMeasure.continuum_ym_from_projective
#check YM.Minkowski.wightman_export_wilson

-- Additional acceptance link checks
#check YM.Transfer.PhysicalGap.T15_accept
#check YM.OSWilson.OddConeDeficit.T11_accept
