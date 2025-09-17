import ym.Main

/-!
Quick verification checks (build-time smoke tests).
- No logic changes here; these help ensure the pipeline names are resolvable
  and core theorems have no axioms.
-/

#check YM.unconditional_mass_gap

#print axioms YM.unconditional_mass_gap

-- If spectral exports are in scope, uncomment these checks when wired:
-- #check YM.continuum_mass_gap_spectral_export
-- #print axioms YM.continuum_mass_gap_spectral_export


