/-!
Smoke checks for export variants (spec-level).
-/

import YM.Export.Variants
import YM.SpectralStability.RescaledNRC
import YM.Transfer.PhysicalGap
import YM.OSWilson.Doeblin

open YM.Export.Variants
open YM.SpectralStability.RescaledNRC
open YM.Transfer.PhysicalGap
open YM.OSWilson.Doeblin

namespace YM.Tests.Variants

-- Spectral variant
def rc := build_resolvent_comparison_rescaled (build_graph_defect_rescaled 0.2 1.0) (build_projection_control_lowE 1.0) (build_compact_calibrator 1.0)
def R := build_nrc_all_nonreal_rescaled rc
def VS := build_spectral_export R
#check spectral_export_spec R VS
theorem spec_ok : spectral_export_spec R VS := by
  simpa using build_spectral_export_holds R

-- Real variant
def G := build_gap_from_doeblin { kappa0 := 0.5, t0 := 1.0, lambda1 := 1.0, S0 := 0.1, a := 1.0 }
def VR := build_real_export G
#check real_export_spec G VR
theorem real_ok : real_export_spec G VR := by rfl

-- Interface variant
def I := build_wilson_gibbs_interface 2 1.0 1.0
def VI := build_interface_export I
#check interface_export_spec I VI
theorem iface_ok : interface_export_spec I VI := by rfl

end YM.Tests.Variants
