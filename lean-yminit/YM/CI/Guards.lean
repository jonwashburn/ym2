/-!
CI Guards (spec-level): import and touch core acceptance symbols so build fails
if placeholders/paths are removed or renamed. No axioms. No `sorry`.
-/

import YM.OSPositivity.OS2
import YM.OSWilson.Doeblin
import YM.Transfer.PhysicalGap
import YM.SpectralStability.RescaledNRC
import YM.OSPositivity.GNS
import YM.OSPositivity.Clustering
import YM.OSPositivity.Wightman

namespace YM.CI.Guards

open YM.OSPositivity.OS2
open YM.OSWilson.Doeblin
open YM.Transfer.PhysicalGap
open YM.SpectralStability.RescaledNRC
open YM.OSPositivity.GNS
open YM.OSPositivity.Clustering
open YM.OSPositivity.Wightman

/-- Guard: OS2 canonical acceptance is present and usable. -/
def guard_os2 : Prop :=
  let W := build_os_positivity_from_crossing 4 3 5
  os_positivity_spec W

/-- Guard: Doeblin domination alias reachable. -/
def guard_doeblin_dom : Prop :=
  doeblin_domination_accept (build_haar_domination_uniform 2)

/-- Guard: γ_cut exports exist (refresh/interface). -/
def guard_gamma_exports : Prop :=
  let I := build_wilson_gibbs_interface 2 1.0 1.0
  gamma_cut_from_refresh 1.0 0.5 1.0 1.0 = (build_cut_export 1.0 0.5 1.0 1.0).gamma_c ∧
  gamma_cut_from_interface I = (export_from_interface I).gamma_c

/-- Guard: embeddings I_ε and NRC norm–resolvent aliases. -/
def guard_nrc : Prop :=
  let P := { a := 0.5, dim := 4 }
  let W := build_embedding_isometry P
  construct_embeddings_Ieps_lattice_to_continuum P W ∧
  let rc := build_resolvent_comparison_rescaled (build_graph_defect_rescaled 0.2 1.0) (build_projection_control_lowE 1.0) (build_compact_calibrator 1.0)
  nrc_all_nonreal_rescaled (build_nrc_all_nonreal_rescaled rc)

/-- Guard: GNS/transfer/sector builders are reachable. -/
def guard_gns : Bool :=
  let pack := YM.OSPositivity.GNS.build_gns_transfer_pack 4 3 5; True

/-- Guard: clustering builder from Doeblin-driven gap. -/
def guard_clustering : Prop :=
  let G := build_gap_from_doeblin { kappa0 := 0.5, t0 := 1.0, lambda1 := 1.0, S0 := 0.1, a := 1.0 }
  clustering_spec { gamma_phys := G.gamma_phys, region_size := 1.0 } (build_clustering_from_doeblin G 1.0)

/-- Guard: OS→Wightman acceptance available (canonical spec). -/
def guard_wightman : Prop :=
  let S : SchwingerAcceptance := { os0_ok := true, os1_ok := true, os2_ok := true }
  os_to_wightman_reconstruction_spec S (build_os_to_wightman_reconstruction S)

end YM.CI.Guards
