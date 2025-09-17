/-!
Smoke checks for embeddings I_ε OS-isometry (spec-level).
-/

import YM.SpectralStability.RescaledNRC

open YM.SpectralStability.RescaledNRC

namespace YM.Tests.RescaledNRC

def P : EmbeddingParams := { a := 0.5, dim := 4 }
def W := build_embedding_isometry P

#check construct_embeddings_Ieps_lattice_to_continuum P W

theorem emb_isometry_ok : construct_embeddings_Ieps_lattice_to_continuum P W := by
  simpa using construct_embeddings_Ieps_lattice_to_continuum_holds P

-- Graph-defect O(a) and compact calibrator
def gd := build_graph_defect_rescaled 0.25 2.0
def cc := build_compact_calibrator 1.0
#check graph_defect_Oa_compact_calibrators gd cc
theorem gd_cal_ok : graph_defect_Oa_compact_calibrators gd cc := by
  simpa [gd, cc] using graph_defect_Oa_compact_calibrators_holds 0.25 2.0 1.0

-- Norm–resolvent convergence for all nonreal z alias
def rc := build_resolvent_comparison_rescaled gd (build_projection_control_lowE 2.0) cc
def Pnrc := build_nrc_all_nonreal_rescaled rc
#check nrc_all_nonreal_rescaled Pnrc
theorem nrc_ok : nrc_all_nonreal_rescaled Pnrc := by
  simpa using build_nrc_all_nonreal_rescaled_satisfies rc

end YM.Tests.RescaledNRC
