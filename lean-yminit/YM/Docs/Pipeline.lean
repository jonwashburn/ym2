/-!
Pipeline API overview (spec-level documentation module).

This module documents, in code-local comments, the entry points used across
the OS2, Doeblin, strong-coupling, and persistence tracks. It introduces
lightweight symbols so the file participates in builds while carrying the
API map for navigation.
-/

namespace YM.Docs.Pipeline

/-- OS2: reflection positivity export from crossing.
Entry: `YM.OSPositivity.OS2.build_os_positivity_from_crossing`
Spec:  `YM.OSPositivity.OS2.os_positivity_spec` -/
def OS2_doc : Bool := true

/-- Doeblin/interface track.
Kernels: `YM.OSWilson.Doeblin.InterSlabKernel`, `build_inter_slab_wilson`
Domination: `YM.OSWilson.Doeblin.haar_domination_spec`
Exports: `YM.OSWilson.Doeblin.export_from_interface` (→ `(c_cut, γ_cut)`) -/
def Doeblin_doc : Bool := true

/-- Strong-coupling (small-β) track.
Influence: `YM.OSWilson.Cluster.influence_bound_spec`
Cluster:   `YM.OSWilson.Cluster.cluster_expansion_spec`
Gap:       `YM.OSWilson.Cluster.pf_gap_from_dobrushin_spec` -/
def StrongCoupling_doc : Bool := true

/-- Best-of-two selector and top gap exports.
Selector: `YM.Transfer.PhysicalGap.best_of_two`
Routes:   `YM.Transfer.PhysicalGap.export_gamma_from_routes` -/
def Exports_doc : Bool := true

/-- GNS/transfer and constants sector.
GNS:   `YM.OSPositivity.GNS.build_gns_from_os`, `gns_from_os_spec`
Trans: `YM.OSPositivity.GNS.build_transfer_on_gns`, `transfer_spec`
Cons.: `YM.OSPositivity.GNS.build_constants_sector`, `constants_sector_spec` -/
def GNS_doc : Bool := true

/-- Persistence and NRC.
Embeddings: `YM.SpectralStability.RescaledNRC.construct_embeddings_Ieps_lattice_to_continuum`
NRC:        `YM.SpectralStability.RescaledNRC.nrc_all_nonreal_rescaled`
Riesz:      `YM.SpectralStability.Persistence.riesz_semicontinuity_spec` -/
def Persistence_doc : Bool := true

/-- Universality.
Cross-reg: `YM.SpectralStability.Universality.cross_regularization_spec`
Equal-gap: `YM.SpectralStability.Universality.gap_universality_spec` -/
def Universality_doc : Bool := true

end YM.Docs.Pipeline
