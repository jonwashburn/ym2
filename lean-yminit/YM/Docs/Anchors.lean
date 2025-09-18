/-!
# TeX anchors ↔ Lean lemmas (acceptance map)

This file provides a lightweight map from key TeX anchors in
`Yang-Mills (25).tex` to the corresponding Lean acceptance lemmas or
specs. The intent is documentary: strengthen traceability by ensuring
each referenced anchor has a concrete Lean symbol that compiles.

We keep this purely as `#check` smoke checks with comments containing
the TeX labels, so the build fails if a mapped symbol disappears.
-/

import YM.OSPositivity.OS2
import YM.OSWilson.Crossing
import YM.OSWilson.Doeblin
import YM.OSWilson.OddConeDeficit
import YM.Transfer.PhysicalGap
import YM.SpectralStability.RescaledNRC
import YM.SpectralStability.Persistence
import YM.OSPositivity.Clustering
import YM.OSPositivity.Vacuum
import YM.OSPositivity.Euclid
import YM.OSPositivity.LocalFields
import YM.Export.Variants
import YM.Clay.Final

namespace YM.Docs.Anchors

open YM.OSPositivity.OS2
open YM.OSWilson.Crossing
open YM.OSWilson.Doeblin
open YM.OSWilson.OddConeDeficit
open YM.Transfer.PhysicalGap
open YM.SpectralStability.RescaledNRC
open YM.SpectralStability.Persistence
open YM.OSPositivity.Clustering
open YM.OSPositivity.Vacuum
open YM.OSPositivity.Euclid
open YM.OSPositivity.LocalFields
open YM.Export.Variants
open YM.Clay.Final

/-! ## OS positivity and transfer (TeX: thm:os)
Lean: `build_os_positivity_from_crossing_holds` and transfer/sector in GNS.
-/
-- TeX \ref{thm:os}
#check build_os_positivity_from_crossing_holds

/-! ## Crossing Gram PSD (TeX: prop:psd-crossing-gram)
Lean: `reflected_psd_gram_holds`.
-/
-- TeX \ref{prop:psd-crossing-gram}
#check reflected_psd_gram_holds

/-! ## Doeblin: explicit constants and domination (TeX: prop:explicit-doeblin-constants, prop:doeblin-full)
Lean: `build_cut_export_satisfies`, `build_haar_domination_uniform_satisfies`.
-/
-- TeX \ref{prop:explicit-doeblin-constants}
#check build_cut_export_satisfies
-- TeX \ref{prop:doeblin-full}
#check build_haar_domination_uniform_satisfies

/-! ## Odd-cone contraction and Gershgorin (TeX: cor:odd-contraction-from-Kint, thm:uniform-odd-contraction)
Lean: `build_odd_cone_contraction_satisfies`, `build_gershgorin_row_bound_satisfies`.
-/
-- TeX \ref{cor:odd-contraction-from-Kint}
#check build_odd_cone_contraction_satisfies
-- TeX \ref{thm:uniform-odd-contraction}
#check build_gershgorin_row_bound_satisfies

/-! ## Eight-tick and gamma_cut export (TeX: cor:8tick-one-link, eq:per-bound)
Lean: `build_eight_tick_satisfies`, `gamma_cut_from_refresh_holds`.
-/
-- TeX \ref{cor:8tick-one-link}
#check build_eight_tick_satisfies
-- TeX \ref{eq:per-bound}
#check gamma_cut_from_refresh_holds

/-! ## NRC all nonreal (TeX: thm:NRC-allz)
Lean: `norm_resolvent_convergence_nonreal_z_holds`/`T10_accept_holds`.
-/
-- TeX \ref{thm:NRC-allz}
#check norm_resolvent_convergence_nonreal_z_holds
#check T10_accept_holds

/-! ## Gap persistence (TeX: thm:gap-persist)
Lean: `build_riesz_from_gap_holds`.
-/
-- TeX \ref{thm:gap-persist}
#check build_riesz_from_gap_holds

/-! ## Gap ⇒ clustering (TeX: thm:gap-to-clustering, prop:gap-to-cluster)
Lean: `build_clustering_holds`.
-/
-- TeX \ref{thm:gap-to-clustering}
-- TeX \ref{prop:gap-to-cluster}
#check build_clustering_holds

/-! ## OS4–OS5 unique vacuum and open gap (TeX: cor:poincare, thm:global-gap-uncond)
Lean: `build_vacuum_gap_export_holds`.
-/
-- TeX \ref{cor:poincare}
-- TeX \ref{thm:global-gap-uncond}
#check build_vacuum_gap_export_holds

/-! ## Euclidean invariance (OS1) (TeX: lem:isotropy-restoration, lem:eqc-modulus)
Lean: `euclid_aggregate_exists` and component specs.
-/
-- TeX \ref{lem:eqc-modulus}
#check euclid_aggregate_exists

/-! ## OS0 polynomial bounds, UEI (TeX: cor:uei-explicit-constants, prop:OS0-poly)
Lean: `uei_aggregate_exists`, `os0_from_moment_quant_holds`.
-/
-- TeX \ref{cor:uei-explicit-constants}
#check uei_aggregate_exists
-- TeX \ref{prop:OS0-poly}
#check os0_from_moment_quant_holds

/-! ## Export variants (spectral/real/interface) and Final (TeX: thm:global-OS, thm:wightman-axioms)
Lean: `build_spectral_export_holds`, `build_real_export_holds`, `build_interface_export_holds`, `build_final_holds`.
-/
-- TeX \ref{thm:global-OS}
-- TeX \ref{thm:wightman-axioms}
#check build_spectral_export_holds
#check build_real_export_holds
#check build_interface_export_holds
#check build_final_holds

end YM.Docs.Anchors
