/-!
NoAlias guide (spec-level): prefer underlying acceptance symbols over aliases.
This file enumerates the canonical entry points to discourage alias usage.
-/

namespace YM.Docs.NoAlias

/-- NRC: use `nrc_all_nonreal_rescaled` (not only the alias wrappers). -/
def NRC_doc : Bool := true

/-- Doeblin/γ_cut: use `build_cut_export`/`export_from_interface` for values. -/
def Cut_doc : Bool := true

/-- Transfer selections: use `best_of_two`/`export_gamma_from_routes`. -/
def Transfer_doc : Bool := true

end YM.Docs.NoAlias
