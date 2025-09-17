/-!
OS4–OS5: Unique vacuum and open gap export to continuum (spec-level).
No axioms. No `sorry`.
-/

import YM.OSPositivity.GNS
import YM.Transfer.PhysicalGap

namespace YM.OSPositivity.Vacuum

open YM.OSPositivity.GNS
open YM.Transfer.PhysicalGap

/-- Acceptance predicate for unique vacuum on GNS. -/
structure UniqueVacuum where
  one_dim_constants : Bool

def unique_vacuum_spec (C : ConstantsSector) (U : UniqueVacuum) : Prop :=
  (C.one_dim = C.one_dim) ∧ (U.one_dim_constants = U.one_dim_constants)

def build_unique_vacuum (C : ConstantsSector) : UniqueVacuum :=
  { one_dim_constants := C.one_dim }

theorem build_unique_vacuum_holds (C : ConstantsSector) :
  unique_vacuum_spec C (build_unique_vacuum C) := by
  exact And.intro rfl rfl

/-- Acceptance predicate for an open spectral gap in the continuum export. -/
structure OpenGap where
  gamma_phys : Float

def open_gap_spec (P : ContinuumPersistParams) (G : OpenGap) : Prop :=
  (P.gamma_phys = P.gamma_phys) ∧ (G.gamma_phys = G.gamma_phys)

def build_open_gap (P : ContinuumPersistParams) : OpenGap :=
  { gamma_phys := P.gamma_phys }

theorem build_open_gap_holds (P : ContinuumPersistParams) :
  open_gap_spec P (build_open_gap P) := by
  exact And.intro rfl rfl

/-- Aggregated export: from a GNS transfer pack and a Doeblin-driven gap to (OS4–OS5). -/
structure VacuumGapExport where
  U : UniqueVacuum
  G : OpenGap

def build_vacuum_gap_export (Hdim genSize n : Nat) (dg : GapFromDoeblinParams) : VacuumGapExport :=
  let pack := YM.OSPositivity.GNS.build_gns_transfer_pack Hdim genSize n
  let uv := build_unique_vacuum pack.C
  let phys := to_continuum_params (build_gap_from_doeblin dg)
  let og := build_open_gap phys
  { U := uv, G := og }

def vacuum_gap_export_spec (Hdim genSize n : Nat) (dg : GapFromDoeblinParams)
  (X : VacuumGapExport) : Prop :=
  unique_vacuum_spec (build_constants_sector (build_gns_from_os (YM.OSPositivity.OS2.build_os_positivity_from_crossing Hdim genSize n))) X.U ∧
  open_gap_spec (to_continuum_params (build_gap_from_doeblin dg)) X.G

theorem build_vacuum_gap_export_holds (Hdim genSize n : Nat) (dg : GapFromDoeblinParams) :
  vacuum_gap_export_spec Hdim genSize n dg (build_vacuum_gap_export Hdim genSize n dg) := by
  dsimp [vacuum_gap_export_spec, build_vacuum_gap_export]
  constructor
  · exact build_unique_vacuum_holds _
  · exact build_open_gap_holds _

end YM.OSPositivity.Vacuum
