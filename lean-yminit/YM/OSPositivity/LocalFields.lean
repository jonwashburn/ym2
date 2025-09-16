/-!
T14 (LocalFields) stubs.
Source: RS_Classical_Bridge_Source.txt (T14 block).
No axioms. No `sorry`.
-/

namespace YM.OSPositivity.LocalFields

structure CloverParams where
  test_support : Float

def clover_net_spec (P : CloverParams) : Prop := True

structure OS0Params where
  poly_bound : Float

def os0_transfer_spec (P : OS0Params) : Prop := True

structure OS2Params where
  cylinder_ok : Bool

def os2_transfer_spec (P : OS2Params) : Prop := True

structure LocalityParams where
  sep : Float

def locality_fields_spec (P : LocalityParams) : Prop := True

structure GapPersistParams where
  gamma_phys : Float

def gap_persistence_fields_spec (P : GapPersistParams) : Prop := True

end YM.OSPositivity.LocalFields
