/-!
T11 (YM_OddConeDeficit) stubs.
Source: RS_Classical_Bridge_Source.txt (T11 block).
No axioms. No `sorry`.
-/

namespace YM.OSWilson.OddConeDeficit

/-! Parameter containers for typed specs (no imports, no proofs). -/

structure OSGramParams where
  R_star : Float
  a0 : Float
  N : Nat

structure OSGramWitness where
  A : Float
  mu : Float
  C_g : Float
  nu : Float

def os_gram_local_spec (P : OSGramParams) (W : OSGramWitness) : Prop := True

structure MixedGramParams where
  R_star : Float
  a0 : Float
  N : Nat

structure MixedGramOut where
  B : Float
  nu_prime : Float
  S0 : Float

def mixed_gram_decay_spec (P : MixedGramParams) (O : MixedGramOut) : Prop := True

structure DiagMixedParams where
  kappa0 : Float
  t0 : Float
  lambda1 : Float

structure DiagMixedOut where
  rho : Float

def diag_mixed_contr_from_doeblin_spec (P : DiagMixedParams) (O : DiagMixedOut) : Prop := True

structure GershgorinParams where
  rho : Float
  S0 : Float

structure GershgorinOut where
  beta0 : Float

def gershgorin_row_bound_spec (P : GershgorinParams) (O : GershgorinOut) : Prop := True

structure TickPoincareParams where
  beta0 : Float
  a : Float

structure TickPoincareOut where
  c_cut : Float

def tick_poincare_local_spec (P : TickPoincareParams) (O : TickPoincareOut) : Prop := True

end YM.OSWilson.OddConeDeficit
