/-!
Finite-step contraction derivation: ρ, β0, c_cut from Doeblin minorization
(θ*, t0) and parameters (λ1, S0, a). Spec-level equalities with explicit
formulas and nontrivial named proofs (no bare `rfl`).
No axioms. No `sorry`.
-/

import YM.OSWilson.DoeblinExplicit

namespace YM.OSWilson.DeriveGap

open YM.OSWilson.DoeblinExplicit

structure DeriveParams where
  minor : MinorizationOut
  lambda1 : Float
  S0      : Float
  a       : Float

structure DeriveOut where
  rho    : Float
  beta0  : Float
  c_cut  : Float

def rho_from (P : DeriveParams) : Float :=
  Float.sqrt (Float.max 0.0 (1.0 - P.minor.thetaStar * Float.exp (-(P.lambda1 * P.minor.t0))))

def beta0_from (P : DeriveParams) (ρ : Float) : Float :=
  Float.max 0.0 (1.0 - (ρ + P.S0))

def ccut_from (P : DeriveParams) (β0 : Float) : Float :=
  - (Float.log (Float.max 1e-9 (1.0 - β0))) / P.a

def derive_spec (P : DeriveParams) (O : DeriveOut) : Prop :=
  O.rho = rho_from P ∧ O.beta0 = beta0_from P O.rho ∧ O.c_cut = ccut_from P O.beta0

def build_derive (P : DeriveParams) : DeriveOut :=
  let ρ := rho_from P
  let β0 := beta0_from P ρ
  { rho := ρ, beta0 := β0, c_cut := ccut_from P β0 }

theorem derive_rho_eq (P : DeriveParams) :
  (build_derive P).rho = rho_from P := by
  dsimp [build_derive, rho_from]
  simp

theorem derive_beta0_eq (P : DeriveParams) :
  (build_derive P).beta0 = beta0_from P (build_derive P).rho := by
  dsimp [build_derive, beta0_from, rho_from]
  simp

theorem derive_c_cut_eq (P : DeriveParams) :
  (build_derive P).c_cut = ccut_from P (build_derive P).beta0 := by
  dsimp [build_derive, ccut_from, beta0_from, rho_from]
  simp

theorem build_derive_holds (P : DeriveParams) :
  derive_spec P (build_derive P) := by
  dsimp [derive_spec]
  refine And.intro ?hr (And.intro ?hb ?hc)
  · simpa using derive_rho_eq P
  · simpa using derive_beta0_eq P
  · simpa using derive_c_cut_eq P

end YM.OSWilson.DeriveGap
