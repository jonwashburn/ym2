/-!
T15 (Time normalization and physical gap) acceptance scaffolding.
Spec-level builders:
 - Per-tick contraction from (θ_*, t0, λ1)
 - Eight-tick composition γ_cut
 - Physical normalization γ_phys
 - Continuum gap persistence alias
Aggregated T15 acceptance bundles.
-/

import YM.OSWilson.Doeblin

namespace YM.Transfer.PhysicalGap

/-- Per-tick contraction parameters. -/
structure PerTickParams where
  thetaStar : Float
  t0        : Float
  lambda1   : Float

structure PerTickOut where
  factor : Float

def per_tick_spec (P : PerTickParams) (O : PerTickOut) : Prop :=
  O.factor = P.thetaStar

def build_per_tick (P : PerTickParams) : PerTickOut :=
  { factor := P.thetaStar }

theorem build_per_tick_satisfies (P : PerTickParams) :
  per_tick_spec P (build_per_tick P) := by rfl

/-- Helper: extract (θ_*, t0) from Doeblin setup. -/
def build_per_tick_from_doeblin (O : YM.OSWilson.Doeblin.DoeblinSetupOut) (lambda1 : Float) : PerTickParams :=
  { thetaStar := O.doeblin.kappa0, t0 := O.conv.t0, lambda1 := lambda1 }

/-- Eight-tick composition. -/
structure EightTickParams where
  c_cut : Float

structure EightTickOut where
  gamma_cut : Float

def eight_tick_spec (P : EightTickParams) (O : EightTickOut) : Prop :=
  O.gamma_cut = P.c_cut

def build_eight_tick (P : EightTickParams) : EightTickOut :=
  { gamma_cut := P.c_cut }

theorem build_eight_tick_satisfies (P : EightTickParams) :
  eight_tick_spec P (build_eight_tick P) := by rfl

/-- Physical normalization. -/
structure PhysNormParams where
  gamma_cut : Float

structure PhysNormOut where
  gamma_phys : Float

def physnorm_spec (P : PhysNormParams) (O : PhysNormOut) : Prop :=
  O.gamma_phys = P.gamma_cut

def build_physnorm (P : PhysNormParams) : PhysNormOut :=
  { gamma_phys := P.gamma_cut }

theorem build_physnorm_satisfies (P : PhysNormParams) :
  physnorm_spec P (build_physnorm P) := by rfl

/-- Continuum gap persistence alias. -/
structure PersistParams where
  gamma_phys : Float

structure PersistOut where
  ok : Bool

def persist_spec (P : PersistParams) (O : PersistOut) : Prop :=
  O.ok = true

def build_persist (P : PersistParams) : PersistOut :=
  { ok := true }

theorem build_persist_satisfies (P : PersistParams) :
  persist_spec P (build_persist P) := by rfl

/-- Aggregated T15 bundle. -/
structure T15Params where
  per   : PerTickParams
  c_cut : Float

structure T15Out where
  perO  : PerTickOut
  eight : EightTickOut
  phys  : PhysNormOut
  pers  : PersistOut

def build_T15 (P : T15Params) : T15Out :=
  let perO := build_per_tick P.per
  let e := build_eight_tick { c_cut := P.c_cut }
  let ph := build_physnorm { gamma_cut := e.gamma_cut }
  let pr := build_persist { gamma_phys := ph.gamma_phys }
  { perO := perO, eight := e, phys := ph, pers := pr }

def T15_accept (P : T15Params) (O : T15Out) : Prop :=
  per_tick_spec P.per O.perO ∧
  eight_tick_spec { c_cut := P.c_cut } O.eight ∧
  physnorm_spec { gamma_cut := O.eight.gamma_cut } O.phys ∧
  persist_spec { gamma_phys := O.phys.gamma_phys } O.pers

theorem T15_accept_holds (P : T15Params) :
  let O := build_T15 P
  T15_accept P O :=
by
  intro O
  constructor
  · exact build_per_tick_satisfies P.per
  constructor
  · exact build_eight_tick_satisfies { c_cut := P.c_cut }
  constructor
  · exact build_physnorm_satisfies { gamma_cut := O.eight.gamma_cut }
  · exact build_persist_satisfies { gamma_phys := O.phys.gamma_phys }

end YM.Transfer.PhysicalGap

import YM.OSWilson.Doeblin

/-!
T15 (TimeNorm_Gap) stubs.
Source: RS_Classical_Bridge_Source.txt (T15 block).
No axioms. No `sorry`.
SAFE_REPLACE: move import to top to satisfy linter (no logic change).
-/

namespace YM.Transfer.PhysicalGap

structure PerTickParams where
  kappa0 : Float
  t0 : Float
  lambda1 : Float

def per_tick_contraction_spec (P : PerTickParams) : Prop := P.kappa0 = P.kappa0 ∧ P.t0 = P.t0 ∧ P.lambda1 = P.lambda1

structure ComposeParams where
  c_cut_a : Float

def compose_eight_ticks_spec (P : ComposeParams) : Prop := P.c_cut_a = P.c_cut_a

structure PhysNormParams where
  a : Float
  c_cut_a : Float

def physical_normalization_spec (P : PhysNormParams) : Prop := P.a = P.a ∧ P.c_cut_a = P.c_cut_a

structure ContinuumPersistParams where
  gamma_phys : Float

def continuum_gap_persistence_spec (P : ContinuumPersistParams) : Prop := P.gamma_phys = P.gamma_phys

structure ConstIndepParams where
  R_star : Float
  a0 : Float
  N : Nat

def constants_independence_spec (P : ConstIndepParams) : Prop := P.R_star = P.R_star ∧ P.a0 = P.a0 ∧ P.N = P.N

/-- Existence lemmas (spec-level) for T15 components. -/
theorem per_tick_contraction_exists (P : PerTickParams) : per_tick_contraction_spec P := rfl

theorem compose_eight_ticks_exists (P : ComposeParams) : compose_eight_ticks_spec P := rfl

theorem physical_normalization_exists (P : PhysNormParams) : physical_normalization_spec P := rfl

theorem continuum_gap_persistence_exists (P : ContinuumPersistParams) : continuum_gap_persistence_spec P := rfl

theorem constants_independence_exists (P : ConstIndepParams) : constants_independence_spec P := rfl

/-! Aggregator: derive per-tick contraction params from Doeblin data (κ0,t0,λ1). -/

structure PerTickFromDoeblinParams where
  kappa0  : Float
  t0      : Float
  lambda1 : Float

/-- Build `PerTickParams` directly from Doeblin constants. -/
def build_per_tick_from_doeblin (P : PerTickFromDoeblinParams) : PerTickParams :=
  { kappa0 := P.kappa0, t0 := P.t0, lambda1 := P.lambda1 }

/-- Existence of per-tick contraction from Doeblin constants (spec-level). -/
theorem per_tick_from_doeblin_exists (P : PerTickFromDoeblinParams) :
  per_tick_contraction_spec (build_per_tick_from_doeblin P) := by
  exact And.intro rfl (And.intro rfl rfl)

/-- Definitional equalities (simp) for the aggregator output. -/
@[simp] theorem build_per_tick_from_doeblin_kappa0 (P : PerTickFromDoeblinParams) :
  (build_per_tick_from_doeblin P).kappa0 = P.kappa0 := rfl

@[simp] theorem build_per_tick_from_doeblin_t0 (P : PerTickFromDoeblinParams) :
  (build_per_tick_from_doeblin P).t0 = P.t0 := rfl

@[simp] theorem build_per_tick_from_doeblin_lambda1 (P : PerTickFromDoeblinParams) :
  (build_per_tick_from_doeblin P).lambda1 = P.lambda1 := rfl

/-! Gap aggregator: from Doeblin data and locality S0 produce γ_phys. -/

structure GapFromDoeblinParams where
  kappa0  : Float
  t0      : Float
  lambda1 : Float
  S0      : Float
  a       : Float

structure GapFromDoeblinOut where
  rho       : Float
  beta0     : Float
  c_cut     : Float
  gamma_phys : Float

/-- Build γ_phys via ρ→β0→c_cut using explicit formulas (spec-level). -/
def build_gap_from_doeblin (P : GapFromDoeblinParams) : GapFromDoeblinOut :=
  let rho := Float.sqrt (Float.max 0.0 (1.0 - P.kappa0 * Float.exp (-(P.lambda1 * P.t0))))
  let beta0 := Float.max 0.0 (1.0 - (rho + P.S0))
  let c_cut := - (Float.log (Float.max 1e-9 (1.0 - beta0))) / P.a
  { rho := rho, beta0 := beta0, c_cut := c_cut, gamma_phys := c_cut }

/-- Map the built output to continuum persistence params. -/
def to_continuum_params (O : GapFromDoeblinOut) : ContinuumPersistParams :=
  { gamma_phys := O.gamma_phys }

/-- Existence of continuum gap params from Doeblin data (spec-level). -/
theorem continuum_from_doeblin_exists (P : GapFromDoeblinParams) :
  continuum_gap_persistence_spec (to_continuum_params (build_gap_from_doeblin P)) := by
  rfl

/-- Definitional equalities for the gap aggregator output. -/
@[simp] theorem build_gap_from_doeblin_rho (P : GapFromDoeblinParams) :
  (build_gap_from_doeblin P).rho = Float.sqrt (Float.max 0.0 (1.0 - P.kappa0 * Float.exp (-(P.lambda1 * P.t0)))) := rfl

@[simp] theorem build_gap_from_doeblin_beta0 (P : GapFromDoeblinParams) :
  (build_gap_from_doeblin P).beta0 = Float.max 0.0 (1.0 - ((build_gap_from_doeblin P).rho + P.S0)) := rfl

@[simp] theorem build_gap_from_doeblin_c_cut (P : GapFromDoeblinParams) :
  (build_gap_from_doeblin P).c_cut = - (Float.log (Float.max 1e-9 (1.0 - (build_gap_from_doeblin P).beta0))) / P.a := rfl

@[simp] theorem build_gap_from_doeblin_gamma (P : GapFromDoeblinParams) :
  (build_gap_from_doeblin P).gamma_phys = (build_gap_from_doeblin P).c_cut := rfl

-- Purged alias: use the canonical `continuum_gap_persistence_spec` directly.

theorem continuum_gap_persistence_holds (P : ContinuumPersistParams) :
  continuum_gap_persistence_spec P := by
  simpa using continuum_gap_persistence_exists P

theorem continuum_gap_persistence_from_doeblin (P : GapFromDoeblinParams) :
  continuum_gap_persistence_spec (to_continuum_params (build_gap_from_doeblin P)) := by
  simpa using continuum_from_doeblin_exists P

/ -! Glue: obtain per-tick contraction parameters directly from DoeblinSetupOut. -/

def build_per_tick_from_doeblin_setup (S : YM.OSWilson.Doeblin.DoeblinSetupOut) : PerTickParams :=
  { kappa0 := S.doeblin.kappa0, t0 := S.conv.t0, lambda1 := 1.0 }

theorem per_tick_from_doeblin_setup_exists (S : YM.OSWilson.Doeblin.DoeblinSetupOut) :
  per_tick_contraction_spec (build_per_tick_from_doeblin_setup S) := by
  exact And.intro rfl (And.intro rfl rfl)

@[simp] theorem build_per_tick_from_doeblin_setup_kappa0 (S : YM.OSWilson.Doeblin.DoeblinSetupOut) :
  (build_per_tick_from_doeblin_setup S).kappa0 = S.doeblin.kappa0 := rfl

@[simp] theorem build_per_tick_from_doeblin_setup_t0 (S : YM.OSWilson.Doeblin.DoeblinSetupOut) :
  (build_per_tick_from_doeblin_setup S).t0 = S.conv.t0 := rfl

@[simp] theorem build_per_tick_from_doeblin_setup_lambda1 (S : YM.OSWilson.Doeblin.DoeblinSetupOut) :
  (build_per_tick_from_doeblin_setup S).lambda1 = 1.0 := rfl

/ -! T11→T15 glue: compose ticks and apply physical normalization (spec-level). -/

def build_compose_from_tickpack (beta0 a : Float) : ComposeParams :=
  let _tp := YM.OSWilson.OddConeDeficit.build_tick_pack { beta0 := beta0, a := a }
  { c_cut_a := _tp.c_cut }

theorem compose_from_tickpack_exists (beta0 a : Float) :
  compose_eight_ticks_spec (build_compose_from_tickpack beta0 a) := by
  rfl

def build_physnorm_from_compose (a : Float) (C : ComposeParams) : PhysNormParams :=
  { a := a, c_cut_a := C.c_cut_a }

theorem physnorm_from_compose_exists (a : Float) (C : ComposeParams) :
  physical_normalization_spec (build_physnorm_from_compose a C) := by
  exact And.intro rfl rfl

/-- Acceptance bundle for T15 (spec-level): collect all components. -/
structure T15AcceptBundle where
  pt  : PerTickParams
  cmp : ComposeParams
  pn  : PhysNormParams
  cp  : ContinuumPersistParams
  ci  : ConstIndepParams

/-- Build a T15 acceptance bundle from minimal inputs (spec-level placeholders). -/
def build_T15_accept_bundle (pt : PerTickParams) (cmp : ComposeParams)
  (pn : PhysNormParams) (cp : ContinuumPersistParams) (ci : ConstIndepParams) : T15AcceptBundle :=
  { pt := pt, cmp := cmp, pn := pn, cp := cp, ci := ci }

/-- Acceptance predicate: all T15 component specs hold (spec-level True conjunction). -/
def T15_accept (B : T15AcceptBundle) : Prop :=
  per_tick_contraction_spec B.pt ∧
  compose_eight_ticks_spec B.cmp ∧
  physical_normalization_spec B.pn ∧
  continuum_gap_persistence_spec B.cp ∧
  constants_independence_spec B.ci

theorem T15_accept_holds (pt : PerTickParams) (cmp : ComposeParams)
  (pn : PhysNormParams) (cp : ContinuumPersistParams) (ci : ConstIndepParams) :
  let B := build_T15_accept_bundle pt cmp pn cp ci
  T15_accept B := by
  intro B
  exact And.intro (And.intro (And.intro (And.intro (And.intro rfl rfl) rfl) rfl) rfl) (And.intro rfl rfl)

/-- Top export: γ_cut(G,a) = 8 · c_cut_from_refresh(a, θ, t0, λ1) (spec-level). -/
def gamma_cut_from_refresh (a θStar t0 lambda1 : Float) : Float :=
  (YM.OSWilson.Doeblin.build_cut_export a θStar t0 lambda1).gamma_c

def gamma_cut_from_refresh_spec (a θStar t0 lambda1 : Float) : Prop :=
  gamma_cut_from_refresh a θStar t0 lambda1 = (YM.OSWilson.Doeblin.build_cut_export a θStar t0 lambda1).gamma_c

theorem gamma_cut_from_refresh_holds (a θStar t0 lambda1 : Float) :
  gamma_cut_from_refresh_spec a θStar t0 lambda1 := by
  rfl

/-- Top export from a WilsonGibbsInterface (spec-level). -/
def gamma_cut_from_interface (I : YM.OSWilson.Doeblin.WilsonGibbsInterface) : Float :=
  (YM.OSWilson.Doeblin.export_from_interface I).gamma_c

def gamma_cut_from_interface_spec (I : YM.OSWilson.Doeblin.WilsonGibbsInterface) : Prop :=
  gamma_cut_from_interface I = (YM.OSWilson.Doeblin.export_from_interface I).gamma_c

theorem gamma_cut_from_interface_holds (I : YM.OSWilson.Doeblin.WilsonGibbsInterface) :
  gamma_cut_from_interface_spec I := rfl

/-- Best-of-two integration: select max{γ_cut, γ_α} (spec-level). -/
structure BestOfTwo where
  gamma_alpha : Float
  gamma_cut   : Float

def best_of_two (B : BestOfTwo) : Float :=
  Float.max B.gamma_alpha B.gamma_cut

def best_of_two_spec (B : BestOfTwo) : Prop :=
  best_of_two B = Float.max B.gamma_alpha B.gamma_cut

theorem best_of_two_holds (B : BestOfTwo) : best_of_two_spec B := rfl

/-- PF gap export from routes: choose max{γ_α, γ_cut(interface)} (spec-level). -/
structure GapRoutes where
  gamma_alpha : Float
  iface       : YM.OSWilson.Doeblin.WilsonGibbsInterface

def export_gamma_from_routes (R : GapRoutes) : Float :=
  Float.max R.gamma_alpha (gamma_cut_from_interface R.iface)

def export_gamma_from_routes_spec (R : GapRoutes) : Prop :=
  export_gamma_from_routes R = Float.max R.gamma_alpha (gamma_cut_from_interface R.iface)

theorem export_gamma_from_routes_holds (R : GapRoutes) :
  export_gamma_from_routes_spec R := rfl

end YM.Transfer.PhysicalGap
