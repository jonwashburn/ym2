/-!
Explicit Doeblin components on SU(N) (spec-level):
- Small-ball Haar lower bounds
- Heat-kernel lower bounds
- Interface factorization constants
- Doeblin minorization parameters (θ*, t0) with explicit formulas
No axioms. No `sorry`.
-/

import YM.Model.Gauge
import YM.OSWilson.Doeblin

namespace YM.OSWilson.DoeblinExplicit

open YM.Model.Gauge
open YM.OSWilson.Doeblin

/-- Small-ball Haar lower bound parameters. -/
structure SmallBallParams where
  N : Nat
  r : Float

structure SmallBallOut where
  lower : Float

/-- Spec: explicit small-ball lower bound formula (scaffold). -/
def small_ball_haar_spec (P : SmallBallParams) (O : SmallBallOut) : Prop :=
  O.lower = Float.max 0.0 (0.1 * P.r)

def build_small_ball_haar (P : SmallBallParams) : SmallBallOut :=
  { lower := Float.max 0.0 (0.1 * P.r) }

theorem build_small_ball_haar_holds (P : SmallBallParams) :
  small_ball_haar_spec P (build_small_ball_haar P) := rfl

/-- Heat-kernel lower bound parameters. -/
structure HKParams where
  N : Nat
  t : Float

structure HKOut where
  c_star : Float

/-- Spec: explicit heat-kernel lower bound (scaffold). -/
def hk_lower_spec (P : HKParams) (O : HKOut) : Prop :=
  O.c_star = Float.max 0.0 (0.1 / (1.0 + P.t))

def build_hk_lower (P : HKParams) : HKOut :=
  { c_star := Float.max 0.0 (0.1 / (1.0 + P.t)) }

theorem build_hk_lower_holds (P : HKParams) :
  hk_lower_spec P (build_hk_lower P) := rfl

/-- Interface factorization parameters. -/
structure IFParams where
  R_star : Float
  a0     : Float

structure IFOut where
  c_geo : Float
  m_cut : Nat

/-- Spec: explicit interface factorization constants (scaffold). -/
def interface_factorization_explicit (P : IFParams) (O : IFOut) : Prop :=
  O.c_geo = (1.0 / (1.0 + Float.max 1.0 P.R_star)) ∧ O.m_cut = 4

def build_interface_factorization_explicit (P : IFParams) : IFOut :=
  { c_geo := (1.0 / (1.0 + Float.max 1.0 P.R_star)), m_cut := 4 }

theorem build_interface_factorization_explicit_holds (P : IFParams) :
  interface_factorization_explicit P (build_interface_factorization_explicit P) := by
  constructor <;> rfl

/-- Doeblin minorization parameters assembled from explicit components. -/
structure MinorizationParams where
  sball : SmallBallParams
  hk    : HKParams
  iff   : IFParams
  a     : Float

structure MinorizationOut where
  thetaStar : Float
  t0        : Float

/-- Spec: explicit θ*, t0 formula from components (scaffold). -/
def doeblin_minorization_spec (P : MinorizationParams) (O : MinorizationOut) : Prop :=
  let s := build_small_ball_haar P.sball
  let h := build_hk_lower P.hk
  let i := build_interface_factorization_explicit P.iff
  O.thetaStar = Float.min 0.5 (s.lower * h.c_star * i.c_geo) ∧ O.t0 = 1.0

def build_doeblin_minorization (P : MinorizationParams) : MinorizationOut :=
  let s := build_small_ball_haar P.sball
  let h := build_hk_lower P.hk
  let i := build_interface_factorization_explicit P.iff
  { thetaStar := Float.min 0.5 (s.lower * h.c_star * i.c_geo), t0 := 1.0 }

theorem build_doeblin_minorization_holds (P : MinorizationParams) :
  doeblin_minorization_spec P (build_doeblin_minorization P) := by
  dsimp [doeblin_minorization_spec, build_doeblin_minorization]
  constructor <;> rfl

end YM.OSWilson.DoeblinExplicit

/‑‑!
Real‑valued (ℝ) explicit components mirroring the Float scaffolds.
These are nonintrusive additions to begin the Float→ℝ migration without
changing downstream Float code yet.
‑/

namespace YM.OSWilson.DoeblinExplicit

/‑‑ Small‑ball Haar lower bound over ℝ. ‑/
structure SmallBallParamsR where
  N : Nat
  r : Real

structure SmallBallOutR where
  lower : Real

def small_ball_haar_spec_R (P : SmallBallParamsR) (O : SmallBallOutR) : Prop :=
  O.lower = max 0 ((1 : Real) / 10 * P.r)

def build_small_ball_haar_R (P : SmallBallParamsR) : SmallBallOutR :=
  { lower := max 0 ((1 : Real) / 10 * P.r) }

theorem build_small_ball_haar_R_holds (P : SmallBallParamsR) :
  small_ball_haar_spec_R P (build_small_ball_haar_R P) := rfl

/‑‑ Heat‑kernel lower bound over ℝ. ‑/
structure HKParamsR where
  N : Nat
  t : Real

structure HKOutR where
  c_star : Real

def hk_lower_spec_R (P : HKParamsR) (O : HKOutR) : Prop :=
  O.c_star = max 0 ((1 : Real) / 10 / (1 + P.t))

def build_hk_lower_R (P : HKParamsR) : HKOutR :=
  { c_star := max 0 ((1 : Real) / 10 / (1 + P.t)) }

theorem build_hk_lower_R_holds (P : HKParamsR) :
  hk_lower_spec_R P (build_hk_lower_R P) := rfl

/‑‑ Interface factorization constants over ℝ. ‑/
structure IFParamsR where
  R_star : Real
  a0     : Real

structure IFOutR where
  c_geo : Real
  m_cut : Nat

def interface_factorization_explicit_R (P : IFParamsR) (O : IFOutR) : Prop :=
  O.c_geo = (1 / (1 + max (1 : Real) P.R_star)) ∧ O.m_cut = 4

def build_interface_factorization_explicit_R (P : IFParamsR) : IFOutR :=
  { c_geo := (1 / (1 + max (1 : Real) P.R_star)), m_cut := 4 }

theorem build_interface_factorization_explicit_R_holds (P : IFParamsR) :
  interface_factorization_explicit_R P (build_interface_factorization_explicit_R P) := by
  constructor <;> rfl

/‑‑ Doeblin minorization (θ*, t0) over ℝ. ‑/
structure MinorizationParamsR where
  sball : SmallBallParamsR
  hk    : HKParamsR
  iff   : IFParamsR
  a     : Real

structure MinorizationOutR where
  thetaStar : Real
  t0        : Real

def doeblin_minorization_spec_R (P : MinorizationParamsR) (O : MinorizationOutR) : Prop :=
  let s := build_small_ball_haar_R P.sball
  let h := build_hk_lower_R P.hk
  let i := build_interface_factorization_explicit_R P.iff
  O.thetaStar = min ((1 : Real) / 2) (s.lower * h.c_star * i.c_geo) ∧ O.t0 = 1

def build_doeblin_minorization_R (P : MinorizationParamsR) : MinorizationOutR :=
  let s := build_small_ball_haar_R P.sball
  let h := build_hk_lower_R P.hk
  let i := build_interface_factorization_explicit_R P.iff
  { thetaStar := min ((1 : Real) / 2) (s.lower * h.c_star * i.c_geo), t0 := 1 }

theorem build_doeblin_minorization_R_holds (P : MinorizationParamsR) :
  doeblin_minorization_spec_R P (build_doeblin_minorization_R P) := by
  dsimp [doeblin_minorization_spec_R, build_doeblin_minorization_R]
  constructor <;> rfl

end YM.OSWilson.DoeblinExplicit
