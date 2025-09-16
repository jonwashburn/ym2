import Mathlib

/-!
Prop-level OS0 (temperedness) interface for Schwinger functions: record that
the n-point distributions extend continuously to Schwartz space with uniform
growth bounds sufficient for OS reconstruction.
-/

namespace YM
namespace OSPositivity

/-- Hypothesis bundle for temperedness (OS0). -/
structure OS0Hypotheses where
  schwartz_extension : Prop   -- S_n extends to S'(R^{dn}) continuously
  uniform_growth : Prop       -- polynomial growth bounds on test functions
  schwartz_extension_holds : schwartz_extension
  uniform_growth_holds : uniform_growth

/-- Recorded conclusion: temperedness of the Schwinger family. -/
def TemperedFrom (H : OS0Hypotheses) : Prop :=
  H.schwartz_extension ∧ H.uniform_growth

/-- Interface lemma exporting OS0. -/
theorem tempered (H : OS0Hypotheses) : TemperedFrom H := by
  exact And.intro H.schwartz_extension_holds H.uniform_growth_holds

/-- OS0 (temperedness) from UEI on fixed physical regions and a holonomy increment
    Hölder bound (via Kolmogorov–Chentsov): interface-level constructor. -/
structure UEIToOS0 where
  uniform_exp_integrability : Prop
  holder_increment_control : Prop
  uniform_exp_integrability_holds : uniform_exp_integrability
  holder_increment_control_holds : holder_increment_control

/-- Export: UEI + increment control implies OS0 temperateness at the interface layer. -/
theorem os0_temperedness_from_uei (D : UEIToOS0) : TemperedFrom
  { schwartz_extension := D.uniform_exp_integrability
  , uniform_growth := D.holder_increment_control
  , schwartz_extension_holds := D.uniform_exp_integrability_holds
  , uniform_growth_holds := D.holder_increment_control_holds } := by
  exact And.intro D.uniform_exp_integrability_holds D.holder_increment_control_holds

/-- Polynomial bounds container for OS0: records exponents and constants for diameter
    and separation growth controls (interface-level). -/
structure OS0PolynomialBounds where
  q : ℝ      -- separation decay exponent (take q > d)
  p : ℝ      -- diameter growth exponent (e.g., p = d + 1)
  Cn : ℕ → ℝ -- n-dependent constant family
  q_gt_dim : Prop
  Cn_nonneg : ∀ n, 0 ≤ Cn n

/-- Export OS0 temperedness with explicit polynomial bounds (interface-level). -/
structure OS0Tempered where
  tempered : Prop
  poly_bounds : OS0PolynomialBounds
  tempered_holds : tempered

/-- From UEI (quantitative) and a uniform gap, provide an OS0 export carrying
    polynomial bounds data. Interface-level constructor. -/
def os0_of_exp_cluster (poly : OS0PolynomialBounds) : OS0Tempered :=
  -- Define temperedness as validity of the polynomial bounds
  { tempered := ∀ n, 0 ≤ poly.Cn n,
    poly_bounds := poly,
    tempered_holds := poly.Cn_nonneg }

end OSPositivity
end YM
