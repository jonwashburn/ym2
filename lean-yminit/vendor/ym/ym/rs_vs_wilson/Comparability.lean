import Mathlib

/-
RS↔Wilson kernel comparability (signatures).
-/

namespace YM
namespace RSvW

structure Locality where
  A : ℝ
  mu : ℝ
  bound : Prop  -- |K(γ,γ')| ≤ A e^{−μ d(γ,γ')}

structure Onsite where
  b : ℝ
  B : ℝ
  bounds : Prop -- b ≤ K(γ,γ) ≤ B

structure Growth where
  Cg : ℝ
  nu : ℝ
  bound : Prop   -- #sphere(r) ≤ Cg e^{ν r}

structure GramBounds where
  lower : ℝ
  upper : ℝ
  lower_pos : Prop
  derived : Prop -- from Gershgorin/Schur

end RSvW
end YM
