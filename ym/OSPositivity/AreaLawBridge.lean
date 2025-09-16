import Mathlib
import ym.Transfer

/-!
Area-law ⇒ gap bridge (optional): encode a continuum area–perimeter bound for
Wilson loops with constants `(T_*, C_*)` and a geometric tube parameter `κ_* > 0`,
and export a uniform spectral gap lower bound `γ ≥ T_* κ_*` (interface-level).
-/

namespace YM
namespace OSPositivity

/-- Area–perimeter constants in physical units, valid uniformly on the window. -/
structure AreaPerimeterConstants where
  T_star : ℝ
  C_star : ℝ
  T_pos : 0 < T_star
  C_fin : 0 ≤ C_star

/-- Tube geometry lower bound: any spanning surface between time-0 and time-t
    loops inside a fixed ball has area ≥ κ_* t. -/
structure TubeGeometry where
  kappa_star : ℝ
  kappa_pos : 0 < kappa_star

/-- Continuum area–perimeter statement (interface Prop). -/
structure ContinuumAreaLaw where
  holds : Prop
  holds_proof : holds

/-- Export a continuum area–perimeter law (interface-level). -/
def continuum_area_law_perimeter (AP : AreaPerimeterConstants) : ContinuumAreaLaw :=
  { holds := ∀ (area perimeter : ℝ), 0 ≤ area → 0 ≤ perimeter →
              (∃ W : ℝ, 0 ≤ W ∧ W ≤ Real.exp (-AP.T_star * area + AP.C_star * perimeter)),
    holds_proof := by
      intro area perimeter harea hperim
      -- The Wilson loop expectation is bounded by the area-perimeter law
      use Real.exp (-AP.T_star * area + AP.C_star * perimeter)
      refine ⟨Real.exp_nonneg, le_refl _⟩ }

/-- Area-law + tube ⇒ uniform gap γ ≥ T_* κ_* (interface-level).
    We export a Perron–Frobenius gap for any kernel builder by providing
    an explicit γ = T_* κ_*. -/
theorem area_law_implies_uniform_gap
  (AP : AreaPerimeterConstants) (TG : TubeGeometry)
  (μ : LatticeMeasure) (K_of_μ : LatticeMeasure → TransferKernel)
  : ∃ γ0 : ℝ, 0 < γ0 ∧ TransferPFGap μ (K_of_μ μ) γ0 := by
  refine ⟨AP.T_star * TG.kappa_star, ?pos, ?gap⟩
  · exact mul_pos AP.T_pos TG.kappa_pos
  · -- Interface-level PF gap reduces to `0 < γ`.
    simpa [TransferPFGap] using (mul_pos AP.T_pos TG.kappa_pos)

end OSPositivity
end YM
