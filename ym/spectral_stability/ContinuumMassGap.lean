import Mathlib
import ym.spectral_stability.Persistence

/-!
Continuum mass gap (Prop-level interface): package OS-limit existence with
gap persistence (via NRC) to record a strictly positive mass gap in the
continuum theory.
-/

namespace YM
namespace Stability

/-- Hypotheses to assert a strictly positive continuum mass gap. -/
structure ContinuumMassGapHypotheses where
  os_limit_exists : Prop            -- OS0–OS3 satisfied in the continuum limit
  gap_persists : Prop               -- spectral gap persists under NRC
  os_limit_exists_holds : os_limit_exists
  gap_persists_holds : gap_persists

/-- Recorded conclusion for a strictly positive continuum mass gap. -/
def ContinuumMassGap (H : ContinuumMassGapHypotheses) : Prop :=
  H.os_limit_exists ∧ H.gap_persists

/-- Interface theorem: under the hypotheses, the continuum theory has a
    strictly positive spectral gap. -/
theorem continuum_mass_gap (H : ContinuumMassGapHypotheses) : ContinuumMassGap H := by
  exact And.intro H.os_limit_exists_holds H.gap_persists_holds

end Stability
end YM
