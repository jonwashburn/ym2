import ym.Main

/-!
Minimal axioms report scaffold. Keep this file light so it does not
participate in heavy dependency resolution during builds.
-/

namespace YM

/-- Build check sentinel. -/
def AxiomsReportReady : Prop := ∀ u : Unit, u = u

end YM
