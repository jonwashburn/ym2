import Mathlib
import ym.PF3x3_Bridge
import ym.Transfer
import ym.spectral_stability.NRCEps
import ym.OSPositivity

/-!
Smoke tests (interface-level):
 - Instantiate PF3×3 bridge and produce a PF gap witness for arbitrary μ, K.
 - Check NRC norm-bound and comparison wrappers compile on toy data.
-/

namespace YM.Tests

open YM

def dummyμ : LatticeMeasure := (inferInstance : Inhabited LatticeMeasure).default
def dummyK : TransferKernel := (inferInstance : Inhabited TransferKernel).default

example : ∃ γ : ℝ, 0 < γ ∧ TransferPFGap dummyμ dummyK γ := by
  simpa using YM.pf_gap_from_reflected3x3 dummyμ dummyK

-- Persistence smoke test: the strengthened GapPersists export is inhabitable
example : YM.GapPersists (1/2) :=
  YM.gap_persists_via_Lipschitz (by norm_num)

example : True := by
  -- NRC wrappers exist and are inhabitable at interface-level
  let S := YM.NRC.ShortTime_wilson
  let K := YM.NRC.Calibrator_wilson
  have : YM.NRC.SpectralStability.NRC_all_nonreal S K := YM.NRC.SpectralStability.nrc_all_nonreal_holds S K
  trivial

end YM.Tests
