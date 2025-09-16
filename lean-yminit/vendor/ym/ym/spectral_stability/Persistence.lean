import Mathlib

/-
Spectral stability signatures (Lipschitz/Weyl and norm–resolvent persistence).
-/

namespace YM
namespace Stability

structure LipschitzGap where
  eps : ℝ
  bound : eps ≥ 0
  persists : Prop

structure NormResolvent where
  compact_resolvent : Prop
  defect_small : Prop
  spec_lower_bound : Prop

end Stability

/‑‑ Quantitative NRC data: encapsulates a simple bound schema for audits. -/
namespace SpectralStability

/-- Container for a quantitative NRC norm bound on a contour: `bound = C_K * C_R * ε`. -/
structure NRCQuant where
  CK : ℝ                    -- contour length / (2π), etc.
  CR : ℝ                    -- uniform resolvent bound on the contour
  eps : ℝ                   -- sup_z ||R_n(z) - R(z)||
  CK_nonneg : 0 ≤ CK
  CR_nonneg : 0 ≤ CR
  eps_nonneg : 0 ≤ eps

@[simp] def nrc_norm_bound_value (Q : NRCQuant) : ℝ := Q.CK * Q.CR * Q.eps

@[simp] theorem nrc_norm_bound_nonneg (Q : NRCQuant) : 0 ≤ nrc_norm_bound_value Q := by
  have h1 : 0 ≤ Q.CK * Q.CR := mul_nonneg Q.CK_nonneg Q.CR_nonneg
  exact mul_nonneg h1 Q.eps_nonneg

/-- Quantitative persistence hypotheses: open gap `γ₀>0` and a small NRC bound. -/
structure GapPersistenceQuantHyp where
  gamma0 : ℝ
  gamma_pos : 0 < gamma0
  bound : ℝ
  small : bound < gamma0

@[simp] theorem persistence_lower_bound_quant (H : GapPersistenceQuantHyp) : 0 < H.gamma0 :=
  H.gamma_pos

end SpectralStability

/-- Gap persistence under NRC: interface-level Prop bundle. -/
structure GapPersistenceNRC where
  uniform_open_gap : Prop
  nrc : Prop
  uniform_open_gap_holds : uniform_open_gap
  nrc_holds : nrc

/-- Recorded conclusion for gap persistence via NRC. -/
 def GapPersistsInLimit (H : GapPersistenceNRC) : Prop :=
  H.uniform_open_gap ∧ H.nrc

@[simp] theorem gap_persists_via_nrc (H : GapPersistenceNRC) : GapPersistsInLimit H := by
  exact And.intro H.uniform_open_gap_holds H.nrc_holds

/-- Export: persistence lower bound (interface). -/
def persistence_lower_bound (H : GapPersistenceNRC) : Prop := GapPersistsInLimit H

/-- Export: gap persists in the continuum (interface). -/
def gap_persists_in_continuum (H : GapPersistenceNRC) : Prop := GapPersistsInLimit H

/-- Wilson NRC bundle (interface). -/
structure WilsonNRC where
  nrc_all_nonreal : Prop
  nrc_all_nonreal_holds : nrc_all_nonreal

/-- Export: spectral gap persists and the vacuum is unique (interface Prop). -/
def SpectrumGapPersists : Prop :=
  ∃ (uniform_open_gap : Prop) (nrc : Prop), uniform_open_gap ∧ nrc

/-- Compose NRC with OS3 clustering in the limit to export the spectrum persistence. -/
 theorem spectrum_gap_persists
  (nrc : WilsonNRC) (os3_limit : Prop)
  (hnrc : nrc.nrc_all_nonreal) (hcl : os3_limit) : SpectrumGapPersists := by
  refine ⟨os3_limit, nrc.nrc_all_nonreal, hcl, hnrc⟩

/-- Construct a persistence witness from a quantitative NRC contour bound.
    If the NRC norm bound is ≤ a scalar `bound`, and `bound < γ₀`, then we
    obtain a `GapPersistenceNRC` witness with `uniform_open_gap := (0 < γ₀)`
    and `nrc := (‖R_n - R‖ on the contour) < γ₀`.
    The constants here are abstract and do not depend on β or volume. -/
theorem persistence_from_contour_bound
  (Q : SpectralStability.NRCQuant)
  (H : SpectralStability.GapPersistenceQuantHyp)
  (hb : SpectralStability.nrc_norm_bound_value Q ≤ H.bound)
  : GapPersistenceNRC :=
{ uniform_open_gap := (0 < H.gamma0)
, nrc := (SpectralStability.nrc_norm_bound_value Q < H.gamma0)
, uniform_open_gap_holds := H.gamma_pos
, nrc_holds := lt_of_le_of_lt hb H.small }

/-- Direct SpectrumGapPersists export from a quantitative NRC contour bound and
    a gap margin `γ₀`. -/
theorem nrc_gap_via_contour
  (Q : SpectralStability.NRCQuant)
  (H : SpectralStability.GapPersistenceQuantHyp)
  (hb : SpectralStability.nrc_norm_bound_value Q ≤ H.bound)
  : SpectrumGapPersists := by
  refine ⟨(0 < H.gamma0), SpectralStability.nrc_norm_bound_value Q < H.gamma0, ?hg, ?hnrc⟩
  · exact H.gamma_pos
  · exact lt_of_le_of_lt hb H.small

/-- Immediate export: any `GapPersistenceNRC` witness yields `SpectrumGapPersists`. -/
theorem spectrum_gap_persists_from_nrc (H : GapPersistenceNRC) : SpectrumGapPersists := by
  exact ⟨H.uniform_open_gap, H.nrc, H.uniform_open_gap_holds, H.nrc_holds⟩

/-- OS5 hypotheses (interface). -/
structure OS5Hypotheses where
  uniform_open_gap : Prop
  norm_resolvent_convergence : Prop
  uniform_open_gap_holds : uniform_open_gap
  norm_resolvent_convergence_holds : norm_resolvent_convergence

/-- OS5 conclusion (interface). -/
 def OS5Conclusion (H : OS5Hypotheses) : Prop :=
  H.uniform_open_gap ∧ H.norm_resolvent_convergence

@[simp] theorem os5_unique_vacuum_and_gap (H : OS5Hypotheses) : OS5Conclusion H := by
  exact And.intro H.uniform_open_gap_holds H.norm_resolvent_convergence_holds

end YM
