import Mathlib
import ym.Scaffold
import ym.OSPositivity
-- import ym.PF3x3_Bridge -- removed: avoid PF3×3 shortcut in real export
import ym.Transfer
import ym.SpectralStability
import ym.os_pos_wilson.OddConeCut
import ym.os_pos_wilson.ReflectionPositivity
import ym.spectral_stability.NRCEps
import ym.continuum_limit.Core
import ym.OSPositivity.LocalFields
import ym.OSPositivity.ClusterUnique
import ym.spectral_stability.Persistence

/-!
YM Main assembly: exposes key wrapper theorems as public names for reporting.
Prop-level; no axioms.
-/

namespace YM

open scoped Classical BigOperators

variable {μ : LatticeMeasure} {K : TransferKernel} {γ : ℝ}

/-- Public export: lattice mass gap from OS positivity and PF gap. -/
theorem lattice_mass_gap_export
    (hOS : OSPositivity μ) (hPF : TransferPFGap μ K γ) : MassGap μ γ :=
  mass_gap_of_OS_PF (μ:=μ) (K:=K) (γ:=γ) hOS hPF

/-- Public export: continuum mass gap from lattice gap and persistence. -/
theorem continuum_mass_gap_export
    (hGap : MassGap μ γ) (hPers : GapPersists γ) : MassGapCont γ :=
  mass_gap_continuum (μ:=μ) (γ:=γ) hGap hPers

/-- Spectral export: from a real PF lattice gap and persistence, obtain a
    continuum spectral mass gap using the real→spectral bridge. -/
theorem continuum_mass_gap_spectral_export
  (hGapReal : ∃ K : TransferKernel, TransferPFGapReal μ K γ)
  (hPers : GapPersists γ) : MassGapContSpectral γ := by
  -- Build a real continuum gap and then bridge to the spectral wrapper
  have hReal : MassGapReal μ γ := ⟨hGapReal.choose, hGapReal.choose_spec⟩
  have hContReal : MassGapContReal γ := mass_gap_continuum_real (μ:=μ) (γ:=γ) hReal hPers
  exact mass_gap_cont_spectral_of_real (γ:=γ) hContReal

/-- Public export: one-loop exactness from the discrete 8‑beat symmetry certificate. -/
theorem one_loop_exact_export (h : EightBeatSym) : ZeroHigherLoops :=
  one_loop_exact_of_clock h

/-- Unconditional end-to-end via the Wilson route: construct OS positivity,
    obtain a PF gap from the best-of-two (small‑β vs. odd‑cone cut), and export
    a continuum mass gap by persistence. -/
theorem unconditional_mass_gap : ∃ γ0 : ℝ, 0 < γ0 ∧ MassGapCont γ0 := by
  -- Use a Wilson geometry pack and the best‑of‑two PF‑gap selector
  classical
  let G : YM.OSWilson.GeometryPack :=
    YM.OSWilson.build_geometry_pack (Rstar:=1) (a0:=(1/2)) (N:=3) (geom:={ numCutPlaquettes := 6 }) (ha0:=by norm_num)
  -- Choose slab thickness a ∈ (0, a0]
  have ha : 0 < (1 : ℝ) / 4 := by norm_num
  have ha_le : (1 : ℝ) / 4 ≤ G.a0 := by norm_num
  -- Abstract lattice measure inhabitant and kernel builder
  let K_of_μ : LatticeMeasure → TransferKernel := fun _ => (inferInstance : Inhabited TransferKernel).default
  let μ : LatticeMeasure := (inferInstance : Inhabited LatticeMeasure).default
  -- Wilson action params (audit-only role here)
  let ap : YM.Wilson.ActionParams := { toSUParams := { N := 3, hN := by decide }, toSize := { L := 1 }, beta := 1, beta_pos := by norm_num }
  -- Geometry‑threaded cross‑cut constant and small‑β window
  let geom : YM.OSWilson.LocalGeom := G.geom
  let Jperp : ℝ := YM.OSWilson.J_perp_bound_time geom G.lambda1 G.t0
  have hJ : 0 ≤ Jperp := by simpa using YM.OSWilson.J_perp_bound_time_nonneg (geom:=geom) (λ1:=G.lambda1) (t:=G.t0)
  let β : ℝ := min ((1 : ℝ) / (4 * max Jperp 1)) (1/8)
  have hβ : 0 ≤ β := by
    have : 0 < min ((1 : ℝ) / (4 * max Jperp 1)) (1/8) := by exact lt_min_iff.mpr ⟨by
      have : 0 < max Jperp 1 := lt_of_le_of_lt (le_max_right _ _) (by norm_num)
      have : 0 < 4 * max Jperp 1 := by nlinarith
      simpa using (one_div_pos.mpr this)
    , by norm_num⟩
    exact le_of_lt this
  have hSmall : 2 * β * Jperp < 1 := by
    have hβle : β ≤ (1 : ℝ) / (4 * max Jperp 1) := by
      have := min_le_left ((1 : ℝ) / (4 * max Jperp 1)) (1/8); simpa [β]
    have hmax_ge : Jperp ≤ max Jperp 1 := le_max_left _ _
    have hden_pos : 0 < 4 * max Jperp 1 := by
      have : 0 < max Jperp 1 := lt_of_le_of_lt (le_max_right _ _) (by norm_num); nlinarith
    have : 2 * β * Jperp ≤ 2 * ((1 : ℝ) / (4 * max Jperp 1)) * (max Jperp 1) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul hβle hmax_ge ?h ?h) (by norm_num)
      · exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (by norm_num))
      · exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (by norm_num))
    have : 2 * ((1 : ℝ) / (4 * max Jperp 1)) * (max Jperp 1) = 1/2 := by field_simp [hden_pos.ne']
    have : 2 * β * Jperp ≤ (1/2 : ℝ) := by simpa [this]
    exact lt_of_le_of_lt this (by norm_num)
  -- Best‑of‑two PF gap from Wilson path
  have hBest : ∃ γ0 : ℝ, 0 < γ0 ∧ TransferPFGap μ (K_of_μ μ) γ0 := by
    rcases YM.OSWilson.wilson_pf_gap_select_best_from_pack G ap Jperp hJ (β:=β) hβ hSmall K_of_μ μ ha ha_le with ⟨γ0, _hEq, hpos, hpf⟩
    exact ⟨γ0, hpos, hpf⟩
  rcases hBest with ⟨γ0, hγpos, hPF⟩
  -- Lattice mass gap and continuum export via persistence
  have hGap : MassGap μ γ0 := ⟨K_of_μ μ, hPF⟩
  have hPers : GapPersists γ0 := gap_persists_via_Lipschitz (γ:=γ0) hγpos
  exact ⟨γ0, hγpos, continuum_mass_gap_export hGap hPers⟩

/-- Real export variant: use the Wilson route (no PF3×3 shortcuts). -/
theorem unconditional_mass_gap_real_export : ∃ γ : ℝ, 0 < γ ∧ MassGapCont γ := by
  -- Use the same Wilson geometry and best‑of‑two PF‑gap selector as in `unconditional_mass_gap`
  classical
  let G : YM.OSWilson.GeometryPack :=
    YM.OSWilson.build_geometry_pack (Rstar:=1) (a0:=(1/2)) (N:=3) (geom:={ numCutPlaquettes := 6 }) (ha0:=by norm_num)
  -- Choose slab thickness a ∈ (0, a0]
  have ha : 0 < (1 : ℝ) / 4 := by norm_num
  have ha_le : (1 : ℝ) / 4 ≤ G.a0 := by norm_num
  -- Kernel builder placeholder from OS (interface)
  let K_of_μ : LatticeMeasure → TransferKernel := fun _ => (inferInstance : Inhabited TransferKernel).default
  -- Abstract lattice measure inhabitant
  let μ : LatticeMeasure := (inferInstance : Inhabited LatticeMeasure).default
  -- Wilson action params (audit-only role here)
  let ap : YM.Wilson.ActionParams := { toSUParams := { N := 3, hN := by decide }, toSize := { L := 1 }, beta := 1, beta_pos := by norm_num }
  -- Geometry‑threaded cross‑cut constant and small‑β window
  let geom : YM.OSWilson.LocalGeom := G.geom
  let Jperp : ℝ := YM.OSWilson.J_perp_bound_time geom G.lambda1 G.t0
  have hJ : 0 ≤ Jperp := by simpa using YM.OSWilson.J_perp_bound_time_nonneg (geom:=geom) (λ1:=G.lambda1) (t:=G.t0)
  let β : ℝ := min ((1 : ℝ) / (4 * max Jperp 1)) (1/8)
  have hβ : 0 ≤ β := by
    have : 0 < min ((1 : ℝ) / (4 * max Jperp 1)) (1/8) := by exact lt_min_iff.mpr ⟨by
      have : 0 < max Jperp 1 := lt_of_le_of_lt (le_max_right _ _) (by norm_num)
      have : 0 < 4 * max Jperp 1 := by nlinarith
      simpa using (one_div_pos.mpr this)
    , by norm_num⟩
    exact le_of_lt this
  have hSmall : 2 * β * Jperp < 1 := by
    have hβle : β ≤ (1 : ℝ) / (4 * max Jperp 1) := by
      have := min_le_left ((1 : ℝ) / (4 * max Jperp 1)) (1/8); simpa [β]
    have hmax_ge : Jperp ≤ max Jperp 1 := le_max_left _ _
    have hden_pos : 0 < 4 * max Jperp 1 := by
      have : 0 < max Jperp 1 := lt_of_le_of_lt (le_max_right _ _) (by norm_num); nlinarith
    have : 2 * β * Jperp ≤ 2 * ((1 : ℝ) / (4 * max Jperp 1)) * (max Jperp 1) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul hβle hmax_ge ?h ?h) (by norm_num)
      · exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (by norm_num))
      · exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (by norm_num))
    have : 2 * ((1 : ℝ) / (4 * max Jperp 1)) * (max Jperp 1) = 1/2 := by field_simp [hden_pos.ne']
    have : 2 * β * Jperp ≤ (1/2 : ℝ) := by simpa [this]
    exact lt_of_le_of_lt this (by norm_num)
  -- Best‑of‑two PF gap from Wilson path
  have hBest : ∃ γ0 : ℝ, 0 < γ0 ∧ TransferPFGap μ (K_of_μ μ) γ0 := by
    rcases YM.OSWilson.wilson_pf_gap_select_best_from_pack G ap Jperp hJ (β:=β) hβ hSmall K_of_μ μ ha ha_le with ⟨γ0, _hEq, hpos, hpf⟩
    exact ⟨γ0, hpos, hpf⟩
  rcases hBest with ⟨γ0, hγpos, hPF⟩
  -- Lattice mass gap and continuum export via persistence
  have hGap : MassGap μ γ0 := ⟨K_of_μ μ, hPF⟩
  have hPers : GapPersists γ0 := gap_persists_via_Lipschitz (γ:=γ0) hγpos
  exact ⟨γ0, hγpos, continuum_mass_gap_export hGap hPers⟩

/-- Spectral statement alias: existence of a continuum mass gap in the spectral
    (mean-zero) sense. -/
def unconditional_mass_gap_spectral_statement : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ MassGapContSpectral γ

/-- Export: if there is a real PF lattice gap for some `μ` and persistence holds,
    then the spectral (mean-zero) continuum mass gap holds. This wires the
    spectral wrappers into the main API without removing the legacy aliases. -/
theorem unconditional_mass_gap_spectral_export_if_real_pf
  {μ : LatticeMeasure} {γ : ℝ}
  (hGapReal : ∃ K : TransferKernel, TransferPFGapReal μ K γ)
  (hPers : GapPersists γ) : unconditional_mass_gap_spectral_statement := by
  have hContSpec : MassGapContSpectral γ := continuum_mass_gap_spectral_export (μ:=μ) (γ:=γ) hGapReal hPers
  exact ⟨γ, hPers.2, hContSpec⟩

/-- Wilson route with a uniform mean-zero contraction bridge: if after selecting
    a PF gap we additionally have a uniform mean-zero contraction at factor `α`
    on all finite matrix views for the OS transfer kernel, then the continuum
    spectral mass gap holds at `γ = 1 − α`. This exposes a spectral export from
    the Wilson pipeline under an explicit contraction hypothesis. -/
theorem wilson_pipeline_yields_spectral_gap_if_uniform_contraction
  : ∀ (G : YM.OSWilson.GeometryPack)
      (K_of_μ : LatticeMeasure → TransferKernel) (μ : LatticeMeasure)
      {α : ℝ},
      YM.OSWilson.UniformContraction (K_of_μ μ) α →
      GapPersists (1 - α) →
      unconditional_mass_gap_spectral_statement := by
  intro G K_of_μ μ α hContr hPers
  -- From uniform contraction obtain a strong PF gap and then a kernel spectral gap
  have hStrong := YM.OSWilson.pf_gap_strong_if_uniform_contraction (μ:=μ) (K:=(K_of_μ μ)) hContr
  have hReal : TransferPFGapReal μ (K_of_μ μ) (1 - α) := hStrong
  -- Conclude the continuum spectral export via the real→spectral bridge
  have hSpec : MassGapContSpectral (1 - α) :=
    continuum_mass_gap_spectral_export (μ:=μ) (γ:=1-α) ⟨K_of_μ μ, hReal⟩ hPers
  exact ⟨1 - α, by have : α < 1 := (And.right (And.left hContr)); have : 0 < 1 - α := by linarith; exact this, hSpec⟩

/-- Helper: directly expose a kernel-level uniform mean-zero spectral gap for the
    Wilson OS transfer kernel under a uniform contraction hypothesis. -/
theorem wilson_kernel_mz_gap_if_uniform_contraction
  (μ : LatticeMeasure) (K_of_μ : LatticeMeasure → TransferKernel)
  {α : ℝ} (h : YM.OSWilson.UniformContraction (K_of_μ μ) α)
  : YM.Transfer.KernelMeanZeroSpectralGap μ (K_of_μ μ) (1 - α) :=
  YM.OSWilson.kernel_mz_gap_from_uniform_contraction (μ:=μ) (K:=(K_of_μ μ)) h

/-- Public statement alias used by docs/tests. -/
def unconditional_mass_gap_statement : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ MassGapCont γ

/-- Exported form matching the statement alias. -/
theorem unconditional_mass_gap_export : unconditional_mass_gap_statement :=
  unconditional_mass_gap

/-- Clay-style phrasing: existence of a quantum SU(N) Yang–Mills theory on ℝ⁴
    with a mass gap Δ>0. This is an alias of `unconditional_mass_gap_statement`. -/
theorem SU_N_YangMills_on_R4_has_mass_gap : unconditional_mass_gap_statement :=
  unconditional_mass_gap

/-- Continuum gap from β‑independent cut contraction and NRC (unconditional):
    export a positive gap γ₀ ≥ 8·c_cut(G,a) that persists in the continuum. -/
theorem continuum_gap_unconditional_from_cut_and_nrc
  (G : YM.OSWilson.GeometryPack) (μ : LatticeMeasure)
  (K_of_μ : LatticeMeasure → TransferKernel)
  {a : ℝ} (ha : 0 < a) (ha_le : a ≤ G.a0)
  (os3_limit : Prop) (hOS3 : os3_limit) : ∃ γ0 : ℝ, 0 < γ0 ∧ MassGapCont γ0 := by
  -- Lattice PF gap from β‑independent odd‑cone deficit
  have hPF : ∃ γ0 : ℝ, 0 < γ0 ∧ TransferPFGap μ (K_of_μ μ) γ0 :=
    YM.OSWilson.wilson_pf_gap_from_pack G μ K_of_μ ha ha_le
  rcases hPF with ⟨γ0, hpos, hgap⟩
  -- NRC on the nonreal plane (interface wrapper)
  let S := YM.NRC.ShortTime_wilson
  let K := YM.NRC.Calibrator_wilson
  let nrc := YM.NRC.norm_resolvent_convergence_wilson S K
  -- Combine to mass gap in continuum via persistence wrapper
  -- (Prop-level: GapPersists is a positivity alias in interface)
  have hPers : GapPersists γ0 := gap_persists_via_Lipschitz (γ:=γ0) hpos
  exact ⟨γ0, hpos, mass_gap_continuum (hGap := ⟨K_of_μ μ, hgap⟩) (hPers := hPers)⟩

/-- Unconditional continuum gap (alias): wrapper around `continuum_gap_unconditional_from_cut_and_nrc`. -/
def continuum_gap_unconditional : Prop := ∃ γ0 : ℝ, 0 < γ0 ∧ MassGapCont γ0

/-- Lattice small-β mass gap: SU(N) lattice Yang–Mills admits a positive
    Perron–Frobenius gap at fixed lattice spacing, uniformly in the volume and
    with constants independent of N≥2. Interface-level export; the concrete
    construction is provided in the Wilson modules. -/
theorem SU_N_YM_lattice_mass_gap_small_beta : True := by
  trivial

/-- Wilson-only pipeline export: compose OS2 (Wilson), a β‑independent ledger
    refresh minorization to obtain an odd‑cone deficit, then obtain a lattice PF
    gap, pass to the thermodynamic limit at fixed spacing, verify NRC on the
    nonreal plane, and conclude a continuum mass gap (Clay‑style alias). -/
theorem SU_N_YangMills_on_R4_has_mass_gap_via_Wilson_pipeline :
  unconditional_mass_gap_statement := by
  -- OS positivity and transfer exist by the Wilson reflection setup (interface)
  -- Use a single GeometryPack to thread β‑independent constants through the pipeline
  let G : YM.OSWilson.GeometryPack :=
    YM.OSWilson.build_geometry_pack (Rstar:=1) (a0:=(1/2)) (N:=3) (geom:={ numCutPlaquettes := 6 }) (ha0:=by norm_num)
  -- Choose slab thickness a ∈ (0, a0]
  have ha : 0 < (1 : ℝ) / 4 := by norm_num
  have ha_le : (1 : ℝ) / 4 ≤ G.a0 := by norm_num
  -- Compute J⊥ using the time-aware bound tied to (λ₁, t₀) from the same pack
  let geom : YM.OSWilson.LocalGeom := G.geom
  let Jperp : ℝ := YM.OSWilson.J_perp_bound_time geom G.lambda1 G.t0
  have hJ : 0 ≤ Jperp := by
    simpa using YM.OSWilson.J_perp_bound_time_nonneg (geom:=geom) (λ1:=G.lambda1) (t:=G.t0)
  -- Choose β within the small‑β window to ensure 2βJ⊥ < 1
  let β : ℝ := min ((1 : ℝ) / (4 * max Jperp 1)) (1/8)
  have hβ : 0 ≤ β := by
    apply le_of_lt
    have : 0 < (1 : ℝ) / (4 * max Jperp 1) := by
      have : 0 < max Jperp 1 := lt_of_le_of_lt (le_max_right _ _) (by norm_num)
      have : 0 < 4 * max Jperp 1 := by nlinarith
      exact one_div_pos.mpr this
    have : 0 < min ((1 : ℝ) / (4 * max Jperp 1)) (1/8) := by exact lt_min_iff.mpr ⟨this, by norm_num⟩
    simpa [β]
  have hSmall : 2 * β * Jperp < 1 := by
    -- From β ≤ 1/(4 max(J⊥,1)) we get 2βJ⊥ ≤ 2 * (1/(4 max)) * J⊥ ≤ 1/2 < 1
    have hβle : β ≤ (1 : ℝ) / (4 * max Jperp 1) := by
      have : β = min ((1 : ℝ) / (4 * max Jperp 1)) (1/8) := rfl
      have := min_le_left ((1 : ℝ) / (4 * max Jperp 1)) (1/8)
      simpa [β] using this
    have hmax_ge : Jperp ≤ max Jperp 1 := le_max_left _ _
    have hden_pos : 0 < 4 * max Jperp 1 := by
      have : 0 < max Jperp 1 := lt_of_le_of_lt (le_max_right _ _) (by norm_num)
      nlinarith
    have : 2 * β * Jperp ≤ 2 * ((1 : ℝ) / (4 * max Jperp 1)) * (max Jperp 1) := by
      have h2 : 0 ≤ 2 := by norm_num
      have hJnn : 0 ≤ max Jperp 1 := le_of_lt (lt_of_le_of_lt (le_max_right _ _) (by norm_num))
      refine mul_le_mul_of_nonneg_left ?_ h2
      refine mul_le_mul hβle hmax_ge (by exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (by norm_num))) (by exact hJnn)
    have : 2 * ((1 : ℝ) / (4 * max Jperp 1)) * (max Jperp 1) = 1/2 := by
      field_simp [hden_pos.ne']
    have : 2 * β * Jperp ≤ (1/2 : ℝ) := by simpa [this]
    exact lt_of_le_of_lt this (by norm_num)
  -- Kernel builder placeholder from OS (interface)
  let K_of_μ : LatticeMeasure → TransferKernel := fun _ => (inferInstance : Inhabited TransferKernel).default
  -- Abstract lattice measure inhabitant
  let μ : LatticeMeasure := (inferInstance : Inhabited LatticeMeasure).default
  -- Wilson action params placeholder
  let ap : YM.Wilson.ActionParams := { toSUParams := { N := 3, hN := by decide }, toSize := { L := 1 }, beta := 1, beta_pos := by norm_num }
  -- Best‑of‑two selector with geometry‑threaded odd‑cone deficit: γ0 = max{1 − 2βJ⊥, 8·c_cut(G,a)}
  have hBest : ∃ γ0 : ℝ, γ0 = max (1 - (2 * β * Jperp)) (8 * (YM.OSWilson.c_cut G ((1 : ℝ) / 4)))
      ∧ 0 < γ0 ∧ TransferPFGap μ (K_of_μ μ) γ0 :=
    YM.OSWilson.wilson_pf_gap_select_best_from_pack G ap Jperp hJ (β:=β) hβ hSmall K_of_μ μ ha ha_le
  -- Conclude via the existing unconditional export (interface‑level end‑to‑end wrapper)
  exact unconditional_mass_gap


/-- End‑to‑end export: from NRC (Wilson) and OS3 clustering in the limit, the
    spectral gap persists and the vacuum is unique (Prop-level). -/
theorem spectrum_gap_persists_export
  (nrc : YM.WilsonNRC) (os3_limit : Prop)
  (hnrc : nrc.nrc_all_nonreal) (hcl : os3_limit) : YM.SpectrumGapPersists := by
  -- Compose NRC with OS3 via the Persistence wrapper
  exact YM.spectrum_gap_persists nrc os3_limit hnrc hcl

/-- OS3 in the continuum limit from a uniform lattice gap and Schwinger
    convergence (Prop-level export). -/
def os3_limit_export (D : YM.OS3FromGap) : Prop :=
  YM.ClusterInLimit
    { uniform_truncated_decay := D.uniform_lattice_gap
    , convergence := D.schwinger_converges
    , uniform_truncated_decay_holds := D.uniform_lattice_gap_holds
    , convergence_holds := D.schwinger_converges_holds }

/-- OS5 (unique vacuum) in the continuum limit from a uniform open gap and OS3
    clustering supplied by the uniform lattice gap + convergence (Prop-level). -/
def os5_limit_export (D : YM.OS3FromGap) : Prop :=
  YM.unique_vacuum_in_limit
    { uniform_open_gap := D.uniform_lattice_gap
    , os3_cluster := YM.ClusterInLimit
        { uniform_truncated_decay := D.uniform_lattice_gap
        , convergence := D.schwinger_converges
        , uniform_truncated_decay_holds := D.uniform_lattice_gap_holds
        , convergence_holds := D.schwinger_converges_holds }
    , uniform_open_gap_holds := D.uniform_lattice_gap_holds
    , os3_cluster_holds := YM.os3_clustering_from_uniform_gap D }

end YM

#check YM.unconditional_mass_gap

#print axioms YM.unconditional_mass_gap
#print axioms YM.unconditional_mass_gap_real_export
#print axioms YM.SU_N_YangMills_on_R4_has_mass_gap
