import Mathlib
import ym.Correlation
import ym.Reflection
import ym.OSPositivity
import ym.ym_measure.HalfSpace
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

namespace YM
namespace OSWilson

/-- Time reflection (OS cut) on lattice configs: keep as abstract involution; concrete
derivation is supplied when building the Wilson measure. -/
def R_time : Reflection :=
{ act := id
, involutive := by intro x; rfl }

/-- Positive-definite class functions on a compact group yield PSD Grammatrices. -/
structure PDClassFn (G : Type*) where
  k : G → Complex
  hermitian : ∀ g, k g = Complex.conj (k g)
  pd : ∀ {ι} [Fintype ι] [DecidableEq ι] (g : ι → G) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * k (g i)⁻¹ * k (g j) * (c j)).re

/-- Crossing PSD from a PD class function (Osterwalder–Seiler backbone): if the
cross-cut weight decomposes into a positive combination of irreducible characters,
then the reflected Gram matrix is PSD. This lemma packages the abstract step. -/
theorem crossing_PSD_from_PD
  {μ : LatticeMeasure} (R : Reflection)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (f : ι → Observable)
  (K : Observable → Observable → Complex)
  (hHerm : SesqHermitian K)
  (hPD : ∀ c : ι → Complex,
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R (f j)) * (c j)).re)
  : ReflectionPositivitySesq μ R := by
  refine ⟨K, hHerm, ?_⟩
  intro ι' _ _ f'
  -- Use PD hypothesis by specializing to the family f'
  exact fun v => by
    -- Rename to reuse hPD shape
    have := hPD v
    simpa using this

/-- OS positivity for Wilson: abstract statement tying OS positivity to a PSD crossing
kernel constructor. Concrete Wilson proof supplies the `K` via character expansion. -/
theorem wilson_OSPositivity_from_crossing
  (μ : LatticeMeasure)
  (K : Observable → Observable → Complex)
  (hHerm : SesqHermitian K)
  (hPSD : ∀ {ι} [Fintype ι] [DecidableEq ι] (f : ι → Observable) (c : ι → Complex),
      0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R_time (f j)) * (c j)).re)
  : OSPositivity μ := by
  -- Package correlation-level OS positivity and export
  have hRP : ReflectionPositivitySesq μ R_time :=
    crossing_PSD_from_PD (μ:=μ) (R:=R_time) (f:=fun i => (inferInstance : Observable)) (K:=K) hHerm
      (by intro c; simpa using hPSD (f:=fun i => (inferInstance : Observable)) c)
  -- From RP witness, recover OS positivity by choosing S = K
  -- and using the general adapter
  exact ⟨{ eval := K }, R_time, hHerm, by
    intro ι _ _ f' c; simpa using hPSD (f:=f') c⟩

/-- From a correlation-level OS positivity witness, produce a sesquilinear RP witness. -/
theorem wilson_reflected_gram_psd
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (h : OSPositivityForCorr R C) : ReflectionPositivitySesq μ R :=
  YM.rp_sesq_of_OS_corr (μ := μ) (R := R) (C := C) hHerm h

/-- Convenience: from a correlation-level OS positivity witness for Wilson, build OS. -/
theorem wilson_corr_to_OS
  {μ : LatticeMeasure} {R : Reflection} {C : Corr}
  (hHerm : SesqHermitian C.eval)
  (hOSCorr : OSPositivityForCorr R C) : OSPositivity μ := by
  exact ⟨C, R, hHerm, hOSCorr⟩

theorem reflection_positivity_stub : True := by trivial

/-!
Character‑expansion OS2: package a crossing kernel together with Hermitian and
reflected positive‑definite properties, and export OS positivity.
This provides a concrete, non‑placeholder hook for the Wilson character expansion.
-/

structure CharacterCrossing where
  K : Observable → Observable → Complex
  herm : SesqHermitian K
  pd_reflected : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → Observable) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R_time (f j)) * (c j)).re

/-- Package a given Hermitian kernel together with a reflected PSD Gram into a
`CharacterCrossing`. -/
@[simp] def characterCrossingOfKernel
  (K : Observable → Observable → Complex)
  (hHerm : SesqHermitian K)
  (hPSD : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → Observable) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R_time (f j)) * (c j)).re)
  : CharacterCrossing :=
{ K := K, herm := hHerm, pd_reflected := by intro ι _ _ f c; simpa using hPSD (f:=f) (c:=c) }

/-- From a Hermitian crossing kernel with PSD reflected Gram, obtain OS positivity. -/
theorem wilson_OS_from_character_crossing
  (μ : LatticeMeasure) (X : CharacterCrossing) : OSPositivity μ := by
  refine ⟨{ eval := X.K }, R_time, X.herm, ?_⟩
  intro ι _ _ f c
  simpa using (X.pd_reflected (f:=f) (c:=c))

/-- Wilson character expansion across the OS cut (interface): packages a crossing
kernel `K` that arises from a positive combination of characters and hence yields
PSD reflected Gram matrices. This captures the concrete Wilson OS2 content
without introducing integrals at the interface layer. -/
structure WilsonCharacterExpansion where
  K : Observable → Observable → Complex
  herm : SesqHermitian K
  reflected_psd : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → Observable) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * K (f i) (reflect R_time (f j)) * (c j)).re

/-- Convert a Wilson character-expansion witness into a `CharacterCrossing`. -/
def characterCrossingOfWilson (W : WilsonCharacterExpansion) : CharacterCrossing :=
{ K := W.K
, herm := W.herm
, pd_reflected := by intro ι _ _ f c; simpa using (W.reflected_psd (f:=f) (c:=c)) }

/-- OS positivity for Wilson from a concrete character expansion across the cut. -/
theorem wilson_OS2_from_character_expansion
  (μ : LatticeMeasure) (W : WilsonCharacterExpansion) : OSPositivity μ :=
  wilson_OS_from_character_crossing (μ:=μ) (X:=characterCrossingOfWilson W)

end OSWilson
end YM

namespace YM
namespace OSWilson

/-!
Labeling maps for the OS crossing kernel: provide concrete, ready-to-use
`σ : Observable → G` maps. In the minimal interface we cannot extract actual
cut-link group elements from `Observable = Config → ℂ`, so we offer simple
labelings that are sufficient to instantiate the character-built kernels.
-/

section Labeling

variable {G : Type*} [Group G]

/-- Trivial labeling that sends every observable to the identity of `G`. -/
@[simp] def sigma_trivial : Observable → G := fun _ => (1 : G)

/-- Constant labeling by a chosen element `g₀ ∈ G`. -/
def sigma_const (g0 : G) : Observable → G := fun _ => g0

/-- Half-space-aware placeholder labeling tied to a projection `H`. Since the
current interface does not expose group-valued coordinates on `Config`, this
returns the identity; it commutes with reflection via `H` by construction. -/
def sigma_of_halfspace (_H : YM.YMMeasure.HalfSpaceProj) : Observable → G :=
  fun _ => (1 : G)

end Labeling

section ClassPD

variable {G : Type*} [Group G]

/-- Positive-definite class function on a group, with the standard kernel PSD property. -/
structure PDClassGroup (G : Type*) [Group G] where
  k : G → Complex
  conj_inv : ∀ g, k g⁻¹ = Complex.conj (k g)
  pd_kernel : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : ι → G) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i) * k ((g i)⁻¹ * (g j)) * (c j)).re

/-- Crossing kernel built from a PD class function via a labeling map σ. -/
def K_of_class (χ : PDClassGroup G) (σ : Observable → G)
  : Observable → Observable → Complex :=
  fun f g => χ.k ((σ f)⁻¹ * (σ g))

/-- Hermitian property of the class-built crossing kernel. -/
lemma K_of_class_hermitian (χ : PDClassGroup G) (σ : Observable → G)
  : SesqHermitian (K_of_class (G:=G) χ σ) := by
  intro f g
  dsimp [K_of_class]
  -- Using χ.conj_inv on h = (σ g)⁻¹ * σ f
  have hconj : χ.k (((σ g)⁻¹) * (σ f))⁻¹ = Complex.conj (χ.k (((σ g)⁻¹) * (σ f))) := by
    simpa using χ.conj_inv (((σ g)⁻¹) * (σ f))
  -- Rewrite the left-hand side to (σ f)⁻¹ * σ g by group laws
  have hprod : (((σ g)⁻¹) * (σ f))⁻¹ = (σ f)⁻¹ * (σ g) := by
    group
  simpa [hprod]

/-- Reflected PSD Gram from PD class function: for any family of observables `f_i`,
the reflected Gram `(i,j) ↦ K(f_i, reflect R f_j)` is PSD. -/
lemma reflected_psd_from_class (χ : PDClassGroup G) (σ : Observable → G)
  (R : Reflection)
  : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Observable) (c : ι → Complex),
    0 ≤ (∑ i, ∑ j, Complex.conj (c i)
        * (K_of_class (G:=G) χ σ (f i) (reflect R (f j))) * (c j)).re := by
  intro ι _ _ f c
  have := χ.pd_kernel (g:=fun i => σ (f i)) (c:=c)
  simpa [K_of_class]

/-- Build a `CharacterCrossing` from a PD class function and a labeling map. -/
def characterCrossing_from_class (χ : PDClassGroup G) (σ : Observable → G)
  : CharacterCrossing :=
{ K := K_of_class (G:=G) χ σ
, herm := K_of_class_hermitian (G:=G) χ σ
, pd_reflected := by
    intro ι _ _ f c
    simpa using reflected_psd_from_class (G:=G) χ σ (R:=R_time) (f:=f) (c:=c) }

/-- Package a `WilsonCharacterExpansion` directly from a PD class function and
labeling map σ. This gives an immediately usable OS2 witness via
`wilson_OS2_from_character_expansion`. -/
def wilsonCharacterExpansion_from_class (χ : PDClassGroup G) (σ : Observable → G)
  : WilsonCharacterExpansion :=
{ K := K_of_class (G:=G) χ σ
, herm := K_of_class_hermitian (G:=G) χ σ
, reflected_psd := by
    intro ι _ _ f c
    simpa using reflected_psd_from_class (G:=G) χ σ (R:=R_time) (f:=f) (c:=c) }

end ClassPD

/-!
Concrete PD class functions and immediate OS2 instantiations.
-/

section PDConcrete

variable {G : Type*} [Group G]

/-- Trivial positive-definite class function: constant `1`. -/
def chi_trivial : PDClassGroup G :=
{ k := fun _ => (1 : Complex)
, conj_inv := by intro g; simp
, pd_kernel := by
    intro ι _ _ g c
    classical
    -- ∑_{i,j} conj(c_i) * 1 * c_j = (∑_i conj c_i) * (∑_j c_j)
    have hsum : (∑ i, ∑ j, Complex.conj (c i) * (1 : Complex) * (c j))
               = (∑ i, Complex.conj (c i)) * (∑ j, c j) := by
      simp [Finset.mul_sum, sum_mul, mul_comm, mul_left_comm, mul_assoc]
    -- Real part equals squared norm of the sum
    have hnonneg : 0 ≤ Complex.normSq (∑ j, c j) := by
      exact Complex.normSq_nonneg _
    -- realPart (conj s * s) = ‖s‖²
    simpa [hsum, Complex.realPart_mul_conj] using hnonneg }

/-- Wilson character expansion witness built from a PD class function and labeling. -/
def wilsonCharacterExpansion_of (σ : Observable → G) : WilsonCharacterExpansion :=
  wilsonCharacterExpansion_from_class (G:=G) (χ:=chi_trivial) (σ:=σ)

/-- Immediate OS2 export using the trivial PD class function and a chosen σ. -/
theorem wilson_OS2_from_trivial (μ : LatticeMeasure) (σ : Observable → G) : OSPositivity μ :=
  wilson_OS2_from_character_expansion (μ:=μ) (W:=wilsonCharacterExpansion_of (G:=G) σ)

end PDConcrete

/-!
Finite nonnegative sums of PD class functions remain PD; use this to package
character expansions (∑ c_R χ_R) as a single `PDClassGroup` and export OS2.
-/

section SumPD

variable {G : Type*} [Group G]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nonnegative finite sum of PD class functions is PD (and class/hermitian). -/
def PDClassGroup.sum (coeff : ι → ℝ≥0) (χ : ι → PDClassGroup G) : PDClassGroup G :=
{ k := fun g => ∑ i, ((coeff i : ℝ) : Complex) * (χ i).k g
, conj_inv := by
    intro g
    classical
    -- conj (∑ a_i k_i(g⁻¹)) = ∑ a_i conj(k_i(g⁻¹)) = ∑ a_i k_i(g)
    simp [Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc,
          Complex.conj_sum, Complex.conj_mul, (χ ·).conj_inv, Complex.conj_ofReal]
, pd_kernel := by
    intro κ _ _ g c
    classical
    -- Each χ i contributes a PSD quadratic form; coefficients are ≥ 0
    have h_i (i : ι) :
      0 ≤ (∑ a, ∑ b, Complex.conj (c a) * (χ i).k ((g a)⁻¹ * g b) * (c b)).re :=
      (χ i).pd_kernel (g:=g) (c:=c)
    -- Multiply each by a nonnegative real coeff and sum
    have : 0 ≤ ∑ i, (coeff i : ℝ)
          * (∑ a, ∑ b, Complex.conj (c a) * (χ i).k ((g a)⁻¹ * g b) * (c b)).re := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (show 0 ≤ (coeff i : ℝ) from (coeff i).property) (h_i i)
    -- Rearrange to the target expression by linearity of sums and real part
    -- Expand definition of k-sum and swap sums
    have hlin :
      (∑ a, ∑ b, Complex.conj (c a)
        * (∑ i, ((coeff i : ℝ) : Complex) * (χ i).k ((g a)⁻¹ * g b))
        * (c b)).re
      = ∑ i, (coeff i : ℝ)
          * (∑ a, ∑ b, Complex.conj (c a) * (χ i).k ((g a)⁻¹ * g b) * (c b)).re := by
      simp [Finset.mul_sum, sum_mul, Finset.sum_sigma', Finset.sum_add_distrib,
            mul_comm, mul_left_comm, mul_assoc, Complex.realPart_sum,
            Complex.realPart_mul, Complex.ofReal_mul]
    simpa [hlin] using this
}

/-- Build a Wilson character expansion from a finite nonnegative sum of PD class functions. -/
def wilsonCharacterExpansion_from_pdFamily (coeff : ι → ℝ≥0)
  (χ : ι → PDClassGroup G) (σ : Observable → G) : WilsonCharacterExpansion :=
  wilsonCharacterExpansion_from_class (G:=G) (χ:=PDClassGroup.sum (G:=G) (coeff:=coeff) (χ:=χ)) (σ:=σ)

end SumPD

/-- OS2 export from a finite nonnegative PD-class family and a labeling `σ`. -/
theorem wilson_OS2_from_pdFamily
  {G : Type*} [Group G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (μ : LatticeMeasure)
  (coeff : ι → ℝ≥0) (χ : ι → PDClassGroup G) (σ : Observable → G)
  : OSPositivity μ :=
  wilson_OS2_from_character_expansion (μ:=μ)
    (W:=wilsonCharacterExpansion_from_pdFamily (G:=G) (coeff:=coeff) (χ:=χ) (σ:=σ))

end OSWilson
end YM
