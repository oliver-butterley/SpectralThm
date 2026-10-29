/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.SpectralTheorem

/-!
# The Borel functional calculus of a normal operator

For a normal operator `a` on a complex Hilbert space `H` with spectral measure `E`, the Borel
functional calculus sends a function `f : ℂ → ℂ` which is bounded and measurable on `σ(a)` to
`f(a) = ∫ f dE`. Following `cfc`, it is defined for all `f`, with the junk value `0` when the
restriction of `f` to `σ(a)` is not in `L^∞(E)`.

## Main definitions

* `IsStarNormal.bfc ha f`: the operator `f(a) = ∫ f dE`.

## Main results

* `IsStarNormal.bfc_eq_cfc`: the Borel functional calculus extends the continuous one.
* `IsStarNormal.bfc_id`: `id(a) = a`.
* `IsStarNormal.bfc_add`, `IsStarNormal.bfc_mul`, `IsStarNormal.bfc_star`, ...: it is a
  `*`-homomorphism.
* `IsStarNormal.bfc_indicator`: the indicator of `s` gives the spectral projection `E(s)`.
* `IsStarNormal.bfc_congr_ae`: `f(a)` only depends on `f` up to `E`-null sets.
* `IsStarNormal.norm_bfc_le`: `‖f(a)‖ ≤ sup_{σ(a)} |f|`.
* `IsStarNormal.inner_bfc`: `⟪x, f(a) y⟫ = ∫ f dE_{x,y}`.
* `IsStarNormal.commute_bfc`: an operator commuting with `a` and `a⋆` commutes with `f(a)`.
* `IsStarNormal.tendsto_bfc_apply`: the bounded convergence theorem, if `fᵢ → g` pointwise on
  `σ(a)` with `|fᵢ| ≤ C`, then `fᵢ(a) → g(a)` in the strong operator topology.
* `IsStarNormal.bfc_mem_vonNeumannAlgebra`: `f(a)` lies in every von Neumann algebra containing `a`.

## Implementation notes

The generic names `bfc` / `bfcHom` (without namespace, in the style of `cfc` / `cfcHom`) are
reserved for an abstract Borel functional calculus class, of which this would be the instance for
`H →L[ℂ] H`. The `*`-homomorphism on `L^∞(E)` is `ha.spectralMeasure.integral`.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap Filter Topology
open scoped InnerProductSpace MeasureTheory.ComplexMeasure ENNReal

namespace IsStarNormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsStarNormal a) {f g : ℂ → ℂ}

open Classical in
/-- The Borel functional calculus `f(a) = ∫ f dE` of a normal operator `a` with spectral
measure `E`. It is `0` if the restriction of `f` to `σ(a)` is not in `L^∞(E)`. -/
noncomputable def bfc (f : ℂ → ℂ) : H →L[ℂ] H :=
  if hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure then
    ha.spectralMeasure.integral (hf.toLp _)
  else 0

lemma bfc_eq_integral (hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure) :
    ha.bfc f = ha.spectralMeasure.integral (hf.toLp _) := by
  simp [bfc, hf]

lemma bfc_eq_integral_of_eq {F : spectrum ℂ a → ℂ} (hF : MemLp F ∞ ha.spectralMeasure.measure)
    (h : (fun z : spectrum ℂ a ↦ f z) = F) :
    ha.bfc f = ha.spectralMeasure.integral (hF.toLp F) := by
  subst h
  exact ha.bfc_eq_integral hF

lemma bfc_of_not_memLp (hf : ¬MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure) :
    ha.bfc f = 0 := by
  simp [bfc, hf]

/-- A function which is measurable and bounded on `σ(a)` is in `L^∞(E)`. -/
lemma memLp_of_bound (hf : Measurable f) {C : ℝ} (hC : ∀ z ∈ spectrum ℂ a, ‖f z‖ ≤ C) :
    MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure :=
  memLp_top_of_bound (hf.comp measurable_subtype_coe).aestronglyMeasurable C
    (ae_of_all _ fun z ↦ hC z z.2)

/-- `f(a)` only depends on `f` up to `E`-null sets. -/
lemma bfc_congr_ae
    (h : (fun z : spectrum ℂ a ↦ f z) =ᵐ[ha.spectralMeasure.measure] fun z ↦ g z) :
    ha.bfc f = ha.bfc g := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral (hf.ae_eq h), MemLp.toLp_congr _ _ h]
  · rw [ha.bfc_of_not_memLp hf, ha.bfc_of_not_memLp fun hg ↦ hf (hg.ae_eq h.symm)]

lemma bfc_congr (h : Set.EqOn f g (spectrum ℂ a)) : ha.bfc f = ha.bfc g :=
  ha.bfc_congr_ae (ae_of_all _ fun z ↦ h z.2)

/-- The Borel functional calculus extends the continuous functional calculus (Rudin 12.22 (a)). -/
theorem bfc_eq_cfc (hf : ContinuousOn f (spectrum ℂ a)) : ha.bfc f = cfc f a := by
  rw [cfc_apply f a ha hf, ha.bfc_eq_integral_of_eq
    (ha.spectralMeasure.memLp_continuousMap ⟨_, hf.domRestrict⟩) rfl, integral_spectralMeasure_toLp]

@[simp]
lemma bfc_id : ha.bfc id = a := by
  rw [ha.bfc_eq_cfc continuousOn_id, cfc_id ℂ a]

@[simp]
lemma bfc_id' : ha.bfc (fun z ↦ z) = a :=
  ha.bfc_id

@[simp]
lemma bfc_star_id : ha.bfc (star · : ℂ → ℂ) = star a := by
  rw [ha.bfc_eq_cfc continuous_star.continuousOn, cfc_star_id a]

@[simp]
lemma bfc_const (c : ℂ) : ha.bfc (fun _ ↦ c) = algebraMap ℂ (H →L[ℂ] H) c := by
  rw [ha.bfc_eq_cfc continuousOn_const, cfc_const c a]

@[simp]
lemma bfc_one : ha.bfc 1 = 1 := by
  rw [ha.bfc_eq_cfc (f := 1) continuousOn_const, cfc_one ℂ a]

@[simp]
lemma bfc_const_one : ha.bfc (fun _ ↦ 1) = 1 :=
  ha.bfc_one

@[simp]
lemma bfc_zero : ha.bfc 0 = 0 := by
  rw [ha.bfc_eq_cfc (f := 0) continuousOn_const, cfc_zero ℂ a]

@[simp]
lemma bfc_const_zero : ha.bfc (fun _ ↦ 0) = 0 :=
  ha.bfc_zero

variable (hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure)
include hf

lemma bfc_add (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ f z + g z) = ha.bfc f + ha.bfc g := by
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg, ← map_add, ← MemLp.toLp_add,
    ha.bfc_eq_integral_of_eq (hf.add hg) rfl]

lemma bfc_sub (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ f z - g z) = ha.bfc f - ha.bfc g := by
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg, ← map_sub, ← MemLp.toLp_sub,
    ha.bfc_eq_integral_of_eq (hf.sub hg) rfl]

lemma bfc_neg : ha.bfc (fun z ↦ -f z) = -ha.bfc f := by
  rw [ha.bfc_eq_integral hf, ← map_neg, ← MemLp.toLp_neg, ha.bfc_eq_integral_of_eq hf.neg rfl]

lemma bfc_smul (c : ℂ) : ha.bfc (fun z ↦ c • f z) = c • ha.bfc f := by
  rw [ha.bfc_eq_integral hf, ← map_smul, ← MemLp.toLp_const_smul,
    ha.bfc_eq_integral_of_eq (hf.const_smul c) rfl]

lemma bfc_mul (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ f z * g z) = ha.bfc f * ha.bfc g := by
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg, ← map_mul, ← Linfty.toLp_mul,
    ha.bfc_eq_integral_of_eq (hf.mul hg) rfl]

lemma bfc_star : ha.bfc (fun z ↦ star (f z)) = star (ha.bfc f) := by
  rw [ha.bfc_eq_integral hf, ← map_star, ← MemLp.toLp_star, ha.bfc_eq_integral_of_eq hf.star rfl]

/-- `‖f(a)‖ = ‖f‖_{L^∞(E)}`. -/
lemma norm_bfc : ‖ha.bfc f‖ = ‖hf.toLp _‖ := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.norm_integral]

/-- `⟪x, f(a) y⟫ = ∫ f dE_{x,y}` (Rudin 12.21 (1)). -/
lemma inner_bfc (x y : H) : ⟪x, ha.bfc f y⟫_ℂ = ∫ᶜ z, f z ∂(ha.cfcMeasure x y) := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.inner_integral,
    toComplexMeasure_spectralMeasure]
  refine VectorMeasure.integral_congr_ae ?_
  rw [← toComplexMeasure_spectralMeasure]
  exact (ha.spectralMeasure.variation_toComplexMeasure_absolutelyContinuous x y).ae_le
    hf.coeFn_toLp

/-- `‖f(a) x‖² = ∫ |f|² dE_{x,x}` (Rudin 12.21 (2)). -/
lemma norm_bfc_apply_sq (x : H) :
    ‖ha.bfc f x‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂(ha.spectralMeasure.toMeasure x) := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.norm_integral_apply_sq_eq_integral]
  refine integral_congr_ae ((ha.spectralMeasure.toMeasure_absolutelyContinuous x).ae_le ?_)
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

omit hf

/-- `‖f(a)‖ ≤ C` if `|f| ≤ C` on `σ(a)`. -/
lemma norm_bfc_le {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ z ∈ spectrum ℂ a, ‖f z‖ ≤ C) :
    ‖ha.bfc f‖ ≤ C := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [ha.norm_bfc hf]
    refine Lp.norm_le_of_ae_bound_top hC₀ ?_
    filter_upwards [hf.coeFn_toLp] with z hz
    rw [hz]
    exact hC z z.2
  · rwa [ha.bfc_of_not_memLp hf, norm_zero]

/-- The indicator function of a measurable set `s` gives the spectral projection `E(s ∩ σ(a))`. -/
@[simp]
theorem bfc_indicator {s : Set ℂ} (hs : MeasurableSet s) :
    ha.bfc (s.indicator 1) = ha.spectralMeasure (Subtype.val ⁻¹' s) := by
  let F := (SimpleFunc.const (spectrum ℂ a) (1 : ℂ)).piecewise _ (measurable_subtype_coe hs)
    (SimpleFunc.const _ 0)
  rw [ha.bfc_eq_integral_of_eq (F.memLp_top _) ?_, ProjectionValuedMeasure.integral_toLp,
    ProjectionValuedMeasure.simpleIntegral_indicator]
  funext z
  by_cases hz : (z : ℂ) ∈ s <;> simp [F, hz]

/-- An operator commuting with `a` and `a⋆` commutes with `f(a)`. -/
theorem commute_bfc {S : H →L[ℂ] H} (h₁ : Commute S a) (h₂ : Commute S (star a)) (f : ℂ → ℂ) :
    Commute S (ha.bfc f) := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [ha.bfc_eq_integral hf]
    exact ha.spectralMeasure.commute_integral_of_forall_commute
      ((ha.forall_commute_spectralMeasure_iff).2 ⟨h₁, h₂⟩) _
  · rw [ha.bfc_of_not_memLp hf]
    exact Commute.zero_right S

lemma commute_bfc_bfc (f g : ℂ → ℂ) : Commute (ha.bfc f) (ha.bfc g) := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · by_cases hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure
    · rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg]
      exact ha.spectralMeasure.commute_integral _ _
    · rw [ha.bfc_of_not_memLp hg]
      exact Commute.zero_right _
  · rw [ha.bfc_of_not_memLp hf]
    exact Commute.zero_left _

/-- `f(a)` is normal. -/
instance isStarNormal_bfc (f : ℂ → ℂ) : IsStarNormal (ha.bfc f) := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [isStarNormal_iff, ← ha.bfc_star hf]
    exact ha.commute_bfc_bfc _ _
  · rw [ha.bfc_of_not_memLp hf]
    exact .zero

/-- The bounded convergence theorem: if `fᵢ → g` pointwise on `σ(a)` with `|fᵢ| ≤ C`, then
`fᵢ(a) x → g(a) x` for every `x`, i.e. `fᵢ(a) → g(a)` in the strong operator topology. -/
theorem tendsto_bfc_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {f : ι → ℂ → ℂ}
    (hf : ∀ i, MemLp (fun z : spectrum ℂ a ↦ f i z) ∞ ha.spectralMeasure.measure)
    (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure)
    {C : ℝ} (hC : ∀ᶠ i in l, ∀ z ∈ spectrum ℂ a, ‖f i z‖ ≤ C)
    (hlim : ∀ z ∈ spectrum ℂ a, Tendsto (f · z) l (𝓝 (g z))) (x : H) :
    Tendsto (fun i ↦ ha.bfc (f i) x) l (𝓝 (ha.bfc g x)) := by
  simp_rw [ha.bfc_eq_integral (hf _), ha.bfc_eq_integral hg]
  exact ha.spectralMeasure.tendsto_integral_toLp_apply hf hg
    (hC.mono fun i hi ↦ ae_of_all _ fun z ↦ hi z z.2) (ae_of_all _ fun z ↦ hlim z z.2) x

/-- `f(a)` lies in every von Neumann algebra containing `a`. -/
theorem bfc_mem_vonNeumannAlgebra {M : VonNeumannAlgebra H} (haM : a ∈ M) (f : ℂ → ℂ) :
    ha.bfc f ∈ M := by
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  intro S hS
  have h₁ : Commute S a := (hS a haM).symm
  have h₂ : Commute S (star a) := (hS _ (star_mem haM)).symm
  exact (ha.commute_bfc h₁ h₂ f).eq

end IsStarNormal
