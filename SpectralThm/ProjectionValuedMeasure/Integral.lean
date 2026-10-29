/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.ProjectionValuedMeasure.Basic
public import SpectralThm.ComplexMeasure.Operations
public import SpectralThm.Linfty.Spectrum

/-!
# Integral against a projection-valued measure

For a projection-valued measure `E` on `X` acting on `H`, we define the integral
`∫ f dE : H →L[ℂ] H` of functions `f ∈ L^∞(E)` (Rudin, *Functional Analysis*, 12.21, where it is
called `Ψ`). It is an isometric `*`-homomorphism `L^∞(E) → H →L[ℂ] H` with closed commutative
range.

The construction follows Mathlib's Bochner integral: on simple functions it is
`SimpleFunc.setToSimpleFunc` applied to `w ↦ (c ↦ c • E w)` (compare `SimpleFunc.integral`), and it
is extended to `L^∞(E)` by `MeasureTheory.setToLinfty`, the `L^∞` analogue of `setToL1`.

## Main definitions

* `ProjectionValuedMeasure.weightedSMul`: the set function `w ↦ (c ↦ c • E w)`.
* `ProjectionValuedMeasure.simpleIntegral`: the integral of simple functions, a `StarAlgHom`.
* `ProjectionValuedMeasure.integralCLM`: the integral as a continuous linear map on `L^∞(E)`.
* `ProjectionValuedMeasure.integral`: the integral as a `StarAlgHom` on `L^∞(E)`.

## Main results

* `ProjectionValuedMeasure.simpleIntegral_apply`: `∫ s dE = ∑ a ∈ s.range, a • E (s ⁻¹' {a})`.
* `ProjectionValuedMeasure.simpleIntegral_congr_ae`: `∫ s dE` only depends on the `E`-a.e. class
  of `s`.
* `ProjectionValuedMeasure.inner_simpleIntegral`: `⟪x, (∫ s dE) y⟫ = ∑ a * E_{x,y}(s ⁻¹' {a})`.
* `ProjectionValuedMeasure.norm_simpleIntegral_apply_sq`:
  `‖(∫ s dE) x‖² = ∑ ‖a‖² ‖E (s ⁻¹' {a}) x‖²`.
* `ProjectionValuedMeasure.norm_simpleIntegral`, `ProjectionValuedMeasure.norm_integral`:
  `‖∫ f dE‖ = ‖f‖_∞`; `lipschitzWith_integral_apply`: `f ↦ (∫ f dE) x` is `‖x‖`-Lipschitz.
* `ProjectionValuedMeasure.isClosed_range_integral`, `ProjectionValuedMeasure.commute_integral`:
  the range is closed and commutative.
* `ProjectionValuedMeasure.range_integralCLM_eq_topologicalClosure_span`: the range of the
  integral is the closure of the span of the projections `E w`.
* `ProjectionValuedMeasure.forall_commute_integral_iff`: an operator commutes with every
  `∫ f dE` iff it commutes with every `E w`.
* `ProjectionValuedMeasure.inner_integral`: `⟪x, (∫ f dE) y⟫ = ∫ f dE_{x,y}` (Rudin 12.21 (1)).
* `ProjectionValuedMeasure.norm_integral_apply_sq`: `‖(∫ f dE) x‖² = ∫ |f|² dE_{x,x}`
  (Rudin 12.21 (2)); `norm_integral_apply_sq_eq_integral` states it for the finite measure
  `E.toMeasure x`.
* `ProjectionValuedMeasure.spectrum_integral`, `spectrum_integral_eq_essRange`: the spectrum of
  `∫ f dE` is the spectrum of `f` in `L^∞(E)`, i.e. the essential range of `f`.
* `ProjectionValuedMeasure.tendsto_integral_toLp_apply`: the bounded convergence theorem, if
  `fᵢ → g` `E`-a.e. with `‖fᵢ‖ ≤ C` then `∫ fᵢ dE → ∫ g dE` in the strong operator topology.

## Implementation notes

`SimpleFunc.setToSimpleFunc` lemmas are stated relative to a measure `μ` and require
`FinMeasAdditive μ T` and integrability with respect to `μ`; we use the zero measure, for which
both hold trivially since `E` is additive on all measurable sets.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory.ComplexMeasure

namespace ProjectionValuedMeasure

variable {X : Type*} {mX : MeasurableSpace X}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ProjectionValuedMeasure X H)

/-- The set function `w ↦ (c ↦ c • E w)`, analogous to `MeasureTheory.weightedSMul`. -/
noncomputable def weightedSMul (w : Set X) : ℂ →L[ℝ] H →L[ℂ] H :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (E w)

@[simp]
lemma weightedSMul_apply (w : Set X) (c : ℂ) : E.weightedSMul w c = c • E w := rfl

lemma weightedSMul_empty : E.weightedSMul ∅ = 0 := by
  ext; simp

lemma finMeasAdditive_weightedSMul (μ : Measure X) : FinMeasAdditive μ E.weightedSMul :=
  fun _ _ h₁ h₂ _ _ h ↦ by ext c : 1; simp [E.apply_union h₁ h₂ h, smul_add]

private lemma setToSimpleFunc_map {β : Type*} [NormedAddCommGroup β] (s : SimpleFunc X β)
    {g : β → ℂ} (hg : g 0 = 0) :
    (s.map g).setToSimpleFunc E.weightedSMul = ∑ b ∈ s.range, g b • E (s ⁻¹' {b}) :=
  SimpleFunc.map_setToSimpleFunc _ (E.finMeasAdditive_weightedSMul 0) integrable_zero_measure
    hg

/-- A function of two simple functions `s`, `t` is integrated over the common refinement of their
fibres. -/
private lemma setToSimpleFunc_pair_map (s t : SimpleFunc X ℂ) {g : ℂ × ℂ → ℂ} (hg : g 0 = 0) :
    ((s.pair t).map g).setToSimpleFunc E.weightedSMul =
      ∑ a ∈ s.range, ∑ b ∈ t.range, g (a, b) • E (s ⁻¹' {a} ∩ t ⁻¹' {b}) := by
  classical
  rw [E.setToSimpleFunc_map _ hg, ← Finset.sum_product']
  refine (Finset.sum_subset (s₂ := s.range ×ˢ t.range) (fun p hp ↦ ?_) (fun p _ hp ↦ ?_)).trans
    (Finset.sum_congr rfl fun p _ ↦ ?_)
  · obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.1 hp
    exact Finset.mem_product.2 ⟨SimpleFunc.mem_range_self s x, SimpleFunc.mem_range_self t x⟩
  · simp [(SimpleFunc.preimage_eq_empty_iff _ _).2 hp]
  · rw [← SimpleFunc.pair_preimage_singleton]

/-- `Ψ(s) = ∑ a • E (s ⁻¹' {a})` for a simple function `s` (Rudin 12.21). It is a unital
`*`-homomorphism. -/
noncomputable def simpleIntegral : SimpleFunc X ℂ →⋆ₐ[ℂ] H →L[ℂ] H where
  toFun s := s.setToSimpleFunc E.weightedSMul
  map_zero' := SimpleFunc.setToSimpleFunc_zero_apply _
  map_add' s t := SimpleFunc.setToSimpleFunc_add _ (E.finMeasAdditive_weightedSMul 0)
    integrable_zero_measure integrable_zero_measure
  map_one' := by
    change (SimpleFunc.const X (1 : ℂ)).setToSimpleFunc _ = 1
    rw [SimpleFunc.setToSimpleFunc_const _ E.weightedSMul_empty, weightedSMul_apply, one_smul,
      apply_univ]
  map_mul' s t := by
    have hst : s * t = (s.pair t).map fun p ↦ p.1 * p.2 := SimpleFunc.ext fun _ ↦ rfl
    simp only [hst, E.setToSimpleFunc_pair_map s t (g := fun p ↦ p.1 * p.2) (by simp)]
    simp only [SimpleFunc.setToSimpleFunc, weightedSMul_apply, Finset.sum_mul_sum, smul_mul_smul,
      ← E.apply_inter (SimpleFunc.measurableSet_fiber _ _) (SimpleFunc.measurableSet_fiber _ _)]
  commutes' c := by
    change (algebraMap ℂ (SimpleFunc X ℂ) c).setToSimpleFunc _ = _
    rw [← SimpleFunc.const_algebraMap, SimpleFunc.setToSimpleFunc_const _ E.weightedSMul_empty,
      weightedSMul_apply, apply_univ, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one]
  map_star' s := by
    rw [show star s = s.map star from rfl, E.setToSimpleFunc_map s (star_zero _)]
    have h (w : Set X) : star (E w) = E w := (E.isStarProjection w).isSelfAdjoint.star_eq
    simp [SimpleFunc.setToSimpleFunc, star_sum, star_smul, h]

lemma simpleIntegral_apply (s : SimpleFunc X ℂ) :
    E.simpleIntegral s = ∑ a ∈ s.range, a • E (s ⁻¹' {a}) := rfl

lemma simpleIntegral_apply_apply (s : SimpleFunc X ℂ) (x : H) :
    E.simpleIntegral s x = ∑ a ∈ s.range, a • E (s ⁻¹' {a}) x := by
  simp [simpleIntegral_apply]

/-- `Ψ(g ∘ s) = ∑ g b • E (s ⁻¹' {b})`, for `g` with `g 0 = 0`. -/
lemma simpleIntegral_map {β : Type*} [NormedAddCommGroup β] (s : SimpleFunc X β) {g : β → ℂ}
    (hg : g 0 = 0) : E.simpleIntegral (s.map g) = ∑ b ∈ s.range, g b • E (s ⁻¹' {b}) :=
  E.setToSimpleFunc_map s hg

@[simp]
lemma simpleIntegral_const (c : ℂ) : E.simpleIntegral (SimpleFunc.const X c) = c • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one, ← E.simpleIntegral.commutes c]
  rfl

/-- `Ψ(𝟙_w) = E w`. -/
lemma simpleIntegral_indicator {w : Set X} (hw : MeasurableSet w) :
    E.simpleIntegral ((SimpleFunc.const X (1 : ℂ)).piecewise w hw (SimpleFunc.const X 0)) =
      E w := by
  rw [← one_smul ℂ (E w), ← weightedSMul_apply]
  exact SimpleFunc.setToSimpleFunc_indicator _ E.weightedSMul_empty hw 1

/-- `Ψ(s)` only depends on the class of `s` modulo `E`-null sets. -/
lemma simpleIntegral_congr_ae {s t : SimpleFunc X ℂ} (h : s =ᵐ[E.measure] t) :
    E.simpleIntegral s = E.simpleIntegral t := by
  refine SimpleFunc.setToSimpleFunc_congr' _ (E.finMeasAdditive_weightedSMul 0)
    integrable_zero_measure integrable_zero_measure fun a b hab ↦ ?_
  have hw := (SimpleFunc.measurableSet_fiber s a).inter (SimpleFunc.measurableSet_fiber t b)
  have h0 : E (s ⁻¹' {a} ∩ t ⁻¹' {b}) = 0 := by
    refine (E.measure_eq_zero_iff hw).1 (measure_mono_null ?_ (MeasureTheory.ae_iff.1 h))
    rintro z ⟨hza, hzb⟩ hst
    exact hab (hza.symm.trans (hst.trans hzb))
  ext c : 1
  simp [h0]

/-- `Ψ(s)` acts on the range of `E (s ⁻¹' {a})` as multiplication by `a`. -/
lemma simpleIntegral_apply_fiber (s : SimpleFunc X ℂ) (a : ℂ) (x : H) :
    E.simpleIntegral s (E (s ⁻¹' {a}) x) = a • E (s ⁻¹' {a}) x := by
  have hp := E.isStarProjection (s ⁻¹' {a})
  by_cases ha : a ∈ s.range
  · rw [simpleIntegral_apply_apply, Finset.sum_eq_single_of_mem a ha fun b _ hba ↦ ?_,
      ← mul_apply_eq_comp, hp.isIdempotentElem.eq]
    rw [← mul_apply_eq_comp, E.mul_eq_zero_of_disjoint ((Set.disjoint_singleton.2 hba).preimage s),
      zero_apply, smul_zero]
  · simp [(SimpleFunc.preimage_eq_empty_iff _ _).2 ha]

/-- `⟪x, Ψ(s) y⟫ = ∑ a * E_{x,y}(s ⁻¹' {a})`. -/
lemma inner_simpleIntegral (s : SimpleFunc X ℂ) (x y : H) :
    ⟪x, E.simpleIntegral s y⟫_ℂ = ∑ a ∈ s.range, a * E.toComplexMeasure x y (s ⁻¹' {a}) := by
  simp [simpleIntegral_apply_apply]

/-- `‖Ψ(s) x‖² = ∑ ‖a‖² ‖E (s ⁻¹' {a}) x‖²`. -/
lemma norm_simpleIntegral_apply_sq (s : SimpleFunc X ℂ) (x : H) :
    ‖E.simpleIntegral s x‖ ^ 2 = ∑ a ∈ s.range, ‖a‖ ^ 2 * ‖E (s ⁻¹' {a}) x‖ ^ 2 := by
  have hs : star s * s = s.map fun a ↦ ((‖a‖ ^ 2 : ℝ) : ℂ) :=
    SimpleFunc.ext fun z ↦ by simp [Complex.conj_mul']
  have h : ((‖E.simpleIntegral s x‖ ^ 2 : ℝ) : ℂ) = ⟪x, E.simpleIntegral (star s * s) x⟫_ℂ := by
    rw [map_mul, map_star, star_eq_adjoint, mul_apply_eq_comp, adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hs, E.simpleIntegral_map s (by simp), sum_apply, inner_sum] at h
  simp_rw [smul_apply, inner_smul_right, inner_apply_self] at h
  exact_mod_cast h

/-- `∑ ‖E (s ⁻¹' {a}) x‖² = ‖x‖²`: the fibres of `s` partition `X`. -/
lemma sum_norm_apply_fiber_sq (s : SimpleFunc X ℂ) (x : H) :
    ∑ a ∈ s.range, ‖E (s ⁻¹' {a}) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := s.sum_range_measure_preimage_singleton (E.toMeasure x)
  simp only [E.toMeasure_apply _ (s.measurableSet_fiber _), toMeasure_univ] at h
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ by positivity, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 h

/-- `‖Ψ(s)‖ = ‖s‖_∞` (Rudin 12.21 (14)). -/
lemma norm_simpleIntegral (s : SimpleFunc X ℂ) :
    ‖E.simpleIntegral s‖ = (eLpNorm s ∞ E.measure).toReal := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have hμ : E.measure = 0 := by
      rw [← Measure.measure_univ_eq_zero, E.measure_eq_zero_iff .univ]
      exact ContinuousLinearMap.ext fun _ ↦ Subsingleton.elim _ _
    have h0 : E.simpleIntegral s = 0 := ContinuousLinearMap.ext fun _ ↦ Subsingleton.elim _ _
    simp [hμ, h0]
  obtain ⟨a, ha, heq⟩ := E.exists_eLpNorm_top_eq s
  rw [heq, toReal_enorm]
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg a) fun x ↦ ?_) ?_
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [norm_simpleIntegral_apply_sq, mul_pow, ← E.sum_norm_apply_fiber_sq s x, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    by_cases hb : E (s ⁻¹' {b}) = 0
    · simp [hb]
    have hba : ‖b‖ₑ ≤ ‖a‖ₑ := by
      rw [← heq, E.eLpNorm_top_eq_iSup s]
      exact le_iSup₂ (f := fun b (_ : E (s ⁻¹' {b}) ≠ 0) ↦ ‖b‖ₑ) b hb
    gcongr
    exact enorm_le_iff_norm_le.1 hba
  · obtain ⟨y, hy⟩ : ∃ y, E (s ⁻¹' {a}) y ≠ 0 := by
      by_contra! h
      exact ha (ContinuousLinearMap.ext h)
    refine le_of_mul_le_mul_right ?_ (norm_pos_iff.2 hy)
    calc ‖a‖ * ‖E (s ⁻¹' {a}) y‖ = ‖E.simpleIntegral s (E (s ⁻¹' {a}) y)‖ := by
          rw [simpleIntegral_apply_fiber, norm_smul]
      _ ≤ ‖E.simpleIntegral s‖ * ‖E (s ⁻¹' {a}) y‖ := le_opNorm _ _

/-- If `Q` commutes with every `E w`, it commutes with every `Ψ(s)` (Rudin 12.21). -/
lemma commute_simpleIntegral {Q : H →L[ℂ] H} (h : ∀ w, Commute Q (E w)) (s : SimpleFunc X ℂ) :
    Commute Q (E.simpleIntegral s) := by
  rw [simpleIntegral_apply]
  exact Commute.sum_right _ _ _ fun a _ ↦ (h _).smul_right a

/-! ### The integral of `L^∞(E)` functions -/

lemma weightedSMul_smul (c : ℂ) (w : Set X) (z : ℂ) :
    E.weightedSMul w (c • z) = c • E.weightedSMul w z := by
  simp [mul_smul]

lemma dominatedLinftyAdditive_weightedSMul :
    DominatedLinftyAdditive E.measure E.weightedSMul 1 where
  add s t hs ht h := (E.finMeasAdditive_weightedSMul 0) s t hs ht (by simp) (by simp) h
  eq_zero_of_measure_zero w hw h := by
    ext c : 1
    simp [(E.measure_eq_zero_iff hw).1 h]
  norm_setToSimpleFunc_le s := (E.norm_simpleIntegral s).trans_le (one_mul _).symm.le

/-- The integral against `E` as a continuous linear map `L^∞(E) →L[ℂ] H →L[ℂ] H`. -/
noncomputable def integralCLM : E.Linfty →L[ℂ] H →L[ℂ] H :=
  setToLinfty ℂ E.dominatedLinftyAdditive_weightedSMul E.weightedSMul_smul

lemma integralCLM_eq_simpleIntegral {f : E.Linfty} {s : SimpleFunc X ℂ}
    (h : f =ᵐ[E.measure] s) : E.integralCLM f = E.simpleIntegral s := by
  rw [show f = (s.memLp_top _).toLp s from Lp.ext (h.trans (MemLp.coeFn_toLp _).symm)]
  exact setToLinfty_toLp _ _ s

lemma integralCLM_coe (f : Lp.simpleFunc ℂ ∞ E.measure) :
    E.integralCLM f = E.simpleIntegral (Lp.simpleFunc.toSimpleFunc f) :=
  E.integralCLM_eq_simpleIntegral (Lp.simpleFunc.toSimpleFunc_eq_toFun f).symm

/-- The integral against a projection-valued measure `E`, as a `*`-homomorphism
`L^∞(E) → H →L[ℂ] H` (Rudin 12.21, where it is called `Ψ`). It extends `E.simpleIntegral` and is
an isometry (`norm_integral`). -/
noncomputable def integral : E.Linfty →⋆ₐ[ℂ] H →L[ℂ] H where
  toFun := E.integralCLM
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by
    rw [E.integralCLM_eq_simpleIntegral (s := 1) Linfty.coeFn_one, map_one]
  map_mul' f g := by
    refine Lp.simpleFunc.denseRange_top.induction_on₂ (p := fun f g ↦
      E.integralCLM (f * g) = E.integralCLM f * E.integralCLM g) ?_ (fun a b ↦ ?_) f g
    · exact isClosed_eq (E.integralCLM.continuous.comp continuous_mul)
        ((E.integralCLM.continuous.comp continuous_fst).mul
          (E.integralCLM.continuous.comp continuous_snd))
    · rw [E.integralCLM_coe, E.integralCLM_coe, ← map_mul,
        E.integralCLM_eq_simpleIntegral]
      filter_upwards [Linfty.coeFn_mul (a : E.Linfty) b, Lp.simpleFunc.toSimpleFunc_eq_toFun a,
        Lp.simpleFunc.toSimpleFunc_eq_toFun b] with x h hx hy
      simp [h, hx, hy]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, E.integralCLM_eq_simpleIntegral (s := 1)
      Linfty.coeFn_one, map_one, Algebra.algebraMap_eq_smul_one]
  map_star' f := by
    refine Lp.simpleFunc.denseRange_top.induction_on (p := fun f ↦
      E.integralCLM (star f) = star (E.integralCLM f)) f ?_ fun a ↦ ?_
    · exact isClosed_eq (E.integralCLM.continuous.comp continuous_star)
        (continuous_star.comp E.integralCLM.continuous)
    · rw [E.integralCLM_coe, ← map_star, E.integralCLM_eq_simpleIntegral]
      filter_upwards [Lp.coeFn_star (a : E.Linfty), Lp.simpleFunc.toSimpleFunc_eq_toFun a]
        with x h hx
      simp [h, hx]

lemma integral_apply (f : E.Linfty) : E.integral f = E.integralCLM f := rfl

/-- On the class of a simple function, the integral is `E.simpleIntegral`. -/
lemma integral_eq_simpleIntegral {f : E.Linfty} {s : SimpleFunc X ℂ} (h : f =ᵐ[E.measure] s) :
    E.integral f = E.simpleIntegral s :=
  E.integralCLM_eq_simpleIntegral h

@[simp]
lemma integral_toLp (s : SimpleFunc X ℂ) :
    E.integral ((s.memLp_top E.measure).toLp s) = E.simpleIntegral s :=
  E.integral_eq_simpleIntegral (MemLp.coeFn_toLp _)

/-- The integral is an isometry: `‖∫ f dE‖ = ‖f‖_∞` (Rudin 12.21 (15)). -/
@[simp]
lemma norm_integral (f : E.Linfty) : ‖E.integral f‖ = ‖f‖ :=
  norm_setToLinfty_apply _ _ E.norm_simpleIntegral f

/-- `‖(∫ f dE) x‖ ≤ ‖f‖_∞ ‖x‖`. -/
lemma norm_integral_apply_le (f : E.Linfty) (x : H) : ‖E.integral f x‖ ≤ ‖f‖ * ‖x‖ :=
  E.norm_integral f ▸ (E.integral f).le_opNorm x

/-- For fixed `x`, `f ↦ (∫ f dE) x` is Lipschitz on `L^∞(E)` with constant `‖x‖`. -/
lemma lipschitzWith_integral_apply (x : H) :
    LipschitzWith ‖x‖₊ fun f : E.Linfty ↦ E.integral f x :=
  .of_dist_le_mul fun f g ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← sub_apply, ← map_sub, coe_nnnorm, mul_comm]
    exact E.norm_integral_apply_le _ x

lemma isometry_integral : Isometry E.integral :=
  AddMonoidHomClass.isometry_of_norm E.integral E.norm_integral

/-- The range of the integral is closed (Rudin 12.21). -/
lemma isClosed_range_integral : IsClosed (Set.range E.integral) :=
  E.isometry_integral.isClosedEmbedding.isClosed_range

/-- The range of the integral is commutative (Rudin 12.21). -/
lemma commute_integral (f g : E.Linfty) : Commute (E.integral f) (E.integral g) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

/-- If `Q` commutes with every `E w`, it commutes with every `∫ f dE` (Rudin 12.21). -/
lemma commute_integral_of_forall_commute {Q : H →L[ℂ] H} (h : ∀ w, Commute Q (E w))
    (f : E.Linfty) : Commute Q (E.integral f) := by
  refine Lp.simpleFunc.denseRange_top.induction_on (p := fun f ↦ Commute Q (E.integral f)) f
    (isClosed_eq (continuous_const.mul (E.integralCLM.continuous))
      ((E.integralCLM.continuous).mul continuous_const)) fun a ↦ ?_
  rw [E.integral_eq_simpleIntegral (Lp.simpleFunc.toSimpleFunc_eq_toFun a).symm]
  exact E.commute_simpleIntegral h _

/-- An operator commutes with every `∫ f dE` iff it commutes with every `E w` (Rudin 12.21). -/
lemma forall_commute_integral_iff {Q : H →L[ℂ] H} :
    (∀ f : E.Linfty, Commute Q (E.integral f)) ↔ ∀ w, Commute Q (E w) := by
  refine ⟨fun h w ↦ ?_, fun h f ↦ E.commute_integral_of_forall_commute h f⟩
  by_cases hw : MeasurableSet w
  · have := h ((((SimpleFunc.const X (1 : ℂ)).piecewise w hw (SimpleFunc.const X 0)).memLp_top
      E.measure).toLp _)
    rwa [integral_toLp, simpleIntegral_indicator] at this
  · simp [E.apply_of_not_measurableSet hw]

/-! ### The integral against the complex measures `E_{x,y}` -/

/-- An element of `L^∞(E)` is integrable with respect to `|E_{x,y}|`. -/
lemma integrable_toComplexMeasure (f : E.Linfty) (x y : H) :
    (E.toComplexMeasure x y).Integrable f :=
  .of_bound (Lp.stronglyMeasurable f).aestronglyMeasurable ‖f‖
    ((E.variation_toComplexMeasure_absolutelyContinuous x y).ae_le (Lp.ae_norm_le_norm f))

/-- `|∫ f dE_{x,y}| ≤ ‖f‖_∞ ‖x‖ ‖y‖`. -/
lemma norm_integral_toComplexMeasure_le (f : E.Linfty) (x y : H) :
    ‖∫ᶜ z, f z ∂(E.toComplexMeasure x y)‖ ≤ ‖f‖ * (‖x‖ * ‖y‖) := by
  refine (VectorMeasure.norm_integral_le_of_norm_le_const
    ((E.variation_toComplexMeasure_absolutelyContinuous x y).ae_le (Lp.ae_norm_le_norm f))).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖ContinuousLinearMap.mul ℝ ℂ‖ * (E.toComplexMeasure x y).variation.real Set.univ
      ≤ 1 * (‖x‖ * ‖y‖) := by
        gcongr
        · exact ContinuousLinearMap.opNorm_mul_le ℝ ℂ
        · refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
          rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
          exact E.variation_toComplexMeasure_univ_le x y
    _ = ‖x‖ * ‖y‖ := one_mul _

/-- `⟪x, (∫ f dE) y⟫ = ∫ f dE_{x,y}` (Rudin 12.21 (1)). -/
theorem inner_integral (f : E.Linfty) (x y : H) :
    ⟪x, E.integral f y⟫_ℂ = ∫ᶜ z, f z ∂(E.toComplexMeasure x y) := by
  have hae {u v : X → ℂ} (h : u =ᵐ[E.measure] v) : u =ᵐ[(E.toComplexMeasure x y).variation] v :=
    (E.variation_toComplexMeasure_absolutelyContinuous x y).ae_le h
  refine Lp.simpleFunc.denseRange_top.induction_on (p := fun f : E.Linfty ↦
    ⟪x, E.integral f y⟫_ℂ = ∫ᶜ z, f z ∂(E.toComplexMeasure x y)) f
    (isClosed_eq ?_ ?_) fun a ↦ ?_
  · exact continuous_const.inner
      ((ContinuousLinearMap.apply ℂ H y).continuous.comp E.integralCLM.continuous)
  · refine (LipschitzWith.of_dist_le_mul (K := ⟨‖x‖ * ‖y‖, by positivity⟩) fun f g ↦ ?_).continuous
    rw [dist_eq_norm, dist_eq_norm,
      ← VectorMeasure.integral_sub (E.integrable_toComplexMeasure f x y)
        (E.integrable_toComplexMeasure g x y),
      VectorMeasure.integral_congr_ae (hae (Lp.coeFn_sub f g)).symm, mul_comm]
    exact E.norm_integral_toComplexMeasure_le (f - g) x y
  · have h := Lp.simpleFunc.toSimpleFunc_eq_toFun a
    rw [E.integral_eq_simpleIntegral h.symm, inner_simpleIntegral,
      VectorMeasure.integral_congr_ae (hae h).symm, ComplexMeasure.integral_simpleFunc]

/-- `‖(∫ f dE) x‖² = ∫ |f|² dE_{x,x}` (Rudin 12.21 (2)). -/
theorem norm_integral_apply_sq (f : E.Linfty) (x : H) :
    ((‖E.integral f x‖ ^ 2 : ℝ) : ℂ) =
      ∫ᶜ z, ((‖f z‖ ^ 2 : ℝ) : ℂ) ∂(E.toComplexMeasure x x) := by
  have h : ((‖E.integral f x‖ ^ 2 : ℝ) : ℂ) = ⟪x, E.integral (star f * f) x⟫_ℂ := by
    rw [map_mul, map_star, star_eq_adjoint, mul_apply_eq_comp, adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h, inner_integral]
  refine VectorMeasure.integral_congr_ae
    ((E.variation_toComplexMeasure_absolutelyContinuous x x).ae_le ?_)
  filter_upwards [Linfty.coeFn_mul (star f) f, Lp.coeFn_star f] with z h₁ h₂
  simp [h₁, h₂, Complex.conj_mul']

/-- The range of the integral is the closure of the span of the projections `E w`
(Rudin 12.22 (c)). -/
theorem range_integralCLM_eq_topologicalClosure_span :
    LinearMap.range E.integralCLM.toLinearMap =
      (Submodule.span ℂ (Set.range E)).topologicalClosure := by
  refine le_antisymm ?_ (Submodule.topologicalClosure_minimal _ ?_ ?_)
  · rintro _ ⟨f, rfl⟩
    refine Lp.simpleFunc.denseRange_top.induction_on (p := fun f : E.Linfty ↦
      E.integralCLM f ∈ (Submodule.span ℂ (Set.range E)).topologicalClosure) f
      ((Submodule.isClosed_topologicalClosure _).preimage E.integralCLM.continuous) fun g ↦ ?_
    rw [E.integralCLM_coe, simpleIntegral_apply]
    exact Submodule.le_topologicalClosure _ (Submodule.sum_mem _ fun c _ ↦
      Submodule.smul_mem _ c (Submodule.subset_span ⟨_, rfl⟩))
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    by_cases hw : MeasurableSet w
    · refine ⟨((((SimpleFunc.const X (1 : ℂ)).piecewise w hw (SimpleFunc.const X 0)).memLp_top
        E.measure).toLp _), ?_⟩
      exact (E.integral_toLp _).trans (E.simpleIntegral_indicator hw)
    · rw [E.apply_of_not_measurableSet hw]
      exact zero_mem _
  · rw [LinearMap.coe_range]
    exact E.isClosed_range_integral

/-! ### The bounded convergence theorem -/

lemma toComplexMeasure_self (x : H) :
    E.toComplexMeasure x x = (E.toMeasure x).toComplexMeasure :=
  VectorMeasure.ext fun w hw ↦ by
    rw [toComplexMeasure_apply, Measure.toComplexMeasure_apply _ hw, measureReal_def,
      toMeasure_apply E w hw, ENNReal.toReal_ofReal (by positivity), inner_apply_self]
    push_cast
    rfl

/-- `‖(∫ f dE) x‖² = ∫ |f|² dE_{x,x}`, with `E_{x,x}` the finite measure `E.toMeasure x`. -/
theorem norm_integral_apply_sq_eq_integral (f : E.Linfty) (x : H) :
    ‖E.integral f x‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂(E.toMeasure x) := by
  have h := E.norm_integral_apply_sq f x
  rw [toComplexMeasure_self, Measure.integral_toComplexMeasure, integral_complex_ofReal] at h
  exact_mod_cast h

/-- The bounded convergence theorem: if `fᵢ → g` `E`-a.e. with `‖fᵢ‖ ≤ C`, then
`(∫ fᵢ dE) x → (∫ g dE) x` for every `x`, i.e. `∫ fᵢ dE → ∫ g dE` in the strong operator
topology. -/
theorem tendsto_integral_toLp_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → ℂ} {g : X → ℂ} (hf : ∀ i, MemLp (f i) ∞ E.measure) (hg : MemLp g ∞ E.measure)
    {C : ℝ} (hC : ∀ᶠ i in l, ∀ᵐ z ∂E.measure, ‖f i z‖ ≤ C)
    (hlim : ∀ᵐ z ∂E.measure, Tendsto (f · z) l (𝓝 (g z))) (x : H) :
    Tendsto (fun i ↦ E.integral ((hf i).toLp (f i)) x) l (𝓝 (E.integral (hg.toLp g) x)) := by
  set D := ‖hg.toLp g‖
  have hgD : ∀ᵐ z ∂E.measure, ‖g z‖ ≤ D := by
    filter_upwards [Lp.ae_norm_le_norm (hg.toLp g), hg.coeFn_toLp] with z h₁ h₂
    rwa [← h₂]
  have hac := E.toMeasure_absolutelyContinuous x
  have heq (i : ι) : ‖E.integral ((hf i).toLp (f i)) x - E.integral (hg.toLp g) x‖ ^ 2 =
      ∫ z, ‖f i z - g z‖ ^ 2 ∂(E.toMeasure x) := by
    rw [← sub_apply, ← map_sub, ← MemLp.toLp_sub, norm_integral_apply_sq_eq_integral]
    refine integral_congr_ae (hac.ae_le ?_)
    filter_upwards [((hf i).sub hg).coeFn_toLp] with z hz
    simp [hz]
  have hsq : Tendsto (fun i ↦ ∫ z, ‖f i z - g z‖ ^ 2 ∂(E.toMeasure x)) l
      (𝓝 (∫ z, ‖(0 : ℂ)‖ ^ 2 ∂(E.toMeasure x))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (C + D) ^ 2)
      (.of_forall fun i ↦
        (((hf i).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2).mono_ac hac)
      ?_ (integrable_const _) ?_
    · filter_upwards [hC] with i hi
      filter_upwards [hac.ae_le hi, hac.ae_le hgD] with z h₁ h₂
      rw [Real.norm_of_nonneg (by positivity)]
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add h₁ h₂)
    · filter_upwards [hac.ae_le hlim] with z hz
      simpa using (hz.sub_const (g z)).norm.pow 2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [← heq] using hsq.sqrt

/-! ### The spectrum -/

/-- The spectrum of `∫ f dE` is the spectrum of `f` in `L^∞(E)`, since the integral is an
injective `*`-homomorphism with closed range (spectral permanence). -/
theorem spectrum_integral (f : E.Linfty) : spectrum ℂ (E.integral f) = spectrum ℂ f := by
  have : IsClosed (E.integral.range : Set (H →L[ℂ] H)) := E.isClosed_range_integral
  rw [← AlgEquiv.spectrum_eq (StarAlgEquiv.ofInjective E.integral
    E.isometry_integral.injective) f, StarSubalgebra.spectrum_eq]
  rfl

/-- The spectrum of `∫ f dE` is the essential range of `f` with respect to `E`. -/
theorem spectrum_integral_eq_essRange (f : E.Linfty) :
    spectrum ℂ (E.integral f) = E.measure.essRange f := by
  rw [spectrum_integral, Linfty.spectrum_eq_essRange]

end ProjectionValuedMeasure

