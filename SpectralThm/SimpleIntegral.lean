/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.Resolutions

/-!
# Integral of simple functions against a resolution of the identity

For a resolution of the identity `E` and a simple function `s = ∑ a • 𝟙_{s⁻¹{a}}`, define
`Ψ(s) = ∑ a • E (s ⁻¹' {a})` (Rudin, *Functional Analysis*, proof of 12.21). This is a unital
`*`-homomorphism from simple functions to `H →L[ℂ] H`, it only depends on the class of `s` modulo
`E`-null sets, and `‖Ψ(s)‖ = ‖s‖_∞`. It is the starting point of the construction of
`Ψ : L^∞(E) → H →L[ℂ] H`.

## Main definitions

* `ResolutionOfIdentity.weightedSMul`: the set function `w ↦ (c ↦ c • E w)`.
* `ResolutionOfIdentity.simpleIntegral`: `Ψ` as a `StarAlgHom` from simple functions.

## Main results

* `ResolutionOfIdentity.simpleIntegral_apply`: `Ψ(s) = ∑ a ∈ s.range, a • E (s ⁻¹' {a})`.
* `ResolutionOfIdentity.simpleIntegral_congr_ae`: `Ψ(s)` only depends on the `E`-a.e. class of `s`.
* `ResolutionOfIdentity.inner_simpleIntegral`: `⟪x, Ψ(s) y⟫ = ∑ a * E_{x,y}(s ⁻¹' {a})`.
* `ResolutionOfIdentity.norm_simpleIntegral_apply_sq`: `‖Ψ(s) x‖² = ∑ ‖a‖² ‖E (s ⁻¹' {a}) x‖²`.
* `ResolutionOfIdentity.norm_simpleIntegral`: `‖Ψ(s)‖ = ‖s‖_∞`.

## Implementation notes

`Ψ` is defined with Mathlib's `SimpleFunc.setToSimpleFunc`, which gives additivity and
well-definedness from finite additivity of `E`. These lemmas are stated relative to a measure `μ`
and require `FinMeasAdditive μ T` and integrability with respect to `μ`; we use the zero measure,
for which both hold trivially since `E` is additive on all measurable sets.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

namespace ResolutionOfIdentity

variable {X : Type*} {mX : MeasurableSpace X}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ResolutionOfIdentity X H)

/-- The set function `w ↦ (c ↦ c • E w)`, analogous to `MeasureTheory.weightedSMul`. -/
noncomputable def weightedSMul (w : Set X) : ℂ →L[ℝ] H →L[ℂ] H :=
  (ContinuousLinearMap.id ℝ ℂ).smulRight (E w)

@[simp]
lemma weightedSMul_apply (w : Set X) (c : ℂ) : E.weightedSMul w c = c • E w := rfl

lemma weightedSMul_empty : E.weightedSMul ∅ = 0 := by
  ext; simp [apply, E.empty']

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
  · simp [(SimpleFunc.preimage_eq_empty_iff _ _).2 hp, apply, E.empty']
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
      apply, E.univ']
  map_mul' s t := by
    have hst : s * t = (s.pair t).map fun p ↦ p.1 * p.2 := SimpleFunc.ext fun _ ↦ rfl
    simp only [hst, E.setToSimpleFunc_pair_map s t (g := fun p ↦ p.1 * p.2) (by simp)]
    simp only [SimpleFunc.setToSimpleFunc, weightedSMul_apply, Finset.sum_mul_sum, smul_mul_smul,
      ← E.apply_inter (SimpleFunc.measurableSet_fiber _ _) (SimpleFunc.measurableSet_fiber _ _)]
  commutes' c := by
    change (algebraMap ℂ (SimpleFunc X ℂ) c).setToSimpleFunc _ = _
    rw [← SimpleFunc.const_algebraMap, SimpleFunc.setToSimpleFunc_const _ E.weightedSMul_empty,
      weightedSMul_apply, apply, E.univ', Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one]
  map_star' s := by
    rw [show star s = s.map star from rfl, E.setToSimpleFunc_map s (star_zero _)]
    have h (w : Set X) : star (E w) = E w := (E.IsStarProjection' w).isSelfAdjoint.star_eq
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
@[simp]
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
  have hp : IsStarProjection (E (s ⁻¹' {a})) := E.IsStarProjection' _
  by_cases ha : a ∈ s.range
  · rw [simpleIntegral_apply_apply, Finset.sum_eq_single_of_mem a ha fun b _ hba ↦ ?_,
      ← mul_apply_eq_comp, hp.isIdempotentElem.eq]
    rw [← mul_apply_eq_comp, E.mul_eq_zero_of_disjoint ((Set.disjoint_singleton.2 hba).preimage s),
      zero_apply, smul_zero]
  · simp [(SimpleFunc.preimage_eq_empty_iff _ _).2 ha, apply, E.empty']

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

end ResolutionOfIdentity
