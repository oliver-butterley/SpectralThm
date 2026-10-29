/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.ComplexMeasure.Integral

/-!
# Conjugate of a complex measure, and complex measures with density

## Main definitions

* `MeasureTheory.ComplexMeasure.conj`: the complex conjugate `s ↦ conj (μ s)` of a complex
  measure `μ`.

## Main results

* `MeasureTheory.ComplexMeasure.variation_conj`: `|conj μ| = |μ|`.
* `MeasureTheory.ComplexMeasure.integral_conj`: `∫ᶜ f d(conj μ) = conj (∫ᶜ conj f dμ)`.
* `MeasureTheory.ComplexMeasure.integral_withDensity`: `∫ᶜ g d(f dμ) = ∫ᶜ g f dμ`, where `f dμ`
  is `μ.withDensity f (ContinuousLinearMap.mul ℝ ℂ)`.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped MeasureTheory.ComplexMeasure ENNReal

variable {X : Type*} {mX : MeasurableSpace X}

namespace MeasureTheory.ComplexMeasure

/-! ### The conjugate of a complex measure -/

section Conj

variable (μ : ComplexMeasure X)

/-- The complex conjugate of a complex measure: the complex measure `s ↦ conj (μ s)`. -/
noncomputable def conj : ComplexMeasure X :=
  VectorMeasure.mapRangeL Complex.conjCLE.toContinuousLinearMap μ

@[simp]
lemma conj_apply (s : Set X) : μ.conj s = starRingEnd ℂ (μ s) := rfl

@[simp]
lemma conj_conj : μ.conj.conj = μ := by
  ext s hs
  simp

@[simp]
lemma variation_conj : μ.conj.variation = μ.variation := by
  have h (ν : ComplexMeasure X) : ν.conj.variation ≤ ν.variation :=
    VectorMeasure.variation_le_of_forall_enorm_le fun s _ ↦ by
      simpa using ν.enorm_measure_le_variation s
  exact le_antisymm (h μ) (by simpa using h μ.conj)

variable {μ} in
@[simp]
lemma integrable_conj_iff {f : X → ℂ} : μ.conj.Integrable f ↔ μ.Integrable f := by
  rw [VectorMeasure.Integrable, VectorMeasure.Integrable, variation_conj]

/-- Integrating against the conjugate measure: `∫ᶜ f d(conj μ) = conj (∫ᶜ conj f dμ)`. -/
theorem integral_conj (f : X → ℂ) :
    ∫ᶜ x, f x ∂μ.conj = starRingEnd ℂ (∫ᶜ x, starRingEnd ℂ (f x) ∂μ) := by
  let c : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  by_cases hf : μ.Integrable f
  swap
  · rw [VectorMeasure.integral_undef (integrable_conj_iff.not.2 hf), VectorMeasure.integral_undef,
      map_zero]
    exact fun h ↦ hf (by simpa [c] using c.integrable_comp h)
  have h₁ := VectorMeasure.continuousLinearMap_apply_integral (B := mul ℝ ℂ) (μ := μ) (C := c)
    (c.integrable_comp hf)
  have h₂ := VectorMeasure.integral_continuousLinearMap_comp
    (B := compL ℝ ℂ ℂ ℂ c ∘L mul ℝ ℂ) (μ := μ) (C := c) hf
  refine Eq.trans ?_ (h₂.symm.trans h₁.symm)
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  simp only [variation_conj]
  refine setToFun_congr_left' _ _ (fun s hs _ ↦ ?_) f
  ext z
  change z * starRingEnd ℂ (μ s) = starRingEnd ℂ (starRingEnd ℂ z * μ s)
  simp

end Conj

/-! ### Complex measures with density with respect to a complex measure -/

section WithDensity

variable {μ : ComplexMeasure X} {f g : X → ℂ}

/-- The variation of `f dμ` is `|f| d|μ|`. -/
lemma variation_withDensity (hf : μ.Integrable f) :
    (μ.withDensity f (mul ℝ ℂ)).variation = μ.variation.withDensity fun x ↦ ‖f x‖ₑ := by
  rw [VectorMeasure.variation_withDensity hf (by simp),
    VectorMeasure.variation_transpose_eq _ _ (by simp)]

/-- If `g` is integrable against `f dμ`, then `g f` is integrable against `μ`. -/
lemma integrable_mul_of_integrable_withDensity (hf : μ.Integrable f)
    (hg : (μ.withDensity f (mul ℝ ℂ)).Integrable g) : μ.Integrable fun x ↦ g x * f x := by
  have hfm : AEMeasurable (fun x ↦ ‖f x‖₊) μ.variation :=
    hf.aestronglyMeasurable.nnnorm.aemeasurable
  rw [VectorMeasure.Integrable, variation_withDensity hf] at hg
  simp_rw [enorm_eq_nnnorm] at hg
  rw [integrable_withDensity_iff_integrable_smul₀ hfm] at hg
  have hs : AEStronglyMeasurable (fun x ↦ f x / (‖f x‖ : ℂ)) μ.variation :=
    (hf.aemeasurable.div
      (Complex.measurable_ofReal.comp_aemeasurable hf.aemeasurable.norm)).aestronglyMeasurable
  refine (hg.bdd_mul (c := 1) hs (.of_forall fun x ↦ ?_)).congr (.of_forall fun x ↦ ?_)
  · simpa [norm_div] using div_self_le_one ‖f x‖
  · rcases eq_or_ne (f x) 0 with h | h
    · simp [h]
    · have : (‖f x‖ : ℂ) ≠ 0 := by simpa using h
      simp only [NNReal.smul_def, coe_nnnorm, Complex.real_smul]
      field_simp

/-- A bounded function which is a.e.-strongly measurable for `|μ|` is integrable against `f dμ`. -/
lemma integrable_withDensity_of_bound (hf : μ.Integrable f)
    (hg : AEStronglyMeasurable g μ.variation) (C : ℝ) (hgC : ∀ᵐ x ∂μ.variation, ‖g x‖ ≤ C) :
    (μ.withDensity f (mul ℝ ℂ)).Integrable g := by
  have hac : (μ.withDensity f (mul ℝ ℂ)).variation ≪ μ.variation := by
    rw [variation_withDensity hf]
    exact withDensity_absolutelyContinuous _ _
  exact .of_bound (hg.mono_ac hac) C (hac.ae_le hgC)

/-- Integrating against `f dμ`: `∫ᶜ g d(f dμ) = ∫ᶜ g f dμ`. -/
theorem integral_withDensity (hf : μ.Integrable f)
    (hg : (μ.withDensity f (mul ℝ ℂ)).Integrable g) :
    ∫ᶜ x, g x ∂(μ.withDensity f (mul ℝ ℂ)) = ∫ᶜ x, g x * f x ∂μ := by
  set ν := μ.withDensity f (mul ℝ ℂ)
  have hfm : AEMeasurable (fun x ↦ ‖f x‖₊) μ.variation :=
    hf.aestronglyMeasurable.nnnorm.aemeasurable
  have hρ : ν.variation = μ.variation.withDensity fun x ↦ (‖f x‖₊ : ℝ≥0∞) :=
    variation_withDensity hf
  have hmul {g : X → ℂ} (hg : ν.Integrable g) : μ.Integrable fun x ↦ g x * f x :=
    integrable_mul_of_integrable_withDensity hf hg
  have hnorm (k : X → ℂ) : ∫ x, ‖k x‖ ∂ν.variation = ∫ x, ‖k x * f x‖ ∂μ.variation := by
    rw [hρ, integral_withDensity_eq_integral_smul₀ hfm]
    congr with x
    simp [NNReal.smul_def, mul_comm]
  refine hg.induction (P := fun g ↦ ∫ᶜ x, g x ∂ν = ∫ᶜ x, g x * f x ∂μ) ?_ ?_ ?_ ?_
  · intro c s hs _
    have h : (fun x ↦ s.indicator (fun _ ↦ c) x * f x) = fun x ↦ c * s.indicator f x := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [VectorMeasure.integral_indicator_const _ hs, h, integral_const_mul,
      VectorMeasure.integral_indicator hs, VectorMeasure.withDensity_apply hf]
    rfl
  · intro g h _ hg hh hPg hPh
    simp only [Pi.add_apply, add_mul]
    rw [VectorMeasure.integral_fun_add hg hh, VectorMeasure.integral_fun_add (hmul hg) (hmul hh),
      hPg, hPh]
  · refine isClosed_eq VectorMeasure.continuous_integral ?_
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun g h ↦ ?_)
    have hg := L1.integrable_coeFn g
    have hh := L1.integrable_coeFn h
    rw [dist_eq_norm, ← VectorMeasure.integral_fun_sub (hmul hg) (hmul hh), NNReal.coe_one,
      one_mul, dist_eq_norm, L1.norm_eq_integral_norm]
    refine (norm_integral_le_integral_norm μ _).trans_eq ?_
    simp_rw [← sub_mul]
    refine (hnorm (⇑g - ⇑h)).symm.trans (integral_congr_ae ?_)
    filter_upwards [Lp.coeFn_sub g h] with x hx
    rw [hx]
  · intro g h hgh _ hPg
    rw [← VectorMeasure.integral_congr_ae hgh, hPg]
    rw [hρ, Filter.EventuallyEq, ae_withDensity_iff' hfm.coe_nnreal_ennreal] at hgh
    refine VectorMeasure.integral_congr_ae ?_
    filter_upwards [hgh] with x hx
    rcases eq_or_ne (f x) 0 with h | h
    · simp [h]
    · rw [hx (by simpa using h)]

end WithDensity

end MeasureTheory.ComplexMeasure
