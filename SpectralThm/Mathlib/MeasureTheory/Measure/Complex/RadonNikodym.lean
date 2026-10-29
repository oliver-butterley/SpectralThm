/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import SpectralThm.Mathlib.MeasureTheory.Measure.Complex.Integral

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Radon–Nikodym derivatives and the polar decomposition of complex measures

## Main results

* `MeasureTheory.ComplexMeasure.withDensityᵥ_rnDeriv_eq`: if `c ≪ μ` then `c = (dc/dμ) μ`
  (the complex analogue of `MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq`).
* `MeasureTheory.ComplexMeasure.withDensityᵥ_variation_rnDeriv_eq`: `μ = (dμ/d|μ|) |μ|`.
* `MeasureTheory.ComplexMeasure.ae_norm_rnDeriv_variation_eq_one`: `‖dμ/d|μ|‖ = 1` `|μ|`-a.e.
  (polar decomposition, [Rudin RCA 6.12]).
* `MeasureTheory.ComplexMeasure.integral_withDensityᵥ`: `∫ f d(k ν) = ∫ k f dν`.
* `MeasureTheory.ComplexMeasure.integral_eq_integral_rnDeriv`: `∫ f dμ = ∫ (dμ/d|μ|) f d|μ|`
  [Rudin RCA 6.18].
* `MeasureTheory.Measure.integral_rnDeriv_mul_of_le`: if `m ≤ ν` then `∫ (dm/dν) g dν = ∫ g dm`
  for complex-valued `g`.

## References

* Section 6 of [Walter Rudin, Real and Complex Analysis.][Rud87]
-/

@[expose] public section

open ENNReal NNReal
open scoped MeasureTheory.ComplexMeasure

namespace MeasureTheory.ComplexMeasure

variable {X : Type*} {mX : MeasurableSpace X}

/-- Two complex measures are equal if their real and imaginary parts are. -/
theorem ext {μ ν : ComplexMeasure X} (hre : μ.re = ν.re) (him : μ.im = ν.im) : μ = ν :=
  equivSignedMeasure.injective <| by simp [hre, him]

theorem ext_iff {μ ν : ComplexMeasure X} : μ = ν ↔ μ.re = ν.re ∧ μ.im = ν.im :=
  ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun h ↦ ext h.1 h.2⟩

/-- The real part of `f μ` is `(re ∘ f) μ`. -/
theorem re_withDensityᵥ {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    ComplexMeasure.re (μ.withDensityᵥ f) = μ.withDensityᵥ (Complex.re ∘ f) := by
  ext E hE
  rw [ComplexMeasure.re_apply,
    MeasureTheory.VectorMeasure.mapRange_apply (μ.withDensityᵥ f) Complex.continuous_re,
    MeasureTheory.withDensityᵥ_apply hf hE, LinearMap.toAddMonoidHom_coe, Complex.reLm_coe,
    ← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hf.integrableOn,
    MeasureTheory.withDensityᵥ_apply (f := Complex.re ∘ f)
      (Complex.reCLM.integrable_comp hf) hE]
  simp

/-- The imaginary part of `f μ` is `(im ∘ f) μ`. -/
theorem im_withDensityᵥ {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    ComplexMeasure.im (μ.withDensityᵥ f) = μ.withDensityᵥ (Complex.im ∘ f) := by
  ext E hE
  rw [ComplexMeasure.im_apply,
    MeasureTheory.VectorMeasure.mapRange_apply (μ.withDensityᵥ f) Complex.continuous_im,
    MeasureTheory.withDensityᵥ_apply hf hE, LinearMap.toAddMonoidHom_coe, Complex.imLm_coe,
    ← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hf.integrableOn,
    MeasureTheory.withDensityᵥ_apply (f := Complex.im ∘ f)
      (Complex.imCLM.integrable_comp hf) hE]
  simp

theorem re_comp_rnDeriv (c : ComplexMeasure X) (μ : Measure X) :
    Complex.re ∘ c.rnDeriv μ = c.re.rnDeriv μ :=
  rfl

theorem im_comp_rnDeriv (c : ComplexMeasure X) (μ : Measure X) :
    Complex.im ∘ c.rnDeriv μ = c.im.rnDeriv μ :=
  rfl

/-- **Radon–Nikodym theorem** for complex measures: if `c ≪ μ` then `c = (dc/dμ) μ`. -/
theorem withDensityᵥ_rnDeriv_eq (c : ComplexMeasure X) (μ : Measure X) [SigmaFinite μ]
    (h : c ≪ᵥ μ.toENNRealVectorMeasure) :
    μ.withDensityᵥ (c.rnDeriv μ) = c := by
  have h' := (absolutelyContinuous_ennreal_iff c _).mp h
  apply ComplexMeasure.ext
  · rw [re_withDensityᵥ (ComplexMeasure.integrable_rnDeriv c μ), re_comp_rnDeriv]
    exact MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ h'.1
  · rw [im_withDensityᵥ (ComplexMeasure.integrable_rnDeriv c μ), im_comp_rnDeriv]
    exact MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ h'.2

/-- A complex measure has density `dμ/d|μ|` with respect to its variation. -/
theorem withDensityᵥ_variation_rnDeriv_eq (μ : ComplexMeasure X) :
    μ.variation.withDensityᵥ (μ.rnDeriv μ.variation) = μ :=
  withDensityᵥ_rnDeriv_eq _ _ <| VectorMeasure.absolutelyContinuous μ

/-- **Polar decomposition** of a complex measure [Rudin RCA 6.12]: the density `dμ/d|μ|` has
norm one `|μ|`-almost everywhere. -/
theorem ae_norm_rnDeriv_variation_eq_one (μ : ComplexMeasure X) :
    ∀ᵐ x ∂μ.variation, ‖μ.rnDeriv μ.variation x‖ = 1 := by
  have hDensity := congrArg VectorMeasure.variation (withDensityᵥ_variation_rnDeriv_eq μ)
  rw [Measure.variation_withDensityᵥ (ComplexMeasure.integrable_rnDeriv μ μ.variation)]
    at hDensity
  have henorm : (fun x ↦ ‖μ.rnDeriv μ.variation x‖ₑ) =ᵐ[μ.variation] 1 := by
    apply (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (ComplexMeasure.integrable_rnDeriv μ μ.variation).aestronglyMeasurable.enorm
      aemeasurable_const).mp
    simpa using hDensity
  filter_upwards [henorm] with x h
  simpa [← ofReal_norm, Pi.one_apply, ofReal_eq_one] using h

/-- The integral against the complex measure `ν.withDensityᵥ k` (i.e. `dμ = k dν`) is
`∫ k f dν`. -/
theorem integral_withDensityᵥ {ν : Measure X} {k : X → ℂ} (hk : Integrable k ν) {f : X → ℂ}
    (hf : Integrable f (ν.withDensityᵥ k).variation) :
    ∫ᶜ x, f x ∂(ν.withDensityᵥ k) = ∫ x, k x * f x ∂ν := by
  have hρ : (ν.withDensityᵥ k).variation = ν.withDensity fun x ↦ (‖k x‖₊ : ℝ≥0∞) :=
    Measure.variation_withDensityᵥ hk
  have hkm : AEMeasurable (fun x ↦ ‖k x‖₊) ν := hk.aestronglyMeasurable.nnnorm.aemeasurable
  have hmul {g : X → ℂ} (hg : Integrable g (ν.withDensityᵥ k).variation) :
      Integrable (fun x ↦ k x * g x) ν := by
    rw [hρ] at hg
    exact hg.mul_of_withDensity_enorm hk.aestronglyMeasurable
  have hdist {g : X → ℂ} (hg : Integrable g (ν.withDensityᵥ k).variation) :
      ‖∫ x, k x * g x ∂ν‖ ≤ ∫ x, ‖g x‖ ∂(ν.withDensityᵥ k).variation := by
    rw [hρ, integral_withDensity_eq_integral_smul₀ hkm]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
    filter_upwards with x
    simp [NNReal.smul_def]
  refine hf.induction (P := fun f ↦ ∫ᶜ x, f x ∂(ν.withDensityᵥ k) = ∫ x, k x * f x ∂ν)
    ?_ ?_ ?_ ?_
  · intro c s hs _
    have h : (fun x ↦ k x * s.indicator (fun _ ↦ c) x) = s.indicator (fun x ↦ k x * c) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [VectorMeasure.integral_indicator_const _ hs, h, integral_indicator hs, integral_mul_const,
      ← withDensityᵥ_apply hk hs, mul_comm]
    rfl
  · intro f g _ hf hg hPf hPg
    simp only [Pi.add_apply, mul_add]
    rw [VectorMeasure.integral_fun_add hf hg, integral_add (hmul hf) (hmul hg), hPf, hPg]
  · refine isClosed_eq VectorMeasure.continuous_integral ?_
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun g h ↦ ?_)
    have hg := L1.integrable_coeFn g
    have hh := L1.integrable_coeFn h
    rw [dist_eq_norm, ← integral_sub (hmul hg) (hmul hh), NNReal.coe_one, one_mul, dist_eq_norm,
      L1.norm_eq_integral_norm]
    calc ‖∫ x, k x * g x - k x * h x ∂ν‖ = ‖∫ x, k x * (⇑g - ⇑h) x ∂ν‖ := by
          simp [mul_sub]
      _ ≤ ∫ x, ‖(⇑g - ⇑h) x‖ ∂(ν.withDensityᵥ k).variation := hdist (hg.sub hh)
      _ = _ := integral_congr_ae <| by
          filter_upwards [Lp.coeFn_sub g h] with x hx
          rw [hx]
  · intro f g hfg _ hPf
    rw [← VectorMeasure.integral_congr_ae hfg, hPf]
    rw [hρ, Filter.EventuallyEq, ae_withDensity_iff' hkm.coe_nnreal_ennreal] at hfg
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rcases eq_or_ne (k x) 0 with h | h
    · simp [h]
    · rw [hx (by simpa using h)]

/-- The integral against a complex measure in terms of its polar decomposition [Rudin RCA 6.18]:
`∫ f dμ = ∫ (dμ/d|μ|) f d|μ|`. -/
theorem integral_eq_integral_rnDeriv (μ : ComplexMeasure X) {f : X → ℂ}
    (hf : Integrable f μ.variation) :
    ∫ᶜ x, f x ∂μ = ∫ x, μ.rnDeriv μ.variation x * f x ∂μ.variation := by
  have h := withDensityᵥ_variation_rnDeriv_eq μ
  conv_lhs => rw [← h]
  exact integral_withDensityᵥ (integrable_rnDeriv μ μ.variation) (by rwa [h])

end MeasureTheory.ComplexMeasure

namespace MeasureTheory.Measure

variable {X : Type*} {mX : MeasurableSpace X} {ν m : Measure X} [IsFiniteMeasure ν]

/-- If `m ≤ ν` then `(dm/dν) g` is `ν`-integrable for any `m`-integrable `g`. -/
lemma integrable_rnDeriv_mul_of_le (h : m ≤ ν) {g : X → ℂ} (hg : Integrable g m) :
    Integrable (fun x ↦ ((m.rnDeriv ν x).toReal : ℂ) * g x) ν := by
  have : IsFiniteMeasure m := isFiniteMeasure_of_le ν h
  simpa [Complex.real_smul] using
    (integrable_rnDeriv_smul_iff (Measure.absolutelyContinuous_of_le h)).mpr hg

/-- If `m ≤ ν` then `∫ (dm/dν) g dν = ∫ g dm`. -/
lemma integral_rnDeriv_mul_of_le (h : m ≤ ν) (g : X → ℂ) :
    ∫ x, ((m.rnDeriv ν x).toReal : ℂ) * g x ∂ν = ∫ x, g x ∂m := by
  have : IsFiniteMeasure m := isFiniteMeasure_of_le ν h
  simpa [Complex.real_smul] using
    integral_rnDeriv_smul (Measure.absolutelyContinuous_of_le h) (f := g)

/-- If `m ≤ ν` then `dm/dν ∈ [0, 1]` `ν`-almost everywhere. -/
lemma toReal_rnDeriv_mem_Icc_of_le (h : m ≤ ν) :
    ∀ᵐ x ∂ν, (m.rnDeriv ν x).toReal ∈ Set.Icc 0 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le h] with x hx
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hx)⟩

end MeasureTheory.Measure
