/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.Mathlib.MeasureTheory.Measure.Complex.Integral

import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Operations on complex measures and the integral

## Main definitions

* `MeasureTheory.Measure.toComplexMeasure`: a finite measure as a complex measure.

## Main results

* `MeasureTheory.Measure.variation_toComplexMeasure`: its variation is the measure itself.
* `MeasureTheory.Measure.integral_toComplexMeasure`: `∫ᶜ f d(μ as a complex measure) = ∫ f dμ`.
* `MeasureTheory.ComplexMeasure.integral_smul_measure`: `∫ᶜ f d(c • μ) = c * ∫ᶜ f dμ` for `c : ℂ`.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap
open scoped MeasureTheory.ComplexMeasure ENNReal

variable {X : Type*} {mX : MeasurableSpace X}

namespace MeasureTheory.Measure

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- A finite measure as a complex measure. -/
noncomputable def toComplexMeasure : ComplexMeasure X :=
  VectorMeasure.mapRangeL Complex.ofRealCLM μ.toSignedMeasure

@[simp]
lemma toComplexMeasure_apply {s : Set X} (hs : MeasurableSet s) :
    μ.toComplexMeasure s = μ.real s := by
  simp [toComplexMeasure, VectorMeasure.mapRangeL, toSignedMeasure_apply_measurable hs]

/-- The variation of a finite measure seen as a complex measure is the measure itself. -/
@[simp]
lemma variation_toComplexMeasure : μ.toComplexMeasure.variation = μ := by
  have h {s : Set X} (hs : MeasurableSet s) : ‖μ.toComplexMeasure s‖ₑ = μ s := by
    rw [toComplexMeasure_apply μ hs, ← ofReal_norm, Complex.norm_real,
      Real.norm_of_nonneg measureReal_nonneg, ofReal_measureReal]
  refine le_antisymm (VectorMeasure.variation_le_of_forall_enorm_le fun s hs ↦ (h hs).le)
    (Measure.le_iff.2 fun s hs ↦ (h hs).symm.le.trans
      (μ.toComplexMeasure.enorm_measure_le_variation s))

/-- Integrating against a finite measure seen as a complex measure is the Bochner integral. -/
@[simp]
lemma integral_toComplexMeasure (f : X → ℂ) :
    ∫ᶜ x, f x ∂μ.toComplexMeasure = ∫ x, f x ∂μ := by
  rw [VectorMeasure.integral_eq_setToFun, MeasureTheory.integral_eq_setToFun]
  simp only [variation_toComplexMeasure]
  refine setToFun_congr_left' _ _ (fun s hs _ ↦ ?_) f
  ext z
  simp [weightedSMul_apply, transpose_eq_cbmApplyMeasure, toComplexMeasure_apply μ hs, mul_comm]

end MeasureTheory.Measure

namespace MeasureTheory.ComplexMeasure

/-- A function integrable against `μ` is integrable against `c • μ`. -/
lemma Integrable.smul_measure {μ : ComplexMeasure X} {f : X → ℂ} (h : μ.Integrable f) (c : ℂ) :
    (c • μ).Integrable f := by
  rw [VectorMeasure.Integrable, VectorMeasure.variation_smul]
  exact h.smul_measure ENNReal.coe_ne_top

/-- `∫ᶜ f d(c • μ) = c * ∫ᶜ f dμ` for `c : ℂ`. -/
lemma integral_smul_measure (c : ℂ) (μ : ComplexMeasure X) (f : X → ℂ) :
    ∫ᶜ x, f x ∂(c • μ) = c * ∫ᶜ x, f x ∂μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hvar : (c • μ).variation = ‖c‖₊ • μ.variation := VectorMeasure.variation_smul
  have hint {g : X → ℂ} : (c • μ).Integrable g ↔ μ.Integrable g := by
    rw [VectorMeasure.Integrable, VectorMeasure.Integrable, hvar]
    exact integrable_smul_measure (by simpa using hc) ENNReal.coe_ne_top
  have hae {g h : X → ℂ} (hgh : g =ᵐ[μ.variation] h) : g =ᵐ[(c • μ).variation] h := by
    rw [hvar]
    exact Measure.ae_smul_measure hgh _
  by_cases hf : μ.Integrable f
  swap
  · rw [VectorMeasure.integral_undef hf, VectorMeasure.integral_undef (hint.not.2 hf), mul_zero]
  refine hf.induction (P := fun f ↦ ∫ᶜ x, f x ∂(c • μ) = c * ∫ᶜ x, f x ∂μ) ?_ ?_ ?_ ?_
  · intro v s hs _
    rw [VectorMeasure.integral_indicator_const _ hs, VectorMeasure.integral_indicator_const _ hs]
    simp [mul_left_comm]
  · intro f g _ hf hg hPf hPg
    simp only [Pi.add_apply]
    rw [VectorMeasure.integral_fun_add (hint.2 hf) (hint.2 hg),
      VectorMeasure.integral_fun_add hf hg, hPf, hPg, mul_add]
  · refine isClosed_eq ?_ (continuous_const.mul VectorMeasure.continuous_integral)
    refine (LipschitzWith.of_dist_le_mul (K := ‖c‖₊) fun g h ↦ ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, ← VectorMeasure.integral_sub (hint.2 (L1.integrable_coeFn g))
      (hint.2 (L1.integrable_coeFn h)), L1.norm_eq_integral_norm]
    refine (norm_integral_le_integral_norm (c • μ) _).trans_eq ?_
    rw [hvar, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, coe_nnnorm]
    congr 1
    exact integral_congr_ae ((Lp.coeFn_sub g h).mono fun x hx ↦ congrArg norm hx.symm)
  · intro f g hfg _ hPf
    rw [← VectorMeasure.integral_congr_ae (hae hfg), ← VectorMeasure.integral_congr_ae hfg, hPf]

end MeasureTheory.ComplexMeasure
