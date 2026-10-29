/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib
public import SpectralThm.VectorMeasure.FiniteDimensional

/-!
# Integral of a complex function against a complex measure

Mathlib defines the integral of `f : X → E` against a vector measure `μ : VectorMeasure X F` through
a continuous bilinear pairing `B : E →L[ℝ] F →L[ℝ] G`, written `∫ᵛ x, f x ∂[B; μ]`
(`MeasureTheory.VectorMeasure.integral`). For a complex function and a complex measure the pairing
is multiplication, `ContinuousLinearMap.mul ℝ ℂ`.

## Notation

* `∫ᶜ x, f x ∂μ`: the integral `∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]` of `f : X → ℂ` against
  `μ : ComplexMeasure X`. Scoped in `MeasureTheory.ComplexMeasure`.

## Main results

* `MeasureTheory.ComplexMeasure.integral_const_mul`: the integral is `ℂ`-linear in `f`.
* `MeasureTheory.ComplexMeasure.norm_integral_le_integral_norm`: `‖∫ f dμ‖ ≤ ∫ ‖f‖ d|μ|`.

The relation with the polar decomposition, `∫ f dμ = ∫ (dμ/d|μ|) f d|μ|`, is
`ComplexRMK.integral_eq_integral_rnDeriv` in `SpectralThm/RieszMarkovKakutani/Complex.lean`.
-/

@[expose] public section

namespace MeasureTheory.ComplexMeasure

open ContinuousLinearMap

@[inherit_doc VectorMeasure.integral]
scoped notation3 "∫ᶜ "(...)", "r:60:(scoped f => f)" ∂"μ:70 =>
  VectorMeasure.integral μ r (ContinuousLinearMap.mul ℝ ℂ)

variable {X : Type*} {mX : MeasurableSpace X} (μ : ComplexMeasure X)

/-- The integral against a complex measure is `ℂ`-linear. -/
lemma integral_const_mul (c : ℂ) (f : X → ℂ) : ∫ᶜ x, c * f x ∂μ = c * ∫ᶜ x, f x ∂μ := by
  by_cases hf : μ.Integrable f
  · have h₁ := VectorMeasure.integral_continuousLinearMap_comp (B := mul ℝ ℂ) (μ := μ)
      (C := mul ℝ ℂ c) hf
    have h₂ := VectorMeasure.continuousLinearMap_apply_integral (B := mul ℝ ℂ) (μ := μ)
      (C := mul ℝ ℂ c) hf
    have h : mul ℝ ℂ ∘L mul ℝ ℂ c = (compL ℝ ℂ ℂ ℂ (mul ℝ ℂ c)) ∘L mul ℝ ℂ := by
      ext x y; simp [mul_assoc]
    exact (h₁.trans (h ▸ h₂.symm) :)
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    rw [VectorMeasure.integral_undef hf, VectorMeasure.integral_undef, mul_zero]
    exact fun h ↦ hf (by simpa [hc] using h.const_mul c⁻¹)

/-- `‖∫ f dμ‖ ≤ ∫ ‖f‖ d|μ|`. -/
lemma norm_integral_le_integral_norm (f : X → ℂ) :
    ‖∫ᶜ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ.variation :=
  (VectorMeasure.norm_integral_le_integral_norm ..).trans <|
    mul_le_of_le_one_left (integral_nonneg fun _ ↦ norm_nonneg _) (opNorm_mul_le ℝ ℂ)

end MeasureTheory.ComplexMeasure
