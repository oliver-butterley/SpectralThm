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
* `MeasureTheory.ComplexMeasure.integral_simpleFunc`: `∫ s dμ = ∑ a * μ (s ⁻¹' {a})`.
* `MeasureTheory.ComplexMeasure.integrable_continuousMap`: continuous functions on a compact
  space are integrable.

The relation with the polar decomposition, `∫ f dμ = ∫ (dμ/d|μ|) f d|μ|`, is
`MeasureTheory.ComplexMeasure.integral_eq_integral_rnDeriv` in
`SpectralThm/ComplexMeasure/RadonNikodym.lean`.

## Notes

The notation `∫ᶜ` is a stopgap. Mathlib already has notations for fixed pairings next to the
definition of the integral (`Mathlib/MeasureTheory/VectorMeasure/Integral.lean`):
`∫ᵛ x, f x ∂•μ` for a real function against a vector measure (pairing `lsmul ℝ ℝ`) and
`∫ᵛ x, f x ∂<•μ` for a vector function against a signed measure. The plan is to generalise `∂•` in
Mathlib from `ℝ` to any scalar field `𝕜`, using the pairing `lsmul ℝ 𝕜` (`f x • dμ`). Since
`lsmul ℝ ℂ = mul ℝ ℂ` as pairings on `ℂ`, `∫ᵛ x, f x ∂•μ` would then cover this file, and also
complex functions against any complex-Banach-valued measure. Once that is in Mathlib, `∫ᶜ` should be
removed in favour of it, and the lemmas here stated for `∂•` and moved to Mathlib.
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

/-- The integral of a simple function against a complex measure. -/
lemma integral_simpleFunc (s : SimpleFunc X ℂ) :
    ∫ᶜ x, s x ∂μ = ∑ a ∈ s.range, a * μ (s ⁻¹' {a}) := by
  rw [VectorMeasure.integral_eq_setToFun,
    setToFun_simpleFunc _ s (SimpleFunc.integrable_of_isFiniteMeasure s)]
  rfl

/-- A continuous function on a compact space is integrable against every complex measure. -/
lemma integrable_continuousMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : ComplexMeasure X) (f : C(X, ℂ)) :
    μ.Integrable f :=
  (BoundedContinuousFunction.mkOfCompact f).integrable _

end MeasureTheory.ComplexMeasure
