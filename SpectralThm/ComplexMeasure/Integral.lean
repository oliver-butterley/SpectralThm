/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib
public import SpectralThm.toMathlib.Variation.Defs
public import SpectralThm.toMathlib.Variation.Lemmas


/-!
# Integral with respect to a complex-valued measure

Three options come to mind for defining the integral with respect to a complex-valued measure:

1. Define the integral with respect to a complex measure by decomposing the measure into real and imaginary parts and then using the definition of integral with respect to a signed measure. I.e.,
```
noncomputable def integral (μ : SignedMeasure α) (f : α → G) : G :=
    ∫ a, f a ∂μ.toJordanDecomposition.posPart - ∫ a, f a ∂μ.toJordanDecomposition.negPart
```
In turn, the integral with respect to as signed measure is defined using the Jordan decomposition
into positive and negative parts.

2. Develop directly the integral with respect to any `VectorMeasure` by introducing simple
functions, etc.

3. Use the polar decomposition of a complex measure into total variation measure and angular
function and hence use the definition of a Bochner integral.

It is unclear what the best design choice is so at the moment we opt for using polar decomposition
as the definition.

Whatever the direction taken with these definitions, the different components should be separated
into their own files.

## Main definitions

* `ComplexMeasure.integral`

## Notation

* `∫ a, f a ∂μ` : integral of `f` with respect to a `ComplexMeasure` `μ`

## To do

* Add many other relevant results.

-/

@[expose] public section

namespace MeasureTheory.ComplexMeasure

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-! ## Polar decomposition of complex measures. -/

/-- The variation measure part in the polar decomposition of a complex measure. -/
noncomputable def var (μ : ComplexMeasure α) := μ.variation.ennrealToMeasure

@[simp]
lemma var_neg (μ : ComplexMeasure α) : (-μ).var = μ.var := by
  simp [var, MeasureTheory.VectorMeasure.variation_neg]

/-- The angular part (density function) in the polar decomposition of a complex measure. -/
noncomputable def ang (μ : ComplexMeasure α) := μ.rnDeriv μ.var

@[simp]
lemma ang_neg (μ : ComplexMeasure α) : (-μ).ang =ᶠ[ae μ.var] -μ.ang := by
  rw [ang, ang, var_neg]
  -- need lenna for `ComplexMeasure` like `MeasureTheory.SignedMeasure.rnDeriv_neg`
  -- To do: adjust this statement to the `μ`-a.e. version.
  -- This should follow from lemmas about `SignedMeasure.neg` and `rnDeriv`
  -- and need that `-(re c).toComplexMeasure (im c) = (re (-c)).toComplexMeasure (im -c)`
  -- maybe add a lemma about `smul` in `Mathlib.MeasureTheory.Measure.Complex`
  sorry

/-! ## Definition of the integral. -/

-- TODO switch the definition to the integral against a vector measure.
-- Find/place these lemma in the folder of `VectorMeasure`

/-- The integral with respect to a complex measure defined using the polar decomposition of the
complex measure and the integral with respect to the total variation.-/
noncomputable def integral (μ : ComplexMeasure α) (f : α → G) :=
  ∫ x,  μ.ang x • f x ∂(μ.var)

notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral μ r

/-! ## Some lemmas related to the integral. -/

/-- For complex measures `μ`, `ν` and integrable function `f`: `∫ f d(μ + ν) = ∫ f dμ + ∫ f dν` -/
lemma integral_add (μ ν : ComplexMeasure α) (f : α → ℂ) :
    ∫ a, f a ∂(μ + ν) = ∫ a, f a ∂μ + ∫ a, f a ∂ν := by
  dsimp [integral]
  /- **Proof outline**:
  - Every complex measure `μ` has polar decomposition `μ = h · |μ|` where `|μ|` is
    the total variation (positive measure) and `|h| = 1` a.e.
  - By definition `∫ f dμ = ∫ (f · h) d|μ|`
  - We use a common dominating measure to avoid relating different polar decompositions
    Let `λ := |μ| + |ν| + |μ + ν|` (finite positive measure)
  - By RN theorem, ∃ `g₁, g₂ ∈ L¹(λ)` such that:
    - `dμ = g₁ dλ`
    - `dν = g₂ dλ`
    - `d(μ + ν) = (g₁ + g₂) dλ`
  - Use linarity with respect to positive measures:
    ∫ f d(μ + ν) = ∫ f(g₁ + g₂) dλ       -- by definition
                  = ∫ fg₁ dλ + ∫ fg₂ dλ  -- linearity w.r.t. positive measure λ
                  = ∫ f dμ + ∫ f dν      -- returning to the original measures
  -/
  sorry

lemma integral_neg (μ  : ComplexMeasure α) (f : α → ℂ) :
    ∫ a, f a ∂(-μ) = -∫ a, f a ∂μ := by
  simp [integral, MeasureTheory.integral_neg]
  sorry -- need lemma for a.e. equality of complex measure

lemma integral_sub (μ₁ μ₂  : ComplexMeasure α) (f : α → ℂ) :
    ∫ a, f a ∂(μ₁ - μ₂) = ∫ a, f a ∂μ₁ - ∫ a, f a ∂μ₂ := by
  calc
    _ = (μ₁ + (-μ₂)).integral f := by rfl
    _ = μ₁.integral f + (-μ₂).integral f := by exact integral_add μ₁ (-μ₂) _
    _ = _ := by rw [integral_neg, sub_eq_add_neg]

end MeasureTheory.ComplexMeasure
