/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# The total variation distance and norm on vector measures

For a vector measure `μ` with values in a normed group, the total variation `|μ|(X)` defines an
extended norm, and `|μ - ν|(X)` an extended distance, on vector measures.

## Main definitions

* `MeasureTheory.VectorMeasure.instEMetricSpace`: the extended metric `edist μ ν = |μ - ν|(X)`.
* `MeasureTheory.VectorMeasure.instENormedAddCommMonoid`: the extended norm `‖μ‖ₑ = |μ|(X)`.

## Main results

* `MeasureTheory.VectorMeasure.variation_univ_eq_zero`: `|μ|(X) = 0 ↔ μ = 0`.
* `MeasureTheory.VectorMeasure.edist_eq_variation_sub`: `edist μ ν = |μ - ν|(X)`.
* `MeasureTheory.VectorMeasure.enorm_eq_variation`: `‖μ‖ₑ = |μ|(X)`.

## References

* Section 6.5 of [Walter Rudin, *Real and Complex Analysis*][Rud87]

## TODO

When the variation is finite (for instance for a finite-dimensional codomain, see
`Mathlib/MeasureTheory/VectorMeasure/Variation/FiniteDimensional.lean`), the total variation
should give a `NormedAddCommGroup` (and, for complex measures, Banach space) structure.
-/

@[expose] public section

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X} [NormedAddCommGroup V]

/-- A vector measure vanishes iff its total variation `|μ|(X)` does. -/
lemma variation_univ_eq_zero {μ : VectorMeasure X V} : μ.variation Set.univ = 0 ↔ μ = 0 := by
  simp

/-- The total variation distance `edist μ ν = |μ - ν|(X)` on vector measures. -/
noncomputable instance instEMetricSpace : EMetricSpace (VectorMeasure X V) where
  edist μ ν := (μ - ν).variation Set.univ
  edist_self _ := by simp
  edist_comm μ ν := by rw [← neg_sub, variation_neg]
  edist_triangle μ ν ρ := by
    simpa using variation_add_le (μ := μ - ν) (ν := ν - ρ) Set.univ
  eq_of_edist_eq_zero h := sub_eq_zero.mp (variation_univ_eq_zero.mp h)

lemma edist_eq_variation_sub (μ ν : VectorMeasure X V) :
    edist μ ν = (μ - ν).variation Set.univ :=
  rfl

/-- The total variation norm `‖μ‖ₑ = |μ|(X)` on vector measures. -/
noncomputable instance instENormedAddCommMonoid : ENormedAddCommMonoid (VectorMeasure X V) where
  enorm μ := μ.variation Set.univ
  continuous_enorm := by
    have : Continuous fun μ : VectorMeasure X V ↦ edist μ 0 := continuous_id.edist continuous_const
    simpa [edist_eq_variation_sub] using this
  enorm_zero := by simp
  enorm_add_le μ ν := by simpa using variation_add_le (μ := μ) (ν := ν) Set.univ
  enorm_eq_zero _ := variation_univ_eq_zero

lemma enorm_eq_variation (μ : VectorMeasure X V) : ‖μ‖ₑ = μ.variation Set.univ :=
  rfl

end MeasureTheory.VectorMeasure
