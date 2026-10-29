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
extended norm, and `|μ - ν|(X)` an extended distance, on vector measures [Rudin RCA 6.5].

## Main definitions

* `MeasureTheory.VectorMeasure.instEMetricSpace`: the extended metric `edist μ ν = |μ - ν|(X)`.
* `MeasureTheory.VectorMeasure.instENormedAddCommMonoid`: the extended norm `‖μ‖ₑ = |μ|(X)`.

## Main results

* `MeasureTheory.VectorMeasure.variation_univ_eq_zero`: `|μ|(X) = 0 ↔ μ = 0`.
* `MeasureTheory.VectorMeasure.edist_eq_variation_sub`: `edist μ ν = |μ - ν|(X)`.

## References

* Section 6 of [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

* For a finite-dimensional codomain the variation is finite, and this should give a
  `NormedAddCommGroup` instance on complex measures [Rudin RCA 6.5].
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
  edist_self := by intro; simp
  edist_comm := by
    intro _ _
    rw [← MeasureTheory.VectorMeasure.variation_neg]
    simp
  edist_triangle := by
    intro x y z
    simpa using Measure.le_iff.mp (VectorMeasure.variation_add_le (μ := x - y) (ν := y - z))
      Set.univ MeasurableSet.univ
  eq_of_edist_eq_zero {x y} h := by
    rw [variation_univ_eq_zero] at h
    exact eq_of_sub_eq_zero h

lemma edist_eq_variation_sub (μ ν : VectorMeasure X V) :
    edist μ ν = (μ - ν).variation Set.univ := by rfl

/-- The total variation norm `‖μ‖ₑ = |μ|(X)` on vector measures. -/
noncomputable instance instENormedAddCommMonoid : ENormedAddCommMonoid (VectorMeasure X V) where
  enorm μ := μ.variation Set.univ
  continuous_enorm := by
    have : Continuous (fun x : VectorMeasure X V ↦ edist x 0) := by
      continuity
    simpa [edist_eq_variation_sub, sub_zero] using this
  enorm_zero := by simp
  enorm_add_le x y := by
    simpa using Measure.le_iff.mp (VectorMeasure.variation_add_le (μ := x) (ν := y)) Set.univ
      MeasurableSet.univ
  enorm_eq_zero x := variation_univ_eq_zero

end MeasureTheory.VectorMeasure
