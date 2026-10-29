/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finiteness of the variation of a vector measure in a finite-dimensional space

## Main results

* instance `IsFiniteMeasure μ.variation` for a signed measure `μ`.
* instance `IsFiniteMeasure μ.variation` for a vector measure `μ` with values in a
  finite-dimensional real normed space. In particular this covers complex measures.

## Notes

This is a shorter version of Mathlib PR #42103, which uses coordinates with respect to a Schauder
basis. -/

@[expose] public section

open ContinuousLinearMap

namespace MeasureTheory.VectorMeasure

variable {X : Type*} {mX : MeasurableSpace X}

/-- The variation of a signed measure is a finite measure. -/
instance (s : SignedMeasure X) : IsFiniteMeasure s.variation :=
  s.totalVariation_eq_variation ▸ inferInstance

/-- Composing a vector measure with a continuous linear map `f` multiplies its variation by at
most `‖f‖`. -/
lemma variation_mapRangeL {𝕜 V W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace 𝕜 W] (μ : VectorMeasure X V)
    (f : V →L[𝕜] W) : (mapRangeL f μ).variation ≤ ‖f‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le; intro s _
  exact (f.le_opENorm _).trans (mul_le_mul_right (enorm_measure_le_variation μ s) _)

/-- The variation of a vector measure with values in a finite-dimensional real normed space is
finite. -/
instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : VectorMeasure X V) : IsFiniteMeasure μ.variation := by
  let b := Module.finBasis ℝ V
  let c i : SignedMeasure X := mapRangeL (b.coord i).toContinuousLinearMap μ
  suffices hμ : ∑ i, mapRangeL (toSpanSingleton ℝ (b i)) (c i) = μ by
    refine isFiniteMeasure_of_le (∑ i, ‖toSpanSingleton ℝ (b i)‖₊ • (c i).variation) ?_
    rw [← hμ]
    refine (variation_finsetSum_le _ _).trans ?_
    gcongr
    exact variation_mapRangeL _ _
  ext
  rw [FunLike.coe_sum, Finset.sum_apply]
  exact b.sum_repr _

end MeasureTheory.VectorMeasure
