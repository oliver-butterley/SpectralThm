/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux, Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Measure.Support

/-!
# Essential range of a function

The essential range of a function `f : α → β` with respect to a measure `μ` on `α` is the support
of the push-forward measure `μ.map f`: the set of points `y` such that `f` takes values in every
neighbourhood of `y` on a set of positive measure. It only depends on the `μ`-a.e. class of `f`,
it is closed, and it contains `f x` for almost every `x`.

## Main definitions

* `essRange f μ`: the essential range of `f` with respect to `μ`.

## Main results

* `essRange_congr_ae`: the essential range only depends on the `μ`-a.e. class of `f`.
* `ae_mem_essRange`: `f` takes values in its essential range almost everywhere.
* `notMem_essRange_iff`: `y` is not in the essential range of `f` iff `f` stays a positive distance
  away from `y` almost everywhere.
* `essRange_subset_closure_range`: the essential range is contained in the closure of the range.
-/

@[expose] public section

open MeasureTheory Measure Filter Topology

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [MeasurableSpace β]
  [TopologicalSpace β] {f g : α → β}

/-- The essential range of `f` with respect to `μ`: the support of the push-forward `μ.map f`. -/
noncomputable def essRange (f : α → β) (μ : Measure α) : Set β :=
  (μ.map f).support

/-- The essential range only depends on the `μ`-a.e. class of the function. -/
theorem essRange_congr_ae (hfg : f =ᵐ[μ] g) : essRange f μ = essRange g μ := by
  rw [essRange, essRange, Measure.map_congr hfg]

/-- The essential range is closed. -/
theorem isClosed_essRange : IsClosed (essRange f μ) :=
  isClosed_support

/-- A function takes values in its essential range almost everywhere. -/
theorem ae_mem_essRange [HereditarilyLindelofSpace β] (hf : AEMeasurable f μ) :
    ∀ᵐ x ∂μ, f x ∈ essRange f μ :=
  ae_of_ae_map hf support_mem_ae

/-- The essential range of `f` is contained in the closure of its range. -/
theorem essRange_subset_closure_range [OpensMeasurableSpace β] (hf : AEMeasurable f μ) :
    essRange f μ ⊆ closure (Set.range f) :=
  support_subset_of_isClosed isClosed_closure <| (mem_ae_map_iff hf
    isClosed_closure.measurableSet).2 <| univ_mem' fun x ↦ subset_closure (Set.mem_range_self x)

/-- `y` is not in the essential range of `f` iff `f` stays a positive distance away from `y`
almost everywhere. -/
theorem notMem_essRange_iff {β : Type*} [MeasurableSpace β] [PseudoMetricSpace β]
    [OpensMeasurableSpace β] {f : α → β} (hf : AEMeasurable f μ) {y : β} :
    y ∉ essRange f μ ↔ ∃ δ > 0, ∀ᵐ x ∂μ, δ ≤ dist y (f x) := by
  have key (δ : ℝ) : μ.map f (Metric.ball y δ) = 0 ↔ ∀ᵐ x ∂μ, δ ≤ dist y (f x) := by
    rw [map_apply_of_aemeasurable hf Metric.isOpen_ball.measurableSet,
      measure_eq_zero_iff_ae_notMem]
    simp [dist_comm]
  rw [essRange, notMem_support_iff_exists]
  constructor
  · rintro ⟨U, hU, hU0⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    exact ⟨δ, hδ, (key δ).1 (measure_mono_null hδU hU0)⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨_, Metric.ball_mem_nhds y hδ, (key δ).2 h⟩
