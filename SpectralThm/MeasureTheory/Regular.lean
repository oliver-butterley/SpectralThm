/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Sums of regular measures

Mathlib has instances for `InnerRegular (μ + ν)` and for scalar multiples of outer regular and
regular measures. This file adds the corresponding instances for sums.

## Main results

* `MeasureTheory.Measure.OuterRegular.add`: the sum of two outer regular measures is outer regular.
* `MeasureTheory.Measure.Regular.add`: the sum of two regular measures is regular.
* `MeasureTheory.Measure.Regular.finset_sum`: a finite sum of regular measures is regular.

## Notes

* File destination: `Mathlib/MeasureTheory/Measure/Regular.lean`
-/

@[expose] public section

namespace MeasureTheory.Measure

variable {X : Type*} {mX : MeasurableSpace X} [TopologicalSpace X]

namespace OuterRegular

/-- The sum of two outer regular measures is outer regular. -/
instance add (μ₁ μ₂ : Measure X) [μ₁.OuterRegular] [μ₂.OuterRegular] :
    (μ₁ + μ₂).OuterRegular := by
  constructor
  intro A hA r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_add_lt_of_add_lt hr
  obtain ⟨U, hAU, hU, hμU⟩ := A.exists_isOpen_lt_of_lt u hu
  obtain ⟨V, hAV, hV, hμV⟩ := A.exists_isOpen_lt_of_lt v hv
  use U ∩ V
  refine ⟨Set.subset_inter hAU hAV, hU.inter hV, ?_⟩
  calc
    (μ₁ + μ₂) (U ∩ V) ≤ μ₁ U + μ₂ V := by
        simp only [Measure.coe_add, Pi.add_apply]
        gcongr
        · exact Set.inter_subset_left
        · exact Set.inter_subset_right
    _ < u + v := by gcongr
    _ < r := by grind

end OuterRegular

namespace Regular

/-- The sum of two regular measures is regular. -/
instance add (μ₁ μ₂ : Measure X) [μ₁.Regular] [μ₂.Regular] : (μ₁ + μ₂).Regular where
  lt_top_of_isCompact _K hK := ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  innerRegular := by
    intro U hU r hr
    simp only [Measure.coe_add, Pi.add_apply] at hr
    rcases eq_or_ne (μ₁ U) 0 with h₁ | h₁
    · simp only [h₁, zero_add] at hr
      obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
      exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
    rcases eq_or_ne (μ₂ U) 0 with h₂ | h₂
    · simp only [h₂, add_zero] at hr
      obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
      exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
    obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_lt_add_of_lt_add hr h₁ h₂
    obtain ⟨K, hKU, hK, huK⟩ := hU.exists_lt_isCompact hu
    obtain ⟨L, hLU, hL, hvL⟩ := hU.exists_lt_isCompact hv
    use K ∪ L
    refine ⟨Set.union_subset hKU hLU, hK.union hL, ?_⟩
    calc
      r < u + v := huv
      _ < μ₁ K + μ₂ L := by gcongr
      _ ≤ (μ₁ + μ₂) (K ∪ L) := by
          simp only [Measure.coe_add, Pi.add_apply]
          gcongr
          · exact Set.subset_union_left
          · exact Set.subset_union_right

/-- A finite sum of regular measures is regular. -/
instance finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure X) [∀ i, (μ i).Regular] :
    (∑ i ∈ s, μ i).Regular := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [Finset.sum_empty] using Measure.Regular.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      infer_instance

end Regular

end MeasureTheory.Measure
