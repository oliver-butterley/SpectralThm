/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Sums of regular measures

Mathlib has instances for `InnerRegular (μ + ν)` and for scalar multiples of outer regular, weakly
regular and regular measures. This file adds the corresponding results for sums.

## Main results

* `MeasureTheory.Measure.InnerRegularWRT.add`: if `p` is stable under binary unions, the sum of two
  measures which are inner regular with respect to `p` and `q` is inner regular with respect to
  `p` and `q`.
* `MeasureTheory.Measure.OuterRegular.add`: the sum of two outer regular measures is outer regular.
* `MeasureTheory.Measure.WeaklyRegular.add`: the sum of two weakly regular measures is weakly
  regular.
* `MeasureTheory.Measure.Regular.add`: the sum of two regular measures is regular.
* `MeasureTheory.Measure.Regular.finset_sum`: a finite sum of regular measures is regular.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {X : Type*} {mX : MeasurableSpace X}

/-- If `p` is stable under binary unions, the sum of two measures which are inner regular with
respect to `p` and `q` is inner regular with respect to `p` and `q`. -/
theorem InnerRegularWRT.add {μ ν : Measure X} {p q : Set X → Prop} (hμ : μ.InnerRegularWRT p q)
    (hν : ν.InnerRegularWRT p q) (hp : ∀ ⦃s t⦄, p s → p t → p (s ∪ t)) :
    (μ + ν).InnerRegularWRT p q := by
  intro U hU r hr
  rw [coe_add, Pi.add_apply] at hr
  rcases eq_or_ne (μ U) 0 with h₁ | h₁
  · rw [h₁, zero_add] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hν hU r hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  rcases eq_or_ne (ν U) 0 with h₂ | h₂
  · rw [h₂, add_zero] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hμ hU r hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_lt_add_of_lt_add hr h₁ h₂
  obtain ⟨K, hKU, hK, huK⟩ := hμ hU u hu
  obtain ⟨L, hLU, hL, hvL⟩ := hν hU v hv
  refine ⟨K ∪ L, Set.union_subset hKU hLU, hp hK hL, huv.trans ?_⟩
  calc
    u + v < μ K + ν L := by gcongr
    _ ≤ μ (K ∪ L) + ν (K ∪ L) := by gcongr <;> simp
    _ = (μ + ν) (K ∪ L) := (add_apply μ ν _).symm

variable [TopologicalSpace X]

namespace OuterRegular

/-- The sum of two outer regular measures is outer regular. -/
instance add (μ ν : Measure X) [μ.OuterRegular] [ν.OuterRegular] : (μ + ν).OuterRegular := by
  refine ⟨fun A hA r hr ↦ ?_⟩
  rw [coe_add, Pi.add_apply] at hr
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_add_lt_of_add_lt hr
  obtain ⟨U, hAU, hU, hμU⟩ := A.exists_isOpen_lt_of_lt u hu
  obtain ⟨V, hAV, hV, hνV⟩ := A.exists_isOpen_lt_of_lt v hv
  refine ⟨U ∩ V, Set.subset_inter hAU hAV, hU.inter hV, lt_of_le_of_lt ?_ huv⟩
  rw [add_apply]
  exact add_le_add ((measure_mono Set.inter_subset_left).trans hμU.le)
    ((measure_mono Set.inter_subset_right).trans hνV.le)

end OuterRegular

/-- The sum of two weakly regular measures is weakly regular. -/
instance WeaklyRegular.add (μ ν : Measure X) [μ.WeaklyRegular] [ν.WeaklyRegular] :
    (μ + ν).WeaklyRegular where
  innerRegular := WeaklyRegular.innerRegular.add WeaklyRegular.innerRegular fun _ _ ↦ .union

namespace Regular

/-- The sum of two regular measures is regular. -/
instance add (μ ν : Measure X) [μ.Regular] [ν.Regular] : (μ + ν).Regular where
  lt_top_of_isCompact _ hK := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩
  innerRegular := Regular.innerRegular.add Regular.innerRegular fun _ _ ↦ .union

/-- A finite sum of regular measures is regular. -/
instance finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure X) [∀ i, (μ i).Regular] :
    (∑ i ∈ s, μ i).Regular := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i s hi ih => rw [Finset.sum_insert hi]; infer_instance

end Regular

end MeasureTheory.Measure
