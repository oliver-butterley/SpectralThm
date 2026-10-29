/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# Finite sums in the weak operator topology

Additions to `Mathlib/Analysis/LocallyConvex/WeakOperatorTopology.lean`: `ofCLM` and `toCLM` commute
with finite sums, and a finite sum of operators is evaluated pointwise.

## Main results

* `ContinuousLinearMapWOT.ofCLM_sum`, `ContinuousLinearMapWOT.toCLM_sum`
* `ContinuousLinearMapWOT.sum_apply`: `(∑ i ∈ s, A i) x = ∑ i ∈ s, A i x`.
-/

@[expose] public section

namespace ContinuousLinearMapWOT

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
  {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F] [IsTopologicalAddGroup F] {ι : Type*}

@[simp]
lemma ofCLM_sum (s : Finset ι) (A : ι → E →SL[σ] F) :
    ofCLM (∑ i ∈ s, A i) = ∑ i ∈ s, ofCLM (A i) :=
  map_sum addEquiv.symm A s

@[simp]
lemma toCLM_sum (s : Finset ι) (A : ι → E →SWOT[σ] F) :
    toCLM (∑ i ∈ s, A i) = ∑ i ∈ s, toCLM (A i) :=
  map_sum addEquiv A s

@[simp]
lemma sum_apply (s : Finset ι) (A : ι → E →SWOT[σ] F) (x : E) :
    (∑ i ∈ s, A i) x = ∑ i ∈ s, A i x := by
  rw [← toCLM_apply, toCLM_sum, _root_.sum_apply]
  rfl

end ContinuousLinearMapWOT
