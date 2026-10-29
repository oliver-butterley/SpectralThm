/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported

import Mathlib.Topology.UrysohnsLemma

/-!
# Additional API for compactly supported continuous functions

## Main definitions

* `CompactlySupportedContinuousMap.normComp`: the pointwise norm `x ↦ ‖f x‖` of `f : C_c(α, β)`.

## Main results

* `ZeroAtInftyContinuousMap.exists_compactlySupported_norm_sub_le`: on a locally compact regular
  space, every continuous function vanishing at infinity is a uniform limit of compactly supported
  continuous functions.
-/

@[expose] public section

open NNReal ZeroAtInfty CompactlySupported

namespace CompactlySupportedContinuousMap

variable {α β : Type*} [TopologicalSpace α]

/-- The pointwise norm `x ↦ ‖f x‖` of a compactly supported continuous function. -/
noncomputable def normComp [SeminormedAddCommGroup β] (f : C_c(α, β)) : C_c(α, ℝ) where
  toFun x := ‖f x‖
  continuous_toFun := f.continuous.norm
  hasCompactSupport' := f.hasCompactSupport'.comp_left (g := fun y : β ↦ ‖y‖) norm_zero

@[simp]
theorem normComp_apply [SeminormedAddCommGroup β] (f : C_c(α, β)) (x : α) :
    f.normComp x = ‖f x‖ :=
  rfl

@[simp]
theorem toReal_zero : (0 : C_c(α, ℝ≥0)).toReal = 0 := by
  ext; simp

theorem toReal_nnrealPart_of_nonneg {f : C_c(α, ℝ)} (hf : 0 ≤ f) : f.nnrealPart.toReal = f := by
  ext x; simpa using hf x

end CompactlySupportedContinuousMap

namespace ZeroAtInftyContinuousMap

variable {α E : Type*} [TopologicalSpace α] [RegularSpace α] [LocallyCompactSpace α]
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous function vanishing at infinity is uniformly approximated by compactly supported
continuous functions. -/
theorem exists_compactlySupported_norm_sub_le (f : C₀(α, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(α, E), ∀ x, ‖f x - g x‖ ≤ ε := by
  obtain ⟨K, hK, hKf⟩ := (Filter.hasBasis_cocompact.tendsto_iff Metric.nhds_basis_closedBall).mp
    f.zero_at_infty' ε hε
  obtain ⟨χ, hχ1, -, hχc, hχ01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  refine ⟨⟨⟨fun x ↦ χ x • f x, by fun_prop⟩, hχc.smul_right⟩, fun x ↦ ?_⟩
  simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
  by_cases hx : x ∈ K
  · simp [hχ1 hx, hε.le]
  · have h₁ : ‖f x‖ ≤ ε := by simpa using hKf x hx
    rw [show f x - χ x • f x = (1 - χ x) • f x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_of_nonneg (sub_nonneg.mpr (hχ01 x).2)]
    nlinarith [(hχ01 x).1, norm_nonneg (f x)]

end ZeroAtInftyContinuousMap
