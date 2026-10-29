/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Additional API for continuous functions vanishing at infinity

## Main definitions

* `ZeroAtInftyContinuousMap.normComp`: the pointwise norm `x ↦ ‖f x‖` of `f : C₀(α, β)`.
* `ZeroAtInftyContinuousMap.toComplex`: a real function vanishing at infinity, seen as a complex
  function.
* `ContinuousMap.liftZeroAtInftyCLE`: on a compact space, `ContinuousMap.liftZeroAtInfty` as a
  continuous linear equivalence `C(α, β) ≃L[R] C₀(α, β)`.

## Main results

* `ZeroAtInftyContinuousMap.norm_coe_le_norm`: `‖f x‖ ≤ ‖f‖`.
* `ZeroAtInftyContinuousMap.norm_le`: `‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C` for `0 ≤ C`.
* `ContinuousMap.isometry_liftZeroAtInfty`: `ContinuousMap.liftZeroAtInfty` is an isometry.
-/

@[expose] public section

open Filter Topology ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {α β : Type*} [TopologicalSpace α]

section Norm

variable [SeminormedAddCommGroup β]

theorem norm_coe_le_norm (f : C₀(α, β)) (x : α) : ‖f x‖ ≤ ‖f‖ :=
  f.toBCF.norm_coe_le_norm x

theorem norm_le {f : C₀(α, β)} {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ x, ‖f x‖ ≤ C :=
  f.toBCF.norm_le hC

/-- The pointwise norm `x ↦ ‖f x‖` of a continuous function vanishing at infinity. -/
noncomputable def normComp (f : C₀(α, β)) : C₀(α, ℝ) where
  toFun x := ‖f x‖
  continuous_toFun := f.continuous.norm
  zero_at_infty' := by simpa using f.zero_at_infty'.norm

@[simp]
theorem normComp_apply (f : C₀(α, β)) (x : α) : f.normComp x = ‖f x‖ :=
  rfl

@[simp]
theorem norm_normComp (f : C₀(α, β)) : ‖f.normComp‖ = ‖f‖ :=
  f.toBCF.norm_normComp

end Norm

/-- A real function vanishing at infinity, seen as a complex function. -/
def toComplex (f : C₀(α, ℝ)) : C₀(α, ℂ) where
  toFun x := f x
  continuous_toFun := Complex.continuous_ofReal.comp f.continuous
  zero_at_infty' :=
    Complex.ofReal_zero ▸ (Complex.continuous_ofReal.tendsto 0).comp f.zero_at_infty'

@[simp]
theorem toComplex_apply (f : C₀(α, ℝ)) (x : α) : f.toComplex x = f x :=
  rfl

@[simp]
theorem toComplex_add (f g : C₀(α, ℝ)) : (f + g).toComplex = f.toComplex + g.toComplex := by
  ext; simp

@[simp]
theorem toComplex_smul (c : ℝ) (f : C₀(α, ℝ)) : (c • f).toComplex = c • f.toComplex := by
  ext; simp

end ZeroAtInftyContinuousMap

namespace ContinuousMap

open ZeroAtInftyContinuousMap.ContinuousMap

variable {α β R : Type*} [TopologicalSpace α] [CompactSpace α] [SeminormedAddCommGroup β]

theorem isometry_liftZeroAtInfty : Isometry (liftZeroAtInfty : C(α, β) → C₀(α, β)) :=
  fun _ _ ↦ rfl

@[simp]
theorem norm_liftZeroAtInfty (f : C(α, β)) : ‖liftZeroAtInfty f‖ = ‖f‖ :=
  rfl

variable [Semiring R] [Module R β] [ContinuousConstSMul R β]

/-- On a compact space, `ContinuousMap.liftZeroAtInfty` as a continuous linear equivalence:
`C(α, β)` and `C₀(α, β)` coincide. -/
@[simps!]
def liftZeroAtInftyCLE : C(α, β) ≃L[R] C₀(α, β) where
  __ := liftZeroAtInfty
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := isometry_liftZeroAtInfty.continuous
  continuous_invFun := isometry_liftZeroAtInfty.right_inv liftZeroAtInfty.right_inv |>.continuous

end ContinuousMap
