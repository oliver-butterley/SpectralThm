/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# Star structures on almost everywhere equal functions

Mathlib equips `α →ₘ[μ] R` with `Star`, `InvolutiveStar` and `TrivialStar` instances. This file
adds the compatibility of the star operation with addition, multiplication and scalar
multiplication.

## Main definitions

* Instances `StarAddMonoid`, `StarMul` and `StarModule` on `α →ₘ[μ] R`.
-/

@[expose] public section

namespace MeasureTheory.AEEqFun

variable {α R : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace R]

@[simp]
theorem star_mk [Star R] [ContinuousStar R] (f : α → R) (hf : AEStronglyMeasurable f μ) :
    star (mk f hf : α →ₘ[μ] R) = mk (star f) hf.star :=
  rfl

instance instStarAddMonoid [AddMonoid R] [StarAddMonoid R] [ContinuousAdd R] [ContinuousStar R] :
    StarAddMonoid (α →ₘ[μ] R) where
  star_add f g := induction_on₂ f g fun f hf g hg ↦ by simp [star_add]

instance instStarMul [Mul R] [StarMul R] [ContinuousMul R] [ContinuousStar R] :
    StarMul (α →ₘ[μ] R) where
  star_mul f g := induction_on₂ f g fun f hf g hg ↦ by simp [star_mul]

instance instStarModule {𝕜 : Type*} [Star 𝕜] [Star R] [SMul 𝕜 R] [StarModule 𝕜 R]
    [ContinuousConstSMul 𝕜 R] [ContinuousStar R] : StarModule 𝕜 (α →ₘ[μ] R) where
  star_smul c f := induction_on f fun f hf ↦ by simp [star_smul]

end MeasureTheory.AEEqFun
