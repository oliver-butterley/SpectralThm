/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Inner products with star projections

Additions to `Mathlib/Analysis/InnerProductSpace/Adjoint.lean`.

## Main results

* `IsStarProjection.inner_apply_apply`: `⟪p x, p y⟫ = ⟪x, p y⟫` for a star projection `p`.
* `IsStarProjection.inner_apply_self`: `⟪x, p x⟫ = ‖p x‖ ^ 2`.
-/

@[expose] public section

open scoped InnerProductSpace

section IsStarProjection

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] {p : H →L[𝕜] H}

/-- For a star projection `p`, `⟪p x, p y⟫ = ⟪x, p y⟫`. -/
lemma IsStarProjection.inner_apply_apply (hp : IsStarProjection p) (x y : H) :
    ⟪p x, p y⟫_𝕜 = ⟪x, p y⟫_𝕜 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, hp.isSelfAdjoint.adjoint_eq,
    ← mul_apply_eq_comp, hp.isIdempotentElem.eq]

/-- For a star projection `p`, `⟪x, p x⟫ = ‖p x‖ ^ 2`. -/
lemma IsStarProjection.inner_apply_self (hp : IsStarProjection p) (x : H) :
    ⟪x, p x⟫_𝕜 = (‖p x‖ : 𝕜) ^ 2 := by
  rw [← hp.inner_apply_apply, inner_self_eq_norm_sq_to_K]

end IsStarProjection
