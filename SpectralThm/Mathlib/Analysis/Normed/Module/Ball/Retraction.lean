/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The radial retraction onto the closed unit ball

## Main definitions

* `unitBallRetraction`: the radial retraction `z ↦ (max 1 ‖z‖)⁻¹ • z` of a real normed space onto
  its closed unit ball.

## Main results

* `continuous_unitBallRetraction`: the retraction is continuous.
* `norm_unitBallRetraction_le`: its values lie in the closed unit ball.
* `unitBallRetraction_of_norm_le_one`: it is the identity on the closed unit ball.
* `norm_unitBallRetraction_sub_le`: `‖unitBallRetraction z - w‖ ≤ 2 * ‖z - w‖` whenever
  `‖w‖ ≤ 1`.
-/

@[expose] public section

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction of `E` onto its closed unit ball. -/
noncomputable def unitBallRetraction (z : E) : E := (max 1 ‖z‖)⁻¹ • z

@[fun_prop]
theorem continuous_unitBallRetraction : Continuous (unitBallRetraction (E := E)) :=
  ((continuous_const.max continuous_norm).inv₀ fun z ↦
    (one_pos.trans_le (le_max_left 1 ‖z‖)).ne').smul continuous_id

@[simp]
theorem unitBallRetraction_zero : unitBallRetraction (0 : E) = 0 := by
  simp [unitBallRetraction]

theorem unitBallRetraction_of_norm_le_one {z : E} (hz : ‖z‖ ≤ 1) : unitBallRetraction z = z := by
  rw [unitBallRetraction, max_eq_left hz, inv_one, one_smul]

theorem norm_unitBallRetraction_le (z : E) : ‖unitBallRetraction z‖ ≤ 1 := by
  have h : 0 < max 1 ‖z‖ := one_pos.trans_le (le_max_left _ _)
  rw [unitBallRetraction, norm_smul, norm_inv, Real.norm_of_nonneg h.le, inv_mul_le_one₀ h]
  exact le_max_right _ _

theorem norm_unitBallRetraction_sub_le {z w : E} (hw : ‖w‖ ≤ 1) :
    ‖unitBallRetraction z - w‖ ≤ 2 * ‖z - w‖ := by
  rcases le_total ‖z‖ 1 with h | h
  · rw [unitBallRetraction_of_norm_le_one h]
    linarith [norm_nonneg (z - w)]
  have hz : 0 < ‖z‖ := one_pos.trans_le h
  have h₁ : ‖unitBallRetraction z - z‖ = ‖z‖ - 1 := by
    rw [unitBallRetraction, max_eq_right h,
      show ‖z‖⁻¹ • z - z = (‖z‖⁻¹ - 1) • z by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, abs_of_nonpos (by linarith [inv_le_one_of_one_le₀ h]), neg_sub,
      sub_mul, one_mul, inv_mul_cancel₀ hz.ne']
  have h₂ : ‖z‖ - 1 ≤ ‖z - w‖ := (sub_le_sub_left hw _).trans (norm_sub_norm_le z w)
  calc ‖unitBallRetraction z - w‖ ≤ ‖unitBallRetraction z - z‖ + ‖z - w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖z - w‖ := by linarith
