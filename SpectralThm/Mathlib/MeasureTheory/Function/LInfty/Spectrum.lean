/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import SpectralThm.Mathlib.MeasureTheory.Function.EssRange
public import SpectralThm.Mathlib.MeasureTheory.Function.LInfty

/-!
# The spectrum in `L^∞`

The spectrum of an element `f` of the algebra `Lp 𝕜 ∞ μ` is the essential range of `f`.

## Main results

* `MeasureTheory.Linfty.isUnit_iff`: `f` is invertible in `L^∞` iff `‖f‖` is bounded away from
  `0` almost everywhere.
* `MeasureTheory.Linfty.spectrum_eq_essRange`: the spectrum of `f` in `L^∞` is its essential
  range.
-/

@[expose] public section

open Filter
open scoped ENNReal

namespace MeasureTheory.Linfty

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- An element of `L^∞` is invertible iff its norm is bounded away from `0` almost everywhere. -/
theorem isUnit_iff {R : Type*} [NormedDivisionRing R] {f : Lp R ∞ μ} :
    IsUnit f ↔ ∃ δ > 0, ∀ᵐ x ∂μ, δ ≤ ‖f x‖ := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(‖(↑u⁻¹ : Lp R ∞ μ)‖ + 1)⁻¹, by positivity, ?_⟩
    filter_upwards [coeFn_mul (↑u⁻¹ : Lp R ∞ μ) u, coeFn_one (R := R) (μ := μ),
      Lp.ae_norm_le_norm (↑u⁻¹ : Lp R ∞ μ)] with x hmul hone hle
    rw [Units.inv_mul, hone, Pi.mul_apply, Pi.one_apply] at hmul
    have h₁ : ‖(↑u⁻¹ : Lp R ∞ μ) x‖ * ‖(u : Lp R ∞ μ) x‖ = 1 := by
      rw [← norm_mul, ← hmul, norm_one]
    rw [inv_le_iff_one_le_mul₀' (by positivity)]
    exact h₁.symm.le.trans (by gcongr; linarith)
  · rintro ⟨δ, hδ, h⟩
    have hinv : MemLp (fun x ↦ (f x)⁻¹) ∞ μ := by
      refine memLp_top_of_bound (Lp.aestronglyMeasurable f).inv₀ δ⁻¹ ?_
      filter_upwards [h] with x hx
      rw [norm_inv]
      exact inv_anti₀ hδ hx
    refine isUnit_iff_exists.2 ⟨hinv.toLp _, Lp.ext ?_, Lp.ext ?_⟩ <;>
    filter_upwards [coeFn_mul f (hinv.toLp _), coeFn_mul (hinv.toLp _) f, hinv.coeFn_toLp,
      coeFn_one (R := R) (μ := μ), h] with x h₁ h₂ hx hone hδx <;>
    simp [h₁, h₂, hx, hone, norm_pos_iff.1 (hδ.trans_le hδx)]

/-- The spectrum of an element of `L^∞` is its essential range. -/
theorem spectrum_eq_essRange {𝕜 : Type*} [NormedField 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Lp 𝕜 ∞ μ) : spectrum 𝕜 f = essRange f μ := by
  ext z
  rw [spectrum.mem_iff, ← not_iff_not, not_not,
    notMem_essRange_iff (Lp.aestronglyMeasurable f).aemeasurable, isUnit_iff]
  have h : ⇑(algebraMap 𝕜 (Lp 𝕜 ∞ μ) z - f) =ᵐ[μ] fun x ↦ z - f x := by
    filter_upwards [Lp.coeFn_sub (algebraMap 𝕜 (Lp 𝕜 ∞ μ) z) f,
      coeFn_algebraMap (R := 𝕜) (μ := μ) z] with x h₁ h₂
    rw [h₁, Pi.sub_apply, h₂, Algebra.algebraMap_self_apply]
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ eventually_congr ?_
  filter_upwards [h] with x hx
  rw [hx, dist_eq_norm]

end MeasureTheory.Linfty
