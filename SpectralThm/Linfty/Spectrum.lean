/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.Linfty.Algebra

/-!
# The spectrum in `L^∞`

The spectrum of `f` in the C⋆-algebra `Lp ℂ ∞ μ` is its essential range.

## Main results

* `MeasureTheory.Measure.notMem_essRange_iff`: `z` is not in the essential range of `f` iff `f`
  stays a positive distance away from `z` almost everywhere.
* `MeasureTheory.Measure.ae_mem_essRange`: `f` takes values in its essential range a.e.
* `MeasureTheory.Measure.essRange_subset_closure_range`: the essential range is contained in the
  closure of the range.
* `MeasureTheory.Linfty.isUnit_iff`: `f` is invertible in `L^∞` iff `|f|` is bounded away from
  `0` almost everywhere.
* `MeasureTheory.Linfty.spectrum_eq_essRange`: the spectrum of `f` in `L^∞` is its essential
  range.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} {mX : MeasurableSpace X} {μ : Measure X}

/-! ### The essential range -/

namespace Measure

variable {Y : Type*} [MeasurableSpace Y] {f : X → Y}

/-- A function takes values in its essential range almost everywhere. -/
lemma ae_mem_essRange [TopologicalSpace Y] [HereditarilyLindelofSpace Y] (hf : AEMeasurable f μ) :
    ∀ᵐ x ∂μ, f x ∈ μ.essRange f :=
  ae_of_ae_map hf support_mem_ae

/-- `z` is not in the essential range of `f` iff `f` stays a positive distance away from `z`
almost everywhere. -/
lemma notMem_essRange_iff [PseudoMetricSpace Y] [OpensMeasurableSpace Y] (hf : AEMeasurable f μ)
    {z : Y} : z ∉ μ.essRange f ↔ ∃ δ > 0, ∀ᵐ x ∂μ, δ ≤ dist z (f x) := by
  have key (δ : ℝ) : map f μ (Metric.ball z δ) = 0 ↔ ∀ᵐ x ∂μ, δ ≤ dist z (f x) := by
    rw [map_apply_of_aemeasurable hf measurableSet_ball, measure_eq_zero_iff_ae_notMem]
    simp [dist_comm]
  rw [essRange, notMem_support_iff_exists]
  constructor
  · rintro ⟨U, hU, hU0⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
    exact ⟨δ, hδ, (key δ).1 (measure_mono_null hδU hU0)⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨_, Metric.ball_mem_nhds z hδ, (key δ).2 h⟩

/-- The essential range of `f` is contained in the closure of its range. -/
lemma essRange_subset_closure_range [TopologicalSpace Y] [OpensMeasurableSpace Y]
    (hf : AEMeasurable f μ) : μ.essRange f ⊆ closure (Set.range f) :=
  support_subset_of_isClosed isClosed_closure <| (mem_ae_map_iff hf
    isClosed_closure.measurableSet).2 <| univ_mem' fun x ↦ subset_closure (Set.mem_range_self x)

end Measure

/-! ### The spectrum in `L^∞` -/

namespace Linfty

variable {𝕜 : Type*} [NormedField 𝕜]

lemma coeFn_algebraMap (c : 𝕜) : ⇑(algebraMap 𝕜 (Lp 𝕜 ∞ μ) c) =ᵐ[μ] fun _ ↦ c := by
  rw [Algebra.algebraMap_eq_smul_one]
  filter_upwards [Lp.coeFn_smul c (1 : Lp 𝕜 ∞ μ), coeFn_one (R := 𝕜) (μ := μ)] with x h₁ h₂
  simp [h₁, h₂]

/-- An element of `L^∞` is invertible iff its absolute value is bounded away from `0` almost
everywhere. -/
lemma isUnit_iff {f : Lp 𝕜 ∞ μ} : IsUnit f ↔ ∃ δ > 0, ∀ᵐ x ∂μ, δ ≤ ‖f x‖ := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨(‖(↑u⁻¹ : Lp 𝕜 ∞ μ)‖ + 1)⁻¹, by positivity, ?_⟩
    filter_upwards [Linfty.coeFn_mul (↑u⁻¹ : Lp 𝕜 ∞ μ) u, coeFn_one (R := 𝕜) (μ := μ),
      Lp.ae_norm_le_norm (↑u⁻¹ : Lp 𝕜 ∞ μ)] with x hmul hone hle
    rw [Units.inv_mul, hone, Pi.mul_apply] at hmul
    have h₁ : 1 = ‖(↑u⁻¹ : Lp 𝕜 ∞ μ) x‖ * ‖(u : Lp 𝕜 ∞ μ) x‖ := by
      rw [← norm_mul, ← hmul, Pi.one_apply, norm_one]
    have h₀ : 0 < ‖(u : Lp 𝕜 ∞ μ) x‖ := by
      refine norm_pos_iff.2 fun h ↦ ?_
      simp [h] at h₁
    rw [inv_le_iff_one_le_mul₀' (by positivity), h₁]
    nlinarith
  · rintro ⟨δ, hδ, h⟩
    have hinv : MemLp (fun x ↦ (f x)⁻¹) ∞ μ := by
      refine memLp_top_of_bound (Lp.aestronglyMeasurable f).inv₀ δ⁻¹ ?_
      filter_upwards [h] with x hx
      rw [norm_inv]
      exact inv_anti₀ hδ hx
    refine .of_mul_eq_one (hinv.toLp _) (Lp.ext ?_)
    filter_upwards [Linfty.coeFn_mul f (hinv.toLp _), hinv.coeFn_toLp,
      coeFn_one (R := 𝕜) (μ := μ), h] with x hmul hx hone hδx
    rw [hmul, hone, Pi.mul_apply, hx, mul_inv_cancel₀ (norm_pos_iff.1 (hδ.trans_le hδx))]
    rfl

/-- The spectrum of an element of `L^∞` is its essential range. -/
theorem spectrum_eq_essRange (f : Lp ℂ ∞ μ) : spectrum ℂ f = μ.essRange f := by
  ext z
  rw [spectrum.mem_iff, ← not_iff_not, not_not,
    Measure.notMem_essRange_iff (Lp.aestronglyMeasurable f).aemeasurable, isUnit_iff]
  have h : ⇑(algebraMap ℂ (Lp ℂ ∞ μ) z - f) =ᵐ[μ] fun x ↦ z - f x := by
    filter_upwards [Lp.coeFn_sub (algebraMap ℂ (Lp ℂ ∞ μ) z) f, coeFn_algebraMap (μ := μ) z]
      with x h₁ h₂
    rw [h₁, Pi.sub_apply, h₂]
  refine exists_congr fun δ ↦ and_congr_right fun _ ↦ ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · filter_upwards [h, h'] with x hx hx'
    rwa [dist_eq_norm, ← hx]
  · filter_upwards [h, h'] with x hx hx'
    rwa [hx, ← dist_eq_norm]

end Linfty

end MeasureTheory
