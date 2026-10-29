/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import SpectralThm.BorelFunctionalCalculus

/-!
# The spectrum of `f(a)` in the Borel functional calculus

For a normal operator `a` with spectral measure `E` and `f` in `L^∞(E)`, the spectrum of the
operator `f(a) = ∫ f dE` is the essential range of `f` (Rudin 12.24-style spectral mapping). As a
consequence, the continuous functional calculus of `f(a)` is the Borel functional calculus of
`a` composed with `f`.

## Main results

* `MeasureTheory.Measure.notMem_essRange_iff`: `z` is not in the essential range of `f` iff `f`
  stays a positive distance away from `z` almost everywhere.
* `MeasureTheory.Measure.ae_mem_essRange`: `f` takes values in its essential range a.e.
* `MeasureTheory.Linfty.isUnit_iff`: `f` is invertible in `L^∞` iff `|f|` is bounded away from
  `0` almost everywhere.
* `MeasureTheory.Linfty.spectrum_eq_essRange`: the spectrum of `f` in `L^∞` is its essential
  range.
* `ProjectionValuedMeasure.spectrum_integral`: `σ(∫ f dE) = σ(f)`, the spectrum in `L^∞(E)`.
* `IsStarNormal.spectrum_bfc`: `σ(f(a))` is the essential range of `f` on `σ(a)` with respect
  to `E`.
* `IsStarNormal.spectrum_bfc_subset_closure_image`: `σ(f(a)) ⊆ closure (f '' σ(a))`.
* `IsStarNormal.cfc_bfc`: `g(f(a)) = (g ∘ f)(a)` for `g` continuous on `σ(f(a))`.
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

/-! ### The spectrum of the integral against a projection-valued measure -/

namespace ProjectionValuedMeasure

variable {X : Type*} {mX : MeasurableSpace X}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ProjectionValuedMeasure X H)

/-- The spectrum of `∫ f dE` is the spectrum of `f` in `L^∞(E)`, since the integral is an
injective `*`-homomorphism with closed range (spectral permanence). -/
theorem spectrum_integral (f : E.Linfty) : spectrum ℂ (E.integral f) = spectrum ℂ f := by
  have : IsClosed (E.integral.range : Set (H →L[ℂ] H)) := E.isClosed_range_integral
  rw [← AlgEquiv.spectrum_eq (StarAlgEquiv.ofInjective E.integral
    E.isometry_integral.injective) f, StarSubalgebra.spectrum_eq]
  rfl

/-- The spectrum of `∫ f dE` is the essential range of `f` with respect to `E`. -/
theorem spectrum_integral_eq_essRange (f : E.Linfty) :
    spectrum ℂ (E.integral f) = E.measure.essRange f := by
  rw [spectrum_integral, Linfty.spectrum_eq_essRange]

end ProjectionValuedMeasure

/-! ### The spectrum of `f(a)` -/

namespace IsStarNormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsStarNormal a) {f : ℂ → ℂ}
  (hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure)
include hf

/-- **Spectral mapping** for the Borel functional calculus: `σ(f(a))` is the essential range of
`f` on `σ(a)` with respect to the spectral measure. -/
theorem spectrum_bfc :
    spectrum ℂ (ha.bfc f) =
      ha.spectralMeasure.measure.essRange (fun z : spectrum ℂ a ↦ f z) := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.spectrum_integral_eq_essRange,
    Measure.essRange_eq_of_ae_eq _ _ hf.coeFn_toLp]

/-- `f` takes values in `σ(f(a))` almost everywhere with respect to the spectral measure. -/
lemma ae_mem_spectrum_bfc :
    ∀ᵐ z : spectrum ℂ a ∂ha.spectralMeasure.measure, f z ∈ spectrum ℂ (ha.bfc f) := by
  rw [ha.spectrum_bfc hf]
  exact Measure.ae_mem_essRange hf.aestronglyMeasurable.aemeasurable

/-- `σ(f(a))` is contained in the closure of `f(σ(a))`. -/
lemma spectrum_bfc_subset_closure_image :
    spectrum ℂ (ha.bfc f) ⊆ closure (f '' spectrum ℂ a) := by
  rw [ha.spectrum_bfc hf, Set.image_eq_range]
  exact Measure.essRange_subset_closure_range hf.aestronglyMeasurable.aemeasurable

/-! ### Composition with the continuous functional calculus -/

section Comp

open Function

omit hf in
private lemma norm_extend_val_le {S : Set ℂ} [CompactSpace S] (k : C(S, ℂ)) (w : ℂ) :
    ‖extend Subtype.val k 0 w‖ ≤ ‖k‖ := by
  by_cases hw : w ∈ S
  · rw [extend_val_apply hw]
    exact k.norm_coe_le_norm _
  · simp [extend_val_apply' hw]

private lemma memLp_extend_val (k : C(spectrum ℂ (ha.bfc f), ℂ)) :
    MemLp (fun z : spectrum ℂ a ↦ extend Subtype.val k 0 (f z)) ∞ ha.spectralMeasure.measure := by
  refine memLp_top_of_bound ?_ ‖k‖ (ae_of_all _ fun _ ↦ norm_extend_val_le k _)
  exact (((MeasurableEmbedding.subtype_coe (spectrum.isClosed _).measurableSet).measurable_extend
    k.continuous.measurable measurable_const).comp_aemeasurable
    hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable

/-- The `*`-homomorphism `k ↦ (k ∘ f)(a)` from `C(σ(f(a)), ℂ)`; it is `cfcHom` (see `cfc_bfc`). -/
private noncomputable def bfcCompHom : C(spectrum ℂ (ha.bfc f), ℂ) →⋆ₐ[ℂ] H →L[ℂ] H where
  toFun k := ha.bfc fun z ↦ extend Subtype.val k 0 (f z)
  map_one' := by
    rw [← ha.bfc_const_one]
    refine ha.bfc_congr_ae ?_
    filter_upwards [ha.ae_mem_spectrum_bfc hf] with z hz
    rw [extend_val_apply hz]
    rfl
  map_mul' k l := by
    rw [← ha.bfc_mul (ha.memLp_extend_val hf k) (ha.memLp_extend_val hf l)]
    refine ha.bfc_congr fun w _ ↦ ?_
    by_cases hw : f w ∈ spectrum ℂ (ha.bfc f) <;> simp [extend_val_apply, hw]
  map_zero' := by
    rw [← ha.bfc_const_zero]
    refine ha.bfc_congr fun w _ ↦ ?_
    by_cases hw : f w ∈ spectrum ℂ (ha.bfc f) <;> simp [extend_val_apply, hw]
  map_add' k l := by
    rw [← ha.bfc_add (ha.memLp_extend_val hf k) (ha.memLp_extend_val hf l)]
    refine ha.bfc_congr fun w _ ↦ ?_
    by_cases hw : f w ∈ spectrum ℂ (ha.bfc f) <;> simp [extend_val_apply, hw]
  commutes' c := by
    rw [← ha.bfc_const]
    refine ha.bfc_congr_ae ?_
    filter_upwards [ha.ae_mem_spectrum_bfc hf] with z hz
    rw [extend_val_apply hz]
    rfl
  map_star' k := by
    rw [← ha.bfc_star (ha.memLp_extend_val hf k)]
    refine ha.bfc_congr fun w _ ↦ ?_
    by_cases hw : f w ∈ spectrum ℂ (ha.bfc f) <;> simp [extend_val_apply, hw]

private lemma bfcCompHom_apply (k : C(spectrum ℂ (ha.bfc f), ℂ)) :
    ha.bfcCompHom hf k = ha.bfc fun z ↦ extend Subtype.val k 0 (f z) :=
  rfl

/-- The continuous functional calculus of `f(a)` is the Borel functional calculus of `a`
composed with `f`: `g(f(a)) = (g ∘ f)(a)` for `g` continuous on `σ(f(a))`. -/
theorem cfc_bfc {g : ℂ → ℂ} (hg : ContinuousOn g (spectrum ℂ (ha.bfc f))) :
    cfc g (ha.bfc f) = ha.bfc (fun z ↦ g (f z)) := by
  have hcont : Continuous (ha.bfcCompHom hf) :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun k ↦ by
      simpa [bfcCompHom_apply] using ha.norm_bfc_le (norm_nonneg k) fun _ _ ↦ norm_extend_val_le k _
  have hid : ha.bfcCompHom hf (.restrict (spectrum ℂ (ha.bfc f)) (.id ℂ)) = ha.bfc f := by
    rw [bfcCompHom_apply]
    refine ha.bfc_congr_ae ?_
    filter_upwards [ha.ae_mem_spectrum_bfc hf] with z hz
    rw [extend_val_apply hz]
    rfl
  rw [cfc_apply g (ha.bfc f), cfcHom_eq_of_continuous_of_map_id _ _ hcont hid, bfcCompHom_apply]
  refine ha.bfc_congr_ae ?_
  filter_upwards [ha.ae_mem_spectrum_bfc hf] with z hz
  rw [extend_val_apply hz]
  rfl

end Comp

end IsStarNormal
