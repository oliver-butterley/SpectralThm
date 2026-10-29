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

* `IsStarNormal.spectrum_bfc`: `σ(f(a))` is the essential range of `f` on `σ(a)` with respect
  to `E`.
* `IsStarNormal.spectrum_bfc_subset_closure_image`: `σ(f(a)) ⊆ closure (f '' σ(a))`.
* `IsStarNormal.isUnit_bfc_iff`, `IsStarNormal.bfc_inv`: `f(a)` is invertible iff `|f|` is
  essentially bounded below on `σ(a)`, and then `f(a)⁻¹ = f⁻¹(a)`.
* `IsStarNormal.cfc_bfc`: `g(f(a)) = (g ∘ f)(a)` for `g` continuous on `σ(f(a))`.
* `IsStarNormal.bfc_comp`: `(g ∘ f)(a) = g(f(a))` for `f` bounded measurable on `σ(a)` and `g`
  bounded measurable on `σ(f(a))`, both in the Borel functional calculus.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

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
      essRange (fun z : spectrum ℂ a ↦ f z) ha.spectralMeasure.measure := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.spectrum_integral_eq_essRange,
    essRange_congr_ae hf.coeFn_toLp]

/-- `f` takes values in `σ(f(a))` almost everywhere with respect to the spectral measure. -/
lemma ae_mem_spectrum_bfc :
    ∀ᵐ z : spectrum ℂ a ∂ha.spectralMeasure.measure, f z ∈ spectrum ℂ (ha.bfc f) := by
  rw [ha.spectrum_bfc hf]
  exact ae_mem_essRange hf.aestronglyMeasurable.aemeasurable

/-- `σ(f(a))` is contained in the closure of `f(σ(a))`. -/
lemma spectrum_bfc_subset_closure_image :
    spectrum ℂ (ha.bfc f) ⊆ closure (f '' spectrum ℂ a) := by
  rw [ha.spectrum_bfc hf, Set.image_eq_range]
  exact essRange_subset_closure_range hf.aestronglyMeasurable.aemeasurable

/-- `f(a)` is invertible iff `|f|` is `E`-a.e. bounded below by a positive constant on `σ(a)`. -/
lemma isUnit_bfc_iff :
    IsUnit (ha.bfc f) ↔ ∃ δ > 0, ∀ᵐ z : spectrum ℂ a ∂ha.spectralMeasure.measure, δ ≤ ‖f z‖ := by
  rw [← spectrum.zero_notMem_iff ℂ, ha.spectrum_bfc hf,
    notMem_essRange_iff hf.aestronglyMeasurable.aemeasurable]
  simp

/-- If `f(a)` is invertible, its inverse is `f⁻¹(a)`. -/
lemma bfc_inv (h : IsUnit (ha.bfc f)) :
    ha.bfc (fun z ↦ (f z)⁻¹) = Ring.inverse (ha.bfc f) := by
  obtain ⟨δ, hδ, hfδ⟩ := (ha.isUnit_bfc_iff hf).1 h
  have hinv : MemLp (fun z : spectrum ℂ a ↦ (f z)⁻¹) ∞ ha.spectralMeasure.measure := by
    refine memLp_top_of_bound hf.aestronglyMeasurable.aemeasurable.inv.aestronglyMeasurable δ⁻¹ ?_
    filter_upwards [hfδ] with z hz
    rw [norm_inv]
    exact inv_anti₀ hδ hz
  have hmul : ha.bfc (fun z ↦ (f z)⁻¹) * ha.bfc f = 1 := by
    rw [← ha.bfc_mul hinv hf, ← ha.bfc_const_one]
    refine ha.bfc_congr_ae ?_
    filter_upwards [hfδ] with z hz
    exact inv_mul_cancel₀ (norm_pos_iff.1 (hδ.trans_le hz))
  rw [← one_mul (Ring.inverse _), ← hmul, mul_assoc, Ring.mul_inverse_cancel _ h, mul_one]

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

/-! ### Composition -/

section BorelComp

variable {g : ℂ → ℂ}

omit hf in
/-- Composition in the Borel functional calculus: `(g ∘ f)(a) = g(f(a))` for `f` measurable and
bounded on `σ(a)` and `g` measurable and bounded on `σ(f(a))`. This follows from the uniqueness
theorem `eq_bfc` applied to `f(a)` and `g ↦ (g ∘ f)(a)`. -/
theorem bfc_comp (hf : Measurable f) {C : ℝ} (hC : ∀ z ∈ spectrum ℂ a, ‖f z‖ ≤ C)
    (hg : Measurable g) {D : ℝ} (hD : ∀ z ∈ spectrum ℂ (ha.bfc f), ‖g z‖ ≤ D) :
    ha.bfc (fun z ↦ g (f z)) = (ha.isStarNormal_bfc f).bfc g := by
  have hfL := ha.memLp_of_bound hf hC
  have hcomp {k : ℂ → ℂ} (hk : Measurable k) (hkC : ∃ C, ∀ z, ‖k z‖ ≤ C) :
      MemLp (fun z : spectrum ℂ a ↦ k (f z)) ∞ ha.spectralMeasure.measure :=
    ha.memLp_of_bound (hk.comp hf) fun z _ ↦ hkC.choose_spec (f z)
  refine (ha.isStarNormal_bfc f).eq_bfc (Φ := fun k ↦ ha.bfc fun z ↦ k (f z)) ?_ ?_ ?_ ?_ hg hD
  · intro k k' hk hk' hkC hk'C
    exact ha.bfc_add (hcomp hk hkC) (hcomp hk' hk'C)
  · intro c k hk hkC
    exact ha.bfc_smul (hcomp hk hkC) c
  · intro k hk
    exact (ha.cfc_bfc hfL hk.continuousOn).symm
  · intro k k₀ C' hk hk₀ hkC hlim x y
    have hmem := ha.ae_mem_spectrum_bfc hfL
    have hk₀L : MemLp (fun z : spectrum ℂ a ↦ k₀ (f z)) ∞ ha.spectralMeasure.measure := by
      refine memLp_top_of_bound ((hk₀.comp hf).comp measurable_subtype_coe).aestronglyMeasurable
        C' ?_
      filter_upwards [hmem] with z hz
      exact le_of_tendsto' (hlim (f z) hz).norm fun n ↦ hkC n _
    exact tendsto_const_nhds.inner (ha.tendsto_bfc_apply_of_ae (f := fun n z ↦ k n (f z))
      (g := fun z ↦ k₀ (f z)) (fun n ↦ hcomp (hk n) ⟨C', hkC n⟩) hk₀L
      (.of_forall fun n ↦ ae_of_all _ fun _ ↦ hkC n _) (hmem.mono fun z hz ↦ hlim (f z) hz) y)

end BorelComp

end IsStarNormal
