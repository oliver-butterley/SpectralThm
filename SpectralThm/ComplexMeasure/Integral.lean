/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib
public import SpectralThm.VectorMeasure.FiniteDimensional

/-!
# Integral of a complex function against a complex measure

Mathlib defines the integral of `f : X → E` against a vector measure `μ : VectorMeasure X F` through
a continuous bilinear pairing `B : E →L[ℝ] F →L[ℝ] G`, written `∫ᵛ x, f x ∂[B; μ]`
(`MeasureTheory.VectorMeasure.integral`). For a complex function and a complex measure the pairing
is multiplication, `ContinuousLinearMap.mul ℝ ℂ`.

## Notation

* `∫ᶜ x, f x ∂μ`: the integral `∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]` of `f : X → ℂ` against
  `μ : ComplexMeasure X`. Scoped in `MeasureTheory.ComplexMeasure`.

## Main results

* `MeasureTheory.ComplexMeasure.integral_const_mul`: the integral is `ℂ`-linear in `f`.
* `MeasureTheory.ComplexMeasure.norm_integral_le_integral_norm`: `‖∫ f dμ‖ ≤ ∫ ‖f‖ d|μ|`.
* `MeasureTheory.ComplexMeasure.integral_simpleFunc`: `∫ s dμ = ∑ a * μ (s ⁻¹' {a})`.
* `MeasureTheory.ComplexMeasure.integrable_continuousMap`: continuous functions on a compact
  space are integrable.
* `MeasureTheory.ComplexMeasure.exists_integral_eq_of_tendsto`: a linear functional on bounded
  measurable functions satisfying bounded convergence is integration against a complex measure.

The relation with the polar decomposition, `∫ f dμ = ∫ (dμ/d|μ|) f d|μ|`, is
`MeasureTheory.ComplexMeasure.integral_eq_integral_rnDeriv` in
`SpectralThm/ComplexMeasure/RadonNikodym.lean`.

## Notes

The notation `∫ᶜ` is a stopgap. Mathlib already has notations for fixed pairings next to the
definition of the integral (`Mathlib/MeasureTheory/VectorMeasure/Integral.lean`):
`∫ᵛ x, f x ∂•μ` for a real function against a vector measure (pairing `lsmul ℝ ℝ`) and
`∫ᵛ x, f x ∂<•μ` for a vector function against a signed measure. The plan is to generalise `∂•` in
Mathlib from `ℝ` to any scalar field `𝕜`, using the pairing `lsmul ℝ 𝕜` (`f x • dμ`). Since
`lsmul ℝ ℂ = mul ℝ ℂ` as pairings on `ℂ`, `∫ᵛ x, f x ∂•μ` would then cover this file, and also
complex functions against any complex-Banach-valued measure. Once that is in Mathlib, `∫ᶜ` should be
removed in favour of it, and the lemmas here stated for `∂•` and moved to Mathlib.
-/

@[expose] public section

namespace MeasureTheory.ComplexMeasure

open ContinuousLinearMap

@[inherit_doc VectorMeasure.integral]
scoped notation3 "∫ᶜ "(...)", "r:60:(scoped f => f)" ∂"μ:70 =>
  VectorMeasure.integral μ r (ContinuousLinearMap.mul ℝ ℂ)

variable {X : Type*} {mX : MeasurableSpace X} (μ : ComplexMeasure X)

/-- The integral against a complex measure is `ℂ`-linear. -/
lemma integral_const_mul (c : ℂ) (f : X → ℂ) : ∫ᶜ x, c * f x ∂μ = c * ∫ᶜ x, f x ∂μ := by
  by_cases hf : μ.Integrable f
  · have h₁ := VectorMeasure.integral_continuousLinearMap_comp (B := mul ℝ ℂ) (μ := μ)
      (C := mul ℝ ℂ c) hf
    have h₂ := VectorMeasure.continuousLinearMap_apply_integral (B := mul ℝ ℂ) (μ := μ)
      (C := mul ℝ ℂ c) hf
    have h : mul ℝ ℂ ∘L mul ℝ ℂ c = (compL ℝ ℂ ℂ ℂ (mul ℝ ℂ c)) ∘L mul ℝ ℂ := by
      ext x y; simp [mul_assoc]
    exact (h₁.trans (h ▸ h₂.symm) :)
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    rw [VectorMeasure.integral_undef hf, VectorMeasure.integral_undef, mul_zero]
    exact fun h ↦ hf (by simpa [hc] using h.const_mul c⁻¹)

/-- `‖∫ f dμ‖ ≤ ∫ ‖f‖ d|μ|`. -/
lemma norm_integral_le_integral_norm (f : X → ℂ) :
    ‖∫ᶜ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ.variation :=
  (VectorMeasure.norm_integral_le_integral_norm ..).trans <|
    mul_le_of_le_one_left (integral_nonneg fun _ ↦ norm_nonneg _) (opNorm_mul_le ℝ ℂ)

/-- The integral of a simple function against a complex measure. -/
lemma integral_simpleFunc (s : SimpleFunc X ℂ) :
    ∫ᶜ x, s x ∂μ = ∑ a ∈ s.range, a * μ (s ⁻¹' {a}) := by
  rw [VectorMeasure.integral_eq_setToFun,
    setToFun_simpleFunc _ s (SimpleFunc.integrable_of_isFiniteMeasure s)]
  rfl

/-- A continuous function on a compact space is integrable against every complex measure. -/
lemma integrable_continuousMap {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : ComplexMeasure X) (f : C(X, ℂ)) :
    μ.Integrable f :=
  (BoundedContinuousFunction.mkOfCompact f).integrable _

section Representation

open Filter Topology

/-- A functional `L` on bounded measurable functions which is linear and satisfies the bounded
convergence theorem is the integral against a complex measure. -/
theorem exists_integral_eq_of_tendsto {X : Type*} [MeasurableSpace X] {L : (X → ℂ) → ℂ}
    (hadd : ∀ f g, Measurable f → Measurable g → (∃ C, ∀ x, ‖f x‖ ≤ C) →
      (∃ C, ∀ x, ‖g x‖ ≤ C) → L (f + g) = L f + L g)
    (hsmul : ∀ (c : ℂ) f, Measurable f → (∃ C, ∀ x, ‖f x‖ ≤ C) → L (c • f) = c * L f)
    (hlim : ∀ (f : ℕ → X → ℂ) (g : X → ℂ) (C : ℝ), (∀ n, Measurable (f n)) →
      (∀ n x, ‖f n x‖ ≤ C) → (∀ x, Tendsto (f · x) atTop (𝓝 (g x))) →
      Tendsto (fun n ↦ L (f n)) atTop (𝓝 (L g))) :
    ∃ μ : ComplexMeasure X, ∀ f, Measurable f → (∃ C, ∀ x, ‖f x‖ ≤ C) →
      ∫ᶜ x, f x ∂μ = L f := by
  classical
  -- `B f`: `f` is measurable and bounded.
  let B : (X → ℂ) → Prop := fun f ↦ Measurable f ∧ ∃ C, ∀ x, ‖f x‖ ≤ C
  have hB_ind {w : Set X} (hw : MeasurableSet w) (c : ℂ) : B (w.indicator fun _ ↦ c) :=
    ⟨measurable_const.indicator hw, ‖c‖, fun x ↦ norm_indicator_le_norm_self _ _⟩
  have hB_one {w : Set X} (hw : MeasurableSet w) : B (w.indicator 1) := hB_ind hw 1
  have hB_sum {ι : Type} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i ∈ s, B (f i)) :
      B (∑ i ∈ s, f i) := by
    refine Finset.sum_induction _ B (fun f g ⟨hf, C, hC⟩ ⟨hg, D, hD⟩ ↦ ⟨hf.add hg, C + D,
      fun x ↦ (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩) ⟨measurable_const, 0, by simp⟩ hf
  have hL_zero : L 0 = 0 := by simpa using hsmul 0 0 measurable_const ⟨0, by simp⟩
  have hL_sum {ι : Type} (s : Finset ι) {f : ι → X → ℂ} (hf : ∀ i ∈ s, B (f i)) :
      L (∑ i ∈ s, f i) = ∑ i ∈ s, L (f i) := by
    induction s using Finset.induction_on with
    | empty => simp [hL_zero]
    | insert i s hi ih =>
      have hs : ∀ j ∈ s, B (f j) := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
      obtain ⟨hfi, hfiC⟩ := hf i (Finset.mem_insert_self i s)
      obtain ⟨hsum, hsumC⟩ := hB_sum s hs
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd _ _ hfi hsum hfiC hsumC, ih hs]
  let m : Set X → ℂ := fun w ↦ if MeasurableSet w then L (w.indicator 1) else 0
  have hm {w : Set X} (hw : MeasurableSet w) : m w = L (w.indicator 1) :=
    ite_eq_left_iff.2 fun h ↦ absurd hw h
  let μ : ComplexMeasure X :=
    { measureOf' := m
      empty' := (hm .empty).trans (by rw [Set.indicator_empty]; exact hL_zero)
      not_measurable' := fun w hw ↦ ite_eq_right_iff.2 fun h ↦ absurd h hw
      m_iUnion' := fun w hw hd ↦ by
        have hsum (s : Finset ℕ) :
            ∑ i ∈ s, m (w i) = L ((⋃ i ∈ s, w i).indicator 1) := by
          rw [Finset.indicator_biUnion _ _ fun i _ j _ hij ↦ hd hij]
          simp_rw [hm (hw _)]
          rw [← hL_sum s fun i _ ↦ hB_one (hw i)]
          congr 1
          ext x
          simp
        rw [hm (.iUnion hw), HasSum]
        simp_rw [hsum]
        refine tendsto_of_seq_tendsto fun u hu ↦ hlim _ _ 1
          (fun n ↦ measurable_one.indicator (Finset.measurableSet_biUnion _ fun i _ ↦ hw i))
          (fun n x ↦ ?_) fun x ↦ ?_
        · simpa using norm_indicator_le_norm_self (1 : X → ℂ) x
        · exact ((tendsto_indicator_biUnion_finset w 1 x).comp hu).mono_right (pure_le_nhds _) }
  have hsimple (s : SimpleFunc X ℂ) : ∫ᶜ x, s x ∂μ = L s := by
    have hs : (s : X → ℂ) = ∑ c ∈ s.range, (s ⁻¹' {c}).indicator fun _ ↦ c := by
      funext x
      rw [Finset.sum_apply, Finset.sum_eq_single (s x)]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · exact fun h ↦ absurd (s.mem_range_self x) h
    rw [integral_simpleFunc]
    conv_rhs => rw [hs, hL_sum _ fun c _ ↦ hB_ind (s.measurableSet_preimage _) c]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    have hc : ((s ⁻¹' {c}).indicator fun _ ↦ c) = c • (s ⁻¹' {c}).indicator 1 := by
      ext x
      by_cases hx : s x = c <;> simp [hx]
    obtain ⟨hc₁, hc₂⟩ := hB_one (s.measurableSet_preimage {c})
    rw [hc, hsmul _ _ hc₁ hc₂]
    exact congrArg (c * ·) (hm (s.measurableSet_preimage _))
  refine ⟨μ, fun f hf ⟨C, hC⟩ ↦ ?_⟩
  have hC' (x : X) : ‖f x‖ ≤ max C 0 := (hC x).trans (le_max_left _ _)
  let s := hf.stronglyMeasurable.approxBounded (max C 0)
  have hs_le : ∀ n x, ‖s n x‖ ≤ max C 0 :=
    hf.stronglyMeasurable.norm_approxBounded_le (le_max_right _ _)
  have hs_lim (x : X) : Tendsto (fun n ↦ s n x) atTop (𝓝 (f x)) :=
    hf.stronglyMeasurable.tendsto_approxBounded_of_norm_le (hC' x)
  refine tendsto_nhds_unique ?_ (hlim (fun n ↦ s n) f _ (fun n ↦ (s n).measurable) hs_le hs_lim)
  simp_rw [← hsimple]
  exact VectorMeasure.tendsto_integral_filter_of_norm_le_const
    (.of_forall fun n ↦ (s n).aestronglyMeasurable) ⟨_, .of_forall fun n ↦ ae_of_all _ (hs_le n)⟩
    (ae_of_all _ hs_lim)

end Representation

end MeasureTheory.ComplexMeasure
