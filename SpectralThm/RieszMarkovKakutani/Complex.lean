/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib
public import SpectralThm.ComplexMeasure.Integral

/-!
# Riesz–Markov–Kakutani representation theorem for complex linear functionals

This file contains the proof of the **Riesz Representations Theorem** a.k.a.
**Riesz–Markov–Kakutani theorem** (complex case).

## Main definition

* `ComplexRMK.rieszMeasure (Φ : C₀(X, ℂ) →L[ℂ] ℂ)` the `ComplexMeasure` associated to the linear
functional`Φ`.

## Main results

* `rieszMeasure_unique`: uniqueness of  `ComplexRMK.rieszMeasure`.
* `integral_rieszMeasure`: that integration with respect to `ComplexRMK.rieszMeasure` is equal to
the action of the linear functional.

## Overview

Firstly the uniqueness of measures satisfying the represenation equation is proven.

The proof of existence of such a measures takes advantage of the corresponding statement for
`ℝ`-valued linear functionals and signed measures (see
`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`). As such, a major part of the
argument is to reduce the complex situation to the case of a `ℝ`-valued linear functional. Moreover
the required measure can be defined using the measure obtained in the `ℝ`-valued linear functional
case.


## Notes

* File destination: `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Complex.lean`

## References

* Section 6 of [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

- Rudin 6.4 `IsFiniteMeasure μ.variation`
- Rudin 6.5 `NormedAddCommGroup` instance for `ComplexMeasure X`
(- Rudin 6.9 lemma, not needed?)
- Rudin 6.12 polar decomposition `exists_l1_eq_withDensity_variation`
- Rudin 6.13, `MeasureTheory.Measure.variation_withDensityᵥ`
- Rudin 6.16: Duality of `L^1` and `L^∞` (not in Mathlib
[https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Lp.20duality/near/495207025])
- Rudin 6.19
* the existence of `Λ`
* take the realRMK measure `λ` associated to `Λ`
* take `g` by duality
* define the  measure `μ` by `dμ = g dλ`
* uniqueness
-/

@[expose] public section

open NNReal ENNReal
open ZeroAtInfty MeasureTheory CompactlySupported CompactlySupportedContinuousMap

namespace ComplexRMK

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

-- TODO
-- move ComplexMeasure in VectorMeasure
-- separate things about SignedMeasure in Basic in a separate file
-- counterexample: a L^∞ valued measure whose variation is not finite?
-- make a folder VectorMeasure/SignedMeasure, make a file Basic, a folder Decomposition

-- Rudin 6.4
instance (μ : ComplexMeasure X) : IsFiniteMeasure μ.variation := sorry

-- Rudin 6.5

@[simp] lemma variation_zero_iff_univ {V : Type*} [NormedAddCommGroup V] {μ : VectorMeasure X V} :
    μ.variation Set.univ = 0 ↔ μ = 0 := by
  simp

noncomputable instance {V : Type*} [NormedAddCommGroup V] : EMetricSpace (VectorMeasure X V) where
  edist μ ν := (μ - ν).variation Set.univ
  edist_self := by intro; simp
  edist_comm := by
    intro _ _
    rw [← MeasureTheory.VectorMeasure.variation_neg]
    simp
  edist_triangle := by
    intro x y z
    simpa using Measure.le_iff.mp (VectorMeasure.variation_add_le (μ := x - y) (ν := y - z))
      Set.univ MeasurableSet.univ
  eq_of_edist_eq_zero {x y} h := by
    rw [variation_zero_iff_univ] at h
    exact eq_of_sub_eq_zero h

lemma edist_eq_variation_sub {V : Type*} [NormedAddCommGroup V] (μ ν : VectorMeasure X V) :
    edist μ ν = (μ - ν).variation Set.univ := by rfl

noncomputable instance {V : Type*} [NormedAddCommGroup V] :
    ENormedAddCommMonoid (VectorMeasure X V) where
  enorm μ := μ.variation Set.univ
  continuous_enorm := by
    have : Continuous (fun x : VectorMeasure X V ↦ edist x 0) := by
      continuity
    simpa [edist_eq_variation_sub, sub_zero] using this
  enorm_zero := by simp
  enorm_add_le x y := by
    simpa using Measure.le_iff.mp (VectorMeasure.variation_add_le (μ := x) (ν := y)) Set.univ
      MeasurableSet.univ
  enorm_eq_zero x := variation_zero_iff_univ

-- Rudin 6.12 polar decomposition

theorem ComplexMeasure.ext (μ ν : ComplexMeasure X) : μ.re = ν.re → μ.im = ν.im → μ = ν := by
  intro hre him
  apply Equiv.injective ComplexMeasure.equivSignedMeasure
  simp [hre, him]

theorem ComplexMeasure.ext_iff (μ ν : ComplexMeasure X) : μ = ν ↔ (μ.re = ν.re ∧ μ.im = ν.im) :=
  ⟨fun h ↦ by constructor <;> rw [h], fun h ↦ ComplexMeasure.ext μ ν h.1 h.2⟩

theorem re_withDensityᵥ_eq {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ):
    ComplexMeasure.re (μ.withDensityᵥ f) = μ.withDensityᵥ (Complex.re ∘ f) := by
  ext E hE
  rw [ComplexMeasure.re_apply,
    MeasureTheory.VectorMeasure.mapRange_apply (μ.withDensityᵥ f) Complex.continuous_re,
    MeasureTheory.withDensityᵥ_apply hf hE, LinearMap.toAddMonoidHom_coe, Complex.reLm_coe,
    ← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hf.integrableOn,
    MeasureTheory.withDensityᵥ_apply (f := Complex.re ∘ f)
      (Complex.reCLM.integrable_comp hf) hE]
  simp

theorem im_withDensityᵥ_eq {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ):
    ComplexMeasure.im (μ.withDensityᵥ f) = μ.withDensityᵥ (Complex.im ∘ f) := by
  ext E hE
  rw [ComplexMeasure.im_apply,
    MeasureTheory.VectorMeasure.mapRange_apply (μ.withDensityᵥ f) Complex.continuous_im,
    MeasureTheory.withDensityᵥ_apply hf hE, LinearMap.toAddMonoidHom_coe, Complex.imLm_coe,
    ← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hf.integrableOn,
    MeasureTheory.withDensityᵥ_apply (f := Complex.im ∘ f)
      (Complex.imCLM.integrable_comp hf) hE]
  simp

theorem re_rnDeriv_eq_rnDeriv_re (v : ComplexMeasure X) (μ : Measure X) :
    Complex.re ∘ (v.rnDeriv μ) = v.re.rnDeriv μ := by rfl

theorem im_rnDeriv_eq_rnDeriv_im (v : ComplexMeasure X) (μ : Measure X) :
    Complex.im ∘ (v.rnDeriv μ) = v.im.rnDeriv μ := by rfl

theorem absolutelyContinuous_re {v : ComplexMeasure X} {μ : Measure X}
    (h : v ≪ᵥ μ.toENNRealVectorMeasure) : v.re ≪ᵥ μ.toENNRealVectorMeasure := by
  intro E hE
  rw [ComplexMeasure.re_apply, VectorMeasure.mapRange_apply v Complex.continuous_re]
  simp [LinearMap.toAddMonoidHom_coe, Complex.reLm_coe, h hE]

theorem absolutelyContinuous_im {v : ComplexMeasure X} {μ : Measure X}
    (h : v ≪ᵥ μ.toENNRealVectorMeasure) : v.im ≪ᵥ μ.toENNRealVectorMeasure := by
  intro E hE
  rw [ComplexMeasure.im_apply, VectorMeasure.mapRange_apply v Complex.continuous_im]
  simp [LinearMap.toAddMonoidHom_coe, Complex.imLm_coe, h hE]

theorem MeasureTheory.ComplexMeasure.withDensityᵥ_rnDeriv_eq {v : ComplexMeasure X} {μ : Measure X}
    [SigmaFinite μ] (h : v ≪ᵥ μ.toENNRealVectorMeasure) :
    μ.withDensityᵥ (v.rnDeriv μ) = v := by
  apply ComplexMeasure.ext
  · rw [re_withDensityᵥ_eq (ComplexMeasure.integrable_rnDeriv v μ), re_rnDeriv_eq_rnDeriv_re]
    exact MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (absolutelyContinuous_re h)
  · rw [im_withDensityᵥ_eq (ComplexMeasure.integrable_rnDeriv v μ), im_rnDeriv_eq_rnDeriv_im]
    exact MeasureTheory.SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ (absolutelyContinuous_im h)

theorem absolutelyContinuous_variation {V : Type} [TopologicalSpace V] [ENormedAddCommMonoid V]
    [T2Space V] (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro E hE
  by_cases hEm : MeasurableSet E
  · rw [MeasureTheory.VectorMeasure.ennrealVariation_apply _ hEm] at hE
    rw [← enorm_eq_zero, ← le_zero_iff, ← hE]
    exact VectorMeasure.enorm_measure_le_variation μ E
  · exact VectorMeasure.not_measurable μ hEm

theorem withDensityᵥ_variation_rnDeriv_eq (μ : ComplexMeasure X) :
    μ.variation.withDensityᵥ (μ.rnDeriv μ.variation) = μ :=
  MeasureTheory.ComplexMeasure.withDensityᵥ_rnDeriv_eq <| absolutelyContinuous_variation μ

theorem exists_l1_eq_withDensity_variation (μ : ComplexMeasure X) :
    μ.rnDeriv μ.variation =ᵐ[μ.variation] 1 := by
  let A : ℝ≥0 → Set X := fun r ↦ {x | ‖μ.rnDeriv μ.variation x‖ < r}
  sorry

lemma eq_zero_of_integral_eq_zero {μ: ComplexMeasure X} (h : ∀ f : C₀(X, ℂ), μ.integral f = 0) :
    μ = 0 := by
  -- [Rudin 87, Theorem 6.19]
  -- Suppose `μ` is a regular complex Borel measure on `X`
  -- and that `∫ f dμ = 0` for all `f \in C_0(X)`.
  -- *Theorem 6.12* gives a Borel function `h`, such that `|h| = 1` and `dμ = h d|μ|`.
  -- For any sequence `{f_n}` in `C_0(X)` we then have
  -- `|μ|(X) = \int_X (\bar{h} - f_n) h`, `d|μ| ≤ \int_X |\bar{h} - f_n| \, d|μ|`.
  -- Since `C_c(X)` is dense in `L^1(|μ|)` (*Theorem 3.14*), `\{f_n\}` can be
  -- so chosen that the last expression in the above tends to 0 as `n → \infty`.
  -- Thus `|μ|(X) = 0`, and `μ = 0`.
  -- (Theorem 3.14: compactly supported continuous functions are dense in `L^p`,
  -- depends on 3.13 `MeasureTheory.Lp.simpleFunc.isDenseEmbedding`, this is written only for
  -- `NormalSpace α` and approximation given by bounded functions)
  -- It is easy to see that the difference of two regular complex Borel measures on `X` is regular.
  sorry

/-- Uniqueness of `ComplexRMK.rieszMeasure`: Let `Φ` be a linear functional on `C_0(X, ℂ)`. Suppose
that `μ`, `μ'` are complex Borel measures such that, `∀ f : C_0(X, ℂ)`, `Φ f = ∫ x, f x ∂μ` and
`Φ f = ∫ x, f x ∂μ'`. Then `μ = μ'`. -/
theorem rieszMeasure_unique {μ₁ μ₂ : ComplexMeasure X} (Φ : C₀(X, ℂ) →L[ℂ] ℂ)
    (h₁ : ∀ f : C₀(X, ℂ), μ₁.integral f = Φ f) (h₂ : ∀ f : C₀(X, ℂ), μ₂.integral f = Φ f):
    μ₁ = μ₂ := by
  let μ := μ₁ - μ₂
  suffices μ = 0 by exact eq_of_sub_eq_zero this
  refine eq_zero_of_integral_eq_zero (fun f ↦ ?_)
  calc μ.integral f
    _ = (μ₁ - μ₂).integral f := by rfl
    _ = μ₁.integral f - μ₂.integral f := by exact ComplexMeasure.integral_sub _ _ _
    _ = Φ f - Φ f := by rw [h₁, h₂]
    _ = 0 := by exact sub_self _

variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

noncomputable def _root_.CompactlySupportedContinuousMap.compNorm (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toContinuousMap := ⟨fun x ↦ ‖f x‖, by continuity⟩
  hasCompactSupport' := by simpa using f.hasCompactSupport'.norm

noncomputable def _root_.ZeroAtInfty.compNorm (f : C₀(X, ℂ)) : C₀(X, ℝ) where
  toContinuousMap := ⟨fun x ↦ ‖f x‖, by continuity⟩
  zero_at_infty' := by simpa using Filter.Tendsto.norm f.zero_at_infty'

-- TO DO: define `norm` as a `ContinuousMap` and use `norm ∘ f` in the following instead of the
-- `absOfFunc X f` hack.
def absOfFunc₀ (f : C₀(X, ℂ)) : C₀(X, ℝ) := sorry
def absOfFunc_c (f : C_c(X, ℂ)) : C_c(X, ℝ) := sorry


-- TO DO: figure out using this coercial directly in the argument.
noncomputable def toZeroAtInftyContinuousMap : C_c(X, ℂ) → C₀(X, ℂ) := fun f ↦ (f : C₀(X, ℂ))
def toZeroAtInftyContinuousMap' : C_c(X, ℝ) → C₀(X, ℝ) := fun f ↦ (f : C₀(X, ℝ))

-- there is a coercion
variable (f : C_c(X, ℂ))
-- #check (f : ZeroAtInftyContinuousMap X ℂ)


-- TO DO: define the identity between the ℝ and ℂ spaces of continuous functions,
-- similar to `CompactlySupportedContinuousMap.toReal`.
noncomputable def _root_.CompactlySupportedContinuousMap.toComplex (f : C_c(X, ℝ)) : C_c(X, ℂ) :=
  f.compLeft Complex.ofRealCLM


noncomputable def preVariationFunctional : C₀(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun := fun f ↦ sSup (nnnorm '' (Φ '' {g : C₀(X, ℂ) | ∀ x, ‖g x‖ ≤ f x}))
  map_add' f g := by
    apply le_antisymm
      sorry
      sorry
  -- We have to show that
  -- (10) `Λ(f + g) = Λ f + Λ g` whenever `f, g ∈ C_c^+(X)`,
  -- and we then have to extend `Λ` to a linear functional on `C_c(X, ℝ)`.
  -- Fix `f` and `g \in C_c^+(X)`.
  -- If `ε > 0`, there exist `h_1, h_2 \in C_c(X, ℝ)` such that `|h_1| ≤ f`, `|h_2| ≤ g`,
  -- `Λ f ≤ |Φ(h_1)| + ε`, `Λ g ≤ |Φ(h_2)| + ε`.
  -- There are complex numbers `α_i`, `|α_i| = 1`, so that `α_i Φ(h_i) = |Φ(h_i)|`, `i = 1, 2`.
  -- Then
  -- `Λ f + Λ g ≤ |Φ(h_1)| + |Φ(h_2)| + 2ε`
  -- `_ = Φ(α_1 h_1 + α_2 h_2) + 2ε`
  -- `_ ≤ Λ(|h_1| + |h_2|) + 2ε`
  -- `_ ≤ Λ(f + g) + 2ε`
  -- so that the inequality `≥` holds in (10).
  -- Next, choose `h ∈ C_c(X)`, subject only to the condition `|h| ≤ f + g`,
  -- let `V = { x : f(x) + g(x) > 0 }`, and define
  -- `h_1(x) = \frac{f(x) h(x)}{f(x) + g(x)}`,
  -- `h_2(x) = \frac{g(x) h(x)}{f(x) + g(x)}` when `x ∈ V`,
  -- `h_1(x) = h_2(x) = 0` when `x ∉ V`.
  -- It is clear that `h_1` is continuous at every point of `V`.
  -- If `x_0 ∉ V`, then `h(x_0) = 0`;
  -- since `h` is continuous and since `|h_1(x)| ≤ |h(x)|` for all `x ∈ X`,
  -- it follows that `x_0` is a point of continuity of `h_1`.
  -- Thus `h_1 \in C_c(X)`, and the same holds for `h_2`.
  -- Since `h_1 + h_2 = h` and `|h_1| ≤ f`, `|h_2| ≤ g`, we have
  -- `|Φ(h)| = |Φ(h_1) + Φ(h_2)| ≤ |Φ(h_1)| + |Φ(h_2)| ≤ Λ f + Λ g`.
  -- Hence `Λ(f + g) ≤ Λ f + Λ g`, and we have proved (10).
  -- If `f` is now a real function, `f \in C_c(X)`, then `2f^+ = |f| + f`,
  -- so that `f^+ \in C_c^+(X)`;
  -- likewise, `f^- \in C_c^+(X)`; and since `f = f^+ - f^-`, it is natural to define
  -- `Λ f = Λ f^+ - Λ f^- ` for `f \in C_c(X)`, `f` real
  -- and
  -- `Λ(u + iv) = Λ u + i Λ v`.
  -- Simple algebraic manipulations, just like those which occur in the proof of
  -- Theorem 1.32, show now that our extended functional `Λ` is linear on `C_c(X)`.
  map_smul' := sorry

/-- Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. There exists a positive linear functional
`Λ` on `C₀(X, ℝ)` such that, `∀ f : C₀(X, ℂ)`, `|Φ f| ≤ Λ |f|` and `Λ |f| ≤ ‖f‖` (`‖⬝‖` denotes
the supremum norm). [Rudin 87, part of proof of Theorem 6.19] -/
theorem exists_pos_lin_func : ∃ (Λ : C₀(X, ℝ) →L[ℝ] ℝ), ∀ (f : C₀(X, ℂ)),
    ‖Φ f‖ ≤ Λ (absOfFunc₀ f) ∧ Λ (absOfFunc₀ f) ≤ ‖Φ‖ * ‖f‖ := by

  -- If `f ∈` [class of all nonnegative real members of `C_c(X, ℝ)`],
  -- define `Λ f = \sup { |Φ(h)| : h ∈ C_c(X, ℂ), |h| ≤ f }`.
  let U (f : C_c(X, ℝ≥0)) := toZeroAtInftyContinuousMap '' {h : C_c(X, ℂ) | ∀ x : X, ‖h x‖ ≤ f x}
  let Λ' (f : C_c(X, ℝ≥0)) := sSup (norm '' (Φ '' U f))

  -- Then `Λ f ≥ 0`, `Λ` satisfies the two required inequalities,
  -- this is not needed?
  have (f : C_c(X, ℝ≥0)) : 0 ≤ Λ' f := by
    -- because it is the sup of nonnegative quantities
    unfold Λ'
    apply Real.sSup_nonneg
    intro x hx
    rw [Set.mem_image] at hx
    obtain ⟨a, _, ha⟩ := hx
    rw [← ha]
    positivity
  have (f : C_c(X, ℝ≥0)) : ‖Φ (toComplex (f.toReal))‖ ≤ Λ' f := by
    -- because `toComplex (f.toReal)` is one of the `h`'s in the definition of `Λ f`
    unfold Λ'
    apply le_csSup
    · by_cases hempty : IsEmpty f.toFun.support
      · simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.isEmpty_coe_sort,
          Function.support_eq_empty_iff] at hempty
        use 0
        intro a
        simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp]
        intro g hg hga
        obtain ⟨k, hk⟩ := hg
        simp only [Set.mem_setOf_eq] at hk
        rw [hempty] at hk
        simp only [Pi.zero_apply, NNReal.coe_zero, norm_le_zero_iff] at hk
        have : g = 0 := by
          ext x
          rw [← hk.2, toZeroAtInftyContinuousMap]
          simpa using hk.1 x
        simp only [this, map_zero, norm_zero] at hga
        grind
      · letI : Nonempty X := by
          push Not at hempty
          obtain ⟨x, hx⟩ := hempty
          exact ⟨x⟩
        obtain ⟨x, hx⟩ := Continuous.exists_forall_ge_of_hasCompactSupport f.continuous
          f.hasCompactSupport'
        use ‖Φ‖ * f x
        intro a ha
        simp only [Set.mem_image, exists_exists_and_eq_and] at ha
        obtain ⟨g, hg, hga⟩ := ha
        obtain ⟨k, hk⟩ := hg
        simp only [Set.mem_setOf_eq] at hk
        rw [← hga]
        apply le_trans (ContinuousLinearMap.le_opNorm Φ g)
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg Φ)
        rw [← g.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_le]
        · intro y
          rw [← hk.2, toZeroAtInftyContinuousMap]
          simp only [ZeroAtInftyContinuousMap.toBCF_apply, ZeroAtInftyContinuousMap.coe_mk]
          apply le_trans <| hk.1 y
          exact_mod_cast hx y
        · simp
    use Φ (toComplex (f.toReal))
    simp only [Set.mem_image, and_true]
    use f.toReal.toComplex
    rw [Set.mem_image]
    simp only [Set.mem_setOf_eq, and_true]
    use f.toReal.toComplex
    constructor
    · intro x
      rw [toComplex, CompactlySupportedContinuousMap.toReal,
        CompactlySupportedContinuousMap.compLeft_apply,
        CompactlySupportedContinuousMap.compLeft_apply]
      simp
      exact coeNNRealReal_zero
      exact Eq.symm (Complex.ext rfl rfl)
    · ext x
      rw [toZeroAtInftyContinuousMap]
  have (f : C_c(X, ℝ≥0)) : Λ' f ≤ ‖Φ‖ * ‖toZeroAtInftyContinuousMap' f.toReal‖ := by
    rw [toZeroAtInftyContinuousMap']
    unfold Λ'
    apply csSup_le
    · use 0
      simp only [Set.mem_image, norm_eq_zero, exists_eq_right]
      use 0
      simp only [map_zero, and_true]
      unfold U
      simp only [Set.mem_image, Set.mem_setOf_eq]
      use 0
      simp only [CompactlySupportedContinuousMap.coe_zero, Pi.zero_apply, norm_zero, zero_le_coe,
        implies_true, true_and]
      rw [toZeroAtInftyContinuousMap]
      ext x
      simp
    · simp only [Set.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro g hg
      apply le_trans (ContinuousLinearMap.le_opNorm Φ g)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg Φ)
      rw [← g.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_le (norm_nonneg _)]
      intro x
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      apply le_trans _ <| BoundedContinuousFunction.apply_le_norm _ x
      simp only [ZeroAtInftyContinuousMap.toBCF_apply, ZeroAtInftyContinuousMap.coe_mk,
        toReal_apply]
      obtain ⟨k, hk⟩ := hg
      rw [← hk.2, toZeroAtInftyContinuousMap]
      simpa using hk.1 x


  -- `0 ≤ f_1 ≤ f_2` implies `Λ f_1 ≤ Λ f_2`, and `Λ (cf) = c Λ f` if `c` is a positive constant.

  -- We have to show that
  -- (10) `Λ(f + g) = Λ f + Λ g` whenever `f, g ∈ C_c^+(X)`,
  -- and we then have to extend `Λ` to a linear functional on `C_c(X, ℝ)`.
  -- Fix `f` and `g \in C_c^+(X)`.
  -- If `ε > 0`, there exist `h_1, h_2 \in C_c(X, ℝ)` such that `|h_1| ≤ f`, `|h_2| ≤ g`,
  -- `Λ f ≤ |Φ(h_1)| + ε`, `Λ g ≤ |Φ(h_2)| + ε`.
  -- There are complex numbers `α_i`, `|α_i| = 1`, so that `α_i Φ(h_i) = |Φ(h_i)|`, `i = 1, 2`.
  -- Then
  -- `Λ f + Λ g ≤ |Φ(h_1)| + |Φ(h_2)| + 2ε`
  -- `_ = Φ(α_1 h_1 + α_2 h_2) + 2ε`
  -- `_ ≤ Λ(|h_1| + |h_2|) + 2ε`
  -- `_ ≤ Λ(f + g) + 2ε`
  -- so that the inequality `≥` holds in (10).
  -- Next, choose `h ∈ C_c(X)`, subject only to the condition `|h| ≤ f + g`,
  -- let `V = { x : f(x) + g(x) > 0 }`, and define
  -- `h_1(x) = \frac{f(x) h(x)}{f(x) + g(x)}`,
  -- `h_2(x) = \frac{g(x) h(x)}{f(x) + g(x)}` when `x ∈ V`,
  -- `h_1(x) = h_2(x) = 0` when `x ∉ V`.
  -- It is clear that `h_1` is continuous at every point of `V`.
  -- If `x_0 ∉ V`, then `h(x_0) = 0`;
  -- since `h` is continuous and since `|h_1(x)| ≤ |h(x)|` for all `x ∈ X`,
  -- it follows that `x_0` is a point of continuity of `h_1`.
  -- Thus `h_1 \in C_c(X)`, and the same holds for `h_2`.
  -- Since `h_1 + h_2 = h` and `|h_1| ≤ f`, `|h_2| ≤ g`, we have
  -- `|Φ(h)| = |Φ(h_1) + Φ(h_2)| ≤ |Φ(h_1)| + |Φ(h_2)| ≤ Λ f + Λ g`.
  -- Hence `Λ(f + g) ≤ Λ f + Λ g`, and we have proved (10).
  -- If `f` is now a real function, `f \in C_c(X)`, then `2f^+ = |f| + f`,
  -- so that `f^+ \in C_c^+(X)`;
  -- likewise, `f^- \in C_c^+(X)`; and since `f = f^+ - f^-`, it is natural to define
  -- `Λ f = Λ f^+ - Λ f^- ` for `f \in C_c(X)`, `f` real
  -- and
  -- `Λ(u + iv) = Λ u + i Λ v`.
  -- Simple algebraic manipulations, just like those which occur in the proof of
  -- Theorem 1.32, show now that our extended functional `Λ` is linear on `C_c(X)`.
  sorry


end ComplexRMK

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)
variable [MeasurableSpace X] [BorelSpace X]

/-- The measure induced by a `ℂ`-linear positive functional `Λ`. -/
noncomputable def rieszMeasure (Φ : C₀(X, ℂ) →L[ℂ] ℂ) : ComplexMeasure X :=
  -- To be defined according to the construction of the proof, using `RealRMK.rieszMeasure`.
  sorry

/-- **Theorem**
Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. Then there exists a complex Borel measure
`μ` such that, `∀ f : C₀(X, ℂ)`, `Φ f = ∫ x, f x ∂μ`, (2) `‖Φ‖ = |μ|(X)`. -/
theorem integral_rieszMeasure (f : C₀(X, ℂ)) :
     Φ f = (rieszMeasure Φ).integral (f ·) := by
  -- **Proof** [Rudin 87, Theorem 6.19]
  -- Assume `‖Φ‖ = 1`, without loss of generality.
  -- *Part 1:*
  -- Using `exists_pos_lin_func` we obtain a *positive* linear functional `Λ` on `C_c(X)`, such that
  -- (4) `|Φ(f)| ≤ Λ(|f|) ≤ ‖f‖` for all `f \in C_c(X))`.
  -- Once we have this `Λ`, we associate with it a positive Borel measure `λ`, given by
  -- have := RealRMK.integral_rieszMeasure
  -- `RealRMK.rieszMeasure hΛ` and which is a representation by `RealRMK.integral_rieszMeasure`.
  -- It also implies that `λ` is regular if `λ(X) < \infty`.
  -- Since `Λ(X) = \sup {Λ f : 0 ≤ f ≤ 1, f \in C_c(X)}`
  -- and since `|Λ f| ≤ 1` if `‖f‖ ≤ 1`, we see that actually `λ(X) ≤ 1`.
  -- We also deduce from (4) that
  -- `|Φ(f)| ≤ Λ(|f|) = ∫_X |f| dλ = ‖f‖_1`, `f \in C_c(X))`.
  -- The last norm refers to the space `L^1(λ)`.
  -- Thus `Φ` is a linear functional on `C_c(X)` of norm at most 1, with respect to the `L^1(λ)`-norm
  -- on `C_c(X)`.
  -- There is a norm-preserving extension of `Φ` to a linear functional on `L^1(λ)`, and therefore
  -- *Theorem 6.16* (the case `p = 1`) gives a Borel function `g`, with `|g| ≤ 1`, such that
  -- (6) `Φ(f) = ∫_X fg dλ`, `f \in C_c(X)`.
  -- Each side of (6) is a continuous functional on `C_0(X)`, and `C_c(X)` is dense in `C_0(X)`.
  -- Hence (6) holds for all `f \in C_0(X)`, and we obtain the representation with `dμ = g dλ`.
  -- *Part 2:*
  -- Since `\|Φ\| = 1`, (6) shows that
  -- `∫_X |g| dλ ≥ \sup { |Φ(f)| : f \in C_0(X), ‖f‖ ≤ 1 } = 1`.
  -- We also know that `λ(X) ≤ 1` and `|g| ≤ 1`.
  -- These facts are compatible only if `λ(X) = 1` and `|g| = 1` a.e. `[λ]`.
  -- Thus `d|μ| = |g| dλ = dλ`, by *Theorem 6.13*,
  -- and `|μ|(X) = λ(X) = 1 = ‖Φ‖`,
  sorry

theorem norm_eq_variation (f : C₀(X, ℂ)) :
    ENNReal.ofReal ‖Φ‖ = (rieszMeasure Φ).variation Set.univ := by
  sorry

end ComplexRMK


open ZeroAtInftyContinuousMap

namespace ZeroAtInftyContinuousMap

section NormedAddGroupHom

variable {α : Type*} {β : Type*} [TopologicalSpace α] [CompactSpace α]
  [SeminormedAddCommGroup β]

def ContinuousMap.liftZeroAtInftyNAGH : NormedAddGroupHom C(α, β) C₀(α, β) where
  toFun := ContinuousMap.liftZeroAtInfty
  map_add' x y := rfl
  bound' := ⟨1, by intro v; simp; apply le_of_eq; rfl⟩

@[simp]
lemma liftZeroAtInftyNAGH_apply (f : C(α, β)) : f.liftZeroAtInftyNAGH = f.liftZeroAtInfty := rfl

end NormedAddGroupHom

section ContinuousLinearEquiv

variable {α : Type*} {β : Type*} {R : Type*} [TopologicalSpace α] [CompactSpace α]
  [SeminormedAddCommGroup β] [Semiring R] [Module R β] [ContinuousConstSMul R β]

noncomputable def ContinuousMap.liftZeroAtInftyCLE : C(α, β) ≃L[R] C₀(α, β) :=
  { toFun := ContinuousMap.liftZeroAtInftyNAGH
    map_add' x y := rfl
    map_smul' c x := rfl
    invFun f := f
    continuous_invFun := Isometry.continuous fun _ ↦ congrFun rfl
  }

end ContinuousLinearEquiv
