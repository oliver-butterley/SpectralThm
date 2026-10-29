/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib
public import SpectralThm.ComplexMeasure.Integral
public import SpectralThm.VectorMeasure.FiniteDimensional

/-!
# Riesz–Markov–Kakutani representation theorem for complex linear functionals

This file contains the proof of the **Riesz Representations Theorem** a.k.a.
**Riesz–Markov–Kakutani theorem** (complex case).

## Main definition

* `ComplexRMK.rieszMeasure (Φ : C₀(X, ℂ) →L[ℂ] ℂ)`: the `ComplexMeasure` associated to the
  bounded linear functional `Φ`.

## Main results

* `ComplexRMK.integral_rieszMeasure`: `Φ f = ∫ f d(rieszMeasure Φ)` for all `f : C₀(X, ℂ)`.
* `ComplexRMK.norm_eq_variation`: `‖Φ‖ = |rieszMeasure Φ|(X)`.
* `ComplexRMK.rieszMeasure_unique`: uniqueness of the representing measure.
* `ComplexRMK.exists_eq_sub_of_bounded`: Jordan decomposition of a bounded linear functional on
  `C_c(X, ℝ)` into a difference of two positive linear functionals.
* `ComplexRMK.exists_pos_lin_func`: the positive functional `Λ` of Rudin's proof, with
  `|Φ f| ≤ Λ |f| ≤ ‖Φ‖ ‖f‖`.

## Overview

Firstly the uniqueness of measures satisfying the representation equation is proven.

The proof of existence reduces to the case of positive `ℝ`-linear functionals on `C_c(X, ℝ)`
(`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`), avoiding the `L¹`–`L^∞` duality
used by Rudin:

* the real and imaginary parts `reFunctional Φ`, `imFunctional Φ` of the restriction of `Φ` to
  `C_c(X, ℝ)` are bounded `ℝ`-linear functionals;
* each of them is a difference `posPart - negPart` of positive functionals (Jordan decomposition,
  `posPart φ f = sup {φ g : 0 ≤ g ≤ f}`), giving four finite regular measures by the real RMK
  theorem;
* with `ν = baseMeasure Φ` the sum of these four measures, Radon–Nikodym gives a bounded density
  `density Φ` with `Φ f = ∫ density Φ * f dν`, first for `f ∈ C_c(X, ℂ)` and then, by uniform
  approximation, for `f ∈ C₀(X, ℂ)` (`apply_eq_integral`);
* `rieszMeasure Φ := ν.withDensityᵥ (density Φ)`, and `integral_withDensityᵥ` identifies the
  integrals;
* `|rieszMeasure Φ| = |density Φ| ν`, and `∫ |density Φ| dν = ‖Φ‖` by testing `Φ` against
  continuous approximations of the conjugate sign of `density Φ`.

## Notes

* File destination: `Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Complex.lean`

## References

* Section 6 of [Walter Rudin, Real and Complex Analysis.][Rud87]

## To do

- Rudin 6.5 `NormedAddCommGroup` instance for `ComplexMeasure X`
- Remove `[NormalSpace X]` from `rieszMeasure_unique` and `norm_eq_variation`, by generalising
  `Integrable.exists_hasCompactSupport_integral_sub_le` to locally compact Hausdorff spaces.
- Prove that `(rieszMeasure Φ).variation` is regular, and more generally that differences of such
  measures are; together with `rieszMeasure_unique` this gives linearity of `rieszMeasure` and the
  isometric isomorphism between the dual of `C₀(X, ℂ)` and regular complex Borel measures.
-/

@[expose] public section

open NNReal ENNReal
open ZeroAtInfty MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped MeasureTheory.ComplexMeasure

section Lemmas

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

lemma outerRegular_add (μ₁ μ₂ : Measure X) [μ₁.OuterRegular] [μ₂.OuterRegular] :
    (μ₁ + μ₂).OuterRegular := by
  constructor
  intro A hA r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_add_lt_of_add_lt hr
  obtain ⟨U, hAU, hU, hμU⟩ := A.exists_isOpen_lt_of_lt u hu
  obtain ⟨V, hAV, hV, hμV⟩ := A.exists_isOpen_lt_of_lt v hv
  use U ∩ V
  refine ⟨Set.subset_inter hAU hAV, hU.inter hV, ?_⟩
  calc
    (μ₁ + μ₂) (U ∩ V) ≤ μ₁ U + μ₂ V := by
        simp only [Measure.coe_add, Pi.add_apply]
        gcongr
        · exact Set.inter_subset_left
        · exact Set.inter_subset_right
    _ < u + v := by gcongr
    _ < r := by grind

lemma innerRegular_add (μ₁ μ₂ : Measure X) [μ₁.Regular] [μ₂.Regular] :
    (μ₁ + μ₂).InnerRegularWRT IsCompact IsOpen := by
  intro U hU r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  rcases eq_or_ne (μ₁ U) 0 with h₁ | h₁
  · simp only [h₁, zero_add] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  rcases eq_or_ne (μ₂ U) 0 with h₂ | h₂
  · simp only [h₂, add_zero] at hr
    obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
    exact ⟨K, hKU, hK, hrK.trans_le (by simp)⟩
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_lt_add_of_lt_add hr h₁ h₂
  obtain ⟨K, hKU, hK, huK⟩ := hU.exists_lt_isCompact hu
  obtain ⟨L, hLU, hL, hvL⟩ := hU.exists_lt_isCompact hv
  use K ∪ L
  refine ⟨Set.union_subset hKU hLU, hK.union hL, ?_⟩
  calc
    r < u + v := huv
    _ < μ₁ K + μ₂ L := by gcongr
    _ ≤ (μ₁ + μ₂) (K ∪ L) := by
        simp only [Measure.coe_add, Pi.add_apply]
        gcongr
        · exact Set.subset_union_left
        · exact Set.subset_union_right

lemma regular_add (μ₁ μ₂ : Measure X) [μ₁.Regular] [μ₂.Regular] : (μ₁ + μ₂).Regular := by
  let ⟨hOuter⟩ := outerRegular_add μ₁ μ₂
  exact
    { lt_top_of_isCompact := fun _K hK =>
        ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩
      outerRegular := hOuter
      innerRegular := innerRegular_add μ₁ μ₂ }

lemma regular_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure X)
    [∀ i, (μ i).Regular] : (∑ i ∈ s, μ i).Regular := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa [Finset.sum_empty] using Measure.Regular.zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact regular_add (μ i) (∑ j ∈ s, μ j)

-- adapt and generalize this to more outerRegular type classes

end Lemmas

namespace ComplexRMK

variable {X : Type*} [MeasurableSpace X]

-- TODO
-- move ComplexMeasure in VectorMeasure
-- separate things about SignedMeasure in Basic in a separate file
-- counterexample: a L^∞ valued measure whose variation is not finite?
-- make a folder VectorMeasure/SignedMeasure, make a file Basic, a folder Decomposition

-- Rudin 6.4: `IsFiniteMeasure μ.variation` is in `SpectralThm/VectorMeasure/FiniteDimensional.lean`

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
     ∀ᵐ x ∂μ.variation, ‖μ.rnDeriv μ.variation x‖ = 1 := by
  have hDensity :
      ((μ.variation).withDensityᵥ (μ.rnDeriv μ.variation)).variation
        = VectorMeasure.variation μ := by
      congr; exact withDensityᵥ_variation_rnDeriv_eq μ
  rw [Measure.variation_withDensityᵥ (ComplexMeasure.integrable_rnDeriv μ μ.variation)]
    at hDensity
  have henorm : (fun x ↦ ‖μ.rnDeriv μ.variation x‖ₑ) =ᵐ[μ.variation] 1 := by
    apply (MeasureTheory.withDensity_eq_iff_of_sigmaFinite
      (ComplexMeasure.integrable_rnDeriv μ μ.variation).aestronglyMeasurable.enorm
      aemeasurable_const).mp
    simpa using hDensity
  filter_upwards [henorm] with x h
  simpa [← ofReal_norm, Pi.one_apply, ofReal_eq_one] using h

/-- The integral against a complex measure in terms of its polar decomposition (Rudin RCA 6.18):
`∫ f dμ = ∫ (dμ/d|μ|) f d|μ|`. -/
theorem integral_eq_integral_rnDeriv (μ : ComplexMeasure X) {f : X → ℂ}
    (hf : Integrable f μ.variation) :
    ∫ᶜ x, f x ∂μ = ∫ x, μ.rnDeriv μ.variation x * f x ∂μ.variation := by
  set a := μ.rnDeriv μ.variation
  have ha : Integrable a μ.variation := ComplexMeasure.integrable_rnDeriv μ μ.variation
  have ha_le : ∀ᵐ x ∂μ.variation, ‖a x‖ ≤ 1 := by
    filter_upwards [exists_l1_eq_withDensity_variation μ] with x hx using hx.le
  have hmul {g : X → ℂ} (hg : Integrable g μ.variation) :
      Integrable (fun x ↦ a x * g x) μ.variation :=
    hg.bdd_mul ha.aestronglyMeasurable ha_le
  refine hf.induction (P := fun f ↦ ∫ᶜ x, f x ∂μ = ∫ x, a x * f x ∂μ.variation) ?_ ?_ ?_ ?_
  · intro c s hs _
    have h : (fun x ↦ a x * s.indicator (fun _ ↦ c) x) = s.indicator (fun x ↦ a x * c) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [VectorMeasure.integral_indicator_const _ hs, h, integral_indicator hs, integral_mul_const,
      ← withDensityᵥ_apply ha hs, withDensityᵥ_variation_rnDeriv_eq, mul_comm]
    rfl
  · intro f g _ hf hg hPf hPg
    simp only [Pi.add_apply, mul_add]
    rw [VectorMeasure.integral_fun_add hf hg, integral_add (hmul hf) (hmul hg), hPf, hPg]
  · refine isClosed_eq VectorMeasure.continuous_integral ?_
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun g h ↦ ?_)
    rw [dist_eq_norm, ← integral_sub (hmul (L1.integrable_coeFn g)) (hmul (L1.integrable_coeFn h)),
      NNReal.coe_one, one_mul, dist_eq_norm, L1.norm_eq_integral_norm]
    refine norm_integral_le_of_norm_le (L1.integrable_coeFn _).norm ?_
    filter_upwards [ha_le, Lp.coeFn_sub g h] with x hx hgh
    rw [← mul_sub, norm_mul, hgh, Pi.sub_apply]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · intro f g hfg _ hPf
    rw [← VectorMeasure.integral_congr_ae hfg, hPf]
    exact integral_congr_ae (hfg.mono fun x hx ↦ congrArg (a x * ·) hx)


variable [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

-- TODO remove `[NormalSpace X]` from `exists_hasCompactSupport_integral_sub_le`
-- switch to `C_c`
lemma eq_zero_of_integral_eq_zero [BorelSpace X] [NormalSpace X] {μ: ComplexMeasure X}
    [Measure.Regular μ.variation]
    (h : ∀ f : C₀(X, ℂ), ∫ᶜ x, f x ∂μ = 0) :
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
  -- depends on 3.13 `exists_hasCompactSupport_integral_sub_le`, this is written only for
  -- `NormalSpace α` and approximation given by bounded functions)
  -- It is easy to see that the difference of two regular complex Borel measures on `X` is regular.
  rw [← variation_zero_iff_univ]
  -- take a sequence `f n` which tends to `star μ.rnDeriv μ.variation` in the L^1 norm of `μ.variation`
  -- calc
  --   μ.variation.real Set.univ = ∫ (x : X), 1 ∂(μ.variation) := by simp
  --   _ = ∫ (x : X), ‖μ.rnDeriv μ.variation x‖ ∂(μ.variation) := by sorry
  --   _ = ∫ (x : X), ‖μ.rnDeriv μ.variation x‖ ^ 2 ∂(μ.variation) := by sorry
  --   _ = ∫ (x : X), (star μ.rnDeriv μ.variation x - f n) * h ∂(μ.variation) := by sorry
  --   _ = ∫ (x : X), (star μ.rnDeriv μ.variation x - f n) ∂ μ := by sorry
  --   _ = ∫ (x : X), ‖star μ.rnDeriv μ.variation x - f n‖ ∂ μ.variation := by sorry
  --   _ ≤ 0
  -- (actually the calc block below is almost ok)

  rw [← measureReal_eq_zero_iff]
  apply le_antisymm _ ENNReal.toReal_nonneg
  · apply _root_.le_of_forall_pos_le_add
    intro ε hε
    let a := μ.rnDeriv μ.variation
    have ha : Integrable (fun x ↦ star (a x)) μ.variation :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp
        (ComplexMeasure.integrable_rnDeriv μ μ.variation)
    obtain ⟨g, hg_support, hg_approx, hg_cont, hg_int⟩ :=
      ha.exists_hasCompactSupport_integral_sub_le hε
    let f : C_c(X, ℂ) := ⟨⟨g, hg_cont⟩, hg_support⟩
    -- start calc here
    have hfg : ∫ x, a x * g x ∂μ.variation = 0 := by
      rw [← integral_eq_integral_rnDeriv μ hg_int]
      simpa [f] using h (f : C₀(X, ℂ))
    have haa : ∀ᵐ x ∂μ.variation, star (a x) * a x = 1 := by
      filter_upwards [exists_l1_eq_withDensity_variation μ] with x hx
      rw [← show (Complex.normSq (a x) : ℂ) = star (a x) * a x by
        simpa only [starRingEnd_apply] using Complex.normSq_eq_conj_mul_self]
      have hx' : ‖a x‖ = 1 := by simpa [a] using hx
      rw [Complex.normSq_eq_norm_sq, hx']
      norm_num
    have ha' : Integrable a μ.variation :=
      ComplexMeasure.integrable_rnDeriv μ μ.variation
    have ha_bound : ∀ᵐ x ∂μ.variation, ‖a x‖ ≤ 1 := by
      filter_upwards [exists_l1_eq_withDensity_variation μ] with x hx
      have hx' : ‖a x‖ = 1 := by simpa [a] using hx
      simp [hx']
    have hdiff : Integrable (fun x ↦ (star (a x) - g x) * a x) μ.variation :=
      (ha.sub hg_int).mul_bdd ha'.aestronglyMeasurable ha_bound
    have hprod : Integrable (fun x ↦ a x * g x) μ.variation :=
      hg_int.bdd_mul ha'.aestronglyMeasurable ha_bound
    calc
      μ.variation.real Set.univ
          = ‖∫ x, star (a x) * a x ∂μ.variation‖ := by
              rw [integral_congr_ae haa]
              simp [abs_of_nonneg]
      _ = ‖∫ x, (star (a x) - g x) * a x ∂μ.variation‖ := by
            congr 1
            calc
              ∫ x, star (a x) * a x ∂μ.variation =
                  ∫ x, (star (a x) - g x) * a x + a x * g x ∂μ.variation := by
                    congr 1
                    funext x
                    ring
              _ = (∫ x, (star (a x) - g x) * a x ∂μ.variation) +
                  ∫ x, a x * g x ∂μ.variation := by
                    exact integral_add hdiff hprod
              _ = _ := by rw [hfg, add_zero]
      _ ≤ ∫ x, ‖star (a x) - g x‖ ∂μ.variation := by
            refine norm_integral_le_of_norm_le (ha.sub hg_int).norm ?_
            filter_upwards [exists_l1_eq_withDensity_variation μ] with x hx
            have hx' : ‖a x‖ = 1 := by simpa [a] using hx
            simp [hx']
      _ ≤ ε := hg_approx
      _ ≤ 0 + ε := by simp

-- need that if `μ₁ μ₂` are regular (in the vector measure sense), then `μ₁ - μ₂` is regular.
/-- Uniqueness of `ComplexRMK.rieszMeasure`: Let `Φ` be a linear functional on `C_0(X, ℂ)`. Suppose
that `μ`, `μ'` are complex Borel measures such that, `∀ f : C_0(X, ℂ)`, `Φ f = ∫ x, f x ∂μ` and
`Φ f = ∫ x, f x ∂μ'`. Then `μ = μ'`. -/
theorem rieszMeasure_unique [BorelSpace X] [NormalSpace X] {μ₁ μ₂ : ComplexMeasure X}
    [Measure.Regular (μ₁ - μ₂).variation]
    (Φ : C₀(X, ℂ) →L[ℂ] ℂ)
    (h₁ : ∀ f : C₀(X, ℂ), ∫ᶜ x, f x ∂μ₁ = Φ f) (h₂ : ∀ f : C₀(X, ℂ), ∫ᶜ x, f x ∂μ₂ = Φ f) :
    μ₁ = μ₂ := by
  refine eq_of_sub_eq_zero (eq_zero_of_integral_eq_zero fun f ↦ ?_)
  have hf (ν : ComplexMeasure X) : ν.Integrable f := f.toBCF.integrable _
  rw [VectorMeasure.integral_sub_vectorMeasure (hf μ₁) (hf μ₂), h₁, h₂, sub_self]

end ComplexRMK

/-! ### Auxiliary lemmas

The lemmas in this section are general facts which should eventually live elsewhere in Mathlib
(`Topology/ContinuousMap/ZeroAtInfty`, `MeasureTheory/VectorMeasure/WithDensityVec`,
`MeasureTheory/Integral/RieszMarkovKakutani/Real`). -/

section compNorm

variable {X : Type*} [TopologicalSpace X]

/-- The pointwise norm `x ↦ ‖f x‖` of a compactly supported continuous function. -/
noncomputable def CompactlySupportedContinuousMap.compNorm (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toContinuousMap := ⟨fun x ↦ ‖f x‖, continuous_norm.comp f.continuous⟩
  hasCompactSupport' := by simpa using f.hasCompactSupport'.norm

@[simp]
lemma CompactlySupportedContinuousMap.compNorm_apply (f : C_c(X, ℂ)) (x : X) :
    f.compNorm x = ‖f x‖ := rfl

/-- The pointwise norm `x ↦ ‖f x‖` of a continuous function vanishing at infinity. -/
noncomputable def ZeroAtInftyContinuousMap.compNorm (f : C₀(X, ℂ)) : C₀(X, ℝ) where
  toContinuousMap := ⟨fun x ↦ ‖f x‖, continuous_norm.comp f.continuous⟩
  zero_at_infty' := by simpa using Filter.Tendsto.norm f.zero_at_infty'

@[simp]
lemma ZeroAtInftyContinuousMap.compNorm_apply (f : C₀(X, ℂ)) (x : X) :
    f.compNorm x = ‖f x‖ := rfl

end compNorm

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

/-- A Riesz measure is finite if the functional is bounded on functions with values in
`[0, 1]`. -/
lemma isFiniteMeasure_rieszMeasure [MeasurableSpace X] [BorelSpace X] (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    {C : ℝ} (hΛ : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → Λ f ≤ C) :
    IsFiniteMeasure (RealRMK.rieszMeasure Λ) := by
  refine ⟨lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := C))⟩
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  refine iSup₂_le fun K _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨f, hf1, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  let g : C_c(X, ℝ) := ⟨f, hfc⟩
  exact (RealRMK.rieszMeasure_le_of_eq_one Λ (f := g) (fun x ↦ (hf01 x).1) hK
    fun x hx ↦ hf1 hx).trans
    (ENNReal.ofReal_le_ofReal (hΛ g hf01))

/-- A function vanishing at infinity is uniformly approximated by compactly supported continuous
functions. -/
lemma exists_compactlySupported_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C₀(X, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X, E), ∀ x, ‖f x - g x‖ ≤ ε := by
  obtain ⟨K, hK, hKf⟩ := (Filter.hasBasis_cocompact.tendsto_iff Metric.nhds_basis_closedBall).mp
    f.zero_at_infty' ε hε
  obtain ⟨χ, hχ1, -, hχc, hχ01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  refine ⟨⟨⟨fun x ↦ χ x • f x, by fun_prop⟩, hχc.smul_right⟩, fun x ↦ ?_⟩
  simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
  by_cases hx : x ∈ K
  · simp [hχ1 hx, hε.le]
  · have h₁ : ‖f x‖ ≤ ε := by simpa using hKf x hx
    rw [show f x - χ x • f x = (1 - χ x) • f x by rw [sub_smul, one_smul], norm_smul,
      Real.norm_of_nonneg (sub_nonneg.mpr (hχ01 x).2)]
    nlinarith [(hχ01 x).1, norm_nonneg (f x)]

end ComplexRMK

namespace ComplexRMK

variable {X : Type*} [MeasurableSpace X]

/-- The integral against the complex measure `ν.withDensityᵥ k` (i.e. `dμ = k dν`) is
`∫ k f dν`. This generalises `integral_eq_integral_rnDeriv`. -/
theorem integral_withDensityᵥ {ν : Measure X} {k : X → ℂ} (hk : Integrable k ν) {f : X → ℂ}
    (hf : Integrable f (ν.withDensityᵥ k).variation) :
    ∫ᶜ x, f x ∂(ν.withDensityᵥ k) = ∫ x, k x * f x ∂ν := by
  have hρ : (ν.withDensityᵥ k).variation = ν.withDensity fun x ↦ (‖k x‖₊ : ℝ≥0∞) :=
    Measure.variation_withDensityᵥ hk
  have hkm : AEMeasurable (fun x ↦ ‖k x‖₊) ν := hk.aestronglyMeasurable.nnnorm.aemeasurable
  have hmul {g : X → ℂ} (hg : Integrable g (ν.withDensityᵥ k).variation) :
      Integrable (fun x ↦ k x * g x) ν := by
    rw [hρ, integrable_withDensity_iff_integrable_smul₀ hkm] at hg
    have hs : AEStronglyMeasurable (fun x ↦ k x / (‖k x‖ : ℂ)) ν :=
      (hk.aemeasurable.div
        (Complex.measurable_ofReal.comp_aemeasurable hk.aemeasurable.norm)).aestronglyMeasurable
    refine (hg.bdd_mul (c := 1) hs (Filter.Eventually.of_forall fun x ↦ ?_)).congr
      (Filter.Eventually.of_forall fun x ↦ ?_)
    · simpa [norm_div] using div_self_le_one ‖k x‖
    · rcases eq_or_ne (k x) 0 with h | h
      · simp [h]
      · have : (‖k x‖ : ℂ) ≠ 0 := by simpa using h
        simp only [NNReal.smul_def, coe_nnnorm, Complex.real_smul]
        field_simp
  have hdist {g : X → ℂ} (hg : Integrable g (ν.withDensityᵥ k).variation) :
      ‖∫ x, k x * g x ∂ν‖ ≤ ∫ x, ‖g x‖ ∂(ν.withDensityᵥ k).variation := by
    rw [hρ, integral_withDensity_eq_integral_smul₀ hkm]
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae ?_)
    filter_upwards with x
    simp [NNReal.smul_def]
  refine hf.induction (P := fun f ↦ ∫ᶜ x, f x ∂(ν.withDensityᵥ k) = ∫ x, k x * f x ∂ν)
    ?_ ?_ ?_ ?_
  · intro c s hs _
    have h : (fun x ↦ k x * s.indicator (fun _ ↦ c) x) = s.indicator (fun x ↦ k x * c) := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [VectorMeasure.integral_indicator_const _ hs, h, integral_indicator hs, integral_mul_const,
      ← withDensityᵥ_apply hk hs, mul_comm]
    rfl
  · intro f g _ hf hg hPf hPg
    simp only [Pi.add_apply, mul_add]
    rw [VectorMeasure.integral_fun_add hf hg, integral_add (hmul hf) (hmul hg), hPf, hPg]
  · refine isClosed_eq VectorMeasure.continuous_integral ?_
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun g h ↦ ?_)
    have hg := L1.integrable_coeFn g
    have hh := L1.integrable_coeFn h
    rw [dist_eq_norm, ← integral_sub (hmul hg) (hmul hh), NNReal.coe_one, one_mul, dist_eq_norm,
      L1.norm_eq_integral_norm]
    calc ‖∫ x, k x * g x - k x * h x ∂ν‖ = ‖∫ x, k x * (⇑g - ⇑h) x ∂ν‖ := by
          simp [mul_sub]
      _ ≤ ∫ x, ‖(⇑g - ⇑h) x‖ ∂(ν.withDensityᵥ k).variation := hdist (hg.sub hh)
      _ = _ := integral_congr_ae <| by
          filter_upwards [Lp.coeFn_sub g h] with x hx
          rw [hx]
  · intro f g hfg _ hPf
    rw [← VectorMeasure.integral_congr_ae hfg, hPf]
    rw [hρ, Filter.EventuallyEq, ae_withDensity_iff' hkm.coe_nnreal_ennreal] at hfg
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rcases eq_or_ne (k x) 0 with h | h
    · simp [h]
    · rw [hx (by simpa using h)]

section RadonNikodym

variable {ν m : Measure X} [IsFiniteMeasure ν]

/-- If `m ≤ ν` then `(dm/dν) g` is `ν`-integrable for any `m`-integrable `g`. -/
lemma integrable_rnDeriv_mul (h : m ≤ ν) {g : X → ℂ} (hg : Integrable g m) :
    Integrable (fun x ↦ ((m.rnDeriv ν x).toReal : ℂ) * g x) ν := by
  have : IsFiniteMeasure m := isFiniteMeasure_of_le ν h
  simpa [Complex.real_smul] using
    (integrable_rnDeriv_smul_iff (Measure.absolutelyContinuous_of_le h)).mpr hg

/-- If `m ≤ ν` then `∫ (dm/dν) g dν = ∫ g dm`. -/
lemma integral_rnDeriv_mul (h : m ≤ ν) (g : X → ℂ) :
    ∫ x, ((m.rnDeriv ν x).toReal : ℂ) * g x ∂ν = ∫ x, g x ∂m := by
  have : IsFiniteMeasure m := isFiniteMeasure_of_le ν h
  simpa [Complex.real_smul] using
    integral_rnDeriv_smul (Measure.absolutelyContinuous_of_le h) (f := g)

lemma toReal_rnDeriv_mem_Icc (h : m ≤ ν) : ∀ᵐ x ∂ν, (m.rnDeriv ν x).toReal ∈ Set.Icc 0 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le h] with x hx
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hx)⟩

end RadonNikodym

end ComplexRMK

/-! ### Jordan decomposition of a bounded functional on `C_c(X, ℝ)` -/

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X]

section JordanDecomposition

variable (φ : C_c(X, ℝ) →ₗ[ℝ] ℝ) {C : ℝ}

/-- The function underlying the positive part `posPart` of `φ`:
`f ↦ sup {(φ g)⁺ : g ∈ C_c(X, ℝ≥0), g ≤ f}`. -/
noncomputable def posPartAux (f : C_c(X, ℝ≥0)) : ℝ≥0 :=
  ⨆ g : {g : C_c(X, ℝ≥0) // g ≤ f}, (φ g.1.toReal).toNNReal

variable {φ}

@[simp] lemma _root_.CompactlySupportedContinuousMap.toReal_zero :
    (0 : C_c(X, ℝ≥0)).toReal = 0 := by
  ext; simp

lemma bddAbove_posPartAux (hφ : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → φ f ≤ C * c)
    (f : C_c(X, ℝ≥0)) :
    BddAbove (Set.range fun g : {g : C_c(X, ℝ≥0) // g ≤ f} ↦ (φ g.1.toReal).toNNReal) := by
  obtain ⟨c, hc⟩ := f.toReal.continuous.bounded_above_of_compact_support f.toReal.hasCompactSupport
  refine ⟨(C * max c 0).toNNReal, ?_⟩
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  refine Real.toNNReal_le_toNNReal (hφ _ _ (le_max_right _ _) fun x ↦ ?_)
  have : (f x : ℝ) ≤ c := by simpa using hc x
  simpa using le_max_of_le_left ((NNReal.coe_le_coe.mpr (hg x)).trans this)


variable (hφ : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → φ f ≤ C * c)
include hφ

lemma le_posPartAux {f g : C_c(X, ℝ≥0)} (hg : g ≤ f) :
    (φ g.toReal).toNNReal ≤ posPartAux φ f :=
  le_ciSup (bddAbove_posPartAux hφ f) (⟨g, hg⟩ : {g : C_c(X, ℝ≥0) // g ≤ f})

lemma le_posPartAux' {f g : C_c(X, ℝ≥0)} (hg : g ≤ f) : φ g.toReal ≤ posPartAux φ f :=
  (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr (le_posPartAux hφ hg))

omit hφ in
lemma posPartAux_le {f : C_c(X, ℝ≥0)} {a : ℝ≥0}
    (h : ∀ g : C_c(X, ℝ≥0), g ≤ f → (φ g.toReal).toNNReal ≤ a) : posPartAux φ f ≤ a :=
  have : Nonempty {g : C_c(X, ℝ≥0) // g ≤ f} := ⟨⟨0, fun _ ↦ zero_le⟩⟩
  ciSup_le fun g ↦ h g.1 g.2

omit hφ in
lemma exists_le_toNNReal_eq (g : C_c(X, ℝ≥0)) :
    ∃ g' ≤ g, (φ g.toReal).toNNReal = (φ g'.toReal).toNNReal ∧ 0 ≤ φ g'.toReal := by
  by_cases h : 0 ≤ φ g.toReal
  · exact ⟨g, le_rfl, rfl, h⟩
  · refine ⟨0, fun _ ↦ zero_le, ?_, by simp⟩
    simp [Real.toNNReal_of_nonpos (le_of_not_ge h)]

lemma posPartAux_add (f₁ f₂ : C_c(X, ℝ≥0)) :
    posPartAux φ (f₁ + f₂) = posPartAux φ f₁ + posPartAux φ f₂ := by
  apply le_antisymm
  · refine posPartAux_le fun g hg ↦ ?_
    obtain ⟨g₂, hg₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ f₁ ≤ g)
    have hle : g₂ ≤ f₂ := fun x ↦ by
      have h₁ := DFunLike.congr_fun hg₂ x
      have h₂ : g x ≤ f₁ x + f₂ x := hg x
      simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
        CompactlySupportedContinuousMap.inf_apply] at h₁ h₂ ⊢
      rcases le_total (g x) (f₁ x) with h | h
      · rw [min_eq_left h] at h₁
        have : g₂ x = 0 := by simpa using h₁
        simp [this]
      · rw [min_eq_right h] at h₁
        rw [← h₁] at h₂
        exact le_of_add_le_add_left h₂
    calc (φ g.toReal).toNNReal = (φ (g ⊓ f₁).toReal + φ g₂.toReal).toNNReal := by
          rw [← map_add, ← CompactlySupportedContinuousMap.toReal_add, hg₂]
      _ ≤ (φ (g ⊓ f₁).toReal).toNNReal + (φ g₂.toReal).toNNReal := Real.toNNReal_add_le
      _ ≤ _ := add_le_add (le_posPartAux hφ inf_le_right) (le_posPartAux hφ hle)
  · have : ∀ f : C_c(X, ℝ≥0), Nonempty {g : C_c(X, ℝ≥0) // g ≤ f} :=
      fun f ↦ ⟨⟨0, fun _ ↦ zero_le⟩⟩
    have e (f : C_c(X, ℝ≥0)) : (posPartAux φ f : ℝ) =
        ⨆ g : {g : C_c(X, ℝ≥0) // g ≤ f}, ((φ g.1.toReal).toNNReal : ℝ) := NNReal.coe_iSup _
    rw [← NNReal.coe_le_coe, NNReal.coe_add, e f₁, e f₂]
    refine ciSup_add_ciSup_le fun g₁ g₂ ↦ ?_
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    obtain ⟨g₁', hg₁', h₁, h₁'⟩ := exists_le_toNNReal_eq (φ := φ) g₁.1
    obtain ⟨g₂', hg₂', h₂, h₂'⟩ := exists_le_toNNReal_eq (φ := φ) g₂.1
    rw [h₁, h₂, ← Real.toNNReal_add h₁' h₂', ← map_add,
      ← CompactlySupportedContinuousMap.toReal_add]
    exact le_posPartAux hφ fun x ↦ add_le_add ((hg₁'.trans g₁.2) x) ((hg₂'.trans g₂.2) x)

lemma posPartAux_smul (c : ℝ≥0) (f : C_c(X, ℝ≥0)) :
    posPartAux φ (c • f) = c * posPartAux φ f := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine le_antisymm (posPartAux_le fun g hg ↦ ?_) (by simp)
    have : g = 0 := by ext x; simpa using hg x
    simp [this]
  apply le_antisymm
  · refine posPartAux_le fun g hg ↦ ?_
    have hle : c⁻¹ • g ≤ f := fun x ↦ by
      have : g x ≤ c * f x := hg x
      simpa [inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hc)] using this
    have hg' : g = c • (c⁻¹ • g) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hg', CompactlySupportedContinuousMap.toReal_smul, NNReal.smul_def, map_smul, smul_eq_mul,
      Real.toNNReal_mul NNReal.zero_le_coe, Real.toNNReal_coe]
    gcongr
    exact le_posPartAux hφ hle
  · rw [posPartAux, NNReal.mul_iSup]
    have : Nonempty {g : C_c(X, ℝ≥0) // g ≤ f} := ⟨⟨0, fun _ ↦ zero_le⟩⟩
    refine ciSup_le fun g ↦ ?_
    rw [← Real.toNNReal_coe (r := c), ← Real.toNNReal_mul NNReal.zero_le_coe, ← smul_eq_mul,
      ← map_smul, ← NNReal.smul_def, ← CompactlySupportedContinuousMap.toReal_smul]
    exact le_posPartAux hφ fun x ↦ by
      have : g.1 x ≤ f x := g.2 x
      simpa using mul_le_mul_of_nonneg_left this (zero_le (a := c))

/-- The positive part of a bounded real linear functional on `C_c(X, ℝ)`, as a `ℝ≥0`-linear
functional on `C_c(X, ℝ≥0)`: `f ↦ sup {φ g : 0 ≤ g ≤ f}`. -/
noncomputable def posPart : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun := posPartAux φ
  map_add' := posPartAux_add hφ
  map_smul' := posPartAux_smul hφ


omit hφ in
lemma _root_.CompactlySupportedContinuousMap.toReal_nnrealPart_of_nonneg {f : C_c(X, ℝ)}
    (hf : 0 ≤ f) : f.nnrealPart.toReal = f := by
  ext x; simpa using hf x

lemma posPart_toRealPositiveLinear_of_nonneg {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    toRealPositiveLinear (posPart hφ) f = posPart hφ f.nnrealPart := by
  simp [toRealPositiveLinear_apply, nnrealPart_neg_eq_zero_of_nonneg hf]

lemma le_posPart_toRealPositiveLinear {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    φ f ≤ toRealPositiveLinear (posPart hφ) f := by
  rw [posPart_toRealPositiveLinear_of_nonneg hφ hf]
  conv_lhs => rw [← toReal_nnrealPart_of_nonneg hf]
  exact le_posPartAux' hφ le_rfl

lemma posPart_toRealPositiveLinear_le {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    toRealPositiveLinear (posPart hφ) f ≤ max C 0 := by
  rw [posPart_toRealPositiveLinear_of_nonneg hφ fun x ↦ (hf x).1]
  have : posPart hφ f.nnrealPart ≤ (max C 0).toNNReal := by
    refine posPartAux_le fun g hg ↦ Real.toNNReal_le_toNNReal ?_
    refine (hφ _ 1 zero_le_one fun x ↦ ?_).trans (by simp)
    have h₁ : (g x : ℝ) ≤ f.nnrealPart x := NNReal.coe_le_coe.mpr (hg x)
    simp only [toReal_apply, NNReal.abs_eq, nnrealPart_apply, Real.coe_toNNReal _ (hf x).1] at h₁ ⊢
    exact h₁.trans (hf x).2
  simpa using NNReal.coe_le_coe.mpr this

/-- The positive linear functional `posPart - φ`. -/
noncomputable def negPart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((toRealPositiveLinear (posPart hφ)).toLinearMap - φ)
    fun _ hf ↦ sub_nonneg.mpr (le_posPart_toRealPositiveLinear hφ hf)

lemma negPart_apply (f : C_c(X, ℝ)) :
    negPart hφ f = toRealPositiveLinear (posPart hφ) f - φ f := rfl

lemma toRealPositiveLinear_posPart_le {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    toRealPositiveLinear (posPart hφ) f ≤ 2 * |C| :=
  (posPart_toRealPositiveLinear_le hφ hf).trans <| by
    linarith [max_le (le_abs_self C) (abs_nonneg C), abs_nonneg C]

lemma negPart_le {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : negPart hφ f ≤ 2 * |C| := by
  have h₁ := posPart_toRealPositiveLinear_le hφ hf
  have h₂ : -φ f ≤ C := by
    simpa using hφ (-f) 1 zero_le_one fun x ↦ by simpa [abs_of_nonneg (hf x).1] using (hf x).2
  rw [negPart_apply]
  linarith [max_le (le_abs_self C) (abs_nonneg C), le_abs_self C]

end JordanDecomposition

/-- **Jordan decomposition** of a bounded linear functional on `C_c(X, ℝ)`: it is the difference
of two positive linear functionals, both bounded by `2 * |C|` on functions with values in
`[0, 1]`. -/
theorem exists_eq_sub_of_bounded (φ : C_c(X, ℝ) →ₗ[ℝ] ℝ) {C : ℝ}
    (hφ : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → φ f ≤ C * c) :
    ∃ Λ₁ Λ₂ : C_c(X, ℝ) →ₚ[ℝ] ℝ, (∀ f, φ f = Λ₁ f - Λ₂ f) ∧
      ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → Λ₁ f ≤ 2 * |C| ∧ Λ₂ f ≤ 2 * |C| :=
  ⟨toRealPositiveLinear (posPart hφ), negPart hφ, fun f ↦ by simp [negPart_apply],
    fun _ hf ↦ ⟨toRealPositiveLinear_posPart_le hφ hf, negPart_le hφ hf⟩⟩

end ComplexRMK

/-! ### Construction of the complex Riesz measure -/

namespace ComplexRMK

open ZeroAtInfty Complex

variable {X : Type*} [TopologicalSpace X]

/-- A real function vanishing at infinity, seen as a complex function. -/
def _root_.ZeroAtInftyContinuousMap.toComplex (u : C₀(X, ℝ)) : C₀(X, ℂ) where
  toFun x := u x
  continuous_toFun := continuous_ofReal.comp u.continuous
  zero_at_infty' := by
    have := (Complex.continuous_ofReal.tendsto 0).comp u.zero_at_infty'
    rwa [Complex.ofReal_zero] at this

@[simp]
lemma _root_.ZeroAtInftyContinuousMap.toComplex_apply (u : C₀(X, ℝ)) (x : X) :
    u.toComplex x = u x := rfl

lemma _root_.ZeroAtInftyContinuousMap.norm_le_of_forall_le {E : Type*} [NormedAddCommGroup E]
    {f : C₀(X, E)} {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x, ‖f x‖ ≤ c) : ‖f‖ ≤ c := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_le hc]
  exact hf

lemma _root_.ZeroAtInftyContinuousMap.norm_apply_le {E : Type*} [NormedAddCommGroup E]
    (f : C₀(X, E)) (x : X) : ‖f x‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm x

variable (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

/-- The restriction of `Φ` to real compactly supported functions, as an `ℝ`-linear map. -/
noncomputable def restrictReal : C_c(X, ℝ) →ₗ[ℝ] ℂ where
  toFun u := Φ (u : C₀(X, ℝ)).toComplex
  map_add' u v := by
    rw [← map_add]
    congr 1
    ext x
    simp
  map_smul' c u := by
    rw [RingHom.id_apply, real_smul, ← smul_eq_mul, ← map_smul]
    congr 1
    ext x
    simp

lemma norm_restrictReal_le (u : C_c(X, ℝ)) {c : ℝ} (hc : 0 ≤ c) (hu : ∀ x, |u x| ≤ c) :
    ‖restrictReal Φ u‖ ≤ ‖Φ‖ * c :=
  (Φ.le_opNorm _).trans <| mul_le_mul_of_nonneg_left
    (ZeroAtInftyContinuousMap.norm_le_of_forall_le hc fun x ↦ by simpa using hu x) (norm_nonneg Φ)

/-- The real part of `Φ`, as a linear functional on `C_c(X, ℝ)`. -/
noncomputable def reFunctional : C_c(X, ℝ) →ₗ[ℝ] ℝ := reLm.comp (restrictReal Φ)

/-- The imaginary part of `Φ`, as a linear functional on `C_c(X, ℝ)`. -/
noncomputable def imFunctional : C_c(X, ℝ) →ₗ[ℝ] ℝ := imLm.comp (restrictReal Φ)

lemma reFunctional_le (u : C_c(X, ℝ)) (c : ℝ) (hc : 0 ≤ c) (hu : ∀ x, |u x| ≤ c) :
    reFunctional Φ u ≤ ‖Φ‖ * c :=
  (re_le_norm _).trans (norm_restrictReal_le Φ u hc hu)

lemma imFunctional_le (u : C_c(X, ℝ)) (c : ℝ) (hc : 0 ≤ c) (hu : ∀ x, |u x| ≤ c) :
    imFunctional Φ u ≤ ‖Φ‖ * c :=
  (im_le_norm _).trans (norm_restrictReal_le Φ u hc hu)

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

section Measures

variable {φ : C_c(X, ℝ) →ₗ[ℝ] ℝ} {C : ℝ}
  (hφ : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → φ f ≤ C * c)

/-- The measure associated to the positive part of a bounded functional on `C_c(X, ℝ)`. -/
noncomputable def posMeasure : Measure X := RealRMK.rieszMeasure (toRealPositiveLinear (posPart hφ))

/-- The measure associated to the negative part of a bounded functional on `C_c(X, ℝ)`. -/
noncomputable def negMeasure : Measure X := RealRMK.rieszMeasure (negPart hφ)

instance : IsFiniteMeasure (posMeasure hφ) :=
  isFiniteMeasure_rieszMeasure _ fun _ hf ↦ toRealPositiveLinear_posPart_le hφ hf

instance : IsFiniteMeasure (negMeasure hφ) :=
  isFiniteMeasure_rieszMeasure _ fun _ hf ↦ negPart_le hφ hf

instance : (posMeasure hφ).Regular := RealRMK.regular_rieszMeasure _

instance : (negMeasure hφ).Regular := RealRMK.regular_rieszMeasure _

lemma integral_posMeasure_sub_integral_negMeasure (u : C_c(X, ℝ)) :
    ∫ x, u x ∂posMeasure hφ - ∫ x, u x ∂negMeasure hφ = φ u := by
  simp [posMeasure, negMeasure, negPart_apply]

end Measures

/-- An auxiliary finite regular measure dominating the four measures in the Jordan decompositions
of the real and imaginary parts of `Φ`. -/
noncomputable def baseMeasure : Measure X :=
  posMeasure (reFunctional_le Φ) + negMeasure (reFunctional_le Φ) +
    posMeasure (imFunctional_le Φ) + negMeasure (imFunctional_le Φ)

instance : IsFiniteMeasure (baseMeasure Φ) := by unfold baseMeasure; infer_instance

instance : (baseMeasure Φ).Regular := by
  unfold baseMeasure
  exact regular_add _ _


lemma posMeasure_re_le : posMeasure (reFunctional_le Φ) ≤ baseMeasure Φ :=
  Measure.le_add_right (Measure.le_add_right (Measure.le_add_right le_rfl))

lemma negMeasure_re_le : negMeasure (reFunctional_le Φ) ≤ baseMeasure Φ :=
  Measure.le_add_right (Measure.le_add_right (Measure.le_add_left le_rfl))

lemma posMeasure_im_le : posMeasure (imFunctional_le Φ) ≤ baseMeasure Φ :=
  Measure.le_add_right (Measure.le_add_left le_rfl)

lemma negMeasure_im_le : negMeasure (imFunctional_le Φ) ≤ baseMeasure Φ :=
  Measure.le_add_left le_rfl

/-- The density of `rieszMeasure Φ` with respect to `baseMeasure Φ`. -/
noncomputable def density (x : X) : ℂ :=
  (((posMeasure (reFunctional_le Φ)).rnDeriv (baseMeasure Φ) x).toReal : ℂ) -
    ((negMeasure (reFunctional_le Φ)).rnDeriv (baseMeasure Φ) x).toReal +
  I * ((((posMeasure (imFunctional_le Φ)).rnDeriv (baseMeasure Φ) x).toReal : ℂ) -
    ((negMeasure (imFunctional_le Φ)).rnDeriv (baseMeasure Φ) x).toReal)

lemma integrable_density : Integrable (density Φ) (baseMeasure Φ) := by
  have h (m : Measure X) [IsFiniteMeasure m] :
      Integrable (fun x ↦ ((m.rnDeriv (baseMeasure Φ) x).toReal : ℂ)) (baseMeasure Φ) :=
    Measure.integrable_toReal_rnDeriv.ofReal
  exact ((h _).sub (h _)).add (((h _).sub (h _)).const_mul I)

lemma norm_density_le : ∀ᵐ x ∂baseMeasure Φ, ‖density Φ x‖ ≤ 2 := by
  filter_upwards [toReal_rnDeriv_mem_Icc (posMeasure_re_le Φ),
    toReal_rnDeriv_mem_Icc (negMeasure_re_le Φ), toReal_rnDeriv_mem_Icc (posMeasure_im_le Φ),
    toReal_rnDeriv_mem_Icc (negMeasure_im_le Φ)] with x h₁ h₂ h₃ h₄
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_I, one_mul, ← Complex.ofReal_sub, ← Complex.ofReal_sub, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have key {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) : |a - b| ≤ 1 :=
    abs_sub_le_iff.mpr ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩
  linarith [key h₁ h₂, key h₃ h₄]

omit [T2Space X] [LocallyCompactSpace X] in
lemma integrable_of_zeroAtInfty (f : C₀(X, ℂ)) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable f μ :=
  f.toBCF.integrable μ

lemma integrable_density_mul (f : C₀(X, ℂ)) :
    Integrable (fun x ↦ density Φ x * f x) (baseMeasure Φ) :=
  (integrable_density Φ).mul_bdd f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall f.norm_apply_le)

/-- On real compactly supported functions, `Φ` is integration against `density Φ`. -/
lemma apply_toComplex_eq_integral (u : C_c(X, ℝ)) :
    Φ (u : C₀(X, ℝ)).toComplex = ∫ x, density Φ x * u x ∂baseMeasure Φ := by
  have e : Φ (u : C₀(X, ℝ)).toComplex = (reFunctional Φ u : ℂ) + I * imFunctional Φ u := by
    rw [mul_comm]; exact (re_add_im _).symm
  rw [e, ← integral_posMeasure_sub_integral_negMeasure (reFunctional_le Φ),
    ← integral_posMeasure_sub_integral_negMeasure (imFunctional_le Φ)]
  have hu (m : Measure X) [IsFiniteMeasure m] : Integrable (fun x ↦ (u x : ℂ)) m :=
    integrable_of_zeroAtInfty (u : C₀(X, ℝ)).toComplex m
  set ν := baseMeasure Φ
  set r : Measure X → X → ℂ := fun m x ↦ ((m.rnDeriv ν x).toReal : ℂ)
  have hint {m : Measure X} (h : m ≤ ν) : Integrable (fun x ↦ r m x * u x) ν :=
    have : IsFiniteMeasure m := isFiniteMeasure_of_le ν h
    integrable_rnDeriv_mul h (hu m)
  set m₁ := posMeasure (reFunctional_le Φ)
  set m₂ := negMeasure (reFunctional_le Φ)
  set m₃ := posMeasure (imFunctional_le Φ)
  set m₄ := negMeasure (imFunctional_le Φ)
  have h₁₂ : Integrable (fun x ↦ r m₁ x * u x - r m₂ x * u x) ν :=
    (hint (posMeasure_re_le Φ)).sub (hint (negMeasure_re_le Φ))
  have h₃₄ : Integrable (fun x ↦ r m₃ x * u x - r m₄ x * u x) ν :=
    (hint (posMeasure_im_le Φ)).sub (hint (negMeasure_im_le Φ))
  have hd : (fun x ↦ density Φ x * u x) = fun x ↦
      (r m₁ x * u x - r m₂ x * u x) + I * (r m₃ x * u x - r m₄ x * u x) := by
    ext x; simp only [density, r, ν, m₁, m₂, m₃, m₄]; ring
  rw [hd, integral_add h₁₂ (h₃₄.const_mul I), integral_const_mul,
    integral_sub (hint (posMeasure_re_le Φ)) (hint (negMeasure_re_le Φ)),
    integral_sub (hint (posMeasure_im_le Φ)) (hint (negMeasure_im_le Φ))]
  rw [integral_rnDeriv_mul (posMeasure_re_le Φ), integral_rnDeriv_mul (negMeasure_re_le Φ),
    integral_rnDeriv_mul (posMeasure_im_le Φ), integral_rnDeriv_mul (negMeasure_im_le Φ)]
  simp only [integral_complex_ofReal]
  push_cast
  ring


/-- On compactly supported functions, `Φ` is integration against `density Φ`. -/
lemma apply_eq_integral_of_compactlySupported (g : C_c(X, ℂ)) :
    Φ g = ∫ x, density Φ x * g x ∂baseMeasure Φ := by
  let u : C_c(X, ℝ) := ⟨⟨fun x ↦ (g x).re, by fun_prop⟩, g.hasCompactSupport.comp_left zero_re⟩
  let v : C_c(X, ℝ) := ⟨⟨fun x ↦ (g x).im, by fun_prop⟩, g.hasCompactSupport.comp_left zero_im⟩
  have hg : (g : C₀(X, ℂ)) = (u : C₀(X, ℝ)).toComplex + I • (v : C₀(X, ℝ)).toComplex := by
    ext x
    simp [u, v, mul_comm I, re_add_im]
  have hu : Integrable (fun x ↦ density Φ x * (u x : ℂ)) (baseMeasure Φ) :=
    integrable_density_mul Φ (u : C₀(X, ℝ)).toComplex
  have hv : Integrable (fun x ↦ density Φ x * (v x : ℂ)) (baseMeasure Φ) :=
    integrable_density_mul Φ (v : C₀(X, ℝ)).toComplex
  rw [hg, map_add, map_smul, apply_toComplex_eq_integral, apply_toComplex_eq_integral, smul_eq_mul,
    ← integral_const_mul, ← integral_add hu (hv.const_mul I)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  conv_rhs => rw [← re_add_im (g x)]
  simp only [u, v, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
  ring

/-- `Φ` is integration against `density Φ`. -/
theorem apply_eq_integral (f : C₀(X, ℂ)) : Φ f = ∫ x, density Φ x * f x ∂baseMeasure Φ := by
  set ν := baseMeasure Φ
  set K := ∫ x, ‖density Φ x‖ ∂ν
  have hK : 0 ≤ K := integral_nonneg fun _ ↦ norm_nonneg _
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hc : 0 < ‖Φ‖ + K + 1 := by positivity
  set δ := ε / (‖Φ‖ + K + 1)
  have hδ : 0 < δ := div_pos hε hc
  obtain ⟨g, hg⟩ := exists_compactlySupported_norm_sub_le f hδ
  have h₁ : ‖Φ f - Φ g‖ ≤ ‖Φ‖ * δ := by
    rw [← map_sub]
    exact Φ.le_opNorm_of_le (ZeroAtInftyContinuousMap.norm_le_of_forall_le hδ.le fun x ↦ hg x)
  have h₂ : ‖∫ x, density Φ x * g x ∂ν - ∫ x, density Φ x * f x ∂ν‖ ≤ K * δ := by
    have hgi : Integrable (fun x ↦ density Φ x * g x) ν := integrable_density_mul Φ g
    rw [← integral_sub hgi (integrable_density_mul Φ f),
      ← integral_mul_const]
    refine norm_integral_le_of_norm_le ((integrable_density Φ).norm.mul_const δ)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    rw [← mul_sub, norm_mul, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)
  rw [apply_eq_integral_of_compactlySupported] at h₁
  calc dist (Φ f) (∫ x, density Φ x * f x ∂ν)
      ≤ ‖Φ f - ∫ x, density Φ x * g x ∂ν‖ +
          ‖∫ x, density Φ x * g x ∂ν - ∫ x, density Φ x * f x ∂ν‖ :=
        by rw [dist_eq_norm]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖Φ‖ * δ + K * δ := add_le_add h₁ h₂
    _ ≤ (‖Φ‖ + K + 1) * δ := by nlinarith
    _ = ε := mul_div_cancel₀ _ hc.ne'


section Retraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial retraction of `E` onto its closed unit ball. -/
noncomputable def unitBallRetraction (z : E) : E := (max 1 ‖z‖)⁻¹ • z

lemma continuous_unitBallRetraction : Continuous (unitBallRetraction (E := E)) :=
  ((continuous_const.max continuous_norm).inv₀ fun z ↦
    (one_pos.trans_le (le_max_left 1 ‖z‖)).ne').smul continuous_id

@[simp] lemma unitBallRetraction_zero : unitBallRetraction (0 : E) = 0 := by
  simp [unitBallRetraction]

lemma norm_unitBallRetraction_le (z : E) : ‖unitBallRetraction z‖ ≤ 1 := by
  have h : 0 < max 1 ‖z‖ := one_pos.trans_le (le_max_left _ _)
  rw [unitBallRetraction, norm_smul, norm_inv, Real.norm_of_nonneg h.le, inv_mul_le_one₀ h]
  exact le_max_right _ _

lemma norm_unitBallRetraction_sub_le {z w : E} (hw : ‖w‖ ≤ 1) :
    ‖unitBallRetraction z - w‖ ≤ 2 * ‖z - w‖ := by
  rcases le_total ‖z‖ 1 with h | h
  · rw [unitBallRetraction, max_eq_left h, inv_one, one_smul]
    linarith [norm_nonneg (z - w)]
  · have hz : 0 < ‖z‖ := one_pos.trans_le h
    have h₁ : ‖unitBallRetraction z - z‖ = ‖z‖ - 1 := by
      rw [unitBallRetraction, max_eq_right h,
        show ‖z‖⁻¹ • z - z = (‖z‖⁻¹ - 1) • z by rw [sub_smul, one_smul], norm_smul,
        Real.norm_eq_abs,
        abs_of_nonpos (by linarith [inv_le_one_of_one_le₀ h]), neg_sub, sub_mul, one_mul,
        inv_mul_cancel₀ hz.ne']
    have h₂ : ‖z‖ - 1 ≤ ‖z - w‖ := (sub_le_sub_left hw _).trans (norm_sub_norm_le z w)
    calc ‖unitBallRetraction z - w‖ ≤ ‖unitBallRetraction z - z‖ + ‖z - w‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖z - w‖ := by linarith

end Retraction

/-- The complex measure representing `Φ`: it has density `density Φ` with respect to the finite
regular measure `baseMeasure Φ`. -/
noncomputable def rieszMeasure : ComplexMeasure X := (baseMeasure Φ).withDensityᵥ (density Φ)

lemma variation_rieszMeasure :
    (rieszMeasure Φ).variation = (baseMeasure Φ).withDensity fun x ↦ ‖density Φ x‖ₑ :=
  Measure.variation_withDensityᵥ (integrable_density Φ)

/-- **Riesz–Markov–Kakutani representation theorem** (complex case, Rudin RCA 6.19): a bounded
linear functional `Φ` on `C₀(X, ℂ)` is integration against the complex measure `rieszMeasure Φ`. -/
theorem integral_rieszMeasure (f : C₀(X, ℂ)) : Φ f = ∫ᶜ x, f x ∂(rieszMeasure Φ) := by
  rw [apply_eq_integral, rieszMeasure,
    integral_withDensityᵥ (integrable_density Φ) (integrable_of_zeroAtInfty f _)]

lemma variation_rieszMeasure_univ :
    (rieszMeasure Φ).variation Set.univ =
      ENNReal.ofReal (∫ x, ‖density Φ x‖ ∂baseMeasure Φ) := by
  rw [variation_rieszMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_norm_eq_lintegral_enorm (integrable_density Φ)]

lemma norm_le_integral_norm_density : ‖Φ‖ ≤ ∫ x, ‖density Φ x‖ ∂baseMeasure Φ := by
  refine Φ.opNorm_le_bound (integral_nonneg fun _ ↦ norm_nonneg _) fun f ↦ ?_
  rw [apply_eq_integral, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_density Φ).norm.mul_const _)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_apply_le x) (norm_nonneg _)

lemma integral_norm_density_le [NormalSpace X] : ∫ x, ‖density Φ x‖ ∂baseMeasure Φ ≤ ‖Φ‖ := by
  set ν := baseMeasure Φ
  set d := density Φ
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- `s` is the conjugate of the sign of `d`, so that `s * d = |d|`.
  set s : X → ℂ := fun x ↦ starRingEnd ℂ (d x) / (‖d x‖ : ℂ)
  have hs_norm (x : X) : ‖s x‖ ≤ 1 := by
    simpa [s, norm_div] using div_self_le_one ‖d x‖
  have hs_mul (x : X) : s x * d x = ‖d x‖ := by
    rcases eq_or_ne (d x) 0 with h | h
    · simp [s, h]
    · have : (‖d x‖ : ℂ) ≠ 0 := by simpa using h
      simp only [s, div_mul_eq_mul_div, conj_mul']
      field_simp
  have hd := (integrable_density Φ).aemeasurable
  have hs_meas : AEStronglyMeasurable s ν :=
    ((Complex.continuous_conj.measurable.comp_aemeasurable hd).div
      (Complex.measurable_ofReal.comp_aemeasurable hd.norm)).aestronglyMeasurable
  have hs_int : Integrable s ν :=
    Integrable.of_bound hs_meas 1 (Filter.Eventually.of_forall hs_norm)
  obtain ⟨g, g_supp, g_approx, g_cont, -⟩ :=
    hs_int.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 4 by positivity)
  let g' : C_c(X, ℂ) := ⟨⟨fun x ↦ unitBallRetraction (g x),
    continuous_unitBallRetraction.comp g_cont⟩, g_supp.comp_left unitBallRetraction_zero⟩
  have hg'_norm : ‖(g' : C₀(X, ℂ))‖ ≤ 1 :=
    ZeroAtInftyContinuousMap.norm_le_of_forall_le zero_le_one fun x ↦
      norm_unitBallRetraction_le (g x)
  have hg'_int : Integrable (fun x ↦ d x * g' x) ν := integrable_density_mul Φ g'
  have hg'i : Integrable (fun x ↦ g' x) ν :=
    g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
  have hsd_int : Integrable (fun x ↦ d x * (s x - g' x)) ν :=
    (hs_int.sub hg'i).bdd_mul (integrable_density Φ).aestronglyMeasurable (norm_density_le Φ)
  have key : ((∫ x, ‖d x‖ ∂ν : ℝ) : ℂ) =
      ∫ x, d x * g' x ∂ν + ∫ x, d x * (s x - g' x) ∂ν := by
    rw [← integral_add hg'_int hsd_int, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [← hs_mul x]
    ring
  have h₁ : ‖∫ x, d x * g' x ∂ν‖ ≤ ‖Φ‖ := by
    rw [← apply_eq_integral_of_compactlySupported]
    exact Φ.le_opNorm_of_le hg'_norm |>.trans_eq (mul_one _)
  have h₂ : ‖∫ x, d x * (s x - g' x) ∂ν‖ ≤ ε := by
    calc ‖∫ x, d x * (s x - g' x) ∂ν‖ ≤ ∫ x, 4 * ‖s x - g x‖ ∂ν := by
          refine norm_integral_le_of_norm_le ((hs_int.sub
            (g_cont.integrable_of_hasCompactSupport g_supp)).norm.const_mul 4) ?_
          filter_upwards [norm_density_le Φ] with x hx
          rw [norm_mul, norm_sub_rev (s x)]
          calc ‖d x‖ * ‖g' x - s x‖ ≤ 2 * (2 * ‖g x - s x‖) := by
                gcongr
                exact norm_unitBallRetraction_sub_le (hs_norm x)
            _ = 4 * ‖s x - g x‖ := by rw [norm_sub_rev]; ring
      _ = 4 * ∫ x, ‖s x - g x‖ ∂ν := integral_const_mul _ _
      _ ≤ ε := by linarith
  have := congrArg norm key
  rw [norm_real, Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] at this
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

/-- The total variation of `rieszMeasure Φ` is the norm of `Φ` (Rudin RCA 6.19).

The `NormalSpace` assumption is only needed because Mathlib's density of compactly supported
continuous functions in `L¹` (`Integrable.exists_hasCompactSupport_integral_sub_le`) is currently
stated for normal spaces; it holds in every locally compact Hausdorff space. -/
theorem norm_eq_variation [NormalSpace X] :
    ENNReal.ofReal ‖Φ‖ = (rieszMeasure Φ).variation Set.univ := by
  rw [variation_rieszMeasure_univ,
    le_antisymm (norm_le_integral_norm_density Φ) (integral_norm_density_le Φ)]


/-- The positive functional `u ↦ ∫ u d|μ|`, where `μ = rieszMeasure Φ`. -/
noncomputable def variationFunctional : C₀(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun u := ∫ x, ‖density Φ x‖ * u x ∂baseMeasure Φ
      map_add' u v := by
        simp only [FunLike.coe_add, Pi.add_apply, mul_add]
        exact integral_add ((integrable_density Φ).norm.mul_bdd u.continuous.aestronglyMeasurable
          (.of_forall u.norm_apply_le)) ((integrable_density Φ).norm.mul_bdd
          v.continuous.aestronglyMeasurable (.of_forall v.norm_apply_le))
      map_smul' c u := by
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_left_comm _ c, integral_const_mul] }
    (∫ x, ‖density Φ x‖ ∂baseMeasure Φ) fun u ↦ by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le ((integrable_density Φ).norm.mul_const _)
        (.of_forall fun x ↦ ?_)
      rw [norm_mul, norm_norm]
      exact mul_le_mul_of_nonneg_left (u.norm_apply_le x) (norm_nonneg _)

lemma variationFunctional_apply (u : C₀(X, ℝ)) :
    variationFunctional Φ u = ∫ x, ‖density Φ x‖ * u x ∂baseMeasure Φ := rfl

end ComplexRMK


namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [NormalSpace X]
  (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

/-- Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. There exists a positive linear functional
`Λ` on `C₀(X, ℝ)` such that, `∀ f : C₀(X, ℂ)`, `|Φ f| ≤ Λ |f|` and `Λ |f| ≤ ‖Φ‖ ‖f‖` (`‖⬝‖` denotes
the supremum norm). [Rudin 87, part of proof of Theorem 6.19]

Here `Λ` is integration against the total variation of `rieszMeasure Φ` (for the Borel
`σ`-algebra). -/
theorem exists_pos_lin_func : ∃ Λ : C₀(X, ℝ) →L[ℝ] ℝ, (∀ u : C₀(X, ℝ), (∀ x, 0 ≤ u x) → 0 ≤ Λ u) ∧
    ∀ f : C₀(X, ℂ), ‖Φ f‖ ≤ Λ f.compNorm ∧ Λ f.compNorm ≤ ‖Φ‖ * ‖f‖ := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  refine ⟨variationFunctional Φ, fun u hu ↦ integral_nonneg fun x ↦
    mul_nonneg (norm_nonneg _) (hu x), fun f ↦ ⟨?_, ?_⟩⟩
  · rw [apply_eq_integral, variationFunctional_apply]
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall fun x ↦ ?_))
    simp
  · rw [variationFunctional_apply]
    calc ∫ x, ‖density Φ x‖ * f.compNorm x ∂baseMeasure Φ
        ≤ ∫ x, ‖density Φ x‖ * ‖f‖ ∂baseMeasure Φ :=
          integral_mono_of_nonneg (.of_forall fun x ↦ mul_nonneg (norm_nonneg _) (by simp))
            ((integrable_density Φ).norm.mul_const _)
            (.of_forall fun x ↦ mul_le_mul_of_nonneg_left (by simpa using f.norm_apply_le x)
              (norm_nonneg _))
      _ = (∫ x, ‖density Φ x‖ ∂baseMeasure Φ) * ‖f‖ := integral_mul_const _ _
      _ ≤ ‖Φ‖ * ‖f‖ := mul_le_mul_of_nonneg_right (integral_norm_density_le Φ) (norm_nonneg f)

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
