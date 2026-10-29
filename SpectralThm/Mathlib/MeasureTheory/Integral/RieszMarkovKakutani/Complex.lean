/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import SpectralThm.Mathlib.MeasureTheory.Measure.Complex.Integral
public import SpectralThm.Mathlib.Topology.ContinuousMap.ZeroAtInfty

import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import SpectralThm.Mathlib.Analysis.Normed.Module.Ball.Retraction
import SpectralThm.Mathlib.MeasureTheory.Measure.Complex.RadonNikodym
import SpectralThm.Mathlib.MeasureTheory.Measure.Regular
import SpectralThm.Mathlib.MeasureTheory.VectorMeasure.Variation.EMetric
import SpectralThm.Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Riesz–Markov–Kakutani representation theorem for complex linear functionals

This file proves the **Riesz–Markov–Kakutani representation theorem** for bounded complex linear
functionals on `C₀(X, ℂ)`, where `X` is a locally compact Hausdorff space: every such functional
`Φ` is integration against a complex Borel measure `ComplexRMK.rieszMeasure Φ`, whose total
variation is `‖Φ‖`.

## Main definitions

* `ComplexRMK.rieszMeasure Φ`: the complex measure associated to a bounded linear functional
  `Φ : C₀(X, ℂ) →L[ℂ] ℂ`.
* `ComplexRMK.posPart`, `ComplexRMK.negPart`: the positive and negative parts of a bounded linear
  functional on `C_c(X, ℝ)`.

## Main results

* `ComplexRMK.integral_rieszMeasure`: `Φ f = ∫ f d(rieszMeasure Φ)` for all `f : C₀(X, ℂ)`.
* `ComplexRMK.norm_eq_variation`: `‖Φ‖ = |rieszMeasure Φ|(X)`.
* `ComplexRMK.rieszMeasure_unique`: uniqueness of the representing measure among complex measures
  with regular variation.
* `MeasureTheory.ComplexMeasure.eq_zero_of_forall_integral_eq_zero`: a complex measure with regular
  variation which integrates every compactly supported continuous function to zero is zero.
* `ComplexRMK.exists_eq_sub_of_bounded`: Jordan decomposition of a bounded linear functional on
  `C_c(X, ℝ)` into a difference of two positive linear functionals.
* `ComplexRMK.exists_dominating_positive_functional`: a positive functional `Λ` on `C₀(X, ℝ)` with
  `‖Φ f‖ ≤ Λ |f| ≤ ‖Φ‖ ‖f‖`.

## Implementation notes

The proof of existence reduces to the case of positive `ℝ`-linear functionals on `C_c(X, ℝ)`
(`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`), avoiding the `L¹`–`L^∞` duality
used by Rudin:

* the real and imaginary parts `reFunctional Φ`, `imFunctional Φ` of the restriction of `Φ` to
  `C_c(X, ℝ)` are bounded `ℝ`-linear functionals;
* each of them is a difference `posPart - negPart` of positive functionals (Jordan decomposition,
  `posPart φ f = sup {φ g : 0 ≤ g ≤ f}`), giving four finite regular measures by the real
  Riesz–Markov–Kakutani theorem;
* with `ν = baseMeasure Φ` the sum of these four measures, Radon–Nikodym gives a bounded density
  `density Φ` with `Φ f = ∫ density Φ * f dν`, first for `f ∈ C_c(X, ℂ)` and then, by uniform
  approximation, for `f ∈ C₀(X, ℂ)` (`apply_eq_integral`);
* `rieszMeasure Φ := ν.withDensityᵥ (density Φ)`, and `ComplexMeasure.integral_withDensityᵥ`
  identifies the integrals;
* `|rieszMeasure Φ| = |density Φ| ν`, and `∫ |density Φ| dν = ‖Φ‖` by testing `Φ` against
  continuous approximations of the conjugate sign of `density Φ`.

The uniqueness proof uses the polar decomposition of a complex measure
(`ComplexMeasure.ae_norm_rnDeriv_variation_eq_one`, `ComplexMeasure.integral_eq_integral_rnDeriv`).

## References

* Section 6 of [Walter Rudin, Real and Complex Analysis.][Rud87]

## TODO

* Remove `[NormalSpace X]` from `rieszMeasure_unique` and `norm_eq_variation`, by generalising
  `Integrable.exists_hasCompactSupport_integral_sub_le` to locally compact Hausdorff spaces.
* Prove that `(rieszMeasure Φ).variation` is regular, and more generally that differences of such
  measures are; together with `rieszMeasure_unique` this gives linearity of `rieszMeasure` and the
  isometric isomorphism between the dual of `C₀(X, ℂ)` and regular complex Borel measures.
-/

@[expose] public section

open NNReal Complex MeasureTheory CompactlySupportedContinuousMap
open scoped ZeroAtInfty CompactlySupported ComplexConjugate MeasureTheory.ComplexMeasure

/-! ### Uniqueness -/

namespace MeasureTheory.ComplexMeasure

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- A complex measure with regular variation which integrates every compactly supported continuous
function to zero is zero [Rudin RCA 6.19]. -/
theorem eq_zero_of_forall_integral_eq_zero {μ : ComplexMeasure X} [μ.variation.Regular]
    (h : ∀ f : C_c(X, ℂ), ∫ᶜ x, f x ∂μ = 0) : μ = 0 := by
  rw [← VectorMeasure.variation_univ_eq_zero, ← measureReal_eq_zero_iff]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) measureReal_nonneg
  set a := μ.rnDeriv μ.variation
  have ha : Integrable a μ.variation := μ.integrable_rnDeriv μ.variation
  have ha₁ : ∀ᵐ x ∂μ.variation, ‖a x‖ = 1 := μ.ae_norm_rnDeriv_variation_eq_one
  have has : Integrable (fun x ↦ star (a x)) μ.variation :=
    (conjCLE : ℂ →L[ℝ] ℂ).integrable_comp ha
  -- approximate `star a` in `L¹(|μ|)` by a compactly supported continuous function `g`
  obtain ⟨g, hg_supp, hg_approx, hg_cont, hg_int⟩ :=
    has.exists_hasCompactSupport_integral_sub_le hε
  have hag : ∫ x, a x * g x ∂μ.variation = 0 := by
    rw [← μ.integral_eq_integral_rnDeriv hg_int]
    exact h ⟨⟨g, hg_cont⟩, hg_supp⟩
  have hint : ∫ x, (star (a x) - g x) * a x ∂μ.variation = μ.variation.real Set.univ := by
    have : (fun x ↦ (star (a x) - g x) * a x) =ᵐ[μ.variation] fun x ↦ 1 - a x * g x := by
      filter_upwards [ha₁] with x hx
      rw [sub_mul, star_def, conj_mul', hx, mul_comm]
      norm_num
    rw [integral_congr_ae this, integral_sub (integrable_const _)
      (hg_int.bdd_mul ha.aestronglyMeasurable (ha₁.mono fun _ hx ↦ hx.le)), hag, sub_zero,
      integral_const, real_smul, mul_one]
  calc μ.variation.real Set.univ = ‖∫ x, (star (a x) - g x) * a x ∂μ.variation‖ := by
        rw [hint, norm_real, Real.norm_of_nonneg measureReal_nonneg]
    _ ≤ ∫ x, ‖star (a x) - g x‖ ∂μ.variation :=
        norm_integral_le_of_norm_le (has.sub hg_int).norm (ha₁.mono fun x hx ↦ by simp [hx])
    _ ≤ 0 + ε := by rwa [zero_add]

end MeasureTheory.ComplexMeasure

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Uniqueness** of the representing measure in the Riesz–Markov–Kakutani theorem: two complex
measures representing the same bounded linear functional on `C₀(X, ℂ)` are equal, provided the
variation of their difference is regular. -/
theorem rieszMeasure_unique {μ₁ μ₂ : ComplexMeasure X} [(μ₁ - μ₂).variation.Regular]
    (Φ : C₀(X, ℂ) →L[ℂ] ℂ) (h₁ : ∀ f : C₀(X, ℂ), ∫ᶜ x, f x ∂μ₁ = Φ f)
    (h₂ : ∀ f : C₀(X, ℂ), ∫ᶜ x, f x ∂μ₂ = Φ f) :
    μ₁ = μ₂ := by
  refine eq_of_sub_eq_zero (ComplexMeasure.eq_zero_of_forall_integral_eq_zero fun f ↦ ?_)
  have hf (ν : ComplexMeasure X) : ν.Integrable f := (f : C₀(X, ℂ)).toBCF.integrable _
  rw [VectorMeasure.integral_sub_vectorMeasure (hf μ₁) (hf μ₂)]
  exact sub_eq_zero.mpr ((h₁ f).trans (h₂ f).symm)

end ComplexRMK

namespace RealRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- The Riesz measure of a positive functional `Λ` is finite if `Λ` is bounded on functions with
values in `[0, 1]`. -/
theorem isFiniteMeasure_rieszMeasure (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) {C : ℝ}
    (hΛ : ∀ f : C_c(X, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) → Λ f ≤ C) :
    IsFiniteMeasure (rieszMeasure Λ) := by
  refine ⟨lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := C))⟩
  rw [isOpen_univ.measure_eq_iSup_isCompact]
  refine iSup₂_le fun K _ ↦ iSup_le fun hK ↦ ?_
  obtain ⟨f, hf1, -, hfc, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  exact (rieszMeasure_le_of_eq_one Λ (f := ⟨f, hfc⟩) (fun x ↦ (hf01 x).1) hK
    fun x hx ↦ hf1 hx).trans (ENNReal.ofReal_le_ofReal (hΛ ⟨f, hfc⟩ hf01))

end RealRMK

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

instance (f : C_c(X, ℝ≥0)) : Nonempty {g : C_c(X, ℝ≥0) // g ≤ f} :=
  ⟨⟨0, fun _ ↦ zero_le⟩⟩

lemma bddAbove_posPartAux (hφ : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → φ f ≤ C * c)
    (f : C_c(X, ℝ≥0)) :
    BddAbove (Set.range fun g : {g : C_c(X, ℝ≥0) // g ≤ f} ↦ (φ g.1.toReal).toNNReal) := by
  obtain ⟨c, hc⟩ := f.toReal.continuous.bounded_above_of_compact_support f.toReal.hasCompactSupport
  refine ⟨(C * max c 0).toNNReal, ?_⟩
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  refine Real.toNNReal_le_toNNReal (hφ _ _ (le_max_right _ _) fun x ↦ ?_)
  have : (f x : ℝ) ≤ c := by simpa using hc x
  simpa using le_max_of_le_left ((NNReal.coe_le_coe.mpr (hg x)).trans this)

lemma posPartAux_le {f : C_c(X, ℝ≥0)} {a : ℝ≥0}
    (h : ∀ g : C_c(X, ℝ≥0), g ≤ f → (φ g.toReal).toNNReal ≤ a) : posPartAux φ f ≤ a :=
  ciSup_le fun g ↦ h g.1 g.2

lemma exists_le_toNNReal_eq (g : C_c(X, ℝ≥0)) :
    ∃ g' ≤ g, (φ g.toReal).toNNReal = (φ g'.toReal).toNNReal ∧ 0 ≤ φ g'.toReal := by
  by_cases h : 0 ≤ φ g.toReal
  · exact ⟨g, le_rfl, rfl, h⟩
  · exact ⟨0, fun _ ↦ zero_le, by simp [Real.toNNReal_of_nonpos (le_of_not_ge h)], by simp⟩

variable (hφ : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → φ f ≤ C * c)
include hφ

lemma le_posPartAux {f g : C_c(X, ℝ≥0)} (hg : g ≤ f) :
    (φ g.toReal).toNNReal ≤ posPartAux φ f :=
  le_ciSup (bddAbove_posPartAux hφ f) (⟨g, hg⟩ : {g : C_c(X, ℝ≥0) // g ≤ f})

lemma apply_le_posPartAux {f g : C_c(X, ℝ≥0)} (hg : g ≤ f) : φ g.toReal ≤ posPartAux φ f :=
  (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr (le_posPartAux hφ hg))

lemma posPartAux_add (f₁ f₂ : C_c(X, ℝ≥0)) :
    posPartAux φ (f₁ + f₂) = posPartAux φ f₁ + posPartAux φ f₂ := by
  apply le_antisymm
  · refine posPartAux_le fun g hg ↦ ?_
    obtain ⟨g₂, hg₂⟩ := CompactlySupportedContinuousMap.exists_add_of_le (inf_le_left : g ⊓ f₁ ≤ g)
    have hle : g₂ ≤ f₂ := fun x ↦ by
      have h₁ := DFunLike.congr_fun hg₂ x
      have h₂ : g x ≤ f₁ x + f₂ x := hg x
      simp only [coe_add, Pi.add_apply, inf_apply] at h₁ h₂
      rcases le_total (g x) (f₁ x) with h | h
      · rw [min_eq_left h, add_eq_left] at h₁
        simp [h₁]
      · rw [min_eq_right h] at h₁
        rw [← h₁] at h₂
        exact le_of_add_le_add_left h₂
    calc (φ g.toReal).toNNReal = (φ (g ⊓ f₁).toReal + φ g₂.toReal).toNNReal := by
          rw [← map_add, ← toReal_add, hg₂]
      _ ≤ (φ (g ⊓ f₁).toReal).toNNReal + (φ g₂.toReal).toNNReal := Real.toNNReal_add_le
      _ ≤ _ := add_le_add (le_posPartAux hφ inf_le_right) (le_posPartAux hφ hle)
  · rw [← NNReal.coe_le_coe, NNReal.coe_add, posPartAux, posPartAux, NNReal.coe_iSup,
      NNReal.coe_iSup]
    refine ciSup_add_ciSup_le fun g₁ g₂ ↦ ?_
    rw [← NNReal.coe_add, NNReal.coe_le_coe]
    obtain ⟨g₁', hg₁', h₁, h₁'⟩ := exists_le_toNNReal_eq (φ := φ) g₁.1
    obtain ⟨g₂', hg₂', h₂, h₂'⟩ := exists_le_toNNReal_eq (φ := φ) g₂.1
    rw [h₁, h₂, ← Real.toNNReal_add h₁' h₂', ← map_add, ← toReal_add]
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
      simpa [inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hc)] using hg x
    have hg' : g = c • (c⁻¹ • g) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [hg', toReal_smul, NNReal.smul_def, map_smul, smul_eq_mul,
      Real.toNNReal_mul NNReal.zero_le_coe, Real.toNNReal_coe]
    gcongr
    exact le_posPartAux hφ hle
  · rw [posPartAux, NNReal.mul_iSup]
    refine ciSup_le fun g ↦ ?_
    rw [← Real.toNNReal_coe (r := c), ← Real.toNNReal_mul NNReal.zero_le_coe, ← smul_eq_mul,
      ← map_smul, ← NNReal.smul_def, ← toReal_smul]
    exact le_posPartAux hφ fun x ↦ by
      simpa using mul_le_mul_of_nonneg_left (g.2 x) (zero_le (a := c))

/-- The positive part of a bounded real linear functional `φ` on `C_c(X, ℝ)`, as an `ℝ≥0`-linear
functional on `C_c(X, ℝ≥0)`: `f ↦ sup {φ g : 0 ≤ g ≤ f}`. -/
noncomputable def posPart : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun := posPartAux φ
  map_add' := posPartAux_add hφ
  map_smul' := posPartAux_smul hφ

lemma toRealPositiveLinear_posPart_of_nonneg {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    toRealPositiveLinear (posPart hφ) f = posPart hφ f.nnrealPart := by
  simp [toRealPositiveLinear_apply, nnrealPart_neg_eq_zero_of_nonneg hf]

lemma le_toRealPositiveLinear_posPart {f : C_c(X, ℝ)} (hf : 0 ≤ f) :
    φ f ≤ toRealPositiveLinear (posPart hφ) f := by
  rw [toRealPositiveLinear_posPart_of_nonneg hφ hf]
  conv_lhs => rw [← toReal_nnrealPart_of_nonneg hf]
  exact apply_le_posPartAux hφ le_rfl

lemma toRealPositiveLinear_posPart_le_max {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    toRealPositiveLinear (posPart hφ) f ≤ max C 0 := by
  rw [toRealPositiveLinear_posPart_of_nonneg hφ fun x ↦ (hf x).1]
  have : posPart hφ f.nnrealPart ≤ (max C 0).toNNReal := by
    refine posPartAux_le fun g hg ↦ Real.toNNReal_le_toNNReal ?_
    refine (hφ _ 1 zero_le_one fun x ↦ ?_).trans (by simp)
    have h₁ : (g x : ℝ) ≤ f.nnrealPart x := NNReal.coe_le_coe.mpr (hg x)
    simp only [toReal_apply, NNReal.abs_eq, nnrealPart_apply, Real.coe_toNNReal _ (hf x).1] at h₁ ⊢
    exact h₁.trans (hf x).2
  simpa using NNReal.coe_le_coe.mpr this

lemma toRealPositiveLinear_posPart_le {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    toRealPositiveLinear (posPart hφ) f ≤ 2 * |C| :=
  (toRealPositiveLinear_posPart_le_max hφ hf).trans <| by
    linarith [max_le (le_abs_self C) (abs_nonneg C), abs_nonneg C]

/-- The negative part `posPart φ - φ` of a bounded real linear functional `φ` on `C_c(X, ℝ)`, as a
positive linear functional. -/
noncomputable def negPart : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ ((toRealPositiveLinear (posPart hφ)).toLinearMap - φ)
    fun _ hf ↦ sub_nonneg.mpr (le_toRealPositiveLinear_posPart hφ hf)

lemma negPart_apply (f : C_c(X, ℝ)) :
    negPart hφ f = toRealPositiveLinear (posPart hφ) f - φ f :=
  rfl

lemma negPart_le {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : negPart hφ f ≤ 2 * |C| := by
  have h₁ := toRealPositiveLinear_posPart_le_max hφ hf
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

/-! ### Construction of the complex Riesz measure -/

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

lemma restrictReal_apply (u : C_c(X, ℝ)) : restrictReal Φ u = Φ (u : C₀(X, ℝ)).toComplex :=
  rfl

lemma norm_restrictReal_le (u : C_c(X, ℝ)) {c : ℝ} (hc : 0 ≤ c) (hu : ∀ x, |u x| ≤ c) :
    ‖restrictReal Φ u‖ ≤ ‖Φ‖ * c :=
  Φ.le_opNorm_of_le <| (ZeroAtInftyContinuousMap.norm_le hc).mpr fun x ↦ by simpa using hu x

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
  RealRMK.isFiniteMeasure_rieszMeasure _ fun _ hf ↦ toRealPositiveLinear_posPart_le hφ hf

instance : IsFiniteMeasure (negMeasure hφ) :=
  RealRMK.isFiniteMeasure_rieszMeasure _ fun _ hf ↦ negPart_le hφ hf

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

instance : (baseMeasure Φ).Regular := by unfold baseMeasure; infer_instance

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
  filter_upwards [Measure.toReal_rnDeriv_mem_Icc_of_le (posMeasure_re_le Φ),
    Measure.toReal_rnDeriv_mem_Icc_of_le (negMeasure_re_le Φ),
    Measure.toReal_rnDeriv_mem_Icc_of_le (posMeasure_im_le Φ),
    Measure.toReal_rnDeriv_mem_Icc_of_le (negMeasure_im_le Φ)] with x h₁ h₂ h₃ h₄
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_I, one_mul, ← ofReal_sub, ← ofReal_sub, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have key {a b : ℝ} (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) : |a - b| ≤ 1 :=
    abs_sub_le_iff.mpr ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩
  linarith [key h₁ h₂, key h₃ h₄]

lemma integrable_density_mul (f : C₀(X, ℂ)) :
    Integrable (fun x ↦ density Φ x * f x) (baseMeasure Φ) :=
  (integrable_density Φ).mul_bdd f.continuous.aestronglyMeasurable
    (.of_forall f.norm_coe_le_norm)

/-- On real compactly supported functions, `Φ` is integration against `density Φ`. -/
lemma apply_toComplex_eq_integral (u : C_c(X, ℝ)) :
    Φ (u : C₀(X, ℝ)).toComplex = ∫ x, density Φ x * u x ∂baseMeasure Φ := by
  have e : Φ (u : C₀(X, ℝ)).toComplex = (reFunctional Φ u : ℂ) + I * imFunctional Φ u := by
    rw [mul_comm]; exact (re_add_im _).symm
  rw [e, ← integral_posMeasure_sub_integral_negMeasure (reFunctional_le Φ),
    ← integral_posMeasure_sub_integral_negMeasure (imFunctional_le Φ)]
  set ν := baseMeasure Φ
  set r : Measure X → X → ℂ := fun m x ↦ ((m.rnDeriv ν x).toReal : ℂ)
  have hint {m : Measure X} (h : m ≤ ν) : Integrable (fun x ↦ r m x * u x) ν :=
    have : IsFiniteMeasure m := isFiniteMeasure_of_le ν h
    Measure.integrable_rnDeriv_mul_of_le h ((u : C₀(X, ℝ)).toComplex.toBCF.integrable m)
  set m₁ := posMeasure (reFunctional_le Φ)
  set m₂ := negMeasure (reFunctional_le Φ)
  set m₃ := posMeasure (imFunctional_le Φ)
  set m₄ := negMeasure (imFunctional_le Φ)
  have hd : (fun x ↦ density Φ x * u x) = fun x ↦
      (r m₁ x * u x - r m₂ x * u x) + I * (r m₃ x * u x - r m₄ x * u x) := by
    ext x; simp only [density, r, ν, m₁, m₂, m₃, m₄]; ring
  have h₁₂ : Integrable (fun x ↦ r m₁ x * u x - r m₂ x * u x) ν :=
    (hint (posMeasure_re_le Φ)).sub (hint (negMeasure_re_le Φ))
  have h₃₄ : Integrable (fun x ↦ r m₃ x * u x - r m₄ x * u x) ν :=
    (hint (posMeasure_im_le Φ)).sub (hint (negMeasure_im_le Φ))
  rw [hd, integral_add h₁₂ (h₃₄.const_mul I), integral_const_mul,
    integral_sub (hint (posMeasure_re_le Φ)) (hint (negMeasure_re_le Φ)),
    integral_sub (hint (posMeasure_im_le Φ)) (hint (negMeasure_im_le Φ)),
    Measure.integral_rnDeriv_mul_of_le (posMeasure_re_le Φ),
    Measure.integral_rnDeriv_mul_of_le (negMeasure_re_le Φ),
    Measure.integral_rnDeriv_mul_of_le (posMeasure_im_le Φ),
    Measure.integral_rnDeriv_mul_of_le (negMeasure_im_le Φ)]
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
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  dsimp only
  conv_rhs => rw [← re_add_im (g x)]
  simp only [u, v, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk]
  ring

/-- `Φ` is integration against `density Φ` with respect to `baseMeasure Φ`. -/
theorem apply_eq_integral (f : C₀(X, ℂ)) : Φ f = ∫ x, density Φ x * f x ∂baseMeasure Φ := by
  set ν := baseMeasure Φ
  set K := ∫ x, ‖density Φ x‖ ∂ν
  have hK : 0 ≤ K := integral_nonneg fun _ ↦ norm_nonneg _
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hc : 0 < ‖Φ‖ + K + 1 := by positivity
  set δ := ε / (‖Φ‖ + K + 1)
  have hδ : 0 < δ := div_pos hε hc
  obtain ⟨g, hg⟩ := f.exists_compactlySupported_norm_sub_le hδ
  have h₁ : ‖Φ f - ∫ x, density Φ x * g x ∂ν‖ ≤ ‖Φ‖ * δ := by
    rw [← apply_eq_integral_of_compactlySupported, ← map_sub]
    exact Φ.le_opNorm_of_le ((ZeroAtInftyContinuousMap.norm_le hδ.le).mpr hg)
  have h₂ : ‖∫ x, density Φ x * g x ∂ν - ∫ x, density Φ x * f x ∂ν‖ ≤ K * δ := by
    have hgi : Integrable (fun x ↦ density Φ x * g x) ν := integrable_density_mul Φ g
    rw [← integral_sub hgi (integrable_density_mul Φ f), ← integral_mul_const]
    refine norm_integral_le_of_norm_le ((integrable_density Φ).norm.mul_const δ)
      (.of_forall fun x ↦ ?_)
    rw [← mul_sub, norm_mul, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (hg x) (norm_nonneg _)
  calc dist (Φ f) (∫ x, density Φ x * f x ∂ν)
      ≤ ‖Φ f - ∫ x, density Φ x * g x ∂ν‖ +
          ‖∫ x, density Φ x * g x ∂ν - ∫ x, density Φ x * f x ∂ν‖ := by
        rw [dist_eq_norm]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖Φ‖ * δ + K * δ := add_le_add h₁ h₂
    _ ≤ (‖Φ‖ + K + 1) * δ := by nlinarith
    _ = ε := mul_div_cancel₀ _ hc.ne'

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
    ComplexMeasure.integral_withDensityᵥ (f := f) (integrable_density Φ) (f.toBCF.integrable _)]

lemma variation_rieszMeasure_univ :
    (rieszMeasure Φ).variation Set.univ = .ofReal (∫ x, ‖density Φ x‖ ∂baseMeasure Φ) := by
  rw [variation_rieszMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_norm_eq_lintegral_enorm (integrable_density Φ)]

lemma norm_le_integral_norm_density : ‖Φ‖ ≤ ∫ x, ‖density Φ x‖ ∂baseMeasure Φ := by
  refine Φ.opNorm_le_bound (integral_nonneg fun _ ↦ norm_nonneg _) fun f ↦ ?_
  rw [apply_eq_integral, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_density Φ).norm.mul_const _)
    (.of_forall fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)

lemma integral_norm_density_le [NormalSpace X] : ∫ x, ‖density Φ x‖ ∂baseMeasure Φ ≤ ‖Φ‖ := by
  set ν := baseMeasure Φ
  set d := density Φ
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  -- `s` is the conjugate of the sign of `d`, so that `s * d = |d|`.
  set s : X → ℂ := fun x ↦ conj (d x) / (‖d x‖ : ℂ)
  have hs_norm (x : X) : ‖s x‖ ≤ 1 := by
    simpa [s, norm_div] using div_self_le_one ‖d x‖
  have hs_mul (x : X) : s x * d x = ‖d x‖ := by
    rcases eq_or_ne (d x) 0 with h | h
    · simp [s, h]
    · have : (‖d x‖ : ℂ) ≠ 0 := by simpa using h
      simp only [s, div_mul_eq_mul_div, conj_mul']
      field_simp
  have hd := (integrable_density Φ).aemeasurable
  have hs_int : Integrable s ν :=
    .of_bound ((continuous_conj.measurable.comp_aemeasurable hd).div
      (measurable_ofReal.comp_aemeasurable hd.norm)).aestronglyMeasurable 1
      (.of_forall hs_norm)
  obtain ⟨g, g_supp, g_approx, g_cont, -⟩ :=
    hs_int.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 4 by positivity)
  -- `g'` is a continuous compactly supported approximation of `s` with values in the unit ball
  let g' : C_c(X, ℂ) := ⟨⟨fun x ↦ unitBallRetraction (g x), by fun_prop⟩,
    g_supp.comp_left unitBallRetraction_zero⟩
  have hg'i : Integrable (fun x ↦ g' x) ν :=
    g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
  have hg'_int : Integrable (fun x ↦ d x * g' x) ν := integrable_density_mul Φ g'
  have hsd_int : Integrable (fun x ↦ d x * (s x - g' x)) ν :=
    (hs_int.sub hg'i).bdd_mul (integrable_density Φ).aestronglyMeasurable (norm_density_le Φ)
  have key : ((∫ x, ‖d x‖ ∂ν : ℝ) : ℂ) = ∫ x, d x * g' x ∂ν + ∫ x, d x * (s x - g' x) ∂ν := by
    rw [← integral_add hg'_int hsd_int, ← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [← hs_mul x]
    ring
  have h₁ : ‖∫ x, d x * g' x ∂ν‖ ≤ ‖Φ‖ := by
    rw [← apply_eq_integral_of_compactlySupported]
    refine Φ.le_opNorm_of_le ((ZeroAtInftyContinuousMap.norm_le zero_le_one).mpr fun x ↦ ?_)
      |>.trans_eq (mul_one _)
    exact norm_unitBallRetraction_le (g x)
  have h₂ : ‖∫ x, d x * (s x - g' x) ∂ν‖ ≤ ε :=
    calc ‖∫ x, d x * (s x - g' x) ∂ν‖ ≤ ∫ x, 4 * ‖s x - g x‖ ∂ν := by
          refine norm_integral_le_of_norm_le ((hs_int.sub
            (g_cont.integrable_of_hasCompactSupport g_supp)).norm.const_mul 4) ?_
          filter_upwards [norm_density_le Φ] with x hx
          rw [norm_mul, norm_sub_rev (s x), norm_sub_rev (s x)]
          calc ‖d x‖ * ‖g' x - s x‖ ≤ 2 * (2 * ‖g x - s x‖) := by
                gcongr
                exact norm_unitBallRetraction_sub_le (hs_norm x)
            _ = 4 * ‖g x - s x‖ := by ring
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

/-- The positive functional `u ↦ ∫ u d|μ|` on `C₀(X, ℝ)`, where `μ = rieszMeasure Φ`. -/
noncomputable def variationFunctional : C₀(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun u := ∫ x, ‖density Φ x‖ * u x ∂baseMeasure Φ
      map_add' u v := by
        simp only [FunLike.coe_add, Pi.add_apply, mul_add]
        exact integral_add ((integrable_density Φ).norm.mul_bdd u.continuous.aestronglyMeasurable
          (.of_forall u.norm_coe_le_norm)) ((integrable_density Φ).norm.mul_bdd
          v.continuous.aestronglyMeasurable (.of_forall v.norm_coe_le_norm))
      map_smul' c u := by
        simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_left_comm _ c, integral_const_mul] }
    (∫ x, ‖density Φ x‖ ∂baseMeasure Φ) fun u ↦ by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le ((integrable_density Φ).norm.mul_const _)
        (.of_forall fun x ↦ ?_)
      rw [norm_mul, norm_norm]
      exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm x) (norm_nonneg _)

lemma variationFunctional_apply (u : C₀(X, ℝ)) :
    variationFunctional Φ u = ∫ x, ‖density Φ x‖ * u x ∂baseMeasure Φ :=
  rfl

end ComplexRMK

namespace ComplexRMK

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [NormalSpace X]
  (Φ : C₀(X, ℂ) →L[ℂ] ℂ)

/-- Let `Φ` be a bounded linear functional on `C₀(X, ℂ)`. There exists a positive linear functional
`Λ` on `C₀(X, ℝ)` such that `‖Φ f‖ ≤ Λ |f| ≤ ‖Φ‖ ‖f‖` for all `f : C₀(X, ℂ)` (part of the proof
of [Rudin RCA 6.19]).

Here `Λ` is integration against the total variation of `rieszMeasure Φ` (for the Borel
`σ`-algebra). -/
theorem exists_dominating_positive_functional :
    ∃ Λ : C₀(X, ℝ) →L[ℝ] ℝ, (∀ u : C₀(X, ℝ), (∀ x, 0 ≤ u x) → 0 ≤ Λ u) ∧
      ∀ f : C₀(X, ℂ), ‖Φ f‖ ≤ Λ f.normComp ∧ Λ f.normComp ≤ ‖Φ‖ * ‖f‖ := by
  let : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  refine ⟨variationFunctional Φ, fun u hu ↦ integral_nonneg fun x ↦
    mul_nonneg (norm_nonneg _) (hu x), fun f ↦ ⟨?_, ?_⟩⟩
  · rw [apply_eq_integral, variationFunctional_apply]
    refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall fun x ↦ ?_))
    simp
  · rw [variationFunctional_apply]
    calc ∫ x, ‖density Φ x‖ * f.normComp x ∂baseMeasure Φ
        ≤ ∫ x, ‖density Φ x‖ * ‖f‖ ∂baseMeasure Φ :=
          integral_mono_of_nonneg (.of_forall fun x ↦ mul_nonneg (norm_nonneg _) (by simp))
            ((integrable_density Φ).norm.mul_const _)
            (.of_forall fun x ↦ mul_le_mul_of_nonneg_left (by simpa using f.norm_coe_le_norm x)
              (norm_nonneg _))
      _ = (∫ x, ‖density Φ x‖ ∂baseMeasure Φ) * ‖f‖ := integral_mul_const _ _
      _ ≤ ‖Φ‖ * ‖f‖ := mul_le_mul_of_nonneg_right (integral_norm_density_le Φ) (norm_nonneg f)

end ComplexRMK
