/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
-- import Mathlib.MeasureTheory.VectorMeasure.Basic
import Mathlib
import SpectralThm.ComplexMeasure.SimpleFunc

-- /-!
-- # Bochner integral

-- The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
-- measure space into a Banach space (complete normed vector space). It is constructed here
-- for L1 functions by extending the integral on simple functions. See the file
-- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` for the integral of functions
-- and corresponding API.

-- ## Main definitions

-- The Bochner integral is defined through the extension process described in the file
-- `Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

-- 1. Define the integral of the indicator of a set. This is `weightedSMul μ s x = μ.real s * x`.
--   `weightedSMul μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
--   (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

-- 2. Define the integral on simple functions of the type `SimpleFunc α E` (notation : `α →ₛ E`)
--   where `E` is a real normed space. (See `SimpleFunc.integral` for details.)

-- 3. Transfer this definition to define the integral on `L1.simpleFunc α E` (notation :
--   `α →₁ₛ[μ] E`), see `L1.simpleFunc.integral`. Show that this integral is a continuous linear
--   map from `α →₁ₛ[μ] E` to `E`.

-- 4. Define the Bochner integral on L1 functions by extending the integral on integrable simple
--   functions `α →₁ₛ[μ] E` using `ContinuousLinearMap.extend` and the fact that the embedding of
--   `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

-- ## Notations

-- * `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
-- * `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
--                 `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
-- * `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
--                  functions (defined in `Mathlib/MeasureTheory/Function/SimpleFuncDense`)

-- We also define notations for integral on a set, which are described in the file
-- `Mathlib/MeasureTheory/Integral/SetIntegral.lean`.

-- Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

-- ## Tags

-- Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-- -/


noncomputable section

open Filter ENNReal Set MeasureTheory VectorMeasure ContinuousLinearMap
open scoped NNReal ENNReal MeasureTheory

variable {α M R S : Type*}

namespace MeasureTheory

section weightedVectorSMul

variable [MeasurableSpace α] [AddCommMonoid M] [TopologicalSpace M] [Semiring R]
  [TopologicalSpace R] [m : Module R M] [ContinuousSMul R M]
  (μ : VectorMeasure α M)

/-- Given a set `s`, return the continuous linear map `fun x => (μ s) x`. The extension
of that set function through `setToL1` gives the Bochner integral of L1 functions. -/
def weightedVectorSMul (s : Set α) : R →L[R] M where
  toFun c := c • (μ s)
  map_add' _ _ := m.add_smul _ _ (μ s)
  map_smul' _ _ := smul_assoc _ _ (μ s)

@[simp]
theorem weightedVectorSMul_apply (s : Set α) (c : R) : weightedVectorSMul μ s c = c • (μ s) := rfl

@[simp]
theorem weightedVectorSMul_zero_measure :
    weightedVectorSMul (0 : VectorMeasure α M) = (0 : Set α → R →L[R] M) := by ext; simp

@[simp]
theorem weightedVectorSMul_empty :
    weightedVectorSMul μ ∅ = (0 : R →L[R] M) := by ext; simp

theorem weightedVectorSMul_smul_vectorMeasure (a b : R) {s : Set α} :
    (weightedVectorSMul (a • μ) s) b = b • (weightedVectorSMul μ s a) := by simp

theorem weightedVectorSMul_congr (s t : Set α) (hst : μ s = μ t) :
    (weightedVectorSMul μ s : R →L[R] M) = weightedVectorSMul μ t := by
  ext
  simp only [weightedVectorSMul_apply, one_smul]
  exact hst

theorem weightedVectorSMul_null {s : Set α} (h_zero : μ s = 0) :
    (weightedVectorSMul μ s : R →L[R] M) = 0 := by
  ext
  simp only [weightedVectorSMul_apply, one_smul, ContinuousLinearMap.zero_apply]
  exact h_zero

theorem weightedVectorSMul_nonneg [PartialOrder M] [PartialOrder R] [OrderedSMul R M]
    {s : Set α} {c : R} (hs : 0 ≤ μ s) (hc : 0 ≤ c) : 0 ≤ weightedVectorSMul μ s c := by
  simp only [weightedVectorSMul_apply]
  exact smul_nonneg hc hs

theorem weightedVectorSMul_smul (c : R) (s : Set α) (x : R) :
    weightedVectorSMul μ s (c • x) = c • weightedVectorSMul μ s x := by
  simp only [weightedVectorSMul_apply]
  exact smul_assoc c x (μ s)

theorem weightedVectorSMul_smul' {𝕜 : Type*} [SMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M]
    (c : 𝕜) (s : Set α) (x : R) :
    weightedVectorSMul μ s (c • x) = c • weightedVectorSMul μ s x := by
  simp only [weightedVectorSMul_apply]
  exact smul_assoc c x (μ s)

variable [ContinuousAdd M]

theorem weightedVectorSMul_add_vectorMeasure (ν : VectorMeasure α M) {s : Set α} :
    (weightedVectorSMul (μ + ν) s : R →L[R] M) = weightedVectorSMul μ s + weightedVectorSMul ν s := by ext; simp

variable [T2Space M]

theorem weightedVectorSMul_union (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hdisj : Disjoint s t) :
    (weightedVectorSMul μ (s ∪ t) : R →L[R] M) = weightedVectorSMul μ s + weightedVectorSMul μ t := by
  ext
  simp only [weightedVectorSMul_apply, one_smul, ContinuousLinearMap.add_apply]
  exact of_union hdisj hs ht

end weightedVectorSMul

section NormedWeightedVectorSMul

variable [MeasurableSpace α] [SeminormedAddCommGroup M] [NontriviallyNormedField R]
  [NormedSpace R M] (μ : VectorMeasure α M)

-- theorem dominatedFinMeasAdditive_weightedSMul {_ : MeasurableSpace α} :
--     DominatedFinMeasAdditive μ (weightedSMul μ : Set α → R →L[R] M) 1 :=
--   ⟨weightedSMul_union, fun s _ _ => (norm_weightedSMul_le s).trans (one_mul _).symm.le⟩

theorem norm_weightedVectorSMul_le (s : Set α) :
    ‖(weightedVectorSMul μ s : R →L[R] M)‖ ≤ ‖μ s‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg (μ s))]
  intro c
  simp only [weightedVectorSMul_apply, mul_comm]
  exact norm_smul_le _ _

end NormedWeightedVectorSMul


local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Integral

-- /-!
-- ### The Bochner integral of simple functions

-- Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
-- and prove basic property of this integral.
-- -/

open Finset
variable [m : MeasurableSpace α] [NormedAddCommGroup M] [NontriviallyNormedField R]
  [NormedSpace R M] (μ : VectorMeasure α M)

/-- Vector integral of simple functions whose codomain is an `R`-valued `NormedSpace`.
This is equal to `∑ x ∈ f.range, x • μ (f ⁻¹' {x})` (see `integral_eq`). -/
def vectorIntegral (f : α →ₛ R) : M := f.setToVectorSimpleFunc (weightedVectorSMul μ)

@[simp]
theorem vectorIntegral_def (f : α →ₛ R) :
    f.vectorIntegral μ = f.setToVectorSimpleFunc (weightedVectorSMul μ) := rfl

theorem vectorIntegral_eq (f : α →ₛ R) : f.vectorIntegral μ = ∑ x ∈ f.range, x • μ (f ⁻¹' {x}) := by
  simp only [vectorIntegral_def]
  rfl

theorem vectorIntegral_eq_sum_filter [DecidablePred fun x : R => x ≠ 0] (f : α →ₛ R) :
    f.vectorIntegral μ = ∑ x ∈ {x ∈ f.range | x ≠ 0}, x • μ (f ⁻¹' {x}) := by
  simp [vectorIntegral_def, ne_eq, setToVectorSimpleFunc_eq_sum_filter, weightedVectorSMul_apply]

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
theorem vectorIntegral_eq_sum_of_subset [DecidablePred fun x : R => x ≠ 0] {f : α →ₛ R}
    {s : Finset R} (hs : {x ∈ f.range | x ≠ 0} ⊆ s) :
    f.vectorIntegral μ = ∑ x ∈ s, x • μ (f ⁻¹' {x}) := by
  rw [SimpleFunc.vectorIntegral_eq_sum_filter, Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx]

@[simp]
theorem vectorIntegral_const (y : R) :
    (const α y).vectorIntegral μ = y • μ univ := by
  classical
  calc
    (const α y).vectorIntegral μ = ∑ z ∈ {y}, z • μ (const α y ⁻¹' {z}) := by
      apply vectorIntegral_eq_sum_of_subset
      exact subset_trans (filter_subset _ _) (range_const_subset _ _)
    _ = y • μ univ := by simp [Set.preimage]

@[simp]
theorem vectorIntegral_piecewise_zero (f : α →ₛ R) {s : Set α} (hs : MeasurableSet s) :
    (piecewise s hs f 0).vectorIntegral μ = f.vectorIntegral (μ.restrict s) := by
  classical
  rw [@vectorIntegral_eq_sum_of_subset _ _ _ _ _ _ _ _ _ (piecewise s hs f 0)
    {x ∈ f.range | x ≠ 0} _, vectorIntegral_eq_sum_filter]
  · apply Finset.sum_congr rfl _
    intro x hx
    simp only [ne_eq, mem_filter, mem_range, Set.mem_range] at hx
    congr 1
    simp only [coe_piecewise, coe_zero, piecewise_eq_indicator]
    rw [VectorMeasure.restrict_apply μ hs (measurableSet_fiber f x)]
    congr
    ext z
    simp only [Set.mem_preimage, mem_singleton_iff, mem_inter_iff]
    refine ⟨?_, ?_⟩
    · intro h
      have hz : z ∈ s ∩ (Function.support f) := by
        apply Set.indicator_apply_ne_zero.mp
        rw [h]
        exact hx.2
      rw [Set.indicator_of_mem (Set.mem_of_mem_inter_left hz)] at h
      exact ⟨h, Set.mem_of_mem_inter_left hz⟩
    · intro h
      rw [Set.indicator_of_mem h.2]
      exact h.1
  · intro x hx
    simp only [mem_filter, mem_range, coe_piecewise, coe_zero, piecewise_eq_indicator,
      Set.mem_range] at hx
    obtain ⟨y, hy⟩ := hx.1
    simp only [ne_eq, mem_filter, mem_range, Set.mem_range]
    refine ⟨?_, hx.2⟩
    use y
    rw [Set.indicator_of_mem] at hy
    · exact hy
    have h : y ∈ s ∩ (Function.support f) := by
      apply Set.indicator_apply_ne_zero.mp
      rw [hy]
      exact hx.2
    exact Set.mem_of_mem_inter_left h

/-- Calculate the integral of `g ∘ f : α →ₛ S`, where `f` is an integrable function from `α` to `E`
    and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
theorem map_vectorIntegral [NormedAddCommGroup S] (f : α →ₛ S) (g : S → R) (hg : g 0 = 0) :
    (f.map g).vectorIntegral μ = ∑ x ∈ f.range, g x • (μ (f ⁻¹' {x})) :=
  map_setToVectorSimpleFunc _ (weightedVectorSMul_union μ) hg

-- /-- `SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has type
--     `α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coercion.
--     See `integral_eq_lintegral` for a simpler version. -/
-- theorem integral_eq_lintegral' {f : α →ₛ E} {g : E → ℝ≥0∞} (hf : Integrable f μ) (hg0 : g 0 = 0)
--     (ht : ∀ b, g b ≠ ∞) :
--     (f.map (ENNReal.toReal ∘ g)).integral μ = ENNReal.toReal (∫⁻ a, g (f a) ∂μ) := by
--   have hf' : f.FinMeasSupp μ := integrable_iff_finMeasSupp.1 hf
--   simp only [← map_apply g f, lintegral_eq_lintegral]
--   rw [map_integral f _ hf, map_lintegral, ENNReal.toReal_sum]
--   · refine Finset.sum_congr rfl fun b _ => ?_
--     rw [smul_eq_mul, toReal_mul, mul_comm, Function.comp_apply, measureReal_def]
--   · rintro a -
--     by_cases a0 : a = 0
--     · rw [a0, hg0, zero_mul]; exact WithTop.zero_ne_top
--     · apply mul_ne_top (ht a) (hf'.meas_preimage_singleton_ne_zero a0).ne
--   · simp [hg0]

-- variable [NormedSpace ℝ E]


theorem vectorIntegral_congr {f g : α →ₛ R} (h : f =ᵐ[μ.variation.ennrealToMeasure] g) :
    f.vectorIntegral μ = g.vectorIntegral μ := setToVectorSimpleFunc_congr (weightedVectorSMul μ)
      (fun s _ hsμ => (weightedVectorSMul_null μ (measure_eq_zero_of_variation_eq_zero μ s hsμ)))
      (weightedVectorSMul_union μ) h

-- /-- `SimpleFunc.bintegral` and `SimpleFunc.integral` agree when the integrand has type
--     `α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coercion. -/
-- theorem integral_eq_lintegral {f : α →ₛ ℝ} (hf : Integrable f μ) (h_pos : 0 ≤ᵐ[μ] f) :
--     f.integral μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) := by
--   have : f =ᵐ[μ] f.map (ENNReal.toReal ∘ ENNReal.ofReal) :=
--     h_pos.mono fun a h => (ENNReal.toReal_ofReal h).symm
--   rw [← integral_eq_lintegral' hf]
--   exacts [integral_congr hf this, ENNReal.ofReal_zero, fun b => ENNReal.ofReal_ne_top]

theorem vectorIntegral_add {f g : α →ₛ R} :
    vectorIntegral μ (f + g) = vectorIntegral μ f + vectorIntegral μ g :=
  setToVectorSimpleFunc_add _ (weightedVectorSMul_union μ)

theorem vectorIntegral_neg {f : α →ₛ R} : vectorIntegral μ (-f) = -vectorIntegral μ f :=
  setToVectorSimpleFunc_neg _ (weightedVectorSMul_union μ)

theorem vectorIntegral_sub {f g : α →ₛ R} :
    vectorIntegral μ (f - g) = vectorIntegral μ f - vectorIntegral μ g :=
  setToVectorSimpleFunc_sub _ (weightedVectorSMul_union μ)

theorem vectorIntegral_smul (c : R) {f : α →ₛ R} :
    vectorIntegral μ (c • f) = c • vectorIntegral μ f :=
  setToVectorSimpleFunc_smul _ (weightedVectorSMul_union μ) c

theorem vectorIntegral_smul' {𝕜 : Type*} [SMulZeroClass 𝕜 R] [DistribSMul 𝕜 M] [IsScalarTower 𝕜 R M]
    (c : 𝕜) {f : α →ₛ R} : vectorIntegral μ (c • f) = c • vectorIntegral μ f := by
  apply setToVectorSimpleFunc_smul' _ (weightedVectorSMul_union μ) (weightedVectorSMul_smul' μ) c

-- theorem norm_setToVectorSimpleFunc_le_integral_norm (T : Set α → E →L[ℝ] F) {C : ℝ}
--     (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s) {f : α →ₛ E}
--     (hf : Integrable f μ) : ‖f.setToSimpleFunc T‖ ≤ C * (f.map norm).integral μ :=
--   calc
--     ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
--       norm_setToVectorSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm f hf
--     _ = C * (f.map norm).integral μ := by
--       rw [map_integral f norm hf norm_zero]; simp_rw [smul_eq_mul]

-- theorem norm_integral_le_integral_norm (f : α →ₛ E) (hf : Integrable f μ) :
--     ‖f.integral μ‖ ≤ (f.map norm).integral μ := by
--   refine (norm_setToVectorSimpleFunc_le_integral_norm _ (fun s _ _ => ?_) hf).trans (one_mul _).le
--   exact (norm_weightedVectorSMul_le s).trans (one_mul _).symm.le

-- theorem integral_add_measure {ν} (f : α →ₛ E) (hf : Integrable f (μ + ν)) :
--     f.integral (μ + ν) = f.integral μ + f.integral ν := by
--   simp_rw [integral_def]
--   refine setToVectorSimpleFunc_add_left'
--     (weightedSMul μ) (weightedSMul ν) (weightedSMul (μ + ν)) (fun s _ hμνs => ?_) hf
--   rw [lt_top_iff_ne_top, Measure.coe_add, Pi.add_apply, ENNReal.add_ne_top] at hμνs
--   rw [weightedVectorSMul_add_measure _ _ hμνs.1 hμνs.2]

-- section Order

-- variable [PartialOrder F] [IsOrderedAddMonoid F] [OrderedSMul ℝ F]

-- lemma integral_nonneg {f : α →ₛ F} (hf : 0 ≤ᵐ[μ] f) :
--     0 ≤ f.integral μ := by
--   rw [integral_eq]
--   apply Finset.sum_nonneg
--   rw [forall_mem_range]
--   intro y
--   by_cases hy : 0 ≤ f y
--   · positivity
--   · suffices μ (f ⁻¹' {f y}) = 0 by simp [this, measureReal_def]
--     rw [← nonpos_iff_eq_zero]
--     refine le_of_le_of_eq (measure_mono fun x hx ↦ ?_) (ae_iff.mp hf)
--     simp only [Set.mem_preimage, mem_singleton_iff, mem_setOf_eq] at hx ⊢
--     exact hx ▸ hy

-- lemma integral_mono {f g : α →ₛ F} (h : f ≤ᵐ[μ] g) (hf : Integrable f μ) (hg : Integrable g μ) :
--     f.integral μ ≤ g.integral μ := by
--   rw [← sub_nonneg, ← integral_sub hg hf]
--   rw [← sub_nonneg_ae] at h
--   exact integral_nonneg h

-- lemma integral_mono_measure {ν} {f : α →ₛ F} (hf : 0 ≤ᵐ[ν] f) (hμν : μ ≤ ν) (hfν : Integrable f ν) :
--     f.integral μ ≤ f.integral ν := by
--   simp only [integral_eq]
--   apply Finset.sum_le_sum
--   simp only [forall_mem_range]
--   intro x
--   by_cases hx : 0 ≤ f x
--   · obtain (hx | hx) := hx.eq_or_lt
--     · simp [← hx]
--     simp only [measureReal_def]
--     gcongr
--     · exact integrable_iff.mp hfν (f x) hx.ne' |>.ne
--     · exact hμν _
--   · suffices ν (f ⁻¹' {f x}) = 0 by
--       have A : μ (f ⁻¹' {f x}) = 0 := by simpa using (hμν _ |>.trans_eq this)
--       simp [measureReal_def, A, this]
--     rw [← nonpos_iff_eq_zero, ← ae_iff.mp hf]
--     refine measure_mono fun y hy ↦ ?_
--     simp_all

-- end Order

-- end Integral

-- end SimpleFunc

-- namespace L1

-- open AEEqFun Lp.simpleFunc Lp

-- variable [NormedAddCommGroup E] {m : MeasurableSpace α} {μ : Measure α}

-- namespace SimpleFunc

-- theorem norm_eq_integral (f : α →₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).integral μ := by
--   rw [norm_eq_sum_mul f, (toSimpleFunc f).map_integral norm (SimpleFunc.integrable f) norm_zero]
--   simp_rw [smul_eq_mul]

-- section PosPart

-- /-- Positive part of a simple function in L1 space. -/
-- nonrec def posPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
--   ⟨Lp.posPart (f : α →₁[μ] ℝ), by
--     rcases f with ⟨f, s, hsf⟩
--     use s.posPart
--     simp only [SimpleFunc.posPart, SimpleFunc.coe_map, Function.comp_def, coe_posPart, ← hsf,
--       posPart_mk] ⟩

-- /-- Negative part of a simple function in L1 space. -/
-- def negPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
--   posPart (-f)

-- @[norm_cast]
-- theorem coe_posPart (f : α →₁ₛ[μ] ℝ) : (posPart f : α →₁[μ] ℝ) = Lp.posPart (f : α →₁[μ] ℝ) := rfl

-- @[norm_cast]
-- theorem coe_negPart (f : α →₁ₛ[μ] ℝ) : (negPart f : α →₁[μ] ℝ) = Lp.negPart (f : α →₁[μ] ℝ) := rfl

-- end PosPart

-- section SimpleFuncIntegral

-- /-!
-- ### The Bochner integral of `L1`

-- Define the Bochner integral on `α →₁ₛ[μ] E` by extension from the simple functions `α →₁ₛ[μ] E`,
-- and prove basic properties of this integral. -/

-- variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]

-- attribute [local instance] simpleFunc.isBoundedSMul simpleFunc.module simpleFunc.normedSpace

-- /-- The Bochner integral over simple functions in L1 space. -/
-- def integral (f : α →₁ₛ[μ] E) : E :=
--   (toSimpleFunc f).integral μ

-- theorem integral_eq_integral (f : α →₁ₛ[μ] E) : integral f = (toSimpleFunc f).integral μ := rfl

-- nonrec theorem integral_eq_lintegral {f : α →₁ₛ[μ] ℝ} (h_pos : 0 ≤ᵐ[μ] toSimpleFunc f) :
--     integral f = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ((toSimpleFunc f) a) ∂μ) := by
--   rw [integral, SimpleFunc.integral_eq_lintegral (SimpleFunc.integrable f) h_pos]

-- theorem integral_eq_setToL1S (f : α →₁ₛ[μ] E) : integral f = setToL1S (weightedSMul μ) f := rfl

-- nonrec theorem integral_congr {f g : α →₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
--     integral f = integral g :=
--   SimpleFunc.integral_congr (SimpleFunc.integrable f) h

-- theorem integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
--   setToL1S_add _ (fun _ _ => weightedSMul_null) weightedSMul_union _ _

-- theorem integral_smul (c : 𝕜) (f : α →₁ₛ[μ] E) : integral (c • f) = c • integral f :=
--   setToL1S_smul _ (fun _ _ => weightedSMul_null) weightedSMul_union weightedSMul_smul c f

-- theorem norm_integral_le_norm (f : α →₁ₛ[μ] E) : ‖integral f‖ ≤ ‖f‖ := by
--   rw [integral, norm_eq_integral]
--   exact (toSimpleFunc f).norm_integral_le_integral_norm (SimpleFunc.integrable f)

-- variable (α E μ 𝕜)

-- /-- The Bochner integral over simple functions in L1 space as a continuous linear map. -/
-- def integralCLM' : (α →₁ₛ[μ] E) →L[𝕜] E :=
--   LinearMap.mkContinuous ⟨⟨integral, integral_add⟩, integral_smul⟩ 1 fun f =>
--     le_trans (norm_integral_le_norm _) <| by rw [one_mul]

-- /-- The Bochner integral over simple functions in L1 space as a continuous linear map over ℝ. -/
-- def integralCLM : (α →₁ₛ[μ] E) →L[ℝ] E :=
--   integralCLM' α E ℝ μ

-- variable {α E μ 𝕜}

-- local notation "Integral" => integralCLM α E μ

-- open ContinuousLinearMap

-- theorem norm_Integral_le_one : ‖Integral‖ ≤ 1 :=
--   LinearMap.mkContinuous_norm_le _ zero_le_one fun f ↦ by
--     simpa [one_mul] using norm_integral_le_norm f

-- section PosPart

-- theorem posPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
--     toSimpleFunc (posPart f) =ᵐ[μ] (toSimpleFunc f).posPart := by
--   have eq : ∀ a, (toSimpleFunc f).posPart a = max ((toSimpleFunc f) a) 0 := fun a => rfl
--   have ae_eq : ∀ᵐ a ∂μ, toSimpleFunc (posPart f) a = max ((toSimpleFunc f) a) 0 := by
--     filter_upwards [toSimpleFunc_eq_toFun (posPart f), Lp.coeFn_posPart (f : α →₁[μ] ℝ),
--       toSimpleFunc_eq_toFun f] with _ _ h₂ h₃
--     convert h₂ using 1
--     rw [h₃]
--   refine ae_eq.mono fun a h => ?_
--   rw [h, eq]

-- theorem negPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
--     toSimpleFunc (negPart f) =ᵐ[μ] (toSimpleFunc f).negPart := by
--   rw [SimpleFunc.negPart, MeasureTheory.SimpleFunc.negPart]
--   filter_upwards [posPart_toSimpleFunc (-f), neg_toSimpleFunc f]
--   intro a h₁ h₂
--   rw [h₁]
--   change max _ _ = max _ _
--   rw [h₂]
--   simp

-- theorem integral_eq_norm_posPart_sub (f : α →₁ₛ[μ] ℝ) : integral f = ‖posPart f‖ - ‖negPart f‖ := by
--   -- Convert things in `L¹` to their `SimpleFunc` counterpart
--   have ae_eq₁ : (toSimpleFunc f).posPart =ᵐ[μ] (toSimpleFunc (posPart f)).map norm := by
--     filter_upwards [posPart_toSimpleFunc f] with _ h
--     rw [SimpleFunc.map_apply, h]
--     conv_lhs => rw [← SimpleFunc.posPart_map_norm, SimpleFunc.map_apply]
--   -- Convert things in `L¹` to their `SimpleFunc` counterpart
--   have ae_eq₂ : (toSimpleFunc f).negPart =ᵐ[μ] (toSimpleFunc (negPart f)).map norm := by
--     filter_upwards [negPart_toSimpleFunc f] with _ h
--     rw [SimpleFunc.map_apply, h]
--     conv_lhs => rw [← SimpleFunc.negPart_map_norm, SimpleFunc.map_apply]
--   rw [integral, norm_eq_integral, norm_eq_integral, ← SimpleFunc.integral_sub]
--   · change (toSimpleFunc f).integral μ =
--       ((toSimpleFunc (posPart f)).map norm - (toSimpleFunc (negPart f)).map norm).integral μ
--     apply MeasureTheory.SimpleFunc.integral_congr (SimpleFunc.integrable f)
--     filter_upwards [ae_eq₁, ae_eq₂] with _ h₁ h₂
--     rw [SimpleFunc.sub_apply, ← h₁, ← h₂]
--     exact DFunLike.congr_fun (toSimpleFunc f).posPart_sub_negPart.symm _
--   · exact (SimpleFunc.integrable f).pos_part.congr ae_eq₁
--   · exact (SimpleFunc.integrable f).neg_part.congr ae_eq₂

-- end PosPart

-- end SimpleFuncIntegral

-- end SimpleFunc

-- open SimpleFunc

-- local notation "Integral" => @integralCLM α E _ _ _ _ _ μ _

-- variable [NormedSpace ℝ E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
--   [CompleteSpace E]

-- section IntegrationInL1

-- attribute [local instance] simpleFunc.isBoundedSMul simpleFunc.module

-- open ContinuousLinearMap

-- variable (𝕜) in
-- /-- The Bochner integral in L1 space as a continuous linear map. -/
-- nonrec def integralCLM' : (α →₁[μ] E) →L[𝕜] E :=
--   (integralCLM' α E 𝕜 μ).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
--     simpleFunc.isUniformInducing

-- /-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
-- def integralCLM : (α →₁[μ] E) →L[ℝ] E :=
--   integralCLM' ℝ

-- /-- The Bochner integral in L1 space -/
-- irreducible_def integral : (α →₁[μ] E) → E :=
--   integralCLM

-- theorem integral_eq (f : α →₁[μ] E) : integral f = integralCLM f := by
--   simp only [integral]

-- theorem integral_eq_setToL1 (f : α →₁[μ] E) :
--     integral f = setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f := by
--   simp only [integral]; rfl

-- @[norm_cast]
-- theorem SimpleFunc.integral_L1_eq_integral (f : α →₁ₛ[μ] E) :
--     L1.integral (f : α →₁[μ] E) = SimpleFunc.integral f := by
--   simp only [integral, L1.integral]
--   exact setToL1_eq_setToL1SCLM (dominatedFinMeasAdditive_weightedSMul μ) f

-- variable (α E)

-- @[simp]
-- theorem integral_zero : integral (0 : α →₁[μ] E) = 0 := by
--   simp only [integral]
--   exact map_zero integralCLM

-- variable {α E}

-- @[integral_simps]
-- theorem integral_add (f g : α →₁[μ] E) : integral (f + g) = integral f + integral g := by
--   simp only [integral]
--   exact map_add integralCLM f g

-- @[integral_simps]
-- theorem integral_neg (f : α →₁[μ] E) : integral (-f) = -integral f := by
--   simp only [integral]
--   exact map_neg integralCLM f

-- @[integral_simps]
-- theorem integral_sub (f g : α →₁[μ] E) : integral (f - g) = integral f - integral g := by
--   simp only [integral]
--   exact map_sub integralCLM f g

-- @[integral_simps]
-- theorem integral_smul (c : 𝕜) (f : α →₁[μ] E) : integral (c • f) = c • integral f := by
--   simp only [integral]
--   change (integralCLM' 𝕜) (c • f) = c • (integralCLM' 𝕜) f
--   exact map_smul (integralCLM' 𝕜) c f

-- theorem norm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖ ≤ 1 :=
--   norm_setToL1_le (dominatedFinMeasAdditive_weightedSMul μ) zero_le_one

-- theorem nnnorm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ 1 :=
--   norm_Integral_le_one

-- theorem norm_integral_le (f : α →₁[μ] E) : ‖integral f‖ ≤ ‖f‖ :=
--   calc
--     ‖integral f‖ = ‖integralCLM f‖ := by simp only [integral]
--     _ ≤ ‖integralCLM (α := α) (μ := μ)‖ * ‖f‖ := le_opNorm _ _
--     _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right norm_Integral_le_one <| norm_nonneg _
--     _ = ‖f‖ := one_mul _

-- theorem nnnorm_integral_le (f : α →₁[μ] E) : ‖integral f‖₊ ≤ ‖f‖₊ :=
--   norm_integral_le f

-- @[continuity]
-- theorem continuous_integral : Continuous fun f : α →₁[μ] E => integral f := by
--   simp only [integral]
--   exact L1.integralCLM.continuous

-- section PosPart

-- theorem integral_eq_norm_posPart_sub (f : α →₁[μ] ℝ) :
--     integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖ := by
--   -- Use `isClosed_property` and `isClosed_eq`
--   refine @isClosed_property _ _ _ ((↑) : (α →₁ₛ[μ] ℝ) → α →₁[μ] ℝ)
--       (fun f : α →₁[μ] ℝ => integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖)
--       (simpleFunc.denseRange one_ne_top) (isClosed_eq ?_ ?_) ?_ f
--   · simp only [integral]
--     exact cont _
--   · refine Continuous.sub (continuous_norm.comp Lp.continuous_posPart)
--       (continuous_norm.comp Lp.continuous_negPart)
--   -- Show that the property holds for all simple functions in the `L¹` space.
--   · intro s
--     norm_cast
--     exact SimpleFunc.integral_eq_norm_posPart_sub _

-- end PosPart

-- end IntegrationInL1

-- end L1

-- end MeasureTheory
