/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib
public import SpectralThm.Linfty
public import SpectralThm.Linfty.Algebra

/-!
# Projection-valued measures

A projection-valued measure (also called a *spectral measure*, or a *resolution of the identity*
in Rudin, *Functional Analysis*, 12.17) on a measurable space `X` with values in a complex Hilbert
space `H` assigns to every measurable set `w` an orthogonal projection `E w`, such that
`E (w₁ ∩ w₂) = E w₁ * E w₂`, `E univ = 1`, and `E` is countably additive in the weak operator
topology. It is a `VectorMeasure X (H →WOT[ℂ] H)` with these extra properties; it is not countably
additive in operator norm and has infinite variation in general.

## Main definitions

* `ProjectionValuedMeasure X H`: projection-valued measures on `X` acting on `H`. It coerces to
  `Set X → H →L[ℂ] H`.
* `ProjectionValuedMeasure.toComplexMeasure E x y`: the complex measure `E_{x,y} w = ⟪x, E w y⟫`.
* `ProjectionValuedMeasure.toMeasure E x`: the finite measure `E_{x,x} w = ‖E w x‖ ^ 2`.
* `ProjectionValuedMeasure.applyVectorMeasure E x`: the `H`-valued measure `w ↦ E w x`.
* `ProjectionValuedMeasure.measure E`: a scalar measure with the same null sets as `E`.
* `ProjectionValuedMeasure.Linfty E`: the algebra `L^∞(E)` (Rudin 12.20).

## Main results

* `ProjectionValuedMeasure.hasSum_apply_iUnion`: `E` is countably additive in the strong operator
  topology, `E (⋃ i, w i) x = ∑ i, E (w i) x` in norm. The definition only asks for the weak
  operator topology; the strong version follows since `‖E w x‖ ^ 2 = E_{x,x} w`.

## Implementation notes

`E` is a vector measure in the weak operator topology rather than in `H →Lₚₜ[ℂ] H` (pointwise
convergence): this is the weaker requirement, it is what the construction of the spectral measure
gives directly, and the strong version is a theorem (`hasSum_apply_iUnion`,
`applyVectorMeasure`). The `H`-valued measure `w ↦ E w x` has finite `∑ ‖E wᵢ x‖ ^ 2` but its
variation `sup ∑ ‖E wᵢ x‖` can be infinite, so Mathlib's `VectorMeasure.integral` (which
integrates against the variation) does not compute `(∫ f dE) x` from it in general.
-/

@[expose] public section

open scoped Function InnerProductSpace
open MeasureTheory BigOperators ENNReal ContinuousLinearMapWOT Filter Topology

section Def

variable (X : Type*) [MeasurableSpace X]
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A projection-valued measure on `X` acting on `H`: a vector measure with values in `H →WOT[ℂ] H`
(so countably additive in the weak operator topology) whose values are orthogonal projections,
multiplicative on intersections and with `E univ = 1`. Rudin calls it a resolution of the
identity. -/
structure ProjectionValuedMeasure extends VectorMeasure X (H →WOT[ℂ] H) where
  /-- Each value is an orthogonal projection. -/
  isStarProjection' (w : Set X) : IsStarProjection (measureOf' w).toCLM
  /-- The projection of an intersection is the product of the projections. -/
  measureOf_inter' ⦃w₁ w₂ : Set X⦄ : MeasurableSet w₁ → MeasurableSet w₂ →
    measureOf' (w₁ ∩ w₂) = measureOf' w₁ * measureOf' w₂
  /-- The whole space has measure the identity. -/
  measureOf_univ' : measureOf' Set.univ = 1

instance ProjectionValuedMeasure.instFunLike :
    FunLike (ProjectionValuedMeasure X H) (Set X) (H →L[ℂ] H) where
  coe E w := (E.measureOf' w).toCLM
  coe_injective E F h := by
    obtain ⟨⟨_⟩, _⟩ := E
    obtain ⟨⟨_⟩, _⟩ := F
    congr
    funext w
    exact toCLM_injective (congrFun h w)

end Def

/-- For a star projection `p`, `⟪x, p x⟫ = ‖p x‖ ^ 2`. -/
lemma IsStarProjection.inner_apply_self {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] {p : H →L[𝕜] H} (hp : IsStarProjection p) (x : H) :
    ⟪x, p x⟫_𝕜 = (‖p x‖ : 𝕜) ^ 2 := by
  rw [← inner_self_eq_norm_sq_to_K, ← ContinuousLinearMap.adjoint_inner_right,
    hp.isSelfAdjoint.adjoint_eq, ← mul_apply_eq_comp, hp.isIdempotentElem.eq]

namespace ProjectionValuedMeasure

variable {X : Type*} {mX : MeasurableSpace X}
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : ProjectionValuedMeasure X H)

lemma isStarProjection (w : Set X) : IsStarProjection (E w) :=
  E.isStarProjection' w

@[simp]
lemma apply_empty : E (∅ : Set X) = 0 := by
  change (E.toVectorMeasure ∅).toCLM = 0
  simp

@[simp]
lemma apply_univ : E (Set.univ : Set X) = 1 := by
  change (E.measureOf' _).toCLM = 1
  rw [E.measureOf_univ']
  rfl

lemma apply_of_not_measurableSet {w : Set X} (hw : ¬MeasurableSet w) : E w = 0 := by
  change (E.toVectorMeasure w).toCLM = 0
  simp [E.toVectorMeasure.not_measurable hw]

lemma apply_union {w₁ w₂ : Set X} (h₁ : MeasurableSet w₁) (h₂ : MeasurableSet w₂)
    (h : Disjoint w₁ w₂) : E (w₁ ∪ w₂) = E w₁ + E w₂ := by
  change (E.toVectorMeasure _).toCLM = (E.toVectorMeasure _).toCLM + (E.toVectorMeasure _).toCLM
  rw [E.toVectorMeasure.of_union h h₁ h₂]
  rfl

lemma apply_inter {w₁ w₂ : Set X} (h₁ : MeasurableSet w₁) (h₂ : MeasurableSet w₂) :
    E (w₁ ∩ w₂) = E w₁ * E w₂ := by
  change (E.measureOf' _).toCLM = _
  rw [E.measureOf_inter' h₁ h₂]
  rfl

lemma apply_mono {w₁ w₂ : Set X} (h₁ : MeasurableSet w₁) (h₂ : MeasurableSet w₂) (h : w₁ ⊆ w₂) :
    E w₁ ≤ E w₂ := by
  rw [← Set.union_sdiff_cancel h, E.apply_union h₁ (h₂.diff h₁) Set.disjoint_sdiff_right]
  simpa using (E.isStarProjection (w₂ \ w₁)).nonneg

/-- The projections `E w` commute with each other (Rudin 12.17). -/
lemma commute (w₁ w₂ : Set X) : Commute (E w₁) (E w₂) := by
  by_cases h₁ : MeasurableSet w₁
  · by_cases h₂ : MeasurableSet w₂
    · rw [Commute, SemiconjBy, ← E.apply_inter h₁ h₂, ← E.apply_inter h₂ h₁, Set.inter_comm]
    · simp [E.apply_of_not_measurableSet h₂]
  · simp [E.apply_of_not_measurableSet h₁]

/-- The projections on disjoint sets have orthogonal ranges (Rudin 12.17). -/
lemma mul_eq_zero_of_disjoint {w₁ w₂ : Set X} (h : Disjoint w₁ w₂) : E w₁ * E w₂ = 0 := by
  by_cases h₁ : MeasurableSet w₁
  · by_cases h₂ : MeasurableSet w₂
    · rw [← E.apply_inter h₁ h₂, Set.disjoint_iff_inter_eq_empty.1 h, apply_empty]
    · simp [E.apply_of_not_measurableSet h₂]
  · simp [E.apply_of_not_measurableSet h₁]

/-- `E` is finitely additive on measurable sets (Rudin 12.17). -/
lemma apply_biUnion_finset {ι : Type*} {s : Finset ι} {w : ι → Set X}
    (hw : ∀ i ∈ s, MeasurableSet (w i)) (hd : (s : Set ι).PairwiseDisjoint w) :
    E (⋃ i ∈ s, w i) = ∑ i ∈ s, E (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hws : ∀ j ∈ s, MeasurableSet (w j) := fun j hj ↦ hw j (Finset.mem_insert_of_mem hj)
    have hdisj : Disjoint (w i) (⋃ j ∈ s, w j) :=
      Set.disjoint_iUnion₂_right.2 fun j hj ↦ hd (by simp) (by simp [hj]) fun h ↦ hi (h ▸ hj)
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi,
      E.apply_union (hw i (Finset.mem_insert_self i s)) (Finset.measurableSet_biUnion s hws) hdisj,
      ih hws (hd.subset (by simp))]

/-- The complex measure `E_{x,y} w = ⟪x, E w y⟫`. -/
noncomputable def toComplexMeasure (x y : H) : ComplexMeasure X :=
  E.toVectorMeasure.mapRange ⟨⟨fun A ↦ ⟪x, A y⟫_ℂ, by simp⟩, fun A B ↦ by simp⟩
    (continuous_dual_apply y (innerSL ℂ x))

@[simp]
lemma toComplexMeasure_apply (x y : H) (w : Set X) : E.toComplexMeasure x y w = ⟪x, E w y⟫_ℂ :=
  rfl

/-- `E` is countably additive in the weak operator topology. -/
lemma hasSum_inner_apply_iUnion (x y : H) {w : ℕ → Set X} (hw : ∀ i, MeasurableSet (w i))
    (hd : Pairwise (Disjoint on w)) :
    HasSum (fun i ↦ ⟪x, E (w i) y⟫_ℂ) ⟪x, E (⋃ i, w i) y⟫_ℂ :=
  (E.toComplexMeasure x y).m_iUnion hw hd

lemma inner_apply_self (w : Set X) (x : H) : ⟪x, E w x⟫_ℂ = (‖E w x‖ : ℂ) ^ 2 :=
  (E.isStarProjection w).inner_apply_self x

/-- The positive measure `E_{x,x} w = ⟪x, E w x⟫ = ‖E w x‖ ^ 2` (Rudin 12.17). -/
noncomputable def toMeasure (x : H) : Measure X := Measure.ofMeasurable
  (fun w _ ↦ ENNReal.ofReal (‖E w x‖ ^ 2))
  (by simp)
  (fun f hf hd ↦ by
    have h := E.hasSum_inner_apply_iUnion x x hf hd
    simp_rw [inner_apply_self, ← Complex.ofReal_pow] at h
    have h' := Complex.hasSum_ofReal.mp h
    rw [← h'.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) h'.summable])

@[simp]
lemma toMeasure_apply (w : Set X) (hw : MeasurableSet w) (x : H) :
    E.toMeasure x w = ENNReal.ofReal (‖E w x‖ ^ 2) :=
  Measure.ofMeasurable_apply w hw

lemma toMeasure_univ (x : H) : E.toMeasure x Set.univ = ‖x‖ₑ ^ 2 := by
  simp [ENNReal.ofReal_pow, ofReal_norm]

instance (x : H) : IsFiniteMeasure (E.toMeasure x) :=
  ⟨by simp⟩

lemma zero_iff (w : Set X) (h : MeasurableSet w) : E w  = 0 ↔ ∀ x, (toMeasure E x) w = 0 := by
  simp [ContinuousLinearMap.ext_iff, toMeasure_apply E w h]

/-- `‖E w x‖ ^ 2 = E_{x,x} w`. -/
lemma norm_apply_sq {w : Set X} (hw : MeasurableSet w) (x : H) :
    ‖E w x‖ ^ 2 = (E.toMeasure x).real w := by
  rw [measureReal_def, toMeasure_apply E w hw, ENNReal.toReal_ofReal (by positivity)]

/-- `E` is countably additive in the strong operator topology:
`E (⋃ i, w i) x = ∑ i, E (w i) x` in norm. -/
theorem hasSum_apply_iUnion {w : ℕ → Set X} (hw : ∀ i, MeasurableSet (w i))
    (hd : Pairwise (Disjoint on w)) (x : H) :
    HasSum (fun i ↦ E (w i) x) (E (⋃ i, w i) x) := by
  have hU : MeasurableSet (⋃ i, w i) := .iUnion hw
  have hs (s : Finset ℕ) : MeasurableSet (⋃ i ∈ s, w i) := s.measurableSet_biUnion fun i _ ↦ hw i
  have hsum (s : Finset ℕ) : ∑ i ∈ s, E (w i) x = E (⋃ i ∈ s, w i) x := by
    rw [E.apply_biUnion_finset (fun i _ ↦ hw i) (fun i _ j _ hij ↦ hd hij), _root_.sum_apply]
  have hdiff (s : Finset ℕ) :
      E (⋃ i ∈ s, w i) x - E (⋃ i, w i) x = -E ((⋃ i, w i) \ ⋃ i ∈ s, w i) x := by
    have hsub : (⋃ i ∈ s, w i) ⊆ ⋃ i, w i := Set.iUnion₂_subset fun i _ ↦ Set.subset_iUnion w i
    conv_lhs => rw [← Set.union_sdiff_cancel hsub, E.apply_union (hs s) (hU.diff (hs s))
      Set.disjoint_sdiff_right]
    simp
  -- `E_{x,x}` of the remainder `⋃ i, w i \ ⋃ i ∈ s, w i` tends to `0`
  have hmeas : Tendsto (fun s : Finset ℕ ↦ E.toMeasure x ((⋃ i, w i) \ ⋃ i ∈ s, w i))
      atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := E.toMeasure x)
      (s := fun s : Finset ℕ ↦ (⋃ i, w i) \ ⋃ i ∈ s, w i)
      (fun s ↦ (hU.diff (hs s)).nullMeasurableSet)
      (fun s t hst ↦ Set.sdiff_subset_sdiff_right (Set.biUnion_subset_biUnion_left hst))
      ⟨∅, measure_ne_top _ _⟩
    have h0 : (⋂ s : Finset ℕ, (⋃ i, w i) \ ⋃ i ∈ s, w i) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 hz ∅).1
      exact (Set.mem_iInter.1 hz {i}).2 (by simpa using hi)
    rwa [h0, measure_empty] at h
  rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hsum, hdiff, norm_neg]
  have hnorm (s : Finset ℕ) : ‖E ((⋃ i, w i) \ ⋃ i ∈ s, w i) x‖ =
      √((E.toMeasure x ((⋃ i, w i) \ ⋃ i ∈ s, w i)).toReal) := by
    rw [← measureReal_def, ← E.norm_apply_sq (hU.diff (hs s)), Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hnorm]
  simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeas).sqrt

/-- The `H`-valued measure `w ↦ E w x`, countably additive in norm (`hasSum_apply_iUnion`). Its
variation can be infinite. -/
noncomputable def applyVectorMeasure (x : H) : VectorMeasure X H where
  measureOf' w := E w x
  empty' := by simp
  not_measurable' w hw := by simp [E.apply_of_not_measurableSet hw]
  m_iUnion' w hw hd := E.hasSum_apply_iUnion hw hd x

@[simp]
lemma applyVectorMeasure_apply (x : H) (w : Set X) : E.applyVectorMeasure x w = E w x :=
  rfl

/-- A scalar measure with the same null sets as `E` (see `measure_eq_zero_iff`): the sum of the
measures `E_{x,x}` over all `x : H`. It only takes the values `0` and `∞` on measurable sets and is
not s-finite in general, so it should only be used through its null sets, e.g. to define
`L^∞(E)`. -/
noncomputable def measure : Measure X :=
  Measure.sum E.toMeasure

/-- A measurable set is `E.measure`-null iff `E` vanishes on it. -/
lemma measure_eq_zero_iff {w : Set X} (hw : MeasurableSet w) : E.measure w = 0 ↔ E w = 0 := by
  simp [measure, Measure.sum_apply _ hw, hw, ContinuousLinearMap.ext_iff]

/-- A set is `E.measure`-null iff it is contained in a measurable set on which `E` vanishes. -/
lemma measure_eq_zero_iff_exists_superset (s : Set X) :
    E.measure s = 0 ↔ ∃ w, s ⊆ w ∧ MeasurableSet w ∧ E w = 0 := by
  rw [← exists_measurable_superset_iff_measure_eq_zero]
  exact exists_congr fun w ↦ and_congr_right fun _ ↦ and_congr_right E.measure_eq_zero_iff

/-- `E.measure`-almost everywhere means outside a measurable set on which `E` vanishes. -/
lemma ae_iff {p : X → Prop} :
    (∀ᵐ x ∂E.measure, p x) ↔ ∃ w, MeasurableSet w ∧ E w = 0 ∧ ∀ x ∉ w, p x := by
  simp only [MeasureTheory.ae_iff, measure_eq_zero_iff_exists_superset, Set.subset_def,
    not_imp_comm]
  exact exists_congr fun w ↦ by tauto

lemma toMeasure_absolutelyContinuous (x : H) : E.toMeasure x ≪ E.measure :=
  (Measure.le_sum E.toMeasure x).absolutelyContinuous

lemma toComplexMeasure_absolutelyContinuous (x y : H) :
    E.toComplexMeasure x y ≪ᵥ E.measure.toENNRealVectorMeasure :=
  VectorMeasure.AbsolutelyContinuous.mk fun w hw h ↦ by
    rw [Measure.toENNRealVectorMeasure_apply_measurable hw, E.measure_eq_zero_iff hw] at h
    simp [h]

lemma norm_inner_le (w : Set X) (x y : H) : ‖⟪x, E w y⟫_ℂ‖ ≤ ‖E w x‖ * ‖E w y‖ := by
  have hp := E.isStarProjection w
  have h : ⟪E w x, E w y⟫_ℂ = ⟪x, E w y⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hp.isSelfAdjoint.adjoint_eq,
      ← mul_apply_eq_comp, hp.isIdempotentElem.eq]
  exact h ▸ norm_inner_le_norm _ _

/-- `|E_{x,y}| ≤ ½ (E_{x,x} + E_{y,y})`. -/
lemma variation_toComplexMeasure_le (x y : H) :
    (E.toComplexMeasure x y).variation ≤ (2 : ℝ≥0∞)⁻¹ • (E.toMeasure x + E.toMeasure y) := by
  refine VectorMeasure.variation_le_of_forall_enorm_le fun w hw ↦ ?_
  have key : ‖⟪x, E w y⟫_ℂ‖ ≤ (‖E w x‖ ^ 2 + ‖E w y‖ ^ 2) / 2 :=
    (E.norm_inner_le w x y).trans (by nlinarith [sq_nonneg (‖E w x‖ - ‖E w y‖)])
  simp only [toComplexMeasure_apply, Measure.smul_apply, Measure.add_apply,
    toMeasure_apply E w hw, smul_eq_mul]
  rw [← ofReal_norm, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine (ENNReal.ofReal_le_ofReal key).trans_eq ?_
  rw [div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
    ENNReal.ofReal_ofNat]

/-- The variation of `E_{x,y}` is absolutely continuous with respect to `E.measure`. -/
lemma variation_toComplexMeasure_absolutelyContinuous (x y : H) :
    (E.toComplexMeasure x y).variation ≪ E.measure :=
  (E.variation_toComplexMeasure_le x y).absolutelyContinuous.trans <|
    ((E.toMeasure_absolutelyContinuous x).add_left (E.toMeasure_absolutelyContinuous y)).smul_left _

lemma toComplexMeasure_smul {t : ℝ} (ht : t ≠ 0) (x y : H) :
    E.toComplexMeasure ((t : ℂ) • x) ((t⁻¹ : ℂ) • y) = E.toComplexMeasure x y :=
  VectorMeasure.ext fun w _ ↦ by
    simp [ht]

/-- `|E_{x,y}|(X) ≤ ‖x‖ ‖y‖`. -/
lemma variation_toComplexMeasure_univ_le (x y : H) :
    (E.toComplexMeasure x y).variation Set.univ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  have hbound (u v : H) :
      (E.toComplexMeasure u v).variation Set.univ ≤ ENNReal.ofReal ((‖u‖ ^ 2 + ‖v‖ ^ 2) / 2) := by
    refine (Measure.le_iff'.1 (E.variation_toComplexMeasure_le u v) _).trans_eq ?_
    rw [Measure.smul_apply, Measure.add_apply, toMeasure_univ, toMeasure_univ, smul_eq_mul,
      ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
      div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hzero {u v : H} (h : u = 0 ∨ v = 0) : E.toComplexMeasure u v = 0 :=
    VectorMeasure.ext fun w _ ↦ by rcases h with rfl | rfl <;> simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp [hzero (.inl rfl)]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [hzero (.inr rfl)]
  set t := Real.sqrt (‖y‖ / ‖x‖)
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx))
  have hsq : t ^ 2 = ‖y‖ / ‖x‖ := Real.sq_sqrt (by positivity)
  rw [← E.toComplexMeasure_smul ht.ne' x y, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine (hbound _ _).trans_eq (congrArg ENNReal.ofReal ?_)
  rw [norm_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_pow,
    mul_pow, inv_pow, hsq]
  field_simp
  ring

/-- The algebra `L^∞(E)` (Rudin 12.20). Its elements are classes of bounded measurable functions
modulo functions vanishing outside an `E`-null set (`ae_iff`), and its norm is Rudin's
essential supremum `‖f‖_∞` with respect to `E`. -/
noncomputable abbrev Linfty := Lp ℂ ∞ E.measure

/-- `∫ |f|² dE_{x,x} ≤ ‖f‖_∞² ‖x‖²` (Rudin 12.21 (12)). -/
lemma lintegral_enorm_sq_le (f : X → ℂ) (x : H) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ∂E.toMeasure x ≤ eLpNorm f ∞ E.measure ^ 2 * ‖x‖ₑ ^ 2 := by
  refine (lintegral_mono_ae ?_).trans_eq (by rw [lintegral_const, toMeasure_univ])
  filter_upwards [(E.toMeasure_absolutelyContinuous x).ae_le
    (ae_le_eLpNormEssSup (f := f) (μ := E.measure))] with y hy
  gcongr
  exact hy.trans eLpNormEssSup_le_eLpNorm_top

lemma measure_ne_zero [Nontrivial H] : E.measure ≠ 0 := by
  rw [Ne, ← Measure.measure_univ_eq_zero, E.measure_eq_zero_iff .univ, apply_univ]
  exact one_ne_zero

/-- The `L^∞(E)` norm of a simple function `s` is the supremum of `‖a‖ₑ` over the values `a` of
`s` with `E (s ⁻¹' {a}) ≠ 0`. -/
lemma eLpNorm_top_eq_iSup (s : SimpleFunc X ℂ) :
    eLpNorm s ∞ E.measure = ⨆ (a) (_ : E (s ⁻¹' {a}) ≠ 0), ‖a‖ₑ := by
  simp_rw [s.eLpNorm_top_eq_iSup, Ne, E.measure_eq_zero_iff (s.measurableSet_preimage _)]

/-- The `L^∞(E)` norm of a simple function `s` is `‖a‖ₑ` for a value `a` of `s` with
`E (s ⁻¹' {a}) ≠ 0` (used in Rudin 12.21 to show `‖Ψ(s)‖ = ‖s‖_∞`). -/
lemma exists_eLpNorm_top_eq [Nontrivial H] (s : SimpleFunc X ℂ) :
    ∃ a, E (s ⁻¹' {a}) ≠ 0 ∧ eLpNorm s ∞ E.measure = ‖a‖ₑ := by
  simp_rw [Ne, ← E.measure_eq_zero_iff (s.measurableSet_preimage _)]
  exact s.exists_eLpNorm_top_eq E.measure_ne_zero

end ProjectionValuedMeasure
