module

public import Mathlib

/-!
# Lemmas on `L^∞`

General facts about `Lp E ∞ μ`, used to identify `L^∞(E)` of a projection-valued measure `E` with
Rudin's quotient `B / N` of bounded measurable functions (Rudin, *Functional Analysis*, 12.20).
None of them needs any finiteness assumption on `μ`.

## Main results

* `MeasureTheory.Lp.exists_stronglyMeasurable_forall_norm_le_ae_eq`: every element of `Lp E ∞ μ`
  has a strongly measurable representative bounded *everywhere* by the norm of the class.
* `IsCompact.exists_simpleFunc_dist_lt`: on a compact set, the identity can be uniformly
  approximated by a simple function.
* `MeasureTheory.Lp.simpleFunc.dense_top`: simple functions are dense in `Lp E ∞ μ`.
* `MeasureTheory.SimpleFunc.eLpNorm_top_eq_iSup`: the `L^∞` norm of a simple function is the
  supremum of `‖a‖ₑ` over the values `a` taken on a set of positive measure.
-/

@[expose] public section

open MeasureTheory ENNReal Set Filter Topology

/-- On a compact set `K`, the identity can be uniformly approximated by a simple function. -/
lemma IsCompact.exists_simpleFunc_dist_lt {α : Type*} [PseudoMetricSpace α] [Zero α]
    [MeasurableSpace α] [OpensMeasurableSpace α] {K : Set α} (hK : IsCompact K) {ε : ℝ}
    (hε : 0 < ε) : ∃ q : SimpleFunc α α, ∀ y ∈ K, dist y (q y) < ε := by
  suffices ∃ (q : SimpleFunc α α) (U : Set α), MeasurableSet U ∧ K ⊆ U ∧
      ∀ y ∈ U, dist y (q y) < ε by
    obtain ⟨q, U, -, hKU, hq⟩ := this
    exact ⟨q, fun y hy ↦ hq y (hKU hy)⟩
  refine hK.induction_on ⟨0, ∅, .empty, Subset.rfl, by simp⟩
    (fun t t' htt' ⟨q, U, hU, ht'U, hq⟩ ↦ ⟨q, U, hU, htt'.trans ht'U, hq⟩)
    (fun t t' ⟨q, U, hU, htU, hq⟩ ⟨q', U', hU', ht'U', hq'⟩ ↦
      ⟨q.piecewise U hU q', U ∪ U', hU.union hU', union_subset_union htU ht'U', fun y hy ↦ ?_⟩)
    fun y _ ↦ ⟨Metric.ball y ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y hε),
      .const α y, Metric.ball y ε, Metric.isOpen_ball.measurableSet, Subset.rfl,
      fun z hz ↦ by simpa using hz⟩
  rw [SimpleFunc.piecewise_apply]
  split_ifs with h
  exacts [hq y h, hq' y (hy.resolve_left h)]

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E]

/-- A simple function takes almost everywhere values whose preimage has positive measure. -/
lemma SimpleFunc.ae_measure_preimage_singleton_ne_zero {β : Type*} (s : SimpleFunc α β) :
    ∀ᵐ x ∂μ, μ (s ⁻¹' {s x}) ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ b ∈ s.range, ⋃ (_ : μ (s ⁻¹' {b}) = 0), s ⁻¹' {b})
    (fun x hx ↦ ?_) ?_
  · exact mem_biUnion (s.mem_range_self x) (mem_iUnion.2 ⟨not_not.1 hx, rfl⟩)
  · exact (measure_biUnion_null_iff s.range.countable_toSet).2 fun b _ ↦
      measure_iUnion_null fun h ↦ h

/-- The `L^∞` norm of a simple function is the supremum of `‖a‖ₑ` over the values `a` taken on a
set of positive measure. -/
lemma SimpleFunc.eLpNorm_top_eq_iSup (s : SimpleFunc α E) :
    eLpNorm s ∞ μ = ⨆ (a) (_ : μ (s ⁻¹' {a}) ≠ 0), ‖a‖ₑ := by
  rw [eLpNorm_exponent_top s.aestronglyMeasurable]
  refine le_antisymm (eLpNormEssSup_le_of_ae_enorm_bound ?_) (iSup₂_le fun a ha ↦ ?_)
  · filter_upwards [s.ae_measure_preimage_singleton_ne_zero] with x hx
    exact le_iSup₂ (f := fun a (_ : μ (s ⁻¹' {a}) ≠ 0) ↦ ‖a‖ₑ) (s x) hx
  · refine le_of_not_gt fun hlt ↦ ha (measure_mono_null (fun x (hx : s x = a) ↦ ?_)
      (ae_iff.1 (ae_lt_of_essSup_lt hlt)))
    simp [hx]

/-- If `μ ≠ 0`, the `L^∞` norm of a simple function `s` is attained: it equals `‖a‖ₑ` for some
value `a` of `s` with `μ (s ⁻¹' {a}) ≠ 0`. -/
lemma SimpleFunc.exists_eLpNorm_top_eq (s : SimpleFunc α E) (hμ : μ ≠ 0) :
    ∃ a, μ (s ⁻¹' {a}) ≠ 0 ∧ eLpNorm s ∞ μ = ‖a‖ₑ := by
  have hfin : {a | μ (s ⁻¹' {a}) ≠ 0}.Finite := s.finite_range.subset fun a ha ↦
    by_contra fun h ↦ ha (by rw [preimage_singleton_eq_empty.2 h, measure_empty])
  have := hfin.to_subtype
  have := ae_neBot.2 hμ
  obtain ⟨x, hx⟩ := (s.ae_measure_preimage_singleton_ne_zero (μ := μ)).exists
  have : Nonempty {a // μ (s ⁻¹' {a}) ≠ 0} := ⟨⟨s x, hx⟩⟩
  obtain ⟨⟨a, ha⟩, h⟩ := exists_eq_ciSup_of_finite (f := fun a : {a // μ (s ⁻¹' {a}) ≠ 0} ↦ ‖a.1‖ₑ)
  exact ⟨a, ha, by rw [s.eLpNorm_top_eq_iSup, iSup_subtype', h]⟩

namespace Lp

lemma ae_norm_le_norm (f : Lp E ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f), ← Lp.enorm_def] at hx
  exact enorm_le_iff_norm_le.mp hx

lemma norm_le_of_ae_bound_top {f : Lp E ∞ μ} {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ‖f‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound hfC)

/-- Every element of `Lp E ∞ μ` has a strongly measurable representative which is bounded
everywhere by the norm of the class. -/
lemma exists_stronglyMeasurable_forall_norm_le_ae_eq (f : Lp E ∞ μ) :
    ∃ g : α → E, StronglyMeasurable g ∧ (∀ x, ‖g x‖ ≤ ‖f‖) ∧ f =ᵐ[μ] g := by
  have hf := Lp.stronglyMeasurable f
  have hs : MeasurableSet {x | ‖f x‖ ≤ ‖f‖} := measurableSet_le hf.norm.measurable measurable_const
  refine ⟨{x | ‖f x‖ ≤ ‖f‖}.indicator f, hf.indicator hs, fun x ↦ ?_, ?_⟩
  · by_cases hx : ‖f x‖ ≤ ‖f‖ <;> simp [hx]
  · filter_upwards [ae_norm_le_norm f] with x hx using (indicator_of_mem hx _).symm

variable [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- Every element of `Lp E ∞ μ` is uniformly approximated by simple functions. -/
lemma exists_simpleFunc_norm_sub_lt (f : Lp E ∞ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : SimpleFunc α E, ‖f - (s.memLp_top μ).toLp s‖ < ε := by
  obtain ⟨g, hg, hgf, hfg⟩ := exists_stronglyMeasurable_forall_norm_le_ae_eq f
  obtain ⟨q, hq⟩ := (isCompact_closedBall (0 : E) ‖f‖).exists_simpleFunc_dist_lt (half_pos hε)
  let s := q.comp g hg.measurable
  refine ⟨s, (norm_le_of_ae_bound_top (half_pos hε).le ?_).trans_lt (half_lt_self hε)⟩
  filter_upwards [Lp.coeFn_sub f ((s.memLp_top μ).toLp s), hfg, (s.memLp_top μ).coeFn_toLp]
    with x h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, h₃, ← dist_eq_norm_sub]
  exact (hq _ (mem_closedBall_zero_iff.mpr (hgf x))).le

/-- Simple functions are dense in `Lp E ∞ μ`. -/
lemma simpleFunc.dense_top : Dense (Lp.simpleFunc E ∞ μ : Set (Lp E ∞ μ)) :=
  Metric.dense_iff.2 fun f _ hr ↦
    have ⟨s, hs⟩ := exists_simpleFunc_norm_sub_lt f hr
    ⟨_, by rwa [Metric.mem_ball', dist_eq_norm_sub], (s.toLp (s.memLp_top μ)).2⟩

/-- The inclusion of simple functions in `Lp E ∞ μ` has dense range. -/
lemma simpleFunc.denseRange_top : DenseRange ((↑) : Lp.simpleFunc E ∞ μ → Lp E ∞ μ) :=
  simpleFunc.dense_top.denseRange_val

end Lp

/-! ### Extension of a set function from simple functions to `L^∞`

The `L^∞` analogue of `MeasureTheory.L1.setToL1`. A set function `T : Set α → E →L[ℝ] F` defines
`f ↦ ∑ x ∈ f.range, T (f ⁻¹' {x}) x` on simple functions (`SimpleFunc.setToSimpleFunc`). If `T` is
additive on disjoint measurable sets, vanishes on `μ`-null sets and this map is bounded in the `L^∞`
norm, it extends to a continuous linear map `Lp E ∞ μ →L[𝕜] F`. Unlike `setToL1`, no finiteness of
`μ` is involved: only its null sets matter. -/

section SetToLinfty

open Lp.simpleFunc

attribute [local instance] Lp.simpleFunc.module Lp.simpleFunc.normedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℝ E]

/-- `T` is additive on disjoint measurable sets, vanishes on `μ`-null sets, and the induced map
on simple functions is bounded by `C` in the `L^∞(μ)` norm. This is the `L^∞` analogue of
`DominatedFinMeasAdditive`. -/
structure DominatedLinftyAdditive (μ : Measure α) (T : Set α → E →L[ℝ] F) (C : ℝ) : Prop where
  add : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → T (s ∪ t) = T s + T t
  eq_zero_of_measure_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0
  norm_setToSimpleFunc_le : ∀ f : SimpleFunc α E, ‖f.setToSimpleFunc T‖ ≤ C * (eLpNorm f ∞ μ).toReal

variable {T : Set α → E →L[ℝ] F} {C : ℝ}

namespace DominatedLinftyAdditive

lemma finMeasAdditive (hT : DominatedLinftyAdditive μ T C) (ν : Measure α) :
    FinMeasAdditive ν T :=
  fun s t hs ht _ _ h ↦ hT.add s t hs ht h

/-- `SimpleFunc.setToSimpleFunc T` only depends on the `μ`-a.e. class of a simple function. -/
lemma setToSimpleFunc_congr (hT : DominatedLinftyAdditive μ T C) {f g : SimpleFunc α E}
    (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T := by
  refine SimpleFunc.setToSimpleFunc_congr' T (hT.finMeasAdditive 0) integrable_zero_measure
    integrable_zero_measure fun a b hab ↦ hT.eq_zero_of_measure_zero _
      ((f.measurableSet_fiber a).inter (g.measurableSet_fiber b)) ?_
  refine measure_mono_null ?_ (ae_iff.1 h)
  rintro x ⟨hxa, hxb⟩ hfg
  exact hab (hxa.symm.trans (hfg.trans hxb))

end DominatedLinftyAdditive

/-- `T` applied to (a representative of) an element of `Lp.simpleFunc E ∞ μ`. -/
noncomputable def setToLinftyS (T : Set α → E →L[ℝ] F) (f : Lp.simpleFunc E ∞ μ) : F :=
  (toSimpleFunc f).setToSimpleFunc T

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

/-- `setToLinftyS` as a continuous linear map on `Lp.simpleFunc E ∞ μ`. -/
noncomputable def setToLinftySCLM (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : Lp.simpleFunc E ∞ μ →L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := setToLinftyS T
      map_add' f g := by
        simp only [setToLinftyS]
        rw [hT.setToSimpleFunc_congr (g := toSimpleFunc f + toSimpleFunc g) (add_toSimpleFunc f g),
          SimpleFunc.setToSimpleFunc_add T (hT.finMeasAdditive 0) integrable_zero_measure
            integrable_zero_measure]
      map_smul' c f := by
        simp only [setToLinftyS, RingHom.id_apply]
        rw [hT.setToSimpleFunc_congr (g := c • toSimpleFunc f) (smul_toSimpleFunc c f),
          SimpleFunc.setToSimpleFunc_smul T (hT.finMeasAdditive 0) h_smul c
            integrable_zero_measure] }
    C fun f ↦ (hT.norm_setToSimpleFunc_le _).trans_eq (by rw [norm_toSimpleFunc])

variable [MeasurableSpace E] [BorelSpace E] [ProperSpace E] [CompleteSpace F]

/-- Extend a set function `T : Set α → E →L[ℝ] F` satisfying `DominatedLinftyAdditive μ T C` to a
continuous linear map `Lp E ∞ μ →L[𝕜] F`. -/
noncomputable def setToLinfty (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : Lp E ∞ μ →L[𝕜] F :=
  (setToLinftySCLM 𝕜 hT h_smul).extend (coeToLp α E 𝕜)

variable {𝕜}

lemma setToLinfty_eq_setToLinftyS (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : Lp.simpleFunc E ∞ μ) :
    setToLinfty 𝕜 hT h_smul f = setToLinftyS T f :=
  ContinuousLinearMap.extend_eq _ Lp.simpleFunc.denseRange_top isUniformInducing f

/-- On (the class of) a simple function, `setToLinfty` is `SimpleFunc.setToSimpleFunc`. -/
lemma setToLinfty_toLp (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : SimpleFunc α E) :
    setToLinfty 𝕜 hT h_smul ((f.memLp_top μ).toLp f) = f.setToSimpleFunc T := by
  rw [← toLp_eq_toLp f (f.memLp_top μ), setToLinfty_eq_setToLinftyS, setToLinftyS,
    hT.setToSimpleFunc_congr (toSimpleFunc_toLp f _)]

lemma norm_setToLinfty_le (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (hC : 0 ≤ C) :
    ‖setToLinfty 𝕜 hT h_smul‖ ≤ C :=
  (ContinuousLinearMap.opNorm_extend_le _ Lp.simpleFunc.denseRange_top (N := 1)
    fun x ↦ by simp; exact le_rfl).trans <| by
    rw [NNReal.coe_one, one_mul]
    exact LinearMap.mkContinuous_norm_le _ hC _

/-- If `T` is isometric on simple functions, then so is `setToLinfty`. -/
lemma norm_setToLinfty_apply (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
    (h_norm : ∀ f : SimpleFunc α E, ‖f.setToSimpleFunc T‖ = (eLpNorm f ∞ μ).toReal)
    (f : Lp E ∞ μ) : ‖setToLinfty 𝕜 hT h_smul f‖ = ‖f‖ := by
  refine Lp.simpleFunc.denseRange_top.induction_on f
    (isClosed_eq (continuous_norm.comp (setToLinfty 𝕜 hT h_smul).continuous) continuous_norm)
    fun g ↦ ?_
  rw [setToLinfty_eq_setToLinftyS, setToLinftyS, h_norm, ← norm_toSimpleFunc]
  rfl

end SetToLinfty

end MeasureTheory
