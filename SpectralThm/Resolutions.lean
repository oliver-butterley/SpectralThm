module

public import Mathlib
public import SpectralThm.Linfty
-- public import SpectralThm.WStarAlgebra.BorelFunctionalCalculus

/-!
# Resoltuions of the identity



-/

@[expose] public section

open scoped Function InnerProductSpace
open MeasureTheory BigOperators ENNReal

section Def

variable (X : Type*) [MeasurableSpace X]
  (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ResolutionOfIdentity where
  /-- The projection-valued measure of sets -/
  measureOf' : Set X → (H →L[ℂ] H)
  /-- Each element is an orthogonal projection -/
  IsStarProjection' : ∀ w, IsStarProjection (measureOf' w)
  /-- The empty set has measure zero -/
  empty' : measureOf' ∅ = 0
  /-- The whole space has measure the identity -/
  univ' : measureOf' Set.univ = 1
  /-- Non-measurable sets have measure zero -/
  not_measurable' ⦃i : Set X⦄ : ¬MeasurableSet i → measureOf' i = 0
  /-- The measure is additive -/
  m_Union' ⦃w₁ w₂ : Set X⦄ : MeasurableSet w₁ → MeasurableSet w₂ → Disjoint w₁ w₂ →
    measureOf' (w₁ ∪ w₂) = measureOf' w₁ + measureOf' w₂
  /-- The measure of the intersection is the intersection of the measures -/
  m_Inter' ⦃w₁ w₂ : Set X⦄ : MeasurableSet w₁ → MeasurableSet w₂ → measureOf' (w₁ ∩ w₂) =
    measureOf' w₁ * measureOf' w₂
  /-- The measure is weakly countably additive -/
  m_iUnion' {x y : H} ⦃w : ℕ → Set X⦄ : (∀ i, MeasurableSet (w i)) → Pairwise (Disjoint on w) →
    HasSum (fun i => ⟪x, measureOf' (w i) y⟫_ℂ) (⟪x, measureOf' (⋃ i, w i) y⟫_ℂ)

instance ResolutionOfIdentity.instFunLike : FunLike (ResolutionOfIdentity X H)
    (Set X) (H →L[ℂ] H) where
  coe E := E.measureOf'
  coe_injective | ⟨_, _, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _, _⟩, rfl => rfl

end Def

/-- For a star projection `p`, `⟪x, p x⟫ = ‖p x‖ ^ 2`. -/
lemma IsStarProjection.inner_apply_self {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] {p : H →L[𝕜] H} (hp : IsStarProjection p) (x : H) :
    ⟪x, p x⟫_𝕜 = (‖p x‖ : 𝕜) ^ 2 := by
  rw [← inner_self_eq_norm_sq_to_K, ← ContinuousLinearMap.adjoint_inner_right,
    hp.isSelfAdjoint.adjoint_eq, ← mul_apply_eq_comp, hp.isIdempotentElem.eq]

section OrthogonalProjection

section Def

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def OrthogonalProjection := { p : H →L[ℂ] H // IsStarProjection p }

end Def

namespace OrthogonalProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma norm_le_of_le (x : H) {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : p ≤ q) : ‖p x‖ ≤ ‖q x‖ := by
  calc
    ‖p x‖ = ‖(p * q) x‖ := by rw [hp.le_iff_mul_eq_left hq |>.mp h]
    _ = ‖p (q x)‖ := by rw [mul_apply_eq_comp]
    _ ≤ ‖p‖ * ‖q x‖ := p.le_opNorm (q x)
    _ ≤ 1 * ‖q x‖ := mul_le_mul_of_nonneg_right (hp.norm_le p) (norm_nonneg _)
    _ = ‖q x‖ := one_mul _

variable (p q : OrthogonalProjection H)

def IsOrthogonalTo : Prop := p.val * q.val = 0

#check p.IsOrthogonalTo q

lemma IsOrthogonalTo.symm (h : p.IsOrthogonalTo q) : q.IsOrthogonalTo p := by
  unfold IsOrthogonalTo
  rw [← star_eq_zero]; simpa [p.property.isSelfAdjoint.star_eq, q.property.isSelfAdjoint.star_eq]

lemma add_isStarProjection_of_isOrthogonalTo (p q : OrthogonalProjection H)
    (h : p.IsOrthogonalTo q) : IsStarProjection (p.val + q.val) := by
  refine ⟨?_, IsSelfAdjoint.add p.property.isSelfAdjoint q.property.isSelfAdjoint⟩
  refine IsIdempotentElem.add p.property.isIdempotentElem q.property.isIdempotentElem ?_
  rw [h, h.symm]; simp


variable (ι : Type*) (p : ι → OrthogonalProjection H) (x : H)

#check fun i ↦ ((p i).val.toPointwiseConvergenceCLM _ _ _ _)
#check ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ q.val

example : ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _ q.val x = q.val x := by rfl

-- TODO
-- define the union of ranges of `p`
-- show that if `(p : ι → OrthogonalProjection H)`, then
-- `HasSum (fun i ↦ (p i).val.toPointwiseConvergenceCLM)

end OrthogonalProjection

end OrthogonalProjection

namespace ResolutionOfIdentity

variable {X : Type*} {mX : MeasurableSpace X}
 {H : Type*} {nacgH : NormedAddCommGroup H} {ipsH : InnerProductSpace ℂ H} {csH : CompleteSpace H}
 (E : ResolutionOfIdentity X H)

lemma apply (w : Set X) : E w = E.measureOf' w := by rfl

@[simp]
lemma m_Union {w₁ w₂ : Set X} (h1 : MeasurableSet w₁) (h2 : MeasurableSet w₂) (h : Disjoint w₁ w₂) :
    E.measureOf' (w₁ ∪ w₂) = E.measureOf' w₁ + E.measureOf' w₂ :=
  E.m_Union' (w₁ := w₁) (w₂ := w₂) h1 h2 h

lemma subset_iff_le (w₁ w₂ : Set X) (h1 : MeasurableSet w₁) (h2 : MeasurableSet w₂) (h : w₁ ⊆ w₂) :
    E w₁ ≤ E w₂ := by
  rw [apply, apply, ← Set.union_sdiff_cancel h, E.m_Union' h1 (h2.diff h1) Set.disjoint_sdiff_right]
  simpa using (E.IsStarProjection' (w₂ \ w₁)).nonneg

noncomputable def toComplexMeasure (x y : H) : ComplexMeasure X where
  measureOf' w := ⟪x, E.measureOf' w y⟫_ℂ
  empty' := by simp [E.empty', zero_apply, inner_zero_right]
  not_measurable' w h := by simp [E.not_measurable' h, zero_apply, inner_zero_right]
  m_iUnion' := E.m_iUnion'

lemma inner_apply_self (w : Set X) (x : H) : ⟪x, E w x⟫_ℂ = (‖E w x‖ : ℂ) ^ 2 :=
  (E.IsStarProjection' w).inner_apply_self x

@[simp]
lemma toComplexMeasure_apply (x y : H) (w : Set X) : E.toComplexMeasure x y w = ⟪x, E w y⟫_ℂ :=
  rfl

/-- The positive measure `E_{x,x} w = ⟪x, E w x⟫ = ‖E w x‖ ^ 2` (Rudin 12.17). -/
noncomputable def toMeasure (x : H) : Measure X := Measure.ofMeasurable
  (fun w _ ↦ ENNReal.ofReal (‖E w x‖ ^ 2))
  (by simp [apply, E.empty'])
  (fun f hf hd ↦ by
    have h := E.m_iUnion' (x := x) (y := x) hf hd
    simp_rw [← apply, inner_apply_self, ← Complex.ofReal_pow] at h
    have h' := Complex.hasSum_ofReal.mp h
    rw [← h'.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) h'.summable])

@[simp]
lemma toMeasure_apply (w : Set X) (hw : MeasurableSet w) (x : H) :
    E.toMeasure x w = ENNReal.ofReal (‖E w x‖ ^ 2) :=
  Measure.ofMeasurable_apply w hw

@[simp]
lemma toMeasure_univ (x : H) : E.toMeasure x Set.univ = ‖x‖ₑ ^ 2 := by
  simp [apply, E.univ', ENNReal.ofReal_pow, ofReal_norm]

instance (x : H) : IsFiniteMeasure (E.toMeasure x) :=
  ⟨by simp⟩

lemma zero_iff (w : Set X) (h : MeasurableSet w) : E w  = 0 ↔ ∀ x, (toMeasure E x) w = 0 := by
  simp [ContinuousLinearMap.ext_iff, toMeasure_apply E w h]

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
  rw [Ne, ← Measure.measure_univ_eq_zero, E.measure_eq_zero_iff .univ, apply, E.univ']
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

end ResolutionOfIdentity

/- TODO

- From a self-adjoint operator `a`, by `IsStarNormal.instContinuousFunctionalCalculus` you can do
the continuous functional calculus: it is a *-isomorphism from the space of continuous functions
on the spectrum to B(H). This is denoted by `cfcHom` (in Rudin it is the map from \hat T to T in
Theorem 12.22).
- Applying vectors `x y` we get bounded complex linear functionals, and by ComplexRMK we get
measures `E_{x, y}`. So the linear functionals can be extended to Borel functions, and it is still
bounded.
- Theorem 12.8 which gives an operator from a bounded sesquilinear form is already there
`InnerProductSpace.continuousLinearMapOfBilin`, and this, combined with ComplexRMK, should give the
resolution of identity from a operator.
- From a resolution of identity, we should define \Psi(f) by Theorem 12.21
- Finally we should prove that \Psi equals the extension of cfcHom. This is the spectral theorem
.-/
