import Mathlib
import SpectralThm.WStarAlgebra.BorelFunctionalCalculus

/-!
# Resoltuions of the identity



-/

open scoped Function InnerProductSpace
open MeasureTheory BigOperators ENNReal

variable (α : Type*) [MeasurableSpace α]

variable {H: Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsOrthogonalProjection (p : H →L[ℂ] H) : Prop := p = p ^ 2 ∧ p = p.adjoint

lemma IsStarProjection_iff (p : H →L[ℂ] H) : IsStarProjection p ↔ ∃ (K : Submodule ℂ H),
    ∃ (kH : K.HasOrthogonalProjection), p = K.subtypeL.comp (@K.orthogonalProjection _ _ _ _ _ kH)
  := by sorry -- waiting for #25958

-- the subspace corresponding to the orthogonal projection
noncomputable def toSubmodule (p : H →L[ℂ] H) (hp : IsStarProjection p) :
  Submodule ℂ H := Classical.choose ((IsStarProjection_iff p).mp hp)

-- the projection as `orthogonalProjection`
noncomputable def toOrthogonalProjection (p : H →L[ℂ] H) (hp : IsStarProjection p) :
  H →L[ℂ] (toSubmodule p hp) :=
  (@(toSubmodule p hp).orthogonalProjection _ _ _ _ _ (Classical.choose (Classical.choose_spec
    ((IsStarProjection_iff p).mp hp))))

structure ResolutionOfIdentity (α : Type*) [MeasurableSpace α] (H: Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection-valued measure of sets -/
  measureOf' : Set α → (H →L[ℂ] H)
  /-- Each element is an orthogonal projection -/
  isOrthogonalProjection' : ∀ w, IsOrthogonalProjection (measureOf' w)
  /-- The empty set has measure zero -/
  empty' : measureOf' ∅ = 0
  /-- Non-measurable sets have measure zero -/
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measureOf' i = 0
  /-- The measure is additive -/
  m_Union' ⦃w₁ w₂ : Set α⦄ : MeasurableSet w₁ → MeasurableSet w₂ → Disjoint w₁ w₂ →
    measureOf' (w₁ ∪ w₂) = measureOf' w₁ + measureOf' w₂
  /-- The measure of the intersection is the intersection of the measures -/
  m_Inter' ⦃w₁ w₂ : Set α⦄ : MeasurableSet w₁ → MeasurableSet w₂ → measureOf' (w₁ ∩ w₂) =
    measureOf' w₁ * measureOf' w₂
  /-- The measure is weakly countably additive -/
  m_iUnion' {x y : H} ⦃w : ℕ → Set α⦄ : (∀ i, MeasurableSet (w i)) → Pairwise (Disjoint on w) →
    HasSum (fun i => ⟪x, measureOf' (w i) y⟫_ℂ) (⟪x, measureOf' (⋃ i, w i) y⟫_ℂ)


instance ResolutionOfIdentity.instFunLike [MeasurableSpace α] : FunLike (ResolutionOfIdentity α H)
    (Set α) (H →L[ℂ] H) where
  coe E := E.measureOf'
  coe_injective' | ⟨_, _, _, _,  _, _, _⟩, ⟨_, _, _, _, _, _, _⟩, rfl => rfl

def toComplexMeasure {α : Type*} [MeasurableSpace α] (E : ResolutionOfIdentity α H) (x y : H) : ComplexMeasure α where
  measureOf' w := ⟪x, E.measureOf' w y⟫_ℂ
  empty' := by
    rw [E.empty']
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
  not_measurable' w h := by
    rw [E.not_measurable' h]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
  m_iUnion' := E.m_iUnion'

def toOuterMeasure {α : Type*} [MeasurableSpace α] (E : ResolutionOfIdentity α H) (x : H) : OuterMeasure α where
  measureOf w := ENNReal.ofReal ‖E.measureOf' w x‖
  empty := by
    rw [E.empty']
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, norm_zero, ofReal_zero]
  mono {w₁ w₂} h := by
    rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    sorry
  iUnion_nat := sorry

noncomputable def toMeasure {α : Type*} [MeasurableSpace α] (E : ResolutionOfIdentity α H)
    (x : H) : Measure α :=
  {
    toOuterMeasure := (toOuterMeasure E x).trim
    m_iUnion {f} f_measurable f_disjoint := sorry
    trim_le := by
      rw [MeasureTheory.OuterMeasure.trim_trim]
  }

variable (E : ResolutionOfIdentity α H)

lemma ResolutionOfIdentity.zero_iff (w : Set α) (h : MeasurableSet w) : E w  = 0 ↔
    ∀ x, (toMeasure E x) w = 0 := by
  sorry

noncomputable def SumOuterMeasure {ι : Type*} (μ : ι → Measure α) : OuterMeasure α where
  measureOf w := ∑' i, μ i w
  empty := by
    simp only [measure_empty, tsum_zero]
  mono {w₁ w₂} h := Summable.tsum_le_tsum (fun i => (μ i).mono h) ENNReal.summable ENNReal.summable
  iUnion_nat w h := by
    rw [← Summable.tsum_comm' ENNReal.summable (fun i => ENNReal.summable)
      (fun i => ENNReal.summable)]
    apply Summable.tsum_le_tsum _ ENNReal.summable ENNReal.summable
    exact fun i => (μ i).iUnion_nat w h

noncomputable def SumMeasure {ι : Type*} (μ : ι → Measure α) : Measure α :=
  {
    toOuterMeasure := (SumOuterMeasure α μ).trim
    m_iUnion {f} f_measurable f_disjoint := by
      rw [MeasureTheory.OuterMeasure.trim_eq _ (MeasurableSet.iUnion f_measurable)]
      have : ∑' i, (SumOuterMeasure α μ).trim (f i) = ∑' i, (SumOuterMeasure α μ) (f i) := by
        congr
        ext i
        exact MeasureTheory.OuterMeasure.trim_eq _ (f_measurable i)
      rw [this]
      rw [← MeasureTheory.OuterMeasure.measureOf_eq_coe]
      rw [SumOuterMeasure]
      rw [← Summable.tsum_comm' ENNReal.summable (fun i => ENNReal.summable)
        (fun i => ENNReal.summable)]
      simp only
      congr
      ext i
      exact (μ i).m_iUnion f_measurable f_disjoint
    trim_le := by
      rw [MeasureTheory.OuterMeasure.trim_trim]
  }

noncomputable def ofUnitBall : {x : H // ‖x‖ ≤ 1} → Measure α := fun x => toMeasure E x

noncomputable def Linfty (E : ResolutionOfIdentity α H) := MeasureTheory.Lp ℂ ⊤ (SumMeasure α (ofUnitBall α E))

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
