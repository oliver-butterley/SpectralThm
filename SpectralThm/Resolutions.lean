import Mathlib

/-!
# Resoltuions of the identity



-/

open scoped Function InnerProductSpace
open MeasureTheory

variable (α : Type*) [MeasurableSpace α]

variable {H: Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsOrthogonalProjection (p : H →L[ℂ] H) : Prop := p = p ^ 2 ∧ p = p.adjoint

lemma IsOrthogonalProjection_iff (p : H →L[ℂ] H) : IsOrthogonalProjection p ↔ ∃ (K : Submodule ℂ H),
    ∃ (kH : K.HasOrthogonalProjection), p = K.subtypeL.comp (@K.orthogonalProjection _ _ _ _ _ kH)
  := by sorry

-- the subspace corresponding to the orthogonal projection
noncomputable def toSubmodule (p : H →L[ℂ] H) (hp : IsOrthogonalProjection p) :
  Submodule ℂ H := Classical.choose ((IsOrthogonalProjection_iff p).mp hp)

-- the projection as `orthogonalProjection`
noncomputable def toOrthogonalProjection (p : H →L[ℂ] H) (hp : IsOrthogonalProjection p) :
  H →L[ℂ] (toSubmodule p hp) :=
  (@(toSubmodule p hp).orthogonalProjection _ _ _ _ _ (Classical.choose (Classical.choose_spec
    ((IsOrthogonalProjection_iff p).mp hp))))

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

def toComplexMeasure (E : ResolutionOfIdentity α H) (x y : H) : ComplexMeasure α where
  measureOf' w := ⟪x, E.measureOf' w y⟫_ℂ
  empty' := by
    rw [E.empty']
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
  not_measurable' w h := by
    rw [E.not_measurable' h]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
  m_iUnion' := E.m_iUnion'
