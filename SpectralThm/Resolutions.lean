module

public import Mathlib
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
  coe_injective | ⟨_, _, _, _, _, _, _⟩, ⟨_, _, _, _, _, _, _⟩, rfl => rfl

end Def

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
  empty' := by
    rw [E.empty']
    simp only [zero_apply, inner_zero_right]
  not_measurable' w h := by
    rw [E.not_measurable' h]
    simp only [zero_apply, inner_zero_right]
  m_iUnion' := E.m_iUnion'

def toOuterMeasure (x : H) : OuterMeasure X where
  measureOf w := ENNReal.ofReal ‖E.measureOf' w x‖
  empty := by
    rw [E.empty']
    simp only [zero_apply, norm_zero, ofReal_zero]
  mono {w₁ w₂} h := by
    rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
    sorry
  iUnion_nat := sorry

noncomputable def toMeasure (x : H) : Measure X :=
  {
    toOuterMeasure := (E.toOuterMeasure x).trim
    m_iUnion {f} f_measurable f_disjoint := sorry
    trim_le := by
      rw [MeasureTheory.OuterMeasure.trim_trim]
  }

variable (E : ResolutionOfIdentity X H)

@[simp]
lemma ResolutionOfIdentity.apply (w: Set X): E w = E.measureOf' w := rfl

@[simp]
lemma toMeasure_apply (x : H) (w : Set X) : toMeasure E x w = (toOuterMeasure E x).trim w := rfl

@[simp]
lemma toOuterMeasure_apply (x : H) (w : Set X) : (toOuterMeasure E x) w = ENNReal.ofReal ‖E.measureOf' w x‖ := rfl

lemma ResolutionOfIdentity.zero_iff (w : Set X) (h : MeasurableSet w) : E w  = 0 ↔
    ∀ x, (toMeasure E x) w = 0 := by
  simp [MeasureTheory.OuterMeasure.trim_eq _ h, ContinuousLinearMap.ext_iff]

noncomputable def SumOuterMeasure {ι : Type*} (μ : ι → Measure X) : OuterMeasure X where
  measureOf w := ∑' i, μ i w
  empty := by
    simp only [measure_empty, tsum_zero]
  mono {w₁ w₂} h := Summable.tsum_le_tsum (fun i => (μ i).mono h) ENNReal.summable ENNReal.summable
  iUnion_nat w h := by
    rw [← Summable.tsum_comm' ENNReal.summable (fun i => ENNReal.summable)
      (fun i => ENNReal.summable)]
    apply Summable.tsum_le_tsum _ ENNReal.summable ENNReal.summable
    exact fun i => (μ i).iUnion_nat w h

noncomputable def SumMeasure {ι : Type*} (μ : ι → Measure X) : Measure X :=
  {
    toOuterMeasure := (SumOuterMeasure μ).trim
    m_iUnion {f} f_measurable f_disjoint := by
      rw [MeasureTheory.OuterMeasure.trim_eq _ (MeasurableSet.iUnion f_measurable)]
      have : ∑' i, (SumOuterMeasure μ).trim (f i) = ∑' i, (SumOuterMeasure μ) (f i) := by
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

noncomputable def ofUnitBall : {x : H // ‖x‖ ≤ 1} → Measure X := fun x => toMeasure E x

noncomputable def Linfty (E : ResolutionOfIdentity X H) := MeasureTheory.Lp ℂ ⊤ (SumMeasure (ofUnitBall E))

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
