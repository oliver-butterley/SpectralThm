import Mathlib
import SpectralThm.RieszMarkovKakutani.Complex
import SpectralThm.Resolutions
import SpectralThm.WStarAlgebra.BorelFunctionalCalculus

/-!
# The Spectral Theorem

-/

open InnerProductSpace ContinuousLinearMap ZeroAtInfty ZeroAtInftyContinuousMap MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)

variable (f : C((spectrum ℂ a), ℂ))

/-- For `x y : H`, consider `b => ⟪x, b y⟫_ℂ` as a bounded linear functional in `b`. -/
def toLinearFunctional (x y : H) : (H →L[ℂ] H) →L[ℂ] ℂ
    := compSL (H →L[ℂ] H) _ _ _ _ (innerSL ℂ x) (apply' H _ y)

@[simp]
lemma toLinearFunctional_apply (x y : H) {b : H →L[ℂ] H}:
    toLinearFunctional x y b = ⟪x, (b y)⟫_ℂ := rfl

/-- The linear functional `b => ⟪x, b y⟫_ℂ` is bounded by `‖x‖ * ‖y‖`. -/
lemma toLinearFunctional_bounded (x y : H) : ‖toLinearFunctional x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [toLinearFunctional]
  grw [ContinuousLinearMap.opNorm_le_bound]
  . positivity
  . intro a
    simp only [compSL_apply, coe_comp', innerSL_apply_coe, Function.comp_apply, apply_apply']
    grw [norm_inner_le_norm, ContinuousLinearMap.le_opNorm]
    group
    rfl

/-- Let `a` a normal bounded operator. By the continuous functional calculus, there is an injective
homomorphism from `C((spectrum ℂ a), ℂ)` to  `H →L[ℂ] H`, informally denoted by `f => f(a)`. This
definition just makes it a continuous linear functional. -/
def cfcContinuousHom {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) : C((spectrum ℂ a), ℂ) →L[ℂ] H →L[ℂ] H
    := ((cfcHom ha.isStarNormal : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H).toLinearMap).mkContinuous 1
        ( by simp only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul];
              exact fun f => le_of_eq (norm_cfcHom a f))

@[simp]
lemma cfcContinuousHom_apply {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) (f : C((spectrum ℂ a), ℂ)) :
  cfcContinuousHom ha f = cfcHom ha.isStarNormal f := rfl

/-- The composition of the linear functional and the continuous functional,
`f => ⟪x, f(a) y⟫_ℂ` as a continuous linear functional. -/
def cfc_toLinearFunctional (x y : H) : C((spectrum ℂ a), ℂ) →L[ℂ] ℂ
    := compSL C(spectrum ℂ a, ℂ) _ _ _ _ (toLinearFunctional x y) (cfcContinuousHom ha)

@[simp]
lemma cfc_toLinearFunctional_apply {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) (f : C((spectrum ℂ a), ℂ))
    (x y : H) : cfc_toLinearFunctional ha x y f = ⟪x, (cfcHom ha.isStarNormal f y)⟫_ℂ := rfl

/-- For each pair `x y : H`, one obtains a complex measure `E_{a, x ,y}` from the continuous linear
functional `f => ⟪x, f(a) y⟫_ℂ` by the Riesz-Markov-Kakutani theorem. -/
def cfc_toComplexMeasure (x y : H) := ComplexRMK.rieszMeasure (compSL C₀((spectrum ℂ a), ℂ)
  C((spectrum ℂ a), ℂ) ℂ _ _ (cfc_toLinearFunctional ha x y)
  (@ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInftyCLE
  (spectrum ℂ a) ℂ ℂ _ _ _ _ _ _).symm.toContinuousLinearMap)

/-- The complex measure `E_{a, x,y}` is bounded by `‖x‖ * ‖y‖`. -/
lemma cfc_toComplexMeasure_bounded (x y : H) (f : C((spectrum ℂ a), ℂ)) :
    ‖(cfc_toComplexMeasure ha x y).integral f‖ ≤ ‖x‖ * ‖y‖ * ‖f‖ := by
  sorry

/-- The total variation of `E_{a, x,y}` is bounded by `‖x‖ * ‖y‖`. -/
lemma cfc_variation_toComplexMeasure_bounded (x y : H) :
    (cfc_toComplexMeasure ha x y).variation Set.univ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  sorry

/-- The integral of a Borel function `f` against `E_{a, x ,y}` is bounded by `‖x‖ * ‖y‖`. -/
lemma bfc_bounded (x y : H) {C : ℝ} {f : (spectrum ℂ a) → ℂ}  (hf_bounded : ∀ x, ‖f x‖ ≤ C)
    (hX : @Measurable _ _ (borel (spectrum ℂ a)) _ f) :
    ‖(cfc_toComplexMeasure ha x y).integral f‖ ≤ ‖x‖ * ‖y‖ * C := by
  sorry

/-- The linear functional from bounded Borel functions `f` to `∫ f z ∂E_{a, x, y} z` as a bounded
linear functional (bounded by `‖x‖ * ‖y‖`). -/
def toBoundedBilin {C : ℝ} (f : (spectrum ℂ a) → ℂ)
  --(hf_bounded : ∀ x, ‖f x‖ ≤ C) (hf_measurable : @Measurable _ _ (borel (spectrum ℂ a)) _ f)
  : H →L⋆[ℂ] H →L[ℂ] ℂ where
  toFun x := {  toFun y := (cfc_toComplexMeasure ha x y).integral f
                map_add' := sorry
                map_smul' := sorry
                cont := sorry }
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

/-- For each indicator function `χ s` of a set `s`, the bounded sesquilinear form
`x, y => ∫ f z ∂E_{a, x ,y} z` gives an orthogonal projection `E_{a} s`. Define the map
`s => E_{a} s` as a resolution of identity`. -/
def toResolutionOfIdentity : ResolutionOfIdentity (spectrum ℂ a) H where
  measureOf' s := InnerProductSpace.continuousLinearMapOfBilin
    (@toBoundedBilin _ _ _ _ _ ha 1 (Set.indicator s (1 : (spectrum ℂ a) → ℂ)))
  isOrthogonalProjection' := sorry
  empty' := by
    ext
    simp [continuousLinearMapOfBilin, toBoundedBilin, cfc_toComplexMeasure, ComplexMeasure.integral]
    rfl
  not_measurable' := sorry
  m_Union' := sorry
  m_Inter' := sorry
  m_iUnion' := sorry

/-- From a resolution of identity `E_{a}` and for each `x y : H`, the map `s => ⟪x, E_{a} s y⟫_ℂ`
gives complex measure. The integraion of the identity map against it gives back the expectation
value `⟪x, a y⟫_ℂ`. -/
theorem SpectralDecomposition (x y : H) :
    ⟪x, a y⟫_ℂ = (toComplexMeasure (toResolutionOfIdentity ha) x y).integral
    (Function.Embedding.subtype (spectrum ℂ a)) := by
  sorry
