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
  grw [ContinuousLinearMap.opNorm_le_bound]
  . positivity
  . intro a
    simp only [toLinearFunctional_apply]
    grw [norm_inner_le_norm, ContinuousLinearMap.le_opNorm]
    apply le_of_eq
    ring

/-- Let `a` a normal bounded operator. By the continuous functional calculus, there is an injective
homomorphism from `C((spectrum ℂ a), ℂ)` to  `H →L[ℂ] H`, informally denoted by `f => f(a)`. This
definition just makes it a continuous linear map.
cf. Rudin "Functional Analysis" Theorem 11.18, the proof of Theorem 12.23, first paragraph.
-/
def cfcCLM : C((spectrum ℂ a), ℂ) →L[ℂ] H →L[ℂ] H
    := ((cfcHom ha.isStarNormal : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H).toLinearMap).mkContinuous 1
        ( by simp only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul];
              exact fun f => le_of_eq (norm_cfcHom a f))

/-- The same map `f => f(a)` as a continuous algebra homomorphism.
-/
def cfcCAH : C((spectrum ℂ a), ℂ) →A[ℂ] H →L[ℂ] H
    := ContinuousAlgHom.mk (cfcHom ha.isStarNormal : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H).toAlgHom
        (by apply @continuous_of_linear_of_bound _ _ _ _ _ _ _ _ _ (cfcHom ha.isStarNormal).toAlgHom.map_add'
              (cfcHom ha.isStarNormal).toLinearMap.map_smul' 1
            simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
              AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
              MonoidHom.coe_coe, StarAlgHom.coe_toAlgHom, one_mul]
            exact fun f => le_of_eq (norm_cfcHom a f))

@[simp]
lemma cfcCLM_apply (f : C((spectrum ℂ a), ℂ)) : cfcCLM ha f = cfcHom ha.isStarNormal f := rfl

/-- The composition of the linear functional and the continuous functional,
`f => ⟪x, f(a) y⟫_ℂ` as a continuous linear functional. -/
def cfc_toLinearFunctional (x y : H) : C((spectrum ℂ a), ℂ) →L[ℂ] ℂ
    := compSL C(spectrum ℂ a, ℂ) _ _ _ _ (toLinearFunctional x y) (cfcCLM ha)

@[simp]
lemma cfc_toLinearFunctional_apply (f : C((spectrum ℂ a), ℂ)) (x y : H) :
    cfc_toLinearFunctional ha x y f = ⟪x, (cfcHom ha.isStarNormal f y)⟫_ℂ := rfl

/-- For each pair `x y : H`, the linear map `f => ⟪x, f(a) y⟫_ℂ`has norm `‖x‖ * ‖y‖`.
This follows from the bound `toLinearFunctional_bounded` and the fact that
`f => f(a)` is an isometry, `norm_cfcHom`. -/
lemma cfc_toLinearFunctional_bound (x y : H) : ‖cfc_toLinearFunctional ha x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro f
    simp only [cfc_toLinearFunctional_apply]
    calc
      ‖⟪x, ((cfcHom (IsSelfAdjoint.isStarNormal ha)) f) y⟫_ℂ‖
        ≤ ‖x‖ * ‖((cfcHom (IsSelfAdjoint.isStarNormal ha)) f) y‖ := norm_inner_le_norm x
          (((cfcHom (IsSelfAdjoint.isStarNormal ha)) f) y)
      _ ≤ ‖x‖ * (‖((cfcHom (IsSelfAdjoint.isStarNormal ha)) f)‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (le_opNorm ((cfcHom (IsSelfAdjoint.isStarNormal ha)) f) y)
          (norm_nonneg x)
      _ = ‖x‖ * ‖y‖ * ‖((cfcHom (IsSelfAdjoint.isStarNormal ha)) f)‖ := by ring
      _ = ‖x‖ * ‖y‖ * ‖f‖ := by rw [norm_cfcHom a f]

/-- For each pair `x y : H`, one obtains a complex measure `E_{a, x ,y}` from the continuous linear
functional `f => ⟪x, f(a) y⟫_ℂ` by the Riesz-Markov-Kakutani theorem.
cf. Rudin "Functiona Analysis" the proof of Theorem 12.22, above formula (5).
-/
def cfc_toComplexMeasure (x y : H) := ComplexRMK.rieszMeasure (compSL C₀((spectrum ℂ a), ℂ)
  C((spectrum ℂ a), ℂ) ℂ _ _ (cfc_toLinearFunctional ha x y)
  (@ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInftyCLE
  (spectrum ℂ a) ℂ ℂ _ _ _ _ _ _).symm.toContinuousLinearMap)

/-- The integral of `f` against `E_{a, x,y}` is bounded by `‖x‖ * ‖y‖ * ‖f‖`. -/
lemma cfc_toComplexMeasure_bounded (x y : H) (f : C((spectrum ℂ a), ℂ)) :
    ‖(cfc_toComplexMeasure ha x y).integral f‖ ≤ ‖x‖ * ‖y‖ * ‖f‖ := by
  sorry

/-- The complex measure `E_{a, x,y}` has the total variation bounded by `‖x‖ * ‖y‖`.
Rudin "Real and complex analysis" Theorem 6.19 (2), combined with the bound by
`cfc_toLinearFunctional_bound`.-/
lemma cfc_variation_toComplexMeasure_bounded (x y : H) :
    (cfc_toComplexMeasure ha x y).variation Set.univ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  sorry

/-- The integral of a Borel function `f` against `E_{a, x ,y}` is bounded by `‖x‖ * ‖y‖`.
We should have an analogue of `MeasureTheory.lintegral_le_const` for `ComplexMeasure.integral`.
-/
lemma bfc_bounded (x y : H) {C : ℝ} {f : (spectrum ℂ a) → ℂ}  (hf_bounded : ∀ x, ‖f x‖ ≤ C)
    (hX : @Measurable _ _ (borel (spectrum ℂ a)) _ f) :
    ‖(cfc_toComplexMeasure ha x y).integral f‖ ≤ ‖x‖ * ‖y‖ * C := by
  sorry

/-- The linear functional from bounded Borel functions `f` to `∫ f z ∂E_{a, x, y} z` as a bounded
linear functional (bounded by `‖x‖ * ‖y‖`). All the remaining properties should follow from
the definition and `bfc_bounded`. -/
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
`s => E_{a} s` as a resolution of identity`.
Probably `s` should be restricted to measurable set (otherwise defined to be `0`) to assure
`not_measurable'`.
cf. Rudin "Functional Analysis" Theorem 12.22, the definition (9) and later.
-/
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
value `⟪x, a y⟫_ℂ`. Check that
`⟪x, cfcHom ha f y⟫_ℂ = (toComplexMeasure (toResolutionOfIdentity ha) x y).integral f` for step
functions `f`, and infer that it holds for all Borel/continuous functions. Apply it to the identity
map.
cf. Rudin "Functional Analysis" Theorem 12.21, Theorem 12.22.
-/
theorem SpectralDecomposition (x y : H) :
    ⟪x, a y⟫_ℂ = (toComplexMeasure (toResolutionOfIdentity ha) x y).integral
    (Function.Embedding.subtype (spectrum ℂ a)) := by
  sorry
