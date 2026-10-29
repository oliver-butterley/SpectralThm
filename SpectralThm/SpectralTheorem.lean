module

public import Mathlib
public import SpectralThm.RieszMarkovKakutani.Complex
public import SpectralThm.ProjectionValuedMeasure.Integral
public import SpectralThm.ComplexMeasure.Operations

/-!
# The Spectral Theorem

-/

@[expose] public section

open InnerProductSpace ContinuousLinearMap ZeroAtInfty ZeroAtInftyContinuousMap MeasureTheory
open scoped MeasureTheory.ComplexMeasure

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsStarNormal a)

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
    := ((cfcHom ha : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H).toLinearMap).mkContinuous 1
        ( by simp only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul];
              exact fun f => le_of_eq (norm_cfcHom a f))

/-- The same map `f => f(a)` as a continuous algebra homomorphism.
-/
def cfcCAH : C((spectrum ℂ a), ℂ) →A[ℂ] H →L[ℂ] H
    := ContinuousAlgHom.mk (cfcHom ha : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H).toAlgHom
        (by apply @continuous_of_linear_of_bound _ _ _ _ _ _ _ _ _ (cfcHom ha).toAlgHom.map_add'
              (cfcHom ha).toLinearMap.map_smul' 1
            simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
              AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
              MonoidHom.coe_ofClass, StarAlgHom.coe_toAlgHom, one_mul]
            exact fun f => le_of_eq (norm_cfcHom a f))

@[simp]
lemma cfcCLM_apply (f : C((spectrum ℂ a), ℂ)) : cfcCLM ha f = cfcHom ha f := rfl

/-- The composition of the linear functional and the continuous functional,
`f => ⟪x, f(a) y⟫_ℂ` as a continuous linear functional. -/
def cfc_toLinearFunctional (x y : H) : C((spectrum ℂ a), ℂ) →L[ℂ] ℂ
    := compSL C(spectrum ℂ a, ℂ) _ _ _ _ (toLinearFunctional x y) (cfcCLM ha)

@[simp]
lemma cfc_toLinearFunctional_apply (f : C((spectrum ℂ a), ℂ)) (x y : H) :
    cfc_toLinearFunctional ha x y f = ⟪x, (cfcHom ha f y)⟫_ℂ := rfl

/-- For each pair `x y : H`, the linear map `f => ⟪x, f(a) y⟫_ℂ`has norm `‖x‖ * ‖y‖`.
This follows from the bound `toLinearFunctional_bounded` and the fact that
`f => f(a)` is an isometry, `norm_cfcHom`. -/
lemma cfc_toLinearFunctional_bound (x y : H) : ‖cfc_toLinearFunctional ha x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro f
    simp only [cfc_toLinearFunctional_apply]
    calc
      ‖⟪x, ((cfcHom ha) f) y⟫_ℂ‖
        ≤ ‖x‖ * ‖((cfcHom ha) f) y‖ := norm_inner_le_norm x
          (((cfcHom ha) f) y)
      _ ≤ ‖x‖ * (‖((cfcHom ha) f)‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (le_opNorm ((cfcHom ha) f) y)
          (norm_nonneg x)
      _ = ‖x‖ * ‖y‖ * ‖((cfcHom ha) f)‖ := by ring
      _ = ‖x‖ * ‖y‖ * ‖f‖ := by rw [norm_cfcHom a f]

/-- The functional `f ↦ ⟪x, f(a) y⟫` on `C₀(σ(a), ℂ)` (which is `C(σ(a), ℂ)` since `σ(a)` is
compact). -/
noncomputable def cfcInnerFunctional (x y : H) : C₀(spectrum ℂ a, ℂ) →L[ℂ] ℂ :=
  (cfc_toLinearFunctional ha x y).comp
    (ContinuousMap.liftZeroAtInftyCLE (R := ℂ)).symm.toContinuousLinearMap

lemma cfcInnerFunctional_apply (x y : H) (f : C₀(spectrum ℂ a, ℂ)) :
    cfcInnerFunctional ha x y f = ⟪x, cfcHom ha (f : C(spectrum ℂ a, ℂ)) y⟫_ℂ := rfl

lemma norm_cfcInnerFunctional_le (x y : H) : ‖cfcInnerFunctional ha x y‖ ≤ ‖x‖ * ‖y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦
    ((cfc_toLinearFunctional ha x y).le_opNorm _).trans <| by
      gcongr
      · exact cfc_toLinearFunctional_bound ha x y
      · exact le_of_eq rfl

/-- For each pair `x y : H`, the complex measure `E_{x,y}` on `σ(a)` representing the functional
`f ↦ ⟪x, f(a) y⟫` by the Riesz–Markov–Kakutani theorem (`integral_cfc_toComplexMeasure`). -/
noncomputable def cfc_toComplexMeasure (x y : H) : ComplexMeasure (spectrum ℂ a) :=
  ComplexRMK.rieszMeasure (cfcInnerFunctional ha x y)

/-- `∫ f dE_{x,y} = ⟪x, f(a) y⟫` for continuous `f`. -/
lemma integral_cfc_toComplexMeasure (x y : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ᶜ z, f z ∂(cfc_toComplexMeasure ha x y) = ⟪x, cfcHom ha f y⟫_ℂ :=
  (ComplexRMK.integral_rieszMeasure _ (ContinuousMap.liftZeroAtInftyCLE (R := ℂ) f)).symm

/-- `E_{x,y}` is the only complex measure representing `f ↦ ⟪x, f(a) y⟫`. -/
lemma eq_cfc_toComplexMeasure {x y : H} {μ : ComplexMeasure (spectrum ℂ a)}
    (h : ∀ f : C(spectrum ℂ a, ℂ), ∫ᶜ z, f z ∂μ = ⟪x, cfcHom ha f y⟫_ℂ) :
    μ = cfc_toComplexMeasure ha x y :=
  ComplexRMK.rieszMeasure_unique (cfcInnerFunctional ha x y) (fun f ↦ h f)
    (fun f ↦ (ComplexRMK.integral_rieszMeasure _ f).symm)

/-- The integral of `f` against `E_{a, x,y}` is bounded by `‖x‖ * ‖y‖ * ‖f‖`. -/
lemma cfc_toComplexMeasure_bounded (x y : H) (f : C((spectrum ℂ a), ℂ)) :
    ‖∫ᶜ z, f z ∂(cfc_toComplexMeasure ha x y)‖ ≤ ‖x‖ * ‖y‖ * ‖f‖ := by
  rw [integral_cfc_toComplexMeasure]
  exact ((cfc_toLinearFunctional ha x y).le_opNorm f).trans
    (by gcongr; exact cfc_toLinearFunctional_bound ha x y)

/-- The complex measure `E_{a, x,y}` has total variation at most `‖x‖ * ‖y‖` (Rudin, *Real and
Complex Analysis*, 6.19 (2), with `norm_cfcInnerFunctional_le`). -/
lemma cfc_variation_toComplexMeasure_bounded (x y : H) :
    (cfc_toComplexMeasure ha x y).variation Set.univ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [cfc_toComplexMeasure, ← ComplexRMK.norm_eq_variation, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_cfcInnerFunctional_le ha x y)

/-- A continuous function on `σ(a)` is integrable against every complex measure. -/
lemma integrable_of_continuous (μ : ComplexMeasure (spectrum ℂ a)) (f : C(spectrum ℂ a, ℂ)) :
    μ.Integrable f :=
  (BoundedContinuousFunction.mkOfCompact f).integrable _

lemma cfc_toComplexMeasure_add_left (x x' y : H) :
    cfc_toComplexMeasure ha (x + x') y =
      cfc_toComplexMeasure ha x y + cfc_toComplexMeasure ha x' y :=
  (eq_cfc_toComplexMeasure ha fun f ↦ by
    rw [VectorMeasure.integral_add_vectorMeasure (integrable_of_continuous _ f)
      (integrable_of_continuous _ f), integral_cfc_toComplexMeasure, integral_cfc_toComplexMeasure,
      inner_add_left]).symm

lemma cfc_toComplexMeasure_add_right (x y y' : H) :
    cfc_toComplexMeasure ha x (y + y') =
      cfc_toComplexMeasure ha x y + cfc_toComplexMeasure ha x y' :=
  (eq_cfc_toComplexMeasure ha fun f ↦ by
    rw [VectorMeasure.integral_add_vectorMeasure (integrable_of_continuous _ f)
      (integrable_of_continuous _ f), integral_cfc_toComplexMeasure, integral_cfc_toComplexMeasure,
      map_add, inner_add_right]).symm

lemma cfc_toComplexMeasure_smul_left (c : ℂ) (x y : H) :
    cfc_toComplexMeasure ha (c • x) y = starRingEnd ℂ c • cfc_toComplexMeasure ha x y :=
  (eq_cfc_toComplexMeasure ha fun f ↦ by
    rw [ComplexMeasure.integral_smul_measure, integral_cfc_toComplexMeasure, inner_smul_left]).symm

lemma cfc_toComplexMeasure_smul_right (c : ℂ) (x y : H) :
    cfc_toComplexMeasure ha x (c • y) = c • cfc_toComplexMeasure ha x y :=
  (eq_cfc_toComplexMeasure ha fun f ↦ by
    rw [ComplexMeasure.integral_smul_measure, integral_cfc_toComplexMeasure, map_smul,
      inner_smul_right]).symm

/-- The integral of a Borel function `f` against `E_{a, x ,y}` is bounded by `‖x‖ * ‖y‖`.
It should follow from `ComplexMeasure.norm_integral_le_integral_norm` and
`cfc_variation_toComplexMeasure_bounded`. -/
lemma bfc_bounded (x y : H) {C : ℝ} {f : (spectrum ℂ a) → ℂ}  (hf_bounded : ∀ x, ‖f x‖ ≤ C)
    (hX : @Measurable _ _ (borel (spectrum ℂ a)) _ f) :
    ‖∫ᶜ z, f z ∂(cfc_toComplexMeasure ha x y)‖ ≤ ‖x‖ * ‖y‖ * C := by
  sorry

/-- The linear functional from bounded Borel functions `f` to `∫ f z ∂E_{a, x, y} z` as a bounded
linear functional (bounded by `‖x‖ * ‖y‖`). All the remaining properties should follow from
the definition and `bfc_bounded`. -/
def toBoundedBilin {C : ℝ} (f : (spectrum ℂ a) → ℂ)
  --(hf_bounded : ∀ x, ‖f x‖ ≤ C) (hf_measurable : @Measurable _ _ (borel (spectrum ℂ a)) _ f)
  : H →L⋆[ℂ] H →L[ℂ] ℂ where
  toFun x := {  toFun y := ∫ᶜ z, f z ∂(cfc_toComplexMeasure ha x y)
                map_add' := sorry
                map_smul' := sorry
                cont := sorry }
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

/-- For each indicator function `χ s` of a set `s`, the bounded sesquilinear form
`x, y => ∫ f z ∂E_{a, x ,y} z` gives an orthogonal projection `E_{a} s`. The map `s => E_{a} s` is
the projection-valued measure (spectral measure) of `a`.
Probably `s` should be restricted to measurable set (otherwise defined to be `0`) to assure
`not_measurable'`.
cf. Rudin "Functional Analysis" Theorem 12.22, the definition (9) and later.
-/
def toProjectionValuedMeasure : ProjectionValuedMeasure (spectrum ℂ a) H where
  measureOf' s := ContinuousLinearMapWOT.ofCLM <| InnerProductSpace.continuousLinearMapOfBilin
    (@toBoundedBilin _ _ _ _ _ ha 1 (Set.indicator s (1 : (spectrum ℂ a) → ℂ)))
  empty' := by
    apply ContinuousLinearMapWOT.toCLM_injective
    ext
    simp [continuousLinearMapOfBilin, toBoundedBilin]
    rfl
  not_measurable' := sorry
  m_iUnion' := sorry
  isStarProjection' := sorry
  measureOf_inter' := sorry
  measureOf_univ' := sorry

/-- From the projection-valued measure `E_{a}` and for each `x y : H`, the map
`s => ⟪x, E_{a} s y⟫_ℂ` gives complex measure. The integraion of the identity map against it gives
back the expectation value `⟪x, a y⟫_ℂ`. Check that
`⟪x, cfcHom ha f y⟫_ℂ = ∫ᶜ z, f z ∂(toComplexMeasure (toProjectionValuedMeasure ha) x y)`
for step functions `f`, and infer that it holds for all Borel/continuous functions. Apply it to the
identity map.
cf. Rudin "Functional Analysis" Theorem 12.21, Theorem 12.22.
-/
theorem SpectralDecomposition (x y : H) :
    ⟪x, a y⟫_ℂ = ∫ᶜ z, (z : ℂ) ∂((toProjectionValuedMeasure ha).toComplexMeasure x y) := by
  sorry
