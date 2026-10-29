module

public import Mathlib
public import SpectralThm.RieszMarkovKakutani.Complex
public import SpectralThm.ProjectionValuedMeasure.Integral
public import SpectralThm.ComplexMeasure.Operations
public import SpectralThm.ComplexMeasure.Conj

/-!
# The spectral theorem for normal operators

Let `a` be a normal operator on a complex Hilbert space `H`. For `x y : H`, the functional
`f ↦ ⟪x, f(a) y⟫` on `C(σ(a), ℂ)` is bounded, so by the Riesz–Markov–Kakutani theorem it is
integration against a complex measure `E_{x,y}` on the spectrum `σ(a)`. These measures are
sesquilinear in `(x, y)`, and `E(w)` with `⟪x, E(w) y⟫ = E_{x,y}(w)` defines the spectral measure of
`a`, a projection-valued measure on `σ(a)` with `∫ f dE = f(a)` for continuous `f`
(Rudin, *Functional Analysis*, 12.22–12.23).

## Main definitions

* `IsStarNormal.cfcInnerFunctional`: the functional `f ↦ ⟪x, f(a) y⟫` on `C₀(σ(a), ℂ)`.
* `IsStarNormal.cfcMeasure`: the complex measure `E_{x,y}` representing it.
* `IsStarNormal.spectralMeasure`: the spectral measure of `a`, a projection-valued measure on
  `σ(a)`.

## Main results

* `IsStarNormal.integral_cfcMeasure`: `∫ f dE_{x,y} = ⟪x, f(a) y⟫` for continuous `f`.
* `IsStarNormal.eq_cfcMeasure`: uniqueness of `E_{x,y}`.
* `IsStarNormal.variation_cfcMeasure_univ_le`: `|E_{x,y}|(σ(a)) ≤ ‖x‖ ‖y‖`.
* `IsStarNormal.inner_spectralMeasure_apply`: `⟪x, E(w) y⟫ = E_{x,y}(w)`.
* `IsStarNormal.integral_spectralMeasure_toLp`: `∫ f dE = f(a)` for continuous `f`
  (Rudin 12.22 (a)).
* `IsStarNormal.integral_spectralMeasure_id`: the spectral decomposition `a = ∫ z dE(z)` (12.23).
* `IsStarNormal.eq_spectralMeasure`: uniqueness of the spectral measure (12.22 (a)).
* `IsStarNormal.spectralMeasure_ne_zero`: `E(w) ≠ 0` for nonempty open `w` (12.22 (d)).
* `IsStarNormal.forall_commute_spectralMeasure_iff`: `S` commutes with every `E(w)` iff it commutes
  with `a` and `a⋆` (12.22 (e)).

The general results of 12.21 (the integral is an isometric `*`-homomorphism of `L^∞(E)` with closed
commutative range) are in `SpectralThm/ProjectionValuedMeasure/Integral.lean`.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap ZeroAtInftyContinuousMap ZeroAtInfty
open scoped InnerProductSpace MeasureTheory.ComplexMeasure ENNReal

noncomputable section

/-- A continuous function on a compact space is integrable against every complex measure. -/
lemma MeasureTheory.ComplexMeasure.integrable_continuousMap {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : ComplexMeasure X)
    (f : C(X, ℂ)) : μ.Integrable f :=
  (BoundedContinuousFunction.mkOfCompact f).integrable _

namespace IsStarNormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsStarNormal a)

/-! ### The complex measures `E_{x,y}` -/

/-- The functional `f ↦ ⟪x, f(a) y⟫` on `C₀(σ(a), ℂ)` (which is `C(σ(a), ℂ)`, as `σ(a)` is
compact). -/
noncomputable def cfcInnerFunctional (x y : H) : C₀(spectrum ℂ a, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun f := ⟪x, cfcHom ha ((ContinuousMap.liftZeroAtInftyCLE (R := ℂ)).symm f) y⟫_ℂ
      map_add' f g := by simp only [map_add, _root_.add_apply, inner_add_right]
      map_smul' c f := by
        simp only [map_smul, _root_.smul_apply, inner_smul_right, RingHom.id_apply,
          smul_eq_mul] }
    (‖x‖ * ‖y‖) fun f ↦ calc
      ‖⟪x, cfcHom ha ((ContinuousMap.liftZeroAtInftyCLE (R := ℂ)).symm f) y⟫_ℂ‖
        ≤ ‖x‖ * (‖cfcHom ha ((ContinuousMap.liftZeroAtInftyCLE (R := ℂ)).symm f)‖ * ‖y‖) :=
          (norm_inner_le_norm _ _).trans (by gcongr; exact le_opNorm _ _)
      _ = ‖x‖ * ‖y‖ * ‖f‖ := by
        rw [norm_cfcHom a]
        change ‖x‖ * (‖f‖ * ‖y‖) = _
        ring

lemma cfcInnerFunctional_apply (x y : H) (f : C₀(spectrum ℂ a, ℂ)) :
    ha.cfcInnerFunctional x y f = ⟪x, cfcHom ha (f : C(spectrum ℂ a, ℂ)) y⟫_ℂ := rfl

lemma norm_cfcInnerFunctional_le (x y : H) : ‖ha.cfcInnerFunctional x y‖ ≤ ‖x‖ * ‖y‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The complex measure `E_{x,y}` on `σ(a)` representing `f ↦ ⟪x, f(a) y⟫` (Riesz–Markov–Kakutani,
`integral_cfcMeasure`). -/
noncomputable def cfcMeasure (x y : H) : ComplexMeasure (spectrum ℂ a) :=
  ComplexRMK.rieszMeasure (ha.cfcInnerFunctional x y)

/-- `∫ f dE_{x,y} = ⟪x, f(a) y⟫` for continuous `f`. -/
lemma integral_cfcMeasure (x y : H) (f : C(spectrum ℂ a, ℂ)) :
    ∫ᶜ z, f z ∂(ha.cfcMeasure x y) = ⟪x, cfcHom ha f y⟫_ℂ :=
  (ComplexRMK.integral_rieszMeasure _ (ContinuousMap.liftZeroAtInftyCLE (R := ℂ) f)).symm

/-- `E_{x,y}` is the only complex measure representing `f ↦ ⟪x, f(a) y⟫`. -/
lemma eq_cfcMeasure {x y : H} {μ : ComplexMeasure (spectrum ℂ a)}
    (h : ∀ f : C(spectrum ℂ a, ℂ), ∫ᶜ z, f z ∂μ = ⟪x, cfcHom ha f y⟫_ℂ) :
    μ = ha.cfcMeasure x y :=
  ComplexRMK.rieszMeasure_unique (ha.cfcInnerFunctional x y) (fun f ↦ h f)
    (fun f ↦ (ComplexRMK.integral_rieszMeasure _ f).symm)

/-- `|∫ f dE_{x,y}| ≤ ‖x‖ ‖y‖ ‖f‖` for continuous `f`. -/
lemma norm_integral_cfcMeasure_le (x y : H) (f : C(spectrum ℂ a, ℂ)) :
    ‖∫ᶜ z, f z ∂(ha.cfcMeasure x y)‖ ≤ ‖x‖ * ‖y‖ * ‖f‖ := by
  rw [ha.integral_cfcMeasure]
  calc ‖⟪x, cfcHom ha f y⟫_ℂ‖ ≤ ‖x‖ * (‖cfcHom ha f‖ * ‖y‖) :=
        (norm_inner_le_norm _ _).trans (by gcongr; exact le_opNorm _ _)
    _ = ‖x‖ * ‖y‖ * ‖f‖ := by rw [norm_cfcHom a]; ring

/-- `|E_{x,y}|(σ(a)) ≤ ‖x‖ ‖y‖` (Rudin, *Real and Complex Analysis*, 6.19). -/
lemma variation_cfcMeasure_univ_le (x y : H) :
    (ha.cfcMeasure x y).variation Set.univ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [cfcMeasure, ← ComplexRMK.norm_eq_variation, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (ha.norm_cfcInnerFunctional_le x y)

/-- `|E_{x,y}(w)| ≤ ‖x‖ ‖y‖`. -/
lemma norm_cfcMeasure_apply_le (x y : H) (w : Set (spectrum ℂ a)) :
    ‖ha.cfcMeasure x y w‖ ≤ ‖x‖ * ‖y‖ := by
  refine (VectorMeasure.norm_measure_le_variation (measure_ne_top _ _)).trans ?_
  refine (ENNReal.toReal_mono (by finiteness) (measure_mono (Set.subset_univ w))).trans ?_
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  exact ha.variation_cfcMeasure_univ_le x y

lemma cfcMeasure_add_left (x x' y : H) :
    ha.cfcMeasure (x + x') y = ha.cfcMeasure x y + ha.cfcMeasure x' y :=
  (ha.eq_cfcMeasure fun f ↦ by
    rw [VectorMeasure.integral_add_vectorMeasure (ComplexMeasure.integrable_continuousMap _ f)
      (ComplexMeasure.integrable_continuousMap _ f), integral_cfcMeasure, integral_cfcMeasure,
      inner_add_left]).symm

lemma cfcMeasure_add_right (x y y' : H) :
    ha.cfcMeasure x (y + y') = ha.cfcMeasure x y + ha.cfcMeasure x y' :=
  (ha.eq_cfcMeasure fun f ↦ by
    rw [VectorMeasure.integral_add_vectorMeasure (ComplexMeasure.integrable_continuousMap _ f)
      (ComplexMeasure.integrable_continuousMap _ f), integral_cfcMeasure, integral_cfcMeasure,
      map_add, inner_add_right]).symm

lemma cfcMeasure_smul_left (c : ℂ) (x y : H) :
    ha.cfcMeasure (c • x) y = starRingEnd ℂ c • ha.cfcMeasure x y :=
  (ha.eq_cfcMeasure fun f ↦ by
    rw [ComplexMeasure.integral_smul_measure, integral_cfcMeasure, inner_smul_left]).symm

lemma cfcMeasure_smul_right (c : ℂ) (x y : H) :
    ha.cfcMeasure x (c • y) = c • ha.cfcMeasure x y :=
  (ha.eq_cfcMeasure fun f ↦ by
    rw [ComplexMeasure.integral_smul_measure, integral_cfcMeasure, map_smul,
      inner_smul_right]).symm

/-! ### The spectral measure -/

/-- For a set `w`, the bounded sesquilinear form `(x, y) ↦ E_{x,y}(w)`. -/
noncomputable def cfcMeasureForm (w : Set (spectrum ℂ a)) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y ↦ ha.cfcMeasure x y w)
      (fun x x' y ↦ by simp [cfcMeasure_add_left])
      (fun c x y ↦ by simp [cfcMeasure_smul_left])
      (fun x y y' ↦ by simp [cfcMeasure_add_right])
      (fun c x y ↦ by simp [cfcMeasure_smul_right]))
    1 fun x y ↦ (ha.norm_cfcMeasure_apply_le x y w).trans_eq (by rw [one_mul])

/-- The operator `E(w)` with `⟪x, E(w) y⟫ = E_{x,y}(w)` (`inner_spectralMeasureAux_apply`). -/
noncomputable def spectralMeasureAux (w : Set (spectrum ℂ a)) : H →L[ℂ] H :=
  adjoint (InnerProductSpace.continuousLinearMapOfBilin (ha.cfcMeasureForm w))

lemma inner_spectralMeasureAux_apply (w : Set (spectrum ℂ a)) (x y : H) :
    ⟪x, ha.spectralMeasureAux w y⟫_ℂ = ha.cfcMeasure x y w := by
  rw [spectralMeasureAux, adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

lemma spectralMeasureAux_eq_zero {w : Set (spectrum ℂ a)}
    (h : ∀ x y, ha.cfcMeasure x y w = 0) : ha.spectralMeasureAux w = 0 :=
  ext fun y ↦ ext_inner_left ℂ fun x ↦ by simp [inner_spectralMeasureAux_apply, h]

/-- `E_{y,x} = conj E_{x,y}`. -/
lemma cfcMeasure_swap (x y : H) : ha.cfcMeasure y x = (ha.cfcMeasure x y).conj :=
  (ha.eq_cfcMeasure fun f ↦ by
    rw [ComplexMeasure.integral_conj]
    change starRingEnd ℂ (∫ᶜ z, (star f) z ∂(ha.cfcMeasure x y)) = _
    rw [integral_cfcMeasure, inner_conj_symm, map_star, star_eq_adjoint, adjoint_inner_left]).symm

/-- For continuous `f`, the measure `w ↦ ∫_w f dE_{x,y}` is `E_{f̄(a) x, y}`. -/
lemma withDensity_cfcMeasure (f : C(spectrum ℂ a, ℂ)) (x y : H) :
    (ha.cfcMeasure x y).withDensity f (ContinuousLinearMap.mul ℝ ℂ) =
      ha.cfcMeasure (cfcHom ha (star f) x) y :=
  ha.eq_cfcMeasure fun g ↦ by
    have hf := ComplexMeasure.integrable_continuousMap (ha.cfcMeasure x y) f
    rw [ComplexMeasure.integral_withDensity hf (ComplexMeasure.integrable_withDensity_of_bound hf
      g.continuous.aestronglyMeasurable ‖g‖ (ae_of_all _ g.norm_coe_le_norm))]
    change ∫ᶜ z, (g * f) z ∂(ha.cfcMeasure x y) = _
    rw [integral_cfcMeasure, map_star, star_eq_adjoint, adjoint_inner_left, ← mul_apply_eq_comp,
      ← map_mul, mul_comm]

/-- `w ↦ ⟪x, E(w) E(w') y⟫` is the restriction of `E_{x,y}` to `w'`. -/
lemma cfcMeasure_spectralMeasureAux (w' : Set (spectrum ℂ a)) (x y : H) :
    ha.cfcMeasure x (ha.spectralMeasureAux w' y) = (ha.cfcMeasure x y).restrict w' :=
  (ha.eq_cfcMeasure fun f ↦ by
    rw [← adjoint_inner_left, inner_spectralMeasureAux_apply, ← star_eq_adjoint, ← map_star,
      ← withDensity_cfcMeasure, VectorMeasure.withDensity_apply
        (ComplexMeasure.integrable_continuousMap _ f)]).symm

lemma spectralMeasureAux_inter {w₁ w₂ : Set (spectrum ℂ a)} (h₁ : MeasurableSet w₁)
    (h₂ : MeasurableSet w₂) :
    ha.spectralMeasureAux (w₁ ∩ w₂) = ha.spectralMeasureAux w₁ * ha.spectralMeasureAux w₂ :=
  ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ by
    rw [mul_apply_eq_comp, inner_spectralMeasureAux_apply, inner_spectralMeasureAux_apply,
      cfcMeasure_spectralMeasureAux, VectorMeasure.restrict_apply _ h₂ h₁]

lemma isSelfAdjoint_spectralMeasureAux (w : Set (spectrum ℂ a)) :
    IsSelfAdjoint (ha.spectralMeasureAux w) := by
  refine ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
  rw [star_eq_adjoint, adjoint_inner_right, ← inner_conj_symm, inner_spectralMeasureAux_apply,
    inner_spectralMeasureAux_apply, cfcMeasure_swap, ComplexMeasure.conj_apply,
    starRingEnd_self_apply]

lemma isStarProjection_spectralMeasureAux (w : Set (spectrum ℂ a)) :
    IsStarProjection (ha.spectralMeasureAux w) := by
  by_cases hw : MeasurableSet w
  · refine ⟨?_, ha.isSelfAdjoint_spectralMeasureAux w⟩
    rw [IsIdempotentElem, ← ha.spectralMeasureAux_inter hw hw, Set.inter_self]
  · rw [ha.spectralMeasureAux_eq_zero fun x y ↦ VectorMeasure.not_measurable _ hw]
    exact IsStarProjection.zero _

/-- The spectral measure of a normal operator `a`: the projection-valued measure `E` on `σ(a)` with
`⟪x, E(w) y⟫ = E_{x,y}(w)` (Rudin, *Functional Analysis*, 12.22). -/
noncomputable def spectralMeasure : ProjectionValuedMeasure (spectrum ℂ a) H where
  measureOf' w := ContinuousLinearMapWOT.ofCLM (ha.spectralMeasureAux w)
  empty' := by
    rw [ha.spectralMeasureAux_eq_zero fun x y ↦ VectorMeasure.empty _]
    rfl
  not_measurable' w hw := by
    rw [ha.spectralMeasureAux_eq_zero fun x y ↦ VectorMeasure.not_measurable _ hw]
    rfl
  m_iUnion' w hw hd := by
    refine ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.2 fun x y ↦ ?_
    have h : (fun s : Finset ℕ ↦ ⟪y, (∑ i ∈ s, ContinuousLinearMapWOT.ofCLM
        (ha.spectralMeasureAux (w i))) x⟫_ℂ) = fun s ↦ ∑ i ∈ s, ha.cfcMeasure y x (w i) := by
      funext s
      change ⟪y, (ContinuousLinearMapWOT.addEquiv (∑ i ∈ s, _)) x⟫_ℂ = _
      rw [map_sum, sum_apply, inner_sum]
      exact Finset.sum_congr rfl fun i _ ↦ ha.inner_spectralMeasureAux_apply _ y x
    rw [h, show ⟪y, ContinuousLinearMapWOT.ofCLM (ha.spectralMeasureAux (⋃ i, w i)) x⟫_ℂ =
      ha.cfcMeasure y x (⋃ i, w i) from ha.inner_spectralMeasureAux_apply _ y x]
    exact (ha.cfcMeasure y x).m_iUnion hw hd
  isStarProjection' := ha.isStarProjection_spectralMeasureAux
  measureOf_inter' w₁ w₂ h₁ h₂ := by
    rw [ha.spectralMeasureAux_inter h₁ h₂]
    rfl
  measureOf_univ' := by
    refine ContinuousLinearMapWOT.toCLM_injective (ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_)
    change ⟪x, ha.spectralMeasureAux _ y⟫_ℂ = ⟪x, y⟫_ℂ
    have h := ha.integral_cfcMeasure x y 1
    simp only [ContinuousMap.one_apply] at h
    rw [VectorMeasure.integral_const] at h
    simpa [inner_spectralMeasureAux_apply] using h

/-! ### The spectral measure and the continuous functional calculus -/

@[simp]
lemma inner_spectralMeasure_apply (w : Set (spectrum ℂ a)) (x y : H) :
    ⟪x, ha.spectralMeasure w y⟫_ℂ = ha.cfcMeasure x y w :=
  ha.inner_spectralMeasureAux_apply w x y

/-- The complex measures `E_{x,y}` of the spectral measure are the measures `cfcMeasure x y`. -/
@[simp]
lemma toComplexMeasure_spectralMeasure (x y : H) :
    ha.spectralMeasure.toComplexMeasure x y = ha.cfcMeasure x y :=
  VectorMeasure.ext fun w _ ↦ by simp

end IsStarNormal

namespace ProjectionValuedMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A continuous function on a compact space as an element of `L^∞(E)`. -/
lemma memLp_continuousMap (E : ProjectionValuedMeasure X H) (f : C(X, ℂ)) :
    MemLp f ∞ E.measure :=
  (BoundedContinuousFunction.mkOfCompact f).memLp_top

/-- `⟪x, (∫ f dE) y⟫ = ∫ f dE_{x,y}` for continuous `f`. -/
lemma inner_integral_toLp_continuousMap (E : ProjectionValuedMeasure X H) (f : C(X, ℂ))
    (x y : H) :
    ⟪x, E.integral ((E.memLp_continuousMap f).toLp f) y⟫_ℂ =
      ∫ᶜ z, f z ∂(E.toComplexMeasure x y) := by
  rw [E.inner_integral]
  exact VectorMeasure.integral_congr_ae
    ((E.variation_toComplexMeasure_absolutelyContinuous x y).ae_le (MemLp.coeFn_toLp _))

end ProjectionValuedMeasure

namespace IsStarNormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsStarNormal a)

/-- The integral against the spectral measure extends the continuous functional calculus:
`∫ f dE = f(a)` for continuous `f` (Rudin 12.22 (a)). -/
theorem integral_spectralMeasure_toLp (f : C(spectrum ℂ a, ℂ)) :
    ha.spectralMeasure.integral ((ha.spectralMeasure.memLp_continuousMap f).toLp f) = cfcHom ha f :=
  ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ by
    rw [ProjectionValuedMeasure.inner_integral_toLp_continuousMap, toComplexMeasure_spectralMeasure,
      integral_cfcMeasure]

/-- The spectral decomposition `a = ∫ z dE(z)` (Rudin 12.23). -/
theorem integral_spectralMeasure_id :
    ha.spectralMeasure.integral ((ha.spectralMeasure.memLp_continuousMap
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))).toLp _) = a := by
  rw [integral_spectralMeasure_toLp, cfcHom_id]

/-- The spectral measure is the only projection-valued measure on `σ(a)` whose integral extends the
continuous functional calculus (Rudin 12.22 (a)). -/
theorem eq_spectralMeasure {E : ProjectionValuedMeasure (spectrum ℂ a) H}
    (h : ∀ f : C(spectrum ℂ a, ℂ), E.integral ((E.memLp_continuousMap f).toLp f) = cfcHom ha f) :
    E = ha.spectralMeasure := by
  have hE (x y : H) : E.toComplexMeasure x y = ha.cfcMeasure x y :=
    ha.eq_cfcMeasure fun f ↦ by rw [← E.inner_integral_toLp_continuousMap, h]
  refine DFunLike.ext _ _ fun w ↦ ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
  rw [inner_spectralMeasure_apply, ← hE, ProjectionValuedMeasure.toComplexMeasure_apply]


/-- An operator commutes with every `E(w)` iff it commutes with `a` and `a⋆`
(Rudin 12.22 (e)). -/
theorem forall_commute_spectralMeasure_iff {S : H →L[ℂ] H} :
    (∀ w, Commute S (ha.spectralMeasure w)) ↔ Commute S a ∧ Commute S (star a) := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ w ↦ ?_⟩
  · have hS := ha.spectralMeasure.forall_commute_integral_iff.2 h
    have hid := hS ((ha.spectralMeasure.memLp_continuousMap
      ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))).toLp _)
    have hstar := hS ((ha.spectralMeasure.memLp_continuousMap
      (star ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)))).toLp _)
    rw [integral_spectralMeasure_id] at hid
    rw [integral_spectralMeasure_toLp, map_star, cfcHom_id] at hstar
    exact ⟨hid, hstar⟩
  · have hμ (x y : H) : ha.cfcMeasure x (S y) = ha.cfcMeasure (adjoint S x) y :=
      (ha.eq_cfcMeasure fun f ↦ by
        rw [integral_cfcMeasure, adjoint_inner_left, ← mul_apply_eq_comp,
          ← (Commute.cfcHom ha h₁.symm h₂.symm f).eq, mul_apply_eq_comp]).symm
    refine ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← adjoint_inner_left, inner_spectralMeasure_apply,
      inner_spectralMeasure_apply, hμ]

/-- `E(w) ≠ 0` for every nonempty open `w ⊆ σ(a)` (Rudin 12.22 (d)). -/
theorem spectralMeasure_ne_zero {w : Set (spectrum ℂ a)} (hw : IsOpen w) (hne : w.Nonempty) :
    ha.spectralMeasure w ≠ 0 := by
  intro h0
  obtain ⟨z, hz⟩ := hne
  obtain ⟨f, hfw, hfz, -⟩ := exists_continuous_zero_one_of_isClosed hw.isClosed_compl
    isClosed_singleton (Set.disjoint_singleton_right.2 (not_not.2 hz))
  let g : C(spectrum ℂ a, ℂ) := ⟨fun t ↦ (f t : ℂ), by fun_prop⟩
  have hg0 : (ha.spectralMeasure.memLp_continuousMap g).toLp g = 0 := by
    have hnull : ha.spectralMeasure.measure w = 0 :=
      (ha.spectralMeasure.measure_eq_zero_iff hw.measurableSet).2 h0
    refine Lp.ext ((MemLp.coeFn_toLp _).trans ?_ |>.trans (Lp.coeFn_zero _ _ _).symm)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with t ht
    simp [g, hfw ht]
  have h := ha.integral_spectralMeasure_toLp g
  rw [hg0, map_zero] at h
  have hn := norm_cfcHom a g
  rw [← h, norm_zero] at hn
  have hgz : g z = 1 := by simp [g, hfz (Set.mem_singleton z)]
  have := g.norm_coe_le_norm z
  rw [hgz, norm_one, ← hn] at this
  norm_num at this

end IsStarNormal
