import Mathlib
import SpectralThm.Complex
import SpectralThm.Resolutions
import SpectralThm.WStarAlgebra.BorelFunctionalCalculus

open InnerProductSpace ContinuousLinearMap ZeroAtInfty ZeroAtInftyContinuousMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsSelfAdjoint a)

variable (f : C((spectrum ℂ a), ℂ))

def toLinearFunctional (x y : H) : (H →L[ℂ] H) →L[ℂ] ℂ
    := compSL (H →L[ℂ] H) _ _ _ _ (innerSL ℂ x) (apply' H _ y)

@[simp]
lemma toLinearFunctional_apply (x y : H) :
    toLinearFunctional x y a = ⟪x ,(a y)⟫_ℂ := rfl

lemma toLinearFunctional_bounded (x y : H) : ‖toLinearFunctional x y‖ ≤ ‖x‖ * ‖y‖ := by
  sorry

def cfcContinuousHom {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) : C((spectrum ℂ a), ℂ) →L[ℂ] H →L[ℂ] H
    := ((cfcHom ha.isStarNormal : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H).toLinearMap).mkContinuous 1
        ( by simp only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul];
              exact fun f => le_of_eq (norm_cfcHom a f))

@[simp]
lemma cfcContinuousHom_apply {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) (f : C((spectrum ℂ a), ℂ)) :
  cfcContinuousHom ha f = cfcHom ha.isStarNormal f := rfl

def cfc_toLinearFunctional (x y : H) : C((spectrum ℂ a), ℂ) →L[ℂ] ℂ
    := compSL C(spectrum ℂ a, ℂ) _ _ _ _ (toLinearFunctional x y) (cfcContinuousHom ha)

@[simp]
lemma cfc_toLinearFunctional_apply {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) (f : C((spectrum ℂ a), ℂ))
    (x y : H) : cfc_toLinearFunctional ha x y f = ⟪x, (cfcHom ha.isStarNormal f y)⟫_ℂ := rfl

def cfc_toComplexMeasure (x y : H) := ComplexRMK.rieszMeasure (compSL C₀((spectrum ℂ a), ℂ)
  C((spectrum ℂ a), ℂ) ℂ _ _ (cfc_toLinearFunctional ha x y)
  (@ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInftyCLE
  (spectrum ℂ a) ℂ ℂ _ _ _ _ _ _).symm.toContinuousLinearMap)

lemma cfc_toComplexMeasure_bounded (x y : H) (f : C((spectrum ℂ a), ℂ)) :
    ‖(cfc_toComplexMeasure ha x y).integral f‖ ≤ ‖x‖ * ‖y‖ * ‖f‖ := by
  sorry


/- TODO
- define Borel functional calculus using `InnerProductSpace.continuousLinearMapOfBilin`
- define a resolution of identity
-/
