import Mathlib
import SpectralThm.Complex
import SpectralThm.Resolutions
import SpectralThm.WStarAlgebra.BorelFunctionalCalculus

open InnerProductSpace ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) (ha : IsSelfAdjoint a)

variable (f : C((spectrum ℂ a), ℂ))

#check (cfcHom ha.isStarNormal : C((spectrum ℂ a), ℂ) →⋆ₐ H →L[ℂ] H)
#check cfcHom ha.isStarNormal

def toLinearFunctional (x y : H) : (H →L[ℂ] H) →L[ℂ] ℂ
    := compSL (H →L[ℂ] H) _ _ _ _ (innerSL ℂ x) (apply' H _ y)

lemma toLinearFunctiona_bounded (x y : H) : ‖toLinearFunctional x y‖ ≤ ‖x‖ * ‖y‖ := by
  sorry


/- TODO
- `cfcHom` as continuous linear map
- compose it with `toLinearFunctional`, obtaining a complex linear functional on
`C((spectrum ℂ a), ℂ)`
- define `toComplexMeasure` using ComplexRMK
- define Borel functional calculus using `InnerProductSpace.continuousLinearMapOfBilin`

-/
