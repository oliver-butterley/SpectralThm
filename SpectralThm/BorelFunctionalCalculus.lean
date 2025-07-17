import Mathlib
import SpectralThm.Resolutions
import SpectralThm.WStarAlgebra.BorelFunctionalCalculus


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) (ha : IsSelfAdjoint a)


#check a.1
#synth ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint


variable (f : C(ℂ, ℂ))
-- #check cfcHom ha.isStarNormal f
