module

public import Mathlib
-- public import SpectralThm.WStarAlgebra.BorelFunctionalCalculus

/-!
# Resoltuions of the identity



-/

@[expose] public section

open scoped Function InnerProductSpace
open MeasureTheory BigOperators ENNReal Bornology

variable (α : Type*) [MeasurableSpace α]

variable {H: Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section BoundedMeasurableMap

open Filter

structure BoundedMeasurableMap (α : Type*) [MeasurableSpace α] (H : Type*)
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H] where
  toFun : α → H
  measurable' : Measurable toFun
  bounded' : ∃ C, ∀ x, ‖toFun x‖ ≤ C

lemma BoundedMeasurableMap.exists_simpleFunc_forall_tendsTo (f : BoundedMeasurableMap α ℂ) :
    ∃ g : ℕ → SimpleFunc α ℂ, ∀ x : α, Filter.Tendsto (fun n => g n x) atTop (nhds (f.toFun x)) := by
  sorry

lemma BoundedMeasurableMap.exists_simpleFunc_forall_finite_tendsTo_integral_sub
    (f : BoundedMeasurableMap α ℂ) :
    ∃ g : ℕ → SimpleFunc α ℂ, ∀ μ : Measure α, IsFiniteMeasure μ →
    Filter.Tendsto (fun n => ∫ x, ‖g n x - f.toFun x‖ ∂ μ) atTop (nhds 0) := by
  sorry

end BoundedMeasurableMap

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
