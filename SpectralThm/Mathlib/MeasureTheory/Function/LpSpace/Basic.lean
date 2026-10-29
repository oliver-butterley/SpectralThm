/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux, Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import SpectralThm.Mathlib.MeasureTheory.Function.AEEqFun

/-!
# Complements on `Lp` spaces

## Main definitions

* Instances `StarAddMonoid` and `StarModule` on `Lp R p μ`.

## Main results

* `MeasureTheory.MemLp.toLp_star`: `MemLp.toLp` commutes with `star`.
* `MeasureTheory.Lp.ae_norm_le_norm`: an element of `Lp E ∞ μ` is bounded almost everywhere by its
  norm.
* `MeasureTheory.Lp.norm_le_of_ae_bound_top`: an almost everywhere bound on an element of
  `Lp E ∞ μ` bounds its norm.
* `MeasureTheory.Lp.exists_stronglyMeasurable_forall_norm_le_ae_eq`: every element of `Lp E ∞ μ`
  has a strongly measurable representative bounded *everywhere* by the norm of the class.
-/

@[expose] public section

open ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

section Star

variable {R : Type*} [NormedAddCommGroup R] [StarAddMonoid R] [NormedStarGroup R]

namespace Lp

noncomputable instance instStarAddMonoid : StarAddMonoid (Lp R p μ) where
  star_add f g := Subtype.ext <| star_add (R := α →ₘ[μ] R) f g

instance instStarModule {𝕜 : Type*} [NormedRing 𝕜] [Star 𝕜] [Module 𝕜 R] [IsBoundedSMul 𝕜 R]
    [StarModule 𝕜 R] :
    StarModule 𝕜 (Lp R p μ) where
  star_smul c f := Subtype.ext <| star_smul (A := α →ₘ[μ] R) c f

end Lp

theorem MemLp.toLp_star {f : α → R} (hf : MemLp f p μ) :
    hf.star.toLp (star f) = star (hf.toLp f) :=
  rfl

end Star

namespace Lp

variable {E : Type*} [NormedAddCommGroup E]

/-- An element of `Lp E ∞ μ` is bounded almost everywhere by its norm. -/
theorem ae_norm_le_norm (f : Lp E ∞ μ) : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f), ← Lp.enorm_def] at hx
  exact enorm_le_iff_norm_le.mp hx

/-- An almost everywhere bound on an element of `Lp E ∞ μ` bounds its norm. -/
theorem norm_le_of_ae_bound_top {f : Lp E ∞ μ} {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖f‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  exact toReal_le_of_le_ofReal hC (eLpNormEssSup_le_of_ae_bound hfC)

/-- Every element of `Lp E ∞ μ` has a strongly measurable representative which is bounded
everywhere by the norm of the class. -/
theorem exists_stronglyMeasurable_forall_norm_le_ae_eq (f : Lp E ∞ μ) :
    ∃ g : α → E, StronglyMeasurable g ∧ (∀ x, ‖g x‖ ≤ ‖f‖) ∧ f =ᵐ[μ] g := by
  have hf := Lp.stronglyMeasurable f
  have hs : MeasurableSet {x | ‖f x‖ ≤ ‖f‖} := measurableSet_le hf.norm.measurable measurable_const
  refine ⟨{x | ‖f x‖ ≤ ‖f‖}.indicator f, hf.indicator hs, fun x ↦ ?_, ?_⟩
  · by_cases hx : ‖f x‖ ≤ ‖f‖ <;> simp [hx]
  · filter_upwards [ae_norm_le_norm f] with x hx using (Set.indicator_of_mem hx _).symm

end Lp

end MeasureTheory
