/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.Holder
public import SpectralThm.Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The algebra `L^∞`

For a measure `μ` and a normed ring `R`, `Lp R ∞ μ` is a normed ring under pointwise (almost
everywhere) multiplication, a normed algebra over any normed field `𝕜` over which `R` is a normed
algebra, a star ring when `R` is, and a (commutative) C⋆-algebra when `R` is. No finiteness
assumption on `μ` is needed.

## Main definitions

* `MeasureTheory.Linfty.const : R →+ Lp R ∞ μ`: the constant functions in `L^∞`.
* Instances `Ring`, `CommRing`, `StarRing`, `NormedRing`, `NormedCommRing`, `NormedAlgebra`,
  `CStarRing`, `CStarAlgebra` and `CommCStarAlgebra` on `Lp R ∞ μ`.

## Main results

* `MeasureTheory.Linfty.coeFn_mul`, `MeasureTheory.Linfty.toLp_mul`: products are computed
  pointwise.
* `MeasureTheory.Linfty.coeFn_one`, `MeasureTheory.Linfty.algebraMap_eq_const`: the unit and the
  algebra map are given by constant functions.

## Implementation notes

The multiplication is the heterogeneous scalar multiplication
`Lp R ∞ μ → Lp R ∞ μ → Lp R ∞ μ` of `Mathlib.MeasureTheory.Function.Holder`.

Mathlib's `MeasureTheory.Lp.const` requires a finite measure; `MeasureTheory.Linfty.const` does
not. Mathlib PRs #29108 and #30030 (open) develop the same material and unify the two via a
`MemLp.Const` class.

## References

This file started on the `BFC` branch of `j-loreaux/LeanOA` (Jon Bannon, Jireh Loreaux).
-/

@[expose] public section

open ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

namespace Linfty

section NormedRing

variable {R : Type*} [NormedRing R]

/-! ### Multiplication -/

/-- Pointwise multiplication on `L^∞`, defined via the heterogeneous scalar multiplication
`Lp R ∞ μ → Lp R ∞ μ → Lp R ∞ μ`. -/
noncomputable instance instMul : Mul (Lp R ∞ μ) where
  mul f g := f • g

theorem coeFn_mul (f g : Lp R ∞ μ) : ⇑(f * g) =ᵐ[μ] ⇑f * g :=
  Lp.coeFn_lpSMul f g

theorem toLp_mul {f g : α → R} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    (hf.mul hg).toLp (f * g) = hf.toLp f * hg.toLp g :=
  Lp.ext <| (MemLp.coeFn_toLp _).trans <| by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, coeFn_mul (hf.toLp f) (hg.toLp g)]
      with x h₁ h₂ h₃
    simp [h₁, h₂, h₃]

/-! ### Constants -/

theorem _root_.MeasureTheory.const_mem_Linfty (c : R) :
    (AEEqFun.const α c : α →ₘ[μ] R) ∈ Lp R ∞ μ :=
  (memLp_top_const c).eLpNorm_mk_lt_top

/-- The constant functions as elements of `L^∞`. Unlike `Lp.const`, no finiteness assumption on
the measure is needed. -/
def const : R →+ Lp R ∞ μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Linfty c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem const_val (c : R) : (const c : Lp R ∞ μ).1 = AEEqFun.const α c :=
  rfl

theorem coeFn_const (c : R) : const (μ := μ) c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

noncomputable instance instOne : One (Lp R ∞ μ) where
  one := const 1

theorem one_def : (1 : Lp R ∞ μ) = const 1 :=
  rfl

theorem coeFn_one : ⇑(1 : Lp R ∞ μ) =ᵐ[μ] 1 :=
  coeFn_const 1

/-! ### The ring structure -/

noncomputable instance instRing : Ring (Lp R ∞ μ) where
  mul_assoc f g h := Lp.ext <| by
    filter_upwards [coeFn_mul (f * g) h, coeFn_mul f (g * h), coeFn_mul f g, coeFn_mul g h]
      with x h₁ h₂ h₃ h₄
    simp [h₁, h₂, h₃, h₄, mul_assoc]
  one_mul f := Lp.ext <| by
    filter_upwards [coeFn_mul 1 f, coeFn_one (R := R) (μ := μ)] with x h₁ h₂
    simp [h₁, h₂]
  mul_one f := Lp.ext <| by
    filter_upwards [coeFn_mul f 1, coeFn_one (R := R) (μ := μ)] with x h₁ h₂
    simp [h₁, h₂]
  zero_mul f := Lp.ext <| by
    filter_upwards [coeFn_mul 0 f, Lp.coeFn_zero R ∞ μ] with x h₁ h₂
    simp only [h₁, h₂, Pi.mul_apply, Pi.zero_apply, zero_mul]
  mul_zero f := Lp.ext <| by
    filter_upwards [coeFn_mul f 0, Lp.coeFn_zero R ∞ μ] with x h₁ h₂
    simp only [h₁, h₂, Pi.mul_apply, Pi.zero_apply, mul_zero]
  left_distrib f g h := Lp.ext <| by
    filter_upwards [coeFn_mul f (g + h), Lp.coeFn_add g h, Lp.coeFn_add (f * g) (f * h),
      coeFn_mul f g, coeFn_mul f h] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, h₄, h₅, Pi.add_apply, Pi.mul_apply, mul_add]
  right_distrib f g h := Lp.ext <| by
    filter_upwards [coeFn_mul (f + g) h, Lp.coeFn_add f g, Lp.coeFn_add (f * h) (g * h),
      coeFn_mul f h, coeFn_mul g h] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁, h₂, h₃, h₄, h₅, Pi.add_apply, Pi.mul_apply, add_mul]

noncomputable instance instNormedRing : NormedRing (Lp R ∞ μ) where
  dist_eq _ _ := rfl
  norm_mul_le := Lp.norm_smul_le

/-! ### The algebra structure -/

section Algebra

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

instance instIsScalarTower : IsScalarTower 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_assoc := Lp.smul_assoc

instance instSMulCommClass : SMulCommClass 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_comm := Lp.smul_comm

noncomputable instance instAlgebra : Algebra 𝕜 (Lp R ∞ μ) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

noncomputable instance instNormedAlgebra : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  norm_smul_le := norm_smul_le

theorem algebraMap_eq_const (c : 𝕜) : algebraMap 𝕜 (Lp R ∞ μ) c = const (algebraMap 𝕜 R c) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, one_def]
  rfl

theorem coeFn_algebraMap (c : 𝕜) :
    ⇑(algebraMap 𝕜 (Lp R ∞ μ) c) =ᵐ[μ] fun _ ↦ algebraMap 𝕜 R c := by
  rw [algebraMap_eq_const]
  exact coeFn_const _

end Algebra

/-! ### The star structure -/

section Star

variable [StarRing R] [NormedStarGroup R]

noncomputable instance instStarRing : StarRing (Lp R ∞ μ) where
  star_mul f g := Lp.ext <| by
    filter_upwards [Lp.coeFn_star (f * g), coeFn_mul f g, coeFn_mul (star g) (star f),
      Lp.coeFn_star f, Lp.coeFn_star g] with x h₁ h₂ h₃ h₄ h₅
    simp [h₁, h₂, h₃, h₄, h₅]
  star_add := star_add

instance instCStarRing [CStarRing R] : CStarRing (Lp R ∞ μ) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (norm_nonneg _) (norm_nonneg _)]
    refine Lp.norm_le_of_ae_bound_top (Real.sqrt_nonneg _) ?_
    filter_upwards [Lp.ae_norm_le_norm (star f * f), Lp.coeFn_star f, coeFn_mul (star f) f]
      with x hx h₁ h₂
    rw [Real.le_sqrt (norm_nonneg _) (norm_nonneg _), sq, ← CStarRing.norm_star_mul_self]
    simpa [h₁, h₂] using hx

end Star

end NormedRing

section CommRing

variable {R : Type*} [NormedCommRing R]

noncomputable instance instCommRing : CommRing (Lp R ∞ μ) where
  mul_comm f g := Lp.ext <| by
    filter_upwards [coeFn_mul f g, coeFn_mul g f] with x h₁ h₂
    simp [h₁, h₂, mul_comm]

noncomputable instance instNormedCommRing : NormedCommRing (Lp R ∞ μ) where
  mul_comm := mul_comm

end CommRing

noncomputable instance instCStarAlgebra {R : Type*} [CStarAlgebra R] :
    CStarAlgebra (Lp R ∞ μ) where

noncomputable instance instCommCStarAlgebra {R : Type*} [CommCStarAlgebra R] :
    CommCStarAlgebra (Lp R ∞ μ) where
  mul_comm := mul_comm

end Linfty

end MeasureTheory
