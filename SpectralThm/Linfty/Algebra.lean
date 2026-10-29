/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.Holder
public import SpectralThm.Linfty

/-!
# The algebra `L^∞`

For a measure `μ` and a normed ring `R`, `Lp R ∞ μ` is a normed ring under pointwise
multiplication, a star ring when `R` is, and a (commutative) C⋆-algebra when `R` is.

## Main definitions

* `MeasureTheory.Measure.essRange`: the essential range of a function.
* Instances: `Ring`, `CommRing`, `StarRing`, `NormedRing`, `NormedCommRing`, `NormedAlgebra`,
  `CStarRing`, `CStarAlgebra` and `CommCStarAlgebra` on `Lp R ∞ μ`.

## Main results

* `MeasureTheory.Linfty.coeFn_mul`, `MeasureTheory.Linfty.toLp_mul`,
  `MeasureTheory.MemLp.toLp_star`: products and stars are computed pointwise.

## References

This file started on the `BFC` branch of `j-loreaux/LeanOA` (Jon Bannon, Jireh Loreaux), as
groundwork for a Borel functional calculus class; its sketch of that class is recorded in
`notes.md`. Mathlib PRs #29108 and #30030 (open) develop the multiplication on `Lp ∞`.
-/

@[expose] public section

namespace MeasureTheory
section BorelSpace

open BorelSpace

namespace Measure

open scoped Topology

section essRange

variable {X : Type*} [MeasurableSpace X]

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]

/-- The essential range of `f` with respect to `μ`: the support of the push-forward `map f μ`. -/
noncomputable def essRange (μ : Measure X) (f : X → Y) : Set Y :=
  (map f μ).support

theorem essRange_eq_of_ae_eq {μ : Measure X} (f g : X → Y) (hfg : f =ᵐ[μ] g) :
    essRange μ f = essRange μ g := by
  rw [essRange, essRange, Measure.map_congr hfg]

end essRange

end Measure

end BorelSpace

open ENNReal

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

section NormedRing

variable {R : Type*} [NormedRing R]

section Mul

noncomputable instance Linfty.instMul : Mul (Lp R ∞ μ) where
  mul f g := f • g

lemma Linfty.coeFn_mul (f g : Lp R ∞ μ) : f * g =ᵐ[μ] ⇑f * g :=
  Lp.coeFn_lpSMul f g

lemma Linfty.toLp_mul {f g : α → R} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    (hf.mul hg).toLp (f * g) = hf.toLp f * hg.toLp g :=
  Lp.ext <| (MemLp.coeFn_toLp _).trans <| by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, coeFn_mul (hf.toLp f) (hg.toLp g)]
      with z h₁ h₂ h₃
    simp [h₁, h₂, h₃]

end Mul

section Const

theorem const_mem_Linfty (c : R) :
    @AEEqFun.const α _ _ μ _ c ∈ Lp R ∞ μ :=
  (memLp_top_const c).eLpNorm_mk_lt_top

/-- Constant functions as elements of `L^∞`. -/
def Linfty.const : R →+ Lp R ∞ μ where
  toFun c := ⟨AEEqFun.const α c, const_mem_Linfty c⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma Linfty.const_val (c : R) : (Linfty.const c).1 = AEEqFun.const (β := R) (μ := μ) α c := rfl

lemma Linfty.coeFn_const (c : R) : Linfty.const (μ := μ) c =ᵐ[μ] Function.const α c :=
  AEEqFun.coeFn_const α c

end Const

section One

section AEEqFun

variable {β : Type*} [TopologicalSpace β] [MulOneClass β] [ContinuousMul β]

theorem AEEqFun.one_mul (f : α →ₘ[μ] β) : 1 * f = f := by
  ext
  filter_upwards [coeFn_mul 1 f, coeFn_one (β := β)] with x hx1 hx2
  simp [hx1, hx2]

theorem AEEqFun.one_smul (f : α →ₘ[μ] β) : (1 : α →ₘ[μ] β) • f = f := by
  simp [smul_eq_mul, AEEqFun.one_mul]

end AEEqFun


instance Linfty.instOne : One (Lp R ∞ μ) where
  one := ⟨MemLp.toLp (fun (_ : α) => (1 : R)) (memLp_top_const (μ := μ) 1), SetLike.coe_mem _⟩

theorem Linfty.coeFn_one : ⇑(1 : Lp R ∞ μ) =ᶠ[ae μ] 1 := coeFn_const ..

theorem Linfty.one_smul (f : Lp R ∞ μ) : (1 : Lp R ∞ μ) • f = f := by
  ext
  filter_upwards [Linfty.coeFn_one (R := R) ..,
    Linfty.coeFn_mul 1 f] with x hx1 hx2
  simp [hx1, hx2]

theorem Linfty.smul_one (f : Lp R ∞ μ) : f • (1 : Lp R ∞ μ) = f := by
  ext
  filter_upwards [Linfty.coeFn_one (R := R) ..,
    Linfty.coeFn_mul f (1 : Lp R ∞ μ)] with x hx1 hx2
  simp_all [Pi.mul_apply, mul_one, smul_eq_mul]

end One

section MulOneClass

noncomputable instance Linfty.instMulOneClass : MulOneClass (Lp R ∞ μ) where
  one_mul := Linfty.one_smul
  mul_one := Linfty.smul_one

end MulOneClass

section Semigroup

noncomputable instance Linfty.instSemigroup : Semigroup (Lp R ∞ μ) where
  mul_assoc := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul (f * g) h, Linfty.coeFn_mul f  (g * h),
      Linfty.coeFn_mul f g, Linfty.coeFn_mul g h] with x hx1 hx2 hx3 hx4
    simp [hx1, Pi.mul_apply, hx3, mul_assoc, hx2, hx4]

end Semigroup

section Distrib

noncomputable instance Linfty.instDistrib : Distrib (Lp R ∞ μ) where
  left_distrib := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul f (g + h),
      Lp.coeFn_add (p := ∞) g h, Lp.coeFn_add (p := ∞) (f * g) (f * h),
      Linfty.coeFn_mul f g, Linfty.coeFn_mul f h] with x h1 h2 h3 h4 h5
    rw [h3, Pi.add_apply, h4, h5, h1, Pi.mul_apply, h2, Pi.add_apply, Pi.mul_apply, Pi.mul_apply,
      mul_add]
  right_distrib := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul (f + g) h, Lp.coeFn_add (p := ∞) f g,
       Lp.coeFn_add (p := ∞) (f * h) (g * h), Linfty.coeFn_mul f h,
       Linfty.coeFn_mul g h] with x h1 h2 h3 h4 h5
    rw [Pi.mul_apply, h2, Pi.add_apply] at h1
    rw [h1, h3, Pi.add_apply, h4, h5, Pi.mul_apply, Pi.mul_apply, add_mul]

end Distrib

section MulZeroClass

noncomputable instance Linfty.instMulZeroClass : MulZeroClass (Lp R ∞ μ) where
  zero_mul := by
    intro f
    ext
    filter_upwards [Lp.coeFn_zero (E := R) (p := ∞) ..,
      Linfty.coeFn_mul 0 f] with x h1 h2
    simp_all only [ZeroMemClass.coe_zero, Pi.zero_apply, Pi.mul_apply, zero_mul]
  mul_zero := by
    intro f
    ext
    filter_upwards [Lp.coeFn_zero (E := R) (p := ∞) ..,
      Linfty.coeFn_mul f 0] with x h1 h2
    simp_all [ZeroMemClass.coe_zero, Pi.mul_apply, mul_zero]

end MulZeroClass

noncomputable instance Linfty.instMonoidWithZero : MonoidWithZero (Lp R ∞ μ) where

noncomputable instance Linfty.instNonUnitalNonAssocSemiring :
    NonUnitalNonAssocSemiring (Lp R ∞ μ) where

noncomputable instance Linfty.instNonAssocSemiring : NonAssocSemiring (Lp R ∞ μ) where

noncomputable instance Linfty.instNonUnitalSemiring : NonUnitalSemiring (Lp R ∞ μ) where

noncomputable instance Linfty.instSemiring : Semiring (Lp R ∞ μ) where

noncomputable instance Linfty.instAddGroupWithOne : AddGroupWithOne (Lp R ∞ μ) where

noncomputable instance Linfty.instNonUnitalRing : NonUnitalRing (Lp R ∞ μ) where

noncomputable instance Linfty.instRing : Ring (Lp R ∞ μ) where

section StarMul
section AEEqFun

variable [StarRing R] [NormedStarGroup R]

instance AEEqFun.instStarMul : StarMul (α →ₘ[μ] R) where
  star_mul f g := by
    ext
    filter_upwards [AEEqFun.coeFn_star (f * g), AEEqFun.coeFn_mul f g,
      AEEqFun.coeFn_mul (star g) (star f), AEEqFun.coeFn_star f,
      AEEqFun.coeFn_star g] with x hx hy hz h1 h2
    simp [hx, Pi.star_apply, hy, Pi.mul_apply, hz, h1, h2, star_mul]

instance AEEqFun.instStarAddMonoid : StarAddMonoid (α →ₘ[μ] R) where
  star_add f g := by
    ext
    filter_upwards [AEEqFun.coeFn_star (f + g), AEEqFun.coeFn_add (star f) (star g),
      AEEqFun.coeFn_add f g, AEEqFun.coeFn_star f, AEEqFun.coeFn_star g] with x hx hy hz hq hw
    simp [hx, Pi.star_apply, hz, Pi.add_apply, star_add, hy, hq, hw]

end AEEqFun

variable [StarRing R] [NormedStarGroup R]

noncomputable instance Linfty.instStarMul : StarMul (Lp R ∞ μ) where
  star_mul f g := by
    ext
    filter_upwards [Lp.coeFn_star (f * g), Linfty.coeFn_mul f g,
      Linfty.coeFn_mul (star g) (star f), Lp.coeFn_star f,
        Lp.coeFn_star g] with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp [hx₁, hx₂, hx₃, hx₄, hx₅]

end StarMul

section StarRing

variable [StarRing R] [NormedStarGroup R]

noncomputable instance Linfty.instStarAddMonoid : StarAddMonoid (Lp R ∞ μ) where
  star_add f g := by
    ext
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_star (f + g), Lp.coeFn_add (star f) (star g),
      Lp.coeFn_star f, Lp.coeFn_star g] with x hx hy hz hw hq
    rw [hy, Pi.star_apply, hx, Pi.add_apply, star_add, hz, Pi.add_apply, hw, hq, Pi.star_apply,
      Pi.star_apply]

noncomputable instance Linfty.instStarRing : StarRing (Lp R ∞ μ) where
  star_add := star_add

end StarRing

lemma MemLp.toLp_star [StarRing R] [NormedStarGroup R] {p : ℝ≥0∞} {f : α → R} (hf : MemLp f p μ) :
    hf.star.toLp (star f) = star (hf.toLp f) :=
  Lp.ext <| (MemLp.coeFn_toLp _).trans <| by
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_star (hf.toLp f)] with z h₁ h₂
    simp [h₁, h₂]

open scoped NNReal

section IsBoundedSMul

variable [IsBoundedSMul R R]

noncomputable instance Linfty.instNormedRing : NormedRing (Lp R ∞ μ) where
  dist_eq _ _ := rfl
  norm_mul_le _ _ := Lp.norm_smul_le _ _

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

instance Linfty.instIsScalarTower : IsScalarTower 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_assoc := Lp.smul_assoc

instance Linfty.instSMulCommClass : SMulCommClass 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_comm := Lp.smul_comm

noncomputable instance Linfty.instAlgebra : Algebra 𝕜 (Lp R ∞ μ) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

noncomputable instance Linfty.instNormedAlgebra : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  norm_smul_le := norm_smul_le

end NormedAlgebra

section CStarRing

instance Linfty.instCStarRing [StarRing R] [CStarRing R] : CStarRing (Lp R ∞ μ) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (by positivity) (by positivity), Real.sqrt_eq_rpow]
    apply Lp.norm_le_of_ae_bound_top (by positivity)
    filter_upwards [Lp.ae_norm_le_norm (star f * f), Lp.coeFn_star f,
      Linfty.coeFn_mul (star f) f] with x hx hx_star hx_mul
    refine Real.rpow_inv_le_iff_of_pos (norm_nonneg _) (norm_nonneg _) (by norm_num)|>.mp ?_
    simp only [one_div, inv_inv, Real.rpow_two]
    convert hx
    simp only [sq, hx_mul, Pi.mul_apply, hx_star, Pi.star_apply]
    exact CStarRing.norm_star_mul_self.symm

end CStarRing

section StarModule

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] [Star 𝕜]
variable [StarRing R] [NormedStarGroup R] [StarModule 𝕜 R]

noncomputable instance AEEqFun.instStarModule : StarModule 𝕜 (α →ₘ[μ] R) where
  star_smul := by
     intro c f
     refine AEEqFun.ext_iff.mpr ?_
     filter_upwards [AEEqFun.coeFn_star (c • f), AEEqFun.coeFn_smul c f,
       AEEqFun.coeFn_smul (star c) (star f) |>.symm,
       AEEqFun.coeFn_star f] with x hstar1 hsmul1 hsmul2 hstar2
     simp [hstar1, Pi.star_apply, hsmul1, Pi.smul_apply, star_smul, ← hsmul2, hstar2]

noncomputable instance Linfty.instStarModule : StarModule 𝕜 (Lp R ∞ μ) where
  star_smul := by
    intro r f
    refine SetLike.coe_eq_coe.mp ?_
    exact star_smul (A := α →ₘ[μ] R) ..

end StarModule

end IsBoundedSMul

end NormedRing
section CommRing

variable {R : Type*} [NormedCommRing R]

noncomputable instance Linfty.instCommRing : CommRing (Lp R ∞ μ) where
  mul_comm f g := by
    ext
    filter_upwards [Linfty.coeFn_mul f g, Linfty.coeFn_mul g f] with x h₁ h₂
    rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, mul_comm]

noncomputable instance Linfty.instNormedCommRing : NormedCommRing (Lp R ∞ μ) where
  mul_comm := mul_comm

end CommRing

section CStarAlgebra

noncomputable instance Linfty.instCStarAlgebra {R : Type*} [CStarAlgebra R] :
    CStarAlgebra (Lp R ∞ μ) where

noncomputable instance Linfty.instCommCStarAlgebra {R : Type*} [CommCStarAlgebra R] :
    CommCStarAlgebra (Lp R ∞ μ) where
  mul_comm := mul_comm

end CStarAlgebra

end MeasureTheory
