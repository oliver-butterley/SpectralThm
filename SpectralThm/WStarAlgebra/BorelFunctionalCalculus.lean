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
# Borel Functional Calculus Class

We develop the basic definition of the `BorelFunctionalCalculus` class, imitating
`ContinuousFunctionalCalculus`

## Main declarations

+ TBD

# TODO

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

noncomputable instance : Mul (Lp R ∞ μ) where
  mul f g := f • g

lemma Linfty.coeFn_mul (f g : Lp R ∞ μ) : f * g =ᵐ[μ] ⇑f * g :=
  Lp.coeFn_lpSMul f g

end Mul

section Const

theorem const_mem_Linfty (c : R) :
    @AEEqFun.const α _ _ μ _ c ∈ Lp R ∞ μ :=
  (memLp_top_const c).eLpNorm_mk_lt_top

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

noncomputable instance : MulOneClass (Lp R ∞ μ) where
  one_mul := Linfty.one_smul
  mul_one := Linfty.smul_one

end MulOneClass

section Semigroup

noncomputable instance : Semigroup (Lp R ∞ μ) where
  mul_assoc := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul (f * g) h, Linfty.coeFn_mul f  (g * h),
      Linfty.coeFn_mul f g, Linfty.coeFn_mul g h] with x hx1 hx2 hx3 hx4
    simp [hx1, Pi.mul_apply, hx3, mul_assoc, hx2, hx4]

end Semigroup

section Distrib

noncomputable instance : Distrib (Lp R ∞ μ) where
  left_distrib := by
    intro f g h
    ext
    filter_upwards [Linfty.coeFn_mul f (g + h),
      Lp.coeFn_add (p := ∞) g h, Lp.coeFn_add (p := ∞) (f * g) (f * h),
      Linfty.coeFn_mul f g, Linfty.coeFn_mul f h] with x h1 h2 h3 h4 h5
    rw [h3, Pi.add_apply, h4, h5, h1, Pi.mul_apply, h2, Pi.add_apply, Pi.mul_apply, Pi.mul_apply, mul_add]
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

noncomputable instance : MulZeroClass (Lp R ∞ μ) where
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

noncomputable instance : MonoidWithZero (Lp R ∞ μ) where

noncomputable instance : NonUnitalNonAssocSemiring (Lp R ∞ μ) where

noncomputable instance : NonAssocSemiring (Lp R ∞ μ) where

noncomputable instance : NonUnitalSemiring (Lp R ∞ μ) where

noncomputable instance : Semiring (Lp R ∞ μ) where

noncomputable instance : AddGroupWithOne (Lp R ∞ μ) where

noncomputable instance : NonUnitalRing (Lp R ∞ μ) where

noncomputable instance : Ring (Lp R ∞ μ) where

section StarMul
section AEEqFun

variable [StarRing R] [NormedStarGroup R]

instance : StarMul (α →ₘ[μ] R) where
  star_mul f g := by
    ext
    filter_upwards [AEEqFun.coeFn_star (f * g), AEEqFun.coeFn_mul f g, AEEqFun.coeFn_mul (star g) (star f), AEEqFun.coeFn_star f,
         AEEqFun.coeFn_star g] with x hx hy hz h1 h2
    simp [hx, Pi.star_apply, hy, Pi.mul_apply, hz, h1, h2, star_mul]

instance : StarAddMonoid (α →ₘ[μ] R) where
  star_add f g:= by
    ext
    filter_upwards [AEEqFun.coeFn_star (f + g), AEEqFun.coeFn_add (star f) (star g), AEEqFun.coeFn_add f g, AEEqFun.coeFn_star f, AEEqFun.coeFn_star g] with x hx hy hz hq hw
    simp [hx, Pi.star_apply, hz, Pi.add_apply, star_add, hy, hq, hw]

end AEEqFun

variable [StarRing R] [NormedStarGroup R]

noncomputable instance : StarMul (Lp R ∞ μ) where
  star_mul f g := by
    ext
    filter_upwards [Lp.coeFn_star (f * g), Linfty.coeFn_mul f g,
      Linfty.coeFn_mul (star g) (star f), Lp.coeFn_star f, Lp.coeFn_star g] with x hx₁ hx₂ hx₃ hx₄ hx₅
    simp [hx₁, hx₂, hx₃, hx₄, hx₅]

end StarMul

section StarRing

variable [StarRing R] [NormedStarGroup R]

noncomputable instance : StarAddMonoid (Lp R ∞ μ) where
  star_add f g := by
    ext
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_star (f + g), Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g] with x hx hy hz hw hq
    rw [hy, Pi.star_apply, hx, Pi.add_apply, star_add, hz, Pi.add_apply, hw, hq, Pi.star_apply, Pi.star_apply]

noncomputable instance : StarRing (Lp R ∞ μ) where
  star_add := star_add

end StarRing

open scoped NNReal

section IsBoundedSMul

variable [IsBoundedSMul R R]

noncomputable instance : NormedRing (Lp R ∞ μ) where
  dist_eq _ _ := rfl
  norm_mul_le _ _ := Lp.norm_smul_le _ _

section NormedAlgebra

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R]

instance : IsScalarTower 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_assoc := Lp.smul_assoc

instance : SMulCommClass 𝕜 (Lp R ∞ μ) (Lp R ∞ μ) where
  smul_comm := Lp.smul_comm

noncomputable instance : Algebra 𝕜 (Lp R ∞ μ) := Algebra.ofModule (smul_mul_assoc) (mul_smul_comm)

noncomputable instance : NormedAlgebra 𝕜 (Lp R ∞ μ) where
  norm_smul_le := norm_smul_le

end NormedAlgebra

section CStarRing

instance [StarRing R] [CStarRing R] : CStarRing (Lp R ∞ μ) where
  norm_mul_self_le f := by
    rw [← sq, ← Real.le_sqrt (by positivity) (by positivity), Real.sqrt_eq_rpow]
    apply Lp.norm_le_of_ae_bound_top (by positivity)
    filter_upwards [Lp.ae_norm_le_norm (star f * f), Lp.coeFn_star f, Linfty.coeFn_mul (star f) f] with x hx hx_star hx_mul
    refine Real.rpow_inv_le_iff_of_pos (norm_nonneg _) (norm_nonneg _) (by norm_num)|>.mp ?_
    simp only [one_div, inv_inv, Real.rpow_two]
    convert hx
    simp only [sq, hx_mul, Pi.mul_apply, hx_star, Pi.star_apply]
    exact CStarRing.norm_star_mul_self.symm

end CStarRing

section StarModule

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] [Star 𝕜]
variable [StarRing R] [NormedStarGroup R] [StarModule 𝕜 R]

noncomputable instance : StarModule 𝕜 (α →ₘ[μ] R) where
  star_smul := by
     intro c f
     refine AEEqFun.ext_iff.mpr ?_
     filter_upwards [AEEqFun.coeFn_star (c • f), AEEqFun.coeFn_smul c f, AEEqFun.coeFn_smul (star c) (star f) |>.symm, AEEqFun.coeFn_star f] with x hstar1 hsmul1 hsmul2 hstar2
     simp [hstar1, Pi.star_apply, hsmul1, Pi.smul_apply, star_smul, ← hsmul2, hstar2]

noncomputable instance : StarModule 𝕜 (Lp R ∞ μ) where
  star_smul := by
    intro r f
    refine SetLike.coe_eq_coe.mp ?_
    exact star_smul (A := α →ₘ[μ] R) ..

end StarModule

end IsBoundedSMul

end NormedRing
section CommRing

variable {R : Type*} [NormedCommRing R]

noncomputable instance : CommRing (Lp R ∞ μ) where
  mul_comm f g := by
    ext
    filter_upwards [Linfty.coeFn_mul f g, Linfty.coeFn_mul g f] with x h₁ h₂
    rw [h₁, h₂, Pi.mul_apply, Pi.mul_apply, mul_comm]

noncomputable instance [IsBoundedSMul R R] : NormedCommRing (Lp R ∞ μ) where
  mul_comm := mul_comm

end CommRing

section CStarAlgebra

noncomputable instance {R : Type*} [CStarAlgebra R] : CStarAlgebra (Lp R ∞ μ) where

noncomputable instance {R : Type*} [CommCStarAlgebra R] : CommCStarAlgebra (Lp R ∞ μ) where
  mul_comm := mul_comm

end CStarAlgebra


/-
section BFC

class BorelFunctionalCalculus {A : Type*} (p : outParam (A → Prop))
    [CStarAlgebra A] [WStarAlgebra A] : Prop where
  predicate_zero : p 0
  [compactSpace_spectrum (a : A) : CompactSpace (spectrum ℂ a)]
  spectrum_nonempty [Nontrivial A] (a : A) (ha : p a) : (spectrum ℂ a).Nonempty
  exists_bfc_of_predicate : ∀ a, p a → ∃ φ : C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A,
    IsClosedEmbedding φ ∧ φ ((ContinuousMap.id ℂ).restrict <| spectrum ℂ a) = a ∧
      (∀ f, spectrum ℂ (φ f) = Set.range f) ∧ ∀ f, p (φ f)

--We need a type synonym for Lp (spectrum ℂ a) ∞ μ with the weak * topology coming from the predual Lp (spectrum ℂ a) 1 μ.
--This Lp (spectrum ℂ a) ∞ μ must also be a *--algebra..this should somehow be in the type synonym.
--Once we have this, we need to replace all instances of C(spectrum ℂ a, ℂ) with Lp (spectrum ℂ a) ∞ μ.
--Still need the essential range for this spectrum result.

end BFC
-/
