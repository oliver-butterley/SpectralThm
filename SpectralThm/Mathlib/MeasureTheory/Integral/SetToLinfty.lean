/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
public import SpectralThm.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Extension of set functions to `L^∞`

This file is the `L^∞` analogue of `Mathlib.MeasureTheory.Integral.SetToL1.L1`. A set function
`T : Set α → E →L[ℝ] F` defines `f ↦ ∑ x ∈ f.range, T (f ⁻¹' {x}) x` on simple functions
(`MeasureTheory.SimpleFunc.setToSimpleFunc`). If `T` is additive on disjoint measurable sets,
vanishes on `μ`-null sets and this map is bounded in the `L^∞` norm, it extends to a continuous
linear map `Lp E ∞ μ →L[𝕜] F`, provided `E` is a proper space (so that simple functions are dense
in `Lp E ∞ μ`) and `F` is complete.

Unlike `setToL1`, no finiteness of `μ` is involved: only its null sets matter.

## Main definitions

* `MeasureTheory.DominatedLinftyAdditive μ T C`: `T` is additive on disjoint measurable sets,
  vanishes on `μ`-null sets, and the induced map on simple functions is bounded by `C` in the
  `L^∞(μ)` norm. This is the analogue of `MeasureTheory.DominatedFinMeasAdditive`.
* `MeasureTheory.Linfty.setToLinftyS T`: the map induced by `T` on the simple functions
  of `Lp E ∞ μ`.
* `MeasureTheory.Linfty.setToLinftySCLM' 𝕜 hT h_smul`: `setToLinftyS T` as a continuous
  `𝕜`-linear map.
* `MeasureTheory.Linfty.setToLinfty' 𝕜 hT h_smul : Lp E ∞ μ →L[𝕜] F` and
  `MeasureTheory.Linfty.setToLinfty hT : Lp E ∞ μ →L[ℝ] F`: the extensions of `setToLinftyS T`
  to `Lp E ∞ μ`.

## Main results

* `MeasureTheory.Linfty.setToLinfty'_toLp`: on simple functions, `setToLinfty'` is
  `MeasureTheory.SimpleFunc.setToSimpleFunc`.
* `MeasureTheory.Linfty.norm_setToLinfty'_le_mul_norm`: `‖setToLinfty' 𝕜 hT h_smul f‖ ≤ C * ‖f‖`.
* `MeasureTheory.Linfty.setToLinfty_eq_setToLinfty'`: the two extensions agree.
* `MeasureTheory.Linfty.norm_setToLinfty'_apply`: if `T` is isometric on simple functions, then
  so is `setToLinfty'`.
-/

@[expose] public section

open ENNReal

namespace MeasureTheory

open Lp.simpleFunc

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {T : Set α → E →L[ℝ] F} {C : ℝ}

/-- `T` is additive on disjoint measurable sets, vanishes on `μ`-null sets, and the induced map
on simple functions is bounded by `C` in the `L^∞(μ)` norm. This is the `L^∞` analogue of
`DominatedFinMeasAdditive`. -/
structure DominatedLinftyAdditive (μ : Measure α) (T : Set α → E →L[ℝ] F) (C : ℝ) : Prop where
  add : ∀ s t, MeasurableSet s → MeasurableSet t → Disjoint s t → T (s ∪ t) = T s + T t
  eq_zero_of_measure_zero : ∀ s, MeasurableSet s → μ s = 0 → T s = 0
  norm_setToSimpleFunc_le : ∀ f : SimpleFunc α E, ‖f.setToSimpleFunc T‖ ≤ C * (eLpNorm f ∞ μ).toReal

namespace DominatedLinftyAdditive

theorem finMeasAdditive (hT : DominatedLinftyAdditive μ T C) (ν : Measure α) :
    FinMeasAdditive ν T :=
  fun s t hs ht _ _ h ↦ hT.add s t hs ht h

/-- `SimpleFunc.setToSimpleFunc T` only depends on the `μ`-a.e. class of a simple function. -/
theorem setToSimpleFunc_congr (hT : DominatedLinftyAdditive μ T C) {f g : SimpleFunc α E}
    (h : f =ᵐ[μ] g) : f.setToSimpleFunc T = g.setToSimpleFunc T := by
  refine SimpleFunc.setToSimpleFunc_congr' T (hT.finMeasAdditive 0) integrable_zero_measure
    integrable_zero_measure fun a b hab ↦ hT.eq_zero_of_measure_zero _
      ((f.measurableSet_fiber a).inter (g.measurableSet_fiber b)) ?_
  refine measure_mono_null ?_ (ae_iff.1 h)
  rintro x ⟨hxa, hxb⟩ hfg
  exact hab (hxa.symm.trans (hfg.trans hxb))

end DominatedLinftyAdditive

namespace Linfty

attribute [local instance] Lp.simpleFunc.module Lp.simpleFunc.normedSpace

section SetToLinftyS

/-- `SimpleFunc.setToSimpleFunc T` applied to (a representative of) an element of
`Lp.simpleFunc E ∞ μ`. -/
noncomputable def setToLinftyS (T : Set α → E →L[ℝ] F) (f : Lp.simpleFunc E ∞ μ) : F :=
  (toSimpleFunc f).setToSimpleFunc T

theorem setToLinftyS_eq_setToSimpleFunc (T : Set α → E →L[ℝ] F) (f : Lp.simpleFunc E ∞ μ) :
    setToLinftyS T f = (toSimpleFunc f).setToSimpleFunc T :=
  rfl

theorem setToLinftyS_toLp (hT : DominatedLinftyAdditive μ T C) (f : SimpleFunc α E) :
    setToLinftyS T (f.toLp (f.memLp_top μ)) = f.setToSimpleFunc T :=
  hT.setToSimpleFunc_congr (toSimpleFunc_toLp f _)

theorem setToLinftyS_add (hT : DominatedLinftyAdditive μ T C) (f g : Lp.simpleFunc E ∞ μ) :
    setToLinftyS T (f + g) = setToLinftyS T f + setToLinftyS T g := by
  rw [setToLinftyS,
    hT.setToSimpleFunc_congr (g := toSimpleFunc f + toSimpleFunc g) (add_toSimpleFunc f g),
    SimpleFunc.setToSimpleFunc_add T (hT.finMeasAdditive 0) integrable_zero_measure
      integrable_zero_measure, setToLinftyS, setToLinftyS]

theorem setToLinftyS_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [DistribSMul 𝕜 F] (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (c : 𝕜) (f : Lp.simpleFunc E ∞ μ) :
    setToLinftyS T (c • f) = c • setToLinftyS T f := by
  rw [setToLinftyS, hT.setToSimpleFunc_congr (g := c • toSimpleFunc f) (smul_toSimpleFunc c f),
    SimpleFunc.setToSimpleFunc_smul T (hT.finMeasAdditive 0) h_smul c integrable_zero_measure,
    setToLinftyS]

theorem norm_setToLinftyS_le (hT : DominatedLinftyAdditive μ T C) (f : Lp.simpleFunc E ∞ μ) :
    ‖setToLinftyS T f‖ ≤ C * ‖f‖ :=
  (hT.norm_setToSimpleFunc_le _).trans_eq (by rw [norm_toSimpleFunc])

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [Module 𝕜 F] [IsBoundedSMul 𝕜 E]
  [IsBoundedSMul 𝕜 F]

/-- `setToLinftyS T` as a continuous `𝕜`-linear map on `Lp.simpleFunc E ∞ μ`. -/
noncomputable def setToLinftySCLM' (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : Lp.simpleFunc E ∞ μ →L[𝕜] F :=
  LinearMap.mkContinuous ⟨⟨setToLinftyS T, setToLinftyS_add hT⟩, setToLinftyS_smul hT h_smul⟩ C
    (norm_setToLinftyS_le hT)

variable {𝕜}

omit [IsBoundedSMul 𝕜 F] in
@[simp]
theorem setToLinftySCLM'_apply (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : Lp.simpleFunc E ∞ μ) :
    setToLinftySCLM' 𝕜 hT h_smul f = setToLinftyS T f :=
  rfl

end SetToLinftyS

variable [ProperSpace E] [CompleteSpace F]

section SetToLinfty'

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [Module 𝕜 F] [IsBoundedSMul 𝕜 E]
  [IsBoundedSMul 𝕜 F]

/-- Extend a set function `T : Set α → E →L[ℝ] F` satisfying `DominatedLinftyAdditive μ T C` to a
continuous `𝕜`-linear map `Lp E ∞ μ →L[𝕜] F`. -/
noncomputable def setToLinfty' (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) : Lp E ∞ μ →L[𝕜] F :=
  (setToLinftySCLM' 𝕜 hT h_smul).extend (coeToLp α E 𝕜)

variable {𝕜}

theorem setToLinfty'_eq_setToLinftyS (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : Lp.simpleFunc E ∞ μ) :
    setToLinfty' 𝕜 hT h_smul f = setToLinftyS T f :=
  ContinuousLinearMap.extend_eq _ Lp.simpleFunc.denseRange_top isUniformInducing f

/-- On (the class of) a simple function, `setToLinfty'` is `SimpleFunc.setToSimpleFunc`. -/
@[simp]
theorem setToLinfty'_toLp (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : SimpleFunc α E) :
    setToLinfty' 𝕜 hT h_smul ((f.memLp_top μ).toLp f) = f.setToSimpleFunc T := by
  rw [← toLp_eq_toLp f (f.memLp_top μ), setToLinfty'_eq_setToLinftyS, setToLinftyS_toLp hT]

theorem norm_setToLinfty'_le_mul_norm (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : Lp E ∞ μ) :
    ‖setToLinfty' 𝕜 hT h_smul f‖ ≤ C * ‖f‖ := by
  refine Lp.simpleFunc.denseRange_top.induction_on f (isClosed_le (by fun_prop) (by fun_prop))
    fun g ↦ ?_
  rw [setToLinfty'_eq_setToLinftyS]
  exact norm_setToLinftyS_le hT g

/-- If `T` is isometric on simple functions, then so is `setToLinfty'`. -/
theorem norm_setToLinfty'_apply (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x)
    (h_norm : ∀ f : SimpleFunc α E, ‖f.setToSimpleFunc T‖ = (eLpNorm f ∞ μ).toReal)
    (f : Lp E ∞ μ) : ‖setToLinfty' 𝕜 hT h_smul f‖ = ‖f‖ := by
  refine Lp.simpleFunc.denseRange_top.induction_on f
    (isClosed_eq (continuous_norm.comp (setToLinfty' 𝕜 hT h_smul).continuous) continuous_norm)
    fun g ↦ ?_
  rw [setToLinfty'_eq_setToLinftyS, setToLinftyS, h_norm, ← norm_toSimpleFunc]
  rfl

end SetToLinfty'

/-- Extend a set function `T : Set α → E →L[ℝ] F` satisfying `DominatedLinftyAdditive μ T C` to a
continuous `ℝ`-linear map `Lp E ∞ μ →L[ℝ] F`. -/
noncomputable def setToLinfty (hT : DominatedLinftyAdditive μ T C) : Lp E ∞ μ →L[ℝ] F :=
  setToLinfty' ℝ hT fun c s x ↦ (T s).map_smul c x

theorem setToLinfty_eq_setToLinfty' {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [Module 𝕜 F]
    [IsBoundedSMul 𝕜 E] [IsBoundedSMul 𝕜 F] (hT : DominatedLinftyAdditive μ T C)
    (h_smul : ∀ c : 𝕜, ∀ s x, T s (c • x) = c • T s x) (f : Lp E ∞ μ) :
    setToLinfty hT f = setToLinfty' 𝕜 hT h_smul f := by
  refine Lp.simpleFunc.denseRange_top.induction_on f
    (isClosed_eq (setToLinfty hT).continuous (setToLinfty' 𝕜 hT h_smul).continuous) fun g ↦ ?_
  rw [setToLinfty, setToLinfty'_eq_setToLinftyS, setToLinfty'_eq_setToLinftyS]

theorem norm_setToLinfty_le_mul_norm (hT : DominatedLinftyAdditive μ T C) (f : Lp E ∞ μ) :
    ‖setToLinfty hT f‖ ≤ C * ‖f‖ :=
  norm_setToLinfty'_le_mul_norm hT _ f

theorem norm_setToLinfty_le (hT : DominatedLinftyAdditive μ T C) (hC : 0 ≤ C) :
    ‖setToLinfty hT‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_setToLinfty_le_mul_norm hT)

end Linfty

end MeasureTheory
