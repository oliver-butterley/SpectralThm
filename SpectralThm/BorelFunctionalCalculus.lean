/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import SpectralThm.SpectralTheorem

/-!
# The Borel functional calculus of a normal operator

For a normal operator `a` on a complex Hilbert space `H` with spectral measure `E`, the Borel
functional calculus sends a function `f : ℂ → ℂ` which is bounded and measurable on `σ(a)` to
`f(a) = ∫ f dE`. Following `cfc`, it is defined for all `f`, with the junk value `0` when the
restriction of `f` to `σ(a)` is not in `L^∞(E)`.

## Main definitions

* `IsStarNormal.bfc ha f`: the operator `f(a) = ∫ f dE`.

## Main results

* `IsStarNormal.bfc_eq_cfc`: the Borel functional calculus extends the continuous one.
* `IsStarNormal.bfc_id`: `id(a) = a`.
* `IsStarNormal.bfc_add`, `IsStarNormal.bfc_mul`, `IsStarNormal.bfc_star`, `IsStarNormal.bfc_pow`,
  `IsStarNormal.bfc_sum`, ...: it is a `*`-homomorphism on functions in `L^∞(E)`.
* `IsStarNormal.bfc_indicator`: the indicator of `s` gives the spectral projection `E(s)`.
* `IsStarNormal.bfc_congr_ae`, `IsStarNormal.bfc_eq_bfc_iff_ae_eq`: `f(a)` only depends on, and
  determines, `f` up to `E`-null sets.
* `IsStarNormal.norm_bfc_le`: `‖f(a)‖ ≤ sup_{σ(a)} |f|`.
* `IsStarNormal.inner_bfc`: `⟪x, f(a) y⟫ = ∫ f dE_{x,y}`.
* `IsStarNormal.commute_bfc`: an operator commuting with `a` commutes with `f(a)` (by
  Fuglede's theorem).
* `IsStarNormal.tendsto_bfc_apply`: the bounded convergence theorem, if `fᵢ → g` pointwise on
  `σ(a)` with `|fᵢ| ≤ C`, then `fᵢ(a) → g(a)` in the strong operator topology; also
  `tendsto_bfc_apply_of_ae` (a.e. hypotheses) and `tendsto_toPointwiseConvergenceCLM_bfc`
  (convergence in `H →Lₚₜ[ℂ] H`).
* `IsStarNormal.bfc_mem_vonNeumannAlgebra`: `f(a)` lies in every von Neumann algebra containing `a`.
* `IsStarNormal.isSelfAdjoint_bfc`, `IsStarNormal.bfc_nonneg`, `IsStarNormal.isStarProjection_bfc`:
  `f(a)` is self-adjoint (resp. nonnegative, an orthogonal projection) if `f` is real (resp.
  nonnegative, `{0, 1}`-valued) on `σ(a)`; `IsStarNormal.bfc_mono`: monotonicity.
* `IsStarNormal.eq_bfc`: uniqueness, any assignment `f ↦ Φ f` which is linear on bounded measurable
  functions, extends `cfc` and satisfies the bounded convergence theorem in the weak operator
  topology agrees with `bfc` on functions which are measurable and bounded on `σ(a)`. Its proof uses
  `MeasureTheory.ComplexMeasure.exists_integral_eq_of_tendsto`: a linear functional on bounded
  measurable functions satisfying bounded convergence is the integral against a complex measure.

## Implementation notes

The hypothesis that `f` is in the domain of the calculus is stated as
`MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure`, so that the `MemLp` API applies
directly; `IsStarNormal.memLp_of_bound` and `IsStarNormal.memLp_of_continuousOn` produce it.

The generic names `bfc` / `bfcHom` (without namespace, in the style of `cfc` / `cfcHom`) are
reserved for an abstract Borel functional calculus class, of which this would be the instance for
`H →L[ℂ] H`. The `*`-homomorphism on `L^∞(E)` is `ha.spectralMeasure.integral`.

## References

* [W. Rudin, *Functional Analysis*][rudin1991], 12.20–12.24.
-/

@[expose] public section

open MeasureTheory ContinuousLinearMap Filter Topology
open scoped InnerProductSpace MeasureTheory.ComplexMeasure ENNReal ComplexOrder

namespace IsStarNormal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {a : H →L[ℂ] H} (ha : IsStarNormal a) {f g : ℂ → ℂ}

open Classical in
/-- The Borel functional calculus `f(a) = ∫ f dE` of a normal operator `a` with spectral
measure `E`. It is `0` if the restriction of `f` to `σ(a)` is not in `L^∞(E)`. -/
noncomputable def bfc (f : ℂ → ℂ) : H →L[ℂ] H :=
  if hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure then
    ha.spectralMeasure.integral (hf.toLp _)
  else 0

lemma bfc_eq_integral (hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure) :
    ha.bfc f = ha.spectralMeasure.integral (hf.toLp _) := by
  simp [bfc, hf]

lemma bfc_eq_integral_of_eq {F : spectrum ℂ a → ℂ} (hF : MemLp F ∞ ha.spectralMeasure.measure)
    (h : (fun z : spectrum ℂ a ↦ f z) = F) :
    ha.bfc f = ha.spectralMeasure.integral (hF.toLp F) := by
  subst h
  exact ha.bfc_eq_integral hF

lemma bfc_of_not_memLp (hf : ¬MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure) :
    ha.bfc f = 0 := by
  simp [bfc, hf]

/-- A function which is measurable and bounded on `σ(a)` is in `L^∞(E)`. -/
lemma memLp_of_bound (hf : Measurable f) {C : ℝ} (hC : ∀ z ∈ spectrum ℂ a, ‖f z‖ ≤ C) :
    MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure :=
  memLp_top_of_bound (hf.comp measurable_subtype_coe).aestronglyMeasurable C
    (ae_of_all _ fun z ↦ hC z z.2)

/-- A function which is continuous on `σ(a)` is in `L^∞(E)`. -/
lemma memLp_of_continuousOn (hf : ContinuousOn f (spectrum ℂ a)) :
    MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure :=
  ha.spectralMeasure.memLp_continuousMap ⟨_, hf.domRestrict⟩

/-- `f(a)` only depends on `f` up to `E`-null sets. -/
lemma bfc_congr_ae
    (h : (fun z : spectrum ℂ a ↦ f z) =ᵐ[ha.spectralMeasure.measure] fun z ↦ g z) :
    ha.bfc f = ha.bfc g := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral (hf.ae_eq h), MemLp.toLp_congr _ _ h]
  · rw [ha.bfc_of_not_memLp hf, ha.bfc_of_not_memLp fun hg ↦ hf (hg.ae_eq h.symm)]

lemma bfc_congr (h : Set.EqOn f g (spectrum ℂ a)) : ha.bfc f = ha.bfc g :=
  ha.bfc_congr_ae (ae_of_all _ fun z ↦ h z.2)

/-- The Borel functional calculus extends the continuous functional calculus (Rudin 12.22 (a)). -/
theorem bfc_eq_cfc (hf : ContinuousOn f (spectrum ℂ a)) : ha.bfc f = cfc f a := by
  rw [cfc_apply f a ha hf, ha.bfc_eq_integral_of_eq
    (ha.spectralMeasure.memLp_continuousMap ⟨_, hf.domRestrict⟩) rfl, integral_spectralMeasure_toLp]

@[simp]
lemma bfc_id : ha.bfc id = a := by
  rw [ha.bfc_eq_cfc continuousOn_id, cfc_id ℂ a]

@[simp]
lemma bfc_id' : ha.bfc (fun z ↦ z) = a :=
  ha.bfc_id

lemma bfc_star_id : ha.bfc (star · : ℂ → ℂ) = star a := by
  rw [ha.bfc_eq_cfc continuous_star.continuousOn, cfc_star_id a]

@[simp]
lemma bfc_conj : ha.bfc (fun z ↦ (starRingEnd ℂ) z) = star a :=
  ha.bfc_star_id

@[simp]
lemma bfc_const (c : ℂ) : ha.bfc (fun _ ↦ c) = algebraMap ℂ (H →L[ℂ] H) c := by
  rw [ha.bfc_eq_cfc continuousOn_const, cfc_const c a]

@[simp]
lemma bfc_one : ha.bfc 1 = 1 := by
  rw [ha.bfc_eq_cfc (f := 1) continuousOn_const, cfc_one ℂ a]

lemma bfc_const_one : ha.bfc (fun _ ↦ 1) = 1 :=
  ha.bfc_one

@[simp]
lemma bfc_zero : ha.bfc 0 = 0 := by
  rw [ha.bfc_eq_cfc (f := 0) continuousOn_const, cfc_zero ℂ a]

lemma bfc_const_zero : ha.bfc (fun _ ↦ 0) = 0 :=
  ha.bfc_zero

lemma bfc_pow_id (n : ℕ) : ha.bfc (· ^ n) = a ^ n := by
  rw [ha.bfc_eq_cfc (continuous_pow n).continuousOn, cfc_pow_id a n]

lemma bfc_polynomial (q : Polynomial ℂ) : ha.bfc q.eval = Polynomial.aeval a q := by
  rw [ha.bfc_eq_cfc q.continuous.continuousOn, cfc_polynomial q a]

variable (hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure)
include hf

lemma bfc_add (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ f z + g z) = ha.bfc f + ha.bfc g := by
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg, ← map_add, ← MemLp.toLp_add,
    ha.bfc_eq_integral_of_eq (hf.add hg) rfl]

lemma bfc_sub (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ f z - g z) = ha.bfc f - ha.bfc g := by
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg, ← map_sub, ← MemLp.toLp_sub,
    ha.bfc_eq_integral_of_eq (hf.sub hg) rfl]

lemma bfc_neg : ha.bfc (fun z ↦ -f z) = -ha.bfc f := by
  rw [ha.bfc_eq_integral hf, ← map_neg, ← MemLp.toLp_neg, ha.bfc_eq_integral_of_eq hf.neg rfl]

lemma bfc_smul (c : ℂ) : ha.bfc (fun z ↦ c • f z) = c • ha.bfc f := by
  rw [ha.bfc_eq_integral hf, ← map_smul, ← MemLp.toLp_const_smul,
    ha.bfc_eq_integral_of_eq (hf.const_smul c) rfl]

lemma bfc_mul (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ f z * g z) = ha.bfc f * ha.bfc g := by
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg, ← map_mul, ← Linfty.toLp_mul,
    ha.bfc_eq_integral_of_eq (hf.mul hg) rfl]

lemma bfc_const_mul (c : ℂ) : ha.bfc (fun z ↦ c * f z) = c • ha.bfc f :=
  ha.bfc_smul hf c

lemma bfc_star : ha.bfc (fun z ↦ star (f z)) = star (ha.bfc f) := by
  rw [ha.bfc_eq_integral hf, ← map_star, ← MemLp.toLp_star, ha.bfc_eq_integral_of_eq hf.star rfl]

lemma bfc_pow (n : ℕ) : ha.bfc (fun z ↦ f z ^ n) = ha.bfc f ^ n := by
  have hpow (n : ℕ) : MemLp (fun z : spectrum ℂ a ↦ f z ^ n) ∞ ha.spectralMeasure.measure := by
    induction n with
    | zero => simpa using memLp_top_const (1 : ℂ)
    | succ n ih =>
      simp_rw [pow_succ]
      exact ih.mul hf
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [pow_succ]
    rw [ha.bfc_mul (f := fun z ↦ f z ^ n) (hpow n) hf, ih]

/-- Two functions in `L^∞(E)` have the same image under the Borel functional calculus iff they
agree `E`-almost everywhere on `σ(a)`. -/
lemma bfc_eq_bfc_iff_ae_eq (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc f = ha.bfc g ↔
      (fun z : spectrum ℂ a ↦ f z) =ᵐ[ha.spectralMeasure.measure] fun z ↦ g z := by
  refine ⟨fun h ↦ ?_, ha.bfc_congr_ae⟩
  rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg] at h
  exact (hf.toLp_eq_toLp_iff hg).1 (ha.spectralMeasure.isometry_integral.injective h)

/-- `‖f(a)‖ = ‖f‖_{L^∞(E)}`. -/
lemma norm_bfc : ‖ha.bfc f‖ = ‖hf.toLp _‖ := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.norm_integral]

/-- `⟪x, f(a) y⟫ = ∫ f dE_{x,y}` (Rudin 12.21 (1)). -/
lemma inner_bfc (x y : H) : ⟪x, ha.bfc f y⟫_ℂ = ∫ᶜ z, f z ∂(ha.cfcMeasure x y) := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.inner_integral,
    complexMeasure_spectralMeasure]
  refine VectorMeasure.integral_congr_ae ?_
  rw [← complexMeasure_spectralMeasure]
  exact (ha.spectralMeasure.variation_complexMeasure_absolutelyContinuous x y).ae_le
    hf.coeFn_toLp

/-- `‖f(a) x‖² = ∫ |f|² dE_{x,x}` (Rudin 12.21 (2)). -/
lemma norm_bfc_apply_sq (x : H) :
    ‖ha.bfc f x‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂(ha.spectralMeasure.measureOf x) := by
  rw [ha.bfc_eq_integral hf, ProjectionValuedMeasure.norm_integral_apply_sq_eq_integral]
  refine integral_congr_ae ((ha.spectralMeasure.measureOf_absolutelyContinuous x).ae_le ?_)
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

omit hf

lemma bfc_sum {ι : Type*} (f : ι → ℂ → ℂ) (s : Finset ι)
    (hf : ∀ i ∈ s, MemLp (fun z : spectrum ℂ a ↦ f i z) ∞ ha.spectralMeasure.measure) :
    ha.bfc (fun z ↦ ∑ i ∈ s, f i z) = ∑ i ∈ s, ha.bfc (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hf
    simp_rw [Finset.sum_cons]
    rw [ha.bfc_add hf.1 (memLp_finsetSum s hf.2), ih hf.2]

/-- `‖f(a)‖ ≤ C` if `|f| ≤ C` on `σ(a)`. -/
lemma norm_bfc_le {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ z ∈ spectrum ℂ a, ‖f z‖ ≤ C) :
    ‖ha.bfc f‖ ≤ C := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [ha.norm_bfc hf]
    refine Lp.norm_le_of_ae_bound_top hC₀ ?_
    filter_upwards [hf.coeFn_toLp] with z hz
    rw [hz]
    exact hC z z.2
  · rwa [ha.bfc_of_not_memLp hf, norm_zero]

/-- The indicator function of a measurable set `s` gives the spectral projection `E(s ∩ σ(a))`. -/
@[simp]
theorem bfc_indicator {s : Set ℂ} (hs : MeasurableSet s) :
    ha.bfc (s.indicator 1) = ha.spectralMeasure (Subtype.val ⁻¹' s) := by
  let F := (SimpleFunc.const (spectrum ℂ a) (1 : ℂ)).piecewise _ (measurable_subtype_coe hs)
    (SimpleFunc.const _ 0)
  rw [ha.bfc_eq_integral_of_eq (F.memLp_top _) ?_, ProjectionValuedMeasure.integral_toLp,
    ProjectionValuedMeasure.simpleIntegral_indicator]
  funext z
  by_cases hz : (z : ℂ) ∈ s <;> simp [F, hz]

/-- An operator commuting with `a` commutes with `f(a)`. -/
theorem commute_bfc {S : H →L[ℂ] H} (h : Commute S a) (f : ℂ → ℂ) :
    Commute S (ha.bfc f) := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [ha.bfc_eq_integral hf]
    exact ha.spectralMeasure.commute_integral_of_forall_commute
      (ha.forall_commute_spectralMeasure_iff.2 h) _
  · rw [ha.bfc_of_not_memLp hf]
    exact Commute.zero_right S

lemma bfc_commute_bfc (f g : ℂ → ℂ) : Commute (ha.bfc f) (ha.bfc g) := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · by_cases hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure
    · rw [ha.bfc_eq_integral hf, ha.bfc_eq_integral hg]
      exact ha.spectralMeasure.commute_integral _ _
    · rw [ha.bfc_of_not_memLp hg]
      exact Commute.zero_right _
  · rw [ha.bfc_of_not_memLp hf]
    exact Commute.zero_left _

/-- `f(a)` is normal. -/
instance isStarNormal_bfc (f : ℂ → ℂ) : IsStarNormal (ha.bfc f) := by
  by_cases hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [isStarNormal_iff, ← ha.bfc_star hf]
    exact ha.bfc_commute_bfc _ _
  · rw [ha.bfc_of_not_memLp hf]
    exact .zero

/-- The bounded convergence theorem: if `fᵢ → g` `E`-a.e. on `σ(a)` with `|fᵢ| ≤ C` `E`-a.e., then
`fᵢ(a) x → g(a) x` for every `x`, i.e. `fᵢ(a) → g(a)` in the strong operator topology. -/
theorem tendsto_bfc_apply_of_ae {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℂ → ℂ} (hf : ∀ i, MemLp (fun z : spectrum ℂ a ↦ f i z) ∞ ha.spectralMeasure.measure)
    (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure)
    {C : ℝ} (hC : ∀ᶠ i in l, ∀ᵐ z : spectrum ℂ a ∂ha.spectralMeasure.measure, ‖f i z‖ ≤ C)
    (hlim : ∀ᵐ z : spectrum ℂ a ∂ha.spectralMeasure.measure, Tendsto (f · z) l (𝓝 (g z)))
    (x : H) : Tendsto (fun i ↦ ha.bfc (f i) x) l (𝓝 (ha.bfc g x)) := by
  simp_rw [ha.bfc_eq_integral (hf _), ha.bfc_eq_integral hg]
  exact ha.spectralMeasure.tendsto_integral_toLp_apply hf hg hC hlim x

/-- The bounded convergence theorem: if `fᵢ → g` pointwise on `σ(a)` with `|fᵢ| ≤ C`, then
`fᵢ(a) x → g(a) x` for every `x`, i.e. `fᵢ(a) → g(a)` in the strong operator topology. -/
theorem tendsto_bfc_apply {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {f : ι → ℂ → ℂ}
    (hf : ∀ i, MemLp (fun z : spectrum ℂ a ↦ f i z) ∞ ha.spectralMeasure.measure)
    (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure)
    {C : ℝ} (hC : ∀ᶠ i in l, ∀ z ∈ spectrum ℂ a, ‖f i z‖ ≤ C)
    (hlim : ∀ z ∈ spectrum ℂ a, Tendsto (f · z) l (𝓝 (g z))) (x : H) :
    Tendsto (fun i ↦ ha.bfc (f i) x) l (𝓝 (ha.bfc g x)) :=
  ha.tendsto_bfc_apply_of_ae hf hg (hC.mono fun _ hi ↦ ae_of_all _ fun z ↦ hi z z.2)
    (ae_of_all _ fun z ↦ hlim z z.2) x

/-- The bounded convergence theorem as convergence in `H →Lₚₜ[ℂ] H`, the space of operators with
the topology of pointwise convergence (the strong operator topology). -/
theorem tendsto_toPointwiseConvergenceCLM_bfc {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → ℂ → ℂ} (hf : ∀ i, MemLp (fun z : spectrum ℂ a ↦ f i z) ∞ ha.spectralMeasure.measure)
    (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure)
    {C : ℝ} (hC : ∀ᶠ i in l, ∀ z ∈ spectrum ℂ a, ‖f i z‖ ≤ C)
    (hlim : ∀ z ∈ spectrum ℂ a, Tendsto (f · z) l (𝓝 (g z))) :
    Tendsto (fun i ↦ toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (ha.bfc (f i))) l
      (𝓝 (toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (ha.bfc g))) :=
  PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.2 (ha.tendsto_bfc_apply hf hg hC hlim)

/-! ### Self-adjointness, positivity and projections -/

/-- `f(a)` is self-adjoint if `f` is real on `σ(a)`. -/
lemma isSelfAdjoint_bfc (hf : ∀ z ∈ spectrum ℂ a, star (f z) = f z) :
    IsSelfAdjoint (ha.bfc f) := by
  by_cases hfm : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [IsSelfAdjoint, ← ha.bfc_star hfm]
    exact ha.bfc_congr hf
  · rw [ha.bfc_of_not_memLp hfm]
    exact .zero _

/-- `f(a)` is nonnegative if `f` is nonnegative on `σ(a)`. -/
lemma bfc_nonneg (hf : ∀ z ∈ spectrum ℂ a, 0 ≤ f z) : 0 ≤ ha.bfc f := by
  by_cases hfm : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  swap
  · rw [ha.bfc_of_not_memLp hfm]
  -- `f = star g * g` on `σ(a)`, with `g = √f`.
  set g : ℂ → ℂ := fun z ↦ (Real.sqrt (f z).re : ℂ)
  have hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure := by
    refine ((memLp_top_const (1 : ℂ)).add hfm).of_le ?_ (ae_of_all _ fun z ↦ ?_)
    · exact (by fun_prop : Continuous fun w : ℂ ↦ (Real.sqrt w.re : ℂ)).comp_aestronglyMeasurable
        hfm.aestronglyMeasurable
    · have h0 := hf z z.2
      rw [Pi.add_apply, ← Complex.re_eq_norm.2 (add_nonneg zero_le_one h0), Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.add_re, Complex.one_re]
      nlinarith [Real.sq_sqrt (Complex.nonneg_iff.1 h0).1, Real.sqrt_nonneg (f z).re]
  have hfg : ha.bfc f = star (ha.bfc g) * ha.bfc g := by
    rw [← ha.bfc_star hg, ← ha.bfc_mul hg.star hg]
    refine ha.bfc_congr fun z hz ↦ ?_
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 (hf z hz)
    simp only [g, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hre]
    exact Complex.ext rfl (by simp [him])
  rw [hfg]
  exact star_mul_self_nonneg _

/-- The Borel functional calculus is monotone on real functions. -/
lemma bfc_mono (h : ∀ z ∈ spectrum ℂ a, f z ≤ g z)
    (hf : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure)
    (hg : MemLp (fun z : spectrum ℂ a ↦ g z) ∞ ha.spectralMeasure.measure) :
    ha.bfc f ≤ ha.bfc g := by
  rw [← sub_nonneg, ← ha.bfc_sub hg hf]
  exact ha.bfc_nonneg fun z hz ↦ sub_nonneg.2 (h z hz)

/-- `f(a)` is an orthogonal projection if `f` takes values in `{0, 1}` on `σ(a)`. -/
lemma isStarProjection_bfc (hf : ∀ z ∈ spectrum ℂ a, IsStarProjection (f z)) :
    IsStarProjection (ha.bfc f) := by
  refine ⟨?_, ha.isSelfAdjoint_bfc fun z hz ↦ (hf z hz).isSelfAdjoint⟩
  by_cases hfm : MemLp (fun z : spectrum ℂ a ↦ f z) ∞ ha.spectralMeasure.measure
  · rw [IsIdempotentElem, ← ha.bfc_mul hfm hfm]
    exact ha.bfc_congr fun z hz ↦ (hf z hz).isIdempotentElem
  · rw [ha.bfc_of_not_memLp hfm]
    exact .zero

/-- `f(a)` lies in every von Neumann algebra containing `a`. -/
theorem bfc_mem_vonNeumannAlgebra {M : VonNeumannAlgebra H} (haM : a ∈ M) (f : ℂ → ℂ) :
    ha.bfc f ∈ M := by
  rw [← SetLike.mem_coe, ← M.centralizer_centralizer]
  exact fun S hS ↦ (ha.commute_bfc (hS a haM).symm f).eq

/-! ### Uniqueness -/

/-- **Uniqueness of the Borel functional calculus**: an assignment `Φ` of operators to functions
which is linear on bounded measurable functions, extends the continuous functional calculus, and
satisfies the bounded convergence theorem in the weak operator topology (for bounded measurable
`fₙ → g` pointwise on `σ(a)`), agrees with the Borel functional calculus on functions which are
measurable and bounded on `σ(a)`. -/
theorem eq_bfc {Φ : (ℂ → ℂ) → H →L[ℂ] H}
    (hadd : ∀ f g, Measurable f → Measurable g → (∃ C, ∀ z, ‖f z‖ ≤ C) →
      (∃ C, ∀ z, ‖g z‖ ≤ C) → Φ (f + g) = Φ f + Φ g)
    (hsmul : ∀ (c : ℂ) f, Measurable f → (∃ C, ∀ z, ‖f z‖ ≤ C) → Φ (c • f) = c • Φ f)
    (hcfc : ∀ f, Continuous f → Φ f = cfc f a)
    (hlim : ∀ (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (C : ℝ), (∀ n, Measurable (f n)) → Measurable g →
      (∀ n z, ‖f n z‖ ≤ C) → (∀ z ∈ spectrum ℂ a, Tendsto (f · z) atTop (𝓝 (g z))) →
      ∀ x y, Tendsto (fun n ↦ ⟪x, Φ (f n) y⟫_ℂ) atTop (𝓝 ⟪x, Φ g y⟫_ℂ))
    (hf : Measurable f) {C : ℝ} (hC : ∀ z ∈ spectrum ℂ a, ‖f z‖ ≤ C) :
    Φ f = ha.bfc f := by
  have hσ : IsClosed (spectrum ℂ a) := spectrum.isClosed a
  -- `Φ f` only depends on the values of `f` on `σ(a)`.
  have hloc {F G : ℂ → ℂ} (hF : Measurable F) (hFC : ∃ C, ∀ z, ‖F z‖ ≤ C) (hG : Measurable G)
      (h : Set.EqOn F G (spectrum ℂ a)) : Φ F = Φ G := by
    obtain ⟨C, hC⟩ := hFC
    refine ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ tendsto_nhds_unique
      tendsto_const_nhds (hlim (fun _ ↦ F) G C (fun _ ↦ hF) hG (fun _ ↦ hC) (fun z hz ↦ ?_) x y)
    simp only [h hz]
    exact tendsto_const_nhds
  -- The extension by zero of functions on `σ(a)`.
  let ext (g : spectrum ℂ a → ℂ) : ℂ → ℂ := Function.extend Subtype.val g 0
  have ext_apply (g : spectrum ℂ a → ℂ) (z : ℂ) (hz : z ∈ spectrum ℂ a) : ext g z = g ⟨z, hz⟩ :=
    Subtype.val_injective.extend_apply _ _ (⟨z, hz⟩ : spectrum ℂ a)
  have ext_meas {g : spectrum ℂ a → ℂ} (hg : Measurable g) : Measurable (ext g) :=
    (MeasurableEmbedding.subtype_coe hσ.measurableSet).measurable_extend hg measurable_const
  have norm_ext_le {g : spectrum ℂ a → ℂ} {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) (z : ℂ) :
      ‖ext g z‖ ≤ max C 0 := by
    by_cases hz : z ∈ spectrum ℂ a
    · rw [ext_apply g z hz]
      exact (hC _).trans (le_max_left _ _)
    · have h0 : ext g z = 0 := Function.extend_apply' g (0 : ℂ → ℂ) z fun ⟨w, hw⟩ ↦ hz (hw ▸ w.2)
      simp [h0]
  have ext_bdd {g : spectrum ℂ a → ℂ} {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
      ∃ C, ∀ z, ‖ext g z‖ ≤ C :=
    ⟨_, norm_ext_le hC⟩
  -- `⟪x, Φ g y⟫ = ∫ g dE_{x,y}` for `g` bounded and measurable on `σ(a)`.
  have key (x y : H) (g : spectrum ℂ a → ℂ) (hg : Measurable g) (hgC : ∃ C, ∀ z, ‖g z‖ ≤ C) :
      ⟪x, Φ (ext g) y⟫_ℂ = ∫ᶜ z, g z ∂(ha.cfcMeasure x y) := by
    refine (ComplexMeasure.exists_integral_eq_of_tendsto
      (L := fun g ↦ ⟪x, Φ (ext g) y⟫_ℂ) ?_ ?_ ?_).elim fun μ hμ ↦ ?_
    · intro g g' hg hg' ⟨C, hC⟩ ⟨D, hD⟩
      rw [hloc (ext_meas (hg.add hg')) (ext_bdd fun z ↦ (norm_add_le _ _).trans
          (add_le_add (hC z) (hD z))) ((ext_meas hg).add (ext_meas hg')) fun z hz ↦ ?_,
        hadd _ _ (ext_meas hg) (ext_meas hg') (ext_bdd hC) (ext_bdd hD), add_apply,
        inner_add_right]
      simp [ext_apply _ z hz]
    · intro c g hg ⟨C, hC⟩
      rw [hloc (ext_meas (hg.const_smul c)) (ext_bdd fun z ↦ (norm_smul_le c (g z)).trans
          (mul_le_mul_of_nonneg_left (hC z) (norm_nonneg c))) ((ext_meas hg).const_smul c)
          fun z hz ↦ ?_, hsmul _ _ (ext_meas hg) (ext_bdd hC), smul_apply, inner_smul_right]
      simp [ext_apply _ z hz]
    · intro f g C hf hC hlim'
      refine hlim _ _ _ (fun n ↦ ext_meas (hf n))
        (ext_meas (measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 hlim')))
        (fun n ↦ norm_ext_le (hC n)) (fun z hz ↦ ?_) x y
      simpa [ext_apply _ z hz] using hlim' ⟨z, hz⟩
    · have hμc : μ = ha.cfcMeasure x y := by
        refine ha.eq_cfcMeasure fun F ↦ ?_
        obtain ⟨G, hG⟩ := F.exists_restrict_eq hσ
        rw [hμ F F.continuous.measurable ⟨‖F‖, F.norm_coe_le_norm⟩,
          hloc (ext_meas F.continuous.measurable) (ext_bdd F.norm_coe_le_norm)
            G.continuous.measurable fun z hz ↦ (ext_apply F z hz).trans (congr($hG ⟨z, hz⟩)).symm,
          hcfc G G.continuous, cfc_apply G a ha G.continuous.continuousOn]
        congr
        ext z
        exact congr($hG z)
      rw [← hμc]
      exact (hμ g hg hgC).symm
  refine ContinuousLinearMap.ext fun y ↦ ext_inner_left ℂ fun x ↦ ?_
  have hfσ : Measurable fun z : spectrum ℂ a ↦ f z := hf.comp measurable_subtype_coe
  rw [ha.inner_bfc (ha.memLp_of_bound hf hC), ← key x y _ hfσ ⟨C, fun z ↦ hC z z.2⟩,
    hloc (ext_meas hfσ) (ext_bdd fun z ↦ hC z z.2) hf fun z hz ↦ ext_apply _ z hz]


end IsStarNormal
