/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.MeasureTheory.VectorMeasure.Basic
/-!
# Subpartitions

Instead of working with partitions of a set `s`, we work with finite sets of disjoint sets
contained within `s` since the same value will be achieved in the supremum. The empty set is
forbidden so that partitions of disjoint sets are disjoint sets of sets.
-/

@[expose] public section

open Function

variable {X : Type*}

/-- A Subpartition is a finite collection of pairwise disjoint measurable sets which are all
contained within a given set. Different to `Setoid.IsPartition` there is no requirement for the
union to be the entire set and the the number of partition elements is required to be finite.
Here `pred` is given so that all members `t ∈ P` satisfy `pred t`. If this is not needed,
one can take `fun _ ↦ True` as `pred`.
-/
structure IsSubpartition (s : Set X) (P : Finset (Set X)) {pred : Set X → Prop}
    (pred_inter : ∀ t₁ t₂ : Set X, pred t₁ → pred t₂ → pred (t₁ ∩ t₂)) where
  /-- Each partition element is contained within the ambient set -/
  subset : ∀ t ∈ P, t ⊆ s
  /-- Each partition element satisfies the specified property -/
  pred_of_mem : ∀ t ∈ P, pred t
  /-- The partition elements are pairwise disjoint -/
  disjoint : (P : Set (Set X)).PairwiseDisjoint id
  /-- No partition element is the empty set -/
  nonempty : ∀ p ∈ P, p.Nonempty

namespace IsSubpartition

variable {pred : Set X → Prop} (pred_inter : ∀ s t : Set X, pred s → pred t → pred (s ∩ t))

/-- A Subpartition of `∅` is empty. -/
lemma eq_empty {P : Finset (Set X)} (hP : IsSubpartition ∅ P pred_inter) : P = ∅ := by
  obtain ⟨h, _, _, h'⟩ := hP
  refine Finset.eq_empty_of_forall_notMem ?_
  by_contra! hc
  obtain ⟨p, hp⟩ := hc
  exact (h' p hp).ne_empty (Set.subset_eq_empty (h p hp) rfl)

/-- If `P` is a Subpartition of `s₁` satisfying `p` and if `s₁ ⊆ s₂`, then `P` is a Subpartition of
`s₂`. -/
lemma mono {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) (P : Finset (Set X)) (hP : IsSubpartition s₁ P pred_inter) :
    IsSubpartition s₂ P pred_inter := by
  obtain ⟨h1, h2, h3, _⟩ := hP
  exact ⟨fun p hp ↦ subset_trans (h1 p hp) h, h2, h3, by simp_all⟩

open Classical in
/-- If the `s i` are pairwise disjoint sets and each `P i` is a subpartition of `s i` then the union
of finitely many of the `P i` is a subpartition of `⋃ i, s i`. -/
lemma iUnion {s : ℕ → Set X} (hs : Pairwise (Disjoint on s))
    {P : ℕ → Finset (Set X)} (hP : ∀ i, IsSubpartition (s i) (P i) pred_inter) (n : ℕ) :
    IsSubpartition (⋃ i, s i) (Finset.biUnion (Finset.range n) P) pred_inter := by
  refine ⟨fun u hu x hp ↦ ?_, fun t ht ↦ ?_, fun t ht q hq hpq _ hrp hrq ↦ ?_, fun u hu ↦ ?_⟩
  · simp only [Finset.mem_biUnion, Finset.mem_range] at hu
    obtain ⟨i, hi⟩ := hu
    rw [Set.mem_iUnion]
    use i
    exact (hP i).subset u hi.2 hp
  · obtain ⟨i, hi, hp⟩ : ∃ i < n, t ∈ P i := by simp_all
    exact (hP i).pred_of_mem t hp
  · obtain ⟨i, hi, hp⟩ : ∃ i < n, t ∈ P i := by simp_all
    obtain ⟨j, hj, hq⟩ : ∃ i < n, q ∈ P i := by simp_all
    obtain hc | hc : i = j ∨ i ≠ j := by omega
    · rw [hc] at hp
      simpa using Set.subset_eq_empty ((hP j).disjoint hp hq hpq hrp hrq) rfl
    · have hp' := (hP i).subset t hp
      have hq' := (hP j).subset q hq
      simpa using Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · obtain ⟨i, hi, ht'⟩ : ∃ i < n, u ∈ P i := by simp_all
    exact ((hP i).nonempty) u ht'

/-- If `P`, `Q` are partitions of two disjoint sets then `P` and `Q` are disjoint. -/
lemma disjoint_of_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : IsSubpartition s P pred_inter) (hQ : IsSubpartition t Q pred_inter) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hc.ne_empty
  have := hst (hP.subset r <| hRP hr) (hQ.subset r <| hRQ hr)
  have hc := Set.subset_eq_empty this rfl
  have := hP.nonempty r (hRP hr)
  simp_all

open Classical in
/-- The restriction of a partition `P` to the set `t`. -/
noncomputable def restriction (t : Set X) (P : Finset (Set X)) : Finset (Set X) :=
  (P.image (fun p ↦ p ∩ t)).filter Set.Nonempty

/-- If `P` is a partition then the restriction of `P` to a set `t` is a partition of `t`. -/
lemma restriction_of_pred {s t : Set X} {P : Finset (Set X)}
    (hs : IsSubpartition s P pred_inter) (ht : pred t) :
    IsSubpartition t (restriction t P) pred_inter := by
  classical
  refine ⟨fun _ h ↦ ?_, fun r hr ↦ ?_, fun _ hr _ hr' ↦ ?_, fun _ hp ↦ ?_⟩
  · obtain ⟨_, _, hp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    simp [← hp]
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    simpa [← hp'] using pred_inter p t (hs.pred_of_mem p hp) ht
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr').1
    rw [← hp', ← hq']
    intro hpqt _ h h'
    have hpq : p ≠ q := fun h ↦ hpqt (congrFun (congrArg Inter.inter h) t)
    exact hs.disjoint hp hq hpq (Set.subset_inter_iff.mp h).1 (Set.subset_inter_iff.mp h').1
  · refine Set.nonempty_coe_sort.mp ?_
    have := (Finset.mem_filter.mp hp).2
    exact Set.Nonempty.to_subtype this

end IsSubpartition

section General

abbrev IsSetSubpartition (s : Set X) (P : Finset (Set X)) :=
  @IsSubpartition _ s P (fun _ ↦ True) (fun _ _ _ _ ↦ True.intro)

#check IsSetSubpartition

end General

section MeasurableSpace

variable [MeasurableSpace X]

abbrev IsMeasurableSubpartition (s : Set X) (P : Finset (Set X)) :=
  @IsSubpartition _ s P MeasurableSet (fun _ _ hs ht ↦ MeasurableSet.inter hs ht)

#check IsMeasurableSubpartition

end MeasurableSpace

open ENNReal

section weight

variable {X : Type*} [MeasurableSpace X] (f : Set X → ℝ≥0∞)

def hpM := (fun (s : Set X) (t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t)
  ↦ MeasurableSet.inter hs ht)

open Classical in
/-- If `s` is measurable then `var_aux s f` is the supremum over Subpartitions (`IsSubpartition`)
`P` of `s` of the quantity `∑ p ∈ P, f p`. If `s` is not measurable then it is set to `0`. -/
noncomputable def var_aux (s : Set X) :=
  if (MeasurableSet s) then ⨆ (P : Finset (Set X)) (_ : IsMeasurableSubpartition s P), ∑ p ∈ P, f p else 0

/-- `var_aux` of the empty set is equal to zero. -/
lemma var_aux_empty : var_aux f ∅ = 0 := by
  suffices ∀ s, IsMeasurableSubpartition ∅ s → ∑ p ∈ s, f p = 0 by
    simpa [var_aux]
  intro _ hP
  simp_all [IsSubpartition.eq_empty hpM hP]

/-- `var_aux` is monotone in terms of the (measurable) set. -/
lemma varAux_mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    var_aux f s₁ ≤ var_aux f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · simp only [var_aux, hs₁, reduceIte, hs₂]
    exact iSup_le_iSup_of_subset (IsSubpartition.mono hpM h)
  · simp [var_aux, hs₁]

lemma exists_isSubpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < var_aux f s) : ∃ P, IsMeasurableSubpartition s P ∧ a < ∑ p ∈ P, f p := by
  simp_all [var_aux, lt_iSup_iff]

lemma exists_isSubpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : NNReal} (hε : 0 < ε)
    (h : var_aux f s ≠ ⊤) : ∃ P, IsMeasurableSubpartition s P ∧ var_aux f s ≤ ∑ p ∈ P, f p + ε := by
  let ε' := min ε (var_aux f s).toNNReal
  have hε1 : ε' ≤ var_aux f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : var_aux f s ≠ 0 ∨ var_aux f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := var_aux f s - ε'
    have ha : a < var_aux f s := by exact ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP, hP'⟩ := exists_isSubpartition_sum_gt f hs ha
    refine ⟨P, hP, ?_⟩
    calc var_aux f s
      _ = a + ε' := (tsub_add_cancel_of_le hε1).symm
      _ ≤ ∑ p ∈ P, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP')
      _ ≤ ∑ p ∈ P, f p + ε := by gcongr
  · simp_rw [hw, zero_le, and_true]
    exact ⟨{ }, by simp, by simp, by simp, by simp⟩

lemma IsSubpartition.sum_le_varAux {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP : IsMeasurableSubpartition s P) : ∑ p ∈ P, f p ≤ var_aux f s := by
  simpa [var_aux, hs] using le_biSup (fun P ↦ ∑ p ∈ P, f p) hP

/-- A set function is subadditive if the value assigned to the union of disjoint sets is bounded
above by the sum of the values assigned to the individual sets. -/
def IsSubadditive (f : Set X → ℝ≥0∞) := ∀ (s : ℕ → Set X), (∀ i, MeasurableSet (s i)) →
  Pairwise (Disjoint on s) → f (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), f (s i)

/-- Given a partition `Q`, `∑ q ∈ Q, f q` is bounded by the sum of the `∑ q ∈ (P i), f q` where
the `P i` are the partitions formed by restricting to a disjoint set of sets `s i`. -/
lemma sum_part_le_tsum_sum_part (hf : IsSubadditive f) (hf' : f ∅ = 0) {s : ℕ → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) {Q : Finset (Set X)}
    (hQ : IsMeasurableSubpartition (⋃ i, s i) Q) : ∑ q ∈ Q, f q ≤ ∑' i, ∑ p ∈ (IsSubpartition.restriction (s i) Q), f p := by
  classical
  let P (i : ℕ) := IsSubpartition.restriction (s i) Q
  calc ∑ q ∈ Q, f q
    _ = ∑ q ∈ Q, f (⋃ i, q ∩ s i) := ?_
    _ ≤ ∑ q ∈ Q, ∑' i, f (q ∩ s i) := ?_
    _ = ∑' i, ∑ q ∈ Q, f (q ∩ s i) := ?_
    _ ≤ ∑' i, ∑ p ∈ (P i), f p := ?_
  · -- Each `q` is equal to the union of `q ∩ s i`.
    -- TO DO: This only needs one direction of the argument since subadditivity implies monotone.
    suffices h : ∀ q ∈ Q, q = ⋃ i, q ∩ s i by
      exact Finset.sum_congr rfl (fun q hq ↦ (by simp [← h q hq]))
    intro q hq
    ext x
    refine ⟨fun hx ↦ ?_, by simp_all⟩
    obtain ⟨_, hs⟩ := (hQ.1 q hq) hx
    obtain ⟨i, _⟩ := Set.mem_range.mp hs.1
    simp_all [Set.mem_iUnion_of_mem i]
  · -- Subadditivity of `f` since the `s i` are pairwise disjoint.
    suffices h : ∀ p ∈ Q, f (⋃ i, p ∩ s i) ≤ ∑' (i : ℕ), f (p ∩ s i) by exact Finset.sum_le_sum h
    intro p hp
    refine hf (fun i ↦ p ∩ s i) (fun i ↦ ?_) ?_
    · exact MeasurableSet.inter (hQ.pred_of_mem p hp) (hs i)
    · refine (Symmetric.pairwise_on (fun ⦃x y⦄ a ↦ Disjoint.symm a) fun i ↦ p ∩ s i).mpr ?_
      intro _ _ _
      exact Disjoint.inter_left' p (Disjoint.inter_right' p (hs' (by omega)))
  · -- Swapping the order of the sum.
    refine Eq.symm (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable))
  · -- By defintion of the restricted partition
    refine ENNReal.tsum_le_tsum (fun i ↦ ?_)
    calc ∑ q ∈ Q, f (q ∩ s i)
      _ = ∑ p ∈ (Finset.image (fun q ↦ q ∩ s i) Q), f p := by
        refine Eq.symm (Finset.sum_image_of_disjoint (by simp [hf']) ?_)
        intro _ hp _ hq hpq
        exact Disjoint.inter_left (s i) (Disjoint.inter_right (s i) (hQ.disjoint hp hq hpq))
      _ ≤  ∑ p ∈ P i, f p := by
        refine Finset.sum_le_sum_of_ne_zero (fun p hp hp' ↦ ?_)
        obtain hc | hc : p = ∅ ∨ ¬p = ∅ := eq_or_ne p ∅
        · simp [hc, hf'] at hp'
        · simp only [P, IsSubpartition.restriction, Finset.mem_filter, Finset.mem_image]
          obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp hp
          refine ⟨⟨q, hq, hq'⟩, ?_⟩
          exact Set.nonempty_iff_ne_empty.mpr hc

lemma IsSubpartition.sum_le_varAux_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (P : ℕ → Finset (Set X))
    (hP : ∀ (i : ℕ), IsMeasurableSubpartition (s i) (P i)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p ≤ var_aux f (⋃ i, s i) := by
  classical
  let Q := Finset.biUnion (Finset.range n) P
  have hQ : IsMeasurableSubpartition (⋃ i, s i) Q := by exact IsSubpartition.iUnion hpM hs' hP n
  calc
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ P i, f p := by simp
    _ = ∑ q ∈ Q, f q := by
      refine Eq.symm (Finset.sum_biUnion fun l _ m _ hlm ↦ ?_)
      exact IsSubpartition.disjoint_of_disjoint hpM (hs' hlm) (hP l) (hP m)
    _ ≤ var_aux f (⋃ i, s i) := by
      simpa using IsSubpartition.sum_le_varAux f (MeasurableSet.iUnion hs) hQ

lemma IsSubpartition.sum_le_varAux_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, var_aux f (s i) ≤ var_aux f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  wlog hn : n ≠ 0
  · simp [show n = 0 by omega]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : var_aux f (s i) ≠ ⊤ := by
    refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt ?_ hsnetop
    exact varAux_mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a)
  -- For each set `s i` we choose a partition `P i` such that, for each `i`,
  -- `var_aux f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_isSubpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, var_aux f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i), f p + ε) := by
      gcongr with i _
      exact (hP i).2
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p + ε' := by
      rw [Finset.sum_add_distrib]
      norm_cast
      simp [show n * ε = ε' by rw [mul_div_cancel₀ _ (by positivity)]]
    _ ≤ var_aux f (⋃ i, s i) + ε' := by
      have := IsSubpartition.sum_le_varAux_iUnion' f hs hs' P (fun i ↦ (hP i).1) n
      gcongr

lemma sum_le_tsum' {f : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ b < a, ∃ n, b < ∑ i ∈ Finset.range n, f i) : a ≤ ∑' i, f i := by
  refine le_of_forall_lt fun b hb ↦ ?_
  obtain ⟨n, hn⟩ := h b hb
  exact lt_of_lt_of_le hn (ENNReal.sum_le_tsum <| Finset.range n)

open Classical in
lemma var_aux_iUnion_le {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) (hf : IsSubadditive f) (hf' : f ∅ = 0) :
    var_aux f (⋃ i, s i) ≤ ∑' i, var_aux f (s i) := by
  refine sum_le_tsum' fun b hb ↦ ?_
  simp only [var_aux, MeasurableSet.iUnion hs, reduceIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ, hbQ⟩ := hb
  -- Take the partitions defined as intersection of `Q` and `s i`.
  let P (i : ℕ) := IsSubpartition.restriction (s i) Q
  have hP (i : ℕ) : IsMeasurableSubpartition (s i) (P i) := IsSubpartition.restriction_of_pred hpM hQ (hs i)
  have hP' := calc
    b < ∑ q ∈ Q, f q := hbQ
    _ ≤ ∑' i, ∑ p ∈ (P i), f p := by exact sum_part_le_tsum_sum_part f hf hf' hs hs' hQ
  have := tendsto_nat_tsum fun i ↦ ∑ p ∈ (P i), f p
  obtain ⟨n, hn, _⟩ := (((tendsto_order.mp this).1 b hP').and (Filter.Ici_mem_atTop 1)).exists
  use n
  calc
    b < ∑ i ∈ Finset.range n, ∑ p ∈ (P i), f p := hn
    _ ≤ ∑ i ∈ Finset.range n, var_aux f (s i) := by
      gcongr with i hi
      exact IsSubpartition.sum_le_varAux f (hs i) (hP i)

/-- Additivity of `variation_aux` for disjoint measurable sets. -/
lemma var_aux_iUnion (hf : IsSubadditive f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ var_aux f (s i)) (var_aux f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (eq_of_le_of_ge ?_ ?_)
  · exact IsSubpartition.sum_le_varAux_iUnion f hs hs'
  · exact var_aux_iUnion_le f hs hs' hf hf'

end weight

-- /-!
-- ## Definition of variation
-- -/

-- section variation

-- variable {X : Type*} [MeasurableSpace X]
-- variable {V : Type*} [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]

-- lemma isSubadditive_enorm_vectorMeasure (μ : VectorMeasure X V) : IsSubadditive (‖μ ·‖ₑ) := by
--   intro _ hs hs'
--   simpa [VectorMeasure.of_disjoint_iUnion hs hs'] using enorm_tsum_le_tsum_enorm

-- /-- The variation of a `VectorMeasure` as an `ℝ≥0∞`-valued `VectorMeasure`. -/
-- noncomputable def variation (μ : VectorMeasure X V) : VectorMeasure X ℝ≥0∞ where
--   measureOf' := var_aux (‖μ ·‖ₑ)
--   empty' := var_aux_empty (‖μ ·‖ₑ)
--   not_measurable' _ h := if_neg h
--   m_iUnion' := var_aux_iUnion (‖μ ·‖ₑ) (isSubadditive_enorm_vectorMeasure μ) (by simp)

-- end variation

-- end MeasureTheory.VectorMeasure
