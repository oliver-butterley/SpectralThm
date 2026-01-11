/-
Copyright (c) 2026 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.Order.OmegaCompletePartialOrder
/-!
# Inner partitions

Instead of working with partitions of a set `s`, we work with finite sets of disjoint sets
contained within `s` since the same value will be achieved in the supremum. The empty set is
forbidden so that partitions of disjoint sets are disjoint sets of sets.
-/

@[expose] public section

open Function

variable {X : Type*}

/-- An inner partition is a finite collection of pairwise disjoint measurable sets which are all
contained within a given set. Different to `Setoid.IsPartition` there is no requirement for the
union to be the entire set and the the number of partition elements is required to be finite.
Here `pred` is given so that all members `t ∈ P` satisfy `pred t`. If this is not needed,
one can take `fun _ ↦ True` as `pred`.
-/
structure IsInnerPart (s : Set X) (P : Finset (Set X)) {pred : Set X → Prop}
    (pred_inter : ∀ t₁ t₂ : Set X, pred t₁ → pred t₂ → pred (t₁ ∩ t₂)) where
  /-- Each partition element is contained within the ambient set -/
  subset : ∀ t ∈ P, t ⊆ s
  /-- Each partition element satisfies the specified property -/
  pred_of_mem : ∀ t ∈ P, pred t
  /-- The partition elements are pairwise disjoint -/
  disjoint : (P : Set (Set X)).PairwiseDisjoint id
  /-- No partition element is the empty set -/
  nonempty : ∀ p ∈ P, p.Nonempty

namespace IsInnerPart

variable {pred : Set X → Prop} (pred_inter : ∀ s t : Set X, pred s → pred t → pred (s ∩ t))

/-- An inner partition of `∅` is empty. -/
lemma eq_empty {P : Finset (Set X)} (hP : IsInnerPart ∅ P pred_inter) : P = ∅ := by
  obtain ⟨h, _, _, h'⟩ := hP
  refine Finset.eq_empty_of_forall_notMem ?_
  by_contra! hc
  obtain ⟨p, hp⟩ := hc
  exact (h' p hp).ne_empty (Set.subset_eq_empty (h p hp) rfl)

/-- If `P` is an inner partition of `s₁` satisfying `p` and if `s₁ ⊆ s₂`, then `P` is an inner
partition of `s₂`. -/
lemma mono {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) (P : Finset (Set X)) (hP : IsInnerPart s₁ P pred_inter) :
    IsInnerPart s₂ P pred_inter := by
  obtain ⟨h1, h2, h3, _⟩ := hP
  exact ⟨fun p hp ↦ subset_trans (h1 p hp) h, h2, h3, by simp_all⟩

open Classical in
/-- If the `s i` are pairwise disjoint sets and each `P i` is a partition of `s i` then the union of
the `P i` is a partition of `⋃ i, s i`. -/
lemma iUnion {s : ℕ → Set X} (hs : Pairwise (Disjoint on s))
    {P : ℕ → Finset (Set X)} (hP : ∀ i, IsInnerPart (s i) (P i) pred_inter) (n : ℕ) :
    IsInnerPart (⋃ i, s i) (Finset.biUnion (Finset.range n) P) pred_inter := by
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
    · have hp' := (hP i).1 t hp
      have hq' := (hP j).1 q hq
      simpa using Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · obtain ⟨i, hi, ht'⟩ : ∃ i < n, u ∈ P i := by simp_all
    exact ((hP i).nonempty) u ht'

/-- If `P`, `Q` are partitions of two disjoint sets then `P` and `Q` are disjoint. -/
lemma disjoint_of_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : IsInnerPart s P pred_inter) (hQ : IsInnerPart t Q pred_inter) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hc.ne_empty
  have := hst (hP.1 r <| hRP hr) (hQ.1 r <| hRQ hr)
  have hc := Set.subset_eq_empty this rfl
  have := hP.nonempty r (hRP hr)
  simp_all

open Classical in
/-- The restriction of a partition `P` to the set `t`. -/
noncomputable def restriction (t : Set X) (P : Finset (Set X)) : Finset (Set X) :=
  (P.image (fun p ↦ p ∩ t)).filter Set.Nonempty
/-- If `P` is a partition then the restriction of `P` to a set `t` is a partition of `t`. -/
lemma restriction_IsInnerPart {s t : Set X} {P : Finset (Set X)} (hs : IsInnerPart s P pred_inter)
    (ht : pred t) : IsInnerPart t (restriction t P) pred_inter := by
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

end IsInnerPart

section General

abbrev IsSetInnerPart (s : Set X) (P : Finset (Set X)) :=
  @IsInnerPart _ s P (fun _ ↦ True) (fun _ _ _ _ ↦ True.intro)

#check IsSetInnerPart

end General

section MeasurableSpace

variable [MeasurableSpace X]

abbrev IsMeasurableInnerPart (s : Set X) (P : Finset (Set X)) :=
  @IsInnerPart _ s P MeasurableSet (fun _ _ hs ht ↦ MeasurableSet.inter hs ht)

#check IsMeasurableInnerPart

end MeasurableSpace
