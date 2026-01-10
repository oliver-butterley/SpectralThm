/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Inner partitions

Instead of working with partitions of a set `s`, we work with finite sets of disjoint sets
contained within `s` since the same value will be achieved in the supremum. The empty set is
forbidden so that partitions of disjoint sets are disjoint sets of sets.
-/

open MeasureTheory BigOperators NNReal ENNReal Function Filter


-- section IsInnerPart

variable {X : Type*} [MeasurableSpace X]

-- TODO generalize this to any predicate `p : Set X → Prop`
-- assuming that `p` holds for union, intersection etc.

/-- An inner partition is a finite collection of pairwise disjoint measurable sets which are all
contained within a given set. Different to `Setoid.IsPartition` there is no requirement for the
union to be the entire set and the the number of partition elements is required to be finite. -/
structure InnerPart (s : Set X) where
  /-- The partition elements -/
  elems : Finset (Set X)
  /-- Each partition element is contained within the ambient set -/
  subset : ∀ t ∈ elems, t ⊆ s
  /-- Each partition element is measurable -/
  measurable : ∀ t ∈ elems, MeasurableSet t
  /-- The partition elements are pairwise disjoint -/
  disjoint : (elems : Set (Set X)).PairwiseDisjoint id
  /-- No partition element is the empty set -/
  nonempty : ∀ p ∈ elems, p.Nonempty

/-- An inner partition is a finite collection of pairwise disjoint measurable sets which are all
contained within a given set. Different to `Setoid.IsPartition` there is no requirement for the
union to be the entire set and the the number of partition elements is required to be finite. -/
def IsInnerPart (s : Set X) (P : Finset (Set X)) : Prop :=
    (∀ t ∈ P, t ⊆ s) ∧ (∀ t ∈ P, MeasurableSet t) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
    (∀ p ∈ P, p.Nonempty)

namespace IsInnerPart

lemma eq_empty {P : Finset (Set X)} (hP : IsInnerPart ∅ P) : P = ∅ := by
  obtain ⟨h, _, _, h'⟩ := hP
  refine Finset.eq_empty_of_forall_notMem ?_
  by_contra! hc
  obtain ⟨p, hp⟩ := hc
  simp_all [Set.subset_eq_empty (h p hp) rfl]

lemma isInnerPart_mono {s₁ s₂ : Set X} (h : s₁ ⊆ s₂) (P : Finset (Set X))
    (hP : IsInnerPart s₁ P) : IsInnerPart s₂ P := by
  obtain ⟨h1, h2, h3, _⟩ := hP
  exact ⟨fun p hp ↦ subset_trans (h1 p hp) h, h2, h3, by simp_all⟩

open Classical in
/-- If the `s i` are pairwise disjoint sets and each `P i` is a partition of `s i` then the union of
the `P i` is a partition of `⋃ i, s i`. -/
lemma iUnion {s : ℕ → Set X} (hs : Pairwise (Disjoint on s))
    {P : ℕ → Finset (Set X)} (hP : ∀ i, IsInnerPart (s i) (P i)) (n : ℕ) :
    IsInnerPart (⋃ i, s i) (Finset.biUnion (Finset.range n) P) := by
  suffices (∀ t, ∀ x < n, t ∈ P x → t ⊆ ⋃ i, s i) ∧ (∀ t, ∀ x < n, t ∈ P x → MeasurableSet t) ∧
      (⋃ x, ⋃ (_ : x < n), ((P x) : Set (Set X))).PairwiseDisjoint id
      ∧ ∀ p, ∀ x < n, p ∈ P x → p.Nonempty by
    simpa [IsInnerPart]
  refine ⟨fun p i _ hp ↦ ?_, fun p i _ hp ↦ ?_, fun p hp q hq hpq _ hrp hrq ↦ ?_, fun s i hn h ↦ ?_⟩
  · exact Set.subset_iUnion_of_subset i ((hP i).1 p hp)
  · exact (hP i).2.1 p hp
  · obtain ⟨i, hi, hp⟩ : ∃ i < n, p ∈ P i := by simp_all
    obtain ⟨j, hj, hq⟩ : ∃ i < n, q ∈ P i := by simp_all
    obtain hc | hc : i = j ∨ i ≠ j := by omega
    · rw [hc] at hp
      simpa using Set.subset_eq_empty ((hP j).2.2.1 hp hq hpq hrp hrq) rfl
    · have hp' := (hP i).1 p hp
      have hq' := (hP j).1 q hq
      simpa using Set.subset_eq_empty (hs hc (subset_trans hrp hp') (subset_trans hrq hq')) rfl
  · exact ((hP i).2.2.2 s) h

/-- If `P`, `Q` are partitions of two disjoint sets then `P` and `Q` are disjoint. -/
lemma disjoint_of_disjoint {s t : Set X} (hst : Disjoint s t) {P Q : Finset (Set X)}
    (hP : IsInnerPart s P) (hQ : IsInnerPart t Q) : Disjoint P Q := by
  intro R hRP hRQ
  simp only [Finset.bot_eq_empty, Finset.le_eq_subset, Finset.subset_empty]
  by_contra! hc
  obtain ⟨r, hr⟩ := Finset.Nonempty.exists_mem <| Finset.nonempty_iff_ne_empty.mpr hc.ne_empty
  have := hst (hP.1 r <| hRP hr) (hQ.1 r <| hRQ hr)
  have hc := Set.subset_eq_empty this rfl
  have := hP.2.2.2 r (hRP hr)
  simp_all

open Classical in
/-- The restriction of a partition `P` to the set `t`. -/
noncomputable def restriction (t : Set X) (P : Finset (Set X)) : Finset (Set X) :=
  (P.image (fun p ↦ p ∩ t)).filter Set.Nonempty
/-- If `P` is a partition then the restriction of `P` to a set `t` is a partition of `t`. -/
lemma restriction_isInnerPart {s t : Set X} {P : Finset (Set X)} (hs : IsInnerPart s P)
    (ht : MeasurableSet t) : IsInnerPart t (restriction t P) := by
  classical
  refine ⟨fun _ h ↦ ?_, fun r hr ↦ ?_, fun _ hr _ hr' ↦ ?_, fun _ hp ↦ ?_⟩
  · obtain ⟨_, _, hp⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
    simp [← hp]
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    simpa [← hp'] using MeasurableSet.inter (hs.2.1 p hp) ht
  · obtain ⟨p, hp, hp'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr).1
    obtain ⟨q, hq, hq'⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hr').1
    rw [← hp', ← hq']
    intro hpqt _ h h'
    have hpq : p ≠ q := fun h ↦ hpqt (congrFun (congrArg Inter.inter h) t)
    exact hs.2.2.1 hp hq hpq (Set.subset_inter_iff.mp h).1 (Set.subset_inter_iff.mp h').1
  · refine Set.nonempty_coe_sort.mp ?_
    have := (Finset.mem_filter.mp hp).2
    exact Set.Nonempty.to_subtype this

end IsInnerPart

#min_imports
