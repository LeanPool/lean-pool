/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4JoinedStarFamily
public import LeanPool.GraphMinor.GM12.Section4DisjointArcDiscs
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Vertex discs from disjoint residual edge halves

For XII (4.5), claim (1), page 253, each residual edge half
joins its vertex disc to a crossing disc. Thicken the disjoint
residual arcs to disjoint arm discs, preserving their two
endpoint contacts. Join the arms with the same vertex owner.
The resulting vertex discs meet the crossing discs exactly in
the assigned endpoint classes.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Disjoint residual arcs from vertex discs to a closed set
produce disjoint vertex discs with exactly their assigned
endpoint classes as contacts. This is the source feasibility
assembly of XII (4.5), claim (1), page 253. -/
theorem exists_residual_star_discs {S V ι : Type} [TopologicalSpace S]
    [T2Space S] [NormalSpace S] [ConnectedSpace S] [Finite V] [Finite ι]
    (hS : IsClosedSurface S) (A : V → Set S) (owner : ι → V)
    (a : ι → unitInterval → S) (Z : Set S)
    (hA : ∀ v, IsClosedDisc (A v))
    (hAA : ∀ v w, v ≠ w → Disjoint (A v) (A w))
    (hZ : IsClosed Z) (hAZ : ∀ v, Disjoint (A v) Z)
    (ha : ∀ i, IsArcMap (a i))
    (haa : ∀ i j, i ≠ j → Disjoint (range (a i)) (range (a j)))
    (ha0 : ∀ i, a i 0 ∈ discBd (A (owner i))) (ha1 : ∀ i, a i 1 ∈ Z)
    (hcontact : ∀ i, range (a i) ∩ (Z ∪ ⋃ v, A v) = {a i 0, a i 1}) :
    ∃ D : V → Set S, (∀ v, IsClosedDisc (D v)) ∧
      (∀ v w, v ≠ w → Disjoint (D v) (D w)) ∧
      (∀ v, A v ⊆ D v) ∧
      ∀ v, D v ∩ Z = {z | ∃ i, owner i = v ∧ a i 1 = z} := by
  classical
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite ι
  have hC : IsClosed (Z ∪ ⋃ v, A v) :=
    hZ.union (isClosed_iUnion_of_finite (fun v => (hA v).isClosed))
  obtain ⟨B, hB', hBB'⟩ := exists_disjoint_arc_discs hS (finite_univ : (univ : Set ι).Finite)
    a (fun i _ => ha i) (fun i _ j _ hij => haa i j hij) (Z ∪ ⋃ v, A v) hC
    (fun i _ => hcontact i)
  have hB := fun i => hB' i (mem_univ i)
  have hBB := fun i j hij => hBB' i (mem_univ i) j (mem_univ j) hij
  have hpA : ∀ i, a i 0 ∈ A (owner i) := fun i => discBd_subset _ (ha0 i)
  have hpB : ∀ i, a i 0 ∈ B i := fun i => (hB i).2.2.2 (mem_range_self 0)
  have hqB : ∀ i, a i 1 ∈ B i := fun i => (hB i).2.2.2 (mem_range_self 1)
  have howner : ∀ i v z, z ∈ B i → z ∈ A v → owner i = v := by
    intro i v z hzB hzA
    have hends := (hB i).2.1.subset ⟨hzB, Or.inr (mem_iUnion.mpr ⟨v, hzA⟩)⟩
    rcases hends with hz0 | hz1
    · have hpAv : a i 0 ∈ A v := hz0 ▸ hzA
      by_contra hne
      exact disjoint_left.mp (hAA (owner i) v hne) (hpA i) hpAv
    · have hz1' : z = a i 1 := mem_singleton_iff.mp hz1
      exact False.elim (disjoint_left.mp (hAZ v) hzA (hz1'.symm ▸ ha1 i))
  have hAB : ∀ i v, owner i = v → A v ∩ B i = {a i 0} := by
    intro i v hiv
    apply Subset.antisymm
    · rintro z ⟨hzA, hzB⟩
      have hends := (hB i).2.1.subset ⟨hzB, Or.inr (mem_iUnion.mpr ⟨v, hzA⟩)⟩
      rcases hends with hz0 | hz1
      · exact hz0
      · have hz1' : z = a i 1 := mem_singleton_iff.mp hz1
        exact False.elim (disjoint_left.mp (hAZ v) hzA (hz1'.symm ▸ ha1 i))
    · intro z hz
      have heq : z = a i 0 := mem_singleton_iff.mp hz
      rw [heq]
      exact ⟨hiv ▸ hpA i, hpB i⟩
  have hBZ : ∀ i, B i ∩ Z = {a i 1} := by
    intro i
    apply Subset.antisymm
    · rintro z ⟨hzB, hzZ⟩
      have hends := (hB i).2.1.subset ⟨hzB, Or.inl hzZ⟩
      rcases hends with hz0 | hz1
      · exact False.elim (disjoint_left.mp (hAZ (owner i)) (hpA i) (hz0 ▸ hzZ))
      · exact hz1
    · intro z hz
      have heq : z = a i 1 := mem_singleton_iff.mp hz
      rw [heq]
      exact ⟨hqB i, ha1 i⟩
  let F : V → Finset ι := fun v => Finset.univ.filter (fun i => owner i = v)
  have hF : ∀ v i, i ∈ F v ↔ owner i = v := by simp [F]
  have hstars : ∀ v w, v ≠ w → Disjoint (A v ∪ ⋃ i ∈ F v, B i) (A w ∪ ⋃ i ∈ F w, B i) := by
    intro v w hvw
    apply disjoint_left.mpr
    rintro z (hzAv | hzBs) (hzAw | hzCs)
    · exact disjoint_left.mp (hAA v w hvw) hzAv hzAw
    · obtain ⟨j, hj, hzBj⟩ := mem_iUnion₂.mp hzCs
      exact hvw ((howner j v z hzBj hzAv).symm.trans ((hF w j).mp hj))
    · obtain ⟨i, hi, hzBi⟩ := mem_iUnion₂.mp hzBs
      exact hvw (((hF v i).mp hi).symm.trans (howner i w z hzBi hzAw))
    · obtain ⟨i, hi, hzBi⟩ := mem_iUnion₂.mp hzBs
      obtain ⟨j, hj, hzBj⟩ := mem_iUnion₂.mp hzCs
      have hij : i ≠ j := by
        intro heq
        exact hvw (((hF v i).mp hi).symm.trans (heq ▸ (hF w j).mp hj))
      exact disjoint_left.mp (hBB i j hij) hzBi hzBj
  obtain ⟨D, hd, hdd, hsub, hDZ, -⟩ := exists_disjoint_joined_stars hS A B (fun i => a i 0) F
    hA (fun _ i _ => (hB i).1) (fun _ i _ j _ hij => hBB i j hij)
    (fun v i hi => hAB i v ((hF v i).mp hi))
    (fun v i hi => ((hF v i).mp hi) ▸ ha0 i)
    (fun _ i _ => (hB i).2.2.1 (Or.inl rfl)) hstars Z hZ
    (fun _ i _ hpZ => disjoint_left.mp (hAZ (owner i)) (hpA i) hpZ)
  refine ⟨D, hd, hdd, (fun v z hz => hsub v (Or.inl hz)), ?_⟩
  intro v
  rw [hDZ v]
  ext z
  constructor
  · rintro ⟨hzK, hzZ⟩
    rcases hzK with hzA | hzBs
    · exact False.elim (disjoint_left.mp (hAZ v) hzA hzZ)
    · obtain ⟨i, hi, hzBi⟩ := mem_iUnion₂.mp hzBs
      exact ⟨i, (hF v i).mp hi, (mem_singleton_iff.mp ((hBZ i).subset ⟨hzBi, hzZ⟩)).symm⟩
  · rintro ⟨i, hiv, hiz⟩
    rw [← hiz]
    exact ⟨Or.inr (mem_iUnion₂.mpr ⟨i, (hF v i).mpr hiv, hqB i⟩), ha1 i⟩

end GraphMinor.GM12
