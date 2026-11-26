/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section1
import LeanPool.GraphMinor.GM12.Section4Cover
import LeanPool.GraphMinor.GM12.Section4ShortestChain
import LeanPool.GraphMinor.GM12.Section4Counting
import LeanPool.GraphMinor.GM12.Section4WalkMetric
import LeanPool.GraphMinor.GM12.Section4CircuitWalk
import LeanPool.GraphMinor.GM12.Section4CircuitMeet
import LeanPool.GraphMinor.GM11.Section6
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The circuit-chain distance calculation

This file proves the calculation in XII (4.1), page 248. Retain maximal
insides in the finite circuit cover, then choose a shortest intersection
chain. Nonconsecutive insides are disjoint, so each separator vertex is
counted at most twice. Traverse the circuit boundaries to witness the
metric bound. This spells out the sum-of-costs inequality without needing
a separate transfer of XI's restraint metric to the radial-walk metric.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM10 GM11 GM14 Hypergraph

universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S]

/-- The circuit-cover calculation in XII (4.1), page 248. The connected
set joins the two endpoints, and every circuit has its original vertices
in the same finite separator. -/
theorem distance_le_twice_separator_of_circuit_cover
    [ConnectedSpace S] {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    {ι : Type*} [Finite ι] (C : ι → Drawing S)
    (hC : ∀ i, (C i).IsCircuit) (hCs : ∀ i, (C i).IsSubdrawing K)
    (hCl : ∀ i, (C i).length < 2 * θ)
    {Z : Set S} (hZ : Z.Finite) (hCZ : ∀ i, (C i).V ∩ Γ.V ⊆ Z)
    {P : Set S} (hP : IsPreconnected P) (hcover : P ⊆ ⋃ i, ins (C i))
    {u v : S} (hu : u ∈ P) (hv : v ∈ P) (huΓ : u ∈ Γ.V) (hvΓ : v ∈ Γ.V) :
    tangleMetric Γ K ins θ {u} {v} ≤ 2 * Z.ncard := by
  classical
  by_cases hlarge : θ ≤ 2 * Z.ncard
  · exact (tangleMetric_le_order hK ins θ {u} {v}).trans hlarge
  let I := {i : ι // ∀ j, ins (C i) ⊆ ins (C j) → ins (C j) ⊆ ins (C i)}
  let M : I → Set S := fun i => ins (C i.val)
  have hcoverM : P ⊆ ⋃ i, M i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨j, hij, hj⟩ := exists_maximal_cover_member (fun i => ins (C i)) i
    exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hi⟩
  have hclosed : ∀ i : I, IsClosed (M i) := fun i =>
    (hd _ (hC i.val) (hCs i.val) (hCl i.val)).1.isClosed
  obtain ⟨a, ha⟩ := mem_iUnion.mp (hcoverM hu)
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hcoverM hv)
  have hreach := intersection_chain_of_finite_closed_cover M hclosed hP hcoverM
    ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
  obtain ⟨n, f, hf0, hflast, hmeet, hdisj⟩ := exists_irredundant_intersection_chain M hreach
  let D : Fin (n + 1) → Drawing S := fun i => C (f i).val
  have hDV : ∀ i : Fin n, ((D i.castSucc).V ∩ (D i.succ).V).Nonempty := by
    intro i
    exact common_vertex_of_maximal_insides hT hK hd
      (hC _) (hCs _) (hCl _) (hC _) (hCs _) (hCl _)
      ((f i.castSucc).property (f i.succ).val) ((f i.succ).property (f i.castSucc).val) (hmeet i)
  have hsum : ∑ i, ((D i).V ∩ Γ.V).ncard ≤ 2 * Z.ncard := by
    let F : Fin (n + 1) → Finset S := fun i =>
      ((D i).finite_V.subset (Set.inter_subset_left (t := Γ.V))).toFinset
    have hsub : ∀ i, F i ⊆ hZ.toFinset := by
      intro i x hx
      exact hZ.mem_toFinset.mpr (hCZ _ (((D i).finite_V.subset (Set.inter_subset_left (t
        := Γ.V))).mem_toFinset.mp hx))
    have hfd : ∀ i j : Fin (n + 1), i.val + 1 < j.val → Disjoint (F i) (F j) := by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      have hi := ((D i).finite_V.subset (Set.inter_subset_left (t := Γ.V))).mem_toFinset.mp hxi
      have hj := ((D j).finite_V.subset (Set.inter_subset_left (t := Γ.V))).mem_toFinset.mp hxj
      have hin : ∀ k : Fin (n + 1), (D k).V ⊆ ins (D k) := by
        intro k y hy
        have hdisc := hd _ (hC _) (hCs _) (hCl (f k).val)
        have hbd : subBd (ins (D k)) ⊆ ins (D k) :=
          GM11.subBd_subset_of_isClosed hdisc.1.isClosed
        rw [hdisc.2.1] at hbd
        exact hbd ((D k).V_subset_U hy)
      exact Set.disjoint_left.mp (hdisj i j hij) (hin i hi.1) (hin j hj.1)
    have hcount := chain_sum_card_le_twice_separator hZ.toFinset F hsub hfd
    simpa only [F, ← Set.ncard_eq_toFinset_card] using hcount
  obtain ⟨w, W, hWlen, hDC⟩ := closed_walk_covering_circuit_chain D
    (fun i => hC (f i).val) (fun i => hCs (f i).val) hDV
  have hlen : W.length = 2 * ∑ i, ((D i).V ∩ Γ.V).ncard := by
    rw [hWlen, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (circuit_length_eq_two_mul_ncard hK.2.1 (hC _) (hCs _)).1
  have hshort : W.length < 2 * θ := by omega
  have hcontains : ∀ i, ins (D i) ⊆ insWalk ins K W := by
    intro i x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨D i, ⟨hC _, hDC i⟩, hx⟩)
  have huD : u ∈ ins (D 0) := by
    change u ∈ M (f 0)
    rw [hf0]
    exact ha
  have hvD : v ∈ ins (D (Fin.last n)) := by
    change v ∈ M (f (Fin.last n))
    rw [hflast]
    exact hb
  have huc : IsCorrespondingAtom Γ K {u} {u} :=
    ⟨Or.inl (Or.inl ⟨u, huΓ, rfl⟩), Or.inl (Or.inl ⟨u, hK.2.1.2.1 huΓ, rfl⟩),
      Or.inl ⟨u, huΓ, rfl, rfl⟩⟩
  have hvc : IsCorrespondingAtom Γ K {v} {v} :=
    ⟨Or.inl (Or.inl ⟨v, hvΓ, rfl⟩), Or.inl (Or.inl ⟨v, hK.2.1.2.1 hvΓ, rfl⟩),
      Or.inl ⟨v, hvΓ, rfl, rfl⟩⟩
  exact (tangleMetric_le_of_walk huc hvc W hshort hlen
    (singleton_subset_iff.mpr (hcontains 0 huD))
    (singleton_subset_iff.mpr (hcontains (Fin.last n) hvD))).trans hsum

end GraphMinor.GM12
