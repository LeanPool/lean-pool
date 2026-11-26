/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ThreeDiscsForest
public import LeanPool.GraphMinor.GM12.Section3IntermediateRegion
import LeanPool.GraphMinor.GM12.Section3AmbientFeasibilityForest
import LeanPool.GraphMinor.GM12.Section3AuxiliaryDisc
import LeanPool.GraphMinor.GM12.Section3PuncturedForest
import LeanPool.GraphMinor.GM12.Section3EmptyBoundaryDisc
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM10.Section12
import Mathlib.Tactic.FinCases

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# The two-disc case of XII (3.2)

Choose the three-disc threshold and double it, then add one.
The intermediate-region lemma finds a region separated from both
prescribed regions by the original threshold. Draw the feasibility
forest first and place an auxiliary disc in that region away from
the forest. The new disc has no drawing vertices on its boundary.
The same forest retains its boundary connections, so the proved
three-disc case gives the required connected subdrawings. This is
the argument on page 247, with the auxiliary-disc avoidance made
explicit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14

universe u

/-- Graph Minors XII (3.2), page 247, for two prescribed discs.
The two prescribed regions are displayed explicitly. -/
theorem theorem_3_2_two_discs
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (z : ℕ) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (Δ r : Fin 2 → Set S) (p : ℕ) (Zs : Fin p → Set S),
      HasTangleMetric Γ θ T d → η ≤ θ →
      (∀ i, IsClosedDisc (Δ i)) → Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
      (∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
      (∀ i, r i ∈ Γ.R) → (∀ i, (r i ∩ Δ i).Nonempty) →
      (∀ i j, i ≠ j → η ≤ d (r i) (r j)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨η', hη'pos, hthree⟩ := theorem_3_2_three_discs_of_forest hS z
  refine ⟨2 * η' + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  intro Γ θ T d Δ r p Zs hm horder hΔ hdis havoid hr hrΔ hsep hfree hcount hcover hdisZ hfeasible
  have hfar := hsep 0 1 (by decide)
  obtain ⟨q, hq, hq0, _, hq1⟩ := exists_intermediate_region hS hm hη'pos (hr 0) (hr 1) hfar
  have hqfar : ∀ i : Fin 2, η' ≤ d (r i) q := by
    intro i
    fin_cases i
    · exact hq0
    · exact hq1
  have h91 := GM11.gm15_theorem_9_1 Γ θ T d hS inferInstance hm
  have hqne : ∀ i, q ≠ r i := by
    intro i heq
    have h := hqfar i
    rw [heq, h91.2.1 (r i) (Or.inr (hr i))] at h
    exact (Nat.not_succ_le_zero _ (hη'pos.trans h))
  have hZV : ∀ j, Zs j ⊆ Γ.V := by
    intro j x hx
    have hxZ : x ∈ discBoundaryVertices Γ Δ := hcover.subset (mem_iUnion.mpr ⟨j, hx⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxZ
    exact hi.1
  have hZbd : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i) := by
    intro j x hx
    have hxZ : x ∈ discBoundaryVertices Γ Δ := hcover.subset (mem_iUnion.mpr ⟨j, hx⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxZ
    exact mem_iUnion.mpr ⟨i, hi.2⟩
  obtain ⟨F, hFF, hFU, hFV, hFclasses⟩ := exists_ambient_feasibility_forest hS Δ hΔ hdis Zs
    (fun j => Γ.finite_V.subset (hZV j)) hZbd hfeasible
  obtain ⟨E, hE, hEq, hEU, hEF, hED⟩ := exists_auxiliary_disc_in_region hS Γ F Δ r hΔ
    havoid hr hrΔ hq hqne
  let Δ' : Fin 3 → Set S := Fin.cons E Δ
  let r' : Fin 3 → Set S := Fin.cons q r
  have hΔ' : ∀ i, IsClosedDisc (Δ' i) := Fin.forall_fin_succ.mpr ⟨hE, hΔ⟩
  have hdis' : Pairwise (fun i j => Disjoint (Δ' i) (Δ' j)) := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact False.elim (hij rfl)
      · intro _
        exact hED j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact (hED i).symm
      · intro hij
        exact hdis (fun he => hij (congrArg Fin.succ he))
  have hVE : Γ.V ∩ discBd E = ∅ := boundary_vertices_eq_empty_of_disc_disjoint Γ hEU
  have havoid' : ∀ i, Γ.U ∩ Δ' i = Γ.V ∩ discBd (Δ' i) := by
    refine Fin.forall_fin_succ.mpr ⟨?_, havoid⟩
    exact hEU.symm.inter_eq.trans hVE.symm
  have hr' : ∀ i, r' i ∈ Γ.R := Fin.forall_fin_succ.mpr ⟨hq, hr⟩
  have hrΔ' : ∀ i, (r' i ∩ Δ' i).Nonempty := by
    refine Fin.forall_fin_succ.mpr ⟨?_, hrΔ⟩
    obtain ⟨x, hx⟩ := hE.nonempty_discInt
    exact ⟨x, hEq hx.1, hx.1⟩
  have hsep' : ∀ i j, i ≠ j → η' ≤ d (r' i) (r' j) := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact False.elim (hij rfl)
      · intro _
        change η' ≤ d q (r j)
        rw [h91.2.2.2.1 q (Or.inr hq) (r j) (Or.inr (hr j))]
        exact hqfar j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact hqfar i
      · intro hij
        change η' ≤ d (r i) (r j)
        exact (Nat.le_add_right η' η' |>.trans (Nat.le_succ _)).trans
          (by simpa only [two_mul] using hsep i j (fun he => hij (congrArg Fin.succ he)))
  have hfree' : ∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ' i)) := by
    refine Fin.forall_fin_succ.mpr ⟨?_, hfree⟩
    change GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd E)
    rw [hVE]
    exact GM10.isFreeSet_empty _ _ _
  have hZeq : discBoundaryVertices Γ Δ' = discBoundaryVertices Γ Δ :=
    discBoundaryVertices_fin_cons_of_disjoint Γ Δ hEU
  have hcontacts := drawing_contact_fin_cons_of_disjoint F Δ hEF
  have hZbd' : (⋃ j, Zs j) ⊆ ⋃ i, discBd (Δ' i) := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hZbd j hj)
    exact mem_iUnion.mpr ⟨i.succ, hi⟩
  have hclasses' : ∀ j, ∀ x ∈ Zs j, ∀ y ∈ F.V ∩ ⋃ i, Δ' i,
      Nonempty (GraphWalk F.toGraph x y) ↔ y ∈ Zs j := by
    intro j x hx y hy
    exact hFclasses j x hx y (hcontacts.2.subset hy)
  obtain ⟨H, hHF, hHB, hclasses⟩ := exists_punctured_forest_of_ambient hS Δ' hΔ' hdis' Zs F hFF
    (hcontacts.1.trans hFU) (hcontacts.2.trans hFV) hZbd' hclasses'
  obtain ⟨hT, K, ins, hK, hd, heq⟩ := hm
  have hsepmetric : ∀ i j, i ≠ j → η' ≤ tangleMetric Γ K ins θ (r' i) (r' j) := by
    intro i j hij
    rw [← heq (r' i) (Or.inr (hr' i)) (r' j) (Or.inr (hr' j))]
    exact hsep' i j hij
  have hηorder : η' ≤ θ := (Nat.le_add_right η' η' |>.trans (Nat.le_succ _)).trans
    (by simpa only [two_mul] using horder)
  have hresult := hthree Γ K θ T ins Δ' r' p Zs hT.2.1 hT.2.2 hK hd hηorder hΔ' hdis' havoid'
    hr' hrΔ' hsepmetric hfree' (hZeq ▸ hcount) (hcover.trans hZeq.symm) hdisZ H hHF hHB hclasses
  rwa [hZeq] at hresult

end GraphMinor.GM12
