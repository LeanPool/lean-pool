/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM15.Cited

import LeanPool.GraphMinor.GM09.Bridge

/-!
# Graph Minors XV, Section 6: Crooked Transactions

This file formalizes Section 6 ("Crooked transactions", pages 133–134) of N. Robertson and P. D.
Seymour, *Graph Minors. XV. Giant steps*, J. Combin. Theory Ser. B 68 (1996) 112–148:
- **Graph Minors XV, (6.1)** (`GM15Theorem61Statement`, `theorem_6_1`, page 134): if `(G, Ω)` has no
  crooked transaction of cardinality `π` (`π ≥ 2`, `π ≠ 3`), there is a segregation `S_seg` of `G`
  of type `(3π + 9, 1)` with `ΩBar ⊆ V(S_seg)` and a disc arrangement of it in a closed disc `Δ`
  with
  `Ω = α⁻¹(bd(Δ))`. Proved from Graph Minors IX, (11.11) (`GM09Theorem1111Statement`).
- **Corrected Graph Minors XV, (6.2)** (page 134, `GM15Theorem62Statement`). The first threshold
  term is `2 * τ₁`, correcting the printed subscript `i`. Every crooked transaction of
  cardinality `≥ (φ - 1)(2τ₁ + τ₂ - 7)` contains a crosscap transaction of size `φ`,
  a leap transaction of size `τ₁`, or a doublecross transaction of size `τ₂`. Proved from Graph
  Minors IX, (7.1) (`GM09Theorem71Statement`).
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14

universe u v

variable {α : Type u} {β : Type v}

/-- Statement of Graph Minors XV, (6.1) (page 134):
"Let $\pi \ge 2$ be an integer, with $\pi \ne 3$, and let $(G, \Omega)$ be a society with no
crooked transaction of cardinality $\pi$. Then there is a segregation $\mathcal{S}$ of $G$
of type $(3\pi + 9, 1)$ with $\bar{\Omega} \subseteq V(\mathcal{S})$, and an arrangement
$\alpha$ of $\mathcal{S}$ in a closed disc $\Delta$, such that $\Omega =
\alpha^{-1}(bd(\Delta))$." -/
def GM15Theorem61Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S : Society α β) (π : ℕ),
    2 ≤ π → π ≠ 3 →
    (∀ P_set : Set (Graph α β), S.IsCrookedTransaction P_set → P_set.ncard ≠ π) →
    ∃ (S_seg : Set (Society α β)) (k : ℕ) (A₀ : Society α β) (A : Fin k → Society α β)
      (Δ α₀ : Set EuclideanPlane) (α_disc : Fin k → Set EuclideanPlane)
      (α_pt : α → EuclideanPlane),
      S_seg = insert A₀ (range A) ∧
      IsSegregationOfType S.G (3 * π + 9) 1 S_seg ∧
      S.Ω.bar ⊆ segregationVertices S_seg ∧
      IsDiscArrangement S A₀ A Δ α₀ α_disc α_pt

/-- **Graph Minors XV, (6.1)** (page 134):
Every society `(G, Ω)` with no crooked transaction of cardinality `π` (`π ≥ 2`, `π ≠ 3`) admits a
segregation `S_seg` of `G` of type `(3π + 9, 1)` with `ΩBar ⊆ V(S_seg)` and an arrangement in a
closed
disc `Δ` with `Ω = α⁻¹(bd(Δ))`.
Proved from Graph Minors IX, (11.11) (`GM09Theorem1111Statement`). -/
theorem theorem_6_1_proof :
    GM15Theorem61Statement.{u, v} := by
  intro α β S π hπ2 hπ3 hno_crooked
  obtain ⟨k, A₀, A, ⟨hSocSeg, Δ, α₀, α_disc, α_pt, hDiscArr⟩, hA_le3, hA0_vortex⟩ :=
    GraphMinor.GM09.gm15_theorem_11_11.{u, v} S π hπ2 hπ3 hno_crooked
  let S_seg : Set (Society α β) := insert A₀ (range A)
  have hGraphSeg : IsGraphSegregation S.G S_seg := by
    refine ⟨(finite_range A).insert A₀, ?_, ?_, ?_, ?_⟩
    · rintro S₀ (rfl | ⟨i, rfl⟩)
      · exact hSocSeg.le_zero
      · exact hSocSeg.le_succ i
    · have hV_eq : ⋃ H ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, V(H) = V(S.G) := by
        rw [← hSocSeg.vertexSet_union]
        ext v
        simp only [S_seg, mem_iUnion, mem_image, mem_insert_iff, mem_range, mem_union]
        constructor
        · rintro ⟨H, ⟨S₀, rfl | ⟨i, rfl⟩, rfl⟩, hv⟩
          · exact Or.inl hv
          · exact Or.inr ⟨i, hv⟩
        · rintro (hv | ⟨i, hv⟩)
          · exact ⟨A₀.G, ⟨A₀, Or.inl rfl, rfl⟩, hv⟩
          · exact ⟨(A i).G, ⟨A i, Or.inr ⟨i, rfl⟩, rfl⟩, hv⟩
      have hE_eq : ⋃ H ∈ (fun S₀ : Society α β => S₀.G) '' S_seg, E(H) = E(S.G) := by
        rw [← hSocSeg.edgeSet_union]
        ext e
        simp only [S_seg, mem_iUnion, mem_image, mem_insert_iff, mem_range, mem_union]
        constructor
        · rintro ⟨H, ⟨S₀, rfl | ⟨i, rfl⟩, rfl⟩, he⟩
          · exact Or.inl he
          · exact Or.inr ⟨i, he⟩
        · rintro (he | ⟨i, he⟩)
          · exact ⟨A₀.G, ⟨A₀, Or.inl rfl, rfl⟩, he⟩
          · exact ⟨(A i).G, ⟨A i, Or.inr ⟨i, rfl⟩, rfl⟩, he⟩
      have hU_le : subgraphSUnion S.G ((fun S₀ : Society α β => S₀.G) '' S_seg) ≤ S.G :=
        restrict_le.trans (S.G.induce_le (by rw [hV_eq]))
      refine (Compatible.of_le_le hU_le le_rfl).ext ?_ ?_
      · simpa [subgraphSUnion] using hV_eq
      · ext e
        simp only [subgraphSUnion, edgeSet_restrict, mem_inter_iff, Graph.edgeSet_induce, hV_eq,
          hE_eq]
        refine ⟨fun h => h.2, fun he => ⟨?_, he⟩⟩
        obtain ⟨x, y, hlink⟩ := exists_isLink_of_mem_edgeSet he
        exact ⟨x, y, hlink, hlink.left_mem, hlink.right_mem⟩
    · rintro S₁ (rfl | ⟨i, rfl⟩) S₂ (rfl | ⟨j, rfl⟩) hne
      · exact (hne rfl).elim
      · exact hSocSeg.inter_zero_subset j
      · intro v ⟨hv1, hv2⟩
        have h := hSocSeg.inter_zero_subset i ⟨hv2, hv1⟩
        exact ⟨h.2, h.1⟩
      · have hij : i ≠ j := fun h => hne (congrArg A h)
        exact hSocSeg.inter_succ_subset i j hij
    · rintro S₁ (rfl | ⟨i, rfl⟩) S₂ (rfl | ⟨j, rfl⟩) hne
      · exact (hne rfl).elim
      · exact hSocSeg.disjoint_zero j
      · exact (hSocSeg.disjoint_zero i).symm
      · have hij : i ≠ j := fun h => hne (congrArg A h)
        exact hSocSeg.disjoint_succ hij
  have hType : IsSegregationOfType S.G (3 * π + 9) 1 S_seg := by
    refine ⟨hGraphSeg, ?_, ?_⟩
    · have hsub : {S₀ ∈ S_seg | 3 < S₀.Ω.bar.ncard} ⊆ {A₀} := by
        rintro S₀ ⟨rfl | ⟨i, rfl⟩, hgt⟩
        · exact mem_singleton S₀
        · exact (not_lt_of_ge (hA_le3 i) hgt).elim
      calc
        {S₀ ∈ S_seg | 3 < S₀.Ω.bar.ncard}.ncard ≤ ({A₀} : Set (Society α β)).ncard :=
          ncard_le_ncard hsub (finite_singleton A₀)
        _ = 1 := ncard_singleton A₀
    · rintro S₀ (rfl | ⟨i, rfl⟩) hgt
      · intro P_set hP
        exact hA0_vortex P_set hP
      · exact (not_lt_of_ge (hA_le3 i) hgt).elim
  have hBar : S.Ω.bar ⊆ segregationVertices S_seg := by
    intro v hv
    rcases hSocSeg.bar_subset_union hv with hv0 | hvi
    · exact mem_biUnion (mem_insert A₀ _) hv0
    · rcases mem_iUnion.mp hvi with ⟨i, hvi⟩
      exact mem_biUnion (mem_insert_of_mem A₀ ⟨i, rfl⟩) hvi
  exact ⟨S_seg, k, A₀, A, Δ, α₀, α_disc, α_pt, rfl, hType, hBar, hDiscArr⟩

/-- Corrected Graph Minors XV, (6.2) (page 134). The threshold uses $2\tau_1$ from IX (7.1) in
place of the printed $2\tau_i$. The corrected statement is:
"Let $\phi \ge 2$, $\tau_1 \ge 3$, $\tau_2 \ge 4$ be integers. Let $\mathcal{P}$ be a crooked
transaction in a society $(G, \Omega)$ such that $|\mathcal{P}| \ge (\phi - 1)(2\tau_1 +
\tau_2 - 7)$. Then there exists $\mathcal{P}' \subseteq \mathcal{P}$ such that either* (i)
*$|\mathcal{P}'| = \phi$ and $\mathcal{P}'$ is a crosscap transaction, or* (ii)
*$|\mathcal{P}'| = \tau_1$ and $\mathcal{P}'$ is a leap transaction, or* (iii)
*$|\mathcal{P}'| = \tau_2$ and $\mathcal{P}'$ is a doublecross transaction." -/
def GM15Theorem62Statement : Prop :=
  ∀ {α : Type u} {β : Type v} (S : Society α β) (φ τ₁ τ₂ : ℕ)
    (P_set : Set (Graph α β)),
    2 ≤ φ → 3 ≤ τ₁ → 4 ≤ τ₂ →
    S.IsCrookedTransaction P_set →
    (φ - 1) * (2 * τ₁ + τ₂ - 7) ≤ P_set.ncard →
    ∃ P' ⊆ P_set,
      (P'.ncard = φ ∧ S.IsCrosscapTransaction P') ∨
      (P'.ncard = τ₁ ∧ S.IsLeapTransaction P') ∨
      (P'.ncard = τ₂ ∧ S.IsDoublecrossTransaction P')

/-- Corrected Graph Minors XV, (6.2) (page 134), with $2\tau_1$ in the threshold.
Every crooked transaction of cardinality `≥ (φ - 1)(2τ₁ + τ₂ - 7)` contains a crosscap transaction
of cardinality `φ`, a leap transaction of cardinality `τ₁`, or a doublecross transaction of
cardinality `τ₂`.
Proved from Graph Minors IX, (7.1) (`GM09Theorem71Statement`). -/
theorem theorem_6_2_proof :
    GM15Theorem62Statement.{u, v} :=
  GraphMinor.GM09.gm15_theorem_7_1.{u, v}

end GraphMinor.GM15
