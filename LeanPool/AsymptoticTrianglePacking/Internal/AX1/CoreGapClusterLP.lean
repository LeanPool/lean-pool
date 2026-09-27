/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the **cluster capacity LP is an upper bound for `ν₃*` of the reduced graph**

`Nibble.AX1.cover_sum_le_cluster_capacity` (`Nibble.CoreGapCoverCapacity`) shows that the covering
sum of *any* family of block sub-triples with pairwise disjoint rectangles is at most

    (∑_{ordered cluster pairs (S,T)} d(S,T)·#S·#T) / 6.

This file proves the matching statement on the other side of
`Nibble.AX1.BlockCoverResidualFine` (`Nibble.CoreGapBlockCover`): the quantity the residual has to
dominate, `ν₃*` of the regularity-reduced graph, is bounded by the **same** expression.

* `Nibble.AX1.nu3star_regularityReduced_le_cluster_capacity` — the capacity bound;
* `Nibble.AX1.nu3star_regularityReduced_le_dense_cluster_capacity` — the same bound with the cluster
  pairs of density below a threshold `θ` discarded, at a cost of `θ·|V|² / 6`; this is the *discard
  step* of the block-allocation construction: only cluster pairs of density at least `θ` matter, so
  the block sizes `τ·d` of `Nibble.AX1.IsGridSubTriple` vary over a bounded range `[τθ, τ]`.

Both are proved from the per-pair capacity constraint
`Nibble.AX1.sum_fracPacking_cluster_pair_le` (`Nibble.CoreGapClusterCapacity`) together with the
fact that a triangle of the reduced graph has its three vertices in **three distinct parts**, so it
is counted by exactly the six ordered pairs of those parts.

Together with `Nibble.AX1.cover_sum_le_cluster_capacity` this says that the fine residual is
**exactly tight**: the family it asks for must realise the cluster capacity LP up to `ε|V|²`, with
no slack anywhere.

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapClusterCapacity
public import LeanPool.AsymptoticTrianglePacking.Internal.AX1.CoreGapCoverCapacity

/-! # CoreGapClusterLP -/

@[expose] public section

open Finset SimpleGraph Hypergraph Nibble.YusterE

namespace Nibble.AX1

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Two elementary facts about interedges -/

omit [Fintype V] [DecidableEq V] in
/-- The density-weighted area of a pair is its number of crossing edges. -/
theorem edgeDensity_mul_card_mul_card (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    (G.edgeDensity S T : ℝ) * (#S : ℝ) * (#T : ℝ) = (#(G.interedges S T) : ℝ) := by
  classical
  rcases Finset.eq_empty_or_nonempty S with rfl | hS
  · simp
  rcases Finset.eq_empty_or_nonempty T with rfl | hT
  · have hempty : G.interedges S ∅ = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro p hp
      rw [SimpleGraph.mem_interedges_iff] at hp
      exact absurd hp.2.1 (Finset.notMem_empty _)
    simp [hempty]
  have hS0 : (0 : ℝ) < (#S : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  have hT0 : (0 : ℝ) < (#T : ℝ) := by exact_mod_cast Finset.card_pos.mpr hT
  have hd : ((G.edgeDensity S T : ℚ) : ℝ)
      = (#(G.interedges S T) : ℝ) / ((#S : ℝ) * (#T : ℝ)) := by
    rw [SimpleGraph.edgeDensity_def]
    push_cast
    ring
  rw [hd]
  field_simp

omit [Fintype V] [DecidableEq V] in
/-- Interedges are monotone in the graph. -/
theorem card_interedges_mono {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : H ≤ G) (S T : Finset V) : #(H.interedges S T) ≤ #(G.interedges S T) := by
  classical
  refine Finset.card_le_card ?_
  intro p hp
  rw [SimpleGraph.mem_interedges_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, h hp.2.2⟩

/-! ### Triangles of the reduced graph span three distinct parts -/

/-- Adjacent vertices of the regularity-reduced graph lie in **different** parts. -/
theorem regularityReduced_parts_ne (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {a b : V}
    (hab : (G.regularityReduced P ep de).Adj a b) {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (ha : a ∈ A) (hb : b ∈ B) : A ≠ B := by
  obtain ⟨-, U, hU, W, hW, haU, hbW, hUW, -, -⟩ := hab
  have hAU : A = U := P.eq_of_mem_parts hA hU ha haU
  have hBW : B = W := P.eq_of_mem_parts hB hW hb hbW
  rw [hAU, hBW]
  exact hUW

/-- **Each triangle of the reduced graph is charged to at least six ordered cluster pairs.** -/
theorem six_le_card_partPairs_of_mem_triangleHypergraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (univ : Finset V)) {ep de : ℝ} {T : Finset (Finset V)}
    (hT : T ∈ triangleHypergraphE (G.regularityReduced P ep de)) :
    6 ≤ #(P.parts.offDiag.filter
      (fun p => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T)) := by
  classical
  rw [triangleHypergraphE, Finset.mem_image] at hT
  obtain ⟨t, ht, rfl⟩ := hT
  rw [SimpleGraph.mem_cliqueFinset_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have hat : a ∈ ({a, b, c} : Finset V) := by simp
  have hbt : b ∈ ({a, b, c} : Finset V) := by simp
  have hct : c ∈ ({a, b, c} : Finset V) := by simp
  have hAB : (G.regularityReduced P ep de).Adj a b := ht.1 hat hbt hab
  have hAC : (G.regularityReduced P ep de).Adj a c := ht.1 hat hct hac
  have hBC : (G.regularityReduced P ep de).Adj b c := ht.1 hbt hct hbc
  obtain ⟨A, hAmem, haA⟩ := P.exists_mem (Finset.mem_univ a)
  obtain ⟨B, hBmem, hbB⟩ := P.exists_mem (Finset.mem_univ b)
  obtain ⟨C, hCmem, hcC⟩ := P.exists_mem (Finset.mem_univ c)
  have hABne : A ≠ B := regularityReduced_parts_ne G P hAB hAmem hBmem haA hbB
  have hACne : A ≠ C := regularityReduced_parts_ne G P hAC hAmem hCmem haA hcC
  have hBCne : B ≠ C := regularityReduced_parts_ne G P hBC hBmem hCmem hbB hcC
  -- the six ordered pairs
  set s6 : Finset (Finset V × Finset V) := {(A, B), (B, A), (A, C), (C, A), (B, C), (C, B)}
    with hs6
  have hmem2 : ∀ {x y : V}, x ≠ y → x ∈ ({a, b, c} : Finset V) → y ∈ ({a, b, c} : Finset V) →
      ({x, y} : Finset V) ∈ ({a, b, c} : Finset V).powersetCard 2 := by
    intro x y hxy hx hy
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simpa using hxy), Finset.card_singleton]
  have hsub : s6 ⊆ P.parts.offDiag.filter
      (fun p => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ ({a, b, c} : Finset V).powersetCard 2)
      := by
    intro p hp
    simp only [hs6, Finset.mem_insert, Finset.mem_singleton] at hp
    rw [Finset.mem_filter, Finset.mem_offDiag]
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨hAmem, hBmem, hABne⟩, a, haA, b, hbB, hmem2 hab hat hbt⟩
    · exact ⟨⟨hBmem, hAmem, hABne.symm⟩, b, hbB, a, haA, hmem2 hab.symm hbt hat⟩
    · exact ⟨⟨hAmem, hCmem, hACne⟩, a, haA, c, hcC, hmem2 hac hat hct⟩
    · exact ⟨⟨hCmem, hAmem, hACne.symm⟩, c, hcC, a, haA, hmem2 hac.symm hct hat⟩
    · exact ⟨⟨hBmem, hCmem, hBCne⟩, b, hbB, c, hcC, hmem2 hbc hbt hct⟩
    · exact ⟨⟨hCmem, hBmem, hBCne.symm⟩, c, hcC, b, hbB, hmem2 hbc.symm hct hbt⟩
  have hcard : #s6 = 6 := by
    rw [hs6]
    rw [Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or];
            tauto),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or];
            tauto),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or];
            tauto),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or];
            tauto),
      Finset.card_insert_of_notMem
        (by simp only [Finset.mem_singleton, Prod.mk.injEq]; tauto),
      Finset.card_singleton]
  calc (6 : ℕ) = #s6 := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### The capacity bound -/

/-- **The cluster capacity LP caps `ν₃*` of the regularity-reduced graph.**  The right-hand side is
*exactly* the ceiling of the covering sum of a family of block sub-triples with disjoint rectangles
(`Nibble.AX1.cover_sum_le_cluster_capacity`), so the fine block-allocation residual carries no
slack. -/
theorem nu3star_regularityReduced_le_cluster_capacity
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V)) (ep de : ℝ) :
    nu3star (G.regularityReduced P ep de)
      ≤ (∑ p ∈ P.parts.offDiag, (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)) / 6 := by
  classical
  have hnn : ∀ p ∈ P.parts.offDiag,
      (0 : ℝ) ≤ (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) := by
    intro p _
    have : (0 : ℝ) ≤ (G.edgeDensity p.1 p.2 : ℝ) := by
      exact_mod_cast G.edgeDensity_nonneg p.1 p.2
    positivity
  have hsum0 : (0 : ℝ) ≤ ∑ p ∈ P.parts.offDiag,
      (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) := Finset.sum_nonneg hnn
  refine Real.sSup_le ?_ (by linarith)
  rintro x ⟨w, hw, rfl⟩
  set R : SimpleGraph V := G.regularityReduced P ep de with hR
  -- each ordered cluster pair is capped by its number of crossing edges
  have hcap : ∀ p ∈ P.parts.offDiag,
      ∑ T ∈ (triangleHypergraphE R).filter
          (fun T => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T), w T
        ≤ (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) := by
    intro p _
    have h1 := sum_fracPacking_cluster_pair_le R hw p.1 p.2
    have h2 : (#(R.interedges p.1 p.2) : ℝ) ≤ (#(G.interedges p.1 p.2) : ℝ) := by
      exact_mod_cast card_interedges_mono (G := G) (H := R) SimpleGraph.regularityReduced_le p.1 p.2
    rw [edgeDensity_mul_card_mul_card]
    linarith
  -- the six-fold charge
  have hswap : ∑ p ∈ P.parts.offDiag, ∑ T ∈ (triangleHypergraphE R).filter
        (fun T => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T), w T
      = ∑ T ∈ triangleHypergraphE R, ∑ p ∈ P.parts.offDiag.filter
        (fun p => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T), w T := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  have hlow : ∀ T ∈ triangleHypergraphE R,
      6 * w T ≤ ∑ _p ∈ P.parts.offDiag.filter
        (fun p => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T), w T := by
    intro T hT
    rw [Finset.sum_const, nsmul_eq_mul]
    have h6 := six_le_card_partPairs_of_mem_triangleHypergraph G P (ep := ep) (de := de) hT
    have h6' : (6 : ℝ) ≤ (#(P.parts.offDiag.filter
        (fun p => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T)) : ℝ) := by exact_mod_cast h6
    exact mul_le_mul_of_nonneg_right h6' (hw.1 T)
  have hstep : 6 * ∑ T ∈ triangleHypergraphE R, w T
      ≤ ∑ p ∈ P.parts.offDiag, ∑ T ∈ (triangleHypergraphE R).filter
          (fun T => ∃ x ∈ p.1, ∃ y ∈ p.2, ({x, y} : Finset V) ∈ T), w T := by
    rw [hswap, Finset.mul_sum]
    exact Finset.sum_le_sum hlow
  have hfin := le_trans hstep (Finset.sum_le_sum hcap)
  linarith

/-! ### Discarding the sparse cluster pairs -/

/-- The total area of the ordered cluster pairs is at most `|V|²`. -/
theorem sum_area_offDiag_le (P : Finpartition (univ : Finset V)) :
    ∑ p ∈ P.parts.offDiag, (#p.1 : ℝ) * (#p.2 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  classical
  have hsub : P.parts.offDiag ⊆ P.parts ×ˢ P.parts := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    exact Finset.mk_mem_product hp.1 hp.2.1
  have hnn : ∀ p ∈ P.parts ×ˢ P.parts, p ∉ P.parts.offDiag →
      (0 : ℝ) ≤ (#p.1 : ℝ) * (#p.2 : ℝ) := by
    intro p _ _; positivity
  have hle : ∑ p ∈ P.parts.offDiag, (#p.1 : ℝ) * (#p.2 : ℝ)
      ≤ ∑ p ∈ P.parts ×ˢ P.parts, (#p.1 : ℝ) * (#p.2 : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have hprod : ∑ p ∈ P.parts ×ˢ P.parts, (#p.1 : ℝ) * (#p.2 : ℝ)
      = (∑ S ∈ P.parts, (#S : ℝ)) * (∑ S ∈ P.parts, (#S : ℝ)) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_product]
  have hcard : ∑ S ∈ P.parts, (#S : ℝ) = (Fintype.card V : ℝ) := by
    have : ∑ S ∈ P.parts, #S = #(univ : Finset V) := by
      simpa using P.sum_card_parts
    have := congrArg (fun n : ℕ => (n : ℝ)) this
    push_cast at this
    simpa [Finset.card_univ] using this
  rw [hprod, hcard] at hle
  calc ∑ p ∈ P.parts.offDiag, (#p.1 : ℝ) * (#p.2 : ℝ)
      ≤ (Fintype.card V : ℝ) * (Fintype.card V : ℝ) := hle
    _ = (Fintype.card V : ℝ) ^ 2 := by ring

/-- **The capacity bound after discarding the sparse cluster pairs.**  Cluster pairs of density
below `θ` can be thrown away at a total cost of `θ·|V|²/6`: this is why the block-allocation
construction may assume that all cluster pairs it uses have density in `[θ, 1]`, so that the block
sizes `τ·d` of `Nibble.AX1.IsGridSubTriple` vary only within the bounded range `[τθ, τ]`. -/
theorem nu3star_regularityReduced_le_dense_cluster_capacity
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finpartition (univ : Finset V)) (ep de : ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    nu3star (G.regularityReduced P ep de)
      ≤ (∑ p ∈ P.parts.offDiag.filter (fun p => θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
            (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)) / 6
          + θ * (Fintype.card V : ℝ) ^ 2 / 6 := by
  classical
  have hsplit : ∑ p ∈ P.parts.offDiag,
        (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)
      = (∑ p ∈ P.parts.offDiag.filter (fun p => θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
            (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ))
        + ∑ p ∈ P.parts.offDiag.filter (fun p => ¬ θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
            (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hsparse : ∑ p ∈ P.parts.offDiag.filter (fun p => ¬ θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
        (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)
      ≤ θ * (Fintype.card V : ℝ) ^ 2 := by
    have hterm : ∀ p ∈ P.parts.offDiag.filter (fun p => ¬ θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
        (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)
          ≤ θ * ((#p.1 : ℝ) * (#p.2 : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hlt : (G.edgeDensity p.1 p.2 : ℝ) ≤ θ := le_of_lt (not_le.mp hp.2)
      have harea : (0 : ℝ) ≤ (#p.1 : ℝ) * (#p.2 : ℝ) := by positivity
      calc (G.edgeDensity p.1 p.2 : ℝ) * (#p.1 : ℝ) * (#p.2 : ℝ)
          = (G.edgeDensity p.1 p.2 : ℝ) * ((#p.1 : ℝ) * (#p.2 : ℝ)) := by ring
        _ ≤ θ * ((#p.1 : ℝ) * (#p.2 : ℝ)) := mul_le_mul_of_nonneg_right hlt harea
    have h1 := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at h1
    have h2 : ∑ p ∈ P.parts.offDiag.filter (fun p => ¬ θ ≤ (G.edgeDensity p.1 p.2 : ℝ)),
        ((#p.1 : ℝ) * (#p.2 : ℝ)) ≤ (Fintype.card V : ℝ) ^ 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => by positivity)) (sum_area_offDiag_le P)
    nlinarith [sum_area_offDiag_le P]
  have hmain := nu3star_regularityReduced_le_cluster_capacity G P ep de
  rw [hsplit] at hmain
  linarith

/-! ### Axiom check -/

section AxCheck




end AxCheck

end Nibble.AX1
