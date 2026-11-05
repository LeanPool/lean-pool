/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChromaticIndexSpec
public import LeanPool.GoldbergSeymour.DensityCeil

/-!
# Density Lower Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem DensityLowerBound {V E : Type*} [Fintype V] [Fintype E]
    (G : LooplessMultigraph V E) : DensityCeil G ≤ ChromaticIndex G := by
  classical
  let k := ChromaticIndex G
  obtain ⟨phi, hproper, hfull⟩ := (ChromaticIndexSpec G).1
  have endpoint_card : ∀ e : E, (G.ends e).toFinset.card = 2 := by
    intro e
    apply Sym2.card_toFinset_of_not_isDiag
    intro hd
    exact G.loopless e ((G.ends e).diagElem hd) (Sym2.diag_diagElem hd).symm
  have matching_card : ∀ (U : Finset V), EligibleOddSet U → ∀ c : Fin k,
      2 * ((InternalEdges G U).filter (fun e => phi e = some c)).card ≤ U.card - 1 := by
    intro U hU c
    let edges := (InternalEdges G U).filter fun e => phi e = some c
    have edges_subset : edges ⊆ InternalEdges G U :=
      Finset.filter_subset _ _
    have disjoint_endpoints : ∀ ⦃e⦄, e ∈ edges → ∀ ⦃f⦄, f ∈ edges →
        e ≠ f → Disjoint (G.ends e).toFinset (G.ends f).toFinset := by
      intro e he f hf hef
      rw [Finset.disjoint_left]
      intro v hev hvf
      have heI := (Finset.mem_filter.mp he).1
      have hfI := (Finset.mem_filter.mp hf).1
      have hce := (Finset.mem_filter.mp he).2
      have hadj : AdjacentEdges G e f := ⟨v, (Sym2.mem_toFinset.mp hev), (Sym2.mem_toFinset.mp hvf)⟩
      have hne := hproper hef hadj hce
      exact hne ((Finset.mem_filter.mp hf).2)
    have union_card_for : ∀ s : Finset E, s ⊆ edges →
        (s.biUnion fun e => (G.ends e).toFinset).card = 2 * s.card := by
      intro s hs
      induction s using Finset.induction_on with
      | empty => simp
      | @insert e s hes ih =>
          rw [Finset.biUnion_insert]
          have hd : Disjoint (G.ends e).toFinset (s.biUnion fun f => (G.ends f).toFinset) := by
            rw [Finset.disjoint_left]
            intro v hev hvs
            obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvs
            have hde := disjoint_endpoints (hs (Finset.mem_insert_self e s))
              (hs (Finset.mem_insert_of_mem hf)) (by intro h; exact hes (by simpa [h] using hf))
            exact (Finset.disjoint_left.mp hde) hev hvf
          rw [Finset.card_union_of_disjoint hd, endpoint_card]
          calc
            2 + (s.biUnion fun e => (G.ends e).toFinset).card = 2 + 2 * s.card := by
              rw [ih (fun x hx => hs (Finset.mem_insert_of_mem hx))]
            _ = 2 * (insert e s).card := by
              rw [Finset.card_insert_of_notMem hes]
              omega
    have union_card := union_card_for edges (by intro e he; exact he)
    have union_subset : edges.biUnion (fun e => (G.ends e).toFinset) ⊆ U := by
      intro v hv
      obtain ⟨e, he, hev⟩ := Finset.mem_biUnion.mp hv
      have heI := (Finset.mem_filter.mp he).1
      exact (Finset.mem_filter.mp heI).2 v (Sym2.mem_toFinset.mp hev)
    have hcard : 2 * edges.card ≤ U.card := by
      rw [← union_card]
      exact Finset.card_le_card union_subset
    have hstrict : 2 * edges.card < U.card := by
      apply Nat.lt_of_le_of_ne hcard
      intro heq
      apply hU.2.not_two_dvd_nat
      refine ⟨edges.card, ?_⟩
      omega
    have heq : edges = (InternalEdges G U).filter (fun e => phi e = some c) := rfl
    rw [← heq]
    omega
  have total_card : ∀ (U : Finset V), EligibleOddSet U →
      2 * (InternalEdges G U).card ≤ k * (U.card - 1) := by
    intro U hU
    let colored := fun s : Finset (Fin k) =>
      (InternalEdges G U).filter (fun e => ∃ c ∈ s, phi e = some c)
    have recurrence : ∀ s : Finset (Fin k),
        2 * (colored s).card ≤ s.card * (U.card - 1) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [colored]
      | @insert c s hcs ih =>
          let old := colored s
          let fresh := (InternalEdges G U).filter (fun e => phi e = some c)
          have split : colored (insert c s) = old ∪ fresh := by
            ext e
            simp only [colored, old, fresh, Finset.mem_union, Finset.mem_filter,
              Finset.mem_insert]
            aesop
          have disj : Disjoint old fresh := by
            rw [Finset.disjoint_left]
            intro e he ho
            have ho' := (Finset.mem_filter.mp he).2
            have h1 := (Finset.mem_filter.mp ho).2
            let d := Classical.choose ho'
            have hd := (Classical.choose_spec ho').1
            have h2 := (Classical.choose_spec ho').2
            have : d = c := by
              have hc : some d = some c := by
                calc
                  some d = phi e := h2.symm
                  _ = some c := h1
              simpa only [Option.some.injEq] using hc
            change d ∈ s at hd
            rw [this] at hd
            exact hcs hd
          rw [split, Finset.card_union_of_disjoint disj]
          have hm := matching_card U hU c
          dsimp [old, fresh] at ih ⊢
          calc
            2 * ((colored s).card + fresh.card) =
                2 * (colored s).card + 2 * fresh.card := by omega
            _ ≤ s.card * (U.card - 1) + (U.card - 1) :=
              Nat.add_le_add ih (matching_card U hU c)
            _ = (insert c s).card * (U.card - 1) := by
              rw [Finset.card_insert_of_notMem hcs]
              simp [Nat.add_mul, Nat.add_comm]
    have hall : colored (Finset.univ : Finset (Fin k)) = InternalEdges G U := by
      ext e
      simp only [colored, Finset.mem_filter]
      aesop
    rw [← hall]
    simpa using (recurrence (Finset.univ : Finset (Fin k)))
  unfold DensityCeil
  rw [Nat.ceil_le]
  unfold Density
  dsimp
  rw [Finset.max'_le_iff]
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_image] at hx
  rcases hx with rfl | ⟨U, hU, rfl⟩
  · norm_num
  · have heligible := (Finset.mem_filter.mp hU).2
    have htotal := total_card U heligible
    dsimp [DensityValue]
    have hpos : (0 : ℚ) < (U.card - 1 : ℚ) := by
      have hu := heligible.1
      have hn : 1 < U.card := by omega
      have hnq : (1 : ℚ) < (U.card : ℚ) := by exact_mod_cast hn
      exact sub_pos.mpr hnq
    apply (div_le_iff₀ hpos).2
    change (2 * (InternalEdges G U).card : ℚ) ≤
      (k : ℚ) * (U.card - 1 : ℚ)
    have hcast : (U.card - 1 : ℚ) = (↑(U.card - 1) : ℚ) := by
      have hu := heligible.1
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    exact_mod_cast htotal

end GoldbergSeymour

end
