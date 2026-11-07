/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.BalancedGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.NormalCycleEdge
public import LeanPool.GoldbergSeymour.ScheideGraphHeightOdd

/-!
# Scheide Trunk Rotation Cycle

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

open scoped Sym2

private theorem helper_hends_75.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hheight : (3 : ℕ) ≤ N.height ∧ Odd
        N.height), (
    ∀ (i : Fin N.height), (↑i : ℕ) = (0 : ℕ) → NormalCycleEdge N i = e0) → (
    ∀ (i : Fin N.height), (↑i : ℕ) + (1 : ℕ) = N.height → NormalCycleEdge N i = N.closingEdge) → (
    ∀ (i : Fin N.height), (1 : ℕ) ≤ (↑i : ℕ) →
    ∀ (hbefore : (↑i : ℕ) + (1 : ℕ) < N.height), NormalCycleEdge N i = T.edge (⟨(↑i : ℕ),
    have hu : N.height ≤ T.length + (1 : ℕ) := N.height_upper; Decidable.byContradiction fun (a :
        ¬(↑i : ℕ) < T.length) =>
    by omega
    ⟩ : Fin T.length)) →
    ∀ (i : Fin N.height), G.ends (NormalCycleEdge N i) = s(T.vertex (Fin.castLE N.height_upper i),
        T.vertex (Fin.castLE N.height_upper (⟨((↑i : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑i :
        ℕ) + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(0 : ℕ) < N.height) =>
    by omega
    )⟩ : Fin N.height))) := by
  classical
  intro V E _ _ _ G k e0 phi T N hheight hcycle_zero hcycle_last hcycle_internal i
  by_cases hz : i.val = 0
  · let z : Fin T.length := ⟨0, T.positive⟩
    obtain ⟨a, ha⟩ := T.attaches z
    calc
      G.ends (NormalCycleEdge N i) = G.ends e0 :=
        congrArg G.ends (hcycle_zero i hz)
      _ = G.ends (T.edge z) :=
        congrArg G.ends T.first_edge.symm
      _ = s(T.vertex z.succ,
            T.vertex (Fin.castLT a (Nat.lt_trans a.isLt
              (Nat.succ_lt_succ z.isLt)))) := ha
      _ = s(T.vertex (Fin.castLE N.height_upper i),
            T.vertex (Fin.castLE N.height_upper
              ⟨(i.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
        apply Sym2.eq_iff.mpr
        right
        constructor
        · apply congrArg T.vertex
          apply Fin.ext
          simp [z, hz, Nat.mod_eq_of_lt (by omega : 1 < N.height)]
        · apply congrArg T.vertex
          apply Fin.ext
          simp [z, hz]
  · by_cases hl : i.val + 1 = N.height
    · calc
        G.ends (NormalCycleEdge N i) = G.ends N.closingEdge :=
          congrArg G.ends (hcycle_last i hl)
        _ = s(T.vertex N.lastIndex,
              T.vertex ⟨0, Nat.zero_lt_succ T.length⟩) := N.closing_ends
        _ = s(T.vertex (Fin.castLE N.height_upper i),
              T.vertex (Fin.castLE N.height_upper
                ⟨(i.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
          apply Sym2.eq_iff.mpr
          left
          constructor
          · apply congrArg T.vertex
            apply Fin.ext
            change N.lastIndex.val = i.val
            have hlastIndex := N.lastIndex_height
            omega
          · apply congrArg T.vertex
            apply Fin.ext
            simp [hl]
    · have hbefore : i.val + 1 < N.height := by omega
      let r : Fin T.length := ⟨i.val, by
        have hu := N.height_upper
        omega⟩
      calc
        G.ends (NormalCycleEdge N i) = G.ends (T.edge r) := by
          exact congrArg G.ends (hcycle_internal i (by omega) hbefore)
        _ = s(T.vertex ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩,
              T.vertex r.succ) :=
          N.trunk_edge_ends r (by simp [r]; omega) (by simp [r]; omega)
        _ = s(T.vertex (Fin.castLE N.height_upper i),
              T.vertex (Fin.castLE N.height_upper
                ⟨(i.val + 1) % N.height, Nat.mod_lt _ (by omega)⟩)) := by
          apply Sym2.eq_iff.mpr
          left
          constructor
          · apply congrArg T.vertex
            apply Fin.ext
            simp [r]
          · apply congrArg T.vertex
            apply Fin.ext
            change i.val + 1 = (i.val + 1) % N.height
            rw [Nat.mod_eq_of_lt hbefore]

private theorem helper_hinjective_193.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hheight : (3 : ℕ) ≤ N.height ∧ Odd
        N.height), (
    ∀ (i : Fin N.height), (↑i : ℕ) = (0 : ℕ) → NormalCycleEdge N i = e0) → (
    ∀ (i : Fin N.height), G.ends (NormalCycleEdge N i) = s(T.vertex (Fin.castLE N.height_upper i),
        T.vertex (Fin.castLE N.height_upper (⟨((↑i : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑i :
        ℕ) + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(0 : ℕ) < N.height) =>
    by
                        omega
    )⟩ : Fin N.height)))) → (
    ∀ (i : Fin N.height), (1 : ℕ) ≤ (↑i : ℕ) → phi (NormalCycleEdge N i) = some N.alpha ∨ phi
        (NormalCycleEdge N i) = some N.beta) → Function.Injective (NormalCycleEdge N) := by
  classical
  intro V E _ _ _ G k e0 phi T N hheight hcycle_zero hends hpositive_color i j hij
  by_cases iz : i.val = 0
  · by_cases jz : j.val = 0
    · apply Fin.ext
      omega
    · have hi0 : phi (NormalCycleEdge N i) = none :=
        (congrArg phi (hcycle_zero i iz)).trans N.global.1.2.2.2.2.1
      rcases hpositive_color j (by omega) with hj | hj
      · rw [← hij, hi0] at hj
        simp at hj
      · rw [← hij, hi0] at hj
        simp at hj
  · by_cases jz : j.val = 0
    · have hj0 : phi (NormalCycleEdge N j) = none :=
        (congrArg phi (hcycle_zero j jz)).trans N.global.1.2.2.2.2.1
      rcases hpositive_color i (by omega) with hi | hi
      · rw [hij, hj0] at hi
        simp at hi
      · rw [hij, hj0] at hi
        simp at hi
    · have hpairs := congrArg (fun e => G.ends e) hij
      rw [hends i, hends j] at hpairs
      rcases Sym2.eq_iff.mp hpairs with hd | hs
      · have hfirst : i.val = j.val := by
          have hv := T.vertex_injective hd.1
          simpa using congrArg Fin.val hv
        exact Fin.ext hfirst
      · have hi_next : (i.val + 1) % N.height = j.val := by
          have hv := T.vertex_injective hs.2
          simpa using congrArg Fin.val hv
        have hj_next : (j.val + 1) % N.height = i.val := by
          have hv := T.vertex_injective hs.1
          simpa using (congrArg Fin.val hv).symm
        by_cases il : i.val + 1 = N.height
        · have : j.val = 0 := by simpa [il] using hi_next.symm
          exact (jz this).elim
        · by_cases jl : j.val + 1 = N.height
          · have : i.val = 0 := by simpa [jl] using hj_next.symm
            exact (iz this).elim
          · rw [Nat.mod_eq_of_lt (by omega)] at hi_next
            rw [Nat.mod_eq_of_lt (by omega)] at hj_next
            omega

private theorem helper_hcolors_261.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0) (N : NormalGlobalMaximumTriple G k e0 phi T) (hheight : (3 : ℕ) ≤ N.height ∧ Odd
        N.height), (
    ∀ (i : Fin N.height), G.ends (NormalCycleEdge N i) = s(T.vertex (Fin.castLE N.height_upper i),
        T.vertex (Fin.castLE N.height_upper (⟨((↑i : ℕ) + (1 : ℕ)) % N.height, Nat.mod_lt ((↑i :
        ℕ) + (1 : ℕ)) (Decidable.byContradiction fun (a : ¬(0 : ℕ) < N.height) =>
    by
                        omega
    )⟩ : Fin N.height)))) → (
    ∀ (i : Fin N.height), (1 : ℕ) ≤ (↑i : ℕ) → phi (NormalCycleEdge N i) = some N.alpha ∨ phi
        (NormalCycleEdge N i) = some N.beta) → Function.Injective (NormalCycleEdge N) →
    let one : Fin N.height := (⟨(1 : ℕ), Decidable.byContradiction fun (a : ¬(1 : ℕ) < N.height)
        =>
    by omega
    ⟩ : Fin N.height); phi (NormalCycleEdge N one) = some N.alpha →
    ∀ (n : ℕ) (hnlt : n < N.height), (1 : ℕ) ≤ n → phi (NormalCycleEdge N (⟨n, hnlt⟩ : Fin
        N.height)) = if Odd n then some N.alpha else some N.beta := by
  classical
  intro V E _ _ _ G k e0 phi T N hheight hends hpositive_color hinjective one hone n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnlt hnpos
      by_cases hn : n = 1
      · subst n
        simpa [one] using hone
      · have hprevpos : 1 ≤ n - 1 := by omega
        have hprevlt : n - 1 < N.height := by omega
        have hprev := ih (n - 1) (by omega) hprevlt hprevpos
        have hcur := hpositive_color ⟨n, hnlt⟩ hnpos
        have hne : NormalCycleEdge N ⟨n - 1, hprevlt⟩ ≠
            NormalCycleEdge N ⟨n, hnlt⟩ := by
          intro heq
          have hh := hinjective heq
          have hv := congrArg Fin.val hh
          simp at hv
          omega
        have hadj : AdjacentEdges G
            (NormalCycleEdge N ⟨n - 1, hprevlt⟩)
            (NormalCycleEdge N ⟨n, hnlt⟩) := by
          refine ⟨T.vertex (Fin.castLE N.height_upper ⟨n, hnlt⟩), ?_, ?_⟩
          · rw [Incident, hends]
            have hmod : (n - 1 + 1) % N.height = n := by
              rw [Nat.sub_add_cancel hnpos, Nat.mod_eq_of_lt hnlt]
            simp [hmod]
          · rw [Incident, hends]
            simp
        have hproper := N.global.1.2.2.2.1
        by_cases hodd : Odd n
        · have hpreveven : ¬ Odd (n - 1) := by
            have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
            exact Nat.odd_add_one.mp (by simpa [hn_eq] using hodd)
          rw [ite_eq_right hpreveven] at hprev
          rw [ite_eq_left hodd]
          exact hcur.resolve_right (hproper hne hadj hprev)
        · have hprevodd : Odd (n - 1) := by
            by_contra hprev
            apply hodd
            have hn_eq : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
            rw [← hn_eq]
            exact Nat.odd_add_one.mpr hprev
          rw [ite_eq_left hprevodd] at hprev
          rw [ite_eq_right hodd]
          exact hcur.resolve_left (hproper hne hadj hprev)

theorem ScheideTrunkRotationCycle {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (N : NormalGlobalMaximumTriple G k e0 phi T)
    (hbalanced : BalancedGlobalMaximumTriple N) :
    3 ≤ N.height ∧
      Odd N.height ∧
        Function.Injective (NormalCycleEdge N) ∧
          (∀ i : Fin N.height,
              G.ends (NormalCycleEdge N i) =
                s(T.vertex (Fin.castLE N.height_upper i),
                  T.vertex
                    (Fin.castLE N.height_upper
                      ⟨(i.val + 1) % N.height, by
                        exact
                          Nat.mod_lt _
                            (by
                              have hp := N.height_lower
                              omega)⟩))) ∧
            ∀ i : Fin N.height,
              1 ≤ i.val →
                phi (NormalCycleEdge N i) = if Odd i.val then some N.alpha else some N.beta := by
  classical
  have hheight : 3 ≤ N.height ∧ Odd N.height := by
    rw [hbalanced.1]
    exact ScheideGraphHeightOdd G k e0 phi T N.global
  have hcycle_zero (i : Fin N.height) (hi : i.val = 0) :
      NormalCycleEdge N i = e0 := by
    simp [NormalCycleEdge, hi]
  have hcycle_last (i : Fin N.height) (hi : i.val + 1 = N.height) :
      NormalCycleEdge N i = N.closingEdge := by
    have hne : i.val ≠ 0 := by omega
    simp [NormalCycleEdge, hne, hi]
  have hcycle_internal (i : Fin N.height) (hpos : 1 ≤ i.val)
      (hbefore : i.val + 1 < N.height) :
      NormalCycleEdge N i = T.edge ⟨i.val, by
        have hu := N.height_upper
        omega⟩ := by
    have hne : i.val ≠ 0 := by omega
    have hnlast : i.val + 1 ≠ N.height := by omega
    simp [NormalCycleEdge, hne, hnlast]
  have hends := @helper_hends_75 V E inferInstance inferInstance inferInstance G k e0 phi T N
      hheight hcycle_zero hcycle_last hcycle_internal
  have hpositive_support : ∀ i : Fin N.height, 1 ≤ i.val →
      Sum.inr (NormalCycleEdge N i) ∈ N.closingPath.support := by
    intro i hi
    apply (N.closingPath_edges _).2
    by_cases hl : i.val + 1 = N.height
    · left
      exact hcycle_last i hl
    · right
      have hb : i.val + 1 < N.height := by omega
      let r : Fin T.length := ⟨i.val, by
        have hu := N.height_upper
        omega⟩
      refine ⟨r, by simpa [r], by simp [r]; omega, ?_⟩
      exact hcycle_internal i hi hb
  have hpositive_color : ∀ i : Fin N.height, 1 ≤ i.val →
      phi (NormalCycleEdge N i) = some N.alpha ∨
        phi (NormalCycleEdge N i) = some N.beta := by
    intro i hi
    have hmem := hpositive_support i hi
    obtain ⟨n, hn, hnle⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hmem
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      rw [N.closingPath.getVert_zero] at hn
      simp at hn
    have hnlt : n < N.closingPath.length := by
      by_contra hnot
      have heq : n = N.closingPath.length := by omega
      subst n
      rw [N.closingPath.getVert_length] at hn
      simp at hn
    have hadj := N.closingPath.adj_getVert_succ (i := n - 1) (by omega)
    have hnext : n - 1 + 1 = n := by omega
    rw [hnext, hn] at hadj
    cases hp : N.closingPath.getVert (n - 1) with
    | inl v =>
        rw [hp] at hadj
        have hinfo : Incident G v (NormalCycleEdge N i) ∧
            (phi (NormalCycleEdge N i) = some N.alpha ∨
              phi (NormalCycleEdge N i) = some N.beta) := by
          simpa [TwoColorIncidenceGraph] using hadj
        exact hinfo.2
    | inr f =>
        rw [hp] at hadj
        simp [TwoColorIncidenceGraph] at hadj
  have hinjective := @helper_hinjective_193 V E inferInstance inferInstance inferInstance G k e0 phi
      T N hheight hcycle_zero hends hpositive_color
  have hthree : 3 ≤ N.height := hheight.1
  let one : Fin N.height := ⟨1, by omega⟩
  have hone : phi (NormalCycleEdge N one) = some N.alpha := by
    have hc := hpositive_color one (by simp [one])
    apply hc.resolve_right
    intro hb
    have hinc : Incident G
        (T.vertex (Fin.castLE N.height_upper one))
        (NormalCycleEdge N one) := by
      rw [Incident, hends]
      simp
    have hp : N.beta ∈ PresentColors G phi
        (T.vertex (Fin.castLE N.height_upper one)) := by
      simp only [PresentColors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨NormalCycleEdge N one, hinc, hb⟩
    have hm : N.beta ∉ PresentColors G phi
        (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩) := by
      simpa [MissingColors] using N.beta_missing
    apply hm
    rw [show T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ =
        T.vertex (Fin.castLE N.height_upper one) by
      apply congrArg T.vertex
      apply Fin.ext
      simp [one]]
    exact hp
  have hcolors := @helper_hcolors_261 V E inferInstance inferInstance inferInstance G k e0 phi T N
      hheight hends hpositive_color hinjective hone
  exact ⟨hheight.1, hheight.2, hinjective, hends,
    fun i hi => hcolors i.val i.isLt hi⟩

end GoldbergSeymour

end
