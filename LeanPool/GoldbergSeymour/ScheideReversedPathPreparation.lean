/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Pow

/-!
# Preparatory lemmas for a reversed Kempe-path tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideReversedPathPreparation.helper_hparity_47.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (d : ℕ), p.length = (4 : ℕ) *
        d →
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e) := by
  classical
  intro V E G k e0 phi T alpha beta p d hd n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    constructor
    · intro he
      by_cases hn0 : n = 0
      · exact ⟨T.vertex ⟨0, Nat.zero_lt_succ T.length⟩, by simpa [hn0] using p.getVert_zero⟩
      · obtain ⟨w, hz⟩ := (ih (n - 1) (by omega) (by omega)).2 (by omega)
        have ha := p.adj_getVert_succ (i := n - 1) (by omega)
        have hn' : n - 1 + 1 = n := by omega
        rw [hn'] at ha
        rw [hz] at ha
        cases hc : p.getVert n with
        | inl v => exact ⟨v, rfl⟩
        | inr e =>
            exfalso
            have ha' : (TwoColorIncidenceGraph G phi alpha beta).Adj
                (Sum.inr w) (Sum.inr e) := hc ▸ ha
            simp [TwoColorIncidenceGraph] at ha'
    · intro ho
      obtain ⟨w, hz⟩ := (ih (n - 1) (by omega) (by omega)).1 (by omega)
      have ha := p.adj_getVert_succ (i := n - 1) (by omega)
      have hn' : n - 1 + 1 = n := by omega
      rw [hn'] at ha
      rw [hz] at ha
      cases hc : p.getVert n with
      | inl v =>
          exfalso
          have ha' : (TwoColorIncidenceGraph G phi alpha beta).Adj
              (Sum.inl w) (Sum.inl v) := hc ▸ ha
          simp [TwoColorIncidenceGraph] at ha'
      | inr e => exact ⟨e, rfl⟩

theorem ScheideReversedPathPreparation.helper_reversedVertex_injective_187.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (d : ℕ) (hd : p.length = (4 :
        ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                exact by
                  have := GoldbergSeymour.TreeSequence.positive T
                  exact by omega
    )).left (
    by omega
    ));
    let reversedVertex : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ if hi : (↑i : ℕ) =
        (0 : ℕ) then vertexAt (0 : Fin (m + (1 : ℕ))) else vertexAt (⟨m + (1 : ℕ) - (↑i : ℕ),
    by omega
    ⟩ : Fin (m + (1 : ℕ))); Function.Injective vertexAt → Function.Injective reversedVertex := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm vertexAt reversedVertex
      vertexAt_injective i j hij
  have hiLt := i.isLt
  have hjLt := j.isLt
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · apply Fin.ext
    omega
  · simp only [reversedVertex, dite_eq_left hi, dite_eq_right hj] at hij
    have hidx := vertexAt_injective hij
    have hidx' := congrArg Fin.val hidx
    apply Fin.ext
    change 0 = m + 1 - j.val at hidx'
    omega
  · simp only [reversedVertex, dite_eq_right hi, dite_eq_left hj] at hij
    have hidx := vertexAt_injective hij
    have hidx' := congrArg Fin.val hidx
    apply Fin.ext
    change m + 1 - i.val = 0 at hidx'
    omega
  · simp only [reversedVertex, dite_eq_right hi, dite_eq_right hj] at hij
    have hidx := vertexAt_injective hij
    have hidx' := congrArg Fin.val hidx
    apply Fin.ext
    change m + 1 - i.val = m + 1 - j.val at hidx'
    omega

theorem ScheideReversedPathPreparation.helper_reversedEdge_injective_212.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq E] (G :
        LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi : PartialEdgeColoring E k) (T : TreeSequence
        G e0), KTriple G k e0 phi →
    ∀ (alpha beta : Fin k) (p : (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex
        (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex
        (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (d : ℕ) (hd :
        p.length = (4 : ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m),
    let edgeAt : Fin m → E := fun (i : Fin m) ↦ Classical.choose ((hparity ((2 : ℕ) * (↑i : ℕ) +
        (1 : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                exact by
                  have := GoldbergSeymour.TreeSequence.positive T
                  exact by omega
    )).right (
    by omega
    )); (
    ∀ (i : Fin m),
    ∃ (c : Fin k), phi (edgeAt i) = some c) →
    let reversedEdge : Fin m → E := fun (i : Fin m) ↦ if hi : (↑i : ℕ) = (0 : ℕ) then e0 else
        edgeAt (⟨m - (↑i : ℕ),
    by omega
    ⟩ : Fin m); Function.Injective edgeAt → Function.Injective reversedEdge := by
  classical
  intro V E _ _ _ G k e0 phi T htriple alpha beta p d hd hparity m hm edgeAt edgeAt_colored
      reversedEdge edgeAt_injective i j hij
  have hiLt := i.isLt
  have hjLt := j.isLt
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
  · apply Fin.ext
    omega
  · simp only [reversedEdge, dite_eq_left hi, dite_eq_right hj] at hij
    exfalso
    have he0 := htriple.2.2.2.2.1
    obtain ⟨c, hc⟩ := edgeAt_colored ⟨m - j.val, by omega⟩
    rw [← hij] at hc
    rw [he0] at hc
    cases hc
  · simp only [reversedEdge, dite_eq_right hi, dite_eq_left hj] at hij
    exfalso
    have he0 := htriple.2.2.2.2.1
    obtain ⟨c, hc⟩ := edgeAt_colored ⟨m - i.val, by omega⟩
    rw [hij] at hc
    rw [he0] at hc
    cases hc
  · simp only [reversedEdge, dite_eq_right hi, dite_eq_right hj] at hij
    have hidx := edgeAt_injective hij
    have hidx' := congrArg Fin.val hidx
    apply Fin.ext
    change m - i.val = m - j.val at hidx'
    omega

theorem ScheideReversedPathPreparation.helper_edge_ends_239.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (d : ℕ) (hd : p.length = (4 :
        ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                exact by
                  have := GoldbergSeymour.TreeSequence.positive T
                  exact by omega
    )).left (
    by omega
    )); (
    ∀ (i : Fin (m + (1 : ℕ))), p.getVert ((2 : ℕ) * (↑i : ℕ)) = Sum.inl (vertexAt i)) →
    let edgeAt : Fin m → E := fun (i : Fin m) ↦ Classical.choose ((hparity ((2 : ℕ) * (↑i : ℕ) +
        (1 : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                exact by
                  have := GoldbergSeymour.TreeSequence.positive T
                  exact by omega
    )).right (
    by omega
    )); (
    ∀ (i : Fin m), p.getVert ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) = Sum.inr (edgeAt i)) →
        Function.Injective vertexAt →
    ∀ (i : Fin m), G.ends (edgeAt i) = s(vertexAt (⟨(↑i : ℕ),
    by omega
    ⟩ : Fin (m + (1 : ℕ))), vertexAt i.succ) := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm vertexAt vertexAt_eq edgeAt edgeAt_eq
      vertexAt_injective i
  have hleft := p.adj_getVert_succ (i := 2 * i.val) (by rw [hm]; omega)
  have hright := p.adj_getVert_succ (i := 2 * i.val + 1) (by rw [hm]; omega)
  rw [vertexAt_eq ⟨i.val, by omega⟩, edgeAt_eq i] at hleft
  rw [edgeAt_eq i] at hright
  have hstep : 2 * i.val + 1 + 1 = 2 * i.succ.val := by
    simp [Fin.succ]
    omega
  rw [hstep, vertexAt_eq i.succ] at hright
  have hleft' : Incident G (vertexAt ⟨i.val, by omega⟩) (edgeAt i) := by
    simpa [TwoColorIncidenceGraph] using hleft.1
  have hright' : Incident G (vertexAt i.succ) (edgeAt i) := by
    simpa [TwoColorIncidenceGraph] using hright.1
  have hne : vertexAt ⟨i.val, by omega⟩ ≠ vertexAt i.succ := by
    intro he
    have hi := vertexAt_injective he
    have hv := congrArg Fin.val hi
    have hv' : i.val = i.val + 1 := by simp [Fin.succ] at hv
    omega
  exact (Sym2.mem_and_mem_iff hne).mp ⟨hleft', hright'⟩

theorem ScheideReversedPathPreparation.helper_branch_272.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k)
      (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk
          (Sum.inl
            (T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ)))))
          (Sum.inl
            (T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ))))))
      (d : ℕ) (hd : p.length = (4 : ℕ) * d)
      (hparity :
        ∀ n ≤ p.length,
          (n % (2 : ℕ) = (0 : ℕ) → ∃ (v : V), p.getVert n = Sum.inl v) ∧
            (n % (2 : ℕ) = (1 : ℕ) → ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m) (hmpos : (2 : ℕ) ≤ m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦
      Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ))
              (by
                have := GoldbergSeymour.TreeSequence.positive T
                exact by
                  have := GoldbergSeymour.TreeSequence.positive T
                  exact by omega)).left
          (by omega));
    let edgeAt : Fin m → E := fun (i : Fin m) ↦
      Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ))
              (by
                have := GoldbergSeymour.TreeSequence.positive T
                exact by
                  have := GoldbergSeymour.TreeSequence.positive T
                  exact by omega)).right
          (by omega));
    let reversedVertex : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦
      if hi : (↑i : ℕ) = (0 : ℕ) then vertexAt (0 : Fin (m + (1 : ℕ)))
      else vertexAt (⟨m + (1 : ℕ) - (↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ)));
    let reversedEdge : Fin m → E := fun (i : Fin m) ↦
      if hi : (↑i : ℕ) = (0 : ℕ) then e0 else edgeAt (⟨m - (↑i : ℕ), by omega⟩ : Fin m);
    reversedVertex (⟨(0 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
        T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))) →
    reversedVertex (⟨(1 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
        T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ))) →
    ∀ (j : Fin m),
    (↑j : ℕ) = (0 : ℕ) →
    ∃ (i : Fin ((↑j : ℕ) + (1 : ℕ))),
    G.ends (reversedEdge j) = s(reversedVertex j.succ, reversedVertex (i.castLT (by omega))) := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm hmpos vertexAt edgeAt reversedVertex
      reversedEdge hvzero hvone j hj
  refine ⟨0, ?_⟩
  obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
  have iLt := i.isLt
  have hi0 : i.val = 0 := Nat.eq_zero_of_le_zero
    (Nat.le_of_lt_succ (by simp))
  have hiV : (i.castLT (Nat.lt_trans i.isLt (Nat.succ_lt_succ (show 0 < T.length by
      omega)))) =
      (⟨0, by omega⟩ : Fin (T.length + 1)) := by
    apply Fin.ext
    simp []
  have heq : T.edge ⟨0, T.positive⟩ = e0 := T.first_edge
  rw [hiV] at hi
  rw [heq] at hi
  have hj0 : j = (⟨0, by omega⟩ : Fin m) := Fin.ext (by simpa using hj)
  have hsucc : (⟨0, by omega⟩ : Fin m).succ = (⟨1, by omega⟩ : Fin (m + 1)) := by
    apply Fin.ext
    rfl
  rw [hj0, hsucc, hvone]
  simp only [reversedVertex]
  have hv0 := hvzero
  simp only [reversedVertex, dite_eq_left rfl] at hv0
  rw [hv0]
  simp [reversedEdge]
  simpa using hi

theorem ScheideReversedPathPreparation.helper_hends_364.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      (T : TreeSequence G e0),
    T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))) ≠
      T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ))) := by
  classical
  intro V E G e0 T h
  have hne : (⟨0, Nat.zero_lt_succ T.length⟩ : Fin (T.length + 1)) ≠
      ⟨1, Nat.succ_lt_succ T.positive⟩ := by
    intro heq
    have hv := congrArg Fin.val heq
    norm_num at hv
  exact hne (T.vertex_injective h)

theorem ScheideReversedPathPreparation.helper_hpos_373.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))) ≠ T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ))) → (0 : ℕ) < p.length := by
  classical
  intro V E G k e0 phi T alpha beta p hends
  by_contra hz
  have hz0 : p.length = 0 := Nat.eq_zero_of_not_pos hz
  have heq := SimpleGraph.Walk.eq_of_length_eq_zero hz0
  apply hends
  simpa using heq

theorem ScheideReversedPathPreparation.helper_edgeAt_colored_392.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (d : ℕ) (hd : p.length = (4 :
        ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).left (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )); (
    ∀ (i : Fin (m + (1 : ℕ))), p.getVert ((2 : ℕ) * (↑i : ℕ)) = Sum.inl (vertexAt i)) →
    let edgeAt : Fin m → E := fun (i : Fin m) ↦ Classical.choose ((hparity ((2 : ℕ) * (↑i : ℕ) +
        (1 : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).right (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )); (
    ∀ (i : Fin m), p.getVert ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) = Sum.inr (edgeAt i)) →
    ∀ (i : Fin m),
    ∃ (c : Fin k), phi (edgeAt i) = some c := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm vertexAt vertexAt_eq edgeAt edgeAt_eq i
  have ha := p.adj_getVert_succ (i := 2 * i.val) (by rw [hm]; omega)
  rw [vertexAt_eq ⟨i.val, by omega⟩, edgeAt_eq i] at ha
  have hc : phi (edgeAt i) = some alpha ∨ phi (edgeAt i) = some beta := by
    simpa [TwoColorIncidenceGraph] using ha.2
  rcases hc with hc | hc
  · exact ⟨alpha, hc⟩
  · exact ⟨beta, hc⟩

theorem ScheideReversedPathPreparation.helper_hvone_418.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))) (d : ℕ) (hd : p.length = (4 :
        ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m) (hmpos : (2 : ℕ) ≤ m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).left (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )); (
    ∀ (i : Fin (m + (1 : ℕ))), p.getVert ((2 : ℕ) * (↑i : ℕ)) = Sum.inl (vertexAt i)) →
    let reversedVertex : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ if hi : (↑i : ℕ) =
        (0 : ℕ) then vertexAt (0 : Fin (m + (1 : ℕ))) else vertexAt (⟨m + (1 : ℕ) - (↑i : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (m + (1 : ℕ))); reversedVertex (⟨(1 : ℕ),
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    ⟩ : Fin (m + (1 : ℕ))) = T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1
        : ℕ))) := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm hmpos vertexAt vertexAt_eq reversedVertex
  simp only [reversedVertex]
  have he : p.getVert p.length =
      Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩) := by
    simpa using p.getVert_length
  rw [hm] at he
  have hh := vertexAt_eq ⟨m, by omega⟩
  rw [he] at hh
  exact Sum.inl.inj hh.symm

theorem ScheideReversedPathPreparation.helper_vertexAt_injective_428.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p.IsPath →
    ∀ (d : ℕ) (hd : p.length = (4 : ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦ Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).left (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )); (
    ∀ (i : Fin (m + (1 : ℕ))), p.getVert ((2 : ℕ) * (↑i : ℕ)) = Sum.inl (vertexAt i)) →
        Function.Injective vertexAt := by
  classical
  intro V E G k e0 phi T alpha beta p hp d hd hparity m hm vertexAt vertexAt_eq i j hij
  have hi := vertexAt_eq i
  have hj := vertexAt_eq j
  have heq : p.getVert (2 * i.val) = p.getVert (2 * j.val) := by
    rw [hi, hj, hij]
  have hi' : 2 * i.val ≤ p.length := by rw [hm]; omega
  have hj' : 2 * j.val ≤ p.length := by rw [hm]; omega
  have hinj := hp.getVert_injOn hi' hj' heq
  omega

theorem ScheideReversedPathPreparation.helper_edgeAt_injective_438.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (k : ℕ) (e0 : E) (phi :
        PartialEdgeColoring E k) (T : TreeSequence G e0) (alpha beta : Fin k) (p :
        (TwoColorIncidenceGraph G phi alpha beta).Walk (Sum.inl (T.vertex (⟨(0 : ℕ),
        Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))) (Sum.inl (T.vertex (⟨(1 : ℕ),
        Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ)))))), p.IsPath →
    ∀ (d : ℕ) (hd : p.length = (4 : ℕ) * d) (hparity :
    ∀ n ≤ p.length, (n % (2 : ℕ) = (0 : ℕ) →
    ∃ (v : V), p.getVert n = Sum.inl v) ∧ (n % (2 : ℕ) = (1 : ℕ) →
    ∃ (e : E), p.getVert n = Sum.inr e)),
    let m : ℕ := p.length / (2 : ℕ);
    ∀ (hm : p.length = (2 : ℕ) * m),
    let edgeAt : Fin m → E := fun (i : Fin m) ↦ Classical.choose ((hparity ((2 : ℕ) * (↑i : ℕ) +
        (1 : ℕ)) (
    by
                have := GoldbergSeymour.TreeSequence.positive T
                omega
    )).right (
    by
            have := GoldbergSeymour.TreeSequence.positive T
            omega
    )); (
    ∀ (i : Fin m), p.getVert ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) = Sum.inr (edgeAt i)) →
        Function.Injective edgeAt := by
  classical
  intro V E G k e0 phi T alpha beta p hp d hd hparity m hm edgeAt edgeAt_eq i j hij
  have hi := edgeAt_eq i
  have hj := edgeAt_eq j
  have heq : p.getVert (2 * i.val + 1) = p.getVert (2 * j.val + 1) := by
    rw [hi, hj, hij]
  have hi' : 2 * i.val + 1 ≤ p.length := by rw [hm]; omega
  have hj' : 2 * j.val + 1 ≤ p.length := by rw [hm]; omega
  have hinj := hp.getVert_injOn hi' hj' heq
  omega

end GoldbergSeymour

end
