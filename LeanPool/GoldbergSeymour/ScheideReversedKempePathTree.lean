/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideReversedPathPreparation

/-!
# Scheide Reversed Kempe Path Tree

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable abbrev helperU647.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          (G : LooplessMultigraph V E) →
            (k : ℕ) →
              (e0 : E) →
                (phi : PartialEdgeColoring E k) →
                  (T : TreeSequence G e0) →
                    (alpha beta : Fin k) →
                      (p :
                          (TwoColorIncidenceGraph G phi alpha beta).Walk
                            (Sum.inl
                              (T.vertex
                                (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ)))))
                            (Sum.inl
                              (T.vertex
                                (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ :
                                  Fin (T.length + (1 : ℕ)))))) →
                        (d : ℕ) →
                          (hd : p.length = (4 : ℕ) * d) →
                            (hparity :
                                ∀ n ≤ p.length,
                                  (n % (2 : ℕ) = (0 : ℕ) → ∃ (v : V), p.getVert n = Sum.inl v) ∧
                                    (n % (2 : ℕ) = (1 : ℕ) → ∃ (e : E), p.getVert n = Sum.inr e)) →
                              let m : ℕ := p.length / (2 : ℕ);
                              (hm : p.length = (2 : ℕ) * m) →
                                (hmpos : (2 : ℕ) ≤ m) →
                                  let vertexAt : Fin (m + (1 : ℕ)) → V :=
                                    fun (i : Fin (m + (1 : ℕ))) ↦
                                    Classical.choose
                                      ((hparity ((2 : ℕ) * (↑i : ℕ)) (by omega)).left (by omega));
                                  let edgeAt : Fin m → E := fun (i : Fin m) ↦
                                    Classical.choose
                                      ((hparity ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) (by omega)).right
                                        (by omega));
                                  let reversedVertex : Fin (m + (1 : ℕ)) → V :=
                                    fun (i : Fin (m + (1 : ℕ))) ↦
                                    if hi : (↑i : ℕ) = (0 : ℕ) then vertexAt (0 : Fin (m + (1 : ℕ)))
                                    else
                                      vertexAt
                                        (⟨m + (1 : ℕ) - (↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ)));
                                  let reversedEdge : Fin m → E := fun (i : Fin m) ↦
                                    if hi : (↑i : ℕ) = (0 : ℕ) then e0
                                    else edgeAt (⟨m - (↑i : ℕ), by omega⟩ : Fin m);
                                  (hvzero :
                                      reversedVertex (⟨(0 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
                                        T.vertex
                                          (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ :
                                            Fin (T.length + (1 : ℕ)))) →
                                    (hvone :
                                        reversedVertex (⟨(1 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
                                          T.vertex
                                            (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ :
                                              Fin (T.length + (1 : ℕ)))) →
                                      (reversedVertex_injective :
                                          Function.Injective reversedVertex) →
                                        (reversedEdge_injective : Function.Injective reversedEdge) →
                                          (edge_ends :
                                              ∀ (i : Fin m),
                                                G.ends (edgeAt i) =
                                                  s(vertexAt
                                                      (⟨(↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ))),
                                                    vertexAt i.succ)) →
                                            TreeSequence G e0 := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm hmpos vertexAt edgeAt reversedVertex
      reversedEdge hvzero hvone reversedVertex_injective reversedEdge_injective edge_ends
  exact {
    length := m
    positive := by omega
    vertex := reversedVertex
    edge := reversedEdge
    vertex_injective := reversedVertex_injective
    edge_injective := reversedEdge_injective
    first_edge := by simp [reversedEdge]
    attaches := by
      intro j
      by_cases hj : j.val = 0
      · exact @ScheideReversedPathPreparation.helper_branch_272 (@V) (@E) (@G) (@k) (@e0) (@phi)
          (@T) (@alpha) (@beta) (@p)
          (@d) (@hd) (@hparity) (@hm) (@hmpos) (@hvzero) (@hvone) (@j) (@hj)
      · refine ⟨⟨j.val, by omega⟩, ?_⟩
        let r : Fin m := ⟨m - j.val, by omega⟩
        have he := edge_ends r
        simp [reversedEdge, hj, reversedVertex]
        have hfirst : vertexAt (⟨r.val, by omega⟩ : Fin (m + 1)) =
            vertexAt (⟨m - j.val, by omega⟩ : Fin (m + 1)) := by
          rfl
        have hsecond : vertexAt r.succ =
            vertexAt (⟨m + 1 - j.val, by omega⟩ : Fin (m + 1)) := by
          apply congrArg vertexAt
          apply Fin.ext
          dsimp [r]
          omega
        rw [hfirst, hsecond] at he
        simpa [Fin.succ] using he }

private theorem helper_path_vertices_314.{u_1, u_2} :
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
    ∀ (hm : p.length = (2 : ℕ) * m) (_ : (0 : ℕ) < p.length) (hmpos : (2 : ℕ) ≤ m),
    let vertexAt : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦
      Classical.choose ((hparity ((2 : ℕ) * (↑i : ℕ)) (by omega)).left (by omega));
    ∀
      (_ :
        ∀ (i : Fin (m + (1 : ℕ))), p.getVert ((2 : ℕ) * (↑i : ℕ)) = Sum.inl (vertexAt i)),
    let edgeAt : Fin m → E := fun (i : Fin m) ↦
      Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) (by omega)).right (by omega));
    let reversedVertex : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦
      if hi : (↑i : ℕ) = (0 : ℕ) then vertexAt (0 : Fin (m + (1 : ℕ)))
      else vertexAt (⟨m + (1 : ℕ) - (↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ)));
    let reversedEdge : Fin m → E := fun (i : Fin m) ↦
      if hi : (↑i : ℕ) = (0 : ℕ) then e0 else edgeAt (⟨m - (↑i : ℕ), by omega⟩ : Fin m);
    ∀
      (hvzero :
        reversedVertex (⟨(0 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
          T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))
      (hvone :
        reversedVertex (⟨(1 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
          T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ))))
      (reversedVertex_injective : Function.Injective reversedVertex)
      (reversedEdge_injective : Function.Injective reversedEdge)
      (edge_ends :
        ∀ (i : Fin m),
          G.ends (edgeAt i) =
            s(vertexAt (⟨(↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ))), vertexAt i.succ)),
    let U : TreeSequence G e0 :=
      helperU647 G k e0 phi T alpha beta p d hd hparity hm hmpos hvzero hvone
        reversedVertex_injective reversedEdge_injective edge_ends;
    ∀ (_ : U.vertex = reversedVertex) (_ : U.edge = reversedEdge) (_ : U.length = m)
      (v : V),
    Sum.inl v ∈ p.support ↔ ∃ (i : Fin (U.length + (1 : ℕ))), v = U.vertex i := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm hpos hmpos vertexAt vertexAt_eq edgeAt
      reversedVertex reversedEdge hvzero hvone reversedVertex_injective reversedEdge_injective
      edge_ends U uVertex uEdge uLength
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert]
  change ∀ v, (∃ n, p.getVert n = Sum.inl v ∧ n ≤ p.length) ↔
    ∃ i : Fin (m + 1), v = U.vertex i
  intro v
  constructor
  · rintro ⟨n, hn, hnle⟩
    have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hcases with heven | hodd
    · let i : Fin (m + 1) := ⟨n / 2, by omega⟩
      have hni : 2 * i.val = n := by
        dsimp [i]
        omega
      have hv : v = vertexAt i := by
        have hh := vertexAt_eq i
        rw [hni] at hh
        exact Sum.inl.inj (hn.symm.trans hh)
      by_cases hi : i.val = 0
      · refine ⟨0, ?_⟩
        have hi' : i = 0 := Fin.ext hi
        rw [hi'] at hv
        simpa [uVertex, uEdge, uLength, reversedVertex] using hv
      · refine ⟨⟨m + 1 - i.val, by omega⟩, ?_⟩
        let r : Fin (m + 1) := ⟨m + 1 - i.val, by omega⟩
        have hr : reversedVertex r = vertexAt i := by
          have hil := i.isLt
          dsimp [reversedVertex, r]
          rw [dite_eq_right (by omega)]
          apply congrArg vertexAt
          apply Fin.ext
          change m + 1 - (m + 1 - i.val) = i.val
          omega
        exact hv.trans (by simpa [uVertex, uEdge, uLength] using hr.symm)
    · have hh := (hparity n hnle).2 hodd
      rw [hn] at hh
      rcases hh with ⟨e, he⟩
      cases he
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val = 0
    · refine ⟨0, ?_, by omega⟩
      have hi' : i = 0 := Fin.ext hi
      subst i
      simpa [uVertex, uEdge, uLength, reversedVertex] using vertexAt_eq (0 : Fin (m + 1))
    · let q : Fin (m + 1) := ⟨m + 1 - i.val, by omega⟩
      refine ⟨2 * q.val, ?_, ?_⟩
      · have hq := vertexAt_eq q
        have hq' : p.getVert (2 * q.val) = Sum.inl (U.vertex i) := by
          have hi0 : ¬ i = 0 := by
            intro h
            apply hi
            simp [h]
          have hr : reversedVertex i = vertexAt q := by
            dsimp [reversedVertex]
            rw [dite_eq_right (by simpa using hi)]
          simpa [uVertex, uEdge, uLength] using hq.trans (congrArg Sum.inl hr.symm)
        exact hq'
      · rw [hm]
        dsimp [q]
        omega

private theorem helper_path_edges_373.{u_1, u_2} :
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
      Classical.choose ((hparity ((2 : ℕ) * (↑i : ℕ)) (by omega)).left (by omega));
    let edgeAt : Fin m → E := fun (i : Fin m) ↦
      Classical.choose
        ((hparity ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) (by omega)).right (by omega));
    ∀ (_ : ∀ (i : Fin m), p.getVert ((2 : ℕ) * (↑i : ℕ) + (1 : ℕ)) = Sum.inr (edgeAt i)),
    let reversedVertex : Fin (m + (1 : ℕ)) → V := fun (i : Fin (m + (1 : ℕ))) ↦
      if hi : (↑i : ℕ) = (0 : ℕ) then vertexAt (0 : Fin (m + (1 : ℕ)))
      else vertexAt (⟨m + (1 : ℕ) - (↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ)));
    let reversedEdge : Fin m → E := fun (i : Fin m) ↦
      if hi : (↑i : ℕ) = (0 : ℕ) then e0 else edgeAt (⟨m - (↑i : ℕ), by omega⟩ : Fin m);
    ∀
      (hvzero :
        reversedVertex (⟨(0 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
          T.vertex (⟨(0 : ℕ), Nat.zero_lt_succ T.length⟩ : Fin (T.length + (1 : ℕ))))
      (hvone :
        reversedVertex (⟨(1 : ℕ), by omega⟩ : Fin (m + (1 : ℕ))) =
          T.vertex (⟨(1 : ℕ), Nat.succ_lt_succ T.positive⟩ : Fin (T.length + (1 : ℕ))))
      (reversedVertex_injective : Function.Injective reversedVertex)
      (reversedEdge_injective : Function.Injective reversedEdge)
      (edge_ends :
        ∀ (i : Fin m),
          G.ends (edgeAt i) =
            s(vertexAt (⟨(↑i : ℕ), by omega⟩ : Fin (m + (1 : ℕ))), vertexAt i.succ)),
    let U : TreeSequence G e0 :=
      helperU647 G k e0 phi T alpha beta p d hd hparity hm hmpos hvzero hvone
        reversedVertex_injective reversedEdge_injective edge_ends;
    ∀ (_ : U.vertex = reversedVertex) (_ : U.edge = reversedEdge) (_ : U.length = m)
      (f : E),
    Sum.inr f ∈ p.support ↔
      f = edgeAt (⟨(0 : ℕ), by omega⟩ : Fin m) ∨
        ∃ (j : Fin U.length), (1 : ℕ) ≤ (↑j : ℕ) ∧ f = U.edge j := by
  classical
  intro V E G k e0 phi T alpha beta p d hd hparity m hm hmpos vertexAt edgeAt edgeAt_eq
      reversedVertex reversedEdge hvzero hvone reversedVertex_injective reversedEdge_injective
      edge_ends U uVertex uEdge uLength
  simp only [SimpleGraph.Walk.mem_support_iff_exists_getVert]
  change ∀ f, (∃ n, p.getVert n = Sum.inr f ∧ n ≤ p.length) ↔
    f = edgeAt ⟨0, by omega⟩ ∨ ∃ j : Fin m, 1 ≤ j.val ∧ f = U.edge j
  intro f
  constructor
  · rintro ⟨n, hn, hnle⟩
    have hcases : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hcases with heven | hodd
    · have hh := (hparity n hnle).1 heven
      rw [hn] at hh
      rcases hh with ⟨v, hv⟩
      cases hv
    · let q : Fin m := ⟨n / 2, by omega⟩
      have hnq : 2 * q.val + 1 = n := by
        dsimp [q]
        omega
      have hf : f = edgeAt q := by
        have hh := edgeAt_eq q
        rw [hnq] at hh
        exact Sum.inr.inj (hn.symm.trans hh)
      by_cases hq : q.val = 0
      · left
        have hq' : q = (⟨0, by omega⟩ : Fin m) := by
          apply Fin.ext
          exact hq
        simpa [hq'] using hf
      · right
        have hqpos : 0 < q.val := by omega
        have hmpos' : 0 < m := by omega
        have qlt := q.isLt
        refine ⟨⟨m - q.val, by
          exact Nat.sub_lt hmpos' hqpos⟩, ?_, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt qlt)
        have hr : reversedEdge ⟨m - q.val, by omega⟩ = edgeAt q := by
          dsimp [reversedEdge]
          rw [dite_eq_right (by omega)]
          apply congrArg edgeAt
          apply Fin.ext
          dsimp [q]
          have qlt := q.isLt
          omega
        exact hf.trans (by simpa [uVertex, uEdge, uLength] using hr.symm)
  · rintro (hf | ⟨j, hj, hf⟩)
    · subst f
      refine ⟨1, ?_, by rw [hm]; omega⟩
      exact edgeAt_eq ⟨0, by omega⟩
    · let q : Fin m := ⟨m - j.val, by omega⟩
      refine ⟨2 * q.val + 1, ?_, ?_⟩
      · subst f
        have hq := edgeAt_eq q
        have hj0 : ¬ j.val = 0 := by
          intro h
          omega
        have hr : reversedEdge j = edgeAt q := by
          dsimp [reversedEdge]
          rw [dite_eq_right hj0]
        have hq' : p.getVert (2 * q.val + 1) = Sum.inr (U.edge j) := by
          simpa [uVertex, uEdge, uLength] using hq.trans (congrArg Sum.inr hr.symm)
        exact hq'
      · rw [hm]
        dsimp [q]
        have jlt := j.isLt
        omega

theorem ScheideReversedKempePathTree {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (alpha beta : Fin k)
    (halpha : alpha ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (hbeta : beta ∈ MissingColors G phi
      (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩))
    (p : (TwoColorIncidenceGraph G phi alpha beta).Walk
      (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
      (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
    (hp : p.IsPath) (hdiv : 4 ∣ p.length) :
    Nonempty (ScheideReversedPathCertificate G k e0 phi T alpha beta p) := by
  classical
  obtain ⟨d, hd⟩ := hdiv
  have hlen : p.length = 4 * d := by omega
  have hparity : ∀ n ≤ p.length,
      (n % 2 = 0 → ∃ v, p.getVert n = Sum.inl v) ∧
      (n % 2 = 1 → ∃ e, p.getVert n = Sum.inr e) := by
    apply ScheideReversedPathPreparation.helper_hparity_47 <;> assumption
  let m := p.length / 2
  have hm : p.length = 2 * m := by omega
  have hends : T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ ≠
      T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ := by
    apply ScheideReversedPathPreparation.helper_hends_364
  have hpos : 0 < p.length := by
    apply ScheideReversedPathPreparation.helper_hpos_373; assumption
  have hmpos : 2 ≤ m := by omega
  let vertexAt : Fin (m + 1) → V := fun i =>
    Classical.choose ((hparity (2 * i.val) (by omega)).1 (by omega))
  have vertexAt_eq : ∀ i : Fin (m + 1),
      p.getVert (2 * i.val) = Sum.inl (vertexAt i) := by
    intro i
    exact Classical.choose_spec ((hparity (2 * i.val) (by omega)).1 (by omega))
  let edgeAt : Fin m → E := fun i =>
    Classical.choose ((hparity (2 * i.val + 1) (by omega)).2 (by omega))
  have edgeAt_eq : ∀ i : Fin m,
      p.getVert (2 * i.val + 1) = Sum.inr (edgeAt i) := by
    intro i
    exact Classical.choose_spec ((hparity (2 * i.val + 1) (by omega)).2 (by omega))
  have edgeAt_colored : ∀ i : Fin m, ∃ c, phi (edgeAt i) = some c := by
    exact @ScheideReversedPathPreparation.helper_edgeAt_colored_392 (@V) (@E) (@G) (@k) (@e0)
        (@phi) (@T) (@alpha) (@beta) (@p)
        (@d) (@hd) (@hparity) (@hm) (@vertexAt_eq) (@edgeAt_eq)
  have edgeAt_colors : ∀ i : Fin m,
      phi (edgeAt i) = some alpha ∨ phi (edgeAt i) = some beta := by
    intro i
    have ha := p.adj_getVert_succ (i := 2 * i.val) (by rw [hm]; omega)
    rw [vertexAt_eq ⟨i.val, by omega⟩, edgeAt_eq i] at ha
    simpa [TwoColorIncidenceGraph] using ha.2
  let reversedVertex : Fin (m + 1) → V := fun i =>
    if hi : i.val = 0 then vertexAt 0
    else vertexAt ⟨m + 1 - i.val, by omega⟩
  let reversedEdge : Fin m → E := fun i =>
    if hi : i.val = 0 then e0
    else edgeAt ⟨m - i.val, by omega⟩
  have hvzero : reversedVertex ⟨0, by omega⟩ =
      T.vertex ⟨0, Nat.zero_lt_succ T.length⟩ := by
    simp only [reversedVertex, dite_eq_left rfl]
    have hh := vertexAt_eq (0 : Fin (m + 1))
    exact Sum.inl.inj (hh.symm.trans (by simpa using p.getVert_zero))
  have hvone : reversedVertex ⟨1, by omega⟩ =
      T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩ := by
    exact @ScheideReversedPathPreparation.helper_hvone_418 (@V) (@E) (@G) (@k) (@e0) (@phi) (@T)
        (@alpha) (@beta) (@p) (@d)
        (@hd) (@hparity) (@hm) (@hmpos) (@vertexAt_eq)
  have vertexAt_injective : Function.Injective vertexAt := by
    exact @ScheideReversedPathPreparation.helper_vertexAt_injective_428 (@V) (@E) (@G) (@k) (@e0)
        (@phi) (@T) (@alpha) (@beta)
        (@p) (@hp) (@d) (@hd) (@hparity) (@hm) (@vertexAt_eq)
  have edgeAt_injective : Function.Injective edgeAt := by
    exact @ScheideReversedPathPreparation.helper_edgeAt_injective_438 (@V) (@E) (@G) (@k) (@e0)
        (@phi) (@T) (@alpha) (@beta)
        (@p) (@hp) (@d) (@hd) (@hparity) (@hm) (@edgeAt_eq)
  have reversedVertex_injective : Function.Injective reversedVertex := by
    exact @ScheideReversedPathPreparation.helper_reversedVertex_injective_187 (@V) (@E) (@G) (@k)
        (@e0) (@phi) (@T) (@alpha)
        (@beta) (@p) (@d) (@hd) (@hparity) (@hm) (@vertexAt_injective)
  have reversedEdge_injective : Function.Injective reversedEdge := by
    exact @ScheideReversedPathPreparation.helper_reversedEdge_injective_212 (@V) (@E)
        inferInstance inferInstance inferInstance
        (@G) (@k) (@e0) (@phi) (@T) (@htriple) (@alpha) (@beta) (@p) (@d) (@hd) (@hparity) (@hm)
        (@edgeAt_colored) (@edgeAt_injective)
  have edge_ends : ∀ i : Fin m,
      G.ends (edgeAt i) = s(vertexAt ⟨i.val, by omega⟩, vertexAt i.succ) := by
    exact @ScheideReversedPathPreparation.helper_edge_ends_239 (@V) (@E) (@G) (@k) (@e0) (@phi)
        (@T) (@alpha) (@beta) (@p) (@d)
        (@hd) (@hparity) (@hm) (@vertexAt_eq) (@edgeAt_eq) (@vertexAt_injective)
  let U := @helperU647 (@V) (@E) (@G) (@k) (@e0) (@phi) (@T) (@alpha) (@beta) (@p) (@d) (@hd)
      (@hparity) (@hm) (@hmpos) (@hvzero) (@hvone) (@reversedVertex_injective)
      (@reversedEdge_injective) (@edge_ends)
  have uVertex : U.vertex = reversedVertex := rfl
  have uEdge : U.edge = reversedEdge := rfl
  have uLength : U.length = m := rfl
  have tash : TashkinovTree G e0 phi U := by
    intro j hj
    have j0 : j.val ≠ 0 := by omega
    rw [show U.edge j = edgeAt ⟨m - j.val, by omega⟩ by simp [uEdge, reversedEdge, dite_eq_right
        j0]]
    have hc := edgeAt_colors ⟨m - j.val, by omega⟩
    rcases hc with hc | hc
    · refine ⟨0, alpha, hc, ?_⟩
      have hv0 := hvzero
      simp only [reversedVertex, dite_eq_left rfl] at hv0
      simp only [uVertex, reversedVertex]
      split
      · simpa [hv0] using halpha
      · rename_i h
        exfalso
        exact h rfl
    · refine ⟨1, beta, hc, ?_⟩
      have hv1 := hvone
      simp [reversedVertex] at hv1
      simp only [uVertex, reversedVertex]
      split
      · rename_i h
        exfalso
        norm_num at h
        omega
      · have hmod : 1 % (j.val + 1) = 1 := by
          apply Nat.mod_eq_of_lt
          omega
        simpa [hv1, hmod] using hbeta
  refine ⟨{
    tree := U
    closingEdge := edgeAt ⟨0, by omega⟩
    length_lower := hmpos
    length_eq := by simp [uLength, m]
    tashkinov := tash
    first_vertex := by simpa [uVertex, uEdge, uLength] using hvzero
    second_vertex := by simpa [uVertex, uEdge, uLength] using hvone
    closing_ends := by
      have he := edge_ends ⟨0, by omega⟩
      have he' : G.ends (edgeAt ⟨0, by omega⟩) =
          s(vertexAt ⟨1, by omega⟩, vertexAt ⟨0, by omega⟩) :=
        he.trans Sym2.eq_swap
      have hm0 : m ≠ 0 := by omega
      simpa [uVertex, uEdge, uLength, reversedVertex, hm0] using he'
    path_vertices := by
      exact @helper_path_vertices_314 (@V) (@E) (@G) (@k) (@e0) (@phi) (@T) (@alpha) (@beta) (@p)
          (@d) (@hd) (@hparity) (@hm) (@hpos) (@hmpos) (@vertexAt_eq) (@hvzero) (@hvone)
          (@reversedVertex_injective) (@reversedEdge_injective) (@edge_ends) (@uVertex) (@uEdge)
          (@uLength)
    path_edges := by
      exact @helper_path_edges_373 (@V) (@E) (@G) (@k) (@e0) (@phi) (@T) (@alpha) (@beta) (@p)
          (@d) (@hd) (@hparity) (@hm) (@hmpos) (@edgeAt_eq) (@hvzero) (@hvone)
          (@reversedVertex_injective) (@reversedEdge_injective) (@edge_ends) (@uVertex) (@uEdge)
          (@uLength)
    trunk_edge_ends := by
      change ∀ j : Fin m, 1 ≤ j.val →
        G.ends (U.edge j) = s(U.vertex ⟨j.val, by change j.val < m + 1; omega⟩, U.vertex j.succ)
      intro j hj
      have j0 : j.val ≠ 0 := by omega
      rw [show U.edge j = edgeAt ⟨m - j.val, by omega⟩ by
        simp [uEdge, reversedEdge, j0]]
      have he := edge_ends ⟨m - j.val, by omega⟩
      have he' := he.trans Sym2.eq_swap
      have hv1 : vertexAt (⟨m - j.val, by omega⟩ : Fin m).succ =
          vertexAt ⟨m + 1 - j.val, by omega⟩ := by
        apply congrArg vertexAt
        apply Fin.ext
        simp [Fin.succ]
        omega
      rw [hv1] at he'
      simpa [uVertex, uEdge, uLength, reversedVertex, j0] using he'
  }⟩

end GoldbergSeymour

end
