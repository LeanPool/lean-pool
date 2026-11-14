/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment

/-!
# Tash Tree Last Index Deletion

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private theorem helper_hattachLast_95.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E)
      (T : TreeSequence G e0),
    (2 : ℕ) < TashTreePathIndex G T →
    TashTreePathIndex G T = T.length →
    ∀ (r : Fin T.length) (p _ : Fin (T.length + (1 : ℕ)))
      (hr : (↑r : ℕ) + (1 : ℕ) = T.length) (hp : (↑p : ℕ) + (1 : ℕ) = T.length)
      (hrval : (↑r : ℕ) = T.length - (1 : ℕ))
      (hrlast : r = (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length)),
    ∃ (i : Fin (T.length - (1 : ℕ))),
    G.ends (T.edge (⟨T.length - (1 : ℕ), by omega⟩ : Fin T.length)) =
      s(T.vertex (Fin.last T.length), T.vertex (i.castLT (by omega))) := by
  classical
  intro V E G e0 T hq hlast r p j hr hp hrval hrlast
  rcases T.attaches ⟨T.length - 1, by omega⟩ with ⟨i, hi⟩
  have hineq : i.val ≠ T.length - 1 := by
    intro heq
    have heqi : i = ⟨T.length - 1, by omega⟩ := Fin.ext heq
    have hbad : TashTreeSuffixPath G T (T.length - 1) := by
      refine ⟨by omega, by omega, ?_⟩
      intro t ht
      have htval : t.val = T.length - 1 := by omega
      have hteq : t = ⟨T.length - 1, by omega⟩ := Fin.ext htval
      rw [hteq]
      have hi' := hi
      rw [heqi] at hi'
      rw [hi']
      apply Sym2.eq_iff.mpr
      right
      constructor <;> rfl
    have hle : TashTreePathIndex G T ≤ T.length - 1 := by
      unfold TashTreePathIndex
      exact Nat.find_min' _ hbad
    omega
  have hilt : i.val < T.length - 1 := by omega
  refine ⟨⟨i.val, hilt⟩, ?_⟩
  rw [hi]
  apply Sym2.eq_iff.mpr
  left
  constructor
  · apply congrArg T.vertex
    apply Fin.ext
    exact Nat.sub_add_cancel (by omega)
  · apply congrArg T.vertex
    apply Fin.ext
    rfl

private theorem helper_vertex_injective_159.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0)
        (r : Fin T.length) (p _ : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length)
        (hp : (↑p : ℕ) + (1 : ℕ) = T.length) (hrval : (↑r : ℕ) = T.length - (1 : ℕ)) (hrlast : r =
        (⟨T.length - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin T.length)),
    let svertex : Fin (T.length - (1 : ℕ) + (1 : ℕ)) → V := fun (i : Fin (T.length - (1 : ℕ) + (1
        : ℕ))) ↦ if hi : (↑i : ℕ) < T.length - (1 : ℕ) then T.vertex (⟨(↑i : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin (T.length + (1 : ℕ))) else T.vertex (Fin.last T.length); Function.Injective svertex
  := by
  classical
  intro V E G e0 T r p j hr hp hrval hrlast svertex a b hab
  by_cases ha : a.val < T.length - 1
  · by_cases hb : b.val < T.length - 1
    · apply Fin.ext
      simpa using congrArg Fin.val (T.vertex_injective (by simpa [svertex, ha, hb] using hab))
    · have hbv : svertex b = T.vertex (Fin.last T.length) := by simp [svertex, hb]
      have hav : svertex a = T.vertex ⟨a.val, by omega⟩ := by simp [svertex, ha]
      have heq : T.vertex ⟨a.val, by omega⟩ = T.vertex (Fin.last T.length) := by
        simpa [hav, hbv] using hab
      have hv := T.vertex_injective heq
      have hval : a.val = T.length := by simpa using congrArg Fin.val hv
      omega
  · by_cases hb : b.val < T.length - 1
    · have hav : svertex a = T.vertex (Fin.last T.length) := by simp [svertex, ha]
      have hbv : svertex b = T.vertex ⟨b.val, by omega⟩ := by simp [svertex, hb]
      have heq : T.vertex (Fin.last T.length) = T.vertex ⟨b.val, by omega⟩ := by
        simpa [hav, hbv] using hab
      have hv := T.vertex_injective heq
      have hval : T.length = b.val := by simpa using congrArg Fin.val hv
      omega
    · apply Fin.ext
      omega

private theorem helper_edge_injective_182.{u_1, u_2} :
    open scoped Classical in
    ∀ {V : Type u_1} {E : Type u_2} (G : LooplessMultigraph V E) (e0 : E) (T : TreeSequence G e0),
        (2 : ℕ) < TashTreePathIndex G T → TashTreePathIndex G T = T.length →
    ∀ (r : Fin T.length) (p _ : Fin (T.length + (1 : ℕ))) (hr : (↑r : ℕ) + (1 : ℕ) = T.length) (hp
        : (↑p : ℕ) + (1 : ℕ) = T.length) (hrval : (↑r : ℕ) = T.length - (1 : ℕ)) (hrlast : r =
        (⟨T.length - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin T.length)),
    let sedge : Fin (T.length - (1 : ℕ)) → E := fun (i : Fin (T.length - (1 : ℕ))) ↦ if _ : (↑i :
        ℕ) < T.length - (2 : ℕ) then T.edge (⟨(↑i : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin T.length) else T.edge (⟨T.length - (1 : ℕ),
    by
              have := GoldbergSeymour.TreeSequence.positive T
              omega
    ⟩ : Fin T.length); Function.Injective sedge := by
  classical
  intro V E G e0 T hq hlast r p j hr hp hrval hrlast sedge a b hab
  by_cases ha : a.val < T.length - 2
  · by_cases hb : b.val < T.length - 2
    · apply Fin.ext
      simpa using congrArg Fin.val (T.edge_injective (by simpa [sedge, ha, hb] using hab))
    · have hbe : sedge b = T.edge ⟨T.length - 1, by omega⟩ := by simp [sedge, hb]
      have hae : sedge a = T.edge ⟨a.val, by omega⟩ := by simp [sedge, ha]
      have heq : T.edge ⟨a.val, by omega⟩ = T.edge ⟨T.length - 1, by omega⟩ := by
        simpa [hae, hbe] using hab
      have hv := T.edge_injective heq
      have hval : a.val = T.length - 1 := by simpa using congrArg Fin.val hv
      omega
  · by_cases hb : b.val < T.length - 2
    · have hae : sedge a = T.edge ⟨T.length - 1, by omega⟩ := by simp [sedge, ha]
      have hbe : sedge b = T.edge ⟨b.val, by omega⟩ := by simp [sedge, hb]
      have heq : T.edge ⟨T.length - 1, by omega⟩ = T.edge ⟨b.val, by omega⟩ := by
        simpa [hae, hbe] using hab
      have hv := T.edge_injective heq
      have hval : T.length - 1 = b.val := by simpa using congrArg Fin.val hv
      omega
    · apply Fin.ext
      omega

private noncomputable abbrev helperS253.{u_1, u_2} :
    open scoped Classical in
      {V : Type u_1} →
        {E : Type u_2} →
          (G : LooplessMultigraph V E) →
            (e0 : E) →
              (T : TreeSequence G e0) →
                (2 : ℕ) < TashTreePathIndex G T →
                  TashTreePathIndex G T = T.length →
                    (r : Fin T.length) →
                      (p j : Fin (T.length + (1 : ℕ))) →
                        (hr : (↑r : ℕ) + (1 : ℕ) = T.length) →
                          (hp : (↑p : ℕ) + (1 : ℕ) = T.length) →
                            (↑j : ℕ) + (2 : ℕ) ≤ T.length →
                              (hrval : (↑r : ℕ) = T.length - (1 : ℕ)) →
                                (hrlast :
                                    r =
                                      (⟨T.length - (1 : ℕ),
                                          by
                                          have := GoldbergSeymour.TreeSequence.positive T
                                          omega⟩ :
                                        Fin T.length)) →
                                  (∃ (i : Fin (T.length - (1 : ℕ))),
                                      G.ends
                                          (T.edge
                                            (⟨T.length - (1 : ℕ),
                                                by
                                                have := GoldbergSeymour.TreeSequence.positive T
                                                omega⟩ :
                                              Fin T.length)) =
                                        s(T.vertex (Fin.last T.length),
                                          T.vertex
                                            (i.castLT
                                              (by
                                                have := GoldbergSeymour.TreeSequence.positive T
                                                omega)))) →
                                    let _ : Fin (T.length - (1 : ℕ) + (1 : ℕ)) → V :=
                                      fun (i : Fin (T.length - (1 : ℕ) + (1 : ℕ))) ↦
                                      if hi : (↑i : ℕ) < T.length - (1 : ℕ) then
                                        T.vertex
                                          (⟨(↑i : ℕ),
                                              by
                                              have := GoldbergSeymour.TreeSequence.positive T
                                              omega⟩ :
                                            Fin (T.length + (1 : ℕ)))
                                      else T.vertex (Fin.last T.length);
                                    let _ : Fin (T.length - (1 : ℕ)) → E :=
                                      fun (i : Fin (T.length - (1 : ℕ))) ↦
                                      if _ : (↑i : ℕ) < T.length - (2 : ℕ) then
                                        T.edge
                                          (⟨(↑i : ℕ),
                                              by
                                              have := GoldbergSeymour.TreeSequence.positive T
                                              omega⟩ :
                                            Fin T.length)
                                      else
                                        T.edge
                                          (⟨T.length - (1 : ℕ),
                                              by
                                              have := GoldbergSeymour.TreeSequence.positive T
                                              omega⟩ :
                                            Fin T.length);
                                    TreeSequence G e0 := by
  classical
  intro V E G e0 T hq hlast r p j hr hp hj hrval hrlast hattachLast svertex sedge
  exact {
    length := T.length - 1
    positive := by omega
    vertex := svertex
    edge := sedge
    vertex_injective := by
      exact @helper_vertex_injective_159 (@V) (@E) (@G) (@e0) (@T) (@r) (@p) (@j) (@hr) (@hp)
          (@hrval) (@hrlast)
    edge_injective := by
      exact @helper_edge_injective_182 (@V) (@E) (@G) (@e0) (@T) (@hq) (@hlast) (@r) (@p) (@j)
          (@hr) (@hp) (@hrval) (@hrlast)
    first_edge := by
      have hh : 0 < T.length - 2 := by omega
      simp [sedge, hh, T.first_edge]
    attaches := by
      intro j
      by_cases hj : j.val < T.length - 2
      · let jj : Fin T.length := ⟨j.val, by omega⟩
        rcases T.attaches jj with ⟨i, hi⟩
        let ii : Fin (j.val + 1) := ⟨i.val, by simp [jj]⟩
        refine ⟨ii, ?_⟩
        have hjv : j.val + 1 < T.length - 1 := by omega
        have hiiv : ii.val < T.length - 1 := by dsimp [ii]; omega
        have hjj : jj = ⟨j.val, by omega⟩ := rfl
        simp only [sedge, dite_eq_left hj]
        change G.ends (T.edge ⟨j.val, by omega⟩) = _
        rw [show svertex j.succ = T.vertex jj.succ by
          simp [svertex, hjv]; congr 1]
        rw [show svertex (Fin.castLT ii (by omega)) = T.vertex (i.castLT (by omega)) by
          simp [svertex, hiiv]; congr 1]
        rw [hi]
      · rcases hattachLast with ⟨i, hi⟩
        let ii : Fin (j.val + 1) := ⟨i.val, by omega⟩
        refine ⟨ii, ?_⟩
        have hjv : j.val + 1 = T.length - 1 := by omega
        have hiiv : ii.val < T.length - 1 := by dsimp [ii]; omega
        rw [show sedge j = T.edge ⟨T.length - 1, by omega⟩ by simp [sedge, hj]]
        rw [show svertex j.succ = T.vertex (Fin.last T.length) by
          simp [svertex, hjv]]
        rw [show svertex (Fin.castLT ii (by omega)) = T.vertex (i.castLT (by omega)) by
          simp [svertex, hiiv]; congr 1]
        exact hi }

theorem TashTreeLastIndexDeletion {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hq : 2 < TashTreePathIndex G T)
    (hlast : TashTreePathIndex G T = T.length)
    (gamma beta : Fin k) (r : Fin T.length) (p j : Fin (T.length + 1))
    (hr : r.val + 1 = T.length) (hp : p.val + 1 = T.length)
    (hj : j.val + 2 ≤ T.length)
    (hrgamma : phi (T.edge r) = some gamma)
    (hpgamma : gamma ∈ PresentColors G phi (T.vertex p))
    (hbj : beta ∈ MissingColors G phi (T.vertex j))
    (hblast : beta ∈ MissingColors G phi (T.vertex (Fin.last T.length))) :
    ∃ (P S : TreeSequence G e0) (s : Fin S.length),
      P.length + 2 = T.length ∧
        TreeSequenceInitialSegment P T ∧
        S.length = P.length + 1 ∧
        TreeSequenceInitialSegment P S ∧
        s.val + 1 = S.length ∧
        S.edge s = T.edge r ∧
        S.vertex (Fin.last S.length) = T.vertex (Fin.last T.length) ∧
        TashTreeBadPair G k e0 phi S ∧
        TashTreeRankLess G S T := by
  classical
  open scoped Sym2 in
  have hlen : 3 ≤ T.length := by omega
  have hqspec : TashTreeSuffixPath G T (TashTreePathIndex G T) := by
    unfold TashTreePathIndex
    exact Nat.find_spec _
  have hindex : TashTreePathIndex G T = T.length := hlast
  have hnotlast : ∀ i : Fin T.length, i.val ≠ T.length - 1 →
      i.val < T.length - 1 := by
    intro i hi
    omega
  have hrval : r.val = T.length - 1 := by omega
  have hrlast : r = ⟨T.length - 1, by omega⟩ := Fin.ext hrval
  let P : TreeSequence G e0 := by
    exact {
      length := T.length - 2
      positive := by omega
      vertex := fun i => T.vertex ⟨i.val, by omega⟩
      edge := fun i => T.edge ⟨i.val, by omega⟩
      vertex_injective := by
        intro a b hab
        apply Fin.ext
        simpa using congrArg Fin.val (T.vertex_injective hab)
      edge_injective := by
        intro a b hab
        apply Fin.ext
        simpa using congrArg Fin.val (T.edge_injective hab)
      first_edge := by
        rw [T.first_edge]
      attaches := by
        intro j
        let jj : Fin T.length := ⟨j.val, by omega⟩
        rcases T.attaches jj with ⟨i, hi⟩
        let ii : Fin (j.val + 1) := ⟨i.val, by simp [jj]⟩
        refine ⟨ii, ?_⟩
        rw [hi]
        apply congrArg₂ Sym2.mk
        · congr 1
        · congr 1 }
  have hattachLast := @helper_hattachLast_95 (@V) (@E) (@G) (@e0) (@T) (@hq) (@hlast) (@r) (@p) (@j)
      (@hr) (@hp) (@hrval) (@hrlast)
  let svertex : Fin (T.length - 1 + 1) → V := fun i =>
    if hi : i.val < T.length - 1 then T.vertex ⟨i.val, by omega⟩
    else T.vertex (Fin.last T.length)
  let sedge : Fin (T.length - 1) → E := fun i =>
    if hi : i.val < T.length - 2 then T.edge ⟨i.val, by omega⟩
    else T.edge ⟨T.length - 1, by omega⟩
  let S := @helperS253 (@V) (@E) (@G) (@e0) (@T) (@hq) (@hlast) (@r) (@p) (@j) (@hr) (@hp) (@hj)
      (@hrval) (@hrlast) (@hattachLast)
  have hPprefix : TreeSequenceInitialSegment P T := by
    refine ⟨by dsimp [P]; omega, ?_, ?_⟩
    · intro i
      rfl
    · intro i
      rfl
  have hPSegment : TreeSequenceInitialSegment P S := by
    refine ⟨by dsimp [P, S]; omega, ?_, ?_⟩
    · intro i
      dsimp [P, S, svertex, sedge]
      have hi' : i.val < P.length + 1 := i.isLt
      have hi : i.val < T.length - 1 := by
        dsimp [P] at hi'
        omega
      simp [hi]
    · intro i
      dsimp [P, S, svertex, sedge]
      have hi' : i.val < P.length := i.isLt
      have hi : i.val < T.length - 2 := by
        dsimp [P] at hi'
        omega
      simp [hi]
  have hTashS : TashkinovTree G e0 phi S := by
    intro q hqpos
    by_cases hqold : q.val < T.length - 2
    · have hT := hmin.1.2.1 ⟨q.val, by omega⟩ hqpos
      rcases hT with ⟨i, c, hc, hm⟩
      let u : Fin (q.val + 1) := ⟨i.val, by simp⟩
      refine ⟨u, c, ?_, ?_⟩
      · have heq : sedge q = T.edge ⟨q.val, by omega⟩ := by simp [sedge, hqold]
        change phi (sedge q) = some c
        rw [heq]
        simpa using hc
      · have hiq : i.val < q.val + 1 := i.isLt
        have hiold : q.val < T.length - 2 := hqold
        have hi : i.val < T.length - 1 := by omega
        have hvi : S.vertex (Fin.castLT u (by omega)) =
            T.vertex (i.castLT (by omega)) := by
          dsimp [S, u]
          simp only [hi, ↓reduceDIte]
          apply congrArg T.vertex
          apply Fin.ext
          rfl
        change c ∈ MissingColors G phi
          (S.vertex (Fin.castLT u (by omega)))
        rw [hvi]
        exact hm
    · have hqb : q.val < T.length - 1 := by
        have hh := q.isLt
        dsimp [S] at hh
        exact hh
      have hqval : q.val = T.length - 2 := by omega
      have hT := hmin.1.2.1 ⟨T.length - 1, by omega⟩ (by omega)
      rcases hT with ⟨i, c, hc, hm⟩
      have hcg : c = gamma := by
        apply Option.some.inj
        exact hc.symm.trans (hrlast ▸ hrgamma)
      subst c
      have hilast : i.val ≠ T.length - 1 := by
        intro hi
        have hii : T.vertex (Fin.castLT i (by omega)) = T.vertex p := by
          apply congrArg T.vertex
          apply Fin.ext
          have := hi
          have hpval : p.val = T.length - 1 := by omega
          simpa [hpval] using this
        have hmiss : gamma ∉ PresentColors G phi (T.vertex p) := by
          rw [← hii]
          simpa [MissingColors] using hm
        exact hmiss (hii ▸ hpgamma)
      let u : Fin (q.val + 1) := ⟨i.val, by omega⟩
      refine ⟨u, gamma, ?_, ?_⟩
      · have heq : sedge q = T.edge ⟨T.length - 1, by omega⟩ := by
          simp [sedge, hqval]
        change phi (sedge q) = some gamma
        rw [heq]
        exact hc
      · have hiil : i.val < T.length - 1 := by omega
        have hvi : S.vertex (Fin.castLT u (by omega)) =
            T.vertex (i.castLT (by omega)) := by
          dsimp [S, u]
          simp only [hiil, ↓reduceDIte]
          apply congrArg T.vertex
          apply Fin.ext
          rfl
        change gamma ∈ MissingColors G phi
          (S.vertex (Fin.castLT u (by omega)))
        rw [hvi]
        exact hm
  have hnotElem : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet S) := by
    intro he
    have hjmem : T.vertex ⟨j.val, by omega⟩ ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      have hjS : j.val < S.length + 1 := by
        dsimp [S]
        omega
      refine Finset.mem_image.mpr ⟨⟨j.val, hjS⟩, Finset.mem_univ _, ?_⟩
      have hvj : svertex ⟨j.val, by omega⟩ = T.vertex ⟨j.val, by omega⟩ := by
        simp [svertex, show j.val < T.length - 1 by omega]
      exact hvj
    have hlmem : T.vertex (Fin.last T.length) ∈ TreeSequenceVertexSet S := by
      rw [TreeSequenceVertexSet]
      have hlastS : T.length - 1 < S.length + 1 := by
        dsimp [S]
        omega
      refine Finset.mem_image.mpr ⟨⟨T.length - 1, hlastS⟩, Finset.mem_univ _, ?_⟩
      simp [S]
    have hvne : T.vertex ⟨j.val, by omega⟩ ≠ T.vertex (Fin.last T.length) := by
      intro hh
      have hv := T.vertex_injective hh
      have hval : j.val = T.length := by
        simpa using congrArg Fin.val hv
      omega
    have hd := he hjmem hlmem hvne
    rw [Finset.disjoint_left] at hd
    exact hd (by simpa using hbj) (by simpa using hblast)
  have hbadS : TashTreeBadPair G k e0 phi S :=
    ⟨hmin.1.1, hTashS, hnotElem⟩
  have hindexS : TashTreePathIndex G S ≤ S.length := by
    have hs := (show TashTreeSuffixPath G S (TashTreePathIndex G S) by
      unfold TashTreePathIndex
      exact Nat.find_spec _)
    exact hs.2.1
  have hrank : TashTreeRankLess G S T := by
    left
    rw [hlast]
    have hslt : S.length < T.length := by dsimp [S]; omega
    exact lt_of_le_of_lt hindexS hslt
  have hsindex : T.length - 2 < S.length := by
    dsimp [S]
    omega
  refine ⟨P, S, ⟨T.length - 2, hsindex⟩, ?_⟩
  refine ⟨by dsimp [P]; omega, hPprefix, by dsimp [P, S]; omega,
    hPSegment, ?_, ?_, ?_, hbadS, hrank⟩
  · dsimp [S]
    omega
  · simp [S, hrlast]
  · simp [S]

end GoldbergSeymour

end
