/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycleSubgraphDegreeTwo
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathVertexIncidentEdge

-- [TABLET NODE: P4651T1CycleComplementaryArcs]

/-!
# P4651T1CycleComplementaryArcs

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CycleArcProof

private theorem splitInterior :
    ∀ (s : List GaussianInt), s.Nodup → ∀ x, x ∈ s → s.head? ≠ some x → s.getLast? ≠ some x → ∃
        l₁ l₂ y z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z := by
  classical
  intro s
  induction s with
  | nil =>
      intro hn x hx
      simp at hx
  | cons w s ih =>
      cases s with
      | nil =>
          intro hn x hx hh hl
          simp? at hx
          subst x
          exact False.elim (hh rfl)
      | cons v t =>
          intro hn x hx hh hl
          rcases List.mem_cons.mp hx with hxw | hxTail
          · subst x
            exact False.elim (hh rfl)
          · rcases List.mem_cons.mp hxTail with hxv | hxt
            · subst x
              cases t with
              | nil => exact False.elim (hl rfl)
              | cons z zs =>
                  refine ⟨[], zs, w, z, ?_, ?_⟩
                  · simp
                  · intro hwz
                    subst z
                    have hnot := (List.nodup_cons.mp hn).1
                    apply hnot
                    simp
            · have hvx : v ≠ x := by
                intro hvx
                subst v
                exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 hxt
              have hht : (v :: t).head? ≠ some x := by simpa using hvx
              have hlt : (v :: t).getLast? ≠ some x := by simpa using hl
              obtain ⟨l₁, l₂, y, z, hdec, hyz⟩ :=
                ih (List.nodup_cons.mp hn).2 x
                  (List.mem_cons.mpr (Or.inr hxt)) hht hlt
              refine ⟨w :: l₁, l₂, y, z, ?_, hyz⟩
              simp [hdec]

private theorem hSupport :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), ∀ (p : List GaussianInt), (p.Nodup)
        → (((2 : ℕ) ≤ p.length) → ((Kplus = (↑p.toFinset : Set GaussianInt)) → ((∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
            GaussianInt), p = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 :
            GaussianInt) ∨ b = a +
        ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e : Finset GaussianInt), e ∈
        Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List
        GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List GaussianInt), (q.Nodup)
        → (((2 : ℕ) ≤ q.length) → ((Kminus = (↑q.toFinset : Set GaussianInt)) → ((∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
            GaussianInt), q = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1 :
            GaussianInt) ∨ b = a +
        ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e : Finset GaussianInt), e ∈
        Fminus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List
        GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    X = {z | ∃ e ∈ GEdges, z ∈ e})))))))))) := by
  classical
  intro Kplus Kminus Fplus Fminus p hpN hpLen hKp hpStep hpEdges q hqN hqLen hKm hqStep hqEdges X
      GEdges
  apply Set.ext
  intro z
  constructor
  · intro hz
    simp only [X, Set.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨e, hze, he⟩ := SimpleGridPathVertexIncidentEdge Kplus Fplus
        ⟨p, hpN, hpLen, hKp, hpStep, hpEdges⟩ z hz
      exact ⟨e, Set.mem_union_left _ he, hze⟩
    · obtain ⟨e, hze, he⟩ := SimpleGridPathVertexIncidentEdge Kminus Fminus
        ⟨q, hqN, hqLen, hKm, hqStep, hqEdges⟩ z hz
      exact ⟨e, Set.mem_union_right _ he, hze⟩
  · rintro ⟨e, he, hze⟩
    simp only [GEdges, Set.mem_union] at he
    rcases he with he | he
    · have hx : z ∈ Kplus := by
        rw [hKp]
        rcases (hpEdges e).mp he with ⟨x, y, l₁, l₂, hpdecomp, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hze
        rw [hpdecomp]
        rcases hze with hze | hze
        · subst z
          simp
        · subst z
          simp
      exact Set.mem_union_left _ hx
    · have hx : z ∈ Kminus := by
        rw [hKm]
        rcases (hqEdges e).mp he with ⟨x, y, l₁, l₂, hqdecomp, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hze
        rw [hqdecomp]
        rcases hze with hze | hze
        · subst z
          simp
        · subst z
          simp
      exact Set.mem_union_right _ hx

private theorem noThree :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), (List GaussianInt) → ((List
        GaussianInt) → ((List GaussianInt) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    ∀ [Finite (↑X : Type)],
    let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
    (∀ v : X, Set.ncard (G.neighborSet v) ≤ 2) → (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (w
        : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), ∀ (hw : w ∈ X), ∀
        (hz : z ∈ X), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → G.Adj ⟨u, hu⟩ ⟨v, hv⟩ →
        G.Adj ⟨u, hu⟩ ⟨w, hw⟩ → G.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False)))) := by
  classical
  intro Kplus Kminus Fplus Fminus c p q X GEdges this G hdeg' u v w z hu hv hw hz huv huw huz hvw
      hvz hwz hUv hUw hUz
  let A : Set X := {⟨v, hv⟩, ⟨w, hw⟩, ⟨z, hz⟩}
  have hsub : A ⊆ G.neighborSet ⟨u, hu⟩ := by
    intro t ht
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht
    · simpa [ht] using hUv
    · simpa [ht] using hUw
    · simpa [ht] using hUz
  have hcard : A.ncard = 3 := by
    simp [A, hvw, hvz, hwz]
  have hle := Set.ncard_mono hsub
  have hbound := hdeg' ⟨u, hu⟩
  rw [hcard] at hle
  omega

private theorem path_other :
    (∀ (s : List GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y) →
        (∀ S, ∀ F, SimpleGridPath S F → ∀ x, x ∈ S → ∃ y, y ≠ x ∧ ({x, y} : Finset GaussianInt) ∈
        F) := by
  classical
  intro pair_ne S F hpath x hx
  rcases hpath with ⟨s, hsN, hsLen, hS, hsStep, hsEdges⟩
  obtain ⟨e, hxe, he⟩ := SimpleGridPathVertexIncidentEdge S F
    ⟨s, hsN, hsLen, hS, hsStep, hsEdges⟩ x hx
  rcases (hsEdges e).mp he with ⟨u, v, l₁, l₂, hdec, rfl⟩
  have hxe' : x = u ∨ x = v := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hxe
  have huv : u ≠ v := pair_ne s hsN u v l₁ l₂ hdec
  rcases hxe' with hxu | hxv
  · subst u
    refine ⟨v, huv.symm, ?_⟩
    exact (hsEdges {x, v}).2 ⟨x, v, l₁, l₂, hdec, rfl⟩
  · subst v
    refine ⟨u, huv, ?_⟩
    simpa [Finset.pair_comm] using
      (hsEdges {u, x}).2 ⟨u, x, l₁, l₂, hdec, rfl⟩

private theorem shared_no_interior_plus :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), (Disjoint Fplus Fminus) → (∀ (p :
            List GaussianInt), (p.Nodup) → ((Kplus = (↑p.toFinset : Set GaussianInt)) → ((∀ (e :
            Finset GaussianInt), e ∈ Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List
        GaussianInt), (q.Nodup) → (((2 : ℕ) ≤ q.length) → ((Kminus = (↑q.toFinset : Set
        GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
            (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1
        : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e :
            Finset GaussianInt), e ∈ Fminus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (s :
            List GaussianInt), s.Nodup → ∀ x, x ∈ s → s.head? ≠ some x → s.getLast? ≠ some x → ∃ l₁
        l₂ y z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ GEdges → G.Adj ⟨u, hu⟩ ⟨v, hv⟩) → ((∀ (u : GaussianInt), ∀ (v :
            GaussianInt), ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈
            X), ∀ (hw : w ∈ X), ∀ (hz : z ∈ X), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
            G.Adj ⟨u,
        hu⟩ ⟨v, hv⟩ → G.Adj ⟨u, hu⟩ ⟨w, hw⟩ → G.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False) → ((∀ (s : List
        GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y) → (∀ x, x ∈
        Kplus → x ∈ Kminus → p.head? ≠ some x → p.getLast? ≠ some x → False))))))))))))) := by
  classical
  intro Kplus Kminus Fplus Fminus hdisjoint p hpN hKp hpEdges q hqN hqLen hKm hqStep hqEdges
      splitInterior X GEdges G edgeAdj noThree pair_ne x hxplus hxminus hhead hlast
  have hxlist : x ∈ p := by
    rw [hKp] at hxplus
    simpa using hxplus
  obtain ⟨l₁, l₂, y, z, hdec, hyz⟩ := splitInterior p hpN x hxlist hhead hlast
  have hdecz : p = (l₁ ++ [y]) ++ x :: z :: l₂ := by simpa using hdec
  have he1 : ({y, x} : Finset GaussianInt) ∈ Fplus :=
    (hpEdges {y, x}).2 ⟨y, x, l₁, z :: l₂, hdec, rfl⟩
  have he2 : ({x, z} : Finset GaussianInt) ∈ Fplus :=
    (hpEdges {x, z}).2 ⟨x, z, l₁ ++ [y], l₂, hdecz, rfl⟩
  have hxy : y ≠ x := pair_ne p hpN y x l₁ (z :: l₂) hdec
  have hxz : x ≠ z := pair_ne p hpN x z (l₁ ++ [y]) l₂ hdecz
  have hyK : y ∈ Kplus := by
    rw [hKp]
    change y ∈ p.toFinset
    rw [hdec]
    simp
  have hzK : z ∈ Kplus := by
    rw [hKp]
    change z ∈ p.toFinset
    rw [hdec]
    simp
  have incident_other : ∃ w, w ≠ x ∧ ({x, w} : Finset GaussianInt) ∈ Fminus := by
    obtain ⟨e, hxe, he⟩ := SimpleGridPathVertexIncidentEdge Kminus Fminus
      ⟨q, hqN, hqLen, hKm, hqStep, hqEdges⟩ x hxminus
    rcases (hqEdges e).mp he with ⟨u, v, k₁, k₂, hdecq, rfl⟩
    have hxe' : x = u ∨ x = v := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxe
    have heuv : ({u, v} : Finset GaussianInt) ∈ Fminus :=
      (hqEdges {u, v}).2 ⟨u, v, k₁, k₂, hdecq, rfl⟩
    rcases hxe' with hxu | hxv
    · subst u
      refine ⟨v, ?_, ?_⟩
      · exact (pair_ne q hqN x v k₁ k₂ hdecq).symm
      · simpa using heuv
    · subst v
      refine ⟨u, ?_, ?_⟩
      · exact pair_ne q hqN u x k₁ k₂ hdecq
      · simpa [Finset.pair_comm] using heuv
  rcases incident_other with ⟨w, hxw, he3⟩
  have hwK : w ∈ Kminus := by
    rw [hKm]
    change w ∈ q.toFinset
    rcases (hqEdges {x, w}).mp he3 with ⟨u, v, k₁, k₂, hdecq, hpair⟩
    have hmem : w = u ∨ w = v := by
      have : w ∈ ({x, w} : Finset GaussianInt) := by simp
      rw [hpair] at this
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hmem with hmem | hmem
    · subst w
      rw [hdecq]
      simp
    · subst w
      rw [hdecq]
      simp
  have hyw : y ≠ w := by
    intro hyw
    subst w
    have hcontra := Set.disjoint_left.mp hdisjoint
    have hminus : ({y, x} : Finset GaussianInt) ∈ Fminus := by
      simpa [Finset.pair_comm] using he3
    exact hcontra he1 hminus
  have hzw : z ≠ w := by
    intro hzw
    subst w
    have hcontra := Set.disjoint_left.mp hdisjoint
    exact hcontra he2 he3
  exact noThree x y z w (Set.mem_union_left _ hxplus)
    (Set.mem_union_left _ hyK) (Set.mem_union_left _ hzK)
    (Set.mem_union_right _ hwK) hxy.symm hxz hxw.symm hyz hyw hzw
    (edgeAdj x y (Set.mem_union_left _ hxplus) (Set.mem_union_left _ hyK)
      hxy.symm (Set.mem_union_left _ (by simpa [Finset.pair_comm] using he1)))
    (edgeAdj x z (Set.mem_union_left _ hxplus) (Set.mem_union_left _ hzK)
      hxz (Set.mem_union_left _ he2))
    (edgeAdj x w (Set.mem_union_left _ hxplus) (Set.mem_union_right _ hwK)
      hxw.symm (Set.mem_union_right _ he3))

private theorem shared_no_interior_minus :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), (Disjoint Fplus Fminus) → (∀ (p :
            List GaussianInt), (p.Nodup) → (((2 : ℕ) ≤ p.length) → ((Kplus = (↑p.toFinset : Set
        GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
            (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1
        : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e :
            Finset GaussianInt), e ∈ Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List
        GaussianInt), (q.Nodup) → ((Kminus = (↑q.toFinset : Set GaussianInt)) → ((∀ (e : Finset
        GaussianInt), e ∈ Fminus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt)
        (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (s : List
        GaussianInt), s.Nodup → ∀ x, x ∈ s → s.head? ≠ some x → s.getLast? ≠ some x → ∃ l₁ l₂ y
        z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ GEdges → G.Adj ⟨u, hu⟩ ⟨v, hv⟩) → ((∀ (u : GaussianInt), ∀ (v :
            GaussianInt), ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈
            X), ∀ (hw : w ∈ X), ∀ (hz : z ∈ X), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
            G.Adj ⟨u,
        hu⟩ ⟨v, hv⟩ → G.Adj ⟨u, hu⟩ ⟨w, hw⟩ → G.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False) → ((∀ (s : List
        GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y) → (∀ x, x ∈
        Kplus → x ∈ Kminus → q.head? ≠ some x → q.getLast? ≠ some x → False))))))))))))) := by
  classical
  intro Kplus Kminus Fplus Fminus hdisjoint p hpN hpLen hKp hpStep hpEdges q hqN hKm hqEdges
      splitInterior X GEdges G edgeAdj noThree pair_ne x hxplus hxminus hhead hlast
  have hxlist : x ∈ q := by
    rw [hKm] at hxminus
    simpa using hxminus
  obtain ⟨l₁, l₂, y, z, hdec, hyz⟩ := splitInterior q hqN x hxlist hhead hlast
  have hdecz : q = (l₁ ++ [y]) ++ x :: z :: l₂ := by simpa using hdec
  have he1 : ({y, x} : Finset GaussianInt) ∈ Fminus :=
    (hqEdges {y, x}).2 ⟨y, x, l₁, z :: l₂, hdec, rfl⟩
  have he2 : ({x, z} : Finset GaussianInt) ∈ Fminus :=
    (hqEdges {x, z}).2 ⟨x, z, l₁ ++ [y], l₂, hdecz, rfl⟩
  have hxy : y ≠ x := pair_ne q hqN y x l₁ (z :: l₂) hdec
  have hxz : x ≠ z := pair_ne q hqN x z (l₁ ++ [y]) l₂ hdecz
  have hyK : y ∈ Kminus := by
    rw [hKm]
    change y ∈ q.toFinset
    rw [hdec]
    simp
  have hzK : z ∈ Kminus := by
    rw [hKm]
    change z ∈ q.toFinset
    rw [hdec]
    simp
  have incident_other : ∃ w, w ≠ x ∧ ({x, w} : Finset GaussianInt) ∈ Fplus := by
    obtain ⟨e, hxe, he⟩ := SimpleGridPathVertexIncidentEdge Kplus Fplus
      ⟨p, hpN, hpLen, hKp, hpStep, hpEdges⟩ x hxplus
    rcases (hpEdges e).mp he with ⟨u, v, k₁, k₂, hdecq, rfl⟩
    have hxe' : x = u ∨ x = v := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hxe
    have heuv : ({u, v} : Finset GaussianInt) ∈ Fplus :=
      (hpEdges {u, v}).2 ⟨u, v, k₁, k₂, hdecq, rfl⟩
    rcases hxe' with hxu | hxv
    · subst u
      refine ⟨v, ?_, ?_⟩
      · exact (pair_ne p hpN x v k₁ k₂ hdecq).symm
      · simpa using heuv
    · subst v
      refine ⟨u, ?_, ?_⟩
      · exact pair_ne p hpN u x k₁ k₂ hdecq
      · simpa [Finset.pair_comm] using heuv
  rcases incident_other with ⟨w, hxw, he3⟩
  have hwK : w ∈ Kplus := by
    rw [hKp]
    change w ∈ p.toFinset
    rcases (hpEdges {x, w}).mp he3 with ⟨u, v, k₁, k₂, hdecq, hpair⟩
    have hmem : w = u ∨ w = v := by
      have : w ∈ ({x, w} : Finset GaussianInt) := by simp
      rw [hpair] at this
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hmem with hmem | hmem
    · subst w
      rw [hdecq]
      simp
    · subst w
      rw [hdecq]
      simp
  have hyw : y ≠ w := by
    intro hyw
    subst w
    have hcontra := Set.disjoint_left.mp hdisjoint.symm
    have hplus : ({y, x} : Finset GaussianInt) ∈ Fplus := by
      simpa [Finset.pair_comm] using he3
    exact hcontra he1 hplus
  have hzw : z ≠ w := by
    intro hzw
    subst w
    have hcontra := Set.disjoint_left.mp hdisjoint.symm
    exact hcontra he2 he3
  exact noThree x y z w (Set.mem_union_right _ hxminus)
    (Set.mem_union_right _ hyK) (Set.mem_union_right _ hzK)
    (Set.mem_union_left _ hwK) hxy.symm hxz hxw.symm hyz hyw hzw
    (edgeAdj x y (Set.mem_union_right _ hxminus) (Set.mem_union_right _ hyK)
      hxy.symm (Set.mem_union_right _ (by simpa [Finset.pair_comm] using he1)))
    (edgeAdj x z (Set.mem_union_right _ hxminus) (Set.mem_union_right _ hzK)
      hxz (Set.mem_union_right _ he2))
    (edgeAdj x w (Set.mem_union_right _ hxminus) (Set.mem_union_left _ hwK)
      hxw.symm (Set.mem_union_left _ he3))

private theorem pOrientation :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt),
        ∀ (a : GaussianInt), (a ∈ Kplus ∩ Kminus) → (∀ (p : List GaussianInt), (r a ∈ Kminus) →
        ((r a ∈ Kplus) → ((a ≠ r a) → ((∀ x, x ∈ Kplus → x ∈ Kminus → p.head? = some x ∨
        p.getLast? = some x) → ((p.head? = some a ∧ p.getLast? = some (r a)) ∨ (p.head? = some (r
        a) ∧ p.getLast? = some a)))))) := by
  classical
  intro Kplus Kminus r a ha p hara harp hdistinct pEndpoint
  rcases pEndpoint a ha.1 ha.2 with haH | haL <;>
    rcases pEndpoint (r a) harp hara with hrH | hrL
  · have : a = r a := Option.some.inj (haH.symm.trans hrH)
    exact False.elim (hdistinct this)
  · exact Or.inl ⟨haH, hrL⟩
  · exact Or.inr ⟨hrH, haL⟩
  · have : a = r a := Option.some.inj (haL.symm.trans hrL)
    exact False.elim (hdistinct this)

private theorem qOrientation :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt),
        ∀ (a : GaussianInt), (a ∈ Kplus ∩ Kminus) → (∀ (q : List GaussianInt), (r a ∈ Kminus) →
        ((r a ∈ Kplus) → ((a ≠ r a) → ((∀ x, x ∈ Kplus → x ∈ Kminus → q.head? = some x ∨
        q.getLast? = some x) → ((q.head? = some (r a) ∧ q.getLast? = some a) ∨ (q.head? = some a
        ∧ q.getLast? = some (r a))))))) := by
  classical
  intro Kplus Kminus r a ha q hara harp hdistinct qEndpoint
  rcases qEndpoint a ha.1 ha.2 with haH | haL <;>
    rcases qEndpoint (r a) harp hara with hrH | hrL
  · have : a = r a := Option.some.inj (haH.symm.trans hrH)
    exact False.elim (hdistinct this)
  · exact Or.inr ⟨haH, hrL⟩
  · exact Or.inl ⟨hrH, haL⟩
  · have : a = r a := Option.some.inj (haL.symm.trans hrL)
    exact False.elim (hdistinct this)

private theorem twoNeighbors :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), ∀ (r : GaussianInt → GaussianInt),
            ∀ (a : GaussianInt), (Disjoint Fplus Fminus) → ((a ∈ Kplus ∩ Kminus) → (∀ (p : List
        GaussianInt), (p.Nodup) → (((2 : ℕ) ≤ p.length) → ((Kplus = (↑p.toFinset : Set
        GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
            (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1
        : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e :
            Finset GaussianInt), e ∈ Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List
        GaussianInt), (q.Nodup) → (((2 : ℕ) ≤ q.length) → ((Kminus = (↑q.toFinset : Set
        GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
            (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1
        : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e :
            Finset GaussianInt), e ∈ Fminus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((r a ∈
        Kminus) → ((r a ∈ Kplus) → ((∀ (s : List GaussianInt), s.Nodup → ∀ x, x ∈ s → s.head? ≠
        some x → s.getLast? ≠ some x → ∃ l₁ l₂ y z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    (∀ (s : List GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y) →
        ((∀ S, ∀ F, SimpleGridPath S F → ∀ x, x ∈ S → ∃ y, y ≠ x ∧ ({x, y} : Finset GaussianInt)
        ∈ F) → (((p.head? = some a ∧ p.getLast? = some (r a)) ∨ (p.head? = some (r a) ∧
        p.getLast? = some a)) → (((q.head? = some (r a) ∧ q.getLast? = some a) ∨ (q.head? = some
        a ∧ q.getLast? = some (r a))) → (∀ x, x ∈ X → ∃ y z, y ≠ z ∧ x ≠ y ∧ x ≠ z ∧ ({x, y} :
        Finset GaussianInt) ∈ GEdges ∧ ({x, z} : Finset GaussianInt) ∈ GEdges)))))))))))))))))))
            := by
  classical
  intro Kplus Kminus Fplus Fminus r a hdisjoint ha p hpN hpLen hKp hpStep hpEdges q hqN hqLen hKm
      hqStep hqEdges hara harp splitInterior X GEdges pair_ne path_other pOrientation
      qOrientation x hx
  simp only [X, Set.mem_union] at hx
  rcases hx with hxP | hxM
  · by_cases hxM : x ∈ Kminus
    · obtain ⟨y, hyx, heY⟩ := path_other Kplus Fplus
        ⟨p, hpN, hpLen, hKp, hpStep, hpEdges⟩ x hxP
      obtain ⟨z, hzx, heZ⟩ := path_other Kminus Fminus
        ⟨q, hqN, hqLen, hKm, hqStep, hqEdges⟩ x hxM
      have hyz : y ≠ z := by
        intro h
        subst z
        exact (Set.disjoint_left.mp hdisjoint) heY heZ
      exact ⟨y, z, hyz, hyx.symm, hzx.symm,
        Set.mem_union_left _ heY, Set.mem_union_right _ heZ⟩
    · have hhead : p.head? ≠ some x := by
        intro hh
        rcases pOrientation with ⟨hph, _⟩ | ⟨hph, _⟩
        · have hxa : x = a := Option.some.inj (hh.symm.trans hph)
          apply hxM
          simpa [hxa] using ha.2
        · have hxr : x = r a := Option.some.inj (hh.symm.trans hph)
          apply hxM
          simpa [hxr] using hara
      have hlast : p.getLast? ≠ some x := by
        intro hh
        rcases pOrientation with ⟨_, hpl⟩ | ⟨_, hpl⟩
        · have hxr : x = r a := Option.some.inj (hh.symm.trans hpl)
          apply hxM
          simpa [hxr] using hara
        · have hxa : x = a := Option.some.inj (hh.symm.trans hpl)
          apply hxM
          simpa [hxa] using ha.2
      have hxlist : x ∈ p := by rw [hKp] at hxP; simpa using hxP
      obtain ⟨l₁, l₂, y, z, hdec, hyz⟩ := splitInterior p hpN x hxlist hhead hlast
      have hdecz : p = (l₁ ++ [y]) ++ x :: z :: l₂ := by simpa using hdec
      have hxy : y ≠ x := pair_ne p hpN y x l₁ (z :: l₂) hdec
      have hxz : x ≠ z := pair_ne p hpN x z (l₁ ++ [y]) l₂ hdecz
      have heY : ({x, y} : Finset GaussianInt) ∈ Fplus := by
        simpa [Finset.pair_comm] using
          (hpEdges {y, x}).2 ⟨y, x, l₁, z :: l₂, hdec, rfl⟩
      have heZ : ({x, z} : Finset GaussianInt) ∈ Fplus :=
        (hpEdges {x, z}).2 ⟨x, z, l₁ ++ [y], l₂, hdecz, rfl⟩
      exact ⟨y, z, hyz, hxy.symm, hxz,
        Set.mem_union_left _ heY, Set.mem_union_left _ heZ⟩
  · by_cases hxP : x ∈ Kplus
    · obtain ⟨y, hyx, heY⟩ := path_other Kplus Fplus
        ⟨p, hpN, hpLen, hKp, hpStep, hpEdges⟩ x hxP
      obtain ⟨z, hzx, heZ⟩ := path_other Kminus Fminus
        ⟨q, hqN, hqLen, hKm, hqStep, hqEdges⟩ x hxM
      have hyz : y ≠ z := by
        intro h
        subst z
        exact (Set.disjoint_left.mp hdisjoint) heY heZ
      exact ⟨y, z, hyz, hyx.symm, hzx.symm,
        Set.mem_union_left _ heY, Set.mem_union_right _ heZ⟩
    · have hhead : q.head? ≠ some x := by
        intro hh
        rcases qOrientation with ⟨hqh, _⟩ | ⟨hqh, _⟩
        · have hxr : x = r a := Option.some.inj (hh.symm.trans hqh)
          apply hxP
          simpa [hxr] using harp
        · have hxa : x = a := Option.some.inj (hh.symm.trans hqh)
          apply hxP
          simpa [hxa] using ha.1
      have hlast : q.getLast? ≠ some x := by
        intro hh
        rcases qOrientation with ⟨_, hql⟩ | ⟨_, hql⟩
        · have hxa : x = a := Option.some.inj (hh.symm.trans hql)
          apply hxP
          simpa [hxa] using ha.1
        · have hxr : x = r a := Option.some.inj (hh.symm.trans hql)
          apply hxP
          simpa [hxr] using harp
      have hxlist : x ∈ q := by rw [hKm] at hxM; simpa using hxM
      obtain ⟨l₁, l₂, y, z, hdec, hyz⟩ := splitInterior q hqN x hxlist hhead hlast
      have hdecz : q = (l₁ ++ [y]) ++ x :: z :: l₂ := by simpa using hdec
      have hxy : y ≠ x := pair_ne q hqN y x l₁ (z :: l₂) hdec
      have hxz : x ≠ z := pair_ne q hqN x z (l₁ ++ [y]) l₂ hdecz
      have heY : ({x, y} : Finset GaussianInt) ∈ Fminus := by
        simpa [Finset.pair_comm] using
          (hqEdges {y, x}).2 ⟨y, x, l₁, z :: l₂, hdec, rfl⟩
      have heZ : ({x, z} : Finset GaussianInt) ∈ Fminus :=
        (hqEdges {x, z}).2 ⟨x, z, l₁ ++ [y], l₂, hdecz, rfl⟩
      exact ⟨y, z, hyz, hxy.symm, hxz,
        Set.mem_union_right _ heY, Set.mem_union_right _ heZ⟩

private theorem hEend :
    ∀ (V : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (c : List GaussianInt), ∀ (cx :
        GaussianInt), ∀ (cy : GaussianInt), (V = (↑c.toFinset : Set GaussianInt)) → ((∀ (e :
        Finset GaussianInt), e ∈ E ↔ e = {cy, cx} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ :
        List GaussianInt) (l₂ : List GaussianInt), c = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((cx ∈
        V) → ((cy ∈ V) → (∀ e, e ∈ E → ∀ x, x ∈ e → x ∈ V)))) := by
  classical
  intro V E c cx cy hVcyc hcEdges hcxV hcyV e he x hx
  rcases (hcEdges e).mp he with hcloseE | ⟨u, v, l₁, l₂, hdec, hpair⟩
  · rw [hcloseE] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact hcyV
    · rw [hx]
      exact hcxV
  · rw [hpair] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx]
      rw [hVcyc]
      change u ∈ c.toFinset
      rw [hdec]
      simp
    · rw [hx]
      rw [hVcyc]
      change v ∈ c.toFinset
      rw [hdec]
      simp

private theorem hEne :
    ∀ (E : Set (Finset GaussianInt)), ∀ (c : List GaussianInt), ∀ (cx : GaussianInt), ∀ (cy :
        GaussianInt), (FourNeighborAdjacent cy cx) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt),
        ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), c = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b) → ((∀ (e : Finset GaussianInt), e ∈ E ↔ e = {cy, cx} ∨ ∃ (a :
        GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), c = l₁ ++
        a :: b :: l₂ ∧ e = {a, b}) → ((List GaussianInt) → ((List GaussianInt) → ((∀ u, ∀ v,
            FourNeighborAdjacent u v → u ≠ v) → (∀ x, ∀ y, ({x, y} : Finset GaussianInt) ∈ E → x ≠
        y)))))) := by
  classical
  intro E c cx cy hclose hcStep hcEdges p q fourNe x y he hxy
  have hcard : ({x, y} : Finset GaussianInt).card = 1 := by simp [hxy]
  rcases (hcEdges {x, y}).mp he with hcloseE | ⟨u, v, l₁, l₂, hdec, hpair⟩
  · have hne := fourNe cy cx hclose
    have hcard' := congrArg Finset.card hcloseE
    rw [hcard, Finset.card_pair hne] at hcard'
    omega
  · have hstep : FourNeighborAdjacent u v := hcStep u v l₁ l₂ hdec
    have hne := fourNe u v hstep
    have hcard' := congrArg Finset.card hpair
    rw [hcard, Finset.card_pair hne] at hcard'
    omega

private theorem cycleOther :
    ∀ (E : Set (Finset GaussianInt)), ∀ (c : List GaussianInt), ∀ (cx : GaussianInt), ∀ (cy :
        GaussianInt), (FourNeighborAdjacent cy cx) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt),
        ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), c = l₁ ++ a :: b :: l₂ →
        FourNeighborAdjacent a b) → ((∀ (e : Finset GaussianInt), e ∈ E ↔ e = {cy, cx} ∨ ∃ (a :
        GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), c = l₁ ++
        a :: b :: l₂ ∧ e = {a, b}) → ((∀ u, ∀ v, FourNeighborAdjacent u v → u ≠ v) → (∀ e, e ∈ E
        → ∀ x, x ∈ e → ∃ y, y ≠ x ∧ e = {x, y})))) := by
  classical
  intro E c cx cy hclose hcStep hcEdges fourNe e he x hx
  rcases (hcEdges e).mp he with hcloseE | ⟨u, v, l₁, l₂, hdec, hpair⟩
  · have hmem : x = cy ∨ x = cx := by
      rw [hcloseE] at hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hmem with hmem | hmem
    · subst x
      exact ⟨cx, (fourNe cy cx hclose).symm, hcloseE⟩
    · subst x
      refine ⟨cy, fourNe cy cx hclose, ?_⟩
      simpa [Finset.pair_comm] using hcloseE
  · have hmem : x = u ∨ x = v := by
      rw [hpair] at hx
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    have hne := fourNe u v (hcStep u v l₁ l₂ hdec)
    rcases hmem with hmem | hmem
    · subst x
      exact ⟨v, hne.symm, hpair⟩
    · subst x
      refine ⟨u, hne, ?_⟩
      simpa [Finset.pair_comm] using hpair

private theorem noThreeE :
    ∀ (E : Set (Finset GaussianInt)), (List GaussianInt) → ((List GaussianInt) → ((List
        GaussianInt) → (
    let U : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    ∀ [Finite (↑U : Type)],
    let C : SimpleGraph U := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ E
    (∀ v : U, Set.ncard (C.neighborSet v) ≤ 2) → (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (w
        : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ U), ∀ (hv : v ∈ U), ∀ (hw : w ∈ U), ∀
        (hz : z ∈ U), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → C.Adj ⟨u, hu⟩ ⟨v, hv⟩ →
        C.Adj ⟨u, hu⟩ ⟨w, hw⟩ → C.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False)))) := by
  classical
  intro E c p q U this C hdegE' u v w z hu hv hw hz huv huw huz hvw hvz hwz hUv hUw hUz
  let A : Set U := {⟨v, hv⟩, ⟨w, hw⟩, ⟨z, hz⟩}
  have hsub : A ⊆ C.neighborSet ⟨u, hu⟩ := by
    intro t ht
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht | ht
    · simpa [ht] using hUv
    · simpa [ht] using hUw
    · simpa [ht] using hUz
  have hcard : A.ncard = 3 := by
    simp [A, hvw, hvz, hwz]
  have hle := Set.ncard_mono hsub
  have hbound := hdegE' ⟨u, hu⟩
  rw [hcard] at hle
  omega

private theorem edgeCovered :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
        ∀ (Fplus : Set (Finset GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)),
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    (GEdges ⊆ E) → ((X = {z | ∃ e ∈ GEdges, z ∈ e}) → ((∀ x, x ∈ X → ∃ y z, y ≠ z ∧ x ≠ y ∧ x ≠ z
        ∧ ({x, y} : Finset GaussianInt) ∈ GEdges ∧ ({x, z} : Finset GaussianInt) ∈ GEdges) → ((∀
            x, ∀ y, ({x, y} : Finset GaussianInt) ∈ E → x ≠ y) → (
    let U : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    let C : SimpleGraph U := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ E
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ U), ∀ (hv : v ∈ U), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ E → C.Adj ⟨u, hu⟩ ⟨v, hv⟩) → ((∀ (u : GaussianInt), ∀ (v :
            GaussianInt), ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ U), ∀ (hv : v ∈
            U), ∀ (hw : w ∈ U), ∀ (hz : z ∈ U), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
            C.Adj ⟨u,
        hu⟩ ⟨v, hv⟩ → C.Adj ⟨u, hu⟩ ⟨w, hw⟩ → C.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False) → ((X ⊆ U) → (∀ x, x
        ∈ X → ∀ y, ({x, y} : Finset GaussianInt) ∈ E → ({x, y} : Finset GaussianInt) ∈
        GEdges))))))) := by
  classical
  intro Kplus Kminus E Fplus Fminus X GEdges hGE hSupport twoNeighbors hEne U C edgeAdjE noThreeE
      hXU x hx y hxyE
  obtain ⟨u, v, huv, hxu, hxv, hxuE, hxvE⟩ := twoNeighbors x hx
  have hxU := hXU hx
  have huX : u ∈ X := by
    rw [hSupport]
    exact ⟨{x, u}, hxuE, by simp⟩
  have hvX : v ∈ X := by
    rw [hSupport]
    exact ⟨{x, v}, hxvE, by simp⟩
  have huU := hXU huX
  have hvU := hXU hvX
  have hyU : y ∈ U := ⟨{x, y}, hxyE, by simp⟩
  by_cases hyu : y = u
  · subst y
    exact hxuE
  · by_cases hyv : y = v
    · subst y
      exact hxvE
    · have hneXY := hEne x y hxyE
      exact False.elim (noThreeE x u v y hxU huU hvU hyU
        hxu hxv hneXY huv (by intro h; exact hyu h.symm)
        (by intro h; exact hyv h.symm)
        (edgeAdjE x u hxU huU hxu (hGE hxuE))
        (edgeAdjE x v hxU hvU hxv (hGE hxvE))
        (edgeAdjE x y hxU hyU hneXY hxyE))

private theorem allTail :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
        ∀ (c : List GaussianInt), ∀ (cx : GaussianInt), ∀ (cy : GaussianInt), (∀ (e : Finset
        GaussianInt), e ∈ E ↔ e = {cy, cx} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), c = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    (∀ x, x ∈ X → ∀ y, ({x, y} : Finset GaussianInt) ∈ E → y ∈ X) → (∀ pre, ∀ x, ∀ s, c = pre ++
        x :: s → x ∈ X → ∀ z, z ∈ s → z ∈ X)) := by
  classical
  intro Kplus Kminus E c cx cy hcEdges X edgeClosure pre x s
  induction s generalizing pre x with
  | nil =>
      intro hdec hx z hz
      simp at hz
  | cons y ys ih =>
      intro hdec hx z hz
      have hey : ({x, y} : Finset GaussianInt) ∈ E :=
        (hcEdges {x, y}).2 (Or.inr ⟨x, y, pre, ys, hdec, rfl⟩)
      have hyX := edgeClosure x hx y hey
      have hdec' : c = (pre ++ [x]) ++ y :: ys := by simpa using hdec
      have hzy : z = y ∨ z ∈ ys := by simpa using hz
      rcases hzy with hzy | hzy
      · subst z
        exact hyX
      · exact ih (pre ++ [x]) y hdec' hyX z hzy

private theorem splitAt :
    ∀ (s : List GaussianInt), ∀ (x : GaussianInt), x ∈ s → ∃ l t, s = l ++ x :: t := by
  classical
  intro s
  induction s with
  | nil => intro x hx; simp at hx
  | cons y ys ih =>
      intro x hx
      rcases List.mem_cons.mp hx with hxy | hxy
      · subst x
        exact ⟨[], ys, rfl⟩
      · rcases ih x hxy with ⟨l, t, h⟩
        exact ⟨y :: l, t, by simp [h, List.cons_append]⟩

private theorem hIntersection :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt),
        ∀ (a : GaussianInt), (a ∈ Kplus ∩ Kminus) → (∀ (p : List GaussianInt), (r a ∈ Kminus) →
        ((r a ∈ Kplus) → ((∀ x, x ∈ Kplus → x ∈ Kminus → p.head? = some x ∨ p.getLast? = some x)
        → (((p.head? = some a ∧ p.getLast? = some (r a)) ∨ (p.head? = some (r a) ∧ p.getLast? =
        some a)) → (Kplus ∩ Kminus = {a, r a}))))) := by
  classical
  intro Kplus Kminus r a ha p hara harp pEndpoint pOrientation
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hEnd := pEndpoint x hx.1 hx.2
    rcases pOrientation with ⟨hpH, hpL⟩ | ⟨hpH, hpL⟩
    · rcases hEnd with hxH | hxL
      · have hxa : x = a := Option.some.inj (hxH.symm.trans hpH)
        simp [hxa]
      · have hxr : x = r a := Option.some.inj (hxL.symm.trans hpL)
        simp [hxr]
    · rcases hEnd with hxH | hxL
      · have hxr : x = r a := Option.some.inj (hxH.symm.trans hpH)
        simp [hxr]
      · have hxa : x = a := Option.some.inj (hxL.symm.trans hpL)
        simp [hxa]
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact ⟨ha.1, ha.2⟩
    · subst x
      exact ⟨harp, hara⟩

private theorem hEdgeCoverage :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E :
        Set (Finset GaussianInt)), ∀ (Fplus : Set (Finset GaussianInt)), ∀ (Fminus : Set (Finset
        GaussianInt)), ∀ (c : List GaussianInt), ∀ (cx : GaussianInt), ∀ (cy : GaussianInt), (∀
            (e : Finset GaussianInt), e ∈ E ↔ e = {cy, cx} ∨ ∃ (a : GaussianInt) (b : GaussianInt)
        (l₁ : List GaussianInt) (l₂ : List GaussianInt), c = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    (∀ e, e ∈ E → ∀ x, x ∈ e → x ∈ V) → ((∀ e, e ∈ E → ∀ x, x ∈ e → ∃ y, y ≠ x ∧ e = {x, y}) →
        ((∀ x, x ∈ X → ∀ y, ({x, y} : Finset GaussianInt) ∈ E → ({x, y} : Finset GaussianInt) ∈
        GEdges) → ((V ⊆ X) → (∀ e, e ∈ E → e ∈ Fplus ∨ e ∈ Fminus))))) := by
  classical
  intro V Kplus Kminus E Fplus Fminus c cx cy hcEdges X GEdges hEend cycleOther edgeCovered hVtoX
      e he
  have heNonempty : e.Nonempty := by
    rcases (hcEdges e).mp he with hcloseE | ⟨u, v, l₁, l₂, hdec, hpair⟩
    · rw [hcloseE]
      simp
    · rw [hpair]
      simp
  obtain ⟨x, hxe⟩ := heNonempty
  obtain ⟨y, _, hpair⟩ := cycleOther e he x hxe
  have hxX : x ∈ X := hVtoX (hEend e he x hxe)
  have hexy : ({x, y} : Finset GaussianInt) ∈ E := by
    rw [← hpair]
    exact he
  have heG := edgeCovered x hxX y hexy
  rw [hpair]
  simp only [GEdges, Set.mem_union] at heG
  exact heG

private theorem hp'Orient :
    ∀ (r : GaussianInt → GaussianInt), ∀ (a : GaussianInt), ∀ (p : List GaussianInt), (a ≠ r a) →
        (((p.head? = some a ∧ p.getLast? = some (r a)) ∨ (p.head? = some (r a) ∧ p.getLast? =
        some a)) → (
    let p' : List GaussianInt := if p.head? = some a then p else p.reverse
    p'.head? = some a ∧ p'.getLast? = some (r a))) := by
  classical
  intro r a p hdistinct pOrientation p'
  dsimp [p']
  split_ifs with h
  · rcases pOrientation with hpF | hpR
    · exact hpF
    · have hab : a = r a := Option.some.inj (h.symm.trans hpR.1)
      exact False.elim (hdistinct hab)
  · rcases pOrientation with hpF | hpR
    · exact False.elim (h hpF.1)
    · constructor
      · simpa [List.head?_reverse] using hpR.2
      · simpa [List.getLast?_reverse] using hpR.1

private theorem hq'Orient :
    ∀ (r : GaussianInt → GaussianInt), ∀ (a : GaussianInt), ∀ (q : List GaussianInt), (a ≠ r a) →
        (((q.head? = some (r a) ∧ q.getLast? = some a) ∨ (q.head? = some a ∧ q.getLast? = some (r
        a))) → (
    let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
    q'.head? = some (r a) ∧ q'.getLast? = some a)) := by
  classical
  intro r a q hdistinct qOrientation q'
  dsimp [q']
  split_ifs with h
  · rcases qOrientation with hqF | hqR
    · exact hqF
    · have hab : r a = a := Option.some.inj (h.symm.trans hqR.1)
      exact False.elim (hdistinct hab.symm)
  · rcases qOrientation with hqF | hqR
    · exact False.elim (h hqF.1)
    · constructor
      · simpa [List.head?_reverse] using hqR.2
      · simpa [List.getLast?_reverse] using hqR.1

private theorem hp'Edges :
    ∀ (Fplus : Set (Finset GaussianInt)), ∀ (a : GaussianInt), ∀ (p : List GaussianInt), (∀ (e :
        Finset GaussianInt), e ∈ Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (
    let p' : List GaussianInt := if p.head? = some a then p else p.reverse
    ∀ x, ∀ y, ∀ l₁, ∀ l₂, p' = l₁ ++ x :: y :: l₂ → ({x, y} : Finset GaussianInt) ∈ Fplus) := by
  classical
  intro Fplus a p hpEdges p' x y l₁ l₂ hdec
  by_cases hforward : p.head? = some a
  · have hdec' : p = l₁ ++ x :: y :: l₂ := by simpa [p', hforward] using hdec
    exact (hpEdges {x, y}).2 ⟨x, y, l₁, l₂, hdec', rfl⟩
  · have hdec' : p.reverse = l₁ ++ x :: y :: l₂ := by
      simpa [p', hforward] using hdec
    have horig : p = l₂.reverse ++ y :: x :: l₁.reverse := by
      calc
        p = p.reverse.reverse := (List.reverse_reverse p).symm
        _ = (l₁ ++ x :: y :: l₂).reverse := congrArg List.reverse hdec'
        _ = l₂.reverse ++ y :: x :: l₁.reverse := by simp [List.reverse_append]
    exact (hpEdges {x, y}).2 ⟨y, x, l₂.reverse, l₁.reverse, horig,
      by simp [Finset.pair_comm]⟩

private theorem hq'Edges :
    ∀ (Fminus : Set (Finset GaussianInt)), ∀ (r : GaussianInt → GaussianInt), ∀ (a :
        GaussianInt), ∀ (q : List GaussianInt), (∀ (e : Finset GaussianInt), e ∈ Fminus ↔ ∃ (a :
        GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), q = l₁ ++
        a :: b :: l₂ ∧ e = {a, b}) → (
    let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
    ∀ x, ∀ y, ∀ l₁, ∀ l₂, q' = l₁ ++ x :: y :: l₂ → ({x, y} : Finset GaussianInt) ∈ Fminus) := by
  classical
  intro Fminus r a q hqEdges q' x y l₁ l₂ hdec
  by_cases hforward : q.head? = some (r a)
  · have hdec' : q = l₁ ++ x :: y :: l₂ := by simpa [q', hforward] using hdec
    exact (hqEdges {x, y}).2 ⟨x, y, l₁, l₂, hdec', rfl⟩
  · have hdec' : q.reverse = l₁ ++ x :: y :: l₂ := by
      simpa [q', hforward] using hdec
    have horig : q = l₂.reverse ++ y :: x :: l₁.reverse := by
      calc
        q = q.reverse.reverse := (List.reverse_reverse q).symm
        _ = (l₁ ++ x :: y :: l₂).reverse := congrArg List.reverse hdec'
        _ = l₂.reverse ++ y :: x :: l₁.reverse := by simp [List.reverse_append]
    exact (hqEdges {x, y}).2 ⟨y, x, l₂.reverse, l₁.reverse, horig,
      by simp [Finset.pair_comm]⟩

end CycleArcProof

namespace CycleArcDetails

private theorem hara :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt),
        ∀ (a : GaussianInt), (r '' Kplus = Kminus) → ((a ∈ Kplus ∩ Kminus) → (r a ∈ Kminus)) := by
  classical
  intro Kplus Kminus r a hcontact ha
  rw [← hcontact]
  exact ⟨a, ha.1, rfl⟩

private theorem harp :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt),
        ∀ (a : GaussianInt), (Function.Involutive r) → ((r '' Kplus = Kminus) → ((a ∈ Kplus ∩
        Kminus) → (r a ∈ Kplus))) := by
  classical
  intro Kplus Kminus r a hinv hcontact ha
  have hImage : a ∈ r '' Kplus := by rw [hcontact]; exact ha.2
  rcases hImage with ⟨z, hz, hza⟩
  have hzr : z = r a := by
    calc z = r (r z) := (hinv z).symm
      _ = r a := by rw [hza]
  rw [← hzr]
  exact hz

private theorem hdistinct :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r :
        GaussianInt → GaussianInt), ∀ (a : GaussianInt), (Kplus ⊆ V) → ((∀ z ∈ V, r z ≠ z) → ((a
        ∈ Kplus ∩ Kminus) → (a ≠ r a))) := by
  classical
  intro V Kplus Kminus r a hpV hfreeV ha h
  exact hfreeV a (hpV ha.1) h.symm

private theorem hXV :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), (Kplus ⊆
        V) → ((Kminus ⊆ V) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    X ⊆ V)) := by
  classical
  intro V Kplus Kminus hpV hmV X z hz
  simp only [X, Set.mem_union] at hz
  rcases hz with hz | hz
  · exact hpV hz
  · exact hmV hz

private theorem hGE :
    ∀ (E : Set (Finset GaussianInt)), ∀ (Fplus : Set (Finset GaussianInt)), ∀ (Fminus : Set
        (Finset GaussianInt)), (Fplus ⊆ E) → ((Fminus ⊆ E) → (
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    GEdges ⊆ E)) := by
  classical
  intro E Fplus Fminus hpE hmE GEdges e he
  simp only [GEdges, Set.mem_union] at he
  rcases he with he | he
  · exact hpE he
  · exact hmE he

private theorem hXfinite :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (p : List GaussianInt), (Kplus =
        (↑p.toFinset : Set GaussianInt)) → (∀ (q : List GaussianInt), (Kminus = (↑q.toFinset :
        Set GaussianInt)) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    X.Finite)) := by
  classical
  intro Kplus Kminus p hKp q hKm X
  change (Kplus ∪ Kminus).Finite
  rw [hKp, hKm]
  exact (Finset.finite_toSet p.toFinset).union
    (Finset.finite_toSet q.toFinset)

private theorem edgeAdj :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)),
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
    ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ GEdges → G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  classical
  intro Kplus Kminus Fplus Fminus X GEdges G u v hu hv huv hedge
  simp only [G, SimpleGraph.fromRel_adj]
  exact ⟨by intro h; apply huv; exact congrArg Subtype.val h,
    Or.inl hedge⟩

private theorem pair_ne :
    ∀ (s : List GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y := by
  classical
  intro s hs x y l₁ l₂ hdec hxy
  have hN : (l₁ ++ x :: y :: l₂).Nodup := by simpa [hdec] using hs
  have htail : (x :: y :: l₂).Nodup := (List.nodup_append.mp hN).2.1
  subst y
  exact (List.nodup_cons.mp htail).1 (by simp)

private theorem pEndpoint :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), (Disjoint Fplus Fminus) → (∀ (p :
        List GaussianInt), (p.Nodup) → ((Kplus = (↑p.toFinset : Set GaussianInt)) → ((∀ (e :
        Finset GaussianInt), e ∈ Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List
        GaussianInt), (q.Nodup) → (((2 : ℕ) ≤ q.length) → ((Kminus = (↑q.toFinset : Set
        GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
        (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1
        : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e :
        Finset GaussianInt), e ∈ Fminus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (s :
        List GaussianInt), s.Nodup → ∀ x, x ∈ s → s.head? ≠ some x → s.getLast? ≠ some x → ∃ l₁
        l₂ y z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ GEdges → G.Adj ⟨u, hu⟩ ⟨v, hv⟩) → ((∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), ∀
        (hw : w ∈ X), ∀ (hz : z ∈ X), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → G.Adj ⟨u,
        hu⟩ ⟨v, hv⟩ → G.Adj ⟨u, hu⟩ ⟨w, hw⟩ → G.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False) → ((∀ (s : List
        GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y) → (∀ x, x ∈
        Kplus → x ∈ Kminus → p.head? = some x ∨ p.getLast? = some x))))))))))))) := by
  classical
  intro Kplus Kminus Fplus Fminus hdisjoint p hpN hKp hpEdges q hqN hqLen hKm hqStep hqEdges
      splitInterior X GEdges G edgeAdj noThree pair_ne x hx₁ hx₂
  by_cases hh : p.head? = some x
  · exact Or.inl hh
  · by_cases hl : p.getLast? = some x
    · exact Or.inr hl
    · exact False.elim ((CycleArcProof.shared_no_interior_plus Kplus Kminus Fplus Fminus
        hdisjoint p hpN hKp hpEdges q hqN hqLen hKm hqStep hqEdges splitInterior edgeAdj noThree
        pair_ne) x hx₁ hx₂ hh hl)

private theorem qEndpoint :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (Fplus : Set (Finset
        GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)), (Disjoint Fplus Fminus) → (∀ (p :
        List GaussianInt), (p.Nodup) → (((2 : ℕ) ≤ p.length) → ((Kplus = (↑p.toFinset : Set
        GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀
        (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ → b = a + (1 : GaussianInt) ∨ b = a - (1
        : GaussianInt) ∨ b = a + ⟨(0 : ℤ), (1 : ℤ)⟩ ∨ b = a - ⟨(0 : ℤ), (1 : ℤ)⟩) → ((∀ (e :
        Finset GaussianInt), e ∈ Fplus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List
        GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀ (q : List
        GaussianInt), (q.Nodup) → ((Kminus = (↑q.toFinset : Set GaussianInt)) → ((∀ (e : Finset
        GaussianInt), e ∈ Fminus ↔ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt)
        (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (s : List
        GaussianInt), s.Nodup → ∀ x, x ∈ s → s.head? ≠ some x → s.getLast? ≠ some x → ∃ l₁ l₂ y
        z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
    (∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ GEdges → G.Adj ⟨u, hu⟩ ⟨v, hv⟩) → ((∀ (u : GaussianInt), ∀ (v :
        GaussianInt), ∀ (w : GaussianInt), ∀ (z : GaussianInt), ∀ (hu : u ∈ X), ∀ (hv : v ∈ X), ∀
        (hw : w ∈ X), ∀ (hz : z ∈ X), u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z → G.Adj ⟨u,
        hu⟩ ⟨v, hv⟩ → G.Adj ⟨u, hu⟩ ⟨w, hw⟩ → G.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False) → ((∀ (s : List
        GaussianInt), s.Nodup → ∀ x, ∀ y, ∀ l₁, ∀ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y) → (∀ x, x ∈
        Kplus → x ∈ Kminus → q.head? = some x ∨ q.getLast? = some x))))))))))))) := by
  classical
  intro Kplus Kminus Fplus Fminus hdisjoint p hpN hpLen hKp hpStep hpEdges q hqN hKm hqEdges
      splitInterior X GEdges G edgeAdj noThree pair_ne x hx₁ hx₂
  by_cases hh : q.head? = some x
  · exact Or.inl hh
  · by_cases hl : q.getLast? = some x
    · exact Or.inr hl
    · exact False.elim ((CycleArcProof.shared_no_interior_minus Kplus Kminus Fplus Fminus
        hdisjoint p hpN hpLen hKp hpStep hpEdges q hqN hKm hqEdges splitInterior edgeAdj noThree
        pair_ne) x hx₁ hx₂ hh hl)

private theorem fourNe :
    (List GaussianInt) → ((List GaussianInt) → ((List GaussianInt) → (∀ u, ∀ v,
        FourNeighborAdjacent u v → u ≠ v))) := by
  classical
  intro c p q u v huv huvEq
  subst v
  simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at huv
  omega

private theorem hcne :
    ∀ (c : List GaussianInt), ((4 : ℕ) ≤ c.length) → (c ≠ []) := by
  classical
  intro c hcLen hc
  simp [hc] at hcLen

private theorem hcxList :
    ∀ (c : List GaussianInt), ∀ (cx : GaussianInt), (c.head? = some cx) → ((c ≠ []) → (cx ∈ c))
        := by
  classical
  intro c cx hcHead hcne
  have hh := (List.head_eq_iff_head?_eq_some hcne).mpr hcHead
  simpa [hh] using List.head_mem hcne

private theorem hcyList :
    ∀ (c : List GaussianInt), ∀ (cy : GaussianInt), (c.getLast? = some cy) → ((c ≠ []) → (cy ∈
        c)) := by
  classical
  intro c cy hcLast hcne
  have hh := (List.getLast_eq_iff_getLast?_eq_some hcne).mpr hcLast
  simpa [hh] using List.getLast_mem hcne

private theorem hUV :
    ∀ (V : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), (∀ e, e ∈ E → ∀ x, x ∈ e → x ∈ V) → (
    let U : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    U ⊆ V) := by
  classical
  intro V E hEend U x hx
  rcases hx with ⟨e, he, hxe⟩
  exact hEend e he x hxe

private theorem hVfinite :
    ∀ (V : Set GaussianInt), ∀ (c : List GaussianInt), (V = (↑c.toFinset : Set GaussianInt)) →
        (V.Finite) := by
  classical
  intro V c hVcyc
  rw [hVcyc]
  exact Finset.finite_toSet c.toFinset

private theorem edgeAdjE :
    ∀ (E : Set (Finset GaussianInt)),
    let U : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    let C : SimpleGraph U := SimpleGraph.fromRel fun u v =>
      ({u.1, v.1} : Finset GaussianInt) ∈ E
    ∀ (u : GaussianInt), ∀ (v : GaussianInt), ∀ (hu : u ∈ U), ∀ (hv : v ∈ U), u ≠ v → ({u, v} :
        Finset GaussianInt) ∈ E → C.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  classical
  intro E U C u v hu hv huv hedge
  simp only [C, SimpleGraph.fromRel_adj]
  exact ⟨by intro h; apply huv; exact congrArg Subtype.val h,
    Or.inl hedge⟩

private theorem hXU :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
        ∀ (Fplus : Set (Finset GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)),
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    (GEdges ⊆ E) → ((X = {z | ∃ e ∈ GEdges, z ∈ e}) → (
    let U : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
    X ⊆ U)) := by
  classical
  intro Kplus Kminus E Fplus Fminus X GEdges hGE hSupport U x hx
  rw [hSupport] at hx
  rcases hx with ⟨e, he, hxe⟩
  exact ⟨e, hGE he, hxe⟩

private theorem edgeClosure :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)),
        ∀ (Fplus : Set (Finset GaussianInt)), ∀ (Fminus : Set (Finset GaussianInt)),
    let X : Set GaussianInt := Kplus ∪ Kminus
    let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
    (X = {z | ∃ e ∈ GEdges, z ∈ e}) → ((∀ x, x ∈ X → ∀ y, ({x, y} : Finset GaussianInt) ∈ E →
        ({x, y} : Finset GaussianInt) ∈ GEdges) → (∀ x, x ∈ X → ∀ y, ({x, y} : Finset
        GaussianInt) ∈ E → y ∈ X)) := by
  classical
  intro Kplus Kminus E Fplus Fminus X GEdges hSupport edgeCovered x hx y he
  rw [hSupport]
  exact ⟨{x, y}, edgeCovered x hx y he, by simp⟩

private theorem haCycle :
    ∀ (V : Set GaussianInt), ∀ (a : GaussianInt), ∀ (c : List GaussianInt), (V = (↑c.toFinset :
        Set GaussianInt)) → ((a ∈ V) → (a ∈ c)) := by
  classical
  intro V a c hVcyc haV
  rw [hVcyc] at haV
  simpa using haV

private theorem hcyLast :
    ∀ (a : GaussianInt), ∀ (c : List GaussianInt), ∀ (cy : GaussianInt), (c.getLast? = some cy) →
        (∀ (pre : List GaussianInt), ∀ (suf : List GaussianInt), (c = pre ++ a :: suf) → ((a ::
        suf).getLast? = some cy)) := by
  classical
  intro a c cy hcLast pre suf hcSplit
  have h := congrArg List.getLast? hcSplit
  simpa only [List.getLast?_append_of_ne_nil pre (by simp : (a :: suf) ≠ [])]
    using h.symm.trans hcLast

private theorem hcySuffix :
    ∀ (a : GaussianInt), ∀ (cy : GaussianInt), ∀ (suf : List GaussianInt), ((a :: suf).getLast? =
        some cy) → (cy ∈ a :: suf) := by
  classical
  intro a cy suf hcyLast
  rcases (List.getLast?_eq_some_iff).mp hcyLast with ⟨t, ht⟩
  rw [ht]
  simp

private theorem hcyX :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (a : GaussianInt), ∀ (c : List
        GaussianInt), ∀ (cy : GaussianInt),
    let X : Set GaussianInt := Kplus ∪ Kminus
    (∀ pre, ∀ x, ∀ s, c = pre ++ x :: s → x ∈ X → ∀ z, z ∈ s → z ∈ X) → (∀ (pre : List
        GaussianInt), ∀ (suf : List GaussianInt), (c = pre ++ a :: suf) → ((a ∈ X) → ((cy ∈ a ::
        suf) → (cy ∈ X)))) := by
  classical
  intro Kplus Kminus a c cy X allTail pre suf hcSplit haX hcySuffix
  rcases List.mem_cons.mp hcySuffix with hca | hcs
  · simpa [hca] using haX
  · exact allTail pre a suf hcSplit haX cy hcs

private theorem hcShape :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E :
        Set (Finset GaussianInt)), ∀ (a : GaussianInt), ∀ (c : List GaussianInt), ∀ (cx :
        GaussianInt), ∀ (cy : GaussianInt), (c.Nodup) → (((4 : ℕ) ≤ c.length) → ((c.head? = some
        cx) → ((c.getLast? = some cy) → ((V = (↑c.toFinset : Set GaussianInt)) → ((∀ (a :
        GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt),
        c = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) → ((∀ (e : Finset GaussianInt), e ∈ E
        ↔ e = {cy, cx} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List
        GaussianInt), c = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    (c ≠ []) → ((cx ∈ c) → ((cy ∈ c) → ((∀ pre, ∀ x, ∀ s, c = pre ++ x :: s → x ∈ X → ∀ z, z ∈ s
        → z ∈ X) → ((a ∈ c) → (∀ (pre : List GaussianInt), ∀ (suf : List GaussianInt), (c = pre
        ++ a :: suf) → (c = cx :: c.tail))))))))))))) := by
  classical
  intro V Kplus Kminus E a c cx cy hcN hcLen hcHead hcLast hVcyc hcStep hcEdges X hcne hcxList
      hcyList allTail haCycle pre suf hcSplit
  cases c with
  | nil => simp at hcLen
  | cons z zs =>
      have hzx : z = cx := by simpa using hcHead
      subst z
      rfl

private theorem hallC :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (c : List GaussianInt), ∀ (cx :
        GaussianInt),
    let X : Set GaussianInt := Kplus ∪ Kminus
    (∀ pre, ∀ x, ∀ s, c = pre ++ x :: s → x ∈ X → ∀ z, z ∈ s → z ∈ X) → ((cx ∈ X) → ((c = cx ::
        c.tail) → (∀ z, z ∈ c → z ∈ X))) := by
  classical
  intro Kplus Kminus c cx X allTail hcxX hcShape z hz
  rw [hcShape] at hz
  rcases List.mem_cons.mp hz with hzc | hzt
  · simpa [hzc] using hcxX
  · exact allTail [] cx c.tail hcShape hcxX z hzt

private theorem hVtoX :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (c :
        List GaussianInt), (V = (↑c.toFinset : Set GaussianInt)) → (
    let X : Set GaussianInt := Kplus ∪ Kminus
    (∀ z, z ∈ c → z ∈ X) → (V ⊆ X)) := by
  classical
  intro V Kplus Kminus c hVcyc X hallC z hz
  rw [hVcyc] at hz
  exact hallC z (by simpa using hz)

private theorem hp'Nodup :
    ∀ (a : GaussianInt), ∀ (p : List GaussianInt), (p.Nodup) → (
    let p' : List GaussianInt := if p.head? = some a then p else p.reverse
    p'.Nodup) := by
  classical
  intro a p hpN p'
  dsimp [p']
  split_ifs <;> simp [hpN]

private theorem hq'Nodup :
    ∀ (r : GaussianInt → GaussianInt), ∀ (a : GaussianInt), ∀ (q : List GaussianInt), (q.Nodup) → (
    let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
    q'.Nodup) := by
  classical
  intro r a q hqN q'
  dsimp [q']
  split_ifs <;> simp [hqN]

private theorem hp'Set :
    ∀ (Kplus : Set GaussianInt), ∀ (a : GaussianInt), ∀ (p : List GaussianInt), (Kplus =
        (↑p.toFinset : Set GaussianInt)) → (
    let p' : List GaussianInt := if p.head? = some a then p else p.reverse
    (p'.toFinset : Set GaussianInt) = Kplus) := by
  classical
  intro Kplus a p hKp p'
  dsimp [p']
  split_ifs
  · exact hKp.symm
  · simpa [List.toFinset_reverse] using hKp.symm

private theorem hq'Set :
    ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt), ∀ (a : GaussianInt), ∀ (q :
        List GaussianInt), (Kminus = (↑q.toFinset : Set GaussianInt)) → (
    let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
    (q'.toFinset : Set GaussianInt) = Kminus) := by
  classical
  intro Kminus r a q hKm q'
  dsimp [q']
  split_ifs
  · exact hKm.symm
  · simpa [List.toFinset_reverse] using hKm.symm

private theorem hVlists :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r :
        GaussianInt → GaussianInt), ∀ (a : GaussianInt), ∀ (p : List GaussianInt), ∀ (q : List
        GaussianInt), (V = Kplus ∪ Kminus) → (
    let p' : List GaussianInt := if p.head? = some a then p else p.reverse
    let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
    ((p'.toFinset : Set GaussianInt) = Kplus) → (((q'.toFinset : Set GaussianInt) = Kminus) → (V
        = (p'.toFinset : Set GaussianInt) ∪ (q'.toFinset : Set GaussianInt)))) := by
  classical
  intro V Kplus Kminus r a p q hVparts p' q' hp'Set hq'Set
  rw [hp'Set, hq'Set]
  exact hVparts

private theorem hIntersectionLists :
    ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (r : GaussianInt → GaussianInt),
        ∀ (a : GaussianInt), (a ∈ Kplus ∩ Kminus) → (∀ (p : List GaussianInt), ∀ (q : List
        GaussianInt), (r a ∈ Kminus) → ((r a ∈ Kplus) → ((∀ x, x ∈ Kplus → x ∈ Kminus → p.head? =
        some x ∨ p.getLast? = some x) → (((p.head? = some a ∧ p.getLast? = some (r a)) ∨ (p.head?
        = some (r a) ∧ p.getLast? = some a)) → (
    let p' : List GaussianInt := if p.head? = some a then p else p.reverse
    let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
    ((p'.toFinset : Set GaussianInt) = Kplus) → (((q'.toFinset : Set GaussianInt) = Kminus) →
        ((p'.toFinset : Set GaussianInt) ∩ (q'.toFinset : Set GaussianInt) = {a, r a}))))))) := by
  classical
  intro Kplus Kminus r a ha p q hara harp pEndpoint pOrientation p' q' hp'Set hq'Set
  rw [hp'Set, hq'Set]
  exact (CycleArcProof.hIntersection Kplus Kminus r a ha p hara harp pEndpoint pOrientation)

end CycleArcDetails

theorem P4651T1CycleComplementaryArcs :
    ∀ (V : Set GaussianInt), ∀ (Kplus : Set GaussianInt), ∀ (Kminus : Set GaussianInt), ∀ (E :
        Set (Finset GaussianInt)), ∀ (Fplus : Set (Finset GaussianInt)), ∀ (Fminus : Set (Finset
        GaussianInt)), ∀ (r : GaussianInt → GaussianInt), ∀ (a : GaussianInt), (SimpleGridCycle V
        E) → ((SimpleGridPath Kplus Fplus) → ((SimpleGridPath Kminus Fminus) → ((Kplus ⊆ V) →
        ((Kminus ⊆ V) → ((Fplus ⊆ E) → ((Fminus ⊆ E) → ((Function.Involutive r) → ((r '' V = V) →
        (((fun e : Finset GaussianInt => e.image r) '' E = E) → ((∀ z ∈ V, r z ≠ z) → ((∀ e ∈ E,
        e.image r ≠ e) → ((r '' Kplus = Kminus) → ((Disjoint Fplus Fminus) → ((a ∈ Kplus ∩
        Kminus) → ((∃ p q : List GaussianInt,
      p.Nodup ∧ q.Nodup ∧
      p.head? = some a ∧ p.getLast? = some (r a) ∧
      q.head? = some (r a) ∧ q.getLast? = some a ∧
      (p.toFinset : Set GaussianInt) = Kplus ∧
      (q.toFinset : Set GaussianInt) = Kminus ∧
      (∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        p = l1 ++ x :: y :: l2 → {x, y} ∈ Fplus) ∧
      (∀ x y : GaussianInt, ∀ l1 l2 : List GaussianInt,
        q = l1 ++ x :: y :: l2 → {x, y} ∈ Fminus) ∧
      V = (p.toFinset : Set GaussianInt) ∪ (q.toFinset : Set GaussianInt) ∧
      (p.toFinset : Set GaussianInt) ∩ (q.toFinset : Set GaussianInt) =
        {a, r a}) ∧
    ∀ e ∈ E, e ∈ Fplus ∨ e ∈ Fminus))))))))))))))) := by
  intro V Kplus Kminus E Fplus Fminus r a hcycle hp hm hpV hmV hpE hmE hinv hV hE hfreeV hfreeE
      hcontact hdisjoint ha
-- BODY
  classical
  rcases hcycle with ⟨c, cx, cy, hcN, hcLen, hcHead, hcLast, hVcyc,
    hclose, hcStep, hcEdges⟩
  rcases hp with ⟨p, hpN, hpLen, hKp, hpStep, hpEdges⟩
  rcases hm with ⟨q, hqN, hqLen, hKm, hqStep, hqEdges⟩
  have hara : r a ∈ Kminus := CycleArcDetails.hara Kplus Kminus r a hcontact ha
  have harp : r a ∈ Kplus := CycleArcDetails.harp Kplus Kminus r a hinv hcontact ha
  have hdistinct : a ≠ r a := CycleArcDetails.hdistinct V Kplus Kminus r a hpV hfreeV ha
  have splitInterior : ∀ (s : List GaussianInt), s.Nodup →
      ∀ x, x ∈ s → s.head? ≠ some x → s.getLast? ≠ some x →
        ∃ l₁ l₂ y z, s = l₁ ++ y :: x :: z :: l₂ ∧ y ≠ z := CycleArcProof.splitInterior
  let X : Set GaussianInt := Kplus ∪ Kminus
  let GEdges : Set (Finset GaussianInt) := Fplus ∪ Fminus
  have hXV : X ⊆ V := CycleArcDetails.hXV V Kplus Kminus hpV hmV
  have hGE : GEdges ⊆ E := CycleArcDetails.hGE E Fplus Fminus hpE hmE
  have hSupport : X = {z | ∃ e ∈ GEdges, z ∈ e} := CycleArcProof.hSupport Kplus Kminus Fplus
      Fminus p hpN hpLen hKp hpStep hpEdges q hqN hqLen hKm hqStep hqEdges
  have hXfinite : X.Finite := CycleArcDetails.hXfinite Kplus Kminus p hKp q hKm
  let : Finite X := hXfinite.to_subtype
  have hdeg := SimpleGridCycleSubgraphDegreeTwo X V GEdges E
    ⟨c, cx, cy, hcN, hcLen, hcHead, hcLast, hVcyc, hclose, hcStep, hcEdges⟩
    hXV hGE
  let G : SimpleGraph X := SimpleGraph.fromRel fun u v =>
    ({u.1, v.1} : Finset GaussianInt) ∈ GEdges
  have hdeg' : ∀ v : X, Set.ncard (G.neighborSet v) ≤ 2 := by
    simpa [G, X, GEdges] using hdeg
  have edgeAdj : ∀ (u v : GaussianInt) (hu : u ∈ X) (hv : v ∈ X),
      u ≠ v → ({u, v} : Finset GaussianInt) ∈ GEdges →
        G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := CycleArcDetails.edgeAdj Kplus Kminus Fplus Fminus
  have noThree : ∀ (u v w z : GaussianInt)
      (hu : u ∈ X) (hv : v ∈ X) (hw : w ∈ X) (hz : z ∈ X),
      u ≠ v → u ≠ w → u ≠ z → v ≠ w → v ≠ z → w ≠ z →
      G.Adj ⟨u, hu⟩ ⟨v, hv⟩ → G.Adj ⟨u, hu⟩ ⟨w, hw⟩ →
      G.Adj ⟨u, hu⟩ ⟨z, hz⟩ → False := CycleArcProof.noThree Kplus Kminus Fplus Fminus c p q
           hdeg'
  have pair_ne : ∀ (s : List GaussianInt), s.Nodup →
      ∀ x y l₁ l₂, s = l₁ ++ x :: y :: l₂ → x ≠ y := CycleArcDetails.pair_ne
  have pEndpoint : ∀ x, x ∈ Kplus → x ∈ Kminus →
      p.head? = some x ∨ p.getLast? = some x := CycleArcDetails.pEndpoint Kplus Kminus Fplus
          Fminus hdisjoint p hpN hKp hpEdges q hqN hqLen hKm hqStep hqEdges splitInterior edgeAdj
          noThree pair_ne
  have qEndpoint : ∀ x, x ∈ Kplus → x ∈ Kminus →
      q.head? = some x ∨ q.getLast? = some x := CycleArcDetails.qEndpoint Kplus Kminus Fplus
          Fminus hdisjoint p hpN hpLen hKp hpStep hpEdges q hqN hKm hqEdges splitInterior edgeAdj
          noThree pair_ne
  have pOrientation :
      (p.head? = some a ∧ p.getLast? = some (r a)) ∨
      (p.head? = some (r a) ∧ p.getLast? = some a) := CycleArcProof.pOrientation Kplus Kminus r a
          ha p hara harp hdistinct pEndpoint
  have qOrientation :
      (q.head? = some (r a) ∧ q.getLast? = some a) ∨
      (q.head? = some a ∧ q.getLast? = some (r a)) := CycleArcProof.qOrientation Kplus Kminus r a
          ha q hara harp hdistinct qEndpoint
  have fourNe : ∀ u v, FourNeighborAdjacent u v → u ≠ v := CycleArcDetails.fourNe c p q
  have hcne : c ≠ [] := CycleArcDetails.hcne c hcLen
  have hcxList : cx ∈ c := CycleArcDetails.hcxList c cx hcHead hcne
  have hcyList : cy ∈ c := CycleArcDetails.hcyList c cy hcLast hcne
  have hcxV : cx ∈ V := by rw [hVcyc]; simpa using hcxList
  have hcyV : cy ∈ V := by rw [hVcyc]; simpa using hcyList
  have hEend : ∀ e, e ∈ E → ∀ x, x ∈ e → x ∈ V := CycleArcProof.hEend V E c cx cy hVcyc hcEdges
      hcxV hcyV
  let U : Set GaussianInt := {x | ∃ e ∈ E, x ∈ e}
  have hUV : U ⊆ V := CycleArcDetails.hUV V E hEend
  have hVfinite : V.Finite := CycleArcDetails.hVfinite V c hVcyc
  have hUfinite : U.Finite := hVfinite.subset hUV
  let : Finite U := hUfinite.to_subtype
  have hdegE := SimpleGridCycleSubgraphDegreeTwo U V E E
    ⟨c, cx, cy, hcN, hcLen, hcHead, hcLast, hVcyc, hclose, hcStep, hcEdges⟩
    hUV (Set.Subset.rfl)
  let C : SimpleGraph U := SimpleGraph.fromRel fun u v =>
    ({u.1, v.1} : Finset GaussianInt) ∈ E
  have hdegE' : ∀ v : U, Set.ncard (C.neighborSet v) ≤ 2 := by
    simpa [C, U] using hdegE
  have edgeAdjE : ∀ (u v : GaussianInt) (hu : u ∈ U) (hv : v ∈ U),
      u ≠ v → ({u, v} : Finset GaussianInt) ∈ E →
        C.Adj ⟨u, hu⟩ ⟨v, hv⟩ := CycleArcDetails.edgeAdjE E
  have hXU : X ⊆ U := CycleArcDetails.hXU Kplus Kminus E Fplus Fminus hGE hSupport
  have edgeCovered : ∀ x, x ∈ X → ∀ y,
      ({x, y} : Finset GaussianInt) ∈ E →
        ({x, y} : Finset GaussianInt) ∈ GEdges := CycleArcProof.edgeCovered Kplus Kminus E Fplus
            Fminus hGE hSupport (CycleArcProof.twoNeighbors Kplus Kminus Fplus Fminus r a
                hdisjoint ha p hpN hpLen hKp hpStep hpEdges q hqN hqLen hKm hqStep hqEdges hara
                harp splitInterior pair_ne (CycleArcProof.path_other pair_ne) pOrientation
                qOrientation) (CycleArcProof.hEne E c cx cy hclose hcStep hcEdges p q fourNe)
                edgeAdjE (CycleArcProof.noThreeE E c p q hdegE') hXU
  have edgeClosure : ∀ x, x ∈ X → ∀ y,
      ({x, y} : Finset GaussianInt) ∈ E → y ∈ X := CycleArcDetails.edgeClosure Kplus Kminus E
          Fplus Fminus hSupport edgeCovered
  have allTail : ∀ pre x s, c = pre ++ x :: s → x ∈ X →
      ∀ z, z ∈ s → z ∈ X := CycleArcProof.allTail Kplus Kminus E c cx cy hcEdges edgeClosure
  have haV : a ∈ V := hpV ha.1
  have haCycle : a ∈ c := CycleArcDetails.haCycle V a c hVcyc haV
  obtain ⟨pre, suf, hcSplit⟩ := (CycleArcProof.splitAt) c a haCycle
  have haX : a ∈ X := Set.mem_union_left _ ha.1
  have hcyLast : (a :: suf).getLast? = some cy := CycleArcDetails.hcyLast a c cy hcLast pre suf
      hcSplit
  have hcySuffix : cy ∈ a :: suf := CycleArcDetails.hcySuffix a cy suf hcyLast
  have hcyX : cy ∈ X := CycleArcDetails.hcyX Kplus Kminus a c cy allTail pre suf hcSplit haX
      hcySuffix
  have hcloseE : ({cy, cx} : Finset GaussianInt) ∈ E :=
    (hcEdges {cy, cx}).2 (Or.inl rfl)
  have hcxX := edgeClosure cy hcyX cx hcloseE
  have hcShape : c = cx :: c.tail := CycleArcDetails.hcShape V Kplus Kminus E a c cx cy hcN hcLen
      hcHead hcLast hVcyc hcStep hcEdges hcne hcxList hcyList allTail haCycle pre suf hcSplit
  have hallC : ∀ z, z ∈ c → z ∈ X := CycleArcDetails.hallC Kplus Kminus c cx allTail hcxX hcShape
  have hVtoX : V ⊆ X := CycleArcDetails.hVtoX V Kplus Kminus c hVcyc hallC
  have hVparts : V = Kplus ∪ Kminus := by
    exact Set.Subset.antisymm hVtoX hXV
  let p' : List GaussianInt := if p.head? = some a then p else p.reverse
  let q' : List GaussianInt := if q.head? = some (r a) then q else q.reverse
  have hp'Orient : p'.head? = some a ∧ p'.getLast? = some (r a) := CycleArcProof.hp'Orient r a p
      hdistinct pOrientation
  have hq'Orient : q'.head? = some (r a) ∧ q'.getLast? = some a := CycleArcProof.hq'Orient r a q
      hdistinct qOrientation
  have hp'Nodup : p'.Nodup := CycleArcDetails.hp'Nodup a p hpN
  have hq'Nodup : q'.Nodup := CycleArcDetails.hq'Nodup r a q hqN
  have hp'Set : (p'.toFinset : Set GaussianInt) = Kplus := CycleArcDetails.hp'Set Kplus a p hKp
  have hq'Set : (q'.toFinset : Set GaussianInt) = Kminus := CycleArcDetails.hq'Set Kminus r a q hKm
  have hVlists : V = (p'.toFinset : Set GaussianInt) ∪
      (q'.toFinset : Set GaussianInt) := CycleArcDetails.hVlists V Kplus Kminus r a p q hVparts
          hp'Set hq'Set
  have hIntersectionLists :
      (p'.toFinset : Set GaussianInt) ∩ (q'.toFinset : Set GaussianInt) =
        {a, r a} := CycleArcDetails.hIntersectionLists Kplus Kminus r a ha p q hara harp
            pEndpoint pOrientation hp'Set hq'Set
  refine ⟨⟨p', q', hp'Nodup, hq'Nodup, hp'Orient.1, hp'Orient.2,
    hq'Orient.1, hq'Orient.2, hp'Set, hq'Set, (CycleArcProof.hp'Edges Fplus a p hpEdges),
    (CycleArcProof.hq'Edges Fminus r a q hqEdges), hVlists, hIntersectionLists⟩,
        (CycleArcProof.hEdgeCoverage V Kplus Kminus E Fplus Fminus c cx cy hcEdges hEend
        (CycleArcProof.cycleOther E c cx cy hclose hcStep hcEdges fourNe) edgeCovered hVtoX)⟩

end ApollonianSuperharmonic

end
