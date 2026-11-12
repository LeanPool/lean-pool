/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.RootedFourNeighborForest
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

-- [TABLET NODE: P4250T2FiniteForestCompletion]

/-!
# P4250T2FiniteForestCompletion

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ForestCompletionLemmas

private theorem noGridTriangle :
    (Finset GaussianInt) → (Finset GaussianInt) → ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z
        : GaussianInt), (FourNeighborAdjacent x y) → (FourNeighborAdjacent y z) →
        (FourNeighborAdjacent z x) → False := by
  classical
  intro W R x y z hxy hyz hzx
  simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hxy hyz hzx
  omega

private theorem adjacentSymm :
    ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b
        a := by
  classical
  intro a b h
  rcases h with h | h | h | h <;> subst b
  all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem hHacyclic :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → (∀ V E, SimpleGridCycle V E → ¬ V ⊆ (W :
        Set GaussianInt)) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (z : GaussianInt),
            (FourNeighborAdjacent x y) → (FourNeighborAdjacent y z) → (FourNeighborAdjacent z x) →
        False) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀ {b : GaussianInt},
            (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    H.IsAcyclic := by
  classical
  intro W R hcycle noGridTriangle adjacentSymm H a c hc
  have walkW {u v : GaussianInt} (p : H.Walk u v) (hu : u ∈ W) :
      ∀ z ∈ p.support, z ∈ W := by
    intro z hz
    induction p with
    | nil =>
      simp only [SimpleGraph.Walk.support, List.mem_cons, List.not_mem_nil, or_false] at hz
      subst z
      exact hu
    | @cons u v w hadj p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · subst z
        exact hadj.2.1
      · exact ih hadj.2.2 hz
  cases c with
  | nil => simp at hc
  | @cons u v w hadj p =>
    have hp3 : 3 ≤ p.length + 1 := by
      simpa using (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mp hc).2
    have hp2 : 2 ≤ p.length := by omega
    have hlen : p.length ≠ 2 := by
      intro heq
      have h₁ : H.Adj v (p.getVert 1) := by
        simpa using p.adj_getVert_succ (i := 0) (by omega)
      have hend : p.getVert 2 = a := by
        simpa [heq] using p.getVert_length
      have h₂ : H.Adj (p.getVert 1) a := by
        simpa [hend] using p.adj_getVert_succ (i := 1) (by omega)
      exact noGridTriangle v (p.getVert 1) a h₁.1 h₂.1 hadj.1
    have hp4 : 3 ≤ p.length := by omega
    let l : List GaussianInt := p.support
    let E : Set (Finset GaussianInt) := {e | e = {a, v} ∨
      ∃ x y l₁ l₂, l = l₁ ++ x :: y :: l₂ ∧ e = {x, y}}
    have hsteps {x y : GaussianInt} {l₁ l₂ : List GaussianInt}
        (heq : p.support = l₁ ++ x :: y :: l₂) : H.Adj x y := by
      have supportAdj : ∀ {s t : GaussianInt} (q : H.Walk s t)
          {l₁ l₂ : List GaussianInt} {x y : GaussianInt},
          q.support = l₁ ++ x :: y :: l₂ → H.Adj x y := by
        intro s t q
        induction q with
        | nil =>
          intro l₁ l₂ x y heq
          have hlen := congrArg List.length heq
          simp [SimpleGraph.Walk.support] at hlen
          omega
        | @cons s t r hadj q ih =>
          intro l₁ l₂ x y heq
          cases l₁ with
          | nil =>
            simp only [List.nil_append, SimpleGraph.Walk.support_cons, List.cons.injEq] at heq
            rcases heq with ⟨rfl, htail⟩
            have hby : y = t := by
              calc
                y = q.support.head (by simp) := by simp [htail]
                _ = t := by simp
            subst y
            exact hadj
          | cons z zs =>
            simp only [List.cons_append, SimpleGraph.Walk.support_cons, List.cons.injEq] at heq
            rcases heq with ⟨rfl, htail⟩
            exact ih htail
      exact supportAdj p heq
    have hL : l.Nodup := by
      simpa [l] using
        (SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mp hc).1.support_nodup
    have hheads : l.head? = some v := by
      simp [l, List.head?_eq_some_head, SimpleGraph.Walk.head_support]
    have hlast : l.getLast? = some a := by
      simp [l, List.getLast?_eq_some_getLast, SimpleGraph.Walk.getLast_support]
    have hverts : (l.toFinset : Set GaussianInt) ⊆ W := by
      intro z hz
      exact walkW p hadj.2.2 z (List.mem_toFinset.mp hz)
    exact hcycle (l.toFinset : Set GaussianInt) E
      (by
        refine ⟨l, v, a, hL, ?_, hheads, hlast, rfl, hadj.1, ?_, ?_⟩
        · simpa [l] using hp4
        · intro x y l₁ l₂ heq
          exact (hsteps heq).1
        · intro e
          rfl)
      hverts

private theorem finj :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    let f : G →g H := {
      toFun := Subtype.val
      map_rel' := by
        intro x y h
        exact ⟨h, x.2, y.2⟩
    }
    Function.Injective f := by
  classical
  intro W R adjacentSymm H X G f x y h
  exact Subtype.ext h

private theorem hGacyclic :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    (H.IsAcyclic) →
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    let f : G →g H := {
      toFun := Subtype.val
      map_rel' := by
        intro x y h
        exact ⟨h, x.2, y.2⟩
    }
    (Function.Injective f) → G.IsAcyclic := by
  classical
  intro W R adjacentSymm H hHacyclic X G f finj x c hc
  exact hHacyclic (c.map f) (hc.map finj)

private theorem hPQ :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    letI : DecidableRel FourNeighborAdjacent := fun _ _ => Classical.propDecidable _
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    let P := (W.product W).filter fun e => FourNeighborAdjacent e.1 e.2
    let Q := Finset.univ.filter fun e : X × X => G.Adj e.1 e.2
    P.card = Q.card := by
  classical
  intro W R adjacentSymm X G P Q
  refine Finset.card_bij' (s := P) (t := Q)
    (fun e he => (⟨e.1, (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1⟩,
      ⟨e.2, (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2⟩))
    (fun q hq => (q.1.1, q.2.1)) ?_ ?_ ?_ ?_
  · intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [G] using he'.2⟩
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨q.1.2, q.2.2⟩, by simpa [G] using hq'.2⟩
  · intro e he
    rfl
  · intro q hq
    apply Prod.ext <;> apply Subtype.ext <;> rfl

private theorem hordered :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    letI : DecidableRel FourNeighborAdjacent := fun _ _ => Classical.propDecidable _
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    let P := (W.product W).filter fun e => FourNeighborAdjacent e.1 e.2
    let Q := Finset.univ.filter fun e : X × X => G.Adj e.1 e.2
    (P.card = Q.card) → P.card = 2 * G.edgeFinset.card := by
  classical
  intro W R adjacentSymm X G P Q hPQ
  calc
    _ = Q.card := hPQ
    _ = 2 * G.edgeFinset.card := by simpa [Q] using G.two_mul_card_edgeFinset.symm

private theorem hdiv :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    letI : DecidableRel FourNeighborAdjacent := fun _ _ => Classical.propDecidable _
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    let P := (W.product W).filter fun e => FourNeighborAdjacent e.1 e.2
    (P.card = 2 * G.edgeFinset.card) → P.card / 2 = G.edgeFinset.card := by
  classical
  intro W R adjacentSymm X G P hordered
  rw [hordered]
  simp

private theorem hcountGraph :
    ∀ (W : Finset GaussianInt), ∀ (R : Finset GaussianInt), ((∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ)
        else 0)) = ((((W.product W).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ)) → ∀ (adjacentSymm : ∀ {a : GaussianInt},
            ∀ {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    letI : DecidableRel FourNeighborAdjacent := fun _ _ => Classical.propDecidable _
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    let P := (W.product W).filter fun e => FourNeighborAdjacent e.1 e.2
    (P.card / 2 = G.edgeFinset.card) → (∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) =
      (G.edgeFinset.card : ℤ) := by
  classical
  intro W R hcount adjacentSymm X G P hdiv
  calc
    _ = (↑(P.card / 2) : ℤ) := by
      simpa [P, decide_eq_true_eq] using hcount
    _ = ↑G.edgeFinset.card := by rw [hdiv]

private theorem supportAdj :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    ∀ {s : GaussianInt}, ∀ {t : GaussianInt}, ∀ (q : H.Walk s t), ∀ {l₁ : List GaussianInt}, ∀
        {l₂ : List GaussianInt}, ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, q.support = l₁ ++ x ::
        y :: l₂ → H.Adj x y := by
  classical
  intro W R adjacentSymm H s t q
  induction q with
  | nil =>
    intro l₁ l₂ x y heq
    have hlen := congrArg List.length heq
    simp [SimpleGraph.Walk.support] at hlen
    omega
  | @cons s t r hadj q ih =>
    intro l₁ l₂ x y heq
    cases l₁ with
    | nil =>
      simp only [List.nil_append, SimpleGraph.Walk.support_cons,
        List.cons.injEq] at heq
      rcases heq with ⟨rfl, htail⟩
      have hby : y = t := by
        calc
          y = q.support.head (by simp) := by simp [htail]
          _ = t := by simp
      subst y
      exact hadj
    | cons z zs =>
      simp only [List.cons_append, SimpleGraph.Walk.support_cons,
        List.cons.injEq] at heq
      rcases heq with ⟨rfl, htail⟩
      exact ih htail

private theorem allWalkW :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    ∀ {u : GaussianInt}, ∀ {v : GaussianInt}, ∀ (q : H.Walk u v), (u ∈ W) → ∀ z ∈ q.support, z ∈
        W := by
  classical
  intro W R adjacentSymm H u v q hu z hz
  induction q with
  | nil =>
    simp only [SimpleGraph.Walk.support, List.mem_cons, List.not_mem_nil, or_false] at hz
    subst z
    exact hu
  | @cons u v w hadj q ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with hz | hz
    · subst z
      exact hadj.2.1
    · exact ih hadj.2.2 hz

private theorem pathToGrid :
    ∀ (W : Finset GaussianInt), (Finset GaussianInt) → ∀ (adjacentSymm : ∀ {a : GaussianInt}, ∀
        {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    (∀ {s : GaussianInt}, ∀ {t : GaussianInt}, ∀ (q : H.Walk s t), ∀ {l₁ : List GaussianInt}, ∀
        {l₂ : List GaussianInt}, ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, q.support = l₁ ++ x ::
        y :: l₂ → H.Adj x y) → (∀ {u : GaussianInt}, ∀ {v : GaussianInt}, ∀ (q : H.Walk u v), (u
        ∈ W) → ∀ z ∈ q.support, z ∈ W) → ∀ {s : GaussianInt}, ∀ {t : GaussianInt}, ∀ (p : H.Walk
        s t), (p.IsPath) → (s ≠ t) → (s ∈ W) → (t ∈ W) → ∃ V E, SimpleGridPathBetween V E s t ∧ V
        ⊆ (W : Set GaussianInt) := by
  classical
  intro W R adjacentSymm H supportAdj allWalkW s t p hp hne hs ht
  let l : List GaussianInt := p.support
  let E : Set (Finset GaussianInt) := {e | ∃ x y l₁ l₂,
    l = l₁ ++ x :: y :: l₂ ∧ e = {x, y}}
  have hlen : 2 ≤ l.length := by
    have hne : 0 < p.length := by
      by_contra hnot
      have hz : p.length = 0 := Nat.eq_zero_of_not_pos hnot
      have hst : s = t := by
        calc
          s = p.getVert 0 := by rw [SimpleGraph.Walk.getVert_zero]
          _ = t := by simpa [hz] using p.getVert_length
      exact hne hst
    simpa [l, SimpleGraph.Walk.length_support] using Nat.add_le_add_right hne 1
  have hnodup : l.Nodup := by simpa [l] using hp.support_nodup
  have hhead : l.head? = some s := by
    simp [l, List.head?_eq_some_head, SimpleGraph.Walk.head_support]
  have hlast : l.getLast? = some t := by
    simp [l, List.getLast?_eq_some_getLast, SimpleGraph.Walk.getLast_support]
  have hV : (l.toFinset : Set GaussianInt) ⊆ (W : Set GaussianInt) := by
    intro z hz
    exact allWalkW p hs z (List.mem_toFinset.mp hz)
  refine ⟨l.toFinset, E, ?_, hV⟩
  refine ⟨l, hnodup, hlen, hhead, hlast, rfl, ?_, ?_⟩
  · intro x y l₁ l₂ heq
    exact (supportAdj p heq).1
  · intro e
    rfl

private theorem hrootSeparateGraph :
    ∀ (W : Finset GaussianInt), ∀ (R : Finset GaussianInt), (∀ a ∈ R, ∀ b ∈ R, ∀ V E,
        SimpleGridPathBetween V E a b → V ⊆ (W : Set GaussianInt) → a = b) → ∀ (adjacentSymm : ∀
            {a : GaussianInt}, ∀ {b : GaussianInt}, (FourNeighborAdjacent a b) →
            FourNeighborAdjacent
        b a),
    let H : SimpleGraph GaussianInt := {
      Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
      symm := ⟨by
        intro x y h
        exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
      loopless := ⟨by
        intro x h
        rcases h.1 with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    let f : G →g H := {
      toFun := Subtype.val
      map_rel' := by
        intro x y h
        exact ⟨h, x.2, y.2⟩
    }
    (Function.Injective f) → (∀ {s : GaussianInt}, ∀ {t : GaussianInt}, ∀ (p : H.Walk s t),
        (p.IsPath) → (s ≠ t) → (s ∈ W) → (t ∈ W) → ∃ V E, SimpleGridPathBetween V E s t ∧ V ⊆ (W
        : Set GaussianInt)) → ∀ x : X, x.1 ∈ R → ∀ y : X, y.1 ∈ R →
      G.Reachable x y → x.1 = y.1 := by
  classical
  intro W R hseparate adjacentSymm H X G f finj pathToGrid x hx y hy hxy
  by_cases heq : x.1 = y.1
  · exact heq
  · obtain ⟨p, hp, hlen⟩ := hxy.exists_path_of_dist
    let q := p.map f
    have hqpath : q.IsPath := SimpleGraph.Walk.IsPath.map finj hp
    obtain ⟨V, E, hgrid, hV⟩ := pathToGrid q hqpath heq x.2 y.2
    exact (heq (hseparate x.1 hx y.1 hy V E hgrid hV)).elim

private theorem forestCount :
    (Finset GaussianInt) → (Finset GaussianInt) → (∀ {a : GaussianInt}, ∀ {b : GaussianInt},
        (FourNeighborAdjacent a b) → FourNeighborAdjacent b a) → ∀ {V : Type}, ∀ [Fintype V], ∀
        (G : SimpleGraph V), ∀ [DecidableRel G.Adj], (G.IsAcyclic) → G.edgeFinset.card + Nat.card
        G.ConnectedComponent = Fintype.card V := by
  classical
  intro W R adjacentSymm V finiteType G adjacencyDecidability hG
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hdegree (c : G.ConnectedComponent) (v : c) :
      c.toSimpleGraph.degree v = G.degree v.val := by
    calc
      _ = (G.induce c.supp).degree v := by
        rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
        exact Fintype.card_congr (Equiv.refl ↑(c.toSimpleGraph.neighborSet v))
      _ = _ := G.degree_induce_of_neighborSet_subset (s := c.supp) (v := v)
        (fun w hw => c.mem_supp_of_adj_mem_supp v.property hw)
  have hvertices : (∑ c : G.ConnectedComponent, Fintype.card c) = Fintype.card V := by
    change (∑ c : G.ConnectedComponent, Fintype.card {v // G.connectedComponentMk v = c}) = _
    simpa using Fintype.sum_fiberwise G.connectedComponentMk (fun _ => (1 : ℕ))
  have hdegrees : (∑ c : G.ConnectedComponent, ∑ v : c, c.toSimpleGraph.degree v) =
      ∑ v : V, G.degree v := by
    simp_rw [hdegree]
    exact Fintype.sum_fiberwise G.connectedComponentMk (fun v => G.degree v)
  have hedges : (∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeFinset.card) =
      G.edgeFinset.card := by
    have ht : 2 * (∑ c : G.ConnectedComponent, c.toSimpleGraph.edgeFinset.card) =
        2 * G.edgeFinset.card := by
      rw [Finset.mul_sum]
      simp_rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
      exact hdegrees
    omega
  have hsum : (∑ c : G.ConnectedComponent, (c.toSimpleGraph.edgeFinset.card + 1)) =
      ∑ c : G.ConnectedComponent, Fintype.card c := by
    apply Finset.sum_congr rfl
    intro c hc
    exact (hG.isTree_connectedComponent c).card_edgeFinset
  rw [Finset.sum_add_distrib, hedges, hvertices] at hsum
  simpa [Nat.card_eq_fintype_card] using hsum

private theorem forestRooted :
    (Finset GaussianInt) → (Finset GaussianInt) → (∀ {a : GaussianInt}, ∀ {b : GaussianInt},
        (FourNeighborAdjacent a b) → FourNeighborAdjacent b a) → (∀ {V : Type}, ∀ [Fintype V], ∀
        (G : SimpleGraph V), ∀ [DecidableRel G.Adj], (G.IsAcyclic) → G.edgeFinset.card + Nat.card
        G.ConnectedComponent = Fintype.card V) → ∀ {V : Type}, ∀ [Fintype V], ∀ (G : SimpleGraph
            V), ∀ [DecidableRel G.Adj], (G.IsAcyclic) → ∀ (S : Set V), (∀ x ∈ S, ∀ y ∈ S,
            G.Reachable x y → x = y) → (G.edgeFinset.card + Nat.card S = Fintype.card V) → ∃
            parent : V → V, ∃ rank : V → ℕ,
        (∀ r ∈ S, parent r = r) ∧
        (∀ x, x ∉ S → G.Adj (parent x) x ∧ rank (parent x) < rank x) ∧
        (∀ x, x ∈ S ↔ rank x = 0) ∧
        (∀ x y, G.Adj x y → x = parent y ∨ y = parent x) := by
  classical
  intro W R adjacentSymm forestCount V finiteType G adjacencyDecidability hG S hsep hnum
  classical
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hcard : Fintype.card S = Fintype.card G.ConnectedComponent := by
    have hc := forestCount G hG
    rw [Nat.card_eq_fintype_card] at hnum hc
    omega
  let rootMap : S → G.ConnectedComponent := fun r => G.connectedComponentMk r.val
  have hinj : Function.Injective rootMap := by
    intro x y hxy
    apply Subtype.ext
    exact hsep x.val x.property y.val y.property (SimpleGraph.ConnectedComponent.exact hxy)
  have hsurj : Function.Surjective rootMap :=
    ((Fintype.bijective_iff_injective_and_card rootMap).mpr ⟨hinj, hcard⟩).2
  have hex : ∀ c : G.ConnectedComponent, ∃ r : c, r.val ∈ S := by
    intro c
    obtain ⟨r, hr⟩ := hsurj c
    exact ⟨⟨r.val, hr⟩, r.property⟩
  choose root hroot using hex
  have hrootEq (c : G.ConnectedComponent) (x : c) (hx : x.val ∈ S) : x = root c := by
    apply Subtype.ext
    exact hsep x.val hx (root c).val (hroot c)
      (c.reachable_of_mem_supp x.property (root c).property)
  have extract (c : G.ConnectedComponent) :
      ∃ parent : c → c, ∃ rank : c → ℕ,
        parent (root c) = root c ∧
        (∀ x, x ≠ root c → c.toSimpleGraph.Adj (parent x) x ∧
          rank (parent x) < rank x) ∧
        (∀ x, rank x = 0 ↔ x = root c) ∧
        (∀ x y, c.toSimpleGraph.Adj x y → x = parent y ∨ y = parent x) := by
    let T := c.toSimpleGraph
    have hacyc : T.IsAcyclic := (hG.isTree_connectedComponent c).isAcyclic
    have hreach : ∀ x, T.Reachable (root c) x :=
      fun x => c.connected_toSimpleGraph.preconnected (root c) x
    choose p hp hd using fun x => (hreach x).exists_path_of_dist
    let parent : c → c := fun x => (p x).penultimate
    let rank : c → ℕ := fun x => (p x).length
    refine ⟨parent, rank, ?_, ?_, ?_, ?_⟩
    · have hnil : p (root c) = .nil := by
        exact Subtype.mk.inj (hacyc.subsingleton_path (root c) (root c) |>.elim
          (Subtype.mk (p (root c)) (hp (root c))) (Subtype.mk .nil SimpleGraph.Walk.IsPath.nil))
      simp [parent, hnil]
    · intro x hx
      have hnon : ¬ (p x).Nil := SimpleGraph.Walk.not_nil_of_ne (Ne.symm hx)
      refine ⟨(p x).adj_penultimate hnon, ?_⟩
      have hpath : p (parent x) = (p x).dropLast := by
        exact Subtype.mk.inj (hacyc.subsingleton_path (root c) (parent x) |>.elim
          (Subtype.mk (p (parent x)) (hp (parent x)))
          (Subtype.mk (p x).dropLast (hp x).dropLast))
      have hlen := (p x).length_dropLast_add_one hnon
      change (p (parent x)).length < (p x).length
      rw [hpath]
      omega
    · intro x
      change (p x).length = 0 ↔ x = root c
      rw [hd x, (hreach x).dist_eq_zero_iff, eq_comm]
    · intro x y hxy
      by_cases hx : x ∈ (p y).support
      · have heq := hacyc.path_concat (hp x) (hp y) hxy hx
        left
        change x = (p y).penultimate
        rw [heq, SimpleGraph.Walk.penultimate_concat]
      · have hy := hacyc.mem_support_of_ne_mem_support_of_adj_of_isPath
          (hp x) (hp y) hxy hx
        have heq := hacyc.path_concat (hp y) (hp x) hxy.symm hy
        right
        change y = (p x).penultimate
        rw [heq, SimpleGraph.Walk.penultimate_concat]
  choose pc nc hself hnon hzero hedge using extract
  let parentV : V → V := fun x => (pc (G.connectedComponentMk x) ⟨x, rfl⟩).val
  let rankV : V → ℕ := fun x => nc (G.connectedComponentMk x) ⟨x, rfl⟩
  have hparentV (c : G.ConnectedComponent) (x : c) :
      parentV x.val = (pc c x).val := by
    rcases x with ⟨x, hx⟩
    change G.connectedComponentMk x = c at hx
    subst c
    rfl
  have hrankV (c : G.ConnectedComponent) (x : c) : rankV x.val = nc c x := by
    rcases x with ⟨x, hx⟩
    change G.connectedComponentMk x = c at hx
    subst c
    rfl
  refine ⟨parentV, rankV, ?_, ?_, ?_, ?_⟩
  · intro r hr
    let c := G.connectedComponentMk r
    let x : c := ⟨r, rfl⟩
    have he := hrootEq c x hr
    change parentV x.val = x.val
    rw [hparentV c x, he, hself]
  · intro x hx
    let c := G.connectedComponentMk x
    let v : c := ⟨x, rfl⟩
    have hvr : v ≠ root c := by
      intro he
      apply hx
      change v.val ∈ S
      rw [he]
      exact hroot c
    obtain ⟨ha, hl⟩ := hnon c v hvr
    constructor
    · change G.Adj (parentV v.val) v.val
      rw [hparentV c v]
      exact ha
    · change rankV (parentV v.val) < rankV v.val
      rw [hparentV c v, hrankV c (pc c v), hrankV c v]
      exact hl
  · intro x
    let c := G.connectedComponentMk x
    let v : c := ⟨x, rfl⟩
    constructor
    · intro hx
      change rankV v.val = 0
      rw [hrankV c v]
      exact (hzero c v).2 (hrootEq c v hx)
    · intro hz
      have hz' : nc c v = 0 := by rw [← hrankV c v]; exact hz
      have he := (hzero c v).1 hz'
      change v.val ∈ S
      rw [he]
      exact hroot c
  · intro x y hxy
    let c := G.connectedComponentMk x
    let vx : c := ⟨x, rfl⟩
    let vy : c := ⟨y, SimpleGraph.ConnectedComponent.sound hxy.symm.reachable⟩
    obtain h | h := hedge c vx vy hxy
    · left
      change vx.val = parentV vy.val
      rw [hparentV c vy]
      exact congrArg Subtype.val h
    · right
      change vy.val = parentV vx.val
      rw [hparentV c vx]
      exact congrArg Subtype.val h

private theorem hsumIndicator :
    ∀ (W : Finset GaussianInt), ∀ (R : Finset GaussianInt), (R ⊆ W) → (∑ x ∈ W, (1 - if x ∈ R
        then (1 : ℤ) else 0)) =
      (W.card : ℤ) - (R.card : ℤ) := by
  classical
  intro W R hRW
  have hfilter : W.filter (fun x => x ∈ R) = R := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hRW h, h⟩⟩
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, hfilter]
  simp

private theorem hcardS :
    ∀ (W : Finset GaussianInt), ∀ (R : Finset GaussianInt), (R ⊆ W) →
    let X := {x : GaussianInt // x ∈ W}
    let S : Set X := {x | x.val ∈ R}
    Nat.card S = R.card := by
  classical
  intro W R hRW X S
  let e : S ≃ {x : GaussianInt // x ∈ R} := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun r => ⟨⟨r.val, hRW r.property⟩, r.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  calc
    _ = Nat.card {x : GaussianInt // x ∈ R} := Nat.card_congr e
    _ = R.card := by simp [Nat.card_eq_fintype_card]

private theorem hbudget :
    ∀ (W : Finset GaussianInt), ∀ (R : Finset GaussianInt), ((∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ)
        else 0)) = ((((W.product W).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ)) → ∀ (adjacentSymm : ∀ {a : GaussianInt},
            ∀ {b : GaussianInt}, (FourNeighborAdjacent a b) → FourNeighborAdjacent b a),
    let X := {x : GaussianInt // x ∈ W}
    let G : SimpleGraph X := {
      Adj := fun x y => FourNeighborAdjacent x.1 y.1
      symm := ⟨by
        intro x y h
        exact adjacentSymm h⟩
      loopless := ⟨by
        intro x h
        rcases h with h | h | h | h <;>
          simp [Zsqrtd.ext_iff] at h <;> omega⟩
    }
    letI : DecidableRel FourNeighborAdjacent := fun _ _ => Classical.propDecidable _
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    let P := (W.product W).filter fun e => FourNeighborAdjacent e.1 e.2
    (P.card / 2 = G.edgeFinset.card) → ((∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) =
        (G.edgeFinset.card : ℤ)) → ((∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) = (W.card : ℤ)
        - (R.card : ℤ)) →
    let S : Set X := {x | x.val ∈ R}
    (Nat.card S = R.card) → G.edgeFinset.card + Nat.card S = Fintype.card X := by
  classical
  intro W R hcount adjacentSymm X G P hdiv hcountGraph hsumIndicator S hcardS
  have hc : (W.card : ℤ) - (R.card : ℤ) = (G.edgeFinset.card : ℤ) :=
    hsumIndicator.symm.trans hcountGraph
  have hcardX : Fintype.card X = W.card := by simp [X]
  rw [hcardS, hcardX]
  omega

private theorem hparent :
    ∀ (W : Finset GaussianInt),
    let X := {x : GaussianInt // x ∈ W}
    ∀ (p : X → X),
    let parent : GaussianInt → GaussianInt := fun x =>
      if hx : x ∈ W then (p ⟨x, hx⟩).val else x
    ∀ (x : X), parent x.val = (p x).val := by
  classical
  intro W X p parent x
  simp [parent, x.property]

private theorem hrank :
    ∀ (W : Finset GaussianInt),
    let X := {x : GaussianInt // x ∈ W}
    ∀ (depth : X → ℕ),
    let rank : GaussianInt → ℕ := fun x =>
      if hx : x ∈ W then depth ⟨x, hx⟩ else 0
    ∀ (x : X), rank x.val = depth x := by
  classical
  intro W X depth rank x
  simp [rank, x.property]

end ForestCompletionLemmas

theorem P4250T2FiniteForestCompletion
    (W R : Finset GaussianInt) (hRW : R ⊆ W)
    (hcycle : ∀ V E, SimpleGridCycle V E → ¬ V ⊆ (W : Set GaussianInt))
    (hseparate : ∀ a ∈ R, ∀ b ∈ R, ∀ V E,
      SimpleGridPathBetween V E a b → V ⊆ (W : Set GaussianInt) → a = b)
    (hcount : (∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) =
      ((((W.product W).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ)) :
    RootedFourNeighborForest W R := by
-- BODY
  classical
  have noGridTriangle (x y z : GaussianInt)
      (hxy : FourNeighborAdjacent x y)
      (hyz : FourNeighborAdjacent y z)
      (hzx : FourNeighborAdjacent z x) : False := ForestCompletionLemmas.noGridTriangle W R x y z
          hxy hyz hzx
  have adjacentSymm {a b : GaussianInt} (h : FourNeighborAdjacent a b) :
      FourNeighborAdjacent b a := ForestCompletionLemmas.adjacentSymm (a := a) (b := b) h
  let H : SimpleGraph GaussianInt := {
    Adj := fun x y => FourNeighborAdjacent x y ∧ x ∈ W ∧ y ∈ W
    symm := ⟨by
      intro x y h
      exact ⟨adjacentSymm h.1, h.2.2, h.2.1⟩⟩
    loopless := ⟨by
      intro x h
      rcases h.1 with h | h | h | h <;>
        simp [Zsqrtd.ext_iff] at h <;> omega⟩
  }
  have hHacyclic : H.IsAcyclic := ForestCompletionLemmas.hHacyclic W R hcycle noGridTriangle
      adjacentSymm
  let X := {x : GaussianInt // x ∈ W}
  let G : SimpleGraph X := {
    Adj := fun x y => FourNeighborAdjacent x.1 y.1
    symm := ⟨by
      intro x y h
      exact adjacentSymm h⟩
    loopless := ⟨by
      intro x h
      rcases h with h | h | h | h <;>
        simp [Zsqrtd.ext_iff] at h <;> omega⟩
  }
  let f : G →g H := {
    toFun := Subtype.val
    map_rel' := by
      intro x y h
      exact ⟨h, x.2, y.2⟩
  }
  have finj : Function.Injective f := ForestCompletionLemmas.finj W R adjacentSymm
  have hGacyclic : G.IsAcyclic := ForestCompletionLemmas.hGacyclic W R adjacentSymm hHacyclic finj
  let P := (W.product W).filter fun e => FourNeighborAdjacent e.1 e.2
  let Q := Finset.univ.filter fun e : X × X => G.Adj e.1 e.2
  have hPQ : P.card = Q.card := ForestCompletionLemmas.hPQ W R adjacentSymm
  have hordered : P.card = 2 * G.edgeFinset.card := ForestCompletionLemmas.hordered W R
      adjacentSymm hPQ
  have hdiv : P.card / 2 = G.edgeFinset.card := ForestCompletionLemmas.hdiv W R adjacentSymm
      hordered
  have hcountGraph : (∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) =
      (G.edgeFinset.card : ℤ) := ForestCompletionLemmas.hcountGraph W R hcount adjacentSymm hdiv
  have supportAdj : ∀ {s t : GaussianInt} (q : H.Walk s t)
      {l₁ l₂ : List GaussianInt} {x y : GaussianInt},
      q.support = l₁ ++ x :: y :: l₂ → H.Adj x y := ForestCompletionLemmas.supportAdj W R
          adjacentSymm
  have allWalkW {u v : GaussianInt} (q : H.Walk u v) (hu : u ∈ W) :
      ∀ z ∈ q.support, z ∈ W := ForestCompletionLemmas.allWalkW W R adjacentSymm (u := u) (v :=
          v) q hu
  have pathToGrid {s t : GaussianInt} (p : H.Walk s t) (hp : p.IsPath)
      (hne : s ≠ t) (hs : s ∈ W) (ht : t ∈ W) :
      ∃ V E, SimpleGridPathBetween V E s t ∧ V ⊆ (W : Set GaussianInt) :=
          ForestCompletionLemmas.pathToGrid W R adjacentSymm supportAdj allWalkW (s := s) (t :=
          t) p hp hne hs ht
  have hrootSeparateGraph : ∀ x : X, x.1 ∈ R → ∀ y : X, y.1 ∈ R →
      G.Reachable x y → x.1 = y.1 := ForestCompletionLemmas.hrootSeparateGraph W R hseparate
          adjacentSymm finj pathToGrid
  have forestCount {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (hG : G.IsAcyclic) :
      G.edgeFinset.card + Nat.card G.ConnectedComponent = Fintype.card V :=
          ForestCompletionLemmas.forestCount W R adjacentSymm (V := V) G hG
  have forestRooted {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (hG : G.IsAcyclic) (S : Set V)
      (hsep : ∀ x ∈ S, ∀ y ∈ S, G.Reachable x y → x = y)
      (hnum : G.edgeFinset.card + Nat.card S = Fintype.card V) :
      ∃ parent : V → V, ∃ rank : V → ℕ,
        (∀ r ∈ S, parent r = r) ∧
        (∀ x, x ∉ S → G.Adj (parent x) x ∧ rank (parent x) < rank x) ∧
        (∀ x, x ∈ S ↔ rank x = 0) ∧
        (∀ x y, G.Adj x y → x = parent y ∨ y = parent x) := ForestCompletionLemmas.forestRooted W
            R adjacentSymm forestCount (V := V) G hG S hsep hnum
  have hsumIndicator : (∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) =
      (W.card : ℤ) - (R.card : ℤ) := ForestCompletionLemmas.hsumIndicator W R hRW
  let S : Set X := {x | x.val ∈ R}
  have hcardS : Nat.card S = R.card := ForestCompletionLemmas.hcardS W R hRW
  have hbudget : G.edgeFinset.card + Nat.card S = Fintype.card X :=
      ForestCompletionLemmas.hbudget W R hcount adjacentSymm hdiv hcountGraph hsumIndicator hcardS
  obtain ⟨p, depth, hp, hpar, hzero, hedge⟩ :=
    forestRooted G hGacyclic S
      (by
        intro x hx y hy hxy
        exact Subtype.ext (hrootSeparateGraph x hx y hy hxy))
      hbudget
  let parent : GaussianInt → GaussianInt := fun x =>
    if hx : x ∈ W then (p ⟨x, hx⟩).val else x
  let rank : GaussianInt → ℕ := fun x =>
    if hx : x ∈ W then depth ⟨x, hx⟩ else 0
  have hparent (x : X) : parent x.val = (p x).val := ForestCompletionLemmas.hparent W p x
  have hrank (x : X) : rank x.val = depth x := ForestCompletionLemmas.hrank W depth x
  refine ⟨hRW, parent, rank, ?_, ?_, ?_, ?_⟩
  · intro r hr
    let x : X := ⟨r, hRW hr⟩
    change parent x.val = x.val
    rw [hparent x, hp x hr]
  · intro x hx hxr
    let v : X := ⟨x, hx⟩
    obtain ⟨ha, hl⟩ := hpar v hxr
    refine ⟨?_, ?_, ?_⟩
    · change parent v.val ∈ W
      rw [hparent v]
      exact (p v).property
    · change FourNeighborAdjacent (parent v.val) v.val
      rw [hparent v]
      exact ha
    · change rank (parent v.val) < rank v.val
      rw [hparent v, hrank (p v), hrank v]
      exact hl
  · intro x hx
    let v : X := ⟨x, hx⟩
    change v.val ∈ R ↔ rank v.val = 0
    rw [hrank v]
    exact hzero v
  · intro x hx y hy hxy
    let vx : X := ⟨x, hx⟩
    let vy : X := ⟨y, hy⟩
    obtain h | h := hedge vx vy hxy
    · left
      change vx.val = parent vy.val
      rw [hparent vy]
      exact congrArg Subtype.val h
    · right
      change vy.val = parent vx.val
      rw [hparent vx]
      exact congrArg Subtype.val h

end ApollonianSuperharmonic

end
