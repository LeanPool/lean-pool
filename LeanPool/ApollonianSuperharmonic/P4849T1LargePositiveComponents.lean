/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4849T1Component
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public meta import Lean.Meta.Tactic.NormCast

-- [TABLET NODE: P4849T1LargePositiveComponents]

/-!
# P4849T1LargePositiveComponents

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PositiveComponentLemmas

private theorem adjSymm :
    ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (FourNeighborAdjacent x y) → FourNeighborAdjacent y
        x := by
  classical
  intro x y h
  rcases h with h | h | h | h <;> subst y <;>
    simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem edgeSymm :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (FourNeighborAdjacent x y) → FourNeighborAdjacent
        y x) → ∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (edge x y) → edge y x := by
  classical
  intro q S edge adjSymm x y h
  exact ⟨adjSymm h.1, h.2.2, h.2.1⟩

private theorem reachSymm :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (edge x y) → edge y x) → ∀ {x : GaussianInt}, ∀ {y
        : GaussianInt}, (reach x y) → reach y x := by
  classical
  intro q S edge reach edgeSymm x y h
  induction h with
  | refl => exact .refl
  | tail h hxy ih => exact (Relation.ReflTransGen.single (edgeSymm hxy)).trans ih

private theorem gridReach :
    ∀ (u : GaussianInt), ∀ (v : GaussianInt), Relation.ReflTransGen FourNeighborAdjacent u v := by
  classical
  intro u v
  have horizontal (a : GaussianInt) (r : ℤ) :
      Relation.ReflTransGen FourNeighborAdjacent a (a + ⟨r, 0⟩) := by
    refine Int.inductionOn' r 0 ?_ ?_ ?_
    · have hz : (⟨0, 0⟩ : GaussianInt) = 0 := by ext <;> simp
      rw [hz, add_zero]
    · intro k hk ih
      have heq : a + ⟨k + 1, 0⟩ = (a + ⟨k, 0⟩) + 1 := by
        ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]; ring
      exact ih.tail (Or.inl heq)
    · intro k hk ih
      have heq : a + ⟨k - 1, 0⟩ = (a + ⟨k, 0⟩) - 1 := by
        ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add,
          Zsqrtd.re_sub, Zsqrtd.im_sub]; ring
      exact ih.tail (Or.inr (Or.inl heq))
  have vertical (a : GaussianInt) (r : ℤ) :
      Relation.ReflTransGen FourNeighborAdjacent a (a + ⟨0, r⟩) := by
    refine Int.inductionOn' r 0 ?_ ?_ ?_
    · have hz : (⟨0, 0⟩ : GaussianInt) = 0 := by ext <;> simp
      rw [hz, add_zero]
    · intro k hk ih
      have heq : a + ⟨0, k + 1⟩ = (a + ⟨0, k⟩) + ⟨0, 1⟩ := by
        ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add]; ring
      exact ih.tail (Or.inr (Or.inr (Or.inl heq)))
    · intro k hk ih
      have heq : a + ⟨0, k - 1⟩ = (a + ⟨0, k⟩) - ⟨0, 1⟩ := by
        ext <;> simp [Zsqrtd.re_add, Zsqrtd.im_add,
          Zsqrtd.re_sub, Zsqrtd.im_sub]; ring
      exact ih.tail (Or.inr (Or.inr (Or.inr heq)))
  let r := v.re - u.re
  let s := v.im - u.im
  have hp := horizontal u r
  have hq := vertical (u + ⟨r, 0⟩) s
  have heq : u + ⟨r, 0⟩ + ⟨0, s⟩ = v := by
    ext <;> simp [r, s, Zsqrtd.re_add, Zsqrtd.im_add]
  rw [← heq]
  exact hp.trans hq

private theorem chainReach :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    ∀ (p : List GaussianInt), (p.IsChain edge) → ∀ (hne : p ≠ []), ∀ y, y ∈ p →
        Relation.ReflTransGen edge (p.head hne) y := by
  classical
  intro q S edge p hp hne
  induction p with
  | nil => simp at hne
  | cons a p ih =>
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact .refl
    · cases p with
      | nil => simp at hy
      | cons b p =>
        have h₁ : edge a b := hp.rel
        have h₂ : List.IsChain edge (b :: p) := hp.tail
        have hn : b :: p ≠ [] := by simp
        have hr := ih h₂ hn y (by simpa using hy)
        simpa using (Relation.ReflTransGen.single h₁).trans hr

private theorem reachPos :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, (a ∈ S) → (reach a b) → b ∈ S := by
  classical
  intro q S edge reach a b ha h
  induction h with
  | refl => exact ha
  | tail h hstep ih => exact hstep.2.2

private theorem reachWalk :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    (∀ (p : List GaussianInt), (p.IsChain edge) → ∀ (hne : p ≠ []), ∀ y, y ∈ p →
        Relation.ReflTransGen edge (p.head hne) y) → (∀ {a : GaussianInt}, ∀ {b : GaussianInt},
        (a ∈ S) → (reach a b) → b ∈ S) → ∀ (x : GaussianInt), ∀ (y : GaussianInt), x ∈ S → reach
        x y →
      ∃ p : List GaussianInt, p.head? = some x ∧ p.getLast? = some y ∧
        (∀ z ∈ p, z ∈ S) ∧ p.IsChain FourNeighborAdjacent := by
  classical
  intro q S edge reach chainReach reachPos x y hx h
  change Relation.ReflTransGen edge x y at h
  obtain ⟨l, hc, hl⟩ := List.exists_isChain_cons_of_relationReflTransGen h
  refine ⟨x :: l, rfl, ?_, ?_, hc.imp (fun _ _ he => he.1)⟩
  · simpa [List.getLast?_eq_some_getLast (List.cons_ne_nil x l)] using
      congrArg some hl
  · intro z hz
    have hne : x :: l ≠ [] := by simp
    have hrz := chainReach (x :: l) hc hne z hz
    exact reachPos hx hrz

private theorem Bsucc :
    ∀ (M : ℤ),
    let B : ℕ → ℤ := fun n => Nat.rec 0 (fun _ b => 4 * b + M) n
    ∀ (n : ℕ), B (n + 1) = 4 * B n + M := by
  classical
  intro M B n
  simp [B]

private theorem Bnonneg :
    ∀ (M : ℤ), (0 ≤ M) →
    let B : ℕ → ℤ := fun n => Nat.rec 0 (fun _ b => 4 * b + M) n
    (∀ (n : ℕ), B (n + 1) = 4 * B n + M) → ∀ (n : ℕ), 0 ≤ B n := by
  classical
  intro M hM B Bsucc n
  induction n with
  | zero => simp [B]
  | succ n ih => rw [Bsucc]; nlinarith [hM]

private theorem Bmono :
    ∀ (M : ℤ), (0 ≤ M) →
    let B : ℕ → ℤ := fun n => Nat.rec 0 (fun _ b => 4 * b + M) n
    (∀ (n : ℕ), B (n + 1) = 4 * B n + M) → (∀ (n : ℕ), 0 ≤ B n) → ∀ (n : ℕ), ∀ (m : ℕ), (n ≤ m) →
        B n ≤ B m := by
  classical
  intro M hM B Bsucc Bnonneg n m hnm
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [Bsucc]
    nlinarith [Bnonneg k, hM]

private theorem hxpos :
    ∀ (q : IntegerLatticeFunction),
      ∀ (M : ℤ),
        ∀ (N : ℕ),
          let S : Set GaussianInt := {x | 0 < q x}
          let B : ℕ → ℤ := fun n => Nat.rec 0 (fun _ b => 4 * b + M) n
          (∀ (n : ℕ), 0 ≤ B n) → ∀ (x : GaussianInt), B (N + 1) < q x → x ∈ S := by
  classical
  intro q M N S B Bnonneg x hx
  change 0 < q x
  have hB := Bnonneg (N + 1)
  omega

private theorem hxC :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    ∀ (x : GaussianInt),
    let C : Set GaussianInt := {y | reach x y}
    x ∈ C := by
  classical
  intro q S edge reach x C
  change reach x x
  exact Relation.ReflTransGen.refl

private theorem hCpos :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    ∀ (x : GaussianInt), (x ∈ S) →
    let C : Set GaussianInt := {y | reach x y}
    C ⊆ S := by
  classical
  intro q S edge reach x hxpos C y hy
  have hy' : reach x y := hy
  change Relation.ReflTransGen edge x y at hy'
  induction hy' with
  | refl => exact hxpos
  | tail hxy hstep ih => exact hstep.2.2

private theorem hCconn :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (reach x y) → reach y x) → (∀ (p : List
        GaussianInt), (p.IsChain edge) → ∀ (hne : p ≠ []), ∀ y, y ∈ p → Relation.ReflTransGen
        edge (p.head hne) y) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), x ∈ S → reach x y → ∃ p
        : List GaussianInt, p.head? = some x ∧ p.getLast? = some y ∧ (∀ z ∈ p, z ∈ S) ∧ p.IsChain
        FourNeighborAdjacent) → ∀ (x : GaussianInt),
    let C : Set GaussianInt := {y | reach x y}
    (x ∈ C) → (C ⊆ S) → FourNeighborConnected C := by
  classical
  intro q S edge reach reachSymm chainReach reachWalk x C hxC hCpos
  refine ⟨⟨x, hxC⟩, ?_⟩
  intro y hy z hz
  have hy' : reach x y := hy
  have hz' : reach x z := hz
  have hyz : reach y z := (reachSymm hy').trans hz'
  obtain ⟨p, hp, hlast, hmem, hchain⟩ := reachWalk y z (hCpos hy) hyz
  refine ⟨p, hp, hlast, ?_, (List.isChain_iff_forall_rel_of_append_cons_cons).mp hchain⟩
  intro w hw
  have hne : p ≠ [] := by intro he; subst p; simp at hp
  have hedges : p.IsChain edge := hchain.imp_of_mem_imp
    (fun a b ha hb hab => ⟨hab, hmem a ha, hmem b hb⟩)
  have hwy := chainReach p hedges hne w hw
  -- Every path vertex is reachable from y, hence from the root x.
  have hyhead : p.head hne = y := by
    simpa [List.head?_eq_some_head hne] using hp
  have hrootw : reach x w := by
    have hwy' : reach y w := by simpa only [hyhead] using hwy
    exact hy'.trans hwy'
  exact hrootw

private theorem hCcomponent :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    ∀ (x : GaussianInt),
    let C : Set GaussianInt := {y | reach x y}
    (C ⊆ S) → (FourNeighborConnected C) → P4849T1Component S C := by
  classical
  intro q S edge reach x C hCpos hCconn
  refine ⟨hCconn, hCpos, ?_⟩
  intro y hy z hz hadj
  have he : edge y z := ⟨hadj, hCpos hy, hz⟩
  change reach x y at hy
  change reach x z
  exact Relation.ReflTransGen.tail hy he

private theorem firstExit :
    ∀ (q : IntegerLatticeFunction),
    let S : Set GaussianInt := {x | 0 < q x}
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
    ∀ (x : GaussianInt),
    let C : Set GaussianInt := {y | reach x y}
    ∀ {a : GaussianInt}, ∀ {b : GaussianInt}, (Relation.ReflTransGen FourNeighborAdjacent a b) →
        (a ∈ C) → (b ∉ C) → ∃ y z, y ∈ C ∧ z ∉ C ∧ FourNeighborAdjacent y z := by
  classical
  intro q S edge reach x C a b h ha hb
  induction h with
  | refl => exact (hb ha).elim
  | @tail b c h hbc ih =>
    by_cases hbC : b ∈ C
    · exact ⟨b, c, hbC, hb, hbc⟩
    · exact ih hbC

private theorem hzEq :
    ∀ (q : IntegerLatticeFunction),
        (∀ x, 0 ≤ q x) →
        let S : Set GaussianInt := {x | 0 < q x};
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S;
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y;
    ∀ (x : GaussianInt),
        let C : Set GaussianInt := {y | reach x y};
    (P4849T1Component S C) → ∀ (a : GaussianInt), ∀ (z : GaussianInt), (a ∈ C) → (z ∉ C) →
        (FourNeighborAdjacent a z) → q z = 0 := by
  classical
  intro q hq S edge reach x C hCcomponent a z haC hzC haz
  by_contra hn
  have hqn := hq z
  have hpos : 0 < q z := by omega
  have hzS : z ∈ S := hpos
  have hzIn : z ∈ C := hCcomponent.2.2 a haC z hzS haz
  exact hzC hzIn

private theorem hNoBig :
    ∀ (q : IntegerLatticeFunction),
        ∀ (N : ℕ), (¬∃ (C : Set GaussianInt),
        P4849T1Component {x : GaussianInt | 0 < q x} C ∧ ∃ (z : GaussianInt) (a : GaussianInt),
        q z = 0 ∧ a ∈ C ∧ FourNeighborAdjacent z a ∧ ∃ (F : Finset GaussianInt), (↑F : Set
        GaussianInt) ⊆ C ∧ N < F.card) →
    let S : Set GaussianInt := {x | 0 < q x};
    let edge (x y : GaussianInt) : Prop :=
      FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S;
    let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y;
    (∀ {x : GaussianInt}, ∀ {y : GaussianInt}, (FourNeighborAdjacent x y) → FourNeighborAdjacent
        y x) → ∀ (x : GaussianInt),
        let C : Set GaussianInt := {y | reach x y};
    (P4849T1Component S C) → ∀ (a : GaussianInt), ∀ (z : GaussianInt), (a ∈ C) →
        (FourNeighborAdjacent a z) → (q z = 0) → ∀ (F : Finset GaussianInt), ((↑F : Set
        GaussianInt) ⊆ C) → F.card ≤ N := by
  classical
  intro q N hbad S edge reach adjSymm x C hCcomponent a z haC haz hzEq F hF
  by_contra hcard
  have hgt : N < F.card := by omega
  apply hbad
  refine ⟨C, ?_, z, a, hzEq, haC, adjSymm haz, F, hF, hgt⟩
  simpa [S] using hCcomponent

end PositiveComponentLemmas

theorem P4849T1LargePositiveComponents (q : IntegerLatticeFunction) (M : ℤ)
    (hq : ∀ x, 0 ≤ q x) (hM : 0 ≤ M)
    (hlap : ∀ x, FourNeighborLaplacian q x ≤ M)
    (hzero : ∃ z, q z = 0) (hunbounded : ∀ B : ℤ, ∃ x, B < q x) :
    ∀ N : ℕ, ∃ C : Set GaussianInt,
      P4849T1Component {x | 0 < q x} C ∧
      ∃ z a : GaussianInt, q z = 0 ∧ a ∈ C ∧ FourNeighborAdjacent z a ∧
        ∃ F : Finset GaussianInt, (↑F : Set GaussianInt) ⊆ C ∧ N < F.card := by
-- BODY
  classical
  intro N
  by_contra hbad
  let S : Set GaussianInt := {x | 0 < q x}
  let edge (x y : GaussianInt) : Prop :=
    FourNeighborAdjacent x y ∧ x ∈ S ∧ y ∈ S
  let reach (x y : GaussianInt) : Prop := Relation.ReflTransGen edge x y
  have adjSymm {x y : GaussianInt} (h : FourNeighborAdjacent x y) :
      FourNeighborAdjacent y x := PositiveComponentLemmas.adjSymm (x := x) (y := y) h
  have edgeSymm {x y : GaussianInt} (h : edge x y) : edge y x := PositiveComponentLemmas.edgeSymm
      q adjSymm (x := x) (y := y) h
  have reachSymm {x y : GaussianInt} (h : reach x y) : reach y x :=
      PositiveComponentLemmas.reachSymm q edgeSymm (x := x) (y := y) h
  have gridReach (u v : GaussianInt) :
      Relation.ReflTransGen FourNeighborAdjacent u v := PositiveComponentLemmas.gridReach u v
  have chainReach (p : List GaussianInt) (hp : p.IsChain edge) (hne : p ≠ []) :
      ∀ y, y ∈ p → Relation.ReflTransGen edge (p.head hne) y :=
          PositiveComponentLemmas.chainReach q p hp hne
  have reachPos {a b : GaussianInt} (ha : a ∈ S) (h : reach a b) : b ∈ S :=
      PositiveComponentLemmas.reachPos q (a := a) (b := b) ha h
  have reachWalk : ∀ (x y : GaussianInt), x ∈ S → reach x y →
      ∃ p : List GaussianInt, p.head? = some x ∧ p.getLast? = some y ∧
        (∀ z ∈ p, z ∈ S) ∧ p.IsChain FourNeighborAdjacent := PositiveComponentLemmas.reachWalk q
            chainReach reachPos
  let B : ℕ → ℤ := fun n => Nat.rec 0 (fun _ b => 4 * b + M) n
  have Bsucc (n : ℕ) : B (n + 1) = 4 * B n + M := PositiveComponentLemmas.Bsucc M n
  have Bnonneg (n : ℕ) : 0 ≤ B n := PositiveComponentLemmas.Bnonneg M hM Bsucc n
  have Bmono (n m : ℕ) (hnm : n ≤ m) : B n ≤ B m := PositiveComponentLemmas.Bmono M hM Bsucc
      Bnonneg n m hnm
  obtain ⟨x, hx⟩ := hunbounded (B (N + 1))
  have hxpos : x ∈ S := PositiveComponentLemmas.hxpos q M N Bnonneg x hx
  obtain ⟨z₀, hz₀⟩ := hzero
  let C : Set GaussianInt := {y | reach x y}
  have hxC : x ∈ C := PositiveComponentLemmas.hxC q x
  have hCpos : C ⊆ S := PositiveComponentLemmas.hCpos q x hxpos
  have hCconn : FourNeighborConnected C := PositiveComponentLemmas.hCconn q reachSymm chainReach
      reachWalk x hxC hCpos
  have hCcomponent : P4849T1Component S C := PositiveComponentLemmas.hCcomponent q x hCpos hCconn
  have hz₀not : z₀ ∉ C := (show
      z₀ ∉ C
    from by
      classical
      intro hz
      have hpos := hCpos hz
      change 0 < q z₀ at hpos
      omega)
  have firstExit {a b : GaussianInt}
      (h : Relation.ReflTransGen FourNeighborAdjacent a b)
      (ha : a ∈ C) (hb : b ∉ C) :
      ∃ y z, y ∈ C ∧ z ∉ C ∧ FourNeighborAdjacent y z := PositiveComponentLemmas.firstExit q x (a
          := a) (b := b) h ha hb
  obtain ⟨a, z, haC, hzC, haz⟩ := firstExit (gridReach x z₀) hxC hz₀not
  have hzEq : q z = 0 := PositiveComponentLemmas.hzEq q hq x hCcomponent a z haC hzC haz
  have hNoBig (F : Finset GaussianInt)
      (hF : (↑F : Set GaussianInt) ⊆ C) : F.card ≤ N := PositiveComponentLemmas.hNoBig q N hbad
          adjSymm x hCcomponent a z haC haz hzEq F hF
  by_cases hN : N = 0
  · have hsingle : (↑({x} : Finset GaussianInt) : Set GaussianInt) ⊆ C := by
      intro y hy
      change y ∈ ({x} : Finset GaussianInt) at hy
      simp only [Finset.mem_singleton] at hy
      simpa [hy] using hxC
    have := hNoBig {x} hsingle
    simp at this
    omega
  · let V := {y : GaussianInt // y ∈ C}
    let G : SimpleGraph V := SimpleGraph.fromRel (fun y w =>
      FourNeighborAdjacent y.1 w.1)
    have rootReach : ∀ {y : GaussianInt} (hy : reach x y),
        G.Reachable ⟨x, hxC⟩ ⟨y, hy⟩ := by
      intro y hy
      rw [SimpleGraph.reachable_iff_reflTransGen]
      change Relation.ReflTransGen edge x y at hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | @tail b c h hstep ih =>
        have hc : c ∈ C := by
          change reach x c
          exact Relation.ReflTransGen.tail h hstep
        have hne : b ≠ c := by
          intro heq
          subst c
          rcases hstep.1 with hh | hh | hh | hh <;>
            simp [Zsqrtd.ext_iff] at hh <;> omega
        have hadj : G.Adj ⟨b, h⟩ ⟨c, hc⟩ := by
          apply (SimpleGraph.fromRel_adj _ _ _).2
          exact ⟨fun heq => hne (congrArg Subtype.val heq), Or.inl hstep.1⟩
        exact Relation.ReflTransGen.tail ih hadj
    let vx : V := ⟨x, hxC⟩
    let va : V := ⟨a, haC⟩
    have hrootA : G.Reachable vx va := rootReach haC
    have hrootX : G.Reachable vx vx := SimpleGraph.Reachable.refl vx
    have hpathReach : G.Reachable va vx := hrootA.symm.trans hrootX
    obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_isPath hpathReach
    let F : Finset GaussianInt := p.support.toFinset.image Subtype.val
    have hFsub : (↑F : Set GaussianInt) ⊆ C := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨w, hw, rfl⟩
      exact w.2
    have hFsize : F.card = p.support.length := by
      rw [Finset.card_image_iff.mpr (by
        intro u hu v hv heq
        exact Subtype.ext heq)]
      exact List.toFinset_card_of_nodup hp.support_nodup
    have hlen : p.length + 1 ≤ N := by
      have h := hNoBig F hFsub
      rw [hFsize, SimpleGraph.Walk.length_support] at h
      omega
    have graphAdjToGrid {u v : V} (h : G.Adj u v) :
        FourNeighborAdjacent u.1 v.1 := by
      have h' := (SimpleGraph.fromRel_adj _ _ _).1 h
      rcases h'.2 with huv | hvu
      · exact huv
      · exact adjSymm hvu
    have neighborBound {u v : GaussianInt}
        (huv : FourNeighborAdjacent u v) : q v ≤ 4 * q u + M := by
      have hl := hlap u
      simp only [FourNeighborLaplacian] at hl
      rcases huv with huv | huv | huv | huv
      · subst v
        nlinarith [hq (u - 1), hq (u + ⟨0, 1⟩), hq (u - ⟨0, 1⟩)]
      · subst v
        nlinarith [hq (u + 1), hq (u + ⟨0, 1⟩), hq (u - ⟨0, 1⟩)]
      · subst v
        nlinarith [hq (u + 1), hq (u - 1), hq (u - ⟨0, 1⟩)]
      · subst v
        nlinarith [hq (u + 1), hq (u - 1), hq (u + ⟨0, 1⟩)]
    have walkBound {u v : V} (t : ℕ) (p : G.Walk u v)
        (hu : q u.1 ≤ B t) : q v.1 ≤ B (t + p.length) := by
      induction p generalizing t with
      | nil => simpa using hu
      | @cons u v w huv p ih =>
        have hqv := neighborBound (graphAdjToGrid huv)
        have hv : q v.1 ≤ B (t + 1) := by
          rw [Bsucc]
          nlinarith
        have hw := ih (t + 1) hv
        have hidx : (t + 1) + p.length = t + (p.length + 1) := by omega
        simpa [hidx] using hw
    have hqa : q a ≤ B 1 := by
      have h := neighborBound (adjSymm haz)
      simpa [B, hzEq] using h
    have hqx := walkBound 1 p hqa
    have hidx : 1 + p.length ≤ N := by omega
    have hbound : q x ≤ B N := le_trans hqx (Bmono _ _ hidx)
    have hmono := Bmono N (N + 1) (by omega)
    omega

end ApollonianSuperharmonic

end
