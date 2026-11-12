/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.NoCheckerboardCellVertex
public import LeanPool.ApollonianSuperharmonic.ProtoTile
public import LeanPool.ApollonianSuperharmonic.SimpleGridCycle

-- [TABLET NODE: LatticeTileComplementGridConnected]

/-!
# LatticeTileComplementGridConnected

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ComplementGridPaths

private theorem adjacent_symm :
    (by
      classical
      exact
        ∀ {a : LatticeCell}, ∀ {b : LatticeCell}, FourNeighborAdjacent a b → FourNeighborAdjacent
            b a ) := by
  classical
  intro a b h
  rcases h with h | h | h | h <;> subst b
  all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem reach_symm :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        (∀ {a : LatticeCell}, ∀ {b : LatticeCell}, (step a b) → (step b a)) → (∀
            {a : LatticeCell}, ∀ {b : LatticeCell}, reach a b → reach b a) ) := by
  classical
  intro T S step reach step_symm a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single (step_symm hstep)) ih

private theorem reach_target_out :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        ∀ {a : LatticeCell}, ∀ {b : LatticeCell}, a ∉ S → reach a b → b ∉ S ) := by
  classical
  intro T S step reach a b ha h
  induction h with
  | refl => exact ha
  | tail h hstep ih => exact hstep.2.2

private theorem local_outside_reach :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        (∀ {a : LatticeCell}, ∀ {b : LatticeCell}, (reach a b) → (reach b a)) → ((∀
            {a : LatticeCell}, ∀ {b : LatticeCell}, (a ∉ S) → ((b ∉ S) → ((FourNeighborAdjacent a
            b) → (reach a b)))) → ((NoCheckerboardCellVertex S) → (
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        ∀ {v : LatticeCell}, ∀ {q : LatticeCell}, ∀ {r : LatticeCell}, around v q → around v r →
            q ∉ S → r ∉ S → reach q r))) ) := by
  classical
  intro T S step reach reach_symm one_step hchecker around v q r hq hr hqS hrS
  have diagA (hv : v ∉ S) (hsw : v - 1 - ⟨0, 1⟩ ∉ S) :
      reach v (v - 1 - ⟨0, 1⟩) := by
    by_cases hnw : v - 1 ∈ S
    · have hse : v - ⟨0, 1⟩ ∉ S := by
        intro hse
        exact hchecker v (Or.inr ⟨hnw, hse, hv, hsw⟩)
      exact Relation.ReflTransGen.trans
        (one_step hv hse (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        (one_step hse hsw (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
    · exact Relation.ReflTransGen.trans
        (one_step hv hnw (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        (one_step hnw hsw (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
  have diagB (hnw : v - 1 ∉ S) (hse : v - ⟨0, 1⟩ ∉ S) :
      reach (v - 1) (v - ⟨0, 1⟩) := by
    by_cases hne : v ∈ S
    · have hsw : v - 1 - ⟨0, 1⟩ ∉ S := by
        intro hsw
        exact hchecker v (Or.inl ⟨hne, hsw, hnw, hse⟩)
      exact Relation.ReflTransGen.trans
        (one_step hnw hsw (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        (one_step hsw hse (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
    · exact Relation.ReflTransGen.trans
        (one_step hnw hne (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
        (one_step hne hse (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff]))
  rcases hq with hq | hq | hq | hq <;>
    rcases hr with hr | hr | hr | hr <;>
    rw [hq] at hqS ⊢ <;>
    rw [hr] at hrS ⊢
  all_goals first
    | exact diagA hqS hrS
    | exact reach_symm (diagA hrS hqS)
    | exact diagB hqS hrS
    | exact reach_symm (diagB hrS hqS)
    | exact one_step hqS hrS (by simp [FourNeighborAdjacent, Zsqrtd.ext_iff])

private theorem boundary_outside_local :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        ∀ {a : LatticeCell}, ∀ {b : LatticeCell}, FourNeighborAdjacent a b → {a, b} ∈
            BoundaryFootprintEdges T → ∃ q ∉ S, around a q ∧ around b q ) := by
  classical
  intro T S around a b hab he
  have habne : a ≠ b := by
    intro h
    subst b
    simp [FourNeighborAdjacent, Zsqrtd.ext_iff] at hab
    omega
  rcases he with ⟨z, (⟨hez, hz⟩ | ⟨hez, hz⟩)⟩
  · have ha : a = z ∨ a = z + 1 := by
      have : a ∈ ({z, z + 1} : Finset GaussianInt) := by rw [← hez]; simp
      simpa using this
    have hb : b = z ∨ b = z + 1 := by
      have : b ∈ ({z, z + 1} : Finset GaussianInt) := by rw [← hez]; simp
      simpa using this
    rcases hz with ⟨hzS, hzout⟩ | ⟨hzout, hzS⟩
    · refine ⟨z - ⟨0, 1⟩, ?_, ?_, ?_⟩
      · simpa [S] using hzout
      · rcases ha with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (by
            simp [sub_eq_add_neg, add_assoc])))
      · rcases hb with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (by
            simp [sub_eq_add_neg, add_assoc])))
    · refine ⟨z, ?_, ?_, ?_⟩
      · simpa [S] using hzout
      · rcases ha with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by simp))
      · rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by simp))
  · have ha : a = z ∨ a = z + ⟨0, 1⟩ := by
      have : a ∈ ({z, z + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← hez]; simp
      simpa using this
    have hb : b = z ∨ b = z + ⟨0, 1⟩ := by
      have : b ∈ ({z, z + ⟨0, 1⟩} : Finset GaussianInt) := by rw [← hez]; simp
      simpa using this
    rcases hz with ⟨hzS, hzout⟩ | ⟨hzout, hzS⟩
    · refine ⟨z - 1, ?_, ?_, ?_⟩
      · simpa [S] using hzout
      · rcases ha with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (by
            simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])))
      · rcases hb with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inr (by
            simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm])))
    · refine ⟨z, ?_, ?_, ?_⟩
      · simpa [S] using hzout
      · rcases ha with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl (by simp)))
      · rcases hb with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl (by simp)))

private theorem hpEdgeRel :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (∀
            (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
            GaussianInt), p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) → ((∀ (e : Finset
            GaussianInt), e ∈ BoundaryFootprintEdges T ↔ e = {y, x} ∨ ∃ (a : GaussianInt) (b :
            GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂
            ∧ e = {a, b}) → (
        let edgeRel (a b : LatticeCell) : Prop :=
          FourNeighborAdjacent a b ∧
            ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
        List.IsChain edgeRel p)) ) := by
  classical
  intro T p x y hpAdjacent hpEdges edgeRel
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro a b l₁ l₂ hp
  refine ⟨hpAdjacent a b l₁ l₂ hp, ?_⟩
  exact (hpEdges {a, b}).2 (Or.inr ⟨a, b, l₁, l₂, hp, rfl⟩)

private theorem good_step :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        (∀ {v : LatticeCell}, ∀ {q : LatticeCell}, ∀ {r : LatticeCell}, (around v q) → ((around v
            r) → ((q ∉ S) → ((r ∉ S) → (reach q r))))) → ((∀ {a : LatticeCell}, ∀
            {b : LatticeCell}, (FourNeighborAdjacent a b) → ((({a, b} : Finset GaussianInt) ∈
            BoundaryFootprintEdges T) → (∃ q, q ∉ S ∧ around a q ∧ around b q))) → (∀ (base :
            LatticeCell),
        let good (v : LatticeCell) : Prop :=
          ∃ q, q ∉ S ∧ around v q ∧ reach q base
        let edgeRel (a b : LatticeCell) : Prop :=
          FourNeighborAdjacent a b ∧
            ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
        ∀ {a : LatticeCell}, ∀ {b : LatticeCell}, good a → edgeRel a b → good b)) ) := by
  classical
  intro T S step reach around local_outside_reach boundary_outside_local base good edgeRel a b ha
      hab
  rcases ha with ⟨q, hqOut, hqa, hqbase⟩
  rcases boundary_outside_local hab.1 hab.2 with ⟨r, hrOut, hra, hrb⟩
  exact ⟨r, hrOut, hrb,
    Relation.ReflTransGen.trans (local_outside_reach hra hqa hrOut hqOut) hqbase⟩

private theorem chain_good :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        ∀ (base : LatticeCell),
        let good (v : LatticeCell) : Prop :=
          ∃ q, q ∉ S ∧ around v q ∧ reach q base
        let edgeRel (a b : LatticeCell) : Prop :=
          FourNeighborAdjacent a b ∧
            ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
        (∀ {a : LatticeCell}, ∀ {b : LatticeCell}, (good a) → ((edgeRel a b) → (good b))) → (∀ (a
            : LatticeCell), ∀ (l : List LatticeCell), good a → List.IsChain edgeRel (a :: l) → ∀
            v ∈ a :: l, good v) ) := by
  classical
  intro T S step reach around base good edgeRel good_step a l
  induction l generalizing a with
  | nil =>
      intro ha _ v hv
      simp only [List.mem_singleton] at hv
      subst v
      exact ha
  | cons b l ih =>
      intro ha hchain v hv
      rw [List.isChain_cons] at hchain
      have hab : edgeRel a b := hchain.1 b (by simp)
      have hb : good b := good_step ha hab
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ha
      · exact ih b hb hchain.2 v hv

private theorem hpNonempty :
    (by
      classical
      exact
        ∀ (p : List GaussianInt), ∀ (x : GaussianInt), (p.head? = some x) → (p ≠ []) ) := by
  classical
  intro p x hpHead hp
  simp [hp] at hpHead

private theorem all_good :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        ∀ (p : List GaussianInt), ∀ (x : GaussianInt), ∀ (y : GaussianInt), (p.Nodup) → (((4 : ℕ)
            ≤ p.length) → ((p.head? = some x) → ((p.getLast? = some y) →
            ((BoundaryFootprintVertices T = (↑p.toFinset : Set GaussianInt)) → ((∀ (a :
            GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
            GaussianInt), p = l₁ ++ a :: b :: l₂ → FourNeighborAdjacent a b) → ((∀ (e : Finset
            GaussianInt), e ∈ BoundaryFootprintEdges T ↔ e = {y, x} ∨ ∃ (a : GaussianInt) (b :
            GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂
            ∧ e = {a, b}) → (∀ (base : LatticeCell),
        let good (v : LatticeCell) : Prop :=
          ∃ q, q ∉ S ∧ around v q ∧ reach q base
        (good x) → (
        let edgeRel (a b : LatticeCell) : Prop :=
          FourNeighborAdjacent a b ∧
            ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
        (List.IsChain edgeRel p) → ((∀ (a : LatticeCell), ∀ (l : List LatticeCell), good a →
            List.IsChain edgeRel (a :: l) → ∀ v ∈ a :: l, good v) → ((p ≠ []) → (∀ v ∈ p, good
            v))))))))))) ) := by
  classical
  intro T S step reach around p x y hpNodup hpLength hpHead hpLast hpVerts hpAdjacent hpEdges
      base good hgoodX edgeRel hpEdgeRel chain_good hpNonempty
  cases p with
  | nil => exact (hpNonempty rfl).elim
  | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hpHead
      subst a
      exact chain_good x l hgoodX hpEdgeRel

private theorem boundary_outside_reaches :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        (∀ {v : LatticeCell}, ∀ {q : LatticeCell}, ∀ {r : LatticeCell}, (around v q) → ((around v
            r) → ((q ∉ S) → ((r ∉ S) → (reach q r))))) → (∀ (p : List GaussianInt), ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), (∀ (e : Finset GaussianInt), e ∈
            BoundaryFootprintEdges T ↔ e = {y, x} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ :
            List GaussianInt) (l₂ : List GaussianInt), p = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → (∀
            (base : LatticeCell),
        let good (v : LatticeCell) : Prop :=
          ∃ q, q ∉ S ∧ around v q ∧ reach q base
        (∀ v ∈ p, good v) → ((x ∈ p) → ((y ∈ p) → (∀ {e : Finset GaussianInt}, ∀
            {v : LatticeCell}, ∀ {q : LatticeCell}, e ∈ BoundaryFootprintEdges T → v ∈ e → q ∉ S
            → around v q → reach q base))))) ) := by
  classical
  intro T S step reach around local_outside_reach p x y hpEdges base good all_good hxmem hymem e
      v q he hv hqOut hqv
  have hvGood : good v := by
    rcases (hpEdges e).1 he with heclose | hepath
    · rw [heclose] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv
      · subst v
        exact all_good y hymem
      · subst v
        exact all_good x hxmem
    · rcases hepath with ⟨a, b, l₁, l₂, hp, rfl⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv
      · subst v
        exact all_good a (by rw [hp]; simp)
      · subst v
        exact all_good b (by rw [hp]; simp)
  rcases hvGood with ⟨r, hrOut, hrv, hrbase⟩
  exact Relation.ReflTransGen.trans
    (local_outside_reach hqv hrv hqOut hrOut) hrbase

private theorem hexteriorOut :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        (List GaussianInt) → (∀ (z : LatticeCell), (∀ x' ∈ T.cells, x'.re ≤ z.re) → (
        let exterior : LatticeCell := z + 1
        exterior ∉ S)) ) := by
  classical
  intro T S p z hzmax exterior he
  have hle := hzmax exterior he
  dsimp [exterior] at hle
  omega

private theorem hrightEdge :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        ∀ (z : LatticeCell), (z ∈ S) → (
        let exterior : LatticeCell := z + 1
        (exterior ∉ S) → (
        let rightEdge : Finset GaussianInt := {z + 1, z + 1 + ⟨0, 1⟩}
        rightEdge ∈ BoundaryFootprintEdges T)) ) := by
  classical
  intro T S z hzS exterior hexteriorOut rightEdge
  refine ⟨z + 1, Or.inr ⟨rfl, Or.inr ⟨?_, ?_⟩⟩⟩
  · exact hexteriorOut
  · simpa [S, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzS

private theorem hexteriorBase :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        ∀ (base : LatticeCell), (∀ {e : Finset GaussianInt}, ∀ {v : LatticeCell}, ∀
            {q : LatticeCell}, (e ∈ BoundaryFootprintEdges T) → ((v ∈ e) → ((q ∉ S) → ((around v
            q) → (reach q base))))) → (∀ (z : LatticeCell),
        let exterior : LatticeCell := z + 1
        (exterior ∉ S) → (
        let rightEdge : Finset GaussianInt := {z + 1, z + 1 + ⟨0, 1⟩}
        (rightEdge ∈ BoundaryFootprintEdges T) → (reach exterior base))) ) := by
  classical
  intro T S step reach around base boundary_outside_reaches z exterior hexteriorOut rightEdge
      hrightEdge
  apply boundary_outside_reaches (v := z + 1) (q := exterior) hrightEdge
  · change z + 1 ∈ ({z + 1, z + 1 + ⟨0, 1⟩} : Finset GaussianInt)
    simp
  · exact hexteriorOut
  · exact Or.inl rfl

private theorem right_halfplane :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        (∀ {a : LatticeCell}, ∀ {b : LatticeCell}, (a ∉ S) → ((b ∉ S) → ((FourNeighborAdjacent a
            b) → (reach a b)))) → ((List GaussianInt) → (∀ (z : LatticeCell), (∀ x' ∈ T.cells,
            x'.re ≤ z.re) → (
        let exterior : LatticeCell := z + 1
        ∀ (q : LatticeCell), z.re < q.re → reach q exterior))) ) := by
  classical
  intro T S step reach one_step p z hzmax exterior q hq
  let column (k : Int) : LatticeCell := ⟨q.re, k⟩
  have column_out (k : Int) : column k ∉ S := by
    intro hkS
    have := hzmax (column k) hkS
    simp [column] at this
    omega
  have vertical : reach q (column z.im) := by
    have hqcol : q = column q.im := by
      apply Zsqrtd.ext <;> simp [column]
    rw [hqcol]
    exact Int.inductionOn' q.im z.im Relation.ReflTransGen.refl
      (fun k _ ih => Relation.ReflTransGen.trans
        (one_step (column_out (k + 1)) (column_out k)
          (by simp [column, FourNeighborAdjacent, Zsqrtd.ext_iff])) ih)
      (fun k _ ih => Relation.ReflTransGen.trans
        (one_step (column_out (k - 1)) (column_out k)
          (by simp [column, FourNeighborAdjacent, Zsqrtd.ext_iff])) ih)
  let row (n : Nat) : LatticeCell := ⟨z.re + 1 + n, z.im⟩
  have row_out (n : Nat) : row n ∉ S := by
    intro hnS
    have := hzmax (row n) hnS
    simp [row] at this
    omega
  have row_reach : ∀ n : Nat, reach (row n) exterior := by
    intro n
    induction n with
    | zero =>
        have : row 0 = exterior := by
          apply Zsqrtd.ext <;> simp [row, exterior]
        rw [this]
    | succ n ih =>
        exact Relation.ReflTransGen.trans
          (one_step (row_out (n + 1)) (row_out n)
            (by
              simp [row, FourNeighborAdjacent, Zsqrtd.ext_iff]
              omega)) ih
  let n : Nat := Int.natAbs (q.re - (z.re + 1))
  have hncast : (n : Int) = q.re - (z.re + 1) := by
    exact Int.natAbs_of_nonneg (by omega)
  have hcolrow : column z.im = row n := by
    apply Zsqrtd.ext
    · simp [column, row, hncast]
    · simp [column, row]
  rw [hcolrow] at vertical
  exact Relation.ReflTransGen.trans vertical (row_reach n)

private theorem every_outside_reaches :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        (∀ {a : LatticeCell}, ∀ {b : LatticeCell}, (a ∉ S) → ((reach a b) → (b ∉ S))) → (
        let around (v q : LatticeCell) : Prop :=
          q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
        (List GaussianInt) → (∀ (base : LatticeCell), (∀ {e : Finset GaussianInt}, ∀
            {v : LatticeCell}, ∀ {q : LatticeCell}, (e ∈ BoundaryFootprintEdges T) → ((v ∈ e) →
            ((q ∉ S) → ((around v q) → (reach q base))))) → (∀ (z : LatticeCell),
        let exterior : LatticeCell := z + 1
        (reach exterior base) → ((∀ (q : LatticeCell), (z.re < q.re) → (reach q exterior)) → (∀ q
            ∉ S, reach q base))))) ) := by
  classical
  intro T S step reach reach_target_out around p base boundary_outside_reaches z exterior
      hexteriorBase right_halfplane q hqOut
  by_contra hqbase
  have hqle : q.re ≤ z.re := by
    by_contra hnot
    exact hqbase (Relation.ReflTransGen.trans
      (right_halfplane q (by omega)) hexteriorBase)
  let distance (r : LatticeCell) : Nat := Int.natAbs (z.re - r.re)
  have hfind : ∃ n, ∃ r : LatticeCell, reach q r ∧ n = distance r :=
    ⟨distance q, q, Relation.ReflTransGen.refl, rfl⟩
  let n := Nat.find hfind
  rcases Nat.find_spec hfind with ⟨r, hqr, hn⟩
  have hrOut : r ∉ S := reach_target_out hqOut hqr
  have hrbase : ¬ reach r base := by
    intro hrbase
    exact hqbase (Relation.ReflTransGen.trans hqr hrbase)
  have hrle : r.re ≤ z.re := by
    by_contra hnot
    exact hrbase (Relation.ReflTransGen.trans
      (right_halfplane r (by omega)) hexteriorBase)
  have hmax : ∀ s : LatticeCell, reach q s → s.re ≤ r.re := by
    intro s hqs
    have hsbase : ¬ reach s base := by
      intro hsbase
      exact hqbase (Relation.ReflTransGen.trans hqs hsbase)
    have hsle : s.re ≤ z.re := by
      by_contra hnot
      exact hsbase (Relation.ReflTransGen.trans
        (right_halfplane s (by omega)) hexteriorBase)
    have hmin := Nat.find_min' hfind ⟨s, hqs, rfl⟩
    rw [hn] at hmin
    simp only [distance,
      ] at hmin
    omega
  have hrRightNotReach : ¬ reach q (r + 1) := by
    intro hreach
    have := hmax (r + 1) hreach
    simp at this
  have hrRightS : r + 1 ∈ S := by
    by_contra hout
    apply hrRightNotReach
    exact Relation.ReflTransGen.tail hqr
      ⟨by simp [FourNeighborAdjacent, Zsqrtd.ext_iff], hrOut, hout⟩
  let e : Finset GaussianInt := {r + 1, r + 1 + ⟨0, 1⟩}
  have he : e ∈ BoundaryFootprintEdges T := by
    refine ⟨r + 1, Or.inr ⟨rfl, Or.inl ⟨hrRightS, ?_⟩⟩⟩
    simpa [S, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hrOut
  have hrbase' : reach r base := by
    apply boundary_outside_reaches (v := r + 1) (q := r) he
    · dsimp [e]
      simp
    · exact hrOut
    · exact Or.inr (Or.inl (by simp))
  exact hrbase hrbase'

private theorem walk_of_reach :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let S : Set LatticeCell := T.cells
        let step : LatticeCell → LatticeCell → Prop := fun a b =>
          FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
        let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
        ∀ {u : LatticeCell}, ∀ {v : LatticeCell}, u ∉ S → reach u v → ∃ p : List LatticeCell,
            p.head? = some u ∧ p.getLast? = some v ∧ (∀ w ∈ p, w ∉ S) ∧ ∀ c d : LatticeCell, ∀ l₁
            l₂ : List LatticeCell, p = l₁ ++ c :: d :: l₂ → FourNeighborAdjacent c d ) := by
  classical
  intro T S step reach u v huOut huv
  induction huv using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨[v], by simp, by simp, ?_, ?_⟩
      · intro w hw
        rcases List.mem_singleton.mp hw with rfl
        exact huOut
      · exact (List.isChain_iff_forall_rel_of_append_cons_cons).1
          (List.isChain_singleton v)
  | @head u c huv hcv ih =>
      rcases huv with ⟨huv, huOut, hcOut⟩
      rcases ih hcOut with ⟨p, hpHead, hpLast, hpOut, hpAdjacent⟩
      have hpne : p ≠ [] := by
        intro hp
        simp [hp] at hpHead
      have hpchain : List.IsChain FourNeighborAdjacent p :=
        (List.isChain_iff_forall_rel_of_append_cons_cons).2 hpAdjacent
      have hchain : List.IsChain FourNeighborAdjacent (u :: p) := by
        rw [List.isChain_cons]
        exact ⟨by simpa [hpHead] using huv, hpchain⟩
      refine ⟨u :: p, by simp, ?_, ?_,
        (List.isChain_iff_forall_rel_of_append_cons_cons).1 hchain⟩
      · cases p with
        | nil => exact (hpne rfl).elim
        | cons c p => simpa using hpLast
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact huOut
        · exact hpOut w hw

end ComplementGridPaths

theorem LatticeTileComplementGridConnected (T : ProtoTile)
    (hT : LatticeTile T) :
    FourNeighborConnected ((T.cells : Set LatticeCell)ᶜ) := by
-- BODY
  classical
  let S : Set LatticeCell := T.cells
  let step : LatticeCell → LatticeCell → Prop := fun a b =>
    FourNeighborAdjacent a b ∧ a ∉ S ∧ b ∉ S
  let reach : LatticeCell → LatticeCell → Prop := Relation.ReflTransGen step
  have adjacent_symm {a b : LatticeCell} (h : FourNeighborAdjacent a b) :=
      ComplementGridPaths.adjacent_symm (a := a) (b := b) h
  have step_symm {a b : LatticeCell} (h : step a b) : step b a :=
    ⟨adjacent_symm h.1, h.2.2, h.2.1⟩
  have reach_symm {a b : LatticeCell} (h : reach a b) := ComplementGridPaths.reach_symm T
      step_symm (a := a) (b := b) h
  have reach_target_out {a b : LatticeCell} (ha : a ∉ S) (h : reach a b) :=
      ComplementGridPaths.reach_target_out T (a := a) (b := b) ha h
  have one_step {a b : LatticeCell} (ha : a ∉ S) (hb : b ∉ S)
      (hab : FourNeighborAdjacent a b) : reach a b :=
    Relation.ReflTransGen.single ⟨hab, ha, hb⟩
  have hgrid := LatticeTileGridStructure T hT
  have hoccupied : FourNeighborConnected S := hgrid.1
  have hchecker : NoCheckerboardCellVertex S := hgrid.2.1
  have hcycle : SimpleGridCycle (BoundaryFootprintVertices T)
      (BoundaryFootprintEdges T) := hgrid.2.2
  let around (v q : LatticeCell) : Prop :=
    q = v ∨ q = v - 1 ∨ q = v - ⟨0, 1⟩ ∨ q = v - 1 - ⟨0, 1⟩
  have local_outside_reach {v q r : LatticeCell}
      (hq : around v q) (hr : around v r) (hqS : q ∉ S) (hrS : r ∉ S) :=
          ComplementGridPaths.local_outside_reach T reach_symm one_step hchecker (v := v) (q :=
          q) (r := r) hq hr hqS hrS
  have boundary_outside_local {a b : LatticeCell}
      (hab : FourNeighborAdjacent a b)
      (he : ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T) :=
          ComplementGridPaths.boundary_outside_local T (a := a) (b := b) hab he
  rcases hcycle with ⟨p, x, y, hpNodup, hpLength, hpHead, hpLast, hpVerts,
    hyx, hpAdjacent, hpEdges⟩
  have hclosingEdge : ({y, x} : Finset GaussianInt) ∈ BoundaryFootprintEdges T :=
    (hpEdges {y, x}).2 (Or.inl rfl)
  rcases boundary_outside_local hyx hclosingEdge with
    ⟨base, hbaseOut, hbaseY, hbaseX⟩
  let good (v : LatticeCell) : Prop :=
    ∃ q, q ∉ S ∧ around v q ∧ reach q base
  have hgoodX : good x :=
    ⟨base, hbaseOut, hbaseX, Relation.ReflTransGen.refl⟩
  let edgeRel (a b : LatticeCell) : Prop :=
    FourNeighborAdjacent a b ∧
      ({a, b} : Finset GaussianInt) ∈ BoundaryFootprintEdges T
  have hpEdgeRel := ComplementGridPaths.hpEdgeRel T p x y hpAdjacent hpEdges
  have good_step {a b : LatticeCell} (ha : good a) (hab : edgeRel a b) :=
      ComplementGridPaths.good_step T local_outside_reach boundary_outside_local base (a := a) (b
      := b) ha hab
  have chain_good := ComplementGridPaths.chain_good T base good_step
  have hpNonempty := ComplementGridPaths.hpNonempty p x hpHead
  have all_good := ComplementGridPaths.all_good T p x y hpNodup hpLength hpHead hpLast hpVerts
      hpAdjacent hpEdges base hgoodX hpEdgeRel chain_good hpNonempty
  have hxmem : x ∈ p := by
    exact List.mem_of_mem_head? (by simp [hpHead])
  have hymem : y ∈ p := by
    exact List.mem_of_mem_getLast? (by simp [hpLast])
  have boundary_outside_reaches {e : Finset GaussianInt} {v q : LatticeCell}
      (he : e ∈ BoundaryFootprintEdges T) (hv : v ∈ e)
      (hqOut : q ∉ S) (hqv : around v q) := ComplementGridPaths.boundary_outside_reaches T
          local_outside_reach p x y hpEdges base all_good hxmem hymem (e := e) (v := v) (q := q)
          he hv hqOut hqv
  rcases hoccupied.1 with ⟨z₀, hz₀⟩
  rcases Finset.exists_max_image T.cells (fun z : LatticeCell => z.re)
      ⟨z₀, hz₀⟩ with ⟨z, hz, hzmax⟩
  have hzS : z ∈ S := hz
  let exterior : LatticeCell := z + 1
  have hexteriorOut : exterior ∉ S := ComplementGridPaths.hexteriorOut T p z hzmax
  let rightEdge : Finset GaussianInt := {z + 1, z + 1 + ⟨0, 1⟩}
  have hrightEdge := ComplementGridPaths.hrightEdge T z hzS hexteriorOut
  have hexteriorBase := ComplementGridPaths.hexteriorBase T base boundary_outside_reaches z
      hexteriorOut hrightEdge
  have right_halfplane (q : LatticeCell) (hq : z.re < q.re) :=
      ComplementGridPaths.right_halfplane T one_step p z hzmax q hq
  have every_outside_reaches (q : LatticeCell) (hqOut : q ∉ S) :=
      ComplementGridPaths.every_outside_reaches T reach_target_out p base
      boundary_outside_reaches z hexteriorBase right_halfplane q hqOut
  constructor
  · exact ⟨exterior, by simpa [S] using hexteriorOut⟩
  · intro a ha b hb
    have haOut : a ∉ S := by simpa [S] using ha
    have hbOut : b ∉ S := by simpa [S] using hb
    have habReach : reach a b := Relation.ReflTransGen.trans
      (every_outside_reaches a haOut)
      (reach_symm (every_outside_reaches b hbOut))
    have walk_of_reach : ∀ {u v : LatticeCell}, u ∉ S → reach u v →
        ∃ p : List LatticeCell,
          p.head? = some u ∧ p.getLast? = some v ∧
          (∀ w ∈ p, w ∉ S) ∧
          ∀ c d : LatticeCell, ∀ l₁ l₂ : List LatticeCell,
            p = l₁ ++ c :: d :: l₂ → FourNeighborAdjacent c d  :=
                ComplementGridPaths.walk_of_reach T
    rcases walk_of_reach haOut habReach with ⟨p, hpHead, hpLast, hpOut, hpAdjacent⟩
    exact ⟨p, hpHead, hpLast, by
      intro w hw
      simpa [S] using hpOut w hw, hpAdjacent⟩

end ApollonianSuperharmonic

end
