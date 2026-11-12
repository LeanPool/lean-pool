/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4677T2TouchingWalk
public import LeanPool.ApollonianSuperharmonic.LatticeTileFourNeighborConnected
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.LatticeTileBoundarySimpleGridCycle
public import Mathlib.Data.List.Chain

-- [TABLET NODE: P4677T2PrecursorWalk]

/-!
# P4677T2PrecursorWalk

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PrecursorWalkGeometry

private theorem boundary_edge_footprint :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ e ∈ BoundaryFootprintEdges T, e ∈ FootprintEdges T ) := by
  classical
  intro T e he
  rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      congr 1 <;> simp [Zsqrtd.ext_iff]
  · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
      congr 1 <;> simp []

private theorem edge_vertex :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ e ∈ FootprintEdges T, ∀ z ∈ e, z ∈ FootprintVertices T ) := by
  classical
  intro T e he z hz
  rcases he with ⟨c, hc, rfl | rfl | rfl | rfl⟩
  all_goals
    simp only [FootprintVertices,
      ite_eq_left (show T.cells.Nonempty from ⟨c, hc⟩), Set.mem_ofPred_eq]
    refine ⟨c, hc, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp

private theorem boundary_vertex_footprint :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (e ∈
            FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges T) → (∀ (z : GaussianInt), (z ∈ e) → (z ∈ FootprintVertices T))) → (∀
            (T : ProtoTile), ∀ z ∈ BoundaryFootprintVertices T, z ∈ FootprintVertices T)) ) := by
  classical
  intro boundary_edge_footprint edge_vertex T z hz
  by_cases hne : T.cells.Nonempty
  · simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hz
    obtain ⟨e, he, hze⟩ := hz
    exact edge_vertex T e (boundary_edge_footprint T e he) z hze
  · have hanchor : z = T.anchor := by
      simpa [BoundaryFootprintVertices, hne] using hz
    simp [FootprintVertices, hne, hanchor]

private theorem R_symm :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile),
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        ∀ (u : GaussianInt), ∀ (v : GaussianInt), R u v → R v u ) := by
  classical
  intro A B R u v huv
  refine ⟨huv.2.1, huv.1, ?_⟩
  simpa [Finset.pair_comm] using huv.2.2

private theorem reverse_reach :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile),
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        (∀ (u : GaussianInt), ∀ (v : GaussianInt), (R u v) → (R v u)) → (∀ {u : GaussianInt}, ∀
            {v : GaussianInt}, Relation.ReflTransGen R u v → Relation.ReflTransGen R v u) ) := by
  classical
  intro A B R R_symm u v h
  induction h with
  | refl => exact .refl
  | @tail b c hab hbc ih => exact ih.head (R_symm b c hbc)

private theorem head_reach :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile),
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        ∀ (u : GaussianInt), ∀ (l : List GaussianInt), List.IsChain R (u :: l) → ∀ z ∈ u :: l,
            Relation.ReflTransGen R u z ) := by
  classical
  intro A B R u l hc
  induction l generalizing u with
  | nil =>
      intro z hz
      have heq : z = u := by simpa using hz
      subst z
      exact .refl
  | cons v l ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact .refl
      · exact (Relation.ReflTransGen.single
          (List.isChain_cons_cons.mp hc).1).trans
          (ih v (List.isChain_cons_cons.mp hc).2 z hz)

private theorem chain_reach :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile),
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        (∀ (u : GaussianInt), ∀ (l : List GaussianInt), (List.IsChain R (u :: l)) → (∀ z ∈ u ::
            l, Relation.ReflTransGen R u z)) → (∀ {p : List GaussianInt}, ∀ {u : GaussianInt}, ∀
            {v : GaussianInt}, List.IsChain R p → p.head? = some u → p.getLast? = some v →
            Relation.ReflTransGen R u v) ) := by
  classical
  intro A B R head_reach p u v hc hh hl
  cases p with
  | nil => simp at hh
  | cons c cs =>
      have hcu : c = u := by simpa using hh
      subst c
      have hvmem : v ∈ u :: cs := by
        rcases List.getLast?_eq_some_iff.mp hl with ⟨l, hform⟩
        rw [hform]
        simp
      exact head_reach u cs hc v hvmem

private theorem edge_parent :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (T : ProtoTile), T.cells ⊆ A.cells → FootprintVertices T ⊆
            FootprintVertices A → ∀ e ∈ FootprintEdges T, e ∈ FootprintEdges A ) := by
  classical
  intro A T hTc hTf e he
  rcases he with ⟨c, hc, hshape⟩
  exact ⟨c, hTc hc, hshape⟩

private theorem edge_parentB :
    (by
      classical
      exact
        ∀ (B : ProtoTile), ∀ (T : ProtoTile), T.cells ⊆ B.cells → ∀ e ∈ FootprintEdges T, e ∈
            FootprintEdges B ) := by
  classical
  intro B T hTc e he
  rcases he with ⟨c, hc, hshape⟩
  exact ⟨c, hTc hc, hshape⟩

private theorem p₁chain :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells ⊆
            A.cells) → ((Y.cells ⊆ B.cells) → ((FootprintVertices X ⊆ FootprintVertices A) →
            ((FootprintVertices Y ⊆ FootprintVertices B) → (∀ (p₁ : List GaussianInt), (∀ z ∈ p₁,
            z ∈ FootprintVertices X ∩ FootprintVertices Y) → ((∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p₁ = l₁ ++ a :: b
            :: l₂ → {a, b} ∈ FootprintEdges X ∩ FootprintEdges Y) → (
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        (∀ (T : ProtoTile), (T.cells ⊆ A.cells) → ((FootprintVertices T ⊆ FootprintVertices A) →
            (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (e ∈ FootprintEdges A)))) → ((∀
            (T : ProtoTile), (T.cells ⊆ B.cells) → (∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges T) → (e ∈ FootprintEdges B))) → (List.IsChain R p₁)))))))) ) := by
  classical
  intro A B X Y hXc hYc hXf hYf p₁ hp₁v hp₁e R edge_parent edge_parentB
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro u v l r h
  refine ⟨?_, ?_, ?_⟩
  · have hu := hp₁v u (by simp [h])
    exact ⟨hXf hu.1, hYf hu.2⟩
  · have hv := hp₁v v (by simp [h])
    exact ⟨hXf hv.1, hYf hv.2⟩
  · have he := hp₁e u v l r h
    exact ⟨edge_parent X hXc hXf _ he.1,
      edge_parentB Y hYc _ he.2⟩

private theorem p₃chain :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (Z : ProtoTile), ∀ (W : ProtoTile), (Z.cells ⊆
            A.cells) → ((W.cells ⊆ B.cells) → ((FootprintVertices Z ⊆ FootprintVertices A) →
            ((FootprintVertices W ⊆ FootprintVertices B) → (∀ (p₃ : List GaussianInt), (∀ z ∈ p₃,
            z ∈ FootprintVertices Z ∩ FootprintVertices W) → ((∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p₃ = l₁ ++ a :: b
            :: l₂ → {a, b} ∈ FootprintEdges Z ∩ FootprintEdges W) → (
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        (∀ (T : ProtoTile), (T.cells ⊆ A.cells) → ((FootprintVertices T ⊆ FootprintVertices A) →
            (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (e ∈ FootprintEdges A)))) → ((∀
            (T : ProtoTile), (T.cells ⊆ B.cells) → (∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges T) → (e ∈ FootprintEdges B))) → (List.IsChain R p₃)))))))) ) := by
  classical
  intro A B Z W hZc hWc hZf hWf p₃ hp₃v hp₃e R edge_parent edge_parentB
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro u v l r h
  refine ⟨?_, ?_, ?_⟩
  · have hu := hp₃v u (by simp [h])
    exact ⟨hZf hu.1, hWf hu.2⟩
  · have hv := hp₃v v (by simp [h])
    exact ⟨hZf hv.1, hWf hv.2⟩
  · have he := hp₃e u v l r h
    exact ⟨edge_parent Z hZc hZf _ he.1,
      edge_parentB W hWc _ he.2⟩

private theorem p₁mem :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (X : ProtoTile), ∀ (Y : ProtoTile),
            (FootprintVertices X ⊆ FootprintVertices A) → ((FootprintVertices Y ⊆
            FootprintVertices B) → (∀ (p₁ : List GaussianInt), (∀ z ∈ p₁, z ∈ FootprintVertices X
            ∩ FootprintVertices Y) → (∀ z ∈ p₁, z ∈ FootprintVertices A ∩ FootprintVertices B)))
            ) := by
  classical
  intro A B X Y hXf hYf p₁ hp₁v z hz
  have hzv := hp₁v z hz
  exact ⟨hXf hzv.1, hYf hzv.2⟩

private theorem p₃mem :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (Z : ProtoTile), ∀ (W : ProtoTile),
            (FootprintVertices Z ⊆ FootprintVertices A) → ((FootprintVertices W ⊆
            FootprintVertices B) → (∀ (p₃ : List GaussianInt), (∀ z ∈ p₃, z ∈ FootprintVertices Z
            ∩ FootprintVertices W) → (∀ z ∈ p₃, z ∈ FootprintVertices A ∩ FootprintVertices B)))
            ) := by
  classical
  intro A B Z W hZf hWf p₃ hp₃v z hz
  have hzv := hp₃v z hz
  exact ⟨hZf hzv.1, hWf hzv.2⟩

private theorem qmem :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (q : List GaussianInt), (BoundaryFootprintVertices O = (↑q.toFinset
            : Set GaussianInt)) → (∀ z ∈ q, z ∈ BoundaryFootprintVertices O) ) := by
  classical
  intro O q hqvertices z hz
  rw [hqvertices]
  simpa using hz

private theorem aq :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (O : ProtoTile), ∀ (a : GaussianInt), (a ∈
            BoundaryFootprintVertices X ∧ a ∈ BoundaryFootprintVertices Y ∧ a ∈
            BoundaryFootprintVertices O) → (∀ (q : List GaussianInt), (BoundaryFootprintVertices
            O = (↑q.toFinset : Set GaussianInt)) → (a ∈ q)) ) := by
  classical
  intro X Y O a ha q hqvertices
  have : a ∈ (q.toFinset : Set GaussianInt) := by rw [← hqvertices]; exact ha.2.2
  simpa using this

private theorem bq :
    (by
      classical
      exact
        ∀ (Z : ProtoTile), ∀ (W : ProtoTile), ∀ (O : ProtoTile), ∀ (b : GaussianInt), (b ∈
            BoundaryFootprintVertices Z ∧ b ∈ BoundaryFootprintVertices W ∧ b ∈
            BoundaryFootprintVertices O) → (∀ (q : List GaussianInt), (BoundaryFootprintVertices
            O = (↑q.toFinset : Set GaussianInt)) → (b ∈ q)) ) := by
  classical
  intro Z W O b hb q hqvertices
  have : b ∈ (q.toFinset : Set GaussianInt) := by rw [← hqvertices]; exact hb.2.2
  simpa using this

private theorem S_symm :
    (by
      classical
      exact
        ∀ (O : ProtoTile),
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        ∀ (u : GaussianInt), ∀ (v : GaussianInt), S u v → S v u ) := by
  classical
  intro O S u v huv
  refine ⟨huv.2.1, huv.1, ?_⟩
  simpa [Finset.pair_comm] using huv.2.2

private theorem qchain :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (q : List GaussianInt), ∀ (q₀ : GaussianInt), ∀ (q₁ : GaussianInt),
            (∀ (e : Finset GaussianInt), e ∈ BoundaryFootprintEdges O ↔ e = {q₁, q₀} ∨ ∃ (a :
            GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂ : List GaussianInt), q =
            l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (z : GaussianInt), (z ∈ q) → (z ∈
            BoundaryFootprintVertices O)) → (
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        List.IsChain S q)) ) := by
  classical
  intro O q q₀ q₁ hqedges qmem S
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro u v l r h
  refine ⟨qmem u (by simp [h]), qmem v (by simp [h]), ?_⟩
  apply (hqedges {u, v}).2
  exact Or.inr ⟨u, v, l, r, h, rfl⟩

private theorem qhead_reach :
    (by
      classical
      exact
        ∀ (O : ProtoTile),
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        ∀ (u : GaussianInt), ∀ (l : List GaussianInt), List.IsChain S (u :: l) → ∀ z ∈ u :: l,
            Relation.ReflTransGen S u z ) := by
  classical
  intro O S u l hc
  induction l generalizing u with
  | nil =>
      intro z hz
      have heq : z = u := by simpa using hz
      subst z
      exact .refl
  | cons v l ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact .refl
      · exact (Relation.ReflTransGen.single
          (List.isChain_cons_cons.mp hc).1).trans
          (ih v (List.isChain_cons_cons.mp hc).2 z hz)

private theorem qreverse :
    (by
      classical
      exact
        ∀ (O : ProtoTile),
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        (∀ (u : GaussianInt), ∀ (v : GaussianInt), (S u v) → (S v u)) → (∀ {u : GaussianInt}, ∀
            {v : GaussianInt}, Relation.ReflTransGen S u v → Relation.ReflTransGen S v u) ) := by
  classical
  intro O S S_symm u v h
  induction h with
  | refl => exact .refl
  | @tail c d hcd hstep ih => exact ih.head (S_symm c d hstep)

private theorem qhead :
    (by
      classical
      exact
        ∀ (O : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (q : List GaussianInt), ∀
            (q₀ : GaussianInt), ∀ (q₁ : GaussianInt), (q.Nodup) → (((4 : ℕ) ≤ q.length) →
            ((q.head? = some q₀) → ((q.getLast? = some q₁) → ((BoundaryFootprintVertices O =
            (↑q.toFinset : Set GaussianInt)) → ((∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁
            : List GaussianInt), ∀ (l₂ : List GaussianInt), q = l₁ ++ a :: b :: l₂ →
            FourNeighborAdjacent a b) → ((∀ (e : Finset GaussianInt), e ∈ BoundaryFootprintEdges
            O ↔ e = {q₁, q₀} ∨ ∃ (a : GaussianInt) (b : GaussianInt) (l₁ : List GaussianInt) (l₂
            : List GaussianInt), q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) → ((∀ (z : GaussianInt), (z
            ∈ q) → (z ∈ BoundaryFootprintVertices O)) → ((a ∈ q) → ((b ∈ q) → (
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        (List.IsChain S q) → (∃ c l, q = c :: l))))))))))) ) := by
  classical
  intro O a b q q₀ q₁ hqnd hqlen hqhead hqlast hqvertices hqstep hqedges qmem aq bq S qchain
  cases q with
  | nil => simp at hqhead
  | cons c l => exact ⟨c, l, rfl⟩

private theorem S_to_R :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (O' : ProtoTile), (O.cells ⊆
            A.cells) → ((O'.cells ⊆ B.cells) → ((FootprintVertices O ⊆ FootprintVertices A) →
            ((FootprintVertices O' ⊆ FootprintVertices B) → ((O.cells = O'.cells) → ((∀ (T :
            ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges T) → (e ∈
            FootprintEdges T)) → ((∀ (T : ProtoTile), ∀ (z : GaussianInt), (z ∈
            BoundaryFootprintVertices T) → (z ∈ FootprintVertices T)) → (
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        (∀ (T : ProtoTile), (T.cells ⊆ A.cells) → ((FootprintVertices T ⊆ FootprintVertices A) →
            (∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → (e ∈ FootprintEdges A)))) → ((∀
            (T : ProtoTile), (T.cells ⊆ B.cells) → (∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges T) → (e ∈ FootprintEdges B))) → ((O'.cells.Nonempty) → (
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        ∀ {u : GaussianInt}, ∀ {v : GaussianInt}, S u v → R u v)))))))))) ) := by
  classical
  intro A B O O' hOc hO'c hOf hO'f hcell boundary_edge_footprint boundary_vertex_footprint R
      edge_parent edge_parentB hneO' S u v huv
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hOf (boundary_vertex_footprint O u huv.1),
      hO'f (boundary_vertex_footprint O' u (by
        simpa [BoundaryFootprintVertices, hneO',
          BoundaryFootprintEdges, hcell] using huv.1))⟩
  · exact ⟨hOf (boundary_vertex_footprint O v huv.2.1),
      hO'f (boundary_vertex_footprint O' v (by
        simpa [BoundaryFootprintVertices, hneO',
          BoundaryFootprintEdges, hcell] using huv.2.1))⟩
  · have heO := boundary_edge_footprint O _ huv.2.2
    have heO' : {u, v} ∈ FootprintEdges O' := by
      simpa [FootprintEdges, hcell] using heO
    exact ⟨edge_parent O hOc hOf _ heO,
      edge_parentB O' hO'c _ heO'⟩

private theorem qrouteR :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (O : ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt),
        let R : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ FootprintVertices A ∩ FootprintVertices B ∧
          v ∈ FootprintVertices A ∩ FootprintVertices B ∧
          {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
        let S : GaussianInt → GaussianInt → Prop := fun u v =>
          u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
            {u, v} ∈ BoundaryFootprintEdges O
        (Relation.ReflTransGen S a b) → ((∀ {u : GaussianInt}, ∀ {v : GaussianInt}, (S u v) → (R
            u v)) → (Relation.ReflTransGen R a b)) ) := by
  classical
  intro A B O a b R S qroute S_to_R
  exact Relation.ReflTransGen.mono (fun _ _ hstep => S_to_R hstep)
    a b qroute

end PrecursorWalkGeometry

theorem P4677T2PrecursorWalk :
    ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z :
        ProtoTile), ∀ (W : ProtoTile), ∀ (O : ProtoTile), ∀ (O' : ProtoTile), ∀ (x :
        GaussianInt), ∀ (y : GaussianInt), (X.cells ⊆ A.cells) → ((Z.cells ⊆ A.cells) → ((Y.cells
        ⊆ B.cells) → ((W.cells ⊆ B.cells) → ((O.cells ⊆ A.cells) → ((O'.cells ⊆ B.cells) →
        ((FootprintVertices X ⊆ FootprintVertices A) → ((FootprintVertices Z ⊆ FootprintVertices
        A) → ((FootprintVertices Y ⊆ FootprintVertices B) → ((FootprintVertices W ⊆
        FootprintVertices B) → ((FootprintVertices O ⊆ FootprintVertices A) → ((FootprintVertices
        O' ⊆ FootprintVertices B) → ((O.cells = O'.cells) → ((O.cells = ∅ → O.anchor = O'.anchor)
        → ((O.cells.Nonempty → LatticeTile O) → ((TouchingTriple X Y O) → ((TouchingTriple Z W O)
        → ((x ∈ FootprintVertices X ∩ FootprintVertices Y) → ((y ∈ FootprintVertices Z ∩
        FootprintVertices W) → (∃ p : List GaussianInt,
      p.head? = some x ∧ p.getLast? = some y ∧
      (∀ z ∈ p, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧
      ∀ a b : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        p = l₁ ++ a :: b :: l₂ →
        {a, b} ∈ FootprintEdges A ∩ FootprintEdges B))))))))))))))))))) := by
  intro A B X Y Z W O O' x y hXc hZc hYc hWc hOc hO'c hXf hZf hYf hWf hOf hO'f hcell hanchor
      hdisk hfirst hlast hx hy
-- BODY
  classical
  have boundary_edge_footprint (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T :=
          PrecursorWalkGeometry.boundary_edge_footprint T e he
  have edge_vertex (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) (z : GaussianInt) (hz : z ∈ e) :
      z ∈ FootprintVertices T := PrecursorWalkGeometry.edge_vertex T e he z hz
  have boundary_vertex_footprint (T : ProtoTile) (z : GaussianInt)
      (hz : z ∈ BoundaryFootprintVertices T) : z ∈ FootprintVertices T :=
          PrecursorWalkGeometry.boundary_vertex_footprint boundary_edge_footprint edge_vertex T z hz
  obtain ⟨a, ha, _⟩ := hfirst.2.2.2
  obtain ⟨b, hb, _⟩ := hlast.2.2.2
  have haX : a ∈ FootprintVertices X := boundary_vertex_footprint X a ha.1
  have haY : a ∈ FootprintVertices Y := boundary_vertex_footprint Y a ha.2.1
  have haO : a ∈ FootprintVertices O := boundary_vertex_footprint O a ha.2.2
  have hbZ : b ∈ FootprintVertices Z := boundary_vertex_footprint Z b hb.1
  have hbW : b ∈ FootprintVertices W := boundary_vertex_footprint W b hb.2.1
  have hbO : b ∈ FootprintVertices O := boundary_vertex_footprint O b hb.2.2
  obtain ⟨p₁, hp₁h, hp₁l, hp₁v, hp₁e⟩ :=
    P4677T2TouchingWalk X Y x a hfirst.1 ⟨hx.1, hx.2⟩ ⟨haX, haY⟩
  obtain ⟨p₃, hp₃h, hp₃l, hp₃v, hp₃e⟩ :=
    P4677T2TouchingWalk Z W b y hlast.1 ⟨hbZ, hbW⟩ ⟨hy.1, hy.2⟩
  have hOeq : O.cells = O'.cells := hcell
  let R : GaussianInt → GaussianInt → Prop := fun u v =>
    u ∈ FootprintVertices A ∩ FootprintVertices B ∧
    v ∈ FootprintVertices A ∩ FootprintVertices B ∧
    {u, v} ∈ FootprintEdges A ∩ FootprintEdges B
  have R_symm (u v : GaussianInt) (huv : R u v) : R v u := PrecursorWalkGeometry.R_symm A B u v huv
  have reverse_reach {u v : GaussianInt}
      (h : Relation.ReflTransGen R u v) : Relation.ReflTransGen R v u :=
          PrecursorWalkGeometry.reverse_reach A B R_symm (u := u) (v := v) h
  have head_reach (u : GaussianInt) (l : List GaussianInt)
      (hc : List.IsChain R (u :: l)) :
      ∀ z ∈ u :: l, Relation.ReflTransGen R u z := PrecursorWalkGeometry.head_reach A B u l hc
  have chain_reach {p : List GaussianInt} {u v : GaussianInt}
      (hc : List.IsChain R p) (hh : p.head? = some u)
      (hl : p.getLast? = some v) : Relation.ReflTransGen R u v :=
          PrecursorWalkGeometry.chain_reach A B head_reach (p := p) (u := u) (v := v) hc hh hl
  have edge_parent (T : ProtoTile) (hTc : T.cells ⊆ A.cells)
      (hTf : FootprintVertices T ⊆ FootprintVertices A)
      (e : Finset GaussianInt) (he : e ∈ FootprintEdges T) :
      e ∈ FootprintEdges A := PrecursorWalkGeometry.edge_parent A T hTc hTf e he
  have edge_parentB (T : ProtoTile) (hTc : T.cells ⊆ B.cells)
      (e : Finset GaussianInt) (he : e ∈ FootprintEdges T) :
      e ∈ FootprintEdges B := PrecursorWalkGeometry.edge_parentB B T hTc e he
  have p₁chain : List.IsChain R p₁ := PrecursorWalkGeometry.p₁chain A B X Y hXc hYc hXf hYf p₁
      hp₁v hp₁e edge_parent edge_parentB
  have p₃chain : List.IsChain R p₃ := PrecursorWalkGeometry.p₃chain A B Z W hZc hWc hZf hWf p₃
      hp₃v hp₃e edge_parent edge_parentB
  have p₁mem (z : GaussianInt) (hz : z ∈ p₁) :
      z ∈ FootprintVertices A ∩ FootprintVertices B := PrecursorWalkGeometry.p₁mem A B X Y hXf
          hYf p₁ hp₁v z hz
  have p₃mem (z : GaussianInt) (hz : z ∈ p₃) :
      z ∈ FootprintVertices A ∩ FootprintVertices B := PrecursorWalkGeometry.p₃mem A B Z W hZf
          hWf p₃ hp₃v z hz
  by_cases hneO : O.cells.Nonempty
  · have hneO' : O'.cells.Nonempty := by rw [← hcell]; exact hneO
    have hcycle := LatticeTileBoundarySimpleGridCycle O (hdisk hneO)
    rcases hcycle with ⟨q, q₀, q₁, hqnd, hqlen, hqhead, hqlast,
      hqvertices, hqclose, hqstep, hqedges⟩
    have qmem (z : GaussianInt) (hz : z ∈ q) :
        z ∈ BoundaryFootprintVertices O := PrecursorWalkGeometry.qmem O q hqvertices z hz
    have aq : a ∈ q := PrecursorWalkGeometry.aq X Y O a ha q hqvertices
    have bq : b ∈ q := PrecursorWalkGeometry.bq Z W O b hb q hqvertices
    let S : GaussianInt → GaussianInt → Prop := fun u v =>
      u ∈ BoundaryFootprintVertices O ∧ v ∈ BoundaryFootprintVertices O ∧
        {u, v} ∈ BoundaryFootprintEdges O
    have S_symm (u v : GaussianInt) (huv : S u v) : S v u := PrecursorWalkGeometry.S_symm O u v huv
    have qchain : List.IsChain S q := PrecursorWalkGeometry.qchain O q q₀ q₁ hqedges qmem
    have qhead_reach (u : GaussianInt) (l : List GaussianInt)
        (hc : List.IsChain S (u :: l)) :
        ∀ z ∈ u :: l, Relation.ReflTransGen S u z := PrecursorWalkGeometry.qhead_reach O u l hc
    have qreverse {u v : GaussianInt}
        (h : Relation.ReflTransGen S u v) : Relation.ReflTransGen S v u :=
            PrecursorWalkGeometry.qreverse O S_symm (u := u) (v := v) h
    have qhead : ∃ c l, q = c :: l := PrecursorWalkGeometry.qhead O a b q q₀ q₁ hqnd hqlen hqhead
        hqlast hqvertices hqstep hqedges qmem aq bq qchain
    rcases qhead with ⟨c, l, rfl⟩
    have hca : c = q₀ := by simpa using hqhead
    subst c
    have amem : a ∈ q₀ :: l := aq
    have bmem : b ∈ q₀ :: l := bq
    have qroute : Relation.ReflTransGen S a b :=
      (qreverse (qhead_reach q₀ l qchain a amem)).trans
        (qhead_reach q₀ l qchain b bmem)
    have S_to_R {u v : GaussianInt} (huv : S u v) : R u v := PrecursorWalkGeometry.S_to_R A B O
        O' hOc hO'c hOf hO'f hcell boundary_edge_footprint boundary_vertex_footprint edge_parent
        edge_parentB hneO' (u := u) (v := v) huv
    have qrouteR : Relation.ReflTransGen R a b := PrecursorWalkGeometry.qrouteR A B O a b qroute
        S_to_R
    have hroute := (chain_reach p₁chain hp₁h hp₁l).trans
      (qrouteR.trans (chain_reach p₃chain hp₃h hp₃l))
    obtain ⟨p, hc, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hroute
    refine ⟨x :: p, rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p), hlast]
    · have inside : ∀ z ∈ x :: p, z ∈ FootprintVertices A ∩ FootprintVertices B :=
        hc.induction (fun z => z ∈ FootprintVertices A ∩ FootprintVertices B)
          (x :: p) (fun {_ _} h _ => h.2.1)
          (fun _ => ⟨hXf hx.1, hYf hx.2⟩)
      intro z hz
      exact inside z hz
    · intro u v l r h
      have hed := (List.isChain_iff_forall_rel_of_append_cons_cons.mp hc h).2.2
      exact hed
  · have haeq : a = O.anchor := by simpa [FootprintVertices, hneO] using haO
    have hbeq : b = O.anchor := by simpa [FootprintVertices, hneO] using hbO
    have hab : a = b := haeq.trans hbeq.symm
    have middle : Relation.ReflTransGen R a b := by
      rw [hab]
    have hroute := (chain_reach p₁chain hp₁h hp₁l).trans
      (middle.trans (chain_reach p₃chain hp₃h hp₃l))
    obtain ⟨p, hc, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hroute
    refine ⟨x :: p, rfl, ?_, ?_, ?_⟩
    · rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x p), hlast]
    · have inside : ∀ z ∈ x :: p, z ∈ FootprintVertices A ∩ FootprintVertices B :=
        hc.induction (fun z => z ∈ FootprintVertices A ∩ FootprintVertices B)
          (x :: p) (fun {_ _} h _ => h.2.1)
          (fun _ => ⟨hXf hx.1, hYf hx.2⟩)
      intro z hz
      exact inside z hz
    · intro u v l r h
      exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp hc h).2.2

end ApollonianSuperharmonic

end
