/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.LatticeTile
public import LeanPool.ApollonianSuperharmonic.OdometerCompatibility
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.P3221T2ClosedWalkCirculation
public import LeanPool.ApollonianSuperharmonic.P3221T2ConnectedPathIntegration

-- [TABLET NODE: OdometerGluing]

/-!
# OdometerGluing

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OdometerGluingProof

private theorem increment_eq :
    (by
      classical
      exact
        ∀ {ι : Type}, ∀ (h : ι → PartialOdometer), (∀ i, ∀ j, OdometerCompatibility (h i) (h j))
            → (∀ (i : ι), ∀ (j : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain)
            → ((b ∈ (h i).domain) → ((a ∈ (h j).domain) → ((b ∈ (h j).domain) → ((h i).value b -
            (h i).value a = (h j).value b - (h j).value a))))) ) := by
  classical
  intro ι h hcompat i j a b hai hbi haj hbj
  rcases hcompat i j with hdis | ⟨c, hc⟩
  · exact (Set.disjoint_left.mp hdis hai haj).elim
  · have ha := hc a hai haj
    have hb := hc b hbi hbj
    omega

private theorem adjacent_symm :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a) ) := by
  classical
  intro a b hab
  rcases hab with rfl | rfl | rfl | rfl
  all_goals simp [FourNeighborAdjacent, Zsqrtd.ext_iff]

private theorem adjacent_irrefl :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ¬ FourNeighborAdjacent a a ) := by
  classical
  intro a hab
  rcases hab with hab | hab | hab | hab
  all_goals
    have hr := congrArg Zsqrtd.re hab
    have hi := congrArg Zsqrtd.im hab
    simp at hr hi
  all_goals omega

private theorem corner :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ T.cells) → (∀ (a : GaussianInt), (a = x ∨ a
            = x + 1 ∨ a = x + ⟨0, 1⟩ ∨
            a = x + 1 + ⟨0, 1⟩) → (a ∈ FootprintVertices T)) ) := by
  classical
  intro T x hx a ha
  simp only [FootprintVertices, ite_eq_left (show T.cells.Nonempty from ⟨x, hx⟩)]
  exact ⟨x, hx, ha⟩

private theorem edge_vertices :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ T.cells) → (∀ (a : GaussianInt), (a = x ∨ a
            = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 + ⟨0, 1⟩) → (a ∈ FootprintVertices T))) → (∀ (T
            : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, b} : Finset
            GaussianInt) ∈ FootprintEdges T) → (a ∈ FootprintVertices T ∧ b ∈ FootprintVertices
            T)) ) := by
  classical
  intro corner T a b he
  obtain ⟨s, hs, he⟩ := he
  have endpoint (v : GaussianInt) (hv : v ∈ ({a, b} : Finset GaussianInt)) :
      v ∈ FootprintVertices T := by
    apply corner T s hs v
    rcases he with he | he | he | he <;> rw [he] at hv
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    all_goals tauto
  exact ⟨endpoint a (by simp), endpoint b (by simp)⟩

private theorem footprint_reachable :
    (by
      classical
      exact
        (∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)) → (∀ (W : ProtoTile), (LatticeTile W) → (∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (a ∈ FootprintVertices W) → ((b ∈
            FootprintVertices W) → (Relation.ReflTransGen (fun u v => FourNeighborAdjacent u v ∧
            ({u, v} : Finset GaussianInt) ∈ FootprintEdges W) a b)))) ) := by
  classical
  intro adjacent_symm W hW a b ha hb
  let R (u v : GaussianInt) : Prop := FourNeighborAdjacent u v ∧
    ({u, v} : Finset GaussianInt) ∈ FootprintEdges W
  let reach := Relation.ReflTransGen R
  have reverse {u v : GaussianInt} (h : reach u v) : reach v u := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h he ih =>
        exact (Relation.ReflTransGen.single
          ⟨adjacent_symm _ _ he.1, by simpa [Finset.pair_comm] using he.2⟩).trans ih
  have bottom (s : GaussianInt) (hs : s ∈ W.cells) : reach s (s + 1) :=
    Relation.ReflTransGen.single ⟨Or.inl rfl, ⟨s, hs, Or.inl rfl⟩⟩
  have left (s : GaussianInt) (hs : s ∈ W.cells) : reach s (s + ⟨0, 1⟩) :=
    Relation.ReflTransGen.single ⟨Or.inr (Or.inr (Or.inl rfl)),
      ⟨s, hs, Or.inr (Or.inl rfl)⟩⟩
  have right (s : GaussianInt) (hs : s ∈ W.cells) :
      reach (s + 1) (s + 1 + ⟨0, 1⟩) :=
    Relation.ReflTransGen.single ⟨Or.inr (Or.inr (Or.inl rfl)),
      ⟨s, hs, Or.inr (Or.inr (Or.inl rfl))⟩⟩
  have to_corner (s : GaussianInt) (hs : s ∈ W.cells) (v : GaussianInt)
      (hv : v = s ∨ v = s + 1 ∨ v = s + ⟨0, 1⟩ ∨ v = s + 1 + ⟨0, 1⟩) :
      reach s v := by
    rcases hv with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact bottom s hs
    · exact left s hs
    · exact (bottom s hs).trans (right s hs)
  have cell_step (u v : GaussianInt) (hu : u ∈ W.cells) (hv : v ∈ W.cells)
      (huv : FourNeighborAdjacent u v) : reach u v := by
    rcases huv with rfl | rfl | rfl | rfl
    · exact bottom u hu
    · simpa using reverse (bottom (u - 1) hv)
    · exact left u hu
    · simpa using reverse (left (u - ⟨0, 1⟩) hv)
  have chain_reach : ∀ (s : GaussianInt) (l : List GaussianInt),
      (∀ v ∈ s :: l, v ∈ W.cells) → List.IsChain FourNeighborAdjacent (s :: l) →
      ∀ t ∈ s :: l, reach s t := by
    intro s l
    induction l generalizing s with
    | nil =>
        intro hcells hchain t ht
        rcases List.mem_singleton.mp ht with rfl
        exact Relation.ReflTransGen.refl
    | cons t l ih =>
        intro hcells hchain v hv
        have hst := (List.isChain_cons.mp hchain).1 t (by simp)
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Relation.ReflTransGen.refl
        · exact (cell_step s t (hcells s (by simp)) (hcells t (by simp)) hst).trans
            (ih t (fun w hw => hcells w (by simp [hw]))
              (List.isChain_cons.mp hchain).2 v hv)
  have hcells := (LatticeTileGridStructure W hW).1
  have hnonempty : W.cells.Nonempty := hcells.1
  simp only [FootprintVertices, ite_eq_left hnonempty] at ha hb
  obtain ⟨s, hs, has⟩ := ha
  obtain ⟨t, ht, hbt⟩ := hb
  obtain ⟨p, hhead, hlast, hp, hsteps⟩ := hcells.2 s hs t ht
  have hst : reach s t := by
    have hchain := List.isChain_iff_forall_rel_of_append_cons_cons.mpr hsteps
    cases p with
    | nil => simp at hhead
    | cons v l =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst v
        exact chain_reach s l hp hchain t
          (List.mem_of_mem_getLast? (by simp [hlast]))
  exact (reverse (to_corner s hs a has)).trans (hst.trans (to_corner t ht b hbt))

private theorem footprint_constant :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ T.cells) → (∀ (a : GaussianInt), (a = x ∨ a
            = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 + ⟨0, 1⟩) → (a ∈ FootprintVertices T))) → ((∀ (T
            : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (({a, b} : Finset
            GaussianInt) ∈ FootprintEdges T) → (a ∈ FootprintVertices T ∧ b ∈ FootprintVertices
            T)) → ((∀ (W : ProtoTile), (LatticeTile W) → (∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (a ∈ FootprintVertices W) → ((b ∈ FootprintVertices W) →
            (Relation.ReflTransGen (fun u v => FourNeighborAdjacent u v ∧ ({u, v} : Finset
            GaussianInt) ∈ FootprintEdges W) a b)))) → (∀ (W : ProtoTile), (LatticeTile W) → (∀
            (F : GaussianInt → ℤ), (∀ a, ∀ b, FourNeighborAdjacent a b →
            ({a, b} : Finset GaussianInt) ∈ FootprintEdges W → F a = F b) → (∃ c : ℤ, ∀ x, x ∈
                FootprintVertices W → F x = c))))) ) := by
  classical
  intro corner edge_vertices footprint_reachable W hW F hF
  obtain ⟨s, hs⟩ := (LatticeTileGridStructure W hW).1.1
  have hsf : s ∈ FootprintVertices W := corner W s hs s (by simp)
  refine ⟨F s, ?_⟩
  intro x hx
  have hr := footprint_reachable W hW s x hsf hx
  have heq : F s = F x := by
    induction hr with
    | refl => rfl
    | tail hr hstep ih =>
        exact (ih (edge_vertices W _ _ hstep.2).1).trans
          (hF _ _ hstep.1 hstep.2)
  exact heq.symm

private theorem walk_sum :
    (by
      classical
      exact
        ∀ {α : Type}, ∀ (G : SimpleGraph α), ∀ (f : α → GaussianInt), ∀ (D : GaussianInt →
            GaussianInt → ℤ), ∀ {a : α}, ∀ {b : α}, ∀ (p : G.Walk a b), (p.darts.map (fun d => D
            (f d.fst) (f d.snd))).sum = (List.zipWith D (p.support.map f) (p.support.map
            f).tail).sum ) := by
  classical
  intro α G f D a b p
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      cases p with
      | nil => simp
      | cons hbc q =>
          simpa only [SimpleGraph.Walk.darts_cons, List.map_cons, List.sum_cons,
            SimpleGraph.Walk.support_cons, List.tail_cons, List.zipWith_cons_cons]
            using congrArg (fun z => D (f a) (f b) + z) ih

private theorem dmemberAt297 :
    (by
      classical
      exact
        (∀ {ι : Type}, ∀ (h : ι → PartialOdometer), (∀ i, ∀ j, OdometerCompatibility (h i) (h j))
            → (∀ (i : ι), ∀ (j : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain)
            → ((b ∈ (h i).domain) → ((a ∈ (h j).domain) → ((b ∈ (h j).domain) → ((h i).value b -
            (h i).value a = (h j).value b - (h j).value a)))))) → (∀ (n : ℕ), ∀ (h : Fin n →
            PartialOdometer), (∀ (i : Fin n), ∀ (j : Fin n), OdometerCompatibility (h i) (h j)) → (
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        ∀ (i : Fin n), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a)))) ) := by
  classical
  intro increment_eq n h hcompat covered D i a b ha hb
  have hc : covered a b := ⟨i, ha, hb⟩
  simp only [D, dite_eq_left hc]
  exact increment_eq h hcompat (Classical.choose hc) i a b
    (Classical.choose_spec hc).1 (Classical.choose_spec hc).2 ha hb

private theorem edge_coverAt304 :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ T.cells) → (∀ (a : GaussianInt), (a = x ∨ a
            = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 + ⟨0, 1⟩) → (a ∈ FootprintVertices T))) → (∀ (n
            : ℕ), ∀ (T : ProtoTile), ∀ (U : Fin n → ProtoTile), ∀ (h : Fin n → PartialOdometer),
            (∀ (i : Fin n), (↑(h i).domain : Set GaussianInt) = FootprintVertices (U i)) → ((∀ (x
            : LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin n), x ∈ (U i).cells) → (
        let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
          ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (E a b) → (covered a b)))) ) := by
  classical
  intro corner n T U h hdom hcells E covered a b hab
  obtain ⟨s, hs, he⟩ := hab.2
  obtain ⟨i, hsi⟩ := (hcells s).1 hs
  have hav : a = s ∨ a = s + 1 ∨ a = s + ⟨0, 1⟩ ∨ a = s + 1 + ⟨0, 1⟩ := by
    have hamem : a ∈ ({a, b} : Finset GaussianInt) := by simp
    rcases he with he | he | he | he <;> rw [he] at hamem
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hamem
    all_goals tauto
  have hbv : b = s ∨ b = s + 1 ∨ b = s + ⟨0, 1⟩ ∨ b = s + 1 + ⟨0, 1⟩ := by
    have hbmem : b ∈ ({a, b} : Finset GaussianInt) := by simp
    rcases he with he | he | he | he <;> rw [he] at hbmem
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton] at hbmem
    all_goals tauto
  refine ⟨i, ?_, ?_⟩
  · change a ∈ ((h i).domain : Set GaussianInt)
    rw [hdom i]
    exact corner (U i) s hsi a hav
  · change b ∈ ((h i).domain : Set GaussianInt)
    rw [hdom i]
    exact corner (U i) s hsi b hbv

private theorem hantiAt324 :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (T : ProtoTile), ∀ (h : Fin n → PartialOdometer),
        let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
          ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (i : Fin n), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a))) → ((∀ (a : GaussianInt), ∀ (b
            : GaussianInt), (E a b) → (covered a b)) → (∀ a, ∀ b, E a b → D b a = -D a b)) ) := by
  classical
  intro n T h E covered D dmember edge_cover a b hab
  obtain ⟨i, ha, hb⟩ := edge_cover a b hab
  rw [dmember i b a hb ha, dmember i a b ha hb]
  omega

private theorem hflatAt329 :
    (by
      classical
      exact
        (∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈ T.cells) → (∀ (a : GaussianInt), (a = x ∨ a
            = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 + ⟨0, 1⟩) → (a ∈ FootprintVertices T))) → (∀ (n
            : ℕ), ∀ (T : ProtoTile), ∀ (U : Fin n → ProtoTile), ∀ (h : Fin n → PartialOdometer),
            (∀ (i : Fin n), (↑(h i).domain : Set GaussianInt) = FootprintVertices (U i)) → ((∀ (x
            : LatticeCell), x ∈ T.cells ↔ ∃ (i : Fin n), x ∈ (U i).cells) → (
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (i : Fin n), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a))) → (∀ x ∈ T.cells, D x (x + 1)
            + D (x + 1) (x + 1 + ⟨0, 1⟩) + D (x + 1 + ⟨0, 1⟩) (x + ⟨0, 1⟩) + D (x + ⟨0, 1⟩) x =
            0)))) ) := by
  classical
  intro corner n T U h hdom hcells covered D dmember x hx
  obtain ⟨i, hxi⟩ := (hcells x).1 hx
  have hc (a : GaussianInt) (ha : a = x ∨ a = x + 1 ∨
      a = x + ⟨0, 1⟩ ∨ a = x + 1 + ⟨0, 1⟩) : a ∈ (h i).domain := by
    change a ∈ ((h i).domain : Set GaussianInt)
    rw [hdom i]
    exact corner (U i) x hxi a ha
  rw [dmember i x (x + 1) (hc x (by simp)) (hc (x + 1) (by simp)),
    dmember i (x + 1) (x + 1 + ⟨0, 1⟩)
      (hc (x + 1) (by simp)) (hc (x + 1 + ⟨0, 1⟩) (by simp)),
    dmember i (x + 1 + ⟨0, 1⟩) (x + ⟨0, 1⟩)
      (hc (x + 1 + ⟨0, 1⟩) (by simp)) (hc (x + ⟨0, 1⟩) (by simp)),
    dmember i (x + ⟨0, 1⟩) x (hc (x + ⟨0, 1⟩) (by simp)) (hc x (by simp))]
  omega

private theorem hconnAt356 :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a), ∀ (corner : ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈
            T.cells) → (∀ (a : GaussianInt), (a = x ∨ a = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 +
            ⟨0, 1⟩) → (a ∈ FootprintVertices T))), (∀ (T : ProtoTile), ∀ (a : GaussianInt), ∀ (b
                : GaussianInt), (({a, b} : Finset GaussianInt) ∈ FootprintEdges T)
            → (a ∈ FootprintVertices T ∧ b ∈ FootprintVertices T)) → ((∀ (W : ProtoTile),
                (LatticeTile W) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈
            FootprintVertices W) → ((b ∈ FootprintVertices W) → (Relation.ReflTransGen (fun u v
            => FourNeighborAdjacent u v ∧ ({u, v} : Finset GaussianInt) ∈ FootprintEdges W) a
            b)))) → (∀ (T : ProtoTile), (LatticeTile T) → (
        let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
          ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
        let G : SimpleGraph {x // x ∈ FootprintVertices T} := {
          Adj := fun a b => E a.val b.val
          symm := ⟨by
            intro a b hab
            exact ⟨adjacent_symm a b hab.1, by simpa [Finset.pair_comm] using hab.2⟩⟩
          loopless := ⟨by intro a ha; exact adjacent_irrefl a ha.1⟩ }
        ∀ (z : LatticeCell), ∀ (hz : z ∈ (↑T.cells : Set LatticeCell)),
        let base : {x // x ∈ FootprintVertices T} := ⟨z, corner T z hz z (by simp)⟩
        ∀ x, Nonempty (G.Walk base x))))) := by
  classical
  intro adjacent_symm adjacent_irrefl corner edge_vertices footprint_reachable T hT E G z hz base
  have lift : ∀ {a b}, Relation.ReflTransGen E a b →
      ∀ (ha : a ∈ FootprintVertices T) (hb : b ∈ FootprintVertices T),
      Nonempty (G.Walk ⟨a, ha⟩ ⟨b, hb⟩) := by
    intro a b hr
    induction hr with
    | refl => intro ha hb; exact ⟨SimpleGraph.Walk.nil⟩
    | @tail b c hr he ih =>
        intro ha hc
        have hb := (edge_vertices T b c he.2).1
        obtain ⟨p⟩ := ih ha hb
        exact ⟨p.concat he⟩
  intro x
  exact lift (footprint_reachable T hT base x base.property x.property)
    base.property x.property

private theorem hclosedAt371 :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a), (∀ {α : Type}, ∀ (G : SimpleGraph α), ∀ (f : α →
                GaussianInt), ∀ (D : GaussianInt → GaussianInt → ℤ), ∀ {a : α}, ∀ {b : α}, ∀ (p :
                G.Walk a b), (p.darts.map (fun d => D (f d.fst) (f d.snd))).sum = (List.zipWith D
            (p.support.map f) (p.support.map f).tail).sum) → (∀ (n : ℕ), ∀ (T : ProtoTile), ∀ (h
                : Fin n → PartialOdometer),
        let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
          ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (p : List GaussianInt), ∀ (x : GaussianInt), p.head? = some x →
            p.getLast? = some x → List.IsChain (fun (a b : LatticeCell) => FourNeighborAdjacent a
            b ∧ {a, b} ∈ FootprintEdges T) p → (List.zipWith D p p.tail).sum = (0 : ℤ)) → (
        let G : SimpleGraph {x // x ∈ FootprintVertices T} := {
          Adj := fun a b => E a.val b.val
          symm := ⟨by
            intro a b hab
            exact ⟨adjacent_symm a b hab.1, by simpa [Finset.pair_comm] using hab.2⟩⟩
          loopless := ⟨by intro a ha; exact adjacent_irrefl a ha.1⟩ }
        ∀ x, ∀ (p : G.Walk x x), (p.darts.map (fun d => D d.fst.val d.snd.val)).sum = 0))) := by
  classical
  intro adjacent_symm adjacent_irrefl walk_sum n T h E covered D hcirculation G x p
  rw [walk_sum G Subtype.val D p]
  apply hcirculation (p.support.map Subtype.val) x.val
  · rw [List.head?_map, List.head?_eq_some_head p.support_ne_nil]
    simp
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast p.support_ne_nil]
    simp
  · exact List.isChain_map_of_isChain Subtype.val
      (fun a b hab => hab) p.isChain_adj_support

private theorem hdomain :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (z : LatticeCell), (z ∈ (↑T.cells : Set LatticeCell)) → (
        let dom : Finset GaussianInt := T.cells.biUnion (fun x =>
          {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
        (dom : Set GaussianInt) = FootprintVertices T) ) := by
  classical
  intro T z hz dom
  ext x
  simp only [dom, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton, FootprintVertices, ite_eq_left (show T.cells.Nonempty from ⟨z, hz⟩)]
  rfl

private theorem hx' :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
        let dom : Finset GaussianInt := T.cells.biUnion (fun x =>
          {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
        ((dom : Set GaussianInt) = FootprintVertices T) → (∀ (x : GaussianInt), (x ∉ dom) → (x ∉
            FootprintVertices T)) ) := by
  classical
  intro T dom hdomain x hx
  rw [← hdomain]
  exact hx

private theorem hgcompat :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a), ∀ (corner : ∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈
            T.cells) → (∀ (a : GaussianInt), (a = x ∨ a = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 +
            ⟨0, 1⟩) → (a ∈ FootprintVertices T))), ∀ (edge_vertices : ∀ (T : ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (({a, b} : Finset GaussianInt) ∈ FootprintEdges T)
            → (a ∈ FootprintVertices T ∧ b ∈ FootprintVertices T)), ∀ (footprint_constant : ∀ (W
            : ProtoTile), (LatticeTile W) → (∀ (F : GaussianInt → ℤ), (∀ a, ∀ b,
            FourNeighborAdjacent a b → ({a, b} : Finset GaussianInt) ∈ FootprintEdges W → F a = F
            b) → (∃ c : ℤ, ∀ x, x ∈ FootprintVertices W → F x = c))), ∀ (n : ℕ), ∀ (T :
            ProtoTile), ∀ (U : Fin n → ProtoTile), ∀ (h : Fin n → PartialOdometer), ∀ (hU : ∀ (i
            : Fin n), LatticeTile (U i)), ∀ (hdom : ∀ (i : Fin n), (↑(h i).domain : Set
            GaussianInt) = FootprintVertices (U i)), ∀ (hcells : ∀ (x : LatticeCell), x ∈ T.cells
            ↔ ∃ (i : Fin n), x ∈ (U i).cells), ∀ (hverts : ∀ (x : GaussianInt), x ∈
            FootprintVertices T ↔ ∃ (i : Fin n), x ∈ (h i).domain),
        let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
          ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        ∀ (dmember : ∀ (i : Fin n), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain)
            → ((b ∈ (h i).domain) → (D a b = (h i).value b - (h i).value a))),
        let G : SimpleGraph {x // x ∈ FootprintVertices T} := {
          Adj := fun a b => E a.val b.val
          symm := ⟨by
            intro a b hab
            exact ⟨adjacent_symm a b hab.1, by simpa [Finset.pair_comm] using hab.2⟩⟩
          loopless := ⟨by intro a ha; exact adjacent_irrefl a ha.1⟩ }
        ∀ (z : LatticeCell), ∀ (hz : z ∈ (↑T.cells : Set LatticeCell)), ∀ (f :
            { x : GaussianInt // x ∈ FootprintVertices T } → ℤ), ∀ (hfedge : ∀ (a :
            { x : GaussianInt // x ∈ FootprintVertices T }), ∀ (b :
            { x : GaussianInt // x ∈ FootprintVertices T }), G.Adj a b → f b - f a = D (↑a :
            GaussianInt) (↑b : GaussianInt)),
        let dom : Finset GaussianInt := T.cells.biUnion (fun x =>
          {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
        ∀ (hdomain : (dom : Set GaussianInt) = FootprintVertices T),
        let g : PartialOdometer := {
          domain := dom
          value := fun x => if hx : x ∈ FootprintVertices T then f ⟨x, hx⟩ else 0
          value_outside := by
            intro x hx
            have hx' : x ∉ FootprintVertices T := by
              rw [← hdomain]
              exact hx
            simp [hx'] }
        (∀ (x : {x // x ∈ FootprintVertices T}), g.value x = f x) → (∀ i, OdometerCompatibility g
            (h i)) ) := by
  classical
  intro adjacent_symm adjacent_irrefl corner edge_vertices footprint_constant n T U h hU hdom
      hcells hverts E covered D dmember G z hz f hfedge dom hdomain g hgvalue i
  obtain ⟨c, hc⟩ := footprint_constant (U i) (hU i)
    (fun x => g.value x - (h i).value x) (by
      intro a b hadj he
      have hends := edge_vertices (U i) a b he
      have hai : a ∈ (h i).domain := by
        change a ∈ ((h i).domain : Set GaussianInt)
        rw [hdom i]
        exact hends.1
      have hbi : b ∈ (h i).domain := by
        change b ∈ ((h i).domain : Set GaussianInt)
        rw [hdom i]
        exact hends.2
      have haT := (hverts a).2 ⟨i, hai⟩
      have hbT := (hverts b).2 ⟨i, hbi⟩
      have heT : ({a, b} : Finset GaussianInt) ∈ FootprintEdges T := by
        obtain ⟨s, hs, hes⟩ := he
        exact ⟨s, (hcells s).2 ⟨i, hs⟩, hes⟩
      have hed := hfedge ⟨a, haT⟩ ⟨b, hbT⟩ ⟨hadj, heT⟩
      have hga := hgvalue ⟨a, haT⟩
      have hgb := hgvalue ⟨b, hbT⟩
      rw [dmember i a b hai hbi] at hed
      dsimp only at hed hga hgb ⊢
      omega)
  apply Or.inr
  refine ⟨-c, ?_⟩
  intro x hxg hxi
  have hxfoot : x ∈ FootprintVertices (U i) := by
    rw [← hdom i]
    exact hxi
  have hxc := hc x hxfoot
  change g.value x - (h i).value x = c at hxc
  omega

private theorem hg'edge :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a), (∀ (T : ProtoTile), ∀ (x : GaussianInt), (x ∈
            T.cells) → (∀ (a : GaussianInt), (a = x ∨ a = x + 1 ∨ a = x + ⟨0, 1⟩ ∨ a = x + 1 +
            ⟨0, 1⟩) → (a ∈ FootprintVertices T))) → (∀ (n : ℕ), ∀ (T : ProtoTile), ∀ (h : Fin n →
            PartialOdometer),
        let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
          ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (i : Fin n), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain)
            → ((b ∈ (h i).domain) → (D a b = (h i).value b - (h i).value a))) → ((∀ (a :
                GaussianInt), ∀ (b : GaussianInt), (E a b) → (covered a b)) → (
        let G : SimpleGraph {x // x ∈ FootprintVertices T} := {
          Adj := fun a b => E a.val b.val
          symm := ⟨by
            intro a b hab
            exact ⟨adjacent_symm a b hab.1, by simpa [Finset.pair_comm] using hab.2⟩⟩
          loopless := ⟨by intro a ha; exact adjacent_irrefl a ha.1⟩ }
        ∀ (z : LatticeCell), (z ∈ (↑T.cells : Set LatticeCell)) →
            (({ x : GaussianInt // x ∈ FootprintVertices T } → ℤ) → (∀ (g' : PartialOdometer),
                ((↑g'.domain : Set GaussianInt) = FootprintVertices T) → ((∀ (i : Fin n),
                OdometerCompatibility g' (h i)) → (∀ a, ∀ b, G.Adj a b → g'.value b - g'.value a = D
            a b)))))))) := by
  classical
  intro adjacent_symm adjacent_irrefl corner n T h E covered D dmember edge_cover G z hz f g'
      hg'dom hg'compat a b hab
  obtain ⟨i, hai, hbi⟩ := edge_cover a b hab
  have hga : a.val ∈ g'.domain := by
    change a.val ∈ (g'.domain : Set GaussianInt)
    rw [hg'dom]
    exact a.property
  have hgb : b.val ∈ g'.domain := by
    change b.val ∈ (g'.domain : Set GaussianInt)
    rw [hg'dom]
    exact b.property
  rcases hg'compat i with hd | ⟨c, hc⟩
  · exact (Set.disjoint_left.mp hd hga hai).elim
  · have hca := hc a hga hai
    have hcb := hc b hgb hbi
    rw [dmember i a b hai hbi]
    omega

private theorem dmemberAt470 :
    (by
      classical
      exact
        (∀ {ι : Type}, ∀ (h : ι → PartialOdometer), (∀ i, ∀ j, OdometerCompatibility (h i) (h j))
            → (∀ (i : ι), ∀ (j : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain)
            → ((b ∈ (h i).domain) → ((a ∈ (h j).domain) → ((b ∈ (h j).domain) → ((h i).value b -
            (h i).value a = (h j).value b - (h j).value a)))))) → (∀ (ι : Type), ∀ (h : ι →
            PartialOdometer), (∀ (i : ι), ∀ (j : ι), OdometerCompatibility (h i) (h j)) → (
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        ∀ (i : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a)))) ) := by
  classical
  intro increment_eq ι h hcompat covered D i a b ha hb
  have hc : covered a b := ⟨i, ha, hb⟩
  simp only [D, dite_eq_left hc]
  exact increment_eq h hcompat (Classical.choose hc) i a b
    (Classical.choose_spec hc).1 (Classical.choose_spec hc).2 ha hb

private theorem edge_coverAt477 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (h : ι → PartialOdometer), (∀ (x : GaussianInt), ∃ (i : ι), x ∈ (h
            i).domain ∧ x + (1 : GaussianInt) ∈ (h i).domain ∧ x + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ (h i).domain ∧ x + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ (h i).domain) → (
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) → (covered a b)) )
            := by
  classical
  intro ι h hcover covered a b hab
  rcases hab with rfl | rfl | rfl | rfl
  · obtain ⟨i, h0, h1, hi, h1i⟩ := hcover a
    exact ⟨i, h0, h1⟩
  · obtain ⟨i, h0, h1, hi, h1i⟩ := hcover (a - 1)
    exact ⟨i, by simpa using h1, h0⟩
  · obtain ⟨i, h0, h1, hi, h1i⟩ := hcover a
    exact ⟨i, h0, hi⟩
  · obtain ⟨i, h0, h1, hi, h1i⟩ := hcover (a - ⟨0, 1⟩)
    exact ⟨i, by simpa using hi, h0⟩

private theorem hantiAt488 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (h : ι → PartialOdometer),
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (i : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a))) → ((∀ (a : GaussianInt), ∀ (b
            : GaussianInt), (FourNeighborAdjacent a b) → (covered a b)) → (∀ a, ∀ b,
            FourNeighborAdjacent a b → D b a = -D a b)) ) := by
  classical
  intro ι h covered D dmember edge_cover a b hab
  obtain ⟨i, ha, hb⟩ := edge_cover a b hab
  rw [dmember i b a hb ha, dmember i a b ha hb]
  omega

private theorem hflatAt493 :
    (by
      classical
      exact
        ∀ (ι : Type), ∀ (h : ι → PartialOdometer), (∀ (x : GaussianInt), ∃ (i : ι), x ∈ (h
            i).domain ∧ x + (1 : GaussianInt) ∈ (h i).domain ∧ x + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ (h i).domain ∧ x + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ (h i).domain) → (
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (i : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a))) → (∀ x, D x (x + 1) + D (x +
            1) (x + 1 + ⟨0, 1⟩) + D (x + 1 + ⟨0, 1⟩) (x + ⟨0, 1⟩) + D (x + ⟨0, 1⟩) x = 0)) ) := by
  classical
  intro ι h hcover covered D dmember x
  obtain ⟨i, h0, h1, hi, h1i⟩ := hcover x
  rw [dmember i x (x + 1) h0 h1,
    dmember i (x + 1) (x + 1 + ⟨0, 1⟩) h1 h1i,
    dmember i (x + 1 + ⟨0, 1⟩) (x + ⟨0, 1⟩) h1i hi,
    dmember i (x + ⟨0, 1⟩) x hi h0]
  omega

private theorem hconnAt508 :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a),
        let G : SimpleGraph GaussianInt := {
          Adj := FourNeighborAdjacent
          symm := ⟨fun {a b} => adjacent_symm a b⟩
          loopless := ⟨fun {a} => adjacent_irrefl a⟩ }
        ∀ x, Nonempty (G.Walk 0 x) ) := by
  classical
  intro adjacent_symm adjacent_irrefl G
  have horizontal (m : ℤ) : G.Reachable 0 ⟨m, 0⟩ := by
    refine Int.inductionOn' m 0 ?_ ?_ ?_
    · exact SimpleGraph.Reachable.refl 0
    · intro k hk ih
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      exact Or.inl (by apply Zsqrtd.ext <;> simp)
    · intro k hk ih
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      exact Or.inr (Or.inl (by apply Zsqrtd.ext <;> simp))
  intro x
  change G.Reachable 0 ⟨x.re, x.im⟩
  refine Int.inductionOn' x.im 0 (horizontal x.re) ?_ ?_
  · intro k hk ih
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    exact Or.inr (Or.inr (Or.inl (by apply Zsqrtd.ext <;> simp)))
  · intro k hk ih
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    exact Or.inr (Or.inr (Or.inr (by apply Zsqrtd.ext <;> simp)))

private theorem hclosedAt527 :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a), (∀ {α : Type}, ∀ (G : SimpleGraph α), ∀ (f : α →
            GaussianInt), ∀ (D : GaussianInt → GaussianInt → ℤ), ∀ {a : α}, ∀ {b : α}, ∀ (p :
            G.Walk a b), (p.darts.map (fun d => D (f d.fst) (f d.snd))).sum = (List.zipWith D
            (p.support.map f) (p.support.map f).tail).sum) → (∀ (ι : Type), ∀ (h : ι →
            PartialOdometer),
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (p : List GaussianInt), ∀ (x : GaussianInt), p.head? = some x → p.getLast? = some x →
            List.IsChain FourNeighborAdjacent p → (List.zipWith D p p.tail).sum = (0 : ℤ)) → (
        let G : SimpleGraph GaussianInt := {
          Adj := FourNeighborAdjacent
          symm := ⟨fun {a b} => adjacent_symm a b⟩
          loopless := ⟨fun {a} => adjacent_irrefl a⟩ }
        ∀ x, ∀ (p : G.Walk x x), (p.darts.map (fun d => D d.fst d.snd)).sum = 0)) ) := by
  classical
  intro adjacent_symm adjacent_irrefl walk_sum ι h covered D hcirculation G x p
  have hi := walk_sum G id D p
  simp only [id_eq, List.map_id] at hi
  rw [hi]
  apply hcirculation p.support x
  · rw [List.head?_eq_some_head p.support_ne_nil]
    simp
  · rw [List.getLast?_eq_some_getLast p.support_ne_nil]
    simp
  · exact p.isChain_adj_support

private theorem hgmember :
    (by
      classical
      exact
        ∀ (adjacent_symm : ∀ (a : GaussianInt), ∀ (b : GaussianInt), (FourNeighborAdjacent a b) →
            (FourNeighborAdjacent b a)), ∀ (adjacent_irrefl : ∀ (a : GaussianInt), ¬
            FourNeighborAdjacent a a), (∀ (T : ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), (({a, b} : Finset GaussianInt) ∈ FootprintEdges T) → (a ∈
            FootprintVertices T ∧ b ∈ FootprintVertices T)) → ((∀ (W : ProtoTile), (LatticeTile
            W) → (∀ (F : GaussianInt → ℤ), (∀ a, ∀ b, FourNeighborAdjacent a b → ({a, b} : Finset
            GaussianInt) ∈ FootprintEdges W → F a = F b) → (∃ c : ℤ, ∀ x, x ∈ FootprintVertices W
            → F x = c))) → (∀ (ι : Type), ∀ (T : ι → ProtoTile), ∀ (h : ι → PartialOdometer), (∀
            (i : ι), LatticeTile (T i)) → ((∀ (i : ι), (↑(h i).domain : Set GaussianInt) =
            FootprintVertices (T i)) → (
        let covered (a b : GaussianInt) : Prop :=
          ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
        let D (a b : GaussianInt) : ℤ :=
          if hc : covered a b then
            (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
          else 0
        (∀ (i : ι), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ∈ (h i).domain) → ((b ∈ (h
            i).domain) → (D a b = (h i).value b - (h i).value a))) → (
        let G : SimpleGraph GaussianInt := {
          Adj := FourNeighborAdjacent
          symm := ⟨fun {a b} => adjacent_symm a b⟩
          loopless := ⟨fun {a} => adjacent_irrefl a⟩ }
        ∀ (g : GaussianInt → ℤ), (∀ (a : GaussianInt), ∀ (b : GaussianInt), G.Adj a b → g b - g a
            = D a b) → (∀ i, ∃ c : ℤ, ∀ x, x ∈ (h i).domain → g x - (h i).value x = c)))))) ) := by
  classical
  intro adjacent_symm adjacent_irrefl edge_vertices footprint_constant ι T h hT hdom covered D
      dmember G g hgedge i
  obtain ⟨c, hc⟩ := footprint_constant (T i) (hT i)
    (fun x => g x - (h i).value x) (by
      intro a b hadj he
      have hends := edge_vertices (T i) a b he
      have hai : a ∈ (h i).domain := by
        change a ∈ ((h i).domain : Set GaussianInt)
        rw [hdom i]
        exact hends.1
      have hbi : b ∈ (h i).domain := by
        change b ∈ ((h i).domain : Set GaussianInt)
        rw [hdom i]
        exact hends.2
      have hed := hgedge a b hadj
      rw [dmember i a b hai hbi] at hed
      change g a - (h i).value a = g b - (h i).value b
      omega)
  refine ⟨c, ?_⟩
  intro x hx
  apply hc x
  rw [← hdom i]
  exact hx

end OdometerGluingProof

theorem OdometerGluing :
    (∀ {n : ℕ} {T : ProtoTile} {U : Fin n → ProtoTile}
        {h : Fin n → PartialOdometer},
      LatticeTile T →
      (∀ i, LatticeTile (U i)) →
      (∀ i, ((h i).domain : Set GaussianInt) = FootprintVertices (U i)) →
      (∀ i j, OdometerCompatibility (h i) (h j)) →
      (∀ x, x ∈ T.cells ↔ ∃ i, x ∈ (U i).cells) →
      (∀ x, x ∈ FootprintVertices T ↔ ∃ i, x ∈ (h i).domain) →
      ∃ g : PartialOdometer,
        (g.domain : Set GaussianInt) = FootprintVertices T ∧
        (∀ i, OdometerCompatibility g (h i)) ∧
        ∀ g' : PartialOdometer,
          (g'.domain : Set GaussianInt) = FootprintVertices T →
          (∀ i, OdometerCompatibility g' (h i)) →
          ∃ c : ℤ, ∀ x, x ∈ g.domain → g'.value x - g.value x = c) ∧
    (∀ {ι : Type} [Nonempty ι] {T : ι → ProtoTile}
        {h : ι → PartialOdometer},
      (∀ i, LatticeTile (T i)) →
      (∀ i, ((h i).domain : Set GaussianInt) = FootprintVertices (T i)) →
      (∀ i j, OdometerCompatibility (h i) (h j)) →
      (∀ x : GaussianInt, ∃ i,
        x ∈ (h i).domain ∧ x + 1 ∈ (h i).domain ∧
        x + ⟨0, 1⟩ ∈ (h i).domain ∧
        x + 1 + ⟨0, 1⟩ ∈ (h i).domain) →
      ∃ g : IntegerLatticeFunction,
        (∀ i, ∃ c : ℤ, ∀ x, x ∈ (h i).domain →
          g x - (h i).value x = c) ∧
        ∀ g' : IntegerLatticeFunction,
          (∀ i, ∃ c : ℤ, ∀ x, x ∈ (h i).domain →
            g' x - (h i).value x = c) →
          ∃ c : ℤ, ∀ x, g' x - g x = c) := by
-- BODY
  classical
  have increment_eq {ι : Type} (h : ι → PartialOdometer)
      (hcompat : ∀ i j, OdometerCompatibility (h i) (h j))
      (i j : ι) (a b : GaussianInt)
      (hai : a ∈ (h i).domain) (hbi : b ∈ (h i).domain)
      (haj : a ∈ (h j).domain) (hbj : b ∈ (h j).domain) := OdometerGluingProof.increment_eq (ι :=
          ι) h hcompat i j a b hai hbi haj hbj
  have adjacent_symm (a b : GaussianInt) (hab : FourNeighborAdjacent a b) :
      FourNeighborAdjacent b a := OdometerGluingProof.adjacent_symm a b hab
  have adjacent_irrefl (a : GaussianInt) := OdometerGluingProof.adjacent_irrefl a
  have corner (T : ProtoTile) (x : GaussianInt) (hx : x ∈ T.cells)
      (a : GaussianInt)
      (ha : a = x ∨ a = x + 1 ∨ a = x + ⟨0, 1⟩ ∨
        a = x + 1 + ⟨0, 1⟩) : a ∈ FootprintVertices T := OdometerGluingProof.corner T x hx a ha
  have edge_vertices (T : ProtoTile) (a b : GaussianInt)
      (he : ({a, b} : Finset GaussianInt) ∈ FootprintEdges T) :=
          OdometerGluingProof.edge_vertices corner T a b he
  have footprint_reachable (W : ProtoTile) (hW : LatticeTile W)
      (a b : GaussianInt) (ha : a ∈ FootprintVertices W) (hb : b ∈ FootprintVertices W) :=
          OdometerGluingProof.footprint_reachable adjacent_symm W hW a b ha hb
  have footprint_constant (W : ProtoTile) (hW : LatticeTile W)
      (F : GaussianInt → ℤ)
      (hF : ∀ a b, FourNeighborAdjacent a b →
        ({a, b} : Finset GaussianInt) ∈ FootprintEdges W → F a = F b) :=
            OdometerGluingProof.footprint_constant corner edge_vertices footprint_reachable W hW
            F hF
  have walk_sum {α : Type} (G : SimpleGraph α)
      (f : α → GaussianInt) (D : GaussianInt → GaussianInt → ℤ)
      {a b : α} (p : G.Walk a b) := OdometerGluingProof.walk_sum (α := α) G f D (a := a) (b := b) p
  constructor
  · intro n T U h hT hU hdom hcompat hcells hverts
    let E (a b : GaussianInt) : Prop := FourNeighborAdjacent a b ∧
      ({a, b} : Finset GaussianInt) ∈ FootprintEdges T
    let covered (a b : GaussianInt) : Prop :=
      ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
    let D (a b : GaussianInt) : ℤ :=
      if hc : covered a b then
        (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
      else 0
    have dmember (i : Fin n) (a b : GaussianInt)
        (ha : a ∈ (h i).domain) (hb : b ∈ (h i).domain) :
        D a b = (h i).value b - (h i).value a := OdometerGluingProof.dmemberAt297 increment_eq n
            h hcompat i a b ha hb
    have edge_cover (a b : GaussianInt) (hab : E a b) := OdometerGluingProof.edge_coverAt304
        corner n T U h hdom hcells a b hab
    have hanti := OdometerGluingProof.hantiAt324 n T h dmember edge_cover
    have hflat := OdometerGluingProof.hflatAt329 corner n T U h hdom hcells dmember
    have hcirculation := P3221T2ClosedWalkCirculation.1 T hT D
      (fun a b ha he => hanti a b ⟨ha, he⟩) hflat
    let G : SimpleGraph {x // x ∈ FootprintVertices T} := {
      Adj := fun a b => E a.val b.val
      symm := ⟨by
        intro a b hab
        exact ⟨adjacent_symm a b hab.1, by simpa [Finset.pair_comm] using hab.2⟩⟩
      loopless := ⟨by intro a ha; exact adjacent_irrefl a ha.1⟩ }
    obtain ⟨z, hz⟩ := (LatticeTileGridStructure T hT).1.1
    let base : {x // x ∈ FootprintVertices T} := ⟨z, corner T z hz z (by simp)⟩
    have hconn := OdometerGluingProof.hconnAt356 adjacent_symm adjacent_irrefl corner
        edge_vertices footprint_reachable T hT z hz
    have hclosed := OdometerGluingProof.hclosedAt371 adjacent_symm adjacent_irrefl walk_sum n T h
        hcirculation
    obtain ⟨f, hfbase, hfedge, hfunique⟩ :=
      P3221T2ConnectedPathIntegration G base hconn
        (fun a b => D a.val b.val) (fun a b hab => hanti a b hab) hclosed
    let dom : Finset GaussianInt := T.cells.biUnion (fun x =>
      {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
    have hdomain : (dom : Set GaussianInt) = FootprintVertices T := OdometerGluingProof.hdomain T
        z hz
    let g : PartialOdometer := {
      domain := dom
      value := fun x => if hx : x ∈ FootprintVertices T then f ⟨x, hx⟩ else 0
      value_outside := by
        intro x hx
        have hx' : x ∉ FootprintVertices T := OdometerGluingProof.hx' T hdomain x hx
        simp [hx'] }
    have hgvalue (x : {x // x ∈ FootprintVertices T}) : g.value x = f x := by
      simp [g, x.property]
    have hgcompat := OdometerGluingProof.hgcompat adjacent_symm adjacent_irrefl corner
        edge_vertices footprint_constant n T U h hU hdom hcells hverts dmember z hz f hfedge
        hdomain hgvalue
    refine ⟨g, hdomain, hgcompat, ?_⟩
    intro g' hg'dom hg'compat
    have hg'edge := OdometerGluingProof.hg'edge adjacent_symm adjacent_irrefl corner n T h
        dmember edge_cover z hz f g' hg'dom hg'compat
    obtain ⟨c, hc⟩ := hfunique (fun x => g'.value x) hg'edge
    refine ⟨c, ?_⟩
    intro x hx
    have hxT : x ∈ FootprintVertices T := by
      rw [← hdomain]
      exact hx
    simpa [g, hxT] using hc ⟨x, hxT⟩
  · intro ι hι T h hT hdom hcompat hcover
    let covered (a b : GaussianInt) : Prop :=
      ∃ i, a ∈ (h i).domain ∧ b ∈ (h i).domain
    let D (a b : GaussianInt) : ℤ :=
      if hc : covered a b then
        (h (Classical.choose hc)).value b - (h (Classical.choose hc)).value a
      else 0
    have dmember (i : ι) (a b : GaussianInt)
        (ha : a ∈ (h i).domain) (hb : b ∈ (h i).domain) :
        D a b = (h i).value b - (h i).value a := OdometerGluingProof.dmemberAt470 increment_eq ι
            h hcompat i a b ha hb
    have edge_cover (a b : GaussianInt) (hab : FourNeighborAdjacent a b) :=
        OdometerGluingProof.edge_coverAt477 ι h hcover a b hab
    have hanti := OdometerGluingProof.hantiAt488 ι h dmember edge_cover
    have hflat := OdometerGluingProof.hflatAt493 ι h hcover dmember
    have hcirculation := P3221T2ClosedWalkCirculation.2 D hanti hflat
    let G : SimpleGraph GaussianInt := {
      Adj := FourNeighborAdjacent
      symm := ⟨fun {a b} => adjacent_symm a b⟩
      loopless := ⟨fun {a} => adjacent_irrefl a⟩ }
    have hconn := OdometerGluingProof.hconnAt508 adjacent_symm adjacent_irrefl
    have hclosed := OdometerGluingProof.hclosedAt527 adjacent_symm adjacent_irrefl walk_sum ι h
        hcirculation
    obtain ⟨g, hgzero, hgedge, hgunique⟩ :=
      P3221T2ConnectedPathIntegration G 0 hconn D hanti hclosed
    have hgmember := OdometerGluingProof.hgmember adjacent_symm adjacent_irrefl edge_vertices
        footprint_constant ι T h hT hdom dmember g hgedge
    refine ⟨g, hgmember, ?_⟩
    intro g' hg'
    apply hgunique g'
    intro a b hab
    obtain ⟨i, ha, hb⟩ := edge_cover a b hab
    obtain ⟨c, hc⟩ := hg' i
    have hca := hc a ha
    have hcb := hc b hb
    rw [dmember i a b ha hb]
    omega

end ApollonianSuperharmonic

end
