/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5260T1PlacementLedger
public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.P5253T1BottomSquareContact
public import LeanPool.ApollonianSuperharmonic.P5253T1LeftSquareContacts
public import LeanPool.ApollonianSuperharmonic.P5253T1OneEdgeInterface
public import LeanPool.ApollonianSuperharmonic.P4055T1ExactTripleImage
public import LeanPool.ApollonianSuperharmonic.CellDisjointCommonEdgesBoundary
public import LeanPool.ApollonianSuperharmonic.DiamondBaseT2
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondCentroid
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.P5124T1SmallerParents
public import LeanPool.ApollonianSuperharmonic.P5691T1DiamondReflectionFootprints

-- [TABLET NODE: P5260T1PredecessorInterfaces]

/-!
# P5260T1PredecessorInterfaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace PredecessorInterfaceGeometry

private theorem rawBoundaryVertices :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩ FootprintVertices Y =
            BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y))) ) := by
  classical
  intro X Y hX hY hdisj
  ext z
  constructor
  · intro hz
    have incident (T : ProtoTile) (hT : T.cells.Nonempty)
        (hmem : z ∈ FootprintVertices T) :
        ∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ T.cells := by
      simp only [FootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq] at hmem
      obtain ⟨c, hc, hcorner⟩ := hmem
      rcases hcorner with hcorner | hcorner | hcorner | hcorner
      · subst z
        exact ⟨0, by simpa [LatticeVertexIncidentCell] using hc⟩
      · subst z
        exact ⟨1, by simpa [LatticeVertexIncidentCell] using hc⟩
      · subst z
        exact ⟨3, by simpa [LatticeVertexIncidentCell] using hc⟩
      · subst z
        have hcell : LatticeVertexIncidentCell (c + 1 + ⟨0, 1⟩) 2 = c := by
          simp [LatticeVertexIncidentCell]
          abel
        exact ⟨2, by rw [hcell]; exact hc⟩
    obtain ⟨ix, hx⟩ := incident X hX hz.1
    obtain ⟨iy, hy⟩ := incident Y hY hz.2
    have hyX : LatticeVertexIncidentCell z iy ∉ X.cells := by
      intro hbad
      exact (Finset.disjoint_left.mp hdisj hbad) hy
    have hxY : LatticeVertexIncidentCell z ix ∉ Y.cells := by
      intro hbad
      exact (Finset.disjoint_left.mp hdisj.symm hbad) hx
    exact ⟨P3161T2IncidentBoundary X z ⟨ix, hx⟩ ⟨iy, hyX⟩,
      P3161T2IncidentBoundary Y z ⟨iy, hy⟩ ⟨ix, hxY⟩⟩
  · intro hz
    have boundaryRaw (T : ProtoTile) (hT : T.cells.Nonempty)
        (hv : z ∈ BoundaryFootprintVertices T) : z ∈ FootprintVertices T := by
      simp only [BoundaryFootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq] at hv
      obtain ⟨e, he, hze⟩ := hv
      rcases he with ⟨c, ⟨heq, hsupport⟩ | ⟨heq, hsupport⟩⟩
      · subst e
        rcases hsupport with ⟨hc, _⟩ | ⟨_, hc⟩
        · simp only [FootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq]
          refine ⟨c, hc, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hze
          rcases hze with h | h <;> subst z <;>
            simp [add_assoc]
        · have hc' : c - ⟨0, 1⟩ ∈ T.cells := hc
          simp only [FootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq]
          refine ⟨c - ⟨0, 1⟩, hc', ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hze
          rcases hze with h | h <;> subst z <;>
            simp [sub_eq_add_neg, add_comm, add_left_comm]
      · subst e
        rcases hsupport with ⟨hc, _⟩ | ⟨_, hc⟩
        · simp only [FootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq]
          refine ⟨c, hc, ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hze
          rcases hze with h | h <;> subst z <;>
            simp [add_assoc]
        · have hc' : c - 1 ∈ T.cells := hc
          simp only [FootprintVertices, ite_eq_left hT, Set.mem_ofPred_eq]
          refine ⟨c - 1, hc', ?_⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hze
          rcases hze with h | h <;> subst z <;>
            simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
    exact ⟨boundaryRaw X hX hz.1, boundaryRaw Y hY hz.2⟩

private theorem rawBoundaryEdges :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (FootprintEdges X ∩
            FootprintEdges Y = BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y) ) := by
  classical
  intro X Y hdisj
  exact CellDisjointCommonEdgesBoundary X Y hdisj

private theorem staircaseBetween :
    (by
      classical
      exact
        (Nat) → (∀ (z : GaussianInt), ∀ (horizontalFirst : Bool), ∀ (s : Int), (s = 1 ∨ s = -1) →
            (∀ (N : Nat), (0 < N) → (SimpleGridPathBetween {v | ∃ j ≤ N, v =
            P5157T1StaircasePoint z horizontalFirst s j} {e | ∃ j < N, e =
            {P5157T1StaircasePoint z horizontalFirst s j,
            P5157T1StaircasePoint z horizontalFirst s (j + 1)}} (P5157T1StaircasePoint z
            horizontalFirst s 0) (P5157T1StaircasePoint z horizontalFirst s N)))) ) := by
  classical
  intro k z horizontalFirst s hs N hN
  let p := P5157T1StaircasePoint z horizontalFirst s
  let l := List.ofFn (fun j : Fin (N + 1) => p j)
  have inj : Function.Injective p :=
    (P5157T1AlternatingStaircase z horizontalFirst s hs N hN).1
  have step (j : Nat) :
      p (j + 1) = p j + 1 ∨ p (j + 1) = p j - 1 ∨
      p (j + 1) = p j + ⟨0, 1⟩ ∨ p (j + 1) = p j - ⟨0, 1⟩ := by
    rcases hs with rfl | rfl <;> cases horizontalFirst <;>
      simp [p, P5157T1StaircasePoint, Zsqrtd.ext_iff] <;> omega
  have chain : l.IsChain (fun a b => ∃ j < N, a = p j ∧ b = p (j + 1)) := by
    apply List.isChain_ofFn.mpr
    intro j hj
    exact ⟨j, by omega, rfl, rfl⟩
  have consecutive (a b : GaussianInt) (l₁ l₂ : List GaussianInt)
      (heq : l = l₁ ++ a :: b :: l₂) :
      ∃ j < N, a = p j ∧ b = p (j + 1) :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp chain heq
  have hhead : l.head? = some (p 0) := by simp [l]
  have hlast : l.getLast? = some (p N) := by
    calc
      l.getLast? = some (l.getLast (by simp [l])) :=
        List.getLast?_eq_getLast_of_ne_nil (by simp [l])
      _ = some (p N) := by
        simp only [l, List.getLast_ofFn_succ]
        congr 1
  refine ⟨l, ?_⟩
  constructor
  · apply List.nodup_ofFn.mpr
    intro a b hab
    exact Fin.ext (inj hab)
  constructor
  · simp [l]
    omega
  constructor
  · exact hhead
  constructor
  · exact hlast
  constructor
  · ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset, l,
      List.mem_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, by omega, rfl⟩
  constructor
  · intro a b l₁ l₂ heq
    obtain ⟨j, _, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
    exact step j
  · intro e
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjl : j < l.length := by simp [l]; omega
      have hjl' : j + 1 < l.length := by simp [l]; omega
      refine ⟨p j, p (j + 1), l.take j, l.drop (j + 2), ?_, rfl⟩
      have hd := List.getElem_cons_drop hjl
      have hd' := List.getElem_cons_drop hjl'
      have heq : l = l.take j ++ l[j] :: l[j + 1] :: l.drop (j + 2) := by
        rw [show j + 2 = j + 1 + 1 by omega, hd', hd, List.take_append_drop]
      simpa only [l, List.getElem_ofFn] using heq
    · rintro ⟨a, b, l₁, l₂, heq, rfl⟩
      obtain ⟨j, hj, rfl, rfl⟩ := consecutive a b l₁ l₂ heq
      exact ⟨j, hj, rfl⟩

private theorem capBetween :
    (by
      classical
      exact
        (Nat) → (∀ (m : Nat), (0 < m) → (∀ (u : GaussianInt), SimpleGridPathBetween
            (BoundaryFootprintVertices (TileTranslation (DiamondTile m) u) ∩
            BoundaryFootprintVertices (TileTranslation (DiamondTile m) (u + ⟨0, 2 * (m : Int)⟩)))
            (BoundaryFootprintEdges (TileTranslation (DiamondTile m) u) ∩ BoundaryFootprintEdges
            (TileTranslation (DiamondTile m) (u + ⟨0, 2 * (m : Int)⟩))) (u + ⟨-1, 2 * (m : Int)⟩)
            (u + ⟨1, 2 * (m : Int)⟩))) ) := by
  classical
  intro k m hm u
  have hcap := P5203T1CapInterface m hm u
  dsimp only at hcap
  obtain ⟨hneT, hneU, hdisj, hV, hE, _⟩ := hcap
  let p0 : GaussianInt := u + ⟨-1, 2 * (m : Int)⟩
  let p1 : GaussianInt := u + ⟨0, 2 * (m : Int)⟩
  let p2 : GaussianInt := u + ⟨1, 2 * (m : Int)⟩
  have hverts : {z | (z - u).im = 2 * (m : Int) ∧
      -1 ≤ (z - u).re ∧ (z - u).re ≤ 1} =
      ({p0, p1, p2} : Set GaussianInt) := by
    ext z
    constructor
    · rintro ⟨him, hlow, hhigh⟩
      have him' : z.im - u.im = 2 * (m : Int) := by
        simpa only [Zsqrtd.im_sub] using him
      have hre' : z.re - u.re = (z - u).re := by simp
      have hlo' : -1 ≤ z.re - u.re := by simpa only [Zsqrtd.re_sub] using hlow
      have hhi' : z.re - u.re ≤ 1 := by simpa only [Zsqrtd.re_sub] using hhigh
      have hre : (z - u).re = -1 ∨ (z - u).re = 0 ∨ (z - u).re = 1 := by omega
      rcases hre with h | h | h
      · left
        have hreal : z.re - u.re = -1 := by rw [hre']; exact h
        have himag : z.im - u.im = 2 * (m : Int) := him'
        apply Zsqrtd.ext_iff.mpr
        constructor <;> simp [p0] <;> omega
      · right; left
        have hreal : z.re - u.re = 0 := by rw [hre']; exact h
        have himag : z.im - u.im = 2 * (m : Int) := him'
        apply Zsqrtd.ext_iff.mpr
        constructor <;> simp [p1] <;> omega
      · right; right
        have hreal : z.re - u.re = 1 := by rw [hre']; exact h
        have himag : z.im - u.im = 2 * (m : Int) := him'
        apply Zsqrtd.ext_iff.mpr
        constructor <;> simp [p2] <;> omega
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, p0, p1, p2]
      rintro (rfl | rfl | rfl) <;>
        simp [Zsqrtd.re_sub, Zsqrtd.im_sub, Zsqrtd.re_add,
          Zsqrtd.im_add] <;> omega
  have hedges : {e : Finset GaussianInt | ∃ a : Int, -1 ≤ a ∧ a < 1 ∧
      e = {u + ⟨a, 2 * (m : Int)⟩, u + ⟨a + 1, 2 * (m : Int)⟩}} =
      ({{p0, p1}, {p1, p2}} : Set (Finset GaussianInt)) := by
    ext e
    constructor
    · rintro ⟨a, ha, ha', rfl⟩
      rcases (show a = -1 ∨ a = 0 by omega) with rfl | rfl
      · simp [p0, p1]
      · simp [p1, p2]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨-1, by omega, by omega, by simp [p0, p1]⟩
      · exact ⟨0, by omega, by omega, by simp [p1, p2]⟩
  have hp0 : p1 = p0 + 1 := by
    apply Zsqrtd.ext <;> simp [p0, p1]
  have hp1 : p2 = p1 + 1 := by
    apply Zsqrtd.ext <;> simp [p1, p2]
  have chain : [p0, p1, p2].IsChain (fun x y =>
      (x = p0 ∧ y = p1) ∨ (x = p1 ∧ y = p2)) := by simp
  rw [hV, hE, hverts, hedges]
  refine ⟨[p0, p1, p2], ?_⟩
  constructor
  · simp [p0, p1, p2, Zsqrtd.ext_iff]
  constructor
  · norm_num
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · ext z
    simp
  constructor
  · intro x y l r h
    rcases List.isChain_iff_forall_rel_of_append_cons_cons.mp chain h with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [p0, p1] using (Or.inl hp0 : p1 = p0 + 1 ∨ _)
    · simpa [p1, p2] using (Or.inl hp1 : p2 = p1 + 1 ∨ _)
  · intro e
    constructor
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨p0, p1, [], [p2], rfl, rfl⟩
      · exact ⟨p1, p2, [p0], [], rfl, rfl⟩
    · rintro ⟨x, y, l, r, h, rfl⟩
      rcases List.isChain_iff_forall_rel_of_append_cons_cons.mp chain h with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · simp

private theorem rawStaircase :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩ FootprintVertices Y =
            BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) → ((∀ (X : ProtoTile),
            ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (FootprintEdges X ∩ FootprintEdges Y
            = BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y)) → ((∀ (z : GaussianInt), ∀
            (horizontalFirst : Bool), ∀ (s : Int), (s = 1 ∨ s = -1) → (∀ (N : Nat), (0 < N) →
            (SimpleGridPathBetween {v | ∃ j ≤ N, v = P5157T1StaircasePoint z horizontalFirst s
            j} {e | ∃ j < N, e = {P5157T1StaircasePoint z horizontalFirst s j,
            P5157T1StaircasePoint z horizontalFirst s (j + 1)}} (P5157T1StaircasePoint z
            horizontalFirst s 0) (P5157T1StaircasePoint z horizontalFirst s N)))) → (∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) → ((Disjoint
            X.cells Y.cells) → (∀ (z : GaussianInt), ∀ (horizontalFirst : Bool), ∀ (s : Int), (s
            = 1 ∨ s = -1) → (∀ (N : Nat), (0 < N) → ((BoundaryFootprintVertices X ∩
            BoundaryFootprintVertices Y =
            {v | ∃ j ≤ N, v = P5157T1StaircasePoint z horizontalFirst s j}) →
                ((BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y =
            {e | ∃ j < N, e = {P5157T1StaircasePoint z horizontalFirst s j,
              P5157T1StaircasePoint z horizontalFirst s (j + 1)}}) → (SimpleGridPathBetween
                  (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges
                  Y) (P5157T1StaircasePoint z horizontalFirst s 0) (P5157T1StaircasePoint z
                  horizontalFirst s N))))))))))) ) := by
  classical
  intro rawBoundaryVertices rawBoundaryEdges staircaseBetween X Y hX hY hdisj z horizontalFirst s
      hs N hN hV hE
  rw [rawBoundaryVertices X Y hX hY hdisj, hV,
    rawBoundaryEdges X Y hdisj, hE]
  exact staircaseBetween z horizontalFirst s hs N hN

private theorem rawCapBetween :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) → ((Y.cells.Nonempty) →
            ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩ FootprintVertices Y =
            BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) → ((∀ (X : ProtoTile),
            ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (FootprintEdges X ∩ FootprintEdges Y
            = BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y)) → ((∀ (m : Nat), (0 < m) → (∀
            (u : GaussianInt), SimpleGridPathBetween (BoundaryFootprintVertices (TileTranslation
            (DiamondTile m) u) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile m) (u +
            ⟨0, 2 * (m : Int)⟩))) (BoundaryFootprintEdges (TileTranslation (DiamondTile m) u) ∩
            BoundaryFootprintEdges (TileTranslation (DiamondTile m) (u + ⟨0, 2 * (m : Int)⟩))) (u
            + ⟨-1, 2 * (m : Int)⟩) (u + ⟨1, 2 * (m : Int)⟩))) → (∀ (m : Nat), (0 < m) → (∀ (u :
            GaussianInt), (Disjoint (TileTranslation (DiamondTile m) u).cells
            (TileTranslation (DiamondTile m) (u + ⟨0, 2 * (m : Int)⟩)).cells) →
                (SimpleGridPathBetween (FootprintVertices (TileTranslation (DiamondTile m) u) ∩
                FootprintVertices (TileTranslation (DiamondTile m) (u + ⟨0, 2 * (m : Int)⟩)))
                (FootprintEdges (TileTranslation (DiamondTile m) u) ∩ FootprintEdges
                (TileTranslation (DiamondTile m) (u + ⟨0, 2 * (m : Int)⟩))) (u + ⟨-1, 2 * (m :
                Int)⟩) (u + ⟨1, 2 * (m : Int)⟩)))))) ) := by
  classical
  intro rawBoundaryVertices rawBoundaryEdges capBetween m hm u hdisj
  have hcap := P5203T1CapInterface m hm u
  dsimp only at hcap
  rcases hcap with ⟨hneT, hneU, _, _, _, _⟩
  rw [rawBoundaryVertices _ _ hneT hneU hdisj,
    rawBoundaryEdges _ _ hdisj]
  exact capBetween m hm u

private theorem twoVertexPath :
    (by
      classical
      exact
        (Nat) → (∀ (V : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (x : GaussianInt),
            ∀ (y : GaussianInt), (x ≠ y) → ((V = {x, y}) → ((E = {{x, y}}) → ((y = x + 1 ∨ y = x
            - 1 ∨ y = x + ⟨0, 1⟩ ∨
            y = x - ⟨0, 1⟩) → (SimpleGridPathBetween V E x y))))) ) := by
  classical
  intro k V E x y hne hV hE hstep
  rw [hV, hE]
  refine ⟨[x, y], ?_⟩
  constructor
  · simp [hne]
  constructor
  · norm_num
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · ext z
    simp
  constructor
  · intro a b l₁ l₂ heq
    have llen := congrArg List.length heq
    simp only [List.length_cons, List.length_nil, List.length_append] at llen
    have h₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst l₁
    subst l₂
    simp only [List.nil_append, List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, rfl⟩
    exact hstep
  · intro e
    constructor
    · rintro rfl
      exact ⟨x, y, [], [], rfl, rfl⟩
    · rintro ⟨a, b, l₁, l₂, heq, rfl⟩
      have llen := congrArg List.length heq
      simp only [List.length_cons, List.length_nil, List.length_append] at llen
      have h₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst l₁
      subst l₂
      simp only [List.nil_append, List.cons.injEq, and_true] at heq
      rcases heq with ⟨rfl, rfl⟩
      rfl

private theorem diamondCellsNonempty :
    (by
      classical
      exact
        ∀ (m : Nat), (0 < m) → ((DiamondTile m).cells.Nonempty) ) := by
  classical
  intro m hm
  refine ⟨0, (P4194T1DiamondCellRows m 0).1.mpr ?_⟩
  norm_num
  omega

private theorem reversePath :
    (by
      classical
      exact
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, (SimpleGridPathBetween V E x y) → (SimpleGridPathBetween V E y x)
            ) := by
  classical
  intro V E x y hp
  rcases hp with ⟨p, hn, hl, hh, ht, hV, hs, he⟩
  have revstep : ∀ a b l₁ l₂, p.reverse = l₁ ++ a :: b :: l₂ →
      b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩ := by
    intro a b l₁ l₂ h
    have h' : p = l₂.reverse ++ b :: a :: l₁.reverse := by
      have := congrArg List.reverse h
      simpa [List.reverse_append, List.append_assoc] using this
    rcases hs b a _ _ h' with h | h | h | h
    · exact Or.inr (Or.inl (by rw [h]; simp))
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr (Or.inr (Or.inr (by rw [h]; simp)))
    · exact Or.inr (Or.inr (Or.inl (by rw [h]; simp)))
  have revocc (q : List GaussianInt) (e : Finset GaussianInt)
      (ho : ∃ a b l₁ l₂, q = l₁ ++ a :: b :: l₂ ∧ e = {a, b}) :
      ∃ a b l₁ l₂, q.reverse = l₁ ++ a :: b :: l₂ ∧ e = {a, b} := by
    rcases ho with ⟨a, b, l₁, l₂, rfl, rfl⟩
    exact ⟨b, a, l₂.reverse, l₁.reverse,
      by simp [List.reverse_append, List.append_assoc], Finset.pair_comm _ _⟩
  refine ⟨p.reverse, List.nodup_reverse.mpr hn, by simpa using hl,
    by simpa using ht, by simpa using hh, by simpa using hV, revstep, ?_⟩
  intro e
  exact ⟨fun h => revocc p e ((he e).mp h), fun h =>
    (he e).mpr (by simpa using revocc p.reverse e h)⟩

private theorem translatedDiamondCellsNonempty :
    (by
      classical
      exact
        (∀ (m : Nat), (0 < m) → ((DiamondTile m).cells.Nonempty)) → (∀ (m : Nat), (0 < m) → (∀ (u
            : GaussianInt), (TileTranslation (DiamondTile m) u).cells.Nonempty)) ) := by
  classical
  intro diamondCellsNonempty m hm u
  rw [(TileTranslationFormulas (DiamondTile m) u).1]
  exact (diamondCellsNonempty m hm).image _

private theorem pathDW :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (∀ (z : GaussianInt), ∀
            (horizontalFirst : Bool), ∀ (s : Int), (s = 1 ∨ s = -1) → (∀ (N : Nat), (0 < N) →
            ((BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y = {v | ∃ j ≤ N, v =
            P5157T1StaircasePoint z horizontalFirst s j}) → ((BoundaryFootprintEdges X ∩
            BoundaryFootprintEdges Y = {e | ∃ j < N, e =
            {P5157T1StaircasePoint z horizontalFirst s j,
            P5157T1StaircasePoint z horizontalFirst s (j + 1)}}) → (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges Y)
            (P5157T1StaircasePoint z horizontalFirst s 0) (P5157T1StaircasePoint z
            horizontalFirst s N))))))))) → ((∀ (m : Nat), (0 < m) → ((DiamondTile
            m).cells.Nonempty)) → ((∀ (m : Nat), (0 < m) → (∀ (u : GaussianInt), (TileTranslation
            (DiamondTile m) u).cells.Nonempty)) → ((0 < k) → ((0 < k - 1) → (
        let N : Nat := 2 * (k - 1)
        (0 < N) → (
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (Disjoint (DiamondTile k).cells (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ),
            (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)).cells) → ((BoundaryFootprintVertices (DiamondTile
            k) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k :
            ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v : GaussianInt | ∃ j ≤ (2 : ℕ) * (k - (1
            : ℕ)), v = P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) j}) →
            ((BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges (TileTranslation
            (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {e :
            Finset GaussianInt | ∃ j < (2 : ℕ) * (k - (1 : ℕ)), e =
            {P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) j,
            P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) (j + (1 : ℕ))}}) →
            (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D
            ∩ FootprintEdges W) (P5157T1StaircasePoint 1 false 1 0) (P5157T1StaircasePoint 1
            false 1 N)))))))))) ) := by
  classical
  intro k rawStaircase diamondCellsNonempty translatedDiamondCellsNonempty hkpos hsmall N hN D W
      hDWd hDWv hDWe
  exact rawStaircase D W (diamondCellsNonempty k hkpos)
    (translatedDiamondCellsNonempty (k - 1) hsmall _) hDWd
    1 false 1 (Or.inl rfl) N hN hDWv hDWe

private theorem pathLW :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (∀ (z : GaussianInt), ∀
            (horizontalFirst : Bool), ∀ (s : Int), (s = 1 ∨ s = -1) → (∀ (N : Nat), (0 < N) →
            ((BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y = {v | ∃ j ≤ N, v =
            P5157T1StaircasePoint z horizontalFirst s j}) → ((BoundaryFootprintEdges X ∩
            BoundaryFootprintEdges Y = {e | ∃ j < N, e =
            {P5157T1StaircasePoint z horizontalFirst s j,
            P5157T1StaircasePoint z horizontalFirst s (j + 1)}}) → (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges Y)
            (P5157T1StaircasePoint z horizontalFirst s 0) (P5157T1StaircasePoint z
            horizontalFirst s N))))))))) → ((∀ (m : Nat), (0 < m) → (∀ (u : GaussianInt),
            (TileTranslation (DiamondTile m) u).cells.Nonempty)) → ((0 < k) → ((0 < k - 1) → (
        let N : Nat := 2 * (k - 1)
        (0 < N) → (
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (Disjoint (TileTranslation (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k : ℤ))⟩ :
            GaussianInt)).cells (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ)
            - (↑k : ℤ)⟩ : GaussianInt)).cells) → ((BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k : ℤ))⟩ : GaussianInt)) ∩
            BoundaryFootprintVertices (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1
            : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v : GaussianInt | ∃ j ≤ (2 : ℕ) * (k - (1 : ℕ)),
            v = P5157T1StaircasePoint (1 : GaussianInt) false (-1 : ℤ) j}) →
            ((BoundaryFootprintEdges (TileTranslation (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k
            : ℤ))⟩ : GaussianInt)) ∩ BoundaryFootprintEdges (TileTranslation (DiamondTile (k - (1
            : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {e : Finset GaussianInt | ∃
            j < (2 : ℕ) * (k - (1 : ℕ)), e =
            {P5157T1StaircasePoint (1 : GaussianInt) false (-1 : ℤ) j,
            P5157T1StaircasePoint (1 : GaussianInt) false (-1 : ℤ) (j + (1 : ℕ))}}) →
            (SimpleGridPathBetween (FootprintVertices L ∩ FootprintVertices W) (FootprintEdges L
            ∩ FootprintEdges W) (P5157T1StaircasePoint 1 false (-1) 0) (P5157T1StaircasePoint
            1 false (-1) N))))))))) ) := by
  classical
  intro k rawStaircase translatedDiamondCellsNonempty hkpos hsmall N hN D W L hLWd hLWv hLWe
  exact rawStaircase L W
    (translatedDiamondCellsNonempty k hkpos _)
    (translatedDiamondCellsNonempty (k - 1) hsmall _) hLWd
    1 false (-1) (Or.inr rfl) N hN hLWv hLWe

private theorem pathDEm :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (∀ (z : GaussianInt), ∀
            (horizontalFirst : Bool), ∀ (s : Int), (s = 1 ∨ s = -1) → (∀ (N : Nat), (0 < N) →
            ((BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y = {v | ∃ j ≤ N, v =
            P5157T1StaircasePoint z horizontalFirst s j}) → ((BoundaryFootprintEdges X ∩
            BoundaryFootprintEdges Y = {e | ∃ j < N, e =
            {P5157T1StaircasePoint z horizontalFirst s j,
            P5157T1StaircasePoint z horizontalFirst s (j + 1)}}) → (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges Y)
            (P5157T1StaircasePoint z horizontalFirst s 0) (P5157T1StaircasePoint z
            horizontalFirst s N))))))))) → ((∀ (m : Nat), (0 < m) → ((DiamondTile
            m).cells.Nonempty)) → ((∀ (m : Nat), (0 < m) → (∀ (u : GaussianInt), (TileTranslation
            (DiamondTile m) u).cells.Nonempty)) → ((0 < k) → ((0 < k - 1) → (
        let N : Nat := 2 * (k - 1)
        (0 < N) → (
        let D := DiamondTile k
        let Em := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
        (Disjoint (DiamondTile k).cells (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨-(↑k : ℤ),
            (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)).cells) → ((BoundaryFootprintVertices (DiamondTile
            k) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨-(↑k :
            ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v : GaussianInt | ∃ j ≤ (2 : ℕ) * (k - (1
            : ℕ)), v = P5157T1StaircasePoint (⟨-(↑k : ℤ), (↑k : ℤ) - (1 : ℤ)⟩ : GaussianInt)
            true (-1 : ℤ) j}) → ((BoundaryFootprintEdges (DiamondTile k) ∩ BoundaryFootprintEdges
            (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨-(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ :
            GaussianInt)) = {e : Finset GaussianInt | ∃ j < (2 : ℕ) * (k - (1 : ℕ)), e =
            {P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) j,
              P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) (j + 1)}}) →
            (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices Em) (FootprintEdges D
            ∩ FootprintEdges Em) (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
            0) (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N)))))))))) ) := by
  classical
  intro k rawStaircase diamondCellsNonempty translatedDiamondCellsNonempty hkpos hsmall N hN D Em
      hDEd hDEv hDEe
  exact rawStaircase D Em (diamondCellsNonempty k hkpos)
    (translatedDiamondCellsNonempty (k - 1) hsmall _) hDEd
    ⟨-(k : Int), (k : Int) - 1⟩ true (-1) (Or.inr rfl) N hN hDEv hDEe

private theorem translatedPath :
    (by
      classical
      exact
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, ∀ (u : GaussianInt), (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween (GaussianTranslation u '' V) ((fun e : Finset GaussianInt =>
            e.image (GaussianTranslation u)) '' E) (GaussianTranslation u x) (GaussianTranslation
            u y)) ) := by
  classical
  intro V E x y u hp
  apply P4055T1GridPathImage (GaussianTranslation u)
  · intro a b hab
    exact add_right_cancel hab
  · intro a b h
    rcases h with h | h | h | h
    · subst b; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [GaussianTranslation]; abel
  · exact hp

private theorem translatePathTiles :
    (by
      classical
      exact
        (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, ∀ (u : GaussianInt), (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween (GaussianTranslation u '' V) ((fun e : Finset GaussianInt =>
            e.image (GaussianTranslation u)) '' E) (GaussianTranslation u x) (GaussianTranslation
            u y))) → (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (u : GaussianInt), ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, (SimpleGridPathBetween (FootprintVertices X ∩
            FootprintVertices Y)
            (FootprintEdges X ∩ FootprintEdges Y) x y) → (SimpleGridPathBetween
                (FootprintVertices (TileTranslation X u) ∩ FootprintVertices (TileTranslation Y
                u)) (FootprintEdges (TileTranslation X u) ∩ FootprintEdges (TileTranslation Y u))
                (GaussianTranslation u x) (GaussianTranslation u y))) ) := by
  classical
  intro translatedPath X Y u x y hp
  have hinj : Function.Injective (GaussianTranslation u) := by
    intro a b hab
    exact add_right_cancel hab
  have heinj : Function.Injective
      (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) :=
    Finset.image_injective hinj
  have hi := translatedPath u hp
  rw [Set.image_inter hinj, Set.image_inter heinj] at hi
  simpa only [(TileTranslationFormulas X u).2.2.2.2.2.1,
    (TileTranslationFormulas Y u).2.2.2.2.2.1,
    (TileTranslationFormulas X u).2.2.2.2.2.2.1,
    (TileTranslationFormulas Y u).2.2.2.2.2.2.1] using hi

private theorem translateComp :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), TileTranslation
            (TileTranslation T u) v = TileTranslation T (u + v) ) := by
  classical
  intro T u v
  cases T with
  | mk cells anchor =>
    apply congrArg₂ ProtoTile.mk
    · simp only [TileTranslation]
      rw [Finset.image_image]
      congr 1
      funext z
      simp [GaussianTranslation, add_comm, add_left_comm]
    · simp [TileTranslation, GaussianTranslation, add_comm,
        add_left_comm]

private theorem hEmShift :
    (by
      classical
      exact
        ∀ (k : Nat),
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let Em := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
        (∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), TileTranslation
            (TileTranslation T u) v = TileTranslation T (u + v)) → (
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        TileTranslation Em shiftR = W) ) := by
  classical
  intro k W Em translateComp shiftR
  rw [show Em = TileTranslation (DiamondTile (k - 1))
    ⟨-(k : Int), 1 - (k : Int)⟩ by rfl,
    translateComp]
  congr 1
  apply Zsqrtd.ext <;> simp [shiftR]; omega

private theorem pathRBC :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let Em := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices Em) (FootprintEdges D ∩
            FootprintEdges Em) (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) 0)
            (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N)) → ((∀ (X :
            ProtoTile), ∀ (Y : ProtoTile), ∀ (u : GaussianInt), ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, (SimpleGridPathBetween (FootprintVertices X ∩ FootprintVertices Y)
            (FootprintEdges X ∩ FootprintEdges Y) x y) → (SimpleGridPathBetween
            (FootprintVertices (TileTranslation X u) ∩ FootprintVertices (TileTranslation Y u))
            (FootprintEdges (TileTranslation X u) ∩ FootprintEdges (TileTranslation Y u))
            (GaussianTranslation u x) (GaussianTranslation u y))) → (
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        (TileTranslation Em shiftR = W) → (SimpleGridPathBetween (FootprintVertices
            (TileTranslation D shiftR) ∩ FootprintVertices W) (FootprintEdges (TileTranslation D
            shiftR) ∩ FootprintEdges W) (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true
            (-1) 0 + shiftR) (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N +
            shiftR)))) ) := by
  classical
  intro k N D W Em pathDEm translatePathTiles shiftR hEmShift
  have hpath := translatePathTiles D Em shiftR pathDEm
  rw [hEmShift] at hpath
  simpa only [GaussianTranslation] using hpath

private theorem hpStart :
    (by
      classical
      exact
        P5157T1StaircasePoint 1 false 1 0 = 1 ) := by
  classical
  apply Zsqrtd.ext_iff.mpr
  constructor <;> simp [P5157T1StaircasePoint]

private theorem hpEnd :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → (
        let N : Nat := 2 * (k - 1)
        P5157T1StaircasePoint 1 false 1 N = ⟨(k : Int), (k : Int) - 1⟩) ) := by
  classical
  intro k hk N
  apply Zsqrtd.ext_iff.mpr
  constructor <;> simp [P5157T1StaircasePoint, N] <;> omega

private theorem hqStart :
    (by
      classical
      exact
        P5157T1StaircasePoint 1 false (-1) 0 = 1 ) := by
  classical
  apply Zsqrtd.ext_iff.mpr
  constructor <;> simp [P5157T1StaircasePoint]

private theorem hqEnd :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → (
        let N : Nat := 2 * (k - 1)
        P5157T1StaircasePoint 1 false (-1) N = ⟨(k : Int), 1 - (k : Int)⟩) ) := by
  classical
  intro k hk N
  apply Zsqrtd.ext_iff.mpr
  constructor <;> simp [P5157T1StaircasePoint, N] <;> omega

private theorem htStart :
    (by
      classical
      exact
        ∀ (k : Nat),
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        GaussianTranslation shiftR (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
            0) = ⟨(k : Int), (k : Int) - 1⟩ ) := by
  classical
  intro k shiftR
  apply Zsqrtd.ext <;> simp [GaussianTranslation, P5157T1StaircasePoint,
    shiftR]; omega

private theorem htEnd :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → (
        let N : Nat := 2 * (k - 1)
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        GaussianTranslation shiftR (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1)
            N) = ⟨2 * (k : Int) - 1, 0⟩) ) := by
  classical
  intro k hk N shiftR
  apply Zsqrtd.ext <;> simp [GaussianTranslation, P5157T1StaircasePoint,
    shiftR, N] <;> omega

private theorem pathWD :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D ∩
            FootprintEdges W) (P5157T1StaircasePoint 1 false 1 0) (P5157T1StaircasePoint 1
            false 1 N)) → (SimpleGridPathBetween (FootprintVertices W ∩ FootprintVertices D)
            (FootprintEdges W ∩ FootprintEdges D) (P5157T1StaircasePoint 1 false 1 0)
            (P5157T1StaircasePoint 1 false 1 N)) ) := by
  classical
  intro k N D W pathDW
  simpa only [Set.inter_comm] using pathDW

private theorem pathWDrev :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween V E y x)) → (
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D ∩
            FootprintEdges W) (P5157T1StaircasePoint 1 false 1 0) (P5157T1StaircasePoint 1
            false 1 N)) → (SimpleGridPathBetween (FootprintVertices W ∩ FootprintVertices D)
            (FootprintEdges W ∩ FootprintEdges D) (P5157T1StaircasePoint 1 false 1 N)
            (P5157T1StaircasePoint 1 false 1 0))) ) := by
  classical
  intro k reversePath N D W pathDW
  simpa only [Set.inter_comm] using reversePath pathDW

private theorem translateZero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), TileTranslation T 0 = T ) := by
  classical
  intro T
  cases T with
  | mk cells anchor =>
    apply congrArg₂ ProtoTile.mk
    · change Finset.image (fun z => z + (0 : GaussianInt)) cells = cells
      simp
    · simp [GaussianTranslation]

private theorem hlowTile :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (∀ (T : ProtoTile), TileTranslation T 0 = T) → (
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (shiftLow + ⟨0, 2 * (k : Int)⟩ = 0) → (TileTranslation D (shiftLow + ⟨0, 2 * (k : Int)⟩)
            = D)) ) := by
  classical
  intro k D translateZero shiftLow hlowZero
  rw [hlowZero]
  exact translateZero D

private theorem pathDL :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween V E y x)) → (
        let D := DiamondTile k
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (SimpleGridPathBetween (FootprintVertices (TileTranslation (DiamondTile k) shiftLow) ∩
            FootprintVertices D) (FootprintEdges (TileTranslation (DiamondTile k) shiftLow) ∩
            FootprintEdges D) (shiftLow + (⟨(-1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))
            (shiftLow + (⟨(1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))) → (SimpleGridPathBetween
            (FootprintVertices D ∩ FootprintVertices L) (FootprintEdges D ∩ FootprintEdges L)
            (shiftLow + ⟨1, 2 * (k : Int)⟩) (shiftLow + ⟨-1, 2 * (k : Int)⟩))) ) := by
  classical
  intro k reversePath D L shiftLow pathLow
  simpa only [Set.inter_comm, L] using reversePath pathLow

private theorem huEq :
    (by
      classical
      exact
        ∀ (k : Nat), ∀ (u : GaussianInt), (((GaussianInt.toComplex : GaussianInt → ℂ) u).re = (↑k
            : ℝ) ∧ ((GaussianInt.toComplex : GaussianInt → ℂ) u).im = (↑k : ℝ)) → (u = ⟨(k :
            Int), (k : Int)⟩) ) := by
  classical
  intro k u hu
  rcases hu with ⟨hre, him⟩
  apply Zsqrtd.ext
  · have h : (u.re : Int) = k := by
      rw [← GaussianInt.intCast_re u] at hre
      exact_mod_cast hre
    exact h
  · have h : (u.im : Int) = k := by
      rw [← GaussianInt.intCast_im u] at him
      exact_mod_cast him
    exact h

private theorem F_inj :
    (by
      classical
      exact
        (Nat) → (∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        Function.Injective F) ) := by
  classical
  intro k u Q F a b hab
  have hq : Q a = Q b := add_right_cancel hab
  apply Zsqrtd.ext
  · have h := congrArg (fun z : GaussianInt => z.im) hq
    simpa [Q, GaussianQuarterTurn] using h
  · have h := congrArg (fun z : GaussianInt => z.re) hq
    have h' : -a.im = -b.im := by simpa [Q, GaussianQuarterTurn] using h
    omega

private theorem F_step :
    (by
      classical
      exact
        (Nat) → (∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        ∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨ b = a - ⟨0, 1⟩) → (F b = F
            a + 1 ∨ F b = F a - 1 ∨ F b = F a + ⟨0, 1⟩ ∨ F b = F a - ⟨0, 1⟩)) ) := by
  classical
  intro k u Q F a b hab
  rcases hab with h | h | h | h
  · subst b; right; right; left; apply Zsqrtd.ext <;> simp [F, Q, GaussianQuarterTurn]; omega
  · subst b; right; right; right; apply Zsqrtd.ext <;> simp [F, Q, GaussianQuarterTurn];
      omega
  · subst b; right; left; apply Zsqrtd.ext <;> simp [F, Q, GaussianQuarterTurn]; omega
  · subst b; left; apply Zsqrtd.ext <;> simp [F, Q, GaussianQuarterTurn]; omega

private theorem quarterVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        ∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        ∀ (d : GaussianInt), F '' FootprintVertices (TileTranslation D d) = FootprintVertices
            (TileTranslation (TileQuarterTurn D) (u + Q d)) ) := by
  classical
  intro k D u Q F d
  rw [(TileTranslationFormulas D d).2.2.2.2.2.1,
    (TileTranslationFormulas (TileQuarterTurn D) (u + Q d)).2.2.2.2.2.1,
    (TileQuarterTurnFormulas D).2.2.2.2.2.1]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  simp [F, Q, GaussianTranslation, GaussianQuarterTurn, add_assoc, add_comm,
    ]

private theorem quarterEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        ∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        ∀ (d : GaussianInt), (fun e : Finset GaussianInt => e.image F) '' FootprintEdges
            (TileTranslation D d) = FootprintEdges (TileTranslation (TileQuarterTurn D) (u + Q
            d)) ) := by
  classical
  intro k D u Q F d
  rw [(TileTranslationFormulas D d).2.2.2.2.2.2.1,
    (TileTranslationFormulas (TileQuarterTurn D) (u + Q d)).2.2.2.2.2.2.1,
    (TileQuarterTurnFormulas D).2.2.2.2.2.2.1]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext e
  ext z
  simp [F, Q, GaussianTranslation, GaussianQuarterTurn,
    add_comm, add_left_comm]

private theorem quarterBaseVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        ∀ (u : GaussianInt), (FootprintVertices (TileTranslation (TileQuarterTurn D) u) =
            FootprintVertices D) → (FootprintVertices (TileTranslation (TileQuarterTurn D) u) =
            FootprintVertices D) ) := by
  classical
  intro k D u hquarterVertices
  exact hquarterVertices

private theorem quarterBaseEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        ∀ (u : GaussianInt), ((TileTranslation (TileQuarterTurn D) u).cells = D.cells) →
            (FootprintEdges (TileTranslation (TileQuarterTurn D) u) = FootprintEdges D) ) := by
  classical
  intro k D u hquarterCells
  unfold FootprintEdges
  rw [hquarterCells]

private theorem quarterCellsAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (∀ (T : ProtoTile), ∀ (u : GaussianInt), ∀ (v : GaussianInt), TileTranslation
            (TileTranslation T u) v = TileTranslation T (u + v)) → (∀ (u : GaussianInt),
            ((TileTranslation (TileQuarterTurn D) u).cells = D.cells) → (∀ (d : GaussianInt),
            (TileTranslation (TileQuarterTurn D) (u + d)).cells = (TileTranslation D d).cells)) )
            := by
  classical
  intro k D translateComp u hquarterCells d
  rw [← translateComp (TileQuarterTurn D) u d]
  rw [(TileTranslationFormulas (TileTranslation (TileQuarterTurn D) u) d).1,
    (TileTranslationFormulas D d).1, hquarterCells]

private theorem quarterVerticesAt :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (m : Nat), (0 < m) → (∀ (u : GaussianInt), (TileTranslation (DiamondTile
            m) u).cells.Nonempty)) → ((0 < k) → (
        let D := DiamondTile k
        ∀ (u : GaussianInt), (∀ (d : GaussianInt), (TileTranslation (TileQuarterTurn D) (u +
            d)).cells = (TileTranslation D d).cells) → (∀ (d : GaussianInt), FootprintVertices
            (TileTranslation (TileQuarterTurn D) (u + d)) = FootprintVertices (TileTranslation D
            d)))) ) := by
  classical
  intro k translatedDiamondCellsNonempty hkpos D u quarterCellsAt d
  have hne : (TileTranslation D d).cells.Nonempty :=
    translatedDiamondCellsNonempty k hkpos d
  unfold FootprintVertices
  rw [ite_eq_left (by rw [quarterCellsAt d]; exact hne), ite_eq_left hne,
    quarterCellsAt d]

private theorem quarterEdgesAt :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        ∀ (u : GaussianInt), (∀ (d : GaussianInt), (TileTranslation (TileQuarterTurn D) (u +
            d)).cells = (TileTranslation D d).cells) → (∀ (d : GaussianInt), FootprintEdges
            (TileTranslation (TileQuarterTurn D) (u + d)) = FootprintEdges (TileTranslation D d))
            ) := by
  classical
  intro k D u quarterCellsAt d
  simp only [FootprintEdges, quarterCellsAt d]

private theorem pathRAB0 :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        (∀ (T : ProtoTile), TileTranslation T 0 = T) → (
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (SimpleGridPathBetween (FootprintVertices (TileTranslation (DiamondTile k) shiftLow) ∩
            FootprintVertices D) (FootprintEdges (TileTranslation (DiamondTile k) shiftLow) ∩
            FootprintEdges D) (shiftLow + (⟨(-1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))
            (shiftLow + (⟨(1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))) → (∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        (Function.Injective F) → ((∀ a b : GaussianInt, (b = a + 1 ∨ b = a - 1 ∨ b = a + ⟨0, 1⟩ ∨
            b = a - ⟨0, 1⟩) → (F b = F a + 1 ∨ F b = F a - 1 ∨ F b = F a + ⟨0, 1⟩ ∨ F b = F a -
            ⟨0, 1⟩)) → ((∀ (d : GaussianInt), F '' FootprintVertices (TileTranslation D d) =
            FootprintVertices (TileTranslation (TileQuarterTurn D) (u + Q d))) → ((∀ (d :
            GaussianInt), (fun e : Finset GaussianInt => e.image F) '' FootprintEdges
            (TileTranslation D d) = FootprintEdges (TileTranslation (TileQuarterTurn D) (u + Q
            d))) → ((FootprintVertices (TileTranslation (TileQuarterTurn D) u) =
            FootprintVertices D) → ((FootprintEdges (TileTranslation (TileQuarterTurn D) u) =
            FootprintEdges D) → ((∀ (d : GaussianInt), FootprintVertices (TileTranslation
            (TileQuarterTurn D) (u + d)) = FootprintVertices (TileTranslation D d)) → ((∀ (d :
            GaussianInt), FootprintEdges (TileTranslation (TileQuarterTurn D) (u + d)) =
            FootprintEdges (TileTranslation D d)) → ((Q shiftLow = shiftR) →
            (SimpleGridPathBetween (FootprintVertices (TileTranslation D shiftR) ∩
            FootprintVertices D) (FootprintEdges (TileTranslation D shiftR) ∩ FootprintEdges D)
            (F (shiftLow + ⟨-1, 2 * (k : Int)⟩)) (F (shiftLow + ⟨1, 2 * (k : Int)⟩))))))))))))) )
            := by
  classical
  intro k D shiftR translateZero shiftLow pathLow u Q F F_inj F_step quarterVertices quarterEdges
      quarterBaseVertices quarterBaseEdges quarterVerticesAt quarterEdgesAt shiftQuarter
  have hi := P4055T1GridPathImage F F_inj F_step _ _ _ _ pathLow
  have hedgeInj : Function.Injective
      (fun e : Finset GaussianInt => e.image F) := Finset.image_injective F_inj
  rw [Set.image_inter F_inj, Set.image_inter hedgeInj] at hi
  rw [← translateZero D] at hi
  rw [quarterVertices shiftLow, quarterVertices 0,
    quarterEdges shiftLow, quarterEdges 0] at hi
  simp only [GaussianQuarterTurn, Int.reduceNeg, Zsqrtd.im_zero, neg_zero, Zsqrtd.re_zero, Q]
      at hi
  have hQshift : (⟨-shiftLow.im, shiftLow.re⟩ : GaussianInt) = shiftR := by
    simpa [Q, GaussianQuarterTurn] using shiftQuarter
  rw [show u + (⟨-shiftLow.im, shiftLow.re⟩ : GaussianInt) = u + shiftR by
    rw [hQshift]] at hi
  simp only [show (⟨0, 0⟩ : GaussianInt) = 0 by rfl, add_zero] at hi
  rw [quarterVerticesAt shiftR, quarterEdgesAt shiftR,
    quarterBaseVertices, quarterBaseEdges] at hi
  simpa [translateZero, Set.inter_comm] using hi

private theorem hxlow :
    (by
      classical
      exact
        ∀ (k : Nat),
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        ∀ (u : GaussianInt), (u = ⟨(k : Int), (k : Int)⟩) → (
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        F (shiftLow + ⟨-1, 2 * (k : Int)⟩) = ⟨(k : Int), (k : Int) - 1⟩) ) := by
  classical
  intro k shiftLow u huEq Q F
  dsimp [F]
  rw [huEq]
  apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn, shiftLow]; omega

private theorem hxhigh :
    (by
      classical
      exact
        ∀ (k : Nat),
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        ∀ (u : GaussianInt), (u = ⟨(k : Int), (k : Int)⟩) → (
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        F (shiftLow + ⟨1, 2 * (k : Int)⟩) = ⟨(k : Int), (k : Int) + 1⟩) ) := by
  classical
  intro k shiftLow u huEq Q F
  dsimp [F]
  rw [huEq]
  apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn, shiftLow]; omega

private theorem pathRAB :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        ∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        (SimpleGridPathBetween (FootprintVertices (TileTranslation D shiftR) ∩ FootprintVertices
            D) (FootprintEdges (TileTranslation D shiftR) ∩ FootprintEdges D) (F (shiftLow + ⟨-1,
            2 * (k : Int)⟩)) (F (shiftLow + ⟨1, 2 * (k : Int)⟩))) → ((F (shiftLow + ⟨-1, 2 * (k :
            Int)⟩) = ⟨(k : Int), (k : Int) - 1⟩) → ((F (shiftLow + ⟨1, 2 * (k : Int)⟩) = ⟨(k :
            Int), (k : Int) + 1⟩) → (SimpleGridPathBetween (FootprintVertices D ∩
            FootprintVertices (TileTranslation D shiftR)) (FootprintEdges D ∩ FootprintEdges
            (TileTranslation D shiftR)) ⟨(k : Int), (k : Int) - 1⟩ ⟨(k : Int), (k : Int) + 1⟩)))
            ) := by
  classical
  intro k D shiftR shiftLow u Q F pathRAB0 hxlow hxhigh
  simpa only [Set.inter_comm, hxlow, hxhigh] using pathRAB0

private theorem capBoundaryVerticesEq :
    (by
      classical
      exact
        (Nat) → (∀ (m : Nat), (0 < m) → (∀ (v : GaussianInt), BoundaryFootprintVertices
            (TileTranslation (DiamondTile m) v) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile m) (v + ⟨0, 2 * (m : Int)⟩)) = {v + ⟨-1, 2 * (m : Int)⟩, v + ⟨0,
            2 * (m : Int)⟩, v + ⟨1, 2 * (m : Int)⟩})) ) := by
  classical
  intro k m hm v
  exact (by
    have hcap := P5203T1CapInterface m hm v
    dsimp only at hcap
    rcases hcap with ⟨_, _, _, hV, _, _⟩
    rw [hV]
    ext z
    constructor
    · rintro ⟨him, hlo, hhi⟩
      have him' : z.im - v.im = 2 * (m : Int) := by
        simpa only [Zsqrtd.im_sub] using him
      have hlo' : -1 ≤ z.re - v.re := by simpa only [Zsqrtd.re_sub] using hlo
      have hhi' : z.re - v.re ≤ 1 := by simpa only [Zsqrtd.re_sub] using hhi
      have hcase : (z - v).re = -1 ∨ (z - v).re = 0 ∨ (z - v).re = 1 := by
        omega
      rcases hcase with h | h | h
      · left
        apply Zsqrtd.ext_iff.mpr
        constructor
        · change z.re = v.re - 1
          have h' : (z - v).re = -1 := h
          simp only [Zsqrtd.re_sub] at h'
          omega
        · change z.im = v.im + 2 * (m : Int)
          have h' : (z - v).im = 2 * (m : Int) := him
          simp only [Zsqrtd.im_sub] at h'
          omega
      · right; left
        apply Zsqrtd.ext_iff.mpr
        constructor
        · change z.re = v.re + 0
          have h' : (z - v).re = 0 := h
          simp only [Zsqrtd.re_sub] at h'
          omega
        · change z.im = v.im + 2 * (m : Int)
          have h' : (z - v).im = 2 * (m : Int) := him
          simp only [Zsqrtd.im_sub] at h'
          omega
      · right; right
        apply Zsqrtd.ext_iff.mpr
        constructor
        · change z.re = v.re + 1
          have h' : (z - v).re = 1 := h
          simp only [Zsqrtd.re_sub] at h'
          omega
        · change z.im = v.im + 2 * (m : Int)
          have h' : (z - v).im = 2 * (m : Int) := him
          simp only [Zsqrtd.im_sub] at h'
          omega
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl | rfl)
      all_goals
        simp only [Set.mem_ofPred_eq, Zsqrtd.re_sub, Zsqrtd.im_sub,
          Zsqrtd.re_add, Zsqrtd.im_add]
        omega
  )

private theorem hcapLowRawVertices :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((0 < k) → (
        let D := DiamondTile k
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (Finset.Nonempty (TileTranslation (DiamondTile k) shiftLow).cells ∧ Finset.Nonempty
            (TileTranslation (DiamondTile k) (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt))).cells ∧ Disjoint (TileTranslation (DiamondTile k) shiftLow).cells
            (TileTranslation (DiamondTile k) (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt))).cells ∧ BoundaryFootprintVertices (TileTranslation (DiamondTile k)
            shiftLow) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile k) (shiftLow +
            (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))) = {z : GaussianInt | (z -
            shiftLow).im = (2 : ℤ) * (↑k : ℤ) ∧ (-1 : ℤ) ≤ (z - shiftLow).re ∧ (z - shiftLow).re
            ≤ (1 : ℤ)} ∧ BoundaryFootprintEdges (TileTranslation (DiamondTile k) shiftLow) ∩
            BoundaryFootprintEdges (TileTranslation (DiamondTile k) (shiftLow + (⟨(0 : ℤ), (2 :
            ℤ) * (↑k : ℤ)⟩ : GaussianInt))) = {e : Finset GaussianInt | ∃ (a : ℤ), (-1 : ℤ) ≤ a ∧
            a < (1 : ℤ) ∧ e = {shiftLow + (⟨a, (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt),
            shiftLow + (⟨a + (1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)}} ∧ SimpleGridPath {z :
            GaussianInt | (z - shiftLow).im = (2 : ℤ) * (↑k : ℤ) ∧ (-1 : ℤ) ≤ (z - shiftLow).re ∧
            (z - shiftLow).re ≤ (1 : ℤ)} {e : Finset GaussianInt | ∃ (a : ℤ), (-1 : ℤ) ≤ a ∧ a <
            (1 : ℤ) ∧ e = {shiftLow + (⟨a, (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt),
            shiftLow + (⟨a + (1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)}}) → ((TileTranslation D
            (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)) = D) → ((∀ (m : Nat), (0 <
            m) → (∀ (v : GaussianInt), BoundaryFootprintVertices (TileTranslation (DiamondTile m)
            v) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile m) (v + ⟨0, 2 * (m :
            Int)⟩)) = {v + ⟨-1, 2 * (m : Int)⟩, v + ⟨0, 2 * (m : Int)⟩, v + ⟨1, 2 * (m : Int)⟩}))
            → (FootprintVertices (TileTranslation D shiftLow) ∩ FootprintVertices D =
            {shiftLow + ⟨-1, 2 * (k : Int)⟩, shiftLow + ⟨0, 2 * (k : Int)⟩, shiftLow + ⟨1,
            2 * (k : Int)⟩}))))) ) := by
  classical
  intro k rawBoundaryVertices hkpos D shiftLow hcapLow hlowTile capBoundaryVerticesEq
  have hupper : TileTranslation (DiamondTile k)
      (shiftLow + ⟨0, 2 * (k : Int)⟩) = D := by
    simpa [D] using hlowTile
  have hupperNe : D.cells.Nonempty := by
    simpa only [hupper] using hcapLow.2.1
  have hlowDisj : Disjoint (TileTranslation D shiftLow).cells D.cells := by
    simpa only [hupper] using hcapLow.2.2.1
  calc
    _ = BoundaryFootprintVertices (TileTranslation D shiftLow) ∩
        BoundaryFootprintVertices D :=
      rawBoundaryVertices _ _ hcapLow.1 hupperNe hlowDisj
    _ = BoundaryFootprintVertices (TileTranslation D shiftLow) ∩
        BoundaryFootprintVertices
          (TileTranslation D (shiftLow + ⟨0, 2 * (k : Int)⟩)) := by
      exact congrArg (fun S : Set GaussianInt =>
        BoundaryFootprintVertices (TileTranslation D shiftLow) ∩ S)
          (congrArg BoundaryFootprintVertices hupper).symm
    _ = _ := capBoundaryVerticesEq k hkpos shiftLow

private theorem quarterVerticesZero :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (∀ (T : ProtoTile), TileTranslation T 0 = T) → (∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        (∀ (d : GaussianInt), F '' FootprintVertices (TileTranslation D d) = FootprintVertices
            (TileTranslation (TileQuarterTurn D) (u + Q d))) → (F '' FootprintVertices D =
            FootprintVertices (TileTranslation (TileQuarterTurn D) u))) ) := by
  classical
  intro k D translateZero u Q F quarterVertices
  have h := quarterVertices 0
  have hq0 : Q 0 = 0 := by apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn]
  simpa only [translateZero, hq0, add_zero] using h

private theorem hRABimage :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        ∀ (u : GaussianInt),
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        (Function.Injective F) → ((∀ (d : GaussianInt), F '' FootprintVertices (TileTranslation D
            d) = FootprintVertices (TileTranslation (TileQuarterTurn D) (u + Q d))) →
            ((FootprintVertices (TileTranslation (TileQuarterTurn D) u) = FootprintVertices D) →
            ((∀ (d : GaussianInt), FootprintVertices (TileTranslation (TileQuarterTurn D) (u +
            d)) = FootprintVertices (TileTranslation D d)) → ((Q shiftLow = shiftR) → ((F ''
            FootprintVertices D = FootprintVertices (TileTranslation (TileQuarterTurn D) u)) → (F
            '' (FootprintVertices (TileTranslation D shiftLow) ∩ FootprintVertices D) =
            FootprintVertices (TileTranslation D shiftR) ∩ FootprintVertices D)))))) ) := by
  classical
  intro k D shiftR shiftLow u Q F F_inj quarterVertices quarterBaseVertices quarterVerticesAt
      shiftQuarter quarterVerticesZero
  rw [Set.image_inter F_inj, quarterVertices shiftLow, quarterVerticesZero]
  simp only [Q, GaussianQuarterTurn]
  rw [show u + (⟨-shiftLow.im, shiftLow.re⟩ : GaussianInt) = u + shiftR by
    rw [show (⟨-shiftLow.im, shiftLow.re⟩ : GaussianInt) = shiftR by
      simpa [Q, GaussianQuarterTurn] using shiftQuarter]]
  rw [quarterVerticesAt shiftR, quarterBaseVertices]

private theorem hRABraw :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        ∀ (u : GaussianInt), (u = ⟨(k : Int), (k : Int)⟩) → (
        let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
        let F : GaussianInt → GaussianInt := fun z => Q z + u
        (F (shiftLow + ⟨-1, 2 * (k : Int)⟩) = ⟨(k : Int), (k : Int) - 1⟩) → ((F (shiftLow + ⟨1, 2
            * (k : Int)⟩) = ⟨(k : Int), (k : Int) + 1⟩) → ((FootprintVertices (TileTranslation D
            shiftLow) ∩ FootprintVertices D = {shiftLow + ⟨-1, 2 * (k : Int)⟩, shiftLow + ⟨0,
            2 * (k : Int)⟩, shiftLow + ⟨1, 2 * (k : Int)⟩}) → ((F '' (FootprintVertices
            (TileTranslation D shiftLow) ∩ FootprintVertices D) = FootprintVertices
            (TileTranslation D shiftR) ∩ FootprintVertices D) → (FootprintVertices D ∩
            FootprintVertices (TileTranslation D shiftR) = {⟨(k : Int), (k : Int) - 1⟩,
            ⟨(k : Int), (k : Int)⟩, ⟨(k : Int), (k : Int) + 1⟩}))))) ) := by
  classical
  intro k D shiftR shiftLow u huEq Q F hxlow hxhigh hcapLowRawVertices hRABimage
  rw [Set.inter_comm, ← hRABimage, hcapLowRawVertices]
  have hmid : F (shiftLow + ⟨0, 2 * (k : Int)⟩) =
      ⟨(k : Int), (k : Int)⟩ := by
    dsimp [F]
    rw [huEq]
    apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn, shiftLow]
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    hxlow, hmid, hxhigh]

private theorem hcontactCell :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → ((⟨(k : Int), 1 - (k : Int)⟩ : GaussianInt) + ⟨-((k - 1 :
            Nat) : Int) - 1, (k : Int) - 2⟩ = ⟨0, -1⟩) ) := by
  classical
  intro k hk
  apply Zsqrtd.ext <;> simp; omega

private theorem hUne :
    (by
      classical
      exact
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        U.cells.Nonempty ) := by
  classical
  intro U
  refine ⟨⟨0, -1⟩, ?_⟩
  simp [U]

private theorem hWUv' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (BoundaryFootprintVertices (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 :
            ℤ) - (↑k : ℤ)⟩ : GaussianInt)) ∩ BoundaryFootprintVertices (⟨{(⟨(0 : ℤ),
            (-1 : ℤ)⟩ : GaussianInt)}, (⟨(0 : ℤ), (-1 : ℤ)⟩ : GaussianInt)⟩ : ProtoTile) =
            {(⟨(0 : ℤ), (-1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt), (⟨(0 : ℤ),
            (-1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)}) →
            (BoundaryFootprintVertices W ∩ BoundaryFootprintVertices U = {1 + ⟨0, -1⟩, 1 + ⟨0,
            0⟩}) ) := by
  classical
  intro k W U hWUv
  simpa [U, W, add_comm, add_assoc, add_left_comm] using hWUv

private theorem hWedge' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        ({(⟨(0 : ℤ), (-1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt), (⟨(0 : ℤ),
            (-1 : ℤ)⟩ : GaussianInt) + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)} ∈
            BoundaryFootprintEdges (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 :
            ℤ) - (↑k : ℤ)⟩ : GaussianInt))) → (({1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩} : Finset GaussianInt) ∈
            BoundaryFootprintEdges W) ) := by
  classical
  intro k W hWUedge
  simpa [W, add_comm, add_assoc, add_left_comm] using hWUedge

private theorem hUedge' :
    (by
      classical
      exact
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        ({1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U ) := by
  classical
  intro U
  have hsing := P5253T1SingletonBoundary ⟨0, -1⟩ ⟨0, -1⟩
  rw [hsing.2]
  simp [Finset.pair_comm, add_comm, add_left_comm]

private theorem hWUpath :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (FootprintEdges
            X ∩ FootprintEdges Y = BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y)) → ((∀ (V
            : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (x ≠ y) → ((V = {x, y}) → ((E = {{x, y}}) → ((y = x + 1 ∨ y = x - 1 ∨ y
            = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) → (SimpleGridPathBetween V E x y))))) → (
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (Finset.Nonempty (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k :
            ℤ)⟩ : GaussianInt)).cells) → ((Disjoint W.cells U.cells) → ((U.cells.Nonempty) →
            ((BoundaryFootprintVertices W ∩ BoundaryFootprintVertices U = {1 + ⟨0, -1⟩, 1 + ⟨0,
            0⟩}) → ((({1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges W)
            → ((({1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩} : Finset GaussianInt) ∈ BoundaryFootprintEdges U) →
            (SimpleGridPathBetween (FootprintVertices W ∩ FootprintVertices U) (FootprintEdges W
            ∩ FootprintEdges U) (1 + ⟨0, -1⟩) (1 + ⟨0, 0⟩)))))))))) ) := by
  classical
  intro k rawBoundaryVertices rawBoundaryEdges twoVertexPath W U hWne hWUdisj hUne hWUv' hWedge'
      hUedge'
  have hone := P5253T1OneEdgeInterface W U (1 + ⟨0, -1⟩) (1 + ⟨0, 0⟩)
    hWne hUne hWUdisj hWUv' hWedge' hUedge'
    (by right; right; left; apply Zsqrtd.ext <;> simp)
  have hV : FootprintVertices W ∩ FootprintVertices U =
      {1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩} := by
    rw [rawBoundaryVertices W U hWne hUne hWUdisj, hWUv']
  have hE : FootprintEdges W ∩ FootprintEdges U =
      {{1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩}} := by
    rw [rawBoundaryEdges W U hWUdisj]
    exact hone.1
  exact twoVertexPath _ _ _ _ (by norm_num [Zsqrtd.ext_iff]) hV hE
    (by right; right; left; apply Zsqrtd.ext <;> simp)

private theorem hDUv :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        (∀ (T : ProtoTile), TileTranslation T 0 = T) → (
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (Finset.Nonempty (TileTranslation (DiamondTile k) (0 : GaussianInt)).cells ∧ Disjoint
            (TileTranslation (DiamondTile k) (0 : GaussianInt)).cells {(⟨(0 : ℤ),
            (-1 : ℤ)⟩ : GaussianInt)} ∧ BoundaryFootprintVertices (TileTranslation (DiamondTile
            k) (0 : GaussianInt)) ∩ BoundaryFootprintVertices (⟨{(⟨(0 : ℤ),
            (-1 : ℤ)⟩ : GaussianInt)}, (⟨(0 : ℤ), (-1 : ℤ)⟩ : GaussianInt)⟩ : ProtoTile) =
            {(0 : GaussianInt), (0 : GaussianInt) + (1 : GaussianInt)} ∧ {(0 : GaussianInt),
            (0 : GaussianInt) + (1 : GaussianInt)} ∈ BoundaryFootprintEdges (TileTranslation
            (DiamondTile k) (0 : GaussianInt))) → (BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices U = {0, 0 + 1})) ) := by
  classical
  intro k D translateZero U hbot
  simpa [D, U, translateZero] using hbot.2.2.1

private theorem hUedgeBot :
    (by
      classical
      exact
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        {0, 1} ∈ BoundaryFootprintEdges U ) := by
  classical
  intro U
  have hsing := P5253T1SingletonBoundary ⟨0, -1⟩ ⟨0, -1⟩
  have hmem : ({0, 0 + 1} : Finset GaussianInt) ∈
      BoundaryFootprintEdges U := by
    rw [hsing.2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    right
    right
    left
    ext z; simp [Zsqrtd.ext_iff]
  exact hmem

private theorem hDUpath :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((∀ (X : ProtoTile), ∀ (Y : ProtoTile), (Disjoint X.cells Y.cells) → (FootprintEdges
            X ∩ FootprintEdges Y = BoundaryFootprintEdges X ∩ BoundaryFootprintEdges Y)) → ((∀ (V
            : Set GaussianInt), ∀ (E : Set (Finset GaussianInt)), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), (x ≠ y) → ((V = {x, y}) → ((E = {{x, y}}) → ((y = x + 1 ∨ y = x - 1 ∨ y
            = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩) → (SimpleGridPathBetween V E x y))))) → ((∀ (m : Nat),
            (0 < m) → ((DiamondTile m).cells.Nonempty)) → ((0 < k) → (
        let D := DiamondTile k
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (U.cells.Nonempty) → ((Disjoint D.cells U.cells) → ((BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices U = {0, 1}) → (({0, 1} ∈ BoundaryFootprintEdges D) → (({0,
            1} ∈ BoundaryFootprintEdges U) → (SimpleGridPathBetween (FootprintVertices D ∩
            FootprintVertices U) (FootprintEdges D ∩ FootprintEdges U) 0 1)))))))))) ) := by
  classical
  intro k rawBoundaryVertices rawBoundaryEdges twoVertexPath diamondCellsNonempty hkpos D U hUne
      hDULdisj hDUv' hDUedge' hUedgeBot'
  have hone := P5253T1OneEdgeInterface D U 0 1
    (diamondCellsNonempty k hkpos) hUne hDULdisj hDUv'
    hDUedge' hUedgeBot' (by left; simp)
  have hV : FootprintVertices D ∩ FootprintVertices U = {0, 1} := by
    rw [rawBoundaryVertices D U (diamondCellsNonempty k hkpos) hUne hDULdisj,
      hDUv']
  have hE : FootprintEdges D ∩ FootprintEdges U = {{0, 1}} := by
    rw [rawBoundaryEdges D U hDULdisj]
    exact hone.1
  exact twoVertexPath _ _ _ _ (by norm_num [Zsqrtd.ext_iff]) hV hE
    (by left; simp)

private theorem hDLboundary :
    (by
      classical
      exact
        ∀ (k : Nat), (0 < k) → (
        let D := DiamondTile k
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (TileTranslation D (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)) = D) → ((∀
            (m : Nat), (0 < m) → (∀ (v : GaussianInt), BoundaryFootprintVertices (TileTranslation
            (DiamondTile m) v) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile m) (v +
            ⟨0, 2 * (m : Int)⟩)) = {v + ⟨-1, 2 * (m : Int)⟩, v + ⟨0, 2 * (m : Int)⟩, v + ⟨1,
            2 * (m : Int)⟩})) → (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices L =
            {shiftLow + ⟨-1, 2 * (k : Int)⟩, shiftLow + ⟨0, 2 * (k : Int)⟩, shiftLow + ⟨1,
            2 * (k : Int)⟩}))) ) := by
  classical
  intro k hkpos D L shiftLow hlowTile capBoundaryVerticesEq
  have hupper : TileTranslation (DiamondTile k)
      (shiftLow + ⟨0, 2 * (k : Int)⟩) = D := by
    simpa [D] using hlowTile
  have h := capBoundaryVerticesEq k hkpos shiftLow
  rw [hupper] at h
  calc
    _ = BoundaryFootprintVertices L ∩ BoundaryFootprintVertices D := by
      exact Set.inter_comm _ _
    _ = {shiftLow + ⟨-1, 2 * (k : Int)⟩,
        shiftLow + ⟨0, 2 * (k : Int)⟩, shiftLow + ⟨1, 2 * (k : Int)⟩} := by
      simpa [L] using h

private theorem hcapRight :
    (by
      classical
      exact
        ∀ (k : Nat),
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (1 : GaussianInt) = shiftLow + ⟨1, 2 * (k : Int)⟩ ) := by
  classical
  intro k shiftLow
  apply Zsqrtd.ext <;> simp [shiftLow]

private theorem hyDL :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (BoundaryFootprintVertices D ∩ BoundaryFootprintVertices L = {shiftLow + ⟨-1,
            2 * (k : Int)⟩, shiftLow + ⟨0, 2 * (k : Int)⟩, shiftLow + ⟨1, 2 * (k : Int)⟩}) → (((1
            : GaussianInt) = shiftLow + ⟨1, 2 * (k : Int)⟩) → ((1 : GaussianInt) ∈
            BoundaryFootprintVertices D ∩ BoundaryFootprintVertices L)) ) := by
  classical
  intro k D L shiftLow hDLboundary hcapRight
  rw [hDLboundary]
  simp [hcapRight]

private theorem hyDW :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (BoundaryFootprintVertices (DiamondTile k) ∩ BoundaryFootprintVertices (TileTranslation
            (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v :
            GaussianInt | ∃ j ≤ (2 : ℕ) * (k - (1 : ℕ)), v = P5157T1StaircasePoint (1 :
            GaussianInt) false (1 : ℤ) j}) → ((1 : GaussianInt) ∈ BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices W) ) := by
  classical
  intro k D W hDWv
  rw [hDWv]
  exact ⟨0, Nat.zero_le _,
    by simp [P5157T1StaircasePoint, Zsqrtd.ext_iff]⟩

private theorem hyLW :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (BoundaryFootprintVertices (TileTranslation (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k :
            ℤ))⟩ : GaussianInt)) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile (k -
            (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v : GaussianInt | ∃ j ≤
            (2 : ℕ) * (k - (1 : ℕ)), v = P5157T1StaircasePoint (1 : GaussianInt) false (-1 : ℤ)
            j}) → ((1 : GaussianInt) ∈ BoundaryFootprintVertices L ∩ BoundaryFootprintVertices W)
            ) := by
  classical
  intro k D W L hLWv
  rw [hLWv]
  exact ⟨0, Nat.zero_le _,
    by simp [P5157T1StaircasePoint, Zsqrtd.ext_iff]⟩

private theorem hsmallI :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (
        let D := DiamondTile k; TouchingTriple D (TileTranslation D (⟨(0 : ℤ), -((2 : ℤ) * (↑k :
            ℤ))⟩ : GaussianInt)) (P5124T1ParentModel k (2 : Fin (3 : ℕ)) true) ∧ TouchingTriple
            D (P5124T1ParentModel k (1 : Fin (3 : ℕ)) true) (P5124T1ParentModel k (2 : Fin (3
            : ℕ)) false) ∧ TouchingTriple D (P5124T1ParentModel k (2 : Fin (3 : ℕ)) true)
            (P5124T1ParentModel k (0 : Fin (3 : ℕ)) false)) → (TouchingTriple D L W) ) := by
  classical
  intro k D W L hsmallTriple
  change TouchingTriple D L W ∧ _ ∧ _ at hsmallTriple
  exact hsmallTriple.1

private theorem hIboundaryUnique :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        ((1 : GaussianInt) ∈ BoundaryFootprintVertices D ∩ BoundaryFootprintVertices L) → (((1 :
            GaussianInt) ∈ BoundaryFootprintVertices L ∩ BoundaryFootprintVertices W) →
            ((TouchingTriple D L W) → (∀ z, (z ∈ BoundaryFootprintVertices D ∧ z ∈
            BoundaryFootprintVertices L ∧ z ∈ BoundaryFootprintVertices W) ↔ z = 1))) ) := by
  classical
  intro k D W L hyDL hyLW hsmallI
  have huniq := hsmallI.2.2.2
  rcases huniq with ⟨p, hp, hunique⟩
  have hpOne : p = 1 := by
    have h := hunique 1 ⟨hyDL.1, hyDL.2, hyLW.2⟩
    exact h.symm
  intro z
  constructor
  · intro hz
    have h := hunique z hz
    exact h.trans hpOne
  · intro hz
    subst z
    exact ⟨hyDL.1, hyDL.2, hyLW.2⟩

private theorem Jcoordinate :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ (z : GaussianInt), J z = ⟨z.re, 2 * (k : Int) - z.im⟩ ) := by
  classical
  intro k J z
  apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]; omega

private theorem reflectedPath :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {x : GaussianInt}, ∀
            {y : GaussianInt}, (SimpleGridPathBetween V E x y) → (SimpleGridPathBetween (J '' V)
            ((fun e : Finset GaussianInt => e.image J) '' E) (J x) (J y)) ) := by
  classical
  intro k J V E x y hp
  apply P4055T1GridPathImage J
  · intro a b hab
    have hR (z : GaussianInt) : GaussianReflection (GaussianReflection z) = z := by
      apply Zsqrtd.ext <;> simp [GaussianReflection]
    have hinjR : Function.Injective GaussianReflection := by
      intro u v huv
      calc
        u = GaussianReflection (GaussianReflection u) := (hR u).symm
        _ = GaussianReflection (GaussianReflection v) := congrArg GaussianReflection huv
        _ = v := hR v
    exact hinjR (add_right_cancel hab)
  · intro a b h
    rcases h with h | h | h | h
    · subst b; left; apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]
    · subst b; right; left; apply Zsqrtd.ext <;> simp [J, GaussianTranslation,
        GaussianReflection]
    · subst b; right; right; right; apply Zsqrtd.ext <;> simp [J, GaussianTranslation,
        GaussianReflection]; abel
    · subst b; right; right; left; apply Zsqrtd.ext <;> simp [J, GaussianTranslation,
        GaussianReflection]; abel
  · exact hp

private theorem Jx :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (z : GaussianInt), J z = ⟨z.re, 2 * (k : Int) - z.im⟩) → (
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        J x = ⟨(k : Int), (k : Int) + 1⟩) ) := by
  classical
  intro k J Jcoordinate x
  rw [Jcoordinate]
  apply Zsqrtd.ext
  · rfl
  · change 2 * (k : Int) - ((k : Int) - 1) = (k : Int) + 1
    ring

private theorem Jy :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (z : GaussianInt), J z = ⟨z.re, 2 * (k : Int) - z.im⟩) → (
        let y : GaussianInt := 1
        J y = ⟨1, 2 * (k : Int)⟩) ) := by
  classical
  intro k J Jcoordinate y
  rw [Jcoordinate]
  apply Zsqrtd.ext <;> simp [y]

private theorem hDWraw :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((∀ (m : Nat), (0 < m) → ((DiamondTile m).cells.Nonempty)) → ((0 < k) → (
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (Disjoint (DiamondTile k).cells (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ),
            (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)).cells) → ((BoundaryFootprintVertices (DiamondTile
            k) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k :
            ℤ), (1 : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v : GaussianInt | ∃ j ≤ (2 : ℕ) * (k - (1
            : ℕ)), v = P5157T1StaircasePoint (1 : GaussianInt) false (1 : ℤ) j}) →
            ((Finset.Nonempty (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) -
            (↑k : ℤ)⟩ : GaussianInt)).cells) → (FootprintVertices D ∩ FootprintVertices W = {v |
            ∃ j ≤ N, v = P5157T1StaircasePoint 1 false 1 j})))))) ) := by
  classical
  intro k rawBoundaryVertices diamondCellsNonempty hkpos N D W hDWd hDWv hWne
  rw [rawBoundaryVertices D W (diamondCellsNonempty k hkpos) hWne hDWd,
    hDWv]

private theorem hLWraw :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((∀ (m : Nat), (0 < m) → (∀ (u : GaussianInt), (TileTranslation (DiamondTile m)
            u).cells.Nonempty)) → ((0 < k) → (
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (Disjoint (TileTranslation (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k : ℤ))⟩ :
            GaussianInt)).cells (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ)
            - (↑k : ℤ)⟩ : GaussianInt)).cells) → ((BoundaryFootprintVertices (TileTranslation
            (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k : ℤ))⟩ : GaussianInt)) ∩
            BoundaryFootprintVertices (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1
            : ℤ) - (↑k : ℤ)⟩ : GaussianInt)) = {v : GaussianInt | ∃ j ≤ (2 : ℕ) * (k - (1 : ℕ)),
            v = P5157T1StaircasePoint (1 : GaussianInt) false (-1 : ℤ) j}) → ((Finset.Nonempty
            (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ :
            GaussianInt)).cells) → (FootprintVertices L ∩ FootprintVertices W = {v | ∃ j ≤ N, v =
            P5157T1StaircasePoint 1 false (-1) j})))))) ) := by
  classical
  intro k rawBoundaryVertices translatedDiamondCellsNonempty hkpos N D W L hLWd hLWv hWne
  rw [rawBoundaryVertices L W (translatedDiamondCellsNonempty k hkpos _)
    hWne hLWd, hLWv]

private theorem hWURaw :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) → (
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (Finset.Nonempty (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k :
            ℤ)⟩ : GaussianInt)).cells) → ((Disjoint W.cells U.cells) → ((U.cells.Nonempty) →
            ((BoundaryFootprintVertices W ∩ BoundaryFootprintVertices U = {1 + ⟨0, -1⟩, 1 + ⟨0,
            0⟩}) → (FootprintVertices W ∩ FootprintVertices U = {1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩}))))) )
            := by
  classical
  intro k rawBoundaryVertices W U hWne hWUdisj hUne hWUv'
  rw [rawBoundaryVertices W U hWne hUne hWUdisj, hWUv']

private theorem hDURaw :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((∀ (m : Nat), (0 < m) → ((DiamondTile m).cells.Nonempty)) → ((0 < k) → (
        let D := DiamondTile k
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (U.cells.Nonempty) → ((Disjoint D.cells U.cells) → ((BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices U = {0, 1}) → (FootprintVertices D ∩ FootprintVertices U =
            {0, 1})))))) ) := by
  classical
  intro k rawBoundaryVertices diamondCellsNonempty hkpos D U hUne hDULdisj hDUv'
  rw [rawBoundaryVertices D U (diamondCellsNonempty k hkpos) hUne hDULdisj,
    hDUv']

private theorem hAunique :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (FootprintVertices W ∩ FootprintVertices U = {1 + ⟨0, -1⟩, 1 + ⟨0, 0⟩}) →
            ((FootprintVertices D ∩ FootprintVertices U = {0, 1}) → (∀ z, z ∈ FootprintVertices D
            ∩ FootprintVertices W ∩ FootprintVertices U ↔ z = 1)) ) := by
  classical
  intro k D W U hWURaw hDURaw z
  constructor
  · intro hz
    have hz' := hz
    simp only [Set.mem_inter_iff] at hz'
    have hWU : z ∈ FootprintVertices W ∩ FootprintVertices U :=
      ⟨hz'.1.2, hz'.2⟩
    have hDU : z ∈ FootprintVertices D ∩ FootprintVertices U :=
      ⟨hz'.1.1, hz'.2⟩
    rw [hWURaw] at hWU
    rw [hDURaw] at hDU
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hWU hDU
    rcases hWU with hWU | hWU
    · rcases hDU with hDU | hDU
      · have hbad : (1 + (⟨0, -1⟩ : GaussianInt)) = 0 :=
          hWU.symm.trans hDU
        norm_num [Zsqrtd.ext_iff] at hbad
      · have hbad : (1 + (⟨0, -1⟩ : GaussianInt)) = 1 :=
          hWU.symm.trans hDU
        norm_num [Zsqrtd.ext_iff] at hbad
    · rcases hDU with hDU | hDU
      · have hbad : (1 : GaussianInt) = 0 := hWU.symm.trans hDU
        norm_num [Zsqrtd.ext_iff] at hbad
      · exact hDU
  · intro hz
    subst z
    have hWU : (1 : GaussianInt) ∈ FootprintVertices W ∩ FootprintVertices U := by
      rw [hWURaw]
      simp [Zsqrtd.ext_iff]
    have hDU : (1 : GaussianInt) ∈ FootprintVertices D ∩ FootprintVertices U := by
      rw [hDURaw]
      simp
    exact ⟨⟨hDU.1, hWU.1⟩, hDU.2⟩

private theorem pathIAB :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices L) (FootprintEdges D ∩
            FootprintEdges L) (shiftLow + ⟨1, 2 * (k : Int)⟩) (shiftLow + ⟨-1, 2 * (k : Int)⟩)) →
            ((shiftLow + ⟨1, 2 * (k : Int)⟩ = 1) → ((shiftLow + ⟨-1, 2 * (k : Int)⟩ = -1) →
            (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices L) (FootprintEdges D
            ∩ FootprintEdges L) 1 (-1)))) ) := by
  classical
  intro k D L shiftLow pathDL hlowStart hlowEnd
  simpa only [hlowStart, hlowEnd] using pathDL

private theorem pathICA :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D ∩
            FootprintEdges W) (P5157T1StaircasePoint 1 false 1 0) (P5157T1StaircasePoint 1
            false 1 N)) → ((P5157T1StaircasePoint 1 false 1 0 = 1) → ((P5157T1StaircasePoint
            1 false 1 N = ⟨(k : Int), (k : Int) - 1⟩) → (
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        SimpleGridPathBetween (FootprintVertices W ∩ FootprintVertices D) (FootprintEdges W ∩
            FootprintEdges D) 1 x))) ) := by
  classical
  intro k N D W pathDW hpStart hpEnd x
  simpa only [Set.inter_comm, hpStart, hpEnd, x] using pathDW

private theorem pathAAB :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D ∩
            FootprintEdges W) (P5157T1StaircasePoint 1 false 1 0) (P5157T1StaircasePoint 1
            false 1 N)) → ((P5157T1StaircasePoint 1 false 1 0 = 1) → ((P5157T1StaircasePoint
            1 false 1 N = ⟨(k : Int), (k : Int) - 1⟩) → (
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D ∩
            FootprintEdges W) 1 x))) ) := by
  classical
  intro k N D W pathDW hpStart hpEnd x
  simpa only [hpStart, hpEnd, x] using pathDW

private theorem pathABC :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween V E y x)) → (
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (SimpleGridPathBetween (FootprintVertices W ∩ FootprintVertices U) (FootprintEdges W ∩
            FootprintEdges U) (1 + ⟨0, -1⟩) (1 + ⟨0, 0⟩)) → (SimpleGridPathBetween
            (FootprintVertices W ∩ FootprintVertices U) (FootprintEdges W ∩ FootprintEdges U) 1
            (1 + ⟨0, -1⟩))) ) := by
  classical
  intro k reversePath W U hWUpath
  have hOne : (1 + ⟨0, 0⟩ : GaussianInt) = 1 := by
    apply Zsqrtd.ext <;> simp
  simpa only [hOne] using reversePath hWUpath

private theorem pathACA :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {x : GaussianInt}, ∀ {y : GaussianInt}, (SimpleGridPathBetween V E x y) →
            (SimpleGridPathBetween V E y x)) → (
        let D := DiamondTile k
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        (SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices U) (FootprintEdges D ∩
            FootprintEdges U) 0 1) → (SimpleGridPathBetween (FootprintVertices U ∩
            FootprintVertices D) (FootprintEdges U ∩ FootprintEdges D) 1 0)) ) := by
  classical
  intro k reversePath D U hDUpath
  simpa only [Set.inter_comm] using reversePath hDUpath

private theorem hRBC :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        (SimpleGridPathBetween (FootprintVertices (TileTranslation D shiftR) ∩ FootprintVertices
            W) (FootprintEdges (TileTranslation D shiftR) ∩ FootprintEdges W)
            (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) 0 + shiftR)
            (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N + shiftR)) →
            ((GaussianTranslation shiftR (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩
            true (-1) 0) = ⟨(k : Int), (k : Int) - 1⟩) → ((GaussianTranslation shiftR
            (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N) = ⟨2 * (k : Int) -
            1, 0⟩) → (
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        SimpleGridPathBetween (FootprintVertices (TileTranslation D shiftR) ∩ FootprintVertices
            W) (FootprintEdges (TileTranslation D shiftR) ∩ FootprintEdges W) x ⟨2 * (k : Int) -
            1, 0⟩))) ) := by
  classical
  intro k N D W shiftR pathRBC htStart htEnd x
  have hstart : P5157T1StaircasePoint
      ⟨-(k : Int), (k : Int) - 1⟩ true (-1) 0 + shiftR = x := by
    change GaussianTranslation shiftR
      (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) 0) = x
    exact htStart
  have hend : P5157T1StaircasePoint
      ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N + shiftR =
        ⟨2 * (k : Int) - 1, 0⟩ := by
    change GaussianTranslation shiftR
      (P5157T1StaircasePoint ⟨-(k : Int), (k : Int) - 1⟩ true (-1) N) = _
    exact htEnd
  rw [hstart, hend] at pathRBC
  exact pathRBC

private theorem hIABoundary :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (∀ z, (z ∈ BoundaryFootprintVertices D ∧ z ∈ BoundaryFootprintVertices L ∧ z ∈
            BoundaryFootprintVertices W) ↔ z = 1) → (∀ z, (z ∈ BoundaryFootprintVertices D ∧ z ∈
            BoundaryFootprintVertices L ∧ z ∈ BoundaryFootprintVertices W) ↔ z = 1) ) := by
  classical
  intro k D W L hIboundaryUnique
  exact hIboundaryUnique

private theorem hIuniqueRaw :
    (by
      classical
      exact
        ∀ (k : Nat), (∀ (X : ProtoTile), ∀ (Y : ProtoTile), (X.cells.Nonempty) →
            ((Y.cells.Nonempty) → ((Disjoint X.cells Y.cells) → (FootprintVertices X ∩
            FootprintVertices Y = BoundaryFootprintVertices X ∩ BoundaryFootprintVertices Y)))) →
            ((∀ (m : Nat), (0 < m) → ((DiamondTile m).cells.Nonempty)) → ((∀ (m : Nat), (0 < m) →
            (∀ (u : GaussianInt), (TileTranslation (DiamondTile m) u).cells.Nonempty)) → ((0 < k)
            → (
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (Disjoint (TileTranslation (DiamondTile k) (⟨(0 : ℤ), -((2 : ℤ) * (↑k : ℤ))⟩ :
            GaussianInt)).cells (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ)
            - (↑k : ℤ)⟩ : GaussianInt)).cells) → (
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        (Finset.Nonempty (TileTranslation (DiamondTile k) shiftLow).cells ∧ Finset.Nonempty
            (TileTranslation (DiamondTile k) (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt))).cells ∧ Disjoint (TileTranslation (DiamondTile k) shiftLow).cells
            (TileTranslation (DiamondTile k) (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt))).cells ∧ BoundaryFootprintVertices (TileTranslation (DiamondTile k)
            shiftLow) ∩ BoundaryFootprintVertices (TileTranslation (DiamondTile k) (shiftLow +
            (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))) = {z : GaussianInt | (z -
            shiftLow).im = (2 : ℤ) * (↑k : ℤ) ∧ (-1 : ℤ) ≤ (z - shiftLow).re ∧ (z - shiftLow).re
            ≤ (1 : ℤ)} ∧ BoundaryFootprintEdges (TileTranslation (DiamondTile k) shiftLow) ∩
            BoundaryFootprintEdges (TileTranslation (DiamondTile k) (shiftLow + (⟨(0 : ℤ), (2 :
            ℤ) * (↑k : ℤ)⟩ : GaussianInt))) = {e : Finset GaussianInt | ∃ (a : ℤ), (-1 : ℤ) ≤ a ∧
            a < (1 : ℤ) ∧ e = {shiftLow + (⟨a, (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt),
            shiftLow + (⟨a + (1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)}} ∧ SimpleGridPath {z :
            GaussianInt | (z - shiftLow).im = (2 : ℤ) * (↑k : ℤ) ∧ (-1 : ℤ) ≤ (z - shiftLow).re ∧
            (z - shiftLow).re ≤ (1 : ℤ)} {e : Finset GaussianInt | ∃ (a : ℤ), (-1 : ℤ) ≤ a ∧ a <
            (1 : ℤ) ∧ e = {shiftLow + (⟨a, (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt),
            shiftLow + (⟨a + (1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)}}) → ((TileTranslation D
            (shiftLow + (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)) = D) → ((Finset.Nonempty
            (TileTranslation (DiamondTile (k - (1 : ℕ))) (⟨(↑k : ℤ), (1 : ℤ) - (↑k : ℤ)⟩ :
            GaussianInt)).cells) → (((1 : GaussianInt) ∈ BoundaryFootprintVertices D ∩
            BoundaryFootprintVertices L) → ((∀ z, (z ∈ BoundaryFootprintVertices D ∧ z ∈
            BoundaryFootprintVertices L ∧ z ∈ BoundaryFootprintVertices W) ↔ z = 1) →
            ((FootprintVertices D ∩ FootprintVertices W = {v | ∃ j ≤ N, v =
            P5157T1StaircasePoint 1 false 1 j}) → (∀ z, z ∈ FootprintVertices D ∩
            FootprintVertices L ∩ FootprintVertices W ↔ z = 1))))))))))) ) := by
  classical
  intro k rawBoundaryVertices diamondCellsNonempty translatedDiamondCellsNonempty hkpos N D W L
      hLWd shiftLow hcapLow hlowTile hWne hyDL hIboundaryUnique hDWraw z
  constructor
  · intro hz
    have hz' := hz
    simp only [Set.mem_inter_iff] at hz'
    have hDL : z ∈ FootprintVertices D ∩ FootprintVertices L :=
      hz'.1
    have hLW : z ∈ FootprintVertices L ∩ FootprintVertices W :=
      ⟨hz'.1.2, hz'.2⟩
    have hcapLowDisj : Disjoint D.cells L.cells := by
      have hupper : TileTranslation (DiamondTile k)
          (shiftLow + ⟨0, 2 * (k : Int)⟩) = D := by
        simpa [D] using hlowTile
      have h' : Disjoint (TileTranslation (DiamondTile k) shiftLow).cells D.cells := by
        simpa only [hupper] using hcapLow.2.2.1
      simpa [L] using h'.symm
    rw [rawBoundaryVertices D L (diamondCellsNonempty k hkpos)
      (translatedDiamondCellsNonempty k hkpos _) hcapLowDisj] at hDL
    rw [rawBoundaryVertices L W (translatedDiamondCellsNonempty k hkpos _)
      hWne hLWd] at hLW
    exact (hIboundaryUnique z).mp ⟨hDL.1, hDL.2, hLW.2⟩
  · intro hz
    subst z
    have hupper : TileTranslation (DiamondTile k)
        (shiftLow + ⟨0, 2 * (k : Int)⟩) = D := by
      simpa [D] using hlowTile
    have hDLdisj : Disjoint D.cells L.cells := by
      have h := hcapLow.2.2.1
      rw [hupper] at h
      simpa [L] using h.symm
    have hDLraw : (1 : GaussianInt) ∈
        FootprintVertices D ∩ FootprintVertices L := by
      rw [rawBoundaryVertices D L (diamondCellsNonempty k hkpos)
        (translatedDiamondCellsNonempty k hkpos _) hDLdisj]
      exact ⟨hyDL.1, hyDL.2⟩
    exact ⟨hDLraw, (by
      have hDW : (1 : GaussianInt) ∈ FootprintVertices D ∩ FootprintVertices W := by
        rw [hDWraw]
        exact ⟨0, Nat.zero_le _, by simp [P5157T1StaircasePoint,
          Zsqrtd.ext_iff]⟩
      exact hDW.2)⟩

private theorem pImagBound :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → (
        let N : Nat := 2 * (k - 1)
        ∀ (j : Nat), (j ≤ N) → ((P5157T1StaircasePoint 1 false 1 j).im ≤ (k : Int) - 1)) ) := by
  classical
  intro k hk N j hj
  simp only [P5157T1StaircasePoint, Zsqrtd.im_add]
  dsimp [N] at hj ⊢
  omega

private theorem hRunique :
    (by
      classical
      exact
        ∀ (k : Nat),
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        (P5157T1StaircasePoint 1 false 1 N = ⟨(k : Int), (k : Int) - 1⟩) → ((FootprintVertices
            D ∩ FootprintVertices (TileTranslation D shiftR) = {⟨(k : Int), (k : Int) - 1⟩,
            ⟨(k : Int), (k : Int)⟩, ⟨(k : Int), (k : Int) + 1⟩}) → (
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        (FootprintVertices D ∩ FootprintVertices W = {v | ∃ j ≤ N, v = P5157T1StaircasePoint 1
            false 1 j}) → ((∀ (j : Nat), (j ≤ N) → ((P5157T1StaircasePoint 1 false 1 j).im ≤ (k
            : Int) - 1)) → (∀ z, z ∈ FootprintVertices D ∩ FootprintVertices (TileTranslation D
            shiftR) ∩ FootprintVertices W ↔ z = x)))) ) := by
  classical
  intro k N D W shiftR hpEnd hRABraw x hDWraw pImagBound z
  constructor
  · intro hz
    have hz' := hz
    simp only [Set.mem_inter_iff] at hz'
    have hAB : z ∈ FootprintVertices D ∩
        FootprintVertices (TileTranslation D shiftR) := ⟨hz'.1.1, hz'.1.2⟩
    have hDW : z ∈ FootprintVertices D ∩ FootprintVertices W :=
      ⟨hz'.1.1, hz'.2⟩
    rw [hRABraw] at hAB
    rw [hDWraw] at hDW
    obtain ⟨j, hj, hpoint⟩ := hDW
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAB
    rcases hAB with hab | hab | hab
    · simpa [x] using hab
    · have him : z.im = (k : Int) := by
        simpa using congrArg Zsqrtd.im hab
      have hjim : z.im ≤ (k : Int) - 1 := by
        rw [hpoint]
        exact pImagBound j hj
      omega
    · have him : z.im = (k : Int) + 1 := by
        simpa using congrArg Zsqrtd.im hab
      have hjim : z.im ≤ (k : Int) - 1 := by
        rw [hpoint]
        exact pImagBound j hj
      omega
  · intro hz
    subst z
    have hxAB : x ∈ FootprintVertices D ∩
        FootprintVertices (TileTranslation D shiftR) := by
      rw [hRABraw]
      simp [x, Zsqrtd.ext_iff]
    have hxDW : x ∈ FootprintVertices D ∩ FootprintVertices W := by
      rw [hDWraw]
      exact ⟨N, le_rfl, hpEnd.symm⟩
    exact ⟨hxAB, hxDW.2⟩

private theorem sameCellObs :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (T' : ProtoTile), (T.cells = T'.cells) → ((T.cells.Nonempty) →
            (FootprintVertices T = FootprintVertices T' ∧ FootprintEdges T = FootprintEdges T'))
            ) := by
  classical
  intro T T' hc hne
  cases T with
  | mk tc ta =>
    cases T' with
    | mk uc ua =>
      dsimp only at hc
      subst uc
      have hne' : tc.Nonempty := hne
      simp [FootprintVertices, FootprintEdges, hne]

private theorem JtranslatedVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) -
            2 * (m : Int) - s.im⟩) → (J '' FootprintVertices (TileTranslation (DiamondTile m) s)
                = FootprintVertices (TileTranslation (DiamondTile m) t))) ) := by
  classical
  intro k J m hm s t hst
  exact (P5691T1DiamondReflectionFootprints k m hm s t hst).1

private theorem JtranslatedEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) -
            2 * (m : Int) - s.im⟩) → ((fun e : Finset GaussianInt => e.image J) '' FootprintEdges
                (TileTranslation (DiamondTile m) s) = FootprintEdges (TileTranslation
                (DiamondTile m) t))) ) := by
  classical
  intro k J m hm s t hst
  exact (P5691T1DiamondReflectionFootprints k m hm s t hst).2

private theorem JtileVertices :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ (T : ProtoTile), FootprintVertices (TileTranslation (TileReflection T) ⟨0, 2 * (k :
            Int)⟩) = J '' FootprintVertices T ) := by
  classical
  intro k J T
  have ht := (TileTranslationFormulas (TileReflection T)
    ⟨0, 2 * (k : Int)⟩).2.2.2.2.2.1
  have hr := (TileReflectionFormulas T).2.2.2.2.2.1
  rw [ht, hr, Set.image_image]

private theorem JtileEdges :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ (T : ProtoTile), (fun e : Finset GaussianInt => e.image J) '' FootprintEdges T =
            FootprintEdges (TileTranslation (TileReflection T) ⟨0, 2 * (k : Int)⟩) ) := by
  classical
  intro k J T
  have ht := (TileTranslationFormulas (TileReflection T)
    ⟨0, 2 * (k : Int)⟩).2.2.2.2.2.2.1
  have hr := (TileReflectionFormulas T).2.2.2.2.2.2.1
  rw [ht, hr, Set.image_image]
  have hfun : (fun e : Finset GaussianInt => e.image J) =
      (fun e => (e.image GaussianReflection).image
        (GaussianTranslation ⟨0, 2 * (k : Int)⟩)) := by
    funext e
    rw [Finset.image_image]
    rfl
  rw [hfun]

private theorem hFalse :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → (
        let N : Nat := 2 * (k - 1)
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
        (SimpleGridPathBetween (FootprintVertices L ∩ FootprintVertices W) (FootprintEdges L ∩
            FootprintEdges W) (P5157T1StaircasePoint 1 false (-1) 0) (P5157T1StaircasePoint 1
            false (-1) N)) → (
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        (P5157T1StaircasePoint 1 false 1 0 = 1) → ((P5157T1StaircasePoint 1 false 1 N = ⟨(k :
            Int), (k : Int) - 1⟩) → ((P5157T1StaircasePoint 1 false (-1) 0 = 1) →
            ((P5157T1StaircasePoint 1 false (-1) N = ⟨(k : Int), 1 - (k : Int)⟩) →
            ((SimpleGridPathBetween (FootprintVertices W ∩ FootprintVertices D) (FootprintEdges W
            ∩ FootprintEdges D) (P5157T1StaircasePoint 1 false 1 N) (P5157T1StaircasePoint 1
            false 1 0)) → ((SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices
            (TileTranslation D shiftR)) (FootprintEdges D ∩ FootprintEdges (TileTranslation D
            shiftR)) ⟨(k : Int), (k : Int) - 1⟩ ⟨(k : Int), (k : Int) + 1⟩) → (
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        (∀ z, z ∈ FootprintVertices D ∩ FootprintVertices W ∩ FootprintVertices U ↔ z = 1) →
            ((SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices L) (FootprintEdges D
            ∩ FootprintEdges L) 1 (-1)) → ((SimpleGridPathBetween (FootprintVertices W ∩
            FootprintVertices D) (FootprintEdges W ∩ FootprintEdges D) 1 x) →
            ((SimpleGridPathBetween (FootprintVertices D ∩ FootprintVertices W) (FootprintEdges D
            ∩ FootprintEdges W) 1 x) → ((SimpleGridPathBetween (FootprintVertices W ∩
            FootprintVertices U) (FootprintEdges W ∩ FootprintEdges U) 1 (1 + ⟨0, -1⟩)) →
            ((SimpleGridPathBetween (FootprintVertices U ∩ FootprintVertices D) (FootprintEdges U
            ∩ FootprintEdges D) 1 0) → ((SimpleGridPathBetween (FootprintVertices
            (TileTranslation D shiftR) ∩ FootprintVertices W) (FootprintEdges (TileTranslation D
            shiftR) ∩ FootprintEdges W) x ⟨2 * (k : Int) - 1, 0⟩) → ((∀ z, z ∈ FootprintVertices
            D ∩ FootprintVertices L ∩ FootprintVertices W ↔ z = 1) → ((∀ z, z ∈ FootprintVertices
            D ∩ FootprintVertices (TileTranslation D shiftR) ∩ FootprintVertices W ↔ z = x) → ((
        let M := P5260T1PlacementLedger k 2 false
           let D := DiamondTile k
           ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
             ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
               ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
                 R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
                 A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
                 I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
                 M.2.2.1 ≠ M.2.2.2)))))))))))))))))) ) := by
  classical
  intro k hk N D W L pathLW shiftR hpStart hpEnd hqStart hqEnd pathWDrev pathRAB U x hAunique
      pathIAB pathICA pathAAB pathABC pathACA hRBC hIuniqueRaw hRunique
  exact (by
    dsimp [P5260T1PlacementLedger, P5124T1ParentModel]
    have pathRCA : SimpleGridPathBetween
        (FootprintVertices W ∩ FootprintVertices D)
        (FootprintEdges W ∩ FootprintEdges D) x 1 := by
      simpa only [hpStart, hpEnd, x] using pathWDrev
    have pathIBC : SimpleGridPathBetween
        (FootprintVertices L ∩ FootprintVertices W)
        (FootprintEdges L ∩ FootprintEdges W) 1
          ⟨(k : Int), 1 - (k : Int)⟩ := by
      simpa only [hqStart, hqEnd] using pathLW
    refine ⟨⟨x, ⟨(k : Int), (k : Int) + 1⟩,
      ⟨2 * (k : Int) - 1, 0⟩, 1,
      pathRAB, hRBC, pathRCA, hRunique⟩,
      ⟨⟨1, -1, ⟨(k : Int), 1 - (k : Int)⟩, x,
        pathIAB, pathIBC, pathICA, hIuniqueRaw⟩,
       ⟨⟨1, x, 1 + ⟨0, -1⟩, 0,
        pathAAB, pathABC, pathACA, hAunique⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro hxy
      have hre := congrArg Zsqrtd.re hxy
      simp [] at hre
      omega)

private theorem Jinj :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        Function.Injective J ) := by
  classical
  intro k J u v huv
  have htrans := congrArg (GaussianTranslation ⟨0, -2 * (k : Int)⟩) huv
  have href (z : GaussianInt) : GaussianReflection (GaussianReflection z) = z := by
    apply Zsqrtd.ext <;> simp [GaussianReflection]
  have hR : GaussianReflection u = GaussianReflection v := by
    simpa [J, GaussianTranslation] using htrans
  calc
    u = GaussianReflection (GaussianReflection u) := (href u).symm
    _ = GaussianReflection (GaussianReflection v) := congrArg GaussianReflection hR
    _ = v := href v

private theorem Jstep :
    (by
      classical
      exact
        ∀ (k : Nat),
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ∀ a c : GaussianInt, (c = a + 1 ∨ c = a - 1 ∨ c = a + ⟨0, 1⟩ ∨ c = a - ⟨0, 1⟩) → (J c = J
            a + 1 ∨ J c = J a - 1 ∨ J c = J a + ⟨0, 1⟩ ∨ J c = J a - ⟨0, 1⟩) ) := by
  classical
  intro k J a c h
  rcases h with h | h | h | h
  · subst c; left; apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]
  · subst c; right; left; apply Zsqrtd.ext <;> simp [J, GaussianTranslation, GaussianReflection]
  · subst c; right; right; right; apply Zsqrtd.ext <;>
      simp [J, GaussianTranslation, GaussianReflection]; omega
  · subst c; right; right; left; apply Zsqrtd.ext <;>
      simp [J, GaussianTranslation, GaussianReflection]; omega

private theorem hzero :
    (by
      classical
      exact
        ∀ (k : Nat), (0 : GaussianInt) = ⟨0, 2 * (k : Int) - 2 * (k : Int) - 0⟩ ) := by
  classical
  intro k
  apply Zsqrtd.ext <;> simp

private theorem hJDe :
    (by
      classical
      exact
        ∀ (k : Nat), (0 < k) → (
        let D := DiamondTile k
        (∀ (T : ProtoTile), TileTranslation T 0 = T) → (
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → ((fun e : Finset GaussianInt => e.image J) ''
            FootprintEdges (TileTranslation (DiamondTile m) s) = FootprintEdges (TileTranslation
            (DiamondTile m) t)))) → (((0 : GaussianInt) = ⟨0, 2 * (k : Int) - 2 * (k : Int) - 0⟩)
            → ((fun e : Finset GaussianInt => e.image J) '' FootprintEdges D = FootprintEdges
            D)))) ) := by
  classical
  intro k hkpos D translateZero J JtranslatedEdges hzero
  simpa only [translateZero] using JtranslatedEdges k hkpos 0 0 hzero

private theorem hshiftR :
    (by
      classical
      exact
        ∀ (k : Nat),
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        shiftR = ⟨shiftR.re, 2 * (k : Int) - 2 * (k : Int) - shiftR.im⟩ ) := by
  classical
  intro k shiftR
  apply Zsqrtd.ext <;> simp [shiftR]

private theorem hJRSv :
    (by
      classical
      exact
        ∀ (k : Nat), (0 < k) → (
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → (J '' FootprintVertices (TileTranslation (DiamondTile
            m) s) = FootprintVertices (TileTranslation (DiamondTile m) t)))) → ((shiftR =
            ⟨shiftR.re, 2 * (k : Int) - 2 * (k : Int) - shiftR.im⟩) → (J '' FootprintVertices
            (TileTranslation D shiftR) = FootprintVertices (TileTranslation D shiftR)))) ) := by
  classical
  intro k hkpos D shiftR J JtranslatedVertices hshiftR
  exact JtranslatedVertices k hkpos shiftR shiftR hshiftR

private theorem hJRSe :
    (by
      classical
      exact
        ∀ (k : Nat), (0 < k) → (
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → ((fun e : Finset GaussianInt => e.image J) ''
            FootprintEdges (TileTranslation (DiamondTile m) s) = FootprintEdges (TileTranslation
            (DiamondTile m) t)))) → ((shiftR = ⟨shiftR.re, 2 * (k : Int) - 2 * (k : Int) -
            shiftR.im⟩) → ((fun e : Finset GaussianInt => e.image J) '' FootprintEdges
            (TileTranslation D shiftR) = FootprintEdges (TileTranslation D shiftR)))) ) := by
  classical
  intro k hkpos D shiftR J JtranslatedEdges hshiftR
  exact JtranslatedEdges k hkpos shiftR shiftR hshiftR

private theorem hJRSe' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        ((fun e : Finset GaussianInt => e.image J) '' FootprintEdges (TileTranslation D shiftR) =
            FootprintEdges (TileTranslation D shiftR)) → (FootprintEdges (TileTranslation D
            shiftR) = (fun e : Finset GaussianInt => e.image J) '' FootprintEdges
            (TileTranslation D shiftR)) ) := by
  classical
  intro k D shiftR J hJRSe
  exact hJRSe.symm

private theorem hJDLv :
    (by
      classical
      exact
        ∀ (k : Nat), (0 < k) → (
        let D := DiamondTile k
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → (J '' FootprintVertices (TileTranslation (DiamondTile
            m) s) = FootprintVertices (TileTranslation (DiamondTile m) t)))) → (
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        J '' FootprintVertices (TileTranslation D shiftLow) = FootprintVertices (TileTranslation
            D shiftHigh))) ) := by
  classical
  intro k hkpos D shiftLow J JtranslatedVertices shiftHigh
  apply JtranslatedVertices k hkpos shiftLow shiftHigh
  apply Zsqrtd.ext <;> simp [shiftLow, shiftHigh]

private theorem hJDLe :
    (by
      classical
      exact
        ∀ (k : Nat), (0 < k) → (
        let D := DiamondTile k
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → ((fun e : Finset GaussianInt => e.image J) ''
            FootprintEdges (TileTranslation (DiamondTile m) s) = FootprintEdges (TileTranslation
            (DiamondTile m) t)))) → (
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        (fun e : Finset GaussianInt => e.image J) '' FootprintEdges (TileTranslation D shiftLow)
            = FootprintEdges (TileTranslation D shiftHigh))) ) := by
  classical
  intro k hkpos D shiftLow J JtranslatedEdges shiftHigh
  apply JtranslatedEdges k hkpos shiftLow shiftHigh
  apply Zsqrtd.ext <;> simp [shiftLow, shiftHigh]

private theorem hJDLe' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        ((fun e : Finset GaussianInt => e.image J) '' FootprintEdges (TileTranslation D shiftLow)
            = FootprintEdges (TileTranslation D shiftHigh)) → (FootprintEdges (TileTranslation D
            shiftHigh) = (fun e : Finset GaussianInt => e.image J) '' FootprintEdges
            (TileTranslation D shiftLow)) ) := by
  classical
  intro k D shiftLow J shiftHigh hJDLe
  exact hJDLe.symm

private theorem hWtopV :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → ((0 < k - 1) → (
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → (J '' FootprintVertices (TileTranslation (DiamondTile
            m) s) = FootprintVertices (TileTranslation (DiamondTile m) t)))) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        J '' FootprintVertices W = FootprintVertices Wtop))) ) := by
  classical
  intro k hk hsmall W J JtranslatedVertices Wtop
  apply JtranslatedVertices (k - 1) hsmall
    ⟨(k : Int), 1 - (k : Int)⟩ ⟨(k : Int), (k : Int) + 1⟩
  apply Zsqrtd.ext
  · rfl
  · push_cast
    omega

private theorem hWtopE :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → ((0 < k - 1) → (
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t : GaussianInt), (t = ⟨s.re, 2 * (k :
            Int) - 2 * (m : Int) - s.im⟩) → ((fun e : Finset GaussianInt => e.image J) ''
            FootprintEdges (TileTranslation (DiamondTile m) s) = FootprintEdges (TileTranslation
            (DiamondTile m) t)))) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        (fun e : Finset GaussianInt => e.image J) '' FootprintEdges W = FootprintEdges Wtop))) )
            := by
  classical
  intro k hk hsmall W J JtranslatedEdges Wtop
  apply JtranslatedEdges (k - 1) hsmall
    ⟨(k : Int), 1 - (k : Int)⟩ ⟨(k : Int), (k : Int) + 1⟩
  apply Zsqrtd.ext
  · rfl
  · push_cast
    omega

private theorem hUtopCells :
    (by
      classical
      exact
        ∀ (k : Nat),
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
        (TileTranslation (TileReflection U) ⟨0, 2 * (k : Int)⟩).cells = Utop.cells ) := by
  classical
  intro k U Utop
  simp [U, Utop, TileTranslation, TileReflection, GaussianTranslation,
    GaussianReflection]

private theorem hUtopNe :
    (by
      classical
      exact
        ∀ (k : Nat),
        let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
        Utop.cells.Nonempty ) := by
  classical
  intro k Utop
  refine ⟨⟨0, 2 * (k : Int)⟩, ?_⟩
  simp [Utop]

private theorem hJUV :
    (by
      classical
      exact
        ∀ (k : Nat),
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (T : ProtoTile), ∀ (T' : ProtoTile), (T.cells = T'.cells) → ((T.cells.Nonempty) →
            (FootprintVertices T = FootprintVertices T' ∧ FootprintEdges T = FootprintEdges T')))
            → ((∀ (T : ProtoTile), FootprintVertices (TileTranslation (TileReflection T) ⟨0, 2 *
            (k : Int)⟩) = J '' FootprintVertices T) → (
        let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
        ((TileTranslation (TileReflection U) ⟨0, 2 * (k : Int)⟩).cells = Utop.cells) →
            ((Utop.cells.Nonempty) → (J '' FootprintVertices U = FootprintVertices Utop)))) ) := by
  classical
  intro k U J sameCellObs JtileVertices Utop hUtopCells hUtopNe
  have hne : (TileTranslation (TileReflection U)
      ⟨0, 2 * (k : Int)⟩).cells.Nonempty := by
    rw [hUtopCells]
    exact hUtopNe
  have hobs := sameCellObs (TileTranslation (TileReflection U)
    ⟨0, 2 * (k : Int)⟩) Utop hUtopCells hne
  exact JtileVertices U |>.symm.trans hobs.1

private theorem hJUE :
    (by
      classical
      exact
        ∀ (k : Nat),
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (∀ (T : ProtoTile), ∀ (T' : ProtoTile), (T.cells = T'.cells) → ((T.cells.Nonempty) →
            (FootprintVertices T = FootprintVertices T' ∧ FootprintEdges T = FootprintEdges T')))
            → ((∀ (T : ProtoTile), (fun e : Finset GaussianInt => e.image J) '' FootprintEdges T
            = FootprintEdges (TileTranslation (TileReflection T) ⟨0, 2 * (k : Int)⟩)) → (
        let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
        ((TileTranslation (TileReflection U) ⟨0, 2 * (k : Int)⟩).cells = Utop.cells) →
            ((Utop.cells.Nonempty) → ((fun e : Finset GaussianInt => e.image J) '' FootprintEdges
            U = FootprintEdges Utop)))) ) := by
  classical
  intro k U J sameCellObs JtileEdges Utop hUtopCells hUtopNe
  have hne : (TileTranslation (TileReflection U)
      ⟨0, 2 * (k : Int)⟩).cells.Nonempty := by
    rw [hUtopCells]
    exact hUtopNe
  have hobs := sameCellObs (TileTranslation (TileReflection U)
    ⟨0, 2 * (k : Int)⟩) Utop hUtopCells hne
  exact (JtileEdges U).trans hobs.2

private theorem hRimgExists :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (Function.Injective J) → ((∀ a c : GaussianInt, (c = a + 1 ∨ c = a - 1 ∨ c = a + ⟨0, 1⟩ ∨
            c = a - ⟨0, 1⟩) → (J c = J a + 1 ∨ J c = J a - 1 ∨ J c = J a + ⟨0, 1⟩ ∨ J c = J a -
            ⟨0, 1⟩)) → ((FootprintVertices D = J '' FootprintVertices D) → ((FootprintEdges D =
            (fun e : Finset GaussianInt => e.image J) '' FootprintEdges D) → ((FootprintVertices
            (TileTranslation D shiftR) = J '' FootprintVertices (TileTranslation D shiftR)) →
            ((FootprintEdges (TileTranslation D shiftR) = (fun e : Finset GaussianInt => e.image
            J) '' FootprintEdges (TileTranslation D shiftR)) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        (FootprintVertices Wtop = J '' FootprintVertices W) → ((FootprintEdges Wtop = (fun e :
            Finset GaussianInt => e.image J) '' FootprintEdges W) → (∀ (R :
            ExactTileInterfaceTriple D (TileTranslation D shiftR) W), ∃ (d' :
            ExactTileInterfaceTriple D (TileTranslation D shiftR) Wtop), d'.point = J R.point ∧
            d'.otherAB = J R.otherAB ∧ d'.otherBC = J R.otherBC ∧ d'.otherCA = J
            R.otherCA)))))))) ) := by
  classical
  intro k D W shiftR J Jinj Jstep hJDv' hJDe' hJRSv' hJRSe' Wtop hWtopV' hWtopE' R
  exact P4055T1ExactTripleImage J Jinj Jstep
    D (TileTranslation D shiftR) W
    D (TileTranslation D shiftR) Wtop
    hJDv' hJRSv' hWtopV' hJDe' hJRSe' hWtopE' R

private theorem hIimgExists :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (Function.Injective J) → ((∀ a c : GaussianInt, (c = a + 1 ∨ c = a - 1 ∨ c = a + ⟨0, 1⟩ ∨
            c = a - ⟨0, 1⟩) → (J c = J a + 1 ∨ J c = J a - 1 ∨ J c = J a + ⟨0, 1⟩ ∨ J c = J a -
            ⟨0, 1⟩)) → ((FootprintVertices D = J '' FootprintVertices D) → ((FootprintEdges D =
            (fun e : Finset GaussianInt => e.image J) '' FootprintEdges D) → (
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        (FootprintVertices (TileTranslation D shiftHigh) = J '' FootprintVertices
            (TileTranslation D shiftLow)) → ((FootprintEdges (TileTranslation D shiftHigh) = (fun
            e : Finset GaussianInt => e.image J) '' FootprintEdges (TileTranslation D shiftLow)) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        (FootprintVertices Wtop = J '' FootprintVertices W) → ((FootprintEdges Wtop = (fun e :
            Finset GaussianInt => e.image J) '' FootprintEdges W) → (∀ (I :
            ExactTileInterfaceTriple D (TileTranslation D shiftLow) W), ∃ (d' :
            ExactTileInterfaceTriple D (TileTranslation D shiftHigh) Wtop), d'.point = J I.point
            ∧ d'.otherAB = J I.otherAB ∧ d'.otherBC = J I.otherBC ∧ d'.otherCA = J
            I.otherCA)))))))) ) := by
  classical
  intro k D W shiftLow J Jinj Jstep hJDv' hJDe' shiftHigh hJDLv' hJDLe' Wtop hWtopV' hWtopE' I
  exact P4055T1ExactTripleImage J Jinj Jstep
    D (TileTranslation D shiftLow) W
    D (TileTranslation D shiftHigh) Wtop
    hJDv' hJDLv' hWtopV' hJDe' hJDLe' hWtopE' I

private theorem hRp :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        (J x = ⟨(k : Int), (k : Int) + 1⟩) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        ∀ (R : ExactTileInterfaceTriple D (TileTranslation D shiftR) W), (R.point = x) → (∀ (R' :
            ExactTileInterfaceTriple D (TileTranslation D shiftR) Wtop), (R'.point = J R.point ∧
            R'.otherAB = J R.otherAB ∧ R'.otherBC = J R.otherBC ∧ R'.otherCA = J R.otherCA) →
            (R'.point = ⟨(k : Int), (k : Int) + 1⟩))) ) := by
  classical
  intro k D W shiftR J x Jx Wtop R hRpoint R' hRimg
  calc
    R'.point = J R.point := hRimg.1
    _ = J x := congrArg J hRpoint
    _ = _ := Jx

private theorem hIp :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let y : GaussianInt := 1
        (J y = ⟨1, 2 * (k : Int)⟩) → (
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        ∀ (I : ExactTileInterfaceTriple D (TileTranslation D shiftLow) W), (I.point = (1 :
            GaussianInt)) → (∀ (I' : ExactTileInterfaceTriple D (TileTranslation D shiftHigh)
            Wtop), (I'.point = J I.point ∧ I'.otherAB = J I.otherAB ∧ I'.otherBC = J I.otherBC ∧
            I'.otherCA = J I.otherCA) → (I'.point = ⟨1, 2 * (k : Int)⟩))) ) := by
  classical
  intro k D W shiftLow J y Jy shiftHigh Wtop I hIpoint I' hIimg
  calc
    I'.point = J I.point := hIimg.1
    _ = J y := congrArg J hIpoint
    _ = _ := Jy

private theorem hAp :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let y : GaussianInt := 1
        (J y = ⟨1, 2 * (k : Int)⟩) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
        ∀ (A : ExactTileInterfaceTriple D W U), (A.point = (1 : GaussianInt)) → (∀ (A' :
            ExactTileInterfaceTriple D Wtop Utop), (A'.point = J A.point ∧ A'.otherAB = J
            A.otherAB ∧ A'.otherBC = J A.otherBC ∧ A'.otherCA = J A.otherCA) → (A'.point = ⟨1, 2
            * (k : Int)⟩))) ) := by
  classical
  intro k D W U J y Jy Wtop Utop A hApoint A' hAimg
  calc
    A'.point = J A.point := hAimg.1
    _ = J y := congrArg J hApoint
    _ = _ := Jy

private theorem hRca' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let y : GaussianInt := 1
        (J y = ⟨1, 2 * (k : Int)⟩) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        ∀ (R : ExactTileInterfaceTriple D (TileTranslation D shiftR) W), (R.otherCA = (1 :
            GaussianInt)) → (∀ (R' : ExactTileInterfaceTriple D (TileTranslation D shiftR) Wtop),
            (R'.point = J R.point ∧ R'.otherAB = J R.otherAB ∧ R'.otherBC = J R.otherBC ∧
            R'.otherCA = J R.otherCA) → (R'.otherCA = ⟨1, 2 * (k : Int)⟩))) ) := by
  classical
  intro k D W shiftR J y Jy Wtop R hRca R' hRimg
  calc
    R'.otherCA = J R.otherCA := hRimg.2.2.2
    _ = J y := congrArg J hRca
    _ = _ := Jy

private theorem hIca' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        (J x = ⟨(k : Int), (k : Int) + 1⟩) → (
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        ∀ (I : ExactTileInterfaceTriple D (TileTranslation D shiftLow) W), (I.otherCA = x) → (∀
            (I' : ExactTileInterfaceTriple D (TileTranslation D shiftHigh) Wtop), (I'.point = J
            I.point ∧ I'.otherAB = J I.otherAB ∧ I'.otherBC = J I.otherBC ∧ I'.otherCA = J
            I.otherCA) → (I'.otherCA = ⟨(k : Int), (k : Int) + 1⟩))) ) := by
  classical
  intro k D W shiftLow J x Jx shiftHigh Wtop I hIca I' hIimg
  calc
    I'.otherCA = J I.otherCA := hIimg.2.2.2
    _ = J x := congrArg J hIca
    _ = _ := Jx

private theorem hAab' :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
        (J x = ⟨(k : Int), (k : Int) + 1⟩) → (
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
        ∀ (A : ExactTileInterfaceTriple D W U), (A.otherAB = x) → (∀ (A' :
            ExactTileInterfaceTriple D Wtop Utop), (A'.point = J A.point ∧ A'.otherAB = J
            A.otherAB ∧ A'.otherBC = J A.otherBC ∧ A'.otherCA = J A.otherCA) → (A'.otherAB = ⟨(k
            : Int), (k : Int) + 1⟩))) ) := by
  classical
  intro k D W U J x Jx Wtop Utop A hAab A' hAimg
  calc
    A'.otherAB = J A.otherAB := hAimg.2.1
    _ = J x := congrArg J hAab
    _ = _ := Jx

private theorem hnew :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        ∀ (R' : ExactTileInterfaceTriple D (TileTranslation D shiftR) Wtop), ∀ (I' :
            ExactTileInterfaceTriple D (TileTranslation D shiftHigh) Wtop), (R'.point = ⟨(k :
            Int), (k : Int) + 1⟩) → ((I'.point = ⟨1, 2 * (k : Int)⟩) → (((⟨(↑k : ℤ), (↑k : ℤ) +
            (1 : ℤ)⟩ : GaussianInt) = (⟨(1 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)) → (R'.point
            = I'.point))) ) := by
  classical
  intro k D shiftR shiftHigh Wtop R' I' hRp hIp heq
  calc
    R'.point = ⟨(k : Int), (k : Int) + 1⟩ := hRp
    _ = ⟨1, 2 * (k : Int)⟩ := heq
    _ = I'.point := hIp.symm

private theorem hji :
    (by
      classical
      exact
        ∀ (k : Nat),
        let D := DiamondTile k
        let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
        let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
        let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
        let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
          ⟨(k : Int), (k : Int) + 1⟩
        ∀ (R : ExactTileInterfaceTriple D (TileTranslation D shiftR) W), ∀ (I :
            ExactTileInterfaceTriple D (TileTranslation D shiftLow) W), ∀ (R' :
            ExactTileInterfaceTriple D (TileTranslation D shiftR) Wtop), (R'.point = J R.point ∧
            R'.otherAB = J R.otherAB ∧ R'.otherBC = J R.otherBC ∧ R'.otherCA = J R.otherCA) → (∀
            (I' : ExactTileInterfaceTriple D (TileTranslation D shiftHigh) Wtop), (I'.point = J
            I.point ∧ I'.otherAB = J I.otherAB ∧ I'.otherBC = J I.otherBC ∧ I'.otherCA = J
            I.otherCA) → ((R'.point = I'.point) → (J R.point = J I.point))) ) := by
  classical
  intro k D W shiftR shiftLow J shiftHigh Wtop R I R' hRimg I' hIimg hnew
  calc
    J R.point = R'.point := hRimg.1.symm
    _ = I'.point := hnew
    _ = J I.point := hIimg.1

end PredecessorInterfaceGeometry

namespace PredecessorReflection

private theorem reflectedInterfaces :
    (by
      classical
      exact
        ∀ (k : Nat), ((1 : ℕ) < k) → (∀ (b : Bool), (0 < k) → ((0 < k - 1) → (
        (∀ (T : ProtoTile), TileTranslation T 0 = T) → (
        let J : GaussianInt → GaussianInt := fun z =>
          GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
        (
        let x := (⟨(↑k : ℤ), (↑k : ℤ) - (1 : ℤ)⟩ : GaussianInt); (fun (z : GaussianInt) =>
            GaussianTranslation (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt) (GaussianReflection
            z)) x = (⟨(↑k : ℤ), (↑k : ℤ) + (1 : ℤ)⟩ : GaussianInt)) → ((
        let y := (1 : GaussianInt); (fun (z : GaussianInt) => GaussianTranslation (⟨(0 : ℤ), (2 :
            ℤ) * (↑k : ℤ)⟩ : GaussianInt) (GaussianReflection z)) y = (⟨(1 : ℤ), (2 : ℤ) * (↑k :
            ℤ)⟩ : GaussianInt)) → ((∀ (T : ProtoTile), ∀ (T' : ProtoTile), T.cells = T'.cells →
            Finset.Nonempty T.cells → FootprintVertices T = FootprintVertices T' ∧ FootprintEdges
            T = FootprintEdges T') → ((∀ (m : Nat), (0 < m) → (∀ (s : GaussianInt), ∀ (t :
            GaussianInt), (t = ⟨s.re, 2 * (k : Int) - 2 * (m : Int) - s.im⟩) → (J ''
            FootprintVertices (TileTranslation (DiamondTile m) s) = FootprintVertices
            (TileTranslation (DiamondTile m) t)))) → ((
        let J := fun (z : GaussianInt) => GaussianTranslation (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt) (GaussianReflection z); ∀ (m : ℕ), (0 : ℕ) < m → ∀ (s : GaussianInt), ∀
            (t : GaussianInt), t = (⟨s.re, (2 : ℤ) * (↑k : ℤ) - (2 : ℤ) * (↑m : ℤ) - s.im⟩ :
            GaussianInt) → (fun (e : Finset GaussianInt) => Finset.image J e) '' FootprintEdges
            (TileTranslation (DiamondTile m) s) = FootprintEdges (TileTranslation (DiamondTile m)
            t)) → ((
        let J := fun (z : GaussianInt) => GaussianTranslation (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt) (GaussianReflection z); ∀ (T : ProtoTile), FootprintVertices
            (TileTranslation (TileReflection T) (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt)) =
            J '' FootprintVertices T) → ((
        let J := fun (z : GaussianInt) => GaussianTranslation (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ :
            GaussianInt) (GaussianReflection z); ∀ (T : ProtoTile), (fun (e : Finset GaussianInt)
            => Finset.image J e) '' FootprintEdges T = FootprintEdges (TileTranslation
            (TileReflection T) (⟨(0 : ℤ), (2 : ℤ) * (↑k : ℤ)⟩ : GaussianInt))) → (((
        let M := P5260T1PlacementLedger k 2 false
           let D := DiamondTile k
           ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
             ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
               ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
                 R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
                 A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
                 I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
                 M.2.2.1 ≠ M.2.2.2)) → (
        let M := P5260T1PlacementLedger k 2 b
        let D := DiamondTile k
        ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
          ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
            ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
              R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
              A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
              I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
              M.2.2.1 ≠ M.2.2.2)))))))))))) ) := by
  classical
  intro k hk b hkpos hsmall translateZero J Jx Jy sameCellObs JtranslatedVertices
      JtranslatedEdges JtileVertices JtileEdges hFalse
  let D := DiamondTile k
  let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
  let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
  let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
  let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
  let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
  let y : GaussianInt := 1
  have Jinj := PredecessorInterfaceGeometry.Jinj k
  have Jstep := PredecessorInterfaceGeometry.Jstep k
  have hzero : (0 : GaussianInt) =
      ⟨0, 2 * (k : Int) - 2 * (k : Int) - 0⟩ := PredecessorInterfaceGeometry.hzero k
  have hJDv : J '' FootprintVertices D = FootprintVertices D := by
    simpa only [translateZero] using JtranslatedVertices k hkpos 0 0 hzero
  have hJDv' : FootprintVertices D = J '' FootprintVertices D := hJDv.symm
  have hJDe := PredecessorInterfaceGeometry.hJDe k hkpos translateZero JtranslatedEdges hzero
  have hJDe' : FootprintEdges D =
      (fun e : Finset GaussianInt => e.image J) '' FootprintEdges D := hJDe.symm
  have hshiftR := PredecessorInterfaceGeometry.hshiftR k
  have hJRSv := PredecessorInterfaceGeometry.hJRSv k hkpos JtranslatedVertices hshiftR
  have hJRSv' : FootprintVertices (TileTranslation D shiftR) =
      J '' FootprintVertices (TileTranslation D shiftR) := hJRSv.symm
  have hJRSe := PredecessorInterfaceGeometry.hJRSe k hkpos JtranslatedEdges hshiftR
  have hJRSe' := PredecessorInterfaceGeometry.hJRSe' k hJRSe
  let shiftHigh : GaussianInt := ⟨0, 2 * (k : Int)⟩
  have hJDLv := PredecessorInterfaceGeometry.hJDLv k hkpos JtranslatedVertices
  have hJDLv' : FootprintVertices (TileTranslation D shiftHigh) =
      J '' FootprintVertices (TileTranslation D shiftLow) := hJDLv.symm
  have hJDLe := PredecessorInterfaceGeometry.hJDLe k hkpos JtranslatedEdges
  have hJDLe' := PredecessorInterfaceGeometry.hJDLe' k hJDLe
  let Wtop : ProtoTile := TileTranslation (DiamondTile (k - 1))
    ⟨(k : Int), (k : Int) + 1⟩
  have hWtopV := PredecessorInterfaceGeometry.hWtopV k hk hsmall JtranslatedVertices
  have hWtopV' : FootprintVertices Wtop = J '' FootprintVertices W := hWtopV.symm
  have hWtopE := PredecessorInterfaceGeometry.hWtopE k hk hsmall JtranslatedEdges
  have hWtopE' : FootprintEdges Wtop =
      (fun e : Finset GaussianInt => e.image J) '' FootprintEdges W := hWtopE.symm
  let Utop : ProtoTile := ⟨{⟨0, 2 * (k : Int)⟩}, ⟨0, 2 * (k : Int)⟩⟩
  have hUtopCells := PredecessorInterfaceGeometry.hUtopCells k
  have hUtopNe := PredecessorInterfaceGeometry.hUtopNe k
  have hJUV := PredecessorInterfaceGeometry.hJUV k sameCellObs JtileVertices hUtopCells hUtopNe
  have hJUV' : FootprintVertices Utop = J '' FootprintVertices U := hJUV.symm
  have hJUE := PredecessorInterfaceGeometry.hJUE k sameCellObs JtileEdges hUtopCells hUtopNe
  have hJUE' : FootprintEdges Utop =
      (fun e : Finset GaussianInt => e.image J) '' FootprintEdges U := hJUE.symm
  cases b
  · exact hFalse
  · dsimp [P5260T1PlacementLedger, P5124T1ParentModel]
    obtain ⟨R, I, A, hRpoint, hIpoint, hApoint, hRca, hIca, hAab, hxy⟩ := hFalse
    simp only [P5260T1PlacementLedger] at hRpoint hIpoint hApoint hRca hIca hAab hxy
    change R.point = x at hRpoint
    change I.point = 1 at hIpoint
    change A.point = 1 at hApoint
    change R.otherCA = 1 at hRca
    change I.otherCA = x at hIca
    change A.otherAB = x at hAab
    change x ≠ 1 at hxy
    change ExactTileInterfaceTriple D (TileTranslation D shiftR) W at R
    change ExactTileInterfaceTriple D (TileTranslation D shiftLow) W at I
    change ExactTileInterfaceTriple D W U at A
    have hRimgExists := PredecessorInterfaceGeometry.hRimgExists k Jinj Jstep hJDv' hJDe'
        hJRSv' hJRSe' hWtopV' hWtopE' R
    obtain ⟨R', hRimg⟩ := hRimgExists
    have hIimgExists := PredecessorInterfaceGeometry.hIimgExists k Jinj Jstep hJDv' hJDe'
        hJDLv' hJDLe' hWtopV' hWtopE' I
    obtain ⟨I', hIimg⟩ := hIimgExists
    have hAimgExists := P4055T1ExactTripleImage J Jinj Jstep
      D W U D Wtop Utop hJDv' hWtopV' hJUV' hJDe' hWtopE' hJUE' A
    obtain ⟨A', hAimg⟩ := hAimgExists
    have hRp := PredecessorInterfaceGeometry.hRp k Jx R hRpoint R' hRimg
    have hIp := PredecessorInterfaceGeometry.hIp k Jy I hIpoint I' hIimg
    have hAp := PredecessorInterfaceGeometry.hAp k Jy A hApoint A' hAimg
    have hRca' := PredecessorInterfaceGeometry.hRca' k Jy R hRca R' hRimg
    have hIca' := PredecessorInterfaceGeometry.hIca' k Jx I hIca I' hIimg
    have hAab' := PredecessorInterfaceGeometry.hAab' k Jx A hAab A' hAimg
    refine ⟨R', ⟨I', ⟨A', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
    · exact hRp
    · exact hIp
    · exact hAp
    · exact hRca'
    · exact hIca'
    · exact hAab'
    · intro heq
      have hnew := PredecessorInterfaceGeometry.hnew k R' I' hRp hIp heq
      have hji := PredecessorInterfaceGeometry.hji k R I R' hRimg I' hIimg hnew
      have hsource : R.point = I.point := Jinj hji
      apply hxy
      calc
        _ = R.point := hRpoint.symm
        _ = I.point := hsource
        _ = _ := hIpoint

end PredecessorReflection

theorem P5260T1PredecessorInterfaces (k : Nat) (hk : 1 < k) (b : Bool) :
    let M := P5260T1PlacementLedger k 2 b
    let D := DiamondTile k
    ∃ R : ExactTileInterfaceTriple D (TileTranslation D M.2.1.1) M.1.1,
      ∃ I : ExactTileInterfaceTriple D (TileTranslation D M.2.1.2) M.1.1,
        ∃ A : ExactTileInterfaceTriple D M.1.1 M.1.2,
          R.point = M.2.2.1 ∧ I.point = M.2.2.2 ∧
          A.point = M.2.2.2 ∧ R.otherCA = M.2.2.2 ∧
          I.otherCA = M.2.2.1 ∧ A.otherAB = M.2.2.1 ∧
          M.2.2.1 ≠ M.2.2.2 := by
-- BODY
  classical
  have rawBoundaryVertices := PredecessorInterfaceGeometry.rawBoundaryVertices
  have rawBoundaryEdges := PredecessorInterfaceGeometry.rawBoundaryEdges
  have rawStaircase := PredecessorInterfaceGeometry.rawStaircase rawBoundaryVertices
      rawBoundaryEdges (PredecessorInterfaceGeometry.staircaseBetween k)
  have twoVertexPath := PredecessorInterfaceGeometry.twoVertexPath k
  have diamondCellsNonempty := PredecessorInterfaceGeometry.diamondCellsNonempty
  have reversePath {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {x y : GaussianInt} (hp : SimpleGridPathBetween V E x y) :=
          PredecessorInterfaceGeometry.reversePath (V := V) (E := E) (x := x) (y := y) hp
  have translatedDiamondCellsNonempty :=
      PredecessorInterfaceGeometry.translatedDiamondCellsNonempty diamondCellsNonempty
  have hkpos : 0 < k := by omega
  have hsmall : 0 < k - 1 := by omega
  let N : Nat := 2 * (k - 1)
  have hN : 0 < N := by dsimp [N]; omega
  let D := DiamondTile k
  let W := TileTranslation (DiamondTile (k - 1)) ⟨(k : Int), 1 - (k : Int)⟩
  let L := TileTranslation D ⟨0, -(2 * (k : Int))⟩
  let Em := TileTranslation (DiamondTile (k - 1)) ⟨-(k : Int), 1 - (k : Int)⟩
  have hstair := P5157T1DiamondStaircaseIntersections k hk
  dsimp only [D, W, L, Em, N] at hstair
  obtain ⟨⟨hDWd, hDWv, hDWe⟩,
    ⟨hLWd, hLWv, hLWe⟩, ⟨hDEd, hDEv, hDEe⟩⟩ := hstair
  have pathDW := PredecessorInterfaceGeometry.pathDW k rawStaircase diamondCellsNonempty
      translatedDiamondCellsNonempty hkpos hsmall hN hDWd hDWv hDWe
  have translateComp := PredecessorInterfaceGeometry.translateComp
  let shiftR : GaussianInt := ⟨2 * (k : Int), 0⟩
  have hpStart := PredecessorInterfaceGeometry.hpStart
  have hpEnd := PredecessorInterfaceGeometry.hpEnd k hk
  have pathWD := PredecessorInterfaceGeometry.pathWD k pathDW
  have translateZero (T : ProtoTile) : TileTranslation T 0 = T :=
      PredecessorInterfaceGeometry.translateZero T
  let shiftLow : GaussianInt := ⟨0, -(2 * (k : Int))⟩
  have hcapLow := P5203T1CapInterface k hkpos shiftLow
  dsimp only at hcapLow
  have pathLow := (PredecessorInterfaceGeometry.rawCapBetween rawBoundaryVertices
      rawBoundaryEdges (PredecessorInterfaceGeometry.capBetween k)) k hkpos shiftLow hcapLow.2.2.1
  have hlowZero : shiftLow + ⟨0, 2 * (k : Int)⟩ = 0 := by
    apply Zsqrtd.ext <;> simp [shiftLow]
  have hlowTile : TileTranslation D
      (shiftLow + ⟨0, 2 * (k : Int)⟩) = D := PredecessorInterfaceGeometry.hlowTile k
          translateZero hlowZero
  rw [hlowTile] at pathLow
  obtain ⟨u, hu, hquarterCells, _, hquarterVertices, _⟩ :=
    QuarterTurnSymmetricCenteredTransport D (DiamondBaseT2 ⟨k, hkpos⟩)
  have hcentroid := P4194T1DiamondCentroid k hkpos
  rw [hcentroid] at hu
  simp only [GaussianRealPoint, Int.reduceNeg, GaussianInt.intCast_re, GaussianInt.intCast_im,
      zero_add, sub_zero, Prod.mk.injEq] at hu
  have huEq := PredecessorInterfaceGeometry.huEq k u hu
  let Q : GaussianInt → GaussianInt := GaussianQuarterTurn
  let F : GaussianInt → GaussianInt := fun z => Q z + u
  have F_inj := PredecessorInterfaceGeometry.F_inj k u
  have quarterVertices := PredecessorInterfaceGeometry.quarterVertices k u
  have quarterBaseVertices := PredecessorInterfaceGeometry.quarterBaseVertices k u
      hquarterVertices
  have quarterCellsAt := PredecessorInterfaceGeometry.quarterCellsAt k translateComp u hquarterCells
  have quarterVerticesAt := PredecessorInterfaceGeometry.quarterVerticesAt k
      translatedDiamondCellsNonempty hkpos u quarterCellsAt
  have shiftQuarter : Q shiftLow = shiftR := by
    apply Zsqrtd.ext <;> simp [Q, GaussianQuarterTurn, shiftLow, shiftR]
  have hxlow := PredecessorInterfaceGeometry.hxlow k u huEq
  have hxhigh := PredecessorInterfaceGeometry.hxhigh k u huEq
  have capBoundaryVerticesEq := PredecessorInterfaceGeometry.capBoundaryVerticesEq k
  let U : ProtoTile := ⟨{⟨0, -1⟩}, ⟨0, -1⟩⟩
  have hleft := P5253T1LeftSquareContacts (k - 1) hsmall
    ⟨(k : Int), 1 - (k : Int)⟩ ((k : Int) - 2) (Or.inl (by omega))
  dsimp only [U, W] at hleft ⊢
  obtain ⟨hWne, hWUdisj, hWUv, hWUedge⟩ := hleft
  have hcontactCell : (⟨(k : Int), 1 - (k : Int)⟩ : GaussianInt) +
      ⟨-((k - 1 : Nat) : Int) - 1, (k : Int) - 2⟩ = ⟨0, -1⟩ :=
          PredecessorInterfaceGeometry.hcontactCell k hk
  rw [hcontactCell] at hWUdisj hWUv hWUedge
  change Disjoint W.cells U.cells at hWUdisj
  have hUne := PredecessorInterfaceGeometry.hUne
  have hWUv' := PredecessorInterfaceGeometry.hWUv' k hWUv
  have hbot := P5253T1BottomSquareContact k hkpos 0
  dsimp only at hbot
  have hneg : (0 : GaussianInt) - ⟨0, 1⟩ = ⟨0, -1⟩ := by
    apply Zsqrtd.ext <;> simp
  rw [hneg] at hbot
  have hDULdisj : Disjoint D.cells U.cells := by
    simpa [D, U, translateZero] using hbot.2.1
  have hDUv : BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U =
      {0, 0 + 1} := PredecessorInterfaceGeometry.hDUv k translateZero hbot
  have hDUedge : {0, 0 + 1} ∈ BoundaryFootprintEdges D := by
    simpa [D, U, translateZero] using hbot.2.2.2
  have hDUv' : BoundaryFootprintVertices D ∩ BoundaryFootprintVertices U =
      {0, 1} := by simpa using hDUv
  have hDUedge' : {0, 1} ∈ BoundaryFootprintEdges D := by
    simpa using hDUedge
  have hUedgeBot' : {0, 1} ∈ BoundaryFootprintEdges U := (PredecessorInterfaceGeometry.hUedgeBot)
  have hyDL := PredecessorInterfaceGeometry.hyDL k (PredecessorInterfaceGeometry.hDLboundary k
      hkpos hlowTile capBoundaryVerticesEq) (PredecessorInterfaceGeometry.hcapRight k)
  have hyDW := PredecessorInterfaceGeometry.hyDW k hDWv
  have hsmallTriple := P5124T1SmallerParents k hk
  have hIboundaryUnique := PredecessorInterfaceGeometry.hIboundaryUnique k hyDL
      (PredecessorInterfaceGeometry.hyLW k hLWv) (PredecessorInterfaceGeometry.hsmallI k
      hsmallTriple)
  let J : GaussianInt → GaussianInt := fun z =>
    GaussianTranslation ⟨0, 2 * (k : Int)⟩ (GaussianReflection z)
  have Jcoordinate := PredecessorInterfaceGeometry.Jcoordinate k
  have reflectedPath {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {x y : GaussianInt} (hp : SimpleGridPathBetween V E x y) :=
          PredecessorInterfaceGeometry.reflectedPath k (V := V) (E := E) (x := x) (y := y) hp
  let x : GaussianInt := ⟨(k : Int), (k : Int) - 1⟩
  let y : GaussianInt := 1
  have hDWraw := PredecessorInterfaceGeometry.hDWraw k rawBoundaryVertices diamondCellsNonempty
      hkpos hDWd hDWv hWne
  have hLWraw := PredecessorInterfaceGeometry.hLWraw k rawBoundaryVertices
      translatedDiamondCellsNonempty hkpos hLWd hLWv hWne
  have hlowStart : shiftLow + ⟨1, 2 * (k : Int)⟩ = 1 := by
    apply Zsqrtd.ext <;> simp [shiftLow]
  have hlowEnd : shiftLow + ⟨-1, 2 * (k : Int)⟩ = -1 := by
    apply Zsqrtd.ext <;> simp [shiftLow]
  have hIABoundary := PredecessorInterfaceGeometry.hIABoundary k hIboundaryUnique
  exact (PredecessorReflection.reflectedInterfaces k hk b hkpos hsmall translateZero
      (PredecessorInterfaceGeometry.Jx k Jcoordinate) (PredecessorInterfaceGeometry.Jy k
      Jcoordinate) (PredecessorInterfaceGeometry.sameCellObs)
      (PredecessorInterfaceGeometry.JtranslatedVertices k)
      (PredecessorInterfaceGeometry.JtranslatedEdges k)
      (PredecessorInterfaceGeometry.JtileVertices k) (PredecessorInterfaceGeometry.JtileEdges k)
      (PredecessorInterfaceGeometry.hFalse k hk (PredecessorInterfaceGeometry.pathLW k
      rawStaircase translatedDiamondCellsNonempty hkpos hsmall hN hLWd hLWv hLWe) hpStart hpEnd
      (PredecessorInterfaceGeometry.hqStart) (PredecessorInterfaceGeometry.hqEnd k hk)
      (PredecessorInterfaceGeometry.pathWDrev k reversePath pathDW)
      (PredecessorInterfaceGeometry.pathRAB k u (PredecessorInterfaceGeometry.pathRAB0 k
      translateZero pathLow u F_inj (PredecessorInterfaceGeometry.F_step k u) quarterVertices
      (PredecessorInterfaceGeometry.quarterEdges k u) quarterBaseVertices
      (PredecessorInterfaceGeometry.quarterBaseEdges k u hquarterCells) quarterVerticesAt
      (PredecessorInterfaceGeometry.quarterEdgesAt k u quarterCellsAt) shiftQuarter) hxlow
      hxhigh) (PredecessorInterfaceGeometry.hAunique k (PredecessorInterfaceGeometry.hWURaw k
      rawBoundaryVertices hWne hWUdisj hUne hWUv') (PredecessorInterfaceGeometry.hDURaw k
      rawBoundaryVertices diamondCellsNonempty hkpos hUne hDULdisj hDUv'))
      (PredecessorInterfaceGeometry.pathIAB k (PredecessorInterfaceGeometry.pathDL k reversePath
      pathLow) hlowStart hlowEnd) (PredecessorInterfaceGeometry.pathICA k pathDW hpStart hpEnd)
      (PredecessorInterfaceGeometry.pathAAB k pathDW hpStart hpEnd)
      (PredecessorInterfaceGeometry.pathABC k reversePath (PredecessorInterfaceGeometry.hWUpath k
      rawBoundaryVertices rawBoundaryEdges twoVertexPath hWne hWUdisj hUne hWUv'
      (PredecessorInterfaceGeometry.hWedge' k hWUedge) (PredecessorInterfaceGeometry.hUedge')))
      (PredecessorInterfaceGeometry.pathACA k reversePath (PredecessorInterfaceGeometry.hDUpath k
      rawBoundaryVertices rawBoundaryEdges twoVertexPath diamondCellsNonempty hkpos hUne hDULdisj
      hDUv' hDUedge' hUedgeBot')) (PredecessorInterfaceGeometry.hRBC k
      (PredecessorInterfaceGeometry.pathRBC k (PredecessorInterfaceGeometry.pathDEm k
      rawStaircase diamondCellsNonempty translatedDiamondCellsNonempty hkpos hsmall hN hDEd hDEv
      hDEe) (PredecessorInterfaceGeometry.translatePathTiles
      (PredecessorInterfaceGeometry.translatedPath)) (PredecessorInterfaceGeometry.hEmShift k
      translateComp)) (PredecessorInterfaceGeometry.htStart k)
      (PredecessorInterfaceGeometry.htEnd k hk)) (PredecessorInterfaceGeometry.hIuniqueRaw k
      rawBoundaryVertices diamondCellsNonempty translatedDiamondCellsNonempty hkpos hLWd hcapLow
      hlowTile hWne hyDL hIboundaryUnique hDWraw) (PredecessorInterfaceGeometry.hRunique k hpEnd
      (PredecessorInterfaceGeometry.hRABraw k u huEq hxlow hxhigh
      (PredecessorInterfaceGeometry.hcapLowRawVertices k rawBoundaryVertices hkpos hcapLow
      hlowTile capBoundaryVerticesEq) (PredecessorInterfaceGeometry.hRABimage k u F_inj
      quarterVertices quarterBaseVertices quarterVerticesAt shiftQuarter
      (PredecessorInterfaceGeometry.quarterVerticesZero k translateZero u quarterVertices)))
      hDWraw (PredecessorInterfaceGeometry.pImagBound k hk))))


end ApollonianSuperharmonic

end
