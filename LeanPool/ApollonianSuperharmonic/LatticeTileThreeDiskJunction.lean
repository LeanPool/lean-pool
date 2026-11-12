/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ExactTileInterfaceTriple
public import LeanPool.ApollonianSuperharmonic.LatticeTileDiskUnionInterface
public import LeanPool.ApollonianSuperharmonic.LocalLatticeInterfaceSectors
public import LeanPool.ApollonianSuperharmonic.SimpleGridPathPointTrichotomy

-- [TABLET NODE: LatticeTileThreeDiskJunction]

/-!
# LatticeTileThreeDiskJunction

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace ThreeDiskJunctionGeometry

private theorem vertex_union :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile), (U.cells.Nonempty) →
            ((V.cells.Nonempty) → ((W.cells.Nonempty) → ((forall z : LatticeCell,
            z ∈ W.cells ↔ z ∈ U.cells ∨ z ∈ V.cells) → (FootprintVertices W = FootprintVertices U
                ∪ FootprintVertices V)))) ) := by
  classical
  intro U V W hUne hVne hWne hunion
  simp only [FootprintVertices, hUne, hVne, hWne, ite_true]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, hx, hz⟩
    rw [hunion x] at hx
    exact hx.elim (fun h => Or.inl ⟨x, h, hz⟩)
      (fun h => Or.inr ⟨x, h, hz⟩)
  · rintro (⟨x, hx, hz⟩ | ⟨x, hx, hz⟩)
    · exact ⟨x, (hunion x).2 (Or.inl hx), hz⟩
    · exact ⟨x, (hunion x).2 (Or.inr hx), hz⟩

private theorem edge_union :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (W : ProtoTile), (forall z : LatticeCell,
            z ∈ W.cells ↔ z ∈ U.cells ∨ z ∈ V.cells) → (FootprintEdges W = FootprintEdges U ∪
                FootprintEdges V) ) := by
  classical
  intro U V W hunion
  ext e
  simp only [FootprintEdges, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, hx, he⟩
    rw [hunion x] at hx
    exact hx.elim (fun h => Or.inl ⟨x, h, he⟩)
      (fun h => Or.inr ⟨x, h, he⟩)
  · rintro (⟨x, hx, he⟩ | ⟨x, hx, he⟩)
    · exact ⟨x, (hunion x).2 (Or.inl hx), he⟩
    · exact ⟨x, (hunion x).2 (Or.inr hx), he⟩

private theorem vertex_finite :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (FootprintVertices T).Finite ) := by
  classical
  intro T
  by_cases hne : T.cells.Nonempty
  · let K : Finset GaussianInt := T.cells.biUnion (fun x =>
      {x, x + 1, x + ⟨0, 1⟩, x + 1 + ⟨0, 1⟩})
    have hK : (K : Set GaussianInt) = FootprintVertices T := by
      ext z
      simp [K, FootprintVertices, hne]
    rw [← hK]
    exact K.finite_toSet
  · simp [FootprintVertices, hne]

private theorem edge_finite :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (FootprintEdges T).Finite ) := by
  classical
  intro T
  let I : GaussianInt := ⟨0, 1⟩
  let edge : T.cells × (Bool × Bool) → Finset GaussianInt := fun q =>
    match q.2 with
    | (false, false) => {q.1.1, q.1.1 + 1}
    | (false, true) => {q.1.1, q.1.1 + I}
    | (true, false) => {q.1.1 + 1, q.1.1 + 1 + I}
    | (true, true) => {q.1.1 + I, q.1.1 + 1 + I}
  apply (Set.finite_range edge).subset
  rintro e ⟨c, hc, h | h | h | h⟩
  · exact ⟨(⟨c, hc⟩, false, false), by simpa [edge] using h.symm⟩
  · exact ⟨(⟨c, hc⟩, false, true), by simpa [edge, I] using h.symm⟩
  · exact ⟨(⟨c, hc⟩, true, false), by simpa [edge, I] using h.symm⟩
  · exact ⟨(⟨c, hc⟩, true, true), by simpa [edge, I] using h.symm⟩

private theorem hunionAB_C (A B C AB ABC : ProtoTile)
    (hunionAB : ∀ z : LatticeCell, z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells)
    (hunionABC : ∀ z : LatticeCell, z ∈ ABC.cells ↔
      z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells) :
    ∀ z : LatticeCell, z ∈ ABC.cells ↔ z ∈ AB.cells ∨ z ∈ C.cells := by
  classical
  intro z
  rw [hunionABC z, hunionAB z]
  tauto

private theorem hpathAB :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), (FootprintVertices A ∩ FootprintVertices B =
            CommonFootprintEdgeVertices A B) → (∀ (xAB : GaussianInt), ∀ (yAB : GaussianInt),
            (SimpleGridPathBetween (CommonFootprintEdgeVertices A B) (FootprintEdges A ∩
            FootprintEdges B) xAB yAB) → (SimpleGridPathBetween (FootprintVertices A ∩
            FootprintVertices B) (FootprintEdges A ∩ FootprintEdges B) xAB yAB)) ) := by
  classical
  intro A B hVrawAB xAB yAB hpathAB0
  rw [hVrawAB]
  exact hpathAB0

private theorem hpathBC :
    (by
      classical
      exact
        ∀ (B : ProtoTile), ∀ (C : ProtoTile), (FootprintVertices B ∩ FootprintVertices C =
            CommonFootprintEdgeVertices B C) → (∀ (xBC : GaussianInt), ∀ (yBC : GaussianInt),
            (SimpleGridPathBetween (CommonFootprintEdgeVertices B C) (FootprintEdges B ∩
            FootprintEdges C) xBC yBC) → (SimpleGridPathBetween (FootprintVertices B ∩
            FootprintVertices C) (FootprintEdges B ∩ FootprintEdges C) xBC yBC)) ) := by
  classical
  intro B C hVrawBC xBC yBC hpathBC0
  rw [hVrawBC]
  exact hpathBC0

private theorem hpathCA :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (C : ProtoTile), (FootprintVertices C ∩ FootprintVertices A =
            CommonFootprintEdgeVertices C A) → (∀ (xCA : GaussianInt), ∀ (yCA : GaussianInt),
            (SimpleGridPathBetween (CommonFootprintEdgeVertices C A) (FootprintEdges C ∩
            FootprintEdges A) xCA yCA) → (SimpleGridPathBetween (FootprintVertices C ∩
            FootprintVertices A) (FootprintEdges C ∩ FootprintEdges A) xCA yCA)) ) := by
  classical
  intro A C hVrawCA xCA yCA hpathCA0
  rw [hVrawCA]
  exact hpathCA0

private theorem hcellsAB :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (AB : ProtoTile), (Disjoint A.cells B.cells) →
            ((∀ (z : LatticeCell), z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) → (AB.cells.card =
            A.cells.card + B.cells.card)) ) := by
  classical
  intro A B AB hdisjointAB hunionAB
  have h : AB.cells = A.cells ∪ B.cells := by ext z; simpa using hunionAB z
  rw [h, Finset.card_union_of_disjoint hdisjointAB]

private theorem hcellsBC :
    (by
      classical
      exact
        ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (BC : ProtoTile), (Disjoint B.cells C.cells) →
            ((∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells) → (BC.cells.card =
            B.cells.card + C.cells.card)) ) := by
  classical
  intro B C BC hdisjointBC hunionBC
  have h : BC.cells = B.cells ∪ C.cells := by ext z; simpa using hunionBC z
  rw [h, Finset.card_union_of_disjoint hdisjointBC]

private theorem hcellsCA :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (C : ProtoTile), ∀ (CA : ProtoTile), (Disjoint C.cells A.cells) →
            ((∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells) → (CA.cells.card =
            C.cells.card + A.cells.card)) ) := by
  classical
  intro A C CA hdisjointCA hunionCA
  have h : CA.cells = C.cells ∪ A.cells := by ext z; simpa using hunionCA z
  rw [h, Finset.card_union_of_disjoint hdisjointCA]

private theorem hdisjointAB_C :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (AB : ProtoTile), (Disjoint
            B.cells C.cells) → ((Disjoint C.cells A.cells) → ((∀ (z : LatticeCell), z ∈ AB.cells
            ↔ z ∈ A.cells ∨ z ∈ B.cells) → (Disjoint AB.cells C.cells))) ) := by
  classical
  intro A B C AB hdisjointBC hdisjointCA hunionAB
  rw [Finset.disjoint_left]
  intro z hzAB hzC
  rw [hunionAB z] at hzAB
  rcases hzAB with hzA | hzB
  · exact (Finset.disjoint_left.mp hdisjointCA) hzC hzA
  · exact (Finset.disjoint_left.mp hdisjointBC) hzB hzC

private theorem hcellsABC :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ∀ (AB : ProtoTile), ∀ (ABC :
            ProtoTile), (forall z : LatticeCell, z ∈ ABC.cells ↔ z ∈ AB.cells ∨ z ∈ C.cells) →
            ((AB.cells.card = A.cells.card + B.cells.card) → ((Disjoint AB.cells C.cells) →
            (ABC.cells.card = A.cells.card + B.cells.card + C.cells.card))) ) := by
  classical
  intro A B C AB ABC hunionAB_C hcellsAB hdisjointAB_C
  have h : ABC.cells = AB.cells ∪ C.cells := by
    ext z
    simpa using hunionAB_C z
  rw [h, Finset.card_union_of_disjoint hdisjointAB_C, hcellsAB]

private theorem horiz_unique (x y : GaussianInt)
    (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) : x = y := by
  classical
  have hx : x = y ∨ x = y + 1 := by
    have : x ∈ ({y, y + 1} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + 1 := by
    have : y ∈ ({x, x + 1} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · have hre := congrArg Zsqrtd.re hxy
    have hre' := congrArg Zsqrtd.re hyx
    norm_num at hre hre'
    omega

private theorem vert_unique :
    let I : GaussianInt := ⟨0, 1⟩
    ∀ x y : GaussianInt, ({x, x + I} : Finset GaussianInt) = {y, y + I} → x = y := by
  classical
  intro I x y h
  have hx : x = y ∨ x = y + I := by
    have : x ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hy : y = x ∨ y = x + I := by
    have : y ∈ ({x, x + I} : Finset GaussianInt) := by rw [h]; simp
    simpa using this
  rcases hx with hxy | hxy
  · exact hxy
  rcases hy with hyx | hyx
  · exact hyx.symm
  · have him := congrArg Zsqrtd.im hxy
    have him' := congrArg Zsqrtd.im hyx
    simp [I] at him him'
    omega

private theorem horiz_ne_vert :
    let I : GaussianInt := ⟨0, 1⟩
    ∀ x y : GaussianInt, ({x, x + 1} : Finset GaussianInt) ≠ {y, y + I} := by
  classical
  intro I x y h
  have hx : x = y ∨ x = y + I := by
    have : x ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  have hx1 : x + 1 = y ∨ x + 1 = y + I := by
    have : x + 1 ∈ ({y, y + I} : Finset GaussianInt) := by rw [← h]; simp
    simpa using this
  rcases hx with hx | hx <;> rcases hx1 with hx1 | hx1
  all_goals
    have hre := congrArg Zsqrtd.re hx
    have him := congrArg Zsqrtd.im hx
    have hre1 := congrArg Zsqrtd.re hx1
    have him1 := congrArg Zsqrtd.im hx1
    simp [I] at hre him hre1 him1
    omega

private theorem footprint_normalize :
    (by
      classical
      exact
        let I : GaussianInt := ⟨0, 1⟩
        ∀ (T : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → ((∃ z, e = {z,
            z + 1} ∧ (z ∈ T.cells ∨ z - I ∈ T.cells)) ∨ (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z -
            1 ∈ T.cells))) ) := by
  classical
  intro I T e he
  rcases he with ⟨x, hx, h | h | h | h⟩
  · exact Or.inl ⟨x, h, Or.inl hx⟩
  · exact Or.inr ⟨x, h, Or.inl hx⟩
  · refine Or.inr ⟨x + 1, h, Or.inr ?_⟩
    simpa [add_sub_cancel_right] using hx
  · refine Or.inl ⟨x + I, ?_, Or.inr ?_⟩
    · simpa [I, Zsqrtd.ext_iff, add_comm, add_left_comm, add_assoc] using h
    · simpa [I, Zsqrtd.ext_iff] using hx

private theorem htripleEdges :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (Disjoint A.cells B.cells) →
            ((Disjoint B.cells C.cells) → ((Disjoint C.cells A.cells) → (
        let I : GaussianInt := ⟨0, 1⟩
        (∀ (x : GaussianInt), ∀ (y : GaussianInt), (({x, x + 1} : Finset GaussianInt) = {y,
            y + 1}) → (x = y)) → ((∀ (x : GaussianInt), ∀ (y : GaussianInt), (({x, x + I} :
            Finset GaussianInt) = {y, y + I}) → (x = y)) → ((∀ (x : GaussianInt), ∀ (y :
            GaussianInt), ({x, x + 1} : Finset GaussianInt) ≠ {y, y + I}) → ((∀ (T : ProtoTile),
            ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges T) → ((∃ z, e = {z, z + 1} ∧ (z ∈
            T.cells ∨ z - I ∈ T.cells)) ∨ (∃ z, e = {z, z + I} ∧ (z ∈ T.cells ∨ z - 1 ∈
            T.cells)))) → (FootprintEdges A ∩ FootprintEdges B ∩ FootprintEdges C = ∅))))))) ) := by
  classical
  intro A B C hdisjointAB hdisjointBC hdisjointCA I horiz_unique vert_unique horiz_ne_vert
      footprint_normalize
  rw [Set.eq_empty_iff_forall_notMem]
  intro e he
  rcases he with ⟨⟨heA, heB⟩, heC⟩
  have hdAB := Finset.disjoint_left.mp hdisjointAB
  have hdBC := Finset.disjoint_left.mp hdisjointBC
  have hdCA := Finset.disjoint_left.mp hdisjointCA
  rcases footprint_normalize A e heA with
      ⟨a, hea, ha⟩ | ⟨a, hea, ha⟩ <;>
    rcases footprint_normalize B e heB with
      ⟨b, heb, hb⟩ | ⟨b, heb, hb⟩ <;>
    rcases footprint_normalize C e heC with
      ⟨c, hec, hc⟩ | ⟨c, hec, hc⟩
  · have hab : a = b := horiz_unique a b (hea.symm.trans heb)
    have hac : a = c := horiz_unique a c (hea.symm.trans hec)
    subst b; subst c
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases hc with hc | hc
    all_goals first
      | exact hdAB ha hb
      | exact hdBC hb hc
      | exact hdCA hc ha
  · exact horiz_ne_vert a c (hea.symm.trans hec)
  · exact horiz_ne_vert a b (hea.symm.trans heb)
  · exact horiz_ne_vert a b (hea.symm.trans heb)
  · exact horiz_ne_vert b a (heb.symm.trans hea)
  · exact horiz_ne_vert b a (heb.symm.trans hea)
  · exact horiz_ne_vert c a (hec.symm.trans hea)
  · have hab : a = b := vert_unique a b (hea.symm.trans heb)
    have hac : a = c := vert_unique a c (hea.symm.trans hec)
    subst b; subst c
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rcases hc with hc | hc
    all_goals first
      | exact hdAB ha hb
      | exact hdBC hb hc
      | exact hdCA hc ha

private theorem hIEvABC :
    (by
      classical
      exact
        ∀ (C : ProtoTile), ∀ (AB : ProtoTile), (∀ (T : ProtoTile), (FootprintVertices T).Finite)
            → ((FootprintVertices AB ∪ FootprintVertices C).ncard + (FootprintVertices AB ∩
            FootprintVertices C).ncard = (FootprintVertices AB).ncard + (FootprintVertices
            C).ncard) ) := by
  classical
  intro C AB vertex_finite
  exact Set.ncard_union_add_ncard_inter
    (FootprintVertices AB) (FootprintVertices C)
    (vertex_finite AB) (vertex_finite C)

private theorem hIEeABC :
    (by
      classical
      exact
        ∀ (C : ProtoTile), ∀ (AB : ProtoTile), (∀ (T : ProtoTile), (FootprintEdges T).Finite) →
            ((FootprintEdges AB ∪ FootprintEdges C).ncard + (FootprintEdges AB ∩ FootprintEdges
            C).ncard = (FootprintEdges AB).ncard + (FootprintEdges C).ncard) ) := by
  classical
  intro C AB edge_finite
  exact Set.ncard_union_add_ncard_inter
    (FootprintEdges AB) (FootprintEdges C)
    (edge_finite AB) (edge_finite C)

private theorem hIEvCross :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (∀ (T : ProtoTile),
            (FootprintVertices T).Finite) → ((FootprintVertices A ∩ FootprintVertices C ∪
            FootprintVertices B ∩ FootprintVertices C).ncard + (FootprintVertices A ∩
            FootprintVertices C ∩ (FootprintVertices B ∩ FootprintVertices C)).ncard =
            (FootprintVertices A ∩ FootprintVertices C).ncard + (FootprintVertices B ∩
            FootprintVertices C).ncard) ) := by
  classical
  intro A B C vertex_finite
  exact Set.ncard_union_add_ncard_inter
    (FootprintVertices A ∩ FootprintVertices C)
    (FootprintVertices B ∩ FootprintVertices C)
    ((vertex_finite A).inter_of_left (FootprintVertices C))
    ((vertex_finite B).inter_of_left (FootprintVertices C))

private theorem hIEeCross :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (∀ (T : ProtoTile),
            (FootprintEdges T).Finite) → ((FootprintEdges A ∩ FootprintEdges C ∪ FootprintEdges B
            ∩ FootprintEdges C).ncard + (FootprintEdges A ∩ FootprintEdges C ∩ (FootprintEdges B
            ∩ FootprintEdges C)).ncard = (FootprintEdges A ∩ FootprintEdges C).ncard +
            (FootprintEdges B ∩ FootprintEdges C).ncard) ) := by
  classical
  intro A B C edge_finite
  exact Set.ncard_union_add_ncard_inter
    (FootprintEdges A ∩ FootprintEdges C)
    (FootprintEdges B ∩ FootprintEdges C)
    ((edge_finite A).inter_of_left (FootprintEdges C))
    ((edge_finite B).inter_of_left (FootprintEdges C))

private theorem htripleVfinite :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (∀ (T : ProtoTile),
            (FootprintVertices T).Finite) → ((FootprintVertices A ∩ FootprintVertices B ∩
            FootprintVertices C).Finite) ) := by
  classical
  intro A B C vertex_finite
  exact ((vertex_finite A).inter_of_left (FootprintVertices B)).inter_of_left
      (FootprintVertices C)

private theorem htripleVnonempty (A B C : ProtoTile)
    (htripleVcard : (FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C).ncard = 1) :
    (FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  rw [hempty, Set.ncard_empty] at htripleVcard
  omega

private theorem huniqueRho :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), ((FootprintVertices A ∩
            FootprintVertices B ∩ FootprintVertices C).ncard = 1) → (((FootprintVertices A ∩
            FootprintVertices B ∩ FootprintVertices C).Finite) → (∀ (rho : GaussianInt), (rho ∈
            FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C) → (∀ (z :
            GaussianInt), z ∈ FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C ↔ z
            = rho))) ) := by
  classical
  intro A B C htripleVcard htripleVfinite rho hrho z
  constructor
  · intro hz
    have hsubset : (↑({z, rho} : Finset GaussianInt) : Set GaussianInt) ⊆
        FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C := by
      intro w hw
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hz
      · exact hrho
    have hge := Set.ncard_le_ncard hsubset htripleVfinite
    rw [htripleVcard] at hge
    exact (Set.ncard_le_one ({z, rho} : Finset GaussianInt).finite_toSet).mp
      hge z (by simp) rho (by simp)
  · rintro rfl
    exact hrho

private theorem footprint_incident :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (T.cells.Nonempty) → (∀ (z : GaussianInt), (z ∈ FootprintVertices T) →
            (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ T.cells)) ) := by
  classical
  intro T hne z hz
  let I : GaussianInt := ⟨0, 1⟩
  unfold FootprintVertices at hz
  rw [ite_eq_left hne] at hz
  rcases hz with ⟨c, hc, h | h | h | h⟩
  · subst z
    exact ⟨0, by simpa [LatticeVertexIncidentCell] using hc⟩
  · subst z
    refine ⟨1, ?_⟩
    simpa [LatticeVertexIncidentCell] using hc
  · subst z
    refine ⟨3, ?_⟩
    simpa [LatticeVertexIncidentCell, I, Zsqrtd.ext_iff] using hc
  · subst z
    refine ⟨2, ?_⟩
    change c + 1 + I - 1 - I ∈ T.cells
    convert hc using 1; ring

private theorem endpoint_of_third :
    (by
      classical
      exact
        ∀ (rho : GaussianInt), (∀ (T : ProtoTile), (T.cells.Nonempty) → (∀ (z : GaussianInt), (z
            ∈ FootprintVertices T) → (∃ j : Fin 4, LatticeVertexIncidentCell z j ∈ T.cells))) →
            (∀ (X : ProtoTile), ∀ (Y : ProtoTile), ∀ (Z : ProtoTile), (LatticeTile X) →
            ((LatticeTile Y) → ((Z.cells.Nonempty) → ((Disjoint X.cells Y.cells) → ((Disjoint
            X.cells Z.cells) → ((Disjoint Y.cells Z.cells) → ((FootprintVertices X ∩
            FootprintVertices Y =
            CommonFootprintEdgeVertices X Y) → ((rho ∈ FootprintVertices X ∩ FootprintVertices Y)
                → ((rho ∈ FootprintVertices Z) → (∀ (a : GaussianInt), ∀ (b : GaussianInt),
                (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y)
            (FootprintEdges X ∩ FootprintEdges Y) a b) → (rho = a ∨ rho = b))))))))))) ) := by
  classical
  intro rho footprint_incident X Y Z hX hY hZne hdXY hdXZ hdYZ hraw hrhoXY hrhoZ a b hpath
  have hcommonVertex : rho ∈ CommonFootprintEdgeVertices X Y := by
    rw [← hraw]
    exact hrhoXY
  rcases hcommonVertex with ⟨e, he, hrhoe⟩
  rcases SimpleGridPathPointTrichotomy
      (FootprintVertices X ∩ FootprintVertices Y)
      (FootprintEdges X ∩ FootprintEdges Y) a b rho hpath
      ⟨e, hrhoe, he⟩ with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rcases h with ⟨e, f, hef, hrhoe, hrhof, he, hf⟩
    have hsectors := (LocalLatticeInterfaceSectors).2 X Y rho
      hX hY hdXY ⟨e, f, hef, hrhoe, hrhof, he, hf⟩
    obtain ⟨j, hjZ⟩ := footprint_incident Z hZne rho hrhoZ
    rcases hsectors.1 j with hjX | hjY
    · exact ((Finset.disjoint_left.mp hdXZ) hjX hjZ).elim
    · exact ((Finset.disjoint_left.mp hdYZ) hjY hjZ).elim

private theorem hendAB :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (LatticeTile A) → ((LatticeTile
            B) → ((Disjoint A.cells B.cells) → ((Disjoint B.cells C.cells) → ((Disjoint C.cells
            A.cells) → ((C.cells.Nonempty) → ((FootprintVertices A ∩ FootprintVertices B =
            CommonFootprintEdgeVertices A B) → (∀ (xAB : GaussianInt), ∀ (yAB : GaussianInt),
            (SimpleGridPathBetween (FootprintVertices A ∩ FootprintVertices B) (FootprintEdges A
            ∩ FootprintEdges B) xAB yAB) → (∀ (rho : GaussianInt), (rho ∈ FootprintVertices A ∩
            FootprintVertices B ∩ FootprintVertices C) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile), (LatticeTile X) → ((LatticeTile Y) → ((Z.cells.Nonempty) →
            ((Disjoint X.cells Y.cells) → ((Disjoint X.cells Z.cells) → ((Disjoint Y.cells
            Z.cells) → ((FootprintVertices X ∩ FootprintVertices Y = CommonFootprintEdgeVertices
            X Y) → ((rho ∈ FootprintVertices X ∩ FootprintVertices Y) → ((rho ∈ FootprintVertices
            Z) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges Y) a
            b) → (rho = a ∨ rho = b))))))))))) → (rho = xAB ∨ rho = yAB)))))))))) ) := by
  classical
  intro A B C hA hB hdisjointAB hdisjointBC hdisjointCA hCne hVrawAB xAB yAB hpathAB rho hrho
      endpoint_of_third
  exact endpoint_of_third A B C hA hB hCne hdisjointAB hdisjointCA.symm
      hdisjointBC hVrawAB ⟨hrho.1.1, hrho.1.2⟩ hrho.2 xAB yAB hpathAB

private theorem hendBC :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (LatticeTile B) → ((LatticeTile
            C) → ((Disjoint A.cells B.cells) → ((Disjoint B.cells C.cells) → ((Disjoint C.cells
            A.cells) → ((A.cells.Nonempty) → ((FootprintVertices B ∩ FootprintVertices C =
            CommonFootprintEdgeVertices B C) → (∀ (xBC : GaussianInt), ∀ (yBC : GaussianInt),
            (SimpleGridPathBetween (FootprintVertices B ∩ FootprintVertices C) (FootprintEdges B
            ∩ FootprintEdges C) xBC yBC) → (∀ (rho : GaussianInt), (rho ∈ FootprintVertices A ∩
            FootprintVertices B ∩ FootprintVertices C) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile), (LatticeTile X) → ((LatticeTile Y) → ((Z.cells.Nonempty) →
            ((Disjoint X.cells Y.cells) → ((Disjoint X.cells Z.cells) → ((Disjoint Y.cells
            Z.cells) → ((FootprintVertices X ∩ FootprintVertices Y = CommonFootprintEdgeVertices
            X Y) → ((rho ∈ FootprintVertices X ∩ FootprintVertices Y) → ((rho ∈ FootprintVertices
            Z) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges Y) a
            b) → (rho = a ∨ rho = b))))))))))) → (rho = xBC ∨ rho = yBC)))))))))) ) := by
  classical
  intro A B C hB hC hdisjointAB hdisjointBC hdisjointCA hAne hVrawBC xBC yBC hpathBC rho hrho
      endpoint_of_third
  exact endpoint_of_third B C A hB hC hAne hdisjointBC hdisjointAB.symm
      hdisjointCA hVrawBC ⟨hrho.1.2, hrho.2⟩ hrho.1.1 xBC yBC hpathBC

private theorem hendCA :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (LatticeTile A) → ((LatticeTile
            C) → ((Disjoint A.cells B.cells) → ((Disjoint B.cells C.cells) → ((Disjoint C.cells
            A.cells) → ((B.cells.Nonempty) → ((FootprintVertices C ∩ FootprintVertices A =
            CommonFootprintEdgeVertices C A) → (∀ (xCA : GaussianInt), ∀ (yCA : GaussianInt),
            (SimpleGridPathBetween (FootprintVertices C ∩ FootprintVertices A) (FootprintEdges C
            ∩ FootprintEdges A) xCA yCA) → (∀ (rho : GaussianInt), (rho ∈ FootprintVertices A ∩
            FootprintVertices B ∩ FootprintVertices C) → ((∀ (X : ProtoTile), ∀ (Y : ProtoTile),
            ∀ (Z : ProtoTile), (LatticeTile X) → ((LatticeTile Y) → ((Z.cells.Nonempty) →
            ((Disjoint X.cells Y.cells) → ((Disjoint X.cells Z.cells) → ((Disjoint Y.cells
            Z.cells) → ((FootprintVertices X ∩ FootprintVertices Y = CommonFootprintEdgeVertices
            X Y) → ((rho ∈ FootprintVertices X ∩ FootprintVertices Y) → ((rho ∈ FootprintVertices
            Z) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), (SimpleGridPathBetween
            (FootprintVertices X ∩ FootprintVertices Y) (FootprintEdges X ∩ FootprintEdges Y) a
            b) → (rho = a ∨ rho = b))))))))))) → (rho = xCA ∨ rho = yCA)))))))))) ) := by
  classical
  intro A B C hA hC hdisjointAB hdisjointBC hdisjointCA hBne hVrawCA xCA yCA hpathCA rho hrho
      endpoint_of_third
  exact endpoint_of_third C A B hC hA hBne hdisjointCA hdisjointBC.symm
      hdisjointAB hVrawCA ⟨hrho.2, hrho.1.1⟩ hrho.1.2 xCA yCA hpathCA

private theorem reverse_path :
    (by
      classical
      exact
        ∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀ {a : GaussianInt}, ∀
            {b : GaussianInt}, (SimpleGridPathBetween V E a b) → (SimpleGridPathBetween V E b a)
            ) := by
  classical
  intro V E a b hpath
  rcases hpath with ⟨p, hnodup, hlen, hhead, hlast, hvertices,
    hstep, hedges⟩
  refine ⟨p.reverse, List.nodup_reverse.mpr hnodup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · simpa using hlast
  · simpa using hhead
  · rw [hvertices]
    ext z
    simp
  · intro x y l₁ l₂ hrev
    have hforward : p = l₂.reverse ++ y :: x :: l₁.reverse := by
      have := congrArg List.reverse hrev
      simpa [List.reverse_append, List.append_assoc] using this
    rcases hstep y x l₂.reverse l₁.reverse hforward with h | h | h | h
    · right; left
      rw [h]
      ring
    · left
      rw [h]
      ring
    · right; right; right
      rw [h]
      ring
    · right; right; left
      rw [h]
      ring
  · intro e
    constructor
    · intro he
      rcases (hedges e).1 he with ⟨x, y, l₁, l₂, hp, rfl⟩
      refine ⟨y, x, l₂.reverse, l₁.reverse, ?_, ?_⟩
      · rw [hp]
        simp [List.reverse_append, List.append_assoc]
      · simp [Finset.pair_comm]
    · rintro ⟨x, y, l₁, l₂, hrev, rfl⟩
      apply (hedges {x, y}).2
      refine ⟨y, x, l₂.reverse, l₁.reverse, ?_, ?_⟩
      · have := congrArg List.reverse hrev
        simpa [List.reverse_append, List.append_assoc] using this
      · simp [Finset.pair_comm]

private theorem orient_path :
    (by
      classical
      exact
        ∀ (rho : GaussianInt), (∀ {V : Set GaussianInt}, ∀ {E : Set (Finset GaussianInt)}, ∀
            {a : GaussianInt}, ∀ {b : GaussianInt}, (SimpleGridPathBetween V E a b) →
            (SimpleGridPathBetween V E b a)) → (∀ {V : Set GaussianInt}, ∀
            {E : Set (Finset GaussianInt)}, ∀ {a : GaussianInt}, ∀ {b : GaussianInt},
            (SimpleGridPathBetween V E a b) → ((rho = a ∨ rho = b) → (∃ other : GaussianInt,
            SimpleGridPathBetween V E rho other))) ) := by
  classical
  intro rho reverse_path V E a b hpath hend
  rcases hend with h | h
  · subst a
    exact ⟨b, hpath⟩
  · subst b
    exact ⟨a, reverse_path hpath⟩

end ThreeDiskJunctionGeometry

theorem LatticeTileThreeDiskJunction
    (A B C AB BC CA ABC : ProtoTile)
    (hA : LatticeTile A) (hB : LatticeTile B) (hC : LatticeTile C)
    (hAB : LatticeTile AB) (hBC : LatticeTile BC)
    (hCA : LatticeTile CA) (hABC : LatticeTile ABC)
    (hdisjointAB : Disjoint A.cells B.cells)
    (hdisjointBC : Disjoint B.cells C.cells)
    (hdisjointCA : Disjoint C.cells A.cells)
    (hunionAB : ∀ z : LatticeCell,
      z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells)
    (hunionBC : ∀ z : LatticeCell,
      z ∈ BC.cells ↔ z ∈ B.cells ∨ z ∈ C.cells)
    (hunionCA : ∀ z : LatticeCell,
      z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈ A.cells)
    (hunionABC : ∀ z : LatticeCell,
      z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈ C.cells)
    (hcommonAB : (FootprintEdges A ∩ FootprintEdges B).Nonempty)
    (hcommonBC : (FootprintEdges B ∩ FootprintEdges C).Nonempty)
    (hcommonCA : (FootprintEdges C ∩ FootprintEdges A).Nonempty) :
    Nonempty (ExactTileInterfaceTriple A B C) := by
-- BODY
  classical
  have hAgrid := LatticeTileGridStructure A hA
  have hBgrid := LatticeTileGridStructure B hB
  have hCgrid := LatticeTileGridStructure C hC
  have hABgrid := LatticeTileGridStructure AB hAB
  have hBCgrid := LatticeTileGridStructure BC hBC
  have hCAgrid := LatticeTileGridStructure CA hCA
  have hABCgrid := LatticeTileGridStructure ABC hABC
  have hAne : A.cells.Nonempty := hAgrid.1.1
  have hBne : B.cells.Nonempty := hBgrid.1.1
  have hCne : C.cells.Nonempty := hCgrid.1.1
  have hABne : AB.cells.Nonempty := hABgrid.1.1
  have hBCne : BC.cells.Nonempty := hBCgrid.1.1
  have hCAne : CA.cells.Nonempty := hCAgrid.1.1
  have hABCne : ABC.cells.Nonempty := hABCgrid.1.1
  have vertex_union (U V W : ProtoTile)
      (hUne : U.cells.Nonempty) (hVne : V.cells.Nonempty)
      (hWne : W.cells.Nonempty)
      (hunion : forall z : LatticeCell,
        z ∈ W.cells ↔ z ∈ U.cells ∨ z ∈ V.cells) := ThreeDiskJunctionGeometry.vertex_union U V W
            hUne hVne hWne hunion
  have edge_union (U V W : ProtoTile)
      (hunion : forall z : LatticeCell,
        z ∈ W.cells ↔ z ∈ U.cells ∨ z ∈ V.cells) := ThreeDiskJunctionGeometry.edge_union U V W
            hunion
  have vertex_finite (T : ProtoTile) := ThreeDiskJunctionGeometry.vertex_finite T
  have edge_finite (T : ProtoTile) := ThreeDiskJunctionGeometry.edge_finite T
  have hVAB := vertex_union A B AB hAne hBne hABne hunionAB
  have hVBC := vertex_union B C BC hBne hCne hBCne hunionBC
  have hVCA := vertex_union C A CA hCne hAne hCAne hunionCA
  have hEAB := edge_union A B AB hunionAB
  have hEBC := edge_union B C BC hunionBC
  have hECA := edge_union C A CA hunionCA
  have hunionAB_C := ThreeDiskJunctionGeometry.hunionAB_C A B C AB ABC hunionAB hunionABC
  have hVABC := vertex_union AB C ABC hABne hCne hABCne hunionAB_C
  have hEABC := edge_union AB C ABC hunionAB_C
  obtain ⟨hVrawAB, ⟨xAB, yAB, hpathAB0⟩, -, -⟩ :=
    LatticeTileDiskUnionInterface A B AB hA hB hAB hdisjointAB
      hunionAB hcommonAB
  obtain ⟨hVrawBC, ⟨xBC, yBC, hpathBC0⟩, -, -⟩ :=
    LatticeTileDiskUnionInterface B C BC hB hC hBC hdisjointBC
      hunionBC hcommonBC
  obtain ⟨hVrawCA, ⟨xCA, yCA, hpathCA0⟩, -, -⟩ :=
    LatticeTileDiskUnionInterface C A CA hC hA hCA hdisjointCA
      hunionCA hcommonCA
  have hpathAB := ThreeDiskJunctionGeometry.hpathAB A B hVrawAB xAB yAB hpathAB0
  have hpathBC := ThreeDiskJunctionGeometry.hpathBC B C hVrawBC xBC yBC hpathBC0
  have hpathCA := ThreeDiskJunctionGeometry.hpathCA A C hVrawCA xCA yCA hpathCA0
  have hcellsAB := ThreeDiskJunctionGeometry.hcellsAB A B AB hdisjointAB hunionAB
  have hcellsBC := ThreeDiskJunctionGeometry.hcellsBC B C BC hdisjointBC hunionBC
  have hcellsCA := ThreeDiskJunctionGeometry.hcellsCA A C CA hdisjointCA hunionCA
  have hdisjointAB_C := ThreeDiskJunctionGeometry.hdisjointAB_C A B C AB hdisjointBC hdisjointCA
      hunionAB
  have hcellsABC := ThreeDiskJunctionGeometry.hcellsABC A B C AB ABC hunionAB_C hcellsAB
      hdisjointAB_C
  have hIEvAB := Set.ncard_union_add_ncard_inter
    (FootprintVertices A) (FootprintVertices B) (vertex_finite A) (vertex_finite B)
  have hIEvBC := Set.ncard_union_add_ncard_inter
    (FootprintVertices B) (FootprintVertices C) (vertex_finite B) (vertex_finite C)
  have hIEvCA := Set.ncard_union_add_ncard_inter
    (FootprintVertices C) (FootprintVertices A) (vertex_finite C) (vertex_finite A)
  have hIEeAB := Set.ncard_union_add_ncard_inter
    (FootprintEdges A) (FootprintEdges B) (edge_finite A) (edge_finite B)
  have hIEeBC := Set.ncard_union_add_ncard_inter
    (FootprintEdges B) (FootprintEdges C) (edge_finite B) (edge_finite C)
  have hIEeCA := Set.ncard_union_add_ncard_inter
    (FootprintEdges C) (FootprintEdges A) (edge_finite C) (edge_finite A)
  rw [← hVAB] at hIEvAB
  rw [← hVBC] at hIEvBC
  rw [← hVCA] at hIEvCA
  rw [← hEAB] at hIEeAB
  rw [← hEBC] at hIEeBC
  rw [← hECA] at hIEeCA
  let I : GaussianInt := ⟨0, 1⟩
  have horiz_unique (x y : GaussianInt)
      (h : ({x, x + 1} : Finset GaussianInt) = {y, y + 1}) :=
          ThreeDiskJunctionGeometry.horiz_unique x y h
  have vert_unique (x y : GaussianInt)
      (h : ({x, x + I} : Finset GaussianInt) = {y, y + I}) :=
          ThreeDiskJunctionGeometry.vert_unique x y h
  have horiz_ne_vert (x y : GaussianInt) := ThreeDiskJunctionGeometry.horiz_ne_vert x y
  have footprint_normalize (T : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ FootprintEdges T) := ThreeDiskJunctionGeometry.footprint_normalize T e he
  have htripleEdges :
      FootprintEdges A ∩ FootprintEdges B ∩ FootprintEdges C = ∅ :=
          ThreeDiskJunctionGeometry.htripleEdges A B C hdisjointAB hdisjointBC hdisjointCA
          horiz_unique vert_unique horiz_ne_vert footprint_normalize
  have hIEvABC := ThreeDiskJunctionGeometry.hIEvABC C AB vertex_finite
  have hIEeABC := ThreeDiskJunctionGeometry.hIEeABC C AB edge_finite
  rw [← hVABC] at hIEvABC
  rw [← hEABC] at hIEeABC
  have hcrossV : FootprintVertices AB ∩ FootprintVertices C =
      (FootprintVertices A ∩ FootprintVertices C) ∪
        (FootprintVertices B ∩ FootprintVertices C) := by
    rw [hVAB]
    exact Set.union_inter_distrib_right _ _ _
  have hcrossE : FootprintEdges AB ∩ FootprintEdges C =
      (FootprintEdges A ∩ FootprintEdges C) ∪
        (FootprintEdges B ∩ FootprintEdges C) := by
    rw [hEAB]
    exact Set.union_inter_distrib_right _ _ _
  rw [hcrossV] at hIEvABC
  rw [hcrossE] at hIEeABC
  have hIEvCross := ThreeDiskJunctionGeometry.hIEvCross A B C vertex_finite
  have hIEeCross := ThreeDiskJunctionGeometry.hIEeCross A B C edge_finite
  have htripleVset :
      (FootprintVertices A ∩ FootprintVertices C) ∩
          (FootprintVertices B ∩ FootprintVertices C) =
        FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C :=
            (Set.inter_inter_distrib_right _ _ _).symm
  have htripleEset :
      (FootprintEdges A ∩ FootprintEdges C) ∩
          (FootprintEdges B ∩ FootprintEdges C) =
        FootprintEdges A ∩ FootprintEdges B ∩ FootprintEdges C :=
            (Set.inter_inter_distrib_right _ _ _).symm
  rw [htripleVset] at hIEvCross
  rw [htripleEset, htripleEdges] at hIEeCross
  simp only [Set.ncard_empty, add_zero] at hIEeCross
  have hEulerA := LatticeTileGridEulerCount A hA
  have hEulerB := LatticeTileGridEulerCount B hB
  have hEulerC := LatticeTileGridEulerCount C hC
  have hEulerAB := LatticeTileGridEulerCount AB hAB
  have hEulerBC := LatticeTileGridEulerCount BC hBC
  have hEulerCA := LatticeTileGridEulerCount CA hCA
  have hEulerABC := LatticeTileGridEulerCount ABC hABC
  have htripleVcard := (show
      (FootprintVertices A ∩ FootprintVertices B ∩ FootprintVertices C).ncard = 1
    from by
      classical
      rw [Set.inter_comm (FootprintVertices C) (FootprintVertices A)] at hIEvCA
      rw [Set.inter_comm (FootprintEdges C) (FootprintEdges A)] at hIEeCA
      omega)
  have htripleVfinite := ThreeDiskJunctionGeometry.htripleVfinite A B C vertex_finite
  have htripleVnonempty := ThreeDiskJunctionGeometry.htripleVnonempty A B C htripleVcard
  obtain ⟨rho, hrho⟩ := htripleVnonempty
  have huniqueRho (z : GaussianInt) := ThreeDiskJunctionGeometry.huniqueRho A B C htripleVcard
      htripleVfinite rho hrho z
  have footprint_incident (T : ProtoTile) (hne : T.cells.Nonempty)
      (z : GaussianInt) (hz : z ∈ FootprintVertices T) :=
          ThreeDiskJunctionGeometry.footprint_incident T hne z hz
  have endpoint_of_third (X Y Z : ProtoTile)
      (hX : LatticeTile X) (hY : LatticeTile Y)
      (hZne : Z.cells.Nonempty)
      (hdXY : Disjoint X.cells Y.cells)
      (hdXZ : Disjoint X.cells Z.cells)
      (hdYZ : Disjoint Y.cells Z.cells)
      (hraw : FootprintVertices X ∩ FootprintVertices Y =
        CommonFootprintEdgeVertices X Y)
      (hrhoXY : rho ∈ FootprintVertices X ∩ FootprintVertices Y)
      (hrhoZ : rho ∈ FootprintVertices Z)
      (a b : GaussianInt)
      (hpath : SimpleGridPathBetween
        (FootprintVertices X ∩ FootprintVertices Y)
        (FootprintEdges X ∩ FootprintEdges Y) a b) := ThreeDiskJunctionGeometry.endpoint_of_third
            rho footprint_incident X Y Z hX hY hZne hdXY hdXZ hdYZ hraw hrhoXY hrhoZ a b hpath
  have hendAB := ThreeDiskJunctionGeometry.hendAB A B C hA hB hdisjointAB hdisjointBC hdisjointCA
      hCne hVrawAB xAB yAB hpathAB rho hrho endpoint_of_third
  have hendBC := ThreeDiskJunctionGeometry.hendBC A B C hB hC hdisjointAB hdisjointBC hdisjointCA
      hAne hVrawBC xBC yBC hpathBC rho hrho endpoint_of_third
  have hendCA := ThreeDiskJunctionGeometry.hendCA A B C hA hC hdisjointAB hdisjointBC hdisjointCA
      hBne hVrawCA xCA yCA hpathCA rho hrho endpoint_of_third
  have reverse_path {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {a b : GaussianInt} (hpath : SimpleGridPathBetween V E a b) :=
          ThreeDiskJunctionGeometry.reverse_path (V := V) (E := E) (a := a) (b := b) hpath
  have orient_path {V : Set GaussianInt} {E : Set (Finset GaussianInt)}
      {a b : GaussianInt} (hpath : SimpleGridPathBetween V E a b)
      (hend : rho = a ∨ rho = b) := ThreeDiskJunctionGeometry.orient_path rho reverse_path (V :=
          V) (E := E) (a := a) (b := b) hpath hend
  obtain ⟨otherAB, pathAB⟩ := orient_path hpathAB hendAB
  obtain ⟨otherBC, pathBC⟩ := orient_path hpathBC hendBC
  obtain ⟨otherCA, pathCA⟩ := orient_path hpathCA hendCA
  exact ⟨{
    point := rho
    otherAB := otherAB
    otherBC := otherBC
    otherCA := otherCA
    pathAB := pathAB
    pathBC := pathBC
    pathCA := pathCA
    unique_common := huniqueRho
  }⟩

end ApollonianSuperharmonic

end
