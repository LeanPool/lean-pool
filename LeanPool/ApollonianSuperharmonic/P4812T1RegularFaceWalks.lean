/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4812T1AffineDrawing
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.P4677T2TouchingWalk
public import LeanPool.ApollonianSuperharmonic.P4733T1WalkTransport
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.PlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.SimpleGridPath
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges

-- [TABLET NODE: P4812T1RegularFaceWalks]

/-!
# P4812T1RegularFaceWalks

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RegularFaceWalkProof

private theorem boundaryFoot :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ z ∈ BoundaryFootprintVertices W, z ∈ FootprintVertices W
    ) := by
  classical
  intro W z hz
  by_cases hW : W.cells.Nonempty
  · simp only [BoundaryFootprintVertices, ite_eq_left hW, Set.mem_ofPred_eq] at hz
    rcases hz with ⟨e, he, hze⟩
    have he' : e ∈ FootprintEdges W := by
      change ∃ c ∈ W.cells,
        e = {c, c + 1} ∨ e = {c, c + ⟨0, 1⟩} ∨
          e = {c + 1, c + 1 + ⟨0, 1⟩} ∨
            e = {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}
      rcases he with ⟨w, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
      · rcases h with ⟨hw, _⟩ | ⟨_, hw⟩
        · exact ⟨w, hw, Or.inl rfl⟩
        · refine ⟨w - ⟨0, 1⟩, hw, Or.inr (Or.inr (Or.inr ?_))⟩
          congr 1 <;> simp [Zsqrtd.ext_iff]
      · rcases h with ⟨hw, _⟩ | ⟨_, hw⟩
        · exact ⟨w, hw, Or.inr (Or.inl rfl)⟩
        · refine ⟨w - 1, hw, Or.inr (Or.inr (Or.inl ?_))⟩
          congr 1 <;> simp []
    rcases he' with ⟨c, hc, hcE⟩
    rcases hcE with hcE | hcE | hcE | hcE
    all_goals
      simp only [FootprintVertices, ite_eq_left hW]
      rw [hcE] at hze
      simp only [Finset.mem_insert, Finset.mem_singleton] at hze
      rcases hze with hze | hze <;> subst z
    · exact ⟨c, hc, Or.inl rfl⟩
    · exact ⟨c, hc, Or.inr (Or.inl rfl)⟩
    · exact ⟨c, hc, Or.inl rfl⟩
    · exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨c, hc, Or.inr (Or.inl rfl)⟩
    · exact ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩
    · exact ⟨c, hc, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨c, hc, Or.inr (Or.inr (Or.inr rfl))⟩
  · simpa [BoundaryFootprintVertices, FootprintVertices, hW] using hz

private theorem translateComp :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (v : GaussianInt), ∀ (w : GaussianInt), TileTranslation
            (TileTranslation W v) w = TileTranslation W (v + w)
    ) := by
  classical
  intro W v w
  cases W with
  | mk cells anchor =>
    simp only [TileTranslation]
    rw [ProtoTile.mk.injEq]
    constructor
    · rw [Finset.image_image]
      congr 1
      funext z
      simp [GaussianTranslation, add_assoc]
    · simp [GaussianTranslation, add_assoc]

private theorem edgeDiff :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        (k (1, 1) = a + b) → ((k (-1, -1) = -(a + b)) → ((k (-1, 0) = -a) → ((k (0, -1) = -b) →
            (∀ (x : ↥L), ∀ (y : ↥L), D.plane.adjacent x y → y = x + a ∨ x = y + a ∨ y = x + b ∨ x
            = y + b ∨ y = x + (a + b) ∨ x = y + (a + b)))))
    ) := by
  classical
  intro L k D a b k11 kneg11 kneg10 kneg01 x y hxy
  have hc := (D.adjacent_iff x y).mp hxy
  have forward {z : L} (hz : y - x = z) : y = x + z := by
    calc y = (y - x) + x := by abel
      _ = z + x := congrArg (fun t : L => t + x) hz
      _ = x + z := add_comm _ _
  have backward {z : L} (hz : y - x = -z) : x = y + z := by
    have hz' : x - y = z := by
      calc x - y = -(y - x) := by abel
        _ = -(-z) := congrArg Neg.neg hz
        _ = z := by simp
    calc x = (x - y) + y := by abel
      _ = z + y := congrArg (fun t : L => t + y) hz'
      _ = y + z := add_comm _ _
  rcases hc with h1 | h2 | h3 | h4 | h5 | h6
  · have hm : y - x = a := by
      simpa [map_sub, k.apply_symm_apply, a, b] using congrArg k h1
    exact Or.inl (forward hm)
  · have hm : y - x = b := by
      simpa [map_sub, k.apply_symm_apply, a, b] using congrArg k h2
    exact Or.inr (Or.inr (Or.inl (forward hm)))
  · have hm : y - x = -(a + b) := by
      simpa [map_sub, k.apply_symm_apply, kneg11] using congrArg k h3
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (backward hm)))))
  · have hm : y - x = -a := by
      simpa [map_sub, k.apply_symm_apply, kneg10] using congrArg k h4
    exact Or.inr (Or.inl (backward hm))
  · have hm : y - x = -b := by
      simpa [map_sub, k.apply_symm_apply, kneg01] using congrArg k h5
    exact Or.inr (Or.inr (Or.inr (Or.inl (backward hm))))
  · have hm : y - x = a + b := by
      simpa [map_sub, k.apply_symm_apply, a, b, k11] using congrArg k h6
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (forward hm)))))

private theorem uniquePair :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (x : ↥L), ∀ (y : ↥L), D.plane.adjacent x y → ∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), f ≠ g → c ≠ d → ((∃ (i :
            Fin (3 : ℕ)), D.plane.faceVertex f i = x) ∧ ∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f
            i = y) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) ∧ ∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex c i = x) ∧ ∃
            (i : Fin (3 : ℕ)), D.plane.faceVertex c i = y) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex d i = x) ∧ ∃ (i : Fin (3 : ℕ)), D.plane.faceVertex d i = y) → f =
            c ∧ g = d ∨ f = d ∧ g = c
    ) := by
  classical
  intro L k D x y hxy f g c d hfg hcd hf hg hc hd
  obtain ⟨p, q, hpq, hp, hq, hu⟩ := D.plane.every_edge_two_faces x y hxy
  have hmem (z : D.plane.Face)
      (hz : (∃ i, D.plane.faceVertex z i = x) ∧
        (∃ i, D.plane.faceVertex z i = y)) : z = p ∨ z = q := hu z hz
  have hfg' : (f = p ∧ g = q) ∨ (f = q ∧ g = p) := by
    rcases hmem f hf with hfp | hfp
    · rcases hmem g hg with hgp | hgp
      · exact False.elim (hfg (hfp.trans hgp.symm))
      · exact Or.inl ⟨hfp, hgp⟩
    · rcases hmem g hg with hgp | hgp
      · exact Or.inr ⟨hfp, hgp⟩
      · exact False.elim (hfg (hfp.trans hgp.symm))
  have hcd' : (c = p ∧ d = q) ∨ (c = q ∧ d = p) := by
    rcases hmem c hc with hcp | hcp
    · rcases hmem d hd with hdp | hdp
      · exact False.elim (hcd (hcp.trans hdp.symm))
      · exact Or.inl ⟨hcp, hdp⟩
    · rcases hmem d hd with hdp | hdp
      · exact Or.inr ⟨hcp, hdp⟩
      · exact False.elim (hcd (hcp.trans hdp.symm))
  rcases hfg' with ⟨hfp, hgq⟩ | ⟨hfq, hgp⟩
  · rcases hcd' with ⟨hcp, hdq⟩ | ⟨hcq, hdp⟩
    · exact Or.inl ⟨hfp.trans hcp.symm, hgq.trans hdq.symm⟩
    · exact Or.inr ⟨hfp.trans hdp.symm, hgq.trans hcq.symm⟩
  · rcases hcd' with ⟨hcp, hdq⟩ | ⟨hcq, hdp⟩
    · exact Or.inr ⟨hfq.trans hdq.symm, hgp.trans hcp.symm⟩
    · exact Or.inl ⟨hfq.trans hcq.symm, hgp.trans hdp.symm⟩

private theorem rho_mem :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (W : ProtoTile), ∀ (z : GaussianInt), (z ∈ BoundaryFootprintVertices W) → (z ∈
            FootprintVertices W)) → ((∀ (W : ProtoTile), ∀ (z : GaussianInt), ∀ (v :
            GaussianInt), (z ∈ BoundaryFootprintVertices W) → (z + v ∈ BoundaryFootprintVertices
            (TileTranslation W v))) → ((∀ (W : ProtoTile), ∀ (v : GaussianInt), ∀ (w :
            GaussianInt), TileTranslation (TileTranslation W v) w = TileTranslation W (v + w)) →
            ((ru ∈ BoundaryFootprintVertices T) → ((ru ∈ BoundaryFootprintVertices
            (TileTranslation T (a : GaussianInt))) → ((ru ∈ BoundaryFootprintVertices
            (TileTranslation T (-(b : GaussianInt)))) → ((rd ∈ BoundaryFootprintVertices T) →
            ((rd ∈ BoundaryFootprintVertices (TileTranslation T (-(a : GaussianInt)))) → ((rd ∈
            BoundaryFootprintVertices (TileTranslation T (b : GaussianInt))) → (∀ (q : ↥L ⊕ ↥L),
            ∀ (i : Fin (3 : ℕ)), rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) q) ∈ FootprintVertices
            (TileTranslation T (↑(D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L → D.plane.Face) q) i) :
            GaussianInt)))))))))))
    ) := by
  classical
  intro L k D T a b ru rd rho boundaryFoot translateBoundary translateComp ru0 rua rub rd0 rda
      rdb q i
  cases q with
  | inl x =>
    unfold rho
    rw [D.faces.symm_apply_apply]
    obtain ⟨hv0, hv1, hv2⟩ := D.up_vertices x
    fin_cases i
    · change ru + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((D.plane.faceVertex (D.faces (.inl x)) 0 : L) :
            GaussianInt))
      rw [hv0]
      exact boundaryFoot _ _ (translateBoundary T ru (x : GaussianInt) ru0)
    · change ru + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((D.plane.faceVertex (D.faces (.inl x)) 1 : L) :
            GaussianInt))
      rw [hv1]
      have heq : (x + a : L) = a + x := add_comm x a
      rw [heq]
      simp only [AddSubgroup.coe_add]
      change ru + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((a : GaussianInt) + (x : GaussianInt)))
      rw [← translateComp T (a : GaussianInt) (x : GaussianInt)]
      exact boundaryFoot _ _ (translateBoundary (TileTranslation T (a : GaussianInt))
        ru (x : GaussianInt) rua)
    · change ru + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((D.plane.faceVertex (D.faces (.inl x)) 2 : L) :
            GaussianInt))
      rw [hv2]
      have heq : (x - b : L) = (-b) + x := by abel
      rw [heq]
      simp only [AddSubgroup.coe_add]
      change ru + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T (-(b : GaussianInt) + (x : GaussianInt)))
      rw [← translateComp T (-(b : GaussianInt)) (x : GaussianInt)]
      exact boundaryFoot _ _ (translateBoundary (TileTranslation T (-(b : GaussianInt)))
        ru (x : GaussianInt) rub)
  | inr x =>
    unfold rho
    rw [D.faces.symm_apply_apply]
    obtain ⟨hv0, hv1, hv2⟩ := D.down_vertices x
    fin_cases i
    · change rd + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((D.plane.faceVertex (D.faces (.inr x)) 0 : L) :
            GaussianInt))
      rw [hv0]
      exact boundaryFoot _ _ (translateBoundary T rd (x : GaussianInt) rd0)
    · change rd + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((D.plane.faceVertex (D.faces (.inr x)) 1 : L) :
            GaussianInt))
      rw [hv1]
      have heq : (x - a : L) = (-a) + x := by abel
      rw [heq]
      simp only [AddSubgroup.coe_add]
      change rd + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T (-(a : GaussianInt) + (x : GaussianInt)))
      rw [← translateComp T (-(a : GaussianInt)) (x : GaussianInt)]
      exact boundaryFoot _ _ (translateBoundary (TileTranslation T (-(a : GaussianInt)))
        rd (x : GaussianInt) rda)
    · change rd + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((D.plane.faceVertex (D.faces (.inr x)) 2 : L) :
            GaussianInt))
      rw [hv2]
      have heq : (x + b : L) = b + x := add_comm x b
      rw [heq]
      simp only [AddSubgroup.coe_add]
      change rd + (x : GaussianInt) ∈
        FootprintVertices (TileTranslation T ((b : GaussianInt) + (x : GaussianInt)))
      rw [← translateComp T (b : GaussianInt) (x : GaussianInt)]
      exact boundaryFoot _ _ (translateBoundary (TileTranslation T (b : GaussianInt))
        rd (x : GaussianInt) rdb)

private theorem transZero :
    (by
      classical
      exact
        ∀ (W : ProtoTile), TileTranslation W (0 : GaussianInt) = W
    ) := by
  classical
  intro W
  cases W with
  | mk cells anchor =>
    simp only [TileTranslation]
    rw [ProtoTile.mk.injEq]
    constructor
    · change cells.image (GaussianTranslation 0) = cells
      have h : GaussianTranslation 0 = id := by
        funext z
        simp [GaussianTranslation]
      rw [h, Finset.image_id]
    · simp [GaussianTranslation]

private theorem mapTranslateRev :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), (∀ (p : List GaussianInt), ∀ (x : L), ∀ (u : L), p.map
            (fun z => z + ((u + x : L) : GaussianInt)) = (p.map (fun z => z + (x :
            GaussianInt))).map (fun z => z + (u : GaussianInt))) → (∀ (p : List GaussianInt), ∀
            (x : ↥L), ∀ (u : ↥L), (List.map (fun (z : GaussianInt) => z + (↑(u + x) :
            GaussianInt)) p).reverse = List.map (fun (z : GaussianInt) => z + (↑u : GaussianInt))
            (List.map (fun (z : GaussianInt) => z + (↑x : GaussianInt)) p).reverse)
    ) := by
  classical
  intro L mapTranslate p x u
  calc
    _ = ((p.map (fun z => z + (x : GaussianInt))).map
        (fun z => z + (u : GaussianInt))).reverse := by
          exact congrArg List.reverse (mapTranslate p x u)
    _ = (((p.map (fun z => z + (x : GaussianInt))).reverse).map
        (fun z => z + (u : GaussianInt))) := by
          simp [List.map_reverse]

private theorem ifMap3 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (u : ↥L), ∀ (P0 : Prop), ∀ (P1 : Prop), ∀ (P2 : Prop),
            ∀ (Q0 : Prop), ∀ (Q1 : Prop), ∀ (Q2 : Prop), (P0 ↔ Q0) → (P1 ↔ Q1) → (P2 ↔ Q2) → ∀
            (A0 : List GaussianInt), ∀ (A1 : List GaussianInt), ∀ (A2 : List GaussianInt), ∀ (B0
            : List GaussianInt), ∀ (B1 : List GaussianInt), ∀ (B2 : List GaussianInt), A0 =
            List.map (fun (z : GaussianInt) => z + (↑u : GaussianInt)) B0 → A1 = List.map (fun (z
            : GaussianInt) => z + (↑u : GaussianInt)) B1 → A2 = List.map (fun (z : GaussianInt)
            => z + (↑u : GaussianInt)) B2 → (if P0 then A0 else if P1 then A1 else if P2 then A2
            else []) = List.map (fun (z : GaussianInt) => z + (↑u : GaussianInt)) (if Q0 then B0
            else if Q1 then B1 else if Q2 then B2 else [])
    ) := by
  classical
  intro L u P0 P1 P2 Q0 Q1 Q2 h0 h1 h2 A0 A1 A2 B0 B1 B2 m0 m1 m2
  by_cases hq0 : Q0 <;> by_cases hq1 : Q1 <;> by_cases hq2 : Q2 <;>
    simp [h0, h1, h2, hq0, hq1, hq2, m0, m1, m2]

private theorem boundaryEdgeFoot :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ e ∈ BoundaryFootprintEdges W, e ∈ FootprintEdges W
    ) := by
  classical
  intro W e he
  simp only [BoundaryFootprintEdges, Set.mem_ofPred_eq] at he
  simp only [FootprintEdges, Set.mem_ofPred_eq]
  change ∃ c ∈ W.cells,
    e = {c, c + 1} ∨ e = {c, c + ⟨0, 1⟩} ∨
      e = {c + 1, c + 1 + ⟨0, 1⟩} ∨
        e = {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}
  rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
  · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inl rfl⟩
    · refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
      congr 1 <;> simp [Zsqrtd.ext_iff]
  · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
    · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
      congr 1 <;> simp []

private theorem commonEdgeTouch :
    (by
      classical
      exact
        (∀ (W : ProtoTile), ∀ (e : Finset GaussianInt), (e ∈ BoundaryFootprintEdges W) → (e ∈
            FootprintEdges W)) → (∀ (V : ProtoTile), ∀ (W : ProtoTile), Finset.Nonempty V.cells →
            Finset.Nonempty W.cells → TileTouching V W → (FootprintEdges V ∩ FootprintEdges
            W).Nonempty)
    ) := by
  classical
  intro boundaryEdgeFoot V W hneV hneW h
  rcases h with h | h | h
  · rcases h with ⟨_, _, _, hp⟩
    rcases hp with ⟨p, _, hlen, _, _, hedges⟩
    cases p with
    | nil => simp at hlen
    | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y ys =>
        let e : Finset GaussianInt := {x, y}
        have he : e ∈ BoundaryFootprintEdges V ∩ BoundaryFootprintEdges W := by
          apply (hedges e).2
          refine ⟨x, y, [], ys, ?_, ?_⟩
          · rfl
          · simp [e]
        exact ⟨e, boundaryEdgeFoot V e he.1, boundaryEdgeFoot W e he.2⟩
  · exact (Finset.nonempty_iff_ne_empty.mp hneV h.1).elim
  · exact (Finset.nonempty_iff_ne_empty.mp hneW h.1).elim

private theorem rowEdge2 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        (∀ (W : ProtoTile), ∀ (v : GaussianInt), ∀ (w : GaussianInt), TileTranslation
            (TileTranslation W v) w = TileTranslation W (v + w)) → (∀ (e2 : Finset GaussianInt),
            (e2 ∈ FootprintEdges (TileTranslation T (↑a : GaussianInt)) ∩ FootprintEdges
            (TileTranslation T (-(↑b : GaussianInt)))) → ((∀ (V : ProtoTile), ∀ (v :
            GaussianInt), ∀ (e : Finset GaussianInt), (e ∈ FootprintEdges V) → (e.image
            (GaussianTranslation v) ∈ FootprintEdges (TileTranslation V v))) → ((∀ (v : L), ∀ (w
            : L), TileTranslation (TileTranslation T (v : GaussianInt)) (w : GaussianInt) =
            TileTranslation T ((v + w : L) : GaussianInt)) → (∀ (w : ↥L), Finset.image
            (GaussianTranslation (↑w : GaussianInt)) e2 ∈ FootprintEdges (TileTranslation T (↑(w
            + a) : GaussianInt)) ∩ FootprintEdges (TileTranslation T (↑(w - b) : GaussianInt))))))
    ) := by
  classical
  intro L k T a b translateComp e2 he2 footprintEdgeTranslate tileAdd w
  refine ⟨?_, ?_⟩
  · simpa [tileAdd, add_assoc, add_comm, add_left_comm] using
      footprintEdgeTranslate (TileTranslation T (a : GaussianInt))
        (w : GaussianInt) e2 he2.1
  · simpa [translateComp, AddSubgroup.coe_neg, AddSubgroup.coe_sub,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      footprintEdgeTranslate (TileTranslation T (-(b : GaussianInt)))
        (w : GaussianInt) e2 he2.2

private theorem rowWalk0 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        let fU := D.faces (.inl (0 : L))
        let fDa := D.faces (.inr a)
        ∀ (p0 : List GaussianInt), (p0.head? = some (rho fU) ∧ p0.getLast? = some (rho fDa) ∧ (∀
            z ∈ p0, z ∈ FootprintVertices T ∩ FootprintVertices (TileTranslation T (↑a :
            GaussianInt))) ∧ ∀ (a_1 : GaussianInt), ∀ (b : GaussianInt), ∀ (l₁ : List
            GaussianInt), ∀ (l₂ : List GaussianInt), p0 = l₁ ++ a_1 :: b :: l₂ → {a_1, b} ∈
            FootprintEdges T ∩ FootprintEdges (TileTranslation T (↑a : GaussianInt))) → ((∀ (v :
            L), ∀ (w : L), TileTranslation (TileTranslation T (v : GaussianInt)) (w :
            GaussianInt) = TileTranslation T ((v + w : L) : GaussianInt)) → ((∀ (w : L), rho
            (D.faces (.inl w)) = rho fU + (w : GaussianInt)) → ((∀ (w : L), rho (D.faces (.inr (w
            + a))) = rho (D.faces (.inr a)) + (w : GaussianInt)) → (∀ (w : ↥L),
            P4733T1ContainedWalk (TileTranslation T (↑w : GaussianInt)) (TileTranslation T (↑(w
            + a) : GaussianInt)) (rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w))) (rho
            ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a)))) (List.map (fun (z :
            GaussianInt) => z + (↑w : GaussianInt)) p0)))))
    ) := by
  classical
  intro L k D T a ru rd rho fU fDa p0 hp0 tileAdd rhoUpShift rhoDown0Shift w
  have hb : P4733T1ContainedWalk T (TileTranslation T (a : GaussianInt))
      (rho fU) (rho fDa) p0 := by
    exact hp0
  have ht := (P4733T1WalkTransport T (TileTranslation T (a : GaussianInt))
    (rho fU) (rho fDa) p0 hb).2 (w : GaussianInt)
  simpa [P4733T1ContainedWalk, tileAdd, rhoUpShift, rhoDown0Shift,
    add_assoc, add_comm, add_left_comm] using ht

private theorem rowWalk1 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (W : ProtoTile), ∀ (v : GaussianInt), ∀ (w : GaussianInt), TileTranslation
            (TileTranslation W v) w = TileTranslation W (v + w)) → (
        let fU := D.faces (.inl (0 : L))
        let fDmb := D.faces (.inr (-b))
        ∀ (p1 : List GaussianInt), (p1.head? = some (rho fU) ∧ p1.getLast? = some (rho fDmb) ∧ (∀
            z ∈ p1, z ∈ FootprintVertices T ∩ FootprintVertices (TileTranslation T (-(↑b :
            GaussianInt)))) ∧ ∀ (a : GaussianInt), ∀ (b_1 : GaussianInt), ∀ (l₁ : List
            GaussianInt), ∀ (l₂ : List GaussianInt), p1 = l₁ ++ a :: b_1 :: l₂ → {a, b_1} ∈
            FootprintEdges T ∩ FootprintEdges (TileTranslation T (-(↑b : GaussianInt)))) → ((∀ (w
            : L), rho (D.faces (.inl w)) = rho fU + (w : GaussianInt)) → ((∀ (w : L), rho
            (D.faces (.inr (w - b))) = rho (D.faces (.inr (-b))) + (w : GaussianInt)) → (∀ (w :
            ↥L), P4733T1ContainedWalk (TileTranslation T (↑w : GaussianInt)) (TileTranslation T
            (↑(w - b) : GaussianInt)) (rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w))) (rho
            ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w - b)))) (List.map (fun (z :
            GaussianInt) => z + (↑w : GaussianInt)) p1)))))
    ) := by
  classical
  intro L k D T b ru rd rho translateComp fU fDmb p1 hp1 rhoUpShift rhoDown1Shift w
  have hb : P4733T1ContainedWalk T (TileTranslation T (-(b : GaussianInt)))
      (rho fU) (rho fDmb) p1 := hp1
  have ht := (P4733T1WalkTransport T (TileTranslation T (-(b : GaussianInt)))
    (rho fU) (rho fDmb) p1 hb).2 (w : GaussianInt)
  rw [rhoDown1Shift]
  simpa [P4733T1ContainedWalk, translateComp, rhoUpShift, rhoDown1Shift,
    AddSubgroup.coe_neg, AddSubgroup.coe_sub, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm] using ht

private theorem rowWalk2 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (W : ProtoTile), ∀ (v : GaussianInt), ∀ (w : GaussianInt), TileTranslation
            (TileTranslation W v) w = TileTranslation W (v + w)) → (
        let fU := D.faces (.inl (0 : L))
        let fDamB := D.faces (.inr (a - b))
        ∀ (p2 : List GaussianInt), (p2.head? = some (rho fU) ∧ p2.getLast? = some (rho fDamB) ∧
            (∀ z ∈ p2, z ∈ FootprintVertices (TileTranslation T (↑a : GaussianInt)) ∩
            FootprintVertices (TileTranslation T (-(↑b : GaussianInt)))) ∧ ∀ (a_1 : GaussianInt),
            ∀ (b_1 : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List GaussianInt), p2 = l₁
            ++ a_1 :: b_1 :: l₂ → {a_1, b_1} ∈ FootprintEdges (TileTranslation T (↑a :
            GaussianInt)) ∩ FootprintEdges (TileTranslation T (-(↑b : GaussianInt)))) → ((∀ (w :
            L), rho (D.faces (.inl w)) = rho fU + (w : GaussianInt)) → ((∀ (w : L), rho (D.faces
            (.inr (w + a - b))) = rho (D.faces (.inr (a - b))) + (w : GaussianInt)) → (∀ (w :
            ↥L), P4733T1ContainedWalk (TileTranslation T (↑(w + a) : GaussianInt))
            (TileTranslation T (↑(w - b) : GaussianInt)) (rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face)
            (Sum.inl w))) (rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a - b))))
            (List.map (fun (z : GaussianInt) => z + (↑w : GaussianInt)) p2)))))
    ) := by
  classical
  intro L k D T a b ru rd rho translateComp fU fDamB p2 hp2 rhoUpShift rhoDown2Shift w
  have hb : P4733T1ContainedWalk (TileTranslation T (a : GaussianInt))
      (TileTranslation T (-(b : GaussianInt))) (rho fU) (rho fDamB) p2 := hp2
  have ht := (P4733T1WalkTransport (TileTranslation T (a : GaussianInt))
    (TileTranslation T (-(b : GaussianInt))) (rho fU) (rho fDamB) p2 hb).2 (w : GaussianInt)
  rw [rhoDown2Shift]
  simpa [P4733T1ContainedWalk, translateComp, rhoUpShift, rhoDown2Shift, fDamB,
    AddSubgroup.coe_neg, AddSubgroup.coe_sub, AddSubgroup.coe_add,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using ht

private theorem row0Inc :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        ∀ (w : ↥L), ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L → D.plane.Face)
            (Sum.inl w)) i = w) ∧ ∃ (i : Fin (3 : ℕ)), D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L →
            D.plane.Face) (Sum.inl w)) i = w + a) ∧ (∃ (i : Fin (3 : ℕ)), D.plane.faceVertex
            ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a))) i = w) ∧ ∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a))) i = w + a
    ) := by
  classical
  intro L k D a w
  constructor <;> constructor
  · exact ⟨0, by simp [D.up_vertices]⟩
  · exact ⟨1, by simp [D.up_vertices, a]⟩
  · exact ⟨1, by simp [D.down_vertices, a, sub_eq_add_neg]⟩
  · exact ⟨0, by simp [D.down_vertices]⟩

private theorem row1Inc :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let b : L := k (0, 1)
        ∀ (w : ↥L), ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L → D.plane.Face)
            (Sum.inl w)) i = w - b) ∧ ∃ (i : Fin (3 : ℕ)), D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L
            → D.plane.Face) (Sum.inl w)) i = w) ∧ (∃ (i : Fin (3 : ℕ)), D.plane.faceVertex
            ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w - b))) i = w - b) ∧ ∃ (i : Fin (3 :
            ℕ)), D.plane.faceVertex ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w - b))) i = w
    ) := by
  classical
  intro L k D b w
  constructor <;> constructor
  · exact ⟨2, by simp [D.up_vertices, b, sub_eq_add_neg]⟩
  · exact ⟨0, by simp [D.up_vertices]⟩
  · exact ⟨0, by simp [D.down_vertices]⟩
  · exact ⟨2, by simp [D.down_vertices, b,
      sub_eq_add_neg, add_comm, add_left_comm]⟩

private theorem row2CanonicalForward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (a ≠ a - b) → ((-b ≠ a - b) → (∀ (w : ↥L), path ((D.faces : ↥L ⊕ ↥L → D.plane.Face)
            (Sum.inl w)) ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a - b))) = List.map
            (fun (z : GaussianInt) => z + (↑w : GaussianInt)) p2))
    ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path aNeAmB negBNeAmB w
  have hn1 : w + a - b ≠ w + a := by
    intro hh
    apply aNeAmB
    have h' : w + (a - b) = w + a := by
      simpa [sub_eq_add_neg, add_assoc] using hh
    exact (add_left_cancel h').symm
  have hn2 : w + a - b ≠ w - b := by
    intro hh
    apply negBNeAmB
    have h' : w + (a - b) = w + (-b) := by
      simpa [sub_eq_add_neg, add_assoc] using hh
    exact (add_left_cancel h').symm
  have ht : w + a - b = w + (a - b) := by abel
  simp only [path, D.faces.symm_apply_apply, ite_eq_right hn1, ite_eq_right hn2,
    ite_eq_left ht, rowPath]
  simp

private theorem row1CanonicalForward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (a ≠ -b) → (∀ (w : ↥L), path ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w)) ((D.faces :
            ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w - b))) = List.map (fun (z : GaussianInt) => z +
            (↑w : GaussianInt)) p1)
    ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path aNeNegB w
  have hn : w - b ≠ w + a := by
    intro hh
    apply aNeNegB
    have h' : w + (-b) = w + a := by simpa [sub_eq_add_neg] using hh
    exact (add_left_cancel h').symm
  simp only [path, D.faces.symm_apply_apply, ite_eq_right hn,
    rowPath]
  simp

private theorem row1CanonicalBackward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (a ≠ -b) → (∀ (w : ↥L), path ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w - b)))
            ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w)) = (List.map (fun (z : GaussianInt)
            => z + (↑w : GaussianInt)) p1).reverse)
    ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path aNeNegB w
  have hn : w - b ≠ w + a := by
    intro hh
    apply aNeNegB
    have h' : w + (-b) = w + a := by simpa [sub_eq_add_neg] using hh
    exact (add_left_cancel h').symm
  simp only [path, D.faces.symm_apply_apply, ite_eq_right hn,
    rowPath]
  simp

private theorem row2CanonicalBackward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (a ≠ a - b) → ((-b ≠ a - b) → (∀ (w : ↥L), path ((D.faces : ↥L ⊕ ↥L → D.plane.Face)
            (Sum.inr (w + a - b))) ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w)) = (List.map
            (fun (z : GaussianInt) => z + (↑w : GaussianInt)) p2).reverse))
    ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path aNeAmB negBNeAmB w
  have hn1 : w + a - b ≠ w + a := by
    intro hh
    apply aNeAmB
    have h' : w + (a - b) = w + a := by
      simpa [sub_eq_add_neg, add_assoc] using hh
    exact (add_left_cancel h').symm
  have hn2 : w + a - b ≠ w - b := by
    intro hh
    apply negBNeAmB
    have h' : w + (a - b) = w + (-b) := by
      simpa [sub_eq_add_neg, add_assoc] using hh
    exact (add_left_cancel h').symm
  have ht : w + a - b = w + (a - b) := by abel
  simp only [path, D.faces.symm_apply_apply, ite_eq_right hn1, ite_eq_right hn2,
    ite_eq_left ht, rowPath]
  simp

private theorem walkClaims :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc : D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P
            : List GaussianInt), P4733T1ContainedWalk A B (rho fc) (rho gc) P → path fc gc = P
            → path gc fc = P.reverse → ∀ (f : D.plane.Face), ∀ (g : D.plane.Face), f = fc ∧ g =
            gc ∨ f = gc ∧ g = fc → (path f g).head? = some (rho f) ∧ (path f g).getLast? = some
            (rho g) ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ (x :
            GaussianInt), ∀ (y : GaussianInt), ∀ (l₁ : List GaussianInt), ∀ (l₂ : List
            GaussianInt), path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈ FootprintEdges A ∩
            FootprintEdges B
    ) := by
  classical
  intro L k D a b ru rd rho p0 p1 p2 rowPath path A B fc gc P hw hforward hbackward f g hpair
  rcases hpair with ⟨hf, hg⟩ | ⟨hf, hg⟩
  · simpa [P4733T1ContainedWalk, hf, hg, hforward] using hw
  · have hr := (P4733T1WalkTransport A B (rho fc) (rho gc) P hw).1
    simpa [P4733T1ContainedWalk, hf, hg, hbackward] using hr

private theorem commonEdgeForAdjacent :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (y = x + a ∨ x = y + a ∨ y = x + b ∨ x =
            y + b ∨ y = x + (a + b) ∨ x = y + (a + b))) → (∀ (e0 : Finset GaussianInt), ∀ (e1 :
            Finset GaussianInt), ∀ (e2 : Finset GaussianInt), (∀ (w : L), e0.image
            (GaussianTranslation (w : GaussianInt)) ∈ FootprintEdges (TileTranslation T (w :
            GaussianInt)) ∩ FootprintEdges (TileTranslation T ((w + a : L) : GaussianInt))) → ((∀
            (w : L), e1.image (GaussianTranslation (w : GaussianInt)) ∈ FootprintEdges
            (TileTranslation T (w : GaussianInt)) ∩ FootprintEdges (TileTranslation T ((w - b :
            L) : GaussianInt))) → ((∀ (w : L), e2.image (GaussianTranslation (w : GaussianInt)) ∈
            FootprintEdges (TileTranslation T ((w + a : L) : GaussianInt)) ∩ FootprintEdges
            (TileTranslation T ((w - b : L) : GaussianInt))) → (∀ (x : ↥L), ∀ (y : ↥L),
            D.plane.adjacent x y → (FootprintEdges (TileTranslation T (↑x : GaussianInt)) ∩
            FootprintEdges (TileTranslation T (↑y : GaussianInt))).Nonempty))))
    ) := by
  classical
  intro L k D T a b edgeDiff e0 e1 e2 rowEdge0 rowEdge1 rowEdge2 x y hxy
  rcases edgeDiff x y hxy with h | h | h | h | h | h
  · refine ⟨e0.image (GaussianTranslation (x : GaussianInt)), ?_⟩
    simpa [h] using rowEdge0 x
  · have he := rowEdge0 y
    rw [Set.inter_comm] at he
    refine ⟨e0.image (GaussianTranslation (y : GaussianInt)), ?_⟩
    simpa [h] using he
  · have he := rowEdge1 y
    rw [Set.inter_comm] at he
    refine ⟨e1.image (GaussianTranslation (y : GaussianInt)), ?_⟩
    simpa [h, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using he
  · refine ⟨e1.image (GaussianTranslation (x : GaussianInt)), ?_⟩
    simpa [h, sub_eq_add_neg, add_assoc] using rowEdge1 x
  · have he := rowEdge2 (x + b)
    rw [Set.inter_comm] at he
    refine ⟨e2.image (GaussianTranslation ((x + b : L) : GaussianInt)), ?_⟩
    have hx : x + b - b = x := by abel
    have hy : x + b + a = y := by rw [h]; abel
    simpa [hx, hy] using he
  · refine ⟨e2.image (GaussianTranslation ((y + b : L) : GaussianInt)), ?_⟩
    have hy : y + b - b = y := by abel
    have hx : y + b + a = x := by rw [h]; abel
    simpa [hy, hx] using rowEdge2 (y + b)

private theorem hcAt922 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        (↥L) → (
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc : D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P
            : List GaussianInt), (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc
            = P) → ((path gc fc = P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f =
            fc ∧ g = gc) ∨ (f = gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f
            g).getLast? = some (rho g) ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩
            FootprintVertices B) ∧ ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁
            ++ x :: y :: l₂ → {x, y} ∈ FootprintEdges A ∩ FootprintEdges B))))) → (∀ (f :
            D.plane.Face), ∀ (g : D.plane.Face),
        let w := x
        let fc := D.faces (.inl w)
        let gc := D.faces (.inr (w - b))
        (f = fc ∧ g = gc ∨ f = gc ∧ g = fc) → ((path fc gc = p1.map (fun z => z + (w :
            GaussianInt))) → ((path gc fc = (p1.map (fun z => z + (w : GaussianInt))).reverse) →
            ((P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation T ((w
            - b : L) : GaussianInt)) (rho fc) (rho gc) (p1.map (fun z => z + (w : GaussianInt))))
            → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g) ∧ (∀ z ∈ path
            f g, z ∈ FootprintVertices (TileTranslation T ↑w) ∩ FootprintVertices
            (TileTranslation T ↑(w - b))) ∧ ∀ x' y' : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
            path f g = l₁ ++ x' :: y' :: l₂ → {x', y'} ∈ FootprintEdges (TileTranslation T ↑w) ∩
            FootprintEdges (TileTranslation T ↑(w - b))))))))) := by
  classical
  intro L k D T a b ru rd x rho p0 p1 p2 rowPath y path walkClaims f g w fc gc hpair hforward
      hbackward hw
  exact walkClaims (TileTranslation T (w : GaussianInt))
    (TileTranslation T ((w - b : L) : GaussianInt)) fc gc
    (p1.map (fun z => z + (w : GaussianInt))) hw hforward hbackward f g hpair

private theorem hdAt961 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (x : ↥L), ∀ (y : ↥L),
        let w := x + b
        let gc := D.faces (.inr (w + a - b))
        (w - b = x) → ((w + a = y) → ((∃ i, D.plane.faceVertex gc i = x) ∧ ∃ i,
            D.plane.faceVertex gc i = y))
    ) := by
  classical
  intro L k D a b x y w gc hwx hwy
  have h1 : w + a - b - a = x := by
    calc
      w + a - b - a = w - b := by abel
      _ = x := hwx
  have h2 : w + a - b + b = y := by
    calc
      w + a - b + b = w + a := sub_add_cancel _ _
      _ = y := hwy
  constructor
  · refine ⟨1, ?_⟩
    change D.plane.faceVertex (D.faces (.inr (w + a - b))) 1 = x
    exact (D.down_vertices (w + a - b)).2.1.trans h1
  · refine ⟨2, ?_⟩
    change D.plane.faceVertex (D.faces (.inr (w + a - b))) 2 = y
    exact (D.down_vertices (w + a - b)).2.2.trans h2

private theorem hdAt1029 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (x : ↥L), ∀ (y : ↥L),
        let w := y + b
        let gc := D.faces (.inr (w + a - b))
        (w - b = y) → ((w + a = x) → ((∃ i, D.plane.faceVertex gc i = y) ∧ ∃ i,
            D.plane.faceVertex gc i = x))
    ) := by
  classical
  intro L k D a b x y w gc hwy hwx
  have h1 : w + a - b - a = y := by
    calc
      w + a - b - a = w - b := by abel
      _ = y := hwy
  have h2 : w + a - b + b = x :=
    (by
      calc
        w + a - b + b = w + a := sub_add_cancel _ _
        _ = x := hwx)
  constructor
  · refine ⟨1, ?_⟩
    change D.plane.faceVertex (D.faces (.inr (w + a - b))) 1 = y
    exact (D.down_vertices (w + a - b)).2.1.trans h1
  · refine ⟨2, ?_⟩
    change D.plane.faceVertex (D.faces (.inr (w + a - b))) 2 = x
    exact (D.down_vertices (w + a - b)).2.2.trans h2

end RegularFaceWalkProof

namespace RegularFaceDetails

private theorem translateBoundary :
    (by
      classical
      exact
        ∀ (W : ProtoTile), ∀ (z : GaussianInt), ∀ (v : GaussianInt), z ∈
            BoundaryFootprintVertices W → z + v ∈ BoundaryFootprintVertices (TileTranslation W v)
            ) := by
  classical
  intro W z v hz
  rw [(TileTranslationFormulas W v).2.2.2.2.2.2.2.1]
  exact ⟨z, hz, by simp [GaussianTranslation]
    ⟩

private theorem k11 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        k (1, 1) = a + b ) := by
  classical
  intro L k a b
  have h : ((1, 1) : Int × Int) = ((1, 0) : Int × Int) + (0, 1) := by
    ext <;> norm_num
  rw [h, map_add]

private theorem kneg11 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        (k (1, 1) = a + b) → (k (-1, -1) = -(a + b)) ) := by
  classical
  intro L k a b k11
  have h : ((-1, -1) : Int × Int) = -((1, 1) : Int × Int) := by
    ext <;> norm_num
  rw [h, map_neg, k11]

private theorem kneg10 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        k (-1, 0) = -a ) := by
  classical
  intro L k a
  have h : ((-1, 0) : Int × Int) = -((1, 0) : Int × Int) := by
    ext <;> norm_num
  rw [h, map_neg]

private theorem kneg01 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let b : L := k (0, 1)
        k (0, -1) = -b ) := by
  classical
  intro L k b
  have h : ((0, -1) : Int × Int) = -((0, 1) : Int × Int) := by
    ext <;> norm_num
  rw [h, map_neg]

private theorem touchSymm :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), TileTouching A B → TileTouching B A ) := by
  classical
  intro A B h
  rcases h with h | h | h
  · rcases h with ⟨hA, hB, hdisj, hp⟩
    exact Or.inl ⟨hB, hA, disjoint_comm.mp hdisj,
      by simpa [Set.inter_comm] using hp⟩
  · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
  · exact Or.inr (Or.inl ⟨h.1, h.2⟩)

private theorem dmb0 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (q : Sum L L), ∀ (i : Fin 3), rho (D.faces q) ∈ FootprintVertices (TileTranslation T
            (D.plane.faceVertex (D.faces q) i : GaussianInt))) → ((∀ (W : ProtoTile),
            TileTranslation W 0 = W) → (
        let fDmb := D.faces (.inr (-b))
        rho fDmb ∈ FootprintVertices T)) ) := by
  classical
  intro L k D T b ru rd rho rho_mem transZero fDmb
  simpa [fDmb, b, D.down_vertices, transZero, add_assoc, add_comm, add_left_comm] using
    rho_mem (.inr (-b)) 2

private theorem damB_mb :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (q : Sum L L), ∀ (i : Fin 3), rho (D.faces q) ∈ FootprintVertices (TileTranslation T
            (D.plane.faceVertex (D.faces q) i : GaussianInt))) → (
        let fDamB := D.faces (.inr (a - b))
        rho fDamB ∈ FootprintVertices (TileTranslation T (-(b : GaussianInt)))) ) := by
  classical
  intro L k D T a b ru rd rho rho_mem fDamB
  have heq : (a - b - a : L) = -b := by abel
  simpa [fDamB, a, b, D.down_vertices, heq] using rho_mem (.inr (a - b)) 1

private theorem shiftEq :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (u : ↥L), ∀ (x : ↥L), ∀ (y : ↥L), ∀ (d : ↥L), u + y =
            u + x + d ↔ y = x + d ) := by
  classical
  intro L u x y d
  rw [add_assoc]
  exact add_left_cancel_iff

private theorem mapTranslate :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (p : List GaussianInt), ∀ (x : ↥L), ∀ (u : ↥L),
            List.map (fun (z : GaussianInt) => z + (↑(u + x) : GaussianInt)) p = List.map (fun (z
            : GaussianInt) => z + (↑u : GaussianInt)) (List.map (fun (z : GaussianInt) => z + (↑x
            : GaussianInt)) p) ) := by
  classical
  intro L p x u
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext z
  simp only [AddSubgroup.coe_add]
  abel

private theorem transNonempty :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (Finset.Nonempty T.cells) → (∀ (v : GaussianInt), Finset.Nonempty
            (TileTranslation T v).cells) ) := by
  classical
  intro T hne v
  rcases hne with ⟨c, hc⟩
  change (T.cells.image (GaussianTranslation v)).Nonempty
  refine ⟨GaussianTranslation v c, ?_⟩
  exact Finset.mem_image.mpr ⟨c, hc, rfl⟩

private theorem footprintEdgeTranslate :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (v : GaussianInt), ∀ e ∈ FootprintEdges V, Finset.image
            (GaussianTranslation v) e ∈ FootprintEdges (TileTranslation V v) ) := by
  classical
  intro V v e he
  rw [(TileTranslationFormulas V v).2.2.2.2.2.2.1]
  exact ⟨e, he, by simp⟩

private theorem tileAdd :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (T : ProtoTile), (∀ (W : ProtoTile), ∀ (v :
            GaussianInt), ∀ (w : GaussianInt), TileTranslation (TileTranslation W v) w =
            TileTranslation W (v + w)) → (∀ (v : ↥L), ∀ (w : ↥L), TileTranslation
            (TileTranslation T (↑v : GaussianInt)) (↑w : GaussianInt) = TileTranslation T (↑(v +
            w) : GaussianInt)) ) := by
  classical
  intro L T translateComp v w
  rw [translateComp]
  simp only [AddSubgroup.coe_add]

private theorem rowEdge0 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        ∀ (e0 : Finset GaussianInt), (e0 ∈ FootprintEdges T ∩ FootprintEdges (TileTranslation T
            (↑a : GaussianInt))) → ((∀ (V : ProtoTile), ∀ (v : GaussianInt), ∀ (e : Finset
            GaussianInt), (e ∈ FootprintEdges V) → (e.image (GaussianTranslation v) ∈
            FootprintEdges (TileTranslation V v))) → ((∀ (v : L), ∀ (w : L), TileTranslation
            (TileTranslation T (v : GaussianInt)) (w : GaussianInt) = TileTranslation T ((v + w :
            L) : GaussianInt)) → (∀ (w : ↥L), Finset.image (GaussianTranslation (↑w :
            GaussianInt)) e0 ∈ FootprintEdges (TileTranslation T (↑w : GaussianInt)) ∩
            FootprintEdges (TileTranslation T (↑(w + a) : GaussianInt))))) ) := by
  classical
  intro L k T a e0 he0 footprintEdgeTranslate tileAdd w
  refine ⟨footprintEdgeTranslate T (w : GaussianInt) e0 he0.1, ?_⟩
  simpa [tileAdd, add_comm] using
    footprintEdgeTranslate (TileTranslation T (a : GaussianInt))
      (w : GaussianInt) e0 he0.2

private theorem rowEdge1 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (T : ProtoTile),
        let b : L := k (0, 1)
        (∀ (W : ProtoTile), ∀ (v : GaussianInt), ∀ (w : GaussianInt), TileTranslation
            (TileTranslation W v) w = TileTranslation W (v + w)) → (∀ (e1 : Finset GaussianInt),
            (e1 ∈ FootprintEdges T ∩ FootprintEdges (TileTranslation T (-(↑b : GaussianInt)))) →
            ((∀ (V : ProtoTile), ∀ (v : GaussianInt), ∀ (e : Finset GaussianInt), (e ∈
            FootprintEdges V) → (e.image (GaussianTranslation v) ∈ FootprintEdges
            (TileTranslation V v))) → (∀ (w : ↥L), Finset.image (GaussianTranslation (↑w :
            GaussianInt)) e1 ∈ FootprintEdges (TileTranslation T (↑w : GaussianInt)) ∩
            FootprintEdges (TileTranslation T (↑(w - b) : GaussianInt))))) ) := by
  classical
  intro L k T b translateComp e1 he1 footprintEdgeTranslate w
  refine ⟨footprintEdgeTranslate T (w : GaussianInt) e1 he1.1, ?_⟩
  simpa [translateComp, AddSubgroup.coe_neg, AddSubgroup.coe_sub,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    footprintEdgeTranslate (TileTranslation T (-(b : GaussianInt)))
      (w : GaussianInt) e1 he1.2

private theorem rhoUpShift :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        let fU := D.faces (.inl (0 : L))
        ∀ (w : ↥L), rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w)) = rho fU + (↑w :
            GaussianInt) ) := by
  classical
  intro L k D ru rd rho fU w
  simp [rho, fU, D.faces.symm_apply_apply]

private theorem rhoDown0Shift :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (w : ↥L), rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a))) = rho ((D.faces :
            ↥L ⊕ ↥L → D.plane.Face) (Sum.inr a)) + (↑w : GaussianInt) ) := by
  classical
  intro L k D a ru rd rho w
  simp [rho, D.faces.symm_apply_apply, AddSubgroup.coe_add, add_comm, add_left_comm]

private theorem rhoDown1Shift :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (w : ↥L), rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w - b))) = rho ((D.faces :
            ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (-b))) + (↑w : GaussianInt) ) := by
  classical
  intro L k D b ru rd rho w
  simp [rho, D.faces.symm_apply_apply,
    sub_eq_add_neg, add_comm, add_left_comm]

private theorem rhoDown2Shift :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (w : ↥L), rho ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a - b))) = rho
            ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (a - b))) + (↑w : GaussianInt) ) := by
  classical
  intro L k D a b ru rd rho w
  simp [rho, D.faces.symm_apply_apply, AddSubgroup.coe_add,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private theorem faceTagsNe :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (x : ↥L), ∀ (y : ↥L), (D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl x) ≠
            (D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr y) ) := by
  classical
  intro L k D x y h
  have hh := D.faces.injective h
  cases hh

private theorem aNeNegB :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        a ≠ -b ) := by
  classical
  intro L k a b h
  have hcoord := congrArg k.symm h
  norm_num [a, b] at hcoord

private theorem aNeAmB :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        a ≠ a - b ) := by
  classical
  intro L k a b h
  have hcoord := congrArg k.symm h
  norm_num [a, b] at hcoord

private theorem negBNeAmB :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        let b : L := k (0, 1);
        -b ≠ a - b ) := by
  classical
  intro L k a b h
  have hcoord := congrArg k.symm h
  norm_num [a, b] at hcoord

private theorem row0CanonicalForward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        ∀ (w : ↥L), path ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inl w)) ((D.faces : ↥L ⊕ ↥L →
            D.plane.Face) (Sum.inr (w + a))) = List.map (fun (z : GaussianInt) => z + (↑w :
            GaussianInt)) p0 ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path w
  simp [path, rowPath, D.faces.symm_apply_apply]

private theorem row0CanonicalBackward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        ∀ (w : ↥L), path ((D.faces : ↥L ⊕ ↥L → D.plane.Face) (Sum.inr (w + a))) ((D.faces : ↥L ⊕
            ↥L → D.plane.Face) (Sum.inl w)) = (List.map (fun (z : GaussianInt) => z + (↑w :
            GaussianInt)) p0).reverse ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path w
  simp [path, rowPath, D.faces.symm_apply_apply]

private theorem transportContainedWalk :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (s :
            GaussianInt), ∀ (t : GaussianInt), ∀ (P : List GaussianInt), A = A' → B = B' →
            P4733T1ContainedWalk A B s t P → P4733T1ContainedWalk A' B' s t P ) := by
  classical
  intro A B A' B' s t P hA hB hw
  rw [← hA, ← hB]
  exact hw

private theorem hs1At1481 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let b : L := k (0, 1)
        (∀ (u : L), ∀ (x : L), ∀ (y : L), ∀ (d : L), (u + y = u + x + d) ↔ y = x + d) → (∀ (u :
            ↥L), ∀ (x : ↥L), ∀ (y : ↥L), (u + y = u + x - b) ↔ y = x - b) ) := by
  classical
  intro L k b shiftEq u x y
  have := shiftEq u x y (-b)
  simpa [sub_eq_add_neg] using this

private theorem hs1At1495 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let b : L := k (0, 1)
        (∀ (u : L), ∀ (x : L), ∀ (y : L), ∀ (d : L), (u + y = u + x + d) ↔ y = x + d) → (∀ (u :
            ↥L), ∀ (x : ↥L), ∀ (y : ↥L), (u + x = u + y - b) ↔ x = y - b) ) := by
  classical
  intro L k b shiftEq u x y
  have := shiftEq u y x (-b)
  simpa [sub_eq_add_neg] using this

private theorem hwAt1515 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (p0 : List GaussianInt), (∀ (w : L), P4733T1ContainedWalk (TileTranslation T (w :
            GaussianInt)) (TileTranslation T ((w + a : L) : GaussianInt)) (rho (D.faces (.inl
            w))) (rho (D.faces (.inr (w + a)))) (p0.map (fun z => z + (w : GaussianInt)))) → (∀
            (y : ↥L), (y = x + a) → (
        let fc := D.faces (.inl x)
        let gc := D.faces (.inr (x + a))
        P4733T1ContainedWalk (TileTranslation T (x : GaussianInt)) (TileTranslation T (y :
            GaussianInt)) (rho fc) (rho gc) (p0.map (fun z => z + (x : GaussianInt))))) ) := by
  classical
  intro L k D T a ru rd x rho p0 rowWalk0 y h fc gc
  simpa [h] using rowWalk0 x

private theorem hcAt1607 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (x : ↥L), ∀ (y : ↥L),
        let w := x + b
        let fc := D.faces (.inl w)
        (w - b = x) → ((w + a = y) → ((∃ i, D.plane.faceVertex fc i = x) ∧ ∃ i,
            D.plane.faceVertex fc i = y)) ) := by
  classical
  intro L k D a b x y w fc hwx hwy
  constructor
  · refine ⟨2, ?_⟩
    change D.plane.faceVertex (D.faces (.inl w)) 2 = x
    exact (D.up_vertices w).2.2.trans hwx
  · refine ⟨1, ?_⟩
    change D.plane.faceVertex (D.faces (.inl w)) 1 = y
    exact (D.up_vertices w).2.1.trans hwy

private theorem hwxAt1656 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (x : ↥L), ∀ (y : ↥L), (x = y + (a + b)) → (
        let w := y + b
        w + a = x) ) := by
  classical
  intro L k a b x y h w
  calc
    w + a = y + b + a := by rfl
    _ = y + (a + b) := by abel
    _ = x := h.symm

private theorem hcAt1662 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (x : ↥L), ∀ (y : ↥L),
        let w := y + b
        let fc := D.faces (.inl w)
        (w - b = y) → ((w + a = x) → ((∃ i, D.plane.faceVertex fc i = y) ∧ ∃ i,
            D.plane.faceVertex fc i = x)) ) := by
  classical
  intro L k D a b x y w fc hwy hwx
  constructor
  · refine ⟨2, ?_⟩
    change D.plane.faceVertex (D.faces (.inl w)) 2 = y
    exact (D.up_vertices w).2.2.trans hwy
  · refine ⟨1, ?_⟩
    change D.plane.faceVertex (D.faces (.inl w)) 1 = x
    exact (D.up_vertices w).2.1.trans hwx

private theorem hwAt1679 :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), (↥L) → (
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        ∀ (p2 : List GaussianInt), (∀ (w : L), P4733T1ContainedWalk (TileTranslation T ((w + a
            : L) : GaussianInt)) (TileTranslation T ((w - b : L) : GaussianInt)) (rho (D.faces
            (.inl w))) (rho (D.faces (.inr (w + a - b)))) (p2.map (fun z => z + (w :
            GaussianInt)))) → (∀ (y : ↥L),
        let w := y + b
        let fc := D.faces (.inl w)
        let gc := D.faces (.inr (w + a - b))
        P4733T1ContainedWalk (TileTranslation T ((w + a : L) : GaussianInt)) (TileTranslation T
            ((w - b : L) : GaussianInt)) (rho fc) (rho gc) (p2.map (fun z => z + (w :
            GaussianInt)))))) := by
  classical
  intro L k D T a b ru rd x rho p2 rowWalk2 y w fc gc
  exact rowWalk2 w

end RegularFaceDetails

namespace RegularFaceProperties

private theorem rhoPeriodic :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        let fs := fun (u : L) (f : D.plane.Face) =>
          D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
        ∀ u, ∀ f, rho (fs u f) = rho f + (u : GaussianInt) ) := by
  classical
  intro L k D ru rd rho fs
  dsimp [fs]
  intro u f
  cases hq : D.faces.symm f with
  | inl x =>
      rw [← D.faces.apply_symm_apply f, hq]
      simp only [D.faces.symm_apply_apply, rho]
      change ru + ((u + x : L) : GaussianInt) =
        (ru + (x : GaussianInt)) + (u : GaussianInt)
      simp only [AddSubgroup.coe_add]
      abel
  | inr x =>
      rw [← D.faces.apply_symm_apply f, hq]
      simp only [D.faces.symm_apply_apply, rho]
      change rd + ((u + x : L) : GaussianInt) =
        (rd + (x : GaussianInt)) + (u : GaussianInt)
      simp only [AddSubgroup.coe_add]
      abel

private theorem pathReverse :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        ∀ f, ∀ g, path g f = (path f g).reverse ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path f g
  cases hf : D.faces.symm f with
  | inl x =>
    cases hg : D.faces.symm g with
    | inl y => simp [path, hf, hg]
    | inr y =>
      simp only [path, hf, hg]
      split_ifs <;> simp
  | inr x =>
    cases hg : D.faces.symm g with
    | inl y =>
      simp only [path, hf, hg]
      split_ifs <;> simp
    | inr y => simp [path, hf, hg]

private theorem pathPeriodic :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (u : L), ∀ (x : L), ∀ (y : L), ∀ (d : L), (u + y = u + x + d) ↔ y = x + d) → ((∀ (p :
            List GaussianInt), ∀ (x : L), ∀ (u : L), p.map (fun z => z + ((u + x : L) :
            GaussianInt)) = (p.map (fun z => z + (x : GaussianInt))).map (fun z => z + (u :
            GaussianInt))) → ((∀ (p : List GaussianInt), ∀ (x : L), ∀ (u : L), ((p.map (fun z =>
            z + ((u + x : L) : GaussianInt))).reverse) = (((p.map (fun z => z + (x :
            GaussianInt))).reverse).map (fun z => z + (u : GaussianInt)))) → ((∀ (u : L), ∀ (P0 :
            Prop), ∀ (P1 : Prop), ∀ (P2 : Prop), ∀ (Q0 : Prop), ∀ (Q1 : Prop), ∀ (Q2 : Prop), (P0
            ↔ Q0) → ((P1 ↔ Q1) → ((P2 ↔ Q2) → (∀ (A0 : List GaussianInt), ∀ (A1 : List
            GaussianInt), ∀ (A2 : List GaussianInt), ∀ (B0 : List GaussianInt), ∀ (B1 : List
            GaussianInt), ∀ (B2 : List GaussianInt), (A0 = B0.map (fun z => z + (u :
            GaussianInt))) → ((A1 = B1.map (fun z => z + (u : GaussianInt))) → ((A2 = B2.map (fun
            z => z + (u : GaussianInt))) → ((if P0 then A0 else if P1 then A1 else if P2 then A2
            else []) = (if Q0 then B0 else if Q1 then B1 else if Q2 then B2 else []).map (fun z
            => z + (u : GaussianInt))))))))) → (
        let fs := fun (u : L) (f : D.plane.Face) =>
          D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
        ∀ u, ∀ f, ∀ g, path (fs u f) (fs u g) = (path f g).map (fun z => z + (u :
            GaussianInt)))))) ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path shiftEq mapTranslate mapTranslateRev ifMap3 fs
  dsimp [fs]
  intro u f g
  cases hf : D.faces.symm f with
  | inl x =>
    cases hg : D.faces.symm g with
    | inl y => simp [path, hf, hg, D.faces.symm_apply_apply]
    | inr y =>
      simp only [path, hf, hg, D.faces.symm_apply_apply,
        Sum.map_inl, Sum.map_inr]
      have hs0 := shiftEq u x y a
      have hs1 : (u + y = u + x - b) ↔ y = x - b := RegularFaceDetails.hs1At1481 L k
          shiftEq u x y
      have hs2 : (u + y = u + x + (a - b)) ↔ y = x + (a - b) :=
        shiftEq u x y (a - b)
      exact ifMap3 u _ _ _ _ _ _ hs0 hs1 hs2 _ _ _ _ _ _
        (mapTranslate (rowPath 0) x u) (mapTranslate (rowPath 1) x u)
        (mapTranslate (rowPath 2) x u)
  | inr x =>
    cases hg : D.faces.symm g with
    | inl y =>
      simp only [path, hf, hg, D.faces.symm_apply_apply,
        Sum.map_inl, Sum.map_inr]
      have hs0 := shiftEq u y x a
      have hs1 : (u + x = u + y - b) ↔ x = y - b := RegularFaceDetails.hs1At1495 L k
          shiftEq u x y
      have hs2 : (u + x = u + y + (a - b)) ↔ x = y + (a - b) :=
        shiftEq u y x (a - b)
      exact ifMap3 u _ _ _ _ _ _ hs0 hs1 hs2 _ _ _ _ _ _
        (mapTranslateRev (rowPath 0) y u) (mapTranslateRev (rowPath 1) y u)
        (mapTranslateRev (rowPath 2) y u)
    | inr y => simp [path, hf, hg, D.faces.symm_apply_apply]

private theorem firstForward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) →
            (((∃ i, D.plane.faceVertex f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i,
            D.plane.faceVertex g i = x) ∧ (∃ i, D.plane.faceVertex g i = y)) → (((∃ i,
            D.plane.faceVertex c i = x) ∧ (∃ i, D.plane.faceVertex c i = y)) → (((∃ i,
            D.plane.faceVertex d i = x) ∧ (∃ i, D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨
            (f = d ∧ g = c))))))))) → (∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀
                (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        ∀ (y : ↥L),
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation
            T ((w + a : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w +
            a)))) (p0.map (fun z => z + (w : GaussianInt)))) → ((∀ (x : L), ∀ (y : L), D.faces
            (.inl x) ≠ D.faces (.inr y)) → ((∀ (w : L), ((∃ i, D.plane.faceVertex (D.faces (.inl
            w)) i = w) ∧ ∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w + a) ∧ ((∃ i,
            D.plane.faceVertex (D.faces (.inr (w + a))) i = w) ∧ ∃ i, D.plane.faceVertex (D.faces
            (.inr (w + a))) i = w + a)) → ((∀ (w : L), path (D.faces (.inl w)) (D.faces (.inr (w
            + a))) = (p0.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), path (D.faces
            (.inr (w + a))) (D.faces (.inl w)) = (p0.map (fun z => z + (w :
            GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((D.plane.adjacent x y) → (∀ (f :
                D.plane.Face), ∀ (g : D.plane.Face), (f ≠ g) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex f i = x) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f i = y) →
            ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → (y = x + a → P4733T1ContainedWalk (TileTranslation T
            (↑x : GaussianInt)) (TileTranslation T (↑y : GaussianInt)) (rho f) (rho g) (path f
            g))))))))))))))) := by
  classical
  intro L k D T a b ru rd x rho uniquePair p0 p1 p2 rowPath y path rowWalk0 faceTagsNe row0Inc
      row0CanonicalForward row0CanonicalBackward walkClaims hxy f g hfg hfa hfb hga hgb h
  let fc := D.faces (.inl x)
  let gc := D.faces (.inr (x + a))
  have hpair := uniquePair x y hxy f g fc gc hfg (faceTagsNe x (x + a))
    ⟨hfa, hfb⟩ ⟨hga, hgb⟩ (by simpa [h] using (row0Inc x).1) (by simpa [h] using
        (row0Inc x).2)
  have hforward : path fc gc = p0.map (fun z => z + (x : GaussianInt)) := by
    simpa [fc, gc] using row0CanonicalForward x
  have hbackward : path gc fc = (p0.map (fun z => z + (x : GaussianInt))).reverse := by
    simpa [fc, gc] using row0CanonicalBackward x
  have hw : P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho fc) (rho gc)
      (p0.map (fun z => z + (x : GaussianInt))) := RegularFaceDetails.hwAt1515 L k D T
          ru rd x p0 rowWalk0 y h
  exact walkClaims _ _ fc gc _ hw hforward hbackward f g hpair

private theorem firstBackward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) →
            (((∃ i, D.plane.faceVertex f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i,
            D.plane.faceVertex g i = x) ∧ (∃ i, D.plane.faceVertex g i = y)) → (((∃ i,
            D.plane.faceVertex c i = x) ∧ (∃ i, D.plane.faceVertex c i = y)) → (((∃ i,
            D.plane.faceVertex d i = x) ∧ (∃ i, D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨
            (f = d ∧ g = c))))))))) → (∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀
                (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        ∀ (y : ↥L),
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation
            T ((w + a : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w +
            a)))) (p0.map (fun z => z + (w : GaussianInt)))) → ((∀ (x : L), ∀ (y : L), D.faces
            (.inl x) ≠ D.faces (.inr y)) → ((∀ (w : L), ((∃ i, D.plane.faceVertex (D.faces (.inl
            w)) i = w) ∧ ∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w + a) ∧ ((∃ i,
            D.plane.faceVertex (D.faces (.inr (w + a))) i = w) ∧ ∃ i, D.plane.faceVertex (D.faces
            (.inr (w + a))) i = w + a)) → ((∀ (w : L), path (D.faces (.inl w)) (D.faces (.inr (w
            + a))) = (p0.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), path (D.faces
            (.inr (w + a))) (D.faces (.inl w)) = (p0.map (fun z => z + (w :
            GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((D.plane.adjacent x y) → (∀ (f :
                D.plane.Face), ∀ (g : D.plane.Face), (f ≠ g) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex f i = x) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f i = y) →
            ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → (x = y + a → P4733T1ContainedWalk (TileTranslation T
            (↑x : GaussianInt)) (TileTranslation T (↑y : GaussianInt)) (rho f) (rho g) (path f
            g))))))))))))))) := by
  classical
  intro L k D T a b ru rd x rho uniquePair p0 p1 p2 rowPath y path rowWalk0 faceTagsNe row0Inc
      row0CanonicalForward row0CanonicalBackward walkClaims hxy f g hfg hfa hfb hga hgb h
  let w := y
  let fc := D.faces (.inl w)
  let gc := D.faces (.inr (w + a))
  have hsym := (D.plane.adjacent_symmetric x y).mp hxy
  have hpair := uniquePair y x hsym f g fc gc hfg (faceTagsNe w (w + a))
    ⟨hfb, hfa⟩ ⟨hgb, hga⟩
    (by simpa [fc, w, h] using (row0Inc w).1)
    (by simpa [gc, w, h] using (row0Inc w).2)
  have hforward : path fc gc = p0.map (fun z => z + (w : GaussianInt)) := by
    simpa [fc, gc] using row0CanonicalForward w
  have hbackward : path gc fc = (p0.map (fun z => z + (w : GaussianInt))).reverse := by
    simpa [fc, gc] using row0CanonicalBackward w
  have hw : P4733T1ContainedWalk (TileTranslation T (w : GaussianInt))
      (TileTranslation T ((w + a : L) : GaussianInt)) (rho fc) (rho gc)
      (p0.map (fun z => z + (w : GaussianInt))) := rowWalk0 w
  have hclaims := walkClaims _ _ fc gc _ hw hforward hbackward f g hpair
  simpa [h, w, Set.inter_comm, P4733T1ContainedWalk] using hclaims

private theorem secondForward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) →
            (((∃ i, D.plane.faceVertex f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i,
            D.plane.faceVertex g i = x) ∧ (∃ i, D.plane.faceVertex g i = y)) → (((∃ i,
            D.plane.faceVertex c i = x) ∧ (∃ i, D.plane.faceVertex c i = y)) → (((∃ i,
            D.plane.faceVertex d i = x) ∧ (∃ i, D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨
            (f = d ∧ g = c))))))))) → (∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀
                (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        ∀ (y : ↥L),
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation
            T ((w - b : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w -
            b)))) (p1.map (fun z => z + (w : GaussianInt)))) → ((∀ (x : L), ∀ (y : L), D.faces
            (.inl x) ≠ D.faces (.inr y)) → ((∀ (w : L), ((∃ i, D.plane.faceVertex (D.faces (.inl
            w)) i = w - b) ∧ ∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w) ∧ ((∃ i,
            D.plane.faceVertex (D.faces (.inr (w - b))) i = w - b) ∧ ∃ i, D.plane.faceVertex
            (D.faces (.inr (w - b))) i = w)) → ((∀ (w : L), path (D.faces (.inl w)) (D.faces
            (.inr (w - b))) = (p1.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), path
            (D.faces (.inr (w - b))) (D.faces (.inl w)) = (p1.map (fun z => z + (w :
            GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((D.plane.adjacent x y) → (∀ (f :
                D.plane.Face), ∀ (g : D.plane.Face), (f ≠ g) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex f i = x) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f i = y) →
            ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → (y = x + b → P4733T1ContainedWalk (TileTranslation T
            (↑x : GaussianInt)) (TileTranslation T (↑y : GaussianInt)) (rho f) (rho g) (path f
            g))))))))))))))) := by
  classical
  intro L k D T a b ru rd x rho uniquePair p0 p1 p2 rowPath y path rowWalk1 faceTagsNe row1Inc
      row1CanonicalForward row1CanonicalBackward walkClaims hxy f g hfg hfa hfb hga hgb h
  let w := y
  let fc := D.faces (.inl w)
  let gc := D.faces (.inr (w - b))
  have hpair := uniquePair x y hxy f g fc gc hfg (faceTagsNe w (w - b))
    ⟨hfa, hfb⟩ ⟨hga, hgb⟩
    (by simpa [h, w, fc, gc, sub_eq_add_neg, add_assoc] using (row1Inc w).1)
    (by simpa [h, w, fc, gc, sub_eq_add_neg, add_assoc] using (row1Inc w).2)
  have hforward : path fc gc = p1.map (fun z => z + (w : GaussianInt)) := by
    simpa [fc, gc] using row1CanonicalForward w
  have hbackward : path gc fc = (p1.map (fun z => z + (w : GaussianInt))).reverse := by
    simpa [fc, gc] using row1CanonicalBackward w
  have hw : P4733T1ContainedWalk (TileTranslation T (w : GaussianInt))
      (TileTranslation T ((w - b : L) : GaussianInt)) (rho fc) (rho gc)
      (p1.map (fun z => z + (w : GaussianInt))) := rowWalk1 w
  have hwx : w - b = x := by dsimp [w]; rw [h]; abel
  have hclaims := walkClaims _ _ fc gc _ hw hforward hbackward f g hpair
  rcases hclaims with ⟨hh, hl, hv, he⟩
  refine ⟨hh, hl, ?_, ?_⟩
  · intro z hz
    rcases hv z hz with ⟨hz1, hz2⟩
    exact ⟨by simpa [hwx, AddSubgroup.coe_sub] using hz2,
      by simpa [w] using hz1⟩
  · intro x' y' l₁ l₂ hp
    rcases he x' y' l₁ l₂ hp with ⟨he1, he2⟩
    exact ⟨by simpa [hwx, AddSubgroup.coe_sub] using he2,
      by simpa [w] using he1⟩

private theorem secondBackward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) →
            (((∃ i, D.plane.faceVertex f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i,
            D.plane.faceVertex g i = x) ∧ (∃ i, D.plane.faceVertex g i = y)) → (((∃ i,
            D.plane.faceVertex c i = x) ∧ (∃ i, D.plane.faceVertex c i = y)) → (((∃ i,
            D.plane.faceVertex d i = x) ∧ (∃ i, D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨
            (f = d ∧ g = c))))))))) → (∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀
                (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        ∀ (y : ↥L),
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation
            T ((w - b : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w -
            b)))) (p1.map (fun z => z + (w : GaussianInt)))) → ((∀ (x : L), ∀ (y : L), D.faces
            (.inl x) ≠ D.faces (.inr y)) → ((∀ (w : L), ((∃ i, D.plane.faceVertex (D.faces (.inl
            w)) i = w - b) ∧ ∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w) ∧ ((∃ i,
            D.plane.faceVertex (D.faces (.inr (w - b))) i = w - b) ∧ ∃ i, D.plane.faceVertex
            (D.faces (.inr (w - b))) i = w)) → ((∀ (w : L), path (D.faces (.inl w)) (D.faces
            (.inr (w - b))) = (p1.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), path
            (D.faces (.inr (w - b))) (D.faces (.inl w)) = (p1.map (fun z => z + (w :
            GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((D.plane.adjacent x y) → (∀ (f :
                D.plane.Face), ∀ (g : D.plane.Face), (f ≠ g) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex f i = x) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f i = y) →
            ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → (x = y + b → P4733T1ContainedWalk (TileTranslation T
            (↑x : GaussianInt)) (TileTranslation T (↑y : GaussianInt)) (rho f) (rho g) (path f
            g))))))))))))))) := by
  classical
  intro L k D T a b ru rd x rho uniquePair p0 p1 p2 rowPath y path rowWalk1 faceTagsNe row1Inc
      row1CanonicalForward row1CanonicalBackward walkClaims hxy f g hfg hfa hfb hga hgb h
  let w := x
  let fc := D.faces (.inl w)
  let gc := D.faces (.inr (w - b))
  have hsym := (D.plane.adjacent_symmetric x y).mp hxy
  have hpair := uniquePair y x hsym f g fc gc hfg (faceTagsNe w (w - b))
    ⟨hfb, hfa⟩ ⟨hgb, hga⟩
    (by simpa [h, w, fc, gc, sub_eq_add_neg, add_assoc] using (row1Inc w).1)
    (by simpa [h, w, fc, gc, sub_eq_add_neg, add_assoc] using (row1Inc w).2)
  have hwy : w - b = y := by dsimp [w]; rw [h]; abel
  have hforward : path fc gc = p1.map (fun z => z + (w : GaussianInt)) :=
    by simpa [fc, gc] using row1CanonicalForward w
  have hbackward : path gc fc = (p1.map (fun z => z + (w : GaussianInt))).reverse :=
    by simpa [fc, gc] using row1CanonicalBackward w
  have hw : P4733T1ContainedWalk (TileTranslation T (w : GaussianInt))
      (TileTranslation T ((w - b : L) : GaussianInt)) (rho fc) (rho gc)
      (p1.map (fun z => z + (w : GaussianInt))) := rowWalk1 w
  have hc : (path f g).head? = some (rho f) ∧
      (path f g).getLast? = some (rho g) ∧
      (∀ z ∈ path f g, z ∈ FootprintVertices (TileTranslation T ↑w) ∩
        FootprintVertices (TileTranslation T ↑(w - b))) ∧
      ∀ x' y' : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
        path f g = l₁ ++ x' :: y' :: l₂ →
          {x', y'} ∈ FootprintEdges (TileTranslation T ↑w) ∩
            FootprintEdges (TileTranslation T ↑(w - b)) := RegularFaceWalkProof.hcAt922
                L k D T ru rd x p0 p1 p2 y walkClaims f g hpair hforward hbackward hw
  rcases hc with ⟨hh, hl, hv, he⟩
  refine ⟨hh, hl, ?_, ?_⟩
  · intro z hz
    rcases hv z hz with ⟨hz1, hz2⟩
    exact ⟨by simpa [w] using hz1,
      by simpa [hwy, AddSubgroup.coe_sub] using hz2⟩
  · intro x' y' l₁ l₂ hp
    rcases he x' y' l₁ l₂ hp with ⟨he1, he2⟩
    exact ⟨by simpa [w] using he1,
      by simpa [hwy, AddSubgroup.coe_sub] using he2⟩

private theorem thirdForward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) →
            (((∃ i, D.plane.faceVertex f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i,
            D.plane.faceVertex g i = x) ∧ (∃ i, D.plane.faceVertex g i = y)) → (((∃ i,
            D.plane.faceVertex c i = x) ∧ (∃ i, D.plane.faceVertex c i = y)) → (((∃ i,
            D.plane.faceVertex d i = x) ∧ (∃ i, D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨
            (f = d ∧ g = c))))))))) → (∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀
                (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        ∀ (y : ↥L),
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T ((w + a : L) : GaussianInt))
            (TileTranslation T ((w - b : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho
            (D.faces (.inr (w + a - b)))) (p2.map (fun z => z + (w : GaussianInt)))) → ((∀ (x :
                L), ∀ (y : L), D.faces (.inl x) ≠ D.faces (.inr y)) → ((∀ (w : L), path (D.faces
            (.inl w)) (D.faces (.inr (w + a - b))) = (p2.map (fun z => z + (w : GaussianInt)))) →
            ((∀ (w : L), path (D.faces (.inr (w + a - b))) (D.faces (.inl w)) = (p2.map (fun z =>
            z + (w : GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((D.plane.adjacent x y) → (∀ (f :
                D.plane.Face), ∀ (g : D.plane.Face), (f ≠ g) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex f i = x) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f i = y) →
            ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → (y = x + (a + b) → P4733T1ContainedWalk
            (TileTranslation T (↑x : GaussianInt)) (TileTranslation T (↑y : GaussianInt)) (rho f)
            (rho g) (path f g)))))))))))))) := by
  classical
  intro L k D T a b ru rd x rho uniquePair p0 p1 p2 rowPath y path rowWalk2 faceTagsNe
      row2CanonicalForward row2CanonicalBackward walkClaims hxy f g hfg hfa hfb hga hgb h
  let w := x + b
  let fc := D.faces (.inl w)
  let gc := D.faces (.inr (w + a - b))
  have hwx : w - b = x := by dsimp [w]; abel
  have hwy : w + a = y := by dsimp [w]; rw [h]; abel
  have hwxG : ((w - b : L) : GaussianInt) = (x : GaussianInt) := by
    simpa only [AddSubgroup.coe_sub] using congrArg (fun z : L => (z : GaussianInt)) hwx
  have hwyG : ((w + a : L) : GaussianInt) = (y : GaussianInt) := by
    exact congrArg (fun z : L => (z : GaussianInt)) hwy
  have hc : (∃ i, D.plane.faceVertex fc i = x) ∧
      ∃ i, D.plane.faceVertex fc i = y := RegularFaceDetails.hcAt1607 L k D x y hwx hwy
  have hd : (∃ i, D.plane.faceVertex gc i = x) ∧
      ∃ i, D.plane.faceVertex gc i = y := RegularFaceWalkProof.hdAt961 L k D x y hwx hwy
  have hpair := uniquePair x y hxy f g fc gc hfg (faceTagsNe w (w + a - b))
    ⟨hfa, hfb⟩ ⟨hga, hgb⟩ hc hd
  have hforward : path fc gc = p2.map (fun z => z + (w : GaussianInt)) :=
    by simpa [fc, gc] using row2CanonicalForward w
  have hbackward : path gc fc = (p2.map (fun z => z + (w : GaussianInt))).reverse :=
    by simpa [fc, gc] using row2CanonicalBackward w
  have hw : P4733T1ContainedWalk
      (TileTranslation T ((w + a : L) : GaussianInt))
      (TileTranslation T ((w - b : L) : GaussianInt)) (rho fc) (rho gc)
      (p2.map (fun z => z + (w : GaussianInt))) := rowWalk2 w
  have hclaims := walkClaims _ _ fc gc _ hw hforward hbackward f g hpair
  rcases hclaims with ⟨hh, hl, hv, he⟩
  refine ⟨hh, hl, ?_, ?_⟩
  · intro z hz
    rcases hv z hz with ⟨hz1, hz2⟩
    have hz2' := hz2
    have hz1' := hz1
    change z ∈ FootprintVertices (TileTranslation T ((w - b : L) : GaussianInt)) at hz2'
    change z ∈ FootprintVertices (TileTranslation T ((w + a : L) : GaussianInt)) at hz1'
    rw [hwxG] at hz2'
    rw [hwyG] at hz1'
    exact ⟨hz2', hz1'⟩
  · intro x' y' l₁ l₂ hp
    rcases he x' y' l₁ l₂ hp with ⟨he1, he2⟩
    have he2' := he2
    have he1' := he1
    change {x', y'} ∈ FootprintEdges (TileTranslation T ((w - b : L) : GaussianInt))
        at he2'
    change {x', y'} ∈ FootprintEdges (TileTranslation T ((w + a : L) : GaussianInt))
        at he1'
    rw [hwxG] at he2'
    rw [hwyG] at he1'
    exact ⟨he2', he1'⟩

private theorem thirdBackward :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt), ∀ (x : ↥L),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g :
            D.plane.Face), ∀ (c : D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) →
            (((∃ i, D.plane.faceVertex f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i,
            D.plane.faceVertex g i = x) ∧ (∃ i, D.plane.faceVertex g i = y)) → (((∃ i,
            D.plane.faceVertex c i = x) ∧ (∃ i, D.plane.faceVertex c i = y)) → (((∃ i,
            D.plane.faceVertex d i = x) ∧ (∃ i, D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨
            (f = d ∧ g = c))))))))) → (∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀
                (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        ∀ (y : ↥L),
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T ((w + a : L) : GaussianInt))
            (TileTranslation T ((w - b : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho
            (D.faces (.inr (w + a - b)))) (p2.map (fun z => z + (w : GaussianInt)))) → ((∀ (x :
                L), ∀ (y : L), D.faces (.inl x) ≠ D.faces (.inr y)) → ((∀ (w : L), path (D.faces
            (.inl w)) (D.faces (.inr (w + a - b))) = (p2.map (fun z => z + (w : GaussianInt)))) →
            ((∀ (w : L), path (D.faces (.inr (w + a - b))) (D.faces (.inl w)) = (p2.map (fun z =>
            z + (w : GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀
                (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (s : GaussianInt), ∀ (t : GaussianInt), ∀
                (P : List GaussianInt), (A = A') → ((B = B') → ((P4733T1ContainedWalk A B s t P) →
            (P4733T1ContainedWalk A' B' s t P)))) → ((D.plane.adjacent x y) → (∀ (f :
                D.plane.Face), ∀ (g : D.plane.Face), (f ≠ g) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex f i = x) → ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex f i = y) →
            ((∃ (i : Fin (3 : ℕ)), D.plane.faceVertex g i = x) → ((∃ (i : Fin (3 : ℕ)),
            D.plane.faceVertex g i = y) → (x = y + (a + b) → P4733T1ContainedWalk
            (TileTranslation T (↑x : GaussianInt)) (TileTranslation T (↑y : GaussianInt)) (rho f)
            (rho g) (path f g))))))))))))))) := by
  classical
  intro L k D T a b ru rd x rho uniquePair p0 p1 p2 rowPath y path rowWalk2 faceTagsNe
      row2CanonicalForward row2CanonicalBackward walkClaims transportContainedWalk hxy f g hfg
      hfa hfb hga hgb h
  let w := y + b
  let fc := D.faces (.inl w)
  let gc := D.faces (.inr (w + a - b))
  have hwy : w - b = y := by
    simpa only [w] using (add_sub_cancel_right y b)
  have hwx : w + a = x := RegularFaceDetails.hwxAt1656 L k x y h
  have hsym := (D.plane.adjacent_symmetric x y).mp hxy
  have hc : (∃ i, D.plane.faceVertex fc i = y) ∧
      ∃ i, D.plane.faceVertex fc i = x := RegularFaceDetails.hcAt1662 L k D x y hwy hwx
  have hd : (∃ i, D.plane.faceVertex gc i = y) ∧
      ∃ i, D.plane.faceVertex gc i = x := RegularFaceWalkProof.hdAt1029 L k D x y hwy hwx
  have hpair := uniquePair y x hsym f g fc gc hfg (faceTagsNe w (w + a - b))
    ⟨hfb, hfa⟩ ⟨hgb, hga⟩ hc hd
  have hforward : path fc gc = p2.map (fun z => z + (w : GaussianInt)) := by
    exact row2CanonicalForward w
  have hbackward : path gc fc = (p2.map (fun z => z + (w : GaussianInt))).reverse := by
    exact row2CanonicalBackward w
  have hw : P4733T1ContainedWalk
      (TileTranslation T ((w + a : L) : GaussianInt))
      (TileTranslation T ((w - b : L) : GaussianInt)) (rho fc) (rho gc)
      (p2.map (fun z => z + (w : GaussianInt))) := RegularFaceDetails.hwAt1679 L k D T
          ru rd x p2 rowWalk2 y
  have hwxG : ((w + a : L) : GaussianInt) = (x : GaussianInt) :=
    congrArg (fun z : L => z.1) hwx
  have hwyG : ((w - b : L) : GaussianInt) = (y : GaussianInt) :=
    congrArg (fun z : L => z.1) hwy
  have hw' := transportContainedWalk _ _ _ _ _ _ _
    (congrArg (TileTranslation T) hwxG)
    (congrArg (TileTranslation T) hwyG) hw
  exact walkClaims _ _ fc gc _ hw' hforward hbackward f g hpair

private theorem pathDiagonal :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (p0 : List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        ∀ f, path f f = [] ) := by
  classical
  intro L k D a b p0 p1 p2 rowPath path f
  cases hf : D.faces.symm f with
  | inl x =>
      rw [← D.faces.apply_symm_apply f, hf]
      simp only [path, D.faces.symm_apply_apply]
  | inr x =>
      rw [← D.faces.apply_symm_apply f, hf]
      simp only [path, D.faces.symm_apply_apply]

end RegularFaceProperties

namespace RegularIncidentWalks

private theorem incidentWalks :
    (by
      classical
      exact
        ∀ (L : AddSubgroup GaussianInt), ∀ (k : (Int × Int) ≃+ L), ∀ (D : P4812T1AffineDrawing
            L k), ∀ (T : ProtoTile),
        let a : L := k (1, 0)
        let b : L := k (0, 1)
        ∀ (ru : GaussianInt), ∀ (rd : GaussianInt),
        let rho : D.plane.Face → GaussianInt := fun f =>
          match D.faces.symm f with
          | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
          | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
        (∀ (x : L), ∀ (y : L), (D.plane.adjacent x y) → (y = x + a ∨ x = y + a ∨ y =
            x + b ∨ x = y + b ∨ y = x + (a + b) ∨ x = y + (a + b))) → ((∀ (x : L), ∀ (y : L),
                (D.plane.adjacent x y) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ∀ (c :
                D.plane.Face), ∀ (d : D.plane.Face), (f ≠ g) → ((c ≠ d) → (((∃ i, D.plane.faceVertex
            f i = x) ∧ (∃ i, D.plane.faceVertex f i = y)) → (((∃ i, D.plane.faceVertex g i = x) ∧
            (∃ i, D.plane.faceVertex g i = y)) → (((∃ i, D.plane.faceVertex c i = x) ∧ (∃ i,
            D.plane.faceVertex c i = y)) → (((∃ i, D.plane.faceVertex d i = x) ∧ (∃ i,
            D.plane.faceVertex d i = y)) → ((f = c ∧ g = d) ∨ (f = d ∧ g = c))))))))) → (∀ (p0 :
                List GaussianInt), ∀ (p1 : List GaussianInt), ∀ (p2 : List GaussianInt),
        let rowPath : Fin 3 → List GaussianInt := fun r =>
          if r = 0 then p0 else if r = 1 then p1 else p2
        let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
          letI : ∀ p : Prop, Decidable p := Classical.propDecidable
          exact match D.faces.symm f, D.faces.symm g with
          | Sum.inl x, Sum.inr y =>
              if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
              else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
              else if y = x + (a - b) then
                (rowPath 2).map (fun z => z + (x : GaussianInt))
              else []
          | Sum.inr y, Sum.inl x =>
              if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
              else if y = x + (a - b) then
                ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
              else []
          | _, _ => []
        (∀ (w : L), P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation
            T ((w + a : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w +
            a)))) (p0.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L),
                P4733T1ContainedWalk (TileTranslation T (w : GaussianInt)) (TileTranslation T
                ((w -
            b : L) : GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w - b))))
            (p1.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), P4733T1ContainedWalk
            (TileTranslation T ((w + a : L) : GaussianInt)) (TileTranslation T ((w - b : L) :
            GaussianInt)) (rho (D.faces (.inl w))) (rho (D.faces (.inr (w + a - b)))) (p2.map
            (fun z => z + (w : GaussianInt)))) → ((∀ (x : L), ∀ (y : L), D.faces (.inl x) ≠
            D.faces (.inr y)) → ((∀ (w : L), ((∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w)
            ∧ ∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w + a) ∧ ((∃ i, D.plane.faceVertex
            (D.faces (.inr (w + a))) i = w) ∧ ∃ i, D.plane.faceVertex (D.faces (.inr (w + a))) i
            = w + a)) → ((∀ (w : L), ((∃ i, D.plane.faceVertex (D.faces (.inl w)) i = w - b) ∧ ∃
            i, D.plane.faceVertex (D.faces (.inl w)) i = w) ∧ ((∃ i, D.plane.faceVertex (D.faces
            (.inr (w - b))) i = w - b) ∧ ∃ i, D.plane.faceVertex (D.faces (.inr (w - b))) i = w))
            → ((∀ (w : L), path (D.faces (.inl w)) (D.faces (.inr (w + a - b))) = (p2.map (fun z
            => z + (w : GaussianInt)))) → ((∀ (w : L), path (D.faces (.inl w)) (D.faces (.inr (w
            - b))) = (p1.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), path (D.faces
            (.inr (w - b))) (D.faces (.inl w)) = (p1.map (fun z => z + (w :
            GaussianInt))).reverse) → ((∀ (w : L), path (D.faces (.inl w)) (D.faces (.inr (w +
            a))) = (p0.map (fun z => z + (w : GaussianInt)))) → ((∀ (w : L), path (D.faces (.inr
            (w + a))) (D.faces (.inl w)) = (p0.map (fun z => z + (w : GaussianInt))).reverse) →
            ((∀ (w : L), path (D.faces (.inr (w + a - b))) (D.faces (.inl w)) = (p2.map (fun z =>
            z + (w : GaussianInt))).reverse) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (fc :
                D.plane.Face), ∀ (gc : D.plane.Face), ∀ (P : List GaussianInt),
                (P4733T1ContainedWalk A B (rho fc) (rho gc) P) → ((path fc gc = P) → ((path gc
                fc =
            P.reverse) → (∀ (f : D.plane.Face), ∀ (g : D.plane.Face), ((f = fc ∧ g = gc) ∨ (f =
            gc ∧ g = fc)) → ((path f g).head? = some (rho f) ∧ (path f g).getLast? = some (rho g)
            ∧ (∀ z ∈ path f g, z ∈ FootprintVertices A ∩ FootprintVertices B) ∧ ∀ x y :
            GaussianInt, ∀ l₁ l₂ : List GaussianInt, path f g = l₁ ++ x :: y :: l₂ → {x, y} ∈
            FootprintEdges A ∩ FootprintEdges B))))) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀
                (A' : ProtoTile), ∀ (B' : ProtoTile), ∀ (s : GaussianInt), ∀ (t : GaussianInt), ∀
                (P : List GaussianInt), (A = A') → ((B = B') → ((P4733T1ContainedWalk A B s t P) →
            (P4733T1ContainedWalk A' B' s t P)))) → (∀ (x : L), ∀ (y : L), D.plane.adjacent x y
            → ∀ (f : D.plane.Face), ∀ (g : D.plane.Face), f ≠ g → (∃ i, D.plane.faceVertex f i =
            x) → (∃ i, D.plane.faceVertex f i = y) → (∃ i, D.plane.faceVertex g i = x) → (∃ i,
            D.plane.faceVertex g i = y) → P4733T1ContainedWalk (TileTranslation T (x :
            GaussianInt)) (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f
            g)))))))))))))))))) := by
  classical
  intro L k D T a b ru rd rho edgeDiff uniquePair p0 p1 p2 rowPath path rowWalk0 rowWalk1
      rowWalk2 faceTagsNe row0Inc row1Inc row2CanonicalForward row1CanonicalForward
      row1CanonicalBackward row0CanonicalForward row0CanonicalBackward row2CanonicalBackward
      walkClaims transportContainedWalk x y hxy f g hfg hfa hfb hga hgb
  have firstForward (h : y = x + a) :
      P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f g) :=
          RegularFaceProperties.firstForward L k D T ru rd x uniquePair p0 p1 p2 y rowWalk0
          faceTagsNe row0Inc row0CanonicalForward row0CanonicalBackward walkClaims hxy f g
          hfg hfa hfb hga hgb h
  have firstBackward (h : x = y + a) :
      P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f g) :=
          RegularFaceProperties.firstBackward L k D T ru rd x uniquePair p0 p1 p2 y
          rowWalk0 faceTagsNe row0Inc row0CanonicalForward row0CanonicalBackward walkClaims
          hxy f g hfg hfa hfb hga hgb h
  have secondForward (h : y = x + b) :
      P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f g) :=
          RegularFaceProperties.secondForward L k D T ru rd x uniquePair p0 p1 p2 y
          rowWalk1 faceTagsNe row1Inc row1CanonicalForward row1CanonicalBackward walkClaims
          hxy f g hfg hfa hfb hga hgb h
  have secondBackward (h : x = y + b) :
      P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f g) :=
          RegularFaceProperties.secondBackward L k D T ru rd x uniquePair p0 p1 p2 y
          rowWalk1 faceTagsNe row1Inc row1CanonicalForward row1CanonicalBackward walkClaims
          hxy f g hfg hfa hfb hga hgb h
  have thirdForward (h : y = x + (a + b)) :
      P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f g) :=
          RegularFaceProperties.thirdForward L k D T ru rd x uniquePair p0 p1 p2 y rowWalk2
          faceTagsNe row2CanonicalForward row2CanonicalBackward walkClaims hxy f g hfg hfa
          hfb hga hgb h
  have thirdBackward (h : x = y + (a + b)) :
      P4733T1ContainedWalk (TileTranslation T (x : GaussianInt))
      (TileTranslation T (y : GaussianInt)) (rho f) (rho g) (path f g) :=
          RegularFaceProperties.thirdBackward L k D T ru rd x uniquePair p0 p1 p2 y
          rowWalk2 faceTagsNe row2CanonicalForward row2CanonicalBackward walkClaims
          transportContainedWalk hxy f g hfg hfa hfb hga hgb h
  rcases edgeDiff x y hxy with h | h | h | h | h | h
  · exact firstForward h
  · exact firstBackward h
  · exact secondForward h
  · exact secondBackward h
  · exact thirdForward h
  · exact thirdBackward h

end RegularIncidentWalks

theorem P4812T1RegularFaceWalks
    (L : AddSubgroup GaussianInt) (k : (Int × Int) ≃+ L)
    (D : P4812T1AffineDrawing L k) (T : ProtoTile)
    (hne : T.cells.Nonempty)
    (hup : TouchingTriple T
      (TileTranslation T (k (1, 0) : GaussianInt))
      (TileTranslation T (-(k (0, 1) : GaussianInt))))
    (hdown : TouchingTriple T
      (TileTranslation T (-(k (1, 0) : GaussianInt)))
      (TileTranslation T (k (0, 1) : GaussianInt))) :
    let fs := fun (u : L) (f : D.plane.Face) =>
      D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
    ∃ rho : D.plane.Face → GaussianInt,
      (∀ f i, rho f ∈ FootprintVertices
        (TileTranslation T (D.plane.faceVertex f i : GaussianInt))) ∧
      (∀ u f, rho (fs u f) = rho f + (u : GaussianInt)) ∧
      ∃ path : D.plane.Face → D.plane.Face → List GaussianInt,
        (∀ f g, path g f = (path f g).reverse) ∧
        (∀ u f g, path (fs u f) (fs u g) =
          (path f g).map (fun z => z + (u : GaussianInt))) ∧
        (∀ a b, D.plane.adjacent a b →
          ∀ f g, f ≠ g →
          (∃ i, D.plane.faceVertex f i = a) →
          (∃ i, D.plane.faceVertex f i = b) →
          (∃ i, D.plane.faceVertex g i = a) →
          (∃ i, D.plane.faceVertex g i = b) →
          (path f g).head? = some (rho f) ∧
          (path f g).getLast? = some (rho g) ∧
          (∀ z ∈ path f g, z ∈
            FootprintVertices (TileTranslation T (a : GaussianInt)) ∩
              FootprintVertices (TileTranslation T (b : GaussianInt))) ∧
          ∀ x y : GaussianInt, ∀ l₁ l₂ : List GaussianInt,
            path f g = l₁ ++ x :: y :: l₂ →
            {x, y} ∈ FootprintEdges (TileTranslation T (a : GaussianInt)) ∩
              FootprintEdges (TileTranslation T (b : GaussianInt))) ∧
        (∀ a b, D.plane.adjacent a b →
          (FootprintEdges (TileTranslation T (a : GaussianInt)) ∩
            FootprintEdges (TileTranslation T (b : GaussianInt))).Nonempty) ∧
        ∀ f, path f f = [] := by
-- BODY
  exact ((by
      classical
      dsimp only
      let a : L := k (1, 0)
      let b : L := k (0, 1)
      obtain ⟨ru, hru⟩ := hup.2.2.2
      obtain ⟨rd, hrd⟩ := hdown.2.2.2
      let rho : D.plane.Face → GaussianInt := fun f =>
        match D.faces.symm f with
        | Sum.inl x => (ru : GaussianInt) + (x : GaussianInt)
        | Sum.inr x => (rd : GaussianInt) + (x : GaussianInt)
      have translateComp (W : ProtoTile) (v w : GaussianInt) :=
          RegularFaceWalkProof.translateComp W v w
      have k11 := RegularFaceDetails.k11 L k
      have edgeDiff (x y : L) (hxy : D.plane.adjacent x y) := RegularFaceWalkProof.edgeDiff L k D
          k11 (RegularFaceDetails.kneg11 L k k11)
                (RegularFaceDetails.kneg10 L k) (RegularFaceDetails.kneg01 L k) x y hxy
      have ru0 : ru ∈ BoundaryFootprintVertices T := hru.1.1
      have rua : ru ∈ BoundaryFootprintVertices (TileTranslation T (a : GaussianInt)) := hru.1.2.1
      have rub : ru ∈ BoundaryFootprintVertices (TileTranslation T (-(b : GaussianInt))) :=
          hru.1.2.2
      have rd0 : rd ∈ BoundaryFootprintVertices T := hrd.1.1
      have rda : rd ∈ BoundaryFootprintVertices (TileTranslation T (-(a : GaussianInt))) :=
          hrd.1.2.1
      have rdb : rd ∈ BoundaryFootprintVertices (TileTranslation T (b : GaussianInt)) := hrd.1.2.2
      have rho_mem (q : Sum L L) (i : Fin 3) :
          rho (D.faces q) ∈ FootprintVertices
            (TileTranslation T (D.plane.faceVertex (D.faces q) i : GaussianInt)) :=
                RegularFaceWalkProof.rho_mem L k D T ru rd (RegularFaceWalkProof.boundaryFoot)
                    (RegularFaceDetails.translateBoundary)
                translateComp ru0 rua rub rd0 rda rdb q i
      have transZero (W : ProtoTile) : TileTranslation W 0 = W := RegularFaceWalkProof.transZero W
      let fU := D.faces (.inl (0 : L))
      let fDa := D.faces (.inr a)
      let fDmb := D.faces (.inr (-b))
      let fDamB := D.faces (.inr (a - b))
      have u00 : rho fU ∈ FootprintVertices T := by
        simpa [fU, D.up_vertices, transZero] using rho_mem (.inl 0) 0
      have u0a : rho fU ∈ FootprintVertices (TileTranslation T (a : GaussianInt)) := by
        simpa [fU, D.up_vertices] using rho_mem (.inl 0) 1
      have da0 : rho fDa ∈ FootprintVertices (TileTranslation T (a : GaussianInt)) := by
        simpa [fDa, D.down_vertices] using rho_mem (.inr a) 0
      have da00 : rho fDa ∈ FootprintVertices T := by
        simpa [fDa, a, D.down_vertices, transZero, sub_self] using rho_mem (.inr a) 1
      have dmb0 : rho fDmb ∈ FootprintVertices T := RegularFaceDetails.dmb0 L k D T ru rd rho_mem
          transZero
      have dmbb : rho fDmb ∈ FootprintVertices (TileTranslation T (-(b : GaussianInt))) := by
        simpa [fDmb, D.down_vertices] using rho_mem (.inr (-b)) 0
      have damB_a : rho fDamB ∈ FootprintVertices (TileTranslation T (a : GaussianInt)) := by
        simpa [fDamB, a, b, D.down_vertices] using rho_mem (.inr (a - b)) 2
      have touch0 : TileTouching T (TileTranslation T (a : GaussianInt)) := hup.1
      have touch1 : TileTouching T (TileTranslation T (-(b : GaussianInt))) :=
        (RegularFaceDetails.touchSymm) _ _ hup.2.2.1
      have touch2 : TileTouching (TileTranslation T (a : GaussianInt))
          (TileTranslation T (-(b : GaussianInt))) := hup.2.1
      obtain ⟨p0, hp0⟩ := P4677T2TouchingWalk T
        (TileTranslation T (a : GaussianInt)) (rho fU) (rho fDa) touch0
        ⟨u00, u0a⟩ ⟨da00, da0⟩
      obtain ⟨p1, hp1⟩ := P4677T2TouchingWalk T
        (TileTranslation T (-(b : GaussianInt))) (rho fU) (rho fDmb) touch1
        ⟨u00, by simpa [fU, b, D.up_vertices, transZero] using (rho_mem (.inl 0) 2)⟩ ⟨dmb0, dmbb⟩
      obtain ⟨p2, hp2⟩ := P4677T2TouchingWalk
        (TileTranslation T (a : GaussianInt)) (TileTranslation T (-(b : GaussianInt)))
        (rho fU) (rho fDamB) touch2 ⟨u0a, by simpa [fU, D.up_vertices, b] using rho_mem (.inl 0) 2⟩
        ⟨damB_a, (RegularFaceDetails.damB_mb L k D T ru rd rho_mem)⟩
      let rowPath : Fin 3 → List GaussianInt := fun r =>
        if r = 0 then p0 else if r = 1 then p1 else p2
      let path : D.plane.Face → D.plane.Face → List GaussianInt := fun f g => by
        letI : ∀ p : Prop, Decidable p := Classical.propDecidable
        exact match D.faces.symm f, D.faces.symm g with
        | Sum.inl x, Sum.inr y =>
            if y = x + a then (rowPath 0).map (fun z => z + (x : GaussianInt))
            else if y = x - b then (rowPath 1).map (fun z => z + (x : GaussianInt))
            else if y = x + (a - b) then
              (rowPath 2).map (fun z => z + (x : GaussianInt))
            else []
        | Sum.inr y, Sum.inl x =>
            if y = x + a then ((rowPath 0).map (fun z => z + (x : GaussianInt))).reverse
            else if y = x - b then ((rowPath 1).map (fun z => z + (x : GaussianInt))).reverse
            else if y = x + (a - b) then
              ((rowPath 2).map (fun z => z + (x : GaussianInt))).reverse
            else []
        | _, _ => []
      have mapTranslate (p : List GaussianInt) (x u : L) := RegularFaceDetails.mapTranslate L p x u
      have commonEdgeTouch (V W : ProtoTile) (hneV : V.cells.Nonempty)
          (hneW : W.cells.Nonempty) (h : TileTouching V W) := RegularFaceWalkProof.commonEdgeTouch
              (RegularFaceWalkProof.boundaryEdgeFoot) V W hneV hneW h
      have transNonempty (v : GaussianInt) := RegularFaceDetails.transNonempty T hne v
      obtain ⟨e0, he0⟩ := commonEdgeTouch T (TileTranslation T (a : GaussianInt)) hne
        (transNonempty (a : GaussianInt)) touch0
      obtain ⟨e1, he1⟩ := commonEdgeTouch T (TileTranslation T (-(b : GaussianInt))) hne
        (transNonempty (-(b : GaussianInt))) touch1
      obtain ⟨e2, he2⟩ := commonEdgeTouch (TileTranslation T (a : GaussianInt))
        (TileTranslation T (-(b : GaussianInt))) (transNonempty (a : GaussianInt))
        (transNonempty (-(b : GaussianInt))) touch2
      have footprintEdgeTranslate (V : ProtoTile) (v : GaussianInt)
          (e : Finset GaussianInt) (he : e ∈ FootprintEdges V) :=
              RegularFaceDetails.footprintEdgeTranslate V v e he
      have tileAdd (v w : L) := RegularFaceDetails.tileAdd L T
                translateComp v w
      have rhoUpShift (w : L) := RegularFaceDetails.rhoUpShift L
              k D ru rd w
      have aNeNegB := RegularFaceDetails.aNeNegB L k
      have aNeAmB := RegularFaceDetails.aNeAmB L k
      have negBNeAmB := RegularFaceDetails.negBNeAmB L k
      let fs := fun (u : L) (f : D.plane.Face) =>
        D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
      refine ⟨rho, ?_, (RegularFaceProperties.rhoPeriodic L k D ru rd), path,
          (RegularFaceProperties.pathReverse L k D p0 p1 p2), (RegularFaceProperties.pathPeriodic
          L k D p0 p1 p2 (RegularFaceDetails.shiftEq L) mapTranslate
          (RegularFaceWalkProof.mapTranslateRev L mapTranslate) (RegularFaceWalkProof.ifMap3 L)),
          (RegularIncidentWalks.incidentWalks L k D T ru rd edgeDiff
          (RegularFaceWalkProof.uniquePair L k D) p0 p1 p2 (RegularFaceWalkProof.rowWalk0 L k D T
          ru rd p0 hp0 tileAdd rhoUpShift (RegularFaceDetails.rhoDown0Shift L k D ru rd))
          (RegularFaceWalkProof.rowWalk1 L k D T ru rd translateComp p1 hp1 rhoUpShift
          (RegularFaceDetails.rhoDown1Shift L k D ru rd)) (RegularFaceWalkProof.rowWalk2 L k D T
          ru rd translateComp p2 hp2 rhoUpShift (RegularFaceDetails.rhoDown2Shift L k D ru rd))
          (RegularFaceDetails.faceTagsNe L k D) (RegularFaceWalkProof.row0Inc L k D)
          (RegularFaceWalkProof.row1Inc L k D) (RegularFaceWalkProof.row2CanonicalForward L k D
          p0 p1 p2 aNeAmB negBNeAmB) (RegularFaceWalkProof.row1CanonicalForward L k D p0 p1 p2
          aNeNegB) (RegularFaceWalkProof.row1CanonicalBackward L k D p0 p1 p2 aNeNegB)
          (RegularFaceDetails.row0CanonicalForward L k D p0 p1 p2)
          (RegularFaceDetails.row0CanonicalBackward L k D p0 p1 p2)
          (RegularFaceWalkProof.row2CanonicalBackward L k D p0 p1 p2 aNeAmB negBNeAmB)
          (RegularFaceWalkProof.walkClaims L k D ru rd p0 p1 p2)
          (RegularFaceDetails.transportContainedWalk)), ?_,
        (RegularFaceProperties.pathDiagonal L k D p0 p1 p2)⟩
      · intro f i
        simpa only [Equiv.apply_symm_apply] using rho_mem (D.faces.symm f) i
      · exact fun x y hxy => (RegularFaceWalkProof.commonEdgeForAdjacent L k D T edgeDiff e0 e1
          e2 (RegularFaceDetails.rowEdge0 L k T e0 he0 footprintEdgeTranslate tileAdd)
          (RegularFaceDetails.rowEdge1 L k T translateComp e1 he1 footprintEdgeTranslate)
          (RegularFaceWalkProof.rowEdge2 L k T translateComp e2 he2 footprintEdgeTranslate
          tileAdd)) x y hxy
  ))

end ApollonianSuperharmonic

end
