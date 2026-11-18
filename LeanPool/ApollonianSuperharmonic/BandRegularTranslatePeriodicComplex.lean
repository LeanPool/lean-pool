/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.BandVectorParentSums
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties

public import LeanPool.ApollonianSuperharmonic.AffineTriangularPlaneTriangulation
public import LeanPool.ApollonianSuperharmonic.AffineTriangularComplexChart
public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.P4812T1LatticeCoordinates
public import LeanPool.ApollonianSuperharmonic.P4812T1AffineTransport
public import LeanPool.ApollonianSuperharmonic.P4812T1ReflectedTouching
public import LeanPool.ApollonianSuperharmonic.P4812T1RegularFaceWalks

-- [TABLET NODE: BandRegularTranslatePeriodicComplex]

/-!
# BandRegularTranslatePeriodicComplex

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RegularPeriodicGeometry

private theorem arcs :
    (by
      classical
      exact
        ∀ (G : PlaneTriangulation (ℤ × ℤ)), (∀ (x : ℤ × ℤ), G.position x = ((↑x.1 : ℝ) - (↑x.2 :
            ℝ) / (2 : ℝ), (↑x.2 : ℝ))) → ((∀ (x : ℤ × ℤ), ∀ (y : ℤ × ℤ), G.edgeArc x y = segment
            ℝ (G.position x) (G.position y)) → (
        let phi (x : Int × Int) : Real × Real :=
          (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real))
        (∀ (x : Int × Int), ∀ (y : Int × Int), phi (x + y) = phi x + phi y) → (∀ (z : Int × Int),
            ∀ (x : Int × Int), ∀ (y : Int × Int), G.edgeArc (z + x) (z + y) = (fun p => p + phi
            z) '' G.edgeArc x y))) ) := by
  classical
  intro G hpos harc phi phi_add z x y
  simp only [harc, hpos]
  change segment Real (phi (z + x)) (phi (z + y)) =
    (fun p => p + phi z) '' segment Real (phi x) (phi y)
  rw [phi_add, phi_add]
  simpa only [add_comm] using (segment_translate_image Real (phi z) (phi x) (phi y)).symm

private theorem regions :
    (by
      classical
      exact
        ∀ (G : PlaneTriangulation (ℤ × ℤ)), ∀ (up : ℤ × ℤ → G.Face), ∀ (down : ℤ × ℤ → G.Face),
            (∀ (x : ℤ × ℤ), G.faceRegion (up x) = (fun (p : ℝ × ℝ) => ((↑x.1 : ℝ) + p.1 - ((↑x.2
            : ℝ) - p.2) / (2 : ℝ), (↑x.2 : ℝ) - p.2)) '' {p : ℝ × ℝ | (0 : ℝ) < p.1 ∧ (0 : ℝ) <
            p.2 ∧ p.1 + p.2 < (1 : ℝ)}) → ((∀ (x : ℤ × ℤ), G.faceRegion (down x) = (fun (p : ℝ ×
            ℝ) => ((↑x.1 : ℝ) - p.1 - ((↑x.2 : ℝ) + p.2) / (2 : ℝ), (↑x.2 : ℝ) + p.2)) '' {p : ℝ
            × ℝ | (0 : ℝ) < p.1 ∧ (0 : ℝ) < p.2 ∧ p.1 + p.2 < (1 : ℝ)}) → (
        let phi (x : Int × Int) : Real × Real :=
          (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real))
        ∀ (z : Int × Int), ∀ (x : Int × Int), G.faceRegion (up (z + x)) = (fun p => p + phi z) ''
            G.faceRegion (up x) ∧ G.faceRegion (down (z + x)) = (fun p => p + phi z) ''
            G.faceRegion (down x))) ) := by
  classical
  intro G up down hru hrd phi z x
  constructor
  · rw [hru, hru, Set.image_image]
    congr 1
    funext p
    ext <;> simp [phi] <;> ring
  · rw [hrd, hrd, Set.image_image]
    congr 1
    funext p
    ext <;> simp [phi] <;> ring

private theorem H_add :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (H : ℝ × ℝ ≃ₜ ℝ × ℝ), (∀ (p : ℝ × ℝ), (H : ℝ × ℝ → ℝ
            × ℝ) p = (p.1 + p.2 / (2 : ℝ)) • GaussianRealPoint (BandVectors.1 (q (1 : Fin (4 :
            ℕ))) (q (0 : Fin (4 : ℕ)))) + p.2 • GaussianRealPoint (BandVectors.1 (q (2 : Fin (4 :
            ℕ))) (q (0 : Fin (4 : ℕ))))) → (∀ (p : Real × Real), ∀ (r : Real × Real), H (p + r) =
            H p + H r) ) := by
  classical
  intro q H hH p r
  simp only [hH]
  ext <;> simp [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

private theorem H_coord :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice
            C)), (∀ (x : ℤ × ℤ), (↑((k : ℤ × ℤ → ↥(TilingLattice C)) x) : GaussianInt) = (↑x.1 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑x.2 :
            GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) → (∀ (H : ℝ
            × ℝ ≃ₜ ℝ × ℝ), (∀ (p : ℝ × ℝ), (H : ℝ × ℝ → ℝ × ℝ) p = (p.1 + p.2 / (2 : ℝ)) •
            GaussianRealPoint (BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) + p.2 •
            GaussianRealPoint (BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))))) → (
        let phi (x : Int × Int) : Real × Real :=
          (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real))
        ∀ (x : Int × Int), H (phi x) = GaussianRealPoint (k x : GaussianInt))) ) := by
  classical
  intro C q k hk H hH phi x
  rw [hH, hk]
  ext <;> simp [phi, GaussianRealPoint,
    smul_eq_mul]

private theorem hc1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (ProperBandQuadruple q) → (((0 : ℤ) < (q (0 : Fin (4 :
            ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 : ℕ)), ∀ (j :
            Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) → (1 < (q
            0).1)) ) := by
  classical
  intro q hq hc
  by_contra hn
  have hz (i : Fin 3) : (q i.succ).1 = 0 := by
    have := hq.2 i
    have := hc.2.1 i
    omega
  have he := hc.2.2 0 1 (hz 0) (hz 1)
  norm_num at he

private theorem fs_zero :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice C)), ∀ (D : P4812T1AffineDrawing
            (TilingLattice C) k),
        let fs (u : TilingLattice C) (f : D.plane.Face) :=
          D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
        ∀ (f : D.plane.Face), fs 0 f = f ) := by
  classical
  intro C k D fs f
  obtain ⟨f, rfl⟩ := D.faces.surjective f
  cases f <;> simp [fs]

private theorem fs_add :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice C)), ∀ (D : P4812T1AffineDrawing
            (TilingLattice C) k),
        let fs (u : TilingLattice C) (f : D.plane.Face) :=
          D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
        ∀ (u : TilingLattice C), ∀ (v : TilingLattice C), ∀ (f : D.plane.Face), fs (u + v) f = fs
            u (fs v f) ) := by
  classical
  intro C k D fs u v f
  obtain ⟨f, rfl⟩ := D.faces.surjective f
  cases f <;> simp [fs, add_assoc]

private theorem fv_per :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice C)), ∀ (D : P4812T1AffineDrawing
            (TilingLattice C) k),
        let fs (u : TilingLattice C) (f : D.plane.Face) :=
          D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
        (∀ (u : TilingLattice C), ∀ (f : Sum (TilingLattice C) (TilingLattice C)), fs u (D.faces
            f) = D.faces (Sum.map (u + ·) (u + ·) f)) → (∀ (u : TilingLattice C), ∀ (f :
            D.plane.Face), ∀ (i : Fin 3), D.plane.faceVertex (fs u f) i = u + D.plane.faceVertex
            f i) ) := by
  classical
  intro C k D fs fs_faces u f i
  obtain ⟨f, rfl⟩ := D.faces.surjective f
  cases f with
  | inl x =>
    rw [fs_faces]
    fin_cases i
    · change D.plane.faceVertex (D.faces (.inl (u + x))) (0 : Fin 3) =
        u + D.plane.faceVertex (D.faces (.inl x)) (0 : Fin 3)
      rw [(D.up_vertices (u + x)).1, (D.up_vertices x).1]
    · change D.plane.faceVertex (D.faces (.inl (u + x))) (1 : Fin 3) =
        u + D.plane.faceVertex (D.faces (.inl x)) (1 : Fin 3)
      rw [(D.up_vertices (u + x)).2.1, (D.up_vertices x).2.1]
      abel
    · change D.plane.faceVertex (D.faces (.inl (u + x))) (2 : Fin 3) =
        u + D.plane.faceVertex (D.faces (.inl x)) (2 : Fin 3)
      rw [(D.up_vertices (u + x)).2.2, (D.up_vertices x).2.2]
      abel
  | inr x =>
    rw [fs_faces]
    fin_cases i
    · change D.plane.faceVertex (D.faces (.inr (u + x))) (0 : Fin 3) =
        u + D.plane.faceVertex (D.faces (.inr x)) (0 : Fin 3)
      rw [(D.down_vertices (u + x)).1, (D.down_vertices x).1]
    · change D.plane.faceVertex (D.faces (.inr (u + x))) (1 : Fin 3) =
        u + D.plane.faceVertex (D.faces (.inr x)) (1 : Fin 3)
      rw [(D.down_vertices (u + x)).2.1, (D.down_vertices x).2.1]
      abel
    · change D.plane.faceVertex (D.faces (.inr (u + x))) (2 : Fin 3) =
        u + D.plane.faceVertex (D.faces (.inr x)) (2 : Fin 3)
      rw [(D.down_vertices (u + x)).2.2, (D.down_vertices x).2.2]
      abel

private theorem delta_inj :
    (by
      classical
      exact
        let delta : Fin 6 → Int × Int := ![(1, 0), (0, 1), (-1, -1),
          (-1, 0), (0, -1), (1, 1)]
        Function.Injective delta ) := by
  classical
  intro delta
  as_aux_lemma =>
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | simp [delta] at h

private theorem coord_adj (C : BandCircle)
    (k : ℤ × ℤ ≃+ ↥(TilingLattice C)) (D : P4812T1AffineDrawing (TilingLattice C) k) :
    let delta : Fin 6 → ℤ × ℤ := ![(1, 0), (0, 1), (-1, -1), (-1, 0), (0, -1), (1, 1)]
    ∀ x y : TilingLattice C, D.plane.adjacent x y ↔ ∃ i : Fin 6,
      k.symm y - k.symm x = delta i := by
  classical
  intro delta x y
  rw [D.adjacent_iff]
  constructor
  · intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [TriangularLatticeAdjacent, delta] at hi ⊢ <;> tauto

private theorem graph_per :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice C)), ∀ (D : P4812T1AffineDrawing
            (TilingLattice C) k),
        let delta : Fin 6 → Int × Int := ![(1, 0), (0, 1), (-1, -1),
          (-1, 0), (0, -1), (1, 1)]
        (∀ (x : TilingLattice C), ∀ (y : TilingLattice C), D.plane.adjacent x y ↔ ∃ i : Fin 6,
            k.symm y - k.symm x = delta i) → (∀ (u : TilingLattice C), ∀ (x : TilingLattice C), ∀
            (y : TilingLattice C), D.plane.adjacent (u + x) (u + y) ↔ D.plane.adjacent x y) ) := by
  classical
  intro C k D delta coord_adj u x y
  have he : k.symm u + k.symm y - (k.symm u + k.symm x) =
      k.symm y - k.symm x := by abel
  simp only [coord_adj, map_add, he]

private theorem edge_reps :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice C)), ∀ (D : P4812T1AffineDrawing
            (TilingLattice C) k),
        let delta : Fin 6 → Int × Int := ![(1, 0), (0, 1), (-1, -1),
          (-1, 0), (0, -1), (1, 1)]
        ∀ (delta_inj : Function.Injective delta),
        let edgeEmbed : Fin 6 ↪ (TilingLattice C × TilingLattice C) :=
          ⟨fun i => (0, k (delta i)), fun i j h => delta_inj (k.injective (congrArg Prod.snd h))⟩
        let edges := Finset.univ.map edgeEmbed
        (∀ (x : TilingLattice C), ∀ (y : TilingLattice C), D.plane.adjacent x y ↔ ∃ i : Fin 6,
            k.symm y - k.symm x = delta i) → (∀ (x : TilingLattice C), ∀ (y : TilingLattice C),
            (D.plane.adjacent x y) → (∃ r ∈ edges, ∃ u : TilingLattice C, x = u + r.1 ∧ y = u +
            r.2)) ) := by
  classical
  intro C k D delta delta_inj edgeEmbed edges coord_adj x y hxy
  obtain ⟨i, hi⟩ := (coord_adj x y).mp hxy
  refine ⟨edgeEmbed i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩, x, ?_, ?_⟩
  · change x = x + 0
    exact (add_zero x).symm
  · change y = x + k (delta i)
    rw [← hi, map_sub, k.apply_symm_apply, k.apply_symm_apply]
    abel

private abbrev incoming_sum := ApollonianSuperharmonic.BandVectorIncomingSum

private theorem kc :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice
            C)), (∀ (x : ℤ × ℤ), (↑((k : ℤ × ℤ → ↥(TilingLattice C)) x) : GaussianInt) = (↑x.1 :
            GaussianInt) * BandVectors.1 (q (1 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ))) + (↑x.2 :
            GaussianInt) * BandVectors.1 (q (2 : Fin (4 : ℕ))) (q (0 : Fin (4 : ℕ)))) →
            ((BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) + BandVectors.1 (q 3) (q 0) =
            0) → ((k (-1, -1) : GaussianInt) = BandVectors.1 (q 3) (q 0))) ) := by
  classical
  intro C q k hk incoming_sum
  rw [hk]
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
  calc
    _ = BandVectors.1 (q 3) (q 0) -
      (BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
        BandVectors.1 (q 3) (q 0)) := by ring
    _ = _ := by rw [incoming_sum]; simp

private theorem signed :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (q : Fin 4 → CircleCoordinates), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice
            C)), ∀ (D : P4812T1AffineDrawing (TilingLattice C) k), ((k (1, 0) : GaussianInt) =
            BandVectors.1 (q 1) (q 0)) → (((k (0, 1) : GaussianInt) = BandVectors.1 (q 2) (q 0)) → (
        let delta : Fin 6 → Int × Int := ![(1, 0), (0, 1), (-1, -1),
          (-1, 0), (0, -1), (1, 1)]
        (∀ (x : TilingLattice C), ∀ (y : TilingLattice C), D.plane.adjacent x y ↔ ∃ i : Fin 6,
            k.symm y - k.symm x = delta i) → (((k (-1, -1) : GaussianInt) = BandVectors.1 (q 3)
            (q 0)) → ((Function.Injective (fun x => (k x : GaussianInt))) → (∀ (x : TilingLattice
            C), ∀ (y : TilingLattice C), D.plane.adjacent x y ↔ ∃ j : Fin 3, (y : GaussianInt) -
            (x : GaussianInt) = BandVectors.1 (q j.succ) (q 0) ∨ (y : GaussianInt) - (x :
            GaussianInt) = -BandVectors.1 (q j.succ) (q 0)))))) ) := by
  classical
  intro C q k D ka kb delta coord_adj kc kinj x y
  have diff : (k (k.symm y - k.symm x) : GaussianInt) =
      (y : GaussianInt) - (x : GaussianInt) := by simp
  have step (i : Fin 6) : ∃ j : Fin 3,
      (k (delta i) : GaussianInt) = BandVectors.1 (q j.succ) (q 0) ∨
      (k (delta i) : GaussianInt) = -BandVectors.1 (q j.succ) (q 0) := by
    fin_cases i
    · exact ⟨0, Or.inl ka⟩
    · exact ⟨1, Or.inl kb⟩
    · exact ⟨2, Or.inl kc⟩
    · refine ⟨0, Or.inr ?_⟩
      change (k (-((1, 0) : Int × Int)) : GaussianInt) = -BandVectors.1 (q 1) (q 0)
      rw [map_neg, AddSubgroup.coe_neg, ka]
    · refine ⟨1, Or.inr ?_⟩
      change (k (-((0, 1) : Int × Int)) : GaussianInt) = -BandVectors.1 (q 2) (q 0)
      rw [map_neg, AddSubgroup.coe_neg, kb]
    · refine ⟨2, Or.inr ?_⟩
      change (k (-((-1, -1) : Int × Int)) : GaussianInt) = -BandVectors.1 (q 3) (q 0)
      rw [map_neg, AddSubgroup.coe_neg, kc]
  rw [coord_adj]
  constructor
  · rintro ⟨i, hi⟩
    rw [← diff, hi]
    exact step i
  · rintro ⟨j, hj | hj⟩
    · fin_cases j
      · exact ⟨0, kinj (diff.trans (hj.trans ka.symm))⟩
      · exact ⟨1, kinj (diff.trans (hj.trans kb.symm))⟩
      · exact ⟨2, kinj (diff.trans (hj.trans kc.symm))⟩
    · fin_cases j
      · refine ⟨3, kinj (diff.trans (hj.trans ?_))⟩
        change -BandVectors.1 (q 1) (q 0) = (k (-((1, 0) : Int × Int)) : GaussianInt)
        rw [map_neg, AddSubgroup.coe_neg, ka]
      · refine ⟨4, kinj (diff.trans (hj.trans ?_))⟩
        change -BandVectors.1 (q 2) (q 0) = (k (-((0, 1) : Int × Int)) : GaussianInt)
        rw [map_neg, AddSubgroup.coe_neg, kb]
      · refine ⟨5, kinj (diff.trans (hj.trans ?_))⟩
        change -BandVectors.1 (q 3) (q 0) = (k (-((-1, -1) : Int × Int)) : GaussianInt)
        rw [map_neg, AddSubgroup.coe_neg, kc]

private theorem facescard :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (k : ℤ × ℤ ≃+ ↥(TilingLattice C)), ∀ (D : P4812T1AffineDrawing
            (TilingLattice C) k),
        let faces : Finset D.plane.Face := {D.faces (.inl 0), D.faces (.inr 0)}
        faces.card = 2 ) := by
  classical
  intro C k D faces
  have hn : D.faces (.inl 0) ≠ D.faces (.inr 0) :=
    fun h => Sum.inl_ne_inr (D.faces.injective h)
  simp [faces, hn]

private abbrev translate_add :=
  TileTranslationProperties.add

private abbrev hzero := ApollonianSuperharmonic.TileTranslationProperties.zero

end RegularPeriodicGeometry

theorem BandRegularTranslatePeriodicComplex (C : BandCircle)
    (q : Fin 4 → CircleCoordinates) (hq : ProperBandQuadruple q)
    (hqC : q 0 = C.1.1) (T : ProtoTile) (hT : BandPrototile (q 0) T) :
    ∃ P : PeriodicTileComplex (TilingLattice C),
      P.lattice = TilingLattice C ∧
      (∀ u, P.tile u = TileTranslation T (u : GaussianInt)) ∧
      (∀ u v, P.plane.adjacent u v ↔
        ∃ j : Fin 3,
          (v : GaussianInt) - (u : GaussianInt) =
              BandVectors.1 (q j.succ) (q 0) ∨
            (v : GaussianInt) - (u : GaussianInt) =
              -BandVectors.1 (q j.succ) (q 0)) ∧
      (∀ u, P.plane.position u = GaussianRealPoint (u : GaussianInt)) ∧
      P.vertexOrbitReps.card = 1 ∧
      P.edgeOrbitReps.card = 6 ∧
      P.faceOrbitReps.card = 2 ∧
      Nonempty (AffineTriangularComplexChart P (fun mn : Int × Int =>
        TileTranslation T
          ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
            (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)))) := by
-- BODY
  classical
  obtain ⟨k, hk, H, hH⟩ := P4812T1LatticeCoordinates C q hq hqC
  obtain ⟨G, up, down, hadj, hu, hd, hud, hall, hup, hdown, hpos,
    harc, hru, hrd⟩ := AffineTriangularPlaneTriangulation
  let phi (x : Int × Int) : Real × Real :=
    (((x.1 : Real) - (x.2 : Real) / 2), (x.2 : Real))
  have phi_add (x y : Int × Int) : phi (x + y) = phi x + phi y := by
    ext <;> simp [phi]; ring
  have arcs (z x y : Int × Int) : G.edgeArc (z + x) (z + y) =
      (fun p => p + phi z) '' G.edgeArc x y := RegularPeriodicGeometry.arcs G hpos harc phi_add z
          x y
  have regions (z x : Int × Int) :
      G.faceRegion (up (z + x)) = (fun p => p + phi z) '' G.faceRegion (up x) ∧
      G.faceRegion (down (z + x)) = (fun p => p + phi z) '' G.faceRegion (down x) :=
          RegularPeriodicGeometry.regions G up down hru hrd z x
  have H_add (p r : Real × Real) : H (p + r) = H p + H r := RegularPeriodicGeometry.H_add q H hH p r
  have H_coord (x : Int × Int) : H (phi x) = GaussianRealPoint (k x : GaussianInt) :=
      RegularPeriodicGeometry.H_coord C q k hk H hH x
  obtain ⟨D⟩ := P4812T1AffineTransport (TilingLattice C) k G up down
    hadj hu hd hud hall hup hdown hpos arcs regions H H_add H_coord
  have hc := ProperBandCurvatureStructure q hq
  have hc1 : 1 < (q 0).1 := RegularPeriodicGeometry.hc1 q hq hc
  have hgeom := BandTileSimultaneousInduction q hq T hT
  have hne : T.cells.Nonempty := by
    apply Finset.card_pos.mp
    have harea : T.cells.card = Int.toNat (q 0).1 := hgeom.2.1
    omega
  have ka : (k (1, 0) : GaussianInt) = BandVectors.1 (q 1) (q 0) := by
    simp [hk]
  have kb : (k (0, 1) : GaussianInt) = BandVectors.1 (q 2) (q 0) := by
    simp [hk]
  have htu : TouchingTriple T
      (TileTranslation T (k (1, 0) : GaussianInt))
      (TileTranslation T (-(k (0, 1) : GaussianInt))) := by
    simpa [ka, kb] using hgeom.2.2.2.2.1 hc1 0
  have htd := P4812T1ReflectedTouching T (k (1, 0)) (k (0, 1)) hne
    hgeom.2.2.2.1 htu
  let fs (u : TilingLattice C) (f : D.plane.Face) :=
    D.faces (Sum.map (u + ·) (u + ·) (D.faces.symm f))
  obtain ⟨rho, hrho, hrhoper, path, hrev, hpathper, hpath, hedge, _⟩ :=
    P4812T1RegularFaceWalks (TilingLattice C) k D T hne htu htd
  have fs_faces (u : TilingLattice C) (f : Sum (TilingLattice C) (TilingLattice C)) :
      fs u (D.faces f) = D.faces (Sum.map (u + ·) (u + ·) f) := by simp [fs]
  have fs_zero (f : D.plane.Face) : fs 0 f = f := RegularPeriodicGeometry.fs_zero C k D f
  have fs_add (u v : TilingLattice C) (f : D.plane.Face) :
      fs (u + v) f = fs u (fs v f) := RegularPeriodicGeometry.fs_add C k D u v f
  have fv_per (u : TilingLattice C) (f : D.plane.Face) (i : Fin 3) :
      D.plane.faceVertex (fs u f) i = u + D.plane.faceVertex f i :=
          RegularPeriodicGeometry.fv_per C k D fs_faces u f i
  let delta : Fin 6 → Int × Int := ![(1, 0), (0, 1), (-1, -1),
    (-1, 0), (0, -1), (1, 1)]
  have delta_inj : Function.Injective delta := RegularPeriodicGeometry.delta_inj
  let edgeEmbed : Fin 6 ↪ (TilingLattice C × TilingLattice C) :=
    ⟨fun i => (0, k (delta i)), fun i j h => delta_inj (k.injective (congrArg Prod.snd h))⟩
  let edges := Finset.univ.map edgeEmbed
  have edgecard : edges.card = 6 := by simp [edges]
  have coord_adj (x y : TilingLattice C) : D.plane.adjacent x y ↔
      ∃ i : Fin 6, k.symm y - k.symm x = delta i := RegularPeriodicGeometry.coord_adj C k D x y
  have graph_per (u x y : TilingLattice C) :
      D.plane.adjacent (u + x) (u + y) ↔ D.plane.adjacent x y :=
          RegularPeriodicGeometry.graph_per C k D coord_adj u x y
  have edge_reps (x y : TilingLattice C) (hxy : D.plane.adjacent x y) :
      ∃ r ∈ edges, ∃ u : TilingLattice C, x = u + r.1 ∧ y = u + r.2 :=
          RegularPeriodicGeometry.edge_reps C k D delta_inj coord_adj x y hxy
  have incoming_sum : BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0) +
      BandVectors.1 (q 3) (q 0) = 0 := RegularPeriodicGeometry.incoming_sum q hq
  have kc : (k (-1, -1) : GaussianInt) = BandVectors.1 (q 3) (q 0) := RegularPeriodicGeometry.kc
      C q k hk incoming_sum
  have kinj : Function.Injective (fun x => (k x : GaussianInt)) :=
    fun _ _ h => k.injective (Subtype.ext h)
  have signed (x y : TilingLattice C) : D.plane.adjacent x y ↔
      ∃ j : Fin 3, (y : GaussianInt) - (x : GaussianInt) =
        BandVectors.1 (q j.succ) (q 0) ∨
        (y : GaussianInt) - (x : GaussianInt) = -BandVectors.1 (q j.succ) (q 0) :=
            RegularPeriodicGeometry.signed C q k D ka kb coord_adj kc kinj x y
  obtain ⟨R, hR, hRcard⟩ := TilingLatticeIndex C
  let faces : Finset D.plane.Face := {D.faces (.inl 0), D.faces (.inr 0)}
  have facescard : faces.card = 2 := RegularPeriodicGeometry.facescard C k D
  have translate_add (U : ProtoTile) (x y : GaussianInt) :
      TileTranslation (TileTranslation U x) y = TileTranslation U (x + y) :=
          RegularPeriodicGeometry.translate_add U x y
  let P : PeriodicTileComplex (TilingLattice C) := {
    plane := D.plane
    tile := fun x => TileTranslation T (x : GaussianInt)
    lattice := TilingLattice C
    latticeReps := R
    vertexOrbitReps := {0}
    edgeOrbitReps := edges
    faceOrbitReps := faces
    shift := fun u x => u + x
    faceShift := fs
    lattice_full_rank := hR
    tiles_are_disks := fun x => (TileDiskAreaCovariance T x).1.mp hgeom.1
    shift_zero := fun x => zero_add x
    shift_add := fun u v x => add_assoc u v x
    faceShift_zero := fs_zero
    faceShift_add := fs_add
    tile_periodic := by
      intro u x
      simp only [AddSubgroup.coe_add, translate_add, add_comm]
    edge_periodic := graph_per
    face_vertices_periodic := fv_per
    position_periodic := by
      intro u x
      simp [D.position_eq, GaussianRealPoint, add_comm]
    edgeArc_periodic := D.edgeArc_periodic
    faceRegion_periodic := by
      intro u f
      simpa only [fs, D.faces.apply_symm_apply] using
        D.faceRegion_periodic u (D.faces.symm f)
    vertex_orbit_representatives := by
      intro x
      refine ⟨0, ⟨by simp, x, by simp⟩, ?_⟩
      intro r hr
      simpa using hr.1
    edge_orbit_representatives := edge_reps
    face_orbit_representatives := by
      intro f
      obtain ⟨f, rfl⟩ := D.faces.surjective f
      cases f with
      | inl x => exact ⟨D.faces (.inl 0), by simp [faces], x, by simp [fs]⟩
      | inr x => exact ⟨D.faces (.inr 0), by simp [faces], x, by simp [fs]⟩
    rho := rho
    rho_common := hrho
    rho_periodic := hrhoper
    facePath := path
    facePath_reverse := hrev
    facePath_periodic := hpathper
    facePath_spec := hpath
    area_balance := by
      simp only [Finset.sum_singleton]
      have hzero : TileTranslation T 0 = T := RegularPeriodicGeometry.hzero T
      rw [AddSubgroup.coe_zero, hzero, hgeom.2.1, hRcard, ← hqC]
      omega
    adjacent_has_common_edge := hedge }
  refine ⟨P, rfl, fun _ => rfl, signed, D.position_eq, by simp [P], edgecard, facescard, ?_⟩
  refine ⟨{
    vertexEquiv := k.toEquiv
    adjacent_iff := by intro x y; simpa [P] using D.adjacent_iff (k x) (k y)
    up := fun x => D.faces (.inl (k x))
    down := fun x => D.faces (.inr (k x))
    up_injective := D.faces.injective.comp (Sum.inl_injective.comp k.injective)
    down_injective := D.faces.injective.comp (Sum.inr_injective.comp k.injective)
    up_ne_down := fun _ _ h => Sum.inl_ne_inr (D.faces.injective h)
    face_exhaustive := by
      intro f
      obtain ⟨f, rfl⟩ := D.faces.surjective f
      cases f with
      | inl x => exact Or.inl ⟨k.symm x, by simp⟩
      | inr x => exact Or.inr ⟨k.symm x, by simp⟩
    up_vertices := by intro x; simpa [P] using D.up_vertices (k x)
    down_vertices := by intro x; simpa [P] using D.down_vertices (k x)
    tile_eq := by intro x; change TileTranslation T (k x : GaussianInt) = _; rw [hk] }⟩

end ApollonianSuperharmonic

end
