/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties
public import LeanPool.ApollonianSuperharmonic.LatticeTileNonempty

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.AffineTriangularComplexChart

-- [TABLET NODE: P4456T2BandGraphTriangle]

/-!
# P4456T2BandGraphTriangle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BandGraphTriangleGeometry

private abbrev hTne := ApollonianSuperharmonic.LatticeTileNonempty.cells

private theorem hcentCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (g : GaussianInt), ((TileTranslation (TileQuarterTurn T) g).cells =
            T.cells) → (
        let rot : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x - 1
        let cent : GaussianInt → GaussianInt := fun x => GaussianTranslation g (rot x)
        T.cells.image cent = T.cells) ) := by
  classical
  intro T g hcenter rot cent
  have hh := hcenter
  rw [(TileTranslationFormulas (TileQuarterTurn T) g).1,
    (TileQuarterTurnFormulas T).1] at hh
  rw [Finset.image_image] at hh
  change T.cells.image (fun x => GaussianTranslation g
    (GaussianQuarterTurn x - 1)) = T.cells at hh
  simpa [cent, rot] using hh

private theorem hturnedCells :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          ∀ (g : GaussianInt),
            (TileTranslation (TileQuarterTurn T) g).cells = T.cells →
              let rot : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x - 1
              let cent : GaussianInt → GaussianInt := fun x =>
                GaussianTranslation g (rot x)
              T.cells.image cent = T.cells →
                ∀ (d : GaussianInt),
                  (TileTranslation (TileQuarterTurn (TileTranslation T d)) g).cells =
                    (TileTranslation T (GaussianQuarterTurn d)).cells
    ) := by
  classical
  intro T g hcenter rot cent hcentCells d
  rw [(TileTranslationFormulas (TileQuarterTurn (TileTranslation T d)) g).1,
    (TileQuarterTurnFormulas (TileTranslation T d)).1,
    (TileTranslationFormulas T d).1,
    (TileTranslationFormulas T (GaussianQuarterTurn d)).1]
  simp only [Finset.image_image, Function.comp_def]
  change T.cells.image (fun x => GaussianTranslation g
      (GaussianQuarterTurn (GaussianTranslation d x) - 1)) =
    T.cells.image (fun x => GaussianTranslation (GaussianQuarterTurn d) x)
  calc
    _ = T.cells.image (fun x => GaussianTranslation (GaussianQuarterTurn d) (cent x)) := by
      apply Finset.image_congr
      intro x hx
      dsimp [cent, rot]
      rcases x with ⟨a, b⟩
      rcases d with ⟨c, e⟩
      rcases g with ⟨r, s⟩
      apply Zsqrtd.ext_iff.mpr
      constructor <;> simp [GaussianTranslation, GaussianQuarterTurn] <;> omega
    _ = (T.cells.image cent).image (GaussianTranslation (GaussianQuarterTurn d)) := by
      rw [Finset.image_image]
      rfl
    _ = T.cells.image (GaussianTranslation (GaussianQuarterTurn d)) := by
      rw [hcentCells]

private theorem hOpp :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        (TouchingTriple T (TileTranslation T u) (TileTranslation T (-v))) → ((T.cells.Nonempty) →
            (∀ (g : GaussianInt), ((TileTranslation (TileQuarterTurn T) g).cells = T.cells) → ((∀
            (d : GaussianInt), (TileTranslation (TileQuarterTurn (TileTranslation T d)) g).cells
            = (TileTranslation T (GaussianQuarterTurn d)).cells) → (TouchingTriple T
            (TileTranslation T (-u)) (TileTranslation T v))))) ) := by
  classical
  intro q T u v hT3 hTne g hcenter hturnedCells
  have htransne (d : GaussianInt) : (TileTranslation T d).cells.Nonempty := by
    rw [(TileTranslationFormulas T d).1]
    exact hTne.image _
  have observables (A B : ProtoTile) (hc : A.cells = B.cells)
      (hBn : B.cells.Nonempty) :
      BoundaryFootprintVertices A = BoundaryFootprintVertices B ∧
        BoundaryFootprintEdges A = BoundaryFootprintEdges B := by
    have hext := ProtoTileObservableExtensionality A B hc (by
      intro hempty
      have hbe : B.cells = ∅ := by rw [← hc]; exact hempty
      exact False.elim (hBn.ne_empty hbe))
    exact ⟨hext.2.1, hext.2.2.1⟩
  have replaceTriple (A A' B B' C C' : ProtoTile)
      (hAc : A.cells = A'.cells) (hBc : B.cells = B'.cells)
      (hCc : C.cells = C'.cells)
      (hAb : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hAe : BoundaryFootprintEdges A = BoundaryFootprintEdges A')
      (hBb : BoundaryFootprintVertices B = BoundaryFootprintVertices B')
      (hBe : BoundaryFootprintEdges B = BoundaryFootprintEdges B')
      (hCb : BoundaryFootprintVertices C = BoundaryFootprintVertices C')
      (hCe : BoundaryFootprintEdges C = BoundaryFootprintEdges C')
      (hnA : A.cells.Nonempty) (hnB : B.cells.Nonempty) (hnC : C.cells.Nonempty)
      (hh : TouchingTriple A B C) : TouchingTriple A' B' C' := by
    have touch (X X' Y Y' : ProtoTile) (hX : X.cells = X'.cells)
        (hY : Y.cells = Y'.cells)
        (hXb : BoundaryFootprintVertices X = BoundaryFootprintVertices X')
        (hXe : BoundaryFootprintEdges X = BoundaryFootprintEdges X')
        (hYb : BoundaryFootprintVertices Y = BoundaryFootprintVertices Y')
        (hYe : BoundaryFootprintEdges Y = BoundaryFootprintEdges Y')
        (hnX : X.cells.Nonempty) (hnY : Y.cells.Nonempty)
        (ht : TileTouching X Y) : TileTouching X' Y' := by
      have hnX' : X'.cells.Nonempty := by rw [← hX]; exact hnX
      have hnY' : Y'.cells.Nonempty := by rw [← hY]; exact hnY
      rcases ht with ⟨_, _, hdis, hpath⟩ | ⟨hempty, _⟩ | ⟨hempty, _⟩
      · left
        refine ⟨hnX', hnY', ?_, ?_⟩
        · simpa [hX, hY] using hdis
        · simpa [hXb, hYb, hXe, hYe] using hpath
      · exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hempty) hnX)
      · exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hempty) hnY)
    rcases hh with ⟨hab, hbc, hca, x, hx, hxuniq⟩
    refine ⟨touch A A' B B' hAc hBc hAb hAe hBb hBe hnA hnB hab,
      touch B B' C C' hBc hCc hBb hBe hCb hCe hnB hnC hbc,
      touch C C' A A' hCc hAc hCb hCe hAb hAe hnC hnA hca, x, ?_, ?_⟩
    · change x ∈ BoundaryFootprintVertices A' ∧
        x ∈ BoundaryFootprintVertices B' ∧ x ∈ BoundaryFootprintVertices C'
      rw [← hAb, ← hBb, ← hCb]
      exact hx
    · intro y hy
      have hy' : y ∈ BoundaryFootprintVertices A ∧
          y ∈ BoundaryFootprintVertices B ∧ y ∈ BoundaryFootprintVertices C := by
        constructor
        · rw [hAb]; exact hy.1
        constructor
        · rw [hBb]; exact hy.2.1
        · rw [hCb]; exact hy.2.2
      exact hxuniq y hy'
  have centeredTriple (d e : GaussianInt)
      (ht : TouchingTriple T (TileTranslation T d) (TileTranslation T e)) :
      TouchingTriple T (TileTranslation T (GaussianQuarterTurn d))
        (TileTranslation T (GaussianQuarterTurn e)) := by
    have hq := (TouchingTripleCovariance T (TileTranslation T d)
      (TileTranslation T e) 0).2.1.mp ht
    have hs := (TouchingTripleCovariance (TileQuarterTurn T)
      (TileQuarterTurn (TileTranslation T d))
      (TileQuarterTurn (TileTranslation T e)) g).1.mp hq
    have hA := observables (TileTranslation (TileQuarterTurn T) g) T hcenter hTne
    have hAne : (TileTranslation (TileQuarterTurn T) g).cells.Nonempty := by
      rw [hcenter]
      exact hTne
    have hBcells := hturnedCells d
    have hCcells := hturnedCells e
    have hB := observables (TileTranslation (TileQuarterTurn (TileTranslation T d)) g)
      (TileTranslation T (GaussianQuarterTurn d)) hBcells (htransne _)
    have hC := observables (TileTranslation (TileQuarterTurn (TileTranslation T e)) g)
      (TileTranslation T (GaussianQuarterTurn e)) hCcells (htransne _)
    exact replaceTriple _ _ _ _ _ _ hcenter hBcells hCcells
      hA.1 hA.2 hB.1 hB.2 hC.1 hC.2 hAne
      (by rw [hBcells]; exact htransne _) (by rw [hCcells]; exact htransne _) hs
  have hrot := centeredTriple u (-v) hT3
  have hhalf (z : GaussianInt) : GaussianQuarterTurn (GaussianQuarterTurn z) = -z := by
    rcases z with ⟨a, b⟩
    apply Zsqrtd.ext_iff.mpr
    simp [GaussianQuarterTurn]
  simpa [hhalf] using centeredTriple (GaussianQuarterTurn u)
    (GaussianQuarterTurn (-v)) hrot

private theorem adjSymm :
    (by
      classical
      exact
        ∀ (x : Int × Int),
          ∀ (y : Int × Int), TriangularLatticeAdjacent x y → TriangularLatticeAdjacent y x
    ) := by
  classical
  intro x y h
  simp only [TriangularLatticeAdjacent, Prod.ext_iff] at h ⊢
  rcases h with h | h | h | h | h | h <;>
    simp only [Prod.fst_sub, Prod.snd_sub] at h ⊢ <;> omega

private theorem hxy :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))), ∀ (a : ι), ∀ (b : ι), (P.plane.adjacent
            a b) → (
        let x : Int × Int := chart.vertexEquiv.symm a
        let y : Int × Int := chart.vertexEquiv.symm b
        (chart.vertexEquiv x = a) → ((chart.vertexEquiv y = b) → (TriangularLatticeAdjacent x
            y))) ) := by
  classical
  intro q T ι P chart a b hab x y hxa hyb
  apply (chart.adjacent_iff x y).mp
  simpa [hxa, hyb] using hab

private abbrev hyz := ApollonianSuperharmonic.BandGraphTriangleGeometry.hxy

private theorem hzx :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))), ∀ (a : ι), ∀ (c : ι), (P.plane.adjacent
            c a) → (
        let x : Int × Int := chart.vertexEquiv.symm a
        let z : Int × Int := chart.vertexEquiv.symm c
        (chart.vertexEquiv x = a) → ((chart.vertexEquiv z = c) → (TriangularLatticeAdjacent z
            x))) ) := by
  classical
  intro q T ι P chart a c hca' x z hxa hzc
  apply (chart.adjacent_iff z x).mp
  simpa [hzc, hxa] using hca'

private theorem hpAt297 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))), ∀ (a : ι), ∀ (b : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let y : Int × Int := chart.vertexEquiv.symm b
        (TriangularLatticeAdjacent x y) → (
        let p := y - x
        TriangularLatticeAdjacent (0, 0) p) ) := by
  classical
  intro q T ι P chart a b x y hxy p
  simp [TriangularLatticeAdjacent, p] at hxy ⊢
  simpa [Prod.sub_def, Prod.ext_iff] using hxy

private abbrev hr := ApollonianSuperharmonic.BandGraphTriangleGeometry.hpAt297

private theorem hpr :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let y : Int × Int := chart.vertexEquiv.symm b
        let z : Int × Int := chart.vertexEquiv.symm c
        (TriangularLatticeAdjacent y z) → (
        let p := y - x
        let r := z - x
        TriangularLatticeAdjacent p r) ) := by
  classical
  intro q T ι P chart a b c x y z hyz p r
  have hh := hyz
  simp only [TriangularLatticeAdjacent, Prod.ext_iff] at hh ⊢
  simp only [p, r, Prod.sub_def] at hh ⊢
  rcases hh with hh | hh | hh | hh | hh | hh <;> omega

private theorem hdir :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))), ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let y : Int × Int := chart.vertexEquiv.symm b
        let z : Int × Int := chart.vertexEquiv.symm c
        let p := y - x
        let r := z - x
        (TriangularLatticeAdjacent (0, 0) p) → ((TriangularLatticeAdjacent (0, 0) r) →
            ((TriangularLatticeAdjacent p r) → ((p = (1, 0) ∧ r = (1, 1)) ∨ (p = (1, 1) ∧ r = (1,
            0)) ∨ (p = (1, 1) ∧ r = (0, 1)) ∨ (p = (0, 1) ∧ r = (1, 1)) ∨ (p = (0, 1) ∧ r = (-1,
            0)) ∨ (p = (-1, 0) ∧ r = (0, 1)) ∨ (p = (-1, 0) ∧ r = (-1, -1)) ∨ (p = (-1, -1) ∧ r =
            (-1, 0)) ∨ (p = (-1, -1) ∧ r = (0, -1)) ∨ (p = (0, -1) ∧ r = (-1, -1)) ∨ (p = (0, -1)
            ∧ r = (1, 0)) ∨ (p = (1, 0) ∧ r = (0, -1))))) ) := by
  classical
  intro q T ι P chart a b c x y z p r hp hr hpr
  generalize hpv : p = pp at hp hr hpr ⊢
  generalize hrv : r = rr at hp hr hpr ⊢
  clear * - hp hr hpr
  simp only [TriangularLatticeAdjacent, Prod.ext_iff, Prod.sub_def,
    ] at hp hr hpr
  rcases hp with hp | hp | hp | hp | hp | hp
  all_goals rcases hr with hr | hr | hr | hr | hr | hr
  all_goals simp_all [Prod.ext_iff]

private theorem shift_add :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        ∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w' ) := by
  classical
  intro q u v shift w w'
  dsimp [shift]
  simp only [Int.cast_add, add_mul]
  ring

private theorem shift_e1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        (∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w') → (∀ (w :
            Int × Int), shift (w + (1, 0)) = shift w + u) ) := by
  classical
  intro q u v shift shift_add w
  rw [shift_add]
  simp [shift, u]

private theorem shift_e2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        (∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w') → (∀ (w :
            Int × Int), shift (w + (0, 1)) = shift w + v) ) := by
  classical
  intro q u v shift shift_add w
  rw [shift_add]
  simp [shift, v]

private theorem shift_neg_e1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        (∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w') → (∀ (w :
            Int × Int), shift (w - (1, 0)) = shift w - u) ) := by
  classical
  intro q u v shift shift_add w
  have h := shift_add (w - (1, 0)) (1, 0)
  have he : (w - (1, 0)) + (1, 0) = w := by ext <;> simp
  rw [he] at h
  have hc : shift (1, 0) = u := by simp [shift, u]
  rw [hc] at h
  calc
    shift (w - (1, 0)) = (shift (w - (1, 0)) + u) - u := by simp
    _ = shift w - u := by rw [h.symm]

private theorem shift_neg_e2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        (∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w') → (∀ (w :
            Int × Int), shift (w - (0, 1)) = shift w - v) ) := by
  classical
  intro q u v shift shift_add w
  have h := shift_add (w - (0, 1)) (0, 1)
  have he : (w - (0, 1)) + (0, 1) = w := by ext <;> simp
  rw [he] at h
  have hc : shift (0, 1) = v := by simp [shift, v]
  rw [hc] at h
  calc
    shift (w - (0, 1)) = (shift (w - (0, 1)) + v) - v := by simp
    _ = shift w - v := by rw [h.symm]

private theorem shift_mne1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        (∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w') → (∀ (w :
            Int × Int), shift (w + (-1, 0)) = shift w - u) ) := by
  classical
  intro q u v shift shift_add w
  rw [shift_add]
  have hc : shift (-1, 0) = -u := by simp [shift, u]
  rw [hc]
  abel

private theorem shift_mne2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        (∀ (w : Int × Int), ∀ (w' : Int × Int), shift (w + w') = shift w + shift w') → (∀ (w :
            Int × Int), shift (w + (0, -1)) = shift w - v) ) := by
  classical
  intro q u v shift shift_add w
  rw [shift_add]
  have hc : shift (0, -1) = -v := by simp [shift, v]
  rw [hc]
  abel

private abbrev transAssoc := ApollonianSuperharmonic.TileTranslationProperties.add

private theorem upFace :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        (TouchingTriple T (TileTranslation T u) (TileTranslation T (-v))) → (
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), shift (w + (1, 0)) = shift w + u) → ((∀ (w : Int × Int), shift (w +
            (0, -1)) = shift w - v) → ((∀ (A : ProtoTile), ∀ (s : GaussianInt), ∀ (t :
            GaussianInt), TileTranslation (TileTranslation A s) t = TileTranslation A (s + t)) →
            (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w + (1, 0))) (tileAt (w - (0,
            1))))))) ) := by
  classical
  intro q T u v hT3 shift tileAt shift_e1 shift_mne2 transAssoc w
  have hh := (TouchingTripleCovariance T (TileTranslation T u)
    (TileTranslation T (-v)) (shift w)).1.mp hT3
  simpa [tileAt, shift_e1, shift_neg_e2, shift_mne2, transAssoc, add_comm, add_left_comm,
    add_assoc, sub_eq_add_neg] using hh

private theorem downFace :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        (TouchingTriple T (TileTranslation T (-u)) (TileTranslation T v)) → (
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), shift (w + (0, 1)) = shift w + v) → ((∀ (w : Int × Int), shift (w +
            (-1, 0)) = shift w - u) → ((∀ (A : ProtoTile), ∀ (s : GaussianInt), ∀ (t :
            GaussianInt), TileTranslation (TileTranslation A s) t = TileTranslation A (s + t)) →
            (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w - (1, 0))) (tileAt (w + (0,
            1))))))) ) := by
  classical
  intro q T u v hOpp shift tileAt shift_e2 shift_mne1 transAssoc w
  have hh := (TouchingTripleCovariance T (TileTranslation T (-u))
    (TileTranslation T v) (shift w)).1.mp hOpp
  simpa [tileAt, shift_neg_e1, shift_mne1, shift_e2, transAssoc, add_comm, add_left_comm,
    add_assoc, sub_eq_add_neg] using hh

private theorem coord_m10_m01 :
    (by
      classical
      exact
        ∀ (w : Int × Int), (w + (-1, 0)) + (0, -1) = w + (-1, -1) ) := by
  classical
  intro w
  ext <;> simp [Prod.add_def]

private theorem coord_m01_m10 :
    (by
      classical
      exact
        ∀ (w : Int × Int), w + (0, -1) - (1, 0) = w + (-1, -1)
    ) := by
  classical
  intro w
  ext <;> simp [Prod.add_def, Prod.sub_def]; omega

private theorem hdown01 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w - (1, 0))) (tileAt (w + (0,
            1)))) → ((∀ (w : Int × Int), (w + (1, 0)) - (1, 0) = w) → ((∀ (w : Int × Int), (w +
            (1, 0)) + (0, 1) = w + (1, 1)) → ((∀ (w : Int × Int), ∀ (w' : Int × Int), (w = w') →
            (tileAt w = tileAt w')) → (TouchingTriple (tileAt (x + (1, 0))) (tileAt x) (tileAt (x
            + (1, 1))))))) ) := by
  classical
  intro q T ι P chart u v a x shift tileAt downFace coord_p10_m10 coord_p10_p01 tileCongr
  have hh := downFace (x + (1, 0))
  rw [tileCongr _ _ (coord_p10_m10 x), tileCongr _ _ (coord_p10_p01 x)] at hh
  exact hh

private theorem hup12 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w + (1, 0))) (tileAt (w - (0,
            1)))) → ((∀ (w : Int × Int), (w + (0, 1)) + (1, 0) = w + (1, 1)) → ((∀ (w : Int ×
            Int), (w + (0, 1)) - (0, 1) = w) → ((∀ (w : Int × Int), ∀ (w' : Int × Int), (w = w')
            → (tileAt w = tileAt w')) → (TouchingTriple (tileAt (x + (0, 1))) (tileAt (x + (1,
            1))) (tileAt x))))) ) := by
  classical
  intro q T ι P chart u v a x shift tileAt upFace coord_p01_p10 coord_p01_m01 tileCongr
  have hh := upFace (x + (0, 1))
  rw [tileCongr _ _ (coord_p01_p10 x), tileCongr _ _ (coord_p01_m01 x)] at hh
  exact hh

private theorem hdown23 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w - (1, 0))) (tileAt (w + (0,
            1)))) → ((∀ (w : Int × Int), w - (1, 0) = w + (-1, 0)) → ((∀ (w : Int × Int), ∀ (w' :
            Int × Int), (w = w') → (tileAt w = tileAt w')) → (TouchingTriple (tileAt x) (tileAt
            (x + (-1, 0))) (tileAt (x + (0, 1)))))) ) := by
  classical
  intro q T ι P chart u v a x shift tileAt downFace coord_sub10 tileCongr
  have hh := downFace x
  rw [tileCongr _ _ (coord_sub10 x)] at hh
  exact hh

private theorem hup34 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w + (1, 0))) (tileAt (w - (0,
            1)))) → ((∀ (w : Int × Int), (w + (-1, 0)) + (1, 0) = w) → ((∀ (w : Int × Int), (w +
            (-1, 0)) + (0, -1) = w + (-1, -1)) → ((∀ (w : Int × Int), w - (0, 1) = w + (0, -1)) →
            ((∀ (w : Int × Int), ∀ (w' : Int × Int), (w = w') → (tileAt w = tileAt w')) →
            (TouchingTriple (tileAt (x + (-1, 0))) (tileAt x) (tileAt (x + (-1, -1)))))))) ) := by
  classical
  intro q T ι P chart u v a x shift tileAt upFace coord_m10_p10 coord_m10_m01 coord_sub01 tileCongr
  have hh := upFace (x + (-1, 0))
  rw [tileCongr _ _ (coord_m10_p10 x), tileCongr _ _ (coord_sub01 (x + (-1, 0))),
    tileCongr _ _ (coord_m10_m01 x)] at hh
  exact hh

private theorem hdown45 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w - (1, 0))) (tileAt (w + (0,
            1)))) → ((∀ (w : Int × Int), (w + (0, -1)) - (1, 0) = w + (-1, -1)) → ((∀ (w : Int ×
            Int), (w + (0, -1)) + (0, 1) = w) → ((∀ (w : Int × Int), ∀ (w' : Int × Int), (w = w')
            → (tileAt w = tileAt w')) → (TouchingTriple (tileAt (x + (0, -1))) (tileAt (x + (-1,
            -1))) (tileAt x))))) ) := by
  classical
  intro q T ι P chart u v a x shift tileAt downFace coord_m01_m10 coord_m01_p01 tileCongr
  have hh := downFace (x + (0, -1))
  rw [tileCongr _ _ (coord_m01_m10 x), tileCongr _ _ (coord_m01_p01 x)] at hh
  exact hh

private theorem hup50 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), TouchingTriple (tileAt w) (tileAt (w + (1, 0))) (tileAt (w - (0,
            1)))) → ((∀ (w : Int × Int), w - (0, 1) = w + (0, -1)) → ((∀ (w : Int × Int), ∀ (w' :
            Int × Int), (w = w') → (tileAt w = tileAt w')) → (TouchingTriple (tileAt x) (tileAt
            (x + (1, 0))) (tileAt (x + (0, -1)))))) ) := by
  classical
  intro q T ι P chart u v a x shift tileAt upFace coord_sub01 tileCongr
  have hh := upFace x
  rw [tileCongr _ _ (coord_sub01 x)] at hh
  exact hh

private theorem offsetEq :
    (by
      classical
      exact
        ∀ (w : Int × Int), ∀ (w' : Int × Int), ∀ (d : Int × Int), w - w' = d → w = w' + d
    ) := by
  classical
  intro w w' d h
  rcases w with ⟨a₁, a₂⟩
  rcases w' with ⟨b₁, b₂⟩
  rcases d with ⟨c₁, c₂⟩
  simp only [Prod.sub_def, Prod.add_def, Prod.mk.injEq] at h ⊢
  omega

private theorem hlocal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let y : Int × Int := chart.vertexEquiv.symm b
        let z : Int × Int := chart.vertexEquiv.symm c
        let p := y - x
        let r := z - x
        ((p = (1, 0) ∧ r = (1, 1)) ∨ (p = (1, 1) ∧ r = (1, 0)) ∨ (p = (1, 1) ∧ r = (0, 1)) ∨ (p =
            (0, 1) ∧ r = (1, 1)) ∨ (p = (0, 1) ∧ r = (-1, 0)) ∨ (p = (-1, 0) ∧ r = (0, 1)) ∨ (p =
            (-1, 0) ∧ r = (-1, -1)) ∨ (p = (-1, -1) ∧ r = (-1, 0)) ∨ (p = (-1, -1) ∧ r = (0, -1))
            ∨ (p = (0, -1) ∧ r = (-1, -1)) ∨ (p = (0, -1) ∧ r = (1, 0)) ∨ (p = (1, 0) ∧ r = (0,
            -1))) → (
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), ∀ (w' : Int × Int), (w = w') → (tileAt w = tileAt w')) →
            ((TouchingTriple (tileAt (x + (1, 0))) (tileAt x) (tileAt (x + (1, 1)))) →
            ((TouchingTriple (tileAt (x + (0, 1))) (tileAt (x + (1, 1))) (tileAt x)) →
            ((TouchingTriple (tileAt x) (tileAt (x + (-1, 0))) (tileAt (x + (0, 1)))) →
            ((TouchingTriple (tileAt (x + (-1, 0))) (tileAt x) (tileAt (x + (-1, -1)))) →
            ((TouchingTriple (tileAt (x + (0, -1))) (tileAt (x + (-1, -1))) (tileAt x)) →
            ((TouchingTriple (tileAt x) (tileAt (x + (1, 0))) (tileAt (x + (0, -1)))) → ((∀ (w :
            Int × Int), ∀ (w' : Int × Int), ∀ (d : Int × Int), (w - w' = d) → (w = w' + d)) →
            (TouchingTriple (tileAt x) (tileAt y) (tileAt z)))))))))) ) := by
  classical
  intro q T ι P chart u v a b c x y z p r hdir shift tileAt tileCongr hdown01 hup12 hdown23 hup34
      hdown45 hup50 offsetEq
  rcases hdir with h | h | h | h | h | h | h | h | h | h | h | h
  · have hy : y = x + (1, 0) := offsetEq y x (1, 0) (by simpa [p] using h.1)
    have hz : z = x + (1, 1) := offsetEq z x (1, 1) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (1, 0)))
      (tileAt x) (tileAt (x + (1, 1)))).mp hdown01
    rw [tileCongr y (x + (1, 0)) hy, tileCongr z (x + (1, 1)) hz]
    exact hperms.2.1
  · have hy : y = x + (1, 1) := offsetEq y x (1, 1) (by simpa [p] using h.1)
    have hz : z = x + (1, 0) := offsetEq z x (1, 0) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (1, 0)))
      (tileAt x) (tileAt (x + (1, 1)))).mp hdown01
    rw [tileCongr y (x + (1, 1)) hy, tileCongr z (x + (1, 0)) hz]
    exact hperms.2.2.1
  · have hy : y = x + (1, 1) := offsetEq y x (1, 1) (by simpa [p] using h.1)
    have hz : z = x + (0, 1) := offsetEq z x (0, 1) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (0, 1)))
      (tileAt (x + (1, 1))) (tileAt x)).mp hup12
    rw [tileCongr y (x + (1, 1)) hy, tileCongr z (x + (0, 1)) hz]
    exact hperms.2.2.2.2
  · have hy : y = x + (0, 1) := offsetEq y x (0, 1) (by simpa [p] using h.1)
    have hz : z = x + (1, 1) := offsetEq z x (1, 1) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (0, 1)))
      (tileAt (x + (1, 1))) (tileAt x)).mp hup12
    rw [tileCongr y (x + (0, 1)) hy, tileCongr z (x + (1, 1)) hz]
    exact hperms.2.2.2.1
  · have hy : y = x + (0, 1) := offsetEq y x (0, 1) (by simpa [p] using h.1)
    have hz : z = x + (-1, 0) := offsetEq z x (-1, 0) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt x) (tileAt (x + (-1, 0)))
      (tileAt (x + (0, 1)))).mp hdown23
    rw [tileCongr y (x + (0, 1)) hy, tileCongr z (x + (-1, 0)) hz]
    exact hperms.1
  · have hy : y = x + (-1, 0) := offsetEq y x (-1, 0) (by simpa [p] using h.1)
    have hz : z = x + (0, 1) := offsetEq z x (0, 1) (by simpa [r] using h.2)
    rw [tileCongr y (x + (-1, 0)) hy, tileCongr z (x + (0, 1)) hz]
    exact hdown23
  · have hy : y = x + (-1, 0) := offsetEq y x (-1, 0) (by simpa [p] using h.1)
    have hz : z = x + (-1, -1) := offsetEq z x (-1, -1) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (-1, 0))) (tileAt x)
      (tileAt (x + (-1, -1)))).mp hup34
    rw [tileCongr y (x + (-1, 0)) hy, tileCongr z (x + (-1, -1)) hz]
    exact hperms.2.1
  · have hy : y = x + (-1, -1) := offsetEq y x (-1, -1) (by simpa [p] using h.1)
    have hz : z = x + (-1, 0) := offsetEq z x (-1, 0) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (-1, 0))) (tileAt x)
      (tileAt (x + (-1, -1)))).mp hup34
    rw [tileCongr y (x + (-1, -1)) hy, tileCongr z (x + (-1, 0)) hz]
    exact hperms.2.2.1
  · have hy : y = x + (-1, -1) := offsetEq y x (-1, -1) (by simpa [p] using h.1)
    have hz : z = x + (0, -1) := offsetEq z x (0, -1) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (0, -1)))
      (tileAt (x + (-1, -1))) (tileAt x)).mp hdown45
    rw [tileCongr y (x + (-1, -1)) hy, tileCongr z (x + (0, -1)) hz]
    exact hperms.2.2.2.2
  · have hy : y = x + (0, -1) := offsetEq y x (0, -1) (by simpa [p] using h.1)
    have hz : z = x + (-1, -1) := offsetEq z x (-1, -1) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt (x + (0, -1)))
      (tileAt (x + (-1, -1))) (tileAt x)).mp hdown45
    rw [tileCongr y (x + (0, -1)) hy, tileCongr z (x + (-1, -1)) hz]
    exact hperms.2.2.2.1
  · have hy : y = x + (0, -1) := offsetEq y x (0, -1) (by simpa [p] using h.1)
    have hz : z = x + (1, 0) := offsetEq z x (1, 0) (by simpa [r] using h.2)
    have hperms := (TouchingTriplePermutations (tileAt x) (tileAt (x + (1, 0)))
      (tileAt (x + (0, -1)))).mp hup50
    rw [tileCongr y (x + (0, -1)) hy, tileCongr z (x + (1, 0)) hz]
    exact hperms.1
  · have hy : y = x + (1, 0) := offsetEq y x (1, 0) (by simpa [p] using h.1)
    have hz : z = x + (0, -1) := offsetEq z x (0, -1) (by simpa [r] using h.2)
    rw [tileCongr y (x + (1, 0)) hy, tileCongr z (x + (0, -1)) hz]
    exact hup50

private theorem htarget :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (ι : Type), ∀ (P :
            PeriodicTileComplex ι), ∀ (chart : AffineTriangularComplexChart P (fun mn : Int × Int
            => TileTranslation T ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) + (mn.2 :
            GaussianInt) * BandVectors.1 (q 2) (q 0)))),
        let u : GaussianInt := BandVectors.1 (q 1) (q 0)
        let v : GaussianInt := BandVectors.1 (q 2) (q 0)
        ∀ (a : ι), ∀ (b : ι), ∀ (c : ι),
        let x : Int × Int := chart.vertexEquiv.symm a
        let y : Int × Int := chart.vertexEquiv.symm b
        let z : Int × Int := chart.vertexEquiv.symm c
        (chart.vertexEquiv x = a) → ((chart.vertexEquiv y = b) → ((chart.vertexEquiv z = c) → (
        let shift : Int × Int → GaussianInt := fun w =>
          (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
        let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
        (∀ (w : Int × Int), P.tile (chart.vertexEquiv w) = tileAt w) → ((TouchingTriple (tileAt
            x) (tileAt y) (tileAt z)) → (TouchingTriple (P.tile a) (P.tile b) (P.tile c)))))) )
            := by
  classical
  intro q T ι P chart u v a b c x y z hxa hyb hzc shift tileAt chartTile hlocal
  have ht := hlocal
  rw [← chartTile x, ← chartTile y, ← chartTile z] at ht
  rw [hxa, hyb, hzc] at ht
  exact ht

end BandGraphTriangleGeometry

theorem P4456T2BandGraphTriangle (q : Fin 4 → CircleCoordinates)
    (hq : ProperBandQuadruple q) (T : ProtoTile)
    (hT : BandPrototile (q 0) T) (hlarge : 1 < (q 0).1)
    {ι : Type} (P : PeriodicTileComplex ι)
    (chart : AffineTriangularComplexChart P (fun mn : Int × Int =>
      TileTranslation T
        ((mn.1 : GaussianInt) * BandVectors.1 (q 1) (q 0) +
          (mn.2 : GaussianInt) * BandVectors.1 (q 2) (q 0)))) :
    ∀ a b c : ι, a ≠ b → b ≠ c → c ≠ a →
      P.plane.adjacent a b → P.plane.adjacent b c →
      P.plane.adjacent c a → TouchingTriple (P.tile a) (P.tile b) (P.tile c) := by
-- BODY
  classical
  let u : GaussianInt := BandVectors.1 (q 1) (q 0)
  let v : GaussianInt := BandVectors.1 (q 2) (q 0)
  have hsim := BandTileSimultaneousInduction q hq T hT
  have hT1 : LatticeTile T := hsim.1
  have hT2 : QuarterTurnSymmetric T := hsim.2.2.2.1
  have hT3 : TouchingTriple T (TileTranslation T u) (TileTranslation T (-v)) := by
    simpa [u, v] using (hsim.2.2.2.2.1 hlarge 0)
  have hTne : T.cells.Nonempty := BandGraphTriangleGeometry.hTne T hT1
  obtain ⟨g, hg, hcenter, _, _, _⟩ := QuarterTurnSymmetricCenteredTransport T hT2
  let rot : GaussianInt → GaussianInt := fun x => GaussianQuarterTurn x - 1
  let cent : GaussianInt → GaussianInt := fun x => GaussianTranslation g (rot x)
  have hcentCells : T.cells.image cent = T.cells := BandGraphTriangleGeometry.hcentCells T g hcenter
  have hturnedCells (d : GaussianInt) :
      (TileTranslation (TileQuarterTurn (TileTranslation T d)) g).cells =
        (TileTranslation T (GaussianQuarterTurn d)).cells :=
            BandGraphTriangleGeometry.hturnedCells T g hcenter hcentCells d
  have hOpp : TouchingTriple T (TileTranslation T (-u)) (TileTranslation T v) :=
      BandGraphTriangleGeometry.hOpp q T hT3 hTne g hcenter hturnedCells
  intro a b c habc hbcc hca hab hbc hca'
  have adjSymm (x y : Int × Int) (h : TriangularLatticeAdjacent x y) :
      TriangularLatticeAdjacent y x := BandGraphTriangleGeometry.adjSymm x y h
  let x : Int × Int := chart.vertexEquiv.symm a
  let y : Int × Int := chart.vertexEquiv.symm b
  let z : Int × Int := chart.vertexEquiv.symm c
  have hxa : chart.vertexEquiv x = a := by simp [x]
  have hyb : chart.vertexEquiv y = b := by simp [y]
  have hzc : chart.vertexEquiv z = c := by simp [z]
  have hxy : TriangularLatticeAdjacent x y := BandGraphTriangleGeometry.hxy q T ι P chart a b hab
      hxa hyb
  have hyz : TriangularLatticeAdjacent y z := BandGraphTriangleGeometry.hyz q T ι P chart b c hbc
      hyb hzc
  have hzx : TriangularLatticeAdjacent z x := BandGraphTriangleGeometry.hzx q T ι P chart a c
      hca' hxa hzc
  have hzx' : TriangularLatticeAdjacent x z := adjSymm z x hzx
  let p := y - x
  let r := z - x
  have hp : TriangularLatticeAdjacent (0, 0) p := BandGraphTriangleGeometry.hpAt297 q T ι P chart
      a b hxy
  have hr : TriangularLatticeAdjacent (0, 0) r := BandGraphTriangleGeometry.hr q T ι P chart a c
      hzx'
  have hpr : TriangularLatticeAdjacent p r := BandGraphTriangleGeometry.hpr q T ι P chart a b c hyz
  have hdir :
      (p = (1, 0) ∧ r = (1, 1)) ∨ (p = (1, 1) ∧ r = (1, 0)) ∨
      (p = (1, 1) ∧ r = (0, 1)) ∨ (p = (0, 1) ∧ r = (1, 1)) ∨
      (p = (0, 1) ∧ r = (-1, 0)) ∨ (p = (-1, 0) ∧ r = (0, 1)) ∨
      (p = (-1, 0) ∧ r = (-1, -1)) ∨ (p = (-1, -1) ∧ r = (-1, 0)) ∨
      (p = (-1, -1) ∧ r = (0, -1)) ∨ (p = (0, -1) ∧ r = (-1, -1)) ∨
      (p = (0, -1) ∧ r = (1, 0)) ∨ (p = (1, 0) ∧ r = (0, -1)) := BandGraphTriangleGeometry.hdir q
          T ι P chart a b c hp hr hpr
  let shift : Int × Int → GaussianInt := fun w =>
    (w.1 : GaussianInt) * u + (w.2 : GaussianInt) * v
  let tileAt : Int × Int → ProtoTile := fun w => TileTranslation T (shift w)
  have shift_add (w w' : Int × Int) : shift (w + w') = shift w + shift w' :=
      BandGraphTriangleGeometry.shift_add q w w'
  have shift_e1 (w : Int × Int) : shift (w + (1, 0)) = shift w + u :=
      BandGraphTriangleGeometry.shift_e1 q shift_add w
  have shift_e2 (w : Int × Int) : shift (w + (0, 1)) = shift w + v :=
      BandGraphTriangleGeometry.shift_e2 q shift_add w
  have shift_mne1 (w : Int × Int) : shift (w + (-1, 0)) = shift w - u :=
      BandGraphTriangleGeometry.shift_mne1 q shift_add w
  have shift_mne2 (w : Int × Int) : shift (w + (0, -1)) = shift w - v :=
      BandGraphTriangleGeometry.shift_mne2 q shift_add w
  have transAssoc (A : ProtoTile) (s t : GaussianInt) :
      TileTranslation (TileTranslation A s) t = TileTranslation A (s + t) :=
          BandGraphTriangleGeometry.transAssoc A s t
  have upFace (w : Int × Int) :
      TouchingTriple (tileAt w) (tileAt (w + (1, 0))) (tileAt (w - (0, 1))) :=
          BandGraphTriangleGeometry.upFace q T hT3 shift_e1 shift_mne2 transAssoc w
  have downFace (w : Int × Int) :
      TouchingTriple (tileAt w) (tileAt (w - (1, 0))) (tileAt (w + (0, 1))) :=
          BandGraphTriangleGeometry.downFace q T hOpp shift_e2 shift_mne1 transAssoc w
  have chartTile (w : Int × Int) : P.tile (chart.vertexEquiv w) = tileAt w := by
    simpa [tileAt, shift, u, v] using chart.tile_eq w
  have coord_p10_m10 (w : Int × Int) :
      (w + (1, 0)) - (1, 0) = w := by ext <;> simp [Prod.add_def, Prod.sub_def]
  have coord_p10_p01 (w : Int × Int) :
      (w + (1, 0)) + (0, 1) = w + (1, 1) := by ext <;> simp [Prod.add_def]
  have coord_p01_p10 (w : Int × Int) :
      (w + (0, 1)) + (1, 0) = w + (1, 1) := by ext <;> simp [Prod.add_def]
  have coord_p01_m01 (w : Int × Int) :
      (w + (0, 1)) - (0, 1) = w := by ext <;> simp [Prod.add_def, Prod.sub_def]
  have coord_m10_p10 (w : Int × Int) :
      (w + (-1, 0)) + (1, 0) = w := by ext <;> simp [Prod.add_def]
  have coord_m10_m01 (w : Int × Int) :
      (w + (-1, 0)) + (0, -1) = w + (-1, -1) := BandGraphTriangleGeometry.coord_m10_m01 w
  have coord_m01_m10 (w : Int × Int) :
      (w + (0, -1)) - (1, 0) = w + (-1, -1) := BandGraphTriangleGeometry.coord_m01_m10 w
  have coord_m01_p01 (w : Int × Int) :
      (w + (0, -1)) + (0, 1) = w := by ext <;> simp [Prod.add_def]
  have coord_sub10 (w : Int × Int) : w - (1, 0) = w + (-1, 0) := by
    ext <;> simp [Prod.add_def, Prod.sub_def]; omega
  have coord_sub01 (w : Int × Int) : w - (0, 1) = w + (0, -1) := by
    ext <;> simp [Prod.add_def, Prod.sub_def]; omega
  have tileCongr (w w' : Int × Int) (h : w = w') : tileAt w = tileAt w' :=
    congrArg tileAt h
  have hdown01 : TouchingTriple (tileAt (x + (1, 0))) (tileAt x)
      (tileAt (x + (1, 1))) := BandGraphTriangleGeometry.hdown01 q T ι P chart a downFace
          coord_p10_m10 coord_p10_p01 tileCongr
  have hup12 : TouchingTriple (tileAt (x + (0, 1)))
      (tileAt (x + (1, 1))) (tileAt x) := BandGraphTriangleGeometry.hup12 q T ι P chart a upFace
          coord_p01_p10 coord_p01_m01 tileCongr
  have hdown23 : TouchingTriple (tileAt x) (tileAt (x + (-1, 0)))
      (tileAt (x + (0, 1))) := BandGraphTriangleGeometry.hdown23 q T ι P chart a downFace
          coord_sub10 tileCongr
  have hup34 : TouchingTriple (tileAt (x + (-1, 0))) (tileAt x)
      (tileAt (x + (-1, -1))) := BandGraphTriangleGeometry.hup34 q T ι P chart a upFace
          coord_m10_p10 coord_m10_m01 coord_sub01 tileCongr
  have hdown45 : TouchingTriple (tileAt (x + (0, -1)))
      (tileAt (x + (-1, -1))) (tileAt x) := BandGraphTriangleGeometry.hdown45 q T ι P chart a
          downFace coord_m01_m10 coord_m01_p01 tileCongr
  have hup50 : TouchingTriple (tileAt x) (tileAt (x + (1, 0)))
      (tileAt (x + (0, -1))) := BandGraphTriangleGeometry.hup50 q T ι P chart a upFace
          coord_sub01 tileCongr
  have offsetEq (w w' d : Int × Int) (h : w - w' = d) : w = w' + d :=
      BandGraphTriangleGeometry.offsetEq w w' d h
  have hlocal : TouchingTriple (tileAt x) (tileAt y) (tileAt z) :=
      BandGraphTriangleGeometry.hlocal q T ι P chart a b c hdir tileCongr hdown01 hup12 hdown23
      hup34 hdown45 hup50 offsetEq
  have htarget : TouchingTriple (P.tile a) (P.tile b) (P.tile c) :=
      BandGraphTriangleGeometry.htarget q T ι P chart a b c hxa hyb hzc chartTile hlocal
  exact htarget

end ApollonianSuperharmonic

end
