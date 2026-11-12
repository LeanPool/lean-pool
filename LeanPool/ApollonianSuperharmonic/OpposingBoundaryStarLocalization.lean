/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularNoFourfoldCellOwners
public import LeanPool.ApollonianSuperharmonic.AncestorOdometer
public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.BandRegularTileTouchingClassification
public import LeanPool.ApollonianSuperharmonic.BandRegularTranslatePeriodicComplex
public import LeanPool.ApollonianSuperharmonic.CircleMatrixIncomingVector
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.LatticeTileGridStructure
public import LeanPool.ApollonianSuperharmonic.OpposingBoundaryInterfaceExhaustion
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.PositiveCurvatureTileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.ProperBandQuadruple
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: OpposingBoundaryStarLocalization]

/-!
# OpposingBoundaryStarLocalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OpposingStarGeometry

private theorem hxT0 :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (h0 : PartialOdometer), ∀ (x : GaussianInt), (x ∈ h0.domain) →
            (((↑h0.domain : Set GaussianInt) = FootprintVertices T0) → (x ∈ FootprintVertices
            T0)) ) := by
  classical
  intro T0 h0 x hx0 hdomain0
  rw [← hdomain0]
  exact hx0

private theorem hxT0' :
    (by
      classical
      exact
        ∀ (T0' : ProtoTile), ∀ (h0' : PartialOdometer), ∀ (x : GaussianInt), (x ∈ h0'.domain) →
            (((↑h0'.domain : Set GaussianInt) = FootprintVertices T0') → (x ∈ FootprintVertices
            T0')) ) := by
  classical
  intro T0' h0' x hx0' hdomain0'
  rw [← hdomain0']
  exact hx0'

private theorem hxPath :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (T0' : ProtoTile), ∀ (x : GaussianInt), ∀ (path : List
            GaussianInt), (FootprintVertices T0 ∩ FootprintVertices T0' = (↑path.toFinset : Set
            GaussianInt)) → ((x ∈ FootprintVertices T0) → ((x ∈ FootprintVertices T0') → (x ∈
            path))) ) := by
  classical
  intro T0 T0' x path hvertices hxT0 hxT0'
  have hxinter : x ∈ FootprintVertices T0 ∩ FootprintVertices T0' := ⟨hxT0, hxT0'⟩
  rw [hvertices] at hxinter
  simpa using hxinter

private theorem cellCorner :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (c : GaussianInt), (c ∈ T.cells) → (∀ (z : GaussianInt), (z = c ∨ z
            = c + 1 ∨ z = c + ⟨0, 1⟩ ∨
            z = c + 1 + ⟨0, 1⟩) → (z ∈ FootprintVertices T)) ) := by
  classical
  intro T c hc z hz
  rw [FootprintVertices, ite_eq_left ⟨c, hc⟩]
  exact ⟨c, hc, hz⟩

private theorem hxU :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (x ∈ U.cells ∧ x - (1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ V.cells ∨ x ∈ V.cells ∧ x - (1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ U.cells ∨ x - (1 : GaussianInt) ∈
            U.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ V.cells ∨ x - (1 : GaussianInt) ∈
            V.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ U.cells) → ((∀ (T : ProtoTile), ∀
            (c : GaussianInt), (c ∈ T.cells) → (∀ (z : GaussianInt), (z = c ∨ z = c + 1 ∨ z = c +
            ⟨0, 1⟩ ∨ z = c + 1 + ⟨0, 1⟩) → (z ∈ FootprintVertices T))) → (x ∈ FootprintVertices
            U)) ) := by
  classical
  intro x U V hownedCells cellCorner
  rcases hownedCells with hA | hB | hC | hD
  · exact cellCorner U x hA.1 x (Or.inl rfl)
  · exact cellCorner U (x - 1 - ⟨0, 1⟩) hB.2 x
      (Or.inr (Or.inr (Or.inr (by abel))) )
  · exact cellCorner U (x - 1) hC.1 x
      (Or.inr (Or.inl (by abel)))
  · exact cellCorner U (x - ⟨0, 1⟩) hD.2 x
      (Or.inr (Or.inr (Or.inl (by abel))))

private theorem hxV :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (x ∈ U.cells ∧ x - (1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ V.cells ∨ x ∈ V.cells ∧ x - (1 :
            GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ U.cells ∨ x - (1 : GaussianInt) ∈
            U.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ V.cells ∨ x - (1 : GaussianInt) ∈
            V.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∈ U.cells) → ((∀ (T : ProtoTile), ∀
            (c : GaussianInt), (c ∈ T.cells) → (∀ (z : GaussianInt), (z = c ∨ z = c + 1 ∨ z = c +
            ⟨0, 1⟩ ∨ z = c + 1 + ⟨0, 1⟩) → (z ∈ FootprintVertices T))) → (x ∈ FootprintVertices
            V)) ) := by
  classical
  intro x U V hownedCells cellCorner
  rcases hownedCells with hA | hB | hC | hD
  · exact cellCorner V (x - 1 - ⟨0, 1⟩) hA.2 x
      (Or.inr (Or.inr (Or.inr (by abel))))
  · exact cellCorner V x hB.1 x (Or.inl rfl)
  · exact cellCorner V (x - ⟨0, 1⟩) hC.2 x
      (Or.inr (Or.inr (Or.inl (by abel))))
  · exact cellCorner V (x - 1) hD.1 x
      (Or.inr (Or.inl (by abel)))

private theorem vertexToG :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (g : PartialOdometer), ((↑g.domain : Set GaussianInt) =
            FootprintVertices U) → (∀ z, z ∈ FootprintVertices U → z ∈ g.domain) ) := by
  classical
  intro U g hdomU z hz
  have hs : z ∈ (g.domain : Set GaussianInt) := by rw [hdomU]; exact hz
  simpa using hs

private theorem vertexToK :
    (by
      classical
      exact
        ∀ (V : ProtoTile), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FootprintVertices V) → (∀ z, z ∈ FootprintVertices V → z ∈ k.domain) ) := by
  classical
  intro V k hdomV z hz
  have hs : z ∈ (k.domain : Set GaussianInt) := by rw [hdomV]; exact hz
  simpa using hs

private theorem hcover :
    (by
      classical
      exact
        ∀ (x : GaussianInt), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (g : PartialOdometer), ∀ (k
            : PartialOdometer), (x ∈ U.cells ∧ x - (1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ V.cells ∨ x ∈ V.cells ∧ x - (1 : GaussianInt) - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ U.cells ∨ x - (1 : GaussianInt) ∈ U.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ V.cells ∨ x - (1 : GaussianInt) ∈ V.cells ∧ x - (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∈ U.cells) → ((∀ (T : ProtoTile), ∀ (c : GaussianInt), (c ∈ T.cells) →
            (∀ (z : GaussianInt), (z = c ∨ z = c + 1 ∨ z = c + ⟨0, 1⟩ ∨ z = c + 1 + ⟨0, 1⟩) → (z
            ∈ FootprintVertices T))) → ((x ∈ g.domain) → ((x ∈ k.domain) → ((∀ z, z ∈
            FootprintVertices U → z ∈ g.domain) → ((∀ z, z ∈ FootprintVertices V → z ∈ k.domain)
            → (∀ z, z = x ∨ z = x + 1 ∨ z = x - 1 ∨ z = x + ⟨0, 1⟩ ∨ z = x - ⟨0, 1⟩ → z ∈
            g.domain ∨ z ∈ k.domain)))))) ) := by
  classical
  intro x U V g k hownedCells cellCorner hxg hxk vertexToG vertexToK z hz
  rcases hownedCells with hA | hB | hC | hD
  · rcases hz with hzx | hzp | hzm | hzi | hzmi
    · rw [hzx]; exact Or.inl hxg
    · rw [hzp]; apply Or.inl; apply vertexToG; apply cellCorner U x hA.1
      exact Or.inr (Or.inl rfl)
    · rw [hzm]; apply Or.inr; apply vertexToK
      apply cellCorner V (x - 1 - ⟨0, 1⟩) hA.2
      exact Or.inr (Or.inr (Or.inl (by abel)))
    · rw [hzi]; apply Or.inl; apply vertexToG; apply cellCorner U x hA.1
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [hzmi]; apply Or.inr; apply vertexToK
      apply cellCorner V (x - 1 - ⟨0, 1⟩) hA.2
      exact Or.inr (Or.inl (by abel))
  · rcases hz with hzx | hzp | hzm | hzi | hzmi
    · rw [hzx]; exact Or.inr hxk
    · rw [hzp]; apply Or.inr; apply vertexToK; apply cellCorner V x hB.1
      exact Or.inr (Or.inl rfl)
    · rw [hzm]; apply Or.inl; apply vertexToG
      apply cellCorner U (x - 1 - ⟨0, 1⟩) hB.2
      exact Or.inr (Or.inr (Or.inl (by abel)))
    · rw [hzi]; apply Or.inr; apply vertexToK; apply cellCorner V x hB.1
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [hzmi]; apply Or.inl; apply vertexToG
      apply cellCorner U (x - 1 - ⟨0, 1⟩) hB.2
      exact Or.inr (Or.inl (by abel))
  · rcases hz with hzx | hzp | hzm | hzi | hzmi
    · rw [hzx]; apply Or.inl; apply vertexToG; apply cellCorner U (x - 1) hC.1
      exact Or.inr (Or.inl (by abel))
    · rw [hzp]; apply Or.inr; apply vertexToK; apply cellCorner V (x - ⟨0, 1⟩) hC.2
      exact Or.inr (Or.inr (Or.inr (by abel)))
    · rw [hzm]; apply Or.inl; apply vertexToG; apply cellCorner U (x - 1) hC.1
      exact Or.inl (by abel)
    · rw [hzi]; apply Or.inl; apply vertexToG; apply cellCorner U (x - 1) hC.1
      exact Or.inr (Or.inr (Or.inr (by abel)))
    · rw [hzmi]; apply Or.inr; apply vertexToK; apply cellCorner V (x - ⟨0, 1⟩) hC.2
      exact Or.inl rfl
  · rcases hz with hzx | hzp | hzm | hzi | hzmi
    · rw [hzx]; apply Or.inr; apply vertexToK; apply cellCorner V (x - 1) hD.1
      exact Or.inr (Or.inl (by abel))
    · rw [hzp]; apply Or.inl; apply vertexToG; apply cellCorner U (x - ⟨0, 1⟩) hD.2
      exact Or.inr (Or.inr (Or.inr (by abel)))
    · rw [hzm]; apply Or.inr; apply vertexToK; apply cellCorner V (x - 1) hD.1
      exact Or.inl rfl
    · rw [hzi]; apply Or.inr; apply vertexToK; apply cellCorner V (x - 1) hD.1
      exact Or.inr (Or.inr (Or.inr (by abel)))
    · rw [hzmi]; apply Or.inl; apply vertexToG; apply cellCorner U (x - ⟨0, 1⟩) hD.2
      exact Or.inl rfl

private theorem hcurvature :
    (by
      classical
      exact
        ∀ (q : Fin 4 -> CircleCoordinates), (BandOrderedGeneralConfiguration q) → (∀ (C0 :
            BandCircle), ∀ (Ci : BandCircle), ∀ (i : Fin 3), (q (0 : Fin (4 : ℕ)) = C0.1.1) → ((q
            i.succ = Ci.1.1) → (Ci.1.1.1 < C0.1.1.1))) ) := by
  classical
  intro q cfg C0 Ci i hC0 hCi
  have hlt := cfg.proper.2 i
  rw [hCi, hC0] at hlt
  exact hlt

private theorem hPU :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (U : ProtoTile), ∀ (u : GaussianInt), ∀ (huL
            : u ∈ TilingLattice Ci), (U = TileTranslation base u) → (
        let uIdx : TilingLattice Ci := ⟨u, huL⟩
        ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (u : ↥(TilingLattice Ci)), P.tile u =
            TileTranslation base (↑u : GaussianInt)) → (P.tile uIdx = U)) ) := by
  classical
  intro Ci base U u huL hUeq uIdx P hPtile
  rw [hPtile]
  simpa [uIdx] using hUeq.symm

private theorem hPV :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (base : ProtoTile), ∀ (V : ProtoTile), ∀ (v : GaussianInt), ∀ (hvL
            : v ∈ TilingLattice Ci), (V = TileTranslation base v) → (
        let vIdx : TilingLattice Ci := ⟨v, hvL⟩
        ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (∀ (u : ↥(TilingLattice Ci)), P.tile u =
            TileTranslation base (↑u : GaussianInt)) → (P.tile vIdx = V)) ) := by
  classical
  intro Ci base V v hvL hVeq vIdx P hPtile
  rw [hPtile]
  simpa [vIdx] using hVeq.symm

private theorem hidxNe :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (U : ProtoTile), ∀ (V : ProtoTile), (U ≠ V) → (∀ (u :
            GaussianInt), ∀ (huL : u ∈ TilingLattice Ci), ∀ (v : GaussianInt), ∀ (hvL : v ∈
            TilingLattice Ci),
        let uIdx : TilingLattice Ci := ⟨u, huL⟩
        let vIdx : TilingLattice Ci := ⟨v, hvL⟩
        ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (P.tile uIdx = U) → ((P.tile vIdx = V) →
            (uIdx ≠ vIdx))) ) := by
  classical
  intro Ci U V hUV u huL v hvL uIdx vIdx P hPU hPV heq
  apply hUV
  calc
    U = P.tile uIdx := hPU.symm
    _ = P.tile vIdx := congrArg P.tile heq
    _ = V := hPV

private theorem hedgeP :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (x : GaussianInt), ∀ (y : GaussianInt), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), ({x, y} ∈ FootprintEdges U ∩ FootprintEdges V) → (∀ (u : GaussianInt), ∀
            (huL : u ∈ TilingLattice Ci), ∀ (v : GaussianInt), ∀ (hvL : v ∈ TilingLattice Ci),
        let uIdx : TilingLattice Ci := ⟨u, huL⟩
        let vIdx : TilingLattice Ci := ⟨v, hvL⟩
        ∀ (P : PeriodicTileComplex ↥(TilingLattice Ci)), (P.tile uIdx = U) → ((P.tile vIdx = V) →
            ((FootprintEdges (P.tile uIdx) ∩ FootprintEdges (P.tile vIdx)).Nonempty))) ) := by
  classical
  intro Ci x y U V hedge u huL v hvL uIdx vIdx P hPU hPV
  refine ⟨{x, y}, ?_⟩
  rw [hPU, hPV]
  exact hedge

private theorem slope_defined :
    (by
      classical
      exact
        (BandCircle) → (∀ (Ci : BandCircle), (GaussianInt) → ((GaussianInt) → ((List GaussianInt)
            → ((PeriodicTileComplex ↥(TilingLattice Ci)) → (∀ (c : CircleCoordinates), ∀ (T :
            ProtoTile), ∀ (f : PartialOdometer), TileOdometer c T f → 1 < c.1 → ∃ p : ℝ × ℝ,
            PartialOdometerSlope f = some p))))) ) := by
  classical
  intro C0 Ci a b rest P c T f ho hc
  induction ho with
  | line w z hw hdom => omega
  | unit z w T f hT hdom htrans => omega
  | @decompose qd hqd S T hs f hT hsub hcells hfoot hcentroid hdom
      hvalue hcompat hslope ih =>
    have facts := ProperBandCurvatureStructure qd hqd
    have hp : ∃ i : Fin 3, 0 < (qd i.succ).1 := by
      by_cases h0 : 0 < (qd (0 : Fin 3).succ).1
      · exact ⟨0, h0⟩
      by_cases h1 : 0 < (qd (1 : Fin 3).succ).1
      · exact ⟨1, h1⟩
      by_cases h2 : 0 < (qd (2 : Fin 3).succ).1
      · exact ⟨2, h2⟩
      have n0 := facts.2.1 (0 : Fin 3)
      have n1 := facts.2.1 (1 : Fin 3)
      have z0 : (qd (0 : Fin 3).succ).1 = 0 := by omega
      have z1 : (qd (1 : Fin 3).succ).1 = 0 := by omega
      exact ((by decide : (0 : Fin 3) ≠ 1) (facts.2.2 0 1 z0 z1)).elim
    rcases hp with ⟨i, hi⟩
    rcases hslope i false with hz | ⟨p, pi, hp, hpi, hpr, hpi'⟩
    · omega
    · exact ⟨p, hp⟩

private theorem invStep :
    (by
      classical
      exact
        (BandCircle) → (∀ (Ci : BandCircle), ((1 : ℤ) < Ci.1.1.1) → ((GaussianInt) →
            ((GaussianInt) → ((List GaussianInt) → ((PeriodicTileComplex ↥(TilingLattice Ci)) → (
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        let centroidVec := fun T : ProtoTile =>
          ![(TileCentroid T).1, (TileCentroid T).2]
        let invariant := fun X : ProtoTile × PartialOdometer =>
          slopeVec X.2 - Matrix.mulVec (CircleMatrix Ci) (centroidVec X.1)
        let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
        ∀ A B : ProtoTile × PartialOdometer, LeftLatticeAdjacent Ci A.1 B.1 A.2 B.2 → invRel A
            B)))))) ) := by
  classical
  intro C0 Ci hlarge a b rest P slopeVec centroidVec invariant invRel A B hadj
  rcases hadj with ⟨_, _, p, p', hp, hp', hcase⟩
  rcases hcase with hunit | ⟨q, j, e, hq, hq0, hcent, hpRe, hpIm⟩
  · omega
  have hin := CircleMatrixIncomingVector Ci q hq.1 hq0 j
  let s : ℝ := if e = true then 1 else -1
  have hc0 : (TileCentroid B.1).1 - (TileCentroid A.1).1 =
      s * ((BandVectors.1 (q j.succ) (q 0)).re : ℝ) := by
    have hh := congrArg Prod.fst hcent
    change (TileCentroid B.1).1 - (TileCentroid A.1).1 =
      (if e = true then (1 : ℝ) else -1) *
        ((BandVectors.1 (q j.succ) (q 0)).re : ℝ) at hh
    simpa [s] using hh
  have hc1 : (TileCentroid B.1).2 - (TileCentroid A.1).2 =
      s * ((BandVectors.1 (q j.succ) (q 0)).im : ℝ) := by
    have hh := congrArg Prod.snd hcent
    change (TileCentroid B.1).2 - (TileCentroid A.1).2 =
      (if e = true then (1 : ℝ) else -1) *
        ((BandVectors.1 (q j.succ) (q 0)).im : ℝ) at hh
    simpa [s] using hh
  have hcentVec : centroidVec B.1 - centroidVec A.1 =
      s • ![((BandVectors.1 (q j.succ) (q 0)).re : ℝ),
        ((BandVectors.1 (q j.succ) (q 0)).im : ℝ)] := by
    ext n
    fin_cases n
    · simpa [centroidVec, s, smul_eq_mul] using hc0
    · simpa [centroidVec, s, smul_eq_mul] using hc1
  have hslopeVec : slopeVec B.2 - slopeVec A.2 =
      s • ![((BandVectors.2 (q j.succ) (q 0)).re : ℝ),
        ((BandVectors.2 (q j.succ) (q 0)).im : ℝ)] := by
    ext n
    fin_cases n <;> simp [slopeVec, hp, hp', hpRe, hpIm, s]
  have hinVec : Matrix.mulVec (CircleMatrix Ci)
      ![((BandVectors.1 (q j.succ) (q 0)).re : ℝ),
        ((BandVectors.1 (q j.succ) (q 0)).im : ℝ)] =
      ![((BandVectors.2 (q j.succ) (q 0)).re : ℝ),
        ((BandVectors.2 (q j.succ) (q 0)).im : ℝ)] := by
    simpa [Matrix.mulVec] using hin
  have hmain : Matrix.mulVec (CircleMatrix Ci)
      (centroidVec B.1 - centroidVec A.1) =
        slopeVec B.2 - slopeVec A.2 := by
    rw [hcentVec, Matrix.mulVec_smul, hinVec, hslopeVec]
  change invariant A = invariant B
  dsimp [invariant]
  ext n
  fin_cases n
  · have heq := congrFun hmain 0
    simp [slopeVec, centroidVec, hp, hp', Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at heq ⊢
    linear_combination heq
  · have heq := congrFun hmain 1
    simp [slopeVec, centroidVec, hp, hp', Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at heq ⊢
    linear_combination heq

private theorem hlenPre :
    (by
      classical
      exact
        (BandCircle) → (∀ (Ci : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀
            (Rminus : ProtoTile), ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (hs : List
            PartialOdometer), ∀ (hplus : PartialOdometer), (OdometerStringRespect Ci orientation
            base Rminus Rplus tiles hs) → ((GaussianInt) → ((GaussianInt) → ((List GaussianInt) →
            ((PeriodicTileComplex ↥(TilingLattice Ci)) → (∀ (preTiles : List ProtoTile), (tiles =
            preTiles ++ [Rplus]) → (∀ (preHs : List PartialOdometer), (hs = preHs ++ [hplus]) →
            (preTiles.length = preHs.length)))))))) ) := by
  classical
  intro C0 Ci orientation base Rminus Rplus tiles hs hplus hRespect a b rest P preTiles hpreTiles
      preHs hpreHs
  have hlen := (List.Forall₂.length_eq hRespect.2.1)
  rw [hpreTiles, hpreHs, List.length_append, List.length_singleton,
    List.length_append, List.length_singleton] at hlen
  omega

private theorem hzipLast :
    (by
      classical
      exact
        ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀
            (hplus : PartialOdometer), ∀ (preTiles : List ProtoTile), (tiles = preTiles ++
            [Rplus]) → (∀ (preHs : List PartialOdometer), (hs = preHs ++ [hplus]) →
            ((preTiles.length = preHs.length) → (tiles.zip hs = preTiles.zip preHs ++ [(Rplus,
            hplus)]))) ) := by
  classical
  intro Rplus tiles hs hplus preTiles hpreTiles preHs hpreHs hlenPre
  rw [hpreTiles, hpreHs, List.zip_append hlenPre]
  simp

private theorem hUzip' :
    (by
      classical
      exact
        ∀ (Rplus : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (hs : List PartialOdometer), ∀
            (hplus : PartialOdometer), ∀ (U : ProtoTile), ∀ (g : PartialOdometer), ((U, g) ∈
            tiles.zip hs) → (∀ (preTiles : List ProtoTile), ∀ (preHs : List PartialOdometer),
            (tiles.zip hs = preTiles.zip preHs ++ [(Rplus, hplus)]) → ((U, g) ∈ preTiles.zip
            preHs ++ [(Rplus, hplus)])) ) := by
  classical
  intro Rplus tiles hs hplus U g hUzip preTiles preHs hzipLast
  rw [← hzipLast]
  exact hUzip

private theorem hzipHead :
    (by
      classical
      exact
        ∀ (Rplus : ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (reverseHs : List
            PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (postTiles : List ProtoTile),
            (reverseTiles = Rplus :: postTiles) → (∀ (postHs : List PartialOdometer), (reverseHs
            = hplus :: postHs) → (reverseTiles.zip reverseHs = (Rplus, hplus) :: postTiles.zip
            postHs)) ) := by
  classical
  intro Rplus reverseTiles reverseHs hplus postTiles hpostTiles postHs hpostHs
  rw [hpostTiles, hpostHs]
  rfl

private theorem hVzip' :
    (by
      classical
      exact
        ∀ (Rplus : ProtoTile), ∀ (reverseTiles : List ProtoTile), ∀ (reverseHs : List
            PartialOdometer), ∀ (hplus : PartialOdometer), ∀ (V : ProtoTile), ∀ (k :
            PartialOdometer), ((V, k) ∈ reverseTiles.zip reverseHs) → (∀ (postTiles : List
            ProtoTile), ∀ (postHs : List PartialOdometer), (reverseTiles.zip reverseHs = (Rplus,
            hplus) :: postTiles.zip postHs) → ((V, k) ∈ (Rplus, hplus) :: postTiles.zip postHs))
            ) := by
  classical
  intro Rplus reverseTiles reverseHs hplus V k hVzip postTiles postHs hzipHead
  rw [← hzipHead]
  exact hVzip

private theorem hInvU :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (Rplus : ProtoTile), ∀ (hplus : PartialOdometer), ∀ (U :
            ProtoTile), ∀ (g : PartialOdometer),
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        let centroidVec := fun T : ProtoTile =>
          ![(TileCentroid T).1, (TileCentroid T).2]
        let invariant := fun X : ProtoTile × PartialOdometer =>
          slopeVec X.2 - Matrix.mulVec (CircleMatrix Ci) (centroidVec X.1)
        let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
        ∀ (preTiles : List ProtoTile), ∀ (preHs : List PartialOdometer), (List.Pairwise invRel
            (preTiles.zip preHs ++ [(Rplus, hplus)])) → (((U, g) ∈ preTiles.zip preHs ++ [(Rplus,
            hplus)]) → (invariant (Rplus, hplus) = invariant (U, g))) ) := by
  classical
  intro Ci Rplus hplus U g slopeVec centroidVec invariant invRel preTiles preHs hfirstPairwise
      hUzip'
  have h := hfirstPairwise.rel_getLast hUzip'
  simpa using h.symm

private theorem hInvV :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (Rplus : ProtoTile), ∀ (hplus : PartialOdometer), ∀ (V :
            ProtoTile), ∀ (k : PartialOdometer),
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        let centroidVec := fun T : ProtoTile =>
          ![(TileCentroid T).1, (TileCentroid T).2]
        let invariant := fun X : ProtoTile × PartialOdometer =>
          slopeVec X.2 - Matrix.mulVec (CircleMatrix Ci) (centroidVec X.1)
        let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
        ∀ (postTiles : List ProtoTile), ∀ (postHs : List PartialOdometer), (List.Pairwise invRel
            ((Rplus, hplus) :: postTiles.zip postHs)) → (((V, k) ∈ (Rplus, hplus) ::
            postTiles.zip postHs) → (invariant (Rplus, hplus) = invariant (V, k))) ) := by
  classical
  intro Ci Rplus hplus V k slopeVec centroidVec invariant invRel postTiles postHs
      hreversePairwise hVzip'
  have h := hreversePairwise.rel_head hVzip'
  simpa using h

private theorem hcentU :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (U : ProtoTile), ∀ (u : GaussianInt), (U = TileTranslation base
            u) → (TileCentroid U = ((TileCentroid base).1 + (u.re : ℝ), (TileCentroid base).2 +
            (u.im : ℝ))) ) := by
  classical
  intro base U u hUeq
  rw [hUeq, (TileTranslationFormulas base u).2.2.2.2.1]

private theorem hcentV :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (V : ProtoTile), ∀ (v : GaussianInt), (V = TileTranslation base
            v) → (TileCentroid V = ((TileCentroid base).1 + (v.re : ℝ), (TileCentroid base).2 +
            (v.im : ℝ))) ) := by
  classical
  intro base V v hVeq
  rw [hVeq, (TileTranslationFormulas base v).2.2.2.2.1]

private theorem hcentUV :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (u : GaussianInt), ∀ (v :
            GaussianInt), (TileCentroid U = ((TileCentroid base).1 + (u.re : ℝ), (TileCentroid
            base).2 + (u.im : ℝ))) → ((TileCentroid V = ((TileCentroid base).1 + (v.re : ℝ),
            (TileCentroid base).2 + (v.im : ℝ))) → (TileCentroid V - TileCentroid U =
            GaussianRealPoint (v - u))) ) := by
  classical
  intro base U V u v hcentU hcentV
  rw [hcentV, hcentU]
  ext <;> simp [GaussianRealPoint]

private theorem hdispSigned :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (u : GaussianInt), ∀ (huL
            : u ∈ TilingLattice Ci), ∀ (v : GaussianInt), ∀ (hvL : v ∈ TilingLattice Ci),
        let uIdx : TilingLattice Ci := ⟨u, huL⟩
        let vIdx : TilingLattice Ci := ⟨v, hvL⟩
        ∀ (j : Fin (3 : ℕ)), ((↑vIdx : GaussianInt) - (↑uIdx : GaussianInt) = BandVectors.1 (r
            j.succ) (r (0 : Fin (4 : ℕ))) ∨ (↑vIdx : GaussianInt) - (↑uIdx : GaussianInt) =
            -BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ)))) → (∃ e : Bool, v - u = (if e = true
            then BandVectors.1 (r j.succ) (r 0) else -BandVectors.1 (r j.succ) (r 0))) ) := by
  classical
  intro Ci r u huL v hvL uIdx vIdx j hdisp
  rcases hdisp with hpos | hneg
  · exact ⟨true, by simpa [uIdx, vIdx] using hpos⟩
  · exact ⟨false, by simpa [uIdx, vIdx] using hneg⟩

private theorem hcentSigned :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (u :
            GaussianInt), ∀ (v : GaussianInt), ∀ (j : Fin (3 : ℕ)), (TileCentroid V -
            TileCentroid U = GaussianRealPoint (v - u)) → (∀ (e : Bool), (v - u = if e = true
            then BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ))) else -BandVectors.1 (r j.succ) (r
            (0 : Fin (4 : ℕ)))) → (TileCentroid V - TileCentroid U = (if e = true then (1 : ℝ)
            else -1) • GaussianRealPoint (BandVectors.1 (r j.succ) (r 0)))) ) := by
  classical
  intro U V r u v j hcentUV e hdisp'
  rw [hcentUV, hdisp']
  cases e <;> simp [GaussianRealPoint]

private theorem hIncoming :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)),
            ((CircleMatrix Ci).mulVec ![(↑(BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ)))).re :
            ℝ), (↑(BandVectors.1 (r j.succ) (r (0 : Fin (4 : ℕ)))).im : ℝ)] = ![(↑(BandVectors.2
            (r j.succ) (r (0 : Fin (4 : ℕ)))).re : ℝ), (↑(BandVectors.2 (r j.succ) (r (0 : Fin (4
            : ℕ)))).im : ℝ)]) → (Matrix.mulVec (CircleMatrix Ci) ![((BandVectors.1 (r j.succ) (r
            0)).re : ℝ), ((BandVectors.1 (r j.succ) (r 0)).im : ℝ)] = ![((BandVectors.2 (r
            j.succ) (r 0)).re : ℝ), ((BandVectors.2 (r j.succ) (r 0)).im : ℝ)]) ) := by
  classical
  intro Ci r j hInRegular
  simpa [Matrix.mulVec] using hInRegular

private theorem hInvExpanded :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (g : PartialOdometer), ∀ (k
            : PartialOdometer), ∀ (pU : ℝ × ℝ), (PartialOdometerSlope g = some pU) → (∀ (pV : ℝ ×
            ℝ), (PartialOdometerSlope k = some pV) → (
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        let centroidVec := fun T : ProtoTile =>
          ![(TileCentroid T).1, (TileCentroid T).2]
        let invariant := fun X : ProtoTile × PartialOdometer =>
          slopeVec X.2 - Matrix.mulVec (CircleMatrix Ci) (centroidVec X.1)
        (invariant (U, g) = invariant (V, k)) → (slopeVec g - Matrix.mulVec (CircleMatrix Ci)
            ![(TileCentroid U).1, (TileCentroid U).2] = slopeVec k - Matrix.mulVec (CircleMatrix
            Ci) ![(TileCentroid V).1, (TileCentroid V).2]))) ) := by
  classical
  intro Ci U V g k pU hpU pV hpV slopeVec centroidVec invariant hInvUV
  simpa [invariant, slopeVec, centroidVec, hpU, hpV] using hInvUV

private theorem hmainUV :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (g : PartialOdometer), ∀ (k
            : PartialOdometer),
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        (slopeVec g - Matrix.mulVec (CircleMatrix Ci) ![(TileCentroid U).1, (TileCentroid U).2] =
            slopeVec k - Matrix.mulVec (CircleMatrix Ci) ![(TileCentroid V).1, (TileCentroid
            V).2]) → (Matrix.mulVec (CircleMatrix Ci) (![(TileCentroid V).1, (TileCentroid V).2]
            - ![(TileCentroid U).1, (TileCentroid U).2]) = slopeVec k - slopeVec g) ) := by
  classical
  intro Ci U V g k slopeVec hInvExpanded
  ext n
  fin_cases n
  · have heq := congrFun hInvExpanded 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at heq ⊢
    linear_combination heq
  · have heq := congrFun hInvExpanded 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at heq ⊢
    linear_combination heq

private theorem hcentVector :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin
            (3 : ℕ)), ∀ (e : Bool), (TileCentroid V - TileCentroid U = (if e = true then (1 : ℝ)
            else -1) • GaussianRealPoint (BandVectors.1 (r j.succ) (r 0))) → (![(TileCentroid
            V).1, (TileCentroid V).2] - ![(TileCentroid U).1, (TileCentroid U).2] = (if e = true
            then (1 : ℝ) else -1) • ![((BandVectors.1 (r j.succ) (r 0)).re : ℝ), ((BandVectors.1
            (r j.succ) (r 0)).im : ℝ)]) ) := by
  classical
  intro U V r j e hcentSigned
  have hh0 := congrArg Prod.fst hcentSigned
  have hh1 := congrArg Prod.snd hcentSigned
  change (TileCentroid V).1 - (TileCentroid U).1 =
    (if e = true then (1 : ℝ) else -1) *
      ((BandVectors.1 (r j.succ) (r 0)).re : ℝ) at hh0
  change (TileCentroid V).2 - (TileCentroid U).2 =
    (if e = true then (1 : ℝ) else -1) *
      ((BandVectors.1 (r j.succ) (r 0)).im : ℝ) at hh1
  ext n
  fin_cases n
  · simpa [Pi.smul_apply, smul_eq_mul] using hh0
  · simpa [Pi.smul_apply, smul_eq_mul] using hh1

private theorem hslopeVector :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (g : PartialOdometer), ∀ (k
            : PartialOdometer), ∀ (r : Fin (4 : ℕ) → CircleCoordinates), ∀ (j : Fin (3 : ℕ)),
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        ∀ (e : Bool), (Matrix.mulVec (CircleMatrix Ci) ![((BandVectors.1 (r j.succ) (r 0)).re :
            ℝ), ((BandVectors.1 (r j.succ) (r 0)).im : ℝ)] = ![((BandVectors.2 (r j.succ) (r
            0)).re : ℝ), ((BandVectors.2 (r j.succ) (r 0)).im : ℝ)]) → ((Matrix.mulVec
            (CircleMatrix Ci) (![(TileCentroid V).1, (TileCentroid V).2] - ![(TileCentroid U).1,
            (TileCentroid U).2]) = slopeVec k - slopeVec g) → ((![(TileCentroid V).1,
            (TileCentroid V).2] - ![(TileCentroid U).1, (TileCentroid U).2] = (if e = true then
            (1 : ℝ) else -1) • ![((BandVectors.1 (r j.succ) (r 0)).re : ℝ), ((BandVectors.1 (r
            j.succ) (r 0)).im : ℝ)]) → (slopeVec k - slopeVec g = (if e = true then (1 : ℝ) else
            -1) • ![((BandVectors.2 (r j.succ) (r 0)).re : ℝ), ((BandVectors.2 (r j.succ) (r
            0)).im : ℝ)]))) ) := by
  classical
  intro Ci U V g k r j slopeVec e hIncoming hmainUV hcentVector
  calc
    slopeVec k - slopeVec g = Matrix.mulVec (CircleMatrix Ci)
        (![(TileCentroid V).1, (TileCentroid V).2] -
          ![(TileCentroid U).1, (TileCentroid U).2]) := hmainUV.symm
    _ = Matrix.mulVec (CircleMatrix Ci) ((if e = true then (1 : ℝ) else -1) •
          ![((BandVectors.1 (r j.succ) (r 0)).re : ℝ),
            ((BandVectors.1 (r j.succ) (r 0)).im : ℝ)]) := by rw [hcentVector]
    _ = (if e = true then (1 : ℝ) else -1) •
          Matrix.mulVec (CircleMatrix Ci)
            ![((BandVectors.1 (r j.succ) (r 0)).re : ℝ),
              ((BandVectors.1 (r j.succ) (r 0)).im : ℝ)] := by
        rw [Matrix.mulVec_smul]
    _ = (if e = true then (1 : ℝ) else -1) •
          ![((BandVectors.2 (r j.succ) (r 0)).re : ℝ),
            ((BandVectors.2 (r j.succ) (r 0)).im : ℝ)] := by rw [hIncoming]

private theorem hLeft :
    (by
      classical
      exact
        ∀ (Ci : BandCircle), ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (g : PartialOdometer), ∀ (k
            : PartialOdometer), (TileOdometer Ci.1.1 U g) → ((TileOdometer Ci.1.1 V k) → (∀ (r :
            Fin (4 : ℕ) → CircleCoordinates), (r (0 : Fin (4 : ℕ)) = Ci.1.1) →
            ((ProperBandQuadruple r) → (∀ (j : Fin (3 : ℕ)), ∀ (pU : ℝ × ℝ),
            (PartialOdometerSlope g = some pU) → (∀ (pV : ℝ × ℝ), (PartialOdometerSlope k = some
            pV) → (
        let slopeVec := fun f : PartialOdometer =>
          let p := (PartialOdometerSlope f).getD (0, 0)
          ![p.1, p.2]
        ∀ (e : Bool), (TileCentroid V - TileCentroid U = (if e = true then (1 : ℝ) else -1) •
            GaussianRealPoint (BandVectors.1 (r j.succ) (r 0))) → ((slopeVec k - slopeVec g = (if
            e = true then (1 : ℝ) else -1) • ![((BandVectors.2 (r j.succ) (r 0)).re : ℝ),
            ((BandVectors.2 (r j.succ) (r 0)).im : ℝ)]) → (LeftLatticeAdjacent Ci U V g k))))))))
            ) := by
  classical
  intro Ci U V g k hUchildOdo hVchildOdo r hr0 hrproper j pU hpU pV hpV slopeVec e hcentSigned
      hslopeVector
  refine ⟨hUchildOdo, hVchildOdo, pU, pV, hpU, hpV,
    Or.inr ⟨r, j, e, hrproper, hr0, hcentSigned, ?_, ?_⟩⟩
  · have hh := congrFun hslopeVector 0
    simpa [slopeVec, hpU, hpV] using hh
  · have hh := congrFun hslopeVector 1
    simpa [slopeVec, hpU, hpV] using hh

end OpposingStarGeometry

theorem OpposingBoundaryStarLocalization
    (q : Fin 4 -> CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C0 Ci : BandCircle) (i : Fin 3)
    (hC0 : q 0 = C0.1.1) (hCi : q i.succ = Ci.1.1)
    (T0 T0' : ProtoTile) (h0 h0' : PartialOdometer)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C0 T0)
    (hsym : QuarterTurnSymmetric T0)
    (hO0 : TileOdometer C0.1.1 T0 h0)
    (hO0' : TileOdometer C0.1.1 T0' h0')
    (hlarge : 1 < Ci.1.1.1)
    (p0 p0' : Real × Real)
    (hs0 : PartialOdometerSlope h0 = some p0)
    (hs0' : PartialOdometerSlope h0' = some p0')
    (hcentroid : TileCentroid T0' - TileCentroid T0 =
      GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)))
    (hslope : p0' - p0 =
      GaussianRealPoint (BandVectors.2 (q i.succ) (q 0)))
    (x : GaussianInt) (hx0 : x ∈ h0.domain) (hx0' : x ∈ h0'.domain)
    (hstar : forall y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ ->
      y ∈ h0.domain ∨ y ∈ h0'.domain) :
    exists orientation : Bool, exists base Rminus Rplus : ProtoTile,
    exists tiles reverseTiles : List ProtoTile,
    exists hs reverseHs : List PartialOdometer,
    exists hminus hplus : PartialOdometer,
    exists path : List GaussianInt,
    exists U V : ProtoTile, exists g k : PartialOdometer,
      BoundaryString C0 Ci i orientation T0 base Rminus Rplus tiles /\
      TileString Ci orientation base Rplus Rminus reverseTiles /\
      OdometerStringRespect Ci orientation base Rminus Rplus tiles hs /\
      OdometerStringRespect Ci orientation base Rplus Rminus
        reverseTiles reverseHs /\
      hs.head? = some hminus /\ hs.getLast? = some hplus /\
      reverseHs.head? = some hplus /\ reverseHs.getLast? = some hminus /\
      path.Nodup /\ 2 <= path.length /\
      FootprintVertices T0 ∩ FootprintVertices T0' =
        (path.toFinset : Set GaussianInt) /\
      (forall e, e ∈ FootprintEdges T0 ∩ FootprintEdges T0' <->
        exists z w : GaussianInt, exists l1 l2 : List GaussianInt,
          path = l1 ++ z :: w :: l2 /\ e = {z, w}) /\
      x ∈ path /\
      U ∈ (tiles.drop 1).dropLast /\ (U, g) ∈ tiles.zip hs /\
      V ∈ (reverseTiles.drop 1).dropLast /\
        (V, k) ∈ reverseTiles.zip reverseHs /\
      TileOdometer Ci.1.1 U g /\ TileOdometer Ci.1.1 V k /\
      AncestorOdometer Ci.1.1 C0.1.1 U T0 g h0 /\
      AncestorOdometer Ci.1.1 C0.1.1 V T0' k h0' /\
      LeftLatticeAdjacent Ci U V g k /\
      x ∈ g.domain /\ x ∈ k.domain /\
      (forall y, y = x ∨ y = x + 1 ∨ y = x - 1 ∨
          y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ ->
        y ∈ g.domain ∨ y ∈ k.domain) /\
      Ci.1.1.1 < C0.1.1.1 := by
-- BODY
  classical
  have hex := OpposingBoundaryInterfaceExhaustion q cfg C0 Ci i hC0 hCi
    T0 T0' h0 h0' cert hsym hO0 hO0' hlarge p0 p0' hs0 hs0'
    hcentroid hslope
  rcases hex with ⟨orientation, base, Rminus, Rplus, tiles, reverseTiles,
    hs, reverseHs, hminus, hplus, pminus, pplus, path, hRest⟩
  rcases hRest with ⟨hBoundary, hRest⟩
  rcases hRest with ⟨hTileString, hRest⟩
  rcases hRest with ⟨hRespect, hRest⟩
  rcases hRest with ⟨hReverseRespect, hRest⟩
  rcases hRest with ⟨hhead, hRest⟩
  rcases hRest with ⟨hlast, hRest⟩
  rcases hRest with ⟨hreverseHead, hRest⟩
  rcases hRest with ⟨hreverseLast, hRest⟩
  rcases hRest with ⟨hOminus, hRest⟩
  rcases hRest with ⟨hOplus, hRest⟩
  rcases hRest with ⟨hsminus, hRest⟩
  rcases hRest with ⟨hsplus, hRest⟩
  rcases hRest with ⟨hminusSlope, hRest⟩
  rcases hRest with ⟨hplusSlope, hRest⟩
  rcases hRest with ⟨hTripleMinus, hRest⟩
  rcases hRest with ⟨hTriplePlus, hRest⟩
  rcases hRest with ⟨hpathNodup, hRest⟩
  rcases hRest with ⟨hpathLength, hRest⟩
  rcases hRest with ⟨hpathEnds, hRest⟩
  rcases hRest with ⟨hpathEndPlus, hRest⟩
  rcases hRest with ⟨hvertices, hRest⟩
  rcases hRest with ⟨hedges, hRest⟩
  rcases hRest with ⟨hboundaryOwners, hRest⟩
  have hcommonEdges := hRest
  have hdomain0 := PositiveCurvatureTileOdometerDomain C0.1.1 T0 h0 C0.2 hO0
  have hdomain0' := PositiveCurvatureTileOdometerDomain C0.1.1 T0' h0' C0.2 hO0'
  have hxPath := OpposingStarGeometry.hxPath T0 T0' x path hvertices (OpposingStarGeometry.hxT0
      T0 h0 x hx0 hdomain0) (OpposingStarGeometry.hxT0' T0' h0' x hx0' hdomain0')
  cases path with
  | nil => simp at hpathLength
  | cons a tail =>
    cases tail with
    | nil => simp at hpathLength
    | cons b rest =>
      obtain ⟨_, _, hstarClause⟩ := hcommonEdges a b [] rest rfl
      obtain ⟨y, U, V, g, k, hconsecutive, hUV, hedge, hUint, hUzip,
        hUancestor, hVint, hVzip, hVancestor, hownedCells⟩ :=
          hstarClause x hxPath hstar
      dsimp [AncestorOdometer] at hUancestor hVancestor
      have hUancestorKeep := hUancestor
      have hVancestorKeep := hVancestor
      rcases hUancestorKeep with ⟨hUodo, hUtile, hUdomEq, hUsubset, hUvalue⟩
      rcases hVancestorKeep with ⟨hVodo, hVtile, hVdomEq, hVsubset, hVvalue⟩
      have hUchildOdo : TileOdometer Ci.1.1 U g :=
        (List.forall₂_iff_zip.mp hRespect.2.1).2 hUzip
      have hVchildOdo : TileOdometer Ci.1.1 V k :=
        (List.forall₂_iff_zip.mp hReverseRespect.2.1).2 hVzip
      have hdomU := PositiveCurvatureTileOdometerDomain Ci.1.1 U g Ci.2 hUchildOdo
      have hdomV := PositiveCurvatureTileOdometerDomain Ci.1.1 V k Ci.2 hVchildOdo
      have cellCorner := OpposingStarGeometry.cellCorner
      have hxU : x ∈ FootprintVertices U := OpposingStarGeometry.hxU x U V hownedCells cellCorner
      have hxV : x ∈ FootprintVertices V := OpposingStarGeometry.hxV x U V hownedCells cellCorner
      have hxgSet : x ∈ (g.domain : Set GaussianInt) := by rw [hdomU]; exact hxU
      have hxkSet : x ∈ (k.domain : Set GaussianInt) := by rw [hdomV]; exact hxV
      have hxg : x ∈ g.domain := by simpa using hxgSet
      have hxk : x ∈ k.domain := by simpa using hxkSet
      have hcover := OpposingStarGeometry.hcover x U V g k hownedCells cellCorner hxg hxk
          (OpposingStarGeometry.vertexToG U g hdomU) (OpposingStarGeometry.vertexToK V k hdomV)
      have hcurvature := OpposingStarGeometry.hcurvature q cfg C0 Ci i hC0 hCi
      have hgenealogy := BandGenealogy Ci
      obtain hunit | ⟨r, hrsemi, hr0, hrless, _⟩ := hgenealogy
      · omega
      have hrproper : ProperBandQuadruple r :=
        ⟨hrsemi, by simpa [hr0] using hrless⟩
      have hUfamily : U ∈ RegularTileFamily base (TilingLattice Ci) :=
        hRespect.1.2.2.2.2.1 U (List.mem_of_mem_drop (List.mem_of_mem_dropLast hUint))
      have hVfamily : V ∈ RegularTileFamily base (TilingLattice Ci) :=
        hTileString.2.2.2.2.1 V (List.mem_of_mem_drop (List.mem_of_mem_dropLast hVint))
      obtain ⟨u, huL, hUeq⟩ := hUfamily
      obtain ⟨v, hvL, hVeq⟩ := hVfamily
      let uIdx : TilingLattice Ci := ⟨u, huL⟩
      let vIdx : TilingLattice Ci := ⟨v, hvL⟩
      obtain ⟨P, hPlattice, hPtile, hPadj, hPposition, _, _, _, _⟩ :=
        BandRegularTranslatePeriodicComplex Ci r hrproper hr0 base
          (by simpa [hr0] using hRespect.1.1)
      have hPU := OpposingStarGeometry.hPU Ci base U u huL hUeq P hPtile
      have hPV := OpposingStarGeometry.hPV Ci base V v hvL hVeq P hPtile
      have hadjP := (PeriodicTileIntersectionClassification P).1 uIdx vIdx
          (OpposingStarGeometry.hidxNe Ci U V hUV u huL v hvL P hPU hPV)
      have hadjIndex : P.plane.adjacent uIdx vIdx := hadjP.1.mp (OpposingStarGeometry.hedgeP Ci x
          y U V hedge u huL v hvL P hPU hPV)
      obtain ⟨j, hdisp⟩ := (hPadj uIdx vIdx).mp hadjIndex
      have slope_defined := OpposingStarGeometry.slope_defined C0 Ci a b rest P
      obtain ⟨pU, hpU⟩ := slope_defined Ci.1.1 U g hUchildOdo (by omega)
      obtain ⟨pV, hpV⟩ := slope_defined Ci.1.1 V k hVchildOdo (by omega)
      let slopeVec := fun f : PartialOdometer =>
        let p := (PartialOdometerSlope f).getD (0, 0)
        ![p.1, p.2]
      let centroidVec := fun T : ProtoTile =>
        ![(TileCentroid T).1, (TileCentroid T).2]
      let invariant := fun X : ProtoTile × PartialOdometer =>
        slopeVec X.2 - Matrix.mulVec (CircleMatrix Ci) (centroidVec X.1)
      let invRel := fun X Y : ProtoTile × PartialOdometer => invariant X = invariant Y
      have invStep := OpposingStarGeometry.invStep C0 Ci hlarge a b rest P
      have hfirstInvChain : List.IsChain invRel (tiles.zip hs) :=
        hRespect.2.2.imp (fun A B hadj => invStep A B hadj)
      have hreverseInvChain : List.IsChain invRel (reverseTiles.zip reverseHs) :=
        hReverseRespect.2.2.imp (fun A B hadj => invStep A B hadj)
      let : Trans invRel invRel invRel := ⟨by
        intro a b c hab hbc
        exact hab.trans hbc⟩
      have hfirstPairwise : (tiles.zip hs).Pairwise invRel :=
        (List.isChain_iff_pairwise).mp hfirstInvChain
      have hreversePairwise : (reverseTiles.zip reverseHs).Pairwise invRel :=
        (List.isChain_iff_pairwise).mp hreverseInvChain
      obtain ⟨preTiles, hpreTiles⟩ :=
        List.getLast?_eq_some_iff.mp hRespect.1.2.2.1
      obtain ⟨preHs, hpreHs⟩ := List.getLast?_eq_some_iff.mp hlast
      have hzipLast : tiles.zip hs = preTiles.zip preHs ++ [(Rplus, hplus)] :=
          OpposingStarGeometry.hzipLast Rplus tiles hs hplus preTiles hpreTiles preHs hpreHs
          (OpposingStarGeometry.hlenPre C0 Ci orientation base Rminus Rplus tiles hs hplus
          hRespect a b rest P preTiles hpreTiles preHs hpreHs)
      have hUzip' := OpposingStarGeometry.hUzip' Rplus tiles hs hplus U g hUzip preTiles preHs
          hzipLast
      obtain ⟨postTiles, hpostTiles⟩ :=
        List.head?_eq_some_iff.mp hTileString.2.1
      obtain ⟨postHs, hpostHs⟩ := List.head?_eq_some_iff.mp hreverseHead
      have hzipHead : reverseTiles.zip reverseHs =
          (Rplus, hplus) :: postTiles.zip postHs := OpposingStarGeometry.hzipHead Rplus
              reverseTiles reverseHs hplus postTiles hpostTiles postHs hpostHs
      rw [hzipLast] at hfirstPairwise
      rw [hzipHead] at hreversePairwise
      have hInvUV : invariant (U, g) = invariant (V, k) := (OpposingStarGeometry.hInvU Ci Rplus
          hplus U g preTiles preHs hfirstPairwise hUzip').symm.trans (OpposingStarGeometry.hInvV
          Ci Rplus hplus V k postTiles postHs hreversePairwise (OpposingStarGeometry.hVzip' Rplus
          reverseTiles reverseHs hplus V k hVzip postTiles postHs hzipHead))
      have hcentUV := OpposingStarGeometry.hcentUV base U V u v (OpposingStarGeometry.hcentU base
          U u hUeq) (OpposingStarGeometry.hcentV base V v hVeq)
      have hdispSigned := OpposingStarGeometry.hdispSigned Ci r u huL v hvL j hdisp
      obtain ⟨e, hdisp'⟩ := hdispSigned
      have hcentSigned := OpposingStarGeometry.hcentSigned U V r u v j hcentUV e hdisp'
      have hInRegular := CircleMatrixIncomingVector Ci r hrsemi hr0 j
      refine ⟨orientation, base, Rminus, Rplus, tiles, reverseTiles, hs,
        reverseHs, hminus, hplus, a :: b :: rest, U, V, g, k, ?_⟩
      refine ⟨hBoundary, hTileString, hRespect, hReverseRespect, hhead,
        hlast, hreverseHead, hreverseLast, hpathNodup, hpathLength,
        hvertices, hedges, hxPath, hUint, hUzip, hVint, hVzip,
        hUchildOdo, hVchildOdo, hUancestor, hVancestor, (OpposingStarGeometry.hLeft Ci U V g k
            hUchildOdo hVchildOdo r hr0 hrproper j pU hpU pV hpV e hcentSigned
            (OpposingStarGeometry.hslopeVector Ci U V g k r j e (OpposingStarGeometry.hIncoming
            Ci r j hInRegular) (OpposingStarGeometry.hmainUV Ci U V g k
            (OpposingStarGeometry.hInvExpanded Ci U V g k pU hpU pV hpV hInvUV))
            (OpposingStarGeometry.hcentVector U V r j e hcentSigned))), hxg, hxk,
        hcover, hcurvature⟩

end ApollonianSuperharmonic

end
