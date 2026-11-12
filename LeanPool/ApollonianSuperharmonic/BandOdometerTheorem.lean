/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init


public import LeanPool.ApollonianSuperharmonic.BandLatticeEquality
public import LeanPool.ApollonianSuperharmonic.TileOdometerDomain
public import LeanPool.ApollonianSuperharmonic.BandOdometerMaximality
public import LeanPool.ApollonianSuperharmonic.BandPeriodicSuperharmonicity

-- [TABLET NODE: BandOdometerTheorem]

/-!
# BandOdometerTheorem

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOdometerTheorem : ∀ C : BandCircle,
    ∃ g : IntegerLatticeFunction,
      IntegerSuperharmonicRepresentative (CircleMatrix C) g ∧
      (∀ v, v ∈ IntegralityLattice C → ∃ a : GaussianInt,
        Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
          ![(a.re : ℝ), (a.im : ℝ)] ∧
        ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) ∧
      ∀ f : IntegerLatticeFunction, (∀ x, g x ≤ f x) →
        (∀ x, FourNeighborLaplacian f x ≤ 1) → BoundedDifference f g := by
-- BODY
  intro C
  obtain ⟨T, h, g, hT, hodo, hext, hcocycle, hremainder⟩ := BandPeriodicOdometer C
  have hdom : (h.domain : Set GaussianInt) = FootprintVertices T := by
    exact TileOdometerDomain _ _ _ hodo
  classical
  have tiling_data : LatticeTile T ∧
      ExactTileTiling (RegularTileFamily T (TilingLattice C)) := by
    generalize coordinate : C.1.1 = c at hT
    cases hT with
    | line w x hw =>
        exfalso
        have hc := C.2
        simp_all []
    | unit z x anchor =>
        have hc : C.1.1.1 = 1 := by
          have := congrArg Prod.fst coordinate
          simpa using this
        let square : ProtoTile := ⟨{0}, 0⟩
        have square_disk : LatticeTile square := by
          have hunit : FordTile 1 = square := by
            have zero_coordinates : (⟨0, 0⟩ : GaussianInt) = 0 := rfl
            simp [square, FordTile, FordCellDomain, zero_coordinates]
          simpa only [hunit] using (FordTileGeometry 1 (by omega)).1
        have translated := (TileDiskAreaCovariance square x).1.mp square_disk
        have identify : ({ cells := {x}, anchor := x } : ProtoTile) =
            TileTranslation square x := by
          simp [square, TileTranslation, GaussianTranslation]
        refine ⟨by
          simpa [LatticeTile, TileRealization, square, TileTranslation,
            GaussianTranslation] using translated, ?_⟩
        have lattice : TilingLattice C = ⊤ := by simp [TilingLattice, hc]
        unfold ExactTileTiling RegularTileFamily
        rw [lattice]
        constructor
        · intro V hV
          rcases hV with ⟨u, hu, rfl⟩
          have hd := (TileDiskAreaCovariance (TileTranslation square x) u).1.mp
            (by simpa [identify] using translated)
          simpa [LatticeTile, TileRealization, square, TileTranslation,
            GaussianTranslation] using hd
        · intro y
          refine ⟨{ cells := {x + (y - x)}, anchor := anchor + (y - x)}, ?_, ?_, ?_⟩
          · simp only [TileTranslation, GaussianTranslation]
            refine ⟨(y : GaussianInt) - x, ?_⟩
            constructor
            · simp
            · simp [GaussianTranslation]
          · simp [sub_eq_add_neg]
          · intro V hV hy
            rcases hV with ⟨a, ha, rfl⟩
            simp only [TileTranslation, Finset.image_singleton, GaussianTranslation,
                Finset.mem_singleton, add_sub_cancel, ProtoTile.mk.injEq,
                Finset.singleton_inj, add_right_inj] at hy ⊢
            obtain rfl := hy
            constructor
            · rfl
            · simp []
    | @decompose q hq S U hS hcells' hfoot' hcentroid' =>
        have hqC : q 0 = C.1.1 := by simp [coordinate]
        have hparent : BandPrototile (q 0) T := by
          exact BandPrototile.decompose hq hS hcells' hfoot' hcentroid'
        obtain ⟨hlat, harea, hcomplements, hsym, hT3, hT4, hT5, hT6⟩ :=
          BandTileSimultaneousInduction q hq T hparent
        obtain ⟨htile, hcard⟩ :=
          BandTileTopologyApplication C q hq hqC T hparent
        exact ⟨hlat, htile⟩
  have hrep : IntegerSuperharmonicRepresentative (CircleMatrix C) g :=
    BandPeriodicSuperharmonicity C T h g hT hodo hext hcocycle hremainder
  refine ⟨g, hrep, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ TilingLattice C := by
      rw [← BandLatticeEquality C]
      exact hv
    exact hcocycle v hv'
  · intro f hfg hlf
    exact BandOdometerMaximality C T h g hT tiling_data.1 hodo hdom hext
      tiling_data.2 hrep hcocycle f hfg hlf

end ApollonianSuperharmonic

end
