/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandPeriodicSuperharmonicity
public import LeanPool.ApollonianSuperharmonic.BandGenealogy
public import LeanPool.ApollonianSuperharmonic.PeriodicBoundaryWebLaplacian
public import LeanPool.ApollonianSuperharmonic.PeriodicOdometerIndicatorRigidity
public import LeanPool.ApollonianSuperharmonic.SufficientBoundedMaximality
public import LeanPool.ApollonianSuperharmonic.TilingLattice
public import LeanPool.ApollonianSuperharmonic.TilingLatticeBasis

-- [TABLET NODE: BandOdometerMaximality]

/-!
# BandOdometerMaximality

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandOdometerMaximality (C : BandCircle)
    (T : ProtoTile) (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hT : BandPrototile C.1.1 T) (hlat : LatticeTile T)
    (hodo : TileOdometer C.1.1 T h)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hext : GlobalOdometerExtends g h)
    (htile : ExactTileTiling (RegularTileFamily T (TilingLattice C)))
    (hrep : IntegerSuperharmonicRepresentative (CircleMatrix C) g)
    (hcocycle : ∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
      Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
        ![(a.re : ℝ), (a.im : ℝ)] ∧
      ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) :
    ∀ f : IntegerLatticeFunction, (∀ x, g x ≤ f x) →
      (∀ x, FourNeighborLaplacian f x ≤ 1) → BoundedDifference f g := by
-- BODY
  have hbound : ∀ x, FourNeighborLaplacian g x ≤ 1 := hrep.2.2
  have lapshift : ∀ w : GaussianInt, w ∈ TilingLattice C →
      ∀ x, FourNeighborLaplacian g (x + w) = FourNeighborLaplacian g x := by
    intro w hw x
    obtain ⟨a, ha, hg⟩ := hcocycle w hw
    rw [FourNeighborLaplacian, FourNeighborLaplacian]
    rw [show x + w + 1 = (x + 1) + w by abel,
      show x + w - 1 = (x - 1) + w by abel,
      show x + w + ⟨0, 1⟩ = (x + ⟨0, 1⟩) + w by abel,
      show x + w - ⟨0, 1⟩ = (x - ⟨0, 1⟩) + w by abel]
    rw [hg, hg, hg, hg, hg]
    simp
    ring
  have hweb := PeriodicBoundaryWebLaplacian C T h g hT hodo hext hcocycle
  have hrigid := PeriodicOdometerIndicatorRigidity C T h g hT hlat hodo hdom
    hext htile lapshift hweb
  have periods : ∃ u v : GaussianInt,
      u.re * v.im - u.im * v.re ≠ 0 ∧
      (∀ x, FourNeighborLaplacian g (x + u) = FourNeighborLaplacian g x) ∧
      ∀ x, FourNeighborLaplacian g (x + v) = FourNeighborLaplacian g x := by
    by_cases hunit : C.1.1.1 = 1
    · refine ⟨1, ⟨0, 1⟩, ?_, ?_, ?_⟩
      · norm_num
      · intro x
        apply lapshift 1 (by simp [TilingLattice, hunit])
      · intro x
        apply lapshift ⟨0, 1⟩ (by simp [TilingLattice, hunit])
    · obtain ⟨q, hsemi, hqC, hlt, huniq⟩ :=
        Or.resolve_left (BandGenealogy C) hunit
      have hproper : ProperBandQuadruple q := ⟨hsemi, by
        intro j
        simpa [hqC] using hlt j⟩
      have basis := TilingLatticeBasis C q hproper hqC
      let a : GaussianInt := BandVectors.1 (q 1) (q 0)
      let b : GaussianInt := BandVectors.1 (q 2) (q 0)
      have ha : a ∈ TilingLattice C := by simpa [a] using basis.1
      have hb : b ∈ TilingLattice C := by simpa [b] using basis.2.1
      have hu : ∀ m n : Int × Int,
          (m.1 : GaussianInt) * a + (m.2 : GaussianInt) * b =
            (n.1 : GaussianInt) * a + (n.2 : GaussianInt) * b → m = n := by
        intro m n hmn
        let z : GaussianInt := (m.1 : GaussianInt) * a + (m.2 : GaussianInt) * b
        have hzmem : z ∈ TilingLattice C := by
          apply (TilingLattice C).add_mem
          · simpa [z] using (TilingLattice C).zsmul_mem ha m.1
          · simpa [z] using (TilingLattice C).zsmul_mem hb m.2
        obtain ⟨w, hw, hwu⟩ := basis.2.2.1 (⟨z, hzmem⟩ : TilingLattice C)
        apply (hwu m ?_).trans (hwu n ?_).symm
        · rfl
        · simpa [a, b, z] using hmn.symm
      have determinant : a.re * b.im - a.im * b.re ≠ 0 := by
        intro hz
        have ha0 : a ≠ 0 := by
          intro ha0
          have he := hu (1, 0) (0, 0)
          apply (by norm_num : (1 : Int) ≠ 0)
          have := he (by simp [ha0])
          exact congrArg Prod.fst this
        by_cases him : a.im = 0 ∧ b.im = 0
        · have hre : b.re * a.re - a.re * b.re = 0 := by
            linarith [hz]
          have he := hu (b.re, -a.re) (0, 0)
          have hzero : (b.re : GaussianInt) * a +
              ((-a.re : Int) : GaussianInt) * b = 0 := by
            ext <;> simp [him.1, him.2]; ring
          have hpair := he (by simpa using hzero)
          have hbre : b.re = 0 := congrArg Prod.fst hpair
          have hare : a.re = 0 := by
            have hh := congrArg Prod.snd hpair
            simpa using neg_eq_zero.mp hh
          apply ha0
          ext <;> simp [hare, him.1]
        · have he := hu (b.im, -a.im) (0, 0)
          have hzero : (b.im : GaussianInt) * a +
              ((-a.im : Int) : GaussianInt) * b = 0 := by
            ext <;> simp <;> linarith [hz]
          have hpair := he (by simpa using hzero)
          have hi1 : b.im = 0 := congrArg Prod.fst hpair
          have hi2 : a.im = 0 := by
            have hh := congrArg Prod.snd hpair
            simpa using neg_eq_zero.mp hh
          exact him ⟨hi2, hi1⟩
      exact ⟨a, b, determinant, lapshift a ha, lapshift b hb⟩
  exact SufficientBoundedMaximality g hbound periods hrigid

end ApollonianSuperharmonic

end
