/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicRepresentative
public import LeanPool.ApollonianSuperharmonic.IntegerLaplacianCastBridge
public import LeanPool.ApollonianSuperharmonic.RealLaplacianContactComparison
public import Mathlib.Order.Int.LeastGreatest
public import Mathlib.Algebra.BigOperators.Fin

-- [TABLET NODE: TranslatedMinimumEnvelope]

/-!
# TranslatedMinimumEnvelope

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem TranslatedMinimumEnvelope
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (b : Fin 2 -> Real) (u : IntegerLatticeFunction)
    (hulap : forall x, FourNeighborLaplacian u x <= 1)
    (hulower : forall x, LatticeQuadraticForm A x +
      dotProduct b ![(x.re : Real), (x.im : Real)] <= (u x : Real)) :
    exists F : GaussianInt -> IntegerLatticeFunction,
      exists g : IntegerLatticeFunction,
        (forall z x,
          F z x = u (x + z) -
            Int.floor (LatticeQuadraticForm A z +
              dotProduct b ![(z.re : Real), (z.im : Real)]) -
            Int.floor ((Matrix.mulVec A
              ![(z.re : Real), (z.im : Real)]) 0 + b 0) * x.re -
            Int.floor ((Matrix.mulVec A
              ![(z.re : Real), (z.im : Real)]) 1 + b 1) * x.im) /\
        (forall z x, FourNeighborLaplacian (F z) x <= 1) /\
        (forall x, (forall z, g x <= F z x) /\ exists z, g x = F z x) /\
        (forall x,
          LatticeQuadraticForm A x - ((abs x.re + abs x.im : Int) : Real) <=
            (g x : Real) /\
          (g x : Real) <= LatticeQuadraticForm A x + (u 0 : Real) + 1 +
            ((abs x.re + abs x.im : Int) : Real)) /\
        IntegerSuperharmonicRepresentative A g := by
-- BODY
  classical
  let c (z : GaussianInt) : Real := LatticeQuadraticForm A z +
    dotProduct b ![(z.re : Real), (z.im : Real)]
  let a (z : GaussianInt) (j : Fin 2) : Real :=
    (Matrix.mulVec A ![(z.re : Real), (z.im : Real)]) j + b j
  let F (z x : GaussianInt) : Int :=
    u (x + z) - Int.floor (c z) - Int.floor (a z 0) * x.re -
      Int.floor (a z 1) * x.im
  let r (z : GaussianInt) (j : Fin 2) : Real := a z j - (Int.floor (a z j) : Real)
  have hexpand (x z : GaussianInt) :
      LatticeQuadraticForm A (x + z) +
          dotProduct b ![((x + z).re : Real), ((x + z).im : Real)] =
        LatticeQuadraticForm A x + c z +
          a z 0 * (x.re : Real) + a z 1 * (x.im : Real) := by
    dsimp [c, a]
    simp [LatticeQuadraticForm, Matrix.mulVec, dotProduct, hA.apply 0 1]
    ring
  have hcast (z x : GaussianInt) :
      (F z x : Real) = (u (x + z) : Real) - (Int.floor (c z) : Real) -
        (Int.floor (a z 0) : Real) * (x.re : Real) -
        (Int.floor (a z 1) : Real) * (x.im : Real) := by
    simp only [F, Int.cast_sub, Int.cast_mul]
  have hrem (t : Real) : 0 <= t - (Int.floor t : Real) ∧
      t - (Int.floor t : Real) <= 1 := by
    constructor
    · linarith [Int.floor_le t]
    · linarith [Int.lt_floor_add_one t]
  have hmul (s t : Real) (hs : 0 <= s) (hs' : s <= 1) :
      -abs t <= s * t ∧ s * t <= abs t := by
    constructor
    · have h := mul_le_mul_of_nonneg_left (neg_le_abs t) hs
      have h' := mul_le_mul_of_nonneg_right hs' (abs_nonneg t)
      nlinarith
    · have h := mul_le_mul_of_nonneg_left (le_abs_self t) hs
      have h' := mul_le_mul_of_nonneg_right hs' (abs_nonneg t)
      nlinarith
  have hlower (z x : GaussianInt) :
      LatticeQuadraticForm A x - ((abs x.re + abs x.im : Int) : Real) <=
        (F z x : Real) := by
    have hu := hulower (x + z)
    rw [hexpand x z] at hu
    have hr0 := (hrem (c z)).1
    have hrx := (hmul (r z 0) (x.re : Real)
      (hrem (a z 0)).1 (hrem (a z 0)).2).1
    have hry := (hmul (r z 1) (x.im : Real)
      (hrem (a z 1)).1 (hrem (a z 1)).2).1
    dsimp only [r] at hrx hry
    rw [Int.cast_add, Int.cast_abs, Int.cast_abs]
    nlinarith [hcast z x]
  have hupper (x : GaussianInt) :
      (F (-x) x : Real) <= LatticeQuadraticForm A x + (u 0 : Real) + 1 +
        ((abs x.re + abs x.im : Int) : Real) := by
    have he := hexpand x (-x)
    have hzero : LatticeQuadraticForm A 0 +
        dotProduct b ![((0 : GaussianInt).re : Real), ((0 : GaussianInt).im : Real)] = 0 := by
      simp [LatticeQuadraticForm, Matrix.mulVec, dotProduct]
    rw [add_neg_cancel, hzero] at he
    have hc := hcast (-x) x
    rw [add_neg_cancel] at hc
    have hr0 := (hrem (c (-x))).2
    have hrx := (hmul (r (-x) 0) (x.re : Real)
      (hrem (a (-x) 0)).1 (hrem (a (-x) 0)).2).2
    have hry := (hmul (r (-x) 1) (x.im : Real)
      (hrem (a (-x) 1)).1 (hrem (a (-x) 1)).2).2
    dsimp only [r] at hrx hry
    rw [Int.cast_add, Int.cast_abs, Int.cast_abs]
    nlinarith
  have hFlap (z x : GaussianInt) : FourNeighborLaplacian (F z) x <= 1 := by
    have he : FourNeighborLaplacian (F z) x = FourNeighborLaplacian u (x + z) := by
      simp only [FourNeighborLaplacian, F]
      rw [show (x + 1) + z = (x + z) + 1 by abel,
        show (x - 1) + z = (x + z) - 1 by abel,
        show (x + ⟨0, 1⟩) + z = (x + z) + ⟨0, 1⟩ by abel,
        show (x - ⟨0, 1⟩) + z = (x + z) - ⟨0, 1⟩ by abel]
      simp [sub_eq_add_neg]
      ring
    rw [he]
    exact hulap (x + z)
  have hminimum (x : GaussianInt) :
      exists m : Int, (exists z, F z x = m) ∧
        forall n : Int, (exists z, F z x = n) -> m <= n := by
    apply Int.exists_least_of_bdd
    · refine ⟨Int.floor (LatticeQuadraticForm A x -
        ((abs x.re + abs x.im : Int) : Real)), ?_⟩
      rintro n ⟨z, rfl⟩
      apply (Int.cast_le (R := Real)).mp
      exact (Int.floor_le _).trans (hlower z x)
    · exact ⟨F 0 x, 0, rfl⟩
  let g (x : GaussianInt) : Int := Classical.choose (hminimum x)
  have hmin (x : GaussianInt) :
      (forall z, g x <= F z x) ∧ exists z, g x = F z x := by
    have hs := Classical.choose_spec (hminimum x)
    constructor
    · intro z
      exact hs.2 (F z x) ⟨z, rfl⟩
    · obtain ⟨z, hz⟩ := hs.1
      exact ⟨z, hz.symm⟩
  have hbounds (x : GaussianInt) :
      LatticeQuadraticForm A x - ((abs x.re + abs x.im : Int) : Real) <=
          (g x : Real) ∧
        (g x : Real) <= LatticeQuadraticForm A x + (u 0 : Real) + 1 +
          ((abs x.re + abs x.im : Int) : Real) := by
    constructor
    · obtain ⟨z, hz⟩ := (hmin x).2
      rw [hz]
      exact hlower z x
    · have hm : (g x : Real) <= (F (-x) x : Real) :=
        Int.cast_le.mpr ((hmin x).1 (-x))
      exact hm.trans (hupper x)
  have hglap (x : GaussianInt) : FourNeighborLaplacian g x <= 1 := by
    obtain ⟨z, hz⟩ := (hmin x).2
    have hc := RealLaplacianContactComparison.1
      (fun y => (g y : Real)) (fun y => (F z y : Real)) x
      (congrArg (fun n : Int => (n : Real)) hz) (by
        intro y hy
        exact Int.cast_le.mpr ((hmin y).1 z))
    rw [IntegerLaplacianCastBridge g x, IntegerLaplacianCastBridge (F z) x] at hc
    exact (Int.cast_le.mp hc).trans (hFlap z x)
  let K : Real := abs ((u 0 : Real) + 1)
  have habs (x : GaussianInt) :
      abs ((g x : Real) - LatticeQuadraticForm A x) <=
        K + abs (x.re : Real) + abs (x.im : Real) := by
    have hb := hbounds x
    rw [Int.cast_add, Int.cast_abs, Int.cast_abs] at hb
    apply abs_le.mpr
    constructor
    · have hK : 0 <= K := abs_nonneg _
      linarith [hb.1]
    · have hK : (u 0 : Real) + 1 <= K := le_abs_self _
      linarith [hb.2]
  have hgrowth : QuadraticGrowthAtInfinity A g := by
    intro eps heps
    have hlinear (t : Real) : abs t <= eps * t ^ 2 / 4 + 1 / eps := by
      apply (mul_le_mul_iff_of_pos_left heps).mp
      have hcancel : eps * (1 / eps) = 1 := by field_simp
      rw [mul_add, hcancel]
      have hs := sq_nonneg (eps * abs t - 2)
      rw [sub_sq, mul_pow, sq_abs] at hs
      nlinarith only [hs]
    refine ⟨2 * (K + 2 / eps) / eps, ?_⟩
    intro x hx
    have hcancel : eps * (2 * (K + 2 / eps) / eps) = 2 * (K + 2 / eps) := by
      field_simp
    have ht := mul_le_mul_of_nonneg_left hx heps.le
    rw [hcancel] at ht
    have hnonneg : 0 <= eps * ((x.re : Real) ^ 2 + (x.im : Real) ^ 2) :=
      mul_nonneg heps.le (add_nonneg (sq_nonneg _) (sq_nonneg _))
    calc
      abs ((g x : Real) - LatticeQuadraticForm A x) <=
          K + abs (x.re : Real) + abs (x.im : Real) := habs x
      _ <= eps * ((x.re : Real) ^ 2 + (x.im : Real) ^ 2) := by
        have hre := hlinear (x.re : Real)
        have him := hlinear (x.im : Real)
        rw [show 2 / eps = 2 * (1 / eps) by ring] at ht
        nlinarith only [ht, hnonneg, hre, him]
  exact ⟨F, g, (fun _ _ => rfl), hFlap, hmin, hbounds, hA, hgrowth, hglap⟩

end ApollonianSuperharmonic

end
