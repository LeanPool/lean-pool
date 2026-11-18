/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import Mathlib.Order.Int.LeastGreatest

public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.IntegerLaplacianCastBridge
public import LeanPool.ApollonianSuperharmonic.LatticeQuadraticForm
public import LeanPool.ApollonianSuperharmonic.RealLaplacianContactComparison
public import LeanPool.ApollonianSuperharmonic.P5667T1RoundedSupportingSlope

-- [TABLET NODE: PSDQuadraticIntegerApproximation]

/-!
# PSDQuadraticIntegerApproximation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PSDQuadraticIntegerApproximation
    (A : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (hpsd : A.PosSemidef) :
    exists g : IntegerLatticeFunction,
      (forall p : GaussianInt,
        (forall K : Int, exists y : GaussianInt,
          Int.floor (LatticeQuadraticForm A y +
              ((abs y.re + abs y.im : Int) : Real)) -
              p.re * y.re - p.im * y.im <= K) ∨
        exists m : Int,
          (forall y : GaussianInt,
            m <= Int.floor (LatticeQuadraticForm A y +
                ((abs y.re + abs y.im : Int) : Real)) -
                p.re * y.re - p.im * y.im) /\
          (exists y : GaussianInt,
            m = Int.floor (LatticeQuadraticForm A y +
                ((abs y.re + abs y.im : Int) : Real)) -
                p.re * y.re - p.im * y.im)) /\
      (forall x : GaussianInt, exists p : GaussianInt, exists m : Int,
        (forall y : GaussianInt,
          m <= Int.floor (LatticeQuadraticForm A y +
              ((abs y.re + abs y.im : Int) : Real)) -
              p.re * y.re - p.im * y.im) /\
        (exists y : GaussianInt,
          m = Int.floor (LatticeQuadraticForm A y +
              ((abs y.re + abs y.im : Int) : Real)) -
              p.re * y.re - p.im * y.im) /\
        g x = m + p.re * x.re + p.im * x.im) /\
      (forall x p : GaussianInt, forall m : Int,
        (forall y : GaussianInt,
          m <= Int.floor (LatticeQuadraticForm A y +
              ((abs y.re + abs y.im : Int) : Real)) -
              p.re * y.re - p.im * y.im) ->
        m + p.re * x.re + p.im * x.im <= g x) /\
      (forall x : GaussianInt,
        LatticeQuadraticForm A x - ((abs x.re + abs x.im : Int) : Real) - 1 <=
          (g x : Real) /\
        (g x : Real) <=
          LatticeQuadraticForm A x + ((abs x.re + abs x.im : Int) : Real) + 1) /\
      (forall x : GaussianInt, 0 <= FourNeighborLaplacian g x) := by
-- BODY
  classical
  let q : GaussianInt → Real := fun z => LatticeQuadraticForm A z
  let energy : GaussianInt → GaussianInt → Int := fun p y =>
    Int.floor (LatticeQuadraticForm A y +
      ((abs y.re + abs y.im : Int) : Real)) - p.re * y.re - p.im * y.im
  let bounded : GaussianInt → Prop := fun p => ∃ b : Int, ∀ y, b ≤ energy p y
  let minimum : GaussianInt → Int := fun p =>
    if hp : bounded p then Classical.choose (Int.exists_least_of_bdd
      (show ∃ b : Int, ∀ z : Int, (∃ y, energy p y = z) → b ≤ z from
        ⟨Classical.choose hp, by
          intro z hz
          rcases hz with ⟨y, hy⟩
          rw [← hy]
          exact Classical.choose_spec hp y⟩)
      ⟨energy p 0, ⟨0, rfl⟩⟩)
    else 0
  have minimum_spec : ∀ p, bounded p →
      (∀ y, minimum p ≤ energy p y) ∧ ∃ y, minimum p = energy p y := by
    intro p hp
    dsimp [minimum]
    rw [dite_eq_left hp]
    have hs := Classical.choose_spec (Int.exists_least_of_bdd
      (show ∃ b : Int, ∀ z : Int, (∃ y, energy p y = z) → b ≤ z from
        ⟨Classical.choose hp, by
          intro z hz
          rcases hz with ⟨y, hy⟩
          rw [← hy]
          exact Classical.choose_spec hp y⟩)
      ⟨energy p 0, ⟨0, rfl⟩⟩)
    rcases hs with ⟨he, hl⟩
    constructor
    · intro y
      apply hl
      exact Exists.intro y rfl
    · rcases he with ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
  have bounded_iff : ∀ p, bounded p ↔ ∃ m : Int, (∀ y, m ≤ energy p y) ∧ ∃ y, m = energy p y := by
    intro p
    constructor
    · intro hp
      exact ⟨minimum p, minimum_spec p hp⟩
    · rintro ⟨m, hm, hy⟩
      exact ⟨m, hm⟩
  have q_nonneg : ∀ z, 0 ≤ q z := by
    intro z
    have hz := hpsd.dotProduct_mulVec_nonneg
      (![ (z.re : Real), (z.im : Real) ] : Fin 2 → Real)
    simpa [q, LatticeQuadraticForm, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      using hz
  let admitted : GaussianInt → Int → Prop := fun x z =>
    ∃ p, bounded p ∧ z = minimum p + p.re * x.re + p.im * x.im
  have admitted_upper : ∀ x z, admitted x z →
      z ≤ Int.floor (LatticeQuadraticForm A x +
        ((abs x.re + abs x.im : Int) : Real)) := by
    intro x z hz
    rcases hz with ⟨p, hp, rfl⟩
    have hm := (minimum_spec p hp).1 x
    dsimp [energy] at hm
    omega
  have admitted_nonempty : ∀ x, ∃ z, admitted x z := by
    intro x
    have hb : bounded 0 := by
      refine ⟨0, ?_⟩
      intro y
      have hf' : 0 ≤ Int.floor (LatticeQuadraticForm A y +
          ((abs y.re + abs y.im : Int) : Real)) := by
        apply Int.floor_nonneg.mpr
        have hi : 0 ≤ abs y.re + abs y.im :=
          add_nonneg (abs_nonneg _) (abs_nonneg _)
        have hw : (0 : Real) ≤ ((abs y.re + abs y.im : Int) : Real) := by
          exact_mod_cast hi
        exact add_nonneg (q_nonneg y) hw
      simpa [energy] using hf'
    refine ⟨minimum 0, 0, hb, ?_⟩
    simp
  let g : IntegerLatticeFunction := fun x =>
    Classical.choose (Int.exists_greatest_of_bdd
      ⟨Int.floor (LatticeQuadraticForm A x +
        ((abs x.re + abs x.im : Int) : Real)), admitted_upper x⟩
      (admitted_nonempty x))
  have g_spec : ∀ x, admitted x (g x) ∧
      ∀ z, admitted x z → z ≤ g x := by
    intro x
    exact Classical.choose_spec (Int.exists_greatest_of_bdd
      ⟨Int.floor (LatticeQuadraticForm A x +
        ((abs x.re + abs x.im : Int) : Real)), admitted_upper x⟩
      (admitted_nonempty x))
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    by_cases hp : bounded p
    · right
      exact bounded_iff p |>.mp hp
    · left
      intro K
      by_contra hn
      apply hp
      refine ⟨K + 1, ?_⟩
      intro y
      by_contra hy
      apply hn
      refine ⟨y, ?_⟩
      have hlt : energy p y ≤ K := by omega
      exact hlt
  · intro x
    rcases g_spec x with ⟨⟨p, hp, hvalue⟩, hgreat⟩
    refine ⟨p, minimum p, (minimum_spec p hp).1, (minimum_spec p hp).2, ?_⟩
    simp [hvalue]
  · intro x p m hm
    have hp : bounded p := ⟨m, hm⟩
    have hmin := (minimum_spec p hp).2
    rcases hmin with ⟨y, hy⟩
    have hle : m ≤ minimum p := by
      have := hm y
      calc
        m ≤ energy p y := by simpa [energy] using this
        _ = minimum p := hy.symm
    have htop := (g_spec x).2
      (minimum p + p.re * x.re + p.im * x.im)
      ⟨p, hp, rfl⟩
    omega
  · intro x
    have hu := admitted_upper x (g x) (g_spec x).1
    have hf := Int.floor_le (LatticeQuadraticForm A x +
      ((abs x.re + abs x.im : Int) : Real))
    constructor
    · obtain ⟨p, lower_energy⟩ := P5667T1RoundedSupportingSlope A hA hpsd x
      have hb : bounded p := ⟨Int.ceil (LatticeQuadraticForm A x -
          ((abs x.re + abs x.im : Int) : Real) - 1 -
          p.re * x.re - p.im * x.im), lower_energy⟩
      have hg := (g_spec x).2
        (minimum p + p.re * x.re + p.im * x.im)
        ⟨p, hb, rfl⟩
      have hminx : (Int.ceil (LatticeQuadraticForm A x -
          ((abs x.re + abs x.im : Int) : Real) - 1 -
          p.re * x.re - p.im * x.im) : Real) ≤
          (minimum p : Real) := by
        rcases (minimum_spec p hb).2 with ⟨y, hy⟩
        have hm' : Int.ceil (LatticeQuadraticForm A x -
            ((abs x.re + abs x.im : Int) : Real) - 1 -
            p.re * x.re - p.im * x.im) ≤ energy p y := by
          exact lower_energy y
        have hmp : Int.ceil (LatticeQuadraticForm A x -
            ((abs x.re + abs x.im : Int) : Real) - 1 -
            p.re * x.re - p.im * x.im) ≤ minimum p := by
          calc
            Int.ceil (LatticeQuadraticForm A x -
              ((abs x.re + abs x.im : Int) : Real) - 1 -
              p.re * x.re - p.im * x.im) ≤ energy p y := hm'
            _ = minimum p := hy.symm
        exact_mod_cast hmp
      have hgf : (minimum p : Real) + p.re * x.re + p.im * x.im ≤ (g x : Real) := by
        exact_mod_cast hg
      have hceil := Int.le_ceil (LatticeQuadraticForm A x -
        ((abs x.re + abs x.im : Int) : Real) - 1 -
        p.re * x.re - p.im * x.im)
      change (minimum p : Real) + (p.re : Real) * (x.re : Real) +
          (p.im : Real) * (x.im : Real) ≤ (g x : Real) at hgf
      linarith [hminx, hceil, hgf]
    · have hgu : (g x : Real) ≤
          (Int.floor (LatticeQuadraticForm A x +
            ((abs x.re + abs x.im : Int) : Real)) : Real) := by
        exact_mod_cast hu
      linarith
  · intro x
    have hl := (g_spec x).1
    rcases hl with ⟨p, hp, hvalue⟩
    have hcontact : ∀ y, y = x + 1 ∨ y = x - 1 ∨
        y = x + ⟨0, 1⟩ ∨ y = x - ⟨0, 1⟩ →
        ((minimum p : Real) + p.re * y.re + p.im * y.im) ≤ (g y : Real) := by
      intro y hy
      have hi := (g_spec y).2
        (minimum p + p.re * y.re + p.im * y.im)
        ⟨p, hp, rfl⟩
      exact_mod_cast hi
    have hcenter :
        (minimum p : Real) + p.re * x.re + p.im * x.im = (g x : Real) := by
      exact_mod_cast hvalue.symm
    have hcomp := RealLaplacianContactComparison.1
      (fun y => (minimum p : Real) + p.re * y.re + p.im * y.im)
      (fun y => (g y : Real)) x hcenter hcontact
    have hzero : RealFourNeighborLaplacian
        (fun y => (minimum p : Real) + p.re * y.re + p.im * y.im) x = 0 := by
      unfold RealFourNeighborLaplacian
      simp
      ring
    have hreal : 0 ≤ RealFourNeighborLaplacian (fun y => (g y : Real)) x := by
      rw [← hzero]
      exact hcomp
    rw [IntegerLaplacianCastBridge g x] at hreal
    exact_mod_cast hreal

end ApollonianSuperharmonic

end
