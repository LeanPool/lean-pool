/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicRepresentative
public import Mathlib.LinearAlgebra.Matrix.Notation

-- [TABLET NODE: IntegerPreservingNormalization]

/-!
# IntegerPreservingNormalization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem IntegerPreservingNormalization
    (A B : Matrix (Fin 2) (Fin 2) Real)
    (f : IntegerLatticeFunction)
    (hrep : IntegerSuperharmonicRepresentative A f)
    (delta : Real) (hdelta : 0 < delta)
    (hB : B = A - delta • (1 : Matrix (Fin 2) (Fin 2) Real)) :
    exists z : GaussianInt, exists n : Fin 2 -> Int,
      exists b : Fin 2 -> Real, exists u : IntegerLatticeFunction,
        (forall i, b i =
          (Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i - n i) /\
        (forall i, abs (b i) <= 1) /\
        (forall x, u x = f (x + z) - f z - n 0 * x.re - n 1 * x.im) /\
        u 0 = 0 /\
        (forall x, FourNeighborLaplacian u x <= 1) /\
        (forall x, LatticeQuadraticForm B x +
          dotProduct b ![(x.re : Real), (x.im : Real)] <= (u x : Real)) := by
-- BODY
  rcases hrep with ⟨hAs, hQg, hflap⟩
  have hBs : B.IsSymm := by
    rw [hB]
    exact hAs.sub (Matrix.isSymm_one.smul delta)
  have hqdiff (x : GaussianInt) :
      LatticeQuadraticForm A x - LatticeQuadraticForm B x =
        (delta / 2) * ((x.re : Real)^2 + (x.im : Real)^2) := by
    rw [hB]
    simp [LatticeQuadraticForm, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two]
    ring_nf
  have hdiv : ∀ M : Real, ∃ R : Real, ∀ x : GaussianInt,
      R ≤ (x.re : Real)^2 + (x.im : Real)^2 →
        M ≤ (f x : Real) - LatticeQuadraticForm B x := by
    intro M
    obtain ⟨R0, hR0⟩ := hQg (delta / 8) (by linarith)
    refine ⟨max R0 (max (4 * M / delta) 0), ?_⟩
    intro x hx
    have hfx := hR0 x (le_trans (le_max_left _ _) hx)
    have hpos : 0 ≤ (x.re : Real)^2 + (x.im : Real)^2 := by positivity
    have hmain :
        (delta / 4) * ((x.re : Real)^2 + (x.im : Real)^2) ≤
          (f x : Real) - LatticeQuadraticForm B x := by
      have he : -(delta / 8 * ((x.re : Real)^2 + (x.im : Real)^2)) ≤
          (f x : Real) - LatticeQuadraticForm A x := neg_le_of_abs_le hfx
      rw [show (f x : Real) - LatticeQuadraticForm B x =
          (LatticeQuadraticForm A x - LatticeQuadraticForm B x) +
            ((f x : Real) - LatticeQuadraticForm A x) by ring]
      rw [hqdiff]
      have hnon : 0 ≤ delta * ((x.re : Real)^2 + (x.im : Real)^2) :=
        mul_nonneg (le_of_lt hdelta) hpos
      linarith
    have hR : 4 * M / delta ≤
        (x.re : Real)^2 + (x.im : Real)^2 :=
      le_trans (le_trans (le_max_left (4 * M / delta) 0)
        (le_max_right R0 (max (4 * M / delta) 0))) hx
    have hR' : 4 * M ≤ delta *
        ((x.re : Real)^2 + (x.im : Real)^2) := by
      simpa [mul_comm] using (div_le_iff₀ hdelta).mp hR
    nlinarith
  obtain ⟨R0, hR0⟩ := hdiv ((f 0 : Real) - LatticeQuadraticForm B 0)
  let radius : Real := max R0 1
  let S : Set GaussianInt := {x | (x.re : Real)^2 + (x.im : Real)^2 < radius}
  obtain ⟨N, hN⟩ := exists_nat_ge radius
  have hR : radius ≤ (N : Real) := hN
  have hNo : (1 : Real) ≤ (N : Real) := le_trans (le_max_right R0 1) hN
  have hS : S.Finite := by
    have hx_of_mem (x : GaussianInt) (hx : x ∈ S) :
        -(N : Int) ≤ x.re ∧ x.re ≤ N ∧ -(N : Int) ≤ x.im ∧ x.im ≤ N := by
      dsimp [S, radius] at hx
      have hr : -(N : Real) ≤ (x.re : Real) := by
        nlinarith [sq_nonneg (x.im : Real), sq_nonneg ((x.re : Real) + N), hR, hNo]
      have hr' : (x.re : Real) ≤ (N : Real) := by
        nlinarith [sq_nonneg (x.im : Real), sq_nonneg ((x.re : Real) - N), hR, hNo]
      have hi : -(N : Real) ≤ (x.im : Real) := by
        nlinarith [sq_nonneg (x.re : Real), sq_nonneg ((x.im : Real) + N), hR, hNo]
      have hi' : (x.im : Real) ≤ (N : Real) := by
        nlinarith [sq_nonneg (x.re : Real), sq_nonneg ((x.im : Real) - N), hR, hNo]
      exact ⟨by exact_mod_cast hr, by exact_mod_cast hr',
        by exact_mod_cast hi, by exact_mod_cast hi'⟩
    let encode (x : S) : Fin (2 * N + 1) × Fin (2 * N + 1) :=
      ⟨⟨(x.1.re + N).toNat, by
          have hxs := hx_of_mem x.1 x.2
          omega⟩, ⟨(x.1.im + N).toNat, by
          have hxs := hx_of_mem x.1 x.2
          omega⟩⟩
    let : Finite S := Finite.of_injective encode (by
      intro x y hxy
      apply Subtype.ext
      apply Zsqrtd.ext
      · have he := congrArg (fun z => z.1) (congrArg Prod.fst hxy)
        have hxn := (hx_of_mem x.1 x.2).1
        have hxp := (hx_of_mem x.1 x.2).2.1
        have hyn := (hx_of_mem y.1 y.2).1
        have hyp := (hx_of_mem y.1 y.2).2.1
        have hxn0 : 0 ≤ x.1.re + N := by omega
        have hyn0 : 0 ≤ y.1.re + N := by omega
        dsimp [encode] at he
        have hxn1 := Int.toNat_of_nonneg hxn0
        have hyn1 := Int.toNat_of_nonneg hyn0
        omega
      · have he := congrArg (fun z => z.val) (congrArg Prod.snd hxy)
        have hxn := (hx_of_mem x.1 x.2).2.2.1
        have hxp := (hx_of_mem x.1 x.2).2.2.2
        have hyn := (hx_of_mem y.1 y.2).2.2.1
        have hyp := (hx_of_mem y.1 y.2).2.2.2
        have hxn0 : 0 ≤ x.1.im + N := by omega
        have hyn0 : 0 ≤ y.1.im + N := by omega
        dsimp [encode] at he
        have hxn1 := Int.toNat_of_nonneg hxn0
        have hyn1 := Int.toNat_of_nonneg hyn0
        omega)
    exact Set.finite_coe_iff.mp (by infer_instance : Finite S)
  have hSne : S.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [S, radius]
    norm_num
  let energy : GaussianInt → Real := fun y => (f y : Real) - LatticeQuadraticForm B y
  obtain ⟨z, hzS, hzmin⟩ := Set.exists_min_image S energy hS hSne
  let n : Fin 2 → Int := fun i =>
    Int.floor ((Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i)
  let b : Fin 2 → Real := fun i =>
    (Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i - n i
  let u : IntegerLatticeFunction := fun x =>
    f (x + z) - f z - n 0 * x.re - n 1 * x.im
  refine ⟨z, n, b, u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    dsimp [b, n]
    have hf := Int.floor_le ((Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i)
    have hg := Int.lt_floor_add_one ((Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i)
    have habs : abs ((Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i -
        (↑⌊(Matrix.mulVec B ![(z.re : Real), (z.im : Real)]) i⌋ : Real)) < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    exact le_of_lt habs
  · intro x
    rfl
  · dsimp [u]
    norm_num
  · intro x
    have hh := hflap (x + z)
    dsimp [u, FourNeighborLaplacian] at hh ⊢
    ring_nf at hh ⊢
    exact hh
  · intro x
    have hglobal : energy z ≤ energy (x + z) := by
      by_cases hxin : x + z ∈ S
      · exact hzmin (x + z) hxin
      · have hlarge : R0 ≤ ((x + z).re : Real)^2 + ((x + z).im : Real)^2 := by
          change ¬(((x + z).re : Real)^2 + ((x + z).im : Real)^2) < radius at hxin
          exact le_trans (le_max_left R0 1) (le_of_not_gt hxin)
        have houtside := hR0 (x + z) hlarge
        have hzero : energy z ≤ energy 0 := hzmin 0 (by
          dsimp [S, radius]
          norm_num)
        exact le_trans hzero houtside
    have hquadadd (x : GaussianInt) :
        LatticeQuadraticForm B (x + z) =
          LatticeQuadraticForm B x + LatticeQuadraticForm B z +
            dotProduct (Matrix.mulVec B ![(z.re : Real), (z.im : Real)])
              ![(x.re : Real), (x.im : Real)] := by
      simp [LatticeQuadraticForm, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        hBs.apply 0 1]
      ring
    have hineq : LatticeQuadraticForm B x +
        dotProduct b ![(x.re : Real), (x.im : Real)] ≤
        (f (x + z) : Real) - f z - n 0 * x.re - n 1 * x.im := by
      dsimp [energy] at hglobal
      rw [hquadadd x] at hglobal
      dsimp [b]
      simp [dotProduct, Fin.sum_univ_two] at hglobal ⊢
      linarith
    change LatticeQuadraticForm B x +
      dotProduct b ![(x.re : Real), (x.im : Real)] ≤
      ((u x : Int) : Real)
    simpa [u, Int.cast_sub, Int.cast_mul] using hineq

end ApollonianSuperharmonic

end
