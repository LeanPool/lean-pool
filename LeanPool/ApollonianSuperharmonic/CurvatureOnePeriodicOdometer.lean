/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicRepresentative
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.TilingLattice

-- [TABLET NODE: CurvatureOnePeriodicOdometer]

/-!
# CurvatureOnePeriodicOdometer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace CurvatureOneProof

private theorem triangular :
    ∀ (a : ℤ), ∀ (b : ℤ), (a + b) * (a + b - (1 : ℤ)) / (2 : ℤ) = a * (a - (1 : ℤ)) / (2 : ℤ) + b
        * (b - (1 : ℤ)) / (2 : ℤ) + a * b := by
  classical
  intro a b
  have ha : Even (a * (a - 1)) := Int.even_mul_pred_self a
  have hb : Even (b * (b - 1)) := Int.even_mul_pred_self b
  have hsum : Even ((a + b) * (a + b - 1)) := Int.even_mul_pred_self (a + b)
  apply Int.ediv_eq_of_eq_mul_left (by norm_num)
  have ha' := Int.two_mul_ediv_two_of_even ha
  have hb' := Int.two_mul_ediv_two_of_even hb
  have hs' := Int.two_mul_ediv_two_of_even hsum
  ring_nf at ha' hb' hs' ⊢
  linarith [ha', hb', hs']

private theorem circle_formula :
    ∀ (C : BandCircle), ∀ (z : GaussianInt), (C.1.1.1 = 1) → ((C.1.1.2 = 1 + 2 * z) →
        (CircleMatrix C = ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)], ![(z.im : ℝ), (-z.re : ℝ)]])) := by
  classical
  intro C z hradius hcenter
  unfold CircleMatrix BandCircleEuclideanData
  simp only [hradius, hcenter]
  ext i j; fin_cases i <;> fin_cases j
  all_goals simp only [
    Complex.div_re, Complex.div_im, GaussianInt.toComplex_def,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im]
  all_goals norm_num
  all_goals ring

private theorem linear_difference :
    ∀ (C : BandCircle), ∀ (z : GaussianInt),
    let g : IntegerLatticeFunction := fun x =>
      (1 + z.re) * (x.re * (x.re - 1) / 2) -
        z.re * (x.im * (x.im - 1) / 2) + z.im * x.re * x.im
    (CircleMatrix C = ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)], ![(z.im : ℝ), (-z.re : ℝ)]]) → (∀ (x
        : GaussianInt), (↑(g x) : ℝ) - LatticeQuadraticForm (CircleMatrix C) x = -((1 : ℝ) +
        (↑z.re : ℝ)) / (2 : ℝ) * (↑x.re : ℝ) + (↑z.re : ℝ) / (2 : ℝ) * (↑x.im : ℝ)) := by
  classical
  intro C z g circle_formula x
  have half (a : ℤ) :
      ((a * (a - 1) / 2 : ℤ) : ℝ) =
        (a : ℝ) * (a - 1 : ℝ) / 2 := by
    have he : Even (a * (a - 1)) := Int.even_mul_pred_self a
    have hh := Int.two_mul_ediv_two_of_even he
    have hh' : a * (a - 1) / 2 * 2 = a * (a - 1) := by
      simpa [mul_comm] using hh
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    exact_mod_cast hh'
  rw [circle_formula]
  simp only [Int.reduceNeg, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one,
      GaussianInt.intCast_re, GaussianInt.intCast_im, LatticeQuadraticForm, one_div,
      dotProduct, Matrix.mulVec, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val',
      Matrix.cons_val_fin_one, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, neg_mul, neg_add_rev, g]
  rw [half x.re, half x.im]
  rw [← GaussianInt.intCast_re z, ← GaussianInt.intCast_im z,
    ← GaussianInt.intCast_re x, ← GaussianInt.intCast_im x]
  ring

private theorem difference :
    ∀ (C : BandCircle), ∀ (z : GaussianInt),
    let g : IntegerLatticeFunction := fun x =>
      (1 + z.re) * (x.re * (x.re - 1) / 2) -
        z.re * (x.im * (x.im - 1) / 2) + z.im * x.re * x.im
    (CircleMatrix C = ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)], ![(z.im : ℝ), (-z.re : ℝ)]]) → (
    let α : ℝ := -(1 + (z.re : ℝ)) / 2
    let β : ℝ := (z.re : ℝ) / 2
    (∀ (a : ℤ), ((a * (a - 1) / 2 : ℤ) : ℝ) = (a : ℝ) * (a - 1 : ℝ) / 2) → (∀ (x : GaussianInt),
        (↑(g x) : ℝ) - LatticeQuadraticForm (CircleMatrix C) x = α * (↑x.re : ℝ) + β * (↑x.im :
        ℝ))) := by
  classical
  intro C z g circle_formula α β half x
  rw [circle_formula]
  simp only [Int.reduceNeg, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_one,
      GaussianInt.intCast_re, GaussianInt.intCast_im, LatticeQuadraticForm, one_div,
      dotProduct, Matrix.mulVec, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val',
      Matrix.cons_val_fin_one, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, neg_mul, g]
  rw [half x.re, half x.im]
  rw [← GaussianInt.intCast_re z, ← GaussianInt.intCast_im z,
    ← GaussianInt.intCast_re x, ← GaussianInt.intCast_im x]
  dsimp [α, β]
  ring

end CurvatureOneProof

theorem CurvatureOnePeriodicOdometer (C : BandCircle)
    (z : GaussianInt) (hC : C.1.1 = (1, 1 + 2 * z)) :
    let g : IntegerLatticeFunction := fun x =>
      (1 + z.re) * (x.re * (x.re - 1) / 2) -
        z.re * (x.im * (x.im - 1) / 2) + z.im * x.re * x.im
    let T : ProtoTile := ⟨{0}, 0⟩
    let h : PartialOdometer := CurvatureOneOdometer z
    BandPrototile C.1.1 T ∧ TileOdometer C.1.1 T h ∧
      (h.domain : Set GaussianInt) = FootprintVertices T ∧
      (∀ x, x ∈ h.domain → g x = h.value x) ∧
      GlobalOdometerExtends g h ∧
      IntegerSuperharmonicRepresentative (CircleMatrix C) g ∧
      (∀ v, v ∈ TilingLattice C → ∃ a : GaussianInt,
        Matrix.mulVec (CircleMatrix C) ![(v.re : ℝ), (v.im : ℝ)] =
          ![(a.re : ℝ), (a.im : ℝ)] ∧
        ∀ x, g (x + v) = g x + x.re * a.re + x.im * a.im + g v) ∧
      ∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
        (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
            (b.1 * (x + v).re + b.2 * (x + v).im) =
          (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
            (b.1 * x.re + b.2 * x.im) := by
-- BODY
  dsimp
  let g : IntegerLatticeFunction := fun x =>
    (1 + z.re) * (x.re * (x.re - 1) / 2) -
      z.re * (x.im * (x.im - 1) / 2) + z.im * x.re * x.im
  let T : ProtoTile := ⟨{0}, 0⟩
  let h : PartialOdometer := CurvatureOneOdometer z
  have triangular (a b : ℤ) :
      (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b :=
          CurvatureOneProof.triangular a b
  have hcoord : C.1.1 = (1, 1 + 2 * z) := hC
  have hradius : C.1.1.1 = 1 := by rw [hcoord]
  have hcenter : C.1.1.2 = 1 + 2 * z := by rw [hcoord]
  have hne0 : (0 : GaussianInt) ≠ 1 + ⟨0, 1⟩ := by
    intro hbad
    have him := congrArg (fun q : GaussianInt => q.im) hbad
    norm_num at him
  have hne1 : (⟨0, 1⟩ : GaussianInt) ≠ 0 := by
    intro hbad
    have him := congrArg (fun q : GaussianInt => q.im) hbad
    norm_num at him
  have circle_formula : CircleMatrix C =
      ![![((1 + z.re : ℤ) : ℝ), (z.im : ℝ)],
        ![(z.im : ℝ), (-z.re : ℝ)]] := CurvatureOneProof.circle_formula C z hradius hcenter
  have triangular_real (a b : ℤ) :
      (((a + b) * (a + b - 1) / 2 : ℤ) : ℝ) =
        ((a * (a - 1) / 2 : ℤ) : ℝ) +
          ((b * (b - 1) / 2 : ℤ) : ℝ) + (a * b : ℝ) := by
    exact_mod_cast triangular a b
  have linear_difference (x : GaussianInt) :
      (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x =
        (-(1 + (z.re : ℝ)) / 2) * x.re + ((z.re : ℝ) / 2) * x.im :=
            CurvatureOneProof.linear_difference C z circle_formula x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoord]
    exact BandPrototile.unit z 0 0
  · rw [hcoord]
    apply TileOdometer.unit z 0 T h
    · rfl
    · ext x
      simp [h, T, CurvatureOneOdometer, FootprintVertices]
    · refine ⟨0, 0, 0, ?_, ?_⟩
      · intro x
        simp [h, CurvatureOneOdometer]
      · intro x hx
        simp [h, CurvatureOneOdometer] at hx ⊢
  · ext x
    simp [CurvatureOneOdometer, FootprintVertices]
  · intro x hx
    simp only [CurvatureOneOdometer, Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
        at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hne0, hne1]
  · refine ⟨0, ?_⟩
    intro x hx
    simp only [CurvatureOneOdometer, Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton,
        add_zero] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp [hne0, hne1]
  · unfold IntegerSuperharmonicRepresentative
    constructor
    · unfold Matrix.IsSymm
      rw [circle_formula]
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    constructor
    · unfold QuadraticGrowthAtInfinity
      intro ε hε
      let α : ℝ := -(1 + (z.re : ℝ)) / 2
      let β : ℝ := (z.re : ℝ) / 2
      have half (a : ℤ) :
          ((a * (a - 1) / 2 : ℤ) : ℝ) =
            (a : ℝ) * (a - 1 : ℝ) / 2 := by
        have he : Even (a * (a - 1)) := Int.even_mul_pred_self a
        have hh := Int.two_mul_ediv_two_of_even he
        apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
        have hh' : a * (a - 1) / 2 * 2 = a * (a - 1) := by
          simpa [mul_comm] using hh
        exact_mod_cast hh'
      have difference (x : GaussianInt) :
          (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x =
            α * x.re + β * x.im := CurvatureOneProof.difference C z circle_formula half x
      let K : ℝ := |α| ^ 2 + |β| ^ 2
      refine ⟨(2 * K / ε ^ 2) + 1, ?_⟩
      intro x hx
      have hx0 : 0 ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 := by positivity
      have ha : |α * (x.re : ℝ)| ≤ ε / 4 * (x.re : ℝ) ^ 2 + |α| ^ 2 / ε := by
        have heq : ε / 4 * (x.re : ℝ) ^ 2 + |α| ^ 2 / ε =
            (ε ^ 2 * (x.re : ℝ) ^ 2 / 4 + |α| ^ 2) / ε := by field_simp
        rw [heq]
        apply (le_div_iff₀ hε).2
        rw [abs_mul]
        have hs := sq_nonneg (ε * |(x.re : ℝ)| - 2 * |α|)
        have habs : |(x.re : ℝ)| ^ 2 = (x.re : ℝ) ^ 2 := sq_abs _
        nlinarith
      have hb : |β * (x.im : ℝ)| ≤ ε / 4 * (x.im : ℝ) ^ 2 + |β| ^ 2 / ε := by
        have heq : ε / 4 * (x.im : ℝ) ^ 2 + |β| ^ 2 / ε =
            (ε ^ 2 * (x.im : ℝ) ^ 2 / 4 + |β| ^ 2) / ε := by field_simp
        rw [heq]
        apply (le_div_iff₀ hε).2
        rw [abs_mul]
        have hs := sq_nonneg (ε * |(x.im : ℝ)| - 2 * |β|)
        have habs : |(x.im : ℝ)| ^ 2 = (x.im : ℝ) ^ 2 := sq_abs _
        nlinarith
      have habs : |α * x.re + β * x.im| ≤
          ε / 4 * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) + K / ε := by
        calc
          _ ≤ |α * (x.re : ℝ)| + |β * (x.im : ℝ)| := abs_add_le _ _
          _ ≤ (ε / 4 * (x.re : ℝ) ^ 2 + |α| ^ 2 / ε) +
              (ε / 4 * (x.im : ℝ) ^ 2 + |β| ^ 2 / ε) := add_le_add ha hb
          _ = _ := by dsimp [K]; ring
      rw [difference]
      have hrel : ε ^ 2 * (K / ε ^ 2) = K := by field_simp
      have hrel2 : ε * (K / ε) = K := by field_simp
      have hbound : K / ε ≤ ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) / 2 := by
        have hK : 0 ≤ K := by dsimp [K]; positivity
        have hmul := mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ ε / 2)
        calc
          K / ε ≤ K / ε + ε / 2 := le_add_of_nonneg_right (by positivity)
          _ = (2 * K / ε ^ 2 + 1) * (ε / 2) := by field_simp
          _ ≤ ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) * (ε / 2) := hmul
          _ = ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) / 2 := by ring
      nlinarith [habs, hbound]
    · intro x
      simp only [FourNeighborLaplacian, Int.reduceNeg, Zsqrtd.re_add, Zsqrtd.re_one,
          add_sub_cancel_right, Zsqrtd.im_add, Zsqrtd.im_one, add_zero, Zsqrtd.re_sub,
          Zsqrtd.im_sub, sub_zero, tsub_le_iff_right]
      have hp : (x.re + 1) * x.re / 2 = x.re * (x.re - 1) / 2 + 1 * 0 / 2 + x.re * 1 := by
        convert triangular x.re 1 using 1 <;> ring
      have hm : (x.re - 1) * (x.re - 1 - 1) / 2 = x.re * (x.re - 1) / 2 + (-1) * (-1 - 1) / 2 +
          x.re * (-1) := by
        convert triangular x.re (-1) using 1; ring
      have hpi : (x.im + 1) * x.im / 2 = x.im * (x.im - 1) / 2 + 1 * 0 / 2 + x.im * 1 := by
        convert triangular x.im 1 using 1 <;> ring
      have hmi : (x.im - 1) * (x.im - 1 - 1) / 2 = x.im * (x.im - 1) / 2 + (-1) * (-1 - 1) / 2 +
          x.im * (-1) := by
        convert triangular x.im (-1) using 1; ring
      rw [hp, hm, hpi, hmi]
      ring_nf
      omega
  · intro v hv
    have hvtop : v ∈ (⊤ : AddSubgroup GaussianInt) := by
      trivial
    have hlat : TilingLattice C = ⊤ := by
      simp [TilingLattice, hcoord]
    rw [hlat] at hv
    refine ⟨⟨(1 + z.re) * v.re + z.im * v.im, z.im * v.re - z.re * v.im⟩, ?_, ?_⟩
    · rw [circle_formula]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, Int.cast_add,
          Int.cast_one, GaussianInt.intCast_re, GaussianInt.intCast_im, Int.cast_mul,
          Int.cast_sub]
      rw [← GaussianInt.intCast_re z, ← GaussianInt.intCast_im z,
        ← GaussianInt.intCast_re v, ← GaussianInt.intCast_im v]
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct]
      ring
    · intro x
      simp only [Int.reduceNeg]
      rw [triangular x.re v.re, triangular x.im v.im]
      ring
  · refine ⟨(-(1 + (z.re : ℝ)) / 2, (z.re : ℝ) / 2), ?_⟩
    intro v hv x
    have hshift := linear_difference (x + v)
    have hbase := linear_difference x
    calc
      (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
          (-(1 + (z.re : ℝ)) / 2 * (x + v).re + (z.re : ℝ) / 2 * (x + v).im) =
          0 := by rw [hshift]; ring
      _ = (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
          (-(1 + (z.re : ℝ)) / 2 * x.re + (z.re : ℝ) / 2 * x.im) := by
            rw [hbase]
            ring
      _ = _ := by rfl

end ApollonianSuperharmonic

end
