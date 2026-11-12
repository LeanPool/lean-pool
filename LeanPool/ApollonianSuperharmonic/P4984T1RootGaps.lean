/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P4984T1ClosedGap
public import LeanPool.ApollonianSuperharmonic.P4828T1Root
public import LeanPool.ApollonianSuperharmonic.BandPackingExterior
public import LeanPool.ApollonianSuperharmonic.P4953T1LiteralHulls
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Complex.BigOperators

-- [TABLET NODE: P4984T1RootGaps]

/-!
# P4984T1RootGaps

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RootGapLemmas

private theorem rectHull :
    ∀ (u : ℝ), ∀ (v : ℝ), convexHull ℝ (Set.range (fun i : Fin 4 =>
        ![⟨u, v⟩, ⟨u + 1, v⟩, ⟨u, v + 2⟩, ⟨u + 1, v + 2⟩] i)) =
        {z : ℂ | u ≤ z.re ∧ z.re ≤ u + 1 ∧ v ≤ z.im ∧ z.im ≤ v + 2} := by
  classical
  intro u v
  let c : Fin 4 → ℂ := ![⟨u, v⟩, ⟨u + 1, v⟩, ⟨u, v + 2⟩, ⟨u + 1, v + 2⟩]
  change convexHull ℝ (Set.range c) = _
  ext z
  constructor
  · intro hz
    rw [mem_convexHull_iff_exists_fintype] at hz
    rcases hz with ⟨ι, _, w, p, hw, hsum, hp, heq⟩
    let : Fintype ι := inferInstance
    have hcoords (i : ι) : u ≤ (p i).re ∧ (p i).re ≤ u + 1 ∧
        v ≤ (p i).im ∧ (p i).im ≤ v + 2 := by
      obtain ⟨j, hj⟩ := hp i
      rw [← hj]
      fin_cases j <;> simp [c]
    have hre : (∑ i, w i * (p i).re) = z.re := by
      have h := congrArg Complex.re heq
      simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul] using h
    have him : (∑ i, w i * (p i).im) = z.im := by
      have h := congrArg Complex.im heq
      simpa only [Complex.im_sum, Complex.smul_im, smul_eq_mul] using h
    constructor
    · calc
        u = u * (∑ i, w i) := by rw [hsum]; ring
        _ = ∑ i, w i * u := by
          calc
            _ = ∑ i, u * w i := by rw [Finset.mul_sum]
            _ = ∑ i, w i * u := by apply Finset.sum_congr rfl; intro i hi; ring
        _ ≤ ∑ i, w i * (p i).re := by
          apply Finset.sum_le_sum (s := Finset.univ)
          intro i hi
          exact mul_le_mul_of_nonneg_left (hcoords i).1 (hw i)
        _ = z.re := hre
    constructor
    · calc
        z.re = ∑ i, w i * (p i).re := hre.symm
        _ ≤ ∑ i, w i * (u + 1) := by
          apply Finset.sum_le_sum (s := Finset.univ)
          intro i hi
          exact mul_le_mul_of_nonneg_left (hcoords i).2.1 (hw i)
        _ = (u + 1) * (∑ i, w i) := by
          calc
            _ = ∑ i, (u + 1) * w i := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (u + 1) * ∑ i, w i := by rw [Finset.mul_sum]
        _ = u + 1 := by rw [hsum]; ring
    constructor
    · calc
        v = v * (∑ i, w i) := by rw [hsum]; ring
        _ = ∑ i, w i * v := by
          calc
            _ = ∑ i, v * w i := by rw [Finset.mul_sum]
            _ = ∑ i, w i * v := by apply Finset.sum_congr rfl; intro i hi; ring
        _ ≤ ∑ i, w i * (p i).im := by
          apply Finset.sum_le_sum (s := Finset.univ)
          intro i hi
          exact mul_le_mul_of_nonneg_left (hcoords i).2.2.1 (hw i)
        _ = z.im := him
    · calc
        z.im = ∑ i, w i * (p i).im := him.symm
        _ ≤ ∑ i, w i * (v + 2) := by
          apply Finset.sum_le_sum (s := Finset.univ)
          intro i hi
          exact mul_le_mul_of_nonneg_left (hcoords i).2.2.2 (hw i)
        _ = (v + 2) * (∑ i, w i) := by
          calc
            _ = ∑ i, (v + 2) * w i := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = (v + 2) * ∑ i, w i := by rw [Finset.mul_sum]
        _ = v + 2 := by rw [hsum]; ring
  · rintro ⟨hxl, hxu, hyl, hyu⟩
    let s : ℝ := z.re - u
    let t : ℝ := (z.im - v) / 2
    let w : Fin 4 → ℝ := ![(1 - s) * (1 - t), s * (1 - t), (1 - s) * t, s * t]
    have hs0 : 0 ≤ s := by dsimp [s]; linarith
    have hs1 : s ≤ 1 := by dsimp [s]; linarith
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : t ≤ 1 := by change (z.im - v) / 2 ≤ 1; linarith
    have hw : ∀ i, 0 ≤ w i := by
      intro i
      fin_cases i <;> simp? [w] <;> positivity
    have hsum : (∑ i : Fin 4, w i) = 1 := by
      simp [Fin.sum_univ_succ, w]; ring
    have heq : (∑ i : Fin 4, w i • c i) = z := by
      apply Complex.ext <;> simp [c, w, s, t, Fin.sum_univ_succ,
        ] <;> ring
    exact mem_convexHull_of_exists_fintype w c hw hsum
      (by intro i; exact ⟨i, rfl⟩) heq

private theorem hpolyMinus :
    ∀ (a : GaussianInt), P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a false) =
        convexHull ℝ (Set.range (fun i : Fin 4 =>
          ![⟨2 * (a.re : ℝ), 2 * (a.im : ℝ)⟩,
            ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩,
            ⟨2 * (a.re : ℝ), 2 * (a.im : ℝ) + 2⟩,
            ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩] i)) := by
  classical
  intro a
  have h2 : GaussianInt.toComplex 2 = (2 : ℂ) := by
    rw [GaussianInt.toComplex_def₂]
    apply Complex.ext <;> norm_num
  have haRe : (GaussianInt.toComplex a).re = (a.re : ℝ) :=
    (GaussianInt.intCast_re a).symm
  have haIm : (GaussianInt.toComplex a).im = (a.im : ℝ) :=
    (GaussianInt.intCast_im a).symm
  have hA : 1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩ := by
    rw [h2, GaussianInt.toComplex_def₂ a]
    apply Complex.ext <;> simp; ring
  have hI : GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt) = Complex.I := by
    rw [GaussianInt.toComplex_def₂]
    apply Complex.ext <;> simp
  have hB : 1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
      GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt) =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩ := by
    rw [h2, GaussianInt.toComplex_def₂ a, hI]
    apply Complex.ext <;> simp; ring
  have hA' : 1 + 2 * (a : ℂ) =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩ := by
    simpa [h2] using hA
  have hB' : 1 + 2 * (a : ℂ) + 2 * Complex.I =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩ := by
    simpa [h2, hI] using hB
  apply congrArg (convexHull ℝ)
  ext z
  simp [P4828T1Root, Fin.exists_fin_succ]
  simp only [h2, hI, hA']
  simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, haRe, haIm]
  all_goals norm_num; ring_nf; tauto

private theorem hpolyPlus :
    ∀ (a : GaussianInt), P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a true) =
        convexHull ℝ (Set.range (fun i : Fin 4 =>
          ![⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩,
            ⟨(2 * (a.re : ℝ) + 1) + 1, 2 * (a.im : ℝ)⟩,
            ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩,
            ⟨(2 * (a.re : ℝ) + 1) + 1, 2 * (a.im : ℝ) + 2⟩] i)) := by
  classical
  intro a
  have h2 : GaussianInt.toComplex 2 = (2 : ℂ) := by
    rw [GaussianInt.toComplex_def₂]
    apply Complex.ext <;> norm_num
  have haRe : (GaussianInt.toComplex a).re = (a.re : ℝ) :=
    (GaussianInt.intCast_re a).symm
  have haIm : (GaussianInt.toComplex a).im = (a.im : ℝ) :=
    (GaussianInt.intCast_im a).symm
  have hA : 1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩ := by
    rw [h2, GaussianInt.toComplex_def₂ a]
    apply Complex.ext <;> simp; ring
  have hI : GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt) = Complex.I := by
    rw [GaussianInt.toComplex_def₂]
    apply Complex.ext <;> simp
  have hB : 1 + GaussianInt.toComplex 2 * GaussianInt.toComplex a +
      GaussianInt.toComplex 2 * GaussianInt.toComplex (⟨0, 1⟩ : GaussianInt) =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩ := by
    rw [h2, GaussianInt.toComplex_def₂ a, hI]
    apply Complex.ext <;> simp; ring
  have hA' : 1 + 2 * (a : ℂ) =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩ := by
    simpa [h2] using hA
  have hB' : 1 + 2 * (a : ℂ) + 2 * Complex.I =
      ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩ := by
    simpa [h2, hI] using hB
  apply congrArg (convexHull ℝ)
  ext z
  simp [P4828T1Root, Fin.exists_fin_succ]
  simp only [h2, hI, hA']
  simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, haRe, haIm]
  all_goals norm_num; ring_nf; tauto

private theorem hdistMinus :
    ∀ (a : GaussianInt), ∀ (z : ℂ), (∀ j : Fin 3, 0 < (P4828T1Root a false j.succ).1 →
        (1 / ((P4828T1Root a false j.succ).1 : ℝ)) ≤
          dist z ((P4828T1Root a false j.succ).2 /
            ((P4828T1Root a false j.succ).1 : ℝ))) ↔
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := by
  classical
  intro a z
  constructor
  · intro hd
    constructor
    · have h := hd 0 (by simp [P4828T1Root])
      simpa [P4828T1Root] using h
    · have h := hd 2 (by simp [P4828T1Root])
      simpa [P4828T1Root] using h
  · rintro ⟨h₁, h₂⟩ j hj
    fin_cases j
    · simpa [P4828T1Root] using h₁
    · simp [P4828T1Root] at hj
    · simpa [P4828T1Root] using h₂

private theorem hdistPlus :
    ∀ (a : GaussianInt), ∀ (z : ℂ), (∀ j : Fin 3, 0 < (P4828T1Root a true j.succ).1 →
        (1 / ((P4828T1Root a true j.succ).1 : ℝ)) ≤
          dist z ((P4828T1Root a true j.succ).2 /
            ((P4828T1Root a true j.succ).1 : ℝ))) ↔
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := by
  classical
  intro a z
  constructor
  · intro hd
    constructor
    · have h := hd 0 (by simp [P4828T1Root])
      simpa [P4828T1Root] using h
    · have h := hd 1 (by simp [P4828T1Root])
      simpa [P4828T1Root] using h
  · rintro ⟨h₁, h₂⟩ j hj
    fin_cases j
    · simpa [P4828T1Root] using h₁
    · simpa [P4828T1Root] using h₂
    · simp [P4828T1Root] at hj

private theorem hminusChar :
    (∀ (u : ℝ), ∀ (v : ℝ), convexHull ℝ (Set.range (fun i : Fin 4 => ![⟨u, v⟩, ⟨u + 1, v⟩, ⟨u, v
        + 2⟩, ⟨u + 1, v + 2⟩] i)) = {z : ℂ | u ≤ z.re ∧ z.re ≤ u + 1 ∧ v ≤ z.im ∧ z.im ≤ v + 2})
        → (∀ (a : GaussianInt), P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a false) =
        convexHull ℝ (Set.range (fun i : Fin 4 => ![⟨2 * (a.re : ℝ), 2 * (a.im : ℝ)⟩, ⟨2 * (a.re
        : ℝ) + 1, 2 * (a.im : ℝ)⟩, ⟨2 * (a.re : ℝ), 2 * (a.im : ℝ) + 2⟩, ⟨2 * (a.re : ℝ) + 1, 2 *
        (a.im : ℝ) + 2⟩] i))) → (∀ (a : GaussianInt), ∀ (z : ℂ), (∀ j : Fin 3, 0 < (P4828T1Root
        a false j.succ).1 → (1 / ((P4828T1Root a false j.succ).1 : ℝ)) ≤ dist z ((P4828T1Root
        a false j.succ).2 / ((P4828T1Root a false j.succ).1 : ℝ))) ↔ 1 ≤ dist z ((1 + 2 * a :
        GaussianInt) : ℂ) ∧ 1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ)) → ∀ (a :
        GaussianInt), ∀ (z : ℂ), z ∈ P4984T1ClosedGap (2 * (a.re : ℝ)) (P4828T1Root a false) ↔
        2 * (a.re : ℝ) ≤ z.re ∧ z.re ≤ 2 * (a.re : ℝ) + 1 ∧
        2 * (a.im : ℝ) ≤ z.im ∧ z.im ≤ 2 * (a.im : ℝ) + 2 ∧
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := by
  classical
  intro rectHull hpolyMinus hdistMinus a z
  change (z ∈ P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a false) ∧
    ∀ j : Fin 3, 0 < (P4828T1Root a false j.succ).1 →
      (1 / ((P4828T1Root a false j.succ).1 : ℝ)) ≤
        dist z ((P4828T1Root a false j.succ).2 /
          ((P4828T1Root a false j.succ).1 : ℝ))) ↔ _
  rw [hpolyMinus a, rectHull, hdistMinus a z]
  simp only [Set.mem_ofPred_eq]
  tauto

private theorem hplusChar :
    (∀ (u : ℝ), ∀ (v : ℝ), convexHull ℝ (Set.range (fun i : Fin 4 => ![⟨u, v⟩, ⟨u + 1, v⟩, ⟨u, v
        + 2⟩, ⟨u + 1, v + 2⟩] i)) = {z : ℂ | u ≤ z.re ∧ z.re ≤ u + 1 ∧ v ≤ z.im ∧ z.im ≤ v + 2})
        → (∀ (a : GaussianInt), P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a true) =
        convexHull ℝ (Set.range (fun i : Fin 4 => ![⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩, ⟨(2 *
        (a.re : ℝ) + 1) + 1, 2 * (a.im : ℝ)⟩, ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩, ⟨(2 *
        (a.re : ℝ) + 1) + 1, 2 * (a.im : ℝ) + 2⟩] i))) → (∀ (a : GaussianInt), ∀ (z : ℂ), (∀ j :
        Fin 3, 0 < (P4828T1Root a true j.succ).1 → (1 / ((P4828T1Root a true j.succ).1 : ℝ))
        ≤ dist z ((P4828T1Root a true j.succ).2 / ((P4828T1Root a true j.succ).1 : ℝ))) ↔ 1 ≤
        dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧ 1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ :
        GaussianInt) : ℂ)) → ∀ (a : GaussianInt), ∀ (z : ℂ), z ∈ P4984T1ClosedGap (2 * (a.re :
        ℝ)) (P4828T1Root a true) ↔
        2 * (a.re : ℝ) + 1 ≤ z.re ∧ z.re ≤ 2 * (a.re : ℝ) + 2 ∧
        2 * (a.im : ℝ) ≤ z.im ∧ z.im ≤ 2 * (a.im : ℝ) + 2 ∧
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := by
  classical
  intro rectHull hpolyPlus hdistPlus a z
  change (z ∈ P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a true) ∧
    ∀ j : Fin 3, 0 < (P4828T1Root a true j.succ).1 →
      (1 / ((P4828T1Root a true j.succ).1 : ℝ)) ≤
        dist z ((P4828T1Root a true j.succ).2 /
          ((P4828T1Root a true j.succ).1 : ℝ))) ↔ _
  rw [hpolyPlus a, rectHull, hdistPlus a z]
  simp only [Set.mem_ofPred_eq]
  ring_nf
  tauto

end RootGapLemmas

theorem P4984T1RootGaps :
    (∀ a : GaussianInt,
      P4984T1ClosedGap (2 * (a.re : Real)) (P4828T1Root a false) =
        {z : Complex |
          2 * (a.re : Real) ≤ z.re ∧ z.re ≤ 2 * (a.re : Real) + 1 ∧
          2 * (a.im : Real) ≤ z.im ∧ z.im ≤ 2 * (a.im : Real) + 2 ∧
          1 ≤ dist z ((1 + 2 * a : GaussianInt) : Complex) ∧
          1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)}) ∧
    (∀ a : GaussianInt,
      P4984T1ClosedGap (2 * (a.re : Real)) (P4828T1Root a true) =
        {z : Complex |
          2 * (a.re : Real) + 1 ≤ z.re ∧ z.re ≤ 2 * (a.re : Real) + 2 ∧
          2 * (a.im : Real) ≤ z.im ∧ z.im ≤ 2 * (a.im : Real) + 2 ∧
          1 ≤ dist z ((1 + 2 * a : GaussianInt) : Complex) ∧
          1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : Complex)}) ∧
    (∀ z : Complex, BandPackingExterior z →
      ∃ a : GaussianInt, ∃ side : Bool,
        z ∈ P4984T1ClosedGap (2 * (a.re : Real)) (P4828T1Root a side)) := by
-- BODY
  classical
  have rectHull (u v : ℝ) :
      convexHull ℝ (Set.range (fun i : Fin 4 =>
        ![⟨u, v⟩, ⟨u + 1, v⟩, ⟨u, v + 2⟩, ⟨u + 1, v + 2⟩] i)) =
        {z : ℂ | u ≤ z.re ∧ z.re ≤ u + 1 ∧ v ≤ z.im ∧ z.im ≤ v + 2} := RootGapLemmas.rectHull u v
  have hpolyMinus (a : GaussianInt) :
      P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a false) =
        convexHull ℝ (Set.range (fun i : Fin 4 =>
          ![⟨2 * (a.re : ℝ), 2 * (a.im : ℝ)⟩,
            ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩,
            ⟨2 * (a.re : ℝ), 2 * (a.im : ℝ) + 2⟩,
            ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩] i)) := RootGapLemmas.hpolyMinus a
  have hpolyPlus (a : GaussianInt) :
      P4909T1ParentPolygon (2 * (a.re : ℝ)) (P4828T1Root a true) =
        convexHull ℝ (Set.range (fun i : Fin 4 =>
          ![⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ)⟩,
            ⟨(2 * (a.re : ℝ) + 1) + 1, 2 * (a.im : ℝ)⟩,
            ⟨2 * (a.re : ℝ) + 1, 2 * (a.im : ℝ) + 2⟩,
            ⟨(2 * (a.re : ℝ) + 1) + 1, 2 * (a.im : ℝ) + 2⟩] i)) := RootGapLemmas.hpolyPlus a
  have hdistMinus (a : GaussianInt) (z : ℂ) :
      (∀ j : Fin 3, 0 < (P4828T1Root a false j.succ).1 →
        (1 / ((P4828T1Root a false j.succ).1 : ℝ)) ≤
          dist z ((P4828T1Root a false j.succ).2 /
            ((P4828T1Root a false j.succ).1 : ℝ))) ↔
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := RootGapLemmas.hdistMinus a z
  have hdistPlus (a : GaussianInt) (z : ℂ) :
      (∀ j : Fin 3, 0 < (P4828T1Root a true j.succ).1 →
        (1 / ((P4828T1Root a true j.succ).1 : ℝ)) ≤
          dist z ((P4828T1Root a true j.succ).2 /
            ((P4828T1Root a true j.succ).1 : ℝ))) ↔
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := RootGapLemmas.hdistPlus a z
  have hminusChar (a : GaussianInt) (z : ℂ) :
      z ∈ P4984T1ClosedGap (2 * (a.re : ℝ)) (P4828T1Root a false) ↔
        2 * (a.re : ℝ) ≤ z.re ∧ z.re ≤ 2 * (a.re : ℝ) + 1 ∧
        2 * (a.im : ℝ) ≤ z.im ∧ z.im ≤ 2 * (a.im : ℝ) + 2 ∧
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := RootGapLemmas.hminusChar
            rectHull hpolyMinus hdistMinus a z
  have hplusChar (a : GaussianInt) (z : ℂ) :
      z ∈ P4984T1ClosedGap (2 * (a.re : ℝ)) (P4828T1Root a true) ↔
        2 * (a.re : ℝ) + 1 ≤ z.re ∧ z.re ≤ 2 * (a.re : ℝ) + 2 ∧
        2 * (a.im : ℝ) ≤ z.im ∧ z.im ≤ 2 * (a.im : ℝ) + 2 ∧
        1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) ∧
        1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := RootGapLemmas.hplusChar
            rectHull hpolyPlus hdistPlus a z
  refine ⟨?_, ?_, ?_⟩
  · intro a
    ext z
    simpa only [Set.mem_ofPred_eq] using hminusChar a z
  · intro a
    ext z
    simpa only [Set.mem_ofPred_eq] using hplusChar a z
  · intro z hz
    let x : ℤ := Int.floor (z.re / 2)
    let y : ℤ := Int.floor (z.im / 2)
    let a : GaussianInt := ⟨x, y⟩
    have hxlo : 2 * (a.re : ℝ) ≤ z.re := by
      dsimp [a, x]
      have h := Int.floor_le (z.re / 2)
      nlinarith
    have hxhi : z.re < 2 * (a.re : ℝ) + 2 := by
      dsimp [a, x]
      have h := Int.lt_floor_add_one (z.re / 2)
      nlinarith
    have hylo : 2 * (a.im : ℝ) ≤ z.im := by
      dsimp [a, y]
      have h := Int.floor_le (z.im / 2)
      nlinarith
    have hyhi : z.im < 2 * (a.im : ℝ) + 2 := by
      dsimp [a, y]
      have h := Int.lt_floor_add_one (z.im / 2)
      nlinarith
    let C₁ : BandCircle := by
      refine ⟨⟨(1, 1 + 2 * a), ?_⟩, by norm_num⟩
      constructor
      · exact Or.inl (by norm_num)
      · refine ⟨![(1, 1 + 2 * a), (1, 1 + 2 * a + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)], SemiProperQuadruple.base a, ?_⟩
        exact ⟨0, by simp⟩
    let C₂ : BandCircle := by
      refine ⟨⟨(1, 1 + 2 * a + 2 * ⟨0, 1⟩), ?_⟩, by norm_num⟩
      constructor
      · exact Or.inl (by norm_num)
      · refine ⟨![(1, 1 + 2 * a), (1, 1 + 2 * a + 2 * ⟨0, 1⟩),
          (0, 1), (0, -1)], SemiProperQuadruple.base a, ?_⟩
        exact ⟨1, by simp⟩
    have hd₁ : 1 ≤ dist z ((1 + 2 * a : GaussianInt) : ℂ) := by
      have h := hz C₁
      simpa [BandPackingExterior, BandCircleEuclideanData, C₁] using h
    have hd₂ : 1 ≤ dist z ((1 + 2 * a + 2 * ⟨0, 1⟩ : GaussianInt) : ℂ) := by
      have h := hz C₂
      simpa [BandPackingExterior, BandCircleEuclideanData, C₂] using h
    by_cases hside : z.re ≤ 2 * (a.re : ℝ) + 1
    · refine ⟨a, false, ?_⟩
      apply (hminusChar a z).2
      exact ⟨hxlo, hside, hylo, hyhi.le, hd₁, hd₂⟩
    · have hleft : 2 * (a.re : ℝ) + 1 ≤ z.re := le_of_not_ge hside
      refine ⟨a, true, ?_⟩
      apply (hplusChar a z).2
      refine ⟨hleft, ?_, hylo, hyhi.le, hd₁, hd₂⟩
      linarith

end ApollonianSuperharmonic

end
