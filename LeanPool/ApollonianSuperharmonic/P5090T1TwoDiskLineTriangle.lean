/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P5090T1TwoDiskLineTriangle]

/-!
# P5090T1TwoDiskLineTriangle

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5090T1TwoDiskLineTriangle (a b u v : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b)
    (ht : dist (⟨a, u⟩ : ℂ) ⟨b, v⟩ = a + b)
    (hz : z ∈ convexHull ℝ
      ({⟨a, u⟩, ⟨b, v⟩, ⟨0, u⟩, ⟨0, v⟩} : Set ℂ))
    (hzA : a ≤ dist z (⟨a, u⟩ : ℂ))
    (hzB : b ≤ dist z (⟨b, v⟩ : ℂ)) :
    z ∈ convexHull ℝ
      ({⟨0, u⟩,
        (b / (a + b)) • (⟨a, u⟩ : ℂ) +
          (a / (a + b)) • (⟨b, v⟩ : ℂ), ⟨0, v⟩} : Set ℂ) := by
-- BODY
  classical
  let A : ℂ := ⟨a, u⟩
  let B : ℂ := ⟨b, v⟩
  let F : ℂ := ⟨0, u⟩
  let G : ℂ := ⟨0, v⟩
  have weights (A B F G z : ℂ)
      (hz : z ∈ convexHull ℝ ({A, B, F, G} : Set ℂ)) :
      ∃ α β φ γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ φ ∧ 0 ≤ γ ∧
        α + β + φ + γ = 1 ∧ z = α • A + β • B + φ • F + γ • G := by
    let T : Set ℂ := {x | ∃ α β φ γ : ℝ,
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ φ ∧ 0 ≤ γ ∧ α + β + φ + γ = 1 ∧
        x = α • A + β • B + φ • F + γ • G}
    have hT : Convex ℝ T := by
      intro x hx y hy s t hs ht hst
      obtain ⟨α, β, φ, γ, hα, hβ, hφ, hγ, hsum, rfl⟩ := hx
      obtain ⟨α', β', φ', γ', hα', hβ', hφ', hγ', hsum', rfl⟩ := hy
      refine ⟨s * α + t * α', s * β + t * β', s * φ + t * φ',
        s * γ + t * γ', by positivity, by positivity, by positivity,
        by positivity, ?_, ?_⟩
      · calc
          _ = s * (α + β + φ + γ) + t * (α' + β' + φ' + γ') := by ring
          _ = 1 := by rw [hsum, hsum']; linarith
      · module
    have hsub : ({A, B, F, G} : Set ℂ) ⊆ T := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨1, 0, 0, 0, by norm_num, le_rfl, le_rfl, le_rfl, by norm_num, by module⟩
      · exact ⟨0, 1, 0, 0, le_rfl, by norm_num, le_rfl, le_rfl, by norm_num, by module⟩
      · exact ⟨0, 0, 1, 0, le_rfl, le_rfl, by norm_num, le_rfl, by norm_num, by module⟩
      · exact ⟨0, 0, 0, 1, le_rfl, le_rfl, le_rfl, by norm_num, by norm_num, by module⟩
    exact (convexHull_min hsub hT) hz
  obtain ⟨α, β, φ, γ, hα, hβ, hφ, hγ, hsum, hx⟩ := weights A B F G z hz
  let s := β + γ
  let t := φ + (b / a) * γ
  let s' := α + φ
  let t' := γ + (a / b) * φ
  have hs : 0 ≤ s := add_nonneg hβ hγ
  have ht' : 0 ≤ t := by dsimp [t]; positivity
  have hs' : 0 ≤ s' := add_nonneg hα hφ
  have ht'' : 0 ≤ t' := by dsimp [t']; positivity
  have hαeq : α = 1 - β - φ - γ := by linarith
  have hconeA : z - A = s • (B - A) + t • (F - A) := by
    rw [hx, hαeq]
    apply Complex.ext
    · simp only [A, B, F, G, s, t, Complex.add_re, Complex.sub_re,
        Complex.smul_re, smul_eq_mul]
      field_simp; ring
    · simp only [A, B, F, G, s, t, Complex.add_im, Complex.sub_im,
        Complex.smul_im, smul_eq_mul]
      ring
  have hconeB : z - B = s' • (A - B) + t' • (G - B) := by
    rw [hx, hαeq]
    apply Complex.ext
    · simp only [A, B, F, G, s', t', hαeq, Complex.add_re, Complex.sub_re,
        Complex.smul_re, smul_eq_mul]
      field_simp; ring
    · simp only [A, B, F, G, s', t', hαeq, Complex.add_im, Complex.sub_im,
        Complex.smul_im, smul_eq_mul]
      ring
  have coneBound (X Y Z x : ℂ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (hx : x - X = s • (Y - X) + t • (Z - X)) :
      dist x X ≤ s * dist X Y + t * dist X Z := by
    rw [dist_eq_norm, hx]
    calc
      ‖s • (Y - X) + t • (Z - X)‖ ≤ ‖s • (Y - X)‖ + ‖t • (Z - X)‖ := norm_add_le _ _
      _ = s * dist X Y + t * dist X Z := by
        simp only [Complex.real_smul, Complex.norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg ht]
        rw [← dist_eq_norm, ← dist_eq_norm, dist_comm Y X, dist_comm Z X]
  have hAF : dist A F = a := by
    simp [A, F, Complex.dist_eq_re_im, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  have hBG : dist B G = b := by
    simp [B, G, Complex.dist_eq_re_im, Real.sqrt_sq_eq_abs, abs_of_pos hb]
  have houtA := hzA.trans (coneBound A B F z s t hs ht' hconeA)
  rw [ht, hAF] at houtA
  have houtB := hzB.trans (coneBound B A G z s' t' hs' ht'' hconeB)
  rw [dist_comm B A, ht, hBG] at houtB
  have hX : z.re = a + (b - a) * s - a * t := by
    have hh := congrArg Complex.re hconeA
    simp only [A, B, F, Complex.sub_re, Complex.add_re, Complex.smul_re,
      smul_eq_mul] at hh
    linarith
  have hY : z.im = (1 - s) * u + s * v := by
    have hh := congrArg Complex.im hconeA
    simp only [A, B, F, Complex.sub_im, Complex.add_im, Complex.smul_im,
      smul_eq_mul] at hh
    linarith
  have hXpos : 0 ≤ z.re := by
    rw [hx]
    simp only [A, B, F, G, Complex.add_re, Complex.smul_re, smul_eq_mul]
    positivity
  have hsrelation : s' = 1 - s := by dsimp [s, s']; linarith
  have htrelation : t' * b = a * t := by
    dsimp [t', t]
    field_simp; ring
  have hXG : z.re ≤ 2 * b * s := by nlinarith only [houtA, hX]
  have hXF : z.re ≤ 2 * a * (1 - s) := by
    rw [hsrelation, htrelation] at houtB
    nlinarith only [houtB, hX]
  let μF := 1 - s - z.re / (2 * a)
  let μK := (a + b) * z.re / (2 * a * b)
  let μG := s - z.re / (2 * b)
  have hμF : 0 ≤ μF := by
    dsimp [μF]
    have hh : z.re / (2 * a) ≤ 1 - s :=
      (div_le_iff₀ (by positivity : 0 < 2 * a)).mpr (by nlinarith only [hXF])
    linarith
  have hμK : 0 ≤ μK := by dsimp [μK]; positivity
  have hμG : 0 ≤ μG := by
    dsimp [μG]
    have hh : z.re / (2 * b) ≤ s :=
      (div_le_iff₀ (by positivity : 0 < 2 * b)).mpr (by nlinarith only [hXG])
    linarith
  have hμsum : μF + μK + μG = 1 := by
    dsimp [μF, μK, μG]
    field_simp; ring
  have hcomb : μF • F + μK • ((b / (a + b)) • A + (a / (a + b)) • B) + μG • G = z := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      dsimp [A, B, F, G, μF, μK, μG]
      field_simp; ring
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      dsimp [A, B, F, G, μF, μK, μG]
      rw [hY]
      field_simp; ring
  apply mem_convexHull_of_exists_fintype (w := ![μF, μK, μG])
    (z := ![F, (b / (a + b)) • A + (a / (a + b)) • B, G])
  · intro i
    fin_cases i <;> assumption
  · simpa [Fin.sum_univ_succ, add_assoc] using hμsum
  · intro i
    fin_cases i <;> simp [A, B, F, G]
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero]
    simpa only [add_assoc] using hcomb

end ApollonianSuperharmonic

end
