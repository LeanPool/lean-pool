/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec162QuantitativeInequality.Setup

/-!
# Trilinear Hilbert transform: TsideF_le
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def TsideFLeStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ c₀)
    (P : ℕ)
    (K : ℕ)
    (u : Option (Fin (4 : ℕ)))
    (Lp : ℕ)
    (Jm : ℕ)
    (E : ℝ)
    (cc : ℕ)
    (kk : ℝ)
    (Vl : Fin (4 : ℕ) → ℝ)
    (ρ : ℝ)
    (V0 : ℝ)
    (_ : A.S = (2 : ℝ))
    (_ : (1 : ℕ) ≤ P)
    (_ : (1 : ℕ) ≤ Lp)
    (_ : (0 : ℝ) ≤ E)
    (_ : (0 : ℝ) < ρ),
  let G0 : ℝ :=
    Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2
      : ℝ) * kk)) ^ (2 : ℕ))
  let R : ℝ :=
    dyadicGridLength A.G A.R.1
  let L0 : ℝ :=
    localFormUniformConstant κ
  ∀ (_ : (0 : ℝ) < R)
    (_ : (0 : ℝ) ≤ L0)
    (_ : (0 : ℝ) ≤ V0),
  let W : ℝ :=
    G0 + E + V0 + (1 : ℝ)
  ∀ (_ : E ≤ W),
  let Y : ℝ :=
    ((1 : ℝ) + L0) ^ (2 : ℕ) * (↑Lp : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑Jm : ℝ)) ^ (2 : ℕ) *
      ((1 : ℝ) + (↑K : ℝ)) ^ (2 : ℕ) * W
  ∀ (_ : Y = ((1 : ℝ) + L0) ^ (2 : ℕ) * (↑Lp : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑Jm : ℝ)) ^ (2 : ℕ)
      * ((1 : ℝ) + (↑K : ℝ)) ^ (2 : ℕ) * W)
    (_ : L0 ^ (2 : ℕ) ≤ ((1 : ℝ) + L0) ^ (2 : ℕ))
    (_ : (1 : ℝ) ≤ (↑Lp : ℝ) ^ (4 : ℕ))
    (_ : (1 : ℝ) ≤ ((1 : ℝ) + (↑Jm : ℝ)) ^ (2 : ℕ))
    (_ : (1 : ℝ) ≤ ((1 : ℝ) + (↑K : ℝ)) ^ (2 : ℕ)),
  let Bs : ℝ :=
    ∑ l : Fin (4 : ℕ), if u = some l then (2 : ℝ) * ((4 : ℝ) * E * R) else (2 : ℝ) *
      ((↑K : ℝ) * ((20 : ℝ) * G0 + (32 : ℝ)) * R) + (2 : ℝ) * ((↑K : ℝ) * (Vl l * R))
  ∀ (_ : Bs ≤ (4 : ℝ) * ((200 : ℝ) * ((1 : ℝ) + (↑K : ℝ)) * W * R))
    (_ : Bs ≤ (800 : ℝ) * Y * R),
  let g : ℝ :=
    (↑K : ℝ) * (G0 * ((4 : ℝ) * R))
  let frz : ℝ :=
    ((2 : ℝ) * √(1 : ℝ)) ^ (2 : ℕ) * (((64 : ℝ) + (8 : ℝ) * (↑K : ℝ)) * (g + (↑P : ℝ) *
      g) + ((1 : ℝ) + (↑K : ℝ)) * g)
  ∀ (_ : ((2 : ℝ) / (↑P : ℝ) * L0) ^ (2 : ℕ) * (6 : ℝ) * frz ≤ (49536 : ℝ) * L0 ^ (2 : ℕ) *
      ((1 : ℝ) + (↑K : ℝ)) ^ (2 : ℕ) * W * R),
  TsideF A P K u Lp Jm (1 : ℝ) E cc kk Vl ρ ≤ (10 : ℝ) ^ (14 : ℕ) * ((1 : ℝ) + L0) ^
    (2 : ℕ) * (↑Lp : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑Jm : ℝ)) ^ (2 : ℕ) * ((1 : ℝ) + (↑K :
    ℝ)) ^ (2 : ℕ) * W / ρ




private theorem TsideF_le_stage_1 : TsideFLeStage1Statement := by
  classical
  intro κ c₀ A P K u Lp Jm E cc kk Vl ρ V0 hS hP hLp hE hρ G0 R L0 hRp hL00 hV0 W hEW Y hY hLL
    hLp4 hJ1 hK1 Bs hBs1 hBsY g frz hfrz1
  set! Z1 := (Lp : ℝ) ^ 2 * (1 + (Jm : ℝ)) * (1 + L0) ^ 2 * (1 + (K : ℝ)) ^ 2 * W with hZ1
  have hZ10 : 0 ≤ Z1 := by positivity
  have hYZ : Y = (Lp : ℝ) ^ 2 * (1 + (Jm : ℝ)) * Z1 := by rw [hY, hZ1]; ring
  set! X := (2 / (P : ℝ) * L0) ^ 2 * 6 * ((Lp : ℝ) * Lp * ((Jm : ℝ) * 5) * frz) with hXd
  have hX : X ≤ 247680 * Z1 * R := by
    have e : X = (Lp : ℝ) ^ 2 * (5 * (Jm : ℝ)) * ((2 / (P : ℝ) * L0) ^ 2 * 6 * frz) := by
      rw [hXd]; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hfrz1 (show 0 ≤ (Lp : ℝ) ^ 2 * (5 * (Jm : ℝ)) by
      positivity)
    refine h1.trans ?_
    have h2 : (Lp : ℝ) ^ 2 * (5 * (Jm : ℝ)) * (49536 * L0 ^ 2 * (1 + (K : ℝ)) ^ 2 * W * R) =
        247680 * ((Lp : ℝ) ^ 2 * (Jm : ℝ) * L0 ^ 2 * ((1 + (K : ℝ)) ^ 2 * W)) * R := by ring
    rw [h2]
    have h3 : (Lp : ℝ) ^ 2 * (Jm : ℝ) * L0 ^ 2 * ((1 + (K : ℝ)) ^ 2 * W) ≤ Z1 := by
      rw [hZ1]
      have hJ : (Jm : ℝ) ≤ 1 + (Jm : ℝ) := by linarith only
      have hA : (Lp : ℝ) ^ 2 * (Jm : ℝ) * L0 ^ 2 ≤ (Lp : ℝ) ^ 2 * (1 + (Jm : ℝ)) *
          (1 + L0) ^ 2 := mul_le_mul (mul_le_mul_of_nonneg_left hJ (by positivity)) hLL
            (by positivity) (by positivity)
      have hB0 : 0 ≤ (1 + (K : ℝ)) ^ 2 * W := by positivity
      have := mul_le_mul_of_nonneg_right hA hB0
      calc _ ≤ (Lp : ℝ) ^ 2 * (1 + (Jm : ℝ)) * (1 + L0) ^ 2 * ((1 + (K : ℝ)) ^ 2 * W) := this
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_right h3 hRp.le
    linarith only [this]
  have hX0 : 0 ≤ X := by positivity
  -- the basic-side term
  set! B₀ := max (2 * Real.sqrt 1) A.S with hB₀
  have hB₀2 : B₀ = 2 := by rw [hB₀, hS, Real.sqrt_one]; norm_num
  have hU1 : (Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) ≤ 128 * Z1 * R := by
    rw [hB₀2]
    have hA : (Lp : ℝ) ^ 2 * L0 ^ 2 * E ≤ Z1 := by
      rw [hZ1]
      have h1 : (Lp : ℝ) ^ 2 * L0 ^ 2 ≤ (Lp : ℝ) ^ 2 * (1 + L0) ^ 2 :=
        mul_le_mul_of_nonneg_left hLL (by positivity)
      have h2 : (1 : ℝ) ≤ (1 + (Jm : ℝ)) * (1 + (K : ℝ)) ^ 2 :=
        one_le_mul_of_one_le_of_one_le (by linarith only) hK1
      have h3 : (Lp : ℝ) ^ 2 * L0 ^ 2 * E ≤ (Lp : ℝ) ^ 2 * (1 + L0) ^ 2 * W :=
        mul_le_mul h1 hEW hE (by positivity)
      calc (Lp : ℝ) ^ 2 * L0 ^ 2 * E ≤ (Lp : ℝ) ^ 2 * (1 + L0) ^ 2 * W := h3
        _ ≤ (Lp : ℝ) ^ 2 * (1 + L0) ^ 2 * W * ((1 + (Jm : ℝ)) * (1 + (K : ℝ)) ^ 2) :=
          le_mul_of_one_le_right (by positivity) h2
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_right hA hRp.le
    linarith only [this]
  have hU0 : 0 ≤ (Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) := by positivity
  have hJ5 : 2 * (1 + 5 * (Jm : ℝ)) ≤ 10 * (1 + (Jm : ℝ)) := by linarith only
  have hJ50 : 0 ≤ 2 * (1 + 5 * (Jm : ℝ)) := by positivity
  have hLJ : (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) ≤ 10 * ((Lp : ℝ) ^ 2 * (1 + (Jm : ℝ))) := by
    have := mul_le_mul_of_nonneg_left hJ5 (sq_nonneg (Lp : ℝ))
    linarith only [this]
  -- the first three-side term
  have hT1 : (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) *
      ((Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) + X) ≤ 2478080 * Y * R := by
    have h1 : (Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) + X ≤ 247808 * Z1 * R := by
      linarith only [hX, hU1]
    have := mul_le_mul hLJ h1 (by positivity) (by positivity)
    calc _ ≤ 10 * ((Lp : ℝ) ^ 2 * (1 + (Jm : ℝ))) * (247808 * Z1 * R) := this
      _ = _ := by rw [hYZ]; ring
  -- the second three-side term
  have hT2 : (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) * X ≤ 2476800 * Y * R := by
    have := mul_le_mul hLJ hX (by positivity) (by positivity)
    calc _ ≤ 10 * ((Lp : ℝ) ^ 2 * (1 + (Jm : ℝ))) * (247680 * Z1 * R) := this
      _ = _ := by rw [hYZ]; ring
  have hT3 : 2 * (L0 * B₀) ^ 2 * Bs ≤ 6400 * Y * R := by
    rw [hB₀2]
    have hA : L0 ^ 2 * ((1 + (K : ℝ)) * W) ≤ Y := by
      rw [hY]
      have h2 : (1 : ℝ) ≤ (Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ)) :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hLp4 hJ1) (by linarith only)
      have h3 : L0 ^ 2 * ((1 + (K : ℝ)) * W) ≤ (1 + L0) ^ 2 * ((1 + (K : ℝ)) * W) :=
        mul_le_mul_of_nonneg_right hLL (by positivity)
      calc L0 ^ 2 * ((1 + (K : ℝ)) * W) ≤ (1 + L0) ^ 2 * ((1 + (K : ℝ)) * W) := h3
        _ ≤ (1 + L0) ^ 2 * ((1 + (K : ℝ)) * W) *
            ((Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ))) :=
          le_mul_of_one_le_right (by positivity) h2
        _ = _ := by ring
    have h1 : 2 * (L0 * 2) ^ 2 * Bs ≤ 8 * L0 ^ 2 * (4 * (200 * (1 + (K : ℝ)) * W * R)) := by
      have := mul_le_mul_of_nonneg_left hBs1 (show 0 ≤ 8 * L0 ^ 2 by positivity)
      linarith only [this]
    have h2 := mul_le_mul_of_nonneg_right hA hRp.le
    linarith only [h1, h2]
  -- assembly
  have hB3 : 2 * (36 * 256 * 256 * ((Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) *
      ((Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) + X))) +
      2 * (36 * 256 * 256 * (2 * (L0 * B₀) ^ 2 * Bs +
        (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) * X)) ≤ 4718592 * 4961280 * Y * R := by
    linarith only [hT1, hT2, hT3]
  have e : TsideF A P K u Lp Jm 1 E cc kk Vl ρ = (Bs / R + (2 * (36 * 256 * 256 *
      ((Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) *
      ((Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) + X))) +
      2 * (36 * 256 * 256 * (2 * (L0 * B₀) ^ 2 * Bs +
        (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) * X))) / R) / ρ := rfl
  rw [e, ← add_div, div_div, div_le_iff₀ (by positivity)]
  have hfin : Bs + (2 * (36 * 256 * 256 * ((Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) *
      ((Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) + X))) +
      2 * (36 * 256 * 256 * (2 * (L0 * B₀) ^ 2 * Bs +
        (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) * X))) ≤ 10 ^ 14 * Y * R := by
    have hYR : 0 ≤ Y * R := by positivity
    calc _ ≤ 800 * Y * R + 4718592 * 4961280 * Y * R := add_le_add hBsY hB3
      _ = (800 + 4718592 * 4961280) * (Y * R) := by ring
      _ ≤ 10 ^ 14 * (Y * R) := mul_le_mul_of_nonneg_right (by norm_num) hYR
      _ = 10 ^ 14 * Y * R := by ring
  calc _ ≤ 10 ^ 14 * Y * R := hfin
    _ = _ := by
      rw [hY]
      field_simp


/-- A crude polynomial bound for the side cap `T_c` at `C_F = 1`, `S = 2`:
`T_c ≤ 10¹⁴ (1 + L₀)² L_p⁴ (1 + J_m)² (1 + K)² (G₀ + E + V₀ + 1) / ρ`. -/
theorem TsideF_le {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀) (P K : ℕ)
    (u : Option (Fin 4)) (Lp Jm : ℕ) {E : ℝ} (cc : ℕ) (kk : ℝ) (Vl : Fin 4 → ℝ) {ρ V0 : ℝ}
    (hS : A.S = 2) (hP : 1 ≤ P) (hLp : 1 ≤ Lp) (hE : 0 ≤ E) (hVl : ∀ l, 0 ≤ Vl l ∧ Vl l ≤ V0)
    (hρ : 0 < ρ) :
    TsideF A P K u Lp Jm 1 E cc kk Vl ρ ≤ 10 ^ 14 * (1 + localFormUniformConstant κ) ^ 2 *
      (Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ)) ^ 2 *
      (Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
        (1 + Real.log (2 * kk)) ^ 2) + E + V0 + 1) / ρ := by
  set G0 := Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2) with hG0
  set R := dyadicGridLength A.G A.R.1 with hR
  set L0 := localFormUniformConstant κ with hL0
  have hRp : 0 < R := dyadicGridLength_pos A.G A.R.1
  have hG1 : 1 ≤ G0 := Real.one_le_exp (by positivity)
  have hL00 : 0 ≤ L0 := localFormUniformConstant_nonneg κ
  have hV0 : 0 ≤ V0 := le_trans (hVl 0).1 (hVl 0).2
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hJ0 : (0 : ℝ) ≤ Jm := Nat.cast_nonneg Jm
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hLp1 : (1 : ℝ) ≤ Lp := by exact_mod_cast hLp
  set W := G0 + E + V0 + 1 with hW
  have hW1 : 1 ≤ W := by linarith only [hE, hG1, hV0]
  have hEW : E ≤ W := by linarith only [hG1, hV0]
  have hGW : G0 ≤ W := by linarith only [hE, hV0]
  have hVW : V0 ≤ W := by linarith only [hE, hG1]
  have hWR : 0 ≤ W * R := by positivity
  -- the common factor
  set! Y := (1 + L0) ^ 2 * (Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ)) ^ 2 * W with hY
  have hL1 : 1 ≤ (1 + L0) ^ 2 := one_le_pow₀ (by linarith only [hL00])
  have hLL : L0 ^ 2 ≤ (1 + L0) ^ 2 := pow_le_pow_left₀ hL00 (by linarith only) 2
  have hLp4 : (1 : ℝ) ≤ (Lp : ℝ) ^ 4 := one_le_pow₀ hLp1
  have hLp24 : (Lp : ℝ) ^ 2 ≤ (Lp : ℝ) ^ 4 := pow_le_pow_right₀ hLp1 (by norm_num)
  have hJ1 : 1 ≤ (1 + (Jm : ℝ)) ^ 2 := one_le_pow₀ (by linarith only)
  have hJJ : 1 + (Jm : ℝ) ≤ (1 + (Jm : ℝ)) ^ 2 := le_self_pow₀ (by linarith only) (by norm_num)
  have hK1 : 1 ≤ (1 + (K : ℝ)) ^ 2 := one_le_pow₀ (by linarith only)
  have hKK : 1 + (K : ℝ) ≤ (1 + (K : ℝ)) ^ 2 := le_self_pow₀ (by linarith only) (by norm_num)
  have hY0 : 0 ≤ Y := by positivity
  -- `Y` dominates each of its factors times `W`
  have hYW : W ≤ Y := by
    have : (1 : ℝ) ≤ (1 + L0) ^ 2 * (Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ)) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hL1 hLp4) hJ1) hK1
    have h := mul_le_mul_of_nonneg_right this (show 0 ≤ W by linarith only [hW1])
    rw [one_mul] at h
    exact h
  -- the side budget
  set! Bs := ∑ l : Fin 4, if u = some l then 2 * (4 * E * R) else
    2 * ((K : ℝ) * (20 * G0 + 32) * R) + 2 * ((K : ℝ) * (Vl l * R)) with hBs
  have hBs1 : Bs ≤ 4 * (200 * (1 + (K : ℝ)) * W * R) := by
    rw [hBs, show 4 * (200 * (1 + (K : ℝ)) * W * R) = ∑ _l : Fin 4, 200 * (1 + (K : ℝ)) * W * R
      by simp]
    refine Finset.sum_le_sum fun l _ => ?_
    have hv := hVl l
    split_ifs
    · have h1 : E * R ≤ W * R := mul_le_mul_of_nonneg_right hEW hRp.le
      have h2 : 0 ≤ (K : ℝ) * (W * R) := mul_nonneg hK0 hWR
      linarith only [h1, h2, hWR]
    · have h1 : (K : ℝ) * (20 * G0 + 32) * R ≤ (K : ℝ) * (52 * W) * R := by
        have : 20 * G0 + 32 ≤ 52 * W := by linarith only [hE, hG1, hV0]
        gcongr
      have h2 : (K : ℝ) * (Vl l * R) ≤ (K : ℝ) * (W * R) := by
        have : Vl l ≤ W := hv.2.trans hVW
        gcongr
      have h3 : 0 ≤ (K : ℝ) * (W * R) := mul_nonneg hK0 hWR
      linarith only [h1, h2, h3, hWR]
  have hBsY : Bs ≤ 800 * Y * R := by
    have h1 : (1 + (K : ℝ)) * W ≤ Y := by
      have : (1 : ℝ) ≤ (1 + L0) ^ 2 * (Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ)) :=
        by
          have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
            (one_le_mul_of_one_le_of_one_le hL1 hLp4) hJ1) (show (1 : ℝ) ≤ 1 + K by linarith only)
          exact this
      have e : Y = (1 + L0) ^ 2 * (Lp : ℝ) ^ 4 * (1 + (Jm : ℝ)) ^ 2 * (1 + (K : ℝ)) *
          ((1 + (K : ℝ)) * W) := by rw [hY]; ring
      rw [e]
      have : 0 ≤ (1 + (K : ℝ)) * W := by positivity
      have h := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ 1 by norm_num)
      have h' := mul_le_mul_of_nonneg_right ‹(1 : ℝ) ≤ _› this
      linarith only [h']
    have h2 := mul_le_mul_of_nonneg_right h1 hRp.le
    linarith only [hBs1, h2]
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun l _ => by
    split_ifs
    · positivity
    · have := (hVl l).1; positivity
  -- the frozen complements
  set! g := (K : ℝ) * (G0 * (4 * R)) with hg
  have hg0 : 0 ≤ g := by positivity
  set! frz := (2 * Real.sqrt 1) ^ 2 * ((64 + 8 * (K : ℝ)) * (g + (P : ℝ) * g) +
    (1 + (K : ℝ)) * g) with hfrz
  have hfrz0 : 0 ≤ frz := by positivity
  have hPp : 0 < (P : ℝ) := by linarith only [hP1]
  have hQ : (64 + 8 * (K : ℝ)) * (1 + P) + (1 + K) ≤ (129 + 17 * (K : ℝ)) * (P : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) + P ≤ 2 * (P : ℝ) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.2 hP1) (show (0 : ℝ) ≤ 2 * P + 1 by linarith only)]
    have h2 : (1 : ℝ) ≤ (P : ℝ) ^ 2 := one_le_pow₀ hP1
    have h3 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 64 + 8 * K by linarith only)
    have h4 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 + K by linarith only)
    linarith only [h3, h4]
  have hfrz1 : (2 / (P : ℝ) * L0) ^ 2 * 6 * frz ≤ 49536 * L0 ^ 2 * (1 + (K : ℝ)) ^ 2 * W * R := by
    have e : (2 / (P : ℝ) * L0) ^ 2 * 6 * frz = 96 * L0 ^ 2 * g *
        (((64 + 8 * (K : ℝ)) * (1 + P) + (1 + K)) / (P : ℝ) ^ 2) := by
      rw [hfrz, Real.sqrt_one]
      field_simp
      ring
    rw [e]
    have h1 : ((64 + 8 * (K : ℝ)) * (1 + P) + (1 + K)) / (P : ℝ) ^ 2 ≤ 129 + 17 * (K : ℝ) := by
      rw [div_le_iff₀ (by positivity)]; exact hQ
    have h2 : 96 * L0 ^ 2 * g * (((64 + 8 * (K : ℝ)) * (1 + P) + (1 + K)) / (P : ℝ) ^ 2) ≤
        96 * L0 ^ 2 * g * (129 + 17 * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans ?_
    have h3 : (K : ℝ) * (129 + 17 * K) ≤ 129 * (1 + (K : ℝ)) ^ 2 := by
      nlinarith only [hK0, sq_nonneg (K : ℝ)]
    have h4 : G0 * R ≤ W * R := mul_le_mul_of_nonneg_right hGW hRp.le
    have e2 : 96 * L0 ^ 2 * g * (129 + 17 * (K : ℝ)) =
        384 * L0 ^ 2 * ((K : ℝ) * (129 + 17 * K)) * (G0 * R) := by rw [hg]; ring
    rw [e2]
    calc 384 * L0 ^ 2 * ((K : ℝ) * (129 + 17 * K)) * (G0 * R)
        ≤ 384 * L0 ^ 2 * (129 * (1 + (K : ℝ)) ^ 2) * (W * R) := by
          gcongr
      _ = 49536 * L0 ^ 2 * (1 + (K : ℝ)) ^ 2 * W * R := by ring
  expose_names
  exact @TsideF_le_stage_1 κ c₀ A P K u Lp Jm E cc kk Vl ρ V0 hS hP hLp hE hρ hRp hL00 hV0 hEW hY
    hLL hLp4 hJ1 hK1 hBs1 hBsY hfrz1

/-- A power with exponent in `[0, 1]` of a nonnegative number is at most `1 + x`. -/
theorem rpow_le_one_add {x a : ℝ} (hx : 0 ≤ x) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : x ^ a ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_le_one hx h ha0]
  · have := Real.rpow_le_rpow_of_exponent_le h ha1
    rw [Real.rpow_one] at this
    linarith

/-- The two-side cap at `C_F = 1`: `T₂ ≤ 4 (K (20 G₀ + 32) + K V₀) / ρ₂`. -/
theorem T2F_le (K : ℕ) (u : Option (Fin 4)) (cc : ℕ) (kk : ℝ) (Vl : Fin 4 → ℝ) {ρ₂ V0 : ℝ}
    (hVl : ∀ l, 0 ≤ Vl l ∧ Vl l ≤ V0) (hρ : 0 < ρ₂) :
    T2F K u cc kk Vl ρ₂ ≤ 4 * ((K : ℝ) * (20 * Real.exp ((4096 * (cc + 1) *
      (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) * (1 + Real.log (2 * kk)) ^ 2) + 32) +
        K * V0) / ρ₂ := by
  unfold T2F
  refine div_le_div_of_nonneg_right ?_ hρ.le
  set G0 := Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hG0 : 0 ≤ G0 := (Real.exp_pos _).le
  have hV0 : 0 ≤ V0 := le_trans (hVl 0).1 (hVl 0).2
  calc ∑ l : Fin 4, (if u = some l then 0 else (K : ℝ) * (20 * G0 + 32) + K * Vl l)
      ≤ ∑ _l : Fin 4, ((K : ℝ) * (20 * G0 + 32) + K * V0) := by
        refine Finset.sum_le_sum fun l _ => ?_
        have h1 : (K : ℝ) * Vl l ≤ K * V0 := mul_le_mul_of_nonneg_left (hVl l).2 hK0
        have h2 : 0 ≤ (K : ℝ) * (20 * G0 + 32) := by positivity
        have h3 : 0 ≤ (K : ℝ) * V0 := by positivity
        split_ifs
        · linarith only [h2, h3]
        · linarith only [h1]
    _ = 4 * ((K : ℝ) * (20 * G0 + 32) + K * V0) := by simp; ring

/-- `log₂` of the integer part of `x ≥ 1`, as a natural logarithm, is at most `2 log x`. -/
theorem natLog_floor_le {x : ℝ} (hx : 1 ≤ x) :
    ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ 2 * Real.log x := by
  have h1 : ((Nat.log 2 ⌊x⌋₊ : ℕ) : ℝ) ≤ Real.logb 2 (⌊x⌋₊ : ℝ) := by
    exact_mod_cast Real.natLog_le_logb ⌊x⌋₊ 2
  have hf1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    exact_mod_cast this
  have h2 : Real.logb 2 (⌊x⌋₊ : ℝ) ≤ Real.logb 2 x :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith only [hf1]) (Nat.floor_le (by linarith))
  exact h1.trans (h2.trans (logb_two_le_two_log hx))

/-- The number of upper heights is at most `J + 1`. -/
theorem card_upperHeights_le (J : ℕ) (δ : ℝ) :
    ((ModeComponents.upperHeights J δ).card : ℝ) ≤ J + 1 := by
  unfold ModeComponents.upperHeights
  have := (Finset.card_filter_le (Finset.range (J + 1))
    (fun h => ⌈4 * δ * J⌉₊ ≤ h)).trans_eq (Finset.card_range (J + 1))
  exact_mod_cast this

/-- The number of role types is at most `(3B)^8` when `log D_* ≤ B`, `B ≥ 1`. -/
theorem card_fourTypesF_le (S : ModeSchedule) {B : ℝ} (hB : 1 ≤ B) (hD1 : 1 ≤ S.Dstar)
    (hD : Real.log S.Dstar ≤ B) : ((fourTypesF S).card : ℝ) ≤ (3 * B) ^ 8 := by
  unfold fourTypesF
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.card_product, Finset.card_range]
  have h := natLog_floor_le hD1
  have ha : ((Nat.log 2 ⌊S.Dstar⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * B := by
    push_cast; linarith only [hB, hD, h]
  have : (((Nat.log 2 ⌊S.Dstar⌋₊ + 1) * (Nat.log 2 ⌊S.Dstar⌋₊ + 1)) ^ 4 : ℕ) =
      (Nat.log 2 ⌊S.Dstar⌋₊ + 1) ^ 8 := by ring
  rw [this]
  push_cast
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast ha) 8

/-- The four-core frequency constant of a schedule with `D_*, H ≥ 1` is nonnegative. -/
theorem fourCcF_nonneg (S : ModeSchedule) (hD1 : 1 ≤ S.Dstar) (hH1 : 1 ≤ S.H) :
    0 ≤ fourCcF S := by
  unfold fourCcF
  have hlog0 : 0 ≤ Real.log (288 * (S.Dstar ^ 5 * S.H)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ S.Dstar ^ 5 * S.H := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1) hH1
    linarith only [this])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 ≤ Real.log ((S.dmax : ℝ) + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ S.dmax := Nat.cast_nonneg _
    linarith only)
  have h1 : 0 ≤ 32 * ((S.dmax : ℝ) + 5) ^ 4 * (Real.log (288 * (S.Dstar ^ 5 * S.H)) +
    Real.log 2 + 1) := by positivity
  have h2 : 0 ≤ 1 + (Real.log 2 + 2 * Real.log ((S.dmax : ℝ) + 1) + 1) / Real.log 2 := by
    positivity
  exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg h1 _)) (Real.rpow_nonneg h2 _)

/-- The four-core frequency constant of a schedule is at most `10^{28} B^{21}` when
`d_max + 5`, `log D_*` and `log H` are at most `B`. -/
theorem fourCcF_le (S : ModeSchedule) {B : ℝ} (hB : 2 ≤ B) (hd : (S.dmax : ℝ) + 5 ≤ B)
    (hD1 : 1 ≤ S.Dstar) (hH1 : 1 ≤ S.H) (hD : Real.log S.Dstar ≤ B)
    (hH : Real.log S.H ≤ B) : fourCcF S ≤ 10 ^ 28 * B ^ 21 := by
  unfold fourCcF
  have hd0 : (0 : ℝ) ≤ S.dmax := Nat.cast_nonneg _
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hl2' : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  -- the main factor
  have hlog : Real.log (288 * (S.Dstar ^ 5 * S.H)) ≤ 288 + 6 * B := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 288 by norm_num)
    push_cast
    linarith only [hD, hH, this]
  have hD0 : 0 ≤ Real.log S.Dstar := Real.log_nonneg hD1
  have hH0 : 0 ≤ Real.log S.H := Real.log_nonneg hH1
  have hlog0 : 0 ≤ Real.log (288 * (S.Dstar ^ 5 * S.H)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ S.Dstar ^ 5 * S.H := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1) hH1
    linarith only [this])
  set x := 32 * ((S.dmax : ℝ) + 5) ^ 4 * (Real.log (288 * (S.Dstar ^ 5 * S.H)) + Real.log 2 + 1)
    with hx
  have hx1 : 1 ≤ x := by
    have h5 : (1 : ℝ) ≤ ((S.dmax : ℝ) + 5) ^ 4 := one_le_pow₀ (by linarith only)
    have h6 : (1 : ℝ) ≤ Real.log (288 * (S.Dstar ^ 5 * S.H)) + Real.log 2 + 1 := by
      linarith only [hl2, hlog0]
    have := one_le_mul_of_one_le_of_one_le h5 h6
    rw [hx]; nlinarith only [this]
  have hxB : x ≤ 4832 * B ^ 5 := by
    have h5 : ((S.dmax : ℝ) + 5) ^ 4 ≤ B ^ 4 := pow_le_pow_left₀ (by linarith only) hd 4
    have h6 : Real.log (288 * (S.Dstar ^ 5 * S.H)) + Real.log 2 + 1 ≤ 151 * B := by
      linarith only [hB, hl2', hlog]
    have h7 := mul_le_mul h5 h6 (by linarith only [hl2, hlog0]) (by positivity)
    rw [hx]
    calc 32 * ((S.dmax : ℝ) + 5) ^ 4 * (Real.log (288 * (S.Dstar ^ 5 * S.H)) + Real.log 2 + 1)
        = 32 * (((S.dmax : ℝ) + 5) ^ 4 *
          (Real.log (288 * (S.Dstar ^ 5 * S.H)) + Real.log 2 + 1)) := by ring
      _ ≤ 32 * (B ^ 4 * (151 * B)) := mul_le_mul_of_nonneg_left h7 (by norm_num)
      _ = 4832 * B ^ 5 := by ring
  have hx4 : x ^ (15 / 4 : ℝ) ≤ 4832 ^ 4 * B ^ 20 := by
    calc x ^ (15 / 4 : ℝ) ≤ x ^ (4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x ^ 4 := by norm_cast
      _ ≤ (4832 * B ^ 5) ^ 4 := pow_le_pow_left₀ (by linarith only [hx1]) hxB 4
      _ = 4832 ^ 4 * B ^ 20 := by ring
  -- the last factor
  set y := 1 + (Real.log 2 + 2 * Real.log ((S.dmax : ℝ) + 1) + 1) / Real.log 2 with hy
  have hlogd : Real.log ((S.dmax : ℝ) + 1) ≤ S.dmax := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < S.dmax + 1 by positivity)
    linarith only [this]
  have hlogd0 : 0 ≤ Real.log ((S.dmax : ℝ) + 1) := Real.log_nonneg (by linarith only)
  have hy1 : 1 ≤ y := by
    rw [hy]
    have : 0 ≤ (Real.log 2 + 2 * Real.log ((S.dmax : ℝ) + 1) + 1) / Real.log 2 := by positivity
    linarith only [this]
  have hyB : y ≤ 6 * B := by
    rw [hy]
    have h : (Real.log 2 + 2 * Real.log ((S.dmax : ℝ) + 1) + 1) / Real.log 2 ≤
        2 * (Real.log 2 + 2 * Real.log ((S.dmax : ℝ) + 1) + 1) := by
      rw [div_le_iff₀ (by linarith only [hl2])]
      nlinarith only [hl2, hlogd0, Real.log_two_gt_d9]
    linarith only [hd, hl2', hlogd, h]
  have hy4 : y ^ (1 / 4 : ℝ) ≤ 6 * B := by
    calc y ^ (1 / 4 : ℝ) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
      _ = y := Real.rpow_one y
      _ ≤ 6 * B := hyB
  have hc : (3 * 10 ^ 11 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 * 10 ^ 11 := by
    calc (3 * 10 ^ 11 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 * 10 ^ 11 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 * 10 ^ 11 := Real.rpow_one _
  have hc0 : 0 ≤ (3 * 10 ^ 11 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  have hx0 : 0 ≤ x ^ (15 / 4 : ℝ) := by positivity
  have hy0 : 0 ≤ y ^ (1 / 4 : ℝ) := by positivity
  calc 16 / 3 * (3 * 10 ^ 11 : ℝ) ^ (1 / 4 : ℝ) * x ^ (15 / 4 : ℝ) * y ^ (1 / 4 : ℝ)
      ≤ 16 / 3 * (3 * 10 ^ 11) * (4832 ^ 4 * B ^ 20) * (6 * B) := by
        gcongr
    _ = 16 / 3 * (3 * 10 ^ 11) * 4832 ^ 4 * 6 * B ^ 21 := by ring
    _ ≤ 10 ^ 28 * B ^ 21 := by
        have : (0 : ℝ) ≤ B ^ 21 := by positivity
        nlinarith only [this]

/-- The constant `K₁ = 2⁴/(1 - 4(2δ_*)^{1/4})` at `δ_* = 1/1024`. -/
noncomputable def K1c : ℝ := 2 ^ 4 / (1 - 4 * (2 * (1 / 1024 : ℝ)) ^ (1 / (4 : ℝ)))

theorem K1c_pos : 0 < K1c := by
  unfold K1c
  have := four_two_delta_quarter_lt_one
  exact div_pos (by norm_num) (by linarith only [this])

/-- The constant of the four-core bound `coreM4F`. -/
noncomputable def C4c (κ : LocalKernelClass) : ℝ :=
  3 ^ 8 * (1 + K1c * (fourKC κ 3 * 2 * 12 ^ 4)) * 10 ^ 28 *
    ActiveSetup.BasicFamilies.FamParams.SideInput.bandC (1 - (1 / 300 : ℝ) / 4) 3

/-- The constant of the three-core bound `coreM3F`. -/
noncomputable def C3c (κ : LocalKernelClass) : ℝ :=
  3 ^ 8 * (1 + K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3)) * 10 ^ 28 *
    ActiveSetup.BasicFamilies.FamParams.SideInput.bandC (1 - (1 / 300 : ℝ) / 4) 3

theorem bandC_nonneg' (p : ℝ) (J : ℕ) :
    0 ≤ ActiveSetup.BasicFamilies.FamParams.SideInput.bandC p J := by
  unfold ActiveSetup.BasicFamilies.FamParams.SideInput.bandC
  exact tsum_nonneg fun t => by positivity

theorem C4c_nonneg (κ : LocalKernelClass) : 0 ≤ C4c κ := by
  unfold C4c
  have := fourKC_nonneg κ 3
  have := K1c_pos
  have := bandC_nonneg' (1 - (1 / 300 : ℝ) / 4) 3
  positivity

theorem C3c_nonneg (κ : LocalKernelClass) : 0 ≤ C3c κ := by
  unfold C3c
  have := entryCU_nonneg' κ 3 1
  have := K1c_pos
  have := bandC_nonneg' (1 - (1 / 300 : ℝ) / 4) 3
  positivity

/-- The four-core bound at `δ_* = 1/1024`, `J = 3`: `M₄ ≤ C B^{30} L⁴ K²` when `J_* + 1`,
`d_max + 5`, `log D_*`, `log H` are at most `B` and `log₂(U/ε) + 1 ≤ L`. -/
theorem coreM4F_le (κ : LocalKernelClass) (S : ModeSchedule) {B L U ε Kc : ℝ} (hB : 2 ≤ B)
    (hd : (S.dmax : ℝ) + 5 ≤ B) (hD1 : 1 ≤ S.Dstar) (hH1 : 1 ≤ S.H)
    (hD : Real.log S.Dstar ≤ B) (hH : Real.log S.H ≤ B) (hJ : (S.Jstar : ℝ) + 1 ≤ B)
    (hL0 : 0 ≤ Real.logb 2 (U / ε) + 1) (hL : Real.logb 2 (U / ε) + 1 ≤ L) (hKc : 1 ≤ Kc) :
    coreM4F κ S (1 / 1024) 3 U ε Kc ≤ C4c κ * B ^ 30 * L ^ 4 * Kc ^ 2 := by
  unfold coreM4F
  have hup := (card_upperHeights_le S.Jstar (1 / 1024)).trans hJ
  have hft := card_fourTypesF_le S (by linarith only [hB]) hD1 hD
  have hcc := fourCcF_le S hB hd hD1 hH1 hD hH
  have hcc0 : 0 ≤ fourCcF S := fourCcF_nonneg S hD1 hH1
  have hband := bandC_nonneg' (1 - (1 / 300 : ℝ) / 4) 3
  have hK1 : (2 ^ 4 / (1 - 4 * (2 * (1 / 1024 : ℝ)) ^ (1 / (4 : ℝ)))) = K1c := rfl
  rw [hK1]
  have hfk := fourKC_nonneg κ 3
  have hK1p := K1c_pos
  have h1 : (K1c * (fourKC κ 3 * 2 * 12 ^ 4)) ^ (1 - (1 / 300 : ℝ) / 4) ≤
      1 + K1c * (fourKC κ 3 * 2 * 12 ^ 4) :=
    rpow_le_one_add (by positivity) (by norm_num) (by norm_num)
  have h2 : Kc ^ (2 - (1 / 300 : ℝ) / 2) ≤ Kc ^ 2 := by
    calc Kc ^ (2 - (1 / 300 : ℝ) / 2) ≤ Kc ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hKc (by norm_num)
      _ = Kc ^ 2 := by norm_cast
  have h3 : (Real.logb 2 (U / ε) + 1) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hL0 hL 4
  have hL0' : 0 ≤ L := hL0.trans hL
  have hB0 : 0 ≤ B := by linarith only [hB]
  calc ((ModeComponents.upperHeights S.Jstar (1 / 1024)).card : ℝ) * (fourTypesF S).card *
        ((K1c * (fourKC κ 3 * 2 * 12 ^ 4)) ^ (1 - (1 / 300 : ℝ) / 4) *
          (fourCcF S * Kc ^ (2 - (1 / 300 : ℝ) / 2)) *
          ((Real.logb 2 (U / ε) + 1) ^ 4 *
            ActiveSetup.BasicFamilies.FamParams.SideInput.bandC (1 - (1 / 300 : ℝ) / 4) 3))
      ≤ B * (3 * B) ^ 8 * ((1 + K1c * (fourKC κ 3 * 2 * 12 ^ 4)) *
          (10 ^ 28 * B ^ 21 * Kc ^ 2) * (L ^ 4 *
            ActiveSetup.BasicFamilies.FamParams.SideInput.bandC (1 - (1 / 300 : ℝ) / 4) 3)) := by
        gcongr
    _ = C4c κ * B ^ 30 * L ^ 4 * Kc ^ 2 := by unfold C4c; ring

/-- The three-core bound at `δ_* = 1/1024`, `J = 3`, `A = 1`: `M₃ ≤ C B^{30} I L⁴ K²` when
moreover `I_w + 1 ≤ I`. -/
theorem coreM3F_le (κ : LocalKernelClass) (S : ModeSchedule) (Iw : ℕ) (l : Fin 4)
    {B L U ε Kc IB : ℝ} (hB : 2 ≤ B)
    (hd : (S.dmax : ℝ) + 5 ≤ B) (hD1 : 1 ≤ S.Dstar) (hH1 : 1 ≤ S.H)
    (hD : Real.log S.Dstar ≤ B) (hH : Real.log S.H ≤ B) (hJ : (S.Jstar : ℝ) + 1 ≤ B)
    (hL0 : 0 ≤ Real.logb 2 (U / ε) + 1) (hL : Real.logb 2 (U / ε) + 1 ≤ L) (hKc : 1 ≤ Kc)
    (hI : (Iw : ℝ) + 1 ≤ IB) :
    coreM3F κ S (1 / 1024) 3 1 Iw U ε Kc l ≤ C3c κ * B ^ 30 * IB * L ^ 4 * Kc ^ 2 := by
  unfold coreM3F
  have hup := (card_upperHeights_le S.Jstar (1 / 1024)).trans hJ
  have hft : (((fourTypesF S).filter fun κ => κ l = (0, 0)).card : ℝ) ≤ (3 * B) ^ 8 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _)
      (card_fourTypesF_le S (by linarith only [hB]) hD1 hD)
  have hcc := fourCcF_le S hB hd hD1 hH1 hD hH
  have hcc0 : 0 ≤ fourCcF S := fourCcF_nonneg S hD1 hH1
  have hband := bandC_nonneg' (1 - (1 / 300 : ℝ) / 4) 3
  have hK1 : (2 ^ 4 / (1 - 4 * (2 * (1 / 1024 : ℝ)) ^ (1 / (4 : ℝ)))) = K1c := rfl
  rw [hK1]
  have hfk := entryCU_nonneg' κ 3 1
  have hK1p := K1c_pos
  have h1 : (K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3)) ^ (1 - (1 / 300 : ℝ) / 4) ≤
      1 + K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3) :=
    rpow_le_one_add (by positivity) (by norm_num) (by norm_num)
  have h2 : Kc ^ (2 - (1 / 300 : ℝ) / 2) ≤ Kc ^ 2 := by
    calc Kc ^ (2 - (1 / 300 : ℝ) / 2) ≤ Kc ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hKc (by norm_num)
      _ = Kc ^ 2 := by norm_cast
  have h3 : (Real.logb 2 (U / ε) + 1) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ hL0 hL 4
  have hL0' : 0 ≤ L := hL0.trans hL
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hI0 : (0 : ℝ) ≤ (Iw : ℝ) + 1 := by positivity
  have hIB0 : 0 ≤ IB := hI0.trans hI
  calc ((ModeComponents.upperHeights S.Jstar (1 / 1024)).card : ℝ) *
        ((fourTypesF S).filter fun κ => κ l = (0, 0)).card *
        ((K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3)) ^ (1 - (1 / 300 : ℝ) / 4) *
          (fourCcF S * Kc ^ (2 - (1 / 300 : ℝ) / 2)) *
          (((Iw : ℝ) + 1) * ((Real.logb 2 (U / ε) + 1) ^ 4 *
            ActiveSetup.BasicFamilies.FamParams.SideInput.bandC (1 - (1 / 300 : ℝ) / 4) 3)))
      ≤ B * (3 * B) ^ 8 * ((1 + K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3)) *
          (10 ^ 28 * B ^ 21 * Kc ^ 2) * (IB * (L ^ 4 *
            ActiveSetup.BasicFamilies.FamParams.SideInput.bandC (1 - (1 / 300 : ℝ) / 4) 3))) := by
        gcongr
    _ = C3c κ * B ^ 30 * IB * L ^ 4 * Kc ^ 2 := by unfold C3c; ring

/-- The near-band bound of a leaf with stack energies at most `Γ` (`Γ_a, Γ_b, Γ_U ≤ Γ`). -/
theorem nearBndF_le (κ : LocalKernelClass) {c₀ : ℕ} (A : ActiveSetup κ c₀) {q : ℝ}
    (hq2 : 2 < q) (hq3 : q < 3) (P K : ℕ) (u : Option (Fin 4)) (Nd N Lp Jm : ℕ) {Mp C₀ ρ : ℝ}
    (Γa Γb : Fin 4 → ℝ) (ΓU : ℝ) (a b e : Fin 4) {Γ : ℝ} (hMp : 0 ≤ Mp) (hC₀ : 0 ≤ C₀)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hΓa : ∀ a, 0 ≤ Γa a ∧ Γa a ≤ Γ) (hΓb : ∀ b, 0 ≤ Γb b ∧ Γb b ≤ Γ)
    (hΓU : 0 ≤ ΓU ∧ ΓU ≤ Γ) :
    nearBndF κ A hq2 hq3 P K u Nd N Lp Jm Mp C₀ ρ Γa Γb ΓU a b e ≤
      4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
          (1 + Real.log ((K : ℝ) + 2)) * ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) *
          (64 * (2 * C₀) * (2 * C₀))) *
        (hullCutConstant (ρ / 2) * (N + 1 : ℕ) * (1 + Real.log (2 + ((N + 1 : ℕ) : ℝ) *
          ((N + 1 : ℕ) : ℝ) * ((ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs Lp Jm).card *
            Mp * A.famVtxBound)))) *
        Γ / Real.sqrt P * dyadicGridLength A.G A.R.1 := by
  have hM := nbCM_nonneg κ hq2 hq3
  have hU := (Classical.choose_spec (near_band_critical_UM κ hq2 hq3)).1
  change 0 ≤ nbCUM κ hq2 hq3 at hU
  have hCN := (finiteDepthConstant_bounds κ hq2.le Nd).1
  have hhull : 0 < hullCutConstant (ρ / 2) :=
    hullCutConstant_pos (by linarith only [hρ]) (by linarith only [hρ1])
  have hR := (dyadicGridLength_pos A.G A.R.1).le
  have hΓ0 : 0 ≤ Γ := (hΓU.1).trans hΓU.2
  have hP0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  unfold nearBndF
  set Y : ℝ := (ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs Lp Jm).card * Mp *
    A.famVtxBound with hY
  set N1 : ℝ := ((N + 1 : ℕ) : ℝ) with hN1d
  set! Z : ℝ := (1 + finiteDepthConstant κ q Nd) * (1 + Real.log ((K : ℝ) + 2)) *
    ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) * (64 * (2 * C₀) * (2 * C₀)) with hZ
  have hY0 : 0 ≤ Y := by positivity
  have hN1 : 1 ≤ N1 := by rw [hN1d]; exact_mod_cast Nat.succ_pos N
  have hlogK : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith only)
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    have : 0 ≤ ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) := by positivity
    have : 0 ≤ 1 + Real.log ((K : ℝ) + 2) := by linarith only [hlogK]
    positivity
  have hlog2 : ∀ x : ℝ, 0 ≤ x → 0 ≤ 1 + Real.log (2 + x) := fun x hx => by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + x by linarith only [hx])
    linarith only [this]
  have hW0 : 0 ≤ hullCutConstant (ρ / 2) * N1 * (1 + Real.log (2 + N1 * N1 * Y)) :=
    mul_nonneg (mul_nonneg hhull.le (by linarith only [hN1d])) (hlog2 _ (by positivity))
  have hsq : ∀ x y : ℝ, 0 ≤ x → x ≤ Γ → 0 ≤ y → y ≤ Γ → Real.sqrt (x * y) ≤ Γ := by
    intro x y hx hxΓ hy hyΓ
    calc Real.sqrt (x * y) ≤ Real.sqrt (Γ * Γ) :=
          Real.sqrt_le_sqrt (mul_le_mul hxΓ hyΓ hy hΓ0)
      _ = Γ := Real.sqrt_mul_self hΓ0
  have hfin : ∀ (c W s : ℝ), 0 ≤ c → c ≤ nbCM κ hq2 hq3 + nbCUM κ hq2 hq3 → 0 ≤ W →
      W ≤ hullCutConstant (ρ / 2) * N1 * (1 + Real.log (2 + N1 * N1 * Y)) → 0 ≤ s → s ≤ Γ →
      4 * (c * (1 + finiteDepthConstant κ q Nd) * (1 + Real.log ((K : ℝ) + 2)) *
        ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) * (64 * (2 * C₀) * (2 * C₀))) * W * s /
          Real.sqrt P * dyadicGridLength A.G A.R.1 ≤
        4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
          (1 + Real.log ((K : ℝ) + 2)) * ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) *
          (64 * (2 * C₀) * (2 * C₀))) *
          (hullCutConstant (ρ / 2) * N1 * (1 + Real.log (2 + N1 * N1 * Y))) * Γ /
            Real.sqrt P * dyadicGridLength A.G A.R.1 := by
    intro c W s hc hcM hW hWM hs hsΓ
    have e : ∀ c' : ℝ, 4 * (c' * (1 + finiteDepthConstant κ q Nd) * (1 + Real.log ((K : ℝ) + 2)) *
        ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) * (64 * (2 * C₀) * (2 * C₀))) =
        4 * (c' * Z) := fun c' => by rw [hZ]; ring
    rw [e, e]
    have h1 : 4 * (c * Z) ≤ 4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * Z) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcM hZ0) (by norm_num)
    have h2 := mul_le_mul (mul_le_mul h1 hWM hW (by positivity)) hsΓ hs (by positivity)
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 hP0) hR
  split_ifs with h1 h2
  · -- the `U` case
    refine hfin _ _ _ hU (by linarith only [hM]) ?_ ?_ (Real.sqrt_nonneg _)
      (hsq _ _ (hΓa a).1 (hΓa a).2 hΓU.1 hΓU.2)
    · rw [Nat.cast_one]
      exact mul_nonneg (mul_nonneg hhull.le (by linarith only [hN1d])) (hlog2 _ (by positivity))
    · rw [Nat.cast_one]
      have h3 : N1 * 1 * Y ≤ N1 * N1 * Y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN1 (by linarith only [hN1d])) hY0
      have h4 : 0 < 2 + N1 * 1 * Y := by positivity
      have h5 := Real.log_le_log h4 (show 2 + N1 * 1 * Y ≤ 2 + N1 * N1 * Y by linarith only [h3])
      have h6 : 1 + Real.log (2 + N1 * 1 * Y) ≤ 1 + Real.log (2 + N1 * N1 * Y) := by
        linarith only [h5]
      exact mul_le_mul_of_nonneg_left h6 (mul_nonneg hhull.le (by linarith only [hN1d]))
  · exact hfin _ _ _ hM (by linarith only [hU]) hW0 le_rfl (Real.sqrt_nonneg _)
      (hsq _ _ (hΓa a).1 (hΓa a).2 (hΓb b).1 (hΓb b).2)
  · have e : 4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
        (1 + Real.log ((K : ℝ) + 2)) * ((K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) *
        (64 * (2 * C₀) * (2 * C₀))) = 4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * Z) := by
      rw [hZ]; ring
    rw [e]
    have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (mul_nonneg (add_nonneg hM hU) hZ0)) hW0) hΓ0
    exact mul_nonneg (div_nonneg this hP0) hR

/-- The arithmetic collapse of the right side of `leaf_bound` at `p = 1 - 1/1200`: the side cap
`T ≤ t_T`, the core and error sizes `≤ t_C`, the path count `N_p ≤ B²`, the far constant
`≤ 64 B (P+1)² τ₃`, the core bounds `≤ t_M` and the error product `≤ X_E` give
`(196608 B³ t_T + 83 (1 + 81 L₀ (t_C + √t_T)) (1 + t_T)³ + t_M) (η^{1/1200} + η₀ + (P+1)² τ₃) |R|`
plus the near bands and the absolute errors. -/
theorem leaf_raw_le {T cB eB Np τ fc η R nearS M Ee cM4 cM3 cE L0 B η₀ τ₃ P tT tC tM XE : ℝ}
    (hT0 : 0 ≤ T) (hT : T ≤ tT) (hcB0 : 0 ≤ cB) (hcB : cB ≤ tC) (heB0 : 0 ≤ eB) (heB : eB ≤ tC)
    (hNp : Np ≤ B ^ 2) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 2 * η₀) (hfc0 : 0 ≤ fc)
    (hfc : fc ≤ 64 * B * (P + 1) ^ 2 * τ₃) (hη0 : 0 ≤ η) (hR : 0 ≤ R)
    (hL0 : 0 ≤ L0) (hB : 1 ≤ B) (hη₀ : 0 ≤ η₀) (hτ₃ : 0 ≤ τ₃)
    (hME : Real.sqrt (4 * M) * Real.sqrt Ee ≤ XE) (htM0 : 0 ≤ tM) (hcM : cM4 + cM3 ≤ tM) :
    6 * 256 * Np * (τ + fc) * T * R + 6 * nearS +
        η ^ (1 - (1 - 1 / 1200 : ℝ)) * (T ^ ((1 - 1 / 1200 : ℝ) / 2) *
          T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) * R) +
      82 * (81 * (L0 * (cB + eB + Real.sqrt T) ^ 3) * (Real.sqrt (4 * M) * Real.sqrt Ee)) +
      82 * (η ^ (1 - (1 - 1 / 1200 : ℝ)) * (81 * L0 * max cB (Real.sqrt T)) ^ (1 - 1 / 1200 : ℝ) *
        (T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) *
          T ^ ((1 - 1 / 1200 : ℝ) / 2) * R)) +
      (η ^ (1 / 1200 : ℝ) * (R * (cM4 + cM3)) + cE) ≤
    (196608 * B ^ 3 * tT + 83 * (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 + tM) *
        (η ^ (1 / 1200 : ℝ) + η₀ + (P + 1) ^ 2 * τ₃) * R +
      6 * nearS + 6642 * L0 * (2 * tC + Real.sqrt tT) ^ 3 * XE + cE := by
  have e1 : (1 - (1 - 1 / 1200 : ℝ)) = 1 / 1200 := by norm_num
  rw [e1]
  set ηe := η ^ (1 / 1200 : ℝ) with hηe
  have hηe0 : 0 ≤ ηe := Real.rpow_nonneg hη0 _
  have htT0 : 0 ≤ tT := hT0.trans hT
  have htC0 : 0 ≤ tC := hcB0.trans hcB
  have hsT : Real.sqrt T ≤ Real.sqrt tT := Real.sqrt_le_sqrt hT
  have hsT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hstT0 : 0 ≤ Real.sqrt tT := Real.sqrt_nonneg _
  -- the powers of the side cap
  have hTp : T ^ ((1 - 1 / 1200 : ℝ) / 2) ≤ 1 + tT :=
    (rpow_le_one_add hT0 (by norm_num) (by norm_num)).trans (by linarith only [hT])
  have hTp0 : 0 ≤ T ^ ((1 - 1 / 1200 : ℝ) / 2) := Real.rpow_nonneg hT0 _
  have h1t : 0 ≤ 1 + tT := by linarith only [htT0]
  have hT3 : T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) *
      T ^ ((1 - 1 / 1200 : ℝ) / 2) ≤ (1 + tT) ^ 3 := by
    have := mul_le_mul (mul_le_mul hTp hTp hTp0 h1t) hTp hTp0 (by positivity)
    calc _ ≤ (1 + tT) * (1 + tT) * (1 + tT) := this
      _ = (1 + tT) ^ 3 := by ring
  have hT30 : 0 ≤ T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) *
      T ^ ((1 - 1 / 1200 : ℝ) / 2) := by positivity
  -- the first term
  have hq0 : 0 ≤ η₀ + (P + 1) ^ 2 * τ₃ := by positivity
  have hA : 6 * 256 * Np * (τ + fc) * T * R ≤
      196608 * B ^ 3 * tT * (η₀ + (P + 1) ^ 2 * τ₃) * R := by
    have h1 : τ + fc ≤ 2 * η₀ + 64 * B * (P + 1) ^ 2 * τ₃ := add_le_add hτ hfc
    have h2 : Np * (τ + fc) ≤ B ^ 2 * (2 * η₀ + 64 * B * (P + 1) ^ 2 * τ₃) :=
      mul_le_mul hNp h1 (by positivity) (by positivity)
    have hB2 : B ^ 2 ≤ B ^ 3 := pow_le_pow_right₀ hB (by norm_num)
    have hB30 : 0 ≤ B ^ 3 := by positivity
    have h3 : B ^ 2 * (2 * η₀ + 64 * B * (P + 1) ^ 2 * τ₃) ≤
        128 * B ^ 3 * (η₀ + (P + 1) ^ 2 * τ₃) := by
      have hb1 : B ^ 2 * (2 * η₀) ≤ B ^ 3 * (2 * η₀) :=
        mul_le_mul_of_nonneg_right hB2 (by positivity)
      have hb2 : B ^ 2 * (64 * B * (P + 1) ^ 2 * τ₃) = 64 * (B ^ 3 * ((P + 1) ^ 2 * τ₃)) := by
        ring
      have hb3 : 0 ≤ B ^ 3 * ((P + 1) ^ 2 * τ₃) := by positivity
      have hb4 : 0 ≤ B ^ 3 * η₀ := by positivity
      calc B ^ 2 * (2 * η₀ + 64 * B * (P + 1) ^ 2 * τ₃)
          = B ^ 2 * (2 * η₀) + B ^ 2 * (64 * B * (P + 1) ^ 2 * τ₃) := by ring
        _ ≤ B ^ 3 * (2 * η₀) + 64 * (B ^ 3 * ((P + 1) ^ 2 * τ₃)) := by rw [hb2]; linarith only [hb1]
        _ ≤ 128 * B ^ 3 * (η₀ + (P + 1) ^ 2 * τ₃) := by linarith only [hb3, hb4]
    have h4 := mul_le_mul_of_nonneg_right (h2.trans h3) (mul_nonneg hT0 hR)
    have h5 : 128 * B ^ 3 * (η₀ + (P + 1) ^ 2 * τ₃) * (T * R) ≤
        128 * B ^ 3 * (η₀ + (P + 1) ^ 2 * τ₃) * (tT * R) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT hR) (by positivity)
    calc 6 * 256 * Np * (τ + fc) * T * R = 1536 * (Np * (τ + fc) * (T * R)) := by ring
      _ ≤ 1536 * (128 * B ^ 3 * (η₀ + (P + 1) ^ 2 * τ₃) * (tT * R)) := by
          linarith only [h4, h5]
      _ = 196608 * B ^ 3 * tT * (η₀ + (P + 1) ^ 2 * τ₃) * R := by ring
  -- the three-side main term
  have hB3 : ηe * (T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) *
      T ^ ((1 - 1 / 1200 : ℝ) / 2) * R) ≤ (1 + tT) ^ 3 * ηe * R := by
    have := mul_le_mul_of_nonneg_right hT3 hR
    have h := mul_le_mul_of_nonneg_left this hηe0
    calc _ ≤ ηe * ((1 + tT) ^ 3 * R) := h
      _ = _ := by ring
  -- the power term
  have hmax : max cB (Real.sqrt T) ≤ tC + Real.sqrt tT :=
    max_le (by linarith only [hcB, hstT0]) (by linarith only [htC0, hsT])
  have hm0 : 0 ≤ 81 * L0 * max cB (Real.sqrt T) :=
    mul_nonneg (by positivity) (le_max_of_le_left hcB0)
  have hpw : (81 * L0 * max cB (Real.sqrt T)) ^ (1 - 1 / 1200 : ℝ) ≤
      1 + 81 * L0 * (tC + Real.sqrt tT) := by
    have := rpow_le_one_add hm0 (by norm_num : (0 : ℝ) ≤ 1 - 1 / 1200) (by norm_num)
    have h2 : 81 * L0 * max cB (Real.sqrt T) ≤ 81 * L0 * (tC + Real.sqrt tT) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    linarith only [this, h2]
  have hC3 : 82 * (ηe * (81 * L0 * max cB (Real.sqrt T)) ^ (1 - 1 / 1200 : ℝ) *
      (T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) *
        T ^ ((1 - 1 / 1200 : ℝ) / 2) * R)) ≤
      82 * (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 * ηe * R := by
    have h1 := mul_le_mul hpw (mul_le_mul_of_nonneg_right hT3 hR) (mul_nonneg hT30 hR)
      (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 82 * ηe by positivity)
    calc _ = 82 * ηe * ((81 * L0 * max cB (Real.sqrt T)) ^ (1 - 1 / 1200 : ℝ) *
          (T ^ ((1 - 1 / 1200 : ℝ) / 2) * T ^ ((1 - 1 / 1200 : ℝ) / 2) *
            T ^ ((1 - 1 / 1200 : ℝ) / 2) * R)) := by ring
      _ ≤ 82 * ηe * ((1 + 81 * L0 * (tC + Real.sqrt tT)) * ((1 + tT) ^ 3 * R)) := h2
      _ = _ := by ring
  -- the error product
  have hD : 82 * (81 * (L0 * (cB + eB + Real.sqrt T) ^ 3) * (Real.sqrt (4 * M) * Real.sqrt Ee)) ≤
      6642 * L0 * (2 * tC + Real.sqrt tT) ^ 3 * XE := by
    have h1 : cB + eB + Real.sqrt T ≤ 2 * tC + Real.sqrt tT := by linarith only [hcB, heB, hsT]
    have h2 : (cB + eB + Real.sqrt T) ^ 3 ≤ (2 * tC + Real.sqrt tT) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have hME0 : 0 ≤ Real.sqrt (4 * M) * Real.sqrt Ee := by positivity
    have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h2 hL0) hME hME0 (by positivity)
    calc _ = 6642 * (L0 * (cB + eB + Real.sqrt T) ^ 3 * (Real.sqrt (4 * M) * Real.sqrt Ee)) := by
          ring
      _ ≤ 6642 * (L0 * (2 * tC + Real.sqrt tT) ^ 3 * XE) := by linarith only [h3]
      _ = _ := by ring
  -- the core term
  have hE : ηe * (R * (cM4 + cM3)) ≤ tM * ηe * R := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcM hR) hηe0
    calc _ ≤ ηe * (R * tM) := this
      _ = _ := by ring
  -- assembly
  have hY1 : (1 + tT) ^ 3 ≤ (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 :=
    le_mul_of_one_le_left (by positivity) (by
      have : 0 ≤ 81 * L0 * (tC + Real.sqrt tT) := by positivity
      linarith only [this])
  have hX0 : 0 ≤ 196608 * B ^ 3 * tT := by positivity
  have hY0 : 0 ≤ (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 := by positivity
  set! Y := (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 with hY
  rewrite [← hY] at hY1 hY0
  set! X := 196608 * B ^ 3 * tT with hX
  rewrite [← hX] at hA hX0 ⊢
  have hfin : X * (η₀ + (P + 1) ^ 2 * τ₃) * R + (1 + tT) ^ 3 * ηe * R +
      82 * (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 * ηe * R + tM * ηe * R ≤
      (X + 83 * Y + tM) * (ηe + η₀ + (P + 1) ^ 2 * τ₃) * R := by
    have e2 : 82 * (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 * ηe * R =
        82 * (Y * (ηe * R)) := by rw [hY]; ring
    rw [e2]
    have hηR : 0 ≤ ηe * R := mul_nonneg hηe0 hR
    have hqR : 0 ≤ (η₀ + (P + 1) ^ 2 * τ₃) * R := mul_nonneg hq0 hR
    have k1 : (1 + tT) ^ 3 * ηe * R ≤ Y * (ηe * R) := by
      have := mul_le_mul_of_nonneg_right hY1 hηR
      calc _ = (1 + tT) ^ 3 * (ηe * R) := by ring
        _ ≤ _ := this
    have k2 : 0 ≤ X * (ηe * R) := mul_nonneg hX0 hηR
    have k3 : 0 ≤ Y * ((η₀ + (P + 1) ^ 2 * τ₃) * R) := mul_nonneg hY0 hqR
    have k4 : 0 ≤ tM * ((η₀ + (P + 1) ^ 2 * τ₃) * R) := mul_nonneg htM0 hqR
    have e3 : (X + 83 * Y + tM) * (ηe + η₀ + (P + 1) ^ 2 * τ₃) * R =
        X * ((η₀ + (P + 1) ^ 2 * τ₃) * R) + X * (ηe * R) + 83 * (Y * (ηe * R)) +
          83 * (Y * ((η₀ + (P + 1) ^ 2 * τ₃) * R)) + tM * (ηe * R) +
          tM * ((η₀ + (P + 1) ^ 2 * τ₃) * R) := by ring
    have e4 : X * (η₀ + (P + 1) ^ 2 * τ₃) * R = X * ((η₀ + (P + 1) ^ 2 * τ₃) * R) := by ring
    have e5 : tM * ηe * R = tM * (ηe * R) := by ring
    rw [e3, e4, e5]
    linarith only [k1, k2, k3, k4]
  have e6 : 196608 * B ^ 3 * tT + 83 * (1 + 81 * L0 * (tC + Real.sqrt tT)) * (1 + tT) ^ 3 + tM =
      X + 83 * Y + tM := by rw [hX, hY]; ring
  rw [e6]
  linarith only [hA, hB3, hC3, hD, hE, hfin]


/-- The polylogarithmic factors of the near bands at block length `K ≥ 1` with
`N = ⌊log₂ K⌋ + 1`: `(1 + log(K+2)) (N+1) (1 + log(2 + (N+1)² Y)) N³ ≤ 80 λ⁶ (1 + log(2 + Y))`,
`λ = 2 + log(K + 2)`. -/
theorem near_lambda_le (K : ℕ) (hK : 1 ≤ K) {Y : ℝ} (hY : 0 ≤ Y) :
    (1 + Real.log ((K : ℝ) + 2)) * ((Nat.log 2 K + 1 + 1 : ℕ) : ℝ) *
      (1 + Real.log (2 + ((Nat.log 2 K + 1 + 1 : ℕ) : ℝ) * ((Nat.log 2 K + 1 + 1 : ℕ) : ℝ) * Y)) *
      ((Nat.log 2 K + 1 : ℕ) : ℝ) ^ 3 ≤
    80 * (2 + Real.log ((K : ℝ) + 2)) ^ 6 * (1 + Real.log (2 + Y)) := by
  set lam := 2 + Real.log ((K : ℝ) + 2) with hlam
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hl0 : 0 ≤ Real.log ((K : ℝ) + 2) := Real.log_nonneg (by linarith only)
  have hlam2 : 2 ≤ lam := by linarith only [hl0]
  -- `log₂ K ≤ 2 log (K + 2)`
  have hn : ((Nat.log 2 K : ℕ) : ℝ) ≤ 2 * Real.log ((K : ℝ) + 2) := by
    have h1 : ((Nat.log 2 K : ℕ) : ℝ) ≤ Real.logb 2 (K : ℝ) := by
      exact_mod_cast Real.natLog_le_logb K 2
    have h2 : Real.logb 2 (K : ℝ) ≤ 2 * Real.log (K : ℝ) := logb_two_le_two_log hK1
    have h3 : Real.log (K : ℝ) ≤ Real.log ((K : ℝ) + 2) :=
      Real.log_le_log (by linarith only [hK1]) (by linarith)
    linarith
  set N1 : ℝ := ((Nat.log 2 K + 1 + 1 : ℕ) : ℝ) with hN1d
  set N0 : ℝ := ((Nat.log 2 K + 1 : ℕ) : ℝ) with hN0d
  have hN1 : N1 = (Nat.log 2 K : ℝ) + 2 := by rw [hN1d]; push_cast; ring
  have hN0 : N0 = (Nat.log 2 K : ℝ) + 1 := by rw [hN0d]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ (Nat.log 2 K : ℝ) := Nat.cast_nonneg _
  have hN1l : N1 ≤ 2 * lam := by rw [hN1]; linarith only [hn]
  have hN0l : N0 ≤ 2 * lam := by rw [hN0]; linarith only [hn]
  have hN11 : 1 ≤ N1 := by rw [hN1]; linarith
  have hN01 : 1 ≤ N0 := by rw [hN0]; linarith
  have hY2 : 0 ≤ Real.log (2 + Y) := Real.log_nonneg (by linarith)
  -- the logarithm of the multiplicity
  have hlog : 1 + Real.log (2 + N1 * N1 * Y) ≤ 5 * lam * (1 + Real.log (2 + Y)) := by
    have h1 : 2 + N1 * N1 * Y ≤ N1 * N1 * (2 + Y) := by
      have : 1 ≤ N1 * N1 := one_le_mul_of_one_le_of_one_le hN11 hN11
      nlinarith only [this, hY]
    have h2 : Real.log (2 + N1 * N1 * Y) ≤ Real.log (N1 * N1 * (2 + Y)) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (N1 * N1 * (2 + Y)) = 2 * Real.log N1 + Real.log (2 + Y) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity)]
      ring
    have h4 : Real.log N1 ≤ N1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < N1 by linarith)
      linarith only [this]
    have h5 : 0 ≤ (4 * lam - 1) * Real.log (2 + Y) := mul_nonneg (by linarith only [hl0]) hY2
    nlinarith only [h2, h3, h4, hN1l, h5, hlam2, hY2]
  have hlog0 : 0 ≤ 1 + Real.log (2 + N1 * N1 * Y) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + N1 * N1 * Y by
      have : 0 ≤ N1 * N1 * Y := by positivity
      linarith only [this])
    linarith
  have hc : N0 ^ 3 ≤ (2 * lam) ^ 3 := pow_le_pow_left₀ (by linarith only [hN0d]) hN0l 3
  have hA : 1 + Real.log ((K : ℝ) + 2) ≤ lam := by linarith only
  have hA0 : 0 ≤ 1 + Real.log ((K : ℝ) + 2) := by linarith
  calc (1 + Real.log ((K : ℝ) + 2)) * N1 * (1 + Real.log (2 + N1 * N1 * Y)) * N0 ^ 3
      ≤ lam * (2 * lam) * (5 * lam * (1 + Real.log (2 + Y))) * (2 * lam) ^ 3 := by
        gcongr
    _ = 80 * lam ^ 6 * (1 + Real.log (2 + Y)) := by ring

/-- `(1 + log 2k)² ≤ 4k` for `k ≥ 1`. -/
theorem one_add_log_two_mul_sq_le {k : ℝ} (hk : 1 ≤ k) : (1 + Real.log (2 * k)) ^ 2 ≤ 4 * k := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith only [hk])
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (by linarith only [hk])
  have h1 : Real.log (2 * k) = Real.log 2 + 2 * Real.log (Real.sqrt k) := by
    rw [Real.log_mul (by norm_num) (by linarith), ← hsk, Real.log_mul hs.ne' hs.ne']
    rw [hsk]; ring
  have h2 : Real.log (Real.sqrt k) ≤ Real.sqrt k - 1 := Real.log_le_sub_one_of_pos hs
  have hl2 : Real.log 2 < 1 := by linarith only [Real.log_two_lt_d9]
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs1 : 1 ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hk
  have hlk : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith only [hk])
  have h3 : 1 + Real.log (2 * k) ≤ 2 * Real.sqrt k := by linarith
  have h4 := pow_le_pow_left₀ (by linarith) h3 2
  calc (1 + Real.log (2 * k)) ^ 2 ≤ (2 * Real.sqrt k) ^ 2 := h4
    _ = 4 * (Real.sqrt k * Real.sqrt k) := by ring
    _ = 4 * k := by rw [hsk]

/-- `k ≤ exp((1 + log 2k)²)` for `k ≥ 1`. -/
theorem le_exp_one_add_log_sq {k : ℝ} (hk : 1 ≤ k) : k ≤ Real.exp ((1 + Real.log (2 * k)) ^ 2) := by
  have h0 : 0 ≤ Real.log (2 * k) := Real.log_nonneg (by linarith only [hk])
  have h1 : Real.log k ≤ Real.log (2 * k) := Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (2 * k) ≤ (1 + Real.log (2 * k)) ^ 2 := by nlinarith only [h0]
  calc k = Real.exp (Real.log k) := (Real.exp_log (by linarith)).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The fuel bound `2 n + 2 ≤ c (log k + 1)` gives `2^n ≤ (3k)^c`. -/
theorem two_pow_le_of_fuel {n c : ℕ} {k : ℝ} (hk : 1 ≤ k)
    (h : ((2 * n + 2 : ℕ) : ℝ) ≤ c * (Real.log k + 1)) : (2 : ℝ) ^ n ≤ (3 * k) ^ c := by
  have hl2 : Real.log 2 < 1 := by linarith only [Real.log_two_lt_d9]
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hn : (n : ℝ) ≤ c * (Real.log k + 1) := by
    have : ((2 * n + 2 : ℕ) : ℝ) = 2 * n + 2 := by push_cast; ring
    rw [this] at h
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [h]
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc (2 : ℝ) ^ n ≤ Real.exp 1 ^ n := pow_le_pow_left₀ (by norm_num) he2 n
    _ = Real.exp n := Real.exp_one_pow n
    _ ≤ Real.exp (c * (Real.log k + 1)) := Real.exp_le_exp.mpr hn
    _ = Real.exp (Real.log k + 1) ^ c := Real.exp_nat_mul _ _
    _ = (k * Real.exp 1) ^ c := by rw [Real.exp_add, Real.exp_log (by linarith)]
    _ ≤ (3 * k) ^ c := pow_le_pow_left₀ (by positivity)
        (by nlinarith only [Real.exp_one_lt_d9, hk]) c

/-- The explicit leaf bound of `leaf_estimate` (the form of `eq:before-absorption` on one leaf):
`C u^C G^C (η^{1/1200} + η₀ + (P+1)² τ₃ + e^{C k^c} (√δ + e^{-k_D})) |R| + C e^{-k} |R|` plus the
near-band term `C (1 + C_N) C_q (C u^C + 2)^{2(q-2)/(q-1)} (2 + log(C u^C + 2))⁶ G^C P^{-1/2} |R|`,
with `u = k_D P` and `G = exp((1 + log 2k)²)`. -/
noncomputable def leafBnd (Cl : ℕ) (kD : ℝ) (P k cc : ℕ) (η η₀ τ₃ δ CN Cq q R : ℝ) : ℝ :=
  (Cl : ℝ) * (kD * P) ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
      (η ^ (1 / 1200 : ℝ) + η₀ + ((P : ℝ) + 1) ^ 2 * τ₃ +
        Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ + Real.exp (-kD))) * R +
    Cl * Real.exp (-(k : ℝ)) * R +
    Cl * (1 + CN) * Cq * (Cl * (kD * P) ^ Cl + 2) ^ (2 * (q - 2) / (q - 1)) *
      (2 + Real.log (Cl * (kD * P) ^ Cl + 2)) ^ 6 *
      Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl / Real.sqrt P * R

/-! Steps of `leaf_final`. Each lemma below is one step of that proof, stated over the
hypotheses and local definitions (as `let`s) of the proof that it uses, so that it is
elaborated in a small local context instead of the long context of the whole proof. -/

/-- Step `hKB` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hKB :
    ∀ (Msch : ℝ), (0 : ℝ) < Msch → ∀ (CΛ : ℕ) (eΛ : ℕ) (Cb : ℕ) (S : ModeSchedule) (Λ : ℝ),
      (0 : ℝ) ≤ Λ → (↑S.K : ℝ) ≤ Msch * Λ ^ (16 : ℕ) → (16 : ℕ) * eΛ ≤ Cb →
      (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) ≤ Cb → ∀ (u : ℝ), Λ ≤ (↑CΛ : ℝ) * u ^ eΛ → (1 : ℝ) ≤ u →
      ∀ (B : ℝ), (∀ (c : ℝ) (e : ℕ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → e ≤ Cb → c * u ^ e ≤ B) →
      Msch ≤ (↑(⌈Msch⌉₊ + (1 : ℕ)) : ℝ) → (1 : ℝ) ≤ (↑CΛ : ℝ) →
    (S.K : ℝ) ≤ B := by
  intro Msch hMsch CΛ eΛ Cb S Λ hΛ0 hK heΛCb hMCb1 u hΛ hu1 B hpowB hMc hCΛ1
  refine hK.trans ?_
  have! h1 := pow_le_pow_left₀ hΛ0 hΛ 16
  have! h2 : Msch * (CΛ * u ^ eΛ) ^ 16 ≤ ((⌈Msch⌉₊ + 1) * CΛ ^ 16 : ℕ) * u ^ (16 * eΛ) := by
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm eΛ 16, ← mul_assoc]
    have! this : (0 : ℝ) ≤ (CΛ : ℝ) ^ 16 * u ^ (16 * eΛ) := by positivity
    have! h3 := mul_le_mul_of_nonneg_right hMc this
    push_cast at h3
    linarith only [h3]
  refine (mul_le_mul_of_nonneg_left h1 hMsch.le).trans (h2.trans (hpowB _ _ (by positivity)
    ?_ (by omega)))
  exact_mod_cast hMCb1

/-- Step `hHB` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hHB :
    ∀ (Msch : ℝ), (0 : ℝ) < Msch → ∀ (CΛ : ℕ) (eΛ : ℕ) (Cb : ℕ) (S : ModeSchedule) (Λ : ℝ),
      (0 : ℝ) ≤ Λ → Real.log S.H ≤ Msch * Λ ^ (12 : ℕ) → (16 : ℕ) * eΛ ≤ Cb →
      (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb → ∀ (u : ℝ), Λ ≤ (↑CΛ : ℝ) * u ^ eΛ →
      (1 : ℝ) ≤ u → ∀ (B : ℝ),
      (∀ (c : ℝ) (e : ℕ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → e ≤ Cb → c * u ^ e ≤ B) →
      (1 : ℝ) ≤ (↑CΛ : ℝ) →
    Real.log S.H + 1 ≤ B := by
  intro Msch hMsch CΛ eΛ Cb S Λ hΛ0 hlogH heΛCb hMCb2 u hΛ hu1 B hpowB hCΛ1
  refine le_trans (show Real.log S.H + 1 ≤ Msch * Λ ^ 12 + 1 by linarith only [hlogH]) ?_
  have! h1 := pow_le_pow_left₀ hΛ0 hΛ 12
  have! hu12 : u ^ (12 * eΛ) ≤ u ^ (16 * eΛ) := pow_le_pow_right₀ hu1 (by omega)
  have! hC12 : (CΛ : ℝ) ^ 12 ≤ CΛ ^ 16 := pow_le_pow_right₀ hCΛ1 (by norm_num)
  have! h2 : Msch * (CΛ * u ^ eΛ) ^ 12 + 1 ≤
      (((⌈Msch⌉₊ + 1) * CΛ ^ 16 : ℕ) + 1 : ℝ) * u ^ (16 * eΛ) := by
    push_cast
    rw [mul_pow, ← pow_mul, mul_comm eΛ 12]
    have! h0 : (0 : ℝ) ≤ u ^ (12 * eΛ) := by positivity
    have! h3 : Msch * ((CΛ : ℝ) ^ 12 * u ^ (12 * eΛ)) ≤
        ((⌈Msch⌉₊ : ℝ) + 1) * ((CΛ : ℝ) ^ 16 * u ^ (16 * eΛ)) :=
      mul_le_mul (by linarith only [Nat.le_ceil Msch]) (mul_le_mul hC12 hu12 h0 (by positivity))
        (by positivity) (by positivity)
    have! h4 : (1 : ℝ) ≤ u ^ (16 * eΛ) := one_le_pow₀ hu1
    nlinarith only [h3, h4]
  have! h3 := mul_le_mul_of_nonneg_left h1 hMsch.le
  refine le_trans (show Msch * Λ ^ 12 + 1 ≤ Msch * (CΛ * u ^ eΛ) ^ 12 + 1 by
    linarith only [h3]) (h2.trans (hpowB _ _ (by positivity) ?_ (by omega)))
  exact_mod_cast hMCb2

/-- Step `hIwB` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hIwB :
    ∀ (Cg : ℕ) (Cb : ℕ) (S : ModeSchedule) (Iw : ℕ),
      Iw = ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊ → (500 : ℕ) * Cg + (1 : ℕ) ≤ Cb → ∀ (u : ℝ),
      Real.log S.Dstar ≤ (↑Cg : ℝ) * u ^ Cg → (1 : ℝ) ≤ u → ∀ (B : ℝ),
      (∀ (c : ℝ) (e : ℕ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → e ≤ Cb → c * u ^ e ≤ B) →
      (1 : ℝ) ≤ S.Dstar → (0 : ℝ) ≤ Real.log S.Dstar →
    (Iw : ℝ) + 1 ≤ B := by
  intro Cg Cb S Iw hIw hCgCb u hlD hu1 B hpowB hD1 hlD0
  have! h1 : (Iw : ℝ) ≤ Real.logb 2 (S.Dstar ^ 250) := by
    rw [hIw]; exact Nat.floor_le (Real.logb_nonneg (by norm_num) (one_le_pow₀ hD1))
  have! h2 : Real.logb 2 (S.Dstar ^ 250) ≤ 500 * Real.log S.Dstar := by
    have! this := logb_two_le_two_log (one_le_pow₀ hD1 : (1 : ℝ) ≤ S.Dstar ^ 250)
    rw [Real.log_pow] at this; push_cast at this; linarith only [this]
  have! h3 : 500 * Real.log S.Dstar + 1 ≤ ((500 * Cg + 1 : ℕ) : ℝ) * u ^ Cg := by
    push_cast
    have! this : (1 : ℝ) ≤ u ^ Cg := one_le_pow₀ hu1
    nlinarith only [hlD, this, hlD0]
  refine le_trans (by linarith only [h1, h2]) (h3.trans (hpowB _ _ (by positivity) ?_
    (by omega)))
  exact_mod_cast (show 500 * Cg + 1 ≤ Cb by omega)

/-- Step `hJmB` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hJmB :
    ∀ (Cb : ℕ) (k : ℕ) (cc : ℕ), (1 : ℕ) ≤ cc → ∀ (famFuel : ℕ),
      (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)) →
      (1 : ℝ) ≤ (↑k : ℝ) → cc + (1 : ℕ) ≤ Cb → (↑k : ℝ) ≤ (↑k : ℝ) ^ cc → ∀ (B : ℝ),
      (∀ (c : ℝ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → c * (↑k : ℝ) ^ cc ≤ B) → (1 : ℝ) ≤ (↑k : ℝ) ^ cc →
    ((2 * famFuel + 2 : ℕ) : ℝ) + 1 ≤ B := by
  intro Cb k cc hcc famFuel hkF hk1 hccCb hkcc0 B hkcc hkcc1
  have! hlk : Real.log k + 1 ≤ k := by
    have! this := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k by linarith only [hk1])
    linarith only [this]
  have! h1 : ((2 * famFuel + 2 : ℕ) : ℝ) + 1 ≤ (cc + 1) * (k : ℝ) ^ cc := by
    have! hcc0 : (0 : ℝ) ≤ cc := Nat.cast_nonneg _
    have! this := mul_le_mul_of_nonneg_left hlk hcc0
    nlinarith only [hkF, this, hkcc0, hcc0, hkcc1]
  refine h1.trans (hkcc _ (by positivity) ?_)
  exact_mod_cast (show cc + 1 ≤ Cb by omega)

/-- Step `hVl0B` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hVl0B :
    ∀ (k : ℕ) (cc : ℕ) (S : ModeSchedule) (Vl0 : ℝ),
      Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
        1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
        Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) →
      ∀ (B : ℝ), (1 : ℝ) ≤ B → ∀ (G : ℝ), (1 : ℝ) ≤ G →
      Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ≤ G →
      (1 : ℝ) ≤ S.Dstar → (2 : ℝ) ≤ S.Dm → (↑S.dmax : ℝ) + (5 : ℝ) ≤ B →
      Real.log ((2 : ℝ) * S.Dm) ≤ B →
    Vl0 ≤ 14000000 * B ^ 2 * G := by
  intro k cc S Vl0 hVl0 B hBB1 G hG1 hGqG hD1 hDm2 hdmB hDmB
  rw [hVl0]
  have! hd0 : (0 : ℝ) ≤ S.dmax := Nat.cast_nonneg _
  have! hDm2' : (1 : ℝ) ≤ 2 * S.Dm := by linarith only [hDm2]
  have! hlDm0 : 0 ≤ Real.log (2 * S.Dm) := Real.log_nonneg hDm2'
  have! hfl : ((⌊180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℕ) : ℝ) ≤
      184320 * B ^ 2 := by
    refine (Nat.floor_le (by positivity)).trans ?_
    have! h1 : (S.dmax : ℝ) ≤ B := by linarith only [hdmB]
    have! h2 := mul_le_mul h1 hDmB hlDm0 (by linarith only [hBB1])
    rw [div_div_eq_mul_div, div_one]
    nlinarith only [h2]
  have! hGq' : Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394 ≤ 3 * G := by
    have! h1 : 2 * 1 / S.Dstar ^ 394 ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have! this := one_le_pow₀ (n := 394) hD1
      linarith only [this]
    linarith only [h1, hGqG, hG1]
  have! hBB2' : (1 : ℝ) ≤ B ^ 2 := one_le_pow₀ hBB1
  have! h0 : (0 : ℝ) ≤ Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394 := by positivity
  calc 24 * (((⌊180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℕ) : ℝ) + 1) *
        (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
          (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394)
      ≤ 24 * (184321 * B ^ 2) * (3 * G) := by
        gcongr; linarith only [hfl, hBB2']
    _ ≤ 14000000 * B ^ 2 * G := by nlinarith only [hBB2', hG1]

/-- Step `hT` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hT :
    ∀ (κ : LocalKernelClass) (cT : ℝ) (k : ℕ) (cc : ℕ) (famFuel : ℕ) (E : ℝ) (ρ : ℝ), (0 : ℝ) ≤ E →
      (0 : ℝ) < ρ → ∀ (S : ModeSchedule), (1 : ℕ) ≤ S.K → ∀ (Vl0 : ℝ) (TT : ℝ),
      TT ≤ (10 : ℝ) ^ (14 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ) * (↑((2 : ℕ) ^
        famFuel) : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ)) ^ (2 : ℕ) *
        ((1 : ℝ) + (↑S.K : ℝ)) ^ (2 : ℕ) * (Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) +
        (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + E + Vl0 + (1 : ℝ)) / ρ →
      cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ) → ∀ (B : ℝ),
      (2 : ℝ) ≤ B → (1 : ℝ) ≤ B → ∀ (G : ℝ), (1 : ℝ) ≤ G →
      Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) *
        (↑k : ℝ))) ^ (2 : ℕ)) ≤ G → (↑S.K : ℝ) ≤ B → E ≤ B → ρ⁻¹ ≤ B →
      (↑((2 : ℕ) ^ famFuel) : ℝ) ≤ B → (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ) ≤ B →
      (0 : ℝ) ≤ Vl0 → Vl0 ≤ (14000000 : ℝ) * B ^ (2 : ℕ) * G →
    TT ≤ cT * B ^ 11 * G := by
  intro κ cT k cc famFuel E ρ hE0 hρ S hK1 Vl0 TT hTTle hcT B hBB2 hBB1 G hG1 hG0G hKB hEB hρB
    hLpB hJmB hVl00 hVl0B
  refine hTTle.trans ?_
  have! hL0 := localFormUniformConstant_nonneg κ
  have! hK1' : (1 : ℝ) + S.K ≤ 2 * B := by linarith only [hKB, hBB1]
  have! hW : Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2) + E + Vl0 + 1 ≤ 15000000 * B ^ 2 * G := by
    have! hBB2' : (1 : ℝ) ≤ B ^ 2 := one_le_pow₀ hBB1
    nlinarith only [hG0G, hEB, hVl0B, hBB2', hG1, hBB1]
  have! hJ1 : (1 : ℝ) + ((2 * famFuel + 2 : ℕ) : ℝ) ≤ B := by linarith only [hJmB]
  have! hρ' : 1 / ρ ≤ B := by rw [one_div]; exact hρB
  rw [div_eq_mul_one_div]
  calc 10 ^ 14 * (1 + localFormUniformConstant κ) ^ 2 * (((2 ^ famFuel : ℕ) : ℝ)) ^ 4 *
        (1 + ((2 * famFuel + 2 : ℕ) : ℝ)) ^ 2 * (1 + (S.K : ℝ)) ^ 2 *
        (Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
          (1 + Real.log (2 * (k : ℝ))) ^ 2) + E + Vl0 + 1) * (1 / ρ)
      ≤ 10 ^ 14 * (1 + localFormUniformConstant κ) ^ 2 * B ^ 4 * B ^ 2 * (2 * B) ^ 2 *
          (15000000 * B ^ 2 * G) * B := by
        gcongr
    _ = 6 * 10 ^ 21 * (1 + localFormUniformConstant κ) ^ 2 * B ^ 11 * G := by ring
    _ ≤ cT * B ^ 11 * G := by
        rw [hcT]
        have! this : (0 : ℝ) ≤ (1 + localFormUniformConstant κ) ^ 2 * B ^ 11 * G := by positivity
        nlinarith only [this]

/-- Step `hT2` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hT2 :
    ∀ (k : ℕ) (cc : ℕ) (ρ : ℝ), (0 : ℝ) < ρ → ∀ (S : ModeSchedule) (Vl0 : ℝ) (T2v : ℝ),
      T2v ≤ (4 : ℝ) * ((↑S.K : ℝ) * ((20 : ℝ) * Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) +
        (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (32 : ℝ)) + (↑S.K : ℝ) *
        Vl0) / ρ → ∀ (B : ℝ), (2 : ℝ) ≤ B → (1 : ℝ) ≤ B → ∀ (G : ℝ), (1 : ℝ) ≤ G →
      Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) *
        (↑k : ℝ))) ^ (2 : ℕ)) ≤ G → (↑S.K : ℝ) ≤ B → (0 : ℝ) ≤ Vl0 →
      Vl0 ≤ (14000000 : ℝ) * B ^ (2 : ℕ) * G → (1 : ℝ) / ρ ≤ B →
    T2v ≤ 60000000 * B ^ 4 * G := by
  intro k cc ρ hρ S Vl0 T2v hT2le B hBB2 hBB1 G hG1 hG0G hKB hVl00 hVl0B hρ1'
  refine hT2le.trans ?_
  have! hK0 : (0 : ℝ) ≤ S.K := Nat.cast_nonneg _
  have! h1 : (S.K : ℝ) * (20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) +
      cc ^ 2 + 3) * (1 + Real.log (2 * (k : ℝ))) ^ 2) + 32) ≤ B * (52 * G) :=
    mul_le_mul hKB (by linarith only [hG0G, hG1]) (by positivity) (by linarith only [hBB1])
  have! h2 : (S.K : ℝ) * Vl0 ≤ B * (14000000 * B ^ 2 * G) :=
    mul_le_mul hKB hVl0B hVl00 (by linarith only [hBB1])
  rw [div_eq_mul_one_div]
  calc 4 * ((S.K : ℝ) * (20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) +
        cc ^ 2 + 3) * (1 + Real.log (2 * (k : ℝ))) ^ 2) + 32) + S.K * Vl0) * (1 / ρ)
      ≤ 4 * (B * (52 * G) + B * (14000000 * B ^ 2 * G)) * B := by
        gcongr
    _ ≤ 60000000 * B ^ 4 * G := by
        have! this : (0 : ℝ) ≤ B ^ 4 * G := by positivity
        have! h4 : B ^ 2 * G ≤ B ^ 4 * G := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hBB1 (by norm_num)) (by linarith only [hG1])
        nlinarith only [this, h4, hBB1, hG1]

/-- Step `hsT2` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hsT2 :
    ∀ (T2v : ℝ) (B : ℝ) (G : ℝ), (1 : ℝ) ≤ G → T2v ≤ (60000000 : ℝ) * B ^ (4 : ℕ) * G →
    Real.sqrt T2v ≤ 7746 * B ^ 2 * G := by
  intro T2v B G hG1 hT2
  have! h1 : T2v ≤ (7746 * B ^ 2 * G) ^ 2 := by
    calc T2v ≤ 60000000 * B ^ 4 * G := hT2
      _ ≤ 60000516 * B ^ 4 * G ^ 2 := by
          have! h0 : (0 : ℝ) ≤ B ^ 4 := by positivity
          have! h1 : B ^ 4 * G ≤ B ^ 4 * G ^ 2 :=
            mul_le_mul_of_nonneg_left (le_self_pow₀ hG1 (by norm_num)) h0
          have! h2 : 0 ≤ B ^ 4 * G ^ 2 := by positivity
          linarith only [h1, h2]
      _ = (7746 * B ^ 2 * G) ^ 2 := by ring
  calc Real.sqrt T2v ≤ Real.sqrt ((7746 * B ^ 2 * G) ^ 2) := Real.sqrt_le_sqrt h1
    _ = 7746 * B ^ 2 * G := Real.sqrt_sq (by positivity)

/-- Step `hlogU` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hlogU :
    ∀ (g : ℕ) (cT : ℝ) (Cb : ℕ) (k : ℕ) (cc : ℕ) (cb : ℝ), (2 : ℝ) ≤ cb →
      Real.log ((2 : ℝ) * cb) ≤ (↑k : ℝ) ^ cc → ∀ (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar →
      ∀ (TT : ℝ), (0 : ℝ) ≤ TT → ∀ (U : ℝ),
      U = max ((2 : ℝ) * (cb + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √TT → ∀ (B : ℝ), (20 : ℝ) ≤ (↑Cb : ℝ) →
      (2 : ℝ) ≤ B → (1 : ℝ) ≤ B → (∀ (c : ℝ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → c * (↑k : ℝ) ^ cc ≤ B) →
      ∀ (X : ℝ), (0 : ℝ) ≤ X → X ≤ (4 : ℝ) * (↑k : ℝ) → ∀ (G : ℝ), G = Real.exp ((↑g : ℝ) * X) →
      (1 : ℝ) ≤ G → (1 : ℝ) ≤ S.Dstar → Real.log S.Dstar ≤ B → (↑k : ℝ) ≤ B → (0 : ℝ) < U →
      TT ≤ cT * B ^ (11 : ℕ) * G → (1 : ℝ) ≤ cT → (1 : ℝ) ≤ cT * B ^ (11 : ℕ) * G →
    Real.log U ≤ (17 + 4 * g + Real.log cT) * B := by
  intro g cT Cb k cc cb hcb hkb S hD2 TT hT0 U hUdef B hCb20 hBB2 hBB1 hkcc X hX0 hX4 G hGdef hG1
    hD1 hlDB hkB' hU0 hTT1 hcT1 hBGT
  have! ha1 : (1 : ℝ) ≤ 2 * (cb + 2) * S.Dstar ^ 2 := by
    have! this := one_le_pow₀ (n := 2) hD1
    nlinarith only [this, hcb]
  have! hsTT : Real.sqrt TT ≤ 2 + TT := by
    have! this := Real.sqrt_le_sqrt (show TT ≤ (1 + TT) ^ 2 by nlinarith only [hT0])
    rw [Real.sqrt_sq (by linarith only [hT0])] at this; linarith only [this]
  have! hUle : U ≤ 2 * (cb + 2) * S.Dstar ^ 2 * (1 + Real.sqrt TT) := by
    rw [hUdef]
    have! h0 := Real.sqrt_nonneg TT
    refine max_le (le_mul_of_one_le_right (by linarith only [ha1]) (by linarith only [h0]))
      ?_
    nlinarith only [h0, ha1]
  have! h1 : Real.log U ≤ Real.log (2 * (cb + 2) * S.Dstar ^ 2) +
      Real.log (1 + Real.sqrt TT) := by
    rw [← Real.log_mul (by linarith only [ha1]) (by positivity)]
    exact Real.log_le_log hU0 hUle
  have! h2 : Real.log (2 * (cb + 2) * S.Dstar ^ 2) ≤ 1 + (k : ℝ) ^ cc + 2 * B := by
    have! hcb4 : cb + 2 ≤ 2 * cb := by linarith only [hcb]
    rw [Real.log_mul (by linarith only [hcb]) (by positivity), Real.log_pow]
    have! h3 : Real.log (2 * (cb + 2)) ≤ Real.log (2 * (2 * cb)) :=
      Real.log_le_log (by linarith only [hcb]) (by linarith only [hcb4])
    have! h4 : Real.log (2 * (2 * cb)) = Real.log 2 + Real.log (2 * cb) := by
      rw [Real.log_mul (by norm_num) (by linarith only [hcb])]
    have! hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    push_cast
    linarith only [h3, h4, hl2, hkb, hlDB]
  have! h3 : Real.log (1 + Real.sqrt TT) ≤ 2 + Real.log cT + 11 * B + 4 * g * B := by
    have! h5 : 1 + Real.sqrt TT ≤ 4 * (cT * B ^ 11 * G) := by linarith only [hsTT, hTT1, hBGT]
    have! h6 := Real.log_le_log (by positivity) h5
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow, hGdef,
      Real.log_exp] at h6
    have! hl3 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith only [Real.log_two_lt_d9]
    have! hlB : Real.log B ≤ B := by
      have! this := Real.log_le_sub_one_of_pos (show (0 : ℝ) < B by linarith only [hBB1])
      linarith only [this]
    have! hgX : (g : ℝ) * X ≤ 4 * g * B := by
      have! this : X ≤ 4 * B := by linarith only [hX4, hkB']
      nlinarith only [this, Nat.cast_nonneg (α := ℝ) g, hX0]
    push_cast at h6
    linarith only [h6, hl3, hlB, hgX]
  have! hlc : 0 ≤ Real.log cT := Real.log_nonneg hcT1
  have! hkB1 := hkcc 1 (by norm_num) (by linarith only [hCb20])
  have! hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  have! hlcB : Real.log cT ≤ Real.log cT * B := le_mul_of_one_le_right hlc hBB1
  nlinarith only [h1, h2, h3, hkB1, hlcB, hBB1, hg0]

/-- Step `hlogMV` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hlogMV :
    ∀ (Cb : ℕ) (k : ℕ) (cc : ℕ) (Mp : ℕ) (V : ℕ) (MV : ℝ), MV = (↑Mp : ℝ) * (↑V : ℝ) → ∀ (B : ℝ),
      (20 : ℝ) ≤ (↑Cb : ℝ) → (1 : ℝ) ≤ B →
      (∀ (c : ℝ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → c * (↑k : ℝ) ^ cc ≤ B) →
      (↑Mp : ℝ) ≤ Real.exp ((↑k : ℝ) ^ cc) → (↑V : ℝ) ≤ (5 : ℝ) * Real.exp ((↑k : ℝ) ^ cc) →
      (0 : ℝ) ≤ MV →
    Real.log (1 + MV) ≤ 4 * B := by
  intro Cb k cc Mp V MV hMV B hCb20 hBB1 hkcc hMpexp hVexp hMV0
  have! h1 : 1 + MV ≤ 6 * Real.exp (2 * (k : ℝ) ^ cc) := by
    rw [hMV]
    have! h2 : (Mp : ℝ) * V ≤ Real.exp ((k : ℝ) ^ cc) *
        (5 * Real.exp ((k : ℝ) ^ cc)) := mul_le_mul hMpexp hVexp (Nat.cast_nonneg _)
          (Real.exp_pos _).le
    have! h3 : Real.exp (2 * (k : ℝ) ^ cc) =
        Real.exp ((k : ℝ) ^ cc) * Real.exp ((k : ℝ) ^ cc) := by
      rw [← Real.exp_add]; ring_nf
    have! h4 : (1 : ℝ) ≤ Real.exp (2 * (k : ℝ) ^ cc) := Real.one_le_exp (by positivity)
    nlinarith only [h2, h3, h4]
  have! h2 := Real.log_le_log (by linarith only [hMV0]) h1
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
  have! hl6 : Real.log 6 ≤ 2 := by
    have! this := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num) (by norm_num)
    have! h7 : Real.log 6 < 2 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have! h8 : (2.7 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
        pow_le_pow_left₀ (by norm_num) (by linarith only [this]) 2
      rw [← Real.exp_nat_mul] at h8; norm_num at h8; linarith only [h8]
    exact h7.le
  have! this := hkcc 1 (by norm_num) (by linarith only [hCb20])
  linarith only [h2, hl6, this, hBB1]

/-- Step `hlogUε` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hlogUε :
    ∀ (g : ℕ) (cT : ℝ) (k : ℕ) (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (U : ℝ) (MV : ℝ) (ε : ℝ)
      (B : ℝ), (2 : ℝ) ≤ B → (1 : ℝ) ≤ B → Real.log S.Dstar ≤ B → (↑k : ℝ) ≤ B → (16 : ℝ) ≤ U →
      (0 : ℝ) ≤ MV → (1 : ℝ) ≤ cT →
      U / ε = U ^ (4 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV) →
      Real.log U ≤ ((17 : ℝ) + (4 : ℝ) * (↑g : ℝ) + Real.log cT) * B →
      Real.log ((1 : ℝ) + MV) ≤ (4 : ℝ) * B →
    Real.log (U / ε) ≤ (78 + 16 * g + 4 * Real.log cT) * B := by
  intro g cT k S hD2 U MV ε B hBB2 hBB1 hlDB hkB' hU16 hMV0 hcT1 hUε hlogU hlogMV
  rw [hUε, Real.log_mul (by positivity) (by linarith only [hMV0]), Real.log_mul (by positivity)
    (Real.exp_pos _).ne', Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_exp]
  have! hlc : 0 ≤ Real.log cT := Real.log_nonneg hcT1
  have! hlcB : Real.log cT ≤ Real.log cT * B := le_mul_of_one_le_right hlc hBB1
  push_cast
  linarith only [hlogU, hlDB, hkB', hlogMV, hBB2, hlcB]

/-- Step `hcL0` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hcL0 :
    ∀ (g : ℕ) (cT : ℝ) (cL : ℝ), cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8 : ℝ) * Real.log cT →
      (1 : ℝ) ≤ cT →
    0 ≤ cL := by
  intro g cT cL hcL hcT1
  rw [hcL]; have := Real.log_nonneg hcT1; positivity

/-- Step `hMtB` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hMtB :
    ∀ (cL : ℝ) (k : ℕ) (cc : ℕ) (ρ : ℝ), (0 : ℝ) < ρ → ∀ (S : ModeSchedule) (Vl0 : ℝ) (U : ℝ)
      (ε : ℝ) (Mt : ℝ) (B : ℝ), (1 : ℝ) ≤ B → ∀ (G : ℝ), (1 : ℝ) ≤ G → (↑S.K : ℝ) ≤ B →
      (↑S.Jstar : ℝ) + (1 : ℝ) ≤ B → (0 : ℝ) ≤ Vl0 → Vl0 ≤ (14000000 : ℝ) * B ^ (2 : ℕ) * G →
      (1 : ℝ) / ρ ≤ B → (0 : ℝ) ≤ cL →
    let Gq : ℝ := Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^
        (2 : ℕ));
    Gq ≤ G →
    let Ts : Finset (ℕ × ℕ) := Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range
        (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ));
    Mt = (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range (S.Jstar +
        (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ →
      (↑Ts.card : ℝ) ≤ ((3 : ℝ) * B) ^ (2 : ℕ) →
      (↑(dyThr ε U S.Dstar).card : ℝ) ≤ cL * B + (2 : ℝ) →
    Mt ≤ 7000000000 * B ^ 7 * G * (cL * B + 2) := by
  intro cL k cc ρ hρ S Vl0 U ε Mt B hBB1 G hG1 hKB hJB hVl00 hVl0B hρ1' hcL0 Gq hGqG Ts hMt
    hcardTs hcardThr
  rw [hMt, Finset.card_product, Finset.card_product, Finset.card_range]
  push_cast
  have! hK0 : (0 : ℝ) ≤ S.K := Nat.cast_nonneg _
  have! h1 : 2 * Gq + 2 * (S.K : ℝ) * Vl0 ≤ 28000002 * B ^ 3 * G := by
    have! h2 : (S.K : ℝ) * Vl0 ≤ B * (14000000 * B ^ 2 * G) :=
      mul_le_mul hKB hVl0B hVl00 (by linarith only [hBB1])
    have! h3 : (1 : ℝ) ≤ B ^ 3 := one_le_pow₀ hBB1
    have! h4 : G ≤ B ^ 3 * G := le_mul_of_one_le_left (by linarith only [hG1]) h3
    nlinarith only [h2, h4, hGqG]
  have! hJ0 : (0 : ℝ) ≤ (S.Jstar : ℝ) + 1 := by positivity
  have! hT0' : (0 : ℝ) ≤ Ts.card := Nat.cast_nonneg _
  have! hThr0' : (0 : ℝ) ≤ (dyThr ε U S.Dstar).card := Nat.cast_nonneg _
  rw [div_eq_mul_one_div]
  calc 24 * (2 * Gq + 2 * (S.K : ℝ) * Vl0) * (((S.Jstar : ℝ) + 1) *
        ((Ts.card : ℝ) * ((dyThr ε U S.Dstar).card : ℝ))) * (1 / ρ)
      ≤ 24 * (28000002 * B ^ 3 * G) * (B * ((3 * B) ^ 2 * (cL * B + 2))) * B := by
        have! hBnn : 0 ≤ B := by linarith only [hBB1]
        have! hcLB : 0 ≤ cL * B + 2 := by nlinarith only [hcL0, hBnn]
        have! hc0 : (0 : ℝ) ≤ (Ts.card : ℝ) * ((dyThr ε U S.Dstar).card : ℝ) :=
          mul_nonneg hT0' hThr0'
        refine mul_le_mul (mul_le_mul (by linarith only [h1]) (mul_le_mul hJB
            (mul_le_mul hcardTs hcardThr hThr0' (sq_nonneg _)) hc0 hBnn) (mul_nonneg hJ0 hc0)
            (by positivity)) hρ1' (by rw [one_div]; exact (inv_pos.mpr hρ).le) ?_
        exact mul_nonneg (by positivity) (mul_nonneg hBnn (mul_nonneg (sq_nonneg _) hcLB))
    _ = 6048000432 * B ^ 7 * G * (cL * B + 2) := by ring
    _ ≤ 7000000000 * B ^ 7 * G * (cL * B + 2) := by
        have! this : (0 : ℝ) ≤ B ^ 7 * G * (cL * B + 2) := by positivity
        nlinarith only [this]

/-- Step `hKcB` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hKcB :
    ∀ (cT : ℝ) (cL : ℝ) (cK : ℝ) (TT : ℝ), (0 : ℝ) ≤ TT → ∀ (Mt : ℝ),
      cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2 : ℝ)) → ∀ (B : ℝ), (1 : ℝ) ≤ B →
      ∀ (G : ℝ), (1 : ℝ) ≤ G → TT ≤ cT * B ^ (11 : ℕ) * G → (1 : ℝ) ≤ cT → (0 : ℝ) ≤ cL →
      Mt ≤ (7000000000 : ℝ) * B ^ (7 : ℕ) * G * (cL * B + (2 : ℝ)) → (0 : ℝ) ≤ Mt →
    let Kc : ℝ := max (max (1 : ℝ) Mt) TT;
    Kc ≤ cK * B ^ 12 * G := by
  intro cT cL cK TT hT0 Mt hcK B hBB1 G hG1 hT hcT1 hcL0 hMtB hMt0 Kc
  have! hB12 : (1 : ℝ) ≤ B ^ 12 * G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hBB1) hG1
  have! h1 : Mt ≤ 7000000000 * (cL + 2) * (B ^ 12 * G) := by
    refine hMtB.trans ?_
    have! h2 : B ^ 7 * B ≤ B ^ 12 := by
      rw [← pow_succ]; exact pow_le_pow_right₀ hBB1 (by norm_num)
    have! h3 : cL * B + 2 ≤ (cL + 2) * B := by nlinarith only [hBB1, hcL0]
    have! h4 : 0 ≤ B ^ 7 * G := by positivity
    calc 7000000000 * B ^ 7 * G * (cL * B + 2) ≤ 7000000000 * B ^ 7 * G * ((cL + 2) * B) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 7000000000 * (cL + 2) * (B ^ 7 * B * G) := by ring
      _ ≤ 7000000000 * (cL + 2) * (B ^ 12 * G) := by gcongr
  have! h2 : TT ≤ cT * (B ^ 12 * G) := by
    refine hT.trans ?_
    have! this : B ^ 11 ≤ B ^ 12 := pow_le_pow_right₀ hBB1 (by norm_num)
    have! h0 : 0 ≤ cT := by linarith only [hcT1]
    calc cT * B ^ 11 * G = cT * (B ^ 11 * G) := by ring
      _ ≤ cT * (B ^ 12 * G) := by gcongr
  have! hle : Kc ≤ 1 + Mt + TT := max_le (max_le (by linarith only [hMt0, hT0])
    (by linarith only [hT0])) (by linarith only [hMt0])
  have! hcK' : (1 + 7000000000 * (cL + 2) + cT) ≤ cK := by
    rw [hcK]; nlinarith only [hcL0, hcT1]
  have! hBG0 : 0 ≤ B ^ 12 * G := by positivity
  calc Kc ≤ 1 + Mt + TT := hle
    _ ≤ (1 + 7000000000 * (cL + 2) + cT) * (B ^ 12 * G) := by nlinarith only [h1, h2, hB12]
    _ ≤ cK * (B ^ 12 * G) := mul_le_mul_of_nonneg_right hcK' hBG0
    _ = cK * B ^ 12 * G := by ring

/-- Step `hcMtot` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hcMtot :
    ∀ (κ : LocalKernelClass) (cL : ℝ) (cK : ℝ) (cMc : ℝ) (TT : ℝ) (Mt : ℝ) (cM4 : ℝ) (cM3 : ℝ),
      cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) → ∀ (B : ℝ), (1 : ℝ) ≤ B →
      ∀ (G : ℝ),
    let Kc : ℝ := max (max (1 : ℝ) Mt) TT;
    (1 : ℝ) ≤ Kc → Kc ≤ cK * B ^ (12 : ℕ) * G →
      cM4 ≤ C4c κ * B ^ (30 : ℕ) * (cL * B) ^ (4 : ℕ) * Kc ^ (2 : ℕ) →
      cM3 ≤ (4 : ℝ) * (C3c κ * B ^ (30 : ℕ) * B * (cL * B) ^ (4 : ℕ) * Kc ^ (2 : ℕ)) →
    cM4 + cM3 ≤ cMc * B ^ 59 * G ^ 2 := by
  intro κ cL cK cMc TT Mt cM4 cM3 hcMc B hBB1 G Kc hKc1 hKcB hcM4' hcM3'
  have! h4 := C4c_nonneg κ
  have! h3 := C3c_nonneg κ
  have! hK2 : Kc ^ 2 ≤ (cK * B ^ 12 * G) ^ 2 := pow_le_pow_left₀ (by linarith only [hKc1]) hKcB 2
  have! hB30 : B ^ 30 ≤ B ^ 30 * B := le_mul_of_one_le_right (by positivity) hBB1
  have! hX0' : 0 ≤ (cL * B) ^ 4 * Kc ^ 2 := by positivity
  calc cM4 + cM3
      ≤ C4c κ * B ^ 30 * (cL * B) ^ 4 * Kc ^ 2 +
          4 * (C3c κ * B ^ 30 * B * (cL * B) ^ 4 * Kc ^ 2) := add_le_add hcM4' hcM3'
    _ ≤ (C4c κ + 4 * C3c κ) * (B ^ 30 * B) * ((cL * B) ^ 4 * Kc ^ 2) := by
        have! this := mul_le_mul_of_nonneg_left hB30 h4
        nlinarith only [this, hX0']
    _ ≤ (C4c κ + 4 * C3c κ) * (B ^ 30 * B) * ((cL * B) ^ 4 * (cK * B ^ 12 * G) ^ 2) := by
        gcongr
    _ = cMc * B ^ 59 * G ^ 2 := by rw [hcMc]; ring

/-- Step `hME` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hME :
    ∀ (κ : LocalKernelClass) (k : ℕ) (cc : ℕ) (cb : ℝ) (Nl : ℝ) (Mp : ℕ) (V : ℕ), (2 : ℝ) ≤ cb →
      (4 : ℝ) ≤ Nl → ∀ (dB : ℕ), (1 : ℕ) ≤ dB → ∀ (δ : ℝ) (R : ℝ), (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) →
      (0 : ℝ) < R → ∀ (S : ModeSchedule) (Iw : ℕ) (U : ℝ) (ε : ℝ) (cE : ℝ),
      cE ≤ ((16 : ℝ) * fourErrC κ (3 : ℕ) * ((S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ)) + K1c *
        ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) +
        (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * ((S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^
        (10 : ℕ)) * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) +
        (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) +
        (1 : ℝ)))))) * ((↑(Mp * V) : ℝ) * R) → ∀ (Ee : ℝ), (0 : ℝ) ≤ Ee →
      Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * cb ^ (2 : ℕ) *
        (1 : ℝ)) * (↑((4 : ℕ) * (Mp * V)) : ℝ) * R → (0 : ℝ) ≤ Nl → ∀ (E1 : ℝ),
      E1 = Real.exp ((↑k : ℝ) ^ cc) → (1 : ℝ) ≤ E1 → (↑Mp : ℝ) ≤ E1 → (↑V : ℝ) ≤ (5 : ℝ) * E1 →
      cb ≤ E1 → Nl ≤ E1 → (↑dB : ℝ) ≤ E1 →
    Real.sqrt (4 * (((Mp * V : ℕ) : ℝ) * R)) *
    Real.sqrt Ee ≤ 288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ * R := by
  intro κ k cc cb Nl Mp V hcb hNl4 dB hdB1 δ R hδ hδ8 hRl0 S Iw U ε cE hcEsum Ee hEe0 hEeb hNl0 E1
    hE1 hE11 hMpE hVE1 hcbE hNlE hdBE
  have hEe00 : 0 ≤ Ee := hEe0
  have! hMV' : (((Mp * V : ℕ) : ℝ)) ≤ 5 * E1 ^ 2 := by
    push_cast
    have! this := mul_le_mul hMpE hVE1 (Nat.cast_nonneg _) (by linarith only [hE11])
    nlinarith only [this]
  have! hMV0' : (0 : ℝ) ≤ (((Mp * V : ℕ) : ℝ)) := Nat.cast_nonneg _
  have! hδ1 : δ ≤ 1 := by linarith only [hδ8]
  have! hdB1' : (1 : ℝ) ≤ dB := by exact_mod_cast hdB1
  have! hc : Nl * (8 * dB * δ + 2 * δ ^ 2) ≤ 10 * E1 ^ 2 * δ := by
    have! h1 : 8 * dB * δ + 2 * δ ^ 2 ≤ 10 * dB * δ := by nlinarith only [hδ, hδ1, hdB1']
    have! h2 : Nl * (10 * dB * δ) ≤ E1 * (10 * E1 * δ) :=
      mul_le_mul hNlE (by nlinarith only [hdBE, hδ]) (by positivity) (by linarith only [hE11])
    have! h3 : Nl * (8 * dB * δ + 2 * δ ^ 2) ≤ Nl * (10 * dB * δ) :=
      mul_le_mul_of_nonneg_left h1 hNl0
    nlinarith only [h2, h3]
  have! hb : cb ^ 2 ≤ E1 ^ 2 := pow_le_pow_left₀ (by linarith only [hcb]) hcbE 2
  have! hprod : 4 * (((Mp * V : ℕ) : ℝ) * R) * Ee ≤
      (288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ * R) ^ 2 := by
    have! hE4 : Real.exp (4 * (k : ℝ) ^ cc) = E1 ^ 4 := by
      rw [hE1, ← Real.exp_nat_mul]; norm_num
    have! hsδ : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
    rw [hE4, mul_pow, mul_pow, mul_pow, hsδ]
    set! m := (((Mp * V : ℕ) : ℝ)) with hm
    rewrite [← hm] at hcEsum hMV' hMV0' ⊢
    have! hEe1 : Ee ≤ (Nl * (8 * dB * δ + 2 * δ ^ 2)) * (16 * cb ^ 2) * m * R := by
      refine hEeb.trans (le_of_eq ?_)
      rw [hm]
      push_cast
      ring
    have! h1 : 4 * (m * R) * Ee ≤ 4 * (m * R) * ((Nl * (8 * dB * δ + 2 * δ ^ 2)) *
        (16 * cb ^ 2) * m * R) := mul_le_mul_of_nonneg_left hEe1 (by positivity)
    have! h2 : 4 * (m * R) * ((Nl * (8 * dB * δ + 2 * δ ^ 2)) * (16 * cb ^ 2) * m * R) =
        64 * (m * m) * (Nl * (8 * dB * δ + 2 * δ ^ 2)) * cb ^ 2 * R ^ 2 := by ring
    have! hmm : m * m ≤ (5 * E1 ^ 2) * (5 * E1 ^ 2) := mul_le_mul hMV' hMV' hMV0' (by positivity)
    have! hnn : 0 ≤ Nl * (8 * dB * δ + 2 * δ ^ 2) := by positivity
    have! h3 : 64 * (m * m) * (Nl * (8 * dB * δ + 2 * δ ^ 2)) * cb ^ 2 * R ^ 2 ≤
        64 * ((5 * E1 ^ 2) * (5 * E1 ^ 2)) * (10 * E1 ^ 2 * δ) * E1 ^ 2 * R ^ 2 := by
      gcongr
    have! h4 : 64 * ((5 * E1 ^ 2) * (5 * E1 ^ 2)) * (10 * E1 ^ 2 * δ) * E1 ^ 2 * R ^ 2 ≤
        288 ^ 2 * (E1 ^ 4) ^ 2 * δ * R ^ 2 := by
      have! this : 0 ≤ E1 ^ 8 * δ * R ^ 2 := by positivity
      nlinarith only [this]
    linarith only [h1, h2, h3, h4]
  rw [← Real.sqrt_mul (by positivity)]
  calc Real.sqrt (4 * (((Mp * V : ℕ) : ℝ) * R) * Ee)
      ≤ Real.sqrt ((288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ *
        R) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = _ := Real.sqrt_sq (by positivity)

/-- Step `hQe0` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hQe0 :
    ∀ (κ : LocalKernelClass) (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (Iw : ℕ) (U : ℝ) (ε : ℝ),
      (16 : ℝ) ≤ U → (0 : ℝ) < ε → ∀ (ι : ℝ), (0 : ℝ) ≤ ι →
    let Qe : ℝ := (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) *
        (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) *
        threeErrC κ (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) *
        (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^
        (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))));
    Qe = (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
        (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ)
        (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) +
        (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) +
        (1 : ℝ))))) →
    0 ≤ Qe := by
  intro κ S hD2 Iw U ε hU16 hε0 ι hι0 Qe hQe
  rw [hQe]
  have! this := fourErrC_nonneg κ 3; have := threeErrC_nonneg κ 3 1; have := fourKC_nonneg κ 3
  have! this := entryCU_nonneg' κ 3 1; have := K1c_pos
  positivity

/-- Step `hε4` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hε4 :
    ∀ (k : ℕ) (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (U : ℝ) (MV : ℝ) (ε : ℝ),
      ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹ →
      (1 : ℝ) ≤ S.Dstar → (16 : ℝ) ≤ U → (0 : ℝ) ≤ MV →
    ε * U ^ 3 * S.Dstar ^ 4 * MV ≤ Real.exp (-(k : ℝ)) := by
  intro k S hD2 U MV ε hεdef hD1 hU16 hMV0
  have! e : ε * U ^ 3 * S.Dstar ^ 4 * MV =
      MV / (1 + MV) * (S.Dstar⁻¹ * (Real.exp k)⁻¹) := by
    rw [hεdef]; field_simp
  rw [e, Real.exp_neg]
  have! h1 : MV / (1 + MV) ≤ 1 := by
    rw [div_le_one (by linarith only [hMV0])]; linarith only []
  have! h2 : S.Dstar⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD1
  have! h0 : 0 ≤ MV / (1 + MV) := by positivity
  calc MV / (1 + MV) * (S.Dstar⁻¹ * (Real.exp k)⁻¹) ≤ 1 * (1 * (Real.exp k)⁻¹) := by
        gcongr
    _ = (Real.exp k)⁻¹ := by ring

/-- Step `hε3` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hε3 :
    ∀ (k : ℕ) (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (Iw : ℕ) (U : ℝ) (MV : ℝ) (ε : ℝ),
      ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹ → (16 : ℝ) ≤ U →
      (0 : ℝ) ≤ MV → (↑Iw : ℝ) + (1 : ℝ) ≤ (501 : ℝ) * S.Dstar ^ (2 : ℕ) →
    ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)) * MV ≤ 501 * Real.exp (-(k : ℝ)) := by
  intro k S hD2 Iw U MV ε hεdef hU16 hMV0 hIwD
  have! e : ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)) * MV =
      MV / (1 + MV) * (((Iw : ℝ) + 1) / S.Dstar ^ 2 * (Real.exp k)⁻¹) := by
    rw [hεdef]; field_simp
  rw [e, Real.exp_neg]
  have! h1 : MV / (1 + MV) ≤ 1 := by
    rw [div_le_one (by linarith only [hMV0])]; linarith only []
  have! h2 : ((Iw : ℝ) + 1) / S.Dstar ^ 2 ≤ 501 := by
    rw [div_le_iff₀ (by positivity)]; exact hIwD
  have! h0 : 0 ≤ MV / (1 + MV) := by positivity
  have! h3 : 0 ≤ ((Iw : ℝ) + 1) / S.Dstar ^ 2 := by positivity
  calc MV / (1 + MV) * (((Iw : ℝ) + 1) / S.Dstar ^ 2 * (Real.exp k)⁻¹)
      ≤ 1 * (501 * (Real.exp k)⁻¹) := by gcongr
    _ = 501 * (Real.exp k)⁻¹ := by ring

/-- Step `hE14` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hE14 :
    ∀ (k : ℕ) (cc : ℕ), (1 : ℕ) ≤ cc → (2 : ℝ) ≤ (↑k : ℝ) → (1 : ℝ) ≤ (↑k : ℝ) → ∀ (E1 : ℝ),
      E1 = Real.exp ((↑k : ℝ) ^ cc) →
    4 ≤ E1 := by
  intro k cc hcc hk2 hk1 E1 hE1
  rw [hE1]
  have! this := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) ^ cc by positivity)
  have! h2 : (2 : ℝ) ≤ (k : ℝ) ^ cc := le_trans hk2 (le_self_pow₀ hk1 (by omega))
  nlinarith only [this, h2]

/-- Step `hιU` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hιU :
    ∀ (cb : ℝ), (2 : ℝ) ≤ cb → ∀ (S : ModeSchedule) (TT : ℝ) (U : ℝ),
      U = max ((2 : ℝ) * (cb + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √TT → ∀ (ι : ℝ), (0 : ℝ) ≤ ι →
      ι ≤ S.Dstar⁻¹ → ι * S.Dstar ^ (2 : ℕ) ≤ S.Dstar⁻¹ →
    ι * U ≤ S.Dstar⁻¹ * (2 * (cb + 2) + Real.sqrt TT) := by
  intro cb hcb S TT U hUdef ι hι0 hιD hιD2
  have! hU' : U ≤ 2 * (cb + 2) * S.Dstar ^ 2 + Real.sqrt TT := by
    rw [hUdef]
    exact max_le (by linarith only [Real.sqrt_nonneg TT]) (by
      have! this : 0 ≤ 2 * (cb + 2) * S.Dstar ^ 2 := by
        have := hcb; positivity
      linarith only [this])
  have! h1 := mul_le_mul_of_nonneg_left hU' hι0
  have! h2 : ι * (2 * (cb + 2) * S.Dstar ^ 2) ≤ S.Dstar⁻¹ * (2 * (cb + 2)) := by
    have! this := mul_le_mul_of_nonneg_right hιD2 (show 0 ≤ 2 * (cb + 2) by
      linarith only [hcb])
    linarith only [this]
  have! h3 : ι * Real.sqrt TT ≤ S.Dstar⁻¹ * Real.sqrt TT :=
    mul_le_mul_of_nonneg_right hιD (Real.sqrt_nonneg _)
  linarith only [h1, h2, h3]

/-- Step `hsTT` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hsTT :
    ∀ (cT : ℝ) (TT : ℝ) (B : ℝ), (1 : ℝ) ≤ B → ∀ (G : ℝ), (1 : ℝ) ≤ G → TT ≤ cT * B ^ (11 : ℕ) * G →
      (1 : ℝ) ≤ cT →
    Real.sqrt TT ≤ Real.sqrt cT * B ^ 6 * G := by
  intro cT TT B hBB1 G hG1 hT hcT1
  have! h1 : TT ≤ (Real.sqrt cT * B ^ 6 * G) ^ 2 := by
    have! hc := Real.sq_sqrt (show 0 ≤ cT by linarith only [hcT1])
    have! h11 : B ^ 11 * G ≤ B ^ 12 * G ^ 2 := by
      have! this := pow_le_pow_right₀ hBB1 (show 11 ≤ 12 by norm_num)
      have! hG2 : G ≤ G ^ 2 := le_self_pow₀ hG1 (by norm_num)
      exact mul_le_mul this hG2 (by linarith only [hG1]) (by positivity)
    calc TT ≤ cT * B ^ 11 * G := hT
      _ ≤ cT * (B ^ 12 * G ^ 2) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h11 (by linarith only [hcT1])
      _ = (Real.sqrt cT * B ^ 6 * G) ^ 2 := by rw [mul_pow, mul_pow, hc]; ring
  calc Real.sqrt TT ≤ Real.sqrt ((Real.sqrt cT * B ^ 6 * G) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt cT * B ^ 6 * G := Real.sqrt_sq (by positivity)

/-- Step `hQeMV` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hQeMV :
    ∀ (κ : LocalKernelClass) (cT : ℝ) (ce2 : ℝ) (k : ℕ) (cc : ℕ) (kD : ℝ) (cb : ℝ), (2 : ℝ) ≤ cb →
      ∀ (S : ModeSchedule) (Iw : ℕ) (TT : ℝ) (U : ℝ) (MV : ℝ) (ε : ℝ),
      ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) *
        entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) *
        (501 : ℝ) → ∀ (B : ℝ), (2 : ℝ) ≤ B → (1 : ℝ) ≤ B → ∀ (G : ℝ), (1 : ℝ) ≤ G →
      (2 : ℝ) * cb ≤ Real.exp ((↑k : ℝ) ^ cc) → (0 : ℝ) ≤ MV → ∀ (E1 : ℝ),
      E1 = Real.exp ((↑k : ℝ) ^ cc) → (1 : ℝ) ≤ E1 → cb ≤ E1 → S.Dstar⁻¹ ≤ Real.exp (-kD) →
      ∀ (ι : ℝ), ι ≤ S.Dstar⁻¹ →
    let Qe : ℝ := (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) *
        (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) *
        threeErrC κ (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) *
        (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^
        (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))));
    Qe = (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
        (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ)
        (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) +
        (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) +
        (1 : ℝ))))) → MV ≤ (5 : ℝ) * E1 ^ (2 : ℕ) →
      ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ) * MV ≤ Real.exp (-(↑k : ℝ)) →
      ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ))) * MV ≤ (501 : ℝ) * Real.exp
        (-(↑k : ℝ)) → (4 : ℝ) ≤ E1 → ι * U ≤ S.Dstar⁻¹ * ((2 : ℝ) * (cb + (2 : ℝ)) + √TT) →
      √TT ≤ √cT * B ^ (6 : ℕ) * G →
    Qe * MV ≤ 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 +
    324 * threeErrC κ 3 1 * Real.sqrt cT) * Real.exp (3 * (k : ℝ) ^ cc) * B ^ 6 * G *
    Real.exp (-kD) + ce2 * Real.exp (-(k : ℝ)) := by
  intro κ cT ce2 k cc kD cb hcb S Iw TT U MV ε hce2 B hBB2 hBB1 G hG1 hcbexp hMV0 E1 hE1 hE11 hcbE
    hDinv ι hιD Qe hQe hMVE hε4 hε3 hE14 hιU hsTT
  have! hf := fourErrC_nonneg κ 3
  have! ht := threeErrC_nonneg κ 3 1
  have! hfk := fourKC_nonneg κ 3
  have! hen := entryCU_nonneg' κ 3 1
  have hK1p := K1c_pos
  -- the powers of `D_*`
  have! hA1 : 16 * fourErrC κ 3 * ι * MV + 4 * (81 * threeErrC κ 3 1 * ι * U) * MV ≤
      S.Dstar⁻¹ * MV * (16 * fourErrC κ 3 + 324 * threeErrC κ 3 1 *
        (2 * (cb + 2) + Real.sqrt TT)) := by
    have! h1 : 16 * fourErrC κ 3 * ι * MV ≤ 16 * fourErrC κ 3 * S.Dstar⁻¹ * MV :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hιD (by positivity)) hMV0
    have! h2 : 81 * threeErrC κ 3 1 * (ι * U) * MV ≤
        81 * threeErrC κ 3 1 * (S.Dstar⁻¹ * (2 * (cb + 2) + Real.sqrt TT)) * MV :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hιU (by positivity)) hMV0
    have! e1 : 4 * (81 * threeErrC κ 3 1 * ι * U) * MV =
        4 * (81 * threeErrC κ 3 1 * (ι * U) * MV) := by
      ring
    rw [e1]
    nlinarith only [h1, h2]
  -- the bound by `e^{3 k^c} B^6 G e^{-k_D}`
  have! hcb2 : 2 * (cb + 2) ≤ 2 * E1 := by linarith only [hcbE, hE14, hcbexp, hE1]
  have! hBG : 1 ≤ B ^ 6 * G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hBB1) hG1
  have! hE3 : Real.exp (3 * (k : ℝ) ^ cc) = E1 ^ 3 := by
    rw [hE1, ← Real.exp_nat_mul]; norm_num
  have! hA2 : S.Dstar⁻¹ * MV * (16 * fourErrC κ 3 + 324 * threeErrC κ 3 1 *
      (2 * (cb + 2) + Real.sqrt TT)) ≤ 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 +
        324 * threeErrC κ 3 1 * Real.sqrt cT) * Real.exp (3 * (k : ℝ) ^ cc) * B ^ 6 * G *
          Real.exp (-kD) := by
    rw [hE3]
    have! h1 : 16 * fourErrC κ 3 + 324 * threeErrC κ 3 1 * (2 * (cb + 2) + Real.sqrt TT) ≤
        (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 * Real.sqrt cT) *
          (E1 * (B ^ 6 * G)) := by
      have! hsc : 0 ≤ Real.sqrt cT := Real.sqrt_nonneg _
      have! hEBG : 1 ≤ E1 * (B ^ 6 * G) := one_le_mul_of_one_le_of_one_le hE11 hBG
      have! h2 : 2 * (cb + 2) + Real.sqrt TT ≤ 2 * (E1 * (B ^ 6 * G)) +
          Real.sqrt cT * (E1 * (B ^ 6 * G)) := by
        have! h3 : 2 * E1 ≤ 2 * (E1 * (B ^ 6 * G)) := by nlinarith only [hBG, hE11]
        have! h4 : Real.sqrt cT * B ^ 6 * G ≤ Real.sqrt cT * (E1 * (B ^ 6 * G)) := by
          have! this := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hE11 :
            B ^ 6 * G ≤ E1 * (B ^ 6 * G)) hsc
          linarith only [this]
        linarith only [hcb2, hsTT, h3, h4]
      have! h5 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 324 * threeErrC κ 3 1 by positivity)
      have! h6 : 16 * fourErrC κ 3 ≤ 16 * fourErrC κ 3 * (E1 * (B ^ 6 * G)) :=
        le_mul_of_one_le_right (by positivity) hEBG
      nlinarith only [h5, h6]
    have! h7 : S.Dstar⁻¹ * MV ≤ Real.exp (-kD) * (5 * E1 ^ 2) :=
      mul_le_mul hDinv hMVE hMV0 (Real.exp_pos _).le
    have! h8 := mul_le_mul h7 h1 (by positivity) (by positivity)
    calc _ ≤ Real.exp (-kD) * (5 * E1 ^ 2) * ((16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 +
          324 * threeErrC κ 3 1 * Real.sqrt cT) * (E1 * (B ^ 6 * G))) := h8
      _ = _ := by ring
  have! hA3 : K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε * U ^ 3 * S.Dstar ^ 4) * MV +
      4 * (K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 *
        (S.Dstar ^ 3 * (Iw + 1)))) * MV ≤ ce2 * Real.exp (-(k : ℝ)) := by
    have! e1 : K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε * U ^ 3 * S.Dstar ^ 4) * MV =
        K1c * (2 * fourKC κ 3 * 12 ^ 4) * (ε * U ^ 3 * S.Dstar ^ 4 * MV) := by ring
    have! e2 : 4 * (K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 *
        (S.Dstar ^ 3 * (Iw + 1)))) * MV = 4 * (K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) *
          12 ^ 3)) * (ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)) * MV) := by ring
    rw [e1, e2, hce2]
    have! h1 := mul_le_mul_of_nonneg_left hε4 (show 0 ≤ K1c * (2 * fourKC κ 3 * 12 ^ 4) by
      positivity)
    have! h2 := mul_le_mul_of_nonneg_left hε3 (show 0 ≤ 4 * (K1c * (8 * entryCU κ 3 1 *
      2 ^ (1 + 4) * 12 ^ 3)) by positivity)
    nlinarith only [h1, h2]
  have! e : Qe * MV = (16 * fourErrC κ 3 * ι * MV + 4 * (81 * threeErrC κ 3 1 * ι * U) * MV) +
      (K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε * U ^ 3 * S.Dstar ^ 4) * MV +
      4 * (K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 *
        (S.Dstar ^ 3 * (Iw + 1)))) * MV) := by rw [hQe]; ring
  rw [e]
  linarith only [hA1, hA2, hA3]

/-- Step `hcMcn` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hcMcn :
    ∀ (κ : LocalKernelClass) (cL : ℝ) (cK : ℝ) (cMc : ℝ),
      cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) →
    0 ≤ cMc := by
  intro κ cL cK cMc hcMc
  rw [hcMc]
  have! h1 := C4c_nonneg κ
  have! h2 := C3c_nonneg κ
  exact mul_nonneg (mul_nonneg (by linarith only [h1, h2]) (by positivity)) (by positivity)

/-- Step `hCjg1` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hCjg1 :
    ∀ (k : ℕ) (cc : ℕ) (famFuel : ℕ),
    let Cjg : ℝ := ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    Cjg = ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) +
        (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))) →
    1 ≤ Cjg := by
  intro k cc famFuel Cjg hCjg
  rw [hCjg]
  have! h0 := Nat.cast_nonneg (α := ℝ) (2 * famFuel + 2)
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith only [h0]))
    (Real.one_le_exp (by positivity))

/-- Step `hOsk` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hOsk :
    ∀ (k : ℕ) (cc : ℕ) (famFuel : ℕ) (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ)),
      Os = ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs ((2 : ℕ) ^ famFuel) ((2 : ℕ) *
        famFuel + (2 : ℕ)) → (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (↑k : ℝ) →
      (2 : ℝ) ^ famFuel ≤ (3 : ℝ) ^ cc * (↑k : ℝ) ^ cc →
    (Os.card : ℝ) ≤ 80 * 9 ^ cc * cc * (k : ℝ) ^ (2 * cc + 1) := by
  intro k cc famFuel Os hOs hJmk hLpk
  have! e : (Os.card : ℝ) = 80 * ((2 : ℝ) ^ famFuel) ^ 2 * ((2 * famFuel + 2 : ℕ) : ℝ) := by
    rw [hOs]
    unfold ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs
    simp only [Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_range]
    push_cast; ring
  rw [e]
  have! h1 : ((2 : ℝ) ^ famFuel) ^ 2 ≤ (3 ^ cc * (k : ℝ) ^ cc) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hLpk 2
  have! h2 : (3 ^ cc * (k : ℝ) ^ cc) ^ 2 * (cc * k) = 9 ^ cc * cc * (k : ℝ) ^ (2 * cc + 1) := by
    rw [show (9 : ℝ) ^ cc = (3 ^ cc) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    ring
  have! h3 := mul_le_mul h1 hJmk (Nat.cast_nonneg _) (by positivity)
  nlinarith only [h3, h2]

/-- Step `hhull` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hhull :
    ∀ (k : ℕ) (cc : ℕ), (2 : ℝ) ≤ (↑k : ℝ) → ∀ (ρ : ℝ), (0 : ℝ) < ρ → ρ⁻¹ ≤ (↑k : ℝ) ^ cc →
    hullCutConstant (ρ / 64 / 2) ≤ 65536 * (k : ℝ) ^ (2 * cc) := by
  intro k cc hk2 ρ hρ hρk
  unfold hullCutConstant
  have! hy : 2 / (ρ / 64 / 2) = 256 * ρ⁻¹ := by field_simp; ring
  rw [hy]
  have! hy0 : 0 < 256 * ρ⁻¹ := by positivity
  have! h1 : 1 + Real.log (256 * ρ⁻¹) ≤ 256 * ρ⁻¹ := by
    have! this := Real.log_le_sub_one_of_pos hy0; linarith only [this]
  have! h2 : 256 * ρ⁻¹ ≤ 256 * (k : ℝ) ^ cc := by linarith only [hρk]
  calc 256 * ρ⁻¹ * (1 + Real.log (256 * ρ⁻¹)) ≤ 256 * ρ⁻¹ * (256 * ρ⁻¹) :=
        mul_le_mul_of_nonneg_left h1 hy0.le
    _ ≤ (256 * (k : ℝ) ^ cc) * (256 * (k : ℝ) ^ cc) :=
        mul_le_mul h2 h2 hy0.le (by positivity)
    _ = 65536 * (k : ℝ) ^ (2 * cc) := by ring

/-- Step `hlogY` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hlogY :
    ∀ (k : ℕ) (cc : ℕ) (Mp : ℕ) (V : ℕ) (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ))
      (E1 : ℝ), E1 = Real.exp ((↑k : ℝ) ^ cc) → (1 : ℝ) ≤ E1 → (↑Mp : ℝ) ≤ E1 →
      (↑V : ℝ) ≤ (5 : ℝ) * E1 → (↑k : ℝ) ^ cc ≤ (↑k : ℝ) ^ ((2 : ℕ) * cc + (1 : ℕ)) →
      (1 : ℝ) ≤ (↑k : ℝ) ^ ((2 : ℕ) * cc + (1 : ℕ)) →
      (↑Os.card : ℝ) ≤ (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ) * (↑k : ℝ) ^ ((2 : ℕ) * cc + (1 : ℕ)) →
      (0 : ℝ) ≤ (↑Os.card : ℝ) →
    let Yn : ℝ := (↑Os.card : ℝ) * (↑Mp : ℝ) * (↑V : ℝ);
    Yn = (↑Os.card : ℝ) * (↑Mp : ℝ) * (↑V : ℝ) → (0 : ℝ) ≤ Yn →
    1 + Real.log (2 + Yn) ≤ (8 + 80 * 9 ^ cc * cc) * (k : ℝ) ^ (2 * cc + 1) := by
  intro k cc Mp V Os E1 hE1 hE11 hMpE hVE1 hkcc' hk2cc hOsk hOs0' Yn hYn hYn0
  have! h1 : 2 + Yn ≤ (2 + Os.card) * ((1 + Mp) * (1 + V)) := by
    rw [hYn]
    have! this : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
    have! this : (0 : ℝ) ≤ V := Nat.cast_nonneg _
    nlinarith only [hOs0', this, ‹(0 : ℝ) ≤ Mp›, mul_nonneg hOs0' ‹(0 : ℝ) ≤ Mp›,
      mul_nonneg ‹(0 : ℝ) ≤ Mp› this, mul_nonneg hOs0' this,
      mul_nonneg (mul_nonneg hOs0' ‹(0 : ℝ) ≤ Mp›) this]
  have! h2 := Real.log_le_log (by linarith only [hYn0]) h1
  rw [Real.log_mul (ne_of_gt (by linarith only [hOs0'])) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h2
  have! h3 : Real.log (2 + Os.card) ≤ 1 + Os.card := by
    have! this := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + Os.card by
      linarith only [hOs0'])
    linarith only [this]
  have! hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have! h4 : Real.log (1 + Mp) ≤ 1 + (k : ℝ) ^ cc := by
    have! h5 : 1 + (Mp : ℝ) ≤ 2 * E1 := by linarith only [hMpE, hE11]
    have! h6 := Real.log_le_log (by positivity) h5
    rw [Real.log_mul (by norm_num) (by linarith only [hE11]), hE1, Real.log_exp] at h6
    linarith only [h6, hl2]
  have! h7 : Real.log (1 + V) ≤ 2 + (k : ℝ) ^ cc := by
    have! h5 : 1 + (V : ℝ) ≤ 6 * E1 := by linarith only [hVE1, hE11]
    have! h6 := Real.log_le_log (by positivity) h5
    rw [Real.log_mul (by norm_num) (by linarith only [hE11]), hE1, Real.log_exp] at h6
    have! hl6 : Real.log 6 ≤ 2 := by
      have! h8 : Real.log 6 < 2 := by
        rw [Real.log_lt_iff_lt_exp (by norm_num)]
        have! h9 : (2.7 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 :=
          pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 2
        rw [← Real.exp_nat_mul] at h9; norm_num at h9; linarith only [h9]
      exact h8.le
    linarith only [h6, hl6]
  have! h8 : (5 : ℝ) + 2 * (k : ℝ) ^ cc ≤ 7 * (k : ℝ) ^ (2 * cc + 1) := by
    linarith only [hkcc', hk2cc]
  have! h9 := mul_le_mul_of_nonneg_left hk2cc (show (0 : ℝ) ≤ 80 * 9 ^ cc * cc by positivity)
  linarith only [h2, h3, h4, h7, h8, hOsk, hk2cc]

/-- Step `hCjgk` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hCjgk :
    ∀ (g : ℕ) (k : ℕ) (cc : ℕ) (famFuel : ℕ), (1 : ℝ) ≤ (↑k : ℝ) →
      (↑g : ℝ) = (8192 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (8 : ℝ) → ∀ (X : ℝ),
      X = ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ) → ∀ (G : ℝ),
      (∀ c ≤ (↑g : ℝ), Real.exp (c * X) ≤ G) →
    let Cjg : ℝ := ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    Cjg = ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) +
        (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))) →
      (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (↑k : ℝ) → (1 : ℝ) ≤ (↑cc : ℝ) →
    Cjg ≤ 4 * cc ^ 2 * (k : ℝ) ^ 2 * G := by
  intro g k cc famFuel hk1 hgr X hX G hexpG Cjg hCjg hJmk hcc1
  rw [hCjg]
  have! h1 : ((2 * famFuel + 2 : ℕ) : ℝ) + 1 ≤ 2 * cc * k := by
    have! this : (1 : ℝ) ≤ cc * k := one_le_mul_of_one_le_of_one_le hcc1 hk1
    linarith only [hJmk, this]
  have! h2 : (((2 * famFuel + 2 : ℕ) : ℝ) + 1) ^ 2 ≤ (2 * cc * k) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have! h3 : Real.exp (2 * (1024 * (cc + 1) * (1024 * (cc + 1) + cc + 7) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2)) ≤ G := by
    rw [show 2 * (1024 * ((cc : ℝ) + 1) * (1024 * (cc + 1) + cc + 7) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) = (2 * (1024 * ((cc : ℝ) + 1) *
          (1024 * (cc + 1) + cc + 7))) * X by rw [hX]; ring]
    refine hexpG _ ?_
    rw [hgr]
    nlinarith only [sq_nonneg (cc : ℝ), Nat.cast_nonneg (α := ℝ) cc]
  calc (((2 * famFuel + 2 : ℕ) : ℝ) + 1) ^ 2 * Real.exp (2 * (1024 * (cc + 1) *
        (1024 * (cc + 1) + cc + 7) * (1 + Real.log (2 * (k : ℝ))) ^ 2))
      ≤ (2 * cc * k) ^ 2 * G := mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity)
    _ = 4 * cc ^ 2 * (k : ℝ) ^ 2 * G := by ring

/-- Step `hWk` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hWk :
    ∀ (k : ℕ) (cc : ℕ) (Nl : ℝ) (dB : ℕ), (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc → ∀ (E : ℝ), E ≤ (↑k : ℝ) ^ cc →
      ∀ (S : ModeSchedule), S.dmax = (2 : ℕ) * dB + (2 : ℕ) → S.Dm = max (2 : ℝ) Nl → ∀ (Vl0 : ℝ),
      (1 : ℝ) ≤ (↑k : ℝ) → ∀ (G : ℝ), (1 : ℝ) ≤ G → (1 : ℝ) ≤ (↑k : ℝ) ^ cc → (1 : ℝ) ≤ S.Dstar →
      Real.log (max (2 : ℝ) Nl) ≤ (↑k : ℝ) ^ cc → (2 : ℝ) ≤ S.Dm →
    let Gq : ℝ := Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^
        (2 : ℕ));
    Gq ≤ G →
      Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
        1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Gq + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) →
      Gq = Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) →
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    G0e ≤ G →
    let W : ℝ := G0e + Vl0 + E + (1 : ℝ);
    W = G0e + Vl0 + E + (1 : ℝ) →
    W ≤ 170000000 * (k : ℝ) ^ (2 * cc) * G := by
  intro k cc Nl dB hdBk E hEk S hSd hSDm Vl0 hk1 G hG1 hkcc1 hD1 hmaxNl hDm2 Gq hGqG hVl0 hGq G0e
    hG0G W hWdef
  let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ)
  let n : ℝ := (↑Nb : ℝ)
  have! hd' : (S.dmax : ℝ) ≤ 4 * (k : ℝ) ^ cc := by
    rw [hSd]; push_cast
    have hdBk' : (dB : ℝ) ≤ (k : ℝ) ^ cc := hdBk
    linarith only [hdBk', hkcc1]
  have! hlDm : Real.log (2 * S.Dm) ≤ 2 * (k : ℝ) ^ cc := by
    rw [hSDm, Real.log_mul (by norm_num) (by positivity)]
    have! hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hl2, hmaxNl, hkcc1]
  have! hlDm0 : 0 ≤ Real.log (2 * S.Dm) := Real.log_nonneg (by linarith only [hDm2])
  have! hk2c : (k : ℝ) ^ (2 * cc) = (k : ℝ) ^ cc * (k : ℝ) ^ cc := by ring
  have! hVk : Vl0 ≤ 106168392 * (k : ℝ) ^ (2 * cc) * G := by
    rw [hVl0]
    have! hfl : ((⌊180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤
        1474561 * (k : ℝ) ^ (2 * cc) := by
      have! h1 := Nat.floor_le (show (0 : ℝ) ≤ 180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024)
        by positivity)
      have! h2 : (S.dmax : ℝ) * Real.log (2 * S.Dm) ≤ 4 * (k : ℝ) ^ cc * (2 * (k : ℝ) ^ cc) :=
        mul_le_mul hd' hlDm hlDm0 (by positivity)
      rw [div_div_eq_mul_div, div_one] at h1 ⊢
      have! h3 : (1 : ℝ) ≤ (k : ℝ) ^ (2 * cc) := one_le_pow₀ hk1
      rw [hk2c] at h3 ⊢
      linarith only [h1, h2, h3]
    have! hGq' : Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394 ≤ 3 * G := by
      have! h1 : 2 * 1 / S.Dstar ^ 394 ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have! this := one_le_pow₀ (n := 394) hD1
        linarith only [this]
      have! h2 : Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
          (1 + Real.log (2 * (k : ℝ))) ^ 2) ≤ G := by rw [← hGq]; exact hGqG
      linarith only [h1, h2, hG1]
    have! h0 : (0 : ℝ) ≤ Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394 := by positivity
    calc 24 * (((⌊180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℕ) : ℝ) + 1) *
          (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
            (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394)
        ≤ 24 * (1474561 * (k : ℝ) ^ (2 * cc)) * (3 * G) := by gcongr
      _ = 106168392 * (k : ℝ) ^ (2 * cc) * G := by ring
  have! h1 : (1 : ℝ) ≤ (k : ℝ) ^ (2 * cc) := one_le_pow₀ hk1
  have! h2 : (k : ℝ) ^ cc ≤ (k : ℝ) ^ (2 * cc) := pow_le_pow_right₀ hk1 (by omega)
  have! hkG : (k : ℝ) ^ (2 * cc) ≤ (k : ℝ) ^ (2 * cc) * G :=
    le_mul_of_one_le_right (by positivity) hG1
  have! hG' : G ≤ (k : ℝ) ^ (2 * cc) * G := le_mul_of_one_le_left (by linarith only [hG1]) h1
  rw [hWdef]
  linarith only [hG0G, hVk, hEk, h1, h2, hkG, hG']

/-- Step `hQk` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hQk :
    ∀ (g : ℕ) (cQ : ℝ) (k : ℕ) (cc : ℕ), (1 : ℕ) ≤ cc → (2 : ℝ) ≤ (↑k : ℝ) → ∀ (Mp : ℕ) (V : ℕ)
      (famFuel : ℕ) (E : ℝ) (ρ : ℝ), (0 : ℝ) < ρ → ρ < (1 : ℝ) → ∀ (Vl0 : ℝ)
      (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ)),
      cQ = (65536 : ℝ) * ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^
        cc * (↑cc : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) →
      (1 : ℝ) ≤ (↑k : ℝ) → ∀ (X : ℝ), X = ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ) →
      ∀ (G : ℝ), G = Real.exp ((↑g : ℝ) * X) → (1 : ℝ) ≤ G →
    let Cjg : ℝ := ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    (1 : ℝ) ≤ Cjg →
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    let W : ℝ := G0e + Vl0 + E + (1 : ℝ);
    (1 : ℝ) ≤ W →
      (↑Os.card : ℝ) ≤ (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ) * (↑k : ℝ) ^ ((2 : ℕ) * cc + (1 : ℕ)) →
      hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) ≤ (65536 : ℝ) * (↑k : ℝ) ^ ((2 : ℕ) * cc) →
    let Yn : ℝ := (↑Os.card : ℝ) * (↑Mp : ℝ) * (↑V : ℝ);
    (0 : ℝ) ≤ Yn →
      (1 : ℝ) + Real.log ((2 : ℝ) + Yn) ≤ ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) *
        (↑k : ℝ) ^ ((2 : ℕ) * cc + (1 : ℕ)) →
      Cjg ≤ (4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ) * (↑k : ℝ) ^ (2 : ℕ) * G →
      W ≤ (170000000 : ℝ) * (↑k : ℝ) ^ ((2 : ℕ) * cc) * G →
    let Qk : ℝ := hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
        (↑Os.card : ℝ) * Cjg * W;
    Qk = hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
        (↑Os.card : ℝ) * Cjg * W → (0 : ℝ) ≤ cQ →
    Qk ≤ cQ * Real.exp X ^ (8 * cc + 4 + 2 * g) := by
  intro g cQ k cc hcc hk2 Mp V famFuel E ρ hρ hρ1 Vl0 Os hcQ hk1 X hX G hGdef hG1 Cjg hCjg1 G0e W
    hW1 hOsk hhull Yn hYn0 hlogY hCjgk hWk Qk hQkdef hcQ0
  have! hkX : (k : ℝ) ≤ Real.exp X := by rw [hX]; exact le_exp_one_add_log_sq hk1
  have! hGX : G = Real.exp X ^ g := by rw [hGdef, ← Real.exp_nat_mul]
  have! hlY0 : 0 ≤ 1 + Real.log (2 + Yn) := by
    have! this := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Yn by linarith only [hYn0])
    linarith only [this]
  have! hh0 : 0 ≤ hullCutConstant (ρ / 64 / 2) :=
    (hullCutConstant_pos (by positivity) (by linarith only [hρ1, hρ])).le
  have! hCjg0 : 0 ≤ Cjg := by linarith only [hCjg1]
  have! hW0 : 0 ≤ W := by linarith only [hW1]
  have! h1 : Qk ≤ (65536 * (k : ℝ) ^ (2 * cc)) *
      ((8 + 80 * 9 ^ cc * cc) * (k : ℝ) ^ (2 * cc + 1)) *
      (80 * 9 ^ cc * cc * (k : ℝ) ^ (2 * cc + 1)) * (4 * cc ^ 2 * (k : ℝ) ^ 2 * G) *
        (170000000 * (k : ℝ) ^ (2 * cc) * G) := by
    rw [hQkdef]
    have! a1 := mul_le_mul hhull hlogY hlY0 (by positivity)
    have! a2 := mul_le_mul a1 hOsk (Nat.cast_nonneg _) (by positivity)
    have! a3 := mul_le_mul a2 hCjgk hCjg0 (by positivity)
    exact mul_le_mul a3 hWk hW0 (by positivity)
  have! h2 : (65536 * (k : ℝ) ^ (2 * cc)) * ((8 + 80 * 9 ^ cc * cc) * (k : ℝ) ^ (2 * cc + 1)) *
      (80 * 9 ^ cc * cc * (k : ℝ) ^ (2 * cc + 1)) * (4 * cc ^ 2 * (k : ℝ) ^ 2 * G) *
        (170000000 * (k : ℝ) ^ (2 * cc) * G) = cQ * ((k : ℝ) ^ (8 * cc + 4) * G ^ 2) := by
    rw [hcQ]; ring
  have! h3 : (k : ℝ) ^ (8 * cc + 4) * G ^ 2 ≤ Real.exp X ^ (8 * cc + 4 + 2 * g) := by
    have! h4 : (k : ℝ) ^ (8 * cc + 4) ≤ Real.exp X ^ (8 * cc + 4) :=
      pow_le_pow_left₀ (by positivity) hkX _
    have! h5 : G ^ 2 = Real.exp X ^ (2 * g) := by rw [hGX, ← pow_mul, mul_comm]
    rw [h5, pow_add (Real.exp X) (8 * cc + 4) (2 * g)]
    exact mul_le_mul_of_nonneg_right h4 (by positivity)
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h3 hcQ0)

/-- Step `hcore` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hcore :
    ∀ (k : ℕ) (cc : ℕ) (Mp : ℕ) (V : ℕ) (famFuel : ℕ) (E : ℝ) (ρ : ℝ) (S : ModeSchedule) (Vl0 : ℝ)
      (Γ : ℝ) (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ)),
    let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ);
    let n : ℝ := (↑Nb : ℝ);
    let Cjg : ℝ := ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    (1 : ℝ) ≤ Cjg →
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    let W : ℝ := G0e + Vl0 + E + (1 : ℝ);
    Γ ≤ (2000 : ℝ) * (↑Os.card : ℝ) * (n ^ (3 : ℕ) * Cjg) * W → (1 : ℝ) ≤ W →
    let Yn : ℝ := (↑Os.card : ℝ) * (↑Mp : ℝ) * (↑V : ℝ);
    let Qk : ℝ := hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
        (↑Os.card : ℝ) * Cjg * W;
    Qk = hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
        (↑Os.card : ℝ) * Cjg * W →
      ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * (↑(Nb + (1 : ℕ)) : ℝ) * ((1 : ℝ) + Real.log
        ((2 : ℝ) + (↑(Nb + (1 : ℕ)) : ℝ) * (↑(Nb + (1 : ℕ)) : ℝ) * Yn)) * (↑Nb : ℝ) ^ (3 : ℕ) ≤
        (80 : ℝ) * ((2 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) ^ (6 : ℕ) * ((1 : ℝ) + Real.log
        ((2 : ℝ) + Yn)) → (0 : ℝ) ≤ hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) →
      (0 : ℝ) ≤ (1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ)) → (0 : ℝ) ≤ (↑(Nb + (1 : ℕ)) : ℝ) →
      (0 : ℝ) ≤ (1 : ℝ) + Real.log ((2 : ℝ) + (↑(Nb + (1 : ℕ)) : ℝ) * (↑(Nb + (1 : ℕ)) : ℝ) * Yn) →
    (1 + Real.log ((S.K : ℝ) + 2)) * ((Nb + 1 : ℕ) : ℝ) *
    (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) * Γ *
    hullCutConstant (ρ / 64 / 2) ≤ 160000 * (2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk := by
  intro k cc Mp V famFuel E ρ S Vl0 Γ Os Nb n Cjg hCjg1 G0e W hΓle hW1 Yn Qk hQkdef hlam hh0 hL10
    hN10 hLY0
  have! hCjg0 : 0 ≤ Cjg := by linarith only [hCjg1]
  have! hW0 : 0 ≤ W := by linarith only [hW1]
  have h1 : Γ ≤ 2000 * Os.card * (n ^ 3 * Cjg) * W := hΓle
  have! hA0 : 0 ≤ (1 + Real.log ((S.K : ℝ) + 2)) * ((Nb + 1 : ℕ) : ℝ) *
      (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) :=
    mul_nonneg (mul_nonneg hL10 hN10) hLY0
  have! h2 := mul_le_mul_of_nonneg_left h1 hA0
  have! h3 : (1 + Real.log ((S.K : ℝ) + 2)) * ((Nb + 1 : ℕ) : ℝ) *
      (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) *
        (2000 * Os.card * (n ^ 3 * Cjg) * W) = 2000 * ((1 + Real.log ((S.K : ℝ) + 2)) *
          ((Nb + 1 : ℕ) : ℝ) * (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) *
            n ^ 3) * (Os.card * Cjg * W) := by ring
  have! h4 := mul_le_mul_of_nonneg_right hlam (show 0 ≤ Os.card * Cjg * W from
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCjg0) hW0)
  have! h5 : (2000 * ((1 + Real.log ((S.K : ℝ) + 2)) * ((Nb + 1 : ℕ) : ℝ) *
      (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) * n ^ 3) *
        (Os.card * Cjg * W)) * hullCutConstant (ρ / 64 / 2) ≤
      (2000 * (80 * (2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * (1 + Real.log (2 + Yn))) *
        (Os.card * Cjg * W)) * hullCutConstant (ρ / 64 / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlam (by norm_num))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCjg0) hW0)) hh0
  have! h6 : (2000 * (80 * (2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * (1 + Real.log (2 + Yn))) *
      (Os.card * Cjg * W)) * hullCutConstant (ρ / 64 / 2) =
      160000 * (2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk := by rw [hQkdef]; ring
  have! h7 := mul_le_mul_of_nonneg_right h2 hh0
  rw [h3] at h7
  linarith only [h7, h5, h6]

/-- Step `hNEAR` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hNEAR :
    ∀ (κ : LocalKernelClass) (q : ℝ) (hq2 : (2 : ℝ) < q) (hq3 : q < (3 : ℝ)) (Nd : ℕ) (Msch : ℝ)
      (g : ℕ) (cm : ℝ) (ce : ℝ) (ce2 : ℝ) (cQ : ℝ) (CΛ : ℕ) (Cb : ℕ) (Cl : ℕ) (k : ℕ) (cc : ℕ),
      (1 : ℕ) ≤ cc → ∀ (P : ℕ) (Mp : ℕ) (V : ℕ) (famFuel : ℕ) (E : ℝ) (ρ : ℝ) (R : ℝ)
      (S : ModeSchedule) (Vl0 : ℝ) (nearS : ℝ) (Γ : ℝ)
      (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ)), (0 : ℝ) ≤ R → (20 : ℕ) ≤ Cb →
      (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb →
      ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
        (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl → ∀ (u : ℝ),
      (1 : ℝ) ≤ u → ∀ (X : ℝ), (0 : ℝ) ≤ X → (0 : ℝ) ≤ cm → (0 : ℝ) ≤ ce → (0 : ℝ) ≤ ce2 →
    let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ);
    let Cjg : ℝ := ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    (1 : ℝ) ≤ Cjg →
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    let W : ℝ := G0e + Vl0 + E + (1 : ℝ);
    (1 : ℝ) ≤ W →
    let Yn : ℝ := (↑Os.card : ℝ) * (↑Mp : ℝ) * (↑V : ℝ);
    (0 : ℝ) ≤ Yn →
    let Qk : ℝ := hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
        (↑Os.card : ℝ) * Cjg * W;
    Qk = hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
        (↑Os.card : ℝ) * Cjg * W → (0 : ℝ) ≤ cQ →
      Qk ≤ cQ * Real.exp X ^ ((8 : ℕ) * cc + (4 : ℕ) + (2 : ℕ) * g) →
    let eq' : ℝ := (2 : ℝ) * (q - (2 : ℝ)) / (q - (1 : ℝ));
    nearS ≤ (64 : ℝ) * ((4 : ℝ) * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * ((1 : ℝ) +
        finiteDepthConstant κ q Nd) * ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * ((↑S.K : ℝ) +
        (2 : ℝ)) ^ eq' * ((64 : ℝ) * ((2 : ℝ) * ((2 : ℝ) * √(1 : ℝ))) * ((2 : ℝ) * ((2 : ℝ) *
        √(1 : ℝ))))) * (hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * (↑(Nb + (1 : ℕ)) : ℝ) *
        ((1 : ℝ) + Real.log ((2 : ℝ) + (↑(Nb + (1 : ℕ)) : ℝ) * (↑(Nb + (1 : ℕ)) : ℝ) * Yn))) * Γ /
        √(↑P : ℝ) * R) →
    let Kb : ℝ := (↑Cl : ℝ) * u ^ Cl;
    ((↑S.K : ℝ) + (2 : ℝ)) ^ eq' ≤ (Kb + (2 : ℝ)) ^ eq' →
      ((2 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) ^ (6 : ℕ) ≤ ((2 : ℝ) + Real.log (Kb +
        (2 : ℝ))) ^ (6 : ℕ) → (0 : ℝ) ≤ ((↑S.K : ℝ) + (2 : ℝ)) ^ eq' →
      (0 : ℝ) ≤ (1 : ℝ) + finiteDepthConstant κ q Nd → (0 : ℝ) ≤ nbCM κ hq2 hq3 + nbCUM κ hq2 hq3 →
      (0 : ℝ) ≤ √(↑P : ℝ) → (0 : ℝ) ≤ hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) →
      ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * (↑(Nb + (1 : ℕ)) : ℝ) * ((1 : ℝ) + Real.log
        ((2 : ℝ) + (↑(Nb + (1 : ℕ)) : ℝ) * (↑(Nb + (1 : ℕ)) : ℝ) * Yn)) * Γ * hullCutConstant (ρ /
        (64 : ℝ) / (2 : ℝ)) ≤ (160000 : ℝ) * ((2 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) ^
        (6 : ℕ) * Qk →
    6 * nearS ≤
    (Cl : ℝ) * (1 + finiteDepthConstant κ q Nd) * (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
    (Kb + 2) ^ eq' * (2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl / Real.sqrt P *
    R := by
  intro κ q hq2 hq3 Nd Msch g cm ce ce2 cQ CΛ Cb Cl k cc hcc P Mp V famFuel E ρ R S Vl0 nearS Γ Os
    hR0 hCb20n hMCb2 hClb u hu1 X hX0 hcmn hcen hce2n Nb Cjg hCjg1 G0e W hW1 Yn hYn0 Qk hQkdef
    hcQ0 hQk eq' hnearS Kb hKp hlamb hKp0 hCN0 hnbc hP0 hh0 hcore
  set! ZT := 4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
        (1 + Real.log ((S.K : ℝ) + 2)) * ((S.K : ℝ) + 2) ^ eq' *
        (64 * (2 * (2 * Real.sqrt 1)) * (2 * (2 * Real.sqrt 1)))) *
      (hullCutConstant (ρ / 64 / 2) * (Nb + 1 : ℕ) * (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) *
        ((Nb + 1 : ℕ) : ℝ) * Yn))) * Γ / Real.sqrt P * R with hZT
  rewrite [← hZT] at hnearS
  have! hZ : ZT ≤ 655360000 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
      (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq') *
        ((2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk) / Real.sqrt P *
          R := by
    have! e1 : ZT = 4096 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq') *
          ((1 + Real.log ((S.K : ℝ) + 2)) * ((Nb + 1 : ℕ) : ℝ) *
            (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) * Γ *
              hullCutConstant (ρ / 64 / 2)) / Real.sqrt P * R := by
      rw [hZT, Real.sqrt_one]; ring
    rw [e1]
    have! hc0 : 0 ≤ 4096 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq') :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hnbc hCN0) hKp0)
    have! h1 := mul_le_mul_of_nonneg_left hcore hc0
    have! h2 := div_le_div_of_nonneg_right h1 hP0
    have! h3 := mul_le_mul_of_nonneg_right h2 hR0
    refine h3.trans (le_of_eq ?_)
    ring
  have! hQkC : 655360000 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
      (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq') *
        ((2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk) ≤
      655360000 * cQ * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq') *
          ((2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl) := by
    have! hX1 : 1 ≤ Real.exp X := Real.one_le_exp hX0
    have! hXC : Real.exp X ^ (8 * cc + 4 + 2 * g) ≤ Real.exp X ^ Cl :=
      pow_le_pow_right₀ hX1 (by omega)
    have! hQk' : Qk ≤ cQ * Real.exp X ^ Cl :=
      hQk.trans (mul_le_mul_of_nonneg_left hXC hcQ0)
    have! hQk0 : 0 ≤ Qk := by
      rw [hQkdef]
      have! this : 0 ≤ 1 + Real.log (2 + Yn) := by
        have! this := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Yn by linarith only [hYn0])
        linarith only [this]
      have! hCjg0 : 0 ≤ Cjg := by linarith only [hCjg1]
      have! hW0 : 0 ≤ W := by linarith only [hW1]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hh0 this) (Nat.cast_nonneg _)) hCjg0)
        hW0
    have! h1 : ((2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk) ≤
        (2 + Real.log (Kb + 2)) ^ 6 * (cQ * Real.exp X ^ Cl) :=
      mul_le_mul hlamb hQk' hQk0 (by positivity)
    have! h2 : (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
        ((S.K : ℝ) + 2) ^ eq' ≤ (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
          (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq' :=
      mul_le_mul_of_nonneg_left hKp (mul_nonneg hnbc hCN0)
    have! h3 := mul_le_mul h2 h1 (mul_nonneg (by positivity) hQk0)
      (mul_nonneg (mul_nonneg hnbc hCN0) (by positivity))
    calc _ = 655360000 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
          (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq' *
            ((2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk)) := mul_assoc _ _ _
      _ ≤ 655360000 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
          (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq' *
            ((2 + Real.log (Kb + 2)) ^ 6 * (cQ * Real.exp X ^ Cl))) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = _ := by ac_rfl
  have! hCl3 : 384 * 655360000 * cQ ≤ Cl := by
    have! h1 : cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ ≤
        ((⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have! h2 : (((⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ : ℕ) : ℝ)) ≤ Cl := by
      exact_mod_cast (show ⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ ≤ Cl by
        omega)
    have! hcm0 : 0 ≤ cm * Cb ^ 59 := mul_nonneg hcmn (by positivity)
    have! hce0 : 0 ≤ ce * Cb ^ 18 := mul_nonneg hcen (by positivity)
    have hce20 : 0 ≤ ce2 := hce2n
    linarith only [h1, h2, hcm0, hce0, hce20, hcQ0]
  have! hfin : 6 * (64 * ZT) ≤ 384 * (655360000 * cQ * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
      (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq') *
        ((2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl)) / Real.sqrt P *
          R := by
    have! h1 := div_le_div_of_nonneg_right hQkC hP0
    have! h2 := mul_le_mul_of_nonneg_right h1 hR0
    have! h3 : 6 * (64 * ZT) ≤ 384 * (655360000 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq') *
          ((2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk) / Real.sqrt P *
            R) := by linarith only [hZ]
    refine h3.trans ?_
    have! this : 384 * (655360000 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (1 + finiteDepthConstant κ q Nd) * ((S.K : ℝ) + 2) ^ eq') *
          ((2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk) / Real.sqrt P *
            R) ≤ 384 * (655360000 * cQ * ((nbCM κ hq2 hq3 +
              nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq') *
                ((2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl) / Real.sqrt P *
                  R) := by linarith only [h2]
    refine this.trans (le_of_eq ?_)
    ring
  have! hfin2 : 384 * (655360000 * cQ * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
      (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq') *
        ((2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl)) / Real.sqrt P *
          R ≤
      (Cl : ℝ) * (1 + finiteDepthConstant κ q Nd) * (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (Kb + 2) ^ eq' * (2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl / Real.sqrt P *
        R := by
    have! hrest : 0 ≤ ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
        (Kb + 2) ^ eq' * ((2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl)) / Real.sqrt P *
          R :=
      mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hnbc hCN0) (by positivity))
        (by positivity)) (Real.sqrt_nonneg _)) hR0
    have! h1 := mul_le_mul_of_nonneg_right hCl3 hrest
    calc _ = 384 * 655360000 * cQ * (((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
          (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq' * ((2 + Real.log (Kb + 2)) ^ 6 *
            Real.exp X ^ Cl)) / Real.sqrt P * R) := by ring
      _ ≤ (Cl : ℝ) * (((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
          (1 + finiteDepthConstant κ q Nd) * (Kb + 2) ^ eq' * ((2 + Real.log (Kb + 2)) ^ 6 *
            Real.exp X ^ Cl)) / Real.sqrt P * R) := h1
      _ = _ := by ring
  linarith only [hnearS, hfin, hfin2]

/-- Step `hceil` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hceil :
    ∀ (Msch : ℝ) (g : ℕ) (cm : ℝ) (ce : ℝ) (ce2 : ℝ) (cQ : ℝ) (CΛ : ℕ) (Cb : ℕ) (Cl : ℕ) (cc : ℕ),
      (1 : ℕ) ≤ cc → (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb →
      ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
        (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl →
    cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ ≤ Cl := by
  intro Msch g cm ce ce2 cQ CΛ Cb Cl cc hcc hMCb2 hClb
  have! h2 : cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ ≤
      ((⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have! h3 : (((⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ : ℕ) : ℝ)) ≤ Cl := by
    exact_mod_cast (show ⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ ≤ Cl by
      omega)
  linarith only [h2, h3]

/-- Step `hCm` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hCm :
    ∀ (κ : LocalKernelClass) (cT : ℝ) (cMc : ℝ) (cm : ℝ), ℕ →
      cm = (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
        ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc → ∀ (B : ℝ), (1 : ℝ) ≤ B → ∀ (G : ℝ),
      (1 : ℝ) ≤ G → (0 : ℝ) ≤ localFormUniformConstant κ → (0 : ℝ) ≤ cT → (0 : ℝ) ≤ cMc →
      (0 : ℝ) ≤ B → (0 : ℝ) ≤ G → √(cT * B ^ (11 : ℕ) * G) ≤ √cT * B ^ (6 : ℕ) * G →
      (1 : ℝ) ≤ B ^ (6 : ℕ) * G → B ^ (2 : ℕ) * G ≤ B ^ (6 : ℕ) * G →
    196608 * B ^ 3 * (cT * B ^ 11 * G) + 83 * (1 + 81 * localFormUniformConstant κ *
    (30000 * B ^ 2 * G + Real.sqrt (cT * B ^ 11 * G))) * (1 + cT * B ^ 11 * G) ^ 3 +
    cMc * B ^ 59 * G ^ 2 ≤ cm * B ^ 59 * G ^ 4 := by
  intro κ cT cMc cm t3 hcm B hBB1 G hG1 hL00 hcT0 hcMcn hBn0 hGn0 hsT' hB6G hB2G6
  have! t1 : B ^ 3 * (cT * B ^ 11 * G) ≤ cT * (B ^ 59 * G ^ 4) := by
    have! h1 : B ^ 14 * G ≤ B ^ 59 * G ^ 4 := mul_le_mul (pow_le_pow_right₀ hBB1 (by norm_num))
      (le_self_pow₀ hG1 (by norm_num)) hGn0 (pow_nonneg hBn0 _)
    calc B ^ 3 * (cT * B ^ 11 * G) = cT * (B ^ 14 * G) := by ring
      _ ≤ cT * (B ^ 59 * G ^ 4) := mul_le_mul_of_nonneg_left h1 hcT0
  have! hsc0 : 0 ≤ 81 * localFormUniformConstant κ := mul_nonneg (by norm_num) hL00
  have! t2a : 1 + 81 * localFormUniformConstant κ * (30000 * B ^ 2 * G +
      Real.sqrt (cT * B ^ 11 * G)) ≤ (1 + 81 * localFormUniformConstant κ *
        (30000 + Real.sqrt cT)) * (B ^ 6 * G) := by
    have! h1 : 30000 * B ^ 2 * G + Real.sqrt (cT * B ^ 11 * G) ≤
        (30000 + Real.sqrt cT) * (B ^ 6 * G) := by
      have! this := mul_le_mul_of_nonneg_left hB2G6 (show (0 : ℝ) ≤ 30000 by norm_num)
      have! e : (30000 + Real.sqrt cT) * (B ^ 6 * G) =
          30000 * (B ^ 6 * G) + Real.sqrt cT * B ^ 6 * G := by ring
      rw [e]
      linarith only [this, hsT']
    have! h2 := mul_le_mul_of_nonneg_left h1 hsc0
    have! h3 : 0 ≤ 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT) :=
      mul_nonneg hsc0 (by positivity)
    have! h4 := mul_le_mul_of_nonneg_left hB6G h3
    have! e : (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) * (B ^ 6 * G) =
        B ^ 6 * G + 81 * localFormUniformConstant κ * ((30000 + Real.sqrt cT) * (B ^ 6 * G)) :=
      by ring
    rw [e]
    linarith only [h2, hB6G]
  have! hB11 : 1 ≤ B ^ 11 * G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hBB1) hG1
  have! t2b : (1 + cT * B ^ 11 * G) ^ 3 ≤ ((1 + cT) * (B ^ 11 * G)) ^ 3 := by
    have! h0 : 0 ≤ 1 + cT * B ^ 11 * G := by
      have! this := mul_nonneg hcT0 (show 0 ≤ B ^ 11 * G by linarith only [hB11])
      linarith only [this]
    have! h1 : 1 + cT * B ^ 11 * G ≤ (1 + cT) * (B ^ 11 * G) := by
      have! e : (1 + cT) * (B ^ 11 * G) = B ^ 11 * G + cT * (B ^ 11 * G) := by ring
      rw [e, ← mul_assoc]
      linarith only [hB11]
    exact pow_le_pow_left₀ h0 h1 3
  have! t2 : (1 + 81 * localFormUniformConstant κ * (30000 * B ^ 2 * G +
      Real.sqrt (cT * B ^ 11 * G))) * (1 + cT * B ^ 11 * G) ^ 3 ≤
      (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) * (1 + cT) ^ 3 *
        (B ^ 59 * G ^ 4) := by
    have! h0a : 0 ≤ (1 + cT * B ^ 11 * G) ^ 3 := by
      have! this := mul_nonneg hcT0 (show 0 ≤ B ^ 11 * G by linarith only [hB11])
      exact pow_nonneg (by linarith only [this]) 3
    have! h0b : 0 ≤ (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) *
        (B ^ 6 * G) := by
      have! this : 0 ≤ 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT) :=
        mul_nonneg hsc0 (by positivity)
      exact mul_nonneg (by linarith only [this]) (by linarith only [hB6G])
    have! h1 := mul_le_mul t2a t2b h0a h0b
    have! h2 : (B ^ 6 * G) * (B ^ 11 * G) ^ 3 ≤ B ^ 59 * G ^ 4 := by
      calc B ^ 6 * G * (B ^ 11 * G) ^ 3 = B ^ 39 * G ^ 4 := by ring
        _ ≤ B ^ 59 * G ^ 4 := mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hBB1 (by norm_num)) (pow_nonneg hGn0 _)
    have! h3 : 0 ≤ (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) *
        (1 + cT) ^ 3 := by
      have! this : 0 ≤ 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT) :=
        mul_nonneg hsc0 (by positivity)
      exact mul_nonneg (by linarith only [this]) (pow_nonneg (by linarith only [hcT0]) 3)
    calc _ ≤ (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) * (B ^ 6 * G) *
          ((1 + cT) * (B ^ 11 * G)) ^ 3 := h1
      _ = (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) * (1 + cT) ^ 3 *
          ((B ^ 6 * G) * (B ^ 11 * G) ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 h3
  have! t3 : cMc * B ^ 59 * G ^ 2 ≤ cMc * (B ^ 59 * G ^ 4) := by
    have! this : B ^ 59 * G ^ 2 ≤ B ^ 59 * G ^ 4 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hG1 (by norm_num)) (pow_nonneg hBn0 _)
    calc cMc * B ^ 59 * G ^ 2 = cMc * (B ^ 59 * G ^ 2) := by ring
      _ ≤ cMc * (B ^ 59 * G ^ 4) := mul_le_mul_of_nonneg_left this hcMcn
  have! e : cm * B ^ 59 * G ^ 4 = 196608 * (cT * (B ^ 59 * G ^ 4)) +
      83 * ((1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) * (1 + cT) ^ 3 *
        (B ^ 59 * G ^ 4)) + cMc * (B ^ 59 * G ^ 4) := by rw [hcm]; ring
  rw [e]
  have! e2 : 196608 * B ^ 3 * (cT * B ^ 11 * G) = 196608 * (B ^ 3 * (cT * B ^ 11 * G)) := by
    ring
  have! e3 : 83 * (1 + 81 * localFormUniformConstant κ * (30000 * B ^ 2 * G +
      Real.sqrt (cT * B ^ 11 * G))) * (1 + cT * B ^ 11 * G) ^ 3 =
      83 * ((1 + 81 * localFormUniformConstant κ * (30000 * B ^ 2 * G +
        Real.sqrt (cT * B ^ 11 * G))) * (1 + cT * B ^ 11 * G) ^ 3) := by ring
  rw [e2, e3]
  linarith only [t1, t2, t3]

/-- Step `hClm` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hClm :
    ∀ (Msch : ℝ) (g : ℕ) (cm : ℝ) (ce : ℝ) (ce2 : ℝ) (cQ : ℝ) (CΛ : ℕ) (Cb : ℕ) (Cl : ℕ) (cc : ℕ),
      (1 : ℕ) ≤ cc → (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb →
      ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
        (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl → ∀ (u : ℝ),
      (1 : ℝ) ≤ u → ∀ (B : ℝ), B = (↑Cb : ℝ) * u ^ Cb → ∀ (X : ℝ) (G : ℝ), (0 : ℝ) ≤ ce2 →
      (0 : ℝ) ≤ cQ → (1 : ℝ) ≤ Real.exp X → G = Real.exp X ^ g → (0 : ℝ) ≤ G →
      cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
        (11 : ℕ) * cQ ≤ (↑Cl : ℝ) → (0 : ℝ) ≤ ce * (↑Cb : ℝ) ^ (18 : ℕ) →
    cm * B ^ 59 * G ^ 4 ≤ Cl * u ^ Cl * Real.exp X ^ Cl := by
  intro Msch g cm ce ce2 cQ CΛ Cb Cl cc hcc hMCb2 hClb u hu1 B hBdef X G hce2n hcQ0 hX1 hGX hGn0
    hceil hce18
  have! h1 : cm * (Cb : ℝ) ^ 59 ≤ Cl := by
    have! this : 0 ≤ 3 * 10 ^ 11 * cQ := mul_nonneg (by norm_num) hcQ0
    linarith only [hceil, hce18, hce2n, this]
  have! h2 : u ^ (59 * Cb) ≤ u ^ Cl := pow_le_pow_right₀ hu1 (by omega)
  have! h3 : G ^ 4 ≤ Real.exp X ^ Cl := by
    rw [hGX, ← pow_mul]; exact pow_le_pow_right₀ hX1 (by omega)
  have! e : cm * B ^ 59 * G ^ 4 = (cm * (Cb : ℝ) ^ 59) * u ^ (59 * Cb) * G ^ 4 := by
    rw [hBdef, mul_pow, ← pow_mul]; ring
  rw [e]
  exact mul_le_mul (mul_le_mul h1 h2 (pow_nonneg (by linarith only [hu1]) _)
    (Nat.cast_nonneg _)) h3 (pow_nonneg hGn0 _)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [hu1]) _))

/-- Step `hErr` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hErr :
    ∀ (κ : LocalKernelClass) (Msch : ℝ) (g : ℕ) (cT : ℝ) (cm : ℝ) (ce : ℝ) (ce2 : ℝ) (cQ : ℝ)
      (CΛ : ℕ) (Cb : ℕ) (Cl : ℕ) (k : ℕ) (cc : ℕ), (1 : ℕ) ≤ cc → ∀ (kD : ℝ) (Mp : ℕ) (V : ℕ)
      (δ : ℝ) (R : ℝ) (S : ModeSchedule) (Iw : ℕ) (U : ℝ) (MV : ℝ) (ε : ℝ) (cE : ℝ),
      ce = (6642 : ℝ) * localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) +
        (9 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) +
        (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) → (0 : ℝ) ≤ R →
      (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb →
      ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
        (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl → ∀ (u : ℝ),
      (1 : ℝ) ≤ u → ∀ (B : ℝ), B = (↑Cb : ℝ) * u ^ Cb → (1 : ℝ) ≤ B → ∀ (X : ℝ) (G : ℝ),
      (1 : ℝ) ≤ G → (1 : ℝ) ≤ (↑k : ℝ) ^ cc → (1 : ℝ) ≤ cT → ∀ (ι : ℝ),
    let Qe : ℝ := (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) *
        (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) *
        threeErrC κ (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) *
        (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^
        (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))));
    cE ≤ Qe * ((↑(Mp * V) : ℝ) * R) → (↑(Mp * V) : ℝ) = MV →
      Qe * MV ≤ (5 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
        (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) * Real.exp ((3 : ℝ) * (↑k : ℝ) ^
        cc) * B ^ (6 : ℕ) * G * Real.exp (-kD) + ce2 * Real.exp (-(↑k : ℝ)) →
      (0 : ℝ) ≤ localFormUniformConstant κ → (0 : ℝ) ≤ ce2 → (0 : ℝ) ≤ cQ → (1 : ℝ) ≤ Real.exp X →
      G = Real.exp X ^ g → (0 : ℝ) ≤ B → (0 : ℝ) ≤ G →
      cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
        (11 : ℕ) * cQ ≤ (↑Cl : ℝ) → (0 : ℝ) ≤ cm * (↑Cb : ℝ) ^ (59 : ℕ) →
      (0 : ℝ) ≤ ce * (↑Cb : ℝ) ^ (18 : ℕ) → √(cT * B ^ (11 : ℕ) * G) ≤ √cT * B ^ (6 : ℕ) * G →
      (1 : ℝ) ≤ B ^ (6 : ℕ) * G → B ^ (2 : ℕ) * G ≤ B ^ (6 : ℕ) * G →
    6642 * localFormUniformConstant κ * (2 * (30000 * B ^ 2 * G) +
    Real.sqrt (cT * B ^ 11 * G)) ^ 3 * (288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ * R) +
    cE ≤
    Cl * u ^ Cl * Real.exp X ^ Cl * (Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ +
    Real.exp (-kD))) * R + Cl * Real.exp (-(k : ℝ)) * R := by
  intro κ Msch g cT cm ce ce2 cQ CΛ Cb Cl k cc hcc kD Mp V δ R S Iw U MV ε cE hce hR0 hMCb2 hClb u
    hu1 B hBdef hBB1 X G hG1 hkcc1 hcT1 ι Qe hcEsum hMVc hQeMV hL00 hce2n hcQ0 hX1 hGX hBn0 hGn0
    hceil hcm59 hce18 hsT' hB6G hB2G6
  obtain ⟨e4, he4⟩ : ∃ x : ℝ, x = Real.exp (4 * (k : ℝ) ^ cc) := ⟨_, rfl⟩
  obtain ⟨e3, he3⟩ : ∃ x : ℝ, x = Real.exp (3 * (k : ℝ) ^ cc) := ⟨_, rfl⟩
  rw [← he4]
  rw [← he3] at hQeMV
  have! he40 : 0 ≤ e4 := by rw [he4]; exact (Real.exp_pos _).le
  have! he30 : 0 ≤ e3 := by rw [he3]; exact (Real.exp_pos _).le
  have! he34 : e3 ≤ e4 := by
    rw [he3, he4]; exact Real.exp_le_exp.mpr (by linarith only [hkcc1])
  have! hsd0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have! hekD : 0 ≤ Real.exp (-kD) := (Real.exp_pos _).le
  have! hek : 0 ≤ Real.exp (-(k : ℝ)) := (Real.exp_pos _).le
  have! hB18 : B ^ 6 * G ≤ B ^ 18 * G ^ 3 := mul_le_mul (pow_le_pow_right₀ hBB1 (by norm_num))
    (le_self_pow₀ hG1 (by norm_num)) hGn0 (pow_nonneg hBn0 _)
  have! hY0 : 0 ≤ B ^ 18 * G ^ 3 * e4 :=
    mul_nonneg (mul_nonneg (pow_nonneg hBn0 _) (pow_nonneg hGn0 _)) he40
  -- the physical errors
  have! h1 : 2 * (30000 * B ^ 2 * G) + Real.sqrt (cT * B ^ 11 * G) ≤
      (60000 + Real.sqrt cT) * (B ^ 6 * G) := by
    have! this := mul_le_mul_of_nonneg_left hB2G6 (show (0 : ℝ) ≤ 60000 by norm_num)
    have! e : (60000 + Real.sqrt cT) * (B ^ 6 * G) =
        60000 * (B ^ 6 * G) + Real.sqrt cT * B ^ 6 * G := by ring
    rw [e]
    linarith only [this, hsT']
  have! h0 : 0 ≤ 2 * (30000 * B ^ 2 * G) + Real.sqrt (cT * B ^ 11 * G) :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num)
      (pow_nonneg hBn0 _)) hGn0)) (Real.sqrt_nonneg _)
  have! h1' := pow_le_pow_left₀ h0 h1 3
  have! hL6 : 0 ≤ 6642 * localFormUniformConstant κ := mul_nonneg (by norm_num) hL00
  have! hp1 : 6642 * localFormUniformConstant κ * (2 * (30000 * B ^ 2 * G) +
      Real.sqrt (cT * B ^ 11 * G)) ^ 3 * (288 * e4 * Real.sqrt δ * R) ≤
      (6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288) *
        (B ^ 18 * G ^ 3 * e4) * Real.sqrt δ * R := by
    have! h2 := mul_le_mul_of_nonneg_left h1' hL6
    have! h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ 288 * e4 * Real.sqrt δ * R from
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) he40) hsd0) hR0)
    refine h3.trans (le_of_eq ?_)
    ring
  -- the core errors
  have! hC0 : 0 ≤ 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 +
      324 * threeErrC κ 3 1 * Real.sqrt cT) := by
    have! this := fourErrC_nonneg κ 3; have := threeErrC_nonneg κ 3 1; positivity
  have! hcE : cE ≤ (5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 *
      Real.sqrt cT)) * (B ^ 18 * G ^ 3 * e4) * Real.exp (-kD) * R +
        ce2 * Real.exp (-(k : ℝ)) * R := by
    have! h2 : cE ≤ Qe * MV * R := by
      calc cE ≤ Qe * (((Mp * V : ℕ) : ℝ) * R) := hcEsum
        _ = Qe * MV * R := by rw [hMVc]; ring
    have! h4 := mul_le_mul_of_nonneg_right hQeMV hR0
    have! h5 : e3 * B ^ 6 * G ≤ B ^ 18 * G ^ 3 * e4 := by
      have! this := mul_le_mul he34 hB18 (by linarith only [hB6G]) he40
      linarith only [this]
    have! h6 : 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 *
        Real.sqrt cT) * e3 * B ^ 6 * G * Real.exp (-kD) ≤
        (5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 *
          Real.sqrt cT)) * (B ^ 18 * G ^ 3 * e4) * Real.exp (-kD) := by
      have! this := mul_le_mul_of_nonneg_left h5 hC0
      have! h7 := mul_le_mul_of_nonneg_right this hekD
      calc _ = 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 *
          Real.sqrt cT) * (e3 * B ^ 6 * G) * Real.exp (-kD) := by ring
        _ ≤ _ := h7
    have! h8 := mul_le_mul_of_nonneg_right h6 hR0
    linarith only [h2, h4, h8]
  -- the constants
  have! hce' : ce * B ^ 18 * G ^ 3 * e4 ≤ Cl * u ^ Cl * Real.exp X ^ Cl *
      Real.exp (Cl * (k : ℝ) ^ cc) := by
    have! h2 : u ^ (18 * Cb) ≤ u ^ Cl := pow_le_pow_right₀ hu1 (by omega)
    have! h3 : G ^ 3 ≤ Real.exp X ^ Cl := by
      rw [hGX, ← pow_mul]; exact pow_le_pow_right₀ hX1 (by omega)
    have! h4 : e4 ≤ Real.exp (Cl * (k : ℝ) ^ cc) := by
      rw [he4]
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (by linarith only [hkcc1]))
      exact_mod_cast (show 4 ≤ Cl by omega)
    have! h5 : ce * (Cb : ℝ) ^ 18 ≤ Cl := by
      have! this : 0 ≤ 3 * 10 ^ 11 * cQ := mul_nonneg (by norm_num) hcQ0
      linarith only [hceil, hcm59, hce2n, this]
    have! e : ce * B ^ 18 * G ^ 3 * e4 = (ce * (Cb : ℝ) ^ 18) * u ^ (18 * Cb) * G ^ 3 * e4 := by
      rw [hBdef, mul_pow, ← pow_mul]; ring
    rw [e]
    have! hu0 : 0 ≤ u := by linarith only [hu1]
    exact mul_le_mul (mul_le_mul (mul_le_mul h5 h2 (pow_nonneg hu0 _) (Nat.cast_nonneg _)) h3
      (pow_nonneg hGn0 _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu0 _))) h4 he40
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu0 _))
        (pow_nonneg (by linarith only [hX1]) _))
  have! hce2' : ce2 ≤ Cl := by
    have! this : 0 ≤ 3 * 10 ^ 11 * cQ := mul_nonneg (by norm_num) hcQ0
    linarith only [hceil, hcm59, hce18, this]
  -- assembly
  have! hsplit : (6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288) *
      (B ^ 18 * G ^ 3 * e4) * Real.sqrt δ * R +
      ((5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 * Real.sqrt cT)) *
        (B ^ 18 * G ^ 3 * e4) * Real.exp (-kD) * R) ≤
      ce * B ^ 18 * G ^ 3 * e4 * ((Real.sqrt δ + Real.exp (-kD)) * R) := by
    have! hA : 0 ≤ 6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288 :=
      mul_nonneg (mul_nonneg hL6 (by positivity)) (by norm_num)
    have! hYR : 0 ≤ B ^ 18 * G ^ 3 * e4 * R := mul_nonneg hY0 hR0
    have hce' : ce = 6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288 +
        9 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 +
          324 * threeErrC κ 3 1 * Real.sqrt cT) := hce
    have! h5 : 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 *
        Real.sqrt cT) ≤ ce := by linarith only [hce', hA, hC0]
    have! h6 : 6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288 ≤ ce := by
      linarith only [hce', hC0]
    have! h7 := mul_le_mul_of_nonneg_right h6 (mul_nonneg hYR hsd0)
    have! h8 := mul_le_mul_of_nonneg_right h5 (mul_nonneg hYR hekD)
    calc _ = (6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288) *
          ((B ^ 18 * G ^ 3 * e4 * R) * Real.sqrt δ) +
          (5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 *
            Real.sqrt cT)) * ((B ^ 18 * G ^ 3 * e4 * R) * Real.exp (-kD)) := by ring
      _ ≤ ce * ((B ^ 18 * G ^ 3 * e4 * R) * Real.sqrt δ) +
          ce * ((B ^ 18 * G ^ 3 * e4 * R) * Real.exp (-kD)) := add_le_add h7 h8
      _ = _ := by ring
  have! hfin1 := mul_le_mul_of_nonneg_right hce' (show 0 ≤ (Real.sqrt δ + Real.exp (-kD)) * R
    from mul_nonneg (add_nonneg hsd0 hekD) hR0)
  have! hfin2 := mul_le_mul_of_nonneg_right hce2' (show 0 ≤ Real.exp (-(k : ℝ)) * R
    from mul_nonneg hek hR0)
  have! e6 : Cl * u ^ Cl * Real.exp X ^ Cl * (Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ +
      Real.exp (-kD))) * R = Cl * u ^ Cl * Real.exp X ^ Cl *
        Real.exp (Cl * (k : ℝ) ^ cc) * ((Real.sqrt δ + Real.exp (-kD)) * R) := by ring
  have! e7 : ce2 * Real.exp (-(k : ℝ)) * R = ce2 * (Real.exp (-(k : ℝ)) * R) := by ring
  have! e8 : (Cl : ℝ) * Real.exp (-(k : ℝ)) * R = Cl * (Real.exp (-(k : ℝ)) * R) := by ring
  rw [e6, e8]
  rw [e7] at hcE
  linarith only [hp1, hcE, hsplit, hfin1, hfin2]

/-- Step `hfc0` of `leaf_final`, over the part of its context that it uses. -/
theorem leaf_final_hfc0 :
    ∀ (P : ℕ) (famFuel : ℕ) (τ₃ : ℝ), (0 : ℝ) < τ₃ → ∀ (fc : ℝ),
      fc = ((2 : ℝ) * (↑famFuel : ℝ) + (2 : ℝ)) * (((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((16 : ℝ) *
        τ₃ * (2 : ℝ) ^ (2 : ℕ))) → (0 : ℝ) ≤ ((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) →
    0 ≤ fc := by
  intro P famFuel τ₃ hτ₃ fc hfc hP0'
  rw [hfc]
  have! h1 : (0 : ℝ) ≤ 2 * (famFuel : ℝ) + 2 := by positivity
  exact mul_nonneg h1 (mul_nonneg hP0' (by linarith only [hτ₃]))



end TrilinearHT.Auto
end
