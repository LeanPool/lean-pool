/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec162QuantitativeInequality.ScalarBounds

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
    have hW0 : 0 ≤ W := by positivity
    clear_value G0 W L0 g frz
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
    clear_value X Y Z1
    have h1 : (Lp : ℝ) ^ 2 * (L0 ^ 2 * (8 * B₀ ^ 2 * (4 * E * R))) + X ≤ 247808 * Z1 * R := by
      linarith only [hX, hU1]
    have := mul_le_mul hLJ h1 (by positivity) (by positivity)
    calc _ ≤ 10 * ((Lp : ℝ) ^ 2 * (1 + (Jm : ℝ))) * (247808 * Z1 * R) := this
      _ = _ := by rw [hYZ]; ring
  -- the second three-side term
  have hT2 : (Lp : ℝ) ^ 2 * (2 * (1 + 5 * (Jm : ℝ))) * X ≤ 2476800 * Y * R := by
    clear_value X Y Z1
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
  clear_value Kc
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
  clear_value Qe
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
  clear_value Qe
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
  clear_value Cjg G0e W
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
  exact (mul_le_mul_of_nonneg_left hnearS (by norm_num : (0 : ℝ) ≤ 6)).trans
    (hfin.trans hfin2)

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


end TrilinearHT.Auto
end
