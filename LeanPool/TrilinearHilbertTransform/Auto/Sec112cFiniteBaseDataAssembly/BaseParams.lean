/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec112cFiniteBaseDataAssembly.BaseTuple

/-!
# Trilinear Hilbert transform: baseParams
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def BaseParamsHP2Statement : Prop :=
  ∀ (C₁ : ℕ)
    (Ca : ℕ),
  let d : ℕ :=
    (2 : ℕ) * C₁ + (2 : ℕ)
  let w : ℕ :=
    max d ((2 : ℕ) * Ca + (1 : ℕ)) + (1 : ℕ)
  let w' : ℕ :=
    max w (d + (2 : ℕ)) + (1 : ℕ)
  let s : ℕ :=
    w' + (1 : ℕ)
  ∀ (Cqa : ℝ)
    (L : ℝ)
    (_ : (2 : ℝ) ≤ L)
    (Mt : ℕ)
    (Hh : ℝ),
  let D : ℝ :=
    max Hh (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + L ^ (2 : ℕ) + Real.log Hh) ^ C₁))
  let K₀ : ℕ :=
    ⌈L ^ (d + (1 : ℕ))⌉₊
  let ε : ℝ :=
    Real.exp (-L ^ (d + (2 : ℕ)))
  let ka : ℕ :=
    ⌈L ^ (2 : ℕ)⌉₊
  let kb : ℕ :=
    ⌈L ^ s⌉₊
  let Ma : ℕ :=
    ⌊(16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ)⌋₊ + (1 : ℕ)
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  ∀ (_ : L ^ w + (1 / 2 : ℝ) * L ^ (d + (1 : ℕ)) + (1 / 2 : ℝ) * (1 : ℝ) + (1 / 2 : ℝ) * L ^
      (d + (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) ≤ L ^ w')
    (_ : Real.log (4 : ℝ) * (1 : ℝ) + L + L ^ w' ≤ L ^ s)
    (_ : (4 : ℝ) ≤ Real.exp (2 : ℝ))
    (_ : (↑Wa : ℝ) ≤ Real.exp (L ^ w))
    (_ : (↑K₀ : ℝ) ≤ L ^ (d + (1 : ℕ)) + (1 : ℝ))
    (_ : Real.exp (-(↑kb : ℝ)) ≤ Real.exp (-L ^ s)),
  ((1 : ℝ) + ((↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)) ≤
    Real.exp (-L) / (2 : ℝ)


open scoped Classical in
private def BaseParamsStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (C₁ : ℕ)
    (Ca : ℕ),
  let d : ℕ :=
    (2 : ℕ) * C₁ + (2 : ℕ)
  let w : ℕ :=
    max d ((2 : ℕ) * Ca + (1 : ℕ)) + (1 : ℕ)
  let w' : ℕ :=
    max w (d + (2 : ℕ)) + (1 : ℕ)
  let s : ℕ :=
    w' + (1 : ℕ)
  let w'' : ℕ :=
    max d (s * Ca + (1 : ℕ)) + (1 : ℕ)
  let S : ℕ :=
    w'' + w + d + s * Ca + (2 : ℕ) * Ca + (4 : ℕ)
  ∀ (Cqa : ℝ),
  let dl : ℝ :=
    delayConst κ
  ∀ (L : ℝ)
    (_ : (2 : ℝ) ≤ L)
    (_ : (0 : ℝ) ≤ L)
    (Mt : ℕ)
    (Hh : ℝ)
    (_ : (↑Mt : ℝ) ≤ Real.exp L),
  let D : ℝ :=
    max Hh (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + L ^ (2 : ℕ) + Real.log Hh) ^ C₁))
  let K₀ : ℕ :=
    ⌈L ^ (d + (1 : ℕ))⌉₊
  let ε : ℝ :=
    Real.exp (-L ^ (d + (2 : ℕ)))
  let ka : ℕ :=
    ⌈L ^ (2 : ℕ)⌉₊
  let kb : ℕ :=
    ⌈L ^ s⌉₊
  let Ma : ℕ :=
    ⌊(16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ)⌋₊ + (1 : ℕ)
  let Mb : ℕ :=
    ⌊(16 : ℝ) * fitBudget Cqa Ca kb ^ (2 : ℕ)⌋₊ + (1 : ℕ)
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  ∀ (_ : L ^ w + (1 / 2 : ℝ) * L ^ (d + (1 : ℕ)) + (1 / 2 : ℝ) * (1 : ℝ) + (1 / 2 : ℝ) * L ^
      (d + (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) ≤ L ^ w')
    (_ : Real.log (1760 : ℝ) * (1 : ℝ) + (5 : ℝ) * L ≤ L ^ (2 : ℕ))
    (_ : Real.log (4 : ℝ) * (1 : ℝ) + L + L ^ w' ≤ L ^ s)
    (_ : L + (4 : ℝ) * (1 : ℝ) + L ^ w + L ^ w'' ≤ L ^ S)
    (_ : ∀ {a b : ℕ}, a ≤ b → L ^ a ≤ L ^ b)
    (_ : ∀ (a : ℕ), (1 : ℝ) ≤ L ^ a)
    (_ : (4 : ℝ) ≤ Real.exp (2 : ℝ))
    (_ : (1 : ℝ) ≤ Real.exp L)
    (_ : D ≤ Real.exp (L ^ d))
    (_ : L ^ (2 : ℕ) ≤ (↑ka : ℝ))
    (_ : L ^ s ≤ (↑kb : ℝ))
    (_ : fitBudget Cqa Ca ka ≤ Real.exp (L ^ ((2 : ℕ) * Ca + (1 : ℕ))))
    (_ : fitBudget Cqa Ca kb ≤ Real.exp (L ^ (s * Ca + (1 : ℕ))))
    (_ : (0 : ℝ) ≤ (↑Mt : ℝ))
    (_ : (↑Wa : ℝ) ≤ Real.exp (L ^ w))
    (_ : (↑Wb : ℝ) ≤ Real.exp (L ^ w''))
    (_ : (↑K₀ : ℝ) ≤ L ^ (d + (1 : ℕ)) + (1 : ℝ)),
  let e2 : ℝ :=
    (2 : ℝ)⁻¹ ^ K₀ + ((1 : ℝ) + (↑K₀ : ℝ)) * √ε
  ∀ (_ : (↑((2 : ℕ) * Mt) : ℝ) * (↑((2 : ℕ) * Mt) : ℝ) * (((2 : ℝ) * Real.exp (-L ^ (2 : ℕ))
      * ((2 : ℝ) * (compBound Wa ε + (↑K₀ : ℝ)) + (1 : ℝ)) + D ^ (2 : ℕ) * (dl * e2 *
      ((1 : ℝ) + D) ^ (4 : ℕ))) * ((2 : ℝ) * ((1 : ℝ) + fitOpponentConst Mt) + (4 : ℝ))
      + ((2 : ℝ) * Real.exp (-L ^ (2 : ℕ)) * ((2 : ℝ) * (compBound Wb ε + (↑K₀ : ℝ)) +
      (1 : ℝ)) + D ^ (2 : ℕ) * (dl * e2 * ((1 : ℝ) + D) ^ (4 : ℕ))) * ((2 : ℝ) * ((2 :
      ℝ) * (compBound Wa ε + (↑K₀ : ℝ)) + fitOpponentConst Mt) + (4 : ℝ))) ≤ (4 : ℝ) *
      Real.exp L ^ (2 : ℕ) * (((2 : ℝ) * Real.exp (-L ^ (2 : ℕ)) * ((4 : ℝ) * Real.exp L
      + (1 : ℝ)) + Real.exp (L ^ d) ^ (2 : ℕ) * (dl * ((3 : ℝ) * Real.exp L * Real.exp
      (-L ^ (d + (1 : ℕ)) / (2 : ℝ))) * ((2 : ℝ) * Real.exp (L ^ d)) ^ (4 : ℕ))) * ((12
      : ℝ) * Real.exp L + (10 : ℝ))))
    (_ : (0 : ℝ) ≤ Real.exp (L ^ d) ^ (2 : ℕ) * (dl * ((3 : ℝ) * Real.exp L * Real.exp (-L ^
      (d + (1 : ℕ)) / (2 : ℝ))) * ((2 : ℝ) * Real.exp (L ^ d)) ^ (4 : ℕ)))
    (_ : (880 : ℝ) * Real.exp (-L ^ (2 : ℕ)) * Real.exp L ^ (4 : ℕ) ≤ Real.exp (-L) / (2 : ℝ))
    (_ : (88 : ℝ) * Real.exp L ^ (3 : ℕ) * (Real.exp (L ^ d) ^ (2 : ℕ) * (dl * ((3 : ℝ) *
      Real.exp L * Real.exp (-L ^ (d + (1 : ℕ)) / (2 : ℝ))) * ((2 : ℝ) * Real.exp (L ^
      d)) ^ (4 : ℕ))) ≤ Real.exp (-L) / (2 : ℝ)),
  baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D (L ^ (2 : ℕ)) ε K₀ Wa Wb (fitOpponentConst
    Mt) (fitOpponentConst Mt) ≤ Real.exp (-L) ∧ ((2 : ℝ) + (2 : ℝ) * ((1 : ℝ) + (6 :
    ℝ) * (↑Mt : ℝ))) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) +
    ((↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)) ≤ Real.exp
    (-L) ∧ D ≤ Real.exp (L ^ S) ∧ (↑K₀ : ℝ) ≤ L ^ S ∧ √ε⁻¹ ≤ Real.exp (L ^ S) ∧ (6 :
    ℝ) * (↑Mt : ℝ) + (↑Wa : ℝ) + (↑Wb : ℝ) ≤ Real.exp (L ^ S) ∧ fitBudget Cqa Ca ka ≤
    Real.exp (L ^ S) ∧ fitBudget Cqa Ca kb ≤ Real.exp (L ^ S)


open scoped Classical in
private def BaseParamsStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (C₁ : ℕ)
    (Ca : ℕ),
  let d : ℕ :=
    (2 : ℕ) * C₁ + (2 : ℕ)
  let w : ℕ :=
    max d ((2 : ℕ) * Ca + (1 : ℕ)) + (1 : ℕ)
  let w' : ℕ :=
    max w (d + (2 : ℕ)) + (1 : ℕ)
  let s : ℕ :=
    w' + (1 : ℕ)
  let w'' : ℕ :=
    max d (s * Ca + (1 : ℕ)) + (1 : ℕ)
  let S : ℕ :=
    w'' + w + d + s * Ca + (2 : ℕ) * Ca + (4 : ℕ)
  ∀ (Cqa : ℝ),
  let c5 : ℝ :=
    (512 : ℝ) * ((↑(1 : ℕ) : ℝ) + (1 : ℝ)) ^ (512 : ℕ)
  ∀ (_ : c5 = (512 : ℝ) * ((↑(1 : ℕ) : ℝ) + (1 : ℝ)) ^ (512 : ℕ)),
  let dl : ℝ :=
    delayConst κ
  ∀ (L : ℝ)
    (_ : (c5 * ((3 : ℝ) + L ^ w + L ^ (d + (2 : ℕ)))) ^ ((512 : ℕ) * ((1 : ℕ) + (1 : ℕ))) ≤
      Real.exp L)
    (_ : (c5 * ((3 : ℝ) + L ^ w'' + L ^ (d + (2 : ℕ)))) ^ ((512 : ℕ) * ((1 : ℕ) + (1 : ℕ))) ≤
      Real.exp L)
    (_ : (c5 * ((3 : ℝ) + L ^ (1 : ℕ) + L ^ (1 : ℕ))) ^ ((512 : ℕ) * ((1 : ℕ) + (1 : ℕ))) ≤
      Real.exp L)
    (_ : (2 : ℝ) * L ^ (d + (1 : ℕ)) ≤ Real.exp L)
    (_ : (2 : ℝ) ≤ L)
    (_ : (0 : ℝ) ≤ L)
    (Mt : ℕ)
    (Hh : ℝ)
    (_ : (↑Mt : ℝ) ≤ Real.exp L)
    (_ : (1 : ℝ) ≤ Hh),
  let D : ℝ :=
    max Hh (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + L ^ (2 : ℕ) + Real.log Hh) ^ C₁))
  let K₀ : ℕ :=
    ⌈L ^ (d + (1 : ℕ))⌉₊
  let ε : ℝ :=
    Real.exp (-L ^ (d + (2 : ℕ)))
  let ka : ℕ :=
    ⌈L ^ (2 : ℕ)⌉₊
  let kb : ℕ :=
    ⌈L ^ s⌉₊
  let Ma : ℕ :=
    ⌊(16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ)⌋₊ + (1 : ℕ)
  let Mb : ℕ :=
    ⌊(16 : ℝ) * fitBudget Cqa Ca kb ^ (2 : ℕ)⌋₊ + (1 : ℕ)
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  ∀ (_ : (3 : ℝ) * (1 : ℝ) + (2 : ℝ) * L + L ^ d + (3 : ℝ) * (1 : ℝ) + (2 : ℝ) * L ^ ((2 : ℕ)
      * Ca + (1 : ℕ)) ≤ L ^ w)
    (_ : L ^ w + (1 / 2 : ℝ) * L ^ (d + (1 : ℕ)) + (1 / 2 : ℝ) * (1 : ℝ) + (1 / 2 : ℝ) * L ^
      (d + (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) ≤ L ^ w')
    (_ : (3 : ℝ) * (1 : ℝ) + (2 : ℝ) * L + L ^ d + (3 : ℝ) * (1 : ℝ) + (2 : ℝ) * L ^ (s * Ca
      + (1 : ℕ)) ≤ L ^ w'')
    (_ : Real.log (1760 : ℝ) * (1 : ℝ) + (5 : ℝ) * L ≤ L ^ (2 : ℕ))
    (_ : (2 : ℝ) * Real.log ((2 : ℝ) * (88 : ℝ) * (48 : ℝ) * (dl + (1 : ℝ))) * (1 : ℝ) + (10
      : ℝ) * L + (12 : ℝ) * L ^ d ≤ L ^ (d + (1 : ℕ)))
    (_ : Real.log (4 : ℝ) * (1 : ℝ) + L + L ^ w' ≤ L ^ s)
    (_ : L + (4 : ℝ) * (1 : ℝ) + L ^ w + L ^ w'' ≤ L ^ S)
    (_ : ∀ {a b : ℕ}, a ≤ b → L ^ a ≤ L ^ b)
    (_ : ∀ (a : ℕ), (1 : ℝ) ≤ L ^ a)
    (_ : (4 : ℝ) ≤ Real.exp (2 : ℝ))
    (_ : (1 : ℝ) ≤ Real.exp L)
    (_ : (1 : ℝ) ≤ D)
    (_ : D ≤ Real.exp (L ^ d))
    (_ : L ^ (2 : ℕ) ≤ (↑ka : ℝ))
    (_ : L ^ s ≤ (↑kb : ℝ))
    (_ : fitBudget Cqa Ca ka ≤ Real.exp (L ^ ((2 : ℕ) * Ca + (1 : ℕ))))
    (_ : fitBudget Cqa Ca kb ≤ Real.exp (L ^ (s * Ca + (1 : ℕ))))
    (_ : (↑Ma : ℝ) ≤ Real.exp ((3 : ℝ) + (2 : ℝ) * L ^ ((2 : ℕ) * Ca + (1 : ℕ))))
    (_ : (↑Mb : ℝ) ≤ Real.exp ((3 : ℝ) + (2 : ℝ) * L ^ (s * Ca + (1 : ℕ)))),
  baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D (L ^ (2 : ℕ)) ε K₀ Wa Wb (fitOpponentConst
    Mt) (fitOpponentConst Mt) ≤ Real.exp (-L) ∧ ((2 : ℝ) + (2 : ℝ) * ((1 : ℝ) + (6 :
    ℝ) * (↑Mt : ℝ))) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) +
    ((↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)) ≤ Real.exp
    (-L) ∧ D ≤ Real.exp (L ^ S) ∧ (↑K₀ : ℝ) ≤ L ^ S ∧ √ε⁻¹ ≤ Real.exp (L ^ S) ∧ (6 :
    ℝ) * (↑Mt : ℝ) + (↑Wa : ℝ) + (↑Wb : ℝ) ≤ Real.exp (L ^ S) ∧ fitBudget Cqa Ca ka ≤
    Real.exp (L ^ S) ∧ fitBudget Cqa Ca kb ≤ Real.exp (L ^ S)




private theorem baseParams_hP2 : BaseParamsHP2Statement := by
  classical
  intro C₁ Ca d w w' s Cqa L hL2 Mt Hh D K₀ ε ka kb Ma Wa f4 f14 he2 hWa hK0 hkb2
  have h2K : (2 : ℝ) ^ K₀ ≤ Real.exp K₀ := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith only [Real.add_one_le_exp (1 : ℝ)]) _
  have hsq : Real.sqrt (2 ^ K₀ / ε) ≤ Real.exp ((K₀ + L ^ (d + 2)) / 2) := by
    have : (2 : ℝ) ^ K₀ / ε ≤ Real.exp (K₀ + L ^ (d + 2)) := by
      rw [div_eq_mul_inv, show ε⁻¹ = Real.exp (L ^ (d + 2)) by
        simp only [ε, Real.exp_neg, inv_inv], Real.exp_add]
      exact mul_le_mul_of_nonneg_right h2K (Real.exp_pos _).le
    exact (Real.sqrt_le_sqrt this).trans (le_of_eq (sqrt_exp' _))
  set! X := L ^ w + (K₀ + L ^ (d + 2)) / 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have h1 : (Wa : ℝ) * Real.sqrt (2 ^ K₀ / ε) ≤ Real.exp X := by
    rw [hX, Real.exp_add]
    exact mul_le_mul hWa hsq (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have h2 : 1 + ((Wa : ℝ) * Real.sqrt (2 ^ K₀ / ε) + 1) ≤ Real.exp (L ^ w') := by
    have h3 : 2 + Real.exp X ≤ Real.exp (X + 2) := by
      rw [Real.exp_add X 2]
      have := Real.one_le_exp hX0
      have k := mul_le_mul_of_nonneg_left he2 (Real.exp_pos X).le
      linarith only [k, this]
    have h4 : X + 2 ≤ L ^ w' := by
      have g4 := f4
      have gK := hK0
      rw [hX]
      generalize L ^ w = P1 at g4 gK ⊢
      generalize L ^ (d + 1) = P2 at g4 gK ⊢
      generalize L ^ (d + 2) = P3 at g4 gK ⊢
      generalize L ^ w' = P4 at g4 gK ⊢
      linarith only [g4, gK]
    linarith only [h1, h3, Real.exp_le_exp.mpr h4]
  have h5 := mul_le_mul h2 hkb2 (Real.exp_pos _).le (Real.exp_pos _).le
  refine h5.trans ?_
  rw [← Real.exp_add, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm]
  refine mul_exp_le_exp (by norm_num) ?_
  have : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have g14 := f14
  rw [mul_one] at g14
  generalize Real.log 4 = A at g14 this
  generalize Real.log 2 = B at this ⊢
  linarith only [g14, this]
-- the outputs



private theorem baseParams_stage_2 : BaseParamsStage2Statement := by
  classical
  intro κ C₁ Ca d w w' s w'' S Cqa dl L hL2 hL0 Mt Hh hMt D K₀ ε ka kb Ma Mb Wa Wb f4 f11 f14 f15
    hpow hp1 he2 heL hDd hka0 hkb0 hBa hBb hMt0 hWa hWb hK0 e2 hmain hTU0 hE1 hE2
  have herr := hmain.trans (final_err_aux heL (Real.exp_pos _).le hTU0 hE1 hE2)
  -- the pair control
  have hka2 : Real.exp (-(ka : ℝ)) ≤ Real.exp (-(L ^ 2)) := Real.exp_le_exp.mpr (by
    linarith only [hka0])
  have hLs2 : L ^ 2 ≤ L ^ s := hpow (by omega)
  have hkb2 : Real.exp (-(kb : ℝ)) ≤ Real.exp (-(L ^ s)) := Real.exp_le_exp.mpr (by
    linarith only [hkb0])
  have hkb3 : Real.exp (-(L ^ s)) ≤ Real.exp (-(L ^ 2)) := Real.exp_le_exp.mpr (by
    linarith only [hLs2])
  have hP1 : (2 + 2 * (1 + 6 * (Mt : ℝ))) * (Real.exp (-(ka : ℝ)) + Real.exp (-(kb : ℝ))) ≤
      Real.exp (-L) / 2 := by
    have h1 : 2 + 2 * (1 + 6 * (Mt : ℝ)) ≤ 16 * Real.exp L := by linarith only [hMt, heL]
    have h2 : Real.exp (-(ka : ℝ)) + Real.exp (-(kb : ℝ)) ≤ 2 * Real.exp (-(L ^ 2)) := by
      linarith only [hka2, hkb2, hkb3]
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have e1 : 16 * Real.exp L * (2 * Real.exp (-(L ^ 2))) = 32 * Real.exp (L - L ^ 2) := by
      rw [show L - L ^ 2 = L + -(L ^ 2) by ring, Real.exp_add]; ring
    rw [e1] at h3
    refine h3.trans ?_
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm, ← mul_assoc,
      show (2 : ℝ) * 32 = 64 by norm_num]
    refine mul_exp_le_exp (by norm_num) ?_
    have : Real.log 64 ≤ Real.log 1760 := Real.log_le_log (by norm_num) (by norm_num)
    have g11 := f11
    rw [mul_one] at g11
    generalize Real.log 1760 = A at g11 this
    generalize Real.log 64 = B at this ⊢
    linarith only [g11, this, hL0]
  have hP2 : (1 + (Wa * Real.sqrt (2 ^ K₀ / ε) + 1)) * Real.exp (-(kb : ℝ)) ≤
      Real.exp (-L) / 2 := by
    expose_names
    exact @baseParams_hP2 C₁ Ca Cqa L hL2 Mt Hh f4 f14 he2 hWa hK0 hkb2
  have he26 : (6 : ℝ) ≤ Real.exp 2 := by
    have h8 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith only [this]
    have h6 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    calc (6 : ℝ) ≤ 2.7 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h8 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold baseErr
    exact herr
  · linarith only [hP1, hP2]
  · exact hDd.trans (Real.exp_le_exp.mpr (hpow (by omega)))
  · have h1 : L ^ (d + 1) + 1 ≤ L ^ (d + 2) := by
      rw [pow_succ L (d + 1)]
      have := hp1 (d + 1)
      nlinarith only [this, hL2]
    exact hK0.trans (h1.trans (hpow (by omega)))
  · rw [show ε⁻¹ = Real.exp (L ^ (d + 2)) by simp only [ε, Real.exp_neg, inv_inv], sqrt_exp']
    exact Real.exp_le_exp.mpr ((show L ^ (d + 2) / 2 ≤ L ^ (d + 2) by
      linarith only [hp1 (d + 2)]).trans (hpow (show d + 2 ≤ S by omega)))
  · have h1 : 6 * (Mt : ℝ) ≤ Real.exp (L + 2) := by
      rw [Real.exp_add, mul_comm (Real.exp L)]
      exact mul_le_mul he26 hMt hMt0 (Real.exp_pos _).le
    have h2 := (add_le_add (add_le_add h1 hWa) hWb).trans
      ((add_le_add (exp_add_exp_le (by positivity) (by positivity)) le_rfl).trans
        (exp_add_exp_le (by positivity) (by positivity)))
    refine le_trans (le_of_eq (by ring)) (h2.trans (Real.exp_le_exp.mpr ?_))
    have g15 := f15
    generalize L ^ w = P1 at g15 ⊢
    generalize L ^ w'' = P2 at g15 ⊢
    generalize L ^ S = P3 at g15 ⊢
    linarith only [g15]
  · exact hBa.trans (Real.exp_le_exp.mpr (hpow (by omega)))
  · exact hBb.trans (Real.exp_le_exp.mpr (hpow (by omega)))



private theorem baseParams_stage_1 : BaseParamsStage1Statement := by
  classical
  intro κ C₁ Ca d w w' s w'' S Cqa c5 hc5 dl L f7 f8 f9 f10 hL2 hL0 Mt Hh hMt hH1 D K₀ ε ka kb Ma
    Mb Wa Wb f3 f4 f6 f11 f12 f14 f15 hpow hp1 he2 heL hD1 hDd hka0 hkb0 hBa hBb hMa hMb
  have hMt0 : (0 : ℝ) ≤ Mt := Nat.cast_nonneg _
  have h4D : ((2 * Mt * (2 * Mt) * ⌊D⌋₊ : ℕ) : ℝ) ≤ Real.exp (2 + 2 * L + L ^ d) := by
    push_cast
    have hfl : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le (by linarith only [hD1])
    have h1 : 2 * (Mt : ℝ) * (2 * Mt) ≤ 4 * Real.exp L ^ 2 := by
      calc 2 * (Mt : ℝ) * (2 * Mt) = 4 * (Mt : ℝ) ^ 2 := by ring
        _ ≤ 4 * Real.exp L ^ 2 := by gcongr
    rw [Real.exp_add, Real.exp_add, show 2 * L = L + L by ring, Real.exp_add]
    have h2 : 4 * Real.exp L ^ 2 * D ≤ Real.exp 2 * (Real.exp L * Real.exp L) *
        Real.exp (L ^ d) := by
      rw [← sq]
      exact mul_le_mul (mul_le_mul_of_nonneg_right he2 (sq_nonneg _)) hDd
        (by linarith only [hD1]) (by positivity)
    calc 2 * (Mt : ℝ) * (2 * Mt) * ⌊D⌋₊ ≤ 4 * Real.exp L ^ 2 * D :=
          mul_le_mul h1 hfl (Nat.cast_nonneg _) (by positivity)
      _ ≤ _ := h2
  have hWa : (Wa : ℝ) ≤ Real.exp (L ^ w) := by
    have : (Wa : ℝ) = ((2 * Mt * (2 * Mt) * ⌊D⌋₊ : ℕ) : ℝ) + Ma := by
      simp only [Wa]; push_cast; ring
    rw [this]
    refine (add_le_add h4D hMa).trans ((exp_add_exp_le (by positivity) (by positivity)).trans
      (Real.exp_le_exp.mpr ?_))
    linarith only [f3]
  have hWb : (Wb : ℝ) ≤ Real.exp (L ^ w'') := by
    have : (Wb : ℝ) = ((2 * Mt * (2 * Mt) * ⌊D⌋₊ : ℕ) : ℝ) + Mb := by
      simp only [Wb]; push_cast; ring
    rw [this]
    refine (add_le_add h4D hMb).trans ((exp_add_exp_le (by positivity) (by positivity)).trans
      (Real.exp_le_exp.mpr ?_))
    linarith only [f6]
  -- the compression constants, opponents and delay
  have hc5 : 0 ≤ c5 := by positivity
  have hba : compBound Wa ε ≤ Real.exp L :=
    (compBound_le (y := L ^ w) (z := L ^ (d + 2)) (by positivity) (by positivity) hWa).trans f7
  have hbb : compBound Wb ε ≤ Real.exp L :=
    (compBound_le (y := L ^ w'') (z := L ^ (d + 2)) (by positivity) (by positivity) hWb).trans f8
  have hCg : fitOpponentConst Mt ≤ Real.exp L := by
    refine (fitOpponentConst_le hL0 hMt).trans (le_trans ?_ f9)
    refine pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left ?_ hc5) _
    simp only [pow_one]; linarith only [hL0]
  have hK0 : (K₀ : ℝ) ≤ L ^ (d + 1) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hK1 : L ^ (d + 1) ≤ K₀ := Nat.le_ceil _
  have hKe : (K₀ : ℝ) ≤ Real.exp L := by linarith only [hK0, f10, hp1 (d + 1)]
  have hs1 : Real.exp (1 / 2) ≤ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 ≤ 4 := by have := Real.exp_one_lt_d9; linarith only [this]
    have h3 : Real.exp (1 / 2) ^ 2 ≤ 2 ^ 2 := by rw [h1]; norm_num; exact h2
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) two_ne_zero).mp h3
  have hhalf : (2⁻¹ : ℝ) ^ K₀ ≤ Real.exp (-(L ^ (d + 1)) / 2) := by
    have h1 : (2⁻¹ : ℝ) ≤ Real.exp (-(1 / 2)) := by
      rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos _) hs1
    calc (2⁻¹ : ℝ) ^ K₀ ≤ Real.exp (-(1 / 2)) ^ K₀ := pow_le_pow_left₀ (by norm_num) h1 _
      _ = Real.exp (-(K₀ : ℝ) / 2) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(L ^ (d + 1)) / 2) := Real.exp_le_exp.mpr (by linarith only [hK1])
  have hsqε : Real.sqrt ε = Real.exp (-(L ^ (d + 2)) / 2) := sqrt_exp_neg _
  have heL2 : 4 ≤ Real.exp L := le_trans he2 (Real.exp_le_exp.mpr hL2)
  have he2' : (2⁻¹ : ℝ) ^ K₀ + (1 + K₀) * Real.sqrt ε ≤
      3 * Real.exp L * Real.exp (-(L ^ (d + 1)) / 2) := by
    rw [hsqε]
    have h1 : Real.exp (-(L ^ (d + 2)) / 2) ≤ Real.exp (-(L ^ (d + 1)) / 2) :=
      Real.exp_le_exp.mpr (by linarith only [hpow (show d + 1 ≤ d + 2 by omega)])
    have h2 : 1 + (K₀ : ℝ) ≤ 2 * Real.exp L := by linarith only [hK0, f10, heL2]
    have h3 := mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
    have h4 : Real.exp (-(L ^ (d + 1)) / 2) ≤ Real.exp L * Real.exp (-(L ^ (d + 1)) / 2) :=
      le_mul_of_one_le_left (Real.exp_pos _).le heL
    linarith only [h3, h4, hhalf]
  set e2 := (2⁻¹ : ℝ) ^ K₀ + (1 + K₀) * Real.sqrt ε with he2_def
  have he20 : 0 ≤ e2 := by positivity
  have hdl0 : 0 ≤ dl := delayConst_nonneg κ
  have hT : D ^ 2 * (dl * e2 * (1 + D) ^ 4) ≤
      Real.exp (L ^ d) ^ 2 * (dl * (3 * Real.exp L * Real.exp (-(L ^ (d + 1)) / 2)) *
        (2 * Real.exp (L ^ d)) ^ 4) := by
    have h1 : 1 + D ≤ 2 * Real.exp (L ^ d) := by linarith only [hDd, hD1]
    gcongr
  -- the error
  have hc : ((2 * Mt : ℕ) : ℝ) * ((2 * Mt : ℕ) : ℝ) ≤ 4 * Real.exp L ^ 2 := by
    push_cast
    calc 2 * (Mt : ℝ) * (2 * Mt) = 4 * (Mt : ℝ) ^ 2 := by ring
      _ ≤ 4 * Real.exp L ^ 2 := by gcongr
  have hmain := errExpr_le (c := ((2 * Mt : ℕ) : ℝ) * ((2 * Mt : ℕ) : ℝ))
    (cU := 4 * Real.exp L ^ 2) (e := Real.exp (-(L ^ 2))) (U := Real.exp L)
    (T := D ^ 2 * (dl * e2 * (1 + D) ^ 4))
    (TU := Real.exp (L ^ d) ^ 2 * (dl * (3 * Real.exp L * Real.exp (-(L ^ (d + 1)) / 2)) *
        (2 * Real.exp (L ^ d)) ^ 4))
    (K := K₀) (ba := compBound Wa ε) (bb := compBound Wb ε) (Cg := fitOpponentConst Mt)
    (by positivity) hc (Real.exp_pos _).le (by positivity) hT (Nat.cast_nonneg _) hKe
    (compBound_nonneg _ _) hba (compBound_nonneg _ _) hbb (fitOpponentConst_nonneg _) hCg
  have hTU0 : 0 ≤ Real.exp (L ^ d) ^ 2 * (dl * (3 * Real.exp L * Real.exp (-(L ^ (d + 1)) / 2)) *
      (2 * Real.exp (L ^ d)) ^ 4) := by positivity
  have hE1 : 880 * Real.exp (-(L ^ 2)) * Real.exp L ^ 4 ≤ Real.exp (-L) / 2 := by
    have e1 : 880 * Real.exp (-(L ^ 2)) * Real.exp L ^ 4 = 880 * Real.exp (4 * L - L ^ 2) := by
      rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; congr 2; push_cast; ring
    rw [e1, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm, ← mul_assoc]
    rw [show (2 : ℝ) * 880 = 1760 by norm_num]
    refine mul_exp_le_exp (by norm_num) ?_
    have g11 := f11
    rw [mul_one] at g11
    generalize Real.log 1760 = A at g11 ⊢
    linarith only [g11, hL0]
  have hE2 : 88 * Real.exp L ^ 3 * (Real.exp (L ^ d) ^ 2 * (dl * (3 * Real.exp L *
      Real.exp (-(L ^ (d + 1)) / 2)) * (2 * Real.exp (L ^ d)) ^ 4)) ≤ Real.exp (-L) / 2 := by
    have e1 : 88 * Real.exp L ^ 3 * (Real.exp (L ^ d) ^ 2 * (dl * (3 * Real.exp L *
        Real.exp (-(L ^ (d + 1)) / 2)) * (2 * Real.exp (L ^ d)) ^ 4)) =
        88 * 48 * dl * (Real.exp L ^ 4 * Real.exp (L ^ d) ^ 6 *
          Real.exp (-(L ^ (d + 1)) / 2)) := by ring
    have e2 : Real.exp L ^ 4 * Real.exp (L ^ d) ^ 6 * Real.exp (-(L ^ (d + 1)) / 2) =
        Real.exp (4 * L + 6 * L ^ d - L ^ (d + 1) / 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    rw [e1, e2, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have h3 : 88 * 48 * dl * Real.exp (4 * L + 6 * L ^ d - L ^ (d + 1) / 2) * 2 ≤
        (2 * 88 * 48 * (dl + 1)) * Real.exp (4 * L + 6 * L ^ d - L ^ (d + 1) / 2) := by
      have := Real.exp_pos (4 * L + 6 * L ^ d - L ^ (d + 1) / 2)
      nlinarith only [this, hdl0]
    refine h3.trans (mul_exp_le_exp (by positivity) ?_)
    have g12 := f12
    rw [mul_one] at g12
    generalize Real.log (2 * 88 * 48 * (dl + 1)) = A at g12 ⊢
    linarith only [g12]
  expose_names
  exact @baseParams_stage_2 κ C₁ Ca Cqa L hL2 hL0 Mt Hh hMt f4 f11 f14 f15 hpow hp1 he2 heL hDd
    hka0 hkb0 hBa hBb hMt0 hWa hWb hK0 hmain hTU0 hE1 hE2


/-- Blueprint prop:base, proof lines 1626-1641 (the parameter choices): with `B_p = L²`,
`K₀ = ⌈L^{d+1}⌉`, `ε = e^{-L^{d+2}}`, accuracies `k_a = ⌈L²⌉`, `k_b = ⌈L^s⌉` and caps
`M_e = ⌊16 B(k_e)²⌋ + 1`, for all large `L` and all low data of size at most `e^L` the
replacement error `baseErr` and the pair-control error are at most `e^{-L}`, and all counts,
complexities and inverse weights are at most `exp(L^S)`. -/
theorem baseParams (κ : LocalKernelClass) (C₁ Ca : ℕ) :
    ∃ (d s S : ℕ), ∀ {Cqa : ℝ}, 0 < Cqa → ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧
      ∀ (Mt : ℕ) (Hh : ℝ), (Mt : ℝ) ≤ Real.exp L → 1 ≤ Hh → Real.log Hh ≤ L →
      let D := max Hh (Real.exp (C₁ * (1 + L ^ 2 + Real.log Hh) ^ C₁))
      let K₀ := ⌈L ^ (d + 1)⌉₊
      let ε := Real.exp (-(L ^ (d + 2)))
      let ka := ⌈L ^ 2⌉₊
      let kb := ⌈L ^ s⌉₊
      let Ma := ⌊16 * fitBudget Cqa Ca ka ^ 2⌋₊ + 1
      let Mb := ⌊16 * fitBudget Cqa Ca kb ^ 2⌋₊ + 1
      let Wa := 2 * Mt * (2 * Mt) * ⌊D⌋₊ + Ma
      let Wb := 2 * Mt * (2 * Mt) * ⌊D⌋₊ + Mb
      baseErr κ (2 * Mt) (2 * Mt) D (L ^ 2) ε K₀ Wa Wb (fitOpponentConst Mt)
          (fitOpponentConst Mt) ≤ Real.exp (-L) ∧
      (2 + 2 * (1 + 6 * Mt)) * (Real.exp (-(ka : ℝ)) + Real.exp (-(kb : ℝ))) +
          (1 + (Wa * Real.sqrt (2 ^ K₀ / ε) + 1)) * Real.exp (-(kb : ℝ)) ≤ Real.exp (-L) ∧
      D ≤ Real.exp (L ^ S) ∧ (K₀ : ℝ) ≤ L ^ S ∧ Real.sqrt ε⁻¹ ≤ Real.exp (L ^ S) ∧
      (6 * Mt + Wa + Wb : ℝ) ≤ Real.exp (L ^ S) ∧ fitBudget Cqa Ca ka ≤ Real.exp (L ^ S) ∧
      fitBudget Cqa Ca kb ≤ Real.exp (L ^ S) := by
  set d := 2 * C₁ + 2 with hd
  set w := max d (2 * Ca + 1) + 1 with hw
  set w' := max w (d + 2) + 1 with hw'
  set s := w' + 1 with hs
  set w'' := max d (s * Ca + 1) + 1 with hw''
  set S := w'' + w + d + s * Ca + 2 * Ca + 4 with hS
  refine ⟨d, s, S, fun {Cqa} hCqa => ?_⟩
  set c5 : ℝ := 512 * ((1 : ℕ) + 1 : ℝ) ^ 512 with hc5
  set dl := delayConst κ with hdl
  -- the asymptotic facts
  have F1 := ev_mul_pow_le_pow (C₁ * 3 ^ C₁ + 1) (2 * C₁ + 1)
  have F2 := ev_mul_pow_le_pow (Cqa * 4 ^ Ca) (2 * Ca)
  have F3 := ev_sum5_le_pow (c₁ := 3) (c₂ := 2) (c₃ := 1) (c₄ := 3) (c₅ := 2) (n₁ := 0) (n₂ := 1)
    (n₃ := d) (n₄ := 0) (n₅ := 2 * Ca + 1) (m := w) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have F4 := ev_sum5_le_pow (c₁ := 1) (c₂ := 1 / 2) (c₃ := 1 / 2) (c₄ := 1 / 2) (c₅ := 2)
    (n₁ := w) (n₂ := d + 1) (n₃ := 0) (n₄ := d + 2) (n₅ := 0) (m := w') (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have F5 := ev_mul_pow_le_pow (Cqa * 4 ^ Ca) (s * Ca)
  have F6 := ev_sum5_le_pow (c₁ := 3) (c₂ := 2) (c₃ := 1) (c₄ := 3) (c₅ := 2) (n₁ := 0) (n₂ := 1)
    (n₃ := d) (n₄ := 0) (n₅ := s * Ca + 1) (m := w'') (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have F7 := ev_poly_pow_le_exp c5 w (d + 2) (512 * (1 + 1))
  have F8 := ev_poly_pow_le_exp c5 w'' (d + 2) (512 * (1 + 1))
  have F9 := ev_poly_pow_le_exp c5 1 1 (512 * (1 + 1))
  have F10 := ev_mul_pow_le_exp 2 (d + 1)
  have F11 := ev_sum5_le_pow (c₁ := Real.log 1760) (c₂ := 5) (c₃ := 0) (c₄ := 0) (c₅ := 0)
    (n₁ := 0) (n₂ := 1) (n₃ := 0) (n₄ := 0) (n₅ := 0) (m := 2) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have F12 := ev_sum5_le_pow (c₁ := 2 * Real.log (2 * 88 * 48 * (dl + 1))) (c₂ := 10) (c₃ := 12)
    (c₄ := 0) (c₅ := 0) (n₁ := 0) (n₂ := 1) (n₃ := d) (n₄ := 0) (n₅ := 0) (m := d + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have F14 := ev_sum5_le_pow (c₁ := Real.log 4) (c₂ := 1) (c₃ := 1) (c₄ := 0) (c₅ := 0)
    (n₁ := 0) (n₂ := 1) (n₃ := w') (n₄ := 0) (n₅ := 0) (m := s) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have F15 := ev_sum5_le_pow (c₁ := 1) (c₂ := 4) (c₃ := 1) (c₄ := 1) (c₅ := 0)
    (n₁ := 1) (n₂ := 0) (n₃ := w) (n₄ := w'') (n₅ := 0) (m := S) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  filter_upwards [F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F14, F15,
    Filter.eventually_ge_atTop 2] with L f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f14 f15 hL2
  have hL1 : 1 ≤ L := by linarith only [hL2]
  have hL0 : 0 ≤ L := by linarith only [hL2]
  refine ⟨hL1, fun Mt Hh hMt hH1 hHL => ?_⟩
  intro D K₀ ε ka kb Ma Mb Wa Wb
  simp only [pow_zero, pow_one, one_mul, zero_mul, add_zero] at f3 f4 f6 f11 f12 f14 f15
  have hpow : ∀ {a b : ℕ}, a ≤ b → L ^ a ≤ L ^ b := fun h => pow_le_pow_right₀ hL1 h
  have hp1 : ∀ a : ℕ, 1 ≤ L ^ a := fun a => one_le_pow₀ hL1
  have hlogH : 0 ≤ Real.log Hh := Real.log_nonneg hH1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith only [this]
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have h7 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have h6 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h7 2
  have heL : 1 ≤ Real.exp L := Real.one_le_exp hL0
  -- the budget D
  have hD1 : 1 ≤ D := le_trans hH1 (le_max_left _ _)
  have hDd : D ≤ Real.exp (L ^ d) := by
    apply max_le
    · calc Hh = Real.exp (Real.log Hh) := (Real.exp_log (by linarith only [hH1])).symm
        _ ≤ Real.exp (L ^ d) := Real.exp_le_exp.mpr (hHL.trans (by
            calc L = L ^ 1 := (pow_one L).symm
              _ ≤ L ^ d := hpow (by omega)))
    · apply Real.exp_le_exp.mpr
      have h3 : 1 + L ^ 2 + Real.log Hh ≤ 3 * L ^ 2 := by
        have : L ≤ L ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hL0 hL1
        linarith only [this, hp1 2, hHL]
      calc (C₁ : ℝ) * (1 + L ^ 2 + Real.log Hh) ^ C₁ ≤ C₁ * (3 * L ^ 2) ^ C₁ := by
            gcongr
        _ = (C₁ * 3 ^ C₁) * L ^ (2 * C₁) := by rw [mul_pow, ← pow_mul]; ring
        _ ≤ (C₁ * 3 ^ C₁ + 1) * L ^ (2 * C₁ + 1) :=
            mul_le_mul (le_add_of_nonneg_right zero_le_one) (hpow (by omega)) (by positivity)
              (by positivity)
        _ ≤ L ^ d := f1
  -- the accurate fit budgets and caps
  have hka1 : (ka : ℝ) ≤ L ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hka0 : L ^ 2 ≤ ka := Nat.le_ceil _
  have hkb1 : (kb : ℝ) ≤ L ^ s + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hkb0 : L ^ s ≤ kb := Nat.le_ceil _
  have hBa : fitBudget Cqa Ca ka ≤ Real.exp (L ^ (2 * Ca + 1)) := by
    refine fitBudget_le_of hCqa hka1 ?_
    calc Cqa * (1 + Real.log 2 + (L ^ 2 + 1)) ^ Ca ≤ Cqa * (4 * L ^ 2) ^ Ca := by
          have := hp1 2
          gcongr
          linarith only [hlog2, hp1 2]
      _ = Cqa * 4 ^ Ca * L ^ (2 * Ca) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ L ^ (2 * Ca + 1) := f2
  have hBb : fitBudget Cqa Ca kb ≤ Real.exp (L ^ (s * Ca + 1)) := by
    refine fitBudget_le_of hCqa hkb1 ?_
    calc Cqa * (1 + Real.log 2 + (L ^ s + 1)) ^ Ca ≤ Cqa * (4 * L ^ s) ^ Ca := by
          have := hp1 s
          gcongr
          linarith only [hlog2, hp1 s]
      _ = Cqa * 4 ^ Ca * L ^ (s * Ca) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ L ^ (s * Ca + 1) := f5
  have hB1 : ∀ k : ℕ, 1 ≤ fitBudget Cqa Ca k := fun k => one_le_fitBudget hCqa Ca k
  have hMa : (Ma : ℝ) ≤ Real.exp (3 + 2 * L ^ (2 * Ca + 1)) := by
    have hB0 := le_trans zero_le_one (hB1 ka)
    refine (nat_fit_le (hB1 ka)).trans ?_
    rw [show 3 + 2 * L ^ (2 * Ca + 1) = 3 + L ^ (2 * Ca + 1) + L ^ (2 * Ca + 1) by ring,
      Real.exp_add, Real.exp_add, mul_assoc, ← sq]
    gcongr
  have hMb : (Mb : ℝ) ≤ Real.exp (3 + 2 * L ^ (s * Ca + 1)) := by
    have hB0 := le_trans zero_le_one (hB1 kb)
    refine (nat_fit_le (hB1 kb)).trans ?_
    rw [show 3 + 2 * L ^ (s * Ca + 1) = 3 + L ^ (s * Ca + 1) + L ^ (s * Ca + 1) by ring,
      Real.exp_add, Real.exp_add, mul_assoc, ← sq]
    gcongr
  -- the system sizes
  expose_names
  exact @baseParams_stage_1 κ C₁ Ca Cqa hc5 L f7 f8 f9 f10 hL2 hL0 Mt Hh hMt hH1 f3 f4 f6 f11 f12
    f14 f15 hpow hp1 he2 heL hD1 hDd hka0 hkb0 hBa hBb hMa hMb

theorem stagAcc_mono {k₁ A ℓ t : ℕ} (hk : 1 ≤ k₁) (hA : 1 ≤ A) (h : ℓ ≤ t) :
    stagAcc k₁ A ℓ ≤ stagAcc k₁ A t := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · have : stagAcc k₁ A 0 = k₁ := by simp [stagAcc]
    rw [this]; exact le_stagAcc hk hA t
  · rw [stagAcc_pow hℓ h]
    have h1 : 1 ≤ stagAcc k₁ A ℓ := hk.trans (le_stagAcc hk hA ℓ)
    calc stagAcc k₁ A ℓ = stagAcc k₁ A ℓ ^ 1 := (pow_one _).symm
      _ ≤ stagAcc k₁ A ℓ ^ (A ^ (t - ℓ)) := Nat.pow_le_pow_right h1 (Nat.one_le_pow _ _ hA)

theorem fitBudget_mono {Cq : ℝ} (hCq : 0 < Cq) (C : ℕ) {k k' : ℕ} (h : k ≤ k') :
    fitBudget Cq C k ≤ fitBudget Cq C k' := by
  unfold fitBudget
  apply Real.exp_le_exp.mpr
  have hk : (k : ℝ) ≤ k' := by exact_mod_cast h
  have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  gcongr

/-- Blueprint §11.3, prop:base, Declaration base (`THT.Base.activeCellReduction`, lines
1600-1662). For the stagger data of `twoEarliestIncrements`, every tuple `eq:base-tuple` of the
levels `u < t` (distinct positions) is reduced, with `k = k_t` and any pair bound
`η₀ ≥ e^{-2 k^{θ₀}}` of the tuple (for `t ≥ 12` the stagger cells give `η₀ = e^{-2 k^{θ₀}}`;
for the initial levels a fixed bound, lines 1643 and 1655), to the replaced tuples
`Y = B + U` of finitely many active setups covering every kernel-hull cell of the tree: their
roots have total length at most `91/3 |J|` and disjoint cells; counts, complexities, inverse
private weights and the delay `K₀` are at most `exp(k^{C_b})`; every pair of `Y` is
`2η₀`-small; the normalized sizes are at most two; the basic sides satisfy
`eq:basic-side` with constant `k^{C_b}`, and the two-`U` term is at most `η₀ k^{C_b} |R|`; and
the length-weighted sum of `|H_I(X)|` over the tree is at most the sum of `|H_I(Y)|` over the
active cells plus `e^{-k} 91/3 |J|`; and each basic argument is a
difference of two current basic projections whose inputs have energy at most `|R|` on the root
(lines 1611-1613). The reduction to the active minima
`eq:active-min` with path multiplicity is `ActiveSetup.reduction` and `ActiveSetup.active_count`
applied to each setup. -/
theorem activeCellReduction (κ : LocalKernelClass) :
    ∃ (c₂ C A : ℕ) (θ₀ : ℝ) (c' Cb : ℕ), 1 ≤ c₂ ∧ 1 ≤ C ∧ 2 ≤ A ∧ 0 < θ₀ ∧ θ₀ ≤ 1 ∧ 1 ≤ c' ∧
    ∀ q : ℝ, 2 < q → ∃ (Cq : ℝ) (K₁ : ℕ), 0 < Cq ∧ ∀ k₁ : ℕ, K₁ ≤ k₁ →
    ∀ (G : RealDyadicGrid) (J : ℤ × ℤ) (N : ℕ) (w : ℤ × ℤ → ℝ × ℝ → ℂ),
    (∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
    ∀ (f : Fin 4 → ℝ → ℂ), (∀ p, Measurable (f p)) →
    (∀ p, ∀ I ∈ dyadicFiniteTree G J N, (I = J ∨ kernelHull G J N w I) →
      eLpNorm (f p) (ENNReal.ofReal q)
        (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1) →
    ∃ (M : ℕ → ℕ) (roots : ℕ → Finset (ℤ × ℤ)) (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
      (n : ℕ → ℤ × ℤ → ℕ) (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ) (g : ℕ → ℤ × ℤ → ℝ → ℂ)
      (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ) (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ),
      (∀ t, IsAdaptiveFit c₂ (fitBudget Cq C (stagAcc k₁ A t)) G J N w (stagPos t) q
        (f (stagPos t)) (stagAcc k₁ A t) (M t) (roots t) (seg t) (n t) (a t) (g t) ∧
        IsAttemptData c₂ (fitBudget Cq C (stagAcc k₁ A t)) G J N (M t) (roots t) (seg t) (n t)
          (a t) (cnt t) (atm t) ∧
        IsFitOpponent G J N (f (stagPos t)) (roots t) (seg t) (g t) (fitOpponentConst (M t))
          (max 2 (M t : ℝ)) c₂ (fitBudget Cq C (stagAcc k₁ A t))) ∧
      (∀ L : Finset ℕ, dyadicRootLength G (L.biUnion roots) ≤
        L.card * (4 / 3 * dyadicGridLength G J.1)) ∧
      (∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∃ D : StaggerCell κ,
        D.a₀ = dyadicGridLeft G I.1 I.2 ∧ D.r = dyadicGridLength G I.1 ∧ D.w = w I ∧
        D.q = q ∧ D.f = f ∧ (∀ t, D.g t = g t I) ∧ (∀ t, D.k t = stagAcc k₁ A t) ∧
        (∀ u t, 12 ≤ t → 1 ≤ u → u < t → stagPos u ≠ stagPos t → ∀ s s' : Fin 4, s ≠ s' →
          PairSmall D.a₀ D.r D.w s s' (D.tuple u t s) (D.tuple u t s')
            (Real.exp (-2 * (stagAcc k₁ A t : ℝ) ^ θ₀))) ∧
        (∀ T, D.H D.f = D.H (D.tail T) + ∑ u ∈ Finset.Icc 1 T,
          (D.H (Function.update (D.tail T) (stagPos u) (D.incr u)) +
            ∑ t ∈ Finset.Ioc u T, if stagPos t ≠ stagPos u then D.H (D.tuple u t) else 0)) ∧
        (∀ T, 4 ≤ T → ‖D.H (D.tail T)‖ ≤ 32 * Real.exp (-(stagAcc k₁ A (T - 3) : ℝ)) ∧
          ∀ u, ‖D.H (Function.update (D.tail T) (stagPos u) (D.incr u))‖ ≤
            32 * Real.exp (-(stagAcc k₁ A (T - 3) : ℝ))) ∧
        ∀ u t l, eLpNorm (D.tuple u t l) 2 D.μ ≤ 2) ∧
      ∀ u t, 1 ≤ u → u < t → stagPos u ≠ stagPos t → ∀ η₀ : ℝ,
        Real.exp (-2 * (stagAcc k₁ A t : ℝ) ^ θ₀) ≤ η₀ →
        (∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ s s' : Fin 4, s ≠ s' →
          PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
            (stagTuple f g u t I s) (stagTuple f g u t I s') η₀) →
        ∃ (ι : Type) (_ : Fintype ι) (B : ι → ActiveSetup κ c'),
          ∑ p, dyadicGridLength G (B p).R.1 ≤ 91 / 3 * dyadicGridLength G J.1 ∧
          (∀ p p' : ι, ∀ I, I ∈ (B p).cells → I ∈ (B p').cells → p = p') ∧
          (∀ p, (B p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (B p).cells, kernelHull G J N w I) ∧
            (∀ I ∈ (B p).cells, ∀ J' : ℤ × ℤ,
              dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 →
              dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (B p).R.1 (B p).R.2 →
                J' ∈ (B p).cells) ∧
            (B p).G = G ∧ (B p).w = w ∧
            (B p).R ∈ dyadicFiniteTree G J N ∧
            1 ≤ (B p).H ∧ (B p).H ≤ Real.exp ((stagAcc k₁ A t : ℝ) ^ Cb) ∧
            (B p).Dc ≤ Real.exp ((stagAcc k₁ A t : ℝ) ^ Cb) ∧
            (Fintype.card (B p).L : ℝ) ≤ Real.exp ((stagAcc k₁ A t : ℝ) ^ Cb) ∧
            (B p).S = 2 ∧ (B p).η = 4 * η₀ ∧
            (∀ I ∈ (B p).cells, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
              (dyadicGridLength G I.1) (w I) s s' ((B p).Y I s) ((B p).Y I s')
              (2 * η₀)) ∧
            (∀ I ∈ (B p).cells, ∀ l, (eLpNorm ((B p).Y I l) 2 ((B p).μ I)).toReal ≤ 2) ∧
            (∀ l, ∑ I ∈ (B p).cells, dyadicGridLength G I.1 *
              (eLpNorm ((B p).U l I) 2 ((B p).μ I)).toReal ^ 2 ≤
                (stagAcc k₁ A t : ℝ) ^ Cb * dyadicGridLength G (B p).R.1) ∧
            ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B p).Hf I ((B p).z 3 I)‖ ≤
              η₀ * ((stagAcc k₁ A t : ℝ) ^ Cb * dyadicGridLength G (B p).R.1) ∧
            (B p).HasColumnRep 1 ∧ (B p).SubRootProps η₀ ((stagAcc k₁ A t : ℝ) ^ Cb)) ∧
          ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
              ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤
            ∑ p, ∑ I ∈ (B p).cells, dyadicGridLength G I.1 * ‖(B p).Hf I ((B p).Y I)‖ +
              Real.exp (-(stagAcc k₁ A t : ℝ)) * (91 / 3 * dyadicGridLength G J.1) := by
  obtain ⟨c₂, C, A, θ₀, hc₂, hC, hA, hθ₀, hθ₁, hstag⟩ := twoEarliestIncrements κ
  obtain ⟨cp, Wp, c₁, C₁, c₂a, Ca, hcp, hWp, hc₁, hc₂a, hbt⟩ := baseTuple κ c₂ hc₂
  obtain ⟨d, s, S, hpar⟩ := baseParams κ C₁ Ca
  refine ⟨c₂, C, A, θ₀, max (max c₁ (max c₂ cp)) c₂a, 2 * ((C + 2) * S) + 2, hc₂, hC, hA, hθ₀,
    hθ₁, le_trans hc₂ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))),
    fun q hq => ?_⟩
  obtain ⟨Cq, K₁, hCq, hstag'⟩ := hstag q hq
  obtain ⟨Cqa, hCqa, hbt'⟩ := hbt q hq
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp (hpar hCqa)
  set! K₂ := max (max K₁ 16) (max ⌈4 * Cq * 2 ^ C⌉₊ (max ⌈L₀⌉₊ (⌈3 + 6 * |Real.log Wp|⌉₊ + 4)))
    with hK₂
  refine ⟨Cq, K₂, hCq, fun k₁ hk₁ G J N w hw f hfm hfq => ?_⟩
  have hk₁K : K₁ ≤ k₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk₁
  obtain ⟨M, roots, seg, n, a, g, cnt, atm, hfit, hroots, hcells⟩ :=
    hstag' k₁ hk₁K G J N w hw f hfm hfq
  refine ⟨M, roots, seg, n, a, g, cnt, atm, hfit, hroots, hcells,
    fun u t hu hut hpos η₀ hη₀e hpair => ?_⟩
  -- the accuracy and the size budget
  have hA1 : 1 ≤ A := by omega
  have hk116 : 16 ≤ k₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk₁
  have hk1 : 1 ≤ k₁ := by omega
  set k := stagAcc k₁ A t with hk_def
  have hkk : k₁ ≤ k := le_stagAcc hk1 hA1 t
  have hK₂k : K₂ ≤ k := le_trans hk₁ hkk
  set x : ℝ := (k : ℝ) with hx_def
  have hx16 : (16 : ℝ) ≤ x := by
    have : 16 ≤ k := le_trans hk116 hkk
    rw [hx_def]; exact_mod_cast this
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxC : 4 * Cq * 2 ^ C ≤ (k : ℝ) := by
    have h1 : ⌈4 * Cq * 2 ^ C⌉₊ ≤ k :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK₂k
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hxL₀ : L₀ ≤ x := by
    have h1 : ⌈L₀⌉₊ ≤ k := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) hK₂k
    exact (Nat.le_ceil _).trans (by rw [hx_def]; exact_mod_cast h1)
  have hxW : 3 + 6 * |Real.log Wp| + 4 ≤ x := by
    have h1 : ⌈3 + 6 * |Real.log Wp|⌉₊ + 4 ≤ k := le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) (le_max_right _ _)) hK₂k
    have h2 : 3 + 6 * |Real.log Wp| ≤ ⌈3 + 6 * |Real.log Wp|⌉₊ := Nat.le_ceil _
    have h3 : ((⌈3 + 6 * |Real.log Wp|⌉₊ + 4 : ℕ) : ℝ) ≤ x := by rw [hx_def]; exact_mod_cast h1
    push_cast at h3
    linarith
  set! L : ℝ := x ^ (C + 2) with hL_def
  have hxpow : ∀ m : ℕ, 1 ≤ x ^ m := fun m => one_le_pow₀ hx1
  have hxL : x ≤ L := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ L := pow_le_pow_right₀ hx1 (by omega)
  have hC1L : x ^ (C + 1) ≤ L := pow_le_pow_right₀ hx1 (by omega)
  obtain ⟨hL1, hP⟩ := hL₀ L (hxL₀.trans hxL)
  -- the budgets of the fits
  set! Bt := fitBudget Cq C k with hBt_def
  have hBt := budget_le_exp hCq (show 16 ≤ k from le_trans hk116 hkk) hxC
  have hBt1 : 1 ≤ Bt := one_le_fitBudget hCq C k
  have h17 : (1 : ℝ) ≤ Real.sqrt 17 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hBtx : Bt ≤ Real.exp (x ^ (C + 1) / 2) := le_trans (le_mul_of_one_le_left (by positivity)
    h17) hBt
  have h17B : 17 * Bt ^ 2 ≤ Real.exp L := by
    have h1 : (Real.sqrt 17 * Bt) ^ 2 ≤ Real.exp (x ^ (C + 1) / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hBt 2
    rw [mul_pow, Real.sq_sqrt (by norm_num), ← Real.exp_nat_mul] at h1
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    push_cast
    linarith
  set! Mt : ℕ := ⌊17 * Bt ^ 2⌋₊ with hMt_def
  have hMtL : (Mt : ℝ) ≤ Real.exp L := (Nat.floor_le (by positivity)).trans h17B
  have hBf : ∀ ℓ ≤ t, fitBudget Cq C (stagAcc k₁ A ℓ) ≤ Bt := fun ℓ hℓ =>
    fitBudget_mono hCq C (stagAcc_mono hk1 hA1 hℓ)
  have hMℓ : ∀ ℓ ≤ t, M ℓ ≤ Mt := fun ℓ hℓ => by
    refine Nat.le_floor ((hfit ℓ).1.1.trans ?_)
    have := hBf ℓ hℓ
    have h0 : 0 ≤ fitBudget Cq C (stagAcc k₁ A ℓ) := le_trans zero_le_one (one_le_fitBudget hCq _ _)
    gcongr
  -- the low height
  set! H := max Bt Wp ^ 6 with hH_def
  have hWp1 : 1 ≤ Wp := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hWp
  have hH1 : 1 ≤ H := one_le_pow₀ (le_trans hWp1 (le_max_right _ _))
  have hHL : Real.log H ≤ L := by
    have hmax : max Bt Wp ≤ Real.exp (x ^ (C + 1) / 2 + |Real.log Wp|) := by
      apply max_le
      · exact hBtx.trans (Real.exp_le_exp.mpr (by linarith [abs_nonneg (Real.log Wp)]))
      · calc Wp = Real.exp (Real.log Wp) := (Real.exp_log (by linarith)).symm
          _ ≤ _ := Real.exp_le_exp.mpr (by
              have := le_abs_self (Real.log Wp)
              have := hxpow (C + 1); linarith)
    have hlog : Real.log (max Bt Wp) ≤ x ^ (C + 1) / 2 + |Real.log Wp| := by
      rw [← Real.exp_le_exp, Real.exp_log (by positivity)]; exact hmax
    rw [hH_def, Real.log_pow]
    have h1 : 6 * (x ^ (C + 1) / 2 + |Real.log Wp|) ≤ L := by
      have h2 : (3 + 6 * |Real.log Wp|) * x ^ (C + 1) ≤ x * x ^ (C + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have h3 : x * x ^ (C + 1) = L := by rw [hL_def]; ring
      have h4 := hxpow (C + 1)
      nlinarith only [abs_nonneg (Real.log Wp), hxW, hxL, h3]
    push_cast
    nlinarith only [hlog, h1]
  -- the stagger cells
  have hsz : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ l,
      eLpNorm (stagTuple f g u t I l) 2
        (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
          ENNReal.ofReal 2 := by
    intro I hI hIH l
    obtain ⟨D, ha₀, hr, -, -, hfD, hgD, -, -, -, -, hszD⟩ := hcells I hI hIH
    have := hszD u t l
    rw [StaggerCell.tuple_eq_stagTuple D hfD hgD] at this
    change eLpNorm _ 2 (normalizedIntervalMeasure D.a₀ D.r) ≤ 2 at this
    rw [ha₀, hr] at this
    rw [ENNReal.ofReal_ofNat]
    exact this
  -- the parameters
  have hL0 : 0 ≤ L := by linarith
  have hBp : 1 ≤ L ^ 2 := one_le_pow₀ hL1
  have hε0 : 0 < Real.exp (-(L ^ (d + 2))) := Real.exp_pos _
  have hε1 : Real.exp (-(L ^ (d + 2))) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := pow_nonneg hL0 (d + 2); linarith)
  have hka : 1 ≤ ⌈L ^ 2⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hkb : 1 ≤ ⌈L ^ s⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; have := one_le_pow₀ (n := s) hL1; linarith)
  have hMa : 16 * fitBudget Cqa Ca ⌈L ^ 2⌉₊ ^ 2 < (⌊16 * fitBudget Cqa Ca ⌈L ^ 2⌉₊ ^ 2⌋₊ + 1 :
      ℕ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hMb : 16 * fitBudget Cqa Ca ⌈L ^ s⌉₊ ^ 2 < (⌊16 * fitBudget Cqa Ca ⌈L ^ s⌉₊ ^ 2⌋₊ + 1 :
      ℕ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hbase := hbt' w hw f hfm hfq (Bf := fun ℓ => fitBudget Cq C (stagAcc k₁ A ℓ))
    (kk := fun ℓ => stagAcc k₁ A ℓ) hfit hu hut hpos (Hc := Bt) (Mt := Mt) hBf hMℓ
    (le_trans (Real.exp_pos _).le hη₀e) hpair hsz (L ^ 2) (Real.exp (-(L ^ (d + 2))))
    ⌈L ^ (d + 1)⌉₊ ⌈L ^ 2⌉₊
    ⌈L ^ s⌉₊ (⌊16 * fitBudget Cqa Ca ⌈L ^ 2⌉₊ ^ 2⌋₊ + 1)
    (⌊16 * fitBudget Cqa Ca ⌈L ^ s⌉₊ ^ 2⌋₊ + 1) hBp hε0 hε1 hka hkb hMa hMb
  dsimp only at hbase
  obtain ⟨ι, hι, B, hpack, hdisj, hB, hsum⟩ := hbase
  obtain ⟨hErr, hPair, hDb, hKb, hDcb, hcardb, hBab, hBbb⟩ := hP Mt H hMtL hH1 hHL
  -- the exponent comparisons
  have hLS : L ^ S ≤ x ^ (2 * ((C + 2) * S) + 2) := by
    rw [hL_def, ← pow_mul]
    exact pow_le_pow_right₀ hx1 (by generalize (C + 2) * S = m; omega)
  have hLS2 : (L ^ S) ^ 2 ≤ x ^ (2 * ((C + 2) * S) + 2) := by
    have e : (L ^ S) ^ 2 = x ^ (2 * ((C + 2) * S)) := by
      rw [hL_def, ← pow_mul, ← pow_mul]; ring_nf
    rw [e]
    exact pow_le_pow_right₀ hx1 (Nat.le_add_right _ _)
  have hηL : Real.exp (-L) ≤ η₀ := by
    refine le_trans ?_ hη₀e
    apply Real.exp_le_exp.mpr
    have h1 : (k : ℝ) ^ θ₀ ≤ x := by
      have := Real.rpow_le_rpow_of_exponent_le hx1 hθ₁
      rwa [Real.rpow_one] at this
    have h2 : 2 * x ≤ L := by
      have : x ^ 2 ≤ L := pow_le_pow_right₀ hx1 (by omega)
      have h5 : 2 * x ≤ x ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith only [hx16]) hx0
      linarith only [this, h5]
    linarith only [h1, h2]
  have hxk : Real.exp (-L) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by
    rw [← hx_def]; linarith only [hxL])
  have hη0 : 0 ≤ η₀ := le_trans (Real.exp_pos _).le hη₀e
  have hK2 : ((⌈L ^ (d + 1)⌉₊ : ℕ) : ℝ) ^ 2 ≤ x ^ (2 * ((C + 2) * S) + 2) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hKb 2).trans hLS2
  refine ⟨ι, hι, B, hpack, hdisj, fun p => ?_, ?_⟩
  · obtain ⟨hcellsT, hcellsH, hanc, hG, hw', hR, hH', hDc, hS, hη, hcard, hpairs, hsize, hside,
      htwo, hcol⟩ := hB p
    have hexp : Real.exp (L ^ S) ≤ Real.exp (x ^ (2 * ((C + 2) * S) + 2)) :=
      Real.exp_le_exp.mpr hLS
    refine ⟨hcellsT, hcellsH, hanc, hG, hw', hR, ?_, ?_, ?_, ?_, hS, hη, ?_, hsize, ?_, ?_,
      hcol.1, hcol.2.mono hη0 hK2⟩
    · rw [hH']; exact le_trans hH1 (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [hH']; exact (max_le hDb (max_le hBab hBbb)).trans hexp
    · rw [hDc]; exact hDcb.trans hexp
    · have h1 := (Nat.cast_le (α := ℝ)).mpr hcard
      refine h1.trans (le_trans (le_of_eq ?_) (hcardb.trans hexp))
      push_cast; ring
    · intro I hI s' s'' hss
      refine (hpairs I hI s' s'' hss).mono ?_
      have := hPair
      linarith only [hPair, hηL]
    · intro l
      refine (hside l).trans ?_
      exact mul_le_mul_of_nonneg_right hK2 (dyadicGridLength_pos G _).le
    · refine htwo.trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2
        (dyadicGridLength_pos G _).le) hη0
  · refine hsum.trans ?_
    have hJ := (dyadicGridLength_pos G J.1).le
    have h1 := mul_le_mul_of_nonneg_right (hErr.trans hxk) (by positivity :
      (0 : ℝ) ≤ 91 / 3 * dyadicGridLength G J.1)
    linarith only [h1]

/-- Blueprint prop:base, line 1643 ("for the finitely many initial levels omit `η`"): every pair
of measurable arguments of normalized `L²` size at most two is `4 C_κ`-small, by the four-`L²`
case of `eq:absolute`. -/
theorem pairSmall_trivial {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {p p' : Fin 4} (hpp : p ≠ p')
    {X Y : ℝ → ℂ} (hX : Measurable X) (hY : Measurable Y)
    (hXn : eLpNorm X 2 (normalizedIntervalMeasure a₀ r) ≤ 2)
    (hYn : eLpNorm Y 2 (normalizedIntervalMeasure a₀ r) ≤ 2) :
    PairSmall a₀ r w p p' X Y (4 * localFormUniformConstant κ) := by
  intro z hz hzn
  obtain ⟨c, d, hcd, hcp, hcp', hdp, hdp', -⟩ := fin4_other_two p p' hpp
  have h := localProgressionForm_enorm_le_slots hr hw (slotPair z p p' X Y)
    (slotPair_meas hz hX hY) hpp hcp.symm hdp.symm hcp'.symm hdp'.symm hcd 2 2 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [slotPair_left hpp, slotPair_right, slotPair_other hcp hcp', slotPair_other hdp hdp'] at h
  have hb : eLpNorm X 2 (normalizedIntervalMeasure a₀ r) * eLpNorm Y 2
      (normalizedIntervalMeasure a₀ r) * eLpNorm (z c) 2 (normalizedIntervalMeasure a₀ r) *
        eLpNorm (z d) 2 (normalizedIntervalMeasure a₀ r) ≤ 2 * 2 * 1 * 1 := by
    gcongr
    · exact hzn c hcp hcp'
    · exact hzn d hdp hdp'
  have hC := localFormUniformConstant_nonneg κ
  have h2 : ‖localProgressionForm r w (slotPair z p p' X Y)‖ₑ ≤
      ENNReal.ofReal (4 * localFormUniformConstant κ) := by
    refine h.trans ?_
    calc ENNReal.ofReal (localFormUniformConstant κ) * _ ≤
        ENNReal.ofReal (localFormUniformConstant κ) * (2 * 2 * 1 * 1) := by gcongr
      _ = ENNReal.ofReal (4 * localFormUniformConstant κ) := by
          rw [ENNReal.ofReal_mul (by norm_num)]; norm_num; ring
  rw [← ofReal_norm] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2

namespace ActiveSetup

open scoped Classical in
/-- Blueprint prop:base, line 1655 ("the finitely many initial levels have fixed budgets and so a
depth-independent bound"): on an active setup with `|H_I(Y)| ≤ η`, the length-weighted sum of
`|H_I(Y)|` is at most the two-`U` term plus `|R|` times `3 η` times the active path
multiplicity at `δ = 1/2` plus the inactive error at `δ = 1/2`. -/
theorem total_le (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (C Ca : ℕ) (Cr : ℝ), 0 ≤ Cr ∧ ∀ A : ActiveSetup κ c₀, 0 ≤ A.η →
      ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.Y I)‖ ≤
        ∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.z 3 I)‖ +
          dyadicGridLength A.G A.R.1 * (3 * A.η * (4 * Fintype.card A.L ^ 3 *
            (Ca * (216 * Real.log (chartTranslationBudget A.H) + Real.log (sliceConst κ) +
              2 * Real.log 2) ^ Ca)) +
          3 * Fintype.card A.L ^ 3 * (A.Dc ^ 3 * (A.S + Fintype.card A.L * A.Dc)) *
            (1 / 2 * Cr * (Real.log (chartTranslationBudget A.H) + Real.log 2 + 1) ^ C)) := by
  obtain ⟨C, Cr, hCr, hred⟩ := reduction κ c₀ hc
  obtain ⟨Ca, -, hcnt⟩ := active_count κ c₀ hc
  refine ⟨C, Ca, Cr, hCr, fun A hη => ?_⟩
  have h := hred A (1 / 2) (by norm_num) (by norm_num) hη
  have hinv : Real.log ((1 : ℝ) / 2)⁻¹ = Real.log 2 := by norm_num
  rw [hinv] at h
  set M : ℝ := 4 * Fintype.card A.L ^ 3 * (Ca * (216 * Real.log (chartTranslationBudget A.H) +
    Real.log (sliceConst κ) + 2 * Real.log 2) ^ Ca)
  have hact : ∀ p : Fin 3, ∑ I ∈ A.cells with A.active (1 / 2) I,
      dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ ≤
        dyadicGridLength A.G A.R.1 * (A.η * M) := by
    intro p
    have hsub : ∀ I ∈ A.cells.filter (A.active (1 / 2)),
        dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 :=
      fun I hI => A.sub I (Finset.mem_filter.mp hI).1
    refine (Finset.sum_le_sum fun I _ => mul_le_mul_of_nonneg_left (min_le_left _ _)
      (dyadicGridLength_pos A.G I.1).le).trans ?_
    refine cells_sum_le_of_path A.G A.R _ hsub (fun _ => hη) fun y => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hη
    have := hcnt A (1 / 2) (by norm_num) (by norm_num) y
    rw [hinv] at this
    refine le_trans (le_of_eq ?_) this
    congr 2
    ext I
    simp only [Finset.mem_filter]
    tauto
  have hsum : ∑ p : Fin 3, ∑ I ∈ A.cells with A.active (1 / 2) I,
      dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ ≤
        dyadicGridLength A.G A.R.1 * (3 * A.η * M) := by
    refine (Finset.sum_le_sum fun p _ => hact p).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  refine h.trans ?_
  have := add_le_add_right (add_le_add_right hsum
    (∑ I ∈ A.cells, dyadicGridLength A.G I.1 * ‖A.Hf I (A.z 3 I)‖))
    (3 * Fintype.card A.L ^ 3 * (A.Dc ^ 3 * (A.S + Fintype.card A.L * A.Dc)) *
      (dyadicGridLength A.G A.R.1 * (1 / 2 * Cr * (Real.log (chartTranslationBudget A.H) +
        Real.log 2 + 1) ^ C)))
  linarith only [hsum]

end ActiveSetup

theorem log_chartTranslationBudget_le {H E : ℝ} (hH : 1 ≤ H) (hHE : H ≤ E) :
    0 ≤ Real.log (chartTranslationBudget H) ∧
      Real.log (chartTranslationBudget H) ≤ 100 * (1 + Real.log E) ^ 3 := by
  unfold chartTranslationBudget logarithmicSize
  rw [Real.log_exp]
  have h0 : 0 ≤ Real.log H := Real.log_nonneg hH
  have h1 : Real.log H ≤ Real.log E := Real.log_le_log (by linarith) hHE
  constructor
  · positivity
  · gcongr

/-- Blueprint prop:base, line 1655, summed over a family of active setups with budgets at most
`E`, `S = 2`, `η = 4 η₀`, two-`U` terms at most `η₀ X |R|` and roots of total length at most
`W`: the length-weighted sum of `|H_I(Y)|` over all setups is at most `W` times an explicit
function of `E, η₀, X` (no dependence on the depth). -/
theorem setups_total_le (κ : LocalKernelClass) (c₀ : ℕ) (hc : 1 ≤ c₀) :
    ∃ (C Ca : ℕ) (Cr : ℝ), 0 ≤ Cr ∧ ∀ {ι : Type} [Fintype ι] (B : ι → ActiveSetup κ c₀)
      {E η₀ X W : ℝ}, 1 ≤ E → 0 ≤ η₀ → 0 ≤ X →
      (∀ p, 1 ≤ (B p).H ∧ (B p).H ≤ E ∧ (B p).Dc ≤ E ∧ (Fintype.card (B p).L : ℝ) ≤ E ∧
        (B p).S = 2 ∧ (B p).η = 4 * η₀ ∧
        ∑ I ∈ (B p).cells, dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).z 3 I)‖ ≤
          η₀ * (X * dyadicGridLength (B p).G (B p).R.1)) →
      ∑ p, dyadicGridLength (B p).G (B p).R.1 ≤ W →
      ∑ p, ∑ I ∈ (B p).cells, dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).Y I)‖ ≤
        W * (η₀ * X + 3 * (4 * η₀) * (4 * E ^ 3 * (Ca * (216 * (100 * (1 + Real.log E) ^ 3) +
          Real.log (sliceConst κ) + 2 * Real.log 2) ^ Ca)) +
          3 * E ^ 3 * (E ^ 3 * (2 + E * E)) *
            (1 / 2 * Cr * (100 * (1 + Real.log E) ^ 3 + Real.log 2 + 1) ^ C)) := by
  obtain ⟨C, Ca, Cr, hCr, htot⟩ := ActiveSetup.total_le κ c₀ hc
  refine ⟨C, Ca, Cr, hCr, fun {ι} _ B E η₀ X W hE hη₀ hX hB hW => ?_⟩
  set Φ := η₀ * X + 3 * (4 * η₀) * (4 * E ^ 3 * (Ca * (216 * (100 * (1 + Real.log E) ^ 3) +
    Real.log (sliceConst κ) + 2 * Real.log 2) ^ Ca)) +
    3 * E ^ 3 * (E ^ 3 * (2 + E * E)) *
      (1 / 2 * Cr * (100 * (1 + Real.log E) ^ 3 + Real.log 2 + 1) ^ C) with hΦ
  have hlogE : 0 ≤ Real.log E := Real.log_nonneg hE
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hls : 0 ≤ Real.log (sliceConst κ) := Real.log_nonneg (one_le_sliceConst κ)
  have hΦ0 : 0 ≤ Φ := by positivity
  have hp : ∀ p, ∑ I ∈ (B p).cells, dyadicGridLength (B p).G I.1 * ‖(B p).Hf I ((B p).Y I)‖ ≤
      dyadicGridLength (B p).G (B p).R.1 * Φ := by
    intro p
    obtain ⟨hH1, hHE, hDc, hL, hS, hη, htwo⟩ := hB p
    have hηp : 0 ≤ (B p).η := by rw [hη]; positivity
    have h := htot (B p) hηp
    obtain ⟨hc0, hcE⟩ := log_chartTranslationBudget_le hH1 hHE
    have hR := (dyadicGridLength_pos (B p).G (B p).R.1).le
    have hDc0 := (B p).Dc_nonneg
    have hL0 : (0 : ℝ) ≤ Fintype.card (B p).L := Nat.cast_nonneg _
    refine h.trans ?_
    rw [hS, hη]
    have k1 : (4 : ℝ) * Fintype.card (B p).L ^ 3 * (Ca * (216 * Real.log (chartTranslationBudget
        (B p).H) + Real.log (sliceConst κ) + 2 * Real.log 2) ^ Ca) ≤
        4 * E ^ 3 * (Ca * (216 * (100 * (1 + Real.log E) ^ 3) + Real.log (sliceConst κ) +
          2 * Real.log 2) ^ Ca) := by
      gcongr
    have k2 : 3 * (Fintype.card (B p).L : ℝ) ^ 3 * ((B p).Dc ^ 3 * (2 + Fintype.card (B p).L *
        (B p).Dc)) * (1 / 2 * Cr * (Real.log (chartTranslationBudget (B p).H) + Real.log 2 + 1) ^
          C) ≤ 3 * E ^ 3 * (E ^ 3 * (2 + E * E)) *
            (1 / 2 * Cr * (100 * (1 + Real.log E) ^ 3 + Real.log 2 + 1) ^ C) := by
      gcongr
    have k3 : 0 ≤ 3 * (4 * η₀) := by positivity
    calc _ ≤ η₀ * (X * dyadicGridLength (B p).G (B p).R.1) +
          dyadicGridLength (B p).G (B p).R.1 * (3 * (4 * η₀) * (4 * E ^ 3 *
            (Ca * (216 * (100 * (1 + Real.log E) ^ 3) + Real.log (sliceConst κ) +
              2 * Real.log 2) ^ Ca)) + 3 * E ^ 3 * (E ^ 3 * (2 + E * E)) *
                (1 / 2 * Cr * (100 * (1 + Real.log E) ^ 3 + Real.log 2 + 1) ^ C)) := by
          gcongr
      _ = _ := by rw [hΦ]; ring
  calc _ ≤ ∑ p, dyadicGridLength (B p).G (B p).R.1 * Φ := Finset.sum_le_sum fun p _ => hp p
    _ = (∑ p, dyadicGridLength (B p).G (B p).R.1) * Φ := by rw [Finset.sum_mul]
    _ ≤ W * Φ := mul_le_mul_of_nonneg_right hW hΦ0

end TrilinearHT.Auto

end
