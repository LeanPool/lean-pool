/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec131OneExpansionAtFirstMatch.Setup

/-!
# Trilinear Hilbert transform: chooseSchedule
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
section ModeSchedule

open scoped Classical in
private def ChooseScheduleHlogXHStatement : Prop :=
  ∀ (Cj : ℕ)
    (CA : ℕ)
    (δs : ℝ)
    (_ : (0 : ℝ) < δs),
  let cJ : ℝ :=
    (1262 : ℝ) * (↑Cj : ℝ) * δs⁻¹ ^ (2 : ℕ) + (1 : ℝ)
  let cA : ℝ :=
    (1564 : ℝ) * (↑CA : ℝ) + (1 : ℝ)
  let cX : ℝ :=
    cJ * cA + cA + (300 : ℝ) + (2 : ℝ) * cJ + (1003 : ℝ)
  ∀ (_ : cX = cJ * cA + cA + (300 : ℝ) + (2 : ℝ) * cJ + (1003 : ℝ))
    (_ : (1 : ℝ) ≤ cJ)
    (dmax : ℕ)
    (Dstar : ℝ)
    (Bstar : ℝ)
    (Q0 : ℕ)
    (_ : (2 : ℕ) ≤ dmax)
    (_ : (2 : ℝ) ≤ Dstar)
    (_ : (2 : ℝ) ≤ Bstar)
    (_ : (1 : ℕ) ≤ Q0)
    (Λ : ℝ),
  let d : ℝ :=
    (↑dmax : ℝ)
  ∀ (_ : (2 : ℝ) ≤ d)
    (_ : (1 : ℝ) ≤ Λ)
    (_ : Real.log Dstar ≤ Λ)
    (_ : Real.log Bstar ≤ Λ)
    (_ : Real.log (↑Q0 : ℝ) ≤ Λ)
    (_ : Real.log d ≤ Λ)
    (_ : ∀ (a b : ℕ), a ≤ b → Λ ^ a ≤ Λ ^ b)
    (_ : Real.log (6 : ℝ) ≤ (2 : ℝ))
    (Cs : ℝ)
    (_ : (1 : ℝ) ≤ Cs)
    (_ : Real.log Cs ≤ (300 : ℝ) * Λ ^ (5 : ℕ))
    (J : ℕ)
    (_ : (↑J : ℝ) ≤ cJ * Λ ^ (7 : ℕ))
    (A : ℝ)
    (_ : (1 : ℝ) ≤ A)
    (_ : Real.log A ≤ cA * Λ ^ (5 : ℕ))
    (_ : (0 : ℝ) ≤ Real.log A),
  let XH : ℝ :=
    d * Cs * A ^ (J + (1 : ℕ)) * Bstar * (6 : ℝ) ^ J * (↑Q0 : ℝ) * Dstar ^ (1000 : ℕ)
  ∀ (_ : XH = d * Cs * A ^ (J + (1 : ℕ)) * Bstar * (6 : ℝ) ^ J * (↑Q0 : ℝ) * Dstar ^ (1000 :
      ℕ)),
  Real.log XH ≤ cX * Λ ^ (12 : ℕ)


open scoped Classical in
private def ChooseScheduleHlogTStatement : Prop :=
  ∀ (Cj : ℕ)
    (CA : ℕ)
    (CT : ℕ)
    (δs : ℝ),
  let cJ : ℝ :=
    (1262 : ℝ) * (↑Cj : ℝ) * δs⁻¹ ^ (2 : ℕ) + (1 : ℝ)
  let cA : ℝ :=
    (1564 : ℝ) * (↑CA : ℝ) + (1 : ℝ)
  let cX : ℝ :=
    cJ * cA + cA + (300 : ℝ) + (2 : ℝ) * cJ + (1003 : ℝ)
  let cH : ℝ :=
    (10 : ℝ) * cX + (1 : ℝ)
  let cT : ℝ :=
    (↑CT : ℝ) * ((1 : ℝ) + cH) + (1001 : ℝ)
  ∀ (_ : cT = (↑CT : ℝ) * ((1 : ℝ) + cH) + (1001 : ℝ))
    (dmax : ℕ)
    (Dstar : ℝ)
    (_ : (2 : ℕ) ≤ dmax)
    (_ : (2 : ℝ) ≤ Dstar)
    (Λ : ℝ),
  let d : ℝ :=
    (↑dmax : ℝ)
  ∀ (_ : (2 : ℝ) ≤ d)
    (_ : Real.log (2 : ℝ) ≤ Real.log Dstar)
    (_ : (1 : ℝ) ≤ Λ)
    (_ : d ≤ Λ)
    (_ : Real.log Dstar ≤ Λ)
    (_ : Real.log d ≤ Λ)
    (Hv : ℝ)
    (_ : (1 : ℝ) ≤ Hv)
    (_ : Real.log Hv ≤ cH * Λ ^ (12 : ℕ)),
  let Tv : ℝ :=
    (d * Hv) ^ (CT * dmax ^ (4 : ℕ)) * Dstar ^ (1000 : ℕ) + (1 : ℝ)
  ∀ (_ : Tv = (d * Hv) ^ (CT * dmax ^ (4 : ℕ)) * Dstar ^ (1000 : ℕ) + (1 : ℝ))
    (_ : (1 : ℝ) ≤ (d * Hv) ^ (CT * dmax ^ (4 : ℕ)) * Dstar ^ (1000 : ℕ)),
  Real.log Tv ≤ cT * Λ ^ (16 : ℕ)


open scoped Classical in
private def ChooseScheduleStage1Statement : Prop :=
  ∀ (Cj : ℕ)
    (CA : ℕ)
    (CT : ℕ)
    (CK : ℕ)
    (δs : ℝ)
    (_ : (0 : ℝ) < δs),
  let cJ : ℝ :=
    (1262 : ℝ) * (↑Cj : ℝ) * δs⁻¹ ^ (2 : ℕ) + (1 : ℝ)
  let cA : ℝ :=
    (1564 : ℝ) * (↑CA : ℝ) + (1 : ℝ)
  let cX : ℝ :=
    cJ * cA + cA + (300 : ℝ) + (2 : ℝ) * cJ + (1003 : ℝ)
  ∀ (_ : cX = cJ * cA + cA + (300 : ℝ) + (2 : ℝ) * cJ + (1003 : ℝ)),
  let cH : ℝ :=
    (10 : ℝ) * cX + (1 : ℝ)
  ∀ (_ : cH = (10 : ℝ) * cX + (1 : ℝ)),
  let cT : ℝ :=
    (↑CT : ℝ) * ((1 : ℝ) + cH) + (1001 : ℝ)
  ∀ (_ : cT = (↑CT : ℝ) * ((1 : ℝ) + cH) + (1001 : ℝ))
    (_ : (1 : ℝ) ≤ cJ)
    (_ : (0 : ℝ) ≤ cX)
    (_ : (0 : ℝ) ≤ cT)
    (dmax : ℕ)
    (Dstar : ℝ)
    (Bstar : ℝ)
    (Dm : ℝ)
    (Wf : ℝ → ℝ)
    (Q0 : ℕ)
    (_ : (2 : ℕ) ≤ dmax)
    (_ : (2 : ℝ) ≤ Dstar)
    (_ : (2 : ℝ) ≤ Bstar)
    (_ : (1 : ℕ) ≤ Q0)
    (_ : ∀ (y : ℝ), (0 : ℝ) ≤ Wf y)
    (Λ : ℝ),
  let d : ℝ :=
    (↑dmax : ℝ)
  ∀ (_ : (2 : ℝ) ≤ d)
    (_ : Real.log (2 : ℝ) ≤ Real.log Dstar)
    (_ : (1 : ℝ) ≤ Λ)
    (_ : d ≤ Λ)
    (_ : Real.log Dstar ≤ Λ)
    (_ : Real.log Bstar ≤ Λ)
    (_ : Real.log (↑Q0 : ℝ) ≤ Λ)
    (_ : Real.log d ≤ Λ)
    (_ : ∀ (a b : ℕ), a ≤ b → Λ ^ a ≤ Λ ^ b)
    (_ : Real.log (6 : ℝ) ≤ (2 : ℝ))
    (Cs : ℝ)
    (_ : Cs = ((10 : ℝ) * d * Dstar) ^ ((100 : ℕ) * dmax ^ (4 : ℕ)))
    (_ : (1 : ℝ) ≤ Cs)
    (_ : Real.log Cs ≤ (300 : ℝ) * Λ ^ (5 : ℕ))
    (Rh : ℕ)
    (_ : Rh = ⌈Real.logb (2 : ℝ) Cs⌉₊ + (30 : ℕ))
    (J : ℕ)
    (_ : J = ⌈(↑Cj : ℝ) * δs⁻¹ ^ (2 : ℕ) * d * (↑Rh : ℝ) * Real.log ((2 : ℝ) * Dm)⌉₊)
    (_ : (↑J : ℝ) ≤ cJ * Λ ^ (7 : ℕ)),
  let A : ℝ :=
    (Cs * (6 : ℝ) ^ Rh * Bstar * Dstar) ^ CA
  ∀ (_ : A = (Cs * (6 : ℝ) ^ Rh * Bstar * Dstar) ^ CA)
    (_ : (1 : ℝ) ≤ A)
    (_ : Real.log A ≤ cA * Λ ^ (5 : ℕ)),
  ∃ (S : ModeSchedule), S.dmax = dmax ∧ S.Dstar = Dstar ∧ S.Bstar = Bstar ∧ S.Dm = Dm
    ∧ S.Q0 = Q0 ∧ S.Valid Cj CA CT CK δs (Wf S.H) ∧ Real.log S.H ≤ (cH + cT + ((8 : ℝ)
    * cT + (4 : ℝ) * (↑CK : ℝ) + (2 : ℝ))) * Λ ^ (12 : ℕ) ∧ Real.log S.T ≤ (cH + cT +
    ((8 : ℝ) * cT + (4 : ℝ) * (↑CK : ℝ) + (2 : ℝ))) * Λ ^ (16 : ℕ) ∧ (↑S.K : ℝ) ≤ (2 :
    ℝ) * Wf S.H + (cH + cT + ((8 : ℝ) * cT + (4 : ℝ) * (↑CK : ℝ) + (2 : ℝ))) * Λ ^ (16
    : ℕ)




private theorem chooseSchedule_hlogXH : ChooseScheduleHlogXHStatement := by
  classical
  intro Cj CA δs hδs cJ cA cX hcX hcJ0 dmax Dstar Bstar Q0 hd hD hB hQ Λ d hd2 hΛ1 hlDΛ hlBΛ hlQΛ
    hldΛ hpow hl6 Cs hCs1 hlogCs J hJb A hA1 hlogA hlogA0 XH hXH
  rw [hXH, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by linarith) (by linarith), Real.log_pow, Real.log_pow, Real.log_pow]
  have e1 : ((J + 1 : ℕ) : ℝ) * Real.log A ≤ (cJ * Λ ^ 7 + 1) * (cA * Λ ^ 5) := by
    push_cast
    exact mul_le_mul (by linarith) hlogA hlogA0 (by positivity)
  have e2 : (J : ℝ) * Real.log 6 ≤ cJ * Λ ^ 7 * 2 :=
    mul_le_mul hJb hl6 (Real.log_nonneg (by norm_num)) (by positivity)
  have e3 : ((1000 : ℕ) : ℝ) * Real.log Dstar ≤ 1000 * Λ := by
    push_cast; linarith
  have hΛ12 := hpow 1 12 (by norm_num); have hΛ5 := hpow 5 12 (by norm_num)
  have hΛ7 := hpow 7 12 (by norm_num)
  simp only [pow_one] at hΛ12
  have hexp : (cJ * Λ ^ 7 + 1) * (cA * Λ ^ 5) = cJ * cA * Λ ^ 12 + cA * Λ ^ 5 := by ring
  have hcJA : 0 ≤ cJ * cA := by positivity
  have hcA5 : cA * Λ ^ 5 ≤ cA * Λ ^ 12 := mul_le_mul_of_nonneg_left hΛ5 (by positivity)
  have hcJ7 : cJ * Λ ^ 7 ≤ cJ * Λ ^ 12 := mul_le_mul_of_nonneg_left hΛ7 (by linarith)
  have hl300 : 300 * Λ ^ 5 ≤ 300 * Λ ^ 12 := by linarith
  have hsplitX : (cJ * cA + cA + 300 + 2 * cJ + 1003) * Λ ^ 12 = cJ * cA * Λ ^ 12 +
      cA * Λ ^ 12 + 300 * Λ ^ 12 + 2 * (cJ * Λ ^ 12) + 1003 * Λ ^ 12 := by ring
  have hlin : Λ + Λ + Λ + 1000 * Λ ≤ 1003 * Λ ^ 12 := by linarith
  rw [hcX, hsplitX]
  linarith



private theorem chooseSchedule_hlogT : ChooseScheduleHlogTStatement := by
  classical
  intro Cj CA CT δs cJ cA cX cH cT hcT dmax Dstar hd hD Λ d hd2 hlD hΛ1 hdΛ hlDΛ hldΛ Hv hHv1
    hlogH Tv hTv hX1
  have h1 : Tv ≤ 2 * ((d * Hv) ^ (CT * dmax ^ 4) * Dstar ^ 1000) := by rw [hTv]; linarith
  have h2 := Real.log_le_log (by linarith) h1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_mul (by linarith) (by linarith)] at h2
  have hC4 : ((CT * dmax ^ 4 : ℕ) : ℝ) ≤ CT * Λ ^ 4 := by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hdΛ 4) (Nat.cast_nonneg _)
  have hΛ12 : Λ ≤ Λ ^ 12 := le_self_pow₀ hΛ1 (by norm_num)
  have hin : Real.log d + Real.log Hv ≤ (1 + cH) * Λ ^ 12 := by
    rw [show (1 + cH) * Λ ^ 12 = Λ ^ 12 + cH * Λ ^ 12 by ring]; linarith
  have hin0 : 0 ≤ Real.log d + Real.log Hv := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ d); have := Real.log_nonneg hHv1
    linarith
  have e1 : ((CT * dmax ^ 4 : ℕ) : ℝ) * (Real.log d + Real.log Hv) ≤
      (CT * Λ ^ 4) * ((1 + cH) * Λ ^ 12) := mul_le_mul hC4 hin hin0 (by positivity)
  have e2 : ((1000 : ℕ) : ℝ) * Real.log Dstar ≤ 1000 * Λ := by push_cast; linarith
  have h16 : Λ ≤ Λ ^ 16 := le_self_pow₀ hΛ1 (by norm_num)
  have h16' : (1 : ℝ) ≤ Λ ^ 16 := one_le_pow₀ hΛ1
  have hexp : (CT * Λ ^ 4) * ((1 + cH) * Λ ^ 12) = CT * (1 + cH) * Λ ^ 16 := by ring
  have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hsplitT : (CT * (1 + cH) + 1001) * Λ ^ 16 = CT * (1 + cH) * Λ ^ 16 + 1001 * Λ ^ 16 := by
    ring
  rw [hcT, hsplitT]
  linarith



private theorem chooseSchedule_stage_1 : ChooseScheduleStage1Statement := by
  classical
  intro Cj CA CT CK δs hδs cJ cA cX hcX cH hcH cT hcT hcJ0 hcX0 hcT0 dmax Dstar Bstar Dm Wf Q0 hd
    hD hB hQ hWf Λ d hd2 hlD hΛ1 hdΛ hlDΛ hlBΛ hlQΛ hldΛ hpow hl6 Cs hCs hCs1 hlogCs Rh hRh J hJ
    hJb A hA hA1 hlogA
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  clear_value A
  set! XH : ℝ := d * Cs * A ^ (J + 1) * Bstar * 6 ^ J * Q0 * Dstar ^ 1000 with hXH
  have hQ1 : (1 : ℝ) ≤ Q0 := by exact_mod_cast hQ
  have hXH1 : 1 ≤ XH := by
    have h1 : 1 ≤ A ^ (J + 1) := one_le_pow₀ hA1
    have h2 : (1 : ℝ) ≤ 6 ^ J := one_le_pow₀ (by norm_num)
    have h3 : (1 : ℝ) ≤ Dstar ^ 1000 := one_le_pow₀ (by linarith)
    have g1 : (1 : ℝ) ≤ d * Cs := one_le_mul_of_one_le_of_one_le (by linarith) hCs1
    have g2 := one_le_mul_of_one_le_of_one_le g1 h1
    have g3 := one_le_mul_of_one_le_of_one_le g2 (by linarith : (1 : ℝ) ≤ Bstar)
    have g4 := one_le_mul_of_one_le_of_one_le g3 h2
    have g5 := one_le_mul_of_one_le_of_one_le g4 hQ1
    exact one_le_mul_of_one_le_of_one_le g5 h3
  have hlogXH : Real.log XH ≤ cX * Λ ^ 12 := by
    expose_names
    exact @chooseSchedule_hlogXH Cj CA δs hδs hcX hcJ0 dmax Dstar Bstar Q0 hd hD hB hQ Λ hd2 hΛ1
      hlDΛ hlBΛ hlQΛ hldΛ hpow hl6 Cs hCs1 hlogCs J hJb A hA1 hlogA hlogA0 hXH
  clear_value XH
  set! Hv : ℝ := XH ^ 10 + 1 with hHv
  have hHv1 : 1 ≤ Hv := by
    have : 0 ≤ XH ^ 10 := by positivity
    linarith
  have hlogH : Real.log Hv ≤ cH * Λ ^ 12 := by
    have h1 : Hv ≤ 2 * XH ^ 10 := by
      have : 1 ≤ XH ^ 10 := one_le_pow₀ hXH1
      rw [hHv]; linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
    have h12 : (1 : ℝ) ≤ Λ ^ 12 := one_le_pow₀ hΛ1
    have hl2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hsplitH : (10 * cX + 1) * Λ ^ 12 = 10 * (cX * Λ ^ 12) + Λ ^ 12 := by ring
    rw [hcH, hsplitH]; push_cast at h2; linarith
  clear_value Hv
  set! Tv : ℝ := (d * Hv) ^ (CT * dmax ^ 4) * Dstar ^ 1000 + 1 with hTv
  have hX1 : 1 ≤ (d * Hv) ^ (CT * dmax ^ 4) * Dstar ^ 1000 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by nlinarith only [hd2,
        hHv1])) (one_le_pow₀ (by linarith))
  have hTv1 : 1 ≤ Tv := by rw [hTv]; linarith
  have hlogT : Real.log Tv ≤ cT * Λ ^ 16 := by
    expose_names
    exact @chooseSchedule_hlogT Cj CA CT δs hcT dmax Dstar hd hD Λ hd2 hlD hΛ1 hdΛ hlDΛ hldΛ Hv
      hHv1 hlogH hTv hX1
  clear_value Tv
  have hW := hWf Hv
  set! x : ℝ := Wf Hv + 2 * Real.logb 2 Tv + CK * Real.logb 2 Dstar + 1 with hx
  have hx1 : 1 ≤ x := by
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hTv1
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith : (1 : ℝ) ≤ Dstar)
    have : (0 : ℝ) ≤ CK * Real.logb 2 Dstar := by positivity
    rw [hx]; linarith
  set! κ : ℕ := ⌈Real.logb 2 x⌉₊ with hκ
  have hxpow : x = (2 : ℝ) ^ (Real.logb 2 x) :=
    (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
  have hK1 : x ≤ (2 : ℝ) ^ κ := by
    rw [← Real.rpow_natCast]
    calc x = (2 : ℝ) ^ (Real.logb 2 x) := hxpow
      _ ≤ (2 : ℝ) ^ (κ : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have hK2 : (2 : ℝ) ^ κ ≤ 2 * x := by
    have hlx : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
    have h1 := Nat.ceil_lt_add_one hlx
    rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (κ : ℝ) ≤ 2 ^ (Real.logb 2 x + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
      _ = 2 * x := by
          rw [Real.rpow_add (by norm_num), ← hxpow, Real.rpow_one]; ring
  refine ⟨⟨dmax, Dstar, Bstar, Dm, Q0, Cs, Rh, J, A, Hv, Tv, 2 ^ κ⟩, rfl, rfl, rfl, rfl, rfl,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨κ, rfl⟩, ?_⟩,
    hlogH.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)),
    hlogT.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity)), ?_⟩
  · change (10 * d * Dstar) ^ (100 * dmax ^ 4) ≤ Cs
    rw [hCs]
  · have h := Nat.le_ceil (Real.logb 2 Cs)
    change Real.logb 2 Cs + 30 ≤ (Rh : ℝ)
    rw [hRh]; push_cast; linarith
  · change (Cj : ℝ) * δs⁻¹ ^ 2 * d * Rh * Real.log (2 * Dm) ≤ J
    rw [hJ]; exact Nat.le_ceil _
  · change (Cs * 6 ^ Rh * Bstar * Dstar) ^ CA ≤ A
    rw [hA]
  · change (d * Cs * A ^ (J + 1) * Bstar * 6 ^ J * Q0 * Dstar ^ 1000) ^ 10 < Hv
    rw [hHv, ← hXH]; linarith
  · change (d * Hv) ^ (CT * dmax ^ 4) * Dstar ^ 1000 < Tv
    rw [hTv]; linarith
  · push_cast
    rw [hx] at hK1
    linarith
  · push_cast
    have hlT : Real.logb 2 Tv ≤ 2 * Real.log Tv := logb_two_le_two_log hTv1
    have hlDb : Real.logb 2 Dstar ≤ 2 * Λ :=
      (logb_two_le_two_log (by linarith : (1 : ℝ) ≤ Dstar)).trans (by linarith)
    have h16 : Λ ≤ Λ ^ 16 := le_self_pow₀ hΛ1 (by norm_num)
    have h16' : (1 : ℝ) ≤ Λ ^ 16 := one_le_pow₀ hΛ1
    have hCK : (CK : ℝ) * Real.logb 2 Dstar ≤ CK * (2 * Λ ^ 16) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ cH * Λ ^ 12 := by positivity
    have : (0 : ℝ) ≤ cT * Λ ^ 16 := by positivity
    rw [hx] at hK2
    have hsplitK : (cH + cT + (8 * cT + 4 * CK + 2)) * Λ ^ 16 = cH * Λ ^ 16 + 9 * (cT * Λ ^ 16) +
        4 * (CK * Λ ^ 16) + 2 * Λ ^ 16 := by ring
    have hT16 : 2 * Real.logb 2 Tv ≤ 4 * (cT * Λ ^ 16) := by linarith only [hlogT, hlT]
    have hK16 : (CK : ℝ) * Real.logb 2 Dstar ≤ 2 * (CK * Λ ^ 16) := by linarith
    have hcH16 : 0 ≤ cH * Λ ^ 16 := by positivity
    have hCK16 : 0 ≤ (CK : ℝ) * Λ ^ 16 := by positivity
    rw [hsplitK]
    linarith


/-- Blueprint `mode-schedule` (line 1976, `THT.Modes.chooseSchedule`): given the main budget
`D_m`, the dimension bound `d_max`, the mode budget `D_*`, the cutoff `B_*`, the clearing
integer `Q₀` and the packet width `W(H)` as a function of the height `H` (lem:height), the
parameters of `eq:mode-parameters` can be chosen in the displayed order (`K` last, using
`W(H)` at the chosen `H`), and all their logarithms are polynomial in
`Λ = d_max + log D_* + log B_* + log D_m + log Q₀ + 1`: `log H ≤ M Λ^{12}`,
`log T ≤ M Λ^{16}`, `K ≤ 2 W(H) + M Λ^{16}`, with `M` depending only on the absolute constants. -/
theorem chooseSchedule (Cj CA CT CK : ℕ) {δs : ℝ} (hδs : 0 < δs) (_hδs1 : δs ≤ 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ (dmax : ℕ) (Dstar Bstar Dm : ℝ) (Wf : ℝ → ℝ) (Q0 : ℕ), 2 ≤ dmax →
      2 ≤ Dstar → 2 ≤ Bstar → 2 ≤ Dm → 1 ≤ Q0 → (∀ y, 0 ≤ Wf y) →
      let Λ := (dmax : ℝ) + Real.log Dstar + Real.log Bstar + Real.log Dm + Real.log Q0 + 1
      ∃ S : ModeSchedule, S.dmax = dmax ∧ S.Dstar = Dstar ∧ S.Bstar = Bstar ∧ S.Dm = Dm ∧
        S.Q0 = Q0 ∧ S.Valid Cj CA CT CK δs (Wf S.H) ∧
        Real.log S.H ≤ M * Λ ^ 12 ∧ Real.log S.T ≤ M * Λ ^ 16 ∧
        (S.K : ℝ) ≤ 2 * Wf S.H + M * Λ ^ 16 := by
  -- the constants
  set cJ : ℝ := 1262 * Cj * (δs⁻¹) ^ 2 + 1 with hcJ
  set cA : ℝ := 1564 * CA + 1 with hcA
  set cX : ℝ := cJ * cA + cA + 300 + 2 * cJ + 1003 with hcX
  set cH : ℝ := 10 * cX + 1 with hcH
  set cT : ℝ := CT * (1 + cH) + 1001 with hcT
  have hcJ0 : 1 ≤ cJ := by
    rw [hcJ]; have : 0 ≤ 1262 * (Cj : ℝ) * (δs⁻¹) ^ 2 := by positivity
    linarith
  have hcA0 : 1 ≤ cA := by rw [hcA]; have : (0 : ℝ) ≤ CA := Nat.cast_nonneg _; linarith
  have hcX0 : 0 ≤ cX := by rw [hcX]; positivity
  have hcH0 : 0 ≤ cH := by rw [hcH]; positivity
  have hcT0 : 0 ≤ cT := by rw [hcT]; positivity
  refine ⟨cH + cT + (8 * cT + 4 * CK + 2), by positivity, ?_⟩
  intro dmax Dstar Bstar Dm Wf Q0 hd hD hB hM hQ hWf Λ
  set! d : ℝ := ((dmax : ℕ) : ℝ) with hdd
  have hd2 : (2 : ℝ) ≤ d := by rw [hdd]; exact_mod_cast hd
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlD : Real.log 2 ≤ Real.log Dstar := Real.log_le_log (by norm_num) hD
  have hlB : Real.log 2 ≤ Real.log Bstar := Real.log_le_log (by norm_num) hB
  have hlM : Real.log 2 ≤ Real.log Dm := Real.log_le_log (by norm_num) hM
  have hlQ : 0 ≤ Real.log Q0 := Real.log_nonneg (by exact_mod_cast hQ)
  have hΛ : d + 1 ≤ Λ := by simp only [Λ, hdd]; linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hdΛ : d ≤ Λ := by linarith
  have hlDΛ : Real.log Dstar ≤ Λ := by simp only [Λ]; linarith
  have hlBΛ : Real.log Bstar ≤ Λ := by simp only [Λ]; linarith
  have hlMΛ : Real.log Dm ≤ Λ := by simp only [Λ]; linarith
  have hlQΛ : Real.log Q0 ≤ Λ := by simp only [Λ]; linarith
  have hldΛ : Real.log d ≤ Λ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  clear_value Λ
  have hpow : ∀ a b : ℕ, a ≤ b → Λ ^ a ≤ Λ ^ b := fun a b h => pow_le_pow_right₀ hΛ1 h
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hl6 : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h2e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2e]
    calc (6 : ℝ) ≤ 2.7 ^ 2 := by norm_num
      _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he 2
  have hl10 : Real.log 10 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h3e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3e]
    calc (10 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he 3
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  -- the witnesses
  set! Cs : ℝ := (10 * d * Dstar) ^ (100 * dmax ^ 4) with hCs
  have hCs1 : 1 ≤ Cs := one_le_pow₀ (by nlinarith only [hD, hd2])
  have hlogCs : Real.log Cs ≤ 300 * Λ ^ 5 := by
    rw [hCs, Real.log_pow, Real.log_mul (by positivity) (by linarith),
      Real.log_mul (by norm_num) (by linarith)]
    have h1 : Real.log 10 + Real.log d + Real.log Dstar ≤ 3 * Λ := by linarith
    have h2 : ((100 * dmax ^ 4 : ℕ) : ℝ) ≤ 100 * Λ ^ 4 := by
      push_cast; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hdΛ 4)
        (by norm_num)
    have h0 : 0 ≤ Real.log 10 + Real.log d + Real.log Dstar := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ d)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 10)
      linarith
    calc ((100 * dmax ^ 4 : ℕ) : ℝ) * (Real.log 10 + Real.log d + Real.log Dstar) ≤
        (100 * Λ ^ 4) * (3 * Λ) := mul_le_mul h2 h1 h0 (by positivity)
      _ = 300 * Λ ^ 5 := by ring
  clear_value Cs
  set! Rh : ℕ := ⌈Real.logb 2 Cs⌉₊ + 30 with hRh
  have hRhb : (Rh : ℝ) ≤ 631 * Λ ^ 5 := by
    have h1 : Real.logb 2 Cs ≤ 2 * Real.log Cs := logb_two_le_two_log hCs1
    have h2 := (Nat.ceil_lt_add_one (Real.logb_nonneg (b := 2) (by norm_num) hCs1)).le
    have h5 : (1 : ℝ) ≤ Λ ^ 5 := one_le_pow₀ hΛ1
    rw [hRh]; push_cast; linarith
  clear_value Rh
  set! J : ℕ := ⌈Cj * δs⁻¹ ^ 2 * d * Rh * Real.log (2 * Dm)⌉₊ with hJ
  have hJb : (J : ℝ) ≤ cJ * Λ ^ 7 := by
    have hl : Real.log (2 * Dm) ≤ 2 * Λ := by
      rw [Real.log_mul (by norm_num) (by linarith)]; linarith [Real.log_two_lt_d9]
    have hlpos : 0 ≤ Real.log (2 * Dm) := Real.log_nonneg (by linarith)
    have h0 : 0 ≤ (Cj : ℝ) * δs⁻¹ ^ 2 := by positivity
    have h1 : (Cj : ℝ) * δs⁻¹ ^ 2 * d * Rh * Real.log (2 * Dm) ≤
        (Cj * δs⁻¹ ^ 2) * Λ * (631 * Λ ^ 5) * (2 * Λ) := by
      apply mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hdΛ h0) hRhb (Nat.cast_nonneg _)
        (by positivity)) hl hlpos (by positivity)
    have h2 := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤
      Cj * δs⁻¹ ^ 2 * d * Rh * Real.log (2 * Dm))).le
    have h7 : (1 : ℝ) ≤ Λ ^ 7 := one_le_pow₀ hΛ1
    have hexp : (Cj * δs⁻¹ ^ 2) * Λ * (631 * Λ ^ 5) * (2 * Λ) = 1262 * Cj * δs⁻¹ ^ 2 * Λ ^ 7 := by
      ring
    have hsplit7 : (1262 * Cj * δs⁻¹ ^ 2 + 1) * Λ ^ 7 = 1262 * Cj * δs⁻¹ ^ 2 * Λ ^ 7 + Λ ^ 7 := by
      ring
    rw [hJ, hcJ, hsplit7]
    linarith
  clear_value J
  set! A : ℝ := (Cs * 6 ^ Rh * Bstar * Dstar) ^ CA with hA
  have hA1 : 1 ≤ A := by
    apply one_le_pow₀
    have h6 : (1 : ℝ) ≤ 6 ^ Rh := one_le_pow₀ (by norm_num)
    have h1 : (1 : ℝ) ≤ Cs * 6 ^ Rh := one_le_mul_of_one_le_of_one_le hCs1 h6
    have h2 : (1 : ℝ) ≤ Cs * 6 ^ Rh * Bstar := one_le_mul_of_one_le_of_one_le h1 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h2 (by linarith)
  have hlogA : Real.log A ≤ cA * Λ ^ 5 := by
    rw [hA, Real.log_pow, Real.log_mul (by positivity) (by linarith),
      Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    have h5 : (1 : ℝ) ≤ Λ ^ 5 := one_le_pow₀ hΛ1
    have hΛ5 : Λ ≤ Λ ^ 5 := le_self_pow₀ hΛ1 (by norm_num)
    have h6 : (Rh : ℝ) * Real.log 6 ≤ 631 * Λ ^ 5 * 2 :=
      mul_le_mul hRhb hl6 (Real.log_nonneg (by norm_num)) (by positivity)
    have hin : Real.log Cs + Rh * Real.log 6 + Real.log Bstar + Real.log Dstar ≤
        1564 * Λ ^ 5 := by linarith
    have hin0 : 0 ≤ Real.log Cs + Rh * Real.log 6 + Real.log Bstar + Real.log Dstar := by
      have := Real.log_nonneg hCs1
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)
      have : (0 : ℝ) ≤ Rh * Real.log 6 := by positivity
      linarith
    have hCA : (0 : ℝ) ≤ CA := Nat.cast_nonneg _
    calc (CA : ℝ) * (Real.log Cs + Rh * Real.log 6 + Real.log Bstar + Real.log Dstar) ≤
        CA * (1564 * Λ ^ 5) := mul_le_mul_of_nonneg_left hin hCA
      _ ≤ cA * Λ ^ 5 := by
          rw [hcA, show ((1564 : ℝ) * CA + 1) * Λ ^ 5 = CA * (1564 * Λ ^ 5) + Λ ^ 5 by ring]
          linarith
  expose_names
  exact @chooseSchedule_stage_1 Cj CA CT CK δs hδs hcX hcH hcT hcJ0 hcX0 hcT0 dmax Dstar Bstar Dm
    Wf Q0 hd hD hB hQ hWf Λ hd2 hlD hΛ1 hdΛ hlDΛ hlBΛ hlQΛ hldΛ hpow hl6 Cs hCs hCs1 hlogCs Rh hRh
    J hJ hJb hA hA1 hlogA

end ModeSchedule

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

@[simp] theorem foldIdx_castAdd {d : ℕ} (a : Fin d) : foldIdx d (Fin.castAdd d a) = a :=
  Fin.addCases_left (motive := fun _ => Fin d) a

theorem foldIdx_natAdd {d : ℕ} (a : Fin d) : foldIdx d (Fin.natAdd d a) = a :=
  Fin.addCases_right (motive := fun _ => Fin d) a

@[simp] theorem foldIdx_addNat {d : ℕ} (a : Fin d) : foldIdx d (a.addNat d) = a := by
  simpa only [Fin.natAdd_eq_addNat] using foldIdx_natAdd a

/-- The averaging projection of the doubled coordinates onto the diagonal. -/
def diagAvgQ (d : ℕ) : Matrix (Fin (d + d)) (Fin (d + d)) ℚ :=
  fun i j => if foldIdx d i = foldIdx d j then 1 / 2 else 0

theorem diagAvg_sum {d : ℕ} (i : Fin (d + d)) (f : Fin (d + d) → ℝ) :
    ∑ k, diagAvgR d i k * f k =
      (1 / 2) * (f (Fin.castAdd d (foldIdx d i)) + f (Fin.natAdd d (foldIdx d i))) := by
  rw [Fin.sum_univ_add]
  simp only [diagAvgR, foldIdx_castAdd, foldIdx_natAdd, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  ring

theorem diagAvgQ_map {d : ℕ} : (diagAvgQ d).map (fun q => (q : ℝ)) = diagAvgR d := by
  ext i j; simp only [Matrix.map_apply, diagAvgQ, diagAvgR]; split_ifs <;> norm_num

theorem diagAvgR_mul_self (d : ℕ) : diagAvgR d * diagAvgR d = diagAvgR d := by
  ext i j
  rw [Matrix.mul_apply, diagAvg_sum]
  simp only [diagAvgR, foldIdx_castAdd, foldIdx_natAdd]
  split_ifs <;> norm_num

theorem diagAvgR_transpose (d : ℕ) : (diagAvgR d).transpose = diagAvgR d := by
  ext i j; simp only [Matrix.transpose_apply, diagAvgR, eq_comm]

theorem diagAvg_isStarProjection (d : ℕ) :
    IsStarProjection (realMatrixOperator (diagAvgR d)) := by
  refine ⟨?_, ?_⟩
  · change (realMatrixOperator (diagAvgR d)).comp (realMatrixOperator (diagAvgR d)) = _
    ext x : 1
    rw [ContinuousLinearMap.comp_apply, ← realMatrixOperator_mul_apply, diagAvgR_mul_self]
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    change inner ℝ (realMatrixOperator (diagAvgR d) x) y = inner ℝ x (realMatrixOperator _ y)
    rw [realMatrixOperator_transpose_inner, diagAvgR_transpose]

theorem rationalHeight_half : rationalHeight (1 / 2 : ℚ) = 2 := by
  rw [rationalHeight, show (1 / 2 : ℚ) = mkRat 1 2 by norm_num [Rat.mkRat_eq_div]]; rfl

theorem rationalHeight_neg_half : rationalHeight (-(1 / 2) : ℚ) = 2 := by
  rw [rationalHeight, show (-(1 / 2) : ℚ) = mkRat (-1) 2 by norm_num [Rat.mkRat_eq_div]]; rfl

theorem rationalHeight_zero : rationalHeight (0 : ℚ) = 1 := by simp [rationalHeight]

/-- Equal tags are joined by an edge of every height `B ≥ 2`: the diagonal of the doubled
coordinates is isotropic for the difference form, and the difference data vanish on it. -/
theorem tagEdge_refl {B : ℝ} (hB : 2 ≤ B) (r : ℝ) (v : ChartTag) : tagEdge B r v v := by
  classical
  set P := realMatrixOperator (diagAvgR v.dim)
  obtain ⟨hU, hPU⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp (diagAvg_isStarProjection v.dim)
  set U := P.range
  have hQmap : (1 - diagAvgQ v.dim).map (fun q => (q : ℝ)) = 1 - diagAvgR v.dim := by
    rw [← diagAvgQ_map]; ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp
  have hQ1map : (1 - (1 - diagAvgQ v.dim)).map (fun q => (q : ℝ)) = diagAvgR v.dim := by
    rw [sub_sub_cancel, diagAvgQ_map]
  -- the diagonal vectors
  have hdiag : ∀ x ∈ U, ∀ i, x.ofLp i = x.ofLp (Fin.castAdd v.dim (foldIdx v.dim i)) := by
    rintro x ⟨w, rfl⟩ i
    change (realMatrixOperator (diagAvgR v.dim) w).ofLp i =
      (realMatrixOperator (diagAvgR v.dim) w).ofLp _
    simp only [realMatrixOperator_apply, Matrix.mulVec, dotProduct]
    rw [diagAvg_sum, diagAvg_sum, foldIdx_castAdd]
  have hV : (1 - diagAvgR v.dim) * tagDiffV r v v = 0 := by
    ext i j
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, Matrix.mul_apply]
    simp only [tagDiffV]
    rw [diagAvg_sum]
    simp only [Fin.append_left, Fin.append_right, Matrix.zero_apply]
    have : Fin.append v.θ v.θ i = v.θ (foldIdx v.dim i) := by
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i
      · rw [foldIdx_castAdd]; exact Fin.append_left _ _ _
      · rw [foldIdx_natAdd]; exact Fin.append_right _ _ _
    rw [this]; ring
  refine ⟨U, 1 - diagAvgQ v.dim, ?_, ?_, ?_, fun i j => ?_, fun i j => ?_, ?_, ?_⟩
  · rw [hQmap, realMatrixOperator_sub, realMatrixOperator_one, Submodule.starProjection_orthogonal,
      ← hPU]
  · rw [hQ1map]; exact hPU
  · intro x hx y hy
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial, realMatrixOperator_apply, dotProduct, Matrix.mulVec]
    rw [Fin.sum_univ_add]
    simp only [Fin.sum_univ_add, Matrix.sub_apply, Matrix.transpose_apply,
      Matrix.map_apply, tagDiffC, chartBlockMatrix, Fin.addCases_left, Fin.addCases_right]
    have hx' : ∀ a, x.ofLp (Fin.natAdd v.dim a) = x.ofLp (Fin.castAdd v.dim a) := fun a => by
      rw [hdiag x hx (Fin.natAdd v.dim a), foldIdx_natAdd]
    have hy' : ∀ a, y.ofLp (Fin.natAdd v.dim a) = y.ofLp (Fin.castAdd v.dim a) := fun a => by
      rw [hdiag y hy (Fin.natAdd v.dim a), foldIdx_natAdd]
    simp only [hx', hy', Rat.cast_zero, sub_self, zero_mul, Finset.sum_const_zero, add_zero,
      zero_add, Matrix.neg_apply, Rat.cast_neg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← add_mul, ← Finset.sum_add_distrib, Finset.sum_eq_zero fun b _ => by ring, zero_mul]
  · simp only [Matrix.sub_apply, Matrix.one_apply, diagAvgQ]
    by_cases h1 : i = j
    · subst h1; simp only [↓reduceIte]; norm_num [rationalHeight_half]; linarith
    · by_cases h2 : foldIdx v.dim i = foldIdx v.dim j
      · simp only [h1, h2, ↓reduceIte]; norm_num [rationalHeight_neg_half]; linarith
      · simp only [h1, h2, ↓reduceIte, sub_zero, rationalHeight_zero]; norm_num; linarith
  · rw [sub_sub_cancel]; simp only [diagAvgQ]
    split_ifs
    · norm_num [rationalHeight_half]; linarith
    · norm_num [rationalHeight_zero]; linarith
  · rw [hQmap, hV]
    have : realMatrixOperator (0 : Matrix (Fin (v.dim + v.dim)) (Fin 1) ℝ) = 0 := by
      ext x i; simp [realMatrixOperator_apply]
    rw [this, norm_zero]; linarith
  · rw [hQmap, hV]
    have hE : effectiveReturnQuadratic ((tagDiffC v v).map fun q => (q : ℝ)) (tagDiffΛ r v v)
        (tagDiffV r v v) ((1 - (1 - diagAvgQ v.dim)).map (fun q => (q : ℝ)) * tagDiffV r v v) 0 =
          0 := by
      ext a b
      fin_cases a; fin_cases b
      simp only [effectiveReturnQuadratic, Matrix.mul_zero, realSymmetricPart]
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Matrix.transpose_zero,
        add_zero, smul_zero, smul_eq_mul]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.map_apply, tagDiffV, tagDiffC, chartBlockMatrix, Fin.sum_univ_add,
        Fin.append_left, Fin.append_right, Fin.addCases_left, Fin.addCases_right, smul_eq_mul]
      push_cast
      simp only [Matrix.neg_apply, Rat.cast_neg, tagDiffΛ, sub_self, mul_zero,
        Finset.sum_const_zero, add_zero, zero_add]
      simp only [mul_neg, ← neg_add, Finset.sum_neg_distrib, neg_mul]
      ring
    have : realMatrixOperator (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
      ext x i; simp [realMatrixOperator_apply]
    rw [hE, this, norm_zero]; linarith

namespace ActiveSetup

namespace AttemptParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (ap : A.AttemptParams)

/-! ### Primaries of a ball are joined to the group center (blueprint lines 1893-1903) -/

end AttemptParams

end ActiveSetup

/-! ### Complexity of the branch charts of a group center (blueprint lines 1893-1903) -/

/-- The Gevrey constant of the bump normalization. -/
noncomputable def bumpConst : ℝ := (max 1 gevreyBumpIntegral⁻¹) ^ 2

theorem one_le_bumpConst : 1 ≤ bumpConst := one_le_pow₀ (le_max_left _ _)

/-- The branch profile at width `δ` has geometric derivative bounds of ratio
`A (8(m+1))³² (2/δ)` up to order `m`. -/
theorem branchProfile_deriv_le {δ : ℝ} (hδ : 0 < δ) {m i : ℕ} (hi : i ≤ m) (x : ℝ) :
    |iteratedDeriv i (branchProfile δ) x| ≤
      (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ)) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · simp only [iteratedDeriv_zero, pow_zero]
    have := branchProfile_mem δ x
    rw [abs_of_nonneg this.1]; exact this.2
  have h := iteratedDeriv_gevreyIntervalCutoff_bound i 0 (2 * δ) (1 - 2 * δ) 1 x
  have hmax : max |2 / (2 * δ - 0)| |(-2) / (1 - (1 - 2 * δ))| = 1 / δ := by
    have e1 : 2 / (2 * δ - 0) = 1 / δ := by rw [sub_zero]; field_simp
    have e2 : (-2) / (1 - (1 - 2 * δ)) = -(1 / δ) := by field_simp; ring
    rw [e1, e2, abs_neg, max_self, abs_of_pos (by positivity)]
  rw [hmax] at h
  change |iteratedDeriv i (gevreyIntervalCutoff 0 (2 * δ) (1 - 2 * δ) 1) x| ≤ _
  refine h.trans ?_
  have hA := one_le_bumpConst
  have hm1 : (1 : ℝ) ≤ 8 * ((m : ℝ) + 1) := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have him : (8 * ((i : ℝ) + 1)) ≤ 8 * ((m : ℝ) + 1) := by
    have : (i : ℝ) ≤ m := by exact_mod_cast hi
    linarith
  have h1 : (max 1 gevreyBumpIntegral⁻¹) ^ 2 ≤ bumpConst ^ i := by
    change bumpConst ≤ bumpConst ^ i
    exact le_self_pow₀ hA (by omega)
  have h2 : (8 * ((i : ℝ) + 1)) ^ (16 * (i + 1)) ≤ ((8 * ((m : ℝ) + 1)) ^ 32) ^ i := by
    rw [← pow_mul]
    calc (8 * ((i : ℝ) + 1)) ^ (16 * (i + 1)) ≤ (8 * ((m : ℝ) + 1)) ^ (16 * (i + 1)) :=
          pow_le_pow_left₀ (by positivity) him _
      _ ≤ (8 * ((m : ℝ) + 1)) ^ (32 * i) := pow_le_pow_right₀ hm1 (by omega)
  have h3 : (2 * (1 / δ)) ^ i = (2 / δ) ^ i := by rw [mul_one_div]
  rw [h3]
  calc (max 1 gevreyBumpIntegral⁻¹) ^ 2 * (8 * ((i : ℝ) + 1)) ^ (16 * (i + 1)) * (2 / δ) ^ i
      ≤ bumpConst ^ i * ((8 * ((m : ℝ) + 1)) ^ 32) ^ i * (2 / δ) ^ i := by gcongr
    _ = _ := by rw [← mul_pow, ← mul_pow]

/-- The branch amplitude is the coordinate product of the branch profile, shifted by `ρ`. -/
theorem branchAmp_eq_shift {d : ℕ} (δ : ℝ) (ρ : Fin d → ℝ) :
    branchAmp δ ρ = fun w => chartCoordinateProduct (branchProfile δ) (w - ρ) := by
  funext w; rfl

theorem branchAmp_iteratedFDeriv_le {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (ρ w : Fin d → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (branchAmp δ ρ) w‖ ≤
      ((d : ℝ) * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))) ^ m := by
  rw [branchAmp_eq_shift, iteratedFDeriv_comp_sub]
  have hs : ContDiff ℝ (⊤ : ℕ∞) (branchProfile δ) :=
    contDiff_infty.mpr fun n => gevreyIntervalCutoff_contDiff n _ _ _ _
  have hR : 0 ≤ bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ) := by
    have := one_le_bumpConst; positivity
  exact chartCoordinateProduct_derivative_geometric hs (w - ρ) hR
    (fun i hi x => branchProfile_deriv_le hδ hi x)

/-- Blueprint lines 1893-1903: the branch chart of a center tag `z` in a slot of multiplier
`c` (phase `-c p_ρ`, amplitude the periodic Gevrey branch cutoff of width `δ`) has Gevrey order
`32` complexity at every height `H ≥ d A 8³² (2/δ)` dominating `e²`, its dimension and matrix
heights (offsets in `[0,1]`). -/
theorem branchChart_complexity (z : ChartTag) (c : ℤ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4)
    (ρ : Fin z.dim → ℝ) (hρ : ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) {H : ℝ} (hH : Real.exp 2 ≤ H)
    (hdim : (z.dim : ℝ) ≤ Real.log H)
    (hC : ∀ i j, (chartRationalHeight ((((-c : ℤ) : ℚ) • z.C) i j) : ℝ) ≤ H)
    (hHδ : (z.dim : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ H) :
    QuadraticChartComplexity 32 H
      (branchChart z c (branchAmp_smooth δ ρ) (branchAmp_hasCompactSupport hδ hδ' ρ)) := by
  have hH1 : 1 ≤ H := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hH
  refine ⟨hH, hdim, hC, fun w hw i => ?_, fun m word w => ?_⟩
  · obtain ⟨h1, h2⟩ := branchAmp_support hδ hδ' hw i
    have := hρ i
    rw [abs_le]
    constructor <;> nlinarith [Real.add_one_le_exp (2 : ℝ), this.1, this.2]
  · refine (norm_coordinateWordDerivative_le _ word w).trans ?_
    refine (branchAmp_iteratedFDeriv_le hδ ρ w m).trans ?_
    set X := (z.dim : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ))
    have hX0 : 0 ≤ X := by have := one_le_bumpConst; positivity
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    have e : (z.dim : ℝ) * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ)) =
        X * ((m : ℝ) + 1) ^ 32 := by
      simp only [X]; rw [mul_pow]; ring
    rw [e, mul_pow, ← pow_mul]
    calc X ^ m * ((m : ℝ) + 1) ^ (32 * m) ≤ H ^ m * ((m : ℝ) + 1) ^ (32 * m) := by
          gcongr
      _ ≤ H ^ (32 * (m + 1)) * ((m : ℝ) + 1) ^ (32 * (m + 1)) :=
          mul_le_mul (pow_le_pow_right₀ hH1 (by omega)) (pow_le_pow_right₀ hm1 (by omega))
            (by positivity) (by positivity)

/-! ### Recentred first-match expansions (blueprint lines 1903-1922: "recentring adds only a
common unrestricted linear phase") -/

/-- Blueprint first-match, recentred at an arbitrary point `a₀`: for a primary `Φ` of tag `v`
matched to a center `z` by an edge at length `r`, the product chart `P = Φ ⊗ branchChart` has,
on the window `|t| ≤ R r` around `a₀`, an exact absolutely convergent expansion
`φ_P(a₀ + t) = Σ_ℓ a_ℓ e(λ_* t² + (β + σ_ℓ·θ) t)` with one common curvature and rational
frequency differences, everything quasipolynomial in the translated complexity and `B`. -/
theorem firstMatchExpansion_at (c₀ : ℕ) (hc : 1 ≤ c₀) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (v z : ChartTag) (c : ℤ), c ≠ 0 → |c| ≤ 3 →
    ∀ (H B r : ℝ) (Φ : QuadraticChartData v.dim)
      {g : (Fin z.dim → ℝ) → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g),
      Φ.horizontal = v.θ → Φ.matrix = (c : ℚ) • v.C → Φ.quadratic = c * v.lam →
      QuadraticChartComplexity c₀ H (productQuadraticChart Φ (branchChart z c hg hgc)) →
      0 < r → 2 ≤ B → tagEdge B r v z → ∀ a₀ : ℝ,
      let P := productQuadraticChart Φ (branchChart z c hg hgc)
      let X := 1 + Real.log (chartTranslationBudget H) + Real.log (3 * B)
      ∃ M : Matrix (Fin (v.dim + z.dim)) (Fin (v.dim + z.dim)) ℚ,
        (∀ i j, (rationalHeight (M i j) : ℝ) ≤ Real.exp (D * X ^ D)) ∧
        |P.quadratic + ∑ i, ∑ j, P.horizontal i * (M i j : ℝ) * P.horizontal j| * r ^ 2 ≤
          Real.exp (D * X ^ D) ∧
        ∃ (ι : Type) (_ : Fintype ι)
          (σ : ι × (Fin ((v.dim + z.dim) + (v.dim + z.dim)) → ℤ) → Fin (v.dim + z.dim) → ℚ),
          (Fintype.card ι : ℝ) ≤ Real.exp (D * X ^ D) ∧
          (∀ p i, (rationalHeight (σ p i) : ℝ) ≤
            Real.exp (D * X ^ D) * (1 + frequencyLength p.2)) ∧
          ∃ (β : ℝ) (a : ι × (Fin ((v.dim + z.dim) + (v.dim + z.dim)) → ℤ) → ℂ),
            (∀ t : ℝ, |t| ≤ R * r →
              HasSum (fun p => a p * (Real.fourierChar ((P.quadratic +
                  ∑ i, ∑ j, P.horizontal i * (M i j : ℝ) * P.horizontal j) * t ^ 2 +
                  (β + ∑ i, (σ p i : ℝ) * P.horizontal i) * t) : ℂ))
                (quadraticChartAtom P (a₀ + t))) ∧
            Summable (fun p => ‖a p‖) ∧ (∑' p, ‖a p‖) ≤ Real.exp (D * X ^ D) ∧
            ∀ T : ℝ, 1 ≤ T → (∑ f : ι, ∑ w ∈ frequencyShell ((v.dim + z.dim) + (v.dim + z.dim)) T,
              ‖a (f, w)‖) * T ≤ Real.exp (D * X ^ D) := by
  obtain ⟨D, hD, DJ, hsp⟩ := splitPhase c₀ hc R hR
  refine ⟨max D (DJ 1), le_trans hD (le_max_left _ _), ?_⟩
  intro v z c hc0 hc3 H B r Φ g hg hgc hθ hM hq hP hr hB hE a₀ P X
  have hW : WeylSplitData (3 * B) (fun i _ => r * P.horizontal i) P.matrix
      (fun _ _ => r ^ 2 * P.quadratic) := by
    have h := (WeylSplitData.smul hc0 hE).mono (B' := 3 * B) (by
      have hc3' : |(c : ℝ)| ≤ 3 := by rw [← Int.cast_abs]; exact_mod_cast hc3
      exact mul_le_mul_of_nonneg_right hc3' (by linarith))
    have hV : tagDiffV r v z = fun i _ => r * P.horizontal i := by
      funext i j
      simp [tagDiffV, P, productQuadraticChart, branchChart, mkQuadraticChart, hθ]
    have hCm : (c : ℚ) • tagDiffC v z = P.matrix := by
      simp only [tagDiffC, P, productQuadraticChart, branchChart, mkQuadraticChart, hM]
      rw [← chartBlockMatrix_smul]
      congr 1
      ext i j; simp
    have hL : (c : ℝ) • tagDiffΛ r v z = fun _ _ => r ^ 2 * P.quadratic := by
      funext i j
      simp [tagDiffΛ, P, productQuadraticChart, branchChart, mkQuadraticChart, hq]
      ring
    rw [hV, hCm, hL] at h
    exact h
  obtain ⟨P', hP', -, hatom, hh, hm, hqd⟩ := quadraticChart_translation_tag hP hc a₀
  have hW' : WeylSplitData (3 * B) (fun i _ => r * P'.horizontal i) P'.matrix
      (fun _ _ => r ^ 2 * P'.quadratic) := by
    rw [hh, hm, hqd]; exact hW
  obtain ⟨M, hMh, hlam, ι, hι, σ, hcard, hσ, a, hexp, hsumm, htot, hJ⟩ :=
    hsp (chartTranslationBudget H) (3 * B) r P' hP' hr (by linarith) hW'
  rw [hh, hqd] at hlam
  have hX1 : 1 ≤ X := by
    have hH := hP.lower
    have h1 : 0 ≤ Real.log (chartTranslationBudget H) := by
      unfold chartTranslationBudget logarithmicSize
      rw [Real.log_exp]
      have : 2 ≤ Real.log H := by
        rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 2) hH)]; exact hH
      positivity
    have h2 : 0 ≤ Real.log (3 * B) := Real.log_nonneg (by linarith)
    simp only [X]; linarith
  have hmono := qpoly_exponent_mono (le_max_left D (DJ 1)) hX1
  have hmono' := qpoly_exponent_mono (le_max_right D (DJ 1)) hX1
  obtain ⟨-, hshell⟩ := hJ 1
  refine ⟨M, fun i j => (hMh i j).trans hmono, hlam.trans hmono, ι, hι, σ, hcard.trans hmono,
    fun p i => ?_, P'.linear, a, fun t ht => ?_, hsumm, htot.trans hmono, fun T hT => ?_⟩
  · have h1 := hσ p i
    have h2 := frequencyLength_nonneg p.2
    refine le_trans (by simpa using h1) (mul_le_mul_of_nonneg_right hmono (by linarith))
  rotate_left
  · refine le_trans ?_ ((hshell T hT).trans hmono')
    gcongr
    exact le_self_pow₀ hT (by positivity)
  have h := (hexp t ht).mul_left (Real.fourierChar ((P'.quadratic +
    ∑ i, ∑ j, P'.horizontal i * (M i j : ℝ) * P'.horizontal j) * t ^ 2 + P'.linear * t) : ℂ)
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
    show (P'.quadratic + ∑ i, ∑ j, P'.horizontal i * (M i j : ℝ) * P'.horizontal j) * t ^ 2 +
      P'.linear * t + -((P'.quadratic + ∑ i, ∑ j, P'.horizontal i * (M i j : ℝ) *
        P'.horizontal j) * t ^ 2 + P'.linear * t) = 0 by ring, AddChar.map_zero_eq_one,
    Circle.coe_one, one_mul, hatom, add_comm t a₀] at h
  rw [hh, hqd] at h
  convert h using 1
  funext p
  rw [mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  ring

/-! ### First-match expansions of attempt primaries (blueprint lines 1903-1922) -/

theorem slotCoeff_abs_le (l : Fin 4) : |slotCoeff l| ≤ 3 := by
  fin_cases l <;> decide

/-! ### Finite first-match expansions (blueprint line 1907: `+ O(δ_c)`) -/

section GlobalLift
variable {Pr Md : Type*} [Fintype Pr] [Fintype Md] [DecidableEq Pr] [DecidableEq Md]

/-! ### The global mode lift (blueprint lines 1932-1940) -/

/-- The pointwise lift as a linear map. -/
noncomputable def modeLiftLin (own : Md → Pr) (s : ℂ) (q : Pr → ℂ) (a : Md → ℂ) (εP : Pr → ℝ)
    (εM : Md → ℝ) : ColumnHilbert Pr →ₗ[ℂ] ColumnHilbert Md where
  toFun := modeLift own s q a εP εM
  map_add' F G := by
    ext o; rcases o with _ | m
    · simp only [modeLift, PiLp.add_apply, Finset.sum_add_distrib, add_div, add_mul, mul_add]
      ring
    · simp only [modeLift, PiLp.add_apply, mul_add, add_div]
  map_smul' c F := by
    ext o; rcases o with _ | m
    · simp only [modeLift, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_div_assoc]
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun x _ => by ring
    · simp only [modeLift, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring

omit [DecidableEq Pr] in
/-- The lift written in coordinates: each output coordinate is a combination of the input
coordinates. -/
theorem modeLift_eq_sum (own : Md → Pr) (s : ℂ) (q : Pr → ℂ) (a : Md → ℂ) (εP : Pr → ℝ)
    (εM : Md → ℝ) (F : ColumnHilbert Pr) :
    modeLift own s q a εP εM F =
      (s * F none + ∑ Φ, F (some Φ) / (Real.sqrt (εP Φ) : ℂ) * q Φ) •
          EuclideanSpace.single none 1 +
        ∑ m, ((Real.sqrt (εM m) : ℂ) * a m * F (some (own m)) /
          (Real.sqrt (εP (own m)) : ℂ)) • EuclideanSpace.single (some m) 1 := by
  ext o; rcases o with _ | m
  · simp [modeLift]
  · simp only [modeLift, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.single_apply]
    simp

end GlobalLift

section GlobalLiftOp
variable {Pr Md : Type*} [Fintype Pr] [Fintype Md] [DecidableEq Pr]

/-- The data of a global mode lift: measurable gauge `s = (ζ^ρ)²` with `|s| ≤ 1`, measurable
physical corrections `|q_Φ| ≤ δ`, mode coefficients and private weights obeying the hypotheses
of `modeLift_norm_sq_le` (blueprint lines 1932-1940). -/
structure LiftData (Pr Md : Type*) [Fintype Pr] [Fintype Md] [DecidableEq Pr] where
  /-- Primary label owning each mode. -/
  own : Md → Pr
  /-- Bounded measurable gauge multiplying the physical component of the lift. -/
  s : ℝ → ℂ
  /-- Small physical correction associated with each primary label. -/
  q : Pr → ℝ → ℂ
  /-- Measurable coefficient of each lifted mode. -/
  a : Md → ℝ → ℂ
  /-- Positive private-coordinate weight assigned to each primary label. -/
  εP : Pr → ℝ
  /-- Nonnegative private-coordinate weight assigned to each mode. -/
  εM : Md → ℝ
  /-- Uniform norm bound for the primary physical corrections. -/
  δ : ℝ
  a_meas : ∀ m, Measurable (a m)
  s_meas : Measurable s
  s_le : ∀ y, ‖s y‖ ≤ 1
  q_meas : ∀ Φ, Measurable (q Φ)
  q_le : ∀ Φ y, ‖q Φ y‖ ≤ δ
  εP_pos : ∀ Φ, 0 < εP Φ
  q_sum : ∀ y, ∑ Φ, ‖q Φ y‖ ^ 2 / εP Φ ≤ 1
  εM_nonneg : ∀ m, 0 ≤ εM m
  weights : ∀ Φ y, ∑ m ∈ Finset.univ.filter (fun m => own m = Φ), εM m * ‖a m y‖ ^ 2 ≤ εP Φ

namespace LiftData
variable (L : LiftData Pr Md)

/-- The lift at the point `y`. -/
noncomputable def at_ (y : ℝ) : ColumnHilbert Pr →ₗ[ℂ] ColumnHilbert Md :=
  modeLiftLin L.own (L.s y) (fun Φ => L.q Φ y) (fun m => L.a m y) L.εP L.εM

theorem norm_at_le (y : ℝ) (F : ColumnHilbert Pr) : ‖L.at_ y F‖ ≤ Real.sqrt 5 * ‖F‖ := by
  have h := modeLift_norm_sq_le' L.own (L.s_le y) (fun Φ => L.q Φ y)
    (fun m => L.a m y) L.εP L.εP_pos (L.q_sum y) L.εM L.εM_nonneg (fun Φ => L.weights Φ y) F
  have h' : ‖L.at_ y F‖ ^ 2 ≤ (Real.sqrt 5 * ‖F‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]; exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'

omit [DecidableEq Pr] in
theorem coord_aestronglyMeasurable (F : ColumnL2 Pr) (o : Option Pr) :
    AEStronglyMeasurable (fun y => (F : ℝ → ColumnHilbert Pr) y o) volume :=
  (EuclideanSpace.proj (𝕜 := ℂ) o).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)

theorem at_aestronglyMeasurable (F : ColumnL2 Pr) :
    AEStronglyMeasurable (fun y => L.at_ y ((F : ℝ → ColumnHilbert Pr) y)) volume := by
  classical
  have e : (fun y => L.at_ y ((F : ℝ → ColumnHilbert Pr) y)) = fun y =>
      (L.s y * (F : ℝ → ColumnHilbert Pr) y none +
        ∑ Φ, (F : ℝ → ColumnHilbert Pr) y (some Φ) * ((Real.sqrt (L.εP Φ) : ℂ))⁻¹ * L.q Φ y) •
          EuclideanSpace.single none 1 +
        ∑ m, ((Real.sqrt (L.εM m) : ℂ) * L.a m y * (F : ℝ → ColumnHilbert Pr) y (some (L.own m)) *
          ((Real.sqrt (L.εP (L.own m)) : ℂ))⁻¹) • EuclideanSpace.single (some m) 1 := by
    funext y
    change modeLift _ _ _ _ _ _ _ = _
    rw [modeLift_eq_sum]
    simp only [div_eq_mul_inv]
  rw [e]
  refine AEStronglyMeasurable.add (AEStronglyMeasurable.smul_const ?_ _) ?_
  · refine (L.s_meas.aestronglyMeasurable.mul (coord_aestronglyMeasurable F none)).add ?_
    exact Finset.aestronglyMeasurable_fun_sum _ fun Φ _ =>
      ((coord_aestronglyMeasurable F (some Φ)).mul aestronglyMeasurable_const).mul
        (L.q_meas Φ).aestronglyMeasurable
  · exact Finset.aestronglyMeasurable_fun_sum _ fun m _ =>
      (((aestronglyMeasurable_const.mul (L.a_meas m).aestronglyMeasurable).mul
        (coord_aestronglyMeasurable F (some (L.own m)))).mul
          aestronglyMeasurable_const).smul_const _

theorem at_memLp (F : ColumnL2 Pr) :
    MemLp (fun y => L.at_ y ((F : ℝ → ColumnHilbert Pr) y)) 2 volume :=
  (Lp.memLp F).of_le_mul (L.at_aestronglyMeasurable F)
    (Filter.Eventually.of_forall fun y => L.norm_at_le y _)

/-- The global lift `R` on square-integrable columns. -/
noncomputable def op : ColumnL2 Pr →L[ℂ] ColumnL2 Md :=
  LinearMap.mkContinuous
    { toFun := fun F => (L.at_memLp F).toLp _
      map_add' := fun F G => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (L.at_memLp (F + G)), MemLp.coeFn_toLp (L.at_memLp F),
          MemLp.coeFn_toLp (L.at_memLp G), Lp.coeFn_add F G,
          Lp.coeFn_add ((L.at_memLp F).toLp _) ((L.at_memLp G).toLp _)] with y h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, map_add]
      map_smul' := fun c F => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (L.at_memLp (c • F)), MemLp.coeFn_toLp (L.at_memLp F),
          Lp.coeFn_smul c F, Lp.coeFn_smul c ((L.at_memLp F).toLp _)] with y h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, h3, Pi.smul_apply, map_smul] }
    (Real.sqrt 5) fun F => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [MemLp.coeFn_toLp (L.at_memLp F)] with y h1
      change ‖((L.at_memLp F).toLp _ : ℝ → ColumnHilbert Md) y‖ ≤ _
      rw [h1]; exact L.norm_at_le y _

theorem op_coeFn (F : ColumnL2 Pr) :
    (L.op F : ℝ → ColumnHilbert Md) =ᵐ[volume] fun y => L.at_ y ((F : ℝ → ColumnHilbert Pr) y) :=
  MemLp.coeFn_toLp (L.at_memLp F)

end LiftData

end GlobalLiftOp

/-- Blueprint lines 1934-1937 with the zero convention before the match: the lift carries a main
output exactly to its mode synthesis whenever the physical corrections are exact on the primaries
with nonzero coefficient. -/
theorem modeLift_synthesis_supp {Pr Md : Type*} [Fintype Pr] [Fintype Md] [DecidableEq Pr]
    [DecidableEq Md] (own : Md → Pr) (s : ℂ) (φ : Pr → ℂ) (a : Md → ℂ) (ψphys : Md → ℂ)
    (εP : Pr → ℝ) (hεP : ∀ Φ, 0 < εP Φ) (εM : Md → ℝ) (q : Pr → ℂ) (β : Pr → ℂ)
    (hq : ∀ Φ, β Φ ≠ 0 →
      q Φ = ∑ m ∈ Finset.univ.filter (fun m => own m = Φ), a m * ψphys m - s * φ Φ) :
    modeLift own s q a εP εM (augmentedMain φ εP β) =
      ∑ m, (β (own m) * a m) • augmentedMode ψphys εM m := by
  classical
  set q' : Pr → ℂ := fun Φ =>
    ∑ m ∈ Finset.univ.filter (fun m => own m = Φ), a m * ψphys m - s * φ Φ
  rw [← modeLift_synthesis own s φ a ψphys εP hεP εM q' (fun Φ => rfl) β]
  ext o
  rcases o with _ | m
  · simp only [modeLift, augmentedMain]
    congr 1
    refine Finset.sum_congr rfl fun Φ _ => ?_
    by_cases hb : β Φ = 0
    · simp [hb]
    · rw [hq Φ hb]
  · rfl

section MaxCells
variable (G : RealDyadicGrid)

/-! ### First-match cells (blueprint line 1891: "At its first match on `I₀`") -/

open Classical in
/-- The maximal cells of a finite family of dyadic cells. -/
noncomputable def maxCells (C : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  C.filter fun I => ∀ J ∈ C, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2 → J = I

variable {G}

theorem mem_maxCells {C : Finset (ℤ × ℤ)} {I : ℤ × ℤ} :
    I ∈ maxCells G C ↔ I ∈ C ∧
      ∀ J ∈ C, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2 → J = I := by
  classical
  unfold maxCells; rw [Finset.mem_filter]

/-- Every cell of the family lies in a maximal one. -/
theorem exists_maxCell_above {C : Finset (ℤ × ℤ)} {I : ℤ × ℤ} (hI : I ∈ C) :
    ∃ I₀ ∈ maxCells G C, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I₀.1 I₀.2 := by
  classical
  set U := C.filter fun J => dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2
  have hne : U.Nonempty := ⟨I, Finset.mem_filter.mpr ⟨hI, subset_rfl⟩⟩
  obtain ⟨J₀, hJ₀, hmin⟩ := U.exists_min_image (fun J => J.1) hne
  obtain ⟨hJ₀C, hIJ₀⟩ := Finset.mem_filter.mp hJ₀
  refine ⟨J₀, mem_maxCells.mpr ⟨hJ₀C, fun K hK hJK => ?_⟩, hIJ₀⟩
  have hKU : K ∈ U := Finset.mem_filter.mpr ⟨hK, hIJ₀.trans hJK⟩
  have h1 := hmin K hKU
  have h2 := dyadicGridCell_depth_le_of_subset G J₀ K hJK
  exact anc_eq_of_depth hJK subset_rfl (le_antisymm h2 h1)

/-- Two maximal cells sharing a point coincide. -/
theorem maxCells_eq_of_mem {C : Finset (ℤ × ℤ)} {I₀ I₁ : ℤ × ℤ} (h₀ : I₀ ∈ maxCells G C)
    (h₁ : I₁ ∈ maxCells G C) {y : ℝ} (hy₀ : y ∈ dyadicGridCell G I₀.1 I₀.2)
    (hy₁ : y ∈ dyadicGridCell G I₁.1 I₁.2) : I₀ = I₁ := by
  obtain ⟨hC₀, hm₀⟩ := mem_maxCells.mp h₀
  obtain ⟨hC₁, hm₁⟩ := mem_maxCells.mp h₁
  rcases le_total I₀.1 I₁.1 with h | h
  · rcases dyadicGridCell_nested_or_disjoint_of_le G h I₀.2 I₁.2 with hd | hs
    · exact absurd hy₁ (Set.disjoint_left.mp hd hy₀)
    · exact hm₁ I₀ hC₀ hs
  · rcases dyadicGridCell_nested_or_disjoint_of_le G h I₁.2 I₀.2 with hd | hs
    · exact absurd hy₀ (Set.disjoint_left.mp hd hy₁)
    · exact (hm₀ I₁ hC₁ hs).symm

end MaxCells

/-! ### The gauge of a group center (blueprint lines 1893-1900) -/

/-- The cutoff `ζ^ρ(θ_z y)` of a center tag. -/
noncomputable def centerCut (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (y : ℝ) : ℝ :=
  branchCutoffValue δ ρ (fun i => z.θ i * y)

/-- The branch phase `p_ρ(y) = λ_z y² + (θ_z y)ᵀ C_z d_ρ(y)` of a center tag. -/
noncomputable def centerPhase (z : ChartTag) (ρ : Fin z.dim → ℝ) (y : ℝ) : ℝ :=
  z.lam * y ^ 2 + chartMatrixPhase z.C (fun i => z.θ i * y) (branchLift ρ (fun i => z.θ i * y))

theorem centerCut_mem (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (y : ℝ) :
    centerCut z δ ρ y ∈ Set.Icc (0 : ℝ) 1 := branchCutoffValue_mem δ ρ _

theorem centerCut_measurable (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) :
    Measurable (centerCut z δ ρ) := by
  unfold centerCut branchCutoffValue
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (branchProfile_continuous δ).measurable.comp
    (measurable_fract.comp ((measurable_const.mul measurable_id).sub measurable_const))

theorem centerPhase_measurable (z : ChartTag) (ρ : Fin z.dim → ℝ) :
    Measurable (centerPhase z ρ) := by
  unfold centerPhase chartMatrixPhase branchLift
  refine (measurable_const.mul (measurable_id.pow_const 2)).add ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_const.mul measurable_id).mul measurable_const).mul (measurable_const.add
    (measurable_fract.comp ((measurable_const.mul measurable_id).sub measurable_const)))

/-- The atom of a primary times the branch chart of a center is the primary atom times the gauge
`ζ^ρ e(-c p_ρ)`. -/
theorem firstMatch_atom {v : ChartTag} (Φ : QuadraticChartData v.dim) (z : ChartTag) (c : ℤ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (ρ : Fin z.dim → ℝ) (y : ℝ) :
    quadraticChartAtom (productQuadraticChart Φ (branchChart z c (branchAmp_smooth δ ρ)
        (branchAmp_hasCompactSupport hδ hδ' ρ))) y =
      quadraticChartAtom Φ y * ((centerCut z δ ρ y : ℂ) *
        (Real.fourierChar (-(c : ℝ) * centerPhase z ρ y) : ℂ)) := by
  rw [productQuadraticChart_atom]
  congr 1
  unfold branchChart
  rw [branchChart_atom z.θ z.C z.lam c ρ (branchAmp_smooth δ ρ)
    (branchAmp_hasCompactSupport hδ hδ' ρ) (fun w hw i => branchAmp_support hδ hδ' hw i) y,
    branchAmp_branchLift]
  rfl

theorem frequencyLength_le_of_mem_box {d N : ℕ} {w : Fin d → ℤ} (hw : w ∈ frequencyBox d N) :
    frequencyLength w ≤ d * N := by
  have hc : ∀ i, (w i : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := fun i => by
    have := (Fintype.mem_piFinset.mp hw) i
    rw [Finset.mem_Icc] at this
    have h1 : (-(N : ℝ)) ≤ w i := by exact_mod_cast this.1
    have h2 : (w i : ℝ) ≤ N := by exact_mod_cast this.2
    nlinarith
  unfold frequencyLength
  calc Real.sqrt (∑ j, (w j : ℝ) ^ 2) ≤ Real.sqrt (∑ _j : Fin d, (N : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hc j)
    _ = N * Real.sqrt d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _), mul_comm]
    _ ≤ d * N := by
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        rcases Nat.eq_zero_or_pos d with h0 | hpos
        · simp [h0]
        · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hpos
          rw [Real.sqrt_le_left (by linarith)]; nlinarith

/-! ### Counted first-match truncation (blueprint line 1913: the number of modes is at most
`D₁`) -/

/-- Frequencies outside the box of radius `2^(K+1)` lie in the dyadic shells from `2^K` on. -/
theorem exists_late_shell_of_not_mem_box {d K : ℕ} {w : Fin d → ℤ}
    (hw : w ∉ frequencyBox d (2 ^ (K + 1))) :
    ∃ k : ℕ, w ∈ frequencyShell d ((2 : ℝ) ^ (K + k)) := by
  have hne : w ≠ 0 := fun h => hw (by
    subst h
    simp only [frequencyBox, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc]
    intro _; exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩)
  refine exists_mem_late_frequencyShell hne K ?_
  simp only [frequencyBox, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hw
  obtain ⟨i, hi⟩ := hw
  have hbig : (2 : ℝ) ^ (K + 1) < |(w i : ℝ)| := by
    have : ((2 ^ (K + 1) : ℕ) : ℤ) < |w i| := by
      by_contra h
      exact hi (abs_le.mp (not_lt.mp h))
    exact_mod_cast this
  have hlen : |(w i : ℝ)| ≤ frequencyLength w := by
    unfold frequencyLength
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => ((w j : ℝ)) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have h2 : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith [frequencyLength_nonneg w]

open Classical in
/-- The absolute tail outside a frequency box from dyadic shell bounds `(Σ_shell |a|) T ≤ B`. -/
theorem box_tail_le {ι : Type*} [Fintype ι] {d : ℕ} (a : ι × (Fin d → ℤ) → ℂ) {B : ℝ}
    (hB : 0 ≤ B)
    (hshell : ∀ T : ℝ, 1 ≤ T → (∑ f : ι, ∑ w ∈ frequencyShell d T, ‖a (f, w)‖) * T ≤ B)
    (K : ℕ) (s : Finset (ι × (Fin d → ℤ)))
    (hs : ∀ p ∈ s, p.2 ∉ frequencyBox d (2 ^ (K + 1))) :
    ∑ p ∈ s, ‖a p‖ ≤ 2 * B / 2 ^ K := by
  have hk : ∀ p ∈ s, ∃ k : ℕ, p.2 ∈ frequencyShell d ((2 : ℝ) ^ (K + k)) := fun p hp =>
    exists_late_shell_of_not_mem_box (hs p hp)
  let kf : ι × (Fin d → ℤ) → ℕ := fun p =>
    if h : ∃ k : ℕ, p.2 ∈ frequencyShell d ((2 : ℝ) ^ (K + k)) then Nat.find h else 0
  have hkf : ∀ p ∈ s, p.2 ∈ frequencyShell d ((2 : ℝ) ^ (K + kf p)) := fun p hp => by
    simp only [kf, dite_eq_left_of_eq_true (eq_true (hk p hp))]; exact Nat.find_spec (hk p hp)
  set M := (s.image kf).sup id + 1
  have hmaps : ∀ p ∈ s, kf p ∈ Finset.range M := fun p hp => by
    rw [Finset.mem_range]
    have := Finset.le_sup (f := id) (Finset.mem_image_of_mem kf hp)
    simp only [id] at this; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ k ∈ Finset.range M, ∑ p ∈ s.filter (fun p => kf p = k), ‖a p‖ ≤
      B / 2 ^ (K + k) := by
    intro k _
    have hT : (1 : ℝ) ≤ 2 ^ (K + k) := one_le_pow₀ (by norm_num)
    have hsub : s.filter (fun p => kf p = k) ⊆
        (Finset.univ : Finset ι) ×ˢ frequencyShell d ((2 : ℝ) ^ (K + k)) := fun p hp => by
      obtain ⟨hps, hpk⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hpk ▸ hkf p hps⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => norm_nonneg _).trans ?_
    rw [Finset.sum_product, le_div_iff₀ (by positivity)]
    exact hshell _ hT
  refine (Finset.sum_le_sum hfib).trans ?_
  have e : ∑ k ∈ Finset.range M, B / 2 ^ (K + k) =
      B / 2 ^ K * ∑ k ∈ Finset.range M, (1 / 2 : ℝ) ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [pow_add, one_div_pow, mul_one_div, div_div]
  rw [e]
  have hg : ∑ k ∈ Finset.range M, (1 / 2 : ℝ) ^ k ≤ 2 := by
    have := sum_geometric_two_le M
    simpa using this
  calc B / 2 ^ K * ∑ k ∈ Finset.range M, (1 / 2 : ℝ) ^ k ≤ B / 2 ^ K * 2 := by
        gcongr
    _ = 2 * B / 2 ^ K := by ring

/-- Truncation of an absolutely convergent unimodular expansion to a frequency box, with the
remainder controlled by the shell bounds. -/
theorem hasSum_box_truncate {ι T : Type*} [Fintype ι] {d : ℕ} (a : ι × (Fin d → ℤ) → ℂ)
    (ha : Summable fun p => ‖a p‖) {B : ℝ} (hB : 0 ≤ B)
    (hshell : ∀ T : ℝ, 1 ≤ T → (∑ f : ι, ∑ w ∈ frequencyShell d T, ‖a (f, w)‖) * T ≤ B)
    (K : ℕ) (e : ι × (Fin d → ℤ) → T → ℂ) (he : ∀ p t, ‖e p t‖ = 1) (F : T → ℂ) (t : T)
    (hF : HasSum (fun p => a p * e p t) (F t)) :
    ‖F t - ∑ p ∈ (Finset.univ : Finset ι) ×ˢ frequencyBox d (2 ^ (K + 1)), a p * e p t‖ ≤
      2 * B / 2 ^ K := by
  set S := (Finset.univ : Finset ι) ×ˢ frequencyBox d (2 ^ (K + 1))
  have hsum : Summable fun p => a p * e p t := by
    refine Summable.of_norm (ha.congr fun p => ?_)
    rw [norm_mul, he, mul_one]
  have h1 := hsum.sum_add_tsum_compl (s := S)
  rw [hF.tsum_eq] at h1
  have h2 : F t - ∑ p ∈ S, a p * e p t =
      ∑' p : ↑((S : Set (ι × (Fin d → ℤ)))ᶜ),
        a (p : ι × (Fin d → ℤ)) * e (p : ι × (Fin d → ℤ)) t := by
    rw [← h1]; ring
  rw [h2]
  have hsc : Summable fun p : ↑((S : Set (ι × (Fin d → ℤ)))ᶜ) =>
      ‖a (p : ι × (Fin d → ℤ)) * e (p : ι × (Fin d → ℤ)) t‖ := (hsum.norm).subtype _
  refine (norm_tsum_le_tsum_norm hsc).trans ?_
  refine tsum_le_of_sum_le' (by positivity) fun s => ?_
  have e1 : ∑ p ∈ s, ‖a (p : ι × (Fin d → ℤ)) * e (p : ι × (Fin d → ℤ)) t‖ =
      ∑ p ∈ s.map (Function.Embedding.subtype _), ‖a p‖ := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun p _ => by rw [norm_mul, he, mul_one]; rfl
  rw [e1]
  refine box_tail_le a hB hshell K _ fun p hp => ?_
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hp
  have hq := q.2
  simp only [Set.mem_compl_iff, Finset.mem_coe, S, Finset.mem_product, Finset.mem_univ,
    true_and] at hq
  exact hq

theorem measurable_fourierChar_comp {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun y => (Real.fourierChar (f y) : ℂ) :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp hf

/-! ### Bounded expansions in a basis (blueprint line 1958: "Expressing a height-`D_*` vector in a
basis of such vectors in dimension at most `d_max` costs coefficients and common denominator at
most `C_*`") -/

/-- Cramer numerators of a pivot minor reproduce every vector of the column span. -/
theorem rational_pivot_cramer_range {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (rows : Fin r ↪ Fin m) (cols : Fin r ↪ Fin n)
    (hdet : (A.submatrix rows cols).det ≠ 0)
    (hspan : Submodule.span ℚ (Set.range (fun j => A.col (cols j))) =
      Submodule.span ℚ (Set.range A.col)) (y : Fin m → ℚ)
    (hy : y ∈ LinearMap.range A.mulVecLin) :
    (A.submatrix id cols).mulVec ((A.submatrix rows cols).cramer (y ∘ rows)) =
      (A.submatrix rows cols).det • y := by
  have h := rational_pivot_rightInverse A rows cols hdet hspan y hy
  rw [rationalMatrixZeroExtend_mulVec, rational_mulVec_extend] at h
  rw [← Matrix.det_smul_inv_mulVec_eq_cramer _ _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.mulVec_smul, h]

/-! ### The normalized frequency vector `Θ' = (θ_v, ϑ)`, `ϑ = θ_z/Q₀` (blueprint line 1893) -/

/-- Scaling the `ϑ`-coordinates of a rational vector by `Q₀`. -/
def scaleZ (dv dz Q0 : ℕ) (a : Fin (dv + dz) → ℚ) : Fin (dv + dz) → ℚ :=
  Fin.append (fun j => a (Fin.castAdd dz j)) (fun l => (Q0 : ℚ) * a (Fin.natAdd dv l))

theorem branchProfile_eq_zero_of_le {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ 0) :
    branchProfile δ s = 0 :=
  gevreyIntervalCutoff_zero_left (by linarith) (by linarith)

theorem branchProfile_eq_zero_of_ge {δ s : ℝ} (hδ : 0 < δ) (hs : 1 ≤ s) :
    branchProfile δ s = 0 :=
  gevreyIntervalCutoff_zero_right (by linarith) (by linarith)

theorem branchProfile_contDiff (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (branchProfile δ) :=
  contDiff_infty.mpr fun n => gevreyIntervalCutoff_contDiff n _ _ _ _

/-- The physical part of a mode (`eq:modes`): `ζ^ρ(y) e(c p_ρ(y)) e(λ(y-a)² + γ(y-a))`. -/
noncomputable def modeWave (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (cl : ℤ) (lam a γ y : ℝ) :
    ℂ :=
  (centerCut z δ ρ y : ℂ) * (Real.fourierChar ((cl : ℝ) * centerPhase z ρ y) : ℂ) *
    (Real.fourierChar (lam * (y - a) ^ 2 + γ * (y - a)) : ℂ)

theorem modeWave_measurable (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (cl : ℤ)
    (lam a γ : ℝ) : Measurable (modeWave z δ ρ cl lam a γ) := by
  refine ((Complex.measurable_ofReal.comp (centerCut_measurable _ _ _)).mul ?_).mul ?_
  · exact measurable_fourierChar_comp (measurable_const.mul (centerPhase_measurable _ _))
  · exact measurable_fourierChar_comp (by fun_prop)

theorem modeWave_norm_le (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (cl : ℤ) (lam a γ y : ℝ) :
    ‖modeWave z δ ρ cl lam a γ y‖ ≤ 1 := by
  simp only [modeWave, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have := centerCut_mem z δ ρ y
  rw [abs_of_nonneg this.1]; exact this.2

section AugModes
variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Augmented modes on cells (`eq:modes`, blueprint line 1928) -/

/-- The augmented mode `1_J (ψ e_phys + √ε e_m)` on a cell `J`. -/
noncomputable def augMode (J : Set ℝ) (ψ : ℝ → ℂ) (ε : ℝ) (m : V) : ℝ → ColumnHilbert V :=
  J.indicator fun y => ψ y • EuclideanSpace.single none 1 +
    ((Real.sqrt ε : ℝ) : ℂ) • EuclideanSpace.single (some m) 1

theorem augMode_memLp {J : Set ℝ} (hJ : MeasurableSet J) (hJf : volume J ≠ ⊤) {ψ : ℝ → ℂ}
    (hψ : Measurable ψ) (hψb : ∀ y, ‖ψ y‖ ≤ 1) (ε : ℝ) (m : V) :
    MemLp (augMode J ψ ε m) 2 volume := by
  have : IsFiniteMeasure (volume.restrict J) := isFiniteMeasure_restrict.mpr hJf
  refine (memLp_indicator_iff_restrict hJ).mpr ?_
  refine MemLp.of_bound (((hψ.smul_const _).add measurable_const).aestronglyMeasurable)
    (1 + Real.sqrt ε) (Filter.Eventually.of_forall fun y => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, PiLp.norm_single, norm_one, mul_one]; exact hψb y
  · rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

end AugModes

/-! ### The frozen-mode data interface of one role and group (blueprint lines 1971-1975) -/

/-- The frozen modes of one role, group and offset (blueprint "Frozen-mode data interface",
lines 1971-1975): for each primary and first-match cell, the finite list of modes with one
curvature, the coefficient functions, the rational frequency differences `eq:mode-differences`
and the private indices, together with the pointwise lift. -/
structure ModeSystem (Gd : RealDyadicGrid) (Mc : ℕ) where
  /-- Finite type of frozen modes. -/
  Md : Type
  [fin : Fintype Md]
  [deq : DecidableEq Md]
  /-- Pointwise global lift from primary columns to frozen modes. -/
  L : LiftData (Fin Mc) Md
  /-- Common curvature tag of the frozen modes. -/
  zc : ChartTag
  /-- Core fraction controlling the frozen-mode branch profiles. -/
  δc : ℝ
  /-- Horizontal branch offset in the coordinates of the common curvature tag. -/
  ρ : Fin zc.dim → ℝ
  /-- Integer slot index used as the frozen reference slot. -/
  cl : ℤ
  /-- First-match cell associated with each frozen mode. -/
  cellOf : Md → ℤ × ℤ
  /-- Quadratic phase coefficient of each frozen mode. -/
  lamOf : Md → ℝ
  /-- Linear phase coefficient of each frozen mode. -/
  γOf : Md → ℝ
  /-- Type of keys identifying a primary label together with its first-match cell. -/
  Key : Type
  [kdeq : DecidableEq Key]
  /-- Key assigned to each frozen mode. -/
  keyOf : Md → Key
  /-- Dimension of the primary tag associated with a mode key. -/
  dvOf : Key → ℕ
  /-- Horizontal direction of the primary tag associated with a mode key. -/
  θvOf : ∀ k, Fin (dvOf k) → ℝ
  /-- Uniform rational-frequency coefficient budget for mode differences. -/
  Bσ : ℝ
  one_le_Bσ : 1 ≤ Bσ
  /-- Uniform quadratic phase budget for the frozen modes. -/
  Λ : ℝ
  key_own : ∀ m m', keyOf m = keyOf m' → L.own m = L.own m'
  key_cell : ∀ m m', keyOf m = keyOf m' → cellOf m = cellOf m'
  own_cell_key : ∀ m m', L.own m = L.own m' → cellOf m = cellOf m' → keyOf m = keyOf m'
  key_lam : ∀ m m', keyOf m = keyOf m' → lamOf m = lamOf m'
  key_diff : ∀ m m', keyOf m = keyOf m' → ∃ a b : Fin (dvOf (keyOf m) + zc.dim) → ℚ,
    (∀ i, (rationalHeight (a i) : ℝ) ≤ Bσ) ∧ (∀ i, (rationalHeight (b i) : ℝ) ≤ Bσ) ∧
    γOf m - γOf m' = ∑ i, ((a - b) i : ℝ) * Fin.append (θvOf (keyOf m)) zc.θ i
  a_ind : ∀ m y, L.a m y = (dyadicGridCell Gd (cellOf m).1 (cellOf m).2).indicator
    (fun _ => L.a m (dyadicGridLeft Gd (cellOf m).1 (cellOf m).2)) y
  lam_le : ∀ m, |lamOf m| * dyadicGridLength Gd (cellOf m).1 ^ 2 ≤ Λ
  εM_pos : ∀ m, 0 < L.εM m

attribute [instance] ModeSystem.fin ModeSystem.deq ModeSystem.kdeq

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc)

/-- The physical wave of a mode (`eq:modes`). -/
noncomputable def wave (m : Ms.Md) : ℝ → ℂ :=
  modeWave Ms.zc Ms.δc Ms.ρ Ms.cl (Ms.lamOf m) (dyadicGridLeft Gd (Ms.cellOf m).1 (Ms.cellOf m).2)
    (Ms.γOf m)

/-- The slope `ω_m(y) = 2λ_m (y - a_m) + γ_m` of a mode. -/
noncomputable def slope (m : Ms.Md) (y : ℝ) : ℝ :=
  2 * Ms.lamOf m * (y - dyadicGridLeft Gd (Ms.cellOf m).1 (Ms.cellOf m).2) + Ms.γOf m

/-- The modes alive on a cell `U`: their first-match cell contains `U`. -/
noncomputable def alive (U : ℤ × ℤ) : Finset Ms.Md := by
  classical exact Finset.univ.filter fun m =>
    dyadicGridCell Gd U.1 U.2 ⊆ dyadicGridCell Gd (Ms.cellOf m).1 (Ms.cellOf m).2

theorem mem_alive {U : ℤ × ℤ} {m : Ms.Md} :
    m ∈ Ms.alive U ↔
      dyadicGridCell Gd U.1 U.2 ⊆ dyadicGridCell Gd (Ms.cellOf m).1 (Ms.cellOf m).2 := by
  classical
  simp [alive]

end ModeSystem

theorem dyadicGridCell_volume_ne_top (Gd : RealDyadicGrid) (I : ℤ × ℤ) :
    volume (dyadicGridCell Gd I.1 I.2) ≠ ⊤ := by
  rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top


/-! ### Blocks, goodness, side modes and side events of a frozen mode system (lines 1952-2047) -/

/-- The numerical data of the coherence argument: heights `Hn`, the mode-difference height `D`,
the gap threshold `T`, witness and kernel size sequences, the stability lag `R`, the shift `Δ`,
the top height `J_*` and the core fraction `δ_*`. -/
structure SideParams where
  /-- Number of height levels used by the coherence argument. -/
  Hn : ℕ
  /-- Rational-height bound for mode differences in the coherence argument. -/
  D : ℕ
  /-- Gap threshold used to separate coherent mode components. -/
  Tt : ℝ
  /-- Witness-size sequence indexed by height. -/
  Eq : ℕ → ℚ
  /-- Kernel-size sequence indexed by height. -/
  Sk : ℕ → ℚ
  /-- Stability lag used when comparing components at different heights. -/
  R : ℕ
  /-- Height shift between predecessor and current mode components. -/
  Δ : ℕ
  /-- Top height in the mode-coherence schedule. -/
  Jst : ℕ
  /-- Core fraction retained by the side-event estimates. -/
  δs : ℝ

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc)

/-! ### The frozen evaluation on a pre-cell as a mode synthesis (blueprint lines 1934-1937, 1959) -/

theorem wave_measurable (m : Ms.Md) : Measurable (Ms.wave m) :=
  modeWave_measurable _ _ _ _ _ _ _

theorem wave_norm_le (m : Ms.Md) (y : ℝ) : ‖Ms.wave m y‖ ≤ 1 :=
  modeWave_norm_le _ _ _ _ _ _ _ y

/-- The augmented mode of `m` on the cell `J`. -/
noncomputable def cellMode (J : ℤ × ℤ) (m : Ms.Md) : ColumnL2 Ms.Md :=
  (augMode_memLp (dyadicGridCell_measurable Gd J.1 J.2) (dyadicGridCell_volume_ne_top Gd J)
    (Ms.wave_measurable m) (Ms.wave_norm_le m) (Ms.L.εM m) m).toLp

end ModeSystem

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ### Frozen evaluations as lifted ball outputs (blueprint lines 1959, 2112-2116) -/

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

section GaugeMultiplier
variable {d : ℕ}

/-- The slot positions `θ y_j = Q₀ (u + (j - l') v)` in the torus variables `x = (u, v)`,
`u = ϑ y_{l'}`, `v = ϑ t`, `ϑ = θ / Q₀`. -/
noncomputable def torusW (Q0 : ℕ) (l' j : Fin 4) (x : Fin (d + d) → ℝ) : Fin d → ℝ :=
  fun a => (Q0 : ℝ) * (x (Fin.castAdd d a) + (((j : ℕ) : ℝ) - ((l' : ℕ) : ℝ)) * x (Fin.natAdd d a))

/-- The carries `k_j = (1-j) n_0 + j n_1 - n_j` of a lattice tuple. -/
noncomputable def carryVec (n : Fin 4 → Fin d → ℤ) (j : Fin 4) : Fin d → ℝ :=
  fun a => (1 - ((j : ℕ) : ℝ)) * (n 0 a : ℝ) + ((j : ℕ) : ℝ) * (n 1 a : ℝ) - (n j a : ℝ)

/-- One carry piece of the gauge multiplier: the shifted branch profiles of the four slots times
the integer-carry character. -/
noncomputable def gaugeTerm (δ : ℝ) (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (ρ : Fin 4 → Fin d → ℝ) (n : Fin 4 → Fin d → ℤ) (x : Fin (d + d) → ℝ) : ℂ :=
  (∏ j : Fin 4, ∏ a, (branchProfile δ (torusW Q0 l' j x a - ρ j a - n j a) : ℂ)) *
    (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
      chartMatrixPhase C (torusW Q0 l' j x) (carryVec n j)) : ℂ)

/-- The branch lattice points `⌊θ y_j - ρ_j⌋`. -/
noncomputable def gaugeFloor (Q0 : ℕ) (l' : Fin 4) (ρ : Fin 4 → Fin d → ℝ)
    (x : Fin (d + d) → ℝ) : Fin 4 → Fin d → ℤ :=
  fun j a => ⌊torusW Q0 l' j x a - ρ j a⌋

/-- Blueprint `eq:gauge-cancel` (lines 1938-1944): the common progression multiplier, the carry
piece of the actual branch lattice points. -/
noncomputable def gaugeMult (δ : ℝ) (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (ρ : Fin 4 → Fin d → ℝ) (x : Fin (d + d) → ℝ) : ℂ :=
  gaugeTerm δ Q0 l' C ρ (gaugeFloor Q0 l' ρ x) x

/-- Only the carry piece of the actual lattice points is nonzero. -/
theorem gaugeTerm_eq_zero {δ : ℝ} (hδ : 0 < δ) (Q0 : ℕ) (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ) {n : Fin 4 → Fin d → ℤ}
    {x : Fin (d + d) → ℝ} (hn : n ≠ gaugeFloor Q0 l' ρ x) : gaugeTerm δ Q0 l' C ρ n x = 0 := by
  obtain ⟨j, a, hja⟩ : ∃ j a, n j a ≠ gaugeFloor Q0 l' ρ x j a := by
    by_contra h
    push Not at h
    exact hn (funext fun j => funext fun a => h j a)
  unfold gaugeTerm
  refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ j)
    (Finset.prod_eq_zero (Finset.mem_univ a) ?_)) _
  set s := torusW Q0 l' j x a - ρ j a
  have hfl : gaugeFloor Q0 l' ρ x j a = ⌊s⌋ := rfl
  rw [hfl] at hja
  have h1 := Int.floor_le s
  have h2 := Int.lt_floor_add_one s
  rcases lt_or_gt_of_ne hja with h | h
  · have : (n j a : ℝ) ≤ ⌊s⌋ - 1 := by exact_mod_cast (by omega : n j a ≤ ⌊s⌋ - 1)
    rw [branchProfile_eq_zero_of_ge hδ (by linarith)]; simp
  · have : (⌊s⌋ : ℝ) + 1 ≤ n j a := by exact_mod_cast (by omega : ⌊s⌋ + 1 ≤ n j a)
    rw [branchProfile_eq_zero_of_le hδ (by linarith)]; simp

/-- Near any point the multiplier is the sum of the carry pieces of the lattice tuples within one
step of the local lattice points. -/
noncomputable def gaugeBox (Q0 : ℕ) (l' : Fin 4) (ρ : Fin 4 → Fin d → ℝ)
    (x₀ : Fin (d + d) → ℝ) : Finset (Fin 4 → Fin d → ℤ) :=
  Fintype.piFinset fun j => Fintype.piFinset fun a =>
    Finset.Icc (gaugeFloor Q0 l' ρ x₀ j a - 1) (gaugeFloor Q0 l' ρ x₀ j a + 1)

theorem gaugeMult_eq_sum {δ : ℝ} (hδ : 0 < δ) (Q0 : ℕ) (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ) {x₀ x : Fin (d + d) → ℝ}
    (hx : gaugeFloor Q0 l' ρ x ∈ gaugeBox Q0 l' ρ x₀) :
    gaugeMult δ Q0 l' C ρ x = ∑ n ∈ gaugeBox Q0 l' ρ x₀, gaugeTerm δ Q0 l' C ρ n x := by
  rw [Finset.sum_eq_single_of_mem _ hx fun n _ hn => gaugeTerm_eq_zero hδ Q0 l' C ρ hn]
  rfl

end GaugeMultiplier

section GaugeMultiplier2
variable {d : ℕ}

/-- The slot position as a continuous linear map of the torus variables. -/
noncomputable def torusWL (Q0 : ℕ) (l' j : Fin 4) : (Fin (d + d) → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun a => (Q0 : ℝ) • (ContinuousLinearMap.proj (Fin.castAdd d a) +
    (((j : ℕ) : ℝ) - ((l' : ℕ) : ℝ)) • ContinuousLinearMap.proj (Fin.natAdd d a))

theorem torusWL_apply (Q0 : ℕ) (l' j : Fin 4) (x : Fin (d + d) → ℝ) :
    torusWL Q0 l' j x = torusW Q0 l' j x := by
  funext a
  simp [torusWL, torusW, mul_add]

theorem norm_torusWL_le (Q0 : ℕ) (l' j : Fin 4) : ‖torusWL (d := d) Q0 l' j‖ ≤ 4 * Q0 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [torusWL_apply]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  simp only [torusW, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have h1 : |x (Fin.castAdd d a)| ≤ ‖x‖ := by
    have := norm_le_pi_norm x (Fin.castAdd d a); rwa [Real.norm_eq_abs] at this
  have h2 : |x (Fin.natAdd d a)| ≤ ‖x‖ := by
    have := norm_le_pi_norm x (Fin.natAdd d a); rwa [Real.norm_eq_abs] at this
  have hj : |((j : ℕ) : ℝ) - ((l' : ℕ) : ℝ)| ≤ 3 := by
    have := j.2; have := l'.2
    rw [abs_le]; constructor <;>
    · have : ((j : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (j : ℕ) ≤ 3)
      have : ((l' : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (l' : ℕ) ≤ 3)
      have : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ (l' : ℕ) := Nat.cast_nonneg _
      linarith
  have hx := norm_nonneg x
  calc (Q0 : ℝ) * |x (Fin.castAdd d a) + (((j : ℕ) : ℝ) - ((l' : ℕ) : ℝ)) * x (Fin.natAdd d a)|
      ≤ Q0 * (|x (Fin.castAdd d a)| + |((j : ℕ) : ℝ) - ((l' : ℕ) : ℝ)| * |x (Fin.natAdd d a)|) := by
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_mul])
    _ ≤ Q0 * (‖x‖ + 3 * ‖x‖) := by gcongr
    _ = 4 * Q0 * ‖x‖ := by ring

/-- The carry phase of a lattice tuple as a continuous linear form of the torus variables. -/
noncomputable def carryPhaseL (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (n : Fin 4 → Fin d → ℤ) : (Fin (d + d) → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin 4, (slotCoeff j : ℝ) • ∑ a, ∑ b, ((C a b : ℝ) * carryVec n j b) •
    (ContinuousLinearMap.proj a).comp (torusWL Q0 l' j)

theorem carryPhaseL_apply (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (n : Fin 4 → Fin d → ℤ) (x : Fin (d + d) → ℝ) :
    carryPhaseL Q0 l' C n x = ∑ j : Fin 4, (slotCoeff j : ℝ) *
      chartMatrixPhase C (torusW Q0 l' j x) (carryVec n j) := by
  simp only [carryPhaseL, sum_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, torusWL_apply,
    chartMatrixPhase]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem gaugeTerm_contDiff {δ : ℝ} (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (ρ : Fin 4 → Fin d → ℝ) (n : Fin 4 → Fin d → ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaugeTerm δ Q0 l' C ρ n) := by
  have hprof : ContDiff ℝ (⊤ : ℕ∞) (branchProfile δ) := branchProfile_contDiff δ
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : Fin (d + d) → ℝ =>
      ∏ j : Fin 4, ∏ a, (branchProfile δ (torusW Q0 l' j x a - ρ j a - n j a) : ℂ) := by
    refine contDiff_prod fun j _ => contDiff_prod fun a _ => ?_
    refine Complex.ofRealCLM.contDiff.comp (hprof.comp ?_)
    have hlin : ContDiff ℝ (⊤ : ℕ∞) fun x : Fin (d + d) → ℝ => torusW Q0 l' j x a := by
      have : (fun x : Fin (d + d) → ℝ => torusW Q0 l' j x a) =
          fun x => (ContinuousLinearMap.proj a).comp (torusWL Q0 l' j) x := by
        funext x; simp [torusWL_apply]
      rw [this]
      exact ContinuousLinearMap.contDiff _
    exact (hlin.sub contDiff_const).sub contDiff_const
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x : Fin (d + d) → ℝ =>
      (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
        chartMatrixPhase C (torusW Q0 l' j x) (carryVec n j)) : ℂ) := by
    simp_rw [← carryPhaseL_apply]
    exact chart_fourierChar_smooth.comp (ContinuousLinearMap.contDiff _)
  exact h1.mul h2

/-- Points within `1 / (4 Q₀ + 1)` keep their lattice points within one step. -/
theorem gaugeFloor_mem_box (Q0 : ℕ) (l' : Fin 4) (ρ : Fin 4 → Fin d → ℝ)
    {x₀ x : Fin (d + d) → ℝ} (hx : ‖x - x₀‖ < 1 / (4 * Q0 + 1)) :
    gaugeFloor Q0 l' ρ x ∈ gaugeBox Q0 l' ρ x₀ := by
  simp only [gaugeBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro j a
  have hW : |torusW Q0 l' j x a - torusW Q0 l' j x₀ a| < 1 := by
    have h := (torusWL (d := d) Q0 l' j).le_opNorm (x - x₀)
    rw [map_sub, torusWL_apply, torusWL_apply] at h
    have ha := norm_le_pi_norm (torusW Q0 l' j x - torusW Q0 l' j x₀) a
    rw [Pi.sub_apply, Real.norm_eq_abs] at ha
    have hn := norm_torusWL_le (d := d) Q0 l' j
    have hpos : (0 : ℝ) < 4 * Q0 + 1 := by positivity
    calc |torusW Q0 l' j x a - torusW Q0 l' j x₀ a|
        ≤ ‖torusWL (d := d) Q0 l' j‖ * ‖x - x₀‖ := ha.trans h
      _ ≤ (4 * Q0) * ‖x - x₀‖ := by gcongr
      _ < (4 * Q0 + 1) * (1 / (4 * Q0 + 1)) := by
          have := norm_nonneg (x - x₀)
          calc (4 * (Q0 : ℝ)) * ‖x - x₀‖ ≤ (4 * Q0 + 1) * ‖x - x₀‖ := by gcongr; linarith
            _ < (4 * Q0 + 1) * (1 / (4 * Q0 + 1)) := by gcongr
      _ = 1 := by field_simp
  rw [abs_lt] at hW
  simp only [gaugeFloor]
  set s0 := torusW Q0 l' j x₀ a - ρ j a
  set s1 := torusW Q0 l' j x a - ρ j a
  have hf0 := Int.floor_le s0
  have hf1 := Int.lt_floor_add_one s0
  constructor
  · rw [Int.le_floor]; push_cast; linarith
  · have : s1 < ((⌊s0⌋ + 1 + 1 : ℤ) : ℝ) := by push_cast; linarith
    have := Int.floor_lt.mpr this
    omega

theorem gaugeMult_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (Q0 : ℕ) (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ) (x₀ : Fin (d + d) → ℝ) :
    gaugeMult δ Q0 l' C ρ =ᶠ[nhds x₀]
      fun x => ∑ n ∈ gaugeBox Q0 l' ρ x₀, gaugeTerm δ Q0 l' C ρ n x := by
  filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : (0 : ℝ) < 1 / (4 * Q0 + 1))]
    with x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  exact gaugeMult_eq_sum hδ Q0 l' C ρ (gaugeFloor_mem_box Q0 l' ρ hx)

/-- The common progression multiplier is smooth: near every point it is a finite sum of smooth
carry pieces, since the branch profiles vanish to infinite order at the cuts. -/
theorem gaugeMult_contDiff {δ : ℝ} (hδ : 0 < δ) (Q0 : ℕ) (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaugeMult δ Q0 l' C ρ) := by
  refine contDiff_iff_contDiffAt.mpr fun x₀ => ?_
  refine (ContDiff.contDiffAt ?_).congr_of_eventuallyEq (gaugeMult_eventuallyEq hδ Q0 l' C ρ x₀)
  exact ContDiff.sum fun n _ => gaugeTerm_contDiff Q0 l' C ρ n

end GaugeMultiplier2

section GaugeMultiplier3
variable {d : ℕ}

theorem torusW_affine (Q0 : ℕ) (l' j : Fin 4) (x : Fin (d + d) → ℝ) (a : Fin d) :
    torusW Q0 l' j x a = (1 - ((j : ℕ) : ℝ)) * torusW Q0 l' 0 x a +
      ((j : ℕ) : ℝ) * torusW Q0 l' 1 x a := by
  simp only [torusW, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  ring

/-- The carries of the lattice tuples in the local box are bounded by `18` when the offsets lie
in `[0, 1]`. -/
theorem carryVec_box_le (Q0 : ℕ) (l' : Fin 4) (ρ : Fin 4 → Fin d → ℝ)
    (hρ : ∀ j a, ρ j a ∈ Set.Icc (0 : ℝ) 1) {x₀ : Fin (d + d) → ℝ}
    {n : Fin 4 → Fin d → ℤ} (hn : n ∈ gaugeBox Q0 l' ρ x₀) (j : Fin 4) (b : Fin d) :
    |carryVec n j b| ≤ 18 := by
  simp only [gaugeBox, Fintype.mem_piFinset, Finset.mem_Icc] at hn
  set f := gaugeFloor Q0 l' ρ x₀
  set s : Fin 4 → ℝ := fun i => torusW Q0 l' i x₀ b - ρ i b
  have hfl : ∀ i, (f i b : ℝ) ≤ s i ∧ s i < f i b + 1 := fun i =>
    ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have hs : s j = (1 - ((j : ℕ) : ℝ)) * s 0 + ((j : ℕ) : ℝ) * s 1 +
      ((1 - ((j : ℕ) : ℝ)) * ρ 0 b + ((j : ℕ) : ℝ) * ρ 1 b - ρ j b) := by
    simp only [s]; rw [torusW_affine Q0 l' j x₀ b]; ring
  have hj3 : ((j : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (j : ℕ) ≤ 3)
  have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have e0 := hn 0 b; have e1 := hn 1 b; have ej := hn j b
  have r0 := hρ 0 b; have r1 := hρ 1 b; have rj := hρ j b
  have f0 := hfl 0; have f1 := hfl 1; have fj := hfl j
  have c0 : ((f 0 b : ℝ) - 1) ≤ n 0 b ∧ (n 0 b : ℝ) ≤ f 0 b + 1 :=
    ⟨by exact_mod_cast e0.1, by exact_mod_cast e0.2⟩
  have c1 : ((f 1 b : ℝ) - 1) ≤ n 1 b ∧ (n 1 b : ℝ) ≤ f 1 b + 1 :=
    ⟨by exact_mod_cast e1.1, by exact_mod_cast e1.2⟩
  have cj : ((f j b : ℝ) - 1) ≤ n j b ∧ (n j b : ℝ) ≤ f j b + 1 :=
    ⟨by exact_mod_cast ej.1, by exact_mod_cast ej.2⟩
  simp only [carryVec]
  rw [abs_le]
  constructor <;> rcases le_total ((j : ℕ) : ℝ) 1 with hj1 | hj1 <;>
    nlinarith only [r0.1, r0.2, r1.1, r1.2, rj.1, rj.2, f0.1, f0.2, f1.1, f1.2, fj.1, fj.2, c0.1,
      c0.2, c1.1, c1.2, cj.1, cj.2, hs, hj3]

theorem norm_carryPhaseL_le (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (n : Fin 4 → Fin d → ℤ) {Cm K : ℝ} (hCm0 : 0 ≤ Cm) (hK0 : 0 ≤ K)
    (hCm : ∀ a b, |(C a b : ℝ)| ≤ Cm) (hK : ∀ j b, |carryVec n j b| ≤ K) :
    ‖carryPhaseL Q0 l' C n‖ ≤ 8 * ((d : ℝ) * ((d : ℝ) * (Cm * K * (4 * Q0)))) := by
  have hinner : ∀ j : Fin 4, ‖∑ a, ∑ b, ((C a b : ℝ) * carryVec n j b) •
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a).comp
        (torusWL (d := d) Q0 l' j)‖ ≤ (d : ℝ) * ((d : ℝ) * (Cm * K * (4 * Q0))) := by
    intro j
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖∑ b, ((C a b : ℝ) * carryVec n j b) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a).comp
            (torusWL (d := d) Q0 l' j)‖
        ≤ ∑ _a : Fin d, (d : ℝ) * (Cm * K * (4 * Q0)) := by
          refine Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_
          calc ∑ b, ‖((C a b : ℝ) * carryVec n j b) •
                (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a).comp
                  (torusWL (d := d) Q0 l' j)‖
              ≤ ∑ _b : Fin d, Cm * K * (4 * Q0) := by
                refine Finset.sum_le_sum fun b _ => ?_
                rw [norm_smul, Real.norm_eq_abs, abs_mul]
                have hp : ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) a).comp
                    (torusWL (d := d) Q0 l' j)‖ ≤ 4 * Q0 := by
                  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
                  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
                  refine (norm_le_pi_norm _ a).trans
                    (((torusWL (d := d) Q0 l' j).le_opNorm x).trans ?_)
                  exact mul_le_mul_of_nonneg_right (norm_torusWL_le Q0 l' j) (norm_nonneg _)
                exact mul_le_mul (mul_le_mul (hCm a b) (hK j b) (abs_nonneg _) hCm0) hp
                  (norm_nonneg _) (mul_nonneg hCm0 hK0)
              _ = (d : ℝ) * (Cm * K * (4 * Q0)) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (d : ℝ) * ((d : ℝ) * (Cm * K * (4 * Q0))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold carryPhaseL
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 4, ‖(slotCoeff j : ℝ) • ∑ a, ∑ b, ((C a b : ℝ) * carryVec n j b) •
        (ContinuousLinearMap.proj a).comp (torusWL Q0 l' j)‖
      ≤ ∑ j : Fin 4, |(slotCoeff j : ℝ)| * ((d : ℝ) * ((d : ℝ) * (Cm * K * (4 * Q0)))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hinner j) (abs_nonneg _)
    _ = 8 * ((d : ℝ) * ((d : ℝ) * (Cm * K * (4 * Q0)))) := by
        simp [Fin.sum_univ_four, slotCoeff]
        ring

end GaugeMultiplier3

section GaugeMultiplier4
variable {d : ℕ}

/-- The derivative constant of the branch profiles up to order `m`. -/
noncomputable def profR (δ : ℝ) (m : ℕ) : ℝ := bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ)

theorem profR_nonneg {δ : ℝ} (hδ : 0 < δ) (m : ℕ) : 0 ≤ profR δ m := by
  unfold profR; have := one_le_bumpConst; positivity

theorem gaugeTerm_eq_mul (δ : ℝ) (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (ρ : Fin 4 → Fin d → ℝ) (n : Fin 4 → Fin d → ℤ) :
    gaugeTerm δ Q0 l' C ρ n = fun x => (∏ j : Fin 4, (fun y : Fin (d + d) → ℝ =>
        chartCoordinateProduct (branchProfile δ)
          (torusWL Q0 l' j y - fun a => ρ j a + n j a)) x) *
      (Real.fourierChar (carryPhaseL Q0 l' C n x) : ℂ) := by
  funext x
  simp only [gaugeTerm, carryPhaseL_apply, chartCoordinateProduct, torusWL_apply, Pi.sub_apply]
  congr 1
  refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun a _ => ?_
  congr 2
  ring

/-- The derivatives of one carry piece: `‖D^m term‖ ≤ (16 Q₀ d R + 2π ‖L_n‖)^m`. -/
theorem gaugeTerm_deriv_le {δ : ℝ} (hδ : 0 < δ) (Q0 : ℕ) (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ) (n : Fin 4 → Fin d → ℤ)
    (m : ℕ) (x : Fin (d + d) → ℝ) :
    ‖iteratedFDeriv ℝ m (gaugeTerm δ Q0 l' C ρ n) x‖ ≤
      (4 * (4 * Q0 * (d * profR δ m)) + 2 * Real.pi * ‖carryPhaseL Q0 l' C n‖) ^ m := by
  set R := profR δ m
  have hR : 0 ≤ R := profR_nonneg hδ m
  have hcp : ContDiff ℝ (⊤ : ℕ∞) (chartCoordinateProduct (d := d) (branchProfile δ)) :=
    chartCoordinateProduct_smooth (branchProfile_contDiff δ)
  -- one slot factor
  have hQ : ∀ j : Fin 4, ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (d + d) → ℝ =>
      chartCoordinateProduct (branchProfile δ) (torusWL Q0 l' j y - fun a => ρ j a + n j a)) :=
    fun j => hcp.comp ((ContinuousLinearMap.contDiff _).sub contDiff_const)
  have hQd : ∀ j : Fin 4, ∀ i ≤ m, ‖iteratedFDeriv ℝ i (fun y : Fin (d + d) → ℝ =>
      chartCoordinateProduct (branchProfile δ)
        (torusWL Q0 l' j y - fun a => ρ j a + n j a)) x‖ ≤ (4 * Q0 * (d * R)) ^ i := by
    intro j i hi
    set c : Fin d → ℝ := fun a => ρ j a + n j a
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin d → ℝ => chartCoordinateProduct (branchProfile δ)
        (z - c)) := hcp.comp (contDiff_id.sub contDiff_const)
    have e : (fun y : Fin (d + d) → ℝ => chartCoordinateProduct (branchProfile δ)
        (torusWL Q0 l' j y - c)) =
        (fun z : Fin d → ℝ => chartCoordinateProduct (branchProfile δ) (z - c)) ∘
          torusWL Q0 l' j := rfl
    rw [e, (torusWL Q0 l' j).iteratedFDeriv_comp_right hg x (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDeriv_comp_sub]
    have h1 := chartCoordinateProduct_derivative_geometric (branchProfile_contDiff δ)
      (torusWL Q0 l' j x - c) hR (m := i) fun k hk y =>
        branchProfile_deriv_le hδ (hk.trans hi) y
    have h2 : ‖torusWL (d := d) Q0 l' j‖ ^ i ≤ (4 * (Q0 : ℝ)) ^ i :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_torusWL_le Q0 l' j) i
    calc ‖iteratedFDeriv ℝ i (chartCoordinateProduct (branchProfile δ))
          (torusWL Q0 l' j x - c)‖ * ‖torusWL (d := d) Q0 l' j‖ ^ i
        ≤ ((d : ℝ) * R) ^ i * (4 * Q0) ^ i := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (4 * Q0 * (d * R)) ^ i := by rw [← mul_pow]; ring
  -- the product of the four slot factors
  have hP := fun i (hi : i ≤ m) =>
    finite_product_derivative_geometric (Finset.univ : Finset (Fin 4))
    (fun j (y : Fin (d + d) → ℝ) => chartCoordinateProduct (branchProfile δ)
      (torusWL Q0 l' j y - fun a => ρ j a + n j a)) (fun j _ => hQ j) x
    (by positivity : (0 : ℝ) ≤ 4 * Q0 * (d * R)) (m := i)
    (fun j _ k hk => hQd j k (hk.trans hi))
  -- the character
  have hE : ∀ i, ‖iteratedFDeriv ℝ i (fun y => (Real.fourierChar (carryPhaseL Q0 l' C n y) : ℂ))
      x‖ ≤ (2 * Real.pi * ‖carryPhaseL Q0 l' C n‖) ^ i := by
    intro i
    have h := chart_linear_phase_derivative_bound (carryPhaseL Q0 l' C n) 0 x i
    simpa using h
  rw [gaugeTerm_eq_mul]
  have hprod : ContDiff ℝ (⊤ : ℕ∞) fun y : Fin (d + d) → ℝ => ∏ j : Fin 4,
      chartCoordinateProduct (branchProfile δ) (torusWL Q0 l' j y - fun a => ρ j a + n j a) :=
    contDiff_prod fun j _ => hQ j
  have hchar : ContDiff ℝ (⊤ : ℕ∞) fun y : Fin (d + d) → ℝ =>
      (Real.fourierChar (carryPhaseL Q0 l' C n y) : ℂ) :=
    chart_fourierChar_smooth.comp (ContinuousLinearMap.contDiff _)
  have h := derivative_product_geometric hprod hchar x (m := m)
    (R := 4 * (4 * Q0 * (d * R))) (T := 2 * Real.pi * ‖carryPhaseL Q0 l' C n‖)
    (by positivity) (by positivity) (fun i hi => by
      have := hP i hi
      simpa [Finset.card_univ, Fintype.card_fin, Finset.prod_apply] using this)
    (fun i _ => hE i)
  simpa [Finset.prod_apply] using h

end GaugeMultiplier4

section GaugeMultiplier5
variable {d : ℕ}

theorem gaugeBox_card (Q0 : ℕ) (l' : Fin 4) (ρ : Fin 4 → Fin d → ℝ) (x₀ : Fin (d + d) → ℝ) :
    (gaugeBox Q0 l' ρ x₀).card = 3 ^ (4 * d) := by
  simp only [gaugeBox, Fintype.card_piFinset, Int.card_Icc]
  have : ∀ (j : Fin 4) (a : Fin d), (gaugeFloor Q0 l' ρ x₀ j a + 1 + 1 -
      (gaugeFloor Q0 l' ρ x₀ j a - 1)).toNat = 3 := fun j a => by omega
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  ring_nf

/-- Blueprint lines 1942-1944 ("its Gevrey and absolute Fourier bounds are uniform in offsets"):
for offsets in `[0, 1]` and `|C_{ab}| ≤ C_m`, the derivatives of the multiplier obey
`‖D^m M‖ ≤ 3^{4d} (16 Q₀ d R + 2π · 8 d² C_m · 18 · 4 Q₀)^m` everywhere. -/
theorem gaugeMult_deriv_le {δ : ℝ} (hδ : 0 < δ) (Q0 : ℕ) (l' : Fin 4)
    (C : Matrix (Fin d) (Fin d) ℚ) (ρ : Fin 4 → Fin d → ℝ)
    (hρ : ∀ j a, ρ j a ∈ Set.Icc (0 : ℝ) 1) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ a b, |(C a b : ℝ)| ≤ Cm) (m : ℕ) (x : Fin (d + d) → ℝ) :
    ‖iteratedFDeriv ℝ m (gaugeMult δ Q0 l' C ρ) x‖ ≤
      3 ^ (4 * d) * (4 * (4 * Q0 * (d * profR δ m)) +
        2 * Real.pi * (8 * ((d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0)))))) ^ m := by
  have hev := Filter.EventuallyEq.iteratedFDeriv ℝ (gaugeMult_eventuallyEq hδ Q0 l' C ρ x) m
  rw [Filter.EventuallyEq.eq_of_nhds hev,
    iteratedFDeriv_sum fun n _ => (gaugeTerm_contDiff Q0 l' C ρ n).of_le (by exact_mod_cast le_top)]
  rw [Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ gaugeBox Q0 l' ρ x, ‖iteratedFDeriv ℝ m (gaugeTerm δ Q0 l' C ρ n) x‖
      ≤ ∑ _n ∈ gaugeBox Q0 l' ρ x, (4 * (4 * Q0 * (d * profR δ m)) +
          2 * Real.pi * (8 * ((d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0)))))) ^ m := by
        refine Finset.sum_le_sum fun n hn => (gaugeTerm_deriv_le hδ Q0 l' C ρ n m x).trans ?_
        have hL := norm_carryPhaseL_le Q0 l' C n hCm0 (by norm_num) hCm
          (fun j b => carryVec_box_le Q0 l' ρ hρ hn j b)
        have := profR_nonneg hδ m
        gcongr
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, gaugeBox_card]
        push_cast; ring

end GaugeMultiplier5

section GaugeMultiplier6
variable {d : ℕ}

/-- Blueprint line 1942 ("for fixed carries the right side is an integer character on
`(ϑ y_{l'}, ϑ t)` ... because `Q₀` clears `C_z`"): the multiplier is `1`-periodic in the torus
variables. -/
theorem gaugeMult_periodic (δ : ℝ) (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (ρ : Fin 4 → Fin d → ℝ) (hQ : ∀ a b, ∃ z : ℤ, (Q0 : ℝ) * (C a b : ℝ) = z)
    (x : Fin (d + d) → ℝ) (e : Fin (d + d) → ℤ) :
    gaugeMult δ Q0 l' C ρ (x + fun i => (e i : ℝ)) = gaugeMult δ Q0 l' C ρ x := by
  choose z hz using hQ
  set mv : Fin 4 → Fin d → ℤ := fun j a =>
    (Q0 : ℤ) * (e (Fin.castAdd d a) + (((j : ℕ) : ℤ) - ((l' : ℕ) : ℤ)) * e (Fin.natAdd d a))
  have hW : ∀ j a, torusW Q0 l' j (x + fun i => (e i : ℝ)) a = torusW Q0 l' j x a + mv j a := by
    intro j a
    simp only [torusW, mv, Pi.add_apply]
    push_cast; ring
  have hfl : gaugeFloor Q0 l' ρ (x + fun i => (e i : ℝ)) = gaugeFloor Q0 l' ρ x + mv := by
    funext j a
    simp only [gaugeFloor, Pi.add_apply, hW]
    rw [show torusW Q0 l' j x a + (mv j a : ℝ) - ρ j a = (torusW Q0 l' j x a - ρ j a) + (mv j a : ℤ)
      by ring, Int.floor_add_intCast]
  have hk : ∀ j, carryVec (gaugeFloor Q0 l' ρ x + mv) j = carryVec (gaugeFloor Q0 l' ρ x) j := by
    intro j; funext b
    simp only [carryVec, Pi.add_apply, mv, Fin.val_zero, Fin.val_one]
    push_cast; ring
  unfold gaugeMult gaugeTerm
  rw [hfl]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun a _ => ?_
    rw [hW]
    simp only [Pi.add_apply]
    push_cast
    ring_nf
  · simp only [hk]
    -- the phase changes by an integer
    have hint : ∃ N : ℤ, ∑ j : Fin 4, (slotCoeff j : ℝ) *
        chartMatrixPhase C (torusW Q0 l' j (x + fun i => (e i : ℝ)))
          (carryVec (gaugeFloor Q0 l' ρ x) j) =
        ∑ j : Fin 4, (slotCoeff j : ℝ) *
          chartMatrixPhase C (torusW Q0 l' j x) (carryVec (gaugeFloor Q0 l' ρ x) j) + N := by
      refine ⟨∑ j : Fin 4, ∑ a, ∑ b, slotCoeff j * ((e (Fin.castAdd d a) +
          (((j : ℕ) : ℤ) - ((l' : ℕ) : ℤ)) * e (Fin.natAdd d a)) * z a b *
          ((1 - ((j : ℕ) : ℤ)) * gaugeFloor Q0 l' ρ x 0 b + ((j : ℕ) : ℤ) *
            gaugeFloor Q0 l' ρ x 1 b - gaugeFloor Q0 l' ρ x j b)), ?_⟩
      push_cast
      simp only [chartMatrixPhase, hW, carryVec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => ?_
      rw [← hz a b]
      simp only [mv]
      push_cast
      ring
    obtain ⟨N, hN⟩ := hint
    rw [hN, chart_fourierChar_add_int]

end GaugeMultiplier6

section GaugeMultiplier7
variable {d : ℕ}

theorem gaugeMult_norm_le (δ : ℝ) (Q0 : ℕ) (l' : Fin 4) (C : Matrix (Fin d) (Fin d) ℚ)
    (ρ : Fin 4 → Fin d → ℝ) (x : Fin (d + d) → ℝ) : ‖gaugeMult δ Q0 l' C ρ x‖ ≤ 1 := by
  unfold gaugeMult gaugeTerm
  rw [norm_mul, Circle.norm_coe, mul_one, norm_prod]
  refine Finset.prod_le_one₀ (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun a _ => norm_nonneg _) fun a _ => ?_
  have := branchProfile_mem δ (torusW Q0 l' j x a - ρ j a - gaugeFloor Q0 l' ρ x j a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

end GaugeMultiplier7

/-- The branch profile vanishes at both cuts with slope at most `R = profR δ 1`:
`b_δ(s) ≤ R |s|` and `b_δ(s) ≤ R |1 - s|`. -/
theorem branchProfile_le_edge {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    branchProfile δ s ≤ profR δ 1 * |s| ∧ branchProfile δ s ≤ profR δ 1 * |1 - s| := by
  have hdiff : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ (branchProfile δ) x := fun x _ =>
    ((branchProfile_contDiff δ).differentiable (by simp)).differentiableAt
  have hbd : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (branchProfile δ) x‖ ≤ profR δ 1 := by
    intro x _
    have h := branchProfile_deriv_le hδ (m := 1) (i := 1) le_rfl x
    rw [iteratedDeriv_one, pow_one] at h
    rw [Real.norm_eq_abs]; exact h
  have hlip := fun x y => convex_univ.norm_image_sub_le_of_norm_deriv_le hdiff hbd
    (Set.mem_univ x) (Set.mem_univ y)
  have h0 : branchProfile δ 0 = 0 := branchProfile_eq_zero_of_le hδ le_rfl
  have h1 : branchProfile δ 1 = 0 := branchProfile_eq_zero_of_ge hδ le_rfl
  constructor
  · have := hlip 0 s
    rw [h0, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, sub_zero] at this
    exact (le_abs_self _).trans this
  · have := hlip 1 s
    rw [h1, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_sub_comm] at this
    exact (le_abs_self _).trans this

theorem prod_le_factor {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) {i : ι} (hi : i ∈ s) : ∏ j ∈ s, f j ≤ f i := by
  classical
  rw [← Finset.mul_prod_erase s f hi]
  exact mul_le_of_le_one_right (h0 i hi) (Finset.prod_le_one₀
    (fun j hj => h0 j (Finset.mem_of_mem_erase hj)) fun j hj => h1 j (Finset.mem_of_mem_erase hj))

section GaugeMultiplier8
variable {d : ℕ}

/-- The torus point `(ϑ y_{l'}, ϑ t)`, `ϑ = θ / Q₀`, of the progression `y_j = x + j t`. -/
noncomputable def torusPt (θ : Fin d → ℝ) (Q0 : ℕ) (l' : Fin 4) (x t : ℝ) : Fin (d + d) → ℝ :=
  Fin.append (fun a => θ a * (x + ((l' : ℕ) : ℝ) * t) / Q0) (fun a => θ a * t / Q0)

theorem torusW_torusPt (θ : Fin d → ℝ) {Q0 : ℕ} (hQ0 : 0 < Q0) (l' j : Fin 4) (x t : ℝ) :
    torusW Q0 l' j (torusPt θ Q0 l' x t) = fun a => θ a * (x + ((j : ℕ) : ℝ) * t) := by
  funext a
  have hQ : (Q0 : ℝ) ≠ 0 := by exact_mod_cast hQ0.ne'
  simp only [torusW, torusPt, Fin.append_left, Fin.append_right]
  field_simp
  ring

theorem gaugeCarry_eq_carryVec (θ : Fin d → ℝ) {Q0 : ℕ} (hQ0 : 0 < Q0) (l' : Fin 4)
    (ρ : Fin 4 → Fin d → ℝ) (x t : ℝ) (j : Fin 4) :
    gaugeCarry θ ρ x t j = carryVec (gaugeFloor Q0 l' ρ (torusPt θ Q0 l' x t)) j := by
  funext a
  have hW := fun i => congrFun (torusW_torusPt θ hQ0 l' i x t) a
  simp only [gaugeCarry, carryVec, gaugeFloor, hW, branchLift, Int.fract]
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]
  ring

/-- Blueprint lines 1942-1944 and 2479 ("on all true cutoff supports the four gauge factors have
the bounded smooth periodic multiplier"), with the thin enlargement of ErrorReport 2026-10-12:
the four true cutoffs times the four gauge phases `e(c_j p_{ρ_j}(y_j))` differ from the four true
cutoffs times the multiplier with cutoff parameter `δ''` by at most `8 d δ'' R_δ`. -/
theorem gauge_factors_eq_mult {δ δ'' : ℝ} (hδ : 0 < δ) (hδ'' : 0 < δ'') (θ : Fin d → ℝ)
    (C : Matrix (Fin d) (Fin d) ℚ) (lam : ℝ) {Q0 : ℕ} (hQ0 : 0 < Q0) (l' : Fin 4)
    (ρ : Fin 4 → Fin d → ℝ) (x t : ℝ) :
    ‖(∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
        (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) * (lam * (x + ((j : ℕ) : ℝ) * t) ^ 2 +
          chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
            (branchLift (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))))) : ℂ) -
      (∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
        gaugeMult δ'' Q0 l' C ρ (torusPt θ Q0 l' x t)‖ ≤ 8 * d * δ'' * profR δ 1 := by
  set s : Fin 4 → Fin d → ℝ := fun j a => Int.fract (θ a * (x + ((j : ℕ) : ℝ) * t) - ρ j a)
  have hW := fun j => torusW_torusPt θ hQ0 l' j x t
  have hWa : ∀ j a, torusW Q0 l' j (torusPt θ Q0 l' x t) a = θ a * (x + ((j : ℕ) : ℝ) * t) :=
    fun j a => congrFun (hW j) a
  -- the multiplier at the torus point
  have hM : gaugeMult δ'' Q0 l' C ρ (torusPt θ Q0 l' x t) =
      (∏ j : Fin 4, ∏ a, (branchProfile δ'' (s j a) : ℂ)) *
        (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
          chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
            (gaugeCarry θ ρ x t j)) : ℂ) := by
    unfold gaugeMult gaugeTerm
    simp only [gaugeCarry_eq_carryVec θ hQ0 l' ρ x t]
    simp only [hW]
    congr 1
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun a _ => ?_
    simp only [s, gaugeFloor, hWa, Int.fract]
  rw [gauge_cancel θ C lam ρ x t, hM]
  set E := (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
    chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) (gaugeCarry θ ρ x t j)) : ℂ)
  set χ : Fin 4 → ℝ := fun j => branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
  have hχ : ∀ j, χ j = ∏ a, branchProfile δ (s j a) := fun j => rfl
  have hχ01 : ∀ j, χ j ∈ Set.Icc (0 : ℝ) 1 := fun j => branchCutoffValue_mem _ _ _
  have hp01 : ∀ j a, branchProfile δ'' (s j a) ∈ Set.Icc (0 : ℝ) 1 :=
    fun j a => branchProfile_mem _ _
  -- rewrite the difference
  have hdiff : (∏ j : Fin 4, (χ j : ℂ)) * E - (∏ j : Fin 4, (χ j : ℂ)) *
      ((∏ j : Fin 4, ∏ a, (branchProfile δ'' (s j a) : ℂ)) * E) =
      (((∏ j : Fin 4, χ j) * (1 - ∏ j : Fin 4, ∏ a, branchProfile δ'' (s j a)) : ℝ) : ℂ) * E := by
    push_cast; ring
  rw [hdiff, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hP0 : 0 ≤ ∏ j : Fin 4, χ j := Finset.prod_nonneg fun j _ => (hχ01 j).1
  have hQ1 : ∏ j : Fin 4, ∏ a, branchProfile δ'' (s j a) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => Finset.prod_nonneg fun a _ => (hp01 j a).1)
      fun j _ => Finset.prod_le_one₀ (fun a _ => (hp01 j a).1) fun a _ => (hp01 j a).2
  rw [abs_of_nonneg (mul_nonneg hP0 (by linarith))]
  -- the layer estimate
  have hlayer : ∀ j a, (∏ j : Fin 4, χ j) * (1 - branchProfile δ'' (s j a)) ≤
      2 * δ'' * profR δ 1 := by
    intro j a
    have hs := Int.fract_nonneg (θ a * (x + ((j : ℕ) : ℝ) * t) - ρ j a)
    have hs1 := Int.fract_lt_one (θ a * (x + ((j : ℕ) : ℝ) * t) - ρ j a)
    have hR := profR_nonneg hδ 1
    have hPle : (∏ j : Fin 4, χ j) ≤ branchProfile δ (s j a) := by
      calc (∏ j : Fin 4, χ j) ≤ χ j := prod_le_factor _ _ (fun i _ => (hχ01 i).1)
            (fun i _ => (hχ01 i).2) (Finset.mem_univ j)
        _ = ∏ b, branchProfile δ (s j b) := hχ j
        _ ≤ branchProfile δ (s j a) := prod_le_factor _ _
            (fun b _ => (branchProfile_mem δ _).1) (fun b _ => (branchProfile_mem δ _).2)
            (Finset.mem_univ a)
    by_cases hin : 2 * δ'' ≤ s j a ∧ s j a ≤ 1 - 2 * δ''
    · rw [branchProfile_eq_one hδ'' hin.1 hin.2, sub_self, mul_zero]; positivity
    · have hedge : branchProfile δ (s j a) ≤ 2 * δ'' * profR δ 1 := by
        obtain ⟨e1, e2⟩ := branchProfile_le_edge hδ (s j a)
        rcases not_and_or.mp hin with h | h
        · rw [not_le] at h
          rw [abs_of_nonneg hs] at e1
          nlinarith
        · rw [not_le] at h
          rw [abs_of_nonneg (by linarith)] at e2
          nlinarith
      have h1p : 1 - branchProfile δ'' (s j a) ≤ 1 := by linarith [(hp01 j a).1]
      have h1p0 : 0 ≤ 1 - branchProfile δ'' (s j a) := by linarith [(hp01 j a).2]
      calc (∏ j : Fin 4, χ j) * (1 - branchProfile δ'' (s j a))
          ≤ (∏ j : Fin 4, χ j) * 1 := mul_le_mul_of_nonneg_left h1p hP0
        _ ≤ 2 * δ'' * profR δ 1 := by rw [mul_one]; exact hPle.trans hedge
  -- sum over the slots and coordinates
  have hsum := one_sub_prod_le_sum (Finset.univ : Finset (Fin 4 × Fin d))
    (fun p => branchProfile δ'' (s p.1 p.2)) (fun p _ => (hp01 p.1 p.2).1)
    (fun p _ => (hp01 p.1 p.2).2)
  rw [← Finset.univ_product_univ, Finset.prod_product] at hsum
  calc (∏ j : Fin 4, χ j) * (1 - ∏ j : Fin 4, ∏ a, branchProfile δ'' (s j a))
      ≤ (∏ j : Fin 4, χ j) * ∑ p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ Finset.univ,
          (1 - branchProfile δ'' (s p.1 p.2)) := mul_le_mul_of_nonneg_left hsum hP0
    _ = ∑ p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin d)),
          (∏ j : Fin 4, χ j) * (1 - branchProfile δ'' (s p.1 p.2)) := Finset.mul_sum _ _ _
    _ ≤ ∑ _p ∈ (Finset.univ : Finset (Fin 4)) ×ˢ (Finset.univ : Finset (Fin d)),
          2 * δ'' * profR δ 1 := Finset.sum_le_sum fun p _ => hlayer p.1 p.2
    _ = 8 * d * δ'' * profR δ 1 := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Finset.card_univ,
          Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end GaugeMultiplier8

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

theorem fourierChar_sum_coe {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (Real.fourierChar (∑ i ∈ s, a i) : ℂ) = ∏ i ∈ s, (Real.fourierChar (a i) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, Circle.coe_mul, ih]

/-- The four gauge factors of a common chart tag at the progression points
`y_j = x + j t` are the four true cutoffs times the gauge phase of `eq:gauge-cancel`. -/
theorem gauge_prod_eq (z : ChartTag) (δ : ℝ) (ρ : Fin 4 → Fin z.dim → ℝ) (x t : ℝ) :
    ∏ j : Fin 4, ((centerCut z δ (ρ j) (x + ((j : ℕ) : ℝ) * t) : ℂ) *
      (Real.fourierChar (((slotCoeff j : ℤ) : ℝ) * centerPhase z (ρ j) (x + ((j : ℕ) : ℝ) * t)) :
        ℂ)) =
    (∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => z.θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
      (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) * (z.lam * (x + ((j : ℕ) : ℝ) * t) ^ 2 +
        chartMatrixPhase z.C (fun a => z.θ a * (x + ((j : ℕ) : ℝ) * t))
          (branchLift (ρ j) (fun a => z.θ a * (x + ((j : ℕ) : ℝ) * t))))) : ℂ) := by
  rw [Finset.prod_mul_distrib, fourierChar_sum_coe]
  rfl


/-! ## Primaries and first-match cells on the main columns (blueprint line 1888) -/

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The primaries of a role (slot `l`, outer ball of the group `G` at the ball level `j`) at the
cell `I`: the main columns available to the maximal pad `P` and the rank `L + j` of the outer ball
(blueprint line 1888). -/
noncomputable def primaries (l : Fin 4) (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ)
    (d : bf.Vtx) (I : ℤ × ℤ) : Finset (bf.Lab ⊕ Fin fp.Mc) :=
  mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j) (fp.bmask I G j fp.P) d

/-- The labels of every individual ball projection of the role are primaries. -/
theorem ballLabels_subset_primaries (l : Fin 4) (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ)
    (d : bf.Vtx) (I : ℤ × ℤ) {p : ℕ} (hp : p ≤ fp.P) :
    mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j) (fp.bmask I G j p) d ⊆
      fp.primaries l s G j d I :=
  mainLabelsM_mono s I _ (fun x hx => fp.bmask_pad_mono I G j hp x hx) d

/-- The primaries are nested in depth (blueprint line 1888: "the mode lists, including primaries
whose coefficients are zero, are nested"; a primary keeps its role on every descendant). -/
theorem primaries_desc (l : Fin 4) (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ) (d : bf.Vtx)
    {I J : ℤ × ℤ} (hI : I ∈ A.cells) (hJ : J ∈ A.cells)
    (hJI : dyadicGridCell A.G J.1 J.2 ⊆ dyadicGridCell A.G I.1 I.2) {v : bf.Lab ⊕ Fin fp.Mc}
    (hv : v ∈ fp.primaries l s G j d I) : v ∈ fp.primaries l s G j d J := by
  obtain ⟨hvL, hvM⟩ := mem_mainLabelsM.mp hv
  refine mem_mainLabelsM.mpr ⟨?_, ?_⟩
  · rcases v with x | n
    · obtain ⟨hl, hav⟩ := (mem_mainLabels.mp hvL : (bf.origCols l).avail I x)
      exact mem_mainLabels.mpr (⟨hl, bf.occAvail_desc hJ hJI hav⟩ : (bf.origCols l).avail J x)
    · obtain ⟨hn, hb, hr⟩ := (mem_mainLabels.mp hvL : ∃ hn : (n : ℕ) < s.length, _)
      exact mem_mainLabels.mpr (⟨hn, hJI.trans hb, hr⟩ : ∃ hn : (n : ℕ) < s.length, _)
  · rcases v with x | n
    · obtain ⟨-, hav⟩ := (mem_mainLabels.mp hvL : (bf.origCols l).avail I x)
      change fp.bmask J G j fp.P (bf.vtxAt J x)
      rw [bf.vtxAt_desc hJ hI hJI hav]
      exact fp.bmask_mono hJ hI hJI G j fp.P _ hvM
    · exact fp.bmask_mono hJ hI hJI G j fp.P _ hvM

open Classical in
/-- The first-match cells of a primary among a family `cs` of active cells: the maximal cells of
`cs` at which it is a primary (blueprint line 1888: "at its first match on `I₀`"). -/
noncomputable def firstCells (cs : Finset (ℤ × ℤ)) (l : Fin 4) (s : List (CatCol bf.Vtx))
    (G : bf.Grp) (j : ℕ) (d : bf.Vtx) (v : bf.Lab ⊕ Fin fp.Mc) : Finset (ℤ × ℤ) :=
  maxCells A.G (cs.filter fun I => v ∈ fp.primaries l s G j d I)

/-- A primary at a cell of the family has a first-match cell containing the cell. -/
theorem exists_firstCell (cs : Finset (ℤ × ℤ)) (l : Fin 4) (s : List (CatCol bf.Vtx))
    (G : bf.Grp) (j : ℕ) (d : bf.Vtx) {v : bf.Lab ⊕ Fin fp.Mc} {I : ℤ × ℤ} (hI : I ∈ cs)
    (hv : v ∈ fp.primaries l s G j d I) :
    ∃ I₀ ∈ fp.firstCells cs l s G j d v,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I₀.1 I₀.2 := by
  classical
  exact exists_maxCell_above (Finset.mem_filter.mpr ⟨hI, hv⟩)

/-- The first-match cell of a primary above a cell is unique. -/
theorem firstCell_unique (cs : Finset (ℤ × ℤ)) (l : Fin 4) (s : List (CatCol bf.Vtx))
    (G : bf.Grp) (j : ℕ) (d : bf.Vtx) {v : bf.Lab ⊕ Fin fp.Mc} {I₀ I₁ : ℤ × ℤ}
    (h₀ : I₀ ∈ fp.firstCells cs l s G j d v) (h₁ : I₁ ∈ fp.firstCells cs l s G j d v) {y : ℝ}
    (hy₀ : y ∈ dyadicGridCell A.G I₀.1 I₀.2) (hy₁ : y ∈ dyadicGridCell A.G I₁.1 I₁.2) :
    I₀ = I₁ := by
  classical
  exact maxCells_eq_of_mem h₀ h₁ hy₀ hy₁

/-- A primary is a primary on every active descendant of its first-match cell (blueprint line
1888: "keep its modes and labels on every descendant"). -/
theorem primaries_of_firstCell (cs : Finset (ℤ × ℤ)) (hcs : cs ⊆ A.cells) (l : Fin 4)
    (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ) (d : bf.Vtx) {v : bf.Lab ⊕ Fin fp.Mc}
    {I₀ I : ℤ × ℤ} (h₀ : I₀ ∈ fp.firstCells cs l s G j d v) (hI : I ∈ A.cells)
    (hII₀ : dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I₀.1 I₀.2) :
    v ∈ fp.primaries l s G j d I := by
  classical
  obtain ⟨hI₀f, -⟩ := mem_maxCells.mp h₀
  obtain ⟨hI₀cs, hv⟩ := Finset.mem_filter.mp hI₀f
  exact fp.primaries_desc l s G j d (hcs hI₀cs) hI hII₀ hv

end ActiveSetup.BasicFamilies.FamParams


/-! ## The first-match expansion on the main columns (blueprint lines 1888, 1903-1910) -/

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- A walk of length `n` in the tag graph of the original basic columns collapses to a path of at
most `n` tag edges between the endpoint tags (equal-tag steps are removed). -/
theorem tagWalk_path (Hed : ℝ) (s : ℤ) :
    ∀ (n : ℕ) (x y : bf.Vtx), reachIn (bf.tagGraphEdge Hed) s n x y →
      ∃ L ≤ n, ∃ v : Fin (L + 1) → ChartTag, v 0 = bf.vtag x ∧ v (Fin.last L) = bf.vtag y ∧
        (∀ i, ∃ w : bf.Vtx, v i = bf.vtag w) ∧
        ∀ j : Fin L, tagEdge Hed (dyadicGridLength A.G s) (v j.castSucc) (v j.succ) := by
  intro n
  induction n with
  | zero =>
    intro x y h
    change x = y at h
    subst h
    exact ⟨0, le_rfl, fun _ => bf.vtag x, rfl, rfl, fun _ => ⟨x, rfl⟩, fun j => j.elim0⟩
  | succ n ih =>
    intro x y h
    obtain ⟨u, hu, huy⟩ := h
    obtain ⟨L, hL, v, h0, hl, hrange, hedge⟩ := ih x u hu
    rcases huy with he | heq
    · refine ⟨L + 1, by omega, Fin.snoc v (bf.vtag y), ?_, by simp, fun i => ?_, fun j => ?_⟩
      · rw [show (0 : Fin (L + 2)) = (0 : Fin (L + 1)).castSucc from rfl, Fin.snoc_castSucc]
        exact h0
      · refine Fin.lastCases ⟨y, by simp⟩ (fun i => ?_) i
        rw [Fin.snoc_castSucc]; exact hrange i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hl]
          simpa using he
        · rw [show j.castSucc.castSucc = (j.castSucc).castSucc from rfl, Fin.snoc_castSucc,
            show j.castSucc.succ = j.succ.castSucc from rfl, Fin.snoc_castSucc]
          exact hedge j
    · exact ⟨L, by omega, v, h0, hl.trans heq, hrange, hedge⟩

/-- Blueprint lem:graph, short paths, for the original basic columns: two vertices at tag-graph
distance at most `n` carry equal tags or tags joined by an edge of height
`exp(10⁵ ((n+1)(d+1))⁸ log(2 H_ed))`, given tag dimensions at most `d` and matrix heights at most
`H_ed`. -/
theorem tagEdge_of_dist {Hed : ℝ} (hHed : 2 ≤ Hed) {dB : ℕ}
    (hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB)
    (hC : ∀ (w : bf.Vtx) a b, (rationalHeight ((bf.vtag w).C a b) : ℝ) ≤ Hed)
    {s : ℤ} {x y : bf.Vtx} {n : ℕ} (hd : (bf.tagDist Hed).d s x y ≤ n) :
    bf.vtag x = bf.vtag y ∨
      tagEdge (Real.exp (100000 * ((n + 1) * (dB + 1) : ℝ) ^ 8 * Real.log (2 * Hed)))
        (dyadicGridLength A.G s) (bf.vtag x) (bf.vtag y) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (bf.tagDist Hed).d s x y = k :=
    ⟨_, (ENat.natCast_toNat (ne_top_of_le_ne_top (by simp) hd)).symm⟩
  have hkn : k ≤ n := by rw [hk] at hd; exact_mod_cast hd
  have hw := exists_reachIn_of_graphDist_eq (edge := bf.tagGraphEdge Hed) hk
  obtain ⟨L, hLk, v, h0, hl, hrange, hedge⟩ := bf.tagWalk_path Hed s k x y hw
  rcases Nat.eq_zero_or_pos L with hL0 | hL1
  · subst hL0
    left; rw [← h0, ← hl]; rfl
  · right
    have hp := tagEdge_path hHed hL1 v
      (fun i => by obtain ⟨w, hw⟩ := hrange i; rw [hw]; exact hdim w)
      (fun i => by obtain ⟨w, hw⟩ := hrange i; rw [hw]; exact hC w) hedge
    rw [h0, hl] at hp
    refine tagEdge_mono hp (Real.exp_le_exp.mpr ?_)
    have hlog : 0 ≤ Real.log (2 * Hed) := Real.log_nonneg (by linarith)
    have hLn : (L : ℝ) ≤ n := by exact_mod_cast hLk.trans hkn
    have h1 : ((L + 1) * (dB + 1) : ℝ) ≤ (n + 1) * (dB + 1) := by
      have : (0 : ℝ) ≤ dB + 1 := by positivity
      nlinarith
    have h2 : ((L + 1) * (dB + 1) : ℝ) ^ 8 ≤ ((n + 1) * (dB + 1) : ℝ) ^ 8 :=
      pow_le_pow_left₀ (by positivity) h1 8
    nlinarith only [hlog, h2]

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The graph radius of a ball mask around its center. -/
noncomputable def ballRadius (g : ℤ) (h : ℕ) : ℕ :=
  (fp.K.b1 * fp.K.d0 - (g - 1) * fp.K.b1 + h).toNat

/-- The edge height of the ball radius `n` in the tag graph. -/
noncomputable def ballEdgeH (dB n : ℕ) : ℝ :=
  Real.exp (100000 * ((n + 1) * (dB + 1) : ℝ) ^ 8 * Real.log (2 * fp.Hed))

theorem two_le_ballEdgeH (hHed : 2 ≤ fp.Hed) (dB n : ℕ) : 2 ≤ fp.ballEdgeH dB n := by
  unfold ballEdgeH
  have hl : 1 ≤ Real.log (2 * fp.Hed) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h1 : (1 : ℝ) ≤ ((n + 1) * (dB + 1) : ℝ) ^ 8 := one_le_pow₀ (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have : (0 : ℝ) ≤ dB := Nat.cast_nonneg dB
    nlinarith)
  have h2 : 1 ≤ 100000 * ((n + 1) * (dB + 1) : ℝ) ^ 8 * Real.log (2 * fp.Hed) := by
    nlinarith only [hl, h1]
  calc (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    _ ≤ _ := Real.exp_le_exp.mpr h2

open Classical in
/-- Blueprint line 1903 (first match, short-path part of lem:graph): a vertex of the ball mask of
a group at an active cell carries a tag joined to the tag of the group center by an edge at the
cell length, of height `ballEdgeH` of the ball radius. -/
theorem mask_tagEdge_center {I : ℤ × ℤ} (hI : I ∈ A.cells) {G : bf.Grp} {h : ℕ} {b : bf.Vtx}
    (hb : b ∈ fp.K.mask bf.admT A.famVtxBound G h (bf.admAt I)) {ρ : Fin fp.K.d0} {z : bf.Vtx}
    {g : ℤ} (hG : G.2.1 = some (ρ, z, g)) (hHed : 2 ≤ fp.Hed) {dB : ℕ}
    (hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB)
    (hC : ∀ (w : bf.Vtx) a c, (rationalHeight ((bf.vtag w).C a c) : ℝ) ≤ fp.Hed) :
    tagEdge (fp.ballEdgeH dB (fp.ballRadius g h)) (dyadicGridLength A.G I.1) (bf.vtag b)
      (bf.vtag z) := by
  obtain ⟨k, hk, hkb⟩ := ColorSetup.mask_center_dist fp.K bf.admT A.famVtxBound hb hG
  have hDp := fp.K.Dp_le ρ z
  have hkn : k ≤ fp.ballRadius g h := by
    unfold ballRadius
    have : (fp.K.Dp ρ z : ℤ) ≤ fp.K.d0 := by exact_mod_cast hDp
    have hb1 : (0 : ℤ) ≤ fp.K.b1 := Int.natCast_nonneg _
    have : (fp.K.b1 : ℤ) * fp.K.Dp ρ z ≤ fp.K.b1 * fp.K.d0 := by nlinarith
    omega
  have hd : (bf.tagDist fp.Hed).d (bf.admT.depth (bf.admAt I)) z b ≤ fp.ballRadius g h := by
    change fp.K.dist.d _ z b ≤ _
    rw [hk]; exact_mod_cast hkn
  rw [bf.depth_admAt hI] at hd
  rcases bf.tagEdge_of_dist (le_trans (by norm_num) hHed) hdim hC hd with he | he
  · rw [he]; exact tagEdge_refl (fp.two_le_ballEdgeH hHed dB _) _ _
  · exact tagEdge_symm he

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- An available main label is, on the cell, a pure chart of its tag in the slot, of the common
source complexity (blueprint line 1798: pure main columns; line 1903: the primary at first
match). -/
theorem mainLabel_chart (l : Fin 4) {Mc : ℕ} (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) {I : ℤ × ℤ} {r : ℕ}
    {v : bf.Lab ⊕ Fin Mc} (hv : v ∈ mainLabels A.G Mc (bf.origCols l) s I r) :
    ∃ B : QuadraticChartData (bf.vtag (labelTag (bf.origCols l) s I d v)).dim,
      QuadraticChartComplexity A.csrc A.Hsrc B ∧ IsBoundedQuadraticChart B ∧
      B.horizontal = (bf.vtag (labelTag (bf.origCols l) s I d v)).θ ∧
      B.matrix = (slotCoeff l : ℚ) • (bf.vtag (labelTag (bf.origCols l) s I d v)).C ∧
      B.quadratic = slotCoeff l * (bf.vtag (labelTag (bf.origCols l) s I d v)).lam ∧
      ∀ y ∈ dyadicGridCell A.G I.1 I.2,
        mainScalar Mc (bf.origCols l) s v y = quadraticChartAtom B y := by
  classical
  rcases v with x | n
  · have hx : (bf.origCols l).avail I x := mem_mainLabels.mp hv
    obtain ⟨hc, hb, hθ, hM, hq, he⟩ := bf.origCol_source l hx
    exact ⟨(bf.vchart (bf.vtxAt I x)).2, hc, hb, hθ, hM, hq, fun y hy => he y hy⟩
  · obtain ⟨hn, -⟩ := (mem_mainLabels.mp hv : ∃ hn : (n : ℕ) < s.length, _)
    set e := s[(n : ℕ)]
    have he : e ∈ s := List.getElem_mem _
    obtain ⟨R, hR, γ, hde⟩ := hT e he
    have htg : labelTag (bf.origCols l) s I d (Sum.inr n : bf.Lab ⊕ Fin Mc) = e.tag := by
      simp only [labelTag, Sum.elim_inr, hn, ↓reduceDIte]; rfl
    rw [htg]
    obtain ⟨A', hA', hθ, hM, hq, hatom⟩ := bf.templateCol_source (htag e he) l hR γ e.birth e.rank
    have hatom' : e.atom = quadraticChartAtom A' := by
      rw [← hatom]; exact congrArg CatCol.atom hde
    refine ⟨A', hA', fun y => by rw [← hatom']; exact e.bound y, hθ, hM, hq, fun y _ => ?_⟩
    simp only [mainScalar, Sum.elim_inr, catAtom, hn, ↓reduceDIte]
    exact congrFun hatom' y

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams

open Classical in
/-- Blueprint first-match (lines 1903-1916, `eq:firstmatch`, `eq:mode-differences`) on the main
columns: a primary `v` of the role (slot `l`, outer ball of the group `G` at the level `j`) at an
active cell `I` is, on the cell, a pure chart `Φ` of its tag (an original column occurrence or a
template), and on the window `|t| ≤ R |I|` at the left end `a_I` of the cell, the product chart
`P` of `Φ` with the branch chart of the group center (cutoff of width `δ`, demodulation
`e(-c_l p_ρ)`) has an exact absolutely convergent mode expansion
`φ_P(a_I + t) = Σ a_ℓ e(λ_* t² + (β + σ_ℓ·θ) t)` with one common curvature, rational frequency
differences, and counts, heights and coefficient sums at most `exp(D X^D)`,
`X = 1 + log T(H⁶) + log(3B)` (`T` the translation budget, `B` the edge height of the ball
radius at the maximal pad). -/
theorem mainFirstMatch_attempt (κ : LocalKernelClass) (c₀ : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (fp : bf.FamParams)
      (l : Fin 4) (s : List (CatCol bf.Vtx))
      (_hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
        e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
      (_htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx)
      {I : ℤ × ℤ} (_hI : I ∈ A.cells) {G : bf.Grp} {j : ℕ} {v : bf.Lab ⊕ Fin fp.Mc}
      (_hv : v ∈ fp.primaries l s G j d I)
      {ρ₀ : Fin fp.K.d0} {z : bf.Vtx} {g : ℤ} (_hG : G.2.1 = some (ρ₀, z, g))
      (_hHed : 2 ≤ fp.Hed) {dB : ℕ} (_hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB)
      (_hC : ∀ (w : bf.Vtx) a c, (rationalHeight ((bf.vtag w).C a c) : ℝ) ≤ fp.Hed)
      {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 4) (ρ : Fin (bf.vtag z).dim → ℝ)
      (_hρ : ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) {H : ℝ} (_hHs : A.Hsrc ≤ H)
      (_hdz : ((bf.vtag z).dim : ℝ) ≤ Real.log H)
      (_hCz : ∀ i k, (chartRationalHeight ((((-slotCoeff l : ℤ) : ℚ) • (bf.vtag z).C) i k) : ℝ) ≤
        H)
      (_hHδ : ((bf.vtag z).dim : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ H),
      ∃ Φ : QuadraticChartData (bf.vtag (labelTag (bf.origCols l) s I d v)).dim,
        (∀ y ∈ dyadicGridCell A.G I.1 I.2,
          mainScalar fp.Mc (bf.origCols l) s v y = quadraticChartAtom Φ y) ∧
        IsBoundedQuadraticChart Φ ∧
        Φ.horizontal = (bf.vtag (labelTag (bf.origCols l) s I d v)).θ ∧
        Φ.matrix = (slotCoeff l : ℚ) • (bf.vtag (labelTag (bf.origCols l) s I d v)).C ∧
        Φ.quadratic = slotCoeff l * (bf.vtag (labelTag (bf.origCols l) s I d v)).lam ∧
      let P := productQuadraticChart Φ (branchChart (bf.vtag z) (slotCoeff l)
        (branchAmp_smooth δ ρ) (branchAmp_hasCompactSupport hδ hδ' ρ))
      let X := 1 + Real.log (chartTranslationBudget (H ^ 6)) +
        Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
      let dd := (bf.vtag (labelTag (bf.origCols l) s I d v)).dim + (bf.vtag z).dim
      ∃ M : Matrix (Fin dd) (Fin dd) ℚ,
        (∀ i k, (rationalHeight (M i k) : ℝ) ≤ Real.exp (D * X ^ D)) ∧
        |P.quadratic + ∑ i, ∑ k, P.horizontal i * (M i k : ℝ) * P.horizontal k| *
            dyadicGridLength A.G I.1 ^ 2 ≤ Real.exp (D * X ^ D) ∧
        ∃ (ι : Type) (_ : Fintype ι) (σ : ι × (Fin (dd + dd) → ℤ) → Fin dd → ℚ),
          (Fintype.card ι : ℝ) ≤ Real.exp (D * X ^ D) ∧
          (∀ q i, (rationalHeight (σ q i) : ℝ) ≤
            Real.exp (D * X ^ D) * (1 + frequencyLength q.2)) ∧
          ∃ (β : ℝ) (a : ι × (Fin (dd + dd) → ℤ) → ℂ),
            (∀ t : ℝ, |t| ≤ R * dyadicGridLength A.G I.1 →
              HasSum (fun q => a q * (Real.fourierChar ((P.quadratic +
                  ∑ i, ∑ k, P.horizontal i * (M i k : ℝ) * P.horizontal k) * t ^ 2 +
                  (β + ∑ i, (σ q i : ℝ) * P.horizontal i) * t) : ℂ))
                (quadraticChartAtom P (dyadicGridLeft A.G I.1 I.2 + t))) ∧
            Summable (fun q => ‖a q‖) ∧ (∑' q, ‖a q‖) ≤ Real.exp (D * X ^ D) ∧
            ∀ T : ℝ, 1 ≤ T → (∑ f : ι, ∑ w ∈ frequencyShell (dd + dd) T, ‖a (f, w)‖) * T ≤
              Real.exp (D * X ^ D) := by
  obtain ⟨D, hD, hfm⟩ := firstMatchExpansion_at (max (max c₀ (2 * tagKρ)) 32)
    (le_trans (by norm_num) (le_max_right _ _)) R hR
  refine ⟨D, hD, ?_⟩
  intro A bf fp l s hT htag d I hI G j v hv ρ₀ z g hG hHed dB hdim hC δ hδ hδ' ρ hρ H hHs hdz
    hCz hHδ
  obtain ⟨hvL, hvM⟩ := mem_mainLabelsM.mp hv
  obtain ⟨Φ, hΦ, hΦb, hθ, hM, hq, he⟩ := bf.mainLabel_chart l s hT htag d hvL
  refine ⟨Φ, he, hΦb, hθ, hM, hq, ?_⟩
  -- the complexities
  have hH2 : Real.exp 2 ≤ H := A.exp_two_le_Hsrc.trans hHs
  have hbr := branchChart_complexity (bf.vtag z) (slotCoeff l) hδ hδ' ρ hρ hH2 hdz hCz hHδ
  have hΦH : QuadraticChartComplexity (max (max c₀ (2 * tagKρ)) 32) H Φ :=
    quadraticChartComplexity_mono_order (quadraticChartComplexity_mono hΦ hHs)
      (le_max_left _ _)
  have hbrH : QuadraticChartComplexity (max (max c₀ (2 * tagKρ)) 32) H
      (branchChart (bf.vtag z) (slotCoeff l) (branchAmp_smooth δ ρ)
        (branchAmp_hasCompactSupport hδ hδ' ρ)) :=
    quadraticChartComplexity_mono_order hbr (le_max_right _ _)
  have hP := productQuadraticChart_complexity hΦH hbrH
    (le_trans (by norm_num) (le_max_right _ _))
  have hE := fp.mask_tagEdge_center hI hvM hG hHed hdim hC
  exact hfm (bf.vtag (labelTag (bf.origCols l) s I d v)) (bf.vtag z) (slotCoeff l)
    (by fin_cases l <;> decide) (slotCoeff_abs_le l) (H ^ 6) _ (dyadicGridLength A.G I.1) Φ _ _
    hθ hM hq hP (dyadicGridLength_pos A.G I.1) (fp.two_le_ballEdgeH hHed dB _) hE
    (dyadicGridLeft A.G I.1 I.2)

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams

open Classical in
/-- Blueprint `eq:firstmatch` (lines 1903-1910) on the main columns: at an active cell where `v`
is a primary of the role, finitely many modes `e(λ (y - a_I)² + γ_k (y - a_I))`, with one
curvature and frequencies `γ_k = β + σ_k·Θ` (`σ_k` rational, `Θ = (θ_v, θ_z)`), approximate
`φ_v ζ^ρ e(-c_l p_ρ)` within `δ_c` on the whole cell, with coefficient sum and `|λ| |I|²` at most
`exp(D X^D)`; the count and the heights are bounded as in `eq:mode-differences`. -/
theorem mainFirstMatch_finite (κ : LocalKernelClass) (c₀ : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (fp : bf.FamParams)
      (l : Fin 4) (s : List (CatCol bf.Vtx))
      (_hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
        e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
      (_htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx)
      {I : ℤ × ℤ} (_hI : I ∈ A.cells) {G : bf.Grp} {j : ℕ} {v : bf.Lab ⊕ Fin fp.Mc}
      (_hv : v ∈ fp.primaries l s G j d I)
      {ρ₀ : Fin fp.K.d0} {z : bf.Vtx} {g : ℤ} (_hG : G.2.1 = some (ρ₀, z, g))
      (_hHed : 2 ≤ fp.Hed) {dB : ℕ} (_hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB)
      (_hC : ∀ (w : bf.Vtx) a c, (rationalHeight ((bf.vtag w).C a c) : ℝ) ≤ fp.Hed)
      {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ < 1 / 4) (ρ : Fin (bf.vtag z).dim → ℝ)
      (_hρ : ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) {H : ℝ} (_hHs : A.Hsrc ≤ H)
      (_hdz : ((bf.vtag z).dim : ℝ) ≤ Real.log H)
      (_hCz : ∀ i k, (chartRationalHeight ((((-slotCoeff l : ℤ) : ℚ) • (bf.vtag z).C) i k) : ℝ) ≤
        H)
      (_hHδ : ((bf.vtag z).dim : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ H) {δc : ℝ} (_hδc : 0 < δc),
      let X := 1 + Real.log (chartTranslationBudget (H ^ 6)) +
        Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
      ∃ (Ny : Type) (_ : Fintype Ny) (coef : Ny → ℂ) (lam : ℝ) (γ : Ny → ℝ) (dv : ℕ)
        (θv : Fin dv → ℝ) (σ : Ny → Fin (dv + (bf.vtag z).dim) → ℚ) (β : ℝ),
        (∀ k, γ k = β + ∑ i, (σ k i : ℝ) * Fin.append θv (bf.vtag z).θ i) ∧ dv ≤ dB ∧
        (Fintype.card Ny : ℝ) ≤ Real.exp (D * X ^ D) *
          (4 * max 1 (4 * Real.exp (D * X ^ D) / δc) + 1) ^
            ((dv + (bf.vtag z).dim) + (dv + (bf.vtag z).dim)) ∧
        (∀ k i, (rationalHeight (σ k i) : ℝ) ≤ Real.exp (D * X ^ D) *
          (1 + 4 * ((dv + (bf.vtag z).dim : ℕ) + 1) * max 1 (4 * Real.exp (D * X ^ D) / δc))) ∧
        (∑ k, ‖coef k‖) ≤ Real.exp (D * X ^ D) ∧
        |lam| * dyadicGridLength A.G I.1 ^ 2 ≤ Real.exp (D * X ^ D) ∧
        ∀ y ∈ dyadicGridCell A.G I.1 I.2,
          ‖∑ k, coef k * (Real.fourierChar (lam * (y - dyadicGridLeft A.G I.1 I.2) ^ 2 +
              γ k * (y - dyadicGridLeft A.G I.1 I.2)) : ℂ) -
            mainScalar fp.Mc (bf.origCols l) s v y * ((centerCut (bf.vtag z) δ ρ y : ℂ) *
              (Real.fourierChar (-(slotCoeff l : ℝ) * centerPhase (bf.vtag z) ρ y) : ℂ))‖ ≤ δc := by
  obtain ⟨D, hD, hfm⟩ := mainFirstMatch_attempt κ c₀ 1 zero_le_one
  refine ⟨D, hD, ?_⟩
  intro A bf fp l s hT htag d I hI G j v hv ρ₀ z g hG hHed dB hdim hC δ hδ hδ' ρ hρ H hHs hdz
    hCz hHδ δc hδc X
  obtain ⟨Φ, he, -, hθ, -, -, M, -, hlam, ι, hι, σ, hcard, hσ, β, a, hexp, hsumm, htot,
    hshell⟩ :=
    hfm A bf fp l s hT htag d hI hv hG hHed hdim hC hδ hδ' ρ hρ hHs hdz hCz hHδ
  set P := productQuadraticChart Φ (branchChart (bf.vtag z) (slotCoeff l) (branchAmp_smooth δ ρ)
    (branchAmp_hasCompactSupport hδ hδ' ρ))
  set lam := P.quadratic + ∑ i, ∑ k, P.horizontal i * (M i k : ℝ) * P.horizontal k
  have hPh : P.horizontal =
      Fin.append (bf.vtag (labelTag (bf.origCols l) s I d v)).θ (bf.vtag z).θ := by
    simp [P, productQuadraticChart, branchChart, mkQuadraticChart, hθ]
  set B := Real.exp (D * X ^ D)
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hex : ∃ K : ℕ, 2 * B / δc ≤ 2 ^ K := pow_unbounded_of_one_lt _ (by norm_num) |>.imp
    fun _ h => h.le
  set! K := Nat.find hex
  have hK : 2 * B / δc ≤ 2 ^ K := Nat.find_spec hex
  have hKt : 2 * B / 2 ^ K ≤ δc := by
    rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ hδc] at hK; linarith
  have hKm : (2 : ℝ) ^ K ≤ max 1 (4 * B / δc) := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0, pow_zero]; exact le_max_left _ _
    · obtain ⟨k, hk⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      have hmin := Nat.find_min hex (show k < K by omega)
      rw [not_le] at hmin
      refine le_trans ?_ (le_max_right _ _)
      rw [hk, pow_succ]
      have : 4 * B / δc = 2 * (2 * B / δc) := by ring
      rw [this]; linarith
  set! S := (Finset.univ : Finset ι) ×ˢ
    frequencyBox (((bf.vtag (labelTag (bf.origCols l) s I d v)).dim + (bf.vtag z).dim) +
      ((bf.vtag (labelTag (bf.origCols l) s I d v)).dim + (bf.vtag z).dim))
      (2 ^ (K + 1))
  refine ⟨{q // q ∈ S}, inferInstance, fun q => a q, lam,
    fun q => β + ∑ i, (σ q i : ℝ) * P.horizontal i,
    (bf.vtag (labelTag (bf.origCols l) s I d v)).dim,
    (bf.vtag (labelTag (bf.origCols l) s I d v)).θ, fun q => σ q,
    β, fun q => by rw [hPh], hdim _, ?_, fun q i => ?_, ?_, hlam,
    fun y hy => ?_⟩
  · rw [Fintype.card_coe, Finset.card_product, Finset.card_univ, card_frequencyBox]
    push_cast
    refine mul_le_mul hcard (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity) hB0
    have : (2 : ℝ) * 2 ^ (K + 1) + 1 = 4 * 2 ^ K + 1 := by ring
    rw [this]; linarith
  · have hq := q.2
    simp only [S, Finset.mem_product] at hq
    have hlen := frequencyLength_le_of_mem_box hq.2
    refine (hσ q.1 i).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    have hmax : (2 : ℝ) ^ K ≤ max 1 (4 * B / δc) := hKm
    push_cast at hlen ⊢
    have h2 : ((2 : ℝ) ^ (K + 1)) = 2 * 2 ^ K := by ring
    rw [h2] at hlen
    have hdθ0 : (0 : ℝ) ≤
        ((bf.vtag (labelTag (bf.origCols l) s I d v)).dim + (bf.vtag z).dim : ℕ) :=
      Nat.cast_nonneg _
    push_cast at hdθ0
    nlinarith only [hmax, frequencyLength_nonneg q.1.2, le_max_left (1 : ℝ) (4 * B / δc), hlen]
  · refine le_trans ?_ htot
    rw [Finset.sum_coe_sort S (fun q => ‖a q‖)]
    exact hsumm.sum_le_tsum _ fun q _ => norm_nonneg _
  · set a₀ := dyadicGridLeft A.G I.1 I.2
    have hy' := hy
    simp only [dyadicGridCell, Set.mem_Ico] at hy'
    have ht : |y - a₀| ≤ 1 * dyadicGridLength A.G I.1 := by
      rw [one_mul, abs_of_nonneg (by linarith)]; linarith
    have h := hasSum_box_truncate a hsumm hB0 hshell K (fun q t => (Real.fourierChar (lam * t ^ 2 +
        (β + ∑ i, (σ q i : ℝ) * P.horizontal i) * t) : ℂ)) (fun _ _ => Circle.norm_coe _)
      (fun t => quadraticChartAtom P (a₀ + t)) (y - a₀) (hexp _ ht)
    rw [add_sub_cancel] at h
    refine le_trans ?_ hKt
    rw [Finset.sum_coe_sort S (fun q => a q * (Real.fourierChar (lam * (y - a₀) ^ 2 +
      (β + ∑ i, (σ q i : ℝ) * P.horizontal i) * (y - a₀)) : ℂ))]
    rw [norm_sub_rev, he y hy, ← firstMatch_atom Φ (bf.vtag z) (slotCoeff l) hδ hδ' ρ y]
    exact h

end ActiveSetup.BasicFamilies.FamParams

/-! ## The main-column lift with local mode weights (blueprint line 1932) -/

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- At every point, the primaries matched there (those with a first-match cell containing the
point) are primaries at the deepest such cell; hence they number at most the main labels there
(blueprint line 1932: the physical correction runs over the primaries matched at `y`). -/
theorem card_matched_le (cs : Finset (ℤ × ℤ)) (hcs : cs ⊆ A.cells) (l : Fin 4)
    (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ) (d : bf.Vtx) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ I ∈ A.cells,
      ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N) (y : ℝ) :
    ((Finset.univ.filter fun v => ∃ I ∈ fp.firstCells cs l s G j d v,
      y ∈ dyadicGridCell A.G I.1 I.2).card : ℝ) ≤ N := by
  set T := cs.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2
  set Mt := Finset.univ.filter fun v => ∃ I ∈ fp.firstCells cs l s G j d v,
    y ∈ dyadicGridCell A.G I.1 I.2
  have hcsI : ∀ {v I}, I ∈ fp.firstCells cs l s G j d v → I ∈ cs := fun hI =>
    (Finset.mem_filter.mp (mem_maxCells.mp hI).1).1
  rcases T.eq_empty_or_nonempty with hT | hT
  · have hMt : Mt = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
      obtain ⟨I, hI, hyI⟩ := (Finset.mem_filter.mp hv).2
      have hIT : I ∈ T := Finset.mem_filter.mpr ⟨hcsI hI, hyI⟩
      rw [hT] at hIT; exact Finset.notMem_empty _ hIT
    rw [hMt, Finset.card_empty, Nat.cast_zero]; exact hN0
  obtain ⟨J, hJ, hmax⟩ := T.exists_max_image (fun I => I.1) hT
  obtain ⟨hJcs, hyJ⟩ := Finset.mem_filter.mp hJ
  have hsub : Mt ⊆ mainLabels A.G fp.Mc (bf.origCols l) s J (fp.brank j) := by
    intro v hv
    obtain ⟨I, hI, hyI⟩ := (Finset.mem_filter.mp hv).2
    have hdep := hmax I (Finset.mem_filter.mpr ⟨hcsI hI, hyI⟩)
    have hJI := dyadicGridCell_subset_of_common_point A.G hyJ hyI hdep
    exact mainLabelsM_subset _ _ _ _ _
      (fp.primaries_of_firstCell cs hcs l s G j d hI (hcs hJcs) hJI)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hN J (hcs hJcs))

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams



end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
