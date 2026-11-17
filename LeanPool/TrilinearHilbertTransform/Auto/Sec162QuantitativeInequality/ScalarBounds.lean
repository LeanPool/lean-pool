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
# Scalar bounds for the final trilinear estimate

These estimates depend only on the quantitative setup. Keeping them separate from
the column-side estimate avoids retaining their elaboration state in its proof.
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

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

theorem bandC_nonneg' (p : ℝ) (J : ℕ) :
    0 ≤ ActiveSetup.BasicFamilies.FamParams.SideInput.bandC p J := by
  unfold ActiveSetup.BasicFamilies.FamParams.SideInput.bandC
  exact tsum_nonneg fun t => by positivity

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
  clear_value Gq Ts
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
  clear_value Cjg
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
  clear_value Yn
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
  clear_value Cjg
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
  clear_value Yn Qk
  clear_value Cjg G0e W
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
  clear_value Yn Qk
  clear_value Cjg G0e W
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
  have! h7 := mul_le_mul_of_nonneg_right h2 hh0
  rw [h3] at h7
  calc
    _ ≤ _ := h7.trans h5
    _ = _ := by rw [hQkdef]; ring

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
