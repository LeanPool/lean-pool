/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUGaussianWeights
public import LeanPool.EscauriazaSereginSverak.Linear.UCDefs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Gaussian weight comparison on collar cells

The Gaussian weight changes by a fixed factor on each enlarged space-time
cell when the parabolic radius is chosen from the Carleman parameter.
-/

public section


open Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem buGaussian_log_time_weight_lipschitz
    {s t : ℝ} (hs : 1 / 6 ≤ s) (ht : 1 / 6 ≤ t) :
    |Real.log (gaussCarlemanTimeWeight s) -
      Real.log (gaussCarlemanTimeWeight t)| ≤ 7 * |s - t| := by
  have hspos : 0 < s := by linarith only [hs]
  have htpos : 0 < t := by linarith only [ht]
  have hswt : gaussCarlemanTimeWeight s = s * Real.exp ((1 - s) / 3) := rfl
  have htwt : gaussCarlemanTimeWeight t = t * Real.exp ((1 - t) / 3) := rfl
  rw [hswt, htwt, Real.log_mul hspos.ne' (Real.exp_ne_zero _),
    Real.log_mul htpos.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
  have hlog : |Real.log s - Real.log t| ≤ 6 * |s - t| := by
    rcases le_total s t with hst | hts
    · have hratio : 0 < t / s := div_pos htpos hspos
      have hlogdiv : Real.log t - Real.log s = Real.log (t / s) := by
        rw [Real.log_div htpos.ne' hspos.ne']
      have hupper := Real.log_le_sub_one_of_pos hratio
      have hquot : t / s - 1 = (t - s) / s := by field_simp
      rw [← hlogdiv, hquot] at hupper
      have hrecip' : 1 / s ≤ 6 := by
        apply (div_le_iff₀ hspos).2
        nlinarith only [hs]
      have hrecip : s⁻¹ ≤ 6 := by simpa [one_div] using hrecip'
      have hmul : (t - s) / s ≤ 6 * (t - s) := by
        calc
          (t - s) / s = (t - s) * s⁻¹ := by ring
          _ ≤ (t - s) * 6 :=
            mul_le_mul_of_nonneg_left hrecip (sub_nonneg.mpr hst)
          _ = 6 * (t - s) := by ring
      have hlogmono : Real.log s ≤ Real.log t := Real.log_le_log hspos hst
      rw [abs_of_nonpos (sub_nonpos.mpr hlogmono)]
      rw [abs_of_nonpos (sub_nonpos.mpr hst)]
      simpa [sub_eq_add_neg] using le_trans hupper hmul
    · have hratio : 0 < s / t := div_pos hspos htpos
      have hlogdiv : Real.log s - Real.log t = Real.log (s / t) := by
        rw [Real.log_div hspos.ne' htpos.ne']
      have hupper := Real.log_le_sub_one_of_pos hratio
      have hquot : s / t - 1 = (s - t) / t := by field_simp
      rw [← hlogdiv, hquot] at hupper
      have hrecip' : 1 / t ≤ 6 := by
        apply (div_le_iff₀ htpos).2
        nlinarith only [ht]
      have hrecip : t⁻¹ ≤ 6 := by simpa [one_div] using hrecip'
      have hmul : (s - t) / t ≤ 6 * (s - t) := by
        calc
          (s - t) / t = (s - t) * t⁻¹ := by ring
          _ ≤ (s - t) * 6 :=
            mul_le_mul_of_nonneg_left hrecip (sub_nonneg.mpr hts)
          _ = 6 * (s - t) := by ring
      have hlogmono : Real.log t ≤ Real.log s := Real.log_le_log htpos hts
      rw [abs_of_nonneg (sub_nonneg.mpr hlogmono)]
      rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      simpa [sub_eq_add_neg] using le_trans hupper hmul
  have hlin : |(1 - s) / 3 - (1 - t) / 3| ≤ |s - t| / 3 := by
    rw [show (1 - s) / 3 - (1 - t) / 3 = -(s - t) / 3 by ring,
      abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hresult : |Real.log s - Real.log t +
      ((1 - s) / 3 - (1 - t) / 3)| ≤ 7 * |s - t| := by
    calc
      _ ≤ |Real.log s - Real.log t| + |(1 - s) / 3 - (1 - t) / 3| :=
        abs_add_le _ _
      _ ≤ 6 * |s - t| + |s - t| / 3 := add_le_add hlog hlin
      _ ≤ 7 * |s - t| := by nlinarith only [abs_nonneg (s - t)]
  convert hresult using 1
  ring_nf

/-- The Carleman weight varies by a uniform factor over an outer collar cell.
The displayed exponent is expressed in the geometric cell parameters so it
can be bounded using the fixed product `ρ r`. -/
theorem buGaussian_weight_cell_comparison
    {ρ a r σ δ : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (hr : 0 < r)
    (hσ : σ = 1 / 6) (hδ : δ = r ^ 2)
    {x y : Vec3} {s t : ℝ}
    (hyx : vec3EuclideanNorm (y - x) < 2 * r)
    (hyρ : vec3EuclideanNorm y ≤ ρ) (hxρ : vec3EuclideanNorm x ≤ ρ)
    (hs : σ ≤ s) (ht : σ ≤ t)
    (hdt : |s - t| ≤ 4 * δ) :
    ucGaussianWeight a (y, s) ≤
      Real.exp (56 * a * δ + 12 * ρ * r + 36 * ρ ^ 2 * δ) *
        ucGaussianWeight a (x, t) := by
  have hspos : 0 < s := by rw [hσ] at hs; linarith only [hs]
  have htpos : 0 < t := by rw [hσ] at ht; linarith only [ht]
  have hwtpos : 0 < gaussCarlemanTimeWeight s := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hwt0pos : 0 < gaussCarlemanTimeWeight t := by
    unfold gaussCarlemanTimeWeight
    positivity
  let ψ : ParabolicPoint → ℝ := fun z =>
    -2 * a * Real.log (gaussCarlemanTimeWeight z.2) -
      vec3EuclideanNorm z.1 ^ 2 / (4 * z.2)
  have hweight (z : ParabolicPoint) (hz : 0 < z.2) :
      ucGaussianWeight a z = Real.exp (ψ z) := by
    change gaussCarlemanTimeWeight z.2 ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm z.1 ^ 2) / (4 * z.2)) = _
    rw [Real.rpow_def_of_pos (by
      unfold gaussCarlemanTimeWeight
      positivity), ← Real.exp_add]
    congr 1
    dsimp [ψ]
    ring
  have hlog := buGaussian_log_time_weight_lipschitz
    (s := s) (t := t) (by rw [hσ] at hs; exact hs)
    (by rw [hσ] at ht; exact ht)
  have hlog' : |Real.log (gaussCarlemanTimeWeight s) -
      Real.log (gaussCarlemanTimeWeight t)| ≤ 28 * δ := by
    calc
      _ ≤ 7 * |s - t| := hlog
      _ ≤ 7 * (4 * δ) := mul_le_mul_of_nonneg_left hdt (by norm_num)
      _ = 28 * δ := by ring
  have hnormdiff : |vec3EuclideanNorm y - vec3EuclideanNorm x| ≤ 2 * r := by
    have hxy : vec3EuclideanNorm y ≤ vec3EuclideanNorm x +
        vec3EuclideanNorm (y - x) := by
      have h := vec3EuclideanNorm_add_le x (y - x)
      have heq : x + (y - x) = y := by abel
      rw [heq] at h
      exact h
    have htriYX : vec3EuclideanNorm x ≤ vec3EuclideanNorm y +
        vec3EuclideanNorm (y - x) := by
      have h := vec3EuclideanNorm_add_le y (x - y)
      have heq : y + (x - y) = x := by abel
      rw [heq, show x - y = -(y - x) by abel,
        vec3EuclideanNorm_neg] at h
      exact h
    have hdiffnonneg : 0 ≤ vec3EuclideanNorm (y - x) :=
      vec3EuclideanNorm_nonneg _
    rw [abs_le]
    constructor
    · nlinarith only [htriYX, hyx, hdiffnonneg]
    · nlinarith only [hxy, hyx, hdiffnonneg]
  have hsqdiff : |vec3EuclideanNorm y ^ 2 - vec3EuclideanNorm x ^ 2| ≤
      4 * ρ * r := by
    rw [show vec3EuclideanNorm y ^ 2 - vec3EuclideanNorm x ^ 2 =
      (vec3EuclideanNorm y - vec3EuclideanNorm x) *
        (vec3EuclideanNorm y + vec3EuclideanNorm x) by ring, abs_mul]
    have hsum : vec3EuclideanNorm y + vec3EuclideanNorm x ≤ 2 * ρ := by
      nlinarith only [hyρ, hxρ]
    have hsumabs : |vec3EuclideanNorm y + vec3EuclideanNorm x| ≤ 2 * ρ := by
      rw [abs_of_nonneg (add_nonneg (vec3EuclideanNorm_nonneg y)
        (vec3EuclideanNorm_nonneg x))]
      exact hsum
    have hnormdiff' : |vec3EuclideanNorm y - vec3EuclideanNorm x| ≤ 2 * r := hnormdiff
    calc
      |vec3EuclideanNorm y - vec3EuclideanNorm x| *
          |vec3EuclideanNorm y + vec3EuclideanNorm x| ≤
          (2 * r) * (2 * ρ) :=
        mul_le_mul hnormdiff' hsumabs
          (abs_nonneg _) (mul_nonneg (by norm_num) (le_of_lt hr))
      _ = 4 * ρ * r := by ring
  have hfirst : |vec3EuclideanNorm y ^ 2 / (4 * s) -
      vec3EuclideanNorm x ^ 2 / (4 * s)| ≤ 6 * ρ * r := by
    have heq : vec3EuclideanNorm y ^ 2 / (4 * s) -
        vec3EuclideanNorm x ^ 2 / (4 * s) =
        (vec3EuclideanNorm y ^ 2 - vec3EuclideanNorm x ^ 2) / (4 * s) := by ring
    rw [heq]
    have hden : 0 < 4 * s := by positivity
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    have hslo : 1 / 6 ≤ s := by rw [hσ] at hs; exact hs
    have hsInv : (4 * s) * (6 * ρ * r) ≥ 4 * ρ * r := by
      have : 1 ≤ 6 * s := by nlinarith only [hslo]
      nlinarith only [this, mul_nonneg (le_of_lt hρ) (le_of_lt hr)]
    nlinarith only [hsqdiff, hsInv,
      mul_nonneg (le_of_lt hρ) (le_of_lt hr)]
  have hinvdiff : |(1 / (4 * s)) - (1 / (4 * t))| ≤ 36 * δ := by
    have hden : 0 < 4 * s * (4 * t) := by positivity
    have heq : (1 / (4 * s)) - (1 / (4 * t)) =
        (4 * t - 4 * s) / (4 * s * (4 * t)) := by field_simp
    rw [heq, abs_div]
    have hnum : |4 * t - 4 * s| ≤ 16 * δ := by
      have := abs_neg (s - t)
      have ht' : |t - s| ≤ 4 * δ := by simpa [abs_sub_comm] using hdt
      rw [show 4 * t - 4 * s = 4 * (t - s) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      nlinarith only [ht']
    have hstlo : (4 * s) * (4 * t) ≥ 4 / 9 := by
      have hs' : 1 / 6 ≤ s := by rw [hσ] at hs; exact hs
      have ht' : 1 / 6 ≤ t := by rw [hσ] at ht; exact ht
      nlinarith only [hs', ht']
    rw [abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    have hδnonneg : 0 ≤ δ := by rw [hδ]; positivity
    nlinarith only [hnum, hstlo, hδnonneg]
  have hsecond : |vec3EuclideanNorm x ^ 2 * (1 / (4 * s) -
      1 / (4 * t))| ≤ 36 * ρ ^ 2 * δ := by
    rw [abs_mul]
    have hnormsq : vec3EuclideanNorm x ^ 2 ≤ ρ ^ 2 := by
      nlinarith only [hxρ, vec3EuclideanNorm_nonneg x]
    calc
      |vec3EuclideanNorm x ^ 2| *
          |1 / (4 * s) - 1 / (4 * t)| ≤ ρ ^ 2 * (36 * δ) :=
        mul_le_mul (by rwa [abs_of_nonneg (sq_nonneg _)]) hinvdiff
          (abs_nonneg _) (by positivity)
      _ = 36 * ρ ^ 2 * δ := by ring
  have hqdiff : |vec3EuclideanNorm y ^ 2 / (4 * s) -
      vec3EuclideanNorm x ^ 2 / (4 * t)| ≤ 6 * ρ * r + 36 * ρ ^ 2 * δ := by
    have halg : vec3EuclideanNorm y ^ 2 / (4 * s) -
        vec3EuclideanNorm x ^ 2 / (4 * t) =
        (vec3EuclideanNorm y ^ 2 / (4 * s) -
          vec3EuclideanNorm x ^ 2 / (4 * s)) +
        vec3EuclideanNorm x ^ 2 * (1 / (4 * s) - 1 / (4 * t)) := by ring
    rw [halg]
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  have hψdiff : |ψ (y, s) - ψ (x, t)| ≤
      56 * a * δ + 12 * ρ * r + 36 * ρ ^ 2 * δ := by
    dsimp [ψ]
    have htime : |(-2 * a) *
        (Real.log (gaussCarlemanTimeWeight s) -
          Real.log (gaussCarlemanTimeWeight t))| ≤ 56 * a * δ := by
      rw [abs_mul, abs_of_nonpos (by nlinarith only [ha])]
      calc
        _ = (2 * a) * |Real.log (gaussCarlemanTimeWeight s) -
            Real.log (gaussCarlemanTimeWeight t)| := by ring
        _ ≤ (2 * a) * (28 * δ) :=
          mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ = 56 * a * δ := by ring
    have hmain : |ψ (y, s) - ψ (x, t)| ≤
        56 * a * δ + 6 * ρ * r + 36 * ρ ^ 2 * δ := by
      rw [show ψ (y, s) - ψ (x, t) =
        (-2 * a) * (Real.log (gaussCarlemanTimeWeight s) -
          Real.log (gaussCarlemanTimeWeight t)) -
        (vec3EuclideanNorm y ^ 2 / (4 * s) -
          vec3EuclideanNorm x ^ 2 / (4 * t)) by dsimp [ψ]; ring]
      calc
        |(-2 * a) * (Real.log (gaussCarlemanTimeWeight s) -
              Real.log (gaussCarlemanTimeWeight t)) -
            (vec3EuclideanNorm y ^ 2 / (4 * s) -
              vec3EuclideanNorm x ^ 2 / (4 * t))| ≤
            |(-2 * a) * (Real.log (gaussCarlemanTimeWeight s) -
              Real.log (gaussCarlemanTimeWeight t))| +
            |vec3EuclideanNorm y ^ 2 / (4 * s) -
              vec3EuclideanNorm x ^ 2 / (4 * t)| := abs_sub _ _
      _ ≤ 56 * a * δ + 6 * ρ * r + 36 * ρ ^ 2 * δ := by
          calc
            _ ≤ 56 * a * δ + (6 * ρ * r + 36 * ρ ^ 2 * δ) :=
              add_le_add htime hqdiff
            _ = 56 * a * δ + 6 * ρ * r + 36 * ρ ^ 2 * δ := by ring
    have hrhoRnonneg : 0 ≤ ρ * r := mul_nonneg (le_of_lt hρ) (le_of_lt hr)
    nlinarith only [hmain, hrhoRnonneg]
  rw [hweight (y, s) hspos, hweight (x, t) htpos]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hupper : ψ (y, s) - ψ (x, t) ≤
      56 * a * δ + 12 * ρ * r + 36 * ρ ^ 2 * δ := le_trans (le_abs_self _) hψdiff
  linarith only [hupper]

end ESS

end
