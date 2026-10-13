/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.AtomTail

/-!
# LambdaWindow

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `s`-window of `p.cg.ellipticity.bounds` at `s = γ`, discharged

## The obligation this module removes

`Proportion.exists_cgExcess_atomTail` and the (B5) statements of
`LambdaSlotB5.lean` carry ONE undischarged premise, the anchor's own `s`-window
read at `s = γ`:

```
cgTailScale M E = exp(−(C_cg^{−1} E^{−2} γ^{−1}))  ≤  γ/2 .
```

This module formalizes that note at the budget `E = C c⋆^{−1}` actually
supplied, in the anchor's OWN regime `γ ≤ C^{−10} c⋆^{10}`.

## The arithmetic, in full

Write `r := c⋆/C`, so that `E^{−1} = r` and the regime reads `γ ≤ r^{10}`.  With
`K := C_{(e.cg.ellip.lower)}` and `S := √(γ^{−1}) ≥ 1`:

* `S ≥ r^{−5}` (square both sides of `γ ≤ r^{10}`);
* `K^{−1} r² γ^{−1} = (K^{−1} r² S) S ≥ (K^{−1} r^{−3}) S ≥ 3 S`, the last step
  being exactly the hypothesis `3 K r³ ≤ 1`;
* `log(2/γ) = log 2 + log(S²) ≤ 1 + 2(S − 1) ≤ 3S`.

Hence `K^{−1} r² γ^{−1} ≥ log(2/γ)`, which is the window.  The hypothesis
`3 K r³ ≤ 1` is met by ANY constant `C ≥ max{6, K}`: `c⋆ ≤ 3/2` gives
`r ≤ (3/2)C^{−1}`, so `3 K r³ ≤ (81/8) K C^{−3}`, and `C ≥ 6` gives
`C³ ≥ 36 C ≥ 36 K ≥ (81/8) K`.  No `γ`-exponent and no `s`-power is moved: the
regime and the amplitude are the printed ones.

Only natural powers, `Real.sqrt`, `Real.log` and `Real.exp` appear; every
transcendental atom is kept opaque (no `nlinarith` anywhere).

## References

* ABK26, `p.cg.ellipticity.bounds`, (the `s`-range).
-/

namespace Algsuperdiff.Section4.Provider.BoundsEaL

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The abstract-real window -/

/-- **The abstract window.**  For `K, r, γ > 0` with `r ≤ 1`, `γ ≤ r^{10}` and
`3 K r³ ≤ 1`, the exponential `exp(−K^{−1}r²γ^{−1})` is at most `γ/2`. -/
private theorem exp_neg_le_half_of_cube_bound {K r gam : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hr1 : r ≤ 1) (hgam : 0 < gam) (hgam10 : gam ≤ r ^ 10)
    (hcube : 3 * K * r ^ 3 ≤ 1) :
    Real.exp (-(K⁻¹ * r ^ 2 * gam⁻¹)) ≤ gam / 2 := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hgne : gam ≠ 0 := ne_of_gt hgam
  have hginv : (0 : ℝ) < gam⁻¹ := inv_pos.mpr hgam
  have hr10 : (0 : ℝ) < r ^ 10 := by positivity
  have hgam1 : gam ≤ 1 := le_trans hgam10 (pow_le_one₀ hr.le hr1)
  have hL1 : (1 : ℝ) ≤ gam⁻¹ := by
    have h := mul_le_mul_of_nonneg_left hgam1 hginv.le
    rwa [mul_one, inv_mul_cancel₀ hgne] at h
  set S : ℝ := Real.sqrt gam⁻¹ with hSdef
  have hS2 : S ^ 2 = gam⁻¹ := Real.sq_sqrt hginv.le
  have hS0 : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hS1 : (1 : ℝ) ≤ S := by
    have h : Real.sqrt 1 ≤ S := Real.sqrt_le_sqrt hL1
    rwa [Real.sqrt_one] at h
  -- `S ≥ r^{-5}`
  have hrpow : ((r⁻¹) ^ 5) ^ 2 ≤ gam⁻¹ := by
    have hid : ((r⁻¹) ^ 5) ^ 2 = (r ^ 10)⁻¹ := by
      rw [← pow_mul, ← inv_pow]
    rw [hid]
    have h := mul_le_mul_of_nonneg_left hgam10
      (mul_nonneg (inv_nonneg.mpr hr10.le) hginv.le)
    have e1 : ((r ^ 10)⁻¹ * gam⁻¹) * gam = (r ^ 10)⁻¹ := by field_simp
    have e2 : ((r ^ 10)⁻¹ * gam⁻¹) * (r ^ 10) = gam⁻¹ := by field_simp
    rwa [e1, e2] at h
  have hrS : (r⁻¹) ^ 5 ≤ S := by
    have h : Real.sqrt (((r⁻¹) ^ 5) ^ 2) ≤ S := Real.sqrt_le_sqrt hrpow
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (r⁻¹) ^ 5)] at h
  -- `K^{-1} r^{-3} ≥ 3`
  have hKr : (3 : ℝ) ≤ K⁻¹ * (r⁻¹) ^ 3 := by
    have hpos : (0 : ℝ) < K * r ^ 3 := by positivity
    have hid : K⁻¹ * (r⁻¹) ^ 3 = (K * r ^ 3)⁻¹ := by
      rw [mul_inv, inv_pow]
    rw [hid, le_inv_comm₀ (by norm_num : (0 : ℝ) < 3) hpos,
      show (3 : ℝ)⁻¹ = 1 / 3 by norm_num]
    linarith only [hcube]
  -- the main chain `3S ≤ K^{-1} r² γ^{-1}`
  have hA0 : (0 : ℝ) < K⁻¹ * r ^ 2 := by positivity
  have hid2 : K⁻¹ * r ^ 2 * (r⁻¹) ^ 5 = K⁻¹ * (r⁻¹) ^ 3 := by
    field_simp
  have h3AS : (3 : ℝ) ≤ K⁻¹ * r ^ 2 * S := by
    have h := mul_le_mul_of_nonneg_left hrS hA0.le
    rw [hid2] at h
    exact le_trans hKr h
  have hchain : 3 * S ≤ K⁻¹ * r ^ 2 * gam⁻¹ := by
    have h := mul_le_mul_of_nonneg_right h3AS hS0
    have hid3 : (K⁻¹ * r ^ 2 * S) * S = K⁻¹ * r ^ 2 * gam⁻¹ := by
      rw [mul_assoc, ← pow_two, hS2]
    rwa [hid3] at h
  -- the logarithmic side
  have hlog : Real.log gam⁻¹ ≤ 2 * S := by
    have hlogS : Real.log S ≤ S - 1 :=
      Real.log_le_sub_one_of_pos (by linarith only [hS1])
    have hexp : Real.log (S ^ 2) = 2 * Real.log S := by
      rw [Real.log_pow]
      norm_num
    rw [← hS2, hexp]
    linarith only [hlogS]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hloginv : Real.log gam⁻¹ = -Real.log gam := Real.log_inv gam
  have hfin : -(K⁻¹ * r ^ 2 * gam⁻¹) ≤ Real.log (gam / 2) := by
    rw [Real.log_div hgne (by norm_num : (2 : ℝ) ≠ 0)]
    linarith only [hchain, hlog, hlog2, hS1, hloginv]
  calc Real.exp (-(K⁻¹ * r ^ 2 * gam⁻¹))
      ≤ Real.exp (Real.log (gam / 2)) := Real.exp_le_exp.mpr hfin
    _ = gam / 2 := Real.exp_log (by linarith only [hgam])

/-! ## 2. The amplitude is monotone in the budget `E` -/

/-- The Orlicz amplitude `exp(−C_cg^{−1}E^{−2}γ^{−1})` is nondecreasing in the
budget `E`: a larger `E` is a weaker conclusion. -/
theorem cgTailScale_mono (M : ABKModel d) {E E' : ℝ} (hE : 0 < E) (hEE : E ≤ E') :
    Proportion.cgTailScale M E ≤ Proportion.cgTailScale M E' := by
  have hE'0 : (0 : ℝ) < E' := lt_of_lt_of_le hE hEE
  have hK : (0 : ℝ) < Support.cgEllipLowerConstant d :=
    Support.cgEllipLowerConstant_pos d
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hinvle : E'⁻¹ ≤ E⁻¹ := by
    have hp := mul_le_mul_of_nonneg_left hEE
      (mul_nonneg (inv_nonneg.mpr hE.le) (inv_nonneg.mpr hE'0.le))
    have e1 : (E⁻¹ * E'⁻¹) * E = E'⁻¹ := by
      field_simp
    have e2 : (E⁻¹ * E'⁻¹) * E' = E⁻¹ := by
      field_simp
    rwa [e1, e2] at hp
  have hsq : (E'⁻¹) ^ 2 ≤ (E⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hE'0.le) hinvle 2
  rw [Proportion.cgTailScale, Proportion.cgTailScale]
  refine Real.exp_le_exp.mpr ?_
  have hmul := mul_le_mul_of_nonneg_left hsq
    (by positivity : (0 : ℝ) ≤ (Support.cgEllipLowerConstant d)⁻¹ * M.gamma⁻¹)
  linarith only [hmul]

/-! ## 3. The window at the anchor's own budget and regime -/

/-- **`hwin`, discharged.**  At the budget `E = C c⋆^{−1}` and in the anchor's own regime
`γ ≤ C^{−10} c⋆^{10}`, the `s`-window at `s = γ` holds for every constant `C ≥
max{6, C_{(e.cg.ellip.lower)}}`. -/
theorem cgTailScale_le_half_gamma (M : ABKModel d) {C : ℝ} (hC6 : 6 ≤ C)
    (hCcg : Support.cgEllipLowerConstant d ≤ C)
    (hreg : M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10) :
    Proportion.cgTailScale M (C * (Disorder.cstar M)⁻¹) ≤ M.gamma / 2 := by
  have hC0 : (0 : ℝ) < C := by linarith only [hC6]
  have hK : (0 : ℝ) < Support.cgEllipLowerConstant d :=
    Support.cgEllipLowerConstant_pos d
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hg : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  set r : ℝ := C⁻¹ * Disorder.cstar M with hrdef
  have hCinv : (0 : ℝ) < C⁻¹ := inv_pos.mpr hC0
  have hr : (0 : ℝ) < r := by
    rw [hrdef]; exact mul_pos hCinv hcs0
  have hrle : r ≤ 3 / 2 * C⁻¹ := by
    rw [hrdef]
    have := mul_le_mul_of_nonneg_left hcs hCinv.le
    linarith only [this]
  have hr1 : r ≤ 1 := by
    have hle : Disorder.cstar M ≤ C := by linarith only [hcs, hC6]
    have h := mul_le_mul_of_nonneg_left hle hCinv.le
    rw [inv_mul_cancel₀ (ne_of_gt hC0)] at h
    rw [hrdef]
    exact h
  -- the regime, rewritten at `r`
  have hgam10 : M.gamma ≤ r ^ 10 := by
    rw [hrdef, mul_pow]
    exact hreg
  -- the cube condition, from `C ≥ 6` and `C ≥ C_cg`
  have hC3 : 81 / 8 * Support.cgEllipLowerConstant d ≤ C ^ 3 := by
    have hsq : (36 : ℝ) ≤ C ^ 2 := by
      have h := mul_le_mul hC6 hC6 (by norm_num : (0 : ℝ) ≤ 6) (by linarith only [hC6])
      calc (36 : ℝ) = 6 * 6 := by norm_num
        _ ≤ C * C := h
        _ = C ^ 2 := by ring
    have hstep : (36 : ℝ) * C ≤ C ^ 2 * C := mul_le_mul_of_nonneg_right hsq hC0.le
    have hcube : C ^ 2 * C = C ^ 3 := by ring
    have hKC : (36 : ℝ) * Support.cgEllipLowerConstant d ≤ 36 * C :=
      mul_le_mul_of_nonneg_left hCcg (by norm_num)
    linarith only [hstep, hcube, hKC, hK]
  have hcube : 3 * Support.cgEllipLowerConstant d * r ^ 3 ≤ 1 := by
    have hrr : r ^ 3 ≤ (3 / 2 * C⁻¹) ^ 3 := pow_le_pow_left₀ hr.le hrle 3
    have hmul := mul_le_mul_of_nonneg_left hrr
      (by positivity : (0 : ℝ) ≤ 3 * Support.cgEllipLowerConstant d)
    have hexpand : 3 * Support.cgEllipLowerConstant d * (3 / 2 * C⁻¹) ^ 3 =
        81 / 8 * Support.cgEllipLowerConstant d * (C⁻¹) ^ 3 := by ring
    have hp : (0 : ℝ) ≤ (C⁻¹) ^ 3 := by positivity
    have hfin := mul_le_mul_of_nonneg_right hC3 hp
    have hone : C ^ 3 * (C⁻¹) ^ 3 = 1 := by
      field_simp
    rw [hone] at hfin
    linarith only [hmul, hexpand, hfin]
  -- the window
  have hEinv : (C * (Disorder.cstar M)⁻¹)⁻¹ = r := by
    rw [hrdef, mul_inv, inv_inv]
  rw [Proportion.cgTailScale, hEinv]
  exact exp_neg_le_half_of_cube_bound hK hr hr1 hg hgam10 hcube

/-! ## 4. The atom tail, unconditional in the anchor's regime -/

/-- **`Proportion.exists_cgExcess_atomTail` with its `hwin` premise removed.**

There is a dimensional constant `C` such that every model in the printed regime
`γ ≤ C^{−10}c⋆^{10}` has, at the budget `E = C c⋆^{−1}`, for every `k ∈ ℤ` and
every real centre `z`,

```
( σ_{k−3} λ_{γ,2}^{-1}(z+□_{k−2}; 𝐚_{k−2}) − C_{(e.cg.ellip.lower)} )_+
  ≤ 𝒪_{Γ_{1/3}} ( exp(−(C_cg C²)^{−1} c⋆² γ^{−1}) ) ,
```

with NO remaining hypothesis.  The constant is the proved one raised to
`C_{(e.cg.ellip.lower)}`, which is what makes the window self-discharging. -/
theorem exists_cgExcess_atomTail_unconditional (d : ℕ) :
    ∃ C : ℝ, 6 ≤ C ∧
      ∀ M : ABKModel d,
        M.gamma ≤ (C⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 →
        ∃ E : {E : ℝ // 1 ≤ E},
          (E : ℝ) = C * (Disorder.cstar M)⁻¹ ∧
            ∀ (k : ℤ) (z : Vec d),
              IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
                (gammaSigma (1 / 3 : ℝ))
                (fun omega =>
                  Localize.cgExcess M (Support.cgEllipLowerConstant d) (k - 2) z omega)
                (Proportion.cgTailScale M (E : ℝ)) := by
  obtain ⟨C0, hC06, hall⟩ := Proportion.exists_cgExcess_atomTail d
  refine ⟨max C0 (Support.cgEllipLowerConstant d), le_trans hC06 (le_max_left _ _), ?_⟩
  intro M hreg
  set C : ℝ := max C0 (Support.cgEllipLowerConstant d) with hCdef
  have hC0le : C0 ≤ C := le_max_left _ _
  have hKle : Support.cgEllipLowerConstant d ≤ C := le_max_right _ _
  have hC6 : (6 : ℝ) ≤ C := le_trans hC06 hC0le
  have hC00 : (0 : ℝ) < C0 := by linarith only [hC06]
  have hCpos : (0 : ℝ) < C := by linarith only [hC6]
  have hcs0 : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcs : Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hcsinv : (0 : ℝ) < (Disorder.cstar M)⁻¹ := inv_pos.mpr hcs0
  have hinvle : C⁻¹ ≤ C0⁻¹ := by
    have hp := mul_le_mul_of_nonneg_left hC0le
      (mul_nonneg (inv_nonneg.mpr hC00.le) (inv_nonneg.mpr hCpos.le))
    have e1 : (C0⁻¹ * C⁻¹) * C0 = C⁻¹ := by field_simp
    have e2 : (C0⁻¹ * C⁻¹) * C = C0⁻¹ := by field_simp
    rwa [e1, e2] at hp
  have hreg0 : M.gamma ≤ (C0⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
    have hpow : (C⁻¹) ^ 10 ≤ (C0⁻¹) ^ 10 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hCpos.le) hinvle 10
    have hmul := mul_le_mul_of_nonneg_right hpow
      (by positivity : (0 : ℝ) ≤ (Disorder.cstar M) ^ 10)
    exact le_trans hreg hmul
  obtain ⟨E0, hE0val, htail⟩ := hall M hreg0
  have hE0pos : (0 : ℝ) < (E0 : ℝ) := lt_of_lt_of_le zero_lt_one E0.2
  have hE0le : (E0 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ := by
    rw [hE0val]
    exact mul_le_mul_of_nonneg_right hC0le hcsinv.le
  have hwin : Proportion.cgTailScale M (E0 : ℝ) ≤ M.gamma / 2 :=
    le_trans (cgTailScale_mono M hE0pos hE0le)
      (cgTailScale_le_half_gamma M hC6 hKle hreg)
  -- the upgraded budget is admissible
  have hone : (1 : ℝ) ≤ C * (Disorder.cstar M)⁻¹ := by
    have hge : (2 : ℝ) / 3 ≤ (Disorder.cstar M)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 2 / 3) hcs0]
      calc Disorder.cstar M ≤ 3 / 2 := hcs
        _ = ((2 : ℝ) / 3)⁻¹ := by norm_num
    have hstep : (6 : ℝ) * (2 / 3) ≤ C * (Disorder.cstar M)⁻¹ :=
      mul_le_mul hC6 hge (by norm_num) (by linarith only [hC6])
    linarith only [hstep]
  refine ⟨⟨C * (Disorder.cstar M)⁻¹, hone⟩, rfl, fun k z => ?_⟩
  exact (htail hwin k z).mono_scale (cgTailScale_mono M hE0pos hE0le)

end

end Algsuperdiff.Section4.Provider.BoundsEaL
