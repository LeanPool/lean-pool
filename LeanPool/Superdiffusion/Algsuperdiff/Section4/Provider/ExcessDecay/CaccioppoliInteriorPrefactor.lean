/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CaccioppoliInteriorDatum
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Public

/-!
# CaccioppoliInteriorPrefactor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Discharging the Caccioppoli prefactor from the good-event ellipticity caps

CoarseGraining's coarse Caccioppoli with right-hand side carries the prefactor

```text
  (C/σ)^{2 + 4s/σ} · s^{-2s/σ} · Θ_{s,t}^{(1-t)/σ} ,      σ = 1 - s - t ,
```

with `Θ_{s,t} = Λ_{s,1}/λ_{t,1}` — the **`q = 1`** coarse-grained ellipticity
constants.  The proved good-event caps (`GoodEventCaps.lean`,
`SlotTransportChildCube.lean`) bound the **`q = 2`** ratios.  This module
supplies the two missing pieces:

1. **the `q = 1 ← q = 2` comparison for `Λ` and `λ⁻¹`** (§1).  The weights of
   the two definitions coincide, `w_{u,1} = w_{u/2,2}`, and CoarseGraining's
   own Jensen split then gives
   ```text
     Λ_{u,1} ≤ Λ_{u/2,2} ,      λ_{u,1}^{-1} ≤ λ_{u/2,2}^{-1}
   ```
   with **no constant**.
2. **the parameter choice that makes the prefactor a dimensional constant**
   (§2--§3).  The Caccioppoli's first exponent is a *free parameter* of the
   lemma; taking it to be the absolute constant `1/4` and the second to be
   `t = s/4` gives, for every `s ∈ (0,1]`,
   ```text
     σ = 3/4 - s/4 ∈ [1/2, 3/4) ,   2 + 4·(1/4)/σ ≤ 4 ,
     (1/4)^{-2·(1/4)/σ} ≤ 4 ,       (1-t)/σ ≤ 2 ,
   ```
   so the prefactor is at most `(2 max(1,C))^4 · 4 · Θ_0^2` — **no transcendental
   estimate is needed anywhere**, and the whole `s`-dependence of the estimate is
   pushed into the forcing factor `t^{-8}(1-2t)^{-1} ≤ 131072 s^{-8}` (§3).

The index choice is exactly what the caps admit: the `q = 1 ← q = 2` step at
index `u` needs the `q = 2` cap at `u/2`, and the caps hold for every `q = 2`
index `≥ s/8`; here `u = 1/4` gives `1/8 ≥ s/8` (as `s ≤ 1`) and `u = s/4` gives
exactly `s/8`.

## Deviation from print, recorded

The specialization chosen here is `(1/4, s/4)`; it yields the *squared* forcing
envelope `s^{-8}`, i.e. `s^{-4}` on the un-squared display, which is
**stronger** than the printed `s^{-11/2}` on `0 < s ≤ 1` (`s^{-8} ≤ s^{-11}`
squared).  Both forms are delivered: the honest `s^{-8}` and, by weakening, the
printed `s^{-11}`.

## References

* ABK26, `l.coarse.grained.Caccioppoli.RHS`; `e.energy.bound.interior`;
  `e.compareEqs`.
* CoarseGraining,
  `Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale`,
  `Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale`,
  `Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum`, `Ch02.one_le_ThetaRatio_of_pos`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The `q = 1 ← q = 2` comparison for the ellipticity constants -/

/-- The `q = 2` weight at index `u/2` is the `q = 1` weight at index `u`. -/
private theorem weight_two_half_eq (u : ℝ) (l : ℕ) :
    Ch02.geometricWeight (u / 2) 2 l = Ch02.geometricWeight u 1 l := by
  have h := HCPolySupport.geometricWeight_eq_mul_one (u / 2) 2 l
  have huu : u / 2 * 2 = u := by ring
  rw [huu] at h
  simp only [Ch02.geometricWeight_eq_old] at h ⊢
  exact h

/-- `Λ_{u,2}` is the weighted shell series of the operator norms. -/
theorem LambdaSq_finite_two_eq_tsum (Q : TriadicCube d)
    (a : CoeffFamily d) {u : ℝ} (hu : 0 < u) :
    Ch02.LambdaSq Q u (.finite 2) a =
      ∑' n : ℕ, Ch02.geometricWeight u 2 n *
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  have h := Ch02.LambdaSqFinite_rpow_q_div_two_eq_tsum Q u 2 a (by norm_num)
    (by positivity)
  rw [show (2 : ℝ) / 2 = 1 by norm_num] at h
  simp only [Real.rpow_eq_pow, Real.rpow_one] at h
  exact h

/-- `λ_{u,2}⁻¹` is the weighted shell series of the inverse lower norms. -/
theorem lambdaSq_finite_two_inv_eq_tsum (Q : TriadicCube d)
    (a : CoeffFamily d) {u : ℝ} (hu : 0 < u) :
    (Ch02.lambdaSq Q u (.finite 2) a)⁻¹ =
      ∑' n : ℕ, Ch02.geometricWeight u 2 n *
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a := by
  have h := Ch02.lambdaSqFinite_rpow_neg_q_div_two_eq_tsum Q u 2 a (by norm_num)
    (by positivity)
  rw [show (-2 : ℝ) / 2 = -1 by norm_num,
    show (2 : ℝ) / 2 = 1 by norm_num] at h
  simp only [Real.rpow_eq_pow, Real.rpow_neg_one, Real.rpow_one] at h
  exact h

/-- **The `q = 1 ← q = 2` comparison for the upper constant.**

```text
  Λ_{u,1}(Q; a) ≤ Λ_{u/2,2}(Q; a)
```

with no constant: the two weight families coincide and CoarseGraining's Jensen
split turns the `q = 1` square root into the `q = 2` linear series. -/
theorem LambdaSq_finite_one_le_finite_two_half [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) {u : ℝ} (hu : 0 < u) :
    Ch02.LambdaSq Q u (.finite 1) a ≤ Ch02.LambdaSq Q (u / 2) (.finite 2) a := by
  have hJ :=
    Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale Q a hu
  rw [LambdaSq_finite_two_eq_tsum Q a (by linarith only [hu] : (0 : ℝ) < u / 2)]
  refine hJ.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [weight_two_half_eq]

/-- **The `q = 1 ← q = 2` comparison for the inverse lower constant.**

```text
  λ_{u,1}(Q; a)⁻¹ ≤ λ_{u/2,2}(Q; a)⁻¹ .
```
-/
theorem lambdaSq_finite_one_inv_le_finite_two_half [NeZero d] (Q : TriadicCube d)
    (a : CoeffFamily d) {u : ℝ} (hu : 0 < u) :
    (Ch02.lambdaSq Q u (.finite 1) a)⁻¹ ≤
      (Ch02.lambdaSq Q (u / 2) (.finite 2) a)⁻¹ := by
  have hJ :=
    Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
      Q a hu
  rw [lambdaSq_finite_two_inv_eq_tsum Q a (by linarith only [hu] : (0 : ℝ) < u / 2)]
  refine hJ.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [weight_two_half_eq]

/-! ## 2. From the `q = 2` ratio cap to the `q = 1` ingredients -/

/-- **The upper `q = 1` cap.**  A `q = 2` ratio cap at index `u/2` caps the
`q = 1` upper constant at index `u`. -/
theorem LambdaS_le_of_ratio_cap [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {u sigma K : ℝ} (hu : 0 < u) (hsigma : 0 < sigma)
    (hcap : sigma⁻¹ * Ch02.LambdaSq Q (u / 2) (.finite 2) a ≤ K) :
    Ch02.LambdaS Q u a ≤ K * sigma := by
  have hq := LambdaSq_finite_one_le_finite_two_half Q a hu
  have hkey : sigma⁻¹ * Ch02.LambdaSq Q u (.finite 1) a ≤ K :=
    le_trans (mul_le_mul_of_nonneg_left hq (inv_nonneg.mpr hsigma.le)) hcap
  rw [Ch02.LambdaS]
  have hmul := mul_le_mul_of_nonneg_right hkey hsigma.le
  rw [inv_mul_eq_div, div_mul_cancel₀ _ hsigma.ne'] at hmul
  exact hmul

/-- **The lower `q = 1` cap.**  A `q = 2` ratio cap at index `u/2` caps the
inverse `q = 1` lower constant at index `u`. -/
theorem lambdaS_inv_le_of_ratio_cap [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {u sigma K : ℝ} (hu : 0 < u) (hsigma : 0 < sigma)
    (hcap : sigma * (Ch02.lambdaSq Q (u / 2) (.finite 2) a)⁻¹ ≤ K) :
    (Ch02.lambdaS Q u a)⁻¹ ≤ K * sigma⁻¹ := by
  have hq := lambdaSq_finite_one_inv_le_finite_two_half Q a hu
  have hkey : sigma * (Ch02.lambdaSq Q u (.finite 1) a)⁻¹ ≤ K :=
    le_trans (mul_le_mul_of_nonneg_left hq hsigma.le) hcap
  rw [Ch02.lambdaS]
  have hmul := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hsigma.le)
  rw [mul_comm sigma, mul_assoc, mul_inv_cancel₀ hsigma.ne', mul_one] at hmul
  exact hmul

/-- The lower constant is dominated by the upper one at any two positive indices
(CoarseGraining's `one_le_ThetaRatio_of_pos`, read as an inequality). -/
theorem lambdaS_le_LambdaS [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Ch02.lambdaS Q t a ≤ Ch02.LambdaS Q s a := by
  have h1 := Ch02.one_le_ThetaRatio_of_pos Q a hs ht
  have hpos : 0 < Ch02.lambdaS Q t a := by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num)
  rw [Ch02.ThetaRatio] at h1
  exact (one_le_div hpos).mp h1

/-- **The contrast `Θ` is capped by the product of the two `q = 1` caps.** -/
theorem thetaRatio_le_of_caps (Q : TriadicCube d) (a : CoeffFamily d)
    {s t B1 B2 : ℝ} (hs : 0 < s) (ht : 0 < t) (hB1 : Ch02.LambdaS Q s a ≤ B1)
    (hB2 : (Ch02.lambdaS Q t a)⁻¹ ≤ B2) :
    Ch02.ThetaRatio Q s t a ≤ B1 * B2 := by
  have hLnn : 0 ≤ Ch02.LambdaS Q s a := by
    rw [Ch02.LambdaS]
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num)
  rw [Ch02.ThetaRatio, div_eq_mul_inv]
  exact mul_le_mul hB1 hB2 (inv_nonneg.mpr (by
    rw [Ch02.lambdaS]
    exact Ch02.lambdaSq_finite_nonneg Q a ht (by norm_num))) (le_trans hLnn hB1)

/-! ## 3. The prefactor and the forcing factor at the chosen parameters -/

/-- **The prefactor at `(s_c, t_c) = (1/4, s/4)` is a constant.**

For every `s ∈ (0,1]`, every `C ≥ 1` and every cap `Θ ≤ Θ₀`,

```text
  (C/σ)^{2+4·(1/4)/σ} · (1/4)^{-2·(1/4)/σ} · Θ^{(1-s/4)/σ} ≤ (2C)^4 · 4 · Θ₀² ,
```

`σ = 1 - 1/4 - s/4 ∈ [1/2, 3/4)`.  Every step is a rational comparison of rpow
exponents; no transcendental estimate is used. -/
theorem caccioppoliWithRHSPrefactor_quarter_le [NeZero d] {Q : TriadicCube d}
    {a : CoeffFamily d} {C s Theta0 : ℝ} (hC : 0 < C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hTheta : Ch02.ThetaRatio Q (1 / 4) (s / 4) a ≤ Theta0) :
    caccioppoliWithRHSPrefactor C Q a (1 / 4) (s / 4) ≤
      (2 * max 1 C) ^ (4 : ℕ) * 4 * Theta0 ^ (2 : ℕ) := by
  have hCm : (1 : ℝ) ≤ max 1 C := le_max_left _ _
  have hCle : C ≤ max 1 C := le_max_right _ _
  have hTh1 : 1 ≤ Ch02.ThetaRatio Q (1 / 4) (s / 4) a :=
    Ch02.one_le_ThetaRatio_of_pos Q a (by norm_num) (by linarith only [hs])
  have hsg_lo : (1 : ℝ) / 2 ≤ 1 - 1 / 4 - s / 4 := by linarith only [hs1]
  have hsg_pos : (0 : ℝ) < 1 - 1 / 4 - s / 4 := by linarith only [hsg_lo]
  have hsg_hi : 1 - 1 / 4 - s / 4 ≤ 1 := by linarith only [hs]
  have hinv : (1 - 1 / 4 - s / 4)⁻¹ ≤ 2 := by
    have h := inv_anti₀ (show (0 : ℝ) < 1 / 2 by norm_num) hsg_lo
    rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num] at h
    exact h
  have hCpos : (0 : ℝ) < C := hC
  have hCmpos : (0 : ℝ) < max 1 C := lt_of_lt_of_le zero_lt_one hCm
  -- the first factor
  have hbase0 : (0 : ℝ) ≤ C / (1 - 1 / 4 - s / 4) :=
    div_nonneg hCpos.le hsg_pos.le
  have hbase2 : C / (1 - 1 / 4 - s / 4) ≤ 2 * max 1 C := by
    rw [div_le_iff₀ hsg_pos]
    have hstep : 2 * max 1 C * (1 / 2) ≤ 2 * max 1 C * (1 - 1 / 4 - s / 4) :=
      mul_le_mul_of_nonneg_left hsg_lo (by linarith only [hCmpos])
    linarith only [hstep, hCle]
  have he1 : (4 : ℝ) * (1 / 4) / (1 - 1 / 4 - s / 4) ≤ 2 := by
    rw [show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_div]
    exact hinv
  have he1nn : (0 : ℝ) ≤ 2 + 4 * (1 / 4) / (1 - 1 / 4 - s / 4) := by
    have : (0 : ℝ) ≤ 4 * (1 / 4) / (1 - 1 / 4 - s / 4) := by positivity
    linarith only [this]
  have hT1 : Real.rpow (C / (1 - 1 / 4 - s / 4))
      (2 + 4 * (1 / 4) / (1 - 1 / 4 - s / 4)) ≤ (2 * max 1 C) ^ (4 : ℕ) := by
    calc Real.rpow (C / (1 - 1 / 4 - s / 4))
          (2 + 4 * (1 / 4) / (1 - 1 / 4 - s / 4))
        ≤ Real.rpow (2 * max 1 C) (2 + 4 * (1 / 4) / (1 - 1 / 4 - s / 4)) :=
          Real.rpow_le_rpow hbase0 hbase2 he1nn
      _ ≤ Real.rpow (2 * max 1 C) (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith only [hCm])
            (by linarith only [he1])
      _ = (2 * max 1 C) ^ (4 : ℕ) := by
          rw [Real.rpow_eq_pow, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
  -- the second factor
  have he2 : (-1 : ℝ) ≤ -(2 * (1 / 4) / (1 - 1 / 4 - s / 4)) := by
    have hhalf : (2 : ℝ) * (1 / 4) / (1 - 1 / 4 - s / 4) ≤ 1 := by
      rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, div_le_one hsg_pos]
      exact hsg_lo
    linarith only [hhalf]
  have hT2 : Real.rpow (1 / 4 : ℝ) (-(2 * (1 / 4) / (1 - 1 / 4 - s / 4))) ≤ 4 := by
    calc Real.rpow (1 / 4 : ℝ) (-(2 * (1 / 4) / (1 - 1 / 4 - s / 4)))
        ≤ Real.rpow (1 / 4 : ℝ) (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) he2
      _ = 4 := by rw [Real.rpow_eq_pow, Real.rpow_neg_one]; norm_num
  -- the third factor
  have he3 : (1 - s / 4) / (1 - 1 / 4 - s / 4) ≤ 2 := by
    rw [div_le_iff₀ hsg_pos]
    linarith only [hs1]
  have he3nn : (0 : ℝ) ≤ (1 - s / 4) / (1 - 1 / 4 - s / 4) := by
    have hnum : (0 : ℝ) ≤ 1 - s / 4 := by linarith only [hs1]
    exact div_nonneg hnum hsg_pos.le
  have hT3 : Real.rpow (Ch02.ThetaRatio Q (1 / 4) (s / 4) a)
      ((1 - s / 4) / (1 - 1 / 4 - s / 4)) ≤ Theta0 ^ (2 : ℕ) := by
    calc Real.rpow (Ch02.ThetaRatio Q (1 / 4) (s / 4) a)
          ((1 - s / 4) / (1 - 1 / 4 - s / 4))
        ≤ Real.rpow (Ch02.ThetaRatio Q (1 / 4) (s / 4) a) (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hTh1 he3
      _ ≤ Real.rpow Theta0 (2 : ℝ) :=
          Real.rpow_le_rpow (le_trans zero_le_one hTh1) hTheta (by norm_num)
      _ = Theta0 ^ (2 : ℕ) := by
          rw [Real.rpow_eq_pow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
  -- assemble
  have hT1nn : (0 : ℝ) ≤ Real.rpow (C / (1 - 1 / 4 - s / 4))
      (2 + 4 * (1 / 4) / (1 - 1 / 4 - s / 4)) :=
    Real.rpow_nonneg hbase0 _
  have hT2nn : (0 : ℝ) ≤ Real.rpow (1 / 4 : ℝ)
      (-(2 * (1 / 4) / (1 - 1 / 4 - s / 4))) :=
    Real.rpow_nonneg (by norm_num) _
  have hT3nn : (0 : ℝ) ≤ Real.rpow (Ch02.ThetaRatio Q (1 / 4) (s / 4) a)
      ((1 - s / 4) / (1 - 1 / 4 - s / 4)) :=
    Real.rpow_nonneg (le_trans zero_le_one hTh1) _
  have hprod1 : (0 : ℝ) ≤ (2 * max 1 C) ^ (4 : ℕ) * 4 := by positivity
  rw [caccioppoliWithRHSPrefactor]
  exact mul_le_mul (mul_le_mul hT1 hT2 hT2nn (by positivity)) hT3 hT3nn hprod1

/-- **The forcing factor.**  At `t = s/4` with `s ∈ (0,1]`,

```text
  t^{-8} (1 - 2t)^{-1} ≤ 131072 · s^{-8} .
```
-/
theorem forcing_factor_quarter_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (s / 4) (-8 : ℝ) / (1 - 2 * (s / 4)) ≤
      131072 * Real.rpow s (-8 : ℝ) := by
  have hden : (1 : ℝ) / 2 ≤ 1 - 2 * (s / 4) := by linarith only [hs1]
  have hdenpos : (0 : ℝ) < 1 - 2 * (s / 4) := by linarith only [hden]
  have h4 : Real.rpow (4 : ℝ) (-8 : ℝ) = (65536 : ℝ)⁻¹ := by
    rw [Real.rpow_eq_pow, show (-8 : ℝ) = ((-8 : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast]
    norm_num
  have hsplit : Real.rpow (s / 4) (-8 : ℝ) = 65536 * Real.rpow s (-8 : ℝ) := by
    rw [Real.rpow_eq_pow, Real.div_rpow hs.le (by norm_num),
      ← Real.rpow_eq_pow s, ← Real.rpow_eq_pow (4 : ℝ), h4]
    field_simp
  have hnn : (0 : ℝ) ≤ Real.rpow s (-8 : ℝ) := Real.rpow_nonneg hs.le _
  rw [hsplit, div_le_iff₀ hdenpos]
  have hstep : 131072 * Real.rpow s (-8 : ℝ) * (1 / 2) ≤
      131072 * Real.rpow s (-8 : ℝ) * (1 - 2 * (s / 4)) :=
    mul_le_mul_of_nonneg_left hden (by positivity)
  linarith only [hstep]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
