/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ShomContinuityCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Two-sided diffusivity comparator: a model-free arithmetic core

This file is **model-free deterministic arithmetic**.  Everything below is
stated for an abstract sequence `s : ℤ → ℝ` and an abstract two-sided
comparator `diffMax`; no renormalization, probabilistic, or geometric object
occurs, and every hypothesis is an explicit input supplied by the caller rather
than a source premise of any frozen theorem.

The genuine long-range step additionally requires the asymptotic diffusivity
profile of `p.propagate.diffusivity.lower.bound` (ABK26), which is neither used
nor asserted here.  What this file provides is the arithmetic that the
manuscript performs *after* that profile has been consumed, i.e. the two steps
that use only the two-sided envelope `e.shom.h.bounds`.

## Source

`e.shom.h.bounds` (ABK26) reads

  `¼ max{c⋆ γ⁻¹ 3^{2γm}, ν²} ≤ σ_m² ≤ 4 max{c⋆ γ⁻¹ 3^{2γm}, ν²}`,

and `diffMax` below is exactly the bracketed maximum.

* The quarter comparison is ABK26: `σ_m² ≥ ¼ max{c⋆γ⁻¹3^{2γm},ν²} ≥ ¼
  max{c⋆γ⁻¹3^{2γn},ν²} ≥ 1/16 σ_n²`, "Taking square roots gives `σ_m ≥ ¼
  σ_n`".
* The far branch is ABK26: for `m − n ≥ γ⁻¹`, `|σ_m σ_n⁻¹ − 1| + |σ_n σ_m⁻¹
  − 1| ≤^{γ(m−n)}`.  The manuscript leaves `C` unnamed; the explicit witness
  proved here is `8`.  The argument in fact delivers `4·3^{γ(m−n)} + 2`, hence
  also the sharper `6·3^{γ(m−n)}`; `8` is retained as the stated constant.

Both statements below are proved under `n ≤ m` although the source range is
`m > n`; the extra equality case costs nothing and is not used to weaken any
conclusion.  Neither statement uses the source's regime split, the constraint
`γ ≤ E^{-10}`, or the endpoint `m₀`: they hold whenever the caller exhibits the
two-sided envelope at the two scales.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ShomContinuityCore

noncomputable section

/-- The two-sided comparator `max{c⋆ γ⁻¹ 3^{2γk}, ν²}` bracketing `σ_k²` in
`e.shom.h.bounds` (ABK26). -/
def diffMax (nu gamma cstar : ℝ) (k : ℤ) : ℝ :=
  max (cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (k : ℝ))) (nu ^ 2)

/-! ### Auxiliary pure-algebra facts

These two lemmas are over abstract reals; they contain no `Real.rpow`, so the
arithmetic tactics below never meet a transcendental atom. -/

/-- Comparison through squares: a real dominated in square by a nonnegative real
is dominated. -/
private lemma le_of_sq_le_sq_nonneg {x y : ℝ} (hy : 0 ≤ y) (hsq : x ^ 2 ≤ y ^ 2) :
    x ≤ y := by
  by_contra hcon
  push Not at hcon
  have hsum : (0 : ℝ) < x + y := by linarith
  have hprod : 0 < (x - y) * (x + y) := mul_pos (by linarith) hsum
  linarith [hprod, hsq]

/-- Pure-algebra core of the far branch.  Once `y ≤ 4x` and `x ≤ 4ty` with
`t ≥ 1`, the two-sided ratio defect is at most `4t + 2`, hence at most `8t`
(and even `6t`). -/
private lemma ratioSum_le_eight_mul {x y t : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ht : 1 ≤ t) (h1 : y ≤ 4 * x) (h2 : x ≤ 4 * t * y) :
    |x / y - 1| + |y / x - 1| ≤ 8 * t := by
  have hxy : 0 ≤ x / y := div_nonneg hx.le hy.le
  have hyx : 0 ≤ y / x := div_nonneg hy.le hx.le
  have e1 : x / y ≤ 4 * t := by
    rw [div_le_iff₀ hy]
    linarith only [h2]
  have e2 : y / x ≤ 4 := by
    rw [div_le_iff₀ hx]
    linarith only [h1]
  have hA : |x / y - 1| ≤ 4 * t - 1 := by
    rw [abs_le]
    exact ⟨by linarith only [hxy, ht], by linarith only [e1]⟩
  have hB : |y / x - 1| ≤ 3 := by
    rw [abs_le]
    exact ⟨by linarith only [hyx], by linarith only [e2]⟩
  linarith only [hA, hB, ht]

/-! ### Elementary properties of the comparator -/

/-- The comparator is nondecreasing in the scale: `c⋆γ⁻¹3^{2γk}` increases and
`ν²` is constant.  This is the second inequality of ABK26. -/
theorem diffMax_mono {nu gamma cstar : ℝ} (hgamma : 0 < gamma) (hcstar : 0 < cstar)
    {n m : ℤ} (hnm : n ≤ m) :
    diffMax nu gamma cstar n ≤ diffMax nu gamma cstar m := by
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hexp : 2 * gamma * (n : ℝ) ≤ 2 * gamma * (m : ℝ) :=
    mul_le_mul_of_nonneg_left hcast (by linarith)
  have hpow : (3 : ℝ) ^ (2 * gamma * (n : ℝ)) ≤ (3 : ℝ) ^ (2 * gamma * (m : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hcoef : (0 : ℝ) ≤ cstar * gamma⁻¹ :=
    mul_nonneg hcstar.le (inv_nonneg.mpr hgamma.le)
  simp only [diffMax]
  exact max_le_max (mul_le_mul_of_nonneg_left hpow hcoef) le_rfl

/-- Geometric growth of the comparator:
`max{c⋆γ⁻¹3^{2γm},ν²} ≤ 3^{2γ(m−n)} max{c⋆γ⁻¹3^{2γn},ν²}` for `n ≤ m`.
The first summand scales exactly by `3^{2γ(m−n)}`, and the constant summand
`ν²` only grows when multiplied by a factor `≥ 1`. -/
theorem diffMax_le_rpow_mul {nu gamma cstar : ℝ} (hgamma : 0 < gamma) {n m : ℤ}
    (hnm : n ≤ m) :
    diffMax nu gamma cstar m
      ≤ (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) * diffMax nu gamma cstar n := by
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hexp : (0 : ℝ) ≤ 2 * gamma * ((m : ℝ) - (n : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hT1 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) := by
    calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 3).symm
      _ ≤ (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hT0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) :=
    le_trans zero_le_one hT1
  have hsplit : (3 : ℝ) ^ (2 * gamma * (m : ℝ))
      = (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (2 * gamma * (n : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  simp only [diffMax]
  rw [hsplit]
  have hmaxnn :
      (0 : ℝ) ≤ max (cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (n : ℝ))) (nu ^ 2) :=
    le_trans (sq_nonneg nu) (le_max_right _ _)
  refine max_le ?_ ?_
  · calc cstar * gamma⁻¹ *
          ((3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) *
            (3 : ℝ) ^ (2 * gamma * (n : ℝ)))
        = (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) *
            (cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (n : ℝ))) := by ring
      _ ≤ (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) *
            max (cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (n : ℝ))) (nu ^ 2) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hT0
  · calc nu ^ 2
        ≤ max (cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (n : ℝ))) (nu ^ 2) :=
          le_max_right _ _
      _ ≤ (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) *
            max (cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (n : ℝ))) (nu ^ 2) :=
          le_mul_of_one_le_left hmaxnn hT1

/-! ### The two regime-free consequences of the two-sided envelope -/

/-- **Quarter comparison** (ABK26).  From the lower envelope at `m`, the upper
envelope at `n`, and monotonicity of the comparator, `σ_m² ≥ ¼ diffMax_m ≥ ¼
diffMax_n ≥ 1/16 σ_n²`, and taking square roots gives `¼ σ_n ≤ σ_m`.  Only
two of the four envelope inequalities are needed. -/
theorem quarter_le_of_twoSided {nu gamma cstar : ℝ} {s : ℤ → ℝ} {n m : ℤ}
    (hgamma : 0 < gamma) (hcstar : 0 < cstar) (hnm : n ≤ m) (hsm : 0 < s m)
    (hlo_m : 1 / 4 * diffMax nu gamma cstar m ≤ s m ^ 2)
    (hhi_n : s n ^ 2 ≤ 4 * diffMax nu gamma cstar n) :
    1 / 4 * s n ≤ s m := by
  have hmono : diffMax nu gamma cstar n ≤ diffMax nu gamma cstar m :=
    diffMax_mono hgamma hcstar hnm
  have hsq : (1 / 4 * s n) ^ 2 ≤ s m ^ 2 := by
    have hexpand : (1 / 4 * s n) ^ 2 = 1 / 16 * s n ^ 2 := by ring
    linarith only [hlo_m, hhi_n, hmono, hexpand]
  exact le_of_sq_le_sq_nonneg hsm.le hsq

/-- **Far branch** (ABK26).  From the two-sided envelope at both scales, `σ_n ≤
4σ_m` and `σ_m ≤ 4·3^{γ(m−n)}σ_n`, whence

  `|σ_m σ_n⁻¹ − 1| + |σ_n σ_m⁻¹ − 1| ≤ 8·3^{γ(m−n)}`.

The manuscript states this with an unnamed `C`; `8` is an explicit witness (the
proof actually yields `4·3^{γ(m−n)} + 2`).  No regime constraint on `m − n` is
used: the bound holds for every `n ≤ m` at which the envelope is available. -/
theorem ratioSum_le_of_twoSided {nu gamma cstar : ℝ} {s : ℤ → ℝ} {n m : ℤ}
    (hgamma : 0 < gamma) (hcstar : 0 < cstar) (hnm : n ≤ m)
    (hsm : 0 < s m) (hsn : 0 < s n)
    (hlo_m : 1 / 4 * diffMax nu gamma cstar m ≤ s m ^ 2)
    (hhi_m : s m ^ 2 ≤ 4 * diffMax nu gamma cstar m)
    (hlo_n : 1 / 4 * diffMax nu gamma cstar n ≤ s n ^ 2)
    (hhi_n : s n ^ 2 ≤ 4 * diffMax nu gamma cstar n) :
    |s m / s n - 1| + |s n / s m - 1|
      ≤ 8 * (3 : ℝ) ^ (gamma * ((m : ℝ) - (n : ℝ))) := by
  have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hexp : (0 : ℝ) ≤ gamma * ((m : ℝ) - (n : ℝ)) :=
    mul_nonneg hgamma.le (by linarith)
  have ht1 : (1 : ℝ) ≤ (3 : ℝ) ^ (gamma * ((m : ℝ) - (n : ℝ))) := by
    calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 3).symm
      _ ≤ (3 : ℝ) ^ (gamma * ((m : ℝ) - (n : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hsquare : (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ)))
      = (3 : ℝ) ^ (gamma * ((m : ℝ) - (n : ℝ))) *
        (3 : ℝ) ^ (gamma * ((m : ℝ) - (n : ℝ))) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hratio := diffMax_le_rpow_mul (nu := nu) (cstar := cstar) hgamma hnm
  rw [hsquare] at hratio
  have hmono : diffMax nu gamma cstar n ≤ diffMax nu gamma cstar m :=
    diffMax_mono hgamma hcstar hnm
  -- abstract the geometric factor: from here on the arithmetic is `rpow`-free
  set t : ℝ := (3 : ℝ) ^ (gamma * ((m : ℝ) - (n : ℝ)))
  clear_value t
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
  have htt : (0 : ℝ) ≤ t * t := mul_nonneg ht0 ht0
  -- `σ_n ≤ 4 σ_m`
  have hb1 : s n ≤ 4 * s m := by
    refine le_of_sq_le_sq_nonneg (by linarith only [hsm.le] : (0 : ℝ) ≤ 4 * s m) ?_
    have hexpand : (4 * s m) ^ 2 = 16 * s m ^ 2 := by ring
    linarith only [hhi_n, hmono, hlo_m, hexpand]
  -- `σ_m ≤ 4 t σ_n`
  have hDn : diffMax nu gamma cstar n ≤ 4 * s n ^ 2 := by linarith only [hlo_n]
  have hstep : t * t * diffMax nu gamma cstar n ≤ t * t * (4 * s n ^ 2) :=
    mul_le_mul_of_nonneg_left hDn htt
  have hb2 : s m ≤ 4 * t * s n := by
    refine le_of_sq_le_sq_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) ht0) hsn.le) ?_
    have hexpand : (4 * t * s n) ^ 2 = 16 * (t * t * s n ^ 2) := by ring
    linarith only [hhi_m, hratio, hstep, hexpand]
  exact ratioSum_le_eight_mul hsm hsn ht1 hb1 hb2

end

end Algsuperdiff.Section3.Provider.Diffusivity.ShomContinuityCore
