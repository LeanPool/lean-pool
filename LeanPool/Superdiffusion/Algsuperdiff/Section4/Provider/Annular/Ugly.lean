/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ugly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The five-term per-cube ("ugly") estimate on the good event

ABK26, Section 4.1, (`e.ugly.estimate.for.J`).  The manuscript takes the four
sensitivity terms of `e.ugly.estimate.for.J.pre` and collapses every `lambda`-
and gradient-factor against the two good-event budgets

```
  sigmaBar_{n-2} lambda_{gamma,2}^{-1}(z+cube_n; a_{n-2}) 1_G <= C 3^{gamma(m-n)}
  sigmaBar_{n-2}^{-1} 3^{2n} ||grad(k_L - k_{n-2})||_{W^{1,infty}(z+cube_n)} 1_G
                                                  <= C 3^{s(m-n)/4}
```

(ABK26, in that order)

together with the running-diffusivity facts

```
  sigmaBar_k >= (1/2) cstar^{1/2} gamma^{-1/2} 3^{gamma k}   (every k <= m)
  sigmaBar_m^{-1} sigmaBar_{n-2} <= C
```

(the second is ABK26)

and one mean-zero Poincare step.  The result is the printed five-term display.

## The two hypotheses this module does NOT discharge

* `hsens` --- the four-term pre-estimate.  It is produced, at the Section 2.4
  anchor, by `Algsuperdiff.Section4.Provider.Annular.UglyPre`.
* `hH` --- the Poincare split `Hsq <= 2 Lnrm^2 + 2 (Cp * 3^{2m} Gm)^2`, i.e.
  the triangle inequality `k_L - (k_L-k_m)_{cube_m} - k_{n-2} = (k_m - k_{n-2})
  + (k_L - k_m - (k_L-k_m)_{cube_m})` followed by the mean-zero Poincare
  inequality on `cube_m`.  The manuscript cites "the Poincare inequality" with
  no label, so it enters here as a hypothesis, at the amplitude `Cp`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The five-term shape -/

/-- The shape of `e.ugly.estimate.for.J`, with the two displayed weights `w =
3^{s(m-n)}` and `w_gamma = 3^{(s+gamma)(m-n)}` left abstract. -/
def IsUglyJEstimate (Jval E2 sigDiff L2 gradN gradM cstar gam w wgam C : ℝ) : Prop :=
  Jval ≤ C * w * E2 + C * w * sigDiff + C * cstar⁻¹ * gam * w * L2 +
    C * cstar⁻¹ * gam * w * gradN + C * cstar⁻¹ * gam * wgam * gradM

/-! ## The running-diffusivity arithmetic

`kap` is the normalization `gamma * kap^2 = cstar`, i.e.
`kap = cstar^{1/2} gamma^{-1/2}`, kept squared so that no square root ever
appears. -/

/-- The inverse form of the `sigmaBar` lower bound
`sigmaBar_k >= (1/2) cstar^{1/2} gamma^{-1/2} 3^{gamma k}`. -/
theorem inv_le_two_mul_inv {kap P sig : ℝ} (hkap0 : 0 < kap) (hP0 : 0 < P)
    (hlow : 1 / 2 * (kap * P) ≤ sig) :
    sig⁻¹ ≤ 2 * (kap⁻¹ * P⁻¹) := by
  have hhalf : (0 : ℝ) < 1 / 2 * (kap * P) := by positivity
  have hstep : sig⁻¹ ≤ (1 / 2 * (kap * P))⁻¹ := by
    exact inv_anti₀ hhalf hlow
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- The inverse form of the *relaxed* `sigmaBar` lower bound `sigmaBar_k >= (1/4)
cstar^{1/2} gamma^{-1/2} 3^{gamma k}`, i.e. the shape the Section 3 state
delivers at the shifted index `k = n-2` once the exponent is moved to `3^{gamma
n}` (see the module docstring). -/
theorem inv_le_four_mul_inv {kap P sig : ℝ} (hkap0 : 0 < kap) (hP0 : 0 < P)
    (hlow : 1 / 4 * (kap * P) ≤ sig) :
    sig⁻¹ ≤ 4 * (kap⁻¹ * P⁻¹) := by
  have hquarter : (0 : ℝ) < 1 / 4 * (kap * P) := by positivity
  have hstep : sig⁻¹ ≤ (1 / 4 * (kap * P))⁻¹ := by
    exact inv_anti₀ hquarter hlow
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- The `kap`-normalization, squared: `(kap^{-1})^2 = cstar^{-1} gamma`. -/
theorem kapInv_sq {kap cstar gam : ℝ} (hkap0 : 0 < kap) (hcstar : 0 < cstar)
    (hkap : gam * kap ^ 2 = cstar) : (kap⁻¹) ^ 2 = cstar⁻¹ * gam := by
  have hk2 : (0 : ℝ) < kap ^ 2 := by positivity
  have hcs : cstar ≠ 0 := ne_of_gt hcstar
  field_simp
  linarith only [hkap]

/-- The `kap`-normalization forces `gamma > 0`. -/
theorem gamma_pos_of_kap {kap cstar gam : ℝ} (hkap0 : 0 < kap) (hcstar : 0 < cstar)
    (hkap : gam * kap ^ 2 = cstar) : 0 < gam := by
  have hk2 : (0 : ℝ) < kap ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  have : gam * kap ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hk2.le
  linarith only [this, hkap, hcstar]

/-! ## The four per-term patches -/

/-- **Patch 1**.  The first sensitivity term, whose growth factor `GF1` is
already collapsed against the weight `W`, becomes the displayed
`C 3^{s(m-n)} E^2` term. -/
theorem uglyPatch1 {Cs Cr A W GF1 E2 muInv : ℝ}
    (hCs : 0 ≤ Cs) (hE2 : 0 ≤ E2) (hmu0 : 0 ≤ muInv) (hmu : muInv ≤ Cr)
    (hGF10 : 0 ≤ GF1) (hGF1 : GF1 ≤ (1 + A) ^ 2 * W) :
    Cs * muInv * GF1 * E2 ≤ Cs * (1 + A) ^ 2 * Cr * W * E2 := by
  have hCr : 0 ≤ Cr := hmu0.trans hmu
  calc
    Cs * muInv * GF1 * E2 ≤ Cs * Cr * ((1 + A) ^ 2 * W) * E2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hmu hCs) hGF1 hGF10
          (mul_nonneg hCs hCr)) hE2
    _ = Cs * (1 + A) ^ 2 * Cr * W * E2 := by ring

/-- **Patch 3**.  The third sensitivity term `Cs sigmaBar_m^{-2} X^2` becomes the
displayed gradient-at-`n` term. -/
theorem uglyPatch3 {Cs cstar gam kap Pm Pn W X sigm : ℝ}
    (hCs : 0 ≤ Cs) (hcstar : 0 < cstar)
    (hkap0 : 0 < kap) (hkap : gam * kap ^ 2 = cstar)
    (hPm0 : 0 < Pm) (hPn0 : 0 < Pn) (hPnPm : Pn ≤ Pm) (hW1 : 1 ≤ W)
    (hsigm0 : 0 < sigm) (hsigmlow : 1 / 2 * (kap * Pm) ≤ sigm) :
    Cs * sigm⁻¹ ^ 2 * X ^ 2 ≤ 4 * Cs * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 := by
  have hgam0 : 0 < gam := gamma_pos_of_kap hkap0 hcstar hkap
  have hkinv : 0 < kap⁻¹ := inv_pos.2 hkap0
  have hPmInv : Pm⁻¹ ≤ Pn⁻¹ := inv_anti₀ hPn0 hPnPm
  have hstep : sigm⁻¹ ≤ 2 * (kap⁻¹ * Pn⁻¹) :=
    (inv_le_two_mul_inv hkap0 hPm0 hsigmlow).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPmInv hkinv.le)
        (by norm_num))
  have hsq : sigm⁻¹ ^ 2 ≤ 4 * ((kap⁻¹) ^ 2 * (Pn⁻¹) ^ 2) := by
    have hnn : (0 : ℝ) ≤ sigm⁻¹ := (inv_pos.2 hsigm0).le
    have := pow_le_pow_left₀ hnn hstep 2
    calc sigm⁻¹ ^ 2 ≤ (2 * (kap⁻¹ * Pn⁻¹)) ^ 2 := this
      _ = 4 * ((kap⁻¹) ^ 2 * (Pn⁻¹) ^ 2) := by ring
  rw [kapInv_sq hkap0 hcstar hkap] at hsq
  have hXsq : (0 : ℝ) ≤ X ^ 2 := sq_nonneg X
  have hcsg : (0 : ℝ) ≤ cstar⁻¹ * gam := by positivity
  calc
    Cs * sigm⁻¹ ^ 2 * X ^ 2
        ≤ Cs * (4 * (cstar⁻¹ * gam * (Pn⁻¹) ^ 2)) * X ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCs) hXsq
    _ = 4 * Cs * cstar⁻¹ * gam * 1 * (Pn⁻¹ * X) ^ 2 := by ring
    _ ≤ 4 * Cs * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 := by
        have hpos : (0 : ℝ) ≤ 4 * Cs * cstar⁻¹ * gam := by positivity
        have hsqnn : (0 : ℝ) ≤ (Pn⁻¹ * X) ^ 2 := sq_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW1 hpos) hsqnn

/-- **Patch 4**.  The fourth sensitivity term `Cs min{1, X lambda^{-1}}^2` also
becomes the displayed gradient-at-`n` term, by the `lambda`-budget
`sigmaBar_{n-2} lambda^{-1} <= Cl 3^{gamma(m-n)}`. -/
theorem uglyPatch4 {Cs Cl cstar gam kap Pn Q W X lamInv sign : ℝ}
    (hCs : 0 ≤ Cs) (hX : 0 ≤ X) (hlamInv : 0 ≤ lamInv) (hcstar : 0 < cstar)
    (hkap0 : 0 < kap) (hkap : gam * kap ^ 2 = cstar)
    (hPn0 : 0 < Pn) (hQ2W : Q ^ 2 ≤ W)
    (hsign0 : 0 < sign) (hsignlow : 1 / 4 * (kap * Pn) ≤ sign)
    (hlam : sign * lamInv ≤ Cl * Q) :
    Cs * min 1 (X * lamInv) ^ 2 ≤ 16 * Cs * Cl ^ 2 * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 := by
  have hgam0 : 0 < gam := gamma_pos_of_kap hkap0 hcstar hkap
  have hkinv : 0 < kap⁻¹ := inv_pos.2 hkap0
  have hsigninv : 0 < sign⁻¹ := inv_pos.2 hsign0
  have hsignstep : sign⁻¹ ≤ 4 * (kap⁻¹ * Pn⁻¹) :=
    inv_le_four_mul_inv hkap0 hPn0 hsignlow
  -- `lamInv <= Cl * Q * sign⁻¹`
  have hlam' : lamInv ≤ Cl * Q * sign⁻¹ := by
    have := mul_le_mul_of_nonneg_right hlam hsigninv.le
    calc lamInv = sign * lamInv * sign⁻¹ := by field_simp
      _ ≤ Cl * Q * sign⁻¹ := this
  have hClQ : 0 ≤ Cl * Q := le_trans (mul_nonneg hsign0.le hlamInv) hlam
  have hlam'' : lamInv ≤ Cl * Q * (4 * (kap⁻¹ * Pn⁻¹)) :=
    hlam'.trans (mul_le_mul_of_nonneg_left hsignstep hClQ)
  -- the `min` is dominated by the product
  have hmin0 : (0 : ℝ) ≤ min 1 (X * lamInv) :=
    le_min zero_le_one (mul_nonneg hX hlamInv)
  have hminle : min 1 (X * lamInv) ≤ X * (Cl * Q * (4 * (kap⁻¹ * Pn⁻¹))) :=
    (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hlam'' hX)
  have hsq := pow_le_pow_left₀ hmin0 hminle 2
  have hkap2 : (kap⁻¹) ^ 2 = cstar⁻¹ * gam := kapInv_sq hkap0 hcstar hkap
  have hexp : (X * (Cl * Q * (4 * (kap⁻¹ * Pn⁻¹)))) ^ 2 =
      16 * Cl ^ 2 * (cstar⁻¹ * gam) * Q ^ 2 * (Pn⁻¹ * X) ^ 2 := by
    rw [show (X * (Cl * Q * (4 * (kap⁻¹ * Pn⁻¹)))) ^ 2 =
        16 * Cl ^ 2 * ((kap⁻¹) ^ 2) * Q ^ 2 * (Pn⁻¹ * X) ^ 2 by ring, hkap2]
  rw [hexp] at hsq
  have hcoef : (0 : ℝ) ≤ 16 * Cs * Cl ^ 2 * cstar⁻¹ * gam := by positivity
  have hpn : (0 : ℝ) ≤ (Pn⁻¹ * X) ^ 2 := sq_nonneg _
  calc
    Cs * min 1 (X * lamInv) ^ 2
        ≤ Cs * (16 * Cl ^ 2 * (cstar⁻¹ * gam) * Q ^ 2 * (Pn⁻¹ * X) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hCs
    _ = 16 * Cs * Cl ^ 2 * cstar⁻¹ * gam * Q ^ 2 * (Pn⁻¹ * X) ^ 2 := by ring
    _ ≤ 16 * Cs * Cl ^ 2 * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ2W hcoef) hpn

/-- **Patch 2**.  The second sensitivity term splits three ways: the
`sigmaBar`-continuity term, the `L^2` term, and --- via the Poincare hypothesis
`hH` --- the displayed gradient-at-`m` term.

`Q * Pn = Pm` is the triadic identity `3^{gamma(m-n)} 3^{gamma n} = 3^{gamma m}`
and `W * Q = Wg` is `3^{s(m-n)} 3^{gamma(m-n)} = 3^{(s+gamma)(m-n)}`. -/
theorem uglyPatch2 {Cs Cl Cr Cp A cstar gam kap Pm Pn Q W Wg GF2 lamInv sigm sign
    Hsq Lnrm Y : ℝ}
    (hCs : 0 ≤ Cs) (hHsq : 0 ≤ Hsq)
    (hlamInv : 0 ≤ lamInv) (hcstar : 0 < cstar)
    (hkap0 : 0 < kap) (hkap : gam * kap ^ 2 = cstar)
    (hPm0 : 0 < Pm) (hPn0 : 0 < Pn) (hQ0 : 0 < Q) (hW0 : 0 ≤ W)
    (hPnPm : Pn ≤ Pm) (hQPn : Q * Pn = Pm) (hWg : W * Q = Wg)
    (hsigm0 : 0 < sigm) (hsign0 : 0 < sign)
    (hsigmlow : 1 / 2 * (kap * Pm) ≤ sigm) (hsignlow : 1 / 4 * (kap * Pn) ≤ sign)
    (hlam : sign * lamInv ≤ Cl * Q) (hratio : sigm⁻¹ * sign ≤ Cr)
    (hGF20 : 0 ≤ GF2) (hGF2 : Q * GF2 ≤ (1 + A) ^ 2 * W)
    (hH : Hsq ≤ 2 * Lnrm ^ 2 + 2 * (Cp * Y) ^ 2) :
    Cs * (sigm⁻¹ * sign ^ 2) * lamInv * GF2 * (sign⁻¹ ^ 2 * Hsq + (sigm * sign⁻¹ - 1) ^ 2)
      ≤ Cs * (1 + A) ^ 2 * Cr * Cl * W * (sigm * sign⁻¹ - 1) ^ 2
        + 16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2
        + 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 := by
  have hgam0 : 0 < gam := gamma_pos_of_kap hkap0 hcstar hkap
  have hkinv : 0 < kap⁻¹ := inv_pos.2 hkap0
  have hsigminv : 0 < sigm⁻¹ := inv_pos.2 hsigm0
  have hsigninv : 0 < sign⁻¹ := inv_pos.2 hsign0
  have hkap2 : (kap⁻¹) ^ 2 = cstar⁻¹ * gam := kapInv_sq hkap0 hcstar hkap
  have hCl0 : 0 ≤ Cl * Q := le_trans (mul_nonneg hsign0.le hlamInv) hlam
  have hCl : 0 ≤ Cl := by
    by_contra hcon
    push Not at hcon
    have hneg : Cl * Q < 0 := mul_neg_of_neg_of_pos hcon hQ0
    linarith only [hCl0, hneg]
  have hCr : 0 ≤ Cr := le_trans (mul_nonneg hsigminv.le hsign0.le) hratio
  -- split the bracket
  have hsplit :
      Cs * (sigm⁻¹ * sign ^ 2) * lamInv * GF2 *
          (sign⁻¹ ^ 2 * Hsq + (sigm * sign⁻¹ - 1) ^ 2) =
        Cs * (sigm⁻¹ * sign⁻¹) * (sign * lamInv) * GF2 * Hsq +
          Cs * (sigm⁻¹ * sign) * (sign * lamInv) * GF2 * (sigm * sign⁻¹ - 1) ^ 2 := by
    have hss : sign * sign⁻¹ = 1 := mul_inv_cancel₀ hsign0.ne'
    have hlhs : Cs * (sigm⁻¹ * sign ^ 2) * lamInv * GF2 *
          (sign⁻¹ ^ 2 * Hsq + (sigm * sign⁻¹ - 1) ^ 2) =
        (sign * sign⁻¹) ^ 2 * (Cs * sigm⁻¹ * lamInv * GF2 * Hsq) +
          Cs * (sigm⁻¹ * sign) * (sign * lamInv) * GF2 * (sigm * sign⁻¹ - 1) ^ 2 := by
      ring
    have hrhs : Cs * (sigm⁻¹ * sign⁻¹) * (sign * lamInv) * GF2 * Hsq =
        (sign * sign⁻¹) * (Cs * sigm⁻¹ * lamInv * GF2 * Hsq) := by
      ring
    rw [hlhs, hrhs, hss]
    ring
  have hlegH : Cs * (sigm⁻¹ * sign⁻¹) * (sign * lamInv) * GF2 * Hsq ≤
      16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 +
        16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 := by
    have hcsg : (0 : ℝ) ≤ Cs * (sigm⁻¹ * sign⁻¹) :=
      mul_nonneg hCs (mul_nonneg hsigminv.le hsigninv.le)
    have hstep1 : Cs * (sigm⁻¹ * sign⁻¹) * (sign * lamInv) * GF2 * Hsq ≤
        Cs * (sigm⁻¹ * sign⁻¹) * (Cl * Q) * GF2 * Hsq :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam hcsg) hGF20) hHsq
    have hQGF : Cs * (sigm⁻¹ * sign⁻¹) * (Cl * Q) * GF2 * Hsq =
        Cs * (sigm⁻¹ * sign⁻¹) * Cl * (Q * GF2) * Hsq := by ring
    have hstep2 : Cs * (sigm⁻¹ * sign⁻¹) * Cl * (Q * GF2) * Hsq ≤
        Cs * (sigm⁻¹ * sign⁻¹) * Cl * ((1 + A) ^ 2 * W) * Hsq :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hGF2 (mul_nonneg hcsg hCl)) hHsq
    -- the two `sigmaBar` lower bounds
    have hsm : sigm⁻¹ ≤ 2 * (kap⁻¹ * Pm⁻¹) :=
      inv_le_two_mul_inv hkap0 hPm0 hsigmlow
    have hsn : sign⁻¹ ≤ 4 * (kap⁻¹ * Pn⁻¹) :=
      inv_le_four_mul_inv hkap0 hPn0 hsignlow
    have hprod : sigm⁻¹ * sign⁻¹ ≤ 8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹) := by
      have : sigm⁻¹ * sign⁻¹ ≤ (2 * (kap⁻¹ * Pm⁻¹)) * (4 * (kap⁻¹ * Pn⁻¹)) :=
        mul_le_mul hsm hsn hsigninv.le (hsigminv.le.trans hsm)
      refine this.trans (le_of_eq ?_)
      rw [show (2 * (kap⁻¹ * Pm⁻¹)) * (4 * (kap⁻¹ * Pn⁻¹)) =
          8 * ((kap⁻¹) ^ 2) * (Pm⁻¹ * Pn⁻¹) by ring, hkap2]
    have hAW : (0 : ℝ) ≤ (1 + A) ^ 2 * W := by positivity
    have hstep3 : Cs * (sigm⁻¹ * sign⁻¹) * Cl * ((1 + A) ^ 2 * W) * Hsq ≤
        Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) * Hsq :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hCs) hCl) hAW) hHsq
    -- insert the Poincare split
    have hcoef : (0 : ℝ) ≤ Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl *
        ((1 + A) ^ 2 * W) := by positivity
    have hstep4 : Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) * Hsq ≤
        Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
          (2 * Lnrm ^ 2 + 2 * (Cp * Y) ^ 2) :=
      mul_le_mul_of_nonneg_left hH hcoef
    -- distribute and compare the two legs separately
    have hPmInv : Pm⁻¹ ≤ Pn⁻¹ := inv_anti₀ hPn0 hPnPm
    have hLleg : Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
          (2 * Lnrm ^ 2) ≤
        16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 := by
      have hbase : Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
          (2 * Lnrm ^ 2) =
          16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pm⁻¹ * Pn⁻¹ * Lnrm ^ 2) := by
        ring
      have htgt : 16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 =
          16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Pn⁻¹ * Lnrm ^ 2) := by
        ring
      rw [hbase, htgt]
      have hc : (0 : ℝ) ≤ 16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W := by positivity
      have hl : (0 : ℝ) ≤ Lnrm ^ 2 := sq_nonneg _
      have hpn : (0 : ℝ) < Pn⁻¹ := inv_pos.2 hPn0
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPmInv hpn.le) hl) hc
    have hYleg : Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
          (2 * (Cp * Y) ^ 2) ≤
        16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 := by
      have hPnQ : Pn⁻¹ = Q * Pm⁻¹ := by
        field_simp
        linarith only [hQPn]
      rw [hPnQ, ← hWg]
      ring_nf
      exact le_of_eq (by ring)
    calc
      Cs * (sigm⁻¹ * sign⁻¹) * (sign * lamInv) * GF2 * Hsq
          ≤ Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
              (2 * Lnrm ^ 2 + 2 * (Cp * Y) ^ 2) := by
            refine hstep1.trans ?_
            rw [hQGF]
            exact hstep2.trans (hstep3.trans hstep4)
      _ = Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
              (2 * Lnrm ^ 2) +
            Cs * (8 * (cstar⁻¹ * gam) * (Pm⁻¹ * Pn⁻¹)) * Cl * ((1 + A) ^ 2 * W) *
              (2 * (Cp * Y) ^ 2) := by ring
      _ ≤ 16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 +
            16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 :=
          add_le_add hLleg hYleg
  have hlegD : Cs * (sigm⁻¹ * sign) * (sign * lamInv) * GF2 * (sigm * sign⁻¹ - 1) ^ 2 ≤
      Cs * (1 + A) ^ 2 * Cr * Cl * W * (sigm * sign⁻¹ - 1) ^ 2 := by
    have hD : (0 : ℝ) ≤ (sigm * sign⁻¹ - 1) ^ 2 := sq_nonneg _
    have hstep1 : Cs * (sigm⁻¹ * sign) * (sign * lamInv) * GF2 * (sigm * sign⁻¹ - 1) ^ 2 ≤
        Cs * Cr * (Cl * Q) * GF2 * (sigm * sign⁻¹ - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hratio hCs) hlam
            (mul_nonneg hsign0.le hlamInv) (mul_nonneg hCs hCr)) hGF20) hD
    have hre : Cs * Cr * (Cl * Q) * GF2 * (sigm * sign⁻¹ - 1) ^ 2 =
        Cs * Cr * Cl * (Q * GF2) * (sigm * sign⁻¹ - 1) ^ 2 := by ring
    have hstep2 : Cs * Cr * Cl * (Q * GF2) * (sigm * sign⁻¹ - 1) ^ 2 ≤
        Cs * Cr * Cl * ((1 + A) ^ 2 * W) * (sigm * sign⁻¹ - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hGF2 (mul_nonneg (mul_nonneg hCs hCr) hCl)) hD
    calc
      Cs * (sigm⁻¹ * sign) * (sign * lamInv) * GF2 * (sigm * sign⁻¹ - 1) ^ 2
          ≤ Cs * Cr * Cl * ((1 + A) ^ 2 * W) * (sigm * sign⁻¹ - 1) ^ 2 := by
            refine hstep1.trans ?_
            rw [hre]; exact hstep2
      _ = Cs * (1 + A) ^ 2 * Cr * Cl * W * (sigm * sign⁻¹ - 1) ^ 2 := by ring
  rw [hsplit]
  linarith only [hlegH, hlegD]

/-! ## The Poincare split -/

/-- The `hH` slot of the assembly, produced from the triangle inequality and one
mean-zero Poincare bound.

`H` is `||k_L - (k_L - k_m)_{cube_m} - k_{n-2}||_{L-underline^2(z+cube_n)}`, `A`
is `||k_m - k_{n-2}||_{L-underline^2(z+cube_n)}`, and `B` is the mean-zero
fluctuation `||k_L - k_m - (k_L - k_m)_{cube_m}||_{L-underline^2(z+cube_n)}`,
whose Poincare bound is `hpoin` (there `Y = 3^{2m} Gm`).

The Poincare input itself is proved upstream, not owed here: CoarseGraining's
`Homogenization.cubeBesovOscillation_two_le_cubeScaleFactor_mul_normalizedW1pSeminorm`
is exactly `||u - (u)_Q||_{L-underline^2(Q)} <= C(d) 3^{Q.scale} ||grad
u||_{L-underline^2(Q)}` on a triadic cube, in the volume-normalized convention
this slice uses. -/
theorem poincareSplit {H A B Cp Y : ℝ} (hH0 : 0 ≤ H) (hB0 : 0 ≤ B)
    (htri : H ≤ A + B) (hpoin : B ≤ Cp * Y) :
    H ^ 2 ≤ 2 * A ^ 2 + 2 * (Cp * Y) ^ 2 := by
  have h1 : H ^ 2 ≤ (A + B) ^ 2 := pow_le_pow_left₀ hH0 htri 2
  have h2 : B ^ 2 ≤ (Cp * Y) ^ 2 := pow_le_pow_left₀ hB0 hpoin 2
  linarith only [h1, h2, sq_nonneg (A - B)]

/-! ## The four-term to five-term assembly -/

/-- **`e.ugly.estimate.for.J`, abstract-weight form**.

The four sensitivity terms `hsens` of `e.ugly.estimate.for.J.pre`, collapsed
against the two good-event budgets (`hlam`, and the growth-factor bounds
`hG/`hG which are where the `3^{s(m-n)/4}` gradient budget has already been
absorbed), the two `sigmaBar` lower bounds and the `sigmaBar` ratio, plus the
Poincare split `hH`, give the printed five-term display at the explicit
constant `C`. -/
theorem uglyJEstimate_core
    {Cs Cl Cr Cp A C cstar gam kap Pm Pn Q W Wg GF1 GF2 lamInv sigm sign
      Jval E2 Hsq Lnrm X Y : ℝ}
    (hCs : 0 ≤ Cs) (hE2 : 0 ≤ E2)
    (hX : 0 ≤ X) (hHsq : 0 ≤ Hsq) (hlamInv : 0 ≤ lamInv)
    (hcstar : 0 < cstar) (hkap0 : 0 < kap) (hkap : gam * kap ^ 2 = cstar)
    (hPm0 : 0 < Pm) (hPn0 : 0 < Pn) (hQ0 : 0 < Q) (hW0 : 0 ≤ W)
    (hPnPm : Pn ≤ Pm) (hW1 : 1 ≤ W) (hQ2W : Q ^ 2 ≤ W) (hQPn : Q * Pn = Pm)
    (hWg : W * Q = Wg)
    (hsigm0 : 0 < sigm) (hsign0 : 0 < sign)
    (hsigmlow : 1 / 2 * (kap * Pm) ≤ sigm) (hsignlow : 1 / 4 * (kap * Pn) ≤ sign)
    (hlam : sign * lamInv ≤ Cl * Q) (hratio : sigm⁻¹ * sign ≤ Cr)
    (hGF10 : 0 ≤ GF1) (hGF1 : GF1 ≤ (1 + A) ^ 2 * W)
    (hGF20 : 0 ≤ GF2) (hGF2 : Q * GF2 ≤ (1 + A) ^ 2 * W)
    (hH : Hsq ≤ 2 * Lnrm ^ 2 + 2 * (Cp * Y) ^ 2)
    (hsens : Jval ≤ Cs * (sigm⁻¹ * sign) * GF1 * E2
      + Cs * (sigm⁻¹ * sign ^ 2) * lamInv * GF2
          * (sign⁻¹ ^ 2 * Hsq + (sigm * sign⁻¹ - 1) ^ 2)
      + Cs * sigm⁻¹ ^ 2 * X ^ 2
      + Cs * min 1 (X * lamInv) ^ 2)
    (hC : Cs * (1 + A) ^ 2 * Cr * (1 + Cl) + 16 * Cs * (1 + A) ^ 2 * Cl * (1 + Cp ^ 2)
      + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C) :
    IsUglyJEstimate Jval E2 ((sigm * sign⁻¹ - 1) ^ 2) ((Pn⁻¹ * Lnrm) ^ 2)
      ((Pn⁻¹ * X) ^ 2) ((Pm⁻¹ * Y) ^ 2) cstar gam W Wg C := by
  have hgam0 : 0 < gam := gamma_pos_of_kap hkap0 hcstar hkap
  have hsigminv : 0 < sigm⁻¹ := inv_pos.2 hsigm0
  have hmu0 : (0 : ℝ) ≤ sigm⁻¹ * sign := mul_nonneg hsigminv.le hsign0.le
  have hCr : 0 ≤ Cr := hmu0.trans hratio
  have hCl0 : 0 ≤ Cl * Q := le_trans (mul_nonneg hsign0.le hlamInv) hlam
  have hCl : 0 ≤ Cl := by
    by_contra hcon
    push Not at hcon
    have hneg : Cl * Q < 0 := mul_neg_of_neg_of_pos hcon hQ0
    linarith only [hCl0, hneg]
  -- the four patches
  have p1 := uglyPatch1 (Cr := Cr) (A := A) (W := W) hCs hE2 hmu0 hratio hGF10 hGF1
  have p2 := uglyPatch2 (Cl := Cl) (Cr := Cr) (Cp := Cp) (A := A) (Wg := Wg)
    (Lnrm := Lnrm) (Y := Y) hCs hHsq hlamInv hcstar hkap0 hkap hPm0 hPn0 hQ0 hW0
    hPnPm hQPn hWg hsigm0 hsign0 hsigmlow hsignlow hlam hratio hGF20 hGF2 hH
  have p3 := uglyPatch3 (X := X) hCs hcstar hkap0 hkap hPm0 hPn0 hPnPm hW1 hsigm0 hsigmlow
  have p4 := uglyPatch4 (Cl := Cl) (W := W) (X := X) hCs hX hlamInv hcstar hkap0 hkap
    hPn0 hQ2W hsign0 hsignlow hlam
  -- the five coefficient comparisons
  have hA2 : (0 : ℝ) ≤ (1 + A) ^ 2 := sq_nonneg _
  have n1 : (0 : ℝ) ≤ Cs * (1 + A) ^ 2 * Cr := mul_nonneg (mul_nonneg hCs hA2) hCr
  have n2 : (0 : ℝ) ≤ Cs * (1 + A) ^ 2 * Cr * Cl := mul_nonneg n1 hCl
  have h16 : (0 : ℝ) ≤ 16 * Cs := by linarith only [hCs]
  have n3 : (0 : ℝ) ≤ 16 * Cs * (1 + A) ^ 2 * Cl := mul_nonneg (mul_nonneg h16 hA2) hCl
  have n4 : (0 : ℝ) ≤ 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 := mul_nonneg n3 (sq_nonneg Cp)
  have n5 : (0 : ℝ) ≤ 4 * Cs := by linarith only [hCs]
  have n6 : (0 : ℝ) ≤ 16 * Cs * Cl ^ 2 := mul_nonneg h16 (sq_nonneg Cl)
  have hsum : Cs * (1 + A) ^ 2 * Cr + Cs * (1 + A) ^ 2 * Cr * Cl +
      16 * Cs * (1 + A) ^ 2 * Cl + 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 +
      4 * Cs + 16 * Cs * Cl ^ 2 ≤ C :=
    (le_of_eq (by ring)).trans hC
  have hc1 : Cs * (1 + A) ^ 2 * Cr ≤ C := by linarith only [hsum, n2, n3, n4, n5, n6]
  have hc2 : Cs * (1 + A) ^ 2 * Cr * Cl ≤ C := by linarith only [hsum, n1, n3, n4, n5, n6]
  have hc3 : 16 * Cs * (1 + A) ^ 2 * Cl ≤ C := by linarith only [hsum, n1, n2, n4, n5, n6]
  have hc4 : 4 * Cs + 16 * Cs * Cl ^ 2 ≤ C := by linarith only [hsum, n1, n2, n3, n4]
  have hc5 : 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 ≤ C := by
    linarith only [hsum, n1, n2, n3, n5, n6]
  -- the five atoms are nonnegative
  have hWg0 : 0 ≤ Wg := by rw [← hWg]; positivity
  have hAE : (0 : ℝ) ≤ W * E2 := mul_nonneg hW0 hE2
  have hAD : (0 : ℝ) ≤ W * (sigm * sign⁻¹ - 1) ^ 2 := mul_nonneg hW0 (sq_nonneg _)
  have hAL : (0 : ℝ) ≤ cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 := by positivity
  have hAG : (0 : ℝ) ≤ cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 := by positivity
  have hAM : (0 : ℝ) ≤ cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 := by positivity
  have bE : Cs * (1 + A) ^ 2 * Cr * W * E2 ≤ C * W * E2 := by
    have hstep := mul_le_mul_of_nonneg_right hc1 hAE
    calc Cs * (1 + A) ^ 2 * Cr * W * E2 = Cs * (1 + A) ^ 2 * Cr * (W * E2) := by ring
      _ ≤ C * (W * E2) := hstep
      _ = C * W * E2 := by ring
  have bD : Cs * (1 + A) ^ 2 * Cr * Cl * W * (sigm * sign⁻¹ - 1) ^ 2 ≤
      C * W * (sigm * sign⁻¹ - 1) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_right hc2 hAD
    calc Cs * (1 + A) ^ 2 * Cr * Cl * W * (sigm * sign⁻¹ - 1) ^ 2
        = Cs * (1 + A) ^ 2 * Cr * Cl * (W * (sigm * sign⁻¹ - 1) ^ 2) := by ring
      _ ≤ C * (W * (sigm * sign⁻¹ - 1) ^ 2) := hstep
      _ = C * W * (sigm * sign⁻¹ - 1) ^ 2 := by ring
  have bL : 16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 ≤
      C * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_right hc3 hAL
    calc 16 * Cs * (1 + A) ^ 2 * Cl * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2
        = 16 * Cs * (1 + A) ^ 2 * Cl * (cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2) := by ring
      _ ≤ C * (cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2) := hstep
      _ = C * cstar⁻¹ * gam * W * (Pn⁻¹ * Lnrm) ^ 2 := by ring
  have bG : 4 * Cs * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 +
      16 * Cs * Cl ^ 2 * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 ≤
      C * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_right hc4 hAG
    calc 4 * Cs * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 +
          16 * Cs * Cl ^ 2 * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2
        = (4 * Cs + 16 * Cs * Cl ^ 2) * (cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2) := by ring
      _ ≤ C * (cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2) := hstep
      _ = C * cstar⁻¹ * gam * W * (Pn⁻¹ * X) ^ 2 := by ring
  have bM : 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 ≤
      C * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 := by
    have hstep := mul_le_mul_of_nonneg_right hc5 hAM
    calc 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2
        = 16 * Cs * (1 + A) ^ 2 * Cl * Cp ^ 2 *
            (cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2) := by ring
      _ ≤ C * (cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2) := hstep
      _ = C * cstar⁻¹ * gam * Wg * (Pm⁻¹ * Y) ^ 2 := by ring
  unfold IsUglyJEstimate
  linarith only [hsens, p1, p2, p3, p4, bE, bD, bL, bG, bM]


/-! ## The triadic weights: the growth-factor collapses -/

private theorem three_rpow_pos (x : ℝ) : (0 : ℝ) < (3 : ℝ) ^ x :=
  Real.rpow_pos_of_pos (by norm_num) x

private theorem three_rpow_mono {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private theorem one_le_three_rpow {x : ℝ} (hx : 0 ≤ x) : (1 : ℝ) ≤ (3 : ℝ) ^ x := by
  calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 3).symm
    _ ≤ (3 : ℝ) ^ x := three_rpow_mono hx

private theorem three_rpow_add (x y : ℝ) :
    (3 : ℝ) ^ x * (3 : ℝ) ^ y = (3 : ℝ) ^ (x + y) :=
  (Real.rpow_add (by norm_num) x y).symm

/-- With the `lambda`- and gradient-budgets already inserted, the first sensitivity
growth factor is dominated by `(1 + A)^2 3^{s(m-n)}`.  At the gapped gauge the
exponent is `2s/(1 - 4 gamma)` and the arithmetic needs `s/2 + 6 gamma <= 1`,
which is what `s <= 1/2` and `gamma <= 1/8` deliver (with equality at the
corner). -/
theorem growthFactor_collapse {A s gam q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hs0 : 0 < s) (hs : s ≤ 1 / 2) (hgam0 : 0 ≤ gam) (hgam : gam ≤ 1 / 8) :
    (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam))
      ≤ (1 + A) ^ 2 * (3 : ℝ) ^ (s * q) := by
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgam]
  have hu0 : (0 : ℝ) ≤ (s / 4 + gam) * q :=
    mul_nonneg (by linarith only [hs0, hgam0]) hq
  have hp0 : (0 : ℝ) ≤ 2 * s / (1 - 4 * gam) :=
    div_nonneg (by linarith only [hs0]) hden.le
  have hp2 : 2 * s / (1 - 4 * gam) ≤ 2 := by
    rw [div_le_iff₀ hden]; linarith only [hs, hgam]
  have ht1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((s / 4 + gam) * q) := one_le_three_rpow hu0
  have hA1 : (1 : ℝ) ≤ 1 + A := by linarith only [hA]
  have hbase : 1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q) ≤
      (1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q) := by
    have hAt : A * 1 ≤ A * (3 : ℝ) ^ ((s / 4 + gam) * q) :=
      mul_le_mul_of_nonneg_left ht1 hA
    have hexp : (1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q) =
        (3 : ℝ) ^ ((s / 4 + gam) * q) + A * (3 : ℝ) ^ ((s / 4 + gam) * q) := by ring
    rw [hexp]
    linarith only [ht1, hAt]
  have hbase0 : (0 : ℝ) ≤ 1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q) := by
    have := (three_rpow_pos ((s / 4 + gam) * q)).le
    have : (0 : ℝ) ≤ A * (3 : ℝ) ^ ((s / 4 + gam) * q) := mul_nonneg hA this
    linarith only [this]
  have step1 : (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam)) ≤
      ((1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam)) :=
    Real.rpow_le_rpow hbase0 hbase hp0
  have hsplit : ((1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam)) =
      (1 + A) ^ (2 * s / (1 - 4 * gam)) *
        ((3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam)) :=
    Real.mul_rpow (by linarith only [hA]) (three_rpow_pos _).le
  have hpow : ((3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam)) =
      (3 : ℝ) ^ ((s / 4 + gam) * q * (2 * s / (1 - 4 * gam))) :=
    (Real.rpow_mul (by norm_num) _ _).symm
  have hfac : (s / 4 + gam) * (2 * s / (1 - 4 * gam)) ≤ s := by
    have hrw : (s / 4 + gam) * (2 * s / (1 - 4 * gam)) =
        ((s / 4 + gam) * (2 * s)) / (1 - 4 * gam) := by ring
    rw [hrw, div_le_iff₀ hden]
    have h1 : s * s ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left hs hs0.le
    have h2 : s * gam ≤ s * (1 / 8) := mul_le_mul_of_nonneg_left hgam hs0.le
    linarith only [h1, h2]
  have hexp2 : (s / 4 + gam) * q * (2 * s / (1 - 4 * gam)) ≤ s * q := by
    have hmul := mul_le_mul_of_nonneg_left hfac hq
    calc (s / 4 + gam) * q * (2 * s / (1 - 4 * gam))
        = q * ((s / 4 + gam) * (2 * s / (1 - 4 * gam))) := by ring
      _ ≤ q * s := hmul
      _ = s * q := by ring
  have step3 : (1 + A) ^ (2 * s / (1 - 4 * gam)) ≤ (1 + A) ^ (2 : ℕ) := by
    have hmono : (1 + A) ^ (2 * s / (1 - 4 * gam)) ≤ (1 + A) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hA1 hp2
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hmono
  have hgf : (0 : ℝ) ≤ (1 + A) ^ (2 * s / (1 - 4 * gam)) :=
    Real.rpow_nonneg (by linarith only [hA]) _
  calc (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (2 * s / (1 - 4 * gam))
      ≤ (1 + A) ^ (2 * s / (1 - 4 * gam)) *
          (3 : ℝ) ^ ((s / 4 + gam) * q * (2 * s / (1 - 4 * gam))) := by
        rw [← hpow, ← hsplit]; exact step1
    _ ≤ (1 + A) ^ (2 : ℕ) * (3 : ℝ) ^ (s * q) := by
        exact mul_le_mul step3 (three_rpow_mono hexp2) (three_rpow_pos _).le
          (pow_nonneg (by linarith only [hA]) 2)

/-- **Growth-factor collapse, second exponent**.  At the gapped gauge the exponent
is `4 gamma/(1 - 4 gamma)` and the arithmetic needs `gamma + 5 s gamma <= s`,
which is what `8 gamma <= s <= 1/2` delivers with room to spare (the left side
is at most `(7/16) s`). -/
theorem growthFactor_collapse_sigma {A s gam q : ℝ} (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hs0 : 0 < s) (hs : s ≤ 1 / 2) (hgam0 : 0 ≤ gam) (hgams : 8 * gam ≤ s) :
    (3 : ℝ) ^ (gam * q) *
        (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam))
      ≤ (1 + A) ^ 2 * (3 : ℝ) ^ (s * q) := by
  have hgamsmall : gam ≤ 1 / 16 := by linarith only [hgams, hs]
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgamsmall]
  have hu0 : (0 : ℝ) ≤ (s / 4 + gam) * q :=
    mul_nonneg (by linarith only [hs0, hgam0]) hq
  have hp0 : (0 : ℝ) ≤ 4 * gam / (1 - 4 * gam) :=
    div_nonneg (by linarith only [hgam0]) hden.le
  have hp2 : 4 * gam / (1 - 4 * gam) ≤ 2 := by
    rw [div_le_iff₀ hden]; linarith only [hgamsmall]
  have ht1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((s / 4 + gam) * q) := one_le_three_rpow hu0
  have hA1 : (1 : ℝ) ≤ 1 + A := by linarith only [hA]
  have hbase : 1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q) ≤
      (1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q) := by
    have hAt : A * 1 ≤ A * (3 : ℝ) ^ ((s / 4 + gam) * q) :=
      mul_le_mul_of_nonneg_left ht1 hA
    have hexp : (1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q) =
        (3 : ℝ) ^ ((s / 4 + gam) * q) + A * (3 : ℝ) ^ ((s / 4 + gam) * q) := by ring
    rw [hexp]
    linarith only [ht1, hAt]
  have hbase0 : (0 : ℝ) ≤ 1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q) := by
    have h1 : (0 : ℝ) ≤ A * (3 : ℝ) ^ ((s / 4 + gam) * q) :=
      mul_nonneg hA (three_rpow_pos _).le
    linarith only [h1]
  have step1 : (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam)) ≤
      ((1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam)) :=
    Real.rpow_le_rpow hbase0 hbase hp0
  have hsplit : ((1 + A) * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam)) =
      (1 + A) ^ (4 * gam / (1 - 4 * gam)) *
        ((3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam)) :=
    Real.mul_rpow (by linarith only [hA]) (three_rpow_pos _).le
  have hpow : ((3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam)) =
      (3 : ℝ) ^ ((s / 4 + gam) * q * (4 * gam / (1 - 4 * gam))) :=
    (Real.rpow_mul (by norm_num) _ _).symm
  have hfac : gam + (s / 4 + gam) * (4 * gam / (1 - 4 * gam)) ≤ s := by
    have h1 : s * gam ≤ s * (s / 8) :=
      mul_le_mul_of_nonneg_left (by linarith only [hgams]) hs0.le
    have h2 : s * s ≤ s * (1 / 2) := mul_le_mul_of_nonneg_left hs hs0.le
    have hkey : (s / 4 + gam) * (4 * gam / (1 - 4 * gam)) ≤ s - gam := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      linarith only [h1, h2, hs0, hgam0, hgams]
    linarith only [hkey]
  have hexp2 : gam * q + (s / 4 + gam) * q * (4 * gam / (1 - 4 * gam)) ≤ s * q := by
    have hmul := mul_le_mul_of_nonneg_left hfac hq
    calc gam * q + (s / 4 + gam) * q * (4 * gam / (1 - 4 * gam))
        = q * (gam + (s / 4 + gam) * (4 * gam / (1 - 4 * gam))) := by ring
      _ ≤ q * s := hmul
      _ = s * q := by ring
  have step3 : (1 + A) ^ (4 * gam / (1 - 4 * gam)) ≤ (1 + A) ^ (2 : ℕ) := by
    have hmono : (1 + A) ^ (4 * gam / (1 - 4 * gam)) ≤ (1 + A) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hA1 hp2
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hmono
  have hgf : (0 : ℝ) ≤ (1 + A) ^ (4 * gam / (1 - 4 * gam)) :=
    Real.rpow_nonneg (by linarith only [hA]) _
  calc (3 : ℝ) ^ (gam * q) *
        (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam))
      ≤ (3 : ℝ) ^ (gam * q) *
          ((1 + A) ^ (4 * gam / (1 - 4 * gam)) *
            (3 : ℝ) ^ ((s / 4 + gam) * q * (4 * gam / (1 - 4 * gam)))) := by
        have hstep : (1 + A * (3 : ℝ) ^ ((s / 4 + gam) * q)) ^ (4 * gam / (1 - 4 * gam)) ≤
            (1 + A) ^ (4 * gam / (1 - 4 * gam)) *
              (3 : ℝ) ^ ((s / 4 + gam) * q * (4 * gam / (1 - 4 * gam))) := by
          rw [← hpow, ← hsplit]; exact step1
        exact mul_le_mul_of_nonneg_left hstep (three_rpow_pos _).le
    _ = (1 + A) ^ (4 * gam / (1 - 4 * gam)) *
          (3 : ℝ) ^ (gam * q + (s / 4 + gam) * q * (4 * gam / (1 - 4 * gam))) := by
        rw [← three_rpow_add]; ring
    _ ≤ (1 + A) ^ (2 : ℕ) * (3 : ℝ) ^ (s * q) := by
        exact mul_le_mul step3 (three_rpow_mono hexp2) (three_rpow_pos _).le
          (pow_nonneg (by linarith only [hA]) 2)

/-! ## `e.ugly.estimate.for.J` at the manuscript's triadic weights -/

/-- **`e.ugly.estimate.for.J`**, at the printed weights `w = 3^{s(m-n)}` and
`w_gamma = 3^{(s+gamma)(m-n)}`.

`hlam` is the lambda-budget, `hshell` the `G_1` gradient budget, `hratio` the
`sigmaBar_m^{-1} sigmaBar_{n-2} <= C`, `hH` the Poincare split, and `hsens` the
four-term pre-estimate.

The `s`-window here is the manuscript's `[8 gamma, 1/2]`.  A consumer that
feeds `hsens` from the Section 2.4 anchor (see `UglyPre`) must further restrict
to `s <= 1/4`; that residual is noted there. -/
theorem uglyJEstimate_of_sensitivity
    {s gam cstar kap Cs Cl Cr Cp Ash C mm nn q lamInv sigm sign
      Jval E2 Hsq Lnrm Gn Gm : ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) (hsgam : 8 * gam ≤ s)
    (hnm : nn ≤ mm) (hq : q = mm - nn)
    (hCs : 0 ≤ Cs) (hAsh : 0 ≤ Ash) (hE2 : 0 ≤ E2) (hGn : 0 ≤ Gn)
    (hHsq : 0 ≤ Hsq) (hlamInv : 0 ≤ lamInv)
    (hcstar : 0 < cstar) (hkap0 : 0 < kap) (hkap : gam * kap ^ 2 = cstar)
    (hsigm0 : 0 < sigm) (hsign0 : 0 < sign)
    (hsigmlow : 1 / 2 * (kap * (3 : ℝ) ^ (gam * mm)) ≤ sigm)
    (hsignlow : 1 / 4 * (kap * (3 : ℝ) ^ (gam * nn)) ≤ sign)
    (hlam : sign * lamInv ≤ Cl * (3 : ℝ) ^ (gam * q))
    (hshell : sign⁻¹ * ((3 : ℝ) ^ (2 * nn) * Gn) ≤ Ash * (3 : ℝ) ^ (s / 4 * q))
    (hratio : sigm⁻¹ * sign ≤ Cr)
    (hH : Hsq ≤ 2 * Lnrm ^ 2 + 2 * (Cp * ((3 : ℝ) ^ (2 * mm) * Gm)) ^ 2)
    (hsens : Jval ≤
      Cs * (sigm⁻¹ * sign) *
          (1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ (2 * s / (1 - 4 * gam)) * E2
        + Cs * (sigm⁻¹ * sign ^ 2) * lamInv *
            (1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ (4 * gam / (1 - 4 * gam)) *
            (sign⁻¹ ^ 2 * Hsq + (sigm * sign⁻¹ - 1) ^ 2)
        + Cs * sigm⁻¹ ^ 2 * ((3 : ℝ) ^ (2 * nn) * Gn) ^ 2
        + Cs * min 1 ((3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ 2)
    (hC : Cs * (1 + Ash * Cl) ^ 2 * Cr * (1 + Cl)
      + 16 * Cs * (1 + Ash * Cl) ^ 2 * Cl * (1 + Cp ^ 2)
      + 4 * Cs * (1 + 4 * Cl ^ 2) ≤ C) :
    IsUglyJEstimate Jval E2 ((sigm * sign⁻¹ - 1) ^ 2)
      (((3 : ℝ) ^ (-(gam * nn)) * Lnrm) ^ 2)
      (((3 : ℝ) ^ ((2 - gam) * nn) * Gn) ^ 2)
      (((3 : ℝ) ^ ((2 - gam) * mm) * Gm) ^ 2)
      cstar gam ((3 : ℝ) ^ (s * q)) ((3 : ℝ) ^ ((s + gam) * q)) C := by
  have hgam0 : 0 < gam := gamma_pos_of_kap hkap0 hcstar hkap
  have hq0 : 0 ≤ q := by rw [hq]; linarith only [hnm]
  have hgam18 : gam ≤ 1 / 8 := by linarith only [hsgam, hs1]
  have hX0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * nn) * Gn :=
    mul_nonneg (three_rpow_pos _).le hGn
  have hClQ : (0 : ℝ) ≤ Cl * (3 : ℝ) ^ (gam * q) :=
    le_trans (mul_nonneg hsign0.le hlamInv) hlam
  have hCl : 0 ≤ Cl := by
    by_contra hcon
    push Not at hcon
    have hneg : Cl * (3 : ℝ) ^ (gam * q) < 0 :=
      mul_neg_of_neg_of_pos hcon (three_rpow_pos _)
    linarith only [hClQ, hneg]
  have hA0 : (0 : ℝ) ≤ Ash * Cl := mul_nonneg hAsh hCl
  -- the two budgets multiply into the growth-factor base
  have hshell0 : (0 : ℝ) ≤ sign⁻¹ * ((3 : ℝ) ^ (2 * nn) * Gn) :=
    mul_nonneg (inv_pos.2 hsign0).le hX0
  have hbudget : (3 : ℝ) ^ (2 * nn) * Gn * lamInv ≤
      Ash * Cl * (3 : ℝ) ^ ((s / 4 + gam) * q) := by
    have hfactor : (3 : ℝ) ^ (2 * nn) * Gn * lamInv =
        (sign⁻¹ * ((3 : ℝ) ^ (2 * nn) * Gn)) * (sign * lamInv) := by
      field_simp
    have hmul : (sign⁻¹ * ((3 : ℝ) ^ (2 * nn) * Gn)) * (sign * lamInv) ≤
        (Ash * (3 : ℝ) ^ (s / 4 * q)) * (Cl * (3 : ℝ) ^ (gam * q)) :=
      mul_le_mul hshell hlam (mul_nonneg hsign0.le hlamInv)
        (mul_nonneg hAsh (three_rpow_pos _).le)
    have hcollect : (Ash * (3 : ℝ) ^ (s / 4 * q)) * (Cl * (3 : ℝ) ^ (gam * q)) =
        Ash * Cl * (3 : ℝ) ^ ((s / 4 + gam) * q) := by
      rw [show Ash * (3 : ℝ) ^ (s / 4 * q) * (Cl * (3 : ℝ) ^ (gam * q)) =
          Ash * Cl * ((3 : ℝ) ^ (s / 4 * q) * (3 : ℝ) ^ (gam * q)) by ring,
        three_rpow_add]
      congr 2
      ring
    rw [hfactor]
    exact hmul.trans (le_of_eq hcollect)
  have hbase0 : (0 : ℝ) ≤ 1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv := by
    have := mul_nonneg hX0 hlamInv
    linarith only [this]
  have hbaseA : 1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv ≤
      1 + Ash * Cl * (3 : ℝ) ^ ((s / 4 + gam) * q) := by linarith only [hbudget]
  have hden : (0 : ℝ) < 1 - 4 * gam := by linarith only [hgam18]
  -- the two collapsed growth factors
  have hGF1 : (1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ (2 * s / (1 - 4 * gam)) ≤
      (1 + Ash * Cl) ^ 2 * (3 : ℝ) ^ (s * q) := by
    refine le_trans (Real.rpow_le_rpow hbase0 hbaseA
      (div_nonneg (by linarith only [hs0]) hden.le)) ?_
    exact growthFactor_collapse hA0 hq0 hs0 hs1 hgam0.le hgam18
  have hGF2 : (3 : ℝ) ^ (gam * q) *
      (1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ (4 * gam / (1 - 4 * gam)) ≤
      (1 + Ash * Cl) ^ 2 * (3 : ℝ) ^ (s * q) := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase0 hbaseA
      (div_nonneg (by linarith only [hgam0]) hden.le)) (three_rpow_pos _).le) ?_
    exact growthFactor_collapse_sigma hA0 hq0 hs0 hs1 hgam0.le hsgam
  -- the triadic weight identities
  have hQPn : (3 : ℝ) ^ (gam * q) * (3 : ℝ) ^ (gam * nn) = (3 : ℝ) ^ (gam * mm) := by
    rw [three_rpow_add]
    congr 1
    rw [hq]; ring
  have hWg : (3 : ℝ) ^ (s * q) * (3 : ℝ) ^ (gam * q) = (3 : ℝ) ^ ((s + gam) * q) := by
    rw [three_rpow_add]
    congr 1
    ring
  have hQ2W : ((3 : ℝ) ^ (gam * q)) ^ 2 ≤ (3 : ℝ) ^ (s * q) := by
    have hsq : ((3 : ℝ) ^ (gam * q)) ^ 2 = (3 : ℝ) ^ (2 * (gam * q)) := by
      rw [show ((3 : ℝ) ^ (gam * q)) ^ 2 =
          (3 : ℝ) ^ (gam * q) * (3 : ℝ) ^ (gam * q) by ring, three_rpow_add]
      congr 1
      ring
    rw [hsq]
    refine three_rpow_mono ?_
    have h2g : 2 * gam ≤ s := by linarith only [hsgam, hgam0]
    have := mul_le_mul_of_nonneg_right h2g hq0
    calc 2 * (gam * q) = 2 * gam * q := by ring
      _ ≤ s * q := this
  have hPnPm : (3 : ℝ) ^ (gam * nn) ≤ (3 : ℝ) ^ (gam * mm) :=
    three_rpow_mono (mul_le_mul_of_nonneg_left hnm hgam0.le)
  have hW1 : (1 : ℝ) ≤ (3 : ℝ) ^ (s * q) :=
    one_le_three_rpow (mul_nonneg hs0.le hq0)
  -- rewrite the goal into the abstract-weight form
  have e1 : (3 : ℝ) ^ (-(gam * nn)) * Lnrm = ((3 : ℝ) ^ (gam * nn))⁻¹ * Lnrm := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have ebase : ∀ x y : ℝ, ((3 : ℝ) ^ (gam * x))⁻¹ * ((3 : ℝ) ^ (2 * x) * y) =
      (3 : ℝ) ^ ((2 - gam) * x) * y := by
    intro x y
    rw [← mul_assoc, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), three_rpow_add]
    congr 2
    ring
  have e2 : (3 : ℝ) ^ ((2 - gam) * nn) * Gn =
      ((3 : ℝ) ^ (gam * nn))⁻¹ * ((3 : ℝ) ^ (2 * nn) * Gn) := (ebase nn Gn).symm
  have e3 : (3 : ℝ) ^ ((2 - gam) * mm) * Gm =
      ((3 : ℝ) ^ (gam * mm))⁻¹ * ((3 : ℝ) ^ (2 * mm) * Gm) := (ebase mm Gm).symm
  rw [e1, e2, e3]
  exact uglyJEstimate_core (Cs := Cs) (Cl := Cl) (Cr := Cr) (Cp := Cp)
    (A := Ash * Cl) (C := C) (cstar := cstar) (gam := gam) (kap := kap)
    (Pm := (3 : ℝ) ^ (gam * mm)) (Pn := (3 : ℝ) ^ (gam * nn))
    (Q := (3 : ℝ) ^ (gam * q)) (W := (3 : ℝ) ^ (s * q)) (Wg := (3 : ℝ) ^ ((s + gam) * q))
    (GF1 := (1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ (2 * s / (1 - 4 * gam)))
    (GF2 := (1 + (3 : ℝ) ^ (2 * nn) * Gn * lamInv) ^ (4 * gam / (1 - 4 * gam)))
    (lamInv := lamInv) (sigm := sigm) (sign := sign) (Jval := Jval) (E2 := E2)
    (Hsq := Hsq) (Lnrm := Lnrm) (X := (3 : ℝ) ^ (2 * nn) * Gn)
    (Y := (3 : ℝ) ^ (2 * mm) * Gm)
    hCs hE2 hX0 hHsq hlamInv hcstar hkap0 hkap (three_rpow_pos _) (three_rpow_pos _)
    (three_rpow_pos _) (three_rpow_pos _).le hPnPm hW1 hQ2W hQPn hWg hsigm0 hsign0
    hsigmlow hsignlow hlam hratio (Real.rpow_nonneg hbase0 _) hGF1
    (Real.rpow_nonneg hbase0 _) hGF2 hH hsens hC

end

end Algsuperdiff.Section4.Provider.Annular
