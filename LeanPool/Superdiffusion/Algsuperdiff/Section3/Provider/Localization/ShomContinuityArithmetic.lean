/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifierGradient
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Numerics

/-!
# ShomContinuityArithmetic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The model-free arithmetic layer of `shom_continuity`

This module is the arithmetic support of
`Algsuperdiff/Section3/Provider/Localization/ShomContinuity.lean`.  The split
itself was **pure motion**: every statement and every proof arrived as the text
that stood in `ShomContinuity.lean`, unchanged apart from `private lemma`
becoming `protected theorem`.  Nothing was strengthened, renamed, added or
dropped.

That pass rewrote proof *bodies* only: all twenty-nine `nlinarith` closers were
replaced by explicit `calc` chains, monotonicity lemmas
(`mul_le_mul_of_nonneg_*`, `pow_le_pow_left₀`, `one_le_pow₀`,
`le_mul_of_one_le_right`) and named factored-nonnegativity `have`s discharged
by `linarith only`, and every remaining unqualified `linarith` was given an
explicit hypothesis list.  The twenty-three statements are byte-identical to
the pre-pass text and no declaration was added, renamed or removed; warm
own-file elaboration fell from 10.2 s to 3.6 s (`interpretation` 11.7 s to 2.6
s).

## What is here

Two groups, in the order they stood in the original file.

* **Abstract-real arithmetic** --- eighteen of the twenty-three declarations.
* **The three transcendental estimates** --- the remaining five declarations,
  namely `rpow_three_two_mul_le`, the third estimate
  `pow_four_mul_sqrt_mul_abs_log_le` with its two helpers
  `abs_log_le_sixteenth` and `sqrt_eq_pow_eight`, and `one_le_abs_log`, isolated
  exactly as before so that the nonlinear arithmetic tactics never meet a
  transcendental atom.

No renormalization, probabilistic or geometric object occurs anywhere below; no
`ABKModel`, no `Annealed.sigmaBar`, no scale.  The five model-level private
lemmas of the continuity route (`near_flow_bound`, `near_recurrence_bound`,
`window_binders`, `slack_bounds`, `defect_display`) stayed in
`ShomContinuity.lean` and are not duplicated here.

## References

* ABK26, `l.shom.continuity`; proof, whose envelope computation is the
  arithmetic realized here.
-/

namespace Algsuperdiff.Section3.Provider.Localization.ShomContinuityArithmetic

open Algsuperdiff.Section3

noncomputable section

/-! ## Abstract-real arithmetic

Every lemma in this section is over abstract reals; none of them contains a
`Real.rpow`, `Real.exp` or `Real.log` atom, so the arithmetic tactics never meet
a transcendental. -/

/-- Two-sided ratio defect from the two one-sided caps: if `a <= (1+u) b` and
`b <= (1+v) a` with `u, v >= 0`, both ratio defects are at most `u + v`. -/
protected theorem abs_ratio_defect_le {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hab : a ≤ (1 + u) * b) (hba : b ≤ (1 + v) * a) :
    |a / b - 1| + |b / a - 1| ≤ 2 * u + 2 * v := by
  have hlow_ab : (1 - v) * b ≤ a := by
    rcases le_or_gt 1 v with hv1 | hv1
    · have hnp : (1 - v) * b ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith only [hv1]) hb.le
      linarith only [hnp, ha]
    · have hmul := mul_le_mul_of_nonneg_left hba (by linarith only [hv1] : (0 : ℝ) ≤ 1 - v)
      have hstep : (1 - v) * ((1 + v) * a) ≤ a := by
        have hfac : (0 : ℝ) ≤ v ^ 2 * a := mul_nonneg (sq_nonneg v) ha.le
        linarith only [hfac]
      linarith only [hmul, hstep]
  have hlow_ba : (1 - u) * a ≤ b := by
    rcases le_or_gt 1 u with hu1 | hu1
    · have hnp : (1 - u) * a ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith only [hu1]) ha.le
      linarith only [hnp, hb]
    · have hmul := mul_le_mul_of_nonneg_left hab (by linarith only [hu1] : (0 : ℝ) ≤ 1 - u)
      have hstep : (1 - u) * ((1 + u) * b) ≤ b := by
        have hfac : (0 : ℝ) ≤ u ^ 2 * b := mul_nonneg (sq_nonneg u) hb.le
        linarith only [hfac]
      linarith only [hmul, hstep]
  have hab' : a / b ≤ 1 + u := (div_le_iff₀ hb).2 (by linarith only [hab])
  have hba' : b / a ≤ 1 + v := (div_le_iff₀ ha).2 (by linarith only [hba])
  have hab'' : 1 - v ≤ a / b := (le_div_iff₀ hb).2 (by linarith only [hlow_ab])
  have hba'' : 1 - u ≤ b / a := (le_div_iff₀ ha).2 (by linarith only [hlow_ba])
  have h1 : |a / b - 1| ≤ u + v := by
    rw [abs_le]
    exact ⟨by linarith only [hab'', hu], by linarith only [hab', hv]⟩
  have h2 : |b / a - 1| ≤ u + v := by
    rw [abs_le]
    exact ⟨by linarith only [hba'', hv], by linarith only [hba', hu]⟩
  linarith only [h1, h2]

/-- **The short-range core of branch (B).**  Two positive reals `a`, `b`
approximating two reals `A`, `B` with the *same* relative accuracy
`delta <= 1/2`, whose targets are ordered `B <= A <= (1 + 4x) B` with
`0 <= x <= 1/8`, have two-sided ratio defect at most `8x + 24 delta`.

This is the arithmetic read off the flow display rather than off the recurrence
display: `delta` is the flow's relative defect and `4x` the geometric growth of
the target profile across the gap. -/
protected theorem ratio_defect_le_of_relative {a b A B x delta : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hdelta1 : delta ≤ 1 / 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 8)
    (hfa : |a - A| ≤ delta * a) (hfb : |b - B| ≤ delta * b)
    (hBA : B ≤ A) (hAB : A ≤ (1 + 4 * x) * B) :
    |a / b - 1| + |b / a - 1| ≤ 8 * x + 24 * delta := by
  rw [abs_le] at hfa hfb
  obtain ⟨hfa1, hfa2⟩ := hfa
  obtain ⟨hfb1, hfb2⟩ := hfb
  have hdelta0 : (0 : ℝ) ≤ delta :=
    le_of_mul_le_mul_right (by linarith only [hfa1, hfa2] : (0 : ℝ) * a ≤ delta * a) ha
  have hAlo : (1 - delta) * a ≤ A := by linarith only [hfa2]
  have hAhi : A ≤ (1 + delta) * a := by linarith only [hfa1]
  have hBlo : (1 - delta) * b ≤ B := by linarith only [hfb2]
  have hBhi : B ≤ (1 + delta) * b := by linarith only [hfb1]
  have hhalf : (0 : ℝ) < 1 - delta := by linarith only [hdelta1]
  have hab : a ≤ (1 + (4 * x + 8 * delta)) * b := by
    have hchain : (1 - delta) * a ≤ (1 + 4 * x) * ((1 + delta) * b) :=
      calc (1 - delta) * a ≤ A := hAlo
        _ ≤ (1 + 4 * x) * B := hAB
        _ ≤ (1 + 4 * x) * ((1 + delta) * b) :=
            mul_le_mul_of_nonneg_left hBhi (by linarith only [hx0])
    have hgap : (1 + 4 * x) * ((1 + delta) * b) ≤
        (1 - delta) * ((1 + (4 * x + 8 * delta)) * b) := by
      have hfac : (0 : ℝ) ≤ 2 * delta * (3 - 4 * x - 4 * delta) * b :=
        mul_nonneg (mul_nonneg (by linarith only [hdelta0])
          (by linarith only [hx1, hdelta1])) hb.le
      linarith only [hfac]
    exact le_of_mul_le_mul_left (le_trans hchain hgap) hhalf
  have hba : b ≤ (1 + 4 * delta) * a := by
    have hchain : (1 - delta) * b ≤ (1 + delta) * a := by
      linarith only [hBlo, hBA, hAhi]
    have hgap : (1 + delta) * a ≤ (1 - delta) * ((1 + 4 * delta) * a) := by
      have hfac : (0 : ℝ) ≤ 2 * delta * (1 - 2 * delta) * a :=
        mul_nonneg (mul_nonneg (by linarith only [hdelta0])
          (by linarith only [hdelta1])) ha.le
      linarith only [hfac]
    exact le_of_mul_le_mul_left (le_trans hchain hgap) hhalf
  have hmain := ShomContinuityArithmetic.abs_ratio_defect_le ha hb
    (by linarith only [hx0, hdelta0] : (0 : ℝ) ≤ 4 * x + 8 * delta)
    (by linarith only [hdelta0] : (0 : ℝ) ≤ 4 * delta) hab hba
  linarith only [hmain]

/-- **The two-sided defect from the two recurrence binders** (branch (C)), over
abstract reals: `u` is the flat slack, `ai` the relative increment
`A_{n,m} shom_n^{-2}` and `qq` the relative quadratic remainder. -/
protected theorem ratio_defect_le_of_caps {sm sn ai qq u : ℝ}
    (hsm : 0 < sm) (hsn : 0 < sn) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    (hai0 : 0 ≤ ai) (hqq0 : 0 ≤ qq)
    (hup : sm ≤ (1 + u) * sn + ai * sn)
    (hlo : (1 - u) * sn + ai * sm - qq * sm ≤ sm) :
    |sm / sn - 1| + |sn / sm - 1| ≤ 6 * u + 2 * ai + 4 * qq := by
  have hupper : sm ≤ (1 + (u + ai)) * sn := by linarith only [hup]
  have hlower : sn ≤ (1 + (2 * u + 2 * qq)) * sm := by
    have hkey : (1 - u) * sn ≤ (1 + qq) * sm := by
      linarith only [hlo, mul_nonneg hai0 hsm.le]
    have hgap : (1 + qq) * sm ≤ (1 - u) * ((1 + (2 * u + 2 * qq)) * sm) := by
      have hfac : (0 : ℝ) ≤ (u + qq) * (1 - 2 * u) * sm :=
        mul_nonneg (mul_nonneg (by linarith only [hu0, hqq0])
          (by linarith only [hu])) hsm.le
      linarith only [hfac]
    have hhalf : (0 : ℝ) < 1 - u := by linarith only [hu]
    exact le_of_mul_le_mul_left (le_trans hkey hgap) hhalf
  have hmain := ShomContinuityArithmetic.abs_ratio_defect_le hsm hsn
    (by linarith only [hu0, hai0] : (0 : ℝ) ≤ u + ai)
    (by linarith only [hu0, hqq0] : (0 : ℝ) ≤ 2 * u + 2 * qq) hupper hlower
  linarith only [hmain]

/-- **The increment leg of the computation.**  With `P = 3^{2 cgamma n}` and `T =
3^{2 cgamma (m-n)} <= 27`, the lower envelope `shom_n^2 >= (1/4) cstar
cgamma^{-1} P` turns `A_{n,m} <= cstar L (m-n) P T` into `A_{n,m} shom_n^{-2} <= 216
cgamma (m-n)`. -/
protected theorem increment_ratio_le {A cs L dmn P T g x sn : ℝ}
    (hcs : 0 < cs) (hg : 0 < g) (hP : 0 < P) (hT0 : 0 < T) (hT : T ≤ 27)
    (hL0 : 0 ≤ L) (hL : L ≤ 2) (hdmn : 0 ≤ dmn)
    (hA : A ≤ cs * L * dmn * (P * T))
    (hlow : 1 / 4 * (cs * g⁻¹ * P) ≤ sn ^ 2) (hx : x = g * dmn) :
    A * (sn⁻¹) ^ 2 ≤ 216 * x := by
  have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg hg.le hdmn
  have hpos : (0 : ℝ) < 1 / 4 * (cs * g⁻¹ * P) := by positivity
  have hinvsq : (sn⁻¹) ^ 2 ≤ 4 * g * cs⁻¹ * P⁻¹ := by
    have hstep : (sn ^ 2)⁻¹ ≤ (1 / 4 * (cs * g⁻¹ * P))⁻¹ := inv_anti₀ hpos hlow
    have hid : (1 / 4 * (cs * g⁻¹ * P))⁻¹ = 4 * g * cs⁻¹ * P⁻¹ := by
      field_simp
    rw [inv_pow]
    linarith only [hstep, hid]
  have hinvsq0 : (0 : ℝ) ≤ (sn⁻¹) ^ 2 := sq_nonneg _
  have hb0 : (0 : ℝ) ≤ cs * L * dmn * (P * T) := by positivity
  have hstep : A * (sn⁻¹) ^ 2 ≤ cs * L * dmn * (P * T) * (4 * g * cs⁻¹ * P⁻¹) :=
    mul_le_mul hA hinvsq hinvsq0 hb0
  have hid : cs * L * dmn * (P * T) * (4 * g * cs⁻¹ * P⁻¹) = 4 * L * T * (g * dmn) := by
    field_simp
  have hLT : 4 * L * T ≤ 216 := by
    have hL4 : 4 * L ≤ 8 := by linarith only [hL]
    calc 4 * L * T ≤ 8 * T := mul_le_mul_of_nonneg_right hL4 hT0.le
      _ ≤ 216 := by linarith only [hT]
  have hfin : 4 * L * T * (g * dmn) ≤ 216 * x := by
    rw [← hx]
    have hmul := mul_le_mul_of_nonneg_right hLT hx0
    linarith only [hmul]
  linarith only [hstep, hid, hfin]

/-- **The quadratic leg of the computation.**  The gate `cgamma (m-n) <= cstar^2 /
2` of branch (C) is what converts the quadratic remainder's `(cgamma (m-n))^2
cstar^{-2}` into a *linear* `cgamma (m-n)`. -/
protected theorem quad_ratio_le {F cs g P T dmn x sn : ℝ}
    (hcs : 0 < cs) (hg : 0 < g) (hP : 0 < P) (hT0 : 0 < T) (hT : T ≤ 27)
    (hF : 1 ≤ F) (hdmn : 0 ≤ dmn)
    (hlow : 1 / 4 * (cs * g⁻¹ * P) ≤ sn ^ 2)
    (hx : x = g * dmn) (hxcs : x ≤ cs ^ 2 / 2) :
    F * dmn ^ 2 * (sn⁻¹) ^ 4 * ((P * T) * (P * T)) ≤ 5832 * F * x := by
  have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg hg.le hdmn
  have hpos : (0 : ℝ) < 1 / 4 * (cs * g⁻¹ * P) := by positivity
  have hinvsq : (sn⁻¹) ^ 2 ≤ 4 * g * cs⁻¹ * P⁻¹ := by
    have hstep : (sn ^ 2)⁻¹ ≤ (1 / 4 * (cs * g⁻¹ * P))⁻¹ := inv_anti₀ hpos hlow
    have hid : (1 / 4 * (cs * g⁻¹ * P))⁻¹ = 4 * g * cs⁻¹ * P⁻¹ := by
      field_simp
    rw [inv_pow]
    linarith only [hstep, hid]
  have hinvsq0 : (0 : ℝ) ≤ (sn⁻¹) ^ 2 := sq_nonneg _
  have hfour : (sn⁻¹) ^ 4 ≤ (4 * g * cs⁻¹ * P⁻¹) ^ 2 := by
    have hid : (sn⁻¹) ^ 4 = ((sn⁻¹) ^ 2) ^ 2 := by ring
    rw [hid]
    exact pow_le_pow_left₀ hinvsq0 hinvsq 2
  have hcoef0 : (0 : ℝ) ≤ F * dmn ^ 2 := by positivity
  have hPT0 : (0 : ℝ) ≤ (P * T) * (P * T) := by positivity
  have hstep : F * dmn ^ 2 * (sn⁻¹) ^ 4 * ((P * T) * (P * T)) ≤
      F * dmn ^ 2 * ((4 * g * cs⁻¹ * P⁻¹) ^ 2) * ((P * T) * (P * T)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfour hcoef0) hPT0
  have hid : F * dmn ^ 2 * ((4 * g * cs⁻¹ * P⁻¹) ^ 2) * ((P * T) * (P * T))
      = 16 * F * T ^ 2 * ((cs ^ 2)⁻¹ * (g * dmn) ^ 2) := by
    field_simp
    ring
  have hcs2 : (0 : ℝ) < cs ^ 2 := pow_pos hcs 2
  have hxsq : x ^ 2 ≤ cs ^ 2 / 2 * x := by
    calc x ^ 2 = x * x := pow_two x
      _ ≤ cs ^ 2 / 2 * x := mul_le_mul_of_nonneg_right hxcs hx0
  have hquot : (cs ^ 2)⁻¹ * x ^ 2 ≤ x / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hxsq (inv_nonneg.2 hcs2.le)
    have hid2 : (cs ^ 2)⁻¹ * (cs ^ 2 / 2 * x) = x / 2 := by field_simp
    linarith only [hmul, hid2]
  have hT2 : T ^ 2 ≤ 729 := by
    calc T ^ 2 ≤ 27 ^ 2 := pow_le_pow_left₀ hT0.le hT 2
      _ = 729 := by norm_num
  have hF0 : (0 : ℝ) ≤ F := by linarith only [hF]
  have hxx0 : (0 : ℝ) ≤ (cs ^ 2)⁻¹ * x ^ 2 := by positivity
  have hfin : 16 * F * T ^ 2 * ((cs ^ 2)⁻¹ * (g * dmn) ^ 2) ≤ 5832 * F * x := by
    rw [← hx]
    have h16F : (0 : ℝ) ≤ 16 * F := by linarith only [hF0]
    have s1 : 16 * F * T ^ 2 * ((cs ^ 2)⁻¹ * x ^ 2) ≤
        16 * F * 729 * ((cs ^ 2)⁻¹ * x ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2 h16F) hxx0
    have s2 : 16 * F * 729 * ((cs ^ 2)⁻¹ * x ^ 2) ≤ 16 * F * 729 * (x / 2) :=
      mul_le_mul_of_nonneg_left hquot (by linarith only [hF0])
    linarith only [s1, s2]
  linarith only [hstep, hid, hfin]

/-- The growth cap from the squared envelope comparison. -/
protected theorem growth_from_sq {sm sn t Dm Dn : ℝ} (hsn : 0 < sn) (ht : 1 ≤ t)
    (hup : sm ^ 2 ≤ 4 * Dm) (hcomp : Dm ≤ t * t * Dn) (hlo : (1 / 4 : ℝ) * Dn ≤ sn ^ 2) :
    sm ≤ 4 * t * sn := by
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hsq : sm ^ 2 ≤ (4 * t * sn) ^ 2 := by
    have hDn : Dn ≤ 4 * sn ^ 2 := by linarith only [hlo]
    have h2 : t * t * Dn ≤ t * t * (4 * sn ^ 2) :=
      mul_le_mul_of_nonneg_left hDn (mul_nonneg ht0 ht0)
    calc sm ^ 2 ≤ 4 * Dm := hup
      _ ≤ 4 * (t * t * Dn) := by linarith only [hcomp]
      _ ≤ 4 * (t * t * (4 * sn ^ 2)) := by linarith only [h2]
      _ = (4 * t * sn) ^ 2 := by ring
  refine Provider.Corrector.le_of_sq_le_sq_of_nonneg hsq ?_
  positivity

/-- The short-range collapse of the growth cap. -/
protected theorem collapse_of_growth {sm sn t : ℝ} (hsn : 0 < sn)
    (hgrow : sm ≤ 4 * t * sn) (ht3 : t ≤ 3) :
    sm / sn ≤ 12 := by
  rw [div_le_iff₀ hsn]
  have hfac : (0 : ℝ) ≤ (12 - 4 * t) * sn := mul_nonneg (by linarith only [ht3]) hsn.le
  linarith only [hgrow, hfac]

/-- The geometric growth of the target profile `nu^2 + c 3^{2 cgamma k}`, once
the geometric factor has been linearised. -/
protected theorem profile_growth {nu2 c g x : ℝ} (hnu2 : 0 ≤ nu2) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hg : g ≤ 1 + 8 * x) :
    nu2 + c * g ≤ (1 + 4 * x) ^ 2 * (nu2 + c) := by
  have h1 : c * g ≤ c * (1 + 8 * x) := mul_le_mul_of_nonneg_left hg hc
  have h2 : (0 : ℝ) ≤ x * nu2 := mul_nonneg hx hnu2
  have h3 : (0 : ℝ) ≤ x ^ 2 * nu2 := mul_nonneg (sq_nonneg x) hnu2
  have h4 : (0 : ℝ) ≤ x ^ 2 * c := mul_nonneg (sq_nonneg x) hc
  linarith only [h1, h2, h3, h4]

/-- **The `delta` gate.**  Under `32 Cflow cstar^{-1} <= E`, `1 <= Cflow` and the
`E^4` gate, the flow's relative defect is below `cstar^2 / 2`.  This is the
sharpening records: it is what removes the manuscript's medium band and keeps
the constant dimension-only. -/
protected theorem defect_le_cstar_sq {sg Ev cs Cf : ℝ}
    (hE : 1 ≤ Ev) (hgate : Ev ^ 4 * sg ≤ 16)
    (hcs0 : 0 < cs) (hCf : 1 ≤ Cf) (hCE : 32 * Cf * cs⁻¹ ≤ Ev) :
    Cf * cs⁻¹ * Ev * sg ≤ cs ^ 2 / 2 := by
  have hE0 : (0 : ℝ) < Ev := lt_of_lt_of_le one_pos hE
  have hcsE : 32 * Cf ≤ cs * Ev := by
    have hmul := mul_le_mul_of_nonneg_right hCE hcs0.le
    have hid : 32 * Cf * cs⁻¹ * cs = 32 * Cf := by field_simp
    linarith only [hmul, hid]
  have hgoal : 2 * Cf * Ev * sg ≤ cs ^ 3 := by
    have hcs3 : (32 * Cf) ^ 3 ≤ (cs * Ev) ^ 3 := pow_le_pow_left₀ (by positivity) hcsE 3
    have hstep : 2 * Cf * Ev * sg * Ev ^ 3 ≤ 32 * Cf := by
      have hfac : (0 : ℝ) ≤ 2 * Cf * (16 - Ev ^ 4 * sg) :=
        mul_nonneg (by linarith only [hCf]) (by linarith only [hgate])
      linarith only [hfac]
    have hCflow3 : 32 * Cf ≤ (32 * Cf) ^ 3 := by
      have h32 : (32 : ℝ) ≤ 32 * Cf := by linarith only [hCf]
      have hsq : (1 : ℝ) ≤ (32 * Cf) ^ 2 := one_le_pow₀ (by linarith only [h32])
      calc 32 * Cf = 32 * Cf * 1 := by ring
        _ ≤ 32 * Cf * (32 * Cf) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by linarith only [h32])
        _ = (32 * Cf) ^ 3 := by ring
    have hE3 : (0 : ℝ) < Ev ^ 3 := by positivity
    have hchain : 2 * Cf * Ev * sg * Ev ^ 3 ≤ cs ^ 3 * Ev ^ 3 := by
      calc 2 * Cf * Ev * sg * Ev ^ 3 ≤ 32 * Cf := hstep
        _ ≤ (32 * Cf) ^ 3 := hCflow3
        _ ≤ (cs * Ev) ^ 3 := hcs3
        _ = cs ^ 3 * Ev ^ 3 := by ring
    exact le_of_mul_le_mul_right (by linarith only [hchain]) hE3
  have hid : Cf * cs⁻¹ * Ev * sg * cs = Cf * Ev * sg := by field_simp
  refine le_of_mul_le_mul_right ?_ hcs0
  rw [hid]
  linarith only [hgoal]

/-- The master smallness of the printed flat entry: `Es E <= 256` where
`Es = E^2 sg^2`. -/
protected theorem flat_master {sg Ev : ℝ} (hE : 1 ≤ Ev) (hsg0 : 0 ≤ sg)
    (hgate : Ev ^ 4 * sg ≤ 16) :
    Ev ^ 2 * sg ^ 2 * Ev ≤ 256 := by
  have hE0 : (0 : ℝ) < Ev := lt_of_lt_of_le one_pos hE
  have hb0 : (0 : ℝ) ≤ Ev ^ 4 * sg := mul_nonneg (by positivity) hsg0
  have hsq : (Ev ^ 4 * sg) ^ 2 ≤ 16 ^ 2 := pow_le_pow_left₀ hb0 hgate 2
  have hid : (Ev ^ 4 * sg) ^ 2 = Ev ^ 8 * sg ^ 2 := by ring
  have hmono : Ev ^ 3 ≤ Ev ^ 8 := pow_le_pow_right₀ hE (by norm_num)
  have hstep : Ev ^ 3 * sg ^ 2 ≤ Ev ^ 8 * sg ^ 2 :=
    mul_le_mul_of_nonneg_right hmono (sq_nonneg sg)
  have hid2 : Ev ^ 2 * sg ^ 2 * Ev = Ev ^ 3 * sg ^ 2 := by ring
  norm_num at hsq
  linarith only [hsq, hid, hstep, hid2]

/-- Any dimension-only multiple of the flat entry is small at a large `E`. -/
protected theorem flat_small {Es Ev K c : ℝ} (hE0 : 0 < Ev)
    (hmaster : Es * Ev ≤ 256) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c)
    (hKE : 256 * K * c ≤ Ev) :
    c * (K * Es) ≤ 1 := by
  have hcK : (0 : ℝ) ≤ c * K := mul_nonneg hc0 hK0
  have h1 : c * K * (Es * Ev) ≤ c * K * 256 := mul_le_mul_of_nonneg_left hmaster hcK
  have h2 : c * K * 256 ≤ Ev := by linarith only [hKE]
  have h3 : c * (K * Es) * Ev ≤ 1 * Ev := by linarith only [h1, h2]
  exact le_of_mul_le_mul_right h3 hE0

/-- `g <= 1/1024` from the `cgamma`-gate at `E >= 2`. -/
protected theorem gamma_small {g Ev : ℝ} (hE : 2 ≤ Ev) (hgate : g ≤ (Ev⁻¹) ^ 10) :
    g ≤ 1 / 1024 := by
  have hE0 : (0 : ℝ) < Ev := by linarith only [hE]
  have hinv : Ev⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hE0 (by norm_num)]
    linarith only [hE]
  have hpow : (Ev⁻¹) ^ 10 ≤ (1 / 2 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (inv_pos.2 hE0).le hinv 10
  have hval : ((1 : ℝ) / 2) ^ 10 = 1 / 1024 := by norm_num
  linarith only [hgate, hpow, hval.le, hval.ge]

/-- `g <= E^2 (g L^2)` when `1 <= E` and `1 <= L`: the printed entry dominates
`cgamma` itself. -/
protected theorem le_flat {g Ev L : ℝ} (hg0 : 0 ≤ g) (hE : 1 ≤ Ev) (hL : 1 ≤ L) :
    g ≤ Ev ^ 2 * (g * L ^ 2) := by
  have hE2 : (1 : ℝ) ≤ Ev ^ 2 := one_le_pow₀ hE
  have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL
  have hprod : (1 : ℝ) ≤ Ev ^ 2 * L ^ 2 :=
    le_trans hE2 (le_mul_of_one_le_right (sq_nonneg Ev) hL2)
  have h1 : g * 1 ≤ g * (Ev ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_left hprod hg0
  have hid : g * (Ev ^ 2 * L ^ 2) = Ev ^ 2 * (g * L ^ 2) := by ring
  linarith only [h1, hid]

/-- `cstar^2 / 2 <= cstar` in the repository's range `cstar <= 3/2`. -/
protected theorem sq_half_le {cs : ℝ} (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2) :
    cs ^ 2 / 2 ≤ cs := by
  have hfac : (0 : ℝ) ≤ cs * (2 - cs) := mul_nonneg hcs0.le (by linarith only [hcs32])
  linarith only [hfac]

/-- Regrouping of the flow display at one scale, with the constant enlarged to `max
1 Cflow`. -/
protected theorem flow_regroup {a Cflow Cf ci Ev r q s : ℝ}
    (h : a ≤ Cflow * ci * Ev * r * q * s) (hCC : Cflow ≤ Cf)
    (hci : 0 ≤ ci) (hEv : 0 ≤ Ev) (hr : 0 ≤ r) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    a ≤ Cf * ci * Ev * (r * q) * s := by
  have hrest : (0 : ℝ) ≤ ci * Ev * (r * q) * s := by positivity
  have hmul := mul_le_mul_of_nonneg_right hCC hrest
  linarith only [h, hmul]

/-- Assembly of the display in the far branch (A). -/
protected theorem display_of_far {S Xv t C : ℝ} (hS : S ≤ 8 * t) (hXv : 1 / 8 ≤ Xv)
    (ht : 1 ≤ t) (hC : 64 ≤ C) :
    S ≤ C * min 1 Xv * t := by
  have hmin : (1 / 8 : ℝ) ≤ min 1 Xv := le_min (by norm_num) hXv
  have ht0 : (0 : ℝ) ≤ t := by linarith only [ht]
  have h1 : (64 : ℝ) * (1 / 8) ≤ C * min 1 Xv :=
    mul_le_mul hC hmin (by norm_num) (by linarith only [hC])
  have h2 : (8 : ℝ) * t ≤ C * min 1 Xv * t := by
    have hstep := mul_le_mul_of_nonneg_right h1 ht0
    linarith only [hstep]
  linarith only [hS, h2]

/-- Assembly of the display in the near branches (B) and (C), from a bound at
the min-entry itself. -/
protected theorem display_of_bound {S X t C : ℝ} (hS : S ≤ C * X) (hX0 : 0 ≤ X)
    (hone : X ≤ 1) (ht : 1 ≤ t) (hC0 : 0 ≤ C) :
    S ≤ C * min 1 X * t := by
  rw [min_eq_right hone]
  have hCX : (0 : ℝ) ≤ C * X := mul_nonneg hC0 hX0
  have hstep := mul_le_mul_of_nonneg_left ht hCX
  linarith only [hS, hstep]

/-- **Abstract-real core of the exponential's tangent bound.**  From
`(1 - u) X <= 1` with `0 <= u <= 1/2`, cancel the positive factor `1 - u`
against `(1 - u)(1 + 2u) = 1 + u - 2u^2 >= 1` (`X` need not be nonnegative).
Applied at `X := Real.exp (4 z)`, `u := 4 z`, it keeps `Real.exp` out of every
nonlinear tactic goal in `rpow_three_two_mul_le`. -/
protected theorem le_one_add_two_mul_of_one_sub_mul_le_one {X u : ℝ}
    (hkey : (1 - u) * X ≤ 1) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) : X ≤ 1 + 2 * u := by
  have hprod : (0 : ℝ) ≤ u * (1 - 2 * u) := mul_nonneg hu0 (by linarith only [hu])
  refine le_of_mul_le_mul_left (le_trans hkey ?_) (by linarith only [hu] : (0 : ℝ) < 1 - u)
  linarith only [hprod]

/-! ## The three transcendental estimates

Each is a consequence of `Real.add_one_le_exp` or `Real.log_le_sub_one_of_pos`;
they are isolated here so that no `nlinarith` ever meets a transcendental.
Since the  elaboration pass this file contains **no `nlinarith` at all**, and
every `linarith` in it is an `only`-form with an explicit hypothesis list, so
no rpow-laden context is preprocessed into products anywhere below.  The only
`nlinarith` on the route is in the consumer `ShomContinuity.lean`, the
`only`-form of `near_recurrence_bound` on three `cstar` facts.  `linarith` in
the consumer does meet `Real.exp`, `Real.log` and `Real.rpow`, but only as
opaque atoms and monomials in them (the earlier unqualified claim, that no
arithmetic tactic there sees them in a nonlinear position, was false as
stated). -/

/-- `3^{2z} <= 1 + 8z` for `0 <= z <= 1/8`, from `log 3 <= 2` and
`exp u <= (1-u)^{-1}`. -/
protected theorem rpow_three_two_mul_le {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 8) :
    (3 : ℝ) ^ (2 * z) ≤ 1 + 8 * z := by
  have hlog3 : Real.log 3 ≤ 2 := Provider.Percolation.log_three_le_two
  have hexp : (3 : ℝ) ^ (2 * z) = Real.exp (Real.log 3 * (2 * z)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hmono : Real.exp (Real.log 3 * (2 * z)) ≤ Real.exp (4 * z) := by
    refine Real.exp_le_exp.2 ?_
    have hz2 : (0 : ℝ) ≤ 2 * z := by linarith only [hz0]
    calc Real.log 3 * (2 * z) ≤ 2 * (2 * z) := mul_le_mul_of_nonneg_right hlog3 hz2
      _ = 4 * z := by ring
  have hu0 : (0 : ℝ) ≤ 4 * z := by linarith only [hz0]
  have hu1 : 4 * z ≤ 1 / 2 := by linarith only [hz1]
  have hbern : -(4 * z) + 1 ≤ Real.exp (-(4 * z)) := Real.add_one_le_exp _
  have hpos : (0 : ℝ) < Real.exp (4 * z) := Real.exp_pos _
  have hinv : Real.exp (-(4 * z)) = (Real.exp (4 * z))⁻¹ := Real.exp_neg _
  have hkey : (1 - 4 * z) * Real.exp (4 * z) ≤ 1 := by
    rw [hinv] at hbern
    have hmul := mul_le_mul_of_nonneg_right hbern hpos.le
    rw [inv_mul_cancel₀ (ne_of_gt hpos)] at hmul
    linarith only [hmul]
  have hfinal : Real.exp (4 * z) ≤ 1 + 8 * z := by
    have hcore :=
      ShomContinuityArithmetic.le_one_add_two_mul_of_one_sub_mul_le_one hkey hu0 hu1
    linarith only [hcore]
  rw [hexp]
  linarith only [hmono, hfinal]

/-- `|log g| <= 16 v^{-1}` with `v = g^{1/16}`, written with iterated square
roots so that no `Real.rpow` occurs. -/
protected theorem abs_log_le_sixteenth {g : ℝ} (hg0 : 0 < g) (hg1 : g ≤ 1) :
    |Real.log g| ≤ 16 * (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g))))⁻¹ := by
  set v : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g))) with hv
  have hv0 : 0 < v := by
    rw [hv]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hg0)))
  have hlogv : Real.log v = Real.log g / 16 := by
    rw [hv, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
      Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hg0.le]
    ring
  have hbern : Real.log v⁻¹ ≤ v⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hv0)
  have hloginv : Real.log v⁻¹ = -(Real.log g / 16) := by rw [Real.log_inv, hlogv]
  have hlognp : Real.log g ≤ 0 := Real.log_nonpos hg0.le hg1
  have habs : |Real.log g| = -Real.log g := abs_of_nonpos hlognp
  rw [hloginv] at hbern
  rw [habs]
  linarith only [hbern]

/-- `sqrt g = v ^ 8` with `v = g^{1/16}`. -/
protected theorem sqrt_eq_pow_eight (g : ℝ) :
    Real.sqrt g = (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g)))) ^ 8 := by
  have h1 : Real.sqrt (Real.sqrt g) ^ 2 = Real.sqrt g :=
    Real.sq_sqrt (Real.sqrt_nonneg g)
  have h2 : Real.sqrt (Real.sqrt (Real.sqrt g)) ^ 2 = Real.sqrt (Real.sqrt g) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g))) ^ 2 =
      Real.sqrt (Real.sqrt (Real.sqrt g)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  calc Real.sqrt g = (Real.sqrt (Real.sqrt g)) ^ 2 := h1.symm
    _ = ((Real.sqrt (Real.sqrt (Real.sqrt g))) ^ 2) ^ 2 := by rw [h2]
    _ = (((Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g)))) ^ 2) ^ 2) ^ 2 := by rw [h3]
    _ = (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g)))) ^ 8 := by ring

/-- **The `cgamma`-gate at the sharp exponent**.  Under `1 <= E` and `cgamma <=
E^{-10}`, `E^4 cgamma^{1/2} |log cgamma| <= 16`.  Every comparison is an
integer power: `v := g^{1/16}` is four square roots, `|log g| <= 16 v^{-1}`,
`sqrt g = v^8`, and `(E^4 v^7)^{16} = E^{64} g^7 <= E^{64} E^{-70} <= 1`. -/
protected theorem pow_four_mul_sqrt_mul_abs_log_le {g Ev : ℝ} (hg0 : 0 < g) (hE : 1 ≤ Ev)
    (hgate : g ≤ (Ev⁻¹) ^ 10) :
    Ev ^ 4 * (Real.sqrt g * |Real.log g|) ≤ 16 := by
  have hE0 : (0 : ℝ) < Ev := lt_of_lt_of_le one_pos hE
  have hinv1 : Ev⁻¹ ≤ 1 := by rw [inv_le_one₀ hE0]; exact hE
  have hinv0 : (0 : ℝ) ≤ Ev⁻¹ := (inv_pos.2 hE0).le
  have hg1 : g ≤ 1 := by
    have hone : (Ev⁻¹) ^ 10 ≤ 1 := pow_le_one₀ hinv0 hinv1
    linarith only [hone, hgate]
  set v : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt g))) with hv
  have hv0 : 0 < v := by
    rw [hv]
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 (Real.sqrt_pos.2 hg0)))
  have hv16 : v ^ 16 = g := by
    have h8 := ShomContinuityArithmetic.sqrt_eq_pow_eight g
    have hsq : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg0.le
    calc v ^ 16 = (v ^ 8) ^ 2 := by ring
      _ = Real.sqrt g ^ 2 := by rw [← h8]
      _ = g := hsq
  have hstep : Real.sqrt g * |Real.log g| ≤ 16 * v ^ 7 := by
    have hlog := ShomContinuityArithmetic.abs_log_le_sixteenth hg0 hg1
    have hsqrt : Real.sqrt g = v ^ 8 := ShomContinuityArithmetic.sqrt_eq_pow_eight g
    have hmul : Real.sqrt g * |Real.log g| ≤ v ^ 8 * (16 * v⁻¹) := by
      rw [hsqrt]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    have hid : v ^ 8 * (16 * v⁻¹) = 16 * v ^ 7 := by field_simp
    linarith only [hmul, hid]
  have hkey : Ev ^ 4 * v ^ 7 ≤ 1 := by
    have hpow : (Ev ^ 4 * v ^ 7) ^ 16 ≤ 1 := by
      have hvg : (v ^ 7) ^ 16 = g ^ 7 := by
        rw [show ((v : ℝ) ^ 7) ^ 16 = (v ^ 16) ^ 7 by ring, hv16]
      have hgE : g ^ 7 ≤ ((Ev⁻¹) ^ 10) ^ 7 := pow_le_pow_left₀ hg0.le hgate 7
      have hid : ((Ev⁻¹) ^ 10) ^ 7 = (Ev ^ 70)⁻¹ := by rw [← pow_mul, ← inv_pow]
      have hexp : (Ev ^ 4 * v ^ 7) ^ 16 = Ev ^ 64 * g ^ 7 := by
        rw [mul_pow, ← pow_mul, hvg]
      have hE70 : (0 : ℝ) < Ev ^ 70 := by positivity
      have hfin : Ev ^ 64 * g ^ 7 ≤ Ev ^ 64 * (Ev ^ 70)⁻¹ := by
        have hlift := mul_le_mul_of_nonneg_left (le_trans hgE (le_of_eq hid))
          (by positivity : (0 : ℝ) ≤ Ev ^ 64)
        linarith only [hlift]
      have hquot : Ev ^ 64 * (Ev ^ 70)⁻¹ ≤ 1 := by
        rw [mul_inv_le_iff₀ hE70, one_mul]
        exact pow_le_pow_right₀ hE (by norm_num)
      rw [hexp]
      linarith only [hfin, hquot]
    by_contra hcon
    push Not at hcon
    have hgt : (1 : ℝ) < (Ev ^ 4 * v ^ 7) ^ 16 := one_lt_pow₀ hcon (by norm_num)
    linarith only [hpow, hgt]
  have hE4 : (0 : ℝ) ≤ Ev ^ 4 := by positivity
  calc Ev ^ 4 * (Real.sqrt g * |Real.log g|) ≤ Ev ^ 4 * (16 * v ^ 7) :=
        mul_le_mul_of_nonneg_left hstep hE4
    _ = 16 * (Ev ^ 4 * v ^ 7) := by ring
    _ ≤ 16 * 1 := by linarith only [hkey]
    _ = 16 := by ring

/-- `1 <= |log g|` for `0 < g <= 1/3`. -/
protected theorem one_le_abs_log {g : ℝ} (hg0 : 0 < g) (hg3 : g ≤ 1 / 3) :
    1 ≤ |Real.log g| := by
  have hL3 : (1 : ℝ) ≤ Real.log 3 := Provider.Percolation.one_le_log_three
  have hval : Real.log (1 / 3 : ℝ) = -Real.log 3 := by
    rw [one_div, Real.log_inv]
  have hmono : Real.log g ≤ -Real.log 3 := by
    have hstep := Real.log_le_log hg0 hg3
    rw [hval] at hstep
    exact hstep
  have hnp : Real.log g ≤ 0 := by linarith only [hL3, hmono]
  rw [abs_of_nonpos hnp]
  linarith only [hmono, hL3]

end

end Algsuperdiff.Section3.Provider.Localization.ShomContinuityArithmetic
