/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration.Core
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Int.Interval

/-!
# Descent

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Deterministic recurrence integration: adaptive descent

This file formalizes the adaptive descent and its purely ordered telescoping
backbone for ABK26 `l.integrate.approx.recurrence`, Steps 3--4.  The argument
uses a single step-back strong induction, an equivalent presentation of the
paper’s adaptive-chain summation.

## References

* ABK26.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

open scoped BigOperators

noncomputable section

namespace Internal

open Real

/-- Growth-flavoured one-sided drop: the `G(1 − q)` factorization dominates
`2κδ·G` once `1 − q ≥ (δ log 3)/2`. Here `κ = log 3 / 18`. -/
lemma growth_side {G q δ κ : ℝ}
    (hG : 0 ≤ G) (hδ : 0 ≤ δ) (hκ : κ = Real.log 3 / 18)
    (h1mq : (δ * Real.log 3) / 2 ≤ 1 - q) :
    2 * κ * δ * G ≤ G * (1 - q) := by
  subst hκ
  have hstep : G * ((δ * Real.log 3) / 2) ≤ G * (1 - q) :=
    mul_le_mul_of_nonneg_left h1mq hG
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hGδl : 0 ≤ G * δ * Real.log 3 := mul_nonneg (mul_nonneg hG hδ) hlog3
  linarith only [hstep, hGδl]

/-- Plateau-flavoured one-sided drop, outer step: if `b ≤ G_n·w` and
`w ≤ r − 1` with `G_n ≥ 0`, then `b ≤ G_n·(r − 1)`. -/
lemma plateau_side {Gn w r b : ℝ}
    (hGn : 0 ≤ Gn) (hb : b ≤ Gn * w) (hr : w ≤ r - 1) :
    b ≤ Gn * (r - 1) :=
  hb.trans (mul_le_mul_of_nonneg_left hr hGn)

/-- Plateau-flavoured one-sided drop, inner product estimate (all opaque
reals). With `G_n = c⋆K_γ·g_n`, `g_n = g_m·q`, `q ≥ 1/9`, the adaptive-step
lower bound `γδν²c⋆⁻¹g_m⁻¹ ≤ 2γa`, and `γK_γ ≥ 1`, one has
`2κδν² ≤ c⋆K_γ·g_n·(2γa·log 3)` with `κ = log 3 / 18`. -/
lemma plateau_product {cstar Kγ gm gn q γ a δ ν2 κ : ℝ}
    (hgn : gn = gm * q) (hq : (1 : ℝ) / 9 ≤ q) (hgm : 0 < gm) (hγ : 0 < γ)
    (ha : γ * δ * ν2 * cstar⁻¹ * gm⁻¹ ≤ 2 * γ * a)
    (hγKγ : 1 ≤ γ * Kγ) (hcstar : 0 < cstar)
    (hδ : 0 ≤ δ) (hν2 : 0 ≤ ν2) (hKγ : 0 ≤ Kγ) (hκ : κ = Real.log 3 / 18) :
    2 * κ * δ * ν2 ≤ cstar * Kγ * gn * (2 * γ * a * Real.log 3) := by
  subst hκ
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hcs_ne : cstar ≠ 0 := ne_of_gt hcstar
  have hgm_ne : gm ≠ 0 := ne_of_gt hgm
  have hcs_cancel : cstar * cstar⁻¹ = 1 := mul_inv_cancel₀ hcs_ne
  have hgm_cancel : gm * gm⁻¹ = 1 := mul_inv_cancel₀ hgm_ne
  -- Let A:= 2γa. We have A ≥ A0:= γδν²c⋆⁻¹g_m⁻¹ ≥ 0, and q ≥ 1/9.
  set A : ℝ := 2 * γ * a with hA
  have hA0nn : 0 ≤ γ * δ * ν2 * cstar⁻¹ * gm⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hγ.le hδ) hν2)
      (inv_nonneg.mpr hcstar.le)) (inv_nonneg.mpr hgm.le)
  have hAnn : 0 ≤ A := le_trans hA0nn ha
  -- q·A ≥ (1/9)·A0
  have hqA : (1 / 9) * (γ * δ * ν2 * cstar⁻¹ * gm⁻¹) ≤ q * A := by
    have h1 : (1 / 9) * A ≤ q * A := mul_le_mul_of_nonneg_right hq hAnn
    have h2 : (1 / 9) * (γ * δ * ν2 * cstar⁻¹ * gm⁻¹) ≤ (1 / 9) * A := by
      linarith only [ha]
    linarith only [h1, h2]
  -- multiply by c⋆K_γ g_m log3 ≥ 0
  have hcoef : 0 ≤ cstar * Kγ * gm * Real.log 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg hcstar.le hKγ) hgm.le) hlog3.le
  have hmul : cstar * Kγ * gm * Real.log 3 * ((1 / 9) * (γ * δ * ν2 * cstar⁻¹ * gm⁻¹))
      ≤ cstar * Kγ * gm * Real.log 3 * (q * A) :=
    mul_le_mul_of_nonneg_left hqA hcoef
  -- LHS simplifies to (1/9)(γKγ)δν²log3 ≥ (1/9)δν²log3 = 2κδν²
  have hLHS : cstar * Kγ * gm * Real.log 3 * ((1 / 9) * (γ * δ * ν2 * cstar⁻¹ * gm⁻¹))
      = (1 / 9) * (γ * Kγ) * δ * ν2 * Real.log 3 * ((cstar * cstar⁻¹) * (gm * gm⁻¹)) := by
    ring
  rw [hcs_cancel, hgm_cancel, mul_one, mul_one] at hLHS
  have hlow : 2 * (Real.log 3 / 18) * δ * ν2
      ≤ (1 / 9) * (γ * Kγ) * δ * ν2 * Real.log 3 := by
    have hbase : 0 ≤ δ * ν2 * Real.log 3 :=
      mul_nonneg (mul_nonneg hδ hν2) hlog3.le
    linarith only [mul_nonneg (by linarith only [hγKγ] : (0:ℝ) ≤ γ * Kγ - 1) hbase]
  -- of hmul equals the target's
  have hRHS : cstar * Kγ * gm * Real.log 3 * (q * A) = cstar * Kγ * gn * (A * Real.log 3) := by
    rw [hgn]; ring
  rw [hLHS] at hmul
  rw [hRHS] at hmul
  calc 2 * (Real.log 3 / 18) * δ * ν2
      ≤ (1 / 9) * (γ * Kγ) * δ * ν2 * Real.log 3 := hlow
    _ ≤ cstar * Kγ * gn * (A * Real.log 3) := hmul
    _ = cstar * Kγ * gn * (2 * γ * a * Real.log 3) := by rw [hA]

/-- **Quadratic-term control (abstract reals).** With `cf = 1 + c⋆⁻²F`, the
adaptive step choice `μ_n·a ≤ δγ⁻¹` and the constant identity `δ²·cf = Eγ`
force the chunk's quadratic term below `E`:
`cf·μ_n²·γ·a² ≤ E`. -/
lemma quad_bound {cf μn a δ γ E : ℝ}
    (hμa : μn * a ≤ δ * γ⁻¹) (hμn : 0 ≤ μn) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hcf : 0 < cf) (hγ : 0 < γ) (hδ2 : δ ^ 2 * cf = E * γ) :
    cf * μn ^ 2 * γ * a ^ 2 ≤ E := by
  have hμa_nn : 0 ≤ μn * a := mul_nonneg hμn ha
  have hδγ_nn : 0 ≤ δ * γ⁻¹ := mul_nonneg hδ (inv_nonneg.mpr hγ.le)
  have hsq : (μn * a) ^ 2 ≤ (δ * γ⁻¹) ^ 2 := by
    apply pow_le_pow_left₀ hμa_nn hμa
  have hval : cf * γ * (δ * γ⁻¹) ^ 2 = E := by
    have h1 : cf * γ * (δ * γ⁻¹) ^ 2 = (δ ^ 2 * cf) * γ⁻¹ * (γ * γ⁻¹) := by ring
    rw [h1, mul_inv_cancel₀ (ne_of_gt hγ), mul_one, hδ2, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
  have hcfγ : 0 ≤ cf * γ := mul_nonneg hcf.le hγ.le
  calc cf * μn ^ 2 * γ * a ^ 2 = cf * γ * (μn * a) ^ 2 := by ring
    _ ≤ cf * γ * (δ * γ⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hsq hcfγ
    _ = E := hval

/-- **Small-scale base case (abstract reals), two-constant form.** From the
small-scale two-sided bound `ν² ≤ s_m² ≤ (1+β)²ν²` with the **envelope**
constant `c⁺` (`β = ν⁻²c⁺γ⁻¹3^{2γm}`), `β ≤ 1`, `4γ ≤ 1`, and
`γ⁻¹ ≤ K_γ ≤ γ⁻¹+4`, the squared deviation against the comparator `T_m` built
from the **recurrence** constant `c⋆ ≤ c⁺` obeys the crude bound
`|s_m² − T_m| ≤ 5·c⁺γ⁻¹3^{2γm}`.

This is `e.small.m.is.done` in division-free form.  The final `≤ C₀√(Θγ)T_m`
shape is recovered downstream using `g_m ≤ B_b`. -/
lemma small_scale_algebra {sm2 nu2 gm cstar cplus γ Kγ β : ℝ}
    (hnu2 : 0 < nu2) (hcstar : 0 < cstar) (hcc : cstar ≤ cplus) (hγ : 0 < γ) (hgm : 0 ≤ gm)
    (hlo : nu2 ≤ sm2) (hup : sm2 ≤ (1 + β) ^ 2 * nu2)
    (hβdef : β = nu2⁻¹ * cplus * γ⁻¹ * gm) (hβ1 : β ≤ 1) (hγ1 : 4 * γ ≤ 1)
    (hKγlo : γ⁻¹ ≤ Kγ) (hKγhi : Kγ ≤ γ⁻¹ + 4) :
    |sm2 - (nu2 + cstar * Kγ * gm)| ≤ 5 * (cplus * γ⁻¹ * gm) := by
  have hγinv : (0:ℝ) ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  set cm := cstar * γ⁻¹ * gm with hcm
  set c := cplus * γ⁻¹ * gm with hc
  have hcmnn : 0 ≤ cm := by rw [hcm]; positivity
  have hcnn : 0 ≤ c := by
    rw [hc]; exact mul_nonneg (mul_nonneg (le_trans hcstar.le hcc) hγinv) hgm
  have hcmc : cm ≤ c := by
    rw [hcm, hc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hγinv) hgm
  have hβc : β * nu2 = c := by
    rw [hβdef, hc,
      show nu2⁻¹ * cplus * γ⁻¹ * gm * nu2 = cplus * γ⁻¹ * gm * (nu2⁻¹ * nu2) by ring,
      inv_mul_cancel₀ (ne_of_gt hnu2), mul_one]
  have hcstargm : cstar * gm = γ * cm := by
    rw [hcm, show γ * (cstar * γ⁻¹ * gm) = cstar * gm * (γ * γ⁻¹) by ring,
      mul_inv_cancel₀ (ne_of_gt hγ), mul_one]
  have hKγc_lo : cm ≤ cstar * Kγ * gm := by
    have h : cstar * γ⁻¹ * gm ≤ cstar * Kγ * gm := by
      linarith only [mul_nonneg (mul_nonneg hcstar.le hgm)
        (by linarith only [hKγlo] : (0:ℝ) ≤ Kγ - γ⁻¹)]
    rwa [← hcm] at h
  have hKγc_hi : cstar * Kγ * gm ≤ 2 * cm := by
    have h1 : cstar * Kγ * gm ≤ cstar * (γ⁻¹ + 4) * gm := by
      linarith only [mul_nonneg (mul_nonneg hcstar.le hgm)
        (by linarith only [hKγhi] : (0:ℝ) ≤ γ⁻¹ + 4 - Kγ)]
    have h2 : cstar * (γ⁻¹ + 4) * gm = cm + 4 * (cstar * gm) := by rw [hcm]; ring
    rw [h2, hcstargm] at h1
    linarith only [h1,
      mul_nonneg (by linarith only [hγ1] : (0:ℝ) ≤ 1 - 4 * γ) hcmnn]
  have hsm_hi : sm2 - nu2 ≤ 3 * c := by
    have h : sm2 - nu2 ≤ 2 * (β * nu2) + β * (β * nu2) := by linarith only [hup]
    rw [hβc] at h
    linarith only [h, mul_nonneg (by linarith only [hβ1] : (0:ℝ) ≤ 1 - β) hcnn]
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith only [hlo, hKγc_hi, hcmc, hcnn]
  · linarith only [hsm_hi, hKγc_lo, hcmnn, hcnn]


open Real

/-- Elementary lower bound `3^v − 1 ≥ v·log 3` for `v ≥ 0`, from `1 + t ≤ eᵗ`.
Used for the plateau-flavoured drop `G_n(3^{2γh} − 1)`. -/
lemma rpow_ge_one_add (v : ℝ) (_hv : 0 ≤ v) :
    v * Real.log 3 ≤ (3 : ℝ) ^ v - 1 := by
  have hexp : (3 : ℝ) ^ v = Real.exp (v * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]; ring_nf
  rw [hexp]
  have hexpv := Real.add_one_le_exp (v * Real.log 3)
  linarith only [hexpv]

/-- Elementary lower bound `1 − 3^{−u} ≥ (u·log 3)/2` valid whenever
`0 ≤ u·log 3 ≤ 1`. Proof: with `t = u log 3`, `eᵗ ≥ t+1` gives
`3^{−u} = e^{−t} ≤ 1/(t+1)`, hence `1 − 3^{−u} ≥ t/(t+1) ≥ t/2`. Used for the
growth-flavoured drop `G_m(1 − 3^{−2γh})`. -/
lemma one_sub_rpow_neg_ge (u : ℝ) (hu : 0 ≤ u) (hsmall : u * Real.log 3 ≤ 1) :
    (u * Real.log 3) / 2 ≤ 1 - (3 : ℝ) ^ (-u) := by
  set t := u * Real.log 3 with ht
  have htnn : 0 ≤ t := by
    rw [ht]; exact mul_nonneg hu (Real.log_nonneg (by norm_num))
  have hexp : (3 : ℝ) ^ (-u) = Real.exp (-t) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), ht]; ring_nf
  rw [hexp]
  -- e^{-t} ≤ 1/(t+1)
  have hexpt : t + 1 ≤ Real.exp t := by linarith only [Real.add_one_le_exp t]
  have ht1pos : 0 < t + 1 := by linarith only [htnn]
  have hexpinv : Real.exp (-t) ≤ 1 / (t + 1) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le ht1pos hexpt
  -- 1/(t+1) ≤ 1 − t/2, hence t/2 ≤ 1 − 1/(t+1) ≤ 1 − e^{−t}.
  have hfrac : 1 / (t + 1) ≤ 1 - t / 2 := by
    rw [div_le_iff₀ ht1pos]
    linarith only [mul_nonneg htnn (by linarith only [hsmall] : (0:ℝ) ≤ 1 - t)]
  linarith only [hexpinv, hfrac]

/-- **Drop combination.** From the two one-sided drop bounds
`2κδ·ν² ≤ drop` (plateau) and `2κδ·G ≤ drop` (growth), together with the
comparator split `T = ν² + G`, derive the clean drop bound `κδ·T ≤ drop`.
(Uses only `max ≥ average`: a quantity dominating both `a` and `b` dominates
`(a+b)/2`.) -/
lemma drop_combine {κ δ nu2 G T drop : ℝ}
    (hB1 : 2 * κ * δ * nu2 ≤ drop) (hB2 : 2 * κ * δ * G ≤ drop)
    (hT : T = nu2 + G) :
    κ * δ * T ≤ drop := by
  have hexp : κ * δ * T = (2 * κ * δ * nu2) / 2 + (2 * κ * δ * G) / 2 := by
    rw [hT]; ring
  rw [hexp]; linarith only [hB1, hB2]

/-- **Per-step assembly (abstract reals).** The engine of the descent's
`hstep`: the chunk estimate `absval ≤ 6400·E·γ·T_m` (after folding the
quadratic term `≤ E`), the constant identity `E·γ = δ·R`, and the drop bound
`κδ·T_m ≤ T_m − T_n` combine — provided the descent constant satisfies
`6400 ≤ C₀·κ` — into the one-step descent inequality
`absval ≤ C₀·R·(T_m − T_n) = Φ_m − Φ_n`. All `rpow`-bearing quantities enter
only as the opaque scalars `absval, Tm, Tn, E, γ, δ, R`. -/
lemma per_step_algebra {absval Tm Tn E γ δ R C₀ κ : ℝ}
    (hchunk : absval ≤ 6400 * E * γ * Tm)
    (hEγ : E * γ = δ * R)
    (hdrop : κ * δ * Tm ≤ Tm - Tn)
    (hRnn : 0 ≤ R) (hδnn : 0 ≤ δ) (hTmnn : 0 ≤ Tm)
    (hκ : 0 < κ) (hC₀κ : 6400 ≤ C₀ * κ) :
    absval ≤ C₀ * R * (Tm - Tn) := by
  have hC₀pos : 0 < C₀ := by
    by_contra h
    push Not at h
    linarith only [mul_nonpos_of_nonpos_of_nonneg h hκ.le, hC₀κ]
  have hCR : 0 ≤ C₀ * R := mul_nonneg hC₀pos.le hRnn
  -- absval ≤ 6400·(δR)·Tm
  have h1 : absval ≤ 6400 * (δ * R) * Tm := by
    have he : 6400 * E * γ * Tm = 6400 * (δ * R) * Tm := by
      rw [show 6400 * E * γ * Tm = 6400 * (E * γ) * Tm by ring, hEγ]
    linarith only [hchunk, he.ge, he.le]
  -- C₀R·(κδTm) ≤ C₀R·(Tm − Tn)
  have h2 : C₀ * R * (κ * δ * Tm) ≤ C₀ * R * (Tm - Tn) :=
    mul_le_mul_of_nonneg_left hdrop hCR
  -- 6400·(δR)·Tm ≤ C₀R·(κδTm)
  have hδRTm : 0 ≤ δ * R * Tm := mul_nonneg (mul_nonneg hδnn hRnn) hTmnn
  have h3 : 6400 * (δ * R) * Tm ≤ C₀ * R * (κ * δ * Tm) := by
    linarith only [mul_nonneg (by linarith only [hC₀κ] : (0:ℝ) ≤ C₀ * κ - 6400) hδRTm]
  linarith only [h1, h2, h3]


open scoped BigOperators
open Real

variable {ν cstar γ E F : ℝ}

/-- Geometric ratio, integer step form: `3^{2γm} = 3^{2γn}·3^{2γ(m−n)}`. -/
lemma geometricTerm_split (γ : ℝ) (n m : ℤ) :
    geometricTerm γ m = geometricTerm γ n * (3 : ℝ) ^ (2 * γ * ((m : ℝ) - (n : ℝ))) := by
  rw [geometricTerm, geometricTerm, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1; ring

/-- `3^{2γn} = 3^{2γm}·3^{−2γ(m−n)}`. -/
lemma geometricTerm_split_inv (γ : ℝ) (n m : ℤ) :
    geometricTerm γ n = geometricTerm γ m * (3 : ℝ) ^ (-(2 * γ * ((m : ℝ) - (n : ℝ))))
      := by
  rw [geometricTerm, geometricTerm, ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1; ring

/-- Comparator difference in factored form:
`T_m − T_n = c⋆ K_γ (3^{2γm} − 3^{2γn})` for `n ≤ m`. -/
lemma recurrenceComparator_sub_eq_cstar_mul_Kgamma {n m : ℤ} :
    recurrenceComparator ν cstar γ m - recurrenceComparator ν cstar γ n
      = cstar * Stream.Kgamma γ * (geometricTerm γ m - geometricTerm γ n) := by
  rw [recurrenceComparator, recurrenceComparator]
  ring

/-- **Drop bound (Step 3 geometric heart).** For a single adaptive step
`n = m − h` (with `a = m − n` the real step length), the comparator drops by at
least `κδ·T_m` with `κ = log 3 / 18`, provided the step obeys the three
structural bounds:

* `h  `½·δν²c⋆⁻¹3^{−2γm} ≤ a`  — the plateau lower bound on the step;
* `h  `δ ≤ 2γa`  — the growth lower bound on the step;

Proof: split `T_m − T_n = c⋆K_γ(3^{2γm} − 3^{2γn})` into its growth
(`G_m(1 − 3^{−2γh})`) and plateau (`G_n(3^{2γh} − 1)`) factorizations, bound each
via `Growth`/`Plateau`, and fuse with `drop_combine`. -/
lemma drop_bound (hcstar : 0 < cstar) (hγ : 0 < γ)
    {δ : ℝ} (hδpos : 0 < δ) (hδlog : δ * Real.log 3 ≤ 1)
    {n m : ℤ} (hnm : n ≤ m)
    (hF1 : (1 / 2) * (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹) ≤ ((m : ℝ) - (n
      : ℝ)))
    (hF2 : δ ≤ 2 * γ * ((m : ℝ) - (n : ℝ)))
    (hF3 : 2 * γ * ((m : ℝ) - (n : ℝ)) ≤ 2) :
    (Real.log 3 / 18) * δ * recurrenceComparator ν cstar γ m ≤ recurrenceComparator ν
      cstar γ m - recurrenceComparator ν cstar γ n := by
  have hgm : 0 < geometricTerm γ m := geometricTerm_pos γ m
  have hgn : 0 < geometricTerm γ n := geometricTerm_pos γ n
  have hKγ0 : 0 ≤ Stream.Kgamma γ := le_trans (inv_pos.mpr hγ).le (Stream.le_Kgamma hγ)
  have hγKγ : 1 ≤ γ * Stream.Kgamma γ := by
    have h := mul_le_mul_of_nonneg_left (Stream.le_Kgamma hγ) hγ.le
    rwa [mul_inv_cancel₀ (ne_of_gt hγ)] at h
  have ha_nn : 0 ≤ (m : ℝ) - (n : ℝ) := by
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith only [hnm']
  have hsplit : geometricTerm γ m = geometricTerm γ n * (3 : ℝ) ^ (2 * γ * ((m : ℝ) - (n
    : ℝ))) :=
    geometricTerm_split γ n m
  have hsplit_inv : geometricTerm γ n
      = geometricTerm γ m * (3 : ℝ) ^ (-(2 * γ * ((m : ℝ) - (n : ℝ)))) :=
    geometricTerm_split_inv γ n m
  -- 3^{-2} = 1/9
  have h19 : (3 : ℝ) ^ (-2 : ℝ) = 1 / 9 := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  -- growth side: (δ log3)/2 ≤ 1 − 3^{-2γa}
  have hmono : (3 : ℝ) ^ (-(2 * γ * ((m : ℝ) - (n : ℝ)))) ≤ (3 : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hF2])
  have helem := one_sub_rpow_neg_ge δ hδpos.le hδlog
  have h1mq : (δ * Real.log 3) / 2 ≤ 1 - (3 : ℝ) ^ (-(2 * γ * ((m : ℝ) - (n : ℝ)))) := by
    linarith only [hmono, helem]
  -- plateau side: 1/9 ≤ 3^{-2γa}, and 2γa·log3 ≤ 3^{2γa} − 1
  have hq : (1 : ℝ) / 9 ≤ (3 : ℝ) ^ (-(2 * γ * ((m : ℝ) - (n : ℝ)))) := by
    rw [← h19]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hF3])
  have hr : (2 * γ * ((m : ℝ) - (n : ℝ))) * Real.log 3
      ≤ (3 : ℝ) ^ (2 * γ * ((m : ℝ) - (n : ℝ))) - 1 :=
    rpow_ge_one_add _ (mul_nonneg (mul_nonneg (by norm_num) hγ.le) ha_nn)
  -- adaptive-step lower bound in product form
  have ha_ineq : γ * δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹
      ≤ 2 * γ * ((m : ℝ) - (n : ℝ)) := by
    have h2γ : (0 : ℝ) ≤ 2 * γ := mul_nonneg (by norm_num) hγ.le
    calc γ * δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹
        = 2 * γ * ((1 / 2) * (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹)) := by ring
      _ ≤ 2 * γ * ((m : ℝ) - (n : ℝ)) := mul_le_mul_of_nonneg_left hF1 h2γ
  -- comparator difference, two factorizations
  have hdrop_B2 : recurrenceComparator ν cstar γ m - recurrenceComparator ν cstar γ n
      = (cstar * Stream.Kgamma γ * geometricTerm γ m)
        * (1 - (3 : ℝ) ^ (-(2 * γ * ((m : ℝ) - (n : ℝ))))) := by
    rw [recurrenceComparator_sub_eq_cstar_mul_Kgamma, hsplit_inv]
    ring
  have hdrop_B1 : recurrenceComparator ν cstar γ m - recurrenceComparator ν cstar γ n
      = (cstar * Stream.Kgamma γ * geometricTerm γ n)
        * ((3 : ℝ) ^ (2 * γ * ((m : ℝ) - (n : ℝ))) - 1) := by
    rw [recurrenceComparator_sub_eq_cstar_mul_Kgamma, hsplit]
    ring
  -- assemble the two one-sided drop bounds
  have hGm_nn : 0 ≤ cstar * Stream.Kgamma γ * geometricTerm γ m :=
    mul_nonneg (mul_nonneg hcstar.le hKγ0) hgm.le
  have hGn_nn : 0 ≤ cstar * Stream.Kgamma γ * geometricTerm γ n :=
    mul_nonneg (mul_nonneg hcstar.le hKγ0) hgn.le
  have hB2 : 2 * (Real.log 3 / 18) * δ * (cstar * Stream.Kgamma γ * geometricTerm γ m)
      ≤ recurrenceComparator ν cstar γ m - recurrenceComparator ν cstar γ n := by
    rw [hdrop_B2]; exact growth_side hGm_nn hδpos.le rfl h1mq
  have hb_prod : 2 * (Real.log 3 / 18) * δ * ν ^ 2
      ≤ (cstar * Stream.Kgamma γ * geometricTerm γ n)
        * (2 * γ * ((m : ℝ) - (n : ℝ)) * Real.log 3) :=
    plateau_product hsplit_inv hq hgm hγ ha_ineq hγKγ hcstar hδpos.le (sq_nonneg ν) hKγ0 rfl
  have hB1 : 2 * (Real.log 3 / 18) * δ * ν ^ 2 ≤ recurrenceComparator ν cstar γ m -
    recurrenceComparator ν cstar γ n := by
    rw [hdrop_B1]; exact plateau_side hGn_nn hb_prod hr
  have hTm_split : recurrenceComparator ν cstar γ m = ν ^ 2 + cstar * Stream.Kgamma γ *
    geometricTerm γ m := by rw [recurrenceComparator]
  exact drop_combine hB1 hB2 hTm_split

/-! ### Floor and threshold helpers -/

/-- `⌊x⌋ ≥ x/2` when `x ≥ 2`. -/
lemma floor_ge_half {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋ : ℝ) := by
  have h := Int.sub_one_lt_floor x
  linarith only [h, hx]

/-- `⌊x⌋ ≥ 1` when `x ≥ 2`. -/
lemma one_le_floor {x : ℝ} (hx : 2 ≤ x) : (1 : ℤ) ≤ ⌊x⌋ := by
  have : (1 : ℤ) ≤ ⌊(2 : ℝ)⌋ := by norm_num
  exact le_trans this (Int.floor_le_floor hx)

/-- `3^{2γk} ≤ B` from `2γk·log 3 ≤ log B` (for `B > 0`). -/
lemma geometricTerm_le_of_log_le {γ : ℝ} {B : ℝ} (hB : 0 < B) {k : ℤ}
    (hk : 2 * γ * (k : ℝ) * Real.log 3 ≤ Real.log B) : geometricTerm γ k ≤ B := by
  rw [geometricTerm, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3), ← Real.exp_log hB]
  apply Real.exp_le_exp.mpr
  calc Real.log 3 * (2 * γ * (k : ℝ)) = 2 * γ * (k : ℝ) * Real.log 3 := by ring
    _ ≤ Real.log B := hk

/-- `B < 3^{2γk}` from `log B < 2γk·log 3` (for `B > 0`). -/
lemma lt_geometricTerm_of_log_lt {γ : ℝ} {B : ℝ} (hB : 0 < B) {k : ℤ}
    (hk : Real.log B < 2 * γ * (k : ℝ) * Real.log 3) : B < geometricTerm γ k := by
  rw [geometricTerm, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3),
    show B = Real.exp (Real.log B) from (Real.exp_log hB).symm]
  apply Real.exp_lt_exp.mpr
  calc Real.log B < 2 * γ * (k : ℝ) * Real.log 3 := hk
    _ = Real.log 3 * (2 * γ * (k : ℝ)) := by ring

/-! ### The adaptive step size `δγ⁻¹μ(m)⁻¹` and its bounds -/

/-- The ideal (real) adaptive step `δγ⁻¹μ(m)⁻¹`, written in max form
`max{δν²c⋆⁻¹3^{−2γm}, δγ⁻¹}`. The chosen step is its floor. -/
noncomputable def adaptStep (δ ν cstar γ : ℝ) (m : ℤ) : ℝ :=
  max (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹) (δ * γ⁻¹)

/-- `adaptStep ≥ 2` from the smallness `δγ⁻¹ ≥ 2`. -/
lemma two_le_adaptStep {δ : ℝ} (hδγ2 : 2 ≤ δ * γ⁻¹) (m : ℤ) :
    2 ≤ adaptStep δ ν cstar γ m :=
  le_trans hδγ2 (le_max_right _ _)

/-- The adaptive step never exceeds `cγ⁻¹` for a *capped* scale `c`, provided
`δ ≤ c` and `3^{2γm} ≥ δν²γ(c⋆c)⁻¹` (the `mc`-threshold, valid for `m > mc`).

Taking `c = min{c⋆, 1}` this yields simultaneously the chunk-range bound `a ≤
c⋆γ⁻¹` (needed to invoke the two recurrence hypotheses) and the unit-range
bound `a ≤ γ⁻¹` (needed for `3^{2γ(m−n)} ≤ 9`), with **no** upper bound assumed
on `c⋆` itself. -/
lemma adaptStep_le_cap (hν : 0 < ν) (hcstar : 0 < cstar) (hγ : 0 < γ)
    {δ cbar : ℝ} (hδpos : 0 < δ) (hcbar : 0 < cbar) (hδcbar : δ ≤ cbar)
    {m : ℤ} (hgm_lb : δ * ν ^ 2 * γ * (cstar * cbar)⁻¹ ≤ geometricTerm γ m) :
    adaptStep δ ν cstar γ m ≤ cbar * γ⁻¹ := by
  have hgm : 0 < geometricTerm γ m := geometricTerm_pos γ m
  have hνne : ν ≠ 0 := ne_of_gt hν
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hγne : γ ≠ 0 := ne_of_gt hγ
  have hcne : cstar ≠ 0 := ne_of_gt hcstar
  have hbne : cbar ≠ 0 := ne_of_gt hcbar
  have hBbpos : 0 < δ * ν ^ 2 * γ * (cstar * cbar)⁻¹ := by
    have : (0:ℝ) < (cstar * cbar)⁻¹ := by positivity
    have h2 : (0:ℝ) < δ * ν ^ 2 * γ := by positivity
    positivity
  refine max_le ?_ ?_
  · -- first arg: δν²c⋆⁻¹g_m⁻¹ ≤ cγ⁻¹
    have hinv : (geometricTerm γ m)⁻¹ ≤ (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)⁻¹ := by
      have h := one_div_le_one_div_of_le hBbpos hgm_lb
      rwa [← inv_eq_one_div, ← inv_eq_one_div] at h
    have hid : δ * ν ^ 2 * cstar⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)⁻¹ = cbar *
      γ⁻¹ := by
      field_simp
    calc δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹
        ≤ δ * ν ^ 2 * cstar⁻¹ * (δ * ν ^ 2 * γ * (cstar * cbar)⁻¹)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = cbar * γ⁻¹ := hid
  · -- second arg: δγ⁻¹ ≤ cγ⁻¹
    exact mul_le_mul_of_nonneg_right hδcbar (inv_nonneg.mpr hγ.le)

/-- Key quadratic-term control: `μ(m)·adaptStep ≤ δγ⁻¹`, where
`μ(m) = min{ν⁻²c⋆γ⁻¹3^{2γm}, 1}`. (In fact equality holds.) -/
lemma mu_mul_adaptStep_le (hν : 0 < ν) (hcstar : 0 < cstar) (hγ : 0 < γ)
    {δ : ℝ} (hδpos : 0 < δ) (m : ℤ) :
    (min ((ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ m) 1) * adaptStep δ ν cstar γ m
      ≤ δ * γ⁻¹ := by
  have hgm : 0 < geometricTerm γ m := geometricTerm_pos γ m
  set w : ℝ := (ν ^ 2)⁻¹ * cstar * γ⁻¹ * geometricTerm γ m with hw
  have hwpos : 0 < w := by rw [hw]; positivity
  have hμnn : 0 ≤ min w 1 := le_min hwpos.le (by norm_num)
  rw [adaptStep]
  rcases le_or_gt (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹) (δ * γ⁻¹) with
    hcase | hcase
  · rw [max_eq_right hcase]
    calc min w 1 * (δ * γ⁻¹) ≤ 1 * (δ * γ⁻¹) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = δ * γ⁻¹ := by ring
  · rw [max_eq_left hcase.le]
    have hwid : w * (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹) = δ * γ⁻¹ := by
      rw [hw]; field_simp
    calc min w 1 * (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹)
        ≤ w * (δ * ν ^ 2 * cstar⁻¹ * (geometricTerm γ m)⁻¹) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = δ * γ⁻¹ := hwid


/-- **Abstract descent, bounded above by `m₀`.** Same as `bound_by_descent`,
but the strict-descent and one-step hypotheses need only hold on
`(mc, m₀]`, and the conclusion is drawn only for `m ≤ m₀`. This is the form
used at the call site, where the chunk estimate requires the upper endpoint to
satisfy `m ≤ m₀`. -/
theorem bound_by_descent_le {mc m₀ : ℤ} {Φ dd : ℤ → ℝ} (nn : ℤ → ℤ)
    (hbase : ∀ m : ℤ, m ≤ mc → |dd m| ≤ Φ m)
    (hlt : ∀ m : ℤ, mc < m → m ≤ m₀ → nn m < m)
    (hstep : ∀ m : ℤ, mc < m → m ≤ m₀ → |dd (nn m)| ≤ Φ (nn m) →
      |dd m - dd (nn m)| ≤ Φ m - Φ (nn m)) :
    ∀ m : ℤ, m ≤ m₀ → |dd m| ≤ Φ m := by
  suffices H : ∀ k : ℕ, ∀ m : ℤ, m ≤ m₀ → (m - mc).toNat ≤ k → |dd m| ≤ Φ m by
    intro m hm; exact H (m - mc).toNat m hm le_rfl
  intro k
  induction k with
  | zero => intro m _ hm; exact hbase m (by omega)
  | succ k ih =>
      intro m hmm₀ hm
      by_cases hle : m ≤ mc
      · exact hbase m hle
      · push Not at hle
        have hnn_lt : nn m < m := hlt m hle hmm₀
        have hdepth : (nn m - mc).toNat ≤ k := by omega
        have hlow : |dd (nn m)| ≤ Φ (nn m) := ih (nn m) (by omega) hdepth
        have hincr : |dd m - dd (nn m)| ≤ Φ m - Φ (nn m) := hstep m hle hmm₀ hlow
        have htri : |dd m| ≤ |dd m - dd (nn m)| + |dd (nn m)| := by
          have h := abs_sub_le (dd m) (dd (nn m)) 0
          simpa using h
        linarith only [htri, hlow, hincr]


end Internal

end

end Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
