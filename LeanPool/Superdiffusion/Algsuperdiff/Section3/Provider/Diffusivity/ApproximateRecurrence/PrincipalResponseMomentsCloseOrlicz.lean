/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Basic

/-!
# PrincipalResponseMomentsCloseOrlicz

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the eighth moment of a shifted three-lane weak-Orlicz bound

This module is the `p = 8` analogue of the `p = 2` engine
`integral_sq_le_of_isTwoTermBigOWith_gammaSigma`
(`PrincipalResponseBudgetMoment.lean`).  What it proves is the elementary
probabilistic fact that a nonnegative random variable dominated by a
deterministic shift plus three stretched-exponential lanes,

```
  0 <= X <= b + Y_1 + Y_2 + Y_3 ,   Y_i = O_{Gamma_{sigma_i}}(A_i) ,
```

has eighth moment inside `(4 (b + sum_i c(sigma_i) A_i))^8`, with `c(sigma) =
gammaMomentConst sigma * 8^{1/sigma}` the class constant supplied by
CoarseGraining's layer-cake bound `integral_rpow_le_of_isBigOWith_gammaSigma`
at `p = 8`.

## Why three lanes and a shift

The consumer is the second inequality of the moment display at ABK26.  Its
integrand is a *sum of two* multiscale ellipticity endpoints, each of which the
coarse-graining ellipticity proposition controls by a deterministic profile plus
weak-Orlicz lanes: two lanes for the upper endpoint (the deterministic-shift
two-term one-sided form) and one lane, uniform in the family index, for the
lower endpoint.  Adding the two endpoints gives exactly one shift and three
lanes.

## How the witnesses are handled

The lane witnesses are not assumed nonnegative, so, exactly as at `p = 2`, the
layer-cake moment bound is applied to the positive parts `max(Y_i, 0)`, which
carry the same one-sided upper tails because the tail threshold `A t` is
positive for `t >= 1` and `A > 0`.  The passage from
`X <= b + sum_i max(Y_i,0)` to the eighth moment then uses only the crude
elementary inequality `(u+v)^8 <= 256 (u^8 + v^8)` twice, which is why the
final envelope carries the harmless factor `4`.  No sharp Minkowski constant is
attempted: every consumer's constant is a free dimensional constant.

## Portability

This file imports **only** Mathlib and `Homogenization.*`.  It mentions no
ABK26 object: no model, no cutoff law, no cube, no scale and no anchor.  It is
therefore a candidate for relocation into CoarseGraining beside the `p`-th
moment layer-cake bound it consumes.

## Main results

* `orliczEighthMomentScale`, `orliczEighthMomentScale_pos`: the class constant
  at `p = 8`.
* `integral_rpow_eight_le_of_shift_add_three_orlicz`: **`MemLp` at exponent
  `8` together with the eighth moment bound**.  The membership travels with the
  bound because Mathlib's Bochner integral is `0` off the integrable locus, so
  the bound alone constrains nothing.
* `orliczSecondMomentScale`, `orliczSecondMomentScale_pos`: the class constant
  at `p = 2`.
* `integral_rpow_two_le_of_shift_add_one_orlicz`: the **one-lane shifted second
  moment**.  The two-lane engine
  `PrincipalResponseBudgetMoment.integral_sq_le_of_isTwoTermBigOWith_gammaSigma`
  cannot consume a single-lane observable carrying a deterministic shift (it has
  no shift and needs two admissible tails), which is the shape produced by the
  fresh-shell `L^8` gradient bound; this supplies exactly that shape.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-! ## Elementary eighth powers -/

private theorem rpow_eight_eq_pow (y : ℝ) : y ^ (8 : ℝ) = y ^ (8 : ℕ) := by
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem pow_eight_add_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a + c) ^ (8 : ℕ) ≤ 256 * (a ^ (8 : ℕ) + c ^ (8 : ℕ)) := by
  rcases le_total a c with h | h
  · have hle : (a + c) ^ (8 : ℕ) ≤ (2 * c) ^ (8 : ℕ) := by
      have h1 : a + c ≤ 2 * c := by linarith
      have h0 : (0 : ℝ) ≤ a + c := by linarith
      exact pow_le_pow_left₀ h0 h1 8
    have heq : (2 * c) ^ (8 : ℕ) = 256 * c ^ (8 : ℕ) := by
      rw [mul_pow]; norm_num
    have hnn : (0 : ℝ) ≤ a ^ (8 : ℕ) := pow_nonneg ha 8
    calc (a + c) ^ (8 : ℕ) ≤ (2 * c) ^ (8 : ℕ) := hle
      _ = 256 * c ^ (8 : ℕ) := heq
      _ ≤ 256 * (a ^ (8 : ℕ) + c ^ (8 : ℕ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hnn) (by norm_num)
  · have hle : (a + c) ^ (8 : ℕ) ≤ (2 * a) ^ (8 : ℕ) := by
      have h1 : a + c ≤ 2 * a := by linarith
      have h0 : (0 : ℝ) ≤ a + c := by linarith
      exact pow_le_pow_left₀ h0 h1 8
    have heq : (2 * a) ^ (8 : ℕ) = 256 * a ^ (8 : ℕ) := by
      rw [mul_pow]; norm_num
    have hnn : (0 : ℝ) ≤ c ^ (8 : ℕ) := pow_nonneg hc 8
    calc (a + c) ^ (8 : ℕ) ≤ (2 * a) ^ (8 : ℕ) := hle
      _ = 256 * a ^ (8 : ℕ) := heq
      _ ≤ 256 * (a ^ (8 : ℕ) + c ^ (8 : ℕ)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnn) (by norm_num)

private theorem pow_eight_add_four_le {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) :
    (a + b + c + e) ^ (8 : ℕ) ≤
      65536 * (a ^ (8 : ℕ) + b ^ (8 : ℕ) + c ^ (8 : ℕ) + e ^ (8 : ℕ)) := by
  have hsplit : a + b + c + e = (a + b) + (c + e) := by ring
  rw [hsplit]
  have h2 := pow_eight_add_le (a := a + b) (c := c + e) (by linarith) (by linarith)
  have h3 := pow_eight_add_le ha hb
  have h4 := pow_eight_add_le hc he
  calc (a + b + (c + e)) ^ (8 : ℕ)
      ≤ 256 * ((a + b) ^ (8 : ℕ) + (c + e) ^ (8 : ℕ)) := h2
    _ ≤ 256 * (256 * (a ^ (8 : ℕ) + b ^ (8 : ℕ)) +
        256 * (c ^ (8 : ℕ) + e ^ (8 : ℕ))) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h4) (by norm_num)
    _ = 65536 * (a ^ (8 : ℕ) + b ^ (8 : ℕ) + c ^ (8 : ℕ) + e ^ (8 : ℕ)) := by
        ring

private theorem pow_eight_sum_four_le {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) :
    a ^ (8 : ℕ) + b ^ (8 : ℕ) + c ^ (8 : ℕ) + e ^ (8 : ℕ) ≤
      (a + b + c + e) ^ (8 : ℕ) := by
  have h1 : a ^ (8 : ℕ) + b ^ (8 : ℕ) ≤ (a + b) ^ (8 : ℕ) :=
    pow_add_pow_le ha hb (by norm_num)
  have h2 : (a + b) ^ (8 : ℕ) + c ^ (8 : ℕ) ≤ (a + b + c) ^ (8 : ℕ) :=
    pow_add_pow_le (by linarith) hc (by norm_num)
  have h3 : (a + b + c) ^ (8 : ℕ) + e ^ (8 : ℕ) ≤ (a + b + c + e) ^ (8 : ℕ) :=
    pow_add_pow_le (by linarith) he (by norm_num)
  calc a ^ (8 : ℕ) + b ^ (8 : ℕ) + c ^ (8 : ℕ) + e ^ (8 : ℕ)
      ≤ (a + b) ^ (8 : ℕ) + c ^ (8 : ℕ) + e ^ (8 : ℕ) :=
        add_le_add (add_le_add h1 le_rfl) le_rfl
    _ ≤ (a + b + c) ^ (8 : ℕ) + e ^ (8 : ℕ) := add_le_add h2 le_rfl
    _ ≤ (a + b + c + e) ^ (8 : ℕ) := h3

/-! ## The class constant at `p = 8` -/

/-- The eighth-moment scale of the stretched-exponential class `Gamma_sigma`:
a variable which is `O_{Gamma_sigma}(A)` has eighth moment at most
`(orliczEighthMomentScale sigma * A)^8`.  It depends on nothing but `sigma`. -/
def orliczEighthMomentScale (sigma : ℝ) : ℝ :=
  IndependentSums.gammaMomentConst sigma * (8 : ℝ) ^ sigma⁻¹

theorem orliczEighthMomentScale_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < orliczEighthMomentScale sigma :=
  mul_pos (IndependentSums.gammaMomentConst_pos hsigma)
    (Real.rpow_pos_of_pos (by norm_num) _)

/-! ## Positive parts -/

/-- The positive part of a variable with a one-sided weak-Orlicz upper tail has
the same tail, the threshold `A t` being positive for `t >= 1`. -/
private theorem isBigOWith_max_zero {mu : Measure Omega} {Psi : ℝ → ℝ}
    {X : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hX : IndependentSums.IsBigOWith mu Psi X A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => max (X omega) 0) A := by
  intro t ht
  have hAt : (0 : ℝ) < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hset :
      IndependentSums.upperTailEvent (fun omega => max (X omega) 0) (A * t) =
        IndependentSums.upperTailEvent X (A * t) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, lt_max_iff]
    constructor
    · rintro (hlt | hlt)
      · exact hlt
      · exact absurd hlt (not_lt.2 hAt.le)
    · exact fun hlt => Or.inl hlt
  rw [hset]
  exact hX ht

variable {mu : Measure Omega} [IsProbabilityMeasure mu]

private theorem integral_pow_eight_max_zero_le {Y : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hYm : Measurable Y)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    ∫ omega, max (Y omega) 0 ^ (8 : ℕ) ∂mu ≤
      (orliczEighthMomentScale sigma * A) ^ (8 : ℕ) := by
  have h := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (p := (8 : ℝ)) hsigma hA (by norm_num) (fun omega => le_max_right _ _)
    (hYm.max measurable_const).aemeasurable (isBigOWith_max_zero hA hY)
  simpa only [rpow_eight_eq_pow, orliczEighthMomentScale] using h

omit [IsProbabilityMeasure mu] in
/-- `MemLp` at exponent `8` from an integrable eighth-power majorant.  Mathlib's
Bochner integral is `0` off the integrable locus, so a bound on `∫ X ^ 8` says
nothing on its own; this is what turns the majorant that produces the bound into
the membership its consumers need. -/
private theorem memLp_eight_of_integrable_majorant {X g : Omega → ℝ}
    (hXm : AEStronglyMeasurable X mu) (hX0 : ∀ omega, 0 ≤ X omega)
    (hg : Integrable g mu)
    (hpoint : ∀ omega, X omega ^ (8 : ℕ) ≤ g omega) :
    MemLp X 8 mu := by
  have hXpow : Integrable (fun omega => X omega ^ (8 : ℕ)) mu := by
    refine hg.mono' (hXm.pow 8) (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX0 omega) 8)]
    exact hpoint omega
  refine (integrable_norm_rpow_iff hXm (by norm_num) (by norm_num)).mp ?_
  have hconv : (fun omega => ‖X omega‖ ^ (8 : ENNReal).toReal) =
      fun omega => X omega ^ (8 : ℕ) := by
    funext omega
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 omega)]
    rw [show (8 : ENNReal).toReal = (8 : ℝ) by norm_num]
    exact rpow_eight_eq_pow _
  rw [hconv]
  exact hXpow

private theorem integrable_pow_eight_max_zero {Y : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hYm : Measurable Y)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    Integrable (fun omega => max (Y omega) 0 ^ (8 : ℕ)) mu := by
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (p := (8 : ℝ)) hsigma hA (by norm_num) (fun omega => le_max_right _ _)
    (hYm.max measurable_const).aemeasurable (isBigOWith_max_zero hA hY)
  simpa only [rpow_eight_eq_pow] using h

/-! ## The eighth moment of a shifted three-lane weak-Orlicz bound -/

/-- **The eighth-moment engine.**

A nonnegative random variable dominated by a deterministic shift `b` plus three
one-sided stretched-exponential lanes has eighth moment inside
`(4 (b + sum_i c(sigma_i) A_i))^8`, where `c = orliczEighthMomentScale`.

The lane witnesses `Y_1, Y_2, Y_3` need not be nonnegative: only their upper
tails are used, through their positive parts. -/
theorem integral_rpow_eight_le_of_shift_add_three_orlicz
    {X Y1 Y2 Y3 : Omega → ℝ} {b A1 A2 A3 s1 s2 s3 : ℝ}
    (hs1 : 0 < s1) (hs2 : 0 < s2) (hs3 : 0 < s3)
    (hA1 : 0 < A1) (hA2 : 0 < A2) (hA3 : 0 < A3) (hb : 0 ≤ b)
    (hY1m : Measurable Y1) (hY2m : Measurable Y2) (hY3m : Measurable Y3)
    (hT1 : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma s1) Y1 A1)
    (hT2 : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma s2) Y2 A2)
    (hT3 : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma s3) Y3 A3)
    (hXm : AEStronglyMeasurable X mu)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (hdom : ∀ omega, X omega ≤ b + Y1 omega + Y2 omega + Y3 omega) :
    MemLp X 8 mu ∧
      ∫ omega, X omega ^ (8 : ℝ) ∂mu ≤
        (4 * (b + orliczEighthMomentScale s1 * A1 +
          orliczEighthMomentScale s2 * A2 +
          orliczEighthMomentScale s3 * A3)) ^ (8 : ℝ) := by
  set v1 : ℝ := orliczEighthMomentScale s1 * A1 with hv1
  set v2 : ℝ := orliczEighthMomentScale s2 * A2 with hv2
  set v3 : ℝ := orliczEighthMomentScale s3 * A3 with hv3
  have hv1nn : 0 ≤ v1 := by
    rw [hv1]; exact mul_nonneg (orliczEighthMomentScale_pos hs1).le hA1.le
  have hv2nn : 0 ≤ v2 := by
    rw [hv2]; exact mul_nonneg (orliczEighthMomentScale_pos hs2).le hA2.le
  have hv3nn : 0 ≤ v3 := by
    rw [hv3]; exact mul_nonneg (orliczEighthMomentScale_pos hs3).le hA3.le
  have hI1 := integrable_pow_eight_max_zero hs1 hA1 hY1m hT1
  have hI2 := integrable_pow_eight_max_zero hs2 hA2 hY2m hT2
  have hI3 := integrable_pow_eight_max_zero hs3 hA3 hY3m hT3
  have hM1 := integral_pow_eight_max_zero_le hs1 hA1 hY1m hT1
  have hM2 := integral_pow_eight_max_zero_le hs2 hA2 hY2m hT2
  have hM3 := integral_pow_eight_max_zero_le hs3 hA3 hY3m hT3
  have hpoint : ∀ omega, X omega ^ (8 : ℕ) ≤
      65536 * (b ^ (8 : ℕ) + max (Y1 omega) 0 ^ (8 : ℕ) +
        max (Y2 omega) 0 ^ (8 : ℕ) + max (Y3 omega) 0 ^ (8 : ℕ)) := by
    intro omega
    have hle : X omega ≤
        b + max (Y1 omega) 0 + max (Y2 omega) 0 + max (Y3 omega) 0 := by
      have h1 : Y1 omega ≤ max (Y1 omega) 0 := le_max_left _ _
      have h2 : Y2 omega ≤ max (Y2 omega) 0 := le_max_left _ _
      have h3 : Y3 omega ≤ max (Y3 omega) 0 := le_max_left _ _
      have := hdom omega
      linarith
    have hpow : X omega ^ (8 : ℕ) ≤
        (b + max (Y1 omega) 0 + max (Y2 omega) 0 + max (Y3 omega) 0) ^ (8 : ℕ) := by
      have h0 := hX0 omega
      exact pow_le_pow_left₀ h0 hle 8
    exact hpow.trans
      (pow_eight_add_four_le hb (le_max_right _ _) (le_max_right _ _)
        (le_max_right _ _))
  have hmaj : Integrable (fun omega =>
      65536 * (b ^ (8 : ℕ) + max (Y1 omega) 0 ^ (8 : ℕ) +
        max (Y2 omega) 0 ^ (8 : ℕ) + max (Y3 omega) 0 ^ (8 : ℕ))) mu :=
    ((((integrable_const (b ^ (8 : ℕ))).add hI1).add hI2).add hI3).const_mul _
  refine ⟨memLp_eight_of_integrable_majorant hXm hX0 hmaj hpoint, ?_⟩
  have hstep : ∫ omega, X omega ^ (8 : ℕ) ∂mu ≤
      ∫ omega, 65536 * (b ^ (8 : ℕ) + max (Y1 omega) 0 ^ (8 : ℕ) +
        max (Y2 omega) 0 ^ (8 : ℕ) + max (Y3 omega) 0 ^ (8 : ℕ)) ∂mu :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega => pow_nonneg (hX0 omega) 8) hmaj
      (Filter.Eventually.of_forall hpoint)
  have hsplit : ∫ omega, 65536 * (b ^ (8 : ℕ) + max (Y1 omega) 0 ^ (8 : ℕ) +
        max (Y2 omega) 0 ^ (8 : ℕ) + max (Y3 omega) 0 ^ (8 : ℕ)) ∂mu =
      65536 * (b ^ (8 : ℕ) + (∫ omega, max (Y1 omega) 0 ^ (8 : ℕ) ∂mu) +
        (∫ omega, max (Y2 omega) 0 ^ (8 : ℕ) ∂mu) +
        ∫ omega, max (Y3 omega) 0 ^ (8 : ℕ) ∂mu) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_add
        (f := fun a => b ^ (8 : ℕ) + max (Y1 a) 0 ^ (8 : ℕ) + max (Y2 a) 0 ^ (8 : ℕ))
        (g := fun a => max (Y3 a) 0 ^ (8 : ℕ))
        (((integrable_const (b ^ (8 : ℕ))).add hI1).add hI2) hI3,
      integral_add
        (f := fun a => b ^ (8 : ℕ) + max (Y1 a) 0 ^ (8 : ℕ))
        (g := fun a => max (Y2 a) 0 ^ (8 : ℕ))
        ((integrable_const (b ^ (8 : ℕ))).add hI1) hI2,
      integral_add
        (f := fun _ => b ^ (8 : ℕ)) (g := fun a => max (Y1 a) 0 ^ (8 : ℕ))
        (integrable_const (b ^ (8 : ℕ))) hI1,
      integral_const]
    simp
  have hsum : b ^ (8 : ℕ) + (∫ omega, max (Y1 omega) 0 ^ (8 : ℕ) ∂mu) +
        (∫ omega, max (Y2 omega) 0 ^ (8 : ℕ) ∂mu) +
        ∫ omega, max (Y3 omega) 0 ^ (8 : ℕ) ∂mu ≤
      (b + v1 + v2 + v3) ^ (8 : ℕ) := by
    have h := pow_eight_sum_four_le hb hv1nn hv2nn hv3nn
    calc b ^ (8 : ℕ) + (∫ omega, max (Y1 omega) 0 ^ (8 : ℕ) ∂mu) +
          (∫ omega, max (Y2 omega) 0 ^ (8 : ℕ) ∂mu) +
          ∫ omega, max (Y3 omega) 0 ^ (8 : ℕ) ∂mu
        ≤ b ^ (8 : ℕ) + v1 ^ (8 : ℕ) + v2 ^ (8 : ℕ) + v3 ^ (8 : ℕ) :=
          add_le_add (add_le_add (add_le_add le_rfl hM1) hM2) hM3
      _ ≤ (b + v1 + v2 + v3) ^ (8 : ℕ) := h
  have hfinal : ∫ omega, X omega ^ (8 : ℕ) ∂mu ≤
      (4 * (b + v1 + v2 + v3)) ^ (8 : ℕ) := by
    have hexp : (4 * (b + v1 + v2 + v3)) ^ (8 : ℕ) =
        65536 * (b + v1 + v2 + v3) ^ (8 : ℕ) := by
      rw [mul_pow]; norm_num
    rw [hsplit] at hstep
    rw [hexp]
    calc ∫ omega, X omega ^ (8 : ℕ) ∂mu
        ≤ 65536 * (b ^ (8 : ℕ) + (∫ omega, max (Y1 omega) 0 ^ (8 : ℕ) ∂mu) +
            (∫ omega, max (Y2 omega) 0 ^ (8 : ℕ) ∂mu) +
            ∫ omega, max (Y3 omega) 0 ^ (8 : ℕ) ∂mu) := hstep
      _ ≤ 65536 * (b + v1 + v2 + v3) ^ (8 : ℕ) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
  simpa only [rpow_eight_eq_pow] using hfinal

/-! ## The one-lane shifted second moment -/

private theorem rpow_two_eq_pow (y : ℝ) : y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem pow_two_add_le (a c : ℝ) :
    (a + c) ^ (2 : ℕ) ≤ 4 * (a ^ (2 : ℕ) + c ^ (2 : ℕ)) := by
  nlinarith [sq_nonneg (a - c), sq_nonneg a, sq_nonneg c]

/-- The second-moment scale of the stretched-exponential class `Gamma_sigma`. -/
def orliczSecondMomentScale (sigma : ℝ) : ℝ :=
  IndependentSums.gammaMomentConst sigma * (2 : ℝ) ^ sigma⁻¹

theorem orliczSecondMomentScale_pos {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < orliczSecondMomentScale sigma :=
  mul_pos (IndependentSums.gammaMomentConst_pos hsigma)
    (Real.rpow_pos_of_pos (by norm_num) _)

private theorem integral_pow_two_max_zero_le {Y : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hYm : Measurable Y)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    ∫ omega, max (Y omega) 0 ^ (2 : ℕ) ∂mu ≤
      (orliczSecondMomentScale sigma * A) ^ (2 : ℕ) := by
  have h := IndependentSums.integral_rpow_le_of_isBigOWith_gammaSigma
    (p := (2 : ℝ)) hsigma hA (by norm_num) (fun omega => le_max_right _ _)
    (hYm.max measurable_const).aemeasurable (isBigOWith_max_zero hA hY)
  simpa only [rpow_two_eq_pow, orliczSecondMomentScale] using h

private theorem integrable_pow_two_max_zero {Y : Omega → ℝ} {A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hYm : Measurable Y)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    Integrable (fun omega => max (Y omega) 0 ^ (2 : ℕ)) mu := by
  have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
    (p := (2 : ℝ)) hsigma hA (by norm_num) (fun omega => le_max_right _ _)
    (hYm.max measurable_const).aemeasurable (isBigOWith_max_zero hA hY)
  simpa only [rpow_two_eq_pow] using h

/-- **The one-lane shifted second moment.**

A nonnegative random variable dominated by a deterministic shift `b` plus a
single one-sided stretched-exponential lane has second moment inside
`(2 (b + c(sigma) A))^2`, with `c = orliczSecondMomentScale`.

The lane witness `Y` need not be nonnegative: only its upper tail is used. -/
theorem integral_rpow_two_le_of_shift_add_one_orlicz
    {X Y : Omega → ℝ} {b A sigma : ℝ} (hsigma : 0 < sigma) (hA : 0 < A) (hb : 0 ≤ b)
    (hYm : Measurable Y)
    (hT : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A)
    (hX0 : ∀ omega, 0 ≤ X omega)
    (hdom : ∀ omega, X omega ≤ b + Y omega) :
    ∫ omega, X omega ^ (2 : ℝ) ∂mu ≤
      (2 * (b + orliczSecondMomentScale sigma * A)) ^ (2 : ℝ) := by
  have hvnn : 0 ≤ orliczSecondMomentScale sigma * A :=
    mul_nonneg (orliczSecondMomentScale_pos hsigma).le hA.le
  have hI := integrable_pow_two_max_zero hsigma hA hYm hT
  have hM := integral_pow_two_max_zero_le hsigma hA hYm hT
  have hpoint : ∀ omega, X omega ^ (2 : ℕ) ≤
      4 * (b ^ (2 : ℕ) + max (Y omega) 0 ^ (2 : ℕ)) := by
    intro omega
    have hle : X omega ≤ b + max (Y omega) 0 := by
      have h1 : Y omega ≤ max (Y omega) 0 := le_max_left _ _
      have := hdom omega
      linarith
    have hpow : X omega ^ (2 : ℕ) ≤ (b + max (Y omega) 0) ^ (2 : ℕ) := by
      have h0 := hX0 omega
      exact pow_le_pow_left₀ h0 hle 2
    exact hpow.trans (pow_two_add_le b (max (Y omega) 0))
  have hmaj : Integrable (fun omega =>
      4 * (b ^ (2 : ℕ) + max (Y omega) 0 ^ (2 : ℕ))) mu :=
    ((integrable_const (b ^ (2 : ℕ))).add hI).const_mul _
  have hstep : ∫ omega, X omega ^ (2 : ℕ) ∂mu ≤
      ∫ omega, 4 * (b ^ (2 : ℕ) + max (Y omega) 0 ^ (2 : ℕ)) ∂mu :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun omega => pow_nonneg (hX0 omega) 2) hmaj
      (Filter.Eventually.of_forall hpoint)
  have hsplit : ∫ omega, 4 * (b ^ (2 : ℕ) + max (Y omega) 0 ^ (2 : ℕ)) ∂mu =
      4 * (b ^ (2 : ℕ) + ∫ omega, max (Y omega) 0 ^ (2 : ℕ) ∂mu) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_add (f := fun _ => b ^ (2 : ℕ))
        (g := fun a => max (Y a) 0 ^ (2 : ℕ)) (integrable_const (b ^ (2 : ℕ))) hI,
      integral_const]
    simp
  have hsum : b ^ (2 : ℕ) + ∫ omega, max (Y omega) 0 ^ (2 : ℕ) ∂mu ≤
      (b + orliczSecondMomentScale sigma * A) ^ (2 : ℕ) := by
    have h := pow_add_pow_le hb hvnn (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  have hfinal : ∫ omega, X omega ^ (2 : ℕ) ∂mu ≤
      (2 * (b + orliczSecondMomentScale sigma * A)) ^ (2 : ℕ) := by
    have hexp : (2 * (b + orliczSecondMomentScale sigma * A)) ^ (2 : ℕ) =
        4 * (b + orliczSecondMomentScale sigma * A) ^ (2 : ℕ) := by
      rw [mul_pow]; norm_num
    rw [hsplit] at hstep
    rw [hexp]
    linarith
  simpa only [rpow_two_eq_pow] using hfinal

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
