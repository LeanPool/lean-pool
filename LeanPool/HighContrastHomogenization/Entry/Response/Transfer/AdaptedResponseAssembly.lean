/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseCutoffEstimate

/-!
# High-contrast homogenization: Entry.Response.Transfer.AdaptedResponseAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Assembling the adapted response decomposition

This file proves `adapted_response_core`, the decomposition claimed in the response transfer
skeleton, from its eleven constituent lemmas — the block algebra, the energy estimate, the diagonal
weak estimate, and the cutoff estimate — with no further unproved step of its own; the substitution
of `p.response.transfer` into that decomposition is carried out here in full. Closing this
substitution needs the same scalar arithmetic that turns a one-step contraction inequality
`κ_t - 1 ≤ ω κ_t` into the target bound `κ_t ≤ 1 + δ_ad`, together with the parameter choice of the
scale `H`, the tolerance `η`, and the base scale `σ₀` that keeps the resulting contraction constant
small enough; both are supplied here as the completeness check of the whole assembly.
-/

section
/-!
## Assembly of `adapted_response_core`

`adapted_response_core_of_holes` is `adapted_response_core` of
`HCPoly/Entry/Multiscale/ResponseTransferSkeleton.lean`, proved -- with no `sorry` of its own --
from the
eleven lemmas of `CenteredEnergyIdentity`, `LoadMeanIdentity`, `WeakEstimateAssembly`,
`ResponseCutoffEstimate`.  It is the completeness check of the assembly: the substitution of
`p.response.transfer` is carried out here in full.

`response_tolerances` is *not* used: it converts `delta` into `delta_ad`, while
`adapted_response_core` receives `delta_ad` directly.  The lemmas of `EccentricityScaleDecay.lean`
are not used here either: they are ingredients of the source smallness estimate, whose output
is all the assembly needs.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

variable {d : ℕ}

/-! ## Arithmetic helpers -/

private theorem sq_of_sqrt_le {x c : ℝ} (hx : 0 ≤ x) (h : Real.sqrt x ≤ c) : x ≤ c ^ 2 := by
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have h2 : Real.sqrt x * Real.sqrt x ≤ c * c :=
    mul_self_le_mul_self (Real.sqrt_nonneg x) h
  have hc2 : c ^ 2 = c * c := pow_two c
  linarith only [hs, h2, hc2]

/-- The substitution of `p.response.transfer`: putting
`e.response.energy.and.defect`, `e.response.weak.estimate` and `L_s <= C kappa_s^{3/2}` into
`e.response.cutoff.estimate` gives
`|Jtilde| <= C'((r-1) + sqrt(r-1) + 3^{-H} + (3^{-alpha H} + C_H eta^{1/(2Q)})^2) kappa_s`. -/
private theorem cutoff_substitution (C T r th Kq EJ tau L W X : ℝ)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hr : 1 ≤ r) (_hth : 0 ≤ th) (hK : 1 ≤ Kq)
    (hEJ0 : 0 ≤ EJ) (hEJ : EJ ≤ C * Kq)
    (_htau0 : 0 ≤ tau) (htau : tau ≤ C * (r - 1) * Kq)
    (hL0 : 0 ≤ L) (hL : L ≤ C * Kq ^ 3)
    (hW0 : 0 ≤ W) (hW : Real.sqrt W ≤ C * th * Kq)
    (hX : X ≤ C * (tau + Real.sqrt (tau * EJ) + Real.sqrt (tau * L) +
      T * (EJ + Real.sqrt (EJ * L)) + W)) :
    X ≤ 3 * C ^ 3 * ((r - 1) + Real.sqrt (r - 1) + T + th ^ 2) * Kq ^ 2 := by
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hK0 : (0 : ℝ) < Kq := lt_of_lt_of_le zero_lt_one hK
  have hR : (0 : ℝ) ≤ r - 1 := by linarith only [hr]
  have hsR : (0 : ℝ) ≤ Real.sqrt (r - 1) := Real.sqrt_nonneg _
  have hKK : (0 : ℝ) ≤ Kq ^ 2 - Kq := by nlinarith only [hK]
  have hKsq : (0 : ℝ) ≤ Kq ^ 2 := by positivity
  have hpos1 : (0 : ℝ) ≤ C * (r - 1) * Kq := by positivity
  have hpos2 : (0 : ℝ) ≤ C * Kq := by positivity
  have e1 : tau * EJ ≤ (C * Kq) ^ 2 * (r - 1) := by
    have h := mul_le_mul htau hEJ hEJ0 hpos1
    linarith only [h]
  have hrw1 : Real.sqrt ((C * Kq) ^ 2 * (r - 1)) = C * Kq * Real.sqrt (r - 1) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have s1 : Real.sqrt (tau * EJ) ≤ C * Kq * Real.sqrt (r - 1) := by
    rw [← hrw1]; exact Real.sqrt_le_sqrt e1
  have e2 : tau * L ≤ (C * Kq ^ 2) ^ 2 * (r - 1) := by
    have h := mul_le_mul htau hL hL0 hpos1
    linarith only [h]
  have hrw2 : Real.sqrt ((C * Kq ^ 2) ^ 2 * (r - 1)) = C * Kq ^ 2 * Real.sqrt (r - 1) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have s2 : Real.sqrt (tau * L) ≤ C * Kq ^ 2 * Real.sqrt (r - 1) := by
    rw [← hrw2]; exact Real.sqrt_le_sqrt e2
  have e3 : EJ * L ≤ (C * Kq ^ 2) ^ 2 := by
    have h := mul_le_mul hEJ hL hL0 hpos2
    linarith only [h]
  have hrw3 : Real.sqrt ((C * Kq ^ 2) ^ 2) = C * Kq ^ 2 := Real.sqrt_sq (by positivity)
  have s3 : Real.sqrt (EJ * L) ≤ C * Kq ^ 2 := by
    rw [← hrw3]; exact Real.sqrt_le_sqrt e3
  have w1 : W ≤ (C * th * Kq) ^ 2 := sq_of_sqrt_le hW0 hW
  have hb1 : tau ≤ C * (r - 1) * Kq ^ 2 := by
    have := mul_nonneg (mul_nonneg hC0.le hR) hKK
    linarith only [htau, this]
  have hb2 : Real.sqrt (tau * EJ) ≤ C * Kq ^ 2 * Real.sqrt (r - 1) := by
    have := mul_nonneg (mul_nonneg hC0.le hsR) hKK
    linarith only [s1, this]
  have hb4 : T * (EJ + Real.sqrt (EJ * L)) ≤ 2 * C * T * Kq ^ 2 := by
    have hcc := mul_nonneg hC0.le hKK
    have hin : EJ + Real.sqrt (EJ * L) ≤ 2 * (C * Kq ^ 2) := by
      linarith only [hEJ, s3, hcc]
    have := mul_le_mul_of_nonneg_left hin hT
    linarith only [this]
  have hb5 : W ≤ C ^ 2 * th ^ 2 * Kq ^ 2 := by linarith only [w1]
  have hsum : tau + Real.sqrt (tau * EJ) + Real.sqrt (tau * L) +
      T * (EJ + Real.sqrt (EJ * L)) + W ≤
      (C * (r - 1) + 2 * C * Real.sqrt (r - 1) + 2 * C * T + C ^ 2 * th ^ 2) * Kq ^ 2 := by
    linarith only [hb1, hb2, s2, hb4, hb5]
  have hmul := mul_le_mul_of_nonneg_left hsum hC0.le
  have hCC : C ^ 2 ≤ C ^ 3 := by nlinarith only [hC, sq_nonneg C]
  have hC3n : (0 : ℝ) ≤ C ^ 3 := by positivity
  have h3C : (0 : ℝ) ≤ 3 * C ^ 3 - C ^ 2 := by linarith only [hCC, hC3n]
  have h2C : (0 : ℝ) ≤ 3 * C ^ 3 - 2 * C ^ 2 := by linarith only [hCC, hC3n]
  have h4C : (0 : ℝ) ≤ 3 * C ^ 3 - C ^ 3 := by linarith only [hC3n]
  have hfin : C * ((C * (r - 1) + 2 * C * Real.sqrt (r - 1) + 2 * C * T + C ^ 2 * th ^ 2) *
      Kq ^ 2) ≤ 3 * C ^ 3 * ((r - 1) + Real.sqrt (r - 1) + T + th ^ 2) * Kq ^ 2 := by
    have p1 := mul_nonneg h3C (mul_nonneg hR hKsq)
    have p2 := mul_nonneg h2C (mul_nonneg hsR hKsq)
    have p3 := mul_nonneg h2C (mul_nonneg hT hKsq)
    have p4 := mul_nonneg h4C (mul_nonneg (sq_nonneg th) hKsq)
    linarith only [p1, p2, p3, p4]
  linarith only [hX, hmul, hfin]

/-- The contraction step of `p.response.transfer`: `kappa_t - 1 <= omega kappa_t`
with `omega = C r^2 (...)`. -/
private theorem contraction_step (Dd Call Om ks kt rr : ℝ)
    (hDd : 0 ≤ Dd) (hOm : 0 ≤ Om) (hCall : 0 ≤ Call)
    (hM : kt - 1 ≤ 12 * Dd * (6 * Call ^ 3 * Om * ks))
    (hks : ks ≤ rr ^ 2 * kt) :
    kt - 1 ≤ 72 * Dd * Call ^ 3 * rr ^ 2 * Om * kt := by
  have h1 : (0 : ℝ) ≤ 72 * Dd * Call ^ 3 * Om :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hDd) (pow_nonneg hCall 3)) hOm
  have h2 := mul_le_mul_of_nonneg_left hks h1
  linarith only [hM, h2]

/-- Shrinking `sigma_0` makes the profile bound of `raw.prof` at most `eta`
(`p.response.transfer`). -/
private theorem exists_sigma_profile (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (ε Cprof η : ℝ)
    (hε : 0 < ε) (hCprof : 0 < Cprof) (hη : 0 < η) :
    ∃ σ₁ : ℝ, σ₁ ∈ Set.Ioc (0 : ℝ) ε ∧
      ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₁ → Cprof * σ ^ ((1 - γ) / 8) ≤ η := by
  have hγ1 : γ < 1 := hγ.2
  have ha : (0 : ℝ) < (1 - γ) / 8 := by linarith only [hγ1]
  have hqpos : (0 : ℝ) < η / Cprof := div_pos hη hCprof
  have hb : (0 : ℝ) < (η / Cprof) ^ (1 / ((1 - γ) / 8)) := Real.rpow_pos_of_pos hqpos _
  refine ⟨min ε ((η / Cprof) ^ (1 / ((1 - γ) / 8))), ⟨lt_min hε hb, min_le_left _ _⟩, ?_⟩
  intro σ hσ
  have h1 : σ ^ ((1 - γ) / 8) ≤
      (min ε ((η / Cprof) ^ (1 / ((1 - γ) / 8)))) ^ ((1 - γ) / 8) :=
    Real.rpow_le_rpow hσ.1.le hσ.2 ha.le
  have h2 : (min ε ((η / Cprof) ^ (1 / ((1 - γ) / 8)))) ^ ((1 - γ) / 8) ≤
      ((η / Cprof) ^ (1 / ((1 - γ) / 8))) ^ ((1 - γ) / 8) :=
    Real.rpow_le_rpow (lt_min hε hb).le (min_le_right _ _) ha.le
  have h3 : ((η / Cprof) ^ (1 / ((1 - γ) / 8))) ^ ((1 - γ) / 8) = η / Cprof := by
    rw [← Real.rpow_mul hqpos.le, one_div_mul_cancel (ne_of_gt ha), Real.rpow_one]
  have h4 : σ ^ ((1 - γ) / 8) ≤ η / Cprof := by rw [← h3]; exact h1.trans h2
  have h5 := mul_le_mul_of_nonneg_left h4 hCprof.le
  have h6 : Cprof * (η / Cprof) = η := by field_simp
  linarith only [h5, h6]

/-- The per-load bound of `p.response.transfer`, for one unit vector `e`. -/
private theorem key_bound (Call C3 C6 C7 C8 : ℝ) (CH : ℕ → ℝ) (d : ℕ) (γ : ℝ)
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (H : ℕ) (η : ℝ) (s t : ℤ)
    (e : Vec d)
    (hCall1 : 1 ≤ Call) (hC3le : C3 ≤ Call) (hC6le : C6 ≤ Call) (hC7le : C7 ≤ Call)
    (hC8le : C8 ≤ Call) (hκs1 : 1 ≤ respKappa P jStar F s)
    (hr1 : 1 ≤ respRatio P jStar F s t)
    (hT0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)))
    (hth0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
      CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))))
    (hed : RespEnergyDefect C3 P jStar F s t e)
    (hwb : RespWeakBound C6 CH d γ P jStar F H η s t e)
    (hlb : RespLoadBound C7 P jStar F s t e)
    (hcb : RespCutoffBound C8 P jStar F H s t e) :
    |respCenteredJMinus P jStar F t e| + |respCenteredJPlus P jStar F t e| ≤
      6 * Call ^ 3 *
        ((respRatio P jStar F s t - 1) + Real.sqrt (respRatio P jStar F s t - 1) +
          (3 : ℝ) ^ (-(H : ℝ)) +
          ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
            CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2) *
        respKappa P jStar F s := by
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (respKappa P jStar F s) := Real.sqrt_nonneg _
  have hKq1 : (1 : ℝ) ≤ Real.sqrt (respKappa P jStar F s) := by
    have hle := Real.sqrt_le_sqrt hκs1
    simpa using hle
  have hKqsq : Real.sqrt (respKappa P jStar F s) ^ 2 = respKappa P jStar F s :=
    Real.sq_sqrt (by linarith only [hκs1])
  have hR0 : (0 : ℝ) ≤ respRatio P jStar F s t - 1 := by linarith only [hr1]
  obtain ⟨hEJ0m, hEJ0p, _, _, hEJm, hEJp, htau0m, htau0p, htaum, htaup⟩ := hed
  obtain ⟨hW0m, hW0p, hWm, hWp⟩ := hwb
  obtain ⟨hL0m, hL0p, hLm, hLp, _hSm, _hSp⟩ := hlb
  obtain ⟨hcbm, hcbp⟩ := hcb
  have hbr0m : (0 : ℝ) ≤ respTauMinus P jStar F s t e +
      Real.sqrt (respTauMinus P jStar F s t e * respEJMinus P jStar F t e) +
      Real.sqrt (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e) +
      (3 : ℝ) ^ (-(H : ℝ)) * (respEJMinus P jStar F t e +
        Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) +
      respWMinus P jStar F t e := by
    have q1 := Real.sqrt_nonneg (respTauMinus P jStar F s t e * respEJMinus P jStar F t e)
    have q2 := Real.sqrt_nonneg (respTauMinus P jStar F s t e * respLsMinus P jStar F s t e)
    have q3 := Real.sqrt_nonneg (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)
    have q4 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) * (respEJMinus P jStar F t e +
        Real.sqrt (respEJMinus P jStar F t e * respLsMinus P jStar F s t e)) :=
      mul_nonneg hT0 (by linarith only [hEJ0m, q3])
    linarith only [htau0m, q1, q2, q4, hW0m]
  have hbr0p : (0 : ℝ) ≤ respTauPlus P jStar F s t e +
      Real.sqrt (respTauPlus P jStar F s t e * respEJPlus P jStar F t e) +
      Real.sqrt (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e) +
      (3 : ℝ) ^ (-(H : ℝ)) * (respEJPlus P jStar F t e +
        Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) +
      respWPlus P jStar F t e := by
    have q1 := Real.sqrt_nonneg (respTauPlus P jStar F s t e * respEJPlus P jStar F t e)
    have q2 := Real.sqrt_nonneg (respTauPlus P jStar F s t e * respLsPlus P jStar F s t e)
    have q3 := Real.sqrt_nonneg (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)
    have q4 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) * (respEJPlus P jStar F t e +
        Real.sqrt (respEJPlus P jStar F t e * respLsPlus P jStar F s t e)) :=
      mul_nonneg hT0 (by linarith only [hEJ0p, q3])
    linarith only [htau0p, q1, q2, q4, hW0p]
  have hLcube : (0 : ℝ) ≤ Real.sqrt (respKappa P jStar F s) ^ 3 := pow_nonneg hsq0 3
  have hm := cutoff_substitution Call ((3 : ℝ) ^ (-(H : ℝ))) (respRatio P jStar F s t)
    ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ :
      ℝ))))
    (Real.sqrt (respKappa P jStar F s)) (respEJMinus P jStar F t e)
    (respTauMinus P jStar F s t e) (respLsMinus P jStar F s t e) (respWMinus P jStar F t e)
    |respCenteredJMinus P jStar F t e| hCall1 hT0 hr1 hth0 hKq1 hEJ0m
    (le_trans hEJm (mul_le_mul_of_nonneg_right hC3le hsq0)) htau0m
    (le_trans htaum (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC3le hR0) hsq0)) hL0m
    (le_trans hLm (mul_le_mul_of_nonneg_right hC7le hLcube)) hW0m
    (le_trans hWm (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC6le hth0) hsq0))
    (le_trans hcbm (mul_le_mul_of_nonneg_right hC8le hbr0m))
  have hp := cutoff_substitution Call ((3 : ℝ) ^ (-(H : ℝ))) (respRatio P jStar F s t)
    ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) + CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ :
      ℝ))))
    (Real.sqrt (respKappa P jStar F s)) (respEJPlus P jStar F t e)
    (respTauPlus P jStar F s t e) (respLsPlus P jStar F s t e) (respWPlus P jStar F t e)
    |respCenteredJPlus P jStar F t e| hCall1 hT0 hr1 hth0 hKq1 hEJ0p
    (le_trans hEJp (mul_le_mul_of_nonneg_right hC3le hsq0)) htau0p
    (le_trans htaup (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC3le hR0) hsq0)) hL0p
    (le_trans hLp (mul_le_mul_of_nonneg_right hC7le hLcube)) hW0p
    (le_trans hWp (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC6le hth0) hsq0))
    (le_trans hcbp (mul_le_mul_of_nonneg_right hC8le hbr0p))
  rw [hKqsq] at hm hp
  linarith only [hm, hp]

/-- `RawOutput` is antitone in the source threshold constant `Csrc`: the only field mentioning
`Csrc` is `hsrc`, whose left-hand side is increasing in `Csrc` because
`0 ≤ logb 3 (2K)` (from `1 < K`, `CoarseEllipticityDagger.one_lt_growthWitness`).  Used to feed
one `RawOutput` at `max Csrc₁₀ Csrc₅` to the source smallness and all-scale estimates, which
produce `Csrc₁₀` and `Csrc₅` respectively. -/
private theorem rawOutput_le_csrc {γ : ℝ} {S : SelectionData}
    {ε σ Cglob Cprof Csrc Csrc' : ℝ} {H : ℕ} {Bresp : ℝ} {P : Measure (CoeffSpace d)}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ}
    {F : BlockMat d} {s t : ℤ}
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ K Src B jStar F s t)
    (h : Csrc' ≤ Csrc) :
    RawOutput d γ S ε σ Cglob Cprof Csrc' H Bresp P E Ψ K Src B jStar F s t := by
  refine ⟨raw.prob, raw.stat, raw.unit, raw.ell, raw.hB, raw.hj, ?_, raw.symm, raw.pos, raw.hst,
    raw.ht, raw.hs_lo, raw.ht_hi, raw.cube, raw.calib_lo, raw.calib_hi, raw.det, raw.prof,
    raw.ecc⟩
  have hK : 1 < K := raw.ell.one_lt_growthWitness
  have hlog : 0 ≤ Real.logb 3 (2 * K) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hK])
  refine le_trans (Int.ceil_mono ?_) raw.hsrc
  have := mul_le_mul_of_nonneg_right h hlog
  linarith only [this]

/-! ## The assembly -/

/-- `adapted_response_core` (`HCPoly/Entry/Multiscale/ResponseTransferSkeleton.lean`),
proved from the eleven lemmas.  Conclusion `e.response.adapted.conclusion`
(`e.response.adapted.conclusion`). -/
theorem adapted_response_core_of_holes (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ)
    (_hγ : γ ∈ Set.Ico (0 : ℝ) 1) (S : SelectionData) (_hS : S.Selects d γ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
      ∀ δad : ℝ, δad ∈ Set.Ioc (0 : ℝ) 1 →
        ∃ H : ℕ, max 4 S.h ≤ H ∧
          ∀ Cprof : ℝ, 0 < Cprof →
            ∃ σ₀ : ℝ, σ₀ ∈ Set.Ioc (0 : ℝ) ε ∧
              ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) σ₀ →
                ∀ Cglob : ℝ, 0 < Cglob →
                  ∃ Bresp : ℝ, 1 ≤ Bresp ∧
                    ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
                      (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
                      RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ K Src B jStar F s t →
                      canonicalImbalance
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar
                            (explicitCanonicalMetric F)) t) ≤
                          1 + δad := by
  obtain ⟨C2, hC2, h2⟩ := response_calibrated_blocks d _hd γ _hγ S _hS
  obtain ⟨Csrc10, hCsrc10, C10, hC10, h10⟩ := response_source_smallness d _hd γ _hγ S _hS
  obtain ⟨C3, hC3, h3⟩ := response_energy_and_defect d _hd γ _hγ S _hS C2 hC2
  obtain ⟨C4, hC4, h4⟩ := response_load_and_mean d _hd γ _hγ S _hS C2 C3 hC2 hC3
  obtain ⟨Csrc5, hCsrc5, C5, hC5, h5⟩ := response_allscale_abs d _hd γ _hγ S _hS C10 hC10
  obtain ⟨Csrc6, hCsrc6, C6, CH, hC6, hCH, h6⟩ :=
    response_weak_estimate d _hd γ _hγ S _hS C2 C3 C4 C5 C10 hC2 hC3 hC4 hC5 hC10
  obtain ⟨Csrc7, hCsrc7, C7, hC7, h7⟩ :=
    response_source_load_bound d _hd γ _hγ S _hS C2 C10 C4 hC2 hC10 hC4
  obtain ⟨Csrc8, hCsrc8, C8, hC8, h8⟩ :=
    response_cutoff_estimate d _hd γ _hγ S _hS C2 C3 C4 C7 hC2 hC3 hC4 hC7
  obtain ⟨Call, hCall1, hC3le, hC6le, hC7le, hC8le⟩ :
      ∃ Call : ℝ, 1 ≤ Call ∧ C3 ≤ Call ∧ C6 ≤ Call ∧ C7 ≤ Call ∧ C8 ≤ Call := by
    refine ⟨max (max C3 C6) (max C7 (max C8 1)), ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_max_right C8 1) (le_trans (le_max_right C7 _) (le_max_right _ _))
    · exact le_trans (le_max_left C3 C6) (le_max_left _ _)
    · exact le_trans (le_max_right C3 C6) (le_max_left _ _)
    · exact le_trans (le_max_left C7 (max C8 1)) (le_max_right _ _)
    · exact le_trans (le_max_left C8 1) (le_trans (le_max_right C7 _) (le_max_right _ _))
  have hCall0 : (0 : ℝ) < Call := lt_of_lt_of_le zero_lt_one hCall1
  obtain ⟨Csrc, hCsrc, hle10, hle6, hle5, hle7, hle8⟩ :
      ∃ Csrc : ℝ, 0 < Csrc ∧ Csrc10 ≤ Csrc ∧ Csrc6 ≤ Csrc ∧ Csrc5 ≤ Csrc ∧ Csrc7 ≤ Csrc ∧
        Csrc8 ≤ Csrc :=
    ⟨max (max Csrc10 Csrc6) (max Csrc5 (max Csrc7 Csrc8)),
      lt_max_iff.mpr (Or.inl (lt_max_iff.mpr (Or.inl hCsrc10))),
      le_trans (le_max_left Csrc10 Csrc6) (le_max_left _ _),
      le_trans (le_max_right Csrc10 Csrc6) (le_max_left _ _),
      le_trans (le_max_left Csrc5 (max Csrc7 Csrc8)) (le_max_right _ _),
      le_trans (le_trans (le_max_left Csrc7 Csrc8) (le_max_right Csrc5 (max Csrc7 Csrc8)))
        (le_max_right _ _),
      le_trans (le_trans (le_max_right Csrc7 Csrc8) (le_max_right Csrc5 (max Csrc7 Csrc8)))
        (le_max_right _ _)⟩
  refine ⟨Csrc, hCsrc, ?_⟩
  intro ε hε δad hδad
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have hdn : (0 : ℕ) < d := lt_of_lt_of_le two_pos _hd
    exact_mod_cast hdn
  have hCbig : (0 : ℝ) < 72 * (d : ℝ) * Call ^ 3 :=
    mul_pos (mul_pos (by norm_num) hd0) (pow_pos hCall0 3)
  have hα : Quenched.contrastAlpha γ ∈ Set.Ioo (0 : ℝ) 1 := by
    have h1 : γ < 1 := _hγ.2
    have h0 : (0 : ℝ) ≤ γ := _hγ.1
    refine ⟨?_, ?_⟩ <;> · simp only [Quenched.contrastAlpha]; linarith only [h0, h1]
  have hQ : 2 ≤ bigQ d γ := by
    have h1 : (0 : ℝ) < 1 - γ := by linarith only [_hγ.2]
    have hx : (0 : ℝ) < 2 * ((d : ℝ) + 1) / (1 - γ) :=
      div_pos (by positivity) h1
    have hc := Nat.ceil_pos.mpr hx
    simp only [bigQ]
    omega
  obtain ⟨H, hH, η, hη, σ₀', hσ₀', hchoice⟩ :=
    response_parameter_choice d _hd S.h (bigQ d γ) ε δad (Quenched.contrastAlpha γ)
      (72 * (d : ℝ) * Call ^ 3) CH hε.1 hδad hα hCbig hQ hCH
  refine ⟨H, hH, ?_⟩
  intro Cprof hCprof
  obtain ⟨σ₁, hσ₁, hprof1⟩ := exists_sigma_profile γ _hγ ε Cprof η hε.1 hCprof hη.1
  refine ⟨min σ₀' σ₁, ⟨lt_min hσ₀'.1 hσ₁.1, le_trans (min_le_left _ _) hσ₀'.2⟩, ?_⟩
  intro σ hσ Cglob hCglob
  have hσ0' : σ ∈ Set.Ioc (0 : ℝ) σ₀' := ⟨hσ.1, le_trans hσ.2 (min_le_left _ _)⟩
  have hσ1' : σ ∈ Set.Ioc (0 : ℝ) σ₁ := ⟨hσ.1, le_trans hσ.2 (min_le_right _ _)⟩
  have hσε : σ ∈ Set.Ioc (0 : ℝ) ε := ⟨hσ.1, le_trans hσ0'.2 hσ₀'.2⟩
  obtain ⟨Bresp, hB1, h10'⟩ := h10 ε hε δad hδad H hH η hη Cprof hCprof σ hσε Cglob hCglob
  refine ⟨Bresp, hB1, ?_⟩
  intro P E Ψ Kg Src B jStar F s t raw
  show respKappa P jStar F t ≤ 1 + δad
  have hcal := h2 ε σ hε hσε Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw
  have hss := h10' P E Ψ Kg Src B jStar F s t (rawOutput_le_csrc raw hle10)
  obtain ⟨hk1, hkts, hksr, hr1, hrexp⟩ :=
    response_imbalance_comparison d _hd γ _hγ S _hS ε σ hε hσε Cglob Cprof Csrc Bresp H P E Ψ
      Kg Src B jStar F s t raw
  have hMQ := h5 ε σ hε hσε Cglob Cprof Bresp hCglob.le H P E Ψ Kg Src B jStar F s t
    (rawOutput_le_csrc raw hle5) η hη
    (hprof1 σ hσ1') hss
  have hκs1 : (1 : ℝ) ≤ respKappa P jStar F s := le_trans hk1 hkts
  have hT0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(H : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hth0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
      CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) := by
    have p1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) := Real.rpow_nonneg
      (by norm_num) _
    have p2 : (0 : ℝ) ≤ η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) := Real.rpow_nonneg hη.1.le _
    have p3 : (0 : ℝ) ≤ CH H := (hCH H).le
    have p4 : (0 : ℝ) ≤ CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))) := mul_nonneg p3 p2
    linarith only [p1, p4]
  have hΩ0 : (0 : ℝ) ≤ (respRatio P jStar F s t - 1) +
      Real.sqrt (respRatio P jStar F s t - 1) + (3 : ℝ) ^ (-(H : ℝ)) +
      ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2 := by
    have q1 := Real.sqrt_nonneg (respRatio P jStar F s t - 1)
    have q2 := sq_nonneg ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
      CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))))
    linarith only [hr1, q1, hT0, q2]
  have key : ∀ e : Vec d, vecDot e e = 1 →
      |respCenteredJMinus P jStar F t e| + |respCenteredJPlus P jStar F t e| ≤
        6 * Call ^ 3 *
          ((respRatio P jStar F s t - 1) + Real.sqrt (respRatio P jStar F s t - 1) +
            (3 : ℝ) ^ (-(H : ℝ)) +
            ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
              CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2) *
          respKappa P jStar F s := by
    intro e he
    have hed := h3 ε σ hε hσε Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw hcal e he
    have hlm := h4 ε σ hε hσε Cglob Cprof Csrc Bresp H P E Ψ Kg Src B jStar F s t raw hcal e
      he hed
    have hlb := h7 ε σ hε hσε Cglob Cprof Bresp hCglob.le H P E Ψ Kg Src B jStar F s t
      (rawOutput_le_csrc raw hle7) hcal η hη (hprof1 σ hσ1') hss e he hlm
    have hwb := h6 ε σ hε hσε Cglob Cprof Bresp hCglob.le H P E Ψ Kg Src B jStar F s t
      (rawOutput_le_csrc raw hle6) hcal η hη (hprof1 σ hσ1') hss hMQ e he hed hlm
    have hcb := h8 ε σ hε hσε Cglob Cprof Bresp hCglob.le H P E Ψ Kg Src B jStar F s t
      (rawOutput_le_csrc raw hle8) hcal e he hed hlm hlb
    exact key_bound Call C3 C6 C7 C8 CH d γ P jStar F H η s t e hCall1 hC3le hC6le hC7le hC8le
      hκs1 hr1 hT0 hth0 hed hwb hlb hcb
  have hM := response_by_centered_energies d _hd γ _hγ S _hS ε σ Cglob Cprof Csrc Bresp H P E Ψ
    Kg Src B jStar F s t raw
    (6 * Call ^ 3 *
      ((respRatio P jStar F s t - 1) + Real.sqrt (respRatio P jStar F s t - 1) +
        (3 : ℝ) ^ (-(H : ℝ)) +
        ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
          CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2) * respKappa P jStar F s) key
  have hω := hchoice σ hσ0' (respRatio P jStar F s t) hr1 hrexp
  have hcontract := contraction_step (d : ℝ) Call
    ((respRatio P jStar F s t - 1) + Real.sqrt (respRatio P jStar F s t - 1) +
      (3 : ℝ) ^ (-(H : ℝ)) +
      ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2)
    (respKappa P jStar F s) (respKappa P jStar F t) (respRatio P jStar F s t)
    hd0.le hΩ0 hCall0.le hM hksr
  refine response_contraction_arith d _hd σ δad (respKappa P jStar F t) (respKappa P jStar F s)
    (respRatio P jStar F s t)
    (72 * (d : ℝ) * Call ^ 3 * respRatio P jStar F s t ^ 2 *
      ((respRatio P jStar F s t - 1) + Real.sqrt (respRatio P jStar F s t - 1) +
        (3 : ℝ) ^ (-(H : ℝ)) +
        ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
          CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2))
    hk1 hkts hksr hrexp hδad ?_ hω
  linarith only [hcontract]

end HCPolySupport.HighContrast.Multiscale
end
