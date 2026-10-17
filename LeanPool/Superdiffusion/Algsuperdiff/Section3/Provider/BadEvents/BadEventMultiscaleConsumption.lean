/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.BadEventEstimate
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound

/-!
# BadEventMultiscaleConsumption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Bad-event estimate at the multiscale parameters

This module applies the frozen bad-event theorem to the event at scales
`(l, l - h)`.  Its private arithmetic derives the theorem's admissibility,
fifth-root, nonlinear-time, and entropy/exponential gates from the scale
separation hypotheses used by the multiscale argument.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open HCPolySupport

noncomputable section

private theorem le_rpow_neg_fifth_of_gamma_le_inv_pow_ten
    {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hgammaE : gamma ≤ E⁻¹ ^ (10 : ℕ)) :
    E ≤ gamma ^ (-(1 / 5 : ℝ)) := by
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hEinv : gamma ≤ (E ^ (10 : ℕ))⁻¹ := by
    simpa only [inv_pow] using hgammaE
  have hE10 : E ^ (10 : ℕ) ≤ gamma⁻¹ := by
    rw [le_inv_comm₀ (pow_pos hEpos 10) hgamma]
    exact hEinv
  have hE5 : E ^ (5 : ℕ) ≤ gamma⁻¹ :=
    (pow_le_pow_right₀ hE (by norm_num : (5 : ℕ) ≤ 10)).trans hE10
  have hroot : E ≤ (gamma⁻¹) ^ (5 : ℝ)⁻¹ := by
    rw [Real.le_rpow_inv_iff_of_pos hE0 (inv_pos.mpr hgamma).le (by norm_num)]
    exact (Real.rpow_natCast E 5).trans_le hE5
  calc
    E ≤ (gamma⁻¹) ^ (5 : ℝ)⁻¹ := hroot
    _ = (gamma⁻¹) ^ (1 / 5 : ℝ) := by norm_num
    _ = (gamma ^ (-1 : ℝ)) ^ (1 / 5 : ℝ) := by rw [Real.rpow_neg_one]
    _ = gamma ^ ((-1 : ℝ) * (1 / 5 : ℝ)) :=
      (Real.rpow_mul hgamma.le _ _).symm
    _ = gamma ^ (-(1 / 5 : ℝ)) := by ring_nf

private theorem multiscaleEntropy_bound
    {d : ℕ} (M : Algsuperdiff.Section3.ABKModel d)
    {Ccg c H epsilon E : ℝ} {h : ℕ}
    (hCcg : 1 ≤ Ccg) (hH : 0 ≤ H) (hE : 1 ≤ E)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hh : (h : ℝ) ≤ H * |Real.log epsilon| + 1)
    (hscale : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ *
      epsilon ^ (-(1 + 2 * |Real.log c| +
        (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
        12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3)) ≤ E)
    (hgammaInv : E ^ (10 : ℕ) ≤ M.gamma⁻¹) :
    (d : ℝ) * (h : ℝ) * Real.log 3 +
      Real.exp ((1 / 8 : ℝ) * (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) ≤
        Real.exp ((1 / 4 : ℝ) * (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) := by
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCcgPos : 0 < Ccg := zero_lt_one.trans_le hCcg
  have hcstarPos : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hlogEpsNonpos : Real.log epsilon ≤ 0 := by
    exact Real.log_nonpos hepsilon.le
      (hepsilonHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have habsLogEps : |Real.log epsilon| = -Real.log epsilon :=
    abs_of_nonpos hlogEpsNonpos
  have hlogEpsHalf : Real.log epsilon ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log hepsilon hepsilonHalf
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hLHalf : (1 / 2 : ℝ) ≤ |Real.log epsilon| := by
    rw [habsLogEps]
    rw [hlogHalf] at hlogEpsHalf
    nlinarith [Real.log_two_gt_d9]
  have hLNonneg : 0 ≤ |Real.log epsilon| := abs_nonneg _
  let C : ℝ :=
    1 + 2 * |Real.log c| +
      (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
      12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3
  have hepsPow : epsilon ^ (-C) =
      Real.exp (C * |Real.log epsilon|) := by
    rw [Real.rpow_def_of_pos hepsilon, habsLogEps]
    congr 1
    ring
  have hcstarInvLower : (2 / 3 : ℝ) ≤
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ := by
    have hcstarUpper :=
      Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
    rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3 / 2) hcstarPos).2 hcstarUpper
  have hExpScale : (2 / 3 : ℝ) * Real.exp (C * |Real.log epsilon|) ≤ E := by
    rw [← hepsPow]
    exact (mul_le_mul_of_nonneg_right hcstarInvLower
      (Real.rpow_pos_of_pos hepsilon _).le).trans hscale
  have hCEntropy :
      12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3 ≤ C := by
    dsimp only [C]
    have hrest : 0 ≤
        1 + 2 * |Real.log c| +
          (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) := by
      positivity
    linarith
  have hhSimple : (h : ℝ) ≤ (H + 2) * |Real.log epsilon| := by
    have hone : (1 : ℝ) ≤ 2 * |Real.log epsilon| := by
      calc
        (1 : ℝ) = 2 * (1 / 2 : ℝ) := by norm_num
        _ ≤ 2 * |Real.log epsilon| :=
          mul_le_mul_of_nonneg_left hLHalf (by norm_num)
    calc
      (h : ℝ) ≤ H * |Real.log epsilon| + 1 := hh
      _ ≤ H * |Real.log epsilon| + 2 * |Real.log epsilon| :=
        add_le_add_right hone _
      _ = (H + 2) * |Real.log epsilon| := by ring
  have hEntropyLinear :
      8 * Ccg * ((d : ℝ) * (h : ℝ) * Real.log 3) ≤
        (2 / 3 : ℝ) * C * |Real.log epsilon| := by
    calc
      8 * Ccg * ((d : ℝ) * (h : ℝ) * Real.log 3) ≤
          8 * Ccg * ((d : ℝ) * ((H + 2) * |Real.log epsilon|) *
            Real.log 3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hhSimple (Nat.cast_nonneg d))
            hlogThree.le)
          (mul_nonneg (by norm_num) hCcgPos.le)
      _ = (2 / 3 : ℝ) *
          (12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3) *
            |Real.log epsilon| := by ring
      _ ≤ (2 / 3 : ℝ) * C * |Real.log epsilon| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCEntropy (by norm_num)) hLNonneg
  have hLinearExp : C * |Real.log epsilon| ≤
      Real.exp (C * |Real.log epsilon|) := by
    calc
      C * |Real.log epsilon| ≤ C * |Real.log epsilon| + 1 :=
        le_add_of_nonneg_right zero_le_one
      _ ≤ Real.exp (C * |Real.log epsilon|) :=
        Real.add_one_le_exp (C * |Real.log epsilon|)
  have hEntropyE :
      8 * Ccg * ((d : ℝ) * (h : ℝ) * Real.log 3) ≤ E := by
    calc
      8 * Ccg * ((d : ℝ) * (h : ℝ) * Real.log 3) ≤
          (2 / 3 : ℝ) * C * |Real.log epsilon| := hEntropyLinear
      _ ≤ (2 / 3 : ℝ) * Real.exp (C * |Real.log epsilon|) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left hLinearExp (by norm_num : (0 : ℝ) ≤ 2 / 3)
      _ ≤ E := hExpScale
  have hELeE8 : E ≤ E ^ (8 : ℕ) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hE (by norm_num : (1 : ℕ) ≤ 8))
  have hEntropyE8 :
      8 * Ccg * ((d : ℝ) * (h : ℝ) * Real.log 3) ≤ E ^ (8 : ℕ) :=
    hEntropyE.trans hELeE8
  have hE8Gamma : E ^ (8 : ℕ) ≤ E⁻¹ ^ 2 * M.gamma⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_left hgammaInv (sq_nonneg E⁻¹)
    calc
      E ^ (8 : ℕ) = E⁻¹ ^ 2 * E ^ (10 : ℕ) := by
        field_simp
      _ ≤ E⁻¹ ^ 2 * M.gamma⁻¹ := hmul
  let X : ℝ := Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹
  have hXNonneg : 0 ≤ X := by
    dsimp only [X]
    positivity
  have hEntropyX :
      (d : ℝ) * (h : ℝ) * Real.log 3 ≤ (1 / 8 : ℝ) * X := by
    have hdiv : (d : ℝ) * (h : ℝ) * Real.log 3 ≤
        (E ^ (8 : ℕ)) / (8 * Ccg) := by
      rw [le_div_iff₀ (mul_pos (by norm_num) hCcgPos)]
      have hcomm : (d : ℝ) * (h : ℝ) * Real.log 3 * (8 * Ccg) =
          8 * Ccg * ((d : ℝ) * (h : ℝ) * Real.log 3) := by ring
      rw [hcomm]
      exact hEntropyE8
    calc
      (d : ℝ) * (h : ℝ) * Real.log 3 ≤
          (E ^ (8 : ℕ)) / (8 * Ccg) := hdiv
      _ ≤ (E⁻¹ ^ 2 * M.gamma⁻¹) / (8 * Ccg) := by
        exact div_le_div_of_nonneg_right hE8Gamma
          (mul_nonneg (by norm_num) hCcgPos.le)
      _ = (1 / 8 : ℝ) * X := by
        dsimp only [X]
        field_simp
  let y : ℝ := (1 / 8 : ℝ) * X
  have hyNonneg : 0 ≤ y := mul_nonneg (by norm_num) hXNonneg
  have hyExp : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hexpOne : 1 ≤ Real.exp y := by
    simpa only [Real.exp_zero] using Real.exp_monotone hyNonneg
  have hyMul : y + Real.exp y ≤ y * Real.exp y + Real.exp y := by
    have hscaled := mul_le_mul_of_nonneg_left hexpOne hyNonneg
    simpa only [mul_one] using add_le_add_left hscaled (Real.exp y)
  have hyAbsorb : y + Real.exp y ≤ Real.exp (2 * y) := by
    calc
      y + Real.exp y ≤ y * Real.exp y + Real.exp y := hyMul
      _ = (y + 1) * Real.exp y := by ring
      _ ≤ Real.exp y * Real.exp y :=
        mul_le_mul_of_nonneg_right hyExp (Real.exp_pos y).le
      _ = Real.exp (2 * y) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hELLIP :
      (d : ℝ) * (h : ℝ) * Real.log 3 +
            Real.exp ((1 / 8 : ℝ) *
              (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) ≤
          Real.exp ((1 / 4 : ℝ) *
            (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) := by
    calc
      (d : ℝ) * (h : ℝ) * Real.log 3 +
            Real.exp ((1 / 8 : ℝ) *
              (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) ≤
          y + Real.exp y := by
        dsimp only [y, X]
        exact add_le_add_left hEntropyX _
      _ ≤ Real.exp (2 * y) := hyAbsorb
      _ = Real.exp ((1 / 4 : ℝ) *
          (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) := by
        congr 1
        dsimp only [y, X]
        ring
  exact hELLIP

private theorem badEventMultiscaleGates
    {d : ℕ} (M : Algsuperdiff.Section3.ABKModel d)
    {Ccg c H epsilon E : ℝ} {h : ℕ}
    (hCcg : 1 ≤ Ccg) (hc : 0 < c) (hH : 0 ≤ H) (hE : 1 ≤ E)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hh : (h : ℝ) ≤ H * |Real.log epsilon| + 1) :
    let C : ℝ :=
      1 + 2 * |Real.log c| +
        (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
        12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3
    1 ≤ C ∧
      ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ E →
        M.gamma ≤ E⁻¹ ^ (10 : ℕ) →
        c⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E ∧
        E ≤ M.gamma ^ (-(1 / 5 : ℝ)) ∧
        (3 : ℝ) ^ (5 * (h : ℝ)) ≤
          c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ ∧
        (d : ℝ) * (h : ℝ) * Real.log 3 +
              Real.exp ((1 / 8 : ℝ) *
                (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) ≤
            Real.exp ((1 / 4 : ℝ) *
              (Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹))) := by
  dsimp only
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCcgPos : 0 < Ccg := zero_lt_one.trans_le hCcg
  have hcstarPos : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hlogEpsNonpos : Real.log epsilon ≤ 0 := by
    exact Real.log_nonpos hepsilon.le
      (hepsilonHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have habsLogEps : |Real.log epsilon| = -Real.log epsilon :=
    abs_of_nonpos hlogEpsNonpos
  have hlogEpsHalf : Real.log epsilon ≤ Real.log (1 / 2 : ℝ) :=
    Real.log_le_log hepsilon hepsilonHalf
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hLHalf : (1 / 2 : ℝ) ≤ |Real.log epsilon| := by
    rw [habsLogEps]
    rw [hlogHalf] at hlogEpsHalf
    nlinarith [Real.log_two_gt_d9]
  have hLNonneg : 0 ≤ |Real.log epsilon| := abs_nonneg _
  let C : ℝ :=
    1 + 2 * |Real.log c| +
      (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
      12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3
  have hCOne : 1 ≤ C := by
    dsimp only [C]
    have hrest : 0 ≤
        2 * |Real.log c| +
          (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
          12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3 := by
      positivity
    linarith
  refine ⟨hCOne, ?_⟩
  intro hscale hgammaE
  have hEPos : 0 < E := zero_lt_one.trans_le hE
  have hepsPow : epsilon ^ (-C) =
      Real.exp (C * |Real.log epsilon|) := by
    rw [Real.rpow_def_of_pos hepsilon, habsLogEps]
    congr 1
    ring
  have hCAbs : 2 * |Real.log c| ≤ C := by
    dsimp only [C]
    have hrest : 0 ≤
        1 + (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
          12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3 := by
      positivity
    linarith
  have hAbsLeCL : |Real.log c| ≤ C * |Real.log epsilon| := by
    have hmul := mul_le_mul_of_nonneg_right hCAbs hLNonneg
    have hfactor : 0 ≤ 2 * |Real.log c| := by positivity
    calc
      |Real.log c| = (2 * |Real.log c|) * (1 / 2 : ℝ) := by ring
      _ ≤ (2 * |Real.log c|) * |Real.log epsilon| :=
        mul_le_mul_of_nonneg_left hLHalf hfactor
      _ ≤ C * |Real.log epsilon| := hmul
  have hcInvLeEps : c⁻¹ ≤ epsilon ^ (-C) := by
    rw [← Real.exp_log (inv_pos.mpr hc), Real.log_inv, hepsPow]
    exact Real.exp_le_exp.2 ((neg_le_abs (Real.log c)).trans hAbsLeCL)
  have hadm : c⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E := by
    calc
      c⁻¹ * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤
          epsilon ^ (-C) * (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ :=
        mul_le_mul_of_nonneg_right hcInvLeEps (inv_pos.mpr hcstarPos).le
      _ = (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * epsilon ^ (-C) :=
        mul_comm _ _
      _ ≤ E := hscale
  have hroot : E ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
    le_rpow_neg_fifth_of_gamma_le_inv_pow_ten hE hgammaPos hgammaE
  have hgammaInv : E ^ (10 : ℕ) ≤ M.gamma⁻¹ := by
    have hgammaInv' : M.gamma ≤ (E ^ (10 : ℕ))⁻¹ := by
      simpa only [inv_pow] using hgammaE
    rw [le_inv_comm₀ (pow_pos hEPos 10) hgammaPos]
    exact hgammaInv'
  have hCNLTM :
      5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|) ≤ C := by
    dsimp only [C]
    have hrest : 0 ≤
        1 + 2 * |Real.log c| +
          12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3 := by
      positivity
    linarith
  have hNLTMLog :
      5 * (h : ℝ) * Real.log 3 + |Real.log c| ≤
        C * |Real.log epsilon| := by
    have hh' := mul_le_mul_of_nonneg_right hh
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hlogThree.le)
    have hCmul := mul_le_mul_of_nonneg_right hCNLTM hLNonneg
    have hconst :
        5 * Real.log 3 + |Real.log c| ≤
          2 * (5 * Real.log 3 + |Real.log c|) * |Real.log epsilon| := by
      have hnonneg : 0 ≤ 5 * Real.log 3 + |Real.log c| := by positivity
      calc
        5 * Real.log 3 + |Real.log c| =
            (2 * (5 * Real.log 3 + |Real.log c|)) * (1 / 2 : ℝ) := by ring
        _ ≤ (2 * (5 * Real.log 3 + |Real.log c|)) *
            |Real.log epsilon| :=
          mul_le_mul_of_nonneg_left hLHalf (mul_nonneg (by norm_num) hnonneg)
    calc
      5 * (h : ℝ) * Real.log 3 + |Real.log c| =
          (h : ℝ) * (5 * Real.log 3) + |Real.log c| := by ring
      _ ≤ (H * |Real.log epsilon| + 1) * (5 * Real.log 3) +
          |Real.log c| := add_le_add_left hh' _
      _ = (5 * H * Real.log 3) * |Real.log epsilon| +
          (5 * Real.log 3 + |Real.log c|) := by ring
      _ ≤ (5 * H * Real.log 3) * |Real.log epsilon| +
          2 * (5 * Real.log 3 + |Real.log c|) * |Real.log epsilon| :=
        add_le_add_right hconst _
      _ = (5 * H * Real.log 3 +
          2 * (5 * Real.log 3 + |Real.log c|)) * |Real.log epsilon| := by ring
      _ ≤ C * |Real.log epsilon| := hCmul
  have hthreeEps : (3 : ℝ) ^ (5 * (h : ℝ)) ≤ c * epsilon ^ (-C) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), hepsPow,
      ← Real.exp_log hc, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hlogLower : -|Real.log c| ≤ Real.log c := neg_abs_le _
    calc
      Real.log 3 * (5 * (h : ℝ)) = 5 * (h : ℝ) * Real.log 3 := by ring
      _ ≤
          C * |Real.log epsilon| - |Real.log c| :=
        (le_sub_iff_add_le).2 hNLTMLog
      _ ≤ C * |Real.log epsilon| + Real.log c := by
        simpa only [sub_eq_add_neg] using
          add_le_add_right hlogLower (C * |Real.log epsilon|)
      _ = Real.log c + C * |Real.log epsilon| := by ring
  have hepsScale : epsilon ^ (-C) ≤
      E * Algsuperdiff.Section3.Disorder.cstar M := by
    have hmul := mul_le_mul_of_nonneg_right hscale hcstarPos.le
    calc
      epsilon ^ (-C) =
          ((Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * epsilon ^ (-C)) *
            Algsuperdiff.Section3.Disorder.cstar M := by field_simp
      _ ≤ E * Algsuperdiff.Section3.Disorder.cstar M := hmul
  have hELeE10 : E ≤ E ^ (10 : ℕ) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hE (by norm_num : (1 : ℕ) ≤ 10))
  have hNLTM : (3 : ℝ) ^ (5 * (h : ℝ)) ≤
      c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by
    calc
      (3 : ℝ) ^ (5 * (h : ℝ)) ≤ c * epsilon ^ (-C) := hthreeEps
      _ ≤ c * (E * Algsuperdiff.Section3.Disorder.cstar M) :=
        mul_le_mul_of_nonneg_left hepsScale hc.le
      _ ≤ c * (E ^ (10 : ℕ) *
          Algsuperdiff.Section3.Disorder.cstar M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hELeE10 hcstarPos.le) hc.le
      _ ≤ c * (M.gamma⁻¹ *
          Algsuperdiff.Section3.Disorder.cstar M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hgammaInv hcstarPos.le) hc.le
      _ = c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ := by ring
  exact ⟨hadm, hroot, hNLTM,
    multiscaleEntropy_bound M hCcg hH hE hepsilon hepsilonHalf hh hscale hgammaInv⟩

/-- Direct use of the frozen bad-event estimate at the multiscale event
`goodLocalEventAt M _ l (l - h) z`.  The two branch-guard estimates are
consequences of the paper's scale separation, not caller-supplied proof
obligations.  The bad-event constants `Ccg` and `c` are selected before `H`;
only the scale exponent `C` depends on `H`. -/
theorem exists_measureReal_compl_goodLocalEventAt_le_of_multiscaleParameters
    (d : ℕ) :
    ∃ Ccg c : ℝ, 1 ≤ Ccg ∧ 0 < c ∧
      ∀ (H : ℝ), 0 ≤ H →
      ∃ C : ℝ, 1 ≤ C ∧
      ∀ (M : Algsuperdiff.Section3.ABKModel d) (m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E})
        (epsilon : ℝ) (h : ℕ) (l : ℤ),
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        epsilon ∈ Set.Ioc 0 (1 / 2) →
        (h : ℝ) ≤ H * |Real.log epsilon| + 1 →
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ * epsilon ^ (-C) ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        l - (h : ℤ) ≤ m0 - 1 →
        ∀ z : Vec d,
          (Algsuperdiff.Section3.Cutoff.cutoffSampleLaw M).toMeasure.real
              (Algsuperdiff.Frozen.Section3.goodLocalEventAt
                M (2 * Ccg) l (l - (h : ℤ)) z)ᶜ ≤
            Real.exp
                (-(c * Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
                  (3 : ℝ) ^ (-5 * scaleGapPos (l - (h : ℤ)) l) *
                  (3 : ℝ) ^ scaleGapPos l (l - (h : ℤ)))) +
              Real.exp (-Real.exp
                (c * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) := by
  obtain ⟨Ccg, c, -, hCcg, hc, hbad⟩ :=
    Algsuperdiff.Frozen.Section3.bad_event_estimate d
  refine ⟨Ccg, c, hCcg, hc, ?_⟩
  intro H hH
  let C : ℝ :=
    1 + 2 * |Real.log c| +
      (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
      12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hCcgPos : 0 < Ccg := zero_lt_one.trans_le hCcg
    have hrest : 0 ≤
        2 * |Real.log c| +
          (5 * H * Real.log 3 + 2 * (5 * Real.log 3 + |Real.log c|)) +
          12 * Ccg * (d : ℝ) * (H + 2) * Real.log 3 := by
      positivity
    linarith
  refine ⟨C, hC, ?_⟩
  intro M m0 E epsilon h l hS hepsilonWindow hh hscale hgammaE hn z
  obtain ⟨hepsilon, hepsilonHalf⟩ := hepsilonWindow
  obtain ⟨_hC, hg⟩ := badEventMultiscaleGates (M := M) hCcg hc hH E.property
    hepsilon hepsilonHalf hh
  have hg' := hg hscale hgammaE
  obtain ⟨hadm, hroot, hNLTM, hELLIP⟩ := hg'
  apply hbad M m0 E hS hadm hroot l (l - (h : ℤ)) hn
  · intro _hlt
    have hle : l - (h : ℤ) ≤ l := by omega
    rw [scaleGapPos_of_le hle]
    convert hNLTM using 1
    norm_num
  · intro _hlt
    convert hELLIP using 1
    norm_num

end

end Algsuperdiff.Section3.Provider.BadEvents
