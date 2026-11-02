/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourBoundaryBudgetErrorWeighted

/-!
# StepFourCollapseErrorWeighted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The `𝓔`-multiplied flat leg -/

/-- **The `L²`-datum leg conversion.**

The error-weighted general clause states its flat `∇h` leg `𝓔`-multiplied, so the
excess-decay display's fourth leg reads `C s^{-6} · 𝓔 · 3^{n-2} · Hl2`.  The
flat weight is `edLeg_four_le`'s own `3^{-n} 3^{n-2} = 1/9`; what is new is
that the `𝓔` factor is spent against `𝓔 ≤ ε_j`, so the leg is delivered with
`ε_j` in place of `𝓔`. -/
theorem edLeg_four_le_errorWeighted {n : ℤ} {Cst s Efl Hl2 epsj Khinf : ℝ}
    (hcoef : 0 ≤ Cst * s ^ (-(6 : ℝ))) (hEfl0 : 0 ≤ Efl) (hEfl : Efl ≤ epsj)
    (hKhinf : 0 ≤ Khinf) (hHl2 : Hl2 ≤ Khinf) :
    (3 : ℝ) ^ (-n) *
        (Cst * s ^ (-(6 : ℝ)) * Efl * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2) ≤
      Cst * s ^ (-(6 : ℝ)) * epsj * ((1 / 9) * Khinf) := by
  have hexp : (3 : ℝ) ^ (-n) *
      (Cst * s ^ (-(6 : ℝ)) * Efl * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2) =
      Cst * s ^ (-(6 : ℝ)) * Efl *
        (((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ))) * Hl2) := by
    ring
  rw [hexp, three_weight_flat n]
  have ha0 : (0 : ℝ) ≤ Cst * s ^ (-(6 : ℝ)) * Efl := mul_nonneg hcoef hEfl0
  have hd0 : (0 : ℝ) ≤ (1 / 9 : ℝ) * Khinf := by linarith only [hKhinf]
  have h1 : Cst * s ^ (-(6 : ℝ)) * Efl * ((1 / 9) * Hl2) ≤
      Cst * s ^ (-(6 : ℝ)) * Efl * ((1 / 9) * Khinf) :=
    mul_le_mul_of_nonneg_left (by linarith only [hHl2]) ha0
  have h2 : Cst * s ^ (-(6 : ℝ)) * Efl * ((1 / 9) * Khinf) ≤
      Cst * s ^ (-(6 : ℝ)) * epsj * ((1 / 9) * Khinf) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEfl hcoef) hd0
  linarith only [h1, h2]

/-! ## 2. The bracket bound -/

/-- **The bracket bound**: the whole excess-decay remainder at the error-weighted
clause, split into the absorbable contraction `(C_ε ε_j) E`, the `ε_j |∇ℓ|`
leg, and `δ_n` in its `stepFourDeltaOutErrorWeighted` shape.  Legs one, two and
three are verbatim; only the fourth is re-run. -/
theorem edBracket_le_errorWeighted {n : ℤ}
    {Crem Vd Cst s Efl Osc Gav Gsem Hsem Hl2 SigInv SigInvN : ℝ}
    {epsj Kg Kh Khinf Cosc E0 S0 : ℝ}
    (hCV : 0 ≤ Crem * Vd) (hs : 0 ≤ s)
    (hcoef4 : 0 ≤ Cst * s ^ (-(4 : ℝ))) (hcoef6 : 0 ≤ Cst * s ^ (-(6 : ℝ)))
    (hcoef7 : 0 ≤ Cst * s ^ (-(7 : ℝ))) (hw : 0 ≤ s ^ (-(3 / 2 : ℝ)))
    (hEfl0 : 0 ≤ Efl) (hEfl : Efl ≤ epsj) (heps0 : 0 ≤ epsj)
    (hOsc0 : 0 ≤ (3 : ℝ) ^ (-n) * Osc)
    (hOsc : (3 : ℝ) ^ (-n) * Osc ≤ Cosc * (E0 + S0))
    (hGav0 : 0 ≤ Gav) (hGav : Gav ≤ Khinf)
    (hSig : SigInv ≤ 8 * SigInvN) (hSigN0 : 0 ≤ SigInvN)
    (hGsem0 : 0 ≤ Gsem) (hKg0 : 0 ≤ Kg)
    (hGsem : Gsem ≤ Kg * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hKh0 : 0 ≤ Kh)
    (hHsem : Hsem ≤ Kh * (3 : ℝ) ^ (((n + 1 : ℤ) : ℝ) * (1 / 2 - s)))
    (hHl2 : Hl2 ≤ Khinf) :
    Crem * ((3 : ℝ) ^ (-n) * (Vd *
        (Cst * s ^ (-(4 : ℝ)) * Efl *
            (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav) +
          Cst * s ^ (-(7 : ℝ)) * SigInv *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem +
          Cst * s ^ (-(6 : ℝ)) *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem +
            Cst * s ^ (-(6 : ℝ)) * Efl *
              (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2))) ≤
      stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * E0 +
        (stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * S0 +
          stepFourDeltaOutErrorWeighted Crem Vd Cst s epsj Khinf SigInvN Kg Kh n) := by
  have hKhinf : (0 : ℝ) ≤ Khinf := le_trans hGav0 hGav
  have h1 := edLeg_one_le (n := n) (Cst := Cst) (s := s) (Efl := Efl) (Osc := Osc)
    (Gav := Gav) (epsj := epsj) (Cosc := Cosc) (Khinf := Khinf) (E0 := E0) (S0 := S0)
    hcoef4 hw hEfl heps0 hOsc0 hOsc hGav0 hGav
  have h2 := edLeg_two_le (n := n) (Cst := Cst) (s := s) (SigInv := SigInv)
    (SigInvN := SigInvN) (Gsem := Gsem) (Kg := Kg) hcoef7 hs hSig hSigN0 hGsem0 hKg0
    hGsem
  have h3 := edLeg_three_le (n := n) (Cst := Cst) (s := s) (Hsem := Hsem) (Kh := Kh)
    hcoef6 hs hKh0 hHsem
  have h4 := edLeg_four_le_errorWeighted (n := n) (Cst := Cst) (s := s) (Efl := Efl)
    (Hl2 := Hl2) (epsj := epsj) (Khinf := Khinf) hcoef6 hEfl0 hEfl hKhinf hHl2
  have hsum :
      (3 : ℝ) ^ (-n) *
          (Cst * s ^ (-(4 : ℝ)) * Efl *
            (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav)) +
        ((3 : ℝ) ^ (-n) *
            (Cst * s ^ (-(7 : ℝ)) * SigInv *
              (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) +
          ((3 : ℝ) ^ (-n) *
              (Cst * s ^ (-(6 : ℝ)) *
                (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) +
            (3 : ℝ) ^ (-n) *
              (Cst * s ^ (-(6 : ℝ)) * Efl *
                (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2))) ≤
        Cst * s ^ (-(4 : ℝ)) * epsj *
            (Cosc * (E0 + S0) + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) +
          (8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) +
            (Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
              Cst * s ^ (-(6 : ℝ)) * epsj * ((1 / 9) * Khinf))) := by
    linarith only [h1, h2, h3, h4]
  have hmul := mul_le_mul_of_nonneg_left hsum hCV
  have hleft : Crem * ((3 : ℝ) ^ (-n) * (Vd *
      (Cst * s ^ (-(4 : ℝ)) * Efl *
          (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav) +
        Cst * s ^ (-(7 : ℝ)) * SigInv *
            (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem +
        Cst * s ^ (-(6 : ℝ)) *
            (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem +
          Cst * s ^ (-(6 : ℝ)) * Efl *
            (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2)))
      = Crem * Vd *
        ((3 : ℝ) ^ (-n) *
            (Cst * s ^ (-(4 : ℝ)) * Efl *
              (Osc + s ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Gav)) +
          ((3 : ℝ) ^ (-n) *
              (Cst * s ^ (-(7 : ℝ)) * SigInv *
                (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Gsem) +
            ((3 : ℝ) ^ (-n) *
                (Cst * s ^ (-(6 : ℝ)) *
                  (3 : ℝ) ^ ((1 + s) * ((n - 2 : ℤ) : ℝ)) * Hsem) +
              (3 : ℝ) ^ (-n) *
                (Cst * s ^ (-(6 : ℝ)) * Efl *
                  (3 : ℝ) ^ (((n - 2 : ℤ) : ℝ)) * Hl2)))) := by
    ring
  have hright : Crem * Vd *
      (Cst * s ^ (-(4 : ℝ)) * epsj *
          (Cosc * (E0 + S0) + s ^ (-(3 / 2 : ℝ)) * (1 / 9) * Khinf) +
        (8 * (Cst * s ^ (-(7 : ℝ))) * (SigInvN * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kg)) +
          (Cst * s ^ (-(6 : ℝ)) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Kh) +
            Cst * s ^ (-(6 : ℝ)) * epsj * ((1 / 9) * Khinf))))
      = stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * E0 +
        (stepFourEpsCoeff Crem Vd Cst s Cosc * epsj * S0 +
          stepFourDeltaOutErrorWeighted Crem Vd Cst s epsj Khinf SigInvN Kg Kh n) := by
    rw [stepFourEpsCoeff, stepFourDeltaOutErrorWeighted]
    ring
  linarith only [hmul, hleft, hright]

end

end Algsuperdiff.Section4.Provider.Regularity
