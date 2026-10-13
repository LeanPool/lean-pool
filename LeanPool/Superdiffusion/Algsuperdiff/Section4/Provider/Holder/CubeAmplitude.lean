/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CubeRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CampanatoFeed

/-!
# CubeAmplitude

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The amplitude of the localized Hölder estimate

The Campanato characterisation delivers a `C^{0,beta}` seminorm bound whose
constant is the one produced by the clipped-window family; the localized
estimate asks instead for the normalized seminorm `3 ^ (beta m) [·]_{C^{0,beta}}`
against the seed `‖u - (u)_{□_m}‖_{L²}` and the force leg
`sigma^{-1} 3 ^ (3m/2) [g]_{C^{0,1/2}}`.  This file performs that
rearrangement once, as an inequality between real numbers.

Three things happen.  The weight `3 ^ (beta m)` cancels the factor
`3 ^ ((1 - beta) m)` carried by the family's constant against the normalization
`3 ^ (-m)` of the seed, leaving the seed and the force leg unweighted.  The
residual scale factor `3 ^ ((1 - beta)(X + 1)/2)` is absorbed into
`3 ^ ((1 - alpha) 2X)` for every exponent `alpha` below `beta`, at the fixed
price `3`.  And the two weights of the bracket are replaced by their maximum.

## Main results

* `rpow_mul_campanatoGridConstant_le` — the rearrangement.
-/

namespace Algsuperdiff.Section4.Provider.Holder

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The scalar rearrangement of the estimate. -/
theorem rpow_mul_campanatoGridConstant_le
    {alpha beta Cosc Cdata S Kg sigma G Ud P2 : ℝ} {m : ℤ} {Xn : ℕ}
    (halpha0 : 0 < alpha) (hab : alpha ≤ beta) (hbeta1 : beta ≤ 1)
    (hCosc : 0 ≤ Cosc) (hCdata : 0 ≤ Cdata) (hS : 0 ≤ S) (hKg : 0 ≤ Kg)
    (hsigma : 0 < sigma) (hP2 : 0 ≤ P2)
    (hG : 0 ≤ G) (hGU : G ≤ Ud) (hUd : 0 ≤ Ud) :
    Real.rpow 3 (beta * (m : ℝ)) *
        (G * campanatoGridConstant beta m Xn Cosc
          ((3 : ℝ) ^ (-m) * (P2 * S) +
            Cdata * (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg))) ≤
      (6 * Ud * Cosc * max P2 Cdata) *
        Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) *
          (S + sigma⁻¹ * Real.rpow 3 (3 * (m : ℝ) / 2) * Kg) := by
  have hrfl : ∀ a b : ℝ, Real.rpow a b = a ^ b := fun _ _ => rfl
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  set q : ℝ := sigma⁻¹ * Real.rpow 3 (3 * (m : ℝ) / 2) * Kg with hqdef
  have hqnn : (0 : ℝ) ≤ q :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hsigma.le) (Real.rpow_nonneg (by norm_num) _)) hKg
  have hW : (3 : ℝ) ^ m *
      ((3 : ℝ) ^ (-m) * (P2 * S) +
        Cdata * (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg)) = P2 * S + Cdata * q := by
    have hpow : (3 : ℝ) ^ m * Real.rpow 3 ((m : ℝ) / 2) = Real.rpow 3 (3 * (m : ℝ) / 2) := by
      simp only [hrfl]
      rw [show ((3 : ℝ) ^ m) = (3 : ℝ) ^ (m : ℝ) from (Real.rpow_intCast 3 m).symm,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hcancel : (3 : ℝ) ^ m * (3 : ℝ) ^ (-m) = 1 := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      simp
    rw [hqdef]
    calc (3 : ℝ) ^ m *
          ((3 : ℝ) ^ (-m) * (P2 * S) +
            Cdata * (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg))
        = ((3 : ℝ) ^ m * (3 : ℝ) ^ (-m)) * (P2 * S) +
            Cdata * (sigma⁻¹ * ((3 : ℝ) ^ m * Real.rpow 3 ((m : ℝ) / 2)) * Kg) := by ring
      _ = P2 * S + Cdata * (sigma⁻¹ * Real.rpow 3 (3 * (m : ℝ) / 2) * Kg) := by
          rw [hcancel, hpow]; ring
  have hexp : Real.rpow 3 (beta * (m : ℝ)) *
      Real.rpow 3 ((1 - beta) * ((m : ℝ) + ((Xn : ℝ) + 1) / 2)) =
        (3 : ℝ) ^ m * Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) := by
    simp only [hrfl]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show ((3 : ℝ) ^ m) = (3 : ℝ) ^ (m : ℝ) from (Real.rpow_intCast 3 m).symm,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  -- regroup
  have hregroup : Real.rpow 3 (beta * (m : ℝ)) *
      (G * campanatoGridConstant beta m Xn Cosc
        ((3 : ℝ) ^ (-m) * (P2 * S) +
          Cdata * (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg))) =
      (G * Real.rpow 2 beta * Cosc *
          Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))) * (P2 * S + Cdata * q) := by
    rw [campanatoGridConstant]
    set D : ℝ := (3 : ℝ) ^ (-m) * (P2 * S) +
      Cdata * (sigma⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg) with hD
    calc Real.rpow 3 (beta * (m : ℝ)) *
          (G * (Real.rpow 2 beta * Cosc *
            Real.rpow 3 ((1 - beta) * ((m : ℝ) + ((Xn : ℝ) + 1) / 2)) * D))
        = (G * Real.rpow 2 beta * Cosc) *
            ((Real.rpow 3 (beta * (m : ℝ)) *
              Real.rpow 3 ((1 - beta) * ((m : ℝ) + ((Xn : ℝ) + 1) / 2))) * D) := by ring
      _ = (G * Real.rpow 2 beta * Cosc) *
            (((3 : ℝ) ^ m * Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))) * D) := by
          rw [hexp]
      _ = (G * Real.rpow 2 beta * Cosc *
            Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))) * ((3 : ℝ) ^ m * D) := by ring
      _ = (G * Real.rpow 2 beta * Cosc *
            Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))) * (P2 * S + Cdata * q) := by
          rw [hD, hW]
  rw [hregroup]
  -- the scalar factors
  have h2b : Real.rpow 2 beta ≤ 2 := by
    simp only [hrfl]
    calc (2 : ℝ) ^ beta ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hbeta1
      _ = 2 := Real.rpow_one 2
  have h2bnn : (0 : ℝ) ≤ Real.rpow 2 beta := Real.rpow_nonneg (by norm_num) _
  have hXnn : (0 : ℝ) ≤ (Xn : ℝ) := Nat.cast_nonneg Xn
  have hcast : (((2 * Xn : ℕ)) : ℝ) = 2 * (Xn : ℝ) := by push_cast; ring
  have hexpineq : (1 - beta) * (((Xn : ℝ) + 1) / 2) ≤
      (1 - alpha) * ((2 * Xn : ℕ) : ℝ) + 1 / 2 := by
    rw [hcast]
    have hp1 : (0 : ℝ) ≤ (beta - alpha) * ((Xn : ℝ) + 1) :=
      mul_nonneg (by linarith only [hab]) (by linarith only [hXnn])
    have hp2 : (0 : ℝ) ≤ (1 - alpha) * (Xn : ℝ) :=
      mul_nonneg (by linarith only [hab, hbeta1]) hXnn
    linarith only [hp1, hp2, halpha0]
  have hrp : Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) ≤
      3 * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) := by
    have hmono : Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) ≤
        Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ) + 1 / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpineq
    have hsplit : Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ) + 1 / 2) =
        Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) * Real.rpow 3 (1 / 2) := by
      simp only [hrfl]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hhalf : Real.rpow 3 (1 / 2 : ℝ) ≤ 3 := by
      simp only [hrfl]
      calc (3 : ℝ) ^ (1 / 2 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    have hbase : (0 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    calc Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))
        ≤ Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) * Real.rpow 3 (1 / 2) := by
          rw [← hsplit]; exact hmono
      _ ≤ Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) * 3 :=
          mul_le_mul_of_nonneg_left hhalf hbase
      _ = 3 * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) := by ring
  have hrpnn : (0 : ℝ) ≤ Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) :=
    Real.rpow_nonneg (by norm_num) _
  have hbase : (0 : ℝ) ≤ Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hA : G * Real.rpow 2 beta * Cosc *
      Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) ≤
        6 * Ud * Cosc * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) := by
    have ha : G * Real.rpow 2 beta ≤ Ud * 2 := mul_le_mul hGU h2b h2bnn hUd
    have hb : Cosc * Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) ≤
        Cosc * (3 * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hrp hCosc
    calc G * Real.rpow 2 beta * Cosc *
          Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))
        = (G * Real.rpow 2 beta) *
            (Cosc * Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))) := by ring
      _ ≤ (Ud * 2) * (Cosc * (3 * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)))) :=
          mul_le_mul ha hb (mul_nonneg hCosc hrpnn)
            (mul_nonneg hUd (by norm_num))
      _ = 6 * Ud * Cosc * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) := by ring
  have hAnn : (0 : ℝ) ≤ G * Real.rpow 2 beta * Cosc *
      Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hG h2bnn) hCosc) hrpnn
  have hWle : P2 * S + Cdata * q ≤ max P2 Cdata * (S + q) := by
    have h1 : P2 * S ≤ max P2 Cdata * S :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    have h2 : Cdata * q ≤ max P2 Cdata * q :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hqnn
    have : max P2 Cdata * (S + q) = max P2 Cdata * S + max P2 Cdata * q := by ring
    linarith only [h1, h2, this]
  have hWnn : (0 : ℝ) ≤ P2 * S + Cdata * q :=
    add_nonneg (mul_nonneg hP2 hS) (mul_nonneg hCdata hqnn)
  have hfinnn : (0 : ℝ) ≤ 6 * Ud * Cosc * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hUd) hCosc) hbase
  calc (G * Real.rpow 2 beta * Cosc *
          Real.rpow 3 ((1 - beta) * (((Xn : ℝ) + 1) / 2))) * (P2 * S + Cdata * q)
      ≤ (6 * Ud * Cosc * Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ))) *
          (max P2 Cdata * (S + q)) := mul_le_mul hA hWle hWnn hfinnn
    _ = (6 * Ud * Cosc * max P2 Cdata) *
          Real.rpow 3 ((1 - alpha) * ((2 * Xn : ℕ) : ℝ)) * (S + q) := by ring

end

end Algsuperdiff.Section4.Provider.Holder
