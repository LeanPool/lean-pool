/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.RootScalePhysicalLipschitz
public import LeanPool.HighContrastHomogenization.Provider.Quenched.CoupledMixingScaleDecay

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1FinitePrefixAbsorption

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-prefix absorption for physical C1 estimates

A simultaneous-slope estimate beginning at a bounded larger radius extends to
the original radius.  On the finite prefix, normalized energy monotonicity and
homothetic ellipsoid volume scaling supply the missing bound.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

private theorem one_le_rpow_mul_rpow_div
    {q r R eta : ℝ} (hq : 1 ≤ q) (hr : 0 < r) (hR : 0 < R)
    (heta : 0 ≤ eta) (hRq : R ≤ q * r) :
    1 ≤ q ^ eta * (r / R) ^ eta := by
  have hratio : 1 ≤ q * (r / R) := by
    rw [show q * (r / R) = (q * r) / R by ring]
    exact (le_div_iff₀ hR).2 (by simpa only [one_mul] using hRq)
  calc
    1 = (1 : ℝ) ^ eta := (Real.one_rpow eta).symm
    _ ≤ (q * (r / R)) ^ eta :=
      Real.rpow_le_rpow (by norm_num) hratio heta
    _ = q ^ eta * (r / R) ^ eta :=
      Real.mul_rpow (zero_le_one.trans hq) (div_nonneg hr.le hR.le)

private theorem rpow_div_le_rpow_mul_rpow_div
    {q r R rStart eta : ℝ} (hq : 1 ≤ q) (hr : 0 < r)
    (hR : 0 < R) (hStart0 : 0 < rStart) (heta : 0 ≤ eta)
    (hStart : rStart ≤ q * r) :
    (rStart / R) ^ eta ≤ q ^ eta * (r / R) ^ eta := by
  have hdiv : rStart / R ≤ q * (r / R) := by
    rw [show q * (r / R) = (q * r) / R by ring]
    exact div_le_div_of_nonneg_right hStart hR.le
  calc
    (rStart / R) ^ eta ≤ (q * (r / R)) ^ eta :=
      Real.rpow_le_rpow (div_nonneg hStart0.le hR.le) hdiv heta
    _ = q ^ eta * (r / R) ^ eta :=
      Real.mul_rpow (zero_le_one.trans hq) (div_nonneg hr.le hR.le)

omit [NeZero d] in
private theorem zero_slope_gradient_ae_of_linear
    {a : CoeffSpace d}
    {gradPhi : Vec d → CoeffSpace d → Vec d → Vec d}
    (hlinear : ∀ (c : ℝ) (e e' : Vec d),
      gradPhi (c • e + e') a =ᵐ[volume]
        fun x ↦ c • gradPhi e a x + gradPhi e' a x) :
    gradPhi 0 a =ᵐ[volume] (fun _ ↦ 0) := by
  filter_upwards [hlinear (-1) 0 0] with y hy
  simpa only [smul_zero, zero_add, neg_one_smul, neg_add_cancel] using hy

omit [NeZero d] in
/-- A delayed physical C1 estimate extends through a bounded homothetic
prefix.  The same slope is retained whenever the delayed range is nonempty;
when the whole interval lies in the prefix, the zero slope is used. -/
theorem exists_rangeCompletePhysicalC1_of_boundedStart
    (L : ℕ) (eta A : ℝ) (heta : 0 ≤ eta) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (abar : Mat d), (symmPart abar).PosDef →
        ∀ (a : CoeffSpace d) (x : ℝ), 1 ≤ x →
          ∀ (gradPhi : Vec d → CoeffSpace d → Vec d → Vec d),
            (∀ (c : ℝ) (e e' : Vec d),
              gradPhi (c • e + e') a =ᵐ[volume]
                fun y ↦ c • gradPhi e a y + gradPhi e' a y) →
            ∀ R : ℝ, x ≤ R →
              ∀ (u : Vec d → ℝ) (Du : Vec d → Vec d),
                MemH1a (fun y ↦ a.1 y) (ellipsoid abar R) u Du →
                IsWeakSolutionOn (fun y ↦ a.1 y) (ellipsoid abar R) Du →
                (let rStart := (3 : ℝ) ^
                    (Quenched.triadicCeilingIndex x + L);
                  rStart ≤ R →
                    ∃ e : Vec d, ∀ r : ℝ, r ∈ Icc rStart R →
                      weightedGradNorm (fun y ↦ a.1 y)
                          (ellipsoid abar r)
                          (fun y ↦ Du y - (e + gradPhi e a y)) ≤
                        ENNReal.ofReal
                            (A * (r / R) ^ eta) *
                          weightedGradNorm (fun y ↦ a.1 y)
                            (ellipsoid abar R) Du) →
                  ∃ e : Vec d, ∀ r : ℝ, r ∈ Icc x R →
                    weightedGradNorm (fun y ↦ a.1 y)
                        (ellipsoid abar r)
                        (fun y ↦ Du y - (e + gradPhi e a y)) ≤
                      ENNReal.ofReal
                          (K * (r / R) ^ eta) *
                        weightedGradNorm (fun y ↦ a.1 y)
                          (ellipsoid abar R) Du := by
  let q : ℝ := (3 : ℝ) ^ (L + 1)
  let P : ℝ≥0∞ := (ENNReal.ofReal (q ^ d)) ^ (1 / 2 : ℝ)
  let D : ℝ≥0∞ := ENNReal.ofReal (q ^ eta)
  let Aen : ℝ≥0∞ := ENNReal.ofReal A
  let B : ℝ≥0∞ := Aen + P * Aen * D + P * D
  let K : ℝ := B.toReal + 1
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact one_le_pow₀ (by norm_num)
  have hPtop : P ≠ ⊤ := by
    dsimp only [P]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hDtop : D ≠ ⊤ := by
    dsimp only [D]
    exact ENNReal.ofReal_ne_top
  have hAtop : Aen ≠ ⊤ := by
    dsimp only [Aen]
    exact ENNReal.ofReal_ne_top
  have hBtop : B ≠ ⊤ := by
    dsimp only [B]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨hAtop, ENNReal.mul_ne_top (ENNReal.mul_ne_top hPtop hAtop) hDtop⟩,
        ENNReal.mul_ne_top hPtop hDtop⟩
  have hBK : B ≤ ENNReal.ofReal K := by
    calc
      B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBtop).symm
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (by
        dsimp only [K]
        exact le_add_of_nonneg_right zero_le_one)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro abar hS a x hx gradPhi hlinear R hxR u Du _hu _hweak hdelayed
  have hzero := zero_slope_gradient_ae_of_linear hlinear
  let rStart : ℝ := (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hRpos : 0 < R := hxpos.trans_le hxR
  have hxStart : x ≤ rStart := by
    calc
      x ≤ (3 : ℝ) ^ Quenched.triadicCeilingIndex x :=
        Quenched.le_pow_triadicCeilingIndex hx
      _ ≤ (3 : ℝ) ^ (Quenched.triadicCeilingIndex x + L) := by
        rw [pow_add]
        exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      _ = rStart := rfl
  have hStartQx : rStart ≤ q * x := by
    have hceil := Quenched.pow_triadicCeilingIndex_le_three_mul hx
    dsimp only [rStart, q]
    rw [pow_add, pow_succ]
    calc
      (3 : ℝ) ^ Quenched.triadicCeilingIndex x * (3 : ℝ) ^ L ≤
          (3 * x) * (3 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_right hceil (by positivity)
      _ = ((3 : ℝ) ^ L * 3) * x := by ring
  by_cases hStartR : rStart ≤ R
  · obtain ⟨e, he⟩ := hdelayed hStartR
    refine ⟨e, ?_⟩
    intro r hrange
    have hrpos : 0 < r := hxpos.trans_le hrange.1
    by_cases hStartR' : rStart ≤ r
    · have hrow := he r ⟨hStartR', hrange.2⟩
      have hAB : Aen ≤ B := by
        dsimp only [B]
        exact (le_add_of_nonneg_right bot_le).trans
          (le_add_of_nonneg_right bot_le)
      have hcoeff : ENNReal.ofReal (A * (r / R) ^ eta) ≤
          ENNReal.ofReal (K * (r / R) ^ eta) := by
        rw [ENNReal.ofReal_mul hA.le,
          ENNReal.ofReal_mul hK.le]
        simpa only [mul_comm] using
          mul_le_mul_left (hAB.trans hBK)
            (ENNReal.ofReal ((r / R) ^ eta))
      exact hrow.trans (by
        simpa only [mul_comm] using
          mul_le_mul_left hcoeff
            (weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du))
    · have hrStart : r ≤ rStart := le_of_not_ge hStartR'
      have hStartQr : rStart ≤ q * r :=
        hStartQx.trans
          (mul_le_mul_of_nonneg_left hrange.1 (zero_le_one.trans hq))
      have hpref := weightedGradNorm_ellipsoid_le_of_le_mul abar hS
        hrpos hrStart hq hStartQr (fun y ↦ a.1 y)
        (fun y ↦ Du y - (e + gradPhi e a y))
      have htop := he rStart ⟨le_rfl, hStartR⟩
      have hrateReal := rpow_div_le_rpow_mul_rpow_div hq hrpos hRpos
        (by positivity) heta hStartQr
      have hrate : ENNReal.ofReal ((rStart / R) ^ eta) ≤
          D * ENNReal.ofReal ((r / R) ^ eta) := by
        dsimp only [D]
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) eta)]
        exact ENNReal.ofReal_le_ofReal hrateReal
      have hPAB : P * Aen * D ≤ B := by
        dsimp only [B]
        exact (le_add_of_nonneg_left (show 0 ≤ Aen from bot_le)).trans
          (le_add_of_nonneg_right bot_le)
      calc
        weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r)
            (fun y ↦ Du y - (e + gradPhi e a y)) ≤
          P * weightedGradNorm (fun y ↦ a.1 y)
            (ellipsoid abar rStart)
            (fun y ↦ Du y - (e + gradPhi e a y)) := by
              simpa only [P, q] using hpref
        _ ≤ P * (ENNReal.ofReal (A * (rStart / R) ^ eta) *
            weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du) := by
                simpa only [mul_comm] using mul_le_mul_left htop P
        _ ≤ (P * Aen * D) * ENNReal.ofReal ((r / R) ^ eta) *
            weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du := by
              rw [ENNReal.ofReal_mul hA.le]
              have h := mul_le_mul_left
                (mul_le_mul_left hrate (P * Aen))
                (weightedGradNorm (fun y ↦ a.1 y)
                  (ellipsoid abar R) Du)
              simpa only [mul_assoc, mul_left_comm, mul_comm] using h
        _ ≤ ENNReal.ofReal (K * (r / R) ^ eta) *
            weightedGradNorm (fun y ↦ a.1 y)
              (ellipsoid abar R) Du := by
              rw [ENNReal.ofReal_mul hK.le]
              have h := mul_le_mul_left
                (mul_le_mul_left (hPAB.trans hBK)
                  (ENNReal.ofReal ((r / R) ^ eta)))
                (weightedGradNorm (fun y ↦ a.1 y)
                  (ellipsoid abar R) Du)
              simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · have hRStart : R ≤ rStart := le_of_not_ge hStartR
    refine ⟨0, ?_⟩
    intro r hrange
    have hrpos : 0 < r := hxpos.trans_le hrange.1
    have hRq : R ≤ q * r := hRStart.trans
      (hStartQx.trans
        (mul_le_mul_of_nonneg_left hrange.1 (zero_le_one.trans hq)))
    have hpref := weightedGradNorm_ellipsoid_le_of_le_mul abar hS
      hrpos hrange.2 hq hRq (fun y ↦ a.1 y) Du
    have hresidual : weightedGradNorm (fun y ↦ a.1 y)
        (ellipsoid abar r) (fun y ↦ Du y - (0 + gradPhi 0 a y)) =
        weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r) Du := by
      apply weightedGradNorm_congr_ae
      filter_upwards [ae_restrict_of_ae hzero] with y hy
      rw [hy]
      simp
    have hrateReal := one_le_rpow_mul_rpow_div hq hrpos hRpos heta hRq
    have hrate : 1 ≤ D * ENNReal.ofReal ((r / R) ^ eta) := by
      dsimp only [D]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg (by positivity) eta)]
      exact ENNReal.ofReal_le_ofReal hrateReal
    have hPDB : P * D ≤ B := by
      dsimp only [B]
      exact le_add_of_nonneg_left (show 0 ≤ Aen + P * Aen * D from bot_le)
    rw [hresidual]
    calc
      weightedGradNorm (fun y ↦ a.1 y) (ellipsoid abar r) Du ≤
          P * weightedGradNorm (fun y ↦ a.1 y)
            (ellipsoid abar R) Du := by simpa only [P, q] using hpref
      _ ≤ (P * D * ENNReal.ofReal ((r / R) ^ eta)) *
          weightedGradNorm (fun y ↦ a.1 y)
            (ellipsoid abar R) Du := by
            have h := mul_le_mul_left
              (mul_le_mul_left hrate P)
              (weightedGradNorm (fun y ↦ a.1 y)
                (ellipsoid abar R) Du)
            simpa only [one_mul, mul_assoc, mul_left_comm, mul_comm] using h
      _ ≤ ENNReal.ofReal (K * (r / R) ^ eta) *
          weightedGradNorm (fun y ↦ a.1 y)
            (ellipsoid abar R) Du := by
            rw [ENNReal.ofReal_mul hK.le]
            have h := mul_le_mul_left
              (mul_le_mul_left (hPDB.trans hBK)
                (ENNReal.ofReal ((r / R) ^ eta)))
              (weightedGradNorm (fun y ↦ a.1 y)
                (ellipsoid abar R) Du)
            simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end

end Root
end HighContrast
end HCPolySupport
