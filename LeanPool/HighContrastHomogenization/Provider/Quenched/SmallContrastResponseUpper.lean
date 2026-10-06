/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastYoungAbsorption
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileFiniteness
public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseAbsolute

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastResponseUpper

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Reabsorbed compact response bounds

This file converts the extended-nonnegative compact pre-Young estimates to
real inequalities only after finite row and weak bounds have been supplied.
It then absorbs the terminal energy and combines the primal and adjoint bounds
at the calibrated Schur loads.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory Set

open scoped ENNReal Matrix

noncomputable section

variable {d : ℕ}

private theorem ennreal_rpow_half_eq_ofReal_sqrt_toReal
    {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x.toReal) := by
  calc
    x ^ (1 / 2 : ℝ) =
        (ENNReal.ofReal x.toReal) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_toReal hx]
    _ = ENNReal.ofReal (x.toReal ^ (1 / 2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
    _ = ENNReal.ofReal (Real.sqrt x.toReal) := by
      rw [Real.sqrt_eq_rpow]

/-- A finite compact pre-Young estimate has the corresponding real form.
The explicit finiteness hypotheses prevent `toReal ⊤ = 0` from weakening the
claim. -/
theorem real_preYoung_of_compact
    {response energy defect C expo : ℝ} {row weak : ℝ≥0∞}
    (hresponse : 0 ≤ response) (hC : 0 ≤ C) (hexpo : 0 ≤ expo)
    (hrow : row ≠ ⊤) (hweak : weak ≠ ⊤)
    (hcompact :
      ENNReal.ofReal response ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt defect) *
            (ENNReal.ofReal (Real.sqrt defect) +
              ENNReal.ofReal (Real.sqrt energy) + row ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal C * ENNReal.ofReal expo *
            ENNReal.ofReal (Real.sqrt energy) *
              (ENNReal.ofReal (Real.sqrt energy) + row ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal C * weak) :
    response ≤
      C * Real.sqrt defect *
          (Real.sqrt defect + Real.sqrt energy + Real.sqrt row.toReal) +
        C * expo * Real.sqrt energy *
          (Real.sqrt energy + Real.sqrt row.toReal) + C * weak.toReal := by
  have hrowRoot := ennreal_rpow_half_eq_ofReal_sqrt_toReal hrow
  rw [hrowRoot, ← ENNReal.ofReal_toReal hweak] at hcompact
  let a : ℝ≥0∞ :=
    ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt defect) *
      (ENNReal.ofReal (Real.sqrt defect) +
        ENNReal.ofReal (Real.sqrt energy) +
          ENNReal.ofReal (Real.sqrt row.toReal))
  let b : ℝ≥0∞ :=
    ENNReal.ofReal C * ENNReal.ofReal expo *
      ENNReal.ofReal (Real.sqrt energy) *
        (ENNReal.ofReal (Real.sqrt energy) +
          ENNReal.ofReal (Real.sqrt row.toReal))
  let c : ℝ≥0∞ := ENNReal.ofReal C * ENNReal.ofReal weak.toReal
  have ha : a ≠ ⊤ := by
    dsimp only [a]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr
          ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
          ENNReal.ofReal_ne_top⟩)
  have hb : b ≠ ⊤ := by
    dsimp only [b]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have hc : c ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  change ENNReal.ofReal response ≤ a + b + c at hcompact
  have hab : a + b ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha, hb⟩
  have habc : a + b + c ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hab, hc⟩
  have hreal := ENNReal.toReal_mono habc hcompact
  rw [ENNReal.toReal_add hab hc, ENNReal.toReal_add ha hb] at hreal
  dsimp only [a, b, c] at hreal
  have hdefectEnergy :
      ENNReal.ofReal (Real.sqrt defect) +
          ENNReal.ofReal (Real.sqrt energy) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_add hdefectEnergy ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hresponse, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofReal hexpo,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg defect),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg energy),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg row.toReal),
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg] using hreal

/-- Finite uniform profile bounds and the compact pre-Young estimates give a
real bound for the calibrated primal--adjoint response supremum. -/
theorem centered_response_sup_le_of_reabsorbed_compact_preYoung
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (U : Domain d) {S SStar K : Mat d}
    {C expo eta D L W Z : ℝ}
    (hC : 0 ≤ C) (hexpo : 0 ≤ expo) (hexpoOne : expo ≤ 1)
    (heta : 0 < eta) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (habsorb : C * eta + (3 / 2 : ℝ) * C * expo ≤ 1 / 2)
    (tauMinus tauPlus EJMinus EJPlus centerMinus centerPlus : Vec d → ℝ)
    (rowMinus rowPlus weakMinus weakPlus : Vec d → ℝ≥0∞)
    (htauMinusNonneg : ∀ e, e ⬝ᵥ e = 1 → 0 ≤ tauMinus e)
    (htauPlusNonneg : ∀ e, e ⬝ᵥ e = 1 → 0 ≤ tauPlus e)
    (hEJMinusNonneg : ∀ e, e ⬝ᵥ e = 1 → 0 ≤ EJMinus e)
    (hEJPlusNonneg : ∀ e, e ⬝ᵥ e = 1 → 0 ≤ EJPlus e)
    (hcenterMinusNonneg : ∀ e, e ⬝ᵥ e = 1 → 0 ≤ centerMinus e)
    (hcenterPlusNonneg : ∀ e, e ⬝ᵥ e = 1 → 0 ≤ centerPlus e)
    (henergyMinus : ∀ e, e ⬝ᵥ e = 1 →
      EJMinus e ≤
        |Response.centeredResponse P U (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e -
            Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| +
          centerMinus e)
    (henergyPlus : ∀ e, e ⬝ᵥ e = 1 →
      EJPlus e ≤
        |Response.centeredAdjointResponse P U
          (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e +
            Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| +
          centerPlus e)
    (hpreYoungMinus : ∀ e, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |Response.centeredResponse P U (Response.centeredResponseLoadP S SStar K e)
            (Response.centeredResponseLoadQ S SStar K e -
              Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (tauMinus e)) *
            (ENNReal.ofReal (Real.sqrt (tauMinus e)) +
              ENNReal.ofReal (Real.sqrt (EJMinus e)) +
                rowMinus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal C * ENNReal.ofReal expo *
            ENNReal.ofReal (Real.sqrt (EJMinus e)) *
              (ENNReal.ofReal (Real.sqrt (EJMinus e)) +
                rowMinus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal C * weakMinus e)
    (hpreYoungPlus : ∀ e, e ⬝ᵥ e = 1 →
      ENNReal.ofReal
          |Response.centeredAdjointResponse P U
            (Response.centeredResponseLoadP S SStar K e)
            (Response.centeredResponseLoadQ S SStar K e +
              Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| ≤
        ENNReal.ofReal C * ENNReal.ofReal (Real.sqrt (tauPlus e)) *
            (ENNReal.ofReal (Real.sqrt (tauPlus e)) +
              ENNReal.ofReal (Real.sqrt (EJPlus e)) +
                rowPlus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal C * ENNReal.ofReal expo *
            ENNReal.ofReal (Real.sqrt (EJPlus e)) *
              (ENNReal.ofReal (Real.sqrt (EJPlus e)) +
                rowPlus e ^ (1 / 2 : ℝ)) +
          ENNReal.ofReal C * weakPlus e)
    (htauMinus : ∀ e, e ⬝ᵥ e = 1 → tauMinus e ≤ D)
    (htauPlus : ∀ e, e ⬝ᵥ e = 1 → tauPlus e ≤ D)
    (hrowMinus : ∀ e, e ⬝ᵥ e = 1 →
      rowMinus e ≤ ENNReal.ofReal L)
    (hrowPlus : ∀ e, e ⬝ᵥ e = 1 →
      rowPlus e ≤ ENNReal.ofReal L)
    (hweakMinus : ∀ e, e ⬝ᵥ e = 1 →
      weakMinus e ≤ ENNReal.ofReal W)
    (hweakPlus : ∀ e, e ⬝ᵥ e = 1 →
      weakPlus e ≤ ENNReal.ofReal W)
    (hcenterMinus : ∀ e, e ⬝ᵥ e = 1 → centerMinus e ≤ Z)
    (hcenterPlus : ∀ e, e ⬝ᵥ e = 1 → centerPlus e ≤ Z) :
    sSup
        ((fun e : Vec d ↦
            |Response.centeredResponse P U (Response.centeredResponseLoadP S SStar K e)
                (Response.centeredResponseLoadQ S SStar K e -
                  Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| +
              |Response.centeredAdjointResponse P U
                (Response.centeredResponseLoadP S SStar K e)
                (Response.centeredResponseLoadQ S SStar K e +
                  Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)|) ''
          {e : Vec d | e ⬝ᵥ e = 1}) ≤
      4 * C * ((3 / 2 + 1 / (4 * eta)) * D + L + W) + 2 * Z := by
  let linear : ℝ := (3 / 2 + 1 / (4 * eta)) * D + L + W
  have hcoef : 0 ≤ (3 / 2 : ℝ) + 1 / (4 * eta) := by positivity
  have hpointwise (e : Vec d) (he : e ⬝ᵥ e = 1) :
      |Response.centeredResponse P U (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e -
            Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| ≤
          2 * C * linear + Z ∧
        |Response.centeredAdjointResponse P U
          (Response.centeredResponseLoadP S SStar K e)
          (Response.centeredResponseLoadQ S SStar K e +
            Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)| ≤
          2 * C * linear + Z := by
    have hrowMinusTop : rowMinus e ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hrowMinus e he)
    have hrowPlusTop : rowPlus e ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hrowPlus e he)
    have hweakMinusTop : weakMinus e ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hweakMinus e he)
    have hweakPlusTop : weakPlus e ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hweakPlus e he)
    have hrowMinusReal : (rowMinus e).toReal ≤ L :=
      Response.toReal_le_of_le_ofReal hL (hrowMinus e he)
    have hrowPlusReal : (rowPlus e).toReal ≤ L :=
      Response.toReal_le_of_le_ofReal hL (hrowPlus e he)
    have hweakMinusReal : (weakMinus e).toReal ≤ W :=
      Response.toReal_le_of_le_ofReal hW (hweakMinus e he)
    have hweakPlusReal : (weakPlus e).toReal ≤ W :=
      Response.toReal_le_of_le_ofReal hW (hweakPlus e he)
    have hminusPre := real_preYoung_of_compact
      (abs_nonneg (Response.centeredResponse P U
        (Response.centeredResponseLoadP S SStar K e)
        (Response.centeredResponseLoadQ S SStar K e -
          Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)))
      hC hexpo hrowMinusTop hweakMinusTop (hpreYoungMinus e he)
    have hplusPre := real_preYoung_of_compact
      (abs_nonneg (Response.centeredAdjointResponse P U
        (Response.centeredResponseLoadP S SStar K e)
        (Response.centeredResponseLoadQ S SStar K e +
          Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)))
      hC hexpo hrowPlusTop hweakPlusTop (hpreYoungPlus e he)
    have hminus := response_le_linear_of_preYoung
      (abs_nonneg (Response.centeredResponse P U
        (Response.centeredResponseLoadP S SStar K e)
        (Response.centeredResponseLoadQ S SStar K e -
          Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)))
      (hEJMinusNonneg e he) (htauMinusNonneg e he) ENNReal.toReal_nonneg
      (hcenterMinusNonneg e he) hC hexpo hexpoOne heta
      (henergyMinus e he) hminusPre habsorb
    have hplus := response_le_linear_of_preYoung
      (abs_nonneg (Response.centeredAdjointResponse P U
        (Response.centeredResponseLoadP S SStar K e)
        (Response.centeredResponseLoadQ S SStar K e +
          Response.responseSkew K *ᵥ Response.centeredResponseLoadP S SStar K e)))
      (hEJPlusNonneg e he) (htauPlusNonneg e he) ENNReal.toReal_nonneg
      (hcenterPlusNonneg e he) hC hexpo hexpoOne heta
      (henergyPlus e he) hplusPre habsorb
    have hminusInner :
        (3 / 2 + 1 / (4 * eta)) * tauMinus e +
            (rowMinus e).toReal + (weakMinus e).toReal ≤ linear := by
      dsimp only [linear]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (htauMinus e he) hcoef)
          hrowMinusReal)
        hweakMinusReal
    have hplusInner :
        (3 / 2 + 1 / (4 * eta)) * tauPlus e +
            (rowPlus e).toReal + (weakPlus e).toReal ≤ linear := by
      dsimp only [linear]
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (htauPlus e he) hcoef)
          hrowPlusReal)
        hweakPlusReal
    constructor
    · calc
        _ ≤ 2 * C *
              ((3 / 2 + 1 / (4 * eta)) * tauMinus e +
                (rowMinus e).toReal + (weakMinus e).toReal) +
            centerMinus e := hminus
        _ ≤ 2 * C * linear + Z := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hminusInner (by positivity))
            (hcenterMinus e he)
    · calc
        _ ≤ 2 * C *
              ((3 / 2 + 1 / (4 * eta)) * tauPlus e +
                (rowPlus e).toReal + (weakPlus e).toReal) +
            centerPlus e := hplus
        _ ≤ 2 * C * linear + Z := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hplusInner (by positivity))
            (hcenterPlus e he)
  apply csSup_le
  · have i0 : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    let e0 : Vec d := Pi.single i0 1
    have he0 : e0 ⬝ᵥ e0 = 1 := by
      simp [e0, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    exact ⟨_, ⟨e0, he0, rfl⟩⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := hx
    obtain ⟨hminus, hplus⟩ := hpointwise e he
    calc
      _ ≤ (2 * C * linear + Z) + (2 * C * linear + Z) :=
        add_le_add hminus hplus
      _ = 4 * C * linear + 2 * Z := by ring
      _ = 4 * C * ((3 / 2 + 1 / (4 * eta)) * D + L + W) +
          2 * Z := by rfl

end

end HCPolySupport.HighContrast.Quenched
