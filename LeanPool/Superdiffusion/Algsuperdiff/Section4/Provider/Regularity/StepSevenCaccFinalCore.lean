/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenLambdaSlots
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2

/-!
# StepSevenCaccFinalCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The square-root conversion on abstract reals -/

/-- **The form conversion.**  A squared two-term bound becomes an energy-norm
two-term bound with the SAME single constant `√P`:

```text
  E ≤ P·(A + B)   ⟹   √E ≤ √P·√A + √P·√B .
```

This is the whole's residue at the level of reals; everything else in the
residue is carrier identification. -/
theorem sqrt_le_of_le_mul_add {E P A B : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : E ≤ P * (A + B)) :
    Real.sqrt E ≤ Real.sqrt P * Real.sqrt A + Real.sqrt P * Real.sqrt B := by
  have h1 : Real.sqrt E ≤ Real.sqrt (P * (A + B)) := Real.sqrt_le_sqrt h
  have h2 : Real.sqrt (P * (A + B)) = Real.sqrt P * Real.sqrt (A + B) :=
    Real.sqrt_mul hP _
  have h3 : Real.sqrt (A + B) ≤ Real.sqrt A + Real.sqrt B :=
    HCPolySupport.sqrt_add_le_add_sqrt_of_nonneg hA hB
  have h4 : Real.sqrt P * Real.sqrt (A + B) ≤
      Real.sqrt P * (Real.sqrt A + Real.sqrt B) :=
    mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  have h5 : Real.sqrt P * (Real.sqrt A + Real.sqrt B) =
      Real.sqrt P * Real.sqrt A + Real.sqrt P * Real.sqrt B := by ring
  linarith only [h1, h2.ge, h2.le, h4, h5.ge, h5.le]

/-! ## 2. The three exact square roots -/

/-- **The `L²` square root is definitional.**  `√(⨍_V f²) = ‖f‖_{L²(V)}`:
CoarseGraining's `normalizedL2SqOnSet` and §4.3's `normalizedL2On` are the same
object under one square root, with no constant and no hypothesis. -/
theorem sqrt_normalizedL2SqOnSet (V : Set (Vec d)) (f : Vec d → ℝ) :
    Real.sqrt (normalizedL2SqOnSet V f) = normalizedL2On V f := rfl

/-- **The scale weight's square root.**  `√(3^{-2j}) = 3^{-j}`, in the two
spellings the two sides use: the Caccioppoli carries the `Real.rpow` form, the
§4.4 windows the `zpow` form. -/
theorem sqrt_rpow_three_neg_two_mul (j : ℤ) :
    Real.sqrt (Real.rpow (3 : ℝ) (-2 * ((j : ℤ) : ℝ))) = (3 : ℝ) ^ (-j) := by
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hsqrt : Real.sqrt (Real.rpow (3 : ℝ) (-2 * (j : ℝ))) =
      Real.rpow (Real.rpow (3 : ℝ) (-2 * (j : ℝ))) (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow _
  have hmul : Real.rpow (Real.rpow (3 : ℝ) (-2 * (j : ℝ))) (1 / 2 : ℝ) =
      Real.rpow (3 : ℝ) (-2 * (j : ℝ) * (1 / 2 : ℝ)) := (Real.rpow_mul h3 _ _).symm
  have hexp : -2 * (j : ℝ) * (1 / 2 : ℝ) = (((-j : ℤ)) : ℝ) := by push_cast; ring
  have hint : Real.rpow (3 : ℝ) ((((-j : ℤ)) : ℝ)) = (3 : ℝ) ^ (-j) :=
    Real.rpow_intCast 3 (-j)
  rw [hsqrt, hmul, hexp, hint]

/-- **The Caccioppoli's own ellipticity coefficient is positive.**  `λ_{t,1}` at a
positive index is positive, so its square root and its inverse are honest
objects. -/
theorem stepSevenCaccLambda_pos [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {t : ℝ} (ht : 0 < t) : 0 < Ch02.lambdaS Q t a := by
  rw [Ch02.lambdaS]
  exact Ch02.lambdaSq_finite_pos Q a ht (by norm_num)

/-! ## 3. The forcing factor at the pin -/

/-- **The Caccioppoli's forcing factor at the §4.4 pin**, `t^{-8}(1-2t)^{-1}` at `t
= 1/8`. -/
def stepSevenCaccForcingFactor : ℝ :=
  Real.rpow stepSevenCaccT (-8 : ℝ) / (1 - 2 * stepSevenCaccT)

theorem stepSevenCaccForcingFactor_nonneg : 0 ≤ stepSevenCaccForcingFactor := by
  have hnum : (0 : ℝ) ≤ Real.rpow stepSevenCaccT (-8 : ℝ) :=
    Real.rpow_nonneg stepSevenCaccT_pos.le _
  have hden : (0 : ℝ) ≤ 1 - 2 * stepSevenCaccT := by
    rw [stepSevenCaccT_eq]; norm_num
  rw [stepSevenCaccForcingFactor]
  exact div_nonneg hnum hden

/-! ## 4. `l.coarse.grained.Caccioppoli.RHS` in the `hcacc` slot shape -/

/-- ** residue, first half: the Caccioppoli in `hcacc` shape.**

`StepSevenCaccMatching.exists_stepSevenCaccioppoliEnergy` converted to the
energy-norm (square-root) two-term form that
`StepSevenCaccGradient.stepSevenGradientWithShom` consumes:

```text
  √(⨍_{core} ∇u·𝐚∇u)
    ≤ √P · ( √λ_{1/8,1} · ( 3^{-scale} ‖u-c‖_{L²(□_Q)} ) )
      + √P · ( √(F·λ_{1/8,1}^{-1}) · [𝐠]_{B^{1/4}(□_Q)} ) ,
```

with `P = caccioppoliWith 𝐚 (1/4) (1/8)` and `F = stepSevenCaccForcingFactor`.
The binder list is `exists_stepSevenCaccioppoliEnergy`'s V; the `∇h` leg is
still absent (residue), which is exactly why the display's indicator `1_{z ∉
□_{m-1}}` marks the boundary of this module's regime. -/
theorem exists_stepSevenCaccioppoliEnergyNorm (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {x : Vec d} {g : Vec d → Vec d}
        (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) (c : ℝ),
        IsForcedEquation Q a u g →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q stepOneS g →
          Real.sqrt
              (localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (a.coeffOn Q) u) ≤
            Real.sqrt (caccioppoliWithRHSPrefactor C Q a stepSevenCaccS stepSevenCaccT) *
                (Real.sqrt (Ch02.lambdaS Q stepSevenCaccT a) *
                  ((3 : ℝ) ^ (-Q.scale) *
                    normalizedL2On (openCubeSet Q) (fun y => u.toFun y - c))) +
              Real.sqrt (caccioppoliWithRHSPrefactor C Q a stepSevenCaccS stepSevenCaccT) *
                (Real.sqrt
                    (stepSevenCaccForcingFactor * (Ch02.lambdaS Q stepSevenCaccT a)⁻¹) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q stepOneS g) := by
  obtain ⟨C, hCpos, hC⟩ := exists_stepSevenCaccioppoliEnergy d
  refine ⟨C, hCpos, ?_⟩
  intro Q a x g u c hu hpatch hg
  have hmain := hC u c hu hpatch hg
  set P : ℝ := caccioppoliWithRHSPrefactor C Q a stepSevenCaccS stepSevenCaccT with hPdef
  set lam : ℝ := Ch02.lambdaS Q stepSevenCaccT a with hlamdef
  set Y : ℝ := scaleNormalizedPositiveBesovVectorSeminormTwo Q stepOneS g with hYdef
  have hlampos : 0 < lam := stepSevenCaccLambda_pos Q a stepSevenCaccT_pos
  have hPnn : (0 : ℝ) ≤ P :=
    caccioppoliWithRHSPrefactor_nonneg hCpos.le stepSevenCaccS_pos stepSevenCaccT_pos
      stepSevenCaccS_add_T_lt_one
  have hYnn : (0 : ℝ) ≤ Y :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q stepOneS g
      hg.partialSeminorms_bddAbove
  -- the two summands of the printed right-hand side
  set W : ℝ := Real.rpow (3 : ℝ) (-2 * ((Q.scale : ℤ) : ℝ)) with hWdef
  set X : ℝ := normalizedL2SqOnSet (openCubeSet Q) (fun y => u.toFun y - c) with hXdef
  set F : ℝ := stepSevenCaccForcingFactor with hFdef
  set L : ℝ := Real.rpow lam (-1 : ℝ) with hLdef
  have hWnn : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hXnn : (0 : ℝ) ≤ X := volumeAverage_sq_nonneg _ _
  have hFnn : (0 : ℝ) ≤ F := stepSevenCaccForcingFactor_nonneg
  have hLnn : (0 : ℝ) ≤ L := Real.rpow_nonneg hlampos.le _
  have hAnn : (0 : ℝ) ≤ lam * W * X :=
    mul_nonneg (mul_nonneg hlampos.le hWnn) hXnn
  have hBnn : (0 : ℝ) ≤ F * L * Y ^ 2 :=
    mul_nonneg (mul_nonneg hFnn hLnn) (sq_nonneg Y)
  have hconv := sqrt_le_of_le_mul_add hPnn hAnn hBnn hmain
  -- the first summand's square root
  have hAeq : Real.sqrt (lam * W * X) =
      Real.sqrt lam * ((3 : ℝ) ^ (-Q.scale) *
        normalizedL2On (openCubeSet Q) (fun y => u.toFun y - c)) := by
    have h1 : Real.sqrt (lam * W * X) = Real.sqrt (lam * W) * Real.sqrt X :=
      Real.sqrt_mul (mul_nonneg hlampos.le hWnn) X
    have h2 : Real.sqrt (lam * W) = Real.sqrt lam * Real.sqrt W :=
      Real.sqrt_mul hlampos.le W
    have h3 : Real.sqrt W = (3 : ℝ) ^ (-Q.scale) := by
      rw [hWdef]; exact sqrt_rpow_three_neg_two_mul Q.scale
    have h4 : Real.sqrt X = normalizedL2On (openCubeSet Q) (fun y => u.toFun y - c) := by
      rw [hXdef]; exact sqrt_normalizedL2SqOnSet _ _
    rw [h1, h2, h3, h4, mul_assoc]
  -- the second summand's square root
  have hBeq : Real.sqrt (F * L * Y ^ 2) = Real.sqrt (F * lam⁻¹) * Y := by
    have hLeq : L = lam⁻¹ := by
      have hc : Real.rpow lam (((-1 : ℤ) : ℝ)) = lam ^ (-1 : ℤ) := Real.rpow_intCast lam (-1)
      have hcast : ((-1 : ℤ) : ℝ) = (-1 : ℝ) := by norm_num
      rw [hcast] at hc
      rw [hLdef, hc, zpow_neg_one]
    have h1 : Real.sqrt (F * L * Y ^ 2) = Real.sqrt (F * L) * Real.sqrt (Y ^ 2) :=
      Real.sqrt_mul (mul_nonneg hFnn hLnn) _
    rw [h1, Real.sqrt_sq hYnn, hLeq]
  rw [hAeq, hBeq] at hconv
  exact hconv

end

end Algsuperdiff.Section4.Provider.Regularity
