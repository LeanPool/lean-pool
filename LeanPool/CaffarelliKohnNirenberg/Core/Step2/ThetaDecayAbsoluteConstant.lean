/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationCZP1Final
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkConstantsNonneg
public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.Iteration
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantityNonneg

/-!
# The combined decay inequality with an absolute leading constant

Paper label `lem:theta-decay` (`eq:theta-decay-1` and `eq:theta-decay-2`):
there are an **absolute** constant `C₂₇` and a constant `C₂₈ = C₂₈(q)` such
that the combined quantity `θ = α + β + κ⁻⁴δ²` decays from scale `ρ` to scale
`κρ`.  The order of the two constants matters downstream: `κ`, `η` and `ε_*`
of `conv:kappa` are built from `C₂₇` alone, so `C₂₇` has to be fixed before
the integrability exponent `q` of the force.

Stating the same two displays with `q` quantified first would only give
`∀ q, ∃ C₂₇`.  The theorem below exchanges the two quantifiers: the witness,
`thetaDecayC₂₇ gagliardoConstant √(2 · max pressureP12Constant
czP1ThetaDecayConstant) caccioppoliC₂₅`, mentions no `q`, so it can be
produced before `q` is introduced.  The Calderón–Zygmund input of
`thm:pressure-decay` is discharged from the solution by
`CKN.theoremA_hCZ_p1_of_sws`.

Following `conv:kappa` the displays are taken at `κ = iterationKappa C₂₇`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Core.Step3

noncomputable section

namespace CKN

/-- Paper label `lem:theta-decay`, displays `eq:theta-decay-1` and
`eq:theta-decay-2`, with the leading constant `C₂₇` absolute (fixed before the
force exponent `q`) and `C₂₈ = C₂₈(q)`, at the scale ratio `κ` of
`conv:kappa`. -/
theorem thetaDecay_T_of_sws_absolute :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧ ∀ q : ℝ, ∃ C₂₈ : ℝ, 0 < C₂₈ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, 0 < ρ →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                (beta u Du z ρ ^ (1 / 2 : ℝ) + beta u Du z ρ) *
                  theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    lambda q f z ρ ^ (1 / 2 : ℝ) +
              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ ∧
        (theta (iterationKappa C₂₇) u Du p z ρ ≤ 1 →
          theta (iterationKappa C₂₇) u Du p z (iterationKappa C₂₇ * ρ) ≤
            C₂₇ * iterationKappa C₂₇ ^ (2 / 3 : ℝ) *
                theta (iterationKappa C₂₇) u Du p z ρ +
              2 * C₂₇ * iterationKappa C₂₇ ^ (-5 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    theta (iterationKappa C₂₇) u Du p z ρ +
              C₂₈ * iterationKappa C₂₇ ^ (-1 / 2 : ℝ) *
                  theta (iterationKappa C₂₇) u Du p z ρ ^ (1 / 2 : ℝ) *
                    lambda q f z ρ ^ (1 / 2 : ℝ) +
              C₂₈ * iterationKappa C₂₇ ^ (-3 : ℝ) * lambda q f z ρ) := by
  let C₁₂_p1 : ℝ := czP1ThetaDecayConstant
  let C₁₄ : ℝ := Real.sqrt (2 * max CKN.pressureP12Constant C₁₂_p1)
  let C₂₅ : ℝ := caccioppoliC₂₅
  let C₂₇ : ℝ := thetaDecayC₂₇ gagliardoConstant C₁₄ C₂₅
  have hP12base : 0 ≤ CKN.pressureP12Constant := by
    rw [CKN.pressureP12Constant]
    rcases le_total pressureP234Constant pressureP56Constant with h | h
    · rw [max_eq_right h]
      exact CKN.pressureP56Constant_nonneg'
    · rw [max_eq_left h]
      exact CKN.pressureP234Constant_nonneg'
  have hP12 : 0 ≤ max CKN.pressureP12Constant C₁₂_p1 :=
    le_trans hP12base (le_max_left _ _)
  have hC₁₄ : 0 ≤ C₁₄ := by
    dsimp [C₁₄]
    positivity
  have hC₂₅ : 0 ≤ C₂₅ := by
    dsimp [C₂₅]
    unfold caccioppoliC₂₅
    positivity
  have hC₂₇ : 0 < C₂₇ := by
    dsimp [C₂₇]
    rw [thetaDecayC₂₇]
    have : 0 < C₂₅ := by
      dsimp [C₂₅]
      have hcg : 0 ≤ cutoffGradientConstant :=
        CKN.Foundation.Heat.cutoffGradientConstant_nonneg_global
      have hcs : 0 ≤ cutoffSecondDerivativeConstant :=
        CKN.Foundation.Heat.cutoffSecondDerivativeConstant_nonneg_global
      have hbase : 0 < caccioppoliC₂₅BaseSquared := by
        unfold caccioppoliC₂₅BaseSquared
        have hlast : 0 < 3000 * cutoffGradientConstant + 1800000 := by
          positivity
        exact lt_of_lt_of_le hlast (le_max_of_le_right (le_max_right _ _))
      unfold caccioppoliC₂₅
      positivity
    positivity
  refine ⟨C₂₇, hC₂₇, fun q => ?_⟩
  let C₁₅ : ℝ := Real.sqrt (2 * max (CKN.pressureP13Constant q)
    (pressureP7SolutionConstant q).toReal)
  let C₂₆ : ℝ := caccioppoliC₂₆ q
  let C₂₈ : ℝ := thetaDecayC₂₈ gagliardoConstant C₁₅ C₂₆
  have hP13base : 0 ≤ CKN.pressureP13Constant q :=
    CKN.pressureP13Constant_nonneg' q
  have hP13 : 0 ≤ max (CKN.pressureP13Constant q)
      (pressureP7SolutionConstant q).toReal :=
    le_trans hP13base (le_max_left _ _)
  have hC₁₅ : 0 ≤ C₁₅ := by
    dsimp [C₁₅]
    positivity
  have hC₂₆ : 0 ≤ C₂₆ := by
    dsimp [C₂₆]
    unfold caccioppoliC₂₆
    positivity
  have hC₂₈ : 0 < C₂₈ := by
    dsimp [C₂₈]
    rw [thetaDecayC₂₈]
    have : 0 < C₂₆ := by
      dsimp [C₂₆]
      unfold caccioppoliC₂₆
      have hv : 0 < 4 * Real.pi / 3 := by positivity
      positivity
    have hC₉ : 0 < gagliardoConstant := by
      unfold gagliardoConstant
      positivity
    positivity
  refine ⟨C₂₈, hC₂₈, ?_⟩
  intro Ω I u Du p f hsol z ρ hρ hsub
  let κ : ℝ := iterationKappa C₂₇
  have hκ : 0 < κ := by
    dsimp [κ]
    exact iterationKappa_pos hC₂₇
  have hr : 0 < κ * ρ := mul_pos hκ hρ
  have hhalf : κ * ρ ≤ ρ / 2 := by
    have hk := iterationKappa_le_half C₂₇
    have hmul := mul_le_mul_of_nonneg_right hk hρ.le
    nlinarith only [hmul]
  have hratio : κ * ρ / ρ = κ := by
    apply (div_eq_iff hρ.ne').2
    ring
  have hpressure := pressureDecay_one_scale_T C₁₂_p1 hsol hρ hr hhalf hsub
    (theoremA_hCZ_p1_of_sws q Ω I u Du p f hsol hρ hr hhalf hsub)
  have hcacc := caccioppoli hsol hρ hr hhalf hsub
  have hcacc' : alpha u z (κ * ρ) + beta u Du z (κ * ρ) ≤
      C₂₅ * (κ * ρ / ρ) * alpha u z ρ +
        C₂₅ * (κ * ρ / ρ)⁻¹ * Real.sqrt (alpha u z ρ) *
          Real.sqrt (beta u Du z ρ) * Real.sqrt (gamma u z ρ) +
        C₂₅ * (κ * ρ / ρ)⁻¹ * delta p z ρ * Real.sqrt (gamma u z ρ) +
        C₂₆ * (κ * ρ / ρ) ^ (-1 / 2 : ℝ) * Real.sqrt (gamma u z ρ) *
          Real.sqrt (lambda q f z ρ) := by
    simpa only [C₂₅, C₂₆, ← Real.sqrt_eq_rpow] using hcacc
  have hfirst := thetaDecay_of_pressure_and_caccioppoli
    (C₁₄ := C₁₄) (C₁₅ := C₁₅) (C₂₅ := C₂₅) (C₂₆ := C₂₆)
    hsol hρ hr hhalf hsub hC₁₄ hC₁₅ hC₂₅ hC₂₆ hpressure hcacc'
  constructor
  · simpa [κ, hratio, C₂₇, C₂₈] using hfirst
  · intro hθ
    have hsmall := thetaDecay_small_of_pressure_and_caccioppoli
      (C₁₄ := C₁₄) (C₁₅ := C₁₅) (C₂₅ := C₂₅) (C₂₆ := C₂₆)
      hsol hρ hr hhalf hsub hC₁₄ hC₁₅ hC₂₅ hC₂₆
      (by simpa [κ, hratio] using hθ) hpressure hcacc'
    simpa [κ, hratio, C₂₇, C₂₈] using hsmall

end CKN
