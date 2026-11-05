/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepFourCollapseEps
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootClauseBFloorRecut

/-!
# ShellEpsPinFloor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The floor arithmetic -/

/-- **The pin's arithmetic, in the abstract.**  If `P > 0`, `0 ≤ E`, `0 < D`, `64P²
≤ D` and `E ≤ Q · (1/32) · √δ` with `δ ≤ D⁻¹` and `A·Q = P`, then `A·E ≤
1/256`.  Stated on free reals; no norm and no measure occurs. -/
private theorem pin_arith {A Q D delta E : ℝ} (hA : 0 < A) (hQ : 0 < Q)
    (hD : 64 * (A * Q) ^ 2 ≤ D) (hdeltaD : delta ≤ D⁻¹)
    (hE : E ≤ Q * (1 / 32 * Real.sqrt delta)) :
    A * E ≤ 1 / 256 := by
  set P : ℝ := A * Q with hP
  have hPpos : (0 : ℝ) < P := mul_pos hA hQ
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  have hsq : (64 : ℝ) * P ^ 2 = (8 * P) ^ 2 := by ring
  have hsqrtD : (8 : ℝ) * P ≤ Real.sqrt D := by
    have h := Real.sqrt_le_sqrt hD
    rwa [hsq, Real.sqrt_sq (by positivity)] at h
  have hsqrtdelta : Real.sqrt delta ≤ (8 * P)⁻¹ := by
    have h1 : Real.sqrt delta ≤ Real.sqrt D⁻¹ := Real.sqrt_le_sqrt hdeltaD
    have h2 : Real.sqrt D⁻¹ = (Real.sqrt D)⁻¹ := Real.sqrt_inv D
    have h3 : (Real.sqrt D)⁻¹ ≤ (8 * P)⁻¹ := inv_anti₀ (by positivity) hsqrtD
    rw [h2] at h1
    exact le_trans h1 h3
  have hkey : A * E ≤ P * (1 / 32 * Real.sqrt delta) := by
    have h := mul_le_mul_of_nonneg_left hE hA.le
    calc A * E ≤ A * (Q * (1 / 32 * Real.sqrt delta)) := h
      _ = P * (1 / 32 * Real.sqrt delta) := by rw [hP]; ring
  have hfin : P * (1 / 32 * Real.sqrt delta) ≤ 1 / 256 := by
    have hstep := mul_le_mul_of_nonneg_left hsqrtdelta
      (by positivity : (0 : ℝ) ≤ P * (1 / 32))
    have hval : P * (1 / 32) * (8 * P)⁻¹ = 1 / 256 := by
      rw [mul_inv, ← mul_assoc]
      field_simp
      norm_num
    calc P * (1 / 32 * Real.sqrt delta) = P * (1 / 32) * Real.sqrt delta := by ring
      _ ≤ P * (1 / 32) * (8 * P)⁻¹ := hstep
      _ = 1 / 256 := hval
  linarith only [hkey, hfin]

/-! ## 2. The pin, produced -/

/-- **The `ε`-pin's shell scalar, produced from a `C_edos` floor.**

For every `A > 0` there is a floor `C_fl ≥ 1` such that, for every `C_edos ≥ C_fl`,
almost surely, on the Step-3/Step-7 good event at this lane's own `δ = δ(C₁,α)` and
at every truncation `L ≥ j`,

```text
   A · 𝓔_j(z)  ≤  s⁴ ,      s = stepOneS = 1/4 .
```

This is the hypothesis's `exists_boundaryScalar_le_displayLegs_of_epsPin`
carries, delivered by the lane's own free parameter. -/
theorem exists_cedosFloor_shellEpsPin (d : ℕ) :
    ∃ Cann : ℝ, 0 < Cann ∧
      ∀ A : ℝ, 0 < A →
        ∃ Cfl : ℝ, 1 ≤ Cfl ∧
          ∀ M : ABKModel d, M.gamma ≤ Cann⁻¹ * Disorder.cstar M ^ (10 : ℕ) →
            M.gamma ≤ 1 / 256 →
              ∀ (Cedos Citer : ℝ) (k : ℕ), Cfl ≤ Cedos →
                ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
                  M.gamma * |Real.log M.gamma| ^ (2 : ℕ) ≤
                      Real.rpow stepOneSEighth (3 / 2 : ℝ) *
                        Disorder.cstar M ^ (2 : ℕ) *
                        stepOneEp (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) →
                    ∀ (j : ℤ) (z : Vec d),
                      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
                        omega ∈ stepThreeGoodEvent M
                            (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) j z →
                          ∀ L : ℤ, j ≤ L →
                            A * Support.fluxCorrectedErrorRepresentative M L j
                                ⟨stepOneSEighth, stepOneSEighth_pos⟩
                                (Cutoff.translateCutoffSample z omega) ≤
                              stepOneS ^ (4 : ℕ) := by
  obtain ⟨Cann, hCann, hcap⟩ := ae_stepOneEpsJ_le d
  refine ⟨Cann, hCann, ?_⟩
  intro A hA
  refine ⟨max 1 (64 * (A * Cann) ^ 2), le_max_left _ _, ?_⟩
  intro M hregime hgamma Cedos Citer k hfloor alpha halpha0 halpha1 hsmall j z
  have hC1two : (2 : ℝ) ≤ stepOneC1 d Cedos 1 Citer k :=
    two_le_stepOneC1 d Cedos 1 Citer k
  have hC1pos : (0 : ℝ) < stepOneC1 d Cedos 1 Citer k := by linarith only [hC1two]
  have hdelta : stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha ∈
      Set.Ioc (0 : ℝ) (1 / 2) := stepOneDelta_mem hC1two halpha0 halpha1
  have hCedos1 : (1 : ℝ) ≤ Cedos := le_trans (le_max_left _ _) hfloor
  have hC1ge : 64 * (A * Cann) ^ 2 ≤ stepOneC1 d Cedos 1 Citer k :=
    le_stepOneC1_of_le_cedos d hCedos1 (le_trans (le_max_right _ _) hfloor) Citer k
  have hdeltale : stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha ≤
      (stepOneC1 d Cedos 1 Citer k)⁻¹ := by
    have hval : stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha =
        (stepOneC1 d Cedos 1 Citer k)⁻¹ * (1 - alpha) := rfl
    have hinv0 : (0 : ℝ) ≤ (stepOneC1 d Cedos 1 Citer k)⁻¹ :=
      inv_nonneg.mpr hC1pos.le
    rw [hval]
    have := mul_le_mul_of_nonneg_left (by linarith only [halpha0] : (1 : ℝ) - alpha ≤ 1)
      hinv0
    linarith only [this]
  filter_upwards [hcap M hregime hgamma
    (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) hdelta hsmall j z] with omega homega
  intro hmem L hjL
  have hE := fluxCorrectedErrorRepresentative_le_stepFiveEps hjL hmem homega
  have hB0 : (0 : ℝ) ≤ Cann * stepOneEp (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) :=
    mul_nonneg hCann.le (stepOneEp_mem_Ioc hdelta).1.le
  have hEps := stepFiveEps_le_of_cap hB0 homega
  have hEcap : Support.fluxCorrectedErrorRepresentative M L j
      ⟨stepOneSEighth, stepOneSEighth_pos⟩ (Cutoff.translateCutoffSample z omega) ≤
      Cann * (1 / 32 *
        Real.sqrt (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha)) := by
    have hval : Cann * stepOneEp (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha) =
        Cann * (1 / 32 *
          Real.sqrt (stepOneDelta (stepOneC1 d Cedos 1 Citer k) alpha)) := by
      rw [stepOneEp, stepOneSEighth_eq]
    rw [← hval]
    exact le_trans hE hEps
  have hpin := pin_arith (A := A) (Q := Cann)
    (D := stepOneC1 d Cedos 1 Citer k) hA hCann hC1ge hdeltale hEcap
  have hs4 : stepOneS ^ (4 : ℕ) = 1 / 256 := by
    rw [stepOneS]; norm_num
  rw [hs4]
  exact hpin

end

end Algsuperdiff.Section4.Provider.Regularity
