/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.LocalHolderEstimate
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.SeedControl

/-!
# PointwiseBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The localized regularity at the Hölder exponent one half

The local Hölder estimate is read at the exponent `alpha = 1/2`, on the cube it
is stated on, at the truncation scale equal to the scale of the cube.  Three
normalizations then meet:

* the localized regularity measures the `1/2`-Hölder seminorm of the continuous
  representative in the gauge `σ_n 3^{-n/2}`, while the local estimate measures
  it in the gauge `3^{n/2}`; the two differ by the factor `σ_n 3^{-n}`, which is
  exactly the gauge of the localized error;
* on the normalized forcing class the datum leg of the local estimate, carrying
  `σ_n⁻¹ 3^{3n/2}` and the seminorm `[g]_{C^{0,1/2}} ≤ 3^{-n/2}`, contributes at
  most one after that rescaling;
* the mean-oscillation seed of the local estimate, in the same gauge, is at most
  `C (1 + E)` with `E` the localized error.

The result is the almost sure pointwise bound

`localizedRegularity ≤ C 3^{X/2} (1 + localizedError)`,

uniform over the forcing class and over the solutions, with `X` the minimal
scale of the local Hölder estimate at `alpha = 1/2` and its exponential tail.

## Main results

* `exists_localizedRegularity_pointwise_bound` — the bound above, together with
  the measurability and the tail of the scale `X`.
-/

namespace Algsuperdiff.Section4.Provider.RegularityMoment

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open _root_.HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem rpow_three_mul (a b : ℝ) :
    Real.rpow 3 a * Real.rpow 3 b = Real.rpow 3 (a + b) :=
  (Real.rpow_add (by norm_num : (0 : ℝ) < 3) a b).symm

/-- **The two Hölder gauges differ by the gauge of the localized error.**  The
infimum over continuous representatives is taken in the gauge `σ_n 3^{-n/2}` of
the localized regularity; it is the gauge `3^{n/2}` of the local Hölder estimate
multiplied by the constant `σ_n 3^{-n}`, which is strictly positive and finite,
so it passes through the infimum. -/
private theorem iInf_gauge_rescale (M : ABKModel d) (n : ℤ) (y : Vec d)
    (u : H1Function (cubeSetAt y n)) :
    (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) =
      ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        ⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
          ENNReal.ofReal (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ))) *
            holderSeminormOn (cubeSetAt y n) (1 / 2) uRep := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) :=
    mul_pos hsig (Real.rpow_pos_of_pos (by norm_num) _)
  have ha0 : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hpos
  have hatop : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun uRep => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun _ => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le]
  congr 2
  rw [mul_assoc, rpow_three_mul,
    show -(n : ℝ) + 1 / 2 * (n : ℝ) = -(n : ℝ) / 2 by ring]

/-- **The datum leg costs nothing on the normalized forcing class.**  The datum
prefactor `σ_n⁻¹ 3^{3n/2}` of the local Hölder estimate, rescaled by the gauge
`σ_n 3^{-n}`, is `3^{n/2}`, and the normalization of the class is exactly
`[g]_{C^{0,1/2}(y+□_n)} ≤ 3^{-n/2}`. -/
private theorem force_leg_le_one (M : ABKModel d) (n : ℤ) (y : Vec d)
    {g : Vec d → Vec d} (hg : NormalizedForceAt y n g) :
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        (ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ)⁻¹ * Real.rpow 3 (3 * (n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) g) ≤ 1 := by
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := (Annealed.sigmaBar M n).2
  have hgle : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≤
      ENNReal.ofReal (Real.rpow 3 (-(n : ℝ) / 2)) :=
    (holderSeminormOn_le_ofReal_iff (Real.rpow_nonneg (by norm_num) _)).2 hg
  have hnn : (0 : ℝ) ≤ (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) :=
    (mul_pos hsig (Real.rpow_pos_of_pos (by norm_num) _)).le
  have hup : (0 : ℝ) ≤ Real.rpow 3 ((n : ℝ) / 2) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hgauge :
      ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ)⁻¹ * Real.rpow 3 (3 * (n : ℝ) / 2)) =
        ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_mul hnn]
    congr 1
    rw [show (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) *
        ((Annealed.sigmaBar M n : ℝ)⁻¹ * Real.rpow 3 (3 * (n : ℝ) / 2)) =
        ((Annealed.sigmaBar M n : ℝ) * (Annealed.sigmaBar M n : ℝ)⁻¹) *
          (Real.rpow 3 (-(n : ℝ)) * Real.rpow 3 (3 * (n : ℝ) / 2)) by ring,
      mul_inv_cancel₀ hsig.ne', one_mul, rpow_three_mul,
      show -(n : ℝ) + 3 * (n : ℝ) / 2 = (n : ℝ) / 2 by ring]
  calc ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        (ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ)⁻¹ * Real.rpow 3 (3 * (n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) g)
      = ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) g := by rw [← mul_assoc, hgauge]
    _ ≤ ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
          ENNReal.ofReal (Real.rpow 3 (-(n : ℝ) / 2)) := mul_le_mul_right hgle _
    _ = 1 := by
        rw [← ENNReal.ofReal_mul hup, rpow_three_mul,
          show (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 by ring]
        simp

/-- **The localized regularity is bounded by the minimal-scale factor and the
localized error.**  At the Hölder exponent `1/2` the local Hölder estimate, the
normalization of the forcing class and the mean-oscillation seed give, almost
surely and simultaneously for every datum of the normalized class and every
solution of the rough-field Dirichlet problem on the cube,

`localizedRegularity M n y ω ≤ C 3^{X ω / 2} (1 + localizedError M n y ω)`,

where `X` is the minimal scale of the local Hölder estimate at `alpha = 1/2`,
with its measurability and its exponential tail.  The centre `y` is arbitrary,
as it is in both inputs. -/
theorem exists_localizedRegularity_pointwise_bound (d : ℕ) (cstar : ℝ) (hdim : 2 ≤ d)
    (hcstar : 0 < cstar) :
    ∃ gamma0 Ctail Camp : ℝ, 0 < gamma0 ∧ 0 < Ctail ∧ 0 < Camp ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ (n : ℤ) (y : Vec d), ∃ X : Cutoff.CutoffSample d → ℕ,
        Measurable X ∧
        (∀ N : ℕ,
          (Cutoff.cutoffSampleLaw M).toMeasure {omega | N ≤ X omega} ≤
            ENNReal.ofReal (Ctail * Real.exp
              (-((1 - (1 : ℝ) / 2) ^ (2 : ℕ) * ((N : ℝ) - Ctail)) / (Ctail * M.gamma)))) ∧
        ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
          localizedRegularity M n y omega ≤
            ENNReal.ofReal (Camp * Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) *
              (1 + localizedError M n y omega) := by
  obtain ⟨g0, Ch, hg0, hCh, hholder⟩ :=
    Algsuperdiff.Frozen.Section4.local_holder_estimate d cstar hcstar
  obtain ⟨Cs, hCs, hseed⟩ := Algsuperdiff.Section5.Provider.exists_seedControl d hdim
  refine ⟨min g0 (4 * Ch ^ 2)⁻¹, Ch, Ch * (Cs + 1), lt_min hg0 (by positivity), hCh,
    by positivity, ?_⟩
  intro M hcs hgamma n y
  have hgle : M.gamma ≤ g0 := hgamma.trans (min_le_left _ _)
  have hgsmall : M.gamma ≤ (4 * Ch ^ 2)⁻¹ := hgamma.trans (min_le_right _ _)
  have halpha : (1 / 2 : ℝ) ≤ 1 - Ch * Real.sqrt M.gamma := by
    have hsqrt : Real.sqrt M.gamma ≤ (2 * Ch)⁻¹ := by
      have hid : ((2 * Ch)⁻¹ : ℝ) ^ 2 = (4 * Ch ^ 2)⁻¹ := by
        field_simp
        ring
      calc Real.sqrt M.gamma ≤ Real.sqrt ((4 * Ch ^ 2)⁻¹) := Real.sqrt_le_sqrt hgsmall
        _ = Real.sqrt (((2 * Ch)⁻¹ : ℝ) ^ 2) := by rw [hid]
        _ = (2 * Ch)⁻¹ := Real.sqrt_sq (by positivity)
    have hmul : Ch * Real.sqrt M.gamma ≤ Ch * (2 * Ch)⁻¹ :=
      mul_le_mul_of_nonneg_left hsqrt hCh.le
    have hval : Ch * (2 * Ch)⁻¹ = 1 / 2 := by
      field_simp
    linarith only [hmul, hval]
  obtain ⟨X, hXmeas, hXtail, hae⟩ :=
    hholder M hcs hgle (1 / 2) (by norm_num) halpha n y
  refine ⟨X, hXmeas, hXtail, ?_⟩
  filter_upwards [hae] with omega homega
  refine localizedRegularity_le_iff.2 fun g hg u hu => ?_
  have hH := homega n le_rfl g u hu
  rw [iInf_gauge_rescale M n y u]
  refine le_trans (mul_le_mul_right hH _) ?_
  have hseedle := hseed M n y omega g hg u hu
  have hforce := force_leg_le_one M n y hg
  have hCsOne : ENNReal.ofReal Cs + 1 = ENNReal.ofReal (Cs + 1) := by
    rw [ENNReal.ofReal_add hCs.le zero_le_one, ENNReal.ofReal_one]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  set E : ℝ≥0∞ := localizedError M n y omega with hE
  set A : ℝ≥0∞ := ENNReal.ofReal (Ch * Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) with hA
  calc ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        (A *
          (eLpNorm (fun x => u.toFun x - volumeAverage (cubeSetAt y n) u.toFun) 2
              (normalizedVolumeMeasureOn (cubeSetAt y n)) +
            ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ)⁻¹ *
                Real.rpow 3 (3 * (n : ℝ) / 2)) *
              holderSeminormOn (cubeSetAt y n) (1 / 2) g))
      = A * (ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          eLpNorm (fun x => u.toFun x - volumeAverage (cubeSetAt y n) u.toFun) 2
            (normalizedVolumeMeasureOn (cubeSetAt y n)) +
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            (ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ)⁻¹ *
                Real.rpow 3 (3 * (n : ℝ) / 2)) *
              holderSeminormOn (cubeSetAt y n) (1 / 2) g)) := by ring
    _ ≤ A * (ENNReal.ofReal Cs * (1 + E) + 1) :=
        mul_le_mul_right (add_le_add hseedle hforce) A
    _ ≤ A * (ENNReal.ofReal Cs * (1 + E) + (1 + E)) :=
        mul_le_mul_right
          (add_le_add (le_refl (ENNReal.ofReal Cs * (1 + E)))
            (show (1 : ℝ≥0∞) ≤ 1 + E from le_self_add)) A
    _ = A * ENNReal.ofReal (Cs + 1) * (1 + E) := by
        rw [← hCsOne]
        ring
    _ = ENNReal.ofReal (Ch * (Cs + 1) * Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ))) *
          (1 + E) := by
        have hCr : (0 : ℝ) ≤ Ch * Real.rpow 3 ((1 / 2 : ℝ) * (X omega : ℝ)) :=
          mul_nonneg hCh.le (Real.rpow_pos_of_pos (by norm_num) _).le
        rw [hA, ← ENNReal.ofReal_mul hCr]
        congr 2
        ring

end

end Algsuperdiff.Section4.Provider.RegularityMoment
