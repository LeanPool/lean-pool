/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ErrorMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CubeTransport

/-!
# SeedControl

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Seed control for localized regularity

The volume-normalized mean oscillation of a rough-field solution is controlled
by its essential-supremum distance from the constant-coefficient comparator and
the uniform bound for that comparator.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem eLpNorm_top_normalizedVolumeMeasureOn_eq {W : Set (Vec d)}
    (hWtop : volume W ≠ ⊤) (f : Vec d → ℝ) :
    eLpNorm f ⊤ (normalizedVolumeMeasureOn W) =
      eLpNorm f ⊤ (volume.restrict W) := by
  rw [normalizedVolumeMeasureOn_def,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hWtop) f ⊤]
  have hexp : (1 / (⊤ : ℝ≥0∞)).toReal = 0 := by norm_num
  rw [hexp, ENNReal.rpow_zero, one_smul]

/-- The normalized seed at every scale is bounded by the localized error and a
dimension-dependent constant. -/
theorem exists_seedControl (d : ℕ) (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (n : ℤ) (y : Vec d) (omega : Cutoff.CutoffSample d)
        (g : Vec d → Vec d), NormalizedForceAt y n g →
        ∀ u : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt
              ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g →
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
              eLpNorm
                (fun x => u.toFun x - volumeAverage (cubeSetAt y n) u.toFun) 2
                (normalizedVolumeMeasureOn (cubeSetAt y n)) ≤
            ENNReal.ofReal C * (1 + localizedError M n y omega) := by
  obtain ⟨Ccomp, hCcomp, hcomp⟩ := localizedError_comparator_term_le d hdim
  obtain ⟨_Crep, _hCrep, hrep⟩ := exists_lipschitzRepresentative_comparator d hdim
  let B : ℝ := (d : ℝ) * Ccomp / 2
  let C : ℝ := 2 * max 1 B
  have hC : 0 < C := by unfold C; positivity
  refine ⟨C, hC, ?_⟩
  intro M n y omega g hg u hu
  obtain ⟨v, vRep, _Ksup, _KHol, hv, _hKsup, _hKHol, _hgrad, _hhol,
      _hest, hvae, hLip, _hsup, _hcontinuous⟩ :=
    hrep M n y g (Real.rpow 3 (-(n : ℝ) / 2)) hg
  let U : Set (Vec d) := cubeSetAt y n
  let coeff : ℝ≥0∞ :=
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)))
  have hU0 : volume U ≠ 0 :=
    (Algsuperdiff.Section4.Provider.Holder.volume_cubeSetAt_pos y n).ne'
  have hUtop : volume U ≠ ⊤ :=
    Algsuperdiff.Section4.Provider.Holder.volume_cubeSetAt_ne_top y n
  let normalizedVolumeMeasureOn_isProbabilityMeasure :
      IsProbabilityMeasure (normalizedVolumeMeasureOn U) :=
    Algsuperdiff.Section4.Provider.ExcessDecay.isProbabilityMeasure_normalizedVolumeMeasureOn
      hU0 hUtop
  have huNorm : MemLp u.toFun 2 (normalizedVolumeMeasureOn U) :=
    Algsuperdiff.Section4.Provider.ExcessDecay.memLp_normalizedVolumeMeasureOn_of_restrict
      hU0 u.memL2
  have hmean : eLpNorm
        (fun x => u.toFun x - volumeAverage U u.toFun) 2
        (normalizedVolumeMeasureOn U) ≤
      2 * eLpNorm u.toFun 2 (normalizedVolumeMeasureOn U) := by
    simpa only [sub_zero] using
      (Algsuperdiff.Section4.Provider.ExcessDecay.eLpNorm_sub_volumeAverage_le_two_mul
        hU0 hUtop huNorm.aestronglyMeasurable 0)
  have hl2top : eLpNorm u.toFun 2 (normalizedVolumeMeasureOn U) ≤
      eLpNorm u.toFun ⊤ (normalizedVolumeMeasureOn U) :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have htop : eLpNorm u.toFun ⊤ (volume.restrict U) ≤
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict U) +
        eLpNorm v.toFun ⊤ (volume.restrict U) := by
    have hsplit : (fun x => u.toFun x - v.toFun x) + v.toFun = u.toFun :=
      funext fun x => sub_add_cancel (u.toFun x) (v.toFun x)
    have hsum := eLpNorm_add_le (f := fun x => u.toFun x - v.toFun x) (g := v.toFun)
      (μ := volume.restrict U) (p := ⊤) (show (1 : ℝ≥0∞) ≤ ⊤ by simp)
    rwa [hsplit] at hsum
  have hmeanTop : eLpNorm
        (fun x => u.toFun x - volumeAverage U u.toFun) 2
        (normalizedVolumeMeasureOn U) ≤
      2 * (eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict U) +
        eLpNorm v.toFun ⊤ (volume.restrict U)) := by
    calc
      eLpNorm (fun x => u.toFun x - volumeAverage U u.toFun) 2
          (normalizedVolumeMeasureOn U) ≤
          2 * eLpNorm u.toFun 2 (normalizedVolumeMeasureOn U) := hmean
      _ ≤ 2 * eLpNorm u.toFun ⊤ (normalizedVolumeMeasureOn U) :=
        mul_le_mul_right hl2top 2
      _ = 2 * eLpNorm u.toFun ⊤ (volume.restrict U) := by
        rw [eLpNorm_top_normalizedVolumeMeasureOn_eq hUtop]
      _ ≤ 2 * (eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict U) +
          eLpNorm v.toFun ⊤ (volume.restrict U)) := mul_le_mul_right htop 2
  have hdiff : coeff *
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict U) ≤
      localizedError M n y omega := by
    exact le_localizedError M n y omega hg hu hv
  have hvRep : IsCubeRepresentative y n v vRep :=
    ⟨hvae.symm, hLip.continuous.continuousOn⟩
  have hvBound : coeff * eLpNorm v.toFun ⊤ (volume.restrict U) ≤
      ENNReal.ofReal B := by
    rw [eLpNorm_top_restrict_eq_supNormOn_of_ae (isOpen_cubeSetAt y n)
      hvRep.1 hvRep.2]
    exact hcomp M n y g hg v hv vRep hvRep
  have hscaled : coeff * eLpNorm
        (fun x => u.toFun x - volumeAverage U u.toFun) 2
        (normalizedVolumeMeasureOn U) ≤
      2 * (localizedError M n y omega + ENNReal.ofReal B) := by
    calc
      coeff * eLpNorm (fun x => u.toFun x - volumeAverage U u.toFun) 2
          (normalizedVolumeMeasureOn U) ≤
          coeff * (2 * (eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
              (volume.restrict U) + eLpNorm v.toFun ⊤ (volume.restrict U))) :=
        mul_le_mul_right hmeanTop coeff
      _ = 2 * (coeff * eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
            (volume.restrict U) + coeff * eLpNorm v.toFun ⊤ (volume.restrict U)) := by
        ring
      _ ≤ 2 * (localizedError M n y omega + ENNReal.ofReal B) :=
        mul_le_mul_right (add_le_add hdiff hvBound) 2
  change coeff * _ ≤ ENNReal.ofReal C * (1 + localizedError M n y omega)
  refine hscaled.trans ?_
  have hBmax : ENNReal.ofReal B ≤ ENNReal.ofReal (max 1 B) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  have honeMax : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max 1 B) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have herror : localizedError M n y omega ≤
      ENNReal.ofReal (max 1 B) * localizedError M n y omega := by
    simpa only [one_mul, mul_comm] using
      mul_le_mul_right honeMax (localizedError M n y omega)
  calc
    2 * (localizedError M n y omega + ENNReal.ofReal B) ≤
        2 * (ENNReal.ofReal (max 1 B) * localizedError M n y omega +
          ENNReal.ofReal (max 1 B)) :=
      mul_le_mul_right (add_le_add herror hBmax) 2
    _ = ENNReal.ofReal C * (1 + localizedError M n y omega) := by
      have hCof : ENNReal.ofReal C = 2 * ENNReal.ofReal (max 1 B) := by
        dsimp only [C]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [hCof]
      ring

end

end Algsuperdiff.Section5.Provider
