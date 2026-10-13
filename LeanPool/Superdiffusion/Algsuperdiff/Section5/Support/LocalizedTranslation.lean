/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedAssembly
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability

/-!
# LocalizedTranslation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Translation covariance of the localized quantities

The localized error and regularity on a cube centred at `y` agree with their
origin-centred versions after translating the cutoff sample by `y`.  Translation
invariance of the cutoff-sample law then makes every measurable moment of these
quantities independent of the centre.

-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem cubeSetAt_zero (n : ℤ) :
    cubeSetAt (0 : Vec d) n = openCubeSet (originCube d n) := by
  ext x
  simp [cubeSetAt]

def toOriginWitness (n : ℤ) (y : Vec d) (u : H1Function (cubeSetAt y n)) :
    H1Function (cubeSetAt (0 : Vec d) n) :=
  castH1 (cubeSetAt_zero n).symm (originPullback y n u)

def fromOriginWitness (n : ℤ) (y : Vec d)
    (u : H1Function (cubeSetAt (0 : Vec d) n)) : H1Function (cubeSetAt y n) :=
  translateSolution y n (castH1 (cubeSetAt_zero n) u)

private theorem originPullback_zero (n : ℤ)
    (u : H1Function (cubeSetAt (0 : Vec d) n)) :
    originPullback 0 n u = castH1 (cubeSetAt_zero n) u := by
  apply h1Function_ext <;> funext x <;> simp [originPullback]

private theorem originPullback_toOriginWitness (n : ℤ) (y : Vec d)
    (u : H1Function (cubeSetAt y n)) :
    originPullback 0 n (toOriginWitness n y u) = originPullback y n u := by
  apply h1Function_ext <;> funext x <;> simp [originPullback, toOriginWitness]

private theorem originPullback_fromOriginWitness (n : ℤ) (y : Vec d)
    (u : H1Function (cubeSetAt (0 : Vec d) n)) :
    originPullback y n (fromOriginWitness n y u) = castH1 (cubeSetAt_zero n) u := by
  exact originPullback_translateSolution y n (castH1 (cubeSetAt_zero n) u)

private theorem normalizedForceAt_translate_iff (n : ℤ) (y : Vec d) (g : Vec d → Vec d) :
    NormalizedForceAt y n g ↔ NormalizedForceAt 0 n (fun x => g (y + x)) := by
  rw [normalizedForceAt_def, normalizedForceAt_def, cubeSetAt_zero]
  constructor
  · exact holderSeminormBoundOn_originCube_of_cubeSetAt
  · intro h x hx z hz
    have hx' : x - y ∈ openCubeSet (originCube d n) := mem_cubeSetAt_iff.1 hx
    have hz' : z - y ∈ openCubeSet (originCube d n) := mem_cubeSetAt_iff.1 hz
    have h := h (x - y) hx' (z - y) hz'
    simpa [add_comm] using h

private theorem toOriginWitness_solution (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    {u : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g) :
    IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n (Cutoff.translateCutoffSample y omega)).toCoeffField)
      0 n (toOriginWitness n y u) (fun x => g (y + x)) := by
  rw [isDirichletSolutionAt_iff_origin]
  have hu' := (isDirichletSolutionAt_iff_origin
    ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n u g).1 hu
  rw [originPullback_toOriginWitness]
  rw [← coefficientCutoff_add_eq_translateCutoffSample]
  simpa only [zero_add] using hu'

private theorem fromOriginWitness_solution (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    {u : H1Function (cubeSetAt (0 : Vec d) n)}
    (hu : IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n (Cutoff.translateCutoffSample y omega)).toCoeffField)
      0 n u g) :
    IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n
      (fromOriginWitness n y u) (fun x => g (x - y)) := by
  rw [isDirichletSolutionAt_iff_origin, originPullback_fromOriginWitness]
  have hu' := (isDirichletSolutionAt_iff_origin
    ((Cutoff.coefficientCutoff M.nu n (Cutoff.translateCutoffSample y omega)).toCoeffField)
    0 n u g).1 hu
  rw [originPullback_zero] at hu'
  rw [coefficientCutoff_add_eq_translateCutoffSample]
  simpa [add_comm] using! hu'

private theorem eLpNorm_sub_toOrigin_eq (n : ℤ) (y : Vec d)
    (u v : H1Function (cubeSetAt y n)) :
    eLpNorm (fun x => (toOriginWitness n y u).toFun x - (toOriginWitness n y v).toFun x) ⊤
        (volume.restrict (cubeSetAt 0 n)) =
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
        (volume.restrict (cubeSetAt y n)) := by
  simp only [toOriginWitness, castH1_toFun, originPullback_toFun]
  have hmeas : AEStronglyMeasurable (fun x => u.toFun x - v.toFun x)
      (volume.restrict (translateSet y (openCubeSet (originCube d n)))) :=
    by
      have hu := u.memL2.aestronglyMeasurable
      have hv := v.memL2.aestronglyMeasurable
      simpa only [cubeSetAt_eq_translateSet, Pi.sub_apply] using! hu.sub hv
  simpa only [Function.comp_apply, cubeSetAt_zero, cubeSetAt_eq_translateSet,
    translateSet_zero, add_comm] using!
    (eLpNorm_comp_measurePreserving hmeas
      (measurePreserving_addRight_restrict_translateSet y
        (openCubeSet (originCube d n))) :
      eLpNorm ((fun x => u.toFun x - v.toFun x) ∘ fun x => x + y) ⊤
          (volume.restrict (openCubeSet (originCube d n))) =
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
          (volume.restrict (translateSet y (openCubeSet (originCube d n)))))

private theorem eLpNorm_sub_fromOrigin_eq (n : ℤ) (y : Vec d)
    (u v : H1Function (cubeSetAt (0 : Vec d) n)) :
    eLpNorm (fun x => (fromOriginWitness n y u).toFun x -
        (fromOriginWitness n y v).toFun x) ⊤ (volume.restrict (cubeSetAt y n)) =
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
        (volume.restrict (cubeSetAt 0 n)) := by
  simp only [fromOriginWitness, translateSolution, castH1_toFun, H1Function.translate_toFun]
  have hmeas : AEStronglyMeasurable (fun x => u.toFun x - v.toFun x)
      (volume.restrict (openCubeSet (originCube d n))) :=
    by
      have hu := u.memL2.aestronglyMeasurable
      have hv := v.memL2.aestronglyMeasurable
      simpa only [cubeSetAt_zero, Pi.sub_apply] using! hu.sub hv
  simpa only [Function.comp_apply, cubeSetAt_zero, cubeSetAt_eq_translateSet,
    translateSet_zero] using!
    (eLpNorm_comp_measurePreserving hmeas
      (measurePreserving_subRight_restrict_translateSet y
        (openCubeSet (originCube d n))) :
      eLpNorm ((fun x => u.toFun x - v.toFun x) ∘ fun x => x - y) ⊤
          (volume.restrict (translateSet y (openCubeSet (originCube d n)))) =
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
          (volume.restrict (openCubeSet (originCube d n))))

private theorem localizedError_le_translate (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) :
    localizedError M n y omega ≤
      localizedError M n 0 (Cutoff.translateCutoffSample y omega) := by
  rw [localizedError_le_iff]
  intro g hg u hu v hv
  have hgu := (normalizedForceAt_translate_iff n y g).1 hg
  have huu := toOriginWitness_solution M n y omega hu
  have hvv : IsDirichletSolutionAt
      (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) 0 n
      (toOriginWitness n y v) (fun x => g (y + x)) := by
    rw [isDirichletSolutionAt_iff_origin, originPullback_toOriginWitness]
    simpa using
      (isDirichletSolutionAt_iff_origin
        (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g).1 hv
  have h := le_localizedError M n 0 (Cutoff.translateCutoffSample y omega) hgu huu hvv
  rwa [eLpNorm_sub_toOrigin_eq] at h

private theorem translate_localizedError_le (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) :
    localizedError M n 0 (Cutoff.translateCutoffSample y omega) ≤
      localizedError M n y omega := by
  rw [localizedError_le_iff]
  intro g hg u hu v hv
  let gy : Vec d → Vec d := fun x => g (x - y)
  have hgy : NormalizedForceAt y n gy :=
    (normalizedForceAt_translate_iff n y gy).2 (by simpa [gy])
  have huu := fromOriginWitness_solution M n y omega hu
  have hvv : IsDirichletSolutionAt
      (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n
      (fromOriginWitness n y v) gy := by
    rw [isDirichletSolutionAt_iff_origin, originPullback_fromOriginWitness]
    have hv' := (isDirichletSolutionAt_iff_origin
        (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) 0 n v g).1 hv
    rw [originPullback_zero] at hv'
    simpa [gy] using
      hv'
  have h := le_localizedError M n y omega hgy huu hvv
  rwa [eLpNorm_sub_fromOrigin_eq] at h

/-- The localized error at `y + □_n` is the origin value of the translated sample. -/
theorem localizedError_eq_translateCutoffSample (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) :
    localizedError M n y omega =
      localizedError M n 0 (Cutoff.translateCutoffSample y omega) :=
  le_antisymm (localizedError_le_translate M n y omega)
    (translate_localizedError_le M n y omega)

/-! ## Moment identities -/

/-- Every real-power moment of the localized error is independent of the cube centre. -/
theorem lintegral_localizedError_rpow_eq_origin (M : ABKModel d) (n : ℤ) (y : Vec d)
    (p : ℝ) :
    (∫⁻ omega, localizedError M n y omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫⁻ omega, localizedError M n 0 omega ^ p ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  calc
    _ = ∫⁻ omega, localizedError M n 0 (Cutoff.translateCutoffSample y omega) ^ p
        ∂(Cutoff.cutoffSampleLaw M).toMeasure :=
      lintegral_congr fun omega => congrArg (fun z : ℝ≥0∞ => z ^ p)
        (localizedError_eq_translateCutoffSample M n y omega)
    _ = _ :=
      (Section4.Provider.GoodEvents.measurePreserving_translateCutoffSample M y).lintegral_comp
        (ENNReal.continuous_rpow_const.measurable.comp (measurable_localizedError M n 0))

end

end Algsuperdiff.Section5.Support
