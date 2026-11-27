/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.ReferenceContourLocalInverse
public import LeanPool.VacuumBellSeparation.Shell.AugmentedInverseCoordinates

/-!
# All contour parameters, with mass retained

There are six active coordinates (five Lorentz parameters and radial
momentum), three other physical coordinates (boost3 and the two other
momenta), and one unchanged mass coordinate. The augmented map has the
same ten real dimensions in source and target. Keeping mass unchanged
lets one work uniformly through normalized mass zero.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Shell contour auxiliary with underlying type `ℝ × (Fin 3 → ℝ) abbrev ShellContourParameters :=
(Fin 6 → ℝ) × ShellContourAux`. -/
abbrev ShellContourAux := ℝ × (Fin 3 → ℝ)
/-- Shell contour parameters with underlying type `(Fin 6 → ℝ) × ShellContourAux`. -/
abbrev ShellContourParameters := (Fin 6 → ℝ) × ShellContourAux

/-- Full contour Lorentz parameters. -/
noncomputable def fullContourLorentzParameters (q : ShellContourParameters) : Fin 6 → ℝ :=
  ![q.1 0, q.1 1, q.1 2, q.1 3, q.1 4, q.2.2 0]

/-- Full contour momentum defined as `WithLp.toLp 2 ![q.2.2 1, B + q.1 5, q.2.2 2]`. -/
noncomputable def fullContourMomentum (B : ℝ) (q : ShellContourParameters) :
    EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![q.2.2 1, B + q.1 5, q.2.2 2]

/-- Full contour energy given by `Real.sqrt ((m + q.2.1) ^ 2 + ((q.2.2 1) ^ 2 + (B + q.1 5) ^ 2 +
(q.2.2 2) ^ 2))`. -/
noncomputable def fullContourEnergy (m B : ℝ) (q : ShellContourParameters) : ℝ :=
  Real.sqrt ((m + q.2.1) ^ 2 +
    ((q.2.2 1) ^ 2 + (B + q.1 5) ^ 2 + (q.2.2 2) ^ 2))

theorem fullContourEnergy_eq_dispersion (m B : ℝ) (q : ShellContourParameters) :
    fullContourEnergy m B q = dispersion (m + q.2.1) (fullContourMomentum B q) := by
  simp [fullContourEnergy, dispersion, fullContourMomentum,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem fullContourEnergy_zero (m B : ℝ) :
    fullContourEnergy m B 0 = radialShellEnergy m B 0 := by
  simp [fullContourEnergy, radialShellEnergy]

theorem contDiffAt_fullContourEnergy {B : ℝ} (hB : 0 < B) (m : ℝ) :
    ContDiffAt ℝ ⊤ (fullContourEnergy m B) 0 := by
  have h : ContDiff ℝ ⊤ (fun q : ShellContourParameters =>
      (m + q.2.1) ^ 2 + ((q.2.2 1) ^ 2 + (B + q.1 5) ^ 2 + (q.2.2 2) ^ 2)) := by
    fun_prop
  exact h.contDiffAt.sqrt (by
    simpa using (add_pos_of_nonneg_of_pos (sq_nonneg m) (sq_pos_of_pos hB)).ne')

/-- Full contour seed. -/
noncomputable def fullContourSeed (m B θ : ℝ) (q : ShellContourParameters) : ComplexSpacetime :=
  (((fullContourEnergy m B q * Real.cos θ : ℝ) : ℂ) +
      Complex.I * (q.2.2 1 * Real.sin θ : ℝ),
    ![((q.2.2 1 * Real.cos θ : ℝ) : ℂ) +
        Complex.I * (fullContourEnergy m B q * Real.sin θ : ℝ),
      ((B + q.1 5 : ℝ) : ℂ), (q.2.2 2 : ℂ)])

theorem fullContourSeed_eq_boost (m B θ : ℝ) (q : ShellContourParameters) :
    fullContourSeed m B θ q = complexShellBoost (m + q.2.1)
      ((θ : ℂ) * Complex.I) (fullContourMomentum B q) := by
  rw [complexShellBoost, ← fullContourEnergy_eq_dispersion,
    Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Prod.ext
  · simp [fullContourSeed, fullContourMomentum, Complex.ofReal_mul]; ring
  · ext i
    fin_cases i <;> simp [fullContourSeed, fullContourMomentum, Complex.ofReal_mul]
    ring

theorem contDiffAt_fullContourSeed {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    ContDiffAt ℝ ⊤ (fullContourSeed m B θ) 0 := by
  have hrealComplex {f : ShellContourParameters → ℝ}
      (hf : ContDiffAt ℝ ⊤ f 0) :
      ContDiffAt ℝ ⊤ (fun q => (f q : ℂ)) 0 := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using!
      Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hf
  have hec : ContDiffAt ℝ ⊤ (fun q : ShellContourParameters =>
      (fullContourEnergy m B q : ℂ)) 0 :=
    hrealComplex (contDiffAt_fullContourEnergy hB m)
  have hp (i : Fin 3) : ContDiffAt ℝ ⊤
      (fun q : ShellContourParameters => (q.2.2 i : ℂ)) 0 :=
    hrealComplex (((contDiff_apply ℝ (fun _ : Fin 3 => ℝ) i).comp
      (contDiff_snd.comp contDiff_snd) : ContDiff ℝ ⊤
        (fun q : ShellContourParameters => q.2.2 i)).contDiffAt)
  apply ContDiffAt.prodMk
  · change ContDiffAt ℝ ⊤ (fun q : ShellContourParameters =>
      ((fullContourEnergy m B q * Real.cos θ : ℝ) : ℂ) +
        Complex.I * (q.2.2 1 * Real.sin θ : ℝ)) 0
    simpa only [Complex.ofReal_mul, Pi.add_def, Pi.mul_def] using!
      (hec.mul contDiffAt_const).add (contDiffAt_const.mul
        ((hp 1).mul contDiffAt_const))
  · apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · change ContDiffAt ℝ ⊤ (fun q : ShellContourParameters =>
        ((q.2.2 1 * Real.cos θ : ℝ) : ℂ) +
          Complex.I * (fullContourEnergy m B q * Real.sin θ : ℝ)) 0
      simpa only [Complex.ofReal_mul, Pi.add_def, Pi.mul_def] using!
        ((hp 1).mul contDiffAt_const).add
          (contDiffAt_const.mul (hec.mul contDiffAt_const))
    · change ContDiffAt ℝ ⊤ (fun q : ShellContourParameters => ((B + q.1 5 : ℝ) : ℂ)) 0
      apply hrealComplex
      exact ((contDiff_const.add ((contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 5).comp
        contDiff_fst)) : ContDiff ℝ ⊤ (fun q : ShellContourParameters => B + q.1 5)).contDiffAt
    · exact hp 2

/-- Full contour map. -/
noncomputable def fullContourMap (m B θ : ℝ) (q : ShellContourParameters) : Fin 3 → ℂ :=
  complexShellCoordinates (complexLorentzFamilyAction (fullContourLorentzParameters q)
    (fullContourSeed m B θ q))

theorem contDiffAt_fullContourMap {B : ℝ} (hB : 0 < B) (m θ : ℝ) :
    ContDiffAt ℝ ⊤ (fullContourMap m B θ) 0 := by
  have hp : ContDiff ℝ ⊤ fullContourLorentzParameters := by
    unfold fullContourLorentzParameters
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 0)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 0).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 1)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 1).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 2)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 2).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 3)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 3).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.1 4)
      exact (contDiff_apply ℝ (fun _ : Fin 6 => ℝ) 4).comp contDiff_fst
    · change ContDiff ℝ ⊤ (fun q : ShellContourParameters => q.2.2 0)
      exact (contDiff_apply ℝ (fun _ : Fin 3 => ℝ) 0).comp (contDiff_snd.comp contDiff_snd)
  have hf : ContDiffAt ℝ ⊤ (fun q : ShellContourParameters =>
      complexLorentzFamilyAction (fullContourLorentzParameters q)
        (fullContourSeed m B θ q)) 0 :=
    contDiff_complexLorentzFamilyAction.comp₂_contDiffAt
      hp.contDiffAt (contDiffAt_fullContourSeed hB m θ)
  -- Project the actual coordinates directly, avoiding the expanded Pi
  -- restrictScalars composition and its duplicate real-module search.
  unfold fullContourMap
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hf.fst
  · exact contDiffAt_pi.mp hf.snd 0
  · exact contDiffAt_pi.mp hf.snd 2

theorem fullContourMap_active_slice (m B θ : ℝ) (a : Fin 6 → ℝ) :
    fullContourMap m B θ (a, 0) = referenceContourMap m B θ a := by
  have hp : fullContourLorentzParameters (a, 0) = activeLorentzParameters a := rfl
  have hz : fullContourSeed m B θ (a, 0) = radialShellContour m B θ (a 5) := by
    apply Prod.ext
    · simp [fullContourSeed, radialShellContour, fullContourEnergy, radialShellEnergy]
    · ext i
      fin_cases i <;>
        simp [fullContourSeed, radialShellContour, fullContourEnergy, radialShellEnergy]
  simp only [fullContourMap, referenceContourMap, hp, hz]

/-- Full contour local coordinates. -/
noncomputable def fullContourLocalCoordinates (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    OpenPartialHomeomorph ShellContourParameters ((Fin 3 → ℂ) × ShellContourAux) :=
  augmentedLocalCoordinates (contDiffAt_fullContourMap hB m θ)
    (referenceContourDerivativeEquiv m hB hθ) (by
      simp only [fullContourMap_active_slice, referenceContourDerivativeEquiv_coe]
      exact hasFDerivAt_referenceContourMap hB m θ)

theorem fullContourLocalCoordinates_apply (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (q : ShellContourParameters) :
    fullContourLocalCoordinates m hB hθ q = (fullContourMap m B θ q, q.2) := rfl

theorem zero_mem_fullContourLocalCoordinates (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    0 ∈ (fullContourLocalCoordinates m hB hθ).source :=
  zero_mem_augmentedLocalCoordinates _ _ _

theorem fullContourLocalCoordinates_inverse_aux (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    {y : (Fin 3 → ℂ) × ShellContourAux}
    (hy : y ∈ (fullContourLocalCoordinates m hB hθ).target) :
    ((fullContourLocalCoordinates m hB hθ).symm y).2 = y.2 := by
  exact congrArg Prod.snd ((fullContourLocalCoordinates m hB hθ).right_inv hy)

end VacuumBellSeparation
