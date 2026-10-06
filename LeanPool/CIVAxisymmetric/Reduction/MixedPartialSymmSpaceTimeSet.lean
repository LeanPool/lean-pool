/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet

/-!
# Mixed partial derivatives on an open product `Ω × I`

The smoothness of classical partial derivatives and the symmetry of mixed space and time
partial derivatives for a jointly smooth scalar field on an open space-time product. These are
the forms used on the cylinder `B(R) × (t₁, t₂)` of `thm:analytic:interior`.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- If a scalar field is jointly smooth on the open set `Ω × I`, so is each of its classical
spatial partial derivatives. -/
theorem contDiffOn_spatialPartial_spaceTimeSet {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g i z) (spaceTimeSet Ω I) := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z : Vec3 × ℝ => g z)) (spaceTimeSet Ω I) :=
    hg.fderiv_of_isOpen (hΩ.prod hI) (by norm_num)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => g w) z) (basisVec i, (0 : ℝ)))
      (spaceTimeSet Ω I) :=
    hD.clm_apply contDiffOn_const
  refine hE.congr fun z hz => ?_
  exact spatialPartial_eq_jointFDeriv
    ((hg.differentiableOn (by norm_num) z hz).differentiableAt
      ((hΩ.prod hI).mem_nhds hz)) i

/-- If a scalar field is jointly smooth on the open set `Ω × I`, so is its classical time partial
derivative. -/
theorem contDiffOn_timePartial_spaceTimeSet {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial g z) (spaceTimeSet Ω I) := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z : Vec3 × ℝ => g z)) (spaceTimeSet Ω I) :=
    hg.fderiv_of_isOpen (hΩ.prod hI) (by norm_num)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => g w) z) ((0 : Vec3), (1 : ℝ)))
      (spaceTimeSet Ω I) :=
    hD.clm_apply contDiffOn_const
  refine hE.congr fun z hz => ?_
  exact timePartial_eq_jointFDeriv
    ((hg.differentiableOn (by norm_num) z hz).differentiableAt
      ((hΩ.prod hI).mem_nhds hz))

private theorem fderiv_comp_apply_const_spaceTimeSet
    {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (V W : Vec3 × ℝ) :
    fderiv ℝ (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w V) z W
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z W V := by
  have hD1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun w : Vec3 × ℝ => g w)) (spaceTimeSet Ω I) :=
    hg.fderiv_of_isOpen (hΩ.prod hI) (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z :=
    (hD1.differentiableOn (by norm_num) z hz).differentiableAt
      ((hΩ.prod hI).mem_nhds hz)
  have hcomp : HasFDerivAt (fun w : Vec3 × ℝ => (fderiv ℝ (fun w' : Vec3 × ℝ => g w') w) V)
      ((ContinuousLinearMap.apply ℝ ℝ V).comp (fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z))
      z :=
    (ContinuousLinearMap.apply ℝ ℝ V).hasFDerivAt.comp (z : Vec3 × ℝ) hD.hasFDerivAt
  rw [hcomp.fderiv]
  simp

theorem spatialSecondPartial_eq_jointFDeriv2_spaceTimeSet
    {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (i j : Fin 3) :
    spatialSecondPartial g i j z
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z (basisVec j, 0) (basisVec i, 0) := by
  have hDiff2 : DifferentiableAt ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z :=
    ((contDiffOn_spatialPartial_spaceTimeSet hΩ hI hg i).differentiableOn (by norm_num) z
      hz).differentiableAt
      ((hΩ.prod hI).mem_nhds hz)
  have hstep1 : spatialSecondPartial g i j z
      = fderiv ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z (basisVec j, 0) :=
    spatialPartial_eq_jointFDeriv hDiff2 j
  have hev : (fun w : Vec3 × ℝ => spatialPartial g i w)
      =ᶠ[nhds z] (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w (basisVec i, 0)) := by
    filter_upwards [(hΩ.prod hI).mem_nhds hz] with w hw
    exact spatialPartial_eq_jointFDeriv
      ((hg.differentiableOn (by norm_num) w hw).differentiableAt
        ((hΩ.prod hI).mem_nhds hw)) i
  rw [hstep1, hev.fderiv_eq,
    fderiv_comp_apply_const_spaceTimeSet hΩ hI hg hz (basisVec i, 0) (basisVec j, 0)]

private theorem jointFDeriv2_symm_spaceTimeSet {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (V W : Vec3 × ℝ) :
    fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z V W
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z W V := by
  have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) z :=
    hg.contDiffAt ((hΩ.prod hI).mem_nhds hz)
  exact (hat.isSymmSndFDerivAt (by simp)).eq V W

/-- Cartesian mixed spatial partials of a jointly smooth scalar field commute. -/
theorem spatialSecondPartial_comm_spaceTimeSet {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (i j : Fin 3) :
    spatialSecondPartial g i j z = spatialSecondPartial g j i z := by
  rw [spatialSecondPartial_eq_jointFDeriv2_spaceTimeSet hΩ hI hg hz i j,
    spatialSecondPartial_eq_jointFDeriv2_spaceTimeSet hΩ hI hg hz j i,
    jointFDeriv2_symm_spaceTimeSet hΩ hI hg hz (basisVec j, 0) (basisVec i, 0)]

theorem spatialPartial_timePartial_eq_jointFDeriv2_spaceTimeSet
    {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (i : Fin 3) :
    spatialPartial (timePartial g) i z
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z (basisVec i, 0) (0, 1) := by
  have hDiff : DifferentiableAt ℝ (fun w : Vec3 × ℝ => timePartial g w) z :=
    ((contDiffOn_timePartial_spaceTimeSet hΩ hI hg).differentiableOn (by norm_num) z
      hz).differentiableAt
      ((hΩ.prod hI).mem_nhds hz)
  have hstep1 : spatialPartial (timePartial g) i z
      = fderiv ℝ (fun w : Vec3 × ℝ => timePartial g w) z (basisVec i, 0) :=
    spatialPartial_eq_jointFDeriv hDiff i
  have hev : (fun w : Vec3 × ℝ => timePartial g w)
      =ᶠ[nhds z] (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w (0, 1)) := by
    filter_upwards [(hΩ.prod hI).mem_nhds hz] with w hw
    exact timePartial_eq_jointFDeriv
      ((hg.differentiableOn (by norm_num) w hw).differentiableAt
        ((hΩ.prod hI).mem_nhds hw))
  rw [hstep1, hev.fderiv_eq,
    fderiv_comp_apply_const_spaceTimeSet hΩ hI hg hz (0, 1) (basisVec i, 0)]

theorem timePartial_spatialPartial_eq_jointFDeriv2_spaceTimeSet
    {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (i : Fin 3) :
    timePartial (spatialPartial g i) z
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z (0, 1) (basisVec i, 0) := by
  have hDiff : DifferentiableAt ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z :=
    ((contDiffOn_spatialPartial_spaceTimeSet hΩ hI hg i).differentiableOn (by norm_num) z
      hz).differentiableAt
      ((hΩ.prod hI).mem_nhds hz)
  have hstep1 : timePartial (spatialPartial g i) z
      = fderiv ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z (0, 1) :=
    timePartial_eq_jointFDeriv hDiff
  have hev : (fun w : Vec3 × ℝ => spatialPartial g i w)
      =ᶠ[nhds z] (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w (basisVec i, 0)) := by
    filter_upwards [(hΩ.prod hI).mem_nhds hz] with w hw
    exact spatialPartial_eq_jointFDeriv
      ((hg.differentiableOn (by norm_num) w hw).differentiableAt
        ((hΩ.prod hI).mem_nhds hw)) i
  rw [hstep1, hev.fderiv_eq,
    fderiv_comp_apply_const_spaceTimeSet hΩ hI hg hz (basisVec i, 0) (0, 1)]

/-- The classical spatial and time partial derivatives of a jointly smooth scalar field
commute. -/
theorem spatialPartial_timePartial_comm_spaceTimeSet {g : ParabolicPoint → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) (spaceTimeSet Ω I)) {z : Vec3 × ℝ}
    (hz : z ∈ (spaceTimeSet Ω I)) (i : Fin 3) :
    spatialPartial (timePartial g) i z = timePartial (spatialPartial g i) z := by
  rw [spatialPartial_timePartial_eq_jointFDeriv2_spaceTimeSet hΩ hI hg hz i,
    timePartial_spatialPartial_eq_jointFDeriv2_spaceTimeSet hΩ hI hg hz i,
    jointFDeriv2_symm_spaceTimeSet hΩ hI hg hz (basisVec i, 0) (0, 1)]

end CIV
