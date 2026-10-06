/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus
public import LeanPool.CIVAxisymmetric.Identities.ScalarSystemR
public import LeanPool.CIVAxisymmetric.Identities.ScalarSystemZ
public import LeanPool.CIVAxisymmetric.Identities.Vorticity
public import LeanPool.CIVAxisymmetric.Identities.PotentialVorticity
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Vorticity Equation

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The classical spatial partial derivative is the joint Fréchet derivative applied to the
embedded spatial direction. -/
theorem spatialPartial_eq_jointFDeriv {g : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) z) (i : Fin 3) :
    spatialPartial g i z = fderiv ℝ (fun w : Vec3 × ℝ => g w) z (basisVec i, 0) := by
  have hcomp : HasFDerivAt (fun x : Vec3 => g (x, z.2))
      ((fderiv ℝ (fun w : Vec3 × ℝ => g w) z).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)) z.1 :=
    hg.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  show fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1 (basisVec i) = _
  rw [hcomp.fderiv]
  rfl

/-- The classical time partial derivative is the joint Fréchet derivative applied to the
embedded time direction. -/
theorem timePartial_eq_jointFDeriv {g : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) z) :
    timePartial g z = fderiv ℝ (fun w : Vec3 × ℝ => g w) z (0, 1) := by
  have hcomp : HasFDerivAt (fun s : ℝ => g (z.1, s))
      ((fderiv ℝ (fun w : Vec3 × ℝ => g w) z).comp (ContinuousLinearMap.inr ℝ Vec3 ℝ)) z.2 :=
    hg.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)
  show fderiv ℝ (fun s : ℝ => g (z.1, s)) z.2 1 = _
  rw [hcomp.fderiv]
  rfl

/-- If a scalar field is jointly smooth on the unit cylinder, so is each of its classical
spatial partial derivatives. -/
theorem contDiffOn_spatialPartial {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) (i : Fin 3) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial g i z) unitCylinder := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z : Vec3 × ℝ => g z)) unitCylinder :=
    hg.fderiv_of_isOpen isOpen_unitCylinder_prod (by norm_num)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => g w) z) (basisVec i, (0 : ℝ)))
      unitCylinder :=
    hD.clm_apply contDiffOn_const
  refine hE.congr fun z hz => ?_
  exact spatialPartial_eq_jointFDeriv
    ((hg.differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)) i

/-- If a scalar field is jointly smooth on the unit cylinder, so is its classical time partial
derivative. -/
theorem contDiffOn_timePartial {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial g z) unitCylinder := by
  have hD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun z : Vec3 × ℝ => g z)) unitCylinder :=
    hg.fderiv_of_isOpen isOpen_unitCylinder_prod (by norm_num)
  have hE : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => (fderiv ℝ (fun w : Vec3 × ℝ => g w) z) ((0 : Vec3), (1 : ℝ)))
      unitCylinder :=
    hD.clm_apply contDiffOn_const
  refine hE.congr fun z hz => ?_
  exact timePartial_eq_jointFDeriv
    ((hg.differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz))

private theorem fderiv_comp_apply_const {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (V W : Vec3 × ℝ) :
    fderiv ℝ (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w V) z W
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z W V := by
  have hD1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fun w : Vec3 × ℝ => g w)) unitCylinder :=
    hg.fderiv_of_isOpen isOpen_unitCylinder_prod (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z :=
    (hD1.differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  have hcomp : HasFDerivAt (fun w : Vec3 × ℝ => (fderiv ℝ (fun w' : Vec3 × ℝ => g w') w) V)
      ((ContinuousLinearMap.apply ℝ ℝ V).comp (fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z))
      z :=
    (ContinuousLinearMap.apply ℝ ℝ V).hasFDerivAt.comp (z : Vec3 × ℝ) hD.hasFDerivAt
  rw [hcomp.fderiv]
  simp

theorem spatialSecondPartial_eq_jointFDeriv2 {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialSecondPartial g i j z
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z (basisVec j, 0) (basisVec i, 0) := by
  have hDiff2 : DifferentiableAt ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z :=
    ((contDiffOn_spatialPartial hg i).differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  have hstep1 : spatialSecondPartial g i j z
      = fderiv ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z (basisVec j, 0) :=
    spatialPartial_eq_jointFDeriv hDiff2 j
  have hev : (fun w : Vec3 × ℝ => spatialPartial g i w)
      =ᶠ[nhds z] (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w (basisVec i, 0)) := by
    filter_upwards [isOpen_unitCylinder_prod.mem_nhds hz] with w hw
    exact spatialPartial_eq_jointFDeriv
      ((hg.differentiableOn (by norm_num) w hw).differentiableAt
        (isOpen_unitCylinder_prod.mem_nhds hw)) i
  rw [hstep1, hev.fderiv_eq, fderiv_comp_apply_const hg hz (basisVec i, 0) (basisVec j, 0)]

private theorem jointFDeriv2_symm {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (V W : Vec3 × ℝ) :
    fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z V W
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z W V := by
  have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => g w) z :=
    hg.contDiffAt (isOpen_unitCylinder_prod.mem_nhds hz)
  exact (hat.isSymmSndFDerivAt (by simp)).eq V W

/-- Cartesian mixed spatial partials of a jointly smooth scalar field commute. -/
theorem spatialSecondPartial_comm {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i j : Fin 3) :
    spatialSecondPartial g i j z = spatialSecondPartial g j i z := by
  rw [spatialSecondPartial_eq_jointFDeriv2 hg hz i j, spatialSecondPartial_eq_jointFDeriv2 hg hz
    j i,
    jointFDeriv2_symm hg hz (basisVec j, 0) (basisVec i, 0)]

theorem spatialPartial_timePartial_eq_jointFDeriv2 {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    spatialPartial (timePartial g) i z
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z (basisVec i, 0) (0, 1) := by
  have hDiff : DifferentiableAt ℝ (fun w : Vec3 × ℝ => timePartial g w) z :=
    ((contDiffOn_timePartial hg).differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  have hstep1 : spatialPartial (timePartial g) i z
      = fderiv ℝ (fun w : Vec3 × ℝ => timePartial g w) z (basisVec i, 0) :=
    spatialPartial_eq_jointFDeriv hDiff i
  have hev : (fun w : Vec3 × ℝ => timePartial g w)
      =ᶠ[nhds z] (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w (0, 1)) := by
    filter_upwards [isOpen_unitCylinder_prod.mem_nhds hz] with w hw
    exact timePartial_eq_jointFDeriv
      ((hg.differentiableOn (by norm_num) w hw).differentiableAt
        (isOpen_unitCylinder_prod.mem_nhds hw))
  rw [hstep1, hev.fderiv_eq, fderiv_comp_apply_const hg hz (0, 1) (basisVec i, 0)]

theorem timePartial_spatialPartial_eq_jointFDeriv2 {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    timePartial (spatialPartial g i) z
      = fderiv ℝ (fderiv ℝ (fun w : Vec3 × ℝ => g w)) z (0, 1) (basisVec i, 0) := by
  have hDiff : DifferentiableAt ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z :=
    ((contDiffOn_spatialPartial hg i).differentiableOn (by norm_num) z hz).differentiableAt
      (isOpen_unitCylinder_prod.mem_nhds hz)
  have hstep1 : timePartial (spatialPartial g i) z
      = fderiv ℝ (fun w : Vec3 × ℝ => spatialPartial g i w) z (0, 1) :=
    timePartial_eq_jointFDeriv hDiff
  have hev : (fun w : Vec3 × ℝ => spatialPartial g i w)
      =ᶠ[nhds z] (fun w : Vec3 × ℝ => fderiv ℝ (fun w' : Vec3 × ℝ => g w') w (basisVec i, 0)) := by
    filter_upwards [isOpen_unitCylinder_prod.mem_nhds hz] with w hw
    exact spatialPartial_eq_jointFDeriv
      ((hg.differentiableOn (by norm_num) w hw).differentiableAt
        (isOpen_unitCylinder_prod.mem_nhds hw)) i
  rw [hstep1, hev.fderiv_eq, fderiv_comp_apply_const hg hz (basisVec i, 0) (0, 1)]

/-- The classical spatial and time partial derivatives of a jointly smooth scalar field
commute. -/
theorem spatialPartial_timePartial_comm {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i : Fin 3) :
    spatialPartial (timePartial g) i z = timePartial (spatialPartial g i) z := by
  rw [spatialPartial_timePartial_eq_jointFDeriv2 hg hz i,
    timePartial_spatialPartial_eq_jointFDeriv2 hg hz i,
    jointFDeriv2_symm hg hz (basisVec i, 0) (0, 1)]

/-- The angular component of a point of the meridional plane vanishes. -/
private theorem meridional_apply_one (a b : ℝ) : (meridional a b : Vec3) 1 = 0 := by
  simp [meridional]

/-- The axial component of a point of the meridional plane. -/
private theorem meridional_apply_two (a b : ℝ) : (meridional a b : Vec3) 2 = b := by
  simp [meridional]

/-- `meridional` decomposes along the radial and axial basis vectors, radial term first. -/
private theorem meridional_eq_smul_add (a b : ℝ) :
    (meridional a b : Vec3) = a • (basisVec 0 : Vec3) + b • (basisVec 2 : Vec3) := by
  ext i
  fin_cases i <;> simp [meridional, basisVec_apply]

/-- `meridional` decomposes along the radial and axial basis vectors, axial term first. -/
private theorem meridional_eq_smul_add' (a b : ℝ) :
    (meridional a b : Vec3) = b • (basisVec 2 : Vec3) + a • (basisVec 0 : Vec3) := by
  rw [meridional_eq_smul_add, add_comm]

/-- The chain rule along an affine line, phrased through the spatial slice of a jointly `C¹`
scalar field. -/
private theorem hasDerivAt_affine_slice {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    (v x0 : Vec3) (t a : ℝ) (hz : ((a • v + x0 : Vec3), t) ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => g (s • v + x0, t))
      (fderiv ℝ (fun y : Vec3 => g (y, t)) (a • v + x0) v) a := by
  have hk : HasDerivAt (fun s : ℝ => (s • v + x0 : Vec3)) v a := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) a := (hasDerivAt_id a).smul_const v
    simpa using h1.add_const x0
  have hL : HasFDerivAt (fun y : Vec3 => g (y, t))
      (fderiv ℝ (fun y : Vec3 => g (y, t)) (a • v + x0)) (a • v + x0) :=
    (differentiableAt_spatialSlice hg hz).hasFDerivAt
  exact hL.comp_hasDerivAt a hk

/-- Differentiating along the meridional plane in the radial direction, at fixed axial
coordinate and time, gives the classical radial spatial partial derivative
(the critical subtlety: `eq:aniso:scalar:nse:r` holds only on the meridional plane, so this
one-dimensional chain rule, not a naive Cartesian derivative, is what lets us differentiate
it). -/
theorem hasDerivAt_meridional_zero {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    {a b t : ℝ} (hz : ((meridional a b : Vec3), t) ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => g (meridional s b, t)) (spatialPartial g 0 (meridional a b, t)) a := by
  have hz' : ((a • (basisVec 0 : Vec3) + b • (basisVec 2 : Vec3) : Vec3), t) ∈ unitCylinder := by
    rw [← meridional_eq_smul_add]; exact hz
  have hd := hasDerivAt_affine_slice hg (basisVec 0) (b • basisVec 2) t a hz'
  simp only [← meridional_eq_smul_add] at hd
  exact hd

/-- Differentiating along the meridional plane in the axial direction, at fixed radial
coordinate and time, gives the classical axial spatial partial derivative (the same critical
subtlety as `hasDerivAt_meridional_zero`). -/
theorem hasDerivAt_meridional_two {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder)
    {a b t : ℝ} (hz : ((meridional a b : Vec3), t) ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => g (meridional a s, t)) (spatialPartial g 2 (meridional a b, t)) b := by
  have hz' : ((b • (basisVec 2 : Vec3) + a • (basisVec 0 : Vec3) : Vec3), t) ∈ unitCylinder := by
    rw [← meridional_eq_smul_add']; exact hz
  have hd := hasDerivAt_affine_slice hg (basisVec 2) (a • basisVec 0) t b hz'
  simp only [← meridional_eq_smul_add'] at hd
  exact hd

/-- A classical spatial partial derivative only sees a scalar field through its values on the
unit cylinder. -/
private theorem spatialPartial_congr_of_eqOn {f g : ParabolicPoint → ℝ}
    (h : ∀ w ∈ unitCylinder, f w = g w) {z : Vec3 × ℝ} (hz : z ∈ unitCylinder) (k : Fin 3) :
    spatialPartial f k z = spatialPartial g k z := by
  have hev : f =ᶠ[nhds z] g := Filter.eventuallyEq_of_mem (isOpen_unitCylinder_prod.mem_nhds hz) h
  have htend : Filter.Tendsto (fun y : Vec3 => (y, z.2)) (nhds z.1) (nhds z) := by
    have hc : Continuous (fun y : Vec3 => (y, z.2)) := continuous_id.prodMk continuous_const
    simpa using hc.tendsto z.1
  have hevSlice : (fun y : Vec3 => f (y, z.2)) =ᶠ[nhds z.1] (fun y : Vec3 => g (y, z.2)) :=
    htend.eventually hev
  show fderiv ℝ (fun y : Vec3 => f (y, z.2)) z.1 (basisVec k)
      = fderiv ℝ (fun y : Vec3 => g (y, z.2)) z.1 (basisVec k)
  rw [hevSlice.fderiv_eq]

/-- Reordering the outer two directions of a third-order iterated spatial partial derivative
of a jointly smooth scalar field. -/
private theorem T3_swap_outer {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i j k : Fin 3) :
    spatialPartial (spatialSecondPartial g i j) k z
      = spatialPartial (spatialSecondPartial g i k) j z :=
  spatialSecondPartial_comm (contDiffOn_spatialPartial hg i) hz j k

/-- Reordering the inner two directions of a third-order iterated spatial partial derivative
of a jointly smooth scalar field. -/
private theorem T3_swap_inner {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) (i j k : Fin 3) :
    spatialPartial (spatialSecondPartial g i j) k z
      = spatialPartial (spatialSecondPartial g j i) k z :=
  spatialPartial_congr_of_eqOn (fun _w hw => spatialSecondPartial_comm hg hw i j) hz k

/-- The reordering `(0,0,2) → (2,0,0)` of a third-order iterated spatial partial derivative,
needed to match the axial differentiation of `scalar_nse_r` against `spatialSecondPartial` of
the azimuthal vorticity. -/
private theorem T3_reorder_002_200 {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) :
    spatialPartial (spatialSecondPartial g 0 0) 2 z
      = spatialPartial (spatialSecondPartial g 2 0) 0 z :=
  (T3_swap_outer hg hz 0 0 2).trans (T3_swap_inner hg hz 0 2 0)

/-- The reordering `(2,2,0) → (0,2,2)` of a third-order iterated spatial partial derivative,
needed to match the radial differentiation of `scalar_nse_z` against `spatialSecondPartial` of
the azimuthal vorticity. -/
private theorem T3_reorder_220_022 {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) :
    spatialPartial (spatialSecondPartial g 2 2) 0 z
      = spatialPartial (spatialSecondPartial g 0 2) 2 z :=
  (T3_swap_outer hg hz 2 2 0).trans (T3_swap_inner hg hz 2 0 2)

/-- `hasDerivAt_meridional_zero`, restated so the basepoint and derivative value are read off
directly at the point itself. -/
theorem hasDerivAt_meridional_zero_at {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) :
    HasDerivAt (fun s : ℝ => g (meridional s (z.1 2), z.2)) (spatialPartial g 0 z) (z.1 0) := by
  have hzeq : (z.1 : Vec3) = meridional (z.1 0) (z.1 2) := by
    ext i; fin_cases i <;> simp [meridional, hplane]
  have hz' : ((meridional (z.1 0) (z.1 2) : Vec3), z.2) ∈ unitCylinder := by rw [← hzeq]; exact hz
  have hd := hasDerivAt_meridional_zero hg hz'
  rwa [← hzeq] at hd

/-- `hasDerivAt_meridional_two`, restated so the basepoint and derivative value are read off
directly at the point itself. -/
theorem hasDerivAt_meridional_two_at {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => g z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) :
    HasDerivAt (fun s : ℝ => g (meridional (z.1 0) s, z.2)) (spatialPartial g 2 z) (z.1 2) := by
  have hzeq : (z.1 : Vec3) = meridional (z.1 0) (z.1 2) := by
    ext i; fin_cases i <;> simp [meridional, hplane]
  have hz' : ((meridional (z.1 0) (z.1 2) : Vec3), z.2) ∈ unitCylinder := by rw [← hzeq]; exact hz
  have hd := hasDerivAt_meridional_two hg hz'
  rwa [← hzeq] at hd

/-- The radial coordinates for which a fixed axial slice of the meridional plane stays in the
unit cylinder form an open set. -/
private theorem isOpen_meridional_radial_slice (b t : ℝ) :
    IsOpen {s : ℝ | ((meridional s b : Vec3), t) ∈ unitCylinder} := by
  have hcont : Continuous (fun s : ℝ => ((meridional s b : Vec3), t)) := by
    apply Continuous.prodMk _ continuous_const
    unfold meridional; fun_prop
  exact isOpen_unitCylinder_prod.preimage hcont

/-- The axial coordinates for which a fixed radial slice of the meridional plane stays in the
unit cylinder form an open set. -/
private theorem isOpen_meridional_axial_slice (a t : ℝ) :
    IsOpen {s : ℝ | ((meridional a s : Vec3), t) ∈ unitCylinder} := by
  have hcont : Continuous (fun s : ℝ => ((meridional a s : Vec3), t)) := by
    apply Continuous.prodMk _ continuous_const
    unfold meridional; fun_prop
  exact isOpen_unitCylinder_prod.preimage hcont

/-- Differentiating `scalar_nse_r` in the axial direction, in raw Cartesian partial
derivatives. -/
private theorem raw_theta_axial
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (spatialPartial (fun w => u w 0) 2) z
        + spatialPartial (fun w => u w 0) 2 z * spatialPartial (fun w => u w 0) 0 z
        + u z 0 * spatialSecondPartial (fun w => u w 0) 0 2 z
        + spatialPartial (fun w => u w 2) 2 z * spatialPartial (fun w => u w 0) 2 z
        + u z 2 * spatialSecondPartial (fun w => u w 0) 2 2 z
        - 2 * u z 1 * spatialPartial (fun w => u w 1) 2 z / z.1 0 =
      spatialPartial (spatialSecondPartial (fun w => u w 0) 0 0) 2 z
        + spatialSecondPartial (fun w => u w 0) 0 2 z / z.1 0
        + spatialPartial (spatialSecondPartial (fun w => u w 0) 2 2) 2 z
        - spatialPartial (fun w => u w 0) 2 z / (z.1 0) ^ 2
        - spatialSecondPartial p 0 2 z
        + spatialPartial (fun w => f w 0) 2 z := by
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1
  have hpTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1
  have hfTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w) unitCylinder := hsol.2.2.1
  have hAtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 0) unitCylinder :=
    contDiffOn_component huTop 0
  have hCtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 2) unitCylinder :=
    contDiffOn_component huTop 2
  have hBtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 1) unitCylinder :=
    contDiffOn_component huTop 1
  have hf0top : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w 0) unitCylinder :=
    contDiffOn_component hfTop 0
  have hA0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 0) 0 w)
      unitCylinder := contDiffOn_spatialPartial hAtop 0
  have hA2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 0) 2 w)
      unitCylinder := contDiffOn_spatialPartial hAtop 2
  have hB2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 1) 2 w)
      unitCylinder := contDiffOn_spatialPartial hBtop 2
  have hA00 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 0) 0 0 w) unitCylinder :=
    contDiffOn_spatialPartial hA0 0
  have hA22 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 0) 2 2 w) unitCylinder :=
    contDiffOn_spatialPartial hA2 2
  have hAt : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => timePartial (fun v => u v 0) w)
      unitCylinder := contDiffOn_timePartial hAtop
  have hp0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial p 0 w) unitCylinder :=
    contDiffOn_spatialPartial hpTop 0
  have hzeq : (z.1 : Vec3) = meridional (z.1 0) (z.1 2) := by
    ext i; fin_cases i <;> simp [meridional, hplane]
  -- The `HasDerivAt` pieces along the fixed-radius axial line through `z`.
  have hdAt0 := hasDerivAt_meridional_two_at (g := timePartial (fun v => u v 0))
    (hAt.of_le (by norm_num)) hz hplane
  have hdAt : HasDerivAt (fun s : ℝ => timePartial (fun v => u v 0) (meridional (z.1 0) s, z.2))
      (timePartial (spatialPartial (fun v => u v 0) 2) z) (z.1 2) :=
    (spatialPartial_timePartial_comm hAtop hz 2) ▸ hdAt0
  have hdA := hasDerivAt_meridional_two_at (g := fun v => u v 0)
    (hAtop.of_le (by norm_num)) hz hplane
  have hdA0 := hasDerivAt_meridional_two_at (g := spatialPartial (fun v => u v 0) 0)
    (hA0.of_le (by norm_num)) hz hplane
  have hdC := hasDerivAt_meridional_two_at (g := fun v => u v 2)
    (hCtop.of_le (by norm_num)) hz hplane
  have hdA2 := hasDerivAt_meridional_two_at (g := spatialPartial (fun v => u v 0) 2)
    (hA2.of_le (by norm_num)) hz hplane
  have hdB := hasDerivAt_meridional_two_at (g := fun v => u v 1)
    (hBtop.of_le (by norm_num)) hz hplane
  have hdA00 := hasDerivAt_meridional_two_at (g := spatialSecondPartial (fun v => u v 0) 0 0)
    (hA00.of_le (by norm_num)) hz hplane
  have hdp0 := hasDerivAt_meridional_two_at (g := spatialPartial p 0)
    (hp0.of_le (by norm_num)) hz hplane
  have hdf0 := hasDerivAt_meridional_two_at (g := fun v => f v 0)
    (hf0top.of_le (by norm_num)) hz hplane
  have hdA22 := hasDerivAt_meridional_two_at (g := spatialSecondPartial (fun v => u v 0) 2 2)
    (hA22.of_le (by norm_num)) hz hplane
  have hLHS := ((hdAt.add (hdA.mul hdA0)).add (hdC.mul hdA2)).sub
    ((hdB.pow 2).div_const (z.1 0))
  have hRHS := (((hdA00.add (hdA0.div_const (z.1 0))).add hdA22).sub
    (hdA.div_const ((z.1 0) ^ 2))).sub hdp0 |>.add hdf0
  have hSopen := isOpen_meridional_axial_slice (z.1 0) z.2
  have hSmem : z.1 2 ∈ {s : ℝ | ((meridional (z.1 0) s : Vec3), z.2) ∈ unitCylinder} := by
    show ((meridional (z.1 0) (z.1 2) : Vec3), z.2) ∈ unitCylinder
    rw [← hzeq]; exact hz
  have heq : (fun s : ℝ => timePartial (fun w => u w 0) (meridional (z.1 0) s, z.2)
        + u (meridional (z.1 0) s, z.2) 0
          * spatialPartial (fun w => u w 0) 0 (meridional (z.1 0) s, z.2)
        + u (meridional (z.1 0) s, z.2) 2
          * spatialPartial (fun w => u w 0) 2 (meridional (z.1 0) s, z.2)
        - u (meridional (z.1 0) s, z.2) 1 ^ 2 / z.1 0)
      =ᶠ[nhds (z.1 2)]
      (fun s : ℝ => spatialSecondPartial (fun w => u w 0) 0 0 (meridional (z.1 0) s, z.2)
        + spatialPartial (fun w => u w 0) 0 (meridional (z.1 0) s, z.2) / z.1 0
        + spatialSecondPartial (fun w => u w 0) 2 2 (meridional (z.1 0) s, z.2)
        - u (meridional (z.1 0) s, z.2) 0 / z.1 0 ^ 2
        - spatialPartial p 0 (meridional (z.1 0) s, z.2)
        + f (meridional (z.1 0) s, z.2) 0) := by
    filter_upwards [hSopen.mem_nhds hSmem] with s hs
    have hplane' : (meridional (z.1 0) s, z.2).1 1 = (0 : ℝ) := meridional_apply_one (z.1 0) s
    have hr' : (meridional (z.1 0) s, z.2).1 0 ≠ 0 := by
      simp only [meridional_apply_zero]; exact hr
    have hkey := scalar_nse_r u p f hsol haxi (meridional (z.1 0) s, z.2) hs hplane' hr'
    simpa only [meridional_apply_zero] using hkey
  have hRHS' := hRHS.congr_of_eventuallyEq heq
  have hEuniq := hLHS.unique hRHS'
  have hpteq : ((meridional (z.1 0) (z.1 2) : Vec3), z.2) = z := Prod.ext hzeq.symm rfl
  rw [hpteq] at hEuniq
  simp only [spatialSecondPartial] at hEuniq ⊢
  linear_combination hEuniq

/-- Differentiating `scalar_nse_z` in the radial direction, in raw Cartesian partial
derivatives. -/
private theorem raw_theta_radial
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (spatialPartial (fun w => u w 2) 0) z
        + spatialPartial (fun w => u w 0) 0 z * spatialPartial (fun w => u w 2) 0 z
        + u z 0 * spatialSecondPartial (fun w => u w 2) 0 0 z
        + spatialPartial (fun w => u w 2) 0 z * spatialPartial (fun w => u w 2) 2 z
        + u z 2 * spatialSecondPartial (fun w => u w 2) 2 0 z =
      spatialPartial (spatialSecondPartial (fun w => u w 2) 0 0) 0 z
        + (spatialSecondPartial (fun w => u w 2) 0 0 z * z.1 0
            - spatialPartial (fun w => u w 2) 0 z) / (z.1 0) ^ 2
        + spatialPartial (spatialSecondPartial (fun w => u w 2) 2 2) 0 z
        - spatialSecondPartial p 2 0 z
        + spatialPartial (fun w => f w 2) 0 z := by
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1
  have hpTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1
  have hfTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w) unitCylinder := hsol.2.2.1
  have hAtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 0) unitCylinder :=
    contDiffOn_component huTop 0
  have hCtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 2) unitCylinder :=
    contDiffOn_component huTop 2
  have hf2top : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => f w 2) unitCylinder :=
    contDiffOn_component hfTop 2
  have hC0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 2) 0 w)
      unitCylinder := contDiffOn_spatialPartial hCtop 0
  have hC2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 2) 2 w)
      unitCylinder := contDiffOn_spatialPartial hCtop 2
  have hC00 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 2) 0 0 w) unitCylinder :=
    contDiffOn_spatialPartial hC0 0
  have hC22 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 2) 2 2 w) unitCylinder :=
    contDiffOn_spatialPartial hC2 2
  have hCt : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => timePartial (fun v => u v 2) w)
      unitCylinder := contDiffOn_timePartial hCtop
  have hp2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial p 2 w) unitCylinder :=
    contDiffOn_spatialPartial hpTop 2
  have hzeq : (z.1 : Vec3) = meridional (z.1 0) (z.1 2) := by
    ext i; fin_cases i <;> simp [meridional, hplane]
  have hdCt0 := hasDerivAt_meridional_zero_at (g := timePartial (fun v => u v 2))
    (hCt.of_le (by norm_num)) hz hplane
  have hdCt : HasDerivAt (fun s : ℝ => timePartial (fun v => u v 2) (meridional s (z.1 2), z.2))
      (timePartial (spatialPartial (fun v => u v 2) 0) z) (z.1 0) :=
    (spatialPartial_timePartial_comm hCtop hz 0) ▸ hdCt0
  have hdA := hasDerivAt_meridional_zero_at (g := fun v => u v 0)
    (hAtop.of_le (by norm_num)) hz hplane
  have hdC0 := hasDerivAt_meridional_zero_at (g := spatialPartial (fun v => u v 2) 0)
    (hC0.of_le (by norm_num)) hz hplane
  have hdC := hasDerivAt_meridional_zero_at (g := fun v => u v 2)
    (hCtop.of_le (by norm_num)) hz hplane
  have hdC2 := hasDerivAt_meridional_zero_at (g := spatialPartial (fun v => u v 2) 2)
    (hC2.of_le (by norm_num)) hz hplane
  have hdC00 := hasDerivAt_meridional_zero_at (g := spatialSecondPartial (fun v => u v 2) 0 0)
    (hC00.of_le (by norm_num)) hz hplane
  have hdp2 := hasDerivAt_meridional_zero_at (g := spatialPartial p 2)
    (hp2.of_le (by norm_num)) hz hplane
  have hdf2 := hasDerivAt_meridional_zero_at (g := fun v => f v 2)
    (hf2top.of_le (by norm_num)) hz hplane
  have hdC22 := hasDerivAt_meridional_zero_at (g := spatialSecondPartial (fun v => u v 2) 2 2)
    (hC22.of_le (by norm_num)) hz hplane
  have hdDenom : HasDerivAt (fun s : ℝ => (meridional s (z.1 2), z.2).1 0) 1 (z.1 0) := by
    have heqfun : (fun s : ℝ => (meridional s (z.1 2), z.2).1 0) = fun s : ℝ => s := by
      funext s; exact meridional_apply_zero s (z.1 2)
    rw [heqfun]; exact hasDerivAt_id (z.1 0)
  have hxne : (meridional (z.1 0) (z.1 2), z.2).1 0 ≠ 0 := by
    simp only [meridional_apply_zero]; exact hr
  have hdQuot := hdC0.fun_div hdDenom hxne
  have hLHS := ((hdCt.add (hdA.mul hdC0)).add (hdC.mul hdC2))
  have hRHS := ((hdC00.add hdQuot).add hdC22).sub hdp2 |>.add hdf2
  have hSopen := isOpen_meridional_radial_slice (z.1 2) z.2
  have hSmem : z.1 0 ∈ {s : ℝ | ((meridional s (z.1 2) : Vec3), z.2) ∈ unitCylinder} := by
    show ((meridional (z.1 0) (z.1 2) : Vec3), z.2) ∈ unitCylinder
    rw [← hzeq]; exact hz
  have heq : (fun s : ℝ => timePartial (fun w => u w 2) (meridional s (z.1 2), z.2)
        + u (meridional s (z.1 2), z.2) 0
          * spatialPartial (fun w => u w 2) 0 (meridional s (z.1 2), z.2)
        + u (meridional s (z.1 2), z.2) 2
          * spatialPartial (fun w => u w 2) 2 (meridional s (z.1 2), z.2))
      =ᶠ[nhds (z.1 0)]
      (fun s : ℝ => spatialSecondPartial (fun w => u w 2) 0 0 (meridional s (z.1 2), z.2)
        + spatialPartial (fun w => u w 2) 0 (meridional s (z.1 2), z.2)
          / (meridional s (z.1 2), z.2).1 0
        + spatialSecondPartial (fun w => u w 2) 2 2 (meridional s (z.1 2), z.2)
        - spatialPartial p 2 (meridional s (z.1 2), z.2)
        + f (meridional s (z.1 2), z.2) 2) := by
    have hS2open : IsOpen {s : ℝ | s ≠ 0} := isOpen_ne
    filter_upwards [(hSopen.inter hS2open).mem_nhds (Set.mem_inter hSmem hr)] with s hs
    have hplane' : (meridional s (z.1 2), z.2).1 1 = (0 : ℝ) := meridional_apply_one s (z.1 2)
    have hr' : (meridional s (z.1 2), z.2).1 0 ≠ 0 := by
      simp only [meridional_apply_zero]; exact hs.2
    have hkey := scalar_nse_z u p f hsol haxi (meridional s (z.1 2), z.2) hs.1 hplane' hr'
    simpa only [meridional_apply_zero] using hkey
  have hRHS' := hRHS.congr_of_eventuallyEq heq
  have hEuniq := hLHS.unique hRHS'
  have hpteq : ((meridional (z.1 0) (z.1 2) : Vec3), z.2) = z := Prod.ext hzeq.symm rfl
  rw [hpteq] at hEuniq
  simp only [spatialSecondPartial] at hEuniq ⊢
  linear_combination hEuniq

/-- The classical time partial derivative is linear over subtraction. -/
private theorem timePartial_sub {f g : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hf : DifferentiableAt ℝ (fun s : ℝ => f (z.1, s)) z.2)
    (hg : DifferentiableAt ℝ (fun s : ℝ => g (z.1, s)) z.2) :
    timePartial (fun w => f w - g w) z = timePartial f z - timePartial g z := by
  show fderiv ℝ (fun s : ℝ => f (z.1, s) - g (z.1, s)) z.2 1 = _
  rw [fderiv_fun_sub hf hg]
  rfl

/-- The time slice of a jointly smooth scalar field is differentiable at every point of the
unit cylinder. -/
private theorem differentiableAt_timeSlice {g : ParabolicPoint → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => g z) unitCylinder) {z : Vec3 × ℝ}
    (hz : z ∈ unitCylinder) :
    DifferentiableAt ℝ (fun s : ℝ => g (z.1, s)) z.2 := by
  have hjoint : DifferentiableAt ℝ (fun w : Vec3 × ℝ => g w) z :=
    (hg.differentiableOn (by norm_num) z hz).differentiableAt (isOpen_unitCylinder_prod.mem_nhds hz)
  exact hjoint.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2).differentiableAt

/-- The classical spatial partial derivative of a squared scalar field, by the chain rule. -/
private theorem spatialPartial_sq {g : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hg : DifferentiableAt ℝ (fun y : Vec3 => g (y, z.2)) z.1) (i : Fin 3) :
    spatialPartial (fun w => (g w) ^ 2) i z = 2 * g z * spatialPartial g i z := by
  show fderiv ℝ (fun x : Vec3 => g (x, z.2) ^ 2) z.1 (basisVec i) = _
  rw [(hg.hasFDerivAt.pow 2).fderiv, smul_apply]
  show (2 • g z ^ (2 - 1)) • spatialPartial g i z = 2 * g z * spatialPartial g i z
  norm_num

/-- The azimuthal vorticity equation `eq:aniso:theta`: away from the axis, the material
derivative of the azimuthal vorticity of a classical, forced, axisymmetric solution equals its
stretching by the radial velocity, the source `∂_z(u_θ²)/r`, its cylindrical Laplacian, and the
azimuthal component of the curl of the force. -/
theorem azimuthal_vorticity_pde
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder)
    (z : ParabolicPoint) (hz : z ∈ unitCylinder) (hplane : z.1 1 = 0) (hr : z.1 0 ≠ 0) :
    timePartial (azimuthalVorticity u) z
        + u z 0 * spatialPartial (azimuthalVorticity u) 0 z
        + u z 2 * spatialPartial (azimuthalVorticity u) 2 z =
      u z 0 / z.1 0 * azimuthalVorticity u z
        + (1 / z.1 0) * spatialPartial (fun w => (u w 1) ^ 2) 2 z
        + (spatialSecondPartial (azimuthalVorticity u) 0 0 z
            + spatialPartial (azimuthalVorticity u) 0 z / z.1 0
            + spatialSecondPartial (azimuthalVorticity u) 2 2 z
            - azimuthalVorticity u z / (z.1 0) ^ 2)
        + (spatialPartial (fun w => f w 0) 2 z - spatialPartial (fun w => f w 2) 0 z) := by
  have huTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w) unitCylinder := hsol.1
  have hpTop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => p w) unitCylinder := hsol.2.1
  have hAtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 0) unitCylinder :=
    contDiffOn_component huTop 0
  have hCtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 2) unitCylinder :=
    contDiffOn_component huTop 2
  have hBtop : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => u w 1) unitCylinder :=
    contDiffOn_component huTop 1
  have hA2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 0) 2 w)
      unitCylinder := contDiffOn_spatialPartial hAtop 2
  have hC0 : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : Vec3 × ℝ => spatialPartial (fun v => u v 2) 0 w)
      unitCylinder := contDiffOn_spatialPartial hCtop 0
  have hA20 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 0) 2 0 w) unitCylinder :=
    contDiffOn_spatialPartial hA2 0
  have hC00 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 2) 0 0 w) unitCylinder :=
    contDiffOn_spatialPartial hC0 0
  have hA22 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 0) 2 2 w) unitCylinder :=
    contDiffOn_spatialPartial hA2 2
  have hC02 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : Vec3 × ℝ => spatialSecondPartial (fun v => u v 2) 0 2 w) unitCylinder :=
    contDiffOn_spatialPartial hC0 2
  have hΩfun : azimuthalVorticity u
      = fun w => spatialPartial (fun v => u v 0) 2 w - spatialPartial (fun v => u v 2) 0 w :=
    funext (curlComp_one u)
  have hΩt : timePartial (azimuthalVorticity u) z
      = timePartial (spatialPartial (fun v => u v 0) 2) z
        - timePartial (spatialPartial (fun v => u v 2) 0) z := by
    rw [hΩfun]
    exact timePartial_sub (differentiableAt_timeSlice hA2 hz) (differentiableAt_timeSlice hC0 hz)
  have hΩ0eqOn : ∀ w ∈ unitCylinder, spatialPartial (azimuthalVorticity u) 0 w
      = spatialSecondPartial (fun v => u v 0) 2 0 w
        - spatialSecondPartial (fun v => u v 2) 0 0 w := by
    intro w hw
    rw [hΩfun]
    exact spatialPartial_sub_of_differentiableAt (i := 0)
      (differentiableAt_spatialSlice (hA2.of_le (by norm_num)) hw)
      (differentiableAt_spatialSlice (hC0.of_le (by norm_num)) hw)
  have hΩ2eqOn : ∀ w ∈ unitCylinder, spatialPartial (azimuthalVorticity u) 2 w
      = spatialSecondPartial (fun v => u v 0) 2 2 w
        - spatialSecondPartial (fun v => u v 2) 0 2 w := by
    intro w hw
    rw [hΩfun]
    exact spatialPartial_sub_of_differentiableAt (i := 2)
      (differentiableAt_spatialSlice (hA2.of_le (by norm_num)) hw)
      (differentiableAt_spatialSlice (hC0.of_le (by norm_num)) hw)
  have hΩ0 := hΩ0eqOn z hz
  have hΩ2 := hΩ2eqOn z hz
  have hΩ00 : spatialSecondPartial (azimuthalVorticity u) 0 0 z
      = spatialPartial (spatialSecondPartial (fun v => u v 0) 2 0) 0 z
        - spatialPartial (spatialSecondPartial (fun v => u v 2) 0 0) 0 z := by
    show spatialPartial (spatialPartial (azimuthalVorticity u) 0) 0 z = _
    rw [spatialPartial_congr_of_eqOn hΩ0eqOn hz 0]
    exact spatialPartial_sub_of_differentiableAt (i := 0)
      (differentiableAt_spatialSlice (hA20.of_le (by norm_num)) hz)
      (differentiableAt_spatialSlice (hC00.of_le (by norm_num)) hz)
  have hΩ22 : spatialSecondPartial (azimuthalVorticity u) 2 2 z
      = spatialPartial (spatialSecondPartial (fun v => u v 0) 2 2) 2 z
        - spatialPartial (spatialSecondPartial (fun v => u v 2) 0 2) 2 z := by
    show spatialPartial (spatialPartial (azimuthalVorticity u) 2) 2 z = _
    rw [spatialPartial_congr_of_eqOn hΩ2eqOn hz 2]
    exact spatialPartial_sub_of_differentiableAt (i := 2)
      (differentiableAt_spatialSlice (hA22.of_le (by norm_num)) hz)
      (differentiableAt_spatialSlice (hC02.of_le (by norm_num)) hz)
  have hΩ : azimuthalVorticity u z
      = spatialPartial (fun v => u v 0) 2 z - spatialPartial (fun v => u v 2) 0 z :=
    curlComp_one u z
  have hE1 := raw_theta_axial u p f hsol haxi z hz hplane hr
  have hE2 := raw_theta_radial u p f hsol haxi z hz hplane hr
  have hAcomm02 := spatialSecondPartial_comm (g := fun w => u w 0) hAtop hz 0 2
  have hCcomm02 := spatialSecondPartial_comm (g := fun w => u w 2) hCtop hz 2 0
  rw [hAcomm02] at hE1
  rw [hCcomm02] at hE2
  have hT3a := T3_reorder_002_200 (g := fun w => u w 0) hAtop hz
  have hT3b := T3_reorder_220_022 (g := fun w => u w 2) hCtop hz
  have hpcomm := spatialSecondPartial_comm hpTop hz 0 2
  have hu1 : ContDiffOn ℝ 1 (fun w : Vec3 × ℝ => u w) unitCylinder := huTop.of_le (by norm_num)
  have hdivcyl : spatialPartial (fun w => u w 0) 0 z + u z 0 / z.1 0
      + spatialPartial (fun w => u w 2) 2 z = 0 := by
    rw [← sum_spatialPartial_meridional haxi hu1 hz hplane hr]
    exact hsol.2.2.2.2 z hz
  have hBsq := spatialPartial_sq (g := fun w => u w 1)
    (differentiableAt_spatialSlice (hBtop.of_le (by norm_num)) hz) 2
  rw [hΩt, hΩ0, hΩ2, hΩ00, hΩ22, hΩ]
  linear_combination (norm := (field_simp; ring)) hE1 - hE2 + hT3a - hT3b - hpcomm
    - (spatialPartial (fun v => u v 0) 2 z - spatialPartial (fun v => u v 2) 0 z) * hdivcyl
    - (1 / z.1 0) * hBsq


end CIV
