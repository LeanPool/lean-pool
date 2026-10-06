/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessGaugeCubeData
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.EnergyPrice.WitnessZeroTraceAtCube
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineCoeffFamily
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ObservationCoefficientTransport

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Dirichlet.FrozenWitnessCubeSolutionData

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# the analytic inputs, parts (b) and (d): the observation family and the cube solution listed as
"absent" both the coefficient identification
`∀ y, aHat (y + c) = (aFam.coeffOn (originCube d j)).toCoeffField y` and the
exhibition of the gauge solution as a `DirichletForcedCubeSolution` on the
origin cube.  Both are closed here.

* **(d), the coefficient family.**  `exists_affineCoeffFamily`
  (`HCPoly.Provider.PolynomialHomogenization.AffineCoeffFamily`)
  produces a Chapter 3 family whose representative is, **on every cube and
  literally**, a prescribed affine pullback.  Applied not to
  `fun w ↦ scaledCoeff ε a w - skewPart abar` (as
  the skew-centered scaled affine family does) but to its **translate by
  the gauge centre** `fun w ↦ scaledCoeff ε a (w + z) - skewPart abar`, it
  gives a family for which the required identification is a *pointwise*
  equality, discharged by the single gauge identity
  `matVecMul S (y + S⁻¹ z) = matVecMul S y + z`.  The a.e. identification that
  the module consumes as `hObsEps` falls out of the same pointwise equality,
  so **one family serves both binders** — which is exactly what that module needs,
  since `hb` and `hObs` there speak about the same `aFam`.

* **(b), the cube solution.**  `IsWeakSolutionOn.untranslate`
  (`HCPoly.Provider.Regularity.ObservationCoefficientTransport`) moves the gauge weak solution
  (row 4′, module that module) from `matImage S⁻¹ U = translateSet c (openCubeSet Q)`
  onto the cube; the pointwise `hb` rewrites its coefficient into
  `(aFam.coeffOn Q).toCoeffField`; the upstream *private*
  `isForcedEquation_zero_of_isWeakSolutionOn'` is re-proved in-module; and E15's
  `witnessDirichletForcedCubeSolution` packages the result.  The construction
  keeps `v.toH1 = uObs` and `dirichletBoundaryGradientField v = gObs.grad`
  definitionally, so the `hu` premise and `hF` are identities read backwards.

  The **one remaining hypothesis** is the zero-trace datum `hzero`; it is a
  binder here, and it is the last of the analytic inputs.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory Book Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## The gauge cancellation -/

/-- An invertible gauge composed with its inverse is the identity on vectors. -/
theorem matVecMul_matVecMul_nonsing_inv {L : Mat d} (hL : IsUnit L.det)
    (w : Vec d) : matVecMul L (matVecMul L⁻¹ w) = w := by
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]

/-! ## (d) The translated observation family -/

/-- The skew-centred rescaled coefficient, **translated by the gauge centre**,
is a Chapter 3 coefficient family with its displayed representative on every
cube. -/
theorem exists_translatedSkewCenteredScaledAffineCoeffFamily
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (a : CoeffSpace d) {abar : Mat d}
    (hS : (symmPart abar).PosDef) (z : Vec d) :
    ∃ aFam : Book.Ch03.CoeffFamily d,
      ∀ Q : TriadicCube d,
        (aFam.coeffOn Q).toCoeffField =
          affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
            (fun w => scaledCoeff epsilon a (w + z) - skewPart abar) := by
  have hqmp :=
    (measurePreserving_add_right (volume : Measure (Vec d)) z).quasiMeasurePreserving
  have hskew : IsSkewMat (skewPart abar) := matTranspose_skewPart abar
  have hcenterEll : IsAELocallyUniformlyElliptic
      (fun x => scaledCoeff epsilon a (x + z) - skewPart abar) := by
    intro R hR
    obtain ⟨lam, Lam, hlam, hle, hEll⟩ :=
      (isAELocallyUniformlyElliptic_scaledCoeff hepsilon a).comp_add_right z R hR
    refine ⟨lam, Response.skewShiftUpper lam Lam (skewPart abar), hlam,
      Response.le_skewShiftUpper hlam hle (skewPart abar), ?_⟩
    filter_upwards [hEll] with x hx hxb
    exact Response.isEllipticMatrix_sub_skew (hx hxb) hskew
  have hcenterMeas : AEStronglyMeasurable
      (fun x => scaledCoeff epsilon a (x + z) - skewPart abar) volume :=
    ((aestronglyMeasurable_scaledCoeff hepsilon a).comp_quasiMeasurePreserving
      hqmp).sub aestronglyMeasurable_const
  exact exists_affineCoeffFamily (matSqrt (symmPart abar))
    (isUnit_det_matSqrt hS) hcenterMeas hcenterEll

/-- **the analytic inputs (d), closed.**  One Chapter 3 family serves both of coefficient binders
at the frozen witness: the *pointwise* `hb` and the
a.e. observation identification `hObs`, at `scaledCoeff ε a`. -/
theorem exists_frozenWitnessCoeffFamilyAtCube
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (a : CoeffSpace d) {abar : Mat d}
    (hS : (symmPart abar).PosDef) (z : Vec d) (j : ℤ) :
    ∃ aFam : Book.Ch03.CoeffFamily d,
      (∀ y : Vec d,
        affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
            (fun w => scaledCoeff epsilon a w - skewPart abar)
            (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
          (aFam.coeffOn (originCube d j)).toCoeffField y) ∧
      ((aFam.coeffOn (originCube d j)).toCoeffField
        =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
        fun y ↦ affineCoefficient (matSqrt (symmPart abar))
          (isUnit_det_matSqrt hS)
          (fun w ↦ scaledCoeff epsilon a w - skewPart abar)
          (y + matVecMul (matSqrt (symmPart abar))⁻¹ z)) := by
  obtain ⟨aFam, hfam⟩ :=
    exists_translatedSkewCenteredScaledAffineCoeffFamily hepsilon a hS z
  have hshift : ∀ y : Vec d,
      matVecMul (matSqrt (symmPart abar))
          (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
        matVecMul (matSqrt (symmPart abar)) y + z := by
    intro y
    rw [matVecMul_add,
      matVecMul_matVecMul_nonsing_inv (isUnit_det_matSqrt hS)]
  have hb : ∀ y : Vec d,
      affineCoefficient (matSqrt (symmPart abar)) (isUnit_det_matSqrt hS)
          (fun w => scaledCoeff epsilon a w - skewPart abar)
          (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
        (aFam.coeffOn (originCube d j)).toCoeffField y := by
    intro y
    rw [hfam (originCube d j)]
    simp only [affineCoefficient_apply, hshift y]
  exact ⟨aFam, hb, _root_.Filter.Eventually.of_forall fun y => (hb y).symm⟩

/-! ## (b) The forced equation and the cube solution -/

/-- The upstream *private* conversion of a cube weak solution into a forced
equation, re-proved in-module so it can be used at the frozen witness. -/
theorem isForcedEquation_zero_of_isWeakSolutionOn
    {Q : TriadicCube d} {aFam : Book.Ch03.CoeffFamily d}
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (aFam.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad) :
    IsForcedEquation Q aFam u (0 : Vec d → Vec d) := by
  have hEll : IsAEEllipticFieldOn (aFam.coeffOn Q).lam (aFam.coeffOn Q).Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d)) (aFam.coeffOn Q).toCoeffField :=
    ⟨(Book.Ch02.cubeDomain Q).measurableSet,
      (aFam.coeffOn Q).aeStronglyMeasurable, (aFam.coeffOn Q).aeElliptic⟩
  have hflux : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((aFam.coeffOn Q).toCoeffField x) (u.grad x)) :=
    hEll.memVectorL2_matVecMul u.grad_memVectorL2
  have hsol : IsSolenoidalOn (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((aFam.coeffOn Q).toCoeffField x) (u.grad x)) := by
    refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hflux
      (Book.Ch02.cubeDomain Q).isOpen ?_
    intro psi hpsi hsupp hsub
    have hzero := (hu psi ⟨hpsi, hsupp, hsub⟩).2
    have hfun :
        (fun x => vecDot
          (matVecMul ((aFam.coeffOn Q).toCoeffField x) (u.grad x))
          (fun i => (fderiv ℝ psi x) (basisVec i))) =
        fun x => vecDot (smoothGrad psi x)
          (matVecMul ((aFam.coeffOn Q).toCoeffField x) (u.grad x)) := by
      funext x
      rw [vecDot_comm]
      rfl
    rw [hfun]
    exact hzero
  have hweak : IsH1DirichletRhsWeakSolutionOn
      (aFam.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u (0 : Vec d → Vec d) :=
    IsH1DirichletRhsWeakSolutionOn.of_residual_solenoidal
      hflux MeasureTheory.MemLp.zero
      (by simpa only [Pi.zero_apply, sub_zero] using hsol)
  simpa only [IsForcedEquation] using! hweak

/-- **the analytic inputs (b), closed modulo the zero-trace datum.**  The gauge solution of
the frozen witness *is* a Dirichlet forced cube solution on the origin cube of
the witness generation, with the prescribed boundary datum. -/
theorem exists_frozenWitnessDirichletCubeSolution [NeZero d]
    {abar : Mat d} (hS : (symmPart abar).PosDef)
    {U : Set (Vec d)} {j : ℤ} {z : Vec d}
    (hU : U = (fun y : Vec d => z + matVecMul (matSqrt (symmPart abar)) y) ''
      openCubeSet (originCube d j))
    {aHat : CoeffField d} {aFam : Book.Ch03.CoeffFamily d}
    (hb : ∀ y : Vec d, aHat (y + matVecMul (matSqrt (symmPart abar))⁻¹ z) =
      (aFam.coeffOn (originCube d j)).toCoeffField y)
    (F : Vec d → Vec d)
    (hWeak : IsWeakSolutionOn aHat (matImage (matSqrt (symmPart abar))⁻¹ U) F)
    (uObs gObs : H1Function (openCubeSet (originCube d j)))
    (huObs : ∀ y : Vec d, uObs.grad y =
      F (y + matVecMul (matSqrt (symmPart abar))⁻¹ z))
    (hzero : ∃ w : H10Function (openCubeSet (originCube d j)),
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet (originCube d j))]
        fun x => uObs.toFun x - gObs.toFun x) :
    ∃ v : Book.Ch03.DirichletForcedCubeSolution (originCube d j) aFam
        (0 : Vec d → Vec d),
      v.toH1 = uObs ∧
      Book.Ch03.dirichletBoundaryGradientField v = gObs.grad := by
  have hgauge := matImage_matSqrtInv_witness_eq_translateSet hS hU
  rw [hgauge] at hWeak
  have huntr := hWeak.untranslate (matVecMul (matSqrt (symmPart abar))⁻¹ z)
  have hcoeff : translateCoeffField (matVecMul (matSqrt (symmPart abar))⁻¹ z)
      aHat = (aFam.coeffOn (originCube d j)).toCoeffField := funext hb
  have hgradfun : (fun x : Vec d =>
      F (x + matVecMul (matSqrt (symmPart abar))⁻¹ z)) = uObs.grad :=
    funext fun y => (huObs y).symm
  rw [hcoeff, hgradfun] at huntr
  exact ⟨EnergyPrice.witnessDirichletForcedCubeSolution uObs gObs
    (isForcedEquation_zero_of_isWeakSolutionOn uObs huntr) hzero, rfl, rfl⟩

end

end RowSupply
end HighContrast
end HCPolySupport
