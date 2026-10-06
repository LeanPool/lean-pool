/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.SymmetricDirichletNeumann.Dirichlet
public import LeanPool.HighContrastHomogenization.Provider.Regularity.GoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ResponseExponentGap
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.DeterministicCore
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.EnergyRHS.Theory

/-!
# High-contrast homogenization: Provider.Regularity.FiniteCorrector

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine-boundary solutions on Euclidean cubes

This module constructs the homogeneous solution with affine boundary values on
a centered triadic cube.  The construction retains the zero-trace correction
returned by the Dirichlet solver, so both the function-level boundary condition
and its gradient consequence are available to deterministic comparison
estimates.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

@[expose]
public noncomputable def finiteAffinePointwiseCoeff {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) :
    Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)) :=
  Internal.Ch02.BookCh02.pointwiseCoeffOn
    (Book.Ch02.cubeDomain (originCube d m)) (a.coeffOn (originCube d m))

private theorem finiteAffinePointwiseCoeff_isElliptic {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) :
    IsEllipticFieldOn (finiteAffinePointwiseCoeff a m).lam
      (finiteAffinePointwiseCoeff a m).Lam
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (finiteAffinePointwiseCoeff a m).toCoeffField := by
  simpa only [finiteAffinePointwiseCoeff] using
    Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
      (Book.Ch02.cubeDomain (originCube d m)) (a.coeffOn (originCube d m))

private theorem finiteAffinePointwiseCoeff_ae_eq {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) :
    (finiteAffinePointwiseCoeff a m).toCoeffField
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      (a.coeffOn (originCube d m)).toCoeffField := by
  simpa only [finiteAffinePointwiseCoeff] using!
    Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq
      (Book.Ch02.cubeDomain (originCube d m)) (a.coeffOn (originCube d m))

/-- The affine boundary datum `x ↦ e · x` on a centered triadic cube. -/
@[expose]
noncomputable def finiteAffineBoundaryH1 {d : ℕ} [NeZero d]
    (m : ℤ) (e : Vec d) :
    H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) :=
  H1Function.affineOnIsSobolevRegularDomain
    (Book.Ch02.cubeDomain (originCube d m)).isDomain.isSobolevRegularDomain e

/-- The affine boundary datum has the prescribed constant gradient. -/
@[simp] theorem finiteAffineBoundaryH1_grad {d : ℕ} [NeZero d]
    (m : ℤ) (e : Vec d) :
    (finiteAffineBoundaryH1 m e).grad = fun _ => e := by
  funext x
  exact H1Function.affineOnIsSobolevRegularDomain_grad
    (Book.Ch02.cubeDomain (originCube d m)).isDomain.isSobolevRegularDomain e x

/-- The affine boundary datum is the Euclidean linear function `x ↦ e · x`. -/
@[simp] theorem finiteAffineBoundaryH1_toFun {d : ℕ} [NeZero d]
    (m : ℤ) (e : Vec d) :
    (finiteAffineBoundaryH1 m e).toFun = fun x => vecDot e x := by
  funext x
  simpa only [finiteAffineBoundaryH1] using!
    H1Function.affineOnIsSobolevRegularDomain_apply
      (Book.Ch02.cubeDomain (originCube d m)).isDomain.isSobolevRegularDomain e x

@[expose]
public noncomputable def finiteAffineForcing {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    Vec d → Vec d :=
  fun x => -matVecMul ((finiteAffinePointwiseCoeff a m).toCoeffField x) e

private theorem isZeroTraceDirichletRhsWeakSolution_add {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {u v : H10Function U}
    {g h : Vec d → Vec d} {lam Lam : ℝ}
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g)
    (hv : IsZeroTraceDirichletRhsWeakSolution a U v h)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hg : MemVectorL2 U g) (hh : MemVectorL2 U h) :
    IsZeroTraceDirichletRhsWeakSolution a U (u + v) (fun x => g x + h x) := by
  intro phi
  have huFlux :
      MemVectorL2 U (fun x => matVecMul (a x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      u.toH1Function.grad_memVectorL2
  have hvFlux :
      MemVectorL2 U (fun x => matVecMul (a x) (v.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      v.toH1Function.grad_memVectorL2
  have huInt :
      IntegrableOn
        (fun x => vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (phi.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 huFlux
      phi.toH1Function.grad_memVectorL2
  have hvInt :
      IntegrableOn
        (fun x => vecDot (matVecMul (a x) (v.toH1Function.grad x))
          (phi.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hvFlux
      phi.toH1Function.grad_memVectorL2
  have hgInt :
      IntegrableOn (fun x => vecDot (g x) (phi.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg phi.toH1Function.grad_memVectorL2
  have hhInt :
      IntegrableOn (fun x => vecDot (h x) (phi.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hh phi.toH1Function.grad_memVectorL2
  change
    (∫ x in U,
      vecDot (matVecMul (a x) ((u.toH1Function + v.toH1Function).grad x))
        (phi.toH1Function.grad x) ∂volume) =
      ∫ x in U, vecDot (g x + h x) (phi.toH1Function.grad x) ∂volume
  simp only [H1Function.add_grad, matVecMul_add, vecDot_add_left]
  rw [integral_add huInt hvInt, integral_add hgInt hhInt, hu phi, hv phi]

private theorem isZeroTraceDirichletRhsWeakSolution_smul {d : ℕ}
    {a : CoeffField d} {U : Set (Vec d)} {u : H10Function U}
    {g : Vec d → Vec d} (c : ℝ)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    IsZeroTraceDirichletRhsWeakSolution a U (c • u) (fun x => c • g x) := by
  intro phi
  change
    (∫ x in U,
      vecDot (matVecMul (a x) ((c • u.toH1Function).grad x))
        (phi.toH1Function.grad x) ∂volume) =
      ∫ x in U, vecDot (c • g x) (phi.toH1Function.grad x) ∂volume
  simpa only [H1Function.smul_grad, Pi.smul_apply, matVecMul_smul,
    vecDot_smul_left, integral_const_mul] using
    congrArg (fun z : ℝ => c * z) (hu phi)

/-- The zero-trace correction in the finite affine Dirichlet problem. -/
@[expose]
noncomputable def finiteAffineCorrection {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    H10Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) :=
  zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
    (a := (finiteAffinePointwiseCoeff a m).toCoeffField)
    (g := finiteAffineForcing a m e)
    (Internal.Ch02.BookCh02.memVectorL2_neg_matVecMul_const
      (finiteAffinePointwiseCoeff_isElliptic a m) e)
    (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
        (Book.Ch02.cubeDomain (originCube d m)).isDomain)
    (Book.Ch02.cubeDomain (originCube d m)).nonempty
    (finiteAffinePointwiseCoeff_isElliptic a m)

/-- The correction satisfies the zero-trace Dirichlet equation driven by the
negative flux of the affine gradient. -/
private theorem finiteAffineCorrection_weakSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    IsZeroTraceDirichletRhsWeakSolution
      (finiteAffinePointwiseCoeff a m).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (finiteAffineCorrection a m e) (finiteAffineForcing a m e) := by
  unfold finiteAffineCorrection
  exact
    isZeroTraceDirichletRhsWeakSolution_zeroTraceDirichletRhsProblemSolution_of_potentialZeroTraceClosureRealization
      (Internal.Ch02.BookCh02.memVectorL2_neg_matVecMul_const
        (finiteAffinePointwiseCoeff_isElliptic a m) e)
      (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
          (Book.Ch02.cubeDomain (originCube d m)).isDomain)
      (Book.Ch02.cubeDomain (originCube d m)).nonempty
      (finiteAffinePointwiseCoeff_isElliptic a m)

private theorem finiteAffineCorrection_grad_ae_eq_of_weakSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d)
    (v : H10Function
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hv : IsZeroTraceDirichletRhsWeakSolution
      (finiteAffinePointwiseCoeff a m).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) v
      (finiteAffineForcing a m e)) :
    (finiteAffineCorrection a m e).toH1Function.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      v.toH1Function.grad := by
  have hgradL2 :=
    IsZeroTraceDirichletRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (Book.Ch02.cubeDomain (originCube d m)).nonempty
      (finiteAffineCorrection_weakSolution a m e) hv
      (finiteAffinePointwiseCoeff_isElliptic a m)
  filter_upwards
      [H1Function.coeFn_gradToVectorL2
        (finiteAffineCorrection a m e).toH1Function,
        H1Function.coeFn_gradToVectorL2 v.toH1Function]
    with x hx hvx
  rw [← hx, ← hvx, hgradL2]

private theorem finiteAffineCorrection_add_weakSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    IsZeroTraceDirichletRhsWeakSolution
      (finiteAffinePointwiseCoeff a m).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (finiteAffineCorrection a m e + finiteAffineCorrection a m e')
      (finiteAffineForcing a m (e + e')) := by
  have hforcing :
      (fun x => finiteAffineForcing a m e x + finiteAffineForcing a m e' x) =
        finiteAffineForcing a m (e + e') := by
    funext x
    simp only [finiteAffineForcing, matVecMul_add]
    abel
  rw [← hforcing]
  exact isZeroTraceDirichletRhsWeakSolution_add
    (finiteAffineCorrection_weakSolution a m e)
    (finiteAffineCorrection_weakSolution a m e')
    (finiteAffinePointwiseCoeff_isElliptic a m)
    (Internal.Ch02.BookCh02.memVectorL2_neg_matVecMul_const
      (finiteAffinePointwiseCoeff_isElliptic a m) e)
    (Internal.Ch02.BookCh02.memVectorL2_neg_matVecMul_const
      (finiteAffinePointwiseCoeff_isElliptic a m) e')

private theorem finiteAffineCorrection_smul_weakSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    IsZeroTraceDirichletRhsWeakSolution
      (finiteAffinePointwiseCoeff a m).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (c • finiteAffineCorrection a m e) (finiteAffineForcing a m (c • e)) := by
  have hforcing :
      (fun x => c • finiteAffineForcing a m e x) =
        finiteAffineForcing a m (c • e) := by
    funext x
    simp only [finiteAffineForcing, matVecMul_smul, smul_neg]
  rw [← hforcing]
  exact isZeroTraceDirichletRhsWeakSolution_smul c
    (finiteAffineCorrection_weakSolution a m e)

private theorem finiteAffineCorrection_grad_add {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    (finiteAffineCorrection a m (e + e')).toH1Function.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => (finiteAffineCorrection a m e).toH1Function.grad x +
        (finiteAffineCorrection a m e').toH1Function.grad x := by
  simpa only [H1Function.add_grad] using!
    finiteAffineCorrection_grad_ae_eq_of_weakSolution a m (e + e')
      (finiteAffineCorrection a m e + finiteAffineCorrection a m e')
      (finiteAffineCorrection_add_weakSolution a m e e')

private theorem finiteAffineCorrection_grad_smul {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    (finiteAffineCorrection a m (c • e)).toH1Function.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => c • (finiteAffineCorrection a m e).toH1Function.grad x := by
  simpa only [H1Function.smul_grad] using!
    finiteAffineCorrection_grad_ae_eq_of_weakSolution a m (c • e)
      (c • finiteAffineCorrection a m e)
      (finiteAffineCorrection_smul_weakSolution a m c e)

private theorem finiteAffineCorrection_toFun_add {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    (finiteAffineCorrection a m (e + e')).toH1Function.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => (finiteAffineCorrection a m e).toH1Function.toFun x +
        (finiteAffineCorrection a m e').toH1Function.toFun x := by
  have hL2 :=
    IsZeroTraceDirichletRhsWeakSolution.toScalarL2_eq_of_isOpenBoundedConvexDomain
      (Book.Ch02.cubeDomain (originCube d m)).isDomain
      (Book.Ch02.cubeDomain (originCube d m)).nonempty
      (finiteAffineCorrection_weakSolution a m (e + e'))
      (finiteAffineCorrection_add_weakSolution a m e e')
      (finiteAffinePointwiseCoeff_isElliptic a m)
  have hfun :
      (finiteAffineCorrection a m (e + e')).toH1Function.toFun
        =ᵐ[volumeMeasureOn
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
        (finiteAffineCorrection a m e +
          finiteAffineCorrection a m e').toH1Function.toFun := by
    apply (HCPolySupport.toScalarL2_eq_toScalarL2_iff
      (finiteAffineCorrection a m (e + e')).toH1Function.memL2
      (finiteAffineCorrection a m e +
        finiteAffineCorrection a m e').toH1Function.memL2).mp
    exact hL2
  simpa only [H1Function.add_toFun] using! hfun

private theorem finiteAffineCorrection_toFun_smul {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    (finiteAffineCorrection a m (c • e)).toH1Function.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => c * (finiteAffineCorrection a m e).toH1Function.toFun x := by
  have hL2 :=
    IsZeroTraceDirichletRhsWeakSolution.toScalarL2_eq_of_isOpenBoundedConvexDomain
      (Book.Ch02.cubeDomain (originCube d m)).isDomain
      (Book.Ch02.cubeDomain (originCube d m)).nonempty
      (finiteAffineCorrection_weakSolution a m (c • e))
      (finiteAffineCorrection_smul_weakSolution a m c e)
      (finiteAffinePointwiseCoeff_isElliptic a m)
  have hfun :
      (finiteAffineCorrection a m (c • e)).toH1Function.toFun
        =ᵐ[volumeMeasureOn
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
        (c • finiteAffineCorrection a m e).toH1Function.toFun := by
    apply (HCPolySupport.toScalarL2_eq_toScalarL2_iff
      (finiteAffineCorrection a m (c • e)).toH1Function.memL2
      (c • finiteAffineCorrection a m e).toH1Function.memL2).mp
    exact hL2
  simpa only [H1Function.smul_toFun] using! hfun

@[expose]
public noncomputable def finiteAffineH1 {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    H1Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) :=
  finiteAffineBoundaryH1 m e + (finiteAffineCorrection a m e).toH1Function

private theorem finiteAffineH1_isHarmonic_pointwise {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    IsAHarmonicGradient (finiteAffinePointwiseCoeff a m).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (finiteAffineH1 a m e).grad := by
  let U : Set (Vec d) :=
    (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
  let b := finiteAffinePointwiseCoeff a m
  let phi := finiteAffineCorrection a m e
  let u := finiteAffineH1 a m e
  have hEll : IsEllipticFieldOn b.lam b.Lam U b.toCoeffField := by
    simpa only [U, b] using finiteAffinePointwiseCoeff_isElliptic a m
  have hphi :
      IsZeroTraceDirichletRhsWeakSolution b.toCoeffField U phi
        (finiteAffineForcing a m e) := by
    simpa only [U, b, phi] using finiteAffineCorrection_weakSolution a m e
  constructor
  · exact u.isPotentialOn
  · intro psi
    have heMem : MemVectorL2 U (fun x => matVecMul (b.toCoeffField x) e) := by
      have he : MemVectorL2 U (fun _ : Vec d => e) :=
        Internal.Ch02.BookCh02.memVectorL2_const_vec e
      exact memVectorL2_matVecMul_of_isEllipticFieldOn hEll he
    have hphiFluxMem :
        MemVectorL2 U
          (fun x => matVecMul (b.toCoeffField x) (phi.toH1Function.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll
        phi.toH1Function.grad_memVectorL2
    have heInt :
        IntegrableOn
          (fun x => vecDot (matVecMul (b.toCoeffField x) e)
            (psi.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 heMem psi.toH1Function.grad_memVectorL2
    have hphiInt :
        IntegrableOn
          (fun x => vecDot
            (matVecMul (b.toCoeffField x) (phi.toH1Function.grad x))
            (psi.toH1Function.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hphiFluxMem
        psi.toH1Function.grad_memVectorL2
    have hsplit :
        (fun x => vecDot (matVecMul (b.toCoeffField x) (u.grad x))
          (psi.toH1Function.grad x)) =
        fun x =>
          vecDot (matVecMul (b.toCoeffField x) e) (psi.toH1Function.grad x) +
            vecDot (matVecMul (b.toCoeffField x) (phi.toH1Function.grad x))
              (psi.toH1Function.grad x) := by
      funext x
      simp only [u, finiteAffineH1, phi, H1Function.add_grad,
        finiteAffineBoundaryH1_grad, matVecMul_add, vecDot_add_left]
    calc
      ∫ x in U, vecDot (matVecMul (b.toCoeffField x) (u.grad x))
          (psi.toH1Function.grad x) ∂volume =
          ∫ x in U,
            (vecDot (matVecMul (b.toCoeffField x) e) (psi.toH1Function.grad x) +
              vecDot (matVecMul (b.toCoeffField x) (phi.toH1Function.grad x))
                (psi.toH1Function.grad x)) ∂volume := by
        rw [hsplit]
      _ =
          (∫ x in U, vecDot (matVecMul (b.toCoeffField x) e)
            (psi.toH1Function.grad x) ∂volume) +
          ∫ x in U, vecDot
            (matVecMul (b.toCoeffField x) (phi.toH1Function.grad x))
            (psi.toH1Function.grad x) ∂volume := by
        rw [integral_add heInt hphiInt]
      _ =
          (∫ x in U, vecDot (matVecMul (b.toCoeffField x) e)
            (psi.toH1Function.grad x) ∂volume) +
          ∫ x in U, vecDot (finiteAffineForcing a m e x)
            (psi.toH1Function.grad x) ∂volume := by
        rw [hphi psi]
      _ = 0 := by
        have hneg :
            (fun x => vecDot (finiteAffineForcing a m e x)
              (psi.toH1Function.grad x)) =
            fun x => -vecDot (matVecMul (b.toCoeffField x) e)
              (psi.toH1Function.grad x) := by
          funext x
          simp only [finiteAffineForcing, b, vecDot_neg_left]
        rw [hneg, integral_neg]
        ring

private theorem finiteAffineH1_isHarmonic {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    IsAHarmonicGradient (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
      (finiteAffineH1 a m e).grad :=
  IsAHarmonicGradient.of_ae_eq_coeff (finiteAffinePointwiseCoeff_ae_eq a m)
    (finiteAffineH1_isHarmonic_pointwise a m e)

/-- The affine-boundary homogeneous solution on the centered triadic cube. -/
@[expose]
noncomputable def finiteAffineSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    Book.Ch03.DirichletForcedCubeSolution (originCube d m) a
      (0 : Vec d → Vec d) where
  toH1 := finiteAffineH1 a m e
  boundaryData := finiteAffineBoundaryH1 m e
  weakSolution := by
    intro psi
    have hzero := (finiteAffineH1_isHarmonic a m e).2 psi
    simpa only [Pi.zero_apply, vecDot_zero_left, integral_zero] using hzero
  zeroTraceDifference := by
    refine ⟨finiteAffineCorrection a m e, Filter.Eventually.of_forall ?_⟩
    intro x
    simp only [finiteAffineH1, H1Function.add_toFun, add_sub_cancel_left]

/-- The selected solution retains its affine datum and zero-trace correction
definitionally. -/
theorem finiteAffineSolution_toH1 {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    (finiteAffineSolution a m e).toH1 =
      finiteAffineBoundaryH1 m e + (finiteAffineCorrection a m e).toH1Function :=
  rfl

/-- The function-level affine boundary condition used by comparison theorems. -/
theorem finiteAffineSolution_zeroTraceDifference {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    ∃ w : H10Function
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)),
      w.toH1Function.toFun
        =ᵐ[volumeMeasureOn
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
        fun x => (finiteAffineSolution a m e).toH1.toFun x -
          (finiteAffineBoundaryH1 m e).toFun x :=
  (finiteAffineSolution a m e).zeroTraceDifference

/-- The affine-boundary solution as the homogeneous cube-solution carrier. -/
@[expose]
noncomputable def finiteAffineCubeSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    Book.Ch03.CubeSolution (originCube d m) a where
  toH1 := (finiteAffineSolution a m e).toH1
  isHarmonic := finiteAffineH1_isHarmonic a m e

/-- The selected cube solution is harmonic with affine boundary slope `e`. -/
theorem finiteAffineSolution_isAffineDirichletSolution {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    IsAffineDirichletSolution
      (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) e
      (finiteAffineSolution a m e).toH1 := by
  constructor
  · exact (finiteAffineCubeSolution a m e).isHarmonic
  · have hgrad :
        (fun x => (finiteAffineSolution a m e).toH1.grad x - e) =
          (finiteAffineCorrection a m e).toH1Function.grad := by
      funext x
      simp only [finiteAffineSolution_toH1, H1Function.add_grad,
        finiteAffineBoundaryH1_grad, add_sub_cancel_left]
    rw [hgrad]
    exact (finiteAffineCorrection a m e).isPotentialZeroTraceOn

private theorem exists_finiteAffineCorrection_weakSolution_of_isAffineDirichletSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
    (e : Vec d)
    (u : H1Function
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsAffineDirichletSolution
      (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) e u) :
    ∃ v : H10Function
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)),
      v.toH1Function.grad = (fun x => u.grad x - e) ∧
        IsZeroTraceDirichletRhsWeakSolution
          (finiteAffinePointwiseCoeff a m).toCoeffField
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) v
          (finiteAffineForcing a m e) := by
  let U : Set (Vec d) :=
    (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
  let b := finiteAffinePointwiseCoeff a m
  have hEll : IsEllipticFieldOn b.lam b.Lam U b.toCoeffField := by
    simpa only [U, b] using finiteAffinePointwiseCoeff_isElliptic a m
  have huPointwise : IsAHarmonicGradient b.toCoeffField U u.grad := by
    exact IsAHarmonicGradient.of_ae_eq_coeff
      (finiteAffinePointwiseCoeff_ae_eq a m).symm hu.1
  rcases hu.2 with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  intro psi
  have huFlux :
      MemVectorL2 U (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have heFlux :
      MemVectorL2 U (fun x => matVecMul (b.toCoeffField x) e) := by
    exact memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      (Internal.Ch02.BookCh02.memVectorL2_const_vec e)
  have huInt :
      IntegrableOn
        (fun x => vecDot (matVecMul (b.toCoeffField x) (u.grad x))
          (psi.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 huFlux
      psi.toH1Function.grad_memVectorL2
  have heInt :
      IntegrableOn
        (fun x => vecDot (matVecMul (b.toCoeffField x) e)
          (psi.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 heFlux
      psi.toH1Function.grad_memVectorL2
  have hsplit :
      (fun x => vecDot
        (matVecMul (b.toCoeffField x) (v.toH1Function.grad x))
        (psi.toH1Function.grad x)) =
      fun x =>
        vecDot (matVecMul (b.toCoeffField x) (u.grad x))
            (psi.toH1Function.grad x) -
          vecDot (matVecMul (b.toCoeffField x) e)
            (psi.toH1Function.grad x) := by
    funext x
    rw [congrFun hv x]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg,
      vecDot_add_left, vecDot_neg_left]
  have hforcing :
      (fun x => vecDot (finiteAffineForcing a m e x)
        (psi.toH1Function.grad x)) =
      fun x => -vecDot (matVecMul (b.toCoeffField x) e)
        (psi.toH1Function.grad x) := by
    funext x
    simp only [finiteAffineForcing, b, vecDot_neg_left]
  calc
    ∫ x in U,
        vecDot (matVecMul (b.toCoeffField x) (v.toH1Function.grad x))
          (psi.toH1Function.grad x) ∂volume =
        ∫ x in U,
          (vecDot (matVecMul (b.toCoeffField x) (u.grad x))
              (psi.toH1Function.grad x) -
            vecDot (matVecMul (b.toCoeffField x) e)
              (psi.toH1Function.grad x)) ∂volume := by
      rw [hsplit]
    _ =
        (∫ x in U, vecDot (matVecMul (b.toCoeffField x) (u.grad x))
          (psi.toH1Function.grad x) ∂volume) -
        ∫ x in U, vecDot (matVecMul (b.toCoeffField x) e)
          (psi.toH1Function.grad x) ∂volume := by
      rw [integral_sub huInt heInt]
    _ = -∫ x in U, vecDot (matVecMul (b.toCoeffField x) e)
          (psi.toH1Function.grad x) ∂volume := by
      rw [huPointwise.2 psi, zero_sub]
    _ = ∫ x in U, vecDot (finiteAffineForcing a m e x)
          (psi.toH1Function.grad x) ∂volume := by
      rw [hforcing, integral_neg]

/-- Any affine Dirichlet solution with the same slope has the selected weak
gradient almost everywhere. -/
theorem finiteAffineSolution_grad_ae_eq_of_isAffineDirichletSolution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
    (e : Vec d)
    (u : H1Function
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
    (hu : IsAffineDirichletSolution
      (a.coeffOn (originCube d m)).toCoeffField
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) e u) :
    (finiteAffineSolution a m e).toH1.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      u.grad := by
  rcases
      exists_finiteAffineCorrection_weakSolution_of_isAffineDirichletSolution
        a m e u hu with
    ⟨v, hv, hvWeak⟩
  have hcorrection :=
    finiteAffineCorrection_grad_ae_eq_of_weakSolution a m e v hvWeak
  filter_upwards [hcorrection] with x hx
  simp only [finiteAffineSolution_toH1, H1Function.add_grad,
    finiteAffineBoundaryH1_grad]
  rw [hx, congrFun hv x]
  abel

/-- The selected affine-solution gradient is additive in the boundary slope. -/
theorem finiteAffineSolution_grad_add {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    (finiteAffineSolution a m (e + e')).toH1.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => (finiteAffineSolution a m e).toH1.grad x +
        (finiteAffineSolution a m e').toH1.grad x := by
  filter_upwards [finiteAffineCorrection_grad_add a m e e'] with x hx
  simp only [finiteAffineSolution_toH1, H1Function.add_grad,
    finiteAffineBoundaryH1_grad] at hx ⊢
  rw [hx]
  abel

/-- The selected affine-solution gradient is homogeneous in the boundary slope. -/
theorem finiteAffineSolution_grad_smul {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    (finiteAffineSolution a m (c • e)).toH1.grad
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => c • (finiteAffineSolution a m e).toH1.grad x := by
  filter_upwards [finiteAffineCorrection_grad_smul a m c e] with x hx
  simp only [finiteAffineSolution_toH1, H1Function.add_grad,
    finiteAffineBoundaryH1_grad] at hx ⊢
  rw [hx, smul_add]

/-- The selected affine solution is additive in the boundary slope almost
everywhere. -/
theorem finiteAffineSolution_toFun_add {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e e' : Vec d) :
    (finiteAffineSolution a m (e + e')).toH1.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => (finiteAffineSolution a m e).toH1.toFun x +
        (finiteAffineSolution a m e').toH1.toFun x := by
  filter_upwards [finiteAffineCorrection_toFun_add a m e e'] with x hx
  simp only [finiteAffineSolution_toH1, H1Function.add_toFun,
    finiteAffineBoundaryH1_toFun] at hx ⊢
  rw [hx, vecDot_add_left]
  abel

/-- The selected affine solution is homogeneous in the boundary slope almost
everywhere. -/
theorem finiteAffineSolution_toFun_smul {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (c : ℝ) (e : Vec d) :
    (finiteAffineSolution a m (c • e)).toH1.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun x => c * (finiteAffineSolution a m e).toH1.toFun x := by
  filter_upwards [finiteAffineCorrection_toFun_smul a m c e] with x hx
  simp only [finiteAffineSolution_toH1, H1Function.add_toFun,
    finiteAffineBoundaryH1_toFun] at hx ⊢
  rw [hx, vecDot_smul_left, mul_add]

private theorem forceBesovRegularity_zero {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) :
    Book.Ch03.ForceBesovRegularity Q s (0 : Vec d → Vec d) := by
  refine ⟨by simp, ?_⟩
  exact cubeBesovPositiveVectorPartialSeminormTwo_zero_bddAbove Q s

private theorem cubeBesovPositiveVectorPartialSeminormTwo_const
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (e : Vec d) (N : ℕ) :
    cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun _ ↦ e) = 0 := by
  have hsub :=
    cubeBesovPositiveVectorPartialSeminormTwo_sub_const
      Q s N (0 : Vec d → Vec d) (-e)
      (fun _ _ _ _ ↦ MeasureTheory.memLp_const (0 : Vec d))
  simpa only [Pi.zero_apply, sub_neg_eq_add, zero_add,
    cubeBesovPositiveVectorPartialSeminormTwo_zero] using hsub

private theorem forceBesovRegularity_const {d : ℕ} (Q : TriadicCube d)
    (s : ℝ) (e : Vec d) :
    Book.Ch03.ForceBesovRegularity Q s (fun _ ↦ e) := by
  refine ⟨MeasureTheory.memLp_const e, ⟨0, ?_⟩⟩
  rintro x ⟨N, rfl⟩
  exact (cubeBesovPositiveVectorPartialSeminormTwo_const Q s e N).le

private theorem scaleNormalizedPositiveBesovVectorNormTwo_const
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (e : Vec d) :
    Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q s (fun _ ↦ e) =
      euclideanNorm e := by
  have hsemi :
      cubeBesovPositiveVectorSeminormTwo Q s (fun _ ↦ e) = 0 := by
    unfold cubeBesovPositiveVectorSeminormTwo
    have hrange :
        Set.range (fun N : ℕ ↦
          cubeBesovPositiveVectorPartialSeminormTwo Q s N (fun _ ↦ e)) =
          ({0} : Set ℝ) := by
      ext x
      simp [cubeBesovPositiveVectorPartialSeminormTwo_const Q s e]
    rw [hrange]
    simp
  unfold Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo
    Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo euclideanNorm
  rw [cubeAverageVec_const, hsemi, add_zero]

private theorem finiteAffineBoundaryH1_isConstantCoeffForcedEquation
    {d : ℕ} [NeZero d] (m : ℤ) (e : Vec d) :
    Book.Ch03.IsConstantCoeffForcedEquation (originCube d m)
      (identityConstantCoeffMatrix d) (finiteAffineBoundaryH1 m e)
      (0 : Vec d → Vec d) := by
  let : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))) := by
    simpa [Book.Ch02.cubeDomain_coe, volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet
        (originCube d m)).isFiniteMeasure_restrict_volume
  have hvol :
      (MeasureTheory.volume
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))).toReal ≠ 0 := by
    change (MeasureTheory.volume (openCubeSet (originCube d m))).toReal ≠ 0
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos (originCube d m)).ne'
  have hsol :
      IsSolenoidalOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))
        (fun _ ↦ e) :=
    IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain
      (Book.Ch02.cubeDomain (originCube d m)).isDomain.isSobolevRegularDomain
      hvol e
  intro φ
  simpa only [identityConstantCoeffMatrix_matrix, HCPolySupport.matVecMul_one,
    Pi.zero_apply, vecDot_zero_left, integral_zero] using! hsol φ

@[expose]
public noncomputable def finiteAffineComparisonDatum {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d) :
    Book.Ch03.CoarseGrainingComparisonDatum (originCube d m) a
      (identityConstantCoeffMatrix d) (0 : Vec d → Vec d) where
  u := (finiteAffineSolution a m e).toH1
  v := finiteAffineBoundaryH1 m e
  uWeakSolution := (finiteAffineSolution a m e).weakSolution
  vWeakSolution := finiteAffineBoundaryH1_isConstantCoeffForcedEquation m e
  zeroTraceDifference := finiteAffineSolution_zeroTraceDifference a m e

private theorem poincareUpperEllipticityFactor_le_weakError {d : ℕ}
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ)
    {s : ℝ} (hs : 0 < s) :
    Book.Ch03.poincareUpperEllipticityFactor (originCube d m) a s (.finite 2) ≤
      Real.sqrt (2 * (d : ℝ)) * (1 + scalarIdentityWeakError a s m) := by
  let E := scalarIdentityWeakError a s m
  have hE_nonneg : 0 ≤ E := scalarIdentityWeakError_nonneg a s m
  have hdim_nonneg : 0 ≤ 2 * (d : ℝ) := by positivity
  have hLambda :=
    Book.Ch02.inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      (originCube d m) a hs (by norm_num : (0 : ℝ) < 1)
  have hLambda' :
      Book.Ch02.LambdaSq (originCube d m) s (.finite 2) a ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hLambda
  have hE_sq : E ^ 2 + 1 ≤ (1 + E) ^ 2 := by linarith only [hE_nonneg]
  have htarget_sq :
      Book.Ch02.LambdaSq (originCube d m) s (.finite 2) a ≤
        (Real.sqrt (2 * (d : ℝ)) * (1 + E)) ^ 2 := by
    calc
      Book.Ch02.LambdaSq (originCube d m) s (.finite 2) a ≤
          2 * (d : ℝ) * (E ^ 2 + 1) := hLambda'
      _ ≤ 2 * (d : ℝ) * (1 + E) ^ 2 :=
        mul_le_mul_of_nonneg_left hE_sq hdim_nonneg
      _ = (Real.sqrt (2 * (d : ℝ)) * (1 + E)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hdim_nonneg]
  have hright_nonneg :
      0 ≤ Real.sqrt (2 * (d : ℝ)) * (1 + E) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith only [hE_nonneg])
  have hsqrt :
      Real.sqrt (Book.Ch02.LambdaSq (originCube d m) s (.finite 2) a) ≤
        Real.sqrt (2 * (d : ℝ)) * (1 + E) :=
    (Real.sqrt_le_iff).2 ⟨hright_nonneg, htarget_sq⟩
  simpa [Book.Ch03.poincareUpperEllipticityFactor, Real.sqrt_eq_rpow, E]
    using hsqrt

private theorem coarseGrainingHomogenizationErrorAtDepth_zero
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Book.Ch03.ConstantCoeffMatrix d) (r : ℝ) :
    Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 =
      Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a a0.matrix := by
  simp [Book.Ch03.coarseGrainingHomogenizationErrorAtDepth,
    descendantsAtDepth_zero, Book.Ch02.finsetSupReal]

private theorem homogenizationComparisonFluxSeminorm_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch03.CoeffFamily d) (a0 : Book.Ch03.ConstantCoeffMatrix d)
    (s : ℝ) (hs : 0 < s)
    (u v : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) := by
  have huGrad : MemVectorL2 (cubeSet Q) u.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet u).grad_memVectorL2
  have hvGrad : MemVectorL2 (cubeSet Q) v.grad := by
    simpa using (Book.Ch03.publicH1ToCubeSet v).grad_memVectorL2
  have hEll0 :
      IsEllipticFieldOn a0.lam a0.Lam (cubeSet Q)
        (constantCoeffField a0.matrix) :=
    Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField a0
      (measurableSet_cubeSet Q)
  let Ginternal : Vec d → Vec d :=
    fluxComparison (Book.Ch03.publicCoeffField Q a) a0.matrix u.grad v.grad
  have hfluxA : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a) huGrad
  have hflux0 : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul a0.matrix (v.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll0 hvGrad
  have hGinternal : MemVectorL2 (cubeSet Q) Ginternal := by
    dsimp [Ginternal, fluxComparison]
    exact hfluxA.sub hflux0
  have hae :
      Book.Ch03.homogenizationComparisonFluxField Q a a0 u v
        =ᵐ[volumeMeasureOn (cubeSet Q)] Ginternal :=
    Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
      (Q := Q) (a := a) (a0 := a0) u v
  have hmem : MemVectorL2 (cubeSet Q)
      (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v) :=
    MeasureTheory.MemLp.ae_eq hae.symm hGinternal
  have hmemNormalized :
      MeasureTheory.MemLp
        (Book.Ch03.homogenizationComparisonFluxField Q a a0 u v)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hmem
  exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp Q hs _ hmemNormalized

private theorem finiteAffineCorrection_grad_eq_comparisonGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (m : ℤ) (e : Vec d) :
    (finiteAffineCorrection a m e).toH1Function.grad =
      Book.Ch03.homogenizationComparisonConstantGradientField
        (identityConstantCoeffMatrix d) (finiteAffineSolution a m e).toH1
        (finiteAffineBoundaryH1 m e) := by
  funext x
  rw [finiteAffineSolution_toH1]
  simp only [Book.Ch03.homogenizationComparisonConstantGradientField,
    identityConstantCoeffMatrix_matrix, HCPolySupport.matVecMul_one]
  have hadd :=
    congrFun (H1Function.add_grad (finiteAffineBoundaryH1 m e)
      (finiteAffineCorrection a m e).toH1Function) x
  have hb := congrFun (finiteAffineBoundaryH1_grad m e) x
  rw [hadd, hb]
  abel

/-- The coefficient-energy norm of the finite affine-boundary solution is
controlled by the `q = 2` identity response error at the same order. -/
theorem exists_finiteAffineSolutionEnergyEstimateConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d),
        Book.Ch03.h1EnergyNormOnCube (originCube d m) a
            (finiteAffineSolution a m e).toH1 ≤
          C * (1 + scalarIdentityWeakError a s m) * euclideanNorm e := by
  rcases (Book.Ch03.energyConsequencesRHSTheory (d := d)).exists_constant with
    ⟨Cbase, hCbase, henergy, _⟩
  let C : ℝ :=
    Cbase * Real.rpow s (-(1 / 2 : ℝ)) * Real.sqrt (2 * (d : ℝ))
  have hdim_pos : 0 < 2 * (d : ℝ) := by
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos hCbase (Real.rpow_pos_of_pos hs _)) (Real.sqrt_pos.2 hdim_pos)
  refine ⟨C, hC, ?_⟩
  intro a m e
  let Q := originCube d m
  have hboundaryRegularity :
      Book.Ch03.ForceBesovRegularity Q s
        (Book.Ch03.dirichletBoundaryGradientField
          (finiteAffineSolution a m e)) := by
    simpa [Q, Book.Ch03.dirichletBoundaryGradientField, finiteAffineSolution] using
      forceBesovRegularity_const Q s e
  have hboundaryNorm :
      Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q s
          (Book.Ch03.dirichletBoundaryGradientField
            (finiteAffineSolution a m e)) = euclideanNorm e := by
    simpa [Q, Book.Ch03.dirichletBoundaryGradientField, finiteAffineSolution] using
      scaleNormalizedPositiveBesovVectorNormTwo_const Q s e
  have hbase :=
    henergy (finiteAffineSolution a m e) hs hs_lt
      (forceBesovRegularity_zero Q s) hboundaryRegularity
  have hbaseExpanded :
      Book.Ch03.h1EnergyNormOnCube Q a (finiteAffineSolution a m e).toH1 ≤
        Cbase * Real.rpow s (-(3 / 2 : ℝ)) *
            Book.Ch03.poincareLowerEllipticityFactor Q a (s / 2) (.finite 2) *
            Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s
              (0 : Vec d → Vec d) +
          Cbase * Real.rpow s (-(1 / 2 : ℝ)) *
            Book.Ch03.poincareUpperEllipticityFactor Q a s (.finite 2) *
            Book.Ch03.scaleNormalizedPositiveBesovVectorNormTwo Q s
              (Book.Ch03.dirichletBoundaryGradientField
                (finiteAffineSolution a m e)) := by
    simpa only [Book.Ch03.dirichletForcedSolutionEnergyNorm,
      Book.Ch03.dirichletEnergyWithRHSRHS] using hbase
  rw [hboundaryNorm] at hbaseExpanded
  have hbase' :
      Book.Ch03.h1EnergyNormOnCube Q a (finiteAffineSolution a m e).toH1 ≤
        Cbase * Real.rpow s (-(1 / 2 : ℝ)) *
          Book.Ch03.poincareUpperEllipticityFactor Q a s (.finite 2) *
            euclideanNorm e := by
    simpa only [cubeBesovPositiveVectorSeminormTwo_zero, mul_zero, zero_add] using
      hbaseExpanded
  have hu := poincareUpperEllipticityFactor_le_weakError a m hs
  have hleft_nonneg :
      0 ≤ Cbase * Real.rpow s (-(1 / 2 : ℝ)) :=
    mul_nonneg hCbase.le (Real.rpow_nonneg hs.le _)
  have he_nonneg : 0 ≤ euclideanNorm e := euclideanNorm_nonneg e
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d m) a
        (finiteAffineSolution a m e).toH1 =
        Book.Ch03.h1EnergyNormOnCube Q a
          (finiteAffineSolution a m e).toH1 := rfl
    _ ≤ Cbase * Real.rpow s (-(1 / 2 : ℝ)) *
          Book.Ch03.poincareUpperEllipticityFactor Q a s (.finite 2) *
            euclideanNorm e := hbase'
    _ ≤ Cbase * Real.rpow s (-(1 / 2 : ℝ)) *
          (Real.sqrt (2 * (d : ℝ)) *
            (1 + scalarIdentityWeakError a s m)) * euclideanNorm e :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu hleft_nonneg) he_nonneg
    _ = C * (1 + scalarIdentityWeakError a s m) * euclideanNorm e := by
      dsimp [C]
      ring

/-- The printed display HC (5.61) at matched order.  At output order
`sOut`, the finite solution's weak gradient and flux errors are controlled by
the `q = 2` response error at **every** order `b` with `2 * b < sOut`; the
symmetric split `b = r / 2` of the negative-Besov estimate constant is the
special case
`r = 2 * b`.  Taking `sOut := b + 1 / 2` therefore admits every `b < 1 / 2`. -/
theorem exists_finiteAffineSolutionNegativeBesovEstimateConstant_at_error_order
    (d : ℕ) [NeZero d] (sOut b : ℝ)
    (hb : 0 < b) (h2b : 2 * b < sOut) (hsOut_lt : sOut < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d),
        Book.Ch03.homogenizationComparisonNegativeBesovLHS
            (originCube d m) a (identityConstantCoeffMatrix d) sOut
            (finiteAffineSolution a m e).toH1 (finiteAffineBoundaryH1 m e) ≤
          C * scalarIdentityWeakError a b m *
            (1 + scalarIdentityWeakError a b m) * euclideanNorm e := by
  have hsOut : 0 < sOut :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) hb).trans h2b
  have hb_half : b < sOut / 2 := by linarith only [h2b]
  let r : ℝ := (b + sOut / 2) / 2
  have hbr : b < r := by
    dsimp [r]
    linarith only [hb_half]
  have hrs : r < sOut / 2 := by
    dsimp [r]
    linarith only [hb_half]
  have hr : 0 < r := hb.trans hbr
  have hr_lt_half : r < 1 / 2 := by linarith only [hrs, hsOut_lt]
  have hb_lt_one : b < 1 := by linarith only [hb_half, hsOut_lt]
  rcases exists_finiteAffineSolutionEnergyEstimateConstant d b hb hb_lt_one with
    ⟨Cenergy, hCenergy, henergy⟩
  rcases exists_normalizedCubeNegativeBesovComparisonConstant d with
    ⟨Ccomparison, hCcomparison, hcomparison⟩
  let M : ℝ :=
    Book.Ch03.constantCoeffMatrixNormHalf (identityConstantCoeffMatrix d)
  let P : ℝ :=
    sOut⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
      Ccomparison * r⁻¹ * M
  let K : ℝ :=
    Book.Ch02.geometricDiscount r 1 *
      (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
      (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹
  let C : ℝ := P * K * Cenergy
  have hmatrix_pos :
      0 < Book.Ch02.matrixNorm (identityConstantCoeffMatrix d).matrix := by
    simpa using
      (lt_of_lt_of_le zero_lt_one (Book.Ch02.one_le_matrixNorm_one (d := d)))
  have hM : 0 < M := Real.rpow_pos_of_pos hmatrix_pos _
  have hP : 0 < P := by
    dsimp [P]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos
            (mul_pos (inv_pos.mpr hsOut) (pow_pos (inv_pos.mpr hr) _))
            (inv_pos.mpr (sub_pos.mpr hr_lt_half)))
          hCcomparison)
        (inv_pos.mpr hr))
      hM
  have hdisc_r_pos : 0 < Book.Ch02.geometricDiscount r 1 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (by simpa only [mul_one] using hr)
  have hdisc_gap_pos : 0 < Book.Ch02.geometricDiscount (r - b) 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos
        (mul_pos (sub_pos.mpr hbr) (by norm_num : (0 : ℝ) < 2))
  have hdisc_b_pos : 0 < Book.Ch02.geometricDiscount b 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      geometricDiscount_pos (mul_pos hb (by norm_num : (0 : ℝ) < 2))
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos
      (mul_pos hdisc_r_pos (inv_pos.mpr (Real.sqrt_pos.2 hdisc_gap_pos)))
      (inv_pos.mpr (Real.sqrt_pos.2 hdisc_b_pos))
  have hC : 0 < C := mul_pos (mul_pos hP hK) hCenergy
  refine ⟨C, hC, ?_⟩
  intro a m e
  let Q := originCube d m
  let E := scalarIdentityWeakError a b m
  let H :=
    Book.Ch02.HomogenizationErrorOnCube Q r .infinity (.finite 1) a
      (1 : Mat d)
  let A := Book.Ch03.h1EnergyNormOnCube Q a (finiteAffineSolution a m e).toH1
  have hcomparisonBase :=
    hcomparison (j := 0) (r₂ := r) (finiteAffineComparisonDatum a m e)
      hsOut hr hrs hsOut_lt le_rfl (forceBesovRegularity_zero Q r)
  have hdepth :
      Book.Ch03.coarseGrainingHomogenizationErrorAtDepth Q a
          (identityConstantCoeffMatrix d) r 0 = H := by
    simpa [Q, H] using
      coarseGrainingHomogenizationErrorAtDepth_zero Q a
        (identityConstantCoeffMatrix d) r
  have hcomparison' :
      Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (identityConstantCoeffMatrix d) sOut
          (finiteAffineSolution a m e).toH1 (finiteAffineBoundaryH1 m e) ≤
        P * H * A := by
    calc
      Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (identityConstantCoeffMatrix d) sOut
          (finiteAffineSolution a m e).toH1 (finiteAffineBoundaryH1 m e) ≤
          Book.Ch03.generalCoarseGrainingL2TwoExponentRHS Ccomparison Q a
            (identityConstantCoeffMatrix d) sOut r r 0
            (0 : Vec d → Vec d) (finiteAffineSolution a m e).toH1 :=
        hcomparisonBase
      _ = P * H * A := by
        simp [Book.Ch03.generalCoarseGrainingL2TwoExponentRHS,
          Book.Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS, hdepth,
          P, M, A]
        ring
  have hHE : H ≤ K * E := by
    simpa [Q, H, K, E, scalarIdentityWeakError] using
      homogenizationErrorOnCube_infinity_one_le_gap_mul_infinity_two
        Q a (1 : Mat d) hb hbr
  have hE_nonneg : 0 ≤ E := scalarIdentityWeakError_nonneg a b m
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have henergy' :
      A ≤ Cenergy * (1 + E) * euclideanNorm e := by
    simpa [A, E, Q] using henergy a m e
  calc
    Book.Ch03.homogenizationComparisonNegativeBesovLHS
        (originCube d m) a (identityConstantCoeffMatrix d) sOut
        (finiteAffineSolution a m e).toH1 (finiteAffineBoundaryH1 m e) =
        Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
          (identityConstantCoeffMatrix d) sOut
          (finiteAffineSolution a m e).toH1 (finiteAffineBoundaryH1 m e) := rfl
    _ ≤ P * H * A := hcomparison'
    _ ≤ P * (K * E) * A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hHE hP.le) hA_nonneg
    _ ≤ P * (K * E) * (Cenergy * (1 + E) * euclideanNorm e) :=
      mul_le_mul_of_nonneg_left henergy'
        (mul_nonneg hP.le (mul_nonneg hK.le hE_nonneg))
    _ = C * E * (1 + E) * euclideanNorm e := by
      dsimp [C]
      ring
    _ = C * scalarIdentityWeakError a b m *
        (1 + scalarIdentityWeakError a b m) * euclideanNorm e := rfl

/-- The printed display HC (5.62) at matched order.  The normalized
`L²` size of the finite zero-trace correction is controlled by the response
error at the **same** order `b`, for every `b ∈ (0, 1/2)` — the printed window
of HC, Proposition 5.3. -/
theorem exists_finiteAffineSolutionL2SlopeErrorEstimateConstant_at_error_order
    (d : ℕ) [NeZero d] (b : ℝ) (hb : 0 < b) (hb_lt : b < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (m : ℤ) (e : Vec d),
        cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
            cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
              (fun x ↦ (finiteAffineCorrection a m e).toH1Function.toFun x) ≤
          C * scalarIdentityWeakError a b m *
            (1 + scalarIdentityWeakError a b m) * euclideanNorm e := by
  let t : ℝ := (b + 1 / 2) / 2
  have hbt : b < t := by
    dsimp [t]
    linarith only [hb_lt]
  have ht : 0 < t := hb.trans hbt
  have ht_lt : t < 1 / 2 := by
    dsimp [t]
    linarith only [hb_lt]
  have hsOut : 0 < 2 * t := by positivity
  have hsOut_lt : 2 * t < 1 := by linarith only [ht_lt]
  have h2b : 2 * b < 2 * t := by linarith only [hbt]
  rcases exists_finiteAffineSolutionNegativeBesovEstimateConstant_at_error_order
      d (2 * t) b hb h2b hsOut_lt with
    ⟨Cweak, hCweak, hweak⟩
  let K : ℝ :=
    (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ) +
        2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹))
  let C : ℝ := max 1 (K * Cweak)
  have hK_nonneg : 0 ≤ K := by
    have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
      Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
    dsimp [K]
    exact mul_nonneg
      (add_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by exact_mod_cast Nat.zero_le d) hcz)
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
          (by exact_mod_cast Nat.zero_le d))
        (mul_nonneg (by norm_num)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)))
      (Real.sqrt_nonneg _)
  have hC : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (K * Cweak))
  refine ⟨C, hC, ?_⟩
  intro a m e
  let Q := originCube d m
  let E := scalarIdentityWeakError a b m
  let N := cubeBesovNegativeVectorSeminormTwo Q (2 * t)
    (fun x ↦ (finiteAffineCorrection a m e).toH1Function.grad x)
  let L := Book.Ch03.homogenizationComparisonNegativeBesovLHS Q a
    (identityConstantCoeffMatrix d) (2 * t) (finiteAffineSolution a m e).toH1
    (finiteAffineBoundaryH1 m e)
  have hPoincare :
      cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ (finiteAffineCorrection a m e).toH1Function.toFun x) ≤
        K * N := by
    simpa [K, N] using
      Book.Ch03.cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
        Q (Book.Ch03.publicH10ToCubeSet (finiteAffineCorrection a m e)) ht ht_lt
  have hflux_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (Book.Ch03.homogenizationComparisonFluxField Q a
          (identityConstantCoeffMatrix d) (finiteAffineSolution a m e).toH1
          (finiteAffineBoundaryH1 m e)) :=
    homogenizationComparisonFluxSeminorm_nonneg Q a
      (identityConstantCoeffMatrix d) (2 * t) hsOut
      (finiteAffineSolution a m e).toH1 (finiteAffineBoundaryH1 m e)
  have hN_eq :
      N = cubeBesovNegativeVectorSeminormTwo Q (2 * t)
        (Book.Ch03.homogenizationComparisonConstantGradientField
          (identityConstantCoeffMatrix d) (finiteAffineSolution a m e).toH1
          (finiteAffineBoundaryH1 m e)) := by
    change cubeBesovNegativeVectorSeminormTwo Q (2 * t)
      (finiteAffineCorrection a m e).toH1Function.grad = _
    exact congrArg (cubeBesovNegativeVectorSeminormTwo Q (2 * t))
      (finiteAffineCorrection_grad_eq_comparisonGradient a m e)
  have hNL : N ≤ L := by
    rw [hN_eq]
    exact le_add_of_nonneg_right hflux_nonneg
  have hweak' :
      L ≤ Cweak * E * (1 + E) * euclideanNorm e := by
    simpa [L, E, Q] using hweak a m e
  have htail_nonneg : 0 ≤ E * (1 + E) * euclideanNorm e := by
    have hE : 0 ≤ E := scalarIdentityWeakError_nonneg a b m
    exact mul_nonneg (mul_nonneg hE (by linarith only [hE]))
      (euclideanNorm_nonneg e)
  calc
    cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
        cubeLpNorm (originCube d m) (2 : ℝ≥0∞)
          (fun x ↦ (finiteAffineCorrection a m e).toH1Function.toFun x) =
        cubeBesovScaleWeight (1 : ℝ) Q *
          cubeLpNorm Q (2 : ℝ≥0∞)
            (fun x ↦ (finiteAffineCorrection a m e).toH1Function.toFun x) := rfl
    _ ≤ K * N := hPoincare
    _ ≤ K * L := mul_le_mul_of_nonneg_left hNL hK_nonneg
    _ ≤ K * (Cweak * E * (1 + E) * euclideanNorm e) :=
      mul_le_mul_of_nonneg_left hweak' hK_nonneg
    _ = (K * Cweak) * (E * (1 + E) * euclideanNorm e) := by ring
    _ ≤ C * (E * (1 + E) * euclideanNorm e) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 (K * Cweak)) htail_nonneg
    _ = C * scalarIdentityWeakError a b m *
        (1 + scalarIdentityWeakError a b m) * euclideanNorm e := by
      dsimp [E]
      ring

end

end HighContrast
end HCPolySupport
