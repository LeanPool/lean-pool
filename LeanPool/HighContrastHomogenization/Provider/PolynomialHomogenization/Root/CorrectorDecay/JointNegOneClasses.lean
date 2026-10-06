/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.NegOneTriangle
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.JointRemainderRows

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.JointNegOneClasses

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private instance openCubeFiniteMeasure (d : ℕ) (Q : TriadicCube d) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
  simpa only [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem openCube_h1_grad_memVectorL2
    {d : ℕ} {Q : TriadicCube d}
    (u : H1Function (Book.Ch02.cubeDomain Q)) :
    MemVectorL2 (openCubeSet Q) u.grad := by
  simpa only [Book.Ch02.cubeDomain_coe] using u.grad_memVectorL2

theorem openCube_const_memVectorL2
    {d : ℕ} (Q : TriadicCube d) (e : Vec d) :
    MemVectorL2 (openCubeSet Q) (fun _ ↦ e) := by
  exact memVectorL2_const e

/-- The finite affine gradient defect as an outer-cube quotient class. -/
@[expose]
noncomputable def outerFiniteGradientClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (m : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d m)) :=
  let u := (finiteAffineSolution a m e).toH1
  toHilbertVectorL2OfVecField
    ((openCube_h1_grad_memVectorL2 u).sub
      (openCube_const_memVectorL2 (originCube d m) e))

/-- The finite affine flux defect as an outer-cube quotient class. -/
@[expose]
noncomputable def outerFiniteFluxClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (m : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d m)) :=
  let Q := originCube d m
  let u := (finiteAffineSolution a m e).toH1
  let hu := openCube_h1_grad_memVectorL2 u
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet Q a
  toHilbertVectorL2OfVecField
    ((memVectorL2_matVecMul_of_isEllipticFieldOn hEll hu).sub
      (openCube_const_memVectorL2 Q e))

/-- The outer finite gradient defect restricted across the fixed gap. -/
@[expose]
noncomputable def innerFiniteGradientClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q : ℕ) :
    HilbertVectorL2 (openCubeSet (originCube d (q : ℤ))) :=
  localHilbertVectorL2Restrict
    (openCubeSet_originCube_subset_of_le (show (q : ℤ) ≤ (q : ℤ) + 3 by omega))
    (outerFiniteGradientClass a e ((q : ℤ) + 3))

/-- The outer finite flux defect restricted across the fixed gap. -/
@[expose]
noncomputable def innerFiniteFluxClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q : ℕ) :
    HilbertVectorL2 (openCubeSet (originCube d (q : ℤ))) :=
  localHilbertVectorL2Restrict
    (openCubeSet_originCube_subset_of_le (show (q : ℤ) ≤ (q : ℤ) + 3 by omega))
    (outerFiniteFluxClass a e ((q : ℤ) + 3))

/-- The exact joint gradient minus its fixed-gap finite approximation. -/
@[expose]
noncomputable def jointGradientRemainderClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (q : ℕ) :
    HilbertVectorL2 (openCubeSet (originCube d (q : ℤ))) :=
  correctorGradientOnOriginCube Phi e (q : ℤ) -
    innerFiniteGradientClass a e q

/-- The exact joint flux defect minus its fixed-gap finite approximation. -/
@[expose]
noncomputable def jointFluxRemainderClass
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (q : ℕ) :
    HilbertVectorL2 (openCubeSet (originCube d (q : ℤ))) :=
  scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e (q : ℤ) -
    innerFiniteFluxClass a e q

/-- The gradient class is the sum of its restricted finite part and its
remainder, as an exact quotient identity. -/
theorem correctorGradient_eq_innerFinite_add_remainder
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (q : ℕ) :
    correctorGradientOnOriginCube Phi e (q : ℤ) =
      innerFiniteGradientClass a e q +
        jointGradientRemainderClass a Phi e q := by
  unfold jointGradientRemainderClass
  abel

/-- The flux class is the sum of its restricted finite part and its
remainder, as an exact quotient identity. -/
theorem correctorFlux_eq_innerFinite_add_remainder
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (q : ℕ) :
    scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e (q : ℤ) =
      innerFiniteFluxClass a e q +
        jointFluxRemainderClass a Phi e q := by
  unfold jointFluxRemainderClass
  abel

theorem outerFiniteGradient_toVec_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (m : ℤ) :
    (fun x ↦ (outerFiniteGradientClass a e m x).toVec)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
      fun x ↦ (finiteAffineSolution a m e).toH1.grad x - e := by
  exact (coeFn_toHilbertVectorL2OfVecField _).mono fun _ hx ↦ by
    simpa only [outerFiniteGradientClass, hilbertifyVecField,
      HilbertVec.toVec_ofVec, Pi.sub_apply] using!
        congrArg HilbertVec.toVec hx

theorem outerFiniteFlux_toVec_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (m : ℤ) :
    (fun x ↦ (outerFiniteFluxClass a e m x).toVec)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
      fun x ↦ matVecMul
        (Book.Ch03.publicCoeffField (originCube d m) a x)
        ((finiteAffineSolution a m e).toH1.grad x) - e := by
  exact (coeFn_toHilbertVectorL2OfVecField _).mono fun _ hx ↦ by
    simpa only [outerFiniteFluxClass, hilbertifyVecField,
      HilbertVec.toVec_ofVec, Pi.sub_apply] using!
        congrArg HilbertVec.toVec hx

private theorem correctorGradient_toVec_ae
    {d : ℕ} (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (q : ℕ) :
    (fun x ↦ (correctorGradientOnOriginCube Phi e (q : ℤ) x).toVec)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))]
      ((Phi e).localH1Function q).grad := by
  have hclass : correctorGradientOnOriginCube Phi e (q : ℤ) =
      ((Phi e).localH1Function q).gradToHilbertVectorL2 := by
    simp only [correctorGradientOnOriginCube,
      LocalGradientCarrier.originCubeComponent_natCast,
      NormalizedLocalH1Carrier.gradientComponent,
      NormalizedLocalH1Carrier.localH1Function_gradToHilbertVectorL2]
    rfl
  rw [hclass]
  exact ((Phi e).localH1Function q).coeFn_gradToHilbertVectorL2.mono
    fun _ hx ↦ by
      simpa only [hilbertifyVecField, HilbertVec.toVec_ofVec] using!
        congrArg HilbertVec.toVec hx

/-- The quotient remainder has the literal finite-to-joint gradient
representative used by the energy telescope. -/
theorem jointGradientRemainder_toVec_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q : ℕ) :
    (fun x ↦ (jointGradientRemainderClass a Phi e q x).toVec)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))]
      (jointFiniteRemainderCubeSolution a Phi hPhi e q (q + 3)
        (by omega)).toH1.grad := by
  change
    (fun x ↦ ((correctorGradientOnOriginCube Phi e (q : ℤ) -
      innerFiniteGradientClass a e q) x).toVec) =ᵐ[_]
      (jointFiniteRemainderCubeSolution a Phi hPhi e q (q + 3)
        (by omega)).toH1.grad
  let hsub : openCubeSet (originCube d (q : ℤ)) ⊆
      openCubeSet (originCube d ((q : ℤ) + 3)) :=
    openCubeSet_originCube_subset_of_le (by omega)
  let z := jointFiniteRemainderCubeSolution a Phi hPhi e q (q + 3)
    (by omega)
  filter_upwards [Lp.coeFn_sub
      (correctorGradientOnOriginCube Phi e (q : ℤ))
      (innerFiniteGradientClass a e q),
    correctorGradient_toVec_ae Phi e q,
    localHilbertVectorL2Restrict_coeFn_ae hsub
      (outerFiniteGradientClass a e ((q : ℤ) + 3)),
    (outerFiniteGradient_toVec_ae a e ((q : ℤ) + 3)).filter_mono
      (ae_mono (Measure.restrict_mono_set volume hsub))]
    with x hsubclass hcorrector hrestrict houter
  rw [hsubclass, Pi.sub_apply]
  change
    ((correctorGradientOnOriginCube Phi e (q : ℤ) x).toVec) -
        ((innerFiniteGradientClass a e q x).toVec) = _
  rw [hcorrector]
  simp only [innerFiniteGradientClass]
  have hrestrictVec := congrArg HilbertVec.toVec hrestrict
  rw [hrestrictVec, houter]
  rw [jointFiniteRemainder_grad]
  have hindex : ((q + 3 : ℕ) : ℤ) = (q : ℤ) + 3 := by omega
  rw [hindex]
  abel_nf

/-- The quotient remainder has the literal finite-to-joint flux
representative used by the energy telescope. -/
theorem jointFluxRemainder_toVec_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d)
    (hPhi : IsFiniteAffineCorrectionJointLocalEquation a Phi)
    (e : Vec d) (q : ℕ) :
    (fun x ↦ (jointFluxRemainderClass a Phi e q x).toVec)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d (q : ℤ)))]
      fun x ↦ matVecMul
        (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a x)
        ((jointFiniteRemainderCubeSolution a Phi hPhi e q (q + 3)
          (by omega)).toH1.grad x) := by
  let hsub : openCubeSet (originCube d (q : ℤ)) ⊆
      openCubeSet (originCube d ((q : ℤ) + 3)) :=
    openCubeSet_originCube_subset_of_le (by omega)
  let z := jointFiniteRemainderCubeSolution a Phi hPhi e q (q + 3)
    (by omega)
  have hgrad := correctorGradient_toVec_ae Phi e q
  have hgradClass : correctorGradientOnOriginCube Phi e (q : ℤ) =
      ((Phi e).localH1Function q).gradToHilbertVectorL2 := by
    simp only [correctorGradientOnOriginCube,
      LocalGradientCarrier.originCubeComponent_natCast,
      NormalizedLocalH1Carrier.gradientComponent,
      NormalizedLocalH1Carrier.localH1Function_gradToHilbertVectorL2]
    rfl
  have hcorrector := scalarIdentityCorrectorFluxDefectOnOriginCube_toVec_ae
    a Phi e (q : ℤ)
      (by simpa only [Book.Ch02.cubeDomain_coe] using!
        ((Phi e).localH1Function q).grad_memVectorL2)
      (by
        rw [hgradClass]
        apply Lp.ext
        filter_upwards [((Phi e).localH1Function q).coeFn_gradToHilbertVectorL2,
          coeFn_toHilbertVectorL2OfVecField
            (by simpa only [Book.Ch02.cubeDomain_coe] using
              ((Phi e).localH1Function q).grad_memVectorL2)] with x hx hy
        exact hx.trans hy.symm)
  change
    (fun x ↦ ((scalarIdentityCorrectorFluxDefectOnOriginCube
      a Phi e (q : ℤ) - innerFiniteFluxClass a e q) x).toVec) =ᵐ[_]
      fun x ↦ matVecMul
        (Book.Ch03.publicCoeffField (originCube d (q : ℤ)) a x)
        ((jointFiniteRemainderCubeSolution a Phi hPhi e q (q + 3)
          (by omega)).toH1.grad x)
  filter_upwards [Lp.coeFn_sub
      (scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e (q : ℤ))
      (innerFiniteFluxClass a e q),
    hcorrector,
    localHilbertVectorL2Restrict_coeFn_ae hsub
      (outerFiniteFluxClass a e ((q : ℤ) + 3)),
    (outerFiniteFlux_toVec_ae a e ((q : ℤ) + 3)).filter_mono
      (ae_mono (Measure.restrict_mono_set volume hsub)),
    publicCoeffField_originCube_ae_eq_of_le a
      (show (q : ℤ) ≤ (q : ℤ) + 3 by omega)]
    with x hsubclass hjoint hrestrict houter hcoeff
  rw [hsubclass, Pi.sub_apply]
  change
    ((scalarIdentityCorrectorFluxDefectOnOriginCube
        a Phi e (q : ℤ) x).toVec) -
      ((innerFiniteFluxClass a e q x).toVec) = _
  rw [hjoint]
  simp only [innerFiniteFluxClass]
  have hrestrictVec := congrArg HilbertVec.toVec hrestrict
  rw [hrestrictVec, houter, hcoeff]
  rw [jointFiniteRemainder_grad]
  have hindex : ((q + 3 : ℕ) : ℤ) = (q : ℤ) + 3 := by omega
  rw [hindex]
  rw [← matVecMul_sub_vec]
  abel

end

end HighContrast
end HCPolySupport
