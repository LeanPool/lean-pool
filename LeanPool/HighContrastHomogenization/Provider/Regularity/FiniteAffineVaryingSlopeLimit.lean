/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleSlopeCompactness
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorOriginCubeFields

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineVaryingSlopeLimit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Varying-slope finite-corrector limits

Finite dimensionality of the slope space upgrades pointwise convergence of
the finite corrector operators to convergence along any convergent sequence
of slopes. No operator-norm estimate or inverse slope comparison is needed.
-/

namespace HCPolySupport
namespace HighContrast

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem memVectorL2_const_varyingSlope {d : ℕ}
    (e : Vec d) (q : ℕ) :
    MemVectorL2 (openCubeSet (originCube d (q : ℤ))) (fun _ => e) := by
  simpa using
    (MeasureTheory.memLp_const
      (μ := volumeMeasureOn (openCubeSet (originCube d (q : ℤ))))
      (p := (2 : ENNReal)) (c := e))

@[expose]
public noncomputable def constantLocalGradientLinearMap
    (d q : ℕ) : Vec d →ₗ[ℝ] LocalGradientL2 d q where
  toFun e := constantGradientOnOriginCube e (q : ℤ)
  map_add' e e' := by
    change constantGradientOnOriginCube (e + e') (q : ℤ) =
        constantGradientOnOriginCube e (q : ℤ) +
          constantGradientOnOriginCube e' (q : ℤ)
    simp only [constantGradientOnOriginCube]
    apply MeasureTheory.Lp.ext
    filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const_varyingSlope e q),
       coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const_varyingSlope e' q),
       coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const_varyingSlope (e + e') q),
       MeasureTheory.Lp.coeFn_add
        (toHilbertVectorL2OfVecField (memVectorL2_const_varyingSlope e q))
        (toHilbertVectorL2OfVecField (memVectorL2_const_varyingSlope e' q))]
      with x he he' hadd hcoeAdd
    rw [hadd]
    rw [hcoeAdd, Pi.add_apply, he, he']
    rfl
  map_smul' c e := by
    change constantGradientOnOriginCube (c • e) (q : ℤ) =
        c • constantGradientOnOriginCube e (q : ℤ)
    simp only [constantGradientOnOriginCube]
    apply MeasureTheory.Lp.ext
    filter_upwards
      [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const_varyingSlope e q),
       coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const_varyingSlope (c • e) q),
       MeasureTheory.Lp.coeFn_smul c
        (toHilbertVectorL2OfVecField (memVectorL2_const_varyingSlope e q))]
      with x he hsmul hcoeSmul
    rw [hsmul]
    rw [hcoeSmul, Pi.smul_apply, he]
    rfl

@[expose]
public noncomputable def finiteAffineFullGradientLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (q k : ℕ) : Vec d →ₗ[ℝ] LocalGradientL2 d q where
  toFun e := constantLocalGradientLinearMap d q e +
    (normalizedLocalPair
      (finiteAffineCorrectionLocalSequence a e) q k).2
  map_add' e e' := by
    have hcorr := congrArg Prod.snd
      (normalizedLocalPair_finiteAffineCorrection_add a e e' q k)
    have hcorr' :
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a (e + e')) q k).2 =
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) q k).2 +
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e') q k).2 := by
      simpa only [Prod.snd_add] using hcorr
    rw [map_add, hcorr']
    abel
  map_smul' c e := by
    have hcorr := congrArg Prod.snd
      (normalizedLocalPair_finiteAffineCorrection_smul a c e q k)
    have hcorr' :
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a (c • e)) q k).2 =
        c • (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) q k).2 := by
      exact hcorr
    rw [map_smul, hcorr']
    simp only [RingHom.id_apply, smul_add]

/-- The canonical affine-plus-joint-corrector gradient on a fixed cube as a
linear map of the slope. -/
@[expose]
noncomputable def jointAffineFullGradientLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (q : ℕ) : Vec d →ₗ[ℝ] LocalGradientL2 d q where
  toFun e := constantLocalGradientLinearMap d q e +
    (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q
  map_add' e e' := by
    rw [map_add, finiteAffineCorrectionJointLocalLimit_add,
      NormalizedLocalH1Carrier.addCarrier_gradientComponent]
    module
  map_smul' c e := by
    rw [map_smul, finiteAffineCorrectionJointLocalLimit_smul,
      NormalizedLocalH1Carrier.smulCarrier_gradientComponent]
    simp only [RingHom.id_apply]
    module

private theorem localGradientRestrict_constantGradientOnOriginCube
    {d q r : ℕ} (hqr : q ≤ r) (e : Vec d) :
    localGradientRestrict hqr
        (show LocalGradientL2 d r from
          constantGradientOnOriginCube e (r : ℤ)) =
      (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) := by
  let hmu : volumeMeasureOn (localGradientCube d q) ≤
      volumeMeasureOn (localGradientCube d r) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hqr)
  have hrq := (coeFn_toHilbertVectorL2OfVecField
    (memVectorL2_const_varyingSlope e r)).filter_mono (ae_mono hmu)
  apply MeasureTheory.Lp.ext
  filter_upwards
    [localGradientRestrict_coeFn_ae hqr
      (show LocalGradientL2 d r from
        constantGradientOnOriginCube e (r : ℤ)),
     hrq,
     coeFn_toHilbertVectorL2OfVecField
      (memVectorL2_const_varyingSlope e q)]
    with x hrestrict hr hq
  rw [hrestrict]
  change (constantGradientOnOriginCube e (r : ℤ)) x =
    (constantGradientOnOriginCube e (q : ℤ)) x
  change (toHilbertVectorL2OfVecField
      (memVectorL2_const_varyingSlope e r)) x =
    (toHilbertVectorL2OfVecField
      (memVectorL2_const_varyingSlope e q)) x
  rw [hr, hq]

/-- Canonical full-gradient classes respect restriction between centered
cubes. -/
theorem localGradientRestrict_jointAffineFullGradientLinearMap
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    {q r : ℕ} (hqr : q ≤ r) (e : Vec d) :
    localGradientRestrict hqr
        ((jointAffineFullGradientLinearMap a hCauchy r) e) =
      (jointAffineFullGradientLinearMap a hCauchy q) e := by
  change localGradientRestrict hqr
      ((show LocalGradientL2 d r from
          constantGradientOnOriginCube e (r : ℤ)) +
        (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent r) =
    (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) +
      (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q
  rw [map_add, localGradientRestrict_constantGradientOnOriginCube]
  exact congrArg
    (fun z : LocalGradientL2 d q =>
      (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) + z)
    (LocalGradientCarrier.restrict_component
      (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradient hqr)

@[expose]
public noncomputable def finiteAffineFullGradientApproximationH1
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) : H1Function (localGradientCube d q) :=
  (show H1Function (localGradientCube d q) from by
    simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
      finiteAffineBoundaryH1 (q : ℤ) e) +
    normalizedLocalH1 (finiteAffineCorrectionLocalSequence a e) q k

private theorem finiteAffineFullGradientApproximationH1_grad
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    (finiteAffineFullGradientApproximationH1 a e q k).grad =
      (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad := by
  funext x
  change
    (finiteAffineBoundaryH1 (q : ℤ) e).grad x +
        (normalizeOnUnitCube
          (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
      (finiteAffineSolution a ((q + k : ℕ) : ℤ) e).toH1.grad x
  rw [finiteAffineSolution_toH1]
  change e +
      (normalizeOnUnitCube
        (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
    e + (finiteAffineCorrectionLocalSequence a e (q + k)).grad x
  rw [normalizeOnUnitCube_grad]

private theorem gradToHilbertVectorL2_eq_of_grad_eq_varyingSlope
    {d : ℕ} {U : Set (Vec d)} (u v : H1Function U)
    (hgrad : u.grad = v.grad) :
    u.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [u.coeFn_gradToHilbertVectorL2, v.coeFn_gradToHilbertVectorL2]
    with x hu hv
  rw [hu, hv, hgrad]

private theorem finiteAffineBoundary_gradToHilbertVectorL2_eq_constant
    {d q : ℕ} [NeZero d] (e : Vec d) :
    (show LocalGradientL2 d q from by
      simp only [localGradientCube]
      exact (finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2) =
      constantGradientOnOriginCube e (q : ℤ) := by
  change (finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2 =
    constantGradientOnOriginCube e (q : ℤ)
  apply MeasureTheory.Lp.ext
  filter_upwards
    [(finiteAffineBoundaryH1 (q : ℤ) e).coeFn_gradToHilbertVectorL2,
      coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const_varyingSlope e q)]
    with x hboundary hconst
  rw [hboundary]
  change hilbertifyVecField (finiteAffineBoundaryH1 (q : ℤ) e).grad x =
    (toHilbertVectorL2OfVecField
      (memVectorL2_const_varyingSlope e q)) x
  rw [hconst, finiteAffineBoundaryH1_grad]

/-- The linear-map presentation of a finite full-gradient class is exactly
the gradient class of the finite affine solution restricted to the fixed
inner cube. -/
theorem finiteAffineFullGradientClass_eq_innerH1Gradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) +
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) q k).2 =
      (finiteAffineSolutionInnerH1 a (q : ℤ) ((q + k : ℕ) : ℤ)
        (by omega) e).gradToHilbertVectorL2 := by
  let w : H1Function (localGradientCube d q) :=
    finiteAffineFullGradientApproximationH1 a e q k
  have hclass : w.gradToHilbertVectorL2 =
      (show LocalGradientL2 d q from
          constantGradientOnOriginCube e (q : ℤ)) +
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) q k).2 := by
    dsimp only [w, finiteAffineFullGradientApproximationH1]
    rw [H1Function.gradToHilbertVectorL2_add]
    change (finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2 + _ = _
    have hb := finiteAffineBoundary_gradToHilbertVectorL2_eq_constant
      (d := d) (q := q) e
    change (finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2 =
      constantGradientOnOriginCube e (q : ℤ) at hb
    rw [hb]
    rfl
  rw [← hclass]
  apply gradToHilbertVectorL2_eq_of_grad_eq_varyingSlope
  exact finiteAffineFullGradientApproximationH1_grad a e q k

private theorem vec_sum_smul_basisVec {d : ℕ} (e : Vec d) :
    ∑ i : Fin d, e i • basisVec i = e := by
  ext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  simp

/-- Pointwise convergence of linear maps out of the finite project-vector
space permits simultaneous convergence of the input vectors. -/
theorem tendsto_linearMap_apply_of_forall_tendsto_of_tendsto
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ → Vec d →ₗ[ℝ] E) (L : Vec d →ₗ[ℝ] E)
    (hT : ∀ e, Tendsto (fun k => T k e) atTop (nhds (L e)))
    (e : ℕ → Vec d) (eLim : Vec d)
    (he : Tendsto e atTop (nhds eLim)) :
    Tendsto (fun k => T k (e k)) atTop (nhds (L eLim)) := by
  have hcoord : ∀ i : Fin d,
      Tendsto (fun k => (e k i) • T k (basisVec i)) atTop
        (nhds ((eLim i) • L (basisVec i))) := by
    intro i
    exact ((continuous_apply i).tendsto eLim |>.comp he).smul (hT (basisVec i))
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  convert hsum using 1
  · funext k
    calc
      T k (e k) = T k (∑ i : Fin d, e k i • basisVec i) := by
        rw [vec_sum_smul_basisVec]
      _ = ∑ i : Fin d, e k i • T k (basisVec i) := by
        simp only [map_sum, map_smul]
  · congr 1
    calc
      L eLim = L (∑ i : Fin d, eLim i • basisVec i) := by
        rw [vec_sum_smul_basisVec]
      _ = ∑ i : Fin d, eLim i • L (basisVec i) := by
        simp only [map_sum, map_smul]

/-- On every fixed cube, finite affine full-gradient classes with convergent
boundary slopes converge to the canonical affine-plus-corrector class at the
limiting slope. -/
theorem finiteAffineFullGradient_varyingSlope_tendsto_jointLocalGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (q : ℕ) (e : ℕ → Vec d) (eLim : Vec d)
    (he : Tendsto e atTop (nhds eLim)) :
    Tendsto
      (fun k => (show LocalGradientL2 d q from
          constantGradientOnOriginCube (e k) (q : ℤ)) +
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a (e k)) q k).2)
      atTop
      (nhds ((show LocalGradientL2 d q from
          constantGradientOnOriginCube eLim (q : ℤ)) +
        (finiteAffineCorrectionJointLocalLimit a hCauchy eLim).gradientComponent q)) := by
  apply tendsto_linearMap_apply_of_forall_tendsto_of_tendsto
    (fun k => finiteAffineFullGradientLinearMap a q k)
    (jointAffineFullGradientLinearMap a hCauchy q) _ e eLim he
  intro p
  exact tendsto_const_nhds.add
    (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy p q).snd_nhds

/-- Equivalent restricted-solution form of the varying-slope convergence
theorem. -/
theorem finiteAffineSolutionInnerGradient_varyingSlope_tendsto_jointLocalGradient
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (q : ℕ) (e : ℕ → Vec d) (eLim : Vec d)
    (he : Tendsto e atTop (nhds eLim)) :
    Tendsto
      (fun k => (finiteAffineSolutionInnerH1 a (q : ℤ)
        ((q + k : ℕ) : ℤ) (by omega) (e k)).gradToHilbertVectorL2)
      atTop
      (nhds ((show LocalGradientL2 d q from
          constantGradientOnOriginCube eLim (q : ℤ)) +
        (finiteAffineCorrectionJointLocalLimit a hCauchy eLim).gradientComponent q)) := by
  exact (finiteAffineFullGradient_varyingSlope_tendsto_jointLocalGradient
    a hCauchy q e eLim he).congr'
      (Eventually.of_forall fun k =>
        finiteAffineFullGradientClass_eq_innerH1Gradient a (e k) q k)

/-- Cofinally reindexed form of the varying-slope restricted-solution
convergence theorem. -/
theorem finiteAffineSolutionInnerGradient_varyingSlope_tendsto_jointLocalGradient_along
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (q : ℕ) (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (e : ℕ → Vec d) (eLim : Vec d)
    (he : Tendsto e atTop (nhds eLim)) :
    Tendsto
      (fun k => (finiteAffineSolutionInnerH1 a (q : ℤ)
        ((q + rho k : ℕ) : ℤ) (by omega) (e k)).gradToHilbertVectorL2)
      atTop
      (nhds ((show LocalGradientL2 d q from
          constantGradientOnOriginCube eLim (q : ℤ)) +
        (finiteAffineCorrectionJointLocalLimit a hCauchy eLim).gradientComponent q)) := by
  have hfull : Tendsto
      (fun k => (finiteAffineFullGradientLinearMap a q (rho k)) (e k)) atTop
      (nhds ((jointAffineFullGradientLinearMap a hCauchy q) eLim)) := by
    apply tendsto_linearMap_apply_of_forall_tendsto_of_tendsto
      (fun k => finiteAffineFullGradientLinearMap a q (rho k))
      (jointAffineFullGradientLinearMap a hCauchy q) _ e eLim he
    intro p
    exact (tendsto_const_nhds.add
      (finiteAffineCorrectionJointLocalLimit_isLimit a hCauchy p q).snd_nhds).comp hrho
  exact hfull.congr' (Eventually.of_forall fun k =>
    finiteAffineFullGradientClass_eq_innerH1Gradient a (e k) q (rho k))

/-- Cofinal outer-scale version of fixed-cube residual identification. -/
theorem finiteAffineResidual_identifies_jointLocalGradient_along
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (q : ℕ) (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (u : ∀ k : ℕ,
      Book.Ch03.CubeSolution (originCube d ((q + rho k : ℕ) : ℤ)) a)
    (Dv : Vec d → Vec d) (huGrad : ∀ k, (u k).toH1.grad = Dv)
    (e : ℕ → Vec d) (eLim : Vec d)
    (he : Tendsto e atTop (nhds eLim))
    (hresidual : Tendsto
      (fun k => weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ (u k).toH1.grad x -
          (finiteAffineSolution a ((q + rho k : ℕ) : ℤ) (e k)).toH1.grad x))
      atTop (nhds 0)) :
    (finiteCubeSolutionRestriction a (by omega) (u 0)).toH1.gradToHilbertVectorL2 =
      (jointAffineFullGradientLinearMap a hCauchy q) eLim := by
  have hqk : ∀ k, (q : ℤ) ≤ ((q + rho k : ℕ) : ℤ) := by intro k; omega
  let r : ℕ → Book.Ch03.CubeSolution (originCube d (q : ℤ)) a :=
    fun k => finiteAffineGradientResidual a (hqk k) (u k) (e k)
  let w : ℕ → H1Function (localGradientCube d q) := fun k =>
    finiteAffineSolutionInnerH1 a (q : ℤ) ((q + rho k : ℕ) : ℤ)
      (hqk k) (e k)
  let v : ℕ → H1Function (localGradientCube d q) := fun k =>
    (finiteCubeSolutionRestriction a (hqk k) (u k)).toH1
  have hrClass : ∀ k, (r k).toH1.gradToHilbertVectorL2 =
      (v k).gradToHilbertVectorL2 - (w k).gradToHilbertVectorL2 := by
    intro k
    apply MeasureTheory.Lp.ext
    filter_upwards
      [(r k).toH1.coeFn_gradToHilbertVectorL2,
       (v k).coeFn_gradToHilbertVectorL2,
       (w k).coeFn_gradToHilbertVectorL2,
       MeasureTheory.Lp.coeFn_sub
        (v k).gradToHilbertVectorL2 (w k).gradToHilbertVectorL2]
      with x hr hv hw hsub
    change (r k).toH1.gradToHilbertVectorL2 x =
      ((v k).gradToHilbertVectorL2 - (w k).gradToHilbertVectorL2) x
    rw [hr, hsub, Pi.sub_apply, hv, hw]
    simp only [r, finiteAffineGradientResidual_grad, v, w]
    rfl
  have hrZero : Tendsto (fun k => (r k).toH1.gradToHilbertVectorL2)
      atTop (nhds 0) := by
    simpa only [r] using
      tendsto_finiteAffineGradientResidual_localGradient_zero
        a q (fun k => ((q + rho k : ℕ) : ℤ)) hqk u e hresidual
  have hwLimit :=
    finiteAffineSolutionInnerGradient_varyingSlope_tendsto_jointLocalGradient_along
      a hCauchy q rho hrho e eLim he
  have hwLimit' : Tendsto (fun k => (w k).gradToHilbertVectorL2) atTop
      (nhds ((jointAffineFullGradientLinearMap a hCauchy q) eLim)) := by
    simpa only [w, jointAffineFullGradientLinearMap] using! hwLimit
  -- Restate the residual's gradient class and its vanishing at the local
  -- gradient exhaustion's own carrier, matching `v` and `w`, so the sum
  -- below stays on a single presentation of the underlying cube.
  let r' : ℕ → HilbertVectorL2 (localGradientCube d q) :=
    fun k => (r k).toH1.gradToHilbertVectorL2
  have hrClass' : ∀ k, r' k = (v k).gradToHilbertVectorL2 - (w k).gradToHilbertVectorL2 :=
    hrClass
  have hrZero' : Tendsto r' atTop (nhds (0 : HilbertVectorL2 (localGradientCube d q))) :=
    hrZero
  have hvLimit := hrZero'.add hwLimit'
  have hvLimit' : Tendsto (fun k => (v k).gradToHilbertVectorL2) atTop
      (nhds ((jointAffineFullGradientLinearMap a hCauchy q) eLim)) := by
    simpa only [zero_add] using
      hvLimit.congr' (Eventually.of_forall fun k => add_eq_of_eq_sub (hrClass' k))
  have hvConst : ∀ k, (v k).gradToHilbertVectorL2 =
      (v 0).gradToHilbertVectorL2 := by
    intro k
    apply MeasureTheory.Lp.ext
    filter_upwards
      [(v k).coeFn_gradToHilbertVectorL2,
       (v 0).coeFn_gradToHilbertVectorL2]
      with x hv hu
    rw [hv, hu]
    change HilbertVec.ofVec ((u k).toH1.grad x) =
      HilbertVec.ofVec ((u 0).toH1.grad x)
    rw [huGrad k, huGrad 0]
  have hconst : Tendsto (fun k => (v k).gradToHilbertVectorL2) atTop
      (nhds ((v 0).gradToHilbertVectorL2)) := by
    simpa only [hvConst] using
      (tendsto_const_nhds : Tendsto
        (fun _k : ℕ => (v 0).gradToHilbertVectorL2) atTop
          (nhds ((v 0).gradToHilbertVectorL2)))
  simpa only [v] using! tendsto_nhds_unique hconst hvLimit'

end

end HighContrast
end HCPolySupport
