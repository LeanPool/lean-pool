/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleGlobalSlope

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleAdditiveConstant

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Recovering the additive constant

The local analytic core of the last Liouville step: an `H¹` function with
zero gradient on a centered cube is almost everywhere its cube average.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

/-- Zero weak gradient on a centered cube forces an `H¹` representative to
equal its integral average almost everywhere. -/
theorem H1Function.ae_eq_integralAverage_of_gradToVectorL2_eq_zero
    {d : ℕ} (q : ℕ) (w : H1Function (localGradientCube d q))
    (hgrad : w.gradToVectorL2 = 0) :
    w.toFun =ᵐ[volumeMeasureOn (localGradientCube d q)]
      fun _ => integralAverage (localGradientCube d q) w := by
  let C := originCubeMeanZeroH1CoerciveEstimate d (q : ℤ)
  have hbound : ‖w.subAverage.toScalarL2‖ ≤ C.constantValue * ‖w.gradToVectorL2‖ := by
    change (w.toMeanZero).valueL2Norm ≤ C.constantValue * ‖w.gradToVectorL2‖
    exact C.bound_subAverage w
  rw [hgrad, norm_zero, mul_zero] at hbound
  have hvalueZero : w.subAverage.toScalarL2 = 0 :=
    norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  have hsubZero : w.subAverage.toFun
      =ᵐ[volumeMeasureOn (localGradientCube d q)] fun _ => 0 := by
    filter_upwards
      [w.subAverage.coeFn_toScalarL2,
       MeasureTheory.Lp.coeFn_zero (E := ℝ)
        (p := (2 : ℝ≥0∞)) (volumeMeasureOn (localGradientCube d q))]
      with x hw hz
    rw [← hw, hvalueZero]
    exact hz
  filter_upwards [hsubZero] with x hx
  change w.toFun x - integralAverage (localGradientCube d q) w = 0 at hx
  linarith only [hx]

/-- Two scalar constants which agree almost everywhere on a centered cube
are equal. -/
theorem eq_of_const_ae_eq_const_localGradientCube
    {d : ℕ} (q : ℕ) {c c' : ℝ}
    (h : (fun _ : Vec d => c) =ᵐ[volumeMeasureOn (localGradientCube d q)]
      fun _ => c') :
    c = c' := by
  have hvolReal : 0 < (volume (localGradientCube d q)).toReal := by
    simpa only [localGradientCube, volume_openCubeSet_toReal] using
      cubeVolume_pos (originCube d (q : ℤ))
  have hmeasure : (volumeMeasureOn (localGradientCube d q)) Set.univ ≠ 0 := by
    rw [volumeMeasureOn, Measure.restrict_apply_univ]
    intro hzero
    rw [hzero, ENNReal.toReal_zero] at hvolReal
    exact lt_irrefl 0 hvolReal
  have h' : ∀ᵐ x ∂(volumeMeasureOn (localGradientCube d q)).restrict Set.univ,
      (fun _ : Vec d => c) x = (fun _ => c') x := by
    simpa only [Measure.restrict_univ] using! h
  obtain ⟨x, _hx, hxc⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (s := Set.univ) hmeasure h'
  exact hxc

/-- Local almost-everywhere identities on every centered cube assemble to a
global almost-everywhere identity. -/
theorem ae_eq_volume_of_forall_localGradientCube_ae_eq
    {d : ℕ} {f g : Vec d → ℝ}
    (h : ∀ q : ℕ, f =ᵐ[volumeMeasureOn (localGradientCube d q)] g) :
    f =ᵐ[volume] g := by
  have hall : ∀ᵐ x ∂volume, ∀ q : ℕ,
      x ∈ localGradientCube d q → f x = g x := by
    apply ae_all_iff.2
    intro q
    exact (ae_restrict_iff' (isOpen_openCubeSet
      (originCube d (q : ℤ))).measurableSet).mp (h q)
  filter_upwards [hall] with x hx
  have hxUnion : x ∈ ⋃ q, localGradientCube d q := by
    rw [iUnion_localGradientCube]
    trivial
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxUnion
  exact hx q hxq

private theorem inner_le_index_add_four (q : ℕ) :
    (q : ℤ) ≤ ((q + 4 : ℕ) : ℤ) - 2 := by
  omega

private theorem gradToHilbertVectorL2_sub_additive
    {d : ℕ} {U : Set (Vec d)} (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  rw [sub_eq_add_neg, H1Function.gradToHilbertVectorL2_add]
  have hneg := H1Function.gradToHilbertVectorL2_smul (-1 : ℝ) v
  rw [show (-v : H1Function U) = (-1 : ℝ) • v by rfl, hneg]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

private theorem finiteAffineBoundaryH1_gradClass_eq_constantGradient
    {d : ℕ} (q : ℕ) (e : Vec d) :
    (show H1Function (localGradientCube d q) from
        finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2 =
      (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) := by
  let b : H1Function (localGradientCube d q) := finiteAffineBoundaryH1 (q : ℤ) e
  change b.gradToHilbertVectorL2 = constantGradientOnOriginCube e (q : ℤ)
  have hbgrad : b.grad = fun _ => e := by
    simpa only [b] using finiteAffineBoundaryH1_grad (q : ℤ) e
  have hmem : MemVectorL2 (localGradientCube d q) (fun _ => e) := by
    simpa only [localGradientCube] using
      (MeasureTheory.memLp_const
        (μ := volumeMeasureOn (openCubeSet (originCube d (q : ℤ))))
        (p := (2 : ENNReal)) (c := e))
  apply MeasureTheory.Lp.ext
  filter_upwards
    [b.coeFn_gradToHilbertVectorL2,
     coeFn_toHilbertVectorL2OfVecField hmem]
    with x hboundary hconstant
  rw [hboundary, hbgrad]
  exact hconstant.symm

/-- Equality of the Liouville gradient with one canonical joint-corrector
gradient determines the Liouville value representative up to one global
additive constant. -/
theorem exists_additiveConstant_of_common_jointSlope
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d} {n : ℤ}
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (u : ∀ p : ℕ,
      Book.Ch03.CubeSolution (originCube d ((p : ℤ) - 2)) a)
    (v : Vec d → ℝ) (huFun : ∀ p, (u p).toH1.toFun = v)
    (e : Vec d)
    (he : ∀ q : ℕ, n.toNat ≤ q →
      (finiteCubeSolutionRestriction a (by omega) (u (q + 4))).toH1.gradToHilbertVectorL2 =
        (jointAffineFullGradientLinearMap a hCauchy q) e) :
    ∃ c : ℝ, v =ᵐ[volume] fun x =>
      vecDot e x +
        (finiteAffineCorrectionJointLocalLimit a hCauchy e).globalValueRepresentative x + c := by
  let z : NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit a hCauchy e
  let f : Vec d → ℝ := fun x =>
    v x - (vecDot e x + z.globalValueRepresentative x)
  let U : ∀ q : ℕ, H1Function (localGradientCube d q) := fun q => by
    simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
      (finiteCubeSolutionRestriction a (inner_le_index_add_four q)
        (u (q + 4))).toH1
  have hlocal : ∀ q : ℕ, n.toNat ≤ q →
      f =ᵐ[volumeMeasureOn (localGradientCube d q)] fun _ =>
        integralAverage (localGradientCube d q)
          (((U q) -
              finiteAffineCorrectionJointLocalH1 a hCauchy e q :
            H1Function (localGradientCube d q)).toFun) := by
    intro q hnq
    let uq : H1Function (localGradientCube d q) := U q
    let target : H1Function (localGradientCube d q) :=
      finiteAffineCorrectionJointLocalH1 a hCauchy e q
    let w : H1Function (localGradientCube d q) :=
      uq - target
    have htargetGrad : target.gradToHilbertVectorL2 =
        (jointAffineFullGradientLinearMap a hCauchy q) e := by
      calc
        target.gradToHilbertVectorL2 =
            (show LocalGradientL2 d q from
                (finiteAffineBoundaryH1 (q : ℤ) e).gradToHilbertVectorL2) +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q :=
          finiteAffineCorrectionJointLocalH1_gradToHilbertVectorL2 a hCauchy e q
        _ = (show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
              (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q := by
          exact congrArg
            (fun g : LocalGradientL2 d q =>
              g + (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)
            (finiteAffineBoundaryH1_gradClass_eq_constantGradient q e)
        _ = (jointAffineFullGradientLinearMap a hCauchy q) e := rfl
    have hgradHilbert : w.gradToHilbertVectorL2 = 0 := by
      dsimp only [w]
      rw [gradToHilbertVectorL2_sub_additive]
      have heq := he q hnq
      change uq.gradToHilbertVectorL2 =
        (jointAffineFullGradientLinearMap a hCauchy q) e at heq
      rw [heq, htargetGrad, sub_self]
    have hgradVector : w.gradToVectorL2 = 0 := by
      have htransport := congrArg
        (hilbertVectorL2ToVectorL2 (U := localGradientCube d q)) hgradHilbert
      simpa [H1Function.gradToHilbertVectorL2,
        hilbertVectorL2ToVectorL2_toHilbertVectorL2] using! htransport
    have hw :=
      HCPolySupport.HighContrast.H1Function.ae_eq_integralAverage_of_gradToVectorL2_eq_zero
        q w hgradVector
    have hvalue : f =ᵐ[volumeMeasureOn (localGradientCube d q)] w.toFun := by
      have hz := z.globalValueRepresentative_ae_eq_localH1Function q
      have huqFun : uq.toFun = v := by
        simpa only [uq, U, id_eq, finiteCubeSolutionRestriction_toFun] using!
          huFun (q + 4)
      have htargetFun : target.toFun = fun x =>
          vecDot e x + z.localH1Function q x := by
        funext x
        simp only [target, finiteAffineCorrectionJointLocalH1,
          H1Function.add_toFun]
        change (finiteAffineBoundaryH1 (q : ℤ) e).toFun x +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).localH1Function q x =
          vecDot e x + z.localH1Function q x
        rw [finiteAffineBoundaryH1_toFun]
      filter_upwards [hz] with x hx
      have huqx := congrFun huqFun x
      have htargetx := congrFun htargetFun x
      dsimp only [f, w]
      rw [H1Function.sub_toFun]
      change v x - (vecDot e x + z.globalValueRepresentative x) =
        uq.toFun x - target.toFun x
      rw [huqx, htargetx, hx]
    change f =ᵐ[volumeMeasureOn (localGradientCube d q)] fun _ =>
      integralAverage (localGradientCube d q) w.toFun
    exact hvalue.trans hw
  let q₀ : ℕ := n.toNat
  let c : ℝ := integralAverage (localGradientCube d q₀)
    (((U q₀) -
        finiteAffineCorrectionJointLocalH1 a hCauchy e q₀ :
      H1Function (localGradientCube d q₀)).toFun)
  have hlocalCommon : ∀ q : ℕ, q₀ ≤ q →
      f =ᵐ[volumeMeasureOn (localGradientCube d q)] fun _ => c := by
    intro q hq
    let cq : ℝ := integralAverage (localGradientCube d q)
      (((U q) -
          finiteAffineCorrectionJointLocalH1 a hCauchy e q :
        H1Function (localGradientCube d q)).toFun)
    have hqLocal : f =ᵐ[volumeMeasureOn (localGradientCube d q)] fun _ => cq :=
      hlocal q hq
    have hmu : volumeMeasureOn (localGradientCube d q₀) ≤
        volumeMeasureOn (localGradientCube d q) :=
      Measure.restrict_mono_set volume (localGradientCube_mono hq)
    have hconst : (fun _ : Vec d => cq)
        =ᵐ[volumeMeasureOn (localGradientCube d q₀)] fun _ => c :=
      ((hqLocal.filter_mono (ae_mono hmu)).symm.trans
        (by simpa only [q₀, c] using hlocal q₀ (le_refl q₀)))
    have hcq : cq = c := eq_of_const_ae_eq_const_localGradientCube q₀ hconst
    simpa only [hcq] using hqLocal
  have hallLocal : ∀ r : ℕ,
      f =ᵐ[volumeMeasureOn (localGradientCube d r)] fun _ => c := by
    intro r
    let q := max q₀ r
    have hrq : r ≤ q := le_max_right _ _
    have hq₀q : q₀ ≤ q := le_max_left _ _
    exact (hlocalCommon q hq₀q).filter_mono
      (ae_mono (Measure.restrict_mono_set volume (localGradientCube_mono hrq)))
  refine ⟨c, ?_⟩
  have hglobal : f =ᵐ[volume] fun _ => c :=
    ae_eq_volume_of_forall_localGradientCube_ae_eq hallLocal
  filter_upwards [hglobal] with x hx
  dsimp only [f] at hx
  linarith only [hx]

end

end HighContrast
end HCPolySupport
