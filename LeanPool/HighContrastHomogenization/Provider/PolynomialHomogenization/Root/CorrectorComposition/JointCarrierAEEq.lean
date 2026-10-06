/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.JointAEEqTransfer

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.JointCarrierAEEq

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The joint local limit depends only on the a.e. coefficient family

`HCPoly.Provider.PolynomialHomogenization.Root.CorrectorDecay.JointAEEqTransfer`
proves that two joint finite-corrector limits for
a.e.-equal coefficient families have identical projective **gradient**
components, and says explicitly that "no equality of value representatives or
of the bundled families is asserted".

This module supplies the value half and therefore the equality of the bundled
carriers.  The analytic content is one line of Poincaré: the two finite affine
corrections at a given generation are `H¹₀` functions on the same cube whose
weak gradients agree almost everywhere, so their difference is an `H¹₀`
function with vanishing gradient class, hence vanishes.

The consequence used downstream is `jointLocalLimit_eq_of_aeeq`: the canonical
joint local limit is **literally the same carrier family** for a.e.-equal
coefficient families.  That is what lets the root's corrector-family hypotheses be
discharged with the certificate's own exact-gauge reference family in place of
the (arbitrarily selected) datum family.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-! ## The value half -/

/-- **Zero-trace corrections with a.e.-equal gradients have equal `L²`
classes.**  The difference is an `H¹₀` function on the cube whose gradient
class vanishes; the zero-trace Poincaré inequality kills it. -/
theorem finiteAffineCorrection_toScalarL2_eq_of_aeeq [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b) (m : ℤ) (e : Vec d) :
    (finiteAffineCorrection a m e).toH1Function.toScalarL2 =
      (finiteAffineCorrection b m e).toH1Function.toScalarL2 := by
  have hdomain : IsOpenBoundedConvexDomain
      (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) := by
    simpa only [Book.Ch02.cubeDomain_coe] using
      isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have hP := H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain
    hdomain
  set w : H10Function (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)) :=
    finiteAffineCorrection a m e - finiteAffineCorrection b m e with hwdef
  have hwH1 : w.toH1Function =
      (finiteAffineCorrection a m e).toH1Function -
        (finiteAffineCorrection b m e).toH1Function := rfl
  have hgradzero : w.toH1Function.gradToVectorL2 = 0 := by
    have hzero : (0 : VectorL2 (Book.Ch02.cubeDomain (originCube d m) :
        Set (Vec d))) =ᵐ[volumeMeasureOn
          (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
        fun _ ↦ (0 : Vec d) := Lp.coeFn_zero _ _ _
    apply Lp.ext
    filter_upwards [H1Function.coeFn_gradToVectorL2 w.toH1Function, hzero,
      finiteAffineCorrection_grad_ae_of_aeeq hab m e] with x hgrad h0 haeq
    rw [hgrad, h0, hwH1, H1Function.sub_grad]
    show (finiteAffineCorrection a m e).toH1Function.grad x -
      (finiteAffineCorrection b m e).toH1Function.grad x = 0
    rw [haeq, sub_self]
  have hzero :=
    H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant hP w hgradzero
  have hcw := H1Function.coeFn_toScalarL2 w.toH1Function
  rw [hzero] at hcw
  have hz0 : (0 : ScalarL2 (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d)))
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d m) : Set (Vec d))]
      fun _ ↦ (0 : ℝ) := Lp.coeFn_zero _ _ _
  apply Lp.ext
  filter_upwards [H1Function.coeFn_toScalarL2
      (finiteAffineCorrection a m e).toH1Function,
    H1Function.coeFn_toScalarL2 (finiteAffineCorrection b m e).toH1Function,
    hcw, hz0] with x ha hb hw h0
  rw [ha, hb]
  have hwx : w.toH1Function.toFun x = 0 := by rw [← hw, h0]
  rw [hwH1] at hwx
  simp only [H1Function.sub_toFun] at hwx
  exact sub_eq_zero.mp hwx

/-- The local sequence's value classes agree. -/
theorem localSequence_toScalarL2_eq_of_aeeq [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b) (e : Vec d) (q : ℕ) :
    (finiteAffineCorrectionLocalSequence a e q).toScalarL2 =
      (finiteAffineCorrectionLocalSequence b e q).toScalarL2 := by
  apply Lp.ext
  have hval := finiteAffineCorrection_toScalarL2_eq_of_aeeq hab (q : ℤ) e
  have hA := H1Function.coeFn_toScalarL2
    (finiteAffineCorrection a (q : ℤ) e).toH1Function
  have hB := H1Function.coeFn_toScalarL2
    (finiteAffineCorrection b (q : ℤ) e).toH1Function
  have hfun : (finiteAffineCorrection a (q : ℤ) e).toH1Function.toFun
      =ᵐ[volumeMeasureOn
        (Book.Ch02.cubeDomain (originCube d (q : ℤ)) : Set (Vec d))]
      (finiteAffineCorrection b (q : ℤ) e).toH1Function.toFun := by
    filter_upwards [hA, hB] with x hxa hxb
    rw [← hxa, ← hxb, hval]
  filter_upwards [(finiteAffineCorrectionLocalSequence a e q).coeFn_toScalarL2,
    (finiteAffineCorrectionLocalSequence b e q).coeFn_toScalarL2, hfun]
    with x ha hb hx
  rw [ha, hb]
  exact hx

/-- Both components of every normalized local pair agree. -/
theorem normalizedLocalPair_eq_of_aeeq [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b) (e : Vec d) (n k : ℕ) :
    normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) n k =
      normalizedLocalPair (finiteAffineCorrectionLocalSequence b e) n k := by
  refine Prod.ext ?_ (normalizedLocalPair_gradient_eq_of_aeeq hab e n k)
  rw [normalizedLocalPair_value_eq, normalizedLocalPair_value_eq,
    localSequence_toScalarL2_eq_of_aeeq hab e (n + k)]

/-! ## The Cauchy condition -/

/-- Local Cauchyness transfers along an a.e. equality of families. -/
theorem finiteAffineCorrectionLocalCauchy_of_aeeq [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (ha : FiniteAffineCorrectionLocalCauchy a) :
    FiniteAffineCorrectionLocalCauchy b := by
  intro e n
  have hfun : (fun k ↦ (normalizedLocalH1
        (finiteAffineCorrectionLocalSequence b e) n k).gradToHilbertVectorL2) =
      fun k ↦ (normalizedLocalH1
        (finiteAffineCorrectionLocalSequence a e) n k).gradToHilbertVectorL2 := by
    funext k
    exact (normalizedLocalPair_gradient_eq_of_aeeq hab e n k).symm
  rw [hfun]
  exact ha e n

/-! ## The carrier -/

/-- **The canonical joint local limit is the same carrier family for
a.e.-equal coefficient families.** -/
theorem jointLocalLimit_eq_of_aeeq [NeZero d]
    {a b : Book.Ch02.TriadicCoeffFamily d}
    (hab : Book.Ch02.TriadicCoeffFamily.AEEq a b)
    (ha : FiniteAffineCorrectionLocalCauchy a)
    (hb : FiniteAffineCorrectionLocalCauchy b) :
    finiteAffineCorrectionJointLocalLimit a ha =
      finiteAffineCorrectionJointLocalLimit b hb := by
  have hpair : ∀ e : Vec d,
      normalizedLocalPair (finiteAffineCorrectionLocalSequence b e) =
        normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) := by
    intro e
    funext n k
    exact (normalizedLocalPair_eq_of_aeeq hab e n k).symm
  have hlimit : IsFiniteAffineCorrectionJointLocalLimit b
      (finiteAffineCorrectionJointLocalLimit a ha) := by
    intro e n
    have h := finiteAffineCorrectionJointLocalLimit_isLimit a ha e n
    rw [hpair e]
    exact h
  exact (isFiniteAffineCorrectionJointLocalLimit_iff_eq b hb _).mp hlimit

end

end CorrectorComposition
end HighContrast
end HCPolySupport
