/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Lipschitz.Gradient
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Coordinate derivatives of smooth functions of a Lipschitz gradient

Generic first-order composition and compact-local weak derivative data,
used by Letwin arXiv:2607.24164v1 Lemma 2.2 infrastructure. No Monge–Ampère
equation, inverse Hessian or integration-by-parts premise is required.
-/

@[expose] public section
section

section MongeAmpereExponentDerivative

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

private lemma gradient_fderiv_coordinate {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x)
    (j k : Fin n) :
    fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
      hessianMatrix u x j k := by
  have hm :
      LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (fderiv ℝ (gradient u) x).toLinearMap =
        hessianMatrix u x := by
    rw [← hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hx,
      Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have hentry :
      fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
        hessianMatrix u x k j := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k j) hm
    simp only [LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis] at he
    exact he
  calc
    fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
        hessianMatrix u x k j := hentry
    _ = hessianMatrix u x j k := by
      simpa only [star_trivial] using
        (hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx).apply j k

/-- AE coordinate chain derivative of the Monge-Ampere right-hand exponent
for Letwin (2.2), with C1 u and Lipschitz gradient, without a C2 premise. -/
theorem ae_fderiv_mongeAmpere_exponent {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          ∑ k, hessianMatrix u x j k *
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
  filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
  intro j
  have hux : DifferentiableAt ℝ u x := hu.differentiable one_ne_zero x
  have hVx : DifferentiableAt ℝ V (gradient u x) :=
    hV.differentiable one_ne_zero (gradient u x)
  have hexp :
      HasFDerivAt (fun y => -u y + V (gradient u y))
        (-fderiv ℝ u x +
          (fderiv ℝ V (gradient u x)).comp (fderiv ℝ (gradient u) x)) x :=
    hux.hasFDerivAt.neg.add (hVx.hasFDerivAt.comp x hx.hasFDerivAt)
  have heval :
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          fderiv ℝ V (gradient u x)
            (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    exact congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      hexp.fderiv
  have hchain :
      fderiv ℝ V (gradient u x)
          (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        ∑ k, hessianMatrix u x j k *
          fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    calc
      fderiv ℝ V (gradient u x)
          (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
          ⟪gradient V (gradient u x),
            fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
        inner_gradient_left.symm
      _ = ∑ k, ⟪gradient V (gradient u x) k,
          fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k⟫ :=
        PiLp.inner_apply _ _
      _ = ∑ k, hessianMatrix u x j k *
          fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
        apply Finset.sum_congr rfl
        intro k _
        have hVk :
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) =
              gradient V (gradient u x) k := by
          calc
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) =
                ⟪gradient V (gradient u x),
                  EuclideanSpace.basisFun (Fin n) ℝ k⟫ :=
              inner_gradient_left.symm
            _ = gradient V (gradient u x) k :=
              EuclideanSpace.inner_basisFun_real
                (Fin n) (gradient V (gradient u x)) k
        calc
          ⟪gradient V (gradient u x) k,
              fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k⟫ =
              gradient V (gradient u x) k *
                fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k :=
            Real.inner_apply _ _
          _ = gradient V (gradient u x) k * hessianMatrix u x j k :=
            congrArg (fun t : ℝ => gradient V (gradient u x) k * t)
              (gradient_fderiv_coordinate hu hx j k)
          _ = hessianMatrix u x j k * gradient V (gradient u x) k :=
            mul_comm _ _
          _ = hessianMatrix u x j k *
              fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
            congrArg (fun t : ℝ => hessianMatrix u x j k * t) hVk.symm
  exact heval.trans
    (congrArg
      (fun t : ℝ => -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) + t)
      hchain)

end FunctionalInequalities.Analysis

end MongeAmpereExponentDerivative

section WeakCoordinateComposition
open MeasureTheory Set
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-- Closed composition of the existing negative-exponent result with the
original Lipschitz potential. A local helper, not a new public interface. -/
private theorem exists_lipschitz_comp_gradient {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hULip : LipschitzWith L u) (hGradLip : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ C : NNReal, LipschitzWith C (fun x => V (gradient u x)) := by
  obtain ⟨LF, hNegCompLip⟩ :=
    exists_lipschitzWith_neg_add_comp_gradient hULip hGradLip hV
  have hSum := hNegCompLip.add hULip
  change LipschitzWith (LF + L) (fun x => (-u x + V (gradient u x)) + u x) at hSum
  have hCancel : (fun x => (-u x + V (gradient u x)) + u x) =
      (fun x => V (gradient u x)) := by
    funext x
    ring
  rw [hCancel] at hSum
  exact ⟨LF + L, hSum⟩

/-- The scalar derivative bound and compact-local L2 calculation for a coordinate derivative
of an arbitrary Lipschitz scalar f. -/
private theorem memLp_coordinate_fderiv_of_lipschitz {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : NNReal}
    (hLip : LipschitzWith C f) (j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ j))
      2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
    isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hMeas : Measurable (fun x => fderiv ℝ f x (e j)) :=
    (show Continuous (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A (e j)) from
      continuous_id.clm_apply continuous_const).measurable.comp (measurable_fderiv ℝ f)
  have hBound (x : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ f x (e j)‖ ≤ (C : ℝ) := by
    have hEval := (fderiv ℝ f x).le_opNorm (e j)
    rw [e.norm_eq_one j, mul_one] at hEval
    exact hEval.trans (norm_fderiv_le_of_lipschitz ℝ hLip)
  exact MemLp.of_bound hMeas.aestronglyMeasurable (C : ℝ)
    (Filter.Eventually.of_forall hBound)

/-- Actual weak derivative of a smooth coordinate derivative composed with a
C1 potential's Lipschitz gradient. Supporting component for weak Letwin (2.6). -/
theorem exists_lipschitzWith_weak_fderiv_comp_gradient {n : ℕ}
    {u W : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hu : ContDiff ℝ 1 u) (hULip : LipschitzWith L u)
    (hGradLip : LipschitzWith G (gradient u)) (hW : ContDiff ℝ 2 W)
    (a : Fin n) :
    ∃ C : NNReal,
      LipschitzWith C (fun x => fderiv ℝ W (gradient u x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)) ∧
      ∀ j : Fin n,
        HasWeakDerivAlong
          (fun x => fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a))
          (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
          (EuclideanSpace.basisFun (Fin n) ℝ j) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp
            (fun x => ∑ b : Fin n, hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  let V : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hV : ContDiff ℝ 1 V := by
    change ContDiff ℝ 1
      (fun z => fderiv ℝ W z (EuclideanSpace.basisFun (Fin n) ℝ a))
    exact (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  obtain ⟨C, hCompLip⟩ :=
    exists_lipschitz_comp_gradient hULip hGradLip hV
  have hCoord (z : EuclideanSpace ℝ (Fin n)) (b : Fin n) :
      fderiv ℝ V z (EuclideanSpace.basisFun (Fin n) ℝ b) =
        hessianMatrix W z b a := by
    change fderiv ℝ
        (fun y => fderiv ℝ W y (EuclideanSpace.basisFun (Fin n) ℝ a)) z
        (EuclideanSpace.basisFun (Fin n) ℝ b) =
      bilinearIteratedFDerivTwo ℝ W z
        (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
    exact
      (FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply
        hW z (EuclideanSpace.basisFun (Fin n) ℝ b)
        (EuclideanSpace.basisFun (Fin n) ℝ a)).symm
  refine ⟨C, ?_, ?_⟩
  · simpa only [V] using hCompLip
  · intro j
    constructor
    · change HasWeakDerivAlong
        (fun x => V (gradient u x))
        (fun x => ∑ b : Fin n,
          hessianMatrix u x j b * hessianMatrix W (gradient u x) b a)
        (EuclideanSpace.basisFun (Fin n) ℝ j)
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              hessianMatrix u x j b * hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, hessianMatrix u x j b *
                hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hWeakClassical :
          HasWeakDerivAlong
            (fun x => V (gradient u x))
            (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j))
            (EuclideanSpace.basisFun (Fin n) ℝ j) :=
        hasWeakDerivAlong_of_lipschitz hCompLip
          (EuclideanSpace.basisFun (Fin n) ℝ j)
      exact hWeakClassical.congr_ae
        (Filter.Eventually.of_forall (fun x => rfl)) hAe
    · intro S hS
      have hClassicalL2 :=
        memLp_coordinate_fderiv_of_lipschitz hCompLip j S hS
      have hExp :=
        FunctionalInequalities.Analysis.ae_fderiv_mongeAmpere_exponent
          hu hGradLip hV
      have hDiffComp :
          ∀ᵐ x : EuclideanSpace ℝ (Fin n)
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            DifferentiableAt ℝ (fun y => V (gradient u y)) x :=
        hCompLip.ae_differentiableAt (μ := volume)
      have hAe :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n)))]
            (fun x => ∑ b : Fin n,
              hessianMatrix u x j b * hessianMatrix W (gradient u x) b a) := by
        filter_upwards [hExp, hDiffComp] with x hxExp hxComp
        have hux : DifferentiableAt ℝ u x :=
          hu.differentiable one_ne_zero x
        have hsum :=
          hux.hasFDerivAt.neg.add hxComp.hasFDerivAt
        have hEval := congrArg
          (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
            A (EuclideanSpace.basisFun (Fin n) ℝ j))
          hsum.fderiv
        have hfun :
            (-u + (fun y => V (gradient u y))) =
              (fun y => -u y + V (gradient u y)) := by
          funext y
          rfl
        rw [hfun] at hEval
        have heval :
            fderiv ℝ (fun y => -u y + V (gradient u y)) x
                (EuclideanSpace.basisFun (Fin n) ℝ j) =
              -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
                fderiv ℝ (fun y => V (gradient u y)) x
                  (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          simpa only [neg_apply, add_apply] using hEval
        have hSum :
            (∑ b : Fin n, hessianMatrix u x j b *
              fderiv ℝ V (gradient u x)
                (EuclideanSpace.basisFun (Fin n) ℝ b)) =
              ∑ b : Fin n, hessianMatrix u x j b *
                hessianMatrix W (gradient u x) b a := by
          apply Finset.sum_congr rfl
          intro b _
          rw [hCoord]
        have hxExp' := hxExp j
        rw [hSum] at hxExp'
        linarith [heval, hxExp']
      have hRestricted :
          (fun x => fderiv ℝ (fun y => V (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᵐ[
                (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S]
            (fun x => ∑ b : Fin n,
              hessianMatrix u x j b * hessianMatrix W (gradient u x) b a) :=
        MeasureTheory.ae_restrict_of_ae hAe
      exact (MeasureTheory.memLp_congr_ae hRestricted).mp hClassicalL2

end FunctionalInequalities.Analysis
end WeakCoordinateComposition
