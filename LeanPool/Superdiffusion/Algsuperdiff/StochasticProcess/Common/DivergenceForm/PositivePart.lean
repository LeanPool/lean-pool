/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ZeroTraceSobolev

/-!
# PositivePart

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Positive-part truncation on the zero-trace Sobolev carrier

This file establishes positive-part truncation after subtracting a nonnegative
constant on `ZeroTraceSobolev`, including its almost-everywhere value and
gradient characterizations.
-/

namespace DivergenceFormProcess.Form.ZeroTraceSobolev

open HCPolySupport MeasureTheory

variable {d : ℕ} {U : Set (Vec d)}

/-- Positive-part truncation after subtracting a nonnegative constant exists
uniquely in `ZeroTraceSobolev`, subject to the stated almost-everywhere value
and gradient characterizations. -/
theorem existsUnique_positivePartSubConst [NeZero d]
    (hU : IsOpenBoundedConvexDomain U) (u : ZeroTraceSobolev U) (c : ℝ)
    (hc : 0 ≤ c) :
    ∃! v : ZeroTraceSobolev U,
      (∀ᵐ x ∂(volumeMeasureOn U),
        toL2 v x = max (toL2 u x - c) 0) ∧
      (∀ᵐ x ∂(volumeMeasureOn U),
        gradient v x = {y | c < toL2 u y}.indicator (gradient u) x) := by
  obtain ⟨w, hwvalue, hwgradient⟩ := exists_h10Function hU u
  have hmatch : MemH10 U (fun x => w.toH1Function.toFun x - (0 : ℝ)) := by
    refine ⟨w, ?_⟩
    funext x
    simp only [sub_zero]
  obtain ⟨ψ, hψfun⟩ :=
    memH10_max_sub_matched hU w.toH1Function (0 : H1Function U) hmatch c
  obtain ⟨q, hqfun, hqgrad⟩ := exists_h1_max_sub_const hU w.toH1Function c
  have hψtarget :
      ψ.toH1Function.toFun = fun x => max (w.toH1Function.toFun x - c) 0 := by
    rw [hψfun]
    funext x
    simp only [H1Function.zero_toFun, Pi.zero_apply, zero_sub,
      max_eq_right (neg_nonpos.mpr hc), sub_zero]
  have hψq : ψ.toH1Function.toFun = q.toFun := by
    rw [hψtarget, hqfun]
  have hψqgrad : ψ.toH1Function.grad =ᵐ[volumeMeasureOn U] q.grad := by
    have hloc : ∀ (z : H1Function U) (i : Fin d),
        LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((z.gradMemL2 i).locallyIntegrable (by norm_num))
    have hcoord : ∀ i : Fin d,
        (fun x => ψ.toH1Function.grad x i) =ᵐ[volumeMeasureOn U]
          fun x => q.grad x i := by
      intro i
      refine HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc _ i) (hloc _ i) ?_
        (q.hasWeakGradient i)
      have hweak := ψ.toH1Function.hasWeakGradient i
      rw [hψq] at hweak
      exact hweak
    filter_upwards [(ae_all_iff).2 hcoord] with x hx
    funext i
    exact hx i
  let v : ZeroTraceSobolev U := ofH10Function ψ
  have hwvalue_ae :
      w.toH1Function.toFun =ᵐ[volumeMeasureOn U] fun x => toL2 u x := by
    filter_upwards [w.toH1Function.coeFn_toScalarL2] with x hx
    exact hx.symm.trans (congrArg (fun f : ScalarL2 U => f x) hwvalue)
  have hwgradient_ae :
      (fun x => hilbertifyVecField w.toH1Function.grad x) =ᵐ[volumeMeasureOn U]
        fun x => gradient u x := by
    filter_upwards [w.toH1Function.coeFn_gradToHilbertVectorL2] with x hx
    exact hx.symm.trans (congrArg (fun f : HilbertVectorL2 U => f x) hwgradient)
  have hvvalue : ∀ᵐ x ∂(volumeMeasureOn U),
      toL2 v x = max (toL2 u x - c) 0 := by
    filter_upwards [ψ.toH1Function.coeFn_toScalarL2, hwvalue_ae] with x hψx hwx
    calc
      toL2 v x = ψ.toH1Function.toScalarL2 x := rfl
      _ = ψ.toH1Function.toFun x := hψx
      _ = max (w.toH1Function.toFun x - c) 0 := congrFun hψtarget x
      _ = max (toL2 u x - c) 0 := by rw [hwx]
  have hvgradient : ∀ᵐ x ∂(volumeMeasureOn U),
      gradient v x = {y | c < toL2 u y}.indicator (gradient u) x := by
    filter_upwards [ψ.toH1Function.coeFn_gradToHilbertVectorL2,
      hψqgrad, hqgrad, hwvalue_ae, hwgradient_ae] with x hψx hψqx hqx hwx hgx
    change ψ.toH1Function.gradToHilbertVectorL2 x = _
    rw [hψx]
    have hraw : ψ.toH1Function.grad x =
        {y | c < w.toH1Function.toFun y}.indicator w.toH1Function.grad x :=
      hψqx.trans hqx
    by_cases hx : c < toL2 u x
    · have hxw : c < w.toH1Function.toFun x := by rwa [hwx]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, hxw, ite_true] at hraw ⊢
      exact (congrArg HilbertVec.ofVec hraw).trans hgx
    · have hxw : ¬c < w.toH1Function.toFun x := by simpa only [hwx] using hx
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, hxw, ite_false] at hraw ⊢
      rw [hilbertifyVecField, hraw]
      rfl
  refine ⟨v, ⟨hvvalue, hvgradient⟩, ?_⟩
  intro z hz
  apply ext
  · apply MeasureTheory.Lp.ext (μ := volumeMeasureOn U)
    filter_upwards [hz.1, hvvalue] with x hzx hvx
    exact hzx.trans hvx.symm
  · apply MeasureTheory.Lp.ext (μ := volumeMeasureOn U)
    filter_upwards [hz.2, hvgradient] with x hzx hvx
    exact hzx.trans hvx.symm

end DivergenceFormProcess.Form.ZeroTraceSobolev
