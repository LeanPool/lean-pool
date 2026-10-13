/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainTransport
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainTruncationTest
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WeakSubsolution

/-!
# PartDomainSubsolution

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Weak subsolutions from part-domain resolvents

This module proves that the zero extension of a nonnegative part-domain
resolvent is a weak subsolution on a larger bounded open convex domain, and
records the resulting nonnegative supersolution remainder and resolvent
estimate.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter
open scoped RealInnerProductSpace

variable {d : ℕ} {V U : Set (Vec d)}

/-- The zero extension of the part-domain resolvent is a weak subsolution on
the larger domain for nonnegative forcing.  The general-open case is not
asserted. -/
theorem partDomainZeroExtension_isSubsolution [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpenBoundedConvexDomain U)
    (hVU : V ⊆ U) {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    IsAlphaShiftedWeakSubsolution a U α f
      (ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
        (alphaShiftedSolution a hα hlam
          (hEll.mono hV.isOpen.measurableSet hVU)
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))) := by
  classical
  let hEllV : IsEllipticFieldOn lam Lam V a :=
    hEll.mono hV.isOpen.measurableSet hVU
  let fV : ScalarL2 V := restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f
  let uV : ZeroTraceSobolev V := alphaShiftedSolution a hα hlam hEllV fV
  let uU : ZeroTraceSobolev U :=
    ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU uV
  have hfVspec : fV =ᵐ[volumeMeasureOn V] f := by
    simpa only [fV] using restrictScalarL2ToPart_coeFn hV.isOpen.measurableSet
      hU.isOpen.measurableSet hVU f
  have hfV : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ fV x := by
    filter_upwards
      [hfVspec, ae_restrict_of_ae_restrict_of_subset hVU hf]
      with x hfx hx
    rw [hfx]
    exact hx
  have huV : ∀ᵐ x ∂volumeMeasureOn V,
      0 ≤ ZeroTraceSobolev.toL2 uV x := by
    simpa only [uV, alphaShiftedResolvent_apply] using
      alphaShiftedResolvent_nonneg_ae a hV hα hlam hEllV fV hfV
  have huVSol : IsAlphaShiftedWeakSolution a V α fV uV := by
    simpa only [uV] using
      alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEllV fV
  intro φ hφ
  let w : H10Function U := Classical.choose
    (ZeroTraceSobolev.exists_h10Function hU φ)
  have hw := Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hU φ)
  let φV : H1Function V := w.toH1Function.restrict hV.isOpen hVU
  have hwValueV := ae_restrict_of_ae_restrict_of_subset hVU
    w.toH1Function.coeFn_toScalarL2
  have hwGradientV := ae_restrict_of_ae_restrict_of_subset hVU
    w.toH1Function.coeFn_gradToHilbertVectorL2
  have hφVValue : φV.toScalarL2 =ᵐ[volumeMeasureOn V]
      ZeroTraceSobolev.toL2 φ := by
    filter_upwards [φV.coeFn_toScalarL2, hwValueV] with x hφVcoe hwcoe
    rw [hφVcoe]
    change w.toH1Function.toFun x = ZeroTraceSobolev.toL2 φ x
    rw [← hwcoe]
    exact congrArg (fun z : ScalarL2 U => z x) hw.1
  have hφVGradient : φV.gradToHilbertVectorL2 =ᵐ[volumeMeasureOn V]
      ZeroTraceSobolev.gradient φ := by
    filter_upwards [φV.coeFn_gradToHilbertVectorL2, hwGradientV]
      with x hφVgrad hwgrad
    rw [hφVgrad]
    change HilbertVec.ofVec (w.toH1Function.grad x) =
      ZeroTraceSobolev.gradient φ x
    have hwgrad' : w.toH1Function.gradToHilbertVectorL2 x =
        HilbertVec.ofVec (w.toH1Function.grad x) := by
      simpa only [hilbertifyVecField] using hwgrad
    rw [← hwgrad']
    exact congrArg (fun z : HilbertVectorL2 U => z x) hw.2
  have hφV : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ φV.toFun x := by
    filter_upwards [φV.coeFn_toScalarL2, hφVValue,
      ae_restrict_of_ae_restrict_of_subset hVU hφ]
      with x hφVcoe hφeq hφx
    rw [← hφVcoe, hφeq]
    exact hφx
  have hcore := part_solution_test_inequality a hV hα hlam hEllV fV uV
    huVSol hfV huV φV hφV
  have huUSpec :=
    ZeroTraceSobolev.extendByZeroToPartSuperset_toL2 hV hU.isOpen hVU uV
  have hgradUSpec :=
    ZeroTraceSobolev.extendByZeroToPartSuperset_gradient hV hU.isOpen hVU uV
  have hmass : inner ℝ (ZeroTraceSobolev.toL2 uU)
      (ZeroTraceSobolev.toL2 φ) =
        inner ℝ (ZeroTraceSobolev.toL2 uV) φV.toScalarL2 :=
    scalar_inner_zeroExtension_eq_restriction hV.isOpen.measurableSet
      hU.isOpen.measurableSet hVU _ _ _ _
      huUSpec hφVValue
  have hcoeff : coefficientPairing a U (ZeroTraceSobolev.gradient uU)
      (ZeroTraceSobolev.gradient φ) =
        coefficientPairing a V (ZeroTraceSobolev.gradient uV)
          φV.gradToHilbertVectorL2 :=
    coefficientPairing_zeroExtension_eq_restriction a hV.isOpen.measurableSet
      hU.isOpen.measurableSet hVU _ _ _ _
      hgradUSpec hφVGradient
  have hforcing : inner ℝ fV φV.toScalarL2 ≤
      inner ℝ f (ZeroTraceSobolev.toL2 φ) :=
    scalar_inner_restriction_le hVU f fV
      (ZeroTraceSobolev.toL2 φ) φV.toScalarL2 hfVspec hφVValue hf hφ
  change α * inner ℝ (ZeroTraceSobolev.toL2 uU)
      (ZeroTraceSobolev.toL2 φ) +
      coefficientPairing a U (ZeroTraceSobolev.gradient uU)
        (ZeroTraceSobolev.gradient φ) ≤
    inner ℝ f (ZeroTraceSobolev.toL2 φ)
  calc
    α * inner ℝ (ZeroTraceSobolev.toL2 uU) (ZeroTraceSobolev.toL2 φ) +
          coefficientPairing a U (ZeroTraceSobolev.gradient uU)
            (ZeroTraceSobolev.gradient φ) =
        α * inner ℝ (ZeroTraceSobolev.toL2 uV) φV.toScalarL2 +
          coefficientPairing a V (ZeroTraceSobolev.gradient uV)
            φV.gradToHilbertVectorL2 := by rw [hmass, hcoeff]
    _ ≤ inner ℝ fV φV.toScalarL2 := hcore
    _ ≤ inner ℝ f (ZeroTraceSobolev.toL2 φ) := hforcing

/-- The difference between the full-domain resolvent solution and the
zero-extended part-domain solution is nonnegative almost everywhere.  The
general-open case is not asserted. -/
theorem partDomainRemainder_nonneg_ae [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpenBoundedConvexDomain U)
    (hVU : V ⊆ U) {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      0 ≤ ZeroTraceSobolev.toL2
        (alphaShiftedSolution a hα hlam hEll f -
          ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
            (alphaShiftedSolution a hα hlam
              (hEll.mono hV.isOpen.measurableSet hVU)
              (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))) x := by
  let uU : ZeroTraceSobolev U :=
    ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
      (alphaShiftedSolution a hα hlam
        (hEll.mono hV.isOpen.measurableSet hVU)
        (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))
  let rU : ZeroTraceSobolev U := alphaShiftedSolution a hα hlam hEll f
  have huSub : IsAlphaShiftedWeakSubsolution a U α f uU := by
    simpa only [uU] using
      partDomainZeroExtension_isSubsolution a hV hU hVU hα hlam hEll f hf
  have hrSol : IsAlphaShiftedWeakSolution a U α f rU := by
    simpa only [rU] using
      alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f
  have hur : ∀ᵐ x ∂volumeMeasureOn U,
      ZeroTraceSobolev.toL2 uU x ≤ ZeroTraceSobolev.toL2 rU x :=
    weakSubsolution_le_weakSupersolution_ae a hU hα hEll huSub
      hrSol.isSupersolution (Filter.Eventually.of_forall fun _ => le_rfl)
  filter_upwards [hur,
    MeasureTheory.Lp.coeFn_sub (ZeroTraceSobolev.toL2 rU)
      (ZeroTraceSobolev.toL2 uU)] with x hx hsub
  change 0 ≤ ZeroTraceSobolev.toL2 (rU - uU) x
  rw [map_sub, hsub, Pi.sub_apply]
  exact sub_nonneg.mpr hx

/-- The full-domain resolvent solution minus the zero-extended part-domain
solution is a weak supersolution with zero right-hand side.  The general-open
case is not asserted. -/
theorem partDomainRemainder_isSupersolution [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpenBoundedConvexDomain U)
    (hVU : V ⊆ U) {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    IsAlphaShiftedWeakSupersolution a U α 0
      (alphaShiftedSolution a hα hlam hEll f -
        ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
          (alphaShiftedSolution a hα hlam
            (hEll.mono hV.isOpen.measurableSet hVU)
            (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))) := by
  let uU : ZeroTraceSobolev U :=
    ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
      (alphaShiftedSolution a hα hlam
        (hEll.mono hV.isOpen.measurableSet hVU)
        (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))
  let rU : ZeroTraceSobolev U := alphaShiftedSolution a hα hlam hEll f
  have huSub : IsAlphaShiftedWeakSubsolution a U α f uU := by
    simpa only [uU] using
      partDomainZeroExtension_isSubsolution a hV hU hVU hα hlam hEll f hf
  have hrSol : IsAlphaShiftedWeakSolution a U α f rU := by
    simpa only [rU] using
      alphaShiftedSolution_isAlphaShiftedWeakSolution a hα hlam hEll f
  intro φ hφ
  have huφ := huSub φ hφ
  have hrφ := hrSol φ
  have huφ' : shiftedBilin hEll α uU φ ≤
      inner ℝ f (ZeroTraceSobolev.toL2 φ) := by
    rw [shiftedBilin_apply]
    exact huφ
  have hrφ' : shiftedBilin hEll α rU φ =
      inner ℝ f (ZeroTraceSobolev.toL2 φ) := by
    rw [shiftedBilin_apply]
    exact hrφ
  rw [inner_zero_left, ← shiftedBilin_apply hEll α]
  change 0 ≤ shiftedBilin hEll α (rU - uU) φ
  rw [map_sub, sub_apply]
  exact sub_nonneg.mpr (huφ'.trans_eq hrφ'.symm)

/-- Resolvent estimate for the nonnegative supersolution remainder generated
by nested bounded open convex domains.  The general-open case is not
asserted. -/
theorem partDomainRemainder_resolvent_le_ae [NeZero d]
    (a : CoeffField d)
    (hV : IsOpenBoundedConvexDomain V) (hU : IsOpenBoundedConvexDomain U)
    (hVU : V ⊆ U) {alpha beta lam Lam : ℝ} (hAlpha : 0 < alpha)
    (hAlphaBeta : alpha < beta) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a) (f : ScalarL2 U)
    (hf : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ f x) :
    ∀ᵐ x ∂volumeMeasureOn U,
      beta * alphaShiftedResolvent a (hAlpha.trans hAlphaBeta) hlam hEll
          (ZeroTraceSobolev.toL2
            (alphaShiftedSolution a hAlpha hlam hEll f -
              ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
                (alphaShiftedSolution a hAlpha hlam
                  (hEll.mono hV.isOpen.measurableSet hVU)
                  (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f)))) x ≤
        (beta / (beta - alpha)) * ZeroTraceSobolev.toL2
          (alphaShiftedSolution a hAlpha hlam hEll f -
            ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
              (alphaShiftedSolution a hAlpha hlam
                (hEll.mono hV.isOpen.measurableSet hVU)
                (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))) x := by
  let v : ZeroTraceSobolev U :=
    alphaShiftedSolution a hAlpha hlam hEll f -
      ZeroTraceSobolev.extendByZeroToPartSuperset hV hU.isOpen hVU
        (alphaShiftedSolution a hAlpha hlam
          (hEll.mono hV.isOpen.measurableSet hVU)
          (restrictScalarL2ToPart (V := V) hU.isOpen.measurableSet f))
  have hv : IsAlphaShiftedWeakSupersolution a U alpha 0 v := by
    simpa only [v] using
      partDomainRemainder_isSupersolution a hV hU hVU hAlpha hlam hEll f hf
  simpa only [v] using
    resolvent_le_of_weakSupersolution_ae a hU (hAlpha.trans hAlphaBeta)
      hAlphaBeta hlam hEll v hv

end DivergenceFormProcess.Form
