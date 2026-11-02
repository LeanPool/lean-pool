/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.PartDomainTransport
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WeakSubsolution
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace
public import LeanPool.Superdiffusion.Support.Sobolev.MatchedPair.Core

/-!
# PartDomainTruncationTest

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Truncated tests for part-domain weak solutions

This module constructs an admissible zero-trace truncation of a nonnegative
ambient Sobolev test and proves the quantitative limiting estimate that extends
the weak equation to that test.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory Filter
open scoped RealInnerProductSpace

variable {d : ℕ} {V : Set (Vec d)}

private theorem coefficientPairing_eq_inner_operator
    {lam Lam : ℝ} {a : CoeffField d} {W : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam W a)
    (F G : HilbertVectorL2 W) :
    coefficientPairing a W F G = inner ℝ (hilbertCoeffOperator hEll F) G := by
  rw [coefficientPairing_eq_integral_inner, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_hilbertCoeffOperator_apply hEll F] with x hx
  rw [hx]

private theorem scalarL2_inner_nonneg_of_ae_nonneg
    {W : Set (Vec d)} (f g : ScalarL2 W)
    (hf : ∀ᵐ x ∂volumeMeasureOn W, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volumeMeasureOn W, 0 ≤ g x) :
    0 ≤ inner ℝ f g := by
  rw [scalarInner_eq_integral]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hfx hgx
  exact mul_nonneg hfx hgx

private theorem scalar_truncation_error_le {K x y : ℝ}
    (hK : 0 < K) :
    x * (y - K * x) ≤ y ^ 2 / (2 * K) := by
  have hsq : 0 ≤ (K * x - y) ^ 2 := sq_nonneg _
  apply (le_div_iff₀ (mul_pos (by norm_num) hK)).2
  nlinarith only [hsq]

private theorem coefficient_truncation_error_le
    {lam Lam K n M : ℝ} (hK : K = n ^ 2 * M ^ 2 / lam)
    (hn : 0 < n) (hlam : 0 < lam) (hM : 0 < M) (hLamM : Lam ≤ M)
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A)
    (F G : HilbertVec d) :
    inner ℝ (HilbertVec.applyMat A F) (G - K • F) ≤
      (n⁻¹) ^ 2 * ‖G‖ ^ 2 / 2 := by
  have hn0 : n ≠ 0 := hn.ne'
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hop : ‖HilbertVec.applyMat A F‖ ≤ M * ‖F‖ := by
    calc
      ‖HilbertVec.applyMat A F‖ ≤ ‖HilbertVec.applyMat A‖ * ‖F‖ :=
        (HilbertVec.applyMat A).le_opNorm F
      _ ≤ M * ‖F‖ := mul_le_mul_of_nonneg_right
        ((HilbertVec.opNorm_applyMat_le_of_isEllipticMatrix hA).trans hLamM)
        (norm_nonneg F)
  have hopSq : ‖HilbertVec.applyMat A F‖ ^ 2 ≤ M ^ 2 * ‖F‖ ^ 2 := by
    calc
      ‖HilbertVec.applyMat A F‖ ^ 2 ≤ (M * ‖F‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hop 2
      _ = M ^ 2 * ‖F‖ ^ 2 := by ring
  have henergy : lam * ‖F‖ ^ 2 ≤
      inner ℝ (HilbertVec.applyMat A F) F := by
    simpa only [HilbertVec.applyMat_apply, HilbertVec.inner_def,
      HilbertVec.toVec_ofVec, HilbertVec.norm_sq_eq_vecDot, vecDot_comm] using!
        hA.2.2.1 F.toVec
  have hyoung := abs_mul_mul_vecDot_le_add_halves_mul_sq_vecNormSq
    n n⁻¹ (HilbertVec.applyMat A F).toVec G.toVec
  have hcross : inner ℝ (HilbertVec.applyMat A F) G ≤
      n ^ 2 * ‖HilbertVec.applyMat A F‖ ^ 2 / 2 +
        (n⁻¹) ^ 2 * ‖G‖ ^ 2 / 2 := by
    calc
      inner ℝ (HilbertVec.applyMat A F) G ≤
          |inner ℝ (HilbertVec.applyMat A F) G| := le_abs_self _
      _ = |n * n⁻¹ * vecDot (HilbertVec.applyMat A F).toVec G.toVec| := by
        rw [mul_inv_cancel₀ hn0, one_mul, HilbertVec.inner_def]
      _ ≤ n ^ 2 * vecNormSq (HilbertVec.applyMat A F).toVec / 2 +
          (n⁻¹) ^ 2 * vecNormSq G.toVec / 2 := hyoung
      _ = n ^ 2 * ‖HilbertVec.applyMat A F‖ ^ 2 / 2 +
          (n⁻¹) ^ 2 * ‖G‖ ^ 2 / 2 := by
        change n ^ 2 * vecDot (HilbertVec.applyMat A F).toVec
            (HilbertVec.applyMat A F).toVec / 2 +
            (n⁻¹) ^ 2 * vecDot G.toVec G.toVec / 2 = _
        rw [← HilbertVec.norm_sq_eq_vecDot, ← HilbertVec.norm_sq_eq_vecDot]
  rw [inner_sub_right]
  have hnSq : 0 ≤ n ^ 2 := sq_nonneg n
  have hKpos : 0 < K := by
    rw [hK]
    positivity
  have hscaledOp := mul_le_mul_of_nonneg_left hopSq hnSq
  have hscaledEnergy := mul_le_mul_of_nonneg_left henergy hKpos.le
  have hcancel : K * (lam * ‖F‖ ^ 2) = n ^ 2 * M ^ 2 * ‖F‖ ^ 2 := by
    rw [hK]
    field_simp [hlam0]
  rw [hcancel] at hscaledEnergy
  have hscaledOpEnergy :
      n ^ 2 * ‖HilbertVec.applyMat A F‖ ^ 2 ≤
        K * inner ℝ (HilbertVec.applyMat A F) F :=
    hscaledOp.trans (by simpa only [mul_assoc] using hscaledEnergy)
  have hscaledOpEnergyHalf :
      n ^ 2 * ‖HilbertVec.applyMat A F‖ ^ 2 / 2 ≤
        K * inner ℝ (HilbertVec.applyMat A F) F / 2 :=
    div_le_div_of_nonneg_right hscaledOpEnergy (by norm_num)
  have henergyNonneg : 0 ≤ inner ℝ (HilbertVec.applyMat A F) F :=
    (mul_nonneg hlam.le (sq_nonneg ‖F‖)).trans henergy
  have hscaledEnergyNonneg :
      0 ≤ K * inner ℝ (HilbertVec.applyMat A F) F :=
    mul_nonneg hKpos.le henergyNonneg
  rw [real_inner_smul_right]
  linarith only [hcross, hscaledOpEnergyHalf, hscaledEnergyNonneg]

/-- A nonnegative Sobolev test function truncated against a nonnegative
zero-trace function. -/
theorem exists_part_truncation
    (hV : IsOpenBoundedConvexDomain V) (φ : H1Function V)
    (u : ZeroTraceSobolev V) (K : ℝ) (hK : 0 ≤ K)
    (hφ : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ φ.toFun x)
    (hu : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ ZeroTraceSobolev.toL2 u x) :
    ∃ q : ZeroTraceSobolev V,
      (∀ᵐ x ∂volumeMeasureOn V,
        ZeroTraceSobolev.toL2 q x =
          min (φ.toFun x) (K * ZeroTraceSobolev.toL2 u x)) ∧
      (∀ᵐ x ∂volumeMeasureOn V,
        ZeroTraceSobolev.gradient q x =
          if φ.toFun x ≤ K * ZeroTraceSobolev.toL2 u x then
            HilbertVec.ofVec (φ.grad x)
          else K • ZeroTraceSobolev.gradient u x) := by
  let w : H10Function V := Classical.choose
    (ZeroTraceSobolev.exists_h10Function hV u)
  have hw := Classical.choose_spec (ZeroTraceSobolev.exists_h10Function hV u)
  let w₂ : H1Function V := φ - K • w.toH1Function
  have hmatch : MemH10 V (fun x => φ.toFun x - w₂.toFun x) := by
    refine ⟨K • w, ?_⟩
    funext x
    change (K • w.toH1Function).toFun x = φ.toFun x - w₂.toFun x
    simp only [w₂, H1Function.smul_toFun, H1Function.sub_toFun]
    ring
  have hmem := memH10_max_sub_matched hV φ w₂ hmatch 0
  obtain ⟨q₀, hq₀⟩ := hmem
  obtain ⟨p₁, hp₁f, hp₁g⟩ := exists_h1_max_sub_const hV φ 0
  obtain ⟨p₂, hp₂f, hp₂g⟩ := exists_h1_max_sub_const hV w₂ 0
  let qH1 : H1Function V := p₁ - p₂
  have hqH1 : qH1.toFun = q₀.toH1Function.toFun := by
    rw [hq₀]
    funext x
    simp only [qH1, H1Function.sub_toFun]
    rw [congrFun hp₁f x, congrFun hp₂f x]
  have hgradCoord : ∀ i : Fin d,
      (fun x => q₀.toH1Function.grad x i) =ᵐ[volumeMeasureOn V]
        (fun x => qH1.grad x i) := by
    intro i
    exact gradCoord_ae_eq_of_toFun_eq hV.isOpen q₀.toH1Function qH1 hqH1.symm i
  have hgrad : ∀ᵐ x ∂volumeMeasureOn V,
      q₀.toH1Function.grad x = qH1.grad x := by
    filter_upwards [ae_all_iff.2 hgradCoord] with x hx
    funext i
    exact hx i
  let q : ZeroTraceSobolev V := ZeroTraceSobolev.ofH10Function q₀
  refine ⟨q, ?_, ?_⟩
  · filter_upwards [q₀.toH1Function.coeFn_toScalarL2,
      φ.coeFn_toScalarL2, w.toH1Function.coeFn_toScalarL2, hφ, hu]
      with x hqcoe hφcoe hwcoe hφx hux
    change q₀.toH1Function.toScalarL2 x = _
    rw [hqcoe, ← hqH1]
    simp only [qH1, H1Function.sub_toFun]
    rw [congrFun hp₁f x, congrFun hp₂f x]
    have hwu : w.toH1Function.toScalarL2 = ZeroTraceSobolev.toL2 u := hw.1
    have hwux : w.toH1Function.toFun x = ZeroTraceSobolev.toL2 u x := by
      rw [← hwcoe, hwu]
    simp only [sub_zero, w₂, H1Function.sub_toFun, H1Function.smul_toFun]
    rw [hwux]
    by_cases hx : φ.toFun x ≤ K * ZeroTraceSobolev.toL2 u x
    · rw [min_eq_left hx, max_eq_left hφx,
        max_eq_right (sub_nonpos.mpr hx), sub_zero]
    · have hx' := lt_of_not_ge hx
      rw [min_eq_right hx'.le, max_eq_left hφx,
        max_eq_left (sub_nonneg.mpr hx'.le)]
      ring
  · have hφzero : ∀ᵐ x ∂volumeMeasureOn V,
        φ.toFun x = 0 → φ.grad x = 0 := grad_ae_zero_on_level_set hV φ 0
    filter_upwards [q₀.toH1Function.coeFn_gradToHilbertVectorL2,
      w.toH1Function.coeFn_gradToHilbertVectorL2, hgrad, hp₁g, hp₂g,
      φ.coeFn_toScalarL2, w.toH1Function.coeFn_toScalarL2, hφ, hu, hφzero]
      with x hqcoe hwgrad hqgrad hp₁grad hp₂grad hφcoe hwcoe hφx hux hφzero
    change q₀.toH1Function.gradToHilbertVectorL2 x = _
    rw [hqcoe]
    change HilbertVec.ofVec (q₀.toH1Function.grad x) = _
    rw [hqgrad]
    simp only [qH1, H1Function.sub_grad]
    rw [hp₁grad, hp₂grad]
    have hwu : w.toH1Function.toScalarL2 = ZeroTraceSobolev.toL2 u := hw.1
    have hwg : w.toH1Function.gradToHilbertVectorL2 =
        ZeroTraceSobolev.gradient u := hw.2
    have hwux : w.toH1Function.toFun x = ZeroTraceSobolev.toL2 u x := by
      rw [← hwcoe, hwu]
    have hwgradx : HilbertVec.ofVec (w.toH1Function.grad x) =
        ZeroTraceSobolev.gradient u x := by
      have hwgrad' : w.toH1Function.gradToHilbertVectorL2 x =
          HilbertVec.ofVec (w.toH1Function.grad x) := by
        simpa only [hilbertifyVecField] using hwgrad
      rw [← hwgrad', hwg]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, w₂,
      H1Function.sub_toFun, H1Function.smul_toFun, H1Function.sub_grad,
      H1Function.smul_grad]
    simp only [hwux]
    by_cases hx : φ.toFun x ≤ K * ZeroTraceSobolev.toL2 u x
    · have hdiff : ¬ 0 < φ.toFun x - K * ZeroTraceSobolev.toL2 u x :=
        not_lt_of_ge (sub_nonpos.mpr hx)
      rw [ite_eq_left hx, ite_eq_right hdiff]
      by_cases hφpos : 0 < φ.toFun x
      · rw [ite_eq_left hφpos]
        simp only [sub_zero]
      · have hφeq : φ.toFun x = 0 := le_antisymm (le_of_not_gt hφpos) hφx
        rw [ite_eq_right hφpos, hφzero hφeq]
        simp only [sub_zero]
    · have hx' : K * ZeroTraceSobolev.toL2 u x < φ.toFun x := lt_of_not_ge hx
      have hKu : 0 ≤ K * ZeroTraceSobolev.toL2 u x := mul_nonneg hK hux
      have hφpos : 0 < φ.toFun x := hKu.trans_lt hx'
      have hdiff : 0 < φ.toFun x - K * ZeroTraceSobolev.toL2 u x := sub_pos.mpr hx'
      rw [ite_eq_right hx, ite_eq_left hφpos, ite_eq_left hdiff]
      rw [sub_sub_cancel, ← hwgradx]
      rfl

/-- The weak equation extends to nonnegative ambient Sobolev test functions. -/
theorem part_solution_test_inequality (a : CoeffField d) (hV : IsOpenBoundedConvexDomain V)
    {α lam Lam : ℝ} (hα : 0 < α) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam V a)
    (f : ScalarL2 V) (u : ZeroTraceSobolev V)
    (huSol : IsAlphaShiftedWeakSolution a V α f u)
    (hf : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ f x)
    (hu : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ ZeroTraceSobolev.toL2 u x)
    (φ : H1Function V)
    (hφ : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ φ.toFun x) :
    α * inner ℝ (ZeroTraceSobolev.toL2 u) φ.toScalarL2 +
        coefficientPairing a V (ZeroTraceSobolev.gradient u)
          φ.gradToHilbertVectorL2 ≤
      inner ℝ f φ.toScalarL2 := by
  let M : ℝ := max Lam 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right Lam 1)
  have hLamM : Lam ≤ M := le_max_left Lam 1
  let D : ℝ :=
    α * inner ℝ (ZeroTraceSobolev.toL2 u) φ.toScalarL2 +
      coefficientPairing a V (ZeroTraceSobolev.gradient u)
        φ.gradToHilbertVectorL2 - inner ℝ f φ.toScalarL2
  have hbound : ∀ n : ℕ,
      D ≤
        (α * (lam / (2 * M ^ 2)) *
            inner ℝ φ.toScalarL2 φ.toScalarL2 +
          (1 / 2 : ℝ) *
            inner ℝ φ.gradToHilbertVectorL2 φ.gradToHilbertVectorL2) /
          ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n
    let nR : ℝ := ((n + 1 : ℕ) : ℝ)
    have hnR : 0 < nR := by positivity
    let K : ℝ := nR ^ 2 * M ^ 2 / lam
    have hK : 0 < K := by
      dsimp only [K]
      positivity
    obtain ⟨q, hqValue, hqGradient⟩ :=
      exists_part_truncation hV φ u K hK.le hφ hu
    let r : ScalarL2 V := φ.toScalarL2 - ZeroTraceSobolev.toL2 q
    let R : HilbertVectorL2 V :=
      φ.gradToHilbertVectorL2 - ZeroTraceSobolev.gradient q
    let S : Set (Vec d) :=
      {x | K * ZeroTraceSobolev.toL2 u x < φ.toScalarL2 x}
    have hS : MeasurableSet S := by
      exact measurableSet_lt
        ((MeasureTheory.Lp.stronglyMeasurable
          (ZeroTraceSobolev.toL2 u)).const_mul K).measurable
        (MeasureTheory.Lp.stronglyMeasurable φ.toScalarL2).measurable
    have hrValue : ∀ᵐ x ∂volumeMeasureOn V,
        r x = S.indicator
          (fun y => φ.toScalarL2 y - K * ZeroTraceSobolev.toL2 u y) x := by
      filter_upwards [MeasureTheory.Lp.coeFn_sub φ.toScalarL2
          (ZeroTraceSobolev.toL2 q), hqValue, φ.coeFn_toScalarL2]
        with x hr hq hφcoe
      change (φ.toScalarL2 - ZeroTraceSobolev.toL2 q) x = _
      rw [hr, Pi.sub_apply, hq, Set.indicator_apply]
      rw [← hφcoe]
      by_cases hx : K * ZeroTraceSobolev.toL2 u x < φ.toScalarL2 x
      · have hxS : x ∈ S := hx
        rw [ite_eq_left hxS, min_eq_right hx.le]
      · have hxS : x ∉ S := hx
        rw [ite_eq_right hxS, min_eq_left (le_of_not_gt hx), sub_self]
    have hRGradient : ∀ᵐ x ∂volumeMeasureOn V,
        R x = S.indicator
          (fun y => φ.gradToHilbertVectorL2 y -
            K • ZeroTraceSobolev.gradient u y) x := by
      filter_upwards [MeasureTheory.Lp.coeFn_sub φ.gradToHilbertVectorL2
          (ZeroTraceSobolev.gradient q), hqGradient,
          φ.coeFn_toScalarL2, φ.coeFn_gradToHilbertVectorL2]
        with x hR hq hφcoe hφgrad
      change (φ.gradToHilbertVectorL2 - ZeroTraceSobolev.gradient q) x = _
      rw [hR, Pi.sub_apply, hq, Set.indicator_apply]
      have hφgrad' : φ.gradToHilbertVectorL2 x = HilbertVec.ofVec (φ.grad x) := by
        simpa only [hilbertifyVecField] using hφgrad
      rw [← hφcoe]
      by_cases hx : K * ZeroTraceSobolev.toL2 u x < φ.toScalarL2 x
      · have hxS : x ∈ S := hx
        rw [ite_eq_left hxS, ite_eq_right (not_le_of_gt hx)]
      · have hxS : x ∉ S := hx
        rw [ite_eq_right hxS, ite_eq_left (le_of_not_gt hx), ← hφgrad', sub_self]
    have hrNonneg : ∀ᵐ x ∂volumeMeasureOn V, 0 ≤ r x := by
      filter_upwards [hrValue] with x hx
      rw [hx, Set.indicator_apply]
      split_ifs with hxs
      · exact sub_nonneg.mpr hxs.le
      · exact le_rfl
    have hresidual :
        D = α * inner ℝ (ZeroTraceSobolev.toL2 u) r +
            coefficientPairing a V (ZeroTraceSobolev.gradient u) R -
          inner ℝ f r := by
      have hqEq := huSol q
      dsimp only [D, r, R]
      rw [coefficientPairing_eq_inner_operator hEll
        (ZeroTraceSobolev.gradient u) (ZeroTraceSobolev.gradient q)] at hqEq
      rw [coefficientPairing_eq_inner_operator hEll
        (ZeroTraceSobolev.gradient u) φ.gradToHilbertVectorL2]
      rw [coefficientPairing_eq_inner_operator hEll
        (ZeroTraceSobolev.gradient u)
          (φ.gradToHilbertVectorL2 - ZeroTraceSobolev.gradient q)]
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      linarith only [hqEq]
    have hforcing : 0 ≤ inner ℝ f r :=
      scalarL2_inner_nonneg_of_ae_nonneg f r hf hrNonneg
    have hmassRaw : inner ℝ (ZeroTraceSobolev.toL2 u) r ≤
        (1 / (2 * K)) * inner ℝ φ.toScalarL2 φ.toScalarL2 := by
      rw [scalarInner_eq_integral, scalarInner_eq_integral,
        ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_mono_ae
      · exact (MeasureTheory.Lp.memLp (ZeroTraceSobolev.toL2 u)).integrable_mul
          (MeasureTheory.Lp.memLp r)
      · exact (MeasureTheory.L2.integrable_inner φ.toScalarL2 φ.toScalarL2).const_mul _
      filter_upwards [hrValue, hu, hφ, φ.coeFn_toScalarL2] with x hr hux hφx hφcoe
      rw [hr, Set.indicator_apply]
      by_cases hx : K * ZeroTraceSobolev.toL2 u x < φ.toScalarL2 x
      · have hxS : x ∈ S := hx
        rw [ite_eq_left hxS]
        change ZeroTraceSobolev.toL2 u x *
            (φ.toScalarL2 x - K * ZeroTraceSobolev.toL2 u x) ≤
          (1 / (2 * K)) * (φ.toScalarL2 x * φ.toScalarL2 x)
        convert scalar_truncation_error_le (x := ZeroTraceSobolev.toL2 u x)
          (y := φ.toScalarL2 x) hK using 1
        all_goals ring
      · have hxS : x ∉ S := hx
        rw [ite_eq_right hxS, mul_zero]
        exact mul_nonneg (by positivity) (mul_self_nonneg _)
    have hmass : α * inner ℝ (ZeroTraceSobolev.toL2 u) r ≤
        α * (1 / (2 * K)) * inner ℝ φ.toScalarL2 φ.toScalarL2 := by
      calc
        α * inner ℝ (ZeroTraceSobolev.toL2 u) r ≤
            α * ((1 / (2 * K)) * inner ℝ φ.toScalarL2 φ.toScalarL2) :=
          mul_le_mul_of_nonneg_left hmassRaw hα.le
        _ = α * (1 / (2 * K)) * inner ℝ φ.toScalarL2 φ.toScalarL2 := by ring
    have hcoeff : coefficientPairing a V (ZeroTraceSobolev.gradient u) R ≤
        (nR⁻¹) ^ 2 / 2 *
          inner ℝ φ.gradToHilbertVectorL2 φ.gradToHilbertVectorL2 := by
      rw [coefficientPairing_eq_inner_operator hEll, MeasureTheory.L2.inner_def,
        MeasureTheory.L2.inner_def, ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_mono_ae
      · exact MeasureTheory.L2.integrable_inner
          (hilbertCoeffOperator hEll (ZeroTraceSobolev.gradient u)) R
      · exact (MeasureTheory.L2.integrable_inner
          φ.gradToHilbertVectorL2 φ.gradToHilbertVectorL2).const_mul _
      filter_upwards [ae_hilbertCoeffOperator_apply hEll
          (ZeroTraceSobolev.gradient u), hRGradient,
          self_mem_ae_restrict hV.isOpen.measurableSet]
        with x hAx hRx hxV
      rw [hAx, hRx, Set.indicator_apply]
      by_cases hx : x ∈ S
      · rw [ite_eq_left hx]
        rw [real_inner_self_eq_norm_sq]
        convert
          coefficient_truncation_error_le (d := d) (K := K) (n := nR)
            rfl hnR hlam hM hLamM (hEll.2 x hxV)
            (ZeroTraceSobolev.gradient u x) (φ.gradToHilbertVectorL2 x) using 1
        all_goals first | rfl | ring
      · rw [ite_eq_right hx, inner_zero_right]
        exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) real_inner_self_nonneg
    have hpre : D ≤
        α * (1 / (2 * K)) * inner ℝ φ.toScalarL2 φ.toScalarL2 +
          (nR⁻¹) ^ 2 / 2 *
            inner ℝ φ.gradToHilbertVectorL2 φ.gradToHilbertVectorL2 := by
      rw [hresidual]
      calc
        α * inner ℝ (ZeroTraceSobolev.toL2 u) r +
              coefficientPairing a V (ZeroTraceSobolev.gradient u) R - inner ℝ f r ≤
            α * inner ℝ (ZeroTraceSobolev.toL2 u) r +
              coefficientPairing a V (ZeroTraceSobolev.gradient u) R :=
          sub_le_self _ hforcing
        _ ≤ _ := add_le_add hmass hcoeff
    dsimp only [K, nR] at hpre ⊢
    have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hnR
    have hM0 : M ≠ 0 := hM.ne'
    have hlam0 : lam ≠ 0 := hlam.ne'
    convert hpre using 1
    all_goals field_simp [hn0, hM0, hlam0]
  have htendInv : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) atTop (nhds 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [one_div, Nat.cast_add, Nat.cast_one, inv_pow,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht.pow 2
  have htend : Tendsto (fun n : ℕ =>
      (α * (lam / (2 * M ^ 2)) * inner ℝ φ.toScalarL2 φ.toScalarL2 +
          (1 / 2 : ℝ) * inner ℝ φ.gradToHilbertVectorL2 φ.gradToHilbertVectorL2) /
        ((n + 1 : ℕ) : ℝ) ^ 2) atTop (nhds 0) := by
    let C : ℝ := α * (lam / (2 * M ^ 2)) * inner ℝ φ.toScalarL2 φ.toScalarL2 +
      (1 / 2 : ℝ) * inner ℝ φ.gradToHilbertVectorL2 φ.gradToHilbertVectorL2
    have hconst : Tendsto (fun _ : ℕ => C) atTop (nhds C) := tendsto_const_nhds
    have ht := hconst.mul htendInv
    dsimp only [C] at ht ⊢
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using ht
  have hD : D ≤ 0 := ge_of_tendsto htend (Filter.Eventually.of_forall hbound)
  dsimp only [D] at hD
  linarith only [hD]

end DivergenceFormProcess.Form
