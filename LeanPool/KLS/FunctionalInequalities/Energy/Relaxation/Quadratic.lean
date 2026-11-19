/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Energy.Form.ClosedQuadratic
public import LeanPool.KLS.FunctionalInequalities.Energy.Form.QuadraticPreEnergy
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.LowerSemicontinuous
public import LeanPool.KLS.FunctionalInequalities.Energy.Relaxation.Recovery
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Order.Filter.ENNReal

/-!
# Quadratic structure of sequential relaxation

This module transfers the algebra of a finite quadratic pre-energy to its sequential relaxation
on a real normed space. The construction does not assume that the concrete energy is constant on
realization fibers: relaxation may strictly decrease it there.

The parallelogram identity itself does not require density. At finite-energy points it follows by
combining recovery sequences; if one input has energy `⊤`, the relevant inequality is automatic.
Density enters only when the resulting quadratic functional is packaged as densely defined.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy.PreEnergy.Quadratic


universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {P : PreEnergy X} [AddCommGroup P.Test] [Module ℝ P.Test]

/-- Addition of approximating sequences is compatible with a linear realization. -/
def addApproximatingSequence (h : P.Quadratic) {x y : X}
    (f : P.ApproximatingSequence x) (g : P.ApproximatingSequence y) :
    P.ApproximatingSequence (x + y) where
  val n := f.1 n + g.1 n
  property := by
    convert f.2.add g.2 using 1
    funext n
    exact h.map_add (f.1 n) (g.1 n)

/-- Subtraction of approximating sequences is compatible with a linear realization. -/
def subApproximatingSequence (h : P.Quadratic) {x y : X}
    (f : P.ApproximatingSequence x) (g : P.ApproximatingSequence y) :
    P.ApproximatingSequence (x - y) where
  val n := f.1 n - g.1 n
  property := by
    convert f.2.sub g.2 using 1
    funext n
    exact h.map_sub (f.1 n) (g.1 n)

/-- For extended nonnegative sequences, the sum of the two `liminf`s is bounded by the
`liminf` of the pointwise sum.

This elementary fact is recorded locally because the corresponding general ordered-group lemma
does not apply to `ENNReal`. The proof uses the monotone sequence of tail infima.
-/
private theorem liminf_add_le_liminf_add (a b : ℕ → ENNReal) :
    liminf a atTop + liminf b atTop ≤
      liminf (fun n ↦ a n + b n) atTop := by
  simp only [Filter.liminf_eq_iSup_iInf_of_nat]
  have ha : Monotone (fun n ↦ ⨅ i, ⨅ (_ : n ≤ i), a i) := by
    intro n m hnm
    refine le_iInf fun i ↦ le_iInf fun hmi ↦ ?_
    exact iInf_le_of_le i (iInf_le_of_le (hnm.trans hmi) le_rfl)
  have hb : Monotone (fun n ↦ ⨅ i, ⨅ (_ : n ≤ i), b i) := by
    intro n m hnm
    refine le_iInf fun i ↦ le_iInf fun hmi ↦ ?_
    exact iInf_le_of_le i (iInf_le_of_le (hnm.trans hmi) le_rfl)
  rw [ENNReal.iSup_add_iSup_of_monotone ha hb]
  refine iSup_le fun n ↦ le_iSup_of_le n ?_
  refine le_iInf fun i ↦ le_iInf fun hi ↦ ?_
  exact add_le_add
    (iInf_le_of_le i (iInf_le_of_le hi le_rfl))
    (iInf_le_of_le i (iInf_le_of_le hi le_rfl))

/-- Scale every concrete test in an approximating sequence. -/
def smulApproximatingSequence (h : P.Quadratic) (c : ℝ) {x : X}
    (f : P.ApproximatingSequence x) : P.ApproximatingSequence (c • x) where
  val n := c • f.1 n
  property := by
    convert f.2.const_smul c using 1
    funext n
    exact h.map_smul c (f.1 n)

/-- The scaled sequence has the expected scaled `liminf` energy. -/
theorem sequenceEnergy_smul (h : P.Quadratic) (c : ℝ) {x : X}
    (f : P.ApproximatingSequence x) :
    P.sequenceEnergy (h.smulApproximatingSequence c f) =
      (‖c‖₊ ^ 2 : ENNReal) * P.sequenceEnergy f := by
  change liminf (fun n ↦ (P.energy (c • f.1 n) : ENNReal)) atTop =
    (‖c‖₊ ^ 2 : ENNReal) * liminf (fun n ↦ (P.energy (f.1 n) : ENNReal)) atTop
  have hpoint : (fun n ↦ (P.energy (c • f.1 n) : ENNReal)) =
      fun n ↦ (‖c‖₊ ^ 2 : ENNReal) * (P.energy (f.1 n) : ENNReal) := by
    funext n
    exact congrArg ((↑) : NNReal → ENNReal) (h.energy_smul c (f.1 n))
  rw [hpoint]
  exact ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top

/-- One direction of quadratic homogeneity follows by scaling every recovery candidate. -/
private theorem sequentialRelaxation_smul_le (h : P.Quadratic) (c : ℝ) (hc : c ≠ 0)
    (x : X) :
    P.sequentialRelaxation (c • x) ≤
      (‖c‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation x := by
  calc
    P.sequentialRelaxation (c • x) ≤
        ⨅ f : P.ApproximatingSequence x,
          (‖c‖₊ ^ 2 : ENNReal) * P.sequenceEnergy f := by
      refine le_iInf fun f ↦ ?_
      exact (P.sequentialRelaxation_le_sequenceEnergy
        (h.smulApproximatingSequence c f)).trans_eq (h.sequenceEnergy_smul c f)
    _ = (‖c‖₊ ^ 2 : ENNReal) *
        (⨅ f : P.ApproximatingSequence x, P.sequenceEnergy f) :=
      (ENNReal.mul_iInf_of_ne (by simp [hc]) ENNReal.coe_ne_top).symm
    _ = (‖c‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation x := rfl

/-- Sequential relaxation inherits nonzero quadratic homogeneity from the concrete pre-energy. -/
theorem sequentialRelaxation_smul_of_ne_zero (h : P.Quadratic) (c : ℝ) (hc : c ≠ 0)
    (x : X) :
    P.sequentialRelaxation (c • x) =
      (‖c‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation x := by
  apply le_antisymm (h.sequentialRelaxation_smul_le c hc x)
  have hback := h.sequentialRelaxation_smul_le c⁻¹ (inv_ne_zero hc) (c • x)
  have hscaled := mul_le_mul_left hback (‖c‖₊ ^ 2 : ENNReal)
  have hscaled' : (‖c‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation x ≤
      (‖c‖₊ ^ 2 : ENNReal) *
        ((‖c⁻¹‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation (c • x)) := by
    simpa [hc, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hcoeff : (‖c‖₊ ^ 2 : ENNReal) * (‖c⁻¹‖₊ ^ 2 : ENNReal) = 1 := by
    rw [← mul_pow]
    simp only [nnNorm_inv]
    rw [ENNReal.coe_inv (nnNorm_ne_zero_iff.mpr hc),
      ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr (nnNorm_ne_zero_iff.mpr hc))
        ENNReal.coe_ne_top,
      one_pow]
  calc
    (‖c‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation x ≤
        (‖c‖₊ ^ 2 : ENNReal) *
          ((‖c⁻¹‖₊ ^ 2 : ENNReal) * P.sequentialRelaxation (c • x)) := hscaled'
    _ = ((‖c‖₊ ^ 2 : ENNReal) * (‖c⁻¹‖₊ ^ 2 : ENNReal)) *
        P.sequentialRelaxation (c • x) := by rw [mul_assoc]
    _ = P.sequentialRelaxation (c • x) := by rw [hcoeff, one_mul]

/-- The easy direction of the relaxed parallelogram identity when both input energies are
finite. -/
private theorem sequentialRelaxation_parallelogram_le_of_finiteAt (h : P.Quadratic)
    {x y : X} (hx : P.sequentialRelaxation.FiniteAt x)
    (hy : P.sequentialRelaxation.FiniteAt y) :
    P.sequentialRelaxation (x + y) + P.sequentialRelaxation (x - y) ≤
      2 * P.sequentialRelaxation x + 2 * P.sequentialRelaxation y := by
  obtain ⟨f, hf⟩ := P.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt hx
  obtain ⟨g, hg⟩ := P.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt hy
  let plus := h.addApproximatingSequence f g
  let minus := h.subApproximatingSequence f g
  have htwo_f :
      Tendsto (fun n ↦ 2 * (P.energy (f.1 n) : ENNReal)) atTop
        (𝓝 (2 * P.sequentialRelaxation x)) :=
    ENNReal.Tendsto.const_mul hf (Or.inr (by norm_num))
  have htwo_g :
      Tendsto (fun n ↦ 2 * (P.energy (g.1 n) : ENNReal)) atTop
        (𝓝 (2 * P.sequentialRelaxation y)) :=
    ENNReal.Tendsto.const_mul hg (Or.inr (by norm_num))
  have hsum :
      Tendsto
        (fun n ↦ 2 * (P.energy (f.1 n) : ENNReal) +
          2 * (P.energy (g.1 n) : ENNReal)) atTop
        (𝓝 (2 * P.sequentialRelaxation x + 2 * P.sequentialRelaxation y)) :=
    htwo_f.add htwo_g
  calc
    P.sequentialRelaxation (x + y) + P.sequentialRelaxation (x - y) ≤
        P.sequenceEnergy plus + P.sequenceEnergy minus :=
      add_le_add
        (P.sequentialRelaxation_le_sequenceEnergy plus)
        (P.sequentialRelaxation_le_sequenceEnergy minus)
    _ ≤ liminf
        (fun n ↦ (P.energy (f.1 n + g.1 n) : ENNReal) +
          (P.energy (f.1 n - g.1 n) : ENNReal)) atTop := by
      exact liminf_add_le_liminf_add _ _
    _ = liminf
        (fun n ↦ 2 * (P.energy (f.1 n) : ENNReal) +
          2 * (P.energy (g.1 n) : ENNReal)) atTop := by
      apply liminf_congr
      exact Eventually.of_forall fun n ↦ by
        simpa using congrArg ((↑) : NNReal → ENNReal)
          (h.parallelogram (f.1 n) (g.1 n))
    _ = 2 * P.sequentialRelaxation x + 2 * P.sequentialRelaxation y :=
      hsum.liminf_eq

/-- The relaxed parallelogram inequality in the direction obtained from recovery sequences.

No density assumption is needed. If an input energy is infinite, the right-hand side is `⊤`;
otherwise both required recovery sequences exist by finiteness.
-/
theorem sequentialRelaxation_parallelogram_le (h : P.Quadratic) (x y : X) :
    P.sequentialRelaxation (x + y) + P.sequentialRelaxation (x - y) ≤
      2 * P.sequentialRelaxation x + 2 * P.sequentialRelaxation y := by
  by_cases hx : P.sequentialRelaxation.FiniteAt x
  · by_cases hy : P.sequentialRelaxation.FiniteAt y
    · exact h.sequentialRelaxation_parallelogram_le_of_finiteAt hx hy
    · have hy_top : P.sequentialRelaxation y = ⊤ := by
        change ¬ P.sequentialRelaxation y ≠ ⊤ at hy
        exact not_ne_iff.mp hy
      simp [hy_top]
  · have hx_top : P.sequentialRelaxation x = ⊤ := by
      change ¬ P.sequentialRelaxation x ≠ ⊤ at hx
      exact not_ne_iff.mp hx
    simp [hx_top]

/-- Sequential relaxation preserves the extended parallelogram identity.

The reverse inequality applies the preceding result to `x + y` and `x - y`, uses homogeneity at
the nonzero scalar `2`, and cancels the positive finite factor `2` in `ENNReal`.
-/
theorem sequentialRelaxation_parallelogram (h : P.Quadratic) (x y : X) :
    P.sequentialRelaxation (x + y) + P.sequentialRelaxation (x - y) =
      2 * P.sequentialRelaxation x + 2 * P.sequentialRelaxation y := by
  apply le_antisymm (h.sequentialRelaxation_parallelogram_le x y)
  have hdouble := h.sequentialRelaxation_parallelogram_le (x + y) (x - y)
  have hsum_sub : (x + y) + (x - y) = (2 : ℝ) • x := by
    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm]
  have hsub_sub : (x + y) - (x - y) = (2 : ℝ) • y := by
    simp [two_smul, sub_eq_add_neg, add_assoc, add_left_comm]
  rw [hsum_sub, hsub_sub, h.sequentialRelaxation_smul_of_ne_zero 2 (by norm_num) x,
    h.sequentialRelaxation_smul_of_ne_zero 2 (by norm_num) y] at hdouble
  norm_num at hdouble
  rw [←
    ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)]
  convert hdouble using 1 <;> ring

/-- The coefficient used by the finite pre-energy is the `ENNReal.ofReal` coefficient expected
by `ClosedQuadratic`. -/
private theorem coe_nnnorm_sq_eq_ofReal_sq (c : ℝ) :
    (‖c‖₊ ^ 2 : ENNReal) = ENNReal.ofReal (c ^ 2) := by
  rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_pow (by positivity)]
  simp [Real.norm_eq_abs]

/-- A dense quadratic pre-energy generates a densely defined closed quadratic functional by
sequential relaxation.

No closability or agreement-on-tests hypothesis is part of this theorem. Such hypotheses are
needed only if one wants the relaxed functional to retain the original energy on every concrete
test.
-/
theorem closedQuadratic_sequentialRelaxation (h : P.Quadratic)
    (hDense : P.DenseRealization) : ClosedQuadratic P.sequentialRelaxation where
  zero := h.sequentialRelaxation_zero
  smul_of_ne_zero c hc x := by
    rw [h.sequentialRelaxation_smul_of_ne_zero c hc x,
      coe_nnnorm_sq_eq_ofReal_sq]
  parallelogram := h.sequentialRelaxation_parallelogram
  lowerSemicontinuous := P.lowerSemicontinuous_sequentialRelaxation
  dense_domain := hDense.dense_relaxation_domain

end FunctionalInequalities.Energy.PreEnergy.Quadratic
