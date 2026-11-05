/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.CutoffTest
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.Basic

/-!
# MaximumPrinciple

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Weak maximum principle with a nonnegative potential

For the equation `-div (a grad u) + (alpha + q) u = 0` with `alpha > 0` and
`q >= 0`, a solution whose positive part above a nonnegative level has zero
trace is bounded by that level.  The proof tests the equation with the
truncation itself: the elliptic term is nonnegative on the superlevel set and
the mass term is bounded below by the square of the truncation.

## Main results

- `DivergenceFormProcess.Decay.ae_le_of_positivePart_zeroTrace`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ} {U : Set (Vec d)}

/-- The zero-trace witness of a positive-part truncation, as a test
function. -/
def positivePartTest {u : H1Function U} {M : ℝ}
    (htrace : MemH10 U (fun x => max (u.toFun x - M) 0)) : H10Function U :=
  Classical.choose htrace

/-- The truncation test has the expected value. -/
theorem positivePartTest_toFun {u : H1Function U} {M : ℝ}
    (htrace : MemH10 U (fun x => max (u.toFun x - M) 0)) :
    (positivePartTest htrace).toH1Function.toFun =
      fun x => max (u.toFun x - M) 0 :=
  Classical.choose_spec htrace

/-- The truncation test has the expected weak gradient. -/
theorem positivePartTest_grad_ae (hU : IsOpenBoundedConvexDomain U)
    {u : H1Function U} {M : ℝ}
    (htrace : MemH10 U (fun x => max (u.toFun x - M) 0)) :
    ∀ᵐ x ∂volumeMeasureOn U,
      (positivePartTest htrace).toH1Function.grad x =
        {y | M < u.toFun y}.indicator u.grad x := by
  obtain ⟨v, hvfun, hvgrad⟩ := exists_h1_max_sub_const hU u M
  let w := positivePartTest htrace
  have hfun : w.toH1Function.toFun = v.toFun := by
    rw [positivePartTest_toFun, hvfun]
  have hcoord : ∀ i : Fin d,
      (fun x => w.toH1Function.grad x i) =ᵐ[volumeMeasureOn U]
        fun x => v.grad x i := by
    intro i
    apply HasWeakPartialDerivOn.ae_eq hU.isOpen
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict
        ((w.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
    · exact locallyIntegrableOn_of_locallyIntegrable_restrict
        ((v.gradMemL2 i).locallyIntegrable (by norm_num))
    · exact w.toH1Function.hasWeakPartialDerivOn i
    · rw [hfun]
      exact v.hasWeakPartialDerivOn i
  filter_upwards [ae_all_iff.mpr hcoord, hvgrad] with x hx hvx
  rw [← hvx]
  funext i
  exact hx i

/-- Weak maximum principle: a solution of `-div (a grad u) + (alpha + q) u = 0`
whose positive part above a nonnegative level has zero trace lies below that
level almost everywhere. -/
theorem ae_le_of_positivePart_zeroTrace (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam alpha M : ℝ} {q : Vec d → ℝ}
    {u : H1Function U} (halpha : 0 < alpha) (hM : 0 ≤ M)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hq : ∀ᵐ x ∂volumeMeasureOn U, 0 ≤ q x)
    (hsol : IsScalarForcedWeakSolution a U
      (fun x => -((alpha + q x) * u.toFun x)) u)
    (htrace : MemH10 U (fun x => max (u.toFun x - M) 0)) :
    ∀ᵐ x ∂volumeMeasureOn U, u.toFun x ≤ M := by
  classical
  let mu := volumeMeasureOn U
  let w := positivePartTest htrace
  let p : Vec d → ℝ := fun x => max (u.toFun x - M) 0
  have hwfun : w.toH1Function.toFun = p := positivePartTest_toFun htrace
  have hwgrad := positivePartTest_grad_ae hU htrace
  have hpL2 : MemScalarL2 U p := by
    have := w.toH1Function.memL2
    rwa [hwfun] at this
  have hforcingInt : Integrable (fun x =>
      (-((alpha + q x) * u.toFun x)) * w.toH1Function.toFun x) mu :=
    hsol.1.integrable_mul w.toH1Function.memL2
  have hsqInt : Integrable (fun x => p x ^ 2) mu := by
    apply (hpL2.integrable_mul hpL2).congr
    filter_upwards with x
    simp only [Pi.mul_apply]
    ring
  have hmem : ∀ᵐ x ∂mu, x ∈ U :=
    (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
      (Filter.Eventually.of_forall fun _ hx => hx)
  have hleft : 0 ≤ ∫ x, vecDot (matVecMul (a x) (u.grad x))
      (w.toH1Function.grad x) ∂mu := by
    apply integral_nonneg_of_ae
    filter_upwards [hmem, hwgrad] with x hx hgx
    rw [hgx, Set.indicator_apply]
    split_ifs
    · have hquad := lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx)
        (u.grad x)
      rw [vecDot_matVecMul_symmPart] at hquad
      rw [vecDot_comm]
      exact le_trans (mul_nonneg (hEll.2 x hx).1.le (vecNormSq_nonneg _)) hquad
    · simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, le_refl]
  have hright : (∫ x, (-((alpha + q x) * u.toFun x)) *
      w.toH1Function.toFun x ∂mu) ≤ -(alpha * ∫ x, p x ^ 2 ∂mu) := by
    rw [← integral_const_mul, ← integral_neg]
    apply integral_mono_ae hforcingInt (hsqInt.const_mul alpha).neg
    filter_upwards [hq] with x hqx
    rw [hwfun]
    by_cases hlevel : M < u.toFun x
    · have hp : p x = u.toFun x - M := by
        simp only [p, max_eq_left (by linarith only [hlevel] : (0:ℝ) ≤ u.toFun x - M)]
      have hu0 : 0 ≤ u.toFun x := by linarith only [hlevel, hM]
      have hpnn : 0 ≤ p x := by rw [hp]; linarith only [hlevel]
      have h1 : alpha * (p x * p x) ≤ alpha * (u.toFun x * p x) := by
        apply mul_le_mul_of_nonneg_left _ halpha.le
        apply mul_le_mul_of_nonneg_right _ hpnn
        rw [hp]; linarith only [hM]
      have h2 : 0 ≤ q x * (u.toFun x * p x) :=
        mul_nonneg hqx (mul_nonneg hu0 hpnn)
      calc
        (-((alpha + q x) * u.toFun x)) * p x =
            -(alpha * (u.toFun x * p x)) - q x * (u.toFun x * p x) := by ring
        _ ≤ -(alpha * (p x * p x)) := by linarith only [h1, h2]
        _ = -(alpha * p x ^ 2) := by ring
    · have hp : p x = 0 :=
        max_eq_right (by linarith only [not_lt.1 hlevel])
      simp only [Pi.neg_apply, hp, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, neg_zero, le_refl]
  have hzero : (∫ x, p x ^ 2 ∂mu) ≤ 0 := by
    have hchain := hsol.2 w
    change (∫ x, vecDot (matVecMul (a x) (u.grad x))
        (w.toH1Function.grad x) ∂mu) =
      ∫ x, (-((alpha + q x) * u.toFun x)) * w.toH1Function.toFun x ∂mu at hchain
    rw [hchain] at hleft
    have hprod : 0 ≤ -(alpha * ∫ x, p x ^ 2 ∂mu) := le_trans hleft hright
    nlinarith only [hprod, halpha]
  have hnonneg : ∀ᵐ x ∂mu, 0 ≤ p x :=
    Filter.Eventually.of_forall fun x => le_max_right _ _
  have hpzero : p =ᵐ[mu] 0 := by
    have hge : 0 ≤ ∫ x, p x ^ 2 ∂mu := by
      apply integral_nonneg_of_ae
      filter_upwards with x
      positivity
    have heq : (∫ x, p x ^ 2 ∂mu) = 0 := le_antisymm hzero hge
    have hsq : (fun x => p x ^ 2) =ᵐ[mu] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hsqInt).1 heq
      filter_upwards with x
      positivity
    filter_upwards [hsq] with x hx
    have hx2 : p x ^ 2 = 0 := hx
    exact sq_eq_zero_iff.1 hx2
  filter_upwards [hpzero] with x hx
  have hx0 : max (u.toFun x - M) 0 = 0 := hx
  linarith only [le_of_max_le_left hx0.le]

end DivergenceFormProcess.Decay
