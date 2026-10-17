/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.Superdiffusion.Support.Sobolev.Truncation.MatchedTrace
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareZeroTrace
public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.Stampacchia.LevelEnergy

/-!
# ScalarWeakMaximumPrinciple

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weak maximum principle for the divergence-form equation

Let `Y` solve `-div (a grad Y) = 0` weakly on a bounded convex domain `U` and let `q` be an
`H¹` function of `U` with `Y - q ∈ H¹₀(U)`; that is, `Y` and `q` have the same trace.  Then `Y`
is almost everywhere bounded by the pointwise bounds of `q`.

The proof is the standard energy test at the truncation `(Y - M)₊`.  Three inputs are used:

* the truncation itself, `exists_h1_max_sub_const`, whose gradient is `1_{Y > M} grad Y`;
* the matched-trace truncation `memH10_max_sub_matched`, which places `(Y - M)₊ - (q - M)₊` in
  `H¹₀(U)`; the second summand vanishes identically because `q ≤ M` everywhere, so the
  truncation is itself an admissible test function;
* the zero-trace Poincare inequality, which turns a vanishing gradient into a vanishing value.

Testing the equation against the truncation `w` gives `∫ (a grad Y) · grad w = 0`, and
`grad w = 1_{Y > M} grad Y` makes the integrand equal to `(a grad w) · grad w` pointwise, whose
integral is at least `lam ∫ |grad w|²` by ellipticity.  Hence `grad w = 0` almost everywhere,
hence `w = 0` almost everywhere, which is `Y ≤ M` almost everywhere.

No shift, no symmetry of the coefficient field and no continuity of any representative is used.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-! ## Two structural facts -/

/-- **The scalar-forced weak equation is odd.**  Negating the solution negates the forcing. -/
theorem IsScalarForcedWeakSolution.neg {a : CoeffField d} {g : Vec d → ℝ} {u : H1Function U}
    (h : IsScalarForcedWeakSolution a U g u) :
    IsScalarForcedWeakSolution a U (fun x ↦ -g x) (-u) := by
  refine ⟨h.1.neg, fun phi ↦ ?_⟩
  calc
    ∫ x in U, vecDot (matVecMul (a x) ((-u).grad x))
        (phi.toH1Function.grad x) ∂volume =
        ∫ x in U, -vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [H1Function.neg_grad]
      simp only [vecDot, matVecMul, Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
    _ = -∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := integral_neg _
    _ = -∫ x in U, g x * phi.toH1Function.toFun x ∂volume := by rw [h.2 phi]
    _ = ∫ x in U, (-g x) * phi.toH1Function.toFun x ∂volume := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards with x
      ring

/-- The zero-trace value function of a zero-trace Sobolev witness with an almost everywhere
vanishing gradient vanishes almost everywhere. -/
private theorem ae_eq_zero_of_ae_grad_eq_zero [NeZero d]
    (hU : IsOpenBoundedConvexDomain U) (W : H10Function U)
    (hgrad : ∀ᵐ x ∂volumeMeasureOn U, W.toH1Function.grad x = 0) :
    W.toH1Function.toFun =ᵐ[volumeMeasureOn U] fun _ ↦ (0 : ℝ) := by
  have hzero : W.toH1Function.gradToVectorL2 = 0 := by
    refine MeasureTheory.Lp.ext (μ := volumeMeasureOn U) ?_
    filter_upwards [H1Function.coeFn_gradToVectorL2 W.toH1Function, hgrad,
      MeasureTheory.Lp.coeFn_zero (E := Vec d) (p := 2) (μ := volumeMeasureOn U)]
      with x hx hgx hz
    simp only [hx, hgx, hz, Pi.zero_apply]
  have hvalue : W.toH1Function.toScalarL2 = 0 :=
    H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
      (H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hU) W hzero
  filter_upwards [W.toH1Function.coeFn_toScalarL2,
    MeasureTheory.Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volumeMeasureOn U)] with x hx hz
  simp only [← hx, hvalue, hz, Pi.zero_apply]

/-! ## The one-sided maximum principle -/

/-- **The weak maximum principle, one-sided.**  A weakly `a`-harmonic function whose trace is
that of a function bounded above by `M` is almost everywhere bounded above by `M`. -/
theorem ae_le_of_isScalarForcedWeakSolution_zero [NeZero d]
    (hU : IsOpenBoundedConvexDomain U) {a : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {Y : H1Function U} (hY : IsScalarForcedWeakSolution a U (fun _ ↦ (0 : ℝ)) Y)
    {q : H1Function U} (hq : MemH10 U fun x ↦ Y.toFun x - q.toFun x)
    {M : ℝ} (hM : ∀ x, q.toFun x ≤ M) :
    ∀ᵐ x ∂volumeMeasureOn U, Y.toFun x ≤ M := by
  obtain ⟨w, hwfun, hwgrad⟩ := exists_h1_max_sub_const hU Y M
  -- the truncation is an admissible test function
  have hmatched : MemH10 U w.toFun := by
    have h := memH10_max_sub_matched hU Y q hq M
    have hEq : (fun x ↦ max (Y.toFun x - M) 0 - max (q.toFun x - M) 0) = w.toFun := by
      funext x
      rw [hwfun, max_eq_right (by linarith only [hM x] : q.toFun x - M ≤ 0), sub_zero]
    rwa [hEq] at h
  obtain ⟨W, hW⟩ := hmatched
  -- the gradient of the test function agrees with that of the truncation
  have hWgrad : W.toH1Function.grad =ᵐ[volumeMeasureOn U] w.grad :=
    h1grad_ae_eq_of_toFun_ae_eq hU.isOpen (Filter.Eventually.of_forall fun x ↦ congrFun hW x)
  -- the energy identity
  have htest := hY.2 W
  have hrhs : ∫ x in U, (fun _ ↦ (0 : ℝ)) x * W.toH1Function.toFun x ∂volume = 0 := by
    simp only [zero_mul, integral_zero]
  rw [hrhs] at htest
  have hpair : ∫ x in U, vecDot (matVecMul (a x) (w.grad x)) (w.grad x) ∂volume = 0 := by
    rw [← htest]
    refine integral_congr_ae ?_
    filter_upwards [hWgrad, hwgrad] with x hx hgx
    rw [hx, hgx]
    by_cases hmem : x ∈ {y | M < Y.toFun y}
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      simp only [vecDot, matVecMul, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  -- ellipticity forces the truncated gradient to vanish
  have hflux : MemVectorL2 U (fun x ↦ matVecMul (a x) (w.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2
  have hpairInt : Integrable (fun x ↦ vecDot (matVecMul (a x) (w.grad x)) (w.grad x))
      (volumeMeasureOn U) :=
    integrableOn_vecDot_of_memVectorL2 hflux w.grad_memVectorL2
  have hnormInt : Integrable (fun x ↦ vecNormSq (w.grad x)) (volumeMeasureOn U) := by
    refine (integrableOn_vecDot_of_memVectorL2 w.grad_memVectorL2 w.grad_memVectorL2).congr ?_
    filter_upwards with x
    rfl
  have hlower : ∀ᵐ x ∂volumeMeasureOn U,
      lam * vecNormSq (w.grad x) ≤ vecDot (matVecMul (a x) (w.grad x)) (w.grad x) := by
    have hmem : ∀ᵐ x ∂volumeMeasureOn U, x ∈ U :=
      (ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun _ hx ↦ hx)
    filter_upwards [hmem] with x hx
    have hquad := lowerBound_symmPart_of_isEllipticMatrix (hEll.2 x hx) (w.grad x)
    rw [vecDot_matVecMul_symmPart] at hquad
    rwa [vecDot_comm]
  have hintLe : lam * ∫ x in U, vecNormSq (w.grad x) ∂volume ≤ 0 := by
    rw [← integral_const_mul, ← hpair]
    exact integral_mono_ae (hnormInt.const_mul lam) hpairInt hlower
  have hintNonneg : 0 ≤ ∫ x in U, vecNormSq (w.grad x) ∂volume :=
    integral_nonneg fun x ↦ vecNormSq_nonneg _
  have hintZero : ∫ x in U, vecNormSq (w.grad x) ∂volume = 0 := by
    nlinarith only [hintLe, hintNonneg, hlam]
  have hgradZero : ∀ᵐ x ∂volumeMeasureOn U, w.grad x = 0 := by
    have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ vecNormSq_nonneg (w.grad x))
      hnormInt).1 hintZero
    filter_upwards [hae] with x hx
    have hx0 : vecNormSq (w.grad x) = 0 := hx
    exact vecNormSq_eq_zero hx0
  -- the Poincare inequality closes the argument
  have hWgradZero : ∀ᵐ x ∂volumeMeasureOn U, W.toH1Function.grad x = 0 := by
    filter_upwards [hWgrad, hgradZero] with x hx hgx
    rw [hx, hgx]
  have hWzero := ae_eq_zero_of_ae_grad_eq_zero hU W hWgradZero
  filter_upwards [hWzero] with x hx
  have hwx : max (Y.toFun x - M) 0 = 0 := by
    rw [← congrFun hwfun x, ← congrFun hW x]
    exact hx
  have hle : Y.toFun x - M ≤ 0 := by
    have := le_max_left (Y.toFun x - M) 0
    rw [hwx] at this
    exact this
  linarith only [hle]

/-! ## The two-sided maximum principle -/

/-- **The weak maximum principle.**  A weakly `a`-harmonic function whose trace is that of a
function bounded by `M` in absolute value is almost everywhere bounded by `M` in absolute
value. -/
theorem ae_abs_le_of_isScalarForcedWeakSolution_zero [NeZero d]
    (hU : IsOpenBoundedConvexDomain U) {a : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U a)
    {Y : H1Function U} (hY : IsScalarForcedWeakSolution a U (fun _ ↦ (0 : ℝ)) Y)
    {q : H1Function U} (hq : MemH10 U fun x ↦ Y.toFun x - q.toFun x)
    {M : ℝ} (hM : ∀ x, |q.toFun x| ≤ M) :
    ∀ᵐ x ∂volumeMeasureOn U, |Y.toFun x| ≤ M := by
  have hupper := ae_le_of_isScalarForcedWeakSolution_zero hU hlam hEll hY hq
    (fun x ↦ (le_abs_self (q.toFun x)).trans (hM x))
  have hnegY : IsScalarForcedWeakSolution a U (fun _ ↦ (0 : ℝ)) (-Y) := by
    simpa only [neg_zero] using hY.neg
  have hnegq : MemH10 U fun x ↦ (-Y).toFun x - (-q).toFun x := by
    have heq : (fun x ↦ (-Y).toFun x - (-q).toFun x) =
        fun x ↦ -(Y.toFun x - q.toFun x) := by
      funext x
      simp only [H1Function.neg_toFun]
      ring
    rw [heq]
    exact memH10_neg hq
  have hlowerBound := ae_le_of_isScalarForcedWeakSolution_zero hU hlam hEll hnegY hnegq
    (q := -q) (M := M) (fun x ↦ by
      rw [H1Function.neg_toFun]
      exact (neg_le_abs (q.toFun x)).trans (hM x))
  filter_upwards [hupper, hlowerBound] with x hx hx'
  rw [H1Function.neg_toFun] at hx'
  exact abs_le.mpr ⟨by linarith only [hx'], hx⟩

end

end DivergenceFormProcess.Form
