/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.Representative
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Continuity
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ConvexApproxSmoothing.WeakDerivSmoothing
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# LipschitzRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A bounded weak gradient produces a Lipschitz representative

A function with a weak gradient bounded by `K` on a bounded open convex set
agrees, away from a null set, with a Lipschitz function.  The Lipschitz constant
is `d · K`: the ambient norm on `Vec d = Fin d → ℝ` is the supremum norm, the
gradient bound `‖∇u x‖ ≤ K` therefore bounds each partial derivative by `K`, and
the operator norm of the differential on `(Fin d → ℝ, ‖·‖_∞)` is the sum of the
`d` partial derivatives.  The factor `d` is sharp, attained by a linear function
whose `d` partial derivatives all equal `K`.

## Route

Mollification.  The convex smoothing operator produces smooth approximants whose
classical partial derivatives agree, away from a null set, with the smoothed
weak partial derivatives; both sides are continuous, so on an open set the
identity holds at every point.  The mollifier is nonnegative with unit mass, so
the smoothed partials inherit the bound `K` pointwise, and the mean value
theorem makes every approximant `d·K`-Lipschitz on the convex set.  The
approximants converge in `L²`, hence in measure, hence pointwise away from a
null set along a subsequence; a pointwise limit of `d·K`-Lipschitz functions is
`d·K`-Lipschitz on the set where the limit exists, and a real-valued Lipschitz
function on a subset extends to a Lipschitz function on the whole space.

## Main results

* `exists_lipschitzWith_representative_of_hasWeakGradientOn`.

## References

* CoarseGraining, `Homogenization/Sobolev/W1p/ConvexApproxSmoothing/`.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The mollified field inherits a pointwise bound -/

/-- A nonnegative unit-mass mollifier does not increase a pointwise bound. -/
theorem abs_convexApproxSmoothRepresentative_le {V : Set (Vec d)} {rho g : Vec d → ℝ}
    (hrho : IsConvexApproxKernel rho) {K : ℝ} (hK : 0 ≤ K)
    (hg : ∀ x ∈ V, |g x| ≤ K) {x0 : Vec d} {r ep : ℝ} (hepr : 0 < ep * r) (x : Vec d) :
    |convexApproxSmoothRepresentative V rho g x0 r ep x| ≤ K := by
  have hk0 : ∀ z, 0 ≤ scaledConvexApproxKernel rho (ep * r) z :=
    scaledConvexApproxKernel_nonneg hrho hepr
  have hkint : Integrable (scaledConvexApproxKernel rho (ep * r)) :=
    integrable_scaledConvexApproxKernel hrho hepr
  have hk1 : ∫ z, scaledConvexApproxKernel rho (ep * r) z = 1 :=
    integral_scaledConvexApproxKernel hrho hepr
  have hind : ∀ w, |Set.indicator V g w| ≤ K := by
    intro w
    by_cases hw : w ∈ V
    · rw [Set.indicator_of_mem hw]
      exact hg w hw
    · rw [Set.indicator_of_notMem hw]
      simpa using hK
  set w : Vec d := (1 - ep) • x + ep • x0 with hw
  have hbound : ∀ z : Vec d,
      ‖(ContinuousLinearMap.lsmul ℝ ℝ (scaledConvexApproxKernel rho (ep * r) z))
          (Set.indicator V g (w - z))‖ ≤
        scaledConvexApproxKernel rho (ep * r) z * K := by
    intro z
    have : ‖(ContinuousLinearMap.lsmul ℝ ℝ (scaledConvexApproxKernel rho (ep * r) z))
        (Set.indicator V g (w - z))‖ =
        scaledConvexApproxKernel rho (ep * r) z * |Set.indicator V g (w - z)| := by
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hk0 z)]
    rw [this]
    exact mul_le_mul_of_nonneg_left (hind _) (hk0 z)
  have hcalc :
      ‖∫ z, (ContinuousLinearMap.lsmul ℝ ℝ (scaledConvexApproxKernel rho (ep * r) z))
          (Set.indicator V g (w - z))‖ ≤
        ∫ z, scaledConvexApproxKernel rho (ep * r) z * K :=
    norm_integral_le_of_norm_le (hkint.mul_const K) (Filter.Eventually.of_forall hbound)
  rw [integral_mul_const, hk1, one_mul] at hcalc
  simpa only [convexApproxSmoothRepresentative, convolution_def, Real.norm_eq_abs, hw]
    using hcalc

/-! ## 2. Every approximant is `d · K`-Lipschitz on the domain -/

private theorem sum_smul_basisVec (h : Vec d) : (∑ i, h i • basisVec i) = h := by
  funext j
  simp [basisVec, Finset.sum_apply, Pi.single_apply]

/-- On the supremum-norm carrier the operator norm of a differential is bounded
by `d` times the bound on the individual partial derivatives. -/
private theorem opNorm_le_of_apply_basisVec_le {F : Vec d → ℝ} {x : Vec d} {K : ℝ}
    (hK : 0 ≤ K) (hbd : ∀ i, |fderiv ℝ F x (basisVec i)| ≤ K) :
    ‖fderiv ℝ F x‖ ≤ (d : ℝ) * K := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have hsum : fderiv ℝ F x h = ∑ i, h i * fderiv ℝ F x (basisVec i) := by
    conv_lhs => rw [← sum_smul_basisVec h]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp [smul_eq_mul]
  rw [hsum, Real.norm_eq_abs]
  calc |∑ i, h i * fderiv ℝ F x (basisVec i)|
      ≤ ∑ i, |h i * fderiv ℝ F x (basisVec i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖h‖ * K := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h i)
          (hbd i) (abs_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * K * ‖h‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ## 3. The representative -/

/-- **A bounded weak gradient produces a Lipschitz representative.**

If `u` has weak gradient `G` on a nonempty bounded open convex set `V` and
`‖G x‖ ≤ K` everywhere, then `u` agrees away from a null set with a function
that is `d · K`-Lipschitz on the whole space.  The factor `d` is the price of
the supremum norm on `Vec d` and is sharp. -/
theorem exists_lipschitzWith_representative_of_hasWeakGradientOn
    {V : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V) (hVne : V.Nonempty)
    {u : Vec d → ℝ} {G : Vec d → Vec d} {K : ℝ} (hK : 0 ≤ K)
    (hu : MemLpOn V 2 u) (hG : ∀ i : Fin d, MemLpOn V 2 (fun x => G x i))
    (hweak : HasWeakGradientOn V u G) (hGbd : ∀ x, ‖G x‖ ≤ K) :
    ∃ uRep : Vec d → ℝ,
      LipschitzWith (Real.toNNReal ((d : ℝ) * K)) uRep ∧
        u =ᵐ[volume.restrict V] uRep := by
  classical
  have hrho : IsConvexApproxKernel (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  obtain ⟨x0, hx0⟩ := hVne
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.1 hV.isOpen x0 hx0
  have hr : 0 < r0 / 2 := by positivity
  have hball : Metric.closedBall x0 (r0 / 2) ⊆ V := by
    refine subset_trans (fun z hz => ?_) hball0
    exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (by linarith))
  have heps0 : ∀ m : ℕ, 0 < unitConvexApproxScale (m + 1) := by
    intro m
    dsimp [unitConvexApproxScale]
    positivity
  have heps1 : ∀ m : ℕ, unitConvexApproxScale (m + 1) < 1 := by
    intro m
    dsimp [unitConvexApproxScale]
    rw [div_lt_one (by positivity)]
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hGi : ∀ (i : Fin d) (x : Vec d), |G x i| ≤ K := by
    intro i x
    calc |G x i| = ‖G x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖G x‖ := norm_le_pi_norm (G x) i
      _ ≤ K := hGbd x
  have hlip : ∀ m : ℕ,
      LipschitzOnWith (Real.toNNReal ((d : ℝ) * K))
        (convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d)) u x0 (r0 / 2)
          (unitConvexApproxScale (m + 1))) V := by
    intro m
    have hsmoothu : ContDiff ℝ (⊤ : ℕ∞)
        (convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d)) u x0 (r0 / 2)
          (unitConvexApproxScale (m + 1))) :=
      contDiff_convexApproxSmoothRepresentative hV.isOpen.measurableSet hrho one_le_two hu hr
        (heps0 m)
    refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => (hsmoothu.differentiable (by simp)).differentiableAt) ?_ hV.convex
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    refine opNorm_le_of_apply_basisVec_le hK fun i => ?_
    have haeq :
        (fun z => fderiv ℝ (convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
            u x0 (r0 / 2) (unitConvexApproxScale (m + 1))) z (basisVec i))
          =ᵐ[volume.restrict V]
          fun z => (1 - unitConvexApproxScale (m + 1)) *
            convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
              (fun w => G w i) x0 (r0 / 2) (unitConvexApproxScale (m + 1)) z :=
      ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec hV hrho one_le_two hu (hG i)
        (hweak i) hball hr (heps0 m) (heps1 m)
    have hcont1 : ContinuousOn (fun z =>
        fderiv ℝ (convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
          u x0 (r0 / 2) (unitConvexApproxScale (m + 1))) z (basisVec i)) V :=
      (((hsmoothu.continuous_fderiv (by simp)).clm_apply continuous_const)).continuousOn
    have hcont2 : ContinuousOn (fun z => (1 - unitConvexApproxScale (m + 1)) *
        convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
          (fun w => G w i) x0 (r0 / 2) (unitConvexApproxScale (m + 1)) z) V :=
      (continuous_const.mul (contDiff_convexApproxSmoothRepresentative
        hV.isOpen.measurableSet hrho one_le_two (hG i) hr (heps0 m)).continuous).continuousOn
    have hEqAt : fderiv ℝ (convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
          u x0 (r0 / 2) (unitConvexApproxScale (m + 1))) x (basisVec i) =
        (1 - unitConvexApproxScale (m + 1)) *
          convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
            (fun w => G w i) x0 (r0 / 2) (unitConvexApproxScale (m + 1)) x :=
      eqOn_of_ae_eq_of_continuousOn hV.isOpen haeq hcont1 hcont2 hx
    rw [hEqAt]
    have hinner := abs_convexApproxSmoothRepresentative_le (V := V) hrho hK
      (fun z _ => hGi i z) (x0 := x0) (r := r0 / 2)
      (mul_pos (heps0 m) hr) x
    rw [abs_mul, abs_of_nonneg (by linarith [(heps1 m).le, (heps0 m).le] :
      (0 : ℝ) ≤ 1 - unitConvexApproxScale (m + 1))]
    calc (1 - unitConvexApproxScale (m + 1)) *
          |convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
            (fun w => G w i) x0 (r0 / 2) (unitConvexApproxScale (m + 1)) x|
        ≤ 1 * K := by
          refine mul_le_mul (by linarith [(heps0 m)]) hinner (abs_nonneg _) zero_le_one
      _ = K := one_mul K
  have hkey : ∀ (m : ℕ), ∀ x ∈ V, ∀ z ∈ V,
      |unitConvexApproxSequence u x0 (r0 / 2) (m + 1) x -
        unitConvexApproxSequence u x0 (r0 / 2) (m + 1) z| ≤ (d : ℝ) * K * ‖x - z‖ := by
    intro m x hx z hz
    have hFx := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u) hV hrho hx hball hr (heps0 m) (heps1 m)
    have hFz := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u) hV hrho hz hball hr (heps0 m) (heps1 m)
    have hd := (hlip m).dist_le_mul x hx z hz
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity), hFx, hFz] at hd
    exact hd
  have hconv0 := tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
    (u := u) (p := 2) hV one_le_two (by norm_num) hu hball hr
  have hconv : Filter.Tendsto
      (fun m : ℕ => eLpNorm
        (fun x => unitConvexApproxSequence u x0 (r0 / 2) (m + 1) x - u x) 2
        (volume.restrict V)) Filter.atTop (nhds 0) :=
    hconv0.comp (Filter.tendsto_add_atTop_nat 1)
  have hTIM : TendstoInMeasure (volume.restrict V)
      (fun m : ℕ => unitConvexApproxSequence u x0 (r0 / 2) (m + 1)) Filter.atTop u := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞)) (by norm_num) ?_
    simpa using! hconv
  obtain ⟨ns, -, hae⟩ := hTIM.exists_seq_tendsto_ae
  have hlipS : LipschitzOnWith (Real.toNNReal ((d : ℝ) * K)) u
      {x | x ∈ V ∧ Filter.Tendsto
        (fun i => unitConvexApproxSequence u x0 (r0 / 2) (ns i + 1) x) Filter.atTop
          (nhds (u x))} := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx z hz => ?_
    have hlim : Filter.Tendsto (fun i =>
        |unitConvexApproxSequence u x0 (r0 / 2) (ns i + 1) x -
          unitConvexApproxSequence u x0 (r0 / 2) (ns i + 1) z|) Filter.atTop
        (nhds |u x - u z|) := (hx.2.sub hz.2).abs
    have hle : |u x - u z| ≤ (d : ℝ) * K * ‖x - z‖ :=
      le_of_tendsto hlim (Filter.Eventually.of_forall fun i => hkey (ns i) x hx.1 z hz.1)
    rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  obtain ⟨uRep, hRepLip, hEq⟩ := hlipS.extend_real
  refine ⟨uRep, hRepLip, ?_⟩
  filter_upwards [hae, ae_restrict_mem hV.isOpen.measurableSet] with x hx1 hx2
  exact hEq ⟨hx2, hx1⟩

end

end Algsuperdiff.Section5.Support
