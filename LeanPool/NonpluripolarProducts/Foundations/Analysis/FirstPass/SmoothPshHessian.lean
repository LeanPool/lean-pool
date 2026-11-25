/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.LocalPotentialIndependence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.MongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshDiscLocalGlobal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.CircleMeanSecondOrder

/-!
# The coordinate Hessian of a smooth PSH function is semipositive

This file proves the missing direction of the smooth Levi criterion on an
open subset of the finite-dimensional complex model.  Smoothness is only
assumed on the open set: at each point a bump function supplies a globally
smooth representative of the germ before the complex-line Laplacian theorem
is applied.
-/

@[expose] public section

noncomputable section

open Set Filter Laplacian MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder BigOperators

namespace SGPT.Foundations.Analysis.FirstPass

open MongeAmpere

variable {n : ℕ}

/-- The vector formed by combining the coordinate vectors with conjugate coefficients. -/
def conjugateCoordinateCombination (x : Fin n → ℂ) : ComplexModel n :=
  ∑ j, ((x j).re • coordinateVector j -
    (x j).im • (Complex.I • coordinateVector j))

theorem conjugateCoordinateCombination_star (v : ComplexModel n) :
    conjugateCoordinateCombination (fun i ↦ star (v i)) = v := by
  ext i
  simp only [conjugateCoordinateCombination, coordinateVector, WithLp.ofLp_sub, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single i (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
  simp [Complex.re_add_im]

private theorem I_smul_conjugateCoordinateCombination (x : Fin n → ℂ) :
    Complex.I • conjugateCoordinateCombination x =
      ∑ j, ((x j).im • coordinateVector j +
        (x j).re • (Complex.I • coordinateVector j)) := by
  unfold conjugateCoordinateCombination
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_sub, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rw [← sub_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

/-- The quadratic form of the coordinate complex Hessian is the Levi form of
the vector having the conjugate coordinate tuple. -/
theorem complexHessian_dotProduct_mulVec_eq_leviForm
    {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (x : Fin n → ℂ) :
    star x ⬝ᵥ ((complexHessian u z).mulVec x) =
      (leviForm u z (conjugateCoordinateCombination x) : ℂ) := by
  apply Complex.ext
  · simp only [leviForm, Complex.ofReal_re]
    rw [show Complex.I • conjugateCoordinateCombination x = _ from
      I_smul_conjugateCoordinateCombination x]
    simp [dotProduct, Matrix.mulVec, complexHessian,
      conjugateCoordinateCombination, realHessian_eq_fderiv,
      Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, smul_eq_mul]
    ring_nf
    simp_rw [Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [Finset.sum_mul]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simpa using (complexHessian_isHermitian hu).im_star_dotProduct_mulVec_self x

/-- A real-valued smooth PSH function has nonnegative Levi form in every
direction.  Only open-domain smoothness is assumed; a globally smooth
representative is constructed separately at each germ. -/
theorem leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
    {U : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hs : ContDiffOn ℝ ∞ u U)
    (hp : PlurisubharmonicOn (fun z ↦ (u z : EReal)) U)
    {z : ComplexModel n} (hz : z ∈ U) (v : ComplexModel n) :
    0 ≤ leviForm u z v := by
  obtain ⟨g, hg, heq⟩ :=
    exists_contDiff_eventuallyEq_of_contDiffOn U.isOpen hs hz
  have hnhd : {y | u y = g y} ∩ (U : Set (ComplexModel n)) ∈ 𝓝 z :=
    inter_mem heq (U.isOpen.mem_nhds hz)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhd
  have hballEq : ∀ y ∈ Metric.ball z ε, u y = g y :=
    fun y hy ↦ (hball hy).1
  have hballU : Metric.ball z ε ⊆ U :=
    fun y hy ↦ (hball hy).2
  obtain ⟨R, hR, L, hL, hLball, _, hdiscs⟩ :=
    exists_compact_affineClosedDisc_family isCompact_singleton Metric.isOpen_ball
      (singleton_subset_iff.mpr (Metric.mem_ball_self hε)) v
  have hpdisc : DiscPshOn (fun y ↦ (u y : EReal)) U :=
    SGPT.Foundations.Analysis.PlurisubharmonicOn.discPshOn hp
  have hmean : ∀ r ∈ Ioo 0 R,
      g z ≤ Real.circleAverage (fun ζ : ℂ ↦ g (z + ζ • v)) 0 r := by
    intro r hr
    have hDball : affineClosedDisc z v r ⊆ Metric.ball z ε :=
      (hdiscs z (mem_singleton z) r hr.2.le).trans hLball
    have hDU : affineClosedDisc z v r ⊆ U := hDball.trans hballU
    obtain ⟨C, hC⟩ := hpdisc.exists_disc_upper_bound z v hr.1.le hDU
    have hpoint (t : ℝ) :
        u (z + circleMap 0 r t • v) = g (z + circleMap 0 r t • v) :=
      hballEq _ (hDball (circle_mem_affineClosedDisc z v hr.1.le t))
    have hcircg : Continuous (fun t : ℝ ↦ g (z + circleMap 0 r t • v)) := by
      fun_prop
    have hint : IntervalIntegrable
        (fun t : ℝ ↦ u (z + circleMap 0 r t • v)) volume 0 (2 * Real.pi) := by
      have hfun : (fun t : ℝ ↦ u (z + circleMap 0 r t • v)) =
          fun t : ℝ ↦ g (z + circleMap 0 r t • v) := funext hpoint
      rw [hfun]
      exact hcircg.intervalIntegrable _ _
    have hsub := hpdisc.submean z v r hr.1 hDU C hC
    have hmeanU : u z ≤ Real.circleAverage (fun ζ : ℂ ↦ u (z + ζ • v)) 0 r :=
      (circleDeficit_coe_le_iff z v r C hint
        (fun t ↦ EReal.coe_le_coe_iff.mp
          (hC _ (circle_mem_affineClosedDisc z v hr.1.le t)))
        (EReal.coe_le_coe_iff.mp
          (hC z (center_mem_affineClosedDisc z v hr.1.le)))).mp hsub
    have havg : Real.circleAverage (fun ζ : ℂ ↦ u (z + ζ • v)) 0 r =
        Real.circleAverage (fun ζ : ℂ ↦ g (z + ζ • v)) 0 r := by
      unfold Real.circleAverage
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      exact hpoint t
    rw [hballEq z (Metric.mem_ball_self hε), havg] at hmeanU
    exact hmeanU
  have hg2 : ContDiff ℝ 2 g :=
    hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hline : ContDiff ℝ 2 (fun ζ : ℂ ↦ g (z + ζ • v)) :=
    hg2.comp (contDiff_const.add (complexLineLinear v).contDiff)
  have hlap : 0 ≤ Δ (fun ζ : ℂ ↦ g (z + ζ • v)) 0 :=
    laplacian_nonneg_of_circleAverage_submean hline 0 hR (by simpa using hmean)
  have hlevig : 0 ≤ leviForm g z v := by
    simpa using (laplacian_complexLine_nonneg_iff hg2 z v 0).mp hlap
  have hsecond : fderiv ℝ (fderiv ℝ u) z = fderiv ℝ (fderiv ℝ g) z :=
    heq.fderiv.fderiv_eq
  have hlevi : leviForm u z v = leviForm g z v := by
    simp only [leviForm, realHessian_eq_fderiv, hsecond]
  rwa [hlevi]

namespace MongeAmpere

/-- Smooth plurisubharmonicity on an open domain already supplies the genuine
coordinate-Hessian semipositivity certificate. -/
theorem isSmoothPshOn_of_psh {U : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hs : ContDiffOn ℝ ∞ u U)
    (hp : PlurisubharmonicOn (fun z ↦ (u z : EReal)) U) :
    IsSmoothPshOn U u := by
  refine ⟨hs, hp, ?_⟩
  intro z hz
  have hs2 : ContDiffAt ℝ 2 u z :=
    ((hs z hz).contDiffAt (U.isOpen.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact complexHessian_isHermitian hs2
  · intro x
    rw [complexHessian_dotProduct_mulVec_eq_leviForm hs2 x]
    exact Complex.nonneg_iff.mpr
      ⟨leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hs hp hz _, rfl⟩

end MongeAmpere

end SGPT.Foundations.Analysis.FirstPass
