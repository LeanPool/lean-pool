/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.FoldNorm
public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.FoldTransport
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Truncation.WeakGradientLimit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.Cutoff.Box
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.PoincareMeanZero

/-!
# Coarse-graining support: Support.Sobolev.CubeEmbedding.Extension

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

namespace HCPolySupport

open MeasureTheory HCPolySupport HCPolySupport.H1Function
open scoped ENNReal NNReal BigOperators Topology

/-!
# Even-fold extension of an `H¹(box)` function

Given `u ∈ H¹(Box lo hi)`, its even-fold extension `Eu (x) = u (Fold lo hi x)`
(with the signed folded gradient) is an `H¹(Box3 lo hi)` function whose `L²`
norms on the tripled box are controlled by `(3^d)^{1/2}` times the `L²` norms of
`u` on the base box, and which agrees with `u` a.e. on the base box.

The construction feeds the globally smooth `convexApproxSmoothH1` approximants of
`u`, cut off to compact support, through the per-approximant fold weak-gradient
identity (`hasWeakPartialDerivOn_univ_foldComp`) and closes under `L²` limits
(`HasWeakGradientOn.of_tendsto_eLpNorm_two`); the norm transport is supplied by
`FoldNorm`.
-/

noncomputable section

variable {d : ℕ}

/-! ## Geometry of the base box -/

theorem isOpen_Box (lo hi : Vec d) : IsOpen (Box lo hi) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem isOpenBoundedConvexDomain_Box (lo hi : Vec d) :
    IsOpenBoundedConvexDomain (Box lo hi) := by
  refine ⟨isOpen_Box lo hi, ?_, ?_⟩
  · exact HCPolySupport.Bornology.IsBounded.isBoundedDomain <|
      Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _
  · exact convex_pi fun _ _ => convex_Ioo _ _

/-- The tripled box is the base box for the reflected corners. -/
theorem Box3_eq_Box (lo hi : Vec d) :
    Box3 lo hi = Box (fun k => 2 * lo k - hi k) (fun k => 2 * hi k - lo k) := rfl

/-- A concrete closed ball inside a nonempty base box. -/
theorem exists_ball_subset_Box (lo hi : Vec d) (hlt : ∀ k, lo k < hi k) (hd : 0 < d) :
    ∃ (x0 : Vec d) (r : ℝ), 0 < r ∧ Metric.closedBall x0 r ⊆ Box lo hi := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  set m : ℝ := Finset.univ.inf' hne (fun k => hi k - lo k) with hm
  have hm_pos : 0 < m := by
    rw [hm, Finset.lt_inf'_iff hne]
    exact fun k _ => by linarith [hlt k]
  refine ⟨fun k => (lo k + hi k) / 2, m / 3, by linarith, ?_⟩
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff (by linarith)] at hx
  refine Set.mem_univ_pi.2 fun k => ?_
  have hxk : dist (x k) ((lo k + hi k) / 2) ≤ m / 3 := hx k
  rw [Real.dist_eq, abs_le] at hxk
  have hmk : m ≤ hi k - lo k := Finset.inf'_le _ (Finset.mem_univ k)
  constructor <;> [skip; skip] <;> [nlinarith [hxk.1, hxk.2]; nlinarith [hxk.1, hxk.2]]

/-! ## `eLpNorm` convergence of the smooth approximants -/

/-- Convergence in `L²(U)` of the `convexApproxSmoothH1` approximants, in the
`eLpNorm` form the closure lemma consumes. -/
theorem tendsto_eLpNorm_convexApproxSmoothH1 {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {x0 : Vec d} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x0 r ⊆ U) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => (convexApproxSmoothH1 hU u x0 hr n).toFun x - u.toFun x) 2
        (volume.restrict U))
      Filter.atTop (nhds 0) := by
  set ψ : ℕ → H1Function U := convexApproxSmoothH1 hU u x0 hr with hψ
  have hedist : ∀ n, eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 2 (volume.restrict U)
      = edist (ψ n).toScalarL2 u.toScalarL2 := by
    intro n
    rw [MeasureTheory.Lp.edist_def]
    refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
    filter_upwards [(ψ n).coeFn_toScalarL2, u.coeFn_toScalarL2] with x hu1 hu2
    simp [Pi.sub_apply, hu1, hu2]
  have h1 : Filter.Tendsto (fun n => (ψ n).toScalarL2) Filter.atTop (nhds u.toScalarL2) :=
    tendsto_convexApproxSmoothH1_toScalarL2 hU u hball hr
  have h2 : Filter.Tendsto (fun n => edist (ψ n).toScalarL2 u.toScalarL2)
      Filter.atTop (nhds 0) := by
    simpa using h1.edist (tendsto_const_nhds (x := u.toScalarL2))
  exact h2.congr (fun n => (hedist n).symm)

/-- Convergence in `L²(U)` of the coordinate gradients of the approximants. -/
theorem tendsto_eLpNorm_grad_convexApproxSmoothH1 {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : H1Function U) {x0 : Vec d} {r : ℝ}
    (hr : 0 < r) (hball : Metric.closedBall x0 r ⊆ U) (i : Fin d) :
    Filter.Tendsto
      (fun n => eLpNorm
        (fun x => (convexApproxSmoothH1 hU u x0 hr n).grad x i - u.grad x i) 2
        (volume.restrict U))
      Filter.atTop (nhds 0) := by
  set ψ : ℕ → H1Function U := convexApproxSmoothH1 hU u x0 hr with hψ
  have hedist : ∀ n, eLpNorm (fun x => (ψ n).grad x i - u.grad x i) 2 (volume.restrict U)
      = edist ((ψ n).gradCoordToScalarL2 i) (u.gradCoordToScalarL2 i) := by
    intro n
    rw [MeasureTheory.Lp.edist_def]
    refine (MeasureTheory.eLpNorm_congr_ae ?_).symm
    filter_upwards [(ψ n).coeFn_gradCoordToScalarL2 i, u.coeFn_gradCoordToScalarL2 i]
      with x hu1 hu2
    simp [Pi.sub_apply, hu1, hu2]
  have h1 : Filter.Tendsto (fun n => (ψ n).gradCoordToScalarL2 i) Filter.atTop
      (nhds (u.gradCoordToScalarL2 i)) :=
    tendsto_convexApproxSmoothH1_gradCoordToScalarL2 hU u hball hr i
  have h2 : Filter.Tendsto (fun n => edist ((ψ n).gradCoordToScalarL2 i)
      (u.gradCoordToScalarL2 i)) Filter.atTop (nhds 0) := by
    simpa using h1.edist (tendsto_const_nhds (x := u.gradCoordToScalarL2 i))
  exact h2.congr (fun n => (hedist n).symm)

/-! ## The fold extension -/

/-- The fold-extension data bundle. -/
structure FoldExtension (lo hi : Vec d) (u : H1Function (Box lo hi)) where
  /-- The extended `H¹` function on the tripled box. -/
  Eu : H1Function (Box3 lo hi)
  /-- The extension agrees with `u` a.e. on the base box. -/
  toFun_ae : Eu.toFun =ᵐ[volume.restrict (Box lo hi)] u.toFun
  /-- The extension's gradient agrees with `u`'s a.e. on the base box. -/
  grad_ae : ∀ i, (fun x => Eu.grad x i) =ᵐ[volume.restrict (Box lo hi)] fun x => u.grad x i
  /-- `L²` control of the extension by the constant `(3^d)^{1/2}`. -/
  eLpNorm_le : eLpNorm Eu.toFun 2 (volume.restrict (Box3 lo hi))
    ≤ ((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2) * eLpNorm u.toFun 2 (volume.restrict (Box lo hi))
  /-- `L²` control of the extension's coordinate gradients. -/
  grad_eLpNorm_le : ∀ i, eLpNorm (fun x => Eu.grad x i) 2 (volume.restrict (Box3 lo hi))
    ≤ ((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2)
      * eLpNorm (fun x => u.grad x i) 2 (volume.restrict (Box lo hi))

/-- `Cd = (3^d)^{1/2}` is finite. -/
theorem Cd_ne_top : (((3 : ℝ≥0∞) ^ d) ^ ((1 : ℝ) / 2)) ≠ ⊤ :=
  (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.pow_ne_top (by simp))).ne

theorem measurable_foldSign_comp (lo hi : Vec d) (i : Fin d) :
    Measurable (fun x : Vec d => foldSign (lo i) (hi i) (x i)) := by
  have hsign : Measurable (foldSign (lo i) (hi i)) := by
    unfold foldSign
    refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const
  exact hsign.comp (measurable_pi_apply i)

theorem norm_foldSign_le_one (lo hi t : ℝ) : ‖foldSign lo hi t‖ ≤ 1 := by
  unfold foldSign; split_ifs <;> simp
end

end HCPolySupport
