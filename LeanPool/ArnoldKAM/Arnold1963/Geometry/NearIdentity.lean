/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Functions
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
Unique implicit roots on closed balls and analytic local inverses in Banach spaces.
-/

@[expose] public section
noncomputable section
open Set Filter Function Metric
open scoped Topology NNReal
namespace KamProject.Arnold1963

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [NormedSpace ℂ E] in
theorem existsUnique_add_eq_on_closedBall {a : E → E} {Q : E} {r κ : ℝ≥0} {ε : ℝ}
    (hb : NormBoundOn a (Metric.closedBall Q r) ε) (hε : ε ≤ r)
    (hκ : κ < 1) (hLip : LipschitzOnWith κ a (Metric.closedBall Q r)) :
    ∃! q, q ∈ Metric.closedBall Q r ∧ q + a q = Q := by
  let T : E → E := fun q => Q - a q
  have hmap : MapsTo T (Metric.closedBall Q r) (Metric.closedBall Q r) := by
    intro q hq
    simpa [T, Metric.mem_closedBall, dist_eq_norm] using (hb.norm_le hq).trans hε
  have hc : ContractingWith κ (hmap.restrict T _ _) := by
    refine ⟨hκ, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    change dist (Q - a x) (Q - a y) ≤ _
    simpa only [dist_sub_left, Subtype.dist_eq] using hLip.dist_le_mul x x.property y y.property
  obtain ⟨q, hq, he, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hc (Metric.mem_closedBall_self r.coe_nonneg)
    (edist_ne_top Q (T Q))
  have heq : q + a q = Q := (eq_sub_iff_add_eq).mp he.symm
  refine ⟨q, ⟨hq, heq⟩, ?_⟩
  intro z hz
  have hzfix : IsFixedPt (hmap.restrict T _ _) (⟨z, hz.1⟩ : Metric.closedBall Q r) := by
    apply Subtype.ext
    exact (eq_sub_iff_add_eq.mpr hz.2).symm
  have hqfix : IsFixedPt (hmap.restrict T _ _) (⟨q, hq⟩ : Metric.closedBall Q r) := by
    apply Subtype.ext
    exact he
  exact congrArg Subtype.val (hc.fixedPoint_unique' hzfix hqfix)

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem norm_sub_le_of_add_eq {a : E → E} {q Q : E} {ε : ℝ}
    (he : q + a q = Q) (hb : ‖a q‖ ≤ ε) : ‖q - Q‖ ≤ ε := by
  rw [← he]
  simpa using hb

theorem exists_analytic_local_inverse_of_isUnit {f : E → E} {x : E}
    (hf : AnalyticAt ℂ f x) (hu : IsUnit (fderiv ℂ f x)) :
    ∃ g : E → E, AnalyticAt ℂ g (f x) ∧ g (f x) = x ∧
      (∀ᶠ y in 𝓝 (f x), f (g y) = y) := by
  obtain ⟨u, hu⟩ := hu
  let i : E ≃L[ℂ] E := ContinuousLinearEquiv.ofUnit u
  have hi : fderiv ℂ f x = (i : E →L[ℂ] E) := hu.symm
  have hd : HasStrictFDerivAt f (i : E →L[ℂ] E) x := by
    rw [← hi]
    exact hf.hasStrictFDerivAt
  let R := hd.toOpenPartialHomeomorph f
  refine ⟨R.symm, ?_, R.left_inv hd.mem_toOpenPartialHomeomorph_source,
    hd.eventually_right_inverse⟩
  exact R.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source hf hi

theorem exists_analytic_local_inverse {f : E → E} {x : E}
    (hf : AnalyticAt ℂ f x)
    (hn : ‖fderiv ℂ f x - ContinuousLinearMap.id ℂ E‖ < 1) :
    ∃ g : E → E, AnalyticAt ℂ g (f x) ∧ g (f x) = x ∧
      (∀ᶠ y in 𝓝 (f x), f (g y) = y) := by
  apply exists_analytic_local_inverse_of_isUnit hf
  have h := isUnit_one_sub_of_norm_lt_one
    (show ‖-(fderiv ℂ f x - ContinuousLinearMap.id ℂ E)‖ < 1 by simpa only [norm_neg] using hn)
  convert h using 1
  change fderiv ℂ f x = 1 - -(fderiv ℂ f x - 1)
  abel

end KamProject.Arnold1963
