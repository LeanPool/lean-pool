/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationEuler
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationIterate
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationRateStep
public import LeanPool.AiyagariEquilibrium.Models.ImpatientDecline
public import LeanPool.AiyagariEquilibrium.Equilibrium.SignChange
public import LeanPool.AiyagariEquilibrium.Analysis.HARA

/-!
# Carroll and Kimball beyond CRRA: the HARA induction step

`IncomeFluctuationCarrollKimball` proves the induction step for `u = crraUtility γ`, where the
Euler equation makes consumption a multiple of the power mean of next period's consumptions and
`powerMean_concave` — Kimball's risk-tolerance aggregation — does the rest. Carroll and Kimball's
theorem is not about CRRA but about HARA, and this file covers the `b ≠ 0` branch,
`u c = crraUtility γ (η + c)`: CRRA with a subsistence level, which includes CRRA itself at
`η = 0`.

## Nothing new is needed

Marginal utility is `(η + c) ^ (-γ)`, so the Euler equation reads

  `(η + C(A)) ^ (-γ) = β R · Σ_{z'} π_{z z'} (η + c_{z'}(A)) ^ (-γ)`,

which is the CRRA equation in the variable `η + c`. So the endogenous-gridpoint map is the CRRA
one applied to SHIFTED consumptions, with the shift removed at the end (`haraEgmMap`), and it is
concave for exactly the same reason: `η + c_{z'}` is concave when `c_{z'}` is, the power mean of
concave positive functions is concave, and a constant shift changes nothing.

That the shift is harmless is the content of "linear risk tolerance". Risk tolerance
`-u' / u''` is `(η + c) / γ`, affine in consumption, and Kimball's aggregation theorem needs
precisely affineness — the level `η` rides through untouched.

## What is and is not covered

The induction STEP is here, for the whole `b ≠ 0` HARA branch. What is not is the assembled
statement: the iteration also needs positive consumption and the asset cap slack. Those are no
longer CRRA-specific — `consumptionFnOf_pos_of_marginal` gets positivity from a FINITE marginal
bound, which is what a shifted CRRA has at zero (`(η + c) ^ (-γ)` at `c = 0` is `η ^ (-γ)`), and
`policyOf_le_of_marginal_bound` was always general. Both branches now carry the assembly
through to a witness: `IncomeFluctuationCARA.caraCal` for CARA, and `StoneGearyWitness.stoneGeary`
for this one. The CARA branch `b = 0`, where marginal utility is `exp (-α c)`, needs a
different aggregator — the soft minimum `-(1/α) log Σ π exp (-α c)` — and is in
`IncomeFluctuationCARA`, on top of `Analysis.SoftMin`.
-/

@[expose] public section

open scoped NNReal
open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **The endogenous-gridpoint map for shifted CRRA.** The CRRA map in the variable `η + c`. -/
noncomputable def haraEgmMap (v : (ℝ × Z) →ᵇ ℝ) (γ η : ℝ) (z : Z) (A : ℝ) : ℝ :=
  ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
      * powerMean (P.transitionMatrix z) (-γ) (fun z' => η + P.consumptionFnOf v z' A) - η

@[simp] theorem haraEgmMap_zero_shift (v : (ℝ × Z) →ᵇ ℝ) (γ : ℝ) (z : Z) (A : ℝ) :
    P.haraEgmMap v γ 0 z A = P.egmMap v γ z A := by
  simp only [haraEgmMap, egmMap, zero_add, sub_zero]

theorem concaveOn_haraEgmMap {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap) (P.haraEgmMap v γ η z) := by
  have hmean := concaveOn_powerMean_comp (convex_Icc assetFloor assetCap)
    (neg_neg_of_pos hγ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
    (f := fun z' a => η + P.consumptionFnOf v z' a)
    (fun z' A hA => by linarith [hpos z' A hA])
    (fun z' => ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => by
      have h := (hconc z').2 hx hy hθ hφ hθφ
      simp only [smul_eq_mul] at h ⊢
      nlinarith [h, hθφ]⟩)
  have hk : (0 : ℝ) ≤ ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ)) :=
    Real.rpow_nonneg (mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le) _
  refine ⟨convex_Icc _ _, fun x hx y hy θ φ hθ hφ hθφ => ?_⟩
  have hstep := hmean.2 hx hy hθ hφ hθφ
  simp only [smul_eq_mul] at hstep ⊢
  simp only [haraEgmMap]
  nlinarith [mul_le_mul_of_nonneg_left hstep hk, hθφ]

theorem monotoneOn_haraEgmMap {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) :
    MonotoneOn (P.haraEgmMap v γ η z) (Icc assetFloor assetCap) := by
  have hmean := monotoneOn_powerMean_comp (D := Icc assetFloor assetCap)
    (neg_neg_of_pos hγ) (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z)
    (f := fun z' a => η + P.consumptionFnOf v z' a)
    (fun z' A hA => by linarith [hpos z' A hA])
    (fun z' x hx y hy hxy => by linarith [hmono z' hx hy hxy])
  intro x hx y hy hxy
  simp only [haraEgmMap]
  have := mul_le_mul_of_nonneg_left (hmean hx hy hxy)
    (Real.rpow_nonneg (mul_nonneg P.discount.coe_nonneg P.interest_gt_neg_one.le)
      (-(1 / γ)))
  linarith

/-- **The Euler equation puts consumption on the endogenous grid**, for shifted CRRA. -/
theorem hara_egm_of_euler {γ η : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (hc : 0 < η + P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < η + P.consumptionFnOf v z' A)
    (heuler : (η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ)
      = (P.discount : ℝ) * ((1 + P.interest)
        * ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ))) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.haraEgmMap v γ η z A := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hS : (0 : ℝ)
      < ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hc'
  have hprod : (η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ)
      = ((P.discount : ℝ) * (1 + P.interest))
        * ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ) := by
    rw [heuler]; ring
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  have hinv : ((η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ)) ^ (-(1 / γ))
      = η + P.consumptionFnOf (P.toExtended.bellman v) z a := by
    rw [← Real.rpow_mul hc.le, hexp, Real.rpow_one]
  have hkey : η + P.consumptionFnOf (P.toExtended.bellman v) z a
      = ((P.discount : ℝ) * (1 + P.interest)) ^ (-(1 / γ))
        * powerMean (P.transitionMatrix z) (-γ)
          (fun z' => η + P.consumptionFnOf v z' A) := by
    rw [← hinv, hprod, Real.mul_rpow hK.le hS.le]
    simp only [powerMean]
    congr 1
    rw [show -(1 / γ) = 1 / (-γ) by field_simp]
  simp only [haraEgmMap]
  linarith

/-- **The Euler hypothesis discharged**, for shifted CRRA: interiority is all that is left. -/
theorem hara_egmMap_consumptionFnOf {γ η : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ))
    (hu : P.u = haraUtility γ η) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (hη : 0 ≤ η) (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hA0 : assetFloor < A) (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint' : ∀ z' : Z, P.policyOf v (A, z') < P.maxSaving (A, z'))
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a = P.haraEgmMap v γ η z A := by
  have hcη : 0 < η + P.consumptionFnOf (P.toExtended.bellman v) z a := by linarith
  have hcη' : ∀ z' : Z, 0 < η + P.consumptionFnOf v z' A := fun z' => by linarith [hc' z']
  have hd : HasDerivAt P.u ((η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_haraUtility γ hcη
  have hd' : ∀ z' : Z, HasDerivAt P.u ((η + P.consumptionFnOf v z' A) ^ (-γ))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_haraUtility γ (hcη' z')
  exact P.hara_egm_of_euler hγ0 hβ hcη hcη'
    (P.euler_eq ha hA hA0 hAmax hint' hc hd hc' hd')

/-- **Carroll and Kimball (1996), the induction step for shifted CRRA.** Given the Euler
equation, the Bellman operator carries a concave consumption function to a concave one. -/
theorem concaveOn_consumptionFnOf_bellman_of_hara_euler {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    {v : (ℝ × Z) →ᵇ ℝ}
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap)) (z : Z)
    (hEuler : ∀ a ∈ Icc assetFloor assetCap,
      P.consumptionFnOf (P.toExtended.bellman v) z a
        = P.haraEgmMap v γ η z (P.policyOf (P.toExtended.bellman v) (a, z))) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm (z := z) (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z))
    (C := P.haraEgmMap v γ η z) (P.concaveOn_haraEgmMap hγ hη z hpos hconc)
    (strictMonoOn_add_egm (P.monotoneOn_haraEgmMap hγ hη z hpos hmono))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => hEuler a ha)
  rw [← hEuler a ha]
  have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
    simp only [resources, max_eq_right ha.1]
  simp only [consumptionFnOf, consumption, hres]
  ring

/-- **The induction step for shifted CRRA, with the Euler equation proved**, exactly as
`concaveOn_consumptionFnOf_bellman_of_interior` does it for CRRA: what is assumed is interiority,
a property of the state, not of the model. -/
theorem concaveOn_consumptionFnOf_bellman_of_hara {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = haraUtility γ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcpos : ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_consumptionFnOf_bellman_of_hara_euler hγ hη hpos hconc hmono z
    fun a ha => ?_
  obtain ⟨hA0, hAmax, hint'⟩ := hint a ha
  exact P.hara_egmMap_consumptionFnOf hγ hβ hu hη ha rfl hA0 hAmax (hcpos a ha) hint'
    (fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z))))

/-- **CRRA is the `η = 0` member**, so the HARA step really does generalise the CRRA one rather
than sitting beside it. -/
theorem concaveOn_consumptionFnOf_bellman_of_crra_via_hara {γ : ℝ} (hγ : 0 < γ)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = crraUtility γ) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z', ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z', ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z', MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcpos : ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hint : ∀ a ∈ Icc assetFloor assetCap, P.EulerInterior v z a) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) :=
  P.concaveOn_consumptionFnOf_bellman_of_hara hγ le_rfl hβ
    (by rw [hu, haraUtility_zero_shift]) z hpos hconc hmono hcpos hint

/-! ### Marginal bounds

A shifted CRRA has FINITE marginal utility at zero, `η ^ (-γ)`, so like CARA it satisfies no
Inada condition and its consumption floor is an inequality rather than a limit. Both bounds are
the CRRA ones read at `η + c`. -/

theorem haraUtility_marginal_bound {γ η R : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 ≤ η)
    {c d : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) (hcR : c ≤ R) :
    (η + R) ^ (-γ) * (c - d) ≤ haraUtility γ η c - haraUtility γ η d := by
  have hstep := crra_marginal_bound_Ici (γ := γ) (R := η + R) hγ0 hγ1
    (d := η + d) (c := η + c) (mem_Ici.mpr (by linarith)) (by linarith) (by linarith)
  simp only [haraUtility]
  have he : η + c - (η + d) = c - d := by ring
  rwa [he] at hstep

/-- The same with the restriction moved from `γ` to the ARGUMENT: a strictly positive
subsistence level keeps `η + c` away from zero, so `γ ≥ 1` — log Stone–Geary included — is
admissible. -/
theorem haraUtility_marginal_bound_pos {γ η R : ℝ} (hγ0 : 0 < γ) {c d : ℝ} (hd : 0 < η + d)
    (hdc : d ≤ c) (hcR : c ≤ R) :
    (η + R) ^ (-γ) * (c - d) ≤ haraUtility γ η c - haraUtility γ η d := by
  have hstep := crra_marginal_bound (γ := γ) (R := η + R) (c := η + c) (d := η + d) hγ0 hd
    (by linarith) (by linarith)
  simp only [haraUtility]
  have he : η + c - (η + d) = c - d := by ring
  rwa [he] at hstep

/-- **A marginal bound near zero for a strictly positive subsistence level.** -/
theorem marginalBoundOn_haraUtility_pos {γ η δ : ℝ} (hγ0 : 0 < γ) (hη : 0 < η) (hδ : 0 < δ) :
    MarginalBoundOn (Ici (0 : ℝ)) (haraUtility γ η) ((η + δ) ^ (-γ)) :=
  ⟨δ, hδ, fun _c _c' hc hcc' hc'δ =>
    haraUtility_marginal_bound_pos hγ0 (by linarith [mem_Ici.mp hc]) hcc'.le hc'δ⟩

theorem marginalBoundOn_haraUtility {γ η δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 ≤ η)
    (hδ : 0 < δ) : MarginalBoundOn (Ici (0 : ℝ)) (haraUtility γ η) ((η + δ) ^ (-γ)) :=
  ⟨δ, hδ, fun _c _c' hc hcc' hc'δ =>
    haraUtility_marginal_bound hγ0 hγ1 hη (mem_Ici.mp hc) hcc'.le hc'δ⟩

/-! ### The Euler inequality, and the corner -/

theorem haraEgmMap_eq_rpow {γ η : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (hη : 0 ≤ η)
    {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {A : ℝ} (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.haraEgmMap v γ η z A = ((P.discount : ℝ) * (1 + P.interest)
      * ∑ z' : Z, P.transitionMatrix z z'
          * (η + P.consumptionFnOf v z' A) ^ (-γ)) ^ (-(1 / γ)) - η := by
  have hγn : γ ≠ 0 := ne_of_gt hγ0
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hpos : ∀ z' : Z, 0 < η + P.consumptionFnOf v z' A := fun z' => by linarith [hc' z']
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z'
      * (η + P.consumptionFnOf v z' A) ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hpos
  rw [Real.mul_rpow hK.le hS.le]
  simp only [haraEgmMap, powerMean]
  congr 2
  rw [show -(1 / γ) = 1 / (-γ) by field_simp]

/-- **The Euler INEQUALITY in endogenous-gridpoint form**, for shifted CRRA: it holds AT the
borrowing limit, where the equality fails. -/
theorem hara_egmMap_ge {γ η : ℝ} (hγ0 : 0 < γ) (hβ : 0 < (P.discount : ℝ)) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) {v : (ℝ × Z) →ᵇ ℝ} {z : Z} {a A : ℝ}
    (ha : a ∈ Icc assetFloor assetCap)
    (hA : P.policyOf (P.toExtended.bellman v) (a, z) = A)
    (hAmax : A < P.maxSaving (a, z))
    (hc : 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hc' : ∀ z' : Z, 0 < P.consumptionFnOf v z' A) :
    P.consumptionFnOf (P.toExtended.bellman v) z a ≤ P.haraEgmMap v γ η z A := by
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hK : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest) := mul_pos hβ hR
  have hcη : 0 < η + P.consumptionFnOf (P.toExtended.bellman v) z a := by linarith
  have hcη' : ∀ z' : Z, 0 < η + P.consumptionFnOf v z' A := fun z' => by linarith [hc' z']
  have hS : (0 : ℝ) < ∑ z' : Z, P.transitionMatrix z z'
      * (η + P.consumptionFnOf v z' A) ^ (-γ) :=
    sum_rpow_pos (P.transitionMatrix_nonneg z) (P.transitionMatrix_sum z) hcη'
  have hd : HasDerivAt P.u ((η + P.consumptionFnOf (P.toExtended.bellman v) z a) ^ (-γ))
      (P.consumptionFnOf (P.toExtended.bellman v) z a) := by
    rw [hu]; exact hasDerivAt_haraUtility γ hcη
  have hd' : ∀ z' : Z, HasDerivAt P.u ((η + P.consumptionFnOf v z' A) ^ (-γ))
      (P.consumptionFnOf v z' A) := fun z' => by
    rw [hu]; exact hasDerivAt_haraUtility γ (hcη' z')
  have heuler := P.euler_le ha hA hAmax hc hd hc' hd'
  rw [P.haraEgmMap_eq_rpow hγ0 hβ hη hc']
  have hKS : (0 : ℝ) < (P.discount : ℝ) * (1 + P.interest)
      * ∑ z' : Z, P.transitionMatrix z z' * (η + P.consumptionFnOf v z' A) ^ (-γ) :=
    mul_pos hK hS
  have hstep := Real.rpow_le_rpow_of_nonpos hKS (by linarith [heuler])
    (show -(1 / γ) ≤ 0 by rw [neg_nonpos]; positivity)
  have hexp : (-γ) * (-(1 / γ)) = 1 := by field_simp
  rw [← Real.rpow_mul hcη.le, hexp, Real.rpow_one] at hstep
  linarith

/-- **Carroll and Kimball for shifted CRRA, across the borrowing-limit kink.** -/
theorem concaveOn_consumptionFnOf_bellman_of_hara_corner {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = haraUtility γ η) {v : (ℝ × Z) →ᵇ ℝ} (z : Z)
    (hpos : ∀ z' : Z, ∀ A ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf v z' A)
    (hconc : ∀ z' : Z, ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFnOf v z'))
    (hmono : ∀ z' : Z, MonotoneOn (P.consumptionFnOf v z') (Icc assetFloor assetCap))
    (hcW : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf (P.toExtended.bellman v) z a)
    (hslackW : ∀ a ∈ Icc assetFloor assetCap,
      P.policyOf (P.toExtended.bellman v) (a, z) < P.maxSaving (a, z))
    (hslackv : ∀ A ∈ Icc assetFloor assetCap, ∀ z' : Z,
      P.policyOf v (A, z') < P.maxSaving (A, z')) :
    ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf (P.toExtended.bellman v) z) := by
  refine P.concaveOn_of_egm_corner (z := z)
    (g := fun a => P.policyOf (P.toExtended.bellman v) (a, z)) (C := P.haraEgmMap v γ η z)
    (P.concaveOn_haraEgmMap hγ hη z hpos hconc)
    (strictMonoOn_add_egm (P.monotoneOn_haraEgmMap hγ hη z hpos hmono))
    (fun a _ => P.feasible_subset_region (P.policyOf_mem _ (a, z))) (fun a ha => ?_)
    (fun a ha => ?_) fun a ha hfloor => ?_
  · have hres : P.resources (a, z) = P.income z + (1 + P.interest) * a := by
      simp only [resources, max_eq_right ha.1]
    simp only [consumptionFnOf, consumption, hres]; ring
  · exact P.hara_egmMap_ge hγ hβ hη hu ha rfl (hslackW a ha) (hcW a ha)
      fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))
  · exact P.hara_egmMap_consumptionFnOf hγ hβ hu hη ha rfl hfloor (hslackW a ha) (hcW a ha)
      (hslackv _ (P.feasible_subset_region (P.policyOf_mem _ (a, z))))
      fun z' => hpos z' _ (P.feasible_subset_region (P.policyOf_mem _ (a, z)))

/-! ### The proportional bound on saving

`policyOf_le_of_marginal_bound` prices a deviation against the LEVEL of the continuation, which
for a bounded utility is far too crude to keep the cap slack at any interesting discount factor.
The CRRA development fixes that with `crra_policyOf_le_mul`: deviate to a FRACTION `θ` of the
saving rather than a fixed amount, and price the extra consumption at the margin where it lands.
The bound then involves the continuation's OSCILLATION and is proportional to consumption.

The shifted-CRRA version is that argument with the marginal step read at `η + c`. Everything
else — the deviation, the concavity of the continuation, the oscillation — knows nothing about
preferences. -/

theorem hara_policyOf_le_mul {γ η θ G : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : P.u = haraUtility γ η)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (hG : 0 ≤ G)
    (hosc : P.OscOn v G) {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (hcpos : 0 < P.consumptionFnOf v z a) :
    P.policyOf v (a, z) - assetFloor
      ≤ ((P.discount : ℝ) * G / θ)
        * (η + P.consumptionFnOf v z a
            + (1 - θ) * (P.policyOf v (a, z) - assetFloor)) ^ γ := by
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hbase : (0 : ℝ) < η + c + (1 - θ) * (b - assetFloor) := by
    have h := mul_nonneg (show (0 : ℝ) ≤ 1 - θ by linarith)
      (show (0 : ℝ) ≤ b - assetFloor by linarith [hbreg.1])
    linarith
  have hrpow : (0 : ℝ) < (η + c + (1 - θ) * (b - assetFloor)) ^ γ := Real.rpow_pos_of_pos hbase _
  rcases eq_or_lt_of_le hbreg.1 with hzero | hbpos
  · rw [← hzero, sub_self]
    positivity
  have hbf : (0 : ℝ) < b - assetFloor := by linarith
  set w : ℝ := assetFloor + θ * (b - assetFloor) with hwdef
  have hw0 : assetFloor < w := by rw [hwdef]; nlinarith
  have hwb : w < b := by rw [hwdef]; nlinarith
  have hwmem : w ∈ Icc assetFloor assetCap := ⟨hw0.le, by linarith [hbreg.2]⟩
  have hfeas : w ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq]
    exact ⟨hw0.le, by linarith [(P.policyOf_mem v (a, z)).2]⟩
  have hcb : c = P.resources (a, z) - b := rfl
  have hcons : P.consumption (a, z) w = c + (1 - θ) * (b - assetFloor) := by
    simp only [consumption, hwdef]; rw [hcb]; ring
  have hdev : 0 < P.consumption (a, z) w := by rw [hcons]; linarith
  have hopt := P.objROf_le_of_mem v ha hfeas (P.mem_dom_of_pos hdev)
  simp only [objROf, hcons] at hopt
  rw [show P.consumption (a, z) (P.policyOf v (a, z)) = c from rfl,
    show P.policyOf v (a, z) = b from rfl] at hopt
  have hslope := (P.concaveOn_contOf hv z).slope_anti_adjacent
    (mem_Icc.mpr ⟨le_rfl, P.assetFloor_le_assetCap⟩) hbreg hw0 hwb
  have hgap := P.contOf_sub_le_osc hosc hwmem
    (show assetFloor ∈ Icc assetFloor assetCap from ⟨le_rfl, P.assetFloor_le_assetCap⟩) z z
  have hbw : b - w = (1 - θ) * (b - assetFloor) := by rw [hwdef]; ring
  have hwf : w - assetFloor = θ * (b - assetFloor) := by rw [hwdef]; ring
  have hloss : P.contOf v z b - P.contOf v z w ≤ (1 - θ) / θ * G := by
    rw [div_le_div_iff₀ (show (0 : ℝ) < b - w by linarith)
      (show (0 : ℝ) < w - assetFloor by linarith), hbw, hwf] at hslope
    have h2 : (P.contOf v z b - P.contOf v z w) * (θ * (b - assetFloor))
        ≤ G * ((1 - θ) * (b - assetFloor)) := by
      nlinarith [hslope, hgap, mul_pos (show (0:ℝ) < 1 - θ by linarith) hbf]
    rw [div_mul_eq_mul_div, le_div_iff₀ hθ0]
    nlinarith [h2, hbf]
  -- the marginal gain, priced where it lands: the CRRA step read at `η + c`
  have hmg : (η + c + (1 - θ) * (b - assetFloor)) ^ (-γ) * ((1 - θ) * (b - assetFloor))
      ≤ P.u (c + (1 - θ) * (b - assetFloor)) - P.u c := by
    rw [hu]
    have hbound := haraUtility_marginal_bound_pos (γ := γ) (η := η)
      (R := c + (1 - θ) * (b - assetFloor)) hγ0 (d := c)
      (c := c + (1 - θ) * (b - assetFloor)) (by linarith)
      (le_add_of_nonneg_right (mul_nonneg (by linarith) hbf.le)) le_rfl
    have he : η + (c + (1 - θ) * (b - assetFloor)) = η + c + (1 - θ) * (b - assetFloor) := by ring
    rw [he] at hbound
    have he2 : c + (1 - θ) * (b - assetFloor) - c = (1 - θ) * (b - assetFloor) := by ring
    rw [he2] at hbound
    exact hbound
  have hmid : P.u (c + (1 - θ) * (b - assetFloor)) - P.u c
      ≤ (P.discount : ℝ) * (P.contOf v z b - P.contOf v z w) := by
    have hd : (P.discount : ℝ) * (P.contOf v z b - P.contOf v z w)
        = (P.discount : ℝ) * P.contOf v z b - (P.discount : ℝ) * P.contOf v z w := by ring
    linarith [hopt, hd.le, hd.ge]
  have hkey := le_trans hmg (le_trans hmid (mul_le_mul_of_nonneg_left hloss hβ))
  rw [Real.rpow_neg hbase.le γ] at hkey
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hexp : ((η + c + (1 - θ) * (b - assetFloor)) ^ γ)⁻¹ * ((1 - θ) * (b - assetFloor))
      = (1 - θ) * ((b - assetFloor) / (η + c + (1 - θ) * (b - assetFloor)) ^ γ) := by field_simp
  rw [hexp, show (P.discount : ℝ) * ((1 - θ) / θ * G)
      = (1 - θ) * ((P.discount : ℝ) * G / θ) from by ring] at hkey
  have hdiv := le_of_mul_le_mul_left hkey h1θ
  rw [div_le_iff₀ hrpow] at hdiv
  linarith

/-- **Saving never reaches the asset cap**, for shifted CRRA. -/
theorem hara_policyOf_lt_assetCap {γ η θ G : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : P.u = haraUtility γ η)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices assetFloor assetCap v) (hG : 0 ≤ G)
    (hosc : P.OscOn v G) (hcpos : ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf v z a)
    (hlt : ((P.discount : ℝ) * G / θ)
        * (η + P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor) ^ γ
      < assetCap - assetFloor)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z) :
    P.policyOf v (a, z) < assetCap := by
  by_contra hcon
  rw [not_lt] at hcon
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  set b : ℝ := P.policyOf v (a, z) with hbdef
  set c : ℝ := P.consumptionFnOf v z a with hcdef
  have hbreg : b ∈ Icc assetFloor assetCap :=
    P.feasible_subset_region (P.policyOf_mem v (a, z))
  have hkey := P.hara_policyOf_le_mul hγ0 hη hθ0 hθ1 hu hv hG hosc ha z (hcpos z a ha)
  rw [← hbdef, ← hcdef] at hkey
  have hcpos' : 0 < c := hcpos z a ha
  have hres : P.resources (a, z) - assetFloor ≤ P.maxConsumption :=
    P.consumption_le_maxConsumption (s := (a, z)) ha le_rfl
  have hsum : c + (1 - θ) * (b - assetFloor)
      = (P.resources (a, z) - assetFloor) - θ * (b - assetFloor) := by
    simp only [hcdef, consumptionFnOf, consumption, ← hbdef]; ring
  have hle : η + c + (1 - θ) * (b - assetFloor)
      ≤ η + P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor := by
    have hθb : θ * (assetCap - assetFloor) ≤ θ * (b - assetFloor) :=
      mul_le_mul_of_nonneg_left (by linarith) hθ0.le
    simp only [maxConsumption] at hres
    nlinarith [hres, hθb, hsum]
  have hnn : (0 : ℝ) ≤ η + c + (1 - θ) * (b - assetFloor) := by
    have h := mul_nonneg (show (0 : ℝ) ≤ 1 - θ by linarith)
      (show (0 : ℝ) ≤ b - assetFloor by linarith [hbreg.1])
    linarith [hcpos']
  have hmono : (η + c + (1 - θ) * (b - assetFloor)) ^ γ
      ≤ (η + P.maxIncome + (1 + P.interest - θ) * assetCap - (1 - θ) * assetFloor) ^ γ :=
    Real.rpow_le_rpow hnn hle hγ0.le
  have hcoef : (0 : ℝ) ≤ (P.discount : ℝ) * G / θ := by positivity
  nlinarith [hkey, mul_le_mul_of_nonneg_left hmono hcoef, hlt]

/-! ### The assembly -/

theorem concaveOn_consumptionFnOf_iterates_of_hara {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hβ : 0 < (P.discount : ℝ)) (hu : P.u = haraUtility γ η)
    (hpos : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < P.maxSaving (a, z)) :
    ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap)
      (P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z) := by
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact P.concaveSlices_bellman ih
  intro n
  induction n with
  | zero => exact P.concaveOn_consumptionFnOf_zero
  | succ k ih =>
    intro z
    have hnext : ∀ a ∈ Icc assetFloor assetCap, 0 < P.consumptionFnOf
        (P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ))) z a := by
      intro a ha
      have := hpos (k + 1) z a ha
      rwa [Function.iterate_succ_apply'] at this
    have hnextslack : ∀ a ∈ Icc assetFloor assetCap, P.policyOf
        (P.toExtended.bellman ((P.toExtended.bellman)^[k] (0 : (ℝ × Z) →ᵇ ℝ))) (a, z)
          < P.maxSaving (a, z) := by
      intro a ha
      have := hslack (k + 1) a ha z
      rwa [Function.iterate_succ_apply'] at this
    rw [Function.iterate_succ_apply']
    exact P.concaveOn_consumptionFnOf_bellman_of_hara_corner hγ hη hβ hu z
      (fun z' A hA => hpos k z' A hA) ih
      (fun z' x hx y hy hxy => P.consumptionFnOf_mono (hslices k) hx hy hxy)
      hnext hnextslack (fun A hA z' => hslack k A hA z')

/-- **Carroll and Kimball for shifted CRRA, from two inequalities.** The same two the CARA
assembly needs, and for the same reasons: marginal utility at zero is finite, so the consumption
floor has to be earned, and the cap has to sit above the saving the marginal bound allows. -/
theorem concaveOn_consumptionFn_of_hara {γ η δ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 ≤ η)
    (hδ : 0 < δ) (hβ : 0 < (P.discount : ℝ)) (hb : P.Bounded) (hu : P.u = haraUtility γ η)
    (hfloor : (P.discount : ℝ) * P.oscSlopeConst P.oscSpread < (η + δ) ^ (-γ))
    (hcap : assetFloor + 4 * (P.discount : ℝ)
        * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount))
        / (η + P.maxConsumption) ^ (-γ) < assetCap)
    (z : Z) : ConcaveOn ℝ (Icc assetFloor assetCap) (P.consumptionFn z) := by
  have hslices : ∀ n : ℕ, ConcaveSlices assetFloor assetCap
      ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact P.concaveSlices_bellman ih
  have hM : MarginalBoundOn P.dom P.u ((η + δ) ^ (-γ)) := by
    rw [hb, hu]
    exact marginalBoundOn_haraUtility hγ0 hγ1 hη hδ
  have hpos : ∀ n : ℕ, ∀ z' : Z, ∀ a ∈ Icc assetFloor assetCap,
      0 < P.consumptionFnOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z' a :=
    fun n z' a ha => P.consumptionFnOf_pos_of_marginal hM P.oscSpread_nonneg (hslices n)
      (P.oscOn_iterate n) hfloor z' ha
  have hmpos : (0 : ℝ) < (η + P.maxConsumption) ^ (-γ) :=
    Real.rpow_pos_of_pos (by linarith [P.maxConsumption_pos]) _
  have hslack : ∀ n : ℕ, ∀ a ∈ Icc assetFloor assetCap, ∀ z' : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z') < P.maxSaving (a, z') := by
    intro n a ha z'
    refine P.policyOf_lt_maxSaving_of_pos (hpos n z' a ha) ?_
    have hbound := P.policyOf_le_of_marginal_bound (hslices n) hmpos ?_ ha z'
    · have hn := P.norm_iterate_le n
      have h4 : (0 : ℝ) ≤ 4 * (P.discount : ℝ) := by positivity
      have hstep := mul_le_mul_of_nonneg_left hn h4
      have hdiv : 4 * (P.discount : ℝ) * ‖(P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)‖
            / (η + P.maxConsumption) ^ (-γ)
          ≤ 4 * (P.discount : ℝ)
            * (max |P.toExtended.rewardMin| |P.toExtended.rewardMax| / (1 - P.discount))
            / (η + P.maxConsumption) ^ (-γ) := by
        rw [div_le_div_iff_of_pos_right hmpos]
        linarith
      linarith
    · intro c d hd hdc hcmax
      rw [hu]
      exact haraUtility_marginal_bound hγ0 hγ1 hη (P.nonneg_of_mem_dom hd) hdc hcmax
  exact P.concaveOn_consumptionFn_of_iterates
    (P.concaveOn_consumptionFnOf_iterates_of_hara hγ0 hη hβ hu hpos hslack) z

/-! ### The two comparative-statics corollaries, for shifted CRRA

Light's Theorem 1 and the impatience-driven decline both take the marginal-utility hypotheses
abstractly, so shifted CRRA discharges them the same way CRRA does — with `(η + c) ^ (-γ)` in
place of `c ^ (-γ)`. Relative risk aversion of the shifted family is `γc/(η + c) ≤ γ`, so a
NON-NEGATIVE subsistence level only helps Light's condition. -/

theorem hara_marginal_antitone {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η) :
    AntitoneOn (fun c => (η + c) ^ (-γ)) (Ioi (0 : ℝ)) := fun x hx y _ hxy =>
  Real.rpow_le_rpow_of_nonpos (by linarith [mem_Ioi.mp hx]) (by linarith) (by linarith)

theorem hara_marginal_pos {γ η : ℝ} (hη : 0 ≤ η) {c : ℝ} (hc : 0 < c) :
    0 < (η + c) ^ (-γ) := Real.rpow_pos_of_pos (by linarith) _

/-- **Light (2018) Theorem 1 for shifted CRRA.** -/
theorem policy_mono_withRate_hara {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)
    {γ η : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 ≤ η) (hu : P.u = haraUtility γ η)
    {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hposv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hposw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hslackw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) :=
  P.policy_mono_withRate' h₁ h₂ hr (du := fun c => (η + c) ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_haraUtility γ (by linarith))
    (hara_marginal_antitone hγ0 hη)
    (by
      have hrra := (relativeRiskAversionLeOne_haraUtility hγ0 hγ1 hη).monotoneOn_mul_deriv
        (du := fun c => (η + c) ^ (-γ))
        (fun c hc => hasDerivAt_haraUtility γ (by have := mem_Ioi.mp hc; linarith))
      exact hrra)
    (fun y hy => (hara_marginal_pos hη (mem_Ioi.mp hy)).le)
    hposv hposw hslackv hslackw hcons ha z

/-- **Açıkgöz Proposition 4 for shifted CRRA**: the decline condition is impatience. -/
theorem hara_exists_exhaust_of_impatient {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η)
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    {a₀ : ℝ} (ha₀ : assetFloor < a₀) (hle : a₀ ≤ assetCap)
    (hzero : ∀ a ∈ Icc assetFloor a₀, P.policy (a, z₀) = assetFloor) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState :=
  P.exists_exhaust_of_impatient hβR hiid (du := fun c => (η + c) ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_haraUtility γ (by linarith))
    (hara_marginal_antitone hγ0 hη)
    (fun c hc => hara_marginal_pos hη hc) hpos hslack hz₀ ha₀ hle hzero

/-! ### The supply floor

The household saves something, so aggregate capital is positive. The shape is the CRRA one: the
cost of saving a little is priced at the margin where consumption is lowest, the gain at the
margin in the bad successor state, and the comparison is between two marginal utilities. With a
subsistence level both are read at `η + c`. -/

theorem hara_cost_of_saving {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) {m h R b : ℝ} (hh0 : 0 < h)
    (hhm : h < m) (hmR : m ≤ R) (hb0 : 0 ≤ b) (hbh : b ≤ h) :
    haraUtility γ η (R - b) - haraUtility γ η (R - h) ≤ (η + m - h) ^ (-γ) * h := by
  have hstep := crra_cost_of_saving (γ := γ) (m := η + m) (h := h) (R := η + R) (b := b) hγ hh0
    (by linarith) (by linarith) hb0 hbh
  have e1 : η + R - b = η + (R - b) := by ring
  have e2 : η + R - h = η + (R - h) := by ring
  have e3 : η + m - h = η + m - h := rfl
  rw [e1, e2] at hstep
  simpa only [haraUtility] using hstep

/-- **The continuation's gain, for shifted CRRA.** -/
theorem hara_cont_sub_ge_gen {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) (hfl : assetFloor = 0) (hpc : P.PositiveConsumption)
    (z z₀ : Z) {x y : ℝ}
    (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap) (hxy : x ≤ y) :
    P.transitionMatrix z z₀ * ((η + P.income z₀ + (1 + P.interest) * y) ^ (-γ)
        * ((1 + P.interest) * (y - x)))
      ≤ P.cont z y - P.cont z x := by
  subst hfl
  have hRh : 0 ≤ (1 + P.interest) * (y - x) :=
    mul_nonneg P.interest_gt_neg_one.le (by linarith)
  have hsum : P.cont z y - P.cont z x = ∑ z' : Z, P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')) := by
    simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
  have hterm : P.transitionMatrix z z₀ *
      (P.toExtended.valueFunction (y, z₀) - P.toExtended.valueFunction (x, z₀))
        ≤ P.cont z y - P.cont z x := by
    rw [hsum]
    refine Finset.single_le_sum (f := fun z' : Z => P.transitionMatrix z z' *
      (P.toExtended.valueFunction (y, z') - P.toExtended.valueFunction (x, z')))
      (fun z' _ => ?_) (Finset.mem_univ z₀)
    exact mul_nonneg (P.transitionMatrix_nonneg _ _)
      (by linarith [P.valueFunction_le_of_le hpc (z := z') hx hy hxy])
  have hc0 : 0 < P.consumption (x, z₀) (P.policy (x, z₀)) := P.consumption_policy_pos hpc hx
  have hresx : P.resources (x, z₀) = P.income z₀ + (1 + P.interest) * x := by
    simp only [resources, max_eq_right hx.1]
  have hcle : P.consumption (x, z₀) (P.policy (x, z₀))
      ≤ P.income z₀ + (1 + P.interest) * x := by
    simp only [consumption, hresx]
    linarith [(P.policy_mem_region (x, z₀)).1]
  have hgain := P.valueFunction_sub_ge hpc hx hy hxy z₀
  rw [hu] at hgain
  have hbound : (η + P.income z₀ + (1 + P.interest) * y) ^ (-γ) * ((1 + P.interest) * (y - x))
      ≤ haraUtility γ η (P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x))
        - haraUtility γ η (P.consumption (x, z₀) (P.policy (x, z₀))) := by
    have hR : P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x)
        ≤ P.income z₀ + (1 + P.interest) * y := by nlinarith [hcle]
    have hstep := haraUtility_marginal_bound_pos (γ := γ) (η := η)
      (R := P.income z₀ + (1 + P.interest) * y) hγ0 (by linarith)
      (le_add_of_nonneg_right hRh) hR
    have he : η + (P.income z₀ + (1 + P.interest) * y)
        = η + P.income z₀ + (1 + P.interest) * y := by ring
    rw [he] at hstep
    have he2 : P.consumption (x, z₀) (P.policy (x, z₀)) + (1 + P.interest) * (y - x)
        - P.consumption (x, z₀) (P.policy (x, z₀)) = (1 + P.interest) * (y - x) := by ring
    rw [he2] at hstep
    exact hstep
  exact le_trans (mul_le_mul_of_nonneg_left (le_trans hbound hgain)
    (P.transitionMatrix_nonneg z z₀)) hterm

/-- **Saving is bounded below**, for shifted CRRA, when the gain beats the cost. -/
theorem hara_policy_ge_of_gain {γ η : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) (hfl : assetFloor = 0)
    (hpc : P.PositiveConsumption) (z₁ : Z) {h : ℝ} (hh0 : 0 < h) (hhcap : h ≤ assetCap)
    (hhinc : h < P.income z₁)
    (hgain : (η + P.income z₁ - h) ^ (-γ) * h
      < P.discount * (P.cont z₁ h - P.cont z₁ (h / 2)))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    h / 2 ≤ P.policy (a, z₁) := by
  refine P.policy_ge_of_cost hfl hpc z₁ hh0 hhcap hhinc (fun R b hm hb0 hbh => ?_) hgain ha
  rw [hu]
  exact hara_cost_of_saving hγ hη hh0 hhinc hm hb0 hbh

/-! ### The corner condition, in primitives

The corner test of `policy_eq_zero_of_corner_at` is `β L < m`: the discounted slope of the value
function against the marginal value of consumption. Both sides have closed forms for shifted
CRRA, so the test becomes one inequality among the primitives.

* The value function's slope is bounded by `slopeBoundU`, amplified by the return and the
  discounting. Concavity prices `slopeBoundU` at the margin halfway down the minimum
  consumption: `(η + minConsumption / 2) ^ (-γ)`.
* The marginal value at `(a, z₀)` for `a ≤ a₀` is at least `(η + income z₀ + R a₀) ^ (-γ)`.

So the corner holds below `a₀` exactly when

  `β · (η + minConsumption/2) ^ (-γ) · R / (1 - β R)  <  (η + income z₀ + R a₀) ^ (-γ)`,

which is checkable by `norm_num` at any calibration. -/

/-- The secant slope is at most the marginal utility at the left end. -/
theorem haraUtility_marginal_bound_above {γ η : ℝ} (hγ0 : 0 < γ) {c d : ℝ} (hd : 0 < η + d)
    (hdc : d ≤ c) :
    haraUtility γ η c - haraUtility γ η d ≤ (η + d) ^ (-γ) * (c - d) := by
  have hstep := crra_marginal_bound_above (γ := γ) (c := η + c) (d := η + d) hγ0 hd
    (by linarith)
  have he : η + c - (η + d) = c - d := by ring
  rw [he] at hstep
  simpa only [haraUtility] using hstep

/-- **The slope constant in closed form.** -/
theorem slopeBoundU_le_hara {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η) (hu : P.u = haraUtility γ η) :
    P.slopeBoundU ≤ (η + P.minConsumption / 2) ^ (-γ) := by
  have hmin := P.minConsumption_pos
  simp only [IncomeFluctuation.slopeBoundU, slopeBound, hu]
  rw [div_le_iff₀ (by linarith)]
  have hstep := haraUtility_marginal_bound_above (γ := γ) (η := η) (c := P.minConsumption)
    (d := P.minConsumption / 2) hγ0 (by linarith) (by linarith)
  have he : P.minConsumption - P.minConsumption / 2 = P.minConsumption / 2 := by ring
  rw [he] at hstep
  exact hstep

/-- The Lipschitz constant of the value function, in primitives. -/
noncomputable def haraLipschitz (γ η : ℝ) : ℝ :=
  (η + P.minConsumption / 2) ^ (-γ) * (1 + P.interest)
    / (1 - P.discount * (1 + P.interest))

theorem haraLipschitz_nonneg {γ η : ℝ} (hη : 0 ≤ η)
    (hβR : P.discount * (1 + P.interest) < 1) : 0 ≤ P.haraLipschitz γ η := by
  have hR := P.interest_gt_neg_one
  have hmin := P.minConsumption_pos
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) hR.le) (by linarith)

/-- **The value function is Lipschitz**, with the constant read off the primitives. -/
theorem hara_valueFunction_lipschitz {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) (hβR : P.discount * (1 + P.interest) < 1) :
    ∀ z : Z, ∀ x ∈ Icc assetFloor assetCap, ∀ y ∈ Icc assetFloor assetCap,
      |P.toExtended.valueFunction (x, z) - P.toExtended.valueFunction (y, z)|
        ≤ P.haraLipschitz γ η * |x - y| := by
  have hR := P.interest_gt_neg_one
  have hne : (0 : ℝ) < 1 - P.discount * (1 + P.interest) := by linarith
  refine P.valueFunction_lipschitz (P.haraLipschitz_nonneg hη hβR) ?_
  have hslope := P.slopeBoundU_le_hara hγ0 hη hu
  have hkey : ((η + P.minConsumption / 2) ^ (-γ)
      + P.discount * P.haraLipschitz γ η) * (1 + P.interest) = P.haraLipschitz γ η := by
    simp only [haraLipschitz]
    field_simp
    ring
  have hmul : (P.slopeBoundU + P.discount * P.haraLipschitz γ η) * (1 + P.interest)
      ≤ ((η + P.minConsumption / 2) ^ (-γ) + P.discount * P.haraLipschitz γ η)
        * (1 + P.interest) :=
    mul_le_mul_of_nonneg_right (by linarith) hR.le
  rw [hkey] at hmul
  exact hmul

/-- **The corner condition from primitives.** One inequality, `norm_num`-checkable. -/
theorem hara_policy_eq_zero_of_primitives {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 < η)
    (hu : P.u = haraUtility γ η) (hfl : assetFloor = 0)
    (hβR : P.discount * (1 + P.interest) < 1) (z₀ : Z) {a₀ : ℝ} (_ha₀ : 0 ≤ a₀)
    (ha₀cap : a₀ ≤ assetCap)
    (hcond : P.discount * P.haraLipschitz γ η
      < (η + P.income z₀ + (1 + P.interest) * a₀) ^ (-γ))
    {a : ℝ} (ha : a ∈ Icc assetFloor a₀) : P.policy (a, z₀) = assetFloor := by
  subst hfl
  have hR := P.interest_gt_neg_one
  have hmem : a ∈ Icc (0 : ℝ) assetCap := ⟨ha.1, le_trans ha.2 ha₀cap⟩
  have hres : P.resources (a, z₀) - 0 ≤ P.income z₀ + (1 + P.interest) * a₀ := by
    simp only [IncomeFluctuation.resources, max_eq_right ha.1, sub_zero]
    have := mul_le_mul_of_nonneg_left ha.2 hR.le
    linarith
  have hres0 : (0 : ℝ) < P.resources (a, z₀) - 0 := by
    have := P.assetFloor_lt_resources (a, z₀)
    linarith
  refine P.policy_eq_zero_of_corner_at (L := P.haraLipschitz γ η)
    (m := (η + P.income z₀ + (1 + P.interest) * a₀) ^ (-γ))
    (P.hara_valueFunction_lipschitz hγ0 hη.le hu hβR) hmem ?_ hcond
  intro c d hd hdc hc
  have hd0 : (0 : ℝ) ≤ d := P.nonneg_of_mem_dom hd
  have hbound := haraUtility_marginal_bound_pos (γ := γ) (η := η)
    (R := P.resources (a, z₀) - 0) hγ0 (show (0 : ℝ) < η + d by linarith) hdc hc
  rw [hu]
  refine le_trans (mul_le_mul_of_nonneg_right ?_ (by linarith)) hbound
  exact rpow_neg_antitone hγ0 (by linarith) (by linarith)

section Measure

variable [MeasurableSpace Z] [BorelSpace Z]

/-- **Positive aggregate capital for shifted CRRA, from primitives.** -/
theorem hara_le_aggregateCapital_of_gain {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) (hfl : assetFloor = 0) (hpc : P.PositiveConsumption)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ h : ℝ}
    (hh0 : 0 < h) (hhcap : h ≤ assetCap) (hhinc : h < P.income z₁)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hgain : (η + P.income z₁ - h) ^ (-γ) * h
      < P.discount * (P.transitionMatrix z₁ z₀
          * ((η + P.income z₀ + (1 + P.interest) * h) ^ (-γ) * ((1 + P.interest) * (h / 2))))) :
    h / 2 * p₀ ≤ P.aggregateCapital μ := by
  subst hfl
  refine P.le_aggregateCapital hμ (by linarith) hp fun a ha => ?_
  refine P.hara_policy_ge_of_gain hγ0 hη hu rfl hpc z₁ hh0 hhcap hhinc ?_ ha
  refine lt_of_lt_of_le hgain (mul_le_mul_of_nonneg_left ?_ P.discount.coe_nonneg)
  have hhalf : h / 2 ∈ Icc (0 : ℝ) assetCap := ⟨by linarith, by linarith⟩
  have hfull : h ∈ Icc (0 : ℝ) assetCap := ⟨hh0.le, hhcap⟩
  have hgen := P.hara_cont_sub_ge_gen hγ0 hη hu rfl hpc z₁ z₀ hhalf hfull (by linarith)
  rw [show h - h / 2 = h / 2 from by ring] at hgen
  exact hgen

/-- **The supply floor with the two powers bounded separately.** The gain condition compares
`(η + y₁ - t)^(-γ)`, the marginal cost of saving `t` in the high state, against
`(η + y₀ + Rt)^(-γ)`, the marginal value of having it in the low state. Bounding the first from
above and the second from below leaves ONE inequality among the bounds — and when a base sits on
the right side of one, its bound needs no root at all (`rpow_neg_le_one_of_one_le`,
`rpow_neg_le_inv_of_le_one`).

This is what makes a supply floor a calibration check rather than a proof. -/
theorem hara_le_aggregateCapital_of_bounds {γ η : ℝ} (hγ0 : 0 < γ) (hη : 0 ≤ η)
    (hu : P.u = haraUtility γ η) (hfl : assetFloor = 0) (hpc : P.PositiveConsumption)
    {μ : ProbabilityMeasure P.State} (hμ : P.IsStationary μ) {z₁ z₀ : Z} {p₀ t U L : ℝ}
    (ht0 : 0 < t) (htcap : t ≤ assetCap) (htinc : t < P.income z₁)
    (hp : ∀ z, p₀ ≤ P.transitionMatrix z z₁)
    (hU : (η + P.income z₁ - t) ^ (-γ) ≤ U)
    (hL : L ≤ (η + P.income z₀ + (1 + P.interest) * t) ^ (-γ))
    (hcond : U * t
      < (P.discount : ℝ) * (P.transitionMatrix z₁ z₀ * (L * ((1 + P.interest) * (t / 2))))) :
    t / 2 * p₀ ≤ P.aggregateCapital μ := by
  refine P.hara_le_aggregateCapital_of_gain hγ0 hη hu hfl hpc hμ (z₀ := z₀) ht0 htcap htinc hp ?_
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hπ : (0 : ℝ) ≤ P.transitionMatrix z₁ z₀ := P.transitionMatrix_nonneg _ _
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hcost : (η + P.income z₁ - t) ^ (-γ) * t ≤ U * t :=
    mul_le_mul_of_nonneg_right hU ht0.le
  have hgainL : (P.discount : ℝ) * (P.transitionMatrix z₁ z₀ * (L * ((1 + P.interest) * (t / 2))))
      ≤ (P.discount : ℝ) * (P.transitionMatrix z₁ z₀
          * ((η + P.income z₀ + (1 + P.interest) * t) ^ (-γ) * ((1 + P.interest) * (t / 2)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL (by positivity)) hπ) hβ
  linarith

end Measure

end IncomeFluctuation

end LeanEconomics
