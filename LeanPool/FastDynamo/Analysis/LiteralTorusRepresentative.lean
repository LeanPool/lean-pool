/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Analysis.LiteralThreeTorus
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The canonical `(0,1]³` section of the quotient `ℝ³ → T³`

`literalTorusPoint : ℝ³ → T³` (`FastDynamo/Analysis/LiteralThreeTorus.lean`) has a canonical
*measurable* section: send a point of the literal three-torus to the representative all of whose
coordinates lie in `(0,1]`.  Measurability is what makes a quantity defined on `ℝ³` and read at
the representative a measurable function on `T³` without any quotient-topology argument, and the
uniform bound `‖·‖ ≤ 2` confines all representatives to one fixed compact ball, which is what
turns a continuous function on `ℝ³` into a bounded function on `T³`.

## Contents

* `literalIocRepresentative`, its coordinates, its measurability, the section property
  `literalTorusPoint_literalIocRepresentative` (hence `literalTorusPoint_surjective`), the
  membership `literalIocRepresentative_mem_Ioc` and the bound `norm_literalIocRepresentative_le`.
* `literalIocPair`, the transverse coordinate pair of the representative: it lands in the
  fundamental box `pairUnitIocBox`, projects to the transverse block of the point, and is
  measurable.  The derivative flows of `FastDynamo/Dynamics/Flow/FlowDerivative.lean` and
  `FastDynamo/Dynamics/Ideal/TruncatedFlow.lean` are defined by reading a plane block matrix at
  this pair.

Nothing here depends on the velocity, on a flow or on a parameter.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

/-! ## The canonical fundamental-domain section of `ℝ³ → T³` -/

/-- The canonical `(0,1]³` representative of a point of the literal three-torus.  This is the
three-dimensional companion of `TransverseSmoothBumpPeriodization.wholePlaneIocRepresentative`. -/
def literalIocRepresentative (x : Torus 3) : R3 :=
  WithLp.toLp 2 fun j : Fin 3 ↦ ((AddCircle.equivIoc 1 0 (x j) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)

/-- Coordinates of the canonical representative. -/
@[simp] theorem literalIocRepresentative_apply (x : Torus 3) (j : Fin 3) :
    literalIocRepresentative x j =
      ((AddCircle.equivIoc 1 0 (x j) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) :=
  rfl

/-- Choosing the canonical representative is a measurable section of the quotient map.  This is
what makes derivatives read at the representative measurable functions on the torus. -/
theorem measurable_literalIocRepresentative : Measurable literalIocRepresentative := by
  apply (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp
  refine Measurable.of_eval fun j ↦ ?_
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 0).measurable.comp (measurable_pi_apply j))

/-- The canonical representative is a representative: it projects back to the point. -/
@[simp] theorem literalTorusPoint_literalIocRepresentative (x : Torus 3) :
    literalTorusPoint (literalIocRepresentative x) = x := by
  funext j
  change (((AddCircle.equivIoc 1 0 (x j) : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : UnitAddCircle) = x j
  exact (AddCircle.equivIoc 1 0).symm_apply_apply (x j)

/-- The quotient `ℝ³ → T³` is surjective. -/
theorem literalTorusPoint_surjective : Function.Surjective literalTorusPoint :=
  fun x ↦ ⟨literalIocRepresentative x, literalTorusPoint_literalIocRepresentative x⟩

/-- Every coordinate of the canonical representative lies in `(0,1]`. -/
theorem literalIocRepresentative_mem_Ioc (x : Torus 3) (j : Fin 3) :
    literalIocRepresentative x j ∈ Set.Ioc (0 : ℝ) (0 + 1) :=
  (AddCircle.equivIoc 1 0 (x j)).2

/-- A vector all of whose coordinates are bounded by one has Euclidean norm at most two. -/
theorem norm_r3_le_two_of_forall_abs_le_one {a : R3} (h : ∀ j, |a j| ≤ 1) : ‖a‖ ≤ 2 := by
  rw [EuclideanSpace.norm_eq]
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j : Fin 3, ‖a j‖ ^ 2 ≤ ∑ _j : Fin 3, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have hj := h j
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (a j)]
    _ ≤ 4 := by norm_num

/-- The canonical representatives all lie in the closed ball of radius two. -/
theorem norm_literalIocRepresentative_le (x : Torus 3) :
    ‖literalIocRepresentative x‖ ≤ 2 := by
  refine norm_r3_le_two_of_forall_abs_le_one fun j ↦ ?_
  obtain ⟨hpos, hle⟩ := literalIocRepresentative_mem_Ioc x j
  rw [abs_of_pos hpos]
  linarith

/-- A continuous function on `ℝ³` is bounded along the canonical representatives, because these
all lie in one fixed compact ball. -/
theorem exists_bound_comp_literalIocRepresentative {F : Type*} [NormedAddCommGroup F]
    {f : R3 → F} (hf : Continuous f) :
    ∃ M : ℝ, ∀ x : Torus 3, ‖f (literalIocRepresentative x)‖ ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : R3) 2).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, fun x ↦ hM _ ?_⟩
  simpa [Metric.mem_closedBall] using norm_literalIocRepresentative_le x

/-! ## The transverse representative of a torus point -/

/-- The transverse coordinate pair of the canonical `(0,1]³` representative of a torus point. -/
def literalIocPair (x : Torus 3) : ℝ × ℝ :=
  (literalIocRepresentative x 0, literalIocRepresentative x 1)

/-- The transverse representative lies in the fundamental box `(0,1]²`. -/
theorem literalIocPair_mem_pairUnitIocBox (x : Torus 3) : literalIocPair x ∈ pairUnitIocBox := by
  have h0 := literalIocRepresentative_mem_Ioc x 0
  have h1 := literalIocRepresentative_mem_Ioc x 1
  rw [zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-- The transverse representative projects to the transverse block of the point. -/
theorem transverseTorusPoint_literalIocPair (x : Torus 3) :
    transverseTorusPoint (literalIocPair x) = fun j : Fin 2 ↦ x j.castSucc := by
  have hc := literalTorusPoint_castSucc (literalIocRepresentative x)
  rw [literalTorusPoint_literalIocRepresentative] at hc
  exact hc.symm

/-- The transverse representative is a measurable function of the torus point: it is the
measurable section `literalIocRepresentative` followed by two continuous coordinate
projections. -/
theorem measurable_literalIocPair : Measurable literalIocPair :=
  (((EuclideanSpace.proj (0 : Fin 3) : R3 →L[ℝ] ℝ)).continuous.measurable.comp
      measurable_literalIocRepresentative).prodMk
    (((EuclideanSpace.proj (1 : Fin 3) : R3 →L[ℝ] ℝ)).continuous.measurable.comp
      measurable_literalIocRepresentative)

end

end FastDynamo
