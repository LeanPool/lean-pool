/-
Copyright (c) 2026 Antonio Anna Mele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Anna Mele
-/
module

public import LeanPool.SingleCopyStabilizer.StabilizerState
public import LeanPool.SingleCopyStabilizer.ExactLearning


/-! The exact round's actual two-copy Born measurements and independent
correction bit induce precisely the finite kernel used in the tail proof. -/

@[expose] public section

noncomputable section

namespace LeanPool.SingleCopyStabilizer.PhysicalSampling

open Measurement
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Lagrangian label state underlying a physical stabilizer state. -/
def labels (S : PureStabilizerState ι) : ExactLearning.State ι :=
  ⟨S.labels, S.isotropic, S.maximal⟩

/-- Two independent fresh computational outcomes, their difference, then
an independent fair correction bit. -/
def outcomePMF (S : PureStabilizerState ι) : PMF (ExactLearning.Outcome ι) :=
  (bornDifferencePMF S.amplitude S.normalized).bind fun u =>
    (PMF.uniformOfFintype (ZMod 2)).map fun b => (u, b)

omit [DecidableEq ι] in
theorem correction_map_apply (u : Bits ι) (o : ExactLearning.Outcome ι) :
    ((PMF.uniformOfFintype (ZMod 2)).map fun b => (u, b)) o =
      if u = o.1 then (1 / 2 : ENNReal) else 0 := by
  classical
  rcases o with ⟨x, c⟩
  by_cases hu : u = x
  · subst u
    simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  · simp [PMF.map_apply, tsum_fintype, hu, Ne.symm hu]

theorem outcomePMF_apply (S : PureStabilizerState ι) (o : ExactLearning.Outcome ι) :
    outcomePMF S o = bornDifferencePMF S.amplitude S.normalized o.1 / 2 := by
  classical
  rw [outcomePMF, PMF.bind_apply, tsum_fintype]
  simp_rw [correction_map_apply]
  simp [mul_ite, div_eq_mul_inv]

/-- The label process's kernel is derived from the physical sampling PMF. -/
theorem outcomePMF_eq_kernel (S : PureStabilizerState ι) (o : ExactLearning.Outcome ι) :
    outcomePMF S o = ENNReal.ofReal (ExactLearning.weight (labels S) o) := by
  classical
  rw [outcomePMF_apply, S.bornDifferencePMF_uniform]
  unfold ExactLearning.weight labels
  dsimp only
  by_cases hu : o.1 ∈ xProjection S.labels
  · rw [ite_eq_left hu, ite_eq_left hu]
    rw [Nat.card_eq_fintype_card]
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  · simp [hu]

theorem outcomePMF_toReal (S : PureStabilizerState ι) (o : ExactLearning.Outcome ι) :
    (outcomePMF S o).toReal = ExactLearning.weight (labels S) o := by
  rw [outcomePMF_eq_kernel, ENNReal.toReal_ofReal (ExactLearning.weight_nonneg _ _)]

theorem outcomePMF_zero_of_not_mem (S : PureStabilizerState ι)
    (o : ExactLearning.Outcome ι) (hu : o.1 ∉ xProjection S.labels) :
    outcomePMF S o = 0 := by
  rw [outcomePMF_eq_kernel]
  simp [ExactLearning.weight, labels, hu]

end LeanPool.SingleCopyStabilizer.PhysicalSampling
