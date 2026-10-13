/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.PositiveShift
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# ResolventDenseRange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Dense range from normalized resolvent convergence

This module isolates the elementary implication from the resolvent identity and
strong normalization at large positive shifts to dense range at every fixed
shift.
-/

open Filter Set Topology

namespace DivergenceFormProcess.Semigroup

open MarkovProcess.Semigroup


/-- A resolvent family whose normalized operators converge pointwise to the
identity has dense range at every positive shift. -/
theorem denseRange_of_resolvent_identity_of_tendsto_scaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : PositiveShift → E →L[ℝ] E)
    (hRI : ∀ α β,
      R α - R β =
        ((β : ℝ) - (α : ℝ)) • ((R α).comp (R β)))
    (hN : ∀ f,
      Tendsto (fun α : PositiveShift ↦ (α : ℝ) • R α f) atTop (nhds f)) :
    ∀ μ, DenseRange (R μ) := by
  intro μ
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  apply mem_closure_of_tendsto (hN f)
  filter_upwards [] with α
  refine ⟨(α : ℝ) •
      (f - (((α : ℝ) - (μ : ℝ)) • R α f)), ?_⟩
  have h := DFunLike.congr_fun (hRI μ α) f
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply] at h
  rw [map_smul, map_sub, map_smul]
  calc
    (α : ℝ) • (R μ f - ((α : ℝ) - (μ : ℝ)) • R μ (R α f)) =
        (α : ℝ) • R α f := by
      rw [← h]
      abel_nf

end DivergenceFormProcess.Semigroup
