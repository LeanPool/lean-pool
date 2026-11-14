/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.AxisCube

/-!
# Cubes

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A centered cubic exhaustion of Euclidean space

The whole-space divergence-form construction uses the open cubes
`(-3^m, 3^m)^d`.  This file records their elementary geometry independently
of the analytic resolvents built on them.
-/

namespace DivergenceFormProcess.Form

open HCPolySupport

noncomputable section

/-- The open cube `(-3^m, 3^m)^d`. -/
def wholeSpaceCube (d m : ℕ) : Set (Vec d) :=
  axisCube (fun _ => -((3 : ℝ) ^ m)) (2 * (3 : ℝ) ^ m)

@[simp] theorem mem_wholeSpaceCube_iff {d m : ℕ} {x : Vec d} :
    x ∈ wholeSpaceCube d m ↔ ∀ i, -((3 : ℝ) ^ m) < x i ∧ x i < (3 : ℝ) ^ m := by
  simp only [wholeSpaceCube, axisCube, Set.mem_pi, Set.mem_univ, forall_const,
    Set.mem_Ioo]
  have hendpoint : -((3 : ℝ) ^ m) + 2 * (3 : ℝ) ^ m = (3 : ℝ) ^ m := by
    ring
  constructor
  · intro h i
    simpa only [hendpoint] using h i
  · intro h i
    simpa only [hendpoint] using h i

/-- Every exhaustion cube is an open bounded convex domain. -/
theorem isOpenBoundedConvexDomain_wholeSpaceCube (d m : ℕ) :
    IsOpenBoundedConvexDomain (wholeSpaceCube d m) :=
  isOpenBoundedConvexDomain_axisCube _ _

/-- Consecutive cubes in the exhaustion are nested. -/
theorem wholeSpaceCube_subset_succ (d m : ℕ) :
    wholeSpaceCube d m ⊆ wholeSpaceCube d (m + 1) := by
  intro x hx
  rw [mem_wholeSpaceCube_iff] at hx ⊢
  intro i
  have hpow : (3 : ℝ) ^ m < (3 : ℝ) ^ (m + 1) := by
    rw [pow_succ]
    have hpos : 0 < (3 : ℝ) ^ m := pow_pos (by norm_num) _
    linarith only [hpos]
  exact ⟨lt_trans (neg_lt_neg hpow) (hx i).1, (hx i).2.trans hpow⟩

end

end DivergenceFormProcess.Form
