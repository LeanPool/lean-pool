/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Domains
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
Closedness, compactness, and the exact radius identity for successive closed-ball erosions.
-/

@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal Pointwise
namespace KamProject.Arnold1963

variable {E : Type*} [NormedAddCommGroup E]

theorem erosion_eq_iInter (U : Set E) (r : ℝ≥0) :
    erosion U r = ⋂ v ∈ closedBall (0 : E) r, (fun x => x + v) ⁻¹' U := by
  ext x
  simp only [mem_iInter, mem_preimage]
  constructor
  · intro hx v hv
    exact hx (by simpa [dist_eq_norm] using hv)
  · intro hx y hy
    have hv : y - x ∈ closedBall (0 : E) r := by simpa [dist_eq_norm] using hy
    simpa using hx (y - x) hv

theorem isClosed_erosion {U : Set E} (hU : IsClosed U) (r : ℝ≥0) :
    IsClosed (erosion U r) := by
  rw [erosion_eq_iInter]
  exact isClosed_iInter fun _ => isClosed_iInter fun _ =>
    hU.preimage (continuous_id.add continuous_const)

theorem isCompact_erosion {U : Set E} (hU : IsCompact U) (r : ℝ≥0) :
    IsCompact (erosion U r) :=
  hU.of_isClosed_subset (isClosed_erosion hU.isClosed r) (erosion_subset U r)

theorem erosion_add [NormedSpace ℝ E] [ProperSpace E] (U : Set E) (r s : ℝ≥0) :
    erosion (erosion U r) s = erosion U (r + s) := by
  ext x
  constructor
  · intro hx y hy
    have hy' : y ∈ closedBall x (s : ℝ) + closedBall (0 : E) (r : ℝ) := by
      rw [closedBall_add_closedBall s.coe_nonneg r.coe_nonneg, add_zero]
      simpa [NNReal.coe_add, add_comm] using hy
    obtain ⟨z, hz, v, hv, rfl⟩ := hy'
    exact hx hz (by simpa [dist_eq_norm] using hv)
  · intro hx y hy z hz
    apply hx
    exact (dist_triangle z y x).trans (by
      change dist z y ≤ (r : ℝ) at hz
      change dist y x ≤ (s : ℝ) at hy
      exact add_le_add hz hy)

end KamProject.Arnold1963
