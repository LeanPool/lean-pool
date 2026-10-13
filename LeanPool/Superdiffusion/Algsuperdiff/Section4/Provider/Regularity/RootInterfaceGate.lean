/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootAssemblyChain
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.RootAssemblyParameters

/-!
# RootInterfaceGate

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The sharp criterion for the cube gate -/

/-- **The cube gate from the coordinate gaps.**  If every coordinate of `z` clears
`½·3^m − ½·3^q`, the translated cube `z + □_q` sits inside `□_m`. -/
theorem image_add_subset_openCubeSet_of_forall_abs_le {m q : ℤ} {z : Vec d}
    (h : ∀ i : Fin d,
      |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    (fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m) := by
  rintro p ⟨w, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hwi := hw i
  have hi := h i
  have hz1 : z i ≤ |z i| := le_abs_self _
  have hz2 : -(z i) ≤ |z i| := neg_le_abs _
  simp only [Pi.add_apply]
  exact ⟨by linarith only [hwi.1, hi, hz2], by linarith only [hwi.2, hi, hz1]⟩

/-- The upper half of the converse: the gate forces every coordinate to clear the
gap on the right.  The escaping point is exhibited explicitly. -/
private theorem coord_le_of_image_add_subset {m q : ℤ} {z : Vec d}
    (h : (fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m)) (i : Fin d) :
    z i + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  classical
  by_contra hcon
  push Not at hcon
  have hQ : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ q := by
    have := zpow_pos (by norm_num : (0 : ℝ) < 3) q
    linarith only [this]
  set a : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - z i with hadef
  have ha : a < (1 / 2 : ℝ) * (3 : ℝ) ^ q := by rw [hadef]; linarith only [hcon]
  set t : ℝ := (max a 0 + (1 / 2 : ℝ) * (3 : ℝ) ^ q) / 2 with htdef
  have hmax1 : a ≤ max a 0 := le_max_left _ _
  have hmax2 : (0 : ℝ) ≤ max a 0 := le_max_right _ _
  have hmax3 : max a 0 < (1 / 2 : ℝ) * (3 : ℝ) ^ q := max_lt ha hQ
  have ht1 : t < (1 / 2 : ℝ) * (3 : ℝ) ^ q := by rw [htdef]; linarith only [hmax3]
  have ht0 : (0 : ℝ) < t := by rw [htdef]; linarith only [hmax2, hQ]
  have hta : a ≤ t := by rw [htdef]; linarith only [hmax1, ha]
  have hw : (fun _ => t : Vec d) ∈ openCubeSet (originCube d q) := by
    rw [mem_openCubeSet_originCube_iff]
    exact fun _ => ⟨by linarith only [ht0, hQ], ht1⟩
  have hmem := h ⟨_, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hmem
  have hi : z i + t < (1 / 2 : ℝ) * (3 : ℝ) ^ m := (hmem i).2
  rw [hadef] at hta
  linarith only [hi, hta]

/-- The `z ↦ -z` symmetry of the gate: the origin cubes are symmetric, so a
translate fits on one side exactly when its reflection fits on the other. -/
private theorem image_add_subset_openCubeSet_neg {m q : ℤ} {z : Vec d}
    (h : (fun y => z + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m)) :
    (fun y => (-z) + y) '' openCubeSet (originCube d q) ⊆
      openCubeSet (originCube d m) := by
  rintro p ⟨w, hw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hw
  have hnw : (-w : Vec d) ∈ openCubeSet (originCube d q) := by
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi := hw i
    simp only [Pi.neg_apply]
    exact ⟨by linarith only [hi.2], by linarith only [hi.1]⟩
  have hmem := h ⟨-w, hnw, rfl⟩
  rw [mem_openCubeSet_originCube_iff] at hmem ⊢
  intro i
  have hi := hmem i
  simp only [Pi.add_apply, Pi.neg_apply] at hi ⊢
  exact ⟨by linarith only [hi.2], by linarith only [hi.1]⟩

/-- **The gate criterion, both directions.**  `z + □_q ⊆ □_m` holds exactly when
every coordinate of `z` clears the gap `½·3^m − ½·3^q`. -/
theorem image_add_subset_openCubeSet_iff {m q : ℤ} {z : Vec d} :
    ((fun y => z + y) '' openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d m)) ↔
      ∀ i : Fin d, |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  refine ⟨fun h i => ?_, image_add_subset_openCubeSet_of_forall_abs_le⟩
  have hup := coord_le_of_image_add_subset h i
  have hlo := coord_le_of_image_add_subset (image_add_subset_openCubeSet_neg h) i
  simp only [Pi.neg_apply] at hlo
  rcases le_or_gt 0 (z i) with hz | hz
  · rw [abs_of_nonneg hz]; exact hup
  · rw [abs_of_neg hz]; exact hlo

/-! ## 3. The truncated form, and the join's geometric half -/

/-- **The truncated window is untruncated exactly on the gated scales.**  This is
the dichotomy in the carrier the chain uses: `(z + □_q) ∩ □_m = z + □_q` iff
the gate holds, and otherwise the intersection is a subset. -/
theorem truncatedWindow_eq_image_add_iff {m q : ℤ} {z : Vec d} :
    truncatedWindow z m q = (fun y => z + y) '' openCubeSet (originCube d q) ↔
      (fun y => z + y) '' openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d m) :=
  Set.inter_eq_left

/-- **The join's window hypothesis holds centre scale.**

`ExcessDecay.excessDecay_oneStep_anchored` replaces the interior gate by the
disjunction "gate OR a met face of `∂□_m`"; its geometric half is a tautology,
because a window that meets no face of `∂□_m` in any coordinate clears the gap
in every coordinate.  So the boundary `hstep4` run owes the geometry nothing:
what it still needs from the join's second disjunct is the competitor data (the
`MemLp` clauses, met-face oddness and classical harmonicity on the doubled
window), which is analytic. -/
theorem gate_or_exists_meetsFace (z : Vec d) (m q : ℤ) :
    ((fun y => z + y) '' openCubeSet (originCube d q) ⊆
        openCubeSet (originCube d m)) ∨
      ∃ i : Fin d, MeetsUpperFace z m q i ∨ MeetsLowerFace z m q i := by
  classical
  by_cases h : ∀ i : Fin d,
      |z i| + (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m
  · exact Or.inl (image_add_subset_openCubeSet_of_forall_abs_le h)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    refine Or.inr ⟨i, ?_⟩
    rcases le_or_gt 0 (z i) with hz | hz
    · left
      change (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ z i + (1 / 2 : ℝ) * (3 : ℝ) ^ q
      rw [abs_of_nonneg hz] at hi
      linarith only [hi]
    · right
      change z i - (1 / 2 : ℝ) * (3 : ℝ) ^ q ≤ -(1 / 2 : ℝ) * (3 : ℝ) ^ m
      rw [abs_of_neg hz] at hi
      linarith only [hi]

end

end Algsuperdiff.Section4.Provider.Regularity
