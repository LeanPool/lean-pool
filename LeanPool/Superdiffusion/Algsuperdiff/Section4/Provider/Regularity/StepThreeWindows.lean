/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryLaneWindows

/-!
# StepThreeWindows

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 3: the window family `U_j := (z + □_j) ∩ □_m`

## The target

```
U_j := (z + □_j) ∩ □_m       for the (possibly truncated) cube at scale j ∈ ℤ.
```

The carrier is the development's existing `truncatedWindow` of
`ExcessDecay/BoundaryLaneWindows.lean` — `(x + □_k) ∩ □_m`, a translation
*image* of an origin cube intersected with the domain cube — read at the
lattice centre `x := z`.  It matches the Step-3 display literally, so no new
carrier is introduced; `stepThreeWindow` is only the scale-indexed *family* the
iteration lemma's binder `U : ℤ → Set (Vec d)` wants.

## What is delivered

`IterationWindowFamily U m` is the three-fold hypothesis block of the proved
anchor `Algsuperdiff.Frozen.Section4.iteration_lemma` transcribed verbatim:
measurability at every `j ≤ m`, the nesting `U (j-1) ⊆ U j`, and the sandwich
`∃ x y, x + □_{j-2} ⊆ U j ⊆ y + □_j`.
`iterationWindowFamily_stepThreeWindow` discharges it for the Step-3 family
from the single fact `z ∈ □_m` (the lattice centre lies in the domain cube)
and nothing else — the sandwich holds at every `j ≤ m`, including the truncated
ones.

## The sandwich, and why the lattice plays no role

Coordinatewise `U_j` is the interval `(max(z_i - h, -H), min(z_i + h, H))` with
`h = 3^j/2`, `H = 3^m/2`.  Its length is at least `h` in all four truncation
cases (`width_le`): `2h` when the cube is interior, `H - z_i + h > h` and
`z_i + H + h > h` at a single face — because `|z_i| < H` — and `2H ≥ h` when the
cube overflows both faces, which forces `j = m`.  Since `3^{j-2} = 3^j/9 ≤ h`,
the *centre of the truncated interval* is a legal inner centre `x`, and the
outer centre is `y := z` outright.  No lattice-gap estimate on `z` is used, so
the family is admissible for every centre in `□_m`, not only the triadic ones,
although the Step-3 text only ever needs the triadic centres.

## References

* ABK26, `t.regularity` Step 3, (the window family).
* ABK26, `l.iteration.lemma`, (the sandwich hypothesis).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

variable {d : ℕ}

/-! ## 1. The family -/

/-- **The Step-3 window family** `U_j := (z + □_j) ∩ □_m`, as the scale-indexed
family the iteration lemma's `U`-binder consumes. -/
def stepThreeWindow (z : Vec d) (m : ℤ) : ℤ → Set (Vec d) :=
  fun j => truncatedWindow z m j

/-- Each window is measurable (it is open). -/
theorem measurableSet_stepThreeWindow (z : Vec d) (m j : ℤ) :
    MeasurableSet (stepThreeWindow z m j) :=
  (isOpen_truncatedWindow z m j).measurableSet

/-- The family is nested: `U_{j-1} ⊆ U_j`. -/
theorem stepThreeWindow_sub_one_subset (z : Vec d) (m j : ℤ) :
    stepThreeWindow z m (j - 1) ⊆ stepThreeWindow z m j :=
  truncatedWindow_mono z m (by linarith only [] : j - 1 ≤ j)

/-! ## 2. The sandwich -/

/-- The truncated interval `(max(t-a,-A), min(t+a,A))` is at least `a` long,
whenever `|t| < A` and `a ≤ A`.  This is the scalar core of the window
sandwich. -/
private theorem width_le {A a t : ℝ} (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A)
    (hlo : -A < t) (hhi : t < A) :
    a ≤ min (t + a) A - max (t - a) (-A) := by
  rcases le_total (t + a) A with h1 | h1 <;> rcases le_total (t - a) (-A) with h2 | h2
  · rw [min_eq_left h1, max_eq_right h2]
    linarith only [hlo]
  · rw [min_eq_left h1, max_eq_left h2]
    linarith only [ha]
  · rw [min_eq_right h1, max_eq_right h2]
    linarith only [hA, haA]
  · rw [min_eq_right h1, max_eq_left h2]
    linarith only [hhi]

/-- **The inner half of the window sandwich** (the iteration lemma's hypothesis):
for every `j ≤ m` there is a centre `x` with `x + □_{j-2} ⊆ (z + □_j) ∩ □_m`.
The witness is the centre of the truncated window, coordinate by coordinate. -/
theorem exists_inner_cube_subset_stepThreeWindow (z : Vec d) {m j : ℤ}
    (hz : z ∈ openCubeSet (originCube d m)) (hjm : j ≤ m) :
    ∃ x : Vec d,
      (fun v => x + v) '' openCubeSet (originCube d (j - 2)) ⊆ stepThreeWindow z m j := by
  set a : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ j with ha_def
  set A : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m with hA_def
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hapos : 0 < a := by rw [ha_def]; linarith only [h3j]
  have hApos : 0 < A := by rw [hA_def]; linarith only [h3m]
  have haA : a ≤ A := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hjm
    rw [ha_def, hA_def]
    linarith only [h]
  have hzmem := mem_openCubeSet_originCube_iff.mp hz
  refine ⟨fun i => (max (z i - a) (-A) + min (z i + a) A) / 2, ?_⟩
  rintro p ⟨y, hy, rfl⟩
  have hymem := mem_openCubeSet_originCube_iff.mp hy
  have hhalf : (3 : ℝ) ^ (j - 2) ≤ a := by
    have h9 : (3 : ℝ) ^ (j - 2) = (3 : ℝ) ^ j / 9 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [h9, ha_def]
    linarith only [h3j]
  have key : ∀ i,
      max (z i - a) (-A) <
          (fun i => (max (z i - a) (-A) + min (z i + a) A) / 2) i + y i ∧
        (fun i => (max (z i - a) (-A) + min (z i + a) A) / 2) i + y i <
          min (z i + a) A := by
    intro i
    have hz1 : -A < z i := by rw [hA_def]; linarith only [(hzmem i).1]
    have hz2 : z i < A := by rw [hA_def]; linarith only [(hzmem i).2]
    have hw := width_le hApos hapos haA hz1 hz2
    have hy1 : -((1 : ℝ) / 2) * (3 : ℝ) ^ (j - 2) < y i := (hymem i).1
    have hy2 : y i < (1 / 2 : ℝ) * (3 : ℝ) ^ (j - 2) := (hymem i).2
    simp only []
    exact ⟨by linarith only [hw, hy1, hhalf], by linarith only [hw, hy2, hhalf]⟩
  constructor
  · refine ⟨fun i => (max (z i - a) (-A) + min (z i + a) A) / 2 + y i - z i, ?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have hk := key i
      have hmax : z i - a ≤ max (z i - a) (-A) := le_max_left _ _
      have hmin : min (z i + a) A ≤ z i + a := min_le_left _ _
      simp only [] at hk ⊢
      rw [ha_def] at hmax hmin
      exact ⟨by linarith only [hk.1, hmax], by linarith only [hk.2, hmin]⟩
    · funext i
      simp only [Pi.add_apply]
      ring
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hk := key i
    have hmax : -A ≤ max (z i - a) (-A) := le_max_right _ _
    have hmin : min (z i + a) A ≤ A := min_le_right _ _
    simp only [Pi.add_apply] at hk ⊢
    rw [hA_def] at hmax hmin
    exact ⟨by linarith only [hk.1, hmax], by linarith only [hk.2, hmin]⟩

/-- **The outer half of the window sandwich**: `U_j ⊆ z + □_j` outright. -/
theorem stepThreeWindow_subset_outer_cube (z : Vec d) (m j : ℤ) :
    stepThreeWindow z m j ⊆ (fun v => z + v) '' openCubeSet (originCube d j) :=
  truncatedWindow_subset_translate z m j

/-! ## 3. The iteration lemma's window binder block -/

/-- Measurable nested windows with inner and outer translated cube bounds. -/
def IterationWindowFamily (U : ℤ → Set (Vec d)) (m : ℤ) : Prop :=
  (∀ j : ℤ, j ≤ m → MeasurableSet (U j)) ∧
    (∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) ∧
    (∀ j : ℤ, j ≤ m →
      ∃ x y : Vec d,
        (fun v => x + v) '' openCubeSet (originCube d (j - 2)) ⊆ U j ∧
          U j ⊆ (fun v => y + v) '' openCubeSet (originCube d j))

/-- **The Step-3 windows are an admissible iteration family.**  The only input is
`z ∈ □_m`, which is half of the Step-3 hypothesis `z ∈ 3^n ℤ^d ∩ □_m`. -/
theorem iterationWindowFamily_stepThreeWindow (z : Vec d) (m : ℤ)
    (hz : z ∈ openCubeSet (originCube d m)) :
    IterationWindowFamily (stepThreeWindow z m) m := by
  refine ⟨fun j _ => measurableSet_stepThreeWindow z m j,
    fun j _ => stepThreeWindow_sub_one_subset z m j, fun j hj => ?_⟩
  obtain ⟨x, hx⟩ := exists_inner_cube_subset_stepThreeWindow z hz hj
  exact ⟨x, z, hx, stepThreeWindow_subset_outer_cube z m j⟩

end Algsuperdiff.Section4.Provider.Regularity
