/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# StepNineOffGridGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` off-grid transfer: the geometry

## The gap

The whole §4.4 proof runs at a lattice centre `z ∈ 3^n ℤ^d ∩ □_m` and ends on the
window `(z + □_{n+1}) ∩ □_m`, while `t.regularity` claims the estimate at an
arbitrary `x ∈ □_m` on `(x + □_n) ∩ □_m`.  The manuscript performs the transfer
nowhere: it is asserted in a single sentence.

## The construction: round toward the origin, not to the nearest lattice point

The admissible set of lattice centres is larger than the manuscript's implicit
"nearest point".  `x + □_n ⊆ z + □_{n+1}` asks only

```text
  |x_i − z_i| ≤ (3^{n+1} − 3^n)/2 = 3^n ,
```

an interval of length `2·3^n` around `x_i`, which contains BOTH `3^n⌊x_i/3^n⌋`
and `3^n⌈x_i/3^n⌉`.  Choosing between them by the SIGN of `x_i` — i.e. rounding
toward the origin — gives simultaneously

```text
  |x_i − z_i| < 3^n        and        |z_i| ≤ |x_i| .
```

The second inequality is what the nearest-point route does not have, and it is
exactly what needs: `z` inherits origin-cube membership of `x`.  In particular
`x ∈ □_m ⟹ z ∈ □_m` (the manuscript's own `z ∈ 3^nℤ^d ∩ □_m`) and `x ∈ □_{m−1}
⟹ z ∈ □_{m−1}` (the boundary indicator, see `StepNineOffGridIndicator`).  No
band enlargement is needed at any scale.

## What is delivered

* `offGridLatticeIndex`, `offGridCentre` — the integer index and the lattice
  point `3^n·v`, in `Support.triadicLatticePoint`'s own carrier;
* `abs_sub_offGridCentre_lt`, `abs_offGridCentre_le` — the two scalar facts;
* `offGridCentre_mem_openCubeSet` — `x ∈ □_k → z ∈ □_k` scale `k`;
* `offGridLatticeIndex_mem_latticeCubeSet` — `z` is a member of the Step-3
  lattice index set `Support.latticeCubeSet d n m`;
* `truncatedWindow_subset_offGrid` — `(x + □_n) ∩ □_m ⊆ (z + □_{n+1}) ∩ □_m`;
* `exists_inner_cube_subset_truncatedWindow` — the inscribed origin cube one
  scale down, the volume lower bound of `StepNineOffGridTransfer`.

## References

* ABK26, `t.regularity`, (the claim at every `x ∈ □_m`) (the lattice-centre
  endpoint and the asserted transfer).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

variable {d : ℕ}

/-! ## 1. The scalar rounding toward the origin -/

/-- The scale-`a` rounding of `t` toward the origin, as an integer. -/
noncomputable def truncIndex (a t : ℝ) : ℤ :=
  if 0 ≤ t then ⌊t / a⌋ else ⌈t / a⌉

/-- Rounding toward the origin moves `t` by strictly less than the lattice
spacing `a`. -/
private theorem truncIndex_dist {a t : ℝ} (ha : 0 < a) :
    |t - a * ((truncIndex a t : ℤ) : ℝ)| < a := by
  rcases le_or_gt 0 t with ht | ht
  · have hq : truncIndex a t = ⌊t / a⌋ := by
      rw [truncIndex, ite_eq_left ht]
    have h1 : ((⌊t / a⌋ : ℤ) : ℝ) ≤ t / a := Int.floor_le _
    have h2 : t / a < ((⌊t / a⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h1' : a * ((⌊t / a⌋ : ℤ) : ℝ) ≤ t := by
      have := mul_le_mul_of_nonneg_left h1 ha.le
      rwa [mul_div_cancel₀ t (ne_of_gt ha)] at this
    have h2' : t < a * ((⌊t / a⌋ : ℤ) : ℝ) + a := by
      have h := mul_lt_mul_of_pos_left h2 ha
      rwa [mul_div_cancel₀ t (ne_of_gt ha), mul_add, mul_one] at h
    rw [hq, abs_lt]
    exact ⟨by linarith only [h1', ha], by linarith only [h2']⟩
  · have hq : truncIndex a t = ⌈t / a⌉ := by
      rw [truncIndex, ite_eq_right (not_le.mpr ht)]
    have h1 : t / a ≤ ((⌈t / a⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h2 : ((⌈t / a⌉ : ℤ) : ℝ) < t / a + 1 := Int.ceil_lt_add_one _
    have h1' : t ≤ a * ((⌈t / a⌉ : ℤ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 ha.le
      rwa [mul_div_cancel₀ t (ne_of_gt ha)] at this
    have h2' : a * ((⌈t / a⌉ : ℤ) : ℝ) < t + a := by
      have h := mul_lt_mul_of_pos_left h2 ha
      rwa [mul_add, mul_div_cancel₀ t (ne_of_gt ha), mul_one] at h
    rw [hq, abs_lt]
    exact ⟨by linarith only [h2'], by linarith only [h1', ha]⟩

/-- Rounding toward the origin never increases the absolute value. -/
private theorem truncIndex_abs_le {a t : ℝ} (ha : 0 < a) :
    |a * ((truncIndex a t : ℤ) : ℝ)| ≤ |t| := by
  rcases le_or_gt 0 t with ht | ht
  · have hq : truncIndex a t = ⌊t / a⌋ := by
      rw [truncIndex, ite_eq_left ht]
    have hfl : (0 : ℤ) ≤ ⌊t / a⌋ := by
      have h0 : (0 : ℤ) = ⌊(0 : ℝ)⌋ := by simp
      rw [h0]
      exact Int.floor_mono (div_nonneg ht ha.le)
    have h1 : ((⌊t / a⌋ : ℤ) : ℝ) ≤ t / a := Int.floor_le _
    have h1' : a * ((⌊t / a⌋ : ℤ) : ℝ) ≤ t := by
      have := mul_le_mul_of_nonneg_left h1 ha.le
      rwa [mul_div_cancel₀ t (ne_of_gt ha)] at this
    have hnn : (0 : ℝ) ≤ a * ((⌊t / a⌋ : ℤ) : ℝ) :=
      mul_nonneg ha.le (by exact_mod_cast hfl)
    rw [hq, abs_of_nonneg hnn, abs_of_nonneg ht]
    exact h1'
  · have hq : truncIndex a t = ⌈t / a⌉ := by
      rw [truncIndex, ite_eq_right (not_le.mpr ht)]
    have hce : ⌈t / a⌉ ≤ (0 : ℤ) := by
      have h0 : (0 : ℤ) = ⌈(0 : ℝ)⌉ := by simp
      rw [h0]
      exact Int.ceil_mono (div_nonpos_of_nonpos_of_nonneg ht.le ha.le)
    have h1 : t / a ≤ ((⌈t / a⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h1' : t ≤ a * ((⌈t / a⌉ : ℤ) : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 ha.le
      rwa [mul_div_cancel₀ t (ne_of_gt ha)] at this
    have hnp : a * ((⌈t / a⌉ : ℤ) : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha.le (by exact_mod_cast hce)
    rw [hq, abs_of_nonpos hnp, abs_of_nonpos ht.le]
    linarith only [h1']

/-! ## 2. The off-grid lattice centre -/

/-- **The off-grid lattice index.**  The integer vector `v` with `3^n v` the
coordinatewise rounding of `x` toward the origin at spacing `3^n`. -/
noncomputable def offGridLatticeIndex (n : ℤ) (x : Vec d) : Fin d → ℤ :=
  fun i => truncIndex ((3 : ℝ) ^ n) (x i)

/-- **The off-grid lattice centre** `z ∈ 3^n ℤ^d`, in the Step-3 carrier
`Support.triadicLatticePoint`. -/
noncomputable def offGridCentre (n : ℤ) (x : Vec d) : Vec d :=
  Support.triadicLatticePoint n (offGridLatticeIndex n x)

/-- **The displacement bound**: `|x_i − z_i| < 3^n`, one full lattice spacing — the
slack the nearest-point route throws away. -/
theorem abs_sub_offGridCentre_lt (n : ℤ) (x : Vec d) (i : Fin d) :
    |x i - offGridCentre n x i| < (3 : ℝ) ^ n :=
  truncIndex_dist (zpow_pos (by norm_num) n)

/-- **The origin-monotonicity**: `|z_i| ≤ |x_i|`.  This is the fact the
manuscript's implicit nearest-point choice does not have, and the one that
makes the boundary indicator transfer without a band enlargement. -/
theorem abs_offGridCentre_le (n : ℤ) (x : Vec d) (i : Fin d) :
    |offGridCentre n x i| ≤ |x i| :=
  truncIndex_abs_le (zpow_pos (by norm_num) n)

/-- **Every origin-cube membership of `x` passes to `z`**, at every scale `k` and
for every `n`. -/
theorem offGridCentre_mem_openCubeSet {k : ℤ} (n : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d k)) :
    offGridCentre n x ∈ openCubeSet (originCube d k) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  intro i
  have habs := abs_offGridCentre_le n x i
  have hxi := hx i
  have hxabs : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
    abs_lt.mpr ⟨by linarith only [hxi.1], hxi.2⟩
  have hz := abs_lt.mp (lt_of_le_of_lt habs hxabs)
  exact ⟨by linarith only [hz.1], hz.2⟩

/-- **`z` is a Step-3 lattice centre**: its index lies in `Support.latticeCubeSet d
n m`, i.e. `z ∈ 3^n ℤ^d ∩ □_m`. -/
theorem offGridLatticeIndex_mem_latticeCubeSet {m : ℤ} (n : ℤ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    offGridLatticeIndex n x ∈ Support.latticeCubeSet d n m :=
  offGridCentre_mem_openCubeSet n hx

/-! ## 3. The window inclusion -/

/-- **The cube inclusion** `x + □_n ⊆ z + □_{n+1}`: the centred cube at an
arbitrary point sits inside the ONE-S cube at its toward-origin lattice point. -/
theorem image_add_subset_offGridCentre (n : ℤ) (x : Vec d) :
    (fun v => x + v) '' openCubeSet (originCube d n) ⊆
      (fun v => offGridCentre n x + v) '' openCubeSet (originCube d (n + 1)) := by
  rintro p ⟨v, hv, rfl⟩
  have hvc := mem_openCubeSet_originCube_iff.mp hv
  have h1 : (3 : ℝ) ^ (n + 1) = 3 * (3 : ℝ) ^ n := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  refine ⟨x + v - offGridCentre n x, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hd := abs_lt.mp (abs_sub_offGridCentre_lt n x i)
    have hvi := hvc i
    simp only [Pi.sub_apply, Pi.add_apply]
    exact ⟨by linarith only [hd.1, hvi.1, h1], by linarith only [hd.2, hvi.2, h1]⟩
  · funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring

/-- **The truncated-window inclusion** (the shape `t.regularity` consumes):

```text
  (x + □_n) ∩ □_m  ⊆  (z + □_{n+1}) ∩ □_m ,        z = offGridCentre n x .
``` -/
theorem truncatedWindow_subset_offGrid (n m : ℤ) (x : Vec d) :
    truncatedWindow x m n ⊆ truncatedWindow (offGridCentre n x) m (n + 1) :=
  Set.inter_subset_inter_left _ (image_add_subset_offGridCentre n x)

/-! ## 4. The inscribed origin cube, one scale down -/

/-- The truncated interval `(max(t−a,−A), min(t+a,A))` is at least `a` long when
`|t| < A` and `a ≤ A`.  (The scalar core of the Step-3 sandwich, re-proved here:
`StepThreeWindows`'s copy is `private`.) -/
private theorem truncatedWidth_le {A a t : ℝ} (hA : 0 < A) (ha : 0 < a)
    (haA : a ≤ A) (hlo : -A < t) (hhi : t < A) :
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

/-- **An inscribed origin cube one scale down.**  For every centre `x ∈ □_m` and
every `k ≤ m` the truncated window `(x + □_k) ∩ □_m` contains a translate of
`□_{k−1}`. -/
theorem exists_inner_cube_subset_truncatedWindow (x : Vec d) {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    ∃ y : Vec d,
      (fun v => y + v) '' openCubeSet (originCube d (k - 1)) ⊆ truncatedWindow x m k := by
  set a : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ k with ha_def
  set A : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m with hA_def
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hapos : 0 < a := by rw [ha_def]; linarith only [h3k]
  have hApos : 0 < A := by rw [hA_def]; linarith only [h3m]
  have haA : a ≤ A := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkm
    rw [ha_def, hA_def]
    linarith only [h]
  have hxmem := mem_openCubeSet_originCube_iff.mp hx
  have hhalf : (3 : ℝ) ^ (k - 1) ≤ a := by
    have h3 : (3 : ℝ) ^ (k - 1) = (3 : ℝ) ^ k / 3 := by
      rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [h3, ha_def]
    linarith only [h3k]
  refine ⟨fun i => (max (x i - a) (-A) + min (x i + a) A) / 2, ?_⟩
  rintro p ⟨y, hy, rfl⟩
  have hymem := mem_openCubeSet_originCube_iff.mp hy
  have key : ∀ i,
      max (x i - a) (-A) <
          (fun i => (max (x i - a) (-A) + min (x i + a) A) / 2) i + y i ∧
        (fun i => (max (x i - a) (-A) + min (x i + a) A) / 2) i + y i <
          min (x i + a) A := by
    intro i
    have hx1 : -A < x i := by rw [hA_def]; linarith only [(hxmem i).1]
    have hx2 : x i < A := by rw [hA_def]; linarith only [(hxmem i).2]
    have hw := truncatedWidth_le hApos hapos haA hx1 hx2
    have hy1 : -((1 : ℝ) / 2) * (3 : ℝ) ^ (k - 1) < y i := (hymem i).1
    have hy2 : y i < (1 / 2 : ℝ) * (3 : ℝ) ^ (k - 1) := (hymem i).2
    simp only []
    exact ⟨by linarith only [hw, hy1, hhalf], by linarith only [hw, hy2, hhalf]⟩
  constructor
  · refine ⟨fun i => (max (x i - a) (-A) + min (x i + a) A) / 2 + y i - x i, ?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have hk := key i
      have hmax : x i - a ≤ max (x i - a) (-A) := le_max_left _ _
      have hmin : min (x i + a) A ≤ x i + a := min_le_left _ _
      simp only [] at hk ⊢
      rw [ha_def] at hmax hmin
      exact ⟨by linarith only [hk.1, hmax], by linarith only [hk.2, hmin]⟩
    · funext i
      simp only [Pi.add_apply]
      ring
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hk := key i
    have hmax : -A ≤ max (x i - a) (-A) := le_max_right _ _
    have hmin : min (x i + a) A ≤ A := min_le_right _ _
    simp only [Pi.add_apply] at hk ⊢
    rw [hA_def] at hmax hmin
    exact ⟨by linarith only [hk.1, hmax], by linarith only [hk.2, hmin]⟩

end Algsuperdiff.Section4.Provider.Regularity
