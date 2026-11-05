/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepThreeWindows

/-!
# StepSevenSandwich

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7a: the sandwich centres `z'`, `z''`

## The target

```text
  We may find a pair z', z'' ∈ □_m such that, for each (y', k') ∈ {(z',m'), (z'',n')},
      (z + □_{k'-1}) ∩ □_m  ⊆  y' + □_{k'-1}  ⊆  (z + □_{k'}) ∩ □_m .
```

## The construction

Write `a := ½·3^{k'-1}` (the half-side of the inner cube) and `A := ½·3^m` (the
half-side of `□_m`).  The centre is the coordinatewise of `z` into the inset
box `[-A+a, A-a]^d`:

```text
  y'_i := max( -A + a , min( z_i , A - a ) ) .
```

Three elementary facts do everything, and each is a two-line `max`/`min`
manipulation (`clamp_mem`, `clamp_capture`, `clamp_dist` below):

* `-A + a ≤ y'_i ≤ A - a`, so `y' + □_{k'-1} ⊆ □_m` — this is the inclusion the
  identity choice `y' := z` at a boundary centre;
* `min(z_i, A-a) ≤ y'_i ≤ max(-A+a, z_i)`, which captures every point of
  `(z + □_{k'-1}) ∩ □_m` (a point of the window is within `a` of `z_i` AND
  within `A` of the origin, so it is within `a` of the clamp);
* `|y'_i - z_i| ≤ 2a`, so `y' + □_{k'-1} ⊆ z + □_{k'}` (the outer cube has half
  side `3a`).

Only `a ≤ A` (i.e. `k' - 1 ≤ m`) and `z ∈ □_m` are used; no lattice structure
of `z` is needed, matching(c).

## What is delivered

* `exists_sandwich_centre` — the sandwich at a general inner index `k`:
  `(z + □_k) ∩ □_m ⊆ y + □_k ⊆ (z + □_{k+1}) ∩ □_m` with `y ∈ □_m`.
* `exists_stepSevenSandwich` — the same in the printed indexing `(k'-1, k')`.

## References

* ABK26, `t.regularity` Step 7, (the sandwich).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay

variable {d : ℕ}

/-! ## 1. The scalar clamp -/

/-- The clamp of `t` into `[-A+a, A-a]` proves there (`a ≤ A`). -/
private theorem clamp_mem {A a t : ℝ} (haA : a ≤ A) :
    -A + a ≤ max (-A + a) (min t (A - a)) ∧
      max (-A + a) (min t (A - a)) ≤ A - a :=
  ⟨le_max_left _ _, max_le (by linarith only [haA]) (min_le_right _ _)⟩

/-- The clamp captures the truncated window: a point `p` with `|p - t| < a` and
`|p| < A` is within `a` of the clamp of `t`. -/
private theorem clamp_capture {A a t p : ℝ} (hlo : -A < p) (hhi : p < A)
    (hpt1 : t - a < p) (hpt2 : p < t + a) :
    p - a < max (-A + a) (min t (A - a)) ∧
      max (-A + a) (min t (A - a)) < p + a :=
  ⟨lt_of_lt_of_le (lt_min (by linarith only [hpt2]) (by linarith only [hhi]))
      (le_max_right _ _),
    lt_of_le_of_lt (max_le_max (le_refl (-A + a)) (min_le_left t (A - a)))
      (max_lt (by linarith only [hlo]) (by linarith only [hpt1]))⟩

/-- The clamp moves `t` by at most `2a` when `|t| < A`. -/
private theorem clamp_dist {A a t : ℝ} (hapos : 0 < a) (hlo : -A < t)
    (hhi : t < A) :
    t - 2 * a ≤ max (-A + a) (min t (A - a)) ∧
      max (-A + a) (min t (A - a)) ≤ t + 2 * a :=
  ⟨le_trans (le_min (by linarith only [hapos]) (by linarith only [hhi, hapos]))
      (le_max_right _ _),
    le_trans (max_le_max (le_refl (-A + a)) (min_le_left t (A - a)))
      (max_le (by linarith only [hlo, hapos]) (by linarith only [hapos]))⟩

/-! ## 2. The sandwich -/

/-- ```text
  (z + □_k) ∩ □_m  ⊆  y + □_k  ⊆  (z + □_{k+1}) ∩ □_m .
```

The witness is the coordinatewise clamp of `z` into the inset box; see the
module docstring. -/
theorem exists_sandwich_centre (z : Vec d) {m k : ℤ}
    (hz : z ∈ openCubeSet (originCube d m)) (hkm : k ≤ m) :
    ∃ y : Vec d, y ∈ openCubeSet (originCube d m) ∧
      truncatedWindow z m k ⊆ (fun v => y + v) '' openCubeSet (originCube d k) ∧
      (fun v => y + v) '' openCubeSet (originCube d k) ⊆
        truncatedWindow z m (k + 1) := by
  have h3k : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h3km : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ m :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hkm
  have hk1 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (1 / 2 : ℝ) * (3 : ℝ) ^ k := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 / 2 : ℝ) * (3 : ℝ) ^ m := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; linarith only [h3k]
  have haA : a ≤ A := by rw [ha, hA]; linarith only [h3km]
  have hzc := mem_openCubeSet_originCube_iff.mp hz
  obtain ⟨y, hy⟩ : ∃ y : Vec d, ∀ i, y i = max (-A + a) (min (z i) (A - a)) :=
    ⟨fun i => max (-A + a) (min (z i) (A - a)), fun _ => rfl⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [mem_openCubeSet_originCube_iff]
    intro i
    have hc := clamp_mem (A := A) (a := a) (t := z i) haA
    rw [hy i]
    exact ⟨by linarith only [hc.1, hA, hapos], by linarith only [hc.2, hA, hapos]⟩
  · intro p hp
    have hpz := mem_openCubeSet_originCube_iff.mp
      (sub_mem_openCubeSet_of_mem_truncatedWindow hp)
    have hpm := mem_openCubeSet_originCube_iff.mp
      (truncatedWindow_subset_domain z m k hp)
    refine ⟨p - y, ?_, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have h1 := hpz i
      rw [Pi.sub_apply] at h1
      have hcc := clamp_capture (A := A) (a := a) (t := z i) (p := p i)
        (by linarith only [(hpm i).1, hA]) (by linarith only [(hpm i).2, hA])
        (by linarith only [h1.1, ha]) (by linarith only [h1.2, ha])
      rw [Pi.sub_apply, hy i]
      exact ⟨by linarith only [hcc.2, ha], by linarith only [hcc.1, ha]⟩
    · funext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
  · rintro p ⟨v, hv, rfl⟩
    have hvc := mem_openCubeSet_originCube_iff.mp hv
    rw [truncatedWindow]
    refine ⟨⟨y + v - z, ?_, ?_⟩, ?_⟩
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have hcd := clamp_dist (A := A) (a := a) (t := z i) hapos
        (by linarith only [(hzc i).1, hA]) (by linarith only [(hzc i).2, hA])
      rw [← hy i] at hcd
      rw [Pi.sub_apply, Pi.add_apply]
      exact ⟨by linarith only [hcd.1, (hvc i).1, ha, hk1],
        by linarith only [hcd.2, (hvc i).2, ha, hk1]⟩
    · funext i
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    · rw [mem_openCubeSet_originCube_iff]
      intro i
      have hc := clamp_mem (A := A) (a := a) (t := z i) haA
      rw [← hy i] at hc
      simp only [Pi.add_apply]
      exact ⟨by linarith only [hc.1, (hvc i).1, ha, hA],
        by linarith only [hc.2, (hvc i).2, ha, hA]⟩

/-- **The Step-7a sandwich in the printed indexing**: at the selected scale `k'`,

```text
  (z + □_{k'-1}) ∩ □_m  ⊆  y' + □_{k'-1}  ⊆  (z + □_{k'}) ∩ □_m ,     y' ∈ □_m .
``` -/
theorem exists_stepSevenSandwich (z : Vec d) {m k' : ℤ}
    (hz : z ∈ openCubeSet (originCube d m)) (hk : k' - 1 ≤ m) :
    ∃ y : Vec d, y ∈ openCubeSet (originCube d m) ∧
      truncatedWindow z m (k' - 1) ⊆
        (fun v => y + v) '' openCubeSet (originCube d (k' - 1)) ∧
      (fun v => y + v) '' openCubeSet (originCube d (k' - 1)) ⊆
        truncatedWindow z m k' := by
  obtain ⟨y, hymem, hin, hout⟩ := exists_sandwich_centre z hz hk
  refine ⟨y, hymem, hin, ?_⟩
  rwa [show k' - 1 + 1 = k' by ring] at hout

end Algsuperdiff.Section4.Provider.Regularity
