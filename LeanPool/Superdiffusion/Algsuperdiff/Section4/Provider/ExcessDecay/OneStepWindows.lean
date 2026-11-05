/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringVolume
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationLemmaProviderGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.QuasiMonotone

/-!
# OneStepWindows

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The one-step window family `U_j = (x+□_{n-j}) ∩ □_m` and its geometry

`l.excess.decay.good.scales` runs on the truncated family

```text
  U_j := (x + □_{n-j}) ∩ □_m ,     j ∈ ℕ₀ ,
```

which is `BoundaryLaneWindows.truncatedWindow x m (n-j)`.  This module proves
the geometry every later leg of the one-step contraction reads off:

* `exists_axisCube_sandwich_truncatedWindow` — the aspect-`1/9` sandwich
  `axisCube zin 3^{k-2} ⊆ (x+□_k) ∩ □_m ⊆ axisCube zout 3^k`, obtained from the
  proved inscribed cube (`image_add_wellPlacedCentre_subset_truncatedWindow`,
  which sits at scale `k-1`) and the proved outer inclusion.  This is the slot
  every `…_of_axisCubeSandwich` producer of the excess layer consumes, and it
  is what makes the `|W|^{-1/d}` normalizer comparable to `3^{-k}` on a
  *truncated* window.
* the volume bounds, the normalizer bounds, positivity, measurability, the
  `MemLp`/`IntegrableOn` slots, and the explicit volume ratio of two nested
  windows of the family;
* `affineExcess_truncatedWindow_le` — excess quasi-monotonicity on the family, at
  the explicit ratio constant;
* **`image_add_wellPlacedCentre_subset_windowChoice`** — the window choice at
  the clamped centre.

## The window choice

The source asserts the existence of `y ∈ □_m` with *both*
`y+□_{n-2} ⊆ (z+□_n) ∩ □_m` and `(x+□_{n-2}) ∩ □_m ⊆ y+□_{n-2}` and exhibits no
construction; and the harmonic lemma instantiated at index `n-2` in fact demands
the *stronger* inclusion `y+□_{n-2} ⊆ (z+□_{n-1}) ∩ □_m`, which the printed
window choice does not supply.

Both are supplied here at the explicit witness

```text
  y := wellPlacedCentre x m (n-2)          (the coordinatewise clamp of x)
```

`image_add_wellPlacedCentre_subset_windowChoice` proves the *stronger*
inclusion `y + □_{n-2} ⊆ (z+□_{n-1}) ∩ □_m` from `x ∈ (z+□_{n-3}) ∩ □_m` and
`n-2 ≤ m` alone, and the second requirement is the proved
`truncatedWindow_subset_image_add_wellPlacedCentre` at `j = k = n-2`.  The
half-width budget is `3^{n-2}/2 + 3^{n-2}/2 + 3^{n-3}/2 = 3.5·3^{n-3}` against
the target `3^{n-1}/2 = 4.5·3^{n-3}`: slack `3^{n-3}`, so the witness is not
borderline.  Note the clamp `y` is a *full* cube centre — the boundary-regime
obstruction described in `BoundaryLaneWindows` concerns the window `(x+□_k) ∩
□_m` itself, not the enclosing full cube, and the two are compatible.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Measurability and the sandwich -/

theorem measurableSet_truncatedWindow (x : Vec d) (m k : ℤ) :
    MeasurableSet (truncatedWindow x m k) :=
  (isOpen_truncatedWindow x m k).measurableSet

/-- **The aspect-`1/9` sandwich of a truncated window.**

The proved inscribed cube sits at scale `k-1`; shrinking it to `k-2` and
reading both inclusions in `axisCube` shape gives exactly the sandwich slot the
excess layer's `…_of_axisCubeSandwich` producers consume. -/
theorem exists_axisCube_sandwich_truncatedWindow {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    ∃ zin zout : Vec d,
      axisCube zin ((3 : ℝ) ^ (k - 2)) ⊆ truncatedWindow x m k ∧
        truncatedWindow x m k ⊆ axisCube zout ((3 : ℝ) ^ k) := by
  refine axisCube_sandwich_of_translateSandwich
    (x := wellPlacedCentre x m (k - 1)) (y := x) ?_ (truncatedWindow_subset_translate x m k)
  refine subset_trans ?_ (image_add_wellPlacedCentre_subset_truncatedWindow x hx hkm)
  rintro p ⟨w, hw, rfl⟩
  exact ⟨w, openCubeSet_originCube_subset_of_le (by omega) hw, rfl⟩

/-! ## 2. Volumes, normalizers and the analytic slots -/

theorem volume_toReal_truncatedWindow_bounds {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    ((3 : ℝ) ^ (k - 2)) ^ d ≤ (volume (truncatedWindow x m k)).toReal ∧
      (volume (truncatedWindow x m k)).toReal ≤ ((3 : ℝ) ^ k) ^ d := by
  obtain ⟨zin, zout, hin, hout⟩ := exists_axisCube_sandwich_truncatedWindow x hx hkm
  exact volume_toReal_bounds_of_axisCubeSandwich (d := d) (zin := zin) (zout := zout) hin hout

theorem volume_toReal_truncatedWindow_pos {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    0 < (volume (truncatedWindow x m k)).toReal :=
  lt_of_lt_of_le (by positivity) (volume_toReal_truncatedWindow_bounds x hx hkm).1

/-- The two-sided comparison of the `|W|^{-1/d}` normalizer with the cube
normalizer `3^{-k}` on a truncated window. -/
theorem rpow_volume_truncatedWindow_bounds (hd : d ≠ 0) {m k : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) :
    (3 : ℝ) ^ (-k) ≤ ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) ∧
      ((volume (truncatedWindow x m k)).toReal) ^ (-(d : ℝ)⁻¹) ≤ 9 * (3 : ℝ) ^ (-k) := by
  obtain ⟨hlo, hhi⟩ := volume_toReal_truncatedWindow_bounds x hx hkm
  exact rpow_normalizer_bounds (d := d) hd hlo hhi

theorem integrableOn_sub_affineEval_sq_truncatedWindow {m k : ℤ} (x : Vec d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict (truncatedWindow x m k)))
    (c : ℝ) (g : Vec d) :
    IntegrableOn (fun p => (u p - affineEval c g p) ^ 2) (truncatedWindow x m k) := by
  refine integrableOn_sub_affineEval_sq_of_axisCubeSandwich
    (zout := x + fun _ => -(1 / 2) * (3 : ℝ) ^ k) (Lout := (3 : ℝ) ^ k)
    (zpow_pos (by norm_num) k) (measurableSet_truncatedWindow x m k) ?_ hu c g
  refine subset_trans (truncatedWindow_subset_translate x m k) ?_
  rw [openCubeSet_originCube_eq_axisCube, image_add_axisCube]

/-! ## 3. The volume ratio of two nested windows of the family -/

/-- The explicit ratio constant of the family: `|U_l| / |U_k| ≤ 3^{(l-k+2)d}` for
`k ≤ l`, raised to the excess exponent `1/d + 1/2`. -/
def windowRatioConst (d : ℕ) (j : ℤ) : ℝ := (((3 : ℝ) ^ (j + 2)) ^ d) ^ ((d : ℝ)⁻¹ + 1 / 2)

theorem windowRatioConst_nonneg (d : ℕ) (j : ℤ) : 0 ≤ windowRatioConst d j := by
  rw [windowRatioConst]
  exact Real.rpow_nonneg (by positivity) _

theorem volume_ratio_truncatedWindow_le {m k l : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) (hlm : l - 1 ≤ m) :
    (volume (truncatedWindow x m l)).toReal / (volume (truncatedWindow x m k)).toReal
      ≤ ((3 : ℝ) ^ (l - k + 2)) ^ d := by
  obtain ⟨_, hhi⟩ := volume_toReal_truncatedWindow_bounds x hx hlm
  obtain ⟨hlo, _⟩ := volume_toReal_truncatedWindow_bounds x hx hkm
  have hkpos : (0 : ℝ) < ((3 : ℝ) ^ (k - 2)) ^ d := by positivity
  have hquot : ((3 : ℝ) ^ l) ^ d / ((3 : ℝ) ^ (k - 2)) ^ d = ((3 : ℝ) ^ (l - k + 2)) ^ d := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), show l - (k - 2) = l - k + 2 by ring]
  have hbpos : (0 : ℝ) < (volume (truncatedWindow x m k)).toReal := lt_of_lt_of_le hkpos hlo
  rw [← hquot, div_le_div_iff₀ hbpos hkpos]
  calc (volume (truncatedWindow x m l)).toReal * ((3 : ℝ) ^ (k - 2)) ^ d
      ≤ ((3 : ℝ) ^ l) ^ d * ((3 : ℝ) ^ (k - 2)) ^ d :=
        mul_le_mul_of_nonneg_right hhi hkpos.le
    _ ≤ ((3 : ℝ) ^ l) ^ d * (volume (truncatedWindow x m k)).toReal :=
        mul_le_mul_of_nonneg_left hlo (by positivity)

/-- **Excess quasi-monotonicity on the one-step family**, at the explicit ratio
constant.  This is the `E(u,U_2) ≲ E(u,U_0)` move of the triangle assembly. -/
theorem affineExcess_truncatedWindow_le {m k l : ℤ} (x : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k - 1 ≤ m) (hlm : l - 1 ≤ m)
    (hkl : k ≤ l) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m l))) :
    affineExcess (truncatedWindow x m k) u
      ≤ windowRatioConst d (l - k) * affineExcess (truncatedWindow x m l) u := by
  have hsub : truncatedWindow x m k ⊆ truncatedWindow x m l := truncatedWindow_mono x m hkl
  have hW : 0 < (volume (truncatedWindow x m l)).toReal :=
    volume_toReal_truncatedWindow_pos x hx hlm
  have hW' : 0 < (volume (truncatedWindow x m k)).toReal :=
    volume_toReal_truncatedWindow_pos x hx hkm
  have hmain := affineExcess_le_of_subset (d := d) (u := u) hsub hW hW'
    (integrableOn_sub_affineEval_sq_truncatedWindow x hu)
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (affineExcess_nonneg _ _))
  refine Real.rpow_le_rpow (by positivity) (volume_ratio_truncatedWindow_le x hx hkm hlm) ?_
  positivity

/-! ## 4. The window choice at the clamped centre -/

/-- **The window choice at the clamped centre.**

With `y := wellPlacedCentre x m (n-2)` the *full* cube `y + □_{n-2}` lies
inside `(z + □_{n-1}) ∩ □_m` — one triadic scale sharper than the printed
requirement `⊆ (z + □_n) ∩ □_m`, and exactly the inclusion the
harmonic-approximation anchor demands at its index `n-2`. -/
theorem image_add_wellPlacedCentre_subset_windowChoice {m n : ℤ} {x z : Vec d}
    (hx : x ∈ truncatedWindow z m (n - 3)) (hnm : n - 2 ≤ m) :
    (fun y => wellPlacedCentre x m (n - 2) + y) '' openCubeSet (originCube d (n - 2)) ⊆
      truncatedWindow z m (n - 1) := by
  have hxm : x ∈ openCubeSet (originCube d m) := truncatedWindow_subset_domain z m (n - 3) hx
  have hxz : x - z ∈ openCubeSet (originCube d (n - 3)) :=
    sub_mem_openCubeSet_of_mem_truncatedWindow hx
  have hxy : x - wellPlacedCentre x m (n - 2) ∈ openCubeSet (originCube d (n - 2)) := by
    have hmem := truncatedWindow_subset_image_add_wellPlacedCentre (k := n - 2) (j := n - 2)
      x hnm le_rfl (mem_truncatedWindow_self (n - 2) hxm)
    rwa [mem_image_add_iff] at hmem
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (n - 3) := zpow_pos (by norm_num) _
  have h2 : (3 : ℝ) ^ (n - 2) = (3 : ℝ) ^ (n - 3) * 3 := by
    rw [show n - 2 = n - 3 + 1 by ring, zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have h1 : (3 : ℝ) ^ (n - 1) = (3 : ℝ) ^ (n - 3) * 9 := by
    rw [show n - 1 = n - 3 + 2 by ring, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rintro p ⟨w, hw, rfl⟩
  refine ⟨?_, image_add_wellPlacedCentre_subset_openCubeSet x hnm ⟨w, hw, rfl⟩⟩
  rw [mem_image_add_iff, HCPolySupport.mem_openCubeSet_originCube_iff]
  rw [HCPolySupport.mem_openCubeSet_originCube_iff] at hw hxy hxz
  intro i
  have hwi := hw i
  have hyi := hxy i
  have hzi := hxz i
  simp only [Pi.sub_apply, Pi.add_apply] at hwi hyi hzi ⊢
  constructor
  · linarith only [hwi.1, hyi.2, hzi.1, h1, h2, h3]
  · linarith only [hwi.2, hyi.1, hzi.2, h1, h2, h3]

/-- The second requirement of the printed window choice, at the same witness:
the truncated window sits inside the full clamped cube. -/
theorem truncatedWindow_subset_image_add_windowChoice {m n : ℤ} (x : Vec d)
    (hnm : n - 2 ≤ m) :
    truncatedWindow x m (n - 2) ⊆
      (fun y => wellPlacedCentre x m (n - 2) + y) '' openCubeSet (originCube d (n - 2)) :=
  truncatedWindow_subset_image_add_wellPlacedCentre (k := n - 2) (j := n - 2) x hnm le_rfl

end

end Algsuperdiff.Section4.Provider.ExcessDecay
