/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionVolume

/-!
# OneStepEvenBoundSlab

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The near-face geometry of the one-met-face boundary window

The boundary branch of the §4.3 excess decay works on the truncated window
`U₂ = truncatedWindow x m k = coordBox (windowLo x m k) (windowHi x m k)` and on its
doubled partner `R = reflectedWindow x m k`, in the regime where **exactly one** face of
`∂□_m` meets the closure of `U₂`, namely the upper `i`-face `{y i = a}` with
`a = ½·3^m`.

This module proves the *near-face geometry* the even (non-odd) part of the
comparison estimate consumes:

* the **core slab** `S = coordBox (slabLo …) (slabHi …)`, the layer of depth `delta`
  directly under the met face, transversally concentric with the window at half its
  side: `S = (a − delta, a) × ∏_{j ≠ i} (x j − 3^k/4, x j + 3^k/4)`;
* the **deep slab** `D`, the core slab pushed one further depth `delta` away from the
  face: `D = (a − 2delta, a − delta) × ∏_{j ≠ i} (x j − 3^k/4, x j + 3^k/4)`;
* the **Taylor box** `T = (a − 2delta, a + delta) × ∏_{j ≠ i} (x j − 3^k/4, x j + 3^k/4)`,
  the slightly larger box that contains the core slab, its `delta`-translate `D`, **and**
  the reflection of the core slab through the met face;
* the **sup-ball family**: every point of `T` carries a sup-ball of radius `3^k/4`
  inside the doubled window `R`, which is what the interior Hessian estimate consumes on
  the doubled domain.

## The window edges in this regime

Write `a = ½·3^m`, `w = 3^k` and `ℓ = windowHi x m k i − windowLo x m k i`.

```text
  MeetsUpperFace x m k i  ↔  a ≤ x i + w/2      ⟹  windowHi x m k i = a;
  k < m and the upper i-face met  ⟹  the lower i-face is unmet
                                  ⟹  windowLo x m k i = x i − w/2;
  x ∈ □_m  ⟹  x i < a  ⟹  ℓ = a − x i + w/2 > w/2 ,   and   ℓ ≤ w .
```

On the unmet coordinates `j ≠ i` the window keeps its full triadic edge
`(x j − w/2, x j + w/2)` and the reflection does not move it; on the met coordinate the
doubled edge is `(a − ℓ, a + ℓ)`, because `reflectedLo = windowLo` and
`reflectedHi = 3^m − windowLo = a + ℓ`.

With the depth budget `16·delta ≤ w` we get `2·delta ≤ w/8 < w/2 < ℓ`, which is exactly
what makes the three boxes fit: transversally `w/4 < w/2`, and in the `i` direction the
Taylor box `(a − 2delta, a + delta)` is inside `(a − ℓ, a + ℓ)` with a margin of at
least `w/8` on each side — enough room for a whole sup-ball of radius `w/4` around every
point of `T`.

## What is not done here

Nothing analytic.  No function is restricted, no Taylor expansion is performed, no
Hessian bound is proved.  This module is pure geometry: box endpoints, inclusions of
boxes, one reflection identity, one ball family, and one lower bound on the Lebesgue
measure of the core slab.

## References

* ABK26, `l.excess.decay.good.scales`.
* `Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionWindow` (the window and its
  partial reflection), `…OddReflectionVolume` (`volume_coordBox`),
  `…OneStepBoundaryGeometry` (the `dist_pi_lt_iff` idiom for sup-balls).
* CoarseGraining
  `Homogenization.Sobolev.Foundations.CubeReflection.Reflections`
  (`coordFaceReflection`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec openCubeSet originCube coordFaceReflection basisVec
  mem_openCubeSet_originCube_iff coordFaceReflection_apply_self
  coordFaceReflection_apply_ne)

noncomputable section

variable {d : ℕ}

/-! ## 1. The window edges in the one-met-face regime -/

/-- The met upper `i`-face is the top of the `i`-edge, so the *bottom* is untruncated. -/
theorem windowLo_eq_of_meetsUpperFace {x : Vec d} {m k : ℤ} {i : Fin d}
    (hkm : k < m) (hup : MeetsUpperFace x m k i) :
    windowLo x m k i = x i - (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
  windowLo_of_not_meetsLowerFace (not_meetsLowerFace_of_meetsUpperFace hkm hup)

/-- On an unmet coordinate the window keeps its full triadic lower endpoint. -/
theorem windowLo_eq_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d}
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hji : j ≠ i) :
    windowLo x m k j = x j - (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
  windowLo_of_not_meetsLowerFace (hother j hji).2

/-- On an unmet coordinate the window keeps its full triadic upper endpoint. -/
theorem windowHi_eq_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d}
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hji : j ≠ i) :
    windowHi x m k j = x j + (1 / 2 : ℝ) * (3 : ℝ) ^ k :=
  windowHi_of_not_meetsUpperFace (hother j hji).1

/-- In the one-met-face regime **no** lower face is met, so the partial reflection never
moves a lower endpoint. -/
theorem reflectedLo_eq {x : Vec d} {m k : ℤ} {i : Fin d} (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (j : Fin d) :
    reflectedLo x m k j = windowLo x m k j := by
  by_cases hji : j = i
  · rw [hji]
    exact reflectedLo_of_not_meetsLowerFace (not_meetsLowerFace_of_meetsUpperFace hkm hup)
  · exact reflectedLo_of_not_meetsLowerFace (hother j hji).2

/-- On an unmet coordinate the partial reflection does not move the upper endpoint. -/
theorem reflectedHi_eq_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d}
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hji : j ≠ i) :
    reflectedHi x m k j = windowHi x m k j :=
  reflectedHi_of_not_meetsUpperFace (hother j hji).1

/-- On the met coordinate the upper endpoint is the reflection of the lower one. -/
theorem reflectedHi_eq_self {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : MeetsUpperFace x m k i) :
    reflectedHi x m k i = (3 : ℝ) ^ m - windowLo x m k i :=
  reflectedHi_of_meetsUpperFace hup

/-! ## 2. The three near-face boxes -/

/-- The lower corner of the **core slab**: the near-face slab of depth `delta`,
transversally concentric with the window at half its side. -/
def slabLo (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun j => if j = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta else x j - (3 : ℝ) ^ k / 4

/-- The upper corner of the core slab. -/
def slabHi (x : Vec d) (m k : ℤ) (i : Fin d) : Fin d → ℝ :=
  fun j => if j = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m else x j + (3 : ℝ) ^ k / 4

/-- The lower corner of the **deep slab**: the core slab pushed one depth `delta` away
from the face. -/
def deepLo (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun j => if j = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - 2 * delta else x j - (3 : ℝ) ^ k / 4

/-- The upper corner of the deep slab. -/
def deepHi (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun j => if j = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta else x j + (3 : ℝ) ^ k / 4

/-- The lower corner of the **Taylor box**. -/
def taylorLo (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun j => if j = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - 2 * delta else x j - (3 : ℝ) ^ k / 4

/-- The upper corner of the Taylor box. -/
def taylorHi (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun j => if j = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m + delta else x j + (3 : ℝ) ^ k / 4

/-! ### The six corners, coordinate by coordinate -/

theorem slabLo_self {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ} :
    slabLo x m k i delta i = (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta := ite_eq_left rfl

theorem slabLo_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ} (hji : j ≠ i) :
    slabLo x m k i delta j = x j - (3 : ℝ) ^ k / 4 := ite_eq_right hji

theorem slabHi_self {x : Vec d} {m k : ℤ} {i : Fin d} :
    slabHi x m k i i = (1 / 2 : ℝ) * (3 : ℝ) ^ m := ite_eq_left rfl

theorem slabHi_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d} (hji : j ≠ i) :
    slabHi x m k i j = x j + (3 : ℝ) ^ k / 4 := ite_eq_right hji

theorem deepLo_self {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ} :
    deepLo x m k i delta i = (1 / 2 : ℝ) * (3 : ℝ) ^ m - 2 * delta := ite_eq_left rfl

theorem deepLo_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ} (hji : j ≠ i) :
    deepLo x m k i delta j = x j - (3 : ℝ) ^ k / 4 := ite_eq_right hji

theorem deepHi_self {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ} :
    deepHi x m k i delta i = (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta := ite_eq_left rfl

theorem deepHi_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ} (hji : j ≠ i) :
    deepHi x m k i delta j = x j + (3 : ℝ) ^ k / 4 := ite_eq_right hji

theorem taylorLo_self {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ} :
    taylorLo x m k i delta i = (1 / 2 : ℝ) * (3 : ℝ) ^ m - 2 * delta := ite_eq_left rfl

theorem taylorLo_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ} (hji : j ≠ i) :
    taylorLo x m k i delta j = x j - (3 : ℝ) ^ k / 4 := ite_eq_right hji

theorem taylorHi_self {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ} :
    taylorHi x m k i delta i = (1 / 2 : ℝ) * (3 : ℝ) ^ m + delta := ite_eq_left rfl

theorem taylorHi_of_ne {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ} (hji : j ≠ i) :
    taylorHi x m k i delta j = x j + (3 : ℝ) ^ k / 4 := ite_eq_right hji

/-! ## 3. Nondegeneracy -/

theorem slabLo_lt_slabHi {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) (j : Fin d) :
    slabLo x m k i delta j < slabHi x m k i j := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  by_cases hji : j = i
  · rw [hji, slabLo_self, slabHi_self]
    linarith only [hdelta]
  · rw [slabLo_of_ne hji, slabHi_of_ne hji]
    linarith only [hw]

theorem deepLo_lt_deepHi {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) (j : Fin d) :
    deepLo x m k i delta j < deepHi x m k i delta j := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  by_cases hji : j = i
  · rw [hji, deepLo_self, deepHi_self]
    linarith only [hdelta]
  · rw [deepLo_of_ne hji, deepHi_of_ne hji]
    linarith only [hw]

theorem windowLo_lt_windowHi {x : Vec d} {m k : ℤ} {i : Fin d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (j : Fin d) :
    windowLo x m k j < windowHi x m k j := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  by_cases hji : j = i
  · have hxi : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
      (mem_openCubeSet_originCube_iff.mp hx i).2
    rw [hji, windowHi_of_meetsUpperFace hup, windowLo_eq_of_meetsUpperFace hkm hup]
    linarith only [hxi, hw]
  · rw [windowLo_eq_of_ne hother hji, windowHi_eq_of_ne hother hji]
    linarith only [hw]

theorem reflectedLo_lt_reflectedHi {x : Vec d} {m k : ℤ} {i : Fin d}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (j : Fin d) :
    reflectedLo x m k j < reflectedHi x m k j := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [reflectedLo_eq hkm hup hother j]
  by_cases hji : j = i
  · have hxi : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
      (mem_openCubeSet_originCube_iff.mp hx i).2
    rw [hji, reflectedHi_eq_self hup, windowLo_eq_of_meetsUpperFace hkm hup]
    linarith only [hxi, hw]
  · rw [reflectedHi_eq_of_ne hother hji]
    exact windowLo_lt_windowHi hx hkm hup hother j

/-! ## 4. The slabs sit inside the window -/

/-- **The core slab is inside the window.**  The met `i`-edge has length
`ℓ > w/2 ≥ 8·delta`, so the depth-`delta` layer under the face fits; transversally the
half-side `w/4` is inside the full half-side `w/2`. -/
theorem coordBox_slab_subset_truncatedWindow {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (slabLo x m k i delta) (slabHi x m k i) ⊆ truncatedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hxi : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    (mem_openCubeSet_originCube_iff.mp hx i).2
  rw [truncatedWindow_eq_coordBox]
  refine coordBox_subset_coordBox (fun j => ?_) (fun j => ?_)
  · by_cases hji : j = i
    · rw [hji, slabLo_self, windowLo_eq_of_meetsUpperFace hkm hup]
      linarith only [hxi, hdelta16, hw]
    · rw [slabLo_of_ne hji, windowLo_eq_of_ne hother hji]
      linarith only [hw]
  · by_cases hji : j = i
    · exact le_of_eq (by rw [hji, slabHi_self, windowHi_of_meetsUpperFace hup])
    · rw [slabHi_of_ne hji, windowHi_eq_of_ne hother hji]
      linarith only [hw]

/-- **The deep slab is inside the window.** -/
theorem coordBox_deep_subset_truncatedWindow {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hdelta : 0 < delta) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (deepLo x m k i delta) (deepHi x m k i delta) ⊆ truncatedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hxi : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    (mem_openCubeSet_originCube_iff.mp hx i).2
  rw [truncatedWindow_eq_coordBox]
  refine coordBox_subset_coordBox (fun j => ?_) (fun j => ?_)
  · by_cases hji : j = i
    · rw [hji, deepLo_self, windowLo_eq_of_meetsUpperFace hkm hup]
      linarith only [hxi, hdelta16, hw]
    · rw [deepLo_of_ne hji, windowLo_eq_of_ne hother hji]
      linarith only [hw]
  · by_cases hji : j = i
    · rw [hji, deepHi_self, windowHi_of_meetsUpperFace hup]
      linarith only [hdelta]
    · rw [deepHi_of_ne hji, windowHi_eq_of_ne hother hji]
      linarith only [hw]

/-! ## 5. The slabs sit inside the Taylor box -/

theorem coordBox_slab_subset_taylor {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) :
    coordBox (slabLo x m k i delta) (slabHi x m k i)
      ⊆ coordBox (taylorLo x m k i delta) (taylorHi x m k i delta) := by
  refine coordBox_subset_coordBox (fun j => ?_) (fun j => ?_)
  · by_cases hji : j = i
    · rw [hji, taylorLo_self, slabLo_self]
      linarith only [hdelta]
    · exact le_of_eq (by rw [taylorLo_of_ne hji, slabLo_of_ne hji])
  · by_cases hji : j = i
    · rw [hji, taylorHi_self, slabHi_self]
      linarith only [hdelta]
    · exact le_of_eq (by rw [taylorHi_of_ne hji, slabHi_of_ne hji])

theorem coordBox_deep_subset_taylor {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) :
    coordBox (deepLo x m k i delta) (deepHi x m k i delta)
      ⊆ coordBox (taylorLo x m k i delta) (taylorHi x m k i delta) := by
  refine coordBox_subset_coordBox (fun j => ?_) (fun j => ?_)
  · by_cases hji : j = i
    · exact le_of_eq (by rw [hji, taylorLo_self, deepLo_self])
    · exact le_of_eq (by rw [taylorLo_of_ne hji, deepLo_of_ne hji])
  · by_cases hji : j = i
    · rw [hji, taylorHi_self, deepHi_self]
      linarith only [hdelta]
    · exact le_of_eq (by rw [taylorHi_of_ne hji, deepHi_of_ne hji])

/-! ## 6. The reflection of the core slab proves in the Taylor box -/

/-- **The reflected core slab is inside the Taylor box.**  The reflection through the met
face `{y i = a}` sends the `i`-range `(a − delta, a)` to `(a, a + delta)` and fixes every
other coordinate, so the union of the core slab and its mirror image is inside
`(a − 2delta, a + delta) × ∏_{j ≠ i} (x j − w/4, x j + w/4)`. -/
theorem reflection_mem_taylor {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ} {y : Vec d}
    (hy : y ∈ coordBox (slabLo x m k i delta) (slabHi x m k i)) (hdelta : 0 < delta) :
    coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y
      ∈ coordBox (taylorLo x m k i delta) (taylorHi x m k i delta) := by
  rw [mem_coordBox_iff] at hy
  rw [mem_coordBox_iff]
  intro j
  have hyj := hy j
  by_cases hji : j = i
  · rw [hji] at hyj ⊢
    rw [slabLo_self, slabHi_self] at hyj
    rw [taylorLo_self, taylorHi_self, coordFaceReflection_apply_self]
    exact ⟨by linarith only [hyj.2, hdelta], by linarith only [hyj.1]⟩
  · rw [slabLo_of_ne hji, slabHi_of_ne hji] at hyj
    rw [taylorLo_of_ne hji, taylorHi_of_ne hji,
      coordFaceReflection_apply_ne _ i j y hji]
    exact hyj

/-! ## 7. The sup-ball family on the Taylor box -/

/-- **The sup-ball family.**  Every point of the Taylor box carries a sup-ball of radius
`3^k/4` inside the doubled window `reflectedWindow x m k`.

In the `i` direction the doubled edge is `(a − ℓ, a + ℓ)` with `ℓ > w/2`, while a ball
around a point of the Taylor box reaches at most
`a − 2delta − w/4 ≥ a − 3w/8` from below and `a + delta + w/4 ≤ a + 5w/16` from above:
both are strictly inside `(a − w/2, a + w/2)`, hence inside `(a − ℓ, a + ℓ)`.
Transversally the reach is `w/4 + w/4 = w/2`, exactly the (unmet, hence untruncated)
half-edge. -/
theorem metricBall_subset_reflectedWindow_of_mem_taylor {x : Vec d} {m k : ℤ} {i : Fin d}
    {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k)
    {p : Vec d} (hp : p ∈ coordBox (taylorLo x m k i delta) (taylorHi x m k i delta)) :
    Metric.ball p ((3 : ℝ) ^ k / 4) ⊆ reflectedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ k / 4 := by linarith only [hw]
  have hxi : x i < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    (mem_openCubeSet_originCube_iff.mp hx i).2
  rw [mem_coordBox_iff] at hp
  intro q hq
  rw [Metric.mem_ball, dist_pi_lt_iff hR] at hq
  rw [mem_reflectedWindow_iff]
  intro j
  have hqj : |q j - p j| < (3 : ℝ) ^ k / 4 := by
    have hqd := hq j
    rwa [Real.dist_eq] at hqd
  have hqj' := abs_lt.1 hqj
  have hpj := hp j
  rw [reflectedLo_eq hkm hup hother j]
  by_cases hji : j = i
  · rw [hji] at hqj' hpj ⊢
    rw [taylorLo_self, taylorHi_self] at hpj
    rw [reflectedHi_eq_self hup, windowLo_eq_of_meetsUpperFace hkm hup]
    exact ⟨by linarith only [hqj'.1, hpj.1, hdelta16, hxi, hw],
      by linarith only [hqj'.2, hpj.2, hdelta16, hxi, hw]⟩
  · rw [taylorLo_of_ne hji, taylorHi_of_ne hji] at hpj
    rw [reflectedHi_eq_of_ne hother hji, windowLo_eq_of_ne hother hji,
      windowHi_eq_of_ne hother hji]
    exact ⟨by linarith only [hqj'.1, hpj.1], by linarith only [hqj'.2, hpj.2]⟩

/-- **The Taylor box is inside the doubled window.** -/
theorem coordBox_taylor_subset_reflectedWindow {x : Vec d} {m k : ℤ} {i : Fin d}
    {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (taylorLo x m k i delta) (taylorHi x m k i delta)
      ⊆ reflectedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  intro p hp
  exact metricBall_subset_reflectedWindow_of_mem_taylor hx hkm hup hother hdelta16 hp
    (Metric.mem_ball_self (by linarith only [hw]))

/-! ## 8. The core slab's volume from below -/

theorem volume_coordBox_slab_ne_top (lo hi : Fin d → ℝ) :
    volume (coordBox lo hi) ≠ ⊤ := by
  rw [volume_coordBox]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- **The core slab's volume from below.**  Every edge of the core slab is at least
`delta`: the met edge is exactly `delta`, and each transversal edge is `w/2 ≥ 8·delta`. -/
theorem volume_coordBox_slab_ge {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    ENNReal.ofReal (delta ^ d)
      ≤ volume (coordBox (slabLo x m k i delta) (slabHi x m k i)) := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hedge : ∀ j : Fin d, delta ≤ slabHi x m k i j - slabLo x m k i delta j := by
    intro j
    by_cases hji : j = i
    · rw [hji, slabHi_self, slabLo_self]
      linarith only [hdelta]
    · rw [slabHi_of_ne hji, slabLo_of_ne hji]
      linarith only [hdelta16, hw]
  rw [volume_coordBox, ENNReal.ofReal_pow hdelta.le]
  calc (ENNReal.ofReal delta) ^ d = ∏ _j : Fin d, ENNReal.ofReal delta := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ j : Fin d, ENNReal.ofReal (slabHi x m k i j - slabLo x m k i delta j) :=
        Finset.prod_le_prod fun j _ => ENNReal.ofReal_le_ofReal (hedge j)

/-- The `toReal` form of the core slab's volume bound. -/
theorem volume_toReal_coordBox_slab_ge {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    delta ^ d ≤ (volume (coordBox (slabLo x m k i delta) (slabHi x m k i))).toReal := by
  have h := ENNReal.toReal_mono
    (volume_coordBox_slab_ne_top (slabLo x m k i delta) (slabHi x m k i))
    (volume_coordBox_slab_ge (x := x) (m := m) (k := k) (i := i) hdelta hdelta16)
  rwa [ENNReal.toReal_ofReal (by positivity)] at h

end

end Algsuperdiff.Section4.Provider.ExcessDecay
