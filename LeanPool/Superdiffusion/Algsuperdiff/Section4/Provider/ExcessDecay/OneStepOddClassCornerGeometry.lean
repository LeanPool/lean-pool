/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundFinal

/-!
# OneStepOddClassCornerGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Corner geometry: window-hugging slabs at a met face, any met configuration

's residue (2) needs the near-face slab apparatus of `OneStepEvenBoundSlab`
**without** the one-met-face hypothesis `hother`: at an edge or corner window
two or more faces are met, and the proved slabs (transversally concentric with
the *centre* `x` at half the triadic side) can poke through a second met face.

The device is per-coordinate **window hugging**: every box built here uses, in
each coordinate that is not the active face, the middle half `(hugLo, hugHi) =
(windowLo + e/4, windowHi − e/4)` of the window's own edge `e = windowHi −
windowLo`.  Since every window edge exceeds half the triadic side
(`half_zpow_lt_window_edge`, proved here for **all** met configurations), the
hugged edge exceeds a quarter of the triadic side, and all containments hold
with no assumption on the met set beyond the active face itself.

Boxes (active met upper face `i`, and for the corner a second met upper face
`j ≠ i`; depth `delta` with `16·delta ≤ 3^k`):

* `cornerFaceSlab i delta` — the near-face slab `(a−delta, a)` at `i`, hugged
  transversally; and its inward `delta`-translate.
* `cornerFaceTaylor i delta` — the Taylor box `(a−2delta, a+delta)` at `i`,
  hugged transversally.
* `cornerPairSlab i j delta` — the corner slab, deep at **both** `i` and `j`.
* `cornerPairTaylor i j delta` — `(a−delta, a)` at `i`, `(a−2delta, a+delta)`
  at `j`, hugged transversally: the Taylor box of the face-`j` step run *on*
  the corner slab.

Containments proved: each slab in the window and in its Taylor box; the
reflected and pushed points in the Taylor box; sup-balls of radius `3^k/16`
around Taylor points inside the doubled window `reflectedWindow` (hence the
Taylor boxes are inside it); the crude volume lower bound `delta^d` for the
slabs.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open HCPolySupport (Vec openCubeSet originCube coordFaceReflection basisVec
  mem_openCubeSet_originCube_iff)
open Algsuperdiff.Section4.Provider.ExcessDecay
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. Window edges at an arbitrary met configuration -/

/-- Every window edge is positive, at any met configuration. -/
theorem windowLo_lt_windowHi_of_mem {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    windowLo x m k l < windowHi x m k l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hxl := (mem_openCubeSet_originCube_iff.mp hx) l
  by_cases hup : MeetsUpperFace x m k l
  · rw [windowHi_of_meetsUpperFace hup,
      windowLo_of_not_meetsLowerFace (not_meetsLowerFace_of_meetsUpperFace hkm hup)]
    linarith only [hxl.2, hw]
  · by_cases hlow : MeetsLowerFace x m k l
    · rw [windowHi_of_not_meetsUpperFace hup, windowLo_of_meetsLowerFace hlow]
      linarith only [hxl.1, hw]
    · rw [windowHi_of_not_meetsUpperFace hup, windowLo_of_not_meetsLowerFace hlow]
      linarith only [hw]

/-- **Every window edge exceeds half the triadic side**, at any met
configuration: an unmet edge is the full side, and a met edge keeps more than
half of it because the centre is inside `□_m`. -/
theorem half_zpow_lt_window_edge {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    (1 / 2 : ℝ) * (3 : ℝ) ^ k < windowHi x m k l - windowLo x m k l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hxl := (mem_openCubeSet_originCube_iff.mp hx) l
  by_cases hup : MeetsUpperFace x m k l
  · rw [windowHi_of_meetsUpperFace hup,
      windowLo_of_not_meetsLowerFace (not_meetsLowerFace_of_meetsUpperFace hkm hup)]
    linarith only [hxl.2]
  · by_cases hlow : MeetsLowerFace x m k l
    · rw [windowHi_of_not_meetsUpperFace hup, windowLo_of_meetsLowerFace hlow]
      linarith only [hxl.1]
    · rw [windowHi_of_not_meetsUpperFace hup, windowLo_of_not_meetsLowerFace hlow]
      linarith only [hw]

/-- The partial reflection never raises a lower endpoint (nondegenerate
windows). -/
theorem reflectedLo_le_windowLo {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    reflectedLo x m k l ≤ windowLo x m k l := by
  by_cases hlow : MeetsLowerFace x m k l
  · rw [reflectedLo_of_meetsLowerFace hlow, windowLo_of_meetsLowerFace hlow]
    have h := windowLo_lt_windowHi_of_mem hx hkm l
    rw [windowLo_of_meetsLowerFace hlow] at h
    linarith only [h]
  · rw [reflectedLo_of_not_meetsLowerFace hlow]

/-- The partial reflection never lowers an upper endpoint (nondegenerate
windows). -/
theorem windowHi_le_reflectedHi {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    windowHi x m k l ≤ reflectedHi x m k l := by
  by_cases hup : MeetsUpperFace x m k l
  · rw [reflectedHi_of_meetsUpperFace hup, windowHi_of_meetsUpperFace hup]
    have h := windowLo_lt_windowHi_of_mem hx hkm l
    rw [windowHi_of_meetsUpperFace hup] at h
    linarith only [h]
  · rw [reflectedHi_of_not_meetsUpperFace hup]

/-- On a met upper face the reflected upper endpoint is the face plus the full
edge. -/
theorem reflectedHi_eq_add_edge_of_meetsUpperFace {x : Vec d} {m k : ℤ} {i : Fin d}
    (hup : MeetsUpperFace x m k i) :
    reflectedHi x m k i
      = (1 / 2 : ℝ) * (3 : ℝ) ^ m
        + (windowHi x m k i - windowLo x m k i) := by
  rw [reflectedHi_of_meetsUpperFace hup, windowHi_of_meetsUpperFace hup]
  have h3m : (3 : ℝ) ^ m = (1 / 2 : ℝ) * (3 : ℝ) ^ m + (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    ring
  linarith only [h3m]

/-! ## 2. The hugged transversal edges -/

/-- The lower endpoint of the middle half of the window's `l`-edge. -/
def hugLo (x : Vec d) (m k : ℤ) (l : Fin d) : ℝ :=
  windowLo x m k l + (windowHi x m k l - windowLo x m k l) / 4

/-- The upper endpoint of the middle half of the window's `l`-edge. -/
def hugHi (x : Vec d) (m k : ℤ) (l : Fin d) : ℝ :=
  windowHi x m k l - (windowHi x m k l - windowLo x m k l) / 4

theorem hugLo_lt_hugHi {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    hugLo x m k l < hugHi x m k l := by
  have h := windowLo_lt_windowHi_of_mem hx hkm l
  rw [hugLo, hugHi]
  linarith only [h]

theorem windowLo_lt_hugLo {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    windowLo x m k l < hugLo x m k l := by
  have h := windowLo_lt_windowHi_of_mem hx hkm l
  rw [hugLo]
  linarith only [h]

theorem hugHi_lt_windowHi {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    hugHi x m k l < windowHi x m k l := by
  have h := windowLo_lt_windowHi_of_mem hx hkm l
  rw [hugHi]
  linarith only [h]

/-- The hugged edge is exactly half the window edge. -/
theorem hugHi_sub_hugLo {x : Vec d} (m k : ℤ) (l : Fin d) :
    hugHi x m k l - hugLo x m k l
      = (windowHi x m k l - windowLo x m k l) / 2 := by
  rw [hugHi, hugLo]
  ring

/-- The hugged edge is concentric with the window edge. -/
theorem hugLo_add_hugHi {x : Vec d} (m k : ℤ) (l : Fin d) :
    hugLo x m k l + hugHi x m k l = windowLo x m k l + windowHi x m k l := by
  rw [hugHi, hugLo]
  ring

/-- The hugged edge exceeds a quarter of the triadic side. -/
theorem quarter_zpow_lt_hug_edge {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    (1 / 4 : ℝ) * (3 : ℝ) ^ k < hugHi x m k l - hugLo x m k l := by
  have h := half_zpow_lt_window_edge hx hkm l
  rw [hugHi_sub_hugLo]
  linarith only [h]

/-- The hug margin exceeds an eighth of the triadic side. -/
theorem eighth_zpow_lt_hug_margin {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    (1 / 8 : ℝ) * (3 : ℝ) ^ k
      < (windowHi x m k l - windowLo x m k l) / 4 := by
  have h := half_zpow_lt_window_edge hx hkm l
  linarith only [h]

/-! ## 3. The four corner boxes -/

/-- The near-face slab at the met upper `i`-face, window-hugged
transversally. -/
def cornerFaceSlabLo (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun l => if l = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta else hugLo x m k l

/-- Upper coordinates of the slab meeting one upper cube face. -/
def cornerFaceSlabHi (x : Vec d) (m k : ℤ) (i : Fin d) : Fin d → ℝ :=
  fun l => if l = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m else hugHi x m k l

/-- The Taylor box at the met upper `i`-face, window-hugged transversally. -/
def cornerFaceTaylorLo (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun l => if l = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - 2 * delta else hugLo x m k l

/-- Upper coordinates of the Taylor box extending across one upper cube face. -/
def cornerFaceTaylorHi (x : Vec d) (m k : ℤ) (i : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun l => if l = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m + delta else hugHi x m k l

/-- The corner slab: deep at both met upper faces `i` and `j`. -/
def cornerPairSlabLo (x : Vec d) (m k : ℤ) (i j : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun l => if l = i ∨ l = j then (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta
    else hugLo x m k l

/-- Upper coordinates of the slab meeting two upper cube faces. -/
def cornerPairSlabHi (x : Vec d) (m k : ℤ) (i j : Fin d) : Fin d → ℝ :=
  fun l => if l = i ∨ l = j then (1 / 2 : ℝ) * (3 : ℝ) ^ m else hugHi x m k l

/-- The Taylor box of the face-`j` step run on the corner slab: still deep at
`i`, extended across the `j`-face. -/
def cornerPairTaylorLo (x : Vec d) (m k : ℤ) (i j : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun l => if l = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta
    else if l = j then (1 / 2 : ℝ) * (3 : ℝ) ^ m - 2 * delta
    else hugLo x m k l

/-- Upper coordinates of the Taylor box for the second face of a corner step. -/
def cornerPairTaylorHi (x : Vec d) (m k : ℤ) (i j : Fin d) (delta : ℝ) : Fin d → ℝ :=
  fun l => if l = i then (1 / 2 : ℝ) * (3 : ℝ) ^ m
    else if l = j then (1 / 2 : ℝ) * (3 : ℝ) ^ m + delta
    else hugHi x m k l

/-! ## 4. Nondegeneracy -/

theorem cornerFaceSlabLo_lt_hi {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (hdelta : 0 < delta)
    (l : Fin d) :
    cornerFaceSlabLo x m k i delta l < cornerFaceSlabHi x m k i l := by
  rw [cornerFaceSlabLo, cornerFaceSlabHi]
  by_cases hli : l = i
  · rw [ite_eq_left hli, ite_eq_left hli]
    linarith only [hdelta]
  · rw [ite_eq_right hli, ite_eq_right hli]
    exact hugLo_lt_hugHi hx hkm l

theorem cornerPairSlabLo_lt_hi {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (hdelta : 0 < delta)
    (l : Fin d) :
    cornerPairSlabLo x m k i j delta l < cornerPairSlabHi x m k i j l := by
  rw [cornerPairSlabLo, cornerPairSlabHi]
  by_cases hlij : l = i ∨ l = j
  · rw [ite_eq_left hlij, ite_eq_left hlij]
    linarith only [hdelta]
  · rw [ite_eq_right hlij, ite_eq_right hlij]
    exact hugLo_lt_hugHi hx hkm l

/-! ## 5. The slabs sit inside the window -/

/-- The hugged interval is inside the window's edge. -/
theorem hug_subset_window {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) (l : Fin d) :
    windowLo x m k l ≤ hugLo x m k l ∧ hugHi x m k l ≤ windowHi x m k l :=
  ⟨(windowLo_lt_hugLo hx hkm l).le, (hugHi_lt_windowHi hx hkm l).le⟩

/-- **The face slab is inside the window.** -/
theorem coordBox_cornerFaceSlab_subset_truncatedWindow {x : Vec d} {m k : ℤ}
    {i : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (cornerFaceSlabLo x m k i delta) (cornerFaceSlabHi x m k i)
      ⊆ truncatedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [truncatedWindow_eq_coordBox]
  refine coordBox_subset_coordBox (fun l => ?_) (fun l => ?_)
  · rw [cornerFaceSlabLo]
    by_cases hli : l = i
    · rw [ite_eq_left hli, hli]
      have hedge := half_zpow_lt_window_edge hx hkm i
      rw [windowHi_of_meetsUpperFace hup] at hedge
      linarith only [hedge, hdelta16, hw]
    · rw [ite_eq_right hli]
      exact (hug_subset_window hx hkm l).1
  · rw [cornerFaceSlabHi]
    by_cases hli : l = i
    · rw [ite_eq_left hli, hli, windowHi_of_meetsUpperFace hup]
    · rw [ite_eq_right hli]
      exact (hug_subset_window hx hkm l).2

/-- **The pushed face slab is inside the window.**  The inward translate by
`delta·eᵢ`. -/
theorem coordBox_cornerFaceSlab_pushed_subset_truncatedWindow {x : Vec d}
    {m k : ℤ} {i : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m))
    (hkm : k < m) (hup : MeetsUpperFace x m k i) (hdelta : 0 < delta)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (fun l => cornerFaceSlabLo x m k i delta l
        - (delta • (basisVec i : Vec d)) l)
      (fun l => cornerFaceSlabHi x m k i l - (delta • (basisVec i : Vec d)) l)
      ⊆ truncatedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [truncatedWindow_eq_coordBox]
  refine coordBox_subset_coordBox (fun l => ?_) (fun l => ?_)
  · rw [cornerFaceSlabLo, smul_basisVec_apply]
    by_cases hli : l = i
    · rw [ite_eq_left hli, ite_eq_left hli, hli]
      have hedge := half_zpow_lt_window_edge hx hkm i
      rw [windowHi_of_meetsUpperFace hup] at hedge
      linarith only [hedge, hdelta16, hw]
    · rw [ite_eq_right hli, ite_eq_right hli, sub_zero]
      exact (hug_subset_window hx hkm l).1
  · rw [cornerFaceSlabHi, smul_basisVec_apply]
    by_cases hli : l = i
    · rw [ite_eq_left hli, ite_eq_left hli, hli, windowHi_of_meetsUpperFace hup]
      linarith only [hdelta]
    · rw [ite_eq_right hli, ite_eq_right hli, sub_zero]
      exact (hug_subset_window hx hkm l).2

/-- **The corner slab is inside the window.** -/
theorem coordBox_cornerPairSlab_subset_truncatedWindow {x : Vec d} {m k : ℤ}
    {i j : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hupi : MeetsUpperFace x m k i) (hupj : MeetsUpperFace x m k j)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (cornerPairSlabLo x m k i j delta) (cornerPairSlabHi x m k i j)
      ⊆ truncatedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [truncatedWindow_eq_coordBox]
  refine coordBox_subset_coordBox (fun l => ?_) (fun l => ?_)
  · rw [cornerPairSlabLo]
    by_cases hlij : l = i ∨ l = j
    · rw [ite_eq_left hlij]
      have hupl : MeetsUpperFace x m k l := by
        rcases hlij with h | h
        · rw [h]; exact hupi
        · rw [h]; exact hupj
      have hedge := half_zpow_lt_window_edge hx hkm l
      rw [windowHi_of_meetsUpperFace hupl] at hedge
      linarith only [hedge, hdelta16, hw]
    · rw [ite_eq_right hlij]
      exact (hug_subset_window hx hkm l).1
  · rw [cornerPairSlabHi]
    by_cases hlij : l = i ∨ l = j
    · rw [ite_eq_left hlij]
      have hupl : MeetsUpperFace x m k l := by
        rcases hlij with h | h
        · rw [h]; exact hupi
        · rw [h]; exact hupj
      rw [windowHi_of_meetsUpperFace hupl]
    · rw [ite_eq_right hlij]
      exact (hug_subset_window hx hkm l).2

/-- **The pushed corner slab is inside the window.**  The inward translate by
`delta·eⱼ`. -/
theorem coordBox_cornerPairSlab_pushed_subset_truncatedWindow {x : Vec d}
    {m k : ℤ} {i j : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m))
    (hkm : k < m) (hupi : MeetsUpperFace x m k i) (hupj : MeetsUpperFace x m k j)
    (hdelta : 0 < delta) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (fun l => cornerPairSlabLo x m k i j delta l
        - (delta • (basisVec j : Vec d)) l)
      (fun l => cornerPairSlabHi x m k i j l - (delta • (basisVec j : Vec d)) l)
      ⊆ truncatedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [truncatedWindow_eq_coordBox]
  refine coordBox_subset_coordBox (fun l => ?_) (fun l => ?_)
  · rw [cornerPairSlabLo, smul_basisVec_apply]
    by_cases hlij : l = i ∨ l = j
    · rw [ite_eq_left hlij]
      have hupl : MeetsUpperFace x m k l := by
        rcases hlij with h | h
        · rw [h]; exact hupi
        · rw [h]; exact hupj
      have hedge := half_zpow_lt_window_edge hx hkm l
      rw [windowHi_of_meetsUpperFace hupl] at hedge
      by_cases hlj : l = j
      · rw [ite_eq_left hlj]
        linarith only [hedge, hdelta16, hw]
      · rw [ite_eq_right hlj, sub_zero]
        linarith only [hedge, hdelta16, hw]
    · have hlj : ¬ l = j := fun h => hlij (Or.inr h)
      rw [ite_eq_right hlij, ite_eq_right hlj, sub_zero]
      exact (hug_subset_window hx hkm l).1
  · rw [cornerPairSlabHi, smul_basisVec_apply]
    by_cases hlij : l = i ∨ l = j
    · rw [ite_eq_left hlij]
      have hupl : MeetsUpperFace x m k l := by
        rcases hlij with h | h
        · rw [h]; exact hupi
        · rw [h]; exact hupj
      rw [windowHi_of_meetsUpperFace hupl]
      by_cases hlj : l = j
      · rw [ite_eq_left hlj]
        linarith only [hdelta]
      · rw [ite_eq_right hlj, sub_zero]
    · have hlj : ¬ l = j := fun h => hlij (Or.inr h)
      rw [ite_eq_right hlij, ite_eq_right hlj, sub_zero]
      exact (hug_subset_window hx hkm l).2

/-! ## 6. Memberships in the Taylor boxes -/

/-- The face slab is inside its Taylor box. -/
theorem coordBox_cornerFaceSlab_subset_taylor {x : Vec d} {m k : ℤ} {i : Fin d}
    {delta : ℝ} (hdelta : 0 < delta) :
    coordBox (cornerFaceSlabLo x m k i delta) (cornerFaceSlabHi x m k i)
      ⊆ coordBox (cornerFaceTaylorLo x m k i delta)
          (cornerFaceTaylorHi x m k i delta) := by
  refine coordBox_subset_coordBox (fun l => ?_) (fun l => ?_)
  · rw [cornerFaceTaylorLo, cornerFaceSlabLo]
    by_cases hli : l = i
    · rw [ite_eq_left hli, ite_eq_left hli]
      linarith only [hdelta]
    · rw [ite_eq_right hli, ite_eq_right hli]
  · rw [cornerFaceTaylorHi, cornerFaceSlabHi]
    by_cases hli : l = i
    · rw [ite_eq_left hli, ite_eq_left hli]
      linarith only [hdelta]
    · rw [ite_eq_right hli, ite_eq_right hli]

/-- The reflected face slab is inside the Taylor box. -/
theorem reflection_cornerFaceSlab_mem_taylor {x : Vec d} {m k : ℤ} {i : Fin d}
    {delta : ℝ} (hdelta : 0 < delta) {y : Vec d}
    (hy : y ∈ coordBox (cornerFaceSlabLo x m k i delta) (cornerFaceSlabHi x m k i)) :
    coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y
      ∈ coordBox (cornerFaceTaylorLo x m k i delta)
          (cornerFaceTaylorHi x m k i delta) := by
  rw [mem_coordBox_iff] at hy
  rw [mem_coordBox_iff]
  intro l
  have hyl := hy l
  rw [cornerFaceTaylorLo, cornerFaceTaylorHi]
  by_cases hli : l = i
  · rw [hli] at hyl ⊢
    rw [cornerFaceSlabLo, ite_eq_left rfl] at hyl
    rw [cornerFaceSlabHi, ite_eq_left rfl] at hyl
    rw [ite_eq_left rfl, ite_eq_left rfl, HCPolySupport.coordFaceReflection_apply_self]
    exact ⟨by linarith only [hyl.2, hdelta], by linarith only [hyl.1]⟩
  · rw [cornerFaceSlabLo, ite_eq_right hli] at hyl
    rw [cornerFaceSlabHi, ite_eq_right hli] at hyl
    rw [ite_eq_right hli, ite_eq_right hli,
      HCPolySupport.coordFaceReflection_apply_ne _ i l y hli]
    exact hyl

/-- The pushed face slab is inside the Taylor box. -/
theorem pushed_cornerFaceSlab_mem_taylor {x : Vec d} {m k : ℤ} {i : Fin d}
    {delta : ℝ} (hdelta : 0 < delta) {y : Vec d}
    (hy : y ∈ coordBox (cornerFaceSlabLo x m k i delta) (cornerFaceSlabHi x m k i)) :
    y - delta • (basisVec i : Vec d)
      ∈ coordBox (cornerFaceTaylorLo x m k i delta)
          (cornerFaceTaylorHi x m k i delta) := by
  rw [mem_coordBox_iff] at hy
  rw [mem_coordBox_iff]
  intro l
  have hyl := hy l
  have happ : (y - delta • (basisVec i : Vec d)) l
      = y l - (delta • (basisVec i : Vec d)) l := rfl
  rw [cornerFaceTaylorLo, cornerFaceTaylorHi, happ, smul_basisVec_apply]
  by_cases hli : l = i
  · rw [hli] at hyl ⊢
    rw [cornerFaceSlabLo, ite_eq_left rfl] at hyl
    rw [cornerFaceSlabHi, ite_eq_left rfl] at hyl
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨by linarith only [hyl.1], by linarith only [hyl.2, hdelta]⟩
  · rw [cornerFaceSlabLo, ite_eq_right hli] at hyl
    rw [cornerFaceSlabHi, ite_eq_right hli] at hyl
    rw [ite_eq_right hli, ite_eq_right hli, ite_eq_right hli, sub_zero]
    exact hyl

/-- The corner slab is inside the pair Taylor box. -/
theorem coordBox_cornerPairSlab_subset_taylor {x : Vec d} {m k : ℤ} {i j : Fin d}
    {delta : ℝ} (hdelta : 0 < delta) :
    coordBox (cornerPairSlabLo x m k i j delta) (cornerPairSlabHi x m k i j)
      ⊆ coordBox (cornerPairTaylorLo x m k i j delta)
          (cornerPairTaylorHi x m k i j delta) := by
  refine coordBox_subset_coordBox (fun l => ?_) (fun l => ?_)
  · rw [cornerPairTaylorLo, cornerPairSlabLo]
    by_cases hli : l = i
    · rw [ite_eq_left hli, ite_eq_left (Or.inl hli)]
    · by_cases hlj : l = j
      · rw [ite_eq_right hli, ite_eq_left hlj, ite_eq_left (Or.inr hlj)]
        linarith only [hdelta]
      · rw [ite_eq_right hli, ite_eq_right hlj, ite_eq_right (fun h => h.elim hli hlj)]
  · rw [cornerPairTaylorHi, cornerPairSlabHi]
    by_cases hli : l = i
    · rw [ite_eq_left hli, ite_eq_left (Or.inl hli)]
    · by_cases hlj : l = j
      · rw [ite_eq_right hli, ite_eq_left hlj, ite_eq_left (Or.inr hlj)]
        linarith only [hdelta]
      · rw [ite_eq_right hli, ite_eq_right hlj, ite_eq_right (fun h => h.elim hli hlj)]

/-- The `j`-reflected corner slab is inside the pair Taylor box. -/
theorem reflection_cornerPairSlab_mem_taylor {x : Vec d} {m k : ℤ} {i j : Fin d}
    {delta : ℝ} (hij : i ≠ j) (hdelta : 0 < delta) {y : Vec d}
    (hy : y ∈ coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j)) :
    coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j y
      ∈ coordBox (cornerPairTaylorLo x m k i j delta)
          (cornerPairTaylorHi x m k i j delta) := by
  rw [mem_coordBox_iff] at hy
  rw [mem_coordBox_iff]
  intro l
  have hyl := hy l
  rw [cornerPairTaylorLo, cornerPairTaylorHi]
  by_cases hlj : l = j
  · have hli : ¬ l = i := fun h => hij (h.symm.trans hlj)
    rw [hlj] at hyl ⊢
    rw [cornerPairSlabLo, ite_eq_left (Or.inr rfl)] at hyl
    rw [cornerPairSlabHi, ite_eq_left (Or.inr rfl)] at hyl
    have hji : ¬ j = i := fun h => hij h.symm
    rw [ite_eq_right hji, ite_eq_left rfl, ite_eq_right hji, ite_eq_left rfl,
      HCPolySupport.coordFaceReflection_apply_self]
    exact ⟨by linarith only [hyl.2, hdelta], by linarith only [hyl.1]⟩
  · rw [HCPolySupport.coordFaceReflection_apply_ne _ j l y hlj]
    by_cases hli : l = i
    · rw [hli] at hyl ⊢
      rw [cornerPairSlabLo, ite_eq_left (Or.inl rfl)] at hyl
      rw [cornerPairSlabHi, ite_eq_left (Or.inl rfl)] at hyl
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact hyl
    · rw [cornerPairSlabLo, ite_eq_right (fun h => h.elim hli hlj)] at hyl
      rw [cornerPairSlabHi, ite_eq_right (fun h => h.elim hli hlj)] at hyl
      rw [ite_eq_right hli, ite_eq_right hlj, ite_eq_right hli, ite_eq_right hlj]
      exact hyl

/-- The `j`-pushed corner slab is inside the pair Taylor box. -/
theorem pushed_cornerPairSlab_mem_taylor {x : Vec d} {m k : ℤ} {i j : Fin d}
    {delta : ℝ} (hij : i ≠ j) (hdelta : 0 < delta) {y : Vec d}
    (hy : y ∈ coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j)) :
    y - delta • (basisVec j : Vec d)
      ∈ coordBox (cornerPairTaylorLo x m k i j delta)
          (cornerPairTaylorHi x m k i j delta) := by
  rw [mem_coordBox_iff] at hy
  rw [mem_coordBox_iff]
  intro l
  have hyl := hy l
  have happ : (y - delta • (basisVec j : Vec d)) l
      = y l - (delta • (basisVec j : Vec d)) l := rfl
  rw [cornerPairTaylorLo, cornerPairTaylorHi, happ, smul_basisVec_apply]
  by_cases hlj : l = j
  · have hji : ¬ l = i := fun h => hij (h.symm.trans hlj)
    rw [hlj] at hyl ⊢
    rw [cornerPairSlabLo, ite_eq_left (Or.inr rfl)] at hyl
    rw [cornerPairSlabHi, ite_eq_left (Or.inr rfl)] at hyl
    have hji' : ¬ j = i := fun h => hij h.symm
    rw [ite_eq_right hji', ite_eq_left rfl, ite_eq_right hji', ite_eq_left rfl, ite_eq_left rfl]
    exact ⟨by linarith only [hyl.1], by linarith only [hyl.2, hdelta]⟩
  · by_cases hli : l = i
    · rw [hli] at hyl ⊢
      rw [cornerPairSlabLo, ite_eq_left (Or.inl rfl)] at hyl
      rw [cornerPairSlabHi, ite_eq_left (Or.inl rfl)] at hyl
      have hij' : ¬ i = j := hij
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hij', sub_zero]
      exact hyl
    · rw [cornerPairSlabLo, ite_eq_right (fun h => h.elim hli hlj)] at hyl
      rw [cornerPairSlabHi, ite_eq_right (fun h => h.elim hli hlj)] at hyl
      rw [ite_eq_right hli, ite_eq_right hlj, ite_eq_right hli, ite_eq_right hlj, ite_eq_right
        hlj, sub_zero]
      exact hyl

/-! ## 7. Sup-balls around the Taylor boxes inside the doubled window -/

/-- The per-coordinate reach of a Taylor point, bounded inside the reflected
edge.  The active face `i` is met; every other coordinate is hugged. -/
private theorem taylor_reach_bounds {x : Vec d} {m k : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m) {l : Fin d}
    {t : ℝ} (hlo : hugLo x m k l - (3 : ℝ) ^ k / 16 < t)
    (hhi : t < hugHi x m k l + (3 : ℝ) ^ k / 16) :
    reflectedLo x m k l < t ∧ t < reflectedHi x m k l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hmargin := eighth_zpow_lt_hug_margin hx hkm l
  have hRlo := reflectedLo_le_windowLo hx hkm l
  have hRhi := windowHi_le_reflectedHi hx hkm l
  have h1 : windowLo x m k l < t := by
    rw [hugLo] at hlo
    linarith only [hlo, hmargin, hw]
  have h2 : t < windowHi x m k l := by
    rw [hugHi] at hhi
    linarith only [hhi, hmargin, hw]
  exact ⟨lt_of_le_of_lt hRlo h1, lt_of_lt_of_le h2 hRhi⟩

/-- **Sup-balls of radius `3^k/16` around the face Taylor box are inside the
doubled window.** -/
theorem metricBall_subset_reflectedWindow_of_mem_cornerFaceTaylor {x : Vec d}
    {m k : ℤ} {i : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m))
    (hkm : k < m) (hup : MeetsUpperFace x m k i)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) {p : Vec d}
    (hp : p ∈ coordBox (cornerFaceTaylorLo x m k i delta)
      (cornerFaceTaylorHi x m k i delta)) :
    Metric.ball p ((3 : ℝ) ^ k / 16) ⊆ reflectedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ k / 16 := by linarith only [hw]
  rw [mem_coordBox_iff] at hp
  intro q hq
  rw [Metric.mem_ball, dist_pi_lt_iff hR] at hq
  rw [mem_reflectedWindow_iff]
  intro l
  have hql : |q l - p l| < (3 : ℝ) ^ k / 16 := by
    have hqd := hq l
    rwa [Real.dist_eq] at hqd
  have hql' := abs_lt.1 hql
  have hpl := hp l
  rw [cornerFaceTaylorLo, cornerFaceTaylorHi] at hpl
  by_cases hli : l = i
  · rw [ite_eq_left hli] at hpl
    obtain ⟨hplo, hphi⟩ := hpl
    rw [ite_eq_left hli] at hphi
    have hedge := half_zpow_lt_window_edge hx hkm l
    rw [hli] at hql' hedge hplo hphi ⊢
    rw [windowHi_of_meetsUpperFace hup] at hedge
    have hRhi := reflectedHi_eq_add_edge_of_meetsUpperFace (i := i) hup
    rw [windowHi_of_meetsUpperFace hup] at hRhi
    constructor
    · rw [reflectedLo_of_not_meetsLowerFace
        (not_meetsLowerFace_of_meetsUpperFace hkm hup)]
      linarith only [hql'.1, hplo, hedge, hdelta16, hw]
    · rw [hRhi]
      linarith only [hql'.2, hphi, hedge, hdelta16, hw]
  · rw [ite_eq_right hli] at hpl
    obtain ⟨hplo, hphi⟩ := hpl
    rw [ite_eq_right hli] at hphi
    have h := taylor_reach_bounds hx hkm (l := l)
      (t := q l) (by linarith only [hql'.1, hplo])
      (by linarith only [hql'.2, hphi])
    exact h

/-- **Sup-balls of radius `3^k/16` around the pair Taylor box are inside the
doubled window.** -/
theorem metricBall_subset_reflectedWindow_of_mem_cornerPairTaylor {x : Vec d}
    {m k : ℤ} {i j : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m))
    (hkm : k < m) (hupi : MeetsUpperFace x m k i)
    (hupj : MeetsUpperFace x m k j)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) {p : Vec d}
    (hp : p ∈ coordBox (cornerPairTaylorLo x m k i j delta)
      (cornerPairTaylorHi x m k i j delta)) :
    Metric.ball p ((3 : ℝ) ^ k / 16) ⊆ reflectedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ k / 16 := by linarith only [hw]
  rw [mem_coordBox_iff] at hp
  intro q hq
  rw [Metric.mem_ball, dist_pi_lt_iff hR] at hq
  rw [mem_reflectedWindow_iff]
  intro l
  have hql : |q l - p l| < (3 : ℝ) ^ k / 16 := by
    have hqd := hq l
    rwa [Real.dist_eq] at hqd
  have hql' := abs_lt.1 hql
  have hpl := hp l
  rw [cornerPairTaylorLo, cornerPairTaylorHi] at hpl
  by_cases hli : l = i
  · rw [ite_eq_left hli] at hpl
    obtain ⟨hplo, hphi⟩ := hpl
    rw [ite_eq_left hli] at hphi
    have hedge := half_zpow_lt_window_edge hx hkm l
    rw [hli] at hql' hedge hplo hphi ⊢
    rw [windowHi_of_meetsUpperFace hupi] at hedge
    have hRhi := reflectedHi_eq_add_edge_of_meetsUpperFace (i := i) hupi
    rw [windowHi_of_meetsUpperFace hupi] at hRhi
    constructor
    · rw [reflectedLo_of_not_meetsLowerFace
        (not_meetsLowerFace_of_meetsUpperFace hkm hupi)]
      linarith only [hql'.1, hplo, hedge, hdelta16, hw]
    · rw [hRhi]
      linarith only [hql'.2, hphi, hedge, hdelta16, hw]
  · rw [ite_eq_right hli] at hpl
    obtain ⟨hplo, hphi⟩ := hpl
    rw [ite_eq_right hli] at hphi
    by_cases hlj : l = j
    · rw [ite_eq_left hlj] at hplo hphi
      have hedge := half_zpow_lt_window_edge hx hkm l
      rw [hlj] at hql' hedge hplo hphi ⊢
      rw [windowHi_of_meetsUpperFace hupj] at hedge
      have hRhi := reflectedHi_eq_add_edge_of_meetsUpperFace (i := j) hupj
      rw [windowHi_of_meetsUpperFace hupj] at hRhi
      constructor
      · rw [reflectedLo_of_not_meetsLowerFace
          (not_meetsLowerFace_of_meetsUpperFace hkm hupj)]
        linarith only [hql'.1, hplo, hedge, hdelta16, hw]
      · rw [hRhi]
        linarith only [hql'.2, hphi, hedge, hdelta16, hw]
    · rw [ite_eq_right hlj] at hplo hphi
      exact taylor_reach_bounds hx hkm (l := l)
        (t := q l) (by linarith only [hql'.1, hplo])
        (by linarith only [hql'.2, hphi])

/-- The face Taylor box is inside the doubled window. -/
theorem coordBox_cornerFaceTaylor_subset_reflectedWindow {x : Vec d} {m k : ℤ}
    {i : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hup : MeetsUpperFace x m k i) (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (cornerFaceTaylorLo x m k i delta) (cornerFaceTaylorHi x m k i delta)
      ⊆ reflectedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  intro p hp
  exact metricBall_subset_reflectedWindow_of_mem_cornerFaceTaylor hx hkm hup
    hdelta16 hp (Metric.mem_ball_self (by linarith only [hw]))

/-- The pair Taylor box is inside the doubled window. -/
theorem coordBox_cornerPairTaylor_subset_reflectedWindow {x : Vec d} {m k : ℤ}
    {i j : Fin d} {delta : ℝ} (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hupi : MeetsUpperFace x m k i) (hupj : MeetsUpperFace x m k j)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) :
    coordBox (cornerPairTaylorLo x m k i j delta)
        (cornerPairTaylorHi x m k i j delta)
      ⊆ reflectedWindow x m k := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  intro p hp
  exact metricBall_subset_reflectedWindow_of_mem_cornerPairTaylor hx hkm hupi
    hupj hdelta16 hp (Metric.mem_ball_self (by linarith only [hw]))

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
