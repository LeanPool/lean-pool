/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.HarmonicityTransferFace

/-!
# OddReflectionAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The odd reflection on the §4.3 windows: the one-met-face transfer

The abstract single-face transfer of `HarmonicityTransferFace.lean` is stated
for an arbitrary reflection-symmetric open bounded convex domain.

## The two geometric facts

* `faceHalf_reflectedWindow_of_meetsUpperFace` (and its lower-face twin) — the
  half of the reflected window on the *window* side of the met face is the
  truncated window itself.
* `mem_reflectedWindow_coordFaceReflection_iff` — the reflected window is
  invariant under the reflection in the met face.  This one needs *only*
  `k < m` and the met face itself: the reflected edge
  `(windowLo, 3^m - windowLo)` is symmetric about `(1/2)·3^m` because its two
  endpoints sum to `3^m`.

## The transfer

`isWeaklyHarmonicOn_reflectedWindow_of_meetsUpperFace` composes them with the
abstract theorem: a weakly harmonic `v` on the truncated window has weakly
harmonic odd extension on the reflected window.  As in the abstract statement,
the `H¹(reflectedWindow)` *packaging* of the odd extension is an input.

## Scope note (measured, not hidden)

Only the **one-met-face** regime is closed here.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Transporting an `H¹` datum along an equality of domains -/

/-- Transport of an `H¹` function along an equality of its domain. -/
def h1FunctionOfSetEq {U V : Set (Vec d)} (h : U = V) (u : H1Function U) : H1Function V :=
  h ▸ u

@[simp] theorem h1FunctionOfSetEq_grad {U V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (h1FunctionOfSetEq h u).grad = u.grad := by
  subst h
  rfl

theorem isWeaklyHarmonicOn_h1FunctionOfSetEq {U V : Set (Vec d)} (h : U = V)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u) :
    IsWeaklyHarmonicOn V (h1FunctionOfSetEq h u) := by
  subst h
  exact hu

/-! ## 2. The met-face geometry of the reflected window -/

/-- **The window is the half of its reflection.**  If the upper `i`-face of
`∂□_m` is the *only* met face, the half of `reflectedWindow x m k` on the
window side of that face is exactly the truncated window. -/
theorem faceHalf_reflectedWindow_of_meetsUpperFace {x : Vec d} {m k : ℤ} (hkm : k < m)
    {i : Fin d} (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j) :
    faceHalf (reflectedWindow x m k) i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1 =
      truncatedWindow x m k := by
  have hlow : ¬ MeetsLowerFace x m k i := not_meetsLowerFace_of_meetsUpperFace hkm hup
  ext y
  rw [truncatedWindow_eq_coordBox, mem_faceHalf_iff, mem_reflectedWindow_iff,
    mem_coordBox_iff]
  constructor
  · rintro ⟨hy, hlt⟩ j
    by_cases hj : j = i
    · subst hj
      refine ⟨?_, ?_⟩
      · have h1 := (hy j).1
        rwa [reflectedLo_of_not_meetsLowerFace hlow] at h1
      · rw [windowHi_of_meetsUpperFace hup]
        linarith only [hlt]
    · obtain ⟨hnu, hnl⟩ := hother j hj
      have h1 := (hy j).1
      have h2 := (hy j).2
      rw [reflectedLo_of_not_meetsLowerFace hnl] at h1
      rw [reflectedHi_of_not_meetsUpperFace hnu] at h2
      exact ⟨h1, h2⟩
  · intro hy
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        have h1 := (hy j).1
        have h2 := (hy j).2
        rw [windowHi_of_meetsUpperFace hup] at h2
        refine ⟨?_, ?_⟩
        · rwa [reflectedLo_of_not_meetsLowerFace hlow]
        · rw [reflectedHi_of_meetsUpperFace hup]
          linarith only [h1, h2]
      · obtain ⟨hnu, hnl⟩ := hother j hj
        rw [reflectedLo_of_not_meetsLowerFace hnl, reflectedHi_of_not_meetsUpperFace hnu]
        exact hy j
    · have h2 := (hy i).2
      rw [windowHi_of_meetsUpperFace hup] at h2
      show (0 : ℝ) < 1 * ((1 / 2 : ℝ) * (3 : ℝ) ^ m - y i)
      linarith only [h2]

/-- The lower-face twin of `faceHalf_reflectedWindow_of_meetsUpperFace`. -/
theorem faceHalf_reflectedWindow_of_meetsLowerFace {x : Vec d} {m k : ℤ} (hkm : k < m)
    {i : Fin d} (hlow : MeetsLowerFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j) :
    faceHalf (reflectedWindow x m k) i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1) =
      truncatedWindow x m k := by
  have hup : ¬ MeetsUpperFace x m k i := fun h =>
    not_meetsLowerFace_of_meetsUpperFace hkm h hlow
  ext y
  rw [truncatedWindow_eq_coordBox, mem_faceHalf_iff, mem_reflectedWindow_iff,
    mem_coordBox_iff]
  constructor
  · rintro ⟨hy, hlt⟩ j
    by_cases hj : j = i
    · subst hj
      refine ⟨?_, ?_⟩
      · rw [windowLo_of_meetsLowerFace hlow]
        linarith only [hlt]
      · have h2 := (hy j).2
        rwa [reflectedHi_of_not_meetsUpperFace hup] at h2
    · obtain ⟨hnu, hnl⟩ := hother j hj
      have h1 := (hy j).1
      have h2 := (hy j).2
      rw [reflectedLo_of_not_meetsLowerFace hnl] at h1
      rw [reflectedHi_of_not_meetsUpperFace hnu] at h2
      exact ⟨h1, h2⟩
  · intro hy
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        have h1 := (hy j).1
        have h2 := (hy j).2
        rw [windowLo_of_meetsLowerFace hlow] at h1
        refine ⟨?_, ?_⟩
        · rw [reflectedLo_of_meetsLowerFace hlow]
          linarith only [h1, h2]
        · rwa [reflectedHi_of_not_meetsUpperFace hup]
      · obtain ⟨hnu, hnl⟩ := hother j hj
        rw [reflectedLo_of_not_meetsLowerFace hnl, reflectedHi_of_not_meetsUpperFace hnu]
        exact hy j
    · have h1 := (hy i).1
      rw [windowLo_of_meetsLowerFace hlow] at h1
      show (0 : ℝ) < -1 * (-(1 / 2 : ℝ) * (3 : ℝ) ^ m - y i)
      linarith only [h1]

/-- **The reflected window is symmetric in a met upper face.**  Only `k < m` and
the met face itself are needed: the reflected `i`-edge has endpoints summing to
`3^m = 2·((1/2)·3^m)`. -/
theorem mem_reflectedWindow_coordFaceReflection_iff {x : Vec d} {m k : ℤ} (hkm : k < m)
    {i : Fin d} (hup : MeetsUpperFace x m k i) (y : Vec d) :
    coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y ∈ reflectedWindow x m k ↔
      y ∈ reflectedWindow x m k := by
  have hlow : ¬ MeetsLowerFace x m k i := not_meetsLowerFace_of_meetsUpperFace hkm hup
  have hsum : reflectedLo x m k i + reflectedHi x m k i = (3 : ℝ) ^ m := by
    rw [reflectedLo_of_not_meetsLowerFace hlow, reflectedHi_of_meetsUpperFace hup]
    ring
  rw [mem_reflectedWindow_iff, mem_reflectedWindow_iff]
  constructor
  · intro hy j
    by_cases hj : j = i
    · subst hj
      have h := hy j
      rw [coordFaceReflection_apply, ite_eq_left rfl] at h
      exact ⟨by linarith only [h.2, hsum], by linarith only [h.1, hsum]⟩
    · have h := hy j
      rwa [coordFaceReflection_apply, ite_eq_right hj] at h
  · intro hy j
    by_cases hj : j = i
    · subst hj
      have h := hy j
      rw [coordFaceReflection_apply, ite_eq_left rfl]
      exact ⟨by linarith only [h.2, hsum], by linarith only [h.1, hsum]⟩
    · rw [coordFaceReflection_apply, ite_eq_right hj]
      exact hy j

/-- The lower-face twin of `mem_reflectedWindow_coordFaceReflection_iff`. -/
theorem mem_reflectedWindow_coordFaceReflection_iff_lower {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i) (y : Vec d) :
    coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y ∈ reflectedWindow x m k ↔
      y ∈ reflectedWindow x m k := by
  have hup : ¬ MeetsUpperFace x m k i := fun h =>
    not_meetsLowerFace_of_meetsUpperFace hkm h hlow
  have hsum : reflectedLo x m k i + reflectedHi x m k i = -(3 : ℝ) ^ m := by
    rw [reflectedLo_of_meetsLowerFace hlow, reflectedHi_of_not_meetsUpperFace hup]
    ring
  rw [mem_reflectedWindow_iff, mem_reflectedWindow_iff]
  constructor
  · intro hy j
    by_cases hj : j = i
    · subst hj
      have h := hy j
      rw [coordFaceReflection_apply, ite_eq_left rfl] at h
      exact ⟨by linarith only [h.2, hsum], by linarith only [h.1, hsum]⟩
    · have h := hy j
      rwa [coordFaceReflection_apply, ite_eq_right hj] at h
  · intro hy j
    by_cases hj : j = i
    · subst hj
      have h := hy j
      rw [coordFaceReflection_apply, ite_eq_left rfl]
      exact ⟨by linarith only [h.2, hsum], by linarith only [h.1, hsum]⟩
    · rw [coordFaceReflection_apply, ite_eq_right hj]
      exact hy j

/-! ## 3. The one-met-face harmonicity transfer on the windows -/

/-- **The one-met-face transfer, upper face.**

`V = (x + □_k) ∩ □_m` meets exactly one face of `∂□_m`, the upper `i`-face.  If
`v` is weakly harmonic on `V` and `w` is an `H¹` function of the reflected
window whose gradient is the odd extension of `v`'s across that face, then `w`
is weakly harmonic on the reflected window. -/
theorem isWeaklyHarmonicOn_reflectedWindow_of_meetsUpperFace {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (v : H1Function (truncatedWindow x m k))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m k) v)
    (w : H1Function (reflectedWindow x m k))
    (hw : ∀ y, w.grad y = oddFaceExtendGrad ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (truncatedWindow x m k) v.grad) y) :
    IsWeaklyHarmonicOn (reflectedWindow x m k) w := by
  have hset : faceHalf (reflectedWindow x m k) i ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1 =
      truncatedWindow x m k := faceHalf_reflectedWindow_of_meetsUpperFace hkm hup hother
  refine isWeaklyHarmonicOn_of_oddFaceExtendGrad
    (isOpenBoundedConvexDomain_reflectedWindow x m k) (σ := 1) (by norm_num)
    (mem_reflectedWindow_coordFaceReflection_iff hkm hup)
    (h1FunctionOfSetEq hset.symm v)
    (isWeaklyHarmonicOn_h1FunctionOfSetEq hset.symm hv) w fun y => ?_
  rw [h1FunctionOfSetEq_grad, hset]
  exact hw y

/-- **The one-met-face transfer, lower face.** -/
theorem isWeaklyHarmonicOn_reflectedWindow_of_meetsLowerFace {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m k j ∧ ¬ MeetsLowerFace x m k j)
    (v : H1Function (truncatedWindow x m k))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m k) v)
    (w : H1Function (reflectedWindow x m k))
    (hw : ∀ y, w.grad y = oddFaceExtendGrad (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (truncatedWindow x m k) v.grad) y) :
    IsWeaklyHarmonicOn (reflectedWindow x m k) w := by
  have hset : faceHalf (reflectedWindow x m k) i (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1) =
      truncatedWindow x m k := faceHalf_reflectedWindow_of_meetsLowerFace hkm hlow hother
  refine isWeaklyHarmonicOn_of_oddFaceExtendGrad
    (isOpenBoundedConvexDomain_reflectedWindow x m k) (σ := -1) (by norm_num)
    (mem_reflectedWindow_coordFaceReflection_iff_lower hkm hlow)
    (h1FunctionOfSetEq hset.symm v)
    (isWeaklyHarmonicOn_h1FunctionOfSetEq hset.symm hv) w fun y => ?_
  rw [h1FunctionOfSetEq_grad, hset]
  exact hw y

end

end Algsuperdiff.Section4.Provider.ExcessDecay
