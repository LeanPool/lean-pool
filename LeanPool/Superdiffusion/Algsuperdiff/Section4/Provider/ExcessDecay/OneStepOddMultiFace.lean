/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OddReflectionAssembly

/-!
# OneStepOddMultiFace

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The multi-met-face harmonicity transfer

This module builds them and proves the iteration.

## The boxes

`partialReflectedWindow x m k T` is the coordinate box whose `i`-edge is the
*reflected* edge for `i ∈ T` and the *window* edge otherwise.  It is again an
open bounded convex box (all three properties are per-coordinate), it is
`truncatedWindow` at `T = ∅`, and it is `reflectedWindow` as soon as `T` contains
every met coordinate.

## The step

The two geometric facts of `OddReflectionAssembly` hold verbatim at a general
`B_T`, and *without the single-met-face hypothesis*: the tangential coordinates
of `B_{T ∪ {i}}` and `B_T` agree by construction, so the one-face computation is
the only one that happens.

* `mem_partialReflectedWindow_coordFaceReflection_iff_upper` — `B_T` is invariant
  under the reflection in a met face `i ∈ T` (its reflected `i`-edge has
  endpoints summing to `3^m`);
* `faceHalf_partialReflectedWindow_insert_upper` — the half of `B_{T ∪ {i}}` on
  the window side of the met `i`-face is `B_T`.

Composing them with `HarmonicityTransferFace.isWeaklyHarmonicOn_of_oddFaceExtendGrad`
gives the single step `isWeaklyHarmonicOn_partialReflectedWindow_insert_upper`
and its lower-face twin: **one met face is unfolded at a time, at any stage of
the fold**.

## The iteration

`isWeaklyHarmonicOn_partialReflectedWindow_of_chain` runs the induction over the
met set: given a family of `H¹` data, one per intermediate box, each pinned to
the odd extension of the previous one's gradient, weak harmonicity propagates
from `B_∅` to every `B_T` with `T` inside the met set — and hence, by
`partialReflectedWindow_eq_reflectedWindow`, to the fully reflected window
(`isWeaklyHarmonicOn_reflectedWindow_of_chain`).  As in the one-face case the
`H¹` *packaging* at each stage is an input, not an output.

## Scope note (measured, not hidden)

What is removed here is the one-met-face restriction on the **transfer**.  The
odd *affine class* still collapses at two met faces
(`OddReflectionMap.affineLift_eq_zero_of_two_met`: at an edge or corner of `□_m`
the only odd affine function is `0`), so the odd-class pricing of the boundary
datum degenerates in the corner regime — that is a property of the class, not of
this transfer.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The intermediate partially reflected boxes -/

/-- The lower endpoint of the `i`-edge of the box that reflects exactly the
faces of `T`. -/
def partialReflectedLo (x : Vec d) (m k : ℤ) (T : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ T then reflectedLo x m k i else windowLo x m k i

/-- The upper endpoint of the `i`-edge of the box that reflects exactly the
faces of `T`. -/
def partialReflectedHi (x : Vec d) (m k : ℤ) (T : Finset (Fin d)) (i : Fin d) : ℝ :=
  if i ∈ T then reflectedHi x m k i else windowHi x m k i

/-- **The intermediate box `B_T`**: the window with exactly the faces of `T`
reflected. -/
def partialReflectedWindow (x : Vec d) (m k : ℤ) (T : Finset (Fin d)) : Set (Vec d) :=
  coordBox (partialReflectedLo x m k T) (partialReflectedHi x m k T)

theorem mem_partialReflectedWindow_iff {x : Vec d} {m k : ℤ} {T : Finset (Fin d)}
    {y : Vec d} :
    y ∈ partialReflectedWindow x m k T ↔
      ∀ i, partialReflectedLo x m k T i < y i ∧ y i < partialReflectedHi x m k T i :=
  mem_coordBox_iff

theorem partialReflectedLo_insert_of_ne {x : Vec d} {m k : ℤ} {T : Finset (Fin d)}
    {i j : Fin d} (hji : j ≠ i) :
    partialReflectedLo x m k (insert i T) j = partialReflectedLo x m k T j := by
  have hiff : j ∈ insert i T ↔ j ∈ T := by simp [Finset.mem_insert, hji]
  simp only [partialReflectedLo, hiff]

theorem partialReflectedHi_insert_of_ne {x : Vec d} {m k : ℤ} {T : Finset (Fin d)}
    {i j : Fin d} (hji : j ≠ i) :
    partialReflectedHi x m k (insert i T) j = partialReflectedHi x m k T j := by
  have hiff : j ∈ insert i T ↔ j ∈ T := by simp [Finset.mem_insert, hji]
  simp only [partialReflectedHi, hiff]

/-- At `T = ∅` the intermediate box is the window itself. -/
theorem partialReflectedWindow_empty (x : Vec d) (m k : ℤ) :
    partialReflectedWindow x m k ∅ = truncatedWindow x m k := by
  rw [truncatedWindow_eq_coordBox, partialReflectedWindow]
  have hlo : partialReflectedLo x m k ∅ = windowLo x m k := by
    funext i
    rw [partialReflectedLo, ite_eq_right (Finset.notMem_empty i)]
  have hhi : partialReflectedHi x m k ∅ = windowHi x m k := by
    funext i
    rw [partialReflectedHi, ite_eq_right (Finset.notMem_empty i)]
  rw [hlo, hhi]

/-- As soon as `T` contains every met coordinate, the intermediate box is the
fully reflected window. -/
theorem partialReflectedWindow_eq_reflectedWindow {x : Vec d} {m k : ℤ}
    {S : Finset (Fin d)}
    (hS : ∀ i, i ∉ S → ¬ MeetsUpperFace x m k i ∧ ¬ MeetsLowerFace x m k i) :
    partialReflectedWindow x m k S = reflectedWindow x m k := by
  rw [partialReflectedWindow, reflectedWindow]
  congr 1
  · funext i
    rw [partialReflectedLo]
    by_cases h : i ∈ S
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, reflectedLo_of_not_meetsLowerFace (hS i h).2]
  · funext i
    rw [partialReflectedHi]
    by_cases h : i ∈ S
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, reflectedHi_of_not_meetsUpperFace (hS i h).1]

/-! ## 2. The intermediate boxes are open bounded convex domains -/

theorem isOpen_partialReflectedWindow (x : Vec d) (m k : ℤ) (T : Finset (Fin d)) :
    IsOpen (partialReflectedWindow x m k T) :=
  isOpen_coordBox _ _

theorem convex_partialReflectedWindow (x : Vec d) (m k : ℤ) (T : Finset (Fin d)) :
    Convex ℝ (partialReflectedWindow x m k T) :=
  convex_coordBox _ _

theorem isBoundedDomain_partialReflectedWindow (x : Vec d) (m k : ℤ)
    (T : Finset (Fin d)) : IsBoundedDomain (partialReflectedWindow x m k T) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨(3 / 2 : ℝ) * (3 : ℝ) ^ m, by linarith only [hpos], ?_⟩
  intro y hy i
  rw [mem_partialReflectedWindow_iff] at hy
  have h1 := (hy i).1
  have h2 := (hy i).2
  rw [abs_le]
  by_cases h : i ∈ T
  · rw [partialReflectedLo, ite_eq_left h] at h1
    rw [partialReflectedHi, ite_eq_left h] at h2
    have hlo := le_reflectedLo x m k i
    have hhi := reflectedHi_le x m k i
    exact ⟨by linarith only [h1, hlo], by linarith only [h2, hhi]⟩
  · rw [partialReflectedLo, ite_eq_right h] at h1
    rw [partialReflectedHi, ite_eq_right h] at h2
    have hlo := neg_half_zpow_le_windowLo x m k i
    have hhi := windowHi_le_half_zpow x m k i
    exact ⟨by linarith only [h1, hlo, hpos], by linarith only [h2, hhi, hpos]⟩

theorem isOpenBoundedConvexDomain_partialReflectedWindow (x : Vec d) (m k : ℤ)
    (T : Finset (Fin d)) : IsOpenBoundedConvexDomain (partialReflectedWindow x m k T) :=
  ⟨isOpen_partialReflectedWindow x m k T, isBoundedDomain_partialReflectedWindow x m k T,
    convex_partialReflectedWindow x m k T⟩

/-! ## 3. The two geometric facts at a general intermediate box -/

/-- **Reflection invariance at an already unfolded met upper face.** -/
theorem mem_partialReflectedWindow_coordFaceReflection_iff_upper {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x m k i) {T : Finset (Fin d)}
    (hiT : i ∈ T) (y : Vec d) :
    coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y ∈ partialReflectedWindow x m k T ↔
      y ∈ partialReflectedWindow x m k T := by
  have hlow : ¬ MeetsLowerFace x m k i := not_meetsLowerFace_of_meetsUpperFace hkm hup
  have hsum : partialReflectedLo x m k T i + partialReflectedHi x m k T i = (3 : ℝ) ^ m := by
    rw [partialReflectedLo, partialReflectedHi, ite_eq_left hiT, ite_eq_left hiT,
      reflectedLo_of_not_meetsLowerFace hlow, reflectedHi_of_meetsUpperFace hup]
    ring
  rw [mem_partialReflectedWindow_iff, mem_partialReflectedWindow_iff]
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

/-- **Reflection invariance at an already unfolded met lower face.** -/
theorem mem_partialReflectedWindow_coordFaceReflection_iff_lower {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i) {T : Finset (Fin d)}
    (hiT : i ∈ T) (y : Vec d) :
    coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y ∈ partialReflectedWindow x m k T ↔
      y ∈ partialReflectedWindow x m k T := by
  have hup : ¬ MeetsUpperFace x m k i := fun h =>
    not_meetsLowerFace_of_meetsUpperFace hkm h hlow
  have hsum : partialReflectedLo x m k T i + partialReflectedHi x m k T i
      = -(3 : ℝ) ^ m := by
    rw [partialReflectedLo, partialReflectedHi, ite_eq_left hiT, ite_eq_left hiT,
      reflectedLo_of_meetsLowerFace hlow, reflectedHi_of_not_meetsUpperFace hup]
    ring
  rw [mem_partialReflectedWindow_iff, mem_partialReflectedWindow_iff]
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

/-- **The previous box is the half of the next one**, upper met face.  No
single-met-face hypothesis: the tangential edges agree by construction. -/
theorem faceHalf_partialReflectedWindow_insert_upper {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x m k i) {T : Finset (Fin d)}
    (hiT : i ∉ T) :
    faceHalf (partialReflectedWindow x m k (insert i T)) i
        ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1
      = partialReflectedWindow x m k T := by
  have hlow : ¬ MeetsLowerFace x m k i := not_meetsLowerFace_of_meetsUpperFace hkm hup
  have hloi : partialReflectedLo x m k (insert i T) i = windowLo x m k i := by
    rw [partialReflectedLo, ite_eq_left (Finset.mem_insert_self i T),
      reflectedLo_of_not_meetsLowerFace hlow]
  have hhii : partialReflectedHi x m k (insert i T) i
      = (3 : ℝ) ^ m - windowLo x m k i := by
    rw [partialReflectedHi, ite_eq_left (Finset.mem_insert_self i T),
      reflectedHi_of_meetsUpperFace hup]
  have hloT : partialReflectedLo x m k T i = windowLo x m k i := by
    rw [partialReflectedLo, ite_eq_right hiT]
  have hhiT : partialReflectedHi x m k T i = (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    rw [partialReflectedHi, ite_eq_right hiT, windowHi_of_meetsUpperFace hup]
  ext y
  rw [mem_faceHalf_iff, mem_partialReflectedWindow_iff, mem_partialReflectedWindow_iff]
  constructor
  · rintro ⟨hy, hlt⟩ j
    have hlt' : y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
      have : (0 : ℝ) < 1 * ((1 / 2 : ℝ) * (3 : ℝ) ^ m - y i) := hlt
      linarith only [this]
    by_cases hj : j = i
    · subst hj
      have h1 := (hy j).1
      rw [hloi] at h1
      exact ⟨by rw [hloT]; exact h1, by rw [hhiT]; exact hlt'⟩
    · have h := hy j
      rwa [partialReflectedLo_insert_of_ne hj, partialReflectedHi_insert_of_ne hj] at h
  · intro hy
    have hyi := hy i
    rw [hloT, hhiT] at hyi
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [hloi, hhii]
        exact ⟨hyi.1, by linarith only [hyi.1, hyi.2]⟩
      · rw [partialReflectedLo_insert_of_ne hj, partialReflectedHi_insert_of_ne hj]
        exact hy j
    · show (0 : ℝ) < 1 * ((1 / 2 : ℝ) * (3 : ℝ) ^ m - y i)
      linarith only [hyi.2]

/-- **The previous box is the half of the next one**, lower met face. -/
theorem faceHalf_partialReflectedWindow_insert_lower {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i) {T : Finset (Fin d)}
    (hiT : i ∉ T) :
    faceHalf (partialReflectedWindow x m k (insert i T)) i
        (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1)
      = partialReflectedWindow x m k T := by
  have hup : ¬ MeetsUpperFace x m k i := fun h =>
    not_meetsLowerFace_of_meetsUpperFace hkm h hlow
  have hloi : partialReflectedLo x m k (insert i T) i
      = -(3 : ℝ) ^ m - windowHi x m k i := by
    rw [partialReflectedLo, ite_eq_left (Finset.mem_insert_self i T),
      reflectedLo_of_meetsLowerFace hlow]
  have hhii : partialReflectedHi x m k (insert i T) i = windowHi x m k i := by
    rw [partialReflectedHi, ite_eq_left (Finset.mem_insert_self i T),
      reflectedHi_of_not_meetsUpperFace hup]
  have hloT : partialReflectedLo x m k T i = -(1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    rw [partialReflectedLo, ite_eq_right hiT, windowLo_of_meetsLowerFace hlow]
  have hhiT : partialReflectedHi x m k T i = windowHi x m k i := by
    rw [partialReflectedHi, ite_eq_right hiT]
  ext y
  rw [mem_faceHalf_iff, mem_partialReflectedWindow_iff, mem_partialReflectedWindow_iff]
  constructor
  · rintro ⟨hy, hlt⟩ j
    have hlt' : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < y i := by
      have : (0 : ℝ) < -1 * (-(1 / 2 : ℝ) * (3 : ℝ) ^ m - y i) := hlt
      linarith only [this]
    by_cases hj : j = i
    · subst hj
      have h2 := (hy j).2
      rw [hhii] at h2
      exact ⟨by rw [hloT]; exact hlt', by rw [hhiT]; exact h2⟩
    · have h := hy j
      rwa [partialReflectedLo_insert_of_ne hj, partialReflectedHi_insert_of_ne hj] at h
  · intro hy
    have hyi := hy i
    rw [hloT, hhiT] at hyi
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj
        rw [hloi, hhii]
        exact ⟨by linarith only [hyi.1, hyi.2], hyi.2⟩
      · rw [partialReflectedLo_insert_of_ne hj, partialReflectedHi_insert_of_ne hj]
        exact hy j
    · show (0 : ℝ) < -1 * (-(1 / 2 : ℝ) * (3 : ℝ) ^ m - y i)
      linarith only [hyi.1]

/-! ## 4. The single unfolding step, at any stage -/

/-- **One met upper face unfolded, at any stage of the fold.** -/
theorem isWeaklyHarmonicOn_partialReflectedWindow_insert_upper {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hup : MeetsUpperFace x m k i) {T : Finset (Fin d)}
    (hiT : i ∉ T)
    (v : H1Function (partialReflectedWindow x m k T))
    (hv : IsWeaklyHarmonicOn (partialReflectedWindow x m k T) v)
    (w : H1Function (partialReflectedWindow x m k (insert i T)))
    (hw : ∀ y, w.grad y = oddFaceExtendGrad ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (partialReflectedWindow x m k T) v.grad) y) :
    IsWeaklyHarmonicOn (partialReflectedWindow x m k (insert i T)) w := by
  have hset : faceHalf (partialReflectedWindow x m k (insert i T)) i
      ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1 = partialReflectedWindow x m k T :=
    faceHalf_partialReflectedWindow_insert_upper hkm hup hiT
  refine isWeaklyHarmonicOn_of_oddFaceExtendGrad
    (isOpenBoundedConvexDomain_partialReflectedWindow x m k (insert i T)) (σ := 1)
    (by norm_num)
    (mem_partialReflectedWindow_coordFaceReflection_iff_upper hkm hup
      (Finset.mem_insert_self i T))
    (h1FunctionOfSetEq hset.symm v)
    (isWeaklyHarmonicOn_h1FunctionOfSetEq hset.symm hv) w fun y => ?_
  rw [h1FunctionOfSetEq_grad, hset]
  exact hw y

/-- **One met lower face unfolded, at any stage of the fold.** -/
theorem isWeaklyHarmonicOn_partialReflectedWindow_insert_lower {x : Vec d} {m k : ℤ}
    (hkm : k < m) {i : Fin d} (hlow : MeetsLowerFace x m k i) {T : Finset (Fin d)}
    (hiT : i ∉ T)
    (v : H1Function (partialReflectedWindow x m k T))
    (hv : IsWeaklyHarmonicOn (partialReflectedWindow x m k T) v)
    (w : H1Function (partialReflectedWindow x m k (insert i T)))
    (hw : ∀ y, w.grad y = oddFaceExtendGrad (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (partialReflectedWindow x m k T) v.grad) y) :
    IsWeaklyHarmonicOn (partialReflectedWindow x m k (insert i T)) w := by
  have hset : faceHalf (partialReflectedWindow x m k (insert i T)) i
      (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1) = partialReflectedWindow x m k T :=
    faceHalf_partialReflectedWindow_insert_lower hkm hlow hiT
  refine isWeaklyHarmonicOn_of_oddFaceExtendGrad
    (isOpenBoundedConvexDomain_partialReflectedWindow x m k (insert i T)) (σ := -1)
    (by norm_num)
    (mem_partialReflectedWindow_coordFaceReflection_iff_lower hkm hlow
      (Finset.mem_insert_self i T))
    (h1FunctionOfSetEq hset.symm v)
    (isWeaklyHarmonicOn_h1FunctionOfSetEq hset.symm hv) w fun y => ?_
  rw [h1FunctionOfSetEq_grad, hset]
  exact hw y

/-! ## 5. The iteration -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
