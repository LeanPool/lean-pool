/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FloatLib Team
-/

/-
Upstream FloatLib code retains its MIT license below. The Lean Pool integration changes are
covered by the standard header above.

MIT License

Copyright (c) 2026 FloatLib

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bracketing a Real Value

A location records whether an input is the lower endpoint of a half-open interval or, for an
interior point, whether it lies below, at, or above the midpoint. The refinement rules transfer
this information from a subdivision cell to its enclosing interval. These are the Lean
counterparts of Flocq's `Calc.Bracket` location semantics.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

/-- Position of a real value relative to the lower endpoint and midpoint of a bracket. -/
inductive Location where
  | exact
  | inexact (midpointOrder : Ordering)
  deriving DecidableEq, Repr

/-- Compute the location of `x` in a bracket whose lower endpoint is `d`. -/
noncomputable def inbetweenLocation (d u x : ℝ) : Location :=
  if d < x then .inexact (cmp x ((d + u) / 2)) else .exact

/-- Semantic meaning of a bracket location. -/
inductive Inbetween (d u x : ℝ) : Location → Prop where
  | exact (hx : x = d) : Inbetween d u x .exact
  | inexact (l : Ordering) (hx : d < x ∧ x < u)
      (hmid : cmp x ((d + u) / 2) = l) : Inbetween d u x (.inexact l)

/-- The computed location satisfies the bracket semantics. -/
theorem inbetweenLocation_spec {d u x : ℝ} (_hdu : d < u) (hx : d ≤ x ∧ x < u) :
    Inbetween d u x (inbetweenLocation d u x) := by
  by_cases hdx : d < x
  · rw [inbetweenLocation, ite_eq_left hdx]
    exact .inexact _ ⟨hdx, hx.2⟩ rfl
  · have hxd : x = d := le_antisymm (le_of_not_gt hdx) hx.1
    rw [inbetweenLocation, ite_eq_right hdx]
    exact .exact hxd

/-- A value has at most one semantic location in a fixed bracket. -/
theorem inbetween_unique {d u x : ℝ} {l l' : Location}
    (hl : Inbetween d u x l) (hl' : Inbetween d u x l') : l = l' := by
  cases hl with
  | exact hx =>
      cases hl' with
      | exact => rfl
      | inexact _ hx' _ => exact (not_lt_of_ge (le_of_eq hx)) hx'.1 |>.elim
  | inexact order hbetween hmid =>
      cases hl' with
      | exact hx => exact (ne_of_lt hbetween.1) hx.symm |>.elim
      | inexact order' _ hmid' =>
          congr
          exact hmid.symm.trans hmid'

/-- Every semantic location places the input in the half-open bracket `[d, u)`. -/
theorem inbetween_bounds {d u x : ℝ} {l : Location} (hdu : d < u)
    (hl : Inbetween d u x l) : d ≤ x ∧ x < u := by
  cases hl with
  | exact hx => simpa [hx] using hdu
  | inexact _ hx _ => exact ⟨hx.1.le, hx.2⟩

/-- An inexact location places the input strictly between the bracket endpoints. -/
theorem inbetween_strict_bounds {d u x : ℝ} {order : Ordering}
    (hl : Inbetween d u x (.inexact order)) : d < x ∧ x < u := by
  cases hl
  assumption

/-- Midpoint comparison is equivalent to comparing distances from the two endpoints. -/
theorem inbetween_distance {d u x : ℝ} {order : Ordering}
    (hl : Inbetween d u x (.inexact order)) :
    cmp (x - d) (u - x) = order := by
  cases hl with
  | inexact _ _ hmid =>
      cases order with
      | lt =>
          rw [cmp_eq_lt_iff] at hmid ⊢
          linarith
      | eq =>
          rw [cmp_eq_eq_iff] at hmid ⊢
          linarith
      | gt =>
          rw [cmp_eq_gt_iff] at hmid ⊢
          linarith

/-- The midpoint order also compares the absolute distances to the endpoints. -/
theorem inbetween_abs_distance {d u x : ℝ} {order : Ordering}
    (hl : Inbetween d u x (.inexact order)) :
    cmp |d - x| |u - x| = order := by
  have hx := inbetween_strict_bounds hl
  rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le), abs_of_nonneg (sub_nonneg.mpr hx.2.le),
    neg_sub]
  exact inbetween_distance hl

/-- Every location is realized by a point in every nondegenerate bracket. -/
theorem inbetween_exists {d u : ℝ} (hdu : d < u) (location : Location) :
    ∃ x, Inbetween d u x location := by
  cases location with
  | exact => exact ⟨d, .exact rfl⟩
  | inexact order =>
      cases order with
      | lt =>
          refine ⟨(3 * d + u) / 4, .inexact .lt ?_ ?_⟩
          · constructor <;> linarith
          · rw [cmp_eq_lt_iff]
            linarith
      | eq =>
          refine ⟨(d + u) / 2, .inexact .eq ?_ ?_⟩
          · constructor <;> linarith
          · rw [cmp_eq_eq_iff]
      | gt =>
          refine ⟨(d + 3 * u) / 4, .inexact .gt ?_ ?_⟩
          · constructor <;> linarith
          · rw [cmp_eq_gt_iff]
            linarith

/-- Consecutive points in a positive-step arithmetic progression are strictly ordered. -/
theorem orderedSteps {start step : ℝ} (hstep : 0 < step) (k : ℤ) :
    start + (k : ℝ) * step < start + (k + 1 : ℤ) * step := by
  norm_num only [Int.cast_add, Int.cast_one]
  linarith

/-- Midpoint of an arithmetic progression interval. -/
theorem stepMidpoint (start step : ℝ) (steps : ℤ) :
    (start + (start + (steps : ℝ) * step)) / 2 =
      start + ((steps : ℝ) / 2) * step := by
  ring

/--
A location in an interior arithmetic-progression cell determines a location in the full interval,
given the comparison with the full midpoint.
-/
theorem inbetween_step_interior {start step x : ℝ} {steps k : ℤ}
    {localLocation : Location} {globalOrder : Ordering}
    (hstep : 0 < step) (_hsteps : 1 < steps) (hk : 0 < k ∧ k < steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x localLocation)
    (hmid : cmp x (start + ((steps : ℝ) / 2) * step) = globalOrder) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact globalOrder) := by
  have hlocalOrder := orderedSteps (start := start) hstep k
  have hlocal := inbetween_bounds hlocalOrder hl
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hkn : (k + 1 : ℤ) ≤ steps := Int.add_one_le_iff.mpr hk.2
  have hknR : ((k + 1 : ℤ) : ℝ) ≤ (steps : ℝ) := by exact_mod_cast hkn
  have hmid' : cmp x ((start + (start + (steps : ℝ) * step)) / 2) = globalOrder := by
    rw [stepMidpoint]
    exact hmid
  refine .inexact globalOrder ?_ hmid'
  constructor
  · calc
      start < start + (k : ℝ) * step := by nlinarith
      _ ≤ x := hlocal.1
  · calc
      x < start + ((k + 1 : ℤ) : ℝ) * step := hlocal.2
      _ ≤ start + (steps : ℝ) * step := by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hknR hstep.le) start

/-- A subinterval strictly below the global midpoint has global location `.lt`. -/
theorem inbetween_step_low {start step x : ℝ} {steps k : ℤ}
    {localLocation : Location}
    (hstep : 0 < step) (hsteps : 1 < steps) (hk : 0 < k)
    (hcell : 2 * k + 1 < steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x localLocation) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact .lt) := by
  have hkSteps : k < steps := by linarith
  apply inbetween_step_interior hstep hsteps ⟨hk, hkSteps⟩ hl
  rw [cmp_eq_lt_iff]
  have hlocal := inbetween_bounds (orderedSteps (start := start) hstep k) hl
  have hindex : 2 * (k + 1) ≤ steps := by linarith
  have hindexR : (2 * ((k + 1 : ℤ) : ℝ)) ≤ (steps : ℝ) := by
    exact_mod_cast hindex
  have hscaled := mul_le_mul_of_nonneg_right hindexR hstep.le
  have hbeforeMid : (((k + 1 : ℤ) : ℝ) * step) ≤
      ((steps : ℝ) / 2) * step := by
    nlinarith
  exact hlocal.2.trans_le (by
    simpa [add_comm] using add_le_add_left hbeforeMid start)

/-- A subinterval strictly above the global midpoint has global location `.gt`. -/
theorem inbetween_step_high {start step x : ℝ} {steps k : ℤ}
    {localLocation : Location}
    (hstep : 0 < step) (hsteps : 1 < steps) (hcell : steps < 2 * k)
    (hk : k < steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x localLocation) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact .gt) := by
  have hkPos : 0 < k := by linarith
  apply inbetween_step_interior hstep hsteps ⟨hkPos, hk⟩ hl
  rw [cmp_eq_gt_iff]
  have hlocal := inbetween_bounds (orderedSteps (start := start) hstep k) hl
  have hindexR : (steps : ℝ) < 2 * (k : ℝ) := by exact_mod_cast hcell
  have hscaled := mul_lt_mul_of_pos_right hindexR hstep
  have hafterMid : ((steps : ℝ) / 2) * step < (k : ℝ) * step := by
    nlinarith
  have hafterMidStart :
      start + ((steps : ℝ) / 2) * step < start + (k : ℝ) * step := by
    simpa [add_comm] using add_lt_add_left hafterMid start
  exact hafterMidStart.trans_le hlocal.1

/-- Exactness at the first cell's lower endpoint remains exact in the full interval. -/
theorem inbetween_step_zero_exact {start step x : ℝ} {steps : ℤ}
    (hl : Inbetween start (start + step) x .exact) :
    Inbetween start (start + (steps : ℝ) * step) x .exact := by
  cases hl with
  | exact hx => exact .exact hx

/-- An inexact point in the first cell lies below the full midpoint when there are several cells. -/
theorem inbetween_step_zero_inexact {start step x : ℝ} {steps : ℤ}
    {order : Ordering} (hstep : 0 < step) (hsteps : 1 < steps)
    (hl : Inbetween start (start + step) x (.inexact order)) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact .lt) := by
  have hlocal := inbetween_strict_bounds hl
  have htwo : (2 : ℤ) ≤ steps := Int.add_one_le_iff.mpr hsteps
  have htwoR : (2 : ℝ) ≤ (steps : ℝ) := by exact_mod_cast htwo
  have hscaled := mul_le_mul_of_nonneg_right htwoR hstep.le
  have hstepMid : step ≤ ((steps : ℝ) / 2) * step := by nlinarith
  have hstepAll : step < (steps : ℝ) * step := by
    have hstepsR : (1 : ℝ) < (steps : ℝ) := by exact_mod_cast hsteps
    nlinarith
  have hstepAllStart : start + step < start + (steps : ℝ) * step := by
    simpa [add_comm] using add_lt_add_left hstepAll start
  refine .inexact .lt ⟨hlocal.1, hlocal.2.trans hstepAllStart⟩ ?_
  rw [cmp_eq_lt_iff, stepMidpoint]
  exact hlocal.2.trans_le (by
    simpa [add_comm] using add_le_add_left hstepMid start)

/-- At the central lower endpoint of an even subdivision, the global location is midpoint exact. -/
theorem inbetween_step_middle_even_exact {start step x : ℝ} {steps k : ℤ}
    (hstep : 0 < step) (hsteps : 1 < steps) (hmiddle : 2 * k = steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x .exact) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact .eq) := by
  cases hl with
  | exact hx =>
      have hkPos : 0 < k := by linarith
      have hkSteps : k < steps := by linarith
      apply inbetween_step_interior hstep hsteps ⟨hkPos, hkSteps⟩ (.exact hx)
      rw [cmp_eq_eq_iff]
      have hmiddleR : (2 : ℝ) * (k : ℝ) = (steps : ℝ) := by exact_mod_cast hmiddle
      rw [hx]
      nlinarith

/-- An inexact point in the central cell of an even subdivision is above the global midpoint. -/
theorem inbetween_step_middle_even_inexact {start step x : ℝ} {steps k : ℤ}
    {order : Ordering} (hstep : 0 < step) (hsteps : 1 < steps)
    (hmiddle : 2 * k = steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x (.inexact order)) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact .gt) := by
  have hkPos : 0 < k := by linarith
  have hkSteps : k < steps := by linarith
  apply inbetween_step_interior hstep hsteps ⟨hkPos, hkSteps⟩ hl
  rw [cmp_eq_gt_iff]
  have hlocal := inbetween_strict_bounds hl
  have hmiddleR : (2 : ℝ) * (k : ℝ) = (steps : ℝ) := by exact_mod_cast hmiddle
  nlinarith

/-- At the lower endpoint of the central cell of an odd subdivision, the global location is low. -/
theorem inbetween_step_middle_odd_exact {start step x : ℝ} {steps k : ℤ}
    (hstep : 0 < step) (hsteps : 1 < steps) (hmiddle : 2 * k + 1 = steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x .exact) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact .lt) := by
  cases hl with
  | exact hx =>
      have hkPos : 0 < k := by linarith
      have hkSteps : k < steps := by linarith
      apply inbetween_step_interior hstep hsteps ⟨hkPos, hkSteps⟩ (.exact hx)
      rw [cmp_eq_lt_iff, hx]
      have hmiddleR : (2 : ℝ) * (k : ℝ) + 1 = (steps : ℝ) := by
        exact_mod_cast hmiddle
      nlinarith

/-- In the central cell of an odd subdivision, local and global midpoint locations agree. -/
theorem inbetween_step_middle_odd_inexact {start step x : ℝ} {steps k : ℤ}
    {order : Ordering} (hstep : 0 < step) (hsteps : 1 < steps)
    (hmiddle : 2 * k + 1 = steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x (.inexact order)) :
    Inbetween start (start + (steps : ℝ) * step) x (.inexact order) := by
  have hkPos : 0 < k := by linarith
  have hkSteps : k < steps := by linarith
  apply inbetween_step_interior hstep hsteps ⟨hkPos, hkSteps⟩ hl
  cases hl with
  | inexact _ _ hlocalMid =>
      have hmiddleR : (2 : ℝ) * (k : ℝ) + 1 = (steps : ℝ) := by
        exact_mod_cast hmiddle
      have hmidpoints :
          ((start + (k : ℝ) * step) +
              (start + ((k + 1 : ℤ) : ℝ) * step)) / 2 =
            start + ((steps : ℝ) / 2) * step := by
        norm_num only [Int.cast_add, Int.cast_one]
        nlinarith
      rw [← hmidpoints]
      exact hlocalMid

/-- Refine a local location when the enclosing subdivision count is even. -/
def refineLocationEven (steps k : ℤ) (location : Location) : Location :=
  if k = 0 then
    match location with
    | .exact => .exact
    | .inexact _ => .inexact .lt
  else
    match cmp (2 * k) steps with
    | .lt => .inexact .lt
    | .eq =>
        match location with
        | .exact => .inexact .eq
        | .inexact _ => .inexact .gt
    | .gt => .inexact .gt

/-- Refine a local location when the enclosing subdivision count is odd. -/
def refineLocationOdd (steps k : ℤ) (location : Location) : Location :=
  if k = 0 then
    match location with
    | .exact => .exact
    | .inexact _ => .inexact .lt
  else
    match cmp (2 * k + 1) steps with
    | .lt => .inexact .lt
    | .eq =>
        match location with
        | .exact => .inexact .lt
        | .inexact order => .inexact order
    | .gt => .inexact .gt

/-- Correctness of location refinement for an even number of cells. -/
theorem refineLocationEven_correct {start step x : ℝ} {steps k : ℤ}
    {location : Location} (hstep : 0 < step) (hsteps : 1 < steps)
    (heven : Even steps) (hk : 0 ≤ k ∧ k < steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x location) :
    Inbetween start (start + (steps : ℝ) * step) x
      (refineLocationEven steps k location) := by
  by_cases hkZero : k = 0
  · subst k
    cases location with
    | exact =>
        simpa [refineLocationEven] using
          (inbetween_step_zero_exact (steps := steps) (by simpa using hl))
    | inexact order =>
        simpa [refineLocationEven] using
          (inbetween_step_zero_inexact (steps := steps) hstep hsteps (by simpa using hl))
  · have hkPos : 0 < k := lt_of_le_of_ne hk.1 (Ne.symm hkZero)
    obtain ⟨half, hhalf⟩ := even_iff_exists_two_mul.mp heven
    rcases lt_trichotomy (2 * k) steps with hlow | hmiddle | hhigh
    · have hkHalf : k < half := by linarith
      have hkNext : k + 1 ≤ half := Int.add_one_le_iff.mpr hkHalf
      have hcell : 2 * k + 1 < steps := by linarith
      simpa [refineLocationEven, hkZero, (cmp_eq_lt_iff _ _).2 hlow] using
        inbetween_step_low hstep hsteps hkPos hcell hl
    · cases location with
      | exact =>
          simpa [refineLocationEven, hkZero, (cmp_eq_eq_iff _ _).2 hmiddle] using
            inbetween_step_middle_even_exact hstep hsteps hmiddle hl
      | inexact order =>
          simpa [refineLocationEven, hkZero, (cmp_eq_eq_iff _ _).2 hmiddle] using
            inbetween_step_middle_even_inexact hstep hsteps hmiddle hl
    · simpa [refineLocationEven, hkZero, (cmp_eq_gt_iff _ _).2 hhigh] using
        inbetween_step_high hstep hsteps hhigh hk.2 hl

/-- Correctness of location refinement for an odd number of cells. -/
theorem refineLocationOdd_correct {start step x : ℝ} {steps k : ℤ}
    {location : Location} (hstep : 0 < step) (hsteps : 1 < steps)
    (hodd : Odd steps) (hk : 0 ≤ k ∧ k < steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x location) :
    Inbetween start (start + (steps : ℝ) * step) x
      (refineLocationOdd steps k location) := by
  by_cases hkZero : k = 0
  · subst k
    cases location with
    | exact =>
        simpa [refineLocationOdd] using
          (inbetween_step_zero_exact (steps := steps) (by simpa using hl))
    | inexact order =>
        simpa [refineLocationOdd] using
          (inbetween_step_zero_inexact (steps := steps) hstep hsteps (by simpa using hl))
  · have hkPos : 0 < k := lt_of_le_of_ne hk.1 (Ne.symm hkZero)
    obtain ⟨half, hhalf⟩ := odd_iff_exists_bit1.mp hodd
    rcases lt_trichotomy (2 * k + 1) steps with hlow | hmiddle | hhigh
    · simpa [refineLocationOdd, hkZero, (cmp_eq_lt_iff _ _).2 hlow] using
        inbetween_step_low hstep hsteps hkPos hlow hl
    · cases location with
      | exact =>
          simpa [refineLocationOdd, hkZero, (cmp_eq_eq_iff _ _).2 hmiddle] using
            inbetween_step_middle_odd_exact hstep hsteps hmiddle hl
      | inexact order =>
          simpa [refineLocationOdd, hkZero, (cmp_eq_eq_iff _ _).2 hmiddle] using
            inbetween_step_middle_odd_inexact hstep hsteps hmiddle hl
    · have hhalfK : half < k := by linarith
      have hhalfNext : half + 1 ≤ k := Int.add_one_le_iff.mpr hhalfK
      have hcell : steps < 2 * k := by linarith
      simpa [refineLocationOdd, hkZero, (cmp_eq_gt_iff _ _).2 hhigh] using
        inbetween_step_high hstep hsteps hcell hk.2 hl

/--
Refine a local location, selecting the even or odd subdivision rule automatically.

The parity test is the decidable `steps % 2 = 0`, so this definition and the truncation layer
built on it are executable.
-/
def refineLocation (steps k : ℤ)
    (location : Location) : Location :=
  if steps % 2 = 0 then
    refineLocationEven steps k location
  else
    refineLocationOdd steps k location

/-- Correctness of automatic local-to-global location refinement. -/
theorem refineLocation_correct {start step x : ℝ} {steps k : ℤ}
    {location : Location} (hstep : 0 < step) (hsteps : 1 < steps)
    (hk : 0 ≤ k ∧ k < steps)
    (hl : Inbetween
      (start + (k : ℝ) * step)
      (start + (k + 1 : ℤ) * step) x location) :
    Inbetween start (start + (steps : ℝ) * step) x
      (refineLocation steps k location) := by
  by_cases heven : steps % 2 = 0
  · rw [refineLocation, ite_eq_left heven]
    exact refineLocationEven_correct hstep hsteps (Int.even_iff.mpr heven) hk hl
  · rw [refineLocation, ite_eq_right heven]
    exact refineLocationOdd_correct hstep hsteps
      (Int.odd_iff.mpr (Int.emod_two_ne_zero.mp heven)) hk hl

end FloatLib.Floats.Formats.Flocq
