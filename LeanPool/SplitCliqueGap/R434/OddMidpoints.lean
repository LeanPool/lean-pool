/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

/-! # Midpoints on odd residue spaces -/

@[expose] public section

namespace GapExtremal.R434

/-- The inverse of two in the cyclic ring when its modulus is odd. -/
def oddHalf (m : ℕ) : ZMod m := (((m + 1) / 2 : ℕ) : ZMod m)

theorem two_mul_oddHalf {m : ℕ} (hm : Odd m) : (2 : ZMod m) * oddHalf m = 1 := by
  obtain ⟨k, hk⟩ := hm
  have hN : 2 * ((m + 1) / 2) = m + 1 := by omega
  have hM := congrArg (fun n : ℕ => (n : ZMod m)) hN
  push_cast at hM
  simpa [oddHalf] using hM

/-- With equal parities, integer and modular midpoints coincide. -/
theorem natCast_midpoint {m a b : ℕ} (hm : Odd m) (hab : a % 2 = b % 2) :
    oddHalf m * ((a : ZMod m) + (b : ZMod m)) = (((a + b) / 2 : ℕ) : ZMod m) := by
  have hN : 2 * ((a + b) / 2) = a + b := by omega
  have hM := congrArg (fun n : ℕ => (n : ZMod m)) hN
  push_cast at hM
  rw [← hM]
  calc
    oddHalf m * (2 * (((a + b) / 2 : ℕ) : ZMod m)) =
        (2 * oddHalf m) * (((a + b) / 2 : ℕ) : ZMod m) := by ring
    _ = _ := by rw [two_mul_oddHalf hm, one_mul]

section Positions

variable {R : Type*} [CommRing R]

theorem triangle_directions (h x y z : R) (hh : 2 * h = 1) :
    (y - x) + (z - y) = 2 * (h * (z - x)) := by
  rw [← mul_assoc, hh, one_mul]
  ring

theorem palette_direction (h d invD c u v : R) (hd : invD * d = 1) :
    invD * ((c + d * h * v) - (c - d * h * u)) = h * (u + v) := by
  calc
    _ = (invD * d) * (h * (u + v)) := by ring
    _ = _ := by rw [hd, one_mul]

theorem midpoint_partner_unique (h x y y' : R) (hh : 2 * h = 1)
    (hc : h * (x + y) = h * (x + y')) : y = y' := by
  have htwo := congrArg (fun b : R => 2 * b) hc
  simp only [← mul_assoc, hh, one_mul] at htwo
  exact add_left_cancel htwo

end Positions

end GapExtremal.R434
