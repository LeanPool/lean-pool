/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic

/-!
# The two Hamilton ports at a vertex

XII (4.5), page 252: "To see this, first draw a Hamilton circuit
without crossings, and then add the remaining edges to the drawing,
so that (i)–(vi) are satisfied. Then (vii) is satisfied too."

Use the cyclic order of the vertices for this Hamilton circuit.
In each vertex block, put the incoming Hamilton port first and the
outgoing Hamilton port second. The other ports come after them.
For at least three vertices the two Hamilton neighbors are distinct.
-/

@[expose] public section

namespace GraphMinor.GM12

/-- Local port priorities for the Hamilton circuit in the source
crossing drawing of XII (4.5), page 252. The predecessor port comes
first, the successor port second, and all other ports after them. -/
def hamiltonPortPriority {p : ℕ} (v w : Fin p) : ℕ :=
  if w = (finRotate p).symm v then 0 else if w = finRotate p v then 1 else 2

/-- A cyclic successor differs from its vertex when there are at
least two vertices. -/
theorem finRotate_ne_self_of_two_le {p : ℕ} (hp : 2 ≤ p) (v : Fin p) :
    finRotate p v ≠ v := by
  let : NeZero p := ⟨by omega⟩
  intro h
  rw [finRotate_apply] at h
  have h01 : (1 : Fin p) = 0 := add_left_cancel (show v + 1 = v + 0 by simpa using h)
  have hval := congrArg Fin.val h01
  have h1 : (1 : ℕ) < p := by omega
  simp [Nat.mod_eq_of_lt h1] at hval

/-- A cyclic predecessor differs from its vertex when there are
at least two vertices. -/
theorem finRotate_predecessor_ne_self_of_two_le {p : ℕ} (hp : 2 ≤ p) (v : Fin p) :
    (finRotate p).symm v ≠ v := by
  intro h
  have heq := congrArg (finRotate p) h
  rw [Equiv.apply_symm_apply] at heq
  exact finRotate_ne_self_of_two_le hp v heq.symm

/-- The predecessor and successor in a Hamilton circuit are
distinct when the circuit has at least three vertices. -/
theorem finRotate_predecessor_ne_successor {p : ℕ} (hp : 3 ≤ p) (v : Fin p) :
    (finRotate p).symm v ≠ finRotate p v := by
  let : NeZero p := ⟨by omega⟩
  intro h
  have hrot := congrArg (finRotate p) h
  rw [Equiv.apply_symm_apply, finRotate_apply, finRotate_apply] at hrot
  have h02 : (0 : Fin p) = (1 : Fin p) + 1 := add_left_cancel
    (show v + 0 = v + (1 + 1) by simpa only [add_zero, add_assoc] using hrot)
  have hval := congrArg Fin.val h02
  have h2 : (2 : ℕ) < p := by omega
  have h1 : (1 : ℕ) < p := by omega
  simp [Fin.val_add, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval

/-- The incoming Hamilton port has first priority. -/
theorem hamiltonPortPriority_predecessor {p : ℕ} (v : Fin p) :
    hamiltonPortPriority v ((finRotate p).symm v) = 0 := by
  simp only [hamiltonPortPriority, ↓reduceIte]

/-- The outgoing Hamilton port has second priority. -/
theorem hamiltonPortPriority_successor {p : ℕ} (hp : 3 ≤ p) (v : Fin p) :
    hamiltonPortPriority v (finRotate p v) = 1 := by
  simp only [hamiltonPortPriority, Ne.symm (finRotate_predecessor_ne_successor hp v), ↓reduceIte]

/-- Every non-Hamilton port follows the two Hamilton ports. -/
theorem hamiltonPortPriority_other {p : ℕ} {v w : Fin p}
    (hpre : w ≠ (finRotate p).symm v) (hnext : w ≠ finRotate p v) :
    hamiltonPortPriority v w = 2 := by
  simp only [hamiltonPortPriority, hpre, hnext, ↓reduceIte]

/-- The incoming port precedes the outgoing port, which precedes
each non-Hamilton port. These strict priorities specify the order
within each vertex block in XII (4.5), page 252. -/
theorem hamiltonPortPriority_order {p : ℕ} (hp : 3 ≤ p) {v w : Fin p}
    (hpre : w ≠ (finRotate p).symm v) (hnext : w ≠ finRotate p v) :
    hamiltonPortPriority v ((finRotate p).symm v) <
      hamiltonPortPriority v (finRotate p v) ∧
    hamiltonPortPriority v (finRotate p v) < hamiltonPortPriority v w := by
  rw [hamiltonPortPriority_predecessor, hamiltonPortPriority_successor hp,
    hamiltonPortPriority_other hpre hnext]
  decide

/-- Predecessor, vertex, and successor occur in cyclic order in
the Hamilton circuit, including its wrap at zero. -/
theorem finRotate_neighbors_cyclic_order {p : ℕ} (hp : 3 ≤ p) (v : Fin p) :
    ((finRotate p).symm v < v ∧ v < finRotate p v) ∨
      (v < finRotate p v ∧ finRotate p v < (finRotate p).symm v) ∨
      (finRotate p v < (finRotate p).symm v ∧ (finRotate p).symm v < v) := by
  cases p with
  | zero => omega
  | succ q =>
    have hq : 2 ≤ q := by omega
    have hprezero : (finRotate (q + 1)).symm (0 : Fin (q + 1)) = Fin.last q := by
      apply (finRotate (q + 1)).injective
      rw [Equiv.apply_symm_apply, finRotate_last]
    by_cases hvzero : v = 0
    · subst v
      right; left
      rw [hprezero, finRotate_apply_zero]
      have h1 : (1 : ℕ) < q + 1 := by omega
      constructor <;> simp [Fin.lt_def, Nat.mod_eq_of_lt h1]
      omega
    · have hprev : (finRotate (q + 1)).symm v < v :=
        (finRotate_symm_lt_iff_ne_zero v).mpr hvzero
      by_cases hvlast : v = Fin.last q
      · right; right
        refine ⟨?_, hprev⟩
        rw [hvlast, finRotate_last]
        have hval := coe_finRotate_symm_of_ne_zero hvzero
        change 0 < ((finRotate (q + 1)).symm (Fin.last q)).val
        rw [← hvlast, hval, hvlast, Fin.val_last]
        omega
      · exact Or.inl ⟨hprev, (lt_finRotate_iff_ne_last v).mpr hvlast⟩

end GraphMinor.GM12
