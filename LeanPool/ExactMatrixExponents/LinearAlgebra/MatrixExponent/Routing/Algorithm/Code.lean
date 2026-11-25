/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coloring.Vector
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Transport.System

/-!
# Deterministic straight-line word programs

A program contains its literal bits and words. A gate stores four bits.
The children of a tabulation are a finite array of programs, fixed before
evaluation. The evaluator materializes each result array once. The word
accounting uses pointers to immutable pairs and arrays.
-/

@[expose] public section

section

namespace MatrixMultiplicationAllFields.MatrixExponent.Routing.Algorithm
open Coloring

/-- The code used in the `Algorithm` construction. -/
inductive Code (w : ℕ) : Type → Type → Type 1
  | id {A} : Code w A A
  | fst {A D} : Code w (A × D) A
  | snd {A D} : Code w (A × D) D
  | comp {A D E} : Code w A D → Code w D E → Code w A E
  | pair {A D E} : Code w A D → Code w A E → Code w A (D × E)
  | select {A} : Code w (Bool × A × A) A
  | tab {A D} {h} : h ≤ w → (B h → Code w A D) → Code w A (B h → D)
  | «at» {A} {h} : h ≤ w → B h → Code w (B h → A) A
  | read {A} {h} : h ≤ w → Code w ((B h → A) × B h) A
  | bit {A} : Bool → Code w A Bool
  | lit {A} {h} : h ≤ w → B h → Code w A (B h)
  | gate : Bool → Bool → Bool → Bool → Code w (Bool × Bool) Bool
  | lt {h} : h ≤ w → Code w (B h × B h) Bool
  | eq {h} : h ≤ w → Code w (B h × B h) Bool
  | add {h} : h ≤ w → Code w (B h × B h) (B h)
  | resize {h k} : h ≤ w → k ≤ w → Code w (B h) (B k)
  | odd {h} : h ≤ w → Code w (B h) Bool
  | halve {h} : h ≤ w → Code w (B h) (B h)

namespace Code
variable {w h : ℕ} {A D : Type}

/-- Materialize the child array, whose entries can then be read by index. -/
def tabulate (hh : h ≤ w) (f : B h → Code w A D) : Code w A (B h → D) :=
  let a := Vector.ofFn f
  tab hh (fun i => a[i.val])

/-- In the case `_, _, .id, x`, this construction gives `x`. -/
def eval : {A D : Type} → Code w A D → A → D
  | _, _, .id, x => x
  | _, _, .fst, x => x.1
  | _, _, .snd, x => x.2
  | _, _, .comp f g, x => g.eval (f.eval x)
  | _, _, .pair f g, x => (f.eval x, g.eval x)
  | _, _, .select, x => if x.1 then x.2.1 else x.2.2
  | _, _, .tab _ f, x =>
    let a := Vector.ofFn (fun i => (f i).eval x)
    fun i => a[i.val]
  | _, _, .at _ i, x => x i
  | _, _, .read _, x => x.1 x.2
  | _, _, .bit b, _ => b
  | _, _, .lit _ i, _ => i
  | _, _, .gate a b c d, x => if x.1 then (if x.2 then d else c) else (if x.2 then b else a)
  | _, _, .lt _, x => decide (x.1 < x.2)
  | _, _, .eq _, x => decide (x.1 = x.2)
  | _, _, .add _, x => x.1 + x.2
  | _, _, .resize _ _, x => Fin.ofNat _ x.val
  | _, _, .odd _, x => decide (x.val % 2 = 1)
  | _, _, .halve _, x => ⟨x.val / 2, (Nat.div_le_self ..).trans_lt x.isLt⟩

/-- Charge each instruction once and each table slot once. -/
def charge (header slot : ℕ) : {A D : Type} → Code w A D → ℕ
  | _, _, .comp f g => header + charge header slot f + charge header slot g
  | _, _, .pair f g => header + charge header slot f + charge header slot g
  | _, _, .tab _ f => header + ∑ i, (slot + charge header slot (f i))
  | _, _, _ => header

/-- Reserve an opcode, literal/width fields, and child references in an
eight-word header. Each tabulation has one additional reference per child. -/
def advice (c : Code w A D) := charge 8 1 c

/-- A frame holds operands, result and continuation. Pairs can stay in
the frame. Tabulation allocates one extra result word per slot. -/
def scratch (c : Code w A D) := charge 8 1 c

/-- Word cost with a fixed charge for dispatch, operations and frame
access. A table slot includes reading its child offset and writing its result. -/
def time (c : Code w A D) := charge 16 4 c

end Code
end MatrixMultiplicationAllFields.MatrixExponent.Routing.Algorithm
end
