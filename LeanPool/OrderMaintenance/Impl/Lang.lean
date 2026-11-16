/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Model.Wrapper
public import LeanPool.OrderMaintenance.Machine.Logic


/-!
# M6: the core language

A small language for the core's code, with two semantics:
* `evalF` runs on Level F's `Core` (this file);
* `compile` translates to a machine `Stmt` over a fixed memory layout (`Compile.lean`).

`Sim.lean` proves once that the two agree, with the machine cost computed from the source.
Each Level F function is then written in this language, and an agreement lemma shows that
`evalF` computes what the Level F function computes.

All values are `Nat`. A record field is read as a number: `Bool` fields as 0/1 (with `dead`
for `alive`, so that every default record reads 0), `St` as 0–3. A write that the encoding
cannot represent (a `Bool` field set to 5, an index past the capacity) is a **bug** of the
source program: `evalF` returns `.bug`, and the agreement lemmas show that it never happens.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)

/-! ### Encodings of small types -/

/-- Encode a Boolean by zero or one. -/
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Encode the four split lifecycle states by the numbers zero through three. -/
def _root_.OrderMaintenance.Model.St.toN : St → Nat
  | .quiet => 0 | .overflow => 1 | .splitting => 2 | .dead => 3

/-- Decode a numeric lifecycle state, mapping values above two to dead. -/
def _root_.OrderMaintenance.Model.St.ofN : Nat → St
  | 0 => .quiet | 1 => .overflow | 2 => .splitting | _ => .dead

theorem _root_.OrderMaintenance.Model.St.ofN_toN (x : St) : St.ofN x.toN = x := by cases x <;> rfl
theorem _root_.OrderMaintenance.Model.St.toN_ofN {v : Nat} (h : v ≤ 3) : (St.ofN v).toN = v := by
  rcases v with _ | _ | _ | _ | v <;> first | rfl | omega

/-! ### Fields -/

/-- Element fields accessible to the typed implementation language. -/
inductive EF | next | prev | grp | lab | dead | h
  deriving DecidableEq, Repr
/-- Group fields accessible to the typed implementation language. -/
inductive GF | next | prev | first | last | chk | lab | size | st | src | l | r | dead
  deriving DecidableEq, Repr
/-- Chunk fields accessible to the typed implementation language. -/
inductive CF | next | prev | first | last | size | st | src | l | r | tag | dead
  deriving DecidableEq, Repr
/-- Top-tree node fields accessible to the typed implementation language. -/
inductive NF | height | livePar | weight | first | last | draining | t1 | t2 | overflow | dead
  deriving DecidableEq, Repr
/-- Plain arrays of numbers, extended on write (`Array.setX`). -/
inductive AF | pqHead | pqNext | pqPrev | pqWhere | nbNext | nbPrev | lpar
  deriving DecidableEq, Repr
/-- Scalars of the core. -/
inductive SF | count | head | tail | firstGroup | firstChunk | notReady | fallbacks | pqHi | pqLo
  deriving DecidableEq, Repr
/-- Record counts (read only; `push` extends them). -/
inductive Tbl | E | G | C | N
  deriving DecidableEq, Repr
/-- Parameters (read only). -/
inductive PF | N | L | G | T | theta | Be | Bg | De | Dg | KG | KC | KR | a | s | beta | H
  deriving DecidableEq, Repr

/-- A numeric field selector across records, plain arrays and core scalars. -/
inductive Fld
  | e (k : EF) | g (k : GF) | c (k : CF) | n (k : NF) | a (k : AF) | s (k : SF)
  deriving DecidableEq, Repr

section fields

/-- Read a element field as a natural number. -/
def EF.get (x : Elem) : EF → Nat
  | .next => x.next | .prev => x.prev | .grp => x.grp | .lab => x.lab
  | .dead => b2n !x.live | .h => x.h

/-- Write a natural-number encoding into a element field. -/
def EF.set (x : Elem) (v : Nat) : EF → Elem
  | .next => { x with next := v } | .prev => { x with prev := v } | .grp => { x with grp := v }
  | .lab => { x with lab := v } | .dead => { x with live := v == 0 } | .h => { x with h := v }

/-- Check that a numeric value is a valid encoding for this element field. -/
def EF.ok (v : Nat) : EF → Bool
  | .dead => decide (v ≤ 1) | _ => true

/-- Read a group field as a natural number. -/
def GF.get (x : Group) : GF → Nat
  | .next => x.next | .prev => x.prev | .first => x.first | .last => x.last | .chk => x.chk
  | .lab => x.lab | .size => x.size | .st => x.st.toN | .src => x.src | .l => x.l | .r => x.r
  | .dead => b2n !x.alive

/-- Write a natural-number encoding into a group field. -/
def GF.set (x : Group) (v : Nat) : GF → Group
  | .next => { x with next := v } | .prev => { x with prev := v } | .first => { x with first := v }
  | .last => { x with last := v } | .chk => { x with chk := v } | .lab => { x with lab := v }
  | .size => { x with size := v } | .st => { x with st := St.ofN v } | .src => { x with src := v }
  | .l => { x with l := v } | .r => { x with r := v } | .dead => { x with alive := v == 0 }

/-- Check that a numeric value is a valid encoding for this group field. -/
def GF.ok (v : Nat) : GF → Bool
  | .st => v ≤ 3 | .dead => decide (v ≤ 1) | _ => true

/-- Read a chunk field as a natural number. -/
def CF.get (x : Chunk) : CF → Nat
  | .next => x.next | .prev => x.prev | .first => x.first | .last => x.last | .size => x.size
  | .st => x.st.toN | .src => x.src | .l => x.l | .r => x.r | .tag => x.tag | .dead => b2n !x.alive

/-- Write a natural-number encoding into a chunk field. -/
def CF.set (x : Chunk) (v : Nat) : CF → Chunk
  | .next => { x with next := v } | .prev => { x with prev := v } | .first => { x with first := v }
  | .last => { x with last := v } | .size => { x with size := v } | .st => { x with st := St.ofN v }
  | .src => { x with src := v } | .l => { x with l := v } | .r => { x with r := v }
  | .tag => { x with tag := v } | .dead => { x with alive := v == 0 }

/-- Check that a numeric value is a valid encoding for this chunk field. -/
def CF.ok (v : Nat) : CF → Bool
  | .st => v ≤ 3 | .dead => decide (v ≤ 1) | _ => true

/-- Read a top-tree node field as a natural number. -/
def NF.get (x : Node) : NF → Nat
  | .height => x.height | .livePar => x.livePar | .weight => x.weight | .first => x.first
  | .last => x.last | .draining => b2n x.draining | .t1 => x.t1 | .t2 => x.t2
  | .overflow => x.overflowOf | .dead => b2n !x.alive

/-- Write a natural-number encoding into a top-tree node field. -/
def NF.set (x : Node) (v : Nat) : NF → Node
  | .height => { x with height := v } | .livePar => { x with livePar := v }
  | .weight => { x with weight := v } | .first => { x with first := v } | .last => { x with last := v }
  | .draining => { x with draining := v != 0 } | .t1 => { x with t1 := v } | .t2 => { x with t2 := v }
  | .overflow => { x with overflowOf := v } | .dead => { x with alive := v == 0 }

/-- Check that a numeric value is a valid encoding for this top-tree node field. -/
def NF.ok (v : Nat) : NF → Bool
  | .draining => v ≤ 1 | .dead => decide (v ≤ 1) | _ => true

/-- Read a plain numeric array from a core. -/
def AF.get (s : Core) : AF → Array Nat
  | .pqHead => s.pqHead | .pqNext => s.pqNext | .pqPrev => s.pqPrev | .pqWhere => s.pqWhere
  | .nbNext => s.nbNext | .nbPrev => s.nbPrev | .lpar => s.lpar

/-- Replace a plain numeric array in a core. -/
def AF.set (s : Core) (a : Array Nat) : AF → Core
  | .pqHead => { s with pqHead := a } | .pqNext => { s with pqNext := a }
  | .pqPrev => { s with pqPrev := a } | .pqWhere => { s with pqWhere := a }
  | .nbNext => { s with nbNext := a } | .nbPrev => { s with nbPrev := a }
  | .lpar => { s with lpar := a }

/-- Read a core scalar as a natural number. -/
def SF.get (s : Core) : SF → Nat
  | .count => s.count | .head => s.head | .tail => s.tail | .firstGroup => s.firstGroup
  | .firstChunk => s.firstChunk | .notReady => b2n !s.ready | .fallbacks => s.fallbacks
  | .pqHi => s.pqHi | .pqLo => s.pqLo

/-- Write a natural-number encoding into a core scalar. -/
def SF.set (s : Core) (v : Nat) : SF → Core
  | .count => { s with count := v } | .head => { s with head := v } | .tail => { s with tail := v }
  | .firstGroup => { s with firstGroup := v } | .firstChunk => { s with firstChunk := v }
  | .notReady => { s with ready := v == 0 } | .fallbacks => { s with fallbacks := v }
  | .pqHi => { s with pqHi := v } | .pqLo => { s with pqLo := v }

/-- Check the Boolean range of the encoded readiness scalar. -/
def SF.ok (v : Nat) : SF → Bool
  | .notReady => decide (v ≤ 1) | _ => true

/-- Read the allocated length of a record table. -/
def Tbl.size (s : Core) : Tbl → Nat
  | .E => s.E.size | .G => s.Gs.size | .C => s.C.size | .N => s.nodes.size

/-- Append a default record to a selected record table. -/
def Tbl.push (s : Core) : Tbl → Core
  | .E => { s with E := s.E.push default } | .G => { s with Gs := s.Gs.push default }
  | .C => { s with C := s.C.push default } | .N => { s with nodes := s.nodes.push default }

/-- Read a parameter selected by its typed field code. -/
def PF.get (P : Params) : PF → Nat

  | .N => P.N
  | .L => P.L
  | .G => P.G
  | .T => P.T
  | .theta => P.theta
  | .Be => P.elementBits
  | .Bg => P.groupBits

  | .De => P.elementSpacing
  | .Dg => P.groupSpacing
  | .KG => P.groupBudget
  | .KC => P.chunkBudget
  | .KR => P.reservationBudget
  | .a => P.a
  | .s => P.s | .beta => P.beta | .H => P.H

end fields

/-! ### Lists, paths and the optional records -/

/-- Encode a drain destination side by zero or one. -/
def sideN : Side → Nat
  | .left => 0 | .right => 1
/-- Decode zero as left and every other natural number as right. -/
def sideOfN : Nat → Side
  | 0 => .left | _ => .right

/-- The lists of the core: per node (children, table, in-tables, sides), per chunk (`cin`), and
the free-group stack. Each is seen as a list of pairs (`view`); the stack is stored reversed, so
that its head is the last element. -/
inductive LK | children | table | inTab | side | cin | freeG
  deriving DecidableEq, Repr

/-- View a selected core list as a list of pairs of natural numbers. -/
def LK.view (s : Core) (i : Nat) : LK → List (Nat × Nat)
  | .children => (s.nodes.getX i).children.map fun e => (e, 0)
  | .table => (s.nodes.getX i).table
  | .inTab => (s.nodes.getX i).inTables.map fun e => (e, 0)
  | .side => (s.nodes.getX i).side.map fun q => (q.1, sideN q.2)
  | .cin => (s.cin.getX i).map fun e => (e, 0)
  | .freeG => if i = 0 then s.freeG.reverse.map fun e => (e, 0) else []

/-- `l` is the view of some list of kind `k`. -/
def LK.valid (l : List (Nat × Nat)) : LK → Bool
  | .table => true
  | .side => l.all fun q => decide (q.2 ≤ 1)
  | _ => l.all fun q => q.2 == 0

/-- Replace a selected core list from its pair-list representation. -/
def LK.put (s : Core) (i : Nat) (l : List (Nat × Nat)) : LK → Core
  | .children => { s with nodes := s.nodes.modify i fun n => { n with children := l.map (·.1) } }
  | .table => { s with nodes := s.nodes.modify i fun n => { n with table := l } }
  | .inTab => { s with nodes := s.nodes.modify i fun n => { n with inTables := l.map (·.1) } }
  | .side => { s with nodes := s.nodes.modify i fun n => { n with side := l.map fun q => (q.1, sideOfN q.2) } }
  | .cin => { s with cin := s.cin.setX i (l.map (·.1)) }
  | .freeG => { s with freeG := (l.map (·.1)).reverse }

/-- The distance between consecutive records' lists in the machine array. The free-group stack
has a single record, so its stride is 0 and the compiled code does not depend on its capacity. -/
def LK.stride (κlcap : LK → Nat) : LK → Nat
  | .freeG => 0
  | k => κlcap k

/-- The record holding the list exists. -/
def LK.recOk (s : Core) (i : Nat) : LK → Bool
  | .children | .table | .inTab | .side => decide (i < s.nodes.size)
  | .cin => true
  | .freeG => decide (i = 0)

/-- The path row of chunk `c`. While the chunk list is being built, the row of the chunk being
prepared holds `prep.path` (so that committing it costs nothing). -/
def rowOf (s : Core) (c : Nat) : Array Nat :=
  match s.prep with
  | some pr => if c = pr.chunk then pr.path else s.path.getX c
  | none => s.path.getX c

/-- The program counter as five numbers. -/
def pcEnc : JobPc → Nat × Nat × Nat × Nat × Nat
  | .copy j => (0, j, 0, 0, 0)
  | .walk none => (1, 0, 0, 0, 0)
  | .walk (some v) => (2, v, 0, 0, 0)
  | .afterDrain v up => (3, v, up, 0, 0)
  | .fund v up src k => (4, v, up, src, k)

/-- Decode a reservation program counter, rejecting malformed payload combinations. -/
def pcDec (t a b c d : Nat) : Option JobPc :=
  match t with
  | 0 => if b = 0 ∧ c = 0 ∧ d = 0 then some (.copy a) else none
  | 1 => if a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 then some (.walk none) else none
  | 2 => if b = 0 ∧ c = 0 ∧ d = 0 then some (.walk (some a)) else none
  | 3 => if c = 0 ∧ d = 0 then some (.afterDrain a b) else none
  | 4 => some (.fund a b c d)
  | _ => none

/-- The optional records, read field by field (0 when absent). -/
inductive OF | prepOn | prepChunk | prepH | prepBelow | prepTag
  | jobOn | jobX | jobY | jobZ | jobT | jobA | jobB | jobC | jobD
  deriving DecidableEq, Repr

/-- Read a numeric field of the optional preparation or reservation-job state. -/
def OF.get (s : Core) : OF → Nat
  | .prepOn => b2n s.prep.isSome
  | .prepChunk => match s.prep with | some pr => pr.chunk | none => 0
  | .prepH => match s.prep with | some pr => pr.h | none => 0
  | .prepBelow => match s.prep with | some pr => pr.below | none => 0
  | .prepTag => match s.prep with | some pr => pr.tag | none => 0
  | .jobOn => b2n s.resJob.isSome
  | .jobX => match s.resJob with | some j => j.x | none => 0
  | .jobY => match s.resJob with | some j => j.y | none => 0
  | .jobZ => match s.resJob with | some j => j.z | none => 0
  | .jobT => match s.resJob with | some j => (pcEnc j.pc).1 | none => 0
  | .jobA => match s.resJob with | some j => (pcEnc j.pc).2.1 | none => 0
  | .jobB => match s.resJob with | some j => (pcEnc j.pc).2.2.1 | none => 0
  | .jobC => match s.resJob with | some j => (pcEnc j.pc).2.2.2.1 | none => 0
  | .jobD => match s.resJob with | some j => (pcEnc j.pc).2.2.2.2 | none => 0

/-- The capacities of the machine arrays: records of each table, plain arrays, lists (records
and elements per record), and the width of a path row. -/
structure Caps where
  /-- Allocated capacity of each record table. -/
  tbl : Tbl → Nat
  /-- Allocated capacity of each plain numeric array. -/
  arr : AF → Nat
  /-- Number of record rows available for each list kind. -/
  lrec : LK → Nat
  /-- Maximum length of a row for each list kind. -/
  lcap : LK → Nat
  /-- Allocated width of one ancestor-path row. -/
  pw : Nat

/-- The containing record table of a record field, when there is one. -/
def Fld.tbl? : Fld → Option Tbl
  | .e _ => some .E | .g _ => some .G | .c _ => some .C | .n _ => some .N | _ => none

/-- The capacity of a field's machine array (1 for a scalar). -/
def Fld.cap (κ : Caps) : Fld → Nat
  | .e _ => κ.tbl .E | .g _ => κ.tbl .G | .c _ => κ.tbl .C | .n _ => κ.tbl .N
  | .a k => κ.arr k | .s _ => 1

/-- The value of field `f` of record `i` (index ignored for a scalar). -/
def Fld.get (s : Core) (i : Nat) : Fld → Nat
  | .e k => k.get (s.E.getX i) | .g k => k.get (s.Gs.getX i) | .c k => k.get (s.C.getX i)
  | .n k => k.get (s.nodes.getX i) | .a k => (k.get s).getX i | .s k => k.get s

/-- Write field `f` of record `i`; `none` if the encoding cannot represent the result. -/
def Fld.set (κ : Caps) (s : Core) (i v : Nat) : Fld → Option Core
  | .e k => if i < s.E.size ∧ k.ok v = true then some { s with E := s.E.modify i (k.set · v) } else none
  | .g k => if i < s.Gs.size ∧ k.ok v = true then some { s with Gs := s.Gs.modify i (k.set · v) } else none
  | .c k => if i < s.C.size ∧ k.ok v = true then some { s with C := s.C.modify i (k.set · v) } else none
  | .n k => if i < s.nodes.size ∧ k.ok v = true then some { s with nodes := s.nodes.modify i (k.set · v) }
    else none
  | .a k => if i < κ.arr k then some (k.set s ((k.get s).setX i v)) else none
  | .s k => if i < 1 ∧ k.ok v = true then some (k.set s v) else none

/-- Replace list `k` of record `i` by `l`; `none` if not representable. -/
def LK.set (κ : Caps) (s : Core) (i : Nat) (l : List (Nat × Nat)) (k : LK) : Option Core :=
  if k.recOk s i = true ∧ k.valid l = true ∧ l.length ≤ κ.lcap k ∧ i < κ.lrec k then some (k.put s i l)
  else none

/-- The path row of `c` reads 0 everywhere. -/
def rowZero (κ : Caps) (s : Core) (c : Nat) : Prop := ∀ j < κ.pw, (rowOf s c).getX j = 0

instance (κ : Caps) (s : Core) (c : Nat) : Decidable (rowZero κ s c) := by
  unfold rowZero; infer_instance

/-- `c` is not the chunk being prepared. -/
def notPrep (s : Core) (c : Nat) : Prop :=
  match s.prep with
  | some pr => c ≠ pr.chunk
  | none => True

instance (s : Core) (c : Nat) : Decidable (notPrep s c) := by unfold notPrep; split <;> infer_instance

/-! ### Syntax -/

/-- Typed expressions reading core records, list rows, parameters and locals. -/
inductive Exp where
  | lit (n : Nat)
  | var (x : Reg)
  /-- Field `f` of record `i`. -/
  | rd (f : Fld) (i : Exp)
  /-- The number of records of a table. -/
  | size (t : Tbl)
  | prm (k : PF)
  | bin (op : BinOp) (a b : Exp)
  | un (op : UnOp) (a : Exp)
  /-- Component `snd` of element `j` of list `k` of record `i`. -/
  | lrd (k : LK) (snd : Bool) (i j : Exp)
  /-- The length of list `k` of record `i`. -/
  | llen (k : LK) (i : Exp)
  /-- Level `j` of the path of chunk `c`. -/
  | prd (c j : Exp)
  | opt (f : OF)
  deriving Repr, Inhabited

/-- Typed core statements with explicit failures, bounded loops and procedure calls. -/
inductive Stm where
  | skip
  | assign (x : Reg) (e : Exp)
  | wr (f : Fld) (i e : Exp)
  /-- Append a default record to table `t`; its index goes to `x`. -/
  | push (t : Tbl) (x : Reg)
  | seq (s t : Stm)
  | ite (c : Exp) (s t : Stm)
  | loop (x : Reg) (n : Exp) (b : Stm)
  | call (name : String) (params : List Reg) (body : Stm) (rets : List Reg) (args : List Exp)
      (dsts : List Reg)
  /-- A failed guard. -/
  | fail
  /-- A state the source program never reaches (an assertion of Level F). -/
  | bug
  | catch (s h : Stm)
  /-- Set component `snd` of element `j` of list `k` of record `i`. -/
  | lwr (k : LK) (snd : Bool) (i j e : Exp)
  /-- Append the element `(a, b)` to list `k` of record `i`. -/
  | lgrow (k : LK) (i a b : Exp)
  /-- Drop the last element of list `k` of record `i`. -/
  | lshrink (k : LK) (i : Exp)
  | lclear (k : LK) (i : Exp)
  /-- Set level `j` of the path of chunk `c`. -/
  | pwr (c j e : Exp)
  /-- Give the fresh chunk `c` the path `[NIL, …, NIL]` (its row already reads 0). -/
  | rowReset (c : Exp)
  /-- Start building the chain above chunk `c` (with `below = b`). -/
  | prepInit (c b : Exp)
  | prepSet (h b t : Exp)
  /-- Set level `j` of the path being built. -/
  | prepPath (j e : Exp)
  /-- The chain is built: its path becomes the chunk's path. -/
  | prepCommit
  | jobSet (x y z t a b c d : Exp)
  | jobClear
  | pcSet (t a b c d : Exp)
  deriving Repr, Inhabited

/-! ### Semantics on Level F -/

/-- Natural-number values assigned to local register names. -/
abbrev Loc := Reg → Nat

/-- Evaluate a typed expression, rejecting invalid reads and arithmetic. -/
def Exp.ev (κ : Caps) (s : Core) (L : Loc) : Exp → Option Nat
  | .lit n => some n
  | .var x => some (L x)
  | .rd f i => (i.ev κ s L).bind fun j => if j < f.cap κ then some (f.get s j) else none
  | .size t => some (t.size s)
  | .prm k => some (k.get s.P)
  | .bin op a b => (a.ev κ s L).bind fun x => (b.ev κ s L).bind fun y => op.eval x y
  | .un op a => (a.ev κ s L).map op.eval
  | .lrd k snd i j => (i.ev κ s L).bind fun x => (j.ev κ s L).bind fun y =>
      if x < κ.lrec k ∧ y < (k.view s x).length then
        some (if snd then ((k.view s x).getD y (0, 0)).2 else ((k.view s x).getD y (0, 0)).1)
      else none
  | .llen k i => (i.ev κ s L).bind fun x => if x < κ.lrec k then some (k.view s x).length else none
  | .prd c j => (c.ev κ s L).bind fun x => (j.ev κ s L).bind fun y =>
      if x < κ.tbl .C ∧ y < κ.pw then some ((rowOf s x).getX y) else none
  | .opt f => some (f.get s)

/-- Evaluate a list of arguments, failing when any argument is invalid. -/
def evList (κ : Caps) (s : Core) (L : Loc) (es : List Exp) : Option (List Nat) := es.mapM (·.ev κ s L)

/-- The number of machine steps to evaluate an expression (that of its compiled form). -/
def Exp.cost : Exp → Nat
  | .lit _ | .var _ => 1
  | .rd _ i => 1 + i.cost
  | .size _ | .prm _ => 2
  | .bin _ a b => 1 + a.cost + b.cost
  | .un _ a => 1 + a.cost
  | .lrd _ _ i j => 1 + (1 + (1 + i.cost + 1) + j.cost)
  | .llen _ i => 1 + i.cost
  | .prd c j => 1 + (1 + (1 + c.cost + 4) + j.cost)
  | .opt _ => 2

/-- Sum the static machine evaluation costs of a list of expressions. -/
def costList (es : List Exp) : Nat := (es.map Exp.cost).sum

/-- An outcome with the number of machine steps taken. -/
inductive Res where
  | ok (s : Core) (L : Loc) (c : Nat)
  | fail (s : Core) (L : Loc) (c : Nat)
  | bug

/-- Add a charged instruction cost to a normal or recoverable-failure outcome. -/
def Res.addCost (c : Nat) : Res → Res
  | .ok s L c' => .ok s L (c + c')
  | .fail s L c' => .fail s L (c + c')
  | .bug => .bug

/-- Continue a normal typed outcome, accumulating cost and propagating abnormal outcomes. -/
def Res.bind (r : Res) (g : Core → Loc → Res) : Res :=
  match r with
  | .ok s L c => (g s L).addCost c
  | r => r

/-- The steps of `push`: read the count, write it back plus one. -/
def pushCost : Nat := 8

/-- Execute a bounded typed loop with its index local and accumulated instruction cost. -/
def runForF (f : Core → Loc → Res) (x : Reg) : Nat → Nat → Core → Loc → Res
  | _, 0, s, L => .ok s L 0
  | k, n + 1, s, L => ((f s (OrderMaintenance.Machine.State.upd L x k)).addCost 1).bind (runForF f x (k + 1) n)

/-- Execute typed core statements with exact charged RAM cost and explicit abnormal outcomes. -/
def evalF (κ : Caps) : Stm → Core → Loc → Res
  | .skip, s, L => .ok s L 1
  | .assign x e, s, L =>
    match e.ev κ s L with
    | some v => .ok s (OrderMaintenance.Machine.State.upd L x v) (1 + e.cost)
    | none => .bug
  | .wr f i e, s, L =>
    match i.ev κ s L, e.ev κ s L with
    | some j, some v => match f.set κ s j v with
      | some s' => .ok s' L (1 + i.cost + e.cost)
      | none => .bug
    | _, _ => .bug
  | .push t x, s, L =>
    if t.size s < κ.tbl t then .ok (t.push s) (OrderMaintenance.Machine.State.upd L x (t.size s)) pushCost
    else .bug
  | .seq c d, s, L => (evalF κ c s L).bind (evalF κ d)
  | .ite c t f, s, L =>
    match c.ev κ s L with
    | some v => ((if v ≠ 0 then evalF κ t else evalF κ f) s L).addCost (1 + c.cost)
    | none => .bug
  | .loop x n b, s, L =>
    match n.ev κ s L with
    | some k => (runForF (evalF κ b) x 0 k s L).addCost (1 + n.cost)
    | none => .bug
  | .call _ ps b rs args ds, s, L =>
    match evList κ s L args with
    | some vs =>
      match evalF κ b s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ps vs) with
      | .ok s' L' c => .ok s' (OrderMaintenance.Machine.State.setLocs L ds (rs.map L'))
          (1 + costList args + ds.length + c)
      | .fail s' _ c => .fail s' L (1 + costList args + ds.length + c)
      | .bug => .bug
    | none => .bug
  | .fail, s, L => .fail s L 1
  | .bug, _, _ => .bug
  | .catch c h, s, L =>
    match evalF κ c s L with
    | .fail s' L' n => (evalF κ h s' L').addCost (1 + n)
    | .ok s' L' n => .ok s' L' (1 + n)
    | .bug => .bug
  | .lwr k snd i j e, s, L =>
    match i.ev κ s L, j.ev κ s L, e.ev κ s L with
    | some x, some y, some v =>
      if y < (k.view s x).length then
        match k.set κ s x ((k.view s x).set y
            (if snd then (((k.view s x).getD y (0, 0)).1, v) else (v, ((k.view s x).getD y (0, 0)).2))) with
        | some s' => .ok s' L (4 + i.cost + j.cost + e.cost)
        | none => .bug
      else .bug
    | _, _, _ => .bug
  | .lgrow k i a b, s, L =>
    match i.ev κ s L, a.ev κ s L, b.ev κ s L with
    | some x, some va, some vb =>
      match k.set κ s x (k.view s x ++ [(va, vb)]) with
      | some s' => .ok s' L (14 + 6 * i.cost + a.cost + b.cost)
      | none => .bug
    | _, _, _ => .bug
  | .lshrink k i, s, L =>
    match i.ev κ s L with
    | some x =>
      if (k.view s x).length ≠ 0 then
        match k.set κ s x (k.view s x).dropLast with
        | some s' => .ok s' L (4 + 2 * i.cost)
        | none => .bug
      else .bug
    | none => .bug
  | .lclear k i, s, L =>
    match i.ev κ s L with
    | some x =>
      match k.set κ s x [] with
      | some s' => .ok s' L (2 + i.cost)
      | none => .bug
    | none => .bug
  | .pwr c j e, s, L =>
    match c.ev κ s L, j.ev κ s L, e.ev κ s L with
    | some x, some y, some v =>
      if x < κ.tbl .C ∧ y < κ.pw ∧ notPrep s x then
        .ok { s with path := s.path.setX x ((s.path.getX x).setX y v) } L (7 + c.cost + j.cost + e.cost)
      else .bug
    | _, _, _ => .bug
  | .rowReset c, s, L =>
    match c.ev κ s L with
    | some x =>
      if x < κ.tbl .C ∧ rowZero κ s x ∧ notPrep s x ∧ s.P.H + 1 ≤ κ.pw then
        .ok { s with path := s.path.setX x (Array.replicate (s.P.H + 1) NIL) } L 1
      else .bug
    | none => .bug
  | .prepInit c b, s, L =>
    match c.ev κ s L, b.ev κ s L with
    | some x, some y =>
      if s.prep.isNone = true ∧ x < κ.tbl .C ∧ rowZero κ s x ∧ s.P.H + 1 ≤ κ.pw then
        .ok { s with prep := some { chunk := x, below := y, path := Array.replicate (s.P.H + 1) NIL } } L
          (16 + c.cost + b.cost)
      else .bug
    | _, _ => .bug
  | .prepSet h b t, s, L =>
    match s.prep, h.ev κ s L, b.ev κ s L, t.ev κ s L with
    | some pr, some vh, some vb, some vt =>
      .ok { s with prep := some { pr with h := vh, below := vb, tag := vt } } L (10 + h.cost + b.cost + t.cost)
    | _, _, _, _ => .bug
  | .prepPath j e, s, L =>
    match s.prep, j.ev κ s L, e.ev κ s L with
    | some pr, some y, some v =>
      if y < κ.pw then
        .ok { s with prep := some { pr with path := pr.path.setX y v } } L (9 + j.cost + e.cost)
      else .bug
    | _, _, _ => .bug
  | .prepCommit, s, L =>
    match s.prep with
    | some pr => .ok { s with path := s.path.setX pr.chunk pr.path, prep := none } L 15
    | none => .bug
  | .jobSet x y z t a b c d, s, L =>
    match evList κ s L [x, y, z, t, a, b, c, d] with
    | some [vx, vy, vz, vt, va, vb, vc, vd] =>
      match pcDec vt va vb vc vd with
      | some pc => .ok { s with resJob := some { x := vx, y := vy, z := vz, pc := pc } } L
          (28 + costList [x, y, z, t, a, b, c, d])
      | none => .bug
    | _ => .bug
  | .jobClear, s, L => .ok { s with resJob := none } L 27
  | .pcSet t a b c d, s, L =>
    match s.resJob, evList κ s L [t, a, b, c, d] with
    | some jb, some [vt, va, vb, vc, vd] =>
      match pcDec vt va vb vc vd with
      | some pc => .ok { s with resJob := some { jb with pc := pc } } L (16 + costList [t, a, b, c, d])
      | none => .bug
    | _, _ => .bug

end OrderMaintenance.Impl
