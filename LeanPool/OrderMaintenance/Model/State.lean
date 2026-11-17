/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module


/-!
# Level F: state

The functional model of the algorithm (`docs/LEAN.md` §4), a transliteration of the Python
prototype (`prototype/core.py`, `pq.py`, `top_wbbt.py`, `wrapper.py`). It is executable and is
tested against the prototype by trace replay (`OrderMaintenance/Test/Replay.lean`).

Conventions:
* Records live in arrays and refer to each other by index. Index 0 is a dummy and `NIL = 0`, so
  every real index is positive (the prototype uses 0-based indices and `NIL = -1`).
* Code runs in `EStateM Err Core`. A failed guard throws `Err.guard` and *keeps* the state
  reached, exactly like the prototype's exceptions; the caller then runs FALLBACK, which
  rebuilds everything from the element list. `Err.bug` marks a situation in which the prototype
  would crash (an assertion, a missing key); the tests check that it never occurs.
* Instrumentation of the prototype is omitted.
-/


@[expose] public section

namespace OrderMaintenance.Model

/-- The zero index reserved for absent pointers and dummy array entries. -/
abbrev NIL : Nat := 0

/-- Parameters of one core (`prototype/core.py` `Params`, plus the top structure's). -/
structure Params where
  /-- Capacity parameter for the core. -/
  N : Nat
  /-- Logarithmic scale used in the capacity formulas. -/
  L : Nat
  /-- Element threshold for beginning a group split. -/
  G : Nat
  /-- Element threshold for beginning a chunk split. -/
  T : Nat
  /-- Quiet-chunk size threshold for entering the priority queue. -/
  theta : Nat
  /-- Bit width of element labels. -/
  elementBits : Nat
  /-- Bit width of group labels. -/
  groupBits : Nat
  /-- Spacing used when appending an element label. -/
  elementSpacing : Nat
  /-- Spacing used when appending a group label. -/
  groupSpacing : Nat
  /-- Group split steps scheduled per insertion. -/
  groupBudget : Nat
  /-- Chunk split steps scheduled per insertion. -/
  chunkBudget : Nat
  /-- Reservation steps scheduled per insertion. -/
  reservationBudget : Nat
  /-- Tree balance parameter controlling child capacity. -/
  a : Nat
  /-- Number of tree sweep steps scheduled at each visit. -/
  s : Nat
  /-- Bit width of one level of a chunk’s composite tag. -/
  beta : Nat
  /-- Maximum height of the top tree. -/
  H : Nat
  deriving Repr, Inhabited

/-- Lifecycle of a group or chunk during incremental splitting. -/
inductive St where
  | quiet | overflow | splitting | dead
  deriving DecidableEq, Repr, Inhabited

/-- An allocated element, including its order label and external handle. -/
structure Elem where
  /-- Next element index in the core list. -/
  next : Nat := NIL
  /-- Previous element index in the core list. -/
  prev : Nat := NIL
  /-- Containing group index. -/
  grp : Nat := NIL
  /-- Order label within the containing group. -/
  lab : Nat := 0
  /-- Whether this element represents a live external handle. -/
  live : Bool := true
  /-- External handle represented by this element. -/
  h : Nat := 0
  deriving Repr, Inhabited

/-- A labelled run of elements and its incremental split state. -/
structure Group where
  /-- Next group index in the core list. -/
  next : Nat := NIL
  /-- Previous group index in the core list. -/
  prev : Nat := NIL
  /-- First element index, or the absent-pointer sentinel. -/
  first : Nat := NIL
  /-- Last element index, or the absent-pointer sentinel. -/
  last : Nat := NIL
  /-- Containing chunk index. -/
  chk : Nat := NIL
  /-- Order label within the containing chunk. -/
  lab : Nat := 0
  /-- Number of elements in the group. -/
  size : Nat := 0
  /-- Current incremental split state. -/
  st : St := .quiet
  /-- Source group of an overflow sibling. -/
  src : Nat := NIL
  /-- Left overflow sibling of a splitting group. -/
  l : Nat := NIL
  /-- Right overflow sibling of a splitting group. -/
  r : Nat := NIL
  /-- Whether this group record is currently allocated. -/
  alive : Bool := true
  deriving Repr, Inhabited

/-- A tagged run of groups and its incremental split state. -/
structure Chunk where
  /-- Next chunk index in the core list. -/
  next : Nat := NIL
  /-- Previous chunk index in the core list. -/
  prev : Nat := NIL
  /-- First group index, or the absent-pointer sentinel. -/
  first : Nat := NIL
  /-- Last group index, or the absent-pointer sentinel. -/
  last : Nat := NIL
  /-- Number of elements in the chunk. -/
  size : Nat := 0
  /-- Current incremental split state. -/
  st : St := .quiet
  /-- Source chunk of an overflow sibling. -/
  src : Nat := NIL
  /-- Left overflow sibling of a splitting chunk. -/
  l : Nat := NIL
  /-- Right overflow sibling of a splitting chunk. -/
  r : Nat := NIL
  /-- Order tag assembled from the top-tree path. -/
  tag : Nat := 0
  /-- Whether this chunk record is live rather than a tombstone. -/
  alive : Bool := true
  deriving Repr, Inhabited

/-- The side of a split receiving a table entry. -/
inductive Side where
  | left | right
  deriving DecidableEq, Repr, Inhabited

/-- A node of the top tree (`prototype/top_wbbt.py` `Node`). The prototype's `lab` dictionary
and `order` list are merged into `table`: the entries with their labels, in label order. -/
structure Node where
  /-- Height above chunks, which occupy height zero. -/
  height : Nat := 0
  /-- Parent in the live top tree. -/
  livePar : Nat := NIL
  /-- Ordered live child indices. -/
  children : List Nat := []
  /-- Weight used by the tree balance and drain rules. -/
  weight : Nat := 0
  /-- Entries and labels in increasing label order. -/
  table : List (Nat × Nat) := []
  /-- Tables in which this node occurs as an entry. -/
  inTables : List Nat := []
  /-- First chunk in the node’s represented range. -/
  first : Nat := NIL
  /-- Last chunk in the node’s represented range. -/
  last : Nat := NIL
  /-- Whether this node is undergoing a drain. -/
  draining : Bool := false
  /-- Left target node of an active drain. -/
  t1 : Nat := NIL
  /-- Right target node of an active drain. -/
  t2 : Nat := NIL
  /-- Destination side assigned to each entry during a drain. -/
  side : List (Nat × Side) := []
  /-- Source of this node when it is an overflow drain target. -/
  overflowOf : Nat := NIL
  /-- Whether this node record is in use. -/
  alive : Bool := true
  deriving Repr, Inhabited

/-- The program counter of a top-structure job (`top_wbbt.py` `_job`, a Python generator).
Each constructor is a point where the generator is suspended. -/
inductive JobPc where
  /-- Before copying level `j` of `x`'s path. -/
  | copy (j : Nat)
  /-- At the head of the upward walk; `none` means "start from `lpar[y]`". -/
  | walk (v : Option Nat)
  /-- Right after `_start_drain(v)` (its `yield`). -/
  | afterDrain (v up : Nat)
  /-- Inside the sweep funding loop of `v`, after `k` sweep steps. -/
  | fund (v up src k : Nat)
  deriving Repr, Inhabited

/-- A suspended reservation job splitting a chunk into two replacements. -/
structure Job where
  /-- Source chunk being split. -/
  x : Nat
  /-- Left replacement chunk. -/
  y : Nat
  /-- Right replacement chunk. -/
  z : Nat
  /-- Suspended position of the reservation computation. -/
  pc : JobPc
  deriving Repr, Inhabited

/-- Deferred construction of the top structure (`init_steps`, a Python generator). -/
structure Prep where
  /-- Initial chunk whose ancestor chain is being prepared. -/
  chunk : Nat
  /-- The next height to build (starts at 1; `H + 1` means "finish"). -/
  h : Nat := 1
  below : Nat
  /-- Composite chunk tag accumulated during preparation. -/
  tag : Nat := 0
  /-- Ancestor path accumulated during preparation. -/
  path : Array Nat
  deriving Repr, Inhabited

/-- One insert-only core with its priority queue and top structure. -/
structure Core where
  /-- Parameters governing this core’s capacities and scheduled work. -/
  P : Params
  /-- Element records, including a dummy record at index zero. -/
  E : Array Elem := #[default]
  /-- Group records, including a dummy record at index zero. -/
  Gs : Array Group := #[default]
  /-- Chunk records, including a dummy record at index zero. -/
  C : Array Chunk := #[default]
  /-- Reusable group indices outside the live group list. -/
  freeG : List Nat := []
  /-- Number of elements inserted into this core. -/
  count : Nat := 0
  /-- Head of the element list, including the dead sentinel. -/
  head : Nat := NIL
  /-- Last allocated element in list order. -/
  tail : Nat := NIL
  /-- Head of the live group list. -/
  firstGroup : Nat := NIL
  /-- Head of the allocated chunk list. -/
  firstChunk : Nat := NIL
  /-- Whether deferred top-tree preparation is complete. -/
  ready : Bool := true
  /-- Suspended top-tree preparation, if any. -/
  prep : Option Prep := none
  /-- Suspended chunk reservation job, if any. -/
  resJob : Option Job := none
  /-- Number of fallback rebuilds performed. -/
  fallbacks : Nat := 0
  -- priority queue (`pq.py`): buckets by size, each a doubly linked list of chunks, pushed and
  -- popped at the head; non-empty buckets form a sorted doubly linked list
  /-- Head chunk index of each size bucket. -/
  pqHead : Array Nat := #[]
  /-- Next queued chunk within the same size bucket. -/
  pqNext : Array Nat := #[]
  /-- Previous queued chunk within the same size bucket. -/
  pqPrev : Array Nat := #[]
  /-- The bucket of a chunk in the queue, 0 if absent (sizes in the queue exceed `theta ≥ 1`). -/
  pqWhere : Array Nat := #[]
  /-- Next nonempty size bucket. -/
  nbNext : Array Nat := #[]
  /-- Previous nonempty size bucket. -/
  nbPrev : Array Nat := #[]
  /-- Largest and smallest non-empty bucket, 0 if the queue is empty. -/
  pqHi : Nat := 0
  /-- Smallest nonempty bucket, or zero for an empty queue. -/
  pqLo : Nat := 0
  -- top structure (`top_wbbt.py`)
  /-- Allocated top-tree node records. -/
  nodes : Array Node := #[default]
  /-- Top-tree ancestor paths indexed by chunk. -/
  path : Array (Array Nat) := #[]
  /-- Containing-table lists for chunk entries. -/
  cin : Array (List Nat) := #[]
  /-- Live parents of chunks at height zero. -/
  lpar : Array Nat := #[]
  deriving Inhabited

/-- Guard failures permit rebuilding; bug failures represent invalid program states. -/
inductive Err where
  | guard (msg : String)
  | bug (msg : String)
  deriving Repr, Inhabited

/-- Stateful core computations that retain the reached state on failure. -/
abbrev CM := EStateM Err Core

/-! ### Arrays as total maps -/

/-- Write `v` at `i`, extending the array with defaults if needed. -/
def _root_.Array.setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) : Array α :=
  if i < a.size then a.set! i v else (a ++ Array.replicate (i - a.size) default).push v

/-- Read an array as a total map, returning the default value outside its bounds. -/
def _root_.Array.getX {α : Type} [Inhabited α] (a : Array α) (i : Nat) : α := a.getD i default

/-! ### Accessors -/

/-- Raise a recoverable guard failure without discarding the current core. -/
def guard {α : Type} (msg : String) : CM α := throw (.guard msg)
/-- Raise an internal failure indicating an invalid program state. -/
def bug {α : Type} (msg : String) : CM α := throw (.bug msg)

/-- Fail the guard `msg` unless `ok`. -/
def require (ok : Bool) (msg : String) : CM Unit := if ok then pure () else guard msg

/-- Read an element record, with the default record for an absent index. -/
@[inline] def getE (i : Nat) : CM Elem := return (← get).E.getX i
/-- Read a group record, with the default record for an absent index. -/
@[inline] def getG (i : Nat) : CM Group := return (← get).Gs.getX i
/-- Read a chunk record, with the default record for an absent index. -/
@[inline] def getC (i : Nat) : CM Chunk := return (← get).C.getX i
/-- Read a top-tree node, with the default record for an absent index. -/
@[inline] def getN (i : Nat) : CM Node := return (← get).nodes.getX i
/-- Read the parameters of the current core. -/
@[inline] def getP : CM Params := return (← get).P

/-- Modify an existing element record without extending the array. -/
@[inline] def modE (i : Nat) (f : Elem → Elem) : CM Unit :=
  modify fun s => { s with E := s.E.modify i f }
/-- Modify an existing group record without extending the array. -/
@[inline] def modG (i : Nat) (f : Group → Group) : CM Unit :=
  modify fun s => { s with Gs := s.Gs.modify i f }
/-- Modify an existing chunk record without extending the array. -/
@[inline] def modC (i : Nat) (f : Chunk → Chunk) : CM Unit :=
  modify fun s => { s with C := s.C.modify i f }
/-- Modify an existing top-tree node without extending the array. -/
@[inline] def modN (i : Nat) (f : Node → Node) : CM Unit :=
  modify fun s => { s with nodes := s.nodes.modify i f }

/-! ### Small list helpers -/

/-- The position of `x` in `l`, if present. -/
def _root_.List.idx? (l : List Nat) (x : Nat) : Option Nat := l.findIdx? (· == x)

/-- Replace the first occurrence of `x` by the list `ys`. -/
def _root_.List.replace1 (l : List Nat) (x : Nat) (ys : List Nat) : List Nat :=
  match l with
  | [] => []
  | a :: t => if a = x then ys ++ t else a :: t.replace1 x ys

/-- Remove the first occurrence of `x`. -/
def _root_.List.remove1 (l : List Nat) (x : Nat) : List Nat := l.erase x

/-- Read the value at the first occurrence of a key in an association list. -/
def lookup {β : Type} (l : List (Nat × β)) (k : Nat) : Option β := (l.find? (·.1 == k)).map (·.2)

/-- Look up the label assigned to an entry in a node table. -/
def Node.lab? (n : Node) (e : Nat) : Option Nat := lookup n.table e
/-- List the entries of a node table in their stored label order. -/
def Node.order (n : Node) : List Nat := n.table.map (·.1)

end OrderMaintenance.Model
