/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Model.Top


/-!
# Level F: the insert-only core (`prototype/core.py`)

Elements → groups → chunks, guarded label writes, group and chunk splits, the reservation
process, and FALLBACK.
-/


@[expose] public section

namespace OrderMaintenance.Model

/-! ### Allocation -/

/-- Append an element with the given group, label and external handle. -/
def newElem (g lab h : Nat) : CM Nat :=
  modifyGet fun s => (s.E.size, { s with E := s.E.push { grp := g, lab := lab, h := h } })

/-- Allocate a group in a chunk, reusing the free list when possible. -/
def newGroup (c : Nat) : CM Nat :=
  modifyGet fun s => match s.freeG with
    | i :: rest => (i, { s with freeG := rest, Gs := s.Gs.set! i { chk := c } })
    | [] => (s.Gs.size, { s with Gs := s.Gs.push { chk := c } })

/-- Chunks are never freed: emptied ones stay as DEAD tombstones until the next rebuild. -/
def newChunk : CM Nat :=
  modifyGet fun s => (s.C.size, { s with C := s.C.push {} })

/-! ### Label primitives (guarded) -/

/-- Choose a midpoint label, failing if there is no strictly intermediate integer. -/
def between (a b : Nat) (why : String) : CM Nat := do
  if a + 1 ≥ b then guard why
  return (a + b) / 2

/-- Choose a label one spacing after its predecessor within the given bit width. -/
def after (a D B : Nat) (why : String) : CM Nat := do
  let v := a + D
  if v ≥ 1 <<< B || v ≤ a then guard why
  return v

/-- Choose a label one positive spacing before its successor. -/
def before (b D : Nat) (why : String) : CM Nat := do
  if b < D || D == 0 then guard why
  return b - D

/-! ### Queries -/

/-- Read an element’s lexicographic chunk, group and element order labels. -/
def key (e : Nat) : CM (Nat × Nat × Nat) := do
  let x ← getE e
  let g ← getG x.grp
  return ((← getC g.chk).tag, g.lab, x.lab)

/-- Compare chunk, group and element labels lexicographically. -/
def keyLt : Nat × Nat × Nat → Nat × Nat × Nat → Bool
  | (a, b, c), (a', b', c') => a < a' || (a == a' && (b < b' || (b == b' && c < c')))

/-- Compare the order labels of two element indices. -/
def order (x y : Nat) : CM Bool := return keyLt (← key x) (← key y)

/-- Mark an element deleted while retaining its linked-list position. -/
def markDead (x : Nat) : CM Unit := modE x fun e => { e with live := false }

/-! ### Chunk sizes -/

/-- Change a chunk’s element count by one and adjust its quiet queue entry. -/
def chunkSize (c : Nat) (inc : Bool) : CM Unit := do
  let C ← getC c
  let new := if inc then C.size + 1 else C.size - 1
  modC c fun C => { C with size := new }
  if C.st == .quiet then pqAdjust c C.size new

/-! ### Element insertion -/

/-- Link a new element `y` (the next free index) with label `lab` and handle `h` right after
`x`, in `x`'s group. -/
def linkElem (s : Core) (x y lab h : Nat) : Core :=
  let ex := s.E.getX x
  let g := ex.grp
  let E1 := s.E.push { grp := g, lab := lab, h := h, prev := x, next := ex.next }
  let E2 := if ex.next != NIL then E1.modify ex.next (fun e => { e with prev := y }) else E1
  { s with
    E := E2.modify x (fun e => { e with next := y })
    tail := if s.tail == x then y else s.tail
    Gs := s.Gs.modify g (fun G => { G with last := if G.last == x then y else G.last,
                                            size := G.size + 1 })
    count := s.count + 1 }

/-- Insert after an element, choosing a guarded label before mutating the list. -/
def insertElem (x h : Nat) : CM Nat := do
  let P ← getP
  let ex ← getE x
  let g := ex.grp
  let G ← getG g
  let lab ←
    if x == G.last then
      after ex.lab P.elementSpacing P.elementBits "elem: no room after last"
    else between ex.lab (← getE ex.next).lab "elem: no room between"
  -- mutate (the chunk's size is updated by `background`, so that nothing after the
  -- mutation can fail a guard: the caller retries the insertion only on such a failure)
  let y := (← get).E.size
  modify (linkElem · x y lab h)
  return y

/-! ### Group splits -/

/-- Link new groups `gl` (label `labL`) and `gr` (label `labR`) right before and after `g`, in
the group list and in `g`'s chunk, as the overflow siblings of `g`. -/
def linkGroupPair (s : Core) (g gl gr labL labR : Nat) : Core :=
  let G := s.Gs.getX g
  let c := G.chk
  let C := s.C.getX c
  let A0 := s.Gs.modify gl fun X =>
    { X with lab := labL, st := .overflow, src := g, prev := G.prev, next := g }
  let A1 := if G.prev != NIL then A0.modify G.prev (fun X => { X with next := gl }) else A0
  let A2 := A1.modify gr fun X =>
    { X with lab := labR, st := .overflow, src := g, prev := g, next := G.next }
  let A3 := if G.next != NIL then A2.modify G.next (fun X => { X with prev := gr }) else A2
  let C1 := if C.first == g then s.C.modify c (fun X => { X with first := gl }) else s.C
  { s with
    Gs := A3.modify g fun X => { X with prev := gl, next := gr, st := .splitting, l := gl, r := gr }
    C := if C.last == g then C1.modify c (fun X => { X with last := gr }) else C1
    firstGroup := if G.prev != NIL then s.firstGroup else gl }

/-- Unlink group `g` from the group list and from its chunk, and free it. -/
def unlinkGroup (s : Core) (g : Nat) : Core :=
  let G := s.Gs.getX g
  let c := G.chk
  let C := s.C.getX c
  let A1 := if G.prev != NIL then s.Gs.modify G.prev (fun X => { X with next := G.next }) else s.Gs
  let A2 := if G.next != NIL then A1.modify G.next (fun X => { X with prev := G.prev }) else A1
  { s with
    Gs := A2.modify g fun X => { X with alive := false, next := NIL, prev := NIL }
    C := if C.first == g && C.last == g then
      s.C.modify c (fun X => { X with first := NIL, last := NIL })
      else if C.first == g then s.C.modify c (fun X => { X with first := G.next })
      else if C.last == g then s.C.modify c (fun X => { X with last := G.prev })
      else s.C
    firstGroup := if G.prev != NIL then s.firstGroup else G.next
    freeG := g :: s.freeG }

/-- Move element `e`, the first of group `g`, to the end of group `gl` with label `lab`. -/
def moveFirstLeft (s : Core) (g gl e lab : Nat) : Core :=
  let G := s.Gs.getX g
  let A1 := s.Gs.modify g fun X =>
    if G.first == G.last then { X with first := NIL, last := NIL }
    else { X with first := (s.E.getX e).next }
  { s with
    Gs := A1.modify gl fun X => { X with first := if X.first == NIL then e else X.first, last := e }
    E := s.E.modify e fun X => { X with grp := gl, lab := lab } }

/-- Move element `e`, the last of group `g`, to the front of group `gr` with label `lab`. -/
def moveLastRight (s : Core) (g gr e lab : Nat) : Core :=
  let G := s.Gs.getX g
  let A1 := s.Gs.modify g fun X =>
    if G.first == G.last then { X with first := NIL, last := NIL }
    else { X with last := (s.E.getX e).prev }
  { s with
    Gs := A1.modify gr fun X => { X with last := if X.first == NIL then e else X.last, first := e }
    E := s.E.modify e fun X => { X with grp := gr, lab := lab } }

/-- A label for a new group right before `g` in its chunk. -/
def labBefore (g : Nat) : CM Nat := do
  let P ← getP
  let G ← getG g
  let C ← getC G.chk
  if g == C.first then before G.lab P.groupSpacing "group: no room before first"
  else between (← getG G.prev).lab G.lab "group: no room left"

/-- A label for a new group right after `g` in its chunk. -/
def labAfter (g : Nat) : CM Nat := do
  let P ← getP
  let G ← getG g
  let C ← getC G.chk
  if g == C.last then after G.lab P.groupSpacing P.groupBits "group: no room after last"
  else between G.lab (← getG G.next).lab "group: no room right"

/-- Allocate the overflow siblings and begin incrementally splitting a group. -/
def startGroupSplit (g : Nat) : CM Unit := do
  let G ← getG g
  require (g != NIL && g < (← get).Gs.size && G.alive) "group: split of a dead group"
  let labL ← labBefore g
  let labR ← labAfter g
  -- mutate
  let gl ← newGroup G.chk
  let gr ← newGroup G.chk
  modify (linkGroupPair · g gl gr labL labR)

/-- Unlink and free group `g`, which must be alive and empty. -/
def unlinkStep (g : Nat) : CM Unit := do
  let G ← getG g
  require (g != NIL && g < (← get).Gs.size && G.alive && G.first == NIL)
    "group split: removing a dead or non-empty group"
  modify (unlinkGroup · g)

/-- Remove an empty group and release its overflow siblings to the quiet state. -/
def removeGroup (g : Nat) : CM Unit := do
  unlinkStep g
  let P ← getP
  let G ← getG g     -- `l` and `r` are not changed by the unlink
  let mut quiet : List Nat := []
  for s in [G.l, G.r] do
    let S ← getG s
    if S.st == .overflow && S.src == g then
      modG s fun X => { X with st := .quiet, src := NIL }
      quiet := quiet ++ [s]
  for s in quiet do
    if (← getG s).size ≥ P.G then startGroupSplit s

/-- Move one element of the splitting group `g` (alive, non-empty) to its lighter sibling.
Returns the sibling. -/
def moveElem (g : Nat) : CM Nat := do
  let P ← getP
  let G ← getG g
  require (g != NIL && g < (← get).Gs.size && G.alive && G.first != NIL)
    "group split: moving out of a dead or empty group"
  let gl := G.l
  let gr := G.r
  let Lg ← getG gl
  let Rg ← getG gr
  let center := 1 <<< (P.elementBits - 1)
  if Lg.size ≤ Rg.size then do
    require (Lg.next == g) "group split: left sibling not adjacent"
    let lab ← if Lg.first == NIL then pure center
      else after (← getE Lg.last).lab P.elementSpacing P.elementBits "elem: push-back room"
    modify (moveFirstLeft · g gl G.first lab)
    pure gl
  else do
    require (Rg.prev == g) "group split: right sibling not adjacent"
    let lab ← if Rg.first == NIL then pure center
      else before (← getE Rg.first).lab P.elementSpacing "elem: push-front room"
    modify (moveLastRight · g gr G.last lab)
    pure gr

/-- One move of a splitting group. Returns `false` once `g` is gone. -/
def groupSplitStep (g : Nat) : CM Bool := do
  let G ← getG g
  require (g != NIL && g < (← get).Gs.size && G.alive) "group split: dead group"
  if G.first == NIL then
    removeGroup g
    return false
  let dst ← moveElem g
  modG g fun X => { X with size := X.size - 1 }
  modG dst fun X => { X with size := X.size + 1 }
  let D ← getG dst
  if D.chk != G.chk then
    -- unreachable under invariant F (family moves)
    chunkSize D.chk true
    chunkSize G.chk false
  return true

/-- Perform at most the configured number of steps of a group split. -/
def driveGroupFrom (s : Nat) : CM Unit := do
  for _ in List.range ((← getP).groupBudget) do
    if !(← groupSplitStep s) then return

/-- Advance the split of a group or of its source if it is an overflow sibling. -/
def driveGroup (g : Nat) : CM Unit := do
  let G ← getG g
  match G.st with
  | .splitting => driveGroupFrom g
  | .overflow => driveGroupFrom G.src
  | _ => pure ()

/-! ### Chunk splits -/

/-- The candidate unit at the left/right end of chunk `x`: the family `(gl, g, gr)` of a
splitting group if the end group is its overflow sibling on that side, else the end group. -/
def unitCand (s : Core) (x : Nat) (left : Bool) : List Nat :=
  let X := s.C.getX x
  let g0 := if left then X.first else X.last
  let G0 := s.Gs.getX g0
  if G0.st != .overflow then [g0]
  else
    let S := s.Gs.getX G0.src
    if left && S.l == g0 then [g0, G0.src, S.r]
    else if !left && S.r == g0 then [S.l, G0.src, g0]
    else [g0]

/-- A family unit must lie in chunk `x`, as consecutive groups (the prototype checked the
chunk of all members but the first). -/
def unitOK (s : Core) (x : Nat) (u : List Nat) : Bool :=
  u.all (fun a => a != NIL && (s.Gs.getX a).chk == x) &&
    (u.zip u.tail).all (fun p => (s.Gs.getX p.1).next == p.2)

/-- The groups that one chunk-split move takes from the left/right end of chunk `x`: a whole
family `(gl, g, gr)` of a splitting group, or one group (invariant F). -/
def unit (x : Nat) (left : Bool) : CM (List Nat) := do
  let s ← get
  let u := unitCand s x left
  if u.length == 1 then return u
  require (unitOK s x u) "chunk split: family not contiguous in chunk"
  return u

/-- Leave an empty chunk as a tombstone and release its overflow siblings. -/
def removeChunk (x : Nat) : CM Unit := do
  modC x fun X => { X with st := .dead }
  let X ← getC x
  for s in [X.l, X.r] do
    let S ← getC s
    if S.st == .overflow && S.src == x then
      modC s fun X => { X with st := .quiet, src := NIL }
      pqEnterIfAbove s

/-- Labels for `k` groups appended after a group labelled `prev` (`none`: the receiving chunk
is empty; start at the centre). -/
def pushBackLabs (center D B : Nat) : Option Nat → Nat → CM (List Nat)
  | _, 0 => pure []
  | prev, k + 1 => do
    let l ← match prev with
      | none => pure center
      | some p => after p D B "group: push-back room"
    return l :: (← pushBackLabs center D B (some l) k)

/-- Labels for `k` groups prepended before a group labelled `nxt`, in list order. -/
def pushFrontLabs (center D : Nat) : Option Nat → Nat → CM (List Nat)
  | _, 0 => pure []
  | nxt, k + 1 => do
    let l ← match nxt with
      | none => pure center
      | some n => before n D "group: push-front room"
    return (← pushFrontLabs center D (some l) k) ++ [l]

/-- Move the groups `u`, a prefix of chunk `x`, to the end of chunk `y`, with labels `labs`. -/
def moveGroupsLeft (s : Core) (x y : Nat) (u labs : List Nat) : Core :=
  let X := s.C.getX x
  let first := u.headD NIL
  let last := u.getLastD NIL
  let C1 := s.C.modify x fun Z =>
    if X.last == last then { Z with first := NIL, last := NIL }
    else { Z with first := (s.Gs.getX last).next }
  { s with
    C := C1.modify y fun Z => {
      Z with
      first := if Z.first == NIL then first else Z.first,
      last := last
    }
    Gs := (u.zip labs).foldl
      (fun a p => a.modify p.1 fun G => { G with chk := y, lab := p.2 }) s.Gs }

/-- Move the groups `u`, a suffix of chunk `x`, to the front of chunk `z`, with labels `labs`. -/
def moveGroupsRight (s : Core) (x z : Nat) (u labs : List Nat) : Core :=
  let X := s.C.getX x
  let first := u.headD NIL
  let last := u.getLastD NIL
  let C1 := s.C.modify x fun Z =>
    if X.first == first then { Z with first := NIL, last := NIL }
    else { Z with last := (s.Gs.getX first).prev }
  { s with
    C := C1.modify z fun Z => {
      Z with
      last := if Z.first == NIL then last else Z.last,
      first := first
    }
    Gs := (u.zip labs).foldl
      (fun a p => a.modify p.1 fun G => { G with chk := z, lab := p.2 }) s.Gs }

/-- Chunk sizes after moving the groups `u` from `x` to `dst`. -/
def moveSizes (x dst : Nat) (u : List Nat) : CM Unit := do
  let s ← get
  let moved := (u.map fun g => (s.Gs.getX g).size).sum
  -- x is SPLITTING and dst is OVERFLOW: neither is in the priority queue
  modC x fun X => { X with size := X.size - moved }
  modC dst fun X => { X with size := X.size + moved }

/-- One chunk-split move of chunk `x` (non-empty) towards its sibling on the `left` (right):
the unit at that end of `x` moves to the end (front) of the sibling, with guarded labels.
Returns the sibling and the unit. -/
def moveUnit (x : Nat) (left : Bool) : CM (Nat × List Nat) := do
  let P ← getP
  let X ← getC x
  require (X.first != NIL) "chunk split: moving out of an empty chunk"
  let center := 1 <<< (P.groupBits - 1)
  let u ← unit x left
  if left then
    let y := X.l
    let Y ← getC y
    require (Y.next == x) "chunk split: left sibling not adjacent"
    let yl := (← getG Y.last).lab
    let labs ← pushBackLabs center P.groupSpacing P.groupBits (if Y.first == NIL then none else
      some yl) u.length
    modify (moveGroupsLeft · x y u labs)
    return (y, u)
  else
    let z := X.r
    let Z ← getC z
    require (Z.prev == x) "chunk split: right sibling not adjacent"
    let zf := (← getG Z.first).lab
    let labs ← pushFrontLabs center P.groupSpacing (if Z.first == NIL then none else some zf)
      u.length
    modify (moveGroupsRight · x z u labs)
    return (z, u)

/-- Move one end unit into an overflow sibling, or finish an empty chunk split. -/
def chunkSplitStep (x : Nat) : CM Bool := do
  let X ← getC x
  if X.first == NIL then
    removeChunk x
    return false
  let left := (← getC X.l).size ≤ (← getC X.r).size
  let (dst, u) ← moveUnit x left
  moveSizes x dst u
  return true

/-- Perform at most the configured number of steps of a chunk split. -/
def driveChunkFrom (s : Nat) : CM Unit := do
  for _ in List.range ((← getP).chunkBudget) do
    if !(← chunkSplitStep s) then return

/-- Advance the split of a chunk or of its source if it is an overflow sibling. -/
def driveChunk (c : Nat) : CM Unit := do
  let C ← getC c
  match C.st with
  | .splitting => driveChunkFrom c
  | .overflow => driveChunkFrom C.src
  | _ => pure ()

/-! ### Reservation -/

/-- Link new chunks `y` and `z` right before and after `x` in the chunk list. -/
def linkChunkPair (s : Core) (x y z : Nat) : Core :=
  let X := s.C.getX x
  let C1 := s.C.modify y (fun C => { C with prev := X.prev, next := x })
  let C2 := if X.prev != NIL then C1.modify X.prev (fun C => { C with next := y }) else C1
  let C3 := C2.modify z (fun C => { C with prev := x, next := X.next })
  let C4 := if X.next != NIL then C3.modify X.next (fun C => { C with prev := z }) else C3
  { s with
    C := C4.modify x (fun C => { C with prev := y, next := z })
    firstChunk := if X.prev != NIL then s.firstChunk else y }

/-- The split's bookkeeping: chunk states and siblings, and the running job. -/
def markSplit (x y z : Nat) (job : Job) : CM Unit := do
  modC x fun C => { C with st := .splitting, l := y, r := z }
  modC y fun C => { C with st := .overflow, src := x }
  modC z fun C => { C with st := .overflow, src := x }
  modify fun s => { s with resJob := some job }

/-- Split chunk `x` (just popped from the queue): link two new chunks around it, give them tags
(guarded) and start the top structure's insertion job. -/
def splitChunkStart (x : Nat) : CM Unit := do
  require (x != NIL && x < (← get).C.size) "reservation: invalid chunk"
  let y ← newChunk
  let z ← newChunk
  modify (linkChunkPair · x y z)
  let job ← insertAround x y z
  markSplit x y z job

/-- Spend a bounded number of steps on the largest queued chunk and its top-tree job. -/
def reservation (k : Nat) : CM Unit := do
  for _ in List.range (k) do
    match (← get).resJob with
    | none =>
      if ← pqEmpty then return
      splitChunkStart (← pqPopMax)
    | some job =>
      let r ← jobStep job
      modify fun s => { s with resJob := r }

/-! ### FALLBACK -/

/-- The element list, from the sentinel. -/
def elements : CM (List Nat) := do
  let s ← get
  return walkList (fun e => (s.E.getX e).next) s.E.size s.head

/-! FALLBACK's layout, in closed form: the element list cut into groups of `⌊G/2⌋`, the groups
cut into chunks of `⌊⌊T/2⌋/⌊G/2⌋⌋`; group `k` (0-based) gets index `k + 1` and lies in chunk
`⌊k / gpc⌋ + 1`; labels are evenly spaced at every level. -/

/-- The target number of elements per group during a fallback rebuild. -/
def fbGS (P : Params) : Nat := max 1 (P.G / 2)
/-- The target number of groups per chunk during a fallback rebuild. -/
def fbGPC (P : Params) : Nat := max 1 ((P.T / 2) / fbGS P)

/-- The number of groups in FALLBACK's chunk `c` (0-based), out of `m`. -/
def fbChunkLen (P : Params) (m c : Nat) : Nat := min (fbGPC P) (m - c * fbGPC P)

/-- The number of chunks for `m` groups. -/
def fbNC (P : Params) (m : Nat) : Nat := (m + fbGPC P - 1) / fbGPC P

/-- Construct one group record for the fallback partition of the element list. -/
def fbGroup (P : Params) (groups : List (List Nat)) (k : Nat) : Group :=
  let m := groups.length
  let elems := groups.getD k []
  let c := k / fbGPC P
  { next := if k + 1 < m then k + 2 else NIL
    prev := if k = 0 then NIL else k
    first := elems.headD NIL
    last := elems.getLastD NIL
    chk := c + 1
    lab := (k % fbGPC P + 1) * ((1 <<< P.groupBits) / (fbChunkLen P m c + 1))
    size := elems.length }

/-- Construct one chunk record for the fallback partition into groups. -/
def fbChunk (P : Params) (groups : List (List Nat)) (c : Nat) : Chunk :=
  let m := groups.length
  let len := fbChunkLen P m c
  { next := if c + 1 < fbNC P m then c + 2 else NIL
    prev := if c = 0 then NIL else c
    first := c * fbGPC P + 1
    last := c * fbGPC P + len
    size := ((groups.drop (c * fbGPC P)).take len).foldl (fun a g => a + g.length) 0 }

/-- Element `i` of group `k` gets group `k + 1` and label `(i + 1)·step`. -/
def fbElems (P : Params) (groups : List (List Nat)) (E : Array Elem) : Array Elem :=
  groups.zipIdx.foldl (fun E p =>
    let step := (1 <<< P.elementBits) / (p.1.length + 1)
    p.1.zipIdx.foldl (fun E q =>
      E.modify q.1 fun e => { e with grp := p.2 + 1, lab := (q.2 + 1) * step }) E) E

/-- The state after FALLBACK's layout (tags are set by `relabelAll`). -/
def fbLayout (P : Params) (seq : List Nat) (s : Core) : Core :=
  let groups := chunksOf (fbGS P) seq
  { s with
    E := fbElems P groups s.E
    Gs := (default :: (List.range groups.length).map (fbGroup P groups)).toArray
    C := (default :: (List.range (fbNC P groups.length)).map (fbChunk P groups)).toArray
    freeG := []
    pqHead := #[], pqNext := #[], pqPrev := #[], pqWhere := #[], nbNext := #[], nbPrev := #[]
    pqHi := 0, pqLo := 0, resJob := none
    firstChunk := 1, firstGroup := 1 }

/-- Synchronous rebuild of groups, chunks and tags from the element list. -/
def fallback : CM Unit := do
  let P ← getP
  modify fun s => { s with fallbacks := s.fallbacks + 1 }
  let seq ← elements
  modify (fbLayout P seq)
  relabelAll

/-! ### Insertion with background work -/

/-- Update sizes and spend the scheduled group, chunk and reservation work after insertion. -/
def background (y : Nat) : CM Unit := do
  let P ← getP
  chunkSize (← getG (← getE y).grp).chk true
  let g := (← getE y).grp
  let G ← getG g
  if G.st == .quiet && G.size ≥ P.G then startGroupSplit g
  driveGroup (← getE y).grp
  driveChunk (← getG (← getE y).grp).chk
  reservation P.reservationBudget

/-- Run `act`; on a failed guard run `handler` from the state reached (bugs propagate). -/
def onGuard {α : Type} (act : CM α) (handler : CM α) : CM α :=
  tryCatch act fun
    | .guard _ => handler
    | e => throw e

/-- Insert an element and run background work, rebuilding after recoverable guard failures. -/
def insertAfter (x h : Nat) : CM Nat := do
  let y ← onGuard (insertElem x h) (do fallback; insertElem x h)
  onGuard (background y) fallback
  return y

/-! ### Construction -/

/-- A fresh core's lists: one chunk, one group, and the sentinel element (dead), all index 1. -/
def initState (P : Params) : Core :=
  { P := P
    E := #[default, { grp := 1, lab := 1 <<< (P.elementBits - 1), h := 0, live := false }]
    Gs := #[default, { chk := 1, lab := 1 <<< (P.groupBits - 1), first := 1, last := 1, size := 1 }]
    C := #[default, { first := 1, last := 1, size := 1 }]
    firstGroup := 1, firstChunk := 1, head := 1, tail := 1, count := 1 }

/-- The top structure of a fresh core: built now, or with `lazy` later, one `prepareStep` at a
time. -/
def initTop (lazy : Bool) : CM Unit := do
  let P ← getP
  modify fun s => { s with
    prep := some { chunk := 1, below := 1, path := Array.replicate (P.H + 1) NIL } }
  if lazy then
    modify fun s => { s with ready := false }
  else
    for _ in List.range (P.H + 1) do
      if ← initStep then break
    modify fun s => { s with ready := true }

/-- A fresh core (`Core.__init__`). -/
def initCore (lazy : Bool) : CM Unit := do
  let P ← getP
  set (initState P)
  initTop lazy

/-- One step of deferred initialization; `true` once the core is ready. -/
def prepareStep : CM Bool := do
  if !(← get).ready then
    if ← initStep then modify fun s => { s with ready := true }
  return (← get).ready

end OrderMaintenance.Model
