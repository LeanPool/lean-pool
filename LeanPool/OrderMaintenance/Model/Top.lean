/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Model.PQ


/-!
# Level F: the top structure (`prototype/top_wbbt.py`)

A weight-balanced tree over the chunks with immutable label tables, stored paths and ghost
drains. A chunk's tag is the concatenation of the labels along its path `p[1..H]`, with
`F_j = lab_{p[j]}(p[j-1])` in bits `[(j-1)β, jβ)`.
-/


@[expose] public section

namespace OrderMaintenance.Model

/-- `(n, l)` with `l` placed after the existing entries, or replacing the entry for `n`. -/
def assocSet {β : Type} (l : List (Nat × β)) (k : Nat) (v : β) : List (Nat × β) :=
  if l.any (·.1 == k) then l.map (fun p => if p.1 == k then (k, v) else p) else l ++ [(k, v)]

/-- Remove every entry with the specified key from an association list. -/
def assocErase {β : Type} (l : List (Nat × β)) (k : Nat) : List (Nat × β) :=
  l.filter (·.1 != k)

/-- Split a list into pieces of length `n` (the last may be shorter). -/
def chunksOf {α : Type} (n : Nat) : List α → List (List α)
  | [] => []
  | x :: xs => ((x :: xs).take (max n 1)) :: chunksOf n ((x :: xs).drop (max n 1))
termination_by l => l.length
decreasing_by simp; omega

/-! ### Utilities -/

/-- Discard the top tree and all of its chunk paths and table memberships. -/
def resetTop : CM Unit :=
  modify fun s => { s with nodes := #[default], path := #[], cin := #[], lpar := #[] }

/-- Append a fresh node at the specified height and return its index. -/
def newNode (h : Nat) : CM Nat :=
  modifyGet fun s => (s.nodes.size, { s with nodes := s.nodes.push { height := h } })

/-- Read the array of top-tree ancestors associated with a chunk. -/
def getPath (c : Nat) : CM (Array Nat) := return (← get).path.getX c
/-- Replace a chunk’s array of top-tree ancestors. -/
def setPath (c : Nat) (p : Array Nat) : CM Unit :=
  modify fun s => { s with path := s.path.setX c p }
/-- Set one height of a chunk’s top-tree ancestor path. -/
def setPathAt (c j v : Nat) : CM Unit :=
  modify fun s => { s with path := s.path.setX c ((s.path.getX c).setX j v) }
/-- Read the live parent of a chunk at height zero. -/
def getLpar (c : Nat) : CM Nat := return (← get).lpar.getX c
/-- Set the live parent of a chunk at height zero. -/
def setLpar (c v : Nat) : CM Unit := modify fun s => { s with lpar := s.lpar.setX c v }

/-- Tables containing entry `e`, which lives at height `h` (0 = chunk). -/
def inTablesOf (e h : Nat) : CM (List Nat) := do
  if h == 0 then return (← get).cin.getX e else return (← getN e).inTables

/-- Replace the containing-table list of a chunk or a higher tree entry. -/
def setInTables (e h : Nat) (l : List Nat) : CM Unit := do
  if h == 0 then modify fun s => { s with cin := s.cin.setX e l }
  else modN e fun n => { n with inTables := l }

/-- Assemble a chunk tag from the labels along its top-tree path. -/
def tagOf (c : Nat) : CM Nat := do
  let P ← getP
  let p ← getPath c
  let mut t := 0
  let mut below := c
  for j in List.range' 1 P.H do
    -- total: a missing label reads as 0 (FALLBACK then checks the tags, `relabelAll`)
    let l := ((← getN (p.getX j)).lab? below).getD 0
    t := t ||| (l <<< ((j - 1) * P.beta))
    below := p.getX j
  return t

/-- Check that a proposed chunk tag lies strictly between its neighbours’ tags. -/
def guardTag (c t : Nat) : CM Unit := do
  let C ← getC c
  if C.prev != NIL && !((← getC C.prev).tag < t) then guard "top: tag not above predecessor"
  if C.next != NIL && !(t < (← getC C.next).tag) then guard "top: tag not below successor"

/-- A guarded tag write (the safety principle): `t` must lie strictly between the tags of the
chunk-list neighbours of `c`. -/
def guardedSetTag (c t : Nat) : CM Unit := do
  guardTag c t
  modC c fun C => { C with tag := t }

/-- A label for a new entry right before/after `e` in the table of node `t` (averaging). -/
def roomNextTo (t e : Nat) (before : Bool) : CM Nat := do
  let P ← getP
  let tab := (← getN t).table
  let some i := tab.findIdx? (·.1 == e) | guard "room_next_to: entry not in table"
  let labAt (k : Nat) : Nat := (tab.getD k (0, 0)).2
  -- `lo1` is the lower neighbour's label plus one (the prototype's `lo = -1` becomes 0)
  let (lo1, hi) :=
    if before then ((if i > 0 then labAt (i - 1) + 1 else 0), labAt i)
    else (labAt i + 1, if i + 1 < tab.length then labAt (i + 1) else 1 <<< P.beta)
  if lo1 ≥ hi then guard "top: table full"
  return (lo1 + hi - 1) / 2

/-- Insert and label a new table entry adjacent to a specified existing entry. -/
def tableInsert (t e new : Nat) (before : Bool) (lab : Nat) : CM Unit := do
  let T ← getN t
  let some i := T.table.findIdx? (·.1 == e) | guard "table_insert: entry not in table"
  let table := T.table.insertIdx (if before then i else i + 1) (new, lab)
  let side ← if T.draining then
      match lookup T.side e with
      | some sd => pure (assocSet T.side new sd)
      | none => guard "table_insert: entry has no side"
    else pure T.side
  modN t fun n => { n with table := table, side := side }

/-! ### Construction -/

/-- One step of `init_steps`: build the chain node of height `prep.h`, or finish. Returns
`true` once the structure is complete. -/
def initStep : CM Bool := do
  let P ← getP
  let some pr := (← get).prep | return true
  let c := pr.chunk
  if pr.h == 1 then
    resetTop
    setInTables c 0 []
  if pr.h ≤ P.H then
    let h := pr.h
    let center := 1 <<< (P.beta - 1)
    let v ← newNode h
    modN v fun n => { n with
      children := [pr.below], table := [(pr.below, center)], weight := 1,
      first := c, last := c }
    if h == 1 then
      setInTables c 0 [v]
      setLpar c v
    else
      modN pr.below fun n => { n with inTables := [v], livePar := v }
    modify fun s => { s with prep := some { pr with
      h := h + 1, below := v, tag := pr.tag ||| (center <<< ((h - 1) * P.beta)),
      path := pr.path.setX h v } }
    return false
  else
    setPath c pr.path
    modC c fun C => { C with tag := pr.tag }
    modify fun s => { s with prep := none }
    return true

/-- Construct a fresh top tree for an ordered list of chunks. -/
def build (chunks : List Nat) : CM Unit := do
  resetTop
  let P ← getP
  let mut level := chunks
  for h in List.range' 1 P.H do
    let groups := if h < P.H then chunksOf P.a level else [level]
    let mut nxt : Array Nat := #[]
    for grp in groups do
      let v ← newNode h
      let gap := (1 <<< P.beta) / (grp.length + 1)
      let mut table : Array (Nat × Nat) := #[]
      let mut weight := 0
      let mut i := 0
      for e in grp do
        table := table.push (e, (i + 1) * gap)
        i := i + 1
        if h == 1 then
          setInTables e 0 [v]
          setLpar e v
          weight := weight + 1
        else
          modN e fun n => { n with inTables := [v], livePar := v }
          weight := weight + (← getN e).weight
      modN v fun n => { n with children := grp, table := table.toList, weight := weight }
      nxt := nxt.push v
    level := nxt.toList
  for c in chunks do
    let mut p := Array.replicate (P.H + 1) NIL
    let mut v ← getLpar c
    for j in List.range' 1 P.H do
      p := p.setX j v
      let V ← getN v
      if V.first == NIL then modN v fun n => { n with first := c }
      modN v fun n => { n with last := c }
      v := V.livePar
    setPath c p
  for c in chunks do
    let t ← tagOf c
    modC c fun C => { C with tag := t }

/-- The linked list from `x` along `nxt`, at most `fuel` long. -/
def walkList (nxt : Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x = NIL then [] else x :: walkList nxt fuel (nxt x)

/-- Number the chunks of `l` as `1, 2, 3, …`. -/
def renumber (l : List Nat) (C : Array Chunk) : Array Chunk :=
  (l.zipIdx 1).foldl (fun C q => C.modify q.1 fun x => { x with tag := q.2 }) C

/-- Strictly increasing? -/
def increasing : List Nat → Bool
  | a :: b :: t => a < b && increasing (b :: t)
  | _ => true

/-- FALLBACK's top part: rebuild the tree, then verify that the tags increase along the chunk
list. If they do not (label width too small, `docs/PROOF.md` §3.4), number the chunks
`1, 2, 3, …` instead: correctness then needs no condition on `β`. -/
def relabelAll : CM Unit := do
  let s ← get
  let chunks := walkList (fun c => (s.C.getX c).next) s.C.size s.firstChunk
  tryCatch (build chunks) fun _ => pure ()
  let s ← get
  if !increasing (chunks.map fun c => (s.C.getX c).tag) then
    modify fun s => { s with C := renumber chunks s.C }

/-! ### Drains -/

/-- Are `a` and `b` the two targets of one running drain? -/
def sameDrainN (ns : Array Node) (a b : Nat) : Bool :=
  (ns.getX a).overflowOf != NIL && (ns.getX a).overflowOf == (ns.getX b).overflowOf

/-- Test whether two node indices belong to the same active drain. -/
def sameDrain (a b : Nat) : CM Bool := return sameDrainN (← get).nodes a b

/-- `startDrain`'s greedy cut: the length of the longest prefix of `ws` with sum at most
`budget`. -/
def cutLen : List Nat → Nat → Nat
  | [], _ => 0
  | w :: ws, budget => if w ≤ budget then cutLen ws (budget - w) + 1 else 0

/-- Move the cut `k` right while children `k - 1, k` form a pair (`pr k`), at most `f` times. -/
def shiftR (pr : Nat → Bool) (n : Nat) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if 0 < k && k < n then (if pr k then shiftR pr n f (k + 1) else k) else k

/-- Move the cut `k` left while children `k - 1, k` form a pair, at most `f` times. -/
def shiftL (pr : Nat → Bool) : Nat → Nat → Nat
  | 0, k => k
  | f + 1, k => if k > 0 then (if pr k then shiftL pr f (k - 1) else k) else k

/-- The side of every entry of `order`: `left` before `boundary`, `right` from it on. -/
def sidesOf (order : List Nat) (boundary : Nat) : List (Nat × Side) :=
  (order.foldl (fun (acc : List (Nat × Side) × Side) e =>
    let sd := if e == boundary then Side.right else acc.2
    (assocSet acc.1 e sd, sd)) ([], .left)).1

/-- A ghost entry takes the side of its first target; `none` if that target has no side. -/
def fixSides (ns : Array Node) : List Nat → List (Nat × Side) → Option (List (Nat × Side))
  | [], side => some side
  | e :: es, side =>
    if (ns.getX e).draining then
      match lookup side (ns.getX e).t1 with
      | some st => fixSides ns es (assocSet side e st)
      | none => none
    else fixSides ns es side

/-- A fresh table: the entries `part` with evenly spaced labels. -/
def evenTable (beta : Nat) (part : List Nat) : List (Nat × Nat) :=
  (List.range part.length).zip part |>.map fun (i, e) => (e, (i + 1) * ((1 <<< beta) /
    (part.length + 1)))

/-- Add table `t` to the tables of entry `e` (height `h`). -/
def addTable (h t e : Nat) : CM Unit := do
  setInTables e h ((← inTablesOf e h) ++ [t])

/-- Insert `v1` right before and `v2` right after `v` in table `T`, with labels `a`, `b`. -/
def insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) : CM Unit := do
  tableInsert q.1 v v1 true q.2.1
  tableInsert q.1 v v2 false q.2.2

/-- Make `w` the live parent of entry `e` (height `h - 1`). -/
def setParent (h w e : Nat) : CM Unit :=
  if h == 1 then setLpar e w else modN e fun n => { n with livePar := w }

/-- `startDrain`'s cut of the children with weights `ws`: the greedy cut `k0`, then (`hh`, above
height 1) moved so as not to separate a pair (`pr k`: children `k - 1, k` are a drain's targets). -/
def drainCut (ws : List Nat) (pr : Nat → Bool) (hh : Bool) : Nat :=
  let n := ws.length
  let k0 := max (cutLen (ws.take (n - 1)) (ws.sum / 2)) 1
  let k1 := if hh then shiftR pr n n k0 else k0
  if hh && decide (k1 ≥ n) then shiftL pr n (n - 1) else k1

/-- The weight `startDrain` gives child `e` of a node of height `h`. -/
def drainWt (ns : Array Node) (h e : Nat) : Nat := if h == 1 then 1 else (ns.getX e).weight

/-- Children `k - 1`, `k` are the targets of one drain. -/
def drainPr (ns : Array Node) (kids : List Nat) (k : Nat) : Bool :=
  sameDrainN ns (kids.getD (k - 1) 0) (kids.getD k 0)

/-- The entries of `V`'s table that move to the new nodes: chunks, children, and ghosts with a
range. -/
def drainEntries (ns : Array Node) (V : Node) : List Nat :=
  V.order.filter fun e => V.height == 1 || V.children.contains e || (ns.getX e).first != NIL

/-- The side of every entry of `V`'s table: by position from `boundary`, a ghost then taking the
side of its first target. -/
def drainSide (ns : Array Node) (V : Node) (boundary : Nat) : Option (List (Nat × Side)) :=
  let side0 := sidesOf V.order boundary
  if V.height > 1 then fixSides ns (drainEntries ns V) side0 else some side0

/-- Begin a balanced node drain without separating an active drain’s targets. -/
def startDrain (v : Nat) : CM Unit := do
  let P ← getP
  let V ← getN v
  let h := V.height
  let kids := V.children
  if kids.length < 2 then return
  let s0 ← get
  -- partition the live children by weight, never separating the targets of an active drain
  let k := drainCut (kids.map (drainWt s0.nodes h)) (drainPr s0.nodes kids) (h > 1)
  if h > 1 && k == 0 then return
  let entries := drainEntries s0.nodes V
  let some side := drainSide s0.nodes V (kids.getD k 0)
    | guard "start_drain: target has no side"
  let sideOf (e : Nat) : Option Side := lookup side e
  let left := entries.filter (sideOf · == some .left)
  let right := entries.filter (sideOf · == some .right)
  -- labels for v1 / v2 in every table holding v (guards first)
  let l1 ← V.inTables.mapM (roomNextTo · v true)
  let l2 ← V.inTables.mapM (roomNextTo · v false)
  -- mutate
  let v1 ← newNode h
  let v2 ← newNode h
  (V.inTables.zip (l1.zip l2)).forM (insertAroundIn v v1 v2)
  modN v1 fun n => { n with inTables := V.inTables, table := evenTable P.beta left }
  modN v2 fun n => { n with inTables := V.inTables, table := evenTable P.beta right }
  left.forM (addTable (h - 1) v1)
  right.forM (addTable (h - 1) v2)
  if !kids.all (fun e => (sideOf e).isSome) then guard "start_drain: child has no side"
  let ch1 := kids.filter (sideOf · == some .left)
  let ch2 := kids.filter (sideOf · == some .right)
  ch1.forM (setParent h v1)
  modN v1 fun n => { n with
    children := ch1, weight := (ch1.map (drainWt s0.nodes h)).sum, livePar := V.livePar,
    overflowOf := v }
  ch2.forM (setParent h v2)
  modN v2 fun n => { n with
    children := ch2, weight := (ch2.map (drainWt s0.nodes h)).sum, livePar := V.livePar,
    overflowOf := v }
  let par ← getN V.livePar
  if !par.children.contains v then guard "start_drain: not a child of its parent"
  modN V.livePar fun n => { n with children := n.children.replace1 v [v1, v2] }
  modN v fun n => { n with
    draining := true, t1 := v1, t2 := v2, side := side,
    livePar := NIL, children := [] }

/-- Remove ghost `v` from the tables of entry `e` (height `h`). -/
def dropTable (h v e : Nat) : CM Unit := do
  let tabs ← inTablesOf e h
  if tabs.contains v then setInTables e h (tabs.erase v)

/-- Remove ghost `v` from table `T`. -/
def dropEntry (v T : Nat) : CM Unit := do
  let Tn ← getN T
  if !(Tn.order.contains v) then guard "finish_drain: ghost missing from a table"
  modN T fun n => { n with table := assocErase n.table v, side := assocErase n.side v }

/-- Release target `t` of ghost `v`. -/
def release (v t : Nat) : CM Unit := do
  if (← getN t).overflowOf == v then modN t fun n => { n with overflowOf := NIL }

/-- Finish a node drain and install the replacement nodes and their links. -/
def finishDrain (v : Nat) : CM Unit := do
  let V ← getN v
  let h := V.height
  V.order.forM (dropTable (h - 1) v)
  V.inTables.forM (dropEntry v)
  release v V.t1
  release v V.t2
  modN v fun n => { n with alive := false, inTables := [] }

/-- The entry below chunk `y` in a table of height `h`. -/
def belowOf (h y : Nat) : CM Nat := do
  if h == 1 then return y else return (← getPath y).getX (h - 1)

/-- Move one chunk off ghost `v`. Returns `false` when `v` is fully drained. -/
def drainStep (v : Nat) : CM Bool := do
  let P ← getP
  let V ← getN v
  if !V.alive then return false
  let h := V.height
  if V.first == NIL then
    finishDrain v
    return false
  let y0 := V.first
  let b0 ← belowOf h y0
  let some sd0 := lookup V.side b0 | guard "drain_step: no side"
  let (t, left, y, below) ← if sd0 == .left then pure (V.t1, true, y0, b0) else do
    let y := V.last
    let b ← belowOf h y
    let some sd := lookup V.side b | guard "drain_step: no side"
    if sd != .right then guard "top: drain sides out of order"
    pure (V.t2, false, y, b)
  let T ← getN t
  let p ← getPath y
  if h + 1 ≥ p.size then guard "drain_step: draining the root"
  let par ← getN (p.getX (h + 1))
  let (some pt, some tb) := (par.lab? t, T.lab? below) | guard "top: missing table entry"
  let some pv := par.lab? v | guard "drain_step: ghost missing from parent table"
  let some vb := V.lab? below | guard "drain_step: entry missing from ghost table"
  let b := P.beta
  let old := (pv <<< (h * b)) ||| (vb <<< ((h - 1) * b))
  let new := (pt <<< (h * b)) ||| (tb <<< ((h - 1) * b))
  let cy ← getC y
  if cy.tag < old then guard "drain_step: negative tag"
  let tag := cy.tag - old + new
  guardedSetTag y tag
  setPathAt y h t
  if V.first == V.last then modN v fun n => { n with first := NIL, last := NIL }
  else if left then modN v fun n => { n with first := cy.next }
  else modN v fun n => { n with last := cy.prev }
  if left then
    if T.first == NIL then modN t fun n => { n with first := y }
    modN t fun n => { n with last := y }
  else
    if T.last == NIL then modN t fun n => { n with last := y }
    modN t fun n => { n with first := y }
  return true

/-! ### Insertion jobs -/

/-- The guarded, read-only part of `insertAround`: labels for the new neighbours `y`, `z` of
`x` in every table holding `x`, the tags of `y` and `z`, and `x`'s live parent. -/
def insertAroundPrep (x : Nat) : CM (Nat × Nat × List Nat × List Nat × List Nat × Nat) := do
  let px ← getPath x
  let tabs := (← get).cin.getX x
  let ly ← tabs.mapM (roomNextTo · x true)
  let lz ← tabs.mapM (roomNextTo · x false)
  let p1 := px.getX 1
  let some f1x := (← getN p1).lab? x | guard "insert_around: x missing from its parent table"
  let some i1 := tabs.idx? p1 | guard "insert_around: parent not among x's tables"
  let tx := (← getC x).tag
  if tx < f1x then guard "insert_around: negative tag"
  let lp ← getLpar x
  if !(← getN lp).children.contains x then guard "insert_around: x not a child of its parent"
  return (tx - f1x + ly.getD i1 0, tx - f1x + lz.getD i1 0, tabs, ly, lz, lp)

/-- A new chunk `c` joins the tables `tabs` and the live parent `lp`; its path is copied later. -/
def joinChunk (tabs : List Nat) (lp c : Nat) : CM Unit := do
  let P ← getP
  setPath c (Array.replicate (P.H + 1) NIL)
  setInTables c 0 tabs
  setLpar c lp

/-- The rest of `insertAround`, in the top structure only: table entries, paths, children. -/
def insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) : CM Job := do
  (tabs.zip (ly.zip lz)).forM (insertAroundIn x y z)
  joinChunk tabs lp y
  joinChunk tabs lp z
  modN lp fun n => { n with children := n.children.replace1 x [y, x, z] }
  return { x := x, y := y, z := z, pc := .copy 1 }

/-- The O(1) part of a top insertion: `y, z` are linked before/after `x` in the chunk list.
The tags are written first (the prototype writes them last; only failure states differ, and
FALLBACK discards those); `y` and `z` are not neighbours, so the second guard is unaffected by
the first write. Returns the job that does the rest. -/
def insertAround (x y z : Nat) : CM Job := do
  let (ty, tz, tabs, ly, lz, lp) ← insertAroundPrep x
  guardedSetTag y ty
  guardedSetTag z tz
  insertAroundFinish x y z tabs ly lz lp

/-- The sweep funding loop of `v`, resumed after `k` sweep steps. -/
def fundLoop (j : Job) (v up src k : Nat) : CM (Option Job) := do
  if k < (← getP).s then
    if (← drainStep src) then return some { j with pc := .fund v up src (k + 1) }
  return some { j with pc := .walk (some up) }

/-- Resume a reservation job after starting a drain, funding its source when needed. -/
def afterDrain (j : Job) (v up : Nat) : CM (Option Job) := do
  let src := (← getN v).overflowOf
  if src != NIL then fundLoop j v up src 0
  else return some { j with pc := .walk (some up) }

/-- The body of the upward walk at node `v`, up to its next suspension point. -/
def walkBody (j : Job) (v : Nat) : CM (Option Job) := do
  if v == NIL then return none
  let P ← getP
  let V ← getN v
  let up := V.livePar
  modN v fun n => { n with weight := n.weight + 2 }
  if up != NIL && !V.draining && V.overflowOf == NIL && V.weight + 2 > 2 * P.a ^ V.height then
    startDrain v
    return some { j with pc := .afterDrain v up }
  afterDrain j v up

/-- Resume a job until its next suspension point (`some`), or to its end (`none`). -/
def jobStep (j : Job) : CM (Option Job) := do
  let P ← getP
  match j.pc with
  | .copy l =>
    let v := (← getPath j.x).getX l
    setPathAt j.y l v
    setPathAt j.z l v
    let V ← getN v
    if V.first == j.x then modN v fun n => { n with first := j.y }
    if V.last == j.x then modN v fun n => { n with last := j.z }
    return some { j with pc := if l < P.H then .copy (l + 1) else .walk none }
  | .walk none => walkBody j (← getLpar j.y)
  | .walk (some v) => walkBody j v
  | .afterDrain v up => afterDrain j v up
  | .fund v up src k => fundLoop j v up src k

end OrderMaintenance.Model
