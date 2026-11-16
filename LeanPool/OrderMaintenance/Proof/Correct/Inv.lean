/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Pairwise
public import LeanPool.OrderMaintenance.Proof.Correct.Monad


/-!
# The safety invariant INV-S (`docs/PROOF.md` §3.1)

A core satisfies INV-S with respect to an abstract nesting `A` (the chunk list, and for each
chunk its run of groups, for each group its run of elements) when:
* the element, group and chunk lists are doubly linked lists, given by `A`;
* the runs' `first`/`last` pointers and the `grp`/`chk` fields agree with `A`;
* labels increase along each run, and tags along the chunk list.

Plus the facts that make the guards meaningful: a group or chunk outside the lists has `NIL`
links (so an adjacency guard `next(a) = b` proves `a` is in the list), a group is alive iff it
is in the list, and the free list holds only unused groups.

**Lemma 3.1** (`keys_sorted`): keys strictly increase along the element list.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model

/-! ### Linked lists -/

/-- The element after `x` in `l` (`NIL` if `x` is last or absent). -/
def succOf : List Nat → Nat → Nat
  | a :: b :: t, x => if a = x then b else succOf (b :: t) x
  | _, _ => NIL

/-- The element before `x` in `l` (`NIL` if `x` is first or absent). -/
def predOf (l : List Nat) (x : Nat) : Nat := succOf l.reverse x

/-- `l` is the doubly linked list starting at `hd`, with links `nxt` and `prv`. -/
structure LList (nxt prv : Nat → Nat) (hd : Nat) (l : List Nat) : Prop where
  nodup : l.Nodup
  nonil : NIL ∉ l
  head : hd = l.headD NIL
  next : ∀ x ∈ l, nxt x = succOf l x
  prev : ∀ x ∈ l, prv x = predOf l x

/-- `first`/`last` pointers of a run `r` (`NIL` for an empty run). -/
def Ends (first last : Nat) (r : List Nat) : Prop :=
  first = r.headD NIL ∧ last = r.getLastD NIL

/-! ### Field accessors -/

section accessors
variable (s : Core)
/-- Next element index. -/
abbrev eN (e : Nat) : Nat := (s.E.getX e).next
/-- Previous element index. -/
abbrev eP (e : Nat) : Nat := (s.E.getX e).prev
/-- Containing group of an element. -/
abbrev eG (e : Nat) : Nat := (s.E.getX e).grp
/-- Element order label. -/
abbrev eL (e : Nat) : Nat := (s.E.getX e).lab
/-- Next group index. -/
abbrev gN (g : Nat) : Nat := (s.Gs.getX g).next
/-- Previous group index. -/
abbrev gP (g : Nat) : Nat := (s.Gs.getX g).prev
/-- First element of a group. -/
abbrev gF (g : Nat) : Nat := (s.Gs.getX g).first
/-- Last element of a group. -/
abbrev gLs (g : Nat) : Nat := (s.Gs.getX g).last
/-- Containing chunk of a group. -/
abbrev gC (g : Nat) : Nat := (s.Gs.getX g).chk
/-- Group order label. -/
abbrev gL (g : Nat) : Nat := (s.Gs.getX g).lab
/-- Liveness flag of a group. -/
abbrev gA (g : Nat) : Bool := (s.Gs.getX g).alive
/-- Next chunk index. -/
abbrev cN (c : Nat) : Nat := (s.C.getX c).next
/-- Previous chunk index. -/
abbrev cP (c : Nat) : Nat := (s.C.getX c).prev
/-- First group of a chunk. -/
abbrev cF (c : Nat) : Nat := (s.C.getX c).first
/-- Last group of a chunk. -/
abbrev cLs (c : Nat) : Nat := (s.C.getX c).last
/-- Chunk order tag. -/
abbrev cT (c : Nat) : Nat := (s.C.getX c).tag
end accessors

/-! ### The abstract nesting -/

/-- Ordered chunk, group and element lists representing a concrete core. -/
structure Abs where
  /-- Chunks in global list order. -/
  chunks : List Nat
  /-- Groups in each chunk, in their list order. -/
  grps : Nat → List Nat
  /-- Elements in each group, in their list order. -/
  elts : Nat → List Nat

/-- Concatenate the chunk-local group lists in global order. -/
def Abs.glist (A : Abs) : List Nat := A.chunks.flatMap A.grps
/-- Concatenate the group-local element lists in global order. -/
def Abs.elist (A : Abs) : List Nat := A.glist.flatMap A.elts

/-! ### INV-S -/

/-- Structural, allocation, label and membership invariants of a core’s abstract nesting. -/
structure INV (s : Core) (A : Abs) : Prop where
  -- elements: every allocated element is in the list (deletion only marks tombstones)
  eList : LList (eN s) (eP s) s.head A.elist
  eAlloc : ∀ e, e ∈ A.elist ↔ 1 ≤ e ∧ e < s.E.size
  tail : s.tail = A.elist.getLastD NIL
  -- groups
  gList : LList (gN s) (gP s) s.firstGroup A.glist
  gAlloc : ∀ g ∈ A.glist, g < s.Gs.size
  gPos : 1 ≤ s.Gs.size
  gAlive : ∀ g, 1 ≤ g → g < s.Gs.size → (gA s g = true ↔ g ∈ A.glist)
  gOut : ∀ g, g ∉ A.glist → gN s g = NIL ∧ gP s g = NIL
  free : ∀ g ∈ s.freeG, 1 ≤ g ∧ g < s.Gs.size ∧ g ∉ A.glist
  freeNodup : s.freeG.Nodup
  -- chunks: every allocated chunk is in the list (emptied ones stay as tombstones)
  cList : LList (cN s) (cP s) s.firstChunk A.chunks
  cAlloc : ∀ c, c ∈ A.chunks ↔ 1 ≤ c ∧ c < s.C.size
  cOut : ∀ c, c ∉ A.chunks → cN s c = NIL ∧ cP s c = NIL ∧ cF s c = NIL
  -- runs
  gEnds : ∀ g ∈ A.glist, Ends (gF s g) (gLs s g) (A.elts g)
  cEnds : ∀ c ∈ A.chunks, Ends (cF s c) (cLs s c) (A.grps c)
  grp : ∀ g ∈ A.glist, ∀ e ∈ A.elts g, eG s e = g
  chk : ∀ c ∈ A.chunks, ∀ g ∈ A.grps c, gC s g = c
  -- sortedness
  eSorted : ∀ g ∈ A.glist, ((A.elts g).map (eL s)).IsChain (· < ·)
  gSorted : ∀ c ∈ A.chunks, ((A.grps c).map (gL s)).IsChain (· < ·)
  cSorted : (A.chunks.map (cT s)).IsChain (· < ·)

/-! ### Transfer: INV depends only on the fields it mentions -/

/-- The fields INV-S reads (except the chunk tags), and the element records, are equal. -/
structure SameLinks (s s' : Core) : Prop where
  Esize : s'.E.size = s.E.size
  eN : ∀ e, eN s' e = eN s e
  eP : ∀ e, eP s' e = eP s e
  eG : ∀ e, eG s' e = eG s e
  eL : ∀ e, eL s' e = eL s e
  eLive : ∀ e, (s'.E.getX e).live = (s.E.getX e).live
  eH : ∀ e, (s'.E.getX e).h = (s.E.getX e).h
  Gsize : s'.Gs.size = s.Gs.size
  gN : ∀ g, gN s' g = gN s g
  gP : ∀ g, gP s' g = gP s g
  gF : ∀ g, gF s' g = gF s g
  gLs : ∀ g, gLs s' g = gLs s g
  gC : ∀ g, gC s' g = gC s g
  gL : ∀ g, gL s' g = gL s g
  gA : ∀ g, gA s' g = gA s g
  freeG : s'.freeG = s.freeG
  head : s'.head = s.head
  tail : s'.tail = s.tail
  firstGroup : s'.firstGroup = s.firstGroup
  firstChunk : s'.firstChunk = s.firstChunk
  Csize : s'.C.size = s.C.size
  cN : ∀ c, cN s' c = cN s c
  cP : ∀ c, cP s' c = cP s c
  cF : ∀ c, cF s' c = cF s c
  cLs : ∀ c, cLs s' c = cLs s c
  P : s'.P = s.P

theorem SameLinks.refl (s : Core) : SameLinks s s := by
  constructor <;> intros <;> rfl

theorem SameLinks.trans {s t u : Core} (h1 : SameLinks s t) (h2 : SameLinks t u) :
    SameLinks s u := by
  constructor <;> (try intro x) <;> first
    | exact (h2.Esize).trans h1.Esize | exact (h2.eN x).trans (h1.eN x)
    | exact (h2.eP x).trans (h1.eP x) | exact (h2.eG x).trans (h1.eG x)
    | exact (h2.eL x).trans (h1.eL x) | exact (h2.eLive x).trans (h1.eLive x)
    | exact (h2.eH x).trans (h1.eH x) | exact (h2.Gsize).trans h1.Gsize
    | exact (h2.gN x).trans (h1.gN x) | exact (h2.gP x).trans (h1.gP x)
    | exact (h2.gF x).trans (h1.gF x) | exact (h2.gLs x).trans (h1.gLs x)
    | exact (h2.gC x).trans (h1.gC x) | exact (h2.gL x).trans (h1.gL x)
    | exact (h2.gA x).trans (h1.gA x) | exact h2.freeG.trans h1.freeG
    | exact h2.head.trans h1.head | exact h2.tail.trans h1.tail
    | exact h2.firstGroup.trans h1.firstGroup | exact h2.firstChunk.trans h1.firstChunk
    | exact h2.Csize.trans h1.Csize | exact (h2.cN x).trans (h1.cN x)
    | exact (h2.cP x).trans (h1.cP x) | exact (h2.cF x).trans (h1.cF x)
    | exact (h2.cLs x).trans (h1.cLs x) | exact h2.P.trans h1.P

theorem INV.of_sameLinks' {s s' : Core} {A : Abs} (h : INV s A) (hs : SameLinks s s')
    (hsorted : (A.chunks.map (cT s')).IsChain (· < ·)) : INV s' A := by
  have e1 : eN s' = eN s := funext hs.eN
  have e2 : eP s' = eP s := funext hs.eP
  have e3 : gN s' = gN s := funext hs.gN
  have e4 : gP s' = gP s := funext hs.gP
  have e5 : cN s' = cN s := funext hs.cN
  have e6 : cP s' = cP s := funext hs.cP
  have e8 : eL s' = eL s := funext hs.eL
  have e9 : gL s' = gL s := funext hs.gL
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := hsorted }
  · rw [e1, e2, hs.head]; exact h.eList
  · rw [hs.Esize]; exact h.eAlloc
  · rw [hs.tail]; exact h.tail
  · rw [e3, e4, hs.firstGroup]; exact h.gList
  · rw [hs.Gsize]; exact h.gAlloc
  · rw [hs.Gsize]; exact h.gPos
  · intro g; rw [hs.gA, hs.Gsize]; exact h.gAlive g
  · intro g; rw [e3, e4]; exact h.gOut g
  · rw [hs.freeG, hs.Gsize]; exact h.free
  · rw [hs.freeG]; exact h.freeNodup
  · rw [e5, e6, hs.firstChunk]; exact h.cList
  · rw [hs.Csize]; exact h.cAlloc
  · intro c hc; rw [e5, e6, hs.cF]; exact h.cOut c hc
  · intro g hg; rw [hs.gF, hs.gLs]; exact h.gEnds g hg
  · intro c hc; rw [hs.cF, hs.cLs]; exact h.cEnds c hc
  · intro g hg e he; rw [hs.eG]; exact h.grp g hg e he
  · intro c hc g hg; rw [hs.gC]; exact h.chk c hc g hg
  · rw [e8]; exact h.eSorted
  · rw [e9]; exact h.gSorted

theorem INV.of_sameLinks {s s' : Core} {A : Abs} (h : INV s A) (hs : SameLinks s s')
    (ht : ∀ c, cT s' c = cT s c) : INV s' A := by
  refine h.of_sameLinks' hs ?_
  have e7 : cT s' = cT s := funext ht
  rw [e7]; exact h.cSorted

/-! ### Lemma 3.1: keys increase along the element list -/

/-- The key of an element: (chunk tag, group label, element label). -/
def keyOf (s : Core) (e : Nat) : Nat × Nat × Nat := (cT s (gC s (eG s e)), gL s (eG s e), eL s e)

/-- Lexicographic order on keys. -/
def KeyLt (k k' : Nat × Nat × Nat) : Prop :=
  k.1 < k'.1 ∨ (k.1 = k'.1 ∧ (k.2.1 < k'.2.1 ∨ (k.2.1 = k'.2.1 ∧ k.2.2 < k'.2.2)))

theorem KeyLt.trans {a b c : Nat × Nat × Nat} (h1 : KeyLt a b) (h2 : KeyLt b c) : KeyLt a c := by
  unfold KeyLt at *; omega

theorem KeyLt.irrefl (a : Nat × Nat × Nat) : ¬ KeyLt a a := by unfold KeyLt; omega

theorem keyLt_iff (k k' : Nat × Nat × Nat) : keyLt k k' = true ↔ KeyLt k k' := by
  obtain ⟨a, b, c⟩ := k
  obtain ⟨a', b', c'⟩ := k'
  simp [keyLt, KeyLt]

theorem chain'_pairwise {l : List Nat} (h : l.IsChain (· < ·)) : l.Pairwise (· < ·) :=
  List.isChain_iff_pairwise.mp h

theorem Abs.elist_eq (A : Abs) :
    A.elist = (A.chunks.map fun c => (A.grps c).flatMap A.elts).flatten := by
  simp only [Abs.elist, Abs.glist, List.flatMap_def, List.map_flatten, List.flatten_flatten,
    List.map_map]
  rfl

theorem keys_sorted {s : Core} {A : Abs} (h : INV s A) :
    A.elist.Pairwise (fun a b => KeyLt (keyOf s a) (keyOf s b)) := by
  rw [Abs.elist_eq, List.pairwise_flatten]
  have hglist : ∀ c ∈ A.chunks, ∀ g ∈ A.grps c, g ∈ A.glist := fun c hc g hg => by
    simp only [Abs.glist, List.mem_flatMap]; exact ⟨c, hc, hg⟩
  constructor
  · -- within one chunk
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨c, hc, rfl⟩ := hl
    rw [List.flatMap_def, List.pairwise_flatten]
    constructor
    · -- within one group: element labels
      intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      have hgl := hglist c hc g hg
      have hs := List.pairwise_map.mp (chain'_pairwise (h.eSorted g hgl))
      refine hs.imp_of_mem fun {a b} ha hb hab => ?_
      simp [keyOf, h.grp g hgl a ha, h.grp g hgl b hb, KeyLt, hab]
    · -- different groups of one chunk: group labels
      have hs := List.pairwise_map.mp (chain'_pairwise (h.gSorted c hc))
      rw [List.pairwise_map]
      refine hs.imp_of_mem fun {g g'} hg hg' hgg => ?_
      intro a ha b hb
      simp [keyOf, h.grp g (hglist c hc g hg) a ha, h.grp g' (hglist c hc g' hg') b hb,
        h.chk c hc g hg, h.chk c hc g' hg', KeyLt, hgg]
  · -- different chunks: tags
    have hs := List.pairwise_map.mp (chain'_pairwise h.cSorted)
    rw [List.pairwise_map]
    refine hs.imp_of_mem fun {c c'} hc hc' hcc => ?_
    intro a ha b hb
    simp only [List.mem_flatMap] at ha hb
    obtain ⟨g, hg, ha⟩ := ha
    obtain ⟨g', hg', hb⟩ := hb
    simp [keyOf, h.grp g (hglist c hc g hg) a ha, h.grp g' (hglist c' hc' g' hg') b hb,
      h.chk c hc g hg, h.chk c' hc' g' hg', KeyLt, hcc]

/-- **Lemma 3.1.** For elements of the list, `order(x, y)` holds iff `x` precedes `y`. -/
theorem order_iff {s : Core} {A : Abs} (h : INV s A) {x y : Nat} (hx : x ∈ A.elist)
    (hy : y ∈ A.elist) :
    KeyLt (keyOf s x) (keyOf s y) ↔ A.elist.idxOf x < A.elist.idxOf y := by
  have hp := keys_sorted h
  constructor
  · intro hk
    rcases Nat.lt_trichotomy (A.elist.idxOf x) (A.elist.idxOf y) with hlt | heq | hgt
    · exact hlt
    · have : x = y := by
        have := congrArg (A.elist[·]?) heq
        simpa [List.getElem?_idxOf hx, List.getElem?_idxOf hy] using this
      subst this; exact absurd hk (KeyLt.irrefl _)
    · have := List.pairwise_iff_getElem.mp hp (A.elist.idxOf y) (A.elist.idxOf x)
        (List.idxOf_lt_length_iff.mpr hy) (List.idxOf_lt_length_iff.mpr hx) hgt
      simp only [List.getElem_idxOf] at this
      exact absurd (KeyLt.trans hk this) (KeyLt.irrefl _)
  · intro hlt
    have := List.pairwise_iff_getElem.mp hp (A.elist.idxOf x) (A.elist.idxOf y)
      (List.idxOf_lt_length_iff.mpr hx) (List.idxOf_lt_length_iff.mpr hy) hlt
    simpa only [List.getElem_idxOf] using this

end OrderMaintenance.Proof
