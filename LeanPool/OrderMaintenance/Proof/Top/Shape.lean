/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Views


/-!
# M5: the order invariant of the top structure (`docs/PROOF.md` §4.5.1)

`Shape s cl ord`: the structural invariant, for a state whose running job (if any) has copied its
whole path. `cl` is the chunk list and `ord h` the order `≺_h` of the nodes of height `h`
(`ord 0 = cl`), a ghost variable.

* the live tree: heights, live parents and children, ordered (`OT`);
* ghosts and targets;
* tables: entries, `inTables`/`cin`, label order (O1), adjacency (W1), (Q), sides (S);
* paths: (P), (W3), (O2), sizes; range pointers; tags.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- Entries of height `h`: chunks for `h = 0`, else nodes. -/
abbrev Ent (ord : Nat → List Nat) (h e : Nat) : Prop := e ∈ ord h

/-- The part of the invariant that orders tags (Lemma T1). -/
structure ShapeT (s : TS) (cl : List Nat) (ord : Nat → List Nat) : Prop where
  H3 : 3 ≤ s.P.H
  ord0 : ord 0 = cl
  ordNodup : ∀ h, (ord h).Nodup
  ordMem : ∀ h, 1 ≤ h → h ≤ s.P.H → ∀ v, v ∈ ord h ↔ isN s v ∧ ht s v = h
  ordHigh : ∀ h, s.P.H < h → ord h = []
  htN : ∀ v, isN s v → 1 ≤ ht s v ∧ ht s v ≤ s.P.H
  root : ord s.P.H = [s.P.H] ∧ liveN s s.P.H ∧ (nd s s.P.H).livePar = NIL
  pathEnt : ∀ c ∈ cl, ∀ j, j ≤ s.P.H → Ent ord j (pp s c j)
  W3 : ∀ c ∈ cl, ∀ j, 1 ≤ j → j ≤ s.P.H → pp s c (j - 1) ∈ order s (pp s c j)
  O2 : ∀ j, j ≤ s.P.H → ∀ c d, Before cl c d →
    pp s c j = pp s d j ∨ Before (ord j) (pp s c j) (pp s d j)
  O1 : ∀ X, isN s X → (order s X).Sublist (ord (ht s X - 1))
  labsOk : ∀ X, isN s X → GapsGe s.P.beta 1 (labs s X)

structure Shape (s : TS) (cl : List Nat) (ord : Nat → List Nat) : Prop extends ShapeT s cl ord where
  -- the live tree
  up : ∀ v, liveN s v → ht s v < s.P.H →
    liveN s (nd s v).livePar ∧ ht s (nd s v).livePar = ht s v + 1 ∧
      v ∈ (nd s (nd s v).livePar).children
  lp : ∀ c ∈ cl, liveN s (lpr s c) ∧ ht s (lpr s c) = 1 ∧ c ∈ (nd s (lpr s c)).children
  kids : ∀ u, liveN s u → (nd s u).children.Nodup ∧
    (nd s u).children.Sublist (ord (ht s u - 1)) ∧
    ∀ e ∈ (nd s u).children, par s (ht s u - 1) e = u ∧ (2 ≤ ht s u → liveN s e)
  /-- The live tree is ordered: the children of `u ≺ u'` precede those of `u'`. -/
  OT : ∀ h, 1 ≤ h → h ≤ s.P.H → ∀ u u' e e', liveN s u → liveN s u' → Before (ord h) u u' →
    Ent ord (h - 1) e → Ent ord (h - 1) e' → par s (h - 1) e = u → par s (h - 1) e' = u' →
    Before (ord (h - 1)) e e'
  -- ghosts and targets
  ghost : ∀ v, ghostN s v →
    liveN s (nd s v).t1 ∧ liveN s (nd s v).t2 ∧ ht s (nd s v).t1 = ht s v ∧
      ht s (nd s v).t2 = ht s v ∧ srcOf s (nd s v).t1 = v ∧ srcOf s (nd s v).t2 = v ∧
      (nd s v).livePar = NIL ∧ (nd s v).children = [] ∧ srcOf s v = NIL ∧ ht s v < s.P.H ∧
      (nd s (nd s v).t1).livePar = (nd s (nd s v).t2).livePar ∧
      [(nd s v).t1, (nd s v).t2] <:+: (nd s (nd s (nd s v).t1).livePar).children ∧
      [(nd s v).t1, v, (nd s v).t2] <:+: ord (ht s v)
  src : ∀ t, liveN s t → srcOf s t ≠ NIL →
    ghostN s (srcOf s t) ∧ (t = (nd s (srcOf s t)).t1 ∨ t = (nd s (srcOf s t)).t2)
  -- tables
  tabEnt : ∀ X, isN s X → ∀ e ∈ order s X, Ent ord (ht s X - 1) e
  tabsIff : ∀ h e X, Ent ord h e → (X ∈ tabs s h e ↔ isN s X ∧ ht s X = h + 1 ∧ e ∈ order s X)
  tabsNodup : ∀ h e, Ent ord h e → (tabs s h e).Nodup
  Q : ∀ h e X, Ent ord h e → X ∈ tabs s h e → X = par s h e ∨ X = srcOf s (par s h e)
  W1 : ∀ v, ghostN s v → ∀ X ∈ tabs s (ht s v) v, [(nd s v).t1, v, (nd s v).t2] <:+: order s X
  side : ∀ v, ghostN s v → ∀ e ∈ order s v,
    lookup (nd s v).side e = some (if par s (ht s v - 1) e = (nd s v).t1 then .left else .right)
  -- paths
  pathSize : ∀ c ∈ cl, (s.path.getX c).size = s.P.H + 1
  P : ∀ c ∈ cl, ∀ j, 1 ≤ j → j ≤ s.P.H → pp s c j = anc s c j ∨
    (ghostN s (pp s c j) ∧ (anc s c j = (nd s (pp s c j)).t1 ∨ anc s c j = (nd s (pp s c j)).t2))
  /-- (S): below a ghost, the entry is in the table of the chunk's live ancestor. -/
  Sr : ∀ c ∈ cl, ∀ j, 1 ≤ j → j ≤ s.P.H → ghostN s (pp s c j) →
    pp s c (j - 1) ∈ order s (anc s c j)
  -- range pointers and tags
  ends : ∀ u, isN s u → (nd s u).first = (rng s cl u).headD NIL ∧
    (nd s u).last = (rng s cl u).getLastD NIL
  tags : ∀ c ∈ cl, s.tag c = tagF s c

end OrderMaintenance.Proof.Top
