/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.ListLib
public import LeanPool.OrderMaintenance.Proof.Top.StartData


/-!
# M6: `startDrain`'s side list (`drainSide`), built in place

`drainSideP` builds the side list of `v` directly in `v`'s side list: first `sidesOf` (a fold
over `v`'s table with `assocSet`), then, above height 1, `fixSides` (ghost entries take the side of
their first target).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model

/-- A side list as stored: sides as 0 / 1. -/
abbrev encS (l : List (Nat × Side)) : List (Nat × Nat) := l.map fun q => (q.1, sideN q.2)

theorem lookup_encS (l : List (Nat × Side)) (x : Nat) : lookup (encS l) x = (lookup l x).map
  sideN := by
  unfold lookup
  rw [List.find?_map]
  simp [Function.comp_def, Option.map_map]

theorem assocSet_encS (l : List (Nat × Side)) (x : Nat) (st : Side) :
    assocSet (encS l) x (sideN st) = encS (assocSet l x st) := by
  unfold assocSet
  simp only [List.any_map, Function.comp_def]
  split
  · simp only [List.map_map, Function.comp_def]
    congr 1; funext p; split <;> rfl
  · simp

theorem sideOfN_sideN (st : Side) : sideOfN (sideN st) = st := by cases st <;> rfl

theorem sideN_le (st : Side) : sideN st ≤ 1 := by cases st <;> simp [sideN]

theorem fixSides_append (ns : Array Node) : ∀ (l1 l2 : List Nat) (side : List (Nat × Side)),
    fixSides ns (l1 ++ l2) side = (fixSides ns l1 side).bind (fixSides ns l2)
  | [], l2, side => by simp [fixSides]
  | e :: l1, l2, side => by
    simp only [List.cons_append, fixSides]
    split
    · split
      · exact fixSides_append ns l1 l2 _
      · rfl
    · exact fixSides_append ns l1 l2 side

open OrderMaintenance.Machine (Reg BinOp UnOp)
open OrderMaintenance.Proof.Top (sideStep sidesOf_eq)

local notation "upd" => Machine.State.upd

theorem put_side_encS (s : Core) (v : Nat) (l : List (Nat × Side)) :
    LK.put s v (encS l) .side = { s with nodes := s.nodes.modify v fun n => { n with side := l }
      } := by
  simp [LK.put, encS, List.map_map, Function.comp_def, sideOfN_sideN]

@[simp] theorem LK.put_nodes_size (s : Core) (i : Nat) (l : List (Nat × Nat)) (k : LK) :
    (k.put s i l).nodes.size = s.nodes.size := by
  cases k <;> simp [LK.put]

/-- One round of `sidesOf`, updating table entry `j` to its current side. -/
def sideBody : Stm := cm{
  e := table[v][j].fst
  if e = b then sd := 1
  call ‹assocSetP .side›(v, e, sd) }

/-- `sidesOf` over the first `j` entries. -/
abbrev preSides (o : List Nat) (b j : Nat) : List (Nat × Side) × Side := (o.take j).foldl
  (sideStep b) ([], .left)

theorem length_preSides (o : List Nat) (b j : Nat) : (preSides o b j).1.length ≤ j := by
  have := OrderMaintenance.Proof.Top.length_sideStep_fold b (o.take j) ([], .left)
  change (List.foldl (sideStep b) ([], Side.left) (List.take j o)).1.length ≤ j
  simp at this; omega

theorem length_assocSet_le' {β : Type} (l : List (Nat × β)) (k : Nat) (v : β) :
    (assocSet l k v).length ≤ l.length + 1 := by
  unfold assocSet; split <;> simp

theorem preSides_succ (o : List Nat) (b j : Nat) (hj : j < o.length) :
    preSides o b (j + 1) = sideStep b (preSides o b j) o[j] := by
  simp only [preSides]; rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl

theorem sideLoop_ok {κ : Caps} {s : Core} {L : Loc} {v b : Nat} (hv : L "v" = v) (hb : L "b" = b)
    (hn : L "n" = (s.nodes.getX v).table.length) (hsd : L "sd" = 0) (hvs : v < s.nodes.size)
    (hvr : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hcap : (s.nodes.getX v).table.length + 1
      ≤ κ.lcap .side) :
    ∃ L' c, evalF κ (.loop "j" "n" sideBody) (LK.put s v [] .side) L =
      .ok (LK.put s v (encS (sidesOf ((s.nodes.getX v).table.map (·.1)) b)) .side) L' c ∧
      c ≤ 3 + (s.nodes.getX v).table.length * (80 + 25 * (s.nodes.getX v).table.length) ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → L' r = L r := by
  set o := (s.nodes.getX v).table.map (·.1)
  set n := (s.nodes.getX v).table.length
  have hon : o.length = n := by simp [o, n]
  have hval : ∀ (l : List (Nat × Side)), LK.side.valid (encS l) = true := by
    intro l; simp [LK.valid, encS, sideN_le]
  have hview : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .table =
    (s.nodes.getX v).table := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp [LK.view]
  have hviewS : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .side = encS l
    := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = LK.put s v (encS (preSides o b j).1)
    .side ∧
    L' "sd" = sideN (preSides o b j).2 ∧ ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → L' r = L r
  obtain ⟨s', L', c, he, hc, hs', -, hF⟩ := evalF_loop (x := "j") (n := .var "n") (b := sideBody)
    (s := LK.put s v [] .side) (L := L) (N := n) (by simp [Exp.ev, hn, n]) I (79 + 25 * n)
    ⟨rfl, by rw [hsd]; rfl, fun r _ _ _ => rfl⟩
    (by
      intro j hj s1 L1 ⟨hs1, hsd1, hF1⟩
      subst hs1
      set acc := preSides o b j
      have hjo : j < o.length := by omega
      set L2 := upd L1 "j" j
      have hv2 : L2 "v" = v := by
        simp only [L2,
          Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]; rw [hF1 "v" (by decide)
            (by decide) (by decide), hv]
      have hb2 : L2 "b" = b := by
        simp only [L2,
          Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]; rw [hF1 "b" (by decide)
            (by decide) (by decide), hb]
      have e1 := evalF_assign_ok (κ := κ) (s := LK.put s v (encS acc.1) .side) (L := L2) (x := "e")
        (e := .lrd .table false "v" "j") (v := o[j]) (by
          simp [Exp.ev, hv2, L2, Machine.State.upd, hvt, hview,
            show j < (s.nodes.getX v).table.length by omega, o])
      set L3 := upd L2 "e" o[j]
      set st' : Side := if o[j] == b then .right else acc.2
      have e2 : ∃ c2, evalF κ (.ite ("e" =ₑ "b") ("sd" ::= 1) .skip) (LK.put s v (encS acc.1)
        .side) L3 =
          .ok (LK.put s v (encS acc.1) .side) (upd L3 "sd" (sideN st')) c2 ∧ c2 ≤ 6 := by
        by_cases hm : o[j] = b
        · have hst : sideN st' = 1 := by simp [st', hm, sideN]
          rw [hst]
          exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, L3,
            Machine.State.upd, hb2, hm])
            one_ne_zero (evalF_assign_ok (v := 1) rfl), by simp [Exp.cost]⟩
        · have hst : upd L3 "sd" (sideN st') = L3 := by
            funext r; simp only [Machine.State.upd]; split
            · next h => subst h; simp [L3, L2, Machine.State.upd, hsd1, st', hm]
            · rfl
          rw [hst]
          exact ⟨_, evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, L3, Machine.State.upd,
            hb2, hm])
            evalF_skip, by simp [Exp.cost]⟩
      obtain ⟨c2, e2, hc2⟩ := e2
      set L4 := upd L3 "sd" (sideN st')
      have hL4 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → L4 r = L1 r := fun r h1 h2 h3 => by
        simp [L4, L3, L2, Machine.State.upd, h1, h2, h3]
      obtain ⟨L5, c5, e5, hc5⟩ := assocSetP_agree κ .side (LK.put s v (encS acc.1) .side)
        (Machine.State.setLocs (fun _ => 0) ["i", "x", "y"] [v, o[j], sideN st']) (i := v) (x :=
          o[j])
        (y := sideN st') (by simp [Machine.State.setLocs, Machine.State.upd])
        (by simp [Machine.State.setLocs, Machine.State.upd])
        (by simp [Machine.State.setLocs, Machine.State.upd])
        (by simp [LK.idOk, LK.recOk, hvs]) (by simp [LK.recOk, hvs]) hvr
        (fun a => by simp [LK.valid, sideN_le]) (by
          rw [hviewS]
          have h1 := length_assocSet_le' (encS acc.1) o[j] (sideN st')
          have h2 : acc.1.length ≤ j := length_preSides o b j
          simp only [encS, List.length_map] at h1 ⊢; omega)
      have ec := evalF_call_ok (q := assocSetP .side) (args := [.var "v", .var "e", .var "sd"])
        (ds := [])
        (L := L4) (by simp [evList, Exp.ev, L4, L3, Machine.State.upd, hv2]) e5
      rw [hviewS, assocSet_encS, LK.put_put] at ec
      refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 ec), ?_, ?_, ?_, ?_⟩
      · have h2 : acc.1.length ≤ j := length_preSides o b j
        rw [hviewS] at hc5; simp only [encS, List.length_map] at hc5
        simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil,
          List.length_nil] at hc2 hc5 ⊢
        omega
      · rw [preSides_succ o b j hjo]; rfl
      · rw [preSides_succ o b j hjo]; simp [Machine.State.setLocs, L4, Machine.State.upd,
          sideStep, st']; rfl
      · intro r h1 h2 h3; simp only [Machine.State.setLocs]; exact (hL4 r h1 h2 h3).trans (hF1 r
          h1 h2 h3))
  have hfin : (preSides o b n).1 = sidesOf o b := by
    simp only [preSides, sidesOf_eq]; rw [← hon, List.take_length]
  rw [hs', hfin] at he
  refine ⟨L', c, he, ?_, hF⟩
  have e : n * (1 + (79 + 25 * n)) = n * (80 + 25 * n) := by ring
  simp only [Exp.cost] at hc; rw [e] at hc; omega

/-! ### `fixSides` -/

theorem fixSides_single (ns : Array Node) (e : Nat) (side : List (Nat × Side)) :
    fixSides ns [e] side = if (ns.getX e).draining then
      (lookup side (ns.getX e).t1).map (assocSet side e) else some side := by
  simp only [fixSides]
  split
  · split <;> simp_all
  · rfl

theorem fixSides_prefix {ns : Array Node} {p : Nat → Bool} {o : List Nat} {side0 side : List
  (Nat × Side)}
    (h : fixSides ns (o.filter p) side0 = some side) (j : Nat) :
    ∃ sj, fixSides ns ((o.take j).filter p) side0 = some sj := by
  have := congrArg (fun l => fixSides ns (l.filter p) side0) (List.take_append_drop j o)
  simp only [List.filter_append, fixSides_append] at this
  rw [h] at this
  cases hj : fixSides ns ((o.take j).filter p) side0 with
  | none => rw [hj] at this; simp at this
  | some sj => exact ⟨sj, rfl⟩

theorem length_fixSides_le (ns : Array Node) : ∀ (es : List Nat) (side side' : List (Nat × Side)),
    fixSides ns es side = some side' → side'.length ≤ side.length + es.length
  | [], side, side', h => by
    simp only [fixSides, Option.some.injEq] at h
    subst h
    simp
  | e :: es, side, side', h => by
    simp only [fixSides] at h
    split at h
    · split at h
      · next st _ =>
        have := length_fixSides_le ns es _ side' h
        have := length_assocSet_le' side e st
        simp; omega
      · simp at h
    · have := length_fixSides_le ns es side side' h; simp; omega

theorem findIdx_pair0 (l : List Nat) (x : Nat) :
    (l.map fun e => (e, 0)).findIdx (·.1 == x) < l.length ↔ l.contains x = true := by
  have := List.findIdx_lt_length (p := fun q : Nat × Nat => q.1 == x) (xs := l.map fun e => (e, 0))
  simp only [List.length_map] at this
  rw [this]; simp

theorem fixSides_step (ns : Array Node) (p : Nat → Bool) (o : List Nat) (side0 : List (Nat ×
  Side)) {j : Nat}
    (hj : j < o.length) : fixSides ns ((o.take (j + 1)).filter p) side0 =
      (fixSides ns ((o.take j).filter p) side0).bind fun sj => if p o[j] then fixSides ns [o[j]
        ] sj else some sj := by
  rw [List.take_succ_eq_append_getElem hj, List.filter_append, fixSides_append]
  congr 1; funext sj
  by_cases h : p o[j] = true
  · simp [h]
  · simp [h, fixSides]

/-- One round of `fixSides`: an entry that is a ghost takes the side of its first target. -/
def fixC : Exp := cme{ (r < m || N[e].first ≠ 0) && N[e].draining }
/-- Repair one table entry's recorded side using the live child partition. -/
def fixBody : Stm := cm{
  e := table[v][j].fst
  r ← ‹findP .children›(v, e)
  m := len children[v]
  if ‹fixC› then {
    (f, x) ← ‹lookupP .side›(v, N[e].t1)
    if f then call ‹assocSetP .side›(v, e, x) else fail } }

/-- The entries of `drainEntries` above height 1. -/
def entP (ns : Array Node) (V : Node) (e : Nat) : Bool := V.children.contains e || (ns.getX
  e).first != NIL

theorem fixLoop_ok {κ : Caps} {s : Core} {L : Loc} {v : Nat} {side0 side : List (Nat × Side)}
    (hv : L "v" = v) (hn : L "n" = (s.nodes.getX v).table.length) (hvs : v < s.nodes.size)
    (hvr : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hvc : v < κ.lrec .children)
    (hN : ∀ e ∈ (s.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (h0 : side0.length ≤ (s.nodes.getX v).table.length)
    (hcap : 2 * (s.nodes.getX v).table.length + 1 ≤ κ.lcap .side)
    (hfix : fixSides s.nodes (((s.nodes.getX v).table.map (·.1)).filter (entP s.nodes
      (s.nodes.getX v))) side0 =
      some side) :
    ∃ L' c, evalF κ (.loop "j" "n" fixBody) (LK.put s v (encS side0) .side) L =
      .ok (LK.put s v (encS side) .side) L' c ∧
      c ≤ 3 + (s.nodes.getX v).table.length * (200 + 20 * (s.nodes.getX v).children.length +
        90 * (s.nodes.getX v).table.length) ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → L' r = L r := by
  set o := (s.nodes.getX v).table.map (·.1)
  set n := (s.nodes.getX v).table.length
  set kids := (s.nodes.getX v).children
  set p := entP s.nodes (s.nodes.getX v)
  have hon : o.length = n := by simp [o, n]
  have hval : ∀ (l : List (Nat × Side)), LK.side.valid (encS l) = true := by
    intro l; simp [LK.valid, encS, sideN_le]
  have hview : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .table =
    (s.nodes.getX v).table := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp [LK.view]
  have hviewC : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .children =
      kids.map fun e => (e, 0) := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp [LK.view, kids]
  have hviewS : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .side = encS l
    := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp
  have hfld : ∀ (l : List (Nat × Side)) (f : Fld) j, f.get (LK.put s v (encS l) .side) j = f.get
    s j :=
    fun l f j => (LK.put_keep s v (encS l) .side).1 f j
  let I : Nat → Core → Loc → Prop := fun j s' L' => ∃ sj, fixSides s.nodes ((o.take j).filter p)
    side0 = some sj ∧
    s' = LK.put s v (encS sj) .side ∧ sj.length ≤ n + j ∧
    ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → L' r = L r
  obtain ⟨s', L', c, he, hc, sj, hsj, hs', -, hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var
    "n") (b := fixBody)
    (s := LK.put s v (encS side0) .side) (L := L) (N := n) (by simp [Exp.ev, hn, n]) I
    (199 + 20 * kids.length + 90 * n)
    ⟨side0, by simp [fixSides], rfl, by omega, fun r _ _ _ _ _ _ => rfl⟩
    (by
      intro j hj s1 L1 ⟨sj, hsj, hs1, hlen, hF1⟩
      subst hs1
      have hjo : j < o.length := by omega
      have hjt : j < (s.nodes.getX v).table.length := hj
      have hoj : o[j] = ((s.nodes.getX v).table.getD j (0, 0)).1 := by
        simp [o, List.getElem?_eq_getElem hjt]
      have heN : o[j] < κ.tbl .N := hN _ (List.getElem_mem hjo)
      set S1 := LK.put s v (encS sj) .side
      have hgetN : ∀ e, S1.nodes.getX e = if e = v then
          { s.nodes.getX v with side := sj } else s.nodes.getX e := by
        intro e
        simp only [S1, put_side_encS, OrderMaintenance.Proof.Top.getX_modify']
        by_cases h : e = v
        · subst h; simp [hvs]
        · simp [h]
      have hfirst : ∀ e, (S1.nodes.getX e).first = (s.nodes.getX e).first := fun e => by
        rw [hgetN]; split <;> simp_all
      have hdrain : ∀ e, (S1.nodes.getX e).draining = (s.nodes.getX e).draining := fun e => by
        rw [hgetN]; split <;> simp_all
      have ht1 : ∀ e, (S1.nodes.getX e).t1 = (s.nodes.getX e).t1 := fun e => by
        rw [hgetN]; split <;> simp_all
      set L2 := upd L1 "j" j
      have hv2 : L2 "v" = v := by
        simp only [L2, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
        rw [hF1 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv]
      have e1 := evalF_assign_ok (κ := κ) (s := S1) (L := L2) (x := "e")
        (e := .lrd .table false "v" "j") (v := o[j]) (by
          simp [Exp.ev, hv2, L2, Machine.State.upd, hvt, S1, hview, hjt, hoj])
      set L3 := upd L2 "e" o[j]
      obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .children S1
        (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, o[j] ]) (i := v) (x := o[j])
        (by simp [Machine.State.setLocs, Machine.State.upd])
        (by simp [Machine.State.setLocs, Machine.State.upd]) hvc
      have e2 := evalF_call_ok (q := findP .children) (args := [.var "v", .var "e"]) (ds :=
        ["r"]) (L := L3)
        (by simp [evList, Exp.ev, L3, Machine.State.upd, hv2]) ef
      set L4 := Machine.State.setLocs L3 ["r"] ((findP .children).rets.map Lf)
      have hr4 : L4 "r" = (kids.map fun e => (e, 0)).findIdx (·.1 == o[j]) := by
        simp [L4, findP, Machine.State.setLocs,
          Machine.State.upd, hrf, S1, hviewC]
      have e3 := evalF_assign_ok (κ := κ) (s := S1) (L := L4) (x := "m") (e := .llen .children "v")
        (v := kids.length) (by
          simp [Exp.ev, L4, L3, findP, Machine.State.setLocs,
            Machine.State.upd, hv2, hvc, S1, hviewC])
      set L5 := upd L4 "m" kids.length
      have hL5 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → L5 r = L1 r := fun r h1 h2 h3 h4 => by
        simp [L5, L4, L3, L2, findP, Machine.State.setLocs,
          Machine.State.upd, h1, h2, h3, h4]
      have hcond : fixC.ev κ S1 L5 =
          some (if p o[j] = true ∧ (s.nodes.getX o[j]).draining = true then 1 else 0) := by
        have hr5 : L5 "r" = (kids.map fun e => (e, 0)).findIdx (·.1 == o[j]) := by
          simp [L5, Machine.State.upd, hr4]
        have hc := findIdx_pair0 kids o[j]
        simp only [fixC, Exp.ev, hr5,
          show L5 "m" = kids.length by simp [L5, Machine.State.upd],
          show L5 "e" = o[j] by simp [L5, L4, L3, findP, Machine.State.setLocs,
            Machine.State.upd],
          Option.bind_some, heN, Fld.cap, Fld.get, NF.get, ite_true, Machine.BinOp.eval,
          Machine.UnOp.eval, Option.map_some, Exp.ofNat_def, hfirst, hdrain]
        simp only [p, entP, NIL]
        simp only [hc]
        congr 1
        cases hd : (s.nodes.getX o[j]).draining <;> cases hk : kids.contains o[j] <;>
          by_cases hf : (s.nodes.getX o[j]).first = 0 <;> simp [hf, b2n]
      have hstep := fixSides_step s.nodes p o side0 (j := j) hjo
      rw [hsj, Option.bind_some] at hstep
      obtain ⟨c1e, hc1e⟩ : ∃ c, c = 1 + (Exp.lrd LK.table false (.var "v") (.var "j")).cost :=
        ⟨_, rfl⟩
      by_cases hq : p o[j] = true ∧ (s.nodes.getX o[j]).draining = true
      · obtain ⟨sj1, hsj1⟩ := fixSides_prefix hfix (j + 1)
        rw [hstep, ite_eq_left hq.1, fixSides_single, ite_eq_left hq.2] at hsj1
        obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp hsj1
        obtain ⟨Lk, ck, ek, hfk, hvk, -, -, hck⟩ := lookupP_agree κ .side S1
          (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, (s.nodes.getX o[j]).t1]) (i := v)
          (x := (s.nodes.getX o[j]).t1) (by simp [Machine.State.setLocs, Machine.State.upd])
          (by simp [Machine.State.setLocs, Machine.State.upd]) hvr
        rw [hviewS, lookup_encS, hst] at hfk hvk
        rw [hviewS] at hck
        have e4 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .rd (.n .t1) "e"]) (ds
          := ["f", "x"])
          (L := L5) (by
            simp [evList, Exp.ev, L5, L4, L3, findP, Machine.State.setLocs,
              Machine.State.upd, hv2, heN,
              Fld.cap, Fld.get, NF.get, ht1]) ek
        set L6 := Machine.State.setLocs L5 ["f", "x"] ((lookupP .side).rets.map Lk)
        have hf6 : L6 "f" = 1 := by
          simp [L6, lookupP, Machine.State.setLocs, Machine.State.upd, hfk]
        have hx6 : L6 "x" = sideN st := by
          simp [L6, lookupP, Machine.State.setLocs,
            Machine.State.upd, hvk]
        have hv6 : L6 "v" = v := by
          simp [L6, L5, L4, L3, lookupP, findP, Machine.State.setLocs,
            Machine.State.upd, hv2]
        have he6 : L6 "e" = o[j] := by
          simp [L6, L5, L4, L3, lookupP, findP, Machine.State.setLocs,
            Machine.State.upd]
        obtain ⟨La, ca, ea, hca⟩ := assocSetP_agree κ .side S1
          (Machine.State.setLocs (fun _ => 0) ["i", "x", "y"] [v, o[j], sideN st]) (i := v) (x
            := o[j])
          (y := sideN st) (by simp [Machine.State.setLocs, Machine.State.upd])
          (by simp [Machine.State.setLocs, Machine.State.upd])
          (by simp [Machine.State.setLocs, Machine.State.upd])
          (by simp [S1, LK.idOk, LK.recOk, hvs]) (by simp [S1, LK.recOk, hvs]) hvr
          (fun a => by simp [LK.valid, sideN_le]) (by
            rw [hviewS]
            have h1 := length_assocSet_le' (encS sj) o[j] (sideN st)
            simp only [encS, List.length_map] at h1 ⊢; omega)
        have e5 := evalF_call_ok (q := assocSetP .side) (args := [.var "v", .var "e", .var "x"])
          (ds := [])
          (L := L6) (by simp [evList, Exp.ev, hv6, he6, hx6]) ea
        rw [hviewS, assocSet_encS, LK.put_put] at e5
        rw [hviewS] at hca
        have e6 := evalF_ite_t (κ := κ) (c := .var "f") (f := .fail) (v := 1) (by simp [Exp.ev,
          hf6]) one_ne_zero e5
        refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3
          (evalF_ite_t (v := 1) (by rw [hcond, ite_eq_left hq]) one_ne_zero (evalF_seq_ok2 e4
            e6)))), ?_,
          assocSet sj o[j] st, (by
            rw [hstep, ite_eq_left hq.1, fixSides_single, ite_eq_left hq.2, hst]
            rfl), rfl, ?_, ?_⟩
        · simp only [encS, List.length_map] at hck hca
          rw [hviewC] at hcf; simp only [List.length_map] at hcf
          simp only [Exp.cost, costList, fixC, List.map, List.sum_cons, List.sum_nil,
            List.length_cons,
            List.length_nil] at hcf hck hca ⊢
          omega
        · have := length_assocSet_le' sj o[j] st; omega
        · intro r h1 h2 h3 h4 h5 h6
          simp only [Machine.State.setLocs, L6, lookupP, List.map]
          simp only [Machine.State.upd, ite_eq_right h5, ite_eq_right h6]
          exact (hL5 r h1 h2 h3 h4).trans (hF1 r h1 h2 h3 h4 h5 h6)
      · refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3
          (evalF_ite_f (by rw [hcond, ite_eq_right hq]) evalF_skip))), ?_, sj, ?_, rfl, by
            omega, ?_⟩
        · rw [hviewC] at hcf; simp only [List.length_map] at hcf
          simp only [Exp.cost, costList, fixC, List.map, List.sum_cons, List.sum_nil,
            List.length_cons,
            List.length_nil] at hcf ⊢
          omega
        · rw [hstep]
          by_cases hp : p o[j] = true
          · rw [ite_eq_left hp, fixSides_single, ite_eq_right (fun h => hq ⟨hp, h⟩)]
          · rw [ite_eq_right hp]
        · intro r h1 h2 h3 h4 h5 h6; exact (hL5 r h1 h2 h3 h4).trans (hF1 r h1 h2 h3 h4 h5 h6))
  rw [← hon, List.take_length, hfix] at hsj
  cases hsj
  rw [hs'] at he
  refine ⟨L', c, he, ?_, hF⟩
  have e : n * (1 + (199 + 20 * kids.length + 90 * n)) = n * (200 + 20 * kids.length + 90 * n) := by
    ring
  simp only [Exp.cost] at hc; rw [e] at hc; omega

/-! ### The side list -/

/-- **`startDrain`'s side list**, built in `v`'s side list (boundary `b`). -/
def drainSideS : Stm := cm{
  clear side[v]; sd := 0; n := len table[v]
  for j < n do sideBody
  if 1 < N[v].height then for j < n do fixBody }

theorem drainSideS_ok {κ : Caps} {s : Core} {L : Loc} {v b : Nat} {side : List (Nat × Side)}
    (hv : L "v" = v) (hb : L "b" = b) (hvs : v < s.nodes.size) (hvN : v < κ.tbl .N)
    (hvr : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hvc : v < κ.lrec .children)
    (hN : ∀ e ∈ (s.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : 2 * (s.nodes.getX v).table.length + 1 ≤ κ.lcap .side)
    (hside : drainSide s.nodes (s.nodes.getX v) b = some side) :
    ∃ L' c, evalF κ drainSideS s L = .ok (LK.put s v (encS side) .side) L' c ∧
      c ≤ 20 + (s.nodes.getX v).table.length * (280 + 20 * (s.nodes.getX v).children.length +
        115 * (s.nodes.getX v).table.length) ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → r ≠ "n" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → L' r
        = L r := by
  set n := (s.nodes.getX v).table.length
  set o := (s.nodes.getX v).table.map (·.1)
  have ec : evalF κ (.lclear .side "v") s L = .ok (LK.put s v [] .side) L 3 := by
    simp [evalF, Exp.ev, hv, LK.set, LK.recOk, hvs, LK.valid, hvr, Exp.cost]
  have a1 := evalF_assign_ok (κ := κ) (s := LK.put s v [] .side) (L := L) (x := "sd") (e := (0 :
    Exp)) (v := 0) rfl
  have a2 := evalF_assign_ok (κ := κ) (s := LK.put s v [] .side) (L := upd L "sd" 0) (x := "n")
    (e := .llen .table "v") (v := n) (by
      have : LK.view (LK.put s v [] .side) v .table = (s.nodes.getX v).table := by
        rw [LK.view_put (by simp [LK.recOk, hvs]) (by simp [LK.valid])]; simp [LK.view]
      simp [Exp.ev, Machine.State.upd, hv, hvt, this, n])
  set L1 := upd (upd L "sd" 0) "n" n
  obtain ⟨L2, c2, e2, hc2, hF2⟩ := sideLoop_ok (κ := κ) (s := s) (L := L1) (v := v) (b := b)
    (by simp [L1, Machine.State.upd,
      hv]) (by simp [L1, Machine.State.upd, hb])
    (by simp [L1, Machine.State.upd,
      n]) (by simp [L1, Machine.State.upd]) hvs hvr hvt (by omega)
  set side0 := sidesOf o b
  have hv2 : L2 "v" = v := by
    rw [hF2 "v" (by decide) (by decide) (by decide)]; simp [L1, Machine.State.upd, hv]
  have hn2 : L2 "n" = n := by
    rw [hF2 "n" (by decide) (by decide) (by decide)]; simp [L1, Machine.State.upd]
  have hF2' : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → r ≠ "n" → L2 r = L r := fun r h1 h2 h3 h4 => by
    rw [hF2 r h1 h2 h3]; simp [L1, Machine.State.upd, h3, h4]
  have hh : (1 <ₑ .rd (.n .height) "v" : Exp).ev κ (LK.put s v (encS side0) .side) L2 =
      some (if 1 < (s.nodes.getX v).height then 1 else 0) := by
    have := (LK.put_keep s v (encS side0) .side).1 (.n .height) v
    simp only [Fld.get, NF.get] at this
    simp [Exp.ev, Machine.BinOp.eval, hv2, hvN, Fld.cap, Fld.get, NF.get, this]
  have h0 : side0.length ≤ n := by
    simpa only [side0, o, n, List.length_map] using
      OrderMaintenance.Proof.Top.length_sidesOf o b
  unfold drainSide at hside
  simp only [Node.order] at hside
  by_cases hht : 1 < (s.nodes.getX v).height
  · rw [ite_eq_left hht] at hside
    have hent : drainEntries s.nodes (s.nodes.getX v) = o.filter (entP s.nodes (s.nodes.getX v))
      := by
      unfold drainEntries; simp only [Node.order]
      congr 1; funext e
      simp [entP, show ((s.nodes.getX v).height == 1) = false by simp; omega]
    rw [hent] at hside
    obtain ⟨L3, c3, e3, hc3, hF3⟩ := fixLoop_ok (κ := κ) (s := s) (L := L2) (v := v) (side0 :=
      side0)
      (side := side) hv2 hn2 hvs hvr hvt hvc hN h0 hcap hside
    refine ⟨L3, _, evalF_seq_ok2 ec (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e2
      (evalF_ite_t (by rw [hh, ite_eq_left hht]) one_ne_zero e3)))), ?_, ?_⟩
    · simp only [Exp.cost] at hc2 hc3 ⊢
      nlinarith
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      rw [hF3 r h1 h2 h5 h6 h7 h8, hF2' r h1 h2 h3 h4]
  · rw [ite_eq_right hht] at hside
    cases hside
    refine ⟨L2, _, evalF_seq_ok2 ec (evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e2
      (evalF_ite_f (by rw [hh, ite_eq_right hht]) evalF_skip)))), ?_, ?_⟩
    · simp only [Exp.cost] at hc2 ⊢
      nlinarith
    · intro r h1 h2 h3 h4 _ _ _ _; exact hF2' r h1 h2 h3 h4

end OrderMaintenance.Impl
