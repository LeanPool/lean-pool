/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Data.List.GetD

public import LeanPool.OrderMaintenance.Impl.Loop
public import LeanPool.OrderMaintenance.Impl.Fields
public import LeanPool.OrderMaintenance.Impl.CM


/-!
# M6: a list library for the core language

Procedures on list `k` of record `i`, each with its agreement lemma:
* `findP k`: the position of the first element with key `x` (`List.findIdx`), or the length.
* `assocSetP k`: `assocSet` with key `x` and value `y`.
* `lookupP k`: `lookup` of key `x` (found flag `f`, value `v`).
* `insertIdxP k`: insert `(a, b)` at position `p` (`List.insertIdx`).
* `copyS k`: append list `k` of record `a` to list `k` of record `w`.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)

/-- The key of element `m` of a list (0 past the end). -/
abbrev key (l : List (Nat × Nat)) (m : Nat) : Nat := (l.getD m (0, 0)).1

/-- Procedure finding the first index of a key in a stored list. -/
def findP (k : LK) : Proc where
  name := "find"
  params := ["i", "x"]
  rets := ["r"]
  body := cm{
    n := len k[i]
    r := n
    f := 0
    for j < n do if f = 0 && k[i][j].fst = x then { r := j; f := 1 } }

theorem findIdx_key (l : List (Nat × Nat)) (x : Nat) :
    (∀ m < l.length, key l m ≠ x) → l.findIdx (·.1 == x) = l.length := by
  intro h
  apply List.findIdx_eq_length.mpr
  intro y hy
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
  have := h m hm
  simp only [key, List.getD_eq_getElem _ _ hm] at this
  simpa using this

theorem findIdx_key_eq (l : List (Nat × Nat)) (x r : Nat) (hr : r < l.length) (h1 : key l r = x)
    (h2 : ∀ m < r, key l m ≠ x) : l.findIdx (·.1 == x) = r := by
  apply (List.findIdx_eq hr).mpr
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [key, List.getD_eq_getElem _ _ hr] at h1; simpa using h1
  · have := h2 m hm
    simp only [key] at this; rw [List.getD_eq_getElem _ _ (by omega)] at this; simpa using this

/-- **`findP` computes `findIdx`.** -/
theorem findP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x : Nat} (hi : L "i" = i) (hx :
  L "x" = x)
    (hir : i < κ.lrec k) :
    ∃ L' c, evalF κ (findP k).body s L = .ok s L' c ∧ L' "r" = (k.view s i).findIdx (·.1 == x) ∧
      c ≤ 20 + 20 * (k.view s i).length := by
  set l := k.view s i
  have hlen : (Exp.llen k (.var "i")).ev κ s L = some l.length := by
    simp only [Exp.ev, hi, Option.bind_some, hir, ↓reduceIte, l]
  -- the three assignments
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = s ∧ L' "i" = i ∧ L' "x" = x ∧ L' "n" =
    l.length ∧
    ((L' "f" = 0 ∧ L' "r" = l.length ∧ ∀ m < j, key l m ≠ x) ∨
     (L' "f" = 1 ∧ L' "r" < j ∧ key l (L' "r") = x ∧ ∀ m < L' "r", key l m ≠ x))
  have hn : (Exp.var "n").ev κ s
      (Machine.State.upd (Machine.State.upd (Machine.State.upd L "n" l.length) "r" l.length) "f"
        0) =
      some l.length := by simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte]
  obtain ⟨s', L', c, he, hc, hI⟩ := evalF_loop (x := "j") (b := .ite (("f" =ₑ 0) &&ₑ (.lrd k
    false "i" "j" =ₑ "x"))
    ("r" ::= "j";; "f" ::= 1) .skip) hn I 17
    ⟨rfl, by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hi], by simp only
      [Machine.State.upd,
        String.reduceEq,
        ↓reduceIte, hx], by
          simp only [Machine.State.upd, String.reduceEq, ↓reduceIte],
      Or.inl ⟨by simp only [Machine.State.upd, ↓reduceIte], by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte],
        fun m hm => absurd hm (by omega)⟩⟩
    (by
      intro j hj s1 L1 ⟨hs, h1, h2, h3, h4⟩
      subst hs
      have hjl : j < l.length := hj
      by_cases hf : L1 "f" = 0 ∧ key l j = x
      · refine ⟨s1, Machine.State.upd (Machine.State.upd (Machine.State.upd L1 "j" j) "r" j) "f"
        1, 17,
          ?_, by omega, rfl, by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, h1],
            by
              simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, h2],
          by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, h3], Or.inr ⟨by simp
            only [Machine.State.upd, ↓reduceIte],
            by
              simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, lt_add_iff_pos_right,
                zero_lt_one],
          by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte]; exact hf.2, ?_⟩⟩
        · have : (l.getD j (0, 0)).1 = x := hf.2
          rw [List.getD_eq_getElem _ _ hjl] at this
          simp only [evalF, Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hf.1,
              BinOp.eval, Option.bind_some, h1, Bool.false_eq_true,
              List.getD_eq_getElem?_getD, hir, hjl, and_self, getElem?_pos,
              Option.getD_some, this, h2, ne_eq, one_ne_zero, not_false_eq_true,
              and_true, ite_not, Res.addCost, Res.bind, Exp.cost, Nat.reduceAdd, l]
        · simp only [Machine.State.upd, ite_true]
          rcases h4 with ⟨-, -, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hf.1] at h; simp only [zero_ne_one] at h
      · refine ⟨s1, Machine.State.upd L1 "j" j, 14, ?_, by omega, rfl, by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, h1],
          by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, h2], by simp only
            [Machine.State.upd, String.reduceEq, ↓reduceIte, h3], ?_⟩
        · have hc : ¬(L1 "f" = 0 ∧ (LK.view s1 i k)[j].1 = x) := by
            intro h; apply hf; refine ⟨h.1, ?_⟩
            change (l.getD j (0, 0)).1 = x; rw [List.getD_eq_getElem _ _ hjl]; exact h.2
          have hc' : L1 "f" = 0 → ¬(LK.view s1 i k)[j].1 = x := fun a b => hc ⟨a, b⟩
          simp only [evalF, Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, BinOp.eval,
              Option.bind_some, h1, Bool.false_eq_true, List.getD_eq_getElem?_getD,
              hir, hjl, and_self, getElem?_pos, Option.getD_some, h2, ne_eq,
              ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not, Res.addCost,
              not_and, not_imp, Res.bind, Exp.cost, Nat.reduceAdd, ite_not, l]
          rw [ite_eq_left hc']
        · simp only [Machine.State.upd, show ("f" = "j") = False by decide,
          show ("r" = "j") = False by decide,
            ite_false]
          rcases h4 with ⟨h5, h6, h7⟩ | ⟨h5, h6, h7, h8⟩
          · refine Or.inl ⟨h5, h6, fun m hm => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
            · exact h7 m hm
            · exact fun e => hf ⟨h5, e⟩
          · exact Or.inr ⟨h5, by omega, h7, h8⟩)
  obtain ⟨hss, -, -, -, hI⟩ := hI; rw [hss] at he
  have a1 := evalF_assign_ok (x := "n") hlen
  have a2 := evalF_assign_ok (κ := κ) (s := s) (x := "r") (e := .var "n")
    (L := Machine.State.upd L "n" l.length) (v := l.length) (by
      simp only [Exp.ev, Machine.State.upd, ↓reduceIte])
  have a3 := evalF_assign_ok (κ := κ) (s := s) (x := "f") (e := (0 : Exp))
    (L := Machine.State.upd (Machine.State.upd L "n" l.length) "r" l.length) (v := 0) (by simp
      only [
        Exp.ev])
  refine ⟨L', (1 + (Exp.llen k (.var "i")).cost) + ((1 + (Exp.var "n").cost) + ((1 + (0 :
    Exp).cost) + c)),
    ?_, ?_, ?_⟩
  · change evalF κ (_;; (_;; (_;; _))) s L = _
    rw [evalF_seq_ok a1, evalF_seq_ok a2, evalF_seq_ok a3, he]; rfl
  · rcases hI with ⟨-, h6, h7⟩ | ⟨-, h6, h7, h8⟩
    · rw [h6]; exact (findIdx_key l x h7).symm
    · exact (findIdx_key_eq l x _ h6 h7 h8).symm
  · simp only [Exp.cost] at hc ⊢; nlinarith

/-! ### List replacement -/

theorem Array.ext_getX {α : Type} [Inhabited α] {a b : Array α} (h : a.size = b.size)
    (h2 : ∀ j, a.getX j = b.getX j) : a = b := by
  apply Array.ext h
  intro j h1 h3
  have := h2 j
  simp only [Array.getX, Array.getD, h1, h3, dite_true] at this
  exact this

theorem size_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) :
    (a.setX i v).size = if i < a.size then a.size else i + 1 :=
  OrderMaintenance.Proof.Array.size_setX a i v

theorem setX_setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (u v : α) :
    (a.setX i u).setX i v = a.setX i v := by
  apply Array.ext_getX
  · simp only [size_setX]; split <;> (try split) <;> omega
  · intro j; simp only [OrderMaintenance.Proof.Top.getX_setX']; split <;> rfl

theorem setX_getX {α : Type} [Inhabited α] (a : Array α) {i : Nat} (h : i < a.size) : a.setX i
  (a.getX i) = a := by
  apply Array.ext_getX
  · simp only [size_setX, ite_eq_left h]
  · intro j; simp only [OrderMaintenance.Proof.Top.getX_setX']; split
    · next e => rw [e]
    · rfl

/-- The list can be put back without change. -/
def LK.idOk (s : Core) (i : Nat) : LK → Prop
  | .cin => i < s.cin.size
  | k => k.recOk s i = true

theorem LK.put_put (s : Core) (i : Nat) (l1 l2 : List (Nat × Nat)) (k : LK) :
    k.put (k.put s i l1) i l2 = k.put s i l2 := by
  cases k <;> simp only [LK.put, Array.modify_modify_same, setX_setX] <;> rfl

theorem LK.put_view {s : Core} {i : Nat} {k : LK} (h : k.idOk s i) : k.put s i (k.view s i) = s
  := by
  cases k <;> simp only [LK.idOk, LK.recOk, decide_eq_true_eq] at h
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def, List.map_id']
    congr 1; apply Array.ext
    · simp only [Array.size_modify]
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp only [Array.getX, Array.getD, h, ↓reduceDIte,
          Array.getInternal_eq_getElem]
      · rfl
  · simp only [LK.put, LK.view]
    congr 1; apply Array.ext
    · simp only [Array.size_modify]
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp only [Array.getX, Array.getD, h, ↓reduceDIte,
          Array.getInternal_eq_getElem]
      · rfl
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def, List.map_id']
    congr 1; apply Array.ext
    · simp only [Array.size_modify]
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp only [Array.getX, Array.getD, h, ↓reduceDIte,
          Array.getInternal_eq_getElem]
      · rfl
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def]
    have : ∀ (l : List (Nat × Side)), l.map (fun q => (q.1, sideOfN (sideN q.2))) = l := by
      intro l; induction l with
      | nil => rfl
      | cons q t ih => rw [List.map_cons, ih]; obtain ⟨a, b⟩ := q; cases b <;> rfl
    simp only [this]
    congr 1; apply Array.ext
    · simp only [Array.size_modify]
    · intro j h1 h2; simp only [Array.getElem_modify]; split
      · next e => subst e; simp only [Array.getX, Array.getD, h, ↓reduceDIte,
          Array.getInternal_eq_getElem]
      · rfl
  · simp only [LK.put, LK.view, List.map_map, Function.comp_def, List.map_id']
    rw [setX_getX _ h]
  · subst h; simp only [put, view, ↓reduceIte, List.map_reverse, List.map_map, Function.comp_def,
      List.map_id_fun', id_eq, List.reverse_reverse]

/-- Every element of a valid list is valid on its own. -/
theorem LK.valid_iff (l : List (Nat × Nat)) (k : LK) : k.valid l = true ↔ ∀ q ∈ l, k.valid [q] =
  true := by
  cases k <;> simp only [valid, List.all_eq_true, beq_iff_eq, Prod.forall, List.all_cons,
      List.all_nil, Bool.and_true, implies_true, decide_eq_true_eq]

theorem LK.valid_view (s : Core) (i : Nat) (k : LK) : k.valid (k.view s i) = true := by
  cases k <;> simp only [valid, view, List.all_map, List.all_eq_true, Function.comp_apply,
      BEq.rfl, implies_true, decide_eq_true_eq, Prod.forall, List.map_reverse,
      List.mem_ite_nil_right, List.mem_reverse, List.mem_map, beq_iff_eq, and_imp,
      forall_exists_index, Prod.mk.injEq]
  · intro a b _; cases b <;> simp only [sideN, zero_le, Std.le_refl]
  · intros; omega

theorem LK.set_ok {κ : Caps} {s : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (hr : k.recOk
  s i = true)
    (hv : k.valid l = true) (hc : l.length ≤ κ.lcap k) (hi : i < κ.lrec k) : k.set κ s i l =
      some (k.put s i l) := by
  simp only [set, hr, hv, hc, hi, and_self, ↓reduceIte]

theorem LK.recOk_put (s : Core) (i j : Nat) (l : List (Nat × Nat)) (k k' : LK) :
    k'.recOk (k.put s i l) j = k'.recOk s j := by
  have := (LK.put_keep s i l k).2.1 .N
  cases k' <;> simp only [LK.recOk] <;> simp only [Tbl.size] at this <;> rw [this]

/-! ### `assocSet` -/

/-- The list after `j` rounds of `assocSetP`: entries before `j` with key `x` get value `y`. -/
def preSet (l : List (Nat × Nat)) (x y j : Nat) : List (Nat × Nat) :=
  (l.take j).map (fun p => if p.1 = x then (p.1, y) else p) ++ l.drop j

theorem preSet_zero (l : List (Nat × Nat)) (x y : Nat) : preSet l x y 0 = l := by
  simp only [preSet, List.take_zero, List.map_nil, List.drop_zero, List.nil_append]

theorem length_preSet (l : List (Nat × Nat)) (x y j : Nat) : (preSet l x y j).length = l.length
  := by
  simp only [preSet, List.map_take, List.length_append, List.length_take, List.length_map,
      List.length_drop]; omega

theorem preSet_getD {l : List (Nat × Nat)} {x y j : Nat} (hj : j < l.length) :
    (preSet l x y j).getD j (0, 0) = l[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_preSet]; exact hj)]
  simp only [preSet]
  rw [List.getElem_append_right (by simp )]
  simp only [List.getElem_drop, List.length_map, List.length_take]
  congr 1; omega

theorem preSet_succ {l : List (Nat × Nat)} {x y j : Nat} (hj : j < l.length) :
    preSet l x y (j + 1) = (preSet l x y j).set j (if l[j].1 = x then (l[j].1, y) else l[j]) := by
  apply List.ext_getElem
  · simp only [length_preSet, List.length_set]
  · intro m h1 h2
    simp only [List.getElem_set]
    simp only [preSet] at h1 h2 ⊢
    by_cases hm : m < j
    · rw [List.getElem_append_left (by
      simp only [List.map_take, List.length_take, List.length_map, lt_min_iff]; omega),
      List.getElem_append_left (by
          simp only [List.map_take, List.length_take, List.length_map, lt_min_iff]; omega)]
      simp only [List.map_take, List.getElem_take, List.getElem_map, right_eq_ite_iff]
      intro e; omega
    · by_cases e : m = j
      · subst e
        rw [ite_eq_left rfl, List.getElem_append_left (by
          simp only [List.map_take, List.length_take, List.length_map, lt_min_iff,
            lt_add_iff_pos_right, zero_lt_one, true_and]; omega)]
        simp only [List.map_take, List.getElem_take, List.getElem_map]
      · rw [ite_eq_right (Ne.symm e), List.getElem_append_right (by
        simp only [List.map_take, List.length_take, List.length_map, min_le_iff]; omega),
          List.getElem_append_right (by
            simp only [List.map_take, List.length_take, List.length_map, min_le_iff]; omega)]
        simp only [List.getElem_drop, List.length_map, List.length_take]
        congr 1; omega

theorem preSet_len (l : List (Nat × Nat)) (x y : Nat) :
    preSet l x y l.length = l.map (fun p => if p.1 = x then (p.1, y) else p) := by
      simp only [preSet, List.take_length, List.drop_length, List.append_nil]

theorem assocSet_eq (l : List (Nat × Nat)) (x y : Nat) :
    assocSet l x y = if l.any (·.1 == x) then preSet l x y l.length else l ++ [(x, y)] := by
  unfold assocSet; rw [preSet_len]
  split
  · congr 1; funext p; by_cases h : p.1 = x <;> simp only [h, BEq.rfl, ↓reduceIte, beq_iff_eq]
  · rfl

theorem preSet_noMatch {l : List (Nat × Nat)} {x y : Nat} (h : l.any (·.1 == x) = false) :
    preSet l x y l.length = l := by
  rw [preSet_len]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro p hp
  have : p.1 ≠ x := by
    intro e; have := List.any_eq_false.mp h p hp; simp only [e, BEq.rfl, not_true_eq_false] at this
  simp only [this, ↓reduceIte, id_eq]

theorem valid_preSet {k : LK} {l : List (Nat × Nat)} {x y j : Nat} (hl : k.valid l = true)
    (hy : ∀ a, k.valid [(a, y)] = true) : k.valid (preSet l x y j) = true := by
  rw [LK.valid_iff] at hl ⊢
  intro q hq
  simp only [preSet, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨p, hp, rfl⟩ | hq
  · split
    · exact hy _
    · exact hl p (List.mem_of_mem_take hp)
  · exact hl q (List.mem_of_mem_drop hq)

/-- Procedure replacing an association-list value or appending a fresh key. -/
def assocSetP (k : LK) : Proc where
  name := "assocSet"
  params := ["i", "x", "y"]
  rets := []
  body := cm{
    n := len k[i]; f := 0
    for j < n do if k[i][j].fst = x then { k[i][j].snd := y; f := 1 }
    if f = 0 then append k[i] (x, y) }

theorem take_succ_any (l : List (Nat × Nat)) (x j : Nat) (hj : j < l.length) :
    (l.take (j + 1)).any (·.1 == x) = ((l.take j).any (·.1 == x) || l[j].1 == x) := by
  rw [List.take_succ_eq_append_getElem hj, List.any_append]; simp only [List.any_cons,
      List.any_nil, Bool.or_false]

/-- **`assocSetP` computes `assocSet`.** -/
theorem assocSetP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x y : Nat} (hi : L "i" = i)
  (hx : L "x" = x)
    (hy : L "y" = y) (hid : k.idOk s i) (hr : k.recOk s i = true) (hir : i < κ.lrec k)
    (hyv : ∀ a, k.valid [(a, y)] = true) (hcap : (assocSet (k.view s i) x y).length ≤ κ.lcap k) :
    ∃ L' c, evalF κ (assocSetP k).body s L = .ok (k.put s i (assocSet (k.view s i) x y)) L' c ∧
      c ≤ 40 + 25 * (k.view s i).length := by
  set l := k.view s i
  have hlv : k.valid l = true := LK.valid_view s i k
  have hcap0 : l.length ≤ κ.lcap k := by
    rw [assocSet_eq] at hcap; split at hcap
    · rw [length_preSet] at hcap; exact hcap
    · simp only [List.length_append, List.length_cons, List.length_nil, zero_add] at hcap; omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen k "i") (v :=
    l.length)
    (by simp only [Exp.ev, hi, Option.bind_some, hir, ↓reduceIte, l])
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := Machine.State.upd L "n" l.length) (x := "f")
    (e := (0 : Exp)) (v := 0) rfl
  set L0 := Machine.State.upd (Machine.State.upd L "n" l.length) "f" 0
  have hL0 : ∀ r, r ≠ "n" → r ≠ "f" → L0 r = L r := fun r h1 h2 => by
    simp only [Machine.State.upd, h2, ↓reduceIte, h1, L0]
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = k.put s i (preSet l x y j) ∧ L' "i" = i ∧
    L' "x" = x ∧ L' "y" = y ∧ L' "n" = l.length ∧ L' "f" = if (l.take j).any (·.1 == x) then 1
      else 0
  obtain ⟨s', L', c, he, hc, hI⟩ := evalF_loop (x := "j") (n := .var "n")
    (b := .ite (.lrd k false "i" "j" =ₑ "x") (.lwr k true "i" "j" "y";; "f" ::= 1) .skip)
    (s := s) (L := L0) (N := l.length) (by
      simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, L0]) I 22
    ⟨by rw [preSet_zero, LK.put_view hid], by rw [hL0 "i" (by decide) (by decide), hi],
      by rw [hL0 "x" (by decide) (by decide), hx], by rw [hL0 "y" (by decide) (by decide), hy],
      by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, L0], by simp only
        [Machine.State.upd, ↓reduceIte,
            List.take_zero, List.any_nil,
            Bool.false_eq_true, L0]⟩
    (by
      intro j hj s1 L1 ⟨hs1, hi1, hx1, hy1, hn1, hf1⟩
      subst hs1
      have hview : k.view (k.put s i (preSet l x y j)) i = preSet l x y j := by
        rw [LK.view_put hr (valid_preSet hlv hyv)]; simp only [and_self, ↓reduceIte]
      set L2 := Machine.State.upd L1 "j" j
      have hL2 : ∀ r, r ≠ "j" → L2 r = L1 r := fun r h => by
        simp only [Machine.State.upd, h, ↓reduceIte, L2]
      have hkey : (Exp.lrd k false "i" "j").ev κ (k.put s i (preSet l x y j)) L2 = some l[j].1 := by
        simp only [Exp.ev, hL2 "i" (by decide), hi1,
          show L2 "j" = j by simp only [Machine.State.upd, ↓reduceIte, L2],
          Option.bind_some, hview, length_preSet, preSet_getD hj]
        simp only [hir, hj, and_self, ↓reduceIte, Bool.false_eq_true]
      have hL2j : L2 "j" = j := by simp only [Machine.State.upd, ↓reduceIte, L2]
      have hcond : (Exp.lrd k false "i" "j" =ₑ "x").ev κ (k.put s i (preSet l x y j)) L2 =
          some (if l[j].1 = x then 1 else 0) := by
        simp only [Exp.ev] at hkey ⊢
        rw [hkey]; simp only [hL2 "x" (by decide), hx1, BinOp.eval, Option.bind_some]
      by_cases hm : l[j].1 = x
      · have hw : (preSet l x y j).set j (((preSet l x y j).getD j (0, 0)).1, y) =
            preSet l x y (j + 1) := by
          rw [preSet_succ hj, ite_eq_left hm, preSet_getD hj]
        have hset : k.set κ (k.put s i (preSet l x y j)) i
            ((preSet l x y j).set j (((preSet l x y j).getD j (0, 0)).1, y)) =
            some (k.put s i (preSet l x y (j + 1))) := by
          rw [hw, LK.set_ok (by rw [LK.recOk_put]; exact hr) (valid_preSet hlv hyv)
            (by rw [length_preSet]; exact hcap0) hir, LK.put_put]
        have ew : evalF κ (.lwr k true "i" "j" "y") (k.put s i (preSet l x y j)) L2 =
            .ok (k.put s i (preSet l x y (j + 1))) L2 7 := by
          simp only [evalF, Exp.ev, hL2 "i" (by decide), hi1, hL2j, hL2 "y" (by decide), hy1, hview,
            length_preSet, ite_eq_left hj, ite_true, hset, Exp.cost]
        have ef := evalF_assign_ok (κ := κ) (s := k.put s i (preSet l x y (j + 1))) (L := L2) (x
          := "f")
          (e := (1 : Exp)) (v := 1) rfl
        refine ⟨_, _, _, evalF_ite_t hcond (by
          simp only [hm, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]) (evalF_seq_ok2 ew ef),
          ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Exp.cost, Nat.reduceAdd, Nat.reduceLeDiff]
        · simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hi1, L2]
        · simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hx1, L2]
        · simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hy1, L2]
        · simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hn1, L2]
        · rw [take_succ_any l x j hj]; simp only [Machine.State.upd, ↓reduceIte, hm, BEq.rfl,
            Bool.or_true]
      · have hs : k.put s i (preSet l x y (j + 1)) = k.put s i (preSet l x y j) := by
          rw [preSet_succ hj, ite_eq_right hm]
          congr 1
          conv => rhs; rw [← List.set_getElem_self (as := preSet l x y j) (i := j) (by
            rw [length_preSet]
            exact hj)]
          congr 1
          rw [← preSet_getD (x := x) (y := y) hj, List.getD_eq_getElem]
        refine ⟨_, _, _, evalF_ite_f (by rw [hcond, ite_eq_right hm]) evalF_skip, ?_, hs.symm,
          ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Exp.cost, Nat.reduceAdd, Nat.reduceLeDiff]
        · rw [hL2 "i" (by decide), hi1]
        · rw [hL2 "x" (by decide), hx1]
        · rw [hL2 "y" (by decide), hy1]
        · rw [hL2 "n" (by decide), hn1]
        · have hb : (l[j].1 == x) = false := by simpa using hm
          rw [hL2 "f" (by decide), hf1, take_succ_any l x j hj, hb, Bool.or_false])
  obtain ⟨hs', hi', hx', hy', hn', hf'⟩ := hI
  rw [List.take_of_length_le le_rfl] at hf'
  subst hs'
  have hview : k.view (k.put s i (preSet l x y l.length)) i = preSet l x y l.length := by
    rw [LK.view_put hr (valid_preSet hlv hyv)]; simp only [and_self, ↓reduceIte]
  rw [assocSet_eq] at hcap ⊢
  by_cases ha : l.any (·.1 == x) = true
  · rw [ite_eq_left ha] at hcap ⊢
    rw [ite_eq_left ha] at hf'
    refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he
      (evalF_ite_f (by
        simp only [Exp.ev, hf', BinOp.eval, Option.bind_some, one_ne_zero, ↓reduceIte])
          evalF_skip))), ?_⟩
    simp only [Exp.cost, Nat.reduceAdd] at hc ⊢; omega
  · have ha' : l.any (·.1 == x) = false := by revert ha; cases l.any (·.1 == x) <;> simp only [
      Bool.false_eq_true,
      not_false_eq_true,
      imp_self,
      not_true_eq_false,
      Bool.true_eq_false]
    rw [ite_eq_right ha] at hcap ⊢
    rw [ite_eq_right ha] at hf'
    rw [preSet_noMatch ha'] at hview he
    have hg : evalF κ (.lgrow k "i" "x" "y") (k.put s i l) L' =
        .ok (k.put s i (l ++ [(x, y)])) L' 22 := by
      have hval : k.valid (l ++ [(x, y)]) = true := by
        rw [LK.valid_iff] at hlv ⊢
        intro q hq; simp only [List.mem_append, List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact hlv q hq
        · exact hyv x
      have hso := LK.set_ok (κ := κ) (s := k.put s i l) (i := i) (l := l ++ [(x, y)]) (k := k)
        (by rw [LK.recOk_put]; exact hr) hval hcap hir
      simp only [evalF, Exp.ev, hi', hx', hy', hview, hso, LK.put_put, Exp.cost]
    refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he
      (evalF_ite_t (by simp only [Exp.ev, hf', BinOp.eval, Option.bind_some, ↓reduceIte])
        one_ne_zero hg))), ?_⟩
    simp only [Exp.cost, Nat.reduceAdd] at hc ⊢; omega

/-! ### `lookup` -/

/-- Procedure returning whether an association key exists and its stored value. -/
def lookupP (k : LK) : Proc where
  name := "lookup"
  params := ["i", "x"]
  rets := ["f", "v"]
  body := cm{
    r ← ‹findP k›(i, x); n := len k[i]; f := r < n
    if f then v := k[i][r].snd else v := 0 }

theorem lookup_findIdx (l : List (Nat × Nat)) (x : Nat) :
    lookup l x = if h : l.findIdx (·.1 == x) < l.length then some l[l.findIdx (·.1 == x)].2 else
      none := by
  unfold lookup
  rw [List.find?_eq_getElem?_findIdx]
  split
  · next h => rw [List.getElem?_eq_getElem h]; rfl
  · next h => rw [List.getElem?_eq_none (by omega)]; rfl

/-- **`lookupP` computes `lookup`.** -/
theorem lookupP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x : Nat} (hi : L "i" = i) (hx
  : L "x" = x)
    (hir : i < κ.lrec k) :
    ∃ L' c, evalF κ (lookupP k).body s L = .ok s L' c ∧
      L' "f" = (if (lookup (k.view s i) x).isSome then 1 else 0) ∧ L' "v" = (lookup (k.view s i)
        x).getD 0 ∧
      L' "i" = i ∧ L' "x" = x ∧ c ≤ 60 + 20 * (k.view s i).length := by
  set l := k.view s i
  obtain ⟨L1, c1, e1, hr1, hc1⟩ := findP_agree κ k s (Machine.State.setLocs (fun _ => 0) ["i",
    "x"] [i, x])
    (i := i) (x := x) (by
      simp only [Machine.State.setLocs, Machine.State.upd, String.reduceEq, ↓reduceIte])
    (by simp only [Machine.State.setLocs, Machine.State.upd, ↓reduceIte]) hir
  have ec := evalF_call_ok (q := findP k) (args := [.var "i", .var "x"]) (ds := ["r"]) (L := L)
    (by
      simp only [evList, List.mapM_cons, Exp.ev, hi, hx, List.mapM_nil, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some]) e1
  set L2 := Machine.State.setLocs L ["r"] ((findP k).rets.map L1)
  have hL2 : ∀ r, r ≠ "r" → L2 r = L r := fun r h => by
    simp only [findP, Exp.ofNat_def, List.map_cons, List.map_nil, Machine.State.setLocs,
        Machine.State.upd, h, ↓reduceIte, L2]
  have hr2 : L2 "r" = l.findIdx (·.1 == x) := by
    simp only [findP, Exp.ofNat_def, List.map_cons, hr1, List.map_nil, Machine.State.setLocs,
        Machine.State.upd, ↓reduceIte, L2, l]
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L2) (x := "n") (e := .llen k "i") (v :=
    l.length)
    (by simp only [Exp.ev, hL2 "i" (by decide), hi, Option.bind_some, hir, ↓reduceIte, l])
  set L3 := Machine.State.upd L2 "n" l.length
  set fv := if l.findIdx (·.1 == x) < l.length then 1 else 0
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "f") (e := ("r" <ₑ "n")) (v := fv)
    (by
      simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hr2, BinOp.eval,
        Option.bind_some, List.findIdx_lt_length, beq_iff_eq, Prod.exists, exists_and_right,
        exists_eq_right, L3, fv])
  set L4 := Machine.State.upd L3 "f" fv
  have hL4 : ∀ r, r ≠ "r" → r ≠ "n" → r ≠ "f" → L4 r = L r := fun r h1 h2 h3 => by
    simp only [L4, L3, Machine.State.upd, ite_eq_right h2,
      ite_eq_right h3]; exact hL2 r h1
  have hr4 : L4 "r" = l.findIdx (·.1 == x) := by
    simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hr2, L4, L3]
  by_cases hf : l.findIdx (·.1 == x) < l.length
  · have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L4) (x := "v") (e := .lrd k true "i" "r")
      (v := l[l.findIdx (·.1 == x)].2) (by
        simp only [Exp.ev, hL4 "i" (by decide) (by decide) (by decide), hi, hr4, ↓reduceIte,
            List.getD_eq_getElem?_getD, Option.bind_some, hir, hf, and_self,
            getElem?_pos, Option.getD_some, l]
        )
    refine ⟨_, _, evalF_seq_ok2 ec (evalF_seq_ok2 a2 (evalF_seq_ok2 a3
      (evalF_ite_t (v := 1) (by simp only [Exp.ev, hf, ↓reduceIte, Machine.State.upd, L4, fv])
        one_ne_zero a4))), ?_, ?_, ?_, ?_, ?_⟩
    · rw [lookup_findIdx, dite_eq_left hf]; simp only [Machine.State.upd, String.reduceEq,
        ↓reduceIte, hf, Option.isSome_some, L4, fv]
    · rw [lookup_findIdx, dite_eq_left hf]; simp only [Machine.State.upd, ↓reduceIte,
        Option.getD_some]
    · simp only [Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]; exact (hL4 "i" (by
      decide) (by decide) (by decide)).trans hi
    · simp only [Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]; exact (hL4 "x" (by
      decide) (by decide) (by decide)).trans hx
    · have : (k.view s i).length = l.length := rfl
      simp only [costList, List.map_cons, Exp.cost, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero, Nat.reduceAdd, List.length_cons, List.length_nil, zero_add, ge_iff_le] at hc1 ⊢
      omega
  · have a4 := evalF_assign_ok (κ := κ) (s := s) (L := L4) (x := "v") (e := (0 : Exp)) (v := 0) rfl
    refine ⟨_, _, evalF_seq_ok2 ec (evalF_seq_ok2 a2 (evalF_seq_ok2 a3
      (evalF_ite_f (by simp only [Exp.ev, hf, ↓reduceIte, Machine.State.upd, L4, fv]) a4))), ?_,
        ?_, ?_, ?_, ?_⟩
    · rw [lookup_findIdx, dite_eq_right hf]; simp only [Machine.State.upd, String.reduceEq,
        ↓reduceIte, hf, Option.isSome_none,
        Bool.false_eq_true, L4, fv]
    · rw [lookup_findIdx, dite_eq_right hf]; simp only [Machine.State.upd, ↓reduceIte,
        Option.getD_none]
    · simp only [Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]; exact (hL4 "i" (by
      decide) (by decide) (by decide)).trans hi
    · simp only [Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]; exact (hL4 "x" (by
      decide) (by decide) (by decide)).trans hx
    · have : (k.view s i).length = l.length := rfl
      simp only [costList, List.map_cons, Exp.cost, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero, Nat.reduceAdd, List.length_cons, List.length_nil, zero_add, ge_iff_le] at hc1 ⊢
      omega

/-! ### `insertIdx` -/

/-- The list after `t` swaps of `insertIdxP`: the new element sits at position `n - t`. -/
def bubble (l : List (Nat × Nat)) (x : Nat × Nat) (m : Nat) : List (Nat × Nat) :=
  l.take m ++ x :: l.drop m

theorem length_bubble (l : List (Nat × Nat)) (x : Nat × Nat) (m : Nat) (hm : m ≤ l.length) :
    (bubble l x m).length = l.length + 1 := by
  simp only [bubble, List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

theorem bubble_get_lo {l : List (Nat × Nat)} {x : Nat × Nat} {m q : Nat} (hq : q < m) (hm : m ≤
  l.length) :
    (bubble l x m).getD q (0, 0) = l[q] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_bubble l x m hm]; omega)]
  simp only [bubble]; rw [List.getElem_append_left (by simp ; omega)]; simp only [
      List.getElem_take]

theorem bubble_get_mid {l : List (Nat × Nat)} {x : Nat × Nat} {m : Nat} (hm : m ≤ l.length) :
    (bubble l x m).getD m (0, 0) = x := by
  rw [List.getD_eq_getElem _ _ (by rw [length_bubble l x m hm]; omega)]
  simp only [bubble]; rw [List.getElem_append_right (by simp )]
  simp only [List.length_take, show m - min m l.length = 0 by omega, List.getElem_cons_zero]

theorem bubble_swap {l : List (Nat × Nat)} {x : Nat × Nat} {m : Nat} (h1 : 1 ≤ m) (hm : m ≤
  l.length) :
    ((bubble l x m).set (m - 1) x).set m l[m - 1] = bubble l x (m - 1) := by
  apply List.ext_getElem
  · simp only [bubble, List.length_set, List.length_append, List.length_take, List.length_cons,
      List.length_drop]; omega
  · intro q hq1 hq2
    simp only [List.getElem_set]
    simp only [List.length_set, length_bubble l x m hm] at hq1
    simp only [bubble] at hq2 ⊢
    by_cases e1 : m = q
    · subst e1
      rw [ite_eq_left rfl, List.getElem_append_right (by simp )]
      simp only [List.length_take, show m - min (m - 1) l.length = 1 by omega,
          List.getElem_cons_succ, List.getElem_drop, add_zero]
    · rw [ite_eq_right e1]
      by_cases e2 : m - 1 = q
      · subst e2; rw [ite_eq_left rfl, List.getElem_append_right (by simp )]
        simp only [List.length_take, show m - 1 - min (m - 1) l.length = 0 by omega,
            List.getElem_cons_zero]
      · rw [ite_eq_right e2]
        by_cases hq : q < m - 1
        · rw [List.getElem_append_left (by simp; omega),
          List.getElem_append_left (by simp; omega)]; simp only [List.getElem_take]
        · rw [List.getElem_append_right (by simp; omega),
          List.getElem_append_right (by simp; omega)]
          simp only [List.length_take, List.getElem_cons, List.getElem_drop]
          have hq' : m < q := by omega
          rw [dite_eq_right (by omega), dite_eq_right (by omega)]
          congr 1; omega

theorem insertIdx_take_drop {α : Type} (x : α) : ∀ (p : Nat) (l : List α), p ≤ l.length →
    l.insertIdx p x = l.take p ++ x :: l.drop p
  | 0, l, _ => by
    simp only [List.insertIdx_zero, List.take_zero, List.drop_zero, List.nil_append]
  | p + 1, [], h => by
    simp only [List.length_nil, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, one_ne_zero,
      and_false] at h
  | p + 1, a :: l, h => by
    rw [List.insertIdx_succ_cons, insertIdx_take_drop x p l (by
      simp only [List.length_cons, add_le_add_iff_right] at h; omega)]; simp only [
        List.take_succ_cons,
        List.drop_succ_cons,
        List.cons_append]

theorem bubble_insertIdx (l : List (Nat × Nat)) (x : Nat × Nat) {p : Nat} (hp : p ≤ l.length) :
    bubble l x p = l.insertIdx p x := by
  rw [insertIdx_take_drop x p l hp]; rfl

theorem bubble_len (l : List (Nat × Nat)) (x : Nat × Nat) : bubble l x l.length = l ++ [x] := by
  simp only [bubble, List.take_length, List.drop_length]

/-- Exchange the working pair with one stored list entry. -/
def swapS (k : LK) : Stm := cm{
  q := n - 1 - t
  x1 := k[i][q].fst; y1 := k[i][q].snd
  x2 := k[i][q + 1].fst; y2 := k[i][q + 1].snd
  k[i][q].fst := x2; k[i][q].snd := y2
  k[i][q + 1].fst := x1; k[i][q + 1].snd := y1 }

/-- Procedure inserting a pair at a specified list index. -/
def insertIdxP (k : LK) : Proc where
  name := "insertIdx"
  params := ["i", "p", "a", "b"]
  rets := []
  body := cm{
    n := len k[i]; append k[i] (a, b); c := n ∸ p
    for t < c do ‹swapS k› }

theorem LK.valid_pair_snd {k : LK} {u u' w : Nat} (h : k.valid [(u, w)] = true) : k.valid [(u',
  w)] = true := by
  cases k <;> simp_all [LK.valid]

theorem LK.valid_set {k : LK} {l : List (Nat × Nat)} {q : Nat} {y : Nat × Nat} (hl : k.valid l =
  true)
    (hy : k.valid [y] = true) : k.valid (l.set q y) = true := by
  rw [LK.valid_iff] at hl ⊢
  intro z hz
  rcases List.mem_or_eq_of_mem_set hz with h | h
  · exact hl z h
  · rw [h]; exact hy

/-- A component write to a list that has been put. -/
theorem lwr_put_ok {κ : Caps} {k : LK} {s : Core} {Lc : Loc} {i y w : Nat} {L0 : List (Nat ×
  Nat)} (snd : Bool)
    {jx ex : Exp} (hLi : Lc "i" = i) (hj : jx.ev κ (k.put s i L0) Lc = some y)
    (he : ex.ev κ (k.put s i L0) Lc = some w) (hy : y < L0.length) (hr : k.recOk s i = true)
      (hir : i < κ.lrec k)
    (hv0 : k.valid L0 = true)
    (hvn : k.valid [if snd then ((L0.getD y (0, 0)).1, w) else (w, (L0.getD y (0, 0)).2)] = true)
    (hlen : L0.length ≤ κ.lcap k) :
    evalF κ (.lwr k snd (.var "i") jx ex) (k.put s i L0) Lc =
      .ok (k.put s i (L0.set y (if snd then ((L0.getD y (0, 0)).1, w) else (w, (L0.getD y (0,
        0)).2))))
        Lc (4 + 1 + jx.cost + ex.cost) := by
  have hview : k.view (k.put s i L0) i = L0 := by rw [LK.view_put hr hv0]; simp only [and_self,
      ↓reduceIte]
  have hso := LK.set_ok (κ := κ) (s := k.put s i L0) (i := i)
    (l := L0.set y (if snd then ((L0.getD y (0, 0)).1, w) else (w, (L0.getD y (0, 0)).2))) (k := k)
    (by rw [LK.recOk_put]; exact hr) (LK.valid_set hv0 hvn) (by rw [List.length_set]; exact
      hlen) hir
  rw [LK.put_put] at hso
  simp only [evalF, Exp.ev, hLi, hj, he, hview, ite_eq_left hy, Exp.cost]
  cases snd <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hso ⊢ <;> rw [hso]

theorem getD_set' (l : List (Nat × Nat)) (i j : Nat) (a : Nat × Nat) :
    (l.set i a).getD j (0, 0) = if i = j ∧ i < l.length then a else l.getD j (0, 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < l.length <;> simp only [↓reduceIte, h2, Option.getD_some,
      and_self, Option.getD_none, and_false,
      not_false_eq_true, getElem?_neg]
  · simp only [h1, ↓reduceIte, false_and]

theorem valid_bubble {k : LK} {l : List (Nat × Nat)} {x : Nat × Nat} {m : Nat} (hl : k.valid l =
  true)
    (hx : k.valid [x] = true) : k.valid (bubble l x m) = true := by
  rw [LK.valid_iff] at hl ⊢
  intro z hz
  simp only [bubble, List.mem_append, List.mem_cons] at hz
  rcases hz with h | rfl | h
  · exact hl z (List.mem_of_mem_take h)
  · exact hx
  · exact hl z (List.mem_of_mem_drop h)

theorem swapS_ok {κ : Caps} {k : LK} {s : Core} {L : Loc} {i : Nat} {l : List (Nat × Nat)} {x :
  Nat × Nat}
    {m t : Nat} (hLi : L "i" = i) (hLn : L "n" = l.length) (hLt : L "t" = t) (hm : m + t = l.length)
    (h1 : 1 ≤ m) (hr : k.recOk s i = true) (hir : i < κ.lrec k) (hvl : k.valid l = true)
    (hvx : k.valid [x] = true) (hcap : l.length + 1 ≤ κ.lcap k) :
    ∃ L' c, evalF κ (swapS k) (k.put s i (bubble l x m)) L = .ok (k.put s i (bubble l x (m -
      1))) L' c ∧
      c ≤ 90 ∧ ∀ r, r ≠ "q" → r ≠ "x1" → r ≠ "y1" → r ≠ "x2" → r ≠ "y2" → L' r = L r := by
  have hml : m ≤ l.length := by omega
  set B := bubble l x m
  have hB : B.length = l.length + 1 := length_bubble l x m hml
  have hvB : k.valid B = true := valid_bubble hvl hvx
  have hview : k.view (k.put s i B) i = B := by rw [LK.view_put hr hvB]; simp only [and_self,
      ↓reduceIte]
  have hlm : m - 1 < l.length := by omega
  have g1 : B.getD (m - 1) (0, 0) = l[m - 1] := bubble_get_lo (by omega) hml
  have g2 : B.getD m (0, 0) = x := bubble_get_mid hml
  have hvl1 : k.valid [l[m - 1] ] = true := (LK.valid_iff l k).mp hvl _ (List.getElem_mem hlm)
  -- the reads
  have a0 := evalF_assign_ok (κ := κ) (s := k.put s i B) (L := L) (x := "q") (e := ("n" - 1) -
    "t") (v := m - 1)
    (by
      simp only [Exp.ofNat_def, Exp.sub_def, Exp.ev, hLn, BinOp.eval, Option.bind_some,
        show 1 ≤ l.length by omega, ↓reduceIte, hLt, show t ≤ l.length - 1 by omega,
        Option.some.injEq]
      omega)
  set La := Machine.State.upd L "q" (m - 1)
  have rd : ∀ (Lx : Loc) (snd : Bool) (jx : Exp) (y : Nat), Lx "i" = i → jx.ev κ (k.put s i B)
    Lx = some y →
      y < B.length → (Exp.lrd k snd "i" jx).ev κ (k.put s i B) Lx =
        some (if snd then (B.getD y (0, 0)).2 else (B.getD y (0, 0)).1) := by
    intro Lx snd jx y h1 h2 h3; simp only [Exp.ev, h1, h2, List.getD_eq_getElem?_getD,
        Option.bind_some, hir, hview, h3, and_self, ↓reduceIte,
        getElem?_pos, Option.getD_some]
  have hBl1 : m - 1 < B.length := by omega
  have hBl2 : m < B.length := by omega
  have hLai : La "i" = i := by
    simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hLi, La]
  have hLaq : La "q" = m - 1 := by simp only [Machine.State.upd, ↓reduceIte, La]
  have e1 := evalF_assign_ok (κ := κ) (s := k.put s i B) (L := La) (x := "x1") (e := .lrd k
    false "i" "q")
    (v := l[m - 1].1) (by
      rw [rd La false (.var "q") (m - 1) hLai (by simp only [Exp.ev, hLaq]) hBl1, g1]
      rfl)
  set Lb := Machine.State.upd La "x1" l[m - 1].1
  have e2 := evalF_assign_ok (κ := κ) (s := k.put s i B) (L := Lb) (x := "y1") (e := .lrd k true
    "i" "q")
    (v := l[m - 1].2) (by
      rw [rd Lb true (.var "q") (m - 1) (by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hLai, Lb])
        (by simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hLaq, Lb]) hBl1,
          g1]; rfl)
  set Lc := Machine.State.upd Lb "y1" l[m - 1].2
  have e3 := evalF_assign_ok (κ := κ) (s := k.put s i B) (L := Lc) (x := "x2") (e := .lrd k
    false "i" ("q" + 1))
    (v := x.1) (by
      rw [rd Lc false ("q" + 1) m (by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hLai, Lc, Lb])
        (by
          simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hLaq, BinOp.eval,
            Option.bind_some, Option.some.injEq, Lc, Lb]; omega) hBl2, g2]; rfl)
  set Ld := Machine.State.upd Lc "x2" x.1
  have e4 := evalF_assign_ok (κ := κ) (s := k.put s i B) (L := Ld) (x := "y2") (e := .lrd k true
    "i" ("q" + 1))
    (v := x.2) (by
      rw [rd Ld true ("q" + 1) m (by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hLai, Ld, Lc, Lb])
        (by
          simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hLaq, BinOp.eval,
            Option.bind_some, Option.some.injEq, Ld, Lc, Lb]; omega) hBl2, g2]; rfl)
  set Le := Machine.State.upd Ld "y2" x.2
  have hLe : ∀ r, r ≠ "q" → r ≠ "x1" → r ≠ "y1" → r ≠ "x2" → r ≠ "y2" → Le r = L r := by
    intro r h1 h2 h3 h4 h5; simp only [Machine.State.upd, h5, ↓reduceIte, h4, h3, h2, h1, Le, Ld,
        Lc, Lb, La]
  have hLei : Le "i" = i := by
    rw [hLe "i" (by decide) (by decide) (by decide) (by decide) (by decide), hLi]
  have hLeq : Le "q" = m - 1 := by
    simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hLaq, Le, Ld, Lc, Lb]
  have hLex1 : Le "x1" = l[m - 1].1 := by
    simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, Le, Ld, Lc, Lb]
  have hLey1 : Le "y1" = l[m - 1].2 := by
    simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, Le, Ld, Lc]
  have hLex2 : Le "x2" = x.1 := by
    simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, Le, Ld]
  have hLey2 : Le "y2" = x.2 := by simp only [Machine.State.upd, ↓reduceIte, Le]
  -- the writes
  set B1 := B.set (m - 1) (x.1, (B.getD (m - 1) (0, 0)).2)
  have hv1 : k.valid [(x.1, (B.getD (m - 1) (0, 0)).2)] = true := by
    rw [g1]; exact LK.valid_pair_snd hvl1
  have w1 := lwr_put_ok (κ := κ) (k := k) (s := s) (Lc := Le) (i := i) (y := m - 1) (w := x.1)
    (L0 := B) false
    (jx := .var "q") (ex := .var "x2") hLei (by simp only [Exp.ev, hLeq]) (by
      simp only [Exp.ev, hLex2]) hBl1 hr hir hvB
    hv1 (by omega)
  have hvB1 : k.valid B1 = true := LK.valid_set hvB hv1
  have hB1l : B1.length = l.length + 1 := by
    simp only [List.getD_eq_getElem?_getD, List.length_set, hB,  B1]
  set B2 := B1.set (m - 1) ((B1.getD (m - 1) (0, 0)).1, x.2)
  have hv2 : k.valid [((B1.getD (m - 1) (0, 0)).1, x.2)] = true := LK.valid_pair_snd hvx
  have w2 := lwr_put_ok (κ := κ) (k := k) (s := s) (Lc := Le) (i := i) (y := m - 1) (w := x.2)
    (L0 := B1) true
    (jx := .var "q") (ex := .var "y2") hLei (by simp only [Exp.ev, hLeq]) (by
      simp only [Exp.ev, hLey2]) (by omega) hr hir
    hvB1 hv2 (by omega)
  have hvB2 : k.valid B2 = true := LK.valid_set hvB1 hv2
  have hB2l : B2.length = l.length + 1 := by
    simp only [List.getD_eq_getElem?_getD, List.length_set, hB1l,  B2]
  set B3 := B2.set m (l[m - 1].1, (B2.getD m (0, 0)).2)
  have hg3 : B2.getD m (0, 0) = x := by
    simp only [B2, B1, getD_set',
      List.length_set]; rw [ite_eq_right (by omega), ite_eq_right (by omega), g2]
  have hv3 : k.valid [(l[m - 1].1, (B2.getD m (0, 0)).2)] = true := by
    rw [hg3]; exact LK.valid_pair_snd hvx
  have w3 := lwr_put_ok (κ := κ) (k := k) (s := s) (Lc := Le) (i := i) (y := m) (w := l[m -
    1].1) (L0 := B2) false
    (jx := "q" + 1) (ex := .var "x1") hLei (by
      simp only [Exp.ev, hLeq, BinOp.eval, Option.bind_some, Option.some.injEq]; omega)
    (by simp only [Exp.ev, hLex1]) (by omega) hr hir hvB2 hv3 (by omega)
  have hvB3 : k.valid B3 = true := LK.valid_set hvB2 hv3
  have hB3l : B3.length = l.length + 1 := by
    simp only [List.getD_eq_getElem?_getD, List.length_set, hB2l,  B3]
  set B4 := B3.set m ((B3.getD m (0, 0)).1, l[m - 1].2)
  have hv4 : k.valid [((B3.getD m (0, 0)).1, l[m - 1].2)] = true := LK.valid_pair_snd hvl1
  have w4 := lwr_put_ok (κ := κ) (k := k) (s := s) (Lc := Le) (i := i) (y := m) (w := l[m -
    1].2) (L0 := B3) true
    (jx := "q" + 1) (ex := .var "y1") hLei (by
      simp only [Exp.ev, hLeq, BinOp.eval, Option.bind_some, Option.some.injEq]; omega)
    (by simp only [Exp.ev, hLey1]) (by omega) hr hir hvB3 hv4 (by omega)
  have g31 : B3.getD m (0, 0) = (l[m - 1].1, x.2) := by
    change (B2.set m _).getD m (0, 0) = _
    rw [getD_set', ite_eq_left ⟨rfl, by rw [hB2l]; omega⟩, hg3]
  have g11 : B1.getD (m - 1) (0, 0) = (x.1, l[m - 1].2) := by
    change (B.set (m - 1) _).getD (m - 1) (0, 0) = _
    rw [getD_set', ite_eq_left ⟨rfl, by rw [hB]; omega⟩, g1]
  have hB4 : B3.set m ((B3.getD m (0, 0)).1, l[m - 1].2) = bubble l x (m - 1) := by
    rw [← bubble_swap (x := x) h1 hml, g31]
    change (B2.set m (l[m - 1].1, (B2.getD m (0, 0)).2)).set m (l[m - 1].1, l[m - 1].2) = _
    rw [hg3, List.set_set]
    change (B1.set (m - 1) ((B1.getD (m - 1) (0, 0)).1, x.2)).set m (l[m - 1].1, l[m - 1].2) = _
    rw [g11]
    change ((B.set (m - 1) (x.1, (B.getD (m - 1) (0, 0)).2)).set (m - 1) (x.1, x.2)).set m
      (l[m - 1].1, l[m - 1].2) = _
    rw [List.set_set]
  simp only [  ite_true] at w4
  rw [hB4] at w4
  simp only [Bool.false_eq_true, ite_false, ite_true] at w1 w2 w3
  refine ⟨Le, _, evalF_seq_ok2 a0 (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3
    (evalF_seq_ok2 e4
    (evalF_seq_ok2 w1 (evalF_seq_ok2 w2 (evalF_seq_ok2 w3 w4))))))), ?_, hLe⟩
  simp only [Exp.ofNat_def, Exp.sub_def, Exp.cost, Nat.reduceAdd, Nat.reduceLeDiff]

/-- **`insertIdxP` computes `insertIdx`.** -/
theorem insertIdxP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i p a b : Nat} (hi : L "i" =
  i) (hp : L "p" = p)
    (ha : L "a" = a) (hb : L "b" = b) (hr : k.recOk s i = true) (hir : i < κ.lrec k)
    (hab : k.valid [(a, b)] = true) (hpl : p ≤ (k.view s i).length)
    (hcap : (k.view s i).length + 1 ≤ κ.lcap k) :
    ∃ L' c, evalF κ (insertIdxP k).body s L = .ok (k.put s i ((k.view s i).insertIdx p (a, b)))
      L' c ∧
      c ≤ 50 + 91 * (k.view s i).length := by
  set l := k.view s i
  have hvl : k.valid l = true := LK.valid_view s i k
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen k "i") (v :=
    l.length)
    (by simp only [Exp.ev, hi, Option.bind_some, hir, ↓reduceIte, l])
  set L1 := Machine.State.upd L "n" l.length
  have hval : k.valid (l ++ [(a, b)]) = true := by
    rw [LK.valid_iff] at hvl ⊢
    intro q hq; simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact hvl q hq
    · exact hab
  have eg : evalF κ (.lgrow k "i" "a" "b") s L1 = .ok (k.put s i (bubble l (a, b) l.length)) L1
    22 := by
    rw [bubble_len]
    have hso : k.set κ s i (k.view s i ++ [(a, b)]) = some (k.put s i (l ++ [(a, b)])) :=
      LK.set_ok hr hval (by simp only [List.length_append, List.length_singleton]; exact hcap) hir
    simp only [evalF, Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hi, ha, hb, hso,
        Exp.cost, mul_one, Nat.reduceAdd, L1]
  have a3 := evalF_assign_ok (κ := κ) (s := k.put s i (bubble l (a, b) l.length)) (L := L1) (x
    := "c")
    (e := .monus "n" "p") (v := l.length - p)
    (Exp.ev_monus κ _ L1 (by simp only [Exp.ev, Machine.State.upd, ↓reduceIte, L1]) (by
      simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, hp, L1]))
  set L3 := Machine.State.upd L1 "c" (l.length - p)
  let I : Nat → Core → Loc → Prop := fun t s' L' => s' = k.put s i (bubble l (a, b) (l.length -
    t)) ∧
    L' "i" = i ∧ L' "n" = l.length
  obtain ⟨s', L', c, he, hc, hs', -, -⟩ := evalF_loop (κ := κ) (x := "t") (n := .var "c") (b :=
    swapS k)
    (s := k.put s i (bubble l (a, b) l.length)) (L := L3) (N := l.length - p)
    (by simp only [Exp.ev, Machine.State.upd, ↓reduceIte, L3]) I 90
    ⟨by simp, by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hi, L3, L1], by simp
      only [
        Machine.State.upd,
        String.reduceEq,
        ↓reduceIte,
        L3, L1]⟩
    (by
      intro t ht s1 L1' ⟨hs1, hi1, hn1⟩
      subst hs1
      obtain ⟨L2, c2, e2, hc2, hF2⟩ := swapS_ok (κ := κ) (k := k) (s := s) (L :=
        Machine.State.upd L1' "t" t)
        (i := i) (l := l) (x := (a, b)) (m := l.length - t) (t := t)
        (by simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, hi1]) (by simp only
          [Machine.State.upd, String.reduceEq, ↓reduceIte, hn1])
        (by simp only [Machine.State.upd, ↓reduceIte]) (by omega) (by omega) hr hir hvl hab (by
          omega)
      refine ⟨_, L2, c2, e2, hc2, by rw [show l.length - (t + 1) = l.length - t - 1 by omega],
        ?_, ?_⟩
      · rw [hF2 "i" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp only [
          Machine.State.upd,
          String.reduceEq,
          ↓reduceIte,
          hi1]
      · rw [hF2 "n" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp only [
          Machine.State.upd,
          String.reduceEq,
          ↓reduceIte,
          hn1])
  rw [hs', show l.length - (l.length - p) = p by omega, bubble_insertIdx l (a, b) hpl] at he
  refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 eg (evalF_seq_ok2 a3 he)), ?_⟩
  have : (l.length - p) * (1 + 90) ≤ 91 * l.length := by
    have := Nat.mul_le_mul_right (1 + 90) (Nat.sub_le l.length p); omega
  simp only [Exp.cost, Nat.reduceAdd, Exp.cost_monus, mul_one, ge_iff_le] at hc ⊢; omega

/-! ### Copying a list -/

/-- Append one entry of the source list to the destination list. -/
def copyBody (k : LK) : Stm := cm{ append k[w] (k[a][j].fst, k[a][j].snd) }
/-- Append the source list to the destination list in list order. -/
def copyS (k : LK) : Stm := cm{ n := len k[a]; for j < n do ‹copyBody k› }

/-- **`copyS` appends list `k` of record `a` to that of record `w`** (`w ≠ a`). -/
theorem copyS_ok {κ : Caps} {k : LK} {s : Core} {L : Loc} {a w : Nat} (ha : L "a" = a) (hw : L
  "w" = w)
    (hne : w ≠ a) (hid : k.idOk s w) (hr : k.recOk s w = true) (hra : a < κ.lrec k) (hrw : w <
      κ.lrec k)
    (hcap : (k.view s w).length + (k.view s a).length ≤ κ.lcap k) :
    ∃ L' c, evalF κ (copyS k) s L = .ok (k.put s w (k.view s w ++ k.view s a)) L' c ∧
      c ≤ 5 + 40 * (k.view s a).length ∧ ∀ r, r ≠ "n" → r ≠ "j" → L' r = L r := by
  set la := k.view s a
  set lw := k.view s w
  have hvw := LK.valid_view s w k
  have hva := LK.valid_view s a k
  have hval : ∀ j, k.valid (lw ++ la.take j) = true := by
    intro j; rw [LK.valid_iff] at hvw hva ⊢
    intro q hq; simp only [List.mem_append] at hq
    rcases hq with hq | hq
    · exact hvw q hq
    · exact hva q (List.mem_of_mem_take hq)
  have hviewA : ∀ l, k.valid l = true → k.view (k.put s w l) a = la := by
    intro l hl; rw [LK.view_put hr hl]; simp only [Ne.symm hne, and_false, ↓reduceIte]; rfl
  have hviewW : ∀ l, k.valid l = true → k.view (k.put s w l) w = l := by
    intro l hl; rw [LK.view_put hr hl]; simp only [and_self, ↓reduceIte]
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "n") (e := .llen k "a") (v :=
    la.length)
    (by simp only [Exp.ev, ha, Option.bind_some, hra, ↓reduceIte, la])
  obtain ⟨S', L', c, he, hc, hs', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "n") (b :=
    copyBody k)
    (s := s) (L := Machine.State.upd L "n" la.length) (N := la.length)
    (by simp only [Exp.ev, Machine.State.upd, ↓reduceIte])
    (fun j S L' => S = k.put s w (lw ++ la.take j) ∧ ∀ r, r ≠ "n" → r ≠ "j" → L' r = L r) 32
    ⟨by simp only [List.take_zero, List.append_nil, LK.put_view hid, lw], fun r h1 _ => by simp
      only [Machine.State.upd, h1,
        ↓reduceIte]⟩
    (by
      intro j hj S1 L1 ⟨hS1, hF1⟩
      subst hS1
      set L2 := Machine.State.upd L1 "j" j
      have h2a : L2 "a" = a := by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, L2]; rw [hF1 "a" (by decide)
          (by decide), ha]
      have h2w : L2 "w" = w := by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, L2]; rw [hF1 "w" (by decide)
          (by decide), hw]
      have hso := LK.set_ok (κ := κ) (s := k.put s w (lw ++ la.take j)) (i := w)
        (l := lw ++ la.take (j + 1)) (k := k) (by rw [LK.recOk_put]; exact hr) (hval (j + 1))
        (by simp only [List.length_append, List.length_take]; omega) hrw
      rw [LK.put_put] at hso
      have hl : lw ++ la.take (j + 1) = (lw ++ la.take j) ++ [(la[j].1, la[j].2)] := by
        rw [List.take_succ_eq_append_getElem hj]; simp only [List.take_append_getElem,
            Prod.mk.eta, List.append_assoc]
      refine ⟨_, L2, _, ?_, le_refl _, rfl, fun r h1 h2 => by
        simp only [Machine.State.upd, h2, ↓reduceIte, L2]; exact hF1 r h1 h2⟩
      simp only [copyBody, evalF, Exp.ev, h2a, h2w,
        show L2 "j" = j by simp only [Machine.State.upd, ↓reduceIte, L2],
        Option.bind_some, hra, hviewA _ (hval j), hj, and_self, ite_true, hviewW _ (hval j),
          Exp.cost]
      simp only [List.getD_eq_getElem _ _ hj, Bool.false_eq_true, ite_false,  ← hl, hso])
  rw [hs', List.take_of_length_le le_rfl] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  simp only [Exp.cost] at hc ⊢; omega

end OrderMaintenance.Impl
