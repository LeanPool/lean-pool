/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Lang


/-!
# M6: compiling the core language to the machine

**Layout.** The core in slot `p` (0 or 1) owns the machine arrays `1000·p + code`:
* one array per record field (codes 10–99), indexed by record, of capacity `κ.tbl`;
* one array per plain number array (`AF`), of capacity `κ.arr`;
* one single-cell array per scalar, and per table size (codes 100–103);
* the parameters, one cell each (code 110).

`Enc p κ s m` says that machine state `m` holds core `s` in slot `p`.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr BinOp UnOp)

/-! ### Codes -/

/-- Fixed numeric column encoding of a element selector. -/
def EF.idx : EF → Nat
  | .next => 0 | .prev => 1 | .grp => 2 | .lab => 3 | .dead => 4 | .h => 5
/-- Fixed numeric column encoding of a group selector. -/
def GF.idx : GF → Nat
  | .next => 0 | .prev => 1 | .first => 2 | .last => 3 | .chk => 4 | .lab => 5 | .size => 6
  | .st => 7 | .src => 8 | .l => 9 | .r => 10 | .dead => 11
/-- Fixed numeric column encoding of a chunk selector. -/
def CF.idx : CF → Nat
  | .next => 0 | .prev => 1 | .first => 2 | .last => 3 | .size => 4 | .st => 5 | .src => 6
  | .l => 7 | .r => 8 | .tag => 9 | .dead => 10
/-- Fixed numeric column encoding of a top-tree node selector. -/
def NF.idx : NF → Nat
  | .height => 0 | .livePar => 1 | .weight => 2 | .first => 3 | .last => 4 | .draining => 5
  | .t1 => 6 | .t2 => 7 | .overflow => 8 | .dead => 9
/-- Fixed numeric column encoding of a plain array selector. -/
def AF.idx : AF → Nat
  | .pqHead => 0 | .pqNext => 1 | .pqPrev => 2 | .pqWhere => 3 | .nbNext => 4 | .nbPrev => 5
  | .lpar => 6
/-- Fixed numeric column encoding of a core scalar selector. -/
def SF.idx : SF → Nat
  | .count => 0 | .head => 1 | .tail => 2 | .firstGroup => 3 | .firstChunk => 4 | .notReady => 5
  | .fallbacks => 6 | .pqHi => 7 | .pqLo => 8
/-- Fixed numeric column encoding of a record table selector. -/
def Tbl.idx : Tbl → Nat
  | .E => 0 | .G => 1 | .C => 2 | .N => 3
/-- Fixed numeric column encoding of a parameter selector. -/
def PF.idx : PF → Nat
  | .N => 0 | .L => 1 | .G => 2 | .T => 3 | .theta => 4 | .Be => 5 | .Bg => 6 | .De => 7
  | .Dg => 8 | .KG => 9 | .KC => 10 | .KR => 11 | .a => 12 | .s => 13 | .beta => 14 | .H => 15

theorem EF.idx_inj {k k' : EF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [EF.idx] at h)
theorem GF.idx_inj {k k' : GF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [GF.idx] at h)
theorem CF.idx_inj {k k' : CF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [CF.idx] at h)
theorem NF.idx_inj {k k' : NF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [NF.idx] at h)
theorem AF.idx_inj {k k' : AF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [AF.idx] at h)
theorem SF.idx_inj {k k' : SF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [SF.idx] at h)
theorem Tbl.idx_inj {k k' : Tbl} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [Tbl.idx] at h)

theorem EF.idx_lt (k : EF) : k.idx < 6 := by cases k <;> decide
theorem GF.idx_lt (k : GF) : k.idx < 12 := by cases k <;> decide
theorem CF.idx_lt (k : CF) : k.idx < 11 := by cases k <;> decide
theorem NF.idx_lt (k : NF) : k.idx < 10 := by cases k <;> decide
theorem AF.idx_lt (k : AF) : k.idx < 7 := by cases k <;> decide
theorem SF.idx_lt (k : SF) : k.idx < 9 := by cases k <;> decide
theorem Tbl.idx_lt (k : Tbl) : k.idx < 4 := by cases k <;> decide
theorem PF.idx_lt (k : PF) : k.idx < 16 := by cases k <;> decide

/-- Disjoint numeric encoding of a typed field selector. -/
def Fld.code : Fld → Nat
  | .e k => 10 + k.idx | .g k => 20 + k.idx | .c k => 40 + k.idx | .n k => 60 + k.idx
  | .a k => 80 + k.idx | .s k => 90 + k.idx

theorem Fld.code_lt (f : Fld) : 10 ≤ f.code ∧ f.code < 100 := by
  cases f with
  | e k => have := k.idx_lt; simp [Fld.code]; omega
  | g k => have := k.idx_lt; simp [Fld.code]; omega
  | c k => have := k.idx_lt; simp [Fld.code]; omega
  | n k => have := k.idx_lt; simp [Fld.code]; omega
  | a k => have := k.idx_lt; simp [Fld.code]; omega
  | s k => have := k.idx_lt; simp [Fld.code]; omega

theorem Fld.code_inj {f g : Fld} (h : f.code = g.code) : f = g := by
  cases f with
  | e k => cases g with
    | e k' => simp [Fld.code] at h; rw [EF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | g k => cases g with
    | g k' => simp [Fld.code] at h; rw [GF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | c k => cases g with
    | c k' => simp [Fld.code] at h; rw [CF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | n k => cases g with
    | n k' => simp [Fld.code] at h; rw [NF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | a k => cases g with
    | a k' => simp [Fld.code] at h; rw [AF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | s k => cases g with
    | s k' => simp [Fld.code] at h; rw [SF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega

/-- Fixed numeric column encoding of a list kind selector. -/
def LK.idx : LK → Nat
  | .children => 0 | .table => 1 | .inTab => 2 | .side => 3 | .cin => 4 | .freeG => 5
/-- Fixed numeric column encoding of a optional-state field selector. -/
def OF.idx : OF → Nat
  | .prepOn => 0 | .prepChunk => 1 | .prepH => 2 | .prepBelow => 3 | .prepTag => 4 | .jobOn => 5
  | .jobX => 6 | .jobY => 7 | .jobZ => 8 | .jobT => 9 | .jobA => 10 | .jobB => 11 | .jobC => 12
  | .jobD => 13

theorem LK.idx_lt (k : LK) : k.idx < 6 := by cases k <;> decide
theorem OF.idx_lt (k : OF) : k.idx < 14 := by cases k <;> decide
theorem LK.idx_inj {k k' : LK} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [LK.idx] at h)
theorem OF.idx_inj {k k' : OF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [OF.idx] at h)

/-- The machine arrays of a core. -/
inductive Slot
  | f (f : Fld) | sz (t : Tbl) | prm | lst (k : LK) (snd : Bool) | len (k : LK) | path | opt (o : OF)

/-- Disjoint numeric encoding of an entire machine-array slot. -/
def Slot.code : Slot → Nat
  | .f x => x.code
  | .sz t => 100 + t.idx
  | .prm => 110
  | .lst k b => 130 + 3 * k.idx + (if b then 1 else 0)
  | .len k => 132 + 3 * k.idx
  | .path => 160
  | .opt o => 170 + o.idx

theorem Slot.code_lt (sl : Slot) : sl.code < 1000 := by
  cases sl with
  | f x => have := x.code_lt; simp [Slot.code]; omega
  | sz t => have := t.idx_lt; simp [Slot.code]; omega
  | prm => simp [Slot.code]
  | lst k b => have := k.idx_lt; cases b <;> simp [Slot.code] <;> omega
  | len k => have := k.idx_lt; simp [Slot.code]; omega
  | path => simp [Slot.code]
  | opt o => have := o.idx_lt; simp [Slot.code]; omega

theorem Slot.code_inj {a b : Slot} (h : a.code = b.code) : a = b := by
  cases a with
  | f x =>
    have := x.code_lt
    cases b with
    | f g => simp [Slot.code] at h; rw [Fld.code_inj h]
    | sz t => have := t.idx_lt; simp [Slot.code] at h; omega
    | prm => simp [Slot.code] at h; omega
    | lst k c => have := k.idx_lt; cases c <;> simp [Slot.code] at h <;> omega
    | len k => have := k.idx_lt; simp [Slot.code] at h; omega
    | path => simp [Slot.code] at h; omega
    | opt o => have := o.idx_lt; simp [Slot.code] at h; omega
  | sz t =>
    have := t.idx_lt
    cases b with
    | f g => have := g.code_lt; simp [Slot.code] at h; omega
    | sz t' => simp [Slot.code] at h; rw [Tbl.idx_inj h]
    | prm => simp [Slot.code] at h; omega
    | lst k c => have := k.idx_lt; cases c <;> simp [Slot.code] at h <;> omega
    | len k => have := k.idx_lt; simp [Slot.code] at h; omega
    | path => simp [Slot.code] at h; omega
    | opt o => have := o.idx_lt; simp [Slot.code] at h; omega
  | prm =>
    cases b with
    | f g => have := g.code_lt; simp [Slot.code] at h; omega
    | sz t' => have := t'.idx_lt; simp [Slot.code] at h; omega
    | prm => rfl
    | lst k c => have := k.idx_lt; cases c <;> simp [Slot.code] at h <;> omega
    | len k => have := k.idx_lt; simp [Slot.code] at h; omega
    | path => simp [Slot.code] at h
    | opt o => have := o.idx_lt; simp [Slot.code] at h; omega
  | lst k c =>
    have := k.idx_lt
    cases b with
    | f g => have := g.code_lt; cases c <;> simp [Slot.code] at h <;> omega
    | sz t' => have := t'.idx_lt; cases c <;> simp [Slot.code] at h <;> omega
    | prm => cases c <;> simp [Slot.code] at h <;> omega
    | lst k' c' =>
      have := k'.idx_lt
      cases c <;> cases c' <;> simp [Slot.code] at h <;>
        first | omega | (have := LK.idx_inj (k := k) (k' := k') (by omega); subst this; rfl)
    | len k' => have := k'.idx_lt; cases c <;> simp [Slot.code] at h <;> omega
    | path => cases c <;> simp [Slot.code] at h <;> omega
    | opt o => have := o.idx_lt; cases c <;> simp [Slot.code] at h <;> omega
  | len k =>
    have := k.idx_lt
    cases b with
    | f g => have := g.code_lt; simp [Slot.code] at h; omega
    | sz t' => have := t'.idx_lt; simp [Slot.code] at h; omega
    | prm => simp [Slot.code] at h; omega
    | lst k' c' => have := k'.idx_lt; cases c' <;> simp [Slot.code] at h <;> omega
    | len k' => simp [Slot.code] at h; rw [LK.idx_inj (k := k) (k' := k') (by omega)]
    | path => simp [Slot.code] at h; omega
    | opt o => have := o.idx_lt; simp [Slot.code] at h; omega
  | path =>
    cases b with
    | f g => have := g.code_lt; simp [Slot.code] at h; omega
    | sz t' => have := t'.idx_lt; simp [Slot.code] at h; omega
    | prm => simp [Slot.code] at h
    | lst k' c' => have := k'.idx_lt; cases c' <;> simp [Slot.code] at h <;> omega
    | len k' => have := k'.idx_lt; simp [Slot.code] at h; omega
    | path => rfl
    | opt o => have := o.idx_lt; simp [Slot.code] at h; omega
  | opt o =>
    have := o.idx_lt
    cases b with
    | f g => have := g.code_lt; simp [Slot.code] at h; omega
    | sz t' => have := t'.idx_lt; simp [Slot.code] at h; omega
    | prm => simp [Slot.code] at h; omega
    | lst k' c' => have := k'.idx_lt; cases c' <;> simp [Slot.code] at h <;> omega
    | len k' => have := k'.idx_lt; simp [Slot.code] at h; omega
    | path => simp [Slot.code] at h; omega
    | opt o' => simp [Slot.code] at h; rw [OF.idx_inj h]

/-- The machine array `sl` of the core in slot `p`. -/
def arr (p : Nat) (sl : Slot) : Arr := 1000 * p + sl.code

theorem arr_inj {p : Nat} {a b : Slot} (h : arr p a = arr p b) : a = b := by
  have h' : (1000 * p + a.code : Nat) = 1000 * p + b.code := h
  exact Slot.code_inj (by omega)

theorem arr_ne {p : Nat} {a b : Slot} (h : a ≠ b) : arr p a ≠ arr p b := fun e => h (arr_inj e)

@[simp] theorem arr_eq_iff {p : Nat} {a b : Slot} : arr p a = arr p b ↔ a = b :=
  ⟨arr_inj, fun h => h ▸ rfl⟩

/-- The machine array of field `f` in slot `p`. -/
abbrev arrF (p : Nat) (f : Fld) : Arr := arr p (.f f)
/-- The machine cell holding the size of table `t`. -/
abbrev arrS (p : Nat) (t : Tbl) : Arr := arr p (.sz t)
/-- The machine array of the parameters. -/
abbrev arrP (p : Nat) : Arr := arr p .prm

theorem arrF_inj {p : Nat} {f g : Fld} (h : arrF p f = arrF p g) : f = g := by
  have := arr_inj h; cases this; rfl
theorem arrF_ne_arrS (p : Nat) (f : Fld) (t : Tbl) : arrF p f ≠ arrS p t := arr_ne (by simp)
theorem arrF_ne_arrP (p : Nat) (f : Fld) : arrF p f ≠ arrP p := arr_ne (by simp)
theorem arrS_inj {p : Nat} {t t' : Tbl} (h : arrS p t = arrS p t') : t = t' := by
  have := arr_inj h; cases this; rfl
theorem arrS_ne_arrP (p : Nat) (t : Tbl) : arrS p t ≠ arrP p := arr_ne (by simp)

/-! ### Compilation -/

/-- Machine array storing one component of the encoded list rows for a core slot. -/
abbrev arrL (p : Nat) (k : LK) (b : Bool) : Arr := arr p (.lst k b)
/-- Machine array storing the lengths of encoded lists for a core slot. -/
abbrev arrLen (p : Nat) (k : LK) : Arr := arr p (.len k)
/-- Machine array storing flattened chunk ancestor paths for a core slot. -/
abbrev arrPath (p : Nat) : Arr := arr p .path
/-- Machine array storing an encoded optional preparation or job field. -/
abbrev arrO (p : Nat) (o : OF) : Arr := arr p (.opt o)

/-- The width of a path row, read from the parameters: `H + 1`. -/
def rowW (p : Nat) : OrderMaintenance.Machine.Expr := .bin .add (.load (arrP p) (.lit PF.H.idx)) (.lit 1)

/-- Translate a typed core expression to a RAM expression using the selected capacities. -/
def Exp.compile (p : Nat) (κ : Caps) : Exp → OrderMaintenance.Machine.Expr
  | .lit n => .lit n
  | .var x => .var x
  | .rd f i => .load (arrF p f) (i.compile p κ)
  | .size t => .load (arrS p t) (.lit 0)
  | .prm k => .load (arrP p) (.lit k.idx)
  | .bin op a b => .bin op (a.compile p κ) (b.compile p κ)
  | .un op a => .un op (a.compile p κ)
  | .lrd k b i j => .load (arrL p k b) (.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap))) (j.compile p κ))
  | .llen k i => .load (arrLen p k) (i.compile p κ)
  | .prd c j => .load (arrPath p) (.bin .add (.bin .mul (c.compile p κ) (rowW p)) (j.compile p κ))
  | .opt o => .load (arrO p o) (.lit 0)

/-- A store to a single-cell array. -/
def st1 (a : Arr) (e : OrderMaintenance.Machine.Expr) : OrderMaintenance.Machine.Stmt := .store a (.lit 0) e

/-- Translate a typed core statement to RAM instructions for one encoded core slot. -/
def Stm.compile (p : Nat) (κ : Caps) : Stm → OrderMaintenance.Machine.Stmt
  | .skip => .skip
  | .assign x e => .assign x (e.compile p κ)
  | .wr f i e => .store (arrF p f) (i.compile p κ) (e.compile p κ)
  | .push t x =>
    .seq (.assign x (.load (arrS p t) (.lit 0)))
      (.store (arrS p t) (.lit 0) (.bin .add (.var x) (.lit 1)))
  | .seq c d => .seq (c.compile p κ) (d.compile p κ)
  | .ite c t f => .ite (c.compile p κ) (t.compile p κ) (f.compile p κ)
  | .loop x n b => .loop x (n.compile p κ) (b.compile p κ)
  | .call nm ps b rs args ds => .call nm ps (b.compile p κ) rs (args.map (Exp.compile p κ)) ds
  | .fail => .fail
  | .bug => .assign "bug" (.bin .sub (.lit 0) (.lit 1))
  | .catch c h => .catch (c.compile p κ) (h.compile p κ)
  | .lwr k b i j e =>
    .store (arrL p k b) (.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap))) (j.compile p κ)) (e.compile p κ)
  | .lgrow k i a b =>
    let li := OrderMaintenance.Machine.Expr.load (arrLen p k) (i.compile p κ)
    let ix := OrderMaintenance.Machine.Expr.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap))) li
    .seq (.store (arrL p k false) ix (a.compile p κ))
      (.seq (.store (arrL p k true) ix (b.compile p κ))
        (.store (arrLen p k) (i.compile p κ) (.bin .add li (.lit 1))))
  | .lshrink k i =>
    .store (arrLen p k) (i.compile p κ) (.bin .sub (.load (arrLen p k) (i.compile p κ)) (.lit 1))
  | .lclear k i => .store (arrLen p k) (i.compile p κ) (.lit 0)
  | .pwr c j e =>
    .store (arrPath p) (.bin .add (.bin .mul (c.compile p κ) (rowW p)) (j.compile p κ)) (e.compile p κ)
  | .rowReset _ => .skip
  | .prepInit c b =>
    .call "prepInit" ["c", "b"]
      (.seq (st1 (arrO p .prepOn) (.lit 1)) (.seq (st1 (arrO p .prepChunk) (.var "c"))
        (.seq (st1 (arrO p .prepH) (.lit 1)) (.seq (st1 (arrO p .prepBelow) (.var "b"))
          (st1 (arrO p .prepTag) (.lit 0))))))
      [] [c.compile p κ, b.compile p κ] []
  | .prepSet h b t =>
    .call "prepSet" ["h", "b", "t"]
      (.seq (st1 (arrO p .prepH) (.var "h")) (.seq (st1 (arrO p .prepBelow) (.var "b"))
        (st1 (arrO p .prepTag) (.var "t"))))
      [] [h.compile p κ, b.compile p κ, t.compile p κ] []
  | .prepPath j e =>
    .store (arrPath p) (.bin .add (.bin .mul (.load (arrO p .prepChunk) (.lit 0)) (rowW p)) (j.compile p κ))
      (e.compile p κ)
  | .prepCommit =>
    .seq (st1 (arrO p .prepOn) (.lit 0)) (.seq (st1 (arrO p .prepChunk) (.lit 0))
      (.seq (st1 (arrO p .prepH) (.lit 0)) (.seq (st1 (arrO p .prepBelow) (.lit 0))
        (st1 (arrO p .prepTag) (.lit 0)))))
  | .jobSet x y z t a b c d =>
    .call "jobSet" ["x", "y", "z", "t", "a", "b", "c", "d"]
      (.seq (st1 (arrO p .jobOn) (.lit 1)) (.seq (st1 (arrO p .jobX) (.var "x"))
        (.seq (st1 (arrO p .jobY) (.var "y")) (.seq (st1 (arrO p .jobZ) (.var "z"))
          (.seq (st1 (arrO p .jobT) (.var "t")) (.seq (st1 (arrO p .jobA) (.var "a"))
            (.seq (st1 (arrO p .jobB) (.var "b")) (.seq (st1 (arrO p .jobC) (.var "c"))
              (st1 (arrO p .jobD) (.var "d"))))))))))
      [] ([x, y, z, t, a, b, c, d].map (Exp.compile p κ)) []
  | .jobClear =>
    .seq (st1 (arrO p .jobOn) (.lit 0)) (.seq (st1 (arrO p .jobX) (.lit 0))
      (.seq (st1 (arrO p .jobY) (.lit 0)) (.seq (st1 (arrO p .jobZ) (.lit 0))
        (.seq (st1 (arrO p .jobT) (.lit 0)) (.seq (st1 (arrO p .jobA) (.lit 0))
          (.seq (st1 (arrO p .jobB) (.lit 0)) (.seq (st1 (arrO p .jobC) (.lit 0))
            (st1 (arrO p .jobD) (.lit 0)))))))))
  | .pcSet t a b c d =>
    .call "pcSet" ["t", "a", "b", "c", "d"]
      (.seq (st1 (arrO p .jobT) (.var "t")) (.seq (st1 (arrO p .jobA) (.var "a"))
        (.seq (st1 (arrO p .jobB) (.var "b")) (.seq (st1 (arrO p .jobC) (.var "c"))
          (st1 (arrO p .jobD) (.var "d"))))))
      [] ([t, a, b, c, d].map (Exp.compile p κ)) []

theorem Exp.cost_compile (p : Nat) (κ : Caps) (e : Exp) : (e.compile p κ).cost = e.cost := by
  induction e with
  | lit | var | size | prm | opt => rfl
  | rd f i ih => simp [Exp.compile, OrderMaintenance.Machine.Expr.cost, Exp.cost, ih]
  | bin op a b iha ihb => simp [Exp.compile, OrderMaintenance.Machine.Expr.cost, Exp.cost, iha, ihb]
  | un op a ih => simp [Exp.compile, OrderMaintenance.Machine.Expr.cost, Exp.cost, ih]
  | lrd k b i j ihi ihj => simp [Exp.compile, OrderMaintenance.Machine.Expr.cost, Exp.cost, ihi, ihj]
  | llen k i ih => simp [Exp.compile, OrderMaintenance.Machine.Expr.cost, Exp.cost, ih]
  | prd c j ihc ihj => simp [Exp.compile, OrderMaintenance.Machine.Expr.cost, Exp.cost, ihc, ihj, rowW]

/-! ### The encoding -/

/-- Machine state `m` holds core `s` in slot `p`, with capacities `κ`. -/
structure Enc (p : Nat) (κ : Caps) (s : Core) (m : OrderMaintenance.Machine.State) : Prop where
  cap : ∀ f : Fld, m.cap (arrF p f) = f.cap κ
  mem : ∀ f : Fld, ∀ i < f.cap κ, m.mem (arrF p f) i = f.get s i
  scap : ∀ t, m.cap (arrS p t) = 1
  smem : ∀ t, m.mem (arrS p t) 0 = t.size s
  sle : ∀ t, t.size s ≤ κ.tbl t
  pcap : m.cap (arrP p) = 16
  pmem : ∀ k : PF, m.mem (arrP p) k.idx = k.get s.P
  /-- Lists: record `i`'s list is stored from `i · lcap`, with its length apart. -/
  lcapA : ∀ k b, m.cap (arrL p k b) = κ.lrec k * κ.lcap k
  lcapN : ∀ k, m.cap (arrLen p k) = κ.lrec k
  llen : ∀ k, ∀ i < κ.lrec k, m.mem (arrLen p k) i = (k.view s i).length ∧ (k.view s i).length ≤ κ.lcap k
  lmem : ∀ k, ∀ i < κ.lrec k, ∀ j < (k.view s i).length,
    m.mem (arrL p k false) (i * k.stride κ.lcap + j) = ((k.view s i).getD j (0, 0)).1 ∧
      m.mem (arrL p k true) (i * k.stride κ.lcap + j) = ((k.view s i).getD j (0, 0)).2
  /-- Paths: chunk `c`'s row is stored from `c · pw`. -/
  wcap : m.cap (arrPath p) = κ.tbl .C * κ.pw
  wmem : ∀ c < κ.tbl .C, ∀ j < κ.pw, m.mem (arrPath p) (c * κ.pw + j) = (rowOf s c).getX j
  ocap : ∀ o, m.cap (arrO p o) = 1
  omem : ∀ o, m.mem (arrO p o) 0 = o.get s
  prepC : ∀ pr, s.prep = some pr → pr.chunk < κ.tbl .C
  /-- The path rows are `H + 1` wide; the free-group stack is one record. -/
  pwH : κ.pw = s.P.H + 1
  frec : κ.lrec .freeG = 1

end OrderMaintenance.Impl
