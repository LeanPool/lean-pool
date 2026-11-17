/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Data.List.GetD

public import LeanPool.OrderMaintenance.Impl.PeakBound
public import LeanPool.OrderMaintenance.Impl.Notation
public import LeanPool.OrderMaintenance.Impl.Fields


/-!
# Theorem W, option (A), stage A2: small values along a run of the core language

The invariant that stage A2 carries through the core procedures.

* `VB K KH κ s`: the **values** stored in core `s` are small: every field below `2^K` (the handle
  below `2^KH`), the parameters, the list entries, the path entries and the optional records below
  `2^K`. It is the value part of `MemW`; the capacity part (sizes, list lengths, `pw = H + 1`)
  comes from an encoding (`EncOK`), which every run of `evalF` keeps (`EncOK.of_ok`, from `sim`).
  `VB.memW` puts them together.
* **The write primitives keep `VB`** when the value written is small: `VB.set` (a field),
  `VB.push`, `VB.lset` (a list), and the path, preparation and job records (`VB.pwr`, …).
* `Exp.vw`: the width of an expression's value, as `Exp.wv` of `PeakBound.lean` but sharper on
  the patterns the core code uses for `max`, truncated subtraction, a 0/1 factor and halving, so
  that `monus p 1`, `max c 1`, `ifz (θ < p) p` and `(a + b) / 2` keep the width of their
  operands. `Exp.vw_sound`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)
open OrderMaintenance.Proof.Top (getX_modify' getX_setX' getX_push')

deriving instance DecidableEq for Exp

variable {K KH : Nat} {κ : Caps}

/-! ### The invariant -/

/-- Room in `K` for the parameters used as shift amounts and label widths. -/
structure PRoom (K : Nat) (P : Params) : Prop where
  Be : P.elementBits ≤ K
  Bg : P.groupBits ≤ K
  beta : P.beta ≤ K
  /-- A label of an even table is below `2^(β + 9)` (at most 162 entries). -/
  beta9 : P.beta + 9 ≤ K
  /-- A digit shifted to the top level, `2^(H·β)`. -/
  Hb : (P.H + 1) * P.beta ≤ K
  Be1 : 1 ≤ P.elementBits
  Bg1 : 1 ≤ P.groupBits
  beta1 : 1 ≤ P.beta
  /-- The walk's threshold `a ^ ht = 1 <<< (log₂ a · ht)` (`powS`), for heights `ht ≤ H`. -/
  aH : Nat.log2 P.a * P.H ≤ K

/-- **The values stored in a core are small** (the value part of `MemW`), and the parameters
leave room in `K`. -/
structure VB (K KH : Nat) (κ : Caps) (s : Core) : Prop where
  fld : ∀ (f : Fld) j, j < f.cap κ → f.get s j < 2 ^ f.wd K KH
  prm : ∀ k : PF, k.get s.P < 2 ^ K
  lst : ∀ (k : LK) i j, i < κ.lrec k → j < (k.view s i).length →
    ((k.view s i).getD j (0, 0)).1 < 2 ^ K ∧ ((k.view s i).getD j (0, 0)).2 < 2 ^ K
  row : ∀ c j, c < κ.tbl .C → j < κ.pw → (rowOf s c).getX j < 2 ^ K
  opt : ∀ o : OF, o.get s < 2 ^ K
  room : PRoom K s.P

/-- Core `s` has an encoding with capacities `κ` (in some slot of some machine state). -/
def EncOK (κ : Caps) (s : Core) : Prop := ∃ p m, Enc p κ s m

theorem VB.memW {s : Core} (hV : VB K KH κ s) (hE : EncOK κ s) (hC : CapsW K κ) : MemW K KH κ s
  := by
  obtain ⟨p, m, h⟩ := hE
  exact { fld := hV.fld, size := fun t => lt_of_le_of_lt (h.sle t) (hC.tbl t), prm := hV.prm,
          H1 := by rw [← h.pwH]; exact hC.pw, len := fun k i hi => (h.llen k i hi).2, lst := hV.lst,
          row := hV.row, opt := hV.opt }

theorem EncOK.of_ok {s s' : Core} {L L' : Loc} {n : Nat} (hE : EncOK κ s) {c : Stm}
    (h : evalF κ c s L = .ok s' L' n) : EncOK κ s' := by
  obtain ⟨p, m, hm⟩ := hE
  have := sim (p := p) c (hm.withLoc L) rfl
  rw [h] at this
  exact ⟨p, _, this.2.1⟩

theorem EncOK.of_fail {s s' : Core} {L L' : Loc} {n : Nat} (hE : EncOK κ s) {c : Stm}
    (h : evalF κ c s L = .fail s' L' n) : EncOK κ s' := by
  obtain ⟨p, m, hm⟩ := hE
  have := sim (p := p) c (hm.withLoc L) rfl
  rw [h] at this
  exact ⟨p, _, this.2.1⟩

theorem EncOK.llen {s : Core} (hE : EncOK κ s) (k : LK) {i : Nat} (hi : i < κ.lrec k) :
    (k.view s i).length ≤ κ.lcap k := by
  obtain ⟨p, m, h⟩ := hE; exact (h.llen k i hi).2

theorem EncOK.sle {s : Core} (hE : EncOK κ s) (t : Tbl) : t.size s ≤ κ.tbl t := by
  obtain ⟨p, m, h⟩ := hE; exact h.sle t

theorem EncOK.pwH {s : Core} (hE : EncOK κ s) : κ.pw = s.P.H + 1 := by
  obtain ⟨p, m, h⟩ := hE; exact h.pwH

theorem EncOK.prepC {s : Core} (hE : EncOK κ s) {pr : Prep} (hp : s.prep = some pr) : pr.chunk <
  κ.tbl .C := by
  obtain ⟨p, m, h⟩ := hE; exact h.prepC pr hp

/-! ### Lists of small pairs -/

/-- Every entry of `l` is a pair of values below `2^K`. -/
def LB (K : Nat) (l : List (Nat × Nat)) : Prop := ∀ q ∈ l, q.1 < 2 ^ K ∧ q.2 < 2 ^ K

theorem getD_mem' {α : Type} {l : List α} {j : Nat} {d : α} (hj : j < l.length) : l.getD j d ∈ l
  := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

theorem VB.lb {s : Core} (hV : VB K KH κ s) (k : LK) {i : Nat} (hi : i < κ.lrec k) : LB K
  (k.view s i) := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
  have := hV.lst k i j hi hj
  rwa [List.getD_eq_getElem _ _ hj] at this

theorem LB.getD {l : List (Nat × Nat)} (h : LB K l) {j : Nat} (hj : j < l.length) :
    (l.getD j (0, 0)).1 < 2 ^ K ∧ (l.getD j (0, 0)).2 < 2 ^ K := h _ (getD_mem' hj)

theorem LB.set {l : List (Nat × Nat)} (h : LB K l) {j : Nat} {q : Nat × Nat} (hq : q.1 < 2 ^ K ∧
  q.2 < 2 ^ K) :
    LB K (l.set j q) := by
  intro r hr
  rcases List.mem_or_eq_of_mem_set hr with h1 | rfl
  · exact h r h1
  · exact hq

theorem LB.append {l : List (Nat × Nat)} (h : LB K l) {q : Nat × Nat} (hq : q.1 < 2 ^ K ∧ q.2 <
  2 ^ K) :
    LB K (l ++ [q]) := by
  intro r hr
  rcases List.mem_append.mp hr with h1 | h1
  · exact h r h1
  · simp only [List.mem_singleton] at h1; subst h1; exact hq

theorem LB.dropLast {l : List (Nat × Nat)} (h : LB K l) : LB K l.dropLast :=
  fun r hr => h r (List.mem_of_mem_dropLast hr)

theorem LB.nil : LB K [] := fun _ h => by cases h

/-! ### Writes keep `VB` -/

section writes
variable {s s' : Core}

theorem VB.set (hV : VB K KH κ s) {f : Fld} {i v : Nat} (h : f.set κ s i v = some s')
    (hv : v < 2 ^ f.wd K KH) : VB K KH κ s' := by
  obtain ⟨hl, hr, ho⟩ := Fld.set_rest h
  have hP := (Fld.set_keep h).2
  refine ⟨fun g j hj => ?_, fun k => by rw [hP]; exact hV.prm k, fun k i' j hi hj => ?_,
    fun c j hc hj => by rw [hr]; exact hV.row c j hc hj, fun o => by rw [ho]; exact hV.opt o, by
      rw [hP]; exact hV.room⟩
  · rw [Fld.get_set h g hj]
    split
    · next e => obtain ⟨rfl, -⟩ := e; exact hv
    · exact hV.fld g j hj
  · rw [hl] at hj ⊢; exact hV.lst k i' j hi hj

theorem VB.push (hV : VB K KH κ s) (t : Tbl) : VB K KH κ (t.push s) := by
  obtain ⟨hl, hr, ho⟩ := Tbl.push_rest s t
  refine ⟨fun g j hj => ?_, fun k => by rw [Tbl.push_P]; exact hV.prm k, fun k i' j hi hj => ?_,
    fun c j hc hj => by rw [hr]; exact hV.row c j hc hj, fun o => by rw [ho]; exact hV.opt o, by
      rw [Tbl.push_P]; exact hV.room⟩
  · rw [Tbl.push_get]; exact hV.fld g j hj
  · rw [hl] at hj ⊢; exact hV.lst k i' j hi hj

theorem VB.lset (hV : VB K KH κ s) {k : LK} {x : Nat} {l : List (Nat × Nat)} (h : k.set κ s x l
  = some s')
    (hl : LB K l) : VB K KH κ s' := by
  unfold LK.set at h
  split at h
  · next hc =>
    cases h
    obtain ⟨hf, -, hP, hr, ho⟩ := LK.put_keep s x l k
    refine ⟨fun g j hj => by rw [hf]; exact hV.fld g j hj, fun k' => by rw [hP]; exact hV.prm k',
      fun k' i' j hi hj => ?_, fun c j hc hj => by rw [hr]; exact hV.row c j hc hj,
      fun o => by rw [ho]; exact hV.opt o, by rw [hP]; exact hV.room⟩
    rw [LK.view_put hc.1 hc.2.1] at hj ⊢
    split
    · exact hl.getD (by rwa [ite_eq_left ‹_›] at hj)
    · next hne => rw [ite_eq_right hne] at hj; exact hV.lst k' i' j hi hj
  · simp only [reduceCtorEq] at h

/-- The fields, lists, sizes and parameters do not see the path rows and the optional records. -/
theorem fld_path (f : Fld) (j : Nat) (p : Array (Array Nat)) : f.get { s with path := p } j =
  f.get s j := by
  cases f <;> rename_i k <;> cases k <;> rfl
theorem fld_prep (f : Fld) (j : Nat) (p : Option Prep) : f.get { s with prep := p } j = f.get s
  j := by
  cases f <;> rename_i k <;> cases k <;> rfl
theorem fld_job (f : Fld) (j : Nat) (p : Option Job) : f.get { s with resJob := p } j = f.get s
  j := by
  cases f <;> rename_i k <;> cases k <;> rfl
theorem fld_pp (f : Fld) (j : Nat) (a : Array (Array Nat)) (p : Option Prep) :
    f.get { s with path := a, prep := p } j = f.get s j := by
  cases f <;> rename_i k <;> cases k <;> rfl
theorem view_path (k : LK) (i : Nat) (p : Array (Array Nat)) : k.view { s with path := p } i =
  k.view s i := by
  cases k <;> rfl
theorem view_prep (k : LK) (i : Nat) (p : Option Prep) : k.view { s with prep := p } i = k.view
  s i := by
  cases k <;> rfl
theorem view_job (k : LK) (i : Nat) (p : Option Job) : k.view { s with resJob := p } i = k.view
  s i := by
  cases k <;> rfl
theorem view_pp (k : LK) (i : Nat) (a : Array (Array Nat)) (p : Option Prep) :
    k.view { s with path := a, prep := p } i = k.view s i := by
  cases k <;> rfl
theorem opt_path (o : OF) (p : Array (Array Nat)) : o.get { s with path := p } = o.get s := by
  cases o <;> rfl
theorem opt_job_prep (o : OF) (p : Option Job) (h : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨
  o = .prepBelow ∨
    o = .prepTag) : o.get { s with resJob := p } = o.get s := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl
theorem opt_prep_job (o : OF) (p : Option Prep) (h : ¬ (o = .prepOn ∨ o = .prepChunk ∨ o =
  .prepH ∨ o = .prepBelow ∨
    o = .prepTag)) : o.get { s with prep := p } = o.get s := by
  cases o <;> simp only [reduceCtorEq, or_self, or_false, not_true_eq_false, or_true,
      not_false_eq_true] at h ⊢ <;> rfl

theorem rowOf_job (p : Option Job) (c : Nat) : rowOf { s with resJob := p } c = rowOf s c := by
  unfold rowOf; rfl

theorem b2n_lt' (hK : 1 ≤ K) (b : Bool) : b2n b < 2 ^ K := by
  have : 2 ≤ 2 ^ K := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  unfold b2n; split <;> omega

theorem lt_pow_of_le {n K : Nat} (h : n ≤ 4) (hK : 3 ≤ K) : n < 2 ^ K := by
  have : 8 ≤ 2 ^ K := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hK
  omega

/-- A path write to a chunk that is not being prepared. -/
theorem VB.pwr (hV : VB K KH κ s) {x y v : Nat} (hx : notPrep s x) (hv : v < 2 ^ K) :
    VB K KH κ { s with path := s.path.setX x ((s.path.getX x).setX y v) } := by
  refine ⟨fun g j hj => by rw [fld_path]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c j hc hj => ?_, fun o => by rw [opt_path]; exact hV.opt o, hV.room⟩
  · rw [view_path] at hj ⊢; exact hV.lst k i j hi hj
  · have hr := hV.row c j hc hj
    unfold rowOf at hr ⊢
    unfold notPrep at hx
    simp only
    split
    · next pr hpr =>
      rw [hpr] at hx hr
      simp only at hr ⊢
      split
      · next e => rw [ite_eq_left e] at hr; exact hr
      · next e =>
        rw [ite_eq_right e] at hr
        rw [getX_setX']
        split
        · next e2 => subst e2; rw [getX_setX']; split
                     · exact hv
                     · exact hr
        · exact hr
    · next hpr =>
      rw [hpr] at hr
      simp only at hr ⊢
      rw [getX_setX']
      split
      · next e2 => subst e2; rw [getX_setX']; split
                   · exact hv
                   · exact hr
      · exact hr

theorem getX_replicate_nil (n j : Nat) : (Array.replicate n NIL).getX j = 0 := getX_replicate0 n j

/-- A fresh row of `NIL`s for a chunk that is not being prepared. -/
theorem VB.rowReset (hV : VB K KH κ s) {x n : Nat} (_hx : notPrep s x) :
    VB K KH κ { s with path := s.path.setX x (Array.replicate n NIL) } := by
  refine ⟨fun g j hj => by rw [fld_path]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c j hc hj => ?_, fun o => by rw [opt_path]; exact hV.opt o, hV.room⟩
  · rw [view_path] at hj ⊢; exact hV.lst k i j hi hj
  · have hr := hV.row c j hc hj
    have h0 : (0 : Nat) < 2 ^ K := Nat.two_pow_pos K
    unfold rowOf at hr ⊢
    unfold notPrep at _hx
    simp only
    split
    · next pr hpr =>
      rw [hpr] at _hx hr
      simp only at hr ⊢
      split
      · next e => rw [ite_eq_left e] at hr; exact hr
      · next e =>
        rw [ite_eq_right e] at hr
        rw [getX_setX']
        split
        · rw [getX_replicate_nil]; exact h0
        · exact hr
    · next hpr =>
      rw [hpr] at hr
      simp only at hr ⊢
      rw [getX_setX']
      split
      · rw [getX_replicate_nil]; exact h0
      · exact hr

/-- A new preparation record. -/
theorem VB.prepInit (hV : VB K KH κ s) (hK : 3 ≤ K) {x y n : Nat} (hp : s.prep = none) (hx : x <
  2 ^ K)
    (hy : y < 2 ^ K) :
    VB K KH κ { s with prep := some { chunk := x, below := y, path := Array.replicate n NIL } }
      := by
  have h0 : (0 : Nat) < 2 ^ K := Nat.two_pow_pos K
  refine ⟨fun g j hj => by rw [fld_prep]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c j hc hj => ?_, fun o => ?_, hV.room⟩
  · rw [view_prep] at hj ⊢; exact hV.lst k i j hi hj
  · have hr := hV.row c j hc hj
    unfold rowOf at hr ⊢
    rw [hp] at hr
    simp only
    split
    · rw [getX_replicate_nil]; exact h0
    · exact hr
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · rcases ho with rfl | rfl | rfl | rfl | rfl
      · exact b2n_lt' (by omega) _
      · exact hx
      · simp only [OF.get]; exact lt_pow_of_le (by norm_num) hK
      · exact hy
      · exact h0
    · rw [opt_prep_job _ _ ho]; exact hV.opt o

/-- New height, below and tag of the preparation record. -/
theorem VB.prepSet (hV : VB K KH κ s) {pr : Prep} (hp : s.prep = some pr) {a b c : Nat} (ha : a
  < 2 ^ K)
    (hb : b < 2 ^ K) (hc : c < 2 ^ K) :
    VB K KH κ { s with prep := some { pr with h := a, below := b, tag := c } } := by
  refine ⟨fun g j hj => by rw [fld_prep]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c' j hc' hj => ?_, fun o => ?_, hV.room⟩
  · rw [view_prep] at hj ⊢; exact hV.lst k i j hi hj
  · have hr := hV.row c' j hc' hj
    unfold rowOf at hr ⊢; rw [hp] at hr; exact hr
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · have := hV.opt .prepChunk
      have h1 := hV.opt .prepOn
      simp only [OF.get, hp] at this h1
      rcases ho with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact this
      · exact ha
      · exact hb
      · exact hc
    · rw [opt_prep_job _ _ ho]; exact hV.opt o

/-- A level of the path being built. -/
theorem VB.prepPath (hV : VB K KH κ s) {pr : Prep} (hp : s.prep = some pr) {y v : Nat} (hv : v <
  2 ^ K) :
    VB K KH κ { s with prep := some { pr with path := pr.path.setX y v } } := by
  refine ⟨fun g j hj => by rw [fld_prep]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c' j hc' hj => ?_, fun o => ?_, hV.room⟩
  · rw [view_prep] at hj ⊢; exact hV.lst k i j hi hj
  · have hr := hV.row c' j hc' hj
    unfold rowOf at hr ⊢; rw [hp] at hr
    simp only at hr ⊢
    split
    · next e =>
      rw [ite_eq_left e] at hr
      rw [getX_setX']
      split
      · exact hv
      · exact hr
    · next e => rw [ite_eq_right e] at hr; exact hr
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · have h2 := hV.opt o
      rcases ho with rfl | rfl | rfl | rfl | rfl <;> simpa [OF.get, hp] using h2
    · rw [opt_prep_job _ _ ho]; exact hV.opt o

/-- The built path becomes the chunk's. -/
theorem VB.prepCommit (hV : VB K KH κ s) {pr : Prep} (hp : s.prep = some pr) :
    VB K KH κ { s with path := s.path.setX pr.chunk pr.path, prep := none } := by
  have h0 : (0 : Nat) < 2 ^ K := Nat.two_pow_pos K
  refine ⟨fun g j hj => by rw [fld_pp]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c' j hc' hj => ?_, fun o => ?_, hV.room⟩
  · rw [view_pp] at hj ⊢; exact hV.lst k i j hi hj
  · have hr := hV.row c' j hc' hj
    unfold rowOf at hr ⊢; rw [hp] at hr
    simp only at hr ⊢
    rw [getX_setX']
    split
    · next e => rw [ite_eq_left e] at hr; exact hr
    · next e => rw [ite_eq_right e] at hr; exact hr
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp only [OF.get, b2n, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, h0]
    · have : o.get { s with path := s.path.setX pr.chunk pr.path, prep := none } = o.get s := by
        cases o <;> simp only [reduceCtorEq, or_self, or_false, not_true_eq_false, or_true,
            not_false_eq_true] at ho ⊢ <;> rfl
      rw [this]; exact hV.opt o

theorem opt_job_eq {o : OF} (h : ¬ (o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨
  o = .prepTag)) :
    o = .jobOn ∨ o = .jobX ∨ o = .jobY ∨ o = .jobZ ∨ o = .jobT ∨ o = .jobA ∨ o = .jobB ∨ o =
      .jobC ∨ o = .jobD := by
  cases o <;> simp only [reduceCtorEq, or_self, or_false, not_true_eq_false, or_true,
      not_false_eq_true] at h ⊢

/-- A new job. -/
theorem VB.jobSet (hV : VB K KH κ s) (hK : 1 ≤ K) {x y z t a b c d : Nat} {pc : JobPc}
    (hpc : pcDec t a b c d = some pc) (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hz : z < 2 ^ K) (ht : t
      < 2 ^ K)
    (ha : a < 2 ^ K) (hb : b < 2 ^ K) (hc : c < 2 ^ K) (hd : d < 2 ^ K) :
    VB K KH κ { s with resJob := some { x := x, y := y, z := z, pc := pc } } := by
  have he := pcEnc_dec hpc
  refine ⟨fun g j hj => by rw [fld_job]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c' j hc' hj => by rw [rowOf_job]; exact hV.row c' j hc' hj, fun o => ?_, hV.room⟩
  · rw [view_job] at hj ⊢; exact hV.lst k i j hi hj
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · rw [opt_job_prep _ _ ho]; exact hV.opt o
    · rcases opt_job_eq ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [OF.get, he] <;> first | exact b2n_lt' hK _ | assumption

theorem VB.jobClear (hV : VB K KH κ s) : VB K KH κ { s with resJob := none } := by
  have h0 : (0 : Nat) < 2 ^ K := Nat.two_pow_pos K
  refine ⟨fun g j hj => by rw [fld_job]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c' j hc' hj => by rw [rowOf_job]; exact hV.row c' j hc' hj, fun o => ?_, hV.room⟩
  · rw [view_job] at hj ⊢; exact hV.lst k i j hi hj
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · rw [opt_job_prep _ _ ho]; exact hV.opt o
    · rcases opt_job_eq ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [
        OF.get,
        b2n,
        Option.isSome_none,
        Bool.false_eq_true,
        ↓reduceIte,
        h0]

/-- A new program counter of the running job. -/
theorem VB.pcSet (hV : VB K KH κ s) {jb : Job} (hj : s.resJob = some jb) {t a b c d : Nat} {pc :
  JobPc}
    (hpc : pcDec t a b c d = some pc) (ht : t < 2 ^ K) (ha : a < 2 ^ K) (hb : b < 2 ^ K) (hc : c
      < 2 ^ K)
    (hd : d < 2 ^ K) : VB K KH κ { s with resJob := some { jb with pc := pc } } := by
  have he := pcEnc_dec hpc
  refine ⟨fun g j hj => by rw [fld_job]; exact hV.fld g j hj, hV.prm, fun k i j hi hj => ?_,
    fun c' j hc' hj => by rw [rowOf_job]; exact hV.row c' j hc' hj, fun o => ?_, hV.room⟩
  · rw [view_job] at hj ⊢; exact hV.lst k i j hi hj
  · by_cases ho : o = .prepOn ∨ o = .prepChunk ∨ o = .prepH ∨ o = .prepBelow ∨ o = .prepTag
    · rw [opt_job_prep _ _ ho]; exact hV.opt o
    · have := hV.opt o
      rcases opt_job_eq ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [OF.get, he, hj] at this ⊢ <;> first | exact this | assumption

end writes

/-! ### A sharper width for the values of expressions -/

/-- A comparison or connective: its value is 0 or 1. -/
def Exp.isCmp : Exp → Bool
  | .bin .lt _ _ | .bin .le _ _ | .bin .eq _ _ | .bin .and _ _ | .bin .or _ _ | .un .not _ => true
  | _ => false

/-- An expression worth 0 or 1: a comparison, `1 − c` of a comparison, or the literal 0 or 1. -/
def Exp.isBool (e : Exp) : Bool :=
  e.isCmp || match e with
    | .bin .sub (.lit 1) c => c.isCmp
    | .lit 0 | .lit 1 => true
    | _ => false

/-- `a + b` is `c·X + (1 − c)·Y` for a comparison `c` (the shape of `Exp.max`): one summand is 0. -/
def Exp.maxShape : Exp → Exp → Bool
  | .bin .mul c _, .bin .mul (.bin .sub (.lit 1) c') _ => decide (c = c') && c.isCmp
  | _, _ => false

/-- The width of `op a b` from the widths of `a` and `b` (sharper than `BinOp.wd` on the shapes
above, on a 0/1 factor and on division by a literal `≥ 2`). -/
def _root_.OrderMaintenance.Machine.BinOp.vw (S : Nat) (op : BinOp) (a b : Exp) (wa wb : Nat) :
  Nat :=
  match op with
  | .add => if Exp.maxShape a b then Max.max wa wb else Max.max wa wb + 1
  | .mul => if a.isBool then wb else if b.isBool then wa else wa + wb
  | .div => match b with
    | .lit n => if 2 ≤ n then wa - 1 else wa
    | _ => wa
  | op => op.wd S wa wb

theorem _root_.OrderMaintenance.Machine.BinOp.vw_add (S : Nat) (a b : Exp) (wa wb : Nat) :
    BinOp.vw S .add a b wa wb = if Exp.maxShape a b then Max.max wa wb else Max.max wa wb + 1 := rfl
theorem _root_.OrderMaintenance.Machine.BinOp.vw_mul (S : Nat) (a b : Exp) (wa wb : Nat) :
    BinOp.vw S .mul a b wa wb = if a.isBool then wb else if b.isBool then wa else wa + wb := rfl
theorem _root_.OrderMaintenance.Machine.BinOp.vw_div_lit (S : Nat) (a : Exp) (n wa wb : Nat) :
    BinOp.vw S .div a (.lit n) wa wb = if 2 ≤ n then wa - 1 else wa := rfl

/-- **The width of an expression's value**, as `Exp.wv` with the sharper `BinOp.vw`. -/
def Exp.vw (Γ : Reg → Nat) (K KH S : Nat) : Exp → Nat
  | .lit n => n
  | .var x => Γ x
  | .rd f _ => f.wd K KH
  | .size _ => K
  | .prm _ => K
  | .bin op a b => op.vw S a b (a.vw Γ K KH S) (b.vw Γ K KH S)
  | .un op a => op.wd (a.vw Γ K KH S)
  | .lrd _ _ _ _ => K
  | .llen _ _ => K
  | .prd _ _ => K
  | .opt _ => K

theorem Exp.isCmp_le {κ : Caps} {s : Core} {L : Loc} {c : Exp} (h : c.isCmp = true) {v : Nat}
    (hv : c.ev κ s L = some v) : v ≤ 1 := by
  cases c with
  | bin op a b =>
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, -, y, -, hv⟩ := hv
    cases op <;> simp only [isCmp, Bool.false_eq_true] at h <;>
      simp only [Machine.BinOp.eval, Option.some.injEq] at hv <;>
      subst hv <;> split <;> omega
  | un op a =>
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, -, rfl⟩ := hv
    cases op <;> simp only [isCmp, Bool.false_eq_true] at h
    simp only [Machine.UnOp.eval]; split <;> omega
  | _ => simp only [isCmp, Bool.false_eq_true] at h

theorem Exp.isBool_le {κ : Caps} {s : Core} {L : Loc} {c : Exp} (h : c.isBool = true) {v : Nat}
    (hv : c.ev κ s L = some v) : v ≤ 1 := by
  unfold Exp.isBool at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Exp.isCmp_le h hv
  · split at h
    · next c' =>
      simp only [Exp.ev, Option.bind_eq_some_iff, Machine.BinOp.eval] at hv
      obtain ⟨one, hone, y, hy, hv⟩ := hv
      simp only [Option.some.injEq] at hone; subst hone
      split at hv
      · simp only [Option.some.injEq] at hv; omega
      · cases hv
    · simp only [ev, Option.some.injEq] at hv; omega
    · simp only [ev, Option.some.injEq] at hv; omega
    · cases h

theorem lt_two_of_lt_pow {x w : Nat} (hx : x < 2 ^ w) (hw : w ≤ 1) : x ≤ 1 := by
  have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hw
  omega

variable {s : Core} {L : Loc} {Γ : Reg → Nat}

/-- **The value of an expression is below `2^vw`.** -/
theorem Exp.vw_sound (hM : MemW K KH κ s) (hC : CapsW K κ) (hΓ : ∀ x, L x < 2 ^ Γ x) {S : Nat} :
    ∀ (e : Exp) {v : Nat}, e.ShOK κ s L S → e.ev κ s L = some v → v < 2 ^ e.vw Γ K KH S
  | .lit n, v, _, hv => by
    simp only [Exp.ev,
      Option.some.injEq] at hv; subst hv; simp only [Exp.vw]; exact Nat.lt_two_pow_self
  | .var x, v, _, hv => by
    simp only [Exp.ev, Option.some.injEq] at hv; subst hv; simp only [Exp.vw]; exact hΓ x
  | .rd f i, v, hs, hv => by
    rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.rd f i) hs hv).1
  | .size t, v, hs, hv => by rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.size t) hs hv).1
  | .prm k, v, hs, hv => by rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.prm k) hs hv).1
  | .lrd k b i j, v, hs, hv => by
    rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.lrd k b i j) hs hv).1
  | .llen k i, v, hs, hv => by
    rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.llen k i) hs hv).1
  | .prd c j, v, hs, hv => by rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.prd c j) hs hv).1
  | .opt o, v, hs, hv => by rw [Exp.vw]; exact (Exp.wd_sound (Γ := Γ) hM hC hΓ (.opt o) hs hv).1
  | .un op a, v, hs, hv => by
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    rw [Exp.vw]
    exact UnOp.wd_sound (Exp.vw_sound hM hC hΓ a hs hx)
  | .bin op a b, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    obtain ⟨hsa, hsb, hsh⟩ := hs
    have hxa := Exp.vw_sound hM hC hΓ a hsa hx
    have hyb := Exp.vw_sound hM hC hΓ b hsb hy
    cases op with
    | add =>
      simp only [Machine.BinOp.eval, Option.some.injEq] at hv; subst hv
      rw [Exp.vw, BinOp.vw_add]
      split
      · next hm =>
        -- `a = c·X`, `b = (1 − c)·Y` with `c` worth 0 or 1: one of `x`, `y` is 0
        have h0 : x = 0 ∨ y = 0 := by
          unfold Exp.maxShape at hm
          split at hm
          · next c X c' Y =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
            obtain ⟨rfl, hc⟩ := hm
            simp only [Exp.ev, Option.bind_eq_some_iff, Machine.BinOp.eval,
              Option.some.injEq] at hx hy
            obtain ⟨u, hu, xX, -, rfl⟩ := hx
            obtain ⟨w, ⟨one, hone, u', hu', hsub⟩, yY, -, rfl⟩ := hy
            subst hone
            rw [hu] at hu'; cases hu'
            have := Exp.isCmp_le hc hu
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with rfl | rfl
            · simp only [zero_mul, mul_eq_zero, true_or]
            · simp only [Std.le_refl, ↓reduceIte, tsub_self, Option.some.injEq] at hsub
              subst hsub
              simp only [one_mul, zero_mul, or_true]
          · cases hm
        rcases h0 with rfl | rfl
        · simpa using lt_pow_max_right (a := a.vw Γ K KH S) hyb
        · simpa using lt_pow_max_left (b := b.vw Γ K KH S) hxa
      · have h1 := lt_pow_max_left (b := b.vw Γ K KH S) hxa
        have h2 := lt_pow_max_right (a := a.vw Γ K KH S) hyb
        rw [pow_succ]; omega
    | mul =>
      simp only [Machine.BinOp.eval, Option.some.injEq] at hv; subst hv
      rw [Exp.vw, BinOp.vw_mul]
      split
      · next h1 =>
        have := Exp.isBool_le h1 hx
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with rfl | rfl
        · simp only [zero_mul, Nat.ofNat_pos, pow_pos]
        · simpa using hyb
      · split
        · next _ h2 =>
          have := Exp.isBool_le h2 hy
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with rfl | rfl
          · simp only [mul_zero, Nat.ofNat_pos, pow_pos]
          · simpa using hxa
        · rw [pow_add]; exact Nat.mul_lt_mul'' hxa hyb
    | div =>
      simp only [Machine.BinOp.eval, Option.some.injEq] at hv; subst hv
      rw [Exp.vw]
      cases b
      case lit n =>
        rw [BinOp.vw_div_lit]
        simp only [Exp.ev, Option.some.injEq] at hy; subst hy
        split
        · next h2 =>
          have hle : x / n ≤ x / 2 := Nat.div_le_div_left h2 (by norm_num)
          rcases Nat.eq_zero_or_pos (a.vw Γ K KH S) with h0 | h0
          · rw [h0] at hxa
            simp only [pow_zero, Nat.lt_one_iff] at hxa
            subst hxa
            simp only [Nat.zero_div, Nat.ofNat_pos, pow_pos]
          · have : 2 ^ a.vw Γ K KH S = 2 * 2 ^ (a.vw Γ K KH S - 1) := by
              rw [← pow_succ']; congr 1; omega
            rw [this] at hxa
            have : x / 2 < 2 ^ (a.vw Γ K KH S - 1) := by omega
            omega
        · exact lt_of_le_of_lt (Nat.div_le_self _ _) hxa
      all_goals exact lt_of_le_of_lt (Nat.div_le_self _ _) hxa
    | _ =>
      simp only [Exp.vw]
      exact BinOp.wd_sound hxa hyb (fun e => le_trans (le_of_eq (Exp.val_of hy).symm) (hsh e)) hv

/-- **The width of an expression's peak**, as `Exp.wp` with the value widths of `Exp.vw`. -/
def Exp.wq (Γ : Reg → Nat) (K KH S : Nat) : Exp → Nat
  | .lit n => n
  | .var x => Γ x
  | .rd f i => Max.max (i.wq Γ K KH S) (f.wd K KH)
  | .size _ => K
  | .prm _ => K
  | e@(.bin _ a b) => Max.max (Max.max (a.wq Γ K KH S) (b.wq Γ K KH S)) (e.vw Γ K KH S)
  | e@(.un _ a) => Max.max (a.wq Γ K KH S) (e.vw Γ K KH S)
  | .lrd _ _ i j => Max.max (Max.max (i.wq Γ K KH S) (j.wq Γ K KH S)) K
  | .llen _ i => Max.max (i.wq Γ K KH S) K
  | .prd c j => Max.max (Max.max (c.wq Γ K KH S) (j.wq Γ K KH S)) K
  | .opt _ => K

/-- **The peak of an expression is below `2^wq`.** -/
theorem Exp.wq_sound (hM : MemW K KH κ s) (hC : CapsW K κ) (hΓ : ∀ x, L x < 2 ^ Γ x) {S : Nat} :
    ∀ (e : Exp) {v : Nat}, e.ShOK κ s L S → e.ev κ s L = some v → e.pk κ s L < 2 ^ e.wq Γ K KH S
  | .lit n, v, _, hv => by simpa [Exp.pk, Exp.wq] using lit_lt_pow n
  | .var x, v, _, hv => by simpa [Exp.pk, Exp.wq] using hΓ x
  | .rd f i, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨j, hj, hv⟩ := hv
    split at hv
    · next hjc =>
      cases hv
      have hf := hM.fld f j hjc
      have hip := Exp.wq_sound hM hC hΓ i hs hj
      simp only [Exp.pk, Exp.wq, Exp.val_of hv']
      exact max_lt_pow hip hf
    · simp only [reduceCtorEq] at hv
  | .size t, v, hs, hv => by
    have := (Exp.wd_sound (Γ := Γ) hM hC hΓ (.size t) hs hv).2; simpa [Exp.wp, Exp.wq] using this
  | .prm k, v, hs, hv => by
    have := (Exp.wd_sound (Γ := Γ) hM hC hΓ (.prm k) hs hv).2; simpa [Exp.wp, Exp.wq] using this
  | .opt o, v, hs, hv => by
    have := (Exp.wd_sound (Γ := Γ) hM hC hΓ (.opt o) hs hv).2; simpa [Exp.wp, Exp.wq] using this
  | .bin op a b, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, -⟩ := hv
    have hs' := hs
    obtain ⟨hsa, hsb, -⟩ := hs
    have hpa := Exp.wq_sound hM hC hΓ a hsa hx
    have hpb := Exp.wq_sound hM hC hΓ b hsb hy
    have hw := Exp.vw_sound hM hC hΓ (.bin op a b) hs' hv'
    simp only [Exp.pk, Exp.wq, Exp.val_of hv']
    exact max_lt_pow (max_lt_pow hpa hpb) hw
  | .un op a, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, -⟩ := hv
    have hpa := Exp.wq_sound hM hC hΓ a hs hx
    have hw := Exp.vw_sound hM hC hΓ (.un op a) hs hv'
    simp only [Exp.pk, Exp.wq, Exp.val_of hv']
    exact max_lt_pow hpa hw
  | .lrd k b i j, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      have hip := Exp.wq_sound hM hC hΓ i hs.1 hx
      have hjp := Exp.wq_sound hM hC hΓ j hs.2 hy
      have hl := hM.len k x hc.1
      have he := hM.lst k x y hc.1 hc.2
      have hval : (if b then ((k.view s x).getD y (0, 0)).2 else ((k.view s x).getD y (0, 0)).1)
        < 2 ^ K := by
        cases b
        · simpa using he.1
        · simpa using he.2
      have hst : k.stride κ.lcap ≤ κ.lcap k := by cases k <;> simp only [LK.stride, Std.le_refl,
          zero_le]
      have hidx : x * k.stride κ.lcap + y < 2 ^ K := by
        have hy' : y < κ.lcap k := lt_of_lt_of_le hc.2 hl
        cases k with
        | freeG =>
          simp only [LK.stride, mul_zero, zero_add, gt_iff_lt]
          exact lt_of_lt_of_le hy' (le_of_lt (hC.lcap _))
        | _ => exact lt_trans (lt_mul_add hc.1 hy') (hC.lst _)
      have hK : ∀ z, z < 2 ^ K → z < 2 ^ Max.max (Max.max (i.wq Γ K KH S) (j.wq Γ K KH S)) K :=
        fun z hz => lt_pow_max_right hz
      have hK1 : ∀ z, z < 2 ^ i.wq Γ K KH S → z < 2 ^ Max.max (Max.max (i.wq Γ K KH S) (j.wq Γ K
        KH S)) K :=
        fun z hz => lt_pow_max_left (lt_pow_max_left hz)
      have hK2 : ∀ z, z < 2 ^ j.wq Γ K KH S → z < 2 ^ Max.max (Max.max (i.wq Γ K KH S) (j.wq Γ K
        KH S)) K :=
        fun z hz => lt_pow_max_left (lt_pow_max_right hz)
      simp only [Exp.pk, Exp.wq, Exp.val_of hv', Exp.val_of hx, Exp.val_of hy]
      refine max_lt (max_lt (max_lt (max_lt (max_lt (hK1 _ hip) (hK _ (lt_of_le_of_lt hst
        (hC.lcap k))))
        (hK _ (by omega))) (hK2 _ hjp)) (hK _ hidx)) (hK _ hval)
    · simp only [reduceCtorEq] at hv
  | .llen k i, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      have hip := Exp.wq_sound hM hC hΓ i hs hx
      have hl : (k.view s x).length < 2 ^ K := lt_of_le_of_lt (hM.len k x hc) (hC.lcap k)
      simp only [Exp.pk, Exp.wq, Exp.val_of hv']
      exact max_lt_pow hip hl
    · simp only [reduceCtorEq] at hv
  | .prd c j, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    split at hv
    · next hcj =>
      cases hv
      have hcp := Exp.wq_sound hM hC hΓ c hs.1 hx
      have hjp := Exp.wq_sound hM hC hΓ j hs.2 hy
      have hval := hM.row x y hcj.1 hcj.2
      have hidx : x * κ.pw + y < 2 ^ K := lt_trans (lt_mul_add hcj.1 hcj.2) hC.path
      have hrow : rowPk s < 2 ^ K := by
        have h1 := hM.H1; have h16 := hC.sixteen
        simp only [rowPk, PF.idx]
        exact max_lt (max_lt (max_lt (by omega) (by omega)) (by omega)) h1
      have hK : ∀ z, z < 2 ^ K → z < 2 ^ Max.max (Max.max (c.wq Γ K KH S) (j.wq Γ K KH S)) K :=
        fun z hz => lt_pow_max_right hz
      simp only [Exp.pk, Exp.wq, Exp.val_of hv', Exp.val_of hx, Exp.val_of hy]
      refine max_lt (max_lt (max_lt (max_lt (max_lt (lt_pow_max_left (lt_pow_max_left hcp)) (hK
        _ hrow))
        (hK _ (by omega))) (lt_pow_max_left (lt_pow_max_right hjp))) (hK _ hidx)) (hK _ hval)
    · simp only [reduceCtorEq] at hv

theorem pkList_lt' (hM : MemW K KH κ s) (hC : CapsW K κ) (hΓ : ∀ x, L x < 2 ^ Γ x) {S W : Nat} :
    ∀ {es : List Exp} {vs : List Nat}, (∀ e ∈ es, e.ShOK κ s L S ∧ e.wq Γ K KH S ≤ W) →
      evList κ s L es = some vs → pkList κ s L es < 2 ^ W
  | [], _, _, _ => by simp only [pkList, List.map_nil, List.foldr_nil, Nat.ofNat_pos, pow_pos]
  | e :: es, vs, h, hv => by
    simp only [evList, List.mapM_cons] at hv
    cases he : e.ev κ s L with
    | none => simp only [he, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at hv
    | some v =>
      cases hes : es.mapM (·.ev κ s L) with
      | none => simp only [he, hes, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at hv
      | some ws =>
        have h1 := Exp.wq_sound hM hC hΓ e (h e (by simp)).1 he
        have h2 := pkList_lt' hM hC hΓ (es := es) (fun e' he' => h e' (by simp only [
            List.mem_cons,
            he',
            or_true])) hes
        simp only [pkList, List.map_cons, List.foldr_cons] at h2 ⊢
        exact max_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (h e (by simp)).2)) h2

/-! ### Runs keep the parameters -/

/-- The outcome keeps the parameters of `s`. -/
def Res.keepsP (s : Core) : Res → Prop
  | .ok s' _ _ => s'.P = s.P
  | .fail s' _ _ => s'.P = s.P
  | .bug => True

theorem Res.keepsP_addCost {s : Core} {r : Res} (c : Nat) (h : r.keepsP s) : (r.addCost
  c).keepsP s := by
  cases r <;> exact h

theorem Res.keepsP_bind {s : Core} {r : Res} {g : Core → Loc → Res} (h : r.keepsP s)
    (hg : ∀ s1 L1, (g s1 L1).keepsP s1) : (r.bind g).keepsP s := by
  cases r with
  | ok s1 L1 c =>
    simp only [Res.bind]
    have := hg s1 L1
    cases hr : g s1 L1 <;> rw [hr] at this <;> simp only [Res.addCost, Res.keepsP] at this ⊢ <;>
      exact this.trans h
  | fail => exact h
  | bug => trivial

theorem LK.set_P {s s' : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (h : k.set κ s i l =
  some s') :
    s'.P = s.P := by
  simp only [LK.set] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  cases k <;> rfl

theorem runForF_keepsP (b : Stm) (x : Reg) (hb : ∀ s L, (evalF κ b s L).keepsP s) :
    ∀ n k s L, (runForF (evalF κ b) x k n s L).keepsP s
  | 0, _, _, _ => rfl
  | n + 1, k, s, L => by
    simp only [runForF]
    exact Res.keepsP_bind (Res.keepsP_addCost 1 (hb s _)) (fun s1 L1 => runForF_keepsP b x hb n
      (k + 1) s1 L1)

theorem evalF_keepsP : ∀ (c : Stm) (s : Core) (L : Loc), (evalF κ c s L).keepsP s
  | .skip, _, _ => rfl
  | .assign x e, s, L => by simp only [evalF]; split <;> trivial
  | .wr f i e, s, L => by
    simp only [evalF]; split
    · split
      · next s' h => exact (Fld.set_keep h).2
      · trivial
    · trivial
  | .push t x, s, L => by simp only [evalF]; split <;> (try trivial); exact Tbl.push_P s t
  | .seq a b, s, L => Res.keepsP_bind (evalF_keepsP a s L) (fun s1 L1 => evalF_keepsP b s1 L1)
  | .ite c a b, s, L => by
    simp only [evalF]; split
    · apply Res.keepsP_addCost; split
      · exact evalF_keepsP a s L
      · exact evalF_keepsP b s L
    · trivial
  | .loop x n b, s, L => by
    simp only [evalF]; split
    · exact Res.keepsP_addCost _ (runForF_keepsP b x (fun s L => evalF_keepsP b s L) _ _ s L)
    · trivial
  | .call _ ps b rs args ds, s, L => by
    simp only [evalF]; split
    · next vs _ =>
      have := evalF_keepsP b s (Machine.State.setLocs (fun _ => 0) ps vs)
      split <;> simp only [Res.keepsP] at this ⊢
      all_goals
        rename_i heq
        rw [heq] at this
        exact this
    · trivial
  | .fail, _, _ => rfl
  | .bug, _, _ => trivial
  | .catch a b, s, L => by
    simp only [evalF]
    have ha := evalF_keepsP a s L
    split
    · next s' L' n heq =>
      rw [heq] at ha
      have hb := Res.keepsP_addCost (1 + n) (evalF_keepsP b s' L')
      revert hb; cases evalF κ b s' L' <;> simp only [Res.addCost, Res.keepsP] <;> intro hb <;>
        first | trivial | exact hb.trans ha
    · next heq => rw [heq] at ha; exact ha
    · trivial
  | .lwr k snd i j e, s, L => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact LK.set_P h
        · trivial
      · trivial
    · trivial
  | .lgrow k i a b, s, L => by
    simp only [evalF]; split
    · split
      · next s' h => exact LK.set_P h
      · trivial
    · trivial
  | .lshrink k i, s, L => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact LK.set_P h
        · trivial
      · trivial
    · trivial
  | .lclear k i, s, L => by
    simp only [evalF]; split
    · split
      · next s' h => exact LK.set_P h
      · trivial
    · trivial
  | .pwr c j e, s, L => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .rowReset c, s, L => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepInit c b, s, L => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepSet h b t, s, L => by simp only [evalF]; split <;> first | rfl | trivial
  | .prepPath j e, s, L => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepCommit, s, L => by simp only [evalF]; split <;> first | rfl | trivial
  | .jobSet x y z t a b c d, s, L => by
    simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .jobClear, _, _ => rfl
  | .pcSet t a b c d, s, L => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial

/-- **A run keeps the parameters.** -/
theorem evalF_P {c : Stm} {s s' : Core} {L L' : Loc} {n : Nat} (h : evalF κ c s L = .ok s' L' n)
  : s'.P = s.P := by
  have := evalF_keepsP (κ := κ) c s L; rw [h] at this; exact this

end OrderMaintenance.Impl
