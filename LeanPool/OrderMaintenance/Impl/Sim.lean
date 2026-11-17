/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports and Lean 4.35 compatibility. -/

module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Order.Defs.PartialOrder
public import LeanPool.OrderMaintenance.Impl.Fields

/-!
# M6: the compiled code simulates the source

`sim`: if machine state `m` holds core `s` (`Enc`) with the same locals, then running the
compiled statement on `m` ends exactly as `evalF` says: the same outcome, a machine state that
holds the resulting core, the same locals, and **the same number of steps**. A `.bug` outcome
promises nothing (the agreement lemmas exclude it).
-/

@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr BinOp UnOp State Out exec Expr maxvList)

variable {p : Nat} {κ : Caps}

@[simp] theorem st_write_cap (m : State) (a : Arr) (j v : Nat) : (m.write a j v).cap = m.cap := rfl
@[simp] theorem st_write_loc (m : State) (a : Arr) (j v : Nat) : (m.write a j v).loc = m.loc := rfl
@[simp] theorem st_bump_cap (m : State) (v : Nat) : (m.bump v).cap = m.cap := rfl
@[simp] theorem st_bump_loc (m : State) (v : Nat) : (m.bump v).loc = m.loc := rfl
@[simp] theorem st_bump_mem (m : State) (v : Nat) : (m.bump v).mem = m.mem := rfl
@[simp] theorem st_leave_mem (m : State) (c : Reg → Nat) (r d : List Reg) :
    (m.leave c r d).mem = m.mem := rfl
@[simp] theorem st_leave_cap (m : State) (c : Reg → Nat) (r d : List Reg) :
    (m.leave c r d).cap = m.cap := rfl
@[simp] theorem st_write_mem (m : State) (a : Arr) (j v : Nat) (b : Arr) :
    (m.write a j v).mem b = if b = a then State.upd (m.mem a) j v else m.mem b := rfl

/-! ### The encoding under machine updates -/

theorem Enc.congr {s : Core} {m m' : State} (h : Enc p κ s m) (hm : m'.mem = m.mem)
    (hc : m'.cap = m.cap) : Enc p κ s m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨by rw [hc]; exact h1, by rw [hm]; exact h2, by rw [hc]; exact h3, by rw [hm]; exact h4, h5,
    by rw [hc]; exact h6, by rw [hm]; exact h7, by rw [hc]; exact h8, by rw [hc]; exact h9,
    by rw [hm]; exact h10, by rw [hm]; exact h11, by rw [hc]; exact h12, by rw [hm]; exact h13,
    by rw [hc]; exact h14, by rw [hm]; exact h15, h16, h17, h18⟩

theorem Enc.bump {s : Core} {m : State} (h : Enc p κ s m) (v : Nat) : Enc p κ s (m.bump v) :=
  h.congr rfl rfl
theorem Enc.setLoc {s : Core} {m : State} (h : Enc p κ s m) (x : Reg) (v : Nat) :
    Enc p κ s (m.setLoc x v) := h.congr rfl rfl
theorem Enc.withLoc {s : Core} {m : State} (h : Enc p κ s m) (l : Reg → Nat) :
    Enc p κ s { m with loc := l } := h.congr rfl rfl

/-- The encoding of `s'` holds when every array other than `a` is unchanged, the cores agree on
everything stored outside `a`, and `a` holds what `s'` needs. -/
theorem Fld.set_prep {s s' : Core} {f : Fld} {j v : Nat} (hs : f.set κ s j v = some s') :
    s'.prep = s.prep := by
  cases f with
  | e k | g k | c k | n k =>
    simp only [Fld.set] at hs; split at hs <;> [skip; simp only [reduceCtorEq] at hs]; cases hs; rfl
  | a k =>
    simp only [Fld.set] at hs
    split at hs <;> [skip; simp only [reduceCtorEq] at hs]
    cases hs
    cases k <;> rfl
  | s k =>
    simp only [Fld.set] at hs
    split at hs <;> [skip; simp only [reduceCtorEq] at hs]
    cases hs
    cases k <;> rfl

theorem lt_mul_add {x y a b : Nat} (hx : x < a) (hy : y < b) : x * b + y < a * b := by
  have : (x + 1) * b ≤ a * b := Nat.mul_le_mul_right b hx
  rw [Nat.add_mul, one_mul] at this; omega

theorem write_other {m : State} {a b : Arr} {j v i : Nat} (h : b ≠ a) :
    (m.write a j v).mem b i = m.mem b i := by
  simp [State.write, h]

theorem write_same {m : State} {a : Arr} {j v i : Nat} :
    (m.write a j v).mem a i = if i = j then v else m.mem a i := by
  simp [State.write, State.upd]

theorem Enc.write {s s' : Core} {m : State} (h : Enc p κ s m) {f : Fld} {j v : Nat}
    (hs : f.set κ s j v = some s') :
    Enc p κ s' (m.write (arrF p f) j v) := by
  obtain ⟨hT, hP⟩ := Fld.set_keep hs
  obtain ⟨hL, hR, hO⟩ := Fld.set_rest hs
  refine ⟨fun g => h.cap g, fun g i hi => ?_, fun t => h.scap t, fun t => ?_, fun t => ?_, h.pcap,
    fun k => ?_, h.lcapA, h.lcapN, fun k i hi => ?_, fun k i hi j hj => ?_, h.wcap,
    fun c hc j hj => ?_,
    h.ocap, fun o => ?_, fun pr hpr => ?_, by rw [hP]; exact h.pwH, h.frec⟩
  · simp only [State.write]
    rw [Fld.get_set hs g hi]
    by_cases eg : arrF p g = arrF p f
    · have := arrF_inj eg; subst this
      rw [ite_eq_left eg]; simp only [State.upd]
      by_cases ei : i = j
      · subst ei; simp
      · rw [ite_eq_right ei, ite_eq_right (fun h => ei h.2)]; exact h.mem g i hi
    · rw [ite_eq_right eg, ite_eq_right (fun h' => eg (by rw [h'.1]))]; exact h.mem g i hi
  · rw [write_other (arr_ne (by simp)), hT]; exact h.smem t
  · rw [hT]; exact h.sle t
  · rw [write_other (arr_ne (by simp)), hP]; exact h.pmem k
  · rw [write_other (arr_ne (by simp)), hL]; exact h.llen k i hi
  · rw [hL] at hj ⊢
    rw [write_other (arr_ne (by simp)), write_other (arr_ne (by simp))]; exact h.lmem k i hi j hj
  · rw [write_other (arr_ne (by simp)), hR]; exact h.wmem c hc j hj
  · rw [write_other (arr_ne (by simp)), hO]; exact h.omem o
  · rw [Fld.set_prep hs] at hpr; exact h.prepC pr hpr

theorem Enc.push {s : Core} {m : State} (h : Enc p κ s m) {t : Tbl} (ht : t.size s < κ.tbl t) :
    Enc p κ (t.push s) (m.write (arrS p t) 0 (t.size s + 1)) := by
  obtain ⟨hL, hR, hO⟩ := Tbl.push_rest s t
  refine ⟨fun g => h.cap g, fun g i hi => ?_, fun t' => h.scap t', fun t' => ?_, fun t' => ?_,
    h.pcap, fun k => ?_, h.lcapA, h.lcapN, fun k i hi => ?_, fun k i hi j hj => ?_, h.wcap,
    fun c hc j hj => ?_, h.ocap, fun o => ?_, fun pr hpr => ?_, by cases t <;> exact h.pwH, h.frec⟩
  · rw [write_other (arr_ne (by simp)), Tbl.push_get]; exact h.mem g i hi
  · simp only [State.write, Tbl.push_size]
    by_cases e : arrS p t' = arrS p t
    · have := arrS_inj e; subst this; rw [ite_eq_left e, ite_eq_left rfl]; simp [State.upd]
    · rw [ite_eq_right e, ite_eq_right (fun h' => e (by rw [h']))]; exact h.smem t'
  · rw [Tbl.push_size]; split
    · next e => subst e; omega
    · exact h.sle t'
  · rw [write_other (arr_ne (by simp)), Tbl.push_P]; exact h.pmem k
  · rw [write_other (arr_ne (by simp)), hL]; exact h.llen k i hi
  · rw [hL] at hj ⊢
    rw [write_other (arr_ne (by simp)), write_other (arr_ne (by simp))]; exact h.lmem k i hi j hj
  · rw [write_other (arr_ne (by simp)), hR]; exact h.wmem c hc j hj
  · rw [write_other (arr_ne (by simp)), hO]; exact h.omem o
  · have : (t.push s).prep = s.prep := by cases t <;> rfl
    rw [this] at hpr; exact h.prepC pr hpr

/-! ### Expressions -/

theorem mul_add_inj {i i' j j' w : Nat} (hj : j < w) (hj' : j' < w) (h : i * w + j = i' * w + j') :
    i = i' ∧ j = j' := by
  have hw : 0 < w := by omega
  have h1 : (i * w + j) / w = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hj]; simp
  have h2 : (i' * w + j') / w = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hj']; simp
  have h3 : (i * w + j) % w = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have h4 : (i' * w + j') % w = j' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
  rw [h] at h1 h3; exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

theorem Enc.stride_lt {s : Core} {m : State} (h : Enc p κ s m) {k : LK} {i j : Nat}
    (hi : i < κ.lrec k)
    (hj : j < κ.lcap k) : i * k.stride κ.lcap + j < κ.lrec k * κ.lcap k := by
  cases k with
  | freeG =>
    have := h.frec; have hi0 : i = 0 := by omega
    subst hi0; simp only [LK.stride, mul_zero, zero_add, this, one_mul, gt_iff_lt]; exact hj
  | _ => exact lt_mul_add hi hj

theorem Enc.stride_inj {s : Core} {m : State} (h : Enc p κ s m) {k : LK} {i i' j j' : Nat}
    (hi : i < κ.lrec k)
    (hi' : i' < κ.lrec k) (hj : j < κ.lcap k) (hj' : j' < κ.lcap k)
    (e : i * k.stride κ.lcap + j = i' * k.stride κ.lcap + j') : i = i' ∧ j = j' := by
  cases k with
  | freeG =>
    have := h.frec
    have h0 : i = 0 := by omega
    have h0' : i' = 0 := by omega
    subst h0; subst h0'; simp only [LK.stride, mul_zero, zero_add] at e; exact ⟨rfl, e⟩
  | _ => exact mul_add_inj hj hj' e

theorem Enc.rowW_eval {s : Core} {m : State} (h : Enc p κ s m) : (rowW p).eval m = some κ.pw := by
  have := h.pmem .H
  simp only [PF.get, PF.idx] at this
  simp [rowW, Expr.eval, h.pcap, PF.idx, this, h.pwH, BinOp.eval]

theorem rowW_maxv (p : Nat) (m : State) : (rowW p).maxv m ≥ 0 := Nat.zero_le _

theorem Exp.ev_compile {s : Core} {m : State} {L : Loc} (h : Enc p κ s m) (hL : m.loc = L) :
    ∀ (e : Exp) {v : Nat}, e.ev κ s L = some v → (e.compile p κ).eval m = some v
  | .lit n, v, hv => by simp [Exp.ev] at hv; simp [Exp.compile, hv]
  | .var x, v, hv => by simp [Exp.ev] at hv; simp [Exp.compile, hL, hv]
  | .rd f i, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨j, hj, hv⟩ := hv
    split at hv
    · next hlt =>
      cases hv
      simp only [Exp.compile, Expr.eval, Exp.ev_compile h hL i hj, Option.bind_some,
        h.cap f, ite_eq_left hlt, h.mem f j hlt]
    · simp only [reduceCtorEq] at hv
  | .size t, v, hv => by
    simp only [Exp.ev, Option.some.injEq] at hv; subst hv
    simp [Exp.compile, h.scap t, h.smem t]
  | .prm k, v, hv => by
    simp only [Exp.ev, Option.some.injEq] at hv; subst hv
    simp [Exp.compile, h.pcap, h.pmem k, k.idx_lt]
  | .bin op a b, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    simp only [Exp.compile, Expr.eval, Exp.ev_compile h hL a hx, Exp.ev_compile h hL b hy,
      Option.bind_some, hv]
  | .un op a, v, hv => by
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, hv⟩ := hv
    simp only [Exp.compile, Expr.eval, Exp.ev_compile h hL a hx, Option.map_some, hv]
  | .lrd k b i j, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      have hle := (h.llen k x hc.1).2
      have hm := h.lmem k x hc.1 y hc.2
      have hlt : x * k.stride κ.lcap + y < m.cap (arrL p k b) := by
        rw [h.lcapA]; exact h.stride_lt hc.1 (by omega)
      simp only [Exp.compile, Expr.eval, Exp.ev_compile h hL i hx, Exp.ev_compile h hL j hy,
        Option.bind_some, BinOp.eval, ite_eq_left hlt]
      cases b <;> simp [hm.1, hm.2]
    · simp only [reduceCtorEq] at hv
  | .llen k i, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      simp only [Exp.compile, Expr.eval, Exp.ev_compile h hL i hx, Option.bind_some,
        h.lcapN k, ite_eq_left hc, (h.llen k x hc).1]
    · simp only [reduceCtorEq] at hv
  | .prd c j, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      have hlt : x * κ.pw + y < m.cap (arrPath p) := by rw [h.wcap]; exact lt_mul_add hc.1 hc.2
      simp only [Exp.compile, Expr.eval, Exp.ev_compile h hL c hx, Exp.ev_compile h hL j hy,
        h.rowW_eval, Option.bind_some, BinOp.eval, ite_eq_left hlt, h.wmem x hc.1 y hc.2]
    · simp only [reduceCtorEq] at hv
  | .opt o, v, hv => by
    simp only [Exp.ev, Option.some.injEq] at hv; subst hv
    simp [Exp.compile, h.ocap o, h.omem o]

theorem evList_compile {s : Core} {m : State} {L : Loc} (h : Enc p κ s m) (hL : m.loc = L) :
    ∀ (es : List Exp) {vs : List Nat}, evList κ s L es = some vs →
      Machine.evalList m (es.map (Exp.compile p κ)) = some vs
  | [], vs, hv => by simp only [evList, List.mapM_nil, Option.pure_def, Option.some.injEq,
      List.nil_eq] at hv; subst hv; rfl
  | e :: es, vs, hv => by
    simp only [evList, List.mapM_cons] at hv
    cases he : e.ev κ s L with
    | none => simp [he] at hv
    | some v =>
      cases hes : es.mapM (·.ev κ s L) with
      | none => simp only [he, hes, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at hv
      | some ws =>
        simp only [he, hes, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at hv; subst hv
        have := evList_compile h hL es (vs := ws) hes
        simp only [Machine.evalList, List.map_cons, List.mapM_cons] at this ⊢
        rw [Exp.ev_compile h hL e he, this]; rfl

theorem costList_compile (es : List Exp) :
    Machine.costList (es.map (Exp.compile p κ)) = costList es := by
  simp only [Machine.costList, costList, List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => Exp.cost_compile p κ e)

/-- Memory reasoning on written machine states: which arrays a write changes. -/
macro "simplifyMemory" : tactic => `(tactic| simp only [st_write_mem, st_bump_mem, st_leave_mem,
    st_write_cap,
  st_bump_cap, st_leave_cap, arr_eq_iff, reduceCtorEq, ite_false,
  Slot.opt.injEq, Slot.lst.injEq, Slot.len.injEq])

/-! ### Statements -/

/-- Outcome `r` of the source and outcome `o` of the compiled code agree. -/
def Agree (p : Nat) (κ : Caps) : Res → Out → Prop
  | .ok s L n, o => o.status = .ok ∧ Enc p κ s o.st ∧ o.st.loc = L ∧ o.cost = n
  | .fail s L n, o => o.status = .fail ∧ Enc p κ s o.st ∧ o.st.loc = L ∧ o.cost = n
  | .bug, _ => True

theorem Agree.addCost {r : Res} {o : Out} (h : Agree p κ r o) (c : Nat) :
    Agree p κ (r.addCost c) ⟨o.st, c + o.cost, o.status⟩ := by
  cases r with
  | ok s L n => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, by simp [h4]⟩
  | fail s L n => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, by simp [h4]⟩
  | bug => trivial

theorem Agree.bind {r : Res} {o : Out} (h : Agree p κ r o) {g : Core → Loc → Res} {k : State → Out}
    (hg : ∀ s L m, Enc p κ s m → m.loc = L → Agree p κ (g s L) (k m)) :
    Agree p κ (r.bind g) (o.bind k) := by
  cases r with
  | ok s L n =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    have := (hg s L o.st h2 h3).addCost n
    simp only [Res.bind, Out.bind, h1]
    rw [h4]; exact this
  | fail s L n =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [Res.bind, Out.bind, h1]; exact ⟨h1, h2, h3, h4⟩
  | bug => trivial

/-- **Frame**: the encoding of `s'` in `m'`, from that of `s` in `m`, for the parts both keep. -/
theorem Enc.frame {s s' : Core} {m m' : State} (h : Enc p κ s m) (hcap : m'.cap = m.cap)
    (hF : ∀ (f : Fld) j, f.get s' j = f.get s j) (hT : ∀ t : Tbl, t.size s' = t.size s)
    (hP : s'.P = s.P)
    (hFm : ∀ f, m'.mem (arrF p f) = m.mem (arrF p f))
    (hSm : ∀ t, m'.mem (arrS p t) = m.mem (arrS p t))
    (hPm : m'.mem (arrP p) = m.mem (arrP p))
    (hlen : ∀ k : LK, ∀ i < κ.lrec k, m'.mem (arrLen p k) i = (k.view s' i).length ∧
      (k.view s' i).length ≤ κ.lcap k)
    (hlm : ∀ k : LK, ∀ i < κ.lrec k, ∀ j < (k.view s' i).length,
      m'.mem (arrL p k false) (i * k.stride κ.lcap + j) = ((k.view s' i).getD j (0, 0)).1 ∧
        m'.mem (arrL p k true) (i * k.stride κ.lcap + j) = ((k.view s' i).getD j (0, 0)).2)
    (hw : ∀ c < κ.tbl .C, ∀ j < κ.pw, m'.mem (arrPath p) (c * κ.pw + j) = (rowOf s' c).getX j)
    (ho : ∀ o : OF, m'.mem (arrO p o) 0 = o.get s')
    (hpc : ∀ pr, s'.prep = some pr → pr.chunk < κ.tbl .C) : Enc p κ s' m' :=
  ⟨fun f => by rw [hcap]; exact h.cap f, fun f i hi => by rw [hFm, hF]; exact h.mem f i hi,
    fun t => by rw [hcap]; exact h.scap t, fun t => by rw [hSm, hT]; exact h.smem t,
    fun t => by rw [hT]; exact h.sle t, by rw [hcap]; exact h.pcap,
    fun k => by rw [hPm, hP]; exact h.pmem k, fun k b => by rw [hcap]; exact h.lcapA k b,
    fun k => by rw [hcap]; exact h.lcapN k, hlen, hlm, by rw [hcap]; exact h.wcap, hw,
    fun o => by rw [hcap]; exact h.ocap o, ho, hpc, by rw [hP]; exact h.pwH, h.frec⟩

/-- A step that changes only the optional records, and only their cells. -/
theorem Enc.optOnly {s s' : Core} {m m' : State} (h : Enc p κ s m) (hcap : m'.cap = m.cap)
    (hF : ∀ (f : Fld) j, f.get s' j = f.get s j) (hT : ∀ t : Tbl, t.size s' = t.size s)
    (hP : s'.P = s.P)
    (hv : ∀ (k : LK) i, k.view s' i = k.view s i)
    (hR : ∀ c < κ.tbl .C, ∀ j < κ.pw, (rowOf s' c).getX j = (rowOf s c).getX j)
    (hmem : ∀ sl : Slot, (∀ o, sl ≠ .opt o) → m'.mem (arr p sl) = m.mem (arr p sl))
    (ho : ∀ o : OF, m'.mem (arrO p o) 0 = o.get s')
    (hpc : ∀ pr, s'.prep = some pr → pr.chunk < κ.tbl .C) : Enc p κ s' m' :=
  h.frame hcap hF hT hP (fun f => hmem _ (by simp)) (fun t => hmem _ (by simp)) (hmem _ (by simp))
    (fun k i hi => by rw [hmem _ (by simp), hv]; exact h.llen k i hi)
    (fun k i hi j hj => by
      rw [hv] at hj ⊢; rw [hmem _ (by simp), hmem _ (by simp)]; exact h.lmem k i hi j hj)
    (fun c hc j hj => by rw [hmem _ (by simp), hR c hc j hj]; exact h.wmem c hc j hj) ho hpc

theorem exec_st1 {m : State} {a : Arr} {e : Expr} {v : Nat} (hc : m.cap a = 1)
    (he : e.eval m = some v) :
    exec (st1 a e) m = ⟨((m.bump 0).bump (e.maxv m)).write a 0 v, 2 + e.cost, .ok⟩ := by
  simp [st1, exec, he, hc]

theorem sim_jobClear {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L) :
    Agree p κ (evalF κ .jobClear s L) (exec (Stm.compile p κ .jobClear) m) := by
  simp only [evalF, Stm.compile, st1, exec, Out.bind, Expr.eval, h.ocap, zero_lt_one, ↓reduceIte,
      State.write, State.bump, Expr.maxv, zero_le, sup_of_le_left, Expr.cost, Nat.reduceAdd,
      arr_eq_iff, Slot.opt.injEq, reduceCtorEq]
  refine ⟨rfl, ?_, hL, rfl⟩
  have hv : ∀ (k : LK) i, k.view { s with resJob := none } i =
              k.view s i := fun k i => by
                cases k <;> rfl
  refine h.frame rfl (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
      (fun t => by cases t <;> rfl) rfl
    (fun f => by funext i; simp) (fun t => by funext i; simp) (by funext i; simp)
    (fun k i hi => by simp only [hv]; simpa using h.llen k i hi)
    (fun k i hi j hj => by simp only [hv] at hj ⊢; simpa using h.lmem k i hi j hj)
    (fun c hc j hj => by simpa [rowOf] using h.wmem c hc j hj)
    (fun o => ?_) (fun pr hpr => h.prepC pr hpr)
  have := h.omem o
  cases o <;> simp only [OF.get, b2n, arr_eq_iff, Slot.opt.injEq, reduceCtorEq, ↓reduceIte,
      State.upd, Option.isSome_none, Bool.false_eq_true] at this ⊢ <;> exact this

theorem evList_cons_some {s : Core} {L : Loc} {e : Exp} {es : List Exp} {v : Nat} {vs : List Nat} :
    evList κ s L (e :: es) = some (v :: vs) ↔ e.ev κ s L = some v ∧ evList κ s L es = some vs := by
  simp only [evList, List.mapM_cons]
  cases e.ev κ s L <;> cases es.mapM (·.ev κ s L) <;> simp

theorem pcEnc_dec {t a b c d : Nat} {pc : JobPc} (h : pcDec t a b c d = some pc) :
    pcEnc pc = (t, a, b, c, d) := by
  unfold pcDec at h
  rcases t with _ | _ | _ | _ | _ | t <;>
    simp only [Option.ite_none_right_eq_some, Option.some.injEq, zero_add,
      Nat.reduceAdd, reduceCtorEq] at h
  · rcases h with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; rfl
  · rcases h with ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩; rfl
  · rcases h with ⟨⟨rfl, rfl, rfl⟩, rfl⟩; rfl
  · rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  · cases h; rfl

theorem sim_jobSet {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (x y z t a b c d : Exp) :
    Agree p κ (evalF κ (.jobSet x y z t a b c d) s L)
      (exec (Stm.compile p κ (.jobSet x y z t a b c d)) m) := by
  simp only [evalF]
  split
  · next vx vy vz vt va vb vc vd hv =>
    have hargs := evList_compile h hL _ hv
    split
    · next pc hpc =>
      have he := pcEnc_dec hpc
      simp only [Stm.compile, exec, hargs]
      generalize hm0 : (m.bump (maxvList m
          (List.map (Exp.compile p κ) [x, y, z, t, a, b, c, d]))).enter
        ["x", "y", "z", "t", "a", "b", "c", "d"] [vx, vy, vz, vt, va, vb, vc, vd] = m0
      have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
      have hmem0 : m0.mem = m.mem := by rw [← hm0]; rfl
      have hcap0 : m0.cap = m.cap := by rw [← hm0]; rfl
      have hl0 : m0.loc "x" = vx ∧ m0.loc "y" = vy ∧ m0.loc "z" = vz ∧ m0.loc "t" = vt ∧
          m0.loc "a" = va ∧
          m0.loc "b" = vb ∧ m0.loc "c" = vc ∧ m0.loc "d" = vd := by
        rw [← hm0]; simp
      simp only [st1, exec, Out.bind, Expr.eval,
        hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
        Expr.maxv]
      refine ⟨rfl, ?_, by simp [hL], ?_⟩
      · have hv : ∀ (k : LK) i,
            k.view { s with resJob := some { x := vx, y := vy, z := vz, pc := pc } } i =
            k.view s i := fun k i => by
              cases k <;> rfl
        refine h.frame (by simp only [st_leave_cap, st_write_cap, st_bump_cap, hcap0])
          (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
              (fun t => by cases t <;> rfl) rfl
          (fun f => by funext i; simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff,
            reduceCtorEq, ite_false, hmem0])
          (fun t => by funext i; simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff,
            reduceCtorEq, ite_false, hmem0])
          (by funext i; simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff,
              reduceCtorEq, ite_false,
            hmem0])
          (fun k i hi => by
            simp only [hv, st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq,
                ite_false, hmem0]
            exact h.llen k i hi)
          (fun k i hi j hj => by
            simp only [hv] at hj ⊢
            simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq,
                ite_false, hmem0]
            exact h.lmem k i hi j hj)
          (fun c hc j hj => by
            simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq,
                ite_false, hmem0]
            exact h.wmem c hc j hj)
          (fun o => ?_) (fun pr hpr => h.prepC pr hpr)
        have := h.omem o
        cases o <;> simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff,
            Slot.opt.injEq, reduceCtorEq,
          ite_false, ite_true, hmem0, State.upd, OF.get, he] at this ⊢ <;>
            first | exact this | rfl
      · simp only [costList_compile]
        simp [Expr.cost, costList]
        omega
    · trivial
  · trivial

theorem sim_pcSet {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (t a b c d : Exp) :
    Agree p κ (evalF κ (.pcSet t a b c d) s L) (exec (Stm.compile p κ (.pcSet t a b c d)) m) := by
  simp only [evalF]
  split
  · next jb vt va vb vc vd hj hv =>
    have hargs := evList_compile h hL _ hv
    split
    · next pc hpc =>
      have he := pcEnc_dec hpc
      simp only [Stm.compile, exec, hargs]
      generalize hm0 : (m.bump (maxvList m (List.map (Exp.compile p κ) [t, a, b, c, d]))).enter
        ["t", "a", "b", "c", "d"] [vt, va, vb, vc, vd] = m0
      have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
      have hmem0 : m0.mem = m.mem := by rw [← hm0]; rfl
      have hcap0 : m0.cap = m.cap := by rw [← hm0]; rfl
      have hl0 : m0.loc "t" = vt ∧ m0.loc "a" = va ∧ m0.loc "b" = vb ∧ m0.loc "c" = vc ∧
          m0.loc "d" = vd := by
        rw [← hm0]; simp
      simp only [st1, exec, Out.bind, Expr.eval,
        hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
        Expr.maxv]
      refine ⟨rfl, ?_, by simp [hL], ?_⟩
      · refine h.optOnly (by simp only [st_leave_cap, st_write_cap, st_bump_cap, hcap0])
          (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
              (fun t => by cases t <;> rfl) rfl
          (fun k i => by cases k <;> rfl) (fun c _ j _ => rfl)
          (fun sl hsl => by funext i; simp only [st_leave_mem, st_write_mem, st_bump_mem,
              arr_eq_iff, hsl,
            ite_false, hmem0]) (fun o => ?_) (fun pr hpr => h.prepC pr hpr)
        have := h.omem o
        cases o <;> simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff,
            Slot.opt.injEq, reduceCtorEq,
          ite_false, ite_true, hmem0, State.upd, OF.get, he, hj] at this ⊢ <;>
            exact this
      · simp only [costList_compile]
        simp [Expr.cost, costList]
        omega
    · trivial
  · trivial

theorem getX_replicate0 (n j : Nat) : (Array.replicate n (0 : Nat)).getX j = 0 := by
  simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem sim_prepInit {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (c b : Exp) :
    Agree p κ (evalF κ (.prepInit c b) s L) (exec (Stm.compile p κ (.prepInit c b)) m) := by
  simp only [evalF]
  split
  · next x y hx hy =>
    split
    · next hc =>
      obtain ⟨hn, hxC, hz, hpw⟩ := hc
      have hargs : Machine.evalList m ([c, b].map (Exp.compile p κ)) = some [x, y] :=
        evList_compile h hL [c, b] (by simp [evList, hx, hy])
      have hpn : s.prep = none := by simpa using hn
      simp only [List.map_cons, List.map_nil] at hargs
      simp only [Stm.compile, exec, hargs]
      generalize hm0 : (m.bump (maxvList m [Exp.compile p κ c, Exp.compile p κ b])).enter
        ["c", "b"] [x, y] = m0
      have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
      have hmem0 : m0.mem = m.mem := by rw [← hm0]; rfl
      have hcap0 : m0.cap = m.cap := by rw [← hm0]; rfl
      have hl0 : m0.loc "c" = x ∧ m0.loc "b" = y := by rw [← hm0]; simp
      simp only [st1, exec, Out.bind, Expr.eval,
        hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
        Expr.maxv]
      refine ⟨rfl, ?_, by simp [hL], ?_⟩
      · refine h.optOnly (by simp only [st_leave_cap, st_write_cap, st_bump_cap, hcap0])
          (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
              (fun t => by cases t <;> rfl) rfl
          (fun k i => by cases k <;> rfl) (fun c' _ j hj => ?_)
          (fun sl hsl => by funext i; simp only [st_leave_mem, st_write_mem, st_bump_mem,
              arr_eq_iff, hsl,
            ite_false, hmem0]) (fun o => ?_)
          (fun pr hpr => by
            simp only [Option.some.injEq] at hpr
            rw [← hpr]
            exact hxC)
        · simp only [rowOf, hpn]
          by_cases e : c' = x
          · subst e; simp only [ite_true,
              getX_replicate0]; exact (hz j hj).symm.trans (by simp [rowOf, hpn])
          · simp [e]
        · have := h.omem o
          cases o <;> simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff,
              Slot.opt.injEq,
            reduceCtorEq, ite_false, ite_true, hmem0, State.upd, OF.get, hpn] at this ⊢ <;>
            first | exact this | rfl
      · simp [Expr.cost,  Exp.cost_compile]
        omega
    · trivial
  · trivial

theorem sim_prepSet {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (hh b t : Exp) :
    Agree p κ (evalF κ (.prepSet hh b t) s L) (exec (Stm.compile p κ (.prepSet hh b t)) m) := by
  simp only [evalF]
  split
  · next pr vh vb vt hpr hvh hvb hvt =>
    have hargs : Machine.evalList m ([hh, b, t].map (Exp.compile p κ)) = some [vh, vb, vt] :=
      evList_compile h hL [hh, b, t] (by simp [evList, hvh, hvb, hvt])
    simp only [List.map_cons, List.map_nil] at hargs
    simp only [Stm.compile, exec, hargs]
    generalize hm0 : (m.bump (maxvList m [Exp.compile p κ hh, Exp.compile p κ b,
      Exp.compile p κ t])).enter ["h", "b", "t"] [vh, vb, vt] = m0
    have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
    have hmem0 : m0.mem = m.mem := by rw [← hm0]; rfl
    have hcap0 : m0.cap = m.cap := by rw [← hm0]; rfl
    have hl0 : m0.loc "h" = vh ∧ m0.loc "b" = vb ∧ m0.loc "t" = vt := by rw [← hm0]; simp
    simp only [st1, exec, Out.bind, Expr.eval,
      hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
      Expr.maxv]
    refine ⟨rfl, ?_, by simp [hL], ?_⟩
    · refine h.optOnly (by simp only [st_leave_cap, st_write_cap, st_bump_cap, hcap0])
        (fun f j => by cases f <;> (rename_i k; cases k <;> rfl)) (fun t => by cases t <;> rfl) rfl
        (fun k i => by cases k <;> rfl) (fun c' _ j _ => by simp [rowOf, hpr])
        (fun sl hsl => by funext i; simp only [st_leave_mem, st_write_mem, st_bump_mem,
            arr_eq_iff, hsl,
          ite_false, hmem0]) (fun o => ?_)
        (fun pr' hpr' => by
          simp only [Option.some.injEq] at hpr'
          rw [← hpr']
          exact h.prepC pr hpr)
      have := h.omem o
      cases o <;> simp only [st_leave_mem, st_write_mem, st_bump_mem, arr_eq_iff, Slot.opt.injEq,
        reduceCtorEq, ite_false, ite_true, hmem0, State.upd, OF.get, hpr] at this ⊢ <;>
        exact this
    · simp [Expr.cost,  Exp.cost_compile]
      omega
  · trivial

theorem sim_prepCommit {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L) :
    Agree p κ (evalF κ .prepCommit s L) (exec (Stm.compile p κ .prepCommit) m) := by
  simp only [evalF]
  split
  · next pr hpr =>
    simp only [Stm.compile, st1, exec, Out.bind, Expr.eval, h.ocap, zero_lt_one, ↓reduceIte,
        State.write, State.bump, Expr.maxv, zero_le, sup_of_le_left, Expr.cost,
        Nat.reduceAdd, arr_eq_iff, Slot.opt.injEq, reduceCtorEq]
    refine ⟨rfl, ?_, hL, rfl⟩
    refine h.optOnly rfl
      (fun f j => by cases f <;> (rename_i k; cases k <;> rfl)) (fun t => by cases t <;> rfl) rfl
      (fun k i => by cases k <;> rfl) (fun c' _ j _ => ?_)
      (fun sl hsl => by funext i; simp [hsl]) (fun o => ?_) (fun pr' hpr' => by simp only [
          reduceCtorEq] at hpr')
    · simp only [rowOf, hpr, OrderMaintenance.Proof.Top.getX_setX']
    · have := h.omem o
      cases o <;> simp only [OF.get, b2n, hpr, Option.isSome_some, ↓reduceIte, arr_eq_iff,
          Slot.opt.injEq, reduceCtorEq, State.upd, Option.isSome_none,
          Bool.false_eq_true] at this ⊢ <;> exact this
  · trivial

theorem sim_pwr {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L) (c j e : Exp) :
    Agree p κ (evalF κ (.pwr c j e) s L) (exec (Stm.compile p κ (.pwr c j e)) m) := by
  simp only [evalF]
  split
  · next x y v hx hy hv =>
    split
    · next hc =>
      obtain ⟨hxC, hyw, hnp⟩ := hc
      have hlt : x * κ.pw + y < m.cap (arrPath p) := by rw [h.wcap]; exact lt_mul_add hxC hyw
      simp only [Stm.compile, exec, Expr.eval, Exp.ev_compile h hL c hx, Exp.ev_compile h hL j hy,
        Exp.ev_compile h hL e hv, h.rowW_eval, Option.bind_some, BinOp.eval]
      rw [ite_eq_left (by simpa using hlt)]
      refine ⟨rfl, ?_, by simp [hL], by simp [Exp.cost_compile, Expr.cost, rowW]; omega⟩
      have hv : ∀ (k : LK) i, k.view { s with path := s.path.setX x ((s.path.getX x).setX y v) } i =
          k.view s i := fun k i => by
            cases k <;> rfl
      refine h.frame (by simplifyMemory) (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
        (fun t => by cases t <;> rfl) rfl
        (fun f => by funext i; simplifyMemory) (fun t => by funext i; simplifyMemory)
        (by funext i; simplifyMemory) (fun k i hi => by
          rw [hv]
          simplifyMemory
          exact h.llen k i hi)
        (fun k i hi j hj => by rw [hv] at hj ⊢; simplifyMemory; exact h.lmem k i hi j hj)
        (fun c' hc' j' hj' => ?_) (fun o => by
          simplifyMemory
          have := h.omem o
          cases o <;> exact this)
        (fun pr hpr => h.prepC pr hpr)
      have hrow : (rowOf { s with path := s.path.setX x ((s.path.getX x).setX y v) } c').getX j' =
          if c' = x ∧ j' = y then v else (rowOf s c').getX j' := by
        unfold notPrep at hnp
        simp only [rowOf]
        cases hp : s.prep with
        | none =>
          simp only [OrderMaintenance.Proof.Top.getX_setX']
          by_cases e2 : c' = x
          · subst e2; by_cases e3 : j' = y <;> simp [e3, OrderMaintenance.Proof.Top.getX_setX']
          · simp [e2]
        | some pr =>
          rw [hp] at hnp
          by_cases e1 : c' = pr.chunk
          · subst e1; simp [Ne.symm hnp]
          · simp only [e1, ite_false, OrderMaintenance.Proof.Top.getX_setX']
            by_cases e2 : c' = x
            · subst e2; by_cases e3 : j' = y <;> simp [e3, OrderMaintenance.Proof.Top.getX_setX']
            · simp [e2]
      rw [hrow]
      simp only [st_write_mem, st_bump_mem, ite_true, State.upd]
      by_cases e : c' * κ.pw + j' = x * κ.pw + y
      · obtain ⟨rfl, rfl⟩ := mul_add_inj hj' hyw e
        simp
      · rw [ite_eq_right e, ite_eq_right (fun h' => e (by rw [h'.1, h'.2]))]
        exact h.wmem c' hc' j' hj'
    · trivial
  · trivial

theorem sim_rowReset {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L) (c : Exp) :
    Agree p κ (evalF κ (.rowReset c) s L) (exec (Stm.compile p κ (.rowReset c)) m) := by
  simp only [evalF]
  split
  · next x hx =>
    split
    · next hc =>
      obtain ⟨hxC, hz, hnp, hpw⟩ := hc
      simp only [Stm.compile, exec]
      refine ⟨rfl, ?_, hL, rfl⟩
      refine h.frame rfl (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
        (fun t => by cases t <;> rfl) rfl (fun f => rfl) (fun t => rfl) rfl
        (fun k i hi => by
          rw [show k.view { s with path := s.path.setX x (Array.replicate (s.P.H + 1) NIL) } i =
              k.view s i
            from by cases k <;> rfl]; exact h.llen k i hi)
        (fun k i hi j hj => by
          rw [show k.view { s with path := s.path.setX x (Array.replicate (s.P.H + 1) NIL) } i =
              k.view s i
            from by cases k <;> rfl] at hj ⊢; exact h.lmem k i hi j hj)
        (fun c' hc' j' hj' => ?_) (fun o => by have := h.omem o; cases o <;> exact this)
        (fun pr hpr => h.prepC pr hpr)
      rw [h.wmem c' hc' j' hj']
      unfold notPrep at hnp
      simp only [rowOf]
      cases hp : s.prep with
      | none =>
        simp only [OrderMaintenance.Proof.Top.getX_setX']
        by_cases e : c' = x
        · subst e; rw [ite_eq_left rfl, getX_replicate0]
          have := hz j' hj'; simp only [rowOf, hp] at this; exact this
        · rw [ite_eq_right e]
      | some pr =>
        rw [hp] at hnp
        by_cases e1 : c' = pr.chunk
        · simp [e1]
        · simp only [e1, ite_false, OrderMaintenance.Proof.Top.getX_setX']
          by_cases e : c' = x
          · subst e; rw [ite_eq_left rfl, getX_replicate0]
            have := hz j' hj'; simp only [rowOf, hp, e1, ite_false] at this; exact this
          · simp [e]
    · trivial
  · trivial

theorem sim_prepPath {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (j e : Exp) :
    Agree p κ (evalF κ (.prepPath j e) s L) (exec (Stm.compile p κ (.prepPath j e)) m) := by
  simp only [evalF]
  split
  · next pr y v hpr hy hv =>
    split
    · next hyw =>
      have hpc := h.prepC pr hpr
      have hch : m.mem (arrO p .prepChunk) 0 = pr.chunk := by rw [h.omem]; simp [OF.get, hpr]
      have hlt : pr.chunk * κ.pw + y < m.cap (arrPath p) := by rw [h.wcap]; exact lt_mul_add hpc hyw
      simp only [Stm.compile, exec, Expr.eval, Exp.ev_compile h hL j hy, Exp.ev_compile h hL e hv,
        h.rowW_eval, Option.bind_some, BinOp.eval, h.ocap, Nat.zero_lt_one, ite_true, hch]
      rw [ite_eq_left (by simpa using hlt)]
      refine ⟨rfl, ?_, by simp [hL], by simp [Exp.cost_compile, Expr.cost, rowW]; omega⟩
      have hv' : ∀ (k : LK) i,
          k.view { s with prep := some { pr with path := pr.path.setX y v } } i =
          k.view s i := fun k i => by
            cases k <;> rfl
      refine h.frame (by simplifyMemory) (fun f j => by cases f <;> (rename_i k; cases k <;> rfl))
        (fun t => by cases t <;> rfl) rfl
        (fun f => by funext i; simplifyMemory) (fun t => by funext i; simplifyMemory)
        (by funext i; simplifyMemory) (fun k i hi => by
          rw [hv']
          simplifyMemory
          exact h.llen k i hi)
        (fun k i hi j hj => by rw [hv'] at hj ⊢; simplifyMemory; exact h.lmem k i hi j hj)
        (fun c' hc' j' hj' => ?_)
        (fun o => by simplifyMemory; have := h.omem o; cases o <;> simpa [OF.get, hpr] using this)
        (fun pr' hpr' => by simp only [Option.some.injEq] at hpr'; rw [← hpr']; exact hpc)
      simp only [st_write_mem, st_bump_mem, ite_true, State.upd, rowOf]
      by_cases e1 : c' = pr.chunk
      · subst e1
        simp only [ite_true, OrderMaintenance.Proof.Top.getX_setX']
        by_cases e2 : j' = y
        · subst e2; simp
        · rw [ite_eq_right (fun h' => e2 (mul_add_inj hj' hyw h').2),
          ite_eq_right e2, h.wmem _ hc' j' hj']
          simp [rowOf, hpr]
      · rw [ite_eq_right (fun h' => e1 (mul_add_inj hj' hyw h').1),
        ite_eq_right e1, h.wmem c' hc' j' hj']
        simp [rowOf, hpr, e1]
    · trivial
  · trivial

theorem LK.put_prep (s : Core) (i : Nat) (l : List (Nat × Nat)) (k : LK) :
    (k.put s i l).prep = s.prep := by
  cases k <;> rfl

/-- **Frame for a list replacement**: only list `k` of record `x` changes. -/
theorem Enc.listUpd {s s' : Core} {m m' : State} (h : Enc p κ s m) {k : LK} {x : Nat}
    {l' : List (Nat × Nat)} (hs : k.set κ s x l' = some s') (hcap : m'.cap = m.cap)
    (hmem : ∀ sl : Slot, (∀ b, sl ≠ .lst k b) → sl ≠ .len k → m'.mem (arr p sl) = m.mem (arr p sl))
    (hlen : ∀ i, i ≠ x → m'.mem (arrLen p k) i = m.mem (arrLen p k) i)
    (hlenx : m'.mem (arrLen p k) x = l'.length)
    (hel : ∀ b i j, i < κ.lrec k → i ≠ x → j < κ.lcap k →
      m'.mem (arrL p k b) (i * k.stride κ.lcap + j) = m.mem (arrL p k b) (i * k.stride κ.lcap + j))
    (helx : ∀ j < l'.length, m'.mem (arrL p k false) (x * k.stride κ.lcap + j) =
      (l'.getD j (0, 0)).1 ∧
      m'.mem (arrL p k true) (x * k.stride κ.lcap + j) = (l'.getD j (0, 0)).2) : Enc p κ s' m' := by
  unfold LK.set at hs
  split at hs
  · next hc =>
    cases hs
    obtain ⟨hr, hv, hlc, hxr⟩ := hc
    obtain ⟨hF, hT, hP, hR, hO⟩ := LK.put_keep s x l' k
    have hview := LK.view_put (s := s) hr hv
    refine h.frame hcap hF hT hP (fun f => hmem _ (by simp) (by simp))
        (fun t => hmem _ (by simp) (by simp))
      (hmem _ (by simp) (by simp)) (fun k' i hi => ?_) (fun k' i hi j hj => ?_)
      (fun c hc j hj => by rw [hmem _ (by simp) (by simp), hR]; exact h.wmem c hc j hj)
      (fun o => by rw [hmem _ (by simp) (by simp), hO]; exact h.omem o)
      (fun pr hpr => by rw [LK.put_prep] at hpr; exact h.prepC pr hpr)
    · rw [hview]
      by_cases ek : k' = k
      · subst ek
        by_cases ei : i = x
        · subst ei; rw [ite_eq_left ⟨rfl, rfl⟩, hlenx]; exact ⟨rfl, hlc⟩
        · rw [ite_eq_right (fun h' => ei h'.2), hlen i ei]; exact h.llen k' i hi
      · rw [ite_eq_right (fun h' => ek h'.1), hmem _ (by simp []) (by simp [ek])]
        exact h.llen k' i hi
    · rw [hview] at hj ⊢
      by_cases ek : k' = k
      · subst ek
        by_cases ei : i = x
        · subst ei; rw [ite_eq_left ⟨rfl, rfl⟩] at hj ⊢; exact helx j hj
        · rw [ite_eq_right (fun h' => ei h'.2)] at hj ⊢
          have hjc : j < κ.lcap k' := Nat.lt_of_lt_of_le hj (h.llen k' i hi).2
          rw [hel false i j hi ei hjc, hel true i j hi ei hjc]; exact h.lmem k' i hi j hj
      · rw [ite_eq_right (fun h' => ek h'.1)] at hj ⊢
        rw [hmem _ (by simp [ek]) (by simp []), hmem _ (by simp [ek]) (by simp [])]
        exact h.lmem k' i hi j hj
  · simp only [reduceCtorEq] at hs

theorem LK.set_lrec {s s' : Core} {k : LK} {x : Nat} {l : List (Nat × Nat)}
    (hs : k.set κ s x l = some s') :
    x < κ.lrec k ∧ l.length ≤ κ.lcap k := by
  unfold LK.set at hs; split at hs
  · next hc => exact ⟨hc.2.2.2, hc.2.2.1⟩
  · simp only [reduceCtorEq] at hs

theorem sim_lwr {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (k : LK) (b : Bool)
    (i j e : Exp) : Agree p κ (evalF κ (.lwr k b i j e) s L)
      (exec (Stm.compile p κ (.lwr k b i j e)) m) := by
  simp only [evalF]
  split
  · next x y v hx hy hv =>
    split
    · next hyl =>
      split
      · next s' hs =>
        obtain ⟨hxr, -⟩ := LK.set_lrec hs
        have hle := (h.llen k x hxr).2
        have hyc : y < κ.lcap k := Nat.lt_of_lt_of_le hyl hle
        have hlt : x * k.stride κ.lcap + y < m.cap (arrL p k b) := by
          rw [h.lcapA]; exact h.stride_lt hxr hyc
        simp only [Stm.compile, exec, Expr.eval, Exp.ev_compile h hL i hx, Exp.ev_compile h hL j hy,
          Exp.ev_compile h hL e hv, Option.bind_some, BinOp.eval]
        rw [ite_eq_left (by simpa using hlt)]
        refine ⟨rfl, ?_, by simp [hL], by simp [Exp.cost_compile, Expr.cost]; omega⟩
        refine h.listUpd hs (by simplifyMemory) (fun sl h1 _ => by
            funext q; simp only [st_write_mem, st_bump_mem, arr_eq_iff, h1 b, ite_false])
          (fun q _ => by simplifyMemory) (by
            simplifyMemory
            rw [(h.llen k x hxr).1, List.length_set])
          (fun b' q j' hq hqx hj' => ?_) (fun j' hj' => ?_)
        · simplifyMemory
          by_cases eb : b' = b
          · subst eb; simp only [and_self, ite_true, State.upd]
            rw [ite_eq_right (fun h' => hqx (h.stride_inj hq hxr hj' hyc h').1)]
          · simp [eb]
        · rw [List.length_set] at hj'
          have hm := h.lmem k x hxr j' hj'
          simplifyMemory
          by_cases ej : j' = y
          · subst ej
            cases b <;> simp [State.upd, List.getD_eq_getElem?_getD,
              hyl, hm.1, hm.2]
          · have hne : x * k.stride κ.lcap + j' ≠ x * k.stride κ.lcap + y := by omega
            cases b <;> simp [State.upd,  List.getD_eq_getElem?_getD,
              Ne.symm ej, ej] <;>
              simpa [List.getD_eq_getElem?_getD] using hm
      · trivial
    · trivial
  · trivial

/-- A write past the end of a list keeps the encoding. -/
theorem Enc.writeBeyond {s : Core} {m : State} (h : Enc p κ s m) {k : LK} {b : Bool} {x n v : Nat}
    (hx : x < κ.lrec k) (hn : (k.view s x).length ≤ n) (hnc : n < κ.lcap k) :
    Enc p κ s (m.write (arrL p k b) (x * k.stride κ.lcap + n) v) := by
  refine h.frame (by simplifyMemory) (fun _ _ => rfl) (fun _ => rfl) rfl
    (fun f => by funext q; simplifyMemory)
    (fun t => by funext q; simplifyMemory) (by funext q; simplifyMemory)
    (fun k' i hi => by simplifyMemory; exact h.llen k' i hi)
    (fun k' i hi j hj => ?_) (fun c hc j hj => by simplifyMemory; exact h.wmem c hc j hj)
    (fun o => by simplifyMemory; exact h.omem o) h.prepC
  have hm := h.lmem k' i hi j hj
  by_cases ek : k' = k
  · subst ek
    have hjc : j < κ.lcap k' := Nat.lt_of_lt_of_le hj (h.llen k' i hi).2
    have hne : i * k'.stride κ.lcap + j ≠ x * k'.stride κ.lcap + n := by
      intro e
      by_cases ei : i = x
      · subst ei; omega
      · exact ei (h.stride_inj hi hx hjc hnc e).1
    simp only [st_write_mem, arr_eq_iff, Slot.lst.injEq, true_and]
    constructor
    · by_cases eb : false = b
      · subst eb; simp only [ite_true, State.upd, ite_eq_right hne]; exact hm.1
      · rw [ite_eq_right eb]; exact hm.1
    · by_cases eb : true = b
      · subst eb; simp only [ite_true, State.upd, ite_eq_right hne]; exact hm.2
      · rw [ite_eq_right eb]; exact hm.2
  · simp only [st_write_mem, arr_eq_iff, Slot.lst.injEq, ek, false_and, ite_false]; exact hm

theorem exec_store_ok {m : State} {a : Arr} {i e : Expr} {j v : Nat} (hi : i.eval m = some j)
    (he : e.eval m = some v) (hj : j < m.cap a) :
    exec (.store a i e) m =
      ⟨((m.bump (i.maxv m)).bump (e.maxv m)).write a j v, 1 + i.cost + e.cost, .ok⟩ := by
  simp [exec, hi, he, hj]

theorem out_bind_ok (st : State) (c : Nat) (g : State → Out) :
    (Out.mk st c .ok).bind g = ⟨(g st).st, c + (g st).cost, (g st).status⟩ := rfl

theorem sim_lgrow {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L) (k : LK)
    (i a b : Exp) : Agree p κ (evalF κ (.lgrow k i a b) s L)
      (exec (Stm.compile p κ (.lgrow k i a b)) m) := by
  simp only [evalF]
  split
  · next x va vb hx ha hb =>
    split
    · next s' hs =>
      obtain ⟨hxr, hlc⟩ := LK.set_lrec hs
      rw [List.length_append, List.length_singleton] at hlc
      have hlen := (h.llen k x hxr).1
      generalize hn : (k.view s x).length = n at hlc hlen
      have hlt : x * k.stride κ.lcap + n < κ.lrec k * κ.lcap k := h.stride_lt hxr (by omega)
      -- the first store
      have h1 := (h.bump (Expr.maxv m (Expr.bin .add (.bin .mul (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ)))))
        |>.bump (a.compile p κ |>.maxv m)
        |>.writeBeyond (b := false) (v := va) hxr (le_of_eq hn) (by omega)
      have hix : (Expr.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap)))
          (.load (arrLen p k) (i.compile p κ))).eval m = some (x * k.stride κ.lcap + n) := by
        simp only [Expr.eval, Exp.ev_compile h hL i hx, BinOp.eval, Option.bind_some, h.lcapN,
            hxr, ↓reduceIte, hlen]
      simp only [Stm.compile]
      rw [Machine.exec, exec_store_ok hix (Exp.ev_compile h hL a ha) (by rw [h.lcapA]; exact hlt),
        out_bind_ok]
      generalize hm1 : (((m.bump (Expr.maxv m (Expr.bin .add (.bin .mul (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ)))))
        |>.bump (a.compile p κ |>.maxv m)).write
          (arrL p k false) (x * k.stride κ.lcap + n) va) = m1 at h1
      have hL1 : m1.loc = L := by rw [← hm1]; simp [hL]
      have hix1 : (Expr.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap)))
          (.load (arrLen p k) (i.compile p κ))).eval m1 = some (x * k.stride κ.lcap + n) := by
        simp [Exp.ev_compile h1 hL1 i hx, h1.lcapN, hxr, (h1.llen k x hxr).1, hn]
      have h2 := (h1.bump (Expr.maxv m1 (Expr.bin .add (.bin .mul (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ)))))
        |>.bump (b.compile p κ |>.maxv m1)
        |>.writeBeyond (b := true) (v := vb) hxr (le_of_eq hn) (by omega)
      rw [Machine.exec, exec_store_ok hix1 (Exp.ev_compile h1 hL1 b hb)
          (by rw [h1.lcapA]; exact hlt),
        out_bind_ok]
      generalize hm2 : (((m1.bump (Expr.maxv m1 (Expr.bin .add (.bin .mul (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ)))))
        |>.bump (b.compile p κ |>.maxv m1)).write
          (arrL p k true) (x * k.stride κ.lcap + n) vb) = m2 at h2
      have hL2 : m2.loc = L := by rw [← hm2]; simp [hL1]
      have hn2 : (Expr.bin .add (.load (arrLen p k) (i.compile p κ)) (.lit 1)).eval m2 =
          some (n + 1) := by
        simp [Exp.ev_compile h2 hL2 i hx, h2.lcapN, hxr, (h2.llen k x hxr).1, hn]
      rw [exec_store_ok (Exp.ev_compile h2 hL2 i hx) hn2 (by rw [h2.lcapN]; exact hxr)]
      refine ⟨rfl, ?_, by simp [hL2], ?_⟩
      · rw [← hm2, ← hm1]
        refine h.listUpd hs (by simplifyMemory)
          (fun sl h1 h2 => by funext q; simp only [st_write_mem, st_bump_mem, arr_eq_iff,
              h1 true, h1 false, h2,
            ite_false])
          (fun q hq => by simp only [st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq,
              ite_false, ite_true,
            State.upd, ite_eq_right hq])
          (by simp only [st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq, ite_false,
              ite_true, State.upd];
              simp [hn])
          (fun b' q j' hq hqx hj' => ?_) (fun j' hj' => ?_)
        · have hne : q * k.stride κ.lcap + j' ≠ x * k.stride κ.lcap + n := by
            intro e
            exact hqx (h.stride_inj hq hxr hj' (by omega) e).1
          simp only [st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq, ite_false,
              Slot.lst.injEq, true_and]
          cases b' <;> simp [State.upd, hne]
        · rw [List.length_append, List.length_singleton] at hj'
          simp only [st_write_mem, st_bump_mem, arr_eq_iff, reduceCtorEq, ite_false,
              Slot.lst.injEq, true_and]
          by_cases ej : j' = (k.view s x).length
          · rw [ej, ← hn]; simp [State.upd, List.getD_eq_getElem?_getD]
          · have hj2 : j' < (k.view s x).length := by omega
            have hjn : j' ≠ n := by omega
            have hm := h.lmem k x hxr j' hj2
            simp [State.upd, hjn, List.getD_eq_getElem?_getD, List.getElem?_append_left hj2]
            simpa [List.getD_eq_getElem?_getD] using hm
      · simp [Exp.cost_compile, Expr.cost]; omega
    · trivial
  · trivial

theorem sim_lshrink {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (k : LK) (i : Exp) :
    Agree p κ (evalF κ (.lshrink k i) s L) (exec (Stm.compile p κ (.lshrink k i)) m) := by
  simp only [evalF]
  split
  · next x hx =>
    split
    · next hne =>
      split
      · next s' hs =>
        obtain ⟨hxr, -⟩ := LK.set_lrec hs
        have hlen := (h.llen k x hxr).1
        have hv : (Expr.bin .sub (.load (arrLen p k) (i.compile p κ)) (.lit 1)).eval m =
            some ((k.view s x).length - 1) := by
          simp only [Expr.eval, Exp.ev_compile h hL i hx, h.lcapN, Option.bind_some, hxr,
              ↓reduceIte, hlen, BinOp.eval, ite_eq_left_iff, not_le, Nat.lt_one_iff,
              List.length_eq_zero_iff, reduceCtorEq, imp_false]
          intro e; rw [e] at hne; simp only [List.length_nil, ne_eq, not_true_eq_false] at hne
        simp only [Stm.compile]
        rw [exec_store_ok (Exp.ev_compile h hL i hx) hv (by rw [h.lcapN]; exact hxr)]
        refine ⟨rfl, ?_, by simp [hL], by simp [Exp.cost_compile, Expr.cost]; omega⟩
        refine h.listUpd hs (by simplifyMemory)
          (fun sl h1 h2 => by funext q; simp only [st_write_mem, st_bump_mem, arr_eq_iff, h2,
              ite_false])
          (fun q hq => by simp only [st_write_mem, st_bump_mem, ite_true, State.upd,
              ite_eq_right hq])
          (by simp only [st_write_mem, st_bump_mem, ite_true, State.upd]; simp)
          (fun b' q j' _ _ _ => by simplifyMemory) (fun j' hj' => ?_)
        rw [List.length_dropLast] at hj'
        have hm := h.lmem k x hxr j' (by omega)
        simplifyMemory
        simpa [List.getD_eq_getElem?_getD, List.getElem?_dropLast,
          show j' < (k.view s x).length - 1 from hj',
          List.getElem?_eq_getElem (show j' < (k.view s x).length by omega)] using hm
      · trivial
    · trivial
  · trivial

theorem sim_lclear {s : Core} {L : Loc} {m : State} (h : Enc p κ s m) (hL : m.loc = L)
    (k : LK) (i : Exp) :
    Agree p κ (evalF κ (.lclear k i) s L) (exec (Stm.compile p κ (.lclear k i)) m) := by
  simp only [evalF]
  split
  · next x hx =>
    split
    · next s' hs =>
      obtain ⟨hxr, -⟩ := LK.set_lrec hs
      simp only [Stm.compile]
      rw [exec_store_ok (Exp.ev_compile h hL i hx) (by rfl) (by rw [h.lcapN]; exact hxr)]
      refine ⟨rfl, ?_, by simp [hL], by simp [Exp.cost_compile, Expr.cost]; omega⟩
      refine h.listUpd hs (by simplifyMemory)
        (fun sl h1 h2 => by funext q; simp only [st_write_mem, st_bump_mem, arr_eq_iff, h2,
            ite_false])
        (fun q hq => by simp only [st_write_mem, st_bump_mem, ite_true, State.upd, ite_eq_right hq])
        (by simp only [st_write_mem, st_bump_mem, ite_true, State.upd]; simp)
        (fun b' q j' _ _ _ => by simplifyMemory) (fun j' hj' => by simp only [List.length_nil,
            not_lt_zero] at hj')
    · trivial
  · trivial

theorem Fld.set_lt {s s' : Core} {f : Fld} {j v : Nat} (h : f.set κ s j v = some s')
    (hle : ∀ t, t.size s ≤ κ.tbl t) : j < f.cap κ := by
  cases f with
  | e k =>
    simp only [Fld.set] at h
    split at h <;> [skip; simp only [reduceCtorEq] at h]
    next hc =>
      have := hle .E; simp [Fld.cap, Tbl.size] at *; omega
  | g k =>
    simp only [Fld.set] at h
    split at h <;> [skip; simp only [reduceCtorEq] at h]
    next hc =>
      have := hle .G; simp [Fld.cap, Tbl.size] at *; omega
  | c k =>
    simp only [Fld.set] at h
    split at h <;> [skip; simp only [reduceCtorEq] at h]
    next hc =>
      have := hle .C; simp [Fld.cap, Tbl.size] at *; omega
  | n k =>
    simp only [Fld.set] at h
    split at h <;> [skip; simp only [reduceCtorEq] at h]
    next hc =>
      have := hle .N; simp [Fld.cap, Tbl.size] at *; omega
  | a k =>
    simp only [Fld.set] at h
    split at h <;> [skip; simp only [reduceCtorEq] at h]
    next hc =>
      simp only [cap]; exact hc
  | s k =>
    simp only [Fld.set] at h
    split at h <;> [skip; simp only [reduceCtorEq] at h]
    next hc =>
      simp only [cap, Nat.lt_one_iff]; have := hc.1; omega

theorem sim_runFor {b : Stm} {x : Reg}
    (ih : ∀ s L m, Enc p κ s m → m.loc = L → Agree p κ (evalF κ b s L) (exec (b.compile p κ) m)) :
    ∀ n k s L m, Enc p κ s m → m.loc = L →
      Agree p κ (runForF (evalF κ b) x k n s L) (Machine.runFor (exec (b.compile p κ)) x k n m)
  | 0, _, s, L, m, h, hL => ⟨rfl, h, hL, rfl⟩
  | n + 1, k, s, L, m, h, hL => by
    simp only [runForF, Machine.runFor]
    refine Agree.bind ?_ (fun s' L' m' h' hL' => sim_runFor ih n (k + 1) s' L' m' h' hL')
    have := (ih s (State.upd L x k) (m.setLoc x k) (h.setLoc x k) (by simp [hL])).addCost 1
    exact this

/-- **The compiled code simulates the source**, step for step. -/
theorem sim (c : Stm) : ∀ {s : Core} {L : Loc} {m : State}, Enc p κ s m → m.loc = L →
    Agree p κ (evalF κ c s L) (exec (c.compile p κ) m) := by
  induction c with
  | skip => intro s L m h hL; exact ⟨rfl, h, hL, rfl⟩
  | assign x e =>
    intro s L m h hL
    simp only [evalF]
    cases he : e.ev κ s L with
    | none => trivial
    | some v =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL e he]
      exact ⟨rfl, (h.bump _).setLoc x v, by simp [hL], by simp [Exp.cost_compile]⟩
  | wr f i e =>
    intro s L m h hL
    simp only [evalF]
    cases hi : i.ev κ s L with
    | none => trivial
    | some j =>
      cases he : e.ev κ s L with
      | none => trivial
      | some v =>
        simp only
        cases hs : f.set κ s j v with
        | none => trivial
        | some s' =>
          have hj := Fld.set_lt hs h.sle
          simp only [Stm.compile, exec, Exp.ev_compile h hL i hi, Exp.ev_compile h hL e he]
          rw [ite_eq_left (by simp only [h.cap f]; exact hj)]
          exact ⟨rfl, ((h.bump _).bump _).write hs, by simp [hL], by simp [Exp.cost_compile]⟩
  | push t x =>
    intro s L m h hL
    simp only [evalF]
    split
    · next ht =>
      have h1 : Enc p κ s ((m.bump (t.size s)).setLoc x (t.size s)) := (h.bump _).setLoc _ _
      have h2 := ((h1.bump (t.size s)).bump (t.size s + 1)).push ht
      simp only [Stm.compile, exec, Out.bind, Expr.eval, State.setLoc, State.bump,
        State.upd, h.scap t, h.smem t, Nat.zero_lt_one, Option.bind_some, BinOp.eval, ite_eq_left]
      refine ⟨rfl, h2.congr rfl rfl, by simp [hL], rfl⟩
    · trivial
  | seq c d ihc ihd =>
    intro s L m h hL
    simp only [evalF, Stm.compile, exec]
    exact Agree.bind (ihc h hL) (fun s' L' m' h' hL' => ihd h' hL')
  | ite c t f iht ihf =>
    intro s L m h hL
    simp only [evalF]
    cases hc : c.ev κ s L with
    | none => trivial
    | some v =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL c hc, Out.bind]
      rw [← Exp.cost_compile p κ c]
      by_cases hv : v ≠ 0
      · simp only [ite_eq_left hv]; exact (iht (h.bump _) (by simp [hL])).addCost _
      · simp only [ite_eq_right hv]; exact (ihf (h.bump _) (by simp [hL])).addCost _
  | loop x n b ihb =>
    intro s L m h hL
    simp only [evalF]
    cases hn : n.ev κ s L with
    | none => trivial
    | some k =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL n hn, Out.bind]
      rw [← Exp.cost_compile p κ n]
      exact (sim_runFor (fun s L m h hL => ihb h hL) k 0 s L _ (h.bump _) (by simp [hL])).addCost _
  | call nm ps b rs args ds ihb =>
    intro s L m h hL
    simp only [evalF]
    cases ha : evList κ s L args with
    | none => trivial
    | some vs =>
      simp only [Stm.compile, exec, evList_compile h hL args ha]
      have hb := ihb (s := s) (L := State.setLocs (fun _ => 0) ps vs)
        (m := (m.bump (maxvList m (args.map (Exp.compile p κ)))).enter ps vs)
        ((h.bump (maxvList m (args.map (Exp.compile p κ)))).congr rfl rfl) (by simp)
      revert hb
      generalize evalF κ b s (State.setLocs (fun _ => 0) ps vs) = r
      generalize exec (b.compile p κ) _ = o
      intro hb
      cases r with
      | ok s' L' n =>
        obtain ⟨h1, h2, h3, h4⟩ := hb
        simp only [h1]
        exact ⟨rfl, h2.congr rfl rfl, by simp [hL, h3], by simp only [costList_compile, h4]⟩
      | fail s' L' n =>
        obtain ⟨h1, h2, h3, h4⟩ := hb
        simp only [h1]
        exact ⟨rfl, h2.withLoc _, by simp [hL], by simp only [costList_compile, h4]⟩
      | bug => trivial
  | fail => intro s L m h hL; exact ⟨rfl, h, hL, rfl⟩
  | bug => intro s L m h hL; trivial
  | «catch» c hd ihc ihh =>
    intro s L m h hL
    simp only [evalF, Stm.compile, exec]
    have hc := ihc h hL
    revert hc
    generalize evalF κ c s L = r
    generalize exec (c.compile p κ) m = o
    intro hc
    cases r with
    | ok s' L' n =>
      obtain ⟨h1, h2, h3, h4⟩ := hc
      simp only [h1]; exact ⟨rfl, h2, h3, by simp [h4]⟩
    | fail s' L' n =>
      obtain ⟨h1, h2, h3, h4⟩ := hc
      simp only [h1]
      have := (ihh h2 h3).addCost (1 + n)
      rw [h4]; exact this
    | bug => trivial
  | lwr k b i j e => intro s L m h hL; exact sim_lwr h hL k b i j e
  | lgrow k i a b => intro s L m h hL; exact sim_lgrow h hL k i a b
  | lshrink k i => intro s L m h hL; exact sim_lshrink h hL k i
  | lclear k i => intro s L m h hL; exact sim_lclear h hL k i
  | pwr c j e => intro s L m h hL; exact sim_pwr h hL c j e
  | rowReset c => intro s L m h hL; exact sim_rowReset h hL c
  | prepInit c b => intro s L m h hL; exact sim_prepInit h hL c b
  | prepSet hh b t => intro s L m h hL; exact sim_prepSet h hL hh b t
  | prepPath j e => intro s L m h hL; exact sim_prepPath h hL j e
  | prepCommit => intro s L m h hL; exact sim_prepCommit h hL
  | jobSet x y z t a b c d => intro s L m h hL; exact sim_jobSet h hL x y z t a b c d
  | jobClear => intro s L m h hL; exact sim_jobClear h hL
  | pcSet t a b c d => intro s L m h hL; exact sim_pcSet h hL t a b c d

end OrderMaintenance.Impl
