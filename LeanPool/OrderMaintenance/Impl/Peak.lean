/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Sim

public import LeanPool.OrderMaintenance.Impl.Notation


/-!
# Theorem W, option (A), stage A1: the peak of the core language

The machine records the largest value it computes (`State.peak`, raised by `bump` with
`Expr.maxv` at every evaluated expression). `sim` (`Sim.lean`) says nothing about it. This file
computes the same quantity on Level F, without running the machine (`docs/WORD.md` §4, approach
(i′)):

* `Exp.pk κ s L e` is `Expr.maxv` of the compiled expression: the largest value among `e`, its
  subexpressions, and the index arithmetic the compiler adds (`i·stride + j` for a list entry,
  `c·(H+1) + j` for a path entry, the parameter index of `prm`). `Exp.maxv_compile` proves the
  two equal whenever `e` evaluates.
* `pkF κ c s L` is the largest `pk` of every expression the run of `evalF κ c s L` evaluates (loop
  bounds, call arguments and the expressions inside the compiled forms of `push`, `lgrow`,
  `prepInit`, …). `PeakSim.lean` proves that when `evalF` returns `ok` or `fail`, the compiled
  run ends with `peak = Max.max m.peak (pkF κ c s L)`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr BinOp UnOp State Out exec)

/-! ### Expressions -/

/-- The value of an expression, 0 if it does not evaluate. -/
def Exp.val (κ : Caps) (s : Core) (L : Loc) (e : Exp) : Nat := (e.ev κ s L).getD 0

/-- The peak of the compiled row width `H + 1` (it reads parameter 15 and adds 1). -/
def rowPk (s : Core) : Nat := Max.max (Max.max (Max.max PF.H.idx s.P.H) 1) (s.P.H + 1)

/-- **The peak of an expression**: `Expr.maxv` of its compiled form (`Exp.maxv_compile`). -/
def Exp.pk (κ : Caps) (s : Core) (L : Loc) : Exp → Nat
  | .lit n => n
  | .var x => L x
  | .rd f i => Max.max (i.pk κ s L) (Exp.val κ s L (.rd f i))
  | .size t => t.size s
  | .prm k => Max.max k.idx (k.get s.P)
  | .bin op a b => Max.max (Max.max (a.pk κ s L) (b.pk κ s L)) (Exp.val κ s L (.bin op a b))
  | .un op a => Max.max (a.pk κ s L) (Exp.val κ s L (.un op a))
  | .lrd k b i j =>
    Max.max (Max.max (Max.max (Max.max (Max.max (i.pk κ s L) (k.stride κ.lcap))
      (i.val κ s L * k.stride κ.lcap))
      (j.pk κ s L))
      (i.val κ s L * k.stride κ.lcap + j.val κ s L)) (Exp.val κ s L (.lrd k b i j))
  | .llen k i => Max.max (i.pk κ s L) (Exp.val κ s L (.llen k i))
  | .prd c j =>
    Max.max (Max.max (Max.max (Max.max (Max.max (c.pk κ s L) (rowPk s)) (c.val κ s L * κ.pw))
      (j.pk κ s L))
      (c.val κ s L * κ.pw + j.val κ s L)) (Exp.val κ s L (.prd c j))
  | .opt o => o.get s

/-- The peak of an argument list (`maxvList` of the compiled list). -/
def pkList (κ : Caps) (s : Core) (L : Loc) (es : List Exp) : Nat :=
  (es.map (Exp.pk κ s L)).foldr Max.max 0

theorem Exp.val_of {κ : Caps} {s : Core} {L : Loc} {e : Exp} {v : Nat} (h : e.ev κ s L = some v) :
    e.val κ s L = v := by simp [Exp.val, h]

/-- The peak bounds the value. -/
theorem Exp.val_le_pk (κ : Caps) (s : Core) (L : Loc) : ∀ e : Exp, e.val κ s L ≤ e.pk κ s L
  | .lit n => by simp [Exp.val, Exp.ev, Exp.pk]
  | .var x => by simp [Exp.val, Exp.ev, Exp.pk]
  | .rd f i => le_max_right _ _
  | .size t => by simp [Exp.val, Exp.ev, Exp.pk]
  | .prm k => by simp [Exp.val, Exp.ev, Exp.pk]
  | .bin op a b => le_max_right _ _
  | .un op a => le_max_right _ _
  | .lrd k b i j => le_max_right _ _
  | .llen k i => le_max_right _ _
  | .prd c j => le_max_right _ _
  | .opt o => by simp [Exp.val, Exp.ev, Exp.pk]

theorem Exp.le_pk {κ : Caps} {s : Core} {L : Loc} {e : Exp} {v : Nat} (h : e.ev κ s L = some v) :
    v ≤ e.pk κ s L := by
  have := e.val_le_pk κ s L; rwa [Exp.val_of h] at this

variable {p : Nat} {κ : Caps}

theorem Enc.rowW_maxv {s : Core} {m : State} (h : Enc p κ s m) : (rowW p).maxv m = rowPk s := by
  have := h.pmem .H
  simp only [PF.get, PF.idx] at this
  simp [rowW, Machine.Expr.maxv, Machine.Expr.eval, h.pcap,
    PF.idx, this, Machine.BinOp.eval, rowPk]

/-- **`pk` is the machine's `maxv`** of the compiled expression, whenever the expression
evaluates. -/
theorem Exp.maxv_compile {s : Core} {m : State} {L : Loc} (h : Enc p κ s m) (hL : m.loc = L) :
    ∀ (e : Exp) {v : Nat}, e.ev κ s L = some v → (e.compile p κ).maxv m = e.pk κ s L
  | .lit n, v, _ => by simp [Exp.compile, Exp.pk, Machine.Expr.maxv]
  | .var x, v, _ => by simp [Exp.compile, Exp.pk, Machine.Expr.maxv, hL]
  | .rd f i, v, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨j, hj, -⟩ := hv
    simp only [Exp.compile, Machine.Expr.maxv, Exp.pk, Exp.maxv_compile h hL i hj]
    rw [show (Machine.Expr.load (arrF p f) (i.compile p κ)) = (Exp.rd f i).compile p κ from rfl,
      Exp.ev_compile h hL _ hv', Exp.val_of hv']; rfl
  | .size t, v, hv => by
    simp only [ev, Option.some.injEq] at hv; subst hv
    simp [Exp.compile, Exp.pk, Machine.Expr.maxv,
      Machine.Expr.eval, h.scap t, h.smem t]
  | .prm k, v, hv => by
    simp only [ev, Option.some.injEq] at hv; subst hv
    simp [Exp.compile, Exp.pk, Machine.Expr.maxv,
      Machine.Expr.eval, h.pcap, h.pmem k, k.idx_lt]
  | .bin op a b, v, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, -⟩ := hv
    simp only [Exp.compile, Machine.Expr.maxv, Exp.pk,
      Exp.maxv_compile h hL a hx, Exp.maxv_compile h hL b hy]
    rw [show (Machine.Expr.bin op (a.compile p κ) (b.compile p κ)) =
        (Exp.bin op a b).compile p κ from rfl,
      Exp.ev_compile h hL _ hv', Exp.val_of hv']; rfl
  | .un op a, v, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, -⟩ := hv
    simp only [Exp.compile, Machine.Expr.maxv, Exp.pk, Exp.maxv_compile h hL a hx]
    rw [show (Machine.Expr.un op (a.compile p κ)) = (Exp.un op a).compile p κ from rfl,
      Exp.ev_compile h hL _ hv', Exp.val_of hv']; rfl
  | .lrd k b i j, v, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, -⟩ := hv
    have hc := Exp.ev_compile h hL _ hv'
    simp only [Exp.compile] at hc ⊢
    simp only [Machine.Expr.eval, Exp.ev_compile h hL i hx,
      Exp.ev_compile h hL j hy, Option.bind_some,
      Machine.BinOp.eval] at hc
    simp only [Machine.Expr.maxv, Exp.pk, Exp.maxv_compile h hL i hx,
      Exp.maxv_compile h hL j hy,
      Exp.val_of hv', Exp.val_of hx, Exp.val_of hy, Machine.Expr.eval, Exp.ev_compile h hL i hx,
      Exp.ev_compile h hL j hy, Option.bind_some, Machine.BinOp.eval, Option.getD_some, hc]
  | .llen k i, v, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, -⟩ := hv
    have hc := Exp.ev_compile h hL _ hv'
    simp only [Exp.compile] at hc ⊢
    simp only [Machine.Expr.maxv, Exp.pk, Exp.maxv_compile h hL i hx, hc,
      Exp.val_of hv', Option.getD_some]
  | .prd c j, v, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, -⟩ := hv
    have hc := Exp.ev_compile h hL _ hv'
    simp only [Exp.compile] at hc ⊢
    simp only [Machine.Expr.eval, Exp.ev_compile h hL c hx,
      Exp.ev_compile h hL j hy, h.rowW_eval,
      Option.bind_some, Machine.BinOp.eval] at hc
    simp only [Machine.Expr.maxv, Exp.pk, Exp.maxv_compile h hL c hx,
      Exp.maxv_compile h hL j hy,
      Exp.val_of hv', Exp.val_of hx, Exp.val_of hy, Machine.Expr.eval, Exp.ev_compile h hL c hx,
      Exp.ev_compile h hL j hy, h.rowW_eval, h.rowW_maxv, Option.bind_some, Machine.BinOp.eval,
      Option.getD_some, hc]
  | .opt o, v, hv => by
    simp only [ev, Option.some.injEq] at hv; subst hv
    simp [Exp.compile, Exp.pk, Machine.Expr.maxv,
      Machine.Expr.eval, h.ocap o, h.omem o]

theorem maxvList_compile {s : Core} {m : State} {L : Loc} (h : Enc p κ s m) (hL : m.loc = L) :
    ∀ (es : List Exp) {vs : List Nat}, evList κ s L es = some vs →
      Machine.maxvList m (es.map (Exp.compile p κ)) = pkList κ s L es
  | [], _, _ => rfl
  | e :: es, vs, hv => by
    simp only [evList, List.mapM_cons] at hv
    cases he : e.ev κ s L with
    | none => simp [he] at hv
    | some v =>
      cases hes : es.mapM (·.ev κ s L) with
      | none => simp [he, hes] at hv
      | some ws =>
        have := maxvList_compile h hL es (vs := ws) hes
        simp only [Machine.maxvList, pkList, List.map_cons,
          List.foldr_cons] at this ⊢
        rw [Exp.maxv_compile h hL e he, this]

/-! ### Statements -/

/-- The peak of the compiled index `i·stride + j` of list `k` (as in `.lrd` and `.lwr`). -/
def lidxPk (κ : Caps) (s : Core) (L : Loc) (k : LK) (i j : Exp) : Nat :=
  Max.max (Max.max (Max.max (Max.max (i.pk κ s L) (k.stride κ.lcap))
      (i.val κ s L * k.stride κ.lcap))
      (j.pk κ s L))
    (i.val κ s L * k.stride κ.lcap + j.val κ s L)

/-- The peak of the compiled path index `x·(H+1) + j`, where `px` is the peak and `x` the value of
the row expression (as in `.prd`, `.pwr` and `.prepPath`). -/
def pidxPk (κ : Caps) (s : Core) (L : Loc) (px x : Nat) (j : Exp) : Nat :=
  Max.max (Max.max (Max.max (Max.max px (rowPk s)) (x * κ.pw)) (j.pk κ s L))
    (x * κ.pw + j.val κ s L)

/-- The peak of iterations `k, …, k+n-1` of a loop whose body runs as `f` with peak `g`
(mirrors `runForF`). -/
def pkFor (f : Core → Loc → Res) (g : Core → Loc → Nat) (x : Reg) : Nat → Nat → Core → Loc → Nat
  | _, 0, _, _ => 0
  | k, n + 1, s, L =>
    Max.max (g s (Machine.State.upd L x k))
      (match f s (Machine.State.upd L x k) with
        | .ok s' L' _ => pkFor f g x (k + 1) n s' L'
        | _ => 0)

/-- **The peak of a run of the core language**: the largest `pk` of every expression that the
compiled code evaluates, following `evalF`'s run (`sim_peak`, `PeakSim.lean`). -/
def pkF (κ : Caps) : Stm → Core → Loc → Nat
  | .skip, _, _ => 0
  | .assign _ e, s, L => e.pk κ s L
  | .wr _ i e, s, L => Max.max (i.pk κ s L) (e.pk κ s L)
  | .push t _, s, _ => t.size s + 1
  | .seq c d, s, L =>
    match evalF κ c s L with
    | .ok s' L' _ => Max.max (pkF κ c s L) (pkF κ d s' L')
    | _ => pkF κ c s L
  | .ite c t f, s, L => Max.max (c.pk κ s L) (if c.val κ s L ≠ 0 then pkF κ t s L else pkF κ f s L)
  | .loop x n b, s, L => Max.max (n.pk κ s L) (pkFor (evalF κ b) (pkF κ b) x 0 (n.val κ s L) s L)
  | .call _ ps b _ args _, s, L =>
    Max.max (pkList κ s L args)
      (pkF κ b s (Machine.State.setLocs (fun _ => 0) ps ((evList κ s L args).getD [])))
  | .fail, _, _ => 0
  | .bug, _, _ => 0
  | .catch c h, s, L =>
    match evalF κ c s L with
    | .fail s' L' _ => Max.max (pkF κ c s L) (pkF κ h s' L')
    | _ => pkF κ c s L
  | .lwr k _ i j e, s, L => Max.max (lidxPk κ s L k i j) (e.pk κ s L)
  | .lgrow k i a b, s, L =>
    Max.max (Max.max (Max.max (Max.max (Max.max (Max.max (i.pk κ s L) (k.stride κ.lcap))
      (i.val κ s L * k.stride κ.lcap)) ((k.view s (i.val κ s L)).length))
      (i.val κ s L * k.stride κ.lcap + (k.view s (i.val κ s L)).length))
      (Max.max (a.pk κ s L) (b.pk κ s L)))
      ((k.view s (i.val κ s L)).length + 1)
  | .lshrink k i, s, L => Max.max (Max.max (i.pk κ s L) ((k.view s (i.val κ s L)).length)) 1
  | .lclear _ i, s, L => i.pk κ s L
  | .pwr c j e, s, L => Max.max (pidxPk κ s L (c.pk κ s L) (c.val κ s L) j) (e.pk κ s L)
  | .rowReset _, _, _ => 0
  | .prepInit c b, s, L => Max.max (pkList κ s L [c, b]) 1
  | .prepSet h b t, s, L => pkList κ s L [h, b, t]
  | .prepPath j e, s, L =>
    Max.max (pidxPk κ s L (OF.prepChunk.get s) (OF.prepChunk.get s) j) (e.pk κ s L)
  | .prepCommit, _, _ => 0
  | .jobSet x y z t a b c d, s, L => Max.max (pkList κ s L [x, y, z, t, a, b, c, d]) 1
  | .jobClear, _, _ => 0
  | .pcSet t a b c d, s, L => pkList κ s L [t, a, b, c, d]

/-! ### Rules for bounding `pkF` (stage A2 follows the agreement proofs with these) -/

section rules
variable {κ : Caps} {s s1 : Core} {L L1 : Loc}

theorem pkF_seq_ok {A B : Stm} {c1 : Nat} (h : evalF κ A s L = .ok s1 L1 c1) :
    pkF κ (A;; B) s L = Max.max (pkF κ A s L) (pkF κ B s1 L1) := by
  simp [pkF, h]

theorem pkF_seq_le {A B : Stm} {c1 W : Nat} (h : evalF κ A s L = .ok s1 L1 c1)
    (hA : pkF κ A s L ≤ W)
    (hB : pkF κ B s1 L1 ≤ W) : pkF κ (A;; B) s L ≤ W := by
  rw [pkF_seq_ok h]; exact max_le hA hB

theorem pkF_seq_fail {A B : Stm} {c1 : Nat} (h : evalF κ A s L = .fail s1 L1 c1) :
    pkF κ (A;; B) s L = pkF κ A s L := by
  simp [pkF, h]

theorem pkF_assign {x : Reg} {e : Exp} : pkF κ (.assign x e) s L = e.pk κ s L := rfl

theorem pkF_ite {c : Exp} {t f : Stm} {v : Nat} (hc : c.ev κ s L = some v) :
    pkF κ (.ite c t f) s L = Max.max (c.pk κ s L) (if v ≠ 0 then pkF κ t s L else pkF κ f s L) := by
  simp only [pkF, Exp.val_of hc]

theorem pkF_call {q : Proc} {args : List Exp} {ds : List Reg} {vs : List Nat}
    (ha : evList κ s L args = some vs) :
    pkF κ (q.call args ds) s L =
      Max.max (pkList κ s L args)
        (pkF κ q.body s (Machine.State.setLocs (fun _ => 0) q.params vs)) := by
  simp [Proc.call, pkF, ha]

theorem pkF_catch_ok {c h : Stm} {c1 : Nat} (hc : evalF κ c s L = .ok s1 L1 c1) :
    pkF κ (.catch c h) s L = pkF κ c s L := by
  simp [pkF, hc]

theorem pkF_catch_fail {c h : Stm} {c1 : Nat} (hc : evalF κ c s L = .fail s1 L1 c1) :
    pkF κ (.catch c h) s L = Max.max (pkF κ c s L) (pkF κ h s1 L1) := by
  simp [pkF, hc]

/-- **The loop rule**: an invariant `I k` before iteration `k` under which the body's peak is at
most `W` and which a normal end of the body passes on. -/
theorem pkFor_le {b : Stm} {x : Reg} {W : Nat} (I : Nat → Core → Loc → Prop)
    (hb : ∀ k s L, I k s L → pkF κ b s (Machine.State.upd L x k) ≤ W ∧
      ∀ s' L' c, evalF κ b s (Machine.State.upd L x k) = .ok s' L' c → I (k + 1) s' L') :
    ∀ n k s L, I k s L → pkFor (evalF κ b) (pkF κ b) x k n s L ≤ W
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, k, s, L, hI => by
    obtain ⟨h1, h2⟩ := hb k s L hI
    simp only [pkFor]
    refine max_le h1 ?_
    split
    · next s' L' c he => exact pkFor_le I hb n (k + 1) s' L' (h2 s' L' c he)
    · exact Nat.zero_le _

theorem pkF_loop_le {x : Reg} {n : Exp} {b : Stm} {N W : Nat} (hn : n.ev κ s L = some N)
    (hW : n.pk κ s L ≤ W)
    (I : Nat → Core → Loc → Prop) (h0 : I 0 s L)
    (hb : ∀ k s L, I k s L → pkF κ b s (Machine.State.upd L x k) ≤ W ∧
      ∀ s' L' c, evalF κ b s (Machine.State.upd L x k) = .ok s' L' c → I (k + 1) s' L') :
    pkF κ (.loop x n b) s L ≤ W := by
  simp only [pkF, Exp.val_of hn]
  exact max_le hW (pkFor_le I hb N 0 s L h0)

end rules

end OrderMaintenance.Impl
