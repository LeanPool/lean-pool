/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

public import LeanPool.OrderMaintenance.Impl.Peak


/-!
# Theorem W, option (A), stage A1: the generic bound on an expression's peak

The lemma of approach (i′) (`docs/WORD.md` §4): if every leaf of an expression is small, and
every shift amount is at most `S`, then its value and its peak (`Exp.pk`, the machine's `maxv` of
the compiled form) are below `2^w` for a width `w` computed from the syntax alone.

* `Exp.wv Γ K KH S e`: the width of `e`'s value. A local `x` has width `Γ x`; a field read has
  width `K` (`KH` for the handle `Elem.h`); a parameter, size, length, list or path entry or
  optional record has width `K`; a literal `n` has width `n`. Then `a + b` adds one bit, `a * b`
  adds the widths, `a <<< b` adds `S`, `−`, `/`, `%`, `>>>` and `msb` keep the width of `a`, and a
  comparison or connective has width 1.
* `Exp.wp Γ K KH S e`: the width of the peak, the maximum of `wv` over the subexpressions, and `K`
  for the compiled index arithmetic.
* `Exp.wd_sound`: under `MemW` (the leaves read from the core), `CapsW` (the capacities), the
  local widths `Γ` and `ShOK` (every shift amount at most `S`), an expression that evaluates to
  `v` has `v < 2^wv` and `pk < 2^wp`.
* `Exp.wp_le_depth`: when every local and handle has width at most `K` and every literal is at
  most `K`, `wp e ≤ 2^(depth e) · (K + S)`.

`wv` and `wp` are plain structural recursions: for a concrete expression, `simp [Exp.wv, Exp.wp]`
computes them as a term in `K`, `S` and the `Γ` of the locals involved, and `omega` compares it
with a target width. This is how stage A2 is meant to use it.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)

/-! ### Widths -/

/-- The width of a field: `KH` for the handle `Elem.h`, `K` for every other field. -/
def Fld.wd (K KH : Nat) : Fld → Nat
  | .e .h => KH
  | _ => K

/-- The width of a binary operation's result from the widths of its operands. -/
def _root_.OrderMaintenance.Machine.BinOp.wd (S : Nat) : BinOp → Nat → Nat → Nat
  | .add, a, b => Max.max a b + 1
  | .sub, a, _ => a
  | .mul, a, b => a + b
  | .div, a, _ => a
  | .mod, a, _ => a
  | .shl, a, _ => a + S
  | .shr, a, _ => a
  | .lt, _, _ | .le, _, _ | .eq, _, _ | .and, _, _ | .or, _, _ => 1

/-- Bound the intermediate values of a unary primitive from an input-value bound. -/
def _root_.OrderMaintenance.Machine.UnOp.wd : UnOp → Nat → Nat
  | .not, _ => 1
  | .msb, a => a

/-- **The width of an expression's value.** -/
def Exp.wv (Γ : Reg → Nat) (K KH S : Nat) : Exp → Nat
  | .lit n => n
  | .var x => Γ x
  | .rd f _ => f.wd K KH
  | .size _ => K
  | .prm _ => K
  | .bin op a b => op.wd S (a.wv Γ K KH S) (b.wv Γ K KH S)
  | .un op a => op.wd (a.wv Γ K KH S)
  | .lrd _ _ _ _ => K
  | .llen _ _ => K
  | .prd _ _ => K
  | .opt _ => K

/-- **The width of an expression's peak.** -/
def Exp.wp (Γ : Reg → Nat) (K KH S : Nat) : Exp → Nat
  | .lit n => n
  | .var x => Γ x
  | .rd f i => Max.max (i.wp Γ K KH S) (f.wd K KH)
  | .size _ => K
  | .prm _ => K
  | .bin op a b => Max.max (Max.max (a.wp Γ K KH S) (b.wp Γ K KH S)) (op.wd S (a.wv Γ K KH S)
    (b.wv Γ K KH S))
  | .un op a => Max.max (a.wp Γ K KH S) (op.wd (a.wv Γ K KH S))
  | .lrd _ _ i j => Max.max (Max.max (i.wp Γ K KH S) (j.wp Γ K KH S)) K
  | .llen _ i => Max.max (i.wp Γ K KH S) K
  | .prd c j => Max.max (Max.max (c.wp Γ K KH S) (j.wp Γ K KH S)) K
  | .opt _ => K

/-- Every shift amount of `e` (as evaluated) is at most `S`. -/
def Exp.ShOK (κ : Caps) (s : Core) (L : Loc) (S : Nat) : Exp → Prop
  | .lit _ | .var _ | .size _ | .prm _ | .opt _ => True
  | .rd _ i | .llen _ i => i.ShOK κ s L S
  | .bin op a b => a.ShOK κ s L S ∧ b.ShOK κ s L S ∧ (op = .shl → b.val κ s L ≤ S)
  | .un _ a => a.ShOK κ s L S
  | .lrd _ _ i j => i.ShOK κ s L S ∧ j.ShOK κ s L S
  | .prd c j => c.ShOK κ s L S ∧ j.ShOK κ s L S

/-- An expression without shifts satisfies `ShOK` for every `S`. -/
def Exp.noShl : Exp → Bool
  | .lit _ | .var _ | .size _ | .prm _ | .opt _ => true
  | .rd _ i | .llen _ i | .un _ i => i.noShl
  | .bin op a b => op != .shl && a.noShl && b.noShl
  | .lrd _ _ i j | .prd i j => i.noShl && j.noShl

theorem Exp.shOK_of_noShl (κ : Caps) (s : Core) (L : Loc) (S : Nat) :
    ∀ e : Exp, e.noShl = true → e.ShOK κ s L S
  | .lit _, _ | .var _, _ | .size _, _ | .prm _, _ | .opt _, _ => trivial
  | .rd _ i, h => by simp only [Exp.noShl] at h; exact Exp.shOK_of_noShl κ s L S i h
  | .llen _ i, h => by simp only [Exp.noShl] at h; exact Exp.shOK_of_noShl κ s L S i h
  | .un _ i, h => by simp only [Exp.noShl] at h; exact Exp.shOK_of_noShl κ s L S i h
  | .bin op a b, h => by
    simp only [Exp.noShl, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨Exp.shOK_of_noShl κ s L S a h.1.2, Exp.shOK_of_noShl κ s L S b h.2, fun e => absurd e
      h.1.1⟩
  | .lrd _ _ i j, h => by
    simp only [Exp.noShl, Bool.and_eq_true] at h
    exact ⟨Exp.shOK_of_noShl κ s L S i h.1, Exp.shOK_of_noShl κ s L S j h.2⟩
  | .prd i j, h => by
    simp only [Exp.noShl, Bool.and_eq_true] at h
    exact ⟨Exp.shOK_of_noShl κ s L S i h.1, Exp.shOK_of_noShl κ s L S j h.2⟩

/-! ### The leaves -/

/-- **The leaves read from the core are small**: every field below `2^K` (the handle below
`2^KH`), every size, parameter, list entry, path entry and optional field below `2^K`, the lists
within their capacity, and the row width `H + 1` below `2^K`. `PeakLeaf.lean` derives it from
option (B)'s `WB`. -/
structure MemW (K KH : Nat) (κ : Caps) (s : Core) : Prop where
  fld : ∀ (f : Fld) j, j < f.cap κ → f.get s j < 2 ^ f.wd K KH
  size : ∀ t : Tbl, t.size s < 2 ^ K
  prm : ∀ k : PF, k.get s.P < 2 ^ K
  H1 : s.P.H + 1 < 2 ^ K
  len : ∀ (k : LK) i, i < κ.lrec k → (k.view s i).length ≤ κ.lcap k
  lst : ∀ (k : LK) i j, i < κ.lrec k → j < (k.view s i).length →
    ((k.view s i).getD j (0, 0)).1 < 2 ^ K ∧ ((k.view s i).getD j (0, 0)).2 < 2 ^ K
  row : ∀ c j, c < κ.tbl .C → j < κ.pw → (rowOf s c).getX j < 2 ^ K
  opt : ∀ o : OF, o.get s < 2 ^ K

/-- **The capacities are small**: the compiled index arithmetic stays below `2^K`. -/
structure CapsW (K : Nat) (κ : Caps) : Prop where
  lst : ∀ k : LK, κ.lrec k * κ.lcap k < 2 ^ K
  lcap : ∀ k : LK, κ.lcap k < 2 ^ K
  path : κ.tbl .C * κ.pw < 2 ^ K
  sixteen : 16 ≤ 2 ^ K
  tbl : ∀ t : Tbl, κ.tbl t < 2 ^ K
  pw : κ.pw < 2 ^ K
  arr : ∀ k : AF, κ.arr k < 2 ^ K
  lcap2 : ∀ k : LK, κ.lcap k + 2 < 2 ^ K

/-! ### Soundness -/

theorem pow_max_left (a b : Nat) : 2 ^ a ≤ 2 ^ Max.max a b := Nat.pow_le_pow_right (by norm_num)
  (le_max_left a b)
theorem pow_max_right (a b : Nat) : 2 ^ b ≤ 2 ^ Max.max a b := Nat.pow_le_pow_right (by
  norm_num) (le_max_right a b)

theorem lt_pow_max_left {x a b : Nat} (h : x < 2 ^ a) : x < 2 ^ Max.max a b := lt_of_lt_of_le h
  (pow_max_left a b)
theorem lt_pow_max_right {x a b : Nat} (h : x < 2 ^ b) : x < 2 ^ Max.max a b := lt_of_lt_of_le h
  (pow_max_right a b)

theorem max_lt_pow {x y a b : Nat} (hx : x < 2 ^ a) (hy : y < 2 ^ b) : Max.max x y < 2 ^ Max.max
  a b :=
  max_lt (lt_pow_max_left hx) (lt_pow_max_right hy)

theorem _root_.OrderMaintenance.Machine.BinOp.wd_sound {S : Nat} {op : BinOp} {x y v wa wb :
  Nat} (hx : x < 2 ^ wa) (hy : y < 2 ^ wb)
    (hs : op = .shl → y ≤ S) (hv : op.eval x y = some v) : v < 2 ^ op.wd S wa wb := by
  cases op <;> simp only [Machine.BinOp.eval, Option.some.injEq] at hv <;> simp only
    [Machine.BinOp.wd]
  · subst hv
    have h1 := lt_pow_max_left (b := wb) hx
    have h2 := lt_pow_max_right (a := wa) hy
    rw [pow_succ]; omega
  · split at hv
    · cases hv; omega
    · simp only [reduceCtorEq] at hv
  · subst hv; rw [pow_add]; exact Nat.mul_lt_mul'' hx hy
  · subst hv; exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
  · subst hv; exact lt_of_le_of_lt (Nat.mod_le _ _) hx
  · subst hv
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (hs rfl)) (by
      positivity)
  · subst hv; exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
  all_goals (subst hv; split <;> norm_num)

theorem _root_.OrderMaintenance.Machine.UnOp.wd_sound {op : UnOp} {x w : Nat} (hx : x < 2 ^ w) :
  op.eval x < 2 ^ op.wd w := by
  cases op <;> simp only [Machine.UnOp.eval, Machine.UnOp.wd]
  · split <;> norm_num
  · exact lt_of_le_of_lt (Nat.log2_le_self x) hx

theorem lit_lt_pow (n : Nat) : n < 2 ^ n := Nat.lt_two_pow_self

variable {κ : Caps} {s : Core} {L : Loc} {Γ : Reg → Nat} {K KH S : Nat}

/-- **The generic expression lemma.** Under small leaves, small capacities and bounded shift
amounts, the value of an expression is below `2^wv` and its peak below `2^wp`. -/
theorem Exp.wd_sound (hM : MemW K KH κ s) (hC : CapsW K κ) (hΓ : ∀ x, L x < 2 ^ Γ x) :
    ∀ (e : Exp) {v : Nat}, e.ShOK κ s L S → e.ev κ s L = some v →
      v < 2 ^ e.wv Γ K KH S ∧ e.pk κ s L < 2 ^ e.wp Γ K KH S
  | .lit n, v, _, hv => by
    simp only [Exp.ev, Option.some.injEq] at hv; subst hv
    exact ⟨lit_lt_pow _, by simpa [Exp.pk, Exp.wp] using lit_lt_pow _⟩
  | .var x, v, _, hv => by
    simp only [Exp.ev, Option.some.injEq] at hv; subst hv
    exact ⟨hΓ x, by simpa [Exp.pk, Exp.wp] using hΓ x⟩
  | .rd f i, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨j, hj, hv⟩ := hv
    split at hv
    · next hjc =>
      cases hv
      have hf := hM.fld f j hjc
      obtain ⟨-, hip⟩ := Exp.wd_sound hM hC hΓ i hs hj
      refine ⟨hf, ?_⟩
      simp only [Exp.pk, Exp.wp, Exp.val_of hv']
      exact max_lt_pow hip hf
    · simp only [reduceCtorEq] at hv
  | .size t, v, _, hv => by
    simp only [ev, Option.some.injEq] at hv; subst hv
    exact ⟨hM.size t, by simpa [Exp.pk, Exp.wp] using hM.size t⟩
  | .prm k, v, _, hv => by
    simp only [ev, Option.some.injEq] at hv; subst hv
    refine ⟨hM.prm k, ?_⟩
    simp only [Exp.pk, Exp.wp]
    have := k.idx_lt
    have := hC.sixteen
    exact max_lt (by omega) (hM.prm k)
  | .bin op a b, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    obtain ⟨hsa, hsb, hsh⟩ := hs
    obtain ⟨hxa, hpa⟩ := Exp.wd_sound hM hC hΓ a hsa hx
    obtain ⟨hyb, hpb⟩ := Exp.wd_sound hM hC hΓ b hsb hy
    have hw := BinOp.wd_sound (S := S) hxa hyb (fun e => by have := hsh e; rwa [Exp.val_of hy]
      at this) hv
    refine ⟨hw, ?_⟩
    simp only [Exp.pk, Exp.wp, Exp.val_of hv']
    exact max_lt_pow (max_lt_pow hpa hpb) hw
  | .un op a, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, hv⟩ := hv
    obtain ⟨hxa, hpa⟩ := Exp.wd_sound hM hC hΓ a hs hx
    have hw : v < 2 ^ op.wd (a.wv Γ K KH S) := by rw [← hv]; exact UnOp.wd_sound hxa
    refine ⟨hw, ?_⟩
    simp only [Exp.pk, Exp.wp, Exp.val_of hv']
    exact max_lt_pow hpa hw
  | .lrd k b i j, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      obtain ⟨-, hip⟩ := Exp.wd_sound hM hC hΓ i hs.1 hx
      obtain ⟨-, hjp⟩ := Exp.wd_sound hM hC hΓ j hs.2 hy
      have hl := hM.len k x hc.1
      have he := hM.lst k x y hc.1 hc.2
      have hval : (if b then ((k.view s x).getD y (0, 0)).2 else ((k.view s x).getD y (0, 0)).1)
        < 2 ^ K := by
        cases b
        · simpa using he.1
        · simpa using he.2
      refine ⟨by simpa [Exp.wv] using hval, ?_⟩
      have hst : k.stride κ.lcap ≤ κ.lcap k := by cases k <;> simp only [LK.stride, Std.le_refl,
          zero_le]
      have hidx : x * k.stride κ.lcap + y < 2 ^ K := by
        have hy' : y < κ.lcap k := lt_of_lt_of_le hc.2 hl
        cases k with
        | freeG =>
          simp only [LK.stride, mul_zero, zero_add, gt_iff_lt]
          exact lt_of_lt_of_le hy' (le_of_lt (hC.lcap _))
        | _ => exact lt_trans (lt_mul_add hc.1 hy') (hC.lst _)
      have hK : ∀ z, z < 2 ^ K → z < 2 ^ Max.max (Max.max (i.wp Γ K KH S) (j.wp Γ K KH S)) K :=
        fun z hz => lt_pow_max_right hz
      have hK1 : ∀ z, z < 2 ^ i.wp Γ K KH S → z < 2 ^ Max.max (Max.max (i.wp Γ K KH S) (j.wp Γ K
        KH S)) K :=
        fun z hz => lt_pow_max_left (lt_pow_max_left hz)
      have hK2 : ∀ z, z < 2 ^ j.wp Γ K KH S → z < 2 ^ Max.max (Max.max (i.wp Γ K KH S) (j.wp Γ K
        KH S)) K :=
        fun z hz => lt_pow_max_left (lt_pow_max_right hz)
      simp only [Exp.pk, Exp.wp, Exp.val_of hv', Exp.val_of hx, Exp.val_of hy]
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
      obtain ⟨-, hip⟩ := Exp.wd_sound hM hC hΓ i hs hx
      have hl : (k.view s x).length < 2 ^ K := lt_of_le_of_lt (hM.len k x hc) (hC.lcap k)
      refine ⟨hl, ?_⟩
      simp only [Exp.pk, Exp.wp, Exp.val_of hv']
      exact max_lt_pow hip hl
    · simp only [reduceCtorEq] at hv
  | .prd c j, v, hs, hv => by
    have hv' := hv
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    split at hv
    · next hcj =>
      cases hv
      obtain ⟨-, hcp⟩ := Exp.wd_sound hM hC hΓ c hs.1 hx
      obtain ⟨-, hjp⟩ := Exp.wd_sound hM hC hΓ j hs.2 hy
      have hval := hM.row x y hcj.1 hcj.2
      refine ⟨hval, ?_⟩
      have hidx : x * κ.pw + y < 2 ^ K := lt_trans (lt_mul_add hcj.1 hcj.2) hC.path
      have hrow : rowPk s < 2 ^ K := by
        have h1 := hM.H1; have h16 := hC.sixteen
        simp only [rowPk, PF.idx]
        exact max_lt (max_lt (max_lt (by omega) (by omega)) (by omega)) h1
      have hK : ∀ z, z < 2 ^ K → z < 2 ^ Max.max (Max.max (c.wp Γ K KH S) (j.wp Γ K KH S)) K :=
        fun z hz => lt_pow_max_right hz
      simp only [Exp.pk, Exp.wp, Exp.val_of hv', Exp.val_of hx, Exp.val_of hy]
      refine max_lt (max_lt (max_lt (max_lt (max_lt (lt_pow_max_left (lt_pow_max_left hcp)) (hK
        _ hrow))
        (hK _ (by omega))) (lt_pow_max_left (lt_pow_max_right hjp))) (hK _ hidx)) (hK _ hval)
    · simp only [reduceCtorEq] at hv
  | .opt o, v, _, hv => by
    simp only [ev, Option.some.injEq] at hv; subst hv
    exact ⟨hM.opt o, by simpa [Exp.pk, Exp.wp] using hM.opt o⟩

/-- The peak alone. -/
theorem Exp.pk_lt (hM : MemW K KH κ s) (hC : CapsW K κ) (hΓ : ∀ x, L x < 2 ^ Γ x) {e : Exp} {v :
  Nat}
    (hs : e.ShOK κ s L S) (hv : e.ev κ s L = some v) : e.pk κ s L < 2 ^ e.wp Γ K KH S :=
  (Exp.wd_sound hM hC hΓ e hs hv).2

/-- The peak of an argument list. -/
theorem pkList_lt (hM : MemW K KH κ s) (hC : CapsW K κ) (hΓ : ∀ x, L x < 2 ^ Γ x) {W : Nat} :
    ∀ {es : List Exp} {vs : List Nat}, (∀ e ∈ es, e.ShOK κ s L S ∧ e.wp Γ K KH S ≤ W) →
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
        have h1 := Exp.pk_lt hM hC hΓ (h e (by simp)).1 he
        have h2 := pkList_lt hM hC hΓ (es := es) (fun e' he' => h e' (by simp only [
            List.mem_cons,
            he',
            or_true])) hes
        simp only [pkList, List.map_cons, List.foldr_cons] at h2 ⊢
        exact max_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (h e (by simp)).2)) h2

/-! ### A closed form in the depth -/

/-- Structural nesting depth used to bound expression intermediates. -/
def Exp.depth : Exp → Nat
  | .lit _ | .var _ | .size _ | .prm _ | .opt _ => 0
  | .rd _ i | .llen _ i | .un _ i => i.depth + 1
  | .bin _ a b | .lrd _ _ a b | .prd a b => Max.max a.depth b.depth + 1

/-- Every literal of `e` is at most `K`. -/
def Exp.litLe (K : Nat) : Exp → Prop
  | .lit n => n ≤ K
  | .var _ | .size _ | .prm _ | .opt _ => True
  | .rd _ i | .llen _ i | .un _ i => i.litLe K
  | .bin _ a b | .lrd _ _ a b | .prd a b => a.litLe K ∧ b.litLe K

theorem Exp.wv_le_wp (Γ : Reg → Nat) (K KH S : Nat) : ∀ e : Exp, e.wv Γ K KH S ≤ e.wp Γ K KH S
  | .lit _ | .var _ | .size _ | .prm _ | .opt _ => le_refl _
  | .rd _ _ | .bin _ _ _ | .un _ _ | .lrd _ _ _ _ | .llen _ _ | .prd _ _ => le_max_right _ _

theorem two_pow_succ_mul (d c : Nat) : 2 ^ (d + 1) * c = 2 * (2 ^ d * c) := by ring

/-- **The closed form**: with every local, handle and literal of width at most `K` (and
`K ≥ 1`), an expression of depth `d` has peak width at most `2^d · (K + S)`. -/
theorem Exp.wp_le_depth (hK : 1 ≤ K) (hΓ : ∀ x, Γ x ≤ K) (hH : KH ≤ K) :
    ∀ e : Exp, e.litLe K → e.wp Γ K KH S ≤ 2 ^ e.depth * (K + S)
  | .lit n, h => by simp only [Exp.wp, Exp.depth, Exp.litLe] at h ⊢; omega
  | .var x, _ => by have := hΓ x; simp only [Exp.wp, Exp.depth]; omega
  | .size _, _ | .prm _, _ | .opt _, _ => by simp only [Exp.wp, Exp.depth]; omega
  | .rd f i, h => by
    have hi := Exp.wp_le_depth hK hΓ hH i h
    have hf : f.wd K KH ≤ K := by unfold Fld.wd; split <;> omega
    have hp : K + S ≤ 2 ^ i.depth * (K + S) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    simp only [Exp.wp, Exp.depth]
    rw [two_pow_succ_mul]
    generalize 2 ^ i.depth * (K + S) = X at hi hp
    omega
  | .llen _ i, h => by
    have hi := Exp.wp_le_depth hK hΓ hH i h
    have hp : K + S ≤ 2 ^ i.depth * (K + S) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    simp only [Exp.wp, Exp.depth]
    rw [two_pow_succ_mul]
    generalize 2 ^ i.depth * (K + S) = X at hi hp
    omega
  | .un op a, h => by
    have ha := Exp.wp_le_depth hK hΓ hH a h
    have hv := Exp.wv_le_wp Γ K KH S a
    have hp : K + S ≤ 2 ^ a.depth * (K + S) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have hw : op.wd (a.wv Γ K KH S) ≤ Max.max (a.wp Γ K KH S) 1 := by
      cases op <;> simp only [Machine.UnOp.wd] <;> omega
    simp only [Exp.wp, Exp.depth]
    rw [two_pow_succ_mul]
    generalize 2 ^ a.depth * (K + S) = X at ha hp
    generalize op.wd (a.wv Γ K KH S) = w at hw ⊢
    omega
  | .bin op a b, h => by
    have ha := Exp.wp_le_depth hK hΓ hH a h.1
    have hb := Exp.wp_le_depth hK hΓ hH b h.2
    have hva := Exp.wv_le_wp Γ K KH S a
    have hvb := Exp.wv_le_wp Γ K KH S b
    have hpa : 2 ^ a.depth * (K + S) ≤ 2 ^ Max.max a.depth b.depth * (K + S) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    have hpb : 2 ^ b.depth * (K + S) ≤ 2 ^ Max.max a.depth b.depth * (K + S) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    have hp : K + S ≤ 2 ^ Max.max a.depth b.depth * (K + S) := Nat.le_mul_of_pos_left _
      (Nat.two_pow_pos _)
    have hw : op.wd S (a.wv Γ K KH S) (b.wv Γ K KH S) ≤
        Max.max (Max.max (a.wv Γ K KH S + b.wv Γ K KH S) (Max.max (a.wv Γ K KH S) (b.wv Γ K KH
          S) + 1))
          (Max.max (a.wv Γ K KH S + S) 1) := by
      cases op <;> simp only [Machine.BinOp.wd] <;> omega
    simp only [Exp.wp, Exp.depth]
    rw [two_pow_succ_mul]
    generalize 2 ^ Max.max a.depth b.depth * (K + S) = X at hpa hpb hp
    generalize op.wd S (a.wv Γ K KH S) (b.wv Γ K KH S) = w at hw ⊢
    omega
  | .lrd _ _ a b, h | .prd a b, h => by
    have ha := Exp.wp_le_depth hK hΓ hH a h.1
    have hb := Exp.wp_le_depth hK hΓ hH b h.2
    have hpa : 2 ^ a.depth * (K + S) ≤ 2 ^ Max.max a.depth b.depth * (K + S) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
    have hpb : 2 ^ b.depth * (K + S) ≤ 2 ^ Max.max a.depth b.depth * (K + S) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
    have hp : K + S ≤ 2 ^ Max.max a.depth b.depth * (K + S) := Nat.le_mul_of_pos_left _
      (Nat.two_pow_pos _)
    simp only [Exp.wp, Exp.depth]
    rw [two_pow_succ_mul]
    generalize 2 ^ Max.max a.depth b.depth * (K + S) = X at hpa hpb hp
    omega

/-- A value below `2^(max a b)` is below `2^a + 2^b`: a width bound `max K KH` with `KH` the width
of a handle splits into "below `2^K`, or at most about twice the handle bound" (the convention
of `docs/WORD.md` §1). -/
theorem lt_pow_max_add {x a b : Nat} (h : x < 2 ^ Max.max a b) : x < 2 ^ a + 2 ^ b := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab] at h; exact lt_of_lt_of_le h (Nat.le_add_left _ _)
  · rw [max_eq_left hab] at h; exact lt_of_lt_of_le h (Nat.le_add_right _ _)

end OrderMaintenance.Impl
