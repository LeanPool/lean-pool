/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakWord


/-!
# A RAM without `alloc`: the flat program

`exec` has one instruction that a standard RAM lacks: `alloc a n` gives array `a` capacity `n`,
all cells reading 0, in one step. This file shows that the program does not need it.
`flatten c` translates a program into one that keeps all its data in a single array, array `0`
(the RAM's memory), and contains no `alloc` (`flatten_noAlloc`, `flatten_maxArr`). The flat
program runs on the same interpreter `exec`, so the trusted base does not grow. The only
assumption is the standard RAM one: the memory array is zero-filled at the start.

**Layout**, for a program whose array names are at most `A` (`Stmt.maxArr`), in a memory of
capacity `M`:
* cell `0` holds the heap pointer (`heapPtr`);
* cell `a + 1` holds the base address of array `a` (`base`): cell `j` of `a` is memory cell
  `base a + j`;
* the heap is `[A + 2, M)`, used from the top down: the cells `[A + 2, heapPtr)` are free and
  read 0, and the arrays lie in `[heapPtr, M)`.

**Translation.** `alloc a n` takes a fresh region just below the heap pointer:
`heapPtr := heapPtr - n; base a := heapPtr`. The region reads 0 because it has never been used;
the old region of `a` is abandoned and never read again. `load a i` becomes
`load 0 (load 0 (a + 1) + i)`, and `store a i e` likewise; everything else (locals, branches,
loops, calls with their frames, `fail`, `catch`) is translated structurally. A prelude
`prelude M` sets the heap pointer to `M`.

**The simulation** (`flatten_sim`). From related states (`FRel`), if `exec c s` does not end in a
machine error, then `exec (flatten c) f` ends with the same status, in related states, within
`5 ×` the steps, provided the free part of the heap has `cost × P` cells, where `cost` is the
original run's cost and `P` bounds its peak: every allocation costs at least one step and its
size is a value the run computes. The heap pointer moves down by at most `cost × P`, and the flat
run computes no value above the original's peak or `M` (`flatten_dpk`). The factor `5`: an array
access costs 3 more steps (4 instead of 1), and `alloc a n` (cost `1 + n.cost`) becomes two stores
of cost `9 + (flattenE n).cost`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-! ### Array names and allocations in the program text -/

/-- The largest array name an expression reads (0 if none). -/
def Expr.maxArr : Expr → Nat
  | .lit _ | .var _ => 0
  | .load a i => max a i.maxArr
  | .bin _ e₁ e₂ => max e₁.maxArr e₂.maxArr
  | .un _ e => e.maxArr

/-- The largest array name a statement mentions, callee bodies included (0 if none). -/
def Stmt.maxArr : Stmt → Nat
  | .skip | .fail => 0
  | .assign _ e => e.maxArr
  | .store a i e => max a (max i.maxArr e.maxArr)
  | .alloc a n => max a n.maxArr
  | .seq c d => max c.maxArr d.maxArr
  | .ite e c d => max e.maxArr (max c.maxArr d.maxArr)
  | .loop _ n b => max n.maxArr b.maxArr
  | .call _ _ b _ args _ => max b.maxArr ((args.map Expr.maxArr).foldr max 0)
  | .catch c h => max c.maxArr h.maxArr

/-- Whether a statement contains an `alloc`, callee bodies included. -/
def Stmt.hasAlloc : Stmt → Bool
  | .alloc _ _ => true
  | .seq c d | .ite _ c d | .catch c d => c.hasAlloc || d.hasAlloc
  | .loop _ _ b | .call _ _ b _ _ _ => b.hasAlloc
  | _ => false

/-! ### The translation -/

/-- The heap pointer of the flat machine: memory cell 0. -/
def heapPtr (f : State) : Nat := f.mem 0 0

/-- The base address of array `a` on the flat machine: memory cell `a + 1`. -/
def base (f : State) (a : Arr) : Nat := f.mem 0 (a + 1)

/-- The address of cell `i` of array `a`: `base a + i`. -/
def addrE (a : Arr) (i : Expr) : Expr := .bin .add (.load 0 (.lit (a + 1))) i

/-- **The translation of an expression**: every array access goes through the table. -/
def flattenE : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .load a i => .load 0 (addrE a (flattenE i))
  | .bin op e₁ e₂ => .bin op (flattenE e₁) (flattenE e₂)
  | .un op e => .un op (flattenE e)

/-- **The translation of a statement.** `alloc a n` becomes
`heapPtr := heapPtr - n; base a := heapPtr`; array accesses go through the table. -/
def flatten : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x (flattenE e)
  | .store a i e => .store 0 (addrE a (flattenE i)) (flattenE e)
  | .alloc a n => .seq (.store 0 (.lit 0) (.bin .sub (.load 0 (.lit 0)) (flattenE n)))
      (.store 0 (.lit (a + 1)) (.load 0 (.lit 0)))
  | .seq c d => .seq (flatten c) (flatten d)
  | .ite e c d => .ite (flattenE e) (flatten c) (flatten d)
  | .loop x n b => .loop x (flattenE n) (flatten b)
  | .call nm ps b rs args ds => .call nm ps (flatten b) rs (args.map flattenE) ds
  | .fail => .fail
  | .catch c h => .catch (flatten c) (flatten h)

/-- **The prelude**: the heap pointer starts at the top of a memory of capacity `M`. -/
def prelude (M : Nat) : Stmt := .store 0 (.lit 0) (.lit M)

/-! ### The flat program has no `alloc` and uses only array 0 -/

theorem flattenE_maxArr : ∀ e : Expr, (flattenE e).maxArr = 0
  | .lit _ | .var _ => rfl
  | .load _ i => by simp [flattenE, addrE, Expr.maxArr, flattenE_maxArr i]
  | .bin _ e₁ e₂ => by simp [flattenE, Expr.maxArr, flattenE_maxArr e₁, flattenE_maxArr e₂]
  | .un _ e => by simp [flattenE, Expr.maxArr, flattenE_maxArr e]

theorem flattenL_maxArr : ∀ es : List Expr, ((es.map flattenE).map Expr.maxArr).foldr max 0 = 0
  | [] => rfl
  | e :: es => by
    simp only [List.map_cons, List.foldr_cons, flattenE_maxArr e, flattenL_maxArr es]; rfl

/-- **The flat program uses only array 0.** -/
theorem flatten_maxArr : ∀ c : Stmt, (flatten c).maxArr = 0
  | .skip | .fail => rfl
  | .assign _ e => by simp [flatten, Stmt.maxArr, flattenE_maxArr]
  | .store _ i e => by simp [flatten, Stmt.maxArr, addrE, Expr.maxArr, flattenE_maxArr]
  | .alloc _ n => by simp [flatten, Stmt.maxArr, Expr.maxArr, flattenE_maxArr]
  | .seq c d => by simp [flatten, Stmt.maxArr, flatten_maxArr c, flatten_maxArr d]
  | .ite e c d => by
    simp [flatten, Stmt.maxArr, flattenE_maxArr, flatten_maxArr c, flatten_maxArr d]
  | .loop _ n b => by simp [flatten, Stmt.maxArr, flattenE_maxArr, flatten_maxArr b]
  | .call _ _ b _ args _ => by
    simp only [flatten, Stmt.maxArr, flatten_maxArr b, flattenL_maxArr]; rfl
  | .catch c h => by simp [flatten, Stmt.maxArr, flatten_maxArr c, flatten_maxArr h]

/-- **The flat program contains no `alloc`.** -/
theorem flatten_noAlloc : ∀ c : Stmt, (flatten c).hasAlloc = false
  | .skip | .fail | .assign _ _ | .store _ _ _ | .alloc _ _ => rfl
  | .seq c d => by simp [flatten, Stmt.hasAlloc, flatten_noAlloc c, flatten_noAlloc d]
  | .ite _ c d => by simp [flatten, Stmt.hasAlloc, flatten_noAlloc c, flatten_noAlloc d]
  | .loop _ _ b => by simp [flatten, Stmt.hasAlloc, flatten_noAlloc b]
  | .call _ _ b _ _ _ => by simp [flatten, Stmt.hasAlloc, flatten_noAlloc b]
  | .catch c h => by simp [flatten, Stmt.hasAlloc, flatten_noAlloc c, flatten_noAlloc h]

/-! ### Costs -/

theorem Expr.cost_pos : ∀ e : Expr, 1 ≤ e.cost
  | .lit _ | .var _ => le_refl _
  | .load _ _ | .bin _ _ _ | .un _ _ => by simp only [Expr.cost]; omega

/-- Each array access costs 3 more steps; an expression has at least one leaf, which is not an
access. -/
theorem flattenE_cost : ∀ e : Expr, (flattenE e).cost + 3 ≤ 4 * e.cost
  | .lit _ | .var _ => by simp [flattenE, Expr.cost]
  | .load _ i => by have := flattenE_cost i; simp only [flattenE, addrE, Expr.cost]; omega
  | .bin _ e₁ e₂ => by
    have := flattenE_cost e₁; have := flattenE_cost e₂; simp only [flattenE, Expr.cost]; omega
  | .un _ e => by have := flattenE_cost e; simp only [flattenE, Expr.cost]; omega

theorem flattenL_cost : ∀ es : List Expr, costList (es.map flattenE) ≤ 4 * costList es
  | [] => le_refl _
  | e :: es => by
    have := flattenE_cost e; have := flattenL_cost es
    simp only [costList, List.map_cons, List.sum_cons] at *; omega

/-! ### The relation between an original and a flat state -/

/-- **The simulation relation** between an original state `s` and a flat state `f`, for array
names at most `A` and a memory of capacity `M`: the same locals; the heap pointer in
`[A + 2, M]`; each array `a ≤ A` stored at `base a` in `[heapPtr, M)`, the arrays pairwise
disjoint; the free cells `[A + 2, heapPtr)` read 0. The peaks are not related. -/
structure FRel (A M : Nat) (s f : State) : Prop where
  loc : f.loc = s.loc
  cap : f.cap 0 = M
  lo : A + 2 ≤ heapPtr f
  hi : heapPtr f ≤ M
  inR : ∀ a ≤ A, ∀ j < s.cap a, heapPtr f ≤ base f a + j ∧ base f a + j < M
  val : ∀ a ≤ A, ∀ j < s.cap a, f.mem 0 (base f a + j) = s.mem a j
  disj : ∀ a ≤ A, ∀ b ≤ A, a ≠ b → ∀ j < s.cap a, ∀ k < s.cap b, base f a + j ≠ base f b + k
  zero : ∀ i, A + 2 ≤ i → i < heapPtr f → f.mem 0 i = 0

/-- The relation reads only the original memory, capacities and locals, and the flat array 0
and locals. -/
theorem FRel.congr {A M : Nat} {s f s' f' : State} (h : FRel A M s f) (hsm : s'.mem = s.mem)
    (hsc : s'.cap = s.cap) (hfm : f'.mem 0 = f.mem 0) (hfc : f'.cap 0 = f.cap 0) (hl : f'.loc =
      s'.loc) :
    FRel A M s' f' := by
  have hp : heapPtr f' = heapPtr f := by simp only [heapPtr, hfm]
  have hb : ∀ a, base f' a = base f a := fun a => by simp only [base, hfm]
  refine ⟨hl, hfc.trans h.cap, hp ▸ h.lo, hp ▸ h.hi, fun a ha j hj => ?_, fun a ha j hj => ?_,
    fun a ha b hb' hab j hj k hk => ?_, fun i h1 h2 => ?_⟩
  · rw [hsc] at hj; rw [hp, hb]; exact h.inR a ha j hj
  · rw [hsc] at hj; rw [hb, hfm, hsm]; exact h.val a ha j hj
  · rw [hsc] at hj hk; rw [hb, hb]; exact h.disj a ha b hb' hab j hj k hk
  · rw [hp] at h2; rw [hfm]; exact h.zero i h1 h2

theorem upd_same {α : Type} [DecidableEq α] (g : α → Nat) (a : α) (v : Nat) : State.upd g a v a
  = v := by
  simp [State.upd]

theorem upd_other {α : Type} [DecidableEq α] (g : α → Nat) {a b : α} (v : Nat) (h : b ≠ a) :
    State.upd g a v b = g b := by
  simp [State.upd, h]

/-- A store to a cell of array `a`: the flat store to its address. -/
theorem FRel.store {A M : Nat} {s f s' f' : State} (h : FRel A M s f) {a j v : Nat} (ha : a ≤ A)
    (hj : j < s.cap a) (hsm : s'.mem = (s.write a j v).mem) (hsc : s'.cap = s.cap)
    (hfm : f'.mem 0 = State.upd (f.mem 0) (base f a + j) v) (hfc : f'.cap 0 = M) (hl : f'.loc =
      s'.loc) :
    FRel A M s' f' := by
  obtain ⟨h1, h2⟩ := h.inR a ha j hj
  have hlo := h.lo
  have hp : heapPtr f' = heapPtr f := by
    unfold heapPtr; rw [hfm, upd_other _ _ (by
      unfold heapPtr at h1 hlo
      omega)]
  have hb : ∀ b ≤ A, base f' b = base f b := fun b hb => by
    unfold base; rw [hfm, upd_other _ _ (by
      unfold heapPtr base at *
      omega)]
  refine ⟨hl, hfc, hp ▸ h.lo, hp ▸ h.hi, fun b hb' k hk => ?_, fun b hb' k hk => ?_,
    fun b hb' c hc hbc k hk l hl' => ?_, fun i i1 i2 => ?_⟩
  · rw [hsc] at hk; rw [hp, hb b hb']; exact h.inR b hb' k hk
  · rw [hsc] at hk; rw [hb b hb', hfm, hsm]
    by_cases e : b = a
    · subst e
      have ew : (s.write b j v).mem b = State.upd (s.mem b) j v := by simp [State.write]
      rw [ew]
      by_cases ek : k = j
      · subst ek; rw [upd_same, upd_same]
      · rw [upd_other _ _ (by omega), upd_other _ _ ek]; exact h.val b hb' k hk
    · have ew : (s.write a j v).mem b = s.mem b := by simp [State.write, e]
      rw [ew, upd_other _ _ (h.disj b hb' a ha e k hk j hj)]; exact h.val b hb' k hk
  · rw [hsc] at hk hl'; rw [hb b hb', hb c hc]; exact h.disj b hb' c hc hbc k hk l hl'
  · rw [hp] at i2; rw [hfm, upd_other _ _ (by omega)]; exact h.zero i i1 i2

/-- An allocation of `k` cells for array `a`: the region just below the heap pointer. -/
theorem FRel.alloc {A M : Nat} {s f s' f' : State} (h : FRel A M s f) {a k : Nat} (ha : a ≤ A)
    (hk : A + 2 + k ≤ heapPtr f) (hsm : s'.mem = (s.alloc a k).mem) (hsc : s'.cap = (s.alloc a
      k).cap)
    (hfm : f'.mem 0 = State.upd (State.upd (f.mem 0) 0 (heapPtr f - k)) (a + 1) (heapPtr f - k))
    (hfc : f'.cap 0 = M) (hl : f'.loc = s'.loc) : FRel A M s' f' := by
  have hhi := h.hi
  have hp : heapPtr f' = heapPtr f - k := by
    unfold heapPtr; rw [hfm, upd_other _ _ (by omega), upd_same]; rfl
  have hba : base f' a = heapPtr f - k := by unfold base; rw [hfm, upd_same]
  have hb : ∀ b, b ≠ a → base f' b = base f b := fun b hb => by
    unfold base; rw [hfm, upd_other _ _ (by omega), upd_other _ _ (by omega)]
  have hm : ∀ i, A + 2 ≤ i → f'.mem 0 i = f.mem 0 i := fun i hi => by
    rw [hfm, upd_other _ _ (by omega), upd_other _ _ (by omega)]
  have hca : s'.cap a = k := by rw [hsc]; simp [State.alloc, State.upd]
  have hcb : ∀ b, b ≠ a → s'.cap b = s.cap b := fun b hb => by rw [hsc]; simp [State.alloc,
    State.upd, hb]
  refine ⟨hl, hfc, by rw [hp]; omega, by rw [hp]; omega, fun b hb' j hj => ?_, fun b hb' j hj => ?_,
    fun b hb' c hc hbc j hj l hl' => ?_, fun i i1 i2 => ?_⟩
  · by_cases e : b = a
    · subst e; rw [hca] at hj; rw [hp, hba]; omega
    · rw [hcb b e] at hj; rw [hp, hb b e]; have := h.inR b hb' j hj; omega
  · by_cases e : b = a
    · subst e; rw [hca] at hj; rw [hba, hm _ (by omega), hsm]
      have ea : (s.alloc b k).mem b j = 0 := by simp [State.alloc]
      rw [ea]; exact h.zero _ (by omega) (by omega)
    · rw [hcb b e] at hj; have := h.inR b hb' j hj
      have ea : (s.alloc a k).mem b j = s.mem b j := by simp [State.alloc, e]
      rw [hb b e, hm _ (by omega), hsm, ea]; exact h.val b hb' j hj
  · by_cases eb : b = a
    · subst eb; have ec : c ≠ b := fun e => hbc e.symm
      rw [hca] at hj; rw [hcb c ec] at hl'
      have := h.inR c hc l hl'; rw [hba, hb c ec]; omega
    · by_cases ec : c = a
      · subst ec; rw [hca] at hl'; rw [hcb b eb] at hj
        have := h.inR b hb' j hj; rw [hba, hb b eb]; omega
      · rw [hcb b eb] at hj; rw [hcb c ec] at hl'; rw [hb b eb, hb c ec]
        exact h.disj b hb' c hc hbc j hj l hl'
  · rw [hp] at i2; rw [hm i i1]; exact h.zero i i1 (by omega)

/-! ### Expressions -/

theorem Expr.le_maxv {s : State} : ∀ {e : Expr} {v : Nat}, e.eval s = some v → v ≤ e.maxv s
  | .lit _, v, h => by simp only [Expr.eval, Option.some.injEq] at h; subst h; exact le_refl _
  | .var _, v, h => by simp only [Expr.eval, Option.some.injEq] at h; subst h; exact le_refl _
  | .load _ _, v, h => by simp only [Expr.maxv]; rw [h]; exact le_max_right _ _
  | .bin _ _ _, v, h => by simp only [Expr.maxv]; rw [h]; exact le_max_right _ _
  | .un _ _, v, h => by simp only [Expr.maxv]; rw [h]; exact le_max_right _ _

/-- The address of a cell of a stored array. -/
theorem addrE_eval {A M : Nat} {s f : State} (h : FRel A M s f) {a : Nat} (ha : a ≤ A) {i :
  Expr} {j : Nat}
    (hi : i.eval f = some j) :
    (addrE a i).eval f = some (base f a + j) ∧
      (addrE a i).maxv f = max (max (max (a + 1) (base f a)) (i.maxv f)) (base f a + j) := by
  have hlo := h.lo; have hhi := h.hi
  have hc : a + 1 < f.cap 0 := by rw [h.cap]; omega
  have e1 : (Expr.load 0 (.lit (a + 1))).eval f = some (base f a) := by
    simp [Expr.eval, hc, base]
  have e2 : (addrE a i).eval f = some (base f a + j) := by
    simp only [addrE, Expr.eval] at e1 ⊢; rw [e1, hi]; rfl
  refine ⟨e2, ?_⟩
  have m0 : (addrE a i).maxv f =
      max (max ((Expr.load 0 (.lit (a + 1))).maxv f) (i.maxv f)) (((addrE a i).eval f).getD 0)
        := rfl
  have e3 : (Expr.load 0 (.lit (a + 1))).maxv f = max (a + 1) (base f a) := by
    simp only [Expr.maxv]; rw [e1]; rfl
  rw [m0, e2, e3]; rfl

/-- **Expressions**: the flat expression has the original's value, and computes no value above
the original's or `M`. -/
theorem flattenE_eval {A M : Nat} {s f : State} (h : FRel A M s f) :
    ∀ (e : Expr), e.maxArr ≤ A → ∀ v, e.eval s = some v →
      (flattenE e).eval f = some v ∧ (flattenE e).maxv f ≤ max (e.maxv s) M
  | .lit n, _, v, hv => by
    simp only [Expr.eval, Option.some.injEq] at hv; subst hv
    exact ⟨rfl, le_max_left _ _⟩
  | .var x, _, v, hv => by
    simp only [Expr.eval, Option.some.injEq] at hv; subst hv
    exact ⟨by simp [flattenE, Expr.eval, h.loc], by simp [flattenE, Expr.maxv, h.loc]⟩
  | .load a i, hA, v, hv => by
    simp only [Expr.maxArr] at hA
    cases hi : i.eval s with
    | none => simp [Expr.eval, hi] at hv
    | some j =>
      have hv' := hv
      simp only [Expr.eval, hi, Option.bind_some] at hv'
      split at hv'
      · next hj =>
        simp only [Option.some.injEq] at hv'; subst hv'
        obtain ⟨hi', hm⟩ := flattenE_eval h i (by omega) j hi
        have ha := le_trans (le_max_left _ _) hA
        obtain ⟨ea, ma⟩ := addrE_eval h ha hi'
        obtain ⟨r1, r2⟩ := h.inR a ha j hj
        have hval := h.val a ha j hj
        have hc : base f a + j < f.cap 0 := by rw [h.cap]; exact r2
        have ev : (flattenE (.load a i)).eval f = some (s.mem a j) := by
          simp only [flattenE, Expr.eval]; rw [ea]; simp [hc, hval]
        refine ⟨ev, ?_⟩
        have hm0 : (Expr.load a i).maxv s = max (i.maxv s) (((Expr.load a i).eval s).getD 0) := rfl
        have hm1 : (flattenE (.load a i)).maxv f =
            max ((addrE a (flattenE i)).maxv f) (((flattenE (.load a i)).eval f).getD 0) := rfl
        rw [hv] at hm0; rw [ev] at hm1
        rw [hm0, hm1, ma]; simp only [Option.getD_some]
        have := h.lo; unfold heapPtr at *
        omega
      · cases hv'
  | .bin op e₁ e₂, hA, v, hv => by
    simp only [Expr.maxArr] at hA
    cases h1 : e₁.eval s with
    | none => simp [Expr.eval, h1] at hv
    | some a =>
      cases h2 : e₂.eval s with
      | none => simp [Expr.eval, h1, h2] at hv
      | some b =>
        obtain ⟨f1, m1⟩ := flattenE_eval h e₁ (by omega) a h1
        obtain ⟨f2, m2⟩ := flattenE_eval h e₂ (by omega) b h2
        have ev : (flattenE (.bin op e₁ e₂)).eval f = some v := by
          simp only [flattenE, Expr.eval, f1, f2, Option.bind_some]
          simp only [Expr.eval, h1, h2, Option.bind_some] at hv; exact hv
        refine ⟨ev, ?_⟩
        have hm0 : (Expr.bin op e₁ e₂).maxv s =
            max (max (e₁.maxv s) (e₂.maxv s)) (((Expr.bin op e₁ e₂).eval s).getD 0) := rfl
        have hm1 : (flattenE (.bin op e₁ e₂)).maxv f =
            max (max ((flattenE e₁).maxv f) ((flattenE e₂).maxv f)) (((flattenE (.bin op e₁
              e₂)).eval f).getD 0) := rfl
        rw [hv] at hm0; rw [ev] at hm1
        rw [hm0, hm1]; simp only [Option.getD_some]; omega
  | .un op e, hA, v, hv => by
    simp only [Expr.maxArr] at hA
    cases h1 : e.eval s with
    | none => simp [Expr.eval, h1] at hv
    | some a =>
      obtain ⟨f1, m1⟩ := flattenE_eval h e hA a h1
      have ev : (flattenE (.un op e)).eval f = some v := by
        simp only [flattenE, Expr.eval, f1]
        simp only [Expr.eval, h1] at hv; exact hv
      refine ⟨ev, ?_⟩
      have hm0 : (Expr.un op e).maxv s = max (e.maxv s) (((Expr.un op e).eval s).getD 0) := rfl
      have hm1 : (flattenE (.un op e)).maxv f =
          max ((flattenE e).maxv f) (((flattenE (.un op e)).eval f).getD 0) := rfl
      rw [hv] at hm0; rw [ev] at hm1
      rw [hm0, hm1]; simp only [Option.getD_some]; omega

theorem maxArrL_le {A : Nat} : ∀ {es : List Expr}, (es.map Expr.maxArr).foldr max 0 ≤ A → ∀ e ∈
  es, e.maxArr ≤ A
  | [], _, _, he => by cases he
  | e :: es, h, e', he => by
    simp only [List.map_cons, List.foldr_cons] at h
    rcases List.mem_cons.1 he with rfl | he
    · omega
    · exact maxArrL_le (by omega) e' he

/-- **Argument lists**, as `flattenE_eval`. -/
theorem flattenL_eval {A M : Nat} {s f : State} (h : FRel A M s f) :
    ∀ (es : List Expr), (∀ e ∈ es, e.maxArr ≤ A) → ∀ vs, evalList s es = some vs →
      evalList f (es.map flattenE) = some vs ∧ maxvList f (es.map flattenE) ≤ max (maxvList s es) M
  | [], _, vs, hv => by
    simp only [evalList, List.mapM_nil, Option.pure_def, Option.some.injEq] at hv; subst hv
    exact ⟨rfl, Nat.zero_le _⟩
  | e :: es, hA, vs, hv => by
    simp only [evalList, List.mapM_cons] at hv
    cases h1 : e.eval s with
    | none => simp [h1] at hv
    | some v =>
      cases h2 : es.mapM (·.eval s) with
      | none => simp [h1, h2] at hv
      | some ws =>
        simp only [h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hv
        subst hv
        obtain ⟨f1, m1⟩ := flattenE_eval h e (hA e (List.mem_cons_self ..)) v h1
        obtain ⟨f2, m2⟩ := flattenL_eval h es (fun e' he' => hA e' (List.mem_cons_of_mem _ he'))
          ws h2
        simp only [evalList] at f2
        refine ⟨?_, ?_⟩
        · simp only [evalList, List.map_cons, List.mapM_cons, f1, f2, Option.bind_eq_bind,
          Option.bind_some,
            Option.pure_def]
        · simp only [maxvList, List.map_cons, List.foldr_cons] at m2 ⊢; omega

/-! ### Outcomes -/

/-- **One simulated outcome**: `o'` (flat, from `f`) has `o`'s status, a related state, at most
`5 ×` its cost, and a heap pointer at most `o.cost × P` below `f`'s; and it computes no value
above `f`'s peak, `o`'s peak or `M`. -/
structure SimOK (A M P : Nat) (f : State) (o o' : Out) : Prop where
  status : o'.status = o.status
  rel : FRel A M o.st o'.st
  cost : o'.cost ≤ 5 * o.cost
  heap : heapPtr f ≤ heapPtr o'.st + o.cost * P
  peak : o'.st.peak ≤ max f.peak (max o.st.peak M)

/-- `SimOK` when `o` is not a machine error, its peak is at most `P`, and the heap has room. -/
def SimO (A M P : Nat) (f : State) (o o' : Out) : Prop :=
  o.status ≠ .err → o.st.peak ≤ P → A + 2 + o.cost * P ≤ heapPtr f → SimOK A M P f o o'

/-- `g'` simulates `g` from related states. -/
def Sims (A M : Nat) (g g' : State → Out) : Prop :=
  ∀ s f P, FRel A M s f → SimO A M P f (g s) (g' f)

theorem SimO.of_eq {A M P : Nat} {f f' : State} {o o' : Out} (h : SimO A M P f o o')
    (hh : heapPtr f = heapPtr f') (hp : f.peak = f'.peak) : SimO A M P f' o o' := by
  intro h1 h2 h3
  obtain ⟨a, b, c, d, e⟩ := h h1 h2 (hh ▸ h3)
  exact ⟨a, b, c, hh ▸ d, hp ▸ e⟩

theorem heapPtr_write (f : State) {p : Nat} (v : Nat) (h : p ≠ 0) : heapPtr (f.write 0 p v) =
  heapPtr f := by
  simp [heapPtr, State.write, State.upd, Ne.symm h]

theorem simO_ok {A M P : Nat} {f s' f' : State} {c c' : Nat} (hR : FRel A M s' f') (hc : c' ≤ 5 * c)
    (hh : heapPtr f ≤ heapPtr f' + c * P) (hp : f'.peak ≤ max f.peak (max s'.peak M)) :
    SimO A M P f ⟨s', c, .ok⟩ ⟨f', c', .ok⟩ :=
  fun _ _ _ => ⟨rfl, hR, hc, hh, hp⟩

theorem Out.cost_le_bind (o : Out) (g : State → Out) : o.cost ≤ (o.bind g).cost := by
  unfold Out.bind; split
  · exact Nat.le_add_right _ _
  · exact le_refl _

theorem Out.ne_err_of_bind {o : Out} {g : State → Out} (h : (o.bind g).status ≠ .err) : o.status
  ≠ .err := by
  unfold Out.bind at h; split at h
  · next hs => rw [hs]; simp
  · exact h

/-- **Sequential composition.** -/
theorem simO_bind {A M P : Nat} {f : State} {o o' : Out} {g g' : State → Out}
    (h : SimO A M P f o o') (hg : Sims A M g g') (hm : ∀ s, s.peak ≤ (g s).st.peak) :
    SimO A M P f (o.bind g) (o'.bind g') := by
  intro herr hpk hvol
  have h1 := h (Out.ne_err_of_bind herr) (le_trans (Out.bind_peak_le hm) hpk)
    (le_trans (by
      have := Nat.mul_le_mul_right P (Out.cost_le_bind o g)
      omega) hvol)
  cases hs : o.status with
  | ok =>
    have hs' : o'.status = .ok := h1.status.trans hs
    rw [Out.bind_ok hs] at herr hpk hvol ⊢
    rw [Out.bind_ok hs']
    simp only [Nat.add_mul] at hvol
    have hh := h1.heap
    have h2 := hg o.st o'.st P h1.rel herr hpk (by omega)
    have := hm o.st
    have := h1.peak; have := h2.peak
    refine ⟨h2.status, h2.rel, by have := h1.cost; have := h2.cost; simp only; omega, ?_, ?_⟩
    · have := h2.heap; simp only [Nat.add_mul]; omega
    · simp only at *; omega
  | fail =>
    have hs' : o'.status = .fail := h1.status.trans hs
    have e1 : o.bind g = o := by unfold Out.bind; rw [hs]
    have e2 : o'.bind g' = o' := by unfold Out.bind; rw [hs']
    rw [e1, e2]; exact h1
  | err => exact absurd hs (Out.ne_err_of_bind herr)

/-- **Loops.** -/
theorem sims_runFor {A M : Nat} {b b' : State → Out} (hb : Sims A M b b') (hm : ∀ s, s.peak ≤ (b
  s).st.peak)
    (x : Reg) : ∀ n k, Sims A M (runFor b x k n) (runFor b' x k n)
  | 0, _ => fun _ _ _ hR => simO_ok hR (le_refl _) (Nat.le_add_right _ _) (le_max_left _ _)
  | n + 1, k => fun s f P hR => by
    change SimO A M P f
      ((Out.bind ⟨s, 1, .ok⟩ fun s => b (s.setLoc x k)).bind (runFor b x (k + 1) n))
      ((Out.bind ⟨f, 1, .ok⟩ fun s => b' (s.setLoc x k)).bind (runFor b' x (k + 1) n))
    refine simO_bind (simO_bind (simO_ok hR (by omega) (Nat.le_add_right _ _) (le_max_left _ _))
      (fun s f P hR => (hb (s.setLoc x k) (f.setLoc x k) P
        (hR.congr rfl rfl rfl rfl (by simp [State.setLoc, hR.loc]))).of_eq rfl rfl)
      (fun s => hm (s.setLoc x k))) (sims_runFor hb hm x n (k + 1)) (runFor_peak_le hm x n (k + 1))

/-! ### The simulation -/

theorem exec_store_some {s : State} {a : Arr} {i e : Expr} {j v : Nat} (hi : i.eval s = some j)
    (he : e.eval s = some v) (hj : j < s.cap a) :
    exec (.store a i e) s = ⟨((s.bump (i.maxv s)).bump (e.maxv s)).write a j v, 1 + i.cost +
      e.cost, .ok⟩ := by
  simp only [exec, hi, he, hj, ↓reduceIte]

/-- An allocation: a fresh region just below the heap pointer, which reads 0. -/
theorem sims_alloc {A M : Nat} {a : Nat} {n : Expr} (ha : a ≤ A) (hA : n.maxArr ≤ A) :
    Sims A M (exec (.alloc a n)) (exec (flatten (.alloc a n))) := fun s f P hR => by
  cases hn : n.eval s with
  | none => intro herr; simp [exec, hn] at herr
  | some k =>
    have xo : exec (.alloc a n) s = ⟨(s.bump (n.maxv s)).alloc a k, 1 + n.cost, .ok⟩ := by
      simp only [exec, hn]
    rw [xo]
    intro _ hpk hvol
    simp only [State.alloc, State.bump] at hpk hvol
    obtain ⟨hn', hm⟩ := flattenE_eval hR n hA k hn
    have hkm := Expr.le_maxv hn
    have := flattenE_cost n; have := Expr.cost_pos n
    have hkP : k ≤ (1 + n.cost) * P := le_trans (by omega) (Nat.le_mul_of_pos_left P (by omega))
    have hlo := hR.lo; have hhi := hR.hi
    have hc0 : 0 < f.cap 0 := by rw [hR.cap]; omega
    have hca : a + 1 < f.cap 0 := by rw [hR.cap]; omega
    have hk : k ≤ heapPtr f := by omega
    -- the first store: `heapPtr := heapPtr - n`
    have e0 : (Expr.load 0 (.lit 0)).eval f = some (heapPtr f) := by simp [Expr.eval, hc0, heapPtr]
    have ev1 : (Expr.bin .sub (.load 0 (.lit 0)) (flattenE n)).eval f = some (heapPtr f - k) := by
      change ((Expr.load 0 (.lit 0)).eval f).bind
        (fun x => ((flattenE n).eval f).bind fun y => BinOp.sub.eval x y) = _
      rw [e0, hn']; simp [BinOp.eval, hk]
    have mv1 : (Expr.bin .sub (.load 0 (.lit 0)) (flattenE n)).maxv f =
        max (max (max 0 (heapPtr f)) ((flattenE n).maxv f)) (heapPtr f - k) := by
      have m0 : (Expr.bin .sub (.load 0 (.lit 0)) (flattenE n)).maxv f =
          max (max ((Expr.load 0 (.lit 0)).maxv f) ((flattenE n).maxv f))
            (((Expr.bin .sub (.load 0 (.lit 0)) (flattenE n)).eval f).getD 0) := rfl
      have m1 : (Expr.load 0 (.lit 0)).maxv f = max 0 (((Expr.load 0 (.lit 0)).eval f).getD 0)
        := rfl
      rw [m0, m1, e0, ev1]; rfl
    have x1 := exec_store_some (a := 0) (e := Expr.bin .sub (.load 0 (.lit 0)) (flattenE n)) (s
      := f)
      (i := .lit 0) rfl ev1 hc0
    rw [mv1] at x1
    generalize hf1 : ((f.bump ((Expr.lit 0).maxv f)).bump
      (max (max (max 0 (heapPtr f)) ((flattenE n).maxv f)) (heapPtr f - k))).write 0 0 (heapPtr
        f - k) = f1 at x1
    have hm1 : f1.mem 0 = State.upd (f.mem 0) 0 (heapPtr f - k) := by
      rw [← hf1]; simp [State.write, State.bump]
    have hp1 : f1.mem 0 0 = heapPtr f - k := by rw [hm1, upd_same]
    have hc1 : f1.cap 0 = f.cap 0 := by rw [← hf1]; rfl
    have hpk1 : f1.peak = max (max f.peak 0) (max (max (max 0 (heapPtr f)) ((flattenE n).maxv
      f)) (heapPtr f - k)) := by
      rw [← hf1]; rfl
    have hl1 : f1.loc = f.loc := by rw [← hf1]; rfl
    -- the second store: `base a := heapPtr`
    have e2 : (Expr.load 0 (.lit 0)).eval f1 = some (heapPtr f - k) := by
      simp [Expr.eval, hc1, hc0, hp1]
    have x2 := exec_store_some (a := 0) (s := f1) (i := .lit (a + 1)) rfl e2 (hc1 ▸ hca)
    have mv2 : (Expr.load 0 (.lit 0)).maxv f1 = max 0 (heapPtr f - k) := by
      have m1 : (Expr.load 0 (.lit 0)).maxv f1 = max 0 (((Expr.load 0 (.lit 0)).eval f1).getD 0)
        := rfl
      rw [m1, e2]; rfl
    rw [mv2] at x2
    have xf : exec (flatten (.alloc a n)) f = (exec (.store 0 (.lit 0) (.bin .sub (.load 0 (.lit
      0)) (flattenE n))) f).bind
        (exec (.store 0 (.lit (a + 1)) (.load 0 (.lit 0)))) := rfl
    rw [xf, x1, Out.bind_ok rfl, x2]
    generalize hf2 : ((f1.bump ((Expr.lit (a + 1)).maxv f1)).bump (max 0 (heapPtr f - k))).write
      0 (a + 1)
      (heapPtr f - k) = f2
    have hfm : f2.mem 0 = State.upd (State.upd (f.mem 0) 0 (heapPtr f - k)) (a + 1) (heapPtr f -
      k) := by
      rw [← hf2, ← hm1]; simp [State.write, State.bump]
    have hp2 : heapPtr f2 = heapPtr f - k := by
      unfold heapPtr; rw [hfm, upd_other _ _ (by omega), upd_same]; rfl
    have hpk2 : f2.peak = max (max f1.peak (a + 1)) (max 0 (heapPtr f - k)) := by rw [← hf2]; rfl
    refine ⟨rfl, hR.alloc ha (by omega) rfl rfl hfm (by
      rw [← hf2]
      exact hc1.trans hR.cap)
      (by
        rw [← hf2]
        simp [State.write, State.bump, State.alloc, hl1, hR.loc]), ?_, ?_, ?_⟩
    · simp only [Expr.cost]; omega
    · change heapPtr f ≤ heapPtr f2 + (1 + n.cost) * P
      rw [hp2]; omega
    · rw [hpk2, hpk1]; simp only [State.alloc, State.bump]
      have := hR.cap; omega

/-- An evaluated expression, recorded in the peak: the first outcome of `ite`, `loop`. -/
theorem simO_expr {A M P : Nat} {s f : State} (hR : FRel A M s f) {e : Expr} (hA : e.maxArr ≤ A)
  {v : Nat}
    (hv : e.eval s = some v) :
    SimO A M P f ⟨s.bump (e.maxv s), 1 + e.cost, .ok⟩ ⟨f.bump ((flattenE e).maxv f), 1 +
      (flattenE e).cost, .ok⟩ := by
  obtain ⟨-, hm⟩ := flattenE_eval hR e hA v hv
  have := flattenE_cost e
  refine simO_ok (hR.congr rfl rfl rfl rfl hR.loc) (by omega) (by
    simp only [heapPtr, State.bump]
    omega) ?_
  simp only [State.bump]; omega

theorem flatten_sims {A M : Nat} : ∀ c : Stmt, c.maxArr ≤ A → Sims A M (exec c) (exec (flatten c))
  | .skip, _ => fun _ _ _ hR => simO_ok hR (by omega) (Nat.le_add_right _ _) (le_max_left _ _)
  | .assign x e, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    cases he : e.eval s with
    | none => intro herr; simp [exec, he] at herr
    | some v =>
      obtain ⟨he', hm⟩ := flattenE_eval hR e hA v he
      have := flattenE_cost e
      simp only [flatten, exec, he, he']
      refine simO_ok (hR.congr rfl rfl rfl rfl (by simp [State.setLoc, State.bump, hR.loc]))
        (by omega) (by
          simp only [heapPtr, State.setLoc, State.bump]
          omega) ?_
      simp only [State.setLoc, State.bump]; omega
  | .store a i e, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    cases hi : i.eval s with
    | none => intro herr; simp [exec, hi] at herr
    | some j =>
      cases he : e.eval s with
      | none => intro herr; simp [exec, hi, he] at herr
      | some v =>
        by_cases hj : j < s.cap a
        · obtain ⟨hi', mi⟩ := flattenE_eval hR i (by omega) j hi
          obtain ⟨he', me⟩ := flattenE_eval hR e (by omega) v he
          have ha := le_trans (le_max_left _ _) hA
          obtain ⟨ea, ma⟩ := addrE_eval hR ha hi'
          obtain ⟨r1, r2⟩ := hR.inR a ha j hj
          have hc : base f a + j < f.cap 0 := by rw [hR.cap]; exact r2
          have := flattenE_cost i; have := flattenE_cost e
          have hlo := hR.lo
          simp only [flatten, exec, hi, he, hj, ea, he', hc]
          refine simO_ok ?_ (by
            simp only [addrE, Expr.cost]
            omega)
            (by rw [heapPtr_write _ _ (by omega)]; exact Nat.le_add_right _ _) ?_
          · exact hR.store ha hj rfl rfl (by simp [State.write, State.bump]) hR.cap
              (by simp [State.write, State.bump, hR.loc])
          · simp only [State.write, State.bump]; rw [ma]; unfold heapPtr at *; omega
        · intro herr; simp [exec, hi, he, hj] at herr
  | .alloc a n, hA => by
    simp only [Stmt.maxArr] at hA
    exact sims_alloc (le_trans (le_max_left _ _) hA) (le_trans (le_max_right _ _) hA)
  | .seq c d, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    exact simO_bind (flatten_sims c (by omega) s f P hR) (flatten_sims d (by omega))
      (peak_le_exec d)
  | .ite e c d, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    cases he : e.eval s with
    | none => intro herr; simp [exec, he] at herr
    | some v =>
      obtain ⟨he', -⟩ := flattenE_eval hR e (by omega) v he
      simp only [flatten, exec, he, he']
      refine simO_bind (simO_expr hR (by omega) he) ?_ ?_
      · by_cases hv : v = 0
        · simp only [hv, ne_eq, not_true_eq_false, ite_false]; exact flatten_sims d (by omega)
        · simp only [hv, ne_eq, not_false_eq_true, ite_true]; exact flatten_sims c (by omega)
      · intro s; split
        · exact peak_le_exec c s
        · exact peak_le_exec d s
  | .loop x n b, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    cases hn : n.eval s with
    | none => intro herr; simp [exec, hn] at herr
    | some k =>
      obtain ⟨hn', -⟩ := flattenE_eval hR n (by omega) k hn
      simp only [flatten, exec, hn, hn']
      exact simO_bind (simO_expr hR (by omega) hn)
        (sims_runFor (flatten_sims b (by omega)) (peak_le_exec b) x k 0)
        (runFor_peak_le (peak_le_exec b) x k 0)
  | .call nm ps b rs args ds, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    cases ha : evalList s args with
    | none =>
      intro herr
      have : exec (.call nm ps b rs args ds) s = ⟨s, 1 + costList args, .err⟩ := by
        simp only [exec, ha]
      rw [this] at herr; exact absurd rfl herr
    | some vs =>
      obtain ⟨ha', hmv⟩ := flattenL_eval hR args (maxArrL_le (by omega)) vs ha
      have hcl := flattenL_cost args
      have hR1 : FRel A M ((s.bump (maxvList s args)).enter ps vs)
          ((f.bump (maxvList f (args.map flattenE))).enter ps vs) :=
        hR.congr rfl rfl rfl rfl (by simp [State.enter, State.bump])
      have ih := flatten_sims b (by omega) _ _ P hR1
      have hpe : max s.peak (maxvList s args) ≤ (exec b ((s.bump (maxvList s args)).enter ps
        vs)).st.peak :=
        peak_le_exec b ((s.bump (maxvList s args)).enter ps vs)
      simp only [flatten, exec, ha, ha']
      intro herr hpk hvol
      generalize exec b ((s.bump (maxvList s args)).enter ps vs) = o at *
      generalize exec (flatten b) ((f.bump (maxvList f (args.map flattenE))).enter ps vs) = o' at *
      have hp0 : heapPtr ((f.bump (maxvList f (args.map flattenE))).enter ps vs) = heapPtr f := rfl
      have hf0 : ((f.bump (maxvList f (args.map flattenE))).enter ps vs).peak =
          max f.peak (maxvList f (args.map flattenE)) := rfl
      cases hs : o.status with
      | ok =>
        simp only [hs] at herr hpk hvol
        have h1 := ih (by
          rw [hs]
          simp) hpk (by
          rw [hp0]
          simp only [Nat.add_mul] at hvol
          omega)
        simp only [h1.status, hs]
        have := h1.heap; have := h1.cost; have := h1.peak
        refine ⟨rfl, h1.rel.congr rfl rfl rfl rfl (by simp [State.leave, h1.rel.loc, hR.loc]),
          ?_, ?_, ?_⟩
        · simp only; omega
        · simp only [heapPtr, State.leave, Nat.add_mul] at *; omega
        · simp only [State.leave] at *; omega
      | fail =>
        simp only [hs] at herr hpk hvol
        have h1 := ih (by
          rw [hs]
          simp) hpk (by
          rw [hp0]
          simp only [Nat.add_mul] at hvol
          omega)
        simp only [h1.status, hs]
        have := h1.heap; have := h1.cost; have := h1.peak
        refine ⟨rfl, h1.rel.congr rfl rfl rfl rfl (by simp [hR.loc]), ?_, ?_, ?_⟩
        · simp only; omega
        · simp only [heapPtr, Nat.add_mul] at *; omega
        · simp only at *; omega
      | err => simp [hs] at herr
  | .fail, _ => fun _ _ _ hR => by
    intro _ _ _; exact ⟨rfl, hR, by simp [flatten, exec], by simp [flatten, exec], le_max_left _ _⟩
  | .catch c h, hA => fun s f P hR => by
    simp only [Stmt.maxArr] at hA
    have ihc := flatten_sims c (by omega) s f P hR
    simp only [flatten, exec]
    intro herr hpk hvol
    have hpc := peak_le_exec h (exec c s).st
    cases hs : (exec c s).status with
    | fail =>
      simp only [hs] at herr hpk hvol
      have h1 := ihc (by
        rw [hs]
        simp) (le_trans hpc hpk)
        (by
          simp only [Nat.add_mul] at hvol
          omega)
      simp only [h1.status, hs]
      have h2 := flatten_sims h (by omega) _ _ P h1.rel herr hpk
        (by
          have := h1.heap
          simp only [Nat.add_mul] at hvol
          omega)
      have := h1.heap; have := h1.cost; have := h1.peak; have := h2.heap; have := h2.cost; have
        := h2.peak
      refine ⟨h2.status, h2.rel, ?_, ?_, ?_⟩
      · simp only; omega
      · simp only [Nat.add_mul]; omega
      · simp only; omega
    | ok =>
      simp only [hs] at herr hpk hvol
      have h1 := ihc (by
        rw [hs]
        simp) hpk (by
        simp only [Nat.add_mul] at hvol
        omega)
      simp only [h1.status, hs]
      have := h1.heap; have := h1.cost; have := h1.peak
      refine ⟨rfl, h1.rel, ?_, ?_, ?_⟩
      · simp only; omega
      · simp only [Nat.add_mul]; omega
      · simp only; omega
    | err => simp [hs] at herr

/-- **The simulation.** Let `c` mention only arrays `≤ A`, and let the flat state `f` be related
to the original state `s` (`FRel A M`: same locals, each array `a ≤ A` stored at `base f a` in a
memory of capacity `M`, the free cells reading 0). If the run of `c` from `s` does not end in a
machine error, its peak is at most `P`, and the free part of the heap has `cost × P` cells, then
the run of `flatten c` from `f`
* ends with the same status, in a state related to the original's;
* takes at most `5 ×` the steps;
* moves the heap pointer down by at most `cost × P` cells (each allocation costs at least one
  step, and its size is a value the run computes, so at most `P`);
* computes no value above `f`'s peak, the original run's peak, or `M`. -/
theorem flatten_sim {A M : Nat} {c : Stmt} (hA : c.maxArr ≤ A) {s f : State} (hR : FRel A M s f)
  {P : Nat}
    (herr : (exec c s).status ≠ .err) (hP : (exec c s).st.peak ≤ P)
    (hmem : A + 2 + (exec c s).cost * P ≤ heapPtr f) :
    (exec (flatten c) f).status = (exec c s).status ∧ FRel A M (exec c s).st (exec (flatten c)
      f).st ∧
    (exec (flatten c) f).cost ≤ 5 * (exec c s).cost ∧
    heapPtr f ≤ heapPtr (exec (flatten c) f).st + (exec c s).cost * P ∧
    (exec (flatten c) f).st.peak ≤ max f.peak (max (exec c s).st.peak M) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := flatten_sims c hA s f P hR herr hP hmem
  exact ⟨h1, h2, h3, h4, h5⟩

/-- **The values the flat run computes** (`dpk`: its peak from a reset peak): none above the
original run's or `M`. -/
theorem flatten_dpk {A M : Nat} {c : Stmt} (hA : c.maxArr ≤ A) {s f : State} (hR : FRel A M s f)
  {P : Nat}
    (herr : (exec c s).status ≠ .err) (hP : dpk c s ≤ P) (hmem : A + 2 + (exec c s).cost * P ≤
      heapPtr f) :
    dpk (flatten c) f ≤ max (dpk c s) M := by
  obtain ⟨-, -, -, eco, est⟩ := exec_reset c s
  obtain ⟨-, -, -, -, h5⟩ := flatten_sim hA (s := {
    s with
    peak := 0
  }) (f := {
    f with
    peak := 0
  })
    (hR.congr rfl rfl rfl rfl hR.loc) (by
      rw [← est]
      exact herr) hP (by
      rw [← eco]
      exact hmem)
  exact le_trans h5 (max_le (Nat.zero_le _) (le_refl _))

end OrderMaintenance.Machine
