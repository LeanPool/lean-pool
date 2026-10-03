/-
Copyright (c) 2019 Jesse Michael Han and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han, Floris van Doorn, and Flypitch4 contributors
-/

module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Order
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.Convert

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/to_mathlib.lean -/


/-! NF weak partition development: Flypitch4.ToMathlib. -/


public section

namespace NFChoice

universe u v w w'

/-! ## Lean 3 → Lean 4 Port: Renames and Drops

### Renames (for downstream file porters, search counts in src/)

1. `imp_self` → `ba_imp_self` (renamed to avoid collision with
Lean 4 core `imp_self`)
   - Call sites: `src/henkin.lean:210`, `src/fol.lean:2097` (2
   sites)

2. `le_trans'` → `le_trans_inf` (renamed to avoid collision with
mathlib4 `ge_trans` alias and
   Lean 4 core `le_trans'` for lists)
   - Call sites: `src/bfol.lean:706`, `src/bvm.lean:64`, `:2475`,
   `:2481`,
   `src/bvm_extras.lean:2121`, `:2124` (6 sites)

3. `mk_union_le` → `mk_union_le_impl` (kept as wrapper; mathlib4
has `Cardinal.mk_union_le`)
   - Call site: `src/collapse.lean:570` — when collapse is ported,
   prefer
   `Cardinal.mk_union_le` over our wrapper

4. `nontrivial.bot_lt_top` → `nontrivial_bot_lt_top` (flattened
from sub-namespace dot notation;
   class accessor pattern changes in Lean 4)
   - Call sites: `src/bfol.lean:790`, `src/bvm.lean:1596`,
   `src/zfc.lean:519`, `:534` (4 sites)

### Drops (declarations removed because they exist in mathlib4)

1. `congr1` and `rexact` tactics (src/to_mathlib.lean:492-510)
   - `congr1` was a custom tactic used in ~10 downstream Lean 3
   proof sites
   - In Lean 4, `congr 1` (with a space) is a built-in tactic
   - When porting `fol`, `henkin`, `language_extension`, etc.,
   translate `congr1` (no space) to
   `congr 1` (with space) inline rather than re-implementing

2. `complete_degenerate_boolean_algebra`
(src/to_mathlib.lean:756)
   - Replaced by mathlib4's `PUnit.instCompleteBooleanAlgebra` in
   `Mathlib/Order/CompleteBooleanAlgebra.lean`
   - No downstream `src/` file uses this directly
-/


/-! ## function namespace

`Function.Injective.ne_iff` already exists in mathlib4. No
redeclaration needed.
-/


/-! ## dvector type and namespace -/


/-- Dependent-length vector: a list of exactly `n` elements of
type `α`. -/
inductive DVec (α : Type u) : ℕ → Type u
  | nil : DVec α 0
  | cons : ∀ {n} (_x : α) (_xs : DVec α n), DVec α (n + 1)

/-- Finite type with `n` elements, used with `DVec`. -/
inductive DFin : ℕ → Type
  | fz {n} : DFin (n + 1)
  | fs {n} : DFin n → DFin (n + 1)

instance haszeroDFin {n} : Zero (DFin (n + 1)) :=
  ⟨DFin.fz⟩

namespace DVec

variable {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

protected theorem zero_eq : ∀ (xs : DVec α 0), xs = DVec.nil
  | DVec.nil => rfl

@[simp, expose]
protected def concat : ∀ {n : ℕ}, DVec α n → α → DVec α (n + 1)
  | _, DVec.nil, x' => DVec.cons x' DVec.nil
  | _, DVec.cons x xs, x' => DVec.cons x (DVec.concat xs x')

@[simp, expose]
protected def nth : ∀ {n : ℕ}, DVec α n → (m : ℕ) → m < n → α
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons x _, 0, _ => x
  | _, DVec.cons _ xs, m + 1, h => DVec.nth xs m (Nat.lt_of_succ_lt_succ h)

protected theorem nth_cons {n : ℕ} (x : α) (xs : DVec α n) (m : ℕ) (h : m < n) :
    DVec.nth (DVec.cons x xs) (m + 1) (Nat.succ_lt_succ h) = DVec.nth xs m h :=
  rfl

@[reducible, simp, expose]
protected def last {n : ℕ} (xs : DVec α (n + 1)) : α :=
  xs.nth n (Nat.lt_succ_self n)

@[expose]
protected def nth' {n : ℕ} (xs : DVec α n) (m : Fin n) : α :=
  xs.nth m.1 m.2

@[expose]
protected def nth'' : ∀ {n : ℕ}, DVec α n → DFin n → α
  | _, DVec.cons x _, DFin.fz => x
  | _, DVec.cons _ xs, DFin.fs m => DVec.nth'' xs m

@[expose]
protected def mem : ∀ {n : ℕ}, α → DVec α n → Prop
  | _, _, DVec.nil => False
  | _, x, DVec.cons x' xs => x = x' ∨ DVec.mem x xs

instance membershipDVec {n : ℕ} : Membership α (DVec α n) :=
  ⟨fun xs a => DVec.mem a xs⟩

@[expose]
protected def pmem : ∀ {n : ℕ}, α → DVec α n → Type
  | _, _, DVec.nil => Empty
  | _, x, DVec.cons x' xs => PSum (x = x') (DVec.pmem x xs)

protected theorem mem_of_pmem : ∀ {n : ℕ} {x : α} {xs : DVec α n}, DVec.pmem x xs → x ∈ xs
  | _, _, DVec.nil, hx => hx.elim
  | _, x, DVec.cons x' xs, hx => by
    -- x ∈ DVec.cons x' xs = DVec.mem x (DVec.cons x' xs) = x = x' ∨
        -- DVec.mem x xs

    change DVec.mem x (DVec.cons x' xs)
    exact hx.casesOn (fun h => Or.inl h) (fun h => Or.inr (DVec.mem_of_pmem h))

@[simp, expose]
protected def map (f : α → β) : ∀ {n : ℕ}, DVec α n → DVec β n
  | _, DVec.nil => DVec.nil
  | _, DVec.cons x xs => DVec.cons (f x) (DVec.map f xs)

@[simp, expose]
protected def map2 (f : α → β → γ) : ∀ {n : ℕ}, DVec α n → DVec β n → DVec γ n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (f x y) (DVec.map2 f xs ys)

@[simp]
protected theorem map_id : ∀ {n : ℕ} (xs : DVec α n), DVec.map (fun x => x) xs = xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_id xs]

@[simp]
protected theorem map_congr_pmem {f g : α → β} :
    ∀ {n : ℕ} {xs : DVec α n},
      (∀ x, DVec.pmem x xs → f x = g x) → DVec.map f xs = DVec.map g xs
  | _, DVec.nil, _ => rfl
  | _, DVec.cons x xs, h => by
    simp only [DVec.map]
    congr 1
    · exact h x (PSum.inl rfl)
    · exact DVec.map_congr_pmem (fun x' hx' => h x' (PSum.inr hx'))

@[simp]
protected theorem map_congr_mem {f g : α → β} {n : ℕ} {xs : DVec α n}
    (h : ∀ x, x ∈ xs → f x = g x) : DVec.map f xs = DVec.map g xs :=
  DVec.map_congr_pmem (fun x hx => h x (DVec.mem_of_pmem hx))

@[simp]
protected theorem map_congr {f g : α → β} (h : ∀ x, f x = g x) :
    ∀ {n : ℕ} (xs : DVec α n), DVec.map f xs = DVec.map g xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, h, DVec.map_congr h xs]

@[simp]
protected theorem map_map (g : β → γ) (f : α → β) :
    ∀ {n : ℕ} (xs : DVec α n), DVec.map g (DVec.map f xs) = DVec.map (fun x => g (f x)) xs
  | _, DVec.nil => rfl
  | _, DVec.cons _ xs => by simp [DVec.map, DVec.map_map g f xs]

protected theorem map_inj {f : α → β} (hf : ∀ {x x'}, f x = f x' → x = x') {n : ℕ}
    {xs xs' : DVec α n} (h : DVec.map f xs = DVec.map f xs') : xs = xs' := by
  induction xs with
  | nil => exact (DVec.zero_eq xs').symm
  | cons x xs ih =>
    cases xs' with
    | cons x' xs' =>
      simp only [DVec.map] at h
      congr 1
      · exact hf (DVec.cons.inj h).1
      · exact ih (DVec.cons.inj h).2

@[simp]
protected theorem map_concat (f : α → β) :
    ∀ {n : ℕ} (xs : DVec α n) (x : α),
      DVec.map f (DVec.concat xs x) = DVec.concat (DVec.map f xs) (f x)
  | _, DVec.nil, _ => rfl
  | _, DVec.cons _ xs, x' => by simp [DVec.map, DVec.concat, DVec.map_concat f xs x']

@[simp]
protected theorem map_nth (f : α → β) :
    ∀ {n : ℕ} (xs : DVec α n) (m : ℕ) (h : m < n),
      DVec.nth (DVec.map f xs) m h = f (DVec.nth xs m h)
  | _, DVec.nil, m, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons _ _, 0, _ => rfl
  | _, DVec.cons _ xs, m + 1, _h => DVec.map_nth f xs m _

protected theorem concat_nth :
    ∀ {n : ℕ} (xs : DVec α n) (x : α) (m : ℕ) (h' : m < n + 1) (h : m < n),
      DVec.nth (DVec.concat xs x) m h' = DVec.nth xs m h
  | _, DVec.nil, _, m, _, h => absurd h (Nat.not_lt_zero m)
  | _, DVec.cons _ _, _, 0, _, _ => rfl
  | _, DVec.cons _ xs, x', m + 1, h', h =>
    by
    simp only [DVec.concat, DVec.nth]
    exact DVec.concat_nth xs x' m _ _

@[simp]
protected theorem concat_nth_last :
    ∀ {n : ℕ} (xs : DVec α n) (x : α) (h : n < n + 1), DVec.nth (DVec.concat xs x) n h = x
  | _, DVec.nil, _, _ => rfl
  | _, DVec.cons _ xs, x', h => by
    simp [DVec.concat, DVec.nth, DVec.concat_nth_last xs x']

@[simp]
protected theorem concat_nth_last' :
    ∀ {n : ℕ} (xs : DVec α n) (x : α) (_h : n < n + 1),
      DVec.last (DVec.concat xs x) = x :=
  DVec.concat_nth_last

@[simp, expose]
protected def append : ∀ {n m : ℕ}, DVec α n → DVec α m → DVec α (m + n)
  | _, _, DVec.nil, xs => xs
  | _, _, DVec.cons x' xs, xs' => DVec.cons x' (DVec.append xs xs')

@[simp, expose]
protected def insert : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α (n + 1)
  | _n, x, 0, xs => DVec.cons x xs
  | 0, x, _, _ => DVec.cons x DVec.nil
  | _n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.insert x k ys)

@[simp]
protected theorem insert_at_zero :
    ∀ {n : ℕ} (x : α) (xs : DVec α n), DVec.insert x 0 xs = DVec.cons x xs := by
  intro n;
  cases n <;> intros <;> rfl

@[simp]
protected theorem insert_nth :
    ∀ {n : ℕ} (x : α) (k : ℕ) (xs : DVec α n) (h : k < n + 1),
      DVec.nth (DVec.insert x k xs) k h = x
  | 0, x, 0, _, _ => rfl
  | 0, x, k + 1, _, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | n + 1, x, 0, _, _ => by simp [DVec.insert, DVec.nth]
  | n + 1, x, k + 1, DVec.cons _ ys, h =>
    by
    simp only [DVec.insert, DVec.nth]
    exact DVec.insert_nth x k ys _

protected theorem insert_cons {n k} {x y : α} {v : DVec α n} :
    DVec.cons x (DVec.insert y k v) = DVec.insert y (k + 1) (DVec.cons x v) := by
  induction v with
  | nil => rfl
  | cons _ _ _ => simp [DVec.insert]

/-- The n-th initial segment of a vector, given a proof that n ≤
m. -/
@[simp, expose]
protected def trunc : ∀ (n) {m : ℕ}, n ≤ m → DVec α m → DVec α n
  | 0, 0, _, _ => DVec.nil
  | 0, _ + 1, _, _ => DVec.nil
  | n + 1, 0, h, _ => absurd h (Nat.not_succ_le_zero n)
  | n + 1, _m + 1, h, DVec.cons x xs =>
    DVec.cons x (DVec.trunc n (Nat.lt_succ_iff.mp (Nat.lt_of_succ_le h)) xs)

@[simp]
protected theorem trunc_n_n {n : ℕ} {h : n ≤ n} {v : DVec α n} : DVec.trunc n h v = v :=
  by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [DVec.trunc, ih]

@[simp]
protected theorem trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : DVec α n} :
    DVec.trunc 0 h v = DVec.nil := by cases v <;> rfl

@[simp]
protected theorem trunc_nth {n m l : ℕ} {h : n ≤ m} {h' : l < n} {v : DVec α m} :
    DVec.nth (DVec.trunc n h v) l h' = DVec.nth v l (Nat.lt_of_lt_of_le h' h) := by
  induction m generalizing n l with
  | zero =>
    have : n = 0 := Nat.eq_zero_of_le_zero h
    subst this; exact absurd h' (Nat.not_lt_zero _)
  | succ m ih =>
    cases n with
    | zero => exact absurd h' (Nat.not_lt_zero _)
    | succ n =>
      cases l with
      | zero =>
        cases v with
        | cons _ _ => rfl
      | succ l =>
        cases v with
        | cons _ vs =>
          change DVec.nth (DVec.trunc n _ vs) l _ = DVec.nth vs l _
          apply ih

protected theorem nth_irrel1 {n k : ℕ} {h : k < n + 1} {h' : k < n + 1 + 1}
    (v : DVec α (n + 1)) (x : α) :
    DVec.nth (DVec.cons x (DVec.trunc n (Nat.le_succ n) v)) k h =
      DVec.nth (DVec.cons x v) k h' :=
  by
  cases k with
  | zero => rfl
  | succ k =>
    change DVec.nth (DVec.trunc n _ v) k _ = DVec.nth v k _
    rw [DVec.trunc_nth]

@[expose]
protected def cast {n m} (p : n = m) (v : DVec α n) : DVec α m :=
  p ▸ v

@[simp]
protected theorem cast_irrel {n m} {p p' : n = m} {v : DVec α n} :
    DVec.cast p v = DVec.cast p' v :=
  rfl

@[simp]
protected theorem cast_rfl {n m} {p : n = m} {q : m = n} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = v := by subst p; rfl

protected theorem cast_hrfl {n m} {p : n = m} {v : DVec α n} : HEq (DVec.cast p v) v := by
  subst p; rfl

@[simp]
protected theorem cast_trans {n m o} {p : n = m} {q : m = o} {v : DVec α n} :
    DVec.cast q (DVec.cast p v) = DVec.cast (p.trans q) v := by subst p; subst q; rfl

@[simp]
theorem cast_cons {n m} (h : n + 1 = m + 1) (x : α) (v : DVec α n) :
    DVec.cast h (DVec.cons x v) = DVec.cons x (DVec.cast (Nat.succ_injective h) v) := by
  cases h; rfl

@[simp]
theorem cast_append_nil :
    ∀ {n} (v : DVec α n) (h : 0 + n = n), DVec.cast h (DVec.append v DVec.nil) = v
  | _, DVec.nil, _ => rfl
  | _, DVec.cons x v, h => by
    simp only [DVec.append, cast_cons]
    congr 1
    exact cast_append_nil v (by omega)

@[simp, expose]
protected def remove_mth : ∀ {n : ℕ}, ℕ → DVec α (n + 1) → DVec α n
  | 0, _, _ => DVec.nil
  | _n, 0, DVec.cons _ ys => ys
  | n + 1, k + 1, DVec.cons y ys => DVec.cons y (DVec.remove_mth k ys)

@[simp, expose]
protected def replace : ∀ {n : ℕ}, α → ℕ → DVec α n → DVec α n
  | _, x, 0, DVec.cons _ ys => DVec.cons x ys
  | 0, _, _, ys => ys
  | _n + 1, x, k + 1, DVec.cons y ys => DVec.cons y (DVec.replace x k ys)

protected theorem insert_nth_lt {n k l : ℕ} (x : α) (xs : DVec α n) (h : l < n)
    (h' : l < n + 1) (h2 : l < k) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs l h := by
  induction xs generalizing k l with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons x' xs ih =>
    cases k with
    | zero => exact absurd h2 (Nat.not_lt_zero _)
    | succ k =>
      cases l with
      | zero => rfl
      | succ l =>
        simp only [DVec.insert, DVec.nth]
        exact
          ih (Nat.lt_of_succ_lt_succ h) (Nat.lt_of_succ_lt_succ h')
            (Nat.lt_of_succ_lt_succ h2)

protected theorem insert_nth_gt' {n k l : ℕ} (x : α) (xs : DVec α n) (h : l - 1 < n)
    (h' : l < n + 1) (h2 : k < l) :
    DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) h := by
  induction xs generalizing k l with
  | nil =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h (Nat.not_lt_zero _)
      | succ l => exact absurd h' (by omega)
  | cons x' xs ih =>
    cases k with
    | zero =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l => simp [DVec.insert, DVec.nth]
    | succ k =>
      cases l with
      | zero => exact absurd h2 (Nat.not_lt_zero _)
      | succ l =>
        cases l with
        | zero => exact absurd h2 (by omega)
        | succ l =>
          simp only [DVec.insert, DVec.nth, Nat.add_one_sub_one]
          have :=
            ih (k := k) (l := l + 1) (by omega) (Nat.lt_of_succ_lt_succ h') (by omega)
          simp only [Nat.add_one_sub_one] at this ⊢
          exact this

@[simp]
protected theorem insert_nth_gt_simp {n k l : ℕ} (x : α) (xs : DVec α n) (h' : l < n + 1)
    (h2 : k < l) : DVec.nth (DVec.insert x k xs) l h' = DVec.nth xs (l - 1) (by omega) :=
  DVec.insert_nth_gt' x xs (by omega) h' h2

protected theorem insert_nth_gt {n k l : ℕ} (x : α) (xs : DVec α n) (h : l < n)
    (h' : l + 1 < n + 1) (h2 : k < l + 1) :
    DVec.nth (DVec.insert x k xs) (l + 1) h' = DVec.nth xs l h :=
  DVec.insert_nth_gt' x xs h h' h2

@[simp]
lemma replace_head {n x z} {xs : DVec α n} :
    DVec.replace z 0 (DVec.cons x xs) = DVec.cons z xs :=
  rfl

@[simp]
lemma replace_neck {n x y z} {xs : DVec α n} :
    DVec.replace z 1 (DVec.cons x (DVec.cons y xs)) = DVec.cons x (DVec.cons z xs) :=
  rfl

@[simp, expose]
def foldr (f : α → β → β) (b : β) : ∀ {n}, DVec α n → β
  | _, DVec.nil => b
  | _, DVec.cons a l => f a (DVec.foldr f b l)

@[simp, expose]
def zip : ∀ {n}, DVec α n → DVec β n → DVec (α × β) n
  | _, DVec.nil, DVec.nil => DVec.nil
  | _, DVec.cons x xs, DVec.cons y ys => DVec.cons (x, y) (DVec.zip xs ys)

/-- The finitary infimum -/
@[expose]
def fInf [SemilatticeInf α] [OrderTop α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊓ b) ⊤ xs

@[simp]
lemma fInf_nil [SemilatticeInf α] [OrderTop α] : fInf (DVec.nil (α := α)) = ⊤ :=
  rfl

@[simp]
lemma fInf_cons [SemilatticeInf α] [OrderTop α] (x : α) (xs : DVec α n) :
    fInf (DVec.cons x xs) = x ⊓ fInf xs :=
  rfl

/-- The finitary supremum -/
@[expose]
def fSup [SemilatticeSup α] [OrderBot α] (xs : DVec α n) : α :=
  DVec.foldr (fun (x b : α) => x ⊔ b) ⊥ xs

@[simp]
lemma fSup_nil [SemilatticeSup α] [OrderBot α] : fSup (DVec.nil (α := α)) = ⊥ :=
  rfl

@[simp]
lemma fSup_cons [SemilatticeSup α] [OrderBot α] (x : α) (xs : DVec α n) :
    fSup (DVec.cons x xs) = x ⊔ fSup xs :=
  rfl

/-- Pointwise relation on DVec, given a setoid on the element
type -/
inductive DVecRel {α : Type u} [Setoid α] : ∀ {n : ℕ}, DVec α n → DVec α n → Prop
  | rnil : DVecRel DVec.nil DVec.nil
  |
  rcons {x x' : α} {n : ℕ} {xs xs' : DVec α n} (hx : x ≈ x') (hxs : DVecRel xs xs') :
    DVecRel (DVec.cons x xs) (DVec.cons x' xs')

protected theorem rel_refl {α : Type u} [Setoid α] {n} (xs : DVec α n) : DVecRel xs xs :=
  by
  induction xs with
  | nil => exact DVecRel.rnil
  | cons _ _ ih => exact DVecRel.rcons (Setoid.refl _) ih

protected theorem rel_symm {α : Type u} [Setoid α] {n} {xs xs' : DVec α n}
    (h : DVecRel xs xs') : DVecRel xs' xs := by
  induction h with
  | rnil => exact DVecRel.rnil
  | rcons hx _ ih => exact DVecRel.rcons (Setoid.symm hx) ih

protected theorem rel_trans {α : Type u} [Setoid α] {n} {xs₁ xs₂ xs₃ : DVec α n}
    (h₁ : DVecRel xs₁ xs₂) (h₂ : DVecRel xs₂ xs₃) : DVecRel xs₁ xs₃ := by
  induction h₁ with
  | rnil => exact h₂
  | rcons hx _ ih =>
    cases h₂ with
    | rcons hx₂ hxs₂ => exact DVecRel.rcons (Setoid.trans hx hx₂) (ih hxs₂)

instance setoidInst {α : Type u} [Setoid α] {n : ℕ} : Setoid (DVec α n) :=
  ⟨DVecRel, DVec.rel_refl, DVec.rel_symm, DVec.rel_trans⟩

@[expose]
noncomputable def quotient_lift {α : Type u} {β : Sort v} {R : Setoid α} :
    ∀ {n} (f : DVec α n → β) (_h : ∀ {xs xs' : DVec α n}, xs ≈ xs' → f xs = f xs')
      (_qs : DVec (Quotient R) n), β
  | 0, f, _, DVec.nil => f DVec.nil
  | n + 1, f, h, DVec.cons q qs =>
    Quotient.lift
      (fun x => DVec.quotient_lift (fun xs => f (DVec.cons x xs))
          (fun hxs => h (DVecRel.rcons (Setoid.refl x) hxs)) qs)
      (fun x x' hx => by
        congr 1; apply funext; intro xs
        apply h; exact DVecRel.rcons hx (DVec.rel_refl xs))
      q

theorem quotient_beta {α : Type u} {β : Sort v} {R : Setoid α} :
    ∀ {n} (f : DVec α n → β) (h : ∀ {xs xs' : DVec α n}, xs ≈ xs' → f xs = f xs')
      (xs : DVec α n), DVec.quotient_lift f h (DVec.map Quotient.mk'' xs) = f xs
  | 0, f, h, DVec.nil => rfl
  | n + 1, f, h, DVec.cons x xs =>
    by
    simp only [DVec.map, DVec.quotient_lift, Quotient.lift_mk]
    exact
      quotient_beta (fun xs' => f (DVec.cons x xs'))
        (fun hxs => h (DVecRel.rcons (Setoid.refl x) hxs)) xs

end DVec

/-! ## set namespace -/


namespace Set

open _root_.Set

theorem disjoint_iff_eq_empty {α} {s t : Set α} : Disjoint s t ↔ s ∩ t = ∅ := by
  rw [Set.disjoint_iff_inter_eq_empty]

@[simp]
theorem not_nonempty_iff {α} {s : Set α} : ¬Nonempty s ↔ s = ∅ := by
  rw [Set.nonempty_coe_sort, Set.not_nonempty_iff_eq_empty]

theorem neq_neg_of_nonempty {α : Type*} {P : Set α} (H_nonempty : Nonempty α) : P ≠ Pᶜ :=
  by
  intro H_eq
  obtain ⟨a⟩ := H_nonempty
  by_cases HP : a ∈ P
  · -- a ∈ P, so by H_eq, a ∈ Pᶜ, i.e., a ∉ P — contradiction

    have : a ∈ Pᶜ := H_eq ▸ HP
    exact this HP
  · -- a ∉ P, so a ∈ Pᶜ, so by H_eq, a ∈ P — contradiction

    have : a ∈ Pᶜ := HP
    rw [← H_eq] at this
    exact HP this

@[simp]
theorem subset_biInter_iff {α β} {s : Set α} {t : Set β} {u : α → Set β} :
    t ⊆ ⋂ x ∈ s, u x ↔ ∀ x ∈ s, t ⊆ u x :=
  Set.subset_iInter₂_iff

-- subset_sInter_iff is already in Mathlib as
-- Set.subset_sInter_iff

theorem ne_empty_of_subset {α} {s t : Set α} (h : s ⊆ t) (hs : s ≠ ∅) : t ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp ((Set.nonempty_iff_ne_empty.mpr hs).mono h)

end Set

/-! ## nat namespace -/


namespace Nat

open _root_.Nat

protected theorem pred_lt_iff_lt_succ {m n : ℕ} (H : 1 ≤ m) :
    Nat.pred m < n ↔ m < Nat.succ n :=
  by
  simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one]
  omega

@[simp]
theorem le_of_le_and_ne_succ {x y : ℕ} (H : x ≤ y + 1) (H' : x ≠ y + 1) : x ≤ y :=
  Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne H H')

end Nat

/-! ## classical namespace (logic helpers) -/


namespace Classical

open _root_.Classical

@[expose]
noncomputable def psigma_of_exists {α : Type u} {p : α → Prop} (h : ∃ x, p x) :
    Σ' x, p x :=
  ⟨Classical.choose h, Classical.choose_spec h⟩

theorem some_eq {α : Type u} {p : α → Prop} {h : ∃ (a : α), p a} (x : α)
    (hx : ∀ y, p y → y = x) : Classical.choose h = x :=
  hx _ (Classical.choose_spec h)

theorem or_not_iff_true (p : Prop) : (p ∨ ¬p) ↔ True :=
  ⟨fun _ => trivial, fun _ => Classical.em p⟩

theorem nonempty_of_not_empty {α : Type u} (s : Set α) (h : ¬s = ∅) : Nonempty s :=
  Set.Nonempty.coe_sort (Set.nonempty_iff_ne_empty.mpr h)

theorem nonempty_of_not_empty_finset {α : Type u} (s : Finset α) (h : ¬s = ∅) :
    Nonempty (s : Set α) :=
  Set.Nonempty.coe_sort (Finset.nonempty_iff_ne_empty.mpr h)

end Classical

/-! ## list namespace -/


namespace List

open _root_.List

@[simp, expose]
protected def toSet {α : Type u} (l : List α) : Set α :=
  {x | x ∈ l}

theorem toSet_map {α : Type u} {β : Type v} (f : α → β) (l : List α) :
    NFChoice.List.toSet (l.map f) = f '' NFChoice.List.toSet l := by
  apply Set.ext;
  intro b; simp [List.toSet, Set.mem_image]

theorem exists_of_toSet_subset_image {α : Type u} {β : Type v} {f : α → β} {l : List β}
    {t : Set α} (h : NFChoice.List.toSet l ⊆ f '' t) :
    ∃ (l' : List α), NFChoice.List.toSet l' ⊆ t ∧ l'.map f = l := by
  induction l with
  | nil => exact ⟨[], by simp [List.toSet], rfl⟩
  | cons hd tl ih =>
    have h_hd : hd ∈ f '' t := h (by simp [List.toSet])
    obtain ⟨x, hx, rfl⟩ := h_hd
    have h_tl : ∀ y ∈ NFChoice.List.toSet tl, y ∈ f '' t := fun y hy =>
      h (by
          simp only [List.toSet, Set.mem_ofPred_eq, List.mem_cons]
          exact Or.inr (hy))
    obtain ⟨xs, hxs, hxs'⟩ := ih (fun y hy => h_tl y hy)
    exact
      ⟨x :: xs, fun y hy =>
        by
        simp only [List.toSet, mem_cons, Set.mem_ofPred_eq] at hy
        cases hy with
        | inl h => exact h ▸ hx
        | inr h => exact hxs h,
        by simp [hxs']⟩

end List

/-! ## additional nat lemmas -/


namespace Nat

open _root_.Nat

theorem add_sub_swap {n k : ℕ} (h : k ≤ n) (m : ℕ) : n + m - k = n - k + m := by omega

end Nat

/-! ## misc prop lemmas -/


theorem imp_eq_congr {a b c d : Prop} (h₁ : a = b) (h₂ : c = d) : (a → c) = (b → d) := by
  subst h₁; subst h₂; rfl

theorem forall_eq_congr {α : Sort u} {p q : α → Prop} (h : ∀ a, p a = q a) :
    (∀ a, p a) = ∀ a, q a := by have h' : p = q := funext h; subst h'; rfl

/-! ## additional set lemmas -/


namespace Set

open _root_.Set

variable {α : Type u} {β : Type v} {γ : Type w}

theorem ne_empty_of_exists_mem {s : Set α} : ∀ (_ : ∃ x, x ∈ s), s ≠ ∅
  | ⟨x, hx⟩ => Set.nonempty_iff_ne_empty.mp ⟨x, hx⟩

theorem inter_sUnion_ne_empty_of_exists_mem {b : Set α} {𝓕 : Set (Set α)}
    (H : ∃ f ∈ 𝓕, b ∩ f ≠ ∅) : b ∩ ⋃₀ 𝓕 ≠ ∅ :=
  by
  apply ne_empty_of_exists_mem
  obtain ⟨f, hf, h⟩ := H
  rw [ne_eq, ← Set.not_nonempty_iff_eq_empty, not_not] at h
  obtain ⟨x, hx1, hx2⟩ := h
  exact ⟨x, hx1, Set.mem_sUnion.mpr ⟨f, hf, hx2⟩⟩

@[simp]
theorem mem_image_univ {f : α → β} {x} : f x ∈ f '' Set.univ :=
  ⟨x, Set.mem_univ x, rfl⟩

theorem image_preimage_eq_of_subset_image {f : α → β} {s : Set β} {t : Set α}
    (h : s ⊆ f '' t) : f '' (f ⁻¹' s) = s :=
  Set.Subset.antisymm (Set.image_preimage_subset f s)
    (fun x hx => by obtain ⟨a, ha, rfl⟩ := h hx; exact Set.mem_image_of_mem f hx)

theorem subset_union_left_of_subset {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  h.trans Set.subset_union_left

theorem subset_union_right_of_subset {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  h.trans Set.subset_union_right

theorem subset_sUnion {s : Set α} {t : Set (Set α)} (h : s ∈ t) : s ⊆ ⋃₀ t :=
  Set.subset_sUnion_of_mem h

theorem subset_union2_left {s t u : Set α} : s ⊆ s ∪ t ∪ u :=
  Set.subset_union_left.trans Set.subset_union_left

theorem subset_union2_middle {s t u : Set α} : t ⊆ s ∪ t ∪ u :=
  Set.subset_union_right.trans Set.subset_union_left

@[expose]
def change {π : α → Type*} [DecidableEq α] (f : ∀ a, π a) {x : α} (z : π x) (y : α) :
    π y :=
  if h : x = y then h ▸ z else f y

theorem dif_mem_pi {π : α → Type*} (i : Set α) (s : ∀ a, Set (π a)) [DecidableEq α]
    (f : ∀ a, π a) (hf : f ∈ Set.pi i s) {x : α} (z : π x) (h : x ∈ i → z ∈ s x) :
    Set.change f z ∈ Set.pi i s := by
  intro y hy
  simp only [Set.change]
  by_cases hxy : x = y
  · rw [dite_eq_left hxy]; subst hxy; exact h hy
  · rw [dite_eq_right hxy]; exact hf y hy

theorem image_pi_pos {π : α → Type*} (i : Set α) (s : ∀ a, Set (π a))
    (hp : (Set.pi i s).Nonempty) (x : α) (hx : x ∈ i) :
    (fun (f : ∀ a, π a) => f x) '' Set.pi i s = s x := by
  classical
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩; exact hf x hx
  · intro z hz
    obtain ⟨f, hf⟩ := hp
    exact ⟨Set.change f z, Set.dif_mem_pi i s f hf z (fun _ => hz), by simp [Set.change]⟩

theorem image_pi_neg {π : α → Type*} (i : Set α) (s : ∀ a, Set (π a))
    (hp : (Set.pi i s).Nonempty) (x : α) (hx : x ∉ i) :
    (fun (f : ∀ a, π a) => f x) '' Set.pi i s = Set.univ := by
  classical
  rw [Set.eq_univ_iff_forall]
  intro z
  obtain ⟨f, hf⟩ := hp
  exact
    ⟨Set.change f z, Set.dif_mem_pi i s f hf z (fun hxi => absurd hxi hx), by
      simp [Set.change]⟩

end Set

/-! ## nonempty namespace -/


namespace Nonempty

open _root_.Nonempty

variable {α : Sort u} {β : Sort v}

protected theorem iff (mp : α → β) (mpr : β → α) : Nonempty α ↔ Nonempty β :=
  ⟨Nonempty.map mp, Nonempty.map mpr⟩

end Nonempty

/-! ## arity' type and namespace -/


/-- The type α → (α → ... (α → β)...) with n α's. -/
@[expose]
def Arity' (α β : Type u) : ℕ → Type u
  | 0 => β
  | n + 1 => α → Arity' α β n

namespace Arity'

@[expose]
def arity'_constant {α β : Type u} : ∀ {n : ℕ}, β → Arity' α β n
  | 0, b => b
  | _ + 1, b => fun _ => arity'_constant b

@[simp, expose]
def of_dvector_map {α β : Type u} : ∀ {l} (_f : DVec α l → β), Arity' α β l
  | 0, f => f DVec.nil
  | _l + 1, f => fun x => of_dvector_map (fun xs => f (DVec.cons x xs))

@[simp, expose]
def arity'_app {α β : Type u} : ∀ {l}, Arity' α β l → DVec α l → β
  | _, b, DVec.nil => b
  | _, f, DVec.cons x xs => arity'_app (f x) xs

@[simp]
theorem arity'_app_zero {α β : Type u} (f : Arity' α β 0) (xs : DVec α 0) :
    arity'_app f xs = f := by cases xs; rfl

@[expose]
def arity'_postcompose {α β γ : Type u} (g : β → γ) :
    ∀ {n} (_f : Arity' α β n), Arity' α γ n
  | 0, b => g b
  | _n + 1, f => fun x => arity'_postcompose g (f x)

@[expose]
def arity'_postcompose2 {α β γ δ : Type u} (h : β → γ → δ) :
    ∀ {n} (_f : Arity' α β n) (_g : Arity' α γ n), Arity' α δ n
  | 0, b, c => h b c
  | _n + 1, f, g => fun x => arity'_postcompose2 h (f x) (g x)

@[expose]
def arity'_precompose {α β γ : Type u} :
    ∀ {n} (_g : Arity' β γ n) (_f : α → β), Arity' α γ n
  | 0, c, _ => c
  | _n + 1, g, f => fun x => arity'_precompose (g (f x)) f

inductive arity'_respect_setoid {α β : Type u} [R : Setoid α] :
    ∀ {n}, Arity' α β n → Type u
  | r_zero (b : β) : @arity'_respect_setoid _ _ _ 0 b
  |
  r_succ (n : ℕ) (f : Arity' α β (n + 1)) (h₁ : ∀ {a a'}, a ≈ a' → f a = f a')
    (h₂ : ∀ a, arity'_respect_setoid (f a)) : arity'_respect_setoid f

instance subsingleton_arity'_respect_setoid {α β : Type u} [R : Setoid α] {n}
    (f : Arity' α β n) : Subsingleton (arity'_respect_setoid f) :=
  by
  constructor
  intro h h'
  induction h with
  | r_zero => cases h'; rfl
  | r_succ n f _ _ ih =>
    cases h' with
    | r_succ => congr; funext x; exact ih x _

@[expose]
def for_all {α : Type u} (P : α → Prop) : Prop :=
  ∀ x, P x

@[simp, expose]
def arity'_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) :
    ∀ {n}, Arity' α β n → Arity' α β n → β
  | 0, x, y => f x y
  | _n + 1, x, y => q (fun z => arity'_map2 q f (x z) (y z))

@[simp]
theorem arity'_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ∀ A, f A A) :
    ∀ {n} (x : Arity' α Prop n), arity'_map2 for_all f x x
  | 0, x => r x
  | _n + 1, x => fun y => arity'_map2_refl r (x y)

@[expose]
def arity'_imp {α : Type} {n : ℕ} (f₁ f₂ : Arity' α Prop n) : Prop :=
  arity'_map2 for_all (fun P Q => P → Q) f₁ f₂

@[expose]
def arity'_iff {α : Type} {n : ℕ} (f₁ f₂ : Arity' α Prop n) : Prop :=
  arity'_map2 for_all Iff f₁ f₂

theorem arity'_iff_refl {α : Type} {n : ℕ} (f : Arity' α Prop n) : arity'_iff f f :=
  arity'_map2_refl Iff.refl f

theorem arity'_iff_rfl {α : Type} {n : ℕ} {f : Arity' α Prop n} : arity'_iff f f :=
  arity'_iff_refl f

end Arity'

/-! ## Miscellaneous lemmas -/


@[simp]
theorem lt_irrefl' {α} [Preorder α] {Γ : α} (H_lt : Γ < Γ) : False :=
  lt_irrefl _ H_lt

end NFChoice
