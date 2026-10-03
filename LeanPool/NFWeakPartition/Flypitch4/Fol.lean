/-
Copyright (c) 2019 Jesse Michael Han and Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Michael Han, Floris van Doorn, and Flypitch4 contributors
-/

module

/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file
LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
/- Lean 4 port of src/fol.lean (lines 23-508): Language, preterm,
term-level material. -/

public import LeanPool.NFWeakPartition.Flypitch4.ToMathlib

/-! NF weak partition development: Flypitch4.Fol. -/


public section

namespace NFChoice

universe u v

namespace Fol

/-! ## Valuation helpers (subst_realize) -/


/-- Given a valuation v, a nat n, and an x : S, return v
truncated to its first n values,
    with the rest of the values replaced by x. -/
@[expose]
def subst_realize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
  if k < n then v k else if n < k then v (k - 1) else x

@[simp]
lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) :
    Fol.subst_realize v x n k = v k := by simp only [subst_realize, H, ite_true]

@[simp]
lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) :
    Fol.subst_realize v x n k = v (k - 1) :=
  by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [subst_realize, h, ite_false, H, ite_true]

@[simp]
lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) :
    Fol.subst_realize v x n n = x := by simp only [subst_realize, lt_irrefl, ite_false]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀ k, v k = v' k) (x : S)
    (n k : ℕ) : Fol.subst_realize v x n k = Fol.subst_realize v' x n k :=
  by
  rcases Nat.lt_trichotomy k n with h | h | h
  · simp [subst_realize, h, hv k]
  · subst h; simp [subst_realize]
  · simp [subst_realize, Nat.lt_asymm h, h, hv (k - 1)]

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
    Fol.subst_realize (Fol.subst_realize v x' (n₁ + n₂)) x n₁ k =
      Fol.subst_realize (Fol.subst_realize v x n₁) x' (n₁ + n₂ + 1) k :=
  by
  simp only [subst_realize]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all [] <;> omega

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
    Fol.subst_realize (Fol.subst_realize v x' n) x 0 k =
      Fol.subst_realize (Fol.subst_realize v x 0) x' (n + 1) k :=
  by
  have h := subst_realize2 v x x' 0 n k
  simp only [Nat.zero_add] at h
  exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ}
    (hv : ∀ k, k < n → v₁ k = v₂ k) (x : S) {k : ℕ} (hk : k < n + 1) :
    Fol.subst_realize v₁ x 0 k = Fol.subst_realize v₂ x 0 k := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [subst_realize, h, hv k (Nat.lt_of_succ_lt_succ hk)]

lemma lift_subst_realize_cancel {S : Type u} (v : ℕ → S) (k : ℕ) :
    Fol.subst_realize (fun n => v (n + 1)) (v 0) 0 k = v k := by
  cases k with
  | zero => simp [subst_realize]
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [subst_realize, h]

lemma subst_fin_realize_eq {S : Type u} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) (x : S) (k : ℕ) (hk : k < n + 1) :
    (DVec.cons x v₁).nth k hk = Fol.subst_realize v₂ x 0 k := by
  cases k with
  | zero => simp [DVec.nth, subst_realize]
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp only [DVec.nth, subst_realize, h, ite_true, Nat.add_sub_cancel]
    exact hv k (Nat.lt_of_succ_lt_succ hk)

/-! ## Language -/


structure Language : Type (u + 1) where
  functions : ℕ → Type u
  relations : ℕ → Type u

@[expose]
def Language.constants (L : Language.{u}) :=
  L.functions 0

variable (L : Language.{u})

/-! ## preterm and term -/


/-- `preterm L l` is a partially applied term. If applied to `l`
terms, it becomes a term (l=0).
    We use de Bruijn variables. -/
inductive preterm : ℕ → Type u
  | var : ∀ (_k : ℕ), preterm 0
  | func : ∀ {l : ℕ} (_f : L.functions l), preterm l
  | app : ∀ {l : ℕ} (_t : preterm (l + 1)) (_s : preterm 0), preterm l

@[reducible, expose]
def term :=
  preterm L 0

variable {L}

prefix:max "&" => Fol.preterm.var

@[simp, expose]
def apps : ∀ {l}, preterm L l → DVec (term L) l → term L
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => apps (preterm.app t t') ts

@[simp]
lemma apps_zero (t : term L) (ts : DVec (term L) 0) : apps t ts = t := by cases ts; rfl

lemma apps_eq_app {l} (t : preterm L (l + 1)) (s : term L) (ts : DVec (term L) l) :
    ∃ t' s', apps t (DVec.cons s ts) = preterm.app t' s' := by
  induction ts generalizing s with
  | nil => exact ⟨t, s, rfl⟩
  | cons t' ts ih => exact ih (preterm.app t s) t'

namespace preterm

@[simp, expose]
def change_arity' : ∀ {l l'} (_ : l = l') (_t : preterm L l), preterm L l'
  | _, _, h, var k => by subst h; exact var k
  | _, _, h, func f => func (by subst h; exact f)
  | _, _, h, app t₁ t₂ => app (change_arity' (by omega) t₁) t₂

@[simp]
lemma change_arity'_rfl : ∀ {l} (t : preterm L l), change_arity' rfl t = t
  | _, var _ => rfl
  | _, func _ => rfl
  | _, app t₁ _ => by simp [change_arity'_rfl t₁]

end preterm

lemma apps_ne_var {l} {f : L.functions l} {ts : DVec (term L) l} {k : ℕ} :
    apps (preterm.func f) ts ≠ &k := by
  intro h
  cases ts with
  | nil =>
    simp only [apps] at h
    exact absurd h (fun h => by cases h)
  | cons ts_x
    ts_xs =>
    rcases apps_eq_app (preterm.func f) ts_x ts_xs with ⟨_, _, h'⟩
    rw [h'] at h
    exact absurd h (fun h => by cases h)

lemma apps_inj' {l} {t t' : preterm L l} {ts ts' : DVec (term L) l}
    (h : apps t ts = apps t' ts') : t = t' ∧ ts = ts' := by
  induction ts with
  | nil =>
    cases ts'
    exact ⟨h, rfl⟩
  | cons x xs ih =>
    cases ts' with
    | cons x' xs' =>
      simp only [apps] at h
      obtain ⟨heq, hts⟩ := ih h
      obtain ⟨ht, hx⟩ := preterm.app.inj heq
      exact ⟨ht, by rw [hx, hts]⟩

lemma apps_inj {l} {f f' : L.functions l} {ts ts' : DVec (term L) l}
    (h : apps (preterm.func f) ts = apps (preterm.func f') ts') : f = f' ∧ ts = ts' :=
  by
  rcases apps_inj' h with ⟨h', rfl⟩
  cases h'
  exact ⟨rfl, rfl⟩

@[expose]
def term_of_function {l} (f : L.functions l) : Arity' (term L) (term L) l :=
  Arity'.of_dvector_map
    (apps (preterm.func f))
      -- term.rec: custom recursion principle via structural recursion


-- term.rec: custom recursion principle via structural recursion
@[expose]
def term.rec {C : term L → Sort v} (hvar : ∀ (k : ℕ), C (&k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (term L) l)
        (_ih_ts : ∀ t, DVec.pmem t ts → C t), C (apps (preterm.func f) ts)) :
    ∀ (t : term L), C t :=
  let rec go :
    ∀ {l} (t : preterm L l) (ts : DVec (term L) l) (ih_ts : ∀ s, DVec.pmem s ts → C s),
      C (apps t ts)
    | _, preterm.var k, ts, _ => by rw [DVec.zero_eq ts]; exact hvar k
    | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
    | _, preterm.app t₁ t₂, ts, ih_ts =>
      go t₁ (DVec.cons t₂ ts) fun t ht => by
        cases ht with
        | inl h => exact h ▸ go t₂ DVec.nil (fun s hs => hs.elim)
        | inr h => exact ih_ts t h
  fun t => go t DVec.nil (fun s hs => hs.elim)

@[expose]
def term.elim' {C : Type v} (hvar : ∀ (_k : ℕ), C)
    (hfunc : ∀ {{l}} (_f : L.functions l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C) :
    ∀ {l} (_t : preterm L l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C
  | _, preterm.var k, _, _ => hvar k
  | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
  | _, preterm.app t s, ts, ih_ts =>
    term.elim' hvar hfunc t (DVec.cons s ts)
      (DVec.cons (term.elim' hvar hfunc s DVec.nil DVec.nil) ih_ts)

@[expose]
def term.elim {C : Type v} (hvar : ∀ (_k : ℕ), C)
    (hfunc : ∀ {{l}} (_f : L.functions l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C) :
    ∀ (_t : term L), C := fun t => term.elim' hvar hfunc t DVec.nil DVec.nil

lemma term.elim'_apps {C : Type v} (hvar : ∀ (_k : ℕ), C)
    (hfunc : ∀ {{l}} (_f : L.functions l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C)
    {l} (t : preterm L l) (ts : DVec (term L) l) :
    @term.elim' L C hvar hfunc 0 (apps t ts) DVec.nil DVec.nil =
      @term.elim' L C hvar hfunc l t ts (ts.map (term.elim hvar hfunc)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih =>
    simp only [DVec.map, apps]
    exact ih (preterm.app t x)

lemma term.elim_apps {C : Type v} (hvar : ∀ (_k : ℕ), C)
    (hfunc : ∀ {{l}} (_f : L.functions l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C)
    {l} (f : L.functions l) (ts : DVec (term L) l) :
    @term.elim L C hvar hfunc (apps (preterm.func f) ts) =
      hfunc f ts (ts.map (@term.elim L C hvar hfunc)) :=
  by
  simp only [term.elim, term.elim'_apps]
  rfl

/-! ## lift_term_at — lifting variables -/


/-- `lift_term_at t n m` raises variables in `t` which are ≥ m by
n. -/
@[simp, expose]
def lift_term_at : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
  | _, preterm.var k, n, m => &(if m ≤ k then k + n else k)
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, n, m => preterm.app (lift_term_at t₁ n m) (lift_term_at t₂ n m)

notation:90 t " ↑' " n " # " m => Fol.lift_term_at t n m

@[reducible, expose]
def lift_term {l} (t : preterm L l) (n : ℕ) : preterm L l :=
  lift_term_at t n 0

infixl:100 " ↑ " => Fol.lift_term

@[reducible, simp, expose]
def lift_term1 {l} (t : preterm L l) : preterm L l :=
  lift_term t 1

@[simp]
lemma lift_term_def {l} (t : preterm L l) (n : ℕ) : lift_term_at t n 0 = lift_term t n :=
  rfl

lemma injective_lift_term_at :
    ∀ {l} {n m : ℕ}, Function.Injective (fun (t : preterm L l) => lift_term_at t n m)
  | _, n, m, preterm.var k, preterm.var k', h =>
    by
    simp only [lift_term_at] at h
    have hk := preterm.var.inj h
    split_ifs at hk with h₁ h₂
    all_goals (try exact congrArg preterm.var (by omega))
  | _, _, _, preterm.var _, preterm.func _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.var _, preterm.app _ _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.func _, preterm.var _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.func _, preterm.func _, h => h
  | _, _, _, preterm.func _, preterm.app _ _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.app _ _, preterm.var _, h => by simp [lift_term_at] at h
  | _, _, _, preterm.app _ _, preterm.func _, h => by simp [lift_term_at] at h
  | _, n, m, preterm.app t₁ t₂, preterm.app t₁' t₂', h =>
    by
    simp only [lift_term_at] at h
    obtain ⟨h1, h2⟩ := preterm.app.inj h
    exact congrArg₂ preterm.app (injective_lift_term_at h1) (injective_lift_term_at h2)

@[simp]
lemma lift_term_at_zero : ∀ {l} (t : preterm L l) (m : ℕ), lift_term_at t 0 m = t
  | _, preterm.var k, _ => by simp [lift_term_at]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, m => by
    simp only [lift_term_at, lift_term_at_zero t₁ m, lift_term_at_zero t₂ m]

@[simp]
lemma lift_term_zero {l} (t : preterm L l) : lift_term t 0 = t :=
  lift_term_at_zero t 0

/-- Iterated lifts: smaller new position -/
lemma lift_term_at2_small :
    ∀ {l} (t : preterm L l) (n n') {m m'},
      m' ≤ m →
        lift_term_at (lift_term_at t n m) n' m' =
          lift_term_at (lift_term_at t n' m') n (m + n')
  | _, preterm.var k, n, n', m, m', H =>
    by
    simp only [lift_term_at]
    split_ifs <;> simp_all [] <;> omega
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H => by
    simp only [lift_term_at, lift_term_at2_small t₁ n n' H, lift_term_at2_small t₂ n n' H]

lemma lift_term_at2_medium :
    ∀ {l} (t : preterm L l) {n} (n') {m m'},
      m ≤ m' →
        m' ≤ m + n → lift_term_at (lift_term_at t n m) n' m' = lift_term_at t (n + n') m
  | _, preterm.var k, n, n', m, m', H₁, H₂ =>
    by
    simp only [lift_term_at]
    split_ifs <;> simp_all [] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H₁, H₂ => by
    simp only [lift_term_at, lift_term_at2_medium t₁ n' H₁ H₂,
      lift_term_at2_medium t₂ n' H₁ H₂]

lemma lift_term2_medium {l} (t : preterm L l) {n} (n') {m'} (h : m' ≤ n) :
    lift_term_at (lift_term t n) n' m' = lift_term t (n + n') :=
  lift_term_at2_medium t n' (Nat.zero_le _) (by omega)

lemma lift_term2 {l} (t : preterm L l) (n n') :
    lift_term (lift_term t n) n' = lift_term t (n + n') :=
  lift_term2_medium t n' (Nat.zero_le _)

lemma lift_term_at2_eq {l} (t : preterm L l) (n n' m : ℕ) :
    lift_term_at (lift_term_at t n m) n' (m + n) = lift_term_at t (n + n') m :=
  lift_term_at2_medium t n' (Nat.le_add_right _ _) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm L l) {n} (n') {m m'} (H : m + n ≤ m') :
    lift_term_at (lift_term_at t n m) n' m' =
      lift_term_at (lift_term_at t n' (m' - n)) n m :=
  by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_term_at2_small t n' n H₂, Nat.sub_add_cancel H₁]

@[simp]
lemma lift_term_var0 (n : ℕ) : lift_term (&0 : term L) n = &n := by
  simp [lift_term, lift_term_at]

@[simp]
lemma lift_term_at_apps {l} (t : preterm L l) (ts : DVec (term L) l) (n m : ℕ) :
    lift_term_at (apps t ts) n m =
      apps (lift_term_at t n m) (ts.map (fun x => lift_term_at x n m)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps, DVec.map]; exact ih (preterm.app t x)

@[simp]
lemma lift_term_apps {l} (t : preterm L l) (ts : DVec (term L) l) (n : ℕ) :
    lift_term (apps t ts) n = apps (lift_term t n) (ts.map (fun x => lift_term x n)) :=
  lift_term_at_apps t ts n 0

/-! ## subst_term — substitution -/


/-- `subst_term t s n` substitutes `s` for `(&n)` in `t` and
reduces variable levels above n. -/
@[expose]
def subst_term : ∀ {l}, preterm L l → term L → ℕ → preterm L l
  | _, preterm.var k, s, n => Fol.subst_realize preterm.var (lift_term s n) n k
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, s, n => preterm.app (subst_term t₁ s n) (subst_term t₂ s n)

@[simp]
lemma subst_term_var_lt (s : term L) {k n : ℕ} (H : k < n) :
    subst_term (preterm.var k) s n = &k := by
  simp only [subst_term, subst_realize, H, ite_true]

@[simp]
lemma subst_term_var_gt (s : term L) {k n : ℕ} (H : n < k) :
    subst_term (preterm.var k) s n = &(k - 1) :=
  by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [subst_term, subst_realize, h, ite_false, H, ite_true]

@[simp]
lemma subst_term_var_eq (s : term L) (n : ℕ) :
    subst_term (preterm.var n) s n = lift_term_at s n 0 := by
  simp [subst_term, subst_realize]

lemma subst_term_var0 (s : term L) : subst_term (preterm.var 0) s 0 = s := by
  simp [subst_term, subst_realize, lift_term_at_zero]

@[simp]
lemma subst_term_func {l} (f : L.functions l) (s : term L) (n : ℕ) :
    subst_term (preterm.func f : preterm L l) s n = preterm.func f :=
  rfl

@[simp]
lemma subst_term_app {l} (t₁ : preterm L (l + 1)) (t₂ s : term L) (n : ℕ) :
    subst_term (preterm.app t₁ t₂) s n =
      preterm.app (subst_term t₁ s n) (subst_term t₂ s n) :=
  rfl

@[simp]
lemma subst_term_apps {l} (t : preterm L l) (ts : DVec (term L) l) (s : term L) (n : ℕ) :
    subst_term (apps t ts) s n =
      apps (subst_term t s n) (ts.map (fun x => subst_term x s n)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps, DVec.map]; exact ih (preterm.app t x)

/-- Lift then substitute: large case (substituted var is above
the lift range) -/
lemma lift_at_subst_term_large :
    ∀ {l} (t : preterm L l) (s : term L) {n₁} (n₂) {m},
      m ≤ n₁ →
        subst_term (lift_term_at t n₂ m) s (n₁ + n₂) =
          lift_term_at (subst_term t s n₁) n₂ m
  | _, preterm.var k, s, n₁, n₂, m, h =>
    by
    simp only [lift_term_at, subst_term, subst_realize]
    split_ifs with h1 h2 h3 h4 h5 <;>
      first
      | rfl
      | omega
      | (simp [lift_term_at]; omega)
      | (rw [← lift_term2_medium s n₂ (by omega)])
      | (congr 1; omega)
      |
        -- Goal: &(k+n₂-1) = &(k-1) ↑' n₂ # m; know m ≤ n₁ < k so m ≤ k-1
        (simp only [lift_term_at]; split_ifs with hm <;> (first | (congr 1; omega)))
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m, h => by
    simp [lift_at_subst_term_large t₁ s n₂ h, lift_at_subst_term_large t₂ s n₂ h]

lemma lift_subst_term_large {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_term (lift_term t n₂) s (n₁ + n₂) = lift_term (subst_term t s n₁) n₂ :=
  lift_at_subst_term_large t s n₂ (Nat.zero_le _)

lemma lift_subst_term_large' {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_term (lift_term t n₂) s (n₂ + n₁) = lift_term (subst_term t s n₁) n₂ := by
  rw [Nat.add_comm]; exact lift_subst_term_large t s n₁ n₂

/-- Lift then substitute: medium case (substituted var is within
the lift range) -/
lemma lift_at_subst_term_medium :
    ∀ {l} (t : preterm L l) (s : term L) {n₁ n₂ m},
      m ≤ n₂ →
        n₂ ≤ m + n₁ → subst_term (lift_term_at t (n₁ + 1) m) s n₂ = lift_term_at t n₁ m
  | _, preterm.var k, s, n₁, n₂, m, h₁, h₂ =>
    by
    simp only [lift_term_at, subst_term, subst_realize]
    split_ifs <;> simp_all [] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
    simp [lift_at_subst_term_medium t₁ s h₁ h₂, lift_at_subst_term_medium t₂ s h₁ h₂]

lemma lift_subst_term_medium {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_term (lift_term t (n₁ + n₂ + 1)) s n₁ = lift_term t (n₁ + n₂) :=
  lift_at_subst_term_medium t s (Nat.zero_le _) (by omega)

lemma lift_at_subst_term_eq {l} (t : preterm L l) (s : term L) (n : ℕ) :
    subst_term (lift_term_at t 1 n) s n = t :=
  by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, lift_at_subst_term_medium t s (le_refl n) (le_refl n), lift_term_at_zero]

@[simp]
lemma lift_term1_subst_term {l} (t : preterm L l) (s : term L) :
    subst_term (lift_term t 1) s 0 = t :=
  lift_at_subst_term_eq t s 0

/-- Lift then substitute: small case -/
lemma lift_at_subst_term_small :
    ∀ {l} (t : preterm L l) (s : term L) (n₁ n₂ m : ℕ),
      subst_term (lift_term_at t n₁ (m + n₂ + 1)) (lift_term_at s n₁ m) n₂ =
        lift_term_at (subst_term t s n₂) n₁ (m + n₂)
  | _, preterm.var k, s, n₁, n₂, m =>
    by
    rcases Nat.lt_trichotomy k n₂ with hk | hk | hk
    · -- k < n₂: subst gives &k, lift gives k (since ¬(m+n₂+1 ≤ k))

      have h1 : ¬(m + n₂ + 1 ≤ k) := by omega
      have h2 : ¬(m + n₂ ≤ k) := by omega
      simp only [lift_term_at, h1, ite_false, subst_term, subst_realize, hk, ite_true, h2,
        ite_false]
    · -- k = n₂: use lift_term_at2_small
              -- After hk: k = n₂. Goal with n₂ replaced by k everywhere:
              -- subst_term (var k ↑' n₁ # m+k+1) (s ↑' n₁ # m) k = (subst_term
              -- (var k) s k) ↑' n₁ # m+k
              -- Since m+k+1 > k, lift of var k at (m+k+1) gives var k.
              -- subst_term (var k) (s ↑' n₁ # m) k = (s ↑' n₁ # m) ↑ k (since
              -- k = n₂ exactly)
              -- subst_term (var k) s k = s ↑ k
              -- Need: (s ↑' n₁ # m) ↑ k = (s ↑ k) ↑' n₁ # m+k =
              -- lift_term_at2_small
              -- rewrite n₂ as k throughout using hk

      rw [← hk]
      simp only [lift_term_at, show ¬(m + k + 1 ≤ k) from by omega, ite_false, subst_term,
        subst_realize, lt_irrefl, ite_false, lift_term]
      exact lift_term_at2_small s n₁ k (Nat.zero_le m)
    · -- k > n₂: subst gives &(k-1), lift depends on m+n₂+1 ≤ k

      by_cases h1 : m + n₂ + 1 ≤ k
      · -- k ≥ m+n₂+1: lift gives &(k+n₁), substitute gives &(k+n₁-1)

        have h2 : m + n₂ ≤ k - 1 := by omega
        have hk1 : 1 ≤ k := by
          omega
            -- lhs: lift var k at (m+n₂+1) gives var (k+n₁); subst at n₂: n₂
                      -- < k+n₁, gives &(k+n₁-1)
                      -- rhs: subst var k at n₂: n₂ < k, gives &(k-1); lift &(k-1) at
                      -- (m+n₂): m+n₂ ≤ k-1, gives &(k-1+n₁)
                      -- need k+n₁-1 = k-1+n₁

        have hknlt : ¬(k < n₂) := Nat.lt_asymm hk
        have hkn1lt : ¬(k + n₁ < n₂) := by omega
        simp only [lift_term_at, h1, ite_true, subst_term, subst_realize, hknlt,
          ite_false, hkn1lt, show n₂ < k + n₁ from by omega, ite_true, h2, ite_true, hk,
          ite_true]
        exact congrArg preterm.var (by omega)
      · -- k < m+n₂+1 but k > n₂: so n₂ < k < m+n₂+1
                  -- lift gives &k (since ¬(m+n₂+1 ≤ k)), subst gives &(k-1) (since
                  -- k > n₂)
                  -- and ¬(m+n₂ ≤ k-1) because k ≤ m+n₂, so k-1 < m+n₂

        have h2 : ¬(m + n₂ ≤ k - 1) := by omega
        simp only [lift_term_at, h1, ite_false, subst_term, subst_realize,
          Nat.lt_asymm hk, ite_false, hk, ite_true, h2, ite_false]
  | _, preterm.func _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m => by
    simp [lift_at_subst_term_small t₁ s n₁ n₂ m, lift_at_subst_term_small t₂ s n₁ n₂ m]

/-- Double substitution lemma -/
lemma subst_term2 :
    ∀ {l} (t : preterm L l) (s₁ s₂ : term L) (n₁ n₂ : ℕ),
      subst_term (subst_term t s₁ n₁) s₂ (n₁ + n₂) =
        subst_term (subst_term t s₂ (n₁ + n₂ + 1)) (subst_term s₁ s₂ n₂) n₁
  | _, preterm.var k, s₁, s₂, n₁, n₂ => by
    -- Case analysis: k < n₁ | k = n₁ | n₁ < k
          -- Then for n₁ < k, further: k < n₁+n₂+1 | k = n₁+n₂+1 | k >
          -- n₁+n₂+1

    rcases Nat.lt_trichotomy k n₁ with hk | hk | hk
    · -- k < n₁: both sides give &k

      have hkn : k < n₁ + n₂ := Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)
      rw [subst_term_var_lt s₁ hk, subst_term_var_lt s₂ (Nat.lt_succ_of_lt hkn),
        subst_term_var_lt _ hkn, subst_term_var_lt _ hk]
    · -- k = n₁: LHS = subst_term (lift_term s₁ n₁) s₂ (n₁+n₂) = lift_term (s₁[s₂//n₂]) n₁
              -- RHS = subst_term (var n₁) (s₁[s₂//n₂]) n₁ = lift_term
              -- (s₁[s₂//n₂]) n₁

      subst hk
      rw [subst_term_var_lt s₂ (by omega : k < k + n₂ + 1),
        subst_term_var_eq (subst_term s₁ s₂ n₂) k, subst_term_var_eq s₁ k,
        lift_subst_term_large']
    · -- n₁ < k

      rcases Nat.lt_trichotomy k (n₁ + n₂ + 1) with hk' | hk' | hk'
      · -- n₁ < k < n₁+n₂+1: both sides give &(k-1)

        have hk1lt : k - 1 < n₁ + n₂ := by omega
        have hk1n1 : n₁ < k - 1 ∨ k - 1 = n₁ := by omega
        have hkn1 : ¬(k - 1 < n₁) := by omega
        rw [subst_term_var_gt s₁ hk, subst_term_var_lt s₂ hk', subst_term_var_lt s₂ hk1lt,
          subst_term_var_gt (subst_term s₁ s₂ n₂) hk]
      · -- k = n₁+n₂+1:
                  -- LHS: subst_term (var (n₁+n₂)) s₂ (n₁+n₂) = lift_term_at s₂
                  -- (n₁+n₂) 0
                  -- RHS: subst_term (lift_term_at s₂ (n₁+n₂+1) 0) (s₁[s₂//n₂]) n₁
                  -- = lift_term_at s₂ (n₁+n₂) 0

        subst hk'
        rw [subst_term_var_gt s₁ hk, show n₁ + n₂ + 1 - 1 = n₁ + n₂ from by omega,
          subst_term_var_eq s₂ (n₁ + n₂)]
          -- LHS = lift_term_at s₂ (n₁+n₂) 0
                    -- RHS: subst_term (subst_term (var (n₁+n₂+1)) s₂ (n₁+n₂+1))
                    -- (s₁[s₂//n₂]) n₁
                    --    = subst_term (lift_term_at s₂ (n₁+n₂+1) 0) (s₁[s₂//n₂]) n₁
                    --    = lift_term_at s₂ (n₁+n₂) 0 [lift_subst_term_medium]

        rw [subst_term_var_eq s₂ (n₁ + n₂ + 1), lift_subst_term_medium]
      · -- k > n₁+n₂+1: both sides give &(k-2)

        have hkgt : n₁ + n₂ + 1 < k := hk'
        have hk1gt : n₁ + n₂ < k - 1 := by omega
        have hn1lt : n₁ < k - 1 := by omega
        rw [subst_term_var_gt s₁ hk, subst_term_var_gt s₂ hk']
          -- LHS: subst_term (var (k-1)) s₂ (n₁+n₂)
                    -- k-1 > n₁+n₂ (since k > n₁+n₂+1), so gives var (k-1-1) = var
                    -- (k-2)

        rw [subst_term_var_gt s₂ hk1gt]
          -- RHS: subst_term (var (k-1)) (s₁[s₂//n₂]) n₁
                    --   k-1 > n₁, so gives var (k-1-1) = var (k-2)

        rw [subst_term_var_gt (subst_term s₁ s₂ n₂) hn1lt]
  | _, preterm.func _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s₁, s₂, n₁, n₂ => by
    simp [subst_term2 t₁ s₁ s₂ n₁ n₂, subst_term2 t₂ s₁ s₂ n₁ n₂]

lemma subst_term2_0 {l} (t : preterm L l) (s₁ s₂ : term L) (n : ℕ) :
    subst_term (subst_term t s₁ 0) s₂ n =
      subst_term (subst_term t s₂ (n + 1)) (subst_term s₁ s₂ n) 0 :=
  by
  have h := subst_term2 t s₁ s₂ 0 n
  simp only [Nat.zero_add] at h
  exact h

lemma lift_subst_term_cancel :
    ∀ {l} (t : preterm L l) (n : ℕ), subst_term (lift_term_at t 1 (n + 1)) (&0) n = t
  | _, preterm.var k, n =>
    by
    simp only [lift_term_at, subst_term, subst_realize]
    split_ifs with h1 h2 h3 <;> simp_all [] <;> omega
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, n => by
    simp [lift_subst_term_cancel t₁ n, lift_subst_term_cancel t₂ n]

/-! ## preformula and formula -/


/-- `preformula L l` is a partially applied formula. If applied
to `l` terms, it becomes a formula (l=0). -/
inductive preformula : ℕ → Type u
  | falsum : preformula 0
  | equal (t₁ t₂ : term L) : preformula 0
  | rel {l : ℕ} (R : L.relations l) : preformula l
  | apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
  | imp (f₁ f₂ : preformula 0) : preformula 0
  |
  all (f : preformula 0) :
    preformula
      0
        -- Switch L back to explicit so that `preformula L l` works in
        -- type signatures.
        -- (After "variable {L}" at line 103, writing "preformula l" has
        -- ambiguous L in type positions.)


-- Switch L back to explicit so that `preformula L l` works in
-- type signatures.
-- (After "variable {L}" at line 103, writing "preformula l" has
-- ambiguous L in type positions.)
variable
  (L)
    -- formula: formula L is the type of first-order formulas over
    -- language L.


-- formula: formula L is the type of first-order formulas over
-- language L.
@[reducible, expose]
def formula (L : Language.{u}) : Type u :=
  @preformula L 0

variable {L}

notation "⊥'" => Fol.preformula.falsum
scoped infix:88 " ≃ " => Fol.preformula.equal
scoped infixr:62 " ⟹ " => Fol.preformula.imp
scoped prefix:110 "∀'" => Fol.preformula.all

@[expose]
def not' (f : formula L) : formula L :=
  preformula.imp f preformula.falsum
scoped prefix:max "∼" => Fol.not'
@[expose]
def and' (f₁ f₂ : formula L) : formula L :=
  not' (preformula.imp f₁ (not' f₂))
scoped infixr:69 " ⊓' " => Fol.and'
@[expose]
def or' (f₁ f₂ : formula L) : formula L :=
  preformula.imp (not' f₁) f₂
scoped infixr:68 " ⊔' " => Fol.or'
@[expose]
def biimp (f₁ f₂ : formula L) : formula L :=
  and' (preformula.imp f₁ f₂) (preformula.imp f₂ f₁)
scoped infix:61 " ⇔ " => Fol.biimp
@[expose]
def ex' (f : formula L) : formula L :=
  not' (preformula.all (not' f))
scoped prefix:110 "∃'" => Fol.ex'

@[simp, expose]
def apps_rel : ∀ {l}, @preformula L l → DVec (term L) l → formula L
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => apps_rel (preformula.apprel f t) ts

@[simp]
lemma apps_rel_zero (f : formula L) (ts : DVec (term L) 0) : apps_rel f ts = f := by
  cases ts; rfl

@[expose]
def formula_of_relation {l} (R : L.relations l) : Arity' (term L) (formula L) l :=
  Arity'.of_dvector_map (apps_rel (preformula.rel R))

@[elab_as_elim, expose]
def formula.rec' {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) :
    ∀ {l} (f : @preformula L l) (ts : DVec (term L) l), C (apps_rel f ts)
  | _, preformula.falsum, ts => by cases ts; exact hfalsum
  | _, preformula.equal t₁ t₂, ts => by cases ts; exact hequal t₁ t₂
  | _, preformula.rel R, ts => hrel R ts
  | _, preformula.apprel f t, ts =>
    formula.rec' hfalsum hequal hrel himp hall f (DVec.cons t ts)
  | _, preformula.imp f₁ f₂, ts => by
    cases ts
    exact
      himp (formula.rec' hfalsum hequal hrel himp hall f₁ DVec.nil)
        (formula.rec' hfalsum hequal hrel himp hall f₂ DVec.nil)
  | _, preformula.all f, ts => by
    cases ts
    exact hall (formula.rec' hfalsum hequal hrel himp hall f DVec.nil)

@[elab_as_elim, expose]
def formula.rec {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) : ∀ f, C f := fun f =>
  have h := @formula.rec' L C hfalsum hequal hrel himp hall 0 f DVec.nil
  apps_rel_zero f DVec.nil ▸ h

lemma formula.rec'_apps_rel {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) {l} (f : @preformula L l)
    (ts : DVec (term L) l) :
    @formula.rec' L C hfalsum hequal hrel himp hall 0 (apps_rel f ts) DVec.nil =
      @formula.rec' L C hfalsum hequal hrel himp hall l f ts :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps_rel]; exact ih (preformula.apprel f x)

lemma formula.rec_apps_rel {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (apps_rel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) {l} (R : L.relations l)
    (ts : DVec (term L) l) :
    @formula.rec L C hfalsum hequal hrel himp hall (apps_rel (preformula.rel R) ts) =
      hrel R ts :=
  -- formula.rec f = apps_rel_zero f [] ▸ formula.rec' ... 0 f []
    -- This is definitionally equal to: (apps_rel_zero ...).symm ▸
    -- formula.rec'_apps_rel ▸ hrel R ts

  show
    (apps_rel_zero (apps_rel (preformula.rel R) ts) DVec.nil ▸
        @formula.rec' L C hfalsum hequal hrel himp hall 0 (apps_rel (preformula.rel R) ts)
          DVec.nil) =
      hrel R ts
    by
    rw [formula.rec'_apps_rel]
    rfl

/-! ## lift_formula_at — lifting variables in formulas -/


@[simp, expose]
def lift_formula_at : ∀ {l}, @preformula L l → ℕ → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, n, m =>
    preformula.equal (lift_term_at t₁ n m) (lift_term_at t₂ n m)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, n, m =>
    preformula.apprel (lift_formula_at f n m) (lift_term_at t n m)
  | _, preformula.imp f₁ f₂, n, m =>
    preformula.imp (lift_formula_at f₁ n m) (lift_formula_at f₂ n m)
  | _, preformula.all f, n, m => preformula.all (lift_formula_at f n (m + 1))

notation:90 f " ↑f' " n " # " m => Fol.lift_formula_at f n m

@[reducible, expose]
def lift_formula {l} (f : @preformula L l) (n : ℕ) : @preformula L l :=
  lift_formula_at f n 0

infixl:100 " ↑f " => Fol.lift_formula

@[reducible, simp, expose]
def lift_formula1 {l} (f : @preformula L l) : @preformula L l :=
  lift_formula f 1

@[simp]
lemma lift_formula_def {l} (f : @preformula L l) (n : ℕ) :
    lift_formula_at f n 0 = lift_formula f n :=
  rfl

@[simp]
lemma lift_formula1_not (n : ℕ) (f : formula L) : ∼f ↑f n = ∼(f ↑f n) :=
  rfl

lemma injective_lift_formula_at {l} {n : ℕ} {m : ℕ} :
    Function.Injective (fun (f : @preformula L l) => lift_formula_at f n m) :=
  by
  intro f f' H
  induction f generalizing m with
  | falsum => cases f' <;> simp [lift_formula_at] at *
  | equal t₁ t₂ =>
    cases f' with
    | equal t₁' t₂' =>
      simp only [lift_formula_at] at H
      obtain ⟨h1, h2⟩ := preformula.equal.inj H
      exact
        congrArg₂ preformula.equal (injective_lift_term_at h1) (injective_lift_term_at h2)
    | _ => simp [lift_formula_at] at H
  | rel R =>
    cases f' with
    | rel R' => exact preformula.rel.inj H ▸ rfl
    | _ => simp [lift_formula_at] at H
  | apprel f t ih =>
    cases f' with
    | apprel f' t' =>
      simp only [lift_formula_at] at H
      obtain ⟨hf, ht⟩ := preformula.apprel.inj H
      exact congrArg₂ preformula.apprel (ih hf) (injective_lift_term_at ht)
    | _ => simp [lift_formula_at] at H
  | imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | imp f₁' f₂' =>
      simp only [lift_formula_at] at H
      obtain ⟨h1, h2⟩ := preformula.imp.inj H
      exact congrArg₂ preformula.imp (ih₁ h1) (ih₂ h2)
    | _ => simp [lift_formula_at] at H
  | all f ih =>
    cases f' with
    | all f' =>
      simp only [lift_formula_at] at H
      exact congrArg preformula.all (ih (preformula.all.inj H))
    | _ => simp [lift_formula_at] at H

@[simp]
lemma lift_formula_at_zero :
    ∀ {l} (f : @preformula L l) (m : ℕ), lift_formula_at f 0 m = f
  | _, preformula.falsum, _ => rfl
  | _, preformula.equal t₁ t₂, m => by simp [lift_formula_at]
  | _, preformula.rel R, _ => rfl
  | _, preformula.apprel f t, m => by
    simp only [lift_formula_at, lift_formula_at_zero f m, lift_term_at_zero]
  | _, preformula.imp f₁ f₂, m => by
    simp only [lift_formula_at, lift_formula_at_zero f₁ m, lift_formula_at_zero f₂ m]
  | _, preformula.all f, m => by
    simp only [lift_formula_at, lift_formula_at_zero f (m + 1)]

lemma lift_formula_at2_small :
    ∀ {l} (f : @preformula L l) (n n') {m m'},
      m' ≤ m →
        lift_formula_at (lift_formula_at f n m) n' m' =
          lift_formula_at (lift_formula_at f n' m') n (m + n')
  | _, preformula.falsum, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H => by
    simp [lift_formula_at, lift_term_at2_small, H]
  | _, preformula.rel R, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H =>
    by
    simp only [lift_formula_at, lift_term_at2_small t n n' H]
    exact congrArg₂ preformula.apprel (lift_formula_at2_small f n n' H) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H =>
    by
    simp only [lift_formula_at]
    exact
      congrArg₂ preformula.imp (lift_formula_at2_small f₁ n n' H)
        (lift_formula_at2_small f₂ n n' H)
  | _, preformula.all f, n, n', m, m', H =>
    by
    simp only [lift_formula_at]
    have := lift_formula_at2_small f n n' (Nat.add_le_add_right H 1)
    rw [show m + 1 + n' = m + n' + 1 from by omega] at this
    exact congrArg preformula.all this

lemma lift_formula_at2_medium :
    ∀ {l} (f : @preformula L l) (n n') {m m'},
      m ≤ m' →
        m' ≤ m + n →
          lift_formula_at (lift_formula_at f n m) n' m' = lift_formula_at f (n + n') m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H₁, H₂ => by
    simp [lift_formula_at, lift_term_at2_medium, H₁, H₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H₁, H₂ =>
    by
    simp only [lift_formula_at, lift_term_at2_medium t n' H₁ H₂]
    exact congrArg₂ preformula.apprel (lift_formula_at2_medium f n n' H₁ H₂) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H₁, H₂ =>
    by
    simp only [lift_formula_at]
    exact
      congrArg₂ preformula.imp (lift_formula_at2_medium f₁ n n' H₁ H₂)
        (lift_formula_at2_medium f₂ n n' H₁ H₂)
  | _, preformula.all f, n, n', m, m', H₁, H₂ =>
    by
    simp only [lift_formula_at]
    exact
      congrArg preformula.all
        (lift_formula_at2_medium f n n' (Nat.add_le_add_right H₁ 1) (by omega))

lemma lift_formula_at2_eq {l} (f : @preformula L l) (n n' m : ℕ) :
    lift_formula_at (lift_formula_at f n m) n' (m + n) = lift_formula_at f (n + n') m :=
  lift_formula_at2_medium f n n' (Nat.le_add_right _ _) (le_refl _)

lemma lift_formula_at2_large {l} (f : @preformula L l) (n n') {m m'} (H : m + n ≤ m') :
    lift_formula_at (lift_formula_at f n m) n' m' =
      lift_formula_at (lift_formula_at f n' (m' - n)) n m :=
  by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_formula_at2_small f n' n H₂, Nat.sub_add_cancel H₁]

@[simp]
lemma lift_formula_at_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l)
    (n m : ℕ) :
    lift_formula_at (apps_rel f ts) n m =
      apps_rel (lift_formula_at f n m) (ts.map (fun x => lift_term_at x n m)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps_rel, DVec.map]; exact ih (preformula.apprel f x)

@[simp]
lemma lift_formula_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l) (n : ℕ) :
    lift_formula (apps_rel f ts) n =
      apps_rel (lift_formula f n) (ts.map (fun x => lift_term x n)) :=
  lift_formula_at_apps_rel f ts n 0

/-! ## subst_formula — substitution into formulas -/


@[simp, expose]
def subst_formula : ∀ {l}, @preformula L l → term L → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, s, n =>
    preformula.equal (subst_term t₁ s n) (subst_term t₂ s n)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, s, n =>
    preformula.apprel (subst_formula f s n) (subst_term t s n)
  | _, preformula.imp f₁ f₂, s, n =>
    preformula.imp (subst_formula f₁ s n) (subst_formula f₂ s n)
  | _, preformula.all f, s, n => preformula.all (subst_formula f s (n + 1))

notation:95 f " [" s " // " n "]f" => Fol.subst_formula f s n

lemma subst_formula_equal (t₁ t₂ s : term L) (n : ℕ) :
    subst_formula (preformula.equal t₁ t₂) s n =
      preformula.equal (subst_term t₁ s n) (subst_term t₂ s n) :=
  rfl

@[simp]
lemma subst_formula_biimp (f₁ f₂ : formula L) (s : term L) (n : ℕ) :
    subst_formula (biimp f₁ f₂) s n =
      biimp (subst_formula f₁ s n) (subst_formula f₂ s n) :=
  rfl

lemma lift_at_subst_formula_large :
    ∀ {l} (f : @preformula L l) (s : term L) {n₁} (n₂) {m},
      m ≤ n₁ →
        subst_formula (lift_formula_at f n₂ m) s (n₁ + n₂) =
          lift_formula_at (subst_formula f s n₁) n₂ m
  | _, preformula.falsum, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m, h => by
    simp [lift_formula_at, subst_formula, lift_at_subst_term_large _ s n₂ h]
  | _, preformula.rel R, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m, h => by
    simp [lift_formula_at, subst_formula, lift_at_subst_term_large t s n₂ h,
      lift_at_subst_formula_large f s n₂ h]
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m, h => by
    simp [lift_formula_at, subst_formula, lift_at_subst_formula_large f₁ s n₂ h,
      lift_at_subst_formula_large f₂ s n₂ h]
  | _, preformula.all f, s, n₁, n₂, m, h =>
    by
    simp only [lift_formula_at, subst_formula]
    have := lift_at_subst_formula_large f s n₂ (Nat.add_le_add_right h 1)
    rw [show n₁ + 1 + n₂ = n₁ + n₂ + 1 from by omega] at this
    exact congrArg preformula.all this

lemma lift_subst_formula_large {l} (f : @preformula L l) (s : term L) {n₁ n₂ : ℕ} :
    subst_formula (lift_formula f n₂) s (n₁ + n₂) =
      lift_formula (subst_formula f s n₁) n₂ :=
  lift_at_subst_formula_large f s n₂ (Nat.zero_le _)

lemma lift_subst_formula_large' {l} (f : @preformula L l) (s : term L) {n₁ n₂ : ℕ} :
    subst_formula (lift_formula f n₂) s (n₂ + n₁) =
      lift_formula (subst_formula f s n₁) n₂ :=
  by rw [Nat.add_comm]; exact lift_subst_formula_large f s

lemma lift_at_subst_formula_medium :
    ∀ {l} (f : @preformula L l) (s : term L) {n₁ n₂ m},
      m ≤ n₂ →
        n₂ ≤ m + n₁ →
          subst_formula (lift_formula_at f (n₁ + 1) m) s n₂ = lift_formula_at f n₁ m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
    simp [lift_formula_at, subst_formula, lift_at_subst_term_medium _ s h₁ h₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m, h₁, h₂ => by
    simp [lift_formula_at, subst_formula, lift_at_subst_term_medium t s h₁ h₂,
      lift_at_subst_formula_medium f s h₁ h₂]
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m, h₁, h₂ => by
    simp [lift_formula_at, subst_formula, lift_at_subst_formula_medium f₁ s h₁ h₂,
      lift_at_subst_formula_medium f₂ s h₁ h₂]
  | _, preformula.all f, s, n₁, n₂, m, h₁, h₂ =>
    by
    simp only [lift_formula_at, subst_formula]
    have h : n₂ + 1 ≤ (m + 1) + n₁ := by omega
    exact
      congrArg preformula.all
        (lift_at_subst_formula_medium f s (Nat.add_le_add_right h₁ 1) h)

lemma lift_subst_formula_medium {l} (f : @preformula L l) (s : term L) (n₁ n₂ : ℕ) :
    subst_formula (lift_formula f (n₁ + n₂ + 1)) s n₁ = lift_formula f (n₁ + n₂) :=
  lift_at_subst_formula_medium f s (Nat.zero_le _) (by omega)

lemma lift_at_subst_formula_eq {l} (f : @preformula L l) (s : term L) (n : ℕ) :
    subst_formula (lift_formula_at f 1 n) s n = f :=
  by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, lift_at_subst_formula_medium f s (le_refl n) (le_refl n), lift_formula_at_zero]

@[simp]
lemma lift_formula1_subst {l} (f : @preformula L l) (s : term L) :
    subst_formula (lift_formula f 1) s 0 = f :=
  lift_at_subst_formula_eq f s 0

lemma lift_at_subst_formula_small :
    ∀ {l} (f : @preformula L l) (s : term L) (n₁ n₂ m : ℕ),
      subst_formula (lift_formula_at f n₁ (m + n₂ + 1)) (lift_term_at s n₁ m) n₂ =
        lift_formula_at (subst_formula f s n₂) n₁ (m + n₂)
  | _, preformula.falsum, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m =>
    by
    simp only [lift_formula_at, subst_formula]
    exact
      congrArg₂ preformula.equal (lift_at_subst_term_small t₁ s n₁ n₂ m)
        (lift_at_subst_term_small t₂ s n₁ n₂ m)
  | _, preformula.rel R, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m =>
    by
    simp only [lift_formula_at, subst_formula]
    exact
      congrArg₂ preformula.apprel (lift_at_subst_formula_small f s n₁ n₂ m)
        (lift_at_subst_term_small t s n₁ n₂ m)
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m =>
    by
    simp only [lift_formula_at, subst_formula]
    exact
      congrArg₂ preformula.imp (lift_at_subst_formula_small f₁ s n₁ n₂ m)
        (lift_at_subst_formula_small f₂ s n₁ n₂ m)
  | _, preformula.all f, s, n₁, n₂, m =>
    by
    simp only [lift_formula_at, subst_formula]
    have := lift_at_subst_formula_small f s n₁ (n₂ + 1) m
    simp only [Nat.add_assoc] at this
    exact congrArg preformula.all this

lemma lift_at_subst_formula_small0 {l} (f : @preformula L l) (s : term L) (n₁ m : ℕ) :
    subst_formula (lift_formula_at f n₁ (m + 1)) (lift_term_at s n₁ m) 0 =
      lift_formula_at (subst_formula f s 0) n₁ m :=
  lift_at_subst_formula_small f s n₁ 0 m

lemma subst_formula2 :
    ∀ {l} (f : @preformula L l) (s₁ s₂ : term L) (n₁ n₂ : ℕ),
      subst_formula (subst_formula f s₁ n₁) s₂ (n₁ + n₂) =
        subst_formula (subst_formula f s₂ (n₁ + n₂ + 1)) (subst_term s₁ s₂ n₂) n₁
  | _, preformula.falsum, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s₁, s₂, n₁, n₂ => by simp [subst_formula, subst_term2]
  | _, preformula.rel R, _, _, _, _ => rfl
  | _, preformula.apprel f t, s₁, s₂, n₁, n₂ => by
    simp [subst_formula, subst_term2, subst_formula2 f s₁ s₂ n₁ n₂]
  | _, preformula.imp f₁ f₂, s₁, s₂, n₁, n₂ => by
    simp [subst_formula, subst_formula2 f₁ s₁ s₂ n₁ n₂, subst_formula2 f₂ s₁ s₂ n₁ n₂]
  | _, preformula.all f, s₁, s₂, n₁, n₂ =>
    by
    simp only [subst_formula]
    have h := subst_formula2 f s₁ s₂ (n₁ + 1) n₂
    simp only [show n₁ + 1 + n₂ = n₁ + n₂ + 1 from by omega, ] at h
    exact congrArg preformula.all h

lemma subst_formula2_zero {l} (f : @preformula L l) (s₁ s₂ : term L) (n : ℕ) :
    subst_formula (subst_formula f s₁ 0) s₂ n =
      subst_formula (subst_formula f s₂ (n + 1)) (subst_term s₁ s₂ n) 0 :=
  by
  have h := subst_formula2 f s₁ s₂ 0 n
  simp only [Nat.zero_add] at h
  exact h

lemma lift_subst_formula_cancel :
    ∀ {l} (f : @preformula L l) (n : ℕ),
      subst_formula (lift_formula_at f 1 (n + 1)) (&0) n = f
  | _, preformula.falsum, _ => rfl
  | _, preformula.equal t₁ t₂, n => by
    simp [lift_formula_at, subst_formula, lift_subst_term_cancel]
  | _, preformula.rel R, _ => rfl
  | _, preformula.apprel f t, n => by
    simp [lift_formula_at, subst_formula, lift_subst_term_cancel t n,
      lift_subst_formula_cancel f n]
  | _, preformula.imp f₁ f₂, n => by
    simp [lift_formula_at, subst_formula, lift_subst_formula_cancel f₁ n,
      lift_subst_formula_cancel f₂ n]
  | _, preformula.all f, n =>
    by
    simp only [lift_formula_at, subst_formula]
    exact congrArg preformula.all (lift_subst_formula_cancel f (n + 1))

@[simp]
lemma subst_formula_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l) (s : term L)
    (n : ℕ) :
    subst_formula (apps_rel f ts) s n =
      apps_rel (subst_formula f s n) (ts.map (fun x => subst_term x s n)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps_rel, DVec.map]; exact ih (preformula.apprel f x)

/-! ## count_quantifiers and quantifier_free -/


@[simp, expose]
def count_quantifiers : ∀ {l}, @preformula L l → ℕ
  | _, preformula.falsum => 0
  | _, preformula.equal _ _ => 0
  | _, preformula.rel _ => 0
  | _, preformula.apprel _ _ => 0
  | _, preformula.imp f₁ f₂ => count_quantifiers f₁ + count_quantifiers f₂
  | _, preformula.all f => count_quantifiers f + 1

@[simp]
theorem count_quantifiers_succ {l} (f : @preformula L (l + 1)) :
    count_quantifiers f = 0 := by cases f <;> rfl

@[simp]
lemma count_quantifiers_subst :
    ∀ {l} (f : @preformula L l) (s : term L) (n : ℕ),
      count_quantifiers (subst_formula f s n) = count_quantifiers f
  | _, preformula.falsum, _, _ => rfl
  | _, preformula.equal _ _, _, _ => rfl
  | _, preformula.rel _, _, _ => rfl
  | _, preformula.apprel _ _, _, _ => rfl
  | _, preformula.imp f₁ f₂, s, n => by
    simp [count_quantifiers_subst f₁ s n, count_quantifiers_subst f₂ s n]
  | _, preformula.all f, s, n => by simp [count_quantifiers_subst f s (n + 1)]

@[expose]
def quantifier_free {l} : @preformula L l → Prop := fun f => count_quantifiers f = 0

/-! ## prf — the proof system (src/fol.lean lines 816-824) -/


/-- `prf Γ A` is the type of proofs of `A` from hypotheses `Γ` in
classical first-order logic. -/
inductive prf : Set (formula L) → formula L → Type u
  | axm {Γ A} (h : A ∈ Γ) : prf Γ A
  | impI {Γ : Set (formula L)} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
  | impE {Γ} (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
  | falsumE {Γ : Set (formula L)} {A} (h : prf (insert (∼A) Γ) ⊥') : prf Γ A
  | allI {Γ A} (h : prf (lift_formula1 '' Γ) A) : prf Γ (∀'A)
  | allE₂ {Γ} (A) (t : term L) (h : prf Γ (∀'A)) : prf Γ (A [t // 0]f)
  | ref (Γ) (t : term L) : prf Γ (t ≃ t)
  |
  subst₂ {Γ} (s t : term L) (f : formula L) (h₁ : prf Γ (s ≃ t))
    (h₂ : prf Γ (f [s // 0]f)) : prf Γ (f [t // 0]f)

scoped infix:51 " ⊢ " => Fol.prf

@[expose]
def provable (T : Set (formula L)) (f : formula L) :=
  Nonempty (T ⊢ f)

scoped infix:51 " ⊢' " => Fol.provable

/-! ## Derived proof rules (src/fol.lean lines 832-1103) -/


@[expose]
def allE {Γ} (A : formula L) (t : term L) {B} (H₁ : Γ ⊢ ∀'A) (H₂ : A [t // 0]f = B) :
    Γ ⊢ B := by subst H₂; exact prf.allE₂ A t H₁

@[expose]
def prf_subst {Γ} {s t : term L} (f₁ : formula L) {f₂} (H₁ : Γ ⊢ s ≃ t)
    (H₂ : Γ ⊢ f₁ [s // 0]f) (H₃ : f₁ [t // 0]f = f₂) : Γ ⊢ f₂ := by
  subst H₃;
  exact prf.subst₂ s t f₁ H₁ H₂

@[expose]
def axm1 {Γ : Set (formula L)} {A : formula L} : insert A Γ ⊢ A :=
  prf.axm (Set.mem_insert A Γ)

@[expose]
def axm2 {Γ : Set (formula L)} {A B : formula L} : insert A (insert B Γ) ⊢ B :=
  prf.axm (Set.mem_insert_of_mem A (Set.mem_insert B Γ))

@[expose]
noncomputable def weakening {Γ Δ : Set (formula L)} {f : formula L} (H₁ : Γ ⊆ Δ)
    (H₂ : Γ ⊢ f) : Δ ⊢ f := by
  induction H₂ generalizing Δ with
  | axm h => exact prf.axm (H₁ h)
  | impI _ ih => exact prf.impI (ih (Set.insert_subset_insert H₁))
  | impE A _ _ ih₁ ih₂ => exact prf.impE A (ih₁ H₁) (ih₂ H₁)
  | falsumE _ ih => exact prf.falsumE (ih (Set.insert_subset_insert H₁))
  | allI _ ih => exact prf.allI (ih (Set.image_mono H₁))
  | allE₂ A t _ ih => exact prf.allE₂ A t (ih H₁)
  | ref => exact prf.ref _ _
  | subst₂ s t f _ _ ih₁ ih₂ => exact prf.subst₂ s t f (ih₁ H₁) (ih₂ H₁)

@[expose]
noncomputable def prf_lift {Γ : Set (formula L)} {f : formula L} (n m : ℕ) (H : Γ ⊢ f) :
    (fun f' => lift_formula_at f' n m) '' Γ ⊢ lift_formula_at f n m := by
  induction H generalizing m with
  | axm h => exact prf.axm (Set.mem_image_of_mem _ h)
  | impI _ ih =>
    apply prf.impI
    have h := ih m
    rwa [Set.image_insert_eq] at h
  | impE A _ _ ih₁ ih₂ => exact prf.impE _ (ih₁ m) (ih₂ m)
  | falsumE _ ih =>
    apply prf.falsumE
    have h := ih m
    rwa [Set.image_insert_eq] at h
  | allI _ ih =>
    apply prf.allI
    rw [Set.image_image]
    have h := ih (m + 1)
    rw [Set.image_image] at h
    apply cast _ h
    congr 1
    apply Set.image_congr'
    intro f'
    exact (lift_formula_at2_small f' n 1 (Nat.zero_le m)).symm
  | allE₂ A t _
    ih =>
    have key :
      lift_formula_at (A [t // 0]f) n m =
        (lift_formula_at A n (m + 1)) [lift_term_at t n m // 0]f :=
      (lift_at_subst_formula_small0 A t n m).symm
    rw [key]
    exact prf.allE₂ _ _ (ih m)
  | ref => exact prf.ref _ _
  | subst₂ s t f _ _ ih₁
    ih₂ =>
    have key1 :
      lift_formula_at (f [t // 0]f) n m =
        (lift_formula_at f n (m + 1)) [lift_term_at t n m // 0]f :=
      (lift_at_subst_formula_small0 f t n m).symm
    have key2 :
      lift_formula_at (f [s // 0]f) n m =
        (lift_formula_at f n (m + 1)) [lift_term_at s n m // 0]f :=
      (lift_at_subst_formula_small0 f s n m).symm
    rw [key1]
    apply prf.subst₂
    · exact ih₁ m
    · have h := ih₂ m
      rw [key2] at h
      exact h

@[expose]
noncomputable def prf_substitution {Γ : Set (formula L)} {f : formula L} (t : term L)
    (n : ℕ) (H : Γ ⊢ f) : (fun x => subst_formula x t n) '' Γ ⊢ subst_formula f t n := by
  induction H generalizing n with
  | axm h => exact prf.axm (Set.mem_image_of_mem _ h)
  | impI _ ih =>
    apply prf.impI
    have h := ih n
    rwa [Set.image_insert_eq] at h
  | impE A _ _ ih₁ ih₂ => exact prf.impE _ (ih₁ n) (ih₂ n)
  | falsumE _ ih =>
    apply prf.falsumE
    have h := ih n
    rwa [Set.image_insert_eq] at h
  | allI _ ih =>
    apply prf.allI
    rw [Set.image_image]
    have h := ih (n + 1)
    rw [Set.image_image] at h
    apply cast _ h
    congr 1
    apply Set.image_congr'
    intro f'
    exact lift_subst_formula_large f' t
  | allE₂ A s _ ih =>
    -- goal: (subst Γ) ⊢ subst_formula (A[s//0]) t n
        -- = (subst Γ) ⊢ (subst_formula A t (n+1)) [subst_term s t n //
        -- 0]
        -- which follows from allE₂ applied to ih n : (subst Γ) ⊢
        -- ∀'(subst_formula A t (n+1))

    have key :
      subst_formula (subst_formula A s 0) t n =
        subst_formula (subst_formula A t (n + 1)) (subst_term s t n) 0 :=
      subst_formula2_zero A s t n
    rw [key]
    exact prf.allE₂ _ _ (ih n)
  | ref => exact prf.ref _ _
  | subst₂ s u f _ _ ih₁
    ih₂ =>
    have key1 :
      subst_formula (subst_formula f u 0) t n =
        subst_formula (subst_formula f t (n + 1)) (subst_term u t n) 0 :=
      subst_formula2_zero f u t n
    have key2 :
      subst_formula (subst_formula f s 0) t n =
        subst_formula (subst_formula f t (n + 1)) (subst_term s t n) 0 :=
      subst_formula2_zero f s t n
    rw [key1]
    apply prf.subst₂
    · exact ih₁ n
    · have h := ih₂ n
      rw [key2] at h
      exact h

@[expose]
noncomputable def reflect_prf_lift1 {Γ : Set (formula L)} {f : formula L}
    (h : lift_formula1 '' Γ ⊢ lift_formula f 1) : Γ ⊢ f :=
  by
  have h2 := prf_substitution (&0) 0 h
  simp only [Set.image_image, lift_formula1_subst] at h2
  convert h2 using 1
  simp []

@[expose]
noncomputable def weakening1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₂) :
    insert f₁ Γ ⊢ f₂ :=
  weakening (Set.subset_insert f₁ Γ) H

@[expose]
noncomputable def weakening2 {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H : insert f₁ Γ ⊢ f₂) : insert f₁ (insert f₃ Γ) ⊢ f₂ :=
  weakening (Set.insert_subset_insert (Set.subset_insert _ Γ)) H

@[expose]
noncomputable def deduction {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A ⟹ B) :
    insert A Γ ⊢ B :=
  prf.impE A (weakening1 H) axm1

@[expose]
noncomputable def exfalso {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ ⊥') : Γ ⊢ A :=
  prf.falsumE (weakening1 H)

theorem exfalso' {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢' ⊥') : Γ ⊢' A :=
  H.map exfalso

@[expose]
noncomputable def notI {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A ⟹ ⊥') : Γ ⊢ ∼A :=
  H

@[expose]
noncomputable def andI {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : Γ ⊢ f₁)
    (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓' f₂ := by
  apply prf.impI
  apply prf.impE f₂
  · apply prf.impE f₁
    · exact axm1
    · exact weakening1 H₁
  · exact weakening1 H₂

@[expose]
noncomputable def andE1 {Γ : Set (formula L)} {f₁ : formula L} (f₂ : formula L)
    (H : Γ ⊢ f₁ ⊓' f₂) : Γ ⊢ f₁ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.impI
  apply exfalso
  apply prf.impE f₁
  · exact axm2
  · exact axm1

@[expose]
noncomputable def andE2 {Γ : Set (formula L)} (f₁ : formula L) {f₂ : formula L}
    (H : Γ ⊢ f₁ ⊓' f₂) : Γ ⊢ f₂ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.impI
  exact axm2

@[expose]
noncomputable def orI1 {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A) : Γ ⊢ A ⊔' B :=
  by
  apply prf.impI
  apply exfalso
  apply prf.impE _ axm1
  exact weakening1 H

@[expose]
noncomputable def orI2 {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ B) : Γ ⊢ A ⊔' B :=
  prf.impI (weakening1 H)

@[expose]
noncomputable def orE {Γ : Set (formula L)} {A B C : formula L} (H₁ : Γ ⊢ A ⊔' B)
    (H₂ : insert A Γ ⊢ C) (H₃ : insert B Γ ⊢ C) : Γ ⊢ C :=
  by
  apply prf.falsumE
  apply prf.impE C
  · exact axm1
  apply prf.impE B
  · apply prf.impI; exact weakening2 H₃
  apply prf.impE _ (weakening1 H₁)
  exact prf.impI (prf.impE _ axm2 (weakening2 H₂))

@[expose]
noncomputable def biimpI {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : insert f₁ Γ ⊢ f₂)
    (H₂ : insert f₂ Γ ⊢ f₁) : Γ ⊢ f₁ ⇔ f₂ :=
  andI (prf.impI H₁) (prf.impI H₂)

@[expose]
noncomputable def biimpE1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) :
    insert f₁ Γ ⊢ f₂ :=
  deduction (andE1 _ H)

@[expose]
noncomputable def biimpE2 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) :
    insert f₂ Γ ⊢ f₁ :=
  deduction (andE2 _ H)

@[expose]
noncomputable def exI {Γ : Set (formula L)} {f : formula L} (t : term L)
    (H : Γ ⊢ f [t // 0]f) : Γ ⊢ ∃'f :=
  by
  apply prf.impI
  apply prf.impE (f [t // 0]f) _ (weakening1 H)
  exact prf.allE₂ (∼f) t axm1

@[expose]
noncomputable def exE {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : Γ ⊢ ∃'f₁)
    (H₂ : insert f₁ (lift_formula1 '' Γ) ⊢ lift_formula1 f₂) : Γ ⊢ f₂ :=
  by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H₁)
  apply prf.allI
  apply prf.impI
  rw [Set.image_insert_eq]
  apply prf.impE _ axm2
  exact weakening2 H₂

@[expose]
noncomputable def ex_not_of_not_all {Γ : Set (formula L)} {f : formula L}
    (H : Γ ⊢ ∼(∀'f)) : Γ ⊢ ∃'(∼f) :=
  by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.allI
  apply prf.falsumE
  rw [Set.image_insert_eq]
  apply prf.impE _ axm2
  apply exI (&0)
  rw [lift_subst_formula_cancel]
  exact axm1

@[expose]
noncomputable def not_and_self {Γ : Set (formula L)} {f : formula L} (H : Γ ⊢ f ⊓' (∼f)) :
    Γ ⊢ ⊥' :=
  prf.impE f (andE2 f H) (andE1 (∼f) H)

@[expose]
noncomputable def prf_symm {Γ : Set (formula L)} {s t : term L} (H : Γ ⊢ s ≃ t) :
    Γ ⊢ t ≃ s := by
  apply prf_subst (&0 ≃ lift_term s 1) H
  · simp only [subst_formula, subst_term_var_eq, lift_term_def, lift_term_at_zero,
      lift_term1_subst_term];
    exact prf.ref _ _
  · simp [lift_term1_subst_term]

@[expose]
noncomputable def prf_trans {Γ : Set (formula L)} {t₁ t₂ t₃ : term L} (H : Γ ⊢ t₁ ≃ t₂)
    (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ :=
  by
  apply prf_subst (lift_term t₁ 1 ≃ &0) H'
  · simp only [subst_formula, lift_term1_subst_term, subst_term_var_eq, lift_term_def,
      lift_term_at_zero];
    exact H
  · simp [lift_term1_subst_term]

@[expose]
noncomputable def prf_congr {Γ : Set (formula L)} {t₁ t₂ : term L} (s : term L)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ subst_term s t₁ 0 ≃ subst_term s t₂ 0 :=
  by
  apply prf_subst (lift_term (subst_term s t₁ 0) 1 ≃ s) H
  · simp only [subst_formula, lift_term1_subst_term]; exact prf.ref _ _
  · simp [lift_term1_subst_term]

@[expose]
noncomputable def app_congr {Γ : Set (formula L)} {t₁ t₂ : term L} (s : preterm L 1)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ preterm.app s t₁ ≃ preterm.app s t₂ :=
  by
  have h := prf_congr (preterm.app (lift_term s 1) (&0)) H
  simp only [Nat.reduceAdd, subst_term_app, lift_term1_subst_term, subst_term_var_eq,
    lift_term_def, lift_term_at_zero] at h
  exact h

@[expose]
noncomputable def apprel_congr {Γ : Set (formula L)} {t₁ t₂ : term L}
    (f : @preformula L 1) (H : Γ ⊢ t₁ ≃ t₂) (H₂ : Γ ⊢ preformula.apprel f t₁) :
    Γ ⊢ preformula.apprel f t₂ :=
  by
  apply prf_subst (preformula.apprel (lift_formula f 1) (&0)) H
  · simp only [subst_formula, Nat.reduceAdd, lift_formula1_subst, subst_term_var_eq,
      lift_term_def, lift_term_at_zero];
    exact H₂
  · simp

@[expose]
noncomputable def imp_trans {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H₁ : Γ ⊢ f₁ ⟹ f₂) (H₂ : Γ ⊢ f₂ ⟹ f₃) : Γ ⊢ f₁ ⟹ f₃ :=
  by
  apply prf.impI
  apply prf.impE _ (weakening1 H₂)
  exact prf.impE _ (weakening1 H₁) axm1

@[expose]
noncomputable def biimp_refl (Γ : Set (formula L)) (f : formula L) : Γ ⊢ f ⇔ f :=
  biimpI axm1 axm1

@[expose]
noncomputable def biimp_trans {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H₁ : Γ ⊢ f₁ ⇔ f₂) (H₂ : Γ ⊢ f₂ ⇔ f₃) : Γ ⊢ f₁ ⇔ f₃ :=
  andI (imp_trans (andE1 _ H₁) (andE1 _ H₂)) (imp_trans (andE2 _ H₂) (andE2 _ H₁))

@[expose]
def equal_preterms (T : Set (formula L)) {l} (t₁ t₂ : preterm L l) : Type u :=
  ∀ (ts : DVec (term L) l), T ⊢ apps t₁ ts ≃ apps t₂ ts

@[expose]
noncomputable def equal_preterms_app {T : Set (formula L)} {l} {t t' : preterm L (l + 1)}
    {s s' : term L} (Ht : equal_preterms T t t') (Hs : T ⊢ s ≃ s') :
    equal_preterms T (preterm.app t s) (preterm.app t' s') :=
  by
  intro xs
  apply prf_trans (Ht (DVec.cons s xs))
  have h := prf_congr (apps (lift_term t' 1) (DVec.cons (&0) (xs.map lift_term1))) Hs
  simp only [apps, lift_term1, subst_term_apps, subst_term_app, lift_term1_subst_term,
    subst_term_var_eq, lift_term_def, lift_term_at_zero, DVec.map_map, DVec.map_id] at h
  exact h

@[refl, expose]
noncomputable def equal_preterms_refl (T : Set (formula L)) {l} (t : preterm L l) :
    equal_preterms T t t := fun xs => prf.ref T (apps t xs)

@[expose]
def equiv_preformulae (T : Set (formula L)) {l} (f₁ f₂ : @preformula L l) : Type u :=
  ∀ (ts : DVec (term L) l), T ⊢ apps_rel f₁ ts ⇔ apps_rel f₂ ts

@[expose]
noncomputable def equiv_preformulae_apprel {T : Set (formula L)} {l}
    {f f' : @preformula L (l + 1)} {s s' : term L} (Ht : equiv_preformulae T f f')
    (Hs : T ⊢ s ≃ s') :
    equiv_preformulae T (preformula.apprel f s) (preformula.apprel f' s') :=
  by
  intro xs
  apply biimp_trans (Ht (DVec.cons s xs))
  apply
    prf_subst
      (apps_rel (lift_formula f' 1) (DVec.cons (lift_term1 s) (xs.map lift_term1)) ⇔
        apps_rel (lift_formula f' 1) (DVec.cons (&0) (xs.map lift_term1)))
      Hs
  · -- H₂: T ⊢ f₁ [s // 0]f. After simp, becomes biimp_refl.

    simp only [subst_formula_biimp, subst_formula_apps_rel, DVec.map, DVec.map_map,
      lift_term1_subst_term, subst_term_var0]
    exact biimp_refl T _
  · -- H₃: f₁ [s' // 0]f = goal. After simp, becomes the target equation.

    simp only [subst_formula_biimp, subst_formula_apps_rel, DVec.map, DVec.map_map,
      lift_term1_subst_term, subst_term_var0]
    simp only [DVec.map_id, apps_rel, lift_formula1_subst]

@[refl, expose]
noncomputable def equiv_preformulae_refl (T : Set (formula L)) {l} (f : @preformula L l) :
    equiv_preformulae T f f := fun xs => biimp_refl T (apps_rel f xs)

theorem impI' {Γ : Set (formula L)} {A B : formula L} (h : insert A Γ ⊢' B) :
    Γ ⊢' (A ⟹ B) :=
  h.map prf.impI

theorem impE' {Γ : Set (formula L)} (A : formula L) {B : formula L} (h₁ : Γ ⊢' A ⟹ B)
    (h₂ : Γ ⊢' A) : Γ ⊢' B :=
  h₁.map2 (prf.impE _) h₂

theorem falsumE' {Γ : Set (formula L)} {A : formula L} (h : insert (∼A) Γ ⊢' ⊥') :
    Γ ⊢' A :=
  h.map prf.falsumE

theorem allI' {Γ : Set (formula L)} {A : formula L} (h : lift_formula1 '' Γ ⊢' A) :
    Γ ⊢' ∀'A :=
  h.map prf.allI

theorem allE' {Γ : Set (formula L)} (A : formula L) (t : term L) {B : formula L}
    (H₁ : Γ ⊢' ∀'A) (H₂ : A [t // 0]f = B) : Γ ⊢' B :=
  H₁.map (fun x => allE _ _ x H₂)

theorem allE₂' {Γ : Set (formula L)} {A : formula L} {t : term L} (h : Γ ⊢' ∀'A) :
    Γ ⊢' A [t // 0]f :=
  h.map (fun x => allE _ _ x rfl)

theorem ref' (Γ : Set (formula L)) (t : term L) : Γ ⊢' (t ≃ t) :=
  ⟨prf.ref Γ t⟩

theorem subst' {Γ : Set (formula L)} {s t : term L} (f₁ : formula L) {f₂ : formula L}
    (H₁ : Γ ⊢' s ≃ t) (H₂ : Γ ⊢' f₁ [s // 0]f) (H₃ : f₁ [t // 0]f = f₂) : Γ ⊢' f₂ :=
  H₁.map2 (fun x y => prf_subst _ x y H₃) H₂

theorem subst₂' {Γ : Set (formula L)} (s t : term L) (f : formula L) (h₁ : Γ ⊢' s ≃ t)
    (h₂ : Γ ⊢' f [s // 0]f) : Γ ⊢' f [t // 0]f :=
  h₁.map2 (prf.subst₂ _ _ _) h₂

theorem weakening' {Γ Δ : Set (formula L)} {f : formula L} (H₁ : Γ ⊆ Δ) (H₂ : Γ ⊢' f) :
    Δ ⊢' f :=
  H₂.map (weakening H₁)

theorem weakening1' {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢' f₂) :
    insert f₁ Γ ⊢' f₂ :=
  H.map weakening1

theorem weakening2' {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L} (H : insert f₁ Γ ⊢' f₂) :
    insert f₁ (insert f₃ Γ) ⊢' f₂ :=
  H.map weakening2

lemma apprel_congr' {Γ : Set (formula L)} {t₁ t₂ : term L} (f : @preformula L 1)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢' preformula.apprel f t₁ ↔ Γ ⊢' preformula.apprel f t₂ :=
  ⟨Nonempty.map (apprel_congr f H), Nonempty.map (apprel_congr f (prf_symm H))⟩

lemma prf_all_iff {Γ : Set (formula L)} {f : formula L} :
    Γ ⊢' ∀'f ↔ lift_formula1 '' Γ ⊢' f :=
  by
  constructor
  · intro H
    rw [← lift_subst_formula_cancel f 0]
    apply allE₂'
    exact H.map (prf_lift 1 0)
  · exact allI'

lemma iff_of_biimp {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢' f₁ ⇔ f₂) :
    Γ ⊢' f₁ ↔ Γ ⊢' f₂ :=
  ⟨impE' _ (H.map (andE1 _)), impE' _ (H.map (andE2 _))⟩

lemma prf_by_cases {Γ : Set (formula L)} (f₁ : formula L) {f₂ : formula L}
    (H₁ : insert f₁ Γ ⊢' f₂) (H₂ : insert (∼f₁) Γ ⊢' f₂) : Γ ⊢' f₂ :=
  by
  apply falsumE'
  apply impE' _ ⟨axm1⟩
  apply impE' _ (impI' (weakening2' H₁))
  apply falsumE'
  apply impE' _ ⟨axm2⟩
  exact weakening2' H₂

/-! ## Theory and consistency (src/fol.lean lines 1105-) -/


@[expose]
def Theory (L : Language.{u}) :=
  Set (formula L)

@[expose]
def is_consistent (T : Theory L) :=
  ¬(T ⊢' ⊥')

/-! ## Structure — L-structures (src/fol.lean line 1109) -/


variable (L)

structure Structure : Type (u + 1) where
  carrier : Type u
  fun_map : ∀ {n}, L.functions n → DVec carrier n → carrier
  rel_map : ∀ {n}, L.relations n → DVec carrier n → Prop

variable {L}

instance : CoeSort (Structure L) (Type u) where coe S := S.carrier

/-! ## realize_term — realization of terms in a structure -/


@[simp, expose]
def realize_term {S : Structure L} (v : ℕ → S) :
    ∀ {l} (_t : preterm L l) (_xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.fun_map f xs
  | _, preterm.app t₁ t₂, xs =>
    realize_term v t₁ (DVec.cons (realize_term v t₂ DVec.nil) xs)

lemma realize_term_congr {S : Structure L} {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : preterm L l) (xs : DVec S l), realize_term v t xs = realize_term v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
    simp only [realize_term]
    rw [realize_term_congr h t₁, realize_term_congr h t₂]

lemma realize_term_subst {S : Structure L} (v : ℕ → S) :
    ∀ {l} (n : ℕ) (t : preterm L l) (s : term L) (xs : DVec S l),
      realize_term (subst_realize v (realize_term v (lift_term s n) DVec.nil) n) t xs =
        realize_term v (subst_term t s n) xs
  | _, n, preterm.var k, s, DVec.nil =>
    by
    rcases Nat.lt_trichotomy k n with h | h | h
    · simp only [realize_term, subst_realize_lt _ _ h, subst_term_var_lt _ h]
    · subst h
      simp only [realize_term, subst_term_var_eq, subst_realize_var_eq, lift_term]
    · simp only [realize_term, subst_realize_gt _ _ h, subst_term_var_gt _ h]
  | _, _, preterm.func _, _, _ => rfl
  | _, n, preterm.app t₁ t₂, s, xs =>
    by
    simp only [realize_term, subst_term]
    rw [realize_term_subst v n t₂ s DVec.nil]
    rw [realize_term_subst v n t₁ s]

lemma realize_term_subst_lift {S : Structure L} (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : preterm L l) (xs : DVec S l),
      realize_term (subst_realize v x m) (lift_term_at t 1 m) xs = realize_term v t xs
  | _, preterm.var k, DVec.nil =>
    by
    simp only [realize_term, lift_term_at]
    by_cases h : m ≤ k
    · -- lift gives k+1, subst_realize gives v k

      have hmk1 : m < k + 1 := Nat.lt_succ_of_le h
      simp only [ite_eq_left h, subst_realize_gt _ _ hmk1, Nat.add_sub_cancel]
    · -- lift gives k, subst_realize gives v k (since k < m)

      have hkm : k < m := Nat.lt_of_not_le h
      simp only [ite_eq_right h, subst_realize_lt _ _ hkm]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs =>
    by
    simp only [realize_term, lift_term_at]
    rw [realize_term_subst_lift v x m t₂ DVec.nil]
    rw [realize_term_subst_lift v x m t₁]

/-! ## realize_formula — satisfaction relation -/


@[simp, expose]
def realize_formula {S : Structure L} : ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → Prop
  | _, _v, preformula.falsum, _ => False
  | _, v, preformula.equal t₁ t₂, _ =>
    realize_term v t₁ DVec.nil = realize_term v t₂ DVec.nil
  | _, _, preformula.rel R, xs => S.rel_map R xs
  | _, v, preformula.apprel f t, xs =>
    realize_formula v f (DVec.cons (realize_term v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs => realize_formula v f₁ xs → realize_formula v f₂ xs
  | _, v, preformula.all f, _ => ∀ x : S, realize_formula (subst_realize v x 0) f DVec.nil

lemma realize_formula_congr {S : Structure L} :
    ∀ {l} {v v' : ℕ → S} (_h : ∀ n, v n = v' n) (f : @preformula L l) (xs : DVec S l),
      realize_formula v f xs ↔ realize_formula v' f xs
  | _, _, _, _, preformula.falsum, _ => Iff.rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
    simp [realize_formula, realize_term_congr h]
  | _, _, _, _, preformula.rel _, _ => Iff.rfl
  | _, _, _, h, preformula.apprel f t, xs =>
    by
    simp only [realize_formula, realize_term_congr h]
    exact realize_formula_congr h f _
  | _, _, _, h, preformula.imp f₁ f₂, xs =>
    by
    simp only [realize_formula]
    exact Iff.imp (realize_formula_congr h f₁ xs) (realize_formula_congr h f₂ xs)
  | _, _, _, h, preformula.all f, _ =>
    by
    simp only [realize_formula]
    apply forall_congr'
    intro x
    exact realize_formula_congr (subst_realize_congr h x 0) f DVec.nil

lemma realize_formula_subst {S : Structure L} :
    ∀ {l} (v : ℕ → S) (n : ℕ) (f : @preformula L l) (s : term L) (xs : DVec S l),
      realize_formula (subst_realize v (realize_term v (lift_term s n) DVec.nil) n) f xs ↔
        realize_formula v (subst_formula f s n) xs
  | _, _, _, preformula.falsum, _, _ => Iff.rfl
  | _, v, n, preformula.equal t₁ t₂, s, _ => by simp [realize_formula, realize_term_subst]
  | _, _, _, preformula.rel _, _, _ => Iff.rfl
  | _, v, n, preformula.apprel f t, s, xs =>
    by
    simp only [realize_formula, subst_formula, realize_term_subst]
    exact realize_formula_subst v n f s _
  | _, v, n, preformula.imp f₁ f₂, s, xs =>
    by
    simp only [realize_formula, subst_formula]
    exact Iff.imp (realize_formula_subst v n f₁ s xs) (realize_formula_subst v n f₂ s xs)
  | _, v, n, preformula.all f, s, _ =>
    by
    simp only [realize_formula, subst_formula]
    apply forall_congr'
    intro x
    rw [← realize_formula_subst (subst_realize v x 0) (n + 1) f s DVec.nil]
    apply realize_formula_congr
    intro k
    rw [subst_realize2_0]
    congr 1
      -- Goal: realize_term v (lift_term s n) [] = realize_term
            -- (subst_realize v x 0) (lift_term s (n+1)) []

    rw [← realize_term_subst_lift v x 0 (lift_term s n) DVec.nil]
    simp only [lift_term_def]
    rw [← lift_term2 s n 1]

lemma realize_formula_subst0 {S : Structure L} {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    realize_formula (subst_realize v (realize_term v s DVec.nil) 0) f xs ↔
      realize_formula v (subst_formula f s 0) xs :=
  by
  have h := realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

lemma realize_formula_subst_lift {S : Structure L} :
    ∀ {l} (v : ℕ → S) (x : S) (m : ℕ) (f : @preformula L l) (xs : DVec S l),
      realize_formula (subst_realize v x m) (lift_formula_at f 1 m) xs =
        realize_formula v f xs
  | _, _, _, _, preformula.falsum, _ => rfl
  | _, v, x, m, preformula.equal t₁ t₂, _ => by
    simp [realize_formula, realize_term_subst_lift]
  | _, _, _, _, preformula.rel _, _ => rfl
  | _, v, x, m, preformula.apprel f t, xs =>
    by
    simp only [realize_formula, lift_formula_at, realize_term_subst_lift]
    exact realize_formula_subst_lift v x m f _
  | _, v, x, m, preformula.imp f₁ f₂, xs =>
    by
    simp only [realize_formula, lift_formula_at]
    exact
      propext
        (Iff.imp (Iff.of_eq (realize_formula_subst_lift v x m f₁ xs))
          (Iff.of_eq (realize_formula_subst_lift v x m f₂ xs)))
  | _, v, x, m, preformula.all f, _ =>
    by
    simp only [realize_formula, lift_formula_at]
    apply propext
    apply forall_congr'
    intro x'
    rw [propext
        (realize_formula_congr (fun k => subst_realize2_0 v x' x m k)
          (lift_formula_at f 1 (m + 1)) DVec.nil)]
    exact
      Iff.of_eq (realize_formula_subst_lift (subst_realize v x' 0) x (m + 1) f DVec.nil)

/-! ## Semantic notions — satisfaction and models -/


@[expose]
def satisfied_in (S : Structure L) (f : formula L) : Prop :=
  ∀ v : ℕ → S, realize_formula v f DVec.nil

scoped infix:51 " ⊨ₛ " => Fol.satisfied_in

@[expose]
def all_satisfied_in (S : Structure L) (T : Set (formula L)) : Prop :=
  ∀ {{f}}, f ∈ T → S ⊨ₛ f

@[expose]
def satisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : Structure L) (v : ℕ → S),
    (∀ f' ∈ T, realize_formula v (f' : formula L) DVec.nil) → realize_formula v f DVec.nil

scoped infix:51 " ⊨ " => Fol.satisfied

@[expose]
def all_satisfied (T T' : Set (formula L)) : Prop :=
  ∀ {{f}}, f ∈ T' → T ⊨ f

theorem satisfied_in_trans {S : Structure L} {T : Set (formula L)} {f : formula L}
    (H' : all_satisfied_in S T) (H : T ⊨ f) : S ⊨ₛ f := fun v =>
  H S v (fun _f' hf' => H' hf' v)

theorem all_satisfied_in_trans {S : Structure L} {T T' : Set (formula L)}
    (H' : all_satisfied_in S T) (H : all_satisfied T T') : all_satisfied_in S T' :=
  fun _f hf => satisfied_in_trans H' (H hf)

theorem satisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ f :=
  fun _S _v h => h f hf

theorem all_satisfied_of_subset {T T' : Set (formula L)} (h : T' ⊆ T) :
    all_satisfied T T' := fun _f hf => satisfied_of_mem (h hf)

theorem satisfied_trans {T₁ T₂ : Set (formula L)} {f : formula L}
    (H' : all_satisfied T₁ T₂) (H : T₂ ⊨ f) : T₁ ⊨ f := fun S v h =>
  H S v (fun _f' hf' => H' hf' S v h)

theorem all_satisfied_trans {T₁ T₂ T₃ : Set (formula L)} (H' : all_satisfied T₁ T₂)
    (H : all_satisfied T₂ T₃) : all_satisfied T₁ T₃ := fun _f hf =>
  satisfied_trans H' (H hf)

theorem satisfied_weakening {T T' : Set (formula L)} (H : T ⊆ T') {f : formula L}
    (HT : T ⊨ f) : T' ⊨ f := fun S v h => HT S v (fun f' hf' => h f' (H hf'))

/-! ## Soundness (src/fol.lean lines 1247-1261) -/


lemma formula_soundness {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A) : Γ ⊨ A :=
  by
  intro S
  induction H with
  | axm h => intro v hΓ; exact hΓ _ h
  | impI _ ih =>
    intro v hΓ ha
    apply ih
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | impE A _ _ ih₁ ih₂ => intro v hΓ; exact ih₁ v hΓ (ih₂ v hΓ)
  | falsumE _ ih =>
    intro v hΓ
    by_contra ha
    apply ih v
    intro f hf
    rcases hf with rfl | hf
    · exact ha
    · exact hΓ f hf
  | allI _ ih =>
    intro v hΓ x
    apply ih
    intro f hf
    rcases hf with ⟨f', hf', rfl⟩
    rw [realize_formula_subst_lift v x 0 f']
    exact hΓ f' hf'
  | allE₂ A t _ ih =>
    intro v hΓ
    rw [← realize_formula_subst0]
    exact ih v hΓ (realize_term v t DVec.nil)
  | ref => intro v _; simp [realize_formula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro v hΓ
    have h' := ih₁ v hΓ
    simp only [realize_formula] at h'
    rw [← realize_formula_subst0, ← h', realize_formula_subst0]
    exact ih₂ v hΓ

/-! ## bounded_preterm, bounded_term, closed_preterm
(src/fol.lean lines 1265-1660) -/
-- Bring L back to explicit so that bounded_preterm's
-- constructors can refer to the
-- inductive type unambiguously (same pattern as Structure and
-- formula above).


-- Bring L back to explicit so that bounded_preterm's
-- constructors can refer to the
-- inductive type unambiguously (same pattern as Structure and
-- formula above).
variable (L)

/-- A bounded preterm: `bounded_preterm L n l` is a partially
applied term with at most `n`
    free de Bruijn variables (indexed by `Fin n`) needing `l` more
    arguments. -/
inductive bounded_preterm (L : Language.{u}) (n : ℕ) : ℕ → Type u
  | bd_var : ∀ (_k : Fin n), bounded_preterm L n 0
  | bd_func : ∀ {l : ℕ} (_f : L.functions l), bounded_preterm L n l
  |
  bd_app :
    ∀ {l : ℕ} (_t : bounded_preterm L n (l + 1)) (_s : bounded_preterm L n 0),
      bounded_preterm L n l

export bounded_preterm (bd_var bd_func bd_app)

/-- A fully applied bounded term with at most `n` free variables.
-/
abbrev bounded_term (n : ℕ) :=
  bounded_preterm L n 0

/-- A closed preterm (no free variables), needing `l` more
arguments. -/
abbrev closed_preterm (l : ℕ) :=
  bounded_preterm L 0 l

/-- A closed term: no free variables and fully applied. -/
abbrev closed_term :=
  closed_preterm L 0

variable {L}

prefix:max "&ᵇ" => @bd_var _ _

@[expose]
def bd_const {n} (c : L.constants) : bounded_term L n :=
  bd_func c

/-- Apply a bounded preterm of level `l + m` to `m` bounded terms
to get level `l`. -/
@[simp, expose]
def bd_apps' {n} :
    ∀ {l m : ℕ},
      bounded_preterm L n (l + m) → DVec (bounded_term L n) m → bounded_preterm L n l
  | _, 0, t, DVec.nil => t
  | _l, _m + 1, t, DVec.cons x xs => bd_apps' (bd_app t x) xs

/-- Apply a bounded preterm of level `l` to `l` bounded terms to
get a bounded term. -/
@[simp, expose]
def bd_apps {n} :
    ∀ {l}, bounded_preterm L n l → DVec (bounded_term L n) l → bounded_term L n
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => bd_apps (bd_app t t') ts

namespace bounded_preterm

/-- Forget boundedness: map a bounded preterm to an ordinary
preterm. -/
@[simp, expose]
protected def fst {n} : ∀ {l}, bounded_preterm L n l → preterm L l
  | _, bd_var k => &k.1
  | _, bd_func f => preterm.func f
  | _, bd_app t s => preterm.app (bounded_preterm.fst t) (bounded_preterm.fst s)

/-- Equality of bounded preterms is determined by their
underlying preterms. -/
@[ext]
protected theorem eq {n} :
    ∀ {l} {t₁ t₂ : bounded_preterm L n l}, t₁.fst = t₂.fst → t₁ = t₂
  | _, bd_var k, bd_var k', h =>
    by
    simp only [bounded_preterm.fst, preterm.var.injEq] at h
    congr 1; exact Fin.ext h
  | _, bd_var _, bd_func _, h => by simp [bounded_preterm.fst] at h
  | _, bd_var _, bd_app _ _, h => by simp [bounded_preterm.fst] at h
  | _, bd_func _, bd_var _, h => by simp [bounded_preterm.fst] at h
  | _, bd_func f, bd_func f', h => by
    simp only [bounded_preterm.fst, preterm.func.injEq] at h; exact congrArg bd_func h
  | _, bd_func _, bd_app _ _, h => by simp [bounded_preterm.fst] at h
  | _, bd_app _ _, bd_var _, h => by simp [bounded_preterm.fst] at h
  | _, bd_app _ _, bd_func _, h => by simp [bounded_preterm.fst] at h
  | _, bd_app t₁ t₂, bd_app t₁' t₂', h =>
    by
    simp only [bounded_preterm.fst, preterm.app.injEq] at h
    exact congrArg₂ bd_app (bounded_preterm.eq h.1) (bounded_preterm.eq h.2)

/-- Cast a bounded_preterm L n l to one with a larger bound m ≥
n. -/
@[simp, expose]
protected def cast {n m} (h : n ≤ m) :
    ∀ {l}, bounded_preterm L n l → bounded_preterm L m l
  | _, bd_var k => bd_var ⟨k.1, Nat.lt_of_lt_of_le k.2 h⟩
  | _, bd_func f => bd_func f
  | _, bd_app t s => bd_app (t.cast h) (s.cast h)

@[simp]
lemma cast_bd_app {n m} (h : n ≤ m) {l} {t : bounded_preterm L n (l + 1)}
    {s : bounded_preterm L n 0} : (bd_app t s).cast h = bd_app (t.cast h) (s.cast h) :=
  rfl

@[simp]
lemma cast_bd_apps {n m} (h : n ≤ m) {l} {t : bounded_preterm L n l}
    {ts : DVec (bounded_term L n) l} :
    (bd_apps t ts).cast h = bd_apps (t.cast h) (ts.map (fun x => x.cast h)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [bd_apps, DVec.map]; exact ih

@[simp]
lemma cast_irrel {n m} {h h' : n ≤ m} :
    ∀ {l} (t : bounded_preterm L n l), t.cast h = t.cast h' := by
  intros l t;
  induction t with
  | bd_var k => simp [bounded_preterm.cast]
  | bd_func f => rfl
  | bd_app t s iht ihs => simp [bounded_preterm.cast, iht, ihs]

@[simp]
lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (t : bounded_preterm L n l), t.cast h = t := by
  intros l t;
  induction t with
  | bd_var k => simp [bounded_preterm.cast]
  | bd_func => rfl
  | bd_app _ _ iht ihs => simp [bounded_preterm.cast, iht, ihs]

@[expose]
protected def cast_eq {n m l} (h : n = m) (t : bounded_preterm L n l) :
    bounded_preterm L m l :=
  t.cast (Nat.le_of_eq h)

@[expose]
protected def cast1 {n l} (t : bounded_preterm L n l) : bounded_preterm L (n + 1) l :=
  t.cast (Nat.le_add_right n 1)

@[simp]
lemma cast_fst {n m} (h : n ≤ m) :
    ∀ {l} (t : bounded_preterm L n l), (t.cast h).fst = t.fst
  | _, bd_var k => rfl
  | _, bd_func f => rfl
  | _, bd_app t s => by simp [bounded_preterm.cast, cast_fst h t, cast_fst h s]

@[simp]
lemma cast_eq_fst {n m l} (h : n = m) (t : bounded_preterm L n l) :
    (t.cast_eq h).fst = t.fst :=
  cast_fst _ t

@[simp]
lemma cast1_fst {n l} (t : bounded_preterm L n l) : t.cast1.fst = t.fst :=
  cast_fst _ t

@[simp]
lemma cast_eq_rfl {n m l} (h : n = m) (t : bounded_preterm L n l) :
    (t.cast_eq h).cast_eq h.symm = t := by apply bounded_preterm.eq; simp [cast_eq_fst]

@[simp]
lemma cast_eq_irrel {n m l} (h h' : n = m) (t : bounded_preterm L n l) :
    t.cast_eq h = t.cast_eq h' :=
  rfl

@[simp]
lemma cast_eq_bd_app {n m} (h : n = m) {l} {t : bounded_preterm L n (l + 1)}
    {s : bounded_preterm L n 0} :
    (bd_app t s).cast_eq h = bd_app (t.cast_eq h) (s.cast_eq h) :=
  rfl

@[simp]
lemma cast_eq_bd_apps {n m} (h : n = m) {l} {t : bounded_preterm L n l}
    {ts : DVec (bounded_term L n) l} :
    (bd_apps t ts).cast_eq h = bd_apps (t.cast_eq h) (ts.map (fun x => x.cast_eq h)) := by
  simp [bounded_preterm.cast_eq, cast_bd_apps]

end bounded_preterm

namespace closed_preterm

@[reducible, expose]
protected def cast0 (n : ℕ) {l} (t : closed_preterm L l) : bounded_preterm L n l :=
  t.cast (Nat.zero_le n)

@[simp]
lemma cast0_fst {n l : ℕ} (t : closed_preterm L l) : (t.cast0 n).fst = t.fst :=
  bounded_preterm.cast_fst _ t

@[simp]
lemma cast_of_cast0 {n} {l} {t : closed_preterm L l} :
    t.cast0 n = t.cast (Nat.zero_le n) :=
  rfl

end closed_preterm

/-! ### bounded_term.rec — custom recursion principle -/


/-- Custom recursion principle for bounded terms, analogous to
`term.rec`. -/
@[expose]
def bounded_term.rec {n} {C : bounded_term L n → Sort v}
    (hvar : ∀ (k : Fin n), C (bd_var k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (bounded_term L n) l)
        (_ih_ts : ∀ t, DVec.pmem t ts → C t), C (bd_apps (bd_func f) ts)) :
    ∀ (t : bounded_term L n), C t :=
  let rec go :
    ∀ {l} (t : bounded_preterm L n l) (ts : DVec (bounded_term L n) l)
      (ih_ts : ∀ s, DVec.pmem s ts → C s), C (bd_apps t ts)
    | _, bd_var k, ts, _ => by rw [DVec.zero_eq ts]; exact hvar k
    | _, bd_func f, ts, ih_ts => hfunc f ts ih_ts
    | _, bd_app t₁ t₂, ts, ih_ts =>
      go t₁ (DVec.cons t₂ ts) fun t ht => by
        cases ht with
        | inl h => exact h ▸ go t₂ DVec.nil (fun s hs => hs.elim)
        | inr h => exact ih_ts t h
  fun t => go t DVec.nil (fun s hs => hs.elim)

/-- Version of `bounded_term.rec` specialized to `n + 1`. -/
@[expose]
def bounded_term.rec1 {n} {C : bounded_term L (n + 1) → Sort v}
    (hvar : ∀ (k : Fin (n + 1)), C (bd_var k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (bounded_term L (n + 1)) l)
        (_ih_ts : ∀ t, DVec.pmem t ts → C t), C (bd_apps (bd_func f) ts)) :
    ∀ (t : bounded_term L (n + 1)), C t :=
  bounded_term.rec hvar hfunc

/-! ### Lift and substitution — irrel lemmas -/


lemma lift_bounded_term_irrel {n : ℕ} :
    ∀ {l} (t : bounded_preterm L n l) (n') {m : ℕ} (_h : n ≤ m), (t.fst ↑' n' # m) = t.fst
  | _, bd_var k, n', m, h =>
    have h' : ¬(m ≤ k.1) := Nat.not_le.mpr (Nat.lt_of_lt_of_le k.2 h)
    by simp [h']
  | _, bd_func _, _, _, _ => rfl
  | _, bd_app t s, n', m, h => by
    simp [lift_bounded_term_irrel t n' h, lift_bounded_term_irrel s n' h]

lemma subst_bounded_term_irrel {n : ℕ} :
    ∀ {l} (t : bounded_preterm L n l) {n'} (s : term L) (_h : n ≤ n'),
      subst_term t.fst s n' = t.fst
  | _, bd_var k, n', s, h => by simp [Nat.lt_of_lt_of_le k.2 h]
  | _, bd_func _, _, _, _ => rfl
  | _, bd_app t₁ t₂, n', s, h => by
    simp [subst_bounded_term_irrel t₁ s h, subst_bounded_term_irrel t₂ s h]

/-! ### realize_bounded_term -/


/-- Realize a bounded preterm given a valuation vector `v : DVec
S n` and extra args `xs : DVec S l`. -/
@[simp, expose]
def realize_bounded_term {S : Structure L} {n} (v : DVec S n) :
    ∀ {l} (_t : bounded_preterm L n l) (_xs : DVec S l), S.carrier
  | _, bd_var k, _ => v.nth k.1 k.2
  | _, bd_func f, xs => S.fun_map f xs
  | _, bd_app t₁ t₂, xs =>
    realize_bounded_term v t₁ (DVec.cons (realize_bounded_term v t₂ DVec.nil) xs)

/-- Notation for realizing a bounded term with an empty extra
argument list. -/
notation:0 S "[" t " ;;; " v "]" => @realize_bounded_term _ S _ v 0 t DVec.nil

notation:0 S "[" t " ;;; " v " ;;; " xs "]" => @realize_bounded_term _ S _ v _ t xs

@[reducible, expose]
def realize_closed_term (S : Structure L) (t : closed_term L) : S.carrier :=
  realize_bounded_term DVec.nil t DVec.nil

lemma realize_bounded_term_eq {S : Structure L} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    ∀ {l} (t : bounded_preterm L n l) (xs : DVec S l),
      realize_bounded_term v₁ t xs = realize_term v₂ t.fst xs
  | _, bd_var k, _ => hv k.1 k.2
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs =>
    by
    simp only [realize_bounded_term, bounded_preterm.fst, realize_term]
    rw [realize_bounded_term_eq hv t₂ DVec.nil, realize_bounded_term_eq hv t₁]

lemma realize_bounded_term_irrel' {S : Structure L} {n n'} {v₁ : DVec S n}
    {v₂ : DVec S n'} (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn') {l}
    (t : bounded_preterm L n l) (t' : bounded_preterm L n' l) (ht : t.fst = t'.fst)
    (xs : DVec S l) : realize_bounded_term v₁ t xs = realize_bounded_term v₂ t' xs := by
  induction t generalizing n' with
  | bd_var k =>
    cases t' with
    | bd_var k' =>
      simp only [bounded_preterm.fst, preterm.var.injEq] at ht
      simp only [realize_bounded_term]
      have hk : k.1 = k'.1 := ht
      calc
        v₁.nth k.1 k.2 = v₂.nth k.1 (hk ▸ k'.2) := h k.1 k.2 (hk ▸ k'.2)
        _ = v₂.nth k'.1 k'.2 := by congr 1
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_func f =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func f' =>
      simp only [bounded_preterm.fst, preterm.func.injEq] at ht
      simp [realize_bounded_term, ht]
    | bd_app => simp [bounded_preterm.fst] at ht
  | bd_app t₁ t₂ iht ihs =>
    cases t' with
    | bd_var => simp [bounded_preterm.fst] at ht
    | bd_func => simp [bounded_preterm.fst] at ht
    | bd_app t₁'
      t₂' =>
      simp only [bounded_preterm.fst, preterm.app.injEq] at ht
      simp only [realize_bounded_term]
      rw [ihs h t₂' ht.2 DVec.nil, iht h t₁' ht.1]

lemma realize_bounded_term_irrel {S : Structure L} {n} {v₁ : DVec S n}
    (t : bounded_term L n) (t' : closed_term L) (ht : t.fst = t'.fst) :
    realize_bounded_term v₁ t DVec.nil = realize_closed_term S t' :=
  realize_bounded_term_irrel' (fun m _hm hm' => absurd hm' (Nat.not_lt_zero m)) t t' ht
    DVec.nil

@[simp]
lemma realize_bounded_term_cast_eq_irrel {S : Structure L} {n m l} {h : n = m}
    {v : DVec S m} {t : bounded_preterm L n l} (xs : DVec S l) :
    realize_bounded_term v (t.cast_eq h) xs = realize_bounded_term (v.cast h.symm) t xs :=
  by
  subst h
  simp only [bounded_preterm.cast_eq, bounded_preterm.cast_rfl, DVec.cast, ]

@[simp]
lemma realize_bounded_term_dvector_cast_irrel {S : Structure L} {n m l} {h : n = m}
    {v : DVec S n} {t : bounded_preterm L n l} {xs : DVec S l} :
    realize_bounded_term (v.cast h) (t.cast (Nat.le_of_eq h)) xs =
      realize_bounded_term v t xs :=
  by
  subst h
  simp only [bounded_preterm.cast_rfl, DVec.cast]

/-! ### lift_bounded_term_at — lifting bounded terms -/


/-- Lift a bounded term by inserting `n'` new variables at
position `m`. -/
@[simp, expose]
def lift_bounded_term_at {n} :
    ∀ {l} (_t : bounded_preterm L n l) (n' _m : ℕ), bounded_preterm L (n + n') l
  | _, bd_var k, n', m =>
    if m ≤ k.1 then bd_var ⟨k.1 + n', by omega⟩ else bd_var ⟨k.1, by omega⟩
  | _, bd_func f, _, _ => bd_func f
  | _, bd_app t₁ t₂, n', m =>
    bd_app (lift_bounded_term_at t₁ n' m) (lift_bounded_term_at t₂ n' m)

notation:90 t " ↑ᵇ' " n " # " m => Fol.lift_bounded_term_at t n m

@[reducible, expose]
def lift_bounded_term {n l} (t : bounded_preterm L n l) (n' : ℕ) :
    bounded_preterm L (n + n') l :=
  lift_bounded_term_at t n' 0

infixl:100 " ↑ᵇ " => Fol.lift_bounded_term

@[reducible, simp, expose]
def lift_bounded_term1 {n' l} (t : bounded_preterm L n' l) :
    bounded_preterm L (n' + 1) l :=
  t ↑ᵇ 1

@[simp]
lemma lift_bounded_term_fst {n} :
    ∀ {l} (t : bounded_preterm L n l) (n' m : ℕ),
      (lift_bounded_term_at t n' m).fst = t.fst ↑' n' # m
  | _, bd_var k, n', m =>
    by
    simp only [lift_bounded_term_at, bounded_preterm.fst, lift_term_at]
    split_ifs with h <;> simp []
  | _, bd_func _, _, _ => rfl
  | _, bd_app t₁ t₂, n', m => by
    simp [lift_bounded_term_fst t₁ n' m, lift_bounded_term_fst t₂ n' m]

/-! ### subst_bounded_term — substitution in bounded terms -/


/-- Substitute the variable at position `n` (within the bound `n
+ n' + 1`) with a bounded term `s`. -/
@[expose]
def subst_bounded_term {n n'} :
    ∀ {l} (_t : bounded_preterm L (n + n' + 1) l) (_s : bounded_term L n'),
      bounded_preterm L (n + n') l
  | _, bd_var k, s =>
    if h : k.1 < n then bd_var ⟨k.1, Nat.lt_of_lt_of_le h (Nat.le_add_right n n')⟩
    else
      if h' : n < k.1 then bd_var ⟨k.1 - 1, by omega⟩
      else (s ↑ᵇ n).cast (Nat.le_of_eq (Nat.add_comm n' n))
  | _, bd_func f, _ => bd_func f
  | _, bd_app t₁ t₂, s => bd_app (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)

notation:0 t "[" s " /// " n "]" => @subst_bounded_term _ n _ _ t s

@[simp]
lemma subst_bounded_term_var_lt {n n'} (s : bounded_term L n') (k : Fin (n + n' + 1))
    (h : k.1 < n) : (subst_bounded_term (bd_var k) s).fst = &k.1 := by
  simp [subst_bounded_term, h]

@[simp]
lemma subst_bounded_term_var_gt {n n'} (s : bounded_term L n') (k : Fin (n + n' + 1))
    (h : n < k.1) : (subst_bounded_term (bd_var k) s).fst = &(k.1 - 1) :=
  by
  have h' : ¬(k.1 < n) := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [subst_bounded_term, h', h]

@[simp]
lemma subst_bounded_term_var_eq {n n'} (s : bounded_term L n') (k : Fin (n + n' + 1))
    (h : k.1 = n) : (subst_bounded_term (bd_var k) s).fst = s.fst ↑' n # 0 :=
  by
  have h₂ : ¬(k.1 < n) := by omega
  have h₃ : ¬(n < k.1) := by omega
  simp only [subst_bounded_term, h₂, h₃, dite_false, bounded_preterm.cast_fst,
    lift_bounded_term, lift_bounded_term_fst s n 0]

@[simp]
lemma subst_bounded_term_bd_app {n n' l} (t₁ : bounded_preterm L (n + n' + 1) (l + 1))
    (t₂ : bounded_term L (n + n' + 1)) (s : bounded_term L n') :
    subst_bounded_term (bd_app t₁ t₂) s =
      bd_app (subst_bounded_term t₁ s) (subst_bounded_term t₂ s) :=
  rfl

@[simp]
lemma subst_bounded_term_fst {n n'} :
    ∀ {l} (t : bounded_preterm L (n + n' + 1) l) (s : bounded_term L n'),
      (subst_bounded_term t s).fst = subst_term t.fst s.fst n
  | _, bd_var k, s => by
    rcases Nat.lt_trichotomy k.1 n with h | h | h
    · simp [h, subst_bounded_term]
    · simp only [subst_bounded_term, show ¬(k.1 < n) from by omega,
        show ¬(n < k.1) from by omega, dite_false, bounded_preterm.cast_fst,
        lift_bounded_term, lift_bounded_term_fst s n 0]
      simp [h]
    · simp [subst_bounded_term, h, Nat.not_lt.mpr (Nat.le_of_lt h), ]
  | _, bd_func f, _ => rfl
  | _, bd_app t₁ t₂, s => by
    simp only [subst_bounded_term, bounded_preterm.fst, subst_term,
      subst_bounded_term_fst t₁ s, subst_bounded_term_fst t₂ s]

/-- Substitute the last (max) variable with a closed term. -/
@[expose]
def subst0_bounded_term {n l} (t : bounded_preterm L (n + 1) l) (s : bounded_term L n) :
    bounded_preterm L n l :=
  (subst_bounded_term (t.cast_eq (n + 1).zero_add.symm) s).cast_eq n.zero_add

@[simp]
lemma subst0_bounded_term_fst {n l} (t : bounded_preterm L (n + 1) l)
    (s : bounded_term L n) : (subst0_bounded_term t s).fst = subst_term t.fst s.fst 0 :=
  by simp [subst0_bounded_term, subst_bounded_term_fst]

/-- Substitute the last (max) variable with a closed term. -/
@[expose]
def substmax_bounded_term {n l} (t : bounded_preterm L (n + 1) l) (s : closed_term L) :
    bounded_preterm L n l :=
  subst_bounded_term t s

@[simp]
lemma substmax_bounded_term_bd_app {n l} (t₁ : bounded_preterm L (n + 1) (l + 1))
    (t₂ : bounded_term L (n + 1)) (s : closed_term L) :
    substmax_bounded_term (bd_app t₁ t₂) s =
      bd_app (substmax_bounded_term t₁ s) (substmax_bounded_term t₂ s) :=
  rfl

theorem substmax_eq_subst0_term {l} (t : bounded_preterm L 1 l) (s : closed_term L) :
    subst0_bounded_term t s = substmax_bounded_term t s := by
  apply bounded_preterm.eq;
  simp only [substmax_bounded_term, subst0_bounded_term, bounded_preterm.cast_eq_fst,
    subst_bounded_term_fst, bounded_preterm.cast_eq_fst]

theorem substmax_var_lt {n} (k : Fin (n + 1)) (s : closed_term L) (h : k.1 < n) :
    substmax_bounded_term (bd_var k : bounded_preterm L (n + 1) 0) s = bd_var ⟨k.1, h⟩ :=
  by apply bounded_preterm.eq; simp [substmax_bounded_term, subst_bounded_term, h]

theorem substmax_var_eq {n} (k : Fin (n + 1)) (s : closed_term L) (h : k.1 = n) :
    substmax_bounded_term (bd_var k : bounded_preterm L (n + 1) 0) s = s.cast0 n :=
  by
  apply bounded_preterm.eq
  simp only [substmax_bounded_term, closed_preterm.cast0, bounded_preterm.cast_fst]
  simp only [subst_bounded_term, show ¬(k.1 < n) from by omega,
    show ¬(n < k.1) from by omega, dite_false, bounded_preterm.cast_fst,
    lift_bounded_term, lift_bounded_term_fst s n 0, bounded_preterm.cast_fst]
    -- Goal: s.fst ↑' n # 0 = s.fst
      -- s : closed_term L = bounded_preterm L 0 0, so bound is 0 ≤ 0
      -- (lift at position 0)

  exact lift_bounded_term_irrel s n (Nat.zero_le 0)

@[expose]
def bounded_term_of_function {l n} (f : L.functions l) :
    Arity' (bounded_term L n) (bounded_term L n) l :=
  Arity'.of_dvector_map (bd_apps (bd_func f))

/-! ### realize_bounded_term lemmas -/


@[simp]
lemma realize_bounded_term_bd_app {S : Structure L} {n l}
    (t : bounded_preterm L n (l + 1)) (s : bounded_term L n) (xs : DVec S n)
    (xs' : DVec S l) :
    realize_bounded_term xs (bd_app t s) xs' =
      realize_bounded_term xs t (DVec.cons (realize_bounded_term xs s DVec.nil) xs') :=
  rfl

@[simp]
lemma realize_closed_term_bd_apps {S : Structure L} {l} (t : closed_preterm L l)
    (ts : DVec (closed_term L) l) :
    realize_closed_term S (bd_apps t ts) =
      realize_bounded_term DVec.nil t
        (ts.map (fun t' => realize_bounded_term DVec.nil t' DVec.nil)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => exact ih (bd_app t x)

lemma realize_bounded_term_bd_apps {S : Structure L} {n l} (xs : DVec S n)
    (t : bounded_preterm L n l) (ts : DVec (bounded_term L n) l) :
    realize_bounded_term xs (bd_apps t ts) DVec.nil =
      realize_bounded_term xs t (ts.map (fun t => realize_bounded_term xs t DVec.nil)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs' ih => exact ih (bd_app t x)

@[simp]
lemma realize_cast_bounded_term {S : Structure L} {n m} {h : n ≤ m} {t : bounded_term L n}
    {v : DVec S m} :
    realize_bounded_term v (t.cast h) DVec.nil =
      realize_bounded_term (v.trunc n h) t DVec.nil :=
  by
  revert t
  apply bounded_term.rec
  · intro k
    simp only [bounded_preterm.cast, realize_bounded_term, DVec.trunc_nth]
  · intro l f ts ih_ts
    simp only [bounded_preterm.cast_bd_apps, realize_bounded_term_bd_apps]
    apply congrArg
    trans
      DVec.map (fun x => realize_bounded_term v (bounded_preterm.cast h x) DVec.nil) ts
    · exact DVec.map_map _ _ ts
    · apply DVec.map_congr_pmem
      intro x hx
      exact ih_ts x hx

/-- When realizing a closed term, the realizing dvector is
irrelevant. -/
@[simp]
lemma realize_closed_term_v_irrel {S : Structure L} {n} {v : DVec S n}
    {t : bounded_term L 0} :
    realize_bounded_term v (t.cast (Nat.zero_le n)) DVec.nil = realize_closed_term S t :=
  by simp [realize_cast_bounded_term]

/-! ## bounded_preformula, bounded_formula, presentence, sentence
(src/fol.lean lines 1660-2200) -/


variable (L)

/-- A bounded pre-formula: `bounded_preformula L n l` is a
partially applied formula
    with at most `n` free de Bruijn variables (< n), needing `l` more
    term arguments.
    `bounded_formula L n = bounded_preformula L n 0`, and `sentence L
    = bounded_preformula L 0 0`. -/
inductive bounded_preformula (L : Language.{u}) : ℕ → ℕ → Type u
  | bd_falsum : ∀ {n}, bounded_preformula L n 0
  | bd_equal : ∀ {n} (_t₁ _t₂ : bounded_term L n), bounded_preformula L n 0
  | bd_rel : ∀ {n l : ℕ} (_R : L.relations l), bounded_preformula L n l
  |
  bd_apprel :
    ∀ {n l} (_f : bounded_preformula L n (l + 1)) (_t : bounded_term L n),
      bounded_preformula L n l
  | bd_imp : ∀ {n} (_f₁ _f₂ : bounded_preformula L n 0), bounded_preformula L n 0
  | bd_all : ∀ {n} (_f : bounded_preformula L (n + 1) 0), bounded_preformula L n 0

export bounded_preformula (bd_falsum bd_equal bd_rel bd_apprel bd_imp bd_all)

@[reducible, expose]
def bounded_formula (n : ℕ) :=
  bounded_preformula L n 0
@[reducible, expose]
def presentence (l : ℕ) :=
  bounded_preformula L 0 l
@[reducible, expose]
def sentence :=
  presentence L 0

variable {L}

instance nonempty_bounded_formula (n : ℕ) : Nonempty (bounded_formula L n) :=
  ⟨bd_falsum⟩

/-! ### bounded_preformula notations -/
-- Note: ≃ and ⟹ and ∀' are already declared for
-- preformula/preterm above (scoped).
-- We overload them here for bounded_preformula. Since these are
-- scoped notations,
-- we extend existing ones in the Fol namespace.

-- bd_falsum notation conflicts with preformula.falsum ⊥'; we use
-- bd_falsum directly.
-- The bounded equality and implication will reuse the same
-- notation symbols.


-- Note: ≃ and ⟹ and ∀' are already declared for
-- preformula/preterm above (scoped).
-- We overload them here for bounded_preformula. Since these are
-- scoped notations,
-- we extend existing ones in the Fol namespace.

-- bd_falsum notation conflicts with preformula.falsum ⊥'; we use
-- bd_falsum directly.
-- The bounded equality and implication will reuse the same
-- notation symbols.

@[expose]
def bd_not {n} (f : bounded_formula L n) : bounded_formula L n :=
  bd_imp f bd_falsum

scoped prefix:max "∼ᵇ" => Fol.bd_not

@[expose]
def bd_and {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_not (bd_imp f₁ (bd_not f₂))

scoped infixr:69 " ⊓ᵇ " => Fol.bd_and

@[expose]
def bd_or {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_imp (bd_not f₁) f₂

scoped infixr:68 " ⊔ᵇ " => Fol.bd_or

@[expose]
def bd_biimp {n} (f₁ f₂ : bounded_formula L n) : bounded_formula L n :=
  bd_and (bd_imp f₁ f₂) (bd_imp f₂ f₁)

scoped infix:61 " ⇔ᵇ " => Fol.bd_biimp

@[expose]
def bd_ex {n} (f : bounded_formula L (n + 1)) : bounded_formula L n :=
  bd_not (bd_all (bd_not f))

scoped prefix:110 "∃ᵇ" => Fol.bd_ex

/-! ### bd_apps_rel -/


@[simp, expose]
def bd_apps_rel {n} :
    ∀ {l} (_f : bounded_preformula L n l) (_ts : DVec (bounded_term L n) l),
      bounded_formula L n
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => bd_apps_rel (bd_apprel f t) ts

@[simp]
lemma bd_apps_rel_zero {n} (f : bounded_formula L n) (ts : DVec (bounded_term L n) 0) :
    bd_apps_rel f ts = f := by cases ts; rfl

/-! ### namespace bounded_preformula -/


namespace bounded_preformula

/-- Forget boundedness: map a bounded_preformula to an ordinary
preformula. -/
@[simp, expose]
protected def fst : ∀ {n l}, bounded_preformula L n l → @preformula L l
  | _, _, bd_falsum => preformula.falsum
  | _, _, bd_equal t₁ t₂ => preformula.equal t₁.fst t₂.fst
  | _, _, bd_rel R => preformula.rel R
  | _, _, bd_apprel f t => preformula.apprel f.fst t.fst
  | _, _, bd_imp f₁ f₂ => preformula.imp f₁.fst f₂.fst
  | _, _, bd_all f => preformula.all f.fst

@[simp]
lemma fst_bd_not {n} {f : bounded_formula L n} : (bd_not f).fst = not' f.fst :=
  rfl

@[simp]
lemma fst_bd_or {n} {f₁ f₂ : bounded_formula L n} :
    (bd_or f₁ f₂).fst = or' f₁.fst f₂.fst :=
  rfl

lemma fst_bd_imp {n} {f₁ f₂ : bounded_formula L n} :
    (bd_imp f₁ f₂).fst = preformula.imp f₁.fst f₂.fst :=
  rfl

@[simp]
lemma fst_bd_and {n} {f₁ f₂ : bounded_formula L n} :
    (bd_and f₁ f₂).fst = and' f₁.fst f₂.fst :=
  rfl

@[simp]
lemma fst_bd_ex {n} {f : bounded_formula L (n + 1)} : (bd_ex f).fst = ex' f.fst :=
  rfl

/-- Equality of bounded_preformulas is determined by their
underlying preformulas. -/
@[ext]
protected theorem eq :
    ∀ {n l} {f₁ f₂ : bounded_preformula L n l}, f₁.fst = f₂.fst → f₁ = f₂
  | _, _, bd_falsum, bd_falsum, _ => rfl
  | _, _, bd_equal t₁ t₂, bd_equal t₁' t₂', h =>
    by
    simp only [bounded_preformula.fst, preformula.equal.injEq] at h
    exact congrArg₂ bd_equal (bounded_preterm.eq h.1) (bounded_preterm.eq h.2)
  | _, _, bd_rel R, bd_rel R', h =>
    by
    simp only [bounded_preformula.fst, preformula.rel.injEq] at h
    exact congrArg bd_rel h
  | _, _, bd_apprel f t, bd_apprel f' t', h =>
    by
    simp only [bounded_preformula.fst, preformula.apprel.injEq] at h
    exact congrArg₂ bd_apprel (bounded_preformula.eq h.1) (bounded_preterm.eq h.2)
  | _, _, bd_imp f₁ f₂, bd_imp f₁' f₂', h =>
    by
    simp only [bounded_preformula.fst, preformula.imp.injEq] at h
    exact congrArg₂ bd_imp (bounded_preformula.eq h.1) (bounded_preformula.eq h.2)
  | _, _, bd_all f, bd_all f', h =>
    by
    simp only [bounded_preformula.fst, preformula.all.injEq] at h
    exact
      congrArg bd_all
        (bounded_preformula.eq h)
          -- cross-constructor cases: fst is in different constructors

  | _, _, bd_falsum, bd_equal _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_falsum, bd_rel _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_falsum, bd_imp _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_falsum, bd_all _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_equal _ _, bd_falsum, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_equal _ _, bd_imp _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_equal _ _, bd_all _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_rel _, bd_apprel _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_apprel _ _, bd_rel _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_imp _ _, bd_falsum, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_imp _ _, bd_equal _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_imp _ _, bd_all _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_all _, bd_falsum, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_all _, bd_equal _ _, h => by simp [bounded_preformula.fst] at h
  | _, _, bd_all _, bd_imp _ _, h => by simp [bounded_preformula.fst] at h

/-- Cast a bounded_preformula to one with a larger variable
bound. -/
@[simp, expose]
protected def cast {n m} (h : n ≤ m) :
    ∀ {l}, bounded_preformula L n l → bounded_preformula L m l
  | _, bd_falsum => bd_falsum
  | _, bd_equal t₁ t₂ => bd_equal (t₁.cast h) (t₂.cast h)
  | _, bd_rel R => bd_rel R
  | _, bd_apprel f t => bd_apprel (f.cast h) (t.cast h)
  | _, bd_imp f₁ f₂ => bd_imp (f₁.cast h) (f₂.cast h)
  | _, bd_all f => bd_all (f.cast (Nat.succ_le_succ h))

@[simp]
lemma cast_irrel :
    ∀ {n m l} (h h' : n ≤ m) (f : bounded_preformula L n l), f.cast h = f.cast h' := by
  intros; rfl

@[simp]
lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (f : bounded_preformula L n l), f.cast h = f
  | _, bd_falsum => rfl
  | _, bd_equal t₁ t₂ => by
    simp only [bounded_preformula.cast, bounded_preterm.cast_rfl t₁,
      bounded_preterm.cast_rfl t₂]
  | _, bd_rel _ => rfl
  | _, bd_apprel f t => by
    simp only [bounded_preformula.cast, cast_rfl f, bounded_preterm.cast_rfl t]
  | _, bd_imp f₁ f₂ => by simp [bounded_preformula.cast, cast_rfl f₁, cast_rfl f₂]
  | _, bd_all f => by simp [bounded_preformula.cast, cast_rfl f]

@[expose]
protected def cast_eq {n m l} (h : n = m) (f : bounded_preformula L n l) :
    bounded_preformula L m l :=
  f.cast (Nat.le_of_eq h)

@[expose]
protected def cast_eqr {n m l} (h : n = m) (f : bounded_preformula L m l) :
    bounded_preformula L n l :=
  f.cast (Nat.le_of_eq h.symm)

lemma cast_bd_apps_rel {n m} (h : n ≤ m) :
    ∀ {l} (f : bounded_preformula L n l) (ts : DVec (bounded_term L n) l),
      (bd_apps_rel f ts).cast h = bd_apps_rel (f.cast h) (ts.map (fun t => t.cast h))
  | _, f, DVec.nil => rfl
  | _, f, DVec.cons x xs => by
    simp only [bd_apps_rel, DVec.map]
    exact cast_bd_apps_rel h (bd_apprel f x) xs

@[expose]
protected def cast1 {n l} (f : bounded_preformula L n l) :
    bounded_preformula L (n + 1) l :=
  f.cast (Nat.le_add_right n 1)

@[simp]
lemma cast_fst :
    ∀ {l n m} (h : n ≤ m) (f : bounded_preformula L n l), (f.cast h).fst = f.fst
  | _, _, _, _, bd_falsum => rfl
  | _, _, _, h, bd_equal t₁ t₂ => by
    simp only [bounded_preformula.cast, bounded_preformula.fst,
      bounded_preterm.cast_fst h t₁, bounded_preterm.cast_fst h t₂]
  | _, _, _, _, bd_rel _ => rfl
  | _, _, _, h, bd_apprel f t => by
    simp only [bounded_preformula.cast, bounded_preformula.fst, cast_fst h f,
      bounded_preterm.cast_fst h t]
  | _, _, _, h, bd_imp f₁ f₂ => by
    simp [bounded_preformula.cast, cast_fst h f₁, cast_fst h f₂]
  | _, _, _, h, bd_all f => by
    simp [bounded_preformula.cast, cast_fst (Nat.succ_le_succ h) f]

@[simp]
lemma cast_eq_fst {l n m} (h : n = m) (f : bounded_preformula L n l) :
    (f.cast_eq h).fst = f.fst :=
  cast_fst _ f

@[simp]
lemma cast1_fst {l n} (f : bounded_preformula L n l) : f.cast1.fst = f.fst :=
  cast_fst _ f

@[simp]
lemma cast_eq_rfl {l n m} (h : n = m) (f : bounded_preformula L n l) :
    (f.cast_eq h).cast_eq h.symm = f := by apply bounded_preformula.eq; simp [cast_eq_fst]

@[simp]
lemma cast_eq_irrel {l n m} (h h' : n = m) (f : bounded_preformula L n l) :
    f.cast_eq h = f.cast_eq h' :=
  rfl

@[simp]
lemma cast_eq_all {n m} (h : n = m) {f : bounded_preformula L (n + 1) 0} :
    (bd_all f).cast_eq h = bd_all (f.cast_eq (congrArg (· + 1) h)) :=
  rfl

@[simp]
lemma cast_eq_trans {n m o l} {h : n = m} {h' : m = o} {f : bounded_preformula L n l} :
    (f.cast_eq h).cast_eq h' = f.cast_eq (h.trans h') := by
  apply bounded_preformula.eq;
  simp [cast_eq_fst]

lemma cast_eq_hrfl {n m l} {h : n = m} {f : bounded_preformula L n l} :
    HEq (f.cast_eq h) f := by
  -- TODO: port from src/fol.lean:1801-1802 (cast_eq_hrfl,
    -- heterogeneous equality)

  subst h
  apply heq_of_eq
  apply bounded_preformula.eq; simp [bounded_preformula.cast_eq_fst]

/-- A bounded_preformula is quantifier-free if its underlying
preformula is. -/
@[expose]
def quantifier_free {l n} (f : bounded_preformula L n l) : Prop :=
  Fol.quantifier_free f.fst

end bounded_preformula

/-! ### namespace presentence -/


namespace presentence

@[reducible, expose]
protected def cast0 {l} (n : ℕ) (f : presentence L l) : bounded_preformula L n l :=
  f.cast (Nat.zero_le n)

@[simp]
lemma cast0_fst {l} (n : ℕ) (f : presentence L l) : (f.cast0 n).fst = f.fst :=
  bounded_preformula.cast_fst _ f

end presentence

/-! ### Irrel lemmas for bounded formulas -/


lemma lift_bounded_formula_irrel :
    ∀ {n l} (f : bounded_preformula L n l) (n') {m : ℕ} (_h : n ≤ m),
      lift_formula_at f.fst n' m = f.fst
  | _, _, bd_falsum, _, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', m, h => by
    simp [bounded_preformula.fst, lift_bounded_term_irrel t₁ n' h,
      lift_bounded_term_irrel t₂ n' h]
  | _, _, bd_rel _, _, _, _ => rfl
  | _, _, bd_apprel f t, n', m, h => by
    simp [bounded_preformula.fst, lift_bounded_formula_irrel f n' h,
      lift_bounded_term_irrel t n' h]
  | _, _, bd_imp f₁ f₂, n', m, h => by
    simp [bounded_preformula.fst, lift_bounded_formula_irrel f₁ n' h,
      lift_bounded_formula_irrel f₂ n' h]
  | _, _, bd_all f, n', m, h =>
    by
    simp only [bounded_preformula.fst, lift_formula_at, preformula.all.injEq]
    exact lift_bounded_formula_irrel f n' (Nat.succ_le_succ h)

lemma lift_sentence_irrel (f : sentence L) : lift_formula f.fst 1 = f.fst :=
  lift_bounded_formula_irrel f 1 (Nat.le_refl 0)

@[simp]
lemma subst_bounded_formula_irrel :
    ∀ {n l} (f : bounded_preformula L n l) {n'} (s : term L) (_h : n ≤ n'),
      subst_formula f.fst s n' = f.fst
  | _, _, bd_falsum, _, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', s, h => by
    simp [bounded_preformula.fst, subst_bounded_term_irrel t₁ s h,
      subst_bounded_term_irrel t₂ s h]
  | _, _, bd_rel _, _, _, _ => rfl
  | _, _, bd_apprel f t, n', s, h => by
    simp [bounded_preformula.fst, subst_bounded_formula_irrel f s h,
      subst_bounded_term_irrel t s h]
  | _, _, bd_imp f₁ f₂, n', s, h => by
    simp [bounded_preformula.fst, subst_bounded_formula_irrel f₁ s h,
      subst_bounded_formula_irrel f₂ s h]
  | _, _, bd_all f, n', s, h =>
    by
    simp only [bounded_preformula.fst, subst_formula, preformula.all.injEq]
    exact subst_bounded_formula_irrel f s (Nat.succ_le_succ h)

lemma subst_sentence_irrel (f : sentence L) (n : ℕ) (s : term L) :
    subst_formula f.fst s n = f.fst :=
  subst_bounded_formula_irrel f s (Nat.zero_le n)

/-! ### realize_bounded_formula -/


@[simp, expose]
def realize_bounded_formula {S : Structure L} :
    ∀ {n l} (_v : DVec S n) (_f : bounded_preformula L n l) (_xs : DVec S l), Prop
  | _, _, _v, bd_falsum, _ => False
  | _, _, v, bd_equal t₁ t₂, _ =>
    realize_bounded_term v t₁ DVec.nil = realize_bounded_term v t₂ DVec.nil
  | _, _, _, bd_rel R, xs => S.rel_map R xs
  | _, _, v, bd_apprel f t, xs =>
    realize_bounded_formula v f (DVec.cons (realize_bounded_term v t DVec.nil) xs)
  | _, _, v, bd_imp f₁ f₂, xs =>
    realize_bounded_formula v f₁ xs → realize_bounded_formula v f₂ xs
  | _, _, v, bd_all f, xs => ∀ x : S, realize_bounded_formula (DVec.cons x v) f xs

@[reducible, expose]
def realize_sentence (S : Structure L) (f : sentence L) : Prop :=
  realize_bounded_formula (DVec.nil : DVec S 0) f DVec.nil

scoped infix:51 " ⊨ₘ " => Fol.realize_sentence

/-! ### realize_bounded_formula lemmas -/
-- Helper for realize_bounded_formula_iff: structural recursion
-- over f


-- Helper for realize_bounded_formula_iff: structural recursion
-- over f
theorem realize_bounded_formula_iff_aux {S : Structure L} :
    ∀ {n l} (f : bounded_preformula L n l) (v₁ : DVec S n) (v₂ : ℕ → S)
      (_hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) (xs : DVec S l),
      realize_bounded_formula v₁ f xs ↔ realize_formula v₂ f.fst xs
  | _, _, bd_falsum, _, _, _, _ => Iff.rfl
  | _, _, bd_equal t₁ t₂, v₁, v₂, hv, _ => by
    simp [realize_bounded_formula, bounded_preformula.fst, realize_formula,
      realize_bounded_term_eq hv t₁ DVec.nil, realize_bounded_term_eq hv t₂ DVec.nil]
  | _, _, bd_rel _, _, _, _, _ => Iff.rfl
  | _, _, bd_apprel f t, v₁, v₂, hv, xs =>
    by
    simp only [realize_bounded_formula, bounded_preformula.fst, realize_formula,
      realize_bounded_term_eq hv t DVec.nil]
    exact realize_bounded_formula_iff_aux f v₁ v₂ hv _
  | _, _, bd_imp f₁ f₂, v₁, v₂, hv, xs =>
    by
    simp only [realize_bounded_formula, bounded_preformula.fst, realize_formula]
    exact
      Iff.imp (realize_bounded_formula_iff_aux f₁ v₁ v₂ hv xs)
        (realize_bounded_formula_iff_aux f₂ v₁ v₂ hv xs)
  | n, _, bd_all f, v₁, v₂, hv, _ =>
    by
    simp only [realize_bounded_formula, bounded_preformula.fst, realize_formula]
    apply forall_congr'
    intro x
    have hv' : ∀ k (hk : k < n + 1), (DVec.cons x v₁).nth k hk = subst_realize v₂ x 0 k :=
      by
      intro k hk
      cases k with
      | zero => simp [DVec.nth, subst_realize]
      | succ k =>
        have hk' : k < n := Nat.lt_of_succ_lt_succ hk
        simp only [DVec.nth, subst_realize, Nat.zero_lt_succ, ↓reduceIte,
          Nat.add_sub_cancel]
        exact hv k hk'
    simp only [DVec.zero_eq]
    exact
      realize_bounded_formula_iff_aux f (DVec.cons x v₁) (subst_realize v₂ x 0) hv'
        DVec.nil

lemma realize_bounded_formula_iff {S : Structure L} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) {l} (f : bounded_preformula L n l)
    (xs : DVec S l) : realize_bounded_formula v₁ f xs ↔ realize_formula v₂ f.fst xs :=
  realize_bounded_formula_iff_aux f v₁ v₂ hv xs

lemma realize_bounded_formula_iff_of_fst {S : Structure L} {n} {v₁ w₁ : DVec S n}
    {v₂ w₂ : ℕ → S} (hv₁ : ∀ k (hk : k < n), v₁.nth k hk = v₂ k)
    (hw₁ : ∀ k (hk : k < n), w₁.nth k hk = w₂ k) {l₁ l₂} (t₁ : bounded_preformula L n l₁)
    (t₂ : bounded_preformula L n l₂) (xs₁ : DVec S l₁) (xs₂ : DVec S l₂)
    (H : realize_formula v₂ t₁.fst xs₁ ↔ realize_formula w₂ t₂.fst xs₂) :
    (realize_bounded_formula v₁ t₁ xs₁ ↔ realize_bounded_formula w₁ t₂ xs₂) :=
  by
  rw [realize_bounded_formula_iff hv₁, realize_bounded_formula_iff hw₁]
  exact H

lemma realize_bounded_formula_irrel' {S : Structure L} {n n'} {v₁ : DVec S n}
    {v₂ : DVec S n'} (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn') {l}
    (f : bounded_preformula L n l) (f' : bounded_preformula L n' l) (hf : f.fst = f'.fst)
    (xs : DVec S l) :
    realize_bounded_formula v₁ f xs ↔ realize_bounded_formula v₂ f' xs := by
  induction f generalizing n' with
  | bd_falsum =>
    cases f' with
    | bd_falsum => exact Iff.rfl
    | _ => simp [bounded_preformula.fst] at hf
  | bd_equal t₁ t₂ =>
    cases f' with
    | bd_equal t₁'
      t₂' =>
      simp only [bounded_preformula.fst, preformula.equal.injEq] at hf
      simp [realize_bounded_formula, realize_bounded_term_irrel' h t₁ t₁' hf.1,
        realize_bounded_term_irrel' h t₂ t₂' hf.2]
    | _ => simp [bounded_preformula.fst] at hf
  | bd_rel =>
    cases f' with
    | bd_rel =>
      simp only [bounded_preformula.fst, preformula.rel.injEq] at hf; subst hf;
      exact Iff.rfl
    | _ => simp [bounded_preformula.fst] at hf
  | bd_apprel f t ih =>
    cases f' with
    | bd_apprel f'
      t' =>
      simp only [bounded_preformula.fst, preformula.apprel.injEq] at hf
      simp only [realize_bounded_formula]
      rw [realize_bounded_term_irrel' h t t' hf.2 DVec.nil]
      exact ih h f' hf.1 _
    | _ => simp [bounded_preformula.fst] at hf
  | bd_imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | bd_imp f₁'
      f₂' =>
      simp only [bounded_preformula.fst, preformula.imp.injEq] at hf
      simp only [realize_bounded_formula]
      exact Iff.imp (ih₁ h f₁' hf.1 xs) (ih₂ h f₂' hf.2 xs)
    | _ => simp [bounded_preformula.fst] at hf
  | bd_all f ih =>
    cases f' with
    | bd_all
      f' =>
      simp only [bounded_preformula.fst, preformula.all.injEq] at hf
      simp only [realize_bounded_formula]
      apply forall_congr'
      intro x
      apply ih
      · intro m hm hm'
        cases m with
        | zero => simp [DVec.nth]
        | succ m => exact h m (Nat.lt_of_succ_lt_succ hm) (Nat.lt_of_succ_lt_succ hm')
      · exact hf
    | _ => simp [bounded_preformula.fst] at hf

lemma realize_bounded_formula_irrel {S : Structure L} {n} {v₁ : DVec S n}
    (f : bounded_formula L n) (f' : sentence L) (hf : f.fst = f'.fst) (xs : DVec S 0) :
    realize_bounded_formula v₁ f xs ↔ realize_sentence S f' :=
  by
  cases xs
  apply realize_bounded_formula_irrel'
  · intro m _hm hm'
    exact absurd hm' (Nat.not_lt_zero m)
  · exact hf

@[simp]
lemma realize_bounded_formula_cast_eq_irrel {S : Structure L} {n m l} {h : n = m}
    {v : DVec S m} {f : bounded_preformula L n l} {xs : DVec S l} :
    realize_bounded_formula v (f.cast_eq h) xs =
      realize_bounded_formula (v.cast h.symm) f xs :=
  by subst h; simp [bounded_preformula.cast_eq, bounded_preformula.cast_rfl, DVec.cast]

/-! ### bounded_formula_of_relation -/


@[expose]
def bounded_formula_of_relation {l n} (R : L.relations l) :
    Arity' (bounded_term L n) (bounded_formula L n) l :=
  Arity'.of_dvector_map (bd_apps_rel (bd_rel R))

/-! ### Recursors for bounded_preformula / bounded_formula
(src/fol.lean lines 1984-2038) -/


/-- Recursor for bounded_preformula at n+1 (i.e., where there is
at least one free variable). -/
@[expose]
def bounded_preformula.rec1 {C : ∀ n l, bounded_preformula L (n + 1) l → Sort v}
    (H0 : ∀ {n}, C n 0 bd_falsum)
    (H1 : ∀ {n} (t₁ t₂ : bounded_term L (n + 1)), C n 0 (bd_equal t₁ t₂))
    (H2 : ∀ {n l : ℕ} (R : L.relations l), C n l (bd_rel R))
    (H3 : ∀ {n l : ℕ} (f : bounded_preformula L (n + 1) (l + 1)) (t : bounded_term L (n + 1))
        (_ih : C n (l + 1) f), C n l (bd_apprel f t))
    (H4 : ∀ {n} (f₁ f₂ : bounded_formula L (n + 1)) (_ih₁ : C n 0 f₁) (_ih₂ : C n 0 f₂),
        C n 0 (bd_imp f₁ f₂))
    (H5 : ∀ {n} (f : bounded_formula L (n + 2)) (_ih : C (n + 1) 0 f), C n 0 (bd_all f)) :
    ∀ {{n l : ℕ}} (f : bounded_preformula L (n + 1) l), C n l f :=
  -- Port from src/fol.lean:1984-2004: define C' with n=0 case =
    -- PUnit, then use full rec

  let C' : ∀ n l, bounded_preformula L n l → Sort v := fun n =>
    match n with
    | 0 => fun _l _f => PUnit
    | k + 1 => C k
  let rec key : ∀ (n l : ℕ) (f : bounded_preformula L n l), C' n l f
    | 0, _, _ => PUnit.unit
    | n + 1, _, bd_falsum => H0
    | n + 1, _, bd_equal t₁ t₂ => H1 t₁ t₂
    | n + 1, _, bd_rel R => H2 R
    | n + 1, _, bd_apprel f t => H3 f t (key (n + 1) _ f)
    | n + 1, _, bd_imp f₁ f₂ => H4 f₁ f₂ (key (n + 1) _ f₁) (key (n + 1) _ f₂)
    | n + 1, _, bd_all f => H5 f (key (n + 2) _ f)
  fun {{n}} {{_l}} f => key (n + 1) _ f

/-- Recursor for bounded_formula at n+1 (fully applied). -/
@[expose]
def bounded_formula.rec1 {C : ∀ n, bounded_formula L (n + 1) → Sort v}
    (hfalsum : ∀ {n}, C n bd_falsum)
    (hequal : ∀ {n} (t₁ t₂ : bounded_term L (n + 1)), C n (bd_equal t₁ t₂))
    (hrel : ∀ {n l : ℕ} (R : L.relations l) (ts : DVec (bounded_term L (n + 1)) l),
        C n (bd_apps_rel (bd_rel R) ts))
    (himp : ∀ {n} {f₁ f₂ : bounded_formula L (n + 1)} (_ih₁ : C n f₁) (_ih₂ : C n f₂),
        C n (bd_imp f₁ f₂))
    (hall : ∀ {n} {f : bounded_formula L (n + 2)} (_ih : C (n + 1) f), C n (bd_all f))
    {{n : ℕ}} (f : bounded_formula L (n + 1)) : C n f :=
  -- Use a helper that handles partially-applied formulas via dvec
    -- accumulator

  let rec go :
    ∀ {n' l} (f' : bounded_preformula L (n' + 1) l)
      (ts : DVec (bounded_term L (n' + 1)) l), C n' (bd_apps_rel f' ts)
    | _, _, bd_falsum, ts => by rw [DVec.zero_eq ts]; exact hfalsum
    | _, _, bd_equal t₁ t₂, ts => by rw [DVec.zero_eq ts]; exact hequal t₁ t₂
    | _, _, bd_rel R, ts => hrel R ts
    | _, _, bd_apprel f' t, ts => go f' (DVec.cons t ts)
    | _, _, bd_imp f₁ f₂, ts => by
      rw [DVec.zero_eq ts]
      exact himp (go f₁ DVec.nil) (go f₂ DVec.nil)
    | _, _, bd_all f', ts => by
      rw [DVec.zero_eq ts]
      exact hall (go f' DVec.nil)
  bd_apps_rel_zero f DVec.nil ▸ go f DVec.nil

/-- Recursor for bounded_formula at any n. -/
@[expose]
def bounded_formula.rec {C : ∀ n, bounded_formula L n → Sort v}
    (hfalsum : ∀ {n}, C n bd_falsum)
    (hequal : ∀ {n} (t₁ t₂ : bounded_term L n), C n (bd_equal t₁ t₂))
    (hrel : ∀ {n l : ℕ} (R : L.relations l) (ts : DVec (bounded_term L n) l),
        C n (bd_apps_rel (bd_rel R) ts))
    (himp : ∀ {n} {f₁ f₂ : bounded_formula L n} (_ih₁ : C n f₁) (_ih₂ : C n f₂),
        C n (bd_imp f₁ f₂))
    (hall : ∀ {n} {f : bounded_formula L (n + 1)} (_ih : C (n + 1) f), C n (bd_all f)) :
    ∀ {{n : ℕ}} (f : bounded_formula L n), C n f :=
  let rec go :
    ∀ {n l} (f : bounded_preformula L n l) (ts : DVec (bounded_term L n) l),
      C n (bd_apps_rel f ts)
    | _, _, bd_falsum, ts => by simp only [DVec.zero_eq ts]; exact hfalsum
    | _, _, bd_equal t₁ t₂, ts => by simp only [DVec.zero_eq ts]; exact hequal t₁ t₂
    | _, _, bd_rel R, ts => hrel R ts
    | _, _, bd_apprel f t, ts => go f (DVec.cons t ts)
    | _, _, bd_imp f₁ f₂, ts => by
      simp only [DVec.zero_eq ts]
      exact himp (go f₁ DVec.nil) (go f₂ DVec.nil)
    | _, _, bd_all f, ts => by
      simp only [DVec.zero_eq ts]
      exact hall (go f DVec.nil)
  fun {{n}} f => bd_apps_rel_zero f DVec.nil ▸ go f DVec.nil

/-! ### substmax_bounded_formula — substitute the max (last)
variable -/


/-- Substitute variable at position `n` in a formula with bound
`n+1`. -/
@[simp, expose]
def subst_bounded_formula :
    ∀ {n n' n'' l} (_f : bounded_preformula L n'' l) (_s : bounded_term L n')
      (_h : n + n' + 1 = n''), bounded_preformula L (n + n') l
  | _, _, _, _, bd_falsum, _, _ => bd_falsum
  | _, _, _, _, bd_equal t₁ t₂, s, rfl =>
    bd_equal (subst_bounded_term t₁ s) (subst_bounded_term t₂ s)
  | _, _, _, _, bd_rel R, _, _ => bd_rel R
  | _, _, _, _, bd_apprel f t, s, rfl =>
    bd_apprel (subst_bounded_formula f s rfl) (subst_bounded_term t s)
  | _, _, _, _, bd_imp f₁ f₂, s, rfl =>
    bd_imp (subst_bounded_formula f₁ s rfl) (subst_bounded_formula f₂ s rfl)
  | n, n', _, _, bd_all f, s, rfl =>
    -- f : bounded_preformula L (n + n' + 1 + 1) 0
          -- we call subst with n+1, n', giving h : (n+1)+n'+1 = n+n'+1+1
          -- (proved by omega)
          -- result: bounded_preformula L ((n+1)+n') 0 = bounded_preformula
          -- L (n+n'+1) 0
          -- then cast to n+n'+1 = n+n'+1 which is trivially true
    bd_all
      ((subst_bounded_formula f s (by omega : (n + 1) + n' + 1 = n + n' + 1 + 1)).cast_eq
        (show (n + 1) + n' = n + n' + 1 from by omega))

@[simp]
lemma subst_bounded_formula_fst :
    ∀ {n n' n'' l} (f : bounded_preformula L n'' l) (s : bounded_term L n')
      (h : n + n' + 1 = n''),
      (subst_bounded_formula f s h).fst = subst_formula f.fst s.fst n
  | _, _, _, _, bd_falsum, _, _ => rfl
  | _, _, _, _, bd_equal t₁ t₂, s, rfl => by
    simp only [subst_bounded_formula, bounded_preformula.fst, subst_formula,
      subst_bounded_term_fst t₁ s, subst_bounded_term_fst t₂ s]
  | _, _, _, _, bd_rel _, _, _ => rfl
  | _, _, _, _, bd_apprel f t, s, rfl => by
    simp only [subst_bounded_formula, bounded_preformula.fst, subst_formula,
      subst_bounded_formula_fst f s rfl, subst_bounded_term_fst t s]
  | _, _, _, _, bd_imp f₁ f₂, s, rfl => by
    simp [subst_bounded_formula, subst_bounded_formula_fst f₁ s rfl,
      subst_bounded_formula_fst f₂ s rfl]
  | n, n', _, _, bd_all f, s, rfl =>
    by
    simp only [subst_bounded_formula, bounded_preformula.fst,
      bounded_preformula.cast_eq_fst]
    rw [subst_bounded_formula_fst f s (by omega : (n + 1) + n' + 1 = n + n' + 1 + 1)]
    simp [subst_formula]

@[simp, expose]
def substmax_bounded_formula {n l} (f : bounded_preformula L (n + 1) l)
    (s : closed_term L) : bounded_preformula L n l :=
  subst_bounded_formula f s rfl

@[simp]
lemma substmax_bounded_formula_fst {n l} (f : bounded_preformula L (n + 1) l)
    (s : closed_term L) :
    (substmax_bounded_formula f s).fst = subst_formula f.fst s.fst n := by
  exact subst_bounded_formula_fst (n := n) f s rfl

@[simp]
lemma substmax_bounded_formula_bd_all {n} (f : bounded_formula L (n + 2))
    (s : closed_term L) :
    substmax_bounded_formula (bd_all f) s = bd_all (substmax_bounded_formula f s) := by
  apply bounded_preformula.eq; simp

lemma substmax_bounded_formula_bd_apps_rel {n l} (f : bounded_preformula L (n + 1) l)
    (t : closed_term L) (ts : DVec (bounded_term L (n + 1)) l) :
    substmax_bounded_formula (bd_apps_rel f ts) t =
      bd_apps_rel (substmax_bounded_formula f t)
        (ts.map fun t' => substmax_bounded_term t' t) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => exact ih (bd_apprel f x)

@[expose]
def subst0_bounded_formula {n l} (f : bounded_preformula L (n + 1) l)
    (s : bounded_term L n) : bounded_preformula L n l :=
  -- n + 1 = 0 + n + 1, so we use h : 0 + n + 1 = n + 1

  (subst_bounded_formula f s (by omega : 0 + n + 1 = n + 1)).cast_eq
    (by omega : 0 + n = n)

@[simp]
lemma subst0_bounded_formula_fst {n l} (f : bounded_preformula L (n + 1) l)
    (s : bounded_term L n) :
    (subst0_bounded_formula f s).fst = subst_formula f.fst s.fst 0 :=
  by
  simp only [subst0_bounded_formula, bounded_preformula.cast_eq_fst]
  rw [subst_bounded_formula_fst f s (by omega : 0 + n + 1 = n + 1)]

theorem substmax_eq_subst0_formula {l} (f : bounded_preformula L 1 l)
    (t : closed_term L) : subst0_bounded_formula f t = substmax_bounded_formula f t :=
  by
  apply bounded_preformula.eq
  simp only [subst0_bounded_formula, substmax_bounded_formula,
    bounded_preformula.cast_eq_fst, subst_bounded_formula_fst]

/-! ### realize_sentence lemmas -/


@[simp]
lemma realize_sentence_false {S : Structure L} :
    realize_sentence S (bd_falsum : sentence L) ↔ False :=
  Iff.rfl

@[simp]
lemma realize_sentence_imp {S : Structure L} {f₁ f₂ : sentence L} :
    realize_sentence S (bd_imp f₁ f₂) ↔ (realize_sentence S f₁ → realize_sentence S f₂) :=
  Iff.rfl

@[simp]
lemma realize_sentence_not {S : Structure L} {f : sentence L} :
    realize_sentence S (bd_not f) ↔ ¬realize_sentence S f :=
  Iff.rfl

@[simp]
lemma realize_sentence_dne {S : Structure L} {f : sentence L} :
    realize_sentence S (bd_not (bd_not f)) ↔ realize_sentence S f :=
  by
  simp only [realize_sentence, realize_bounded_formula, bd_not]
  tauto

@[simp]
lemma realize_sentence_all {S : Structure L} {f : bounded_formula L 1} :
    realize_sentence S (bd_all f) ↔
      ∀ x : S, realize_bounded_formula (DVec.cons x DVec.nil) f DVec.nil :=
  Iff.rfl

@[simp]
lemma realize_bounded_formula_imp {S : Structure L} :
    ∀ {n} {v : DVec S n} {f g : bounded_formula L n},
      realize_bounded_formula v (bd_imp f g) DVec.nil ↔
        (realize_bounded_formula v f DVec.nil → realize_bounded_formula v g DVec.nil) :=
  Iff.rfl

@[simp]
lemma realize_bounded_formula_and {S : Structure L} :
    ∀ {n} {v : DVec S n} {f g : bounded_formula L n},
      realize_bounded_formula v (bd_and f g) DVec.nil ↔
        (realize_bounded_formula v f DVec.nil ∧ realize_bounded_formula v g DVec.nil) :=
  by
  intros n v f g
  simp only [bd_and, bd_not, realize_bounded_formula]
  tauto

@[simp]
lemma realize_bounded_formula_not {S : Structure L} :
    ∀ {n} {v : DVec S n} {f : bounded_formula L n},
      realize_bounded_formula v (bd_not f) DVec.nil ↔
        ¬(realize_bounded_formula v f DVec.nil) :=
  Iff.rfl

@[simp]
lemma realize_bounded_formula_ex {S : Structure L} :
    ∀ {n} {v : DVec S n} {f : bounded_formula L (n + 1)},
      realize_bounded_formula v (bd_ex f) DVec.nil ↔
        ∃ x : S, realize_bounded_formula (DVec.cons x v) f DVec.nil :=
  by
  intros n v f
  simp only [bd_ex, bd_not, realize_bounded_formula]
    -- Goal: (∀ x, realize_bounded_formula (x ::ᵥ v) f [] → False) →
      -- False ↔ ∃ x, ...

  constructor
  · intro h
    by_contra hc
    apply h
    intro x hx
    exact hc ⟨x, hx⟩
  · intro ⟨x, hx⟩ h
    exact h x hx

@[simp]
lemma realize_sentence_ex {S : Structure L} {f : bounded_formula L 1} :
    realize_sentence S (bd_ex f) ↔
      ∃ x : S, realize_bounded_formula (DVec.cons x DVec.nil) f DVec.nil :=
  by apply realize_bounded_formula_ex

@[simp]
lemma realize_sentence_and {S : Structure L} {f₁ f₂ : sentence L} :
    realize_sentence S (bd_and f₁ f₂) ↔ (realize_sentence S f₁ ∧ realize_sentence S f₂) :=
  realize_bounded_formula_and

@[simp]
lemma realize_bounded_formula_biimp {S : Structure L} :
    ∀ {n} {v : DVec S n} {f g : bounded_formula L n},
      realize_bounded_formula v (bd_biimp f g) DVec.nil ↔
        (realize_bounded_formula v f DVec.nil ↔ realize_bounded_formula v g DVec.nil) :=
  by
  intros n v f g
  simp [bd_biimp, realize_bounded_formula_and]
  tauto

@[simp]
lemma realize_sentence_biimp {S : Structure L} {f₁ f₂ : sentence L} :
    realize_sentence S (bd_biimp f₁ f₂) ↔
      (realize_sentence S f₁ ↔ realize_sentence S f₂) :=
  realize_bounded_formula_biimp

lemma realize_bounded_formula_bd_apps_rel {S : Structure L} {n l} (xs : DVec S n)
    (f : bounded_preformula L n l) (ts : DVec (bounded_term L n) l) :
    realize_bounded_formula xs (bd_apps_rel f ts) DVec.nil ↔
      realize_bounded_formula xs f (ts.map fun t => realize_bounded_term xs t DVec.nil) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs' ih => exact ih (bd_apprel f x)

@[simp]
lemma realize_cast_bounded_formula {S : Structure L} {n m} {h : n ≤ m}
    {f : bounded_formula L n} {v : DVec S m} :
    realize_bounded_formula v (f.cast h) DVec.nil =
      realize_bounded_formula (v.trunc n h) f DVec.nil :=
  by
  -- Case split: n = m or n < m

  by_cases hn : n = m
  · -- n = m: cast is identity, trunc is identity
    subst hn; simp [bounded_preformula.cast_rfl]
  · -- n < m

    have hnlt : n < m := Nat.lt_of_le_of_ne h hn
    apply propext
    apply realize_bounded_formula_irrel'
    · -- Show v.nth k (hk : k < m) = (v.trunc n h).nth k (hk' : k < n) when k < n

      intro k hkn hkm
      rw [DVec.trunc_nth]
    · -- Show (f.cast h).fst = f.fst
      simp [bounded_preformula.cast_fst]

lemma realize_sentence_bd_apps_rel' {S : Structure L} {l} (f : presentence L l)
    (ts : DVec (closed_term L) l) :
    realize_sentence S (bd_apps_rel f ts) ↔
      realize_bounded_formula (DVec.nil : DVec S 0) f (ts.map (realize_closed_term S)) :=
  realize_bounded_formula_bd_apps_rel DVec.nil f ts

lemma realize_bd_apps_rel {S : Structure L} {l} (R : L.relations l)
    (ts : DVec (closed_term L) l) :
    realize_sentence S (bd_apps_rel (bd_rel R) ts) ↔
      S.rel_map R (ts.map (realize_closed_term S)) :=
  realize_bounded_formula_bd_apps_rel DVec.nil (bd_rel R) ts

lemma realize_sentence_equal {S : Structure L} (t₁ t₂ : closed_term L) :
    realize_sentence S (bd_equal t₁ t₂) ↔
      realize_closed_term S t₁ = realize_closed_term S t₂ :=
  Iff.rfl

lemma realize_sentence_iff {S : Structure L} (v : ℕ → S) (f : sentence L) :
    realize_sentence S f ↔ realize_formula v f.fst DVec.nil :=
  by
  apply realize_bounded_formula_iff
  intro k hk
  exact absurd hk (Nat.not_lt_zero k)

/-! ### lift_bounded_formula_at — lift bounded formulas -/


@[simp, expose]
def lift_bounded_formula_at :
    ∀ {n l} (_f : bounded_preformula L n l) (n' _m : ℕ), bounded_preformula L (n + n') l
  | _, _, bd_falsum, _, _ => bd_falsum
  | _, _, bd_equal t₁ t₂, n', m => bd_equal (t₁ ↑ᵇ' n' # m) (t₂ ↑ᵇ' n' # m)
  | _, _, bd_rel R, _, _ => bd_rel R
  | _, _, bd_apprel f t, n', m =>
    bd_apprel (lift_bounded_formula_at f n' m) (t ↑ᵇ' n' # m)
  | _, _, bd_imp f₁ f₂, n', m =>
    bd_imp (lift_bounded_formula_at f₁ n' m) (lift_bounded_formula_at f₂ n' m)
  | n, _, bd_all f, n', m =>
    bd_all ((lift_bounded_formula_at f n' (m + 1)).cast_eq (by omega))

notation:90 f " ↑ᶠᵇ' " n " # " m => Fol.lift_bounded_formula_at f n m

@[reducible, expose]
def lift_bounded_formula {n l} (f : bounded_preformula L n l) (n' : ℕ) :
    bounded_preformula L (n + n') l :=
  lift_bounded_formula_at f n' 0

infixl:100 " ↑ᶠᵇ " => Fol.lift_bounded_formula

@[reducible, simp, expose]
def lift_bounded_formula1 {n' l} (f : bounded_preformula L n' l) :
    bounded_preformula L (n' + 1) l :=
  f ↑ᶠᵇ 1

@[simp]
lemma lift_bounded_formula_fst :
    ∀ {n l} (f : bounded_preformula L n l) (n' m : ℕ),
      (lift_bounded_formula_at f n' m).fst = lift_formula_at f.fst n' m
  | _, _, bd_falsum, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', m => by
    simp only [lift_bounded_formula_at, bounded_preformula.fst, lift_formula_at,
      lift_bounded_term_fst t₁ n' m, lift_bounded_term_fst t₂ n' m]
  | _, _, bd_rel _, _, _ => rfl
  | _, _, bd_apprel f t, n', m => by
    simp only [lift_bounded_formula_at, bounded_preformula.fst, lift_formula_at,
      lift_bounded_formula_fst f n' m, lift_bounded_term_fst t n' m]
  | _, _, bd_imp f₁ f₂, n', m => by
    simp [lift_bounded_formula_fst f₁ n' m, lift_bounded_formula_fst f₂ n' m]
  | n, _, bd_all f, n', m =>
    by
    simp only [lift_bounded_formula_at, bounded_preformula.fst,
      bounded_preformula.cast_eq_fst, lift_bounded_formula_fst f n' (m + 1)]
    rfl

/-! ## Sentence theories (src/fol.lean lines 2233-2759) -/


/-- A `SentTheory` is a set of sentences (Lean 3: `Theory L = set
(sentence L)`). -/
abbrev SentTheory (L : Language.{u}) :=
  Set (sentence L)

/-- Project a sentence theory to a set of formulas -/
@[reducible, expose]
def SentTheory.fst (T : SentTheory L) : Set (formula L) :=
  bounded_preformula.fst '' T

lemma SentTheory.lift_irrel (T : SentTheory L) : (lift_formula1 '' T.fst) = T.fst :=
  by
  rw [Set.image_image]
  apply Set.image_congr'
  exact lift_sentence_irrel

/-- Derivability for sentence theories: T.fst ⊢ f.fst -/
@[expose]
def SentTheory.sprf (T : SentTheory L) (f : sentence L) : Type u :=
  T.fst ⊢ f.fst

/-- Provability (nonempty-wrapped) for sentence theories -/
@[expose]
def SentTheory.sprovable (T : SentTheory L) (f : sentence L) : Prop :=
  T.fst ⊢' f.fst

scoped notation:51 T " ⊢ₛ " f => Fol.SentTheory.sprf T f
scoped notation:51 T " ⊢ₛ' " f => Fol.SentTheory.sprovable T f

/-! ### All-realize-sentence — a structure models a sentence
theory -/


/-- A structure S realizes all sentences in T -/
@[expose]
def all_realize_sentence (S : Structure L) (T : SentTheory L) : Prop :=
  ∀ ⦃f⦄, f ∈ T → S ⊨ₘ f

-- Use ⊨ₜ for "structure realizes a sentence theory" (distinct
-- from existing ⊨ₛ)
scoped notation:51 S " ⊨ₜ " T => Fol.all_realize_sentence S T

lemma all_realize_sentence_of_subset {S : Structure L} {T₁ T₂ : SentTheory L}
    (H : S ⊨ₜ T₂) (h_sub : T₁ ⊆ T₂) : S ⊨ₜ T₁ := fun _ hf => H (h_sub hf)

@[simp]
lemma all_realize_sentence_insert {S : Structure L} {f : sentence L} {T : SentTheory L} :
    (S ⊨ₜ (insert f T)) ↔ (S ⊨ₘ f) ∧ (S ⊨ₜ T) :=
  by
  constructor
  · intro H
    exact ⟨H (Set.mem_insert f T), fun g hg => H (Set.mem_insert_of_mem f hg)⟩
  · intro ⟨Hf, HT⟩ g hg
    rcases hg with rfl | hg
    · exact Hf
    · exact HT hg

@[simp]
lemma all_realize_sentence_singleton {S : Structure L} {f : sentence L} :
    (S ⊨ₜ ({ f } : SentTheory L)) ↔ S ⊨ₘ f :=
  ⟨fun H => H (Set.mem_singleton f), fun H g hg => by
    rw [Set.mem_singleton_iff] at hg;
    subst hg; exact H⟩

@[simp]
lemma realize_sentence_of_mem {S : Structure L} {T : SentTheory L} {f : sentence L}
    (H : S ⊨ₜ T) (h_mem : f ∈ T) : S ⊨ₘ f :=
  H h_mem

/-! ### ssatisfied — semantic consequence for sentence theories
-/


/-- T semantically entails ψ: every nonempty model of T satisfies
ψ -/
@[expose]
def ssatisfied (T : SentTheory L) (f : sentence L) : Prop :=
  ∀ ⦃S : Structure L⦄, Nonempty S → all_realize_sentence S T → S ⊨ₘ f

-- Note: ⊨ₛ is already taken by satisfied_in; use ssatisfied
-- directly.

@[expose]
def all_ssatisfied (T T' : SentTheory L) : Prop :=
  ∀ f ∈ T', ssatisfied T f

/-! ### Connection between ssatisfied and satisfied -/


lemma satisfied_of_ssatisfied {T : SentTheory L} {f : sentence L} (H : ssatisfied T f) :
    T.fst ⊨ f.fst := by
  intro S v hT
  rw [← realize_sentence_iff]
  apply H ⟨v 0⟩
  intro f' hf'
  rw [realize_sentence_iff v]
  apply hT
  exact Set.mem_image_of_mem _ hf'

lemma ssatisfied_of_satisfied {T : SentTheory L} {f : sentence L} (H : T.fst ⊨ f.fst) :
    ssatisfied T f := by
  intro S hS hT
  obtain ⟨s⟩ := hS
  rw [realize_sentence_iff (fun _ => s)]
  apply H
  intro f' hf'
  rcases hf' with ⟨f'', hf'', rfl⟩
  rw [← realize_sentence_iff]
  exact hT hf''

lemma satisfied_iff_ssatisfied {T : SentTheory L} {f : sentence L} :
    ssatisfied T f ↔ T.fst ⊨ f.fst :=
  ⟨satisfied_of_ssatisfied, ssatisfied_of_satisfied⟩

lemma ssatisfied_snot {S : Structure L} {f : sentence L} (hS : ¬(S ⊨ₘ f)) :
    S ⊨ₘ (bd_not f) :=
  hS

/-! ## Model — bundled structure satisfying a sentence theory -/


/-- A model of T is a structure satisfying T.
    Lean 3 `Σ' (S : Structure L), S ⊨ T` → Lean 4 `{S : Structure L
    // all_realize_sentence S T}` -/
@[expose]
def Model (T : SentTheory L) : Type (u + 1) :=
  { S : Structure L // all_realize_sentence S T }

namespace Model

variable {T : SentTheory L}

/-- The underlying structure of a model -/
abbrev str (M : Model T) : Structure L :=
  M.val

/-- The model satisfies its theory -/
lemma sat (M : Model T) : all_realize_sentence M.str T :=
  M.property

/-- A model realizes a sentence -/
@[reducible, expose]
def realize (M : Model T) (ψ : sentence L) : Prop :=
  M.str ⊨ₘ ψ

end Model

@[simp]
lemma Model_realize_iff {T : SentTheory L} {M : Model T} {ψ : sentence L} :
    Model.realize M ψ ↔ M.str ⊨ₘ ψ :=
  Iff.rfl

lemma Model_realize_of_theory {T : SentTheory L} (M : Model T) {ψ : sentence L}
    (h : ψ ∈ T) : Model.realize M ψ :=
  M.sat h

@[simp]
lemma false_of_Model_absurd {T : SentTheory L} (M : Model T) {ψ : sentence L}
    (h : Model.realize M ψ) (h' : Model.realize M (bd_not ψ)) : False :=
  h' h

/-! ### Soundness at sentence level -/


lemma ssatisfied_soundness {T : SentTheory L} {A : sentence L} (H : T ⊢ₛ' A) :
    ssatisfied T A :=
  ssatisfied_of_satisfied (formula_soundness (Nonempty.some H))

/-- Given a model M with M realizes ¬ψ, we have ¬ ssatisfied T ψ
-/
lemma not_ssatisfied_of_model_not {T : SentTheory L} {ψ : sentence L} (M : Model T)
    (hM : Model.realize M (bd_not ψ)) (h_nonempty : Nonempty M.str) : ¬ssatisfied T ψ :=
  by
  intro H
  exact false_of_Model_absurd M (H h_nonempty M.sat) hM

/-! ### Sentence-level is_consistent -/


/-- T is consistent if T.fst ⊬' ⊥ (at sentence/formula level) -/
@[expose]
def SentTheory.is_consistent (T : SentTheory L) : Prop :=
  ¬(T.fst ⊢' ⊥')

/-! ### Theory of a structure -/


/-- The theory of a structure S: all sentences true in S -/
@[expose]
def Th (S : Structure L) : SentTheory L :=
  {f : sentence L | S ⊨ₘ f}

lemma realize_sentence_Th (S : Structure L) : all_realize_sentence S (Th S) :=
  fun _f hf => hf

lemma SentTheory.is_consistent_Th (S : Structure L) (HS : Nonempty S) :
    (Th S).is_consistent := by
  intro H
  obtain ⟨h⟩ := H
  have hsat : (Th S).fst ⊨ (⊥' : formula L) := formula_soundness h
  obtain ⟨s⟩ := HS
  exact
    hsat S (fun _ => s)
      (by
        intro f hf
        rcases hf with ⟨g, hg, rfl⟩
        exact (realize_sentence_iff (fun _ => s) g).mp hg)

@[simp]
lemma in_theory_iff_satisfied {S : Structure L} {f : sentence L} : f ∈ Th S ↔ S ⊨ₘ f :=
  Iff.rfl

/-! ### eliminates_quantifiers -/


@[expose]
def eliminates_quantifiers (T : SentTheory L) : Prop :=
  ∀ (f : sentence L),
    f ∈ T →
      ∃ f' : sentence L, bounded_preformula.quantifier_free f' ∧ T.fst ⊢' (f.fst ⇔ f'.fst)

/-! ### L_empty, T_empty, T_equality -/


/-- The empty language with no functions and no relations -/
@[expose]
def L_empty : Language.{u} :=
  ⟨fun _ => PEmpty, fun _ => PEmpty⟩

/-- The empty theory over a language -/
@[expose]
def T_empty (L : Language.{u}) : SentTheory L :=
  ∅

/-- The equality theory: empty theory over the empty language -/
@[reducible, expose]
def T_equality : SentTheory (@L_empty.{u}) :=
  T_empty (@L_empty.{u})

/-! ## Section bd_alls (src/fol.lean lines 2706-2757) -/


/-- Apply ∀' n times to an unbounded formula -/
@[simp, expose]
def alls : ∀ (_n : ℕ), formula L → formula L
  | 0, f => f
  | n + 1, f => ∀'(alls n f)

/-- Apply bd_all k times, reducing the bound index from n+k to n
-/
@[simp, expose]
def bd_alls' : ∀ (k n : ℕ), bounded_formula L (n + k) → bounded_formula L n
  | 0, _n, f => f
  | k + 1, n, f => bd_alls' k n (bd_all f)

/-- Close off a bounded formula by universally quantifying all n
free variables -/
@[simp, expose]
def bd_alls : ∀ (n : ℕ), bounded_formula L n → sentence L
  | 0, f => f
  | n + 1, f => bd_alls n (bd_all f)

@[simp]
lemma alls'_alls :
    ∀ (n : ℕ) (ψ : bounded_formula L n),
      bd_alls n ψ = bd_alls' n 0 (ψ.cast_eq (Nat.zero_add n).symm) :=
  by
  intro n
  induction n with
  | zero => intro ψ; simp [bounded_preformula.cast_eq]
  | succ n ih =>
    intro ψ
    simp only [bd_alls, bd_alls']
    rw [ih (bd_all ψ)]
    simp [bounded_preformula.cast_eq]

@[simp]
lemma alls'_all_commute {n k : ℕ} (f : bounded_formula L (n + k + 1)) :
    bd_alls' k n (bd_all f) = bd_all (bd_alls' k (n + 1) (f.cast_eq (by omega))) := by
  induction k generalizing n with
  | zero => simp [bd_alls', bounded_preformula.cast_eq]
  | succ k ih =>
    simp only [bd_alls']
    rw [ih]
    simp [bounded_preformula.cast_eq]

@[simp]
lemma realize_sentence_bd_alls {n : ℕ} {f : bounded_formula L n} {S : Structure L} :
    S ⊨ₘ (bd_alls n f) ↔ ∀ xs : DVec S n, realize_bounded_formula xs f DVec.nil := by
  induction n with
  | zero =>
    simp only [bd_alls, realize_sentence]
    constructor
    · intro H xs
      rwa [DVec.zero_eq xs]
    · intro H
      exact H DVec.nil
  | succ n ih =>
    simp only [bd_alls]
    rw [ih]
    constructor
    · intro H xs
      cases xs with
      | cons x xs' => exact H xs' x
    · intro H xs x
      exact H (DVec.cons x xs)

@[simp]
lemma alls_0 (ψ : formula L) : alls 0 ψ = ψ :=
  rfl

@[simp]
lemma alls_all_commute (f : formula L) {k : ℕ} : alls k (∀'f) = ∀'(alls k f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [alls]
    rw [ih]

@[simp]
lemma alls_succ_k (f : formula L) {k : ℕ} : alls (k + 1) f = ∀'(alls k f) :=
  rfl

end Fol

end NFChoice
