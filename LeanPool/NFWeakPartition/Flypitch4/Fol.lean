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
def substRealize {S : Type u} (v : ℕ → S) (x : S) (n k : ℕ) : S :=
  if k < n then v k else if n < k then v (k - 1) else x

@[simp]
lemma subst_realize_lt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : k < n) :
    Fol.substRealize v x n k = v k := by simp only [substRealize, H, ite_true]

@[simp]
lemma subst_realize_gt {S : Type u} (v : ℕ → S) (x : S) {n k : ℕ} (H : n < k) :
    Fol.substRealize v x n k = v (k - 1) :=
  by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [substRealize, h, ite_false, H, ite_true]

@[simp]
lemma subst_realize_var_eq {S : Type u} (v : ℕ → S) (x : S) (n : ℕ) :
    Fol.substRealize v x n n = x := by simp only [substRealize, lt_irrefl, ite_false]

lemma subst_realize_congr {S : Type u} {v v' : ℕ → S} (hv : ∀ k, v k = v' k) (x : S)
    (n k : ℕ) : Fol.substRealize v x n k = Fol.substRealize v' x n k :=
  by
  rcases Nat.lt_trichotomy k n with h | h | h
  · simp [substRealize, h, hv k]
  · subst h; simp [substRealize]
  · simp [substRealize, Nat.lt_asymm h, h, hv (k - 1)]

lemma subst_realize2 {S : Type u} (v : ℕ → S) (x x' : S) (n₁ n₂ k : ℕ) :
    Fol.substRealize (Fol.substRealize v x' (n₁ + n₂)) x n₁ k =
      Fol.substRealize (Fol.substRealize v x n₁) x' (n₁ + n₂ + 1) k :=
  by
  simp only [substRealize]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all [] <;> omega

lemma subst_realize2_0 {S : Type u} (v : ℕ → S) (x x' : S) (n k : ℕ) :
    Fol.substRealize (Fol.substRealize v x' n) x 0 k =
      Fol.substRealize (Fol.substRealize v x 0) x' (n + 1) k :=
  by
  have h := subst_realize2 v x x' 0 n k
  simp only [Nat.zero_add] at h
  exact h

lemma subst_realize_irrel {S : Type u} {v₁ v₂ : ℕ → S} {n : ℕ}
    (hv : ∀ k, k < n → v₁ k = v₂ k) (x : S) {k : ℕ} (hk : k < n + 1) :
    Fol.substRealize v₁ x 0 k = Fol.substRealize v₂ x 0 k := by
  cases k with
  | zero => rfl
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [substRealize, h, hv k (Nat.lt_of_succ_lt_succ hk)]

lemma lift_subst_realize_cancel {S : Type u} (v : ℕ → S) (k : ℕ) :
    Fol.substRealize (fun n => v (n + 1)) (v 0) 0 k = v k := by
  cases k with
  | zero => simp [substRealize]
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp [substRealize, h]

lemma subst_fin_realize_eq {S : Type u} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) (x : S) (k : ℕ) (hk : k < n + 1) :
    (DVec.cons x v₁).nth k hk = Fol.substRealize v₂ x 0 k := by
  cases k with
  | zero => simp [DVec.nth, substRealize]
  | succ k =>
    have h : 0 < k + 1 := Nat.succ_pos _
    simp only [DVec.nth, substRealize, h, ite_true, Nat.add_sub_cancel]
    exact hv k (Nat.lt_of_succ_lt_succ hk)

/-! ## Language -/


/-- Flypitch construction `Language`, retained by the first-order soundness and completeness
development.
-/
structure Language : Type (u + 1) where
  /-- The `functions` component of the corresponding first-order structure. -/
  functions : ℕ → Type u
  /-- The `relations` component of the corresponding first-order structure. -/
  relations : ℕ → Type u

/-- Flypitch construction `Language.constants`, retained by the first-order soundness and
completeness development.
-/
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

/-- Flypitch construction `term`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def term :=
  preterm L 0

variable {L}

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
prefix:max "&" => Fol.preterm.var

/-- Flypitch construction `apps`, retained by the first-order soundness and completeness
development.
-/
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

/-- Flypitch construction `change_arity'`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def changeArity' : ∀ {l l'} (_ : l = l') (_t : preterm L l), preterm L l'
  | _, _, h, var k => by subst h; exact var k
  | _, _, h, func f => func (by subst h; exact f)
  | _, _, h, app t₁ t₂ => app (changeArity' (by omega) t₁) t₂

@[simp]
lemma change_arity'_rfl : ∀ {l} (t : preterm L l), changeArity' rfl t = t
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

/-- Flypitch construction `term_of_function`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def term_of_function {l} (f : L.functions l) : Arity' (term L) (term L) l :=
  Arity'.ofDvectorMap
    (apps (preterm.func f))
      -- term.rec: custom recursion principle via structural recursion


-- term.rec: custom recursion principle via structural recursion
/-- Flypitch construction `term.rec`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def term.rec {C : term L → Sort v} (hvar : ∀ (k : ℕ), C (&k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (term L) l)
        (_ih_ts : ∀ t, DVec.pmem t ts → C t), C (apps (preterm.func f) ts)) :
    ∀ (t : term L), C t :=
  let rec /-- Structural recursion accumulator. -/ go :
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

/-- Flypitch construction `term.elim'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def term.elim' {C : Type v} (hvar : ∀ (_k : ℕ), C)
    (hfunc : ∀ {{l}} (_f : L.functions l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C) :
    ∀ {l} (_t : preterm L l) (_ts : DVec (term L) l) (_ih_ts : DVec C l), C
  | _, preterm.var k, _, _ => hvar k
  | _, preterm.func f, ts, ih_ts => hfunc f ts ih_ts
  | _, preterm.app t s, ts, ih_ts =>
    term.elim' hvar hfunc t (DVec.cons s ts)
      (DVec.cons (term.elim' hvar hfunc s DVec.nil DVec.nil) ih_ts)

/-- Flypitch construction `term.elim`, retained by the first-order soundness and completeness
development.
-/
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
def liftTermAt : ∀ {l}, preterm L l → ℕ → ℕ → preterm L l
  | _, preterm.var k, n, m => &(if m ≤ k then k + n else k)
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, n, m => preterm.app (liftTermAt t₁ n m) (liftTermAt t₂ n m)

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:90 t " ↑' " n " # " m => Fol.liftTermAt t n m

/-- Flypitch construction `lift_term`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def liftTerm {l} (t : preterm L l) (n : ℕ) : preterm L l :=
  liftTermAt t n 0

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
infixl:100 " ↑ " => Fol.liftTerm

/-- Flypitch construction `lift_term1`, retained by the first-order soundness and completeness
development.
-/
@[reducible, simp, expose]
def liftTerm1 {l} (t : preterm L l) : preterm L l :=
  liftTerm t 1

@[simp]
lemma lift_term_def {l} (t : preterm L l) (n : ℕ) : liftTermAt t n 0 = liftTerm t n :=
  rfl

lemma injective_lift_term_at :
    ∀ {l} {n m : ℕ}, Function.Injective (fun (t : preterm L l) => liftTermAt t n m)
  | _, n, m, preterm.var k, preterm.var k', h =>
    by
    simp only [liftTermAt] at h
    have hk := preterm.var.inj h
    split_ifs at hk with h₁ h₂
    all_goals (try exact congrArg preterm.var (by omega))
  | _, _, _, preterm.var _, preterm.func _, h => by simp [liftTermAt] at h
  | _, _, _, preterm.var _, preterm.app _ _, h => by simp [liftTermAt] at h
  | _, _, _, preterm.func _, preterm.var _, h => by simp [liftTermAt] at h
  | _, _, _, preterm.func _, preterm.func _, h => h
  | _, _, _, preterm.func _, preterm.app _ _, h => by simp [liftTermAt] at h
  | _, _, _, preterm.app _ _, preterm.var _, h => by simp [liftTermAt] at h
  | _, _, _, preterm.app _ _, preterm.func _, h => by simp [liftTermAt] at h
  | _, n, m, preterm.app t₁ t₂, preterm.app t₁' t₂', h =>
    by
    simp only [liftTermAt] at h
    obtain ⟨h1, h2⟩ := preterm.app.inj h
    exact congrArg₂ preterm.app (injective_lift_term_at h1) (injective_lift_term_at h2)

@[simp]
lemma lift_term_at_zero : ∀ {l} (t : preterm L l) (m : ℕ), liftTermAt t 0 m = t
  | _, preterm.var k, _ => by simp [liftTermAt]
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, m => by
    simp only [liftTermAt, lift_term_at_zero t₁ m, lift_term_at_zero t₂ m]

lemma lift_term_zero {l} (t : preterm L l) : liftTerm t 0 = t :=
  lift_term_at_zero t 0

/-- Iterated lifts: smaller new position -/
lemma lift_term_at2_small :
    ∀ {l} (t : preterm L l) (n n') {m m'},
      m' ≤ m →
        liftTermAt (liftTermAt t n m) n' m' =
          liftTermAt (liftTermAt t n' m') n (m + n')
  | _, preterm.var k, n, n', m, m', H =>
    by
    simp only [liftTermAt]
    split_ifs <;> simp_all [] <;> omega
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H => by
    simp only [liftTermAt, lift_term_at2_small t₁ n n' H, lift_term_at2_small t₂ n n' H]

lemma lift_term_at2_medium :
    ∀ {l} (t : preterm L l) {n} (n') {m m'},
      m ≤ m' →
        m' ≤ m + n → liftTermAt (liftTermAt t n m) n' m' = liftTermAt t (n + n') m
  | _, preterm.var k, n, n', m, m', H₁, H₂ =>
    by
    simp only [liftTermAt]
    split_ifs <;> simp_all [] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, n, n', m, m', H₁, H₂ => by
    simp only [liftTermAt, lift_term_at2_medium t₁ n' H₁ H₂,
      lift_term_at2_medium t₂ n' H₁ H₂]

lemma lift_term2_medium {l} (t : preterm L l) {n} (n') {m'} (h : m' ≤ n) :
    liftTermAt (liftTerm t n) n' m' = liftTerm t (n + n') :=
  lift_term_at2_medium t n' (Nat.zero_le _) (by omega)

lemma lift_term2 {l} (t : preterm L l) (n n') :
    liftTerm (liftTerm t n) n' = liftTerm t (n + n') :=
  lift_term2_medium t n' (Nat.zero_le _)

lemma lift_term_at2_eq {l} (t : preterm L l) (n n' m : ℕ) :
    liftTermAt (liftTermAt t n m) n' (m + n) = liftTermAt t (n + n') m :=
  lift_term_at2_medium t n' (Nat.le_add_right _ _) (le_refl _)

lemma lift_term_at2_large {l} (t : preterm L l) {n} (n') {m m'} (H : m + n ≤ m') :
    liftTermAt (liftTermAt t n m) n' m' =
      liftTermAt (liftTermAt t n' (m' - n)) n m :=
  by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_term_at2_small t n' n H₂, Nat.sub_add_cancel H₁]

lemma lift_term_var0 (n : ℕ) : liftTerm (&0 : term L) n = &n := by
  simp [liftTerm, liftTermAt]

@[simp]
lemma lift_term_at_apps {l} (t : preterm L l) (ts : DVec (term L) l) (n m : ℕ) :
    liftTermAt (apps t ts) n m =
      apps (liftTermAt t n m) (ts.map (fun x => liftTermAt x n m)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps, DVec.map]; exact ih (preterm.app t x)

lemma lift_term_apps {l} (t : preterm L l) (ts : DVec (term L) l) (n : ℕ) :
    liftTerm (apps t ts) n = apps (liftTerm t n) (ts.map (fun x => liftTerm x n)) :=
  lift_term_at_apps t ts n 0

/-! ## subst_term — substitution -/


/-- `subst_term t s n` substitutes `s` for `(&n)` in `t` and
reduces variable levels above n. -/
@[expose]
def substTerm : ∀ {l}, preterm L l → term L → ℕ → preterm L l
  | _, preterm.var k, s, n => Fol.substRealize preterm.var (liftTerm s n) n k
  | _, preterm.func f, _, _ => preterm.func f
  | _, preterm.app t₁ t₂, s, n => preterm.app (substTerm t₁ s n) (substTerm t₂ s n)

@[simp]
lemma subst_term_var_lt (s : term L) {k n : ℕ} (H : k < n) :
    substTerm (preterm.var k) s n = &k := by
  simp only [substTerm, substRealize, H, ite_true]

@[simp]
lemma subst_term_var_gt (s : term L) {k n : ℕ} (H : n < k) :
    substTerm (preterm.var k) s n = &(k - 1) :=
  by
  have h : ¬(k < n) := Nat.lt_asymm H
  simp only [substTerm, substRealize, h, ite_false, H, ite_true]

@[simp]
lemma subst_term_var_eq (s : term L) (n : ℕ) :
    substTerm (preterm.var n) s n = liftTermAt s n 0 := by
  simp [substTerm, substRealize]

lemma subst_term_var0 (s : term L) : substTerm (preterm.var 0) s 0 = s := by
  simp [substTerm, substRealize, lift_term_at_zero]

@[simp]
lemma subst_term_func {l} (f : L.functions l) (s : term L) (n : ℕ) :
    substTerm (preterm.func f : preterm L l) s n = preterm.func f :=
  rfl

@[simp]
lemma subst_term_app {l} (t₁ : preterm L (l + 1)) (t₂ s : term L) (n : ℕ) :
    substTerm (preterm.app t₁ t₂) s n =
      preterm.app (substTerm t₁ s n) (substTerm t₂ s n) :=
  rfl

@[simp]
lemma subst_term_apps {l} (t : preterm L l) (ts : DVec (term L) l) (s : term L) (n : ℕ) :
    substTerm (apps t ts) s n =
      apps (substTerm t s n) (ts.map (fun x => substTerm x s n)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [apps, DVec.map]; exact ih (preterm.app t x)

/-- Lift then substitute: large case (substituted var is above
the lift range) -/
lemma lift_at_subst_term_large :
    ∀ {l} (t : preterm L l) (s : term L) {n₁} (n₂) {m},
      m ≤ n₁ →
        substTerm (liftTermAt t n₂ m) s (n₁ + n₂) =
          liftTermAt (substTerm t s n₁) n₂ m
  | _, preterm.var k, s, n₁, n₂, m, h =>
    by
    simp only [liftTermAt, substTerm, substRealize]
    split_ifs with h1 h2 h3 h4 h5 <;>
      first
      | rfl
      | omega
      | (simp [liftTermAt]; omega)
      | (rw [← lift_term2_medium s n₂ (by omega)])
      | (congr 1; omega)
      |
        -- Goal: &(k+n₂-1) = &(k-1) ↑' n₂ # m; know m ≤ n₁ < k so m ≤ k-1
        (simp only [liftTermAt]; split_ifs with hm <;> ((congr 1; omega)))
  | _, preterm.func _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m, h => by
    simp [lift_at_subst_term_large t₁ s n₂ h, lift_at_subst_term_large t₂ s n₂ h]

lemma lift_subst_term_large {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    substTerm (liftTerm t n₂) s (n₁ + n₂) = liftTerm (substTerm t s n₁) n₂ :=
  lift_at_subst_term_large t s n₂ (Nat.zero_le _)

lemma lift_subst_term_large' {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    substTerm (liftTerm t n₂) s (n₂ + n₁) = liftTerm (substTerm t s n₁) n₂ := by
  rw [Nat.add_comm]; exact lift_subst_term_large t s n₁ n₂

/-- Lift then substitute: medium case (substituted var is within
the lift range) -/
lemma lift_at_subst_term_medium :
    ∀ {l} (t : preterm L l) (s : term L) {n₁ n₂ m},
      m ≤ n₂ →
        n₂ ≤ m + n₁ → substTerm (liftTermAt t (n₁ + 1) m) s n₂ = liftTermAt t n₁ m
  | _, preterm.var k, s, n₁, n₂, m, h₁, h₂ =>
    by
    simp only [liftTermAt, substTerm, substRealize]
    split_ifs <;> simp_all [] <;> omega
  | _, preterm.func _, _, _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
    simp [lift_at_subst_term_medium t₁ s h₁ h₂, lift_at_subst_term_medium t₂ s h₁ h₂]

lemma lift_subst_term_medium {l} (t : preterm L l) (s : term L) (n₁ n₂ : ℕ) :
    substTerm (liftTerm t (n₁ + n₂ + 1)) s n₁ = liftTerm t (n₁ + n₂) :=
  lift_at_subst_term_medium t s (Nat.zero_le _) (by omega)

lemma lift_at_subst_term_eq {l} (t : preterm L l) (s : term L) (n : ℕ) :
    substTerm (liftTermAt t 1 n) s n = t :=
  by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, lift_at_subst_term_medium t s (le_refl n) (le_refl n), lift_term_at_zero]

@[simp]
lemma lift_term1_subst_term {l} (t : preterm L l) (s : term L) :
    substTerm (liftTerm t 1) s 0 = t :=
  lift_at_subst_term_eq t s 0

/-- Lift then substitute: small case -/
lemma lift_at_subst_term_small :
    ∀ {l} (t : preterm L l) (s : term L) (n₁ n₂ m : ℕ),
      substTerm (liftTermAt t n₁ (m + n₂ + 1)) (liftTermAt s n₁ m) n₂ =
        liftTermAt (substTerm t s n₂) n₁ (m + n₂)
  | _, preterm.var k, s, n₁, n₂, m =>
    by
    rcases Nat.lt_trichotomy k n₂ with hk | hk | hk
    · -- k < n₂: subst gives &k, lift gives k (since ¬(m+n₂+1 ≤ k))
      have h1 : ¬(m + n₂ + 1 ≤ k) := by omega
      have h2 : ¬(m + n₂ ≤ k) := by omega
      simp only [liftTermAt, h1, ite_false, substTerm, substRealize, hk, ite_true, h2,
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
      simp only [liftTermAt, show ¬(m + k + 1 ≤ k) from by omega, ite_false, substTerm,
        substRealize, lt_irrefl, ite_false, liftTerm]
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
        simp only [liftTermAt, h1, ite_true, substTerm, substRealize, hknlt,
          ite_false, hkn1lt, show n₂ < k + n₁ from by omega, ite_true, h2, ite_true, hk,
          ite_true]
        exact congrArg preterm.var (by omega)
      · -- k < m+n₂+1 but k > n₂: so n₂ < k < m+n₂+1
                  -- lift gives &k (since ¬(m+n₂+1 ≤ k)), subst gives &(k-1) (since
                  -- k > n₂)
                  -- and ¬(m+n₂ ≤ k-1) because k ≤ m+n₂, so k-1 < m+n₂
        have h2 : ¬(m + n₂ ≤ k - 1) := by omega
        simp only [liftTermAt, h1, ite_false, substTerm, substRealize,
          Nat.lt_asymm hk, ite_false, hk, ite_true, h2, ite_false]
  | _, preterm.func _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s, n₁, n₂, m => by
    simp [lift_at_subst_term_small t₁ s n₁ n₂ m, lift_at_subst_term_small t₂ s n₁ n₂ m]

/-- Double substitution lemma -/
lemma subst_term2 :
    ∀ {l} (t : preterm L l) (s₁ s₂ : term L) (n₁ n₂ : ℕ),
      substTerm (substTerm t s₁ n₁) s₂ (n₁ + n₂) =
        substTerm (substTerm t s₂ (n₁ + n₂ + 1)) (substTerm s₁ s₂ n₂) n₁
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
        subst_term_var_eq (substTerm s₁ s₂ n₂) k, subst_term_var_eq s₁ k,
        lift_subst_term_large']
    · -- n₁ < k
      rcases Nat.lt_trichotomy k (n₁ + n₂ + 1) with hk' | hk' | hk'
      · -- n₁ < k < n₁+n₂+1: both sides give &(k-1)
        have hk1lt : k - 1 < n₁ + n₂ := by omega
        have hk1n1 : n₁ < k - 1 ∨ k - 1 = n₁ := by omega
        have hkn1 : ¬(k - 1 < n₁) := by omega
        rw [subst_term_var_gt s₁ hk, subst_term_var_lt s₂ hk', subst_term_var_lt s₂ hk1lt,
          subst_term_var_gt (substTerm s₁ s₂ n₂) hk]
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
        rw [subst_term_var_gt (substTerm s₁ s₂ n₂) hn1lt]
  | _, preterm.func _, _, _, _, _ => rfl
  | _, preterm.app t₁ t₂, s₁, s₂, n₁, n₂ => by
    simp [subst_term2 t₁ s₁ s₂ n₁ n₂, subst_term2 t₂ s₁ s₂ n₁ n₂]

lemma subst_term2_0 {l} (t : preterm L l) (s₁ s₂ : term L) (n : ℕ) :
    substTerm (substTerm t s₁ 0) s₂ n =
      substTerm (substTerm t s₂ (n + 1)) (substTerm s₁ s₂ n) 0 :=
  by
  have h := subst_term2 t s₁ s₂ 0 n
  simp only [Nat.zero_add] at h
  exact h

lemma lift_subst_term_cancel :
    ∀ {l} (t : preterm L l) (n : ℕ), substTerm (liftTermAt t 1 (n + 1)) (&0) n = t
  | _, preterm.var k, n =>
    by
    simp only [liftTermAt, substTerm, substRealize]
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
/-- Flypitch construction `formula`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def formula (L : Language.{u}) : Type u :=
  @preformula L 0

variable {L}

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation "⊥'" => Fol.preformula.falsum
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:88 " ≃ " => Fol.preformula.equal
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infixr:62 " ⟹ " => Fol.preformula.imp
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped prefix:110 "∀'" => Fol.preformula.all

/-- Flypitch construction `not'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def not' (f : formula L) : formula L :=
  preformula.imp f preformula.falsum
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped prefix:max "∼" => Fol.not'
/-- Flypitch construction `and'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def and' (f₁ f₂ : formula L) : formula L :=
  not' (preformula.imp f₁ (not' f₂))
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infixr:69 " ⊓' " => Fol.and'
/-- Flypitch construction `or'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def or' (f₁ f₂ : formula L) : formula L :=
  preformula.imp (not' f₁) f₂
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infixr:68 " ⊔' " => Fol.or'
/-- Flypitch construction `biimp`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def biimp (f₁ f₂ : formula L) : formula L :=
  and' (preformula.imp f₁ f₂) (preformula.imp f₂ f₁)
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:61 " ⇔ " => Fol.biimp
/-- Flypitch construction `ex'`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def ex' (f : formula L) : formula L :=
  not' (preformula.all (not' f))
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped prefix:110 "∃'" => Fol.ex'

/-- Flypitch construction `apps_rel`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def appsRel : ∀ {l}, @preformula L l → DVec (term L) l → formula L
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => appsRel (preformula.apprel f t) ts

@[simp]
lemma apps_rel_zero (f : formula L) (ts : DVec (term L) 0) : appsRel f ts = f := by
  cases ts; rfl

/-- Flypitch construction `formula_of_relation`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def formulaOfRelation {l} (R : L.relations l) : Arity' (term L) (formula L) l :=
  Arity'.ofDvectorMap (appsRel (preformula.rel R))

/-- Flypitch construction `formula.rec'`, retained by the first-order soundness and completeness
development.
-/
@[elab_as_elim, expose]
def formula.rec' {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (appsRel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) :
    ∀ {l} (f : @preformula L l) (ts : DVec (term L) l), C (appsRel f ts)
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

/-- Flypitch construction `formula.rec`, retained by the first-order soundness and completeness
development.
-/
@[elab_as_elim, expose]
def formula.rec {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (appsRel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) : ∀ f, C f := fun f =>
  have h := @formula.rec' L C hfalsum hequal hrel himp hall 0 f DVec.nil
  apps_rel_zero f DVec.nil ▸ h

lemma formula.rec'_apps_rel {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (appsRel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) {l} (f : @preformula L l)
    (ts : DVec (term L) l) :
    @formula.rec' L C hfalsum hequal hrel himp hall 0 (appsRel f ts) DVec.nil =
      @formula.rec' L C hfalsum hequal hrel himp hall l f ts :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [appsRel]; exact ih (preformula.apprel f x)

lemma formula.rec_apps_rel {C : formula L → Sort v} (hfalsum : C ⊥')
    (hequal : ∀ (t₁ t₂ : term L), C (t₁ ≃ t₂))
    (hrel : ∀ {{l}} (R : L.relations l) (ts : DVec (term L) l),
        C (appsRel (preformula.rel R) ts))
    (himp : ∀ {{f₁ f₂ : formula L}} (_ih₁ : C f₁) (_ih₂ : C f₂), C (f₁ ⟹ f₂))
    (hall : ∀ {{f : formula L}} (_ih : C f), C (∀'f)) {l} (R : L.relations l)
    (ts : DVec (term L) l) :
    @formula.rec L C hfalsum hequal hrel himp hall (appsRel (preformula.rel R) ts) =
      hrel R ts :=
  -- formula.rec f = apps_rel_zero f [] ▸ formula.rec' ... 0 f []
    -- This is definitionally equal to: (apps_rel_zero ...).symm ▸
    -- formula.rec'_apps_rel ▸ hrel R ts
  show
    (apps_rel_zero (appsRel (preformula.rel R) ts) DVec.nil ▸
        @formula.rec' L C hfalsum hequal hrel himp hall 0 (appsRel (preformula.rel R) ts)
          DVec.nil) =
      hrel R ts
    by
    rw [formula.rec'_apps_rel]
    rfl

/-! ## lift_formula_at — lifting variables in formulas -/


/-- Flypitch construction `lift_formula_at`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def liftFormulaAt : ∀ {l}, @preformula L l → ℕ → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, n, m =>
    preformula.equal (liftTermAt t₁ n m) (liftTermAt t₂ n m)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, n, m =>
    preformula.apprel (liftFormulaAt f n m) (liftTermAt t n m)
  | _, preformula.imp f₁ f₂, n, m =>
    preformula.imp (liftFormulaAt f₁ n m) (liftFormulaAt f₂ n m)
  | _, preformula.all f, n, m => preformula.all (liftFormulaAt f n (m + 1))

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:90 f " ↑f' " n " # " m => Fol.liftFormulaAt f n m

/-- Flypitch construction `lift_formula`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def liftFormula {l} (f : @preformula L l) (n : ℕ) : @preformula L l :=
  liftFormulaAt f n 0

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
infixl:100 " ↑f " => Fol.liftFormula

/-- Flypitch construction `lift_formula1`, retained by the first-order soundness and
completeness development.
-/
@[reducible, simp, expose]
def liftFormula1 {l} (f : @preformula L l) : @preformula L l :=
  liftFormula f 1

@[simp]
lemma lift_formula_def {l} (f : @preformula L l) (n : ℕ) :
    liftFormulaAt f n 0 = liftFormula f n :=
  rfl

@[simp]
lemma lift_formula1_not (n : ℕ) (f : formula L) : ∼f ↑f n = ∼(f ↑f n) :=
  rfl

lemma injective_lift_formula_at {l} {n : ℕ} {m : ℕ} :
    Function.Injective (fun (f : @preformula L l) => liftFormulaAt f n m) :=
  by
  intro f f' H
  induction f generalizing m with
  | falsum => cases f' <;> simp [liftFormulaAt] at *
  | equal t₁ t₂ =>
    cases f' with
    | equal t₁' t₂' =>
      simp only [liftFormulaAt] at H
      obtain ⟨h1, h2⟩ := preformula.equal.inj H
      exact
        congrArg₂ preformula.equal (injective_lift_term_at h1) (injective_lift_term_at h2)
    | _ => simp [liftFormulaAt] at H
  | rel R =>
    cases f' with
    | rel R' => exact preformula.rel.inj H ▸ rfl
    | _ => simp [liftFormulaAt] at H
  | apprel f t ih =>
    cases f' with
    | apprel f' t' =>
      simp only [liftFormulaAt] at H
      obtain ⟨hf, ht⟩ := preformula.apprel.inj H
      exact congrArg₂ preformula.apprel (ih hf) (injective_lift_term_at ht)
    | _ => simp [liftFormulaAt] at H
  | imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | imp f₁' f₂' =>
      simp only [liftFormulaAt] at H
      obtain ⟨h1, h2⟩ := preformula.imp.inj H
      exact congrArg₂ preformula.imp (ih₁ h1) (ih₂ h2)
    | _ => simp [liftFormulaAt] at H
  | all f ih =>
    cases f' with
    | all f' =>
      simp only [liftFormulaAt] at H
      exact congrArg preformula.all (ih (preformula.all.inj H))
    | _ => simp [liftFormulaAt] at H

@[simp]
lemma lift_formula_at_zero :
    ∀ {l} (f : @preformula L l) (m : ℕ), liftFormulaAt f 0 m = f
  | _, preformula.falsum, _ => rfl
  | _, preformula.equal t₁ t₂, m => by simp [liftFormulaAt]
  | _, preformula.rel R, _ => rfl
  | _, preformula.apprel f t, m => by
    simp only [liftFormulaAt, lift_formula_at_zero f m, lift_term_at_zero]
  | _, preformula.imp f₁ f₂, m => by
    simp only [liftFormulaAt, lift_formula_at_zero f₁ m, lift_formula_at_zero f₂ m]
  | _, preformula.all f, m => by
    simp only [liftFormulaAt, lift_formula_at_zero f (m + 1)]

lemma lift_formula_at2_small :
    ∀ {l} (f : @preformula L l) (n n') {m m'},
      m' ≤ m →
        liftFormulaAt (liftFormulaAt f n m) n' m' =
          liftFormulaAt (liftFormulaAt f n' m') n (m + n')
  | _, preformula.falsum, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H => by
    simp [liftFormulaAt, lift_term_at2_small, H]
  | _, preformula.rel R, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H =>
    by
    simp only [liftFormulaAt, lift_term_at2_small t n n' H]
    exact congrArg₂ preformula.apprel (lift_formula_at2_small f n n' H) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H =>
    by
    simp only [liftFormulaAt]
    exact
      congrArg₂ preformula.imp (lift_formula_at2_small f₁ n n' H)
        (lift_formula_at2_small f₂ n n' H)
  | _, preformula.all f, n, n', m, m', H =>
    by
    simp only [liftFormulaAt]
    have := lift_formula_at2_small f n n' (Nat.add_le_add_right H 1)
    rw [show m + 1 + n' = m + n' + 1 from by omega] at this
    exact congrArg preformula.all this

lemma lift_formula_at2_medium :
    ∀ {l} (f : @preformula L l) (n n') {m m'},
      m ≤ m' →
        m' ≤ m + n →
          liftFormulaAt (liftFormulaAt f n m) n' m' = liftFormulaAt f (n + n') m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, n, n', m, m', H₁, H₂ => by
    simp [liftFormulaAt, lift_term_at2_medium, H₁, H₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, n, n', m, m', H₁, H₂ =>
    by
    simp only [liftFormulaAt, lift_term_at2_medium t n' H₁ H₂]
    exact congrArg₂ preformula.apprel (lift_formula_at2_medium f n n' H₁ H₂) rfl
  | _, preformula.imp f₁ f₂, n, n', m, m', H₁, H₂ =>
    by
    simp only [liftFormulaAt]
    exact
      congrArg₂ preformula.imp (lift_formula_at2_medium f₁ n n' H₁ H₂)
        (lift_formula_at2_medium f₂ n n' H₁ H₂)
  | _, preformula.all f, n, n', m, m', H₁, H₂ =>
    by
    simp only [liftFormulaAt]
    exact
      congrArg preformula.all
        (lift_formula_at2_medium f n n' (Nat.add_le_add_right H₁ 1) (by omega))

lemma lift_formula_at2_eq {l} (f : @preformula L l) (n n' m : ℕ) :
    liftFormulaAt (liftFormulaAt f n m) n' (m + n) = liftFormulaAt f (n + n') m :=
  lift_formula_at2_medium f n n' (Nat.le_add_right _ _) (le_refl _)

lemma lift_formula_at2_large {l} (f : @preformula L l) (n n') {m m'} (H : m + n ≤ m') :
    liftFormulaAt (liftFormulaAt f n m) n' m' =
      liftFormulaAt (liftFormulaAt f n' (m' - n)) n m :=
  by
  have H₁ : n ≤ m' := Nat.le_trans (Nat.le_add_left _ _) H
  have H₂ : m ≤ m' - n := by omega
  rw [lift_formula_at2_small f n' n H₂, Nat.sub_add_cancel H₁]

@[simp]
lemma lift_formula_at_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l)
    (n m : ℕ) :
    liftFormulaAt (appsRel f ts) n m =
      appsRel (liftFormulaAt f n m) (ts.map (fun x => liftTermAt x n m)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [appsRel, DVec.map]; exact ih (preformula.apprel f x)

lemma lift_formula_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l) (n : ℕ) :
    liftFormula (appsRel f ts) n =
      appsRel (liftFormula f n) (ts.map (fun x => liftTerm x n)) :=
  lift_formula_at_apps_rel f ts n 0

/-! ## subst_formula — substitution into formulas -/


/-- Flypitch construction `subst_formula`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def substFormula : ∀ {l}, @preformula L l → term L → ℕ → @preformula L l
  | _, preformula.falsum, _, _ => preformula.falsum
  | _, preformula.equal t₁ t₂, s, n =>
    preformula.equal (substTerm t₁ s n) (substTerm t₂ s n)
  | _, preformula.rel R, _, _ => preformula.rel R
  | _, preformula.apprel f t, s, n =>
    preformula.apprel (substFormula f s n) (substTerm t s n)
  | _, preformula.imp f₁ f₂, s, n =>
    preformula.imp (substFormula f₁ s n) (substFormula f₂ s n)
  | _, preformula.all f, s, n => preformula.all (substFormula f s (n + 1))

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:95 f " [" s " // " n "]f" => Fol.substFormula f s n

lemma subst_formula_equal (t₁ t₂ s : term L) (n : ℕ) :
    substFormula (preformula.equal t₁ t₂) s n =
      preformula.equal (substTerm t₁ s n) (substTerm t₂ s n) :=
  rfl

@[simp]
lemma subst_formula_biimp (f₁ f₂ : formula L) (s : term L) (n : ℕ) :
    substFormula (biimp f₁ f₂) s n =
      biimp (substFormula f₁ s n) (substFormula f₂ s n) :=
  rfl

lemma lift_at_subst_formula_large :
    ∀ {l} (f : @preformula L l) (s : term L) {n₁} (n₂) {m},
      m ≤ n₁ →
        substFormula (liftFormulaAt f n₂ m) s (n₁ + n₂) =
          liftFormulaAt (substFormula f s n₁) n₂ m
  | _, preformula.falsum, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m, h => by
    simp [liftFormulaAt, substFormula, lift_at_subst_term_large _ s n₂ h]
  | _, preformula.rel R, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m, h => by
    simp [liftFormulaAt, substFormula, lift_at_subst_term_large t s n₂ h,
      lift_at_subst_formula_large f s n₂ h]
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m, h => by
    simp [liftFormulaAt, substFormula, lift_at_subst_formula_large f₁ s n₂ h,
      lift_at_subst_formula_large f₂ s n₂ h]
  | _, preformula.all f, s, n₁, n₂, m, h =>
    by
    simp only [liftFormulaAt, substFormula]
    have := lift_at_subst_formula_large f s n₂ (Nat.add_le_add_right h 1)
    rw [show n₁ + 1 + n₂ = n₁ + n₂ + 1 from by omega] at this
    exact congrArg preformula.all this

lemma lift_subst_formula_large {l} (f : @preformula L l) (s : term L) {n₁ n₂ : ℕ} :
    substFormula (liftFormula f n₂) s (n₁ + n₂) =
      liftFormula (substFormula f s n₁) n₂ :=
  lift_at_subst_formula_large f s n₂ (Nat.zero_le _)

lemma lift_subst_formula_large' {l} (f : @preformula L l) (s : term L) {n₁ n₂ : ℕ} :
    substFormula (liftFormula f n₂) s (n₂ + n₁) =
      liftFormula (substFormula f s n₁) n₂ :=
  by rw [Nat.add_comm]; exact lift_subst_formula_large f s

lemma lift_at_subst_formula_medium :
    ∀ {l} (f : @preformula L l) (s : term L) {n₁ n₂ m},
      m ≤ n₂ →
        n₂ ≤ m + n₁ →
          substFormula (liftFormulaAt f (n₁ + 1) m) s n₂ = liftFormulaAt f n₁ m
  | _, preformula.falsum, _, _, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m, h₁, h₂ => by
    simp [liftFormulaAt, substFormula, lift_at_subst_term_medium _ s h₁ h₂]
  | _, preformula.rel R, _, _, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m, h₁, h₂ => by
    simp [liftFormulaAt, substFormula, lift_at_subst_term_medium t s h₁ h₂,
      lift_at_subst_formula_medium f s h₁ h₂]
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m, h₁, h₂ => by
    simp [liftFormulaAt, substFormula, lift_at_subst_formula_medium f₁ s h₁ h₂,
      lift_at_subst_formula_medium f₂ s h₁ h₂]
  | _, preformula.all f, s, n₁, n₂, m, h₁, h₂ =>
    by
    simp only [liftFormulaAt, substFormula]
    have h : n₂ + 1 ≤ (m + 1) + n₁ := by omega
    exact
      congrArg preformula.all
        (lift_at_subst_formula_medium f s (Nat.add_le_add_right h₁ 1) h)

lemma lift_subst_formula_medium {l} (f : @preformula L l) (s : term L) (n₁ n₂ : ℕ) :
    substFormula (liftFormula f (n₁ + n₂ + 1)) s n₁ = liftFormula f (n₁ + n₂) :=
  lift_at_subst_formula_medium f s (Nat.zero_le _) (by omega)

lemma lift_at_subst_formula_eq {l} (f : @preformula L l) (s : term L) (n : ℕ) :
    substFormula (liftFormulaAt f 1 n) s n = f :=
  by
  have h : (1 : ℕ) = 0 + 1 := rfl
  rw [h, lift_at_subst_formula_medium f s (le_refl n) (le_refl n), lift_formula_at_zero]

@[simp]
lemma lift_formula1_subst {l} (f : @preformula L l) (s : term L) :
    substFormula (liftFormula f 1) s 0 = f :=
  lift_at_subst_formula_eq f s 0

lemma lift_at_subst_formula_small :
    ∀ {l} (f : @preformula L l) (s : term L) (n₁ n₂ m : ℕ),
      substFormula (liftFormulaAt f n₁ (m + n₂ + 1)) (liftTermAt s n₁ m) n₂ =
        liftFormulaAt (substFormula f s n₂) n₁ (m + n₂)
  | _, preformula.falsum, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s, n₁, n₂, m =>
    by
    simp only [liftFormulaAt, substFormula]
    exact
      congrArg₂ preformula.equal (lift_at_subst_term_small t₁ s n₁ n₂ m)
        (lift_at_subst_term_small t₂ s n₁ n₂ m)
  | _, preformula.rel R, _, _, _, _ => rfl
  | _, preformula.apprel f t, s, n₁, n₂, m =>
    by
    simp only [liftFormulaAt, substFormula]
    exact
      congrArg₂ preformula.apprel (lift_at_subst_formula_small f s n₁ n₂ m)
        (lift_at_subst_term_small t s n₁ n₂ m)
  | _, preformula.imp f₁ f₂, s, n₁, n₂, m =>
    by
    simp only [liftFormulaAt, substFormula]
    exact
      congrArg₂ preformula.imp (lift_at_subst_formula_small f₁ s n₁ n₂ m)
        (lift_at_subst_formula_small f₂ s n₁ n₂ m)
  | _, preformula.all f, s, n₁, n₂, m =>
    by
    simp only [liftFormulaAt, substFormula]
    have := lift_at_subst_formula_small f s n₁ (n₂ + 1) m
    simp only [Nat.add_assoc] at this
    exact congrArg preformula.all this

lemma lift_at_subst_formula_small0 {l} (f : @preformula L l) (s : term L) (n₁ m : ℕ) :
    substFormula (liftFormulaAt f n₁ (m + 1)) (liftTermAt s n₁ m) 0 =
      liftFormulaAt (substFormula f s 0) n₁ m :=
  lift_at_subst_formula_small f s n₁ 0 m

lemma subst_formula2 :
    ∀ {l} (f : @preformula L l) (s₁ s₂ : term L) (n₁ n₂ : ℕ),
      substFormula (substFormula f s₁ n₁) s₂ (n₁ + n₂) =
        substFormula (substFormula f s₂ (n₁ + n₂ + 1)) (substTerm s₁ s₂ n₂) n₁
  | _, preformula.falsum, _, _, _, _ => rfl
  | _, preformula.equal t₁ t₂, s₁, s₂, n₁, n₂ => by simp [substFormula, subst_term2]
  | _, preformula.rel R, _, _, _, _ => rfl
  | _, preformula.apprel f t, s₁, s₂, n₁, n₂ => by
    simp [substFormula, subst_term2, subst_formula2 f s₁ s₂ n₁ n₂]
  | _, preformula.imp f₁ f₂, s₁, s₂, n₁, n₂ => by
    simp [substFormula, subst_formula2 f₁ s₁ s₂ n₁ n₂, subst_formula2 f₂ s₁ s₂ n₁ n₂]
  | _, preformula.all f, s₁, s₂, n₁, n₂ =>
    by
    simp only [substFormula]
    have h := subst_formula2 f s₁ s₂ (n₁ + 1) n₂
    simp only [show n₁ + 1 + n₂ = n₁ + n₂ + 1 from by omega, ] at h
    exact congrArg preformula.all h

lemma subst_formula2_zero {l} (f : @preformula L l) (s₁ s₂ : term L) (n : ℕ) :
    substFormula (substFormula f s₁ 0) s₂ n =
      substFormula (substFormula f s₂ (n + 1)) (substTerm s₁ s₂ n) 0 :=
  by
  have h := subst_formula2 f s₁ s₂ 0 n
  simp only [Nat.zero_add] at h
  exact h

lemma lift_subst_formula_cancel :
    ∀ {l} (f : @preformula L l) (n : ℕ),
      substFormula (liftFormulaAt f 1 (n + 1)) (&0) n = f
  | _, preformula.falsum, _ => rfl
  | _, preformula.equal t₁ t₂, n => by
    simp [liftFormulaAt, substFormula, lift_subst_term_cancel]
  | _, preformula.rel R, _ => rfl
  | _, preformula.apprel f t, n => by
    simp [liftFormulaAt, substFormula, lift_subst_term_cancel t n,
      lift_subst_formula_cancel f n]
  | _, preformula.imp f₁ f₂, n => by
    simp [liftFormulaAt, substFormula, lift_subst_formula_cancel f₁ n,
      lift_subst_formula_cancel f₂ n]
  | _, preformula.all f, n =>
    by
    simp only [liftFormulaAt, substFormula]
    exact congrArg preformula.all (lift_subst_formula_cancel f (n + 1))

@[simp]
lemma subst_formula_apps_rel {l} (f : @preformula L l) (ts : DVec (term L) l) (s : term L)
    (n : ℕ) :
    substFormula (appsRel f ts) s n =
      appsRel (substFormula f s n) (ts.map (fun x => substTerm x s n)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [appsRel, DVec.map]; exact ih (preformula.apprel f x)

/-! ## count_quantifiers and quantifier_free -/


/-- Flypitch construction `count_quantifiers`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def countQuantifiers : ∀ {l}, @preformula L l → ℕ
  | _, preformula.falsum => 0
  | _, preformula.equal _ _ => 0
  | _, preformula.rel _ => 0
  | _, preformula.apprel _ _ => 0
  | _, preformula.imp f₁ f₂ => countQuantifiers f₁ + countQuantifiers f₂
  | _, preformula.all f => countQuantifiers f + 1

@[simp]
theorem count_quantifiers_succ {l} (f : @preformula L (l + 1)) :
    countQuantifiers f = 0 := by cases f <;> rfl

@[simp]
lemma count_quantifiers_subst :
    ∀ {l} (f : @preformula L l) (s : term L) (n : ℕ),
      countQuantifiers (substFormula f s n) = countQuantifiers f
  | _, preformula.falsum, _, _ => rfl
  | _, preformula.equal _ _, _, _ => rfl
  | _, preformula.rel _, _, _ => rfl
  | _, preformula.apprel _ _, _, _ => rfl
  | _, preformula.imp f₁ f₂, s, n => by
    simp [count_quantifiers_subst f₁ s n, count_quantifiers_subst f₂ s n]
  | _, preformula.all f, s, n => by simp [count_quantifiers_subst f s (n + 1)]

/-- Flypitch construction `quantifier_free`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def quantifierFree {l} : @preformula L l → Prop := fun f => countQuantifiers f = 0

/-! ## prf — the proof system (src/fol.lean lines 816-824) -/


/-- `prf Γ A` is the type of proofs of `A` from hypotheses `Γ` in
classical first-order logic. -/
inductive prf : Set (formula L) → formula L → Type u
  | axm {Γ A} (h : A ∈ Γ) : prf Γ A
  | impI {Γ : Set (formula L)} {A B} (h : prf (insert A Γ) B) : prf Γ (A ⟹ B)
  | impE {Γ} (A) {B} (h₁ : prf Γ (A ⟹ B)) (h₂ : prf Γ A) : prf Γ B
  | falsumE {Γ : Set (formula L)} {A} (h : prf (insert (∼A) Γ) ⊥') : prf Γ A
  | allI {Γ A} (h : prf (liftFormula1 '' Γ) A) : prf Γ (∀'A)
  | allE₂ {Γ} (A) (t : term L) (h : prf Γ (∀'A)) : prf Γ (A [t // 0]f)
  | ref (Γ) (t : term L) : prf Γ (t ≃ t)
  |
  subst₂ {Γ} (s t : term L) (f : formula L) (h₁ : prf Γ (s ≃ t))
    (h₂ : prf Γ (f [s // 0]f)) : prf Γ (f [t // 0]f)

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:51 " ⊢ " => Fol.prf

/-- Flypitch construction `provable`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def provable (T : Set (formula L)) (f : formula L) :=
  Nonempty (T ⊢ f)

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:51 " ⊢' " => Fol.provable

/-! ## Derived proof rules (src/fol.lean lines 832-1103) -/


/-- Flypitch construction `allE`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def allE {Γ} (A : formula L) (t : term L) {B} (H₁ : Γ ⊢ ∀'A) (H₂ : A [t // 0]f = B) :
    Γ ⊢ B := by subst H₂; exact prf.allE₂ A t H₁

/-- Flypitch construction `prf_subst`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def prfSubst {Γ} {s t : term L} (f₁ : formula L) {f₂} (H₁ : Γ ⊢ s ≃ t)
    (H₂ : Γ ⊢ f₁ [s // 0]f) (H₃ : f₁ [t // 0]f = f₂) : Γ ⊢ f₂ := by
  subst H₃;
  exact prf.subst₂ s t f₁ H₁ H₂

/-- Flypitch construction `axm1`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def axm1 {Γ : Set (formula L)} {A : formula L} : insert A Γ ⊢ A :=
  prf.axm (Set.mem_insert A Γ)

/-- Flypitch construction `axm2`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def axm2 {Γ : Set (formula L)} {A B : formula L} : insert A (insert B Γ) ⊢ B :=
  prf.axm (Set.mem_insert_of_mem A (Set.mem_insert B Γ))

/-- Flypitch construction `weakening`, retained by the first-order soundness and completeness
development.
-/
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

/-- Flypitch construction `prf_lift`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def prfLift {Γ : Set (formula L)} {f : formula L} (n m : ℕ) (H : Γ ⊢ f) :
    (fun f' => liftFormulaAt f' n m) '' Γ ⊢ liftFormulaAt f n m := by
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
      liftFormulaAt (A [t // 0]f) n m =
        (liftFormulaAt A n (m + 1)) [liftTermAt t n m // 0]f :=
      (lift_at_subst_formula_small0 A t n m).symm
    rw [key]
    exact prf.allE₂ _ _ (ih m)
  | ref => exact prf.ref _ _
  | subst₂ s t f _ _ ih₁
    ih₂ =>
    have key1 :
      liftFormulaAt (f [t // 0]f) n m =
        (liftFormulaAt f n (m + 1)) [liftTermAt t n m // 0]f :=
      (lift_at_subst_formula_small0 f t n m).symm
    have key2 :
      liftFormulaAt (f [s // 0]f) n m =
        (liftFormulaAt f n (m + 1)) [liftTermAt s n m // 0]f :=
      (lift_at_subst_formula_small0 f s n m).symm
    rw [key1]
    apply prf.subst₂
    · exact ih₁ m
    · have h := ih₂ m
      rw [key2] at h
      exact h

/-- Flypitch construction `prf_substitution`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def prfSubstitution {Γ : Set (formula L)} {f : formula L} (t : term L)
    (n : ℕ) (H : Γ ⊢ f) : (fun x => substFormula x t n) '' Γ ⊢ substFormula f t n := by
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
      substFormula (substFormula A s 0) t n =
        substFormula (substFormula A t (n + 1)) (substTerm s t n) 0 :=
      subst_formula2_zero A s t n
    rw [key]
    exact prf.allE₂ _ _ (ih n)
  | ref => exact prf.ref _ _
  | subst₂ s u f _ _ ih₁
    ih₂ =>
    have key1 :
      substFormula (substFormula f u 0) t n =
        substFormula (substFormula f t (n + 1)) (substTerm u t n) 0 :=
      subst_formula2_zero f u t n
    have key2 :
      substFormula (substFormula f s 0) t n =
        substFormula (substFormula f t (n + 1)) (substTerm s t n) 0 :=
      subst_formula2_zero f s t n
    rw [key1]
    apply prf.subst₂
    · exact ih₁ n
    · have h := ih₂ n
      rw [key2] at h
      exact h

/-- Flypitch construction `reflect_prf_lift1`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def reflectPrfLift1 {Γ : Set (formula L)} {f : formula L}
    (h : liftFormula1 '' Γ ⊢ liftFormula f 1) : Γ ⊢ f :=
  by
  have h2 := prfSubstitution (&0) 0 h
  simp only [Set.image_image, lift_formula1_subst] at h2
  convert h2 using 1
  simp []

/-- Flypitch construction `weakening1`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def weakening1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₂) :
    insert f₁ Γ ⊢ f₂ :=
  weakening (Set.subset_insert f₁ Γ) H

/-- Flypitch construction `weakening2`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def weakening2 {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H : insert f₁ Γ ⊢ f₂) : insert f₁ (insert f₃ Γ) ⊢ f₂ :=
  weakening (Set.insert_subset_insert (Set.subset_insert _ Γ)) H

/-- Flypitch construction `deduction`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def deduction {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A ⟹ B) :
    insert A Γ ⊢ B :=
  prf.impE A (weakening1 H) axm1

/-- Flypitch construction `exfalso`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def exfalso {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ ⊥') : Γ ⊢ A :=
  prf.falsumE (weakening1 H)

theorem exfalso' {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢' ⊥') : Γ ⊢' A :=
  H.map exfalso

/-- Flypitch construction `notI`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def notI {Γ : Set (formula L)} {A : formula L} (H : Γ ⊢ A ⟹ ⊥') : Γ ⊢ ∼A :=
  H

/-- Flypitch construction `andI`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def andI {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : Γ ⊢ f₁)
    (H₂ : Γ ⊢ f₂) : Γ ⊢ f₁ ⊓' f₂ := by
  apply prf.impI
  apply prf.impE f₂
  · apply prf.impE f₁
    · exact axm1
    · exact weakening1 H₁
  · exact weakening1 H₂

/-- Flypitch construction `andE1`, retained by the first-order soundness and completeness
development.
-/
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

/-- Flypitch construction `andE2`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def andE2 {Γ : Set (formula L)} (f₁ : formula L) {f₂ : formula L}
    (H : Γ ⊢ f₁ ⊓' f₂) : Γ ⊢ f₂ := by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H)
  apply prf.impI
  exact axm2

/-- Flypitch construction `orI1`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def orI1 {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ A) : Γ ⊢ A ⊔' B :=
  by
  apply prf.impI
  apply exfalso
  apply prf.impE _ axm1
  exact weakening1 H

/-- Flypitch construction `orI2`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def orI2 {Γ : Set (formula L)} {A B : formula L} (H : Γ ⊢ B) : Γ ⊢ A ⊔' B :=
  prf.impI (weakening1 H)

/-- Flypitch construction `orE`, retained by the first-order soundness and completeness
development.
-/
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

/-- Flypitch construction `biimpI`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def biimpI {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : insert f₁ Γ ⊢ f₂)
    (H₂ : insert f₂ Γ ⊢ f₁) : Γ ⊢ f₁ ⇔ f₂ :=
  andI (prf.impI H₁) (prf.impI H₂)

/-- Flypitch construction `biimpE1`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def biimpE1 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) :
    insert f₁ Γ ⊢ f₂ :=
  deduction (andE1 _ H)

/-- Flypitch construction `biimpE2`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def biimpE2 {Γ : Set (formula L)} {f₁ f₂ : formula L} (H : Γ ⊢ f₁ ⇔ f₂) :
    insert f₂ Γ ⊢ f₁ :=
  deduction (andE2 _ H)

/-- Flypitch construction `exI`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def exI {Γ : Set (formula L)} {f : formula L} (t : term L)
    (H : Γ ⊢ f [t // 0]f) : Γ ⊢ ∃'f :=
  by
  apply prf.impI
  apply prf.impE (f [t // 0]f) _ (weakening1 H)
  exact prf.allE₂ (∼f) t axm1

/-- Flypitch construction `exE`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def exE {Γ : Set (formula L)} {f₁ f₂ : formula L} (H₁ : Γ ⊢ ∃'f₁)
    (H₂ : insert f₁ (liftFormula1 '' Γ) ⊢ liftFormula1 f₂) : Γ ⊢ f₂ :=
  by
  apply prf.falsumE
  apply prf.impE _ (weakening1 H₁)
  apply prf.allI
  apply prf.impI
  rw [Set.image_insert_eq]
  apply prf.impE _ axm2
  exact weakening2 H₂

/-- Flypitch construction `ex_not_of_not_all`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def exNotOfNotAll {Γ : Set (formula L)} {f : formula L}
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

/-- Flypitch construction `not_and_self`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def notAndSelf {Γ : Set (formula L)} {f : formula L} (H : Γ ⊢ f ⊓' (∼f)) :
    Γ ⊢ ⊥' :=
  prf.impE f (andE2 f H) (andE1 (∼f) H)

/-- Flypitch construction `prf_symm`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def prfSymm {Γ : Set (formula L)} {s t : term L} (H : Γ ⊢ s ≃ t) :
    Γ ⊢ t ≃ s := by
  apply prfSubst (&0 ≃ liftTerm s 1) H
  · simp only [substFormula, subst_term_var_eq, lift_term_def, lift_term_at_zero,
      lift_term1_subst_term];
    exact prf.ref _ _
  · simp [lift_term1_subst_term]

/-- Flypitch construction `prf_trans`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def prfTrans {Γ : Set (formula L)} {t₁ t₂ t₃ : term L} (H : Γ ⊢ t₁ ≃ t₂)
    (H' : Γ ⊢ t₂ ≃ t₃) : Γ ⊢ t₁ ≃ t₃ :=
  by
  apply prfSubst (liftTerm t₁ 1 ≃ &0) H'
  · simp only [substFormula, lift_term1_subst_term, subst_term_var_eq, lift_term_def,
      lift_term_at_zero];
    exact H
  · simp [lift_term1_subst_term]

/-- Flypitch construction `prf_congr`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def prfCongr {Γ : Set (formula L)} {t₁ t₂ : term L} (s : term L)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ substTerm s t₁ 0 ≃ substTerm s t₂ 0 :=
  by
  apply prfSubst (liftTerm (substTerm s t₁ 0) 1 ≃ s) H
  · simp only [substFormula, lift_term1_subst_term]; exact prf.ref _ _
  · simp [lift_term1_subst_term]

/-- Flypitch construction `app_congr`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def appCongr {Γ : Set (formula L)} {t₁ t₂ : term L} (s : preterm L 1)
    (H : Γ ⊢ t₁ ≃ t₂) : Γ ⊢ preterm.app s t₁ ≃ preterm.app s t₂ :=
  by
  have h := prfCongr (preterm.app (liftTerm s 1) (&0)) H
  simp only [Nat.reduceAdd, subst_term_app, lift_term1_subst_term, subst_term_var_eq,
    lift_term_def, lift_term_at_zero] at h
  exact h

/-- Flypitch construction `apprel_congr`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def apprelCongr {Γ : Set (formula L)} {t₁ t₂ : term L}
    (f : @preformula L 1) (H : Γ ⊢ t₁ ≃ t₂) (H₂ : Γ ⊢ preformula.apprel f t₁) :
    Γ ⊢ preformula.apprel f t₂ :=
  by
  apply prfSubst (preformula.apprel (liftFormula f 1) (&0)) H
  · simp only [substFormula, Nat.reduceAdd, lift_formula1_subst, subst_term_var_eq,
      lift_term_def, lift_term_at_zero];
    exact H₂
  · simp

/-- Flypitch construction `imp_trans`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def impTrans {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H₁ : Γ ⊢ f₁ ⟹ f₂) (H₂ : Γ ⊢ f₂ ⟹ f₃) : Γ ⊢ f₁ ⟹ f₃ :=
  by
  apply prf.impI
  apply prf.impE _ (weakening1 H₂)
  exact prf.impE _ (weakening1 H₁) axm1

/-- Flypitch construction `biimp_refl`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def biimpReflCertificate (Γ : Set (formula L)) (f : formula L) : Γ ⊢ f ⇔ f :=
  biimpI axm1 axm1

/-- Flypitch construction `biimp_trans`, retained by the first-order soundness and completeness
development.
-/
@[expose]
noncomputable def biimpTrans {Γ : Set (formula L)} {f₁ f₂ f₃ : formula L}
    (H₁ : Γ ⊢ f₁ ⇔ f₂) (H₂ : Γ ⊢ f₂ ⇔ f₃) : Γ ⊢ f₁ ⇔ f₃ :=
  andI (impTrans (andE1 _ H₁) (andE1 _ H₂)) (impTrans (andE2 _ H₂) (andE2 _ H₁))

/-- Flypitch construction `equal_preterms`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def equalPreterms (T : Set (formula L)) {l} (t₁ t₂ : preterm L l) : Type u :=
  ∀ (ts : DVec (term L) l), T ⊢ apps t₁ ts ≃ apps t₂ ts

/-- Flypitch construction `equal_preterms_app`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def equalPretermsApp {T : Set (formula L)} {l} {t t' : preterm L (l + 1)}
    {s s' : term L} (Ht : equalPreterms T t t') (Hs : T ⊢ s ≃ s') :
    equalPreterms T (preterm.app t s) (preterm.app t' s') :=
  by
  intro xs
  apply prfTrans (Ht (DVec.cons s xs))
  have h := prfCongr (apps (liftTerm t' 1) (DVec.cons (&0) (xs.map liftTerm1))) Hs
  simp only [apps, liftTerm1, subst_term_apps, subst_term_app, lift_term1_subst_term,
    subst_term_var_eq, lift_term_def, lift_term_at_zero, DVec.map_map, DVec.map_id] at h
  exact h

/-- Flypitch construction `equal_preterms_refl`, retained by the first-order soundness and
completeness development.
-/
@[refl, expose]
noncomputable def equalPretermsRefl (T : Set (formula L)) {l} (t : preterm L l) :
    equalPreterms T t t := fun xs => prf.ref T (apps t xs)

/-- Flypitch construction `equiv_preformulae`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def equivPreformulae (T : Set (formula L)) {l} (f₁ f₂ : @preformula L l) : Type u :=
  ∀ (ts : DVec (term L) l), T ⊢ appsRel f₁ ts ⇔ appsRel f₂ ts

/-- Flypitch construction `equiv_preformulae_apprel`, retained by the first-order soundness and
completeness development.
-/
@[expose]
noncomputable def equivPreformulaeApprel {T : Set (formula L)} {l}
    {f f' : @preformula L (l + 1)} {s s' : term L} (Ht : equivPreformulae T f f')
    (Hs : T ⊢ s ≃ s') :
    equivPreformulae T (preformula.apprel f s) (preformula.apprel f' s') :=
  by
  intro xs
  apply biimpTrans (Ht (DVec.cons s xs))
  apply
    prfSubst
      (appsRel (liftFormula f' 1) (DVec.cons (liftTerm1 s) (xs.map liftTerm1)) ⇔
        appsRel (liftFormula f' 1) (DVec.cons (&0) (xs.map liftTerm1)))
      Hs
  · -- H₂: T ⊢ f₁ [s // 0]f. After simp, becomes biimp_refl.
    simp only [subst_formula_biimp, subst_formula_apps_rel, DVec.map, DVec.map_map,
      lift_term1_subst_term, subst_term_var0]
    exact biimpReflCertificate T _
  · -- H₃: f₁ [s' // 0]f = goal. After simp, becomes the target equation.
    simp only [subst_formula_biimp, subst_formula_apps_rel, DVec.map, DVec.map_map,
      lift_term1_subst_term, subst_term_var0]
    simp only [DVec.map_id, appsRel, lift_formula1_subst]

/-- Flypitch construction `equiv_preformulae_refl`, retained by the first-order soundness and
completeness development.
-/
@[refl, expose]
noncomputable def equivPreformulaeRefl (T : Set (formula L)) {l} (f : @preformula L l) :
    equivPreformulae T f f := fun xs => biimpReflCertificate T (appsRel f xs)

theorem impI' {Γ : Set (formula L)} {A B : formula L} (h : insert A Γ ⊢' B) :
    Γ ⊢' (A ⟹ B) :=
  h.map prf.impI

theorem impE' {Γ : Set (formula L)} (A : formula L) {B : formula L} (h₁ : Γ ⊢' A ⟹ B)
    (h₂ : Γ ⊢' A) : Γ ⊢' B :=
  h₁.map2 (prf.impE _) h₂

theorem falsumE' {Γ : Set (formula L)} {A : formula L} (h : insert (∼A) Γ ⊢' ⊥') :
    Γ ⊢' A :=
  h.map prf.falsumE

theorem allI' {Γ : Set (formula L)} {A : formula L} (h : liftFormula1 '' Γ ⊢' A) :
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
  H₁.map2 (fun x y => prfSubst _ x y H₃) H₂

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
  ⟨Nonempty.map (apprelCongr f H), Nonempty.map (apprelCongr f (prfSymm H))⟩

lemma prf_all_iff {Γ : Set (formula L)} {f : formula L} :
    Γ ⊢' ∀'f ↔ liftFormula1 '' Γ ⊢' f :=
  by
  constructor
  · intro H
    rw [← lift_subst_formula_cancel f 0]
    apply allE₂'
    exact H.map (prfLift 1 0)
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


/-- Flypitch construction `Theory`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def Theory (L : Language.{u}) :=
  Set (formula L)

/-- Flypitch construction `is_consistent`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def isConsistent (T : Theory L) :=
  ¬(T ⊢' ⊥')

/-! ## Structure — L-structures (src/fol.lean line 1109) -/


variable (L)

/-- Flypitch construction `Structure`, retained by the first-order soundness and completeness
development.
-/
structure Structure : Type (u + 1) where
  /-- The `carrier` component of the corresponding first-order structure. -/
  carrier : Type u
  /-- The `fun_map` component of the corresponding first-order structure. -/
  funMap : ∀ {n}, L.functions n → DVec carrier n → carrier
  /-- The `rel_map` component of the corresponding first-order structure. -/
  relMap : ∀ {n}, L.relations n → DVec carrier n → Prop

variable {L}

instance : CoeSort (Structure L) (Type u) where coe S := S.carrier

/-! ## realize_term — realization of terms in a structure -/


/-- Flypitch construction `realize_term`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def realizeTerm {S : Structure L} (v : ℕ → S) :
    ∀ {l} (_t : preterm L l) (_xs : DVec S l), S.carrier
  | _, preterm.var k, _ => v k
  | _, preterm.func f, xs => S.funMap f xs
  | _, preterm.app t₁ t₂, xs =>
    realizeTerm v t₁ (DVec.cons (realizeTerm v t₂ DVec.nil) xs)

lemma realize_term_congr {S : Structure L} {v v' : ℕ → S} (h : ∀ n, v n = v' n) :
    ∀ {l} (t : preterm L l) (xs : DVec S l), realizeTerm v t xs = realizeTerm v' t xs
  | _, preterm.var k, _ => h k
  | _, preterm.func _, _ => rfl
  | _, preterm.app t₁ t₂, xs => by
    simp only [realizeTerm]
    rw [realize_term_congr h t₁, realize_term_congr h t₂]

lemma realize_term_subst {S : Structure L} (v : ℕ → S) :
    ∀ {l} (n : ℕ) (t : preterm L l) (s : term L) (xs : DVec S l),
      realizeTerm (substRealize v (realizeTerm v (liftTerm s n) DVec.nil) n) t xs =
        realizeTerm v (substTerm t s n) xs
  | _, n, preterm.var k, s, DVec.nil =>
    by
    rcases Nat.lt_trichotomy k n with h | h | h
    · simp only [realizeTerm, subst_realize_lt _ _ h, subst_term_var_lt _ h]
    · subst h
      simp only [realizeTerm, subst_term_var_eq, subst_realize_var_eq, liftTerm]
    · simp only [realizeTerm, subst_realize_gt _ _ h, subst_term_var_gt _ h]
  | _, _, preterm.func _, _, _ => rfl
  | _, n, preterm.app t₁ t₂, s, xs =>
    by
    simp only [realizeTerm, substTerm]
    rw [realize_term_subst v n t₂ s DVec.nil]
    rw [realize_term_subst v n t₁ s]

lemma realize_term_subst_lift {S : Structure L} (v : ℕ → S) (x : S) (m : ℕ) :
    ∀ {l} (t : preterm L l) (xs : DVec S l),
      realizeTerm (substRealize v x m) (liftTermAt t 1 m) xs = realizeTerm v t xs
  | _, preterm.var k, DVec.nil =>
    by
    simp only [realizeTerm, liftTermAt]
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
    simp only [realizeTerm, liftTermAt]
    rw [realize_term_subst_lift v x m t₂ DVec.nil]
    rw [realize_term_subst_lift v x m t₁]

/-! ## realize_formula — satisfaction relation -/


/-- Flypitch construction `realize_formula`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def realizeFormula {S : Structure L} : ∀ {l}, (ℕ → S) → @preformula L l → DVec S l → Prop
  | _, _v, preformula.falsum, _ => False
  | _, v, preformula.equal t₁ t₂, _ =>
    realizeTerm v t₁ DVec.nil = realizeTerm v t₂ DVec.nil
  | _, _, preformula.rel R, xs => S.relMap R xs
  | _, v, preformula.apprel f t, xs =>
    realizeFormula v f (DVec.cons (realizeTerm v t DVec.nil) xs)
  | _, v, preformula.imp f₁ f₂, xs => realizeFormula v f₁ xs → realizeFormula v f₂ xs
  | _, v, preformula.all f, _ => ∀ x : S, realizeFormula (substRealize v x 0) f DVec.nil

lemma realize_formula_congr {S : Structure L} :
    ∀ {l} {v v' : ℕ → S} (_h : ∀ n, v n = v' n) (f : @preformula L l) (xs : DVec S l),
      realizeFormula v f xs ↔ realizeFormula v' f xs
  | _, _, _, _, preformula.falsum, _ => Iff.rfl
  | _, _, _, h, preformula.equal t₁ t₂, _ => by
    simp [realizeFormula, realize_term_congr h]
  | _, _, _, _, preformula.rel _, _ => Iff.rfl
  | _, _, _, h, preformula.apprel f t, xs =>
    by
    simp only [realizeFormula, realize_term_congr h]
    exact realize_formula_congr h f _
  | _, _, _, h, preformula.imp f₁ f₂, xs =>
    by
    simp only [realizeFormula]
    exact Iff.imp (realize_formula_congr h f₁ xs) (realize_formula_congr h f₂ xs)
  | _, _, _, h, preformula.all f, _ =>
    by
    simp only [realizeFormula]
    apply forall_congr'
    intro x
    exact realize_formula_congr (subst_realize_congr h x 0) f DVec.nil

lemma realize_formula_subst {S : Structure L} :
    ∀ {l} (v : ℕ → S) (n : ℕ) (f : @preformula L l) (s : term L) (xs : DVec S l),
      realizeFormula (substRealize v (realizeTerm v (liftTerm s n) DVec.nil) n) f xs ↔
        realizeFormula v (substFormula f s n) xs
  | _, _, _, preformula.falsum, _, _ => Iff.rfl
  | _, v, n, preformula.equal t₁ t₂, s, _ => by simp [realizeFormula, realize_term_subst]
  | _, _, _, preformula.rel _, _, _ => Iff.rfl
  | _, v, n, preformula.apprel f t, s, xs =>
    by
    simp only [realizeFormula, substFormula, realize_term_subst]
    exact realize_formula_subst v n f s _
  | _, v, n, preformula.imp f₁ f₂, s, xs =>
    by
    simp only [realizeFormula, substFormula]
    exact Iff.imp (realize_formula_subst v n f₁ s xs) (realize_formula_subst v n f₂ s xs)
  | _, v, n, preformula.all f, s, _ =>
    by
    simp only [realizeFormula, substFormula]
    apply forall_congr'
    intro x
    rw [← realize_formula_subst (substRealize v x 0) (n + 1) f s DVec.nil]
    apply realize_formula_congr
    intro k
    rw [subst_realize2_0]
    congr 1
      -- Goal: realize_term v (lift_term s n) [] = realize_term
            -- (subst_realize v x 0) (lift_term s (n+1)) []
    rw [← realize_term_subst_lift v x 0 (liftTerm s n) DVec.nil]
    simp only [lift_term_def]
    rw [← lift_term2 s n 1]

lemma realize_formula_subst0 {S : Structure L} {l} (v : ℕ → S) (f : @preformula L l)
    (s : term L) (xs : DVec S l) :
    realizeFormula (substRealize v (realizeTerm v s DVec.nil) 0) f xs ↔
      realizeFormula v (substFormula f s 0) xs :=
  by
  have h := realize_formula_subst v 0 f s
  simp only [lift_term_zero] at h
  exact h xs

lemma realize_formula_subst_lift {S : Structure L} :
    ∀ {l} (v : ℕ → S) (x : S) (m : ℕ) (f : @preformula L l) (xs : DVec S l),
      realizeFormula (substRealize v x m) (liftFormulaAt f 1 m) xs =
        realizeFormula v f xs
  | _, _, _, _, preformula.falsum, _ => rfl
  | _, v, x, m, preformula.equal t₁ t₂, _ => by
    simp [realizeFormula, realize_term_subst_lift]
  | _, _, _, _, preformula.rel _, _ => rfl
  | _, v, x, m, preformula.apprel f t, xs =>
    by
    simp only [realizeFormula, liftFormulaAt, realize_term_subst_lift]
    exact realize_formula_subst_lift v x m f _
  | _, v, x, m, preformula.imp f₁ f₂, xs =>
    by
    simp only [realizeFormula, liftFormulaAt]
    exact
      propext
        (Iff.imp (Iff.of_eq (realize_formula_subst_lift v x m f₁ xs))
          (Iff.of_eq (realize_formula_subst_lift v x m f₂ xs)))
  | _, v, x, m, preformula.all f, _ =>
    by
    simp only [realizeFormula, liftFormulaAt]
    apply propext
    apply forall_congr'
    intro x'
    rw [propext
        (realize_formula_congr (fun k => subst_realize2_0 v x' x m k)
          (liftFormulaAt f 1 (m + 1)) DVec.nil)]
    exact
      Iff.of_eq (realize_formula_subst_lift (substRealize v x' 0) x (m + 1) f DVec.nil)

/-! ## Semantic notions — satisfaction and models -/


/-- Flypitch construction `satisfied_in`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def satisfiedIn (S : Structure L) (f : formula L) : Prop :=
  ∀ v : ℕ → S, realizeFormula v f DVec.nil

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:51 " ⊨ₛ " => Fol.satisfiedIn

/-- Flypitch construction `all_satisfied_in`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def allSatisfiedIn (S : Structure L) (T : Set (formula L)) : Prop :=
  ∀ {{f}}, f ∈ T → S ⊨ₛ f

/-- Flypitch construction `satisfied`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def satisfied (T : Set (formula L)) (f : formula L) : Prop :=
  ∀ (S : Structure L) (v : ℕ → S),
    (∀ f' ∈ T, realizeFormula v (f' : formula L) DVec.nil) → realizeFormula v f DVec.nil

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:51 " ⊨ " => Fol.satisfied

/-- Flypitch construction `all_satisfied`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def allSatisfied (T T' : Set (formula L)) : Prop :=
  ∀ {{f}}, f ∈ T' → T ⊨ f

theorem satisfied_in_trans {S : Structure L} {T : Set (formula L)} {f : formula L}
    (H' : allSatisfiedIn S T) (H : T ⊨ f) : S ⊨ₛ f := fun v =>
  H S v (fun _f' hf' => H' hf' v)

theorem all_satisfied_in_trans {S : Structure L} {T T' : Set (formula L)}
    (H' : allSatisfiedIn S T) (H : allSatisfied T T') : allSatisfiedIn S T' :=
  fun _f hf => satisfied_in_trans H' (H hf)

theorem satisfied_of_mem {T : Set (formula L)} {f : formula L} (hf : f ∈ T) : T ⊨ f :=
  fun _S _v h => h f hf

theorem all_satisfied_of_subset {T T' : Set (formula L)} (h : T' ⊆ T) :
    allSatisfied T T' := fun _f hf => satisfied_of_mem (h hf)

theorem satisfied_trans {T₁ T₂ : Set (formula L)} {f : formula L}
    (H' : allSatisfied T₁ T₂) (H : T₂ ⊨ f) : T₁ ⊨ f := fun S v h =>
  H S v (fun _f' hf' => H' hf' S v h)

theorem all_satisfied_trans {T₁ T₂ T₃ : Set (formula L)} (H' : allSatisfied T₁ T₂)
    (H : allSatisfied T₂ T₃) : allSatisfied T₁ T₃ := fun _f hf =>
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
    exact ih v hΓ (realizeTerm v t DVec.nil)
  | ref => intro v _; simp [realizeFormula]
  | subst₂ s t f _ _ ih₁ ih₂ =>
    intro v hΓ
    have h' := ih₁ v hΓ
    simp only [realizeFormula] at h'
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
inductive BoundedPreterm (L : Language.{u}) (n : ℕ) : ℕ → Type u
  | bd_var : ∀ (_k : Fin n), BoundedPreterm L n 0
  | bd_func : ∀ {l : ℕ} (_f : L.functions l), BoundedPreterm L n l
  |
  bd_app :
    ∀ {l : ℕ} (_t : BoundedPreterm L n (l + 1)) (_s : BoundedPreterm L n 0),
      BoundedPreterm L n l

export BoundedPreterm (bd_var bd_func bd_app)

/-- A fully applied bounded term with at most `n` free variables.
-/
abbrev boundedTerm (n : ℕ) :=
  BoundedPreterm L n 0

/-- A closed preterm (no free variables), needing `l` more
arguments. -/
abbrev closedPreterm (l : ℕ) :=
  BoundedPreterm L 0 l

/-- A closed term: no free variables and fully applied. -/
abbrev closedTerm :=
  closedPreterm L 0

variable {L}

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
prefix:max "&ᵇ" => @bd_var _ _

/-- Flypitch construction `bd_const`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def bdConst {n} (c : L.constants) : boundedTerm L n :=
  bd_func c

/-- Apply a bounded preterm of level `l + m` to `m` bounded terms
to get level `l`. -/
@[simp, expose]
def bdApps' {n} :
    ∀ {l m : ℕ},
      BoundedPreterm L n (l + m) → DVec (boundedTerm L n) m → BoundedPreterm L n l
  | _, 0, t, DVec.nil => t
  | _l, _m + 1, t, DVec.cons x xs => bdApps' (bd_app t x) xs

/-- Apply a bounded preterm of level `l` to `l` bounded terms to
get a bounded term. -/
@[simp, expose]
def bdApps {n} :
    ∀ {l}, BoundedPreterm L n l → DVec (boundedTerm L n) l → boundedTerm L n
  | _, t, DVec.nil => t
  | _, t, DVec.cons t' ts => bdApps (bd_app t t') ts

namespace BoundedPreterm

/-- Forget boundedness: map a bounded preterm to an ordinary
preterm. -/
@[simp, expose]
protected def fst {n} : ∀ {l}, BoundedPreterm L n l → preterm L l
  | _, bd_var k => &k.1
  | _, bd_func f => preterm.func f
  | _, bd_app t s => preterm.app (BoundedPreterm.fst t) (BoundedPreterm.fst s)

/-- Equality of bounded preterms is determined by their
underlying preterms. -/
@[ext]
protected theorem eq {n} :
    ∀ {l} {t₁ t₂ : BoundedPreterm L n l}, t₁.fst = t₂.fst → t₁ = t₂
  | _, bd_var k, bd_var k', h =>
    by
    simp only [BoundedPreterm.fst, preterm.var.injEq] at h
    congr 1; exact Fin.ext h
  | _, bd_var _, bd_func _, h => by simp [BoundedPreterm.fst] at h
  | _, bd_var _, bd_app _ _, h => by simp [BoundedPreterm.fst] at h
  | _, bd_func _, bd_var _, h => by simp [BoundedPreterm.fst] at h
  | _, bd_func f, bd_func f', h => by
    simp only [BoundedPreterm.fst, preterm.func.injEq] at h; exact congrArg bd_func h
  | _, bd_func _, bd_app _ _, h => by simp [BoundedPreterm.fst] at h
  | _, bd_app _ _, bd_var _, h => by simp [BoundedPreterm.fst] at h
  | _, bd_app _ _, bd_func _, h => by simp [BoundedPreterm.fst] at h
  | _, bd_app t₁ t₂, bd_app t₁' t₂', h =>
    by
    simp only [BoundedPreterm.fst, preterm.app.injEq] at h
    exact congrArg₂ bd_app (BoundedPreterm.eq h.1) (BoundedPreterm.eq h.2)

/-- Cast a bounded_preterm L n l to one with a larger bound m ≥
n. -/
@[simp, expose]
protected def cast {n m} (h : n ≤ m) :
    ∀ {l}, BoundedPreterm L n l → BoundedPreterm L m l
  | _, bd_var k => bd_var ⟨k.1, Nat.lt_of_lt_of_le k.2 h⟩
  | _, bd_func f => bd_func f
  | _, bd_app t s => bd_app (t.cast h) (s.cast h)

@[simp]
lemma cast_bd_app {n m} (h : n ≤ m) {l} {t : BoundedPreterm L n (l + 1)}
    {s : BoundedPreterm L n 0} : (bd_app t s).cast h = bd_app (t.cast h) (s.cast h) :=
  rfl

@[simp]
lemma cast_bd_apps {n m} (h : n ≤ m) {l} {t : BoundedPreterm L n l}
    {ts : DVec (boundedTerm L n) l} :
    (bdApps t ts).cast h = bdApps (t.cast h) (ts.map (fun x => x.cast h)) := by
  induction ts with
  | nil => rfl
  | cons x xs ih => simp only [bdApps, DVec.map]; exact ih

@[simp]
lemma cast_irrel {n m} {h h' : n ≤ m} :
    ∀ {l} (t : BoundedPreterm L n l), t.cast h = t.cast h' := by
  intros l t;
  induction t with
  | bd_var k => simp [BoundedPreterm.cast]
  | bd_func f => rfl
  | bd_app t s iht ihs => simp [BoundedPreterm.cast, iht, ihs]

@[simp]
lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (t : BoundedPreterm L n l), t.cast h = t := by
  intros l t;
  induction t with
  | bd_var k => simp [BoundedPreterm.cast]
  | bd_func => rfl
  | bd_app _ _ iht ihs => simp [BoundedPreterm.cast, iht, ihs]

/-- Flypitch construction `cast_eq`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def castEq {n m l} (h : n = m) (t : BoundedPreterm L n l) :
    BoundedPreterm L m l :=
  t.cast (Nat.le_of_eq h)

/-- Flypitch construction `cast1`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def cast1 {n l} (t : BoundedPreterm L n l) : BoundedPreterm L (n + 1) l :=
  t.cast (Nat.le_add_right n 1)

@[simp]
lemma cast_fst {n m} (h : n ≤ m) :
    ∀ {l} (t : BoundedPreterm L n l), (t.cast h).fst = t.fst
  | _, bd_var k => rfl
  | _, bd_func f => rfl
  | _, bd_app t s => by simp [BoundedPreterm.cast, cast_fst h t, cast_fst h s]

@[simp]
lemma cast_eq_fst {n m l} (h : n = m) (t : BoundedPreterm L n l) :
    (t.castEq h).fst = t.fst :=
  cast_fst _ t

@[simp]
lemma cast1_fst {n l} (t : BoundedPreterm L n l) : t.cast1.fst = t.fst :=
  cast_fst _ t

@[simp]
lemma cast_eq_rfl {n m l} (h : n = m) (t : BoundedPreterm L n l) :
    (t.castEq h).castEq h.symm = t := by apply BoundedPreterm.eq; simp [cast_eq_fst]

@[simp]
lemma cast_eq_irrel {n m l} (h h' : n = m) (t : BoundedPreterm L n l) :
    t.castEq h = t.castEq h' :=
  rfl

@[simp]
lemma cast_eq_bd_app {n m} (h : n = m) {l} {t : BoundedPreterm L n (l + 1)}
    {s : BoundedPreterm L n 0} :
    (bd_app t s).castEq h = bd_app (t.castEq h) (s.castEq h) :=
  rfl

@[simp]
lemma cast_eq_bd_apps {n m} (h : n = m) {l} {t : BoundedPreterm L n l}
    {ts : DVec (boundedTerm L n) l} :
    (bdApps t ts).castEq h = bdApps (t.castEq h) (ts.map (fun x => x.castEq h)) := by
  simp [BoundedPreterm.castEq, cast_bd_apps]

end BoundedPreterm

namespace closedPreterm

/-- Flypitch construction `cast0`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
protected def cast0 (n : ℕ) {l} (t : closedPreterm L l) : BoundedPreterm L n l :=
  t.cast (Nat.zero_le n)

lemma cast0_fst {n l : ℕ} (t : closedPreterm L l) : (t.cast0 n).fst = t.fst :=
  BoundedPreterm.cast_fst _ t

@[simp]
lemma cast_of_cast0 {n} {l} {t : closedPreterm L l} :
    t.cast0 n = t.cast (Nat.zero_le n) :=
  rfl

end closedPreterm

/-! ### bounded_term.rec — custom recursion principle -/


/-- Custom recursion principle for bounded terms, analogous to
`term.rec`. -/
@[expose]
def boundedTerm.rec {n} {C : boundedTerm L n → Sort v}
    (hvar : ∀ (k : Fin n), C (bd_var k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (boundedTerm L n) l)
        (_ih_ts : ∀ t, DVec.pmem t ts → C t), C (bdApps (bd_func f) ts)) :
    ∀ (t : boundedTerm L n), C t :=
  let rec /-- Structural recursion accumulator. -/ go :
    ∀ {l} (t : BoundedPreterm L n l) (ts : DVec (boundedTerm L n) l)
      (ih_ts : ∀ s, DVec.pmem s ts → C s), C (bdApps t ts)
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
def boundedTerm.rec1 {n} {C : boundedTerm L (n + 1) → Sort v}
    (hvar : ∀ (k : Fin (n + 1)), C (bd_var k))
    (hfunc : ∀ {l} (f : L.functions l) (ts : DVec (boundedTerm L (n + 1)) l)
        (_ih_ts : ∀ t, DVec.pmem t ts → C t), C (bdApps (bd_func f) ts)) :
    ∀ (t : boundedTerm L (n + 1)), C t :=
  boundedTerm.rec hvar hfunc

/-! ### Lift and substitution — irrel lemmas -/


lemma lift_bounded_term_irrel {n : ℕ} :
    ∀ {l} (t : BoundedPreterm L n l) (n') {m : ℕ} (_h : n ≤ m), (t.fst ↑' n' # m) = t.fst
  | _, bd_var k, n', m, h =>
    have h' : ¬(m ≤ k.1) := Nat.not_le.mpr (Nat.lt_of_lt_of_le k.2 h)
    by simp [h']
  | _, bd_func _, _, _, _ => rfl
  | _, bd_app t s, n', m, h => by
    simp [lift_bounded_term_irrel t n' h, lift_bounded_term_irrel s n' h]

lemma subst_bounded_term_irrel {n : ℕ} :
    ∀ {l} (t : BoundedPreterm L n l) {n'} (s : term L) (_h : n ≤ n'),
      substTerm t.fst s n' = t.fst
  | _, bd_var k, n', s, h => by simp [Nat.lt_of_lt_of_le k.2 h]
  | _, bd_func _, _, _, _ => rfl
  | _, bd_app t₁ t₂, n', s, h => by
    simp [subst_bounded_term_irrel t₁ s h, subst_bounded_term_irrel t₂ s h]

/-! ### realize_bounded_term -/


/-- Realize a bounded preterm given a valuation vector `v : DVec
S n` and extra args `xs : DVec S l`. -/
@[simp, expose]
def realizeBoundedTerm {S : Structure L} {n} (v : DVec S n) :
    ∀ {l} (_t : BoundedPreterm L n l) (_xs : DVec S l), S.carrier
  | _, bd_var k, _ => v.nth k.1 k.2
  | _, bd_func f, xs => S.funMap f xs
  | _, bd_app t₁ t₂, xs =>
    realizeBoundedTerm v t₁ (DVec.cons (realizeBoundedTerm v t₂ DVec.nil) xs)

/-- Notation for realizing a bounded term with an empty extra
argument list. -/
notation:0 S "[" t ";;;" v "]" => @realizeBoundedTerm _ S _ v 0 t DVec.nil

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:0 S "[" t ";;;" v ";;;" xs "]" => @realizeBoundedTerm _ S _ v _ t xs

/-- Flypitch construction `realize_closed_term`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def realizeClosedTerm (S : Structure L) (t : closedTerm L) : S.carrier :=
  realizeBoundedTerm DVec.nil t DVec.nil

lemma realize_bounded_term_eq {S : Structure L} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) :
    ∀ {l} (t : BoundedPreterm L n l) (xs : DVec S l),
      realizeBoundedTerm v₁ t xs = realizeTerm v₂ t.fst xs
  | _, bd_var k, _ => hv k.1 k.2
  | _, bd_func f, xs => rfl
  | _, bd_app t₁ t₂, xs =>
    by
    simp only [realizeBoundedTerm, BoundedPreterm.fst, realizeTerm]
    rw [realize_bounded_term_eq hv t₂ DVec.nil, realize_bounded_term_eq hv t₁]

lemma realize_bounded_term_irrel' {S : Structure L} {n n'} {v₁ : DVec S n}
    {v₂ : DVec S n'} (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn') {l}
    (t : BoundedPreterm L n l) (t' : BoundedPreterm L n' l) (ht : t.fst = t'.fst)
    (xs : DVec S l) : realizeBoundedTerm v₁ t xs = realizeBoundedTerm v₂ t' xs := by
  induction t generalizing n' with
  | bd_var k =>
    cases t' with
    | bd_var k' =>
      simp only [BoundedPreterm.fst, preterm.var.injEq] at ht
      simp only [realizeBoundedTerm]
      have hk : k.1 = k'.1 := ht
      calc
        v₁.nth k.1 k.2 = v₂.nth k.1 (hk ▸ k'.2) := h k.1 k.2 (hk ▸ k'.2)
        _ = v₂.nth k'.1 k'.2 := by congr 1
    | bd_func => simp [BoundedPreterm.fst] at ht
    | bd_app => simp [BoundedPreterm.fst] at ht
  | bd_func f =>
    cases t' with
    | bd_var => simp [BoundedPreterm.fst] at ht
    | bd_func f' =>
      simp only [BoundedPreterm.fst, preterm.func.injEq] at ht
      simp [realizeBoundedTerm, ht]
    | bd_app => simp [BoundedPreterm.fst] at ht
  | bd_app t₁ t₂ iht ihs =>
    cases t' with
    | bd_var => simp [BoundedPreterm.fst] at ht
    | bd_func => simp [BoundedPreterm.fst] at ht
    | bd_app t₁'
      t₂' =>
      simp only [BoundedPreterm.fst, preterm.app.injEq] at ht
      simp only [realizeBoundedTerm]
      rw [ihs h t₂' ht.2 DVec.nil, iht h t₁' ht.1]

lemma realize_bounded_term_irrel {S : Structure L} {n} {v₁ : DVec S n}
    (t : boundedTerm L n) (t' : closedTerm L) (ht : t.fst = t'.fst) :
    realizeBoundedTerm v₁ t DVec.nil = realizeClosedTerm S t' :=
  realize_bounded_term_irrel' (fun m _hm hm' => absurd hm' (Nat.not_lt_zero m)) t t' ht
    DVec.nil

@[simp]
lemma realize_bounded_term_cast_eq_irrel {S : Structure L} {n m l} {h : n = m}
    {v : DVec S m} {t : BoundedPreterm L n l} (xs : DVec S l) :
    realizeBoundedTerm v (t.castEq h) xs = realizeBoundedTerm (v.cast h.symm) t xs :=
  by
  subst h
  simp only [BoundedPreterm.castEq, BoundedPreterm.cast_rfl, DVec.cast, ]

@[simp]
lemma realize_bounded_term_dvector_cast_irrel {S : Structure L} {n m l} {h : n = m}
    {v : DVec S n} {t : BoundedPreterm L n l} {xs : DVec S l} :
    realizeBoundedTerm (v.cast h) (t.cast (Nat.le_of_eq h)) xs =
      realizeBoundedTerm v t xs :=
  by
  subst h
  simp only [BoundedPreterm.cast_rfl, DVec.cast]

/-! ### lift_bounded_term_at — lifting bounded terms -/


/-- Lift a bounded term by inserting `n'` new variables at
position `m`. -/
@[simp, expose]
def liftBoundedTermAt {n} :
    ∀ {l} (_t : BoundedPreterm L n l) (n' _m : ℕ), BoundedPreterm L (n + n') l
  | _, bd_var k, n', m =>
    if m ≤ k.1 then bd_var ⟨k.1 + n', by omega⟩ else bd_var ⟨k.1, by omega⟩
  | _, bd_func f, _, _ => bd_func f
  | _, bd_app t₁ t₂, n', m =>
    bd_app (liftBoundedTermAt t₁ n' m) (liftBoundedTermAt t₂ n' m)

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:90 t " ↑ᵇ' " n " # " m => Fol.liftBoundedTermAt t n m

/-- Flypitch construction `lift_bounded_term`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def liftBoundedTerm {n l} (t : BoundedPreterm L n l) (n' : ℕ) :
    BoundedPreterm L (n + n') l :=
  liftBoundedTermAt t n' 0

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
infixl:100 " ↑ᵇ " => Fol.liftBoundedTerm

/-- Flypitch construction `lift_bounded_term1`, retained by the first-order soundness and
completeness development.
-/
@[reducible, simp, expose]
def liftBoundedTerm1 {n' l} (t : BoundedPreterm L n' l) :
    BoundedPreterm L (n' + 1) l :=
  t ↑ᵇ 1

@[simp]
lemma lift_bounded_term_fst {n} :
    ∀ {l} (t : BoundedPreterm L n l) (n' m : ℕ),
      (liftBoundedTermAt t n' m).fst = t.fst ↑' n' # m
  | _, bd_var k, n', m =>
    by
    simp only [liftBoundedTermAt, BoundedPreterm.fst, liftTermAt]
    split_ifs with h <;> simp []
  | _, bd_func _, _, _ => rfl
  | _, bd_app t₁ t₂, n', m => by
    simp [lift_bounded_term_fst t₁ n' m, lift_bounded_term_fst t₂ n' m]

/-! ### subst_bounded_term — substitution in bounded terms -/


/-- Substitute the variable at position `n` (within the bound `n
+ n' + 1`) with a bounded term `s`. -/
@[expose]
def substBoundedTerm {n n'} :
    ∀ {l} (_t : BoundedPreterm L (n + n' + 1) l) (_s : boundedTerm L n'),
      BoundedPreterm L (n + n') l
  | _, bd_var k, s =>
    if h : k.1 < n then bd_var ⟨k.1, Nat.lt_of_lt_of_le h (Nat.le_add_right n n')⟩
    else
      if h' : n < k.1 then bd_var ⟨k.1 - 1, by omega⟩
      else (s ↑ᵇ n).cast (Nat.le_of_eq (Nat.add_comm n' n))
  | _, bd_func f, _ => bd_func f
  | _, bd_app t₁ t₂, s => bd_app (substBoundedTerm t₁ s) (substBoundedTerm t₂ s)

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:0 t "[" s " /// " n "]" => @substBoundedTerm _ n _ _ t s

lemma subst_bounded_term_var_lt {n n'} (s : boundedTerm L n') (k : Fin (n + n' + 1))
    (h : k.1 < n) : (substBoundedTerm (bd_var k) s).fst = &k.1 := by
  simp [substBoundedTerm, h]

lemma subst_bounded_term_var_gt {n n'} (s : boundedTerm L n') (k : Fin (n + n' + 1))
    (h : n < k.1) : (substBoundedTerm (bd_var k) s).fst = &(k.1 - 1) :=
  by
  have h' : ¬(k.1 < n) := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [substBoundedTerm, h', h]

lemma subst_bounded_term_var_eq {n n'} (s : boundedTerm L n') (k : Fin (n + n' + 1))
    (h : k.1 = n) : (substBoundedTerm (bd_var k) s).fst = s.fst ↑' n # 0 :=
  by
  have h₂ : ¬(k.1 < n) := by omega
  have h₃ : ¬(n < k.1) := by omega
  simp only [substBoundedTerm, h₂, h₃, dite_false, BoundedPreterm.cast_fst,
    liftBoundedTerm, lift_bounded_term_fst s n 0]

@[simp]
lemma subst_bounded_term_bd_app {n n' l} (t₁ : BoundedPreterm L (n + n' + 1) (l + 1))
    (t₂ : boundedTerm L (n + n' + 1)) (s : boundedTerm L n') :
    substBoundedTerm (bd_app t₁ t₂) s =
      bd_app (substBoundedTerm t₁ s) (substBoundedTerm t₂ s) :=
  rfl

@[simp]
lemma subst_bounded_term_fst {n n'} :
    ∀ {l} (t : BoundedPreterm L (n + n' + 1) l) (s : boundedTerm L n'),
      (substBoundedTerm t s).fst = substTerm t.fst s.fst n
  | _, bd_var k, s => by
    rcases Nat.lt_trichotomy k.1 n with h | h | h
    · simp [h, substBoundedTerm]
    · simp only [substBoundedTerm, show ¬(k.1 < n) from by omega,
        show ¬(n < k.1) from by omega, dite_false, BoundedPreterm.cast_fst,
        liftBoundedTerm, lift_bounded_term_fst s n 0]
      simp [h]
    · simp [substBoundedTerm, h, Nat.not_lt.mpr (Nat.le_of_lt h), ]
  | _, bd_func f, _ => rfl
  | _, bd_app t₁ t₂, s => by
    simp only [substBoundedTerm, BoundedPreterm.fst, substTerm,
      subst_bounded_term_fst t₁ s, subst_bounded_term_fst t₂ s]

/-- Substitute the last (max) variable with a closed term. -/
@[expose]
def subst0BoundedTerm {n l} (t : BoundedPreterm L (n + 1) l) (s : boundedTerm L n) :
    BoundedPreterm L n l :=
  (substBoundedTerm (t.castEq (n + 1).zero_add.symm) s).castEq n.zero_add

@[simp]
lemma subst0_bounded_term_fst {n l} (t : BoundedPreterm L (n + 1) l)
    (s : boundedTerm L n) : (subst0BoundedTerm t s).fst = substTerm t.fst s.fst 0 :=
  by simp [subst0BoundedTerm, subst_bounded_term_fst]

/-- Substitute the last (max) variable with a closed term. -/
@[expose]
def substmaxBoundedTerm {n l} (t : BoundedPreterm L (n + 1) l) (s : closedTerm L) :
    BoundedPreterm L n l :=
  substBoundedTerm t s

@[simp]
lemma substmax_bounded_term_bd_app {n l} (t₁ : BoundedPreterm L (n + 1) (l + 1))
    (t₂ : boundedTerm L (n + 1)) (s : closedTerm L) :
    substmaxBoundedTerm (bd_app t₁ t₂) s =
      bd_app (substmaxBoundedTerm t₁ s) (substmaxBoundedTerm t₂ s) :=
  rfl

theorem substmax_eq_subst0_term {l} (t : BoundedPreterm L 1 l) (s : closedTerm L) :
    subst0BoundedTerm t s = substmaxBoundedTerm t s := by
  apply BoundedPreterm.eq;
  simp only [substmaxBoundedTerm, subst0BoundedTerm, BoundedPreterm.cast_eq_fst,
    subst_bounded_term_fst, BoundedPreterm.cast_eq_fst]

theorem substmax_var_lt {n} (k : Fin (n + 1)) (s : closedTerm L) (h : k.1 < n) :
    substmaxBoundedTerm (bd_var k : BoundedPreterm L (n + 1) 0) s = bd_var ⟨k.1, h⟩ :=
  by apply BoundedPreterm.eq; simp [substmaxBoundedTerm, substBoundedTerm, h]

theorem substmax_var_eq {n} (k : Fin (n + 1)) (s : closedTerm L) (h : k.1 = n) :
    substmaxBoundedTerm (bd_var k : BoundedPreterm L (n + 1) 0) s = s.cast0 n :=
  by
  apply BoundedPreterm.eq
  simp only [substmaxBoundedTerm, closedPreterm.cast0, BoundedPreterm.cast_fst]
  simp only [substBoundedTerm, show ¬(k.1 < n) from by omega,
    show ¬(n < k.1) from by omega, dite_false, BoundedPreterm.cast_fst,
    liftBoundedTerm, lift_bounded_term_fst s n 0, BoundedPreterm.cast_fst]
    -- Goal: s.fst ↑' n # 0 = s.fst
      -- s : closed_term L = bounded_preterm L 0 0, so bound is 0 ≤ 0
      -- (lift at position 0)
  exact lift_bounded_term_irrel s n (Nat.zero_le 0)

/-- Flypitch construction `bounded_term_of_function`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def boundedTermOfFunction {l n} (f : L.functions l) :
    Arity' (boundedTerm L n) (boundedTerm L n) l :=
  Arity'.ofDvectorMap (bdApps (bd_func f))

/-! ### realize_bounded_term lemmas -/


@[simp]
lemma realize_bounded_term_bd_app {S : Structure L} {n l}
    (t : BoundedPreterm L n (l + 1)) (s : boundedTerm L n) (xs : DVec S n)
    (xs' : DVec S l) :
    realizeBoundedTerm xs (bd_app t s) xs' =
      realizeBoundedTerm xs t (DVec.cons (realizeBoundedTerm xs s DVec.nil) xs') :=
  rfl

@[simp]
lemma realize_closed_term_bd_apps {S : Structure L} {l} (t : closedPreterm L l)
    (ts : DVec (closedTerm L) l) :
    realizeClosedTerm S (bdApps t ts) =
      realizeBoundedTerm DVec.nil t
        (ts.map (fun t' => realizeBoundedTerm DVec.nil t' DVec.nil)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => exact ih (bd_app t x)

lemma realize_bounded_term_bd_apps {S : Structure L} {n l} (xs : DVec S n)
    (t : BoundedPreterm L n l) (ts : DVec (boundedTerm L n) l) :
    realizeBoundedTerm xs (bdApps t ts) DVec.nil =
      realizeBoundedTerm xs t (ts.map (fun t => realizeBoundedTerm xs t DVec.nil)) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs' ih => exact ih (bd_app t x)

@[simp]
lemma realize_cast_bounded_term {S : Structure L} {n m} {h : n ≤ m} {t : boundedTerm L n}
    {v : DVec S m} :
    realizeBoundedTerm v (t.cast h) DVec.nil =
      realizeBoundedTerm (v.trunc n h) t DVec.nil :=
  by
  revert t
  apply boundedTerm.rec
  · intro k
    simp only [BoundedPreterm.cast, realizeBoundedTerm, DVec.trunc_nth]
  · intro l f ts ih_ts
    simp only [BoundedPreterm.cast_bd_apps, realize_bounded_term_bd_apps]
    apply congrArg
    trans
      DVec.map (fun x => realizeBoundedTerm v (BoundedPreterm.cast h x) DVec.nil) ts
    · exact DVec.map_map _ _ ts
    · apply DVec.map_congr_pmem
      intro x hx
      exact ih_ts x hx

/-- When realizing a closed term, the realizing dvector is
irrelevant. -/
lemma realize_closed_term_v_irrel {S : Structure L} {n} {v : DVec S n}
    {t : boundedTerm L 0} :
    realizeBoundedTerm v (t.cast (Nat.zero_le n)) DVec.nil = realizeClosedTerm S t :=
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
inductive BoundedPreformula (L : Language.{u}) : ℕ → ℕ → Type u
  | bd_falsum : ∀ {n}, BoundedPreformula L n 0
  | bd_equal : ∀ {n} (_t₁ _t₂ : boundedTerm L n), BoundedPreformula L n 0
  | bd_rel : ∀ {n l : ℕ} (_R : L.relations l), BoundedPreformula L n l
  |
  bd_apprel :
    ∀ {n l} (_f : BoundedPreformula L n (l + 1)) (_t : boundedTerm L n),
      BoundedPreformula L n l
  | bd_imp : ∀ {n} (_f₁ _f₂ : BoundedPreformula L n 0), BoundedPreformula L n 0
  | bd_all : ∀ {n} (_f : BoundedPreformula L (n + 1) 0), BoundedPreformula L n 0

export BoundedPreformula (bd_falsum bd_equal bd_rel bd_apprel bd_imp bd_all)

/-- Flypitch construction `bounded_formula`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def boundedFormula (n : ℕ) :=
  BoundedPreformula L n 0
/-- Flypitch construction `presentence`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def presentence (l : ℕ) :=
  BoundedPreformula L 0 l
/-- Flypitch construction `sentence`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
def sentence :=
  presentence L 0

variable {L}

instance nonempty_bounded_formula (n : ℕ) : Nonempty (boundedFormula L n) :=
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

/-- Flypitch construction `bd_not`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def bdNot {n} (f : boundedFormula L n) : boundedFormula L n :=
  bd_imp f bd_falsum

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped prefix:max "∼ᵇ" => Fol.bdNot

/-- Flypitch construction `bd_and`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def bdAnd {n} (f₁ f₂ : boundedFormula L n) : boundedFormula L n :=
  bdNot (bd_imp f₁ (bdNot f₂))

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infixr:69 " ⊓ᵇ " => Fol.bdAnd

/-- Flypitch construction `bd_or`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def bdOr {n} (f₁ f₂ : boundedFormula L n) : boundedFormula L n :=
  bd_imp (bdNot f₁) f₂

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infixr:68 " ⊔ᵇ " => Fol.bdOr

/-- Flypitch construction `bd_biimp`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def bdBiimp {n} (f₁ f₂ : boundedFormula L n) : boundedFormula L n :=
  bdAnd (bd_imp f₁ f₂) (bd_imp f₂ f₁)

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:61 " ⇔ᵇ " => Fol.bdBiimp

/-- Flypitch construction `bd_ex`, retained by the first-order soundness and completeness
development.
-/
@[expose]
def bdEx {n} (f : boundedFormula L (n + 1)) : boundedFormula L n :=
  bdNot (bd_all (bdNot f))

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped prefix:110 "∃ᵇ" => Fol.bdEx

/-! ### bd_apps_rel -/


/-- Flypitch construction `bd_apps_rel`, retained by the first-order soundness and completeness
development.
-/
@[simp, expose]
def bdAppsRel {n} :
    ∀ {l} (_f : BoundedPreformula L n l) (_ts : DVec (boundedTerm L n) l),
      boundedFormula L n
  | _, f, DVec.nil => f
  | _, f, DVec.cons t ts => bdAppsRel (bd_apprel f t) ts

@[simp]
lemma bd_apps_rel_zero {n} (f : boundedFormula L n) (ts : DVec (boundedTerm L n) 0) :
    bdAppsRel f ts = f := by cases ts; rfl

/-! ### namespace bounded_preformula -/


namespace BoundedPreformula

/-- Forget boundedness: map a bounded_preformula to an ordinary
preformula. -/
@[simp, expose]
protected def fst : ∀ {n l}, BoundedPreformula L n l → @preformula L l
  | _, _, bd_falsum => preformula.falsum
  | _, _, bd_equal t₁ t₂ => preformula.equal t₁.fst t₂.fst
  | _, _, bd_rel R => preformula.rel R
  | _, _, bd_apprel f t => preformula.apprel f.fst t.fst
  | _, _, bd_imp f₁ f₂ => preformula.imp f₁.fst f₂.fst
  | _, _, bd_all f => preformula.all f.fst

@[simp]
lemma fst_bd_not {n} {f : boundedFormula L n} : (bdNot f).fst = not' f.fst :=
  rfl

@[simp]
lemma fst_bd_or {n} {f₁ f₂ : boundedFormula L n} :
    (bdOr f₁ f₂).fst = or' f₁.fst f₂.fst :=
  rfl

lemma fst_bd_imp {n} {f₁ f₂ : boundedFormula L n} :
    (bd_imp f₁ f₂).fst = preformula.imp f₁.fst f₂.fst :=
  rfl

@[simp]
lemma fst_bd_and {n} {f₁ f₂ : boundedFormula L n} :
    (bdAnd f₁ f₂).fst = and' f₁.fst f₂.fst :=
  rfl

@[simp]
lemma fst_bd_ex {n} {f : boundedFormula L (n + 1)} : (bdEx f).fst = ex' f.fst :=
  rfl

/-- Equality of bounded_preformulas is determined by their
underlying preformulas. -/
@[ext]
protected theorem eq :
    ∀ {n l} {f₁ f₂ : BoundedPreformula L n l}, f₁.fst = f₂.fst → f₁ = f₂
  | _, _, bd_falsum, bd_falsum, _ => rfl
  | _, _, bd_equal t₁ t₂, bd_equal t₁' t₂', h =>
    by
    simp only [BoundedPreformula.fst, preformula.equal.injEq] at h
    exact congrArg₂ bd_equal (BoundedPreterm.eq h.1) (BoundedPreterm.eq h.2)
  | _, _, bd_rel R, bd_rel R', h =>
    by
    simp only [BoundedPreformula.fst, preformula.rel.injEq] at h
    exact congrArg bd_rel h
  | _, _, bd_apprel f t, bd_apprel f' t', h =>
    by
    simp only [BoundedPreformula.fst, preformula.apprel.injEq] at h
    exact congrArg₂ bd_apprel (BoundedPreformula.eq h.1) (BoundedPreterm.eq h.2)
  | _, _, bd_imp f₁ f₂, bd_imp f₁' f₂', h =>
    by
    simp only [BoundedPreformula.fst, preformula.imp.injEq] at h
    exact congrArg₂ bd_imp (BoundedPreformula.eq h.1) (BoundedPreformula.eq h.2)
  | _, _, bd_all f, bd_all f', h =>
    by
    simp only [BoundedPreformula.fst, preformula.all.injEq] at h
    exact
      congrArg bd_all
        (BoundedPreformula.eq h)
          -- cross-constructor cases: fst is in different constructors
  | _, _, bd_falsum, bd_equal _ _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_falsum, bd_rel _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_falsum, bd_imp _ _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_falsum, bd_all _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_equal _ _, bd_falsum, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_equal _ _, bd_imp _ _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_equal _ _, bd_all _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_rel _, bd_apprel _ _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_apprel _ _, bd_rel _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_imp _ _, bd_falsum, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_imp _ _, bd_equal _ _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_imp _ _, bd_all _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_all _, bd_falsum, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_all _, bd_equal _ _, h => by simp [BoundedPreformula.fst] at h
  | _, _, bd_all _, bd_imp _ _, h => by simp [BoundedPreformula.fst] at h

/-- Cast a bounded_preformula to one with a larger variable
bound. -/
@[simp, expose]
protected def cast {n m} (h : n ≤ m) :
    ∀ {l}, BoundedPreformula L n l → BoundedPreformula L m l
  | _, bd_falsum => bd_falsum
  | _, bd_equal t₁ t₂ => bd_equal (t₁.cast h) (t₂.cast h)
  | _, bd_rel R => bd_rel R
  | _, bd_apprel f t => bd_apprel (f.cast h) (t.cast h)
  | _, bd_imp f₁ f₂ => bd_imp (f₁.cast h) (f₂.cast h)
  | _, bd_all f => bd_all (f.cast (Nat.succ_le_succ h))

@[simp]
lemma cast_irrel :
    ∀ {n m l} (h h' : n ≤ m) (f : BoundedPreformula L n l), f.cast h = f.cast h' := by
  intros; rfl

@[simp]
lemma cast_rfl {n} {h : n ≤ n} : ∀ {l} (f : BoundedPreformula L n l), f.cast h = f
  | _, bd_falsum => rfl
  | _, bd_equal t₁ t₂ => by
    simp only [BoundedPreformula.cast, BoundedPreterm.cast_rfl t₁,
      BoundedPreterm.cast_rfl t₂]
  | _, bd_rel _ => rfl
  | _, bd_apprel f t => by
    simp only [BoundedPreformula.cast, cast_rfl f, BoundedPreterm.cast_rfl t]
  | _, bd_imp f₁ f₂ => by simp [BoundedPreformula.cast, cast_rfl f₁, cast_rfl f₂]
  | _, bd_all f => by simp [BoundedPreformula.cast, cast_rfl f]

/-- Flypitch construction `cast_eq`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def castEq {n m l} (h : n = m) (f : BoundedPreformula L n l) :
    BoundedPreformula L m l :=
  f.cast (Nat.le_of_eq h)

/-- Flypitch construction `cast_eqr`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def castEqr {n m l} (h : n = m) (f : BoundedPreformula L m l) :
    BoundedPreformula L n l :=
  f.cast (Nat.le_of_eq h.symm)

lemma cast_bd_apps_rel {n m} (h : n ≤ m) :
    ∀ {l} (f : BoundedPreformula L n l) (ts : DVec (boundedTerm L n) l),
      (bdAppsRel f ts).cast h = bdAppsRel (f.cast h) (ts.map (fun t => t.cast h))
  | _, f, DVec.nil => rfl
  | _, f, DVec.cons x xs => by
    simp only [bdAppsRel, DVec.map]
    exact cast_bd_apps_rel h (bd_apprel f x) xs

/-- Flypitch construction `cast1`, retained by the first-order soundness and completeness
development.
-/
@[expose]
protected def cast1 {n l} (f : BoundedPreformula L n l) :
    BoundedPreformula L (n + 1) l :=
  f.cast (Nat.le_add_right n 1)

@[simp]
lemma cast_fst :
    ∀ {l n m} (h : n ≤ m) (f : BoundedPreformula L n l), (f.cast h).fst = f.fst
  | _, _, _, _, bd_falsum => rfl
  | _, _, _, h, bd_equal t₁ t₂ => by
    simp only [BoundedPreformula.cast, BoundedPreformula.fst,
      BoundedPreterm.cast_fst h t₁, BoundedPreterm.cast_fst h t₂]
  | _, _, _, _, bd_rel _ => rfl
  | _, _, _, h, bd_apprel f t => by
    simp only [BoundedPreformula.cast, BoundedPreformula.fst, cast_fst h f,
      BoundedPreterm.cast_fst h t]
  | _, _, _, h, bd_imp f₁ f₂ => by
    simp [BoundedPreformula.cast, cast_fst h f₁, cast_fst h f₂]
  | _, _, _, h, bd_all f => by
    simp [BoundedPreformula.cast, cast_fst (Nat.succ_le_succ h) f]

@[simp]
lemma cast_eq_fst {l n m} (h : n = m) (f : BoundedPreformula L n l) :
    (f.castEq h).fst = f.fst :=
  cast_fst _ f

@[simp]
lemma cast1_fst {l n} (f : BoundedPreformula L n l) : f.cast1.fst = f.fst :=
  cast_fst _ f

@[simp]
lemma cast_eq_rfl {l n m} (h : n = m) (f : BoundedPreformula L n l) :
    (f.castEq h).castEq h.symm = f := by apply BoundedPreformula.eq; simp [cast_eq_fst]

@[simp]
lemma cast_eq_irrel {l n m} (h h' : n = m) (f : BoundedPreformula L n l) :
    f.castEq h = f.castEq h' :=
  rfl

@[simp]
lemma cast_eq_all {n m} (h : n = m) {f : BoundedPreformula L (n + 1) 0} :
    (bd_all f).castEq h = bd_all (f.castEq (congrArg (· + 1) h)) :=
  rfl

@[simp]
lemma cast_eq_trans {n m o l} {h : n = m} {h' : m = o} {f : BoundedPreformula L n l} :
    (f.castEq h).castEq h' = f.castEq (h.trans h') := by
  apply BoundedPreformula.eq;
  simp [cast_eq_fst]

lemma cast_eq_hrfl {n m l} {h : n = m} {f : BoundedPreformula L n l} :
    HEq (f.castEq h) f := by
  -- TODO: port from src/fol.lean:1801-1802 (cast_eq_hrfl,
    -- heterogeneous equality)
  subst h
  apply heq_of_eq
  apply BoundedPreformula.eq; simp [BoundedPreformula.cast_eq_fst]

/-- A bounded_preformula is quantifier-free if its underlying
preformula is. -/
@[expose]
def quantifierFree {l n} (f : BoundedPreformula L n l) : Prop :=
  Fol.quantifierFree f.fst

end BoundedPreformula

/-! ### namespace presentence -/


namespace presentence

/-- Flypitch construction `cast0`, retained by the first-order soundness and completeness
development.
-/
@[reducible, expose]
protected def cast0 {l} (n : ℕ) (f : presentence L l) : BoundedPreformula L n l :=
  f.cast (Nat.zero_le n)

lemma cast0_fst {l} (n : ℕ) (f : presentence L l) : (f.cast0 n).fst = f.fst :=
  BoundedPreformula.cast_fst _ f

end presentence

/-! ### Irrel lemmas for bounded formulas -/


lemma lift_bounded_formula_irrel :
    ∀ {n l} (f : BoundedPreformula L n l) (n') {m : ℕ} (_h : n ≤ m),
      liftFormulaAt f.fst n' m = f.fst
  | _, _, bd_falsum, _, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', m, h => by
    simp [BoundedPreformula.fst, lift_bounded_term_irrel t₁ n' h,
      lift_bounded_term_irrel t₂ n' h]
  | _, _, bd_rel _, _, _, _ => rfl
  | _, _, bd_apprel f t, n', m, h => by
    simp [BoundedPreformula.fst, lift_bounded_formula_irrel f n' h,
      lift_bounded_term_irrel t n' h]
  | _, _, bd_imp f₁ f₂, n', m, h => by
    simp [BoundedPreformula.fst, lift_bounded_formula_irrel f₁ n' h,
      lift_bounded_formula_irrel f₂ n' h]
  | _, _, bd_all f, n', m, h =>
    by
    simp only [BoundedPreformula.fst, liftFormulaAt, preformula.all.injEq]
    exact lift_bounded_formula_irrel f n' (Nat.succ_le_succ h)

lemma lift_sentence_irrel (f : sentence L) : liftFormula f.fst 1 = f.fst :=
  lift_bounded_formula_irrel f 1 (Nat.le_refl 0)

@[simp]
lemma subst_bounded_formula_irrel :
    ∀ {n l} (f : BoundedPreformula L n l) {n'} (s : term L) (_h : n ≤ n'),
      substFormula f.fst s n' = f.fst
  | _, _, bd_falsum, _, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', s, h => by
    simp [BoundedPreformula.fst, subst_bounded_term_irrel t₁ s h,
      subst_bounded_term_irrel t₂ s h]
  | _, _, bd_rel _, _, _, _ => rfl
  | _, _, bd_apprel f t, n', s, h => by
    simp [BoundedPreformula.fst, subst_bounded_formula_irrel f s h,
      subst_bounded_term_irrel t s h]
  | _, _, bd_imp f₁ f₂, n', s, h => by
    simp [BoundedPreformula.fst, subst_bounded_formula_irrel f₁ s h,
      subst_bounded_formula_irrel f₂ s h]
  | _, _, bd_all f, n', s, h =>
    by
    simp only [BoundedPreformula.fst, substFormula, preformula.all.injEq]
    exact subst_bounded_formula_irrel f s (Nat.succ_le_succ h)

lemma subst_sentence_irrel (f : sentence L) (n : ℕ) (s : term L) :
    substFormula f.fst s n = f.fst :=
  subst_bounded_formula_irrel f s (Nat.zero_le n)

/-! ### realize_bounded_formula -/


/-- Flypitch construction `realize_bounded_formula`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def realizeBoundedFormula {S : Structure L} :
    ∀ {n l} (_v : DVec S n) (_f : BoundedPreformula L n l) (_xs : DVec S l), Prop
  | _, _, _v, bd_falsum, _ => False
  | _, _, v, bd_equal t₁ t₂, _ =>
    realizeBoundedTerm v t₁ DVec.nil = realizeBoundedTerm v t₂ DVec.nil
  | _, _, _, bd_rel R, xs => S.relMap R xs
  | _, _, v, bd_apprel f t, xs =>
    realizeBoundedFormula v f (DVec.cons (realizeBoundedTerm v t DVec.nil) xs)
  | _, _, v, bd_imp f₁ f₂, xs =>
    realizeBoundedFormula v f₁ xs → realizeBoundedFormula v f₂ xs
  | _, _, v, bd_all f, xs => ∀ x : S, realizeBoundedFormula (DVec.cons x v) f xs

/-- Flypitch construction `realize_sentence`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def realizeSentence (S : Structure L) (f : sentence L) : Prop :=
  realizeBoundedFormula (DVec.nil : DVec S 0) f DVec.nil

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped infix:51 " ⊨ₘ " => Fol.realizeSentence

/-! ### realize_bounded_formula lemmas -/
-- Helper for realize_bounded_formula_iff: structural recursion
-- over f


-- Helper for realize_bounded_formula_iff: structural recursion
-- over f
theorem realize_bounded_formula_iff_aux {S : Structure L} :
    ∀ {n l} (f : BoundedPreformula L n l) (v₁ : DVec S n) (v₂ : ℕ → S)
      (_hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) (xs : DVec S l),
      realizeBoundedFormula v₁ f xs ↔ realizeFormula v₂ f.fst xs
  | _, _, bd_falsum, _, _, _, _ => Iff.rfl
  | _, _, bd_equal t₁ t₂, v₁, v₂, hv, _ => by
    simp [realizeBoundedFormula, BoundedPreformula.fst, realizeFormula,
      realize_bounded_term_eq hv t₁ DVec.nil, realize_bounded_term_eq hv t₂ DVec.nil]
  | _, _, bd_rel _, _, _, _, _ => Iff.rfl
  | _, _, bd_apprel f t, v₁, v₂, hv, xs =>
    by
    simp only [realizeBoundedFormula, BoundedPreformula.fst, realizeFormula,
      realize_bounded_term_eq hv t DVec.nil]
    exact realize_bounded_formula_iff_aux f v₁ v₂ hv _
  | _, _, bd_imp f₁ f₂, v₁, v₂, hv, xs =>
    by
    simp only [realizeBoundedFormula, BoundedPreformula.fst, realizeFormula]
    exact
      Iff.imp (realize_bounded_formula_iff_aux f₁ v₁ v₂ hv xs)
        (realize_bounded_formula_iff_aux f₂ v₁ v₂ hv xs)
  | n, _, bd_all f, v₁, v₂, hv, _ =>
    by
    simp only [realizeBoundedFormula, BoundedPreformula.fst, realizeFormula]
    apply forall_congr'
    intro x
    have hv' : ∀ k (hk : k < n + 1), (DVec.cons x v₁).nth k hk = substRealize v₂ x 0 k :=
      by
      intro k hk
      cases k with
      | zero => simp [DVec.nth, substRealize]
      | succ k =>
        have hk' : k < n := Nat.lt_of_succ_lt_succ hk
        simp only [DVec.nth, substRealize, Nat.zero_lt_succ, ↓reduceIte,
          Nat.add_sub_cancel]
        exact hv k hk'
    simp only [DVec.zero_eq]
    exact
      realize_bounded_formula_iff_aux f (DVec.cons x v₁) (substRealize v₂ x 0) hv'
        DVec.nil

lemma realize_bounded_formula_iff {S : Structure L} {n} {v₁ : DVec S n} {v₂ : ℕ → S}
    (hv : ∀ k (hk : k < n), v₁.nth k hk = v₂ k) {l} (f : BoundedPreformula L n l)
    (xs : DVec S l) : realizeBoundedFormula v₁ f xs ↔ realizeFormula v₂ f.fst xs :=
  realize_bounded_formula_iff_aux f v₁ v₂ hv xs

lemma realize_bounded_formula_iff_of_fst {S : Structure L} {n} {v₁ w₁ : DVec S n}
    {v₂ w₂ : ℕ → S} (hv₁ : ∀ k (hk : k < n), v₁.nth k hk = v₂ k)
    (hw₁ : ∀ k (hk : k < n), w₁.nth k hk = w₂ k) {l₁ l₂} (t₁ : BoundedPreformula L n l₁)
    (t₂ : BoundedPreformula L n l₂) (xs₁ : DVec S l₁) (xs₂ : DVec S l₂)
    (H : realizeFormula v₂ t₁.fst xs₁ ↔ realizeFormula w₂ t₂.fst xs₂) :
    (realizeBoundedFormula v₁ t₁ xs₁ ↔ realizeBoundedFormula w₁ t₂ xs₂) :=
  by
  rw [realize_bounded_formula_iff hv₁, realize_bounded_formula_iff hw₁]
  exact H

lemma realize_bounded_formula_irrel' {S : Structure L} {n n'} {v₁ : DVec S n}
    {v₂ : DVec S n'} (h : ∀ m (hn : m < n) (hn' : m < n'), v₁.nth m hn = v₂.nth m hn') {l}
    (f : BoundedPreformula L n l) (f' : BoundedPreformula L n' l) (hf : f.fst = f'.fst)
    (xs : DVec S l) :
    realizeBoundedFormula v₁ f xs ↔ realizeBoundedFormula v₂ f' xs := by
  induction f generalizing n' with
  | bd_falsum =>
    cases f' with
    | bd_falsum => exact Iff.rfl
    | _ => simp [BoundedPreformula.fst] at hf
  | bd_equal t₁ t₂ =>
    cases f' with
    | bd_equal t₁'
      t₂' =>
      simp only [BoundedPreformula.fst, preformula.equal.injEq] at hf
      simp [realizeBoundedFormula, realize_bounded_term_irrel' h t₁ t₁' hf.1,
        realize_bounded_term_irrel' h t₂ t₂' hf.2]
    | _ => simp [BoundedPreformula.fst] at hf
  | bd_rel =>
    cases f' with
    | bd_rel =>
      simp only [BoundedPreformula.fst, preformula.rel.injEq] at hf; subst hf;
      exact Iff.rfl
    | _ => simp [BoundedPreformula.fst] at hf
  | bd_apprel f t ih =>
    cases f' with
    | bd_apprel f'
      t' =>
      simp only [BoundedPreformula.fst, preformula.apprel.injEq] at hf
      simp only [realizeBoundedFormula]
      rw [realize_bounded_term_irrel' h t t' hf.2 DVec.nil]
      exact ih h f' hf.1 _
    | _ => simp [BoundedPreformula.fst] at hf
  | bd_imp f₁ f₂ ih₁ ih₂ =>
    cases f' with
    | bd_imp f₁'
      f₂' =>
      simp only [BoundedPreformula.fst, preformula.imp.injEq] at hf
      simp only [realizeBoundedFormula]
      exact Iff.imp (ih₁ h f₁' hf.1 xs) (ih₂ h f₂' hf.2 xs)
    | _ => simp [BoundedPreformula.fst] at hf
  | bd_all f ih =>
    cases f' with
    | bd_all
      f' =>
      simp only [BoundedPreformula.fst, preformula.all.injEq] at hf
      simp only [realizeBoundedFormula]
      apply forall_congr'
      intro x
      apply ih
      · intro m hm hm'
        cases m with
        | zero => simp [DVec.nth]
        | succ m => exact h m (Nat.lt_of_succ_lt_succ hm) (Nat.lt_of_succ_lt_succ hm')
      · exact hf
    | _ => simp [BoundedPreformula.fst] at hf

lemma realize_bounded_formula_irrel {S : Structure L} {n} {v₁ : DVec S n}
    (f : boundedFormula L n) (f' : sentence L) (hf : f.fst = f'.fst) (xs : DVec S 0) :
    realizeBoundedFormula v₁ f xs ↔ realizeSentence S f' :=
  by
  cases xs
  apply realize_bounded_formula_irrel'
  · intro m _hm hm'
    exact absurd hm' (Nat.not_lt_zero m)
  · exact hf

@[simp]
lemma realize_bounded_formula_cast_eq_irrel {S : Structure L} {n m l} {h : n = m}
    {v : DVec S m} {f : BoundedPreformula L n l} {xs : DVec S l} :
    realizeBoundedFormula v (f.castEq h) xs =
      realizeBoundedFormula (v.cast h.symm) f xs :=
  by subst h; simp [BoundedPreformula.castEq, BoundedPreformula.cast_rfl, DVec.cast]

/-! ### bounded_formula_of_relation -/


/-- Flypitch construction `bounded_formula_of_relation`, retained by the first-order soundness
and completeness development.
-/
@[expose]
def boundedFormulaOfRelation {l n} (R : L.relations l) :
    Arity' (boundedTerm L n) (boundedFormula L n) l :=
  Arity'.ofDvectorMap (bdAppsRel (bd_rel R))

/-! ### Recursors for bounded_preformula / bounded_formula
(src/fol.lean lines 1984-2038) -/


/-- Recursor for bounded_preformula at n+1 (i.e., where there is
at least one free variable). -/
@[expose]
def BoundedPreformula.rec1 {C : ∀ n l, BoundedPreformula L (n + 1) l → Sort v}
    (H0 : ∀ {n}, C n 0 bd_falsum)
    (H1 : ∀ {n} (t₁ t₂ : boundedTerm L (n + 1)), C n 0 (bd_equal t₁ t₂))
    (H2 : ∀ {n l : ℕ} (R : L.relations l), C n l (bd_rel R))
    (H3 : ∀ {n l : ℕ} (f : BoundedPreformula L (n + 1) (l + 1)) (t : boundedTerm L (n + 1))
        (_ih : C n (l + 1) f), C n l (bd_apprel f t))
    (H4 : ∀ {n} (f₁ f₂ : boundedFormula L (n + 1)) (_ih₁ : C n 0 f₁) (_ih₂ : C n 0 f₂),
        C n 0 (bd_imp f₁ f₂))
    (H5 : ∀ {n} (f : boundedFormula L (n + 2)) (_ih : C (n + 1) 0 f), C n 0 (bd_all f)) :
    ∀ {{n l : ℕ}} (f : BoundedPreformula L (n + 1) l), C n l f :=
  -- Port from src/fol.lean:1984-2004: define C' with n=0 case =
    -- PUnit, then use full rec
  let C' : ∀ n l, BoundedPreformula L n l → Sort v := fun n =>
    match n with
    | 0 => fun _l _f => PUnit
    | k + 1 => C k
  let rec /-- Recursive extension of the positive-arity motive. -/ key :
    ∀ (n l : ℕ) (f : BoundedPreformula L n l), C' n l f
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
def boundedFormula.rec1 {C : ∀ n, boundedFormula L (n + 1) → Sort v}
    (hfalsum : ∀ {n}, C n bd_falsum)
    (hequal : ∀ {n} (t₁ t₂ : boundedTerm L (n + 1)), C n (bd_equal t₁ t₂))
    (hrel : ∀ {n l : ℕ} (R : L.relations l) (ts : DVec (boundedTerm L (n + 1)) l),
        C n (bdAppsRel (bd_rel R) ts))
    (himp : ∀ {n} {f₁ f₂ : boundedFormula L (n + 1)} (_ih₁ : C n f₁) (_ih₂ : C n f₂),
        C n (bd_imp f₁ f₂))
    (hall : ∀ {n} {f : boundedFormula L (n + 2)} (_ih : C (n + 1) f), C n (bd_all f))
    {{n : ℕ}} (f : boundedFormula L (n + 1)) : C n f :=
  -- Use a helper that handles partially-applied formulas via dvec
    -- accumulator
  let rec /-- Structural recursion accumulator. -/ go :
    ∀ {n' l} (f' : BoundedPreformula L (n' + 1) l)
      (ts : DVec (boundedTerm L (n' + 1)) l), C n' (bdAppsRel f' ts)
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
def boundedFormula.rec {C : ∀ n, boundedFormula L n → Sort v}
    (hfalsum : ∀ {n}, C n bd_falsum)
    (hequal : ∀ {n} (t₁ t₂ : boundedTerm L n), C n (bd_equal t₁ t₂))
    (hrel : ∀ {n l : ℕ} (R : L.relations l) (ts : DVec (boundedTerm L n) l),
        C n (bdAppsRel (bd_rel R) ts))
    (himp : ∀ {n} {f₁ f₂ : boundedFormula L n} (_ih₁ : C n f₁) (_ih₂ : C n f₂),
        C n (bd_imp f₁ f₂))
    (hall : ∀ {n} {f : boundedFormula L (n + 1)} (_ih : C (n + 1) f), C n (bd_all f)) :
    ∀ {{n : ℕ}} (f : boundedFormula L n), C n f :=
  let rec /-- Structural recursion accumulator. -/ go :
    ∀ {n l} (f : BoundedPreformula L n l) (ts : DVec (boundedTerm L n) l),
      C n (bdAppsRel f ts)
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
def substBoundedFormula :
    ∀ {n n' n'' l} (_f : BoundedPreformula L n'' l) (_s : boundedTerm L n')
      (_h : n + n' + 1 = n''), BoundedPreformula L (n + n') l
  | _, _, _, _, bd_falsum, _, _ => bd_falsum
  | _, _, _, _, bd_equal t₁ t₂, s, rfl =>
    bd_equal (substBoundedTerm t₁ s) (substBoundedTerm t₂ s)
  | _, _, _, _, bd_rel R, _, _ => bd_rel R
  | _, _, _, _, bd_apprel f t, s, rfl =>
    bd_apprel (substBoundedFormula f s rfl) (substBoundedTerm t s)
  | _, _, _, _, bd_imp f₁ f₂, s, rfl =>
    bd_imp (substBoundedFormula f₁ s rfl) (substBoundedFormula f₂ s rfl)
  | n, n', _, _, bd_all f, s, rfl =>
    -- f : bounded_preformula L (n + n' + 1 + 1) 0
          -- we call subst with n+1, n', giving h : (n+1)+n'+1 = n+n'+1+1
          -- (proved by omega)
          -- result: bounded_preformula L ((n+1)+n') 0 = bounded_preformula
          -- L (n+n'+1) 0
          -- then cast to n+n'+1 = n+n'+1 which is trivially true
    bd_all
      ((substBoundedFormula f s (by omega : (n + 1) + n' + 1 = n + n' + 1 + 1)).castEq
        (show (n + 1) + n' = n + n' + 1 from by omega))

@[simp]
lemma subst_bounded_formula_fst :
    ∀ {n n' n'' l} (f : BoundedPreformula L n'' l) (s : boundedTerm L n')
      (h : n + n' + 1 = n''),
      (substBoundedFormula f s h).fst = substFormula f.fst s.fst n
  | _, _, _, _, bd_falsum, _, _ => rfl
  | _, _, _, _, bd_equal t₁ t₂, s, rfl => by
    simp only [substBoundedFormula, BoundedPreformula.fst, substFormula,
      subst_bounded_term_fst t₁ s, subst_bounded_term_fst t₂ s]
  | _, _, _, _, bd_rel _, _, _ => rfl
  | _, _, _, _, bd_apprel f t, s, rfl => by
    simp only [substBoundedFormula, BoundedPreformula.fst, substFormula,
      subst_bounded_formula_fst f s rfl, subst_bounded_term_fst t s]
  | _, _, _, _, bd_imp f₁ f₂, s, rfl => by
    simp [substBoundedFormula, subst_bounded_formula_fst f₁ s rfl,
      subst_bounded_formula_fst f₂ s rfl]
  | n, n', _, _, bd_all f, s, rfl =>
    by
    simp only [substBoundedFormula, BoundedPreformula.fst,
      BoundedPreformula.cast_eq_fst]
    rw [subst_bounded_formula_fst f s (by omega : (n + 1) + n' + 1 = n + n' + 1 + 1)]
    simp [substFormula]

/-- Flypitch construction `substmax_bounded_formula`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def substmaxBoundedFormula {n l} (f : BoundedPreformula L (n + 1) l)
    (s : closedTerm L) : BoundedPreformula L n l :=
  substBoundedFormula f s rfl

lemma substmax_bounded_formula_fst {n l} (f : BoundedPreformula L (n + 1) l)
    (s : closedTerm L) :
    (substmaxBoundedFormula f s).fst = substFormula f.fst s.fst n := by
  exact subst_bounded_formula_fst (n := n) f s rfl

lemma substmax_bounded_formula_bd_all {n} (f : boundedFormula L (n + 2))
    (s : closedTerm L) :
    substmaxBoundedFormula (bd_all f) s = bd_all (substmaxBoundedFormula f s) := by
  apply BoundedPreformula.eq; simp

lemma substmax_bounded_formula_bd_apps_rel {n l} (f : BoundedPreformula L (n + 1) l)
    (t : closedTerm L) (ts : DVec (boundedTerm L (n + 1)) l) :
    substmaxBoundedFormula (bdAppsRel f ts) t =
      bdAppsRel (substmaxBoundedFormula f t)
        (ts.map fun t' => substmaxBoundedTerm t' t) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs ih => exact ih (bd_apprel f x)

/-- Flypitch construction `subst0_bounded_formula`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def subst0BoundedFormula {n l} (f : BoundedPreformula L (n + 1) l)
    (s : boundedTerm L n) : BoundedPreformula L n l :=
  -- n + 1 = 0 + n + 1, so we use h : 0 + n + 1 = n + 1
  (substBoundedFormula f s (by omega : 0 + n + 1 = n + 1)).castEq
    (by omega : 0 + n = n)

@[simp]
lemma subst0_bounded_formula_fst {n l} (f : BoundedPreformula L (n + 1) l)
    (s : boundedTerm L n) :
    (subst0BoundedFormula f s).fst = substFormula f.fst s.fst 0 :=
  by
  simp only [subst0BoundedFormula, BoundedPreformula.cast_eq_fst]
  rw [subst_bounded_formula_fst f s (by omega : 0 + n + 1 = n + 1)]

theorem substmax_eq_subst0_formula {l} (f : BoundedPreformula L 1 l)
    (t : closedTerm L) : subst0BoundedFormula f t = substmaxBoundedFormula f t :=
  by
  apply BoundedPreformula.eq
  simp only [subst0BoundedFormula, substmaxBoundedFormula,
    BoundedPreformula.cast_eq_fst, subst_bounded_formula_fst]

/-! ### realize_sentence lemmas -/


lemma realize_sentence_false {S : Structure L} :
    realizeSentence S (bd_falsum : sentence L) ↔ False :=
  Iff.rfl

lemma realize_sentence_imp {S : Structure L} {f₁ f₂ : sentence L} :
    realizeSentence S (bd_imp f₁ f₂) ↔ (realizeSentence S f₁ → realizeSentence S f₂) :=
  Iff.rfl

lemma realize_sentence_not {S : Structure L} {f : sentence L} :
    realizeSentence S (bdNot f) ↔ ¬realizeSentence S f :=
  Iff.rfl

lemma realize_sentence_dne {S : Structure L} {f : sentence L} :
    realizeSentence S (bdNot (bdNot f)) ↔ realizeSentence S f :=
  by
  simp only [realizeSentence, realizeBoundedFormula, bdNot]
  tauto

lemma realize_sentence_all {S : Structure L} {f : boundedFormula L 1} :
    realizeSentence S (bd_all f) ↔
      ∀ x : S, realizeBoundedFormula (DVec.cons x DVec.nil) f DVec.nil :=
  Iff.rfl

@[simp]
lemma realize_bounded_formula_imp {S : Structure L} :
    ∀ {n} {v : DVec S n} {f g : boundedFormula L n},
      realizeBoundedFormula v (bd_imp f g) DVec.nil ↔
        (realizeBoundedFormula v f DVec.nil → realizeBoundedFormula v g DVec.nil) :=
  Iff.rfl

@[simp]
lemma realize_bounded_formula_and {S : Structure L} :
    ∀ {n} {v : DVec S n} {f g : boundedFormula L n},
      realizeBoundedFormula v (bdAnd f g) DVec.nil ↔
        (realizeBoundedFormula v f DVec.nil ∧ realizeBoundedFormula v g DVec.nil) :=
  by
  intros n v f g
  simp only [bdAnd, bdNot, realizeBoundedFormula]
  tauto

@[simp]
lemma realize_bounded_formula_not {S : Structure L} :
    ∀ {n} {v : DVec S n} {f : boundedFormula L n},
      realizeBoundedFormula v (bdNot f) DVec.nil ↔
        ¬(realizeBoundedFormula v f DVec.nil) :=
  Iff.rfl

@[simp]
lemma realize_bounded_formula_ex {S : Structure L} :
    ∀ {n} {v : DVec S n} {f : boundedFormula L (n + 1)},
      realizeBoundedFormula v (bdEx f) DVec.nil ↔
        ∃ x : S, realizeBoundedFormula (DVec.cons x v) f DVec.nil :=
  by
  intros n v f
  simp only [bdEx, bdNot, realizeBoundedFormula]
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

lemma realize_sentence_ex {S : Structure L} {f : boundedFormula L 1} :
    realizeSentence S (bdEx f) ↔
      ∃ x : S, realizeBoundedFormula (DVec.cons x DVec.nil) f DVec.nil :=
  by apply realize_bounded_formula_ex

lemma realize_sentence_and {S : Structure L} {f₁ f₂ : sentence L} :
    realizeSentence S (bdAnd f₁ f₂) ↔ (realizeSentence S f₁ ∧ realizeSentence S f₂) :=
  realize_bounded_formula_and

@[simp]
lemma realize_bounded_formula_biimp {S : Structure L} :
    ∀ {n} {v : DVec S n} {f g : boundedFormula L n},
      realizeBoundedFormula v (bdBiimp f g) DVec.nil ↔
        (realizeBoundedFormula v f DVec.nil ↔ realizeBoundedFormula v g DVec.nil) :=
  by
  intros n v f g
  simp [bdBiimp, realize_bounded_formula_and]
  tauto

lemma realize_sentence_biimp {S : Structure L} {f₁ f₂ : sentence L} :
    realizeSentence S (bdBiimp f₁ f₂) ↔
      (realizeSentence S f₁ ↔ realizeSentence S f₂) :=
  realize_bounded_formula_biimp

lemma realize_bounded_formula_bd_apps_rel {S : Structure L} {n l} (xs : DVec S n)
    (f : BoundedPreformula L n l) (ts : DVec (boundedTerm L n) l) :
    realizeBoundedFormula xs (bdAppsRel f ts) DVec.nil ↔
      realizeBoundedFormula xs f (ts.map fun t => realizeBoundedTerm xs t DVec.nil) :=
  by
  induction ts with
  | nil => rfl
  | cons x xs' ih => exact ih (bd_apprel f x)

@[simp]
lemma realize_cast_bounded_formula {S : Structure L} {n m} {h : n ≤ m}
    {f : boundedFormula L n} {v : DVec S m} :
    realizeBoundedFormula v (f.cast h) DVec.nil =
      realizeBoundedFormula (v.trunc n h) f DVec.nil :=
  by
  -- Case split: n = m or n < m
  by_cases hn : n = m
  · -- n = m: cast is identity, trunc is identity
    subst hn; simp [BoundedPreformula.cast_rfl]
  · -- n < m
    have hnlt : n < m := Nat.lt_of_le_of_ne h hn
    apply propext
    apply realize_bounded_formula_irrel'
    · -- Show v.nth k (hk : k < m) = (v.trunc n h).nth k (hk' : k < n) when k < n
      intro k hkn hkm
      rw [DVec.trunc_nth]
    · -- Show (f.cast h).fst = f.fst
      simp [BoundedPreformula.cast_fst]

lemma realize_sentence_bd_apps_rel' {S : Structure L} {l} (f : presentence L l)
    (ts : DVec (closedTerm L) l) :
    realizeSentence S (bdAppsRel f ts) ↔
      realizeBoundedFormula (DVec.nil : DVec S 0) f (ts.map (realizeClosedTerm S)) :=
  realize_bounded_formula_bd_apps_rel DVec.nil f ts

lemma realize_bd_apps_rel {S : Structure L} {l} (R : L.relations l)
    (ts : DVec (closedTerm L) l) :
    realizeSentence S (bdAppsRel (bd_rel R) ts) ↔
      S.relMap R (ts.map (realizeClosedTerm S)) :=
  realize_bounded_formula_bd_apps_rel DVec.nil (bd_rel R) ts

lemma realize_sentence_equal {S : Structure L} (t₁ t₂ : closedTerm L) :
    realizeSentence S (bd_equal t₁ t₂) ↔
      realizeClosedTerm S t₁ = realizeClosedTerm S t₂ :=
  Iff.rfl

lemma realize_sentence_iff {S : Structure L} (v : ℕ → S) (f : sentence L) :
    realizeSentence S f ↔ realizeFormula v f.fst DVec.nil :=
  by
  apply realize_bounded_formula_iff
  intro k hk
  exact absurd hk (Nat.not_lt_zero k)

/-! ### lift_bounded_formula_at — lift bounded formulas -/


/-- Flypitch construction `lift_bounded_formula_at`, retained by the first-order soundness and
completeness development.
-/
@[simp, expose]
def liftBoundedFormulaAt :
    ∀ {n l} (_f : BoundedPreformula L n l) (n' _m : ℕ), BoundedPreformula L (n + n') l
  | _, _, bd_falsum, _, _ => bd_falsum
  | _, _, bd_equal t₁ t₂, n', m => bd_equal (t₁ ↑ᵇ' n' # m) (t₂ ↑ᵇ' n' # m)
  | _, _, bd_rel R, _, _ => bd_rel R
  | _, _, bd_apprel f t, n', m =>
    bd_apprel (liftBoundedFormulaAt f n' m) (t ↑ᵇ' n' # m)
  | _, _, bd_imp f₁ f₂, n', m =>
    bd_imp (liftBoundedFormulaAt f₁ n' m) (liftBoundedFormulaAt f₂ n' m)
  | n, _, bd_all f, n', m =>
    bd_all ((liftBoundedFormulaAt f n' (m + 1)).castEq (by omega))

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
notation:90 f " ↑ᶠᵇ' " n " # " m => Fol.liftBoundedFormulaAt f n m

/-- Flypitch construction `lift_bounded_formula`, retained by the first-order soundness and
completeness development.
-/
@[reducible, expose]
def liftBoundedFormula {n l} (f : BoundedPreformula L n l) (n' : ℕ) :
    BoundedPreformula L (n + n') l :=
  liftBoundedFormulaAt f n' 0

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
infixl:100 " ↑ᶠᵇ " => Fol.liftBoundedFormula

/-- Flypitch construction `lift_bounded_formula1`, retained by the first-order soundness and
completeness development.
-/
@[reducible, simp, expose]
def liftBoundedFormula1 {n' l} (f : BoundedPreformula L n' l) :
    BoundedPreformula L (n' + 1) l :=
  f ↑ᶠᵇ 1

@[simp]
lemma lift_bounded_formula_fst :
    ∀ {n l} (f : BoundedPreformula L n l) (n' m : ℕ),
      (liftBoundedFormulaAt f n' m).fst = liftFormulaAt f.fst n' m
  | _, _, bd_falsum, _, _ => rfl
  | _, _, bd_equal t₁ t₂, n', m => by
    simp only [liftBoundedFormulaAt, BoundedPreformula.fst, liftFormulaAt,
      lift_bounded_term_fst t₁ n' m, lift_bounded_term_fst t₂ n' m]
  | _, _, bd_rel _, _, _ => rfl
  | _, _, bd_apprel f t, n', m => by
    simp only [liftBoundedFormulaAt, BoundedPreformula.fst, liftFormulaAt,
      lift_bounded_formula_fst f n' m, lift_bounded_term_fst t n' m]
  | _, _, bd_imp f₁ f₂, n', m => by
    simp [lift_bounded_formula_fst f₁ n' m, lift_bounded_formula_fst f₂ n' m]
  | n, _, bd_all f, n', m =>
    by
    simp only [liftBoundedFormulaAt, BoundedPreformula.fst,
      BoundedPreformula.cast_eq_fst, lift_bounded_formula_fst f n' (m + 1)]
    rfl

/-! ## Sentence theories (src/fol.lean lines 2233-2759) -/


/-- A `SentTheory` is a set of sentences (Lean 3: `Theory L = set
(sentence L)`). -/
abbrev SentTheory (L : Language.{u}) :=
  Set (sentence L)

/-- Project a sentence theory to a set of formulas -/
@[reducible, expose]
def SentTheory.fst (T : SentTheory L) : Set (formula L) :=
  BoundedPreformula.fst '' T

lemma SentTheory.lift_irrel (T : SentTheory L) : (liftFormula1 '' T.fst) = T.fst :=
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

/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped notation:51 T " ⊢ₛ " f => Fol.SentTheory.sprf T f
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped notation:51 T " ⊢ₛ' " f => Fol.SentTheory.sprovable T f

/-! ### All-realize-sentence — a structure models a sentence
theory -/


/-- A structure S realizes all sentences in T -/
@[expose]
def allRealizeSentence (S : Structure L) (T : SentTheory L) : Prop :=
  ∀ ⦃f⦄, f ∈ T → S ⊨ₘ f

-- Use ⊨ₜ for "structure realizes a sentence theory" (distinct
-- from existing ⊨ₛ)
/-- Notation for the corresponding first-order syntax or interpretation operation. -/
scoped notation:51 S " ⊨ₜ " T => Fol.allRealizeSentence S T

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

lemma realize_sentence_of_mem {S : Structure L} {T : SentTheory L} {f : sentence L}
    (H : S ⊨ₜ T) (h_mem : f ∈ T) : S ⊨ₘ f :=
  H h_mem

/-! ### ssatisfied — semantic consequence for sentence theories
-/


/-- T semantically entails ψ: every nonempty model of T satisfies
ψ -/
@[expose]
def ssatisfied (T : SentTheory L) (f : sentence L) : Prop :=
  ∀ ⦃S : Structure L⦄, Nonempty S → allRealizeSentence S T → S ⊨ₘ f

-- Note: ⊨ₛ is already taken by satisfied_in; use ssatisfied
-- directly.

/-- Flypitch construction `all_ssatisfied`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def allSsatisfied (T T' : SentTheory L) : Prop :=
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
    S ⊨ₘ (bdNot f) :=
  hS

/-! ## Model — bundled structure satisfying a sentence theory -/


/-- A model of T is a structure satisfying T.
    Lean 3 `Σ' (S : Structure L), S ⊨ T` → Lean 4 `{S : Structure L
    // all_realize_sentence S T}` -/
@[expose]
def Model (T : SentTheory L) : Type (u + 1) :=
  { S : Structure L // allRealizeSentence S T }

namespace Model

variable {T : SentTheory L}

/-- The underlying structure of a model -/
abbrev str (M : Model T) : Structure L :=
  M.val

/-- The model satisfies its theory -/
lemma sat (M : Model T) : allRealizeSentence M.str T :=
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

lemma false_of_Model_absurd {T : SentTheory L} (M : Model T) {ψ : sentence L}
    (h : Model.realize M ψ) (h' : Model.realize M (bdNot ψ)) : False :=
  h' h

/-! ### Soundness at sentence level -/


lemma ssatisfied_soundness {T : SentTheory L} {A : sentence L} (H : T ⊢ₛ' A) :
    ssatisfied T A :=
  ssatisfied_of_satisfied (formula_soundness (Nonempty.some H))

/-- Given a model M with M realizes ¬ψ, we have ¬ ssatisfied T ψ
-/
lemma not_ssatisfied_of_model_not {T : SentTheory L} {ψ : sentence L} (M : Model T)
    (hM : Model.realize M (bdNot ψ)) (h_nonempty : Nonempty M.str) : ¬ssatisfied T ψ :=
  by
  intro H
  exact false_of_Model_absurd M (H h_nonempty M.sat) hM

/-! ### Sentence-level is_consistent -/


/-- T is consistent if T.fst ⊬' ⊥ (at sentence/formula level) -/
@[expose]
def SentTheory.isConsistent (T : SentTheory L) : Prop :=
  ¬(T.fst ⊢' ⊥')

/-! ### Theory of a structure -/


/-- The theory of a structure S: all sentences true in S -/
@[expose]
def Th (S : Structure L) : SentTheory L :=
  {f : sentence L | S ⊨ₘ f}

lemma realize_sentence_Th (S : Structure L) : allRealizeSentence S (Th S) :=
  fun _f hf => hf

lemma SentTheory.is_consistent_Th (S : Structure L) (HS : Nonempty S) :
    (Th S).isConsistent := by
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


/-- Flypitch construction `eliminates_quantifiers`, retained by the first-order soundness and
completeness development.
-/
@[expose]
def eliminatesQuantifiers (T : SentTheory L) : Prop :=
  ∀ (f : sentence L),
    f ∈ T →
      ∃ f' : sentence L, BoundedPreformula.quantifierFree f' ∧ T.fst ⊢' (f.fst ⇔ f'.fst)

/-! ### L_empty, T_empty, T_equality -/


/-- The empty language with no functions and no relations -/
@[expose]
def LEmpty : Language.{u} :=
  ⟨fun _ => PEmpty, fun _ => PEmpty⟩

/-- The empty theory over a language -/
@[expose]
def TEmpty (L : Language.{u}) : SentTheory L :=
  ∅

/-- The equality theory: empty theory over the empty language -/
@[reducible, expose]
def TEquality : SentTheory (@LEmpty.{u}) :=
  TEmpty (@LEmpty.{u})

/-! ## Section bd_alls (src/fol.lean lines 2706-2757) -/


/-- Apply ∀' n times to an unbounded formula -/
@[simp, expose]
def alls : ∀ (_n : ℕ), formula L → formula L
  | 0, f => f
  | n + 1, f => ∀'(alls n f)

/-- Apply bd_all k times, reducing the bound index from n+k to n
-/
@[simp, expose]
def bdAlls' : ∀ (k n : ℕ), boundedFormula L (n + k) → boundedFormula L n
  | 0, _n, f => f
  | k + 1, n, f => bdAlls' k n (bd_all f)

/-- Close off a bounded formula by universally quantifying all n
free variables -/
@[simp, expose]
def bdAlls : ∀ (n : ℕ), boundedFormula L n → sentence L
  | 0, f => f
  | n + 1, f => bdAlls n (bd_all f)

@[simp]
lemma alls'_alls :
    ∀ (n : ℕ) (ψ : boundedFormula L n),
      bdAlls n ψ = bdAlls' n 0 (ψ.castEq (Nat.zero_add n).symm) :=
  by
  intro n
  induction n with
  | zero => intro ψ; simp [BoundedPreformula.castEq]
  | succ n ih =>
    intro ψ
    simp only [bdAlls, bdAlls']
    rw [ih (bd_all ψ)]
    simp [BoundedPreformula.castEq]

@[simp]
lemma alls'_all_commute {n k : ℕ} (f : boundedFormula L (n + k + 1)) :
    bdAlls' k n (bd_all f) = bd_all (bdAlls' k (n + 1) (f.castEq (by omega))) := by
  induction k generalizing n with
  | zero => simp [bdAlls', BoundedPreformula.castEq]
  | succ k ih =>
    simp only [bdAlls']
    rw [ih]
    simp [BoundedPreformula.castEq]

lemma realize_sentence_bd_alls {n : ℕ} {f : boundedFormula L n} {S : Structure L} :
    S ⊨ₘ (bdAlls n f) ↔ ∀ xs : DVec S n, realizeBoundedFormula xs f DVec.nil := by
  induction n with
  | zero =>
    simp only [bdAlls, realizeSentence]
    constructor
    · intro H xs
      rwa [DVec.zero_eq xs]
    · intro H
      exact H DVec.nil
  | succ n ih =>
    simp only [bdAlls]
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
