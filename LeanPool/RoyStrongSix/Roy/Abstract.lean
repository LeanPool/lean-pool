/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.Ring.Basic

/-!
# Roy's "four equivalent statements" (Roy 1992, §3) in an abstract admissible system

Roy works in a category `𝒞` with a zero object in which every kernel admits a cokernel and vice
versa, kernels and cokernels being closed under composition ("admissible"). His argument only
uses the *existence* of kernels, cokernels and exact triples, so we encode an admissible category
by three relations on objects:

* `Ker A B` : there is a kernel `A → B`;
* `Cok B C` : there is a cokernel `B → C`;
* `Ex A B C` : there is a kernel `A → B` admitting a cokernel `B → C`.

Functions `Ob → ℕ` are *additive* (resp. *upper additive*) if `f B = f A + f C`
(resp. `f B ≥ f A + f C`) on exact triples.

Main results:
* `stmt1_to_stmt2`, `stmt2_to_stmt1'` (Roy, Theorem 3), and by duality `stmt1_to_stmt2'`;
* `theorem2bis_identity`: Roy's Theorem 2bis for the identity cokernel, which is the form used
  in the proof of Roy's Theorem 4.
-/

@[expose] public section

namespace LeanPool

namespace StrongSix.Roy

/-- An admissible system: the kernel / cokernel structure of an admissible category. -/
structure AdmSys (Ob : Type*) where
  /-- The first object is a kernel subobject of the second. -/
  Ker : Ob → Ob → Prop
  /-- The second object is a cokernel quotient of the first. -/
  Cok : Ob → Ob → Prop
  /-- Admissible exact triples, ordered as kernel, middle term, and cokernel. -/
  Ex : Ob → Ob → Ob → Prop
  ker_refl : ∀ X, Ker X X
  cok_refl : ∀ X, Cok X X
  ker_trans : ∀ {A B C}, Ker A B → Ker B C → Ker A C
  cok_trans : ∀ {A B C}, Cok A B → Cok B C → Cok A C
  ex_ker : ∀ {A B C}, Ex A B C → Ker A B
  ex_cok : ∀ {A B C}, Ex A B C → Cok B C
  ker_ex : ∀ {A B}, Ker A B → ∃ C, Ex A B C
  cok_ex : ∀ {B C}, Cok B C → ∃ A, Ex A B C

variable {Ob : Type*}

/-- The opposite admissible system. -/
def AdmSys.op (S : AdmSys Ob) : AdmSys Ob where
  Ker A B := S.Cok B A
  Cok A B := S.Ker B A
  Ex A B C := S.Ex C B A
  ker_refl X := S.cok_refl X
  cok_refl X := S.ker_refl X
  ker_trans h1 h2 := S.cok_trans h2 h1
  cok_trans h1 h2 := S.ker_trans h2 h1
  ex_ker h := S.ex_cok h
  ex_cok h := S.ex_ker h
  ker_ex h := S.cok_ex h
  cok_ex h := S.ker_ex h

variable (S : AdmSys Ob)

/-- An invariant that adds across every admissible exact triple. -/
def Additive (f : Ob → ℕ) : Prop := ∀ ⦃A B C⦄, S.Ex A B C → f B = f A + f C

/-- The middle value bounds the sum of the values on the ends of an exact triple. -/
def UpperAdd (f : Ob → ℕ) : Prop := ∀ ⦃A B C⦄, S.Ex A B C → f A + f C ≤ f B

/-- Roy's standing hypotheses in Theorem 3. -/
structure Hyp (a b c d r : Ob → ℕ) : Prop where
  ha : UpperAdd S a
  hd : UpperAdd S d
  hb : Additive S b
  hc : Additive S c
  hr : Additive S r
  van : ∀ X, r X = 0 → a X = 0 ∧ b X = 0 ∧ c X = 0 ∧ d X = 0

theorem Hyp.op {a b c d r : Ob → ℕ} (h : Hyp S a b c d r) : Hyp S.op d c b a r where
  ha _ _ _ e := by have := h.hd e; simp only [AdmSys.op] at *; omega
  hd _ _ _ e := by have := h.ha e; simp only [AdmSys.op] at *; omega
  hb _ _ _ e := by have := h.hc e; omega
  hc _ _ _ e := by have := h.hb e; omega
  hr _ _ _ e := by have := h.hr e; omega
  van X hX := by have := h.van X hX; tauto

/-! ### The four statements -/

/-- Roy's descent statement selecting a cokernel with combined ratio at most `a / b`. -/
def Stmt1 (a b c d : Ob → ℕ) : Prop :=
  ∀ X, b X ≠ 0 → ∃ X', S.Cok X X' ∧ b X' + d X' ≠ 0 ∧
    ((a X' + c X' : ℕ) : ℚ) / (b X' + d X' : ℕ) ≤ (a X : ℚ) / b X

/-- Roy's extremal statement comparing `b / a` and `d / c` at a kernel minimum. -/
def Stmt2 (a b c d r : Ob → ℕ) : Prop :=
  ∀ X, b X ≠ 0 → c X ≠ 0 →
    (∀ Xs, S.Ker Xs X → c Xs ≠ 0 → (d X : ℚ) / c X ≤ (d Xs : ℚ) / c Xs) →
    (¬ ∃ X', S.Cok X X' ∧ c X' = 0 ∧ d X' = 0 ∧ r X' ≠ 0) →
    a X ≠ 0 ∧ (b X : ℚ) / a X ≤ (d X : ℚ) / c X

/-- The dual descent statement, selecting a kernel with a bounded ratio. -/
def Stmt1' (a b c d : Ob → ℕ) : Prop :=
  ∀ X, c X ≠ 0 → ∃ Xs, S.Ker Xs X ∧ a Xs + c Xs ≠ 0 ∧
    ((b Xs + d Xs : ℕ) : ℚ) / (a Xs + c Xs : ℕ) ≤ (d X : ℚ) / c X

/-- The dual extremal statement comparing `c / d` and `a / b` at a cokernel minimum. -/
def Stmt2' (a b c d r : Ob → ℕ) : Prop :=
  ∀ X, b X ≠ 0 → c X ≠ 0 →
    (∀ X', S.Cok X X' → b X' ≠ 0 → (a X : ℚ) / b X ≤ (a X' : ℚ) / b X') →
    (¬ ∃ Xs, S.Ker Xs X ∧ a Xs = 0 ∧ b Xs = 0 ∧ r Xs ≠ 0) →
    d X ≠ 0 ∧ (c X : ℚ) / d X ≤ (a X : ℚ) / b X

/-! ### Minimizing a ratio with bounded denominators -/

theorem exists_min_ratio {α : Type*} (P : α → Prop) (num den : α → ℕ) (B : ℕ)
    (hden : ∀ x, P x → 0 < den x ∧ den x ≤ B) (hne : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → (num x : ℚ) / den x ≤ (num y : ℚ) / den y := by
  classical
  -- key y = num y * (B! / den y), so that num y / den y = key y / B!
  let key : α → ℕ := fun y => num y * (B.factorial / den y)
  have hkey : ∀ y, P y → (num y : ℚ) / den y = (key y : ℚ) / B.factorial := by
    intro y hy
    obtain ⟨h0, hB⟩ := hden y hy
    have hdvd : den y ∣ B.factorial := Nat.dvd_factorial h0 hB
    have hf : (B.factorial : ℚ) = den y * ((B.factorial / den y : ℕ) : ℚ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    have hd0 : (den y : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
    have hq0 : ((B.factorial / den y : ℕ) : ℚ) ≠ 0 := by
      have : 0 < B.factorial / den y := Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos B) hdvd) h0
      exact_mod_cast this.ne'
    simp only [key]
    rw [hf, Nat.cast_mul]
    field_simp
  have hex : ∃ k, ∃ y, P y ∧ key y = k := by
    obtain ⟨x, hx⟩ := hne; exact ⟨key x, x, hx, rfl⟩
  obtain ⟨x, hx, hxk⟩ := Nat.find_spec hex
  refine ⟨x, hx, fun y hy => ?_⟩
  rw [hkey x hx, hkey y hy]
  have hmin : Nat.find hex ≤ key y := Nat.find_min' hex ⟨y, hy, rfl⟩
  rw [hxk]
  gcongr

theorem exists_min_nat {α : Type*} (P : α → Prop) (f : α → ℕ) (hne : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → f x ≤ f y := by
  classical
  have hex : ∃ k, ∃ y, P y ∧ f y = k := by
    obtain ⟨x, hx⟩ := hne; exact ⟨f x, x, hx, rfl⟩
  obtain ⟨x, hx, hxk⟩ := Nat.find_spec hex
  exact ⟨x, hx, fun y hy => hxk ▸ Nat.find_min' hex ⟨y, hy, rfl⟩⟩

/-! ### Elementary ratio inequalities (all quantities are natural numbers) -/

section Ratios

variable {p q m n t : ℚ}

/-- If `p/m ≥ t` and `(p+q)/(m+n) ≤ t` with `m, n > 0`, then `q/n ≤ t`. -/
theorem div_le_of_mediant (hm : 0 < m) (hn : 0 < n) (h1 : t ≤ p / m)
    (h2 : (p + q) / (m + n) ≤ t) : q / n ≤ t := by
  rw [le_div_iff₀ hm] at h1
  rw [div_le_iff₀ (by linarith)] at h2
  rw [div_le_iff₀ hn]
  nlinarith

/-- If `p/m ≤ t` and `q/n ≤ t` with `m, n > 0`, then `(p+q)/(m+n) ≤ t`. -/
theorem mediant_le (hm : 0 < m) (hn : 0 < n) (h1 : p / m ≤ t) (h2 : q / n ≤ t) :
    (p + q) / (m + n) ≤ t := by
  rw [div_le_iff₀ hm] at h1
  rw [div_le_iff₀ hn] at h2
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- If `t ≤ (p+q)/(m+n)` and `p/m ≤ t` with `m, n > 0`, then `t ≤ q/n`. -/
theorem le_div_of_mediant (hm : 0 < m) (hn : 0 < n) (h1 : p / m ≤ t)
    (h2 : t ≤ (p + q) / (m + n)) : t ≤ q / n := by
  rw [div_le_iff₀ hm] at h1
  rw [le_div_iff₀ (by linarith)] at h2
  rw [le_div_iff₀ hn]
  nlinarith

end Ratios

/-! ### Statement 1 ⇒ Statement 2 -/

variable {S}

theorem cok_b_le {b : Ob → ℕ} (hb : Additive S b) {X X' : Ob} (h : S.Cok X X') : b X' ≤ b X := by
  obtain ⟨A, hA⟩ := S.cok_ex h
  have := hb hA; omega

theorem ker_c_le {c : Ob → ℕ} (hc : Additive S c) {Xs X : Ob} (h : S.Ker Xs X) : c Xs ≤ c X := by
  obtain ⟨C, hC⟩ := S.ker_ex h
  have := hc hC; omega

theorem stmt1_to_stmt2 {a b c d r : Ob → ℕ} (H : Hyp S a b c d r) (h1 : Stmt1 S a b c d) :
    Stmt2 S a b c d r := by
  intro X hbX hcX hker hno
  -- E = cokernels with b ≠ 0; choose `X'` minimizing a/b
  obtain ⟨X', ⟨hXX', hbX'⟩, hmin⟩ := exists_min_ratio
    (fun Y => S.Cok X Y ∧ b Y ≠ 0) a b (b X)
    (fun Y hY => ⟨Nat.pos_of_ne_zero hY.2, cok_b_le H.hb hY.1⟩) ⟨X, S.cok_refl X, hbX⟩
  obtain ⟨X'', hX'X'', hbd'', h1''⟩ := h1 X' hbX'
  have hXX'' : S.Cok X X'' := S.cok_trans hXX' hX'X''
  have hb'pos : (0 : ℚ) < b X' := by exact_mod_cast Nat.pos_of_ne_zero hbX'
  -- (2)
  have h2 : b X'' ≠ 0 → (a X' : ℚ) / b X' ≤ (a X'' : ℚ) / b X'' :=
    fun hb'' => hmin X'' ⟨hXX'', hb''⟩
  -- d(X'') ≠ 0
  have hd'' : d X'' ≠ 0 := by
    intro hd0
    have hb'' : b X'' ≠ 0 := by omega
    have hb''pos : (0 : ℚ) < b X'' := by exact_mod_cast Nat.pos_of_ne_zero hb''
    have hc'' : c X'' = 0 := by
      have e1 := h1''
      rw [hd0] at e1
      push_cast at e1
      have e2 := h2 hb''
      have : (c X'' : ℚ) / b X'' ≤ 0 := by
        have := div_le_of_mediant (m := (b X'' : ℚ)) (n := (b X'' : ℚ)) hb''pos hb''pos
          (p := a X'') (q := c X'') (t := (a X'' : ℚ) / b X'') le_rfl
        have e3 : ((a X'' : ℚ) + c X'') / (b X'' + 0) ≤ (a X'' : ℚ) / b X'' := e1.trans e2
        rw [add_zero, add_div] at e3
        have : (c X'' : ℚ) / b X'' ≤ 0 := by linarith
        exact this
      have hnn : (0 : ℚ) ≤ (c X'' : ℚ) / b X'' := by positivity
      have : (c X'' : ℚ) / b X'' = 0 := le_antisymm this hnn
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · exact_mod_cast h
      · exact absurd h hb''pos.ne'
    have hr'' : r X'' ≠ 0 := fun hr0 => hb'' (H.van X'' hr0).2.1
    exact hno ⟨X'', hXX'', hc'', hd0, hr''⟩
  have hd''pos : (0 : ℚ) < d X'' := by exact_mod_cast Nat.pos_of_ne_zero hd''
  -- (3) c''/d'' ≤ a'/b'
  have h3 : (c X'' : ℚ) / d X'' ≤ (a X' : ℚ) / b X' := by
    by_cases hb'' : b X'' = 0
    · have e1 := h1''
      rw [hb''] at e1
      push_cast at e1
      rw [zero_add] at e1
      calc (c X'' : ℚ) / d X'' ≤ ((a X'' : ℚ) + c X'') / d X'' := by
            gcongr; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
        _ ≤ _ := e1
    · have hb''pos : (0 : ℚ) < b X'' := by exact_mod_cast Nat.pos_of_ne_zero hb''
      have e1 := h1''
      push_cast at e1
      exact div_le_of_mediant hb''pos hd''pos (h2 hb'') e1
  -- (4) a'/b' ≤ a/b
  have h4 : (a X' : ℚ) / b X' ≤ (a X : ℚ) / b X := hmin X ⟨S.cok_refl X, hbX⟩
  -- kernel of the composite cokernel
  obtain ⟨Xs, hEx⟩ := S.cok_ex hXX''
  have hcadd := H.hc hEx
  have hdadd := H.hd hEx
  have hdX : d X ≠ 0 := by omega
  have hdXpos : (0 : ℚ) < d X := by exact_mod_cast Nat.pos_of_ne_zero hdX
  have hcXpos : (0 : ℚ) < c X := by exact_mod_cast Nat.pos_of_ne_zero hcX
  -- (5) c/d ≤ (c* + c'')/(d* + d'')
  have h5 : (c X : ℚ) / d X ≤ ((c Xs : ℚ) + c X'') / ((d Xs : ℚ) + d X'') := by
    rw [hcadd]; push_cast
    have hpos : (0 : ℚ) < (d Xs : ℚ) + d X'' := by positivity
    rw [div_le_div_iff₀ hdXpos hpos]
    have : ((d Xs : ℚ) + d X'') ≤ d X := by exact_mod_cast hdadd
    have hc0 : (0 : ℚ) ≤ (c Xs : ℚ) + c X'' := by positivity
    nlinarith
  -- (6) c/d ≤ c''/d''
  have h6 : (c X : ℚ) / d X ≤ (c X'' : ℚ) / d X'' := by
    by_cases hcs : c Xs = 0
    · rw [hcs] at h5; push_cast at h5; rw [zero_add] at h5
      calc (c X : ℚ) / d X ≤ (c X'' : ℚ) / ((d Xs : ℚ) + d X'') := h5
        _ ≤ (c X'' : ℚ) / d X'' := by
            gcongr; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    · have hk := hker Xs (S.ex_ker hEx) hcs
      have hcspos : (0 : ℚ) < c Xs := by exact_mod_cast Nat.pos_of_ne_zero hcs
      -- d* ≠ 0, otherwise d/c ≤ 0
      have hds : d Xs ≠ 0 := by
        intro h0
        rw [h0] at hk; push_cast at hk; rw [zero_div] at hk
        have : (0 : ℚ) < (d X : ℚ) / c X := by positivity
        linarith
      have hdspos : (0 : ℚ) < d Xs := by exact_mod_cast Nat.pos_of_ne_zero hds
      have hk' : (c Xs : ℚ) / d Xs ≤ (c X : ℚ) / d X := by
        rw [div_le_div_iff₀ hcXpos hcspos] at hk
        rw [div_le_div_iff₀ hdspos hdXpos]
        linarith
      exact le_div_of_mediant hdspos hd''pos hk' h5
  have hcda : (c X : ℚ) / d X ≤ (a X : ℚ) / b X := h6.trans (h3.trans h4)
  have hbXpos : (0 : ℚ) < b X := by exact_mod_cast Nat.pos_of_ne_zero hbX
  have haX : a X ≠ 0 := by
    intro h0
    rw [h0] at hcda; push_cast at hcda; rw [zero_div] at hcda
    have : (0 : ℚ) < (c X : ℚ) / d X := by positivity
    linarith
  refine ⟨haX, ?_⟩
  have haXpos : (0 : ℚ) < a X := by exact_mod_cast Nat.pos_of_ne_zero haX
  rw [div_le_div_iff₀ hdXpos hbXpos] at hcda
  rw [div_le_div_iff₀ haXpos hcXpos]
  linarith

/-! ### Statement 2 ⇒ Statement 1' -/

theorem stmt2_to_stmt1' {a b c d r : Ob → ℕ} (H : Hyp S a b c d r) (h2 : Stmt2 S a b c d r) :
    Stmt1' S a b c d := by
  intro X hcX
  -- E = kernels with c ≠ 0; E0 = minimizers of d/c; choose one with r minimal
  obtain ⟨X0, ⟨hK0, hc0⟩, hmin0⟩ := exists_min_ratio
    (fun Y => S.Ker Y X ∧ c Y ≠ 0) d c (c X)
    (fun Y hY => ⟨Nat.pos_of_ne_zero hY.2, ker_c_le H.hc hY.1⟩) ⟨X, S.ker_refl X, hcX⟩
  obtain ⟨Xs, ⟨⟨hKs, hcs⟩, hEs⟩, hrmin⟩ := exists_min_nat
    (fun Y => (S.Ker Y X ∧ c Y ≠ 0) ∧ (d Y : ℚ) / c Y = (d X0 : ℚ) / c X0) r
    ⟨X0, ⟨hK0, hc0⟩, rfl⟩
  have hminS : ∀ Y, S.Ker Y X → c Y ≠ 0 → (d Xs : ℚ) / c Xs ≤ (d Y : ℚ) / c Y := by
    intro Y hY hcY; rw [hEs]; exact hmin0 Y ⟨hY, hcY⟩
  have hcspos : (0 : ℚ) < c Xs := by exact_mod_cast Nat.pos_of_ne_zero hcs
  have hcXpos : (0 : ℚ) < c X := by exact_mod_cast Nat.pos_of_ne_zero hcX
  have hidX : (d Xs : ℚ) / c Xs ≤ (d X : ℚ) / c X := hminS X (S.ker_refl X) hcX
  refine ⟨Xs, hKs, by omega, ?_⟩
  push_cast
  by_cases hbs : b Xs = 0
  · rw [hbs]; push_cast; rw [zero_add]
    calc (d Xs : ℚ) / ((a Xs : ℚ) + c Xs) ≤ (d Xs : ℚ) / c Xs := by
          gcongr; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
      _ ≤ _ := hidX
  · -- `Xs` satisfies the hypotheses of Statement 2
    have hk : ∀ Y, S.Ker Y Xs → c Y ≠ 0 → (d Xs : ℚ) / c Xs ≤ (d Y : ℚ) / c Y :=
      fun Y hY hcY => hminS Y (S.ker_trans hY hKs) hcY
    have hno : ¬ ∃ X', S.Cok Xs X' ∧ c X' = 0 ∧ d X' = 0 ∧ r X' ≠ 0 := by
      rintro ⟨X', hC, hc', hd', hr'⟩
      obtain ⟨Y, hY⟩ := S.cok_ex hC
      have ec := H.hc hY
      have ed := H.hd hY
      have er := H.hr hY
      have hcY : c Y ≠ 0 := by omega
      have hcYpos : (0 : ℚ) < c Y := by exact_mod_cast Nat.pos_of_ne_zero hcY
      have hKY : S.Ker Y X := S.ker_trans (S.ex_ker hY) hKs
      -- d(Y)/c(Y) ≤ d(Xs)/c(Xs), so `Y` is also a minimizer
      have hle : (d Y : ℚ) / c Y ≤ (d Xs : ℚ) / c Xs := by
        have : c Y = c Xs := by omega
        rw [this]; gcongr; exact_mod_cast (by omega : d Y ≤ d Xs)
      have hEY : (d Y : ℚ) / c Y = (d X0 : ℚ) / c X0 := by
        rw [← hEs]; exact le_antisymm hle (hminS Y hKY hcY)
      have := hrmin Y ⟨⟨hKY, hcY⟩, hEY⟩
      omega
    obtain ⟨has, hba⟩ := h2 Xs hbs hcs hk hno
    have haspos : (0 : ℚ) < a Xs := by exact_mod_cast Nat.pos_of_ne_zero has
    exact (mediant_le haspos hcspos hba le_rfl).trans hidX

/-! ### Duality: Statement 1 ⇒ Statement 2' -/

theorem stmt1_to_stmt2' {a b c d r : Ob → ℕ} (H : Hyp S a b c d r) (h1 : Stmt1 S a b c d) :
    Stmt2' S a b c d r := by
  have h1' := stmt2_to_stmt1' H (stmt1_to_stmt2 H h1)
  -- Statement 1' for `S` is Statement 1 for `S.op` with `(d, c, b, a)`
  have h1op : Stmt1 S.op d c b a := by
    intro X hcX
    obtain ⟨Xs, hK, hne, hle⟩ := h1' X hcX
    refine ⟨Xs, hK, by omega, ?_⟩
    have e1 : ((d Xs + b Xs : ℕ) : ℚ) = ((b Xs + d Xs : ℕ) : ℚ) := by push_cast; ring
    have e2 : ((c Xs + a Xs : ℕ) : ℚ) = ((a Xs + c Xs : ℕ) : ℚ) := by push_cast; ring
    rw [e1, e2]; exact hle
  have h2op := stmt1_to_stmt2 (S := S.op) H.op h1op
  intro X hbX hcX hcok hno
  exact h2op X hcX hbX hcok (fun ⟨Xs, hK, hb, ha, hr⟩ => hno ⟨Xs, hK, ha, hb, hr⟩)

/-! ### Theorem 2bis for the identity cokernel -/

/-- **Roy, Theorem 2bis (identity case).** Assume Statement 1 and Roy's Proposition 3. If the
identity of `X` minimizes `d₁/b` among cokernels of `X` with `b ≠ 0`, and there is no kernel
`Xs → X` with `d₁ = b = 0` and `r ≠ 0`, then `(d₁ + c)/(b + d) ≤ d₁/b` at `X`. -/
theorem theorem2bis_identity {a b c d r d1 : Ob → ℕ} (H : Hyp S a b c d r)
    (hd1 : Additive S d1) (h1 : Stmt1 S a b c d)
    (hprop3 : ∀ X, ∃ X'', S.Cok X X'' ∧ d1 X'' ≤ a X ∧ b X'' = b X)
    (ha_le : ∀ X, a X ≤ d1 X)
    (X : Ob) (hbX : b X ≠ 0)
    (hE1 : ∀ X', S.Cok X X' → b X' ≠ 0 → (d1 X : ℚ) / b X ≤ (d1 X' : ℚ) / b X')
    (hnoker : ¬ ∃ Xs, S.Ker Xs X ∧ d1 Xs = 0 ∧ b Xs = 0 ∧ r Xs ≠ 0) :
    ((d1 X + c X : ℕ) : ℚ) / (b X + d X : ℕ) ≤ (d1 X : ℚ) / b X := by
  have hbXpos : (0 : ℚ) < b X := by exact_mod_cast Nat.pos_of_ne_zero hbX
  -- a(X) = d₁(X)
  have haX : a X = d1 X := by
    obtain ⟨X'', hC, hd1'', hb''⟩ := hprop3 X
    have := hE1 X'' hC (by rw [hb'']; exact hbX)
    rw [hb''] at this
    have : (d1 X : ℚ) ≤ d1 X'' := by
      rwa [div_le_div_iff_of_pos_right hbXpos] at this
    have : d1 X ≤ d1 X'' := by exact_mod_cast this
    have := ha_le X
    omega
  -- the identity minimizes a/b
  have hE0 : ∀ X', S.Cok X X' → b X' ≠ 0 → (a X : ℚ) / b X ≤ (a X' : ℚ) / b X' := by
    intro X' hC hb'
    obtain ⟨X'', hC'', hd1'', hb''⟩ := hprop3 X'
    have hb'pos : (0 : ℚ) < b X' := by exact_mod_cast Nat.pos_of_ne_zero hb'
    have h := hE1 X'' (S.cok_trans hC hC'') (by rw [hb'']; exact hb')
    rw [hb''] at h
    rw [haX]
    calc (d1 X : ℚ) / b X ≤ (d1 X'' : ℚ) / b X' := h
      _ ≤ (a X' : ℚ) / b X' := by gcongr
  by_cases hcX : c X = 0
  · rw [hcX]; push_cast; rw [add_zero]
    gcongr; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · have hno : ¬ ∃ Xs, S.Ker Xs X ∧ a Xs = 0 ∧ b Xs = 0 ∧ r Xs ≠ 0 := by
      rintro ⟨Xs, hK, -, hbs, hrs⟩
      obtain ⟨X'', hEx⟩ := S.ker_ex hK
      have eb := H.hb hEx
      have ed1 := hd1 hEx
      have hb'' : b X'' = b X := by omega
      have := hE1 X'' (S.ex_cok hEx) (by rw [hb'']; exact hbX)
      rw [hb''] at this
      have : (d1 X : ℚ) ≤ d1 X'' := by rwa [div_le_div_iff_of_pos_right hbXpos] at this
      have : d1 X ≤ d1 X'' := by exact_mod_cast this
      exact hnoker ⟨Xs, hK, by omega, hbs, hrs⟩
    obtain ⟨hdX, hcd⟩ := stmt1_to_stmt2' H h1 X hbX hcX hE0 hno
    have hdXpos : (0 : ℚ) < d X := by exact_mod_cast Nat.pos_of_ne_zero hdX
    push_cast
    rw [← haX]
    exact mediant_le hbXpos hdXpos le_rfl hcd

end StrongSix.Roy

end LeanPool
