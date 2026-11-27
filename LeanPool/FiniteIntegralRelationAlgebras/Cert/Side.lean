/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Fast

/-!
# Pre-classified sides of the associativity conditions

One side of the condition of a quadruple is a disjunction of conjunctions of two class codes.
Once the number `b` of low variables is fixed, every term is of one of a few kinds: constant,
a low variable or a conjunction of two (a *fixed* term, a table independent of the high
variables), or guarded by high variables (an *item* `(tm, code)`: active when the high variables
selected by the mask `tm` are all true, and then contributing `true` for `code = 0` or the low
variable `code - 1`).

A `Side` lists the items and fixed terms explicitly, so that evaluating it for given high
variables takes a few kernel reduction steps per item; `classify` computes the same data from
the rows of class codes and `classify_sem` shows that it has the right meaning.
-/

@[expose] public section

namespace RACert

/-- A side of a condition: the mask of its high variables, its items `(tm, code)` and its fixed
terms `i * 64 + j` (the conjunction of the low variables `i ≤ j`). -/
abbrev Side := ℕ × List (ℕ × ℕ) × List ℕ

/-- Reduce a small number and pass it on as a literal. The kernel caches the values of
expressions, so the arguments of an expensive function such as `pat` must always have the same
form; here it is the literal handed to the minor premise of the recursor. -/
noncomputable def forceL {γ : Type} (r : ℕ) (k : ℕ → γ) : γ :=
  Nat.rec (motive := fun _ => γ) (k 0) (fun n _ => k n) (Nat.add r 1)

theorem forceL_eq {γ : Type} (r : ℕ) (k : ℕ → γ) : forceL r k = k r := rfl

/-- The table of a fixed term. -/
noncomputable def termV (b c : ℕ) : ℕ :=
  bif Nat.beq (Nat.div c 64) (Nat.mod c 64) then pat b (Nat.mod c 64)
  else Nat.land (pat b (Nat.div c 64)) (pat b (Nat.mod c 64))

/-- The meaning of a fixed term. -/
def termSem (c β : ℕ) : Bool := β.testBit (c / 64) && β.testBit (c % 64)

theorem termV_spec {b c β : ℕ} (h₁ : c / 64 < b) (h₂ : c % 64 < b) (hβ : β < 2 ^ b) :
    termV b c < top b ∧ (termV b c).testBit β = termSem c β := by
  obtain ⟨p1, p2⟩ := pat_spec h₁ hβ
  obtain ⟨q1, q2⟩ := pat_spec h₂ hβ
  unfold termV termSem
  by_cases h : c / 64 = c % 64
  · rw [beq_true (show Nat.div c 64 = Nat.mod c 64 from h)]
    refine ⟨q1, ?_⟩
    change (pat b (c % 64)).testBit β = _
    rw [q2, h, Bool.and_self]
  · rw [beq_false (show Nat.div c 64 ≠ Nat.mod c 64 from h)]
    refine ⟨land_lt q1, ?_⟩
    change (Nat.land (pat b (c / 64)) (pat b (c % 64))).testBit β = _
    rw [testBit_land, p2, q2]

/-- Pass the expression of the table of a fixed term to the continuation. -/
noncomputable def termK {γ : Type} (b c : ℕ) (k : ℕ → γ) : γ :=
  forceL (Nat.div c 64) fun i => forceL (Nat.mod c 64) fun j =>
    bif Nat.beq i j then k (pat b j) else k (Nat.land (pat b i) (pat b j))

theorem termK_eq {γ : Type} (b c : ℕ) (k : ℕ → γ) : termK b c k = k (termV b c) := by
  unfold termK termV
  rw [forceL_eq, forceL_eq]
  cases Nat.beq (Nat.div c 64) (Nat.mod c 64) <;> rfl

/-!
Tables are handled as *expressions*: a value `some e : Option ℕ` carries an expression `e` that
the kernel only evaluates when it becomes the argument of a big-number operation, at which point
the result is cached under `e`. A table which is just handed on is never evaluated a second time,
and equal expressions built for different leaves are evaluated once. `none` is the empty table.
-/

/-- The table of an optional expression. -/
def optV : Option ℕ → ℕ
  | none => 0
  | some e => e

/-- Disjunction of an optional table with a table. -/
noncomputable def orO (acc : Option ℕ) (t : ℕ) : Option ℕ :=
  Option.rec (motive := fun _ => Option ℕ) (some t) (fun e => some (Nat.lor e t)) acc

theorem orO_spec {b t : ℕ} {acc : Option ℕ} (hacc : optV acc < top b) (ht : t < top b) (β : ℕ) :
    optV (orO acc t) < top b ∧
      (optV (orO acc t)).testBit β = ((optV acc).testBit β || t.testBit β) := by
  cases acc with
  | none => exact ⟨ht, by simp [orO, optV]⟩
  | some e => exact ⟨lor_lt hacc ht, testBit_lor _ _ _⟩

/-- The disjunction of the fixed terms, added to `acc`. -/
noncomputable def fixedA (b : ℕ) : List ℕ → Option ℕ → Option ℕ
  | [], acc => acc
  | c :: fixed, acc => fixedA b fixed (orO acc (termV b c))

/-- The disjunction of the fixed terms. -/
noncomputable def fixedO (b : ℕ) (fixed : List ℕ) : Option ℕ :=
  List.rec (motive := fun _ => Option ℕ → Option ℕ) (fun acc => acc)
    (fun c _ ih acc => termK b c fun t => ih (orO acc t)) fixed none

theorem fixedO_eq (b : ℕ) (fixed : List ℕ) : fixedO b fixed = fixedA b fixed none := by
  have h : ∀ (fixed : List ℕ) (acc : Option ℕ),
      List.rec (motive := fun _ => Option ℕ → Option ℕ) (fun acc => acc)
        (fun c _ ih acc => termK b c fun t => ih (orO acc t)) fixed acc = fixedA b fixed acc := by
    intro fixed
    induction fixed with
    | nil => intro acc; rfl
    | cons c fixed ih =>
      intro acc
      change termK b c (fun t => List.rec (motive := fun _ => Option ℕ → Option ℕ)
        (fun acc => acc) (fun c _ ih acc => termK b c fun t => ih (orO acc t)) fixed
          (orO acc t)) = _
      rw [termK_eq, ih]
      rfl
  exact h fixed none

theorem fixedA_spec {b β : ℕ} (hβ : β < 2 ^ b) : ∀ {fixed : List ℕ} {acc : Option ℕ},
    (fixed.all fun c => Nat.blt (c / 64) b && Nat.blt (c % 64) b) = true → optV acc < top b →
    optV (fixedA b fixed acc) < top b ∧ (optV (fixedA b fixed acc)).testBit β =
      ((optV acc).testBit β || fixed.any fun c => termSem c β)
  | [], acc, _, hacc => ⟨hacc, by simp [fixedA]⟩
  | c :: fixed, acc, h, hacc => by
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
    obtain ⟨t1, t2⟩ := termV_spec h.1.1 h.1.2 hβ
    obtain ⟨o1, o2⟩ := orO_spec hacc t1 β
    obtain ⟨i1, i2⟩ := fixedA_spec hβ h.2 o1
    rw [fixedA]
    refine ⟨i1, ?_⟩
    rw [i2, o2, t2, List.any_cons, Bool.or_assoc]

/-- The value of a side: constant true, constant false, or a table given by an expression. -/
inductive SVal where
  | top
  | zero
  | tab (e : ℕ)

namespace SVal

/-- The value at an assignment of the low variables. -/
def sem : SVal → ℕ → Bool
  | top, _ => true
  | zero, _ => false
  | tab e, β => e.testBit β

/-- The table of the value is a table on `2 ^ b` bits. -/
def lt (b : ℕ) : SVal → Prop
  | tab e => e < RACert.top b
  | _ => True

end SVal

/-- The value of an optional table as a side. -/
noncomputable def ofOpt (acc : Option ℕ) : SVal :=
  Option.rec (motive := fun _ => SVal) SVal.zero (fun e => SVal.tab e) acc

/-- Add the active items to the accumulator `acc`: an active item with code `0` makes the whole
side true. -/
noncomputable def itemsO (b r : ℕ) (items : List (ℕ × ℕ)) : Option ℕ → SVal :=
  List.rec (motive := fun _ => Option ℕ → SVal) (fun acc => ofOpt acc)
    (fun it _ ih acc =>
      bif Nat.beq (Nat.land r it.1) it.1 then
        Nat.rec (motive := fun _ => SVal) SVal.top (fun i _ => ih (orO acc (pat b i))) it.2
      else ih acc) items

theorem itemsO_nil (b r : ℕ) (acc : Option ℕ) : itemsO b r [] acc = ofOpt acc := rfl

theorem itemsO_cons (b r : ℕ) (it : ℕ × ℕ) (items : List (ℕ × ℕ)) (acc : Option ℕ) :
    itemsO b r (it :: items) acc =
      bif Nat.beq (Nat.land r it.1) it.1 then
        Nat.rec (motive := fun _ => SVal) SVal.top
          (fun i _ => itemsO b r items (orO acc (pat b i))) it.2
      else itemsO b r items acc := rfl

/-- The meaning of an item. -/
def itemSem (r β : ℕ) (it : ℕ × ℕ) : Bool :=
  Nat.beq (Nat.land r it.1) it.1 && (Nat.beq it.2 0 || β.testBit (it.2 - 1))

theorem itemsO_spec {b r β : ℕ} (hβ : β < 2 ^ b) : ∀ {items : List (ℕ × ℕ)} {acc : Option ℕ},
    (items.all fun it => Nat.beq it.2 0 || Nat.blt (it.2 - 1) b) = true → optV acc < top b →
    (itemsO b r items acc).lt b ∧
      (itemsO b r items acc).sem β = ((optV acc).testBit β || items.any (itemSem r β))
  | [], acc, _, hacc => by
    rw [itemsO_nil]
    cases acc with
    | none => exact ⟨trivial, by simp [ofOpt, SVal.sem, optV]⟩
    | some e => exact ⟨show e < RACert.top b from hacc, by simp [ofOpt, SVal.sem, optV]⟩
  | it :: items, acc, h, hacc => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [itemsO_cons, List.any_cons, itemSem]
    cases hact : Nat.beq (Nat.land r it.1) it.1
    · obtain ⟨g1, g2⟩ := itemsO_spec (r := r) hβ h.2 hacc
      simp only [Bool.cond_false, Bool.false_and, Bool.false_or]
      exact ⟨g1, g2⟩
    · obtain ⟨tm, code⟩ := it
      match code, h.1 with
      | 0, _ => exact ⟨trivial, by rw [Bool.cond_true]; simp [SVal.sem]⟩
      | i + 1, hc =>
        have hi : i < b := by simpa using hc
        obtain ⟨p1, p2⟩ := pat_spec hi hβ
        obtain ⟨o1, o2⟩ := orO_spec hacc p1 β
        obtain ⟨g1, g2⟩ := itemsO_spec (r := r) hβ h.2 o1
        have hz : Nat.beq (i + 1) 0 = false := rfl
        rw [Bool.cond_true]
        change (itemsO b r items (orO acc (pat b i))).lt b ∧
          (itemsO b r items (orO acc (pat b i))).sem β = _
        refine ⟨g1, ?_⟩
        rw [g2, o2, p2]
        simp [Bool.or_assoc, hz]

/-- The value of a side, the high variables being given by `r`. -/
noncomputable def sideO (b : ℕ) (S : Side) (r : ℕ) : SVal := itemsO b r S.2.1 (fixedO b S.2.2)

/-- The meaning of a side. -/
def sideSem (S : List (ℕ × ℕ) × List ℕ) (r β : ℕ) : Bool :=
  S.1.any (itemSem r β) || S.2.any fun c => termSem c β

/-- The codes of a side refer to low variables, and its mask contains the masks of its items. -/
def sideWF (b : ℕ) (S : Side) : Bool :=
  (S.2.1.all fun it => Nat.beq it.2 0 || Nat.blt (it.2 - 1) b) &&
    ((S.2.1.all fun it => Nat.beq (Nat.land S.1 it.1) it.1) &&
      S.2.2.all fun c => Nat.blt (c / 64) b && Nat.blt (c % 64) b)

theorem sideO_spec {b β : ℕ} {S : Side} (hwf : sideWF b S = true) (hβ : β < 2 ^ b) (r : ℕ) :
    (sideO b S r).lt b ∧ (sideO b S r).sem β = sideSem S.2 r β := by
  rw [sideWF, Bool.and_eq_true, Bool.and_eq_true] at hwf
  obtain ⟨f1, f2⟩ := fixedA_spec hβ hwf.2.2 (acc := none) (top_pos b)
  rw [← fixedO_eq] at f1 f2
  obtain ⟨g1, g2⟩ := itemsO_spec (r := r) hβ hwf.1 f1
  refine ⟨g1, ?_⟩
  rw [sideO, g2, f2, sideSem]
  simp [optV, Bool.or_comm]

theorem land_of_sub {ρ α M m : ℕ} (h : Nat.land ρ M = Nat.land α M) (hs : Nat.land M m = m) :
    Nat.land ρ m = Nat.land α m := by
  have e : ∀ x : ℕ, Nat.land x m = Nat.land (Nat.land x M) m := by
    intro x
    change x &&& m = (x &&& M) &&& m
    rw [Nat.and_assoc]
    exact congrArg (x &&& ·) hs.symm
  rw [e ρ, e α, h]

/-- A side only depends on the high variables selected by its mask. -/
theorem sideSem_congr {b : ℕ} {S : Side} (hwf : sideWF b S = true) {r r' : ℕ}
    (h : Nat.land r S.1 = Nat.land r' S.1) (β : ℕ) : sideSem S.2 r β = sideSem S.2 r' β := by
  rw [sideWF, Bool.and_eq_true, Bool.and_eq_true] at hwf
  have key : ∀ it ∈ S.2.1, itemSem r β it = itemSem r' β it := by
    intro it hit
    have hs := List.all_eq_true.mp hwf.2.1 it hit
    rw [Nat.beq_eq] at hs
    rw [itemSem, itemSem, land_of_sub h hs]
  have hany : ∀ l : List (ℕ × ℕ), (∀ it ∈ l, itemSem r β it = itemSem r' β it) →
      l.any (itemSem r β) = l.any (itemSem r' β) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.any_cons, List.any_cons, hl x List.mem_cons_self,
        ih fun it hit => hl it (List.mem_cons_of_mem _ hit)]
  rw [sideSem, sideSem, hany S.2.1 key]

/-! ### Classification of the terms -/

/-- The mask of the high variable of a class code (`0` if it is not a high variable). -/
def hmOf (b c : ℕ) : ℕ := bif Nat.blt c (b + 2) then 0 else Nat.pow 2 (c - 2 - b)

/-- The low variable of a class code plus one (`0` if it is not a low variable). -/
def lvOf (b c : ℕ) : ℕ := bif Nat.blt c 2 then 0 else bif Nat.blt c (b + 2) then c - 1 else 0

/-- Add the term with class codes `c₁`, `c₂` to the items and fixed terms. -/
def clsTerm (b c₁ c₂ : ℕ) (S : List (ℕ × ℕ) × List ℕ) : List (ℕ × ℕ) × List ℕ :=
  bif Nat.beq c₁ 0 || Nat.beq c₂ 0 then S
  else bif Nat.beq (lvOf b c₁) 0 then
    (bif Nat.beq (lvOf b c₂) 0 || !Nat.beq (Nat.lor (hmOf b c₁) (hmOf b c₂)) 0 then
      ((Nat.lor (hmOf b c₁) (hmOf b c₂), lvOf b c₂) :: S.1, S.2)
    else (S.1, ((lvOf b c₂ - 1) * 64 + (lvOf b c₂ - 1)) :: S.2))
  else bif Nat.beq (lvOf b c₂) 0 then
    (bif !Nat.beq (Nat.lor (hmOf b c₁) (hmOf b c₂)) 0 then
      ((Nat.lor (hmOf b c₁) (hmOf b c₂), lvOf b c₁) :: S.1, S.2)
    else (S.1, ((lvOf b c₁ - 1) * 64 + (lvOf b c₁ - 1)) :: S.2))
  else
    (S.1, (min (lvOf b c₁ - 1) (lvOf b c₂ - 1) * 64 + max (lvOf b c₁ - 1) (lvOf b c₂ - 1)) :: S.2)

/-- The items and fixed terms of the disjunction of conjunctions of two rows. -/
def clsRows (b : ℕ) : List ℕ → List ℕ → List (ℕ × ℕ) × List ℕ
  | x :: xs, y :: ys => clsTerm b x y (clsRows b xs ys)
  | _, _ => ([], [])

/-- The items and fixed terms of the disjunction of conjunctions of two rows; a constant true
term makes the side constant. -/
def classify (b : ℕ) (r₁ r₂ : List ℕ) : List (ℕ × ℕ) × List ℕ :=
  bif hasTop r₁ r₂ then ([(0, 0)], []) else clsRows b r₁ r₂

/-- Whether the high variables selected by `h` are all true. -/
def actB (α h : ℕ) : Bool := Nat.beq (Nat.land α h) h

theorem actB_zero (α : ℕ) : actB α 0 = true := by
  rw [actB, Nat.beq_eq]
  exact Nat.and_zero α

theorem actB_two_pow (α h : ℕ) : actB α (Nat.pow 2 h) = α.testBit h := by
  rw [actB]
  change Nat.beq (α &&& 2 ^ h) (2 ^ h) = _
  rw [Nat.and_two_pow]
  cases α.testBit h
  · exact beq_false (by simpa using (Nat.two_pow_pos h).ne)
  · exact beq_true (by simp)

theorem actB_lor (α h₁ h₂ : ℕ) : actB α (Nat.lor h₁ h₂) = (actB α h₁ && actB α h₂) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, actB, actB, actB, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
  constructor
  · intro h
    have key : ∀ j, (h₁.testBit j || h₂.testBit j) = true → α.testBit j = true := by
      intro j hj
      have := congrArg (fun x => Nat.testBit x j) h
      simp only [testBit_land, testBit_lor] at this
      rw [hj, Bool.and_true] at this
      exact this
    constructor
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_land]
      cases hb : h₁.testBit j
      · simp
      · rw [key j (by simp [hb])]
        rfl
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [testBit_land]
      cases hb : h₂.testBit j
      · simp
      · rw [key j (by simp [hb])]
        rfl
  · rintro ⟨e₁, e₂⟩
    apply Nat.eq_of_testBit_eq
    intro j
    have a₁ := congrArg (fun x => Nat.testBit x j) e₁
    have a₂ := congrArg (fun x => Nat.testBit x j) e₂
    simp only [testBit_land] at a₁ a₂
    rw [testBit_land, testBit_lor, Bool.and_or_distrib_left, a₁, a₂]

/-- The value of the low variable `l - 1` (true for `l = 0`). -/
def lowB (β l : ℕ) : Bool := Nat.beq l 0 || β.testBit (l - 1)

/-- The value of a nonzero class code in terms of its high and low parts. -/
theorem litB_split (b α β : ℕ) {c : ℕ} (hc : c ≠ 0) :
    litB (joinN b α β) c = (actB α (hmOf b c) && lowB β (lvOf b c)) := by
  match c, hc with
  | 1, _ =>
    have h1 : hmOf b 1 = 0 := by
      have : Nat.blt 1 (b + 2) = true := by rw [Nat.blt_eq]; omega
      rw [hmOf, this]
      rfl
    rw [h1, actB_zero]
    rfl
  | j + 2, _ =>
    have hl : Nat.blt (j + 2) 2 = false := by
      rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
      omega
    by_cases hj : j < b
    · have hb : Nat.blt (j + 2) (b + 2) = true := by rw [Nat.blt_eq]; omega
      have hz : Nat.beq (j + 2 - 1) 0 = false := beq_false (by omega)
      rw [hmOf, lvOf, hb, hl]
      simp only [Bool.cond_true, Bool.cond_false]
      rw [actB_zero, lowB, hz]
      simp [litB, joinN, hj]
    · have hb : Nat.blt (j + 2) (b + 2) = false := by
        rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
        omega
      rw [hmOf, lvOf, hb, hl]
      simp only [Bool.cond_false, Nat.add_sub_cancel]
      rw [actB_two_pow]
      simp [litB, joinN, hj, lowB]

theorem lvOf_le (b c : ℕ) : lvOf b c ≤ b := by
  unfold lvOf
  cases Nat.blt c 2
  · cases h : Nat.blt c (b + 2)
    · exact Nat.zero_le b
    · rw [Nat.blt_eq] at h
      simp only [Bool.cond_false, Bool.cond_true]
      omega
  · exact Nat.zero_le b

theorem hmOf_of_lvOf {b c : ℕ} (h : lvOf b c ≠ 0) : hmOf b c = 0 := by
  unfold lvOf at h
  unfold hmOf
  cases h2 : Nat.blt c 2
  · cases h3 : Nat.blt c (b + 2)
    · rw [h2, h3] at h
      exact absurd rfl h
    · rfl
  · rw [h2] at h
    exact absurd rfl h

theorem termSem_pair {i j : ℕ} (hj : j < 64) (β : ℕ) :
    termSem (i * 64 + j) β = (β.testBit i && β.testBit j) := by
  rw [termSem]
  have h1 : (i * 64 + j) / 64 = i := by omega
  have h2 : (i * 64 + j) % 64 = j := by omega
  rw [h1, h2]

theorem sideSem_item (S : List (ℕ × ℕ) × List ℕ) (it : ℕ × ℕ) (r β : ℕ) :
    sideSem (it :: S.1, S.2) r β = (itemSem r β it || sideSem S r β) := by
  rw [sideSem, sideSem, List.any_cons, Bool.or_assoc]

theorem sideSem_fixed (S : List (ℕ × ℕ) × List ℕ) (c : ℕ) (r β : ℕ) :
    sideSem (S.1, c :: S.2) r β = (termSem c β || sideSem S r β) := by
  rw [sideSem, sideSem, List.any_cons]
  cases termSem c β <;> cases S.1.any (itemSem r β) <;> simp

/-- The meaning of the classification of one term. -/
theorem clsTerm_sem {b : ℕ} (hb : b ≤ 64) (α β c₁ c₂ : ℕ) (S : List (ℕ × ℕ) × List ℕ) :
    sideSem (clsTerm b c₁ c₂ S) α β =
      ((litB (joinN b α β) c₁ && litB (joinN b α β) c₂) || sideSem S α β) := by
  unfold clsTerm
  by_cases h0 : c₁ = 0 ∨ c₂ = 0
  · have : (Nat.beq c₁ 0 || Nat.beq c₂ 0) = true := by
      rcases h0 with h | h <;> simp [h]
    rw [this]
    rcases h0 with h | h <;> simp [h, litB]
  · have hc₁ : c₁ ≠ 0 := fun h => h0 (Or.inl h)
    have hc₂ : c₂ ≠ 0 := fun h => h0 (Or.inr h)
    have : (Nat.beq c₁ 0 || Nat.beq c₂ 0) = false := by
      rw [beq_false hc₁, beq_false hc₂]
      rfl
    rw [this, litB_split b α β hc₁, litB_split b α β hc₂]
    simp only [Bool.cond_false]
    have l₁ := lvOf_le b c₁
    have l₂ := lvOf_le b c₂
    by_cases e₁ : lvOf b c₁ = 0
    · rw [beq_true e₁]
      simp only [Bool.cond_true]
      by_cases e₂ : lvOf b c₂ = 0
      · rw [beq_true e₂]
        simp only [Bool.true_or, Bool.cond_true]
        rw [sideSem_item, itemSem, e₁, e₂]
        change (actB α _ && _ || _) = _
        rw [actB_lor]
        simp [lowB]
      · rw [beq_false e₂, Bool.false_or]
        have hm₂ := hmOf_of_lvOf e₂
        by_cases et : Nat.lor (hmOf b c₁) (hmOf b c₂) = 0
        · rw [beq_true et]
          simp only [Bool.not_true, Bool.cond_false]
          have hm₁ : hmOf b c₁ = 0 := by
            rw [hm₂] at et
            exact (Nat.or_zero _).symm.trans et
          rw [sideSem_fixed, termSem_pair (by omega), hm₁, hm₂, actB_zero, e₁]
          simp [lowB, beq_false e₂]
        · rw [beq_false et]
          simp only [Bool.not_false, Bool.cond_true]
          rw [sideSem_item, itemSem, e₁]
          change (actB α _ && _ || _) = _
          rw [actB_lor]
          simp [lowB, beq_false e₂, Bool.and_assoc]
    · rw [beq_false e₁]
      simp only [Bool.cond_false]
      have hm₁ := hmOf_of_lvOf e₁
      by_cases e₂ : lvOf b c₂ = 0
      · rw [beq_true e₂]
        simp only [Bool.cond_true]
        by_cases et : Nat.lor (hmOf b c₁) (hmOf b c₂) = 0
        · rw [beq_true et]
          simp only [Bool.not_true, Bool.cond_false]
          have hm₂ : hmOf b c₂ = 0 := by
            rw [hm₁] at et
            exact (Nat.zero_or _).symm.trans et
          rw [sideSem_fixed, termSem_pair (by omega), hm₁, hm₂, actB_zero, e₂]
          simp [lowB, beq_false e₁]
        · rw [beq_false et]
          simp only [Bool.not_false, Bool.cond_true]
          rw [sideSem_item, itemSem, e₂]
          change (actB α _ && _ || _) = _
          rw [actB_lor]
          simp only [lowB, beq_false e₁, Bool.false_or, beq_true rfl, Bool.true_or,
            Bool.and_true]
          cases actB α (hmOf b c₁) <;> cases actB α (hmOf b c₂) <;>
            cases β.testBit (lvOf b c₁ - 1) <;> rfl
      · rw [beq_false e₂]
        simp only [Bool.cond_false]
        have hm₂ := hmOf_of_lvOf e₂
        rw [sideSem_fixed, termSem_pair (by omega), hm₁, hm₂, actB_zero]
        simp only [lowB, beq_false e₁, beq_false e₂, Bool.false_or, Bool.true_and]
        rcases Nat.le_total (lvOf b c₁ - 1) (lvOf b c₂ - 1) with h | h
        · rw [Nat.min_eq_left h, Nat.max_eq_right h]
        · rw [Nat.min_eq_right h, Nat.max_eq_left h, Bool.and_comm]

theorem clsRows_sem {b : ℕ} (hb : b ≤ 64) (α β : ℕ) : ∀ (r₁ r₂ : List ℕ),
    sideSem (clsRows b r₁ r₂) α β =
      (r₁.zip r₂).any fun p => litB (joinN b α β) p.1 && litB (joinN b α β) p.2
  | x :: xs, y :: ys => by
    rw [clsRows, clsTerm_sem hb, clsRows_sem hb α β xs ys, List.zip_cons_cons, List.any_cons]
  | [], _ => by simp [clsRows, sideSem]
  | _ :: _, [] => by simp [clsRows, sideSem]

theorem zip_any_of_hasTop (f : ℕ → Bool) (hf : f 1 = true) : ∀ {r₁ r₂ : List ℕ},
    hasTop r₁ r₂ = true → ((r₁.zip r₂).any fun p => f p.1 && f p.2) = true
  | x :: xs, y :: ys, h => by
    rw [hasTop, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    rw [List.zip_cons_cons, List.any_cons, Bool.or_eq_true]
    rcases h with ⟨hx, hy⟩ | h
    · exact Or.inl (by rw [hx, hy, hf]; rfl)
    · exact Or.inr (zip_any_of_hasTop f hf h)
  | [], _, h => by simp [hasTop] at h
  | _ :: _, [], h => by simp [hasTop] at h

/-- **The meaning of the classification**: the disjunction of conjunctions of the two rows. -/
theorem classify_sem {b : ℕ} (hb : b ≤ 64) (α β : ℕ) (r₁ r₂ : List ℕ) :
    sideSem (classify b r₁ r₂) α β =
      (r₁.zip r₂).any fun p => litB (joinN b α β) p.1 && litB (joinN b α β) p.2 := by
  unfold classify
  cases h : hasTop r₁ r₂
  · exact clsRows_sem hb α β r₁ r₂
  · rw [zip_any_of_hasTop (litB (joinN b α β)) rfl h]
    simp [sideSem, itemSem]

/-- Equality of lists of pairs of numbers, as a Boolean. -/
def listBeq₂ : List (ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x.1 y.1 && (Nat.beq x.2 y.2 && listBeq₂ xs ys)
  | _, _ => false

theorem listBeq₂_eq : ∀ {l₁ l₂ : List (ℕ × ℕ)}, listBeq₂ l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | (a, c) :: xs, (a', c') :: ys, h => by
    rw [listBeq₂, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp only at h1 h2
    rw [h1, h2, listBeq₂_eq h3]
  | [], _ :: _, h => by simp [listBeq₂] at h
  | _ :: _, [], h => by simp [listBeq₂] at h

/-- The side `S` is the classification of the rows `r₁`, `r₂`. -/
def checkSide (b : ℕ) (S : Side) (r₁ r₂ : List ℕ) : Bool :=
  sideWF b S && (listBeq₂ S.2.1 (classify b r₁ r₂).1 && listBeq S.2.2 (classify b r₁ r₂).2)

theorem checkSide_spec {b : ℕ} {S : Side} {r₁ r₂ : List ℕ} (h : checkSide b S r₁ r₂ = true) :
    sideWF b S = true ∧ S.2 = classify b r₁ r₂ := by
  rw [checkSide, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1, Prod.ext (listBeq₂_eq h.2.1) (listBeq_eq h.2.2)⟩

end RACert
