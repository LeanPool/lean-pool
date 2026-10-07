/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PresentedGroup

/-!
# Presentation

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

/-- A letter in a word on `n` generators. The Boolean records the sign. -/
abbrev SignedGenerator (n : ℕ) := Fin n × Bool

/-- A word on `n` generators. -/
abbrev Word (n : ℕ) := List (SignedGenerator n)

namespace Word

/-- The empty word. -/
def one : Word n :=
  []

/-- A positive generator as a one-letter word. -/
def generator (i : Fin n) : Word n :=
  [(i, true)]

/-- Formal inverse of a word. -/
def inverse (w : Word n) : Word n :=
  (w.reverse.map fun x => (x.1, !x.2))

/-- Formal word inversion is primitive recursive for the standard word encoding. -/
theorem inverse_primrec (n : ℕ) : Primrec (@inverse n) := by
  have hletterInverse : Primrec fun x : SignedGenerator n => (x.1, !x.2) :=
    Primrec.pair Primrec.fst (Primrec.not.comp Primrec.snd)
  apply Primrec.of_eq
    (Primrec.list_map Primrec.list_reverse (hletterInverse.comp Primrec.snd).to₂)
  intro w
  rfl

/-- Multiplication of words is concatenation. -/
def mul (u v : Word n) : Word n :=
  u ++ v

/-- Concatenate a finite list of words. -/
def product (ws : List (Word n)) : Word n :=
  ws.flatten

/-- A nonnegative power of a word. -/
def pow (w : Word n) (k : ℕ) : Word n :=
  (List.replicate k w).flatten

/-- Reindex the generators occurring in a word. -/
def mapGenerators (f : Fin n → Fin k) (w : Word n) : Word k :=
  w.map fun x => (f x.1, x.2)

/-- Interpret a positive two-letter word by substituting two group words. -/
def substitutePositive (s₁ s₂ : Word n) (w : List (Fin 2)) : Word n :=
  w.flatMap fun i => if i = 0 then s₁ else s₂

/-- Substitute a word for every signed generator in a word. -/
def substitute {A : Type*} (s : A → Word n) (w : List (A × Bool)) : Word n :=
  w.flatMap fun x => if x.2 then s x.1 else inverse (s x.1)

/-- The relator corresponding to the equation `lhs = rhs`. -/
def relation (lhs rhs : Word n) : Word n :=
  mul lhs (inverse rhs)

/-- The commutator convention `[u,v] = u⁻¹v⁻¹uv` used in the paper. -/
def commutator (u v : Word n) : Word n :=
  mul (inverse u) (mul (inverse v) (mul u v))

@[simp]
theorem inverse_mul (u v : Word n) :
    inverse (mul u v) = mul (inverse v) (inverse u) := by
  simp [inverse, mul, List.reverse_append]

@[simp]
theorem inverse_inverse (w : Word n) : inverse (inverse w) = w := by
  simp [inverse, Function.comp_def]

@[simp]
theorem substitute_append {A : Type*} (s : A → Word n)
    (u v : List (A × Bool)) :
    substitute s (u ++ v) = mul (substitute s u) (substitute s v) := by
  simp [substitute, mul]

@[simp]
theorem substitute_invRev {A : Type*} (s : A → Word n)
    (w : List (A × Bool)) :
    substitute s (FreeGroup.invRev w) = inverse (substitute s w) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨i, sign⟩
      rw [show FreeGroup.invRev ((i, sign) :: w) =
        FreeGroup.invRev w ++ [(i, !sign)] by
          simp [FreeGroup.invRev]]
      rw [substitute_append, ih]
      cases sign with
      | false =>
          simp only [substitute, Bool.not_false, Bool.false_eq_true,
            ite_false, ite_true, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          change mul (inverse (substitute s w)) (s i) =
            inverse (mul (inverse (s i)) (substitute s w))
          rw [inverse_mul, inverse_inverse]
      | true =>
          simp only [substitute, Bool.not_true,
            ite_true, List.flatMap_cons, List.flatMap_nil,
            List.append_nil]
          change mul (inverse (substitute s w)) (inverse (s i)) =
            inverse (mul (s i) (substitute s w))
          rw [inverse_mul]

@[simp]
theorem substitute_flatten {A : Type*} (s : A → Word n)
    (ws : List (List (A × Bool))) :
    substitute s ws.flatten = product (ws.map (substitute s)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      change substitute s (w ++ ws.flatten) =
        mul (substitute s w) (product (ws.map (substitute s)))
      rw [substitute_append, ih]

/-- Evaluate a syntactic word after choosing values for its generators. -/
def eval {G : Type*} [Group G] (x : Fin n → G) (w : Word n) : G :=
  FreeGroup.lift x (FreeGroup.mk w)

@[simp]
theorem eval_generator {G : Type*} [Group G]
    (x : Fin n → G) (i : Fin n) :
    eval x (generator i) = x i := by
  simp [eval, generator]

@[simp]
theorem eval_mul {G : Type*} [Group G]
    (x : Fin n → G) (u v : Word n) :
    eval x (mul u v) = eval x u * eval x v :=
  map_mul (FreeGroup.lift x) (FreeGroup.mk u) (FreeGroup.mk v)

@[simp]
theorem eval_append {G : Type*} [Group G]
    (x : Fin n → G) (u v : Word n) :
    eval x (u ++ v) = eval x u * eval x v :=
  eval_mul x u v

theorem mk_inverse (w : Word n) :
    FreeGroup.mk (inverse w) = (FreeGroup.mk w)⁻¹ := by
  rw [FreeGroup.inv_mk]
  simp only [inverse, FreeGroup.invRev, List.map_reverse]

@[simp]
theorem eval_inverse {G : Type*} [Group G]
    (x : Fin n → G) (w : Word n) :
    eval x (inverse w) = (eval x w)⁻¹ := by
  rw [eval, mk_inverse]
  exact map_inv (FreeGroup.lift x) (FreeGroup.mk w)

@[simp]
theorem eval_pow {G : Type*} [Group G]
    (x : Fin n → G) (w : Word n) (k : ℕ) :
    eval x (pow w k) = eval x w ^ k := by
  rw [eval, pow, ← FreeGroup.pow_mk]
  exact map_pow (FreeGroup.lift x) (FreeGroup.mk w) k

@[simp]
theorem eval_product {G : Type*} [Group G]
    (x : Fin n → G) (ws : List (Word n)) :
    eval x (product ws) = (ws.map (eval x)).prod := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      change eval x (mul w (product ws)) = _
      simp [ih]

@[simp]
theorem eval_mapGenerators {G : Type*} [Group G]
    (x : Fin k → G) (f : Fin n → Fin k) (w : Word n) :
    eval x (mapGenerators f w) = eval (x ∘ f) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨i, sign⟩
      cases sign <;>
        simp [eval, mapGenerators, FreeGroup.lift_mk, Function.comp_def]

theorem map_eval {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : Fin n → G) (w : Word n) :
    f (eval x w) = eval (f ∘ x) w := by
  change (f.comp (FreeGroup.lift x)) (FreeGroup.mk w) =
    (FreeGroup.lift (f ∘ x)) (FreeGroup.mk w)
  congr 1
  apply FreeGroup.ext_hom
  intro i
  simp [Function.comp_def]

@[simp]
theorem eval_substitutePositive {G : Type*} [Group G]
    (x : Fin n → G) (s₁ s₂ : Word n) (w : List (Fin 2)) :
    eval x (substitutePositive s₁ s₂ w) =
      (w.map fun i => if i = 0 then eval x s₁ else eval x s₂).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change eval x
          ((if i = 0 then s₁ else s₂) ++ substitutePositive s₁ s₂ w) =
        (if i = 0 then eval x s₁ else eval x s₂) *
          (w.map fun j => if j = 0 then eval x s₁ else eval x s₂).prod
      rw [eval_append, ih]
      split <;> rfl

@[simp]
theorem eval_substitute {G : Type*} [Group G]
    (x : Fin k → G) (s : Fin n → Word k) (w : Word n) :
    eval x (substitute s w) = eval (fun i => eval x (s i)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rcases a with ⟨i, sign⟩
      change eval x
          (mul (if sign then s i else inverse (s i)) (substitute s w)) =
        eval (fun i => eval x (s i)) ([(i, sign)] ++ w)
      rw [eval_mul, ih]
      cases sign
      · simp only [Bool.false_eq_true, ite_false]
        rw [eval_inverse]
        simp [eval, FreeGroup.lift_mk]
      · simp only [ite_true]
        simp [eval, FreeGroup.lift_mk]

@[simp]
theorem eval_relation {G : Type*} [Group G]
    (x : Fin n → G) (lhs rhs : Word n) :
    eval x (relation lhs rhs) = eval x lhs * (eval x rhs)⁻¹ := by
  simp [relation]

theorem eval_relation_eq_one_iff {G : Type*} [Group G]
    (x : Fin n → G) (lhs rhs : Word n) :
    eval x (relation lhs rhs) = 1 ↔ eval x lhs = eval x rhs := by
  rw [eval_relation]
  exact mul_inv_eq_one

@[simp]
theorem eval_commutator {G : Type*} [Group G]
    (x : Fin n → G) (u v : Word n) :
    eval x (commutator u v) =
      (eval x u)⁻¹ * (eval x v)⁻¹ * eval x u * eval x v := by
  simp [commutator, mul_assoc]

end Word

/--
Syntax for a finite group presentation with exactly `n` generator slots and
exactly `m` relator slots.
-/
structure FP (n m : ℕ) where
  /-- The indexed list of relator words in a finite group presentation. -/
  relator : Fin m → Word n

namespace FP

/-- The relators of a finite presentation, interpreted in the free group. -/
def relSet (P : FP n m) : Set (FreeGroup (Fin n)) :=
  Set.range fun i => FreeGroup.mk (P.relator i)

/-- The group defined by a finite presentation. -/
abbrev Group (P : FP n m) :=
  PresentedGroup P.relSet

/-- The word problem for a finite presentation. -/
def wordProblem (P : FP n m) (w : Word n) : Prop :=
  PresentedGroup.mk P.relSet (FreeGroup.mk w) = 1

/-- Evaluate a word in the group defined by a presentation. -/
def evalWord (P : FP n m) (w : Word n) : P.Group :=
  Word.eval (fun i => PresentedGroup.of i) w

theorem evalWord_eq_mk (P : FP n m) (w : Word n) :
    P.evalWord w = PresentedGroup.mk P.relSet (FreeGroup.mk w) := by
  change (FreeGroup.lift (fun i => PresentedGroup.of i)) (FreeGroup.mk w) = _
  congr 1
  apply FreeGroup.ext_hom
  intro i
  rfl

theorem wordProblem_iff_evalWord_eq_one (P : FP n m) (w : Word n) :
    P.wordProblem w ↔ P.evalWord w = 1 := by
  rw [evalWord_eq_mk]
  rfl

/-- Every designated relator evaluates to one in the presented group. -/
theorem relator_eq_one (P : FP n m) (i : Fin m) :
    P.evalWord (P.relator i) = 1 := by
  rw [evalWord_eq_mk]
  apply PresentedGroup.one_of_mem
  exact ⟨i, rfl⟩

/-- Map a presented group by choosing images of its generators and proving
that the designated relators hold. -/
def homOfRelators {G : Type*} [_root_.Group G] (P : FP n m) (x : Fin n → G)
    (h : ∀ i, Word.eval x (P.relator i) = 1) : P.Group →* G :=
  PresentedGroup.toGroup (f := x) fun r hr => by
    obtain ⟨i, rfl⟩ := hr
    exact h i

@[simp]
theorem homOfRelators_of {G : Type*} [_root_.Group G] (P : FP n m)
    (x : Fin n → G) (h : ∀ i, Word.eval x (P.relator i) = 1) (i : Fin n) :
    P.homOfRelators x h (PresentedGroup.of i) = x i :=
  PresentedGroup.toGroup.of (f := x) _

@[simp]
theorem homOfRelators_evalWord {G : Type*} [_root_.Group G] (P : FP n m)
    (x : Fin n → G) (h : ∀ i, Word.eval x (P.relator i) = 1) (w : Word n) :
    P.homOfRelators x h (P.evalWord w) = Word.eval x w := by
  rw [evalWord, Word.map_eval]
  congr 1
  funext i
  exact P.homOfRelators_of x h i

/-- A presentation presents the trivial group when every word represents `1`. -/
def presentsTrivial (P : FP n m) : Prop :=
  ∀ w : Word n, P.wordProblem w

/-- A word normally generates the group defined by `P`. -/
def NormallyGenerates (P : FP n m) (z : Word n) : Prop :=
  Subgroup.normalClosure
      ({PresentedGroup.mk P.relSet (FreeGroup.mk z)} : Set P.Group) =
    ⊤

theorem presentsTrivial_iff_subsingleton (P : FP n m) :
    P.presentsTrivial ↔ Subsingleton P.Group := by
  constructor
  · intro h
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective P.relSet a
    obtain ⟨y, rfl⟩ := PresentedGroup.mk_surjective P.relSet b
    have hx : PresentedGroup.mk P.relSet x = 1 := by
      rw [← FreeGroup.mk_toWord (x := x)]
      exact h x.toWord
    have hy : PresentedGroup.mk P.relSet y = 1 := by
      rw [← FreeGroup.mk_toWord (x := y)]
      exact h y.toWord
    exact hx.trans hy.symm
  · intro h w
    exact h.elim _ _

/-- A finite presentation is trivial when all of its canonical generators
are equal to one. -/
theorem presentsTrivial_of_generator_eq_one (P : FP n m)
    (h : ∀ i, (PresentedGroup.of i : P.Group) = 1) : P.presentsTrivial := by
  rw [presentsTrivial_iff_subsingleton]
  constructor
  intro a b
  have hmk : PresentedGroup.mk P.relSet =
      (1 : FreeGroup (Fin n) →* P.Group) := by
    apply FreeGroup.ext_hom
    intro i
    simpa [PresentedGroup.of] using h i
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective P.relSet a
  obtain ⟨y, rfl⟩ := PresentedGroup.mk_surjective P.relSet b
  rw [hmk]
  rfl

/--
A family of finite presentations is effective when one algorithm computes the
`i`th relator of the `j`th presentation from `j` and `i`.
-/
def Effective (A : ℕ → FP n m) : Prop :=
  Computable₂ fun j i => (A j).relator i

/--
An effective Adian--Rabin family for triviality: there is no algorithm deciding
which member of the family presents the trivial group.
-/
def IsAdianRabinFamily (A : ℕ → FP n m) : Prop :=
  Effective A ∧
    ¬ ComputablePred fun j => (A j).presentsTrivial

end FP

end Undecidability
