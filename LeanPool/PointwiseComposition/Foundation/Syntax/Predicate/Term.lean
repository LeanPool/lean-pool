/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Syntax.Predicate.Language
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.String

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Terms of first-order logic

This file defines the terms of first-order logic.

The bounded variables are denoted by `#x` for `x : Fin n`, and free variables are denoted by
`&x` for `x : ξ`.
`t : Semiterm L ξ n` is a (semi-)term of language `L` with bounded variables of `Fin n` and free
variables of `ξ`.

-/

namespace FFL

namespace FirstOrder

/--
A semiterm of language `L`, with bound variables indexed by `Fin n` and free variables indexed
by `ξ`. In `FFL.FirstOrder.Semiformula`, bound variables are de Bruijn indices with a separate
type from free variables.
-/
inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n

/-- `&x` is the free variable indexed by the element `x : ξ`. -/
scoped prefix:max "&" => Semiterm.fvar

/-- `#x` is the bound variable with de Bruijn index `x`. -/
scoped prefix:max "#" => Semiterm.bvar

/-- The Term construction in `FFL.FirstOrder`. -/
abbrev Term (L : Language) (ξ : Type*) :=
  Semiterm L ξ 0

/-- The Closed Semiterm construction in `FFL.FirstOrder`. -/
abbrev ClosedSemiterm (L : Language) (n : ℕ) :=
  Semiterm L Empty n

/-- The Closed Term construction in `FFL.FirstOrder`. -/
abbrev ClosedTerm (L : Language) :=
  Semiterm L Empty 0

/-- The Syntactic Semiterm construction in `FFL.FirstOrder`. -/
abbrev SyntacticSemiterm (L : Language) (n : ℕ) :=
  Semiterm L ℕ n

/-- The Syntactic Term construction in `FFL.FirstOrder`. -/
abbrev SyntacticTerm (L : Language) :=
  SyntacticSemiterm L 0

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

instance [Inhabited ξ] : Inhabited (Semiterm L ξ n) :=
  ⟨&default⟩

section ToString

variable [∀ k, ToString (L.Func k)] [ToString ξ]

/-- The to Str construction in `FFL.FirstOrder.Semiterm`. -/
def toStr : Semiterm L ξ n → String
  | #x => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _ => toString c
  | func (arity := _ + 1) f v =>
    "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"

instance : Repr (Semiterm L ξ n) :=
  ⟨fun t _ => toStr t⟩

instance : ToString (Semiterm L ξ n) :=
  ⟨toStr⟩

end ToString

section Decidable

variable [∀ k, DecidableEq (L.Func k)] [DecidableEq ξ]

/-- The has Dec Eq construction in `FFL.FirstOrder.Semiterm`. -/
def hasDecEq : (t u : Semiterm L ξ n) → Decidable (Eq t u)
  | #x, #y => by simpa using decEq x y
  | #_, &_ => isFalse (by simp)
  | #_, func _ _ => isFalse (by simp)
  | &_, #_ => isFalse (by simp)
  | &x, &y => by simpa using decEq x y
  | &_, func _ _ => isFalse (by simp)
  | func _ _, #_ => isFalse (by simp)
  | func _ _, &_ => isFalse (by simp)
  | @func L ξ _ k₁ r₁ v₁, @func L ξ _ k₂ r₂ v₂ =>
    by
    by_cases e : k₁ = k₂
    · rcases e with rfl
      exact
        match decEq r₁ r₂ with
        | isTrue h => by simpa [h] using Matrix.decVec _ _ fun i ↦ hasDecEq (v₁ i) (v₂ i)
        | isFalse h => isFalse (by simp [h])
    · exact isFalse (by simp [e])

instance : DecidableEq (Semiterm L ξ n) :=
  hasDecEq

end Decidable

/-- The complexity of a semiterm, taking suprema at function symbols.
-/
def complexity : Semiterm L ξ n → ℕ
  | #_ => 0
  | &_ => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1

@[simp]
lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 :=
  rfl

@[simp]
lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 :=
  rfl

lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 :=
  rfl

@[simp]
lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  simpa [complexity_func, Nat.lt_add_one_iff] using
    Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)

/-- The func! construction in `FFL.FirstOrder.Semiterm`. -/
abbrev funcWithArity (k) (f : L.Func k) (v : Fin k → Semiterm L ξ n) :=
  func f v

/-- The set of bound variables occurring in a semiterm.
-/
def bv : Semiterm L ξ n → Finset (Fin n)
  | #x => { x }
  | &_ => ∅
  | func _ v => .biUnion .univ fun i ↦ bv (v i)

@[simp]
lemma bv_bvar : (#x : Semiterm L ξ n).bv = { x } :=
  rfl

@[simp]
lemma bv_fvar : (&x : Semiterm L ξ n).bv = ∅ :=
  rfl

lemma bv_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).bv = .biUnion .univ fun i ↦ bv (v i) :=
  rfl

@[simp]
lemma bv_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).bv = ∅ :=
  rfl

/-- The Positive construction in `FFL.FirstOrder.Semiterm`. -/
def Positive (t : Semiterm L ξ (n + 1)) : Prop :=
  ∀ x ∈ t.bv, 0 < x

namespace Positive

@[simp]
protected lemma bvar : Positive (#x : Semiterm L ξ (n + 1)) ↔ 0 < x := by simp [Positive]

@[simp]
protected lemma fvar : Positive (&x : Semiterm L ξ (n + 1)) := by simp [Positive]

@[simp]
protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ (n + 1)) :
    Positive (func f v) ↔ ∀ i, Positive (v i) := by simpa [Positive, bv] using forall_comm

end Positive

lemma bv_eq_empty_of_positive {t : Semiterm L ξ 1} (ht : t.Positive) : t.bv = ∅ :=
  Finset.eq_empty_of_forall_notMem <| by simp_all [Positive]

section freeVariables

variable [DecidableEq ξ]

/-- The set of free variables occuring in a semiterm.
-/
def freeVariables : Semiterm L ξ n → Finset ξ
  | #_ => ∅
  | &x => { x }
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)

@[simp]
lemma freeVariables_bvar : (#x : Semiterm L ξ n).freeVariables = ∅ :=
  rfl

@[simp]
lemma freeVariables_fvar : (&x : Semiterm L ξ n).freeVariables = { x } :=
  rfl

lemma freeVariables_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables :=
  rfl

@[simp]
lemma freeVariables_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) :
    (func f v).freeVariables = ∅ :=
  rfl

@[simp]
lemma freeVariables_empty {ο : Type*} [IsEmpty ο] {t : Semiterm L ο n} : t.freeVariables = ∅ :=
  by ext x; exact IsEmpty.elim inferInstance x

/-- The FVar? construction in `FFL.FirstOrder.Semiterm`. -/
abbrev HasFreeVariable (t : Semiterm L ξ n) (x : ξ) : Prop :=
  x ∈ t.freeVariables

@[simp]
lemma hasFreeVariable_bvar (x z) : ¬(#x : Semiterm L ξ n).HasFreeVariable z := by
  simp [HasFreeVariable]

@[simp]
lemma hasFreeVariable_fvar (x z) : (&x : Semiterm L ξ n).HasFreeVariable z ↔ x = z := by
  simp [HasFreeVariable, Eq.comm]

@[simp]
lemma hasFreeVariable_func (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).HasFreeVariable x ↔ ∃ i, (v i).HasFreeVariable x := by
  simp [HasFreeVariable, freeVariables_func]

end freeVariables

section lMap

variable (Φ : L₁ →ᵥ L₂)

/-- The map on terms induced from a homomorphism between languages.
-/
def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  | #x => #x
  | &x => &x
  | func f v => func (Φ.func f) fun i ↦ lMap Φ (v i)

@[simp]
lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x :=
  rfl

@[simp]
lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x :=
  rfl

@[simp]
lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (lMap Φ ∘ v) :=
  rfl

lemma lMap_func' {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) fun i ↦ lMap Φ (v i) :=
  rfl

@[simp]
lemma lMap_positive (t : Semiterm L₁ ξ (n + 1)) : (t.lMap Φ).Positive ↔ t.Positive := by
  induction t <;> simp [lMap_func, *]

@[simp]
lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (t : Semiterm L₁ ξ n) :
    (Semiterm.lMap Φ t).freeVariables = t.freeVariables :=
  by
  induction t
  case bvar => simp
  case fvar => simp
  case func k f v ih => ext x; simp [lMap_func, freeVariables_func, ih]

end lMap

section

variable [L.ConstantInhabited]

instance : Inhabited (Semiterm L ξ n) :=
  ⟨func default ![]⟩

lemma default_def : (default : Semiterm L ξ n) = func default ![] :=
  rfl

end

section idxOfFVar

/-- The fvar List construction in `FFL.FirstOrder.Semiterm`. -/
def fvarList : Semiterm L ξ n → List ξ
  | #_ => []
  | &x => [x]
  | func _ v => List.flatten <| Matrix.toList fun i ↦ fvarList (v i)

/-- The idx Of FVar construction in `FFL.FirstOrder.Semiterm`. -/
def idxOfFVar [DecidableEq ξ] (t : Semiterm L ξ n) : ξ → ℕ :=
  t.fvarList.idxOf

/-- The enumerate FVar construction in `FFL.FirstOrder.Semiterm`. -/
def enumerateFVar [Inhabited ξ] (t : Semiterm L ξ n) : ℕ → ξ := fun i ↦
  if hi : i < t.fvarList.length then t.fvarList.get ⟨i, hi⟩ else default

lemma enumerateFVar_idxOfFVar [DecidableEq ξ] [Inhabited ξ] {t : Semiterm L ξ n} {x : ξ}
    (hx : x ∈ t.fvarList) : enumerateFVar t (idxOfFVar t x) = x := by
  simpa [enumerateFVar, idxOfFVar] using fun h ↦
    False.elim <| not_le.mpr (List.idxOf_lt_length_iff.mpr <| hx) h

lemma mem_fvarList_iff_hasFreeVariable [DecidableEq ξ] {t : Semiterm L ξ n} :
    x ∈ t.fvarList ↔ t.HasFreeVariable x := by
  induction t <;>
    { simp [fvarList, *]; try tauto
    }

end idxOfFVar

end Semiterm

end FirstOrder

end FFL

end

end PointwiseComposition
