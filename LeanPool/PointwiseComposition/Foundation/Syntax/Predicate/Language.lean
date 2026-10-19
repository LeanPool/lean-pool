/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Logic.Entailment
public import Mathlib.Logic.Encodable.Basic

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Language of first-order logic

This file defines the language of first-order logic.

- `FFL.FirstOrder.Language.empty` is the empty language.
- `FFL.FirstOrder.Language.ofConstants C` is a language with only constants of the element `C`.
- `FFL.FirstOrder.Language.oRing`, `ℒₒᵣ` is the language of ordered ring.
-/

namespace FFL

namespace FirstOrder

/-- Function and relation symbols indexed by their arities. -/
structure Language where
  /-- The Func construction in `FFL.FirstOrder.Language`. -/
  Func : Nat → Type u
  /-- The Rel construction in `FFL.FirstOrder.Language`. -/
  Rel : Nat → Type u

namespace Language

/-- Data and laws for Relational in `FFL.FirstOrder.Language`. -/
class Relational (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func k)

instance {L : Language} [L.Relational] : IsEmpty (L.Func k) :=
  Relational.func_empty k

/-- Data and laws for Is Constant in `FFL.FirstOrder.Language`. -/
class IsConstant (L : Language) where
  func_empty : ∀ k, IsEmpty (L.Func (k + 1))
  rel_empty : ∀ k, IsEmpty (L.Rel k)

/-- Data and laws for Constant Inhabited in `FFL.FirstOrder.Language`. -/
class ConstantInhabited (L : Language) extends Inhabited (L.Func 0)

instance {L : Language} [L.ConstantInhabited] : Inhabited (L.Func 0) :=
  inferInstance

/-- The empty construction in `FFL.FirstOrder.Language`. -/
protected def empty : Language where
  Func := fun _ => PEmpty
  Rel := fun _ => PEmpty

instance : Inhabited Language :=
  ⟨Language.empty⟩

/-- Data and laws for Graph Func in `FFL.FirstOrder.Language`. -/
inductive GraphFunc : ℕ → Type
  | start : GraphFunc 0
  | terminal : GraphFunc 0

/-- Data and laws for Graph Rel in `FFL.FirstOrder.Language`. -/
inductive GraphRel : ℕ → Type
  | equal : GraphRel 2
  | le : GraphRel 2

/-- The graph construction in `FFL.FirstOrder.Language`. -/
def graph : Language where
  Func := GraphFunc
  Rel := GraphRel

/-- Data and laws for Binary Rel in `FFL.FirstOrder.Language`. -/
inductive BinaryRel : ℕ → Type
  | isone : BinaryRel 1
  | equal : BinaryRel 2
  | le : BinaryRel 2

/-- The binary construction in `FFL.FirstOrder.Language`. -/
def binary : Language where
  Func := fun _ => Empty
  Rel := BinaryRel

/-- Data and laws for Eq Rel in `FFL.FirstOrder.Language`. -/
inductive EqRel : ℕ → Type
  | equal : EqRel 2

/-- The equal construction in `FFL.FirstOrder.Language`. -/
@[reducible]
def equal : Language where
  Func := fun _ => Empty
  Rel := EqRel

instance (k) : ToString (equal.Func k) :=
  ⟨fun _ => ""⟩

instance (k) : ToString (equal.Rel k) :=
  ⟨fun _ => "\\mathrm{Eq}"⟩

instance (k) : DecidableEq (equal.Func k) := fun a b => by rcases a

instance (k) : DecidableEq (equal.Rel k) := fun a b => by rcases a; rcases b; exact isTrue (by simp)

instance (k) : Encodable (equal.Func k) :=
  IsEmpty.toEncodable

instance (k) : Encodable (equal.Rel k)
    where
  encode := fun _ => 0
  decode := fun _ =>
    match k with
    | 2 => some EqRel.equal
    | _ => none
  encodek := fun x => by rcases x; simp

namespace ORing

/-- Data and laws for Func in `FFL.FirstOrder.Language.ORing`. -/
inductive Func : ℕ → Type
  | zero : Func 0
  | one : Func 0
  | add : Func 2
  | mul : Func 2

/-- Data and laws for Rel in `FFL.FirstOrder.Language.ORing`. -/
inductive Rel : ℕ → Type
  | eq : Rel 2
  | lt : Rel 2

end ORing

/-- The ℒₒᵣ construction in `ℒₒᵣ`. -/
@[reducible]
def oRing : Language where
  Func := ORing.Func
  Rel := ORing.Rel

/-- The termℒₒᵣ construction in `FFL.FirstOrder.Language`. -/
notation "ℒₒᵣ" => oRing

namespace ORing

instance (k) : ToString (oRing.Func k) :=
  ⟨fun s =>
    match s with
    | Func.zero => "0"
    | Func.one => "1"
    | Func.add => "(+)"
    | Func.mul => "(\\cdot)"⟩

instance (k) : ToString (oRing.Rel k) :=
  ⟨fun s =>
    match s with
    | Rel.eq => "\\mathrm{Eq}"
    | Rel.lt => "\\mathrm{LT}"⟩

instance (k) : DecidableEq (oRing.Func k) := fun a b => by
  rcases a <;> rcases b <;> simp only [reduceCtorEq] <;>
      try { exact instDecidableTrue
      } <;>
    try { exact instDecidableFalse
    }

instance (k) : DecidableEq (oRing.Rel k) := fun a b => by
  rcases a <;> rcases b <;> simp only [reduceCtorEq] <;>
      try { exact instDecidableTrue
      } <;>
    try { exact instDecidableFalse
    }

instance (k) : Encodable (oRing.Func k)
    where
  encode := fun x =>
    match x with
    | Func.zero => 0
    | Func.one => 1
    | Func.add => 0
    | Func.mul => 1
  decode := fun e =>
    match k, e with
    | 0, 0 => some Func.zero
    | 0, 1 => some Func.one
    | 2, 0 => some Func.add
    | 2, 1 => some Func.mul
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

instance Func1IsEmpty : IsEmpty (oRing.Func 1) :=
  ⟨by rintro ⟨⟩⟩

lemma FuncGe3IsEmpty : ∀ k ≥ 3, IsEmpty (oRing.Func k)
  | 0 => by simp
  | 1 => by simp [show ¬3 ≤ 1 from of_decide_eq_false rfl]
  | 2 => by simp [show ¬3 ≤ 2 from of_decide_eq_false rfl]
  | (n + 3) => fun _ => ⟨by rintro ⟨⟩⟩

instance (k) : Encodable (oRing.Rel k)
    where
  encode := fun x =>
    match x with
    | Rel.eq => 0
    | Rel.lt => 1
  decode := fun e =>
    match k, e with
    | 2, 0 => some Rel.eq
    | 2, 1 => some Rel.lt
    | _, _ => none
  encodek := fun x => by rcases x <;> simp

/-- The func Equiv Fin Four construction in `FFL.FirstOrder.Language.ORing`. -/
def funcEquivFinFour : (k : ℕ) × oRing.Func k ≃ Fin 4
    where
  toFun
    f :=
    match f with
    | ⟨0, Func.zero⟩ => 0
    | ⟨0, Func.one⟩ => 1
    | ⟨2, Func.add⟩ => 2
    | ⟨2, Func.mul⟩ => 3
  invFun
    x :=
    match x with
    | 0 => ⟨0, Func.zero⟩
    | 1 => ⟨0, Func.one⟩
    | 2 => ⟨2, Func.add⟩
    | 3 => ⟨2, Func.mul⟩
  left_inv
    f :=
    match f with
    | ⟨0, Func.zero⟩ => rfl
    | ⟨0, Func.one⟩ => rfl
    | ⟨2, Func.add⟩ => rfl
    | ⟨2, Func.mul⟩ => rfl
  right_inv
    x :=
    match x with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl

/-- The rel Equiv Fin Two construction in `FFL.FirstOrder.Language.ORing`. -/
def relEquivFinTwo : (k : ℕ) × oRing.Rel k ≃ Fin 2
    where
  toFun
    f :=
    match f with
    | ⟨2, Rel.eq⟩ => 0
    | ⟨2, Rel.lt⟩ => 1
  invFun
    x :=
    match x with
    | 0 => ⟨2, Rel.eq⟩
    | 1 => ⟨2, Rel.lt⟩
  left_inv
    f :=
    match f with
    | ⟨2, Rel.eq⟩ => rfl
    | ⟨2, Rel.lt⟩ => rfl
  right_inv
    x :=
    match x with
    | 0 => rfl
    | 1 => rfl

end ORing

namespace Constant

variable (C : Type*)

/-- Data and laws for Func in `FFL.FirstOrder.Language.Constant`. -/
inductive Func : ℕ → Type _
  | const (c : C) : Func 0

end Constant

section Constant

variable (C : Type*)

/-- The of Constants construction in `FFL.FirstOrder.Language`. -/
def ofConstants : Language := ⟨Constant.Func C, fun _ => PEmpty⟩

--instance : Coe (Type*) Language := ⟨ofConstants⟩

instance : Coe C ((ofConstants C).Func 0) :=
  ⟨Constant.Func.const⟩

instance : IsConstant (ofConstants C)
    where
  func_empty := fun k => ⟨by rintro ⟨⟩⟩
  rel_empty := fun k => ⟨by rintro ⟨⟩⟩

/-- The unit construction in `FFL.FirstOrder.Language`. -/
abbrev unit : Language :=
  ofConstants PUnit

end Constant

/-- The of Func construction in `FFL.FirstOrder.Language`. -/
def ofFunc (F : ℕ → Type v) : Language :=
  ⟨F, fun _ => PEmpty⟩

/-- The add construction in `FFL.FirstOrder.Language`. -/
def add (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) : Language :=
  ⟨fun k => L₁.Func k ⊕ L₂.Func k, fun k => L₁.Rel k ⊕ L₂.Rel k⟩

instance : _root_.Add Language :=
  ⟨add⟩

/-- The sigma construction in `FFL.FirstOrder.Language`. -/
def sigma (L : ι → Language) : Language :=
  ⟨fun k => Σ i, (L i).Func k, fun k => Σ i, (L i).Rel k⟩

/-- Data and laws for Eq in `FFL.FirstOrder.Language`. -/
protected class Eq (L : Language) where
  /-- The eq construction in `FFL.FirstOrder.Language.Eq`. -/
  eq : L.Rel 2

/-- Data and laws for LT in `FFL.FirstOrder.Language`. -/
protected class LT (L : Language) where
  /-- The lt construction in `FFL.FirstOrder.Language.LT`. -/
  lt : L.Rel 2

/-- Data and laws for Mem in `FFL.FirstOrder.Language`. -/
protected class Mem (L : Language) where
  /-- The mem construction in `FFL.FirstOrder.Language.Mem`. -/
  mem : L.Rel 2

/-- Data and laws for Zero in `FFL.FirstOrder.Language`. -/
protected class Zero (L : Language) where
  /-- The zero construction in `FFL.FirstOrder.Language.Zero`. -/
  zero : L.Func 0

/-- Data and laws for One in `FFL.FirstOrder.Language`. -/
protected class One (L : Language) where
  /-- The one construction in `FFL.FirstOrder.Language.One`. -/
  one : L.Func 0

/-- Data and laws for Add in `FFL.FirstOrder.Language`. -/
protected class Add (L : Language) where
  /-- The add construction in `FFL.FirstOrder.Language.Add`. -/
  add : L.Func 2

/-- Data and laws for Mul in `FFL.FirstOrder.Language`. -/
protected class Mul (L : Language) where
  /-- The mul construction in `FFL.FirstOrder.Language.Mul`. -/
  mul : L.Func 2

/-- Data and laws for Pow in `FFL.FirstOrder.Language`. -/
protected class Pow (L : Language) where
  /-- The pow construction in `FFL.FirstOrder.Language.Pow`. -/
  pow : L.Func 2

/-- Data and laws for Exp in `FFL.FirstOrder.Language`. -/
protected class Exp (L : Language) where
  /-- The exp construction in `FFL.FirstOrder.Language.Exp`. -/
  exp : L.Func 1

/-- Data and laws for Pairing in `FFL.FirstOrder.Language`. -/
class Pairing (L : Language) where
  /-- The pair construction in `FFL.FirstOrder.Language.Pairing`. -/
  pair : L.Func 2

/-- Data and laws for Star in `FFL.FirstOrder.Language`. -/
class Star (L : Language) where
  /-- The star construction in `FFL.FirstOrder.Language.Star`. -/
  star : L.Func 0

attribute [match_pattern] Zero.zero One.one Add.add Mul.mul Exp.exp Eq.eq LT.lt Mem.mem
  Star.star

/-- Data and laws for ORing in `FFL.FirstOrder.Language`. -/
class ORing (L : Language) extends L.Eq, L.LT, L.Zero, L.One, L.Add, L.Mul

instance : ORing oRing where
  eq := .eq
  lt := .lt
  zero := .zero
  one := .one
  add := .add
  mul := .mul

instance : ConstantInhabited ℒₒᵣ where default := Language.Zero.zero

instance : Star unit where star := ()

instance (L : Language) (S : Language) [Star S] : Star (L.add S) where star := Sum.inr Star.star

instance (L : Language) (S : Language) [L.Zero] : (L.add S).Zero where zero := Sum.inl Zero.zero

instance (L : Language) (S : Language) [L.One] : (L.add S).One where one := Sum.inl One.one

instance (L : Language) (S : Language) [L.Add] : (L.add S).Add where add := Sum.inl Add.add

instance (L : Language) (S : Language) [L.Mul] : (L.add S).Mul where mul := Sum.inl Mul.mul

instance (L : Language) (S : Language) [L.Eq] : (L.add S).Eq where eq := Sum.inl Eq.eq

instance (L : Language) (S : Language) [L.LT] : (L.add S).LT where lt := Sum.inl LT.lt

/-- Data and laws for Hom in `FFL.FirstOrder.Language`. -/
@[ext]
structure Hom (L₁ L₂ : Language) where
  /-- The func construction in `FFL.FirstOrder.Language.Hom`. -/
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  /-- The rel construction in `FFL.FirstOrder.Language.Hom`. -/
  rel : {k : ℕ} → L₁.Rel k → L₂.Rel k

/--
A structure for the homomorphisms (respecting function and relation symbols) between first-order
languages.
-/
scoped[PointwiseComposition.FFL.FirstOrder]
  infix:25 " →ᵥ " => PointwiseComposition.FFL.FirstOrder.Language.Hom

namespace Hom
variable (L L₁ L₂ L₃ : Language) (Φ : Hom L₁ L₂)

/-- The id construction in `FFL.FirstOrder.Language.Hom`. -/
protected def id : L →ᵥ L where
  func := id
  rel := id

variable {L L₁ L₂ L₃}

/-- The comp construction in `FFL.FirstOrder.Language.Hom`. -/
def comp (Ψ : L₂ →ᵥ L₃) (Φ : L₁ →ᵥ L₂) : L₁ →ᵥ L₃
    where
  func := Ψ.func ∘ Φ.func
  rel := Ψ.rel ∘ Φ.rel

/-- The add₁ construction in `FFL.FirstOrder.Language.Hom`. -/
def add₁ (L₁ : Language) (L₂ : Language) : L₁ →ᵥ L₁.add L₂ :=
  ⟨Sum.inl, Sum.inl⟩

/-- The add₂ construction in `FFL.FirstOrder.Language.Hom`. -/
def add₂ (L₁ : Language) (L₂ : Language) : L₂ →ᵥ L₁.add L₂ :=
  ⟨Sum.inr, Sum.inr⟩

lemma func_add₁ (L₁ : Language) (L₂ : Language) (f : L₁.Func k) :
    (add₁ L₁ L₂).func f = Sum.inl f :=
  rfl

lemma rel_add₁ (L₁ : Language) (L₂ : Language) (r : L₁.Rel k) :
    (add₁ L₁ L₂).rel r = Sum.inl r :=
  rfl

lemma func_add₂ (L₁ : Language) (L₂ : Language) (f : L₂.Func k) :
    (add₂ L₁ L₂).func f = Sum.inr f :=
  rfl

lemma rel_add₂ (L₁ : Language) (L₂ : Language) (r : L₂.Rel k) :
    (add₂ L₁ L₂).rel r = Sum.inr r :=
  rfl

@[simp]
lemma add₂_star (L₁ : Language) (L₂ : Language) [Star L₂] :
    (add₂ L₁ L₂).func Star.star = Star.star :=
  rfl

@[simp]
lemma add₁_zero (L₁ : Language) (L₂ : Language) [L₁.Zero] :
    (add₁ L₁ L₂).func Zero.zero = Zero.zero :=
  rfl

@[simp]
lemma add₁_one (L₁ : Language) (L₂ : Language) [L₁.One] : (add₁ L₁ L₂).func One.one = One.one :=
  rfl

@[simp]
lemma add₁_add (L₁ : Language) (L₂ : Language) [L₁.Add] : (add₁ L₁ L₂).func Add.add = Add.add :=
  rfl

@[simp]
lemma add₁_mul (L₁ : Language) (L₂ : Language) [L₁.Mul] : (add₁ L₁ L₂).func Mul.mul = Mul.mul :=
  rfl

@[simp]
lemma add₁_eq (L₁ : Language) (L₂ : Language) [L₁.Eq] : (add₁ L₁ L₂).rel Eq.eq = Eq.eq :=
  rfl

@[simp]
lemma add₁_lt (L₁ : Language) (L₂ : Language) [L₁.LT] : (add₁ L₁ L₂).rel LT.lt = LT.lt :=
  rfl

/-- The sigma construction in `FFL.FirstOrder.Language.Hom`. -/
def sigma (L : ι → Language) (i : ι) : L i →ᵥ Language.sigma L :=
  ⟨fun f => ⟨i, f⟩, fun r => ⟨i, r⟩⟩

lemma func_sigma (L : ι → Language) (i : ι) (f : (L i).Func k) : (sigma L i).func f = ⟨i, f⟩ :=
  rfl

lemma rel_sigma (L : ι → Language) (i : ι) (r : (L i).Rel k) : (sigma L i).rel r = ⟨i, r⟩ :=
  rfl

end Hom

/-- The embedding construction in `FFL.FirstOrder.Language.ORing`. -/
def ORing.embedding (L : Language) [ORing L] : ℒₒᵣ →ᵥ L
    where
  func := fun {n} f ↦
    match n, f with
    | 0, Zero.zero => Zero.zero
    | 0, One.one => One.one
    | 2, Add.add => Add.add
    | 2, Mul.mul => Mul.mul
  rel := fun {n} r ↦
    match n, r with
    | 2, Eq.eq => Eq.eq
    | 2, LT.lt => LT.lt
end Language

/-- Data and laws for Decidable Eq in `FFL.FirstOrder.Language`. -/
protected class Language.DecidableEq (L : Language) where
  /-- The func construction in `FFL.FirstOrder.Language.DecidableEq`. -/
  func : (k : ℕ) → DecidableEq (L.Func k)
  /-- The rel construction in `FFL.FirstOrder.Language.DecidableEq`. -/
  rel : (k : ℕ) → DecidableEq (L.Rel k)

instance (L : Language) [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] :
    L.DecidableEq :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Func k) :=
  Language.DecidableEq.func k

instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) :=
  Language.DecidableEq.rel k

instance (L : Language) [L.DecidableEq] (k : ℕ) : DecidableEq (L.Rel k) :=
  Language.DecidableEq.rel k

/-- Data and laws for Encodable in `FFL.FirstOrder.Language`. -/
protected class Language.Encodable (L : Language) where
  /-- The func construction in `FFL.FirstOrder.Language.Encodable`. -/
  func : (k : ℕ) → Encodable (L.Func k)
  /-- The rel construction in `FFL.FirstOrder.Language.Encodable`. -/
  rel : (k : ℕ) → Encodable (L.Rel k)

instance (L : Language) [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] :
    L.Encodable :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Func k) :=
  Language.Encodable.func k

instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Rel k) :=
  Language.Encodable.rel k

instance (L : Language) [L.Encodable] (k : ℕ) : Encodable (L.Rel k) :=
  Language.Encodable.rel k

/-- Data and laws for Finite in `FFL.FirstOrder.Language`. -/
class Language.Finite (L : Language) where
  /-- The func construction in `FFL.FirstOrder.Language.Finite`. -/
  func : Fintype ((k : ℕ) × L.Func k)
  /-- The rel construction in `FFL.FirstOrder.Language.Finite`. -/
  rel : Fintype ((k : ℕ) × L.Rel k)

instance : Language.Finite ℒₒᵣ
    where
  func := Fintype.ofEquiv (Fin 4) Language.ORing.funcEquivFinFour.symm
  rel := Fintype.ofEquiv (Fin 2) Language.ORing.relEquivFinTwo.symm

end FirstOrder

end FFL
end

end PointwiseComposition
