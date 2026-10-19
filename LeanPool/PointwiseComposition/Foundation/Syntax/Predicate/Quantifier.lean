/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Logic.LogicSymbol

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL

/-- Data and laws for Polarity in `FFL`. -/
inductive Polarity where
  | sigma
  | pi

namespace Polarity

instance : SigmaSymbol Polarity :=
  ⟨sigma⟩

instance : PiSymbol Polarity :=
  ⟨pi⟩

/-- The alt construction in `FFL.Polarity`. -/
def alt : Polarity → Polarity
  | Σ => Π
  | Π => Σ

lemma eq_sigma : sigma = Σ :=
  rfl

lemma eq_pi : pi = Π :=
  rfl

@[simp]
lemma alt_sigma : alt Σ = Π :=
  rfl

@[simp]
lemma alt_pi : alt Π = Σ :=
  rfl

@[simp]
lemma alt_alt (Γ : Polarity) : Γ.alt.alt = Γ := by cases Γ <;> rfl

/-- `Γ` with its polarity flipped `k` times. -/
abbrev altItr (Γ : Polarity) (k : ℕ) : Polarity :=
  Polarity.alt^[k] Γ

@[simp]
lemma altItr_zero (Γ : Polarity) : Γ.altItr 0 = Γ :=
  rfl

lemma altItr_succ (Γ : Polarity) (k : ℕ) : Γ.altItr (k + 1) = (Γ.altItr k).alt :=
  Function.iterate_succ_apply' _ _ _

lemma altItr_succ' (Γ : Polarity) (k : ℕ) : Γ.altItr (k + 1) = Γ.alt.altItr k :=
  Function.iterate_succ_apply _ _ _

section symbol

variable {α : Type*} [SigmaSymbol α] [PiSymbol α]

/-- The coe construction in `FFL.Polarity`. -/
protected def coe : Polarity → α
  | Σ => Σ
  | Π => Π

instance : Coe Polarity α :=
  ⟨Polarity.coe⟩

@[simp]
lemma coe_sigma : ((Σ : Polarity) : α) = Σ :=
  rfl

@[simp]
lemma coe_pi : ((Π : Polarity) : α) = Π :=
  rfl

end symbol

end Polarity

/-- Data and laws for Sigma Pi Delta in `FFL`. -/
inductive SigmaPiDelta where
  | sigma
  | pi
  | delta

namespace SigmaPiDelta

instance : SigmaSymbol SigmaPiDelta :=
  ⟨sigma⟩

instance : PiSymbol SigmaPiDelta :=
  ⟨pi⟩

instance : DeltaSymbol SigmaPiDelta :=
  ⟨delta⟩

/-- The alt construction in `FFL.SigmaPiDelta`. -/
def alt : SigmaPiDelta → SigmaPiDelta
  | Σ => Π
  | Π => Σ
  | ∆ => ∆

lemma eq_sigma : sigma = Σ :=
  rfl

lemma eq_pi : pi = Π :=
  rfl

lemma eq_delta : delta = ∆ :=
  rfl

@[simp]
lemma alt_sigma : alt Σ = Π :=
  rfl

@[simp]
lemma alt_pi : alt Π = Σ :=
  rfl

@[simp]
lemma alt_delta : alt ∆ = ∆ :=
  rfl

@[simp]
lemma alt_alt (Γ : SigmaPiDelta) : Γ.alt.alt = Γ := by cases Γ <;> rfl

@[simp]
lemma alt_coe (Γ : Polarity) : SigmaPiDelta.alt Γ = (Γ.alt : SigmaPiDelta) := by cases Γ <;> rfl

end SigmaPiDelta

/-!
## First-order quantifiers -/

namespace FirstOrder

/-- Data and laws for Univ Quantifier in `FFL.FirstOrder`. -/
class UnivQuantifier (α : ℕ → Type*) where
  /-- The all construction in `FFL.FirstOrder.UnivQuantifier`. -/
  all : α (n + 1) → α n

/-- The «term∀¹ » construction in `FFL.FirstOrder`. -/
prefix:64 "∀¹ " => UnivQuantifier.all

/-- Data and laws for Exs Quantifier in `FFL.FirstOrder`. -/
class ExsQuantifier (α : ℕ → Type*) where
  /-- The exs construction in `FFL.FirstOrder.ExsQuantifier`. -/
  exs : α (n + 1) → α n

/-- The «term∃¹ » construction in `FFL.FirstOrder`. -/
prefix:64 "∃¹ " => ExsQuantifier.exs

attribute [match_pattern] UnivQuantifier.all ExsQuantifier.exs

/-- Data and laws for Quantifier in `FFL.FirstOrder`. -/
class Quantifier (α : ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → Type*) extends Quantifier α where
  /-- The connectives construction in `FFL.FirstOrder.LCWQ`. -/
  connectives : (n : ℕ) → LogicalConnective (α n)
  /-- The neutrals construction in `FFL.FirstOrder.LCWQ`. -/
  neutrals : (n : ℕ) → LogicalNeutral (α n)

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalConnective (α n) :=
  LCWQ.connectives n

instance (α : ℕ → Type*) [LCWQ α] (n : ℕ) : LogicalNeutral (α n) :=
  LCWQ.neutrals n

instance (α : ℕ → Type*) [Quantifier α] [(n : ℕ) → LogicalConnective (α n)]
    [(n : ℕ) → LogicalNeutral (α n)] : LCWQ α
    where
  connectives := inferInstance
  neutrals := inferInstance

section UnivQuantifier

variable {α : ℕ → Type*} [UnivQuantifier α]

/-- The all Closure construction in `FFL.FirstOrder`. -/
def allClosure : {n : ℕ} → α n → α 0
  | 0, a => a
  | _ + 1, a => allClosure (∀¹ a)

/-- The universal closure of a formula.
-/
prefix:64 "∀¹* " => allClosure

@[simp]
lemma allClosure_zero (a : α 0) : ∀¹* a = a :=
  rfl

lemma allClosure_succ {n} (a : α (n + 1)) : ∀¹* a = ∀¹* ∀¹ a :=
  rfl

/-- The all Itr construction in `FFL.FirstOrder`. -/
def allItr : (k : ℕ) → α (n + k) → α n
  | 0, a => a
  | k + 1, a => allItr k (∀¹ a)

/-- The «term∀¹^[ ] » construction in `FFL.FirstOrder`. -/
notation "∀¹^[" k "] " φ:64 => allItr k φ

@[simp]
lemma allItr_zero (a : α n) : ∀¹^[0] a = a :=
  rfl

@[simp]
lemma allItr_one (a : α (n + 1)) : ∀¹^[1] a = ∀¹ a :=
  rfl

lemma allItr_succ {k} (a : α (n + (k + 1))) : ∀¹^[k + 1] a = ∀¹^[k] (∀¹ a) :=
  rfl

end UnivQuantifier

section ExsQuantifier

variable {α : ℕ → Type*} [ExsQuantifier α]

/-- The exs Closure construction in `FFL.FirstOrder`. -/
def exsClosure : {n : ℕ} → α n → α 0
  | 0, a => a
  | _ + 1, a => exsClosure (∃¹ a)

/-- The existential closure of a formula.
-/
prefix:64 "∃¹* " => exsClosure

@[simp]
lemma exsClosure_zero (a : α 0) : ∃¹* a = a :=
  rfl

lemma exsClosure_succ {n} (a : α (n + 1)) : ∃¹* a = ∃¹* ∃¹ a :=
  rfl

/-- The exs Itr construction in `FFL.FirstOrder`. -/
def exsItr : (k : ℕ) → α (n + k) → α n
  | 0, a => a
  | k + 1, a => exsItr k (∃¹ a)

/-- Iterated application of `k` existential quantifiers. -/
notation "∃¹^[" k "] " φ:64 => exsItr k φ

@[simp]
lemma exsItr_zero (a : α n) : ∃¹^[0] a = a :=
  rfl

@[simp]
lemma exsItr_one (a : α (n + 1)) : ∃¹^[1] a = ∃¹ a :=
  rfl

lemma exsItr_succ {k} (a : α (n + (k + 1))) : ∃¹^[k + 1] a = ∃¹^[k] (∃¹ a) :=
  rfl

end ExsQuantifier

section quantifier

variable {α : ℕ → Type*}

/-- The ball construction in `FFL.FirstOrder`. -/
def ball [UnivQuantifier α] [Arrow (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n :=
  ∀¹ (φ ⇒ₗ ψ)

/-- The bexs construction in `FFL.FirstOrder`. -/
def bexs [ExsQuantifier α] [Wedge (α (n + 1))] (φ : α (n + 1)) (ψ : α (n + 1)) : α n :=
  ∃¹ (φ ⋏ ψ)

/-- A bounded universal quantifier. `∀¹[φ] ψ` is defined as `∀¹ (φ ⇒ₗ ψ)`. -/
notation:64 "∀¹[" φ "] " ψ => ball φ ψ

/-- A bounded existential quantifier. `∃¹[φ] ψ` is defined as `∃¹ (φ ⋏ ψ)`. -/
notation:64 "∃¹[" φ "] " ψ => bexs φ ψ

end quantifier

end FirstOrder

namespace Polarity

variable {α : ℕ → Type*} [FirstOrder.UnivQuantifier α] [FirstOrder.ExsQuantifier α] {n : ℕ}
  {Γ : Polarity}

/-- The quant construction in `FFL.Polarity`. -/
def quant : Polarity → α (n + 1) → α n
  | Σ => FirstOrder.ExsQuantifier.exs
  | Π => FirstOrder.UnivQuantifier.all

@[simp]
lemma quant_sigma (φ : α (n + 1)) : (Σ : Polarity).quant φ = ∃¹ φ :=
  rfl

@[simp]
lemma quant_pi (φ : α (n + 1)) : (Π : Polarity).quant φ = ∀¹ φ :=
  rfl

/-- Prefixes `k` alternating quantifiers starting with `Γ`. -/
def quantItr (Γ : Polarity) : (k : ℕ) → {n : ℕ} → α (n + k) → α n
  | 0, n, φ => φ
  | k + 1, n, φ => Γ.quant <| quantItr Γ.alt k (cast (by grind) φ)

@[simp]
lemma quantItr_zero (φ : α n) : quantItr Γ 0 φ = φ :=
  rfl

@[simp]
lemma quantItr_one (φ : α (n + 1)) : quantItr Γ 1 φ = Γ.quant φ :=
  rfl

lemma quantItr_succ {k} (φ : α (n + (k + 1))) :
    quantItr Γ (k + 1) φ = Γ.quant (quantItr Γ.alt k (cast (by grind) φ)) :=
  rfl

lemma cast_quant {m₁ m₂ : ℕ} (h : m₁ = m₂) (Γ : Polarity) (φ : α (m₁ + 1)) :
    cast (congrArg α h) (Γ.quant φ) = Γ.quant (cast (by grind) φ) := by subst h; rfl

lemma quantItr_succ' {k} (φ : α (n + (k + 1))) :
    quantItr Γ (k + 1) φ = quantItr Γ k ((Γ.altItr k).quant φ) := by
  induction k generalizing n Γ with
  | zero => simp [quantItr_one];
  | succ k ih =>
    rw [quantItr_succ, ih, quantItr_succ, altItr_succ']
    congr 2; grind;

end Polarity

/-!
## Second-order quantifiers -/

namespace SecondOrder

/-- Data and laws for Univ Quantifier in `FFL.SecondOrder`. -/
class UnivQuantifier (α : ℕ → ℕ → Type*) where
  /-- The all₁ construction in `FFL.SecondOrder.UnivQuantifier`. -/
  all₁ : α (m + 1) n → α m n

/-- The «term∀² » construction in `FFL.SecondOrder`. -/
prefix:64 "∀² " => UnivQuantifier.all₁

/-- Data and laws for Exs Quantifier in `FFL.SecondOrder`. -/
class ExsQuantifier (α : ℕ → ℕ → Type*) where
  /-- The exs₁ construction in `FFL.SecondOrder.ExsQuantifier`. -/
  exs₁ : α (m + 1) n → α m n

/-- The «term∃² » construction in `FFL.SecondOrder`. -/
prefix:64 "∃² " => ExsQuantifier.exs₁

attribute [match_pattern] UnivQuantifier.all₁ ExsQuantifier.exs₁

/-- Data and laws for Quantifier in `FFL.SecondOrder`. -/
class Quantifier (α : ℕ → ℕ → Type*) extends UnivQuantifier α, ExsQuantifier α

/-- Logical Connectives with Quantifiers. -/
class LCWQ (α : ℕ → ℕ → Type*) extends Quantifier α where
  /-- The first Order construction in `FFL.SecondOrder.LCWQ`. -/
  firstOrder : (m : ℕ) → FirstOrder.LCWQ (α m)

instance (α : ℕ → ℕ → Type*) [LCWQ α] (m : ℕ) : FirstOrder.LCWQ (α m) :=
  LCWQ.firstOrder m

instance (α : ℕ → ℕ → Type*) [Quantifier α] [(m : ℕ) → FirstOrder.LCWQ (α m)] : LCWQ α where
  firstOrder := inferInstance

section UnivQuantifier

variable {α : ℕ → ℕ → Type*} [UnivQuantifier α]

/-- The all Closure construction in `FFL.SecondOrder`. -/
def allClosure : {m : ℕ} → α m n → α 0 n
  | 0, a => a
  | _ + 1, a => allClosure (∀² a)

/-- The «term∀²* » construction in `FFL.SecondOrder`. -/
prefix:64 "∀²* " => allClosure

@[simp]
lemma allClosure_zero (a : α 0 n) : ∀²* a = a :=
  rfl

lemma allClosure_succ {n} (a : α (n + 1) n) : ∀²* a = ∀²* ∀² a :=
  rfl

/-- The all Itr construction in `FFL.SecondOrder`. -/
def allItr : (k : ℕ) → α (m + k) n → α m n
  | 0, a => a
  | k + 1, a => allItr k (∀² a)

/-- The «term∀²^[ ] » construction in `FFL.SecondOrder`. -/
notation "∀²^[" k "] " φ:64 => allItr k φ

@[simp]
lemma allItr_zero (a : α m n) : ∀²^[0] a = a :=
  rfl

@[simp]
lemma allItr_one (a : α (m + 1) n) : ∀²^[1] a = ∀² a :=
  rfl

lemma allItr_succ {k} (a : α (m + (k + 1)) n) : ∀²^[k + 1] a = ∀²^[k] (∀² a) :=
  rfl

end UnivQuantifier

section ExsQuantifier

variable {α : ℕ → ℕ → Type*} [ExsQuantifier α]

/-- The exs Closure construction in `FFL.SecondOrder`. -/
def exsClosure : {m : ℕ} → α m n → α 0 n
  | 0, a => a
  | _ + 1, a => exsClosure (∃² a)

/-- The «term∃²* » construction in `FFL.SecondOrder`. -/
prefix:64 "∃²* " => exsClosure

@[simp]
lemma exsClosure_zero (a : α 0 n) : ∃²* a = a :=
  rfl

lemma exsClosure_succ {n} (a : α (m + 1) n) : ∃²* a = ∃²* ∃² a :=
  rfl

/-- The exs Itr construction in `FFL.SecondOrder`. -/
def exsItr : (k : ℕ) → α (m + k) n → α m n
  | 0, a => a
  | k + 1, a => exsItr k (∃² a)

/-- The «term∃²^[ ] » construction in `FFL.SecondOrder`. -/
notation "∃²^[" k "] " φ:64 => exsItr k φ

@[simp]
lemma exsItr_zero (a : α m n) : ∃²^[0] a = a :=
  rfl

@[simp]
lemma exsItr_one (a : α (m + 1) n) : ∃²^[1] a = ∃² a :=
  rfl

lemma exsItr_succ {k} (a : α (m + (k + 1)) n) : ∃²^[k + 1] a = ∃²^[k] (∃² a) :=
  rfl

end ExsQuantifier

section quantifier

variable {α : ℕ → ℕ → Type*}

/-- The ball construction in `FFL.SecondOrder`. -/
def ball [UnivQuantifier α] [Arrow (α (m + 1) n)] (φ : α (m + 1) n) (ψ : α (m + 1) n) : α m n :=
  ∀² (φ ⇒ₗ ψ)

/-- The bexs construction in `FFL.SecondOrder`. -/
def bexs [ExsQuantifier α] [Wedge (α (m + 1) n)] (φ : α (m + 1) n) (ψ : α (m + 1) n) : α m n :=
  ∃² (φ ⋏ ψ)

/-- The «term∀²[ ] » construction in `FFL.SecondOrder`. -/
notation:64 "∀²[" φ "] " ψ => ball φ ψ

/-- The «term∃²[ ] » construction in `FFL.SecondOrder`. -/
notation:64 "∃²[" φ "] " ψ => bexs φ ψ

end quantifier

end SecondOrder

end FFL

end

end PointwiseComposition
