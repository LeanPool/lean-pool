/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Arithmetical Formula Sorted by Arithmetical Hierarchy

This file defines the $\Sigma_n / \Pi_n / \Delta_n$ formulas of arithmetic of first-order logic.

- `Σ-[m].Semiformula ξ n` is a `ArithmeticSemiformula ξ n` which is `Σ-[m]`.
- `Π-[m].Semiformula ξ n` is a `ArithmeticSemiformula ξ n` which is `Π-[m]`.
- `∆-[m].Semiformula ξ n` is a pair of `Σ-[m].Semiformula ξ n` and `Π-[m].Semiformula ξ n`.
- `ProperOn` : `φ.ProperOn M` iff `φ`'s two element `φ.sigma` and `φ.pi` are equivalent on model
`M`.

-/

namespace FFL
namespace FirstOrder
namespace Arithmetic

/-- Data and laws for Hierarchy Symbol in `FFL.FirstOrder.Arithmetic`. -/
structure HierarchySymbol where
  /-- The Γ construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol`. -/
  Γ : SigmaPiDelta
  /-- The rank construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol`. -/
  rank : ℕ

/-- The «term -[ ]» construction in `FFL.FirstOrder.Arithmetic`. -/
scoped notation:max Γ:max "-[" n "]" => HierarchySymbol.mk Γ n

/-- The Σ₀ construction in `Σ₀`. -/
abbrev HierarchySymbol.sigmaZero : HierarchySymbol :=
  Σ-[0]

/-- The Π₀ construction in `Π₀`. -/
abbrev HierarchySymbol.piZero : HierarchySymbol :=
  Π-[0]

/-- The ∆₀ construction in `∆₀`. -/
abbrev HierarchySymbol.deltaZero : HierarchySymbol :=
  ∆-[0]

/-- The Σ₁ construction in `Σ₁`. -/
abbrev HierarchySymbol.sigmaOne : HierarchySymbol :=
  Σ-[1]

/-- The Π₁ construction in `Π₁`. -/
abbrev HierarchySymbol.piOne : HierarchySymbol :=
  Π-[1]

/-- The ∆₁ construction in `∆₁`. -/
abbrev HierarchySymbol.deltaOne : HierarchySymbol :=
  ∆-[1]

/-- The «termΣ₀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "Σ₀" => HierarchySymbol.sigmaZero

/-- The «termΠ₀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "Π₀" => HierarchySymbol.piZero

/-- The «term∆₀» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "∆₀" => HierarchySymbol.deltaZero

/-- The «termΣ₁» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "Σ₁" => HierarchySymbol.sigmaOne

/-- The «termΠ₁» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "Π₁" => HierarchySymbol.piOne

/-- The «term∆₁» construction in `FFL.FirstOrder.Arithmetic`. -/
notation "∆₁" => HierarchySymbol.deltaOne

namespace HierarchySymbol

variable (ξ : Type*) (n : ℕ)

/-- First-order formulas with separate bound and free variables. -/
protected inductive Semiformula : HierarchySymbol → Type _ where
  |
  mkSigma {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy Σ m φ := by simp) :
    Σ-[m].Semiformula
  |
  mkPi {m} (φ : ArithmeticSemiformula ξ n) (hφ : Hierarchy Π m φ := by simp) : Π-[m].Semiformula
  | mkDelta {m} : Σ-[m].Semiformula → Π-[m].Semiformula → ∆-[m].Semiformula

/-- The Semisentence construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol`. -/
protected abbrev Semisentence (Γ : HierarchySymbol) (n : ℕ) :=
  Γ.Semiformula Empty n

/-- The Sentence construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol`. -/
protected abbrev Sentence (Γ : HierarchySymbol) :=
  Γ.Semiformula Empty 0

variable {Γ : HierarchySymbol}

variable {ξ n}

namespace Semiformula

/-- The val construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
@[coe]
def val {Γ : HierarchySymbol} : Γ.Semiformula ξ n → ArithmeticSemiformula ξ n
  | mkSigma φ _ => φ
  | mkPi φ _ => φ
  | mkDelta φ _ => φ.val

@[simp]
lemma val_mkSigma (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy Σ m φ) :
    (mkSigma φ hp).val = φ :=
  rfl

@[simp]
lemma val_mkPi (φ : ArithmeticSemiformula ξ n) (hp : Hierarchy Π m φ) : (mkPi φ hp).val = φ :=
  rfl

@[simp]
lemma val_mkDelta (φ : Σ-[m].Semiformula ξ n) (ψ : Π-[m].Semiformula ξ n) :
    (mkDelta φ ψ).val = φ.val :=
  rfl

instance : Coe (Σ₀.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩

instance : Coe (Π₀.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩

instance : Coe (∆₀.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩

instance : Coe (Σ₁.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩

instance : Coe (Π₁.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩

instance : Coe (∆₁.Semisentence n) (ArithmeticSemisentence n) :=
  ⟨Semiformula.val⟩

lemma sigma_prop : (φ : Σ-[m].Semiformula ξ n) → Hierarchy Σ m φ.val
  | mkSigma _ h => h

lemma pi_prop : (φ : Π-[m].Semiformula ξ n) → Hierarchy Π m φ.val
  | mkPi _ h => h

@[simp]
lemma polarity_prop : {Γ : Polarity} → (φ : Γ-[m].Semiformula ξ n) → Hierarchy Γ m φ.val
  | Σ, φ => φ.sigma_prop
  | Π, φ => φ.pi_prop

/-- The sigma construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def sigma : ∆-[m].Semiformula ξ n → Σ-[m].Semiformula ξ n
  | mkDelta φ _ => φ

@[simp]
lemma sigma_mkDelta (φ : Σ-[m].Semiformula ξ n) (ψ : Π-[m].Semiformula ξ n) :
    (mkDelta φ ψ).sigma = φ :=
  rfl

/-- The pi construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def pi : ∆-[m].Semiformula ξ n → Π-[m].Semiformula ξ n
  | mkDelta _ φ => φ

@[simp]
lemma pi_mkDelta (φ : Σ-[m].Semiformula ξ n) (ψ : Π-[m].Semiformula ξ n) :
    (mkDelta φ ψ).pi = ψ :=
  rfl

lemma val_sigma (φ : ∆-[m].Semiformula ξ n) : φ.sigma.val = φ.val := by rcases φ; simp

/-- The mk Polarity construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def mkPolarity (φ : ArithmeticSemiformula ξ n) :
    (Γ : Polarity) → Hierarchy Γ m φ → Γ-[m].Semiformula ξ n
  | Σ, h => mkSigma φ h
  | Π, h => mkPi φ h

@[simp]
lemma val_mkPolarity (φ : ArithmeticSemiformula ξ n) {Γ} (h : Hierarchy Γ m φ) :
    (mkPolarity φ Γ h).val = φ := by cases Γ <;> rfl

@[simp]
lemma hierarchy_sigma (φ : Σ-[m].Semiformula ξ n) : Hierarchy Σ m φ.val :=
  φ.sigma_prop

@[simp]
lemma hierarchy_pi (φ : Π-[m].Semiformula ξ n) : Hierarchy Π m φ.val :=
  φ.pi_prop

@[simp]
lemma hierarchy_zero {Γ Γ' m} (φ : Γ-[0].Semiformula ξ n) : Hierarchy Γ' m φ.val :=
  by
  cases Γ
  · exact Hierarchy.of_zero φ.sigma_prop
  · exact Hierarchy.of_zero φ.pi_prop
  · cases φ
    simpa using Hierarchy.of_zero (sigma_prop _)

variable {M : Type*} [ORingStructure M]

variable (M)

/-- The Proper On construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def ProperOn (φ : ∆-[m].Semisentence n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e

/-- The Proper With Param On construction in
`FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def ProperWithParamOn (φ : ∆-[m].Semiformula M n) : Prop :=
  ∀ (e : Fin n → M), φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id

/-- The Provably Proper On construction in
`FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def ProvablyProperOn (φ : ∆-[m].Semisentence n) (T : ArithmeticTheory) : Prop :=
  T ⊢ ∀¹* (“!φ.sigma.val⋯ ↔ !φ.pi.val⋯”)

variable {M}

lemma ProperOn.iff {φ : ∆-[m].Semisentence n} (h : φ.ProperOn M) (e : Fin n → M) :
    φ.sigma.val.Evalb e ↔ φ.pi.val.Evalb e :=
  h e

lemma ProperWithParamOn.iff {φ : ∆-[m].Semiformula M n} (h : φ.ProperWithParamOn M)
    (e : Fin n → M) : φ.sigma.val.Eval e id ↔ φ.pi.val.Eval e id :=
  h e

lemma ProperOn.iff' {φ : ∆-[m].Semisentence n} (h : φ.ProperOn M) (e : Fin n → M) :
    φ.pi.val.Evalb e ↔ φ.val.Evalb e := by simp [← h.iff, val_sigma]

lemma ProperWithParamOn.iff' {φ : ∆-[m].Semiformula M n} (h : φ.ProperWithParamOn M)
    (e : Fin n → M) : φ.pi.val.Eval e id ↔ φ.val.Eval e id := by simp [← h.iff, val_sigma]

/-- Data and laws for Provably Proper On' in
`FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
inductive ProvablyProperOn' (T : ArithmeticTheory) :
    {Γ : HierarchySymbol} → {n : ℕ} → (φ : Γ.Semisentence n) → Prop
  | sigma (φ : Σ-[m].Semisentence n) : φ.ProvablyProperOn' T
  | pi (φ : Π-[m].Semisentence n) : φ.ProvablyProperOn' T
  | delta (φ : ∆-[m].Semisentence n) : φ.ProvablyProperOn T → φ.ProvablyProperOn' T

section ProvablyProperOn

variable (T : ArithmeticTheory)

lemma ProvablyProperOn.ofProperOn [𝐄𝐐 ℒₒᵣ ≼ T] {φ : ∆-[m].Semisentence n}
    (h : ∀ (M : Type w) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T], φ.ProperOn M) :
    φ.ProvablyProperOn T :=
  by
  apply FirstOrder.Arithmetic.complete.{w} T _ ?_
  intro M _ _
  simpa [models_iff] using! (h M).iff

variable {T}

lemma ProvablyProperOn.properOn {φ : ∆-[m].Semisentence n} (h : φ.ProvablyProperOn T)
    (M : Type w) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] : φ.ProperOn M :=
  by
  intro v
  have := by simpa [models_iff] using consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  exact this v

end ProvablyProperOn

/-- The rew construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ₁ n₁ → Γ.Semiformula ξ₂ n₂
  | Σ-[_], mkSigma φ hp => mkSigma (ω ▹ φ) (by simpa using hp)
  | Π-[_], mkPi φ hp => mkPi (ω ▹ φ) (by simpa using hp)
  | ∆-[_], mkDelta φ ψ => mkDelta (φ.rew ω) (ψ.rew ω)

@[simp]
lemma val_rew (ω : Rew ℒₒᵣ ξ₁ n₁ ξ₂ n₂) {Γ : HierarchySymbol} (φ : Γ.Semiformula ξ₁ n₁) :
    (φ.rew ω).val = ω ▹ φ.val := by
  rcases Γ with ⟨Γ, m⟩;
  rcases φ with (_ | _ | ⟨⟨p, _⟩, ⟨q, _⟩⟩) <;> simp [rew]

@[simp]
lemma ProperOn.rew {φ : ∆-[m].Semisentence n₁} (h : φ.ProperOn M)
    (ω : Rew ℒₒᵣ Empty n₁ Empty n₂) : (φ.rew ω).ProperOn M :=
  by
  rcases φ;
  simp only [ProperOn, Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew,
    Empty.eq_elim, pi_mkDelta]
  intro e; exact h.iff _

@[simp]
lemma ProperOn.rew' {φ : ∆-[m].Semisentence n₁} (h : φ.ProperOn M) (ω : Rew ℒₒᵣ Empty n₁ M n₂) :
    (φ.rew ω).ProperWithParamOn M := by
  rcases φ; intro e; simp [Semiformula.rew, Semiformula.eval_rew, Empty.eq_elim]
  simpa using h.iff _

@[simp]
lemma ProperWithParamOn.rew {φ : ∆-[m].Semiformula M n₁} (h : φ.ProperWithParamOn M)
    (f : Fin n₁ → ArithmeticSemiterm M n₂) : (φ.rew (Rew.subst f)).ProperWithParamOn M :=
  by
  rcases φ; intro e;
  simp only [Semiformula.rew, sigma_mkDelta, val_rew, Semiformula.eval_rew, pi_mkDelta]
  exact h.iff _

lemma sigmaZero {Γ} (φ : Γ-[0].Semiformula ξ k) : Hierarchy Σ 0 φ.val :=
  match Γ with
  | Σ => φ.sigma_prop
  | Π => φ.pi_prop.of_zero
  | ∆ => by simp

/-- The of Zero construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def ofZero {Γ'} (φ : Γ'-[0].Semiformula ξ k) : (Γ : HierarchySymbol) → Γ.Semiformula ξ k
  | Σ-[_] => mkSigma φ.val φ.sigmaZero.of_zero
  | Π-[_] => mkPi φ.val φ.sigmaZero.of_zero
  | ∆-[_] => mkDelta (mkSigma φ.val φ.sigmaZero.of_zero) (mkPi φ.val φ.sigmaZero.of_zero)

/-- The of Delta One construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def ofDeltaOne (φ : ∆₁.Semiformula ξ k) :
    (Γ : SigmaPiDelta) → (m : ℕ) → Γ-[m + 1].Semiformula ξ k
  | Σ, m => mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp))
  | Π, m => mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp))
  | ∆, m =>
    mkDelta (mkSigma φ.sigma.val (φ.sigma.sigma_prop.mono (by simp)))
      (mkPi φ.pi.val (φ.pi.pi_prop.mono (by simp)))

@[simp]
lemma ofZero_val {Γ'} (φ : Γ'-[0].Semiformula ξ n) (Γ) : (ofZero φ Γ).val = φ.val := by
  match Γ with
  | Σ-[_] => simp [ofZero]
  | Π-[_] => simp [ofZero]
  | ∆-[_] => simp [ofZero]

@[simp]
lemma ProperOn.of_zero (φ : Γ'-[0].Semisentence k) (m) : (ofZero φ ∆-[m]).ProperOn M := by
  simp [ProperOn, ofZero]

@[simp]
lemma ProperWithParamOn.of_zero (φ : Γ'-[0].Semiformula M k) (m) :
    (ofZero φ ∆-[m]).ProperWithParamOn M := by simp [ProperWithParamOn, ofZero]

/-- The verum construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def verum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | Σ-[m] => mkSigma ⊤ (by simp)
  | Π-[m] => mkPi ⊤ (by simp)
  | ∆-[m] => mkDelta (mkSigma ⊤ (by simp)) (mkPi ⊤ (by simp))

/-- The falsum construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def falsum : {Γ : HierarchySymbol} → Γ.Semiformula ξ n
  | Σ-[m] => mkSigma ⊥ (by simp)
  | Π-[m] => mkPi ⊥ (by simp)
  | ∆-[m] => mkDelta (mkSigma ⊥ (by simp)) (mkPi ⊥ (by simp))

/-- The and construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def and : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | Σ-[m], φ, ψ => mkSigma (φ.val ⋏ ψ.val) (by simp)
  | Π-[m], φ, ψ => mkPi (φ.val ⋏ ψ.val) (by simp)
  | ∆-[m], φ, ψ =>
    mkDelta (mkSigma (φ.sigma.val ⋏ ψ.sigma.val) (by simp))
      (mkPi (φ.pi.val ⋏ ψ.pi.val) (by simp))

/-- The or construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def or : {Γ : HierarchySymbol} → Γ.Semiformula ξ n → Γ.Semiformula ξ n → Γ.Semiformula ξ n
  | Σ-[m], φ, ψ => mkSigma (φ.val ⋎ ψ.val) (by simp)
  | Π-[m], φ, ψ => mkPi (φ.val ⋎ ψ.val) (by simp)
  | ∆-[m], φ, ψ =>
    mkDelta (mkSigma (φ.sigma.val ⋎ ψ.sigma.val) (by simp))
      (mkPi (φ.pi.val ⋎ ψ.pi.val) (by simp))

/-- The neg Sigma construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def negSigma (φ : Σ-[m].Semiformula ξ n) : Π-[m].Semiformula ξ n :=
  mkPi (∼φ.val) (by simp)

/-- The neg Pi construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def negPi (φ : Π-[m].Semiformula ξ n) : Σ-[m].Semiformula ξ n :=
  mkSigma (∼φ.val) (by simp)

/-- The neg Delta construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def negDelta (φ : ∆-[m].Semiformula ξ n) : ∆-[m].Semiformula ξ n :=
  mkDelta (φ.pi.negPi) (φ.sigma.negSigma)

/-- The ball construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def ball (t : ArithmeticSemiterm ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | Σ-[m], φ => mkSigma (∀¹[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | Π-[m], φ => mkPi (∀¹[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | ∆-[m], φ =>
    mkDelta (mkSigma (∀¹[“#0 < !!(Rew.bShift t)”] φ.sigma.val) (by simp))
      (mkPi (∀¹[“#0 < !!(Rew.bShift t)”] φ.pi.val) (by simp))

/-- The bexs construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def bexs (t : ArithmeticSemiterm ξ n) :
    {Γ : HierarchySymbol} → Γ.Semiformula ξ (n + 1) → Γ.Semiformula ξ n
  | Σ-[m], φ => mkSigma (∃¹[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | Π-[m], φ => mkPi (∃¹[“#0 < !!(Rew.bShift t)”] φ.val) (by simp)
  | ∆-[m], φ =>
    mkDelta (mkSigma (∃¹[“#0 < !!(Rew.bShift t)”] φ.sigma.val) (by simp))
      (mkPi (∃¹[“#0 < !!(Rew.bShift t)”] φ.pi.val) (by simp))

/-- The all construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def all (φ : Π-[m + 1].Semiformula ξ (n + 1)) : Π-[m + 1].Semiformula ξ n :=
  mkPi (∀¹ φ.val) φ.pi_prop.all

/-- The exs construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def exs (φ : Σ-[m + 1].Semiformula ξ (n + 1)) : Σ-[m + 1].Semiformula ξ n :=
  mkSigma (∃¹ φ.val) φ.sigma_prop.exs

instance : Top (Γ.Semiformula ξ n) :=
  ⟨verum⟩

instance : Bot (Γ.Semiformula ξ n) :=
  ⟨falsum⟩

instance : Wedge (Γ.Semiformula ξ n) :=
  ⟨and⟩

instance : Vee (Γ.Semiformula ξ n) :=
  ⟨or⟩

instance : Tilde (∆-[m].Semiformula ξ n) :=
  ⟨negDelta⟩

instance : LogicalConnective (∆-[m].Semiformula ξ n) where arrow φ ψ := ∼φ ⋎ ψ

instance : ExsQuantifier (Σ-[m + 1].Semiformula ξ) :=
  ⟨exs⟩

instance : UnivQuantifier (Π-[m + 1].Semiformula ξ) :=
  ⟨all⟩

/-- The subst Sigma construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def substSigma (φ : Σ-[m + 1].Semiformula ξ 1) (F : Σ-[m + 1].Semiformula ξ (n + 1)) :
    Σ-[m + 1].Semiformula ξ n :=
  (F ⋏ φ.rew (Rew.subst ![#0])).exs

@[simp]
lemma val_verum : (⊤ : Γ.Semiformula ξ n).val = ⊤ := by rcases Γ with ⟨Γ, m⟩; cases Γ <;> rfl

@[simp]
lemma sigma_verum {m} : (⊤ : ∆-[m].Semiformula ξ n).sigma = ⊤ := by simp [Top.top, verum]

@[simp]
lemma pi_verum {m} : (⊤ : ∆-[m].Semiformula ξ n).pi = ⊤ := by simp [Top.top, verum]

@[simp]
lemma val_falsum : (⊥ : Γ.Semiformula ξ n).val = ⊥ := by rcases Γ with ⟨Γ, m⟩; cases Γ <;> rfl

@[simp]
lemma sigma_falsum {m} : (⊥ : ∆-[m].Semiformula ξ n).sigma = ⊥ := by simp [Bot.bot, falsum]

@[simp]
lemma pi_falsum {m} : (⊥ : ∆-[m].Semiformula ξ n).pi = ⊥ := by simp [Bot.bot, falsum]

@[simp]
lemma val_and (φ ψ : Γ.Semiformula ξ n) : (φ ⋏ ψ).val = φ.val ⋏ ψ.val :=
  by
  suffices (φ.and ψ).val = φ.val ⋏ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [and, val, val_sigma]

@[simp]
lemma sigma_and (φ ψ : ∆-[m].Semiformula ξ n) : (φ ⋏ ψ).sigma = φ.sigma ⋏ ψ.sigma :=
  rfl

@[simp]
lemma pi_and (φ ψ : ∆-[m].Semiformula ξ n) : (φ ⋏ ψ).pi = φ.pi ⋏ ψ.pi :=
  rfl

@[simp]
lemma val_or (φ ψ : Γ.Semiformula ξ n) : (φ ⋎ ψ).val = φ.val ⋎ ψ.val :=
  by
  suffices (φ.or ψ).val = φ.val ⋎ ψ.val from this
  rcases Γ with ⟨Γ, m⟩; rcases Γ <;> simp [or, val, val_sigma]

@[simp]
lemma sigma_or (φ ψ : ∆-[m].Semiformula ξ n) : (φ ⋎ ψ).sigma = φ.sigma ⋎ ψ.sigma :=
  rfl

@[simp]
lemma pi_or (φ ψ : ∆-[m].Semiformula ξ n) : (φ ⋎ ψ).pi = φ.pi ⋎ ψ.pi :=
  rfl

@[simp]
lemma val_negSigma {m} (φ : Σ-[m].Semiformula ξ n) : φ.negSigma.val = ∼φ.val := by
  simp [negSigma]

@[simp]
lemma val_negPi {m} (φ : Π-[m].Semiformula ξ n) : φ.negPi.val = ∼φ.val := by simp [negPi]

lemma val_negDelta {m} (φ : ∆-[m].Semiformula ξ n) : (∼φ).val = ∼φ.pi.val := by
  simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp]
lemma sigma_negDelta {m} (φ : ∆-[m].Semiformula ξ n) : (∼φ).sigma = φ.pi.negPi := by
  simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp]
lemma sigma_negPi {m} (φ : ∆-[m].Semiformula ξ n) : (∼φ).pi = φ.sigma.negSigma := by
  simp [HTilde.hTilde, Tilde.tilde, negDelta]

@[simp]
lemma val_ball (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (ball t φ).val = ∀¹[“#0 < !!(Rew.bShift t)”] φ.val := by
  rcases Γ with ⟨Γ, m⟩;
  rcases Γ <;> simp [ball, val, val_sigma]

@[simp]
lemma val_bexs (t : ArithmeticSemiterm ξ n) (φ : Γ.Semiformula ξ (n + 1)) :
    (bexs t φ).val = ∃¹[“#0 < !!(Rew.bShift t)”] φ.val := by
  rcases Γ with ⟨Γ, m⟩;
  rcases Γ <;> simp [bexs, val, val_sigma]

@[simp]
lemma val_exsSigma {m} (φ : Σ-[m + 1].Semiformula ξ (n + 1)) : (exs φ).val = ∃¹ φ.val :=
  rfl

@[simp]
lemma val_allPi {m} (φ : Π-[m + 1].Semiformula ξ (n + 1)) : (all φ).val = ∀¹ φ.val :=
  rfl

@[simp]
lemma ProperOn.verum : (⊤ : ∆-[m].Semisentence k).ProperOn M := by intro e; simp

@[simp]
lemma ProperOn.falsum : (⊥ : ∆-[m].Semisentence k).ProperOn M := by intro e; simp

lemma ProperOn.and {φ ψ : ∆-[m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) :
    (φ ⋏ ψ).ProperOn M := by intro e; simp [hp.iff, hq.iff]

lemma ProperOn.or {φ ψ : ∆-[m].Semisentence k} (hp : φ.ProperOn M) (hq : ψ.ProperOn M) :
    (φ ⋎ ψ).ProperOn M := by intro e; simp [hp.iff, hq.iff]

lemma ProperOn.neg {φ : ∆-[m].Semisentence k} (hp : φ.ProperOn M) : (∼φ).ProperOn M := by
  intro e; simp [hp.iff]

lemma ProperOn.eval_neg {φ : ∆-[m].Semisentence k} (hp : φ.ProperOn M) (e : Fin k → M) :
    (∼φ).val.Evalb e ↔ ¬φ.val.Evalb e := by simp [← val_sigma, hp.iff]

lemma ProperOn.ball {t} {φ : ∆-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) :
    (ball t φ).ProperOn M := by intro e; simp [Semiformula.ball, hp.iff]

lemma ProperOn.bexs {t} {φ : ∆-[m + 1].Semisentence (k + 1)} (hp : φ.ProperOn M) :
    (bexs t φ).ProperOn M := by intro e; simp [Semiformula.bexs, hp.iff]

@[simp]
lemma ProperWithParamOn.verum : (⊤ : ∆-[m].Semiformula M k).ProperWithParamOn M := by
  intro e;
  simp

@[simp]
lemma ProperWithParamOn.falsum : (⊥ : ∆-[m].Semiformula M k).ProperWithParamOn M := by
  intro e;
  simp

lemma ProperWithParamOn.and {φ ψ : ∆-[m].Semiformula M k} (hp : φ.ProperWithParamOn M)
    (hq : ψ.ProperWithParamOn M) : (φ ⋏ ψ).ProperWithParamOn M := by
  intro e;
  simp [hp.iff, hq.iff]

lemma ProperWithParamOn.or {φ ψ : ∆-[m].Semiformula M k} (hp : φ.ProperWithParamOn M)
    (hq : ψ.ProperWithParamOn M) : (φ ⋎ ψ).ProperWithParamOn M := by
  intro e;
  simp [hp.iff, hq.iff]

lemma ProperWithParamOn.neg {φ : ∆-[m].Semiformula M k} (hp : φ.ProperWithParamOn M) :
    (∼φ).ProperWithParamOn M := by intro e; simp [hp.iff]

lemma ProperWithParamOn.eval_neg {φ : ∆-[m].Semiformula M k} (hp : φ.ProperWithParamOn M)
    (e : Fin k → M) : (∼φ).val.Eval e id ↔ ¬φ.val.Eval e id := by simp [← val_sigma, hp.iff]

lemma ProperWithParamOn.ball {t} {φ : ∆-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (ball t φ).ProperWithParamOn M := by
  intro e;
  simp [Semiformula.ball, hp.iff]

lemma ProperWithParamOn.bexs {t} {φ : ∆-[m].Semiformula M (k + 1)}
    (hp : φ.ProperWithParamOn M) : (bexs t φ).ProperWithParamOn M := by
  intro e;
  simp [Semiformula.bexs, hp.iff]

/-- The graph Delta construction in `FFL.FirstOrder.Arithmetic.HierarchySymbol.Semiformula`. -/
def graphDelta (φ : Σ-[m].Semiformula ξ (k + 1)) : ∆-[m].Semiformula ξ (k + 1) :=
  match m with
  | 0 => φ.ofZero _
  | m + 1 => mkDelta φ (mkPi (“x. ∀ y, !φ.val y⋯ → y = x”))

@[simp]
lemma graphDelta_val (φ : Σ-[m].Semiformula ξ (k + 1)) : φ.graphDelta.val = φ.val := by
  cases m <;> simp [graphDelta]

end Semiformula

end HierarchySymbol

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
