/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.PeanoMinus

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D3}$ and formalized $\Sigma_1$-completeness
-/

namespace FFL
namespace FirstOrder
namespace Arithmetic
namespace Bootstrapping
namespace ObjectArithmetic



open FFL.Entailment FFL.Entailment.FiniteContext

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

local prefix:max "#'" => Semiterm.bvar (V := V) (L := ℒₒᵣ)

local prefix:max "&'" => Semiterm.fvar (V := V) (L := ℒₒᵣ)

local postfix:max "↑ᵗ" => Semiterm.shift

local postfix:max "↑ᶠ" => Semiformula.shift

local infix:40 " ↤ᵗ " => Semiterm.subst

local infix:40 " ↤ᶠ " => Semiformula.subst

variable (T : ArithmeticTheory) [Theory.Δ₁ T] [𝐏𝐀⁻ ≼ T]

variable {T}

lemma eq_comm {t₁ t₂ : Term V ℒₒᵣ} : T.internalize V ⊢ t₁ ≐ t₂ → T.internalize V ⊢ t₂ ≐ t₁ :=
  fun h ↦ eq_symm T _ _⨀h

/--
The to Num Vec construction in `FFL.FirstOrder.Arithmetic.Bootstrapping.ObjectArithmetic`. -/
noncomputable abbrev toNumVec (w : Fin n → V) : SemitermVec V ℒₒᵣ n k :=
  ((ℕᵗ·)↗ w)

variable (T)

theorem term_complete {n : ℕ} (t : FirstOrder.ClosedSemiterm ℒₒᵣ n) (w : Fin n → V) :
    T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t⌝) ≐ ℕᵗ(t.valb w) :=
  match t with
  | #z => by simp
  | &x => Empty.elim x
  | .func Language.Zero.zero v => by simp
  | .func Language.One.one v => by simp
  | .func Language.Add.add v =>
    by
    suffices
      T.internalize V ⊢
        (toNumVec w ↤ᵗ ⌜v 0⌝) + (toNumVec w ↤ᵗ ⌜v 1⌝) ≐ ℕᵗ((v 0).valb w + (v 1).valb w)
      by simpa [Rew.func, Semiterm.val_func]
    have ih :
      T.internalize V ⊢
        (toNumVec w ↤ᵗ ⌜v 0⌝) + (toNumVec w ↤ᵗ ⌜v 1⌝) ≐ ℕᵗ((v 0).valb w) + ℕᵗ((v 1).valb w) :=
      subst_add_eq_add T _ _ _ _⨀term_complete (v 0) w⨀term_complete (v 1) w
    have :
      T.internalize V ⊢ ℕᵗ((v 0).valb w) + ℕᵗ((v 1).valb w) ≐ ℕᵗ((v 0).valb w + (v 1).valb w) :=
      numeral_add T _ _
    exact eq_trans ih this
  | .func Language.Mul.mul v =>
    by
    suffices
      T.internalize V ⊢
        (toNumVec w ↤ᵗ ⌜v 0⌝) * (toNumVec w ↤ᵗ ⌜v 1⌝) ≐ ℕᵗ((v 0).valb w * (v 1).valb w)
      by simpa [Rew.func, Semiterm.val_func]
    have ih :
      T.internalize V ⊢
        (toNumVec w ↤ᵗ ⌜v 0⌝) * (toNumVec w ↤ᵗ ⌜v 1⌝) ≐ ℕᵗ((v 0).valb w) * ℕᵗ((v 1).valb w) :=
      subst_mul_eq_mul T _ _ _ _⨀term_complete (v 0) w⨀term_complete (v 1) w
    have :
      T.internalize V ⊢ ℕᵗ((v 0).valb w) * ℕᵗ((v 1).valb w) ≐ ℕᵗ((v 0).valb w * (v 1).valb w) :=
      numeral_mul T _ _
    exact eq_trans ih this

open FirstOrder.Arithmetic

theorem bold_sigma_one_complete {n} {φ : ArithmeticSemisentence n} (hp : Hierarchy Σ 1 φ) {w} :
    V ⊧/w φ → T.internalize V ⊢ (toNumVec w ↤ᶠ ⌜φ⌝) :=
  by
  revert w
  apply sigma₁_induction' hp
  case hVerum => intro n; simp
  case hFalsum => intro n; simp
  case hEQ =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) ≐ (toNumVec w ↤ᵗ ⌜t₂⌝) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valb w = t₂.valb w := by simpa using h
    have h₀ : T.internalize V ⊢ ℕᵗ(t₁.valb w) ≐ ℕᵗ(t₂.valb w) := by simp [this]
    have h₁ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) ≐ ℕᵗ(t₁.valb w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₂⌝) ≐ ℕᵗ(t₂.valb w) := term_complete T t₂ w
    exact eq_trans (eq_trans h₁ h₀) (eq_comm h₂)
  case hNEQ =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) ≉ (toNumVec w ↤ᵗ ⌜t₂⌝) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valb w ≠ t₂.valb w := by simpa using h
    have h₀ : T.internalize V ⊢ ℕᵗ(t₁.valb w) ≉ ℕᵗ(t₂.valb w) := by
      simpa using numeral_ne T this
    have h₁ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) ≐ ℕᵗ(t₁.valb w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₂⌝) ≐ ℕᵗ(t₂.valb w) := term_complete T t₂ w
    exact subst_ne T _ _ _ _⨀eq_comm h₁⨀eq_comm h₂⨀h₀
  case hLT =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) <' (toNumVec w ↤ᵗ ⌜t₂⌝) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valb w < t₂.valb w := by simpa using h
    have h₀ : T.internalize V ⊢ ℕᵗ(t₁.valb w) <' ℕᵗ(t₂.valb w) := by
      simpa using numeral_lt T this
    have h₁ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) ≐ ℕᵗ(t₁.valb w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₂⌝) ≐ ℕᵗ(t₂.valb w) := term_complete T t₂ w
    exact subst_lt T _ _ _ _⨀eq_comm h₁⨀eq_comm h₂⨀h₀
  case hNLT =>
    intro n t₁ t₂ w h
    suffices T.internalize V ⊢ ((toNumVec w ↤ᵗ ⌜t₁⌝) ≮' (toNumVec w ↤ᵗ ⌜t₂⌝)) by
      simpa [Sentence.typed_quote_def]
    have : t₁.valb w ≥ t₂.valb w := by simpa using h
    have h₀ : T.internalize V ⊢ ℕᵗ(t₁.valb w) ≮' ℕᵗ(t₂.valb w) := by
      simpa using numeral_nlt T this
    have h₁ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₁⌝) ≐ ℕᵗ(t₁.valb w) := term_complete T t₁ w
    have h₂ : T.internalize V ⊢ (toNumVec w ↤ᵗ ⌜t₂⌝) ≐ ℕᵗ(t₂.valb w) := term_complete T t₂ w
    exact subst_nlt T _ _ _ _⨀eq_comm h₁⨀eq_comm h₂⨀h₀
  case hAnd =>
    intro n φ ψ _ _ ihφ ihψ w h
    have H : V ⊧/w φ ∧ V ⊧/w ψ := by simpa using h
    simpa using K_intro (ihφ H.1) (ihψ H.2)
  case hOr =>
    intro n φ ψ _ _ ihφ ihψ w h
    suffices T.internalize V ⊢ (toNumVec w ↤ᶠ ⌜φ⌝) ⋎ (toNumVec w ↤ᶠ ⌜ψ⌝) by simpa
    have : V ⊧/w φ ∨ V ⊧/w ψ := by simpa using h
    rcases this with (h | h)
    · apply A_intro_left (ihφ h)
    · apply A_intro_right (ihψ h)
  case hBall =>
    intro n t φ _ ih w h
    have h : ∀ i < t.valb w, V ⊧/(i :> w) φ := by simpa using h
    suffices T.internalize V ⊢ ((toNumVec w).q ↤ᶠ ⌜φ⌝).ball (toNumVec w ↤ᵗ ⌜t⌝) by
      simpa [Semiterm.empty_typed_quote_def, ← Rew.emb_bShift_term, Semiformula.ball, ball,
        Semiformula.imp_def]
    have : T.internalize V ⊢ ((toNumVec w).q ↤ᶠ ⌜φ⌝).ball ℕᵗ(t.valb w) :=
      by
      apply ball_intro
      intro i hi
      suffices T.internalize V ⊢ (toNumVec (i :> w) ↤ᶠ ⌜φ⌝) by
        simpa [Semiformula.substs_substs, Matrix.vecMap_vecMap_comp']
      exact ih (h i hi)
    exact ball_replace T ((toNumVec w).q ↤ᶠ ⌜φ⌝) _ _⨀(eq_comm <| term_complete T t w)⨀this
  case hExs =>
    intro n φ hφ ih w hφ
    have : ∃ a, V ⊧/(a :> w) φ := by simpa using hφ
    rcases this with ⟨i, hφ⟩
    suffices T.internalize V ⊢ ∃¹ ((toNumVec w).q ↤ᶠ ⌜φ⌝) by simpa
    apply TProof.exsProof (ℕᵗi)
    suffices T.internalize V ⊢ (toNumVec (i :> w) ↤ᶠ ⌜φ⌝) by
      simpa [Semiformula.substs_substs, Matrix.vecMap_vecMap_comp']
    exact ih hφ

theorem sigma_one_provable_of_models {σ : ArithmeticSentence} (hσ : Hierarchy Σ 1 σ) :
    V↓[ℒₒᵣ] ⊧ σ → T.internalize V ⊢ ⌜σ⌝ := by
  intro h
  have : T.internalize V ⊢ (toNumVec ![] ↤ᶠ ⌜σ⌝) :=
    bold_sigma_one_complete T hσ (by simpa [models_iff] using h)
  simpa using this

/-- Hilbert–Bernays provability condition D3 -/
theorem sigma_one_complete {σ : ArithmeticSentence} (hσ : Hierarchy Σ 1 σ) :
    V↓[ℒₒᵣ] ⊧ σ → Provable T (⌜σ⌝ : V) := fun h ↦ by
  simpa [tprovable_iff_provable] using!
    Bootstrapping.ObjectArithmetic.sigma_one_provable_of_models T hσ h

theorem provable_internalize {σ : ArithmeticSentence} :
    Provable T (⌜σ⌝ : V) → Provable T (⌜provabilityPred T σ⌝ : V) := by
  simpa [models_iff] using
    sigma_one_complete (V := V) (T := T) (σ := provabilityPred T σ) (by simp)

end ObjectArithmetic
end Bootstrapping
end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
