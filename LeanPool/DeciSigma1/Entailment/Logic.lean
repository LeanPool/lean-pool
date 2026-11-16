/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Entailment.Decide
public import LeanPool.DeciSigma1.Logic.Decide
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Boolean sentences over `{⊥, f}`

Terms over `{⊥, f}` are built from variables, the constant `⊥` and the covariant constructor
`f` of arity `n`; they denote trees over `{⊥, f}`, ordered by inclusion of constructor
positions. This module instantiates the Boolean sentences of `DeciSigma1.Logic` with these
terms, flattens clauses into the flat literals `Constraints.TopFree.Lit`, and decides the
sentences over arbitrary, regular and finite trees with the procedures for disjunctive
entailment of `DeciSigma1.Entailment.Decide`. Since disjunctive entailment has the same truth
value over regular and over arbitrary trees, so has every sentence
(`booleanSentence_regular_iff`); over finite trees it may differ.

## Main declarations

- `BFTerm`, `BFTerm.eval`: terms over `{⊥, f}` and their values.
- `BooleanSentence`, `BooleanSentence.HoldsIn`: Boolean combinations of existential and
  universal sentences over `{⊥, f}`, and their truth in a class of trees.
- `BFTermClosed`: classes of trees that contain `⊥` and are closed under `f`.
- `TreeClass`, `TreeClass.Contains`: arbitrary, regular or finite trees.
- `flattening`: flat literals that name subterms.
- `decideBooleanSentence`: the decision procedure.
- `booleanSentence_regular_iff`: truth over regular trees equals truth over arbitrary trees.
-/

@[expose] public section


namespace DeciSigma1.Entailment.Logic

open DeciSigma1.Constraints.TopFree DeciSigma1.Semantics

/-- Terms over `{⊥, f}` with variables in `V`. -/
inductive BFTerm (n : ℕ) (V : Type) where
  /-- A variable. -/
  | var (v : V)
  /-- The constant `⊥`. -/
  | bot
  /-- The constructor `f(t₀, …, t_{n-1})`. -/
  | node (t : Fin n → BFTerm n V)

variable {n : ℕ} {V W : Type}

namespace BFTerm

/-- Decidable equality of terms, comparing the finitely many children of a constructor. -/
def decEq [DecidableEq V] : (s t : BFTerm n V) → Decidable (s = t)
  | .var v, .var w => decidable_of_iff (v = w) (by simp)
  | .bot, .bot => isTrue rfl
  | .node a, .node b =>
    letI (i : Fin n) : Decidable (a i = b i) := decEq (a i) (b i)
    decidable_of_iff (∀ i, a i = b i) (by simp [funext_iff])
  | .var _, .bot | .var _, .node _ | .bot, .var _ | .bot, .node _ |
    .node _, .var _ | .node _, .bot => isFalse (by intro h; cases h)

instance [DecidableEq V] : DecidableEq (BFTerm n V) := decEq

/-- The value of a term when its variables have the values `ρ`. -/
def eval (ρ : V → PrefixSet n) : BFTerm n V → PrefixSet n
  | .var v => ρ v
  | .bot => PrefixSet.bot
  | .node t => PrefixSet.node fun i => (t i).eval ρ

/-- The subterms of a term, including the term itself. -/
def subterms : BFTerm n V → List (BFTerm n V)
  | .var v => [.var v]
  | .bot => [.bot]
  | .node a => .node a :: (List.finRange n).flatMap fun i => (a i).subterms

theorem mem_subterms (t : BFTerm n V) : t ∈ t.subterms := by
  cases t <;> simp [subterms]

theorem mem_subterms_node {a : Fin n → BFTerm n V} {s : BFTerm n V} (i : Fin n)
    (hs : s ∈ (a i).subterms) : s ∈ (node a).subterms := by
  simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
  exact Or.inr ⟨i, hs⟩

theorem subterms_trans {s t u : BFTerm n V} (hs : s ∈ t.subterms) (hu : u ∈ s.subterms) :
    u ∈ t.subterms := by
  induction t with
  | var v => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | bot => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | node a ih =>
    simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hs
    rcases hs with rfl | ⟨i, hi⟩
    · exact hu
    · exact mem_subterms_node i (ih i hi)

/-- Flat literals defining `name t`: `name t = var v` for a variable, `name t = ⊥`, and
`name t = f(name t₀, …, name t_{n-1})`. -/
def defs (var : V → W) (name : BFTerm n V → W) (t : BFTerm n V) : List (Lit n W) :=
  match t with
  | .var v => [.le (name t) (var v), .le (var v) (name t)]
  | .bot => [.eqBot (name t)]
  | .node a => [.fLe (fun i => name (a i)) (name t), .leF (name t) (fun i => name (a i))]

theorem holds_defs (var : V → W) (name : BFTerm n V → W) (σ : W → PrefixSet n)
    (t : BFTerm n V) (h : ∀ s ∈ t.subterms, σ (name s) = s.eval (σ ∘ var)) :
    ∀ l ∈ defs var name t, l.Holds σ := by
  have ht := h t t.mem_subterms
  cases t with
  | var v => simp_all [defs, Lit.Holds, eval]
  | bot => simp_all [defs, Lit.Holds, eval]
  | node a =>
    have hc (i : Fin n) := h (a i) (mem_subterms_node i (a i).mem_subterms)
    simp_all [defs, Lit.Holds, eval, Function.comp_def]

theorem eval_of_holds_defs (var : V → W) (name : BFTerm n V → W) (σ : W → PrefixSet n)
    (t : BFTerm n V) (h : ∀ s ∈ t.subterms, ∀ l ∈ defs var name s, l.Holds σ) :
    σ (name t) = t.eval (σ ∘ var) := by
  have ht := h t t.mem_subterms
  induction t with
  | var v =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Lit.Holds] at ht
    exact le_antisymm ht.1 ht.2
  | bot => simpa [defs, Lit.Holds, eval] using ht
  | node a ih =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Lit.Holds] at ht
    rw [le_antisymm ht.2 ht.1]
    simp only [eval]
    congr 1
    funext i
    exact ih i (fun s hs => h s (mem_subterms_node i hs))
        (h _ (mem_subterms_node i (a i).mem_subterms))

end BFTerm

/-- Terms over `{⊥, f}` denote sets of constructor positions, ordered by inclusion. -/
def interpretation (n : ℕ) : DeciSigma1.Logic.Interpretation (BFTerm n) (PrefixSet n) where
  eval ρ t := t.eval ρ
  le := (· ≤ ·)

/-- Boolean combinations of existential and universal sentences over `{⊥, f}`. -/
abbrev BooleanSentence (n : ℕ) : Type := DeciSigma1.Logic.BooleanSentence (BFTerm n)

/-- Truth of a sentence over `{⊥, f}` when the variables range over the class `C`. -/
abbrev BooleanSentence.HoldsIn (C : PrefixSet n → Prop) (φ : BooleanSentence n) : Prop :=
  DeciSigma1.Logic.BooleanSentence.HoldsIn (interpretation n) C φ

/-- The flat literals `Constraints.TopFree.Lit` name the subterms of terms over `{⊥, f}`. -/
def flattening (n : ℕ) : DeciSigma1.Logic.Flattening (interpretation n) where
  Lit := Lit n
  Holds σ l := l.Holds σ
  leLit := .le
  holds_leLit _ _ _ := Iff.rfl
  subterms := BFTerm.subterms
  mem_subterms := BFTerm.mem_subterms
  subterms_trans := BFTerm.subterms_trans
  bot := .bot
  defs := BFTerm.defs
  holds_defs := BFTerm.holds_defs
  eval_of_holds_defs := BFTerm.eval_of_holds_defs

/-- A class of trees that contains `⊥` and is closed under the constructor. -/
structure BFTermClosed (C : PrefixSet n → Prop) : Prop where
  bot : C PrefixSet.bot
  node : ∀ a : Fin n → PrefixSet n, (∀ i, C (a i)) → C (PrefixSet.node a)

/-- A class closed under `⊥` and the constructor contains the value of every term whose
variables take values in it. -/
theorem BFTermClosed.eval {C : PrefixSet n → Prop} (hC : BFTermClosed C) :
    (interpretation n).TermClosed C := by
  intro V ρ t hρ
  induction t with
  | var v => exact hρ v
  | bot => exact hC.bot
  | node a ih => exact hC.node _ ih

theorem bfTermClosed_all : BFTermClosed fun _ : PrefixSet n => True :=
  ⟨trivial, fun _ _ => trivial⟩

theorem bfTermClosed_reg : BFTermClosed (@IsRegularTree n) :=
  ⟨isRegularTree_bot, isRegularTree_node⟩

theorem bfTermClosed_fin : BFTermClosed (@IsFiniteTree n) :=
  ⟨isFiniteTree_bot, isFiniteTree_node⟩

/-- The classes of trees over which the sentences are decided. -/
inductive TreeClass where
  /-- All trees. -/
  | arbitrary
  /-- The regular trees. -/
  | regular
  /-- The finite trees. -/
  | finite
  deriving DecidableEq

/-- The trees in a class. -/
def TreeClass.Contains : TreeClass → PrefixSet n → Prop
  | .arbitrary => fun _ => True
  | .regular => IsRegularTree
  | .finite => IsFiniteTree

theorem TreeClass.bfTermClosed : (C : TreeClass) → BFTermClosed (C.Contains (n := n))
  | .arbitrary => bfTermClosed_all
  | .regular => bfTermClosed_reg
  | .finite => bfTermClosed_fin

variable [Fintype V] [DecidableEq V]

/-- The procedures for disjunctive entailment over arbitrary, regular and finite trees. -/
@[instance_reducible] def disjEntailmentDecider :
    (C : TreeClass) → DeciSigma1.Logic.DisjEntailmentDecider (flattening n) C.Contains
  | .arbitrary => fun Γ q => decideDisjEntails Γ q
  | .regular => fun Γ q => decideDisjEntailsReg Γ q
  | .finite => fun Γ q => decideDisjEntailsFin Γ q

/-- Boolean sentences over `{⊥, f}` are decidable over arbitrary, regular and finite trees. -/
def decideBooleanSentence (C : TreeClass) (φ : BooleanSentence n) :
    Decidable (φ.HoldsIn C.Contains) :=
  DeciSigma1.Logic.decideBooleanSentence (flattening n) (C.bfTermClosed.eval)
    (disjEntailmentDecider C) φ

/-- A sentence over `{⊥, f}` has the same truth value over regular and over arbitrary
trees. -/
theorem booleanSentence_regular_iff (φ : BooleanSentence n) :
    φ.HoldsIn IsRegularTree ↔ φ.HoldsIn (fun _ => True) :=
  DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff (flattening n)
    bfTermClosed_reg.eval bfTermClosed_all.eval
    (fun Γ q => show (flattening n).DisjEntailsIn IsRegularTree Γ q ↔
      (flattening n).DisjEntailsIn (fun _ => True) Γ q from disjEntailsIn_regular_iff Γ q) φ

end DeciSigma1.Entailment.Logic
