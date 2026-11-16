/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Decide
public import LeanPool.DeciSigma1.Logic.Decide
public import LeanPool.DeciSigma1.Semantics.Classes
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Boolean sentences over `{⊥, f, ⊤}`

Terms over `{⊥, f, ⊤}` are built from variables, the constants `⊥` and `⊤` and the
constructor `f` of arity `n`, whose arguments have the variance `c : Fin n → Bool`. This module
instantiates the Boolean sentences of `DeciSigma1.Logic` with these terms, interpreted in trees
ordered by `Tree.Le c`, flattens clauses into the flat literals `Constraints.LitT`, and decides
the sentences over arbitrary, regular and finite trees with the procedures for disjunctive
entailment of `DeciSigma1.Full.Decide`. Over arbitrary and over regular trees every sentence
has the same truth value (`booleanSentence_regular_iff`); over finite trees it may differ.

## Main declarations

- `Term`, `Term.eval`: terms over `{⊥, f, ⊤}` and their values.
- `BooleanSentence`, `BooleanSentence.HoldsIn`: Boolean combinations of existential and
  universal sentences over `{⊥, f, ⊤}`, and their truth in a class of trees.
- `TermClosed`: classes of trees that contain `⊥` and `⊤` and are closed under `f`.
- `TreeClass`, `TreeClass.Contains`: arbitrary, regular or finite trees.
- `flattening`: flat literals that name subterms.
- `decideBooleanSentence`: the decision procedure.
- `booleanSentence_regular_iff`: truth over regular trees equals truth over arbitrary trees.
-/

@[expose] public section


namespace DeciSigma1.Full.Logic

open DeciSigma1.Constraints DeciSigma1.Semantics DeciSigma1.Full.Models

/-- Terms over `{⊥, f, ⊤}` with variables in `V`. -/
inductive Term (n : ℕ) (V : Type) where
  /-- A variable. -/
  | var (v : V)
  /-- The constant `⊥`. -/
  | bot
  /-- The constant `⊤`. -/
  | top
  /-- The constructor `f(t₀, …, t_{n-1})`. -/
  | node (t : Fin n → Term n V)

variable {n : ℕ} {V W : Type}

namespace Term

/-- Decidable equality of terms, comparing the finitely many children of a constructor. -/
def decEq [DecidableEq V] : (s t : Term n V) → Decidable (s = t)
  | .var v, .var w => decidable_of_iff (v = w) (by simp)
  | .top, .top => isTrue rfl
  | .bot, .bot => isTrue rfl
  | .node a, .node b =>
    letI (i : Fin n) : Decidable (a i = b i) := decEq (a i) (b i)
    decidable_of_iff (∀ i, a i = b i) (by simp [funext_iff])
  | .top, .var _ | .top, .bot | .top, .node _ |
    .var _, .top | .bot, .top | .node _, .top |
    .var _, .bot | .var _, .node _ | .bot, .var _ | .bot, .node _ |
    .node _, .var _ | .node _, .bot => isFalse (by intro h; cases h)

instance [DecidableEq V] : DecidableEq (Term n V) := decEq

/-- The value of a term when its variables have the values `ρ`. -/
def eval (ρ : V → Tree n) : Term n V → Tree n
  | .var v => ρ v
  | .bot => Tree.bot
  | .top => Tree.top
  | .node t => Semantics.Tree.node fun i => (t i).eval ρ

/-- The subterms of a term, including the term itself. -/
def subterms : Term n V → List (Term n V)
  | .var v => [.var v]
  | .bot => [.bot]
  | .top => [.top]
  | .node a => .node a :: (List.finRange n).flatMap fun i => (a i).subterms

theorem mem_subterms (t : Term n V) : t ∈ t.subterms := by
  cases t <;> simp [subterms]

theorem mem_subterms_node {a : Fin n → Term n V} {s : Term n V} (i : Fin n)
    (hs : s ∈ (a i).subterms) : s ∈ (node a).subterms := by
  simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and]
  exact Or.inr ⟨i, hs⟩

theorem subterms_trans {s t u : Term n V} (hs : s ∈ t.subterms) (hu : u ∈ s.subterms) :
    u ∈ t.subterms := by
  induction t with
  | var v => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | bot => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | top => simp only [subterms, List.mem_singleton] at hs; exact hs ▸ hu
  | node a ih =>
    simp only [subterms, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hs
    rcases hs with rfl | ⟨i, hi⟩
    · exact hu
    · exact mem_subterms_node i (ih i hi)

/-- Flat literals defining `name t`: `name t = var v` for a variable, `name t = ⊥`,
`name t = ⊤`, and `name t = f(name t₀, …, name t_{n-1})`. -/
def defs (var : V → W) (name : Term n V → W) (t : Term n V) : List (LitT n W) :=
  match t with
  | .var v => [.le (name t) (var v), .le (var v) (name t)]
  | .bot => [.eqBot (name t)]
  | .top => [.eqTop (name t)]
  | .node a => [.fLe (fun i => name (a i)) (name t), .leF (name t) (fun i => name (a i))]

variable (c : Fin n → Bool)

theorem holds_defs (var : V → W) (name : Term n V → W) (σ : W → Tree n) (t : Term n V)
    (h : ∀ s ∈ t.subterms, σ (name s) = s.eval (σ ∘ var)) :
    ∀ l ∈ defs var name t, HoldsT c σ l := by
  have ht := h t t.mem_subterms
  cases t with
  | var v => simp_all [defs, HoldsT, eval, treeLe_refl]
  | bot => simp_all [defs, HoldsT, eval]
  | top => simp_all [defs, HoldsT, eval]
  | node a =>
    have hc : (fun i => σ (name (a i))) = fun i => (a i).eval (σ ∘ var) :=
      funext fun i => h (a i) (mem_subterms_node i (a i).mem_subterms)
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      HoldsT, Function.comp_def, hc, ht, eval]
    exact ⟨treeLe_refl c _, treeLe_refl c _⟩

theorem eval_of_holds_defs (var : V → W) (name : Term n V → W) (σ : W → Tree n)
    (t : Term n V) (h : ∀ s ∈ t.subterms, ∀ l ∈ defs var name s, HoldsT c σ l) :
    σ (name t) = t.eval (σ ∘ var) := by
  have ht := h t t.mem_subterms
  induction t with
  | var v =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      HoldsT] at ht
    exact treeLe_antisymm ht.1 ht.2
  | bot => simpa [defs, HoldsT, eval] using ht
  | top => simpa [defs, HoldsT, eval] using ht
  | node a ih =>
    simp only [defs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      HoldsT] at ht
    rw [treeLe_antisymm ht.2 ht.1]
    simp only [eval]
    congr 1
    funext i
    exact ih i (fun s hs => h s (mem_subterms_node i hs))
      (h _ (mem_subterms_node i (a i).mem_subterms))

end Term

variable (c : Fin n → Bool)

/-- Terms over `{⊥, f, ⊤}` denote trees, ordered by `Tree.Le c`. -/
def interpretation : DeciSigma1.Logic.Interpretation (Term n) (Tree n) where
  eval ρ t := t.eval ρ
  le := Tree.Le c

/-- Boolean combinations of existential and universal sentences over `{⊥, f, ⊤}`. -/
abbrev BooleanSentence (n : ℕ) : Type := DeciSigma1.Logic.BooleanSentence (Term n)

/-- Truth of a sentence over `{⊥, f, ⊤}` with variance `c` when the variables range over the
class `C`. -/
abbrev BooleanSentence.HoldsIn (C : Tree n → Prop) (c : Fin n → Bool) (φ : BooleanSentence n) :
    Prop :=
  DeciSigma1.Logic.BooleanSentence.HoldsIn (interpretation c) C φ

/-- An equation holds exactly when both sides have the same value. -/
theorem holds_eq_iff (ρ : V → Tree n) (s t : Term n V) :
    (DeciSigma1.Logic.QuantifierFreeFormula.eq s t).Holds (interpretation c) ρ ↔
      s.eval ρ = t.eval ρ := by
  change Tree.Le c (s.eval ρ) (t.eval ρ) ∧ Tree.Le c (t.eval ρ) (s.eval ρ) ↔ _
  exact ⟨fun h => treeLe_antisymm h.1 h.2, fun h => h ▸ ⟨treeLe_refl c _, treeLe_refl c _⟩⟩

/-- The flat literals `Constraints.LitT` name the subterms of terms over `{⊥, f, ⊤}`. -/
def flattening : DeciSigma1.Logic.Flattening (interpretation (n := n) c) where
  Lit := LitT n
  Holds σ l := HoldsT c σ l
  leLit := .le
  holds_leLit _ _ _ := Iff.rfl
  subterms := Term.subterms
  mem_subterms := Term.mem_subterms
  subterms_trans := Term.subterms_trans
  bot := .bot
  defs := Term.defs
  holds_defs := Term.holds_defs c
  eval_of_holds_defs := Term.eval_of_holds_defs c

/-! ## Tree classes -/

/-- A class of trees that contains `⊥` and `⊤` and is closed under the constructor. -/
structure TermClosed (C : Tree n → Prop) : Prop where
  bot : C Tree.bot
  top : C Tree.top
  node : ∀ a : Fin n → Tree n, (∀ i, C (a i)) → C (Semantics.Tree.node a)

/-- A class closed under the constants and the constructor contains the value of every term
whose variables take values in it. -/
theorem TermClosed.eval {C : Tree n → Prop} (hC : TermClosed C) :
    (interpretation c).TermClosed C := by
  intro V ρ t hρ
  induction t with
  | var v => exact hρ v
  | bot => exact hC.bot
  | top => exact hC.top
  | node a ih => exact hC.node _ ih

theorem termClosed_all : TermClosed fun _ : Tree n => True :=
  ⟨trivial, trivial, fun _ _ => trivial⟩

theorem termClosed_fin : TermClosed (@FiniteTop n) := by
  refine ⟨⟨.bot, rfl⟩, ⟨.top, rfl⟩, fun a ha => ?_⟩
  choose b hb using ha
  exact ⟨.node b, by simp [hb]⟩

theorem regularTop_of_finiteTop {t : Tree n} (ht : FiniteTop t) : RegularTop t := by
  obtain ⟨s, rfl⟩ := ht
  exact Characterization.subtrees_finite_of_dom_finite _ (Characterization.dom_toTree_finite s)

theorem regularTop_node (a : Fin n → Tree n) (ha : ∀ i, RegularTop (a i)) :
    RegularTop (Semantics.Tree.node a) := by
  change (Characterization.subtrees (Semantics.Tree.node a)).Finite
  apply ((Set.finite_singleton (Semantics.Tree.node a)).union
    (Set.finite_iUnion ha)).subset
  rintro u ⟨w, hw⟩
  cases w with
  | nil =>
    left
    simpa only [Set.mem_singleton_iff, Characterization.subtree_nil, Option.some.injEq]
      using hw.symm
  | cons i w =>
    right
    refine Set.mem_iUnion.mpr ⟨i, w, ?_⟩
    have he : (Semantics.Tree.node a).subtree (i :: w) = (a i).subtree w := by
      simp only [Tree.subtree, Tree.node_fn_cons, List.cons_append]
      rfl
    exact he.symm.trans hw

theorem termClosed_reg : TermClosed (@RegularTop n) :=
  ⟨regularTop_of_finiteTop termClosed_fin.bot, regularTop_of_finiteTop termClosed_fin.top,
    regularTop_node⟩

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
def TreeClass.Contains : TreeClass → Tree n → Prop
  | .arbitrary => fun _ => True
  | .regular => RegularTop
  | .finite => FiniteTop

theorem TreeClass.termClosed : (C : TreeClass) → TermClosed (C.Contains (n := n))
  | .arbitrary => termClosed_all
  | .regular => termClosed_reg
  | .finite => termClosed_fin

/-! ## Decision procedures -/

/-- The procedures for disjunctive entailment over arbitrary, regular and finite trees. -/
@[instance_reducible] def disjEntailmentDecider :
    (C : TreeClass) → DeciSigma1.Logic.DisjEntailmentDecider (flattening c) C.Contains
  | .arbitrary => fun Γ q => decideDisjEntails c Γ q
  | .regular => fun Γ q => decideDisjEntailsReg c Γ q
  | .finite => fun Γ q => decideDisjEntailsFin c Γ q

/-- Boolean sentences over `{⊥, f, ⊤}` are decidable over arbitrary, regular and finite
trees. -/
def decideBooleanSentence (C : TreeClass) (φ : BooleanSentence n) :
    Decidable (φ.HoldsIn C.Contains c) :=
  DeciSigma1.Logic.decideBooleanSentence (flattening c) (C.termClosed.eval c)
    (disjEntailmentDecider c C) φ

/-- A sentence over `{⊥, f, ⊤}` has the same truth value over regular and over arbitrary
trees. -/
theorem booleanSentence_regular_iff (φ : BooleanSentence n) :
    φ.HoldsIn RegularTop c ↔ φ.HoldsIn (fun _ => True) c :=
  DeciSigma1.Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff (flattening c)
    (termClosed_reg.eval c) (termClosed_all.eval c)
    (fun Γ q => show (flattening c).DisjEntailsIn RegularTop Γ q ↔
      (flattening c).DisjEntailsIn (fun _ => True) Γ q from Reduction.disjEntails_regular_iff) φ

end DeciSigma1.Full.Logic
