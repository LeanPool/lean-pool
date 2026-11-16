/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Entailment.Basic
public import LeanPool.DeciSigma1.Entailment.Embedding
public import LeanPool.DeciSigma1.Full.Reduction.Transfer
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Data.Set.Finite.Basic

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Disjunctive entailment over `{⊥, f}` through `{⊥, f, ⊤}`

A constraint `Γ` over `{⊥, f}` is read over `{⊥, f, ⊤}` with a covariant constructor, together
with a guard that excludes `⊤`: a fresh variable `u` (the variable `none` of `Option V`) with
`u ≤ f(u, …, u)`, and `x ≤ u` for every variable `x` of `V`, including those that occur only in
the queries. In a solution of the guarded constraint no value contains `⊤`, so the values of all
variables are embedded trees over `{⊥, f}`. Conversely, a solution of `Γ` over `{⊥, f}` extends
to a solution of the guarded constraint by any tree `g ≤ f(g, …, g)` above its values: the tree
all of whose paths are labeled `f` over arbitrary and over regular trees, and over finite trees
a complete tree whose depth exceeds the length of every constructor position of the values.
Hence `Γ` entails a disjunction over `{⊥, f}` exactly when the guarded constraint entails it
over `{⊥, f, ⊤}`, over arbitrary, regular and finite trees, and the entailments over regular and
over arbitrary trees over `{⊥, f}` agree because those over `{⊥, f, ⊤}` do.

## Main declarations

- `Constraints.TopFree.Lit.toLitT`, `Constraints.TopFree.holdsT_toLitT`: a literal over `{⊥, f}`
  as a literal over `{⊥, f, ⊤}`; the embedding of trees preserves and reflects satisfaction.
- `Entailment.guarded`, `Entailment.guardedQueries`: the guarded constraint and its queries.
- `Entailment.disjEntailsIn_iff_guarded`, `Entailment.disjEntailsIn_regular_iff_guarded`,
  `Entailment.disjEntailsIn_finite_iff_guarded`: the reduction over arbitrary, regular and
  finite trees.
- `Entailment.disjEntailsIn_regular_iff`: regular and arbitrary disjunctive entailment agree.
-/

@[expose] public section


namespace DeciSigma1.Constraints.TopFree

open DeciSigma1.Semantics

variable {n : ℕ} {V : Type}

/-- A literal over `{⊥, f}` as a literal over `{⊥, f, ⊤}`. -/
def Lit.toLitT : Lit n V → LitT n V
  | .le u v => .le u v
  | .fLe a u => .fLe a u
  | .leF u a => .leF u a
  | .eqBot u => .eqBot u

/-- An assignment of trees over `{⊥, f}` satisfies a literal exactly when the embedded
assignment satisfies it over `{⊥, f, ⊤}` with a covariant constructor. -/
theorem holdsT_toLitT (ρ : V → PrefixSet n) (l : Lit n V) :
    HoldsT (fun _ => false) (fun v => (ρ v).toTree) l.toLitT ↔ l.Holds ρ := by
  have hn (a : Fin n → V) :
      Semantics.Tree.node ((fun v => (ρ v).toTree) ∘ a) = (PrefixSet.node (ρ ∘ a)).toTree :=
    (PrefixSet.toTree_node _).symm
  cases l with
  | le u v => exact (treeLe_false_iff_le _ _).trans (PrefixSet.toTree_le_toTree _ _)
  | fLe a u =>
    exact (treeLe_false_iff_le _ _).trans ((hn a).symm ▸ PrefixSet.toTree_le_toTree _ _)
  | leF u a =>
    exact (treeLe_false_iff_le _ _).trans ((hn a).symm ▸ PrefixSet.toTree_le_toTree _ _)
  | eqBot u => exact PrefixSet.toTree_eq_bot_iff _

end DeciSigma1.Constraints.TopFree

namespace DeciSigma1.Entailment

open DeciSigma1.Constraints DeciSigma1.Constraints.TopFree DeciSigma1.Semantics

variable {n k : ℕ} {V : Type}

/-- The guarded constraint over `{⊥, f, ⊤}`: the literals of `Γ`, the inequality
`u ≤ f(u, …, u)` for the fresh variable `u = none`, and `x ≤ u` for every `x` in `vs`. -/
def guarded (vs : List V) (Γ : List (Lit n V)) : List (LitT n (Option V)) :=
  .leF none (fun _ => none) ::
    (vs.map (fun v => .le (some v) none) ++ Γ.map (fun l => l.toLitT.map some))

/-- The queries of the guarded constraint. -/
def guardedQueries (q : Fin k → V × V) (i : Fin k) : Option V × Option V :=
  (some (q i).1, some (q i).2)

/-- An assignment satisfies the guarded constraint exactly when the value of the fresh
variable `u` satisfies `u ≤ f(u, …, u)`, the values of the variables in `vs` are below it, and the
literals of `Γ` hold. -/
theorem satT_guarded (vs : List V) (Γ : List (Lit n V)) (σ : Option V → Semantics.Tree n) :
    SatT (fun _ => false) σ (guarded vs Γ) ↔
      σ none ≤ Semantics.Tree.node (fun _ => σ none) ∧ (∀ v ∈ vs, σ (some v) ≤ σ none) ∧
        ∀ l ∈ Γ, HoldsT (fun _ => false) (σ ∘ some) l.toLitT := by
  constructor
  · intro h
    exact ⟨(treeLe_false_iff_le _ _).mp (h _ List.mem_cons_self),
      fun v hv => (treeLe_false_iff_le _ _).mp (h (.le (some v) none)
        (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hv)))),
      fun l hl => (holdsT_map _ _ _ _).mp
        (h _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_map_of_mem hl))))⟩
  · rintro ⟨hu, hle, hΓ⟩ l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact (treeLe_false_iff_le _ _).mpr hu
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hl
      exact (treeLe_false_iff_le _ _).mpr (hle v hv)
    · obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      exact (holdsT_map _ _ _ _).mpr (hΓ l' hl')

/-- Disjunctive entailment over `{⊥, f}` is the entailment of the guarded constraint over
`{⊥, f, ⊤}` with a covariant constructor, for corresponding classes of trees: a class `C` of
trees over `{⊥, f}` in which every assignment lies below a guard `g ≤ f(g, …, g)` of `C`, and a
class `D` whose trees without `⊤` are the embeddings of the trees in `C`. The list `vs`
contains every variable. -/
theorem disjEntailsIn_iff_guarded_of_classes {C : PrefixSet n → Prop}
    {D : Semantics.Tree n → Prop} (hD : ∀ P, D P.toTree ↔ C P)
    (hC : ∀ ρ : V → PrefixSet n, (∀ v, C (ρ v)) →
      ∃ g, C g ∧ g ≤ PrefixSet.node (fun _ => g) ∧ ∀ v, ρ v ≤ g)
    {vs : List V} (hvs : ∀ v, v ∈ vs) (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn C Γ q ↔
      Full.DisjEntailsIn D (fun _ => false) (guarded vs Γ) (guardedQueries q) := by
  constructor
  · intro h σ hσ hsat
    obtain ⟨hu, hle, hΓ⟩ := (satT_guarded vs Γ σ).mp hsat
    have ht (v : V) : (σ (some v)).positions.toTree = σ (some v) :=
      Tree.toTree_positions (Tree.isTopFree_of_le_of_le_node hu (hle v (hvs v)))
    have he : (fun v => (σ (some v)).positions.toTree) = σ ∘ some := funext ht
    obtain ⟨i, hi⟩ := h (fun v => (σ (some v)).positions)
      (fun v => (hD _).mp (by rw [ht]; exact hσ (some v)))
      (fun l hl => (holdsT_toLitT _ l).mp (by rw [he]; exact hΓ l hl))
    refine ⟨i, (treeLe_false_iff_le _ _).mpr ?_⟩
    change σ (some (q i).1) ≤ σ (some (q i).2)
    rw [← ht (q i).1, ← ht (q i).2]
    exact (PrefixSet.toTree_le_toTree _ _).mpr hi
  · intro h ρ hρ hsat
    obtain ⟨g, hg, hgg, hρg⟩ := hC ρ hρ
    let σ : Option V → Semantics.Tree n := fun o => (o.elim g ρ).toTree
    obtain ⟨i, hi⟩ := h σ
      (fun o => (hD _).mpr (by cases o; exacts [hg, hρ _]))
      ((satT_guarded vs Γ σ).mpr
        ⟨(PrefixSet.toTree_node _).symm ▸ (PrefixSet.toTree_le_toTree _ _).mpr hgg,
          fun v _ => (PrefixSet.toTree_le_toTree _ _).mpr (hρg v),
          fun l hl => (holdsT_toLitT ρ l).mpr (hsat l hl)⟩)
    exact ⟨i, (PrefixSet.toTree_le_toTree _ _).mp ((treeLe_false_iff_le _ _).mp hi)⟩

/-- In a class that contains the tree all of whose paths are labeled `f`, every assignment lies
below this tree, which is a guard. -/
theorem exists_guard_of_univ {C : PrefixSet n → Prop} (hC : C PrefixSet.univ)
    (ρ : V → PrefixSet n) : ∃ g, C g ∧ g ≤ PrefixSet.node (fun _ => g) ∧ ∀ v, ρ v ≤ g :=
  ⟨PrefixSet.univ, hC, PrefixSet.node_univ.ge, fun v => PrefixSet.le_univ (ρ v)⟩

/-- Disjunctive entailment over arbitrary trees over `{⊥, f}` is the entailment of the guarded
constraint over arbitrary trees over `{⊥, f, ⊤}`. -/
theorem disjEntailsIn_iff_guarded {vs : List V} (hvs : ∀ v, v ∈ vs) (Γ : List (Lit n V))
    (q : Fin k → V × V) :
    DisjEntailsIn (fun _ => True) Γ q ↔
      Full.DisjEntailsIn (fun _ => True) (fun _ => false) (guarded vs Γ) (guardedQueries q) :=
  disjEntailsIn_iff_guarded_of_classes (D := fun _ => True) (fun _ => Iff.rfl)
    (fun ρ _ => exists_guard_of_univ trivial ρ) hvs Γ q

/-- Disjunctive entailment over regular trees over `{⊥, f}` is the entailment of the guarded
constraint over regular trees over `{⊥, f, ⊤}`. -/
theorem disjEntailsIn_regular_iff_guarded {vs : List V} (hvs : ∀ v, v ∈ vs)
    (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn IsRegularTree Γ q ↔
      Full.DisjEntailsIn Full.Models.RegularTop (fun _ => false) (guarded vs Γ)
        (guardedQueries q) :=
  disjEntailsIn_iff_guarded_of_classes PrefixSet.subtrees_toTree_finite_iff
    (fun ρ _ => exists_guard_of_univ isRegularTree_univ ρ) hvs Γ q

/-- Disjunctive entailment over finite trees over `{⊥, f}` is the entailment of the guarded
constraint over finite trees over `{⊥, f, ⊤}`. The guard of finitely many finite trees is a
complete tree whose depth exceeds the length of all their constructor positions. -/
theorem disjEntailsIn_finite_iff_guarded {vs : List V} (hvs : ∀ v, v ∈ vs)
    (Γ : List (Lit n V)) (q : Fin k → V × V) :
    DisjEntailsIn IsFiniteTree Γ q ↔
      Full.DisjEntailsIn Full.Models.FiniteTop (fun _ => false) (guarded vs Γ)
        (guardedQueries q) := by
  classical
  have : Finite V := Set.finite_univ_iff.mp (vs.finite_toSet.subset fun v _ => hvs v)
  refine disjEntailsIn_iff_guarded_of_classes PrefixSet.finiteTop_toTree_iff
    (fun ρ hρ => ?_) hvs Γ q
  obtain ⟨d, hd⟩ := exists_le_complete hρ
  exact ⟨PrefixSet.complete d, isFiniteTree_complete d, PrefixSet.complete_le_node d, hd⟩

/-- Disjunctive entailment over `{⊥, f}` holds over regular trees exactly when it holds over
arbitrary trees. -/
theorem disjEntailsIn_regular_iff [Finite V] (Γ : List (Lit n V))
    (q : Fin k → V × V) :
    DisjEntailsIn IsRegularTree Γ q ↔ DisjEntailsIn (fun _ => True) Γ q := by
  classical
  let := Fintype.ofFinite V
  have hvs : ∀ v : V, v ∈ Finset.univ.toList := fun v => Finset.mem_toList.mpr (Finset.mem_univ v)
  exact (disjEntailsIn_regular_iff_guarded hvs Γ q).trans
    (Full.Reduction.disjEntails_regular_iff.trans (disjEntailsIn_iff_guarded hvs Γ q).symm)

end DeciSigma1.Entailment
