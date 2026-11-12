/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases

/-!
# First-order interpretations and FO reductions

Complexity theory is essentially absent from Mathlib because formalizing a
machine model of computation (and resource bounds on it) is hard. However, many
classical NP-hardness reductions do not need the full power of polynomial-time
computation: the reduction is *first-order expressible* – the output structure
can be described by fixed first-order formulas evaluated in the input
structure. Such FO reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so
exhibiting an FO reduction is (much) stronger than exhibiting a Karp
reduction ([Karp 1972][karp1972reducibility]), while being completely
machine-model-free and therefore easy to
formalize on top of Mathlib's `ModelTheory` library.

This file defines:

* `DescriptiveComplexity.DecisionProblem L`: a “problem” over the vocabulary `L`, i.e., a
  property of `L`-structures;
* `DescriptiveComplexity.FOInterpretation L L' Tag dim`: a tagged, `dim`-dimensional
  first-order interpretation of a relational language `L'` in a language `L`,
  mapping every `L`-structure `A` to an `L'`-structure `I.Map A` with universe
  `Tag × (Fin dim → A)`;
* `DescriptiveComplexity.FOInterpretation.IsQuantifierFree`: interpretations all of whose
  defining formulas are quantifier-free (an even weaker reduction notion);
* `DescriptiveComplexity.FOReduction P Q`: an FO reduction from problem `P` to problem
  `Q`, i.e., an interpretation mapping yes-instances of `P` exactly to
  yes-instances of `Q`.

## Design notes

The textbook notion of FO reduction maps a structure `A` to a structure with
universe a definable subset of `A^k`, using a linear order on `A` to encode
constantly many “sorts” of elements. To stay order-free and subset-free we
instead tag tuples with elements of a finite type `Tag`, and use the full
universe `Tag × A^dim`: junk elements are harmless in practice because the
defining formulas can exclude them from all relations. Every tagged
interpretation can be converted into a textbook `k`-ary FO reduction on
ordered structures (using the order to encode constantly many tags), so the
notion formalized here is a genuine form of FO reducibility.

The universe of `I.Map A` is `Tag × (Fin dim → A)`, which is finite whenever
`A` and `Tag` are (`FOInterpretation.map_finite`): FO reductions map finite
structures to finite structures, as required for reductions between decision
problems on finite structures.

Following the usual convention of finite model theory, reductions are only
required to be correct on *nonempty* structures (and their tag types are
required to be nonempty, so that nonempty structures map to nonempty
structures). Empty structures are degenerate: no fixed-dimension
interpretation can produce a nonempty structure from an empty one, so e.g., no
problem that is false on an empty structure could reduce to SAT (whose empty
instance is trivially satisfiable), and hardness results would fail for
spurious reasons.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

/-- A decision problem in the sense of descriptive complexity: an
isomorphism-closed property of `L`-structures, whose yes-instances are the
`L`-structures satisfying it. Isomorphism-invariance is part of the notion –
a decision problem cannot distinguish isomorphic presentations of the same
structure.

The vocabulary is *relational*, as everywhere in finite model theory: the
instance argument makes the convention structural, so every notion built on
decision problems – interpretations, reductions, complexity classes –
inherits it once and for all. -/
structure DecisionProblem [L.IsRelational] where
  /-- The predicate: `P A` (through the function coercion) states that the
  structure `A` is a yes-instance. -/
  Holds : ∀ (A : Type) [L.Structure A], Prop
  /-- Decision problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → (Holds A ↔ Holds B)

namespace DecisionProblem

variable {L} [L.IsRelational]

instance : CoeFun (DecisionProblem L) fun _ => ∀ (A : Type) [L.Structure A], Prop :=
  ⟨Holds⟩

@[ext]
theorem ext {P Q : DecisionProblem L} (h : ∀ (A : Type) [L.Structure A], P A ↔ Q A) :
    P = Q := by
  obtain ⟨p, hp⟩ := P
  obtain ⟨q, hq⟩ := Q
  have : p = q := funext fun A => funext fun inst => propext (h A)
  subst this
  rfl

end DecisionProblem

/-! ### Transport of relations along isomorphisms

Proving the `iso_invariant` field of a `DecisionProblem` always starts the
same way: the semantic property is phrased in terms of `RelMap r ![a]` /
`RelMap r ![a, b]`, and one must know that these transport along an
`L`-isomorphism. The two lemmas below package this step once and for all
(`Mathlib`'s `StrongHomClass.map_rel` states it with `e ∘ ![a, b]`, which
must first be normalized to `![e a, e b]`). -/

section RelMapTransport

variable {L} {A B : Type} [L.Structure A] [L.Structure B]

/-- A unary relation transports along an `L`-isomorphism. -/
theorem relMap_equiv₁ (e : A ≃[L] B) (r : L.Relations 1) (a : A) :
    RelMap r ![a] ↔ RelMap r ![e a] := by
  have h := StrongHomClass.map_rel e r ![a]
  have hv : e ∘ ![a] = ![e a] := by
    funext j
    fin_cases j
    simp
  rw [hv] at h
  exact h.symm

/-- A binary relation transports along an `L`-isomorphism. -/
theorem relMap_equiv₂ (e : A ≃[L] B) (r : L.Relations 2) (a b : A) :
    RelMap r ![a, b] ↔ RelMap r ![e a, e b] := by
  have h := StrongHomClass.map_rel e r ![a, b]
  have hv : e ∘ ![a, b] = ![e a, e b] := by
    funext j
    fin_cases j <;> simp
  rw [hv] at h
  exact h.symm

/-- A ternary relation transports along an `L`-isomorphism. -/
private theorem relMap_equiv₃ (e : A ≃[L] B) (r : L.Relations 3) (a b c : A) :
    RelMap r ![a, b, c] ↔ RelMap r ![e a, e b, e c] := by
  have h := StrongHomClass.map_rel e r ![a, b, c]
  have hv : e ∘ ![a, b, c] = ![e a, e b, e c] := by
    funext j
    fin_cases j <;> simp
  rw [hv] at h
  exact h.symm

/-- Realization of an atom of arity 3, the shape Mathlib's
`Formula.realize_rel₁` and `Formula.realize_rel₂` stop short of. -/
theorem realize_rel₃ {L : Language} {α M : Type} [L.Structure M] {R : L.Relations 3}
    {t₁ t₂ t₃ : L.Term α} {v : α → M} :
    (R.formula ![t₁, t₂, t₃]).Realize v ↔
      RelMap R ![t₁.realize v, t₂.realize v, t₃.realize v] := by
  rw [Formula.realize_rel, iff_eq_eq]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Realization of an atom of arity 4. -/
theorem realize_rel₄ {L : Language} {α M : Type} [L.Structure M] {R : L.Relations 4}
    {t₁ t₂ t₃ t₄ : L.Term α} {v : α → M} :
    (R.formula ![t₁, t₂, t₃, t₄]).Realize v ↔
      RelMap R ![t₁.realize v, t₂.realize v, t₃.realize v, t₄.realize v] := by
  rw [Formula.realize_rel, iff_eq_eq]
  congr 1
  funext i
  fin_cases i <;> rfl

end RelMapTransport

/-- A *tagged `dim`-dimensional first-order interpretation* of the relational
language `L'` in the language `L`. It maps an `L`-structure `A` to the
`L'`-structure with universe `Tag × A^dim` in which an `n`-ary relation symbol
`R` holds of tagged tuples `(t₁, ā₁), …, (tₙ, āₙ)` iff the first-order
`L`-formula `relFormula R (t₁, …, tₙ)` – whose free variable `(i, j)` stands
for the `j`-th coordinate `āᵢ j` of the `i`-th argument – holds in `A`. -/
structure FOInterpretation (Tag : Type) (dim : ℕ) where
  /-- The defining `L`-formula of each relation symbol of `L'`, for each tuple
  of tags; the free variable `(i, j)` is the `j`-th coordinate of the `i`-th
  argument tuple. -/
  relFormula : ∀ {n : ℕ}, L'.Relations n → (Fin n → Tag) → L.Formula (Fin n × Fin dim)

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- The universe of the structure interpreted in `A`: tagged `dim`-tuples.

This is a plain `def` (not an `abbrev`) so that the `L'.Structure` instance on
it can be found by instance search, while `rcases`-style destructuring still
sees through it. -/
protected def Map (_I : FOInterpretation L L' Tag dim) (A : Type) : Type :=
  Tag × (Fin dim → A)

variable (I : FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The `L'`-structure interpreted in the `L`-structure `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) where
  funMap f := isEmptyElim f
  RelMap R xs := (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2

theorem relMap_map [L'.IsRelational] {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.Map A) :
    RelMap R xs ↔ (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2 :=
  Iff.rfl

omit [L.Structure A] in
/-- FO interpretations map finite structures to finite structures. -/
theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  inferInstanceAs (Finite (Tag × (Fin dim → A)))

omit [L.Structure A] in
/-- FO interpretations with nonempty tags map nonempty structures to nonempty
structures. -/
theorem map_nonempty [Nonempty Tag] [Nonempty A] : Nonempty (I.Map A) :=
  inferInstanceAs (Nonempty (Tag × (Fin dim → A)))

/-- An interpretation is quantifier-free if all its defining formulas are.
Quantifier-free reductions are the weakest reduction notion in common use in
descriptive complexity; SAT remains NP-complete under them. -/
def IsQuantifierFree : Prop :=
  ∀ {n : ℕ} (R : L'.Relations n) (t : Fin n → Tag), (I.relFormula R t).IsQF

end FOInterpretation

variable {L L' : Language.{0, 0}}

/-- A first-order reduction from the problem `P` (on `L`-structures) to the
problem `Q` (on `L'`-structures): a first-order interpretation mapping
yes-instances of `P` exactly to yes-instances of `Q`.

Since FO interpretations are computable in AC⁰ ⊆ PTIME on (encodings of)
finite structures, an `FOReduction P Q` is in particular a Karp reduction from
`P` to `Q`: any NP-hardness argument for `P` transfers to `Q`, without any
formalized machine model. -/
structure FOReduction [L.IsRelational] [L'.IsRelational] (P : DecisionProblem L)
    (Q : DecisionProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty
  structures. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation. -/
  toInterpretation : FOInterpretation L L' Tag dim
  /-- Yes-instances map exactly to yes-instances, on the *finite* nonempty
  structures: membership and hardness read a problem only there
  (`DescriptiveComplexity.ComplexityClass`), so asking anything of the infinite
  ones would be an obligation nothing consumes. The ordered and relativized
  notions restrict the same way. -/
  correct : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ " Q:51 => FOReduction P Q

/-- For a one-dimensional interpretation with a single tag, the interpreted
universe is equivalent, as a plain type, to the original universe. -/
def FOInterpretation.mapEquivSelf (I : FOInterpretation L L' Unit 1) (A : Type) :
    I.Map A ≃ A where
  toFun x := x.2 0
  invFun a := ((), fun _ => a)
  left_inv x :=
    Prod.ext_iff.mpr ⟨rfl, funext fun j => congrArg x.2 (Subsingleton.elim 0 j)⟩
  right_inv _ := rfl

/-- Interpretations are functorial on isomorphisms: an `L`-isomorphism of the
base structures induces an `L'`-isomorphism of the interpreted structures. -/
def FOInterpretation.mapLEquiv [L'.IsRelational] {Tag : Type} {dim : ℕ}
    (I : FOInterpretation L L' Tag dim) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : I.Map M ≃[L'] I.Map N where
  toFun p := (p.1, fun j => e (p.2 j))
  invFun p := (p.1, fun j => e.symm (p.2 j))
  left_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun j => e.symm_apply_apply (p.2 j)⟩
  right_inv p := Prod.ext_iff.mpr ⟨rfl, funext fun j => e.apply_symm_apply (p.2 j)⟩
  map_fun' f := isEmptyElim f
  map_rel' R x := by
    rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    exact StrongHomClass.realize_formula e _

end DescriptiveComplexity
