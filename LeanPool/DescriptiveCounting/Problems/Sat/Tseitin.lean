/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrder
public import LeanPool.DescriptiveCounting.Padding
import Mathlib.Tactic.FinCases
import all LeanPool.DescriptiveCounting.Padding

/-!
# The Tseitin encoding of a first-order kernel: semantic layer

Machinery for the hardness half of the Cook–Levin theorem
([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal];
`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`, in
`DescriptiveComplexity.Problems.Sat.Hardness`): the generic, machine-free reduction of
any existential-second-order definable problem to SAT (via a Tseitin
([Tseitin 1968][tseitin1968complexity]) encoding), in the style of Dahlhaus
([Dahlhaus 1983][dahlhaus1983reduction]). Given the first-order kernel `φ`
(a sentence over the input
vocabulary expanded by one second-order block), the produced CNF instance has

* one propositional variable per relation variable `i` of the block and tuple
  `ā` (“`ā ∈ Rᵢ`”), and one per subformula position `p` of `φ` and context
  tuple `w` (“the subformula at `p` holds under `w`”);
* Tseitin-style clauses per subformula position, forcing the position
  variables to compute the truth value of their subformulas bottom-up.

This file contains the *semantic* part of the construction, independent of
the FO formulas defining the CNF instance inside the input structure:

* `DescriptiveComplexity.Tseitin.NodeAt f m`: the type of subformula positions of `f`
  with context length `m` (the root is uniformly reachable via
  `DescriptiveComplexity.Tseitin.rootAt`);
* `DescriptiveComplexity.Tseitin.Gates`: a valuation of the position variables computes
  truth values correctly at every position (“all Tseitin gates hold”);
* `DescriptiveComplexity.Tseitin.canonVal`, the canonical valuation by actual truth
  values, which satisfies all gates (`DescriptiveComplexity.Tseitin.gates_canonVal`),
  and the converse reading (`DescriptiveComplexity.Tseitin.gates_realize`): any
  valuation satisfying the gates assigns the root its actual truth value;
* `DescriptiveComplexity.Tseitin.IsClauseSem` / `DescriptiveComplexity.Tseitin.LitSem`: the clauses
  of the encoding and their literals, as semantic predicates on tuples of a
  fixed length `D` padded with minimal elements (junk tuples are excluded by
  canonicity conditions);
* the main equivalence `DescriptiveComplexity.Tseitin.satCond_iff_gates`: a valuation
  satisfies every clause iff the induced (padding-invariant) valuation
  satisfies every gate.

The corresponding first-order formulas and their realization lemmas are in
`DescriptiveComplexity.Problems.Sat.TseitinFormulas`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

namespace Tseitin

open Language Structure

/-! ### Subformula positions -/

section Nodes

variable {L' : Language.{0, 0}}

/-- The type of subformula positions (“nodes”) of `f` with context length
`m`: positions at which the subformula has `m` free de Bruijn variables. The
family is indexed by the context length so that all node-dependent data
(valuations, clauses) can be typed uniformly, without a dependent context
function. -/
def NodeAt : ∀ {n : ℕ}, L'.BoundedFormula Empty n → ℕ → Type
  | n, .falsum, m => PLift (n = m)
  | n, .equal _ _, m => PLift (n = m)
  | n, .rel _ _, m => PLift (n = m)
  | n, .imp f₁ f₂, m => PLift (n = m) ⊕ (NodeAt f₁ m ⊕ NodeAt f₂ m)
  | n, .all f, m => PLift (n = m) ⊕ NodeAt f m

/-- The root position of a formula. -/
def rootAt : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), NodeAt f n
  | _, .falsum => ⟨rfl⟩
  | _, .equal _ _ => ⟨rfl⟩
  | _, .rel _ _ => ⟨rfl⟩
  | _, .imp _ _ => Sum.inl ⟨rfl⟩
  | _, .all _ => Sum.inl ⟨rfl⟩

/-- Whether a position is the root, as a Boolean (usable inside formula
definitions, where positions of a variable formula cannot be
pattern-matched). -/
def isRootB : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ}, NodeAt f m → Bool
  | _, .falsum, _, _ => true
  | _, .equal _ _, _, _ => true
  | _, .rel _ _, _, _ => true
  | _, .imp _ _, _, p => Sum.isLeft p
  | _, .all _, _, p => Sum.isLeft p

/-- A position is the root iff `isRootB` says so; in that case its context
length is the formula's own index. Stated as an equality of dependent
pairs. -/
private theorem isRootB_iff :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ} (p : NodeAt f m),
      isRootB f p = true ↔ (⟨m, p⟩ : Σ m', NodeAt f m') = ⟨n, rootAt f⟩
  | _, .falsum, _, p => by obtain ⟨rfl⟩ := p; simp [isRootB, rootAt]
  | _, .equal _ _, _, p => by obtain ⟨rfl⟩ := p; simp [isRootB, rootAt]
  | _, .rel _ _, _, p => by obtain ⟨rfl⟩ := p; simp [isRootB, rootAt]
  | _, .imp _ _, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · simp [isRootB, rootAt]
      · refine iff_of_false (by simp [isRootB]) fun h => ?_
        injection h with h1 h2
        subst h1
        exact absurd (eq_of_heq h2) (by rintro ⟨⟩)
  | _, .all _, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · simp [isRootB, rootAt]
      · refine iff_of_false (by simp [isRootB]) fun h => ?_
        injection h with h1 h2
        subst h1
        exact absurd (eq_of_heq h2) (by rintro ⟨⟩)

/-- Equality of dependent pairs through a fiberwise injective map. -/
private theorem sigma_map_eq_iff {β β' : ℕ → Type} (F : ∀ m, β m → β' m)
    (hF : ∀ m, Function.Injective (F m)) {m₁ m₂ : ℕ} (a : β m₁) (b : β m₂) :
    (⟨m₁, F m₁ a⟩ : Σ m, β' m) = ⟨m₂, F m₂ b⟩ ↔ (⟨m₁, a⟩ : Σ m, β m) = ⟨m₂, b⟩ := by
  constructor
  · intro h
    injection h with h1 h2
    subst h1
    exact congrArg (Sigma.mk m₁) (hF _ (eq_of_heq h2))
  · intro h
    injection h with h1 h2
    subst h1
    exact congrArg (Sigma.mk m₁) (congrArg (F m₁) (eq_of_heq h2))

/-- The largest context length occurring in a formula. -/
def maxCtx : ∀ {n : ℕ}, L'.BoundedFormula Empty n → ℕ
  | n, .falsum => n
  | n, .equal _ _ => n
  | n, .rel _ _ => n
  | _, .imp f₁ f₂ => max (maxCtx f₁) (maxCtx f₂)
  | _, .all f => maxCtx f

/-- A formula's own index is a context length, hence bounded by `maxCtx`. -/
theorem le_maxCtx : ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), n ≤ maxCtx f
  | _, .falsum => le_rfl
  | _, .equal _ _ => le_rfl
  | _, .rel _ _ => le_rfl
  | _, .imp f₁ _ => (le_maxCtx f₁).trans (le_max_left _ _)
  | n, .all f => (Nat.le_succ n).trans (le_maxCtx f)

/-- Context lengths of actual positions are bounded by `maxCtx`. -/
theorem nodeAt_le_maxCtx :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n) {m : ℕ}, NodeAt f m → m ≤ maxCtx f
  | _, .falsum, _, p => by obtain ⟨rfl⟩ := p; exact le_rfl
  | _, .equal _ _, _, p => by obtain ⟨rfl⟩ := p; exact le_rfl
  | _, .rel _ _, _, p => by obtain ⟨rfl⟩ := p; exact le_rfl
  | _, .imp f₁ f₂, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q | q := p
      · exact le_maxCtx _
      · exact (nodeAt_le_maxCtx f₁ q).trans (le_max_left _ _)
      · exact (nodeAt_le_maxCtx f₂ q).trans (le_max_right _ _)
  | _, .all f, _, p => by
      obtain ⟨⟨rfl⟩⟩ | q := p
      · exact le_maxCtx _
      · exact nodeAt_le_maxCtx f q

private def rootSigmaEquiv (n : ℕ) : PUnit.{1} ≃ (Σ m, PLift (n = m)) where
  toFun _ := ⟨n, ⟨rfl⟩⟩
  invFun _ := ⟨⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨m, ⟨rfl⟩⟩; rfl

instance (n : ℕ) : Finite (Σ m, PLift (n = m)) :=
  Finite.of_equiv _ (rootSigmaEquiv n)

/-- There are finitely many positions in a formula. -/
instance finite_sigma_nodeAt :
    ∀ {n : ℕ} (f : L'.BoundedFormula Empty n), Finite (Σ m, NodeAt f m)
  | n, .falsum => inferInstanceAs (Finite (Σ m, PLift (n = m)))
  | n, .equal _ _ => inferInstanceAs (Finite (Σ m, PLift (n = m)))
  | n, .rel _ _ => inferInstanceAs (Finite (Σ m, PLift (n = m)))
  | _, .imp f₁ f₂ =>
      haveI := finite_sigma_nodeAt f₁
      haveI := finite_sigma_nodeAt f₂
      Finite.of_equiv _
        ((Equiv.sigmaSumDistrib _ _).trans
          ((Equiv.refl _).sumCongr (Equiv.sigmaSumDistrib _ _))).symm
  | _, .all f =>
      haveI := finite_sigma_nodeAt f
      Finite.of_equiv _ (Equiv.sigmaSumDistrib _ _).symm

end Nodes

/-! ### Terms of the expanded language -/

section Terms

variable {L : Language.{0, 0}} {B : SOBlock}

/-- A term of the language expanded by a (relational) block is a term of the
base language. -/
def termToL {α : Type} : (L.sum B.lang).Term α → L.Term α
  | .var a => .var a
  | .func f ts =>
      match f with
      | Sum.inl f => .func f fun i => termToL (ts i)
      | Sum.inr f => isEmptyElim f

/-- Reembedding `termToL` into the expanded language gives the term back. -/
private theorem sumInl_onTerm_termToL {α : Type} (t : (L.sum B.lang).Term α) :
    LHom.sumInl.onTerm (termToL t) = t := by
  induction t with
  | var a => rfl
  | func f ts ih =>
      cases f with
      | inl f =>
          change Term.func (Sum.inl f) (fun i => LHom.sumInl.onTerm (termToL (ts i))) = _
          exact congrArg _ (funext ih)
      | inr f => exact isEmptyElim f

variable {A : Type}

/-- Realization of `termToL` in the base structure agrees with realization of
the term in any expansion. -/
private theorem realize_termToL [L.Structure A] [(L.sum B.lang).Structure A]
    [(LHom.sumInl : L →ᴸ L.sum B.lang).IsExpansionOn A] {α : Type}
    (t : (L.sum B.lang).Term α) (v : α → A) :
    (termToL t).realize v = t.realize v := by
  conv_rhs => rw [← sumInl_onTerm_termToL t]
  exact (LHom.realize_onTerm _ _ _).symm

end Terms

/-! ### Gates: correctness of a valuation of the position variables -/

section Gates

variable {L : Language.{0, 0}} {B : SOBlock} {A : Type}

/-- The expansion of an `L`-structure by a block assignment. -/
@[instance_reducible]
def assignStructure (L : Language.{0, 0}) [L.Structure A] {B : SOBlock}
    (μ : B.Assignment A) : (L.sum B.lang).Structure A :=
  letI := B.structure μ
  inferInstance

/-- Realization of a kernel formula in the expansion of an `L`-structure by a
block assignment. -/
def RealizeWith [L.Structure A] (μ : B.Assignment A) {n : ℕ}
    (f : (L.sum B.lang).BoundedFormula Empty n) (w : Fin n → A) : Prop :=
  letI := assignStructure L μ
  f.Realize isEmptyElim w

variable [L.Structure A]

/-- The truth value of an equality atom of the kernel under a context
tuple. -/
def eqGuard {m : ℕ} (t₁ t₂ : (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  (termToL t₁).realize (Sum.elim isEmptyElim w) =
    (termToL t₂).realize (Sum.elim isEmptyElim w)

/-- The truth value of an input-relation atom of the kernel under a context
tuple. -/
def relGuard {m l : ℕ} (r : L.Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  RelMap r fun k => (termToL (ts k)).realize (Sum.elim isEmptyElim w)

/-- The truth value of a block-variable atom of the kernel under an
assignment and a context tuple. -/
def blockAtom (μ : B.Assignment A) {m l : ℕ} (r : B.lang.Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  μ r.1 fun k => (termToL (ts (Fin.cast r.2 k))).realize (Sum.elim isEmptyElim w)

/-- The truth value of an arbitrary atom of the kernel. -/
def atomHolds (μ : B.Assignment A) {m l : ℕ} (R : (L.sum B.lang).Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m)) (w : Fin m → A) : Prop :=
  match R with
  | Sum.inl r => relGuard r ts w
  | Sum.inr r => blockAtom μ r ts w

/-- A valuation of the position variables of a formula: a truth value for
every position and context tuple. -/
abbrev NodeVal (A : Type) {L' : Language.{0, 0}} {n : ℕ}
    (f : L'.BoundedFormula Empty n) : Type :=
  ∀ m, NodeAt f m → (Fin m → A) → Prop

/-- All Tseitin gates of a formula hold under a valuation of its position
variables: at every position, the valuation relates to the valuations at the
children (or to the atom's truth value) as dictated by the connective. A
valuation satisfying all gates computes actual truth values
(`DescriptiveComplexity.Tseitin.gates_realize`). -/
def Gates (μ : B.Assignment A) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), NodeVal A f → Prop
  | n, .falsum, ν => ∀ w : Fin n → A, ¬ν n ⟨rfl⟩ w
  | n, .equal t₁ t₂, ν => ∀ w : Fin n → A, ν n ⟨rfl⟩ w ↔ eqGuard t₁ t₂ w
  | n, .rel R ts, ν => ∀ w : Fin n → A, ν n ⟨rfl⟩ w ↔ atomHolds μ R ts w
  | n, .imp f₁ f₂, ν =>
      (∀ w : Fin n → A, ν n (Sum.inl ⟨rfl⟩) w ↔
        (ν n (Sum.inr (Sum.inl (rootAt f₁))) w →
          ν n (Sum.inr (Sum.inr (rootAt f₂))) w)) ∧
      Gates μ f₁ (fun m q => ν m (Sum.inr (Sum.inl q))) ∧
      Gates μ f₂ (fun m q => ν m (Sum.inr (Sum.inr q)))
  | n, .all f, ν =>
      (∀ w : Fin n → A, ν n (Sum.inl ⟨rfl⟩) w ↔
        ∀ a : A, ν (n + 1) (Sum.inr (rootAt f)) (Fin.snoc w a)) ∧
      Gates μ f (fun m q => ν m (Sum.inr q))

/-- The canonical valuation: each position variable receives the truth value
of its subformula. -/
def canonVal (μ : B.Assignment A) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), NodeVal A f
  | _, .falsum, _, _, _ => False
  | _, .equal t₁ t₂, _, p, w =>
      RealizeWith μ (.equal t₁ t₂) (w ∘ Fin.cast p.down)
  | _, .rel R ts, _, p, w => RealizeWith μ (.rel R ts) (w ∘ Fin.cast p.down)
  | _, .imp f₁ f₂, _, p, w =>
      (match p with
        | Sum.inl h => RealizeWith μ (f₁.imp f₂) (w ∘ Fin.cast h.down)
        | Sum.inr (Sum.inl q) => canonVal μ f₁ _ q w
        | Sum.inr (Sum.inr q) => canonVal μ f₂ _ q w)
  | _, .all f, _, p, w =>
      (match p with
        | Sum.inl h => RealizeWith μ f.all (w ∘ Fin.cast h.down)
        | Sum.inr q => canonVal μ f _ q w)

/-- The canonical valuation at the root is the truth value of the whole
formula. -/
private theorem canonVal_rootAt (μ : B.Assignment A) {n : ℕ}
    (f : (L.sum B.lang).BoundedFormula Empty n) (w : Fin n → A) :
    canonVal μ f n (rootAt f) w ↔ RealizeWith μ f w := by
  cases f <;> exact Iff.rfl

/-! ### Unfolding `RealizeWith` -/

variable (μ : B.Assignment A)

private theorem realizeWith_falsum {n : ℕ} (w : Fin n → A) :
    ¬RealizeWith μ (.falsum : (L.sum B.lang).BoundedFormula Empty n) w := id

private theorem realizeWith_equal {n : ℕ} (t₁ t₂ : (L.sum B.lang).Term (Empty ⊕ Fin n))
    (w : Fin n → A) : RealizeWith μ (.equal t₁ t₂) w ↔ eqGuard t₁ t₂ w := by
  let := B.structure μ
  change t₁.realize (Sum.elim isEmptyElim w) = t₂.realize (Sum.elim isEmptyElim w) ↔ _
  rw [eqGuard, realize_termToL t₁, realize_termToL t₂]

private theorem realizeWith_rel {n l : ℕ} (R : (L.sum B.lang).Relations l)
    (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin n)) (w : Fin n → A) :
    RealizeWith μ (.rel R ts) w ↔ atomHolds μ R ts w := by
  let := B.structure μ
  cases R with
  | inl r =>
      change RelMap r (fun k => (ts k).realize (Sum.elim isEmptyElim w)) ↔
        relGuard r ts w
      rw [relGuard]
      simp only [realize_termToL]
  | inr r =>
      change μ r.1 (fun j => (ts (Fin.cast r.2 j)).realize (Sum.elim isEmptyElim w)) ↔
        blockAtom μ r ts w
      rw [blockAtom]
      simp only [realize_termToL]

private theorem realizeWith_imp {n : ℕ} (f₁ f₂ : (L.sum B.lang).BoundedFormula Empty n)
    (w : Fin n → A) :
    RealizeWith μ (f₁.imp f₂) w ↔ (RealizeWith μ f₁ w → RealizeWith μ f₂ w) :=
  Iff.rfl

private theorem realizeWith_all {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty (n + 1))
    (w : Fin n → A) :
    RealizeWith μ f.all w ↔ ∀ a : A, RealizeWith μ f (Fin.snoc w a) :=
  Iff.rfl

/-! ### Gates compute truth values -/

/-- Any valuation satisfying all gates assigns to the root the truth value of
the formula. -/
theorem gates_realize :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (ν : NodeVal A f),
      Gates μ f ν → ∀ w : Fin n → A, (ν n (rootAt f) w ↔ RealizeWith μ f w)
  | _, .falsum, _, hg, w => iff_of_false (hg w) (realizeWith_falsum μ w)
  | _, .equal t₁ t₂, _, hg, w => (hg w).trans (realizeWith_equal μ t₁ t₂ w).symm
  | _, .rel R ts, _, hg, w => (hg w).trans (realizeWith_rel μ R ts w).symm
  | _, .imp f₁ f₂, ν, hg, w => by
      obtain ⟨hroot, hg₁, hg₂⟩ := hg
      refine (hroot w).trans ?_
      rw [realizeWith_imp]
      exact imp_congr (gates_realize f₁ _ hg₁ w) (gates_realize f₂ _ hg₂ w)
  | _, .all f, ν, hg, w => by
      obtain ⟨hroot, hg'⟩ := hg
      refine (hroot w).trans ?_
      rw [realizeWith_all]
      exact forall_congr' fun a => gates_realize f _ hg' (Fin.snoc w a)

/-- The canonical valuation satisfies all gates. -/
theorem gates_canonVal :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), Gates μ f (canonVal μ f)
  | _, .falsum => fun _ h => h
  | _, .equal t₁ t₂ => fun w => realizeWith_equal μ t₁ t₂ w
  | _, .rel R ts => fun w => realizeWith_rel μ R ts w
  | _, .imp f₁ f₂ =>
      ⟨fun w => (realizeWith_imp μ f₁ f₂ w).trans
          (imp_congr (canonVal_rootAt μ f₁ w).symm (canonVal_rootAt μ f₂ w).symm),
        gates_canonVal f₁, gates_canonVal f₂⟩
  | _, .all f =>
      ⟨fun w => (realizeWith_all μ f w).trans
          (forall_congr' fun a => (canonVal_rootAt μ f (Fin.snoc w a)).symm),
        gates_canonVal f⟩

end Gates

/-! ### The clauses of the encoding and their literals -/

section Clauses

variable {L : Language.{0, 0}} {B : SOBlock} {A : Type} {D : ℕ}
variable [L.Structure A] [LE A]

/-- The literal tuple of a block-variable atom: canonical, with the atom's
term values as prefix. -/
def atomLit {m l : ℕ} (ts : Fin l → (L.sum B.lang).Term (Empty ⊕ Fin m))
    (w : Fin m → A) (x : Fin D → A) : Prop :=
  Canon l x ∧ ∀ (j : Fin D) (hj : (j : ℕ) < l),
    x j = (termToL (ts ⟨(j : ℕ), hj⟩)).realize (Sum.elim isEmptyElim w)

/-- The clauses of the Tseitin encoding, as a predicate on positions, clause
kinds (`Fin 3`) and canonical `D`-tuples:

* `falsum` node at context `w`: kind 0, the unit clause `¬v(p, w)`;
* `equal`/input-relation node: kind 0, the unit clause `v(p, w)`, present
  when the atom holds under `w`; kind 1, the unit clause `¬v(p, w)`, present
  otherwise;
* block-variable node: kind 0, `¬v(p, w) ∨ R(ā)`; kind 1, `v(p, w) ∨ ¬R(ā)`;
* `imp` node with children `a`, `b`: kind 0, `¬v(p, w) ∨ ¬a(w) ∨ b(w)`;
  kind 1, `v(p, w) ∨ a(w)`; kind 2, `v(p, w) ∨ ¬b(w)`;
* `all` node with child `c`: kind 0 (indexed by extended tuples `w ⌢ a`),
  `¬v(p, w) ∨ c(w ⌢ a)`; kind 1, the wide clause
  `v(p, w) ∨ ⋁_a ¬c(w ⌢ a)`. -/
def IsClauseSem :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), maxCtx f ≤ D →
      ∀ {m : ℕ}, NodeAt f m → Fin 3 → (Fin D → A) → Prop
  | n, .falsum, _, _, _, k, u => k = 0 ∧ Canon n u
  | n, .equal t₁ t₂, h, _, _, k, u =>
      Canon n u ∧
        ((k = 0 ∧ eqGuard t₁ t₂ (pref ((le_maxCtx _).trans h) u)) ∨
         (k = 1 ∧ ¬eqGuard t₁ t₂ (pref ((le_maxCtx _).trans h) u)))
  | n, .rel R ts, h, _, _, k, u =>
      (match R with
       | Sum.inl r =>
           Canon n u ∧
             ((k = 0 ∧ relGuard r ts (pref ((le_maxCtx _).trans h) u)) ∨
              (k = 1 ∧ ¬relGuard r ts (pref ((le_maxCtx _).trans h) u)))
       | Sum.inr _ => Canon n u ∧ (k = 0 ∨ k = 1))
  | n, .imp f₁ f₂, h, _, p, k, u =>
      (match p with
       | Sum.inl _ => Canon n u
       | Sum.inr (Sum.inl q) => IsClauseSem f₁ ((le_max_left _ _).trans h) q k u
       | Sum.inr (Sum.inr q) => IsClauseSem f₂ ((le_max_right _ _).trans h) q k u)
  | n, .all f, h, _, p, k, u =>
      (match p with
       | Sum.inl _ => (k = 0 ∧ Canon (n + 1) u) ∨ (k = 1 ∧ Canon n u)
       | Sum.inr q => IsClauseSem f h q k u)

/-- The literals of the clauses of the Tseitin encoding: `LitSem s f h p k u v x`
states that the propositional variable indexed by `v` (a block variable index
or a position) at tuple `x` occurs with sign `s` in the clause `(p, k, u)`.
The clause-existence guards of `DescriptiveComplexity.Tseitin.IsClauseSem` are not
repeated here. -/
def LitSem (s : Bool) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n), maxCtx f ≤ D →
      ∀ {m : ℕ}, NodeAt f m → Fin 3 → (Fin D → A) →
        (B.ι ⊕ Σ m', NodeAt f m') → (Fin D → A) → Prop
  | n, .falsum, _, _, _, k, u, v, x =>
      s = false ∧ k = 0 ∧ v = Sum.inr ⟨n, ⟨rfl⟩⟩ ∧ x = u
  | n, .equal _ _, _, _, _, k, u, v, x =>
      v = Sum.inr ⟨n, ⟨rfl⟩⟩ ∧ x = u ∧
        ((s = true ∧ k = 0) ∨ (s = false ∧ k = 1))
  | n, .rel R ts, h, _, _, k, u, v, x =>
      (match R with
       | Sum.inl _ =>
           v = Sum.inr ⟨n, ⟨rfl⟩⟩ ∧ x = u ∧
             ((s = true ∧ k = 0) ∨ (s = false ∧ k = 1))
       | Sum.inr r =>
           (v = Sum.inr ⟨n, ⟨rfl⟩⟩ ∧ x = u ∧
              ((s = false ∧ k = 0) ∨ (s = true ∧ k = 1))) ∨
           (v = Sum.inl r.1 ∧
              atomLit ts (pref ((le_maxCtx _).trans h) u) x ∧
              ((s = true ∧ k = 0) ∨ (s = false ∧ k = 1))))
  | n, .imp f₁ f₂, h, _, p, k, u, v, x =>
      (match p with
       | Sum.inl _ =>
           x = u ∧
             ((v = Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩ ∧
                ((s = false ∧ k = 0) ∨ (s = true ∧ (k = 1 ∨ k = 2)))) ∨
              (v = Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩ ∧
                ((s = false ∧ k = 0) ∨ (s = true ∧ k = 1))) ∨
              (v = Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩ ∧
                ((s = true ∧ k = 0) ∨ (s = false ∧ k = 2))))
       | Sum.inr (Sum.inl q) =>
           (match v with
            | Sum.inl i =>
                LitSem s f₁ ((le_max_left _ _).trans h) q k u (Sum.inl i) x
            | Sum.inr ⟨m', Sum.inr (Sum.inl q')⟩ =>
                LitSem s f₁ ((le_max_left _ _).trans h) q k u (Sum.inr ⟨m', q'⟩) x
            | _ => False)
       | Sum.inr (Sum.inr q) =>
           (match v with
            | Sum.inl i =>
                LitSem s f₂ ((le_max_right _ _).trans h) q k u (Sum.inl i) x
            | Sum.inr ⟨m', Sum.inr (Sum.inr q')⟩ =>
                LitSem s f₂ ((le_max_right _ _).trans h) q k u (Sum.inr ⟨m', q'⟩) x
            | _ => False))
  | n, .all f, h, _, p, k, u, v, x =>
      (match p with
       | Sum.inl _ =>
           (k = 0 ∧
              ((s = false ∧ v = Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩ ∧
                 Agree n u x ∧ Canon n x) ∨
               (s = true ∧ v = Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩ ∧ x = u))) ∨
           (k = 1 ∧
              ((s = true ∧ v = Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩ ∧ x = u) ∨
               (s = false ∧ v = Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩ ∧
                 Agree n u x ∧ Canon (n + 1) x)))
       | Sum.inr q =>
           (match v with
            | Sum.inl i => LitSem s f h q k u (Sum.inl i) x
            | Sum.inr ⟨m', Sum.inr q'⟩ =>
                LitSem s f h q k u (Sum.inr ⟨m', q'⟩) x
            | _ => False))

end Clauses

/-! ### Clause satisfaction is gate satisfaction -/

section Correctness

variable {L : Language.{0, 0}} {B : SOBlock} {A : Type} {D : ℕ}
variable [L.Structure A] [LinearOrder A]

/-- Every clause of the encoding contains a literal made true by the
valuation `tv` of the propositional variables. -/
def SatCond {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (hctx : maxCtx f ≤ D)
    (tv : (B.ι ⊕ Σ m, NodeAt f m) → (Fin D → A) → Prop) : Prop :=
  ∀ (m : ℕ) (p : NodeAt f m) (k : Fin 3) (u : Fin D → A),
    IsClauseSem f hctx p k u →
    ∃ v x, (LitSem true f hctx p k u v x ∧ tv v x) ∨
      (LitSem false f hctx p k u v x ∧ ¬tv v x)

/-- The block assignment read off a valuation of the propositional variables,
on padded tuples. -/
def padAssign (a₀ : A) {n : ℕ} {f : (L.sum B.lang).BoundedFormula Empty n}
    (tv : (B.ι ⊕ Σ m, NodeAt f m) → (Fin D → A) → Prop) : B.Assignment A :=
  fun i a => tv (Sum.inl i) (pad a₀ a)

/-- The position valuation read off a valuation of the propositional
variables, on padded tuples. -/
def padVal (a₀ : A) {n : ℕ} {f : (L.sum B.lang).BoundedFormula Empty n}
    (tv : (B.ι ⊕ Σ m, NodeAt f m) → (Fin D → A) → Prop) : NodeVal A f :=
  fun m q w => tv (Sum.inr ⟨m, q⟩) (pad a₀ w)

/-- **Clause satisfaction is gate satisfaction**: a valuation of the
propositional variables makes every clause of the Tseitin encoding true iff
the valuation it induces on positions (through canonical padding) satisfies
every gate, with the block variables read off the atom variables. -/
theorem satCond_iff_gates {a₀ : A} (h₀ : IsBot a₀) (harity : ∀ i : B.ι, B.arity i ≤ D) :
    ∀ {n : ℕ} (f : (L.sum B.lang).BoundedFormula Empty n) (hctx : maxCtx f ≤ D)
      (tv : (B.ι ⊕ Σ m, NodeAt f m) → (Fin D → A) → Prop),
      SatCond f hctx tv ↔ Gates (padAssign a₀ tv) f (padVal a₀ tv)
  | n, .falsum, hctx, tv => by
      have hn : n ≤ D := (le_maxCtx _).trans hctx
      constructor
      · intro hsat w
        obtain ⟨v, x, ⟨hlit, -⟩ | ⟨hlit, hv⟩⟩ :=
          hsat n ⟨rfl⟩ 0 (pad a₀ w) ⟨rfl, canon_pad h₀ n w⟩
        · exact absurd hlit.1 (by decide)
        · obtain ⟨-, -, rfl, rfl⟩ := hlit
          exact hv
      · intro hg m p k u hcl
        obtain ⟨rfl⟩ := p
        obtain ⟨rfl, hu⟩ := hcl
        refine ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u, Or.inr ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩⟩
        rw [← pad_pref_of_canon h₀ hn hu]
        exact hg (pref hn u)
  | n, .equal t₁ t₂, hctx, tv => by
      have hn : n ≤ D := (le_maxCtx _).trans hctx
      constructor
      · intro hsat w
        constructor
        · intro hv
          by_contra hguard
          obtain ⟨v, x, ⟨hlit, -⟩ | ⟨hlit, hx⟩⟩ :=
            hsat n ⟨rfl⟩ 1 (pad a₀ w)
              ⟨canon_pad h₀ n w, Or.inr ⟨rfl, by rwa [pref_pad]⟩⟩
          · obtain ⟨-, -, htk | hfk⟩ := hlit
            · exact absurd htk.2 (by decide)
            · exact absurd hfk.1 (by decide)
          · obtain ⟨rfl, rfl, -⟩ := hlit
            exact hx hv
        · intro hguard
          obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
            hsat n ⟨rfl⟩ 0 (pad a₀ w)
              ⟨canon_pad h₀ n w, Or.inl ⟨rfl, by rwa [pref_pad]⟩⟩
          · obtain ⟨rfl, rfl, -⟩ := hlit
            exact hx
          · obtain ⟨-, -, htk | hfk⟩ := hlit
            · exact absurd htk.1 (by decide)
            · exact absurd hfk.2 (by decide)
      · intro hg m p k u hcl
        obtain ⟨rfl⟩ := p
        obtain ⟨hu, ⟨rfl, hguard⟩ | ⟨rfl, hguard⟩⟩ := hcl
        · refine ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u, Or.inl ⟨⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩⟩
          have hv : tv (Sum.inr ⟨n, ⟨rfl⟩⟩) (pad a₀ (pref hn u)) :=
            (hg (pref hn u)).mpr hguard
          rwa [pad_pref_of_canon h₀ hn hu] at hv
        · refine ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u, Or.inr ⟨⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩⟩
          intro hv
          rw [← pad_pref_of_canon h₀ hn hu] at hv
          exact hguard ((hg (pref hn u)).mp hv)
  | n, .rel R ts, hctx, tv => by
      have hn : n ≤ D := (le_maxCtx _).trans hctx
      cases R with
      | inl r =>
          constructor
          · intro hsat w
            constructor
            · intro hv
              by_contra hguard
              obtain ⟨v, x, ⟨hlit, -⟩ | ⟨hlit, hx⟩⟩ :=
                hsat n ⟨rfl⟩ 1 (pad a₀ w)
                  ⟨canon_pad h₀ n w, Or.inr ⟨rfl, by rwa [pref_pad]⟩⟩
              · obtain ⟨-, -, htk | hfk⟩ := hlit
                · exact absurd htk.2 (by decide)
                · exact absurd hfk.1 (by decide)
              · obtain ⟨rfl, rfl, -⟩ := hlit
                exact hx hv
            · intro hguard
              obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
                hsat n ⟨rfl⟩ 0 (pad a₀ w)
                  ⟨canon_pad h₀ n w, Or.inl ⟨rfl, by rwa [pref_pad]⟩⟩
              · obtain ⟨rfl, rfl, -⟩ := hlit
                exact hx
              · obtain ⟨-, -, htk | hfk⟩ := hlit
                · exact absurd htk.1 (by decide)
                · exact absurd hfk.2 (by decide)
          · intro hg m p k u hcl
            obtain ⟨rfl⟩ := p
            obtain ⟨hu, ⟨rfl, hguard⟩ | ⟨rfl, hguard⟩⟩ := hcl
            · refine ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u,
                Or.inl ⟨⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩⟩
              have hv : tv (Sum.inr ⟨n, ⟨rfl⟩⟩) (pad a₀ (pref hn u)) :=
                (hg (pref hn u)).mpr hguard
              rwa [pad_pref_of_canon h₀ hn hu] at hv
            · refine ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u,
                Or.inr ⟨⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩⟩
              intro hv
              rw [← pad_pref_of_canon h₀ hn hu] at hv
              exact hguard ((hg (pref hn u)).mp hv)
      | inr r =>
          obtain ⟨i, hi⟩ := r
          subst hi
          have hAL : ∀ (w : Fin n → A) (x : Fin D → A),
              atomLit (D := D) ts w x ↔
                x = pad a₀
                  (fun k => (termToL (ts k)).realize (Sum.elim isEmptyElim w)) := by
            intro w x
            constructor
            · rintro ⟨hcx, hval⟩
              funext j
              rw [pad]
              split_ifs with hj
              · exact hval j hj
              · exact ((h₀ (x j)).antisymm (hcx j (not_lt.mp hj) a₀)).symm
            · rintro rfl
              refine ⟨canon_pad h₀ _ _, fun j hj => ?_⟩
              rw [pad, dite_eq_left hj]
          constructor
          · intro hsat w
            constructor
            · intro hv
              obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
                hsat n ⟨rfl⟩ 0 (pad a₀ w) ⟨canon_pad h₀ n w, Or.inl rfl⟩
              · rcases hlit with ⟨-, -, hsk⟩ | ⟨rfl, hal, -⟩
                · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                  · exact absurd hf (by decide)
                  · exact absurd hk (by decide)
                · rw [pref_pad, hAL w x] at hal
                  subst hal
                  exact hx
              · rcases hlit with ⟨rfl, rfl, -⟩ | ⟨-, -, hsk⟩
                · exact absurd hv hx
                · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                  · exact absurd hf (by decide)
                  · exact absurd hk (by decide)
            · intro hatom
              obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
                hsat n ⟨rfl⟩ 1 (pad a₀ w) ⟨canon_pad h₀ n w, Or.inr rfl⟩
              · rcases hlit with ⟨rfl, rfl, -⟩ | ⟨-, -, hsk⟩
                · exact hx
                · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                  · exact absurd hk (by decide)
                  · exact absurd hf (by decide)
              · rcases hlit with ⟨-, -, hsk⟩ | ⟨rfl, hal, -⟩
                · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                  · exact absurd hk (by decide)
                  · exact absurd hf (by decide)
                · rw [pref_pad, hAL w x] at hal
                  subst hal
                  exact absurd hatom hx
          · intro hg m p k u hcl
            obtain ⟨rfl⟩ := p
            obtain ⟨hu, hk⟩ := hcl
            have hgu : tv (Sum.inr ⟨n, ⟨rfl⟩⟩) (pad a₀ (pref hn u)) ↔
                tv (Sum.inl i) (pad a₀ (fun k =>
                  (termToL (ts k)).realize (Sum.elim isEmptyElim (pref hn u)))) :=
              hg (pref hn u)
            rw [pad_pref_of_canon h₀ hn hu] at hgu
            rcases hk with rfl | rfl
            · by_cases hv : tv (Sum.inr ⟨n, ⟨rfl⟩⟩) u
              · refine ⟨Sum.inl i, _,
                  Or.inl ⟨Or.inr ⟨rfl, (hAL (pref hn u) _).mpr rfl,
                    Or.inl ⟨rfl, rfl⟩⟩, hgu.mp hv⟩⟩
              · exact ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u,
                  Or.inr ⟨Or.inl ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩, hv⟩⟩
            · by_cases hv : tv (Sum.inr ⟨n, ⟨rfl⟩⟩) u
              · exact ⟨Sum.inr ⟨n, ⟨rfl⟩⟩, u,
                  Or.inl ⟨Or.inl ⟨rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩, hv⟩⟩
              · refine ⟨Sum.inl i, _,
                  Or.inr ⟨Or.inr ⟨rfl, (hAL (pref hn u) _).mpr rfl,
                    Or.inr ⟨rfl, rfl⟩⟩, fun h => hv (hgu.mpr h)⟩⟩
  | n, .imp f₁ f₂, hctx, tv => by
      have hn : n ≤ D := (le_maxCtx (f₁.imp f₂)).trans hctx
      have h₁ : maxCtx f₁ ≤ D := (le_max_left _ _).trans hctx
      have h₂ : maxCtx f₂ ≤ D := (le_max_right _ _).trans hctx
      constructor
      · intro hsat
        refine ⟨fun w => ?_, ?_, ?_⟩
        · -- the root gate, from the three root clauses at `pad a₀ w`
          have e0 : ¬tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ w) ∨
              ¬tv (Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩) (pad a₀ w) ∨
              tv (Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩) (pad a₀ w) := by
            obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
              hsat n (Sum.inl ⟨rfl⟩) 0 (pad a₀ w) (canon_pad h₀ n w)
            · obtain ⟨rfl, hv⟩ := hlit
              rcases hv with ⟨rfl, hsk⟩ | ⟨rfl, hsk⟩ | ⟨rfl, -⟩
              · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                · exact absurd hf (by decide)
                · rcases hk with hk | hk <;> exact absurd hk (by decide)
              · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                · exact absurd hf (by decide)
                · exact absurd hk (by decide)
              · exact Or.inr (Or.inr hx)
            · obtain ⟨rfl, hv⟩ := hlit
              rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hsk⟩
              · exact Or.inl hx
              · exact Or.inr (Or.inl hx)
              · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                · exact absurd hf (by decide)
                · exact absurd hk (by decide)
          have e1 : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ w) ∨
              tv (Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩) (pad a₀ w) := by
            obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
              hsat n (Sum.inl ⟨rfl⟩) 1 (pad a₀ w) (canon_pad h₀ n w)
            · obtain ⟨rfl, hv⟩ := hlit
              rcases hv with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, hsk⟩
              · exact Or.inl hx
              · exact Or.inr hx
              · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                · exact absurd hk (by decide)
                · exact absurd hf (by decide)
            · obtain ⟨rfl, hv⟩ := hlit
              rcases hv with ⟨rfl, hsk⟩ | ⟨rfl, hsk⟩ | ⟨rfl, hsk⟩
              · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                · exact absurd hk (by decide)
                · exact absurd hf (by decide)
              · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                · exact absurd hk (by decide)
                · exact absurd hf (by decide)
              · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                · exact absurd hf (by decide)
                · exact absurd hk (by decide)
          have e2 : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ w) ∨
              ¬tv (Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩) (pad a₀ w) := by
            obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
              hsat n (Sum.inl ⟨rfl⟩) 2 (pad a₀ w) (canon_pad h₀ n w)
            · obtain ⟨rfl, hv⟩ := hlit
              rcases hv with ⟨rfl, -⟩ | ⟨rfl, hsk⟩ | ⟨rfl, hsk⟩
              · exact Or.inl hx
              · rcases hsk with ⟨hf, -⟩ | ⟨-, hk⟩
                · exact absurd hf (by decide)
                · exact absurd hk (by decide)
              · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                · exact absurd hk (by decide)
                · exact absurd hf (by decide)
            · obtain ⟨rfl, hv⟩ := hlit
              rcases hv with ⟨rfl, hsk⟩ | ⟨rfl, hsk⟩ | ⟨rfl, -⟩
              · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                · exact absurd hk (by decide)
                · exact absurd hf (by decide)
              · rcases hsk with ⟨-, hk⟩ | ⟨hf, -⟩
                · exact absurd hk (by decide)
                · exact absurd hf (by decide)
              · exact Or.inr hx
          constructor
          · intro hg hca
            rcases e0 with h | h | h
            · exact absurd hg h
            · exact absurd hca h
            · exact h
          · intro hab
            rcases e1 with h | h
            · exact h
            · rcases e2 with h' | h'
              · exact h'
              · exact absurd (hab h) h'
        · refine (satCond_iff_gates h₀ harity f₁ h₁
            (fun v x => tv (match v with
              | Sum.inl i => Sum.inl i
              | Sum.inr σ => Sum.inr ⟨σ.1, Sum.inr (Sum.inl σ.2)⟩) x)).mp ?_
          intro m q k u hcl
          obtain ⟨v, x, hor⟩ := hsat m (Sum.inr (Sum.inl q)) k u hcl
          rcases v with i | ⟨m', p'⟩
          · exact ⟨Sum.inl i, x, hor⟩
          · rcases p' with ⟨h'⟩ | q' | q'
            · rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim
            · exact ⟨Sum.inr ⟨m', q'⟩, x, hor⟩
            · rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim
        · refine (satCond_iff_gates h₀ harity f₂ h₂
            (fun v x => tv (match v with
              | Sum.inl i => Sum.inl i
              | Sum.inr σ => Sum.inr ⟨σ.1, Sum.inr (Sum.inr σ.2)⟩) x)).mp ?_
          intro m q k u hcl
          obtain ⟨v, x, hor⟩ := hsat m (Sum.inr (Sum.inr q)) k u hcl
          rcases v with i | ⟨m', p'⟩
          · exact ⟨Sum.inl i, x, hor⟩
          · rcases p' with ⟨h'⟩ | q' | q'
            · rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim
            · rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim
            · exact ⟨Sum.inr ⟨m', q'⟩, x, hor⟩
      · rintro ⟨hroot, hg₁, hg₂⟩ m p k u hcl
        obtain ⟨⟨rfl⟩⟩ | q | q := p
        · have hgw : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ (pref hn u)) ↔
              (tv (Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩) (pad a₀ (pref hn u)) →
                tv (Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩) (pad a₀ (pref hn u))) :=
            hroot (pref hn u)
          rw [pad_pref_of_canon h₀ hn hcl] at hgw
          fin_cases k
          · by_cases hca : tv (Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩) u
            · by_cases hg : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) u
              · exact ⟨Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩, u,
                  Or.inl ⟨⟨rfl, Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩,
                    hgw.mp hg hca⟩⟩
              · exact ⟨Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩, u,
                  Or.inr ⟨⟨rfl, Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩⟩, hg⟩⟩
            · exact ⟨Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩, u,
                Or.inr ⟨⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩, hca⟩⟩
          · by_cases hg : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) u
            · exact ⟨Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩, u,
                Or.inl ⟨⟨rfl, Or.inl ⟨rfl, Or.inr ⟨rfl, Or.inl rfl⟩⟩⟩, hg⟩⟩
            · have hca : tv (Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩) u := by
                by_contra hca
                exact hg (hgw.mpr fun h => absurd h hca)
              exact ⟨Sum.inr ⟨n, Sum.inr (Sum.inl (rootAt f₁))⟩, u,
                Or.inl ⟨⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩, hca⟩⟩
          · by_cases hg : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) u
            · exact ⟨Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩, u,
                Or.inl ⟨⟨rfl, Or.inl ⟨rfl, Or.inr ⟨rfl, Or.inr rfl⟩⟩⟩, hg⟩⟩
            · have hcb : ¬tv (Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩) u := by
                intro hcb
                exact hg (hgw.mpr fun _ => hcb)
              exact ⟨Sum.inr ⟨n, Sum.inr (Sum.inr (rootAt f₂))⟩, u,
                Or.inr ⟨⟨rfl, Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)⟩, hcb⟩⟩
        · obtain ⟨v₁, x, hor⟩ :=
            (satCond_iff_gates h₀ harity f₁ h₁
              (fun v x => tv (match v with
                | Sum.inl i => Sum.inl i
                | Sum.inr σ => Sum.inr ⟨σ.1, Sum.inr (Sum.inl σ.2)⟩) x)).mpr
              hg₁ m q k u hcl
          rcases v₁ with i | ⟨m', q'⟩
          · exact ⟨Sum.inl i, x, hor⟩
          · exact ⟨Sum.inr ⟨m', Sum.inr (Sum.inl q')⟩, x, hor⟩
        · obtain ⟨v₂, x, hor⟩ :=
            (satCond_iff_gates h₀ harity f₂ h₂
              (fun v x => tv (match v with
                | Sum.inl i => Sum.inl i
                | Sum.inr σ => Sum.inr ⟨σ.1, Sum.inr (Sum.inr σ.2)⟩) x)).mpr
              hg₂ m q k u hcl
          rcases v₂ with i | ⟨m', q'⟩
          · exact ⟨Sum.inl i, x, hor⟩
          · exact ⟨Sum.inr ⟨m', Sum.inr (Sum.inr q')⟩, x, hor⟩
  | n, .all f, hctx, tv => by
      have hn : n ≤ D := (le_maxCtx f.all).trans hctx
      have hn1 : n + 1 ≤ D := (le_maxCtx f).trans hctx
      have hnD : n < D := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn1
      constructor
      · intro hsat
        refine ⟨fun w => ⟨?_, ?_⟩, ?_⟩
        · -- from the per-element clauses
          intro hg a
          obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
            hsat n (Sum.inl ⟨rfl⟩) 0 (pad a₀ (Fin.snoc w a))
              (Or.inl ⟨rfl, canon_pad h₀ (n + 1) (Fin.snoc w a)⟩)
          · rcases hlit with ⟨-, ⟨hf, -⟩ | ⟨-, rfl, rfl⟩⟩ | ⟨hk, -⟩
            · exact absurd hf (by decide)
            · exact hx
            · exact absurd hk (by decide)
          · rcases hlit with ⟨-, ⟨-, rfl, hag, hcx⟩ | ⟨hf, -⟩⟩ | ⟨hk, -⟩
            · have h' := eq_pad_of_canon_agree h₀ hn hcx hag
              rw [pref_pad_snoc] at h'
              subst h'
              exact absurd hg hx
            · exact absurd hf (by decide)
            · exact absurd hk (by decide)
        · -- from the wide clause
          intro hall
          obtain ⟨v, x, ⟨hlit, hx⟩ | ⟨hlit, hx⟩⟩ :=
            hsat n (Sum.inl ⟨rfl⟩) 1 (pad a₀ w) (Or.inr ⟨rfl, canon_pad h₀ n w⟩)
          · rcases hlit with ⟨hk, -⟩ | ⟨-, ⟨-, rfl, rfl⟩ | ⟨hf, -⟩⟩
            · exact absurd hk (by decide)
            · exact hx
            · exact absurd hf (by decide)
          · rcases hlit with ⟨hk, -⟩ | ⟨-, ⟨hf, -⟩ | ⟨-, rfl, hag, hcx⟩⟩
            · exact absurd hk (by decide)
            · exact absurd hf (by decide)
            · have hx' : x = pad a₀ (Fin.snoc (pref hnD.le (pad a₀ w)) (x ⟨n, hnD⟩)) :=
                eq_pad_snoc_of_canon_agree h₀ hnD hcx hag
              rw [pref_pad] at hx'
              rw [hx'] at hx
              exact absurd (hall (x ⟨n, hnD⟩)) hx
        · refine (satCond_iff_gates h₀ harity f hctx
            (fun v x => tv (match v with
              | Sum.inl i => Sum.inl i
              | Sum.inr σ => Sum.inr ⟨σ.1, Sum.inr σ.2⟩) x)).mp ?_
          intro m q k u hcl
          obtain ⟨v, x, hor⟩ := hsat m (Sum.inr q) k u hcl
          rcases v with i | ⟨m', p'⟩
          · exact ⟨Sum.inl i, x, hor⟩
          · rcases p' with ⟨h'⟩ | q'
            · rcases hor with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim
            · exact ⟨Sum.inr ⟨m', q'⟩, x, hor⟩
      · rintro ⟨hroot, hgf⟩ m p k u hcl
        obtain ⟨⟨rfl⟩⟩ | q := p
        · rcases hcl with ⟨rfl, hu⟩ | ⟨rfl, hu⟩
          · -- per-element clause, `u` canonical at `n + 1`
            have hu' : u = pad a₀
                (Fin.snoc (Fin.init (pref hn1 u)) (pref hn1 u (Fin.last n))) := by
              rw [Fin.snoc_init_self]
              exact (pad_pref_of_canon h₀ hn1 hu).symm
            set w := Fin.init (pref hn1 u) with hw
            set a := pref hn1 u (Fin.last n) with ha
            have hgw : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ w) ↔
                ∀ a', tv (Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩)
                  (pad a₀ (Fin.snoc w a')) :=
              hroot w
            by_cases hg : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ w)
            · refine ⟨Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩, u,
                Or.inl ⟨Or.inl ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩, ?_⟩⟩
              have hchild := hgw.mp hg a
              rwa [← hu'] at hchild
            · refine ⟨Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩, pad a₀ w,
                Or.inr ⟨Or.inl ⟨rfl, Or.inl ⟨rfl, rfl, ?_, canon_pad h₀ n w⟩⟩, hg⟩⟩
              rw [hu']
              exact agree_pad_pad a₀ w a
          · -- wide clause, `u` canonical at `n`
            have hu' : pad a₀ (pref hn u) = u := pad_pref_of_canon h₀ hn hu
            have hgw : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) (pad a₀ (pref hn u)) ↔
                ∀ a', tv (Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩)
                  (pad a₀ (Fin.snoc (pref hn u) a')) :=
              hroot (pref hn u)
            rw [hu'] at hgw
            by_cases hg : tv (Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩) u
            · exact ⟨Sum.inr ⟨n, Sum.inl ⟨rfl⟩⟩, u,
                Or.inl ⟨Or.inr ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩, hg⟩⟩
            · obtain ⟨a', hna⟩ := not_forall.mp fun hall => hg (hgw.mpr hall)
              refine ⟨Sum.inr ⟨n + 1, Sum.inr (rootAt f)⟩,
                pad a₀ (Fin.snoc (pref hn u) a'),
                Or.inr ⟨Or.inr ⟨rfl, Or.inr ⟨rfl, rfl, ?_,
                  canon_pad h₀ (n + 1) _⟩⟩, hna⟩⟩
              exact agree_pad_snoc_pref a₀ a' hn u
        · obtain ⟨v₁, x, hor⟩ :=
            (satCond_iff_gates h₀ harity f hctx
              (fun v x => tv (match v with
                | Sum.inl i => Sum.inl i
                | Sum.inr σ => Sum.inr ⟨σ.1, Sum.inr σ.2⟩) x)).mpr
              hgf m q k u hcl
          rcases v₁ with i | ⟨m', q'⟩
          · exact ⟨Sum.inl i, x, hor⟩
          · exact ⟨Sum.inr ⟨m', Sum.inr q'⟩, x, hor⟩

end Correctness

end Tseitin

end DescriptiveComplexity
