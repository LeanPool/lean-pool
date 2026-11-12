/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import LeanPool.DescriptiveCounting.FixedPoint
public import LeanPool.DescriptiveCounting.OrderWalk
public import LeanPool.DescriptiveCounting.Hierarchy
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Lattice
import all LeanPool.DescriptiveCounting.Complexity
import all LeanPool.DescriptiveCounting.FixedPoint
import all LeanPool.DescriptiveCounting.OrderWalk
import all LeanPool.DescriptiveCounting.Padding

/-!
# FO(LFP) = SO-Horn: the translation into the fragment

The hard half of Grädel's equivalence ([Grädel 1992][gradel1992capturing]):
every FO(LFP) definable problem is SO-Horn definable
(`DescriptiveComplexity.LFPDefinable.sigmaSOHornDefinable`). With the easy half
`DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` the two formalisms are
interchangeable (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`), so the
fragment inherits the closure property that only a full logic has by
construction: **SO-Horn definability is closed under complement**
(`DescriptiveComplexity.SigmaSOHornDefinable.compl`), and level 0 of the polynomial
hierarchy collapses, `Π₀ᵖ = Σ₀ᵖ` (`DescriptiveComplexity.piP_zero_eq`) – polynomial
time, as defined by the Horn fragment, is closed under complement.

## The construction

Where a `Σ₁` certificate could *guess* a fixed point and its derivation order,
a Horn program must *derive* them. The program built here
(`DescriptiveComplexity.LFPHorn.trProg`) has one goal clause – “the output sentence is
not false” – and rules computing, as its least model, the entire evaluation of
the FO(LFP) definition (`DescriptiveComplexity.LFPHorn.canonAssign`):

* the **fixed point** itself, on a copy of the original block, by the original
  rules (`DescriptiveComplexity.LFPHorn.liftedRules`);
* the **complement of the fixed point**, the part a positive formalism cannot
  see directly: relations `N j i (t, x)` – the atom `i x` is *not yet* derived
  at stage `(j, t)` – for stages indexed lexicographically by `hc + 1` static
  copies of the tuples `t ∈ A^hm` (`DescriptiveComplexity.LFPHorn.hs` copies suffice on
  *every* nonempty structure, where tuples alone would fail on one-element
  universes: `(hc+1)·n^hm` always exceeds the `Σᵢ n^{arityᵢ}` rounds after
  which the stages stabilize, `DescriptiveComplexity.derivesIn_iff_derives_of_card_le`).
  The base rules populate `N` at the bottom stage; the step rules carry an
  underived atom to the next stage when *no* rule instance derives it, that
  unbounded conjunction over the valuations being assembled by the non-firing
  accumulators `NF j (c, a) (t, x, w)` walking the lexicographic order of the
  valuations `w ∈ A^k` – the technique of
  `DescriptiveComplexity.Problems.HornSat.Definability`, applied to a rule system
  rather than one clause body, with the order machinery of
  `DescriptiveComplexity.OrderWalk`;
* an **evaluator for the output sentence**: truth and falsity relations for
  every subformula (`DescriptiveComplexity.subs` lists them; no recursion over the
  syntax is needed in the index type), with falsity of a fixed-point atom read
  from `N` at the last stage, implication evaluated clausewise, and the
  universal quantifier assembled by one more accumulator along the order.

Correctness is the identity between the least model of this program and the
canonical assignment: soundness (`DescriptiveComplexity.LFPHorn.trRules_sound`, the
canonical assignment satisfies every rule) gives one inclusion and makes the
canonical assignment the witness when the output holds; completeness (the
`DescriptiveComplexity.LFPHorn.derives_n`/`derives_nf`/`derives_eval` inductions along
stages, valuations and subformulas) shows every canonical fact derivable, so
that any satisfying assignment of the program contains it – in particular the
falsity of the output, when false, always reaches the goal clause
(`DescriptiveComplexity.LFPHorn.holds_iff_exists`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Stripping a relational summand out of terms -/

section Strip

variable {L₀ R : Language.{0, 0}} [R.IsRelational] {α : Type}

/-- A term over `L₀.sum R` with `R` relational is a term over `L₀`: the
summand contributes no function symbols. -/
def stripTerm : (L₀.sum R).Term α → L₀.Term α
  | .var a => .var a
  | .func (Sum.inl f) ts => .func f fun i => stripTerm (ts i)
  | .func (Sum.inr f) _ => isEmptyElim f

private theorem realize_stripTerm {A : Type} [L₀.Structure A] [R.Structure A] (v : α → A)
    (t : (L₀.sum R).Term α) :
    (stripTerm t).realize v = Term.realize (L := L₀.sum R) v t := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    cases f with
    | inl f =>
      rw [stripTerm]
      simp only [Term.realize_func]
      exact congrArg _ (funext fun i => ih i)
    | inr f => exact isEmptyElim f

end Strip

/-! ### The subformula closure of a sentence, as a list -/

section Subformulas

variable {Lg : Language.{0, 0}}

/-- The subformulas of a bounded formula over `Empty`, each with its binder
depth, as a list; the formula itself is included. -/
def subs : ∀ {n : ℕ}, Lg.BoundedFormula Empty n → List (Σ n' : ℕ, Lg.BoundedFormula Empty n')
  | n, .falsum => [⟨n, .falsum⟩]
  | n, .equal t u => [⟨n, .equal t u⟩]
  | n, .rel r ts => [⟨n, .rel r ts⟩]
  | n, .imp a b => ⟨n, a.imp b⟩ :: (subs a ++ subs b)
  | n, .all a => ⟨n, a.all⟩ :: subs a

theorem self_mem_subs {n : ℕ} (φ : Lg.BoundedFormula Empty n) : ⟨n, φ⟩ ∈ subs φ := by
  cases φ <;> simp [subs]

theorem subs_trans {n : ℕ} {φ : Lg.BoundedFormula Empty n}
    {x : Σ n', Lg.BoundedFormula Empty n'} (hx : x ∈ subs φ) : subs x.2 ⊆ subs φ := by
  obtain ⟨nx, ψ⟩ := x
  induction φ with
  | falsum =>
    rw [subs, List.mem_singleton] at hx
    obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
    obtain rfl := eq_of_heq h
    exact fun y hy => hy
  | equal t u =>
    rw [subs, List.mem_singleton] at hx
    obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
    obtain rfl := eq_of_heq h
    exact fun y hy => hy
  | rel r ts =>
    rw [subs, List.mem_singleton] at hx
    obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
    obtain rfl := eq_of_heq h
    exact fun y hy => hy
  | imp a b iha ihb =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
      obtain rfl := eq_of_heq h
      exact fun y hy => hy
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.Subset.trans (iha hx)
          (List.subset_cons_of_subset _ (List.subset_append_left _ _))
      · exact List.Subset.trans (ihb hx)
          (List.subset_cons_of_subset _ (List.subset_append_right _ _))
  | all a iha =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · obtain ⟨rfl, h⟩ := Sigma.mk.injEq .. ▸ hx
      obtain rfl := eq_of_heq h
      exact fun y hy => hy
    · exact List.Subset.trans (iha hx) (List.subset_cons_self _ _)

theorem left_mem_subs_imp {n : ℕ} (a b : Lg.BoundedFormula Empty n) :
    (⟨n, a⟩ : Σ n', Lg.BoundedFormula Empty n') ∈ subs (a.imp b) := by
  rw [subs, List.mem_cons]
  exact Or.inr (List.mem_append_left _ (self_mem_subs a))

theorem right_mem_subs_imp {n : ℕ} (a b : Lg.BoundedFormula Empty n) :
    (⟨n, b⟩ : Σ n', Lg.BoundedFormula Empty n') ∈ subs (a.imp b) := by
  rw [subs, List.mem_cons]
  exact Or.inr (List.mem_append_right _ (self_mem_subs b))

theorem mem_subs_all {n : ℕ} (a : Lg.BoundedFormula Empty (n + 1)) :
    (⟨n + 1, a⟩ : Σ n', Lg.BoundedFormula Empty n') ∈ subs a.all := by
  rw [subs, List.mem_cons]
  exact Or.inr (self_mem_subs a)

/-- A bound on the binder depths of the subformula closure. -/
def ctxB : ∀ {n : ℕ}, Lg.BoundedFormula Empty n → ℕ
  | _, .imp a b => max (ctxB a) (ctxB b)
  | _, .all a => ctxB a
  | n, _ => n

private theorem le_ctxB : ∀ {n : ℕ} (φ : Lg.BoundedFormula Empty n), n ≤ ctxB φ
  | _, .falsum => le_rfl
  | _, .equal _ _ => le_rfl
  | _, .rel _ _ => le_rfl
  | _, .imp a _ => le_trans (le_ctxB a) (le_max_left _ _)
  | _, .all a => le_trans (Nat.le_succ _) (le_ctxB a)

private theorem fst_le_ctxB {n : ℕ} {φ : Lg.BoundedFormula Empty n}
    {x : Σ n', Lg.BoundedFormula Empty n'} (hx : x ∈ subs φ) : x.1 ≤ ctxB φ := by
  induction φ with
  | falsum =>
    rw [subs, List.mem_singleton] at hx
    rw [congrArg Sigma.fst hx]
    exact le_rfl
  | equal t u =>
    rw [subs, List.mem_singleton] at hx
    rw [congrArg Sigma.fst hx]
    exact le_rfl
  | rel r ts =>
    rw [subs, List.mem_singleton] at hx
    rw [congrArg Sigma.fst hx]
    exact le_rfl
  | imp a b iha ihb =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [congrArg Sigma.fst hx]
      exact le_ctxB _
    · rcases List.mem_append.mp hx with hx | hx
      · exact le_trans (iha hx) (le_max_left _ _)
      · exact le_trans (ihb hx) (le_max_right _ _)
  | all a iha =>
    rw [subs, List.mem_cons] at hx
    rcases hx with hx | hx
    · rw [congrArg Sigma.fst hx]
      exact le_ctxB _
    · exact iha hx

end Subformulas

namespace LFPHorn

variable {L : Language.{0, 0}} (d : LFPDef L)

/-! ### The headed clauses of the rule system -/

/-- The rules with a head, paired with their heads: goal clauses derive
nothing, so only these participate in the stage machinery. -/
noncomputable def headed :
    List (HornClause (L.sum Language.order) d.B d.k × SOAtom d.B d.k) :=
  d.rules.filterMap fun c => c.head.map fun a => (c, a)

private theorem mem_headed {ca : HornClause (L.sum Language.order) d.B d.k × SOAtom d.B d.k} :
    ca ∈ headed d ↔ ca.1 ∈ d.rules ∧ ca.1.head = some ca.2 := by
  rw [headed, List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hmap⟩
    rw [Option.map_eq_some_iff] at hmap
    obtain ⟨a, ha, rfl⟩ := hmap
    exact ⟨hc, ha⟩
  · rintro ⟨hc, hh⟩
    exact ⟨ca.1, hc, by rw [hh, Option.map_some]⟩

/-! ### Dimensions of the construction -/

/-- The width of a stage tuple: the arity bound of the block. -/
noncomputable def hm : ℕ := blockArityBound d.B

/-- The number of copies of the stage relations, minus one. -/
noncomputable def hc : ℕ := Nat.card d.B.ι

/-- The number of copies of the stage relations: enough for `(hc + 1) · n^hm`
stages to exceed the number of atoms of the block on every nonempty
structure. -/
noncomputable def hs : ℕ := hc d + 1

/-- The number of variables reserved for evaluating the output sentence. -/
noncomputable def hX : ℕ := ctxB d.out

/-- The universally quantified first-order variables shared by all clauses of
the translated program: three stage-tuple blocks, two valuation blocks, the
evaluation block, and one spare. -/
noncomputable def kk : ℕ := 3 * hm d + 2 * d.k + hX d + 1

/-- The binder depth of a subformula of the output is within the evaluation
block. (A dedicated lemma, so that proof terms in the rules carry exactly this
type.) -/
theorem ctx_le_hX {n : ℕ}
    {ψ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n}
    (h : (⟨n, ψ⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out) : n ≤ hX d :=
  fst_le_ctxB h

/-- The left subformula of an implication in the output. -/
theorem left_mem_out {n : ℕ}
    {a b : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n}
    (h : (⟨n, a.imp b⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out) :
    (⟨n, a⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
      subs d.out :=
  subs_trans h (left_mem_subs_imp a b)

/-- The right subformula of an implication in the output. -/
theorem right_mem_out {n : ℕ}
    {a b : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n}
    (h : (⟨n, a.imp b⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out) :
    (⟨n, b⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
      subs d.out :=
  subs_trans h (right_mem_subs_imp a b)

/-- The body of a universally quantified subformula of the output. -/
theorem all_mem_out {n : ℕ}
    {a : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1)}
    (h : (⟨n, a.all⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out) :
    (⟨n + 1, a⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out :=
  subs_trans h (mem_subs_all a)

/-! ### The block of the translation -/

/-- Index of the subformula relations: a subformula of the output sentence,
with its binder depth. -/
def SubIx : Type :=
  {x : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n' // x ∈ subs d.out}

/-- Index of the non-firing relations: a headed clause of the rule system. -/
noncomputable def HIx : Type := {ca // ca ∈ headed d}

instance : Finite (SubIx d) := (List.finite_toSet _).to_subtype
instance : Finite (HIx d) := (List.finite_toSet _).to_subtype

/-- The relation variables of the translated program: the original block
(computing the fixed point), the stage complements `N`, the non-firing
accumulators `NF`, the subformula truth/falsity relations, and the
`∀`-accumulators. -/
abbrev TrIx : Type :=
  d.B.ι ⊕ (Fin (hs d) × d.B.ι) ⊕ (Fin (hs d) × HIx d) ⊕ ((SubIx d × Bool) ⊕ SubIx d)

/-- The original relation variables. -/
abbrev rIx (i : d.B.ι) : TrIx d := Sum.inl i

/-- `N j i (t, x)`: at stage `(j, t)`, the atom `i x` is *not yet* derived. -/
abbrev nIx (j : Fin (hs d)) (i : d.B.ι) : TrIx d := Sum.inr (Sum.inl (j, i))

/-- `NF j (c, a) (t, x, w)`: no valuation up to `w` fires the clause `c` at
stage `(j, t)` to derive the atom `a.idx x`. -/
abbrev nfIx (j : Fin (hs d)) (ca : HIx d) : TrIx d := Sum.inr (Sum.inr (Sum.inl (j, ca)))

/-- Truth (`true`) and falsity (`false`) of a subformula of the output. -/
abbrev tfIx (x : SubIx d) (b : Bool) : TrIx d := Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, b))))

/-- The accumulator of a universally quantified subformula. -/
abbrev acIx (x : SubIx d) : TrIx d := Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))

/-- The arities: stage relations carry a stage tuple in front, non-firing
relations also a valuation tuple behind, subformula relations their binder
depth. -/
noncomputable def trArity : TrIx d → ℕ
  | Sum.inl i => d.B.arity i
  | Sum.inr (Sum.inl (_, i)) => hm d + d.B.arity i
  | Sum.inr (Sum.inr (Sum.inl (_, ca))) => hm d + d.B.arity ca.1.2.idx + d.k
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, _)))) => x.1.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) => x.1.1 + 1

/-- The block of the translated program. -/
noncomputable def trBlock : SOBlock := ⟨TrIx d, trArity d⟩

/-! ### The shared first-order variables and their layout

All clauses of the translated program share `kk d` universally quantified
variables: three stage-tuple blocks (current stage, next stage, and the atom
tuple), two valuation blocks for the rule being tested, a block for the
free variables of the output's subformulas, and one spare variable for the
`∀`-accumulators. -/

/-- The current stage tuple `t`. -/
noncomputable def vT1 (q : Fin (hm d)) : Fin (kk d) :=
  ⟨q, by have := q.isLt; simp only [kk]; omega⟩

/-- The next stage tuple `t'`. -/
noncomputable def vT2 (q : Fin (hm d)) : Fin (kk d) :=
  ⟨hm d + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The atom tuple `x` (also the interpreted arguments `y` of the output's
fixed-point atoms). -/
noncomputable def vX (q : Fin (hm d)) : Fin (kk d) :=
  ⟨2 * hm d + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The first valuation block `w`. -/
noncomputable def vW1 (q : Fin d.k) : Fin (kk d) :=
  ⟨3 * hm d + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The second valuation block `w'`. -/
noncomputable def vW2 (q : Fin d.k) : Fin (kk d) :=
  ⟨3 * hm d + d.k + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The evaluation block `ē`, holding the free variables of a subformula. -/
noncomputable def vE (q : Fin (hX d)) : Fin (kk d) :=
  ⟨3 * hm d + 2 * d.k + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The spare variable, the accumulator's predecessor. -/
noncomputable def vS : Fin (kk d) :=
  ⟨3 * hm d + 2 * d.k + hX d, by simp only [kk]; omega⟩

/-- The atom tuple of a relation variable `i`, inside the `x` block. -/
noncomputable def xa (i : d.B.ι) (q : Fin (d.B.arity i)) : Fin (kk d) :=
  vX d ⟨q, lt_of_lt_of_le q.isLt (arity_le_blockArityBound d.B i)⟩

/-- The first `n` variables of the evaluation block. -/
noncomputable def eSel {n : ℕ} (hn : n ≤ hX d) (q : Fin n) : Fin (kk d) :=
  vE d ⟨q, lt_of_lt_of_le q.isLt hn⟩

/-- The first copy. -/
noncomputable def j0 : Fin (hs d) := ⟨0, by simp only [hs]; omega⟩

/-- The last copy. -/
noncomputable def jTop : Fin (hs d) := ⟨hc d, by simp only [hs]; omega⟩

/-! ### Atom builders -/

/-- An atom of an original relation variable. -/
noncomputable def rAt (i : d.B.ι) (sel : Fin (d.B.arity i) → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨rIx d i, sel⟩

/-- An atom `N j i (t, x)`. -/
noncomputable def nAt (j : Fin (hs d)) (i : d.B.ι) (ts : Fin (hm d) → Fin (kk d))
    (xs : Fin (d.B.arity i) → Fin (kk d)) : SOAtom (trBlock d) (kk d) :=
  ⟨nIx d j i, Fin.addCases ts xs⟩

/-- An atom `NF j (c, a) (t, x, w)`. -/
noncomputable def nfAt (j : Fin (hs d)) (ca : HIx d) (ts : Fin (hm d) → Fin (kk d))
    (xs : Fin (d.B.arity ca.1.2.idx) → Fin (kk d)) (ws : Fin d.k → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨nfIx d j ca, Fin.addCases (Fin.addCases ts xs) ws⟩

/-- A truth or falsity atom of a subformula. -/
noncomputable def tfAt (x : SubIx d) (b : Bool) (es : Fin x.1.1 → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨tfIx d x b, es⟩

/-- An accumulator atom of a subformula. -/
noncomputable def acAt (x : SubIx d) (es : Fin (x.1.1 + 1) → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨acIx d x, es⟩

/-! ### The rules of the translated program -/

/-- The relation variables, as a list. -/
noncomputable def iotaList : List d.B.ι :=
  (@Finset.univ d.B.ι (Fintype.ofFinite _)).toList

private theorem mem_iotaList (i : d.B.ι) : i ∈ iotaList d := by
  rw [iotaList, Finset.mem_toList]
  exact @Finset.mem_univ _ (Fintype.ofFinite _) i

/-- An original atom, over the lifted block and variables. -/
noncomputable def liftAtom (a : SOAtom d.B d.k) : SOAtom (trBlock d) (kk d) :=
  rAt d a.idx fun q => vW1 d (a.args q)

/-- An original rule, over the lifted block and variables. -/
noncomputable def liftClause (c : HornClause (L.sum Language.order) d.B d.k) :
    HornClause (L.sum Language.order) (trBlock d) (kk d) :=
  { guard := c.guard.relabel (vW1 d)
    body := c.body.map (liftAtom d)
    head := c.head.map (liftAtom d) }

/-- The original headed rules, lifted: they compute the fixed point on the
`R`-part of the block. (Goal clauses of the rule system are *not* lifted:
in FO(LFP) they derive nothing, and their content is carried by the output
sentence.) -/
noncomputable def liftedRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (headed d).map fun ca => liftClause d ca.1

/-- The stage-successor pairs of copies: within one copy, or crossing to the
next. -/
noncomputable def stagePairs : List (Fin (hs d) × Fin (hs d)) :=
  ((List.finRange (hs d)).flatMap fun j => (List.finRange (hs d)).map fun j' => (j, j')).filter
    fun p => p.1 = p.2 ∨ (p.1 : ℕ) + 1 = (p.2 : ℕ)

private theorem mem_stagePairs {j j' : Fin (hs d)} :
    (j, j') ∈ stagePairs d ↔ j = j' ∨ (j : ℕ) + 1 = (j' : ℕ) := by
  rw [stagePairs, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    simpa using h
  · intro h
    refine ⟨List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      List.mem_map.mpr ⟨j', List.mem_finRange j', rfl⟩⟩, by simpa using h⟩

/-- The guard stepping from stage `(j, t)` to stage `(j', t')`: the successor
tuple within a copy, the wrap-around between consecutive copies. -/
noncomputable def stageG (j j' : Fin (hs d)) :
    (L.sum Language.order).Formula (Fin (kk d)) :=
  if j = j' then succTupF (vT1 d) (vT2 d) else maxTupF (vT1 d) ⊓ minTupF (vT2 d)

/-- Base rules: at the first stage, nothing is derived. -/
noncomputable def nBase : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (iotaList d).map fun i =>
    { guard := minTupF (vT1 d)
      body := []
      head := some (nAt d (j0 d) i (vT1 d) (xa d i)) }

/-- Step rules: an atom underivable at a stage all of whose potential
derivations fail to fire stays underivable at the next stage. -/
noncomputable def nStep : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  open Classical in
  (stagePairs d).flatMap fun jj =>
    (iotaList d).map fun i =>
      { guard := stageG d jj.1 jj.2 ⊓ maxTupF (vW1 d)
        body := nAt d jj.1 i (vT1 d) (xa d i) ::
          (((headed d).attach.filter fun ca => ca.1.2.idx = i).map fun ca =>
            nfAt d jj.1 ca (vT1 d) (xa d ca.1.2.idx) (vW1 d))
        head := some (nAt d jj.2 i (vT2 d) (xa d i)) }

/-- The non-firing rules for one copy and one headed clause `(c, a)`: walking
the valuations `w'` along their lexicographic order, `NF (t, x, w')` is
derived when the previous accumulator holds (at the base, nothing) and the
clause does not derive `a.idx x` at valuation `w'` – because its guard fails,
because its head tuple differs from `x`, or because one of its body atoms is
not derived at the stage. -/
noncomputable def nfClauses (j : Fin (hs d)) (ca : HIx d) :
    HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  [{ guard := minTupF (vW2 d) ⊓ ∼(ca.1.1.guard.relabel (vW2 d))
     body := []
     head := some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)) },
   { guard := minTupF (vW2 d) ⊓ ∼(eqTupF (fun q => vW2 d (ca.1.2.args q)) (xa d ca.1.2.idx))
     body := []
     head := some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)) },
   { guard := succTupF (vW1 d) (vW2 d) ⊓ ∼(ca.1.1.guard.relabel (vW2 d))
     body := [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)]
     head := some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)) },
   { guard := succTupF (vW1 d) (vW2 d) ⊓
       ∼(eqTupF (fun q => vW2 d (ca.1.2.args q)) (xa d ca.1.2.idx))
     body := [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)]
     head := some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)) }] ++
  (ca.1.1.body.map fun b =>
    { guard := minTupF (vW2 d)
      body := [nAt d j b.idx (vT1 d) fun q => vW2 d (b.args q)]
      head := some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)) }) ++
  (ca.1.1.body.map fun b =>
    { guard := succTupF (vW1 d) (vW2 d)
      body := [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d),
        nAt d j b.idx (vT1 d) fun q => vW2 d (b.args q)]
      head := some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)) })

/-- All non-firing rules. -/
noncomputable def nfRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (List.finRange (hs d)).flatMap fun j => (headed d).attach.flatMap fun ca => nfClauses d j ca

/-- A term of a subformula, as a term of the guard vocabulary over the
evaluation variables. -/
noncomputable def evTerm {n : ℕ} (hn : n ≤ hX d)
    (t : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    (L.sum Language.order).Term (Fin (kk d)) :=
  (stripTerm t).relabel (Sum.elim (fun e => e.elim) (eSel d hn))

/-- The rules evaluating one subformula of the output, by shape. -/
noncomputable def evalClauses (x : SubIx d) :
    HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  match x with
  | ⟨⟨n, .falsum⟩, hmem⟩ =>
    [{ guard := ⊤
       body := []
       head := some (tfAt d ⟨⟨n, .falsum⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) }]
  | ⟨⟨n, .equal t u⟩, hmem⟩ =>
    [{ guard := Term.equal (evTerm d (ctx_le_hX d hmem) t) (evTerm d (ctx_le_hX d hmem) u)
       body := []
       head := some (tfAt d ⟨⟨n, .equal t u⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) },
     { guard := ∼(Term.equal (evTerm d (ctx_le_hX d hmem) t) (evTerm d (ctx_le_hX d hmem) u))
       body := []
       head := some (tfAt d ⟨⟨n, .equal t u⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) }]
  | ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ =>
    [{ guard := Relations.formula r fun l => evTerm d (ctx_le_hX d hmem) (ts l)
       body := []
       head := some (tfAt d ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ true
         (eSel d (ctx_le_hX d hmem))) },
     { guard := ∼(Relations.formula r fun l => evTerm d (ctx_le_hX d hmem) (ts l))
       body := []
       head := some (tfAt d ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ false
         (eSel d (ctx_le_hX d hmem))) }]
  | ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ =>
    [{ guard := listInf ((List.finRange (d.B.arity r.1)).map fun q =>
         Term.equal (Term.var (xa d r.1 q)) (evTerm d (ctx_le_hX d hmem) (ts (Fin.cast r.2 q))))
       body := [rAt d r.1 (xa d r.1)]
       head := some (tfAt d ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ true
         (eSel d (ctx_le_hX d hmem))) },
     { guard := listInf ((List.finRange (d.B.arity r.1)).map fun q =>
         Term.equal (Term.var (xa d r.1 q))
           (evTerm d (ctx_le_hX d hmem) (ts (Fin.cast r.2 q)))) ⊓ maxTupF (vT1 d)
       body := [nAt d (jTop d) r.1 (vT1 d) (xa d r.1)]
       head := some (tfAt d ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ false
         (eSel d (ctx_le_hX d hmem))) }]
  | ⟨⟨n, .imp a b⟩, hmem⟩ =>
    [{ guard := ⊤
       body := [tfAt d ⟨⟨n, a⟩, left_mem_out d hmem⟩ false (eSel d (ctx_le_hX d hmem))]
       head := some (tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) },
     { guard := ⊤
       body := [tfAt d ⟨⟨n, b⟩, right_mem_out d hmem⟩ true (eSel d (ctx_le_hX d hmem))]
       head := some (tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) },
     { guard := ⊤
       body := [tfAt d ⟨⟨n, a⟩, left_mem_out d hmem⟩ true (eSel d (ctx_le_hX d hmem)),
         tfAt d ⟨⟨n, b⟩, right_mem_out d hmem⟩ false (eSel d (ctx_le_hX d hmem))]
       head := some (tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) }]
  | ⟨⟨n, .all a⟩, hmem⟩ =>
    [{ guard := minF (eSel d (ctx_le_hX d (all_mem_out d hmem)) (Fin.last n))
       body := [tfAt d ⟨⟨n + 1, a⟩, all_mem_out d hmem⟩ true
         (eSel d (ctx_le_hX d (all_mem_out d hmem)))]
       head := some (acAt d ⟨⟨n, a.all⟩, hmem⟩
         (eSel d (ctx_le_hX d (all_mem_out d hmem)))) },
     { guard := succF (vS d) (eSel d (ctx_le_hX d (all_mem_out d hmem)) (Fin.last n))
       body := [acAt d ⟨⟨n, a.all⟩, hmem⟩ (Fin.snoc (eSel d (ctx_le_hX d hmem)) (vS d)),
         tfAt d ⟨⟨n + 1, a⟩, all_mem_out d hmem⟩ true
           (eSel d (ctx_le_hX d (all_mem_out d hmem)))]
       head := some (acAt d ⟨⟨n, a.all⟩, hmem⟩
         (eSel d (ctx_le_hX d (all_mem_out d hmem)))) },
     { guard := maxF (eSel d (ctx_le_hX d (all_mem_out d hmem)) (Fin.last n))
       body := [acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d (ctx_le_hX d (all_mem_out d hmem)))]
       head := some (tfAt d ⟨⟨n, a.all⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) },
     { guard := ⊤
       body := [tfAt d ⟨⟨n + 1, a⟩, all_mem_out d hmem⟩ false
         (eSel d (ctx_le_hX d (all_mem_out d hmem)))]
       head := some (tfAt d ⟨⟨n, a.all⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) }]

/-- All subformula-evaluation rules. -/
noncomputable def evalRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (subs d.out).attach.flatMap fun x => evalClauses d ⟨x.1, x.2⟩

/-- The unique goal clause: the output sentence must not be false at the fixed
point. -/
noncomputable def goalClause : HornClause (L.sum Language.order) (trBlock d) (kk d) :=
  { guard := ⊤
    body := [tfAt d ⟨⟨0, d.out⟩, self_mem_subs d.out⟩ false Fin.elim0]
    head := none }

/-- The rules of the translated program: everything but the goal clause. -/
noncomputable def trRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  liftedRules d ++ nBase d ++ nStep d ++ nfRules d ++ evalRules d

/-- The translated program. -/
noncomputable def trProg : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  trRules d ++ [goalClause d]

/-! ### The canonical assignment

Over a fixed ordered structure, each relation variable of the block has an
intended value; the correctness proof shows that the least model of the
translated program is exactly this assignment. -/

/-- Composition distributes over `Fin.addCases`. -/
private theorem comp_addCases {m n : ℕ} {α β : Type*} (g : α → β) (f₁ : Fin m → α)
    (f₂ : Fin n → α) : (fun q => g (Fin.addCases f₁ f₂ q)) =
      Fin.addCases (fun q => g (f₁ q)) (fun q => g (f₂ q)) := by
  funext q
  induction q using Fin.addCases with
  | left q => rw [Fin.addCases_left, Fin.addCases_left]
  | right q => rw [Fin.addCases_right, Fin.addCases_right]

section Canonical

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- The rank of a stage: its position in the lexicographic order of the pairs
of a copy index and a stage tuple. -/
noncomputable def srank (j : Fin (hs d)) (t : Fin (hm d) → A) : ℕ :=
  orank (A := Fin (hs d) ×ₗ Lex (Fin (hm d) → A)) (toLex (j, toLex t))

/-- The complement of a stage: at stage `(j, t)`, the atom `i x` is not yet
derived. (A named definition, so that reduction stops here rather than
exposing the recursion of `DescriptiveComplexity.derivesIn`.) -/
noncomputable def canonN (j : Fin (hs d)) (i : d.B.ι)
    (w : Fin (hm d + d.B.arity i) → A) : Prop :=
  ¬derivesIn d.rules (srank d A j fun q => w (Fin.castAdd (d.B.arity i) q))
    ⟨i, fun q => w (Fin.natAdd (hm d) q)⟩

/-- The clause `c` with head atom `a` does not derive the atom `a.idx x` at
stage rank `r`, at any valuation lexicographically up to `w`. -/
def NFsem (r : ℕ) (c : HornClause (L.sum Language.order) d.B d.k) (a : SOAtom d.B d.k)
    (x : Fin (d.B.arity a.idx) → A) (w : Fin d.k → A) : Prop :=
  ∀ v : Fin d.k → A, toLex v ≤ toLex w →
    ¬(c.guard.Realize v ∧
      (∀ b ∈ c.body, derivesIn d.rules r ⟨b.idx, fun q => v (b.args q)⟩) ∧
      (fun q => v (a.args q)) = x)

/-- The structure interpreting the expanded vocabulary at the least fixed
point of the rules – the structure the output sentence is read in. -/
@[instance_reducible]
noncomputable def lfpStr : ((L.sum Language.order).sum d.B.lang).Structure A :=
  @sumStructure (L.sum Language.order) d.B.lang A _ (d.B.structure (lfpAssign d.rules))

/-- Truth of a subformula of the output at the least fixed point. -/
noncomputable def evalT {n : ℕ}
    (ψ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n) (v : Fin n → A) :
    Prop :=
  @BoundedFormula.Realize ((L.sum Language.order).sum d.B.lang) A (lfpStr d A)
    Empty n ψ default v

/-- The intended accumulator of a universally quantified subformula: the
quantified subformula holds up to the last argument. Other subformulas have no
accumulator; theirs is empty. -/
noncomputable def canonAc : (x : SubIx d) → (Fin (x.1.1 + 1) → A) → Prop :=
  fun x =>
    match x with
    | ⟨⟨n, .all χ⟩, _⟩ => fun w =>
        ∀ y : A, y ≤ w (Fin.last n) → evalT d A χ (Fin.snoc (fun q => w q.castSucc) y)
    | _ => fun _ => False

/-- The canonical assignment: the fixed point on the original variables, the
complements of its stages on `N`, the non-firing predicates on `NF`, truth and
falsity of the output's subformulas, and the accumulators. -/
noncomputable def canonAssign : (trBlock d).Assignment A := fun ix =>
  match ix with
  | Sum.inl i => fun x => Derives d.rules ⟨i, x⟩
  | Sum.inr (Sum.inl (j, i)) => canonN d A j i
  | Sum.inr (Sum.inr (Sum.inl (j, ca))) => fun w =>
      NFsem d A
        (srank d A j fun q => w (Fin.castAdd d.k (Fin.castAdd (d.B.arity ca.1.2.idx) q)))
        ca.1.1 ca.1.2
        (fun q => w (Fin.castAdd d.k (Fin.natAdd (hm d) q)))
        (fun q => w (Fin.natAdd (hm d + d.B.arity ca.1.2.idx) q))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, true)))) => fun v => evalT d A x.1.2 v
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (x, false)))) => fun v => ¬evalT d A x.1.2 v
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) => canonAc d A x

/-! #### Atom characterizations under the canonical assignment -/

variable {d} {A}

private theorem rAt_holds {i : d.B.ι} {sel : Fin (d.B.arity i) → Fin (kk d)}
    {V : Fin (kk d) → A} :
    (rAt d i sel).Holds (canonAssign d A) V ↔ Derives d.rules ⟨i, fun q => V (sel q)⟩ :=
  Iff.rfl

private theorem canonN_addCases {j : Fin (hs d)} {i : d.B.ι} {t : Fin (hm d) → A}
    {x : Fin (d.B.arity i) → A} :
    canonN d A j i (Fin.addCases t x) ↔ ¬derivesIn d.rules (srank d A j t) ⟨i, x⟩ := by
  have ha : (fun q => Fin.addCases (m := hm d) t x (Fin.castAdd (d.B.arity i) q)) = t :=
    funext fun q => Fin.addCases_left q
  have hb : (fun q => Fin.addCases (m := hm d) t x (Fin.natAdd (hm d) q)) = x :=
    funext fun q => Fin.addCases_right q
  rw [canonN, ha, hb]

private theorem nAt_holds {j : Fin (hs d)} {i : d.B.ι} {ts : Fin (hm d) → Fin (kk d)}
    {xs : Fin (d.B.arity i) → Fin (kk d)} {V : Fin (kk d) → A} :
    (nAt d j i ts xs).Holds (canonAssign d A) V ↔
      ¬derivesIn d.rules (srank d A j fun q => V (ts q)) ⟨i, fun q => V (xs q)⟩ := by
  have h0 : (nAt d j i ts xs).Holds (canonAssign d A) V ↔
      canonN d A j i fun q => V (Fin.addCases ts xs q) := Iff.rfl
  rw [h0, comp_addCases V ts xs, canonN_addCases]

private theorem nfAt_holds {j : Fin (hs d)} {ca : HIx d} {ts : Fin (hm d) → Fin (kk d)}
    {xs : Fin (d.B.arity ca.1.2.idx) → Fin (kk d)} {ws : Fin d.k → Fin (kk d)}
    {V : Fin (kk d) → A} :
    (nfAt d j ca ts xs ws).Holds (canonAssign d A) V ↔
      NFsem d A (srank d A j fun q => V (ts q)) ca.1.1 ca.1.2 (fun q => V (xs q))
        (fun q => V (ws q)) := by
  have h1 : (fun q => V (Fin.addCases (Fin.addCases ts xs) ws
      (Fin.castAdd d.k (Fin.castAdd (d.B.arity ca.1.2.idx) q)))) =
      fun q => V (ts q) := funext fun q => by rw [Fin.addCases_left, Fin.addCases_left]
  have h2 : (fun q => V (Fin.addCases (Fin.addCases ts xs) ws
      (Fin.castAdd d.k (Fin.natAdd (hm d) q)))) =
      fun q => V (xs q) := funext fun q => by rw [Fin.addCases_left, Fin.addCases_right]
  have h3 : (fun q => V (Fin.addCases (Fin.addCases ts xs) ws
      (Fin.natAdd (hm d + d.B.arity ca.1.2.idx) q))) =
      fun q => V (ws q) := funext fun q => by rw [Fin.addCases_right]
  change NFsem d A
      (srank d A j fun q => V (Fin.addCases (Fin.addCases ts xs) ws
        (Fin.castAdd d.k (Fin.castAdd (d.B.arity ca.1.2.idx) q))))
      ca.1.1 ca.1.2
      (fun q => V (Fin.addCases (Fin.addCases ts xs) ws
        (Fin.castAdd d.k (Fin.natAdd (hm d) q))))
      (fun q => V (Fin.addCases (Fin.addCases ts xs) ws
        (Fin.natAdd (hm d + d.B.arity ca.1.2.idx) q))) ↔ _
  rw [h1, h2, h3]

private theorem tAt_holds {x : SubIx d} {es : Fin x.1.1 → Fin (kk d)} {V : Fin (kk d) → A} :
    (tfAt d x true es).Holds (canonAssign d A) V ↔ evalT d A x.1.2 (fun q => V (es q)) :=
  Iff.rfl

private theorem fAt_holds {x : SubIx d} {es : Fin x.1.1 → Fin (kk d)} {V : Fin (kk d) → A} :
    (tfAt d x false es).Holds (canonAssign d A) V ↔
      ¬evalT d A x.1.2 (fun q => V (es q)) :=
  Iff.rfl

private theorem acAt_holds {x : SubIx d} {es : Fin (x.1.1 + 1) → Fin (kk d)} {V : Fin (kk d) → A} :
    (acAt d x es).Holds (canonAssign d A) V ↔ canonAc d A x (fun q => V (es q)) :=
  Iff.rfl

/-- The accumulator of `∀`, at an explicit `snoc` tuple. -/
private theorem canonAc_all_snoc {n : ℕ}
    {χ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1)}
    {hmem : (⟨n, χ.all⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out} {v : Fin n → A} {y : A} :
    canonAc d A ⟨⟨n, χ.all⟩, hmem⟩ (Fin.snoc v y) ↔
      ∀ z : A, z ≤ y → evalT d A χ (Fin.snoc v z) := by
  have hred : canonAc d A ⟨⟨n, χ.all⟩, hmem⟩ (Fin.snoc v y) ↔
      ∀ z : A, z ≤ Fin.snoc (α := fun _ => A) v y (Fin.last n) →
        evalT d A χ (Fin.snoc (fun q => Fin.snoc (α := fun _ => A) v y q.castSucc) z) :=
    Iff.rfl
  rw [hred, Fin.snoc_last]
  have h2 : (fun q : Fin n => Fin.snoc (α := fun _ => A) v y q.castSucc) = v :=
    funext fun q => by rw [Fin.snoc_castSucc]
  rw [h2]

end Canonical

/-! ### Counting: the last stage is beyond every derivation -/

private theorem card_le_srank_top {A : Type} [LinearOrder A] [Finite A]
    [Nonempty A] {t : Fin (hm d) → A} (ht : ∀ (p : Fin (hm d)) (a : A), a ≤ t p) :
    Nat.card (BAtom d.B A) ≤ srank d A (jTop d) t := by
  have htop : ∀ u : Fin (hs d) ×ₗ Lex (Fin (hm d) → A),
      u ≤ toLex (jTop d, toLex t) := by
    refine prodLex_isTop_iff.mpr ⟨fun x => ?_, fun y => tup_isTop_iff.mpr ht y⟩
    change (x : ℕ) ≤ hc d
    exact Nat.le_of_lt_succ x.isLt
  rw [srank, orank_isTop htop]
  have hfin : ∀ n : ℕ, Nat.card (Fin n) = n := fun n => by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have h1 : Nat.card (Fin (hs d) ×ₗ Lex (Fin (hm d) → A)) =
      hs d * Nat.card A ^ hm d := by
    rw [← Nat.card_congr (toLex (α := Fin (hs d) × Lex (Fin (hm d) → A))), Nat.card_prod,
      ← Nat.card_congr (toLex (α := Fin (hm d) → A)), Nat.card_fun, hfin, hfin]
  have h2 : Nat.card (BAtom d.B A) ≤ hc d * Nat.card A ^ hm d := by
    simpa only [hc, hm] using d.B.card_atoms_le A
  have h3 : 0 < Nat.card A ^ hm d := Nat.pow_pos Nat.card_pos
  have h4 : hs d * Nat.card A ^ hm d = hc d * Nat.card A ^ hm d + Nat.card A ^ hm d := by
    rw [hs, add_one_mul]
  rw [h1, h4]
  exact Nat.le_pred_of_lt (h2.trans_lt (Nat.lt_add_of_pos_right h3))

/-! ### Soundness: the canonical assignment satisfies the rules

Each rule family preserves the canonical assignment; the goal clause is dealt
with at assembly time, where it encodes the output sentence itself. -/

section Soundness

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {V : Fin (kk d) → A}

omit [Finite A] [Nonempty A] in
theorem lifted_sound {ca : HornClause (L.sum Language.order) d.B d.k × SOAtom d.B d.k}
    (hca : ca ∈ headed d) : (liftClause d ca.1).Holds (canonAssign d A) V := by
  obtain ⟨hc₀, hhead⟩ := (mem_headed (d := d)).mp hca
  rintro ⟨hg, hb⟩
  have hg' : ca.1.guard.Realize fun q => V (vW1 d q) := by
    have h2 : (ca.1.guard.relabel (vW1 d)).Realize V := hg
    rwa [Formula.realize_relabel] at h2
  have hbody : ∀ b ∈ ca.1.body, SOAtom.Holds b (lfpAssign d.rules)
      fun q => V (vW1 d q) := by
    intro b hbmem
    exact hb _ (List.mem_map_of_mem (f := liftAtom d) hbmem)
  have hh := lfpAssign_rule hc₀ hhead (fun q => V (vW1 d q)) ⟨hg', hbody⟩
  rw [HornClause.HeadHolds, hhead, Option.elim_some] at hh
  have hlift : (liftClause d ca.1).head = some (liftAtom d ca.2) := by
    change ca.1.head.map (liftAtom d) = _
    rw [hhead, Option.map_some]
  rw [HornClause.HeadHolds, hlift, Option.elim_some]
  exact hh

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem srank_bot {t : Fin (hm d) → A} (ht : ∀ (p : Fin (hm d)) (a : A), t p ≤ a) :
    srank d A (j0 d) t = 0 := by
  refine orank_eq_zero (prodLex_isBot_iff.mpr ⟨fun x => ?_, tup_isBot_iff.mpr ht⟩)
  rw [Fin.le_def]
  simp [j0]

omit [Finite A] [Nonempty A] in
theorem nBase_sound {i : d.B.ι} :
    (HornClause.mk (minTupF (L := L) (vT1 d)) []
      (some (nAt d (j0 d) i (vT1 d) (xa d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, -⟩
  refine nAt_holds.mpr ?_
  rw [srank_bot ((realize_minTupF (L := L) _).mp hg)]
  intro hder
  exact hder

omit [Finite A] in
theorem stageG_covBy {j j' : Fin (hs d)} (hjj : (j, j') ∈ stagePairs d)
    (h : (stageG d j j').Realize V) :
    toLex ((j, toLex fun q => V (vT1 d q)) : Fin (hs d) × Lex (Fin (hm d) → A)) ⋖
      toLex (j', toLex fun q => V (vT2 d q)) := by
  rcases (mem_stagePairs (d := d)).mp hjj with rfl | hcross
  · rw [stageG, ite_eq_left rfl] at h
    exact prodLex_covBy_iff.mpr (Or.inl ⟨rfl,
      tupSucc_iff_covBy.mp ((realize_succTupF (L := L) _ _).mp h)⟩)
  · have hne : j ≠ j' := by
      intro he
      rw [he] at hcross
      omega
    rw [stageG, ite_eq_right hne, Formula.realize_inf] at h
    refine prodLex_covBy_iff.mpr (Or.inr ⟨finCovBy_iff.mpr hcross, ?_, ?_⟩)
    · exact tup_isTop_iff.mpr ((realize_maxTupF (L := L) _).mp h.1)
    · exact tup_isBot_iff.mpr ((realize_minTupF (L := L) _).mp h.2)

open Classical in
private theorem nStep_sound {j j' : Fin (hs d)} (hjj : (j, j') ∈ stagePairs d) {i : d.B.ι} :
    (HornClause.mk (stageG d j j' ⊓ maxTupF (vW1 d))
      (nAt d j i (vT1 d) (xa d i) ::
        (((headed d).attach.filter fun ca => ca.1.2.idx = i).map fun ca =>
          nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)))
      (some (nAt d j' i (vT2 d) (xa d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, hb⟩
  rw [Formula.realize_inf] at hg
  obtain ⟨hg1, hg2⟩ := hg
  have hstep : srank d A j' (fun q => V (vT2 d q)) =
      srank d A j (fun q => V (vT1 d q)) + 1 := orank_covBy (stageG_covBy hjj hg1)
  refine nAt_holds.mpr ?_
  rw [hstep]
  intro hder
  have hN := nAt_holds.mp (hb _ (List.mem_cons_self ..))
  rcases hder with hprev | hstep2
  · exact hN hprev
  · obtain ⟨c, hcmem, a, hha, v, heq, hgc, hbc⟩ := hstep2
    obtain ⟨h1, h2⟩ := Sigma.mk.injEq .. ▸ heq
    subst h1
    have hca : (c, a) ∈ headed d := (mem_headed (d := d)).mpr ⟨hcmem, hha⟩
    have hmemf : (⟨(c, a), hca⟩ : HIx d) ∈
        (headed d).attach.filter fun ca => ca.1.2.idx = a.idx := by
      rw [List.mem_filter]
      exact ⟨List.mem_attach _ _, by simp⟩
    have hNF := nfAt_holds.mp (hb _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hmemf)))
    have hvle : toLex v ≤ toLex fun q => V (vW1 d q) :=
      tup_isTop_iff.mpr ((realize_maxTupF (L := L) _).mp hg2) (toLex v)
    exact hNF v hvle ⟨hgc, hbc, (eq_of_heq h2).symm⟩

omit [Finite A] [Nonempty A] in
/-- Extending a non-firing certificate at the bottom valuation. -/
private theorem NFsem_base {r : ℕ} {c₀ : HornClause (L.sum Language.order) d.B d.k}
    {a₀ : SOAtom d.B d.k} {x : Fin (d.B.arity a₀.idx) → A} {w : Fin d.k → A}
    (hbot : ∀ (p : Fin d.k) (a : A), w p ≤ a)
    (hfail : ¬(c₀.guard.Realize w ∧
      (∀ b ∈ c₀.body, derivesIn d.rules r ⟨b.idx, fun q => w (b.args q)⟩) ∧
      (fun q => w (a₀.args q)) = x)) :
    NFsem d A r c₀ a₀ x w := by
  intro v hv
  have hveq : v = w := toLex_inj.mp (le_antisymm hv (tup_isBot_iff.mpr hbot (toLex v)))
  rw [hveq]
  exact hfail

omit [Finite A] [Nonempty A] in
/-- Extending a non-firing certificate along the successor valuation. -/
private theorem NFsem_step {r : ℕ} {c₀ : HornClause (L.sum Language.order) d.B d.k}
    {a₀ : SOAtom d.B d.k} {x : Fin (d.B.arity a₀.idx) → A} {w w' : Fin d.k → A}
    (hsucc : TupSucc w w') (hprev : NFsem d A r c₀ a₀ x w)
    (hfail : ¬(c₀.guard.Realize w' ∧
      (∀ b ∈ c₀.body, derivesIn d.rules r ⟨b.idx, fun q => w' (b.args q)⟩) ∧
      (fun q => w' (a₀.args q)) = x)) :
    NFsem d A r c₀ a₀ x w' := by
  intro v hv
  rcases covBy_le_cases (tupSucc_iff_covBy.mp hsucc) hv with h | h
  · exact hprev v h
  · rw [toLex_inj.mp h]
    exact hfail

omit [Finite A] [Nonempty A] in
theorem nfClauses_sound {j : Fin (hs d)} {ca : HIx d}
    {c : HornClause (L.sum Language.order) (trBlock d) (kk d)}
    (hc : c ∈ nfClauses d j ca) : c.Holds (canonAssign d A) V := by
  rw [nfClauses] at hc
  rcases List.mem_append.mp hc with hc' | hc'
  · rcases List.mem_append.mp hc' with hc'' | hc''
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc''
      rcases hc'' with rfl | rfl | rfl | rfl
      · -- base, guard fails
        rintro ⟨hg, -⟩
        rw [Formula.realize_inf, Formula.realize_not, Formula.realize_relabel] at hg
        refine nfAt_holds.mpr (NFsem_base ((realize_minTupF (L := L) _).mp hg.1) ?_)
        exact fun h => hg.2 h.1
      · -- base, head tuple differs
        rintro ⟨hg, -⟩
        rw [Formula.realize_inf, Formula.realize_not, realize_eqTupF] at hg
        refine nfAt_holds.mpr (NFsem_base ((realize_minTupF (L := L) _).mp hg.1) ?_)
        exact fun h => hg.2 h.2.2.symm
      · -- step, guard fails
        rintro ⟨hg, hb⟩
        rw [Formula.realize_inf, Formula.realize_not, Formula.realize_relabel] at hg
        have hprev := nfAt_holds.mp (hb _ (List.mem_cons_self ..))
        refine nfAt_holds.mpr
          (NFsem_step ((realize_succTupF (L := L) _ _).mp hg.1) hprev ?_)
        exact fun h => hg.2 h.1
      · -- step, head tuple differs
        rintro ⟨hg, hb⟩
        rw [Formula.realize_inf, Formula.realize_not, realize_eqTupF] at hg
        have hprev := nfAt_holds.mp (hb _ (List.mem_cons_self ..))
        refine nfAt_holds.mpr
          (NFsem_step ((realize_succTupF (L := L) _ _).mp hg.1) hprev ?_)
        exact fun h => hg.2 h.2.2.symm
    · -- base, a body atom is not derived
      obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hc''
      rintro ⟨hg, hb⟩
      have hbN := nAt_holds.mp (hb _ (List.mem_cons_self ..))
      refine nfAt_holds.mpr (NFsem_base ((realize_minTupF (L := L) _).mp hg) ?_)
      exact fun h => hbN (h.2.1 b hbmem)
  · -- step, a body atom is not derived
    obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hc'
    rintro ⟨hg, hb⟩
    have hprev := nfAt_holds.mp (hb _ (List.mem_cons_self ..))
    have hbN := nAt_holds.mp (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    refine nfAt_holds.mpr (NFsem_step ((realize_succTupF (L := L) _ _).mp hg) hprev ?_)
    exact fun h => hbN (h.2.1 b hbmem)

/-! #### Evaluating the output sentence -/

/-- The value of a term of the expanded vocabulary at the least fixed point. -/
noncomputable def evTermVal {n : ℕ} (v : Fin n → A)
    (t : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) : A :=
  @Term.realize ((L.sum Language.order).sum d.B.lang) A (lfpStr d A) _
    (Sum.elim default v) t

omit [Finite A] [Nonempty A]

private theorem evalT_imp {n : ℕ}
    {a b : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n} {v : Fin n → A} :
    evalT d A (a.imp b) v ↔ (evalT d A a v → evalT d A b v) :=
  Iff.rfl

private theorem evalT_all {n : ℕ}
    {a : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1)}
    {v : Fin n → A} :
    evalT d A a.all v ↔ ∀ y : A, evalT d A a (Fin.snoc v y) :=
  Iff.rfl

private theorem evalT_equal {n : ℕ}
    {t u : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)} {v : Fin n → A} :
    evalT d A (.equal t u) v ↔ evTermVal v t = evTermVal v u :=
  Iff.rfl

private theorem evalT_rel_inl {n l : ℕ} {r : (L.sum Language.order).Relations l}
    {ts : Fin l → ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)}
    {v : Fin n → A} :
    evalT d A (.rel (Sum.inl r) ts) v ↔ RelMap (M := A) r fun q => evTermVal v (ts q) :=
  Iff.rfl

private theorem evalT_rel_inr {n l : ℕ} {r : d.B.lang.Relations l}
    {ts : Fin l → ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)}
    {v : Fin n → A} :
    evalT d A (.rel (Sum.inr r) ts) v ↔
      Derives d.rules ⟨r.1, fun q => evTermVal v (ts (Fin.cast r.2 q))⟩ :=
  Iff.rfl

private theorem realize_evTerm {n : ℕ} (hn : n ≤ hX d) {V : Fin (kk d) → A}
    (t : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    (evTerm d hn t).realize V = evTermVal (fun q => V (eSel d hn q)) t := by
  rw [evTerm, Term.realize_relabel]
  have hval : (V ∘ Sum.elim (fun e : Empty => e.elim) (eSel d hn)) =
      Sum.elim (default : Empty → A) fun q => V (eSel d hn q) := by
    funext z
    cases z with
    | inl e => exact e.elim
    | inr q => rfl
  rw [hval]
  exact @realize_stripTerm (L.sum Language.order) d.B.lang _ _ A _
    (d.B.structure (lfpAssign d.rules)) _ t

omit [L.Structure A] [LinearOrder A] in
/-- The evaluation tuple of a wider context, as a `snoc`. -/
private theorem eSel_snoc {n : ℕ} (hn1 : n + 1 ≤ hX d) {V : Fin (kk d) → A} :
    (fun q => V (eSel d hn1 q)) =
      Fin.snoc (fun q => V (eSel d (le_trans (Nat.le_succ n) hn1) q))
        (V (eSel d hn1 (Fin.last n))) := by
  funext q
  induction q using Fin.lastCases with
  | last => rw [Fin.snoc_last]
  | cast q =>
    rw [Fin.snoc_castSucc]
    rfl

/-- Composition distributes over `Fin.snoc`. -/
private theorem comp_snoc_lambda {n : ℕ} {α β : Type*} (g : α → β) (f : Fin n → α) (c : α) :
    (fun q => g (Fin.snoc (α := fun _ => α) f c q)) =
      Fin.snoc (fun q => g (f q)) (g c) := by
  funext q
  induction q using Fin.lastCases with
  | last => rw [Fin.snoc_last, Fin.snoc_last]
  | cast q => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

variable [Finite A] [Nonempty A]

private theorem evalClauses_sound {x : SubIx d}
    {c : HornClause (L.sum Language.order) (trBlock d) (kk d)}
    (hc : c ∈ evalClauses d x) : c.Holds (canonAssign d A) V := by
  obtain ⟨⟨n, ψ⟩, hmem⟩ := x
  cases ψ with
  | falsum =>
    simp only [evalClauses, List.mem_singleton] at hc
    subst hc
    rintro ⟨-, -⟩
    exact fAt_holds.mpr fun h => h
  | equal t u =>
    simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rintro ⟨hg, -⟩
      rw [Formula.realize_equal, realize_evTerm, realize_evTerm] at hg
      exact tAt_holds.mpr (evalT_equal.mpr hg)
    · rintro ⟨hg, -⟩
      rw [Formula.realize_not, Formula.realize_equal, realize_evTerm,
        realize_evTerm] at hg
      exact fAt_holds.mpr fun h => hg (evalT_equal.mp h)
  | rel R ts =>
    rcases R with r | r
    · simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rintro ⟨hg, -⟩
        rw [Formula.realize_rel] at hg
        have hts : (fun q => (evTerm d (ctx_le_hX d hmem) (ts q)).realize V) =
            fun q => evTermVal (fun p => V (eSel d (ctx_le_hX d hmem) p)) (ts q) :=
          funext fun q => realize_evTerm _ _
        rw [hts] at hg
        exact tAt_holds.mpr (evalT_rel_inl.mpr hg)
      · rintro ⟨hg, -⟩
        rw [Formula.realize_not, Formula.realize_rel] at hg
        have hts : (fun q => (evTerm d (ctx_le_hX d hmem) (ts q)).realize V) =
            fun q => evTermVal (fun p => V (eSel d (ctx_le_hX d hmem) p)) (ts q) :=
          funext fun q => realize_evTerm _ _
        rw [hts] at hg
        exact fAt_holds.mpr fun h => hg (evalT_rel_inl.mp h)
    · simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rintro ⟨hg, hb⟩
        have hR := rAt_holds.mp (hb _ (List.mem_cons_self ..))
        refine tAt_holds.mpr (evalT_rel_inr.mpr ?_)
        have htup : (fun q => V (xa d r.1 q)) =
            fun q => evTermVal (fun p => V (eSel d (ctx_le_hX d hmem) p))
              (ts (Fin.cast r.2 q)) := by
          funext q
          have h := (realize_listInf _).mp hg _
            (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
          rw [Formula.realize_equal, Term.realize_var, realize_evTerm] at h
          exact h
        rw [← htup]
        exact hR
      · rintro ⟨hg, hb⟩
        rw [Formula.realize_inf] at hg
        have hN := nAt_holds.mp (hb _ (List.mem_cons_self ..))
        have hcard := card_le_srank_top d (A := A)
          ((realize_maxTupF (L := L) _).mp hg.2)
        have hnotder : ¬Derives d.rules ⟨r.1, fun q => V (xa d r.1 q)⟩ := fun h =>
          hN ((derivesIn_iff_derives_of_card_le hcard).mpr h)
        have htup : (fun q => V (xa d r.1 q)) =
            fun q => evTermVal (fun p => V (eSel d (ctx_le_hX d hmem) p))
              (ts (Fin.cast r.2 q)) := by
          funext q
          have h := (realize_listInf _).mp hg.1 _
            (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
          rw [Formula.realize_equal, Term.realize_var, realize_evTerm] at h
          exact h
        refine fAt_holds.mpr fun h => ?_
        have h2 := evalT_rel_inr.mp h
        rw [← htup] at h2
        exact hnotder h2
  | imp a b =>
    simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rintro ⟨-, hb⟩
      have hFa := fAt_holds.mp (hb _ (List.mem_cons_self ..))
      exact tAt_holds.mpr (evalT_imp.mpr fun ha => absurd ha hFa)
    · rintro ⟨-, hb⟩
      have hTb := tAt_holds.mp (hb _ (List.mem_cons_self ..))
      exact tAt_holds.mpr (evalT_imp.mpr fun _ => hTb)
    · rintro ⟨-, hb⟩
      have hTa := tAt_holds.mp (hb _ (List.mem_cons_self ..))
      have hFb := fAt_holds.mp (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      exact fAt_holds.mpr fun h => hFb (evalT_imp.mp h hTa)
  | all a =>
    simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
    have hn1 : n + 1 ≤ hX d := ctx_le_hX d (all_mem_out d hmem)
    rcases hc with rfl | rfl | rfl | rfl
    · -- accumulator base
      rintro ⟨hg, hb⟩
      have hTa := tAt_holds.mp (hb _ (List.mem_cons_self ..))
      change (acAt d ⟨⟨n, a.all⟩, hmem⟩
        (eSel d (ctx_le_hX d (all_mem_out d hmem)))).Holds (canonAssign d A) V
      refine acAt_holds.mpr ?_
      rw [eSel_snoc hn1]
      refine canonAc_all_snoc.mpr fun z hz => ?_
      have hzeq : z = V (eSel d hn1 (Fin.last n)) :=
        le_antisymm hz ((realize_minF (L := L) _).mp hg z)
      rw [hzeq, ← eSel_snoc hn1]
      exact hTa
    · -- accumulator step
      rintro ⟨hg, hb⟩
      rw [realize_succF] at hg
      have hAcc := acAt_holds.mp (hb _ (List.mem_cons_self ..))
      have hTa := tAt_holds.mp (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      rw [comp_snoc_lambda] at hAcc
      have hprev := canonAc_all_snoc.mp hAcc
      change (acAt d ⟨⟨n, a.all⟩, hmem⟩
        (eSel d (ctx_le_hX d (all_mem_out d hmem)))).Holds (canonAssign d A) V
      refine acAt_holds.mpr ?_
      rw [eSel_snoc hn1]
      refine canonAc_all_snoc.mpr fun z hz => ?_
      rcases le_or_gt z (V (vS d)) with hle | hgt
      · exact hprev z hle
      · have hzeq : z = V (eSel d hn1 (Fin.last n)) := by
          rcases lt_or_eq_of_le hz with hlt | he
          · exact absurd ⟨hgt, hlt⟩ (hg.2 z)
          · exact he
        rw [hzeq, ← eSel_snoc hn1]
        exact hTa
    · -- from a full accumulator to the truth of `∀`
      rintro ⟨hg, hb⟩
      have hAcc := acAt_holds.mp (hb _ (List.mem_cons_self ..))
      rw [eSel_snoc hn1] at hAcc
      have hAcc' := canonAc_all_snoc.mp hAcc
      exact tAt_holds.mpr (evalT_all.mpr fun y => hAcc' y ((realize_maxF (L := L) _).mp hg y))
    · -- falsity, from a witness
      rintro ⟨-, hb⟩
      have hFa := fAt_holds.mp (hb _ (List.mem_cons_self ..))
      refine fAt_holds.mpr fun h => ?_
      have h2 := evalT_all.mp h (V (eSel d hn1 (Fin.last n)))
      rw [← eSel_snoc hn1] at h2
      exact hFa h2

/-! #### All rules are sound -/

theorem trRules_sound (V : Fin (kk d) → A)
    {c : HornClause (L.sum Language.order) (trBlock d) (kk d)} (hc : c ∈ trRules d) :
    c.Holds (canonAssign d A) V := by
  rw [trRules] at hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨ca, hca, rfl⟩ := List.mem_map.mp hc
          exact lifted_sound hca
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
          exact nBase_sound
      · obtain ⟨⟨j, j'⟩, hjj, hmm⟩ := List.mem_flatMap.mp hc
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hmm
        exact nStep_sound hjj
    · obtain ⟨j, -, hmm⟩ := List.mem_flatMap.mp hc
      obtain ⟨ca, -, hcin⟩ := List.mem_flatMap.mp hmm
      exact nfClauses_sound hcin
  · obtain ⟨x, hx, hcin⟩ := List.mem_flatMap.mp hc
    exact evalClauses_sound hcin

end Soundness

/-! ### Completeness: every canonical fact is derivable

The other inclusion: each component of the canonical assignment is contained
in the least model of the translated program. The fixed point part is
leastness itself; the stage complements walk the stage order, the non-firing
predicates walk the valuation order, and the subformula relations follow the
structure of the output. -/

section Completeness

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Assembling a valuation of the shared variables from its blocks. -/
private noncomputable def packV (t1 t2 x : Fin (hm d) → A) (w1 w2 : Fin d.k → A)
    (e : Fin (hX d) → A) (sp : A) : Fin (kk d) → A := fun q =>
  if h1 : (q : ℕ) < hm d then t1 ⟨q, h1⟩
  else if h2 : (q : ℕ) < 2 * hm d then t2 ⟨(q : ℕ) - hm d, by omega⟩
  else if h3 : (q : ℕ) < 3 * hm d then x ⟨(q : ℕ) - 2 * hm d, by omega⟩
  else if h4 : (q : ℕ) < 3 * hm d + d.k then w1 ⟨(q : ℕ) - 3 * hm d, by omega⟩
  else if h5 : (q : ℕ) < 3 * hm d + 2 * d.k then
    w2 ⟨(q : ℕ) - (3 * hm d + d.k), by omega⟩
  else if h6 : (q : ℕ) < 3 * hm d + 2 * d.k + hX d then
    e ⟨(q : ℕ) - (3 * hm d + 2 * d.k), by omega⟩
  else sp

/-- Extending a tuple to a wider block, junk-padded. -/
private noncomputable def padF {m M : ℕ} (f : Fin m → A) : Fin M → A :=
  fun p => if h : (p : ℕ) < m then f ⟨p, h⟩ else Classical.arbitrary A

variable {t1 t2 x : Fin (hm d) → A} {w1 w2 : Fin d.k → A} {e : Fin (hX d) → A} {sp : A}

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

private theorem packV_comp_vT1 : (fun q => packV t1 t2 x w1 w2 e sp (vT1 d q)) = t1 := by
  funext q
  have hq := q.isLt
  have hv : ((vT1 d q : Fin (kk d)) : ℕ) = (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_left (by rw [hv]; omega)]
  exact congrArg t1 (Fin.ext (show ((vT1 d q : Fin (kk d)) : ℕ) = (q : ℕ) from hv))

private theorem packV_comp_vT2 : (fun q => packV t1 t2 x w1 w2 e sp (vT2 d q)) = t2 := by
  funext q
  have hq := q.isLt
  have hv : ((vT2 d q : Fin (kk d)) : ℕ) = hm d + (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_left (by rw [hv]; omega)]
  exact congrArg t2 (Fin.ext
    (show ((vT2 d q : Fin (kk d)) : ℕ) - hm d = (q : ℕ) from by rw [hv]; omega))

private theorem packV_comp_vW1 : (fun q => packV t1 t2 x w1 w2 e sp (vW1 d q)) = w1 := by
  funext q
  have hq := q.isLt
  have hv : ((vW1 d q : Fin (kk d)) : ℕ) = 3 * hm d + (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_left (by rw [hv]; omega)]
  exact congrArg w1 (Fin.ext
    (show ((vW1 d q : Fin (kk d)) : ℕ) - 3 * hm d = (q : ℕ) from by rw [hv]; omega))

private theorem packV_comp_vW2 : (fun q => packV t1 t2 x w1 w2 e sp (vW2 d q)) = w2 := by
  funext q
  have hq := q.isLt
  have hv : ((vW2 d q : Fin (kk d)) : ℕ) = 3 * hm d + d.k + (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_left (by rw [hv]; omega)]
  exact congrArg w2 (Fin.ext
    (show ((vW2 d q : Fin (kk d)) : ℕ) - (3 * hm d + d.k) = (q : ℕ) from by
      rw [hv]; omega))

private theorem packV_comp_eSel {n : ℕ} [Nonempty A] (hn : n ≤ hX d) {v : Fin n → A} :
    (fun q => packV t1 t2 x w1 w2 (padF v) sp (eSel d hn q)) = v := by
  funext q
  have hq := q.isLt
  have hv : ((eSel d hn q : Fin (kk d)) : ℕ) = 3 * hm d + 2 * d.k + (q : ℕ) := rfl
  simp only [packV, padF]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_left (by rw [hv]; omega)]
  have hq2 : (((eSel d hn q : Fin (kk d)) : ℕ) - (3 * hm d + 2 * d.k) : ℕ) < n := by
    rw [hv]; omega
  rw [dite_eq_left hq2]
  exact congrArg v (Fin.ext
    (show ((eSel d hn q : Fin (kk d)) : ℕ) - (3 * hm d + 2 * d.k) = (q : ℕ) from by
      rw [hv]; omega))

private theorem packV_vS : packV t1 t2 x w1 w2 e sp (vS d) = sp := by
  have hv : ((vS d : Fin (kk d)) : ℕ) = 3 * hm d + 2 * d.k + hX d := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega)]

private theorem packV_comp_xa {i : d.B.ι} [Nonempty A] {xt : Fin (d.B.arity i) → A} :
    (fun q => packV t1 t2 (padF xt) w1 w2 e sp (xa d i q)) = xt := by
  funext q
  have hq := q.isLt
  have hqm : (q : ℕ) < hm d := lt_of_lt_of_le hq (arity_le_blockArityBound d.B i)
  have hv : ((xa d i q : Fin (kk d)) : ℕ) = 2 * hm d + (q : ℕ) := rfl
  simp only [packV, padF]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_left (by rw [hv]; omega)]
  have hq2 : (((xa d i q : Fin (kk d)) : ℕ) - 2 * hm d : ℕ) < d.B.arity i := by
    rw [hv]; omega
  rw [dite_eq_left hq2]
  exact congrArg xt (Fin.ext
    (show ((xa d i q : Fin (kk d)) : ℕ) - 2 * hm d = (q : ℕ) from by rw [hv]; omega))

/-- Rewriting the tuple of a derived atom. -/
private theorem derives_congr_tuple {Lg : Language.{0, 0}} {B : SOBlock} {k : ℕ}
    {rules : List (HornClause Lg B k)} {ix : B.ι} {w w' : Fin (B.arity ix) → A}
    [Lg.Structure A] (h : w = w') (hd : Derives rules ⟨ix, w⟩) :
    Derives rules ⟨ix, w'⟩ :=
  h ▸ hd

/-! #### Membership of the rules in the program -/

private theorem mem_trProg_trRules {c : HornClause (L.sum Language.order) (trBlock d) (kk d)}
    (h : c ∈ trRules d) : c ∈ trProg d := by
  rw [trProg]
  exact List.mem_append_left _ h

private theorem mem_trProg_lifted {c} (h : c ∈ liftedRules d) : c ∈ trProg d :=
  mem_trProg_trRules (by
    rw [trRules]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ h))))

private theorem mem_trProg_nBase {c} (h : c ∈ nBase d) : c ∈ trProg d :=
  mem_trProg_trRules (by
    rw [trRules]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ h))))

private theorem mem_trProg_nStep {c} (h : c ∈ nStep d) : c ∈ trProg d :=
  mem_trProg_trRules (by
    rw [trRules]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h)))

private theorem mem_trProg_nfRules {c} (h : c ∈ nfRules d) : c ∈ trProg d :=
  mem_trProg_trRules (by
    rw [trRules]
    exact List.mem_append_left _ (List.mem_append_right _ h))

private theorem mem_trProg_evalRules {c} (h : c ∈ evalRules d) : c ∈ trProg d :=
  mem_trProg_trRules (by
    rw [trRules]
    exact List.mem_append_right _ h)

private theorem mem_evalRules {x : SubIx d} {c} (h : c ∈ evalClauses d x) : c ∈ evalRules d := by
  rw [evalRules]
  exact List.mem_flatMap.mpr ⟨⟨x.1, x.2⟩, List.mem_attach _ _, h⟩

variable [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! #### The fixed point itself -/

omit [Finite A] in
/-- The fixed point of the rules is derivable on the `R`-part: leastness,
against the lifted rules. -/
private theorem derives_r {i : d.B.ι} {x : Fin (d.B.arity i) → A}
    (h : Derives d.rules ⟨i, x⟩) : Derives (trProg d) ⟨rIx d i, x⟩ := by
  refine lfpAssign_least_of_closed
    (ρ := fun i x => Derives (trProg d) ⟨rIx d i, x⟩) ?_ h
  intro c hc a ha v hg hb
  have hmem : liftClause d c ∈ trProg d :=
    mem_trProg_lifted (List.mem_map_of_mem (f := fun ca => liftClause d ca.1)
      (a := (c, a)) ((mem_headed (d := d)).mpr ⟨hc, ha⟩))
  have hhead : (liftClause d c).head = some (liftAtom d a) := by
    change c.head.map (liftAtom d) = _
    rw [ha, Option.map_some]
  set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
    (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) v
    (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
    (Classical.arbitrary A) with hV
  have hgV : (liftClause d c).guard.Realize V := by
    change (c.guard.relabel (vW1 d)).Realize V
    rw [Formula.realize_relabel]
    change c.guard.Realize fun q => V (vW1 d q)
    rw [hV, packV_comp_vW1]
    exact hg
  have hW1 : (fun q => V (vW1 d q)) = v := by rw [hV, packV_comp_vW1]
  have hbV : ∀ b ∈ (liftClause d c).body,
      Derives (trProg d) ⟨b.idx, fun q => V (b.args q)⟩ := by
    intro b' hb'
    obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hb'
    exact derives_congr_tuple (funext fun j => (congrFun hW1 (b.args j)).symm) (hb b hbmem)
  have key := Derives.rule (rules := trProg d) hmem hhead hgV hbV
  exact derives_congr_tuple (funext fun j => congrFun hW1 (a.args j)) key

/-! #### The stage complements -/

omit [Finite A] [Nonempty A] in
/-- A stage that derives nothing new certifies non-firing at every
valuation. -/
private theorem NFsem_of_not_derivesIn {r : ℕ} {c : HornClause (L.sum Language.order) d.B d.k}
    {a : SOAtom d.B d.k} (hc : c ∈ d.rules) (ha : c.head = some a)
    {xt : Fin (d.B.arity a.idx) → A} (hnd : ¬derivesIn d.rules (r + 1) ⟨a.idx, xt⟩)
    (w : Fin d.k → A) : NFsem d A r c a xt w := by
  rintro v hv ⟨hg, hb, hx⟩
  exact hnd (Or.inr ⟨c, hc, a, ha, v, congrArg (Sigma.mk a.idx) hx.symm, hg, hb⟩)

omit [Finite A] in
/-- The stage-successor guard is realizable along a cover. -/
private theorem stageG_realize {j j' : Fin (hs d)} {V : Fin (kk d) → A}
    (hjj : (j, j') ∈ stagePairs d)
    (hcov : toLex ((j, toLex fun q => V (vT1 d q)) : Fin (hs d) × Lex (Fin (hm d) → A)) ⋖
      toLex (j', toLex fun q => V (vT2 d q))) :
    (stageG d j j').Realize V := by
  rcases (mem_stagePairs (d := d)).mp hjj with rfl | hcross
  · rw [stageG, ite_eq_left rfl]
    rcases prodLex_covBy_iff.mp hcov with ⟨-, htail⟩ | ⟨hjcov, -, -⟩
    · exact (realize_succTupF (L := L) _ _).mpr (tupSucc_iff_covBy.mpr htail)
    · exact absurd hjcov.1 (lt_irrefl _)
  · have hne : j ≠ j' := by
      intro he
      rw [he] at hcross
      omega
    rw [stageG, ite_eq_right hne, Formula.realize_inf]
    rcases prodLex_covBy_iff.mp hcov with ⟨heq, -⟩ | ⟨-, htop, hbot⟩
    · exact absurd heq hne
    · exact ⟨(realize_maxTupF (L := L) _).mpr (tup_isTop_iff.mp htop),
        (realize_minTupF (L := L) _).mpr (tup_isBot_iff.mp hbot)⟩

omit [L.Structure A] [Finite A] in
/-- A cover of stages is a stage pair. -/
private theorem stagePairs_of_covBy {j j' : Fin (hs d)} {u u' : Lex (Fin (hm d) → A)}
    (hcov : toLex ((j, u) : Fin (hs d) × Lex (Fin (hm d) → A)) ⋖ toLex (j', u')) :
    (j, j') ∈ stagePairs d := by
  rcases prodLex_covBy_iff.mp hcov with ⟨rfl, -⟩ | ⟨hjcov, -, -⟩
  · exact (mem_stagePairs (d := d)).mpr (Or.inl rfl)
  · exact (mem_stagePairs (d := d)).mpr (Or.inr (finCovBy_iff.mp hjcov))

omit [Finite A] in
/-- At the bottom stage, everything is underived, by the base rules. -/
private theorem derives_nBase {i : d.B.ι} {t : Fin (hm d) → A}
    (ht : ∀ (p : Fin (hm d)) (a : A), t p ≤ a) (xt : Fin (d.B.arity i) → A) :
    Derives (trProg d) ⟨nIx d (j0 d) i, Fin.addCases t xt⟩ := by
  have hmem : (HornClause.mk (minTupF (L := L) (vT1 d)) []
      (some (nAt d (j0 d) i (vT1 d) (xa d i)))) ∈ trProg d :=
    mem_trProg_nBase (List.mem_map.mpr ⟨i, mem_iotaList d i, rfl⟩)
  set V : Fin (kk d) → A := packV t t (padF xt) (fun _ => Classical.arbitrary A)
    (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
    (Classical.arbitrary A) with hV
  have hgV : (minTupF (L := L) (vT1 d)).Realize V := by
    refine (realize_minTupF (L := L) _).mpr fun p a' => ?_
    rw [hV, congrFun packV_comp_vT1 p]
    exact ht p a'
  have key := Derives.rule (rules := trProg d) hmem (a := nAt d (j0 d) i (vT1 d) (xa d i))
    rfl hgV (fun b hb => absurd hb (by simp))
  refine derives_congr_tuple ?_ key
  change (fun q => V (Fin.addCases (vT1 d) (xa d i) q)) = _
  rw [comp_addCases, hV, packV_comp_vT1, packV_comp_xa]

/-- Membership of a non-firing clause in the program. -/
private theorem mem_trProg_nfClauses {j : Fin (hs d)} {ca : HIx d} {c}
    (h : c ∈ nfClauses d j ca) : c ∈ trProg d :=
  mem_trProg_nfRules (List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
    List.mem_flatMap.mpr ⟨ca, List.mem_attach _ _, h⟩⟩)

omit [Finite A] [Nonempty A] in
/-- Firing one non-firing clause, given its guard and bodies. -/
private theorem fireNF {j : Fin (hs d)} {ca : HIx d} {t : Fin (hm d) → A}
    {xt : Fin (d.B.arity ca.1.2.idx) → A} {w : Fin d.k → A} {V : Fin (kk d) → A}
    {c : HornClause (L.sum Language.order) (trBlock d) (kk d)}
    (hcmem : c ∈ nfClauses d j ca)
    (hhead : c.head = some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d)))
    (hg : c.guard.Realize V)
    (hb : ∀ b ∈ c.body, Derives (trProg d) ⟨b.idx, fun q => V (b.args q)⟩)
    (ht1 : (fun q => V (vT1 d q)) = t)
    (hxa : (fun q => V (xa d ca.1.2.idx q)) = xt)
    (hw2 : (fun q => V (vW2 d q)) = w) :
    Derives (trProg d) ⟨nfIx d j ca, Fin.addCases (Fin.addCases t xt) w⟩ := by
  have key := Derives.rule (rules := trProg d) (mem_trProg_nfClauses hcmem) hhead hg hb
  refine derives_congr_tuple ?_ key
  change (fun q =>
    V (Fin.addCases (Fin.addCases (vT1 d) (xa d ca.1.2.idx)) (vW2 d) q)) = _
  rw [comp_addCases, comp_addCases, ht1, hxa, hw2]

/-- The non-firing certificates are derivable, walking the valuations. -/
private theorem derives_nf {j : Fin (hs d)} {t : Fin (hm d) → A}
    (hN : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      ¬derivesIn d.rules (srank d A j t) ⟨i, xt⟩ →
      Derives (trProg d) ⟨nIx d j i, Fin.addCases t xt⟩)
    (ca : HIx d) (xt : Fin (d.B.arity ca.1.2.idx) → A) (w : Fin d.k → A)
    (hnf : NFsem d A (srank d A j t) ca.1.1 ca.1.2 xt w) :
    Derives (trProg d) ⟨nfIx d j ca, Fin.addCases (Fin.addCases t xt) w⟩ := by
  revert hnf
  refine order_induction (A := Lex (Fin d.k → A))
    (P := fun wl => NFsem d A (srank d A j t) ca.1.1 ca.1.2 xt (ofLex wl) →
      Derives (trProg d) ⟨nfIx d j ca, Fin.addCases (Fin.addCases t xt) (ofLex wl)⟩)
    ?_ ?_ (toLex w)
  · -- base: the bottom valuation
    intro wl hbot hnf
    have hbotc : ∀ (p : Fin d.k) (a : A), ofLex wl p ≤ a := tup_isBot_iff.mp hbot
    have hfail := hnf (ofLex wl) le_rfl
    set V : Fin (kk d) → A := packV t t (padF xt) (fun _ => Classical.arbitrary A)
      (ofLex wl) (fun _ => Classical.arbitrary A) (Classical.arbitrary A) with hV
    have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
    have hXa : (fun q => V (xa d ca.1.2.idx q)) = xt := by rw [hV, packV_comp_xa]
    have hW2 : (fun q => V (vW2 d q)) = ofLex wl := by rw [hV, packV_comp_vW2]
    have hminW : (minTupF (L := L) (vW2 d)).Realize V := by
      refine (realize_minTupF (L := L) _).mpr fun p a' => ?_
      rw [hV, congrFun packV_comp_vW2 p]
      exact hbotc p a'
    by_cases hgc : ca.1.1.guard.Realize (ofLex wl)
    · by_cases hxeq : (fun q => (ofLex wl) (ca.1.2.args q)) = xt
      · have hbods : ¬∀ b ∈ ca.1.1.body,
            derivesIn d.rules (srank d A j t) ⟨b.idx, fun q => (ofLex wl) (b.args q)⟩ :=
          fun hb => hfail ⟨hgc, hb, hxeq⟩
        push Not at hbods
        obtain ⟨b, hbmem, hbnd⟩ := hbods
        refine fireNF (c := HornClause.mk (minTupF (L := L) (vW2 d))
            [nAt d j b.idx (vT1 d) fun q => vW2 d (b.args q)]
            (some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d))))
          ?_ rfl hminW ?_ ?_ ?_ ?_
        · rw [nfClauses]
          exact List.mem_append_left _ (List.mem_append_right _
            (List.mem_map_of_mem hbmem))
        · intro b' hb'
          rw [List.mem_singleton] at hb'
          subst hb'
          refine derives_congr_tuple ?_ (hN b.idx (fun q => (ofLex wl) (b.args q)) hbnd)
          change _ = fun q =>
            V (Fin.addCases (vT1 d) (fun p => vW2 d (b.args p)) q)
          rw [comp_addCases, hT1]
          have hx : (fun q => (ofLex wl) (b.args q)) = fun q => V (vW2 d (b.args q)) :=
            funext fun q => (congrFun hW2 (b.args q)).symm
          rw [hx]
        · exact hT1
        · exact hXa
        · exact hW2
      · refine fireNF (c := HornClause.mk (minTupF (L := L) (vW2 d) ⊓
            ∼(eqTupF (fun q => vW2 d (ca.1.2.args q)) (xa d ca.1.2.idx)))
            [] (some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d))))
          ?_ rfl ?_ (fun b hb => absurd hb (by simp)) hT1 hXa hW2
        · rw [nfClauses]
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        · rw [Formula.realize_inf, Formula.realize_not, realize_eqTupF]
          refine ⟨hminW, fun he => hxeq ?_⟩
          rw [hXa] at he
          have hr : (fun q => V (vW2 d (ca.1.2.args q))) =
              fun q => (ofLex wl) (ca.1.2.args q) :=
            funext fun q => congrFun hW2 (ca.1.2.args q)
          rw [hr] at he
          exact he.symm
    · refine fireNF (c := HornClause.mk (minTupF (L := L) (vW2 d) ⊓
          ∼(ca.1.1.guard.relabel (vW2 d)))
          [] (some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d))))
        ?_ rfl ?_ (fun b hb => absurd hb (by simp)) hT1 hXa hW2
      · rw [nfClauses]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
      · rw [Formula.realize_inf, Formula.realize_not, Formula.realize_relabel]
        refine ⟨hminW, fun hg' => hgc ?_⟩
        have hg2 : ca.1.1.guard.Realize fun q => V (vW2 d q) := hg'
        rw [hW2] at hg2
        exact hg2
  · -- step: along the successor valuation
    intro wpl wl hlt hnb ih hnf
    have hcov : wpl ⋖ wl := ⟨hlt, fun c h1 h2 => hnb c ⟨h1, h2⟩⟩
    have hsucc : TupSucc (ofLex wpl) (ofLex wl) := tupSucc_iff_covBy.mpr hcov
    have hprevD := ih fun v hv => hnf v (le_trans hv hlt.le)
    have hfail := hnf (ofLex wl) le_rfl
    set V : Fin (kk d) → A := packV t t (padF xt) (ofLex wpl)
      (ofLex wl) (fun _ => Classical.arbitrary A) (Classical.arbitrary A) with hV
    have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
    have hXa : (fun q => V (xa d ca.1.2.idx q)) = xt := by rw [hV, packV_comp_xa]
    have hW1 : (fun q => V (vW1 d q)) = ofLex wpl := by rw [hV, packV_comp_vW1]
    have hW2 : (fun q => V (vW2 d q)) = ofLex wl := by rw [hV, packV_comp_vW2]
    have hsuccW : (succTupF (L := L) (vW1 d) (vW2 d)).Realize V := by
      refine (realize_succTupF (L := L) _ _).mpr ?_
      change TupSucc (fun q => V (vW1 d q)) fun q => V (vW2 d q)
      rw [hW1, hW2]
      exact hsucc
    have hprevAt : ∀ c' ∈ [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)],
        Derives (trProg d) ⟨c'.idx, fun q => V (c'.args q)⟩ := by
      intro c' hc'
      rw [List.mem_singleton] at hc'
      subst hc'
      refine derives_congr_tuple ?_ hprevD
      change _ = fun q =>
        V (Fin.addCases (Fin.addCases (vT1 d) (xa d ca.1.2.idx)) (vW1 d) q)
      rw [comp_addCases, comp_addCases, hT1, hXa, hW1]
    by_cases hgc : ca.1.1.guard.Realize (ofLex wl)
    · by_cases hxeq : (fun q => (ofLex wl) (ca.1.2.args q)) = xt
      · have hbods : ¬∀ b ∈ ca.1.1.body,
            derivesIn d.rules (srank d A j t) ⟨b.idx, fun q => (ofLex wl) (b.args q)⟩ :=
          fun hb => hfail ⟨hgc, hb, hxeq⟩
        push Not at hbods
        obtain ⟨b, hbmem, hbnd⟩ := hbods
        refine fireNF (c := HornClause.mk (succTupF (vW1 d) (vW2 d))
            [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d),
              nAt d j b.idx (vT1 d) fun q => vW2 d (b.args q)]
            (some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d))))
          ?_ rfl hsuccW ?_ ?_ ?_ ?_
        · rw [nfClauses]
          exact List.mem_append_right _ (List.mem_map_of_mem hbmem)
        · intro b' hb'
          rcases List.mem_cons.mp hb' with rfl | hb''
          · exact hprevAt _ (List.mem_singleton.mpr rfl)
          · rw [List.mem_singleton] at hb''
            subst hb''
            refine derives_congr_tuple ?_ (hN b.idx (fun q => (ofLex wl) (b.args q)) hbnd)
            change _ = fun q =>
              V (Fin.addCases (vT1 d) (fun p => vW2 d (b.args p)) q)
            rw [comp_addCases, hT1]
            have hx : (fun q => (ofLex wl) (b.args q)) = fun q => V (vW2 d (b.args q)) :=
              funext fun q => (congrFun hW2 (b.args q)).symm
            rw [hx]
        · exact hT1
        · exact hXa
        · exact hW2
      · refine fireNF (c := HornClause.mk (succTupF (vW1 d) (vW2 d) ⊓
            ∼(eqTupF (fun q => vW2 d (ca.1.2.args q)) (xa d ca.1.2.idx)))
            [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)]
            (some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d))))
          ?_ rfl ?_ hprevAt hT1 hXa hW2
        · rw [nfClauses]
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_self ..)))))
        · rw [Formula.realize_inf, Formula.realize_not, realize_eqTupF]
          refine ⟨hsuccW, fun he => hxeq ?_⟩
          rw [hXa] at he
          have hr : (fun q => V (vW2 d (ca.1.2.args q))) =
              fun q => (ofLex wl) (ca.1.2.args q) :=
            funext fun q => congrFun hW2 (ca.1.2.args q)
          rw [hr] at he
          exact he.symm
    · refine fireNF (c := HornClause.mk (succTupF (vW1 d) (vW2 d) ⊓
          ∼(ca.1.1.guard.relabel (vW2 d)))
          [nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)]
          (some (nfAt d j ca (vT1 d) (xa d ca.1.2.idx) (vW2 d))))
        ?_ rfl ?_ hprevAt hT1 hXa hW2
      · rw [nfClauses]
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      · rw [Formula.realize_inf, Formula.realize_not, Formula.realize_relabel]
        refine ⟨hsuccW, fun hg' => hgc ?_⟩
        have hg2 : ca.1.1.guard.Realize fun q => V (vW2 d q) := hg'
        rw [hW2] at hg2
        exact hg2

open Classical in
/-- The stage complements are derivable, walking the stages. -/
theorem derives_n (S : Fin (hs d) ×ₗ Lex (Fin (hm d) → A)) :
    ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      ¬derivesIn d.rules (orank S) ⟨i, xt⟩ →
      Derives (trProg d) ⟨nIx d (ofLex S).1 i, Fin.addCases (ofLex (ofLex S).2) xt⟩ := by
  refine order_induction (A := Fin (hs d) ×ₗ Lex (Fin (hm d) → A))
    (P := fun S => ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      ¬derivesIn d.rules (orank S) ⟨i, xt⟩ →
      Derives (trProg d) ⟨nIx d (ofLex S).1 i, Fin.addCases (ofLex (ofLex S).2) xt⟩)
    ?_ ?_ S
  · -- the bottom stage
    intro S₀ hbot i xt _
    obtain ⟨hj, ht⟩ :=
      (prodLex_isBot_iff (a := (ofLex S₀).1) (b := (ofLex S₀).2)).mp hbot
    have hj0 : (ofLex S₀).1 = j0 d :=
      le_antisymm (hj (j0 d)) (by rw [Fin.le_def]; simp [j0])
    have key := derives_nBase (d := d) (tup_isBot_iff.mp ht) xt
    rw [← hj0] at key
    exact key
  · -- a cover of stages
    intro S₀ S₁ hlt hnb ih i xt hnd
    have hcov : S₀ ⋖ S₁ := ⟨hlt, fun c h1 h2 => hnb c ⟨h1, h2⟩⟩
    rw [orank_covBy hcov] at hnd
    have hjj : ((ofLex S₀).1, (ofLex S₁).1) ∈ stagePairs d :=
      stagePairs_of_covBy (u := (ofLex S₀).2) (u' := (ofLex S₁).2) hcov
    obtain ⟨mA, hmA⟩ := Finite.exists_max (fun a : A => a)
    set V : Fin (kk d) → A := packV (ofLex (ofLex S₀).2) (ofLex (ofLex S₁).2)
      (padF xt) (fun _ => mA) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (Classical.arbitrary A) with hV
    have hcmem : (HornClause.mk (stageG d (ofLex S₀).1 (ofLex S₁).1 ⊓ maxTupF (vW1 d))
        (nAt d (ofLex S₀).1 i (vT1 d) (xa d i) ::
          (((headed d).attach.filter fun ca => ca.1.2.idx = i).map fun ca =>
            nfAt d (ofLex S₀).1 ca (vT1 d) (xa d ca.1.2.idx) (vW1 d)))
        (some (nAt d (ofLex S₁).1 i (vT2 d) (xa d i)))) ∈ trProg d :=
      mem_trProg_nStep (List.mem_flatMap.mpr ⟨((ofLex S₀).1, (ofLex S₁).1), hjj,
        List.mem_map.mpr ⟨i, mem_iotaList d i, rfl⟩⟩)
    have hT1 : (fun q => V (vT1 d q)) = ofLex (ofLex S₀).2 := by
      rw [hV, packV_comp_vT1]
    have hT2 : (fun q => V (vT2 d q)) = ofLex (ofLex S₁).2 := by
      rw [hV, packV_comp_vT2]
    have hW1 : (fun q => V (vW1 d q)) = fun _ => mA := by rw [hV, packV_comp_vW1]
    have hgV : (stageG d (ofLex S₀).1 (ofLex S₁).1 ⊓ maxTupF (vW1 d)).Realize V := by
      rw [Formula.realize_inf]
      constructor
      · refine stageG_realize hjj ?_
        rw [hT1, hT2]
        exact hcov
      · refine (realize_maxTupF (L := L) _).mpr fun p a' => ?_
        rw [congrFun hW1 p]
        exact hmA a'
    have hbV : ∀ b ∈ (nAt d (ofLex S₀).1 i (vT1 d) (xa d i) ::
        (((headed d).attach.filter fun ca => ca.1.2.idx = i).map fun ca =>
          nfAt d (ofLex S₀).1 ca (vT1 d) (xa d ca.1.2.idx) (vW1 d))),
        Derives (trProg d) ⟨b.idx, fun q => V (b.args q)⟩ := by
      intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb''
      · refine derives_congr_tuple ?_
          (ih i xt fun h => hnd (derivesIn_succ h))
        change _ = fun q => V (Fin.addCases (vT1 d) (xa d i) q)
        rw [comp_addCases, hT1, hV, packV_comp_xa]
      · obtain ⟨ca, hcaf, rfl⟩ := List.mem_map.mp hb''
        have hidx : ca.1.2.idx = i := by
          have := (List.mem_filter.mp hcaf).2
          simpa using this
        subst hidx
        obtain ⟨hc', ha'⟩ := (mem_headed (d := d)).mp ca.2
        have hnf : NFsem d A (srank d A (ofLex S₀).1 (ofLex (ofLex S₀).2))
            ca.1.1 ca.1.2 xt fun _ => mA :=
          NFsem_of_not_derivesIn hc' ha' hnd _
        have key := derives_nf (fun i' xt' h => ih i' xt' h) ca xt (fun _ => mA) hnf
        refine derives_congr_tuple ?_ key
        change _ = fun q =>
          V (Fin.addCases (Fin.addCases (vT1 d) (xa d ca.1.2.idx)) (vW1 d) q)
        rw [comp_addCases, comp_addCases, hT1, hW1, hV, packV_comp_xa]
    have key := Derives.rule (rules := trProg d) hcmem
      (a := nAt d (ofLex S₁).1 i (vT2 d) (xa d i)) rfl hgV hbV
    refine derives_congr_tuple ?_ key
    change (fun q => V (Fin.addCases (vT2 d) (xa d i) q)) = _
    rw [comp_addCases, hT2, hV, packV_comp_xa]

/-! #### The subformula relations -/

private theorem mem_trProg_evalClauses {x : SubIx d} {c} (h : c ∈ evalClauses d x) :
    c ∈ trProg d :=
  mem_trProg_evalRules (mem_evalRules h)

omit [Finite A] in
private theorem derives_eval_falsum {n : ℕ} :
    ∀ hmem (v : Fin n → A),
      (evalT d A .falsum v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, .falsum⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A .falsum v → Derives (trProg d) ⟨tfIx d ⟨⟨_, .falsum⟩, hmem⟩ false, v⟩) := by
  intro hmem v
  constructor
  · intro h
    exact False.elim h
  · intro _
    have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d))) []
        (some (tfAt d ⟨⟨n, .falsum⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))))) ∈
        trProg d :=
      mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .falsum⟩, hmem⟩)
        (List.mem_singleton.mpr rfl)
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      rw [hV, packV_comp_eSel]
    have hgT : Formula.Realize (L := L.sum Language.order)
        (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
      Formula.realize_top.mpr trivial
    have key := Derives.rule (rules := trProg d) hcmem
      (a := tfAt d ⟨⟨n, .falsum⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) rfl
      hgT (fun b hb => absurd hb (by simp))
    exact derives_congr_tuple hE key
omit [Finite A] in
private theorem derives_eval_equal {n : ℕ}
    (t u : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    ∀ hmem (v : Fin n → A),
      (evalT d A (.equal t u) v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, (.equal t u)⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A (.equal t u) v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, (.equal t u)⟩, hmem⟩ false, v⟩) := by
  intro hmem v
  have hE0 : ∀ (V : Fin (kk d) → A), (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v →
      ∀ tm, (evTerm d (ctx_le_hX d hmem) tm).realize V = evTermVal v tm := by
    intro V hE tm
    rw [realize_evTerm, hE]
  constructor
  · intro h
    have hcmem : (HornClause.mk
        (Term.equal (evTerm d (ctx_le_hX d hmem) t) (evTerm d (ctx_le_hX d hmem) u)) []
        (some (tfAt d ⟨⟨n, .equal t u⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))))) ∈
        trProg d :=
      mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .equal t u⟩, hmem⟩)
        (List.mem_cons_self ..)
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      rw [hV, packV_comp_eSel]
    have hg : (Term.equal (evTerm d (ctx_le_hX d hmem) t)
        (evTerm d (ctx_le_hX d hmem) u)).Realize V := by
      rw [Formula.realize_equal, hE0 V hE, hE0 V hE]
      exact h
    have key := Derives.rule (rules := trProg d) hcmem
      (a := tfAt d ⟨⟨n, .equal t u⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) rfl hg
      (fun b hb => absurd hb (by simp))
    exact derives_congr_tuple hE key
  · intro h
    have hcmem : (HornClause.mk
        (∼(Term.equal (evTerm d (ctx_le_hX d hmem) t) (evTerm d (ctx_le_hX d hmem) u)))
        []
        (some (tfAt d ⟨⟨n, .equal t u⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))))) ∈
        trProg d :=
      mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .equal t u⟩, hmem⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      rw [hV, packV_comp_eSel]
    have hg : Formula.Realize (L := L.sum Language.order)
        (∼(Term.equal (evTerm d (ctx_le_hX d hmem) t)
          (evTerm d (ctx_le_hX d hmem) u))) V := by
      rw [Formula.realize_not, Formula.realize_equal, hE0 V hE, hE0 V hE]
      exact h
    have key := Derives.rule (rules := trProg d) hcmem
      (a := tfAt d ⟨⟨n, .equal t u⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) rfl hg
      (fun b hb => absurd hb (by simp))
    exact derives_congr_tuple hE key
private theorem derives_eval_rel {n l : ℕ}
    (R : ((L.sum Language.order).sum d.B.lang).Relations l)
    (ts : Fin l → ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    ∀ hmem (v : Fin n → A),
      (evalT d A (.rel R ts) v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, (.rel R ts)⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A (.rel R ts) v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, (.rel R ts)⟩, hmem⟩ false, v⟩) := by
  intro hmem v
  rcases R with r | r
  · have hE0 : ∀ (V : Fin (kk d) → A),
        (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v →
        (fun l => (evTerm d (ctx_le_hX d hmem) (ts l)).realize V) =
          fun l => evTermVal v (ts l) := by
      intro V hE
      funext l
      rw [realize_evTerm, hE]
    constructor
    · intro h
      have hcmem : (HornClause.mk
          (Relations.formula r fun l => evTerm d (ctx_le_hX d hmem) (ts l)) []
          (some (tfAt d ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ true
            (eSel d (ctx_le_hX d hmem))))) ∈ trProg d :=
        mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩)
          (List.mem_cons_self ..)
      set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
        (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
        (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
        rw [hV, packV_comp_eSel]
      have hg : (Relations.formula r
          fun l => evTerm d (ctx_le_hX d hmem) (ts l)).Realize V := by
        rw [Formula.realize_rel, hE0 V hE]
        exact evalT_rel_inl.mp h
      have key := Derives.rule (rules := trProg d) hcmem
        (a := tfAt d ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ true
          (eSel d (ctx_le_hX d hmem))) rfl hg (fun b hb => absurd hb (by simp))
      exact derives_congr_tuple hE key
    · intro h
      have hcmem : (HornClause.mk
          (∼(Relations.formula r fun l => evTerm d (ctx_le_hX d hmem) (ts l))) []
          (some (tfAt d ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ false
            (eSel d (ctx_le_hX d hmem))))) ∈ trProg d :=
        mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩)
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
        (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
        (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
        rw [hV, packV_comp_eSel]
      have hg : Formula.Realize (L := L.sum Language.order)
          (∼(Relations.formula r fun l => evTerm d (ctx_le_hX d hmem) (ts l))) V := by
        rw [Formula.realize_not, Formula.realize_rel, hE0 V hE]
        exact fun h2 => h (evalT_rel_inl.mpr h2)
      have key := Derives.rule (rules := trProg d) hcmem
        (a := tfAt d ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩ false
          (eSel d (ctx_le_hX d hmem))) rfl hg (fun b hb => absurd hb (by simp))
      exact derives_congr_tuple hE key
  · -- a fixed-point atom
    set xt : Fin (d.B.arity r.1) → A :=
      fun q => evTermVal v (ts (Fin.cast r.2 q)) with hxt
    constructor
    · intro h
      have hcmem : (HornClause.mk
          (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
            Term.equal (Term.var (xa d r.1 q))
              (evTerm d (ctx_le_hX d hmem) (ts (Fin.cast r.2 q)))))
          [rAt d r.1 (xa d r.1)]
          (some (tfAt d ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ true
            (eSel d (ctx_le_hX d hmem))))) ∈ trProg d :=
        mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩)
          (List.mem_cons_self ..)
      set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
        (fun _ => Classical.arbitrary A) (padF xt)
        (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
        rw [hV, packV_comp_eSel]
      have hXa : (fun q => V (xa d r.1 q)) = xt := by rw [hV, packV_comp_xa]
      have hg : (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
          Term.equal (Term.var (xa d r.1 q))
            (evTerm d (ctx_le_hX d hmem) (ts (Fin.cast r.2 q))))).Realize V := by
        rw [realize_listInf]
        intro φ hφ
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
        rw [Formula.realize_equal, Term.realize_var, realize_evTerm, hE]
        exact congrFun hXa q
      have hb : ∀ b ∈ [rAt d r.1 (xa d r.1)],
          Derives (trProg d) ⟨b.idx, fun q => V (b.args q)⟩ := by
        intro b hb
        rw [List.mem_singleton] at hb
        subst hb
        refine derives_congr_tuple hXa.symm (derives_r ?_)
        exact evalT_rel_inr.mp h
      have key := Derives.rule (rules := trProg d) hcmem
        (a := tfAt d ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ true
          (eSel d (ctx_le_hX d hmem))) rfl hg hb
      exact derives_congr_tuple hE key
    · intro h
      obtain ⟨mA, hmA⟩ := Finite.exists_max (fun a : A => a)
      have hcmem : (HornClause.mk
          (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
            Term.equal (Term.var (xa d r.1 q))
              (evTerm d (ctx_le_hX d hmem) (ts (Fin.cast r.2 q)))) ⊓ maxTupF (vT1 d))
          [nAt d (jTop d) r.1 (vT1 d) (xa d r.1)]
          (some (tfAt d ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ false
            (eSel d (ctx_le_hX d hmem))))) ∈ trProg d :=
        mem_trProg_evalClauses (d := d) (x := ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩)
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      set V : Fin (kk d) → A := packV (fun _ => mA)
        (fun _ => Classical.arbitrary A) (padF xt)
        (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
        rw [hV, packV_comp_eSel]
      have hXa : (fun q => V (xa d r.1 q)) = xt := by rw [hV, packV_comp_xa]
      have hT1 : (fun q => V (vT1 d q)) = fun _ => mA := by rw [hV, packV_comp_vT1]
      have hg : (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
          Term.equal (Term.var (xa d r.1 q))
            (evTerm d (ctx_le_hX d hmem) (ts (Fin.cast r.2 q)))) ⊓
          maxTupF (vT1 d)).Realize V := by
        rw [Formula.realize_inf]
        constructor
        · rw [realize_listInf]
          intro φ hφ
          obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
          rw [Formula.realize_equal, Term.realize_var, realize_evTerm, hE]
          exact congrFun hXa q
        · refine (realize_maxTupF (L := L) _).mpr fun p a' => ?_
          rw [congrFun hT1 p]
          exact hmA a'
      have hcard : Nat.card (BAtom d.B A) ≤ srank d A (jTop d) fun _ => mA :=
        card_le_srank_top d fun p a' => hmA a'
      have hnd : ¬derivesIn d.rules (srank d A (jTop d) fun _ => mA) ⟨r.1, xt⟩ :=
        fun hder => h (evalT_rel_inr.mpr
          ((derivesIn_iff_derives_of_card_le hcard).mp hder))
      have hb : ∀ b ∈ [nAt d (jTop d) r.1 (vT1 d) (xa d r.1)],
          Derives (trProg d) ⟨b.idx, fun q => V (b.args q)⟩ := by
        intro b hb
        rw [List.mem_singleton] at hb
        subst hb
        have key := derives_n (toLex ((jTop d, toLex fun _ => mA) :
          Fin (hs d) × Lex (Fin (hm d) → A))) r.1 xt hnd
        refine derives_congr_tuple ?_ key
        change _ = fun q => V (Fin.addCases (vT1 d) (xa d r.1) q)
        rw [comp_addCases, hT1, hXa]
        rfl
      have key := Derives.rule (rules := trProg d) hcmem
        (a := tfAt d ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩ false
          (eSel d (ctx_le_hX d hmem))) rfl hg hb
      exact derives_congr_tuple hE key
omit [Finite A] in
private theorem derives_eval_imp {n : ℕ}
    (a b : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n)
    (iha : ∀ hmem (v : Fin n → A),
      (evalT d A a v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, a⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A a v → Derives (trProg d) ⟨tfIx d ⟨⟨_, a⟩, hmem⟩ false, v⟩))
    (ihb : ∀ hmem (v : Fin n → A),
      (evalT d A b v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, b⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A b v → Derives (trProg d) ⟨tfIx d ⟨⟨_, b⟩, hmem⟩ false, v⟩)) :
    ∀ hmem (v : Fin n → A),
      (evalT d A (a.imp b) v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, (a.imp b)⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A (a.imp b) v → Derives (trProg d) ⟨tfIx d ⟨⟨_, (a.imp b)⟩, hmem⟩ false, v⟩) := by
  intro hmem v
  have hla := left_mem_out d hmem
  have hrb := right_mem_out d hmem
  constructor
  · intro h
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      rw [hV, packV_comp_eSel]
    by_cases hA : evalT d A a v
    · have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
          [tfAt d ⟨⟨n, b⟩, hrb⟩ true (eSel d (ctx_le_hX d hmem))]
          (some (tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))))) ∈
          trProg d :=
        mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.imp b⟩, hmem⟩)
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hb : ∀ b' ∈ [tfAt d ⟨⟨n, b⟩, hrb⟩ true (eSel d (ctx_le_hX d hmem))],
          Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
        intro b' hb'
        rw [List.mem_singleton] at hb'
        subst hb'
        exact derives_congr_tuple hE.symm ((ihb hrb v).1 (h hA))
      have hgT : Formula.Realize (L := L.sum Language.order)
          (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
        Formula.realize_top.mpr trivial
      have key := Derives.rule (rules := trProg d) hcmem
        (a := tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) rfl
        hgT hb
      exact derives_congr_tuple hE key
    · have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
          [tfAt d ⟨⟨n, a⟩, hla⟩ false (eSel d (ctx_le_hX d hmem))]
          (some (tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))))) ∈
          trProg d :=
        mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.imp b⟩, hmem⟩)
          (List.mem_cons_self ..)
      have hb : ∀ b' ∈ [tfAt d ⟨⟨n, a⟩, hla⟩ false (eSel d (ctx_le_hX d hmem))],
          Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
        intro b' hb'
        rw [List.mem_singleton] at hb'
        subst hb'
        exact derives_congr_tuple hE.symm ((iha hla v).2 hA)
      have hgT : Formula.Realize (L := L.sum Language.order)
          (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
        Formula.realize_top.mpr trivial
      have key := Derives.rule (rules := trProg d) hcmem
        (a := tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) rfl
        hgT hb
      exact derives_congr_tuple hE key
  · intro h
    have h2 : evalT d A a v ∧ ¬evalT d A b v := by
      rw [evalT_imp] at h
      push Not at h
      exact h
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      rw [hV, packV_comp_eSel]
    have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
        [tfAt d ⟨⟨n, a⟩, hla⟩ true (eSel d (ctx_le_hX d hmem)),
          tfAt d ⟨⟨n, b⟩, hrb⟩ false (eSel d (ctx_le_hX d hmem))]
        (some (tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))))) ∈
        trProg d :=
      mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.imp b⟩, hmem⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hb : ∀ b' ∈ [tfAt d ⟨⟨n, a⟩, hla⟩ true (eSel d (ctx_le_hX d hmem)),
        tfAt d ⟨⟨n, b⟩, hrb⟩ false (eSel d (ctx_le_hX d hmem))],
        Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
      intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact derives_congr_tuple hE.symm ((iha hla v).1 h2.1)
      · rw [List.mem_singleton] at hb''
        subst hb''
        exact derives_congr_tuple hE.symm ((ihb hrb v).2 h2.2)
    have hgT : Formula.Realize (L := L.sum Language.order)
        (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
      Formula.realize_top.mpr trivial
    have key := Derives.rule (rules := trProg d) hcmem
      (a := tfAt d ⟨⟨n, a.imp b⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) rfl
      hgT hb
    exact derives_congr_tuple hE key
private theorem derives_eval_all {n : ℕ}
    (a : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1))
    (ih : ∀ hmem (v : Fin (n + 1) → A),
      (evalT d A a v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, a⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A a v → Derives (trProg d) ⟨tfIx d ⟨⟨_, a⟩, hmem⟩ false, v⟩)) :
    ∀ hmem (v : Fin n → A),
      (evalT d A a.all v →
        Derives (trProg d) ⟨tfIx d ⟨⟨_, a.all⟩, hmem⟩ true, v⟩) ∧
      (¬evalT d A a.all v → Derives (trProg d) ⟨tfIx d ⟨⟨_, a.all⟩, hmem⟩ false, v⟩) := by
  intro hmem v
  have hsub := all_mem_out d hmem
  have hn1 : n + 1 ≤ hX d := ctx_le_hX d hsub
  constructor
  · intro h
    -- the accumulator holds at every bound, by induction along the order
    have hAcc : ∀ z : A,
        Derives (trProg d) ⟨acIx d ⟨⟨n, a.all⟩, hmem⟩, Fin.snoc v z⟩ := by
      refine order_induction (A := A) ?_ ?_
      · intro z hz
        have hcmem : (HornClause.mk (minF (eSel d hn1 (Fin.last n)))
            [tfAt d ⟨⟨n + 1, a⟩, hsub⟩ true (eSel d hn1)]
            (some (acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d hn1)))) ∈ trProg d :=
          mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.all⟩, hmem⟩)
            (List.mem_cons_self ..)
        set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
          (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
          (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
          (padF (Fin.snoc v z)) (Classical.arbitrary A) with hV
        have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v z := by
          rw [hV, packV_comp_eSel]
        have hg : (minF (L := L) (eSel d hn1 (Fin.last n))).Realize V := by
          refine (realize_minF (L := L) _).mpr fun a' => ?_
          rw [congrFun hE1 (Fin.last n), Fin.snoc_last]
          exact hz a'
        have hb : ∀ b' ∈ [tfAt d ⟨⟨n + 1, a⟩, hsub⟩ true (eSel d hn1)],
            Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
          intro b' hb'
          rw [List.mem_singleton] at hb'
          subst hb'
          exact derives_congr_tuple hE1.symm ((ih hsub (Fin.snoc v z)).1 (h z))
        have key := Derives.rule (rules := trProg d) hcmem
          (a := acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d hn1)) rfl hg hb
        exact derives_congr_tuple hE1 key
      · intro w z hwz hnb ihz
        have hcmem : (HornClause.mk (succF (vS d) (eSel d hn1 (Fin.last n)))
            [acAt d ⟨⟨n, a.all⟩, hmem⟩ (Fin.snoc (eSel d (ctx_le_hX d hmem)) (vS d)),
              tfAt d ⟨⟨n + 1, a⟩, hsub⟩ true (eSel d hn1)]
            (some (acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d hn1)))) ∈ trProg d :=
          mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.all⟩, hmem⟩)
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
          (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
          (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
          (padF (Fin.snoc v z)) w with hV
        have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v z := by
          rw [hV, packV_comp_eSel]
        have hEn : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
          have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
          exact (Fin.snoc_inj.mp hsplit).1
        have hlast : V (eSel d hn1 (Fin.last n)) = z := by
          have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
          exact (Fin.snoc_inj.mp hsplit).2
        have hvs : V (vS d) = w := by rw [hV, packV_vS]
        have hg : (succF (L := L) (vS d) (eSel d hn1 (Fin.last n))).Realize V := by
          rw [realize_succF, hvs, hlast]
          exact ⟨hwz, hnb⟩
        have hb : ∀ b' ∈ [acAt d ⟨⟨n, a.all⟩, hmem⟩
            (Fin.snoc (eSel d (ctx_le_hX d hmem)) (vS d)),
            tfAt d ⟨⟨n + 1, a⟩, hsub⟩ true (eSel d hn1)],
            Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
          intro b' hb'
          rcases List.mem_cons.mp hb' with rfl | hb''
          · refine derives_congr_tuple ?_ ihz
            change _ = fun q =>
              V (Fin.snoc (α := fun _ => Fin (kk d)) (eSel d (ctx_le_hX d hmem))
                (vS d) q)
            rw [comp_snoc_lambda, hEn, hvs]
          · rw [List.mem_singleton] at hb''
            subst hb''
            exact derives_congr_tuple hE1.symm ((ih hsub (Fin.snoc v z)).1 (h z))
        have key := Derives.rule (rules := trProg d) hcmem
          (a := acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d hn1)) rfl hg hb
        exact derives_congr_tuple hE1 key
    -- and at a maximum it yields the truth of `∀`
    obtain ⟨mA, hmA⟩ := Finite.exists_max (fun a : A => a)
    have hcmem : (HornClause.mk (maxF (eSel d hn1 (Fin.last n)))
        [acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d hn1)]
        (some (tfAt d ⟨⟨n, a.all⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))))) ∈
        trProg d :=
      mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.all⟩, hmem⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (padF (Fin.snoc v mA)) (Classical.arbitrary A) with hV
    have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v mA := by
      rw [hV, packV_comp_eSel]
    have hEn : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
      exact (Fin.snoc_inj.mp hsplit).1
    have hlast : V (eSel d hn1 (Fin.last n)) = mA := by
      have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
      exact (Fin.snoc_inj.mp hsplit).2
    have hg : (maxF (L := L) (eSel d hn1 (Fin.last n))).Realize V := by
      refine (realize_maxF (L := L) _).mpr fun a' => ?_
      rw [hlast]
      exact hmA a'
    have hb : ∀ b' ∈ [acAt d ⟨⟨n, a.all⟩, hmem⟩ (eSel d hn1)],
        Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
      intro b' hb'
      rw [List.mem_singleton] at hb'
      subst hb'
      exact derives_congr_tuple hE1.symm (hAcc mA)
    have key := Derives.rule (rules := trProg d) hcmem
      (a := tfAt d ⟨⟨n, a.all⟩, hmem⟩ true (eSel d (ctx_le_hX d hmem))) rfl hg hb
    exact derives_congr_tuple hEn key
  · intro h
    have h2 : ∃ y : A, ¬evalT d A a (Fin.snoc v y) := by
      rw [evalT_all] at h
      push Not at h
      exact h
    obtain ⟨y, hy⟩ := h2
    have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
        [tfAt d ⟨⟨n + 1, a⟩, hsub⟩ false (eSel d hn1)]
        (some (tfAt d ⟨⟨n, a.all⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))))) ∈
        trProg d :=
      mem_trProg_evalClauses (d := d) (x := ⟨⟨n, a.all⟩, hmem⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    set V : Fin (kk d) → A := packV (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary A)
      (padF (Fin.snoc v y)) (Classical.arbitrary A) with hV
    have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v y := by
      rw [hV, packV_comp_eSel]
    have hEn : (fun q => V (eSel d (ctx_le_hX d hmem) q)) = v := by
      have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
      exact (Fin.snoc_inj.mp hsplit).1
    have hb : ∀ b' ∈ [tfAt d ⟨⟨n + 1, a⟩, hsub⟩ false (eSel d hn1)],
        Derives (trProg d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
      intro b' hb'
      rw [List.mem_singleton] at hb'
      subst hb'
      exact derives_congr_tuple hE1.symm ((ih hsub (Fin.snoc v y)).2 hy)
    have hgT : Formula.Realize (L := L.sum Language.order)
        (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
      Formula.realize_top.mpr trivial
    have key := Derives.rule (rules := trProg d) hcmem
      (a := tfAt d ⟨⟨n, a.all⟩, hmem⟩ false (eSel d (ctx_le_hX d hmem))) rfl
      hgT hb
    exact derives_congr_tuple hEn key
/-- Truth and falsity of every subformula of the output are derivable, by
structural induction; universally quantified subformulas accumulate their
instances along the order. -/
private theorem derives_eval : ∀ {n : ℕ}
    (ψ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n)
    (hmem : (⟨n, ψ⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula
      Empty n') ∈ subs d.out) (v : Fin n → A),
    (evalT d A ψ v → Derives (trProg d) ⟨tfIx d ⟨⟨n, ψ⟩, hmem⟩ true, v⟩) ∧
    (¬evalT d A ψ v → Derives (trProg d) ⟨tfIx d ⟨⟨n, ψ⟩, hmem⟩ false, v⟩) := by
  intro n ψ
  induction ψ with
  | falsum => exact derives_eval_falsum
  | equal t u => exact derives_eval_equal t u
  | rel R ts => exact derives_eval_rel R ts
  | imp a b iha ihb => exact derives_eval_imp a b iha ihb
  | all a ih => exact derives_eval_all a ih

end Completeness

/-! ### Assembly: the translated program defines the same problem -/

section Assembly

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- The truth of the output sentence, as the canonical value of its root. -/
private theorem evalT_out_iff {v : Fin 0 → A} : evalT d A d.out v ↔ d.Holds A :=
  iff_of_eq (congrArg
    (@BoundedFormula.Realize ((L.sum Language.order).sum d.B.lang) A (lfpStr d A)
      Empty 0 d.out default)
    (funext fun q => Fin.elim0 q))

variable (d)

/-- **The translated program has a satisfying assignment exactly when the
FO(LFP) definition holds.** Left to right, the canonical assignment satisfies
every rule, and the goal clause because the output is true; right to left, any
satisfying assignment contains the least model, and if the output were false
its falsity would be derivable, firing the goal clause. -/
theorem holds_iff_exists :
    d.Holds A ↔ ∃ ρ : (trBlock d).Assignment A, (trProg d).Holds ρ := by
  constructor
  · intro h
    refine ⟨canonAssign d A, ?_⟩
    intro V c hc
    rw [trProg] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact trRules_sound V hc
    · rw [List.mem_singleton] at hc
      subst hc
      rintro ⟨-, hb⟩
      have hF := fAt_holds.mp (hb _ (List.mem_cons_self ..))
      exact hF (evalT_out_iff.mpr h)
  · rintro ⟨ρ, hρ⟩
    by_contra hnh
    have hFder : Derives (trProg d)
        ⟨tfIx d ⟨⟨0, d.out⟩, self_mem_subs d.out⟩ false, Fin.elim0⟩ :=
      (derives_eval d.out (self_mem_subs d.out) Fin.elim0).2
        fun h => hnh (evalT_out_iff.mp h)
    have hρF := lfpAssign_least hρ hFder
    have hgoal := hρ (fun _ => Classical.arbitrary A) (goalClause d)
      (by rw [trProg]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
    refine hgoal ⟨Formula.realize_top.mpr trivial, ?_⟩
    intro b hb
    obtain rfl := List.mem_singleton.mp hb
    have hgen : ∀ w w' : Fin 0 → A,
        ρ (tfIx d ⟨⟨0, d.out⟩, self_mem_subs d.out⟩ false) w →
        ρ (tfIx d ⟨⟨0, d.out⟩, self_mem_subs d.out⟩ false) w' := by
      intro w w' hw
      rwa [show w' = w from funext fun q => q.elim0]
    exact hgen _ _ hρF

end Assembly

end LFPHorn

/-! ### The equivalence of FO(LFP) and SO-Horn -/

variable {L : Language.{0, 0}}

/-- **Every FO(LFP) definable problem is SO-Horn definable** – the hard
direction of Grädel's equivalence, by the staged translation above. Together
with `DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` this makes the two
formalisms interchangeable.
Registered in the Lax archive as
[`Lax535992.HornIsLeastFixedPoint.lfpDefinable_sigmaSOHornDefinable`](https://laxarchive.org/lax-535992/Lax535992.HornIsLeastFixedPoint.html#s-Lax535992.HornIsLeastFixedPoint.lfpDefinable_sigmaSOHornDefinable). -/
theorem LFPDefinable.sigmaSOHornDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : LFPDefinable P) : SigmaSOHornDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨LFPHorn.trBlock d, LFPHorn.kk d, LFPHorn.trProg d, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (LFPHorn.holds_iff_exists d)

/-- **FO(LFP) = SO-Horn** ([Grädel 1992][gradel1992capturing]): a problem is
FO(LFP) definable iff it is SO-Horn definable, on ordered structures. -/
theorem lfpDefinable_iff_sigmaSOHornDefinable [L.IsRelational] (P : DecisionProblem L) :
    LFPDefinable P ↔ SigmaSOHornDefinable P :=
  ⟨LFPDefinable.sigmaSOHornDefinable, SigmaSOHornDefinable.lfpDefinable⟩

/-- **Immerman–Vardi: `PTIME = FO(≤, LFP)`** ([Vardi 1982][vardi1982complexity];
[Immerman 1986][immerman1986relational]) – a problem is in polynomial time exactly
when it is the value of a least-fixed-point definition read over a linearly ordered
universe.

Two readings of the statement are worth separating. Against the library's own class
it is `DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable` under the definition
of `DescriptiveComplexity.PTIME` by the Horn fragment, so the mathematical content is
the pair of translations above; that the definition is *order-invariant*, the side
condition of the classical statement, is built into
`DescriptiveComplexity.LFPDefinable`, which asks for the equivalence at every linear
order. Against machines the reading is
`DescriptiveComplexity.mem_PTIME_iff_le_dtmAccept`, deterministic polynomial-time
acceptance being complete for the class; the residual gap there is the string-encoding
one documented in `DescriptiveComplexity.Problems.Machine`, not this equivalence.
Registered in the Lax archive as
[`Lax535992.ImmermanVardi.lfpDefinable_iff_mem_PTIME`](https://laxarchive.org/lax-535992/Lax535992.ImmermanVardi.html#s-Lax535992.ImmermanVardi.lfpDefinable_iff_mem_PTIME). -/
theorem lfpDefinable_iff_mem_PTIME [L.IsRelational] (P : DecisionProblem L) :
    LFPDefinable P ↔ P ∈ PTIME :=
  lfpDefinable_iff_sigmaSOHornDefinable P

/-- **SO-Horn definability is closed under complement**: through the logic
FO(LFP), where complementation is negating the output formula. This is the
statement that was out of reach of the fragment alone.
Registered in the Lax archive as
[`Lax535992.PTIMEEqCoPTIME.sigmaSOHornDefinable_compl`](https://laxarchive.org/lax-535992/Lax535992.PTIMEEqCoPTIME.html#s-Lax535992.PTIMEEqCoPTIME.sigmaSOHornDefinable_compl). -/
theorem SigmaSOHornDefinable.compl [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSOHornDefinable P) : SigmaSOHornDefinable Pᶜ :=
  LFPDefinable.sigmaSOHornDefinable (LFPDefinable.compl h.lfpDefinable)

/-! ### Level 0 of the hierarchy: `Π₀ᵖ = Σ₀ᵖ` -/

/-- Complementation is a bijection of the SO-Horn definable problems. -/
private theorem sigmaSOHornDefinable_compl_iff [L.IsRelational] (P : DecisionProblem L) :
    SigmaSOHornDefinable Pᶜ ↔ SigmaSOHornDefinable P := by
  constructor
  · intro h
    have h2 := h.compl
    rwa [DecisionProblem.compl_compl] at h2
  · exact fun h => h.compl

/-- **`Π₀ᵖ = Σ₀ᵖ`: polynomial time is closed under complement** – Grädel's
capture theorem at level 0 of the hierarchy, the identity that was open while
the fragment stood alone: it needs the least model of a Horn program computed
*inside* the fragment, which is what the translation through FO(LFP)
provides.
Registered in the Lax archive as
[`Lax564036.PolynomialTimeInHierarchy.piP_zero_eq`](https://laxarchive.org/lax-564036/Lax564036.PolynomialTimeInHierarchy.html#s-Lax564036.PolynomialTimeInHierarchy.piP_zero_eq). -/
theorem piP_zero_eq : PiP 0 = SigmaP 0 := by
  change PTIME.compl = PTIME
  refine ComplexityClass.ext (fun P => sigmaSOHornDefinable_compl_iff P) fun P => ?_
  constructor
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((sigmaSOHornDefinable_compl_iff Q).mpr hQ)
  · intro h L' _ S hS L'' _ Q hQ
    exact h S hS Q ((sigmaSOHornDefinable_compl_iff Q).mp hQ)

end DescriptiveComplexity
