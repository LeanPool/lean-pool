/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointInflationary
public import LeanPool.DescriptiveCounting.SecondOrderBlockHom
public import LeanPool.DescriptiveCounting.FixedPointHorn
import all LeanPool.DescriptiveCounting.FixedPointHorn
import all LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.OrderWalk
import all LeanPool.DescriptiveCounting.Padding

/-!
# FO(≤, IFP) into FO(LFP): the capture of the inflationary limit

The hard half of the capture theorem **FO(≤, IFP) = PTIME**
(`DescriptiveComplexity.ifpDefinable_iff_mem_PTIME`): every ordered
inflationary definition translates back into FO(LFP)
(`DescriptiveComplexity.IFPDefinable.lfpDefinable`), so with the embedding of
`DescriptiveComplexity.FixedPointInflationary` the two logics are
interchangeable (`DescriptiveComplexity.ifpDefinable_iff_lfpDefinable`) and
FO(≤, IFP) captures polynomial time through Grädel's Horn fragment.

## The construction

Let `d : StepDef (L.sum Language.order)`. Because inflation adds and never
removes, both a stage and its *complement* advance positively:

* `x ∈ stage (s+1) of i` iff `x ∈ stage s` **or** `step i` holds at stage
  `s` – positive in the stage relations and in the truth relations below;
* `x ∉ stage (s+1) of i` iff `x ∉ stage s` **and** `step i` *fails* at
  stage `s` – positive in the complements and the falsity relations.

So the translated program (`DescriptiveComplexity.IFPLfp.trDef`) carries, for
each stage index `(j, t)` (the `DescriptiveComplexity.FixedPointHorn` stage
walk: `hs` static copies of `hm`-tuples in lexicographic order), the stage
`S`, its complement `N`, and a *dual evaluator* deriving truth `T` and
falsity `F` of every subformula of every step formula at that stage, with an
accumulator `AC` walking the order under universal quantifiers.
Base-vocabulary atoms become guards; block atoms read `S`/`N` at the current
stage – which is what distinguishes this evaluator from the one of
`DescriptiveComplexity.FixedPointHorn`, whose subformula relations read the
finished fixed point: here evaluation is *per stage*, mutually recursive with
the stages themselves, stratified as stage `s` before evaluator at `s` before
stage `s + 1`. The answer variables `R` are read off the maximal stage, and
the output sentence survives *unchanged* modulo the block injection
`DescriptiveComplexity.SOBlock.homLHom` – the point of targeting FO(LFP)
rather than SO-Horn: no evaluator is ever built for the output.

## Correctness

The canonical assignment (`DescriptiveComplexity.IFPLfp.canonAssign`) gives
every translated variable its intended value; soundness
(`DescriptiveComplexity.IFPLfp.trRules_sound`) shows it satisfies every rule,
and completeness derives every canonical fact – the dual evaluator by
induction on the subformula at a fixed stage
(`DescriptiveComplexity.IFPLfp.derives_tf`, with the stage's own `S`/`N`
derivability as hypotheses), the stages by induction along the cover walk of
the stage order (`DescriptiveComplexity.IFPLfp.derives_SN`), and the answer
variables by reading the top of the walk
(`DescriptiveComplexity.IFPLfp.derives_r`, through
`DescriptiveComplexity.IFPLfp.inflStage_srank_top`: the top rank is beyond
the atom count, where the stages have stabilized to the limit).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace IFPLfp

variable {L : Language.{0, 0}} (d : StepDef (L.sum Language.order))

/-! ### The step formulas, over `Empty` -/

/-- A step formula, as a bounded formula over `Empty` whose binders are the
arguments of its variable: the form the subformula machinery of
`DescriptiveComplexity.FixedPointHorn` operates on. -/
def stepB (i : d.B.ι) :
    ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (d.B.arity i + 0) :=
  BoundedFormula.relabel (Sum.inr : Fin (d.B.arity i) → Empty ⊕ Fin (d.B.arity i))
    (d.step i)

/-! ### Dimensions -/

/-- The width of a stage tuple: the arity bound of the block. -/
noncomputable def hm : ℕ := blockArityBound d.B

/-- The number of copies of the stage relations: as in
`DescriptiveComplexity.LFPHorn.hs`, enough for `(hc + 1) · n^hm` stages to
exceed the number of atoms of the block on every nonempty structure. -/
noncomputable def hc : ℕ := Nat.card d.B.ι

@[inherit_doc hc]
noncomputable def hs : ℕ := hc d + 1

open Classical in
/-- The number of variables reserved for evaluating the step formulas: a
bound on the binder depths of all their subformulas. -/
noncomputable def hX : ℕ :=
  letI := Fintype.ofFinite d.B.ι
  (Finset.univ.sup fun i => contextBound (stepB d i) : ℕ)

private theorem contextBound_le_hX (i : d.B.ι) : contextBound (stepB d i) ≤ hX d := by
  let := Fintype.ofFinite d.B.ι
  have h : contextBound (stepB d i) ≤ (Finset.univ.sup fun i => contextBound (stepB d i) : ℕ) :=
    Finset.le_sup (f := fun i => contextBound (stepB d i)) (Finset.mem_univ i)
  exact h

/-- The universally quantified first-order variables shared by all clauses:
two stage-tuple blocks (current and next), the atom tuple, the evaluation
block, and one spare for the accumulators. -/
noncomputable def kk : ℕ := 3 * hm d + hX d + 1

/-! ### The block of the translation -/

/-- Index of the truth, falsity and accumulator relations: a variable of the
block together with a subformula of its step formula. -/
def SubIx : Type :=
  Σ i : d.B.ι,
    {x : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n' //
      x ∈ subs (stepB d i)}

instance (i : d.B.ι) :
    Finite {x : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n' //
      x ∈ subs (stepB d i)} :=
  (List.finite_toSet _).to_subtype

instance : Finite (SubIx d) :=
  inferInstanceAs (Finite (Σ i : d.B.ι,
    {x : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n' //
      x ∈ subs (stepB d i)}))

/-- The binder depth of a subformula index is within the evaluation block. -/
theorem subIx_le_hX (x : SubIx d) : x.2.1.1 ≤ hX d :=
  le_trans (fst_le_contextBound x.2.2) (contextBound_le_hX d x.1)

/-- The relation variables of the translated program: the answer variables
`R`, the stages `S`, their complements `N`, the truth/falsity relations
`T`/`F` (`Bool`-tagged), and the `∀`-accumulators `AC`. -/
abbrev TrIx : Type :=
  d.B.ι ⊕ (Bool × Fin (hs d) × d.B.ι) ⊕ ((Fin (hs d) × SubIx d × Bool) ⊕ (Fin (hs d) × SubIx d))

/-- The answer variables. -/
abbrev rIx (i : d.B.ι) : TrIx d := Sum.inl i

/-- `S j i (t, x)`: at stage `(j, t)`, the atom `i x` is derived. -/
abbrev sIx (j : Fin (hs d)) (i : d.B.ι) : TrIx d := Sum.inr (Sum.inl (true, j, i))

/-- `N j i (t, x)`: at stage `(j, t)`, the atom `i x` is *not* derived. -/
abbrev nIx (j : Fin (hs d)) (i : d.B.ι) : TrIx d := Sum.inr (Sum.inl (false, j, i))

/-- Truth (`true`) and falsity (`false`) of a subformula of a step formula at
a stage. -/
abbrev tfIx (j : Fin (hs d)) (x : SubIx d) (b : Bool) : TrIx d :=
  Sum.inr (Sum.inr (Sum.inl (j, x, b)))

/-- The accumulator of a universally quantified subformula at a stage. -/
abbrev acIx (j : Fin (hs d)) (x : SubIx d) : TrIx d := Sum.inr (Sum.inr (Sum.inr (j, x)))

/-- The arities: answer variables keep theirs, stage relations carry a stage
tuple in front of theirs, subformula relations a stage tuple in front of
their binder depth, accumulators one more. -/
noncomputable def trArity : TrIx d → ℕ
  | Sum.inl i => d.B.arity i
  | Sum.inr (Sum.inl (_, _, i)) => hm d + d.B.arity i
  | Sum.inr (Sum.inr (Sum.inl (_, x, _))) => hm d + x.2.1.1
  | Sum.inr (Sum.inr (Sum.inr (_, x))) => hm d + x.2.1.1 + 1

/-- The block of the translated program. -/
noncomputable def trBlock : SOBlock := ⟨TrIx d, trArity d⟩

/-! ### The shared first-order variables and their layout -/

/-- The current stage tuple `t`. -/
noncomputable def vT1 (q : Fin (hm d)) : Fin (kk d) :=
  ⟨q, by have := q.isLt; simp only [kk]; omega⟩

/-- The next stage tuple `t'`. -/
noncomputable def vT2 (q : Fin (hm d)) : Fin (kk d) :=
  ⟨hm d + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The atom tuple `x`, the scratch the block-atom evaluation rules equate
with the (evaluated) arguments of a block atom. -/
noncomputable def vX (q : Fin (hm d)) : Fin (kk d) :=
  ⟨2 * hm d + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The evaluation block `ē`, holding the free variables of a subformula of a
step formula. -/
noncomputable def vE (q : Fin (hX d)) : Fin (kk d) :=
  ⟨3 * hm d + q, by have := q.isLt; simp only [kk]; omega⟩

/-- The spare variable, the accumulator's predecessor. -/
noncomputable def vS : Fin (kk d) :=
  ⟨3 * hm d + hX d, by simp only [kk]; omega⟩

/-- The first `n` variables of the evaluation block. -/
noncomputable def eSel {n : ℕ} (hn : n ≤ hX d) (q : Fin n) : Fin (kk d) :=
  vE d ⟨q, lt_of_lt_of_le q.isLt hn⟩

/-- The atom tuple of a relation variable `i`, inside the `x` block. -/
noncomputable def xa (i : d.B.ι) (q : Fin (d.B.arity i)) : Fin (kk d) :=
  vX d ⟨q, lt_of_lt_of_le q.isLt (arity_le_blockArityBound d.B i)⟩

/-- The first copy. -/
noncomputable def j0 : Fin (hs d) := ⟨0, by simp only [hs]; omega⟩

/-- The last copy. -/
noncomputable def jTop : Fin (hs d) := ⟨hc d, by simp only [hs]; omega⟩

/-! ### Atom builders -/

/-- An atom of an answer variable. -/
noncomputable def rAt (i : d.B.ι) (sel : Fin (d.B.arity i) → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨rIx d i, sel⟩

/-- An atom `S j i (t, x)`. -/
noncomputable def sAt (j : Fin (hs d)) (i : d.B.ι) (ts : Fin (hm d) → Fin (kk d))
    (xs : Fin (d.B.arity i) → Fin (kk d)) : SOAtom (trBlock d) (kk d) :=
  ⟨sIx d j i, Fin.addCases ts xs⟩

/-- An atom `N j i (t, x)`. -/
noncomputable def nAt (j : Fin (hs d)) (i : d.B.ι) (ts : Fin (hm d) → Fin (kk d))
    (xs : Fin (d.B.arity i) → Fin (kk d)) : SOAtom (trBlock d) (kk d) :=
  ⟨nIx d j i, Fin.addCases ts xs⟩

/-- A truth or falsity atom of a subformula at a stage. -/
noncomputable def tfAt (j : Fin (hs d)) (x : SubIx d) (b : Bool)
    (ts : Fin (hm d) → Fin (kk d)) (es : Fin x.2.1.1 → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨tfIx d j x b, Fin.addCases ts es⟩

/-- An accumulator atom of a subformula at a stage. -/
noncomputable def acAt (j : Fin (hs d)) (x : SubIx d)
    (ts : Fin (hm d) → Fin (kk d)) (es : Fin (x.2.1.1 + 1) → Fin (kk d)) :
    SOAtom (trBlock d) (kk d) :=
  ⟨acIx d j x, Fin.addCases (m := hm d) (n := x.2.1.1 + 1) ts es⟩

/-! ### The rules of the translated program -/

/-- The stage-successor pairs of copies: within one copy, or crossing to the
next (as in `DescriptiveComplexity.LFPHorn.stagePairs`). -/
noncomputable def stagePairs : List (Fin (hs d) × Fin (hs d)) :=
  StageWalk.pairs (hs d)

/-- The guard stepping from stage `(j, t)` to stage `(j', t')`: the successor
tuple within a copy, the wrap-around between consecutive copies. -/
noncomputable def stageG (j j' : Fin (hs d)) :
    (L.sum Language.order).Formula (Fin (kk d)) :=
  StageWalk.guard (vT1 d) (vT2 d) j j'

/-- The root subformula of a variable's step formula. -/
def rootSub (i : d.B.ι) : SubIx d :=
  ⟨i, ⟨⟨d.B.arity i + 0, stepB d i⟩, self_mem_subs (stepB d i)⟩⟩

/-- The evaluation selector of the root subformula is the atom tuple. -/
noncomputable def rootSel (i : d.B.ι) : Fin ((rootSub d i).2.1.1) → Fin (kk d) :=
  eSel d (subIx_le_hX d (rootSub d i))

/-! #### The stage rules -/

/-- Carry: a derived atom stays derived at the next stage. -/
noncomputable def sCarry : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (stagePairs d).flatMap fun jj =>
    (d.B.idxList).map fun i =>
      { guard := stageG d jj.1 jj.2
        body := [sAt d jj.1 i (vT1 d) (xa d i)]
        head := some (sAt d jj.2 i (vT2 d) (xa d i)) }

/-- Derive: an atom whose step formula is true at a stage is derived at the
next stage. This is where inflation is *used*: the new stage is the old one
plus what the step formulas add. -/
noncomputable def sDerive : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (stagePairs d).flatMap fun jj =>
    (d.B.idxList).map fun i =>
      { guard := stageG d jj.1 jj.2
        body := [tfAt d jj.1 (rootSub d i) true (vT1 d) (rootSel d i)]
        head := some (sAt d jj.2 i (vT2 d) (rootSel d i)) }

/-- Base: at the first stage, nothing is derived. -/
noncomputable def nBase : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (d.B.idxList).map fun i =>
    { guard := minTupF (vT1 d)
      body := []
      head := some (nAt d (j0 d) i (vT1 d) (xa d i)) }

/-- Complement step: an underived atom whose step formula is *false* at a
stage stays underived at the next stage. This is where inflation *pays*:
non-membership in the next stage is a conjunction of two positive atoms. -/
noncomputable def nStep : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (stagePairs d).flatMap fun jj =>
    (d.B.idxList).map fun i =>
      { guard := stageG d jj.1 jj.2
        body := [nAt d jj.1 i (vT1 d) (rootSel d i),
          tfAt d jj.1 (rootSub d i) false (vT1 d) (rootSel d i)]
        head := some (nAt d jj.2 i (vT2 d) (rootSel d i)) }

/-- Read-off: the answer variables hold the maximal stage. -/
noncomputable def rRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (d.B.idxList).map fun i =>
    { guard := maxTupF (vT1 d)
      body := [sAt d (jTop d) i (vT1 d) (xa d i)]
      head := some (rAt d i (xa d i)) }

/-! #### The dual evaluator -/

/-- A term of a subformula, as a term of the guard vocabulary over the
evaluation variables. -/
noncomputable def evTerm {n : ℕ} (hn : n ≤ hX d)
    (t : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    (L.sum Language.order).Term (Fin (kk d)) :=
  (stripTerm t).relabel (Sum.elim (fun e => e.elim) (eSel d hn))

/-- The rules evaluating one subformula of a step formula at the stages, by
shape: the dual `T`/`F` derivation, with base-vocabulary atoms and equalities
as guards, block atoms reading `S`/`N` at the current stage, and the
accumulator walking the order under a universal quantifier. -/
noncomputable def evalClauses (j : Fin (hs d)) (x : SubIx d) :
    HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  match x with
  | ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩ =>
    [{ guard := ⊤
       body := []
       head := some (tfAt d j ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩ false (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩))) }]
  | ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩ =>
    [{ guard := Term.equal (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩) t)
         (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩) u)
       body := []
       head := some (tfAt d j ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩ true (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩))) },
     { guard := ∼(Term.equal (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩) t)
         (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩) u))
       body := []
       head := some (tfAt d j ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩ false (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .equal t u⟩, hmem⟩⟩))) }]
  | ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ =>
    [{ guard := Relations.formula r fun l =>
         evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩) (ts l)
       body := []
       head := some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ true (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩))) },
     { guard := ∼(Relations.formula r fun l =>
         evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩) (ts l))
       body := []
       head := some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ false (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩))) }]
  | ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ =>
    [{ guard := listInf ((List.finRange (d.B.arity r.1)).map fun q =>
         Term.equal (Term.var (xa d r.1 q))
           (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩)
             (ts (Fin.cast r.2 q))))
       body := [sAt d j r.1 (vT1 d) (xa d r.1)]
       head := some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ true (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩))) },
     { guard := listInf ((List.finRange (d.B.arity r.1)).map fun q =>
         Term.equal (Term.var (xa d r.1 q))
           (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩)
             (ts (Fin.cast r.2 q))))
       body := [nAt d j r.1 (vT1 d) (xa d r.1)]
       head := some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ false (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩))) }]
  | ⟨i, ⟨⟨n, .imp a b⟩, hmem⟩⟩ =>
    [{ guard := ⊤
       body := [tfAt d j ⟨i, ⟨⟨n, a⟩, subs_trans hmem (left_mem_subs_imp a b)⟩⟩ false
         (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩))]
       head := some (tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ true (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩))) },
     { guard := ⊤
       body := [tfAt d j ⟨i, ⟨⟨n, b⟩, subs_trans hmem (right_mem_subs_imp a b)⟩⟩ true
         (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩))]
       head := some (tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ true (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩))) },
     { guard := ⊤
       body := [tfAt d j ⟨i, ⟨⟨n, a⟩, subs_trans hmem (left_mem_subs_imp a b)⟩⟩ true
         (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩)),
         tfAt d j ⟨i, ⟨⟨n, b⟩, subs_trans hmem (right_mem_subs_imp a b)⟩⟩ false
           (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩))]
       head := some (tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ false (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩))) }]
  | ⟨i, ⟨⟨n, .all a⟩, hmem⟩⟩ =>
    [{ guard := minF (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
         subs_trans hmem (mem_subs_all a)⟩⟩) (Fin.last n))
       body := [tfAt d j ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩ true
         (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
           subs_trans hmem (mem_subs_all a)⟩⟩))]
       head := some (acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩))) },
     { guard := succF (vS d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
         subs_trans hmem (mem_subs_all a)⟩⟩) (Fin.last n))
       body := [acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
           (Fin.snoc (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩)) (vS d)),
         tfAt d j ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩ true
           (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
             subs_trans hmem (mem_subs_all a)⟩⟩))]
       head := some (acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩))) },
     { guard := maxF (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
         subs_trans hmem (mem_subs_all a)⟩⟩) (Fin.last n))
       body := [acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩))]
       head := some (tfAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ true (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩))) },
     { guard := ⊤
       body := [tfAt d j ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩ false
         (vT1 d) (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
           subs_trans hmem (mem_subs_all a)⟩⟩))]
       head := some (tfAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ false (vT1 d)
         (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩))) }]

/-- All evaluation rules: every stage copy, every variable, every subformula
of its step formula. -/
noncomputable def evalRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  (List.finRange (hs d)).flatMap fun j =>
    (d.B.idxList).flatMap fun i =>
      (subs (stepB d i)).attach.flatMap fun x => evalClauses d j ⟨i, ⟨x.1, x.2⟩⟩

/-- The rules of the translated program. -/
noncomputable def trRules : HornProgram (L.sum Language.order) (trBlock d) (kk d) :=
  sCarry d ++ sDerive d ++ nBase d ++ nStep d ++ rRules d ++ evalRules d

/-! ### The translated definition -/

/-- The arities of the answer variables are those of the original block. -/
theorem trArity_rIx (i : d.B.ι) : (trBlock d).arity (rIx d i) = d.B.arity i := rfl

/-- **The translated FO(LFP) definition**: the rules above, with the original
output sentence transported along the answer-variable injection
(`DescriptiveComplexity.SOBlock.homLHom`). -/
private noncomputable def trDef : LFPDef L where
  B := trBlock d
  k := kk d
  rules := trRules d
  out := (LHom.sumMap (LHom.id (L.sum Language.order))
    (SOBlock.homLHom (B := d.B) (B' := trBlock d) (rIx d) (trArity_rIx d))).onSentence d.out

/-! ### The canonical assignment

Over a fixed ordered structure, each relation variable of the translated
block has an intended value; the correctness proof (to come) will show that
the least model of the rules is exactly this assignment. Every predicate is a
*named* definition, so reduction stops at it (the
`DescriptiveComplexity.FixedPointHorn` discipline). -/

section Canonical

variable (A : Type) [L.Structure A] [LinearOrder A]

/-- The rank of a stage: its position in the lexicographic order of the pairs
of a copy index and a stage tuple. -/
noncomputable def srank (j : Fin (hs d)) (t : Fin (hm d) → A) : ℕ :=
  StageWalk.rank A j t

/-- A stage of the inflationary iteration, at a stage index. -/
noncomputable def canonS (j : Fin (hs d)) (i : d.B.ι)
    (w : Fin (hm d + d.B.arity i) → A) : Prop :=
  d.inflStage A (srank d A j fun q => w (Fin.castAdd (d.B.arity i) q)) i
    fun q => w (Fin.natAdd (hm d) q)

/-- The complement of a stage of the inflationary iteration. -/
noncomputable def canonN (j : Fin (hs d)) (i : d.B.ι)
    (w : Fin (hm d + d.B.arity i) → A) : Prop :=
  ¬d.inflStage A (srank d A j fun q => w (Fin.castAdd (d.B.arity i) q)) i
    fun q => w (Fin.natAdd (hm d) q)

/-- The structure interpreting the expanded vocabulary at a stage of the
iteration – the structure the step formulas are read in there. -/
@[instance_reducible]
noncomputable def stageStr (r : ℕ) :
    ((L.sum Language.order).sum d.B.lang).Structure A :=
  @sumStructure (L.sum Language.order) d.B.lang A _ (d.B.structure (d.inflStage A r))

/-- Truth of a subformula of a step formula at a stage of the iteration. -/
noncomputable def evalT (r : ℕ) {n : ℕ}
    (ψ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n)
    (v : Fin n → A) : Prop :=
  @BoundedFormula.Realize ((L.sum Language.order).sum d.B.lang) A (stageStr d A r)
    Empty n ψ default v

/-- The intended accumulator of a universally quantified subformula at a
stage: the quantified subformula holds up to the last argument. Other
subformulas have no accumulator; theirs is empty. -/
noncomputable def canonAc (r : ℕ) : (x : SubIx d) → (Fin (x.2.1.1 + 1) → A) → Prop :=
  fun x =>
    match x with
    | ⟨_, ⟨⟨n, .all χ⟩, _⟩⟩ => fun w =>
        ∀ y : A, y ≤ w (Fin.last n) →
          evalT d A r χ (Fin.snoc (fun q => w q.castSucc) y)
    | _ => fun _ => False

/-- The canonical assignment: the limit on the answer variables, the stages
and their complements on `S`/`N`, truth and falsity of the step formulas'
subformulas at the stages, and the accumulators. -/
noncomputable def canonAssign : (trBlock d).Assignment A := fun ix =>
  match ix with
  | Sum.inl i => fun x => d.inflLimit A i x
  | Sum.inr (Sum.inl (true, j, i)) => canonS d A j i
  | Sum.inr (Sum.inl (false, j, i)) => canonN d A j i
  | Sum.inr (Sum.inr (Sum.inl (j, x, true))) => fun w =>
      evalT d A (srank d A j fun q => w (Fin.castAdd x.2.1.1 q)) x.2.1.2
        fun q => w (Fin.natAdd (hm d) q)
  | Sum.inr (Sum.inr (Sum.inl (j, x, false))) => fun w =>
      ¬evalT d A (srank d A j fun q => w (Fin.castAdd x.2.1.1 q)) x.2.1.2
        fun q => w (Fin.natAdd (hm d) q)
  | Sum.inr (Sum.inr (Sum.inr (j, x))) => fun w =>
      canonAc d A (srank d A j fun q => w (Fin.castAdd (x.2.1.1 + 1) q)) x
        fun q => w (Fin.natAdd (hm d) q)

/-! #### Atom characterizations under the canonical assignment -/

variable {d} {A}

private theorem rAt_holds {i : d.B.ι} {sel : Fin (d.B.arity i) → Fin (kk d)}
    {V : Fin (kk d) → A} :
    (rAt d i sel).Holds (canonAssign d A) V ↔ d.inflLimit A i fun q => V (sel q) :=
  Iff.rfl

private theorem sAt_holds {j : Fin (hs d)} {i : d.B.ι} {ts : Fin (hm d) → Fin (kk d)}
    {xs : Fin (d.B.arity i) → Fin (kk d)} {V : Fin (kk d) → A} :
    (sAt d j i ts xs).Holds (canonAssign d A) V ↔
      d.inflStage A (srank d A j fun q => V (ts q)) i fun q => V (xs q) := by
  have h0 : (sAt d j i ts xs).Holds (canonAssign d A) V ↔
      canonS d A j i fun q => V (Fin.addCases ts xs q) := Iff.rfl
  rw [h0, LFPHorn.comp_addCases V ts xs, canonS]
  have ha : (fun q => Fin.addCases (m := hm d) (fun q => V (ts q)) (fun q => V (xs q))
      (Fin.castAdd (d.B.arity i) q)) = fun q => V (ts q) :=
    funext fun q => Fin.addCases_left q
  have hb : (fun q => Fin.addCases (m := hm d) (fun q => V (ts q)) (fun q => V (xs q))
      (Fin.natAdd (hm d) q)) = fun q => V (xs q) :=
    funext fun q => Fin.addCases_right q
  rw [ha, hb]

private theorem nAt_holds {j : Fin (hs d)} {i : d.B.ι} {ts : Fin (hm d) → Fin (kk d)}
    {xs : Fin (d.B.arity i) → Fin (kk d)} {V : Fin (kk d) → A} :
    (nAt d j i ts xs).Holds (canonAssign d A) V ↔
      ¬d.inflStage A (srank d A j fun q => V (ts q)) i fun q => V (xs q) := by
  have h0 : (nAt d j i ts xs).Holds (canonAssign d A) V ↔
      canonN d A j i fun q => V (Fin.addCases ts xs q) := Iff.rfl
  rw [h0, LFPHorn.comp_addCases V ts xs, canonN]
  have ha : (fun q => Fin.addCases (m := hm d) (fun q => V (ts q)) (fun q => V (xs q))
      (Fin.castAdd (d.B.arity i) q)) = fun q => V (ts q) :=
    funext fun q => Fin.addCases_left q
  have hb : (fun q => Fin.addCases (m := hm d) (fun q => V (ts q)) (fun q => V (xs q))
      (Fin.natAdd (hm d) q)) = fun q => V (xs q) :=
    funext fun q => Fin.addCases_right q
  rw [ha, hb]

private theorem tAt_holds {j : Fin (hs d)} {x : SubIx d} {ts : Fin (hm d) → Fin (kk d)}
    {es : Fin x.2.1.1 → Fin (kk d)} {V : Fin (kk d) → A} :
    (tfAt d j x true ts es).Holds (canonAssign d A) V ↔
      evalT d A (srank d A j fun q => V (ts q)) x.2.1.2 fun q => V (es q) := by
  have h0 : (tfAt d j x true ts es).Holds (canonAssign d A) V ↔
      evalT d A (srank d A j fun q =>
          (fun p => V (Fin.addCases ts es p)) (Fin.castAdd x.2.1.1 q)) x.2.1.2
        (fun q => (fun p => V (Fin.addCases ts es p)) (Fin.natAdd (hm d) q)) := Iff.rfl
  rw [h0]
  have ha : (fun q => (fun p => V (Fin.addCases ts es p)) (Fin.castAdd x.2.1.1 q)) =
      fun q => V (ts q) := funext fun q => congrArg V (Fin.addCases_left q)
  have hb : (fun q => (fun p => V (Fin.addCases ts es p)) (Fin.natAdd (hm d) q)) =
      fun q => V (es q) := funext fun q => congrArg V (Fin.addCases_right q)
  rw [ha, hb]

private theorem fAt_holds {j : Fin (hs d)} {x : SubIx d} {ts : Fin (hm d) → Fin (kk d)}
    {es : Fin x.2.1.1 → Fin (kk d)} {V : Fin (kk d) → A} :
    (tfAt d j x false ts es).Holds (canonAssign d A) V ↔
      ¬evalT d A (srank d A j fun q => V (ts q)) x.2.1.2 fun q => V (es q) := by
  have h0 : (tfAt d j x false ts es).Holds (canonAssign d A) V ↔
      ¬evalT d A (srank d A j fun q =>
          (fun p => V (Fin.addCases ts es p)) (Fin.castAdd x.2.1.1 q)) x.2.1.2
        (fun q => (fun p => V (Fin.addCases ts es p)) (Fin.natAdd (hm d) q)) := Iff.rfl
  rw [h0]
  have ha : (fun q => (fun p => V (Fin.addCases ts es p)) (Fin.castAdd x.2.1.1 q)) =
      fun q => V (ts q) := funext fun q => congrArg V (Fin.addCases_left q)
  have hb : (fun q => (fun p => V (Fin.addCases ts es p)) (Fin.natAdd (hm d) q)) =
      fun q => V (es q) := funext fun q => congrArg V (Fin.addCases_right q)
  rw [ha, hb]

private theorem acAt_holds {j : Fin (hs d)} {x : SubIx d} {ts : Fin (hm d) → Fin (kk d)}
    {es : Fin (x.2.1.1 + 1) → Fin (kk d)} {V : Fin (kk d) → A} :
    (acAt d j x ts es).Holds (canonAssign d A) V ↔
      canonAc d A (srank d A j fun q => V (ts q)) x fun q => V (es q) := by
  have h0 : (acAt d j x ts es).Holds (canonAssign d A) V ↔
      canonAc d A (srank d A j fun q =>
          (fun p => V (Fin.addCases (m := hm d) (n := x.2.1.1 + 1) ts es p))
            (Fin.castAdd (x.2.1.1 + 1) q)) x
        (fun q => (fun p => V (Fin.addCases (m := hm d) (n := x.2.1.1 + 1) ts es p))
          (Fin.natAdd (hm d) q)) := Iff.rfl
  rw [h0]
  have ha : (fun q => (fun p => V (Fin.addCases (m := hm d) (n := x.2.1.1 + 1) ts es p))
      (Fin.castAdd (x.2.1.1 + 1) q)) = fun q => V (ts q) :=
    funext fun q => congrArg V (Fin.addCases_left q)
  have hb : (fun q => (fun p => V (Fin.addCases (m := hm d) (n := x.2.1.1 + 1) ts es p))
      (Fin.natAdd (hm d) q)) = fun q => V (es q) :=
    funext fun q => congrArg V (Fin.addCases_right q)
  rw [ha, hb]

/-- The accumulator of `∀`, at an explicit `snoc` tuple. -/
private theorem canonAc_all_snoc {r : ℕ} {i : d.B.ι} {n : ℕ}
    {χ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1)}
    {hmem : (⟨n, χ.all⟩ : Σ n',
      ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)} {v : Fin n → A} {y : A} :
    canonAc d A r ⟨i, ⟨⟨n, χ.all⟩, hmem⟩⟩ (Fin.snoc v y) ↔
      ∀ z : A, z ≤ y → evalT d A r χ (Fin.snoc v z) := by
  have hred : canonAc d A r ⟨i, ⟨⟨n, χ.all⟩, hmem⟩⟩ (Fin.snoc v y) ↔
      ∀ z : A, z ≤ Fin.snoc (α := fun _ => A) v y (Fin.last n) →
        evalT d A r χ (Fin.snoc (fun q => Fin.snoc (α := fun _ => A) v y q.castSucc) z) :=
    Iff.rfl
  rw [hred, Fin.snoc_last]
  have h2 : (fun q : Fin n => Fin.snoc (α := fun _ => A) v y q.castSucc) = v :=
    funext fun q => by rw [Fin.snoc_castSucc]
  rw [h2]

end Canonical

/-! ### The stage walk, quantitatively

The interface the correctness inductions consume: the first stage has rank
`0`, a `stageG` step raises the rank by one, and the last stage's rank is
beyond the atom count – so the stage read off by the answer rules is the
inflationary limit. -/

section Rank

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [L.Structure A] [Finite A] [Nonempty A] in
theorem srank_bot {t : Fin (hm d) → A} (ht : ∀ (p : Fin (hm d)) (a : A), t p ≤ a) :
    srank d A (j0 d) t = 0 := by
  refine orank_eq_zero (prodLex_isBot_iff.mpr ⟨fun x => ?_, tup_isBot_iff.mpr ht⟩)
  rw [Fin.le_def]
  simp [j0]

omit [Finite A] in
theorem stageG_covBy {j j' : Fin (hs d)} {V : Fin (kk d) → A}
    (hjj : (j, j') ∈ stagePairs d) (h : (stageG d j j').Realize V) :
    toLex ((j, toLex fun q => V (vT1 d q)) : Fin (hs d) × Lex (Fin (hm d) → A)) ⋖
      toLex (j', toLex fun q => V (vT2 d q)) :=
  StageWalk.guard_covBy hjj h

omit [Finite A] in
/-- A cover of stages, as a realized stage guard. -/
private theorem stageG_realize {j j' : Fin (hs d)} {V : Fin (kk d) → A}
    (hjj : (j, j') ∈ stagePairs d)
    (hcov : toLex ((j, toLex fun q => V (vT1 d q)) :
        Fin (hs d) × Lex (Fin (hm d) → A)) ⋖
      toLex (j', toLex fun q => V (vT2 d q))) :
    (stageG d j j').Realize V :=
  StageWalk.guard_realize hjj hcov

omit [L.Structure A] [Finite A] in
/-- A cover of stages is a stage pair. -/
private theorem stagePairs_of_covBy {j j' : Fin (hs d)} {u u' : Lex (Fin (hm d) → A)}
    (hcov : toLex ((j, u) : Fin (hs d) × Lex (Fin (hm d) → A)) ⋖ toLex (j', u')) :
    (j, j') ∈ stagePairs d :=
  StageWalk.pairs_of_covBy hcov

/-- A `stageG` step raises the stage rank by one. -/
private theorem srank_stageG {j j' : Fin (hs d)} {V : Fin (kk d) → A}
    (hjj : (j, j') ∈ stagePairs d) (h : (stageG d j j').Realize V) :
    srank d A j' (fun q => V (vT2 d q)) = srank d A j (fun q => V (vT1 d q)) + 1 :=
  StageWalk.rank_guard hjj h

omit [L.Structure A] in
theorem card_le_srank_top {t : Fin (hm d) → A}
    (ht : ∀ (p : Fin (hm d)) (a : A), a ≤ t p) :
    Nat.card (BAtom d.B A) ≤ srank d A (jTop d) t := by
  have htop : ∀ u : Fin (hs d) ×ₗ Lex (Fin (hm d) → A),
      u ≤ toLex (jTop d, toLex t) := by
    refine prodLex_isTop_iff.mpr ⟨fun x => ?_, fun y => tup_isTop_iff.mpr ht y⟩
    change (x : ℕ) ≤ hc d
    exact Nat.le_of_lt_succ x.isLt
  rw [srank, StageWalk.rank, orank_isTop htop]
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

/-- The stage at the top rank is the inflationary limit. -/
theorem inflStage_srank_top {t : Fin (hm d) → A}
    (ht : ∀ (p : Fin (hm d)) (a : A), a ≤ t p) :
    d.inflStage A (srank d A (jTop d) t) = d.inflLimit A := by
  rw [d.inflLimit_eq_stage_card A]
  exact (d.inflStage_eq_of_card_le (card_le_srank_top ht)).trans
    ((d.inflStage_eq_of_card_le le_rfl).symm)

end Rank

/-! ### Soundness: the canonical assignment satisfies the rules -/

section Soundness

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {V : Fin (kk d) → A}

/-- The value of a term of the expanded vocabulary at a stage. -/
noncomputable def evTermVal (r : ℕ) {n : ℕ} (v : Fin n → A)
    (t : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) : A :=
  @Term.realize ((L.sum Language.order).sum d.B.lang) A (stageStr d A r) _
    (Sum.elim default v) t

omit [Finite A] [Nonempty A]

private theorem evalT_imp {r n : ℕ}
    {a b : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n}
    {v : Fin n → A} :
    evalT d A r (a.imp b) v ↔ (evalT d A r a v → evalT d A r b v) :=
  Iff.rfl

private theorem evalT_all {r n : ℕ}
    {a : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1)}
    {v : Fin n → A} :
    evalT d A r a.all v ↔ ∀ y : A, evalT d A r a (Fin.snoc v y) :=
  Iff.rfl

private theorem evalT_equal {r n : ℕ}
    {t u : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)}
    {v : Fin n → A} :
    evalT d A r (.equal t u) v ↔
      evTermVal (d := d) (A := A) r v t = evTermVal (d := d) (A := A) r v u :=
  Iff.rfl

private theorem evalT_rel_inl {r n l : ℕ} {rl : (L.sum Language.order).Relations l}
    {ts : Fin l → ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)}
    {v : Fin n → A} :
    evalT d A r (.rel (Sum.inl rl) ts) v ↔
      RelMap (M := A) rl fun q => evTermVal (d := d) (A := A) r v (ts q) :=
  Iff.rfl

private theorem evalT_rel_inr {r n l : ℕ} {rl : d.B.lang.Relations l}
    {ts : Fin l → ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)}
    {v : Fin n → A} :
    evalT d A r (.rel (Sum.inr rl) ts) v ↔
      d.inflStage A r rl.1 fun q => evTermVal (d := d) (A := A) r v (ts (Fin.cast rl.2 q)) :=
  Iff.rfl

/-- Truth of a step formula at a stage is one application of the step. -/
private theorem evalT_stepB {r : ℕ} {i : d.B.ι} {v : Fin (d.B.arity i + 0) → A} :
    evalT d A r (stepB d i) v ↔
      d.next (d.inflStage A r) i fun q => v (Fin.castAdd 0 q) := by
  let := stageStr d A r
  rw [evalT, stepB, BoundedFormula.realize_relabel]
  exact iff_of_eq (congrArg₂
    (fun a b => @BoundedFormula.Realize ((L.sum Language.order).sum d.B.lang) A
      (stageStr d A r) _ _ (d.step i) a b)
    (funext fun q => rfl) (Subsingleton.elim _ _))

private theorem realize_evTerm {r n : ℕ} (hn : n ≤ hX d) {V : Fin (kk d) → A}
    (t : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    (evTerm d hn t).realize V = evTermVal (d := d) (A := A) r (fun q => V (eSel d hn q)) t := by
  rw [evTerm, Term.realize_relabel]
  have hval : (V ∘ Sum.elim (fun e : Empty => e.elim) (eSel d hn)) =
      Sum.elim (default : Empty → A) fun q => V (eSel d hn q) := by
    funext z
    cases z with
    | inl e => exact e.elim
    | inr q => rfl
  rw [hval]
  let : d.B.lang.Structure A := d.B.structure (d.inflStage A r)
  exact realize_stripTerm (L₀ := L.sum Language.order) (R := d.B.lang) (A := A) _ t

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

variable [Finite A] [Nonempty A]

/-! #### The stage rules are sound -/

private theorem sCarry_sound {j j' : Fin (hs d)} (hjj : (j, j') ∈ stagePairs d) {i : d.B.ι} :
    (HornClause.mk (stageG d j j') [sAt d j i (vT1 d) (xa d i)]
      (some (sAt d j' i (vT2 d) (xa d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, hb⟩
  have hstep := srank_stageG hjj hg
  have hS := sAt_holds.mp (hb _ (List.mem_cons_self ..))
  refine sAt_holds.mpr ?_
  rw [hstep]
  exact d.inflStage_le_succ _ i _ hS

private theorem sDerive_sound {j j' : Fin (hs d)} (hjj : (j, j') ∈ stagePairs d) {i : d.B.ι} :
    (HornClause.mk (stageG d j j')
      [tfAt d j (rootSub d i) true (vT1 d) (rootSel d i)]
      (some (sAt d j' i (vT2 d) (rootSel d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, hb⟩
  have hstep := srank_stageG hjj hg
  have hT := tAt_holds.mp (hb _ (List.mem_cons_self ..))
  have hnext := evalT_stepB.mp hT
  refine sAt_holds.mpr ?_
  rw [hstep, d.inflStage_succ]
  exact Or.inr hnext

omit [Finite A] [Nonempty A] in
theorem nBase_sound {i : d.B.ι} :
    (HornClause.mk (minTupF (L := L) (vT1 d)) []
      (some (nAt d (j0 d) i (vT1 d) (xa d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, -⟩
  refine nAt_holds.mpr ?_
  rw [srank_bot ((realize_minTupF (L := L) _).mp hg)]
  intro hder
  exact hder

private theorem nStep_sound {j j' : Fin (hs d)} (hjj : (j, j') ∈ stagePairs d) {i : d.B.ι} :
    (HornClause.mk (stageG d j j')
      [nAt d j i (vT1 d) (rootSel d i),
        tfAt d j (rootSub d i) false (vT1 d) (rootSel d i)]
      (some (nAt d j' i (vT2 d) (rootSel d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, hb⟩
  have hstep := srank_stageG hjj hg
  have hN := nAt_holds.mp (hb _ (List.mem_cons_self ..))
  have hF := fAt_holds.mp (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine nAt_holds.mpr ?_
  rw [hstep, d.inflStage_succ]
  rintro (hprev | hnext)
  · exact hN hprev
  · exact hF (evalT_stepB.mpr hnext)

private theorem rRules_sound {i : d.B.ι} :
    (HornClause.mk (maxTupF (L := L) (vT1 d)) [sAt d (jTop d) i (vT1 d) (xa d i)]
      (some (rAt d i (xa d i)))).Holds (canonAssign d A) V := by
  rintro ⟨hg, hb⟩
  have hS := sAt_holds.mp (hb _ (List.mem_cons_self ..))
  refine rAt_holds.mpr ?_
  rw [inflStage_srank_top ((realize_maxTupF (L := L) _).mp hg)] at hS
  exact hS

/-! #### The evaluator is sound -/

omit [Finite A] [Nonempty A] in
theorem evalClauses_sound {j : Fin (hs d)} {x : SubIx d}
    {c : HornClause (L.sum Language.order) (trBlock d) (kk d)}
    (hc : c ∈ evalClauses d j x) : c.Holds (canonAssign d A) V := by
  obtain ⟨i, ⟨⟨n, ψ⟩, hmem⟩⟩ := x
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
      rw [Formula.realize_equal, realize_evTerm (r := srank d A j fun q => V (vT1 d q)),
        realize_evTerm (r := srank d A j fun q => V (vT1 d q))] at hg
      exact tAt_holds.mpr (evalT_equal.mpr hg)
    · rintro ⟨hg, -⟩
      rw [Formula.realize_not, Formula.realize_equal,
        realize_evTerm (r := srank d A j fun q => V (vT1 d q)),
        realize_evTerm (r := srank d A j fun q => V (vT1 d q))] at hg
      exact fAt_holds.mpr fun h => hg (evalT_equal.mp h)
  | rel R ts =>
    rcases R with r | r
    · simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rintro ⟨hg, -⟩
        rw [Formula.realize_rel] at hg
        have hts : (fun q =>
            (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩)
              (ts q)).realize V) =
            fun q => evTermVal (d := d) (A := A) (srank d A j fun p => V (vT1 d p))
              (fun p => V (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩,
                hmem⟩⟩) p)) (ts q) :=
          funext fun q => realize_evTerm _ _
        rw [hts] at hg
        exact tAt_holds.mpr (evalT_rel_inl.mpr hg)
      · rintro ⟨hg, -⟩
        rw [Formula.realize_not, Formula.realize_rel] at hg
        have hts : (fun q =>
            (evTerm d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩)
              (ts q)).realize V) =
            fun q => evTermVal (d := d) (A := A) (srank d A j fun p => V (vT1 d p))
              (fun p => V (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩,
                hmem⟩⟩) p)) (ts q) :=
          funext fun q => realize_evTerm _ _
        rw [hts] at hg
        exact fAt_holds.mpr fun h => hg (evalT_rel_inl.mp h)
    · simp only [evalClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rintro ⟨hg, hb⟩
        have hS := sAt_holds.mp (hb _ (List.mem_cons_self ..))
        refine tAt_holds.mpr (evalT_rel_inr.mpr ?_)
        have htup : (fun q => V (xa d r.1 q)) =
            fun q => evTermVal (d := d) (A := A) (srank d A j fun p => V (vT1 d p))
              (fun p => V (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩,
                hmem⟩⟩) p)) (ts (Fin.cast r.2 q)) := by
          funext q
          have h := (realize_listInf _).mp hg _
            (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
          rw [Formula.realize_equal, Term.realize_var,
            realize_evTerm (r := srank d A j fun p => V (vT1 d p))] at h
          exact h
        rw [← htup]
        exact hS
      · rintro ⟨hg, hb⟩
        have hN := nAt_holds.mp (hb _ (List.mem_cons_self ..))
        refine fAt_holds.mpr fun h => ?_
        have h2 := evalT_rel_inr.mp h
        have htup : (fun q => V (xa d r.1 q)) =
            fun q => evTermVal (d := d) (A := A) (srank d A j fun p => V (vT1 d p))
              (fun p => V (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩,
                hmem⟩⟩) p)) (ts (Fin.cast r.2 q)) := by
          funext q
          have h' := (realize_listInf _).mp hg _
            (List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩)
          rw [Formula.realize_equal, Term.realize_var,
            realize_evTerm (r := srank d A j fun p => V (vT1 d p))] at h'
          exact h'
        rw [← htup] at h2
        exact hN h2
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
    have hn1 : n + 1 ≤ hX d :=
      subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩, subs_trans hmem (mem_subs_all a)⟩⟩
    rcases hc with rfl | rfl | rfl | rfl
    · -- accumulator base
      rintro ⟨hg, hb⟩
      have hTa := tAt_holds.mp (hb _ (List.mem_cons_self ..))
      change (acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
        (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
          subs_trans hmem (mem_subs_all a)⟩⟩))).Holds (canonAssign d A) V
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
      rw [LFPHorn.comp_snoc_lambda] at hAcc
      have hprev := canonAc_all_snoc.mp hAcc
      change (acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
        (eSel d (subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩,
          subs_trans hmem (mem_subs_all a)⟩⟩))).Holds (canonAssign d A) V
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
      exact tAt_holds.mpr (evalT_all.mpr fun y =>
        hAcc' y ((realize_maxF (L := L) _).mp hg y))
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
        · rcases List.mem_append.mp hc with hc | hc
          · obtain ⟨⟨j, j'⟩, hjj, hmm⟩ := List.mem_flatMap.mp hc
            obtain ⟨i, -, rfl⟩ := List.mem_map.mp hmm
            exact sCarry_sound hjj
          · obtain ⟨⟨j, j'⟩, hjj, hmm⟩ := List.mem_flatMap.mp hc
            obtain ⟨i, -, rfl⟩ := List.mem_map.mp hmm
            exact sDerive_sound hjj
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
          exact nBase_sound
      · obtain ⟨⟨j, j'⟩, hjj, hmm⟩ := List.mem_flatMap.mp hc
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hmm
        exact nStep_sound hjj
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
      exact rRules_sound
  · obtain ⟨j, -, hmm⟩ := List.mem_flatMap.mp hc
    obtain ⟨i, -, hmm2⟩ := List.mem_flatMap.mp hmm
    obtain ⟨x, -, hcin⟩ := List.mem_flatMap.mp hmm2
    exact evalClauses_sound hcin

end Soundness

/-! ### Completeness: every canonical fact is derivable -/

section Completeness

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Assembling a valuation of the shared variables from its blocks. -/
noncomputable def packV (t1 t2 x : Fin (hm d) → A) (e : Fin (hX d) → A) (sp : A) :
    Fin (kk d) → A := fun q =>
  if h1 : (q : ℕ) < hm d then t1 ⟨q, h1⟩
  else if h2 : (q : ℕ) < 2 * hm d then t2 ⟨(q : ℕ) - hm d, by omega⟩
  else if h3 : (q : ℕ) < 3 * hm d then x ⟨(q : ℕ) - 2 * hm d, by omega⟩
  else if h4 : (q : ℕ) < 3 * hm d + hX d then e ⟨(q : ℕ) - 3 * hm d, by omega⟩
  else sp

variable {t1 t2 x : Fin (hm d) → A} {e : Fin (hX d) → A} {sp : A}

section PackProj

omit [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

private theorem packV_comp_vT1 : (fun q => packV t1 t2 x e sp (vT1 d q)) = t1 := by
  funext q
  have hq := q.isLt
  have hv : ((vT1 d q : Fin (kk d)) : ℕ) = (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_left (by rw [hv]; omega)]
  exact congrArg t1 (Fin.ext (show ((vT1 d q : Fin (kk d)) : ℕ) = (q : ℕ) from hv))

private theorem packV_comp_vT2 : (fun q => packV t1 t2 x e sp (vT2 d q)) = t2 := by
  funext q
  have hq := q.isLt
  have hv : ((vT2 d q : Fin (kk d)) : ℕ) = hm d + (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_left (by rw [hv]; omega)]
  exact congrArg t2 (Fin.ext
    (show ((vT2 d q : Fin (kk d)) : ℕ) - hm d = (q : ℕ) from by rw [hv]; omega))

private theorem packV_comp_eSel {n : ℕ} (hn : n ≤ hX d) {v : Fin n → A}
    (hpad : ∀ q : Fin n, e ⟨q, lt_of_lt_of_le q.isLt hn⟩ = v q) :
    (fun q => packV t1 t2 x e sp (eSel d hn q)) = v := by
  funext q
  have hq := q.isLt
  have hv : ((eSel d hn q : Fin (kk d)) : ℕ) = 3 * hm d + (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega),
    dite_eq_left (by rw [hv]; have := lt_of_lt_of_le hq hn; omega)]
  rw [← hpad q]
  exact congrArg e (Fin.ext
    (show ((eSel d hn q : Fin (kk d)) : ℕ) - 3 * hm d = (q : ℕ) from by rw [hv]; omega))

private theorem packV_vS : packV t1 t2 x e sp (vS d) = sp := by
  have hv : ((vS d : Fin (kk d)) : ℕ) = 3 * hm d + hX d := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega)]

private theorem packV_comp_xa {i : d.B.ι}
    {xt : Fin (d.B.arity i) → A}
    (hpad : ∀ q : Fin (d.B.arity i),
      x ⟨q, lt_of_lt_of_le q.isLt (arity_le_blockArityBound d.B i)⟩ = xt q) :
    (fun q => packV t1 t2 x e sp (xa d i q)) = xt := by
  funext q
  have hq := lt_of_lt_of_le q.isLt (arity_le_blockArityBound d.B i)
  have hv : ((xa d i q : Fin (kk d)) : ℕ) = 2 * hm d + (q : ℕ) := rfl
  simp only [packV]
  rw [dite_eq_right (by rw [hv]; omega), dite_eq_right (by rw [hv]; omega),
    dite_eq_left (by rw [hv]; simp only [hm] at hq ⊢; omega)]
  rw [← hpad q]
  exact congrArg x (Fin.ext
    (show ((xa d i q : Fin (kk d)) : ℕ) - 2 * hm d = (q : ℕ) from by rw [hv]; omega))

end PackProj

omit [L.Structure A] [LinearOrder A] [Finite A] in
/-- Extending a tuple to a wider block, junk-padded. -/
noncomputable def padF {m M : ℕ} (f : Fin m → A) : Fin M → A :=
  fun p => if h : (p : ℕ) < m then f ⟨p, h⟩ else Classical.arbitrary A

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem packV_comp_eSel_pad {n : ℕ} (hn : n ≤ hX d) {v : Fin n → A} :
    (fun q => packV t1 t2 x (padF v) sp (eSel d hn q)) = v :=
  packV_comp_eSel hn fun q => by
    rw [padF, dite_eq_left (show ((⟨q, lt_of_lt_of_le q.isLt hn⟩ : Fin (hX d)) : ℕ) < n
      from q.isLt)]

omit [L.Structure A] [LinearOrder A] [Finite A] in
theorem packV_comp_xa_pad {i : d.B.ι} {xt : Fin (d.B.arity i) → A} :
    (fun q => packV t1 t2 (padF xt) e sp (xa d i q)) = xt :=
  packV_comp_xa fun q => by
    rw [padF, dite_eq_left (show ((⟨q, lt_of_lt_of_le q.isLt
      (arity_le_blockArityBound d.B i)⟩ : Fin (hm d)) : ℕ) < d.B.arity i from q.isLt)]

/-! #### Membership of the rules in the program -/

private theorem mem_trRules_sCarry {c} (h : c ∈ sCarry d) : c ∈ trRules d := by
  rw [trRules]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ h))))

private theorem mem_trRules_sDerive {c} (h : c ∈ sDerive d) : c ∈ trRules d := by
  rw [trRules]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ h))))

private theorem mem_trRules_nBase {c} (h : c ∈ nBase d) : c ∈ trRules d := by
  rw [trRules]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ h)))

private theorem mem_trRules_nStep {c} (h : c ∈ nStep d) : c ∈ trRules d := by
  rw [trRules]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

private theorem mem_trRules_rRules {c} (h : c ∈ rRules d) : c ∈ trRules d := by
  rw [trRules]
  exact List.mem_append_left _ (List.mem_append_right _ h)

private theorem mem_trRules_evalClauses {j : Fin (hs d)} {x : SubIx d} {c}
    (h : c ∈ evalClauses d j x) : c ∈ trRules d := by
  rw [trRules]
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, ?_⟩)
  refine List.mem_flatMap.mpr ⟨x.1, d.B.mem_idxList x.1, ?_⟩
  refine List.mem_flatMap.mpr ⟨⟨x.2.1, x.2.2⟩, List.mem_attach _ _, ?_⟩
  exact h

/-! #### The subformula relations are derivable -/


omit [Finite A] in
private theorem derives_tf_falsum {j : Fin (hs d)} {t : Fin (hm d) → A} {n : ℕ} :
    ∀ {i : d.B.ι}
      (hmem : (⟨n, .falsum⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) .falsum v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) .falsum v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩) := by
  intro i hmem v
  constructor
  · intro h
    exact False.elim h
  · intro _
    have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d))) []
        (some (tfAt d j ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩ false (vT1 d)
          (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩))))) ∈ trRules d :=
      mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩)
        (List.mem_singleton.mpr rfl)
    set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hgT : Formula.Realize (L := L.sum Language.order)
        (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
      Formula.realize_top.mpr trivial
    have key := Derives.rule (rules := trRules d) hcmem
      (a := tfAt d j ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩ false (vT1 d)
        (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩))) rfl
      hgT (fun b hb => absurd hb (by simp))
    refine LFPHorn.derives_congr_tuple ?_ key
    change (fun q => V (Fin.addCases (vT1 d)
      (eSel d (subIx_le_hX d ⟨i, ⟨⟨n, .falsum⟩, hmem⟩⟩)) q)) = _
    rw [LFPHorn.comp_addCases, hV, packV_comp_vT1, packV_comp_eSel_pad]

omit [Finite A] in
private theorem derives_tf_equal {j : Fin (hs d)} {t : Fin (hm d) → A} {n : ℕ}
    (t' u : ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    ∀ {i : d.B.ι}
      (hmem : (⟨n, (.equal t' u)⟩ :
        Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) (.equal t' u) v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, (.equal t' u)⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) (.equal t' u) v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, (.equal t' u)⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩) := by
  intro i hmem v
  have hle := subIx_le_hX d ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩
  have hE0 : ∀ (V : Fin (kk d) → A), (fun q => V (eSel d hle q)) = v →
      ∀ tm, (evTerm d hle tm).realize V =
        evTermVal (d := d) (A := A) (srank d A j t) v tm := by
    intro V hE tm
    rw [realize_evTerm (r := srank d A j t), hE]
  constructor
  · intro h
    have hcmem : (HornClause.mk
        (Term.equal (evTerm d hle t') (evTerm d hle u)) []
        (some (tfAt d j ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩ true (vT1 d)
          (eSel d hle)))) ∈ trRules d :=
      mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩)
        (List.mem_cons_self ..)
    set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d hle q)) = v := by
      rw [hV, packV_comp_eSel_pad]
    have hg : (Term.equal (evTerm d hle t') (evTerm d hle u)).Realize V := by
      rw [Formula.realize_equal, hE0 V hE, hE0 V hE]
      exact h
    have key := Derives.rule (rules := trRules d) hcmem
      (a := tfAt d j ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩ true (vT1 d) (eSel d hle)) rfl hg
      (fun b hb => absurd hb (by simp))
    refine LFPHorn.derives_congr_tuple ?_ key
    change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
    rw [LFPHorn.comp_addCases, hV, packV_comp_vT1, packV_comp_eSel_pad]
  · intro h
    have hcmem : (HornClause.mk
        (∼(Term.equal (evTerm d hle t') (evTerm d hle u))) []
        (some (tfAt d j ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩ false (vT1 d)
          (eSel d hle)))) ∈ trRules d :=
      mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A) (padF v)
      (Classical.arbitrary A) with hV
    have hE : (fun q => V (eSel d hle q)) = v := by
      rw [hV, packV_comp_eSel_pad]
    have hg : Formula.Realize (L := L.sum Language.order)
        (∼(Term.equal (evTerm d hle t') (evTerm d hle u))) V := by
      rw [Formula.realize_not, Formula.realize_equal, hE0 V hE, hE0 V hE]
      exact h
    have key := Derives.rule (rules := trRules d) hcmem
      (a := tfAt d j ⟨i, ⟨⟨n, .equal t' u⟩, hmem⟩⟩ false (vT1 d) (eSel d hle)) rfl hg
      (fun b hb => absurd hb (by simp))
    refine LFPHorn.derives_congr_tuple ?_ key
    change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
    rw [LFPHorn.comp_addCases, hV, packV_comp_vT1, packV_comp_eSel_pad]

omit [Finite A] in
private theorem derives_tf_rel {j : Fin (hs d)} {t : Fin (hm d) → A} {n l : ℕ}
    (hS : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      d.inflStage A (srank d A j t) i xt →
      Derives (trRules d) ⟨sIx d j i, Fin.addCases t xt⟩)
    (hN : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      ¬d.inflStage A (srank d A j t) i xt →
      Derives (trRules d) ⟨nIx d j i, Fin.addCases t xt⟩)
    (R : ((L.sum Language.order).sum d.B.lang).Relations l)
    (ts : Fin l → ((L.sum Language.order).sum d.B.lang).Term (Empty ⊕ Fin n)) :
    ∀ {i : d.B.ι}
      (hmem : (⟨n, (.rel R ts)⟩ :
        Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) (.rel R ts) v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, (.rel R ts)⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) (.rel R ts) v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, (.rel R ts)⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩) := by
  intro i hmem v
  rcases R with r | r
  · have hle := subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩
    have hE0 : ∀ (V : Fin (kk d) → A), (fun q => V (eSel d hle q)) = v →
        (fun l => (evTerm d hle (ts l)).realize V) =
          fun l => evTermVal (d := d) (A := A) (srank d A j t) v (ts l) := by
      intro V hE
      funext l
      rw [realize_evTerm (r := srank d A j t), hE]
    constructor
    · intro h
      have hcmem : (HornClause.mk
          (Relations.formula r fun l => evTerm d hle (ts l)) []
          (some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ true (vT1 d)
            (eSel d hle)))) ∈ trRules d :=
        mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩)
          (List.mem_cons_self ..)
      set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d hle q)) = v := by
        rw [hV, packV_comp_eSel_pad]
      have hg : (Relations.formula r fun l => evTerm d hle (ts l)).Realize V := by
        rw [Formula.realize_rel, hE0 V hE]
        exact evalT_rel_inl.mp h
      have key := Derives.rule (rules := trRules d) hcmem
        (a := tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ true (vT1 d)
          (eSel d hle)) rfl hg (fun b hb => absurd hb (by simp))
      refine LFPHorn.derives_congr_tuple ?_ key
      change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
      rw [LFPHorn.comp_addCases, hV, packV_comp_vT1, packV_comp_eSel_pad]
    · intro h
      have hcmem : (HornClause.mk
          (∼(Relations.formula r fun l => evTerm d hle (ts l))) []
          (some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ false (vT1 d)
            (eSel d hle)))) ∈ trRules d :=
        mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩)
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d hle q)) = v := by
        rw [hV, packV_comp_eSel_pad]
      have hg : Formula.Realize (L := L.sum Language.order)
          (∼(Relations.formula r fun l => evTerm d hle (ts l))) V := by
        rw [Formula.realize_not, Formula.realize_rel, hE0 V hE]
        exact fun h2 => h (evalT_rel_inl.mpr h2)
      have key := Derives.rule (rules := trRules d) hcmem
        (a := tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inl r) ts⟩, hmem⟩⟩ false (vT1 d)
          (eSel d hle)) rfl hg (fun b hb => absurd hb (by simp))
      refine LFPHorn.derives_congr_tuple ?_ key
      change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
      rw [LFPHorn.comp_addCases, hV, packV_comp_vT1, packV_comp_eSel_pad]
  · -- a block atom: read the stage or its complement
    have hle := subIx_le_hX d ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩
    set xt : Fin (d.B.arity r.1) → A :=
      fun q => evTermVal (d := d) (A := A) (srank d A j t) v (ts (Fin.cast r.2 q))
      with hxt
    have hguard : ∀ (V : Fin (kk d) → A), (fun q => V (eSel d hle q)) = v →
        (fun q => V (xa d r.1 q)) = xt →
        (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
          Term.equal (Term.var (xa d r.1 q))
            (evTerm d hle (ts (Fin.cast r.2 q))))).Realize V := by
      intro V hE hXa
      rw [realize_listInf]
      intro φ hφ
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hφ
      rw [Formula.realize_equal, Term.realize_var,
        realize_evTerm (r := srank d A j t), hE]
      exact congrFun hXa q
    constructor
    · intro h
      have hcmem : (HornClause.mk
          (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
            Term.equal (Term.var (xa d r.1 q))
              (evTerm d hle (ts (Fin.cast r.2 q)))))
          [sAt d j r.1 (vT1 d) (xa d r.1)]
          (some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ true (vT1 d)
            (eSel d hle)))) ∈ trRules d :=
        mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩)
          (List.mem_cons_self ..)
      set V : Fin (kk d) → A := packV t t (padF xt) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d hle q)) = v := by
        rw [hV, packV_comp_eSel_pad]
      have hXa : (fun q => V (xa d r.1 q)) = xt := by
        rw [hV, packV_comp_xa_pad]
      have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
      have hb : ∀ b ∈ [sAt d j r.1 (vT1 d) (xa d r.1)],
          Derives (trRules d) ⟨b.idx, fun q => V (b.args q)⟩ := by
        intro b hb
        rw [List.mem_singleton] at hb
        subst hb
        have hkey := hS r.1 xt (evalT_rel_inr.mp h)
        refine LFPHorn.derives_congr_tuple ?_ hkey
        change _ = fun q => V (Fin.addCases (vT1 d) (xa d r.1) q)
        rw [LFPHorn.comp_addCases, hT1, hXa]
      have key := Derives.rule (rules := trRules d) hcmem
        (a := tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ true (vT1 d)
          (eSel d hle)) rfl (hguard V hE hXa) hb
      refine LFPHorn.derives_congr_tuple ?_ key
      change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
      rw [LFPHorn.comp_addCases, hT1, hE]
    · intro h
      have hcmem : (HornClause.mk
          (listInf ((List.finRange (d.B.arity r.1)).map fun q =>
            Term.equal (Term.var (xa d r.1 q))
              (evTerm d hle (ts (Fin.cast r.2 q)))))
          [nAt d j r.1 (vT1 d) (xa d r.1)]
          (some (tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ false (vT1 d)
            (eSel d hle)))) ∈ trRules d :=
        mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩)
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      set V : Fin (kk d) → A := packV t t (padF xt) (padF v)
        (Classical.arbitrary A) with hV
      have hE : (fun q => V (eSel d hle q)) = v := by
        rw [hV, packV_comp_eSel_pad]
      have hXa : (fun q => V (xa d r.1 q)) = xt := by
        rw [hV, packV_comp_xa_pad]
      have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
      have hb : ∀ b ∈ [nAt d j r.1 (vT1 d) (xa d r.1)],
          Derives (trRules d) ⟨b.idx, fun q => V (b.args q)⟩ := by
        intro b hb
        rw [List.mem_singleton] at hb
        subst hb
        have hkey := hN r.1 xt fun h2 => h (evalT_rel_inr.mpr h2)
        refine LFPHorn.derives_congr_tuple ?_ hkey
        change _ = fun q => V (Fin.addCases (vT1 d) (xa d r.1) q)
        rw [LFPHorn.comp_addCases, hT1, hXa]
      have key := Derives.rule (rules := trRules d) hcmem
        (a := tfAt d j ⟨i, ⟨⟨n, .rel (Sum.inr r) ts⟩, hmem⟩⟩ false (vT1 d)
          (eSel d hle)) rfl (hguard V hE hXa) hb
      refine LFPHorn.derives_congr_tuple ?_ key
      change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
      rw [LFPHorn.comp_addCases, hT1, hE]

omit [Finite A] in
private theorem derives_tf_imp {j : Fin (hs d)} {t : Fin (hm d) → A} {n : ℕ}
    (a b : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n)
    (iha : ∀ {i : d.B.ι}
      (hmem : (⟨n, a⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) a v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, a⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) a v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, a⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩))
    (ihb : ∀ {i : d.B.ι}
      (hmem : (⟨n, b⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) b v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, b⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) b v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, b⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩)) :
    ∀ {i : d.B.ι}
      (hmem : (⟨n, (a.imp b)⟩ :
        Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) (a.imp b) v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, (a.imp b)⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) (a.imp b) v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, (a.imp b)⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩) := by
  intro i hmem v
  have hla := subs_trans hmem (left_mem_subs_imp a b)
  have hrb := subs_trans hmem (right_mem_subs_imp a b)
  have hle := subIx_le_hX d ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩
  set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A) (padF v)
    (Classical.arbitrary A) with hV
  have hE : (fun q => V (eSel d hle q)) = v := by
    rw [hV, packV_comp_eSel_pad]
  have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
  have hgT : Formula.Realize (L := L.sum Language.order)
      (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
    Formula.realize_top.mpr trivial
  have hhead : (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) =
      Fin.addCases t v := by
    rw [LFPHorn.comp_addCases, hT1, hE]
  have hbody : (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) =
      Fin.addCases t v := hhead
  constructor
  · intro h
    by_cases hA : evalT d A (srank d A j t) a v
    · have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
          [tfAt d j ⟨i, ⟨⟨n, b⟩, hrb⟩⟩ true (vT1 d) (eSel d hle)]
          (some (tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ true (vT1 d)
            (eSel d hle)))) ∈ trRules d :=
        mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩)
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hb : ∀ b' ∈ [tfAt d j ⟨i, ⟨⟨n, b⟩, hrb⟩⟩ true (vT1 d) (eSel d hle)],
          Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
        intro b' hb'
        rw [List.mem_singleton] at hb'
        subst hb'
        exact LFPHorn.derives_congr_tuple hbody.symm ((ihb hrb v).1 (h hA))
      have key := Derives.rule (rules := trRules d) hcmem
        (a := tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ true (vT1 d) (eSel d hle)) rfl
        hgT hb
      exact LFPHorn.derives_congr_tuple hhead key
    · have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
          [tfAt d j ⟨i, ⟨⟨n, a⟩, hla⟩⟩ false (vT1 d) (eSel d hle)]
          (some (tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ true (vT1 d)
            (eSel d hle)))) ∈ trRules d :=
        mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩)
          (List.mem_cons_self ..)
      have hb : ∀ b' ∈ [tfAt d j ⟨i, ⟨⟨n, a⟩, hla⟩⟩ false (vT1 d) (eSel d hle)],
          Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
        intro b' hb'
        rw [List.mem_singleton] at hb'
        subst hb'
        exact LFPHorn.derives_congr_tuple hbody.symm ((iha hla v).2 hA)
      have key := Derives.rule (rules := trRules d) hcmem
        (a := tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ true (vT1 d) (eSel d hle)) rfl
        hgT hb
      exact LFPHorn.derives_congr_tuple hhead key
  · intro h
    have h2 : evalT d A (srank d A j t) a v ∧
        ¬evalT d A (srank d A j t) b v := by
      rw [evalT_imp] at h
      push Not at h
      exact h
    have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
        [tfAt d j ⟨i, ⟨⟨n, a⟩, hla⟩⟩ true (vT1 d) (eSel d hle),
          tfAt d j ⟨i, ⟨⟨n, b⟩, hrb⟩⟩ false (vT1 d) (eSel d hle)]
        (some (tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ false (vT1 d)
          (eSel d hle)))) ∈ trRules d :=
      mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hb : ∀ b' ∈ [tfAt d j ⟨i, ⟨⟨n, a⟩, hla⟩⟩ true (vT1 d) (eSel d hle),
        tfAt d j ⟨i, ⟨⟨n, b⟩, hrb⟩⟩ false (vT1 d) (eSel d hle)],
        Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
      intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact LFPHorn.derives_congr_tuple hbody.symm ((iha hla v).1 h2.1)
      · rw [List.mem_singleton] at hb''
        subst hb''
        exact LFPHorn.derives_congr_tuple hbody.symm ((ihb hrb v).2 h2.2)
    have key := Derives.rule (rules := trRules d) hcmem
      (a := tfAt d j ⟨i, ⟨⟨n, a.imp b⟩, hmem⟩⟩ false (vT1 d) (eSel d hle)) rfl
      hgT hb
    exact LFPHorn.derives_congr_tuple hhead key

private theorem derives_tf_all {j : Fin (hs d)} {t : Fin (hm d) → A} {n : ℕ}
    (a : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty (n + 1))
    (ih : ∀ {i : d.B.ι}
      (hmem : (⟨n + 1, a⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n + 1) → A),
      (evalT d A (srank d A j t) a v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n + 1, a⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) a v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n + 1, a⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩)) :
    ∀ {i : d.B.ι}
      (hmem : (⟨n, a.all⟩ : Σ n', ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
        subs (stepB d i)) (v : Fin (n) → A),
      (evalT d A (srank d A j t) a.all v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ true,
          Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) a.all v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ false,
          Fin.addCases t v⟩) := by
  intro i hmem v
  have hsub := subs_trans hmem (mem_subs_all a)
  have hle := subIx_le_hX d ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩
  have hn1 : n + 1 ≤ hX d := subIx_le_hX d ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩
  constructor
  · intro h
    have hAcc : ∀ z : A, Derives (trRules d)
        ⟨acIx d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩,
          Fin.addCases (m := hm d) (n := n + 1) t (Fin.snoc v z)⟩ := by
      refine order_induction (A := A) ?_ ?_
      · intro z hz
        have hcmem : (HornClause.mk (minF (eSel d hn1 (Fin.last n)))
            [tfAt d j ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩ true (vT1 d) (eSel d hn1)]
            (some (acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d) (eSel d hn1)))) ∈
            trRules d :=
          mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩)
            (List.mem_cons_self ..)
        set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A)
          (padF (Fin.snoc v z)) (Classical.arbitrary A) with hV
        have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v z := by
          rw [hV, packV_comp_eSel_pad]
        have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
        have hg : (minF (L := L) (eSel d hn1 (Fin.last n))).Realize V := by
          refine (realize_minF (L := L) _).mpr fun a' => ?_
          rw [congrFun hE1 (Fin.last n), Fin.snoc_last]
          exact hz a'
        have hb : ∀ b' ∈ [tfAt d j ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩ true (vT1 d)
            (eSel d hn1)],
            Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
          intro b' hb'
          rw [List.mem_singleton] at hb'
          subst hb'
          refine LFPHorn.derives_congr_tuple ?_ ((ih hsub (Fin.snoc v z)).1 (h z))
          change _ = fun q => V (Fin.addCases (vT1 d) (eSel d hn1) q)
          rw [LFPHorn.comp_addCases, hT1, hE1]
        have key := Derives.rule (rules := trRules d) hcmem
          (a := acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d) (eSel d hn1)) rfl hg hb
        refine LFPHorn.derives_congr_tuple ?_ key
        change (fun q => V (Fin.addCases (vT1 d) (eSel d hn1) q)) = _
        rw [LFPHorn.comp_addCases, hT1, hE1]
      · intro w z hwz hnb ihz
        have hcmem : (HornClause.mk (succF (vS d) (eSel d hn1 (Fin.last n)))
            [acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
                (Fin.snoc (eSel d hle) (vS d)),
              tfAt d j ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩ true (vT1 d) (eSel d hn1)]
            (some (acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d) (eSel d hn1)))) ∈
            trRules d :=
          mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩)
            (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A)
          (padF (Fin.snoc v z)) w with hV
        have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v z := by
          rw [hV, packV_comp_eSel_pad]
        have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
        have hEn : (fun q => V (eSel d hle q)) = v := by
          have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
          exact (Fin.snoc_inj.mp hsplit).1
        have hlast : V (eSel d hn1 (Fin.last n)) = z := by
          have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
          exact (Fin.snoc_inj.mp hsplit).2
        have hvs : V (vS d) = w := by rw [hV, packV_vS]
        have hg : (succF (L := L) (vS d) (eSel d hn1 (Fin.last n))).Realize V := by
          rw [realize_succF, hvs, hlast]
          exact ⟨hwz, hnb⟩
        have hb : ∀ b' ∈ [acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d)
            (Fin.snoc (eSel d hle) (vS d)),
            tfAt d j ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩ true (vT1 d) (eSel d hn1)],
            Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
          intro b' hb'
          rcases List.mem_cons.mp hb' with rfl | hb''
          · refine LFPHorn.derives_congr_tuple ?_ ihz
            change _ = fun q => V (Fin.addCases (vT1 d)
              (Fin.snoc (α := fun _ => Fin (kk d)) (eSel d hle) (vS d)) q)
            rw [LFPHorn.comp_addCases, LFPHorn.comp_snoc_lambda, hT1, hEn, hvs]
          · rw [List.mem_singleton] at hb''
            subst hb''
            refine LFPHorn.derives_congr_tuple ?_
              ((ih hsub (Fin.snoc v z)).1 (h z))
            change _ = fun q => V (Fin.addCases (vT1 d) (eSel d hn1) q)
            rw [LFPHorn.comp_addCases, hT1, hE1]
        have key := Derives.rule (rules := trRules d) hcmem
          (a := acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d) (eSel d hn1)) rfl hg hb
        refine LFPHorn.derives_congr_tuple ?_ key
        change (fun q => V (Fin.addCases (vT1 d) (eSel d hn1) q)) = _
        rw [LFPHorn.comp_addCases, hT1, hE1]
    obtain ⟨mA, hmA⟩ := Finite.exists_max (fun a : A => a)
    have hcmem : (HornClause.mk (maxF (eSel d hn1 (Fin.last n)))
        [acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d) (eSel d hn1)]
        (some (tfAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ true (vT1 d)
          (eSel d hle)))) ∈ trRules d :=
      mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A)
      (padF (Fin.snoc v mA)) (Classical.arbitrary A) with hV
    have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v mA := by
      rw [hV, packV_comp_eSel_pad]
    have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
    have hEn : (fun q => V (eSel d hle q)) = v := by
      have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
      exact (Fin.snoc_inj.mp hsplit).1
    have hlast : V (eSel d hn1 (Fin.last n)) = mA := by
      have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
      exact (Fin.snoc_inj.mp hsplit).2
    have hg : (maxF (L := L) (eSel d hn1 (Fin.last n))).Realize V := by
      refine (realize_maxF (L := L) _).mpr fun a' => ?_
      rw [hlast]
      exact hmA a'
    have hb : ∀ b' ∈ [acAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ (vT1 d) (eSel d hn1)],
        Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
      intro b' hb'
      rw [List.mem_singleton] at hb'
      subst hb'
      refine LFPHorn.derives_congr_tuple ?_ (hAcc mA)
      change _ = fun q => V (Fin.addCases (vT1 d) (eSel d hn1) q)
      rw [LFPHorn.comp_addCases, hT1, hE1]
    have key := Derives.rule (rules := trRules d) hcmem
      (a := tfAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ true (vT1 d) (eSel d hle)) rfl hg hb
    refine LFPHorn.derives_congr_tuple ?_ key
    change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
    rw [LFPHorn.comp_addCases, hT1, hEn]
  · intro h
    have h2 : ∃ y : A, ¬evalT d A (srank d A j t) a (Fin.snoc v y) := by
      rw [evalT_all] at h
      push Not at h
      exact h
    obtain ⟨y₀, hy₀⟩ := h2
    have hcmem : (HornClause.mk (⊤ : (L.sum Language.order).Formula (Fin (kk d)))
        [tfAt d j ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩ false (vT1 d) (eSel d hn1)]
        (some (tfAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ false (vT1 d)
          (eSel d hle)))) ∈ trRules d :=
      mem_trRules_evalClauses (x := ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    set V : Fin (kk d) → A := packV t t (fun _ => Classical.arbitrary A)
      (padF (Fin.snoc v y₀)) (Classical.arbitrary A) with hV
    have hE1 : (fun q => V (eSel d hn1 q)) = Fin.snoc v y₀ := by
      rw [hV, packV_comp_eSel_pad]
    have hT1 : (fun q => V (vT1 d q)) = t := by rw [hV, packV_comp_vT1]
    have hEn : (fun q => V (eSel d hle q)) = v := by
      have hsplit := (eSel_snoc hn1 (V := V)).symm.trans hE1
      exact (Fin.snoc_inj.mp hsplit).1
    have hgT : Formula.Realize (L := L.sum Language.order)
        (⊤ : (L.sum Language.order).Formula (Fin (kk d))) V :=
      Formula.realize_top.mpr trivial
    have hb : ∀ b' ∈ [tfAt d j ⟨i, ⟨⟨n + 1, a⟩, hsub⟩⟩ false (vT1 d)
        (eSel d hn1)],
        Derives (trRules d) ⟨b'.idx, fun q => V (b'.args q)⟩ := by
      intro b' hb'
      rw [List.mem_singleton] at hb'
      subst hb'
      refine LFPHorn.derives_congr_tuple ?_ ((ih hsub (Fin.snoc v y₀)).2 hy₀)
      change _ = fun q => V (Fin.addCases (vT1 d) (eSel d hn1) q)
      rw [LFPHorn.comp_addCases, hT1, hE1]
    have key := Derives.rule (rules := trRules d) hcmem
      (a := tfAt d j ⟨i, ⟨⟨n, a.all⟩, hmem⟩⟩ false (vT1 d) (eSel d hle)) rfl
      hgT hb
    refine LFPHorn.derives_congr_tuple ?_ key
    change (fun q => V (Fin.addCases (vT1 d) (eSel d hle) q)) = _
    rw [LFPHorn.comp_addCases, hT1, hEn]

/-! #### The stages and their complements are derivable -/

/-- **The dual evaluator is complete at a stage**: given that the stage and
its complement are derivable there, truth and falsity of every subformula of
every step formula are derivable, by induction on the subformula. -/
theorem derives_tf {j : Fin (hs d)} {t : Fin (hm d) → A}
    (hS : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      d.inflStage A (srank d A j t) i xt →
      Derives (trRules d) ⟨sIx d j i, Fin.addCases t xt⟩)
    (hN : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      ¬d.inflStage A (srank d A j t) i xt →
      Derives (trRules d) ⟨nIx d j i, Fin.addCases t xt⟩) :
    ∀ {n : ℕ} (ψ : ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n)
      {i : d.B.ι}
      (hmem : (⟨n, ψ⟩ : Σ n',
        ((L.sum Language.order).sum d.B.lang).BoundedFormula Empty n') ∈
          subs (stepB d i)) (v : Fin n → A),
      (evalT d A (srank d A j t) ψ v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, ψ⟩, hmem⟩⟩ true, Fin.addCases t v⟩) ∧
      (¬evalT d A (srank d A j t) ψ v →
        Derives (trRules d) ⟨tfIx d j ⟨i, ⟨⟨n, ψ⟩, hmem⟩⟩ false, Fin.addCases t v⟩) := by
  intro n ψ
  induction ψ with
  | falsum => exact derives_tf_falsum
  | equal t' u => exact derives_tf_equal t' u
  | rel R ts => exact derives_tf_rel hS hN R ts
  | imp a b iha ihb => exact derives_tf_imp a b iha ihb
  | all a ih => exact derives_tf_all a ih

/-- **The stage walk is complete**: at every stage index, the stage and its
complement are derivable – by induction along the cover walk of the stage
order, the evaluator supplying the step formulas' values at the predecessor
stage. -/
theorem derives_SN (u : Fin (hs d) ×ₗ Lex (Fin (hm d) → A)) :
    (∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      d.inflStage A (orank u) i xt →
      Derives (trRules d)
        ⟨sIx d (ofLex u).1 i, Fin.addCases (ofLex (ofLex u).2) xt⟩) ∧
    (∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
      ¬d.inflStage A (orank u) i xt →
      Derives (trRules d)
        ⟨nIx d (ofLex u).1 i, Fin.addCases (ofLex (ofLex u).2) xt⟩) := by
  refine order_induction (A := Fin (hs d) ×ₗ Lex (Fin (hm d) → A))
    (P := fun u =>
      (∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
        d.inflStage A (orank u) i xt →
        Derives (trRules d)
          ⟨sIx d (ofLex u).1 i, Fin.addCases (ofLex (ofLex u).2) xt⟩) ∧
      (∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
        ¬d.inflStage A (orank u) i xt →
        Derives (trRules d)
          ⟨nIx d (ofLex u).1 i, Fin.addCases (ofLex (ofLex u).2) xt⟩))
    ?_ ?_ u
  · -- the bottom stage
    intro u₀ hbot
    have hrank : orank u₀ = 0 := orank_eq_zero hbot
    obtain ⟨hj, ht⟩ :=
      (prodLex_isBot_iff (a := (ofLex u₀).1) (b := (ofLex u₀).2)).mp hbot
    have hj0 : (ofLex u₀).1 = j0 d :=
      le_antisymm (hj (j0 d)) (by rw [Fin.le_def]; simp [j0])
    constructor
    · intro i xt hst
      rw [hrank] at hst
      exact hst.elim
    · intro i xt _
      have hcmem : (HornClause.mk (minTupF (L := L) (vT1 d)) []
          (some (nAt d (j0 d) i (vT1 d) (xa d i)))) ∈ trRules d :=
        mem_trRules_nBase (List.mem_map.mpr ⟨i, d.B.mem_idxList i, rfl⟩)
      set V : Fin (kk d) → A := packV (ofLex (ofLex u₀).2) (ofLex (ofLex u₀).2)
        (padF xt) (fun _ => Classical.arbitrary A) (Classical.arbitrary A) with hV
      have hT1 : (fun q => V (vT1 d q)) = ofLex (ofLex u₀).2 := by
        rw [hV, packV_comp_vT1]
      have hgV : (minTupF (L := L) (vT1 d)).Realize V := by
        refine (realize_minTupF (L := L) _).mpr fun p a' => ?_
        rw [congrFun hT1 p]
        exact tup_isBot_iff.mp ht p a'
      have key := Derives.rule (rules := trRules d) hcmem
        (a := nAt d (j0 d) i (vT1 d) (xa d i)) rfl hgV
        (fun b hb => absurd hb (by simp))
      rw [← hj0] at key
      refine LFPHorn.derives_congr_tuple ?_ key
      change (fun q => V (Fin.addCases (vT1 d) (xa d i) q)) = _
      rw [LFPHorn.comp_addCases, hT1, hV, packV_comp_xa_pad]
  · -- a cover of stages
    intro u₀ u₁ hlt hnb ih
    have hcov : u₀ ⋖ u₁ := ⟨hlt, fun c h1 h2 => hnb c ⟨h1, h2⟩⟩
    have hrank : orank u₁ = orank u₀ + 1 := orank_covBy hcov
    have hjj : ((ofLex u₀).1, (ofLex u₁).1) ∈ stagePairs d :=
      stagePairs_of_covBy (u := (ofLex u₀).2) (u' := (ofLex u₁).2) hcov
    -- the evaluator at the predecessor stage
    have hsrank : srank d A (ofLex u₀).1 (ofLex (ofLex u₀).2) = orank u₀ := rfl
    have hSarg : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
        d.inflStage A (srank d A (ofLex u₀).1 (ofLex (ofLex u₀).2)) i xt →
        Derives (trRules d)
          ⟨sIx d (ofLex u₀).1 i, Fin.addCases (ofLex (ofLex u₀).2) xt⟩ :=
      fun i xt hst => ih.1 i xt (by rwa [hsrank] at hst)
    have hNarg : ∀ (i : d.B.ι) (xt : Fin (d.B.arity i) → A),
        ¬d.inflStage A (srank d A (ofLex u₀).1 (ofLex (ofLex u₀).2)) i xt →
        Derives (trRules d)
          ⟨nIx d (ofLex u₀).1 i, Fin.addCases (ofLex (ofLex u₀).2) xt⟩ :=
      fun i xt hst => ih.2 i xt (by rwa [hsrank] at hst)
    constructor
    · intro i xt hst
      rw [hrank, d.inflStage_succ] at hst
      set V : Fin (kk d) → A := packV (ofLex (ofLex u₀).2) (ofLex (ofLex u₁).2)
        (padF xt) (padF (xt : Fin (d.B.arity i + 0) → A))
        (Classical.arbitrary A) with hV
      have hT1 : (fun q => V (vT1 d q)) = ofLex (ofLex u₀).2 := by
        rw [hV, packV_comp_vT1]
      have hT2 : (fun q => V (vT2 d q)) = ofLex (ofLex u₁).2 := by
        rw [hV, packV_comp_vT2]
      have hgV : (stageG d (ofLex u₀).1 (ofLex u₁).1).Realize V := by
        refine stageG_realize hjj ?_
        rw [hT1, hT2]
        exact hcov
      have hroot : (fun q => V (rootSel d i q)) =
          (xt : Fin (d.B.arity i + 0) → A) := by
        rw [hV]
        exact packV_comp_eSel_pad (subIx_le_hX d (rootSub d i))
          (v := (xt : Fin (d.B.arity i + 0) → A))
      rcases hst with hprev | hnext
      · -- carry
        have hcmem : (HornClause.mk (stageG d (ofLex u₀).1 (ofLex u₁).1)
            [sAt d (ofLex u₀).1 i (vT1 d) (xa d i)]
            (some (sAt d (ofLex u₁).1 i (vT2 d) (xa d i)))) ∈ trRules d :=
          mem_trRules_sCarry (List.mem_flatMap.mpr ⟨((ofLex u₀).1, (ofLex u₁).1), hjj,
            List.mem_map.mpr ⟨i, d.B.mem_idxList i, rfl⟩⟩)
        have hb : ∀ b ∈ [sAt d (ofLex u₀).1 i (vT1 d) (xa d i)],
            Derives (trRules d) ⟨b.idx, fun q => V (b.args q)⟩ := by
          intro b hb
          rw [List.mem_singleton] at hb
          subst hb
          refine LFPHorn.derives_congr_tuple ?_ (ih.1 i xt hprev)
          change _ = fun q => V (Fin.addCases (vT1 d) (xa d i) q)
          rw [LFPHorn.comp_addCases, hT1, hV, packV_comp_xa_pad]
        have key := Derives.rule (rules := trRules d) hcmem
          (a := sAt d (ofLex u₁).1 i (vT2 d) (xa d i)) rfl hgV hb
        refine LFPHorn.derives_congr_tuple ?_ key
        change (fun q => V (Fin.addCases (vT2 d) (xa d i) q)) = _
        rw [LFPHorn.comp_addCases, hT2, hV, packV_comp_xa_pad]
      · -- derive
        have hcmem : (HornClause.mk (stageG d (ofLex u₀).1 (ofLex u₁).1)
            [tfAt d (ofLex u₀).1 (rootSub d i) true (vT1 d) (rootSel d i)]
            (some (sAt d (ofLex u₁).1 i (vT2 d) (rootSel d i)))) ∈ trRules d :=
          mem_trRules_sDerive (List.mem_flatMap.mpr ⟨((ofLex u₀).1, (ofLex u₁).1),
            hjj, List.mem_map.mpr ⟨i, d.B.mem_idxList i, rfl⟩⟩)
        have hT : evalT d A (srank d A (ofLex u₀).1 (ofLex (ofLex u₀).2))
            (stepB d i) (xt : Fin (d.B.arity i + 0) → A) := by
          refine evalT_stepB.mpr ?_
          rw [hsrank]
          exact hnext
        have hb : ∀ b ∈ [tfAt d (ofLex u₀).1 (rootSub d i) true (vT1 d)
            (rootSel d i)],
            Derives (trRules d) ⟨b.idx, fun q => V (b.args q)⟩ := by
          intro b hb
          rw [List.mem_singleton] at hb
          subst hb
          refine LFPHorn.derives_congr_tuple ?_
            ((derives_tf hSarg hNarg (stepB d i) (self_mem_subs (stepB d i))
              (xt : Fin (d.B.arity i + 0) → A)).1 hT)
          change _ = fun q => V (Fin.addCases (vT1 d) (rootSel d i) q)
          rw [LFPHorn.comp_addCases, hT1, hroot]
          rfl
        have key := Derives.rule (rules := trRules d) hcmem
          (a := sAt d (ofLex u₁).1 i (vT2 d) (rootSel d i)) rfl hgV hb
        refine LFPHorn.derives_congr_tuple ?_ key
        change (fun q => V (Fin.addCases (vT2 d) (rootSel d i) q)) = _
        rw [LFPHorn.comp_addCases, hT2, hroot]
        rfl
    · intro i xt hst
      rw [hrank, d.inflStage_succ] at hst
      have hst2 : ¬d.inflStage A (orank u₀) i xt ∧
          ¬d.next (d.inflStage A (orank u₀)) i xt := by
        constructor
        · exact fun hp => hst (Or.inl hp)
        · exact fun hn => hst (Or.inr hn)
      set V : Fin (kk d) → A := packV (ofLex (ofLex u₀).2) (ofLex (ofLex u₁).2)
        (fun _ => Classical.arbitrary A) (padF (xt : Fin (d.B.arity i + 0) → A))
        (Classical.arbitrary A) with hV
      have hT1 : (fun q => V (vT1 d q)) = ofLex (ofLex u₀).2 := by
        rw [hV, packV_comp_vT1]
      have hT2 : (fun q => V (vT2 d q)) = ofLex (ofLex u₁).2 := by
        rw [hV, packV_comp_vT2]
      have hgV : (stageG d (ofLex u₀).1 (ofLex u₁).1).Realize V := by
        refine stageG_realize hjj ?_
        rw [hT1, hT2]
        exact hcov
      have hroot : (fun q => V (rootSel d i q)) =
          (xt : Fin (d.B.arity i + 0) → A) := by
        rw [hV]
        exact packV_comp_eSel_pad (subIx_le_hX d (rootSub d i))
          (v := (xt : Fin (d.B.arity i + 0) → A))
      have hF : ¬evalT d A (srank d A (ofLex u₀).1 (ofLex (ofLex u₀).2))
          (stepB d i) (xt : Fin (d.B.arity i + 0) → A) := by
        intro hT
        have := evalT_stepB.mp hT
        rw [hsrank] at this
        exact hst2.2 this
      have hcmem : (HornClause.mk (stageG d (ofLex u₀).1 (ofLex u₁).1)
          [nAt d (ofLex u₀).1 i (vT1 d) (rootSel d i),
            tfAt d (ofLex u₀).1 (rootSub d i) false (vT1 d) (rootSel d i)]
          (some (nAt d (ofLex u₁).1 i (vT2 d) (rootSel d i)))) ∈ trRules d :=
        mem_trRules_nStep (List.mem_flatMap.mpr ⟨((ofLex u₀).1, (ofLex u₁).1), hjj,
          List.mem_map.mpr ⟨i, d.B.mem_idxList i, rfl⟩⟩)
      have hb : ∀ b ∈ [nAt d (ofLex u₀).1 i (vT1 d) (rootSel d i),
          tfAt d (ofLex u₀).1 (rootSub d i) false (vT1 d) (rootSel d i)],
          Derives (trRules d) ⟨b.idx, fun q => V (b.args q)⟩ := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · refine LFPHorn.derives_congr_tuple ?_ (ih.2 i xt hst2.1)
          change _ = fun q => V (Fin.addCases (vT1 d) (rootSel d i) q)
          rw [LFPHorn.comp_addCases, hT1, hroot]
          rfl
        · rw [List.mem_singleton] at hb'
          subst hb'
          refine LFPHorn.derives_congr_tuple ?_
            ((derives_tf hSarg hNarg (stepB d i) (self_mem_subs (stepB d i))
              (xt : Fin (d.B.arity i + 0) → A)).2 hF)
          change _ = fun q => V (Fin.addCases (vT1 d) (rootSel d i) q)
          rw [LFPHorn.comp_addCases, hT1, hroot]
          rfl
      have key := Derives.rule (rules := trRules d) hcmem
        (a := nAt d (ofLex u₁).1 i (vT2 d) (rootSel d i)) rfl hgV hb
      refine LFPHorn.derives_congr_tuple ?_ key
      change (fun q => V (Fin.addCases (vT2 d) (rootSel d i) q)) = _
      rw [LFPHorn.comp_addCases, hT2, hroot]
      rfl

/-! #### The answer variables are derivable -/

/-- **Every atom of the inflationary limit is derivable on the answer
variables**: read the stage at the top of the walk. -/
theorem derives_r {i : d.B.ι} {x : Fin (d.B.arity i) → A}
    (h : d.inflLimit A i x) : Derives (trRules d) ⟨rIx d i, x⟩ := by
  obtain ⟨mA, hmA⟩ := Finite.exists_max (fun a : A => a)
  have hlim : d.inflStage A (srank d A (jTop d) fun _ => mA) = d.inflLimit A :=
    inflStage_srank_top fun p a' => hmA a'
  have hlim' : d.inflStage A (orank (toLex ((jTop d, toLex fun _ => mA) :
      Fin (hs d) × Lex (Fin (hm d) → A)))) = d.inflLimit A := hlim
  have hS := (derives_SN (toLex ((jTop d, toLex fun _ => mA) :
      Fin (hs d) × Lex (Fin (hm d) → A)))).1 i x (by rw [hlim']; exact h)
  have hcmem : (HornClause.mk (maxTupF (L := L) (vT1 d))
      [sAt d (jTop d) i (vT1 d) (xa d i)] (some (rAt d i (xa d i)))) ∈ trRules d :=
    mem_trRules_rRules (List.mem_map.mpr ⟨i, d.B.mem_idxList i, rfl⟩)
  set V : Fin (kk d) → A := packV (fun _ => mA) (fun _ => mA) (padF x)
    (fun _ => Classical.arbitrary A) (Classical.arbitrary A) with hV
  have hT1 : (fun q => V (vT1 d q)) = fun _ => mA := by rw [hV, packV_comp_vT1]
  have hXa : (fun q => V (xa d i q)) = x := by rw [hV, packV_comp_xa_pad]
  have hgV : (maxTupF (L := L) (vT1 d)).Realize V := by
    refine (realize_maxTupF (L := L) _).mpr fun p a' => ?_
    rw [congrFun hT1 p]
    exact hmA a'
  have hb : ∀ b ∈ [sAt d (jTop d) i (vT1 d) (xa d i)],
      Derives (trRules d) ⟨b.idx, fun q => V (b.args q)⟩ := by
    intro b hb
    rw [List.mem_singleton] at hb
    subst hb
    refine LFPHorn.derives_congr_tuple ?_ hS
    change _ = fun q => V (Fin.addCases (vT1 d) (xa d i) q)
    rw [LFPHorn.comp_addCases, hT1, hXa]
    rfl
  have key := Derives.rule (rules := trRules d) hcmem (a := rAt d i (xa d i)) rfl
    hgV hb
  exact LFPHorn.derives_congr_tuple hXa key

end Completeness

/-! ### Assembly: the capture of the inflationary limit -/

section Assembly

variable {d}
variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **The answer variables of the least model are the inflationary limit**:
soundness bounds the least model by the canonical assignment, and
completeness derives every limit atom. -/
theorem homAssign_lfpAssign_trRules :
    SOBlock.homAssign (B := d.B) (B' := trBlock d) (rIx d) (trArity_rIx d)
      (lfpAssign (trRules d)) = d.inflLimit A := by
  funext i x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have hsub := lfpAssign_least_of_closed (ρ := canonAssign d A)
      (fun c hc a ha v hg hb => by
        have hHolds := trRules_sound (d := d) (A := A) v (c := c) hc
        have := hHolds ⟨hg, hb⟩
        rwa [HornClause.HeadHolds, ha, Option.elim_some] at this) h
    exact hsub
  · exact derives_r h

/-- **The translated definition means the inflationary definition.** -/
private theorem trDef_holds_iff : (trDef d).Holds A ↔ d.IFPHolds A := by
  rw [LFPDef.Holds, StepDef.IFPHolds]
  have htrans := SOBlock.realize_homSentence (B := d.B) (B' := trBlock d) (rIx d)
    (trArity_rIx d) (L := L.sum Language.order) (A := A)
    (lfpAssign (trRules d)) d.out
  rw [homAssign_lfpAssign_trRules] at htrans
  exact htrans

end Assembly

end IFPLfp

open IFPLfp in
/-- **Every FO(≤, IFP) definition is an FO(LFP) definition**: the hard half of
the capture theorem FO(≤, IFP) = PTIME – translate the inflationary iteration
into a stage walk with a dual truth/falsity evaluator for the step
formulas.
Registered in the Lax archive as
[`Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_lfpDefinable`](https://laxarchive.org/lax-535992/Lax535992.InflationaryIsLeastFixedPoint.html#s-Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_lfpDefinable). -/
theorem IFPDefinable.lfpDefinable {L : Language.{0, 0}} [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinable P) : LFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨trDef d, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (trDef_holds_iff (d := d)).symm

/-- **FO(≤, IFP) = FO(LFP)** ([Gurevich–Shelah 1986][gurevich1986fixed]: on
ordered structures, and indeed on all structures, the inflationary fixed
point adds no power over the least fixed point; here the ordered capture,
proved by translation in both directions). -/
theorem ifpDefinable_iff_lfpDefinable {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    IFPDefinable P ↔ LFPDefinable P :=
  ⟨IFPDefinable.lfpDefinable, LFPDefinable.ifpDefinable⟩

/-- **The capture theorem FO(≤, IFP) = PTIME**: a problem is FO(≤, IFP)
definable exactly when it is in PTIME.
Registered in the Lax archive as
[`Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_iff_mem_PTIME`](https://laxarchive.org/lax-535992/Lax535992.InflationaryIsLeastFixedPoint.html#s-Lax535992.InflationaryIsLeastFixedPoint.ifpDefinable_iff_mem_PTIME). -/
theorem ifpDefinable_iff_mem_PTIME {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) :
    IFPDefinable P ↔ P ∈ PTIME :=
  (ifpDefinable_iff_lfpDefinable P).trans (lfpDefinable_iff_sigmaSOHornDefinable P)

end DescriptiveComplexity
