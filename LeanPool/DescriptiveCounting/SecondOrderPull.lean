/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Composition
public import LeanPool.DescriptiveCounting.SecondOrder
public import Mathlib.Basic.Finite.Sigma

/-!
# Pulling second-order definability back through an interpretation

If `P ≤ᶠᵒ Q` and `Q` is `Σₖ`- (resp. `Πₖ`-) definable, then so is `P`
(`DescriptiveComplexity.SigmaSODefinable.of_foReduction`,
`DescriptiveComplexity.PiSODefinable.of_foReduction`): the levels of the polynomial
hierarchy, defined by second-order alternation, are closed under first-order
reductions.

The proof pulls the defining second-order sentence back through the
interpretation `I` underlying the reduction, block by block:

* a second-order quantifier over an `n`-ary relation on the interpreted
  universe `Tag × A^d` becomes a family of second-order quantifiers over
  `(n·d)`-ary relations on `A`, one per `n`-tuple of tags
  (`DescriptiveComplexity.SOBlock.pull`; assignments transfer bijectively via
  `DescriptiveComplexity.SOBlock.pullAssign` / `DescriptiveComplexity.SOBlock.mergeAssign`);
* the interpretation extends to the languages expanded by a block
  (`DescriptiveComplexity.FOInterpretation.extendSO`): relation variables of the block
  are interpreted by the corresponding pulled relation variables, reading the
  tag tuple off statically; interpreting-then-expanding agrees with
  expanding-then-interpreting (`DescriptiveComplexity.FOInterpretation.extendSOEquiv`);
* the first-order kernel is pulled back by
  `DescriptiveComplexity.FOInterpretation.pull` from `DescriptiveComplexity.Composition`, packaged
  at the sentence level as `DescriptiveComplexity.FOInterpretation.pullSentence`.

`DescriptiveComplexity.sorealize_pullSO` puts these together: alternating second-order
satisfaction in the interpreted structure coincides with alternating
second-order satisfaction of the pulled sentence (over the pulled blocks) in
the base structure.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Pulling back a sentence -/

section PullSentence

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]
variable (I : FOInterpretation L₁ L₂ Tag d)

/-- The pullback of an `L₂`-sentence through the interpretation `I`: an
`L₁`-sentence that holds in `A` exactly when the original sentence holds in
`I.Map A` (see `FOInterpretation.realize_pullSentence`). -/
noncomputable def FOInterpretation.pullSentence (φ : L₂.Sentence) : L₁.Sentence :=
  (I.pull (φ : L₂.BoundedFormula Empty 0) (isEmptyElim : (Empty ⊕ Fin 0) → Tag)).relabel
    fun p => (isEmptyElim p.1 : Empty)

theorem FOInterpretation.realize_pullSentence (φ : L₂.Sentence) (A : Type)
    [L₁.Structure A] :
    A ⊨ I.pullSentence φ ↔ I.Map A ⊨ φ := by
  have h1 : A ⊨ I.pullSentence φ ↔
      (I.pull (φ : L₂.BoundedFormula Empty 0) (isEmptyElim : (Empty ⊕ Fin 0) → Tag)).Realize
        ((default : Empty → A) ∘ fun p : (Empty ⊕ Fin 0) × Fin d =>
          (isEmptyElim p.1 : Empty)) :=
    Formula.realize_relabel
  rw [h1, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula Empty 0) a b)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end PullSentence

/-! ### Pulling back a block -/

section PullBlock

variable (Tag : Type) [Finite Tag] (d : ℕ)

/-- The pullback of a second-order quantifier block through a tagged
`d`-dimensional interpretation: an `n`-ary relation variable on the
interpreted universe `Tag × A^d` becomes one `(n·d)`-ary relation variable on
`A` per `n`-tuple of tags. -/
def SOBlock.pull (B : SOBlock) : SOBlock where
  ι := Σ i : B.ι, Fin (B.arity i) → Tag
  arity p := B.arity p.1 * d

variable {Tag d} {A : Type}

/-- Transfer of an assignment on the interpreted universe to an assignment of
the pulled block on the base universe. -/
def SOBlock.pullAssign (B : SOBlock) (ρ : B.Assignment (Tag × (Fin d → A))) :
    (B.pull Tag d).Assignment A :=
  fun p x => ρ p.1 fun k => (p.2 k, fun j => x (finProdFinEquiv (k, j)))

/-- Transfer of an assignment of the pulled block on the base universe to an
assignment on the interpreted universe. -/
def SOBlock.mergeAssign (B : SOBlock) (σ : (B.pull Tag d).Assignment A) :
    B.Assignment (Tag × (Fin d → A)) :=
  fun i y => σ ⟨i, fun k => (y k).1⟩
    fun m => (y (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2

/-- The two assignment transfers are inverse (in the direction needed to
biject the second-order quantifiers). -/
theorem SOBlock.pullAssign_mergeAssign (B : SOBlock) (σ : (B.pull Tag d).Assignment A) :
    B.pullAssign (B.mergeAssign σ) = σ := by
  funext p x
  change σ p
    (fun m => x (finProdFinEquiv
      ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))) = σ p x
  exact congrArg (σ p) (funext fun m => congrArg x (Equiv.apply_symm_apply _ _))

/-- Merging a pulled assignment gives the assignment back: the transfer
`DescriptiveComplexity.SOBlock.pullAssign` is injective, with
`DescriptiveComplexity.SOBlock.mergeAssign` as a retraction on the other side. -/
theorem SOBlock.mergeAssign_pullAssign (B : SOBlock)
    (ρ : B.Assignment (Tag × (Fin d → A))) : B.mergeAssign (B.pullAssign ρ) = ρ := by
  funext i y
  change ρ i (fun k => ((y k).1, fun j =>
    (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).2
      (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2)) = ρ i y
  refine congrArg (ρ i) (funext fun k => ?_)
  simp only [Equiv.symm_apply_apply]

variable (Tag d A) in
/-- Assignments of the pulled block on the base universe correspond bijectively
to assignments of the block on the tagged tuples. This is what a pullback needs
when the assignments themselves matter and not only their existence: the states
of a walk (`DescriptiveComplexity.SecondOrderTransitiveClosurePull`), the witnesses a
counting problem counts (`DescriptiveComplexity.witnessCount_map`). -/
def SOBlock.pullAssignEquiv (B : SOBlock) :
    B.Assignment (Tag × (Fin d → A)) ≃ (B.pull Tag d).Assignment A where
  toFun := B.pullAssign
  invFun := B.mergeAssign
  left_inv := B.mergeAssign_pullAssign
  right_inv := B.pullAssign_mergeAssign

end PullBlock

/-! ### Extending an interpretation along a block -/

section ExtendSO

variable {Tag : Type} {d : ℕ} [L₂.IsRelational] [Finite Tag]

/-- The relation symbol of the pulled block corresponding to a relation
variable of the original block and a tuple of tags. -/
def SOBlock.pullSym (B : SOBlock) (Tag : Type) [Finite Tag] (d : ℕ) {n : ℕ}
    (r : B.lang.Relations n) (τ : Fin n → Tag) :
    (B.pull Tag d).lang.Relations (B.arity r.1 * d) :=
  ⟨⟨r.1, fun k => τ (Fin.cast r.2 k)⟩, rfl⟩

/-- Extension of an interpretation along a second-order quantifier block: an
interpretation of the target language expanded by the block in the source
language expanded by the pulled block. Symbols of the target language keep
their defining formulas; a relation variable of the block is interpreted by
the pulled relation variable selected by the (static) tag tuple, its
argument positions decoded by `finProdFinEquiv`. -/
def FOInterpretation.extendSO (I : FOInterpretation L₁ L₂ Tag d) (B : SOBlock) :
    FOInterpretation (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) Tag d where
  relFormula {_n} R τ :=
    match R with
    | Sum.inl r => LHom.sumInl.onFormula (I.relFormula r τ)
    | Sum.inr r =>
        Relations.formula (Sum.inr (B.pullSym Tag d r τ))
          fun m => Term.var
            (Fin.cast r.2 (finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)

variable (I : FOInterpretation L₁ L₂ Tag d) (B : SOBlock) (A : Type)
variable [instA : L₁.Structure A]

/-- Interpreting and then expanding by a block agrees with expanding by the
pulled block and then interpreting through the extended interpretation: the
identity map is an isomorphism over the expanded target language, when the
block is interpreted by an assignment on the interpreted universe on one side
and by its pulled transfer on the other. -/
def FOInterpretation.extendSOEquiv (ρ : B.Assignment (I.Map A)) :
    @Language.Equiv (L₂.sum B.lang) ((I.extendSO B).Map A) (I.Map A)
      (letI := (B.pull Tag d).structure (B.pullAssign ρ)
       FOInterpretation.mapStructure (I.extendSO B) A)
      (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) :=
  letI := (B.pull Tag d).structure (B.pullAssign ρ)
  letI := B.structure ρ
  { toEquiv := Equiv.refl _
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r =>
        exact (LHom.realize_onFormula LHom.sumInl
          (I.relFormula r fun i => (x i).1)).symm
      | inr r =>
        change ρ r.1 (fun j => x (Fin.cast r.2 j)) ↔
          ρ r.1 (fun k => ((x (Fin.cast r.2 k)).1,
            fun j => (x (Fin.cast r.2
                (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).2
              (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2))
        refine iff_of_eq (congrArg (ρ r.1) (funext fun k => ?_))
        simp only [Equiv.symm_apply_apply]
        exact rfl }

end ExtendSO

/-! ### Pulling back an alternating second-order sentence -/

section PullSO

variable {Tag : Type} {d : ℕ} [Finite Tag]

/-- The blockwise pullback of a list of blocks. -/
def pullBlocks (Tag : Type) [Finite Tag] (d : ℕ) (Bs : List SOBlock) : List SOBlock :=
  Bs.map fun B => B.pull Tag d

/-- The pullback of a sentence over the block expansion of the target
language: pull each block, then pull the first-order kernel through the
(iteratively extended) interpretation. -/
noncomputable def pullSO :
    ∀ (Bs : List SOBlock) (L₁ L₂ : Language.{0, 0}) [L₂.IsRelational]
      (_I : FOInterpretation L₁ L₂ Tag d),
      (soLang L₂ Bs).Sentence → (soLang L₁ (pullBlocks Tag d Bs)).Sentence
  | [], _, _, _, I, φ => I.pullSentence φ
  | B :: Bs, L₁, L₂, _, I, φ =>
      pullSO Bs (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) (I.extendSO B) φ

private theorem sorealize_pullSO_aux :
    ∀ (Bs : List SOBlock) (L₁ L₂ : Language.{0, 0}) (instRel : L₂.IsRelational)
      (I : FOInterpretation L₁ L₂ Tag d) (A : Type) (instA : L₁.Structure A)
      (φ : (soLang L₂ Bs).Sentence) (pol : Bool),
      @SORealize L₂ (I.Map A)
          (@FOInterpretation.mapStructure L₁ L₂ Tag d I A instA instRel) Bs φ pol ↔
        @SORealize L₁ A instA (pullBlocks Tag d Bs)
          (@pullSO Tag d _ Bs L₁ L₂ instRel I φ) pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L₁ L₂ instRel I A instA φ pol
    exact (I.realize_pullSentence φ A).symm
  | cons B Bs ih =>
    intro L₁ L₂ instRel I A instA φ pol
    let := instA
    have key : ∀ ρ : B.Assignment (I.Map A),
        (@SORealize (L₂.sum B.lang) (I.Map A)
            (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) Bs φ
            (!pol) ↔
          @SORealize (L₁.sum (B.pull Tag d).lang) A
            (@sumStructure L₁ (B.pull Tag d).lang A instA
              ((B.pull Tag d).structure (B.pullAssign ρ)))
            (pullBlocks Tag d Bs)
            (@pullSO Tag d _ Bs (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) _
              (I.extendSO B) φ) (!pol)) := by
      intro ρ
      let := (B.pull Tag d).structure (B.pullAssign ρ)
      refine Iff.trans (Iff.symm (@sorealize_iso (L₂.sum B.lang) ((I.extendSO B).Map A)
        (I.Map A) (FOInterpretation.mapStructure (I.extendSO B) A)
        (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ))
        (I.extendSOEquiv B A ρ) Bs φ (!pol))) ?_
      exact ih (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) inferInstance (I.extendSO B) A
        (@sumStructure L₁ (B.pull Tag d).lang A instA
          ((B.pull Tag d).structure (B.pullAssign ρ))) φ (!pol)
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment (I.Map A),
          @SORealize (L₂.sum B.lang) (I.Map A)
            (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) Bs φ
            false) ↔
        ∃ σ : (B.pull Tag d).Assignment A,
          @SORealize (L₁.sum (B.pull Tag d).lang) A
            (@sumStructure L₁ (B.pull Tag d).lang A instA ((B.pull Tag d).structure σ))
            (pullBlocks Tag d Bs)
            (@pullSO Tag d _ Bs (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) _
              (I.extendSO B) φ) false
      constructor
      · rintro ⟨ρ, h⟩
        exact ⟨B.pullAssign ρ, (key ρ).mp h⟩
      · rintro ⟨σ, h⟩
        rw [← B.pullAssign_mergeAssign σ] at h
        exact ⟨B.mergeAssign σ, (key (B.mergeAssign σ)).mpr h⟩
    | false =>
      change (∀ ρ : B.Assignment (I.Map A),
          @SORealize (L₂.sum B.lang) (I.Map A)
            (@sumStructure L₂ B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) Bs φ
            true) ↔
        ∀ σ : (B.pull Tag d).Assignment A,
          @SORealize (L₁.sum (B.pull Tag d).lang) A
            (@sumStructure L₁ (B.pull Tag d).lang A instA ((B.pull Tag d).structure σ))
            (pullBlocks Tag d Bs)
            (@pullSO Tag d _ Bs (L₁.sum (B.pull Tag d).lang) (L₂.sum B.lang) _
              (I.extendSO B) φ) true
      constructor
      · intro h σ
        rw [← B.pullAssign_mergeAssign σ]
        exact (key (B.mergeAssign σ)).mp (h (B.mergeAssign σ))
      · intro h ρ
        exact (key ρ).mpr (h (B.pullAssign ρ))

/-- **Pulling second-order satisfaction back through an interpretation**:
alternating second-order satisfaction in the interpreted structure coincides
with satisfaction of the pulled sentence, over the pulled blocks, in the base
structure. -/
theorem sorealize_pullSO [instRel : L₂.IsRelational] (I : FOInterpretation L₁ L₂ Tag d)
    (A : Type) [L₁.Structure A] (Bs : List SOBlock) (φ : (soLang L₂ Bs).Sentence)
    (pol : Bool) :
    SORealize L₂ (I.Map A) Bs φ pol ↔
      SORealize L₁ A (pullBlocks Tag d Bs) (pullSO Bs L₁ L₂ I φ) pol :=
  sorealize_pullSO_aux Bs L₁ L₂ instRel I A _ φ pol

end PullSO

/-! ### Closure of the definability levels under FO reductions -/

section Closure

variable [L₁.IsRelational] [L₂.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
variable {k : ℕ}

/-- `Σₖ`-definability is closed under first-order reductions.
Registered in the Lax archive (for `NP`) as
[`Lax904597.NPClass.NP_mem_of_foReduction`](https://laxarchive.org/lax-904597/Lax904597.NPClass.html#s-Lax904597.NPClass.NP_mem_of_foReduction). -/
theorem SigmaSODefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : SigmaSODefinable k Q) :
    SigmaSODefinable k P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨pullBlocks f.Tag f.dim Bs, by simp [pullBlocks, hk],
    pullSO Bs L₁ L₂ f.toInterpretation φ, ?_⟩
  intro A _ _ _
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hφ (f.toInterpretation.Map A)).trans
    (sorealize_pullSO f.toInterpretation A Bs φ true))

/-- `Πₖ`-definability is closed under first-order reductions. -/
theorem PiSODefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : PiSODefinable k Q) :
    PiSODefinable k P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨pullBlocks f.Tag f.dim Bs, by simp [pullBlocks, hk],
    pullSO Bs L₁ L₂ f.toInterpretation φ, ?_⟩
  intro A _ _ _
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  exact (f.correct A).trans ((hφ (f.toInterpretation.Map A)).trans
    (sorealize_pullSO f.toInterpretation A Bs φ false))

end Closure

/-! ### Pulling back atoms, guards and tag assignments

The clausal fragments (SO-Horn, SO-Krom) pull a *clause list* back through an
interpretation rather than a formula: each clause becomes one clause per static
assignment of tags to its universally quantified variables, its guard becoming
an ordinary formula pullback and its atoms becoming atoms of the pulled
relation variables. The pieces that do not depend on the shape of a clause are
collected here, and are shared by `DescriptiveComplexity.SecondOrderHornPull` and
`DescriptiveComplexity.SecondOrderKromPull`. -/

section Clausal

variable {Tag : Type} [Finite Tag] {d : ℕ} {B : SOBlock} {k : ℕ}

/-- The pullback of a second-order atom at a static assignment of tags to the
universally quantified variables: the atom of the pulled relation variable
selected by the tags, its arguments the `d` coordinates of each original
argument. -/
def SOAtom.pull (a : SOAtom B k) (d : ℕ) (t : Fin k → Tag) :
    SOAtom (B.pull Tag d) (k * d) where
  idx := ⟨a.idx, fun j => t (a.args j)⟩
  args := fun m =>
    finProdFinEquiv (a.args (finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)

/-- The interpreted valuation determined by a tag assignment and a valuation
of the coordinates. -/
def tagVal (I : FOInterpretation L₁ L₂ Tag d) {A : Type} (t : Fin k → Tag)
    (w : Fin (k * d) → A) : Fin k → I.Map A :=
  fun p => (t p, fun j => w (finProdFinEquiv (p, j)))

private theorem SOAtom.pull_holds {A : Type} (I : FOInterpretation L₁ L₂ Tag d) (a : SOAtom B k)
    (t : Fin k → Tag) (ρ : B.Assignment (I.Map A)) (w : Fin (k * d) → A) :
    (a.pull d t).Holds (B.pullAssign ρ) w ↔ a.Holds ρ (tagVal I t w) := by
  refine iff_of_eq (congrArg (ρ a.idx) (funext fun j => ?_))
  refine Prod.ext_iff.mpr ⟨rfl, funext fun i => ?_⟩
  refine congrArg w ?_
  change finProdFinEquiv (a.args (finProdFinEquiv.symm (finProdFinEquiv (j, i))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (j, i))).2) = finProdFinEquiv (a.args j, i)
  rw [Equiv.symm_apply_apply]

omit [Finite Tag] in
/-- Splitting an interpreted valuation into its tags and its coordinates. -/
theorem tagVal_split {A : Type} (I : FOInterpretation L₁ L₂ Tag d) (v : Fin k → I.Map A) :
    tagVal I (fun p => (v p).1)
      (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2) = v := by
  funext p
  refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
  rw [tagVal]
  exact congrArg₂ (fun (q : Fin k) (i : Fin d) => (v q).2 i)
    (congrArg Prod.fst (Equiv.symm_apply_apply _ _))
    (congrArg Prod.snd (Equiv.symm_apply_apply _ _))

section Guards

variable [L₂.IsRelational]

/-- The pullback of a guard: the ordinary formula pullback at the tag
assignment `t`, its variables re-indexed as coordinates. -/
noncomputable def guardPull (I : FOInterpretation L₁ L₂ Tag d) (φ : L₂.Formula (Fin k))
    (t : Fin k → Tag) : L₁.Formula (Fin (k * d)) :=
  (I.pull (φ : L₂.BoundedFormula (Fin k) 0) (Sum.elim t finZeroElim)).relabel
    fun p => finProdFinEquiv (Sum.elim id finZeroElim p.1, p.2)

private theorem realize_guardPull {A : Type} [L₁.Structure A] (I : FOInterpretation L₁ L₂ Tag d)
    (φ : L₂.Formula (Fin k)) (t : Fin k → Tag) (w : Fin (k * d) → A) :
    (guardPull I φ t).Realize w ↔ φ.Realize (M := I.Map A) (tagVal I t w) := by
  rw [guardPull, Formula.realize_relabel, I.realize_pull]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := I.Map A) (φ : L₂.BoundedFormula (Fin k) 0) a b)
    (funext fun _ => rfl) (Subsingleton.elim _ _))

end Guards

open Classical in
/-- All assignments of tags to the `k` universally quantified variables, as a
list: the pullback of a clause is instantiated at each of them. -/
noncomputable def allTagAssign (Tag : Type) [Finite Tag] (k : ℕ) : List (Fin k → Tag) :=
  letI : Fintype Tag := Fintype.ofFinite Tag
  (Finset.univ : Finset (Fin k → Tag)).toList

open Classical in
private theorem mem_allTagAssign (t : Fin k → Tag) : t ∈ allTagAssign Tag k := by
  let : Fintype Tag := Fintype.ofFinite Tag
  exact Finset.mem_toList.mpr (Finset.mem_univ t)

end Clausal

end DescriptiveComplexity
