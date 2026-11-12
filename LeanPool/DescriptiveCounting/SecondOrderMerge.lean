/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrderLift

/-!
# Merging a quantifier prefix into a single second-order block

A second-order sentence with `k` alternating blocks quantifies over a list of
blocks `Bs`, and its kernel lives over the iterated expansion
`DescriptiveComplexity.soLang L Bs`. Constructions that must *read* the kernel – above all
the Tseitin translation of `DescriptiveComplexity.Problems.Sat.Tseitin`, which turns it
into a CNF instance – are stated for a single block, over `L.sum B.lang`.

This file bridges the two: `DescriptiveComplexity.mergeBlocks` collects a list of blocks
into one block whose relation variables are the disjoint union of theirs, and
`DescriptiveComplexity.mergeHom` transports the kernel accordingly. The alternation is
*not* lost – it moves from the block list to
`DescriptiveComplexity.altAssign`, which quantifies the components of a merged assignment
alternately – so `DescriptiveComplexity.sorealize_iff_altAssign` rewrites alternating
second-order satisfaction as an alternating quantification over the pieces of
a single assignment, with a single-block kernel.

The only mathematical content is the re-association
`(L ⊕ B) ⊕ M ≅ L ⊕ (B ⊕ M)` of `DescriptiveComplexity.mergeStep`, applied once per block.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Merging blocks -/

/-- Prepending a block to another: the relation variables are the disjoint
union of both families. Reducible, so that `(SOBlock.cons B M).ι` unfolds to a
sum type when elaborating index literals. -/
@[reducible]
def SOBlock.cons (B M : SOBlock) : SOBlock where
  ι := B.ι ⊕ M.ι
  arity := Sum.elim B.arity M.arity

/-- The single block merging a whole list of blocks: one relation variable per
relation variable of one of the blocks. -/
def mergeBlocks : List SOBlock → SOBlock
  | [] => SOBlock.trivial
  | B :: Bs => SOBlock.cons B (mergeBlocks Bs)

/-- An assignment of the merged block `SOBlock.cons B M`, assembled from an
assignment of `B` and one of `M`. -/
def consAssign {A : Type} {B M : SOBlock} (ρ : B.Assignment A) (μ : M.Assignment A) :
    (SOBlock.cons B M).Assignment A
  | Sum.inl i => ρ i
  | Sum.inr i => μ i

/-- The unique assignment of the merged block of the empty list. -/
def nilAssign (A : Type) : (mergeBlocks []).Assignment A :=
  fun i => Empty.elim (i : Empty)

/-! ### Re-associating an expansion -/

/-- Re-association of language expansions: expanding `L` by a block `B` and
then by a block `M` is expanding `L` by the merged block `SOBlock.cons B M`. -/
def mergeStep (L : Language.{0, 0}) (B M : SOBlock) :
    (L.sum B.lang).sum M.lang →ᴸ L.sum (SOBlock.cons B M).lang where
  onFunction := fun {_} f =>
    match f with
    | Sum.inl (Sum.inl f) => Sum.inl f
    | Sum.inl (Sum.inr f) => isEmptyElim f
    | Sum.inr f => isEmptyElim f
  onRelation := fun {_} r =>
    match r with
    | Sum.inl (Sum.inl r) => Sum.inl r
    | Sum.inl (Sum.inr r) => Sum.inr ⟨Sum.inl r.1, r.2⟩
    | Sum.inr r => Sum.inr ⟨Sum.inr r.1, r.2⟩

/-- The re-association is an expansion: it does not change how any symbol is
interpreted, when the two block assignments on one side are assembled into a
single merged assignment on the other. -/
private theorem mergeStep_isExpansionOn (L : Language.{0, 0}) {A : Type} (instL : L.Structure A)
    (B M : SOBlock) (ρ : B.Assignment A) (μ : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (mergeStep L B M) A
      (@sumStructure (L.sum B.lang) M.lang A
        (@sumStructure L B.lang A instL (B.structure ρ)) (M.structure μ))
      (@sumStructure L (SOBlock.cons B M).lang A instL
        ((SOBlock.cons B M).structure (consAssign ρ μ))) := by
  let := instL
  let := B.structure ρ
  let := M.structure μ
  let := (SOBlock.cons B M).structure (consAssign ρ μ)
  refine ⟨?_, ?_⟩
  · intro n f x
    rcases f with f | f
    · rcases f with f | f
      · rfl
      · exact isEmptyElim f
    · exact isEmptyElim f
  · intro n r x
    rcases r with r | r
    · rcases r with r | r
      · rfl
      · rfl
    · rfl

/-! ### Transporting the kernel -/

/-- The morphism transporting a kernel over the iterated block expansion into
one over the single merged block. -/
def mergeHom : ∀ (Bs : List SOBlock) (L : Language.{0, 0}),
    soLang L Bs →ᴸ L.sum (mergeBlocks Bs).lang
  | [], _ => LHom.sumInl
  | B :: Bs, L => (mergeStep L B (mergeBlocks Bs)).comp (mergeHom Bs (L.sum B.lang))

private theorem mergeHom_cons (B : SOBlock) (Bs : List SOBlock) (L : Language.{0, 0})
    (φ : (soLang L (B :: Bs)).Sentence) :
    (mergeHom (B :: Bs) L).onSentence φ =
      (mergeStep L B (mergeBlocks Bs)).onSentence
        ((mergeHom Bs (L.sum B.lang)).onSentence φ) :=
  congrFun (LHom.comp_onBoundedFormula (mergeStep L B (mergeBlocks Bs))
    (mergeHom Bs (L.sum B.lang))) φ

/-! ### Alternating quantification over a merged assignment -/

/-- Alternating quantification over the components of an assignment of the
merged block: the component of the first block is quantified outermost,
existentially if `pol` is `true`, and the polarities alternate inwards. -/
def altAssign (A : Type) : ∀ (Bs : List SOBlock),
    ((mergeBlocks Bs).Assignment A → Prop) → Bool → Prop
  | [], P, _ => P (nilAssign A)
  | B :: Bs, P, true =>
      ∃ ρ : B.Assignment A, altAssign A Bs (fun μ => P (consAssign ρ μ)) false
  | B :: Bs, P, false =>
      ∀ ρ : B.Assignment A, altAssign A Bs (fun μ => P (consAssign ρ μ)) true

/-- Alternating quantification over a merged assignment only depends on the
quantified predicate up to pointwise equivalence. -/
private theorem altAssign_congr {A : Type} :
    ∀ (Bs : List SOBlock) (P Q : (mergeBlocks Bs).Assignment A → Prop),
      (∀ μ, P μ ↔ Q μ) → ∀ pol : Bool, altAssign A Bs P pol ↔ altAssign A Bs Q pol := by
  intro Bs
  induction Bs with
  | nil => intro P Q h pol; exact h _
  | cons B Bs ih =>
    intro P Q h pol
    cases pol with
    | true => exact exists_congr fun ρ => ih _ _ (fun μ => h _) false
    | false => exact forall_congr' fun ρ => ih _ _ (fun μ => h _) true

/-! ### The merging theorem -/

/-- **Merging a quantifier prefix**: alternating second-order satisfaction
over a list of blocks is the alternating quantification, over the components
of a single merged assignment, of the transported kernel. -/
theorem sorealize_iff_altAssign :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A instL Bs φ pol ↔
        altAssign A Bs (fun μ =>
          @Sentence.Realize (L.sum (mergeBlocks Bs).lang) A
            (@sumStructure L (mergeBlocks Bs).lang A instL ((mergeBlocks Bs).structure μ))
            ((mergeHom Bs L).onSentence φ)) pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL φ pol
    let := instL
    let := SOBlock.trivial.structure (nilAssign A)
    exact ((LHom.sumInl : L →ᴸ L.sum SOBlock.trivial.lang).realize_onSentence A φ).symm
  | cons B Bs ih =>
    intro L A instL φ pol
    have key : ∀ (ρ : B.Assignment A) (μ : (mergeBlocks Bs).Assignment A),
        @Sentence.Realize ((L.sum B.lang).sum (mergeBlocks Bs).lang) A
            (@sumStructure (L.sum B.lang) (mergeBlocks Bs).lang A
              (@sumStructure L B.lang A instL (B.structure ρ))
              ((mergeBlocks Bs).structure μ))
            ((mergeHom Bs (L.sum B.lang)).onSentence φ) ↔
          @Sentence.Realize (L.sum (mergeBlocks (B :: Bs)).lang) A
            (@sumStructure L (mergeBlocks (B :: Bs)).lang A instL
              ((mergeBlocks (B :: Bs)).structure (consAssign ρ μ)))
            ((mergeHom (B :: Bs) L).onSentence φ) := by
      intro ρ μ
      let := instL
      let := B.structure ρ
      let := (mergeBlocks Bs).structure μ
      let := (SOBlock.cons B (mergeBlocks Bs)).structure (consAssign ρ μ)
      rw [mergeHom_cons]
      have := mergeStep_isExpansionOn L instL B (mergeBlocks Bs) ρ μ
      exact ((mergeStep L B (mergeBlocks Bs)).realize_onSentence A _).symm
    cases pol with
    | true =>
      exact exists_congr fun ρ =>
        (ih (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) φ false).trans
          (altAssign_congr Bs _ _ (fun μ => key ρ μ) false)
    | false =>
      exact forall_congr' fun ρ =>
        (ih (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) φ true).trans
          (altAssign_congr Bs _ _ (fun μ => key ρ μ) true)

/-! ### Enlarging the innermost block

The Tseitin translation of a kernel introduces auxiliary *gate* variables,
which have to be quantified together with the relation variables of the
innermost block. The constructions below enlarge the last block of a prefix by
a further block `Gt`, and show that quantifying the enlarged prefix is
quantifying the original one with an extra quantifier – of the *innermost*
polarity – over `Gt` inside. Lists are given as a head and a tail, so that
“nonempty” is built into the syntax and the recursion has no overlapping
patterns. -/

/-- Quantification with a polarity: existential if `pol` is `true`. -/
def quantB (pol : Bool) {α : Type} (P : α → Prop) : Prop :=
  match pol with
  | true => ∃ a, P a
  | false => ∀ a, P a

/-- The polarity of the innermost quantifier of a prefix whose tail has length
`n` and whose outermost polarity is `pol`. -/
def innerPol : ℕ → Bool → Bool
  | 0, pol => pol
  | n + 1, pol => innerPol n (!pol)

/-- The innermost polarity in closed form: it flips with the parity of the
number of blocks below it. -/
private theorem innerPol_eq
    : ∀ (n : ℕ) (pol : Bool), innerPol n pol = xor (decide (n % 2 = 1)) pol := by
  intro n
  induction n with
  | zero => intro pol; cases pol <;> rfl
  | succ n ih =>
    intro pol
    rw [innerPol, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h1 : (n + 1) % 2 = 1 := by omega
      rw [h, h1]; cases pol <;> rfl
    · have h1 : (n + 1) % 2 = 0 := by omega
      rw [h, h1]; cases pol <;> rfl

/-- The prefix `B :: Bs` with its innermost block enlarged by `Gt`. Reducible,
so that `(consLast Gt B Bs).length` computes and `Fin` numerals over it
elaborate. -/
@[reducible]
def consLast (Gt : SOBlock) : SOBlock → List SOBlock → List SOBlock
  | B, [] => [SOBlock.cons B Gt]
  | B, B' :: Bs => B :: consLast Gt B' Bs

/-- An assignment of the enlarged prefix, assembled from an assignment of the
original prefix and one of the extra block. -/
def combineLast (Gt : SOBlock) {A : Type} : ∀ (B : SOBlock) (Bs : List SOBlock),
    (mergeBlocks (B :: Bs)).Assignment A → Gt.Assignment A →
      (mergeBlocks (consLast Gt B Bs)).Assignment A
  | _, [], μ, g => consAssign (consAssign (fun i => μ (Sum.inl i)) g) (nilAssign A)
  | _, B' :: Bs, μ, g =>
      consAssign (fun i => μ (Sum.inl i)) (combineLast Gt B' Bs (fun i => μ (Sum.inr i)) g)

/-- Enlarging the innermost block does not change the number of blocks. -/
theorem consLast_length (Gt : SOBlock) :
    ∀ (B : SOBlock) (Bs : List SOBlock), (consLast Gt B Bs).length = Bs.length + 1
  | _, [] => rfl
  | _, _ :: Bs => congrArg (· + 1) (consLast_length Gt _ Bs)

/-- Routing a relation variable of the enlarged prefix: it is either a
relation variable of the original prefix, or a variable of the extra block.
Note that this is a plain function – no dependent types – so a reading built
from it needs no arity cast. -/
def splitIdx (Gt : SOBlock) : ∀ (B : SOBlock) (Bs : List SOBlock),
    (mergeBlocks (consLast Gt B Bs)).ι → (mergeBlocks (B :: Bs)).ι ⊕ Gt.ι
  | _, [], Sum.inl (Sum.inl i) => Sum.inl (Sum.inl i)
  | _, [], Sum.inl (Sum.inr j) => Sum.inr j
  | _, [], Sum.inr e => Empty.elim (e : Empty)
  | _, _ :: _, Sum.inl i => Sum.inl (Sum.inl i)
  | _, B' :: Bs, Sum.inr i =>
      Sum.elim (fun x => Sum.inl (Sum.inr x)) Sum.inr (splitIdx Gt B' Bs i)

/-- Arities of the enlarged prefix are bounded by the bounds of its two
parts. -/
private theorem arity_consLast_le (Gt : SOBlock) {D : ℕ} (hGt : ∀ j : Gt.ι, Gt.arity j ≤ D) :
    ∀ (B : SOBlock) (Bs : List SOBlock),
      (∀ i : (mergeBlocks (B :: Bs)).ι, (mergeBlocks (B :: Bs)).arity i ≤ D) →
      ∀ i : (mergeBlocks (consLast Gt B Bs)).ι,
        (mergeBlocks (consLast Gt B Bs)).arity i ≤ D := by
  intro B Bs
  induction Bs generalizing B with
  | nil =>
    intro hM i
    rcases i with i | e
    · rcases i with i | j
      · exact hM (Sum.inl i)
      · exact hGt j
    · exact Empty.elim (e : Empty)
  | cons B' Bs ih =>
    intro hM i
    rcases i with i | i
    · exact hM (Sum.inl i)
    · exact ih B' (fun i' => hM (Sum.inr i')) i

/-- Splitting and reassembling an assignment of a merged pair of blocks. -/
theorem consAssign_split {A : Type} {B C : SOBlock}
    (ρ : (SOBlock.cons B C).Assignment A) :
    consAssign (fun i => ρ (Sum.inl i)) (fun j => ρ (Sum.inr j)) = ρ := by
  funext i
  rcases i with i | i <;> rfl

/-- The original part of an assignment of the enlarged prefix. -/
def atomPart (Gt : SOBlock) {A : Type} : ∀ (B : SOBlock) (Bs : List SOBlock),
    (mergeBlocks (consLast Gt B Bs)).Assignment A → (mergeBlocks (B :: Bs)).Assignment A
  | _, [], μ => consAssign (fun i => μ (Sum.inl (Sum.inl i))) (nilAssign A)
  | _, B' :: Bs, μ =>
      consAssign (fun i => μ (Sum.inl i)) (atomPart Gt B' Bs fun i => μ (Sum.inr i))

/-- The gate part of an assignment of the enlarged prefix. -/
def gatePart (Gt : SOBlock) {A : Type} : ∀ (B : SOBlock) (Bs : List SOBlock),
    (mergeBlocks (consLast Gt B Bs)).Assignment A → Gt.Assignment A
  | _, [], μ => fun j => μ (Sum.inl (Sum.inr j))
  | _, B' :: Bs, μ => gatePart Gt B' Bs fun i => μ (Sum.inr i)

/-- Reassembling a singleton merged assignment. -/
private theorem consAssign_nil {A : Type} {B : SOBlock} (μ : (mergeBlocks [B]).Assignment A) :
    consAssign (fun i => μ (Sum.inl i)) (nilAssign A) = μ := by
  funext i
  rcases i with i | i
  · rfl
  · exact Empty.elim (i : Empty)

private theorem atomPart_combineLast (Gt : SOBlock) {A : Type} :
    ∀ (B : SOBlock) (Bs : List SOBlock) (μ : (mergeBlocks (B :: Bs)).Assignment A)
      (g : Gt.Assignment A), atomPart Gt B Bs (combineLast Gt B Bs μ g) = μ := by
  intro B Bs
  induction Bs generalizing B with
  | nil => intro μ g; exact consAssign_nil μ
  | cons B' Bs ih =>
    intro μ g
    change consAssign (fun i => μ (Sum.inl i))
      (atomPart Gt B' Bs (combineLast Gt B' Bs (fun i => μ (Sum.inr i)) g)) = μ
    rw [ih B' (fun i => μ (Sum.inr i)) g]
    exact consAssign_split μ

private theorem gatePart_combineLast (Gt : SOBlock) {A : Type} :
    ∀ (B : SOBlock) (Bs : List SOBlock) (μ : (mergeBlocks (B :: Bs)).Assignment A)
      (g : Gt.Assignment A), gatePart Gt B Bs (combineLast Gt B Bs μ g) = g := by
  intro B Bs
  induction Bs generalizing B with
  | nil => intro μ g; rfl
  | cons B' Bs ih => intro μ g; exact ih B' (fun i => μ (Sum.inr i)) g

private theorem quantB_cons {A : Type} {B C : SOBlock} (pol : Bool)
    (P : (SOBlock.cons B C).Assignment A → Prop) :
    quantB pol (fun ρ : (SOBlock.cons B C).Assignment A => P ρ) ↔
      quantB pol fun ρ : B.Assignment A =>
        quantB pol fun g : C.Assignment A => P (consAssign ρ g) := by
  cases pol with
  | true =>
    constructor
    · rintro ⟨ρ, hρ⟩
      exact ⟨fun i => ρ (Sum.inl i), fun j => ρ (Sum.inr j), (consAssign_split ρ).symm ▸ hρ⟩
    · rintro ⟨ρ, g, h⟩
      exact ⟨consAssign ρ g, h⟩
  | false =>
    constructor
    · intro h ρ g
      exact h (consAssign ρ g)
    · intro h ρ
      have h2 : P (consAssign (fun i => ρ (Sum.inl i)) fun j => ρ (Sum.inr j)) :=
        h (fun i => ρ (Sum.inl i)) fun j => ρ (Sum.inr j)
      rwa [consAssign_split ρ] at h2

/-- **Enlarging the innermost block**: quantifying a prefix whose innermost
block has been enlarged by `Gt` is quantifying the original prefix, with an
extra quantifier over `Gt` – of the innermost polarity – inside. -/
private theorem altAssign_consLast (Gt : SOBlock) {A : Type} :
    ∀ (B : SOBlock) (Bs : List SOBlock)
      (G : (mergeBlocks (consLast Gt B Bs)).Assignment A → Prop) (pol : Bool),
      altAssign A (consLast Gt B Bs) G pol ↔
        altAssign A (B :: Bs)
          (fun μ => quantB (innerPol Bs.length pol)
            fun g : Gt.Assignment A => G (combineLast Gt B Bs μ g)) pol := by
  intro B Bs
  induction Bs generalizing B with
  | nil =>
    intro G pol
    cases pol with
    | true =>
      exact quantB_cons (B := B) (C := Gt) true fun ρ => G (consAssign ρ (nilAssign A))
    | false =>
      exact quantB_cons (B := B) (C := Gt) false fun ρ => G (consAssign ρ (nilAssign A))
  | cons B' Bs ih =>
    intro G pol
    have key : ∀ ρ : B.Assignment A,
        altAssign A (consLast Gt B' Bs) (fun μ => G (consAssign ρ μ)) (!pol) ↔
          altAssign A (B' :: Bs)
            (fun μ' => quantB (innerPol Bs.length (!pol))
              fun g => G (combineLast Gt B (B' :: Bs) (consAssign ρ μ') g)) (!pol) := by
      intro ρ
      exact ih B' _ (!pol)
    cases pol with
    | true => exact exists_congr fun ρ => key ρ
    | false => exact forall_congr' fun ρ => key ρ

/-! ### The converse transport

For *stating* that a problem is second-order definable one needs to go the
other way: a kernel written over the single merged block has to be turned into
a kernel over the iterated expansion. The morphisms below invert those above,
and give the same theorem read from right to left
(`DescriptiveComplexity.sorealize_unmerge`). -/

/-- The inverse of `DescriptiveComplexity.mergeStep`: splitting the merged block back
into the head block and the merged tail. -/
def unmergeStep (L : Language.{0, 0}) (B M : SOBlock) :
    L.sum (SOBlock.cons B M).lang →ᴸ (L.sum B.lang).sum M.lang where
  onFunction := fun {_} f =>
    match f with
    | Sum.inl f => Sum.inl (Sum.inl f)
    | Sum.inr f => isEmptyElim f
  onRelation := fun {_} r =>
    match r with
    | Sum.inl r => Sum.inl (Sum.inl r)
    | Sum.inr ⟨Sum.inl i, h⟩ => Sum.inl (Sum.inr ⟨i, h⟩)
    | Sum.inr ⟨Sum.inr i, h⟩ => Sum.inr ⟨i, h⟩

private theorem unmergeStep_isExpansionOn (L : Language.{0, 0}) {A : Type} (instL : L.Structure A)
    (B M : SOBlock) (ρ : B.Assignment A) (μ : M.Assignment A) :
    @LHom.IsExpansionOn _ _ (unmergeStep L B M) A
      (@sumStructure L (SOBlock.cons B M).lang A instL
        ((SOBlock.cons B M).structure (consAssign ρ μ)))
      (@sumStructure (L.sum B.lang) M.lang A
        (@sumStructure L B.lang A instL (B.structure ρ)) (M.structure μ)) := by
  let := instL
  let := B.structure ρ
  let := M.structure μ
  let := (SOBlock.cons B M).structure (consAssign ρ μ)
  refine ⟨?_, ?_⟩
  · intro n f x
    rcases f with f | f
    · rfl
    · exact isEmptyElim f
  · intro n r x
    rcases r with r | ⟨i, h⟩
    · rfl
    · rcases i with i | i
      · rfl
      · rfl

/-- Discarding the trivial block from an expansion. -/
def unmergeNil (L : Language.{0, 0}) : L.sum SOBlock.trivial.lang →ᴸ L where
  onFunction := fun {_} f =>
    match f with
    | Sum.inl f => f
    | Sum.inr f => isEmptyElim f
  onRelation := fun {_} r =>
    match r with
    | Sum.inl r => r
    | Sum.inr r => Empty.elim (r.1 : Empty)

private theorem unmergeNil_isExpansionOn (L : Language.{0, 0}) {A : Type} (instL : L.Structure A)
    (μ : SOBlock.trivial.Assignment A) :
    @LHom.IsExpansionOn _ _ (unmergeNil L) A
      (@sumStructure L SOBlock.trivial.lang A instL (SOBlock.trivial.structure μ)) instL := by
  let := instL
  let := SOBlock.trivial.structure μ
  refine ⟨?_, ?_⟩
  · intro n f x
    rcases f with f | f
    · rfl
    · exact isEmptyElim f
  · intro n r x
    rcases r with r | r
    · rfl
    · exact Empty.elim (r.1 : Empty)

/-- The morphism transporting a single-block kernel into the iterated block
expansion. -/
def unmergeHom : ∀ (Bs : List SOBlock) (L : Language.{0, 0}),
    L.sum (mergeBlocks Bs).lang →ᴸ soLang L Bs
  | [], L => unmergeNil L
  | B :: Bs, L => (unmergeHom Bs (L.sum B.lang)).comp (unmergeStep L B (mergeBlocks Bs))

private theorem unmergeHom_cons (B : SOBlock) (Bs : List SOBlock) (L : Language.{0, 0})
    (ψ : (L.sum (mergeBlocks (B :: Bs)).lang).Sentence) :
    (unmergeHom (B :: Bs) L).onSentence ψ =
      (unmergeHom Bs (L.sum B.lang)).onSentence
        ((unmergeStep L B (mergeBlocks Bs)).onSentence ψ) :=
  congrFun (LHom.comp_onBoundedFormula (unmergeHom Bs (L.sum B.lang))
    (unmergeStep L B (mergeBlocks Bs))) ψ

/-- **Merging a quantifier prefix, read backwards**: a kernel over the single
merged block, transported into the iterated expansion, is satisfied
alternately exactly when the merged assignment is quantified alternately. -/
theorem sorealize_unmerge :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (ψ : (L.sum (mergeBlocks Bs).lang).Sentence) (pol : Bool),
      @SORealize L A instL Bs ((unmergeHom Bs L).onSentence ψ) pol ↔
        altAssign A Bs (fun μ =>
          @Sentence.Realize (L.sum (mergeBlocks Bs).lang) A
            (@sumStructure L (mergeBlocks Bs).lang A instL ((mergeBlocks Bs).structure μ))
            ψ) pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL ψ pol
    let := instL
    let := SOBlock.trivial.structure (nilAssign A)
    have := unmergeNil_isExpansionOn L instL (nilAssign A)
    exact (unmergeNil L).realize_onSentence A ψ
  | cons B Bs ih =>
    intro L A instL ψ pol
    have key : ∀ (ρ : B.Assignment A) (μ : (mergeBlocks Bs).Assignment A),
        @Sentence.Realize ((L.sum B.lang).sum (mergeBlocks Bs).lang) A
            (@sumStructure (L.sum B.lang) (mergeBlocks Bs).lang A
              (@sumStructure L B.lang A instL (B.structure ρ))
              ((mergeBlocks Bs).structure μ))
            ((unmergeStep L B (mergeBlocks Bs)).onSentence ψ) ↔
          @Sentence.Realize (L.sum (mergeBlocks (B :: Bs)).lang) A
            (@sumStructure L (mergeBlocks (B :: Bs)).lang A instL
              ((mergeBlocks (B :: Bs)).structure (consAssign ρ μ)))
            ψ := by
      intro ρ μ
      let := instL
      let := B.structure ρ
      let := (mergeBlocks Bs).structure μ
      let := (SOBlock.cons B (mergeBlocks Bs)).structure (consAssign ρ μ)
      have := unmergeStep_isExpansionOn L instL B (mergeBlocks Bs) ρ μ
      exact (unmergeStep L B (mergeBlocks Bs)).realize_onSentence A ψ
    have hcons : ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((unmergeHom (B :: Bs) L).onSentence ψ) (!pol) ↔
          altAssign A Bs (fun μ =>
            @Sentence.Realize (L.sum (mergeBlocks (B :: Bs)).lang) A
              (@sumStructure L (mergeBlocks (B :: Bs)).lang A instL
                ((mergeBlocks (B :: Bs)).structure (consAssign ρ μ)))
              ψ) (!pol) := by
      intro ρ
      rw [unmergeHom_cons]
      refine (ih (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) _
        (!pol)).trans ?_
      exact altAssign_congr Bs _ _ (fun μ => key ρ μ) (!pol)
    cases pol with
    | true => exact exists_congr fun ρ => hcons ρ
    | false => exact forall_congr' fun ρ => hcons ρ

end DescriptiveComplexity
