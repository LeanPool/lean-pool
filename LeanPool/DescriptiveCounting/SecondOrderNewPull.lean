/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Relativize
public import LeanPool.DescriptiveCounting.RelComposition
public import LeanPool.DescriptiveCounting.SecondOrderPull
import all LeanPool.DescriptiveCounting.SecondOrderNew

/-!
# Pulling `∃SO[new]` definability back through an interpretation

Closure of definability in existential second-order logic with value invention
under first-order reductions (`DescriptiveComplexity.SigmaSONewDefinable.of_foReduction`),
the closure that makes RE a `DescriptiveComplexity.ComplexityClass`.

## The construction

Let `I` be the interpretation of a reduction `P ≤ᶠᵒ Q`, and let `Q` be defined
by a block `B` and a kernel `φ` read in the extended universe
`I.Map A ⊕ Fin m`. The extended universe of the *source* is `A ⊕ Fin m` – the
same number of invented values – and the point of the construction is that
the target's extended universe is **definable inside it**:

* a point of `I.Map A` is a tag `t` together with `dim` original elements;
* an invented value is an invented value.

Both are tagged tuples, so they are the universe of a *relativized*
interpretation `DescriptiveComplexity.newInterp` with tags `Tag ⊕ Unit` and
dimension `dim + 1`, whose domain formula asks, at tag `Sum.inl t`, that the
first `dim` coordinates be original, and at tag `Sum.inr ()`, that the last
coordinate be invented and the others copy it (a diagonal, so that each
invented value is *one* point). The spare coordinate of a `Sum.inl` point has
to be pinned to a single element, for which the block guesses a **canonical
element** (`DescriptiveComplexity.canonSym`), constrained to be unique by
`DescriptiveComplexity.canonGuard`; pinning it to a coordinate of the tuple
would not survive `dim = 0`, where `I.Map A` is a constant-size structure.

Everything else is machinery that already exists:

* the kernel is pulled back by the guarded pullback
  `DescriptiveComplexity.RelFOInterpretation.pullRel` of
  `DescriptiveComplexity.RelComposition`, which relativizes quantifiers to the
  definable universe and substitutes the defining formulas for atoms;
* the relation variables of `B` are pulled back exactly as in
  `DescriptiveComplexity.SecondOrderPull`, one `(k · (dim+1))`-ary variable per
  tuple of tags (`DescriptiveComplexity.SOBlock.pull`). Their assignments
  transfer in the *flipped* direction a definable universe forces:
  `DescriptiveComplexity.targetAssign` reads a guessed assignment back on the
  target's universe, `DescriptiveComplexity.sourceAssign` extends an assignment
  of the target's block by junk off the interpreted points, and the composite
  `targetAssign ∘ sourceAssign` is the identity, not merely the identity on the
  interpreted points
  (`DescriptiveComplexity.targetAssign_sourceAssign`) – which is all an
  *existential* block needs;
* the interpretation's own defining formulas quantify over `A`, so they are
  read in `A ⊕ Fin m` relativized to the original elements
  (`DescriptiveComplexity.relOld` of `DescriptiveComplexity.Relativize`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The pulled block -/

section Block

variable (Tag : Type) [Finite Tag] (dim : ℕ) (B : SOBlock)

/-- The block guessed on the source side: a canonical element (used to pin the
spare coordinate of an interpreted point) together with the pullback of the
target's block through the interpretation below. -/
abbrev newBlock : SOBlock where
  ι := Unit ⊕ (B.pull (Tag ⊕ Unit) (dim + 1)).ι
  arity := Sum.elim (fun _ => 1) (B.pull (Tag ⊕ Unit) (dim + 1)).arity

/-- The canonical-element variable of the guessed block. -/
def canonSym : (newBlock Tag dim B).lang.Relations 1 :=
  ⟨Sum.inl (), rfl⟩

/-- The pulled relation variable of the target's block selected by a tuple of
tags. -/
def newPullSym {k : ℕ} (r : B.lang.Relations k) (τ : Fin k → Tag ⊕ Unit) :
    (newBlock Tag dim B).lang.Relations (B.arity r.1 * (dim + 1)) :=
  ⟨Sum.inr ⟨r.1, fun j => τ (Fin.cast r.2 j)⟩, rfl⟩

end Block

section Parts

variable {Tag : Type} [Finite Tag] {dim : ℕ} {B : SOBlock} {M : Type}

/-- The canonical-element part of a guessed assignment. -/
abbrev canonPart (ρ : (newBlock Tag dim B).Assignment M) : M → Prop :=
  fun c => ρ (Sum.inl ()) ![c]

/-- The pulled-block part of a guessed assignment: an assignment of the block
pulled back through the interpretation below. -/
abbrev pullPart (ρ : (newBlock Tag dim B).Assignment M) :
    (B.pull (Tag ⊕ Unit) (dim + 1)).Assignment M :=
  fun p => ρ (Sum.inr p)

/-- A guessed assignment, from its two parts. -/
def joinParts (c : (Fin 1 → M) → Prop) (σ : (B.pull (Tag ⊕ Unit) (dim + 1)).Assignment M) :
    (newBlock Tag dim B).Assignment M :=
  fun i => match i with
    | Sum.inl _ => c
    | Sum.inr p => σ p

end Parts

/-! ### The two vocabularies -/

/-- The vocabulary the pulled-back kernel is written in: the source
vocabulary, the marker `old`, and the guessed relation variables. -/
abbrev newHost (L₁ : Language.{0, 0}) (Tag : Type) [Finite Tag] (dim : ℕ) (B : SOBlock) :
    Language :=
  (newLang L₁).sum (newBlock Tag dim B).lang

/-- The vocabulary the target's kernel is written in. -/
abbrev newTarget (L₂ : Language.{0, 0}) (B : SOBlock) : Language :=
  (newLang L₂).sum B.lang

/-- A symbol of the target vocabulary, as a symbol of the extended one. -/
abbrev tgtBaseSym (L₂ : Language.{0, 0}) (B : SOBlock) {k : ℕ} (R : L₂.Relations k) :
    (newTarget L₂ B).Relations k :=
  Sum.inl (Sum.inl R)

/-- The marker `old` of the target's extended vocabulary. -/
abbrev tgtOldSym (L₂ : Language.{0, 0}) (B : SOBlock) : (newTarget L₂ B).Relations 1 :=
  Sum.inl (Sum.inr Language.oldSym)

/-- A relation variable of the target's block, as a symbol. -/
abbrev tgtBlockSym (L₂ : Language.{0, 0}) (B : SOBlock) {k : ℕ} (r : B.lang.Relations k) :
    (newTarget L₂ B).Relations k :=
  Sum.inr r

/-! ### The interpretation of the target's extended universe -/

section Interp

variable (L₁ : Language.{0, 0}) {L₂ : Language.{0, 0}} (Tag : Type) [Finite Tag]
variable (dim : ℕ) (B : SOBlock)

/-- The marker `old`, as a symbol of the host vocabulary. -/
abbrev oldHostSym : (newHost L₁ Tag dim B).Relations 1 :=
  Sum.inl (Sum.inr Language.oldSym)

/-- The canonical-element variable, as a symbol of the host vocabulary. -/
abbrev canonHostSym : (newHost L₁ Tag dim B).Relations 1 :=
  Sum.inr (canonSym Tag dim B)

/-- A pulled relation variable, as a symbol of the host vocabulary. -/
abbrev blockHostSym {k : ℕ} (r : B.lang.Relations k) (τ : Fin k → Tag ⊕ Unit) :
    (newHost L₁ Tag dim B).Relations (B.arity r.1 * (dim + 1)) :=
  Sum.inr (newPullSym Tag dim B r τ)

/-- `old x`, as a formula over the host vocabulary. -/
def oldHostF {α : Type} (x : α) : (newHost L₁ Tag dim B).Formula α :=
  Relations.formula₁ (oldHostSym L₁ Tag dim B) (Term.var x)

/-- `C x`, the canonical-element variable, as a formula over the host
vocabulary. -/
def canonHostF {α : Type} (x : α) : (newHost L₁ Tag dim B).Formula α :=
  Relations.formula₁ (canonHostSym L₁ Tag dim B) (Term.var x)

/-- The domain formula: a `Sum.inl t` point is a tuple of original elements
with its spare coordinate pinned to the canonical element; a `Sum.inr ()`
point is a diagonal tuple of one invented value. -/
noncomputable def newDom : Tag ⊕ Unit → (newHost L₁ Tag dim B).Formula (Fin (dim + 1))
  | Sum.inl _ =>
      (Formula.iInf fun j : Fin dim => oldHostF L₁ Tag dim B (Fin.castSucc j)) ⊓
        canonHostF L₁ Tag dim B (Fin.last dim)
  | Sum.inr _ =>
      (∼(oldHostF L₁ Tag dim B (Fin.last dim))) ⊓
        Formula.iInf fun j : Fin dim =>
          Term.equal (Term.var (Fin.castSucc j)) (Term.var (Fin.last dim))

open Classical in
/-- The defining formulas: a symbol of the target vocabulary holds of
interpreted points exactly when the reduction's own defining formula holds of
their coordinates (read among the original elements), it never holds of an
invented point; `old` marks the interpreted points; a relation variable of the
target's block is read off the pulled variable selected by the tags. -/
noncomputable def newRelF (I : FOInterpretation L₁ L₂ Tag dim) :
    ∀ {k : ℕ}, (newTarget L₂ B).Relations k → (Fin k → Tag ⊕ Unit) →
      (newHost L₁ Tag dim B).Formula (Fin k × Fin (dim + 1))
  | k, Sum.inl (Sum.inl R), τ =>
      if h : ∃ t : Fin k → Tag, ∀ i, τ i = Sum.inl (t i) then
        (LHom.sumInl.onFormula (relOld (I.relFormula R h.choose))).relabel
          fun p => (p.1, Fin.castSucc p.2)
      else ⊥
  | _, Sum.inl (Sum.inr r), τ =>
      match r, τ with
      | .old, τ => if (τ 0).isLeft then ⊤ else ⊥
  | _, Sum.inr r, τ =>
      Relations.formula (blockHostSym L₁ Tag dim B r τ) fun mm =>
        Term.var (Fin.cast r.2 (finProdFinEquiv.symm mm).1, (finProdFinEquiv.symm mm).2)

/-- **The interpretation of the target's extended universe in the source's**:
tagged `(dim+1)`-tuples, an interpreted point per tag of the reduction and an
invented value per diagonal. -/
noncomputable def newInterp (I : FOInterpretation L₁ L₂ Tag dim) :
    RelFOInterpretation (newHost L₁ Tag dim B) (newTarget L₂ B) (Tag ⊕ Unit) (dim + 1) where
  relFormula := newRelF L₁ Tag dim B I
  domFormula := newDom L₁ Tag dim B

/-- The guard: the canonical-element variable holds of exactly one element. -/
private noncomputable def canonGuard : (newHost L₁ Tag dim B).Sentence :=
  (canonHostF L₁ Tag dim B (Sum.inr 0)).iExsUnique (Fin 1)

end Interp

/-! ### Realization in the host structure -/

section Realize

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] {Tag : Type} [Finite Tag] {dim : ℕ}
variable {B : SOBlock} (A : Type) [L₁.Structure A] (n : ℕ)
variable (ρ : (newBlock Tag dim B).Assignment (A ⊕ Fin n))

/-- The host structure: the extended structure of the instance, expanded by
the guessed relation variables. -/
@[instance_reducible]
noncomputable def hostStruc : (newHost L₁ Tag dim B).Structure (A ⊕ Fin n) :=
  @sumStructure (newLang L₁) (newBlock Tag dim B).lang (A ⊕ Fin n) (extStructure L₁ A n)
    ((newBlock Tag dim B).structure ρ)

variable {A n ρ}

private theorem realize_oldHostF {α : Type} (x : α) (v : α → A ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (oldHostF L₁ Tag dim B x).Realize v ↔ IsOld (v x) := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [oldHostF, Formula.realize_rel₁]
  exact Iff.rfl

private theorem realize_canonHostF {α : Type} (x : α) (v : α → A ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (canonHostF L₁ Tag dim B x).Realize v ↔ canonPart ρ (v x) := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [canonHostF, Formula.realize_rel₁]
  exact Iff.rfl

private theorem realize_newDom_inl (t : Tag) (w : Fin (dim + 1) → A ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (newDom L₁ Tag dim B (Sum.inl t)).Realize w ↔
      (∀ j : Fin dim, IsOld (w (Fin.castSucc j))) ∧ canonPart ρ (w (Fin.last dim)) := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [newDom, Formula.realize_inf, Formula.realize_iInf]
  exact and_congr (forall_congr' fun j => realize_oldHostF _ w) (realize_canonHostF _ w)

private theorem realize_newDom_inr (u : Unit) (w : Fin (dim + 1) → A ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (newDom L₁ Tag dim B (Sum.inr u)).Realize w ↔
      ¬IsOld (w (Fin.last dim)) ∧ ∀ j : Fin dim, w (Fin.castSucc j) = w (Fin.last dim) := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [newDom, Formula.realize_inf, Formula.realize_not, Formula.realize_iInf]
  refine and_congr (not_congr (realize_oldHostF _ w)) (forall_congr' fun j => ?_)
  rw [Formula.realize_equal]
  exact Iff.rfl

private theorem realize_canonGuard :
    letI := hostStruc (L₁ := L₁) A n ρ
    (A ⊕ Fin n) ⊨ canonGuard L₁ Tag dim B ↔ ∃! c : A ⊕ Fin n, canonPart ρ c := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [canonGuard, Sentence.Realize, Formula.realize_iExsUnique]
  constructor
  · rintro ⟨i, hi, huniq⟩
    refine ⟨i 0, ?_, fun c hc => ?_⟩
    · exact (realize_canonHostF (L₁ := L₁) (B := B) (Sum.inr 0) (Sum.elim default i)).mp hi
    · have := huniq (fun _ => c)
        ((realize_canonHostF (L₁ := L₁) (B := B) (Sum.inr 0) (Sum.elim default fun _ => c)).mpr hc)
      exact congrFun this 0
  · rintro ⟨c, hc, huniq⟩
    refine ⟨fun _ => c, ?_, fun i hi => ?_⟩
    · exact (realize_canonHostF (L₁ := L₁) (B := B) (Sum.inr 0)
        (Sum.elim default fun _ => c)).mpr hc
    · funext j
      have hc0 := huniq (i 0)
        ((realize_canonHostF (L₁ := L₁) (B := B) (Sum.inr 0) (Sum.elim default i)).mp hi)
      rw [Subsingleton.elim j 0]
      exact hc0

variable (I : FOInterpretation L₁ L₂ Tag dim)

/-- A base symbol at a tuple of interpreted tags: the reduction's own defining
formula, read among the original elements. -/
private theorem realize_newRelF_base {k : ℕ} (R : L₂.Relations k) (t : Fin k → Tag)
    (a : Fin k → Fin dim → A) (w : Fin k × Fin (dim + 1) → A ⊕ Fin n)
    (hw : ∀ (i : Fin k) (j : Fin dim), w (i, Fin.castSucc j) = Sum.inl (a i j)) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (newRelF L₁ Tag dim B I (tgtBaseSym L₂ B R) (fun i => Sum.inl (t i))).Realize w ↔
      (I.relFormula R t).Realize fun p => a p.1 p.2 := by
  let := hostStruc (L₁ := L₁) A n ρ
  have hex : ∃ t' : Fin k → Tag, ∀ i, (Sum.inl (t i) : Tag ⊕ Unit) = Sum.inl (t' i) :=
    ⟨t, fun _ => rfl⟩
  rw [newRelF, dite_eq_left hex]
  have hch : hex.choose = t := funext fun i => (Sum.inl_injective (hex.choose_spec i)).symm
  rw [hch, Formula.realize_relabel, LHom.realize_onFormula]
  have hval : (w ∘ fun p : Fin k × Fin dim => (p.1, Fin.castSucc p.2)) =
      fun p : Fin k × Fin dim => Sum.inl (a p.1 p.2) := by
    funext p
    exact hw p.1 p.2
  rw [hval]
  exact realize_relOld (I.relFormula R t) fun p => a p.1 p.2

omit [L₁.IsRelational] in
/-- A base symbol never holds of an invented point. -/
private theorem newRelF_base_eq_bot {k : ℕ} (R : L₂.Relations k) (τ : Fin k → Tag ⊕ Unit)
    (h : ¬∃ t : Fin k → Tag, ∀ i, τ i = Sum.inl (t i)) :
    newRelF L₁ Tag dim B I (tgtBaseSym L₂ B R) τ = ⊥ := by
  rw [newRelF, dite_eq_right h]

/-- The marker `old` holds exactly of the interpreted points. -/
private theorem realize_newRelF_old
    (τ : Fin 1 → Tag ⊕ Unit) (w : Fin 1 × Fin (dim + 1) → A ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (newRelF L₁ Tag dim B I (tgtOldSym L₂ B) τ).Realize w ↔ (τ 0).isLeft = true := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [newRelF]
  by_cases h : (τ 0).isLeft = true
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    simp [h]

/-- A relation variable of the target's block is read off the pulled variable
selected by the tags. -/
private theorem realize_newRelF_block {k : ℕ} (r : B.lang.Relations k) (τ : Fin k → Tag ⊕ Unit)
    (w : Fin k × Fin (dim + 1) → A ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (newRelF L₁ Tag dim B I (tgtBlockSym L₂ B r) τ).Realize w ↔
      pullPart ρ ⟨r.1, fun j => τ (Fin.cast r.2 j)⟩
        (fun mm => w (Fin.cast r.2 (finProdFinEquiv.symm mm).1,
          (finProdFinEquiv.symm mm).2)) := by
  let := hostStruc (L₁ := L₁) A n ρ
  rw [newRelF, Formula.realize_rel]
  exact Iff.rfl

end Realize

/-! ### The interpreted universe *is* the target's extended universe -/

section Universe

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] {Tag : Type}
variable [Finite Tag] {dim : ℕ}
variable {B : SOBlock} {A : Type} [L₁.Structure A] {n : ℕ}
variable (I : FOInterpretation L₁ L₂ Tag dim) (c₀ : A ⊕ Fin n)

/-- The tagged tuple representing a point of the target's extended universe:
an interpreted point becomes its tag together with its coordinates, the spare
coordinate pinned to `c₀`; an invented value becomes a diagonal tuple. -/
def newPoint : (I.Map A) ⊕ Fin n → (Tag ⊕ Unit) × (Fin (dim + 1) → A ⊕ Fin n)
  | Sum.inl p => (Sum.inl p.1, Fin.snoc (fun j => Sum.inl (p.2 j)) c₀)
  | Sum.inr i => (Sum.inr (), fun _ => Sum.inr i)

omit [L₁.IsRelational] [L₂.IsRelational] [Finite Tag] [L₁.Structure A] in
@[simp]
theorem newPoint_inl (p : I.Map A) :
    newPoint I c₀ (Sum.inl p) = (Sum.inl p.1, Fin.snoc (fun j => Sum.inl (p.2 j)) c₀) := rfl

omit [L₁.IsRelational] [L₂.IsRelational] [Finite Tag] [L₁.Structure A] in
@[simp]
theorem newPoint_inr (i : Fin n) :
    newPoint I c₀ (Sum.inr i) = (Sum.inr (), fun _ => Sum.inr i) := rfl

omit [L₁.IsRelational] [L₂.IsRelational] [Finite Tag] [L₁.Structure A] in
theorem newPoint_injective : Function.Injective (newPoint I c₀) := by
  rintro (p | i) (q | j) h
  · have htag : (Sum.inl p.1 : Tag ⊕ Unit) = Sum.inl q.1 := congrArg Prod.fst h
    have hco := congrArg Prod.snd h
    refine congrArg Sum.inl (Prod.ext_iff.mpr ⟨Sum.inl_injective htag, funext fun j => ?_⟩)
    have hj := congrFun hco (Fin.castSucc j)
    simp only [newPoint_inl, Fin.snoc_castSucc] at hj
    exact Sum.inl_injective hj
  · exact absurd (congrArg Prod.fst h) (by simp)
  · exact absurd (congrArg Prod.fst h) (by simp)
  · have := congrFun (congrArg Prod.snd h) (Fin.last dim)
    exact congrArg Sum.inr (Sum.inr_injective this)

variable {I c₀} (ρ : (newBlock Tag dim B).Assignment (A ⊕ Fin n))

omit [L₂.IsRelational] in
theorem newPoint_mem_dom (hc₀ : canonPart ρ c₀) (x : (I.Map A) ⊕ Fin n) :
    letI := hostStruc (L₁ := L₁) A n ρ
    (newDom L₁ Tag dim B (newPoint I c₀ x).1).Realize (newPoint I c₀ x).2 := by
  let := hostStruc (L₁ := L₁) A n ρ
  cases x with
  | inl p =>
    refine (realize_newDom_inl (L₁ := L₁) (B := B) p.1 _).mpr ⟨fun j => ?_, ?_⟩
    · simp only [newPoint_inl, Fin.snoc_castSucc]
      exact isOld_inl _
    · simp only [newPoint_inl, Fin.snoc_last]
      exact hc₀
  | inr i =>
    exact (realize_newDom_inr (L₁ := L₁) (B := B) () _).mpr ⟨not_isOld_inr i, fun _ => rfl⟩

omit [L₂.IsRelational] in
/-- Every point of the interpreted universe is the image of a point of the
target's extended universe: an interpreted tag carries a tuple of original
elements, an invented tag a single invented value. -/
private theorem newPoint_surjective (hc : ∀ y : A ⊕ Fin n, canonPart ρ y ↔ y = c₀)
    (z : (Tag ⊕ Unit) × (Fin (dim + 1) → A ⊕ Fin n))
    (hz : letI := hostStruc (L₁ := L₁) A n ρ
      (newDom L₁ Tag dim B z.1).Realize z.2) :
    ∃ x : (I.Map A) ⊕ Fin n, newPoint I c₀ x = z := by
  let := hostStruc (L₁ := L₁) A n ρ
  obtain ⟨tag, w⟩ := z
  cases tag with
  | inl t =>
    obtain ⟨hold, hcan⟩ := (realize_newDom_inl (L₁ := L₁) (B := B) t w).mp hz
    choose a ha using fun j => isOld_iff.mp (hold j)
    refine ⟨Sum.inl ((t, a) : I.Map A), ?_⟩
    change ((Sum.inl t, Fin.snoc (fun j => Sum.inl (a j)) c₀) :
      (Tag ⊕ Unit) × (Fin (dim + 1) → A ⊕ Fin n)) = (Sum.inl t, w)
    refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [Fin.snoc_last]
      exact ((hc (w (Fin.last dim))).mp hcan).symm
    · simp only [Fin.snoc_castSucc]
      exact (ha j').symm
  | inr u =>
    obtain ⟨hnew, hdiag⟩ := (realize_newDom_inr (L₁ := L₁) (B := B) u w).mp hz
    obtain ⟨i, hi⟩ : ∃ i : Fin n, w (Fin.last dim) = Sum.inr i := by
      cases hw : w (Fin.last dim) with
      | inl a => exact absurd (hw ▸ isOld_inl a) hnew
      | inr i => exact ⟨i, rfl⟩
    refine ⟨Sum.inr i, ?_⟩
    change ((Sum.inr (), fun _ => Sum.inr i) :
      (Tag ⊕ Unit) × (Fin (dim + 1) → A ⊕ Fin n)) = (Sum.inr u, w)
    refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · exact hi.symm
    · exact ((hdiag j').trans hi).symm

omit [L₁.IsRelational] [L₂.IsRelational] [Finite Tag] [L₁.Structure A] in
theorem isLeft_newPoint (x : (I.Map A) ⊕ Fin n) :
    (newPoint I c₀ x).1.isLeft = true ↔ IsOld x := by
  cases x <;> simp

end Universe

/-! ### Transfer of the kernel -/

section Transfer

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] {Tag : Type}
variable [Finite Tag] [Nonempty Tag]
variable {dim : ℕ} {B : SOBlock} {A : Type} [L₁.Structure A] [Nonempty A] {n : ℕ}

/-- The assignment of the target's block on the target's extended universe,
read off a guessed assignment on the source's: the pulled variable selected by
the tags of the arguments, at their coordinates. -/
def targetAssign (I : FOInterpretation L₁ L₂ Tag dim) (c₀ : A ⊕ Fin n)
    (ρ : (newBlock Tag dim B).Assignment (A ⊕ Fin n)) : B.Assignment ((I.Map A) ⊕ Fin n) :=
  fun i y => pullPart ρ ⟨i, fun k => (newPoint I c₀ (y k)).1⟩
    fun mm => (newPoint I c₀ (y (finProdFinEquiv.symm mm).1)).2 (finProdFinEquiv.symm mm).2

/-- **The interpreted structure is the target's extended structure**: the map
sending a point of `I.Map A ⊕ Fin n` to its tagged tuple is an isomorphism
over the target's extended vocabulary, the target's block being interpreted by
`DescriptiveComplexity.targetAssign`. -/
private noncomputable def newTargetEquiv (I : FOInterpretation L₁ L₂ Tag dim) (c₀ : A ⊕ Fin n)
    (ρ : (newBlock Tag dim B).Assignment (A ⊕ Fin n))
    (hc : ∀ y : A ⊕ Fin n, canonPart ρ y ↔ y = c₀) :
    letI := hostStruc (L₁ := L₁) A n ρ
    haveI := I.map_nonempty A
    letI := B.structure (targetAssign I c₀ ρ)
    @Language.Equiv (newTarget L₂ B) ((I.Map A) ⊕ Fin n)
      ((newInterp L₁ Tag dim B I).MapRel (A ⊕ Fin n)) _ _ :=
  letI := hostStruc (L₁ := L₁) A n ρ
  haveI := I.map_nonempty A
  letI := B.structure (targetAssign I c₀ ρ)
  { toEquiv := Equiv.ofBijective
      (fun x => (⟨newPoint I c₀ x, newPoint_mem_dom ρ ((hc c₀).mpr rfl) x⟩ :
        (newInterp L₁ Tag dim B I).MapRel (A ⊕ Fin n)))
      ⟨fun x y h => newPoint_injective I c₀ (congrArg Subtype.val h),
        fun z => by
          obtain ⟨x, hx⟩ := newPoint_surjective ρ hc z.1 z.2
          exact ⟨x, Subtype.ext hx⟩⟩
    map_fun' := fun f _ => isEmptyElim f
    map_rel' := fun {k} R x => by
      rw [RelFOInterpretation.relMap_mapRel]
      cases R with
      | inl R' =>
        cases R' with
        | inl R =>
          by_cases hall : ∀ i, ∃ p : I.Map A, x i = Sum.inl p
          · choose y hy using hall
            have htags : (fun i => (newPoint I c₀ (x i)).1) = fun i => Sum.inl ((y i).1) := by
              funext i
              rw [hy i]
              rfl
            have hcoords : ∀ (i : Fin k) (j : Fin dim),
                (fun p : Fin k × Fin (dim + 1) => (newPoint I c₀ (x p.1)).2 p.2)
                  (i, Fin.castSucc j) = Sum.inl ((y i).2 j) := by
              intro i j
              simp only [hy i, newPoint_inl, Fin.snoc_castSucc]
            change ((newInterp L₁ Tag dim B I).relFormula (tgtBaseSym L₂ B R)
              (fun i => (newPoint I c₀ (x i)).1)).Realize
                (fun p => (newPoint I c₀ (x p.1)).2 p.2) ↔ _
            rw [show (newInterp L₁ Tag dim B I).relFormula = newRelF L₁ Tag dim B I from rfl,
              htags, realize_newRelF_base (ρ := ρ) I R (fun i => (y i).1)
                (fun i j => (y i).2 j) _ hcoords]
            refine Iff.trans ?_ (relMap_ext_iff (L := L₂) (A := I.Map A) (m := n) R x).symm
            constructor
            · intro h
              exact ⟨y, hy, h⟩
            · rintro ⟨y', hy', h⟩
              have hyy : y = y' := funext fun i => Sum.inl_injective ((hy i).symm.trans (hy' i))
              rw [hyy]
              exact h
          · obtain ⟨i₀, hi₀⟩ := not_forall.mp hall
            have hne : ¬∃ t : Fin k → Tag, ∀ i, (newPoint I c₀ (x i)).1 = Sum.inl (t i) := by
              rintro ⟨t, ht⟩
              cases hx : x i₀ with
              | inl p => exact hi₀ ⟨p, hx⟩
              | inr i =>
                have hti := ht i₀
                rw [hx] at hti
                simp at hti
            change ((newInterp L₁ Tag dim B I).relFormula (tgtBaseSym L₂ B R)
              (fun i => (newPoint I c₀ (x i)).1)).Realize
                (fun p => (newPoint I c₀ (x p.1)).2 p.2) ↔ _
            rw [show (newInterp L₁ Tag dim B I).relFormula = newRelF L₁ Tag dim B I from rfl,
              newRelF_base_eq_bot I R _ hne]
            refine Iff.trans ?_ (relMap_ext_iff (L := L₂) (A := I.Map A) (m := n) R x).symm
            simp only [Formula.realize_bot, false_iff]
            rintro ⟨y', hy', -⟩
            cases hx : x i₀ with
            | inl p => exact hi₀ ⟨p, hx⟩
            | inr i =>
              have hyi := hy' i₀
              rw [hx] at hyi
              simp at hyi
        | inr R =>
          cases R with
          | old =>
            change ((newInterp L₁ Tag dim B I).relFormula (tgtOldSym L₂ B)
              (fun i => (newPoint I c₀ (x i)).1)).Realize
                (fun p => (newPoint I c₀ (x p.1)).2 p.2) ↔ _
            rw [show (newInterp L₁ Tag dim B I).relFormula = newRelF L₁ Tag dim B I from rfl,
              realize_newRelF_old (ρ := ρ) I _ _]
            refine Iff.trans (isLeft_newPoint (I := I) (c₀ := c₀) (x 0)) ?_
            exact (relMap_ext_old (L := L₂) (A := I.Map A) (m := n) x).symm
      | inr r =>
        change ((newInterp L₁ Tag dim B I).relFormula (tgtBlockSym L₂ B r)
          (fun i => (newPoint I c₀ (x i)).1)).Realize
            (fun p => (newPoint I c₀ (x p.1)).2 p.2) ↔ _
        rw [show (newInterp L₁ Tag dim B I).relFormula = newRelF L₁ Tag dim B I from rfl,
          realize_newRelF_block (ρ := ρ) I r _ _]
        exact Iff.rfl }

omit [Nonempty Tag] [Nonempty A] in
/-- Sentence transfer: what the target's kernel says in the target's extended
universe, it says in the interpreted universe. -/
private theorem realize_transfer (I : FOInterpretation L₁ L₂ Tag dim) (c₀ : A ⊕ Fin n)
    (ρ : (newBlock Tag dim B).Assignment (A ⊕ Fin n))
    (hc : ∀ y : A ⊕ Fin n, canonPart ρ y ↔ y = c₀)
    (ρT : B.Assignment ((I.Map A) ⊕ Fin n)) (hT : targetAssign I c₀ ρ = ρT)
    (φ : (newTarget L₂ B).Sentence) :
    letI := hostStruc (L₁ := L₁) A n ρ
    ((@Sentence.Realize (newTarget L₂ B) ((I.Map A) ⊕ Fin n)
        (@sumStructure (newLang L₂) B.lang ((I.Map A) ⊕ Fin n) (extStructure L₂ (I.Map A) n)
          (B.structure ρT)) φ) ↔
      ((newInterp L₁ Tag dim B I).MapRel (A ⊕ Fin n) ⊨ φ)) := by
  let := hostStruc (L₁ := L₁) A n ρ
  subst hT
  let := B.structure (targetAssign I c₀ ρ)
  exact StrongHomClass.realize_sentence (newTargetEquiv I c₀ ρ hc) φ

end Transfer

/-! ### The guarded pullback of a sentence -/

namespace RelFOInterpretation

variable {L₃ L₄ : Language.{0, 0}} {TagJ : Type} {dJ : ℕ}
variable (J : RelFOInterpretation L₃ L₄ TagJ dJ) [L₄.IsRelational] [Finite TagJ]

/-- The guarded pullback of a sentence through a relativized interpretation:
an `L₃`-sentence that holds in `A` exactly when the original sentence holds in
the definable universe `J.MapRel A` (the relativized counterpart of
`DescriptiveComplexity.FOInterpretation.pullSentence`). -/
noncomputable def pullRelSentence (φ : L₄.Sentence) : L₃.Sentence :=
  (J.pullRel (φ : L₄.BoundedFormula Empty 0) (isEmptyElim : (Empty ⊕ Fin 0) → TagJ)).relabel
    fun p => (isEmptyElim p.1 : Empty)

private theorem realize_pullRelSentence (φ : L₄.Sentence) (A : Type) [L₃.Structure A] :
    A ⊨ J.pullRelSentence φ ↔ (J.MapRel A) ⊨ φ := by
  have h1 : A ⊨ J.pullRelSentence φ ↔
      (J.pullRel (φ : L₄.BoundedFormula Empty 0)
          (isEmptyElim : (Empty ⊕ Fin 0) → TagJ)).Realize
        ((default : Empty → A) ∘ fun p : (Empty ⊕ Fin 0) × Fin dJ => (isEmptyElim p.1 : Empty)) :=
    Formula.realize_relabel
  rw [h1, J.realize_pullRel (φ : L₄.BoundedFormula Empty 0) isEmptyElim _
    (fun b => isEmptyElim b)]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := J.MapRel A) (φ : L₄.BoundedFormula Empty 0) a b)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

end RelFOInterpretation

/-! ### Reproducing an assignment of the target's block -/

section Source

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] {Tag : Type}
variable [Finite Tag] [Nonempty Tag]
variable {dim : ℕ} {B : SOBlock} {A : Type} [L₁.Structure A] [Nonempty A] {n : ℕ}

/-- The pulled-block assignment reproducing a given assignment of the target's
block: a pulled variable holds of a tuple exactly when that tuple is the image
of a tuple of the target's universe that the assignment relates. -/
def sourceAssign (I : FOInterpretation L₁ L₂ Tag dim) (c₀ : A ⊕ Fin n)
    (ρT : B.Assignment ((I.Map A) ⊕ Fin n)) :
    (B.pull (Tag ⊕ Unit) (dim + 1)).Assignment (A ⊕ Fin n) :=
  fun p v => ∃ y : Fin (B.arity p.1) → (I.Map A) ⊕ Fin n,
    (∀ k, newPoint I c₀ (y k) = (p.2 k, fun j => v (finProdFinEquiv (k, j)))) ∧ ρT p.1 y

omit [L₁.IsRelational] [L₂.IsRelational] [Nonempty Tag] [L₁.Structure A] [Nonempty A] in
/-- Reading the reproduced assignment back gives the original one: the two
transfers compose to the identity in the direction a definable universe
allows. -/
theorem targetAssign_sourceAssign (I : FOInterpretation L₁ L₂ Tag dim) (c₀ : A ⊕ Fin n)
    (ρT : B.Assignment ((I.Map A) ⊕ Fin n)) :
    targetAssign I c₀ (joinParts (fun z => z 0 = c₀) (sourceAssign I c₀ ρT)) = ρT := by
  funext i y
  have key : ∀ k : Fin (B.arity i),
      (((newPoint I c₀ (y k)).1,
          fun j => (newPoint I c₀ (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).2
            (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2) :
        (Tag ⊕ Unit) × (Fin (dim + 1) → A ⊕ Fin n)) = newPoint I c₀ (y k) := by
    intro k
    refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
    simp only [Equiv.symm_apply_apply]
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨y', hy', hρ⟩ := h
    have hyy : y' = y := funext fun k => newPoint_injective I c₀ ((hy' k).trans (key k))
    exact hyy ▸ hρ
  · exact ⟨y, fun k => (key k).symm, h⟩

end Source

/-! ### The closure theorem -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]

/-- **Definability in `∃SO[new]` transfers through an interpretation**: with
the *same* number of invented values, the target's kernel holds in the
target's extended universe exactly when its guarded pullback holds in the
source's. -/
private theorem sorealize_newPull {Tag : Type} [Finite Tag] [Nonempty Tag] {dim : ℕ}
    (I : FOInterpretation L₁ L₂ Tag dim) (B : SOBlock) (φ : (newTarget L₂ B).Sentence)
    (A : Type) [L₁.Structure A] [Nonempty A] (n : ℕ) :
    haveI := I.map_nonempty A
    SORealize (newLang L₂) ((I.Map A) ⊕ Fin n) [B] φ true ↔
      SORealize (newLang L₁) (A ⊕ Fin n) [newBlock Tag dim B]
        (canonGuard L₁ Tag dim B ⊓ (newInterp L₁ Tag dim B I).pullRelSentence φ) true := by
  have := I.map_nonempty A
  constructor
  · rintro ⟨ρT, hρT⟩
    have hc : ∀ y : A ⊕ Fin n,
        canonPart (joinParts (fun z => z 0 = (Sum.inl (Classical.arbitrary A) : A ⊕ Fin n))
          (sourceAssign I (Sum.inl (Classical.arbitrary A)) ρT)) y ↔
        y = (Sum.inl (Classical.arbitrary A) : A ⊕ Fin n) := fun _ => Iff.rfl
    refine ⟨joinParts (fun z => z 0 = (Sum.inl (Classical.arbitrary A) : A ⊕ Fin n))
      (sourceAssign I (Sum.inl (Classical.arbitrary A)) ρT), ?_⟩
    let := hostStruc (L₁ := L₁) A n
      (joinParts (fun z => z 0 = (Sum.inl (Classical.arbitrary A) : A ⊕ Fin n))
        (sourceAssign I (Sum.inl (Classical.arbitrary A)) ρT))
    refine (Sentence.realize_inf (M := A ⊕ Fin n)).mpr ⟨?_, ?_⟩
    · exact (realize_canonGuard (L₁ := L₁) (B := B)).mpr
        ⟨_, (hc _).mpr rfl, fun z hz => (hc z).mp hz⟩
    · refine ((newInterp L₁ Tag dim B I).realize_pullRelSentence φ (A ⊕ Fin n)).mpr ?_
      exact (realize_transfer I _ _ hc ρT (targetAssign_sourceAssign I _ ρT) φ).mp hρT
  · rintro ⟨ρ, hρ⟩
    let := hostStruc (L₁ := L₁) A n ρ
    obtain ⟨hguard, hpull⟩ := (Sentence.realize_inf (M := A ⊕ Fin n)).mp hρ
    obtain ⟨c₀, hc₀, huniq⟩ := (realize_canonGuard (L₁ := L₁) (B := B)).mp hguard
    have hc : ∀ y : A ⊕ Fin n, canonPart ρ y ↔ y = c₀ :=
      fun y => ⟨fun h => huniq y h, fun h => h ▸ hc₀⟩
    refine ⟨targetAssign I c₀ ρ, ?_⟩
    refine (realize_transfer I c₀ ρ hc _ rfl φ).mpr ?_
    exact ((newInterp L₁ Tag dim B I).realize_pullRelSentence φ (A ⊕ Fin n)).mp hpull

variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **`∃SO[new]`-definability is closed under first-order reductions**, the
closure that makes RE a complexity class: the target's extended universe is
interpreted inside the source's, with the same invented values, and the kernel
is pulled back through that interpretation. -/
theorem SigmaSONewDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : SigmaSONewDefinable Q) :
    SigmaSONewDefinable P := by
  obtain ⟨B, φ, hφ⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨newBlock f.Tag f.dim B, canonGuard L₁ f.Tag f.dim B ⊓
    (newInterp L₁ f.Tag f.dim B f.toInterpretation).pullRelSentence φ, ?_⟩
  intro A _ _ _
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  rw [f.correct A, hφ (f.toInterpretation.Map A)]
  exact exists_congr fun n => sorealize_newPull f.toInterpretation B φ A n

end Closure

end DescriptiveComplexity
