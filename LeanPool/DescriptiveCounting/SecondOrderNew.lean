/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrderLift

/-!
# Existential second-order logic with value invention

The logic `∃SO[new]` defining the class RE of recursively enumerable problems:
existential second-order logic whose relation variables range over a universe
*extended by finitely many invented values*, in the style of the
object-creating query languages of ([Abiteboul–Hull–Vianu 1995]
[abiteboul1995foundations], ch. 18).

Bounding the certificate by the instance is what keeps a second-order class
inside NP: a `Σ₁` sentence guesses relations over `A` itself, so the search
space is exponential in `|A|`. Value invention
removes exactly that bound and nothing else: the certificate is a finite
extension `A ⊕ Fin m` of the universe – with `m` *unbounded* – together with
relations over it, checked by a fixed first-order kernel. The witness is still
a finite object and the kernel is still decidable on a finite structure, so
the yes-instances are those found by an unbounded search over finite
witnesses: this is a logical definition of *recursive enumerability*, with no
machine model. (The converse inclusion, RE ⊆ `∃SO[new]`, is the
Trakhtenbrot-style encoding of an accepting run into invented values; it lives
with the machine bridge, not here.)

## The extended structure

An instance `A` and a number `m` of invented values determine an extended
structure over the vocabulary `DescriptiveComplexity.newLang L`, the base
vocabulary `L` together with one unary predicate `old`:

* its universe is `A ⊕ Fin m`;
* the symbols of `L` hold exactly where they hold in `A`, on original
  elements only – invented values are related to nothing
  (`DescriptiveComplexity.extBase`);
* `old` marks the original elements (`DescriptiveComplexity.IsOld`).

The vocabulary is relational, as every vocabulary of a
`DescriptiveComplexity.DecisionProblem` is, so invented values carry no
structure at all until the certificate's relations put some on them.

## Main definitions and results

* `DescriptiveComplexity.SigmaSONewDefinable`: definability by an `∃SO[new]`
  sentence – one existential second-order block over the extended universe and
  a first-order kernel, reusing the alternation machinery of
  `DescriptiveComplexity.SecondOrder` at a one-block list;
* `DescriptiveComplexity.extEquiv`: extended structures are functorial in the
  base isomorphism, so `∃SO[new]` expresses isomorphism-invariant properties;
* `DescriptiveComplexity.sigmaSONewDefinable_congr`: definability depends only
  on the finite instances of a problem;
* `DescriptiveComplexity.SigmaSODefinable.toNew`: `Σ₁ ⊆ ∃SO[new]`, by
  inventing nothing – the kernel is guarded by
  `DescriptiveComplexity.noNewSentence`, “every element is original”, which
  pins the number of invented values to zero. As a statement about classes this
  is `DescriptiveComplexity.NP_subset_RE`.

No alternation hierarchy is built on top of `∃SO[new]`, deliberately:
alternating second-order blocks over a *finite* extended universe are still
checked by an unbounded search over finite witnesses, so the levels would
collapse into RE rather than stack. (That collapse is a semantic remark, not a
theorem here: proving it inside the logic needs the same encoding as the
inclusion RE ⊆ `∃SO[new]`.)
-/

@[expose] public section

namespace FirstOrder

namespace Language

/-- Relation symbols of the language marking the original elements inside an
extended universe. -/
inductive oldRel : ℕ → Type
  /-- `old x`: the element `x` comes from the original structure, i.e., it is
  not an invented value. -/
  | old : oldRel 1
  deriving DecidableEq

/-- The one-symbol relational language marking, inside a universe extended
with invented values, the elements of the original structure. -/
protected def oldMark : Language :=
  ⟨fun _ => Empty, oldRel⟩
  deriving IsRelational

/-- The symbol marking the original elements. -/
abbrev oldSym : Language.oldMark.Relations 1 := .old

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-- The vocabulary of extended structures: the base vocabulary together with
the unary predicate `old` marking the elements of the original structure. -/
abbrev newLang (L : Language.{0, 0}) : Language := L.sum Language.oldMark

/-! ### The extended universe -/

section Extended

/-- The original elements of a universe extended by invented values. The
invented values are an arbitrary type, so that the same predicate reads an
extension by a *set* of them and not only by an initial segment. -/
def IsOld {A N : Type} : A ⊕ N → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The base structure carried by the extended universe: a relation symbol
holds of a tuple exactly when all its entries are original elements and it
holds of them in `A`. Invented values are related to nothing. -/
@[instance_reducible]
def extBase (L : Language.{0, 0}) [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ) :
    L.Structure (A ⊕ Fin m) where
  funMap f := isEmptyElim f
  RelMap {_k} r x := ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y

/-- The interpretation of the marking predicate on the extended universe. -/
@[instance_reducible]
def oldMarkStructure (A : Type) (m : ℕ) : Language.oldMark.Structure (A ⊕ Fin m) where
  RelMap | .old => fun x => IsOld (x 0)

/-- **The extended structure**: the instance `A` together with `m` invented
values, over the vocabulary `DescriptiveComplexity.newLang L`. -/
instance extStructure (L : Language.{0, 0}) [L.IsRelational] (A : Type) [L.Structure A]
    (m : ℕ) : (newLang L).Structure (A ⊕ Fin m) :=
  @sumStructure L Language.oldMark (A ⊕ Fin m) (extBase L A m) (oldMarkStructure A m)

variable {L : Language.{0, 0}} {A A' : Type} {m m' : ℕ}

@[simp]
theorem isOld_inl (a : A) : IsOld (Sum.inl a : A ⊕ Fin m) := trivial

@[simp]
theorem not_isOld_inr (i : Fin m) : ¬IsOld (Sum.inr i : A ⊕ Fin m) := id

theorem isOld_iff {x : A ⊕ Fin m} : IsOld x ↔ ∃ a : A, x = Sum.inl a := by
  cases x <;> simp

theorem relMap_ext_iff [L.IsRelational] [L.Structure A] {k : ℕ} (r : L.Relations k)
    (x : Fin k → A ⊕ Fin m) :
    RelMap (L := newLang L) (Sum.inl r) x ↔ ∃ y, (∀ i, x i = Sum.inl (y i)) ∧ RelMap r y :=
  Iff.rfl

/-- On original elements, the extended structure is the original one. -/
@[simp]
theorem relMap_ext_inl [L.IsRelational] [L.Structure A] {k : ℕ} (r : L.Relations k)
    (y : Fin k → A) :
    RelMap (L := newLang L) (M := A ⊕ Fin m) (Sum.inl r) (fun i => Sum.inl (y i)) ↔
      RelMap r y := by
  rw [relMap_ext_iff]
  refine ⟨fun h => ?_, fun h => ⟨y, fun _ => rfl, h⟩⟩
  obtain ⟨y', hy', h⟩ := h
  have hyy : y = y' := funext fun i => Sum.inl_injective (hy' i)
  exact hyy ▸ h

@[simp]
theorem relMap_ext_old [L.IsRelational] [L.Structure A] (x : Fin 1 → A ⊕ Fin m) :
    RelMap (L := newLang L) (Sum.inr Language.oldSym) x ↔ IsOld (x 0) :=
  Iff.rfl

/-! ### Functoriality in the base structure -/

private theorem relMap_ext_map [L.IsRelational] [L.Structure A] [L.Structure A']
    (e : A ≃[L] A') (σ : Fin m ≃ Fin m') {k : ℕ} (r : L.Relations k)
    (x : Fin k → A ⊕ Fin m) :
    RelMap (L := newLang L) (Sum.inl r) (fun i => Sum.map e σ (x i)) ↔
      RelMap (L := newLang L) (Sum.inl r) x := by
  simp only [relMap_ext_iff]
  constructor
  · rintro ⟨y', hy', h⟩
    refine ⟨fun i => e.symm (y' i), fun i => ?_, (StrongHomClass.map_rel e.symm r y').mpr h⟩
    have hi : Sum.map (e : A → A') (σ : Fin m → Fin m') (x i) = Sum.inl (y' i) := hy' i
    change x i = Sum.inl (e.symm (y' i))
    cases hxi : x i with
    | inl a =>
      rw [hxi] at hi
      rw [← Sum.inl_injective hi, e.symm_apply_apply]
    | inr j =>
      rw [hxi] at hi
      exact absurd hi (by simp)
  · rintro ⟨y, hy, h⟩
    refine ⟨fun i => e (y i), fun i => ?_, (StrongHomClass.map_rel e r y).mpr h⟩
    change Sum.map (e : A → A') (σ : Fin m → Fin m') (x i) = Sum.inl (e (y i))
    rw [hy i]
    rfl

/-- Extended structures are functorial in the base structure: an isomorphism
of instances and a bijection of the invented values induce an isomorphism of
the extended structures. -/
private def extEquiv [L.IsRelational] [L.Structure A] [L.Structure A']
    (e : A ≃[L] A') (σ : Fin m ≃ Fin m') : (A ⊕ Fin m) ≃[newLang L] (A' ⊕ Fin m') where
  toEquiv := e.toEquiv.sumCongr σ
  map_fun' f _ := isEmptyElim f
  map_rel' {_k} r x := by
    cases r with
    | inl s => exact relMap_ext_map e σ s x
    | inr s =>
      cases s with
      | old =>
        change IsOld (Sum.map e σ (x 0)) ↔ IsOld (x 0)
        cases x 0 <;> simp

end Extended

/-! ### Definability

`SORealize` is reused at the one-block list `[B]`, so that an `∃SO[new]`
sentence is literally an `∃SO` sentence – over the extended vocabulary, read
in the extended structure. -/

section Definability

variable {L : Language.{0, 0}}

/-- Unfolding of alternating satisfaction at a single existential block. -/
private theorem sorealize_singleton (A : Type) [inst : L.Structure A] (B : SOBlock)
    (φ : (soLang L [B]).Sentence) :
    SORealize L A [B] φ true ↔
      ∃ ρ : B.Assignment A, @Sentence.Realize (L.sum B.lang) A
        (@sumStructure L B.lang A inst (B.structure ρ)) φ :=
  Iff.rfl

/-- **Definability in `∃SO[new]`**, existential second-order logic with value
invention: on nonempty finite structures, `P A` holds exactly when, for *some*
number `m` of invented values, the relation variables of the block `B` can be
assigned relations over the extended universe `A ⊕ Fin m` satisfying the
first-order kernel `φ` in the extended structure.

The number `m` of invented values is unbounded, which is precisely what takes
the notion beyond `Σ₁` (`DescriptiveComplexity.SigmaSODefinable`, where the
certificate lives over `A` itself): a witness is a finite object, but no
function of `|A|` bounds its size. -/
def SigmaSONewDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ B : SOBlock, ∃ φ : (soLang (newLang L) [B]).Sentence,
    ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ m : ℕ, SORealize (newLang L) (A ⊕ Fin m) [B] φ true

/-- `∃SO[new]`-definability only depends on the finite instances of a
problem. -/
theorem sigmaSONewDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    SigmaSONewDefinable P ↔ SigmaSONewDefinable Q := by
  constructor <;> rintro ⟨B, φ, hφ⟩ <;> refine ⟨B, φ, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hφ A)
  · exact (h A).trans (hφ A)

end Definability

/-! ### Inventing nothing

The `Σ₁` sentences are the `∃SO[new]` sentences that invent nothing: the
kernel is guarded by `DescriptiveComplexity.noNewSentence`, which forces the
extended universe to be the original one. -/

section NoNew

variable (L : Language.{0, 0})

/-- The atom `old x`, over the extended vocabulary. -/
def oldF {α : Type} (x : α) : (newLang L).Formula α :=
  Relations.formula₁ (Sum.inr Language.oldSym) (Term.var x)

/-- The sentence “nothing was invented”: every element of the universe is an
original element. -/
private noncomputable def noNewSentence : (newLang L).Sentence :=
  (oldF L (Sum.inr 0)).iAlls (Fin 1)

private theorem realize_noNewSentence [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ) :
    @Sentence.Realize (newLang L) (A ⊕ Fin m) _ (noNewSentence L) ↔
      ∀ x : A ⊕ Fin m, IsOld x := by
  simp only [noNewSentence, oldF, Sentence.Realize, Formula.realize_iAlls]
  exact ⟨fun h x => h fun _ => x, fun h i => h (i 0)⟩

/-- The mark of the original elements on the original universe itself: every
element is original. -/
@[instance_reducible]
def allOldMarkStructure (A : Type) : Language.oldMark.Structure A where
  RelMap | .old => fun _ => True

/-- The instance itself, over the extended vocabulary: nothing is invented, so
every element is marked as original. -/
@[instance_reducible]
def allOldStructure (A : Type) [L.Structure A] : (newLang L).Structure A :=
  @sumStructure L Language.oldMark A _ (allOldMarkStructure A)

/-- With no invented values, the extended structure is the instance itself. -/
def extEquivNoNew [L.IsRelational] (A : Type) [L.Structure A] (m : ℕ)
    [IsEmpty (Fin m)] :
    @Language.Equiv (newLang L) A (A ⊕ Fin m) (allOldStructure L A) (extStructure L A m) :=
  letI := allOldStructure L A
  { toEquiv := (Equiv.sumEmpty A (Fin m)).symm
    map_fun' := fun {_n} f _ => isEmptyElim f
    map_rel' := fun {_k} r x => by
      cases r with
      | inl s => exact relMap_ext_inl s x
      | inr s =>
        cases s with
        | old => exact iff_of_true (isOld_inl (m := m) (x 0)) trivial }

end NoNew

/-! ### `Σ₁ ⊆ ∃SO[new]` -/

variable {L : Language.{0, 0}}

/-- **The guarded sentence, read over an extended universe**: it holds exactly
when nothing was invented and the original sentence holds over the instance
itself. This is the whole content of inventing nothing, and it is what both
`DescriptiveComplexity.SigmaSODefinable.toNew` and its bounded twin read. -/
private theorem sorealize_guardNoNew_iff [L.IsRelational] {B : SOBlock}
    (φ : (soLang L [B]).Sentence) (A : Type) [instA : L.Structure A] (m : ℕ) :
    SORealize (newLang L) (A ⊕ Fin m) [B]
      ((soLangEmbed [B] (newLang L)).onSentence (noNewSentence L) ⊓
        (soLangLift [B] L (newLang L) LHom.sumInl).onSentence φ) true ↔
      (IsEmpty (Fin m) ∧ SORealize L A [B] φ true) := by
  let instAll := allOldStructure L A
  rw [sorealize_inf_embed [B] (newLang L) (A ⊕ Fin m) _ (noNewSentence L) _ true,
    realize_noNewSentence L A m]
  constructor
  · rintro ⟨hno, hrest⟩
    have : IsEmpty (Fin m) := ⟨fun i => not_isOld_inr i (hno (Sum.inr i))⟩
    refine ⟨inferInstance, ?_⟩
    have h1 := (@sorealize_iso (newLang L) A (A ⊕ Fin m) instAll _
      (extEquivNoNew L A m) [B] _ true).mpr hrest
    exact (sorealize_soLangLift [B] L (newLang L) LHom.sumInl A instA instAll
      (by let := allOldMarkStructure A; infer_instance) φ true).mp h1
  · rintro ⟨hempty, hφA⟩
    have := hempty
    refine ⟨fun x => ?_, ?_⟩
    · cases x with
      | inl a => exact isOld_inl a
      | inr i => exact (hempty.false i).elim
    · have h1 := (sorealize_soLangLift [B] L (newLang L) LHom.sumInl A instA instAll
        (by let := allOldMarkStructure A; infer_instance) φ true).mpr hφA
      exact (@sorealize_iso (newLang L) A (A ⊕ Fin m) instAll _
        (extEquivNoNew L A m) [B] _ true).mp h1

/-- **Existential second-order definability implies `∃SO[new]`-definability**:
an `∃SO` sentence becomes an `∃SO[new]` sentence when guarded by “nothing was
invented”. Once RE is a complexity class, this is the inclusion `NP ⊆ RE`. -/
theorem SigmaSODefinable.toNew [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSODefinable 1 P) : SigmaSONewDefinable P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  obtain ⟨B, rfl⟩ : ∃ B, Bs = [B] := by
    match Bs, hk with
    | [B], _ => exact ⟨B, rfl⟩
  refine ⟨B, (soLangEmbed [B] (newLang L)).onSentence (noNewSentence L) ⊓
    (soLangLift [B] L (newLang L) LHom.sumInl).onSentence φ, ?_⟩
  intro A instA _ _
  constructor
  · intro hP
    exact ⟨0, (sorealize_guardNoNew_iff φ A 0).mpr ⟨inferInstance, (hφ A).mp hP⟩⟩
  · rintro ⟨m, hm⟩
    exact (hφ A).mpr ((sorealize_guardNoNew_iff φ A m).mp hm).2

end DescriptiveComplexity
