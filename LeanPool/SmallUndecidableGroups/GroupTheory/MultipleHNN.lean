/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.GroupTheory.HNNExtension

/-!
# A two-stable-letter form of Britton's lemma

This file packages an iterated HNN extension in which both stable letters
identify the same pair of subgroups of a base group.  At the second stage the
associated subgroups are, necessarily, their images in the first HNN
extension.

The type `ReducedWord` records a reduced word for every coefficient in the
first HNN extension, together with the usual reducedness condition for the
outer HNN extension.  The main theorem `eval_not_mem_base` says that a reduced
word containing either stable letter cannot represent an element of the
original base group.  In particular, such a word is nontrivial.

The construction is independent of Borisov's concrete base group and can be
reused for the two-stable-letter stage of his group `G₀`.
-/

@[expose] public section

open Function

namespace Undecidability
namespace MultipleHNN

noncomputable section

variable {G : Type*} [Group G]
variable (A B : Subgroup G) (phi : A ≃* B)

/-- The first HNN extension, with its first stable letter. -/
abbrev StageOne := HNNExtension G A B phi

/-- The canonical embedding of the original base in the first stage. -/
def stageOneOf : G →* StageOne A B phi :=
  HNNExtension.of

/-- The first associated subgroup transported to the first stage. -/
abbrev MappedA : Subgroup (StageOne A B phi) :=
  A.map (stageOneOf A B phi)

/-- The second associated subgroup transported to the first stage. -/
abbrev MappedB : Subgroup (StageOne A B phi) :=
  B.map (stageOneOf A B phi)

/-- The equivalence of the mapped associated subgroups induced by `phi`. -/
def mappedEquiv : MappedA A B phi ≃* MappedB A B phi :=
  (A.equivMapOfInjective (stageOneOf A B phi)
      (HNNExtension.of_injective phi)).symm.trans
    (phi.trans
      (B.equivMapOfInjective (stageOneOf A B phi)
        (HNNExtension.of_injective phi)))

/-- The iterated HNN extension, carrying two stable letters. -/
abbrev Extension :=
  HNNExtension (StageOne A B phi) (MappedA A B phi) (MappedB A B phi)
    (mappedEquiv A B phi)

/-- The canonical embedding of the first stage in the two-letter extension. -/
def stageTwoOf : StageOne A B phi →* Extension A B phi :=
  HNNExtension.of

/-- The canonical embedding of the original base in the two-letter extension. -/
def baseEmbedding : G →* Extension A B phi :=
  (stageTwoOf A B phi).comp (stageOneOf A B phi)

/-- The first stable letter, viewed in the iterated extension. -/
def firstStable : Extension A B phi :=
  stageTwoOf A B phi (HNNExtension.t : StageOne A B phi)

/-- The second stable letter. -/
def secondStable : Extension A B phi :=
  HNNExtension.t

/-- A reduced word in the first HNN extension. -/
abbrev InnerReducedWord := HNNExtension.NormalWord.ReducedWord G A B

/-- An outer syllable consists of a sign for the second stable letter and a
reduced coefficient in the first HNN extension. -/
abbrev Syllable := ℤˣ × InnerReducedWord A B

/--
A nested reduced word for the two-stable-letter extension.

The inner words are already reduced with respect to the first stable letter.
The `chain` field says that, after evaluating those coefficients, the outer
word is reduced with respect to the second stable letter.
-/
structure ReducedWord where
  /-- The coefficient before the first occurrence of the second stable letter. -/
  head : InnerReducedWord A B
  /-- The second-stable-letter syllables and their following coefficients. -/
  toList : List (Syllable A B)
  /-- Britton reducedness for the outer HNN extension. -/
  chain :
    (toList.map (fun p ↦ (p.1, p.2.prod phi))).IsChain
      (fun a b ↦
        a.2 ∈ HNNExtension.toSubgroup
          (MappedA A B phi) (MappedB A B phi) a.1 → a.1 = b.1)

namespace ReducedWord

/-- Forget the nested description and obtain an ordinary reduced word for the
outer HNN extension. -/
def toOuter (w : ReducedWord A B phi) :
    HNNExtension.NormalWord.ReducedWord
      (StageOne A B phi) (MappedA A B phi) (MappedB A B phi) where
  head := w.head.prod phi
  toList := w.toList.map (fun p ↦ (p.1, p.2.prod phi))
  chain := w.chain

/-- Evaluation of a nested reduced word in the iterated HNN extension. -/
def eval (w : ReducedWord A B phi) : Extension A B phi :=
  w.toOuter.prod (mappedEquiv A B phi)

/-- The word contains the second stable letter. -/
def ContainsSecond (w : ReducedWord A B phi) : Prop :=
  w.toList ≠ []

/-- If the outer list is empty, the first stable letters in `head` are the
stable letters occurring in the whole word.  Together with `ContainsSecond`,
this is the support condition needed by the generalized Britton lemma. -/
def ContainsFirstInHead (w : ReducedWord A B phi) : Prop :=
  w.head.toList ≠ []

/-- The nested word contains at least one of the two stable letters. -/
def ContainsStable (w : ReducedWord A B phi) : Prop :=
  w.ContainsSecond ∨ w.ContainsFirstInHead

/-- Outer Britton lemma: a reduced word containing the second stable letter
does not lie in the embedded first-stage group. -/
theorem eval_not_mem_stageOne (w : ReducedWord A B phi)
    (hsecond : w.ContainsSecond) :
    w.eval ∉ MonoidHom.range (stageTwoOf A B phi) := by
  intro hbase
  have hnil :=
    HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
      (mappedEquiv A B phi) w.toOuter hbase
  have : w.toList = [] := by
    simpa [toOuter] using hnil
  exact hsecond this

/-- Generalized two-stable-letter Britton lemma: a reduced word containing a
stable letter does not represent an element of the original base group. -/
theorem eval_not_mem_base (w : ReducedWord A B phi)
    (hstable : w.ContainsStable) :
    w.eval ∉ MonoidHom.range (baseEmbedding A B phi) := by
  intro hbase
  rcases hbase with ⟨g, hg⟩
  have hstageOne : w.eval ∈ MonoidHom.range (stageTwoOf A B phi) :=
    ⟨stageOneOf A B phi g, by simpa [baseEmbedding] using hg⟩
  by_cases hsecond : w.ContainsSecond
  · exact eval_not_mem_stageOne (A := A) (B := B) (phi := phi) w
      hsecond hstageOne
  · have hfirst : w.ContainsFirstInHead := hstable.resolve_left hsecond
    have houterNil : w.toList = [] := not_ne_iff.mp hsecond
    have heq :
        stageTwoOf A B phi (w.head.prod phi) =
          stageTwoOf A B phi (stageOneOf A B phi g) := by
      simpa [eval, toOuter, houterNil, baseEmbedding,
        stageTwoOf, stageOneOf,
        HNNExtension.NormalWord.ReducedWord.prod] using hg.symm
    have hinner : w.head.prod phi = stageOneOf A B phi g :=
      (HNNExtension.of_injective (mappedEquiv A B phi)) heq
    have hinnerBase :
        w.head.prod phi ∈ MonoidHom.range (stageOneOf A B phi) :=
      ⟨g, hinner.symm⟩
    have hnil :=
      HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
        phi w.head hinnerBase
    exact hfirst hnil

/-- A reduced two-stable-letter word containing a stable letter is nontrivial. -/
theorem eval_ne_one (w : ReducedWord A B phi)
    (hstable : w.ContainsStable) :
    w.eval ≠ 1 := by
  intro hOne
  apply eval_not_mem_base (A := A) (B := B) (phi := phi) w hstable
  refine ⟨1, ?_⟩
  simp [hOne]

end ReducedWord

end

end MultipleHNN
end Undecidability
