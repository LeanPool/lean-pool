/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrder

/-!
# Functoriality of block expansion, and padding with trivial blocks

Infrastructure for the second-order definability layer of
`DescriptiveComplexity.SecondOrder`:

* *Functoriality*: a language morphism `Φ : L →ᴸ L'` lifts through the
  expansion by a list of blocks (`DescriptiveComplexity.soLangLift`), and alternating
  second-order satisfaction is invariant when the base structure is expanded
  along `Φ` (`DescriptiveComplexity.sorealize_soLangLift`).
* *Embedded first-order sentences*: a sentence of the base language, embedded
  into the block expansion (`DescriptiveComplexity.soLangEmbed`), can be pulled out of
  the second-order quantification when it appears as a conjunct or as the
  premise of an implication (`DescriptiveComplexity.sorealize_inf_embed`,
  `DescriptiveComplexity.sorealize_imp_embed`). This is how the auxiliary order of an
  ordered reduction is eliminated: the order becomes a second-order variable
  of the first block, guarded by the first-order sentence “it is a linear
  order”.
* *Padding*: appending or prepending the trivial (empty) block
  (`DescriptiveComplexity.SOBlock.trivial`) does not change alternating second-order
  satisfaction (`DescriptiveComplexity.sorealize_append_trivial`), so `Σₖ`- and
  `Πₖ`-definability satisfy the level inclusions of the polynomial hierarchy:
  `Σₖ ⊆ Σₖ₊₁ ∩ Πₖ₊₁` and dually (`DescriptiveComplexity.SigmaSODefinable.succ`,
  `DescriptiveComplexity.SigmaSODefinable.piSucc`, `DescriptiveComplexity.PiSODefinable.succ`,
  `DescriptiveComplexity.PiSODefinable.sigmaSucc`).

Languages vary through all the inductions, so the recursive definitions and
statements take them as explicit arguments.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Assignments always exist -/

instance SOBlock.instNonemptyAssignment (B : SOBlock) (A : Type) :
    Nonempty (B.Assignment A) :=
  ⟨fun _ _ => True⟩

/-! ### Functoriality of block expansion -/

/-- Lift of a language morphism through the expansion by blocks: symbols of
the base language are mapped by the morphism, relation variables of the
blocks to themselves. -/
def soLangLift : ∀ (Bs : List SOBlock) (L L' : Language.{0, 0}),
    (L →ᴸ L') → (soLang L Bs →ᴸ soLang L' Bs)
  | [], _, _, Φ => Φ
  | B :: Bs, L, L', Φ =>
      soLangLift Bs (L.sum B.lang) (L'.sum B.lang) (Φ.sumMap (LHom.id B.lang))

/-- Alternating second-order satisfaction only depends on the base structure
through the symbols the kernel mentions: it is invariant under transporting
the kernel along a language morphism whose expansion the structure is. -/
theorem sorealize_soLangLift :
    ∀ (Bs : List SOBlock) (L L' : Language.{0, 0}) (Φ : L →ᴸ L') (A : Type)
      (instL : L.Structure A) (instL' : L'.Structure A),
      @LHom.IsExpansionOn L L' Φ A instL instL' →
      ∀ (φ : (soLang L Bs).Sentence) (pol : Bool),
        @SORealize L' A instL' Bs ((soLangLift Bs L L' Φ).onSentence φ) pol ↔
          @SORealize L A instL Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L L' Φ A instL instL' hexp φ pol
    let := instL
    let := instL'
    have := hexp
    exact Φ.realize_onSentence A φ
  | cons B Bs ih =>
    intro L L' Φ A instL instL' hexp φ pol
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @SORealize (L'.sum B.lang) A (@sumStructure L' B.lang A instL' (B.structure ρ)) Bs
            ((soLangLift Bs (L.sum B.lang) (L'.sum B.lang)
              (Φ.sumMap (LHom.id B.lang))).onSentence φ) false) ↔
        ∃ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            φ false
      refine exists_congr fun ρ => ?_
      exact ih (L.sum B.lang) (L'.sum B.lang) (Φ.sumMap (LHom.id B.lang)) A _ _
        (by let := instL; let := instL'; let := B.structure ρ; have := hexp
            infer_instance) φ false
    | false =>
      change (∀ ρ : B.Assignment A,
          @SORealize (L'.sum B.lang) A (@sumStructure L' B.lang A instL' (B.structure ρ)) Bs
            ((soLangLift Bs (L.sum B.lang) (L'.sum B.lang)
              (Φ.sumMap (LHom.id B.lang))).onSentence φ) true) ↔
        ∀ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            φ true
      refine forall_congr' fun ρ => ?_
      exact ih (L.sum B.lang) (L'.sum B.lang) (Φ.sumMap (LHom.id B.lang)) A _ _
        (by let := instL; let := instL'; let := B.structure ρ; have := hexp
            infer_instance) φ true

/-! ### Embedding the base language into a block expansion -/

/-- The embedding of the base language into its expansion by blocks. -/
def soLangEmbed : ∀ (Bs : List SOBlock) (L : Language.{0, 0}), L →ᴸ soLang L Bs
  | [], L => LHom.id L
  | B :: Bs, L => (soLangEmbed Bs (L.sum B.lang)).comp LHom.sumInl

private theorem soLangEmbed_cons (B : SOBlock) (Bs : List SOBlock) (L : Language.{0, 0})
    (χ : L.Sentence) :
    (soLangEmbed (B :: Bs) L).onSentence χ =
      (soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) :=
  congrFun (LHom.comp_onBoundedFormula (soLangEmbed Bs (L.sum B.lang)) LHom.sumInl) χ

/-- A conjunct that is (the embedding of) a sentence of the base language can
be pulled out of the second-order quantification. -/
theorem sorealize_inf_embed :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (χ : L.Sentence) (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A instL Bs ((soLangEmbed Bs L).onSentence χ ⊓ φ) pol ↔
        @Sentence.Realize L A instL χ ∧ @SORealize L A instL Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL χ φ pol
    let := instL
    let : (soLang L []).Structure A := instL
    refine Iff.trans (Sentence.realize_inf (L := soLang L []) (M := A)) ?_
    exact and_congr_left' ((LHom.id L).realize_onSentence A χ)
  | cons B Bs ih =>
    intro L A instL χ φ pol
    rw [soLangEmbed_cons]
    have key : ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⊓ φ)
            (!pol) ↔
          @Sentence.Realize L A instL χ ∧
            @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
              φ (!pol) := by
      intro ρ
      let := instL
      let := B.structure ρ
      refine (ih (L.sum B.lang) A _ (LHom.sumInl.onSentence χ) φ (!pol)).trans ?_
      exact and_congr_left' (LHom.sumInl.realize_onSentence A χ)
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⊓ φ)
            false) ↔ _
      refine (exists_congr fun ρ => key ρ).trans ?_
      exact exists_and_left
    | false =>
      change (∀ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⊓ φ)
            true) ↔ _
      refine (forall_congr' fun ρ => key ρ).trans ?_
      constructor
      · intro h
        exact ⟨(h (Classical.arbitrary _)).1, fun ρ => (h ρ).2⟩
      · rintro ⟨hχ, h⟩ ρ
        exact ⟨hχ, h ρ⟩

/-- A premise that is (the embedding of) a sentence of the base language can
be pulled out of the second-order quantification. -/
theorem sorealize_imp_embed :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (χ : L.Sentence) (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A instL Bs ((soLangEmbed Bs L).onSentence χ ⟹ φ) pol ↔
        (@Sentence.Realize L A instL χ → @SORealize L A instL Bs φ pol) := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL χ φ pol
    let := instL
    let : (soLang L []).Structure A := instL
    refine Iff.trans (Sentence.realize_imp (L := soLang L []) (M := A)) ?_
    exact imp_congr ((LHom.id L).realize_onSentence A χ) Iff.rfl
  | cons B Bs ih =>
    intro L A instL χ φ pol
    rw [soLangEmbed_cons]
    have key : ∀ ρ : B.Assignment A,
        @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⟹ φ)
            (!pol) ↔
          (@Sentence.Realize L A instL χ →
            @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
              φ (!pol)) := by
      intro ρ
      let := instL
      let := B.structure ρ
      refine (ih (L.sum B.lang) A _ (LHom.sumInl.onSentence χ) φ (!pol)).trans ?_
      exact imp_congr (LHom.sumInl.realize_onSentence A χ) Iff.rfl
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⟹ φ)
            false) ↔ _
      refine (exists_congr fun ρ => key ρ).trans ?_
      constructor
      · rintro ⟨ρ, h⟩ hχ
        exact ⟨ρ, h hχ⟩
      · intro h
        rcases Classical.em (@Sentence.Realize L A instL χ) with hχ | hχ
        · obtain ⟨ρ, hρ⟩ := h hχ
          exact ⟨ρ, fun _ => hρ⟩
        · exact ⟨Classical.arbitrary _, fun hχ' => absurd hχ' hχ⟩
    | false =>
      change (∀ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            ((soLangEmbed Bs (L.sum B.lang)).onSentence (LHom.sumInl.onSentence χ) ⟹ φ)
            true) ↔ _
      refine (forall_congr' fun ρ => key ρ).trans ?_
      exact ⟨fun h hχ ρ => h ρ hχ, fun h ρ hχ => h hχ ρ⟩

/-! ### The trivial block, and padding -/

/-- The trivial second-order quantifier block, with no relation variables.
Quantifying over it (in either polarity) does not change satisfaction; it
pads a quantifier prefix to a larger number of alternations. -/
def SOBlock.trivial : SOBlock where
  ι := Empty
  arity := Empty.elim

/-- Extension of the block expansion under appending one more block at the
end of the list. -/
def soLangAppendOne (C : SOBlock) : ∀ (L : Language.{0, 0}) (Bs : List SOBlock),
    soLang L Bs →ᴸ soLang L (Bs ++ [C])
  | _, [] => LHom.sumInl
  | L, B :: Bs => soLangAppendOne C (L.sum B.lang) Bs

/-- Appending the trivial block does not change alternating second-order
satisfaction. -/
theorem sorealize_append_trivial :
    ∀ (Bs : List SOBlock) (L : Language.{0, 0}) (A : Type) (instL : L.Structure A)
      (φ : (soLang L Bs).Sentence) (pol : Bool),
      @SORealize L A instL (Bs ++ [SOBlock.trivial])
          ((soLangAppendOne SOBlock.trivial L Bs).onSentence φ) pol ↔
        @SORealize L A instL Bs φ pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L A instL φ pol
    have key : ∀ ρ : SOBlock.trivial.Assignment A,
        @SORealize (L.sum SOBlock.trivial.lang) A
            (@sumStructure L SOBlock.trivial.lang A instL (SOBlock.trivial.structure ρ)) []
            ((LHom.sumInl : L →ᴸ L.sum SOBlock.trivial.lang).onSentence φ) (!pol) ↔
          @SORealize L A instL [] φ pol := by
      intro ρ
      let := instL
      let := SOBlock.trivial.structure ρ
      exact (LHom.sumInl : L →ᴸ L.sum SOBlock.trivial.lang).realize_onSentence A φ
    cases pol with
    | true =>
      change (∃ ρ : SOBlock.trivial.Assignment A, _) ↔ _
      exact ⟨fun ⟨ρ, h⟩ => (key ρ).mp h,
        fun h => ⟨Classical.arbitrary _, (key _).mpr h⟩⟩
    | false =>
      change (∀ ρ : SOBlock.trivial.Assignment A, _) ↔ _
      exact ⟨fun h => (key (Classical.arbitrary _)).mp (h _), fun h ρ => (key ρ).mpr h⟩
  | cons B Bs ih =>
    intro L A instL φ pol
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ))
            (Bs ++ [SOBlock.trivial])
            ((soLangAppendOne SOBlock.trivial (L.sum B.lang) Bs).onSentence φ) false) ↔
        ∃ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            φ false
      exact exists_congr fun ρ => ih (L.sum B.lang) A _ φ false
    | false =>
      change (∀ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ))
            (Bs ++ [SOBlock.trivial])
            ((soLangAppendOne SOBlock.trivial (L.sum B.lang) Bs).onSentence φ) true) ↔
        ∀ ρ : B.Assignment A,
          @SORealize (L.sum B.lang) A (@sumStructure L B.lang A instL (B.structure ρ)) Bs
            φ true
      exact forall_congr' fun ρ => ih (L.sum B.lang) A _ φ true

/-! ### Level inclusions at the definability level -/

variable {L : Language.{0, 0}} [L.IsRelational] {k : ℕ} {P : DecisionProblem L}

/-- `Σₖ ⊆ Σₖ₊₁`: pad by appending the trivial block. -/
theorem SigmaSODefinable.succ (h : SigmaSODefinable k P) : SigmaSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  refine ⟨Bs ++ [SOBlock.trivial], by simp [hk],
    (soLangAppendOne SOBlock.trivial L Bs).onSentence φ, ?_⟩
  intro A _ _ _
  rw [hφ A]
  exact (sorealize_append_trivial Bs L A _ φ true).symm

/-- `Πₖ ⊆ Πₖ₊₁`: pad by appending the trivial block. -/
theorem PiSODefinable.succ (h : PiSODefinable k P) : PiSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  refine ⟨Bs ++ [SOBlock.trivial], by simp [hk],
    (soLangAppendOne SOBlock.trivial L Bs).onSentence φ, ?_⟩
  intro A _ _ _
  rw [hφ A]
  exact (sorealize_append_trivial Bs L A _ φ false).symm

/-- `Σₖ ⊆ Πₖ₊₁`: pad by prepending the trivial block. -/
theorem SigmaSODefinable.piSucc (h : SigmaSODefinable k P) : PiSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  refine ⟨SOBlock.trivial :: Bs, by simp [hk],
    (soLangLift Bs L (L.sum SOBlock.trivial.lang) LHom.sumInl).onSentence φ, ?_⟩
  intro A instA _ _
  have key : ∀ ρ : SOBlock.trivial.Assignment A,
      @SORealize (L.sum SOBlock.trivial.lang) A
          (@sumStructure L SOBlock.trivial.lang A instA (SOBlock.trivial.structure ρ)) Bs
          ((soLangLift Bs L (L.sum SOBlock.trivial.lang) LHom.sumInl).onSentence φ)
          true ↔ P A := by
    intro ρ
    refine (sorealize_soLangLift Bs L (L.sum SOBlock.trivial.lang) LHom.sumInl A instA _
      (by let := instA; let := SOBlock.trivial.structure ρ; infer_instance)
      φ true).trans (hφ A).symm
  change P A ↔ ∀ ρ : SOBlock.trivial.Assignment A, _
  exact ⟨fun hP ρ => (key ρ).mpr hP, fun h => (key (Classical.arbitrary _)).mp (h _)⟩

/-- `Πₖ ⊆ Σₖ₊₁`: pad by prepending the trivial block. -/
theorem PiSODefinable.sigmaSucc (h : PiSODefinable k P) : SigmaSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  refine ⟨SOBlock.trivial :: Bs, by simp [hk],
    (soLangLift Bs L (L.sum SOBlock.trivial.lang) LHom.sumInl).onSentence φ, ?_⟩
  intro A instA _ _
  have key : ∀ ρ : SOBlock.trivial.Assignment A,
      @SORealize (L.sum SOBlock.trivial.lang) A
          (@sumStructure L SOBlock.trivial.lang A instA (SOBlock.trivial.structure ρ)) Bs
          ((soLangLift Bs L (L.sum SOBlock.trivial.lang) LHom.sumInl).onSentence φ)
          false ↔ P A := by
    intro ρ
    refine (sorealize_soLangLift Bs L (L.sum SOBlock.trivial.lang) LHom.sumInl A instA _
      (by let := instA; let := SOBlock.trivial.structure ρ; infer_instance)
      φ false).trans (hφ A).symm
  change P A ↔ ∃ ρ : SOBlock.trivial.Assignment A, _
  exact ⟨fun hP => ⟨Classical.arbitrary _, (key _).mpr hP⟩, fun ⟨ρ, h⟩ => (key ρ).mp h⟩

end DescriptiveComplexity
