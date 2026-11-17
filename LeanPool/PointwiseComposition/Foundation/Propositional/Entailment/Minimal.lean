/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.Logic.Entailment
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Finset.Basic

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

/-- The Neg Equiv construction in `FFL.Axioms`. -/
protected abbrev NegEquiv [LogicalNeutral F] :=
  ∼φ ⇔ₗ (φ ⇒ₗ ⊥)

/-- The Verum construction in `FFL.Axioms`. -/
protected abbrev Verum [LogicalNeutral F] : F :=
  ⊤

/-- The Imply K construction in `FFL.Axioms`. -/
protected abbrev ImplyK :=
  φ ⇒ₗ ψ ⇒ₗ φ

/-- The Imply S construction in `FFL.Axioms`. -/
protected abbrev ImplyS :=
  (φ ⇒ₗ ψ ⇒ₗ χ) ⇒ₗ (φ ⇒ₗ ψ) ⇒ₗ φ ⇒ₗ χ

/-- The And Elim₁ construction in `FFL.Axioms`. -/
protected abbrev AndElim₁ :=
  φ ⋏ ψ ⇒ₗ φ

/-- The And Elim₂ construction in `FFL.Axioms`. -/
protected abbrev AndElim₂ :=
  φ ⋏ ψ ⇒ₗ ψ

/-- The And Inst construction in `FFL.Axioms`. -/
protected abbrev AndInst :=
  φ ⇒ₗ ψ ⇒ₗ φ ⋏ ψ

/-- The Or Inst₁ construction in `FFL.Axioms`. -/
protected abbrev OrInst₁ :=
  φ ⇒ₗ φ ⋎ ψ

/-- The Or Inst₂ construction in `FFL.Axioms`. -/
protected abbrev OrInst₂ :=
  ψ ⇒ₗ φ ⋎ ψ

/-- The Or Elim construction in `FFL.Axioms`. -/
protected abbrev OrElim :=
  (φ ⇒ₗ χ) ⇒ₗ (ψ ⇒ₗ χ) ⇒ₗ (φ ⋎ ψ ⇒ₗ χ)

end Axioms
end FFL

namespace FFL
namespace Entailment

-- def cast (e : φ = ψ) (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ := e ▸ b
-- lemma cast! (e : φ = ψ) (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ := ⟨cast e b.some⟩

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

/-- A proof system closed under modus ponens. -/
class ModusPonens (𝓢 : S) where
  /-- The mdp! construction in `FFL.Entailment.ModusPonens`. -/
  mdpProof {φ ψ : F} : 𝓢 ⊢! φ ⇒ₗ ψ → 𝓢 ⊢! φ → 𝓢 ⊢! ψ

alias mdpProof := ModusPonens.mdpProof
/-- The «term ⨀ » construction in `FFL.Entailment`. -/
infixl:90 "⨀" => mdpProof

lemma mdp [ModusPonens 𝓢] : 𝓢 ⊢ φ ⇒ₗ ψ → 𝓢 ⊢ φ → 𝓢 ⊢ ψ := by rintro ⟨hpq⟩ ⟨hp⟩; exact ⟨hpq⨀hp⟩
/-- The «term ⨀  1» construction in `FFL.Entailment`. -/
infixl:90 "⨀" => mdp
/-- The «term ⨀! » construction in `FFL.Entailment`. -/
infixl:90 "⨀!" => mdpProof

/-- Negation `∼φ` is equivalent to `φ ⇒ₗ ⊥` on **system**.

  This is weaker asssumption than _"introducing `∼φ` as an abbreviation of `φ ⇒ₗ ⊥`" (`NegAbbrev`)_.
-/
class NegationEquiv [LogicalNeutral F] (𝓢 : S) where
  /-- The neg Equiv! construction in `FFL.Entailment`. -/
  negEquivProof {φ : F} : 𝓢 ⊢! Axioms.NegEquiv φ
export NegationEquiv (negEquivProof)

@[simp]
lemma neg_equiv [LogicalNeutral F] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ⇔ₗ (φ ⇒ₗ ⊥) :=
  ⟨negEquivProof⟩

/-- Proofs of the truth constant in the given proof system. -/
class HasAxiomVerum [LogicalNeutral F] (𝓢 : S) where
  /-- The verum! construction in `FFL.Entailment.HasAxiomVerum`. -/
  verumProof : 𝓢 ⊢! Axioms.Verum

/-- The verum! construction in `FFL.Entailment`. -/
def verumProof [LogicalNeutral F] [HasAxiomVerum 𝓢] : 𝓢 ⊢! ⊤ :=
  HasAxiomVerum.verumProof

omit [LogicalConnective F] in
@[simp]
lemma verum [LogicalNeutral F] [HasAxiomVerum 𝓢] : 𝓢 ⊢ ⊤ :=
  ⟨verumProof⟩

/-- Proofs of the implication-K axiom in the given proof system. -/
class HasAxiomImplyK (𝓢 : S) where
  /-- The imply K! construction in `FFL.Entailment`. -/
  implyKProof {φ ψ : F} : 𝓢 ⊢! Axioms.ImplyK φ ψ
export HasAxiomImplyK (implyKProof)

@[simp]
lemma implyK [HasAxiomImplyK 𝓢] : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ φ :=
  ⟨implyKProof⟩

/-- The C! of conseq! construction in `FFL.Entailment`. -/
def CProofOfConseqProof [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ⇒ₗ φ :=
  implyKProof⨀h
alias dhypProof := CProofOfConseqProof

lemma C_of_conseq [ModusPonens 𝓢] [HasAxiomImplyK 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ ψ ⇒ₗ φ :=
  ⟨CProofOfConseqProof d.some⟩
alias dhyp := C_of_conseq

/-- Proofs of the implication-S axiom in the given proof system. -/
class HasAxiomImplyS (𝓢 : S) where
  /-- The imply S! construction in `FFL.Entailment`. -/
  implySProof {φ ψ χ : F} : 𝓢 ⊢! Axioms.ImplyS φ ψ χ
export HasAxiomImplyS (implySProof)

@[simp]
lemma implyS [HasAxiomImplyS 𝓢] : 𝓢 ⊢ (φ ⇒ₗ ψ ⇒ₗ χ) ⇒ₗ (φ ⇒ₗ ψ) ⇒ₗ φ ⇒ₗ χ :=
  ⟨implySProof⟩

/-- Proofs of the two conjunction-elimination axioms. -/
class HasAxiomAndElim (𝓢 : S) where
  /-- The and₁! construction in `FFL.Entailment`. -/
  and₁Proof {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₁ φ ψ
  /-- The and₂! construction in `FFL.Entailment`. -/
  and₂Proof {φ ψ : F} : 𝓢 ⊢! Axioms.AndElim₂ φ ψ
export HasAxiomAndElim (and₁Proof and₂Proof)

@[simp]
lemma and₁ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ⇒ₗ φ :=
  ⟨and₁Proof⟩

/-- The K! left construction in `FFL.Entailment`. -/
def KProofLeft [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! φ :=
  and₁Proof⨀d
@[grind ->]
lemma K_left [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ φ :=
  ⟨KProofLeft d.some⟩

@[simp]
lemma and₂ [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ⇒ₗ ψ :=
  ⟨and₂Proof⟩

/-- The K! right construction in `FFL.Entailment`. -/
def KProofRight [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ :=
  and₂Proof⨀d
@[grind ->]
lemma K_right [ModusPonens 𝓢] [HasAxiomAndElim 𝓢] (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ :=
  ⟨KProofRight d.some⟩

/-- Proofs of the conjunction-introduction axiom. -/
class HasAxiomAndInst (𝓢 : S) where
  /-- The and₃! construction in `FFL.Entailment`. -/
  and₃Proof {φ ψ : F} : 𝓢 ⊢! Axioms.AndInst φ ψ
export HasAxiomAndInst (and₃Proof)

@[simp]
lemma and₃ [HasAxiomAndInst 𝓢] : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ φ ⋏ ψ :=
  ⟨and₃Proof⟩

/-- The K! intro construction in `FFL.Entailment`. -/
def KProofIntro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢! φ) (d₂ : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋏ ψ :=
  and₃Proof⨀d₁⨀d₂
@[grind <-]
lemma K_intro [ModusPonens 𝓢] [HasAxiomAndInst 𝓢] (d₁ : 𝓢 ⊢ φ) (d₂ : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋏ ψ :=
  ⟨KProofIntro d₁.some d₂.some⟩

/-- Data and laws for Has Axiom Or Inst in `FFL.Entailment`. -/
class HasAxiomOrInst (𝓢 : S) where
  /-- The or₁! construction in `FFL.Entailment`. -/
  or₁Proof {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₁ φ ψ
  /-- The or₂! construction in `FFL.Entailment`. -/
  or₂Proof {φ ψ : F} : 𝓢 ⊢! Axioms.OrInst₂ φ ψ
export HasAxiomOrInst (or₁Proof or₂Proof)

@[simp]
lemma or₁ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ φ ⇒ₗ φ ⋎ ψ :=
  ⟨or₁Proof⟩

/-- The A! intro left construction in `FFL.Entailment`. -/
def AProofIntroLeft [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! φ) : 𝓢 ⊢! φ ⋎ ψ :=
  or₁Proof⨀d
@[grind .]
lemma A_intro_left [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ φ) : 𝓢 ⊢ φ ⋎ ψ :=
  ⟨AProofIntroLeft d.some⟩

@[simp]
lemma or₂ [HasAxiomOrInst 𝓢] : 𝓢 ⊢ ψ ⇒ₗ φ ⋎ ψ :=
  ⟨or₂Proof⟩

/-- The A! intro right construction in `FFL.Entailment`. -/
def AProofIntroRight [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢! ψ) : 𝓢 ⊢! φ ⋎ ψ :=
  or₂Proof⨀d
@[grind .]
lemma A_intro_right [HasAxiomOrInst 𝓢] [ModusPonens 𝓢] (d : 𝓢 ⊢ ψ) : 𝓢 ⊢ φ ⋎ ψ :=
  ⟨AProofIntroRight d.some⟩

/-- Data and laws for Has Axiom Or Elim in `FFL.Entailment`. -/
class HasAxiomOrElim (𝓢 : S) where
  /-- The or₃! construction in `FFL.Entailment`. -/
  or₃Proof {φ ψ χ : F} : 𝓢 ⊢! Axioms.OrElim φ ψ χ
export HasAxiomOrElim (or₃Proof)

@[simp]
lemma or₃ [HasAxiomOrElim 𝓢] : 𝓢 ⊢ (φ ⇒ₗ χ) ⇒ₗ (ψ ⇒ₗ χ) ⇒ₗ (φ ⋎ ψ) ⇒ₗ χ :=
  ⟨or₃Proof⟩

/-- The left A! intro construction in `FFL.Entailment`. -/
def leftAProofIntro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ⇒ₗ χ) (d₂ : 𝓢 ⊢! ψ ⇒ₗ χ) :
    𝓢 ⊢! φ ⋎ ψ ⇒ₗ χ :=
  or₃Proof⨀d₁⨀d₂
alias CAProofOfCProofOfCProof := leftAProofIntro

lemma left_A_intro [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ⇒ₗ χ) (d₂ : 𝓢 ⊢ ψ ⇒ₗ χ) :
    𝓢 ⊢ φ ⋎ ψ ⇒ₗ χ :=
  ⟨leftAProofIntro d₁.some d₂.some⟩
alias CA_of_C_of_C := left_A_intro

/-- The of C! of C! of A! construction in `FFL.Entailment`. -/
def ofCProofOfCProofOfAProof [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢! φ ⇒ₗ χ)
    (d₂ : 𝓢 ⊢! ψ ⇒ₗ χ) (d₃ : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! χ :=
  or₃Proof⨀d₁⨀d₂⨀d₃
alias AProofCases := ofCProofOfCProofOfAProof

lemma of_C_of_C_of_A [HasAxiomOrElim 𝓢] [ModusPonens 𝓢] (d₁ : 𝓢 ⊢ φ ⇒ₗ χ) (d₂ : 𝓢 ⊢ ψ ⇒ₗ χ)
    (d₃ : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ χ :=
  ⟨ofCProofOfCProofOfAProof d₁.some d₂.some d₃.some⟩
alias A_cases := of_C_of_C_of_A

/-- Data and laws for Minimal in `FFL.Entailment`. -/
protected class Minimal [LogicalNeutral F] (𝓢 : S) extends ModusPonens 𝓢, NegationEquiv 𝓢,
    HasAxiomVerum 𝓢, HasAxiomImplyK 𝓢, HasAxiomImplyS 𝓢, HasAxiomAndElim 𝓢, HasAxiomAndInst 𝓢,
    HasAxiomOrInst 𝓢, HasAxiomOrElim 𝓢

end

section

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} [ModusPonens 𝓢] {φ ψ χ : F}

/-- The CO! of N! construction in `FFL.Entailment`. -/
def COProofOfNProof [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢! ∼φ → 𝓢 ⊢! φ ⇒ₗ ⊥ := fun h => (KProofLeft negEquivProof)⨀h
/-- The N! of CO! construction in `FFL.Entailment`. -/
def NProofOfCOProof [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] :
    𝓢 ⊢! φ ⇒ₗ ⊥ → 𝓢 ⊢! ∼φ := fun h => (KProofRight negEquivProof)⨀h
@[grind =]
lemma N_iff_CO [LogicalNeutral F] [HasAxiomAndElim 𝓢] [NegationEquiv 𝓢] : 𝓢 ⊢ ∼φ ↔ 𝓢 ⊢ φ ⇒ₗ ⊥ :=
  ⟨fun ⟨h⟩ => ⟨COProofOfNProof h⟩, fun ⟨h⟩ => ⟨NProofOfCOProof h⟩⟩

/-- The E! intro construction in `FFL.Entailment`. -/
def EProofIntro [HasAxiomAndInst 𝓢] (b₁ : 𝓢 ⊢! φ ⇒ₗ ψ) (b₂ : 𝓢 ⊢! ψ ⇒ₗ φ) : 𝓢 ⊢! φ ⇔ₗ ψ :=
  KProofIntro b₁ b₂
@[grind ←]
lemma E_intro [HasAxiomAndInst 𝓢] (h₁ : 𝓢 ⊢ φ ⇒ₗ ψ) (h₂ : 𝓢 ⊢ ψ ⇒ₗ φ) : 𝓢 ⊢ φ ⇔ₗ ψ :=
  ⟨KProofIntro h₁.some h₂.some⟩

@[grind =]
lemma K_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⋏ ψ ↔ 𝓢 ⊢ φ ∧ 𝓢 ⊢ ψ := by
  grind
@[grind =]
lemma E_intro_iff [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] :
    𝓢 ⊢ φ ⇔ₗ ψ ↔ 𝓢 ⊢ φ ⇒ₗ ψ ∧ 𝓢 ⊢ ψ ⇒ₗ φ :=
  ⟨fun h ↦ ⟨K_left h, K_right h⟩, by grind⟩

/-- The C! of E! mp construction in `FFL.Entailment`. -/
def CProofOfEProofMp [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⇔ₗ ψ) : 𝓢 ⊢! φ ⇒ₗ ψ :=
  KProofLeft h
@[grind →]
lemma C_of_E_mp [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⇔ₗ ψ → 𝓢 ⊢ φ ⇒ₗ ψ := fun ⟨d⟩ => ⟨CProofOfEProofMp d⟩

/-- The C! of E! mpr construction in `FFL.Entailment`. -/
def CProofOfEProofMpr [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢! φ ⇔ₗ ψ) : 𝓢 ⊢! ψ ⇒ₗ φ :=
  KProofRight h
@[grind →]
lemma C_of_E_mpr [HasAxiomAndElim 𝓢] : 𝓢 ⊢ φ ⇔ₗ ψ → 𝓢 ⊢ ψ ⇒ₗ φ := fun ⟨d⟩ =>
  ⟨CProofOfEProofMpr d⟩

@[grind →]
lemma iff_of_E [HasAxiomAndElim 𝓢] (h : 𝓢 ⊢ φ ⇔ₗ ψ) : 𝓢 ⊢ φ ↔ 𝓢 ⊢ ψ :=
  ⟨fun hp ↦ K_left h⨀hp, fun hq ↦ K_right h⨀hq⟩

/-- The C! id construction in `FFL.Entailment`. -/
def CProofId [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ ⇒ₗ φ :=
  implySProof (φ := φ) (ψ := (φ ⇒ₗ φ)) (χ := φ)⨀implyKProof⨀implyKProof
@[simp]
theorem C_id [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⇒ₗ φ :=
  ⟨CProofId⟩

/-- The E! id construction in `FFL.Entailment`. -/
def EProofId [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] {φ : F} : 𝓢 ⊢! φ ⇔ₗ φ :=
  KProofIntro CProofId CProofId
@[simp]
theorem E_id [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⇔ₗ φ :=
  ⟨EProofId⟩

instance [LogicalNeutral F] [NegAbbrev F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    [HasAxiomAndInst 𝓢] : Entailment.NegationEquiv 𝓢 where
  negEquivProof
    {φ} :=
    by
    suffices 𝓢 ⊢! (φ ⇒ₗ ⊥) ⇔ₗ (φ ⇒ₗ ⊥) by simpa [Axioms.NegEquiv, NegAbbrev.neg];
    apply EProofId;

/-- The NO! construction in `FFL.Entailment`. -/
def NOProof [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢]
    [HasAxiomAndElim 𝓢] : 𝓢 ⊢! ∼⊥ :=
  NProofOfCOProof CProofId
@[simp]
lemma NO [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] [NegationEquiv 𝓢]
    [HasAxiomAndElim 𝓢] : 𝓢 ⊢ ∼⊥ :=
  ⟨NOProof⟩

/-- The mdp₁! construction in `FFL.Entailment`. -/
def mdp₁Proof [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ) (bq : 𝓢 ⊢! φ ⇒ₗ ψ) : 𝓢 ⊢! φ ⇒ₗ χ :=
  implySProof⨀bqr⨀bq
@[grind →]
lemma mdp₁ [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ) (hq : 𝓢 ⊢ φ ⇒ₗ ψ) : 𝓢 ⊢ φ ⇒ₗ χ :=
  ⟨mdp₁Proof hqr.some hq.some⟩

/-- The «term ⨀₁ » construction in `FFL.Entailment`. -/
infixl:90 "⨀₁" => mdp₁Proof
/-- The «term ⨀₁  1» construction in `FFL.Entailment`. -/
infixl:90 "⨀₁" => mdp₁

/-- The mdp₂! construction in `FFL.Entailment`. -/
def mdp₂Proof [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s)
    (bq : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ s :=
  CProofOfConseqProof (implySProof)⨀₁bqr⨀₁bq
@[grind →]
lemma mdp₂ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s)
    (hq : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ) : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ s :=
  ⟨mdp₂Proof hqr.some hq.some⟩

/-- The «term ⨀₂ » construction in `FFL.Entailment`. -/
infixl:90 "⨀₂" => mdp₂Proof
/-- The «term ⨀₂  1» construction in `FFL.Entailment`. -/
infixl:90 "⨀₂" => mdp₂

/-- The mdp₃! construction in `FFL.Entailment`. -/
def mdp₃Proof [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ t)
    (bq : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s) : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ t :=
  (CProofOfConseqProof <| CProofOfConseqProof <| implySProof)⨀₂bqr⨀₂bq
@[grind →]
lemma mdp₃ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ t)
    (hq : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s) : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ t :=
  ⟨mdp₃Proof hqr.some hq.some⟩

/-- The «term ⨀₃ » construction in `FFL.Entailment`. -/
infixl:90 "⨀₃" => mdp₃Proof
/-- The «term ⨀₃  1» construction in `FFL.Entailment`. -/
infixl:90 "⨀₃" => mdp₃

/-- The mdp₄! construction in `FFL.Entailment`. -/
def mdp₄Proof [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bqr : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ t ⇒ₗ u)
    (bq : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ t) : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ u :=
  (CProofOfConseqProof <| CProofOfConseqProof <| CProofOfConseqProof <| implySProof)⨀₃bqr⨀₃bq
@[grind →]
lemma mdp₄ [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hqr : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ t ⇒ₗ u)
    (hq : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ t) : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ s ⇒ₗ u :=
  ⟨mdp₄Proof hqr.some hq.some⟩
/-- The «term ⨀₄ » construction in `FFL.Entailment`. -/
infixl:90 "⨀₄" => mdp₄Proof
/-- The «term ⨀₄  1» construction in `FFL.Entailment`. -/
infixl:90 "⨀₄" => mdp₄

/-- The C! trans construction in `FFL.Entailment`. -/
def CProofTrans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (bpq : 𝓢 ⊢! φ ⇒ₗ ψ) (bqr : 𝓢 ⊢! ψ ⇒ₗ χ) :
    𝓢 ⊢! φ ⇒ₗ χ :=
  implySProof⨀CProofOfConseqProof bqr⨀bpq
@[grind <=]
lemma C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ ⇒ₗ ψ) (hqr : 𝓢 ⊢ ψ ⇒ₗ χ) :
    𝓢 ⊢ φ ⇒ₗ χ :=
  ⟨CProofTrans hpq.some hqr.some⟩

/-- The C! replace construction in `FFL.Entailment`. -/
def CProofReplace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢! ψ₁ ⇒ₗ φ₁)
    (h₂ : 𝓢 ⊢! φ₂ ⇒ₗ ψ₂) : 𝓢 ⊢! φ₁ ⇒ₗ φ₂ → 𝓢 ⊢! ψ₁ ⇒ₗ ψ₂ := fun h =>
  CProofTrans h₁ <| CProofTrans h h₂
lemma C_replace [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (h₁ : 𝓢 ⊢ ψ₁ ⇒ₗ φ₁) (h₂ : 𝓢 ⊢ φ₂ ⇒ₗ ψ₂) :
    𝓢 ⊢ φ₁ ⇒ₗ φ₂ → 𝓢 ⊢ ψ₁ ⇒ₗ ψ₂ := fun h => ⟨CProofReplace h₁.some h₂.some h.some⟩

/-- The E! replace construction in `FFL.Entailment`. -/
def EProofReplace [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h₁ : 𝓢 ⊢! φ₁ ⇔ₗ ψ₁) (h₂ : 𝓢 ⊢! φ₂ ⇔ₗ ψ₂) (h₃ : 𝓢 ⊢! φ₁ ⇔ₗ φ₂) : 𝓢 ⊢! ψ₁ ⇔ₗ ψ₂ :=
  by
  apply EProofIntro;
  · exact CProofReplace (CProofOfEProofMpr h₁) (CProofOfEProofMp h₂) (CProofOfEProofMp h₃);
  · exact CProofReplace (CProofOfEProofMpr h₂) (CProofOfEProofMp h₁) (CProofOfEProofMpr h₃);
lemma E_replace [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢ φ₁ ⇔ₗ ψ₁ → 𝓢 ⊢ φ₂ ⇔ₗ ψ₂ → 𝓢 ⊢ φ₁ ⇔ₗ φ₂ → 𝓢 ⊢ ψ₁ ⇔ₗ ψ₂ := fun ⟨d₁⟩ ⟨d₂⟩ ⟨d₃⟩ =>
  ⟨EProofReplace d₁ d₂ d₃⟩

/-- The E! trans construction in `FFL.Entailment`. -/
def EProofTrans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h₁ : 𝓢 ⊢! φ ⇔ₗ ψ) (h₂ : 𝓢 ⊢! ψ ⇔ₗ χ) : 𝓢 ⊢! φ ⇔ₗ χ :=
  by
  apply EProofIntro; · exact CProofTrans (KProofLeft h₁) (KProofLeft h₂);
  · exact CProofTrans (KProofRight h₂) (KProofRight h₁);
@[grind <=]
lemma E_trans [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h₁ : 𝓢 ⊢ φ ⇔ₗ ψ) (h₂ : 𝓢 ⊢ ψ ⇔ₗ χ) : 𝓢 ⊢ φ ⇔ₗ χ :=
  ⟨EProofTrans h₁.some h₂.some⟩

/-- The CCCC! construction in `FFL.Entailment`. -/
def CCCCProof [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ φ :=
  CProofTrans implyKProof implyKProof
@[grind .]
lemma CCCC [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] : 𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ ⇒ₗ φ :=
  ⟨CCCCProof⟩

/-- The CK! of C! of C! construction in `FFL.Entailment`. -/
def CKProofOfCProofOfCProof [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (bq : 𝓢 ⊢! φ ⇒ₗ ψ) (br : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! φ ⇒ₗ ψ ⋏ χ :=
  CProofOfConseqProof and₃Proof⨀₁bq⨀₁br
@[grind <=]
lemma CK_of_C_of_C [HasAxiomAndInst 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hq : 𝓢 ⊢ φ ⇒ₗ ψ)
    (hr : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ φ ⇒ₗ ψ ⋏ χ :=
  ⟨CKProofOfCProofOfCProof hq.some hr.some⟩

/-- The CKK! construction in `FFL.Entailment`. -/
def CKKProof [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢! φ ⋏ ψ ⇒ₗ ψ ⋏ φ :=
  CKProofOfCProofOfCProof and₂Proof and₁Proof
@[simp, grind .]
lemma CKK [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢ φ ⋏ ψ ⇒ₗ ψ ⋏ φ :=
  ⟨CKKProof⟩

/-- The K! symm construction in `FFL.Entailment`. -/
def KProofSymm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ψ ⋏ φ :=
  CKKProof⨀h
@[grind <-]
lemma K_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ψ ⋏ φ :=
  ⟨KProofSymm h.some⟩

/-- The CEE! construction in `FFL.Entailment`. -/
def CEEProof [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢! (φ ⇔ₗ ψ) ⇒ₗ (ψ ⇔ₗ φ) :=
  CKKProof
@[simp]
lemma CEE [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢ (φ ⇔ₗ ψ) ⇒ₗ (ψ ⇔ₗ φ) :=
  ⟨CEEProof⟩

/-- The E! symm construction in `FFL.Entailment`. -/
def EProofSymm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h : 𝓢 ⊢! φ ⇔ₗ ψ) : 𝓢 ⊢! ψ ⇔ₗ φ :=
  CEEProof⨀h
@[grind <-]
lemma E_symm [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢]
    (h : 𝓢 ⊢ φ ⇔ₗ ψ) : 𝓢 ⊢ ψ ⇔ₗ φ :=
  ⟨EProofSymm h.some⟩

/-- The ECKCC! construction in `FFL.Entailment`. -/
def ECKCCProof [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢! (φ ⋏ ψ ⇒ₗ χ) ⇔ₗ (φ ⇒ₗ ψ ⇒ₗ χ) :=
  by
  let b₁ : 𝓢 ⊢! (φ ⋏ ψ ⇒ₗ χ) ⇒ₗ φ ⇒ₗ ψ ⇒ₗ χ :=
    CCCCProof⨀₃CProofOfConseqProof (ψ := φ ⋏ ψ ⇒ₗ χ) and₃Proof
  let b₂ : 𝓢 ⊢! (φ ⇒ₗ ψ ⇒ₗ χ) ⇒ₗ φ ⋏ ψ ⇒ₗ χ :=
    implyKProof⨀₂(CProofOfConseqProof (ψ := φ ⇒ₗ ψ ⇒ₗ χ)
          and₁Proof)⨀₂(CProofOfConseqProof (ψ := φ ⇒ₗ ψ ⇒ₗ χ) and₂Proof);
  exact EProofIntro b₁ b₂
@[simp, grind .]
lemma ECKCC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    𝓢 ⊢ (φ ⋏ ψ ⇒ₗ χ) ⇔ₗ (φ ⇒ₗ ψ ⇒ₗ χ) :=
  ⟨ECKCCProof⟩

/-- The CC! of CK! construction in `FFL.Entailment`. -/
def CCProofOfCKProof [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ ⋏ ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ :=
  (KProofLeft <| ECKCCProof)⨀d
/-- The CK! of CC! construction in `FFL.Entailment`. -/
def CKProofOfCCProof [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢]
    [HasAxiomImplyS 𝓢] (d : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⋏ ψ ⇒ₗ χ :=
  (KProofRight <| ECKCCProof)⨀d

@[grind =]
lemma CK_iff_CC [HasAxiomAndInst 𝓢] [HasAxiomAndElim 𝓢] [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] :
    (𝓢 ⊢ φ ⋏ ψ ⇒ₗ χ) ↔ (𝓢 ⊢ φ ⇒ₗ ψ ⇒ₗ χ) :=
  iff_of_E ECKCC

/-- The CV! construction in `FFL.Entailment`. -/
def CVProof [LogicalNeutral F] [HasAxiomVerum 𝓢] [HasAxiomImplyK 𝓢] : 𝓢 ⊢! φ ⇒ₗ ⊤ :=
  CProofOfConseqProof verumProof
@[simp]
lemma CV [LogicalNeutral F] [HasAxiomImplyK 𝓢] [HasAxiomVerum 𝓢] : 𝓢 ⊢ φ ⇒ₗ ⊤ :=
  ⟨CVProof⟩

@[grind →]
lemma unprovable_C_trans [HasAxiomImplyK 𝓢] [HasAxiomImplyS 𝓢] (hpq : 𝓢 ⊢ φ ⇒ₗ ψ) :
    𝓢 ⊬ φ ⇒ₗ χ → 𝓢 ⊬ ψ ⇒ₗ χ := by contrapose!; exact C_trans hpq;

@[grind →]
lemma uniff_of_E [HasAxiomAndElim 𝓢] (H : 𝓢 ⊢ φ ⇔ₗ ψ) : 𝓢 ⊬ φ ↔ 𝓢 ⊬ ψ :=
  by
  constructor; · intro hp hq; have := K_right H⨀hq; contradiction;
  · intro hq hp; have := K_left H⨀hp; contradiction;

end

section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [Entailment S F]
variable {𝓢 : S} [Entailment.Minimal 𝓢] {φ ψ χ : F}

variable {Γ Δ : List F}

/-- The conj₂Nth! construction in `FFL.Entailment`. -/
def conj₂NthProof : (Γ : List F) → (n : ℕ) → (hn : n < Γ.length) → 𝓢 ⊢! ⋀Γ ⇒ₗ Γ[n]
  | [], _, hn => by simp at hn
  | [ψ], 0, _ => CProofId
  | φ :: ψ :: Γ, 0, _ => and₁Proof
  | φ :: ψ :: Γ, n + 1, hn =>
    CProofTrans (and₂Proof (φ := φ)) (conj₂NthProof (ψ :: Γ) n (Nat.succ_lt_succ_iff.mp hn))

theorem conj₂_nth (Γ : List F) (n : ℕ) (hn : n < Γ.length) : 𝓢 ⊢ ⋀Γ ⇒ₗ Γ[n] :=
  ⟨conj₂NthProof Γ n hn⟩

/-- The left Conj! intro construction in `FFL.Entailment`. -/
def leftConjProofIntro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) :
    𝓢 ⊢! (PointwiseComposition.List.conj Γ) ⇒ₗ φ :=
  match Γ with
  | [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then e ▸ and₁Proof
    else
      have : φ ∈ Γ := by simpa [e] using h
      CProofTrans and₂Proof (leftConjProofIntro this)
lemma left_Conj_intro (h : φ ∈ Γ) : 𝓢 ⊢ (PointwiseComposition.List.conj Γ) ⇒ₗ φ := by
  classical exact ⟨leftConjProofIntro h⟩
/-- The Conj! intro construction in `FFL.Entailment`. -/
def ConjProofIntro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) :
    𝓢 ⊢! (PointwiseComposition.List.conj Γ) :=
  match Γ with
  | [] => verumProof
  | ψ :: Γ => KProofIntro (b ψ (by simp)) (ConjProofIntro Γ (fun ψ hq ↦ b ψ (by simp [hq])))
lemma Conj_intro {Γ : List F} (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) :
    𝓢 ⊢ (PointwiseComposition.List.conj Γ) :=
  ⟨ConjProofIntro Γ fun φ hφ => (b φ hφ).some⟩

/-- The right Conj! intro construction in `FFL.Entailment`. -/
def rightConjProofIntro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ⇒ₗ ψ) :
    𝓢 ⊢! φ ⇒ₗ (PointwiseComposition.List.conj Γ) :=
  match Γ with
  | [] => CProofOfConseqProof verumProof
  | ψ :: Γ =>
    CKProofOfCProofOfCProof (b ψ (by simp))
      (rightConjProofIntro φ Γ (fun ψ hq ↦ b ψ (by simp [hq])))
theorem right_Conj_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ⇒ₗ ψ) :
    𝓢 ⊢ φ ⇒ₗ (PointwiseComposition.List.conj Γ) :=
  ⟨rightConjProofIntro φ Γ fun ψ h ↦ (b ψ h).get⟩

/-- The CConj Conj! construction in `FFL.Entailment`. -/
def CConjConjProof [DecidableEq F] (h : Δ ⊆ Γ) :
    𝓢 ⊢! (PointwiseComposition.List.conj Γ) ⇒ₗ (PointwiseComposition.List.conj Δ) :=
  rightConjProofIntro _ _ (fun _ hq ↦ leftConjProofIntro (h hq))

/-- The left Conj₂! intro construction in `FFL.Entailment`. -/
def leftConj₂ProofIntro [DecidableEq F] {Γ : List F} {φ : F} (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ⇒ₗ φ :=
  have : Γ.idxOf φ < Γ.length := List.idxOf_lt_length_of_mem h
  cast <| conj₂NthProof Γ (Γ.idxOf φ) (by assumption)
lemma left_Conj₂_intro (h : φ ∈ Γ) : 𝓢 ⊢ ⋀Γ ⇒ₗ φ := by classical exact ⟨leftConj₂ProofIntro h⟩
/-- The Conj₂! intro construction in `FFL.Entailment`. -/
def Conj₂ProofIntro (Γ : List F) (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢! φ) : 𝓢 ⊢! ⋀Γ :=
  match Γ with
  | [] => verumProof
  | [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by exact KProofIntro (b ψ (by simp)) (Conj₂ProofIntro _ (by aesop))
lemma Conj₂_intro (b : (φ : F) → φ ∈ Γ → 𝓢 ⊢ φ) : 𝓢 ⊢ ⋀Γ :=
  ⟨Conj₂ProofIntro Γ (fun φ hp => (b φ hp).some)⟩

/-- The right Conj₂! intro construction in `FFL.Entailment`. -/
def rightConj₂ProofIntro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! φ ⇒ₗ ψ) :
    𝓢 ⊢! φ ⇒ₗ ⋀Γ :=
  match Γ with
  | [] => CProofOfConseqProof verumProof
  | [ψ] => by apply b; simp;
  | ψ :: χ :: Γ => by
    apply
      CKProofOfCProofOfCProof (b ψ (by simp))
        (rightConj₂ProofIntro φ _ (fun ψ hq ↦ b ψ (by simp [hq])));
lemma right_Conj₂_intro (φ : F) (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ φ ⇒ₗ ψ) : 𝓢 ⊢ φ ⇒ₗ ⋀Γ :=
  ⟨rightConj₂ProofIntro φ Γ (fun ψ hq => (b ψ hq).some)⟩

/-- The CConj₂Conj₂! construction in `FFL.Entailment`. -/
def CConj₂Conj₂Proof [DecidableEq F] {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢! ⋀Γ ⇒ₗ ⋀Δ :=
  rightConj₂ProofIntro _ _ (fun _ hq ↦ leftConj₂ProofIntro (h hq))
lemma CConj₂Conj₂ {Γ Δ : List F} (h : Δ ⊆ Γ) : 𝓢 ⊢ ⋀Γ ⇒ₗ ⋀Δ := by
  classical exact ⟨CConj₂Conj₂Proof h⟩
section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

/-- The of Equiv construction in `FFL.Entailment.Minimal`. -/
abbrev Minimal.ofEquiv (𝓢 : S) [Entailment.Minimal 𝓢] (𝓣 : T) (f : G →ˡᶜ F)
    (e : (φ : G) → 𝓢 ⊢! f φ ≃ 𝓣 ⊢! φ) : Entailment.Minimal 𝓣
    where
  mdpProof
    {φ ψ dpq dp} :=
    (e ψ)
      (let d : 𝓢 ⊢! f φ ⇒ₗ f ψ := by simpa using (e (φ ⇒ₗ ψ)).symm dpq
      d⨀((e φ).symm dp))
  negEquivProof := e _ (by simpa using negEquivProof)
  verumProof := e _ (by simpa using verumProof)
  implyKProof := e _ (by simpa using implyKProof)
  implySProof := e _ (by simpa using implySProof)
  and₁Proof := e _ (by simpa using and₁Proof)
  and₂Proof := e _ (by simpa using and₂Proof)
  and₃Proof := e _ (by simpa using and₃Proof)
  or₁Proof := e _ (by simpa using or₁Proof)
  or₂Proof := e _ (by simpa using or₂Proof)
  or₃Proof := e _ (by simpa using or₃Proof)

end

end

section

/-- Data and laws for Finite Context in `FFL.Entailment`. -/
structure FiniteContext (F) (𝓢 : S) where
  /-- The ctx construction in `FFL.Entailment.FiniteContext`. -/
  ctx : List F

namespace FiniteContext

variable {F} {S} {𝓢 : S}

instance : Coe (List F) (FiniteContext F 𝓢) :=
  ⟨mk⟩

/-- The conj construction in `FFL.Entailment.FiniteContext`. -/
abbrev conj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F :=
  ⋀Γ.ctx

/-- The disj construction in `FFL.Entailment.FiniteContext`. -/
abbrev disj [LogicalConnective F] [LogicalNeutral F] (Γ : FiniteContext F 𝓢) : F :=
  ⋁Γ.ctx

instance : EmptyCollection (FiniteContext F 𝓢) :=
  ⟨⟨[]⟩⟩

instance : Membership F (FiniteContext F 𝓢) :=
  ⟨fun Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (FiniteContext F 𝓢) :=
  ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (FiniteContext F 𝓢) :=
  ⟨(· :: ·.ctx)⟩

lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx :=
  iff_of_eq rfl

@[simp]
lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ :=
  iff_of_eq rfl

@[simp]
lemma mem_coe_iff {φ : F} {Γ : List F} : φ ∈ (Γ : FiniteContext F 𝓢) ↔ φ ∈ Γ :=
  iff_of_eq rfl

lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : FiniteContext F 𝓢) := by
  simp [EmptyCollection.emptyCollection]

instance : AdjunctiveSet F (FiniteContext F 𝓢)
    where
  subset_iff := List.subset_def
  not_mem_empty := not_mem_empty
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [Entailment S F] [LogicalConnective F] [LogicalNeutral F]

instance (𝓢 : S) : Entailment (FiniteContext F 𝓢) F :=
  ⟨(𝓢 ⊢! ·.conj ⇒ₗ ·)⟩

/-- The Prf construction in `FFL.Entailment.FiniteContext`. -/
abbrev Prf (𝓢 : S) (Γ : List F) (φ : F) : Type _ :=
  (Γ : FiniteContext F 𝓢) ⊢! φ

/-- The Provable construction in `FFL.Entailment.FiniteContext`. -/
abbrev Provable (𝓢 : S) (Γ : List F) (φ : F) : Prop :=
  (Γ : FiniteContext F 𝓢) ⊢ φ

/-- The Unprovable construction in `FFL.Entailment.FiniteContext`. -/
abbrev Unprovable (𝓢 : S) (Γ : List F) (φ : F) : Prop :=
  (Γ : FiniteContext F 𝓢) ⊬ φ

/-- The Prf Set construction in `FFL.Entailment.FiniteContext`. -/
abbrev PrfSet (𝓢 : S) (Γ : List F) (s : Set F) : Type _ :=
  (Γ : FiniteContext F 𝓢) ⊢!* s

/-- The Provable Set construction in `FFL.Entailment.FiniteContext`. -/
abbrev ProvableSet (𝓢 : S) (Γ : List F) (s : Set F) : Prop :=
  (Γ : FiniteContext F 𝓢) ⊢* s

/-- The «term ⊢[ ]! » construction in `FFL.Entailment.FiniteContext`. -/
notation Γ:45 " ⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

/-- The «term ⊢[ ] » construction in `FFL.Entailment.FiniteContext`. -/
notation Γ:45 " ⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

/-- The «term ⊬[ ] » construction in `FFL.Entailment.FiniteContext`. -/
notation Γ:45 " ⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

/-- The «term ⊢[ ]!* » construction in `FFL.Entailment.FiniteContext`. -/
notation Γ:45 " ⊢[" 𝓢 "]!* " s:46 => PrfSet 𝓢 Γ s

/-- The «term ⊢[ ]* » construction in `FFL.Entailment.FiniteContext`. -/
notation Γ:45 " ⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) : (Γ ⊢! φ) = (𝓢 ⊢! Γ.conj ⇒ₗ φ) :=
  rfl

/-- The of Def! construction in `FFL.Entailment.FiniteContext`. -/
def ofDefProof {Γ : List F} {φ : F} (b : 𝓢 ⊢! ⋀Γ ⇒ₗ φ) : Γ ⊢[𝓢]! φ :=
  b

/-- The to Def! construction in `FFL.Entailment.FiniteContext`. -/
def toDefProof {Γ : List F} {φ : F} (b : Γ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Γ ⇒ₗ φ :=
  b

lemma toₛ (b : Γ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Γ ⇒ₗ φ :=
  b

lemma provable_iff {φ : F} : Γ ⊢[𝓢] φ ↔ 𝓢 ⊢ ⋀Γ ⇒ₗ φ :=
  iff_of_eq rfl

/-- The cast! construction in `FFL.Entailment.FiniteContext`. -/
def castProof {Γ φ} (d : Γ ⊢[𝓢]! φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Γ' ⊢[𝓢]! φ' :=
  eΓ ▸ eφ ▸ d

section

variable {Γ Δ E : List F}
variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢)
    where
  prfAxm := fun hp ↦ leftConj₂ProofIntro hp
  weakening := fun H b ↦ CProofTrans (CConj₂Conj₂Proof H) b

instance : Compact (FiniteContext F 𝓢)
    where
  core := fun {Γ} _ _ ↦ Γ
  corePrf := id
  core_subset := by simp
  core_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

/-- The nth Axm! construction in `FFL.Entailment.FiniteContext`. -/
def nthAxmProof {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢]! Γ[n] :=
  conj₂NthProof Γ n h
lemma nth_axm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Γ ⊢[𝓢] Γ[n] :=
  ⟨nthAxmProof n h⟩

/-- The by Axm! construction in `FFL.Entailment.FiniteContext`. -/
def byAxmProof [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Γ ⊢[𝓢]! φ :=
  Axiomatized.prfAxm (by simpa)

lemma by_axm {φ} (h : φ ∈ Γ := by classical simp) : Γ ⊢[𝓢] φ := by
  classical exact Axiomatized.provable_refl _ (by simpa)

/-- The weakening! construction in `FFL.Entailment.FiniteContext`. -/
def weakeningProof [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢]! φ → Δ ⊢[𝓢]! φ :=
  Axiomatized.weakening (by simpa)

lemma weakening (h : Γ ⊆ Δ) {φ} : Γ ⊢[𝓢] φ → Δ ⊢[𝓢] φ := by
  classical exact fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h
/-- The of! construction in `FFL.Entailment.FiniteContext`. -/
def ofProof {φ : F} (b : 𝓢 ⊢! φ) : Γ ⊢[𝓢]! φ :=
  CProofOfConseqProof (ψ := ⋀Γ) b

/-- The empty Prf! construction in `FFL.Entailment.FiniteContext`. -/
def emptyPrfProof {φ : F} : [] ⊢[𝓢]! φ → 𝓢 ⊢! φ := fun b ↦ b⨀verumProof

theorem provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ [] ⊢[𝓢] φ :=
  ⟨fun b ↦ ⟨ofProof b.some⟩, fun b ↦ ⟨emptyPrfProof b.some⟩⟩

lemma of' (h : 𝓢 ⊢ φ) : Γ ⊢[𝓢] φ := by
  classical exact weakening (by simp) <| provable_iff_provable.mp h
/-- The id! construction in `FFL.Entailment.FiniteContext`. -/
def idProof : [φ] ⊢[𝓢]! φ :=
  nthAxmProof 0
@[simp]
lemma id : [φ] ⊢[𝓢] φ :=
  nth_axm 0

/-- The by Axm₀! construction in `FFL.Entailment.FiniteContext`. -/
def byAxm₀Proof : (φ :: Γ) ⊢[𝓢]! φ :=
  nthAxmProof 0
lemma by_axm₀ : (φ :: Γ) ⊢[𝓢] φ :=
  nth_axm 0

/-- The by Axm₁! construction in `FFL.Entailment.FiniteContext`. -/
def byAxm₁Proof : (φ :: ψ :: Γ) ⊢[𝓢]! ψ :=
  nthAxmProof 1
lemma by_axm₁ : (φ :: ψ :: Γ) ⊢[𝓢] ψ :=
  nth_axm 1

/-- The by Axm₂! construction in `FFL.Entailment.FiniteContext`. -/
def byAxm₂Proof : (φ :: ψ :: χ :: Γ) ⊢[𝓢]! χ :=
  nthAxmProof 2
lemma by_axm₂ : (φ :: ψ :: χ :: Γ) ⊢[𝓢] χ :=
  nth_axm 2

instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ :=
  ⟨mdp₁Proof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ :=
  ⟨ofProof verumProof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyK Γ :=
  ⟨ofProof implyKProof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImplyS Γ :=
  ⟨ofProof implySProof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ :=
  ⟨ofProof and₁Proof, ofProof and₂Proof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ :=
  ⟨ofProof and₃Proof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ :=
  ⟨ofProof or₁Proof, ofProof or₂Proof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ :=
  ⟨ofProof or₃Proof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ :=
  ⟨ofProof negEquivProof⟩

instance (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where

/-- The mdp'! construction in `FFL.Entailment.FiniteContext`. -/
def mdp'Proof [DecidableEq F] (bΓ : Γ ⊢[𝓢]! φ ⇒ₗ ψ) (bΔ : Δ ⊢[𝓢]! φ) : (Γ ++ Δ) ⊢[𝓢]! ψ :=
  wk (by simp) bΓ⨀wk (by simp) bΔ

/-- The deduct! construction in `FFL.Entailment.FiniteContext`. -/
def deductProof {φ ψ : F} : {Γ : List F} → (φ :: Γ) ⊢[𝓢]! ψ → Γ ⊢[𝓢]! φ ⇒ₗ ψ
  | .nil => fun b ↦ ofDefProof <| CProofOfConseqProof (toDefProof b)
  | .cons _ _ => fun b ↦ ofDefProof <| CCProofOfCKProof (CProofTrans CKKProof (toDefProof b))

lemma deduct (h : (φ :: Γ) ⊢[𝓢] ψ) : Γ ⊢[𝓢] φ ⇒ₗ ψ :=
  ⟨FiniteContext.deductProof h.some⟩

/-- The deduct Inv! construction in `FFL.Entailment.FiniteContext`. -/
def deductInvProof {φ ψ : F} : {Γ : List F} → Γ ⊢[𝓢]! φ ⇒ₗ ψ → (φ :: Γ) ⊢[𝓢]! ψ
  | .nil => fun b => ofDefProof <| (toDefProof b)⨀verumProof
  | .cons _ _ => fun b => ofDefProof <| (CProofTrans CKKProof (CKProofOfCCProof (toDefProof b)))

lemma deductInv (h : Γ ⊢[𝓢] φ ⇒ₗ ψ) : (φ :: Γ) ⊢[𝓢] ψ :=
  ⟨FiniteContext.deductInvProof h.some⟩

lemma deduct_iff {φ ψ : F} {Γ : List F} : Γ ⊢[𝓢] φ ⇒ₗ ψ ↔ (φ :: Γ) ⊢[𝓢] ψ :=
  ⟨fun h ↦ ⟨deductInvProof h.some⟩, fun h ↦ ⟨deductProof h.some⟩⟩

/-- The deduct'! construction in `FFL.Entailment.FiniteContext`. -/
def deduct'Proof : [φ] ⊢[𝓢]! ψ → 𝓢 ⊢! φ ⇒ₗ ψ := fun b ↦ emptyPrfProof <| deductProof b

lemma deduct' (h : [φ] ⊢[𝓢] ψ) : 𝓢 ⊢ φ ⇒ₗ ψ :=
  ⟨FiniteContext.deduct'Proof h.some⟩

/-- The deduct Inv'! construction in `FFL.Entailment.FiniteContext`. -/
def deductInv'Proof : 𝓢 ⊢! φ ⇒ₗ ψ → [φ] ⊢[𝓢]! ψ := fun b ↦ deductInvProof <| ofProof b

lemma deductInv' (h : 𝓢 ⊢ φ ⇒ₗ ψ) : [φ] ⊢[𝓢] ψ :=
  ⟨FiniteContext.deductInv'Proof h.some⟩

instance deduction : Deduction (FiniteContext F 𝓢)
    where
  ofInsert := deductProof
  inv := deductInvProof

instance : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Γ ⊢! Δ.conj := Conj₂ProofIntro _ (fun _ hp ↦ bΓ hp)
    ofDefProof <| CProofTrans (toDefProof this) (toDefProof bΔ)⟩

end

end FiniteContext

variable (F)

/-- Data and laws for Context in `FFL.Entailment`. -/
structure Context (𝓢 : S) where
  /-- The ctx construction in `FFL.Entailment.Context`. -/
  ctx : Set F

variable {F}

namespace Context

variable {𝓢 : S}

instance : Coe (Set F) (Context F 𝓢) :=
  ⟨mk⟩

instance : EmptyCollection (Context F 𝓢) :=
  ⟨⟨∅⟩⟩

instance : Membership F (Context F 𝓢) :=
  ⟨fun Γ x => (x ∈ Γ.ctx)⟩

instance : HasSubset (Context F 𝓢) :=
  ⟨(·.ctx ⊆ ·.ctx)⟩

instance : Adjoin F (Context F 𝓢) :=
  ⟨(⟨insert · ·.ctx⟩)⟩

lemma mem_def {φ : F} {Γ : Context F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx :=
  iff_of_eq rfl

@[simp]
lemma coe_subset_coe_iff {Γ Δ : Set F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ :=
  iff_of_eq rfl

@[simp]
lemma mem_coe_iff {φ : F} {Γ : Set F} : φ ∈ (Γ : Context F 𝓢) ↔ φ ∈ Γ :=
  iff_of_eq rfl

lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : Context F 𝓢) := by exact fun a ↦ a

instance : AdjunctiveSet F (Context F 𝓢)
    where
  subset_iff := by rintro ⟨s⟩ ⟨u⟩; simp [Set.subset_def]
  not_mem_empty := not_mem_empty
  mem_cons_iff := by simp [Adjoin.adjoin, mem_def]

variable [LogicalConnective F] [LogicalNeutral F] [Entailment S F]

/-- Data and laws for Proof in `FFL.Entailment.Context`. -/
structure Proof (Γ : Context F 𝓢) (φ : F) where
  /-- The ctx construction in `FFL.Entailment.Context.Proof`. -/
  ctx : List F
  subset : ∀ ψ ∈ ctx, ψ ∈ Γ
  /-- The prf construction in `FFL.Entailment.Context.Proof`. -/
  prf : ctx ⊢[𝓢]! φ

instance (𝓢 : S) : Entailment (Context F 𝓢) F :=
  ⟨Proof⟩

variable (𝓢)

/-- The Prf construction in `FFL.Entailment.Context`. -/
abbrev Prf (Γ : Set F) (φ : F) : Type _ :=
  (Γ : Context F 𝓢) ⊢! φ

/-- The Provable construction in `FFL.Entailment.Context`. -/
abbrev Provable (Γ : Set F) (φ : F) : Prop :=
  (Γ : Context F 𝓢) ⊢ φ

/-- The Unprovable construction in `FFL.Entailment.Context`. -/
abbrev Unprovable (Γ : Set F) (φ : F) : Prop :=
  (Γ : Context F 𝓢) ⊬ φ

/-- The Prf Set construction in `FFL.Entailment.Context`. -/
abbrev PrfSet (Γ : Set F) (s : Set F) : Type _ :=
  (Γ : Context F 𝓢) ⊢!* s

/-- The Provable Set construction in `FFL.Entailment.Context`. -/
abbrev ProvableSet (Γ : Set F) (s : Set F) : Prop :=
  (Γ : Context F 𝓢) ⊢* s

/-- The «term *⊢[ ]! » construction in `FFL.Entailment.Context`. -/
notation Γ:45 " *⊢[" 𝓢 "]! " φ:46 => Prf 𝓢 Γ φ

/-- The «term *⊢[ ] » construction in `FFL.Entailment.Context`. -/
notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Provable 𝓢 Γ φ

/-- The «term *⊬[ ] » construction in `FFL.Entailment.Context`. -/
notation Γ:45 " *⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ

/-- The «term *⊢[ ]!* » construction in `FFL.Entailment.Context`. -/
notation Γ:45 " *⊢[" 𝓢 "]!* " s:46 => PrfSet 𝓢 Γ s

/-- The «term *⊢[ ]* » construction in `FFL.Entailment.Context`. -/
notation Γ:45 " *⊢[" 𝓢 "]* " s:46 => ProvableSet 𝓢 Γ s

section

variable {𝓢}

lemma provable_iff {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Δ ⊢[𝓢] φ :=
  ⟨by rintro ⟨⟨Δ, h, b⟩⟩; exact ⟨Δ, h, ⟨b⟩⟩, by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨⟨Δ, h, d⟩⟩⟩

section minimal

variable [Entailment.Minimal 𝓢]

instance [DecidableEq F] : Axiomatized (Context F 𝓢)
    where
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, byAxm (by simp)⟩
  weakening := fun h b ↦
    ⟨b.ctx, fun φ hp ↦ AdjunctiveSet.subset_iff.mp h φ (b.subset φ hp), b.prf⟩

/-- The by Axm! construction in `FFL.Entailment.Context`. -/
def byAxmProof [DecidableEq F] {Γ : Set F} {φ : F} (h : φ ∈ Γ) : Γ *⊢[𝓢]! φ :=
  Axiomatized.prfAxm (by simpa)

instance : Compact (Context F 𝓢) where
  core := fun b ↦ AdjunctiveSet.set b.ctx
  corePrf := fun b ↦ ⟨b.ctx, by simp [AdjunctiveSet.set], b.prf⟩
  core_subset := by rintro ⟨Γ⟩ φ b; exact b.subset
  core_finite := by rintro ⟨Γ⟩; simp [AdjunctiveSet.Finite, AdjunctiveSet.set]

-- lemma provable_iff' [DecidableEq F] {φ : F} : Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ

/-- The deduct! construction in `FFL.Entailment.Context`. -/
def deductProof [DecidableEq F] {φ ψ : F} {Γ : Set F} : (insert φ Γ) *⊢[𝓢]! ψ → Γ *⊢[𝓢]! φ ⇒ₗ ψ
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : (φ :: Δ.filter (· ≠ φ)) ⊢[𝓢]! ψ :=
      FiniteContext.weakeningProof (by simp [List.subset_def, List.mem_filter]; grind) b
    ⟨Δ.filter (· ≠ φ), by
      intro ψ
      suffices ψ ∈ Δ → ψ ≠ φ → ψ ∈ Γ by simpa [List.mem_filter]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption, FiniteContext.deductProof b'⟩
lemma deduct (h : (insert φ Γ) *⊢[𝓢] ψ) : Γ *⊢[𝓢] φ ⇒ₗ ψ := by
  classical exact ⟨Context.deductProof h.some⟩
/-- The deduct Inv! construction in `FFL.Entailment.Context`. -/
def deductInvProof {φ ψ : F} {Γ : Set F} : Γ *⊢[𝓢]! φ ⇒ₗ ψ → (insert φ Γ) *⊢[𝓢]! ψ
  | ⟨Δ, h, b⟩ =>
    ⟨φ :: Δ, by simpa using fun χ hr ↦ Or.inr (h χ hr), FiniteContext.deductInvProof b⟩
lemma deductInv (h : Γ *⊢[𝓢] φ ⇒ₗ ψ) : (insert φ Γ) *⊢[𝓢] ψ := by
  classical exact ⟨Context.deductInvProof h.some⟩
instance deduction [DecidableEq F] : Deduction (Context F 𝓢)
    where
  ofInsert := deductProof
  inv := deductInvProof

/-- The weakening! construction in `FFL.Entailment.Context`. -/
def weakeningProof [DecidableEq F] (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢]! φ → Δ *⊢[𝓢]! φ :=
  Axiomatized.weakening (by simpa)
lemma weakening (h : Γ ⊆ Δ) {φ : F} : Γ *⊢[𝓢] φ → Δ *⊢[𝓢] φ := by
  classical exact fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h
/-- The of! construction in `FFL.Entailment.Context`. -/
def ofProof {φ : F} (b : 𝓢 ⊢! φ) : Γ *⊢[𝓢]! φ :=
  ⟨[], by simp, FiniteContext.ofProof b⟩

lemma of (b : 𝓢 ⊢ φ) : Γ *⊢[𝓢] φ :=
  ⟨Context.ofProof b.some⟩

/-- The mdp! construction in `FFL.Entailment.Context`. -/
def mdpProof [DecidableEq F] {Γ : Set F} (bpq : Γ *⊢[𝓢]! φ ⇒ₗ ψ) (bp : Γ *⊢[𝓢]! φ) :
    Γ *⊢[𝓢]! ψ :=
  ⟨bpq.ctx ++ bp.ctx, by
    simp only [List.mem_append, mem_coe_iff]
    rintro χ (hr | hr)
    · exact bpq.subset χ hr
    · exact bp.subset χ hr, FiniteContext.mdp'Proof bpq.prf bp.prf⟩

lemma by_axm (h : φ ∈ Γ) : Γ *⊢[𝓢] φ := by classical exact Entailment.by_axm (by simpa)
/-- The empty Prf! construction in `FFL.Entailment.Context`. -/
def emptyPrfProof {φ : F} : ∅ *⊢[𝓢]! φ → 𝓢 ⊢! φ := by
  rintro ⟨Γ, hΓ, h⟩;
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ;
  subst this;
  exact FiniteContext.emptyPrfProof h;

lemma emptyPrf {φ : F} : ∅ *⊢[𝓢] φ → 𝓢 ⊢ φ := fun h ↦ ⟨emptyPrfProof h.some⟩

lemma provable_iff_provable {φ : F} : 𝓢 ⊢ φ ↔ ∅ *⊢[𝓢] φ :=
  ⟨of, emptyPrf⟩

lemma iff_provable_context_provable_finiteContext_toList {Δ : Finset F} :
    ↑Δ *⊢[𝓢] φ ↔ Δ.toList ⊢[𝓢] φ := by
  classical
  constructor;
  · intro h; obtain ⟨Γ, hΓ₁, hΓ₂⟩ := Context.provable_iff.mp h;
    apply FiniteContext.weakening ?_ hΓ₂; intro ψ hψ; simpa using hΓ₁ ψ hψ;
  · intro h; apply Context.provable_iff.mpr; use Δ.toList; constructor;
    · simp only [Finset.mem_toList, SetLike.mem_coe]; tauto;
    · assumption;

instance minimal [DecidableEq F] (Γ : Context F 𝓢) : Entailment.Minimal Γ
    where
  mdpProof := mdpProof
  verumProof := ofProof verumProof
  implyKProof := ofProof implyKProof
  implySProof := ofProof implySProof
  and₁Proof := ofProof and₁Proof
  and₂Proof := ofProof and₂Proof
  and₃Proof := ofProof and₃Proof
  or₁Proof := ofProof or₁Proof
  or₂Proof := ofProof or₂Proof
  or₃Proof := ofProof or₃Proof
  negEquivProof := ofProof negEquivProof

end minimal

end

end Context

end

section

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] {S : Type*} [Entailment S F]
  {𝓢 : S} [Entailment.Minimal 𝓢] {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F} {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open _root_.List List

@[simp]
lemma CVNO : 𝓢 ⊢ ⊤ ⇒ₗ ∼⊥ :=
  deduct' NO

/-- The inner MDP! construction in `FFL.Entailment`. -/
def innerMDPProof [DecidableEq F] : 𝓢 ⊢! φ ⋏ (φ ⇒ₗ ψ) ⇒ₗ ψ := by
  apply deduct'Proof;
  have hp  : [φ, φ ⇒ₗ ψ] ⊢[𝓢]! φ := FiniteContext.byAxmProof;
  have hpq : [φ, φ ⇒ₗ ψ] ⊢[𝓢]! φ ⇒ₗ ψ := FiniteContext.byAxmProof;
  exact hpq ⨀ hp;
lemma inner_mdp : 𝓢 ⊢ φ ⋏ (φ ⇒ₗ ψ) ⇒ₗ ψ := by classical exact ⟨innerMDPProof⟩
/-- The bot of mem either! construction in `FFL.Entailment`. -/
def botOfMemEitherProof [DecidableEq F] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := by
  have hp : Γ ⊢[𝓢]! φ := FiniteContext.byAxmProof h₁;
  have hnp : Γ ⊢[𝓢]! φ ⇒ₗ ⊥ := COProofOfNProof <| FiniteContext.byAxmProof h₂; exact hnp⨀hp
lemma bot_of_mem_either (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  classical exact ⟨botOfMemEitherProof h₁ h₂⟩
/-- The neg MDP! construction in `FFL.Entailment`. -/
def negMDPProof (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ :=
  (COProofOfNProof hnp)⨀hn
lemma neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ :=
  ⟨negMDPProof hnp.some hn.some⟩

/-- The right A! intro left construction in `FFL.Entailment`. -/
def rightAProofIntroLeft (h : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! φ ⇒ₗ (χ ⋎ ψ) := by
  apply deduct'Proof;
  apply AProofIntroLeft;
  apply deductInvProof;
  exact ofProof h;
lemma right_A_intro_left (h : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ φ ⇒ₗ (χ ⋎ ψ) :=
  ⟨rightAProofIntroLeft h.some⟩

/-- The right A! intro right construction in `FFL.Entailment`. -/
def rightAProofIntroRight (h : 𝓢 ⊢! ψ ⇒ₗ χ) : 𝓢 ⊢! ψ ⇒ₗ (φ ⋎ χ) := by
  apply deduct'Proof;
  apply AProofIntroRight;
  apply deductInvProof;
  exact ofProof h;
lemma right_A_intro_right (h : 𝓢 ⊢ ψ ⇒ₗ χ) : 𝓢 ⊢ ψ ⇒ₗ (φ ⋎ χ) :=
  ⟨rightAProofIntroRight h.some⟩

/-- The right K! intro construction in `FFL.Entailment`. -/
def rightKProofIntro [DecidableEq F] (hq : 𝓢 ⊢! φ ⇒ₗ ψ) (hr : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! φ ⇒ₗ ψ ⋏ χ := by
  apply deduct'Proof;
  replace hq : [] ⊢[𝓢]! φ ⇒ₗ ψ := ofProof hq;
  replace hr : [] ⊢[𝓢]! φ ⇒ₗ χ := ofProof hr;
  exact KProofIntro (mdp'Proof hq FiniteContext.idProof) (mdp'Proof hr FiniteContext.idProof)
lemma right_K_intro (hq : 𝓢 ⊢ φ ⇒ₗ ψ) (hr : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ φ ⇒ₗ ψ ⋏ χ := by
  classical exact ⟨rightKProofIntro hq.some hr.some⟩
lemma left_K_symm (d : 𝓢 ⊢ φ ⋏ ψ ⇒ₗ χ) : 𝓢 ⊢ ψ ⋏ φ ⇒ₗ χ :=
  C_trans CKK d

lemma left_K_intro_right (h : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ (ψ ⋏ φ) ⇒ₗ χ := by
  classical apply CK_iff_CC.mpr; apply deduct'; exact FiniteContext.of' (Γ := [ψ]) h;

lemma left_K_intro_left (h : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ (φ ⋏ ψ) ⇒ₗ χ := by
  classical exact C_trans CKK (left_K_intro_right h)
lemma cut (d₁ : 𝓢 ⊢ φ₁ ⋏ c ⇒ₗ ψ₁) (d₂ : 𝓢 ⊢ φ₂ ⇒ₗ c ⋎ ψ₂) : 𝓢 ⊢ φ₁ ⋏ φ₂ ⇒ₗ ψ₁ ⋎ ψ₂ := by
  classical
  apply deduct';
  exact of_C_of_C_of_A (right_A_intro_left <| of' (CK_iff_CC.mp d₁) ⨀ (K_left id)) or₂ (of' d₂ ⨀
      K_right id);



/-- The CAA! construction in `FFL.Entailment`. -/
def CAAProof : 𝓢 ⊢! φ ⋎ ψ ⇒ₗ ψ ⋎ φ := by
  apply deduct'Proof;
  exact ofCProofOfCProofOfAProof or₂Proof or₁Proof <| FiniteContext.idProof
lemma CAA : 𝓢 ⊢ φ ⋎ ψ ⇒ₗ ψ ⋎ φ :=
  ⟨CAAProof⟩

/-- The A! symm construction in `FFL.Entailment`. -/
def AProofSymm (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ :=
  CAAProof⨀h
lemma A_symm (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ :=
  ⟨AProofSymm h.some⟩

lemma A_assoc : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢ (φ ⋎ ψ) ⋎ χ := by
  constructor;
  · intro h;
    exact of_C_of_C_of_A
      (right_A_intro_left <| right_A_intro_left C_id)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C_of_C_of_A (right_A_intro_left <| right_A_intro_right C_id)
            (right_A_intro_right C_id) id;
      )
      h;
  · intro h;
    exact of_C_of_C_of_A
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact of_C_of_C_of_A (right_A_intro_left C_id) (right_A_intro_right <|
            right_A_intro_left C_id) id;
      )
      (right_A_intro_right <| right_A_intro_right C_id)
      h;



lemma K_assoc : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ ⇔ₗ φ ⋏ (ψ ⋏ χ) :=
  by
  apply E_intro;
  · apply FiniteContext.deduct'; have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] φ := K_left <| K_left id;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] ψ := K_right <| K_left id;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢] χ := K_right id; exact K_intro hp (K_intro hq hr);
  · apply FiniteContext.deduct'; have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] φ := K_left id;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] ψ := K_left <| K_right id;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢] χ := K_right <| K_right id; apply K_intro;
    · exact K_intro hp hq;
    · exact hr;

lemma K_assoc_mp (h : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ) : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ) :=
  C_of_E_mp K_assoc⨀h
lemma K_assoc_mpr (h : 𝓢 ⊢ φ ⋏ (ψ ⋏ χ)) : 𝓢 ⊢ (φ ⋏ ψ) ⋏ χ :=
  C_of_E_mpr K_assoc⨀h

/-- The K! replace left construction in `FFL.Entailment`. -/
def KProofReplaceLeft (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! χ ⋏ ψ :=
  KProofIntro (h⨀KProofLeft hc) (KProofRight hc)
lemma K_replace_left (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ χ ⋏ ψ :=
  ⟨KProofReplaceLeft hc.some h.some⟩

/-- The CKK! of C! construction in `FFL.Entailment`. -/
def CKKProofOfCProof (h : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! φ ⋏ ψ ⇒ₗ χ ⋏ ψ := by
  apply deduct'Proof;
  exact KProofReplaceLeft FiniteContext.idProof (ofProof h)
lemma CKK_of_C (h : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ φ ⋏ ψ ⇒ₗ χ ⋏ ψ :=
  ⟨CKKProofOfCProof h.some⟩

/-- The K! replace right construction in `FFL.Entailment`. -/
def KProofReplaceRight (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⋏ χ :=
  KProofIntro (KProofLeft hc) (h⨀KProofRight hc)
lemma K_replace_right (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ⇒ₗ χ) : 𝓢 ⊢ φ ⋏ χ :=
  ⟨KProofReplaceRight hc.some h.some⟩

/-- The CKK! of C!' construction in `FFL.Entailment`. -/
def CKKProofOfCProof' (h : 𝓢 ⊢! ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⋏ ψ ⇒ₗ φ ⋏ χ := by
  apply deduct'Proof;
  exact KProofReplaceRight (FiniteContext.idProof) (ofProof h)
lemma CKK_of_C' (h : 𝓢 ⊢ ψ ⇒ₗ χ) : 𝓢 ⊢ φ ⋏ ψ ⇒ₗ φ ⋏ χ :=
  ⟨CKKProofOfCProof' h.some⟩

/-- The K! replace construction in `FFL.Entailment`. -/
def KProofReplace (hc : 𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ ⇒ₗ χ) (h₂ : 𝓢 ⊢! ψ ⇒ₗ ξ) : 𝓢 ⊢! χ ⋏ ξ :=
  KProofReplaceRight (KProofReplaceLeft hc h₁) h₂
lemma K_replace (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ ⇒ₗ χ) (h₂ : 𝓢 ⊢ ψ ⇒ₗ ξ) : 𝓢 ⊢ χ ⋏ ξ :=
  ⟨KProofReplace hc.some h₁.some h₂.some⟩

/-- The CKK! of C! of C! construction in `FFL.Entailment`. -/
def CKKProofOfCProofOfCProof (h₁ : 𝓢 ⊢! φ ⇒ₗ χ) (h₂ : 𝓢 ⊢! ψ ⇒ₗ ξ) : 𝓢 ⊢! φ ⋏ ψ ⇒ₗ χ ⋏ ξ := by
  apply deduct'Proof; exact KProofReplace FiniteContext.idProof (ofProof h₁) (ofProof h₂)
lemma CKK_of_C_of_C (h₁ : 𝓢 ⊢ φ ⇒ₗ χ) (h₂ : 𝓢 ⊢ ψ ⇒ₗ ξ) : 𝓢 ⊢ φ ⋏ ψ ⇒ₗ χ ⋏ ξ :=
  ⟨CKKProofOfCProofOfCProof h₁.some h₂.some⟩

/-- The A! replace left construction in `FFL.Entailment`. -/
def AProofReplaceLeft (hc : 𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! χ ⋎ ψ :=
  ofCProofOfCProofOfAProof (CProofTrans hp or₁Proof) (or₂Proof) hc
lemma A_replace_left (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ χ ⋎ ψ :=
  ⟨AProofReplaceLeft hc.some hp.some⟩

/-- The CAA! of C! left construction in `FFL.Entailment`. -/
def CAAProofOfCProofLeft (hp : 𝓢 ⊢! φ ⇒ₗ χ) : 𝓢 ⊢! φ ⋎ ψ ⇒ₗ χ ⋎ ψ := by
  apply deduct'Proof;
  exact AProofReplaceLeft FiniteContext.idProof (ofProof hp)
lemma CAA_of_C_left (hp : 𝓢 ⊢ φ ⇒ₗ χ) : 𝓢 ⊢ φ ⋎ ψ ⇒ₗ χ ⋎ ψ :=
  ⟨CAAProofOfCProofLeft hp.some⟩

/-- The A! replace right construction in `FFL.Entailment`. -/
def AProofReplaceRight (hc : 𝓢 ⊢! φ ⋎ ψ) (hq : 𝓢 ⊢! ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⋎ χ :=
  ofCProofOfCProofOfAProof (or₁Proof) (CProofTrans hq or₂Proof) hc
lemma A_replace_right (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ⇒ₗ χ) : 𝓢 ⊢ φ ⋎ χ :=
  ⟨AProofReplaceRight hc.some hq.some⟩

/-- The CAA! of C! right construction in `FFL.Entailment`. -/
def CAAProofOfCProofRight (hq : 𝓢 ⊢! ψ ⇒ₗ χ) : 𝓢 ⊢! φ ⋎ ψ ⇒ₗ φ ⋎ χ := by
  apply deduct'Proof;
  exact AProofReplaceRight FiniteContext.idProof (ofProof hq)
lemma CAA_of_C_right (hq : 𝓢 ⊢ ψ ⇒ₗ χ) : 𝓢 ⊢ φ ⋎ ψ ⇒ₗ φ ⋎ χ :=
  ⟨CAAProofOfCProofRight hq.some⟩

/-- The A! replace construction in `FFL.Entailment`. -/
def AProofReplace (h : 𝓢 ⊢! φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢! φ₁ ⇒ₗ φ₂) (hq : 𝓢 ⊢! ψ₁ ⇒ₗ ψ₂) : 𝓢 ⊢! φ₂ ⋎ ψ₂ :=
  AProofReplaceRight (AProofReplaceLeft h hp) hq
lemma A_replace (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ ⇒ₗ φ₂) (hq : 𝓢 ⊢ ψ₁ ⇒ₗ ψ₂) : 𝓢 ⊢ φ₂ ⋎ ψ₂ :=
  ⟨AProofReplace h.some hp.some hq.some⟩

/-- The CAA! of C! of C! construction in `FFL.Entailment`. -/
def CAAProofOfCProofOfCProof (hp : 𝓢 ⊢! φ₁ ⇒ₗ φ₂) (hq : 𝓢 ⊢! ψ₁ ⇒ₗ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ⇒ₗ φ₂ ⋎ ψ₂
    := by
  apply deduct'Proof;
  exact AProofReplace FiniteContext.idProof (ofProof hp) (ofProof hq);

lemma CAA_of_C_of_C (hp : 𝓢 ⊢ φ₁ ⇒ₗ φ₂) (hq : 𝓢 ⊢ ψ₁ ⇒ₗ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ⇒ₗ φ₂ ⋎ ψ₂ :=
  ⟨CAAProofOfCProofOfCProof hp.some hq.some⟩

/-- The EAA! of E! of E! construction in `FFL.Entailment`. -/
def EAAProofOfEProofOfEProof (hp : 𝓢 ⊢! φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢! ψ₁ ⇔ₗ ψ₂) :
    𝓢 ⊢! φ₁ ⋎ ψ₁ ⇔ₗ φ₂ ⋎ ψ₂ := by
  apply EProofIntro; · exact CAAProofOfCProofOfCProof (KProofLeft hp) (KProofLeft hq);
  · exact CAAProofOfCProofOfCProof (KProofRight hp) (KProofRight hq);
lemma EAA_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢ ψ₁ ⇔ₗ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ⇔ₗ φ₂ ⋎ ψ₂ :=
  ⟨EAAProofOfEProofOfEProof hp.some hq.some⟩

lemma EAAAA : 𝓢 ⊢ φ ⋎ (ψ ⋎ χ) ⇔ₗ (φ ⋎ ψ) ⋎ χ :=
  by
  apply E_intro; · exact deduct' <| A_assoc.mp id;
  · exact deduct' <| A_assoc.mpr id;

lemma EAA_of_E_right (d : 𝓢 ⊢ ψ ⇔ₗ χ) : 𝓢 ⊢ φ ⋎ ψ ⇔ₗ φ ⋎ χ :=
  by
  apply E_intro; · apply CAA_of_C_right; exact K_left d;
  · apply CAA_of_C_right; exact K_right d;

lemma EAA_of_E_left (d : 𝓢 ⊢ φ ⇔ₗ χ) : 𝓢 ⊢ φ ⋎ ψ ⇔ₗ χ ⋎ ψ :=
  by
  apply E_intro; · apply CAA_of_C_left; exact K_left d;
  · apply CAA_of_C_left; exact K_right d;

/-- The EKK! of E! of E! construction in `FFL.Entailment`. -/
def EKKProofOfEProofOfEProof (hp : 𝓢 ⊢! φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢! ψ₁ ⇔ₗ ψ₂) :
    𝓢 ⊢! φ₁ ⋏ ψ₁ ⇔ₗ φ₂ ⋏ ψ₂ := by
  apply EProofIntro; · exact CKKProofOfCProofOfCProof (KProofLeft hp) (KProofLeft hq);
  · exact CKKProofOfCProofOfCProof (KProofRight hp) (KProofRight hq);
lemma EKK_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢ ψ₁ ⇔ₗ ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ ⇔ₗ φ₂ ⋏ ψ₂ :=
  ⟨EKKProofOfEProofOfEProof hp.some hq.some⟩

/-- The ECC! of E! of E! construction in `FFL.Entailment`. -/
def ECCProofOfEProofOfEProof (hp : 𝓢 ⊢! φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢! ψ₁ ⇔ₗ ψ₂) :
    𝓢 ⊢! (φ₁ ⇒ₗ ψ₁) ⇔ₗ (φ₂ ⇒ₗ ψ₂) := by
  apply EProofIntro;
  · apply deduct'Proof;
    exact
      CProofTrans (ofProof <| KProofRight hp) <|
        CProofTrans (FiniteContext.idProof) (ofProof <| KProofLeft hq);
  · apply deduct'Proof;
    exact
      CProofTrans (ofProof <| KProofLeft hp) <|
        CProofTrans (FiniteContext.idProof) (ofProof <| KProofRight hq);
lemma ECC_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢ ψ₁ ⇔ₗ ψ₂) : 𝓢 ⊢ (φ₁ ⇒ₗ ψ₁) ⇔ₗ (φ₂ ⇒ₗ ψ₂) :=
  ⟨ECCProofOfEProofOfEProof hp.some hq.some⟩

lemma C_iff_C_of_E_of_E (hp : 𝓢 ⊢ φ₁ ⇔ₗ φ₂) (hq : 𝓢 ⊢ ψ₁ ⇔ₗ ψ₂) : 𝓢 ⊢ φ₁ ⇒ₗ ψ₁ ↔ 𝓢 ⊢ φ₂ ⇒ₗ ψ₂ :=
  by classical exact iff_of_E (ECC_of_E_of_E hp hq)
/-- The dni! construction in `FFL.Entailment`. -/
def dniProof [DecidableEq F] : 𝓢 ⊢! φ ⇒ₗ ∼∼φ := by
  apply deduct'Proof;
  apply NProofOfCOProof;
  apply deductProof;
  exact botOfMemEitherProof (φ := φ) (by simp) (by simp);
@[simp]
lemma dni : 𝓢 ⊢ φ ⇒ₗ ∼∼φ := by classical exact ⟨dniProof⟩
/-- The dni'! construction in `FFL.Entailment`. -/
def dni'Proof [DecidableEq F] (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ :=
  dniProof⨀b
lemma dni' (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := by classical exact ⟨dni'Proof b.some⟩
/-- The ANNNN! of A! construction in `FFL.Entailment`. -/
def ANNNNProofOfAProof [DecidableEq F] (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ :=
  ofCProofOfCProofOfAProof (CProofTrans dniProof or₁Proof) (CProofTrans dniProof or₂Proof) d
lemma ANNNN_of_A (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := by
  classical exact ⟨ANNNNProofOfAProof d.some⟩
/-- The KNNNN! of K! construction in `FFL.Entailment`. -/
def KNNNNProofOfKProof [DecidableEq F] (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ :=
  KProofIntro (dni'Proof <| KProofLeft d) (dni'Proof <| KProofRight d)
lemma KNNNN_of_K (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := by
  classical exact ⟨KNNNNProofOfKProof d.some⟩
/-- The CNNOO! construction in `FFL.Entailment`. -/
def CNNOOProof : 𝓢 ⊢! ∼∼⊥ ⇒ₗ ⊥ := by
  apply deduct'Proof
  have d₁ : [∼∼⊥] ⊢[𝓢]! ∼⊥ ⇒ₗ ⊥ := COProofOfNProof byAxm₀Proof
  have d₂ : [∼∼⊥] ⊢[𝓢]! ∼⊥ := NProofOfCOProof CProofId
  exact d₁⨀d₂

/-- The ENNOO! construction in `FFL.Entailment`. -/
def ENNOOProof [DecidableEq F] : 𝓢 ⊢! ∼∼⊥ ⇔ₗ ⊥ :=
  KProofIntro CNNOOProof dniProof

/-- The CCCNN! construction in `FFL.Entailment`. -/
def CCCNNProof [DecidableEq F] : 𝓢 ⊢! (φ ⇒ₗ ψ) ⇒ₗ (∼ψ ⇒ₗ ∼φ) := by
  apply deduct'Proof;
  apply deductProof;
  apply NProofOfCOProof;
  apply deductProof;
  have dp  : [φ, ∼ψ, φ ⇒ₗ ψ] ⊢[𝓢]! φ := FiniteContext.byAxmProof;
  have dpq : [φ, ∼ψ, φ ⇒ₗ ψ] ⊢[𝓢]! φ ⇒ₗ ψ := FiniteContext.byAxmProof;
  have dq  : [φ, ∼ψ, φ ⇒ₗ ψ] ⊢[𝓢]! ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ ⇒ₗ ψ] ⊢[𝓢]! ψ ⇒ₗ ⊥ := COProofOfNProof <| FiniteContext.byAxmProof;
  exact dnq ⨀ dq;
@[simp]
theorem CCCNN : 𝓢 ⊢ (φ ⇒ₗ ψ) ⇒ₗ (∼ψ ⇒ₗ ∼φ) := by classical exact ⟨CCCNNProof⟩
@[deprecated "use `CCCNN!`" (since := "2026-07-20")]
alias contra₀Proof := CCCNNProof
@[deprecated "use `CCCNN`" (since := "2026-07-20")]
alias contra₀ := CCCNN

/-- The contra! construction in `FFL.Entailment`. -/
def contraProof [DecidableEq F] (b : 𝓢 ⊢! φ ⇒ₗ ψ) : 𝓢 ⊢! ∼ψ ⇒ₗ ∼φ :=
  CCCNNProof⨀b
lemma contra (b : 𝓢 ⊢ φ ⇒ₗ ψ) : 𝓢 ⊢ ∼ψ ⇒ₗ ∼φ := by classical exact ⟨contraProof b.some⟩
@[deprecated "use `contra!`" (since := "2026-07-20")]
alias contra₀'Proof := contraProof
@[deprecated "use `contra`" (since := "2026-07-20")]
alias contra₀' := contra

/-- The CNNNN! of C! construction in `FFL.Entailment`. -/
def CNNNNProofOfCProof [DecidableEq F] (b : 𝓢 ⊢! φ ⇒ₗ ψ) : 𝓢 ⊢! ∼∼φ ⇒ₗ ∼∼ψ :=
  contraProof <| contraProof b
@[grind <=]
lemma CNNNN_of_C (b : 𝓢 ⊢ φ ⇒ₗ ψ) : 𝓢 ⊢ ∼∼φ ⇒ₗ ∼∼ψ := by
  classical exact ⟨CNNNNProofOfCProof b.some⟩
/-- The CCCNNNN! construction in `FFL.Entailment`. -/
def CCCNNNNProof [DecidableEq F] : 𝓢 ⊢! (φ ⇒ₗ ψ) ⇒ₗ (∼∼φ ⇒ₗ ∼∼ψ) :=
  deduct'Proof <| CNNNNProofOfCProof FiniteContext.idProof
@[simp]
lemma CCCNNNN : 𝓢 ⊢ (φ ⇒ₗ ψ) ⇒ₗ (∼∼φ ⇒ₗ ∼∼ψ) := by classical exact ⟨CCCNNNNProof⟩
/-- The CN! of CN! right construction in `FFL.Entailment`. -/
def CNProofOfCNProofRight [DecidableEq F] (b : 𝓢 ⊢! φ ⇒ₗ ∼ψ) : 𝓢 ⊢! ψ ⇒ₗ ∼φ :=
  CProofTrans dniProof (contraProof b)
lemma CN_of_CN_right (b : 𝓢 ⊢ φ ⇒ₗ ∼ψ) : 𝓢 ⊢ ψ ⇒ₗ ∼φ := by
  classical exact ⟨CNProofOfCNProofRight b.some⟩
/-- The CCNCN! construction in `FFL.Entailment`. -/
def CCNCNProof [DecidableEq F] : 𝓢 ⊢! (φ ⇒ₗ ∼ψ) ⇒ₗ (ψ ⇒ₗ ∼φ) :=
  deduct'Proof <| CNProofOfCNProofRight FiniteContext.idProof
lemma CCNCN : 𝓢 ⊢ (φ ⇒ₗ ∼ψ) ⇒ₗ (ψ ⇒ₗ ∼φ) := by classical exact ⟨CCNCNProof⟩
/-- The ENN! of E! construction in `FFL.Entailment`. -/
def ENNProofOfEProof [DecidableEq F] (b : 𝓢 ⊢! φ ⇔ₗ ψ) : 𝓢 ⊢! ∼φ ⇔ₗ ∼ψ :=
  EProofIntro (contraProof <| KProofRight b) (contraProof <| KProofLeft b)
lemma ENN_of_E (b : 𝓢 ⊢ φ ⇔ₗ ψ) : 𝓢 ⊢ ∼φ ⇔ₗ ∼ψ := by classical exact ⟨ENNProofOfEProof b.some⟩
section NegationEquiv

/-- The ENNCCOO! construction in `FFL.Entailment`. -/
def ENNCCOOProof [DecidableEq F] : 𝓢 ⊢! ∼∼φ ⇔ₗ ((φ ⇒ₗ ⊥) ⇒ₗ ⊥) :=
  by
  apply EProofIntro;
  · exact
      CProofTrans (by apply contraProof; exact KProofRight negEquivProof)
        (KProofLeft negEquivProof)
  · exact
      CProofTrans (KProofRight negEquivProof)
        (by apply contraProof; exact KProofLeft negEquivProof)
@[simp]
lemma ENNCCOO : 𝓢 ⊢ ∼∼φ ⇔ₗ ((φ ⇒ₗ ⊥) ⇒ₗ ⊥) := by classical exact ⟨ENNCCOOProof⟩
end NegationEquiv

/-- The tne! construction in `FFL.Entailment`. -/
def tneProof [DecidableEq F] : 𝓢 ⊢! ∼(∼∼φ) ⇒ₗ ∼φ :=
  contraProof dniProof
@[simp]
lemma tne : 𝓢 ⊢ ∼(∼∼φ) ⇒ₗ ∼φ := by classical exact ⟨tneProof⟩
/-- The tne'! construction in `FFL.Entailment`. -/
def tne'Proof [DecidableEq F] (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ :=
  tneProof⨀b
lemma tne' (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := by classical exact ⟨tne'Proof b.some⟩
/-- The tne Iff! construction in `FFL.Entailment`. -/
def tneIffProof [DecidableEq F] : 𝓢 ⊢! ∼∼∼φ ⇔ₗ ∼φ :=
  KProofIntro tneProof dniProof

/-- The CCC! of C! left construction in `FFL.Entailment`. -/
def CCCProofOfCProofLeft (h : 𝓢 ⊢! ψ ⇒ₗ φ) : 𝓢 ⊢! (φ ⇒ₗ χ) ⇒ₗ (ψ ⇒ₗ χ) := by
  apply deduct'Proof;
  exact CProofTrans (ofProof h) idProof;
lemma CCC_of_C_left (h : 𝓢 ⊢ ψ ⇒ₗ φ) : 𝓢 ⊢ (φ ⇒ₗ χ) ⇒ₗ (ψ ⇒ₗ χ) :=
  ⟨CCCProofOfCProofLeft h.some⟩

@[deprecated "use `CCC!OfC!Left`" (since := "2026-07-20")]
alias revDhypImp'Proof := CCCProofOfCProofLeft
@[deprecated "use `CCC_of_C_left`" (since := "2026-07-20")]
alias rev_dhyp_imp' := CCC_of_C_left

lemma C_iff_C_of_iff_left (h : 𝓢 ⊢ φ ⇔ₗ ψ) : 𝓢 ⊢ φ ⇒ₗ χ ↔ 𝓢 ⊢ ψ ⇒ₗ χ :=
  by
  constructor; · exact C_trans <| K_right h;
  · exact C_trans <| K_left h;

lemma C_iff_C_of_iff_right (h : 𝓢 ⊢ φ ⇔ₗ ψ) : 𝓢 ⊢ χ ⇒ₗ φ ↔ 𝓢 ⊢ χ ⇒ₗ ψ :=
  by
  constructor; · intro hrp; exact C_trans hrp <| K_left h;
  · intro hrq; exact C_trans hrq <| K_right h;

/-- The C! swap construction in `FFL.Entailment`. -/
def CProofSwap [DecidableEq F] (h : 𝓢 ⊢! φ ⇒ₗ ψ ⇒ₗ χ) : 𝓢 ⊢! ψ ⇒ₗ φ ⇒ₗ χ := by
  apply deduct'Proof; apply deductProof;
  exact (ofProof (Γ := [φ, ψ]) h)⨀FiniteContext.byAxmProof⨀FiniteContext.byAxmProof;
lemma C_swap (h : 𝓢 ⊢ (φ ⇒ₗ ψ ⇒ₗ χ)) : 𝓢 ⊢ (ψ ⇒ₗ φ ⇒ₗ χ) := by
  classical exact ⟨CProofSwap h.some⟩
/-- The CCCCC! construction in `FFL.Entailment`. -/
def CCCCCProof [DecidableEq F] : 𝓢 ⊢! (φ ⇒ₗ ψ ⇒ₗ χ) ⇒ₗ (ψ ⇒ₗ φ ⇒ₗ χ) :=
  deduct'Proof <| CProofSwap FiniteContext.idProof
@[simp]
lemma CCCCC : 𝓢 ⊢ (φ ⇒ₗ ψ ⇒ₗ χ) ⇒ₗ (ψ ⇒ₗ φ ⇒ₗ χ) := by classical exact ⟨CCCCCProof⟩
/-- The C! of CC! construction in `FFL.Entailment`. -/
def CProofOfCCProof [DecidableEq F] (h : 𝓢 ⊢! φ ⇒ₗ φ ⇒ₗ ψ) : 𝓢 ⊢! φ ⇒ₗ ψ := by
  apply deduct'Proof; have := ofProof (Γ := [φ]) h;
  exact this⨀(FiniteContext.byAxmProof)⨀(FiniteContext.byAxmProof);
lemma C_of_CC (h : 𝓢 ⊢ φ ⇒ₗ φ ⇒ₗ ψ) : 𝓢 ⊢ φ ⇒ₗ ψ := by classical exact ⟨CProofOfCCProof h.some⟩
/-- The CCC! construction in `FFL.Entailment`. -/
def CCCProof [DecidableEq F] : 𝓢 ⊢! φ ⇒ₗ (φ ⇒ₗ ψ) ⇒ₗ ψ :=
  CProofSwap <| CProofId
lemma CCC : 𝓢 ⊢ φ ⇒ₗ (φ ⇒ₗ ψ) ⇒ₗ ψ := by classical exact ⟨CCCProof⟩
/-- The CCC! of C! right construction in `FFL.Entailment`. -/
def CCCProofOfCProofRight (h : 𝓢 ⊢! φ ⇒ₗ ψ) : 𝓢 ⊢! (χ ⇒ₗ φ) ⇒ₗ (χ ⇒ₗ ψ) :=
  implySProof⨀(CProofOfConseqProof h)
lemma CCC_of_C_right (h : 𝓢 ⊢ φ ⇒ₗ ψ) : 𝓢 ⊢ (χ ⇒ₗ φ) ⇒ₗ (χ ⇒ₗ ψ) :=
  ⟨CCCProofOfCProofRight h.some⟩

/-- The CNNCCNNNN! construction in `FFL.Entailment`. -/
def CNNCCNNNNProof [DecidableEq F] : 𝓢 ⊢! ∼∼(φ ⇒ₗ ψ) ⇒ₗ (∼∼φ ⇒ₗ ∼∼ψ) := by
  apply CProofSwap;
  apply deduct'Proof;
  exact CProofTrans (CNNNNProofOfCProof <| deductInvProof <| ofProof <| CProofSwap <|
      CCCNNNNProof) tneProof;

@[simp]
lemma CNNCCNNNN : 𝓢 ⊢ ∼∼(φ ⇒ₗ ψ) ⇒ₗ (∼∼φ ⇒ₗ ∼∼ψ) := by classical exact ⟨CNNCCNNNNProof⟩
/-- The CNNNN! of NNC! construction in `FFL.Entailment`. -/
def CNNNNProofOfNNCProof [DecidableEq F] (b : 𝓢 ⊢! ∼∼(φ ⇒ₗ ψ)) : 𝓢 ⊢! ∼∼φ ⇒ₗ ∼∼ψ :=
  CNNCCNNNNProof⨀b
lemma CNNNN_of_NNC (b : 𝓢 ⊢ ∼∼(φ ⇒ₗ ψ)) : 𝓢 ⊢ ∼∼φ ⇒ₗ ∼∼ψ := by
  classical exact ⟨CNNNNProofOfNNCProof b.some⟩
/-- The O! intro of KN! construction in `FFL.Entailment`. -/
def OProofIntroOfKNProof (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ :=
  (COProofOfNProof <| KProofRight h)⨀(KProofLeft h)
lemma O_intro_of_KN (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ :=
  ⟨OProofIntroOfKNProof h.some⟩
/-- Law of contradiction -/
alias lac' := O_intro_of_KN

/-- The CKNO! construction in `FFL.Entailment`. -/
def CKNOProof : 𝓢 ⊢! φ ⋏ ∼φ ⇒ₗ ⊥ := by
  apply deduct'Proof;
  exact OProofIntroOfKNProof (φ := φ) <| FiniteContext.idProof
@[simp]
lemma CKNO : 𝓢 ⊢ φ ⋏ ∼φ ⇒ₗ ⊥ :=
  ⟨CKNOProof⟩
/-- Law of contradiction -/
alias lac := CKNO

/-- The CANNNK! construction in `FFL.Entailment`. -/
def CANNNKProof [DecidableEq F] : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ⇒ₗ ∼(φ ⋏ ψ) :=
  leftAProofIntro (contraProof and₁Proof) (contraProof and₂Proof)
@[simp]
lemma CANNNK : 𝓢 ⊢ (∼φ ⋎ ∼ψ) ⇒ₗ ∼(φ ⋏ ψ) := by classical exact ⟨CANNNKProof⟩
/-- The NK! of ANN! construction in `FFL.Entailment`. -/
def NKProofOfANNProof [DecidableEq F] (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ) :=
  CANNNKProof⨀d
lemma NK_of_ANN (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ) := by
  classical exact ⟨NKProofOfANNProof d.some⟩
/-- The CKNNNA! construction in `FFL.Entailment`. -/
def CKNNNAProof [DecidableEq F] : 𝓢 ⊢! (∼φ ⋏ ∼ψ) ⇒ₗ ∼(φ ⋎ ψ) := by
  apply CKProofOfCCProof;
  apply deduct'Proof;
  apply deductProof;
  apply NProofOfCOProof;
  apply deductProof;
  exact ofCProofOfCProofOfAProof (COProofOfNProof FiniteContext.byAxmProof) (COProofOfNProof
      FiniteContext.byAxmProof) (FiniteContext.byAxmProof (φ := φ ⋎ ψ));

@[simp]
lemma CKNNNA : 𝓢 ⊢ ∼φ ⋏ ∼ψ ⇒ₗ ∼(φ ⋎ ψ) := by classical exact ⟨CKNNNAProof⟩
/-- The NA! of KNN! construction in `FFL.Entailment`. -/
def NAProofOfKNNProof [DecidableEq F] (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) :=
  CKNNNAProof⨀d
lemma NA_of_KNN (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := by
  classical exact ⟨NAProofOfKNNProof d.some⟩
/-- The CNAKNN! construction in `FFL.Entailment`. -/
def CNAKNNProof [DecidableEq F] : 𝓢 ⊢! ∼(φ ⋎ ψ) ⇒ₗ (∼φ ⋏ ∼ψ) := by
  apply deduct'Proof;
  exact KProofIntro (deductInvProof <| contraProof <| or₁Proof) (deductInvProof <| contraProof
      <| or₂Proof)

@[simp]
lemma CNAKNN : 𝓢 ⊢ ∼(φ ⋎ ψ) ⇒ₗ (∼φ ⋏ ∼ψ) := by classical exact ⟨CNAKNNProof⟩
/-- The KNN! of NA! construction in `FFL.Entailment`. -/
def KNNProofOfNAProof [DecidableEq F] (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ :=
  CNAKNNProof⨀b
lemma KNN_of_NA (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := by
  classical exact ⟨KNNProofOfNAProof b.some⟩
section Conjunction

/-- The EConj₂Conj! construction in `FFL.Entailment`. -/
def EConj₂ConjProof : (Γ : List F) → 𝓢 ⊢! ⋀Γ ⇔ₗ (PointwiseComposition.List.conj Γ)
  | [] => EProofId
  | [_] => EProofIntro (deduct'Proof <| KProofIntro FiniteContext.idProof verumProof) and₁Proof
  | _ :: ψ :: Γ => EKKProofOfEProofOfEProof (EProofId) (EConj₂ConjProof (ψ :: Γ))
@[simp]
lemma EConj₂Conj : 𝓢 ⊢ ⋀Γ ⇔ₗ (PointwiseComposition.List.conj Γ) :=
  ⟨EConj₂ConjProof Γ⟩

lemma CConj_iff_CConj₂ : 𝓢 ⊢ (PointwiseComposition.List.conj Γ) ⇒ₗ φ ↔ 𝓢 ⊢ ⋀Γ ⇒ₗ φ :=
  C_iff_C_of_iff_left <| E_symm EConj₂Conj

/-- ! note: It may be easier to handle define `List.conj` based on `List.conj' (?)` -/
def rightConj'ProofIntro [DecidableEq F] (φ : F) (l : List ι) (ψ : ι → F)
    (b : ∀ i ∈ l, 𝓢 ⊢! φ ⇒ₗ ψ i) : 𝓢 ⊢! φ ⇒ₗ (PointwiseComposition.List.conj' · l) ψ :=
  rightConj₂ProofIntro φ (l.map ψ) fun χ h ↦
    let ⟨i, hi, e⟩ := l.chooseX (fun i ↦ ψ i = χ) (by simpa using h)
    e ▸ (b i hi)
lemma right_Conj'_intro (φ : F) (l : List ι) (ψ : ι → F) (b : ∀ i ∈ l, 𝓢 ⊢ φ ⇒ₗ ψ i) :
    𝓢 ⊢ φ ⇒ₗ (PointwiseComposition.List.conj' · l) ψ := by
  classical exact ⟨rightConj'ProofIntro φ l ψ fun i hi ↦ (b i hi).get⟩
/-- The left Conj'! intro construction in `FFL.Entailment`. -/
def leftConj'ProofIntro [DecidableEq F] {l : List ι} (h : i ∈ l) (φ : ι → F) :
    𝓢 ⊢! (PointwiseComposition.List.conj' · l) φ ⇒ₗ φ i :=
  leftConj₂ProofIntro (by simp only [mem_map]; use i)
lemma left_Conj'_intro {l : List ι} (h : i ∈ l) (φ : ι → F) :
    𝓢 ⊢ (PointwiseComposition.List.conj' · l) φ ⇒ₗ φ i := by
  classical exact ⟨leftConj'ProofIntro h φ⟩
lemma right_Fconj_intro (φ : F) (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢ φ ⇒ₗ ψ) :
    𝓢 ⊢ φ ⇒ₗ (PointwiseComposition.Finset.conj s) :=
  right_Conj₂_intro φ s.toList fun ψ hψ ↦ b ψ (by simpa using hψ)

lemma left_Fconj_intro [DecidableEq F] {s : Finset F} (h : φ ∈ s) :
    𝓢 ⊢ (PointwiseComposition.Finset.conj s) ⇒ₗ φ :=
  left_Conj₂_intro <| by simp [h]

lemma right_Fconj'_intro (φ : F) (s : Finset ι) (ψ : ι → F) (b : ∀ i ∈ s, 𝓢 ⊢ φ ⇒ₗ ψ i) :
    𝓢 ⊢ φ ⇒ₗ ⋀ i ∈ s, ψ i := by classical exact right_Conj'_intro φ s.toList ψ (by simpa)
lemma left_Fconj'_intro {s : Finset ι} (φ : ι → F) {i} (hi : i ∈ s) :
    𝓢 ⊢ (⋀ i ∈ s, φ i) ⇒ₗ φ i := by classical exact left_Conj'_intro (by simpa) φ
lemma right_Uconj_intro [Fintype ι] (φ : F) (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢ φ ⇒ₗ ψ i) :
    𝓢 ⊢ φ ⇒ₗ ⋀ i, ψ i := by
  classical exact right_Fconj'_intro φ Finset.univ ψ (by simpa using b)
lemma left_Uconj_intro [Fintype ι] (φ : ι → F) (i) : 𝓢 ⊢ (⋀ i, φ i) ⇒ₗ φ i := by
  classical exact left_Fconj'_intro _ <| by simp
lemma Conj₂_iff_forall_provable {Γ : List F} : (𝓢 ⊢ ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  classical
    induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ
    ih =>
    simp_all only [ne_eq, not_false_eq_true, conj₂_cons_nonempty, mem_cons, forall_eq_or_imp];
    constructor;
    · intro h; constructor; · exact K_left h;
      · exact ih.mp (K_right h);
    · rintro ⟨h₁, h₂⟩; exact K_intro h₁ (ih.mpr h₂);

lemma CConj₂Conj₂_of_subset (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢ ⋀Δ ⇒ₗ ⋀Γ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact left_Conj₂_intro h
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true,
      conj₂_cons_nonempty];
    exact right_K_intro (left_Conj₂_intro h.1) ih;

lemma CConj₂Conj₂_of_provable (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : 𝓢 ⊢ ⋀Δ ⇒ₗ ⋀Γ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hnil => exact C_of_conseq verum;
  | hsingle =>
    simp_all only [mem_cons, not_mem_nil, or_false, forall_eq, conj₂_singleton]
    exact provable_iff.mp h
  | hcons φ Γ hne ih =>
    simp_all only [ne_eq, mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
      not_false_eq_true,
      conj₂_cons_nonempty];
    exact right_K_intro (provable_iff.mp h.1) ih;

lemma CConj₂_of_forall_provable (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢] φ) : Δ ⊢[𝓢] ⋀Γ := by
  classical exact provable_iff.mpr <| CConj₂Conj₂_of_provable h
lemma CConj₂_of_unique (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢ φ ⇒ₗ ⋀Γ := by
  classical
    induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all only [ne_eq, mem_cons, true_or, or_true, implies_true, forall_const,
      forall_eq_or_imp, not_false_eq_true, conj₂_cons_nonempty];
    have ⟨he₁, he₂⟩ := he; subst he₁; exact right_K_intro C_id ih;
  | _ => simp_all;

lemma C_of_CConj₂_of_unique (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢ ⋀Γ ⇒ₗ ψ) : 𝓢 ⊢ φ ⇒ₗ ψ := by
  classical exact C_trans (CConj₂_of_unique he) hd
lemma CConj₂_iff_CKConj₂ : 𝓢 ⊢ ⋀(φ :: Γ) ⇒ₗ ψ ↔ 𝓢 ⊢ φ ⋏ ⋀Γ ⇒ₗ ψ := by
  classical
    induction Γ with
  | nil =>
    simp only [conj₂_singleton, conj₂_nil, CK_iff_CC]; constructor;
    · intro h; apply C_swap; exact C_of_conseq h;
    · intro h; exact C_swap h⨀verum;
  | cons ψ ih => simp;

@[simp]
lemma CConj₂AppendKConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) ⇒ₗ ⋀Γ ⋏ ⋀Δ := by
  classical
  apply FiniteContext.deduct'; have : [⋀(Γ ++ Δ)] ⊢[𝓢] ⋀(Γ ++ Δ) := id;
  have d := Conj₂_iff_forall_provable.mp this; apply K_intro;
  · apply Conj₂_iff_forall_provable.mpr; intro φ hp;
    exact d φ (by simp only [mem_append]; left; exact hp);
  · apply Conj₂_iff_forall_provable.mpr; intro φ hp;
    exact d φ (by simp only [mem_append]; right; exact hp);

@[simp]
lemma CKConj₂RemoveConj₂ [DecidableEq F] :
    𝓢 ⊢ ⋀((PointwiseComposition.List.remove · Γ) φ) ⋏ φ ⇒ₗ ⋀Γ :=
  by
  apply deduct'; apply Conj₂_iff_forall_provable.mpr; intro ψ hq; by_cases e : ψ = φ;
  · subst e; exact K_right id;
  · exact
      Conj₂_iff_forall_provable.mp (K_left id) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma CKConj₂Remove_of_CConj₂ [DecidableEq F] (b : 𝓢 ⊢ ⋀Γ ⇒ₗ ψ) :
    𝓢 ⊢ ⋀((PointwiseComposition.List.remove · Γ) φ) ⋏ φ ⇒ₗ ψ :=
  C_trans CKConj₂RemoveConj₂ b

lemma Conj₂Append_iff_KConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) ↔ 𝓢 ⊢ ⋀Γ ⋏ ⋀Δ := by
  classical
  constructor;
  · intro h; replace h := Conj₂_iff_forall_provable.mp h; apply K_intro;
    · apply Conj₂_iff_forall_provable.mpr; intro φ hp;
      exact h φ (by simp only [List.mem_append]; left; simpa);
    · apply Conj₂_iff_forall_provable.mpr; intro φ hp;
      exact h φ (by simp only [List.mem_append]; right; simpa);
  · intro h; apply Conj₂_iff_forall_provable.mpr; simp only [List.mem_append];
    rintro φ (hp₁ | hp₂); · exact (Conj₂_iff_forall_provable.mp <| K_left h) φ hp₁;
    · exact (Conj₂_iff_forall_provable.mp <| K_right h) φ hp₂;

@[simp]
lemma EConj₂AppendKConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) ⇔ₗ ⋀Γ ⋏ ⋀Δ := by
  classical
  apply E_intro; · apply deduct'; apply Conj₂Append_iff_KConj₂Conj₂.mp; exact id;
  · apply deduct'; apply Conj₂Append_iff_KConj₂Conj₂.mpr; exact id;

lemma CConj₂Append_iff_CKConj₂Conj₂ : 𝓢 ⊢ ⋀(Γ ++ Δ) ⇒ₗ φ ↔ 𝓢 ⊢ (⋀Γ ⋏ ⋀Δ) ⇒ₗ φ := by
  classical
  constructor; · intro h; exact C_trans (K_right EConj₂AppendKConj₂Conj₂) h;
  · intro h; exact C_trans (K_left EConj₂AppendKConj₂Conj₂) h;

@[simp]
lemma CConj₂FConj {Γ : Finset F} : 𝓢 ⊢ ⋀Γ.toList ⇒ₗ (PointwiseComposition.Finset.conj Γ) := by
  classical apply CConj₂Conj₂_of_provable; apply FiniteContext.by_axm;

@[simp] lemma CConj₂FConj_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢ ⋀Γ ⇒ₗ
    (PointwiseComposition.Finset.conj Γ.toFinset) := by
  apply C_trans ?_ CConj₂FConj;
  apply CConj₂Conj₂_of_subset;
  simp;

@[simp]
lemma CFConjConj₂ {Γ : Finset F} : 𝓢 ⊢ (PointwiseComposition.Finset.conj Γ) ⇒ₗ ⋀Γ.toList := by
  classical apply right_Conj₂_intro; intro φ hφ; apply left_Fconj_intro; simpa using hφ;

@[simp] lemma CFConjConj₂_list [DecidableEq F] {Γ : List F} : 𝓢 ⊢
    (PointwiseComposition.Finset.conj Γ.toFinset) ⇒ₗ ⋀Γ := by
  apply C_trans <| CFConjConj₂;
  apply CConj₂Conj₂_of_subset;
  simp;

lemma FConj_DT {Γ : Finset F} : 𝓢 ⊢ (PointwiseComposition.Finset.conj Γ) ⇒ₗ φ ↔ Γ *⊢[𝓢] φ := by
  classical
  constructor;
  · intro h; apply Context.provable_iff.mpr; use Γ.toList; constructor; · simp;
    · apply FiniteContext.provable_iff.mpr; exact C_trans (by simp) h;
  · intro h; obtain ⟨Δ, hΔ₁, hΔ₂⟩ := Context.provable_iff.mp h;
    replace hΔ₂ : 𝓢 ⊢ ⋀Γ.toList ⇒ₗ φ :=
      C_trans (CConj₂Conj₂_of_subset (by simpa)) <| FiniteContext.provable_iff.mp hΔ₂
    exact C_trans (by simp) hΔ₂;

lemma FConj_iff_forall_provable [DecidableEq F] {Γ : Finset F} :
    (𝓢 ⊢ (PointwiseComposition.Finset.conj Γ)) ↔ (∀ φ ∈ Γ, 𝓢 ⊢ φ) := by
  apply Iff.trans Conj₂_iff_forall_provable; constructor <;> simp_all;

lemma FConj_of_FConj_of_subset {Γ Δ : Finset F} (h : Δ ⊆ Γ)
    (hΓ : 𝓢 ⊢ (PointwiseComposition.Finset.conj Γ)) :
    𝓢 ⊢ (PointwiseComposition.Finset.conj Δ) := by
  classical rw [FConj_iff_forall_provable] at hΓ ⊢; intro φ hφ; apply hΓ; apply h hφ;

lemma CFConjFConj_of_subset {Γ Δ : Finset F} (h : Δ ⊆ Γ) :
    𝓢 ⊢ (PointwiseComposition.Finset.conj Γ) ⇒ₗ (PointwiseComposition.Finset.conj Δ) := by
  classical apply FConj_DT.mpr; apply FConj_of_FConj_of_subset h; apply FConj_DT.mp; simp;

@[simp] lemma CFconjUnionKFconj [DecidableEq F] {Γ Δ : Finset F} : 𝓢 ⊢
    (PointwiseComposition.Finset.conj (Γ ∪ Δ)) ⇒ₗ (PointwiseComposition.Finset.conj Γ) ⋏
    (PointwiseComposition.Finset.conj Δ) := by
  apply FConj_DT.mpr;
  apply K_intro <;>
  · apply FConj_DT.mp;
    apply CFConjFConj_of_subset;
    simp;

@[simp]
lemma CinsertFConjKFConj [DecidableEq F] {Γ : Finset F} :
    𝓢 ⊢
      (PointwiseComposition.Finset.conj (insert φ Γ)) ⇒ₗ
        φ ⋏ (PointwiseComposition.Finset.conj Γ) :=
  by
  suffices
    𝓢 ⊢
      (PointwiseComposition.Finset.conj ({ φ } ∪ Γ)) ⇒ₗ
        (Finset.conj { φ }) ⋏ (PointwiseComposition.Finset.conj Γ)
    by simpa using this;
  apply CFconjUnionKFconj;

@[simp]
lemma CKFconjFconjUnion [DecidableEq F] {Γ Δ : Finset F} :
    𝓢 ⊢
      (PointwiseComposition.Finset.conj Γ) ⋏ (PointwiseComposition.Finset.conj Δ) ⇒ₗ
        (PointwiseComposition.Finset.conj (Γ ∪ Δ)) :=
  by
  apply right_Fconj_intro; simp only [Finset.mem_union]; rintro φ (hφ | hφ);
  · apply left_K_intro_left
    apply left_Fconj_intro hφ;
  · apply left_K_intro_right; apply left_Fconj_intro hφ;

@[simp]
lemma CKFConjinsertFConj [DecidableEq F] {Γ : Finset F} :
    𝓢 ⊢
      φ ⋏ (PointwiseComposition.Finset.conj Γ) ⇒ₗ
        (PointwiseComposition.Finset.conj (insert φ Γ)) :=
  by
  suffices
    𝓢 ⊢
      (Finset.conj { φ }) ⋏ (PointwiseComposition.Finset.conj Γ) ⇒ₗ
        (PointwiseComposition.Finset.conj ({ φ } ∪ Γ))
    by simpa using this;
  apply CKFconjFconjUnion;

lemma FConj_DT' [DecidableEq F] {Γ Δ : Finset F} :
    Γ *⊢[𝓢] (PointwiseComposition.Finset.conj Δ) ⇒ₗ φ ↔ ↑(Γ ∪ Δ) *⊢[𝓢] φ :=
  by
  constructor;
  · intro h; exact FConj_DT.mp <| C_trans CFconjUnionKFconj <| CK_iff_CC.mpr <| FConj_DT.mpr h;
  · intro h; exact FConj_DT.mp <| CK_iff_CC.mp <| C_trans CKFconjFconjUnion <| FConj_DT.mpr h;

lemma CFconjFconj_of_provable [DecidableEq F] {Γ Δ : Finset _} (h : ∀ φ, φ ∈ Γ → Δ *⊢[𝓢] φ) :
    𝓢 ⊢ (PointwiseComposition.Finset.conj Δ) ⇒ₗ (PointwiseComposition.Finset.conj Γ) :=
  by
  have : 𝓢 ⊢ ⋀(Δ.toList) ⇒ₗ ⋀(Γ.toList) :=
    CConj₂Conj₂_of_provable <| by
      intro φ hφ; apply Context.iff_provable_context_provable_finiteContext_toList.mp
      apply h φ; simpa using hφ;
  refine C_replace ?_ ?_ this; · simp;
  · simp;

end Conjunction

section disjunction

/-- The right Disj! intro construction in `FFL.Entailment`. -/
def rightDisjProofIntro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) :
    𝓢 ⊢! φ ⇒ₗ (PointwiseComposition.List.disj Γ) :=
  match Γ with
  | [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then
      cast (or₁Proof : 𝓢 ⊢! φ ⇒ₗ φ ⋎ (PointwiseComposition.List.disj Γ)) (by simp [e])
    else
      have : φ ∈ Γ := by simpa [e] using h
      CProofTrans (rightDisjProofIntro Γ this) or₂Proof
theorem right_Disj_intro (Γ : List F) (h : φ ∈ Γ) :
    𝓢 ⊢ φ ⇒ₗ (PointwiseComposition.List.disj Γ) := by classical exact ⟨rightDisjProofIntro Γ h⟩
/-- The right Disj! intro' construction in `FFL.Entailment`. -/
def rightDisjProofIntro' [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢! ψ ⇒ₗ φ) :
    𝓢 ⊢! ψ ⇒ₗ (PointwiseComposition.List.disj Γ) :=
  CProofTrans hψ (rightDisjProofIntro Γ h)
theorem right_Disj_intro' (Γ : List F) (h : φ ∈ Γ) (hψ : 𝓢 ⊢ ψ ⇒ₗ φ) :
    𝓢 ⊢ ψ ⇒ₗ (PointwiseComposition.List.disj Γ) := by
  classical exact ⟨rightDisjProofIntro' Γ h hψ.get⟩
/-- The right Disj₂! intro construction in `FFL.Entailment`. -/
def rightDisj₂ProofIntro [DecidableEq F] (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ ⇒ₗ ⋁Γ :=
  match Γ with
  | [] => by simp at h
  | [ψ] => (show ⋁[ψ] = φ by simp_all) ▸ CProofId
  | ψ :: χ :: Γ =>
    if e : φ = ψ then cast (or₁Proof : 𝓢 ⊢! φ ⇒ₗ φ ⋎ ⋁(χ :: Γ)) (by simp [e])
    else
      have : φ ∈ χ :: Γ := by simpa [e] using h
      CProofTrans (rightDisj₂ProofIntro _ this) or₂Proof
theorem right_Disj₂_intro (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ ⇒ₗ ⋁Γ := by
  classical exact ⟨rightDisj₂ProofIntro Γ h⟩
/-- The right Disj'! intro construction in `FFL.Entailment`. -/
def rightDisj'ProofIntro [DecidableEq F] (φ : ι → F) (l : List ι) (h : i ∈ l) :
    𝓢 ⊢! φ i ⇒ₗ (PointwiseComposition.List.disj' · l) φ :=
  rightDisj₂ProofIntro (l.map φ) (by simpa using ⟨i, h, rfl⟩)
lemma right_Disj'_intro (φ : ι → F) (l : List ι) (h : i ∈ l) :
    𝓢 ⊢ φ i ⇒ₗ (PointwiseComposition.List.disj' · l) φ := by
  classical exact ⟨rightDisj'ProofIntro φ l h⟩
lemma right_Fdisj_intro [DecidableEq F] (s : Finset F) (h : φ ∈ s) :
    𝓢 ⊢ φ ⇒ₗ (PointwiseComposition.Finset.disj s) :=
  right_Disj₂_intro _ (by simp [h])

lemma right_Fdisj'_intro (s : Finset ι) (φ : ι → F) {i} (hi : i ∈ s) :
    𝓢 ⊢ φ i ⇒ₗ ⋁ j ∈ s, φ j := by classical exact right_Disj'_intro _ _ (by simp [hi])
lemma right_Udisj_intro [Fintype ι] (φ : ι → F) : 𝓢 ⊢ φ i ⇒ₗ ⋁ j, φ j := by
  classical exact right_Fdisj'_intro _ _ (by simp)
end disjunction

section

variable {Γ Δ : Finset F}

lemma CFConjFDisj_of_K_intro [DecidableEq F] (hp : φ ∈ Γ) (hpq : ψ ∈ Γ) (hψ : φ ⋏ ψ ∈ Δ) :
    𝓢 ⊢ (PointwiseComposition.Finset.conj Γ) ⇒ₗ (PointwiseComposition.Finset.disj Δ) :=
  by
  apply C_trans (ψ := Finset.disj {φ ⋏ ψ});
  · apply C_trans (ψ := Finset.conj { φ, ψ }) ?_;
    · apply FConj_DT.mpr;
      simp only [Finset.coe_insert, Finset.coe_singleton, Finset.disj_singleton];
      apply K_intro <;> exact Context.by_axm <| by simp;
    · apply CFConjFConj_of_subset; apply Finset.doubleton_subset.mpr; tauto;
  · simp only [Finset.disj_singleton]; apply right_Fdisj_intro _ hψ;

lemma CFConjFDisj_of_innerMDP [DecidableEq F] (hp : φ ∈ Γ) (hpq : φ ⇒ₗ ψ ∈ Γ) (hψ : ψ ∈ Δ) : 𝓢 ⊢
    (PointwiseComposition.Finset.conj Γ) ⇒ₗ (PointwiseComposition.Finset.disj Δ) := by
  apply C_trans (ψ := Finset.disj {ψ});
  · apply C_trans (ψ := Finset.conj {φ, φ ⇒ₗ ψ}) ?_;
    · apply FConj_DT.mpr;
      have h₁ : ({φ, φ ⇒ₗ ψ}) *⊢[𝓢] φ ⇒ₗ ψ := Context.by_axm <| by simp;
      have h₂ : ({φ, φ ⇒ₗ ψ}) *⊢[𝓢] φ := Context.by_axm <| by simp;
      simpa using h₁ ⨀ h₂;
    · apply CFConjFConj_of_subset;
      apply Finset.doubleton_subset.mpr;
      tauto;
  · simp only [Finset.disj_singleton];
    apply right_Fdisj_intro _ hψ;

lemma iff_FiniteContext_Context [DecidableEq F] {Γ : List F} : Γ ⊢[𝓢] φ ↔ ↑Γ.toFinset *⊢[𝓢] φ :=
  by
  constructor;
  · intro h; replace h := FiniteContext.provable_iff.mp h; apply FConj_DT.mp;
    exact C_trans (by simp) h;
  · intro h; replace h := FConj_DT.mpr h; apply FiniteContext.provable_iff.mpr;
    exact C_trans (by simp) h;

lemma FConj'_iff_forall_provable {s : Finset α} {ι : α → F} :
    (𝓢 ⊢ ⋀ i ∈ s, ι i) ↔ (∀ i ∈ s, 𝓢 ⊢ ι i) := by
  classical
  have : 𝓢 ⊢ ⋀(s.toList.map ι) ↔ ∀ i ∈ s, 𝓢 ⊢ ι i := by
    simpa using Conj₂_iff_forall_provable (Γ := s.toList.map ι);
  apply Iff.trans ?_ this; simp [Finset.conj', List.conj'];

end

namespace Context

lemma provable_iff_finset {Γ : Set F} {φ : F} :
    Γ *⊢[𝓢] φ ↔ ∃ Δ : Finset F, (↑Δ ⊆ Γ) ∧ Δ *⊢[𝓢] φ := by
  classical
  apply Iff.trans Context.provable_iff; constructor;
  · rintro ⟨Δ, hΔ₁, hΔ₂⟩; use Δ.toFinset; constructor; · simpa;
    · apply provable_iff.mpr
      use Δ; constructor <;> simp_all;
  · rintro ⟨Δ, hΔ₁, hΔ₂⟩; use Δ.toList; constructor; · simpa;
    · apply FiniteContext.provable_iff.mpr; refine C_trans ?_ (FConj_DT.mpr hΔ₂); simp;

lemma bot_of_mem_neg {Γ : Set F} (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ *⊢[𝓢] ⊥ := by
  classical
  replace h₁ : Γ *⊢[𝓢] φ := by_axm h₁;
  replace h₂ : Γ *⊢[𝓢] φ ⇒ₗ ⊥ := N_iff_CO.mp <| by_axm h₂;
  exact h₂ ⨀ h₁;

end Context

end

end Entailment
end FFL

end

end PointwiseComposition
