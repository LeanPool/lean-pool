/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.
public import LeanPool.PointwiseComposition.Foundation.Propositional.Entailment.Int

/-! Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

/-- The DNE construction in `FFL.Axioms`. -/
protected abbrev DNE :=
  ∼∼φ ⇒ₗ φ

/-- The LEM construction in `FFL.Axioms`. -/
protected abbrev LEM :=
  φ ⋎ ∼φ

/-- The Peirce construction in `FFL.Axioms`. -/
protected abbrev Peirce :=
  ((φ ⇒ₗ ψ) ⇒ₗ φ) ⇒ₗ φ

/-- The Elim Contra construction in `FFL.Axioms`. -/
protected abbrev ElimContra :=
  (∼ψ ⇒ₗ ∼φ) ⇒ₗ (φ ⇒ₗ ψ)

end Axioms
end FFL

namespace FFL
namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

/-- Proofs of double-negation elimination in the given proof system. -/
class HasAxiomDNE (𝓢 : S) where
  /-- The dne! construction in `FFL.Entailment`. -/
  dneProof {φ : F} : 𝓢 ⊢! Axioms.DNE φ
export HasAxiomDNE (dneProof)

@[simp]
lemma dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ⇒ₗ φ :=
  ⟨dneProof⟩

/-- The of NN! construction in `FFL.Entailment`. -/
def ofNNProof [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ :=
  dneProof⨀b
@[grind ⇒]
lemma of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ :=
  ⟨ofNNProof h.some⟩

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ :=
  ⟨ofProof dneProof⟩

end FiniteContext

namespace Context

instance [Entailment.HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ :=
  ⟨ofProof dneProof⟩

end Context

end

/-- Proofs of excluded middle in the given proof system. -/
class HasAxiomLEM (𝓢 : S) where
  /-- The lem! construction in `FFL.Entailment`. -/
  lemProof {φ : F} : 𝓢 ⊢! Axioms.LEM φ
export HasAxiomLEM (lemProof)

@[simp]
lemma lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ :=
  ⟨lemProof⟩

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomLEM 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomLEM Γ :=
  ⟨ofProof lemProof⟩

end FiniteContext

namespace Context

instance [Entailment.HasAxiomLEM 𝓢] (Γ : Context F 𝓢) : HasAxiomLEM Γ :=
  ⟨ofProof lemProof⟩

end Context

end

/-- Proofs of Peirce's law in the given proof system. -/
class HasAxiomPeirce (𝓢 : S) where
  /-- The peirce! construction in `FFL.Entailment`. -/
  peirceProof {φ ψ : F} : 𝓢 ⊢! Axioms.Peirce φ ψ
export HasAxiomPeirce (peirceProof)

@[simp]
lemma peirce [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((φ ⇒ₗ ψ) ⇒ₗ φ) ⇒ₗ φ :=
  ⟨peirceProof⟩

section

variable [LogicalNeutral F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomPeirce 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomPeirce Γ :=
  ⟨ofProof peirceProof⟩

end FiniteContext

namespace Context

instance [Entailment.HasAxiomPeirce 𝓢] (Γ : Context F 𝓢) : HasAxiomPeirce Γ :=
  ⟨ofProof peirceProof⟩

end Context

end

/-- Data and laws for Has Axiom Elim Contra in `FFL.Entailment`. -/
class HasAxiomElimContra (𝓢 : S) where
  /-- The elim Contra! construction in `FFL.Entailment`. -/
  elimContraProof {φ ψ : F} : 𝓢 ⊢! Axioms.ElimContra φ ψ
export HasAxiomElimContra (elimContraProof)

@[simp]
lemma elim_contra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ (∼ψ ⇒ₗ ∼φ) ⇒ₗ (φ ⇒ₗ ψ) :=
  ⟨elimContraProof⟩

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] {S : Type*}
  [Entailment S F] {𝓢 : S} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F} {Γ Δ : List F}

/-- Data and laws for Cl in `FFL.Entailment`. -/
protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomDNE 𝓢

variable [Entailment.Cl 𝓢]

namespace FiniteContext
instance (Γ : FiniteContext F 𝓢) : Entailment.Cl Γ where
end FiniteContext

namespace Context
instance (Γ : Context F 𝓢) : Entailment.Cl Γ where
end Context

open NegationEquiv
open FiniteContext
open _root_.List List

/-- The dn! construction in `FFL.Entailment`. -/
def dnProof : 𝓢 ⊢! φ ⇔ₗ ∼∼φ :=
  EProofIntro dniProof dneProof
omit [DecidableEq F] in
@[simp]
lemma dn : 𝓢 ⊢ φ ⇔ₗ ∼∼φ := by classical exact ⟨dnProof⟩
/-- The A! of ANNNN! construction in `FFL.Entailment`. -/
def AProofOfANNNNProof (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ :=
  ofCProofOfCProofOfAProof (CProofTrans dneProof or₁Proof) (CProofTrans dneProof or₂Proof) d
omit [DecidableEq F] in
lemma A_of_ANNNN (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ :=
  ⟨AProofOfANNNNProof d.some⟩

/-- The CN! of CN! left construction in `FFL.Entailment`. -/
def CNProofOfCNProofLeft (b : 𝓢 ⊢! ∼φ ⇒ₗ ψ) : 𝓢 ⊢! ∼ψ ⇒ₗ φ :=
  CProofTrans (contraProof b) dneProof
omit [DecidableEq F] in
lemma CN_of_CN_left (b : 𝓢 ⊢ ∼φ ⇒ₗ ψ) : 𝓢 ⊢ ∼ψ ⇒ₗ φ := by
  classical exact ⟨CNProofOfCNProofLeft b.some⟩
/-- The CCNCN'! construction in `FFL.Entailment`. -/
def CCNCN'Proof : 𝓢 ⊢! (∼φ ⇒ₗ ψ) ⇒ₗ (∼ψ ⇒ₗ φ) :=
  deduct'Proof <| CNProofOfCNProofLeft FiniteContext.idProof
omit [DecidableEq F] in
@[simp]
lemma CCNCN' : 𝓢 ⊢ (∼φ ⇒ₗ ψ) ⇒ₗ (∼ψ ⇒ₗ φ) := by classical exact ⟨CCNCN'Proof⟩
/-- The C! of CNN! construction in `FFL.Entailment`. -/
def CProofOfCNNProof (b : 𝓢 ⊢! ∼φ ⇒ₗ ∼ψ) : 𝓢 ⊢! ψ ⇒ₗ φ :=
  CProofTrans dniProof (CNProofOfCNProofLeft b)
omit [DecidableEq F] in
lemma C_of_CNN (b : 𝓢 ⊢ ∼φ ⇒ₗ ∼ψ) : 𝓢 ⊢ ψ ⇒ₗ φ := by classical exact ⟨CProofOfCNNProof b.some⟩
/-- The CCNNC! construction in `FFL.Entailment`. -/
def CCNNCProof : 𝓢 ⊢! (∼φ ⇒ₗ ∼ψ) ⇒ₗ (ψ ⇒ₗ φ) :=
  deduct'Proof <| CProofOfCNNProof FiniteContext.idProof
omit [DecidableEq F] in
@[simp]
lemma CCNNC : 𝓢 ⊢ (∼φ ⇒ₗ ∼ψ) ⇒ₗ (ψ ⇒ₗ φ) := by classical exact ⟨CCNNCProof⟩
/-- The EN! of EN! right construction in `FFL.Entailment`. -/
def ENProofOfENProofRight (h : 𝓢 ⊢! φ ⇔ₗ ∼ψ) : 𝓢 ⊢! ∼φ ⇔ₗ ψ :=
  by
  apply EProofIntro; · apply CNProofOfCNProofLeft <| KProofRight h;
  · apply CNProofOfCNProofRight <| KProofLeft h;
omit [DecidableEq F] in
lemma EN_of_EN_right (h : 𝓢 ⊢ φ ⇔ₗ ∼ψ) : 𝓢 ⊢ ∼φ ⇔ₗ ψ := by
  classical exact ⟨ENProofOfENProofRight h.some⟩
/-- The EN! of EN! left construction in `FFL.Entailment`. -/
def ENProofOfENProofLeft (h : 𝓢 ⊢! ∼φ ⇔ₗ ψ) : 𝓢 ⊢! φ ⇔ₗ ∼ψ :=
  EProofSymm <| ENProofOfENProofRight <| EProofSymm h
omit [DecidableEq F] in
lemma EN_of_EN_left (h : 𝓢 ⊢ ∼φ ⇔ₗ ψ) : 𝓢 ⊢ φ ⇔ₗ ∼ψ := by
  classical exact ⟨ENProofOfENProofLeft h.some⟩
/-- The ECCOO! construction in `FFL.Entailment`. -/
def ECCOOProof : 𝓢 ⊢! φ ⇔ₗ ((φ ⇒ₗ ⊥) ⇒ₗ ⊥) :=
  EProofTrans dnProof ENNCCOOProof
omit [DecidableEq F] in
lemma ECCOO : 𝓢 ⊢ φ ⇔ₗ ((φ ⇒ₗ ⊥) ⇒ₗ ⊥) := by classical exact ⟨ECCOOProof⟩
/-- The CNKANN! construction in `FFL.Entailment`. -/
def CNKANNProof : 𝓢 ⊢! ∼(φ ⋏ ψ) ⇒ₗ (∼φ ⋎ ∼ψ) := by
  apply CNProofOfCNProofLeft;
  apply deduct'Proof;
  exact KProofReplace (KNNProofOfNAProof <| FiniteContext.idProof) dneProof dneProof;
omit [DecidableEq F] in
@[simp]
lemma CNKANN : 𝓢 ⊢ ∼(φ ⋏ ψ) ⇒ₗ (∼φ ⋎ ∼ψ) := by classical exact ⟨CNKANNProof⟩
/-- The ANN! of NK! construction in `FFL.Entailment`. -/
def ANNProofOfNKProof (b : 𝓢 ⊢! ∼(φ ⋏ ψ)) : 𝓢 ⊢! ∼φ ⋎ ∼ψ :=
  CNKANNProof⨀b
omit [DecidableEq F] in
lemma ANN_of_NK (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := by
  classical exact ⟨ANNProofOfNKProof b.some⟩
/-- The AN! of C! construction in `FFL.Entailment`. -/
def ANProofOfCProof (d : 𝓢 ⊢! φ ⇒ₗ ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := by
  apply ofNNProof;
  apply NProofOfCOProof;
  apply deduct'Proof;
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼∼φ ⋏ ∼ψ := KNNProofOfNAProof <| FiniteContext.idProof;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ ⇒ₗ ⊥ := COProofOfNProof <| KProofLeft d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ := (ofProof (Γ := [∼(∼φ ⋎ ψ)]) <| contraProof d) ⨀ (KProofRight
      d₁);
  exact d₂ ⨀ d₃;

omit [DecidableEq F] in
lemma AN_of_C (d : 𝓢 ⊢ φ ⇒ₗ ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := by classical exact ⟨ANProofOfCProof d.some⟩
/-- The CCAN! construction in `FFL.Entailment`. -/
def CCANProof : 𝓢 ⊢! (φ ⇒ₗ ψ) ⇒ₗ (∼φ ⋎ ψ) := by
  apply deduct'Proof;
  apply ANProofOfCProof;
  exact FiniteContext.byAxmProof;
omit [DecidableEq F] in
lemma CCAN : 𝓢 ⊢ (φ ⇒ₗ ψ) ⇒ₗ ∼φ ⋎ ψ := by classical exact ⟨CCANProof⟩
instance : HasAxiomEFQ 𝓢 where
  efqProof {φ} := by
    apply CProofOfCNNProof;
    exact CProofTrans (KProofLeft negEquivProof) <| CProofTrans (CProofSwap implyKProof)
        (KProofRight negEquivProof);

instance : Entailment.Int 𝓢 where

instance : HasAxiomElimContra 𝓢 where
  elimContraProof {φ ψ} := by
    apply deduct'Proof;
    have : [∼ψ ⇒ₗ ∼φ] ⊢[𝓢]! ∼ψ ⇒ₗ ∼φ := FiniteContext.byAxmProof;
    exact CProofOfCNNProof this;

instance : HasAxiomLEM 𝓢 :=
  ⟨AProofOfANNNNProof <| ANProofOfCProof dniProof⟩

omit [DecidableEq F] in
lemma CNC_of_C_of_CN (hpq : 𝓢 ⊢ φ ⇒ₗ ψ) (hpnr : 𝓢 ⊢ φ ⇒ₗ ∼ξ) : 𝓢 ⊢ φ ⇒ₗ ∼(ψ ⇒ₗ ξ) := by
  classical
    exact
    deduct' <|
      (contra <|
          CCAN)⨀(NA_of_KNN <|
          K_intro (dni' <| of' hpq⨀FiniteContext.by_axm) (of' hpnr⨀FiniteContext.by_axm))
/-- The of A! of N! construction in `FFL.Entailment`. -/
def ofAProofOfNProof (b : 𝓢 ⊢! φ ⋎ ψ) (d : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! ψ :=
  AProofCases (CProofOfCNNProof (dhypProof d)) (CProofId) b

omit [DecidableEq F] in
theorem of_A_of_N (b : 𝓢 ⊢ φ ⋎ ψ) (d : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := by
  classical exact ⟨ofAProofOfNProof b.get d.get⟩
/-- The ECAN! construction in `FFL.Entailment`. -/
def ECANProof : 𝓢 ⊢! (φ ⇒ₗ ψ) ⇔ₗ (∼φ ⋎ ψ) :=
  EProofIntro CCANProof (deduct'Proof (AProofCases CNCProof implyKProof byAxm₀Proof))
omit [DecidableEq F] in
theorem ECAN : 𝓢 ⊢ (φ ⇒ₗ ψ) ⇔ₗ (∼φ ⋎ ψ) := by classical exact ⟨ECANProof⟩
section

omit [DecidableEq F] in
@[simp]
lemma CNDisj₂NConj₂ {Γ : List F} : 𝓢 ⊢ ∼⋁(Γ.map (∼·)) ⇒ₗ ⋀Γ := by
  classical
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons,
        List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    suffices 𝓢 ⊢ ∼(∼φ ⋎ ∼∼⋁List.map (fun x ↦ ∼x) Γ) ⇒ₗ φ ⋏ ⋀Γ by
      apply C_trans ?_ this;
      apply contra;
      apply CAA_of_C_right;
      exact dne;
    apply C_trans CNAKNN ?_;
    apply CKK_of_C_of_C;
    · exact dne;
    · exact C_trans dne ih;

lemma CNFdisj₂NFconj₂ {Γ : Finset F} :
    𝓢 ⊢
      ∼(PointwiseComposition.Finset.disj (Γ.image (∼·))) ⇒ₗ
        (PointwiseComposition.Finset.conj Γ) :=
  by
  apply C_replace ?_ ?_ <| CNDisj₂NConj₂ (Γ := Γ.toList);
  · apply contra; apply left_Disj₂_intro; intro ψ hψ; apply right_Fdisj_intro; simpa using hψ;
  · simp;

end

section consistency

omit [Entailment.Cl 𝓢]

variable [AdjunctiveSet F S] [Axiomatized S] [Deduction S] [∀ 𝓢 : S, Entailment.Cl 𝓢]

omit [DecidableEq F] in
lemma provable_iff_inconsistent_adjoin {φ : F} : 𝓢 ⊢ φ ↔ Inconsistent (adjoin (∼φ) 𝓢) := by
  classical
  constructor
  · intro h
    apply inconsistent_of_provable_of_unprovable (φ := φ)
    · exact Axiomatized.to_adjoin h
    · exact Axiomatized.adjoinProof _ _
  · intro h
    have : 𝓢 ⊢ ∼φ ⇒ₗ ⊥ := Deduction.of_insertProof (h _)
    refine of_NN <| N_iff_CO.mpr this

omit [DecidableEq F] in
lemma unprovable_iff_consistent_adjoin {φ : F} : 𝓢 ⊬ φ ↔ Consistent (adjoin (∼φ) 𝓢) := by
  classical simpa using provable_iff_inconsistent_adjoin.not

instance deductiveExplosion : Entailment.DeductiveExplosion S :=
  inferInstance

end consistency

section

instance : HasAxiomPeirce 𝓢 where
  peirceProof
    {φ
      ψ} := by
    apply ofCProofOfCProofOfAProof implyKProof ?_ lemProof; apply deduct'Proof;
    apply deductProof; refine (FiniteContext.byAxmProof (φ := (φ ⇒ₗ ψ) ⇒ₗ φ))⨀?_;
    apply deductProof; apply efqOfMemEitherProof (φ := φ); · simp;
    · simp;

instance : HasAxiomEFQ 𝓢 :=
  inferInstance

instance : Entailment.Int 𝓢 where

end

section

variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}

/-- The of Equiv construction in `FFL.Entailment.Cl`. -/
abbrev Cl.ofEquiv (𝓢 : S) [Entailment.Cl 𝓢] (𝓣 : T) (f : G →ˡᶜ F)
    (e : (φ : G) → 𝓢 ⊢! f φ ≃ 𝓣 ⊢! φ) : Entailment.Cl 𝓣
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
  dneProof := e _ (by simpa using dneProof)

end

section

variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] [Entailment S F]
  {𝓢 : S} [Entailment.Int 𝓢]

open FiniteContext

instance [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dneProof {φ} := by
    apply deduct'Proof;
    exact ofCProofOfCProofOfAProof CProofId (by
      apply deductProof;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢]! ∼φ ⇒ₗ ⊥ := COProofOfNProof <| FiniteContext.byAxmProof;
      have np : [∼φ, ∼∼φ] ⊢[𝓢]! ∼φ := FiniteContext.byAxmProof;
      exact ofOProof <| nnp ⨀ np;
    ) <| ofProof lemProof;

instance [HasAxiomLEM 𝓢] : Entailment.Cl 𝓢 where

end

end Entailment
end FFL

end

end PointwiseComposition
