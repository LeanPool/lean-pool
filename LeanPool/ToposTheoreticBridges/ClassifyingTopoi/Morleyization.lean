/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Semantics

/-!
# Morleyization

Every first-order theory `T` over `L` is, up to a definitional extension, a coherent theory: the
Morleyization adds to `L` a relation symbol `R_φ` for each first-order formula `φ`
(`Morleyization.language`), with coherent axioms stating that `R_φ` is equivalent to the formula
built from the symbols of the subformulas of `φ`, and the axioms `⊤ ⊢ R_ψ` for `ψ ∈ T`
(`Morleyization.Axiom`). Negation and universal quantification, which are not geometric, are
expressed by excluded-middle axioms `⊤ ⊢ R_φ ∨ R_{φ ⇒ ψ}` and `⊤ ⊢ R_{∀φ} ∨ ∃ R_{¬φ}`.

## Main results

* `LeanPool.ClassifyingTopoi.Morleyization.relMap_iff`: in a set-model of the Morleyization
  expanding an `L`-structure, `R_φ` is interpreted by the satisfaction of `φ`;
* `LeanPool.ClassifyingTopoi.exists_morleyization`: the set-models of the Morleyization satisfy
  `T`, and every model of `T` has exactly one expansion to a set-model of the Morleyization
  (`Morleyization.canonicalStructure`).

## References

* P. T. Johnstone, *Sketches of an Elephant*, D1.5.13.
-/

@[expose] public section

universe u₁ u₂ v

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{u₁, u₂}}

namespace Morleyization

variable (L) in
/-- The language of the Morleyization of `L`: the function symbols of `L`, and as relation
symbols of arity `n` those of `L` together with a new symbol for each first-order formula of `L`
in `n` free variables. -/
def language : FirstOrder.Language.{u₁, max u₁ u₂} :=
  ⟨L.Functions, fun n => L.Relations n ⊕ L.BoundedFormula Empty n⟩

variable (L) in
/-- The inclusion of `L` into its Morleyization. -/
def lhom : L →ᴸ language L where
  onFunction _ f := f
  onRelation _ R := Sum.inl R

/-- The new relation symbol of a first-order formula. -/
abbrev formulaRel {n : ℕ} (φ : L.BoundedFormula Empty n) : (language L).Relations n :=
  Sum.inr φ

/-- A term of `L` in the variables `Empty ⊕ Fin n`, as a term of the Morleyization in the context
`Fin n`. -/
def term {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) : (language L).Term (Fin n) :=
  ((lhom L).onTerm t).relabel (Sum.elim Empty.elim id)

/-- The atomic geometric formula given by the symbol of a first-order formula, applied to the
variables of the context. -/
def symb {n : ℕ} (φ : L.BoundedFormula Empty n) : GeometricFormula.{0} (language L) n :=
  .rel (formulaRel φ) fun i => Term.var i

/-- Binary disjunction of geometric formulas, a disjunction indexed by `Bool`. -/
def or {L' : FirstOrder.Language.{u₁, u₂}} {n : ℕ} (φ ψ : GeometricFormula.{0} L' n) :
    GeometricFormula.{0} L' n :=
  .iSup fun b : Bool => cond b φ ψ

variable (T : L.Theory)

/-- The axioms of the Morleyization of a first-order theory `T`: each symbol `R_φ` is equivalent
to the formula built from the symbols of the subformulas of `φ` (implication `φ ⇒ ψ` through
`R_{φ ⇒ ψ} ∧ R_φ ⊢ R_ψ`, `R_ψ ⊢ R_{φ ⇒ ψ}` and `⊤ ⊢ R_φ ∨ R_{φ ⇒ ψ}`; universal quantification
through `R_{∀φ} ⊢ R_φ` and `⊤ ⊢ R_{∀φ} ∨ ∃ R_{¬φ}`), and `⊤ ⊢ R_ψ` for each axiom `ψ` of `T`. -/
inductive Axiom : Sequent.{0} (language L) → Prop
  | theory (ψ : L.Sentence) (h : ψ ∈ T) : Axiom ⟨0, .top, symb ψ⟩
  | falsum (n : ℕ) : Axiom ⟨n, symb (⊥ : L.BoundedFormula Empty n), GeometricFormula.bot⟩
  | equal_left {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) :
      Axiom ⟨n, symb (.equal t₁ t₂), .equal (term t₁) (term t₂)⟩
  | equal_right {n : ℕ} (t₁ t₂ : L.Term (Empty ⊕ Fin n)) :
      Axiom ⟨n, .equal (term t₁) (term t₂), symb (.equal t₁ t₂)⟩
  | rel_left {n k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (Empty ⊕ Fin n)) :
      Axiom ⟨n, symb (.rel R ts), .rel ((lhom L).onRelation R) fun i => term (ts i)⟩
  | rel_right {n k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (Empty ⊕ Fin n)) :
      Axiom ⟨n, .rel ((lhom L).onRelation R) (fun i => term (ts i)), symb (.rel R ts)⟩
  | imp_elim {n : ℕ} (φ ψ : L.BoundedFormula Empty n) :
      Axiom ⟨n, .and (symb (φ.imp ψ)) (symb φ), symb ψ⟩
  | imp_intro {n : ℕ} (φ ψ : L.BoundedFormula Empty n) : Axiom ⟨n, symb ψ, symb (φ.imp ψ)⟩
  | imp_em {n : ℕ} (φ ψ : L.BoundedFormula Empty n) :
      Axiom ⟨n, .top, or (symb φ) (symb (φ.imp ψ))⟩
  | all_elim {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
      Axiom ⟨n + 1, .rel (formulaRel φ.all) (fun i => Term.var i.castSucc),
        symb φ⟩
  | all_intro {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
      Axiom ⟨n, .top, or (symb φ.all) (.ex (symb (φ.imp ⊥)))⟩

/-- The symbol of a formula is a coherent formula. -/
theorem isCoherent_symb {n : ℕ} (φ : L.BoundedFormula Empty n) : (symb φ).IsCoherent := trivial

/-- A disjunction of two coherent formulas is coherent. -/
theorem isCoherent_or {L' : FirstOrder.Language.{u₁, u₂}} {n : ℕ} {φ ψ : GeometricFormula.{0} L' n}
    (hφ : φ.IsCoherent) (hψ : ψ.IsCoherent) : (or φ ψ).IsCoherent :=
  ⟨inferInstance, fun b => by cases b <;> assumption⟩

/-- The axioms of the Morleyization are coherent sequents. -/
theorem isCoherent_axiom {σ : Sequent.{0} (language L)} (h : Axiom T σ) :
    σ.lhs.IsCoherent ∧ σ.rhs.IsCoherent := by
  cases h <;> refine ⟨?_, ?_⟩ <;>
    first
    | trivial
    | exact ⟨inferInstance, fun i => i.elim⟩
    | exact isCoherent_or trivial trivial


/-- A binary disjunction is realized when one of the disjuncts is. -/
theorem realize_or {L' : FirstOrder.Language.{u₁, u₂}} {M : Type v} [L'.Structure M] {n : ℕ}
    (φ ψ : GeometricFormula.{0} L' n) (xs : Fin n → M) :
    (or φ ψ).Realize xs ↔ φ.Realize xs ∨ ψ.Realize xs := by
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩

section Model

variable {M : Type v} [L.Structure M] [(language L).Structure M] [(lhom L).IsExpansionOn M]

/-- Realization of a translated term in an expansion. -/
theorem realize_term {n : ℕ} (t : L.Term (Empty ⊕ Fin n)) (xs : Fin n → M) :
    (term t).realize xs = t.realize (Sum.elim (Empty.elim : Empty → M) xs) := by
  rw [term, Term.realize_relabel, LHom.realize_onTerm]
  congr 1
  funext x
  cases x with
  | inl e => exact e.elim
  | inr i => rfl

/-- In an expansion that is a set-model of the Morleyization, the symbol `R_φ` is interpreted
by the satisfaction of `φ`, by induction on `φ`. -/
theorem relMap_iff (hM : GeometricTheory.IsSetModel {σ | Axiom T σ} M) {n : ℕ}
    (φ : L.BoundedFormula Empty n) (xs : Fin n → M) :
    Structure.RelMap (formulaRel φ) xs ↔
      φ.Realize (Empty.elim : Empty → M) xs := by
  induction φ with
  | falsum =>
    exact ⟨fun h => (GeometricFormula.realize_bot _ (hM _ (Axiom.falsum _) xs h)).elim,
      fun h => h.elim⟩
  | equal t₁ t₂ =>
    have h₁ := hM _ (Axiom.equal_left t₁ t₂) xs
    have h₂ := hM _ (Axiom.equal_right t₁ t₂) xs
    simp only [GeometricFormula.Realize, realize_term] at h₁ h₂
    exact ⟨h₁, h₂⟩
  | rel R ts =>
    have h₁ := hM _ (Axiom.rel_left R ts) xs
    have h₂ := hM _ (Axiom.rel_right R ts) xs
    simp only [GeometricFormula.Realize, realize_term,
      LHom.map_onRelation] at h₁ h₂
    exact ⟨h₁, h₂⟩
  | imp φ ψ ihφ ihψ =>
    have h₁ := hM _ (Axiom.imp_elim φ ψ) xs
    have h₂ := hM _ (Axiom.imp_intro φ ψ) xs
    have h₃ := hM _ (Axiom.imp_em φ ψ) xs trivial
    rw [realize_or] at h₃
    simp only [GeometricFormula.Realize] at h₁ h₂ h₃
    rw [BoundedFormula.realize_imp, ← ihφ, ← ihψ]
    exact ⟨fun h hφ => h₁ ⟨h, hφ⟩, fun h => h₃.elim (fun hφ => h₂ (h hφ)) id⟩
  | all φ ih =>
    rw [BoundedFormula.realize_all]
    simp_rw [← ih]
    constructor
    · intro h a
      have h₁ := hM _ (Axiom.all_elim φ) (Fin.snoc xs a)
      simp only [GeometricFormula.Realize, Term.realize_var, Fin.snoc_castSucc] at h₁
      exact h₁ h
    · intro h
      have h₂ := hM _ (Axiom.all_intro φ) xs trivial
      rw [realize_or] at h₂
      simp only [GeometricFormula.Realize] at h₂
      refine h₂.resolve_right ?_
      rintro ⟨a, ha⟩
      have h₃ := hM _ (Axiom.imp_elim φ ⊥) (Fin.snoc xs a)
      have h₄ := hM _ (Axiom.falsum _) (Fin.snoc xs a)
      simp only [GeometricFormula.Realize] at h₃
      exact GeometricFormula.realize_bot _ (h₄ (h₃ ⟨ha, h a⟩))

end Model

section Canonical

variable (M : Type v) [L.Structure M]

/-- The canonical expansion of an `L`-structure to the Morleyization: each symbol `R_φ` is
interpreted by the satisfaction of `φ`. -/
abbrev canonicalStructure : (language L).Structure M where
  funMap f := Structure.funMap (L := L) f
  RelMap r := Sum.elim (fun R => Structure.RelMap (L := L) R)
    (fun φ => φ.Realize (Empty.elim : Empty → M)) r

attribute [local instance] canonicalStructure

/-- The symbol `R_φ` in the canonical expansion is the satisfaction of `φ`. -/
theorem canonicalStructure_relMap {n : ℕ} (φ : L.BoundedFormula Empty n) (xs : Fin n → M) :
    Structure.RelMap (formulaRel φ) xs ↔ φ.Realize (Empty.elim : Empty → M) xs :=
  Iff.rfl

/-- The canonical expansion is an expansion. -/
instance isExpansionOn_canonicalStructure : (lhom L).IsExpansionOn M where
  map_onFunction _ _ := rfl
  map_onRelation _ _ := rfl

/-- The canonical expansion of a model of `T` is a set-model of the Morleyization. -/
theorem isSetModel_canonicalStructure (hT : T.Model M) :
    GeometricTheory.IsSetModel {σ | Axiom T σ} M := by
  intro σ h xs hx
  cases h with
  | theory ψ h =>
    change BoundedFormula.Realize ψ (Empty.elim : Empty → M) _
    have := Theory.realize_sentence_of_mem (M := M) T h
    rwa [Sentence.Realize, Formula.Realize, Subsingleton.elim (default : Empty → M) Empty.elim,
      Subsingleton.elim (default : Fin 0 → M)] at this
  | falsum n => exact hx.elim
  | equal_left t₁ t₂ =>
    change _ = _
    rw [realize_term, realize_term]
    exact hx
  | equal_right t₁ t₂ =>
    change _ = _ at hx
    rw [realize_term, realize_term] at hx
    exact hx
  | rel_left R ts =>
    change Structure.RelMap R _
    simp only [realize_term]
    exact hx
  | rel_right R ts =>
    change Structure.RelMap R _ at hx
    simp only [realize_term] at hx
    exact hx
  | imp_elim φ ψ => exact hx.1 hx.2
  | imp_intro φ ψ => exact fun _ => hx
  | imp_em φ ψ =>
    rw [realize_or]
    exact (em _).imp id fun h h' => (h h').elim
  | all_elim φ =>
    change BoundedFormula.Realize (∀' φ) (Empty.elim : Empty → M) (Fin.init xs) at hx
    change BoundedFormula.Realize φ (Empty.elim : Empty → M) xs
    have := BoundedFormula.realize_all.1 hx (xs (Fin.last _))
    rwa [Fin.snoc_init_self] at this
  | all_intro φ =>
    rw [realize_or]
    by_cases h : ∀ a, φ.Realize (Empty.elim : Empty → M) (Fin.snoc xs a)
    · exact Or.inl (BoundedFormula.realize_all.2 h)
    · obtain ⟨a, ha⟩ := not_forall.1 h
      exact Or.inr ⟨a, fun h' => ha h'⟩

end Canonical

end Morleyization

open Morleyization in
/-- **Morleyization**: every first-order theory `T` has a geometric theory `T'`, all of whose
sequents are coherent, over a language `L'` receiving `L`, such that the set-models of `T'`
expanding an `L`-structure satisfy `T`, and every model of `T` in sets has exactly one expansion
that is a set-model of `T'`. -/
theorem exists_morleyization (T : L.Theory) :
    ∃ (L' : FirstOrder.Language.{u₁, max u₁ u₂}) (ϕ : L →ᴸ L') (T' : GeometricTheory.{0} L'),
      (∀ σ ∈ T', σ.lhs.IsCoherent ∧ σ.rhs.IsCoherent) ∧
      (∀ (M : Type v) [L.Structure M] [L'.Structure M] [ϕ.IsExpansionOn M],
        T'.IsSetModel M → T.Model M) ∧
      ∀ (M : Type v) [L.Structure M], T.Model M →
        ∃! S : L'.Structure M,
          @FirstOrder.Language.LHom.IsExpansionOn L L' ϕ M _ S ∧
            @GeometricTheory.IsSetModel L' T' M S := by
  refine ⟨language L, lhom L, {σ | Axiom T σ}, fun σ h => isCoherent_axiom T h, ?_, ?_⟩
  · intro M _ _ _ hM
    refine (Theory.model_iff T).2 fun ψ h => ?_
    have := (relMap_iff T hM ψ default).1 (hM _ (Axiom.theory ψ h) default trivial)
    rwa [Sentence.Realize, Formula.Realize, Subsingleton.elim (default : Empty → M) Empty.elim]
  · intro M _ hT
    refine ⟨canonicalStructure M, ⟨isExpansionOn_canonicalStructure M,
      isSetModel_canonicalStructure T M hT⟩, ?_⟩
    rintro S ⟨hS, hSM⟩
    have hf : ∀ {n} (f : (language L).Functions n) (xs : Fin n → M),
        S.funMap f xs = Structure.funMap (L := L) f xs :=
      fun f xs => @LHom.map_onFunction _ _ (lhom L) M _ S hS _ f xs
    have hr : ∀ {n} (r : (language L).Relations n) (xs : Fin n → M),
        S.RelMap r xs ↔ (canonicalStructure M).RelMap r xs := by
      intro n r xs
      cases r with
      | inl R => exact iff_of_eq (@LHom.map_onRelation _ _ (lhom L) M _ S hS _ R xs)
      | inr φ => exact @relMap_iff _ T M _ S hS hSM n φ xs
    obtain ⟨fS, rS⟩ := S
    congr
    · funext n f xs
      exact hf f xs
    · funext n r xs
      exact propext (hr r xs)
end LeanPool.ClassifyingTopoi
