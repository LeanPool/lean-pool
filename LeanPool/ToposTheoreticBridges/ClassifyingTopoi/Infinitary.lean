/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Semantics
public import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# Geometric logic inside infinitary first-order logic

A geometric formula is a formula of `L_{∞ω}`, the infinitary first-order logic of Tau Ceti
(`FirstOrder.Language.BoundedFormulaInf`). Its disjunctions are indexed by arbitrary types in
`Type w`, while those of Tau Ceti range over one fixed carrier, so the carrier chosen is
`Σ X : Type w, X`: the disjunction of `φ : ι → _` becomes the disjunction over the pairs `⟨X, x⟩`,
whose branch is `φ x` when `X = ι` and `⊥` otherwise. The context `Fin n` of a geometric formula
becomes its `n` bound-variable slots, with no free variables. A sequent `φ ⊢ ψ` becomes the
`L_{∞ω}` sentence `∀ x, φ(x) → ψ(x)`.

## Main definitions

* `LeanPool.ClassifyingTopoi.GeometricFormula.toInf`: the translation of geometric formulas;
* `LeanPool.ClassifyingTopoi.Sequent.toInf`: the translation of sequents into sentences.

## Main results

* `LeanPool.ClassifyingTopoi.GeometricFormula.realize_toInf`: the translation preserves
  satisfaction in every `L`-structure;
* `LeanPool.ClassifyingTopoi.Sequent.realize_toInf`,
  `LeanPool.ClassifyingTopoi.GeometricTheory.isSetModel_iff_toInf`: a structure is a set-model of
  a geometric theory exactly when it satisfies the translations of its axioms.

## References

* P. T. Johnstone, *Sketches of an Elephant*, D1.1.3 (geometric formulas as formulas of
  `L_{∞ω}`) and D1.2 (their semantics).
* O. Caramello, *Theories, Sites, Toposes*, 1.2.1, Definition 1.2.3 and the remark following it.
-/

@[expose] public section

universe w u₁ u₂ v

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{u₁, u₂}}

/-- A geometric formula as an `L_{∞ω}` formula of Tau Ceti, with no free variables, the context
as bound-variable slots, and branching carrier `Σ X : Type w, X`: the disjunction of
`φ : ι → _` becomes the disjunction over the pairs `⟨X, x⟩`, whose branch is `φ x` when `X = ι`
and `⊥` otherwise. -/
noncomputable def GeometricFormula.toInf :
    {n : ℕ} → GeometricFormula.{w} L n → L.BoundedFormulaInf (Σ X : Type w, X) Empty n
  | _, .top => ⊤
  | _, .and φ ψ => φ.toInf ⊓ ψ.toInf
  | _, .iSup (ι := ι) φ => .iSup fun p =>
      haveI := Classical.propDecidable (p.1 = ι)
      if h : p.1 = ι then (φ (cast h p.2)).toInf else ⊥
  | _, .equal t₁ t₂ => .equal (t₁.relabel Sum.inr) (t₂.relabel Sum.inr)
  | _, .rel R ts => .rel R fun i => (ts i).relabel Sum.inr
  | _, .ex φ => φ.toInf.ex

/-- The translation into Tau Ceti's `L_{∞ω}` preserves satisfaction: the translation of `φ`
holds at the assignment `x` of its bound-variable slots exactly when `φ` holds at `x`. -/
theorem GeometricFormula.realize_toInf {M : Type v} [L.Structure M] {n : ℕ}
    (φ : GeometricFormula.{w} L n) (x : Fin n → M) :
    φ.toInf.Realize (Empty.elim : Empty → M) x ↔ φ.Realize x := by
  induction φ with
  | top => simp [toInf, Realize]
  | and φ ψ ihφ ihψ => simp [toInf, Realize, ihφ, ihψ]
  | @iSup n ι φ ih =>
    simp only [toInf, BoundedFormulaInf.realize_iSup, Realize]
    constructor
    · rintro ⟨⟨X, a⟩, h⟩
      by_cases hX : X = ι
      · subst hX
        rw [dite_eq_left rfl] at h
        exact ⟨a, (ih a x).1 h⟩
      · rw [dite_eq_right hX, BoundedFormulaInf.realize_bot] at h
        exact h.elim
    · rintro ⟨i, h⟩
      exact ⟨⟨ι, i⟩, by rw [dite_eq_left rfl]; exact (ih i x).2 h⟩
  | equal t₁ t₂ =>
    simp [toInf, Realize, Term.realize_relabel, Sum.elim_comp_inr]
  | rel R ts =>
    simp [toInf, Realize, Term.realize_relabel, Sum.elim_comp_inr]
  | ex φ ih => simp [toInf, Realize, ih]

/-- A geometric sequent `φ ⊢ ψ` in the context `Fin n` as the `L_{∞ω}` sentence
`∀ x, φ(x) → ψ(x)`. -/
noncomputable def Sequent.toInf (σ : Sequent.{w} L) : L.SentenceInf (Σ X : Type w, X) :=
  (σ.lhs.toInf.imp σ.rhs.toInf).alls

/-- A structure satisfies the translation of a sequent exactly when the sequent holds in it. -/
theorem Sequent.realize_toInf (σ : Sequent.{w} L) (M : Type v) [L.Structure M] :
    σ.toInf.Realize M ↔ σ.Realize M := by
  simp only [toInf, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_imp,
    GeometricFormula.realize_toInf, Sequent.Realize]

/-- A structure is a set-model of a geometric theory exactly when it satisfies the translations
into `L_{∞ω}` of all the axioms of the theory. -/
theorem GeometricTheory.isSetModel_iff_toInf (T : GeometricTheory.{w} L) (M : Type v)
    [L.Structure M] : T.IsSetModel M ↔ ∀ σ ∈ T, σ.toInf.Realize M := by
  simp only [IsSetModel, Sequent.realize_toInf]

end LeanPool.ClassifyingTopoi
