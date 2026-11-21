/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntax
public import Mathlib.ModelTheory.Semantics

/-!
# Geometric logic: set-theoretic semantics

Satisfaction of a geometric formula in an `L`-structure on a type (Mathlib's
`FirstOrder.Language.Structure`), at an assignment `Fin n → M` of the context; validity of a
sequent; set-models of a geometric theory.

## Main results

* `LeanPool.ClassifyingTopoi.GeometricFormula.realize_hom`: geometric formulas are preserved by
  homomorphisms of structures (`FirstOrder.Language.Hom`), by induction on the formula: terms are
  preserved by `HomClass.realize_term`, relations by `Hom.map_rel`, and disjunctions and
  existentials push forward their witnesses.

The translation of geometric formulas into the infinitary first-order logic `L_{∞ω}` of
Tau Ceti (roadmap 1.2, `GeometricFormula.toInf`) is in the module
`LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Infinitary`.
-/

@[expose] public section

universe w u₁ u₂ v v'

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{u₁, u₂}}

/-- Satisfaction of a geometric formula in a structure on a type, at an assignment of
the context. -/
def GeometricFormula.Realize {M : Type v} [L.Structure M] :
    {n : ℕ} → GeometricFormula.{w} L n → (Fin n → M) → Prop
  | _, .top, _ => True
  | _, .and φ ψ, x => φ.Realize x ∧ ψ.Realize x
  | _, .iSup φ, x => ∃ i, (φ i).Realize x
  | _, .equal t₁ t₂, x => t₁.realize x = t₂.realize x
  | _, .rel R ts, x => FirstOrder.Language.Structure.RelMap R fun i => (ts i).realize x
  | _, .ex φ, x => ∃ a : M, φ.Realize (Fin.snoc x a)

/-- A sequent holds in a structure on a type when every assignment satisfying its
hypothesis satisfies its conclusion. -/
def Sequent.Realize (σ : Sequent.{w} L) (M : Type v) [L.Structure M] : Prop :=
  ∀ x : Fin σ.n → M, σ.lhs.Realize x → σ.rhs.Realize x

/-- A model of a geometric theory in sets. -/
def GeometricTheory.IsSetModel (T : GeometricTheory.{w} L) (M : Type v) [L.Structure M] : Prop :=
  ∀ σ ∈ T, σ.Realize M

/-- The false formula is satisfied nowhere. -/
@[simp]
theorem GeometricFormula.realize_bot {M : Type v} [L.Structure M] {n : ℕ} (x : Fin n → M) :
    ¬ (GeometricFormula.bot.{w} : GeometricFormula L n).Realize x := by
  rintro ⟨i, -⟩
  exact i.elim

/-- Geometric formulas are preserved by homomorphisms of structures. -/
theorem GeometricFormula.realize_hom {M : Type v} {N : Type v'} [L.Structure M]
    [L.Structure N] (f : M →[L] N) {n : ℕ} (φ : GeometricFormula.{w} L n) (x : Fin n → M)
    (h : φ.Realize x) : φ.Realize (f ∘ x) := by
  induction φ with
  | top => trivial
  | and φ ψ ihφ ihψ => exact ⟨ihφ x h.1, ihψ x h.2⟩
  | iSup φ ih =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, ih i x hi⟩
  | equal t₁ t₂ =>
    change t₁.realize (f ∘ x) = t₂.realize (f ∘ x)
    rw [HomClass.realize_term f, HomClass.realize_term f]
    exact congrArg f h
  | rel R ts =>
    change Structure.RelMap R fun i => (ts i).realize (f ∘ x)
    simp_rw [HomClass.realize_term f]
    exact f.map_rel R _ h
  | ex φ ih =>
    obtain ⟨a, ha⟩ := h
    refine ⟨f a, ?_⟩
    have := ih _ ha
    rwa [Fin.comp_snoc] at this

end LeanPool.ClassifyingTopoi
