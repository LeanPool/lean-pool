/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.LK.Basic

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

/-!
# Canonical model of classical first-order logic

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination [Avi01]
 -/

namespace FFL
namespace FirstOrder

variable {L : Language.{u}}

namespace LK
namespace Derivation

/-- Data and laws for Is Cut Free in `FFL.FirstOrder.LK.Derivation`. -/
inductive IsCutFree : {Γ : LK.Sequent L} → ⊢ᴸᴷ¹ Γ → Prop
  | identity (r : L.Rel k) (v) : IsCutFree (identity r v)
  | verum : IsCutFree verum
  | or {d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄} : IsCutFree d → IsCutFree d.or
  |
  and {dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄} {dψ : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄} :
    IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
  | all {d : ⊢ᴸᴷ¹ Γ⁺ + ⦃Rewriting.free φ⦄} : IsCutFree d → IsCutFree d.all
  | exs (t) {d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄} : IsCutFree d → IsCutFree d.exs
  | contraction {d : ⊢ᴸᴷ¹ Γ + ⦃φ, φ⦄} : IsCutFree d → IsCutFree d.contraction
  | weakening {d : ⊢ᴸᴷ¹ Γ} : IsCutFree d → IsCutFree (d.weakening (φ := φ))

attribute [simp] IsCutFree.identity IsCutFree.verum

variable {Γ Δ : LK.Sequent L}

-- One characterization avoids repeated dependent elimination through quotient-indexed contexts.
private def cutFreeStep {Γ : LK.Sequent L} : (⊢ᴸᴷ¹ Γ) → Prop
  | .identity _ _ => True
  | .verum => True
  | .or d => IsCutFree d
  | .and d e => IsCutFree d ∧ IsCutFree e
  | .all d => IsCutFree d
  | .exs d => IsCutFree d
  | .contraction d => IsCutFree d
  | .weakening d => IsCutFree d
  | .cut _ _ => False

private theorem isCutFree_iff_step {Γ : LK.Sequent L} (d : ⊢ᴸᴷ¹ Γ) :
    IsCutFree d ↔ cutFreeStep d := by
  constructor
  · intro h
    induction h <;> first | exact True.intro | assumption | constructor <;> assumption
  · intro h
    cases d with
    | identity r v => exact .identity r v
    | verum => exact .verum
    | or d => exact .or h
    | and d e => exact .and h.1 h.2
    | all d => exact .all h
    | exs d => exact .exs _ h
    | contraction d => exact .contraction h
    | weakening d => exact .weakening h
    | cut d e => exact False.elim h

@[simp]
lemma isCutFree_or_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ, ψ⦄} : IsCutFree d.or ↔ IsCutFree d :=
  isCutFree_iff_step d.or

@[simp]
lemma isCutFree_and_iff {dφ : ⊢ᴸᴷ¹ Γ + ⦃φ⦄} {dψ : ⊢ᴸᴷ¹ Γ + ⦃ψ⦄} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ :=
  isCutFree_iff_step (dφ.and dψ)

@[simp]
lemma isCutFree_all_iff {d : ⊢ᴸᴷ¹ Γ⁺ + ⦃Rewriting.free φ⦄} : IsCutFree d.all ↔ IsCutFree d :=
  isCutFree_iff_step d.all

@[simp]
lemma isCutFree_exs_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ/[t]⦄} : IsCutFree d.exs ↔ IsCutFree d :=
  isCutFree_iff_step d.exs

@[simp]
lemma isCutFree_contraction_iff {d : ⊢ᴸᴷ¹ Γ + ⦃φ, φ⦄} : IsCutFree d.contraction ↔ IsCutFree d :=
  isCutFree_iff_step d.contraction

@[simp]
lemma isCutFree_weakening_iff {d : ⊢ᴸᴷ¹ Γ} : IsCutFree (d.weakening (φ := φ)) ↔ IsCutFree d :=
  isCutFree_iff_step (d.weakening (φ := φ))

@[simp]
lemma IsCutFree.cast {d : ⊢ᴸᴷ¹ Γ} {e : Γ = Δ} : IsCutFree (.cast d e) ↔ IsCutFree d := by
  rcases e; rfl

@[simp]
lemma IsCutFree.not_cut (dp : ⊢ᴸᴷ¹ Γ + ⦃φ⦄) (dn : ⊢ᴸᴷ¹ Δ + ⦃∼φ⦄) : ¬IsCutFree (dp.cut dn) :=
  (isCutFree_iff_step (dp.cut dn)).mp

@[simp]
lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᴸᴷ¹ Γ} :
    IsCutFree (rewrite f d) ↔ IsCutFree d :=
  by
  induction d generalizing f <;> simp only [rewrite, IsCutFree.identity, iff_true, IsCutFree.cast,
    IsCutFree.not_cut, isCutFree_contraction_iff, *, isCutFree_weakening_iff, IsCutFree.verum,
    isCutFree_or_iff, isCutFree_and_iff, Nat.reduceAdd, isCutFree_all_iff, Nat.succ_eq_add_one,
    isCutFree_exs_iff]
  · exact .identity _ _
  · exact .verum

@[simp]
lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᴸᴷ¹ Γ} :
    IsCutFree (LK.Derivation.map d f) ↔ IsCutFree d :=
  isCutFree_rewrite_iff_isCutFree

@[simp]
lemma IsCutFree.generalizeByNewVar_isCutFree {φ : Semiproposition L 1}
    (hp : ¬φ.HasFreeVariable m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.HasFreeVariable m) (d : ⊢ᴸᴷ¹ Δ + ⦃φ/[&m]⦄) :
    IsCutFree (generalizeByNewVar hp hΔ d) ↔ IsCutFree d := by simp [generalizeByNewVar]

end Derivation
end LK

end FirstOrder

end FFL

end

end PointwiseComposition
