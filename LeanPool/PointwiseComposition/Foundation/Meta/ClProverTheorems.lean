/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public meta import LeanPool.PointwiseComposition.Foundation.Meta.Lit
public meta import LeanPool.PointwiseComposition.Foundation.Meta.TwoSided
public import LeanPool.PointwiseComposition.Foundation.Meta.Lit
public import LeanPool.PointwiseComposition.Foundation.Meta.TwoSided

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Proof automation based on the proof search on $\mathbf{LK}$
-/

public meta section

namespace FFL
namespace Meta

open _root_.Lean Mathlib _root_.Qq Qq Lean Elab Meta Tactic

namespace ClProver

namespace Theorems

open Entailment TwoSided FiniteContext

variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] {S : Type*}
  [Entailment S F] (𝓢 : S) [Entailment.Cl 𝓢]

local notation Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ

omit [DecidableEq F] in
lemma to_provable (φ) (h : [] ⟹ [φ]) : 𝓢 ⊢ φ := by classical exact TwoSided.to_provable h

omit [DecidableEq F] in
lemma rotate_right (Γ Δ φ) (hφ : Γ ⟹ Δ ++ [φ]) : Γ ⟹ φ :: Δ := by
  classical exact TwoSided.rotate_right hφ

omit [DecidableEq F] in
lemma rotate_left (Γ Δ φ) (hφ : (Γ ++ [φ]) ⟹ Δ) : (φ :: Γ) ⟹ Δ := by
  classical exact TwoSided.rotate_left hφ

omit [DecidableEq F] in
lemma add_hyp (𝒯 : S) (s : 𝒯 ≼ 𝓢) (Γ Δ φ) (hφ : 𝒯 ⊢ φ) (h : (φ :: Γ) ⟹ Δ) : Γ ⟹ Δ := by
  classical exact TwoSided.add_hyp hφ h

omit [DecidableEq F] in
lemma right_closed (Γ Δ φ) (h : φ ∈ Γ) : Γ ⟹ φ :: Δ := by
  classical exact TwoSided.right_closed h

omit [DecidableEq F] in
lemma left_closed (Γ Δ φ) (h : φ ∈ Δ) : (φ :: Γ) ⟹ Δ := by
  classical exact TwoSided.left_closed h

omit [DecidableEq F] in
lemma verum_right (Γ Δ) : Γ ⟹ ⊤ :: Δ := by classical exact TwoSided.verum_right

omit [DecidableEq F] in
lemma falsum_left (Γ Δ) : (⊥ :: Γ) ⟹ Δ := by classical exact TwoSided.falsum_left

omit [DecidableEq F] in
lemma falsum_right (Γ Δ) (h : Γ ⟹ Δ) : Γ ⟹ ⊥ :: Δ := by classical exact TwoSided.falsum_right h

omit [DecidableEq F] in
lemma verum_left (Γ Δ) (h : Γ ⟹ Δ) : (⊤ :: Γ) ⟹ Δ := by classical exact TwoSided.verum_left h

omit [DecidableEq F] in
lemma and_right (Γ Δ φ ψ) (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ⟹ Δ ++ [ψ]) : Γ ⟹ φ ⋏ ψ :: Δ := by
  classical exact TwoSided.and_right (weakening hφ) (weakening hψ)

omit [DecidableEq F] in
lemma or_left (Γ Δ φ ψ) (hφ : (Γ ++ [φ]) ⟹ Δ) (hψ : (Γ ++ [ψ]) ⟹ Δ) : (φ ⋎ ψ :: Γ) ⟹ Δ := by
  classical exact TwoSided.or_left (weakening hφ) (weakening hψ)

omit [DecidableEq F] in
lemma or_right (Γ Δ φ ψ) (h : Γ ⟹ Δ ++ [φ, ψ]) : Γ ⟹ φ ⋎ ψ :: Δ := by
  classical exact TwoSided.or_right (weakening h)

omit [DecidableEq F] in
lemma and_left (Γ Δ φ ψ) (h : (Γ ++ [φ, ψ]) ⟹ Δ) : (φ ⋏ ψ :: Γ) ⟹ Δ := by
  classical exact TwoSided.and_left (weakening h)

omit [DecidableEq F] in
lemma neg_right (Γ Δ φ) (h : (Γ ++ [φ]) ⟹ Δ) : Γ ⟹ ∼φ :: Δ := by
  classical exact TwoSided.neg_right_cl (weakening h)

omit [DecidableEq F] in
lemma neg_left (Γ Δ φ) (h : Γ ⟹ Δ ++ [φ]) : (∼φ :: Γ) ⟹ Δ := by
  classical exact TwoSided.neg_left (weakening h)

omit [DecidableEq F] in
lemma imply_right (Γ Δ φ ψ) (h : (Γ ++ [φ]) ⟹ Δ ++ [ψ]) : Γ ⟹ (φ ⇒ₗ ψ) :: Δ := by
  classical exact TwoSided.imply_right_cl (weakening h)

omit [DecidableEq F] in
lemma imply_left (Γ Δ φ ψ) (hφ : Γ ⟹ Δ ++ [φ]) (hψ : (Γ ++ [ψ]) ⟹ Δ) : ((φ ⇒ₗ ψ) :: Γ) ⟹ Δ := by
  classical exact TwoSided.imply_left (weakening hφ) (weakening hψ)

omit [DecidableEq F] in
lemma iff_right (Γ Δ φ ψ) (hr : (Γ ++ [φ]) ⟹ Δ ++ [ψ]) (hl : (Γ ++ [ψ]) ⟹ Δ ++ [φ]) :
    Γ ⟹ (φ ⇔ₗ ψ) :: Δ := by classical exact TwoSided.iff_right_cl (weakening hr) (weakening hl)

omit [DecidableEq F] in
lemma iff_left (Γ Δ φ ψ) (hr : Γ ⟹ Δ ++ [φ, ψ]) (hl : (Γ ++ [φ, ψ]) ⟹ Δ) :
    ((φ ⇔ₗ ψ) :: Γ) ⟹ Δ := by classical exact TwoSided.iff_left (weakening hr) (weakening hl)

end Theorems

end ClProver

end Meta
end FFL

end

end PointwiseComposition
