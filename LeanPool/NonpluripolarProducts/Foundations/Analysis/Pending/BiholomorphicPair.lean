/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.ComplexManifold
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Biholomorphic maps of coordinate domains
-/

@[expose] public section

open Set TopologicalSpace
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass

variable {n : ℕ}

/-- A biholomorphism between two open sets, given by mutually inverse maps. -/
structure IsBiholomorphicPair (A B : Opens (ComplexModel n))
    (τ σ : ComplexModel n → ComplexModel n) : Prop where
  holo : ContDiffOn ℂ ∞ τ A
  holo_inv : ContDiffOn ℂ ∞ σ B
  mapsTo : MapsTo τ A B
  mapsTo_inv : MapsTo σ B A
  left_inv : ∀ x ∈ A, σ (τ x) = x
  right_inv : ∀ w ∈ B, τ (σ w) = w

namespace IsBiholomorphicPair

variable {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

theorem image_eq (h : IsBiholomorphicPair A B τ σ) {U : Set (ComplexModel n)} (hUA : U ⊆ A) :
    τ '' U = (B : Set (ComplexModel n)) ∩ σ ⁻¹' U := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h.mapsTo (hUA hx), by simpa [h.left_inv x (hUA hx)] using hx⟩
  · rintro ⟨hwB, hw⟩
    exact ⟨σ w, hw, h.right_inv w hwB⟩

theorem preimage_inter_subset_image (h : IsBiholomorphicPair A B τ σ) (K : Set (ComplexModel n)) :
    (B : Set (ComplexModel n)) ∩ σ ⁻¹' K ⊆ τ '' K := fun w hw ↦ ⟨σ w, hw.2, h.right_inv w hw.1⟩

end IsBiholomorphicPair

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
