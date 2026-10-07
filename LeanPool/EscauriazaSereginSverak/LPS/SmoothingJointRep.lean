/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEmbeddingRep

/-!
# Smooth representatives of all-order weak families

`lem:lps-Bochner-joint-smooth`: a whole-space function whose weak derivative
family exists to every order has a `C^∞` representative, and the sup norm of
each ordered derivative is controlled by the Sobolev norm of the family.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The embedding constant of `lps_sobolevFamily_contDiff_rep` at order `k`. -/
@[expose] def lpsEmbC (k : ℕ) : ℝ := Classical.choose (lps_sobolevFamily_contDiff_rep k)

theorem lpsEmbC_nonneg (k : ℕ) : 0 ≤ lpsEmbC k :=
  (Classical.choose_spec (lps_sobolevFamily_contDiff_rep k)).1

/-- Two continuous functions that agree almost everywhere agree everywhere. -/
theorem lps_eq_of_continuous_ae_eq {g₁ g₂ : Vec3 → ℝ} (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (h : g₁ =ᵐ[volume] g₂) : g₁ = g₂ :=
  (Continuous.ae_eq_iff_eq volume h₁ h₂).mp h

/-- `lem:lps-Bochner-joint-smooth`: a function with weak families of every order
has a `C^∞` representative whose ordered derivatives represent the family, with
sup norms controlled by the Sobolev norm at each order. -/
theorem lps_sobolevFamily_smooth_rep {f : Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (h : ∀ m : ℕ, IsSobolevFamilyOn m univ f D) :
    ∃ g : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ g =ᵐ[volume] f ∧
      (∀ α : List (Fin 3), wordDeriv α g =ᵐ[volume] D α) ∧
      ∀ (k : ℕ) (α : List (Fin 3)), α.length ≤ k → ∀ x,
        |wordDeriv α g x| ≤ lpsEmbC k * Real.sqrt (sobolevNormSqOn (k + 2) univ D) := by
  have hk : ∀ k : ℕ, ∃ g : Vec3 → ℝ, ContDiff ℝ k g ∧ g =ᵐ[volume] f ∧
      (∀ α : List (Fin 3), α.length ≤ k → wordDeriv α g =ᵐ[volume] D α) ∧
      ∀ α : List (Fin 3), α.length ≤ k → ∀ x,
        |wordDeriv α g x| ≤ lpsEmbC k * Real.sqrt (sobolevNormSqOn (k + 2) univ D) :=
    fun k => (Classical.choose_spec (lps_sobolevFamily_contDiff_rep k)).2 f D (h (k + 2))
  choose gk hgkC hgkf hgkD hgkB using hk
  have hgk : ∀ k, gk k = gk 0 := fun k =>
    lps_eq_of_continuous_ae_eq (hgkC k).continuous (hgkC 0).continuous
      ((hgkf k).trans (hgkf 0).symm)
  refine ⟨gk 0, ?_, hgkf 0, ?_, ?_⟩
  · rw [contDiff_infty]
    intro n
    have := hgkC n
    rwa [hgk n] at this
  · intro α
    have := hgkD α.length α le_rfl
    rwa [hgk] at this
  · intro k α hα x
    have := hgkB k α hα x
    rwa [hgk k] at this

end ESS
