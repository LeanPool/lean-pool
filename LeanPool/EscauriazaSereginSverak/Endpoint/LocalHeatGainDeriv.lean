/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainCutoff

/-!
# Heat equations for spatial derivatives

If `∂ₜ u - Δ u = g` in distributions on `ℝ³ × I` and `U_k` is the
distributional derivative `∂_k u`, then `∂ₜ U_k - Δ U_k = ∂_k g` in divergence
form, and in source form when `∂_k g` is a function. Iterating along the words
of a space-time derivative family gives the equations for all spatial
derivatives of a solution up to the order of its source.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem spatialPartial_neg_of_contDiff {A : Vec3 × ℝ → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (j : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ => -A q) j p = -spatialPartial A j p := by
  rw [vorticityHeatSmooth_spatialPartial_eq hA.neg, vorticityHeatSmooth_spatialPartial_eq hA,
    fderiv_fun_neg]
  simp

/-- The spatial derivative of the backward heat operator applied to a test
function is the backward heat operator applied to its spatial derivative. -/
theorem spatialPartial_backwardHeat {φ : Vec3 × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : Fin 3) (p : Vec3 × ℝ) :
    spatialPartial (fun q : Vec3 × ℝ =>
        -timePartial φ q - ∑ j : Fin 3, spatialSecondPartial φ j j q) k p =
      -timePartial (fun q : Vec3 × ℝ => spatialPartial φ k q) p -
        ∑ j : Fin 3, spatialSecondPartial (fun q : Vec3 × ℝ => spatialPartial φ k q) j j p := by
  have hA : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => -timePartial φ q) :=
    (vorticityHeatSmooth_timePartial_contDiff hφ).neg
  have hB (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => spatialSecondPartial φ j j q) :=
    vorticityHeatSmooth_spatialPartial_contDiff
      (vorticityHeatSmooth_spatialPartial_contDiff hφ j) j
  rw [spatialPartial_sub_sum hA hB k p,
    spatialPartial_neg_of_contDiff (vorticityHeatSmooth_timePartial_contDiff hφ) k p]
  have ht : spatialPartial (fun q : Vec3 × ℝ => timePartial φ q) k p =
      timePartial (fun q : Vec3 × ℝ => spatialPartial φ k q) p :=
    (timePartial_spatialPartial_comm hφ p k).symm
  have hs (j : Fin 3) : spatialPartial (fun q : Vec3 × ℝ => spatialSecondPartial φ j j q) k p =
      spatialSecondPartial (fun q : Vec3 × ℝ => spatialPartial φ k q) j j p :=
    (congrFun (spatialSecondPartial_spaceTimeWord [k] j hφ) p).symm
  rw [ht, Finset.sum_congr rfl fun j _ => hs j]

/-- A spatial derivative of a solution with source `g` solves the heat
equation with the divergence-form source `∂_k g`. -/
theorem heatSolution_deriv_flux {I : Set ℝ} {u g Uk : Vec3 × ℝ → ℝ} {k : Fin 3}
    (hheat : IsHeatSolutionOn univ I u g)
    (hk : IsSpaceTimeWeakPartial ((univ : Set Vec3) ×ˢ I) k u Uk) :
    ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set Vec3) ×ˢ I →
      ∫ p in (univ : Set Vec3) ×ˢ I,
          Uk p * (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
        -∫ p in (univ : Set Vec3) ×ˢ I, g p * spatialPartial φ k p := by
  intro φ hφ hφc hφV
  let ψ : Vec3 × ℝ → ℝ := fun q => -timePartial φ q - ∑ j : Fin 3, spatialSecondPartial φ j j q
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (vorticityHeatSmooth_timePartial_contDiff hφ).neg.sub
      (ContDiff.sum (s := Finset.univ) fun j _ =>
        vorticityHeatSmooth_spatialPartial_contDiff
          (vorticityHeatSmooth_spatialPartial_contDiff hφ j) j)
  have hψsupp : Function.support ψ ⊆ tsupport φ := by
    intro p hp
    by_contra hpt
    apply hp
    simp only [ψ, CKN.timePartial_eq_zero_off_tsupport hpt,
      fun j => CKN.spatialSecondPartial_eq_zero_off_tsupport hpt j j,
      Finset.sum_const_zero, neg_zero, sub_zero]
  have hψc : HasCompactSupport ψ := hφc.mono' hψsupp
  have hψV : tsupport ψ ⊆ (univ : Set Vec3) ×ˢ I :=
    (closure_minimal hψsupp (isClosed_tsupport φ)).trans hφV
  have hdφ : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial φ k q) :=
    vorticityHeatSmooth_spatialPartial_contDiff hφ k
  have hdφc : HasCompactSupport (fun q : Vec3 × ℝ => spatialPartial φ k q) :=
    CKN.hasCompactSupport_spatialPartial hφc k
  have hdφV : tsupport (fun q : Vec3 × ℝ => spatialPartial φ k q) ⊆ (univ : Set Vec3) ×ˢ I := by
    refine (closure_minimal (fun p hp => ?_) (isClosed_tsupport φ)).trans hφV
    by_contra hpt
    exact hp (CKN.spatialPartial_eq_zero_off_tsupport hpt k)
  have h1 := hk ψ hψ hψc hψV
  have h2 := hheat (fun q : Vec3 × ℝ => spatialPartial φ k q) hdφ hdφc hdφV
  have h3 : ∫ p in (univ : Set Vec3) ×ˢ I, u p * spatialPartial ψ k p =
      ∫ p in (univ : Set Vec3) ×ˢ I, u p *
        (-timePartial (fun q : Vec3 × ℝ => spatialPartial φ k q) p -
          ∑ j : Fin 3, spatialSecondPartial (fun q : Vec3 × ℝ => spatialPartial φ k q) j j p) :=
    integral_congr_ae (ae_of_all _ fun p =>
      congrArg (fun c => u p * c) (spatialPartial_backwardHeat hφ k p))
  change ∫ p in (univ : Set Vec3) ×ˢ I, Uk p * ψ p = _
  rw [h3, h2] at h1
  linarith only [h1]

/-- If moreover `∂_k g` is a function, the derivative solves the heat
equation with source `∂_k g`. -/
theorem heatSolution_deriv_source {I : Set ℝ} {u g Uk gk : Vec3 × ℝ → ℝ} {k : Fin 3}
    (hheat : IsHeatSolutionOn univ I u g)
    (hk : IsSpaceTimeWeakPartial ((univ : Set Vec3) ×ˢ I) k u Uk)
    (hgk : IsSpaceTimeWeakPartial ((univ : Set Vec3) ×ˢ I) k g gk) :
    IsHeatSolutionOn univ I Uk gk := by
  intro φ hφ hφc hφV
  rw [heatSolution_deriv_flux hheat hk φ hφ hφc hφV, hgk φ hφ hφc hφV, neg_neg]

/-- The heat equations along a derivative family, through the order of the
source. -/
theorem heatSolution_family_source {I : Set ℝ} {m : ℕ} {Dw DH : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hw : IsSpaceTimeFamily m ((univ : Set Vec3) ×ˢ I) Dw)
    (hH : IsSpaceTimeFamily (m - 1) ((univ : Set Vec3) ×ˢ I) DH)
    (hheat : IsHeatSolutionOn univ I (Dw []) (DH [])) :
    ∀ β : List (Fin 3), β.length ≤ m - 1 → IsHeatSolutionOn univ I (Dw β) (DH β) := by
  intro β
  induction β using List.reverseRecOn with
  | nil => exact fun _ => hheat
  | append_singleton β k ih =>
      intro hβ
      have hlen : β.length + 1 ≤ m - 1 := by
        simpa only [List.length_append, List.length_singleton] using hβ
      exact heatSolution_deriv_source (ih (by omega)) (hw.weak β k (by omega))
        (hH.weak β k (by omega))

/-- The top-order heat equations in divergence form. -/
theorem heatSolution_family_flux {I : Set ℝ} {m : ℕ} {Dw DH : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hw : IsSpaceTimeFamily m ((univ : Set Vec3) ×ˢ I) Dw)
    (hH : IsSpaceTimeFamily (m - 1) ((univ : Set Vec3) ×ˢ I) DH)
    (hheat : IsHeatSolutionOn univ I (Dw []) (DH [])) (hm : 1 ≤ m)
    (β : List (Fin 3)) (hβ : β.length ≤ m - 1) (k : Fin 3) :
    ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ (univ : Set Vec3) ×ˢ I →
      ∫ p in (univ : Set Vec3) ×ˢ I,
          Dw (β ++ [k]) p * (-timePartial φ p - ∑ j : Fin 3, spatialSecondPartial φ j j p) =
        -∫ p in (univ : Set Vec3) ×ˢ I, DH β p * spatialPartial φ k p :=
  heatSolution_deriv_flux (heatSolution_family_source hw hH hheat β hβ)
    (hw.weak β k (by omega))

end ESS
