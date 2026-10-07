/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingHeatPairing

/-!
# Spatial pairing of a differentiated momentum equation

For one scalar component and one ordered derivative, whole-space
integration by parts converts the Laplacian into gradient dissipation
and moves tensor divergence onto the test derivative.
-/

public section

open MeasureTheory
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The spatial energy pairing of a differentiated momentum component
(`eq:lps-regularized-Hm-identity`). -/
theorem lps_spatial_energy_component
    {h q p : Vec3 → ℝ} {F : Fin 3 → Vec3 → ℝ} (i : Fin 3)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hF : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (F j))
    (h0 : MemLp h 2 volume)
    (h1 : ∀ j : Fin 3, MemLp (spatialDeriv h j) 2 volume)
    (h2 : ∀ j : Fin 3,
      MemLp (spatialDeriv (spatialDeriv h j) j) 2 volume)
    (hF0 : ∀ j : Fin 3, MemLp (F j) 2 volume)
    (hF1 : ∀ j : Fin 3, MemLp (spatialDeriv (F j) j) 2 volume)
    (hp1 : MemLp (spatialDeriv p i) 2 volume)
    (hPDE : ∀ x : Vec3,
      q x = (∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x) -
        (∑ j : Fin 3, spatialDeriv (F j) j x) -
          spatialDeriv p i x) :
    (∫ x : Vec3, h x * q x) +
      ∑ j : Fin 3, ∫ x : Vec3, spatialDeriv h j x ^ 2 =
        (∑ j : Fin 3,
          ∫ x : Vec3, spatialDeriv h j x * F j x) -
          ∫ x : Vec3, h x * spatialDeriv p i x := by
  have hheatInt : Integrable (fun x : Vec3 => h x *
      (∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x)) volume := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ => h0.integrable_mul (h2 j))
  have htransportInt : Integrable (fun x : Vec3 => h x *
      (∑ j : Fin 3, spatialDeriv (F j) j x)) volume := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ => h0.integrable_mul (hF1 j))
  have hpressureInt : Integrable
      (fun x : Vec3 => h x * spatialDeriv p i x) volume :=
    h0.integrable_mul hp1
  have hheat := lps_heat_pairing_laplacian hh h0 h1 h2
  have htransport :
      (∫ x : Vec3, h x * (∑ j : Fin 3, spatialDeriv (F j) j x)) =
        -(∑ j : Fin 3,
          ∫ x : Vec3, spatialDeriv h j x * F j x) := by
    calc
      _ = ∑ j : Fin 3, ∫ x : Vec3, h x * spatialDeriv (F j) j x := by
        simp_rw [Finset.mul_sum]
        exact integral_finsetSum _ (fun j _ => h0.integrable_mul (hF1 j))
      _ = ∑ j : Fin 3,
          -(∫ x : Vec3, spatialDeriv h j x * F j x) := by
            apply Finset.sum_congr rfl
            intro j _
            exact lps_divergence_pairing_direction
              hh (hF j) j h0 (h1 j) (hF0 j) (hF1 j)
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hPDEint : (∫ x : Vec3, h x * q x) =
      (∫ x : Vec3, h x *
        (∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x)) -
      (∫ x : Vec3, h x *
        (∑ j : Fin 3, spatialDeriv (F j) j x)) -
      (∫ x : Vec3, h x * spatialDeriv p i x) := by
    simp_rw [hPDE]
    have hpoint (x : Vec3) :
        h x * ((∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x) -
          (∑ j : Fin 3, spatialDeriv (F j) j x) -
            spatialDeriv p i x) =
          h x * (∑ j : Fin 3, spatialDeriv (spatialDeriv h j) j x) -
            h x * (∑ j : Fin 3, spatialDeriv (F j) j x) -
              h x * spatialDeriv p i x := by ring
    simp_rw [hpoint]
    have hsub1 := integral_sub hheatInt htransportInt
    have hsub2 := integral_sub (hheatInt.sub htransportInt) hpressureInt
    simpa only [Pi.sub_apply, hsub1] using hsub2
  rw [hPDEint, hheat, htransport]
  ring

end ESS
