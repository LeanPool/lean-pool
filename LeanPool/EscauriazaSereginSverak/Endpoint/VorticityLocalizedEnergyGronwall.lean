/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLocalizedEnergyComponent
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Grönwall's inequality and the component solutions

The integral form of Grönwall's inequality for a continuous energy, and the
component heat solutions of the localized vorticity equation for measurable
data with `|v| ≤ M` (`lem:localized-vorticity-energy`).
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped Topology


noncomputable section

namespace ESS

open CKN.Foundation.Parabolic

/-- Grönwall's inequality in integral form. -/
theorem vl_gronwall {a τ K L : ℝ} (hat : a ≤ τ) (hL : 0 < L) {e d : ℝ → ℝ}
    (he : ContinuousOn e (Icc a τ)) (he0 : ∀ t ∈ Icc a τ, 0 ≤ e t)
    (hd0 : ∀ t ∈ Icc a τ, 0 ≤ d t)
    (hineq : ∀ t ∈ Icc a τ, e t + d t ≤ K + L * ∫ s in Ioo a t, e s) :
    ∀ t ∈ Icc a τ, e t + d t ≤ K * Real.exp (L * (t - a)) := by
  -- a continuous extension of `e`
  let eExt : ℝ → ℝ := fun s => e (projIcc a τ hat s)
  have heExtc : Continuous eExt :=
    he.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc a τ hat s).2)
  have heExteq : ∀ s ∈ Icc a τ, eExt s = e s := fun s hs => by
    simp only [eExt, projIcc_of_mem hat hs]
  let u : ℝ → ℝ := fun t => ∫ s in a..t, eExt s
  have hu_eq : ∀ t ∈ Icc a τ, u t = ∫ s in Ioo a t, e s := by
    intro t ht
    simp only [u]
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo (fun s hs => ?_)
    exact heExteq s ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hu_deriv : ∀ t, HasDerivAt u (eExt t) t := fun t =>
    (heExtc.integral_hasStrictDerivAt a t).hasDerivAt
  have hu0 : ∀ t ∈ Icc a τ, 0 ≤ u t := by
    intro t ht
    rw [hu_eq t ht]
    exact setIntegral_nonneg measurableSet_Ioo fun s hs =>
      he0 s ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := u) (f' := eExt) (δ := 0)
    (K := L) (ε := K) (a := a) (b := τ)
    (fun t _ => (hu_deriv t).continuousAt.continuousWithinAt)
    (fun t _ => (hu_deriv t).hasDerivWithinAt)
    (by simp [u])
    (by
      intro t ht
      have htI : t ∈ Icc a τ := Ico_subset_Icc_self ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by rw [heExteq t htI]; exact he0 t htI),
        Real.norm_eq_abs, abs_of_nonneg (hu0 t htI), heExteq t htI]
      have h := hineq t htI
      rw [← hu_eq t htI] at h
      linarith only [h, hd0 t htI])
  intro t ht
  have hg := hgr t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (hu0 t ht), gronwallBound_of_K_ne_0 hL.ne'] at hg
  simp only [zero_mul, zero_add] at hg
  have h := hineq t ht
  rw [← hu_eq t ht] at h
  have hmul : L * u t ≤ L * (K / L * (Real.exp (L * (t - a)) - 1)) :=
    mul_le_mul_of_nonneg_left hg hL.le
  have hsimp : L * (K / L * (Real.exp (L * (t - a)) - 1)) =
      K * Real.exp (L * (t - a)) - K := by
    field_simp
  linarith only [h, hmul, hsimp]

/-- A drift flux component is bounded by the velocity bound. -/
theorem vl_flux_abs_le {M : ℝ} {v z : Vec3} (hv : vec3EuclideanNorm v ≤ M) (i j : Fin 3) :
    |v j * z i - z j * v i| ≤ M * |z i| + M * |z j| := by
  have hvj : |v j| ≤ M := (norm_le_pi_norm v j).trans ((norm_le_vec3EuclideanNorm v).trans hv)
  have hvi : |v i| ≤ M := (norm_le_pi_norm v i).trans ((norm_le_vec3EuclideanNorm v).trans hv)
  calc
    |v j * z i - z j * v i| ≤ |v j * z i| + |z j * v i| := abs_sub _ _
    _ = |v j| * |z i| + |z j| * |v i| := by rw [abs_mul, abs_mul]
    _ ≤ M * |z i| + |z j| * M := by
      gcongr
    _ = M * |z i| + M * |z j| := by ring

/-- For measurable data, each component of a solution of the localized
vorticity equation is a weak heat solution. -/
theorem vlVector_componentSolution {a τ M : ℝ} (hat : a < τ) {z v g₀ : Vec3 × ℝ → Vec3}
    {F G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ} {z₀ : Vec3 → Vec3}
    (hzm : ∀ i, StronglyMeasurable (fun p => z p i))
    (hvm : ∀ j, StronglyMeasurable (fun p => v p j))
    (hFm : ∀ j i, StronglyMeasurable (fun p => F p j i))
    (hGm : ∀ j i, StronglyMeasurable (fun p => G p j i))
    (hgm : ∀ i, StronglyMeasurable (fun p => g₀ p i))
    (hz : ∀ i, MemLp (fun p => z p i) 2 (volume.restrict (vlSlab a τ)))
    (hv : ∀ᵐ p ∂(volume.restrict (vlSlab a τ)), vec3EuclideanNorm (v p) ≤ M)
    (hF : ∀ j i, MemLp (fun p => F p j i) 2 (volume.restrict (vlSlab a τ)))
    (hG : ∀ j i, MemLp (fun p => G p j i) 2 (volume.restrict (vlSlab a τ)))
    (hg : ∀ i, MemLp (fun p => g₀ p i) 2 (volume.restrict (vlSlab a τ)))
    (hz₀ : ∀ i, MemLp (fun x => z₀ x i) 2 volume)
    (hweak : (∀ φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (univ : Set Vec3) (Ioo a τ),
      ∫ p in vlSlab a τ, ∑ i : Fin 3, z p i *
          (-vorticityTestTimeDerivative φ p i - vorticityTestLaplacian φ p i) =
        ∫ p in vlSlab a τ, (∑ j : Fin 3, ∑ i : Fin 3,
          (v p j * z p i - z p j * v p i - F p j i - G p j i) *
            CKN.spatialPartial (fun q : Vec3 × ℝ => φ q i) j p +
          ∑ i : Fin 3, g₀ p i * φ p i)))
    (htrace : (∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ c : ℝ → ℝ, ContinuousOn c (Icc a τ) ∧ c a = ∫ x, ∑ i : Fin 3, z₀ x i * ψ x i ∧
        ∀ᵐ t ∂(volume.restrict (Ioo a τ)), c t = ∫ x, ∑ i : Fin 3, z (x, t) i * ψ x i))
    (i : Fin 3) :
    VlHeatSolution a τ (fun p => z p i)
      (fun j p => F p j i + G p j i - (v p j * z p i - z p j * v p i))
      (fun p => g₀ p i) (fun x => z₀ x i) := by
  have hBm : ∀ j, StronglyMeasurable (fun p => v p j * z p i - z p j * v p i) := fun j =>
    ((hvm j).mul (hzm i)).sub ((hzm j).mul (hvm i))
  have hB : ∀ j, MemLp (fun p => v p j * z p i - z p j * v p i) 2
      (volume.restrict (vlSlab a τ)) := by
    intro j
    refine (((hz i).norm.const_mul M).add ((hz j).norm.const_mul M)).of_le
      (hBm j).aestronglyMeasurable ?_
    filter_upwards [hv] with p hp
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (vl_flux_abs_le hp i j).trans (le_abs_self _) |>.trans_eq ?_
    simp [Real.norm_eq_abs]
  refine
    { lt := hat
      w_meas := hzm i
      H_meas := fun j => ((hFm j i).add (hGm j i)).sub (hBm j)
      f_meas := hgm i
      w_L2 := hz i
      H_L2 := fun j => ((hF j i).add (hG j i)).sub (hB j)
      f_L2 := hg i
      w₀_L2 := hz₀ i
      weak := fun φ hφ => vlVectorWeak_component hweak i hφ
      trace := fun ψ hψ hψc => vlVectorTrace_component htrace i hψ hψc }

end ESS

end
