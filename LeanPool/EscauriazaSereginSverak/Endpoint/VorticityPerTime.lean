/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLevelTwo
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLevelTwoL4
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticitySobolevSmooth

/-!
# Estimates at a fixed time for smooth approximations

The div–curl estimate and the `H²` to `L∞` embedding applied to the time slices of smooth
space-time fields whose divergence, antisymmetric derivatives or first derivatives are prescribed
on a ball (`lem:local-div-curl` and the embedding step of `thm:vorticity-regularity`), and the
locality of backward mollification.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The div–curl estimate on a time slice. -/
theorem vorticity_divCurl_slice {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (t : ℝ) (V Φ : Fin 3 → Vec3 × ℝ → ℝ),
      (∀ b, ContDiff ℝ (⊤ : ℕ∞) (V b)) → (∀ l, Continuous (Φ l)) →
      (∀ x ∈ vec3Ball x₀ R, ∑ a : Fin 3, spatialPartial (V a) a (x, t) = 0) →
      (∀ x ∈ vec3Ball x₀ R, ∀ a b : Fin 3,
        spatialPartial (V b) a (x, t) - spatialPartial (V a) b (x, t) =
          vorticityAntisym (fun l => Φ l (x, t)) a b) →
      ∫ x in vec3Ball x₀ r, ∑ a : Fin 3, ∑ b : Fin 3, spatialPartial (V b) a (x, t) ^ 2 ≤
        C * ∫ x in vec3Ball x₀ R, (∑ l : Fin 3, Φ l (x, t) ^ 2 + ∑ b : Fin 3, V b (x, t) ^ 2) := by
  obtain ⟨C₀, hC₀, hdc⟩ := vorticityDivCurlSmooth_local hr hrR
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro x₀ t V Φ hV hΦ hdiv hcurl
  set Vt : Fin 3 → Vec3 → ℝ := fun b x => V b (x, t) with hVtdef
  have hVt : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (Vt b) := fun b =>
    (hV b).comp (contDiff_id.prodMk contDiff_const)
  have h := hdc x₀ Vt hVt
  have hd : ∀ b a x, spatialDeriv (Vt b) a x = spatialPartial (V b) a (x, t) := fun _ _ _ => rfl
  simp only [hd] at h
  refine h.trans ?_
  rw [← integral_const_mul, ← integral_const_mul]
  have hcont1 : Continuous (fun x : Vec3 => (∑ a : Fin 3, spatialPartial (V a) a (x, t)) ^ 2 +
      ∑ a : Fin 3, ∑ b : Fin 3,
        (spatialPartial (V b) a (x, t) - spatialPartial (V a) b (x, t)) ^ 2 +
      ∑ b : Fin 3, V b (x, t) ^ 2) := by
    have hp : ∀ b a, Continuous (fun x : Vec3 => spatialPartial (V b) a (x, t)) := fun b a =>
      (CKN.spatialPartial_contDiff (hV b) a).continuous.comp
        (continuous_id.prodMk continuous_const)
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · exact (continuous_finsetSum _ fun a _ => hp a a).pow 2
    · exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        ((hp b a).sub (hp a b)).pow 2
    · exact continuous_finsetSum _ fun b _ =>
        ((hV b).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hcont2 : Continuous (fun x : Vec3 => 2 * C₀ *
      (∑ l : Fin 3, Φ l (x, t) ^ 2 + ∑ b : Fin 3, V b (x, t) ^ 2)) := by
    refine continuous_const.mul (Continuous.add ?_ ?_)
    · exact continuous_finsetSum _ fun l _ =>
        ((hΦ l).comp (continuous_id.prodMk continuous_const)).pow 2
    · exact continuous_finsetSum _ fun b _ =>
        ((hV b).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  apply setIntegral_mono_on ((vorticityHeatSmooth_integrableOn_ball hcont1 x₀ R).const_mul C₀)
    (vorticityHeatSmooth_integrableOn_ball hcont2 x₀ R) (isOpen_vec3Ball x₀ R).measurableSet
  intro x hx
  rw [hdiv x hx]
  have hanti : ∑ a : Fin 3, ∑ b : Fin 3,
      (spatialPartial (V b) a (x, t) - spatialPartial (V a) b (x, t)) ^ 2 ≤
        2 * ∑ l : Fin 3, Φ l (x, t) ^ 2 := by
    have h := vorticityAntisym_sq_sum_le (fun l => Φ l (x, t))
    simpa only [hcurl x hx] using h
  have hV0 : 0 ≤ ∑ b : Fin 3, V b (x, t) ^ 2 := by positivity
  have hΦ0 : 0 ≤ ∑ l : Fin 3, Φ l (x, t) ^ 2 := by positivity
  nlinarith only [hanti, hV0, hΦ0, hC₀]

/-- The `H²` to `L∞` embedding on a time slice, for a smooth field with prescribed first
derivatives on a ball. -/
theorem vorticity_sobolev_slice {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (t : ℝ) (f : Vec3 × ℝ → ℝ) (g : Fin 3 → Vec3 × ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j)) →
      (∀ x ∈ vec3Ball x₀ R, ∀ j, spatialPartial f j (x, t) = g j (x, t)) →
      ∀ x, vec3EuclideanNorm (x - x₀) ≤ r →
        f (x, t) ^ 2 ≤ C * ∫ y in vec3Ball x₀ R, (f (y, t) ^ 2 + ∑ j : Fin 3, g j (y, t) ^ 2 +
          ∑ j : Fin 3, ∑ k : Fin 3, spatialPartial (g j) k (y, t) ^ 2) := by
  obtain ⟨C, hC, hsob⟩ := vorticitySobolevSmooth_sup hr hrR
  refine ⟨C, hC, ?_⟩
  intro x₀ t f g hf hg hfg x hx
  set F : Vec3 → ℝ := fun x => f (x, t) with hFdef
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hf.comp (contDiff_id.prodMk contDiff_const)
  have h := hsob x₀ F hF x hx
  have d1 : ∀ j, ∀ y ∈ vec3Ball x₀ R, spatialDeriv F j y = g j (y, t) := fun j y hy =>
    hfg y hy j
  have d2 : ∀ j k, ∀ y ∈ vec3Ball x₀ R,
      spatialDeriv (spatialDeriv F j) k y = spatialPartial (g j) k (y, t) := by
    intro j k y hy
    exact vorticity_spatialDeriv_congr_on (isOpen_vec3Ball x₀ R) (d1 j) hy k
  have e : ∫ y in vec3Ball x₀ R, (F y ^ 2 + ∑ j : Fin 3, spatialDeriv F j y ^ 2 +
        ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv F j) k y ^ 2) =
      ∫ y in vec3Ball x₀ R, (f (y, t) ^ 2 + ∑ j : Fin 3, g j (y, t) ^ 2 +
        ∑ j : Fin 3, ∑ k : Fin 3, spatialPartial (g j) k (y, t) ^ 2) :=
    setIntegral_congr_fun (isOpen_vec3Ball x₀ R).measurableSet fun y hy => by
      simp only [F, d1 _ y hy, d2 _ _ y hy]
  rw [e, sq_abs] at h
  exact h

/-- Backward mollification commutes with the antisymmetric matrix of a vector field. -/
theorem vorticityBackMollify_antisym {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {v : Fin 3 → Vec3 × ℝ → ℝ} (hv : ∀ l, IntegrableOn (v l) W) {ε : ℝ} (hε : 0 < ε)
    (i k : Fin 3) (z : Vec3 × ℝ) :
    vorticityBackMollify W (fun y => vorticityAntisym (fun l => v l y) i k) ε hε z =
      vorticityAntisym (fun l => vorticityBackMollify W (v l) ε hε z) i k := by
  rw [← vorticityBackTest_pairing hW hε z, vorticityAntisym_eq_sum]
  have hpt : ∀ y, vorticityAntisym (fun l => v l y) i k * vorticityBackTest ε hε z y =
      ∑ l : Fin 3, vorticityEps i k l * (v l y * vorticityBackTest ε hε z y) := by
    intro y
    rw [vorticityAntisym_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hint : ∀ l, IntegrableOn (fun y => v l y * vorticityBackTest ε hε z y) W := fun l =>
    vorticity_integrableOn_mul_smooth (hv l) (vorticityBackTest_contDiff hε z).continuous
      (vorticityBackTest_hasCompactSupport hε z)
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun l _ => (hint l).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, vorticityBackTest_pairing hW hε z]

end ESS
