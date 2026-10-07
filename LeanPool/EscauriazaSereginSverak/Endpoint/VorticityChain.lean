/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticitySmoothPackage

/-!
# The div–curl chain at a fixed time

At a fixed time, three applications of the div–curl estimate and one of the `H²` to `L∞`
embedding bound the smooth approximations of the first, second and third derivatives of the
velocity, and the gradient pointwise, by the vorticity and its derivatives (the velocity levels
of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Rotating the order of a triple sum. -/
theorem vorticity_sum_rotate (f : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, f l j k =
      ∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f l j k := by
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]

/-- The div–curl chain at a fixed time, on the balls of radii `ρ, ρ - 1/64, …, ρ - 4/64`. -/
theorem vorticityChain {ρ : ℝ} (hρ : 4 / 64 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (t : ℝ) (U w : Fin 3 → Vec3 × ℝ → ℝ)
      (G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (U i)) → (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (G i j)) →
      (∀ i j k, ContDiff ℝ (⊤ : ℕ∞) (D2 i j k)) → (∀ i, Continuous (w i)) →
      (∀ i j, Continuous (Ω1 i j)) → (∀ i j k, Continuous (Ω2 i j k)) →
      (∀ x ∈ vec3Ball x₀ ρ, ∑ i : Fin 3, spatialPartial (U i) i (x, t) = 0) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ i k : Fin 3, spatialPartial (U k) i (x, t) -
        spatialPartial (U i) k (x, t) = vorticityAntisym (fun l => w l (x, t)) i k) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ i j : Fin 3, spatialPartial (U i) j (x, t) = G i j (x, t)) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ m : Fin 3, ∑ i : Fin 3, spatialPartial (G i m) i (x, t) = 0) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ m i k : Fin 3, spatialPartial (G k m) i (x, t) -
        spatialPartial (G i m) k (x, t) = vorticityAntisym (fun l => Ω1 l m (x, t)) i k) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ i j k : Fin 3, spatialPartial (G i j) k (x, t) = D2 i j k (x, t)) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ j k : Fin 3,
        ∑ i : Fin 3, spatialPartial (D2 i j k) i (x, t) = 0) →
      (∀ x ∈ vec3Ball x₀ ρ, ∀ j k i c : Fin 3, spatialPartial (D2 c j k) i (x, t) -
        spatialPartial (D2 i j k) c (x, t) = vorticityAntisym (fun l => Ω2 l j k (x, t)) i c) →
      (∫ x in vec3Ball x₀ (ρ - 1 / 64), ∑ i : Fin 3, ∑ j : Fin 3, G i j (x, t) ^ 2 ≤
        C * ∫ x in vec3Ball x₀ ρ, (∑ l : Fin 3, w l (x, t) ^ 2 + ∑ i : Fin 3, U i (x, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (ρ - 2 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          D2 i j k (x, t) ^ 2 ≤
        C * ∫ x in vec3Ball x₀ (ρ - 1 / 64), (∑ l : Fin 3, ∑ m : Fin 3, Ω1 l m (x, t) ^ 2 +
          ∑ i : Fin 3, ∑ j : Fin 3, G i j (x, t) ^ 2)) ∧
      (∫ x in vec3Ball x₀ (ρ - 3 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ c : Fin 3,
          spatialPartial (D2 i j k) c (x, t) ^ 2 ≤
        C * ∫ x in vec3Ball x₀ (ρ - 2 / 64), (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          Ω2 l j k (x, t) ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k (x, t) ^ 2)) ∧
      (∀ x, vec3EuclideanNorm (x - x₀) ≤ ρ - 4 / 64 → ∀ i j : Fin 3,
        G i j (x, t) ^ 2 ≤ C * ∫ y in vec3Ball x₀ (ρ - 3 / 64), (G i j (y, t) ^ 2 +
          ∑ k : Fin 3, D2 i j k (y, t) ^ 2 +
            ∑ k : Fin 3, ∑ c : Fin 3, spatialPartial (D2 i j k) c (y, t) ^ 2)) := by
  obtain ⟨C₁, hC₁, h1⟩ := vorticity_divCurl_slice (r := ρ - 1 / 64) (R := ρ)
    (by linarith only [hρ]) (by linarith only)
  obtain ⟨C₂, hC₂, h2⟩ := vorticity_divCurl_slice (r := ρ - 2 / 64) (R := ρ - 1 / 64)
    (by linarith only [hρ]) (by linarith only)
  obtain ⟨C₃, hC₃, h3⟩ := vorticity_divCurl_slice (r := ρ - 3 / 64) (R := ρ - 2 / 64)
    (by linarith only [hρ]) (by linarith only)
  obtain ⟨C₄, hC₄, h4⟩ := vorticity_sobolev_slice (r := ρ - 4 / 64) (R := ρ - 3 / 64)
    (by linarith only [hρ]) (by linarith only)
  refine ⟨C₁ + C₂ + C₃ + C₄, by positivity, ?_⟩
  intro x₀ t U w G Ω1 D2 Ω2 hU hG hD2 hw hΩ1 hΩ2 hdivU hantiU hdU hdivG hantiG hdG hdivD hantiD
  have hsl : ∀ h : Vec3 × ℝ → ℝ, Continuous h → Continuous (fun x : Vec3 => h (x, t)) :=
    fun h hh => hh.comp (continuous_id.prodMk continuous_const)
  have hpc : ∀ h : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ∀ a : Fin 3,
      Continuous (fun x : Vec3 => spatialPartial h a (x, t)) := fun h hh a =>
    hsl _ (CKN.spatialPartial_contDiff hh a).continuous
  have hib : ∀ (h : Vec3 → ℝ) (r : ℝ), Continuous h → IntegrableOn h (vec3Ball x₀ r) :=
    fun h r hh => vorticityHeatSmooth_integrableOn_ball hh x₀ r
  have hsub : ∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → vec3Ball x₀ r₁ ⊆ vec3Ball x₀ r₂ := fun h => vec3Ball_mono h
  have hCle : ∀ (A : ℝ), 0 ≤ A → ∀ c : ℝ, 0 ≤ c → c ≤ C₁ + C₂ + C₃ + C₄ →
      c * A ≤ (C₁ + C₂ + C₃ + C₄) * A := fun A hA c _ hc => mul_le_mul_of_nonneg_right hc hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- first derivatives of the velocity
    have h := h1 x₀ t U w hU hw hdivU (fun x hx a b => hantiU x hx a b)
    have e : ∫ x in vec3Ball x₀ (ρ - 1 / 64), ∑ a : Fin 3, ∑ b : Fin 3,
        spatialPartial (U b) a (x, t) ^ 2 =
        ∫ x in vec3Ball x₀ (ρ - 1 / 64), ∑ i : Fin 3, ∑ j : Fin 3, G i j (x, t) ^ 2 :=
      setIntegral_congr_fun (isOpen_vec3Ball x₀ _).measurableSet fun x hx => by
        simp only [hdU x (hsub (by linarith only) hx)]
        exact Finset.sum_comm
    rw [e] at h
    refine h.trans (hCle _ (setIntegral_nonneg (isOpen_vec3Ball x₀ _).measurableSet
      fun x _ => by positivity) _ hC₁ (by linarith only [hC₂, hC₃, hC₄]))
  · -- second derivatives of the velocity
    have hm : ∀ m : Fin 3, ∫ x in vec3Ball x₀ (ρ - 2 / 64), ∑ a : Fin 3, ∑ b : Fin 3,
        D2 b m a (x, t) ^ 2 ≤ C₂ * ∫ x in vec3Ball x₀ (ρ - 1 / 64),
          (∑ l : Fin 3, Ω1 l m (x, t) ^ 2 + ∑ b : Fin 3, G b m (x, t) ^ 2) := by
      intro m
      have h := h2 x₀ t (fun b => G b m) (fun l => Ω1 l m) (fun b => hG b m) (fun l => hΩ1 l m)
        (fun x hx => hdivG x (hsub (by linarith only) hx) m)
        (fun x hx a b => hantiG x (hsub (by linarith only) hx) m a b)
      have e : ∫ x in vec3Ball x₀ (ρ - 2 / 64), ∑ a : Fin 3, ∑ b : Fin 3,
          spatialPartial (G b m) a (x, t) ^ 2 =
          ∫ x in vec3Ball x₀ (ρ - 2 / 64), ∑ a : Fin 3, ∑ b : Fin 3, D2 b m a (x, t) ^ 2 :=
        setIntegral_congr_fun (isOpen_vec3Ball x₀ _).measurableSet fun x hx => by
          simp only [hdG x (hsub (by linarith only) hx)]
      rwa [e] at h
    have hLi : ∀ m : Fin 3, IntegrableOn (fun x : Vec3 => ∑ a : Fin 3, ∑ b : Fin 3,
        D2 b m a (x, t) ^ 2) (vec3Ball x₀ (ρ - 2 / 64)) := fun m =>
      hib _ _ (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        (hsl _ (hD2 b m a).continuous).pow 2)
    have hRi : ∀ m : Fin 3, IntegrableOn (fun x : Vec3 => ∑ l : Fin 3, Ω1 l m (x, t) ^ 2 +
        ∑ b : Fin 3, G b m (x, t) ^ 2) (vec3Ball x₀ (ρ - 1 / 64)) := fun m =>
      hib _ _ ((continuous_finsetSum _ fun l _ => (hsl _ (hΩ1 l m)).pow 2).add
        (continuous_finsetSum _ fun b _ => (hsl _ (hG b m).continuous).pow 2))
    have eL : ∫ x in vec3Ball x₀ (ρ - 2 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        D2 i j k (x, t) ^ 2 = ∑ m : Fin 3, ∫ x in vec3Ball x₀ (ρ - 2 / 64),
          ∑ a : Fin 3, ∑ b : Fin 3, D2 b m a (x, t) ^ 2 := by
      rw [← integral_finsetSum _ fun m _ => hLi m]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    have eR : ∑ m : Fin 3, C₂ * ∫ x in vec3Ball x₀ (ρ - 1 / 64),
        (∑ l : Fin 3, Ω1 l m (x, t) ^ 2 + ∑ b : Fin 3, G b m (x, t) ^ 2) =
        C₂ * ∫ x in vec3Ball x₀ (ρ - 1 / 64), (∑ l : Fin 3, ∑ m : Fin 3, Ω1 l m (x, t) ^ 2 +
          ∑ i : Fin 3, ∑ j : Fin 3, G i j (x, t) ^ 2) := by
      rw [← Finset.mul_sum, ← integral_finsetSum _ fun m _ => hRi m]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun m l => Ω1 l m (x, t) ^ 2),
        Finset.sum_comm (f := fun m b => G b m (x, t) ^ 2)]
    rw [eL]
    refine (Finset.sum_le_sum fun m _ => hm m).trans ?_
    rw [eR]
    exact hCle _ (setIntegral_nonneg (isOpen_vec3Ball x₀ _).measurableSet
      fun x _ => by positivity) _ hC₂ (by linarith only [hC₁, hC₃, hC₄])
  · -- third derivatives of the velocity
    have hm : ∀ j k : Fin 3, ∫ x in vec3Ball x₀ (ρ - 3 / 64), ∑ a : Fin 3, ∑ b : Fin 3,
        spatialPartial (D2 b j k) a (x, t) ^ 2 ≤ C₃ * ∫ x in vec3Ball x₀ (ρ - 2 / 64),
          (∑ l : Fin 3, Ω2 l j k (x, t) ^ 2 + ∑ b : Fin 3, D2 b j k (x, t) ^ 2) := by
      intro j k
      exact h3 x₀ t (fun b => D2 b j k) (fun l => Ω2 l j k) (fun b => hD2 b j k)
        (fun l => hΩ2 l j k) (fun x hx => hdivD x (hsub (by linarith only) hx) j k)
        (fun x hx a b => hantiD x (hsub (by linarith only) hx) j k a b)
    have hLi : ∀ j k : Fin 3, IntegrableOn (fun x : Vec3 => ∑ a : Fin 3, ∑ b : Fin 3,
        spatialPartial (D2 b j k) a (x, t) ^ 2) (vec3Ball x₀ (ρ - 3 / 64)) := fun j k =>
      hib _ _ (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        (hpc _ (hD2 b j k) a).pow 2)
    have hRi : ∀ j k : Fin 3, IntegrableOn (fun x : Vec3 => ∑ l : Fin 3, Ω2 l j k (x, t) ^ 2 +
        ∑ b : Fin 3, D2 b j k (x, t) ^ 2) (vec3Ball x₀ (ρ - 2 / 64)) := fun j k =>
      hib _ _ ((continuous_finsetSum _ fun l _ => (hsl _ (hΩ2 l j k)).pow 2).add
        (continuous_finsetSum _ fun b _ => (hsl _ (hD2 b j k).continuous).pow 2))
    have eL : ∫ x in vec3Ball x₀ (ρ - 3 / 64), ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
        ∑ c : Fin 3, spatialPartial (D2 i j k) c (x, t) ^ 2 =
        ∑ j : Fin 3, ∑ k : Fin 3, ∫ x in vec3Ball x₀ (ρ - 3 / 64),
          ∑ a : Fin 3, ∑ b : Fin 3, spatialPartial (D2 b j k) a (x, t) ^ 2 := by
      rw [← Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hLi j k,
        ← integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hLi j k]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact Finset.sum_comm
    have eR : ∑ j : Fin 3, ∑ k : Fin 3, C₃ * ∫ x in vec3Ball x₀ (ρ - 2 / 64),
        (∑ l : Fin 3, Ω2 l j k (x, t) ^ 2 + ∑ b : Fin 3, D2 b j k (x, t) ^ 2) =
        C₃ * ∫ x in vec3Ball x₀ (ρ - 2 / 64), (∑ l : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          Ω2 l j k (x, t) ^ 2 + ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k (x, t) ^ 2) := by
      rw [Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm, ← Finset.mul_sum,
        ← Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hRi j k,
        ← integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hRi j k]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Finset.sum_add_distrib]
      rw [vorticity_sum_rotate (fun l j k => Ω2 l j k (x, t) ^ 2),
        vorticity_sum_rotate (fun i j k => D2 i j k (x, t) ^ 2)]
    rw [eL]
    refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hm j k).trans ?_
    rw [eR]
    exact hCle _ (setIntegral_nonneg (isOpen_vec3Ball x₀ _).measurableSet
      fun x _ => by positivity) _ hC₃ (by linarith only [hC₁, hC₂, hC₄])
  · -- the pointwise gradient bound
    intro x hx i j
    have h := h4 x₀ t (G i j) (fun k => D2 i j k) (hG i j) (fun k => hD2 i j k)
      (fun y hy k => hdG y (hsub (by linarith only) hy) i j k) x hx
    exact h.trans (hCle _ (setIntegral_nonneg (isOpen_vec3Ball x₀ _).measurableSet
      fun y _ => by positivity) _ hC₄ (by linarith only [hC₁, hC₂, hC₃]))

end ESS
