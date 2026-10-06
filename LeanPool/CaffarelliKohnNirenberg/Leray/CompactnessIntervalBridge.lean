/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessTimeExhaustion
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientEnergy

/-!
# Compactness Interval Bridge

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Uniform slice bounds on compact intervals extend to arbitrary compact
time sets inside the same interval. -/
theorem compact_time_slice_bounds_of_interval_bounds
    {U : Set Vec3} {I : Set ℝ} (hI : OrdConnected I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ Icc a b →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ T →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M := by
  intro C hC hCU T hT hTI
  obtain ⟨a, b, hTab, habI⟩ :=
    compact_time_subset_compact_interval hI hT hTI
  obtain ⟨M, hM, hMb⟩ := hbound C hC hCU a b habI
  exact ⟨M, hM, fun n t ht => hMb n t (hTab ht)⟩

/-- Integrated gradient bounds on compact intervals extend to compact time
sets by monotonicity of the outer integral. -/
theorem compact_time_gradient_bounds_of_interval_bounds
    {U : Set Vec3} {I : Set ℝ} (hI : OrdConnected I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc a b, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in T, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G := by
  intro C hC hCU T hT hTI
  obtain ⟨a, b, hTab, habI⟩ :=
    compact_time_subset_compact_interval hI hT hTI
  obtain ⟨G, hG, hGb⟩ := hbound C hC hCU a b habI
  refine ⟨G, hG, fun n => ?_⟩
  exact (lintegral_mono_set hTab).trans (hGb n)

/-- A pairing modulus on compact intervals restricts to each compact
time set in the open interval. -/
theorem compact_time_pairing_modulus_of_interval_modulus
    {U : Set Vec3} {I : Set ℝ} (hI : OrdConnected I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
          |(∫ x : Vec3, ∑ i : Fin 3, u n (x,t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, u n (x,s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ) :
    ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ T : Set ℝ, IsCompact T → T ⊆ I →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ T → t ∈ T →
          |(∫ x : Vec3, ∑ i : Fin 3, u n (x,t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, u n (x,s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ := by
  intro C hC hCU T hT hTI w hw hws hsup
  obtain ⟨a, b, hTab, habI⟩ :=
    compact_time_subset_compact_interval hI hT hTI
  obtain ⟨A, B, θ, hA, hB, hθ, hmod'⟩ :=
    hmod C hC hCU a b habI w hw hws hsup
  exact ⟨A, B, θ, hA, hB, hθ,
    fun n s t hs ht => hmod' n s t (hTab hs) (hTab ht)⟩

end CKN.Leray
