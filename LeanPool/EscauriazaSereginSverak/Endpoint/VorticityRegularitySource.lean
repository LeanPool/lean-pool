/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure

/-!
# Essential velocity-gradient bound in the vorticity regularity conclusion

The pointwise gradient estimate for the weak velocity gradient holds almost everywhere on the
open past half-cylinder. This records that estimate alongside the continuous vorticity and
space-time derivative conclusions of `thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The pointwise gradient estimate on the half-box from the vorticity stages. -/
theorem vorticityRegularity_gradient_box (M K₀ : ℝ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) →
    (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀)), ∀ i, |U i z| ≤ M) →
    ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤ K₀ →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ y in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, U i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, G i j y * ψ y) →
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ y in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, U i y * spatialPartial ψ i y = 0) →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀,
          vorticityCurl G i z * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀,
          ∑ j : Fin 3, -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z) *
            spatialPartial ψ j z) →
    ∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)),
      Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2) ≤ 3 * K := by
  obtain ⟨Kw, K1, K2, hst⟩ := vorticityStages M K₀ hM
  obtain ⟨K, hK, hgrad⟩ := vorticityFinal_gradBound M Kw K1 K2 hM
  refine ⟨K, hK, ?_⟩
  intro x₀ t₀ U G hU hG hUb hK0 hdU hdiv hheat
  obtain ⟨Ω1, D2, Ω2, hD2, hΩ1, hΩ2, hF', hF'', hdG, hdw, hdΩ, hhΩ1, hhΩ2, hKw, hK1, hK2⟩ :=
    hst x₀ t₀ U G hU hG hUb hK0 hdU hdiv hheat
  have b50 : (vec3Ball x₀ (43 / 64) ×ˢ
      Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ : Set (Vec3 × ℝ)) ⊆
        vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ :=
    vorticityBox_subset x₀ t₀ (by norm_num) (by linarith only [])
  have rM : ∀ {S T : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}, S ⊆ T →
      MemLp f 2 (volume.restrict T) → MemLp f 2 (volume.restrict S) :=
    fun h hf => hf.mono_measure (Measure.restrict_mono h le_rfl)
  have hU5 := fun i => rM b50 (hU i)
  have hUb5 := ae_restrict_of_ae_restrict_of_subset b50 hUb
  have hG5 := fun i j => rM b50 (hG i j)
  have hdU5 := fun i j => vorticity_weakPartial_restrict b50 (hdU i j)
  have hdiv5 := vorticityDiv_restrict b50 hdiv
  have hheat5 := fun i => vorticityHeat_restrict b50 (hheat i)
  have hFm5 := fun i j =>
    vorticityFluxOf_memLp (fun i => (hU5 i).aestronglyMeasurable) hG5 hUb5 i j
  have hw5 := vorticityCurl_memLp hG5
  have hWo5 := vorticityBox_isOpen x₀ (43 / 64)
    (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀
  have hWb5 := vorticityBox_isBounded x₀ (43 / 64) _
    (Metric.isBounded_Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀)
  have hGb := hgrad x₀ (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ U G Ω1
    (fun i j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) D2 Ω2
    (vorticityFluxDeriv U G Ω1) (vorticityFluxDeriv2 U G Ω1 D2 Ω2) (by linarith only [])
    (by linarith only []) hU5 hUb5 hG5 hD2 hΩ1 hΩ2 hFm5 hF' hF'' hdU5 hdG hdw hdΩ hdiv5 hheat5
    hhΩ1 hhΩ2 hKw hK1 hK2
  have bS : (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ : Set (Vec3 × ℝ)) ⊆
      vec3Ball x₀ (38 / 64) ×ˢ
        Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32 + 1 / 64) t₀ :=
    vorticityBox_subset x₀ t₀ (by norm_num) (by linarith only [])
  have hGbS := ae_restrict_of_ae_restrict_of_subset bS hGb
  filter_upwards [hGbS] with z hz
  have hsq : ∀ i j : Fin 3, G i j z ^ 2 ≤ K ^ 2 := by
    intro i j
    nlinarith only [hz i j, hK, abs_nonneg (G i j z), sq_abs (G i j z)]
  have hsum : ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤ 9 * K ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, K ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq i j
      _ = 9 * K ^ 2 := by rw [Fin.sum_univ_three, Fin.sum_univ_three]; ring
  calc
    Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2) ≤ Real.sqrt (9 * K ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = 3 * K := by
      rw [show (9 : ℝ) * K ^ 2 = (3 * K) ^ 2 by ring, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by positivity)]

end ESS
