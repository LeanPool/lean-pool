/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularityCore
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityContinuityExport

/-!
# Quantitative vorticity regularity on a product box

From the velocity, its weak gradient, the velocity bound, the gradient energy and the weak
vorticity equation on a unit box, the vorticity has on the box `B_{1/2} × (t₀ - 1/4, t₀)` a
representative which is continuous and bounded up to the top time, space-time weak derivatives
in `L²`, and satisfies the differential inequality of `thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem vorticityRegularity_integral_sum1 {S : Set (Vec3 × ℝ)}
    {f : Fin 3 → Vec3 × ℝ → ℝ}
    (hf : ∀ i, Integrable (f i) (volume.restrict S)) :
    (∫ z in S, ∑ i : Fin 3, f i z) = ∑ i : Fin 3, ∫ z in S, f i z := by
  exact integral_finsetSum Finset.univ (fun i _ => hf i)

private theorem vorticityRegularity_integral_sum2 {S : Set (Vec3 × ℝ)}
    {f : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hf : ∀ i j, Integrable (f i j) (volume.restrict S)) :
    (∫ z in S, ∑ i : Fin 3, ∑ j : Fin 3, f i j z) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ z in S, f i j z := by
  rw [vorticityRegularity_integral_sum1 (fun i =>
    integrable_finsetSum Finset.univ (fun j _ => hf i j))]
  apply Finset.sum_congr rfl
  intro i hi
  exact vorticityRegularity_integral_sum1 (fun j => hf i j)

private theorem vorticityRegularity_integral_sum3 {S : Set (Vec3 × ℝ)}
    {f : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hf : ∀ i j k, Integrable (f i j k) (volume.restrict S)) :
    (∫ z in S, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k z) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∫ z in S, f i j k z := by
  rw [vorticityRegularity_integral_sum2 (fun i j =>
    integrable_finsetSum Finset.univ (fun k _ => hf i j k))]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact vorticityRegularity_integral_sum1 (fun k => hf i j k)

/-- `thm:vorticity-regularity` on a product box, retaining the stage constants and exporting
the uniform time-slice `H²` bound. -/
theorem vorticityRegularity_box_quantified (M K₀ : ℝ) (hM : 0 ≤ M) :
    ∃ Kw K1 K2 C Cslice Cw : ℝ, 0 ≤ C ∧ 0 ≤ Cslice ∧ 0 ≤ Cw ∧
      ∀ (x₀ : Vec3) (t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
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
    ∃ (ω : Fin 3 → Vec3 × ℝ → ℝ) (Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
      (Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (Dt : Fin 3 → Vec3 × ℝ → ℝ),
      (∀ i, ContinuousOn (ω i)
        ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 1 / 2} ×ˢ Icc (t₀ - 1 / 4) t₀)) ∧
      (∀ i, ∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 1 / 2} ×ˢ Icc (t₀ - 1 / 4) t₀ :
        Set (Vec3 × ℝ)), |ω i z| ≤ C) ∧
      (∀ i, ω i =ᵐ[volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)]
        vorticityCurl G i) ∧
      (∀ i, MemLp (ω i) 2 (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀))) ∧
      (∀ i j, MemLp (Ω1 i j) 2
        (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀))) ∧
      (∀ i j k, MemLp (Ω2 i j k) 2
        (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀))) ∧
      (∀ i, MemLp (Dt i) 2 (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀))) ∧
      (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ →
        ∫ y in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀, ω i y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀, Ω1 i j y * ψ y) ∧
      (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ →
        ∫ y in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀, Ω1 i j y * spatialPartial ψ k y =
          -∫ y in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀, Ω2 i j k y * ψ y) ∧
      (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ →
        ∫ y in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀, ω i y * timePartial ψ y =
          -∫ y in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀, Dt i y * ψ y) ∧
      (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)), ∀ i,
        |Dt i z - ∑ j : Fin 3, Ω2 i j j z| ≤
          C * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|)) ∧
      (∀ i : Fin 3, ∀ t ∈ Icc (t₀ - 1 / 4) t₀, ∃ Gt : Fin 3 → Vec3 → ℝ,
        ∃ Ht : Fin 3 → Fin 3 → Vec3 → ℝ,
          (∀ j, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) j
            (fun x => ω i (x, t)) (Gt j)) ∧
          (∀ j k, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) k
            (Gt j) (Ht j k)) ∧
          ∫ x in vec3Ball x₀ (38 / 64),
            (ω i (x, t) ^ 2 + ∑ j : Fin 3, Gt j x ^ 2 +
              ∑ j : Fin 3, ∑ k : Fin 3, Ht j k x ^ 2) ≤
            Cslice * (|Kw| + |K1| + |K2| + 1)) ∧
      Real.sqrt (∫ z in vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀,
        (∑ i : Fin 3, ω i z ^ 2) +
          (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) +
          (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2) +
          (∑ i : Fin 3, Dt i z ^ 2)) ≤ Cw := by
  obtain ⟨Kw, K1, K2, hst⟩ := vorticityStages M K₀ hM
  obtain ⟨K, hK, hgrad⟩ := vorticityFinal_gradBound M Kw K1 K2 hM
  obtain ⟨Cc, Cslice, hCc, hCslice, hcont⟩ := vorticity_continuousRep_export Kw K1 K2
  set Cw : ℝ := Real.sqrt (3 * |Kw| + 63 * |K1| + 189 * |K2|)
  refine ⟨Kw, K1, K2, Cc + 6 * (K + M), Cslice, Cw, by positivity, hCslice,
    Real.sqrt_nonneg _, ?_⟩
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
  have hWo5 := vorticityBox_isOpen x₀ (43 / 64)
    (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀
  have hWb5 := vorticityBox_isBounded x₀ (43 / 64) _
    (Metric.isBounded_Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀)
  have hU5 := fun i => rM b50 (hU i)
  have hUb5 := ae_restrict_of_ae_restrict_of_subset b50 hUb
  have hG5 := fun i j => rM b50 (hG i j)
  have hdU5 := fun i j => vorticity_weakPartial_restrict b50 (hdU i j)
  have hdiv5 := vorticityDiv_restrict b50 hdiv
  have hheat5 := fun i => vorticityHeat_restrict b50 (hheat i)
  have hFm5 := fun i j =>
    vorticityFluxOf_memLp (fun i => (hU5 i).aestronglyMeasurable) hG5 hUb5 i j
  have hw5 := vorticityCurl_memLp hG5
  have hGb := hgrad x₀ (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ U G Ω1
    (fun i j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) D2 Ω2
    (vorticityFluxDeriv U G Ω1) (vorticityFluxDeriv2 U G Ω1 D2 Ω2) (by linarith only [])
    (by linarith only []) hU5 hUb5 hG5 hD2 hΩ1 hΩ2 hFm5 hF' hF'' hdU5 hdG hdw hdΩ hdiv5 hheat5
    hhΩ1 hhΩ2 hKw hK1 hK2
  set a : ℝ := t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32
  have hrep : ∀ i : Fin 3, ∃ ωi : Vec3 × ℝ → ℝ,
      ContinuousOn ωi ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀) ∧
      (∀ z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ Icc (a + 1 / 64) t₀ :
          Set (Vec3 × ℝ)), |ωi z| ≤ Cc) ∧
      ωi =ᵐ[volume.restrict (vec3Ball x₀ (38 / 64) ×ˢ Ioo (a + 1 / 64) t₀)]
        vorticityCurl G i ∧ (∀ t ∈ Icc (a + 1 / 64) t₀,
        ∃ Gt : Fin 3 → Vec3 → ℝ, ∃ Ht : Fin 3 → Fin 3 → Vec3 → ℝ,
          (∀ j, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) j (fun x => ωi (x, t)) (Gt j)) ∧
          (∀ j k, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) k (Gt j) (Ht j k)) ∧
          ∫ x in vec3Ball x₀ (38 / 64), (ωi (x, t) ^ 2 + ∑ j : Fin 3, Gt j x ^ 2 +
            ∑ j : Fin 3, ∑ k : Fin 3, Ht j k x ^ 2) ≤
              Cslice * (|Kw| + |K1| + |K2| + 1)) := by
    intro i
    obtain ⟨ε, hεpos, ωi, hωc, hωb, hωae, hTU, hωslice⟩ :=
      hcont x₀ a t₀
        (vorticityCurl G i) (fun m => Ω1 i m)
        (fun j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z))
        (fun m k => Ω2 i m k) (fun m j => vorticityFluxDeriv U G Ω1 i j m)
        (fun m k j => vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k)
        (by dsimp [a]; linarith only []) (by dsimp [a]; linarith only [])
        (hw5 i) (fun m => hΩ1 i m)
        (fun m k => hΩ2 i m k) (fun j => hFm5 i j) (fun m j => hF' i j m)
        (fun m k j => hF'' i j m k) (hdw i) (hdΩ i) (hheat5 i) (hhΩ1 i) (hhΩ2 i)
        (hKw i) (fun m => hK1 i m) (fun m k => hK2 i m k)
    refine ⟨ωi, hωc, hωb, ?_, ?_⟩
    · exact hωae
    · intro t ht
      exact hωslice t ht
  choose ω hωc hωb hωae hωslice using hrep
  have bS5 : (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ : Set (Vec3 × ℝ)) ⊆
      vec3Ball x₀ (43 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ :=
    vorticityBox_subset x₀ t₀ (by norm_num) (by linarith only [])
  have bSB : (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ : Set (Vec3 × ℝ)) ⊆
      vec3Ball x₀ (38 / 64) ×ˢ
        Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32 + 1 / 64) t₀ :=
    vorticityBox_subset x₀ t₀ (by norm_num) (by linarith only [])
  have hSb := vorticityBox_isBounded x₀ (1 / 2) _ (Metric.isBounded_Ioo (t₀ - 1 / 4) t₀)
  have : IsFiniteMeasure (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) :=
    isFiniteMeasure_restrict.2 hSb.measure_lt_top.ne
  have hint : ∀ {f : Vec3 × ℝ → ℝ},
      MemLp f 2 (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) →
      IntegrableOn f (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀) :=
    fun hf => hf.integrable (by norm_num)
  have hKK : ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 1 / 2} ×ˢ Icc (t₀ - 1 / 4) t₀ :
      Set (Vec3 × ℝ)) ⊆ {x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 38 / 64} ×ˢ
        Icc (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32 + 1 / 64) t₀ := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨le_trans (show vec3EuclideanNorm (x - x₀) ≤ 1 / 2 from hx) (by norm_num), ?_, ht2⟩
    linarith only [ht1]
  have hωS : ∀ i, ω i =ᵐ[volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)]
      vorticityCurl G i := fun i => ae_restrict_of_ae_restrict_of_subset bSB (hωae i)
  let F0 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z =>
    -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)
  let Dt : Fin 3 → Vec3 × ℝ → ℝ := fun i z =>
    ∑ j : Fin 3, Ω2 i j j z + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z
  let S : Set (Vec3 × ℝ) := vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀
  let T : Set (Vec3 × ℝ) := vec3Ball x₀ (43 / 64) ×ˢ Ioo a t₀
  let A : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, (vorticityCurl G i z ^ 2 + ∑ j : Fin 3, F0 i j z ^ 2)
  let B : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ m : Fin 3,
      (Ω1 i m z ^ 2 + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2)
  let D : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
      (Ω2 i m k z ^ 2 + ∑ j : Fin 3,
        vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2)
  have hF0Lp : ∀ i j, MemLp (F0 i j) 2 (volume.restrict T) := by
    intro i j
    simpa [F0, T, a] using hFm5 i j
  have hAint : IntegrableOn A T := by
    apply integrable_finsetSum
    intro i hi
    exact ((hw5 i).integrable_sq).add
      (integrable_finsetSum _ fun j _ => (hF0Lp i j).integrable_sq)
  have hBint : IntegrableOn B T := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro m hm
    exact ((hΩ1 i m).integrable_sq).add
      (integrable_finsetSum _ fun j _ => (hF' i j m).integrable_sq)
  have hDint : IntegrableOn D T := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro m hm
    apply integrable_finsetSum
    intro k hk
    exact ((hΩ2 i m k).integrable_sq).add
      (integrable_finsetSum _ fun j _ => (hF'' i j m k).integrable_sq)
  have hAstage : ∀ i, ∫ z in T,
      vorticityCurl G i z ^ 2 + ∑ j : Fin 3, F0 i j z ^ 2 ≤ Kw := by
    intro i
    simpa [F0, T, a] using hKw i
  have hBstage : ∀ i m, ∫ z in T,
      Ω1 i m z ^ 2 + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤ K1 := by
    intro i m
    simpa [T, a] using hK1 i m
  have hDstage : ∀ i m k, ∫ z in T,
      Ω2 i m k z ^ 2 + ∑ j : Fin 3,
        vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2 ≤ K2 := by
    intro i m k
    simpa [T, a] using hK2 i m k
  have hAintBound : ∫ z in T, A z ≤ 3 * Kw := by
    calc
      ∫ z in T, A z = ∑ i : Fin 3,
          ∫ z in T, (vorticityCurl G i z ^ 2 + ∑ j : Fin 3, F0 i j z ^ 2) := by
        simpa [A] using vorticityRegularity_integral_sum1 (S := T)
          (f := fun i z => vorticityCurl G i z ^ 2 + ∑ j : Fin 3, F0 i j z ^ 2)
          (fun i => ((hw5 i).integrable_sq).add
            (integrable_finsetSum Finset.univ (fun j _ => (hF0Lp i j).integrable_sq)))
      _ ≤ ∑ _i : Fin 3, Kw := Finset.sum_le_sum fun i _ => hAstage i
      _ = 3 * Kw := by rw [Fin.sum_univ_three]; ring
  have hBintBound : ∫ z in T, B z ≤ 9 * K1 := by
    calc
      ∫ z in T, B z = ∑ i : Fin 3, ∑ m : Fin 3,
          ∫ z in T, (Ω1 i m z ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2) := by
        simpa [B] using vorticityRegularity_integral_sum2 (S := T)
          (f := fun i m z => Ω1 i m z ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2)
          (fun i m => ((hΩ1 i m).integrable_sq).add
            (integrable_finsetSum Finset.univ (fun j _ => (hF' i j m).integrable_sq)))
      _ ≤ ∑ _i : Fin 3, ∑ _m : Fin 3, K1 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => hBstage i m
      _ = 9 * K1 := by rw [Fin.sum_univ_three, Fin.sum_univ_three]; ring
  have hDintBound : ∫ z in T, D z ≤ 27 * K2 := by
    calc
      ∫ z in T, D z = ∑ i : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3,
          ∫ z in T, (Ω2 i m k z ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2) := by
        simpa [D] using vorticityRegularity_integral_sum3 (S := T)
          (f := fun i m k z => Ω2 i m k z ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2)
          (fun i m k => ((hΩ2 i m k).integrable_sq).add
            (integrable_finsetSum Finset.univ (fun j _ => (hF'' i j m k).integrable_sq)))
      _ ≤ ∑ _i : Fin 3, ∑ _m : Fin 3, ∑ _k : Fin 3, K2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ =>
          Finset.sum_le_sum fun k _ => hDstage i m k
      _ = 27 * K2 := by
        rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
        ring
  have hDtLp : ∀ i, MemLp (Dt i) 2 (volume.restrict S) := by
    intro i
    dsimp [Dt]
    exact (memLp_finsetSum _ fun j _ => rM bS5 (hΩ2 i j j)).add
      (memLp_finsetSum _ fun j _ => rM bS5 (hF' i j j))
  have hωLp : ∀ i, MemLp (ω i) 2 (volume.restrict S) := fun i =>
    (rM bS5 (hw5 i)).ae_eq (hωS i).symm
  have hW21int : IntegrableOn (fun z =>
      (∑ i : Fin 3, ω i z ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2) +
        (∑ i : Fin 3, Dt i z ^ 2)) S := by
    have hωsq : Integrable (fun z => ∑ i : Fin 3, ω i z ^ 2) (volume.restrict S) :=
      integrable_finsetSum Finset.univ (fun i _ => (hωLp i).integrable_sq)
    have hΩ1sq : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2)
        (volume.restrict S) :=
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
        (fun j _ => (rM bS5 (hΩ1 i j)).integrable_sq))
    have hΩ2sq : Integrable
        (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2)
        (volume.restrict S) :=
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
        (fun j _ => integrable_finsetSum Finset.univ
          (fun k _ => (rM bS5 (hΩ2 i j k)).integrable_sq)))
    have hDtsq : Integrable (fun z => ∑ i : Fin 3, Dt i z ^ 2) (volume.restrict S) :=
      integrable_finsetSum Finset.univ (fun i _ => (hDtLp i).integrable_sq)
    exact ((hωsq.add hΩ1sq).add hΩ2sq).add hDtsq
  have hRint : IntegrableOn (fun z => A z + 7 * B z + 7 * D z) T := by
    have hR : IntegrableOn (fun z => A z + (7 * B z + 7 * D z)) T :=
      hAint.add ((hBint.const_mul 7).add (hDint.const_mul 7))
    simpa only [add_assoc] using hR
  have hωSall : ∀ᵐ z ∂(volume.restrict S), ∀ i, ω i z = vorticityCurl G i z :=
    ae_all_iff.2 hωS
  have hpoint : ∀ᵐ z ∂(volume.restrict S),
      (∑ i : Fin 3, ω i z ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2) +
        (∑ i : Fin 3, Dt i z ^ 2) ≤ A z + 7 * B z + 7 * D z := by
    filter_upwards [hωSall] with z hωz
    have hωeq : (∑ i : Fin 3, ω i z ^ 2) = ∑ i : Fin 3, vorticityCurl G i z ^ 2 :=
      Finset.sum_congr rfl fun i _ => congrArg (fun r : ℝ => r ^ 2) (hωz i)
    have hΩ1base : (∑ i : Fin 3, ∑ m : Fin 3, Ω1 i m z ^ 2) ≤ B z := by
      dsimp [B]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ =>
        le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hΩ2base : (∑ i : Fin 3, ∑ m : Fin 3, ∑ k : Fin 3, Ω2 i m k z ^ 2) ≤ D z := by
      dsimp [D]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ =>
        Finset.sum_le_sum fun k _ =>
          le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hωbase : (∑ i : Fin 3, vorticityCurl G i z ^ 2) ≤ A z := by
      dsimp [A]
      exact Finset.sum_le_sum fun i _ =>
        le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hdiagΩ2 : (∑ i : Fin 3, ∑ m : Fin 3, Ω2 i m m z ^ 2) ≤ D z := by
      dsimp [D]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ =>
        (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
          (Finset.single_le_sum
            (f := fun k => Ω2 i m k z ^ 2 + ∑ j : Fin 3,
              vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2)
            (fun k _ => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
            (Finset.mem_univ m))
    have hdiagF : (∑ i : Fin 3, ∑ m : Fin 3,
        vorticityFluxDeriv U G Ω1 i m m z ^ 2) ≤ B z := by
      dsimp [B]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ =>
        le_trans
          (Finset.single_le_sum
            (f := fun j => vorticityFluxDeriv U G Ω1 i j m z ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ m))
          (le_add_of_nonneg_left (sq_nonneg _))
    have hdt : ∀ i, Dt i z ^ 2 ≤ 6 *
        ((∑ j : Fin 3, Ω2 i j j z ^ 2) +
          ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z ^ 2) := by
      intro i
      have hsumΩ := vorticity_sq_sum_three_le (fun j => Ω2 i j j z)
      have hsumF := vorticity_sq_sum_three_le
        (fun j => vorticityFluxDeriv U G Ω1 i j j z)
      have hadd : ((∑ j : Fin 3, Ω2 i j j z) +
          ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z) ^ 2 ≤
          2 * ((∑ j : Fin 3, Ω2 i j j z) ^ 2 +
            (∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z) ^ 2) := by
        nlinarith only [sq_nonneg ((∑ j : Fin 3, Ω2 i j j z) -
          ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z)]
      dsimp [Dt]
      nlinarith only [hadd, hsumΩ, hsumF]
    have hDtbase : (∑ i : Fin 3, Dt i z ^ 2) ≤ 6 * (D z + B z) := by
      calc
        _ ≤ ∑ i : Fin 3, 6 *
            ((∑ j : Fin 3, Ω2 i j j z ^ 2) +
              ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z ^ 2) :=
          Finset.sum_le_sum fun i _ => hdt i
        _ = 6 * ((∑ i : Fin 3, ∑ m : Fin 3, Ω2 i m m z ^ 2) +
            ∑ i : Fin 3, ∑ m : Fin 3, vorticityFluxDeriv U G Ω1 i m m z ^ 2) := by
          simp only [Fin.sum_univ_three]
          ring
        _ ≤ 6 * (D z + B z) := by
          gcongr
    calc
      _ = (∑ i : Fin 3, vorticityCurl G i z ^ 2) +
          (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) +
          (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2) +
          (∑ i : Fin 3, Dt i z ^ 2) := by rw [hωeq]
      _ ≤ A z + B z + D z + 6 * (D z + B z) :=
        add_le_add (add_le_add (add_le_add hωbase hΩ1base) hΩ2base) hDtbase
      _ = A z + 7 * B z + 7 * D z := by ring
  have hW21intBound : ∫ z in S,
      (∑ i : Fin 3, ω i z ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) +
        (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k z ^ 2) +
        (∑ i : Fin 3, Dt i z ^ 2) ≤
      3 * |Kw| + 63 * |K1| + 189 * |K2| := by
    have hRintS : IntegrableOn (fun z => A z + 7 * B z + 7 * D z) S := hRint.mono_set bS5
    have hnonneg : ∀ z, 0 ≤ A z + 7 * B z + 7 * D z := by
      intro z
      dsimp [A, B, D]
      positivity
    have hAabs : ∫ z in T, A z ≤ 3 * |Kw| :=
      hAintBound.trans (mul_le_mul_of_nonneg_left (le_abs_self Kw) (by norm_num))
    have hBabs : ∫ z in T, B z ≤ 9 * |K1| :=
      hBintBound.trans (mul_le_mul_of_nonneg_left (le_abs_self K1) (by norm_num))
    have hDabs : ∫ z in T, D z ≤ 27 * |K2| :=
      hDintBound.trans (mul_le_mul_of_nonneg_left (le_abs_self K2) (by norm_num))
    have hsplit : ∫ z in T, A z + 7 * B z + 7 * D z =
        (∫ z in T, A z) + 7 * (∫ z in T, B z) + 7 * (∫ z in T, D z) := by
      calc
        ∫ z in T, (A z + 7 * B z) + 7 * D z =
            (∫ z in T, A z + 7 * B z) + (∫ z in T, 7 * D z) :=
          integral_add (hAint.add (hBint.const_mul 7)).integrable (hDint.const_mul 7)
        _ = (∫ z in T, A z) + 7 * (∫ z in T, B z) + 7 * (∫ z in T, D z) := by
          rw [integral_add hAint.integrable (hBint.const_mul 7),
            integral_const_mul, integral_const_mul]
    calc
      _ ≤ ∫ z in S, A z + 7 * B z + 7 * D z := integral_mono_ae hW21int hRintS hpoint
      _ ≤ ∫ z in T, A z + 7 * B z + 7 * D z :=
        setIntegral_mono_set hRint (Eventually.of_forall hnonneg) bS5.eventuallyLE
      _ = (∫ z in T, A z) + 7 * (∫ z in T, B z) + 7 * (∫ z in T, D z) := hsplit
      _ ≤ 3 * |Kw| + 63 * |K1| + 189 * |K2| := by
        have hBscaled := mul_le_mul_of_nonneg_left hBabs (by norm_num : (0 : ℝ) ≤ 7)
        have hDscaled := mul_le_mul_of_nonneg_left hDabs (by norm_num : (0 : ℝ) ≤ 7)
        calc
          _ ≤ 3 * |Kw| + 7 * (9 * |K1|) + 7 * (27 * |K2|) :=
            add_le_add (add_le_add hAabs hBscaled) hDscaled
          _ = 3 * |Kw| + 63 * |K1| + 189 * |K2| := by ring
  refine ⟨ω, Ω1, Ω2, Dt,
      fun i => (hωc i).mono hKK, fun i z hz => (hωb i z (hKK hz)).trans
      (le_add_of_nonneg_right (by positivity)), hωS,
    hωLp, fun i j => rM bS5 (hΩ1 i j),
    fun i j k => rM bS5 (hΩ2 i j k), fun i => hDtLp i, fun i j => ?_,
    fun i j k => vorticity_weakPartial_restrict bS5 (hdΩ i j k), fun i => ?_, ?_, ?_, ?_⟩
  · intro ψ hψ hψc hψS
    refine (integral_congr_ae ((hωS i).mono fun z hz =>
      congrArg (fun r => r * spatialPartial ψ j z) hz)).trans ?_
    exact vorticity_weakPartial_restrict bS5 (hdw i j) ψ hψ hψc hψS
  · intro ψ hψ hψc hψS
    refine (integral_congr_ae ((hωS i).mono fun z hz =>
      congrArg (fun r => r * timePartial ψ z) hz)).trans ?_
    exact vorticityHeat_timeDeriv (g := fun j => Ω1 i j) (h := fun j => Ω2 i j j)
      (F := fun j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z))
      (Fd := fun j => vorticityFluxDeriv U G Ω1 i j j) (hint (rM bS5 (hw5 i)))
      (fun j => hint (rM bS5 (hΩ2 i j j))) (fun j => hint (rM bS5 (hFm5 i j)))
      (fun j => hint (rM bS5 (hF' i j j))) (vorticityHeat_restrict bS5 (hheat5 i))
      (fun j => vorticity_weakPartial_restrict bS5 (hdw i j))
      (fun j => vorticity_weakPartial_restrict bS5 (hdΩ i j j))
      (fun j => vorticity_weakPartial_restrict bS5
        (vorticityFlux_weakDeriv hWo5 hWb5 hU5 hG5 hΩ1 hdU5 hdw i j j)) ψ hψ hψc hψS
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset bSB hGb,
      ae_restrict_of_ae_restrict_of_subset bS5 hUb5, ae_all_iff.2 hωS] with z hGz hUz hωz i
    have hA0 : 0 ≤ ∑ l : Fin 3, |ω l z| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hB0 : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hwA : ∀ l, |vorticityCurl G l z| ≤ ∑ l : Fin 3, |ω l z| := fun l => by
      rw [← hωz l]
      exact Finset.single_le_sum (f := fun l => |ω l z|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    have hΩB : ∀ a b, |Ω1 a b z| ≤ ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z| := fun a b =>
      (Finset.single_le_sum (f := fun b => |Ω1 a b z|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, |Ω1 a b z|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a))
    have hj : ∀ j, |vorticityFluxDeriv U G Ω1 i j j z| ≤
        2 * (K * ∑ l : Fin 3, |ω l z|) + 2 * (M * ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) := by
      intro j
      refine le_trans (vorticity_abs_neg_sub_le (G j j z * vorticityCurl G i z)
        (U j z * Ω1 i j z) (Ω1 j j z * U i z) (vorticityCurl G j z * G i j z)) ?_
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      have t1 := mul_le_mul (hGz j j) (hwA i) (abs_nonneg _) hK
      have t2 := mul_le_mul (hUz j) (hΩB i j) (abs_nonneg _) hM
      have t3 := mul_le_mul (hUz i) (hΩB j j) (abs_nonneg _) hM
      have t4 := mul_le_mul (hGz i j) (hwA j) (abs_nonneg _) hK
      rw [mul_comm |Ω1 j j z|, mul_comm |vorticityCurl G j z|]
      linarith only [t1, t2, t3, t4]
    show |(∑ j : Fin 3, Ω2 i j j z + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z) -
      ∑ j : Fin 3, Ω2 i j j z| ≤ (Cc + 6 * (K + M)) *
        (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|)
    rw [add_sub_cancel_left]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hj j).trans ?_)
    rw [Fin.sum_univ_three]
    have e : (Cc + 6 * (K + M)) *
        (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) =
        Cc * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) +
          6 * (K * ∑ l : Fin 3, |ω l z|) + 6 * (K * ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) +
          6 * (M * ∑ l : Fin 3, |ω l z|) +
          6 * (M * ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) := by ring
    have p1 := mul_nonneg hCc (add_nonneg hA0 hB0)
    have p2 := mul_nonneg hK hB0
    have p3 := mul_nonneg hM hA0
    linarith only [e, p1, p2, p3]
  · intro i t ht
    have ht' : t ∈ Icc (a + 1 / 64) t₀ := by
      refine ⟨?_, ht.2⟩
      dsimp [a]
      linarith only [ht.1]
    obtain ⟨Gt, Ht, hGt, hHt, hbound⟩ := hωslice i t ht'
    exact ⟨Gt, Ht, hGt, hHt, hbound⟩
  · have hsqrt := Real.sqrt_le_sqrt hW21intBound
    simpa [Cw, S, Dt] using hsqrt

end ESS
