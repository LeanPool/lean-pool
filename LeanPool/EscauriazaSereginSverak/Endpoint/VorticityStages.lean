/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityStagesTools

/-!
# The chain of interior estimates for the vorticity

From the velocity, its weak gradient, the velocity bound, the gradient energy and the weak
vorticity equation on a unit box, the interior estimates of `thm:vorticity-regularity` produce,
on a smaller box, the first and second spatial derivatives of the vorticity and the second
derivatives of the velocity, the heat equations they solve, and bounds depending only on the
velocity bound and the gradient energy.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The interior estimates of `thm:vorticity-regularity` up to the second derivatives of the
vorticity. -/
theorem vorticityStages (M K₀ : ℝ) (hM : 0 ≤ M) :
    ∃ Kw K1 K2 : ℝ, ∀ (x₀ : Vec3) (t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
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
    ∃ (Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (D2 Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
      (∀ i j k, MemLp (D2 i j k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ
        Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀))) ∧
      (∀ i j, MemLp (Ω1 i j) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ
        Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀))) ∧
      (∀ i j k, MemLp (Ω2 i j k) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ
        Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀))) ∧
      (∀ i j m, MemLp (vorticityFluxDeriv U G Ω1 i j m) 2 (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ
        Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀))) ∧
      (∀ i j m k, MemLp (vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k) 2
        (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀))) ∧
      (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ →
        ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            G i j y * spatialPartial ψ k y =
          -∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀, D2 i j k y * ψ y) ∧
      (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ →
        ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            vorticityCurl G i y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀, Ω1 i j y * ψ y) ∧
      (∀ i j k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ →
        ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            Ω1 i j y * spatialPartial ψ k y =
          -∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀, Ω2 i j k y * ψ y) ∧
      (∀ i m : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ →
        ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            Ω1 i m y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
          -∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y * spatialPartial ψ j y) ∧
      (∀ i m k : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ →
        ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            Ω2 i m k y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
          -∫ y in vec3Ball x₀ (43 / 64) ×ˢ
            Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
            ∑ j : Fin 3, vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k y * spatialPartial ψ j y) ∧
      (∀ i, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
        (vorticityCurl G i y ^ 2 +
          ∑ j : Fin 3, (-(U j y * vorticityCurl G i y - vorticityCurl G j y * U i y)) ^ 2) ≤
            Kw) ∧
      (∀ i m, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
        (Ω1 i m y ^ 2 + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) ≤ K1) ∧
      (∀ i m k, ∫ y in vec3Ball x₀ (43 / 64) ×ˢ
          Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀,
        (Ω2 i m k y ^ 2 + ∑ j : Fin 3, vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k y ^ 2) ≤ K2) := by
  obtain ⟨K₁, -, hL1⟩ := vorticityLevelOne_heat M K₀
  obtain ⟨K₂, -, hDC⟩ := vorticityLevelOne_divCurl K₀ K₁
  obtain ⟨K₄, -, hL4⟩ := vorticityLevelTwo_L4 M K₀ K₂ hM
  obtain ⟨K₃, -, hL2⟩ := vorticityLevelTwo M K₁ K₄
  obtain ⟨KS, -, hSP⟩ := vorticityLevelThree_SP M ((2 + 24 * M ^ 2) * K₀)
    ((1 + 24 * M ^ 2) * K₁ + 48 * K₄) K₀ K₂ K₃ hM
  refine ⟨(2 + 24 * M ^ 2) * K₀, (1 + 24 * M ^ 2) * K₁ + 48 * K₄,
    (1 + 48 * M ^ 2) * K₃ + 192 * KS, ?_⟩
  intro x₀ t₀ U G hU hG hUb hK hdU hdiv hheat
  have box : ∀ {r R a b : ℝ}, r ≤ R → a ≤ b →
      (vec3Ball x₀ r ×ˢ Ioo b t₀ : Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ R ×ˢ Ioo a t₀ :=
    fun h1 h2 => vorticityBox_subset x₀ t₀ h1 h2
  have rM : ∀ {S T : Set (Vec3 × ℝ)} {f : Vec3 × ℝ → ℝ}, S ⊆ T →
      MemLp f 2 (volume.restrict T) → MemLp f 2 (volume.restrict S) :=
    fun h hf => hf.mono_measure (Measure.restrict_mono h le_rfl)
  have sq2 : ∀ {S : Set (Vec3 × ℝ)} (f : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
      (∀ i j, MemLp (f i j) 2 (volume.restrict S)) →
      Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, f i j z ^ 2) (volume.restrict S) :=
    fun f hf => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hf i j).integrable_sq
  have sq3 : ∀ {S : Set (Vec3 × ℝ)} (f : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
      (∀ i j k, MemLp (f i j k) 2 (volume.restrict S)) →
      Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, f i j k z ^ 2)
        (volume.restrict S) :=
    fun f hf => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => (hf i j k).integrable_sq
  -- level one
  obtain ⟨Ω1, hΩ1, hdw1, hbΩ1⟩ := hL1 x₀ t₀ U G hU hG hUb hK hheat
  obtain ⟨D2, hD2, hdG2, hbD2⟩ := hDC x₀ t₀ U G Ω1 hU hG hK hdU hdiv hΩ1 hdw1 hbΩ1
  -- the fourth power of the gradient
  have b20 : (vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀ : Set (Vec3 × ℝ)) ⊆
      vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ := box (by norm_num) (by linarith only [])
  obtain ⟨hS3i, hS3⟩ := hL4 x₀ (t₀ - 1 + 1 / 16 + 1 / 16) t₀ U G D2 (fun i => rM b20 (hU i))
    (ae_restrict_of_ae_restrict_of_subset b20 hUb) (fun i j => rM b20 (hG i j))
    (vorticity_setIntegral_le_of_subset b20 (sq2 G hG) (fun z => by positivity) hK) hD2 hbD2
    (fun i j => vorticity_weakPartial_restrict b20 (hdU i j)) hdG2
  -- level two
  have b30 : (vec3Ball x₀ (13 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ := box (by norm_num) (by linarith only [])
  have b31 : (vec3Ball x₀ (13 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀ :=
    box (by norm_num) (by linarith only [])
  obtain ⟨Ω2, hΩ2, hdΩ2, hbΩ2⟩ := hL2 x₀ (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16) t₀ U G Ω1
    (by linarith only []) (by linarith only []) (fun i => rM b30 (hU i))
    (ae_restrict_of_ae_restrict_of_subset b30 hUb) (fun i j => rM b30 (hG i j)) hS3i hS3
    (fun i j => rM b31 (hΩ1 i j))
    (vorticity_setIntegral_le_of_subset b31 (sq2 Ω1 hΩ1) (fun z => by positivity) hbΩ1)
    (fun i j => vorticity_weakPartial_restrict b30 (hdU i j))
    (fun i j => vorticity_weakPartial_restrict b31 (hdw1 i j))
    (fun i => vorticityHeat_restrict b30 (hheat i))
  -- level three: the data on the box of radius 48/64
  have b40 : (vec3Ball x₀ (48 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ := box (by norm_num) (by linarith only [])
  have b41 : (vec3Ball x₀ (48 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀ :=
    box (by norm_num) (by linarith only [])
  have b42 : (vec3Ball x₀ (48 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀ :=
    box (by norm_num) (by linarith only [])
  have b43 : (vec3Ball x₀ (48 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆ vec3Ball x₀ (13 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :=
    box (by norm_num) (by linarith only [])
  have b44 : (vec3Ball x₀ (48 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :
      Set (Vec3 × ℝ)) ⊆
        vec3Ball x₀ (12 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :=
    box (by norm_num) (by linarith only [])
  have hWo4 := vorticityBox_isOpen x₀ (48 / 64) (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀
  have hWb4 := vorticityBox_isBounded x₀ (48 / 64) _
    (Metric.isBounded_Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀)
  have hfin4 : IsFiniteMeasure (volume.restrict (vec3Ball x₀ (48 / 64) ×ˢ
      Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀)) :=
    isFiniteMeasure_restrict.2 hWb4.measure_lt_top.ne
  have hU4 := fun i => rM b40 (hU i)
  have hUb4 := ae_restrict_of_ae_restrict_of_subset b40 hUb
  have hG4 := fun i j => rM b40 (hG i j)
  have hD24 := fun i j k => rM b42 (hD2 i j k)
  have hΩ14 := fun i j => rM b41 (hΩ1 i j)
  have hΩ24 := fun i j k => rM b44 (hΩ2 i j k)
  have hFm4 := fun i j => vorticityFluxOf_memLp (fun i => (hU4 i).aestronglyMeasurable) hG4 hUb4 i j
  have hS4i := hS3i.mono_measure (Measure.restrict_mono b43 le_rfl)
  have hF'4 := fun i j m => vorticityFluxDeriv_memLp hU4 hUb4 hG4 hS4i hΩ14 i j m
  have hdU4 := fun i j => vorticity_weakPartial_restrict b40 (hdU i j)
  have hdG4 := fun i j k => vorticity_weakPartial_restrict b42 (hdG2 i j k)
  have hdw4 := fun i j => vorticity_weakPartial_restrict b41 (hdw1 i j)
  have hdΩ4 := fun i j k => vorticity_weakPartial_restrict b44 (hdΩ2 i j k)
  have hdiv4 := vorticityDiv_restrict b40 hdiv
  have hheat4 := fun i => vorticityHeat_restrict b40 (hheat i)
  have hheatΩ4 := vorticityLevelTwo_heat hWo4 hWb4 hU4 hUb4 hG4 hΩ14
    (fun i j m => (hF'4 i j m).integrable (by norm_num)) hdU4 hdw4 hheat4
  have hK4 := vorticity_setIntegral_le_of_subset b40 (sq2 G hG) (fun z => by positivity) hK
  have hKw4 : ∀ i, ∫ y in vec3Ball x₀ (48 / 64) ×ˢ
      Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀,
      (vorticityCurl G i y ^ 2 +
        ∑ j : Fin 3, (-(U j y * vorticityCurl G i y - vorticityCurl G j y * U i y)) ^ 2) ≤
          (2 + 24 * M ^ 2) * K₀ := by
    intro i
    refine (integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
      ((sq2 G hG4).const_mul (2 + 24 * M ^ 2)) ?_).trans ?_
    · filter_upwards [hUb4] with z hz using vorticityFluxOf_sq_le hz i
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hK4 (by positivity)
  have hK14 : ∀ i m, ∫ y in vec3Ball x₀ (48 / 64) ×ˢ
      Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀,
      (Ω1 i m y ^ 2 + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) ≤
        (1 + 24 * M ^ 2) * K₁ + 48 * K₄ := by
    intro i m
    refine vorticity_integral_le_combo (by positivity) (by norm_num)
      (fun z => by positivity) (sq2 Ω1 hΩ14) hS4i ?_
      (vorticity_setIntegral_le_of_subset b41 (sq2 Ω1 hΩ1) (fun z => by positivity) hbΩ1)
      (vorticity_setIntegral_le_of_subset b43 hS3i (fun z => by positivity) hS3)
    filter_upwards [hUb4] with z hz
    have h1 : Ω1 i m z ^ 2 ≤ ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2 :=
      vorticity_sq_le_sum_two (fun a b => Ω1 a b z) i m
    have h2 : ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤
        3 * (16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) ^ 2 +
          8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) := by
      refine (Finset.sum_le_sum fun j _ => vorticityFluxDeriv_sq_le hz i j m).trans
        (le_of_eq ?_)
      rw [Fin.sum_univ_three]
      ring
    have e : (∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) +
        3 * (16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) ^ 2 +
          8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) =
        (1 + 24 * M ^ 2) * (∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) +
          48 * (∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) ^ 2 := by ring
    linarith only [h1, h2, e]
  obtain ⟨hSPi, hSPb⟩ := hSP x₀ (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ U G Ω1
    (fun i j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) D2 Ω2
    (vorticityFluxDeriv U G Ω1) (by linarith only []) (by linarith only []) hU4 hUb4 hG4 hD24
    hΩ14 hΩ24 hFm4 hF'4 hdU4 hdG4 hdw4 hdΩ4 hdiv4 hheat4 hheatΩ4 hKw4 hK14 hK4
    (vorticity_setIntegral_le_of_subset b42 (sq3 D2 hD2) (fun z => by positivity) hbD2)
    (vorticity_setIntegral_le_of_subset b44 (sq3 Ω2 hΩ2) (fun z => by positivity) hbΩ2)
  -- the final box
  have b54 : (vec3Ball x₀ (43 / 64) ×ˢ
      Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀ : Set (Vec3 × ℝ)) ⊆
        vec3Ball x₀ (48 / 64) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16) t₀ :=
    box (by norm_num) (by linarith only [])
  have hWo5 := vorticityBox_isOpen x₀ (43 / 64)
    (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀
  have hWb5 := vorticityBox_isBounded x₀ (43 / 64) _
    (Metric.isBounded_Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀)
  have hfin5 : IsFiniteMeasure (volume.restrict (vec3Ball x₀ (43 / 64) ×ˢ
      Ioo (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀)) :=
    isFiniteMeasure_restrict.2 hWb5.measure_lt_top.ne
  have hU5 := fun i => rM b54 (hU4 i)
  have hUb5 := ae_restrict_of_ae_restrict_of_subset b54 hUb4
  have hG5 := fun i j => rM b54 (hG4 i j)
  have hD25 := fun i j k => rM b54 (hD24 i j k)
  have hΩ15 := fun i j => rM b54 (hΩ14 i j)
  have hΩ25 := fun i j k => rM b54 (hΩ24 i j k)
  have hF'5 := fun i j m => rM b54 (hF'4 i j m)
  have hF''5 := fun i j m k => vorticityFluxDeriv2_memLp hU5 hUb5 hG5 hD25 hΩ15 hΩ25 hSPi i j m k
  have hdU5 := fun i j => vorticity_weakPartial_restrict b54 (hdU4 i j)
  have hdG5 := fun i j k => vorticity_weakPartial_restrict b54 (hdG4 i j k)
  have hdw5 := fun i j => vorticity_weakPartial_restrict b54 (hdw4 i j)
  have hdΩ5 := fun i j k => vorticity_weakPartial_restrict b54 (hdΩ4 i j k)
  have hheatΩ5 := fun i m => vorticityHeat_restrict b54 (hheatΩ4 i m)
  have hheatΩ25 := fun i m k => vorticityHeat_weak_deriv
    (fun j => (hF'5 i j m).integrable (by norm_num))
    (fun j => (hF''5 i j m k).integrable (by norm_num)) (hheatΩ5 i m) (hdΩ5 i m k)
    (fun j => vorticityFluxDeriv_weakDeriv hWo5 hWb5 hU5 hG5 hD25 hΩ15 hΩ25 hdU5 hdG5 hdw5 hdΩ5
      i j m k)
  refine ⟨Ω1, D2, Ω2, hD25, hΩ15, hΩ25, hF'5, hF''5, hdG5, hdw5, hdΩ5, hheatΩ5, hheatΩ25,
    fun i => ?_, fun i m => ?_, fun i m k => ?_⟩
  · exact vorticity_setIntegral_le_of_subset b54 (((vorticityCurl_memLp hG4 i).integrable_sq).add
      (integrable_finsetSum _ fun j _ => (hFm4 i j).integrable_sq))
      (fun z => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (hKw4 i)
  · exact vorticity_setIntegral_le_of_subset b54 (((hΩ14 i m).integrable_sq).add
      (integrable_finsetSum _ fun j _ => (hF'4 i j m).integrable_sq))
      (fun z => add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (hK14 i m)
  · refine vorticity_integral_le_combo (by positivity) (by norm_num)
      (fun z => by positivity) (sq3 Ω2 hΩ25) hSPi ?_
      (vorticity_setIntegral_le_of_subset (b54.trans b44) (sq3 Ω2 hΩ2) (fun z => by positivity)
        hbΩ2) hSPb
    filter_upwards [hUb5] with z hz
    have h1 : Ω2 i m k z ^ 2 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2 :=
      vorticity_sq_le_sum_three (fun a b c => Ω2 a b c z) i m k
    have h2 : ∑ j : Fin 3, vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k z ^ 2 ≤
        3 * (64 * ((∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) *
          ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, D2 a b c z ^ 2) +
            ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2)) +
          16 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2) := by
      refine (Finset.sum_le_sum fun j _ => vorticityFluxDeriv2_sq_le hz i j m k).trans
        (le_of_eq ?_)
      rw [Fin.sum_univ_three]
      ring
    have e : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2) +
        3 * (64 * ((∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) *
          ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, D2 a b c z ^ 2) +
            ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2)) +
          16 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2) =
        (1 + 48 * M ^ 2) * (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, Ω2 a b c z ^ 2) +
          192 * ((∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) *
            ((∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, D2 a b c z ^ 2) +
              ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2)) := by ring
    linarith only [h1, h2, e]

end ESS
