/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakAlgebra

/-!
# The first level of the vorticity bootstrap

From the starting data on the unit box, the weak local heat gain gives square-integrable first
spatial derivatives of the vorticity, and the weak div–curl recovery gives square-integrable
second spatial derivatives of the velocity, with bounds by the velocity bound and the gradient
energy (the initial energy level and the first velocity level of `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The vorticity components of a square-integrable gradient are square integrable. -/
theorem vorticityCurl_memLp {μ : Measure (Vec3 × ℝ)} {G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hG : ∀ i j, MemLp (G i j) 2 μ) (l : Fin 3) : MemLp (vorticityCurl G l) 2 μ := by
  have h0 : vorticityCurl G 0 = fun z => G 2 1 z - G 1 2 z := rfl
  have h1 : vorticityCurl G 1 = fun z => G 0 2 z - G 2 0 z := rfl
  have h2 : vorticityCurl G 2 = fun z => G 1 0 z - G 0 1 z := rfl
  fin_cases l
  · rw [show ((⟨0, by norm_num⟩ : Fin 3)) = 0 from rfl, h0]; exact (hG 2 1).sub (hG 1 2)
  · rw [show ((⟨1, by norm_num⟩ : Fin 3)) = 1 from rfl, h1]; exact (hG 0 2).sub (hG 2 0)
  · rw [show ((⟨2, by norm_num⟩ : Fin 3)) = 2 from rfl, h2]; exact (hG 1 0).sub (hG 0 1)

/-- The vorticity flux of a bounded velocity and a square-integrable gradient. -/
theorem vorticityFluxOf_memLp {μ : Measure (Vec3 × ℝ)} {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {M : ℝ} (hU : ∀ i, AEStronglyMeasurable (U i) μ)
    (hG : ∀ i j, MemLp (G i j) 2 μ) (hUb : ∀ᵐ z ∂μ, ∀ i, |U i z| ≤ M) (i j : Fin 3) :
    MemLp (fun z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) 2 μ := by
  have hw := vorticityCurl_memLp hG
  have hdom : MemLp (fun z => M * |vorticityCurl G i z| + M * |vorticityCurl G j z|) 2 μ :=
    ((hw i).abs.const_mul M).add ((hw j).abs.const_mul M)
  refine hdom.of_le (((hU j).mul (hw i).aestronglyMeasurable).sub
    ((hw j).aestronglyMeasurable.mul (hU i))).neg ?_
  filter_upwards [hUb] with z hz
  have hM : 0 ≤ M := (abs_nonneg _).trans (hz 0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  have ha := hz j
  have hb := hz i
  calc
    |U j z * vorticityCurl G i z - vorticityCurl G j z * U i z| ≤
        |U j z| * |vorticityCurl G i z| + |vorticityCurl G j z| * |U i z| := by
      rw [← abs_mul, ← abs_mul]
      exact abs_sub _ _
    _ ≤ M * |vorticityCurl G i z| + |vorticityCurl G j z| * M := by
      gcongr
    _ = M * |vorticityCurl G i z| + M * |vorticityCurl G j z| := by ring
    _ ≤ abs (M * |vorticityCurl G i z| + M * |vorticityCurl G j z|) := le_abs_self _

/-- The pointwise bound of the vorticity and its flux by the gradient. -/
theorem vorticityFluxOf_sq_le {U : Fin 3 → Vec3 × ℝ → ℝ} {G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {M : ℝ} {z : Vec3 × ℝ} (hz : ∀ i, |U i z| ≤ M) (i : Fin 3) :
    vorticityCurl G i z ^ 2 +
        ∑ j : Fin 3, (-(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) ^ 2 ≤
      (2 + 24 * M ^ 2) * ∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2 := by
  set S := ∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2 with hS
  have hw : ∀ l, vorticityCurl G l z ^ 2 ≤ 2 * S := fun l => vorticityCurl_sq_le G z l
  have hsq : ∀ l, U l z ^ 2 ≤ M ^ 2 := fun l => by
    have := hz l
    have h0 : 0 ≤ |U l z| := abs_nonneg _
    nlinarith only [this, h0, sq_abs (U l z)]
  have hterm : ∀ j, (-(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) ^ 2 ≤
      2 * M ^ 2 * (vorticityCurl G i z ^ 2 + vorticityCurl G j z ^ 2) := by
    intro j
    have h1 := hsq j
    have h2 := hsq i
    nlinarith only [h1, h2, sq_nonneg (U j z * vorticityCurl G i z + vorticityCurl G j z * U i z),
      sq_nonneg (vorticityCurl G i z), sq_nonneg (vorticityCurl G j z),
      mul_le_mul_of_nonneg_right h1 (sq_nonneg (vorticityCurl G i z)),
      mul_le_mul_of_nonneg_right h2 (sq_nonneg (vorticityCurl G j z))]
  have hS0 : 0 ≤ S := by positivity
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  calc
    vorticityCurl G i z ^ 2 +
        ∑ j : Fin 3, (-(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z)) ^ 2 ≤
        2 * S + ∑ j : Fin 3, 2 * M ^ 2 * (vorticityCurl G i z ^ 2 + vorticityCurl G j z ^ 2) :=
      add_le_add (hw i) (Finset.sum_le_sum fun j _ => hterm j)
    _ ≤ 2 * S + ∑ _j : Fin 3, 2 * M ^ 2 * (2 * S + 2 * S) := by
      gcongr with j
      · exact hw i
      · exact hw j
    _ = (2 + 24 * M ^ 2) * S := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The heat step of the first level: square-integrable first derivatives of the vorticity
(the initial energy level of `thm:vorticity-regularity`). -/
theorem vorticityLevelOne_heat (M K₀ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) →
    (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀)), ∀ i, |U i z| ≤ M) →
    ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤ K₀ →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀,
          vorticityCurl G i z * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀,
          ∑ j : Fin 3, -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z) *
            spatialPartial ψ j z) →
    ∃ Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j, MemLp (Ω1 i j) 2
        (volume.restrict (vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀))) ∧
      (∀ i j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀ →
        ∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀,
            vorticityCurl G i y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀, Ω1 i j y * ψ y) ∧
      ∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀,
          ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j y ^ 2 ≤ K := by
  obtain ⟨C, hC, heng⟩ := vorticityHeatEngine (r := 15 / 16) (R := 1) (κ := 1 / 16)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨3 * (C * ((2 + 24 * M ^ 2) * |K₀|)), by positivity, ?_⟩
  intro x₀ t₀ U G hU hG hUb hGb hheat
  have hGb' : ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤
      |K₀| := hGb.trans (le_abs_self K₀)
  clear hGb
  set W₀ := (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) with hW₀def
  have hFmem : ∀ i j, MemLp (fun z => -(U j z * vorticityCurl G i z -
      vorticityCurl G j z * U i z)) 2 (volume.restrict W₀) := fun i j =>
    vorticityFluxOf_memLp (fun i => (hU i).aestronglyMeasurable) hG hUb i j
  have hstep : ∀ i : Fin 3, ∃ g : Fin 3 → Vec3 × ℝ → ℝ,
      (∀ j, MemLp (g j) 2
        (volume.restrict (vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀))) ∧
      (∀ j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀ →
        ∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀,
            vorticityCurl G i y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀, g j y * ψ y) ∧
      ∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀, ∑ j : Fin 3, g j y ^ 2 ≤
        C * ∫ y in W₀, (vorticityCurl G i y ^ 2 + ∑ j : Fin 3,
          (-(U j y * vorticityCurl G i y - vorticityCurl G j y * U i y)) ^ 2) := fun i =>
    heng x₀ (t₀ - 1) t₀ (vorticityCurl G i)
      (fun j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z))
      (by linarith only) (by linarith only) (vorticityCurl_memLp hG i) (fun j => hFmem i j)
      (hheat i)
  choose Ω1 hΩmem hΩweak hΩbd using hstep
  refine ⟨Ω1, hΩmem, hΩweak, ?_⟩
  have hdata : ∀ i : Fin 3, ∫ y in W₀, (vorticityCurl G i y ^ 2 + ∑ j : Fin 3,
      (-(U j y * vorticityCurl G i y - vorticityCurl G j y * U i y)) ^ 2) ≤
      (2 + 24 * M ^ 2) * |K₀| := by
    intro i
    have hint1 : Integrable (fun y => vorticityCurl G i y ^ 2 + ∑ j : Fin 3,
        (-(U j y * vorticityCurl G i y - vorticityCurl G j y * U i y)) ^ 2)
        (volume.restrict W₀) := by
      refine ((memLp_two_iff_integrable_sq (vorticityCurl_memLp hG i).aestronglyMeasurable).1
        (vorticityCurl_memLp hG i)).add (integrable_finsetSum _ fun j _ => ?_)
      exact (memLp_two_iff_integrable_sq (hFmem i j).aestronglyMeasurable).1 (hFmem i j)
    have hint2 : Integrable (fun y => (2 + 24 * M ^ 2) *
        ∑ a : Fin 3, ∑ b : Fin 3, G a b y ^ 2) (volume.restrict W₀) :=
      (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
        (memLp_two_iff_integrable_sq (hG a b).aestronglyMeasurable).1 (hG a b)).const_mul _
    calc
      _ ≤ ∫ y in W₀, (2 + 24 * M ^ 2) * ∑ a : Fin 3, ∑ b : Fin 3, G a b y ^ 2 := by
        apply integral_mono_ae hint1 hint2
        filter_upwards [hUb] with z hz
        exact vorticityFluxOf_sq_le hz i
      _ = (2 + 24 * M ^ 2) * ∫ y in W₀, ∑ a : Fin 3, ∑ b : Fin 3, G a b y ^ 2 :=
        integral_const_mul _ _
      _ ≤ (2 + 24 * M ^ 2) * |K₀| := by gcongr
  have hint : ∀ i, Integrable (fun y => ∑ j : Fin 3, Ω1 i j y ^ 2)
      (volume.restrict (vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀)) := fun i =>
    integrable_finsetSum _ fun j _ =>
      (memLp_two_iff_integrable_sq (hΩmem i j).aestronglyMeasurable).1 (hΩmem i j)
  rw [integral_finsetSum _ fun i _ => hint i]
  calc
    _ ≤ ∑ _i : Fin 3, C * ((2 + 24 * M ^ 2) * |K₀|) :=
      Finset.sum_le_sum fun i _ => (hΩbd i).trans (mul_le_mul_of_nonneg_left (hdata i) hC)
    _ = 3 * (C * ((2 + 24 * M ^ 2) * |K₀|)) := by simp

/-- The antisymmetric matrix of square-integrable fields is square integrable. -/
theorem vorticityAntisym_memLp {μ : Measure (Vec3 × ℝ)} {v : Fin 3 → Vec3 × ℝ → ℝ}
    (hv : ∀ l, MemLp (v l) 2 μ) (i k : Fin 3) :
    MemLp (fun z => vorticityAntisym (fun l => v l z) i k) 2 μ := by
  have h : (fun z => vorticityAntisym (fun l => v l z) i k) =
      fun z => ∑ l : Fin 3, vorticityEps i k l * v l z := by
    funext z
    exact vorticityAntisym_eq_sum _ i k
  rw [h]
  exact memLp_finsetSum _ fun l _ => (hv l).const_mul _

/-- The div–curl step of the first level: square-integrable second derivatives of the velocity
(the first velocity level of `thm:vorticity-regularity`). -/
theorem vorticityLevelOne_divCurl (K₀ K₁ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ),
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) →
    ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2 ≤ K₀ →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ y in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, U i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, G i j y * ψ y) →
    (∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ y in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, U i y * spatialPartial ψ i y = 0) →
    (∀ i j, MemLp (Ω1 i j) 2
      (volume.restrict (vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀))) →
    (∀ i j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀ →
      ∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀,
          vorticityCurl G i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀, Ω1 i j y * ψ y) →
    ∫ y in vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀,
        ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j y ^ 2 ≤ K₁ →
    ∃ D2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j k, MemLp (D2 i j k) 2
        (volume.restrict (vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀))) ∧
      (∀ i j k, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀ →
        ∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀,
            G i j y * spatialPartial ψ k y =
          -∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀,
            D2 i j k y * ψ y) ∧
      ∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀,
          ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, D2 i j k y ^ 2 ≤ K := by
  obtain ⟨C, hC, deng⟩ := vorticityDivCurlEngine (r := 14 / 16) (R := 15 / 16) (κ := 1 / 16)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C * (2 * |K₁| + |K₀|), by positivity, ?_⟩
  intro x₀ t₀ U G Ω1 hU hG hGb hdU hdiv hΩ hdΩ hΩb
  set W₀ := (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) with hW₀def
  set W₁ := (vec3Ball x₀ (15 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16) t₀ : Set (Vec3 × ℝ)) with hW₁def
  have hW₁W₀ : W₁ ⊆ W₀ := by
    rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
    refine ⟨show vec3EuclideanNorm (x - x₀) < 1 from
      lt_trans (show vec3EuclideanNorm (x - x₀) < 15 / 16 from hx) (by norm_num), ?_, ht2⟩
    change t₀ - 1 < t
    change t₀ - 1 + 1 / 16 < t at ht1
    linarith only [ht1]
  have hU₁ : ∀ i, MemLp (U i) 2 (volume.restrict W₁) := fun i =>
    (hU i).mono_measure (Measure.restrict_mono hW₁W₀ le_rfl)
  have hG₁ : ∀ i j, MemLp (G i j) 2 (volume.restrict W₁) := fun i j =>
    (hG i j).mono_measure (Measure.restrict_mono hW₁W₀ le_rfl)
  have hW₁b : Bornology.IsBounded W₁ :=
    vorticityBox_isBounded x₀ _ _ (Metric.isBounded_Ioo _ _)
  have hfin : IsFiniteMeasure (volume.restrict W₁) :=
    isFiniteMeasure_restrict.2 hW₁b.measure_lt_top.ne
  have hint : ∀ f : Vec3 × ℝ → ℝ, MemLp f 2 (volume.restrict W₁) → IntegrableOn f W₁ :=
    fun f hf => hf.integrable (by norm_num)
  have hdU₁ := fun i j => vorticity_weakPartial_restrict hW₁W₀ (hdU i j)
  have hdiv₁ := vorticityDiv_restrict hW₁W₀ hdiv
  have hanti₁ := vorticityAnti_base (fun i j => hint _ (hG₁ i j)) (fun i => hint _ (hU₁ i)) hdU₁
  have hstep : ∀ m : Fin 3, ∃ g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j, MemLp (g i j) 2
        (volume.restrict (vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀))) ∧
      (∀ i j, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀ →
        ∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀,
            G i m y * spatialPartial ψ j y =
          -∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀, g i j y * ψ y) ∧
      ∫ y in vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀,
          ∑ i : Fin 3, ∑ j : Fin 3, g i j y ^ 2 ≤
        C * ∫ y in W₁, (∑ i : Fin 3, ∑ k : Fin 3,
          vorticityAntisym (fun l => Ω1 l m y) i k ^ 2 + ∑ i : Fin 3, G i m y ^ 2) := by
    intro m
    exact deng x₀ (t₀ - 1 + 1 / 16) t₀ (fun i => G i m)
      (fun i k y => vorticityAntisym (fun l => Ω1 l m y) i k)
      (fun i => hG₁ i m) (fun i k => vorticityAntisym_memLp (fun l => hΩ l m) i k)
      (vorticityDiv_deriv (fun i => hint _ (hU₁ i)) (fun i => hint _ (hG₁ i m)) hdiv₁
        (fun i => hdU₁ i m))
      (vorticityAnti_deriv (fun i => hint _ (hU₁ i))
        (fun l => hint _ (vorticityCurl_memLp hG₁ l)) (fun l => hint _ (hΩ l m)) hanti₁
        (fun i => hdU₁ i m) (fun l => hdΩ l m) (fun i => hint _ (hG₁ i m)))
  choose g hgmem hgweak hgbd using hstep
  refine ⟨fun i j k => g j i k, fun i j k => hgmem j i k, fun i j k => hgweak j i k, ?_⟩
  set W₂ := (vec3Ball x₀ (14 / 16) ×ˢ Ioo (t₀ - 1 + 1 / 16 + 1 / 16) t₀ : Set (Vec3 × ℝ))
    with hW₂def
  have hsq : ∀ (μ : Measure (Vec3 × ℝ)) (f : Vec3 × ℝ → ℝ), MemLp f 2 μ →
      Integrable (fun y => f y ^ 2) μ := fun μ f hf =>
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hgi : ∀ m, Integrable (fun y => ∑ i : Fin 3, ∑ k : Fin 3, g m i k y ^ 2)
      (volume.restrict W₂) := fun m =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hsq _ _ (hgmem m i k)
  have hRi : ∀ m, Integrable (fun y => ∑ i : Fin 3, ∑ k : Fin 3,
      vorticityAntisym (fun l => Ω1 l m y) i k ^ 2 + ∑ i : Fin 3, G i m y ^ 2)
      (volume.restrict W₁) := fun m =>
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      hsq _ _ (vorticityAntisym_memLp (fun l => hΩ l m) i k)).add
      (integrable_finsetSum _ fun i _ => hsq _ _ (hG₁ i m))
  have hΩi : Integrable (fun y => ∑ l : Fin 3, ∑ m : Fin 3, Ω1 l m y ^ 2)
      (volume.restrict W₁) :=
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hsq _ _ (hΩ l m)
  have hGi₀ : Integrable (fun y => ∑ i : Fin 3, ∑ m : Fin 3, G i m y ^ 2)
      (volume.restrict W₀) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hsq _ _ (hG i m)
  have hGW₁ : ∫ y in W₁, ∑ i : Fin 3, ∑ m : Fin 3, G i m y ^ 2 ≤ |K₀| :=
    (setIntegral_mono_set hGi₀ (Eventually.of_forall fun y => by positivity)
      (Eventually.of_forall hW₁W₀)).trans (hGb.trans (le_abs_self _))
  calc
    ∫ y in W₂, ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, g j i k y ^ 2 =
        ∫ y in W₂, ∑ m : Fin 3, ∑ i : Fin 3, ∑ k : Fin 3, g m i k y ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun y => Finset.sum_comm)
    _ = ∑ m : Fin 3, ∫ y in W₂, ∑ i : Fin 3, ∑ k : Fin 3, g m i k y ^ 2 :=
      integral_finsetSum _ fun m _ => hgi m
    _ ≤ ∑ m : Fin 3, C * ∫ y in W₁, (∑ i : Fin 3, ∑ k : Fin 3,
          vorticityAntisym (fun l => Ω1 l m y) i k ^ 2 + ∑ i : Fin 3, G i m y ^ 2) :=
      Finset.sum_le_sum fun m _ => hgbd m
    _ = C * ∫ y in W₁, ∑ m : Fin 3, (∑ i : Fin 3, ∑ k : Fin 3,
          vorticityAntisym (fun l => Ω1 l m y) i k ^ 2 + ∑ i : Fin 3, G i m y ^ 2) := by
      rw [← Finset.mul_sum, integral_finsetSum _ fun m _ => hRi m]
    _ ≤ C * (2 * (∫ y in W₁, ∑ l : Fin 3, ∑ m : Fin 3, Ω1 l m y ^ 2) +
          ∫ y in W₁, ∑ i : Fin 3, ∑ m : Fin 3, G i m y ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hGi₁ : Integrable (fun y => ∑ i : Fin 3, ∑ m : Fin 3, G i m y ^ 2)
          (volume.restrict W₁) :=
        integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hsq _ _ (hG₁ i m)
      rw [← integral_const_mul, ← integral_add (hΩi.const_mul 2) hGi₁]
      apply integral_mono (integrable_finsetSum _ fun m _ => hRi m)
        ((hΩi.const_mul 2).add hGi₁)
      intro y
      simp only
      rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun m i => G i m y ^ 2)]
      refine add_le_add ?_ le_rfl
      change _ ≤ 2 * ∑ l : Fin 3, ∑ m : Fin 3, Ω1 l m y ^ 2
      rw [Finset.sum_comm (f := fun l m => Ω1 l m y ^ 2), Finset.mul_sum]
      exact Finset.sum_le_sum fun m _ => vorticityAntisym_sq_sum_le (fun l => Ω1 l m y)
    _ ≤ C * (2 * |K₁| + |K₀|) := by
      gcongr
      exact hΩb.trans (le_abs_self _)

end ESS
