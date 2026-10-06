/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularityCore

/-!
# The conclusions of the vorticity regularity theorem on a product box

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

/-- `thm:vorticity-regularity` on the product box, for fields on `Vec3 × ℝ`. -/
theorem vorticityRegularity_box (M K₀ : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
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
          C * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|)) := by
  obtain ⟨Kw, K1, K2, hst⟩ := vorticityStages M K₀ hM
  obtain ⟨K, hK, hgrad⟩ := vorticityFinal_gradBound M Kw K1 K2 hM
  obtain ⟨Cc, hCc, hcont⟩ := vorticity_continuousRep Kw K1 K2
  refine ⟨Cc + 6 * (K + M), by positivity, ?_⟩
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
  have hrep := fun i => hcont x₀ (t₀ - 1 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 16 + 1 / 32) t₀
    (vorticityCurl G i) (fun m => Ω1 i m)
    (fun j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z))
    (fun m k => Ω2 i m k) (fun m j => vorticityFluxDeriv U G Ω1 i j m)
    (fun m k j => vorticityFluxDeriv2 U G Ω1 D2 Ω2 i j m k) (by linarith only [])
    (by linarith only []) (hw5 i) (fun m => hΩ1 i m) (fun m k => hΩ2 i m k) (fun j => hFm5 i j)
    (fun m j => hF' i j m) (fun m k j => hF'' i j m k) (hdw i) (hdΩ i) (hheat5 i) (hhΩ1 i)
    (hhΩ2 i) (hKw i) (hK1 i) (hK2 i)
  choose ω hωc hωb hωae using hrep
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
  refine ⟨ω, Ω1, Ω2, fun i z => ∑ j : Fin 3, Ω2 i j j z +
      ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j j z,
    fun i => (hωc i).mono hKK, fun i z hz => (hωb i z (hKK hz)).trans
      (le_add_of_nonneg_right (by positivity)), hωS,
    fun i => (rM bS5 (hw5 i)).ae_eq (hωS i).symm, fun i j => rM bS5 (hΩ1 i j),
    fun i j k => rM bS5 (hΩ2 i j k), fun i => ?_, fun i j => ?_,
    fun i j k => vorticity_weakPartial_restrict bS5 (hdΩ i j k), fun i => ?_, ?_⟩
  · exact (memLp_finsetSum _ fun j _ => rM bS5 (hΩ2 i j j)).add
      (memLp_finsetSum _ fun j _ => rM bS5 (hF' i j j))
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

end ESS
