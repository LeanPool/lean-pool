/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityFluxDeriv
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityLevelOne

/-!
# The second level of the vorticity bootstrap

The first derivative of the vorticity flux is square integrable once the velocity gradient is in
`L⁴`; differentiating the weak vorticity equation and applying the weak local heat gain gives
square-integrable second derivatives of the vorticity (the second level of
`thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The first derivative of the vorticity flux, `∂ₘ(-(uⱼ ωᵢ - ωⱼ uᵢ))`. -/
@[expose] def vorticityFluxDeriv (U : Fin 3 → Vec3 × ℝ → ℝ) (G : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ) (i j m : Fin 3) (z : Vec3 × ℝ) : ℝ :=
  -((G j m z * vorticityCurl G i z + U j z * Ω1 i m z) -
    (Ω1 j m z * U i z + vorticityCurl G j z * G i m z))

/-- The weak derivative of the vorticity flux. -/
theorem vorticityFlux_weakDeriv {W : Set (Vec3 × ℝ)} (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict W)) (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict W))
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 (volume.restrict W))
    (hdU : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, U i y * spatialPartial ψ j y = -∫ y in W, G i j y * ψ y)
    (hdw : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, vorticityCurl G i y * spatialPartial ψ j y = -∫ y in W, Ω1 i j y * ψ y)
    (i j m : Fin 3) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ y in W, -(U j y * vorticityCurl G i y - vorticityCurl G j y * U i y) *
          spatialPartial ψ m y =
        -∫ y in W, vorticityFluxDeriv U G Ω1 i j m y * ψ y := by
  have hw := vorticityCurl_memLp hG
  exact vorticity_weakPartial_neg (vorticity_weakPartial_prodDiff hWo hWb (hU j) (hw i) (hw j)
    (hU i) (hG j m) (hΩ1 i m) (hΩ1 j m) (hG i m) (hdU j m) (hdw i m) (hdw j m) (hdU i m))

/-- The pointwise bound of the flux derivative by the fourth power of the gradient and the
square of the vorticity derivative. -/
theorem vorticityFluxDeriv_sq_le {U : Fin 3 → Vec3 × ℝ → ℝ} {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {M : ℝ} {z : Vec3 × ℝ} (hz : ∀ i, |U i z| ≤ M) (i j m : Fin 3) :
    vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤
      16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) ^ 2 +
        8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2 := by
  set S := ∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2 with hS
  set T := ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2 with hT
  have hGe : ∀ a b, G a b z ^ 2 ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => G a b z ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, G a b z ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a))
  have hΩe : ∀ a b, Ω1 a b z ^ 2 ≤ T := fun a b =>
    (Finset.single_le_sum (f := fun b => Ω1 a b z ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, Ω1 a b z ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a))
  have hw : ∀ l, vorticityCurl G l z ^ 2 ≤ 2 * S := fun l => vorticityCurl_sq_le G z l
  have hU2 : ∀ l, U l z ^ 2 ≤ M ^ 2 := fun l => by
    have := hz l
    have h0 : 0 ≤ |U l z| := abs_nonneg _
    nlinarith only [this, h0, sq_abs (U l z)]
  set A := G j m z * vorticityCurl G i z
  set B := U j z * Ω1 i m z
  set C := Ω1 j m z * U i z
  set D := vorticityCurl G j z * G i m z
  have hA : A ^ 2 ≤ 2 * S ^ 2 := by
    have h := mul_le_mul (hGe j m) (hw i) (sq_nonneg _) (by positivity)
    calc A ^ 2 = G j m z ^ 2 * vorticityCurl G i z ^ 2 := by ring
      _ ≤ S * (2 * S) := h
      _ = 2 * S ^ 2 := by ring
  have hB : B ^ 2 ≤ M ^ 2 * T := by
    have h := mul_le_mul (hU2 j) (hΩe i m) (sq_nonneg _) (sq_nonneg _)
    calc B ^ 2 = U j z ^ 2 * Ω1 i m z ^ 2 := by ring
      _ ≤ M ^ 2 * T := h
  have hC : C ^ 2 ≤ M ^ 2 * T := by
    have h := mul_le_mul (hU2 i) (hΩe j m) (sq_nonneg _) (sq_nonneg _)
    calc C ^ 2 = U i z ^ 2 * Ω1 j m z ^ 2 := by ring
      _ ≤ M ^ 2 * T := h
  have hD : D ^ 2 ≤ 2 * S ^ 2 := by
    have h := mul_le_mul (hw j) (hGe i m) (sq_nonneg _) (by positivity)
    calc D ^ 2 = vorticityCurl G j z ^ 2 * G i m z ^ 2 := by ring
      _ ≤ 2 * S * S := h
      _ = 2 * S ^ 2 := by ring
  have hsum : vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
    have e : vorticityFluxDeriv U G Ω1 i j m z = -((A + B) - (C + D)) := rfl
    rw [e]
    nlinarith only [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A + D), sq_nonneg (B + C),
      sq_nonneg (B + D), sq_nonneg (C - D)]
  nlinarith only [hsum, hA, hB, hC, hD]

/-- The weak heat equation for the first derivatives of the vorticity, with the differentiated
flux as source. -/
theorem vorticityLevelTwo_heat {W : Set (Vec3 × ℝ)} (hWo : IsOpen W)
    (hWb : Bornology.IsBounded W) {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {M : ℝ}
    (hU : ∀ i, MemLp (U i) 2 (volume.restrict W))
    (hUb : ∀ᵐ z ∂(volume.restrict W), ∀ i, |U i z| ≤ M)
    (hG : ∀ i j, MemLp (G i j) 2 (volume.restrict W))
    (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 (volume.restrict W))
    (hF' : ∀ i j m, IntegrableOn (vorticityFluxDeriv U G Ω1 i j m) W)
    (hdU : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, U i y * spatialPartial ψ j y = -∫ y in W, G i j y * ψ y)
    (hdw : ∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, vorticityCurl G i y * spatialPartial ψ j y = -∫ y in W, Ω1 i j y * ψ y)
    (hheat : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ z in W, vorticityCurl G i z *
          (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in W, ∑ j : Fin 3, -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z) *
            spatialPartial ψ j z)
    (i m : Fin 3) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ W →
      ∫ z in W, Ω1 i m z * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in W, ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z * spatialPartial ψ j z := by
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hFi : ∀ j, IntegrableOn (fun z => -(U j z * vorticityCurl G i z -
      vorticityCurl G j z * U i z)) W := fun j =>
    (vorticityFluxOf_memLp (fun i => (hU i).aestronglyMeasurable) hG hUb i j).integrable
      (by norm_num)
  exact vorticityHeat_weak_deriv (w := vorticityCurl G i) (w' := Ω1 i m)
    (F := fun j z => -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z))
    (F' := fun j => vorticityFluxDeriv U G Ω1 i j m) hFi (fun j => hF' i j m) (hheat i)
    (hdw i m) (fun j => vorticityFlux_weakDeriv hWo hWb hU hG hΩ1 hdU hdw i j m)

/-- Square integrability of the flux derivative. -/
theorem vorticityFluxDeriv_memLp {μ : Measure (Vec3 × ℝ)} {U : Fin 3 → Vec3 × ℝ → ℝ}
    {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {M : ℝ}
    (hU : ∀ i, MemLp (U i) 2 μ) (hUb : ∀ᵐ z ∂μ, ∀ i, |U i z| ≤ M)
    (hG : ∀ i j, MemLp (G i j) 2 μ) (hS : Integrable (fun z => (∑ a : Fin 3, ∑ b : Fin 3,
      G a b z ^ 2) ^ 2) μ) (hΩ1 : ∀ i j, MemLp (Ω1 i j) 2 μ) (i j m : Fin 3) :
    MemLp (vorticityFluxDeriv U G Ω1 i j m) 2 μ := by
  have hw := vorticityCurl_memLp hG
  have hmeas : AEStronglyMeasurable (vorticityFluxDeriv U G Ω1 i j m) μ := by
    unfold vorticityFluxDeriv
    exact ((((hG j m).aestronglyMeasurable.mul (hw i).aestronglyMeasurable).add
      ((hU j).aestronglyMeasurable.mul (hΩ1 i m).aestronglyMeasurable)).sub
      (((hΩ1 j m).aestronglyMeasurable.mul (hU i).aestronglyMeasurable).add
        ((hw j).aestronglyMeasurable.mul (hG i m).aestronglyMeasurable))).neg
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have hT : Integrable (fun z => ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) μ :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      (memLp_two_iff_integrable_sq (hΩ1 a b).aestronglyMeasurable).1 (hΩ1 a b)
  refine ((hS.const_mul 16).add (hT.const_mul (8 * M ^ 2))).mono' (hmeas.pow 2) ?_
  filter_upwards [hUb] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact vorticityFluxDeriv_sq_le hz i j m

/-- The second level of the bootstrap: square-integrable second derivatives of the vorticity
(the second vorticity level of `thm:vorticity-regularity`). -/
theorem vorticityLevelTwo (M K₁ K₄ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x₀ : Vec3) (a t₀ : ℝ) (U : Fin 3 → Vec3 × ℝ → ℝ)
      (G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ), a + 1 / 16 < t₀ → t₀ ≤ a + 1 →
    (∀ i, MemLp (U i) 2 (volume.restrict (vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀))) →
    (∀ᵐ z ∂(volume.restrict (vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀)), ∀ i, |U i z| ≤ M) →
    (∀ i j, MemLp (G i j) 2 (volume.restrict (vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀))) →
    Integrable (fun z => (∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2) ^ 2)
      (volume.restrict (vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀)) →
    ∫ z in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀, (∑ i : Fin 3, ∑ j : Fin 3, G i j z ^ 2) ^ 2 ≤ K₄ →
    (∀ i j, MemLp (Ω1 i j) 2 (volume.restrict (vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀))) →
    ∫ z in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀, ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2 ≤ K₁ →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀, U i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀, G i j y * ψ y) →
    (∀ i j : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀ →
      ∫ y in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀, vorticityCurl G i y * spatialPartial ψ j y =
        -∫ y in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀, Ω1 i j y * ψ y) →
    (∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀ →
      ∫ z in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀,
          vorticityCurl G i z * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀,
          ∑ j : Fin 3, -(U j z * vorticityCurl G i z - vorticityCurl G j z * U i z) *
            spatialPartial ψ j z) →
    ∃ Ω2 : Fin 3 → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ,
      (∀ i j k, MemLp (Ω2 i j k) 2
        (volume.restrict (vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀))) ∧
      (∀ i j k, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀ →
        ∫ y in vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀, Ω1 i j y * spatialPartial ψ k y =
          -∫ y in vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀, Ω2 i j k y * ψ y) ∧
      ∫ y in vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀,
          ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k y ^ 2 ≤ K := by
  obtain ⟨C, hC, heng⟩ := vorticityHeatEngine (r := 12 / 16) (R := 13 / 16) (κ := 1 / 16)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C * (|K₁| + 27 * (16 * |K₄| + 8 * M ^ 2 * |K₁|)), by positivity, ?_⟩
  intro x₀ a t₀ U G Ω1 hat hta hU hUb hG hS hSb hΩ1 hΩ1b hdU hdw hheat
  set W := (vec3Ball x₀ (13 / 16) ×ˢ Ioo a t₀ : Set (Vec3 × ℝ)) with hWdef
  have hWo : IsOpen W := vorticityBox_isOpen x₀ _ a t₀
  have hWb : Bornology.IsBounded W := vorticityBox_isBounded x₀ _ _ (Metric.isBounded_Ioo a t₀)
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.2 hWb.measure_lt_top.ne
  have hF'm : ∀ i j m, MemLp (vorticityFluxDeriv U G Ω1 i j m) 2 (volume.restrict W) :=
    vorticityFluxDeriv_memLp hU hUb hG hS hΩ1
  have hheat' := vorticityLevelTwo_heat hWo hWb hU hUb hG hΩ1
    (fun i j m => (hF'm i j m).integrable (by norm_num)) hdU hdw hheat
  have hstep : ∀ i m : Fin 3, ∃ g : Fin 3 → Vec3 × ℝ → ℝ,
      (∀ k, MemLp (g k) 2 (volume.restrict (vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀))) ∧
      (∀ k, ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀ →
        ∫ y in vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀, Ω1 i m y * spatialPartial ψ k y =
          -∫ y in vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀, g k y * ψ y) ∧
      ∫ y in vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀, ∑ k : Fin 3, g k y ^ 2 ≤
        C * ∫ y in W, (Ω1 i m y ^ 2 + ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) :=
    fun i m => heng x₀ a t₀ (Ω1 i m) (fun j => vorticityFluxDeriv U G Ω1 i j m) hat hta
      (hΩ1 i m) (fun j => hF'm i j m) (hheat' i m)
  choose Ω2 hΩ2m hΩ2w hΩ2b using hstep
  refine ⟨Ω2, hΩ2m, hΩ2w, ?_⟩
  set W' := (vec3Ball x₀ (12 / 16) ×ˢ Ioo (a + 1 / 16) t₀ : Set (Vec3 × ℝ)) with hW'def
  have hsq : ∀ (μ : Measure (Vec3 × ℝ)) (f : Vec3 × ℝ → ℝ), MemLp f 2 μ →
      Integrable (fun y => f y ^ 2) μ := fun μ f hf =>
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hT : Integrable (fun z => ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) (volume.restrict W) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hsq _ _ (hΩ1 a b)
  have hF'2 : ∀ i m, Integrable (fun z => ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2)
      (volume.restrict W) := fun i m =>
    integrable_finsetSum _ fun j _ => hsq _ _ (hF'm i j m)
  have hdata : ∀ i m, Integrable (fun y => Ω1 i m y ^ 2 +
      ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) (volume.restrict W) := fun i m =>
    (hsq _ _ (hΩ1 i m)).add (hF'2 i m)
  have hΩ2i : ∀ i m, Integrable (fun y => ∑ k : Fin 3, Ω2 i m k y ^ 2) (volume.restrict W') :=
    fun i m => integrable_finsetSum _ fun k _ => hsq _ _ (hΩ2m i m k)
  have hF'b : ∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, ∑ j : Fin 3,
      vorticityFluxDeriv U G Ω1 i j m y ^ 2 ≤ 27 * (16 * |K₄| + 8 * M ^ 2 * |K₁|) := by
    have hbd : Integrable (fun y => 27 * (16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b y ^ 2) ^ 2 +
        8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b y ^ 2)) (volume.restrict W) :=
      ((hS.const_mul 16).add (hT.const_mul _)).const_mul 27
    calc
      _ ≤ ∫ y in W, 27 * (16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b y ^ 2) ^ 2 +
          8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b y ^ 2) := by
        apply integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_finsetSum _
          fun m _ => hF'2 i m) hbd
        filter_upwards [hUb] with z hz
        calc
          ∑ i : Fin 3, ∑ m : Fin 3, ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤
              ∑ _i : Fin 3, ∑ _m : Fin 3, ∑ _j : Fin 3,
                (16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) ^ 2 +
                  8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => Finset.sum_le_sum
              fun j _ => vorticityFluxDeriv_sq_le hz i j m
          _ = _ := by simp; ring
      _ = 27 * (16 * ∫ y in W, (∑ a : Fin 3, ∑ b : Fin 3, G a b y ^ 2) ^ 2) +
          27 * (8 * M ^ 2 * ∫ y in W, ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b y ^ 2) := by
        rw [integral_const_mul, integral_add (hS.const_mul 16) (hT.const_mul _),
          integral_const_mul, integral_const_mul]
        ring
      _ ≤ 27 * (16 * |K₄|) + 27 * (8 * M ^ 2 * |K₁|) := by
        gcongr
        · exact hSb.trans (le_abs_self _)
        · exact hΩ1b.trans (le_abs_self _)
      _ = 27 * (16 * |K₄| + 8 * M ^ 2 * |K₁|) := by ring
  calc
    ∫ y in W', ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, Ω2 i j k y ^ 2 =
        ∑ i : Fin 3, ∑ m : Fin 3, ∫ y in W', ∑ k : Fin 3, Ω2 i m k y ^ 2 := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hΩ2i i m]
      exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun m _ => hΩ2i i m
    _ ≤ ∑ i : Fin 3, ∑ m : Fin 3, C * ∫ y in W, (Ω1 i m y ^ 2 +
          ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => hΩ2b i m
    _ = C * ((∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, Ω1 i m y ^ 2) +
          ∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, ∑ j : Fin 3,
            vorticityFluxDeriv U G Ω1 i j m y ^ 2) := by
      have hF3 : Integrable (fun y => ∑ i : Fin 3, ∑ m : Fin 3, ∑ j : Fin 3,
          vorticityFluxDeriv U G Ω1 i j m y ^ 2) (volume.restrict W) :=
        integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hF'2 i m
      have e1 : (∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, Ω1 i m y ^ 2) +
          (∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, ∑ j : Fin 3,
            vorticityFluxDeriv U G Ω1 i j m y ^ 2) =
          ∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, (Ω1 i m y ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) := by
        rw [← integral_add hT hF3]
        exact integral_congr_ae (Eventually.of_forall fun y => by
          simp only [Finset.sum_add_distrib])
      have e2 : ∫ y in W, ∑ i : Fin 3, ∑ m : Fin 3, (Ω1 i m y ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) =
          ∑ i : Fin 3, ∑ m : Fin 3, ∫ y in W, (Ω1 i m y ^ 2 +
            ∑ j : Fin 3, vorticityFluxDeriv U G Ω1 i j m y ^ 2) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun m _ => hdata i m]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun m _ => hdata i m
      rw [e1, e2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    _ ≤ C * (|K₁| + 27 * (16 * |K₄| + 8 * M ^ 2 * |K₁|)) := by
      gcongr
      exact hΩ1b.trans (le_abs_self _)

end ESS
