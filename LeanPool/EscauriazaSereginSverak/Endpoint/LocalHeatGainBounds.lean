/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainWord

/-!
# Norm bounds for the cutoff solution and its source

The squared `L²_t H^m_x` norm of the cutoff `ηz` and the squared
`L²_t H^{m-1}_x` norm of its source `ηG + (∂ₜη - Δη) z - 2 ∇η · ∇z` are bounded
by the squared norms of `z` and `G`, with a factor `L²` for a bound `L` on the
spatial derivatives of the cutoff (`lem:local-heat-gain`).
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Integrals over `ℝ³ × I` of fields vanishing outside `B × ℝ` are integrals
over `B × I`. -/
theorem integral_univ_prod_sq_eq {B K : Set Vec3} {I : Set ℝ} (hIm : MeasurableSet I)
    (hKB : K ⊆ B) {F : Vec3 × ℝ → ℝ} (hF : ∀ p : Vec3 × ℝ, p.1 ∉ K → F p = 0) :
    ∫ p in (univ : Set Vec3) ×ˢ I, F p ^ 2 = ∫ p in B ×ˢ I, F p ^ 2 :=
  setIntegral_univ_prod_eq (U := B) hIm fun p hp => by rw [hF p fun h => hp (hKB h)]; simp

/-- The norm bounds for the cutoff solution and its source. -/
theorem localHeatGain_normBounds (m : ℕ) (hm1 : 1 ≤ m) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ (B K : Set Vec3) (I : Set ℝ) (η : Vec3 × ℝ → ℝ) (L : ℝ)
      (Dz DG : List (Fin 3) → Vec3 × ℝ → ℝ),
      MeasurableSet B → MeasurableSet I → IsLocalHeatCutoff B K η →
      (∀ γ : List (Fin 3), γ.length ≤ m → ∀ p, |spaceTimeWord γ η p| ≤ L) →
      (∀ γ : List (Fin 3), γ.length ≤ m → ∀ p,
        |spaceTimeWord γ (localHeatGainZeta η) p| ≤ L) →
      (∀ (j : Fin 3) (γ : List (Fin 3)), γ.length ≤ m → ∀ p,
        |spaceTimeWord γ (fun q => spatialPartial η j q) p| ≤ L) →
      IsSpaceTimeFamily m (B ×ˢ I) Dz → IsSpaceTimeFamily (m - 1) (B ×ˢ I) DG →
      (∑ α ∈ sobolevWords m, ∫ p in (univ : Set Vec3) ×ˢ I, localHeatGainDw η Dz α p ^ 2 ≤
          Kc * L ^ 2 * ∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2) ∧
      (∑ α ∈ sobolevWords (m - 1),
          ∫ p in (univ : Set Vec3) ×ˢ I, localHeatGainDH η Dz DG α p ^ 2 ≤
        Kc * L ^ 2 * ((∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2) +
          ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, DG α p ^ 2)) := by
  obtain ⟨C₀, hC₀, hL₀⟩ := stLeibniz_normSq_le m
  obtain ⟨C₁, hC₁, hL₁⟩ := stLeibniz_normSq_le (m - 1)
  refine ⟨C₀ + 111 * C₁, by positivity, ?_⟩
  intro B K I η L Dz DG hBm hIm hη hLη hLζ hLg hDz hDG
  have hLm1 : ∀ {P : List (Fin 3) → Prop}, (∀ γ : List (Fin 3), γ.length ≤ m → P γ) →
      ∀ γ : List (Fin 3), γ.length ≤ m - 1 → P γ :=
    fun h γ hγ => h γ (hγ.trans (Nat.sub_le m 1))
  have hVm : MeasurableSet (B ×ˢ I) := hBm.prod hIm
  have hmeas (ζ : Vec3 × ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (γ : List (Fin 3)) :
      AEStronglyMeasurable (spaceTimeWord γ ζ) (volume.restrict (B ×ˢ I)) :=
    (contDiff_spaceTimeWord γ hζ).continuous.aestronglyMeasurable
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hLη [] (Nat.zero_le _) (0, 0))
  -- vanishing outside `K`
  have hvη (p : Vec3 × ℝ) (hp : p.1 ∉ K) (γ : List (Fin 3)) : spaceTimeWord γ η p = 0 :=
    spaceTimeWord_eq_zero_of_compl hη.compact γ hη.zero p.1 hp p.2
  have hvζ (p : Vec3 × ℝ) (hp : p.1 ∉ K) (γ : List (Fin 3)) :
      spaceTimeWord γ (localHeatGainZeta η) p = 0 :=
    spaceTimeWord_eq_zero_of_compl hη.compact γ hη.zeta_zero p.1 hp p.2
  have hvj (j : Fin 3) (p : Vec3 × ℝ) (hp : p.1 ∉ K) (γ : List (Fin 3)) :
      spaceTimeWord γ (fun q => spatialPartial η j q) p = 0 :=
    spaceTimeWord_eq_zero_of_compl hη.compact γ (hη.grad_zero j) p.1 hp p.2
  have hDw0 : ∀ α (p : Vec3 × ℝ), p.1 ∉ K → localHeatGainDw η Dz α p = 0 :=
    fun α p hp => stLeibniz_eq_zero_of_forall α (hvη p hp)
  have hDH0 : ∀ α (p : Vec3 × ℝ), p.1 ∉ K → localHeatGainDH η Dz DG α p = 0 := by
    intro α p hp
    simp only [localHeatGainDH, stLeibniz_eq_zero_of_forall α (hvη p hp),
      stLeibniz_eq_zero_of_forall α (hvζ p hp),
      fun j => stLeibniz_eq_zero_of_forall α (B := fun γ => Dz (j :: γ)) (hvj j p hp),
      Finset.sum_const_zero, mul_zero, add_zero]
  -- the cutoff solution
  have hNz0 : 0 ≤ ∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNG0 : 0 ≤ ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, DG α p ^ 2 :=
    Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_congr rfl fun α _ => integral_univ_prod_sq_eq hIm hη.subset (hDw0 α)]
    have h := hL₀ (B ×ˢ I) (fun γ => spaceTimeWord γ η) Dz L hLη
      (fun γ _ => hmeas η hη.smooth γ) (fun γ hγ => hDz.memL2 γ hγ)
    refine h.trans ?_
    gcongr
    linarith only [hC₁]
  -- the source
  rw [Finset.sum_congr rfl fun α _ => integral_univ_prod_sq_eq hIm hη.subset (hDH0 α)]
  let X₁ : List (Fin 3) → Vec3 × ℝ → ℝ := fun α => stLeibniz α (fun γ => spaceTimeWord γ η) DG
  let X₂ : List (Fin 3) → Vec3 × ℝ → ℝ :=
    fun α => stLeibniz α (fun γ => spaceTimeWord γ (localHeatGainZeta η)) Dz
  let Y : Fin 3 → List (Fin 3) → Vec3 × ℝ → ℝ := fun j α =>
    stLeibniz α (fun γ => spaceTimeWord γ (fun q => spatialPartial η j q)) (fun γ => Dz (j :: γ))
  have hDzm1 : IsSpaceTimeFamily (m - 1) (B ×ˢ I) Dz := hDz.mono_order (Nat.sub_le m 1)
  have hDzj (j : Fin 3) : IsSpaceTimeFamily (m - 1) (B ×ˢ I) (fun γ => Dz (j :: γ)) :=
    hDz.shift hm1 j
  have hX₁L (α : List (Fin 3)) (hα : α ∈ sobolevWords (m - 1)) :
      MemLp (X₁ α) 2 (volume.restrict (B ×ˢ I)) :=
    stLeibniz_memLp α L (fun γ hγ => hLm1 hLη γ (hγ.trans (mem_sobolevWords.1 hα)))
      (fun γ _ => hmeas η hη.smooth γ)
      (fun γ hγ => hDG.memL2 γ (hγ.trans (mem_sobolevWords.1 hα)))
  have hX₂L (α : List (Fin 3)) (hα : α ∈ sobolevWords (m - 1)) :
      MemLp (X₂ α) 2 (volume.restrict (B ×ˢ I)) :=
    stLeibniz_memLp α L (fun γ hγ => hLm1 hLζ γ (hγ.trans (mem_sobolevWords.1 hα)))
      (fun γ _ => hmeas _ hη.smooth_zeta γ)
      (fun γ hγ => hDzm1.memL2 γ (hγ.trans (mem_sobolevWords.1 hα)))
  have hYL (j : Fin 3) (α : List (Fin 3)) (hα : α ∈ sobolevWords (m - 1)) :
      MemLp (Y j α) 2 (volume.restrict (B ×ˢ I)) :=
    stLeibniz_memLp α L (fun γ hγ => hLm1 (hLg j) γ (hγ.trans (mem_sobolevWords.1 hα)))
      (fun γ _ => hmeas _ (hη.smooth_grad j) γ)
      (fun γ hγ => (hDzj j).memL2 γ (hγ.trans (mem_sobolevWords.1 hα)))
  have hpt (α : List (Fin 3)) (p : Vec3 × ℝ) :
      localHeatGainDH η Dz DG α p ^ 2 ≤
        3 * X₁ α p ^ 2 + 3 * X₂ α p ^ 2 + 36 * ∑ j : Fin 3, Y j α p ^ 2 := by
    change (X₁ α p + (X₂ α p + (-2) * ∑ j : Fin 3, Y j α p)) ^ 2 ≤ _
    simp only [Fin.sum_univ_three]
    nlinarith only [sq_nonneg (X₁ α p - X₂ α p),
      sq_nonneg (X₁ α p + 2 * (Y 0 α p + Y 1 α p + Y 2 α p)),
      sq_nonneg (X₂ α p + 2 * (Y 0 α p + Y 1 α p + Y 2 α p)),
      sq_nonneg (Y 0 α p - Y 1 α p), sq_nonneg (Y 1 α p - Y 2 α p),
      sq_nonneg (Y 0 α p - Y 2 α p)]
  have hint (α : List (Fin 3)) (hα : α ∈ sobolevWords (m - 1)) :
      ∫ p in B ×ˢ I, localHeatGainDH η Dz DG α p ^ 2 ≤
        3 * (∫ p in B ×ˢ I, X₁ α p ^ 2) + 3 * (∫ p in B ×ˢ I, X₂ α p ^ 2) +
          36 * ∑ j : Fin 3, ∫ p in B ×ˢ I, Y j α p ^ 2 := by
    have i1 := (hX₁L α hα).integrable_sq
    have i2 := (hX₂L α hα).integrable_sq
    have i3 (j : Fin 3) := (hYL j α hα).integrable_sq
    have hDHL : MemLp (localHeatGainDH η Dz DG α) 2 (volume.restrict (B ×ˢ I)) :=
      (hX₁L α hα).add ((hX₂L α hα).add
        ((memLp_finsetSum _ fun j _ => hYL j α hα).const_mul (-2)))
    have iR : Integrable (fun p => 3 * X₁ α p ^ 2 + 3 * X₂ α p ^ 2 +
        36 * ∑ j : Fin 3, Y j α p ^ 2) (volume.restrict (B ×ˢ I)) :=
      ((i1.const_mul 3).add (i2.const_mul 3)).add
        ((integrable_finsetSum _ fun j _ => i3 j).const_mul 36)
    refine (integral_mono hDHL.integrable_sq iR (hpt α)).trans (le_of_eq ?_)
    have i12 : Integrable (fun p => 3 * X₁ α p ^ 2 + 3 * X₂ α p ^ 2)
        (volume.restrict (B ×ˢ I)) := (i1.const_mul 3).add (i2.const_mul 3)
    rw [integral_add i12 ((integrable_finsetSum _ fun j _ => i3 j).const_mul 36),
      integral_add (i1.const_mul 3) (i2.const_mul 3), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun j _ => i3 j]
  have hS1 := hL₁ (B ×ˢ I) (fun γ => spaceTimeWord γ η) DG L (hLm1 hLη)
    (fun γ _ => hmeas η hη.smooth γ) (fun γ hγ => hDG.memL2 γ hγ)
  have hS2 := hL₁ (B ×ˢ I) (fun γ => spaceTimeWord γ (localHeatGainZeta η)) Dz L (hLm1 hLζ)
    (fun γ _ => hmeas _ hη.smooth_zeta γ) (fun γ hγ => hDzm1.memL2 γ hγ)
  have hS3 (j : Fin 3) := hL₁ (B ×ˢ I) (fun γ => spaceTimeWord γ (fun q => spatialPartial η j q))
    (fun γ => Dz (j :: γ)) L (hLm1 (hLg j)) (fun γ _ => hmeas _ (hη.smooth_grad j) γ)
    (fun γ hγ => (hDzj j).memL2 γ hγ)
  have hW1 : ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, Dz α p ^ 2 ≤
      ∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (sobolevWords_mono (Nat.sub_le m 1))
      fun _ _ _ => integral_nonneg fun _ => sq_nonneg _
  have hW2 (j : Fin 3) : ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, Dz (j :: α) p ^ 2 ≤
      ∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2 := by
    have h := sum_sobolevWords_cons_le (m - 1) j (fun α => ∫ p in B ×ˢ I, Dz α p ^ 2)
      fun _ => integral_nonneg fun _ => sq_nonneg _
    rwa [Nat.sub_add_cancel hm1] at h
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  calc
    ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, localHeatGainDH η Dz DG α p ^ 2 ≤
        ∑ α ∈ sobolevWords (m - 1), (3 * (∫ p in B ×ˢ I, X₁ α p ^ 2) +
          3 * (∫ p in B ×ˢ I, X₂ α p ^ 2) + 36 * ∑ j : Fin 3, ∫ p in B ×ˢ I, Y j α p ^ 2) :=
      Finset.sum_le_sum hint
    _ = 3 * (∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, X₁ α p ^ 2) +
          3 * (∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, X₂ α p ^ 2) +
          36 * ∑ j : Fin 3, ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, Y j α p ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 3 * (C₁ * L ^ 2 * ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, DG α p ^ 2) +
          3 * (C₁ * L ^ 2 * ∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2) +
          36 * ∑ j : Fin 3, C₁ * L ^ 2 * ∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2 := by
      refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hS1 (by norm_num))
        (mul_le_mul_of_nonneg_left ((hS2).trans
          (mul_le_mul_of_nonneg_left hW1 (by positivity))) (by norm_num)))
        (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => (hS3 j).trans
          (mul_le_mul_of_nonneg_left (hW2 j) (by positivity))) (by norm_num))
    _ ≤ (C₀ + 111 * C₁) * L ^ 2 * ((∑ α ∈ sobolevWords m, ∫ p in B ×ˢ I, Dz α p ^ 2) +
          ∑ α ∈ sobolevWords (m - 1), ∫ p in B ×ˢ I, DG α p ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]
      have hC₀L : 0 ≤ C₀ * L ^ 2 := mul_nonneg hC₀ hL2
      have hC₁L : 0 ≤ C₁ * L ^ 2 := mul_nonneg hC₁ hL2
      nlinarith only [mul_nonneg hC₀L hNz0, mul_nonneg hC₀L hNG0,
        mul_nonneg hC₁L hNz0, mul_nonneg hC₁L hNG0]

end ESS
