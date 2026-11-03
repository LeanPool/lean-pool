/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec111aPredictors.BandScaleSumAssembly

/-!
# Trilinear Hilbert transform: expansion_catalog_tail
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate

open scoped Classical in
private def ExpansionCatalogTailHcellStatement : Prop :=
  ∀ (d : ℕ)
    (A : QuadraticChartData d)
    (E : ℝ)
    (E1 : ℝ)
    (K₀ : ℕ)
    (G : RealDyadicGrid)
    (S : Finset (ℤ × ℤ))
    (lamf : ℤ → ℝ)
    (σf : ℤ → ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ)
    (coeff : ℤ → ℕ × (Fin (d + d) → ℤ) → ℂ),
  let T : Finset ℤ :=
    Finset.image Prod.fst S
  let N₀ : ℕ :=
    ⌊E⌋₊
  let P : Finset (ℕ × (Fin (d + d) → ℤ)) :=
    Finset.range N₀ ×ˢ frequencyTruncationSet (d + d) K₀
  let freq : ℤ → ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (s : ℤ) (p : ℕ × (Fin (d + d) → ℤ)) => A.linear + ∑ i : Fin d, (↑(σf s p i) : ℝ)
      * A.horizontal i
  ∀ (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ),
  let env : ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (p : ℕ × (Fin (d + d) → ℤ)) => if p.1 < N₀ then E1 * (((1 : ℝ) + frequencyLength
      p.2) ^ (d + (1 : ℕ)) ^ (2 : ℕ))⁻¹ else (0 : ℝ)
  ∀ (_ : ∀ s ∈ T, ∀ (p : ℕ × (Fin (d + d) → ℤ)), ‖coeff s p‖ ≤ env p)
    (_ : ∀ I ∈ S, Summable fun (p : ℕ × (Fin (d + d) → ℤ)) => if p ∈ P then (0 : ℝ) else env
      p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)),
  ∀ I ∈ S, (dyadicGridLength G I.1 * ∑' (p : ℕ × (Fin (d + d) → ℤ)), if p ∈ P then (0
    : ℝ) else ‖coeff I.1 p‖ * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖) ≤ ∑' (p : ℕ
    × (Fin (d + d) → ℤ)), if p ∈ P then (0 : ℝ) else env p * (dyadicGridLength G I.1 *
    ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)


open scoped Classical in
private def ExpansionCatalogTailHphaseStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (G : RealDyadicGrid)
    (S : Finset (ℤ × ℤ))
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : Measurable ψa)
    (_ : Measurable ψb)
    (_ : ∀ (y : ℝ), ‖ψa y‖ ≤ (1 : ℝ))
    (_ : ∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ))
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : (0 : ℝ) ≤ localKernelSupBound κ)
    (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ),
  ∀ I ∈ S, ∀ (φ : ℝ → ℂ), (∀ (t : ℝ), ‖φ t‖ ≤ (1 : ℝ)) → dyadicGridLength G I.1 * ‖Hf
    I φ‖ ≤ localKernelSupBound κ * (√(∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖za I y‖
    ^ (2 : ℕ)) * √(∫ (y : ℝ) in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ (2 : ℕ)))


open scoped Classical in
private def ExpansionCatalogTailStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (d : ℕ)
    (_ : (1 : ℕ) ≤ d)
    (A : QuadraticChartData d)
    (E : ℝ)
    (E1 : ℝ)
    (_ : (1 : ℝ) ≤ E)
    (_ : (0 : ℝ) ≤ E1)
    (K₀ : ℕ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (S : Finset (ℤ × ℤ))
    (_ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1) (w I))
    (a : Fin (4 : ℕ))
    (b : Fin (4 : ℕ))
    (_ : a ≠ b)
    (ψa : ℝ → ℂ)
    (ψb : ℝ → ℂ)
    (_ : Measurable ψa)
    (_ : Measurable ψb)
    (_ : ∀ (y : ℝ), ‖ψa y‖ ≤ (1 : ℝ))
    (_ : ∀ (y : ℝ), ‖ψb y‖ ≤ (1 : ℝ))
    (Fa : ℝ → ℂ)
    (Fb : ℝ → ℂ)
    (za : ℤ × ℤ → ℝ → ℂ)
    (zb : ℤ × ℤ → ℝ → ℂ)
    (Ka : ℝ)
    (Kb : ℝ)
    (_ : (0 : ℝ) ≤ Ka)
    (_ : (0 : ℝ) ≤ Kb)
    (_ : IsAdmissibleOpponent G J Fa za Ka)
    (_ : IsAdmissibleOpponent G J Fb zb Kb)
    (_ : HasDepthEnergy G J Fa za Ka)
    (_ : HasDepthEnergy G J Fb zb Kb)
    (_ : ∀ (I : ℤ × ℤ), Measurable (za I))
    (_ : ∀ (I : ℤ × ℤ), Measurable (zb I))
    (_ : ∀ (I : ℤ × ℤ), MemLp (za I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (I : ℤ × ℤ), MemLp (zb I) (2 : ENNReal) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (lamf : ℤ → ℝ)
    (Mf : ℤ → Matrix (Fin d) (Fin d) ℚ)
    (σf : ℤ → ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ)
    (coeff : ℤ → ℕ × (Fin (d + d) → ℤ) → ℂ),
  let T : Finset ℤ :=
    Finset.image Prod.fst S
  let N₀ : ℕ :=
    ⌊E⌋₊
  ∀ (_ : ∀ s ∈ T, (∀ (i j : Fin d), (↑(rationalHeight (Mf s i j)) : ℝ) ≤ E) ∧ lamf s =
      A.quadratic + ∑ i : Fin d, ∑ j : Fin d, A.horizontal i * (↑(Mf s i j) : ℝ) *
      A.horizontal j ∧ |lamf s| * dyadicGridLength G s ^ (2 : ℕ) ≤ E ∧ (∀ (p : ℕ × (Fin
      (d + d) → ℤ)) (i : Fin d), (↑(rationalHeight (σf s p i)) : ℝ) ≤ E * ((1 : ℝ) +
      frequencyLength p.2)) ∧ (∀ (p : ℕ × (Fin (d + d) → ℤ)), N₀ ≤ p.1 → coeff s p = (0
      : ℂ)) ∧ ∀ (p : ℕ × (Fin (d + d) → ℤ)), ‖coeff s p‖ * ((1 : ℝ) + frequencyLength
      p.2) ^ (d + (1 : ℕ)) ^ (2 : ℕ) ≤ E1),
  let P : Finset (ℕ × (Fin (d + d) → ℤ)) :=
    Finset.range N₀ ×ˢ frequencyTruncationSet (d + d) K₀
  let Na : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ (2 : ℕ))
  let Nb : ℝ :=
    √(∫ (y : ℝ) in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) ≤ Ka * Kb * Na * Nb)
    (_ : (0 : ℝ) ≤ localKernelSupBound κ)
    (_ : (0 : ℝ) ≤ linearScaleConst κ),
  let freq : ℤ → ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (s : ℤ) (p : ℕ × (Fin (d + d) → ℤ)) => A.linear + ∑ i : Fin d, (↑(σf s p i) : ℝ)
      * A.horizontal i
  ∀ (Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ)
    (_ : ∀ (I : ℤ × ℤ) (φ : ℝ → ℂ), (separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun (y : ℝ) => ψa y * za I y) fun (y : ℝ) => ψb y * zb I y) = Hf I φ),
  let env : ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun (p : ℕ × (Fin (d + d) → ℤ)) => if p.1 < N₀ then E1 * (((1 : ℝ) + frequencyLength
      p.2) ^ (d + (1 : ℕ)) ^ (2 : ℕ))⁻¹ else (0 : ℝ)
  ∀ (_ : ∀ (p : ℕ × (Fin (d + d) → ℤ)), (0 : ℝ) ≤ env p)
    (_ : ∀ I ∈ S, Summable fun (p : ℕ × (Fin (d + d) → ℤ)) => if p ∈ P then (0 : ℝ) else env
      p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖))
    (_ : ∀ I ∈ S, (dyadicGridLength G I.1 * ∑' (p : ℕ × (Fin (d + d) → ℤ)), if p ∈ P then (0
      : ℝ) else ‖coeff I.1 p‖ * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖) ≤ ∑' (p : ℕ
      × (Fin (d + d) → ℤ)), if p ∈ P then (0 : ℝ) else env p * (dyadicGridLength G I.1 *
      ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)),
  (∑ x ∈ S, dyadicGridLength G x.1 * ∑' (p : ℕ × (Fin (d + d) → ℤ)), if p ∈ P then (0
    : ℝ) else ‖coeff x.1 p‖ * ‖Hf x (quadPhase (lamf x.1) (A.linear + ∑ i : Fin d,
    (↑(σf x.1 p i) : ℝ) * A.horizontal i))‖) ≤ (↑N₀ : ℝ) * (E1 * tailCT κ d E * ((2 :
    ℝ) * (7 : ℝ) ^ (d + d) * ((2 : ℝ) * Real.pi) ^ ((d + (1 : ℕ)) ^ (2 : ℕ) - (1 : ℕ))
    / (2 : ℝ) ^ K₀)) * Ka * Kb * Na * Nb




private theorem expansion_catalog_tail_hcell : ExpansionCatalogTailHcellStatement := by
  classical
  intro d A E E1 K₀ G S lamf σf coeff T N₀ P freq Hf env henv hgs I hI
  rw [← tsum_mul_left]
  have hs1 : Summable (fun p => dyadicGridLength G I.1 * (if p ∈ P then 0 else
      ‖coeff I.1 p‖ * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)) := by
    refine Summable.of_nonneg_of_le (fun p => by
        split_ifs
        · exact mul_nonneg (dyadicGridLength_pos G I.1).le le_rfl
        · exact mul_nonneg (dyadicGridLength_pos G I.1).le
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (fun p => ?_) (hgs I hI)
    split_ifs
    · simp
    · calc dyadicGridLength G I.1 * (‖coeff I.1 p‖ *
            ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)
          = ‖coeff I.1 p‖ * (dyadicGridLength G I.1 *
            ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (henv I.1 (Finset.mem_image_of_mem _ hI) p)
            (by have := dyadicGridLength_pos G I.1; positivity)
  refine Summable.tsum_le_tsum (fun p => ?_) hs1 (hgs I hI)
  split_ifs
  · simp
  · calc dyadicGridLength G I.1 * (‖coeff I.1 p‖ *
          ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)
        = ‖coeff I.1 p‖ * (dyadicGridLength G I.1 *
          ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (henv I.1 (Finset.mem_image_of_mem _ hI) p)
          (by have := dyadicGridLength_pos G I.1; positivity)
-- rational centers and the quadratic total



private theorem expansion_catalog_tail_hphase : ExpansionCatalogTailHphaseStatement := by
  classical
  intro κ G S w hw a b hab ψa ψb hψam hψbm hψa hψb za zb hzam hzbm hza2 hzb2 hC Hf eHf I hIS φ hφ
  have hr := dyadicGridLength_pos G I.1
  have hFam : Measurable (fun y => ψa y * za I y) := hψam.mul (hzam I)
  have hFbm : Measurable (fun y => ψb y * zb I y) := hψbm.mul (hzbm I)
  have h := separatedLocalForm_sup_le hr (hw I hIS) hab zero_le_one (fun t _ => hφ t)
    hFam hFbm (memLp_mul_bounded_restrict hψam hψa (hza2 I))
    (memLp_mul_bounded_restrict hψbm hψb (hzb2 I))
  rw [eHf] at h
  have hnorm := cell_normalized_product (X := ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
      (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2)
    (Y := ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
      (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2) hr
  have hXa := setIntegral_mul_bounded_le hψa (hza2 I)
  have hXb := setIntegral_mul_bounded_le hψb (hzb2 I)
  calc dyadicGridLength G I.1 * ‖Hf I φ‖
      ≤ dyadicGridLength G I.1 * (localKernelSupBound κ * 1 *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hr.le
    _ = localKernelSupBound κ * (dyadicGridLength G I.1 *
          (Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψa y * za I y‖ ^ 2) *
          Real.sqrt ((dyadicGridLength G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft G I.1 I.2)
            (dyadicGridLeft G I.1 I.2 + dyadicGridLength G I.1), ‖ψb y * zb I y‖ ^ 2))) := by
        ring
    _ ≤ _ := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hXa)
          (Real.sqrt_le_sqrt hXb) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hC
-- per-cell domination by the envelope



private theorem expansion_catalog_tail_stage_1 : ExpansionCatalogTailStage1Statement := by
  classical
  intro κ d hd A E E1 hE hE10 K₀ G J S hSJ w hw a b hab ψa ψb hψam hψbm hψa hψb Fa Fb za zb Ka Kb
    hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 lamf Mf σf coeff T N₀ hprops P Na Nb hK hC hlin
    freq Hf eHf env henv0 hgs hcell
  set! k : ℤ := ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) with hkd
  have hkR : (k : ℝ) = (b : ℝ) - (a : ℝ) := by rw [hkd]; push_cast; rfl
  have hk0 : k ≠ 0 := by
    rw [hkd]; intro h; apply hab; apply Fin.ext; omega
  have hk3 : |(k : ℝ)| ≤ 3 := by
    rw [hkR]
    have ha := abs_fin_four_le a
    have hb := abs_fin_four_le b
    rw [abs_le] at ha hb ⊢
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2,
      show (0 : ℝ) ≤ (a : ℝ) by positivity, show (0 : ℝ) ≤ (b : ℝ) by positivity]
  have hB₁2 : 2 ≤ E + 2 := by linarith
  set! Λ := tailLam d E with hΛd
  have hΛ : ∑ s ∈ T, 2 * Real.pi * |lamf s| * dyadicGridLength G s ^ 2 ≤ Λ := by
    have h := band_quadratic_total G A.horizontal A.quadratic T lamf Mf (by linarith) hB₁2
      (fun s hs => (hprops s hs).2.1)
      (fun s hs i j => ((hprops s hs).1 i j).trans (by linarith))
      (fun s hs => (hprops s hs).2.2.1)
    refine h.trans (le_of_eq ?_)
    rw [hΛd, tailLam]
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛd, tailLam]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (E + 2) by linarith)
    positivity
  set! Mt : ℕ × (Fin (d + d) → ℤ) → ℝ := fun p =>
    clumpMultiplicity (d + 1) (6 * (E * (1 + frequencyLength p.2)) ^ 2 + 6) with hMtd
  have hMt : ∀ p ξ, ∑ x ∈ S.image (fun I => (I.1, freq I.1 p / ((b : ℝ) - (a : ℝ)))),
      bumpMultiplier (dyadicGridLength G x.1 * (ξ - x.2)) ≤ Mt p := by
    intro p ξ
    have hB : 2 ≤ 6 * (E * (1 + frequencyLength p.2)) ^ 2 + 6 := by
      have : 0 ≤ 6 * (E * (1 + frequencyLength p.2)) ^ 2 := by positivity
      linarith
    refine rational_center_multiplicity G (Fin.cons A.linear A.horizontal) hB _
      (fun x hx => ?_) (fun x hx y hy hxy hne => ?_) ξ
    · obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
      have hs : I.1 ∈ T := Finset.mem_image_of_mem _ hI
      obtain ⟨h1, h2⟩ := center_rational A.linear A.horizontal (σf I.1 p) hk0 hk3
        ((hprops I.1 hs).2.2.2.1 p)
      refine ⟨_, h1, ?_⟩
      simp only
      rw [← hkR]; exact h2
    · exfalso
      obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨I', _, rfl⟩ := Finset.mem_image.mp hy
      simp only at hxy
      apply hne
      simp only [hxy]
  have hCT0 := tailCT_nonneg κ d hE
  have hg : ∀ p : ℕ × (Fin (d + d) → ℤ), linearScaleConst κ * Mt p +
      localKernelSupBound κ * Λ ≤ tailCT κ d E * (1 + frequencyLength p.2) := by
    intro p
    have hu : 1 ≤ 1 + frequencyLength p.2 := by have := frequencyLength_nonneg p.2; linarith
    have h1 := clumpMultiplicity_tail_le' d hE hu
    have e1 : linearScaleConst κ * Mt p ≤
        linearScaleConst κ * tailAlpha d E * (1 + frequencyLength p.2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hlin
    have e2 : localKernelSupBound κ * Λ ≤
        localKernelSupBound κ * Λ * (1 + frequencyLength p.2) :=
      le_mul_of_one_le_right (mul_nonneg hC hΛ0) hu
    calc linearScaleConst κ * Mt p + localKernelSupBound κ * Λ
        ≤ linearScaleConst κ * tailAlpha d E * (1 + frequencyLength p.2) +
          localKernelSupBound κ * Λ * (1 + frequencyLength p.2) := add_le_add e1 e2
      _ = tailCT κ d E * (1 + frequencyLength p.2) := by rw [tailCT, hΛd]; ring
  have hg0 : ∀ p, 0 ≤ linearScaleConst κ * Mt p + localKernelSupBound κ * Λ := by
    intro p
    have hM0 : 0 ≤ Mt p := by
      simp only [hMtd, clumpMultiplicity]
      have : 2 ≤ 6 * (E * (1 + frequencyLength p.2)) ^ 2 + 6 := by
        have : 0 ≤ 6 * (E * (1 + frequencyLength p.2)) ^ 2 := by positivity
        linarith
      have := heightBandConst_nonneg (d + 1) this
      positivity
    positivity
  obtain ⟨_, hTs, hTt⟩ := catalog_weighted_tail hd (N₀ := N₀) (K₀ := K₀) hE10 hCT0
    (fun p => linearScaleConst κ * Mt p + localKernelSupBound κ * Λ) hg0 hg
  -- assemble
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [← Summable.tsum_finsetSum hgs]
  have hpt : ∀ p, ∑ I ∈ S, (if p ∈ P then 0 else
      env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)) ≤
      (if p ∈ P then 0 else env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ)) *
        (Ka * Kb * Na * Nb) := by
    intro p
    by_cases hp : p ∈ P
    · simp [hp]
    simp only [hp, ite_false]
    rw [← Finset.mul_sum]
    have hsp := single_phase_scale_sum G κ J S hSJ w hw hab lamf (fun s => freq s p)
      hψam hψbm hψa hψb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 (M := Mt p)
      (fun ξ => hMt p ξ) (Λ := Λ) hΛ
    simp only [eHf] at hsp
    calc env p * ∑ I ∈ S, dyadicGridLength G I.1 * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖
        ≤ env p * ((linearScaleConst κ * Mt p + localKernelSupBound κ * Λ) * Ka * Kb *
          Na * Nb) := mul_le_mul_of_nonneg_left hsp (henv0 p)
      _ = _ := by ring
  refine (Summable.tsum_le_tsum hpt (summable_sum fun I hI => hgs I hI) (hTs.mul_right _)).trans ?_
  rw [tsum_mul_right]
  calc (∑' p, (if p ∈ P then 0 else
        env p * (linearScaleConst κ * Mt p + localKernelSupBound κ * Λ))) * (Ka * Kb * Na * Nb)
      ≤ ((N₀ : ℝ) * (E1 * tailCT κ d E *
        (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2 - 1) / 2 ^ K₀))) * (Ka * Kb * Na * Nb) :=
        mul_le_mul_of_nonneg_right hTt hK
    _ = _ := by ring


/-- Blueprint lem:predictors, proof lines 1519-1523: the pooled chart-expansion tails
outside a finite catalog are small in the absolute scale-sum norm. -/
theorem expansion_catalog_tail (κ : LocalKernelClass) {d : ℕ} (hd : 1 ≤ d)
    (A : QuadraticChartData d) {E E1 : ℝ} (hE : 1 ≤ E) (hE10 : 0 ≤ E1) (K₀ : ℕ)
    (G : RealDyadicGrid) (J : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (hSJ : ∀ I ∈ S, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J.1 J.2)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (hw : ∀ I ∈ S, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    {a b : Fin 4} (hab : a ≠ b) {ψa ψb : ℝ → ℂ} (hψam : Measurable ψa) (hψbm : Measurable ψb)
    (hψa : ∀ y, ‖ψa y‖ ≤ 1) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    {Fa Fb : ℝ → ℂ} {za zb : ℤ × ℤ → ℝ → ℂ} {Ka Kb : ℝ} (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb)
    (hza : IsAdmissibleOpponent G J Fa za Ka) (hzb : IsAdmissibleOpponent G J Fb zb Kb)
    (hEa : HasDepthEnergy G J Fa za Ka) (hEb : HasDepthEnergy G J Fb zb Kb)
    (hzam : ∀ I, Measurable (za I)) (hzbm : ∀ I, Measurable (zb I))
    (hza2 : ∀ I, MemLp (za I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (hzb2 : ∀ I, MemLp (zb I) 2 (volume.restrict (dyadicGridCell G I.1 I.2)))
    (lamf : ℤ → ℝ) (Mf : ℤ → Matrix (Fin d) (Fin d) ℚ)
    (σf : ℤ → ℕ × (Fin (d + d) → ℤ) → Fin d → ℚ) (coeff : ℤ → ℕ × (Fin (d + d) → ℤ) → ℂ)
    (hprops : ∀ s ∈ S.image Prod.fst,
      (∀ i j, (rationalHeight (Mf s i j) : ℝ) ≤ E) ∧
      lamf s = A.quadratic + ∑ i, ∑ j, A.horizontal i * (Mf s i j : ℝ) * A.horizontal j ∧
      |lamf s| * dyadicGridLength G s ^ 2 ≤ E ∧
      (∀ p i, (rationalHeight (σf s p i) : ℝ) ≤ E * (1 + frequencyLength p.2)) ∧
      (∀ p, ⌊E⌋₊ ≤ p.1 → coeff s p = 0) ∧
      ∀ p, ‖coeff s p‖ * (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) ≤ E1) :
    ∑ I ∈ S, dyadicGridLength G I.1 * ∑' p, (if p ∈ (Finset.range ⌊E⌋₊) ×ˢ
      (frequencyTruncationSet (d + d) K₀) then 0 else ‖coeff I.1 p‖ *
        ‖separatedLocalForm (dyadicGridLength G I.1) (w I)
          (quadPhase (lamf I.1) (A.linear + ∑ i, (σf I.1 p i : ℝ) * A.horizontal i)) a b
          (fun y => ψa y * za I y) (fun y => ψb y * zb I y)‖) ≤
      (⌊E⌋₊ : ℝ) * (E1 * tailCT κ d E *
        (2 * 7 ^ (d + d) * (2 * Real.pi) ^ ((d + 1) ^ 2 - 1) / 2 ^ K₀)) *
        Ka * Kb * Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2) *
        Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2) := by
  classical
  set T := S.image Prod.fst with hT
  set N₀ := ⌊E⌋₊ with hN₀
  set P : Finset (ℕ × (Fin (d + d) → ℤ)) :=
    (Finset.range N₀) ×ˢ (frequencyTruncationSet (d + d) K₀) with hP
  set Na := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fa y‖ ^ 2)
  set Nb := Real.sqrt (∫ y in dyadicGridCell G J.1 J.2, ‖Fb y‖ ^ 2)
  have hK : 0 ≤ Ka * Kb * Na * Nb := by positivity
  have hC := localKernelSupBound_nonneg κ
  have hlin := linearScaleConst_nonneg κ
  set! freq : ℤ → ℕ × (Fin (d + d) → ℤ) → ℝ :=
    fun s p => A.linear + ∑ i, (σf s p i : ℝ) * A.horizontal i with hfreq
  obtain ⟨Hf, hHf⟩ : ∃ Hf : ℤ × ℤ → (ℝ → ℂ) → ℂ, Hf = fun I φ =>
      separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
        (fun y => ψa y * za I y) (fun y => ψb y * zb I y) := ⟨_, rfl⟩
  have eHf : ∀ I φ, separatedLocalForm (dyadicGridLength G I.1) (w I) φ a b
      (fun y => ψa y * za I y) (fun y => ψb y * zb I y) = Hf I φ := fun I φ => by rw [hHf]
  simp only [eHf]
  -- the envelope
  set! env : ℕ × (Fin (d + d) → ℤ) → ℝ := fun p => if p.1 < N₀ then
    E1 * ((1 + frequencyLength p.2) ^ ((d + 1) ^ 2))⁻¹ else 0 with henvd
  have henv0 : ∀ p, 0 ≤ env p := fun p => by
    simp only [henvd]; split_ifs
    · have := frequencyLength_nonneg p.2; positivity
    · exact le_rfl
  have henv : ∀ s ∈ T, ∀ p, ‖coeff s p‖ ≤ env p := by
    intro s hs p
    have hpos : 0 < (1 + frequencyLength p.2) ^ ((d + 1) ^ 2) := by
      have := frequencyLength_nonneg p.2; positivity
    simp only [henvd]
    split_ifs with hp
    · rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      exact (hprops s hs).2.2.2.2.2 p
    · rw [(hprops s hs).2.2.2.2.1 p (not_lt.mp hp), norm_zero]
  -- uniform bound of single forms
  have hphase : ∀ I ∈ S, ∀ φ : ℝ → ℂ, (∀ t, ‖φ t‖ ≤ 1) →
      dyadicGridLength G I.1 * ‖Hf I φ‖ ≤ localKernelSupBound κ *
        (Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ 2)) := by
    expose_names
    exact @expansion_catalog_tail_hphase κ G S w hw a b hab ψa ψb hψam hψbm hψa hψb za zb hzam
      hzbm hza2 hzb2 hC Hf eHf
  have hgs : ∀ I ∈ S, Summable (fun p => if p ∈ P then 0 else
      env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)) := by
    intro I hI
    have hens0 := (catalog_weighted_tail (N₀ := N₀) (K₀ := K₀) hd hE10 (le_refl 0)
      (fun _ => (0 : ℝ)) (fun _ => le_rfl) (fun p => by simp)).1
    have hens : Summable env := hens0
    have hr := dyadicGridLength_pos G I.1
    have hXY : 0 ≤ localKernelSupBound κ *
        (Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ 2)) := by positivity
    refine Summable.of_nonneg_of_le (fun p => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (henv0 p) (mul_nonneg hr.le (norm_nonneg _)))
      (fun p => ?_) (hens.mul_right (localKernelSupBound κ *
        (Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖za I y‖ ^ 2) *
          Real.sqrt (∫ y in dyadicGridCell G I.1 I.2, ‖zb I y‖ ^ 2))))
    by_cases hp : p ∈ P
    · rw [ite_eq_left hp]; exact mul_nonneg (henv0 p) hXY
    · rw [ite_eq_right hp]
      exact mul_le_mul_of_nonneg_left (hphase I hI (quadPhase (lamf I.1) (freq I.1 p))
        fun t => (norm_quadPhase _ _ t).le) (henv0 p)
  have hcell : ∀ I ∈ S, dyadicGridLength G I.1 * ∑' p, (if p ∈ P then 0 else
      ‖coeff I.1 p‖ * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖) ≤
      ∑' p, (if p ∈ P then 0 else
        env p * (dyadicGridLength G I.1 * ‖Hf I (quadPhase (lamf I.1) (freq I.1 p))‖)) := by
    expose_names
    exact @expansion_catalog_tail_hcell d A E E1 K₀ G S lamf σf coeff Hf henv hgs
  expose_names
  exact @expansion_catalog_tail_stage_1 κ d hd A E E1 hE hE10 K₀ G J S hSJ w hw a b hab ψa ψb hψam
    hψbm hψa hψb Fa Fb za zb Ka Kb hKa hKb hza hzb hEa hEb hzam hzbm hza2 hzb2 lamf Mf σf coeff
    hprops hK hC hlin Hf eHf henv0 hgs hcell

/-- Layer-cake form of the separation shell bound: the size-weighted coefficient mass beyond
`T₀` is at most `4 E / T₀^{99}` (blueprint lem:predictors, line 1546). -/
theorem weighted_shell_tail {τ : Type*} (cf : τ → ℂ) (size : τ → ℝ)
    {Es : ℝ} (hEs : 0 ≤ Es)
    (htail : ∀ T : ℝ, 1 ≤ T → (∑' q, if T ≤ size q then ‖cf q‖ else 0) ≤ Es / T ^ 100)
    (hcs : Summable (fun q => ‖cf q‖)) {T₀ : ℝ} (hT₀ : 1 ≤ T₀) :
    Summable (fun q => if T₀ < size q then ‖cf q‖ * size q else 0) ∧
      (∑' q, if T₀ < size q then ‖cf q‖ * size q else 0) ≤ 4 * Es / T₀ ^ 99 := by
  classical
  have hT0 : 0 < T₀ := by linarith
  set g : ℕ × τ → ℝ := fun x => if (2 : ℝ) ^ x.1 * T₀ ≤ size x.2 then
    ‖cf x.2‖ * ((2 : ℝ) ^ (x.1 + 1) * T₀) else 0 with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => by simp only [hg]; split_ifs <;> positivity
  -- the inner sums over `τ`
  have hinner : ∀ j : ℕ, Summable (fun q => g (j, q)) ∧
      (∑' q, g (j, q)) ≤ 2 * Es / T₀ ^ 99 * ((1 / 2 : ℝ) ^ 99) ^ j := by
    intro j
    have hT : 1 ≤ (2 : ℝ) ^ j * T₀ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hT₀
    have hs : Summable (fun q => if (2 : ℝ) ^ j * T₀ ≤ size q then ‖cf q‖ else 0) :=
      hcs.of_nonneg_of_le (fun q => by split_ifs <;> positivity) (fun q => by
        split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
    have he : (fun q => g (j, q)) = fun q =>
        (if (2 : ℝ) ^ j * T₀ ≤ size q then ‖cf q‖ else 0) * ((2 : ℝ) ^ (j + 1) * T₀) := by
      funext q; simp only [hg]; split_ifs <;> simp
    rw [he]
    refine ⟨hs.mul_right _, ?_⟩
    rw [tsum_mul_right]
    have h := htail _ hT
    calc (∑' q, if (2 : ℝ) ^ j * T₀ ≤ size q then ‖cf q‖ else 0) * ((2 : ℝ) ^ (j + 1) * T₀)
        ≤ Es / ((2 : ℝ) ^ j * T₀) ^ 100 * ((2 : ℝ) ^ (j + 1) * T₀) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = 2 * Es / T₀ ^ 99 * ((1 / 2 : ℝ) ^ 99) ^ j := by
          have hu : (0 : ℝ) < 2 ^ j := by positivity
          have e1 : ((1 / 2 : ℝ) ^ 99) ^ j = (((2 : ℝ) ^ j)⁻¹) ^ 99 := by
            rw [← pow_mul, mul_comm, pow_mul, one_div, inv_pow]
          rw [e1, pow_succ]
          set u := (2 : ℝ) ^ j
          field_simp
          ring
  have hgeo : Summable (fun j : ℕ => 2 * Es / T₀ ^ 99 * ((1 / 2 : ℝ) ^ 99) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _
  have hgsum : Summable g := by
    rw [summable_prod_of_nonneg hg0]
    exact ⟨fun j => (hinner j).1, hgeo.of_nonneg_of_le (fun j => tsum_nonneg fun q => hg0 _)
      (fun j => (hinner j).2)⟩
  -- the pointwise layer-cake bound
  have hpt : ∀ q, (if T₀ < size q then ‖cf q‖ * size q else 0) ≤ ∑' j : ℕ, g (j, q) := by
    intro q
    split_ifs with hq
    · have hx : 1 ≤ size q / T₀ := by rw [le_div_iff₀ hT0]; linarith
      obtain ⟨J, hJ1, hJ2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
      have hsJ : Summable (fun j : ℕ => g (j, q)) := hgsum.prod_symm.prod_factor q
      have hle := hsJ.le_tsum J (fun j _ => hg0 _)
      refine le_trans ?_ hle
      simp only [hg]
      rw [ite_eq_left (by rw [← le_div_iff₀ hT0]; exact hJ1)]
      have : size q ≤ (2 : ℝ) ^ (J + 1) * T₀ := by
        have := (div_lt_iff₀ hT0).mp hJ2; linarith
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
    · exact tsum_nonneg fun j => hg0 _
  have hu : Summable (Function.uncurry (fun (j : ℕ) (q : τ) => g (j, q))) := hgsum
  have hcomm : ∑' q, ∑' j : ℕ, g (j, q) = ∑' j : ℕ, ∑' q, g (j, q) :=
    hu.tsum_comm' (fun j => (hinner j).1) (fun q => hgsum.prod_symm.prod_factor q)
  have hlhs : Summable (fun q => if T₀ < size q then ‖cf q‖ * size q else 0) :=
    hgsum.prod_symm.prod.of_nonneg_of_le (fun q => by
      split_ifs with h
      · exact mul_nonneg (norm_nonneg _) (by linarith)
      · exact le_rfl) hpt
  refine ⟨hlhs, ?_⟩
  calc (∑' q, if T₀ < size q then ‖cf q‖ * size q else 0)
      ≤ ∑' q, ∑' j : ℕ, g (j, q) := hlhs.tsum_le_tsum hpt hgsum.prod_symm.prod
    _ = ∑' j : ℕ, ∑' q, g (j, q) := hcomm
    _ ≤ ∑' j : ℕ, 2 * Es / T₀ ^ 99 * ((1 / 2 : ℝ) ^ 99) ^ j :=
        (hgsum.prod).tsum_le_tsum (fun j => (hinner j).2) hgeo
    _ = 2 * Es / T₀ ^ 99 * (1 - (1 / 2 : ℝ) ^ 99)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by norm_num)]
    _ ≤ 4 * Es / T₀ ^ 99 := by
        have h1 : (1 - (1 / 2 : ℝ) ^ 99)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ (by norm_num) (by norm_num)]; norm_num
        have h2 : 0 ≤ 2 * Es / T₀ ^ 99 := by positivity
        calc 2 * Es / T₀ ^ 99 * (1 - (1 / 2 : ℝ) ^ 99)⁻¹ ≤ 2 * Es / T₀ ^ 99 * 2 :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = 4 * Es / T₀ ^ 99 := by ring

/-- Polynomials in `log s` are dominated by `s`: `(a₀ + 6 log s)^C ≤ a₀^C (1 + 6C)^C s`. -/
theorem log_weight_le {a₀ s : ℝ} (ha₀ : 1 ≤ a₀) (hs : 1 ≤ s) (C : ℕ) :
    (a₀ + 6 * Real.log s) ^ C ≤ a₀ ^ C * (1 + 6 * C) ^ C * s := by
  rcases Nat.eq_zero_or_pos C with hC | hC
  · subst hC; simp; linarith
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hs0 : 0 < s := by linarith
  have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs
  have h1 : Real.log s ≤ s ^ (1 / (C : ℝ)) / (1 / (C : ℝ)) :=
    Real.log_le_rpow_div hs0.le (by positivity)
  have hsr : 1 ≤ s ^ (1 / (C : ℝ)) := Real.one_le_rpow hs (by positivity)
  have h2 : Real.log s ≤ C * s ^ (1 / (C : ℝ)) := by
    rw [div_div_eq_mul_div, div_one] at h1; linarith
  have h3 : a₀ + 6 * Real.log s ≤ a₀ * (1 + 6 * C) * s ^ (1 / (C : ℝ)) := by
    have : a₀ + 6 * Real.log s ≤ a₀ * (1 + 6 * Real.log s) := by nlinarith
    refine this.trans ?_
    have h4 : 1 + 6 * Real.log s ≤ (1 + 6 * C) * s ^ (1 / (C : ℝ)) := by nlinarith
    calc a₀ * (1 + 6 * Real.log s) ≤ a₀ * ((1 + 6 * C) * s ^ (1 / (C : ℝ))) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = _ := by ring
  have h5 : (a₀ + 6 * Real.log s) ^ C ≤ (a₀ * (1 + 6 * C) * s ^ (1 / (C : ℝ))) ^ C :=
    pow_le_pow_left₀ (by positivity) h3 C
  refine h5.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (s ^ (1 / (C : ℝ))), ← Real.rpow_mul hs0.le,
    one_div_mul_cancel hC'.ne', Real.rpow_one]

/-- The norm of a tail sum over the complement of a finite set. -/
theorem norm_tsum_compl_le {π : Type*} [DecidableEq π] (P : Finset π) (f : π → ℂ)
    (hf : Summable (fun p => ‖f p‖)) :
    ‖∑' p : ↥((P : Set π)ᶜ), f p‖ ≤ ∑' p, (if p ∈ P then 0 else ‖f p‖) := by
  have hs2 : Summable (fun p : ↥((P : Set π)ᶜ) => ‖f p‖) := hf.subtype _
  refine (norm_tsum_le_tsum_norm hs2).trans (le_of_eq ?_)
  rw [tsum_subtype ((P : Set π)ᶜ) (fun p => ‖f p‖)]
  congr 1; funext p
  by_cases hp : p ∈ P
  · simp [hp]
  · simp [hp]

/-- Blueprint lem:predictors, proof lines 1544-1547, at one cell: the replacement of the
atom-pair form by the retained catalog terms leaves the discarded shells, the discarded
bands and the catalog tails. -/
theorem predictor_cell_bound {τ π : Type*} [DecidableEq τ]
    [DecidableEq π] (cf : τ → ℂ) (hcs : Summable (fun q => ‖cf q‖)) (sepQ : τ → ℂ) {M : ℝ}
    (hsepQ : ∀ q, ‖sepQ q‖ ≤ M) {LF : ℂ} (hLF : HasSum (fun q => cf q * sepQ q) LF)
    (R : Finset τ) (ret : τ → Prop) [DecidablePred ret] (P : Finset π) (coeff : τ → π → ℂ)
    (sepP : τ → π → ℂ) (hcoeff : ∀ q, Summable (fun p => ‖coeff q p‖)) {M' : ℝ}
    (hsepP : ∀ q p, ‖sepP q p‖ ≤ M')
    (hexp : ∀ q ∈ R, ret q → HasSum (fun p => coeff q p * sepP q p) (sepQ q / 4)) :
    ‖LF - ∑ q ∈ R, (if ret q then 4 * cf q * ∑ p ∈ P, coeff q p * sepP q p else 0)‖ ≤
      (∑' q, if q ∈ R then 0 else ‖cf q‖ * ‖sepQ q‖) +
      ∑ q ∈ R, (if ret q then 0 else ‖cf q‖ * ‖sepQ q‖) +
      ∑ q ∈ R, (if ret q then 4 * ‖cf q‖ *
        ∑' p, (if p ∈ P then 0 else ‖coeff q p‖ * ‖sepP q p‖) else 0) := by
  classical
  have hs : Summable (fun q => cf q * sepQ q) := hLF.summable
  have hsplit := hs.sum_add_tsum_compl (s := R)
  rw [hLF.tsum_eq] at hsplit
  have hfn : Summable (fun q => ‖cf q * sepQ q‖) := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_) (hcs.mul_right M)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hsepQ q) (norm_nonneg _)
  -- the retained catalog identity
  have hq : ∀ q ∈ R, cf q * sepQ q -
      (if ret q then 4 * cf q * ∑ p ∈ P, coeff q p * sepP q p else 0) =
      if ret q then 4 * cf q * ∑' p : ↥((P : Set π)ᶜ), coeff q p * sepP q p
      else cf q * sepQ q := by
    intro q hqR
    split_ifs with hr
    · have he := hexp q hqR hr
      have hs' : Summable (fun p => coeff q p * sepP q p) := he.summable
      have h2 := hs'.sum_add_tsum_compl (s := P)
      rw [he.tsum_eq] at h2
      have : sepQ q = 4 * (sepQ q / 4) := by ring
      rw [this, ← h2]; ring
    · ring
  have hdiff : LF - ∑ q ∈ R, (if ret q then 4 * cf q * ∑ p ∈ P, coeff q p * sepP q p else 0) =
      (∑' q : ↥((R : Set τ)ᶜ), cf q * sepQ q) + ∑ q ∈ R,
        (if ret q then 4 * cf q * ∑' p : ↥((P : Set π)ᶜ), coeff q p * sepP q p
          else cf q * sepQ q) := by
    rw [← hsplit, ← Finset.sum_congr rfl hq, Finset.sum_sub_distrib]; ring
  rw [hdiff]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑' q : ↥((R : Set τ)ᶜ), cf q * sepQ q‖ ≤
      ∑' q, if q ∈ R then 0 else ‖cf q‖ * ‖sepQ q‖ := by
    refine (norm_tsum_compl_le R _ hfn).trans (le_of_eq ?_)
    congr 1; funext q; split_ifs <;> simp
  have h2 : ‖∑ q ∈ R, (if ret q then 4 * cf q * ∑' p : ↥((P : Set π)ᶜ), coeff q p * sepP q p
      else cf q * sepQ q)‖ ≤ ∑ q ∈ R, (if ret q then 0 else ‖cf q‖ * ‖sepQ q‖) +
      ∑ q ∈ R, (if ret q then 4 * ‖cf q‖ *
        ∑' p, (if p ∈ P then 0 else ‖coeff q p‖ * ‖sepP q p‖) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    split_ifs with hr
    · rw [zero_add, norm_mul, norm_mul]
      have : ‖(4 : ℂ)‖ = 4 := by norm_num
      rw [this]
      have hsp : Summable (fun p => ‖coeff q p * sepP q p‖) := by
        refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
          ((hcoeff q).mul_right M')
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hsepP q p) (norm_nonneg _)
      have := norm_tsum_compl_le P _ hsp
      refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) (by positivity)
      congr 1; funext p; split_ifs <;> simp
    · rw [add_zero, norm_mul]
  linarith

/-- Regrouping the retained catalog terms of all retained separation terms into the finite
predictor list `(q, M, σ)` with scale-dependent coefficients. -/
theorem predictor_grouping {τ π μ ν : Type*} [DecidableEq μ] [DecidableEq ν]
    (R : Finset τ) (Mset : Finset μ) (σset : Finset ν) (P : Finset π) (ret : τ → Prop)
    [DecidablePred ret] (Mq : τ → μ) (σq : τ → π → ν) (cf : τ → ℂ) (coeff : τ → π → ℂ)
    (X : τ → μ → ν → ℂ) (sepP : τ → π → ℂ)
    (hM : ∀ q ∈ R, ret q → Mq q ∈ Mset) (hσ : ∀ q ∈ R, ret q → ∀ p ∈ P, σq q p ∈ σset)
    (hX : ∀ q ∈ R, ret q → ∀ p ∈ P, X q (Mq q) (σq q p) = sepP q p) :
    ∑ ℓ ∈ R ×ˢ (Mset ×ˢ σset), (if ret ℓ.1 ∧ Mq ℓ.1 = ℓ.2.1 then
      4 * cf ℓ.1 * ∑ p ∈ P.filter (fun p => σq ℓ.1 p = ℓ.2.2), coeff ℓ.1 p else 0) *
        X ℓ.1 ℓ.2.1 ℓ.2.2 =
      ∑ q ∈ R, (if ret q then 4 * cf q * ∑ p ∈ P, coeff q p * sepP q p else 0) := by
  classical
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_product]
  by_cases hr : ret q
  · simp only [hr, true_and, ite_true]
    -- only `M = Mq q` contributes
    have h1 : ∑ M ∈ Mset, ∑ σ ∈ σset, (if Mq q = M then 4 * cf q *
        ∑ p ∈ P.filter (fun p => σq q p = σ), coeff q p else 0) * X q M σ =
        ∑ σ ∈ σset, (4 * cf q * ∑ p ∈ P.filter (fun p => σq q p = σ), coeff q p) *
          X q (Mq q) σ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Finset.sum_eq_single (Mq q)]
      · simp
      · intro M _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (hM q hq hr) h
    rw [h1]
    have h2 : ∑ σ ∈ σset, (4 * cf q * ∑ p ∈ P.filter (fun p => σq q p = σ), coeff q p) *
        X q (Mq q) σ = 4 * cf q * ∑ σ ∈ σset, ∑ p ∈ P.filter (fun p => σq q p = σ),
          coeff q p * X q (Mq q) (σq q p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    rw [h2, Finset.sum_fiberwise_of_maps_to (g := fun p => σq q p) (fun p hp => hσ q hq hr p hp)]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hX q hq hr p hp]
  · simp [hr]

theorem eLpNorm_normalized_ne_top {a r : ℝ} {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Set.Ico a (a + r)))) :
    eLpNorm g 2 (normalizedIntervalMeasure a r) ≠ ⊤ := by
  have hres : volume.restrict (Set.Ico a (a + r)) = volume.restrict (Set.Icc a (a + r)) :=
    Measure.restrict_congr_set Ico_ae_eq_Icc
  rw [hres] at hg
  have h := hg.smul_measure (c := ENNReal.ofReal r⁻¹) ENNReal.ofReal_ne_top
  exact h.eLpNorm_ne_top

theorem eLpNorm_normalized_le_toReal {a r : ℝ} {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Set.Ico a (a + r)))) :
    eLpNorm g 2 (normalizedIntervalMeasure a r) ≤
      ENNReal.ofReal (eLpNorm g 2 (normalizedIntervalMeasure a r)).toReal := by
  rw [ENNReal.ofReal_toReal (eLpNorm_normalized_ne_top hg)]

/-! Explicit parameters of the predictor list (blueprint lem:predictors, lines 1495-1503 and
proof lines 1544-1547). -/

/-- Logarithmic height parameter for the predictor catalog. -/
noncomputable def pdX (H : ℝ) : ℝ := 1 + Real.log H

/-- Initial exponential chart budget for the predictor construction. -/
noncomputable def pdEs (Ds : ℕ) (H : ℝ) : ℝ := Real.exp (Ds * pdX H ^ Ds)

/-- Polynomial base controlling the predictor tail estimates. -/
noncomputable def pdA0 (Ds : ℕ) (H : ℝ) : ℝ := 2 + 6 * (Ds * pdX H ^ Ds)

/-- Initial predictor scale determined by chart complexity and accuracy. -/
noncomputable def pdT0 (Ds Cr : ℕ) (H B : ℝ) : ℝ :=
  12 * Cr * pdA0 Ds H ^ Cr * (1 + 6 * Cr) ^ Cr * pdEs Ds H * Real.exp B + 1

/-- Height budget used to construct the predictor catalog. -/
noncomputable def pdH0 (Ds Cr : ℕ) (H B : ℝ) : ℝ :=
  max ((pdEs Ds H * pdT0 Ds Cr H B) ^ 6) (bandLip + 1)

/-- Integer accuracy level used in the predictor tail cutoff. -/
noncomputable def pdM0 (Ds Cr : ℕ) (H B : ℝ) : ℕ :=
  ⌈2 * (B + Real.log (3 * pdEs Ds H * Cr * (2 + Real.log (pdH0 Ds Cr H B)) ^ Cr + 1))⌉₊

/-- Combined logarithmic height and accuracy parameter for the predictor catalog. -/
noncomputable def pdLE (Ds Cr : ℕ) (H B : ℝ) : ℝ :=
  2 + Real.log (pdH0 Ds Cr H B) + pdM0 Ds Cr H B

/-- Exponential predictor coefficient budget. -/
noncomputable def pdE (Dc Ds Cr : ℕ) (H B : ℝ) : ℝ := Real.exp (Dc * pdLE Ds Cr H B ^ Dc)

/-- Exponential higher-order coefficient-tail budget for the predictor catalog. -/
noncomputable def pdE1 (J1 Ds Cr : ℕ) (H B : ℝ) : ℝ := Real.exp (J1 * pdLE Ds Cr H B ^ J1)

/-- Dyadic truncation depth sufficient for the predictor coefficient tail. -/
noncomputable def pdK0 (κ : LocalKernelClass) (d' Dc J1 Ds Cr : ℕ) (H B : ℝ) : ℕ :=
  ⌈Real.logb 2 (12 * pdEs Ds H * (pdE Dc Ds Cr H B + 1) * pdE1 J1 Ds Cr H B *
    (tailCT κ d' (pdE Dc Ds Cr H B) + 1) * 2 * 7 ^ (d' + d') * (2 * Real.pi) ^ ((d' + 1) ^ 2) *
    Real.exp B)⌉₊

section PredictorBudget
variable {Ds Cr : ℕ} {H B : ℝ}

theorem pdX_nonneg (hH : 1 ≤ H) : 0 ≤ pdX H := by
  unfold pdX; have := Real.log_nonneg hH; linarith

theorem one_le_pdEs (hH : 1 ≤ H) : 1 ≤ pdEs Ds H := by
  unfold pdEs; have := pdX_nonneg hH; exact Real.one_le_exp (by positivity)

theorem one_le_pdA0 (hH : 1 ≤ H) : 1 ≤ pdA0 Ds H := by
  unfold pdA0; have := pdX_nonneg hH
  have : 0 ≤ (Ds : ℝ) * pdX H ^ Ds := by positivity
  linarith

theorem one_le_pdT0 (hH : 1 ≤ H) : 1 ≤ pdT0 Ds Cr H B := by
  unfold pdT0
  have := one_le_pdEs (Ds := Ds) hH
  have := one_le_pdA0 (Ds := Ds) hH
  have : 0 ≤ 12 * (Cr : ℝ) * pdA0 Ds H ^ Cr * (1 + 6 * Cr) ^ Cr * pdEs Ds H * Real.exp B := by
    positivity
  linarith

theorem one_le_pdH0 : 1 ≤ pdH0 Ds Cr H B := by
  unfold pdH0
  have := bandLip_spec.1
  exact le_trans (by linarith) (le_max_right _ _)

/-- The shell budget: the size-weighted tail beyond `T₀` costs at most `e^{-B}/3`. -/
theorem pd_shell_budget (hH : 1 ≤ H) :
    Cr * pdA0 Ds H ^ Cr * (1 + 6 * Cr) ^ Cr * (4 * pdEs Ds H / pdT0 Ds Cr H B ^ 99) ≤
      Real.exp (-B) / 3 := by
  have hT := one_le_pdT0 (Ds := Ds) (Cr := Cr) (B := B) hH
  have hEs := one_le_pdEs (Ds := Ds) hH
  have hA := one_le_pdA0 (Ds := Ds) hH
  set c := (Cr : ℝ) * pdA0 Ds H ^ Cr * (1 + 6 * Cr) ^ Cr with hc
  have hc0 : 0 ≤ c := by positivity
  have hT99 : pdT0 Ds Cr H B ≤ pdT0 Ds Cr H B ^ 99 := le_self_pow₀ hT (by norm_num)
  have hTdef : 12 * c * pdEs Ds H * Real.exp B ≤ pdT0 Ds Cr H B := by
    unfold pdT0; rw [hc]; linarith
  have hem : Real.exp (-B) * Real.exp B = 1 := by rw [← Real.exp_add]; simp
  have hTpos : 0 < pdT0 Ds Cr H B := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : c * (4 * pdEs Ds H) * 3 ≤ Real.exp (-B) * pdT0 Ds Cr H B := by
    have := mul_le_mul_of_nonneg_left hTdef (Real.exp_pos (-B)).le
    calc c * (4 * pdEs Ds H) * 3 = Real.exp (-B) * (12 * c * pdEs Ds H * Real.exp B) := by
          rw [show Real.exp (-B) * (12 * c * pdEs Ds H * Real.exp B) =
            12 * c * pdEs Ds H * (Real.exp (-B) * Real.exp B) by ring, hem]; ring
      _ ≤ _ := this
  calc c * (4 * pdEs Ds H) * 3 ≤ Real.exp (-B) * pdT0 Ds Cr H B := h1
    _ ≤ Real.exp (-B) * pdT0 Ds Cr H B ^ 99 :=
        mul_le_mul_of_nonneg_left hT99 (Real.exp_pos _).le

/-- The band budget: discarding the bands `m > M₀` costs at most `e^{-B}/3`. -/
theorem pd_band_budget (hH : 1 ≤ H) :
    pdEs Ds H * (Real.exp (-(pdM0 Ds Cr H B : ℝ) / 2) *
      (Cr * (2 + Real.log (pdH0 Ds Cr H B)) ^ Cr)) ≤ Real.exp (-B) / 3 := by
  have hEs := one_le_pdEs (Ds := Ds) hH
  have hH0 := one_le_pdH0 (Ds := Ds) (Cr := Cr) (H := H) (B := B)
  have hl : 0 ≤ Real.log (pdH0 Ds Cr H B) := Real.log_nonneg hH0
  set Z := 3 * pdEs Ds H * Cr * (2 + Real.log (pdH0 Ds Cr H B)) ^ Cr with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have hM : 2 * (B + Real.log (Z + 1)) ≤ (pdM0 Ds Cr H B : ℝ) := by
    unfold pdM0; rw [← hZ]; exact Nat.le_ceil _
  have hexp : Real.exp (-(pdM0 Ds Cr H B : ℝ) / 2) ≤ Real.exp (-B) / (Z + 1) := by
    have e : Real.exp (-B) / (Z + 1) = Real.exp (-B - Real.log (Z + 1)) := by
      rw [Real.exp_sub, Real.exp_log (by linarith)]
    rw [e]
    apply Real.exp_le_exp.mpr
    linarith
  have hgoal : pdEs Ds H * (Cr * (2 + Real.log (pdH0 Ds Cr H B)) ^ Cr) = Z / 3 := by
    rw [hZ]; ring
  calc pdEs Ds H * (Real.exp (-(pdM0 Ds Cr H B : ℝ) / 2) *
        (Cr * (2 + Real.log (pdH0 Ds Cr H B)) ^ Cr))
      = Real.exp (-(pdM0 Ds Cr H B : ℝ) / 2) * (Z / 3) := by rw [← hgoal]; ring
    _ ≤ Real.exp (-B) / (Z + 1) * (Z / 3) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (-B) / 3 := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by norm_num)]
        have := Real.exp_pos (-B)
        nlinarith only [this]

end PredictorBudget

theorem one_le_pdE (Dc Ds Cr : ℕ) (H B : ℝ) : 1 ≤ pdE Dc Ds Cr H B := by
  unfold pdE pdLE
  have h1 := one_le_pdH0 (Ds := Ds) (Cr := Cr) (H := H) (B := B)
  have := Real.log_nonneg h1
  exact Real.one_le_exp (by positivity)

/-- The catalog budget: the pooled catalog tails cost at most `e^{-B}/3`. -/
theorem pd_catalog_budget (κ : LocalKernelClass) (d' Dc J1 Ds Cr : ℕ) {H B : ℝ} (hH : 1 ≤ H) :
    4 * pdEs Ds H * ((⌊pdE Dc Ds Cr H B⌋₊ : ℝ) * (pdE1 J1 Ds Cr H B *
      tailCT κ d' (pdE Dc Ds Cr H B) *
      (2 * 7 ^ (d' + d') * (2 * Real.pi) ^ ((d' + 1) ^ 2 - 1) /
        2 ^ pdK0 κ d' Dc J1 Ds Cr H B))) ≤ Real.exp (-B) / 3 := by
  have hEs := one_le_pdEs (Ds := Ds) hH
  have hE := one_le_pdE Dc Ds Cr H B
  have hE1 : 0 < pdE1 J1 Ds Cr H B := Real.exp_pos _
  have hCT := tailCT_nonneg κ d' hE
  have hfl : (⌊pdE Dc Ds Cr H B⌋₊ : ℝ) ≤ pdE Dc Ds Cr H B + 1 := by
    have := Nat.floor_le (show 0 ≤ pdE Dc Ds Cr H B by linarith); linarith
  set Z := 12 * pdEs Ds H * (pdE Dc Ds Cr H B + 1) * pdE1 J1 Ds Cr H B *
    (tailCT κ d' (pdE Dc Ds Cr H B) + 1) * 2 * 7 ^ (d' + d') * (2 * Real.pi) ^ ((d' + 1) ^ 2) *
    Real.exp B with hZ
  have hZ0 : 0 < Z := by rw [hZ]; positivity
  have hK : Z ≤ (2 : ℝ) ^ pdK0 κ d' Dc J1 Ds Cr H B := two_pow_ceil_logb_ge hZ0
  have hpi : (2 * Real.pi) ^ ((d' + 1) ^ 2 - 1) ≤ (2 * Real.pi) ^ ((d' + 1) ^ 2) :=
    pow_le_pow_right₀ (by nlinarith only [Real.pi_gt_three]) (Nat.sub_le _ _)
  have hnum : 4 * pdEs Ds H * ((⌊pdE Dc Ds Cr H B⌋₊ : ℝ) * (pdE1 J1 Ds Cr H B *
      tailCT κ d' (pdE Dc Ds Cr H B) * (2 * 7 ^ (d' + d') * (2 * Real.pi) ^ ((d' + 1) ^ 2 - 1)))) ≤
      4 * pdEs Ds H * ((pdE Dc Ds Cr H B + 1) * (pdE1 J1 Ds Cr H B *
      (tailCT κ d' (pdE Dc Ds Cr H B) + 1) * (2 * 7 ^ (d' + d') *
        (2 * Real.pi) ^ ((d' + 1) ^ 2)))) := by
    gcongr; linarith
  have hem : Real.exp (-B) * Real.exp B = 1 := by rw [← Real.exp_add]; simp
  calc 4 * pdEs Ds H * ((⌊pdE Dc Ds Cr H B⌋₊ : ℝ) * (pdE1 J1 Ds Cr H B *
        tailCT κ d' (pdE Dc Ds Cr H B) *
        (2 * 7 ^ (d' + d') * (2 * Real.pi) ^ ((d' + 1) ^ 2 - 1) /
          2 ^ pdK0 κ d' Dc J1 Ds Cr H B)))
      = 4 * pdEs Ds H * ((⌊pdE Dc Ds Cr H B⌋₊ : ℝ) * (pdE1 J1 Ds Cr H B *
        tailCT κ d' (pdE Dc Ds Cr H B) * (2 * 7 ^ (d' + d') *
          (2 * Real.pi) ^ ((d' + 1) ^ 2 - 1)))) / 2 ^ pdK0 κ d' Dc J1 Ds Cr H B := by ring
    _ ≤ 4 * pdEs Ds H * ((pdE Dc Ds Cr H B + 1) * (pdE1 J1 Ds Cr H B *
        (tailCT κ d' (pdE Dc Ds Cr H B) + 1) * (2 * 7 ^ (d' + d') *
          (2 * Real.pi) ^ ((d' + 1) ^ 2)))) / Z := div_le_div₀ (by positivity) hnum hZ0 hK
    _ = Real.exp (-B) / 3 := by
        rw [hZ, div_eq_iff (by positivity)]
        have hem' : Real.exp B * Real.exp (-B) = 1 := by rw [mul_comm]; exact hem
        field_simp
        nlinarith only [hem', Real.exp_pos B]

/-- The cell-summed form of `predictor_cell_bound`. -/
theorem predictor_sum_bound {τ π : Type*} [Countable τ] [Countable π] [DecidableEq τ]
    [DecidableEq π] (S : Finset (ℤ × ℤ)) (len : ℤ × ℤ → ℝ) (hlen : ∀ I, 0 ≤ len I)
    (cf : τ → ℂ) (hcs : Summable (fun q => ‖cf q‖)) (LF : ℤ × ℤ → ℂ) (sepQ : ℤ × ℤ → τ → ℂ)
    (MQ : ℤ × ℤ → ℝ) (hsepQ : ∀ I ∈ S, ∀ q, ‖sepQ I q‖ ≤ MQ I)
    (hLF : ∀ I ∈ S, HasSum (fun q => cf q * sepQ I q) (LF I))
    (R : Finset τ) (ret : τ → ℤ × ℤ → Prop) [∀ q I, Decidable (ret q I)] (P : Finset π)
    (coeff : ℤ × ℤ → τ → π → ℂ) (sepP : ℤ × ℤ → τ → π → ℂ)
    (hcoeff : ∀ I q, Summable (fun p => ‖coeff I q p‖)) (MP : ℤ × ℤ → ℝ)
    (hsepP : ∀ I ∈ S, ∀ q p, ‖sepP I q p‖ ≤ MP I)
    (hexp : ∀ I ∈ S, ∀ q ∈ R, ret q I → HasSum (fun p => coeff I q p * sepP I q p)
      (sepQ I q / 4)) :
    ∑ I ∈ S, len I * ‖LF I - ∑ q ∈ R, (if ret q I then
        4 * cf q * ∑ p ∈ P, coeff I q p * sepP I q p else 0)‖ ≤
      (∑' q, if q ∈ R then 0 else ‖cf q‖ * ∑ I ∈ S, len I * ‖sepQ I q‖) +
      ∑ q ∈ R, ‖cf q‖ * ∑ I ∈ S.filter (fun I => ¬ ret q I), len I * ‖sepQ I q‖ +
      ∑ q ∈ R, 4 * ‖cf q‖ * ∑ I ∈ S.filter (fun I => ret q I), len I *
        ∑' p, (if p ∈ P then 0 else ‖coeff I q p‖ * ‖sepP I q p‖) := by
  classical
  have hcell : ∀ I ∈ S, len I * ‖LF I - ∑ q ∈ R, (if ret q I then
      4 * cf q * ∑ p ∈ P, coeff I q p * sepP I q p else 0)‖ ≤
      len I * ((∑' q, if q ∈ R then 0 else ‖cf q‖ * ‖sepQ I q‖) +
      ∑ q ∈ R, (if ret q I then 0 else ‖cf q‖ * ‖sepQ I q‖) +
      ∑ q ∈ R, (if ret q I then 4 * ‖cf q‖ *
        ∑' p, (if p ∈ P then 0 else ‖coeff I q p‖ * ‖sepP I q p‖) else 0)) := by
    intro I hI
    exact mul_le_mul_of_nonneg_left (predictor_cell_bound cf hcs (sepQ I) (hsepQ I hI)
      (hLF I hI) R (fun q => ret q I) P (coeff I) (sepP I) (hcoeff I) (hsepP I hI)
      (fun q hq hr => hexp I hI q hq hr)) (hlen I)
  refine (Finset.sum_le_sum hcell).trans (le_of_eq ?_)
  simp only [mul_add, Finset.sum_add_distrib]
  refine congr (congrArg HAdd.hAdd (congr (congrArg HAdd.hAdd ?_) ?_)) ?_
  · -- the discarded shells: swap the finite and the infinite sums
    have hsum : ∀ I ∈ S, Summable (fun q => if q ∈ R then 0 else ‖cf q‖ * ‖sepQ I q‖) := by
      intro I hI
      refine Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity) (fun q => ?_)
        (hcs.mul_right (MQ I))
      split_ifs
      · exact mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hsepQ I hI q))
      · exact mul_le_mul_of_nonneg_left (hsepQ I hI q) (norm_nonneg _)
    rw [Finset.sum_congr rfl (fun I hI => (tsum_mul_left).symm), ← Summable.tsum_finsetSum
      (fun I hI => (hsum I hI).mul_left (len I))]
    congr 1; funext q
    split_ifs
    · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> ring
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> ring

theorem separatedLocalForm_smul_right (r : ℝ) (w : ℝ × ℝ → ℂ) (Q : ℝ → ℂ) (a b : Fin 4)
    (Fa Fb : ℝ → ℂ) (c : ℂ) :
    separatedLocalForm r w Q a b Fa (fun y => c * Fb y) =
      c * separatedLocalForm r w Q a b Fa Fb := by
  unfold separatedLocalForm
  rw [mul_left_comm, ← integral_const_mul c]
  congr 1; congr 1; funext z; ring

/-- The atom-pair expansion of the local form at one cell, for arbitrary cell-local `L²`
inputs in the remaining slots, with a uniform bound of the separated forms. -/
theorem pair_expansion_cell {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {a i k b : Fin 4}
    (hai : a ≠ i) (hak : a ≠ k) (hab : a ≠ b) (hik : i ≠ k) (hib : i ≠ b) (hkb : k ≠ b)
    {R v φ φ' : ℝ → ℂ} (hRm : Measurable R) (hvm : Measurable v)
    (hR2 : MemLp R 2 (volume.restrict (Set.Ico a₀ (a₀ + r))))
    (hv2 : MemLp v 2 (volume.restrict (Set.Ico a₀ (a₀ + r))))
    {τ : Type*} [Countable τ] (cf : τ → ℂ) (ψa ψb Q : τ → ℝ → ℂ)
    (hψam : ∀ q, Measurable (ψa q)) (hψbm : ∀ q, Measurable (ψb q)) (hQm : ∀ q, Measurable (Q q))
    (hψab : ∀ q y, ‖ψa q y‖ ≤ 1) (hψbb : ∀ q y, ‖ψb q y‖ ≤ 1) (hQb : ∀ q y, ‖Q q y‖ ≤ 1)
    (hcs : Summable (fun q => ‖cf q‖))
    (hexp : ∀ x t : ℝ, HasSum (fun q => cf q * ψa q (x + (a : ℝ) * t) *
      ψb q (x + (b : ℝ) * t) * Q q t) (φ (x + (i : ℝ) * t) * φ' (x + (k : ℝ) * t)))
    (f : Fin 4 → ℝ → ℂ) (hfa : f a = R) (hfi : f i = φ) (hfk : f k = φ') (hfb : f b = v) :
    ∃ M : ℝ, HasSum (fun q => cf q * separatedLocalForm r w (Q q) a b
        (fun y => ψa q y * R y) (fun y => ψb q y * v y)) (localProgressionForm r w f) ∧
      ∀ q, ‖separatedLocalForm r w (Q q) a b (fun y => ψa q y * R y)
        (fun y => ψb q y * v y)‖ ≤ M := by
  classical
  set! cv : ℝ := max 1 (eLpNorm v 2 (normalizedIntervalMeasure a₀ r)).toReal with hcv
  have hcv1 : 1 ≤ cv := le_max_left _ _
  have hcv0 : 0 < cv := by linarith
  set! v' : ℝ → ℂ := fun y => ((cv⁻¹ : ℝ) : ℂ) * v y with hv'
  have hv'm : Measurable v' := measurable_const.mul hvm
  have hv'n : eLpNorm v' 2 (normalizedIntervalMeasure a₀ r) ≤ 1 := by
    have hne := eLpNorm_normalized_ne_top hv2
    have h := eLpNorm_const_smul (μ := normalizedIntervalMeasure a₀ r) (p := 2)
      ((cv⁻¹ : ℝ) : ℂ) v
    have he : v' = ((cv⁻¹ : ℝ) : ℂ) • v := by funext y; simp [hv']
    rw [he, h]
    rw [show ‖((cv⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal cv⁻¹ by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]]
    rw [← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_one.mpr
    rw [inv_mul_le_iff₀ hcv0, mul_one]
    exact le_max_right _ _
  set! C₁ := (eLpNorm R 2 (normalizedIntervalMeasure a₀ r)).toReal with hC₁
  have hC₁0 : 0 ≤ C₁ := ENNReal.toReal_nonneg
  have hRn : eLpNorm R 2 (normalizedIntervalMeasure a₀ r) ≤ ENNReal.ofReal C₁ :=
    eLpNorm_normalized_le_toReal hR2
  set! f' := Function.update f b v' with hf'
  have hf'a : f' a = R := by rw [hf', Function.update_of_ne hab]; exact hfa
  have hf'i : f' i = φ := by rw [hf', Function.update_of_ne hib]; exact hfi
  have hf'k : f' k = φ' := by rw [hf', Function.update_of_ne hkb]; exact hfk
  have hf'b : f' b = v' := by rw [hf', Function.update_self]
  obtain ⟨hHS, hXb⟩ := localProgressionForm_pair_expansion hr hw hai hak hab hik hib hkb
    hRm hv'm hC₁0 hRn hv'n cf ψa ψb Q hψam hψbm hQm hψab hψbb hQb hcs hexp f' hf'a hf'i hf'k
    hf'b
  -- undo the normalization of `v`
  have hLF : localProgressionForm r w f' = ((cv⁻¹ : ℝ) : ℂ) * localProgressionForm r w f := by
    have h := localProgressionForm_update_const_smul r w f b ((cv⁻¹ : ℝ) : ℂ) v
    have e1 : Function.update f b (((cv⁻¹ : ℝ) : ℂ) • v) = f' := by
      rw [hf']; congr 1
    have e2 : Function.update f b v = f := by
      rw [← hfb, Function.update_eq_self]
    rw [e1, e2] at h
    exact h
  have hsep : ∀ q, separatedLocalForm r w (Q q) a b (fun y => R y * ψa q y)
      (fun y => v' y * ψb q y) = ((cv⁻¹ : ℝ) : ℂ) *
        separatedLocalForm r w (Q q) a b (fun y => ψa q y * R y) (fun y => ψb q y * v y) := by
    intro q
    rw [← separatedLocalForm_smul_right]
    congr 1
    · funext y; ring
    · funext y; simp only [hv']; ring
  refine ⟨cv * (localFormUniformConstant κ * C₁), ?_, fun q => ?_⟩
  · have h2 := hHS.mul_left ((cv : ℝ) : ℂ)
    rw [hLF] at h2
    have hc : ((cv : ℝ) : ℂ) * (((cv⁻¹ : ℝ) : ℂ) * localProgressionForm r w f) =
        localProgressionForm r w f := by
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hcv0.ne', Complex.ofReal_one,
        one_mul]
    rw [hc] at h2
    convert h2 using 1
    funext q
    have hcvC : ((cv : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcv0.ne'
    rw [hsep q, Complex.ofReal_inv]
    field_simp
  · have h := hXb q
    rw [hsep q, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    rw [← le_div_iff₀' (by positivity : (0 : ℝ) < cv⁻¹)] at h
    calc ‖separatedLocalForm r w (Q q) a b (fun y => ψa q y * R y) (fun y => ψb q y * v y)‖
        ≤ localFormUniformConstant κ * C₁ / cv⁻¹ := h
      _ = cv * (localFormUniformConstant κ * C₁) := by field_simp

/-- A uniform bound of separated forms with bounded time factor and bounded multipliers. -/
theorem separatedLocalForm_bounded_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r)
    {w : ℝ × ℝ → ℂ} (hw : IsAdmissibleLocalKernel κ a₀ r w) {a b : Fin 4} (hab : a ≠ b)
    {K : ℝ → ℂ} (hK : ∀ t, ‖K t‖ ≤ 1) {ψa ψb za zb : ℝ → ℂ} (hψam : Measurable ψa)
    (hψbm : Measurable ψb) (hψa : ∀ y, ‖ψa y‖ ≤ 1) (hψb : ∀ y, ‖ψb y‖ ≤ 1)
    (hzam : Measurable za) (hzbm : Measurable zb)
    (hza : MemLp za 2 (volume.restrict (Set.Ico a₀ (a₀ + r))))
    (hzb : MemLp zb 2 (volume.restrict (Set.Ico a₀ (a₀ + r)))) :
    ‖separatedLocalForm r w K a b (fun y => ψa y * za y) (fun y => ψb y * zb y)‖ ≤
      localKernelSupBound κ * Real.sqrt (r⁻¹ * ∫ y in Set.Ico a₀ (a₀ + r), ‖za y‖ ^ 2) *
        Real.sqrt (r⁻¹ * ∫ y in Set.Ico a₀ (a₀ + r), ‖zb y‖ ^ 2) := by
  have h := separatedLocalForm_sup_le hr hw hab zero_le_one (fun t _ => hK t)
    (hψam.mul hzam) (hψbm.mul hzbm) (memLp_mul_bounded_restrict hψam hψa hza)
    (memLp_mul_bounded_restrict hψbm hψb hzb)
  refine h.trans ?_
  rw [mul_one]
  have hC := localKernelSupBound_nonneg κ
  have hr' : 0 ≤ r⁻¹ := by positivity
  have ha := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (setIntegral_mul_bounded_le hψa hza) hr')
  have hb := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (setIntegral_mul_bounded_le hψb hzb) hr')
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha hC) hb (Real.sqrt_nonneg _) (by positivity)

theorem pd_shell_log (Ds : ℕ) {H s : ℝ} (hs : 1 ≤ s) :
    2 + Real.log ((pdEs Ds H * s) ^ 6) = pdA0 Ds H + 6 * Real.log s := by
  rw [Real.log_pow, pdEs, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, pdA0]
  push_cast; ring

/-- The size bound of the predictor list. -/
noncomputable def pdCard (κ : LocalKernelClass) (d' Dc J1 Ds Cr : ℕ) (H B : ℝ) : ℝ :=
  Real.exp (10 * pdX H ^ 2) * (3 * pdT0 Ds Cr H B) ^ (3 * d') *
    (3 * (⌊pdE Dc Ds Cr H B⌋₊ : ℝ) ^ 2) ^ (d' * d') *
    (3 * (⌊pdE Dc Ds Cr H B * 2 ^ pdK0 κ d' Dc J1 Ds Cr H B⌋₊ : ℝ) ^ 2) ^ d'



end TrilinearHT.Auto
end
