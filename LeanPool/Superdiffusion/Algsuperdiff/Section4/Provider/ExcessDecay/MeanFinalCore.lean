/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.MeanFinalPointwise

/-!
# MeanFinalCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `(A)`, step 2: the doubled-window transfer for a face-odd function

```text
  ⨍_D G² ≤ 3 ⨍_K G² + 8β² ,   hence   ‖G‖_{L²(D)} ≤ 2‖G‖_{L²(K)} + 3|β| .
```

The `β`-term is unavoidable and is the reason the final assembly of `(A)` is an
*absorption*: `G` is not odd, only `W` is, and `G ∘ ρ = −(G + 2β)`.  In the
assembly this term is multiplied by the quadratically small Hessian factor, so
it is absorbed rather than iterated.

The proof is a measure-preserving change of variables (`ρ` is an involutive
measurable embedding preserving Lebesgue measure) plus the observation that the
face hyperplane is null.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory
open HCPolySupport (Vec coordFaceReflection volumeAverage)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The face hyperplane is null -/

/-- A coordinate hyperplane has Lebesgue measure zero. -/
theorem volume_coordHyperplane_eq_zero (i : Fin d) (a : ℝ) :
    volume {y : Vec d | y i = a} = 0 := by
  classical
  have hset : {y : Vec d | y i = a}
      = Set.univ.pi (fun j : Fin d => if j = i then ({a} : Set ℝ) else Set.univ) := by
    ext y
    constructor
    · intro hy j _
      by_cases hj : j = i
      · subst hj
        simpa using hy
      · simp [hj]
    · intro hy
      have hi := hy i (Set.mem_univ i)
      simpa using hi
  rw [hset, volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

/-! ## 2. The doubled-window transfer -/

/-- **The oscillation on the doubled window, transferred back to the cube.**

For `W` odd about `{yᵢ = a}` and `D` covered — up to that hyperplane — by `K`
and the reflection of `K`, the normalized seminorm of `G = W − β` on `D` is
controlled by the one on `K` plus a multiple of `|β|`. -/
theorem normalizedL2On_doubled_le {i : Fin d} {a : ℝ} {K D : Set (Vec d)}
    {W : Vec d → ℝ} {beta : ℝ}
    (hodd : ∀ z, W (coordFaceReflection a i z) = -W z)
    (hKm : MeasurableSet K) (hDm : MeasurableSet D) (hKD : K ⊆ D)
    (hDsplit : ∀ y ∈ D, y ∈ K ∨ coordFaceReflection a i y ∈ K ∨ y i = a)
    (hKpos : 0 < (volume K).toReal) (hDpos : 0 < (volume D).toReal)
    (hKleD : (volume K).toReal ≤ (volume D).toReal)
    (hDtop : volume D ≠ ⊤)
    (hGD : MemLp (fun y => W y - beta) 2 (volume.restrict D)) :
    normalizedL2On D (fun y => W y - beta)
      ≤ 2 * normalizedL2On K (fun y => W y - beta) + 3 * |beta| := by
  classical
  set G : Vec d → ℝ := fun y => W y - beta with hGdef
  have : IsFiniteMeasure (volume.restrict D) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hDtop
  have hKtop : volume K ≠ ⊤ := ne_top_of_le_ne_top hDtop (measure_mono hKD)
  have : IsFiniteMeasure (volume.restrict K) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hKtop
  have hGK : MemLp G 2 (volume.restrict K) :=
    hGD.mono_measure (Measure.restrict_mono hKD le_rfl)
  have hintD : IntegrableOn (fun y => G y ^ 2) D volume := hGD.integrable_sq
  have hintK : IntegrableOn (fun y => G y ^ 2) K volume := hintD.mono_set hKD
  have hGKint : IntegrableOn G K volume := hGK.integrable one_le_two
  -- the reflected part of the doubled window
  set B : Set (Vec d) := D ∩ (coordFaceReflection a i ⁻¹' K) with hBdef
  have hrhomeas : Measurable (coordFaceReflection (d := d) a i) :=
    (HCPolySupport.measurableEmbedding_coordFaceReflection a i).measurable
  have hBm : MeasurableSet B := hDm.inter (hrhomeas hKm)
  have hBD : B ⊆ D := Set.inter_subset_left
  have hcover : D \ (K ∪ B) ⊆ {y : Vec d | y i = a} := by
    intro y hy
    rcases hDsplit y hy.1 with h | h | h
    · exact absurd (Or.inl h) hy.2
    · exact absurd (Or.inr ⟨hy.1, h⟩) hy.2
    · exact h
  have hDae : D =ᵐ[volume] (K ∪ B : Set (Vec d)) := by
    refine MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null hcover (volume_coordHyperplane_eq_zero i a)
    · have hsub : (K ∪ B) \ D = ∅ := by
        refine Set.eq_empty_of_forall_notMem ?_
        rintro y ⟨hy, hyD⟩
        rcases hy with hy | hy
        · exact hyD (hKD hy)
        · exact hyD hy.1
      rw [hsub, measure_empty]
  -- the split of the integral
  have hintB : IntegrableOn (fun y => G y ^ 2) B volume := hintD.mono_set hBD
  have hsplit : ∫ y in D, G y ^ 2 ≤ (∫ y in K, G y ^ 2) + ∫ y in B, G y ^ 2 := by
    have hcongr : ∫ y in D, G y ^ 2 = ∫ y in K ∪ B, G y ^ 2 :=
      MeasureTheory.setIntegral_congr_set hDae
    have hunion : K ∪ B = K ∪ (B \ K) := (Set.union_sdiff_self (s := K) (t := B)).symm
    have hintBK : IntegrableOn (fun y => G y ^ 2) (B \ K) volume :=
      hintB.mono_set Set.sdiff_subset
    have hadd : ∫ y in K ∪ (B \ K), G y ^ 2
        = (∫ y in K, G y ^ 2) + ∫ y in B \ K, G y ^ 2 :=
      MeasureTheory.setIntegral_union Set.disjoint_sdiff_right (hBm.diff hKm) hintK hintBK
    have hmono : ∫ y in B \ K, G y ^ 2 ≤ ∫ y in B, G y ^ 2 :=
      MeasureTheory.setIntegral_mono_set hintB
        (Filter.Eventually.of_forall fun y => sq_nonneg (G y))
        (LE.le.eventuallyLE Set.sdiff_subset)
    rw [hcongr, hunion, hadd]
    linarith only [hmono]
  -- the change of variables on the reflected part
  have hpreB : coordFaceReflection a i ⁻¹' B ⊆ K := by
    intro y hy
    have h2 : coordFaceReflection a i (coordFaceReflection a i y) ∈ K := hy.2
    rwa [HCPolySupport.coordFaceReflection_involutive] at h2
  have hcov := (HCPolySupport.measurePreserving_coordFaceReflection
      (d := d) a i).setIntegral_preimage_emb
    (HCPolySupport.measurableEmbedding_coordFaceReflection a i) (fun y => G y ^ 2) B
  have hGrho : ∀ x : Vec d, G (coordFaceReflection a i x) ^ 2 = (G x + 2 * beta) ^ 2 := by
    intro x
    have h := hodd x
    show (W (coordFaceReflection a i x) - beta) ^ 2 = (W x - beta + 2 * beta) ^ 2
    rw [h]
    ring
  have hintKshift : IntegrableOn (fun x => (G x + 2 * beta) ^ 2) K volume := by
    have hexp : (fun x => (G x + 2 * beta) ^ 2)
        = fun x => G x ^ 2 + (4 * beta * G x + 4 * beta ^ 2) := by
      funext x; ring
    rw [hexp]
    exact hintK.add ((hGKint.const_mul (4 * beta)).add
      (MeasureTheory.integrable_const (4 * beta ^ 2)))
  have hBint : ∫ y in B, G y ^ 2 ≤ ∫ x in K, (G x + 2 * beta) ^ 2 := by
    have h1 : ∫ x in coordFaceReflection a i ⁻¹' B, (G x + 2 * beta) ^ 2
        = ∫ y in B, G y ^ 2 := by
      rw [← hcov]
      exact MeasureTheory.setIntegral_congr_fun (hrhomeas hBm)
        (fun x _ => (hGrho x).symm)
    rw [← h1]
    exact MeasureTheory.setIntegral_mono_set hintKshift
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (LE.le.eventuallyLE hpreB)
  -- the pointwise expansion on `K`
  have hexpand : ∫ x in K, (G x + 2 * beta) ^ 2
      ≤ 2 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal := by
    have hdom : ∫ x in K, (G x + 2 * beta) ^ 2
        ≤ ∫ x in K, (2 * G x ^ 2 + 8 * beta ^ 2) := by
      refine MeasureTheory.setIntegral_mono_on hintKshift
        ((hintK.const_mul 2).add (MeasureTheory.integrable_const _)) hKm ?_
      intro x _
      have hsq := sq_nonneg (G x - 2 * beta)
      have hid : (2 * G x ^ 2 + 8 * beta ^ 2) - (G x + 2 * beta) ^ 2
          = (G x - 2 * beta) ^ 2 := by ring
      linarith only [hsq, hid]
    have hval : ∫ x in K, (2 * G x ^ 2 + 8 * beta ^ 2)
        = 2 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal := by
      rw [MeasureTheory.integral_add (hintK.const_mul 2)
        (MeasureTheory.integrable_const _), MeasureTheory.integral_const_mul,
        MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.measureReal_def]
      ring
    rw [hval] at hdom
    exact hdom
  -- the averages
  have hIK0 : 0 ≤ ∫ x in K, G x ^ 2 :=
    MeasureTheory.setIntegral_nonneg hKm fun x _ => sq_nonneg (G x)
  have hfinal : ∫ y in D, G y ^ 2
      ≤ 3 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal := by
    linarith only [hsplit, hBint, hexpand]
  have hnn : 0 ≤ 3 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal := by
    have h1 : 0 ≤ 8 * beta ^ 2 * (volume K).toReal :=
      mul_nonneg (by linarith only [sq_nonneg beta] : (0 : ℝ) ≤ 8 * beta ^ 2)
        ENNReal.toReal_nonneg
    linarith only [hIK0, h1]
  have hinvle : ((volume D).toReal)⁻¹ ≤ ((volume K).toReal)⁻¹ := by
    rw [inv_le_inv₀ hDpos hKpos]
    exact hKleD
  have havg : volumeAverage D (fun y => G y ^ 2)
      ≤ 3 * volumeAverage K (fun y => G y ^ 2) + 8 * beta ^ 2 := by
    have hA : ((volume D).toReal)⁻¹ * (∫ y in D, G y ^ 2)
        ≤ ((volume D).toReal)⁻¹ *
          (3 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal) :=
      mul_le_mul_of_nonneg_left hfinal (inv_nonneg.mpr ENNReal.toReal_nonneg)
    have hC : ((volume D).toReal)⁻¹ *
        (3 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal)
        ≤ ((volume K).toReal)⁻¹ *
          (3 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal) :=
      mul_le_mul_of_nonneg_right hinvle hnn
    have hrw : ((volume K).toReal)⁻¹ *
        (3 * (∫ x in K, G x ^ 2) + 8 * beta ^ 2 * (volume K).toReal)
        = 3 * (((volume K).toReal)⁻¹ * ∫ x in K, G x ^ 2) + 8 * beta ^ 2 := by
      field_simp
    have hstep : ((volume D).toReal)⁻¹ * (∫ y in D, G y ^ 2)
        ≤ 3 * (((volume K).toReal)⁻¹ * ∫ x in K, G x ^ 2) + 8 * beta ^ 2 := by
      rw [← hrw]
      linarith only [hA, hC]
    unfold volumeAverage
    exact hstep
  -- take square roots
  have hosc0 : 0 ≤ normalizedL2On K G := normalizedL2On_nonneg K G
  have hb0 : 0 ≤ |beta| := abs_nonneg beta
  have hM0 : (0 : ℝ) ≤ 2 * normalizedL2On K G + 3 * |beta| := by
    linarith only [hosc0, hb0]
  refine normalizedL2On_le_of_sq_le hM0 ?_
  have hoscsq : normalizedL2On K G ^ 2 = volumeAverage K (fun y => G y ^ 2) :=
    normalizedL2On_sq K G
  have hbsq : beta ^ 2 = |beta| ^ 2 := (sq_abs beta).symm
  have hcross : 0 ≤ normalizedL2On K G * |beta| := mul_nonneg hosc0 hb0
  have hexp2 : (2 * normalizedL2On K G + 3 * |beta|) ^ 2
      = 4 * volumeAverage K (fun y => G y ^ 2)
        + 12 * (normalizedL2On K G * |beta|) + 9 * |beta| ^ 2 := by
    rw [← hoscsq]; ring
  have hKavg0 : 0 ≤ volumeAverage K (fun y => G y ^ 2) := volumeAverage_sq_nonneg K G
  have hbsq0 : (0 : ℝ) ≤ |beta| ^ 2 := sq_nonneg _
  rw [hexp2]
  rw [hbsq] at havg
  linarith only [havg, hcross, hKavg0, hbsq0]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
