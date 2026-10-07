/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCGaussianSeries

/-!
# Integral flatness from Gaussian boxes

Uniform Gaussian decay on nearby boxes yields vanishing of every integral
order at their common spatial center.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Uniform Gaussian decay over all sufficiently small nearby boxes yields
integral vanishing of every order at their common spatial center. -/
theorem uc_box_decay_implies_integral_flatness
    (F : Finset Vec3)
    (hF : ∀ y ∈ closure (vec3Ball 0 1),
      ∃ c ∈ F, y ∈ vec3Ball c (1 / 2))
    (hFpos : 0 < F.card)
    (x : Vec3) (R T δ A b : ℝ)
    (hδ : 0 < δ)
    (hA : 0 ≤ A) (hb : 0 < b)
    (w : ParabolicPoint → Vec3)
    (hlocalInt : ∀ r : ℝ, 0 < r → r < δ →
      IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
        (spaceTimeSet (vec3Ball x r) (Ioo 0 (r ^ 2))) volume)
    (hslabInt : ∀ r : ℝ, 0 < r → r < δ → ∀ n : ℕ,
      IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
        (spaceTimeSet (vec3Ball x r)
          (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
            (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) volume)
    (hboxInt : ∀ r : ℝ, 0 < r → r < δ → ∀ n : ℕ,
      ∀ c ∈ vec3Ball x (2 * r),
      IntegrableOn (fun z => vec3EuclideanNorm (w z) ^ 2)
        (spaceTimeSet
          (vec3Ball c (Real.sqrt
            (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
          (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
            (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) volume)
    (hbox : ∀ r : ℝ, 0 < r → r < δ → ∀ n : ℕ,
      ∀ c ∈ vec3Ball x (2 * r),
      (∫ z in spaceTimeSet
        (vec3Ball c (Real.sqrt
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))),
        vec3EuclideanNorm (w z) ^ 2) ≤
          A * Real.exp (-(b /
            ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) :
    UCIntegralFlatness x R T w := by
  intro m
  let K : ℝ := F.card
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hFpos
  obtain ⟨N, hNm, hq⟩ := uc_geometric_gaussian_order K hK m
  have hN : 0 < N := by omega
  let q : ℝ := K * (3 / 4 : ℝ) ^ N
  let D : ℝ := K * (((N : ℝ) * (3 / 5) / b) ^ N) *
    (1 - q)⁻¹
  have hD : 0 ≤ D := by
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hq1 : q < 1 := hq
    dsimp [D]
    positivity
  let C : ℝ := 1 + A * D
  have hC : 0 < C := by dsimp [C]; positivity
  let r₀ : ℝ := min δ 1
  have hr₀ : 0 < r₀ := lt_min hδ (by norm_num)
  refine ⟨C, r₀, hC, hr₀, ?_⟩
  intro r hr hrbound
  have hrsmall : r < δ := by
    have h := lt_of_lt_of_le hrbound (min_le_right _ _)
    have h' := h.trans_le (min_le_right _ _)
    exact h'.trans_le (min_le_left _ _)
  have hrone : r ≤ 1 := by
    have h := lt_of_lt_of_le hrbound (min_le_right _ _)
    have h' := h.trans_le (min_le_right _ _)
    exact (h'.trans_le (min_le_right _ _)).le
  let g : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (w z) ^ 2
  let S : Set ParabolicPoint := spaceTimeSet (vec3Ball x r) (Ioo 0 (r ^ 2))
  let Sₙ (n : ℕ) : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball x r)
      (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
        (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))
  let term (n : ℕ) : ℝ := K ^ (n + 1) *
    Real.exp (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))
  have hseries := uc_geometric_gaussian_series_le K b r N hK.le hb hr hN hq
  have hseriesSummable : Summable term := hseries.1
  have hseriesBound : (∑' n, term n) ≤ D * r ^ (2 * N) := by
    calc
      _ ≤ K * (((N : ℝ) * (3 / 5) / b) ^ N) * r ^ (2 * N) *
          (1 - K * (3 / 4 : ℝ) ^ N)⁻¹ := hseries.2
      _ = _ := by dsimp [D, q]; ring
  have hslab (n : ℕ) : (∫ z in Sₙ n, g z) ≤ A * term n := by
    have h := uc_geometric_slab_integral_le F hF x r hr n g
      (fun z => sq_nonneg _) _
      (mul_nonneg hA (Real.exp_pos _).le)
      (hslabInt r hr hrsmall n)
      (hboxInt r hr hrsmall n)
      (hbox r hr hrsmall n)
    change (∫ z in Sₙ n, g z) ≤
      K ^ (n + 1) * (A * Real.exp
        (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) at h
    dsimp [term]
    calc
      _ ≤ K ^ (n + 1) * (A * Real.exp
        (-(b / ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) := h
      _ = _ := by ring
  have hslab0 (n : ℕ) : 0 ≤ ∫ z in Sₙ n, g z :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _))
  have hscaledSummable : Summable (fun n => A * term n) :=
    hseriesSummable.mul_left A
  have hslabSummable : Summable (fun n => ∫ z in Sₙ n, g z) :=
    Summable.of_nonneg_of_le hslab0 hslab hscaledSummable
  have hcover : S ⊆ ⋃ n, Sₙ n :=
    uc_geometric_slabs_cover x r hr
  have htotal := uc_integral_le_tsum_of_cover g
    (fun z => sq_nonneg _) S Sₙ hcover
    (hlocalInt r hr hrsmall) (hslabInt r hr hrsmall) hslabSummable
  have hsum : (∑' n, ∫ z in Sₙ n, g z) ≤ A * D * r ^ (2 * N) := by
    calc
      _ ≤ ∑' n, A * term n :=
        hslabSummable.tsum_le_tsum hslab hscaledSummable
      _ = A * ∑' n, term n := tsum_mul_left
      _ ≤ A * (D * r ^ (2 * N)) :=
        mul_le_mul_of_nonneg_left hseriesBound hA
      _ = _ := by ring
  have hpow : r ^ (2 * N) ≤ r ^ m := by
    have hmN : m ≤ 2 * N := by omega
    exact pow_le_pow_of_le_one hr.le hrone hmN
  have hcoef : 0 ≤ A * D := mul_nonneg hA hD
  have hfinal : (∫ z in S, g z) ≤ C * r ^ m := by
    calc
      _ ≤ A * D * r ^ (2 * N) := htotal.trans hsum
      _ ≤ A * D * r ^ m :=
        mul_le_mul_of_nonneg_left hpow hcoef
      _ ≤ C * r ^ m := by
        dsimp [C]
        have hrpow : 0 ≤ r ^ m := pow_nonneg hr.le _
        nlinarith only [hrpow]
  exact hfinal

end ESS
