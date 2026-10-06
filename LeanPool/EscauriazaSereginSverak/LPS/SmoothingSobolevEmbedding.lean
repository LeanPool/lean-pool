/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticitySobolevSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus

/-!
# Whole-space Sobolev control for smoothing

The local smooth Sobolev inequality gives an `H² → L∞` bound for smooth
fields with square-integrable derivatives on all of `ℝ³`. The source
uses this bound when estimating the high-order transport tensor.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Applying two ordered derivative words in sequence is the derivative
indexed by their concatenation (eq:lps-Hm-energy). -/
theorem lps_wordDeriv_append_words (α β : List (Fin 3)) (f : Vec3 → ℝ) :
    wordDeriv β (wordDeriv α f) = wordDeriv (α ++ β) f := by
  induction α generalizing f with
  | nil => rfl
  | cons j α ih =>
      change wordDeriv β (wordDeriv α (spatialDeriv f j)) =
        wordDeriv (α ++ β) (spatialDeriv f j)
      exact ih (spatialDeriv f j)

/-- The whole-space H² norm bounds a smooth scalar field uniformly,
without a compact-support assumption (eq:lps-Hm-energy). -/
theorem lps_smooth_h2_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      MemLp f 2 volume →
      (∀ j : Fin 3, MemLp (spatialDeriv f j) 2 volume) →
      (∀ j k : Fin 3,
        MemLp (spatialDeriv (spatialDeriv f j) k) 2 volume) →
      ∀ x, |f x| ≤ C * Real.sqrt
        (sobolevNormSqOn 2 univ (fun α => wordDeriv α f)) := by
  obtain ⟨C₀, hC₀, hlocal⟩ := vorticitySobolevSmooth_sup
    (r := (1 : ℝ)) (R := (2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt (13 * C₀), Real.sqrt_nonneg _, ?_⟩
  intro f hf hf0 hf1 hf2 x
  let F : Vec3 → ℝ := fun y =>
    f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 +
      ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k y ^ 2
  have h0int : Integrable (fun y => f y ^ 2) volume := hf0.integrable_sq
  have h1int (j : Fin 3) :
      Integrable (fun y => spatialDeriv f j y ^ 2) volume :=
    (hf1 j).integrable_sq
  have h2int (j k : Fin 3) :
      Integrable (fun y => spatialDeriv (spatialDeriv f j) k y ^ 2) volume :=
    (hf2 j k).integrable_sq
  have hsum1int :
      Integrable (fun y => ∑ j : Fin 3, spatialDeriv f j y ^ 2) volume :=
    integrable_finsetSum _ fun j _ => h1int j
  have hsum2int :
      Integrable (fun y => ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k y ^ 2) volume :=
    integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => h2int j k
  have hFint : Integrable F volume :=
    (h0int.add hsum1int).add hsum2int
  have hFnn (y : Vec3) : 0 ≤ F y := by
    dsimp [F]
    positivity
  have hball : ∫ y in vec3Ball x 2, F y ≤ ∫ y, F y :=
    setIntegral_le_integral hFint (ae_of_all volume hFnn)
  let N : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  have hNnn : 0 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun y => sq_nonneg _
  have hsingle (α : List (Fin 3)) (hα : α.length ≤ 2) :
      ∫ y, wordDeriv α f y ^ 2 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    simp only [Measure.restrict_univ]
    exact Finset.single_le_sum
      (f := fun β : List (Fin 3) => ∫ y, wordDeriv β f y ^ 2)
      (s := sobolevWords 2)
      (fun β _ => integral_nonneg fun y => sq_nonneg (wordDeriv β f y))
      (mem_sobolevWords.mpr hα)
  have h0 : ∫ y, f y ^ 2 ≤ N := hsingle [] (by norm_num)
  have h1 (j : Fin 3) :
      ∫ y, spatialDeriv f j y ^ 2 ≤ N := by
    simpa only [wordDeriv] using hsingle [j] (by simp)
  have h2 (j k : Fin 3) :
      ∫ y, spatialDeriv (spatialDeriv f j) k y ^ 2 ≤ N := by
    simpa only [wordDeriv] using hsingle [j, k] (by simp)
  have hFbound : ∫ y, F y ≤ 13 * N := by
    have hsum1 : ∑ j : Fin 3,
        (∫ y, spatialDeriv f j y ^ 2) ≤ 3 * N := by
      calc
        _ ≤ ∑ _j : Fin 3, N := Finset.sum_le_sum fun j _ => h1 j
        _ = 3 * N := by simp
    have hsum2 : ∑ j : Fin 3, ∑ k : Fin 3,
        (∫ y, spatialDeriv (spatialDeriv f j) k y ^ 2) ≤ 9 * N := by
      calc
        _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, N :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h2 j k
        _ = 9 * N := by simp only [Fin.sum_univ_three]; ring
    have houter : ∫ y, F y =
        (∫ y, f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2) +
          ∫ y, ∑ j : Fin 3, ∑ k : Fin 3,
            spatialDeriv (spatialDeriv f j) k y ^ 2 := by
      exact integral_add (h0int.add hsum1int) hsum2int
    have hinner :
        ∫ y, f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 =
        (∫ y, f y ^ 2) +
          ∫ y, ∑ j : Fin 3, spatialDeriv f j y ^ 2 := by
      exact integral_add h0int hsum1int
    rw [houter, hinner,
      integral_finsetSum _ fun j _ => h1int j,
      integral_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => h2int j k]
    simp_rw [integral_finsetSum _ fun k _ => h2int _ k]
    linarith only [h0, hsum1, hsum2]
  have hx0 : vec3EuclideanNorm (x - x) ≤ (1 : ℝ) := by
    simp [vec3EuclideanNorm]
  have hxbound := hlocal x f hf x hx0
  have hxSq : |f x| ^ 2 ≤ (13 * C₀) * N := by
    calc
      |f x| ^ 2 ≤ C₀ * ∫ y in vec3Ball x 2, F y := hxbound
      _ ≤ C₀ * ∫ y, F y := by gcongr
      _ ≤ C₀ * (13 * N) := by gcongr
      _ = (13 * C₀) * N := by ring
  have hsqrt := Real.sqrt_le_sqrt hxSq
  rw [Real.sqrt_sq_eq_abs, abs_abs] at hsqrt
  rw [Real.sqrt_mul (by positivity : 0 ≤ 13 * C₀)] at hsqrt
  exact hsqrt

/-- An ordered derivative at least two orders below `m` is uniformly
bounded by the full `H^m` energy (eq:lps-Hm-energy). -/
theorem lps_lower_word_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (f : Vec3 → ℝ)
      (α : List (Fin 3)),
      ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ β : List (Fin 3), β.length ≤ m →
        MemLp (wordDeriv β f) 2 volume) →
      α.length + 2 ≤ m →
      ∀ x, |wordDeriv α f x| ≤ C * Real.sqrt
        (sobolevNormSqOn m univ (fun β => wordDeriv β f)) := by
  obtain ⟨C, hC, hH2⟩ := lps_smooth_h2_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro m f α hf hL2 hα x
  let g : Vec3 → ℝ := wordDeriv α f
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_wordDeriv hf α
  have hgL2 : MemLp g 2 volume := by
    simpa only [g, lps_wordDeriv_append_words, List.append_nil] using
      hL2 α (by omega)
  have hgDL2 (j : Fin 3) : MemLp (spatialDeriv g j) 2 volume := by
    simpa only [g, ← wordDeriv_append, lps_wordDeriv_append_words] using
      hL2 (α ++ [j]) (by simp; omega)
  have hgD2L2 (j k : Fin 3) :
      MemLp (spatialDeriv (spatialDeriv g j) k) 2 volume := by
    simpa [g, ← wordDeriv_append, lps_wordDeriv_append_words,
      List.append_assoc] using
      hL2 (α ++ [j, k]) (by simp; omega)
  have hsubset : (sobolevWords 2).image (fun β => α ++ β) ⊆ sobolevWords m := by
    intro γ hγ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hγ
    apply mem_sobolevWords.mpr
    have hβlen := mem_sobolevWords.mp hβ
    simp only [List.length_append]
    omega
  have hnorm : sobolevNormSqOn 2 univ (fun β => wordDeriv β g) ≤
      sobolevNormSqOn m univ (fun β => wordDeriv β f) := by
    unfold sobolevNormSqOn
    simp_rw [show ∀ β, wordDeriv β g = wordDeriv (α ++ β) f from
      fun β => lps_wordDeriv_append_words α β f]
    calc
      _ = ∑ γ ∈ (sobolevWords 2).image (fun β => α ++ β),
          ∫ y in univ, wordDeriv γ f y ^ 2 := by
            rw [Finset.sum_image (fun β _ γ _ h =>
              (List.append_right_injective α) h)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun β _ _ => integral_nonneg fun y => sq_nonneg _)
  have h := hH2 g hg hgL2 hgDL2 hgD2L2 x
  calc
    |wordDeriv α f x| = |g x| := rfl
    _ ≤ C * Real.sqrt (sobolevNormSqOn 2 univ
      (fun β => wordDeriv β g)) := h
    _ ≤ C * Real.sqrt (sobolevNormSqOn m univ
      (fun β => wordDeriv β f)) := by gcongr

/-- A lower derivative times any derivative through order `m` has a
square-integrable product, controlled by the two ordered Sobolev energies
(`eq:lps-Hm-energy`). -/
theorem lps_lower_word_product_integral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (f g : Vec3 → ℝ)
      (α β : List (Fin 3)),
      ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ γ : List (Fin 3), γ.length ≤ m →
        MemLp (wordDeriv γ f) 2 volume) →
      (∀ γ : List (Fin 3), γ.length ≤ m →
        MemLp (wordDeriv γ g) 2 volume) →
      α.length + 2 ≤ m → β.length ≤ m →
      Integrable (fun x =>
        (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
      (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
        C ^ 2 * sobolevNormSqOn m univ (fun γ => wordDeriv γ f) *
          (∫ x, wordDeriv β g x ^ 2) := by
  obtain ⟨C, hC, hBound⟩ := lps_lower_word_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro m f g α β hf hfL2 hgL2 hα hβ
  let N : ℝ := sobolevNormSqOn m univ (fun γ => wordDeriv γ f)
  have hN : 0 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hBound' (x : Vec3) : |wordDeriv α f x| ≤ C * Real.sqrt N :=
    hBound m f α hf hfL2 hα x
  have hb := hgL2 β hβ
  have haMeas : AEStronglyMeasurable (wordDeriv α f) volume :=
    (contDiff_wordDeriv hf α).continuous.aestronglyMeasurable
  have hprod : MemLp (fun x => wordDeriv α f x * wordDeriv β g x)
      2 volume := by
    apply MemLp.of_le_mul hb (haMeas.mul hb.aestronglyMeasurable)
    filter_upwards [] with x
    change |wordDeriv α f x * wordDeriv β g x| ≤
      (C * Real.sqrt N) * |wordDeriv β g x|
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hBound' x) (abs_nonneg _)
  have hpoint (x : Vec3) :
      (wordDeriv α f x * wordDeriv β g x) ^ 2 ≤
        (C ^ 2 * N) * wordDeriv β g x ^ 2 := by
    have hsquare : wordDeriv α f x ^ 2 ≤ (C * Real.sqrt N) ^ 2 := by
      calc
        wordDeriv α f x ^ 2 = |wordDeriv α f x| ^ 2 :=
          (sq_abs _).symm
        _ ≤ (C * Real.sqrt N) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (hBound' x) 2
    calc
      (wordDeriv α f x * wordDeriv β g x) ^ 2 =
          wordDeriv α f x ^ 2 * wordDeriv β g x ^ 2 := by ring
      _ ≤ (C * Real.sqrt N) ^ 2 * wordDeriv β g x ^ 2 := by
        gcongr
      _ = (C ^ 2 * N) * wordDeriv β g x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hN]
  refine ⟨hprod.integrable_sq, ?_⟩
  have hright : Integrable
      (fun x => (C ^ 2 * N) * wordDeriv β g x ^ 2) volume :=
    hb.integrable_sq.const_mul _
  calc
    (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
        ∫ x, (C ^ 2 * N) * wordDeriv β g x ^ 2 :=
          integral_mono hprod.integrable_sq hright hpoint
    _ = C ^ 2 * N * (∫ x, wordDeriv β g x ^ 2) := by
      rw [integral_const_mul]

/-- Each ordered derivative contributes a nonnegative summand to the
whole `H^m` energy (eq:lps-Hm-energy). -/
theorem lps_wordDeriv_integral_le_sobolev (m : ℕ)
    (f : Vec3 → ℝ) (α : List (Fin 3)) (hα : α.length ≤ m) :
    (∫ x, wordDeriv α f x ^ 2) ≤
      sobolevNormSqOn m univ (fun β => wordDeriv β f) := by
  unfold sobolevNormSqOn
  simp only [Measure.restrict_univ]
  exact Finset.single_le_sum
    (f := fun β : List (Fin 3) => ∫ x, wordDeriv β f x ^ 2)
    (s := sobolevWords m)
    (fun β _ => integral_nonneg fun x => sq_nonneg _)
    (mem_sobolevWords.mpr hα)

/-- At order at least three, each Leibniz split of total degree at most
`m` has a factor with at least two unused derivatives. Its product is
therefore controlled by the two `H^m` energies (`eq:lps-Hm-energy`). -/
theorem lps_word_pair_integral_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (f g : Vec3 → ℝ)
      (α β : List (Fin 3)),
      3 ≤ m → α.length + β.length ≤ m →
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ γ : List (Fin 3), γ.length ≤ m →
        MemLp (wordDeriv γ f) 2 volume) →
      (∀ γ : List (Fin 3), γ.length ≤ m →
        MemLp (wordDeriv γ g) 2 volume) →
      Integrable (fun x =>
        (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
      (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
        C ^ 2 *
          sobolevNormSqOn m univ (fun γ => wordDeriv γ f) *
          sobolevNormSqOn m univ (fun γ => wordDeriv γ g) := by
  obtain ⟨C, hC, hLow⟩ := lps_lower_word_product_integral_bound
  refine ⟨C, hC, ?_⟩
  intro m f g α β hm hdegree hf hg hfL2 hgL2
  have hα : α.length ≤ m := by omega
  have hβ : β.length ≤ m := by omega
  have hNf : 0 ≤ sobolevNormSqOn m univ (fun γ => wordDeriv γ f) := by
    unfold sobolevNormSqOn
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hNg : 0 ≤ sobolevNormSqOn m univ (fun γ => wordDeriv γ g) := by
    unfold sobolevNormSqOn
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  by_cases hαlow : α.length + 2 ≤ m
  · obtain ⟨hint, hbound⟩ :=
      hLow m f g α β hf hfL2 hgL2 hαlow hβ
    refine ⟨hint, ?_⟩
    calc
      _ ≤ C ^ 2 * sobolevNormSqOn m univ
          (fun γ => wordDeriv γ f) *
          (∫ x, wordDeriv β g x ^ 2) := hbound
      _ ≤ C ^ 2 * sobolevNormSqOn m univ
          (fun γ => wordDeriv γ f) *
          sobolevNormSqOn m univ (fun γ => wordDeriv γ g) := by
            gcongr
            exact lps_wordDeriv_integral_le_sobolev m g β hβ
  · have hβlow : β.length + 2 ≤ m := by omega
    obtain ⟨hint, hbound⟩ :=
      hLow m g f β α hg hgL2 hfL2 hβlow hα
    have heq : (fun x => (wordDeriv α f x * wordDeriv β g x) ^ 2) =
        (fun x => (wordDeriv β g x * wordDeriv α f x) ^ 2) := by
      funext x
      ring
    rw [heq]
    refine ⟨hint, ?_⟩
    calc
      _ ≤ C ^ 2 * sobolevNormSqOn m univ
          (fun γ => wordDeriv γ g) *
          (∫ x, wordDeriv α f x ^ 2) := hbound
      _ ≤ C ^ 2 * sobolevNormSqOn m univ
          (fun γ => wordDeriv γ g) *
          sobolevNormSqOn m univ (fun γ => wordDeriv γ f) := by
            gcongr
            exact lps_wordDeriv_integral_le_sobolev m f α hα
      _ = _ := by ring

/-- At order two, the only Leibniz split outside the lower-derivative
bound assigns one derivative to each factor. A quantitative bound for
that middle split completes the termwise estimate
(`eq:lps-Hm-energy`). -/
theorem lps_word_pair_integral_bound_two_of_middle :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ γ : List (Fin 3), γ.length ≤ 2 →
        MemLp (wordDeriv γ f) 2 volume) →
      (∀ γ : List (Fin 3), γ.length ≤ 2 →
        MemLp (wordDeriv γ g) 2 volume) →
      ∀ (M : ℝ), 0 ≤ M →
      (∀ α β : List (Fin 3), α.length = 1 → β.length = 1 →
        Integrable (fun x =>
          (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
        (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
          M * sobolevNormSqOn 2 univ (fun γ => wordDeriv γ f) *
            sobolevNormSqOn 2 univ (fun γ => wordDeriv γ g)) →
      ∀ α β : List (Fin 3),
        α.length + β.length ≤ 2 →
        Integrable (fun x =>
          (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
        (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
          (C₀ ^ 2 + M) * sobolevNormSqOn 2 univ (fun γ => wordDeriv γ f) *
            sobolevNormSqOn 2 univ (fun γ => wordDeriv γ g) := by
  obtain ⟨C₀, hC₀, hLow⟩ := lps_lower_word_product_integral_bound
  refine ⟨C₀, hC₀, ?_⟩
  intro f g hf hg hfL2 hgL2 M hM hmid α β hdegree
  let Nf := sobolevNormSqOn 2 univ (fun γ => wordDeriv γ f)
  let Ng := sobolevNormSqOn 2 univ (fun γ => wordDeriv γ g)
  have hNf : 0 ≤ Nf := by
    dsimp [Nf, sobolevNormSqOn]
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hNg : 0 ≤ Ng := by
    dsimp [Ng, sobolevNormSqOn]
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hprodN : 0 ≤ Nf * Ng := mul_nonneg hNf hNg
  have hα : α.length ≤ 2 := by omega
  have hβ : β.length ≤ 2 := by omega
  by_cases hαlow : α.length + 2 ≤ 2
  · obtain ⟨hint, hbound⟩ := hLow 2 f g α β hf hfL2 hgL2 hαlow hβ
    refine ⟨hint, ?_⟩
    calc
      _ ≤ C₀ ^ 2 * Nf * (∫ x, wordDeriv β g x ^ 2) := hbound
      _ ≤ C₀ ^ 2 * Nf * Ng := by
        gcongr
        exact lps_wordDeriv_integral_le_sobolev 2 g β hβ
      _ ≤ (C₀ ^ 2 + M) * Nf * Ng := by
        nlinarith only [hprodN, hM, sq_nonneg C₀]
  · by_cases hβlow : β.length + 2 ≤ 2
    · obtain ⟨hint, hbound⟩ := hLow 2 g f β α hg hgL2 hfL2 hβlow hα
      have heq : (fun x => (wordDeriv α f x * wordDeriv β g x) ^ 2) =
          (fun x => (wordDeriv β g x * wordDeriv α f x) ^ 2) := by
        funext x
        ring
      rw [heq]
      refine ⟨hint, ?_⟩
      calc
        _ ≤ C₀ ^ 2 * Ng * (∫ x, wordDeriv α f x ^ 2) := hbound
        _ ≤ C₀ ^ 2 * Ng * Nf := by
          gcongr
          exact lps_wordDeriv_integral_le_sobolev 2 f α hα
        _ ≤ (C₀ ^ 2 + M) * Nf * Ng := by
          nlinarith only [hprodN, hM, sq_nonneg C₀]
    · have hαone : α.length = 1 := by omega
      have hβone : β.length = 1 := by omega
      obtain ⟨hint, hbound⟩ := hmid α β hαone hβone
      refine ⟨hint, ?_⟩
      calc
        _ ≤ M * Nf * Ng := hbound
        _ ≤ (C₀ ^ 2 + M) * Nf * Ng := by
          nlinarith only [hprodN, hM, sq_nonneg C₀]

end ESS
