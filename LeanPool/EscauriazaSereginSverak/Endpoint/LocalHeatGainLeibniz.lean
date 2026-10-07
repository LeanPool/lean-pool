/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainEnergy

/-!
# Space-time Sobolev families and multiplication by smooth cutoffs

On a set `V ⊆ ℝ³ × ℝ`, a family `B` of square-integrable fields indexed by
derivative words, with `B (α ++ [j])` the distributional spatial derivative
`∂_j B α` on `V`, describes a field in `L²_t H^n_x`. Multiplication by a smooth
field `ζ` whose spatial derivatives are all bounded maps such a family to the
Leibniz family `stLeibniz α (spaceTimeWord · ζ) B` of the product. This is the
cutoff step in the proof of `lem:local-heat-gain`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `g` is the distributional `j`-th spatial derivative of `f` on `V`. -/
@[expose] def IsSpaceTimeWeakPartial (V : Set (Vec3 × ℝ)) (j : Fin 3) (f g : Vec3 × ℝ → ℝ) : Prop :=
  ∀ φ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ V →
    ∫ p in V, f p * spatialPartial φ j p = -∫ p in V, g p * φ p

/-- A space-time derivative family through order `n` on `V`. -/
structure IsSpaceTimeFamily (n : ℕ) (V : Set (Vec3 × ℝ)) (B : List (Fin 3) → Vec3 × ℝ → ℝ) :
    Prop where
  memL2 : ∀ α : List (Fin 3), α.length ≤ n → MemLp (B α) 2 (volume.restrict V)
  weak : ∀ (α : List (Fin 3)) (j : Fin 3), α.length < n →
    IsSpaceTimeWeakPartial V j (B α) (B (α ++ [j]))

/-- The Leibniz family of a product of two space-time families; the first
letter of the word is applied first. -/
@[expose] def stLeibniz : List (Fin 3) → (List (Fin 3) → Vec3 × ℝ → ℝ) →
    (List (Fin 3) → Vec3 × ℝ → ℝ) → Vec3 × ℝ → ℝ
  | [], A, B => fun p => A [] p * B [] p
  | j :: α, A, B => fun p =>
      stLeibniz α (fun γ => A (j :: γ)) B p + stLeibniz α A (fun γ => B (j :: γ)) p

/-- A space-time test function is square integrable on every restriction. -/
theorem memLp_two_restrict_of_test {φ : Vec3 × ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (V : Set (Vec3 × ℝ)) :
    MemLp φ 2 (volume.restrict V) :=
  (hφ.memLp_of_hasCompactSupport hφc).restrict V

/-- The first-order Leibniz rule for a distributional spatial derivative and
a smooth factor. -/
theorem IsSpaceTimeWeakPartial.smooth_mul {V : Set (Vec3 × ℝ)} {j : Fin 3}
    {f g ζ : Vec3 × ℝ → ℝ} (h : IsSpaceTimeWeakPartial V j f g)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hf : MemLp f 2 (volume.restrict V))
    (hg : MemLp g 2 (volume.restrict V)) :
    IsSpaceTimeWeakPartial V j (fun p => ζ p * f p)
      (fun p => spatialPartial ζ j p * f p + ζ p * g p) := by
  intro φ hφ hφc hφV
  have hζφ : ContDiff ℝ (⊤ : ℕ∞) (fun q => ζ q * φ q) := hζ.mul hφ
  have hζφc : HasCompactSupport (fun q => ζ q * φ q) := hφc.mul_left
  have hζφV : tsupport (fun q => ζ q * φ q) ⊆ V :=
    (tsupport_mul_subset_right (f := ζ) (g := φ)).trans hφV
  have hdζ : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial ζ j q) :=
    vorticityHeatSmooth_spatialPartial_contDiff hζ j
  have hdφ : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial φ j q) :=
    vorticityHeatSmooth_spatialPartial_contDiff hφ j
  have hprod (p : Vec3 × ℝ) :
      spatialPartial (fun q : Vec3 × ℝ => ζ q * φ q) j p =
        ζ p * spatialPartial φ j p + φ p * spatialPartial ζ j p :=
    vorticityHeatSmooth_spatialPartial_mul hζ hφ j p
  have hL2_1 : MemLp (fun q : Vec3 × ℝ => spatialPartial (fun r : Vec3 × ℝ => ζ r * φ r) j q) 2
      (volume.restrict V) :=
    memLp_two_restrict_of_test (vorticityHeatSmooth_spatialPartial_contDiff hζφ j).continuous
      (CKN.hasCompactSupport_spatialPartial hζφc j) V
  have hL2_2 : MemLp (fun q => φ q * spatialPartial ζ j q) 2 (volume.restrict V) :=
    memLp_two_restrict_of_test (hφ.continuous.mul hdζ.continuous) hφc.mul_right V
  have hL2_3 : MemLp (fun q => ζ q * φ q) 2 (volume.restrict V) :=
    memLp_two_restrict_of_test hζφ.continuous hζφc V
  have hL2_4 : MemLp φ 2 (volume.restrict V) :=
    memLp_two_restrict_of_test hφ.continuous hφc V
  have hkey := h (fun q => ζ q * φ q) hζφ hζφc hζφV
  have hsplit : (fun p => ζ p * f p * spatialPartial φ j p) =
      fun p => f p * spatialPartial (fun q : Vec3 × ℝ => ζ q * φ q) j p -
        f p * (φ p * spatialPartial ζ j p) := by
    funext p
    rw [hprod p]
    ring
  have i1 : Integrable (fun p => f p * spatialPartial (fun q : Vec3 × ℝ => ζ q * φ q) j p)
      (volume.restrict V) := hf.integrable_mul hL2_1
  have i2 : Integrable (fun p => f p * (φ p * spatialPartial ζ j p)) (volume.restrict V) :=
    hf.integrable_mul hL2_2
  have i3 : Integrable (fun p => -(g p * (ζ p * φ p))) (volume.restrict V) :=
    (hg.integrable_mul hL2_3).neg
  calc
    ∫ p in V, ζ p * f p * spatialPartial φ j p =
        (∫ p in V, f p * spatialPartial (fun q : Vec3 × ℝ => ζ q * φ q) j p) -
          ∫ p in V, f p * (φ p * spatialPartial ζ j p) := by
      rw [hsplit, integral_sub i1 i2]
    _ = -(∫ p in V, g p * (ζ p * φ p)) - ∫ p in V, f p * (φ p * spatialPartial ζ j p) := by
      rw [hkey]
    _ = -∫ p in V, (spatialPartial ζ j p * f p + ζ p * g p) * φ p := by
      rw [← integral_neg, ← integral_sub i3 i2, ← integral_neg]
      congr 1
      funext p
      ring

/-- The sum rule for distributional spatial derivatives. -/
theorem IsSpaceTimeWeakPartial.add {V : Set (Vec3 × ℝ)} {j : Fin 3} {f₁ g₁ f₂ g₂ : Vec3 × ℝ → ℝ}
    (h₁ : IsSpaceTimeWeakPartial V j f₁ g₁) (h₂ : IsSpaceTimeWeakPartial V j f₂ g₂)
    (hf₁ : MemLp f₁ 2 (volume.restrict V)) (hf₂ : MemLp f₂ 2 (volume.restrict V))
    (hg₁ : MemLp g₁ 2 (volume.restrict V)) (hg₂ : MemLp g₂ 2 (volume.restrict V)) :
    IsSpaceTimeWeakPartial V j (fun p => f₁ p + f₂ p) (fun p => g₁ p + g₂ p) := by
  intro φ hφ hφc hφV
  have hφ2 := memLp_two_restrict_of_test hφ.continuous hφc V
  have hdφ2 : MemLp (fun q : Vec3 × ℝ => spatialPartial φ j q) 2 (volume.restrict V) :=
    memLp_two_restrict_of_test (vorticityHeatSmooth_spatialPartial_contDiff hφ j).continuous
      (CKN.hasCompactSupport_spatialPartial hφc j) V
  have i1 : Integrable (fun p => f₁ p * spatialPartial φ j p) (volume.restrict V) :=
    hf₁.integrable_mul hdφ2
  have i2 : Integrable (fun p => f₂ p * spatialPartial φ j p) (volume.restrict V) :=
    hf₂.integrable_mul hdφ2
  have i3 : Integrable (fun p => g₁ p * φ p) (volume.restrict V) := hg₁.integrable_mul hφ2
  have i4 : Integrable (fun p => g₂ p * φ p) (volume.restrict V) := hg₂.integrable_mul hφ2
  have e1 : (fun p => (f₁ p + f₂ p) * spatialPartial φ j p) =
      fun p => f₁ p * spatialPartial φ j p + f₂ p * spatialPartial φ j p := by
    funext p
    ring
  have e2 : (fun p => (g₁ p + g₂ p) * φ p) = fun p => g₁ p * φ p + g₂ p * φ p := by
    funext p
    ring
  rw [e1, e2, integral_add i1 i2, integral_add i3 i4, h₁ φ hφ hφc hφV, h₂ φ hφ hφc hφV]
  ring

theorem sobolevWords_zero : sobolevWords 0 = {[]} := by
  ext α
  rw [mem_sobolevWords, Finset.mem_singleton, Nat.le_zero, List.length_eq_zero_iff]

theorem sobolevWords_mono {k n : ℕ} (hkn : k ≤ n) : sobolevWords k ⊆ sobolevWords n := by
  intro α hα
  rw [mem_sobolevWords] at hα ⊢
  omega

/-- Sums over words of length at most `k`, shifted by a first letter, are
bounded by sums over words of length at most `k + 1`. -/
theorem sum_sobolevWords_cons_le (k : ℕ) (j : Fin 3) (φ : List (Fin 3) → ℝ)
    (hφ : ∀ α, 0 ≤ φ α) :
    ∑ γ ∈ sobolevWords k, φ (j :: γ) ≤ ∑ γ ∈ sobolevWords (k + 1), φ γ := by
  classical
  have hinj : Set.InjOn (fun γ : List (Fin 3) => j :: γ) ↑(sobolevWords k) :=
    fun _ _ _ _ h => List.cons_injective h
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun α _ _ => hφ α
  intro α hα
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hα
  rw [mem_sobolevWords] at hγ ⊢
  simp only [List.length_cons]
  omega

/-- The pointwise bound for a Leibniz family with a bounded first factor. -/
theorem stLeibniz_abs_le (α : List (Fin 3)) (A B : List (Fin 3) → Vec3 × ℝ → ℝ) (L : ℝ)
    (hA : ∀ γ : List (Fin 3), γ.length ≤ α.length → ∀ p, |A γ p| ≤ L) (p : Vec3 × ℝ) :
    |stLeibniz α A B p| ≤ 2 ^ α.length * L * ∑ γ ∈ sobolevWords α.length, |B γ p| := by
  induction α generalizing A B with
  | nil =>
      have hL : |A [] p| ≤ L := hA [] le_rfl p
      simp only [stLeibniz, List.length_nil, pow_zero, one_mul, sobolevWords_zero,
        Finset.sum_singleton, abs_mul]
      exact mul_le_mul_of_nonneg_right hL (abs_nonneg _)
  | cons j α ih =>
      have hL0 : 0 ≤ L := (abs_nonneg _).trans (hA [] (by simp) p)
      have h1 := ih (fun γ => A (j :: γ)) B (fun γ hγ q => hA (j :: γ)
        (by simp only [List.length_cons]; omega) q)
      have h2 := ih A (fun γ => B (j :: γ)) (fun γ hγ q => hA γ
        (by simp only [List.length_cons]; omega) q)
      have hS1 : ∑ γ ∈ sobolevWords α.length, |B γ p| ≤
          ∑ γ ∈ sobolevWords (α.length + 1), |B γ p| :=
        Finset.sum_le_sum_of_subset_of_nonneg (sobolevWords_mono (Nat.le_succ _))
          fun _ _ _ => abs_nonneg _
      have hS2 := sum_sobolevWords_cons_le α.length j (fun γ => |B γ p|) fun _ => abs_nonneg _
      have hc : 0 ≤ 2 ^ α.length * L := by positivity
      simp only [stLeibniz, List.length_cons]
      calc
        |stLeibniz α (fun γ => A (j :: γ)) B p + stLeibniz α A (fun γ => B (j :: γ)) p|
            ≤ |stLeibniz α (fun γ => A (j :: γ)) B p| +
                |stLeibniz α A (fun γ => B (j :: γ)) p| := abs_add_le _ _
        _ ≤ 2 ^ α.length * L * ∑ γ ∈ sobolevWords α.length, |B γ p| +
              2 ^ α.length * L * ∑ γ ∈ sobolevWords α.length, |B (j :: γ) p| :=
            add_le_add h1 h2
        _ ≤ 2 ^ α.length * L * ∑ γ ∈ sobolevWords (α.length + 1), |B γ p| +
              2 ^ α.length * L * ∑ γ ∈ sobolevWords (α.length + 1), |B γ p| :=
            add_le_add (mul_le_mul_of_nonneg_left hS1 hc) (mul_le_mul_of_nonneg_left hS2 hc)
        _ = 2 ^ (α.length + 1) * L * ∑ γ ∈ sobolevWords (α.length + 1), |B γ p| := by
            ring

/-- Leibniz families of almost everywhere strongly measurable families are
almost everywhere strongly measurable. -/
theorem stLeibniz_aestronglyMeasurable (α : List (Fin 3)) (A B : List (Fin 3) → Vec3 × ℝ → ℝ)
    {μ : Measure (Vec3 × ℝ)}
    (hA : ∀ γ : List (Fin 3), γ.length ≤ α.length → AEStronglyMeasurable (A γ) μ)
    (hB : ∀ γ : List (Fin 3), γ.length ≤ α.length → AEStronglyMeasurable (B γ) μ) :
    AEStronglyMeasurable (stLeibniz α A B) μ := by
  induction α generalizing A B with
  | nil => exact (hA [] le_rfl).mul (hB [] le_rfl)
  | cons j α ih =>
      exact (ih (fun γ => A (j :: γ)) B
          (fun γ hγ => hA (j :: γ) (by simp only [List.length_cons]; omega))
          (fun γ hγ => hB γ (by simp only [List.length_cons]; omega))).add
        (ih A (fun γ => B (j :: γ))
          (fun γ hγ => hA γ (by simp only [List.length_cons]; omega))
          (fun γ hγ => hB (j :: γ) (by simp only [List.length_cons]; omega)))

/-- Leibniz families with a bounded measurable first factor and a square
integrable second factor are square integrable. -/
theorem stLeibniz_memLp (α : List (Fin 3)) {A B : List (Fin 3) → Vec3 × ℝ → ℝ}
    {V : Set (Vec3 × ℝ)} (L : ℝ)
    (hAb : ∀ γ : List (Fin 3), γ.length ≤ α.length → ∀ p, |A γ p| ≤ L)
    (hAm : ∀ γ : List (Fin 3), γ.length ≤ α.length →
      AEStronglyMeasurable (A γ) (volume.restrict V))
    (hB : ∀ γ : List (Fin 3), γ.length ≤ α.length → MemLp (B γ) 2 (volume.restrict V)) :
    MemLp (stLeibniz α A B) 2 (volume.restrict V) := by
  have hg : MemLp (fun p => 2 ^ α.length * L * ∑ γ ∈ sobolevWords α.length, |B γ p|) 2
      (volume.restrict V) := by
    refine MemLp.const_mul ?_ _
    refine memLp_finsetSum _ fun γ hγ => ?_
    exact (hB γ (mem_sobolevWords.1 hγ)).abs
  refine hg.of_le (stLeibniz_aestronglyMeasurable α A B hAm
    (fun γ hγ => (hB γ hγ).aestronglyMeasurable)) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (stLeibniz_abs_le α A B L hAb p).trans (le_abs_self _)

/-- Bounds for each spatial word derivative give a uniform bound through any
finite order. -/
theorem exists_uniform_wordBound {ζ : Vec3 × ℝ → ℝ}
    (hζb : ∀ γ : List (Fin 3), ∃ L : ℝ, ∀ p, |spaceTimeWord γ ζ p| ≤ L) (k : ℕ) :
    ∃ L : ℝ, ∀ γ : List (Fin 3), γ.length ≤ k → ∀ p, |spaceTimeWord γ ζ p| ≤ L := by
  classical
  choose Lf hLf using hζb
  refine ⟨∑ γ ∈ sobolevWords k, |Lf γ|, fun γ hγ p => ?_⟩
  have hmem : γ ∈ sobolevWords k := mem_sobolevWords.2 hγ
  calc
    |spaceTimeWord γ ζ p| ≤ Lf γ := hLf γ p
    _ ≤ |Lf γ| := le_abs_self _
    _ ≤ ∑ γ ∈ sobolevWords k, |Lf γ| :=
      Finset.single_le_sum (f := fun γ => |Lf γ|) (fun _ _ => abs_nonneg _) hmem

/-- Multiplication by a smooth field with bounded spatial derivatives maps a
space-time derivative family to the Leibniz family of the product. -/
theorem IsSpaceTimeFamily.smooth_mul {n : ℕ} {V : Set (Vec3 × ℝ)}
    {B : List (Fin 3) → Vec3 × ℝ → ℝ} (hB : IsSpaceTimeFamily n V B)
    {ζ : Vec3 × ℝ → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζb : ∀ γ : List (Fin 3), ∃ L : ℝ, ∀ p, |spaceTimeWord γ ζ p| ≤ L) :
    IsSpaceTimeFamily n V (fun α => stLeibniz α (fun γ => spaceTimeWord γ ζ) B) := by
  have hmem : ∀ (n : ℕ) (ζ : Vec3 × ℝ → ℝ) (B : List (Fin 3) → Vec3 × ℝ → ℝ),
      IsSpaceTimeFamily n V B → ContDiff ℝ (⊤ : ℕ∞) ζ →
      (∀ γ : List (Fin 3), ∃ L : ℝ, ∀ p, |spaceTimeWord γ ζ p| ≤ L) →
      ∀ α : List (Fin 3), α.length ≤ n →
        MemLp (stLeibniz α (fun γ => spaceTimeWord γ ζ) B) 2 (volume.restrict V) := by
    intro n ζ B hB hζ hζb α hα
    obtain ⟨L, hL⟩ := exists_uniform_wordBound hζb α.length
    exact stLeibniz_memLp α L hL
      (fun γ _ => (contDiff_spaceTimeWord γ hζ).continuous.aestronglyMeasurable)
      (fun γ hγ => hB.memL2 γ (hγ.trans hα))
  refine ⟨hmem n ζ B hB hζ hζb, ?_⟩
  intro α
  induction α generalizing n ζ B with
  | nil =>
      intro k hn
      exact (hB.weak [] k hn).smooth_mul hζ (hB.memL2 [] (Nat.zero_le _))
        (hB.memL2 [k] (by simp only [List.length_singleton, List.length_nil] at hn ⊢; omega))
  | cons j α ih =>
      intro k hn
      have hn1 : α.length < n - 1 := by simp only [List.length_cons] at hn; omega
      let ζ' : Vec3 × ℝ → ℝ := fun p => spatialPartial ζ j p
      have hζ' : ContDiff ℝ (⊤ : ℕ∞) ζ' := vorticityHeatSmooth_spatialPartial_contDiff hζ j
      have hζ'b : ∀ γ : List (Fin 3), ∃ L : ℝ, ∀ p, |spaceTimeWord γ ζ' p| ≤ L :=
        fun γ => hζb (j :: γ)
      have hB' : IsSpaceTimeFamily (n - 1) V (fun γ => B (j :: γ)) :=
        ⟨fun γ hγ => hB.memL2 (j :: γ) (by simp only [List.length_cons]; omega),
          fun γ l hγ => hB.weak (j :: γ) l (by simp only [List.length_cons]; omega)⟩
      have hB0 : IsSpaceTimeFamily n V B := hB
      have h1 := ih hB0 hζ' hζ'b k (by simp only [List.length_cons] at hn; omega)
      have h2 := ih hB' hζ hζb k hn1
      exact h1.add h2
        (hmem n ζ' B hB0 hζ' hζ'b α (by omega))
        (hmem (n - 1) ζ (fun γ => B (j :: γ)) hB' hζ hζb α (by omega))
        (hmem n ζ' B hB0 hζ' hζ'b (α ++ [k])
          (by simp only [List.length_append, List.length_singleton]; omega))
        (hmem (n - 1) ζ (fun γ => B (j :: γ)) hB' hζ hζb (α ++ [k])
          (by simp only [List.length_append, List.length_singleton]; omega))

/-- The squared `L²_t H^n_x` norm of a Leibniz family is bounded by the
squared norm of the second factor times the square of a bound for the first. -/
theorem stLeibniz_normSq_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Set (Vec3 × ℝ)) (A B : List (Fin 3) → Vec3 × ℝ → ℝ) (L : ℝ),
      (∀ γ : List (Fin 3), γ.length ≤ n → ∀ p, |A γ p| ≤ L) →
      (∀ γ : List (Fin 3), γ.length ≤ n → AEStronglyMeasurable (A γ) (volume.restrict V)) →
      (∀ γ : List (Fin 3), γ.length ≤ n → MemLp (B γ) 2 (volume.restrict V)) →
      ∑ α ∈ sobolevWords n, ∫ p in V, stLeibniz α A B p ^ 2 ≤
        C * L ^ 2 * ∑ α ∈ sobolevWords n, ∫ p in V, B α p ^ 2 := by
  let c : ℝ := (sobolevWords n).card
  refine ⟨c * 4 ^ n * c, by positivity, ?_⟩
  intro V A B L hAb hAm hB
  have hpt (α : List (Fin 3)) (hα : α ∈ sobolevWords n) (p : Vec3 × ℝ) :
      stLeibniz α A B p ^ 2 ≤ 4 ^ n * L ^ 2 * c * ∑ γ ∈ sobolevWords n, B γ p ^ 2 := by
    have hαn := mem_sobolevWords.1 hα
    have hL0 : 0 ≤ L := (abs_nonneg _).trans (hAb [] (Nat.zero_le _) p)
    have h1 := stLeibniz_abs_le α A B L (fun γ hγ => hAb γ (hγ.trans hαn)) p
    have h2 : ∑ γ ∈ sobolevWords α.length, |B γ p| ≤ ∑ γ ∈ sobolevWords n, |B γ p| :=
      Finset.sum_le_sum_of_subset_of_nonneg (sobolevWords_mono hαn) fun _ _ _ => abs_nonneg _
    have h3 : (2 : ℝ) ^ α.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hαn
    have h4 : |stLeibniz α A B p| ≤ 2 ^ n * L * ∑ γ ∈ sobolevWords n, |B γ p| :=
      h1.trans (by gcongr)
    have h5 : (∑ γ ∈ sobolevWords n, |B γ p|) ^ 2 ≤ c * ∑ γ ∈ sobolevWords n, |B γ p| ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h6 : ∑ γ ∈ sobolevWords n, |B γ p| ^ 2 = ∑ γ ∈ sobolevWords n, B γ p ^ 2 := by
      simp only [sq_abs]
    calc
      stLeibniz α A B p ^ 2 = |stLeibniz α A B p| ^ 2 := (sq_abs _).symm
      _ ≤ (2 ^ n * L * ∑ γ ∈ sobolevWords n, |B γ p|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h4 2
      _ = 4 ^ n * L ^ 2 * (∑ γ ∈ sobolevWords n, |B γ p|) ^ 2 := by
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
        norm_num
      _ ≤ 4 ^ n * L ^ 2 * (c * ∑ γ ∈ sobolevWords n, |B γ p| ^ 2) := by gcongr
      _ = 4 ^ n * L ^ 2 * c * ∑ γ ∈ sobolevWords n, B γ p ^ 2 := by rw [h6]; ring
  have hint (α : List (Fin 3)) (hα : α ∈ sobolevWords n) :
      Integrable (fun p => stLeibniz α A B p ^ 2) (volume.restrict V) := by
    have hαn := mem_sobolevWords.1 hα
    exact (stLeibniz_memLp α L (fun γ hγ => hAb γ (hγ.trans hαn))
      (fun γ hγ => hAm γ (hγ.trans hαn)) (fun γ hγ => hB γ (hγ.trans hαn))).integrable_sq
  have hBint (γ : List (Fin 3)) (hγ : γ ∈ sobolevWords n) :
      Integrable (fun p => B γ p ^ 2) (volume.restrict V) :=
    (hB γ (mem_sobolevWords.1 hγ)).integrable_sq
  calc
    ∑ α ∈ sobolevWords n, ∫ p in V, stLeibniz α A B p ^ 2 ≤
        ∑ α ∈ sobolevWords n, ∫ p in V, 4 ^ n * L ^ 2 * c * ∑ γ ∈ sobolevWords n, B γ p ^ 2 :=
      Finset.sum_le_sum fun α hα => integral_mono (hint α hα)
        ((integrable_finsetSum _ hBint).const_mul _) (hpt α hα)
    _ = c * 4 ^ n * c * L ^ 2 * ∑ α ∈ sobolevWords n, ∫ p in V, B α p ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul, integral_const_mul, integral_finsetSum _ hBint]
      ring

end ESS
