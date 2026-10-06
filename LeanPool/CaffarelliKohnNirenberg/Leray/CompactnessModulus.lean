/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeak

/-!
# Compactness Modulus

Supporting estimates for the Navier–Stokes development.
-/

public section

open Filter Topology Set

namespace CKN.Leray

/-- A two-term power modulus makes a real-valued map continuous. -/
theorem continuous_of_two_term_time_modulus
    {T : Type*} [PseudoMetricSpace T] (F : T → ℝ)
    (C D θ : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hθ : 0 < θ)
    (hmod : ∀ s t, |F t - F s| ≤
      C * dist t s + D * (dist t s) ^ θ) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ₁ : ℝ := ε / (2 * (C + 1))
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hpowTendsto : Tendsto (fun x : ℝ => x ^ θ) (nhds 0) (nhds 0) :=
    Filter.Tendsto.rpow_const_nhds_zero tendsto_id hθ
  have hthreshold : 0 < ε / (2 * (D + 1)) := by positivity
  have hpowSmall : ∀ᶠ x : ℝ in nhds 0,
      x ^ θ < ε / (2 * (D + 1)) :=
    hpowTendsto.eventually (isOpen_Iio.mem_nhds hthreshold)
  obtain ⟨δ₂, hδ₂, hδ₂ball⟩ := Metric.eventually_nhds_iff.mp hpowSmall
  have hfracC : C / (2 * (C + 1)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hC]
  have hfracD : D / (2 * (D + 1)) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [hD]
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
  have ht₁ : dist t t₀ < δ₁ := (lt_min_iff.mp ht).1
  have ht₂ : dist t t₀ < δ₂ := (lt_min_iff.mp ht).2
  have hlinear : C * dist t t₀ < ε / 2 := by
    calc
      C * dist t t₀ ≤ C * δ₁ := mul_le_mul_of_nonneg_left ht₁.le hC
      _ = ε * (C / (2 * (C + 1))) := by dsimp [δ₁]; ring
      _ < ε * (1 / 2) := mul_lt_mul_of_pos_left hfracC hε
      _ = ε / 2 := by ring
  have hdistNonneg : 0 ≤ dist t t₀ := dist_nonneg
  have hpowMem : dist (dist t t₀) 0 < δ₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hdistNonneg]
    exact ht₂
  have hpower : (dist t t₀) ^ θ < ε / (2 * (D + 1)) :=
    hδ₂ball hpowMem
  have hpower' : D * (dist t t₀) ^ θ < ε / 2 := by
    calc
      D * (dist t t₀) ^ θ ≤ D * (ε / (2 * (D + 1))) :=
        mul_le_mul_of_nonneg_left hpower.le hD
      _ = ε * (D / (2 * (D + 1))) := by ring
      _ < ε * (1 / 2) := mul_lt_mul_of_pos_left hfracD hε
      _ = ε / 2 := by ring
  rw [Real.dist_eq]
  calc
    |F t - F t₀| ≤ C * dist t t₀ + D * (dist t t₀) ^ θ := hmod t₀ t
    _ < ε / 2 + ε / 2 := add_lt_add hlinear hpower'
    _ = ε := by ring

/-- The two-term time modulus supplies continuous scalar pairing maps on each
compact time window. -/
@[expose]
def continuousMapOfTwoTermTimeModulus
    {T : Type*} [PseudoMetricSpace T] (F : T → ℝ)
    (C D θ : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hθ : 0 < θ)
    (hmod : ∀ s t, |F t - F s| ≤
      C * dist t s + D * (dist t s) ^ θ) : C(T, ℝ) :=
  ⟨F, continuous_of_two_term_time_modulus F C D θ hC hD hθ hmod⟩

/-- Countably many compact-time Hilbert families admit one weakly convergent
subsequence when each dense-test pairing has a uniform two-term modulus. -/
theorem exists_common_subsequence_weak_pairings_of_two_term_moduli
    {ι : Type*} [Countable ι]
    (T : ι → Type*) [∀ i, PseudoMetricSpace (T i)]
      [∀ i, CompactSpace (T i)] [∀ i, CompactlyCoherentSpace (T i)]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
      [∀ i, InnerProductSpace ℝ (E i)] [∀ i, CompleteSpace (E i)]
    (u : ℕ → ∀ i, T i → E i) (ψ : ∀ i, ℕ → E i)
    (hψ : ∀ i, DenseRange (ψ i)) (C : ι → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hbound : ∀ n i t, ‖u n i t‖ ≤ C i)
    (hmod : ∀ i m, ∃ A B θ : ℝ,
      0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, |inner ℝ (u n i t) (ψ i m) -
        inner ℝ (u n i s) (ψ i m)| ≤
          A * dist t s + B * (dist t s) ^ θ) :
    ∃ F : ℕ → ∀ i, ℕ → C(T i, ℝ),
      (∀ n i m t, F n i m t = inner ℝ (u n i t) (ψ i m)) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ v : ∀ i, T i → E i,
        (∀ i t x, Tendsto (fun n => inner ℝ (u (σ n) i t) x) atTop
          (nhds (inner ℝ (v i t) x))) ∧
        (∀ i x, Continuous (fun t => inner ℝ (v i t) x)) ∧
        (∀ i t x, |inner ℝ (v i t) x| ≤ C i * ‖x‖) ∧
        ∃ L : ∀ i, ℕ → C(T i, ℝ),
          (∀ i m t, L i m t = inner ℝ (v i t) (ψ i m)) ∧
          ∀ i m, Tendsto (fun n => F (σ n) i m) atTop (nhds (L i m)) := by
  classical
  let A : ∀ i m, ℝ := fun i m => Classical.choose (hmod i m)
  let B : ∀ i m, ℝ := fun i m => Classical.choose (Classical.choose_spec (hmod i m))
  let θ : ∀ i m, ℝ := fun i m =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hmod i m)))
  have hspec (i : ι) (m : ℕ) :
      0 ≤ A i m ∧ 0 ≤ B i m ∧ 0 < θ i m ∧
        ∀ n s t, |inner ℝ (u n i t) (ψ i m) -
          inner ℝ (u n i s) (ψ i m)| ≤
            A i m * dist t s + B i m * (dist t s) ^ θ i m :=
    Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (hmod i m)))
  let F : ℕ → ∀ i, ℕ → C(T i, ℝ) := fun n i m =>
    continuousMapOfTwoTermTimeModulus
      (fun t => inner ℝ (u n i t) (ψ i m)) (A i m) (B i m) (θ i m)
      (hspec i m).1 (hspec i m).2.1 (hspec i m).2.2.1
      (fun s t => hspec i m |>.2.2.2 n s t)
  have hpair (n : ℕ) (i : ι) (m : ℕ) (t : T i) :
      F n i m t = inner ℝ (u n i t) (ψ i m) := rfl
  have hequi (i : ι) (m : ℕ) : EquicontinuousOn
      (fun g : range fun n => F n i m => (g : T i → ℝ)) univ := by
    exact equicontinuous_of_two_term_time_modulus
      (fun n => F n i m) (A i m) (B i m) (θ i m)
      (hspec i m).1 (hspec i m).2.1 (hspec i m).2.2.1
      (fun n s t => hspec i m |>.2.2.2 n s t)
  obtain ⟨σ, hσ, v, hv, hcontinuous, hvbound, L, hLval, hLconv⟩ :=
    exists_common_subsequence_weak_pairings_on_compact_times
      T E u ψ hψ C hC hbound F hpair hequi
  exact ⟨F, hpair, σ, hσ, v, hv, hcontinuous, hvbound, L, hLval, hLconv⟩

end CKN.Leray
