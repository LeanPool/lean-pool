/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevEmbedding
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLeibnizSplits
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct

/-!
# High-order whole-space Sobolev product estimate

At integer order at least three, every Leibniz term has a factor
with at least two derivatives to spare. Whole-space `H² → L∞`
therefore bounds the product in the ordered Sobolev energy.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The ordered Leibniz family of two smooth `H^m` functions has
square-integrable derivatives through order `m ≥ 3`, with an `H^m`
algebra bound (eq:lps-Hm-energy). -/
theorem lps_smooth_leibniz_normSq_high (m : ℕ) (hm : 3 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α g) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ m →
        Integrable (fun x =>
          sobolevLeibnizFamily α
            (fun β => wordDeriv β f)
            (fun β => wordDeriv β g) x ^ 2) volume) ∧
      sobolevNormSqOn m univ
        (fun α => sobolevLeibnizFamily α
          (fun β => wordDeriv β f)
          (fun β => wordDeriv β g)) ≤
        C * sobolevNormSqOn m univ (fun α => wordDeriv α f) *
          sobolevNormSqOn m univ (fun α => wordDeriv α g) := by
  obtain ⟨C₀, hC₀, hpair⟩ := lps_word_pair_integral_bound
  let W := sobolevWords m
  let M : ℝ := ∑ α ∈ W, ((lpsLeibnizSplits α).length : ℝ) ^ 2
  let C : ℝ := M * C₀ ^ 2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun α _ => sq_nonneg _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f g hf hg hfL2 hgL2
  let Nf := sobolevNormSqOn m univ (fun α => wordDeriv α f)
  let Ng := sobolevNormSqOn m univ (fun α => wordDeriv α g)
  have hNf : 0 ≤ Nf := by
    dsimp [Nf, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hNg : 0 ≤ Ng := by
    dsimp [Ng, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hterm (α : List (Fin 3)) (hα : α.length ≤ m) :
      Integrable (fun x =>
        sobolevLeibnizFamily α (fun β => wordDeriv β f)
          (fun β => wordDeriv β g) x ^ 2) volume ∧
      (∫ x, sobolevLeibnizFamily α
        (fun β => wordDeriv β f)
        (fun β => wordDeriv β g) x ^ 2) ≤
          ((lpsLeibnizSplits α).length : ℝ) ^ 2 *
            (C₀ ^ 2 * Nf * Ng) := by
    apply lps_leibniz_integral_bound
    intro p hp
    have hdegree := lps_leibniz_splits_degree α p hp
    have hpair' := hpair m f g p.1 p.2 hm
      (by omega) hf hg hfL2 hgL2
    have hmeas : AEStronglyMeasurable
        (fun x => wordDeriv p.1 f x * wordDeriv p.2 g x)
        volume :=
      ((contDiff_wordDeriv hf p.1).continuous.mul
        (contDiff_wordDeriv hg p.2).continuous).aestronglyMeasurable
    refine ⟨(memLp_two_iff_integrable_sq hmeas).2 hpair'.1, ?_⟩
    simpa only [Nf, Ng] using hpair'.2
  refine ⟨fun α hα => (hterm α hα).1, ?_⟩
  change (∑ α ∈ W, ∫ x in univ, sobolevLeibnizFamily α
    (fun β => wordDeriv β f) (fun β => wordDeriv β g) x ^ 2) ≤
      C * Nf * Ng
  simp only [Measure.restrict_univ]
  calc
    _ ≤ ∑ α ∈ W, ((lpsLeibnizSplits α).length : ℝ) ^ 2 *
        (C₀ ^ 2 * Nf * Ng) := by
          exact Finset.sum_le_sum fun α hα =>
            (hterm α (mem_sobolevWords.mp hα)).2
    _ = C * Nf * Ng := by
      rw [← Finset.sum_mul]
      dsimp [C, M]
      ring

/-- Smooth multiplication is bounded in the ordered whole-space `H^m`
norm for every integer `m ≥ 3` (eq:lps-Hm-energy). -/
theorem lps_smooth_product_normSq_high (m : ℕ) (hm : 3 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α g) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ m →
        MemLp (wordDeriv α (fun x => f x * g x)) 2 volume) ∧
      sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => f x * g x)) ≤
        C * sobolevNormSqOn m univ (fun α => wordDeriv α f) *
          sobolevNormSqOn m univ (fun α => wordDeriv α g) := by
  obtain ⟨C, hC, hbound⟩ := lps_smooth_leibniz_normSq_high m hm
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hfL2 hgL2
  obtain ⟨hint, hnorm⟩ := hbound f g hf hg hfL2 hgL2
  have heq (α : List (Fin 3)) :
      wordDeriv α (fun x => f x * g x) =
        sobolevLeibnizFamily α
          (fun β => wordDeriv β f)
          (fun β => wordDeriv β g) :=
    lps_wordDeriv_mul_leibniz hf hg α
  refine ⟨?_, ?_⟩
  · intro α hα
    have hmeas : AEStronglyMeasurable
        (wordDeriv α (fun x => f x * g x)) volume :=
      (contDiff_wordDeriv (hf.mul hg) α).continuous.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hmeas).2
    rw [heq α]
    exact hint α hα
  · simp_rw [heq]
    exact hnorm

end ESS
