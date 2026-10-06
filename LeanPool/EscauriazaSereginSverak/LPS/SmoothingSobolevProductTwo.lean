/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevEmbedding
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingLeibnizSplits
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevGN

/-!
# Order-two Sobolev product reduction

The `H²` algebra estimate reduces to the product of two first
derivatives. The latter receives a quantitative whole-space `L⁴`
bound from the Sobolev interpolation step.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A uniform middle-split estimate for first derivatives implies the
ordered whole-space `H²` algebra estimate (eq:lps-Hm-energy). -/
theorem lps_smooth_product_normSq_two_of_middle
    (M : ℝ) (hM : 0 ≤ M)
    (hmid : ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α g) 2 volume) →
      ∀ α β : List (Fin 3), α.length = 1 → β.length = 1 →
        Integrable (fun x =>
          (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
        (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
          M * sobolevNormSqOn 2 univ (fun γ => wordDeriv γ f) *
            sobolevNormSqOn 2 univ (fun γ => wordDeriv γ g)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α g) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α (fun x => f x * g x)) 2 volume) ∧
      sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => f x * g x)) ≤
        C * sobolevNormSqOn 2 univ (fun α => wordDeriv α f) *
          sobolevNormSqOn 2 univ (fun α => wordDeriv α g) := by
  obtain ⟨C₀, hC₀, hpair⟩ := lps_word_pair_integral_bound_two_of_middle
  let W := sobolevWords 2
  let P : ℝ := C₀ ^ 2 + M
  let S : ℝ := ∑ α ∈ W, ((lpsLeibnizSplits α).length : ℝ) ^ 2
  let C : ℝ := S * P
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun α _ => sq_nonneg _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f g hf hg hfL2 hgL2
  let Nf := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  let Ng := sobolevNormSqOn 2 univ (fun α => wordDeriv α g)
  have hpair' (α β : List (Fin 3))
      (hdegree : α.length + β.length ≤ 2) :
      Integrable (fun x =>
        (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
      (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
        P * Nf * Ng := by
    exact hpair f g hf hg hfL2 hgL2 M hM
      (hmid f g hf hg hfL2 hgL2) α β hdegree
  have hterm (α : List (Fin 3)) (hα : α.length ≤ 2) :
      Integrable (fun x =>
        sobolevLeibnizFamily α (fun β => wordDeriv β f)
          (fun β => wordDeriv β g) x ^ 2) volume ∧
      (∫ x, sobolevLeibnizFamily α
        (fun β => wordDeriv β f)
        (fun β => wordDeriv β g) x ^ 2) ≤
          ((lpsLeibnizSplits α).length : ℝ) ^ 2 *
            (P * Nf * Ng) := by
    apply lps_leibniz_integral_bound
    intro p hp
    have hdegree := lps_leibniz_splits_degree α p hp
    have hp' := hpair' p.1 p.2 (by omega)
    have hmeas : AEStronglyMeasurable
        (fun x => wordDeriv p.1 f x * wordDeriv p.2 g x)
        volume :=
      ((contDiff_wordDeriv hf p.1).continuous.mul
        (contDiff_wordDeriv hg p.2).continuous).aestronglyMeasurable
    exact ⟨(memLp_two_iff_integrable_sq hmeas).2 hp'.1, hp'.2⟩
  have hnorm : sobolevNormSqOn 2 univ
        (fun α => sobolevLeibnizFamily α
          (fun β => wordDeriv β f)
          (fun β => wordDeriv β g)) ≤ C * Nf * Ng := by
    change (∑ α ∈ W, ∫ x in univ, sobolevLeibnizFamily α
      (fun β => wordDeriv β f) (fun β => wordDeriv β g) x ^ 2) ≤
        C * Nf * Ng
    simp only [Measure.restrict_univ]
    calc
      _ ≤ ∑ α ∈ W, ((lpsLeibnizSplits α).length : ℝ) ^ 2 *
          (P * Nf * Ng) := by
            exact Finset.sum_le_sum fun α hα =>
              (hterm α (mem_sobolevWords.mp hα)).2
      _ = C * Nf * Ng := by
        rw [← Finset.sum_mul]
        dsimp [C, S]
        ring
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
    exact (hterm α hα).1
  · simp_rw [heq]
    exact hnorm

/-- Smooth multiplication is bounded in the ordered whole-space `H²`
norm (eq:lps-Hm-energy). -/
theorem lps_smooth_product_normSq_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α g) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α (fun x => f x * g x)) 2 volume) ∧
      sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => f x * g x)) ≤
        C * sobolevNormSqOn 2 univ (fun α => wordDeriv α f) *
          sobolevNormSqOn 2 univ (fun α => wordDeriv α g) := by
  obtain ⟨M, hM, hmid⟩ := lps_smooth_h2_middle_product_energy
  exact lps_smooth_product_normSq_two_of_middle M hM hmid

end ESS
