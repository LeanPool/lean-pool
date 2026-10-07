/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SobolevEmbeddingR3
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEmbeddingLimit
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainShape
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityLocalizedEnergyMollifier

/-!
# Sobolev embedding for whole-space weak families

A function with a Sobolev family through order `k + 2` on `ℝ³` has a `C^k`
representative whose ordered derivatives represent the family, bounded by the
Sobolev norm (`lem:lps-Bochner-joint-smooth`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A square-integrable function that is the `L²` limit of smooth compactly
supported functions with square-integrable difference `a n - a m` has
Cauchy square integrals (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_integral_sq_sub_small {a : ℕ → Vec3 → ℝ} {D : Vec3 → ℝ}
    (ha : ∀ n, MemLp (a n) 2 volume) (hD : MemLp D 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (a n - D) 2 volume) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ∫ x, (a n x - a m x) ^ 2 < ε := by
  intro ε hε
  have hreal : Tendsto (fun n => (eLpNorm (a n - D) 2 volume).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun n => ((ha n).sub hD).eLpNorm_ne_top)).2 hconv
  have hη : 0 < Real.sqrt ε / 4 := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hreal) (Real.sqrt ε / 4) hη
  refine ⟨N, fun n hn m hm => ?_⟩
  have hnN := hN n hn
  have hmN := hN m hm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at hnN hmN
  have hsub : MemLp (fun x => a n x - a m x) 2 volume := (ha n).sub (ha m)
  rw [vl_integral_sq_eq hsub]
  have htri : (eLpNorm (fun x => a n x - a m x) 2 volume).toReal ≤
      (eLpNorm (a n - D) 2 volume).toReal + (eLpNorm (a m - D) 2 volume).toReal := by
    have h1 : eLpNorm (fun x => a n x - a m x) 2 volume ≤
        eLpNorm (a n - D) 2 volume + eLpNorm (a m - D) 2 volume := by
      have : (fun x => a n x - a m x) = (a n - D) - (a m - D) := by
        funext x
        simp
      rw [this]
      exact eLpNorm_sub_le (by norm_num)
    have hfin : eLpNorm (a n - D) 2 volume + eLpNorm (a m - D) 2 volume ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨((ha n).sub hD).eLpNorm_ne_top, ((ha m).sub hD).eLpNorm_ne_top⟩
    have := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_add ((ha n).sub hD).eLpNorm_ne_top ((ha m).sub hD).eLpNorm_ne_top]
      at this
  have hle : (eLpNorm (fun x => a n x - a m x) 2 volume).toReal < Real.sqrt ε / 2 := by
    linarith only [htri, hnN, hmN]
  have h0 : 0 ≤ (eLpNorm (fun x => a n x - a m x) 2 volume).toReal := ENNReal.toReal_nonneg
  calc (eLpNorm (fun x => a n x - a m x) 2 volume).toReal ^ 2
      < (Real.sqrt ε / 2) ^ 2 := by gcongr
    _ = ε / 4 := by
        rw [div_pow, Real.sq_sqrt hε.le]
        norm_num
    _ < ε := by linarith only [hε]

/-- The `H²` norm squared of an ordered derivative of a difference of two members
of an `L²`-convergent smooth family is eventually small
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_sobolevNormSq_two_sub_small {g : ℕ → Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    {k : ℕ}
    (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) (hgc : ∀ n, HasCompactSupport (g n))
    (hD : ∀ α : List (Fin 3), α.length ≤ k + 2 → MemLp (D α) 2 volume)
    (hconv : ∀ α : List (Fin 3), α.length ≤ k + 2 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n) - D α) 2 volume) atTop (𝓝 0))
    (α : List (Fin 3)) (hα : α.length ≤ k) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      sobolevNormSqOn 2 univ
        (fun β => wordDeriv β (wordDeriv α (fun x => g n x - g m x))) < ε := by
  intro ε hε
  have hmem (n : ℕ) (γ : List (Fin 3)) : MemLp (wordDeriv γ (g n)) 2 volume :=
    (contDiff_wordDeriv (hg n) γ).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_wordDeriv (hgc n) γ)
  set c : ℝ := ((sobolevWords 2).card : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hε' : 0 < ε / (c + 1) := by positivity
  have hβ : ∀ β ∈ sobolevWords 2, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      ∫ x, (wordDeriv (α ++ β) (g n) x - wordDeriv (α ++ β) (g m) x) ^ 2 < ε / (c + 1) := by
    intro β hβ
    have hβl := mem_sobolevWords.mp hβ
    have hlen : (α ++ β).length ≤ k + 2 := by
      simp only [List.length_append]
      omega
    exact lps_integral_sq_sub_small (a := fun n => wordDeriv (α ++ β) (g n))
      (fun n => hmem n _) (hD _ hlen) (hconv _ hlen) (ε / (c + 1)) hε'
  choose! Nβ hNβ using hβ
  obtain ⟨M, hM'⟩ := (Finset.image Nβ (sobolevWords 2)).exists_le
  have hM : ∀ β ∈ sobolevWords 2, Nβ β ≤ M := fun β hβ => hM' _ (Finset.mem_image_of_mem _ hβ)
  refine ⟨M, fun n hn m hm => ?_⟩
  have hexpand : sobolevNormSqOn 2 univ
      (fun β => wordDeriv β (wordDeriv α (fun x => g n x - g m x))) =
      ∑ β ∈ sobolevWords 2,
        ∫ x, (wordDeriv (α ++ β) (g n) x - wordDeriv (α ++ β) (g m) x) ^ 2 := by
    unfold sobolevNormSqOn
    simp only [Measure.restrict_univ]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [lps_wordDeriv_append_words,
      lps_wordDeriv_sub (hg n) (hg m)]
  rw [hexpand]
  calc ∑ β ∈ sobolevWords 2,
        ∫ x, (wordDeriv (α ++ β) (g n) x - wordDeriv (α ++ β) (g m) x) ^ 2
      ≤ ∑ β ∈ sobolevWords 2, ε / (c + 1) := by
        refine Finset.sum_le_sum fun β hβ => (hNβ β hβ n ?_ m ?_).le
        · exact (hM β hβ).trans hn
        · exact (hM β hβ).trans hm
    _ = c * (ε / (c + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith only [hε, hc0]

end ESS
