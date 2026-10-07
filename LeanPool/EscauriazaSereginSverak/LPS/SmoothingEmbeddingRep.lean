/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingEmbedding

/-!
# `C^k` representatives of whole-space weak families

`lem:lps-Bochner-joint-smooth`: a function with a Sobolev family through order
`k + 2` on `ℝ³` has a `C^k` representative whose ordered derivatives represent
the family, with sup norms controlled by the Sobolev norm.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Triangle inequality for real `L²` norms (`lem:lps-Bochner-joint-smooth`). -/
theorem lps_toReal_eLpNorm_le_add {f g : Vec3 → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) :
    (eLpNorm f 2 volume).toReal ≤
      (eLpNorm g 2 volume).toReal + (eLpNorm (f - g) 2 volume).toReal := by
  have h1 : eLpNorm f 2 volume ≤ eLpNorm g 2 volume + eLpNorm (f - g) 2 volume := by
    have : f = g + (f - g) := by
      funext x
      simp
    calc eLpNorm f 2 volume = eLpNorm (g + (f - g)) 2 volume := by rw [← this]
      _ ≤ eLpNorm g 2 volume + eLpNorm (f - g) 2 volume := eLpNorm_add_le (by norm_num)
  have hfin : eLpNorm g 2 volume + eLpNorm (f - g) 2 volume ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hg.eLpNorm_ne_top, (hf.sub hg).eLpNorm_ne_top⟩
  have := ENNReal.toReal_mono hfin h1
  rwa [ENNReal.toReal_add hg.eLpNorm_ne_top (hf.sub hg).eLpNorm_ne_top] at this

/-- Uniformly Cauchy sequences of real functions converge uniformly
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_tendstoUniformly_of_uniformCauchy {a : ℕ → Vec3 → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ x, |a n x - a m x| < ε) :
    ∃ l : Vec3 → ℝ, TendstoUniformly a l atTop := by
  have hcauchy : ∀ x, CauchySeq (fun n => a n x) := by
    intro x
    refine Metric.cauchySeq_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn m hm => by
      rw [Real.dist_eq]
      exact hN n hn m hm x⟩
  choose l hl using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨l, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop N] with n hn x
  have hlim : Tendsto (fun m => |a n x - a m x|) atTop (𝓝 |a n x - l x|) :=
    ((tendsto_const_nhds.sub (hl x)).abs)
  have hle : |a n x - l x| ≤ ε / 2 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with m hm
    exact (hN n hn m hm x).le
  rw [dist_comm, Real.dist_eq]
  linarith only [hle, hε]

/-- `lem:lps-Bochner-joint-smooth`: a whole-space weak family through order
`k + 2` has a `C^k` representative, its ordered derivatives represent the family,
and their sup norms are bounded by the Sobolev norm. -/
theorem lps_sobolevFamily_contDiff_rep (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec3 → ℝ) (D : List (Fin 3) → Vec3 → ℝ),
      IsSobolevFamilyOn (k + 2) univ f D →
      ∃ g : Vec3 → ℝ, ContDiff ℝ k g ∧ g =ᵐ[volume] f ∧
        (∀ α : List (Fin 3), α.length ≤ k → wordDeriv α g =ᵐ[volume] D α) ∧
        ∀ α : List (Fin 3), α.length ≤ k → ∀ x,
          |wordDeriv α g x| ≤ C * Real.sqrt (sobolevNormSqOn (k + 2) univ D) := by
  obtain ⟨C₀, hC₀, hC⟩ := abs_le_sobolevTwo_smooth
  refine ⟨C₀, hC₀, fun f D h => ?_⟩
  obtain ⟨g, hg, hgc, hgconv, -⟩ := sobolevFamily_smooth_approx (ι := Unit) (m := k + 2)
    (f := fun _ => f) (D := fun α _ => D α) (fun _ => h)
  have hg' : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n ()) := fun n => hg n ()
  have hgc' : ∀ n, HasCompactSupport (g n ()) := fun n => hgc n ()
  have hDmem : ∀ α : List (Fin 3), α.length ≤ k + 2 → MemLp (D α) 2 volume := by
    intro α hα
    simpa only [Measure.restrict_univ] using h.memL2 α hα
  have hconv' : ∀ α : List (Fin 3), α.length ≤ k + 2 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n ()) - D α) 2 volume) atTop (𝓝 0) :=
    fun α hα => hgconv () α hα
  have hmem (n : ℕ) (γ : List (Fin 3)) : MemLp (wordDeriv γ (g n ())) 2 volume :=
    (contDiff_wordDeriv (hg' n) γ).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_wordDeriv (hgc' n) γ)
  -- uniform Cauchy property of all ordered derivatives up to order `k`
  have hunif : ∀ α : List (Fin 3), α.length ≤ k →
      ∃ l : Vec3 → ℝ, TendstoUniformly (fun n => wordDeriv α (g n ())) l atTop := by
    intro α hα
    refine lps_tendstoUniformly_of_uniformCauchy fun ε hε => ?_
    obtain ⟨N, hN⟩ := lps_sobolevNormSq_two_sub_small hg' hgc' hDmem hconv' α hα
      ((ε / (C₀ + 1)) ^ 2) (by positivity)
    refine ⟨N, fun n hn m hm x => ?_⟩
    have hdiffC : ContDiff ℝ (⊤ : ℕ∞) (wordDeriv α (fun y => g n () y - g m () y)) :=
      contDiff_wordDeriv ((hg' n).sub (hg' m)) α
    have hdiffc : HasCompactSupport (wordDeriv α (fun y => g n () y - g m () y)) := by
      refine hasCompactSupport_wordDeriv ?_ α
      exact (hgc' n).sub (hgc' m)
    have hb := hC _ hdiffC hdiffc x
    have hrewrite : wordDeriv α (fun y => g n () y - g m () y) =
        fun y => wordDeriv α (g n ()) y - wordDeriv α (g m ()) y :=
      lps_wordDeriv_sub (hg' n) (hg' m) α
    rw [hrewrite] at hb
    have hN' := hN n hn m hm
    have hsq : Real.sqrt (sobolevNormSqOn 2 univ (fun β => wordDeriv β
        (wordDeriv α (fun y => g n () y - g m () y)))) < ε / (C₀ + 1) := by
      rw [show ε / (C₀ + 1) = Real.sqrt ((ε / (C₀ + 1)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_lt_sqrt (Finset.sum_nonneg fun β _ =>
        integral_nonneg fun y => sq_nonneg _) hN'
    rw [hrewrite] at hsq
    calc |wordDeriv α (g n ()) x - wordDeriv α (g m ()) x|
        ≤ C₀ * Real.sqrt (sobolevNormSqOn 2 univ (fun β => wordDeriv β
            (fun y => wordDeriv α (g n ()) y - wordDeriv α (g m ()) y))) := hb
      _ ≤ C₀ * (ε / (C₀ + 1)) := mul_le_mul_of_nonneg_left hsq.le hC₀
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith only [hε, hC₀]
  obtain ⟨f', hf'C, hf'T⟩ := lps_uniform_limit_contDiff k (fun n => g n ()) hg' hunif
  have hae : ∀ α : List (Fin 3), α.length ≤ k → wordDeriv α f' =ᵐ[volume] D α := by
    intro α hα
    have hlen : α.length ≤ k + 2 := by omega
    have hTM : TendstoInMeasure volume (fun n => wordDeriv α (g n ())) atTop (D α) :=
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hconv' α hlen)
    obtain ⟨ns, hns, hns'⟩ := hTM.exists_seq_tendsto_ae
    filter_upwards [hns'] with x hx
    have h2 : Tendsto (fun i => wordDeriv α (g (ns i) ()) x) atTop
        (𝓝 (wordDeriv α f' x)) := ((hf'T α hα).tendsto_at x).comp hns.tendsto_atTop
    exact tendsto_nhds_unique h2 hx
  refine ⟨f', hf'C, ?_, hae, ?_⟩
  · have h0 := hae [] (by simp)
    simp only [wordDeriv] at h0
    exact h0.trans (by simpa only [Measure.restrict_univ] using h.zero)
  · intro α hα x
    -- bound along the approximating sequence
    have hseq : ∀ n, |wordDeriv α (g n ()) x| ≤ C₀ * Real.sqrt (∑ β ∈ sobolevWords 2,
        ∫ y, (wordDeriv (α ++ β) (g n ()) y) ^ 2) := by
      intro n
      have hb := hC _ (contDiff_wordDeriv (hg' n) α)
        (hasCompactSupport_wordDeriv (hgc' n) α) x
      refine hb.trans (le_of_eq ?_)
      congr 3
      unfold sobolevNormSqOn
      simp only [Measure.restrict_univ]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [lps_wordDeriv_append_words]
    -- convergence of the right-hand side
    have hterm : ∀ β ∈ sobolevWords 2, Tendsto
        (fun n => ∫ y, (wordDeriv (α ++ β) (g n ()) y) ^ 2) atTop
        (𝓝 (∫ y, (D (α ++ β) y) ^ 2)) := by
      intro β hβ
      have hβl := mem_sobolevWords.mp hβ
      have hlen : (α ++ β).length ≤ k + 2 := by
        simp only [List.length_append]
        omega
      have hDm := hDmem _ hlen
      have hnorm : Tendsto (fun n => (eLpNorm (wordDeriv (α ++ β) (g n ())) 2 volume).toReal)
          atTop (𝓝 (eLpNorm (D (α ++ β)) 2 volume).toReal) := by
        have hreal : Tendsto (fun n => (eLpNorm (wordDeriv (α ++ β) (g n ()) -
            D (α ++ β)) 2 volume).toReal) atTop (𝓝 0) :=
          (ENNReal.tendsto_toReal_zero_iff
            (fun n => ((hmem n _).sub hDm).eLpNorm_ne_top)).2 (hconv' _ hlen)
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hreal
        rw [Real.dist_eq, abs_le]
        have h1 := lps_toReal_eLpNorm_le_add (hmem n (α ++ β)) hDm
        have h2 := lps_toReal_eLpNorm_le_add hDm (hmem n (α ++ β))
        rw [eLpNorm_sub_comm] at h2
        constructor <;> linarith only [h1, h2]
      have hsq := hnorm.pow 2
      have heq : ∀ n, ∫ y, (wordDeriv (α ++ β) (g n ()) y) ^ 2 =
          (eLpNorm (wordDeriv (α ++ β) (g n ())) 2 volume).toReal ^ 2 :=
        fun n => vl_integral_sq_eq (hmem n _)
      rw [vl_integral_sq_eq hDm]
      simpa only [heq] using hsq
    have hsum := tendsto_finsetSum (sobolevWords 2) hterm
    have hrhs : Tendsto (fun n => C₀ * Real.sqrt (∑ β ∈ sobolevWords 2,
        ∫ y, (wordDeriv (α ++ β) (g n ()) y) ^ 2)) atTop
        (𝓝 (C₀ * Real.sqrt (∑ β ∈ sobolevWords 2, ∫ y, (D (α ++ β) y) ^ 2))) :=
      (hsum.sqrt).const_mul C₀
    have hlhs : Tendsto (fun n => |wordDeriv α (g n ()) x|) atTop
        (𝓝 |wordDeriv α f' x|) := ((hf'T α hα).tendsto_at x).abs
    have hlim := le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall hseq)
    refine hlim.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC₀)
    -- the sum over shifted words is bounded by the Sobolev norm
    unfold sobolevNormSqOn
    simp only [Measure.restrict_univ]
    have hinj : Set.InjOn (fun β : List (Fin 3) => α ++ β) (sobolevWords 2 : Set (List (Fin 3))) :=
      fun a _ b _ hab => List.append_cancel_left hab
    rw [← Finset.sum_image (f := fun γ : List (Fin 3) => ∫ y, (D γ y) ^ 2) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun γ _ _ => integral_nonneg fun y =>
      sq_nonneg _)
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨β, hβ, rfl⟩ := hγ
    rw [mem_sobolevWords] at hβ ⊢
    simp only [List.length_append]
    omega

end ESS
