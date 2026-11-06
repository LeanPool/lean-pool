/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Main
public import LeanPool.RareSubtreePatterns.Bridge.CriterionS
public import LeanPool.RareSubtreePatterns.Bridge.Microscopic
public import LeanPool.RareSubtreePatterns.Cyclic.UniformVertex
public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof
public import LeanPool.RareSubtreePatterns.DirectApplications.FringeCorollary

/-!
# Elementary criteria for the hypotheses of Theorem 1.1 (inventory U01)

Source lines 227–237 (expected count and the uniform vertex), 293–295 (a uniform pair bound
implies (C)) and 359–364 (a convenient sufficient criterion).

* `integral_markCount_eq_mul_uniformFringeLaw`: `E[N_n] = n P(G_{k_n}(𝒯^n_{U_n}) = 1)`, where
  `N_n = #{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}` (Corollary `cor:cyclicshift`, re-exported from
  `Cyclic.integral_markCount_conditioned`);
* `microscopic_first_iff`: the first clause of (M) is equivalent to `E[N_n] / n ∼ π_n`
  (source lines 235–237: "the expected proportion of marked fringe subtrees is asymptotic to
  `π_n`");
* `nonClustering_of_iSup_pairProb`: `sup_{ℓ ≥ 1} A_n(ℓ) = o((n / M_n) π_n²)` implies (C)
  (source lines 293–295); `nonClustering_of_uniform_pair_bound` is the same statement with any
  bound `b_n ≥ A_n(ℓ)` (for all `ℓ ≥ 1`) in place of the supremum;
* `hypotheses_of_convenient_criterion` (**source lines 359–364**): if the decompositions of
  Assumption (S) satisfy `E_{k_n}[C_{k_n} + L_{k_n}] = n^{o(1)}` and
  `sup_{ℓ ≥ 1} A_n(ℓ) ≤ n^{o(1)} π_n²`, then for every `η ∈ (0, 1 - 1/α)` the hypotheses of
  Theorem 1.1 hold with `M_n = ⌊n^{1-η}⌋` (encoded as `max 1 ⌊n^{1-η}⌋₊`, equal for `n ≥ 1`);
  `poisson_of_convenient_criterion` combines it with Theorem 1.1.

As in Lemma `lem:critM` (`Bridge.critM`), the hypotheses `x_n = n^{o(1)}` are used only through
their upper halves "for every `δ > 0`, eventually `x_n ≤ n^δ`", along admissible sizes.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.DirectApplications

open PlaneTree

/-- **`U01`, first part** (source lines 227–237, Corollary `cor:cyclicshift`): the expected
number of marked fringe subtrees of `𝒯^n` is `n` times the probability that the fringe subtree
at a uniform vertex is marked, `E[N_n] = n P(G_{k_n}(𝒯^n_{U_n}) = 1)`. -/
theorem integral_markCount_eq_mul_uniformFringeLaw (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop)
    (k : ℕ → ℕ) (n : ℕ) :
    ∫ T, (markCount (G (k n)) T : ℝ) ∂conditioned μ n =
      n * (uniformFringeLaw μ n).real {T | G (k n) T} :=
  Cyclic.integral_markCount_conditioned μ n (G (k n))

/-- The first clause of Assumption (M) says that the expected proportion of marked fringe
subtrees is asymptotic to `π_n` (source lines 235–237). -/
theorem microscopic_first_iff (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) :
    IsEquivalent (admissibleSizes μ)
      (fun n => (uniformFringeLaw μ n).real {T | G (k n) T}) (markProb μ G k) ↔
    IsEquivalent (admissibleSizes μ)
      (fun n => (∫ T, (markCount (G (k n)) T : ℝ) ∂conditioned μ n) / n) (markProb μ G k) := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have heq : (fun n => (uniformFringeLaw μ n).real {T | G (k n) T}) =ᶠ[admissibleSizes μ]
      (fun n => (∫ T, (markCount (G (k n)) T : ℝ) ∂conditioned μ n) / n) := by
    filter_upwards [hl (eventually_gt_atTop 0)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [integral_markCount_eq_mul_uniformFringeLaw, mul_div_cancel_left₀ _ hn']
  exact ⟨fun h => h.congr_left heq, fun h => h.congr_left heq.symm⟩

/-- **`U01`, uniform pair bound** (source lines 293–295): if `A_n(ℓ) ≤ b_n` for all `ℓ ≥ 1`
(eventually in `n`) and `b_n = o((n / M_n) π_n²)`, then Assumption (C) holds. -/
theorem nonClustering_of_uniform_pair_bound {μ : PMF ℕ} {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M) {b : ℕ → ℝ}
    (hb : ∀ᶠ n in admissibleSizes μ, ∀ ℓ : ℕ, 1 ≤ ℓ → pairProb μ G k n ℓ ≤ b n)
    (hbo : b =o[admissibleSizes μ] (fun n => (n : ℝ) / M n * markProb μ G k n ^ 2)) :
    NonClustering μ G k M := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  rw [NonClustering, isLittleO_iff]
  intro c hc
  filter_upwards [hb, hbo.bound hc, hl (eventually_ge_atTop 1)] with n hbn hcn hn1
  have hMpos : (0 : ℝ) < M n := by exact_mod_cast hM.pos n hn1
  have hπ : 0 ≤ markProb μ G k n := measureReal_nonneg
  have hsum0 : 0 ≤ ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ :=
    Finset.sum_nonneg fun ℓ _ => measureReal_nonneg
  have hg0 : 0 ≤ (n : ℝ) * markProb μ G k n ^ 2 := by positivity
  have hg0' : 0 ≤ (n : ℝ) / M n * markProb μ G k n ^ 2 := by positivity
  rw [Real.norm_of_nonneg hsum0, Real.norm_of_nonneg hg0]
  rw [Real.norm_of_nonneg hg0'] at hcn
  calc ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ G k n ℓ
      ≤ ∑ _ℓ ∈ Finset.Icc 1 (M n), b n :=
        Finset.sum_le_sum fun ℓ hℓ => hbn ℓ (Finset.mem_Icc.1 hℓ).1
    _ = M n * b n := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ M n * ‖b n‖ := mul_le_mul_of_nonneg_left (Real.le_norm_self _) hMpos.le
    _ ≤ M n * (c * ((n : ℝ) / M n * markProb μ G k n ^ 2)) :=
        mul_le_mul_of_nonneg_left hcn hMpos.le
    _ = c * ((n : ℝ) * markProb μ G k n ^ 2) := by field_simp

/-- `A_n(ℓ) ≤ 1`: the pair probabilities are bounded (the Bienaymé measure has mass at most one). -/
theorem pairProb_le_one (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) (n ℓ : ℕ) :
    pairProb μ G k n ℓ ≤ 1 := by
  refine (measureReal_mono (Set.subset_univ _)).trans ?_
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact bienayme_univ_le_one μ)

/-- **`U01`, uniform pair bound, supremum form** (source lines 293–295): if
`sup_{ℓ ≥ 1} A_n(ℓ) = o((n / M_n) π_n²)`, then Assumption (C) holds. -/
theorem nonClustering_of_iSup_pairProb {μ : PMF ℕ} {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hsup : (fun n => ⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ}, pairProb μ G k n ℓ) =o[admissibleSizes μ]
      (fun n => (n : ℝ) / M n * markProb μ G k n ^ 2)) :
    NonClustering μ G k M := by
  refine nonClustering_of_uniform_pair_bound hM (Eventually.of_forall fun n ℓ hℓ => ?_) hsup
  have hbdd : BddAbove (Set.range fun ℓ : {ℓ : ℕ // 1 ≤ ℓ} => pairProb μ G k n ℓ) :=
    ⟨1, by rintro _ ⟨ℓ, rfl⟩; exact pairProb_le_one μ G k n ℓ⟩
  exact le_ciSup (f := fun ℓ : {ℓ : ℕ // 1 ≤ ℓ} => pairProb μ G k n ℓ) hbdd ⟨ℓ, hℓ⟩

/-- The polynomial cutoff satisfies `M_n ≤ n^{1-η}` for `n ≥ 1`. -/
theorem max_one_floor_rpow_le {η : ℝ} (hη : η < 1) {n : ℕ} (hn : 1 ≤ n) :
    ((max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 - η) := by
  have hx1 : 1 ≤ (n : ℝ) ^ (1 - η) := Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  rcases le_total 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ with h | h
  · rw [max_eq_right h]
    exact Nat.floor_le (by linarith)
  · rw [max_eq_left h, Nat.cast_one]
    exact hx1

/-- **The convenient sufficient criterion** (source lines 359–364). Let `ρ_j` be decompositions as
in Assumption (S) (at every mark of positive probability) with `E_{k_n}[C_{k_n} + L_{k_n}] =
n^{o(1)}`, and assume `sup_{ℓ ≥ 1} A_n(ℓ) ≤ n^{o(1)} π_n²`. Then for every fixed
`η ∈ (0, 1 - 1/α)`, the hypotheses of Theorem 1.1 hold with `M_n = ⌊n^{1-η}⌋`: `M` is a cutoff
sequence, and Assumptions (M) and (C) hold along `(k_n)` with respect to `M`. -/
theorem hypotheses_of_convenient_criterion {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (hμ : StableDomain μ α a) {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (ρ : ℕ → Measure (PlaneTree × ℕ × List PlaneTree))
    (hρ : ∀ j, 0 < bienayme μ {T | G j T} → Skeleton μ (G j) (ρ j))
    (hmom : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂ρ (k n) ≤
        ENNReal.ofReal ((n : ℝ) ^ δ))
    (hpair : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, ∀ ℓ : ℕ, 1 ≤ ℓ →
      pairProb μ G k n ℓ ≤ (n : ℝ) ^ δ * markProb μ G k n ^ 2)
    {η : ℝ} (hη : 0 < η ∧ η < 1 - 1 / α) :
    IsCutoff (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) ∧
      Microscopic μ G k (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) ∧
      NonClustering μ G k (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) := by
  have hT := Stable.stableToolkit hμ
  have hα : 0 < 1 / α := hT.rho_pos
  have hη1 : η < 1 := by linarith
  have hM := Bridge.isCutoff_max_one_floor_rpow hη.1 hη1
  refine ⟨hM, Bridge.microscopic_of_structural hT hM (Bridge.critM hT hη ρ hρ hmom), ?_⟩
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hη2 : 0 < η / 2 := half_pos hη.1
  refine nonClustering_of_uniform_pair_bound hM (b := fun n => (n : ℝ) ^ (η / 2) *
    markProb μ G k n ^ 2) (hpair (η / 2) hη2) ?_
  rw [isLittleO_iff]
  intro c hc
  -- `n^{-η/2} ≤ c` eventually
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(η / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hη2).comp tendsto_natCast_atTop_atTop
  filter_upwards [hl (ht.eventually (ge_mem_nhds hc)), hl (eventually_ge_atTop 1)] with n hcn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set M : ℕ := max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊ with hMdef
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM.pos n hn1
  have hMle : (M : ℝ) ≤ (n : ℝ) ^ (1 - η) := max_one_floor_rpow_le hη1 hn1
  have hπ2 : 0 ≤ markProb μ G k n ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  -- `n^{η/2} M_n ≤ n^{1-η/2} = n · n^{-η/2} ≤ c n`
  have hkey : (n : ℝ) ^ (η / 2) * M ≤ c * n := by
    calc (n : ℝ) ^ (η / 2) * M ≤ (n : ℝ) ^ (η / 2) * (n : ℝ) ^ (1 - η) :=
          mul_le_mul_of_nonneg_left hMle (by positivity)
      _ = (n : ℝ) ^ (-(η / 2)) * n := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add_one hn0.ne']
          ring_nf
      _ ≤ c * n := mul_le_mul_of_nonneg_right hcn hn0.le
  calc (n : ℝ) ^ (η / 2) * markProb μ G k n ^ 2
      = ((n : ℝ) ^ (η / 2) * M) * (markProb μ G k n ^ 2 / M) := by field_simp
    _ ≤ (c * n) * (markProb μ G k n ^ 2 / M) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = c * ((n : ℝ) / M * markProb μ G k n ^ 2) := by ring

/-- The convenient criterion combined with Theorem 1.1 (source lines 359–364): under its
hypotheses, both conclusions of Theorem 1.1 hold. -/
theorem poisson_of_convenient_criterion (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    {α : ℝ} {a : ℕ → ℝ} (hμ : StableDomain μ α a) {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (ρ : ℕ → Measure (PlaneTree × ℕ × List PlaneTree))
    (hρ : ∀ j, 0 < bienayme μ {T | G j T} → Skeleton μ (G j) (ρ j))
    (hmom : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂ρ (k n) ≤
        ENNReal.ofReal ((n : ℝ) ^ δ))
    (hpair : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, ∀ ℓ : ℕ, 1 ≤ ℓ →
      pairProb μ G k n ℓ ≤ (n : ℝ) ^ δ * markProb μ G k n ^ 2) :
    PoissonApproximationConclusion μ G k := by
  -- some `η ∈ (0, 1 - 1/α)` exists since `α > 1`
  have hT := Stable.stableToolkit hμ
  have hρ1 : 1 / α < 1 := hT.rho_lt_one
  have hη : 0 < (1 - 1 / α) / 2 ∧ (1 - 1 / α) / 2 < 1 - 1 / α := ⟨by linarith, by linarith⟩
  exact h1 μ ⟨α, a, hμ⟩ G k ⟨_, hypotheses_of_convenient_criterion hμ ρ hρ hmom hpair hη⟩

end PoissonDeclumping.DirectApplications
