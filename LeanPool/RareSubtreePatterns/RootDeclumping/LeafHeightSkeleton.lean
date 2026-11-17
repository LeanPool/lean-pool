/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RootDeclumping.GenerationBranching
public import LeanPool.RareSubtreePatterns.RootDeclumping.LeafHeightGenerations
public import LeanPool.RareSubtreePatterns.Setup.Marks

/-!
# The skeleton decomposition for the leaf-height marks

The tree-law input of Lemma `lem:S_lh` (source lines 3066–3114, inventory P23) for the marks
`G_k(T) = 1{λ_∅(T) ≥ k}`. Under `P_k = P(· | λ_∅(𝒯) ≥ k)` put `C_k = Z_0 + ⋯ + Z_{k-1}`
(`skelSize`), `L_k = Z_k`, and let `𝒯^{(1)}, …, 𝒯^{(L_k)}` be the fringe subtrees rooted at
generation `k` (`gen k`). The law `lhSkeleton μ k` of `(𝒯, C_k, (𝒯^{(i)})_{i ≤ L_k})` under `P_k`
is a decomposition in the sense of Assumption (S) (`Skeleton`, `Setup.Marks`):

* `lhSkeleton_skeleton`: its first marginal is `P_k`; conditionally on `(C_k, L_k)` the trees
  `𝒯^{(i)}` are independent `μ`-Bienaymé trees (from `bienayme_trunc_mem_gen_eq`); and
  `|𝒯| = C_k + ∑_{i ≤ L_k} |𝒯^{(i)}|`;
* `lintegral_lhSkeleton_le`: `E_k[C_k + L_k] ≤ C k` (`κ = 1`, `k ≥ 1`) and `≤ C κ^k` (`κ ≥ 2`).

The remaining step of Lemma `lem:S_lh` (Lemma `lem:critM`, which needs the regular variation of
`(a_n)`, and Corollary `cor:SM`) is not proved here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping
namespace RootDeclumping

open PlaneTree LeafHeight

variable {μ : PMF ℕ}

variable (μ) in
/-- The law of `(𝒯, C_k(𝒯), (𝒯_v)_{|v| = k})` under `P(· | λ_∅(𝒯) ≥ k)`. -/
noncomputable def lhSkeleton (k : ℕ) : Measure (PlaneTree × ℕ × List PlaneTree) :=
  (cond (bienayme μ) {T | k ≤ rootLeafHeight T}).map fun T => (T, skelSize k T, gen k T)

theorem lintegral_lhSkeleton (k : ℕ) (F : PlaneTree × ℕ × List PlaneTree → ℝ≥0∞) :
    ∫⁻ ω, F ω ∂(lhSkeleton μ k) =
      ∫⁻ T, F (T, skelSize k T, gen k T) ∂(cond (bienayme μ) {T | k ≤ rootLeafHeight T}) :=
  lintegral_map Measurable.of_discrete Measurable.of_discrete

/-- `{λ_∅ ≥ k, C_k = c}` is determined by the truncation at height `k`. -/
theorem setOf_le_rootLeafHeight_skelSize_eq (k c : ℕ) (P : List PlaneTree → Prop) :
    {T : PlaneTree | k ≤ rootLeafHeight T} ∩ {T | skelSize k T = c ∧ P (gen k T)} =
      {T | trunc k T ∈ {S : PlaneTree | k ≤ rootLeafHeight S ∧ skelSize k S = c} ∧
        P (gen k T)} := by
  ext T
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, le_rootLeafHeight_trunc_iff, skelSize_trunc,
    and_assoc]

/-- **Assumption (S) decomposition for `G_k = 1{λ_∅ ≥ k}`** (source lines 3066–3083): for a
critical `μ` with `μ_1 ≠ 1` and every `k`, `lhSkeleton μ k` is a decomposition
`(𝒯, C_k, 𝒯^{(1)}, …, 𝒯^{(L_k)})` as in Assumption (S). -/
theorem lhSkeleton_skeleton (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (k : ℕ) :
    Skeleton μ (fun T => k ≤ rootLeafHeight T) (lhSkeleton μ k) := by
  have hne : bienayme μ {T | k ≤ rootLeafHeight T} ≠ 0 := by
    rw [bienayme_le_rootLeafHeight hc h1]
    exact (ENNReal.ofReal_pos.mpr (piSeq_pos hc h1 k)).ne'
  have := cond_isProbabilityMeasure (μ := bienayme μ) hne
  refine ⟨by rw [lhSkeleton]; infer_instance, ?_, ?_, ?_⟩
  · rw [lhSkeleton, Measure.map_map measurable_fst Measurable.of_discrete]
    exact Measure.map_id
  · intro c ts
    rw [lhSkeleton, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
      cond_apply MeasurableSet.of_discrete, cond_apply MeasurableSet.of_discrete, mul_assoc]
    congr 1
    have h1' := setOf_le_rootLeafHeight_skelSize_eq k c (fun l => l = ts)
    have h2' := setOf_le_rootLeafHeight_skelSize_eq k c (fun l => l.length = ts.length)
    simp only [Set.preimage_ofPred_eq] at h1' h2' ⊢
    rw [h1', h2']
    exact bienayme_trunc_mem_gen_eq hc h1 k _ ts
  · rw [lhSkeleton, ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete]
    exact Filter.Eventually.of_forall fun T => vertexCount_eq_skelSize_add k T

/-- **`E_k[C_k + L_k]` for the skeleton decomposition** (source lines 3108–3114): there is
`C > 0` with `E_k[C_k + L_k] ≤ C k` for `k ≥ 1` if `κ = 1`, and `≤ C κ^k` if `κ ≥ 2`. -/
theorem lintegral_lhSkeleton_le (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ C : ℝ, 0 < C ∧
      (kappa μ = 1 → ∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ((ω.2.1 + ω.2.2.length : ℕ) : ℝ≥0∞) ∂(lhSkeleton μ k) ≤
          ENNReal.ofReal (C * k)) ∧
      (2 ≤ kappa μ → ∀ k : ℕ,
        ∫⁻ ω, ((ω.2.1 + ω.2.2.length : ℕ) : ℝ≥0∞) ∂(lhSkeleton μ k) ≤
          ENNReal.ofReal (C * (kappa μ : ℝ) ^ k)) := by
  obtain ⟨C, hC, h1C, h2C⟩ := lintegral_skelSize_add_genCount_cond_le hc h1
  refine ⟨C, hC, fun hκ k hk => ?_, fun hκ k => ?_⟩
  · rw [lintegral_lhSkeleton]
    exact h1C hκ k hk
  · rw [lintegral_lhSkeleton]
    exact h2C hκ k

/-- The tree-law input of Lemma `lem:S_lh`, combined: for every `k` a decomposition as in
Assumption (S) for `G_k = 1{λ_∅ ≥ k}` exists, with `E_k[C_k + L_k] ≤ C k` (`κ = 1`, `k ≥ 1`)
or `≤ C κ^k` (`κ ≥ 2`) for one constant `C`. -/
theorem lem_S_lh_tree_input (hc : IsCritical μ) (h1 : μ 1 ≠ 1) :
    ∃ ρ : ℕ → Measure (PlaneTree × ℕ × List PlaneTree),
      (∀ k, Skeleton μ (fun T => k ≤ rootLeafHeight T) (ρ k)) ∧
      ∃ C : ℝ, 0 < C ∧
        (kappa μ = 1 → ∀ k : ℕ, 1 ≤ k →
          ∫⁻ ω, ((ω.2.1 + ω.2.2.length : ℕ) : ℝ≥0∞) ∂ρ k ≤ ENNReal.ofReal (C * k)) ∧
        (2 ≤ kappa μ → ∀ k : ℕ,
          ∫⁻ ω, ((ω.2.1 + ω.2.2.length : ℕ) : ℝ≥0∞) ∂ρ k ≤
            ENNReal.ofReal (C * (kappa μ : ℝ) ^ k)) :=
  ⟨lhSkeleton μ, lhSkeleton_skeleton hc h1, lintegral_lhSkeleton_le hc h1⟩

end RootDeclumping
end PoissonDeclumping
