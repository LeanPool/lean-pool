/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.DirectApplications.Criteria
public import LeanPool.RareSubtreePatterns.Patterns.NonFringe
public import LeanPool.RareSubtreePatterns.Applications.TreeCriteria
public import LeanPool.RareSubtreePatterns.Stable.Lattice

/-!
# Raw non-fringe counts: Corollary `cor:Non-fringe Poisson`

Source lines 1366–1445 (Corollary 3.8 and its proof; inventory C3.8, U06, P06).

For plane trees `T_k` the marks are `G_k(T) = 1{T_k ≺ T}` (`Embeds (Tk k) T`), with
`L_k = #{leaves of T_k}` (`leafCount`) and `C_k = k - L_k` (`internalCount (Tk k)` when
`|T_k| = k`).

* `structuralMicroscopic_embeds` (**P06, first part**): if `C_{k_n} = o(M_n)` and
  `L_{k_n} = o(a_{M_n})`, then Assumption (S) holds along `(k_n)` with respect to `(M_n)`, with
  the decomposition of U06 (`PlaneTree.skeleton_embeds`: conditionally on `T_k ≺ 𝒯`, `𝒯` is
  `T_k` with independent unconditioned Bienaymé trees grafted on its `L_k` leaves, so `C`
  and `L` are deterministic). For every `ε > 0`, `a_n P_{k_n}(C_{k_n} > ε M_n) = 0` for all
  large `n`, and `E_{k_n}[L_{k_n}] / a_{M_n} = L_{k_n} / a_{M_n} → 0`.
* The uniform two-point condition implies the summed condition (C)
  (**P06, second part**): `nonClustering_of_iSup_pairProb` (in `Criteria`).
* `nonfringe_poisson_of_general`: Theorem 1.1's conclusion under the three conditions,
  without the aperiodicity, `|T_k| = k` and `k_n → ∞` hypotheses (the proof does not use them
  once `C_k` is the number of internal vertices).
* `nonfringe_poisson_of` (**Corollary `cor:Non-fringe Poisson`**, with exactly the paper's
  hypotheses, including aperiodicity `Stable.latticeSpan μ = 1`, which the proof does not use).

The hypotheses `C_{k_n} = o(M_n)`, `L_{k_n} = o(a_{M_n})` and
`sup_ℓ A_n(ℓ) = o((n / M_n) π_n²)` are stated along admissible sizes (for aperiodic `μ` these are
all large `n`). Conclusion (ii) also contains `N_n → ∞` in probability (Theorem 1.1(ii)).
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.DirectApplications

open PlaneTree

/-- Under the decomposition of U06, the core size `C` exceeds `x` with probability zero when
`x ≥ C_k`: `C = internalCount T'` is deterministic. -/
theorem embedsSkeletonLaw_core_gt_eq_zero (μ : PMF ℕ) (T' : PlaneTree) {x : ℝ}
    (hx : (internalCount T' : ℝ) ≤ x) :
    (embedsSkeletonLaw μ T').real {ω | x < ω.2.1} = 0 := by
  rw [measureReal_def, embedsSkeletonLaw_apply]
  have hempty : {T : PlaneTree | (T, internalCount T', leafTrees T' T) ∈
      {ω : PlaneTree × ℕ × List PlaneTree | x < ω.2.1}} = ∅ := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hx
  rw [hempty, measure_empty, ENNReal.toReal_zero]

/-- Under the decomposition of U06, `E[L] ≤ L_k`: the number of grafted trees is `leafCount T'`
almost surely. -/
theorem lintegral_length_embedsSkeletonLaw_le (μ : PMF ℕ) (T' : PlaneTree) :
    ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂embedsSkeletonLaw μ T' ≤ leafCount T' := by
  calc ∫⁻ ω, (ω.2.2.length : ℝ≥0∞) ∂embedsSkeletonLaw μ T'
      = ∫⁻ _ω, (leafCount T' : ℝ≥0∞) ∂embedsSkeletonLaw μ T' := by
        refine lintegral_congr_ae ?_
        filter_upwards [embedsSkeletonLaw_ae μ T'] with ω hω
        rw [hω.2.1]
    _ = leafCount T' * embedsSkeletonLaw μ T' Set.univ := lintegral_const _
    _ ≤ leafCount T' * 1 := by
        gcongr
        rw [embedsSkeletonLaw_apply]
        exact cond_univ_le_one _ _
    _ = leafCount T' := mul_one _

/-- **P06, first part** (source lines 1437–1441): for the marks `G_k = 1{T_k ≺ ·}`, the
deterministic skeleton conditions `C_{k_n} = o(M_n)` and `L_{k_n} = o(a_{M_n})` imply
Assumption (S) along `(k_n)` with respect to `(M_n)`. -/
theorem structuralMicroscopic_embeds {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (hμ : StableDomain μ α a) (Tk : ℕ → PlaneTree) {k M : ℕ → ℕ} (hM : IsCutoff M)
    (hC : (fun n => (internalCount (Tk (k n)) : ℝ)) =o[admissibleSizes μ] (fun n => (M n : ℝ)))
    (hL : (fun n => (leafCount (Tk (k n)) : ℝ)) =o[admissibleSizes μ] (fun n => a (M n))) :
    StructuralMicroscopic μ a (fun j T => Embeds (Tk j) T) k M := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  refine ⟨fun j => embedsSkeletonLaw μ (Tk j),
    fun j hpos => skeleton_embeds hμ.critical hμ.nondegenerate hpos, fun ε hε => ?_, ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hC.bound hε] with n hn
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    rw [embedsSkeletonLaw_core_gt_eq_zero μ _ hn, mul_zero]
  · have hpos : ∀ᶠ n in admissibleSizes μ, 0 < a (M n) := by
      filter_upwards [hl (eventually_ge_atTop 1)] with n hn
      exact hμ.pos _ (hM.pos n hn)
    have hlim : Tendsto (fun n => ENNReal.ofReal ((leafCount (Tk (k n)) : ℝ) / a (M n)))
        (admissibleSizes μ) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal hL.tendsto_div_nhds_zero
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [hpos] with n hn
    rw [ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_natCast]
    exact ENNReal.div_le_div_right (lintegral_length_embedsSkeletonLaw_le μ _) _

/-- Corollary 3.8 in the generality of its proof: for patterns `T_k` with `C_{k_n} = o(M_n)`
internal vertices, `L_{k_n} = o(a_{M_n})` leaves and the uniform two-point condition
`sup_{ℓ ≥ 1} P(|𝒯| ≥ ℓ+1, T_{k_n} ≺ 𝒯, T_{k_n} ≺ 𝒯_{u_{ℓ+1}(𝒯)}) = o((n / M_n) π_n²)`,
both conclusions of Theorem 1.1 hold for `#{u ∈ 𝒯^n : T_{k_n} ≺ 𝒯^n_u}`. -/
theorem nonfringe_poisson_of_general (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    {α : ℝ} {a : ℕ → ℝ} (hμ : StableDomain μ α a) (Tk : ℕ → PlaneTree) {k M : ℕ → ℕ}
    (hM : IsCutoff M)
    (hC : (fun n => (internalCount (Tk (k n)) : ℝ)) =o[admissibleSizes μ] (fun n => (M n : ℝ)))
    (hL : (fun n => (leafCount (Tk (k n)) : ℝ)) =o[admissibleSizes μ] (fun n => a (M n)))
    (hsup : (fun n => ⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
        pairProb μ (fun j T => Embeds (Tk j) T) k n ℓ) =o[admissibleSizes μ]
      (fun n => (n : ℝ) / M n * markProb μ (fun j T => Embeds (Tk j) T) k n ^ 2)) :
    PoissonApproximationConclusion μ (fun j T => Embeds (Tk j) T) k :=
  h1 μ ⟨α, a, hμ⟩ _ k ⟨M, hM,
    Bridge.microscopic_of_structural (Stable.stableToolkit hμ) hM
      (structuralMicroscopic_embeds hμ Tk hM hC hL),
    nonClustering_of_iSup_pairProb hM hsup⟩

/-- **Corollary `cor:Non-fringe Poisson`** (source lines 1387–1422), from Theorem 1.1, with the
paper's hypotheses: `μ` critical, aperiodic, in the domain of attraction of an `α`-stable law
(normalizing sequence `a`); plane trees `T_k` with `|T_k| = k` (`k ≥ 1`), `L_k` leaves and
`C_k = k - L_k`; `k_n → ∞`; a cutoff `(M_n)` with `C_{k_n} = o(M_n)`, `L_{k_n} = o(a_{M_n})` and
`sup_{ℓ ≥ 1} P(|𝒯| ≥ ℓ+1, T_{k_n} ≺ 𝒯, T_{k_n} ≺ 𝒯_{u_{ℓ+1}(𝒯)}) = o((n / M_n) π_n²)`, where
`π_n = P(T_{k_n} ≺ 𝒯)`. Then (i) bounded `n π_n` gives
`d_TV(#{u : T_{k_n} ≺ 𝒯^n_u}, Po(n π_n)) → 0` and (ii) `n π_n → ∞` gives
`#{u : T_{k_n} ≺ 𝒯^n_u} / (n π_n) → 1` in probability (and the count tends to infinity). -/
theorem nonfringe_poisson_of (h1 : PoissonApproximationStatement) {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) (_haper : Stable.latticeSpan μ = 1)
    (Tk : ℕ → PlaneTree) (hTk : ∀ j : ℕ, 1 ≤ j → (Tk j).vertexCount = j) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) {M : ℕ → ℕ} (hM : IsCutoff M)
    (hC : (fun n => ((k n - leafCount (Tk (k n)) : ℕ) : ℝ)) =o[admissibleSizes μ]
      (fun n => (M n : ℝ)))
    (hL : (fun n => (leafCount (Tk (k n)) : ℝ)) =o[admissibleSizes μ] (fun n => a (M n)))
    (hsup : (fun n => ⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
        pairProb μ (fun j T => Embeds (Tk j) T) k n ℓ) =o[admissibleSizes μ]
      (fun n => (n : ℝ) / M n * markProb μ (fun j T => Embeds (Tk j) T) k n ^ 2)) :
    PoissonApproximationConclusion μ (fun j T => Embeds (Tk j) T) k := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  refine nonfringe_poisson_of_general h1 hμ Tk hM (hC.congr' ?_ EventuallyEq.rfl) hL hsup
  filter_upwards [hl (hk.eventually_ge_atTop 1)] with n hn
  have h := leafCount_add_internalCount (Tk (k n))
  rw [hTk _ hn] at h
  congr 1
  omega

end PoissonDeclumping.DirectApplications
