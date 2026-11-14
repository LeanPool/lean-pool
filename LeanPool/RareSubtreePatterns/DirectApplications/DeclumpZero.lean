/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Main
public import LeanPool.RareSubtreePatterns.Bridge.Microscopic
public import LeanPool.RareSubtreePatterns.Declumping.Conditioned
public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof

/-!
# Corollary `cor:declump_zero`: raw zero events from declumped Poisson approximation

Source lines 2403–2422 (inventory C5.3). Under the hypotheses of Theorem 1.2
(`thm:PoissonApproximation2`), the propagation property of Lemma `lem:declump_to_raw` and
`π_n = P(G_{k_n}(𝒯) = 1) = O(1/n)`, the raw count `N_{k_n}(𝒯^n) = #{u : G_{k_n}(𝒯^n_u) = 1}`
satisfies `P(N_{k_n}(𝒯^n) = 0) - exp(-c_B n π_n) → 0`.

Theorem 1.2 is taken as the explicit hypothesis `h2 : PoissonApproximation2Statement` (the
paper's own theorem, proved elsewhere); the proof is the paper's three-line argument:

* `π_n = O(1/n)` gives a bounded mean `n π_n`, so Theorem 1.2(i) gives the declumped Poisson
  approximation with parameter `c_B n π_n`;
* Corollary `cor:SM`(iii) (`Bridge.conditioned_mark_tendsto_zero`) gives
  `P(G_{k_n}(𝒯^n) = 1) → 0`;
* Lemma `lem:declump_to_raw` (`PlaneTree.conditioned_declump_to_raw`) compares the two zero
  events.

The constant is `c_B = (cB μ B).toReal`, which is the real number `∑_{j ∈ B} j μ_j` since
`0 < cB μ B < ∞` is assumed.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.DirectApplications

open PlaneTree

/-- `π_n = O(1/n)` along admissible sizes gives a bounded mean: eventually `n π_n ≤ C`. -/
theorem exists_eventually_mul_markProb_le_of_isBigO {μ : PMF ℕ} {G : ℕ → PlaneTree → Prop}
    {k : ℕ → ℕ} (hO : markProb μ G k =O[admissibleSizes μ] (fun n => 1 / (n : ℝ))) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C := by
  obtain ⟨C, hC⟩ := hO.bound
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  refine ⟨C, ?_⟩
  filter_upwards [hC, hl (eventually_gt_atTop 0)] with n hn hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp : 0 ≤ markProb μ G k n := measureReal_nonneg
  rw [Real.norm_of_nonneg hp, Real.norm_of_nonneg (by positivity)] at hn
  calc (n : ℝ) * markProb μ G k n ≤ n * (C * (1 / n)) := mul_le_mul_of_nonneg_left hn hn0'.le
    _ = C := by field_simp

/-- **Corollary `cor:declump_zero`** (source lines 2403–2422), from Theorem 1.2.
Assume the hypotheses of Theorem 1.2 (`(H_α)` with normalizing sequence `a`, a cutoff `M`,
`c_B ∈ (0, ∞)`, Assumption (S) for `(G_k)` and Assumption (C) for the declumped marks
`(Ghat_k)`, all along `(k_n)` with respect to `(M_n)`), the propagation property of Lemma
`lem:declump_to_raw` for every `k`, and `π_n = O(1/n)`. Then
`P(N_{k_n}(𝒯^n) = 0) - exp(-c_B n π_n) → 0` along admissible sizes. -/
theorem declump_zero_of (h2 : PoissonApproximation2Statement) {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ}
    (hM : IsCutoff M) {B : Set ℕ} (hB0 : 0 < cB μ B) (hBfin : cB μ B < ∞)
    (hS : StructuralMicroscopic μ a G k M)
    (hC : NonClustering μ (fun j => declumpedMark B (G j)) k M)
    (hprop : ∀ j, PropagatesOutside B (G j))
    (hO : markProb μ G k =O[admissibleSizes μ] (fun n => 1 / (n : ℝ))) :
    Tendsto (fun n : ℕ => (conditioned μ n).real {T | markCount (G (k n)) T = 0} -
      Real.exp (-((cB μ B).toReal * ((n : ℝ) * markProb μ G k n))))
      (admissibleSizes μ) (𝓝 0) := by
  have hT := Stable.stableToolkit hμ
  have htv := (h2 μ α a hμ G k M hM B hB0 hBfin hS hC).1
    (exists_eventually_mul_markProb_le_of_isBigO hO)
  have hroot := Bridge.conditioned_mark_tendsto_zero hT hM hS hO
  have h := conditioned_declump_to_raw μ B (fun n => G (k n))
    (fun n => Real.toNNReal ((cB μ B).toReal * ((n : ℝ) * markProb μ G k n)))
    (fun n => hprop (k n)) hroot htv
  refine h.congr fun n => ?_
  have hp : 0 ≤ markProb μ G k n := measureReal_nonneg
  rw [Real.coe_toNNReal _ (by positivity)]

end PoissonDeclumping.DirectApplications
