/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.RootDeclumping.ParentFormula
public import LeanPool.RareSubtreePatterns.Statements.Main

/-!
# Lemma `lem:root_declumping`(i),(ii) in the paper's notation

Source lines 2197–2229. This restates the general results of
`PoissonDeclumping.RootDeclumping.ParentFormula` with the paper's objects: the sequence
`π_n = P(G_{k_n}(𝒯) = 1) = markProb μ G k n`, the declumped marks
`Ghat_k = declumpedMark B G_k`, the constant `c_B = cB μ B` of `Statements.Main` (an extended
nonnegative real, finite for critical `μ`), and limits along admissible sizes
(`admissibleSizes μ`).

Part (iii) (raw Assumption (S) implies declumped Assumption (M)) needs forest and local-limit
estimates and is not proved here.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PoissonDeclumping
namespace RootDeclumping

open PlaneTree LeafHeight

variable {μ : PMF ℕ}

/-- For critical `μ`, the constant `c_B` of `Statements.Main` is finite. -/
theorem cB_ne_top (hc : IsCritical μ) (B : Set ℕ) : cB μ B ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc cB μ B ≤ ∑' j : ℕ, (j : ℝ≥0∞) * μ j :=
        ENNReal.tsum_le_tsum fun j => Set.indicator_le_self _ _ j
    _ = 1 := hc

/-- The real value of the constant `c_B` of `Statements.Main` is `cBReal μ B = ∑_{j ∈ B} j μ_j`
(for critical `μ`, `c_B` is finite by `cB_ne_top`). -/
theorem cBReal_eq_toReal_cB (B : Set ℕ) :
    cBReal μ B = (cB μ B).toReal := by
  have hfin : ∀ j, B.indicator (fun j => (j : ℝ≥0∞) * μ j) j ≠ ∞ := fun j =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top j) (μ.apply_ne_top j))
      (Set.indicator_le_self _ _ j)
  rw [cB, ENNReal.tsum_toReal_eq hfin, cBReal]
  refine tsum_congr fun j => ?_
  by_cases hj : j ∈ B
  · simp [Set.indicator_of_mem hj, ENNReal.toReal_mul, mass]
  · simp [Set.indicator_of_notMem hj]

theorem cB_pos_iff (hc : IsCritical μ) (B : Set ℕ) : 0 < cB μ B ↔ 0 < cBReal μ B := by
  rw [cBReal_eq_toReal_cB, ENNReal.toReal_pos_iff]
  exact ⟨fun h => ⟨h, (cB_ne_top hc B).lt_top⟩, fun h => h.1⟩

/-- **Lemma `lem:root_declumping`, first assertion and parts (i), (ii)** (source lines
2197–2229). Let `μ` be critical with `μ_1 ≠ 1`, `(G_k)` marks, `(k_n)` a sequence, and
`B ⊆ ℕ` with `c_B > 0` (the standing assumption `c_B ∈ (0, ∞)` of Section 5; finiteness is
automatic). Then `b_B = P(k_∅(𝒯) ∈ B, k_∅(𝒯) ≥ 1) > 0`, `π̂_n ≥ b_B π_n` for every `n`, and,
along admissible sizes:
(i) if `(n π_n)` is bounded, then `n π̂_n - c_B n π_n → 0`;
(ii) if `n π_n → ∞`, then `n π̂_n → ∞`. -/
theorem lem_root_declumping (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (G : ℕ → PlaneTree → Prop)
    (k : ℕ → ℕ) (B : Set ℕ) (hB : 0 < cB μ B) :
    bB μ B = (bienayme μ).real {T | T.rootDegree ∈ B ∧ 1 ≤ T.rootDegree} ∧ 0 < bB μ B ∧
    (∀ n, bB μ B * markProb μ G k n ≤ markProb μ (fun j => declumpedMark B (G j)) k n) ∧
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      Tendsto (fun n : ℕ => (n : ℝ) * markProb μ (fun j => declumpedMark B (G j)) k n -
        (cB μ B).toReal * ((n : ℝ) * markProb μ G k n)) (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop →
      Tendsto (fun n : ℕ => (n : ℝ) * markProb μ (fun j => declumpedMark B (G j)) k n)
        (admissibleSizes μ) atTop) := by
  have hbpos : 0 < bB μ B := (bB_pos_iff_cBReal_pos hc B).mpr ((cB_pos_iff hc B).mp hB)
  have hx : Tendsto (fun n : ℕ => (n : ℝ)) (admissibleSizes μ) atTop :=
    tendsto_natCast_atTop_atTop.mono_left inf_le_left
  refine ⟨bB_eq_prob hc h1 B, hbpos, fun n => bB_mul_le_declumped hc h1 B (G (k n)),
    fun hbdd => ?_, fun hdiv => ?_⟩
  · rw [← cBReal_eq_toReal_cB]
    exact root_declumping_bounded hc h1 B (fun n => G (k n)) (fun n => (n : ℝ)) hx hbdd
  · exact root_declumping_divergent hc h1 B hbpos (fun n => G (k n)) (fun n => (n : ℝ)) hdiv

end RootDeclumping
end PoissonDeclumping
