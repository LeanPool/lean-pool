/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentBand
public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentTailMajorant
public import LeanPool.NairTenenbaum.Smooth.PrimeBandContribution

/-! # The weighted contribution of a smooth prefix at prime arguments -/

@[expose] public section

namespace NairTenenbaum

/-- The contribution of smooth prefixes above the mass cutoff at prime arguments. -/
noncomputable def PolynomialSystem.primeSmoothTailPrefixContribution {k r : ℕ} (P :
    PolynomialSystem k r)
    (F : ArithmeticMap k) (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) (z : ℝ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter (fun t => P.HasSmoothTailPrefix N s X z t ∧ t.natAbs.Prime ∧
      z < t.natAbs),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

/-- The contribution uses existence of a suitable prefix and does not depend on
any particular choice of witnesses. -/
theorem PolynomialSystem.primeSmoothTailPrefixContribution_le {k r : ℕ} (P : PolynomialSystem k r)
    {A B σ : ℝ} {F : ArithmeticMap k} (hF : Admissible A B σ F) (hA : 1 ≤ A) (hB : 0 ≤ B)
    (g : ℕ) (N : ℕ+) (s : Finset ℕ) (X : ℝ) (a b : ℤ) {x α c : ℝ} (hx : 1 < x) (hα : 0 < α)
    (hvalue : ∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) :
    P.primeSmoothTailPrefixContribution F N s X a b (x ^ α) ≤
      A ^ (c / α) * P.primeSmoothTailSiftedSum F g N s X a b (x ^ α) := by
  classical
  let T := (Finset.Ioc a b).filter (fun t => P.HasSmoothTailPrefix N s X (x ^ α) t ∧
      t.natAbs.Prime ∧ x ^ α < t.natAbs)
  choose! n q hn using fun t (ht : t ∈ T) => (Finset.mem_filter.mp ht).2.1
  exact P.sum_primeRoughSmoothTailPrefix_le hF hA hB g N s X a b T n q (Finset.filter_subset _ _)
    (fun t ht => (hn t ht).1) hx hα
    (fun t ht => (Finset.mem_filter.mp ht).2.2.1)
    (fun t ht => (Finset.mem_filter.mp ht).2.2.2) (fun t ht => (hn t ht).2.2.2.2)
    (fun t ht => (hn t ht).2.1) (fun t ht => (hn t ht).2.2.1)
    (fun t ht => (hn t ht).2.2.2.1) (fun t ht => hvalue t (Finset.mem_filter.mp ht).1)

/-- Uniform one-band bound for the original arithmetic weights, rather than
just the selected divisor weights. -/
theorem exists_primeArgumentBandContribution_mainTerm_bound {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K x₀ : ℝ, 0 < K ∧ 1 ≤ x₀ ∧ ∀ (k r : ℕ) (P : PolynomialSystem k r),
      P.total.natDegree = g → P.total.eval 0 ≠ 0 → ∀ (A B σ κ c : ℝ) (F : ArithmeticMap k),
      Admissible A B σ F → 1 ≤ A → 1 ≤ B → 0 < σ → 0 ≤ κ → (g : ℝ) ^ 2 * σ ≤ 1 / 8 →
      c * Real.log A + 4 * (g : ℝ) * Real.log 4 + 2 ≤ κ * (3 * (g : ℝ) ^ 2 * ε / 2) / 2 →
      ∀ (x y α : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x → 1 < x → 1 ≤ Real.log x →
      0 < α → 2 * α ≤ 1 → α ≤ (g : ℝ) * ε / 16 →
      2 ≤ x ^ α → 2 * (g : ℝ) ≤ x ^ α → 16 ≤ Real.log (x ^ α) →
      8 * (g : ℝ) ^ 2 * κ ≤ Real.log (x ^ (2 * α)) →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.primeSmoothTailPrefixContribution F N (Finset.Icc 0 ⌊x ^ (2 * α)⌋₊)
        (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) a b (x ^ α) ≤
        K * primeArgumentTailSieveCost A B κ g P.badDiscriminant * Real.exp (-1 / α) *
            primeMainTerm P F x y := by
  obtain ⟨K, x₀, hK, hx₀, H⟩ := exists_primeArgumentBandSiftedSum_mainTerm_bound hg hε
  refine ⟨K, x₀, hK, hx₀, ?_⟩
  intro k r P hdeg hzero A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
    x y α N a b hxx hx hlog hα hα₁ hαcut hz hgz hzlog hwlog hN hy hab hlen hlen' hvalue
  exact (P.primeSmoothTailPrefixContribution_le hF hA (zero_le_one.trans hB) g N _ _ a b hx hα
      hvalue).trans
    (H k r P hdeg hzero A B σ κ c F hF hA hB hσ hκ hσsmall hdecay
      x y α N a b hxx hx hlog hα hα₁ hαcut hz hgz hzlog hwlog hN hy hab hlen hlen')

end NairTenenbaum
