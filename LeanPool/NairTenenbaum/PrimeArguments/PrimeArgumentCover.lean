/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.PrimeArguments.PrimeArgumentBands
public import LeanPool.NairTenenbaum.Smooth.PrimeBandCover

/-! # Covering the fourth class at prime arguments by logarithmic bands -/

@[expose] public section

namespace NairTenenbaum

/-- The intermediate-prefix contribution restricted to prime arguments above the scale. -/
noncomputable def PolynomialSystem.primeIntermediatePrefixContribution {k r : ℕ}
    (P : PolynomialSystem k r) (F : ArithmeticMap k) (N : ℕ+)
    (X w₀ x u : ℝ) (a b : ℤ) : ℝ := by
  classical
  exact ∑ t ∈ (Finset.Ioc a b).filter
    (fun t => P.HasIntermediatePrefix N X w₀ x u t ∧ t.natAbs.Prime ∧ x < t.natAbs),
    extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs)

theorem PolynomialSystem.primeIntermediatePrefixContribution_le_bands {k r : ℕ} (P :
    PolynomialSystem k r)
    {F : ArithmeticMap k} (hF : ∀ n, 0 ≤ F n) (N : ℕ+) (X w₀ x u : ℝ) (a b : ℤ)
    (hx : 1 < x) (hw₀ : 1 ≤ w₀) (hu : 0 ≤ u) (hu₁ : u ≤ 1) :
    ∃ J : Finset ℕ, (∀ j ∈ J, w₀ < x ^ (2 * (u / 2 ^ (j + 1)))) ∧
      P.primeIntermediatePrefixContribution F N X w₀ x u a b ≤
        ∑ j ∈ J, P.primeSmoothTailPrefixContribution F N
          (Finset.Icc 0 ⌊x ^ (2 * (u / 2 ^ (j + 1)))⌋₊) X a b (x ^ (u / 2 ^ (j + 1))) := by
  classical
  let T := (Finset.Ioc a b).filter (fun t => P.HasIntermediatePrefix N X w₀ x u t ∧ t.natAbs.Prime
      ∧ x < t.natAbs)
  apply exists_finset_sum_le_cover T
    (fun j => (Finset.Ioc a b).filter (fun t => P.HasSmoothTailPrefix N (Finset.Icc 0 ⌊x ^ (2 * (u /
      2 ^ (j + 1)))⌋₊)
        X (x ^ (u / 2 ^ (j + 1))) t ∧ t.natAbs.Prime ∧
        x ^ (u / 2 ^ (j + 1)) < t.natAbs))
    (fun j => w₀ < x ^ (2 * (u / 2 ^ (j + 1))))
    (fun t => extendArithmeticMap F (fun j => ((P.Q j).eval t).natAbs))
    (fun _ => extendArithmeticMap_nonneg hF _)
  intro t ht
  obtain ⟨j, hj, hprefix⟩ := ((Finset.mem_filter.mp ht).2.1).exists_band hx hw₀
  have hα : u / 2 ^ (j + 1) ≤ 1 :=
    (div_le_self hu (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hu₁
  have hzx : x ^ (u / 2 ^ (j + 1)) ≤ x := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx.le hα
  exact ⟨j, hj, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht).1, hprefix,
    (Finset.mem_filter.mp ht).2.2.1, hzx.trans_lt (Finset.mem_filter.mp ht).2.2.2⟩⟩

theorem exists_primeIntermediatePrefixContribution_value_bound {g : ℕ} (hg : 0 < g)
    {ε A c : ℝ} (hε : 0 < ε) (hsmall : (g : ℝ) ^ 2 * ε ≤ 1 / 8)
    (hA : 1 ≤ A) (hc : 0 ≤ c) :
    ∃ K x₀ κ w₀ : ℝ, 0 < K ∧ 1 < x₀ ∧ 0 < κ ∧ 1 < w₀ ∧
      ∀ (k r : ℕ) (P : PolynomialSystem k r), P.total.natDegree = g → P.total.eval 0 ≠ 0 →
      ∀ (B σ : ℝ) (F : ArithmeticMap k), Admissible A B σ F → 1 ≤ B → 0 < σ →
      (g : ℝ) ^ 2 * σ ≤ 1 / 8 → ∀ (x y : ℝ) (N : ℕ+) (a b : ℤ), x₀ ≤ x →
      (N : ℝ) ≤ x ^ (3 * (g : ℝ) ^ 2 * ε) → x ^ (4 * (g : ℝ) ^ 2 * ε) ≤ y →
      a ≤ b → y / 2 ≤ (b : ℝ) - a → (b : ℝ) - a ≤ 2 * y →
      (∀ t ∈ Finset.Ioc a b, ((P.total.eval t).natAbs : ℝ) ≤ x ^ c) →
      P.primeIntermediatePrefixContribution F N (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) w₀ x
        ((g : ℝ) * ε / 16) a b ≤
        K * primeArgumentTailSieveCost A B κ g P.badDiscriminant * primeMainTerm P F x y := by
  have hg₁ : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hu : 0 < (g : ℝ) * ε / 16 := by positivity
  have hu₁ : (g : ℝ) * ε / 16 ≤ 1 := by
    nlinarith [mul_nonneg hε.le (mul_nonneg (show (0 : ℝ) ≤ g by positivity)
      (sub_nonneg.mpr hg₁))]
  obtain ⟨K, x₁, κ, w₀, hK, _, hκ, hw₀, H⟩ := exists_primeArgumentBands_mainTerm_bound hg hε hA hc
  let x₀ : ℝ := max x₁ (Real.exp 1)
  have hxx₀ : Real.exp 1 ≤ x₀ := le_max_right _ _
  have hx₀ : 1 < x₀ := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hxx₀
  refine ⟨K, x₀, κ, w₀, hK, hx₀, hκ, hw₀, ?_⟩
  intro k r P hdeg hzero B σ F hF hB hσ hσsmall x y N a b hxx hN hy hab hlen hlen' hvalue
  have hx : 1 < x := hx₀.trans_le hxx
  have hlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hxx₀.trans hxx)
  obtain ⟨J, hJ, HJ⟩ := P.primeIntermediatePrefixContribution_le_bands hF.nonneg N
    (x ^ (3 * (g : ℝ) ^ 2 * ε / 2)) w₀ x ((g : ℝ) * ε / 16) a b hx hw₀.le hu.le hu₁
  exact HJ.trans (H k r P hdeg hzero B σ F hF hB hσ hσsmall x y ((g : ℝ) * ε / 16) N a b J
    ((le_max_left _ _).trans hxx) hx hlog hu hu₁ le_rfl (fun j hj => (hJ j hj).le)
    hN hy hab hlen hlen' hvalue)

end NairTenenbaum
