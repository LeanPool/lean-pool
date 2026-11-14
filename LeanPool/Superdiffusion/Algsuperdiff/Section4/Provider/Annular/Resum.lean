/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Groups
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Resum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The annular resummation of the Section 4.1 chain

Local helpers for ABK26, Section 4.1, proof of Proposition
`p.mathcalE.annular.decomp`: the step the manuscript compresses into one
sentence, summing the five-term "ugly" estimate over the annular double sum
`sum_{j <= m} sum_{n <= j-1}` and composing the result with the Step-1
estimate.

Everything here is a proved *conditional* helper over abstract reals and
abstract real sequences.  The caller-supplied inequalities (the ugly estimate,
the Step-1 estimate, the four summability facts, the essential-sup prefactor)
are conditional A obligations, not source premises; no source node is claimed,
realized or closed by this module.

## Contents

* `annFam` / `annDouble` -- the guarded annular family over `Z x Z` and the
  guarded iterated double sum `sum_{j <= m} sum_{n <= j-1}`, with the bridge
  `tsum_annFam`.  Termwise comparisons live in the product reading; the
  iterated reading is what the Section 4.1 displays speak.
* `weight_collapse_one` / `weight_collapse_two` -- the two scale-weight
  collapses `3^(-2sq) 3^(sq) = 3^(-sq)` and
  `3^(-2sq) 3^((s+gamma)q) = 3^(-(s-gamma)q)`.
* `half_le_one_sub_threeRpow_neg` -- the elementary convexity input
  `1 - 3^(-x) >= x/2` on `(0,1]`, behind every `c^(-1)` geometric constant.
* `annWeightFam_tsum_le` -- the **annulus-multiplicity** weight sum
  `sum_{j <= m} sum_{n <= j-1} 3^(-c(m-n)) <= 4 c^(-2)`: for each scale `n`
  there are `m - n` annuli, so this double geometric sum is a
  polynomial-times-geometric quantity, and its `c^(-2)` blow-up is the origin of
  the `s^(-2)` prefactor of the fifth `pre.zero` term.
* `annularResum_core` / `annularResum` -- the resummation, over abstract
  weights and then at the manuscript's weights.
* `IsAnnularDecompPre` -- a local abbreviation for the Step-1 shape.
* `preZero_of_pre_and_ugly` -- the composition delivering the five-term
  `pre.zero` shape.

## The annulus multiplicity

Plugging the ugly estimate into the annular double sum costs a factor `m - n`
-- the number of annuli `j` in `[n+1, m]` -- on every term whose content does
not depend on the annulus index `j`.  The manuscript carries this multiplicity
explicitly in the two Step-3 displays (: the factors `m-n+1` and `(m-n+1)^2`)
and its fifth `pre.zero` term is stated with the compatible prefactor, but its
**second** (`sigma-bar` continuity) term is printed as a single sum, without
the multiplicity.  Nothing downstream breaks: the Step-3 consumer takes the
`sigma-bar` sum with a *free* constant `Csig`, and the multiplicity costs one
extra power of `(s - 2 gamma)^(-1)`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The guarded annular family and double sum -/

/-- The guarded annular family over `Z x Z`: supported on
`{(j,n) : j <= m, n <= j-1}`, the index region of every Section 4.1 annular
double sum. -/
def annFam (m : ℤ) (h : ℤ → ℤ → ℝ) : ℤ × ℤ → ℝ :=
  fun p => if p.1 ≤ m ∧ p.2 ≤ p.1 - 1 then h p.1 p.2 else 0

@[simp] theorem annFam_apply (m : ℤ) (h : ℤ → ℤ → ℝ) (j n : ℤ) :
    annFam m h (j, n) = if j ≤ m ∧ n ≤ j - 1 then h j n else 0 := rfl

/-- The guarded annular double sum `sum_{j <= m} sum_{n <= j-1} h j n`. -/
def annDouble (m : ℤ) (h : ℤ → ℤ → ℝ) : ℝ :=
  ∑' j : ℤ, (if j ≤ m then ∑' n : ℤ, (if n ≤ j - 1 then h j n else 0) else 0)

theorem annDouble_def (m : ℤ) (h : ℤ → ℤ → ℝ) :
    annDouble m h
      = ∑' j : ℤ, (if j ≤ m then ∑' n : ℤ, (if n ≤ j - 1 then h j n else 0) else 0) :=
  rfl

theorem annFam_nonneg {m : ℤ} {h : ℤ → ℤ → ℝ} (hh : ∀ j n, 0 ≤ h j n) (p : ℤ × ℤ) :
    0 ≤ annFam m h p := by
  simp only [annFam]
  split_ifs with hc
  · exact hh _ _
  · exact le_rfl

theorem annDouble_nonneg {m : ℤ} {h : ℤ → ℤ → ℝ} (hh : ∀ j n, 0 ≤ h j n) :
    0 ≤ annDouble m h := by
  refine tsum_nonneg fun j => ?_
  split_ifs with hj
  · refine tsum_nonneg fun n => ?_
    split_ifs with hn
    · exact hh _ _
    · exact le_rfl
  · exact le_rfl

/-- **The product-to-iterated bridge.**  For a summable guarded annular family
the `Z x Z` sum is the iterated double sum. -/
theorem tsum_annFam {m : ℤ} {h : ℤ → ℤ → ℝ} (hs : Summable (annFam m h)) :
    (∑' p : ℤ × ℤ, annFam m h p) = annDouble m h := by
  classical
  rw [hs.tsum_prod, annDouble_def]
  refine tsum_congr fun j => ?_
  by_cases hj : j ≤ m
  · rw [ite_eq_left hj]
    refine tsum_congr fun n => ?_
    by_cases hn : n ≤ j - 1
    · rw [annFam_apply, ite_eq_left (⟨hj, hn⟩ : j ≤ m ∧ n ≤ j - 1), ite_eq_left hn]
    · rw [annFam_apply, ite_eq_right (fun hc : j ≤ m ∧ n ≤ j - 1 => hn hc.2), ite_eq_right hn]
  · rw [ite_eq_right hj]
    have hzero : ∀ n : ℤ, annFam m h (j, n) = 0 := by
      intro n
      rw [annFam_apply]
      exact ite_eq_right (fun hc : j ≤ m ∧ n ≤ j - 1 => hj hc.1)
    calc ∑' n : ℤ, annFam m h (j, n) = ∑' _ : ℤ, (0 : ℝ) := tsum_congr hzero
      _ = 0 := tsum_zero

/-! ## The two scale-weight collapses -/

/-- `3^(-2sq) * 3^(sq) = 3^(-sq)` -- the weight collapse of the first four
`pre.zero` terms: the ugly estimate's growth factor eats one of the two
`s`-powers of the Step-1 weight. -/
theorem weight_collapse_one (s q : ℝ) :
    (3 : ℝ) ^ (-(2 * s * q)) * (3 : ℝ) ^ (s * q) = (3 : ℝ) ^ (-(s * q)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- `3^(-2sq) * 3^((s+gamma)q) = 3^(-(s-gamma)q)` -- the weight collapse of the
fifth `pre.zero` term. -/
theorem weight_collapse_two (s gamma q : ℝ) :
    (3 : ℝ) ^ (-(2 * s * q)) * (3 : ℝ) ^ ((s + gamma) * q)
      = (3 : ℝ) ^ (-((s - gamma) * q)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-! ## The elementary convexity input -/

/-- The abstract-real core of the convexity step: no logarithm is entered by a
numeric tactic. -/
private theorem half_mul_le_of_one_le (x L : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hL : 1 ≤ L) : x / 2 * (1 + x * L) ≤ x * L := by
  have p1 : 0 ≤ x * (L - 1) := mul_nonneg hx0.le (by linarith only [hL])
  have p2 : 0 ≤ x * ((1 - x) * L) :=
    mul_nonneg hx0.le (mul_nonneg (by linarith only [hx1]) (by linarith only [hL]))
  linarith only [p1, p2]

/-- **`1 - 3^(-x) >= x/2` for `x` in `(0,1]`.**  From `exp y >= 1 + y` one gets
`3^(-x) <= (1 + x log 3)^(-1)`, and `x log 3 / (1 + x log 3) >= x / 2` reduces
to `log 3 >= 1`.  This is the linear lower bound behind every `c^(-1)` and
`c^(-2)` geometric constant of the Section 4.1 sums. -/
theorem half_le_one_sub_threeRpow_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - (3 : ℝ) ^ (-x) := by
  have hlog : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    exact le_trans Real.exp_one_lt_d9.le (by norm_num)
  have hE : (3 : ℝ) ^ (-x) = Real.exp (-(x * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hy0 : 0 < x * Real.log 3 := mul_pos hx0 (by linarith only [hlog])
  have h1py : (0 : ℝ) < 1 + x * Real.log 3 := by linarith only [hy0]
  have hEpos : 0 < Real.exp (-(x * Real.log 3)) := Real.exp_pos _
  have hprod : Real.exp (-(x * Real.log 3)) * Real.exp (x * Real.log 3) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hexp : 1 + x * Real.log 3 ≤ Real.exp (x * Real.log 3) := by
    linarith only [Real.add_one_le_exp (x * Real.log 3)]
  have hkey : Real.exp (-(x * Real.log 3)) * (1 + x * Real.log 3) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hexp hEpos.le
    rw [hprod] at hmul
    exact hmul
  have hEle : Real.exp (-(x * Real.log 3)) ≤ 1 / (1 + x * Real.log 3) := by
    rw [le_div_iff₀ h1py]
    exact hkey
  have hfrac : 1 / (1 + x * Real.log 3) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ h1py]
    linarith only [half_mul_le_of_one_le x (Real.log 3) hx0 hx1 hlog]
  rw [hE]
  linarith only [hEle, hfrac]

/-! ## The annulus-multiplicity weight sum -/

/-- The fifth `pre.zero` term's weight family: the guarded annular family of the
pure weight `3^(-c(m-n))`.  Summing it over the annular region counts, for each
scale `n`, the `m - n` annuli `j` in `[n+1, m]`. -/
def annWeightFam (c : ℝ) (m : ℤ) : ℤ × ℤ → ℝ :=
  annFam m (fun _ n => (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ))))

theorem annWeightFam_def (c : ℝ) (m : ℤ) :
    annWeightFam c m = annFam m (fun _ n => (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ)))) :=
  rfl

/-- The transport of the guarded annular region to `N x N`. -/
def annIdx (m : ℤ) : ℕ × ℕ → ℤ × ℤ :=
  fun ab => (m - (ab.1 : ℤ), m - (ab.1 : ℤ) - 1 - (ab.2 : ℤ))

private theorem annIdx_injective (m : ℤ) : Function.Injective (annIdx m) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  simp only [annIdx, Prod.mk.injEq] at hab
  obtain ⟨h1, h2⟩ := hab
  have ha : a = a' := by omega
  subst ha
  have hb : b = b' := by omega
  subst hb
  rfl

private theorem annWeightFam_annIdx (c : ℝ) (m : ℤ) (a b : ℕ) :
    annWeightFam c m (annIdx m (a, b))
      = ((3 : ℝ) ^ (-c)) ^ (a + 1) * ((3 : ℝ) ^ (-c)) ^ b := by
  have hg : m - (a : ℤ) ≤ m ∧ m - (a : ℤ) - 1 - (b : ℤ) ≤ m - (a : ℤ) - 1 :=
    ⟨by omega, by omega⟩
  rw [annWeightFam_def, annIdx, annFam_apply, ite_eq_left hg]
  have hcast : ((m - (m - (a : ℤ) - 1 - (b : ℤ)) : ℤ) : ℝ) = ((a + b + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, threeRpow_neg_natMul c (a + b + 1),
    show a + b + 1 = a + 1 + b from by omega, pow_add]

private theorem annWeightFam_support (c : ℝ) (m : ℤ) :
    ∀ p : ℤ × ℤ, p ∉ Set.range (annIdx m) → annWeightFam c m p = 0 := by
  rintro ⟨j, n⟩ hp
  rw [annWeightFam_def, annFam_apply]
  refine ite_eq_right ?_
  rintro ⟨h1, h2⟩
  refine hp ⟨((m - j).toNat, (j - 1 - n).toNat), ?_⟩
  simp only [annIdx, Prod.mk.injEq]
  omega

private theorem annWeightFam_support_subset (c : ℝ) (m : ℤ) :
    Function.support (annWeightFam c m) ⊆ Set.range (annIdx m) := by
  intro p hp
  by_contra hnr
  exact hp (annWeightFam_support c m p hnr)

private theorem annWeight_geomProd_summable {c : ℝ} (hc : 0 < c) :
    Summable (fun ab : ℕ × ℕ =>
      ((3 : ℝ) ^ (-c)) ^ (ab.1 + 1) * ((3 : ℝ) ^ (-c)) ^ ab.2) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-c) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-c) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc])
  have hB : Summable (fun b : ℕ => ((3 : ℝ) ^ (-c)) ^ b) :=
    summable_geometric_of_lt_one hr0 hr1
  have hA : Summable (fun a : ℕ => ((3 : ℝ) ^ (-c)) ^ (a + 1)) := by
    refine (hB.mul_left ((3 : ℝ) ^ (-c))).congr fun a => ?_
    rw [pow_succ]
    ring
  exact hA.mul_of_nonneg hB (fun a => pow_nonneg hr0 _) (fun b => pow_nonneg hr0 _)

/-- **The annulus-multiplicity weight sum is summable.** -/
theorem annWeightFam_summable {c : ℝ} (hc : 0 < c) (m : ℤ) :
    Summable (annWeightFam c m) := by
  have hcomp : Summable (fun ab : ℕ × ℕ => annWeightFam c m (annIdx m ab)) := by
    refine (annWeight_geomProd_summable hc).congr fun ab => ?_
    exact (annWeightFam_annIdx c m ab.1 ab.2).symm
  exact ((annIdx_injective m).summable_iff (annWeightFam_support c m)).1 hcomp

/-- The abstract-real core of the multiplicity bound: no `rpow` term is entered
by a numeric tactic. -/
private theorem geom_sq_bound {c rho : ℝ} (hc0 : 0 < c) (hrho1 : rho < 1)
    (hhalf : c / 2 ≤ 1 - rho) :
    rho * (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ 4 / c ^ 2 := by
  have hpos : (0 : ℝ) < 1 - rho := by linarith only [hrho1]
  have hu : (0 : ℝ) < (1 - rho)⁻¹ := inv_pos.2 hpos
  have hcancel : (1 - rho) * (1 - rho)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hpos)
  have hcu : c * (1 - rho)⁻¹ ≤ 2 := by
    have h := mul_le_mul_of_nonneg_right hhalf hu.le
    rw [hcancel] at h
    linarith only [h]
  have hcu0 : (0 : ℝ) ≤ c * (1 - rho)⁻¹ := mul_nonneg hc0.le hu.le
  have hprod : (c * (1 - rho)⁻¹) * (c * (1 - rho)⁻¹) ≤ 2 * 2 :=
    mul_le_mul hcu hcu hcu0 (by norm_num)
  have hc2 : (0 : ℝ) < c ^ 2 := pow_pos hc0 2
  have hu2 : (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ 4 / c ^ 2 := by
    rw [le_div_iff₀ hc2]
    linarith only [hprod]
  have hstep : rho * (1 - rho)⁻¹ * (1 - rho)⁻¹ ≤ 1 * (1 - rho)⁻¹ * (1 - rho)⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrho1.le hu.le) hu.le
  linarith only [hstep, hu2]

/-- **The annulus-multiplicity weight sum.**  For `c` in `(0,1]`,

```
sum_{j <= m} sum_{n <= j-1} 3^(-c(m-n)) = 3^(-c) (1 - 3^(-c))^(-2) <= 4 c^(-2) .
```

The double sum counts the `m - n` annuli at each scale; the bound uses the
linear lower bound `1 - 3^(-c) >= c/2`. -/
theorem annWeightFam_tsum_le {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (m : ℤ) :
    (∑' p : ℤ × ℤ, annWeightFam c m p) ≤ 4 / c ^ 2 := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-c) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-c) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hc0])
  have hB : Summable (fun b : ℕ => ((3 : ℝ) ^ (-c)) ^ b) :=
    summable_geometric_of_lt_one hr0 hr1
  have hA : Summable (fun a : ℕ => ((3 : ℝ) ^ (-c)) ^ (a + 1)) := by
    refine (hB.mul_left ((3 : ℝ) ^ (-c))).congr fun a => ?_
    rw [pow_succ]
    ring
  have hAB := annWeight_geomProd_summable hc0
  have heq : (∑' p : ℤ × ℤ, annWeightFam c m p)
      = (∑' a : ℕ, ((3 : ℝ) ^ (-c)) ^ (a + 1)) * (∑' b : ℕ, ((3 : ℝ) ^ (-c)) ^ b) := by
    rw [← (annIdx_injective m).tsum_eq (annWeightFam_support_subset c m),
      Summable.tsum_mul_tsum hA hB hAB]
    exact tsum_congr fun ab => annWeightFam_annIdx c m ab.1 ab.2
  have hBval : (∑' b : ℕ, ((3 : ℝ) ^ (-c)) ^ b) = (1 - (3 : ℝ) ^ (-c))⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hAval : (∑' a : ℕ, ((3 : ℝ) ^ (-c)) ^ (a + 1))
      = (3 : ℝ) ^ (-c) * (1 - (3 : ℝ) ^ (-c))⁻¹ := by
    rw [← hBval, ← tsum_mul_left]
    refine tsum_congr fun a => ?_
    rw [pow_succ]
    ring
  rw [heq, hAval, hBval]
  exact geom_sq_bound hc0 hr1 (half_le_one_sub_threeRpow_neg hc0 hc1)

/-! ## A five-way termwise comparison of infinite sums -/

/-- **Five-way termwise domination of infinite sums.**  A nonnegative family
dominated termwise by the sum of five summable families has its sum dominated by
the sum of their five sums. -/
theorem tsum_le_five {iota : Type*} {f g₁ g₂ g₃ g₄ g₅ : iota → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ g₁ i + g₂ i + g₃ i + g₄ i + g₅ i)
    (h₁ : Summable g₁) (h₂ : Summable g₂) (h₃ : Summable g₃) (h₄ : Summable g₄)
    (h₅ : Summable g₅) :
    ∑' i, f i
      ≤ (∑' i, g₁ i) + (∑' i, g₂ i) + (∑' i, g₃ i) + (∑' i, g₄ i) + (∑' i, g₅ i) := by
  have h1234 : Summable (fun i => g₁ i + g₂ i + g₃ i + g₄ i) := ((h₁.add h₂).add h₃).add h₄
  have hg : Summable (fun i => g₁ i + g₂ i + g₃ i + g₄ i + g₅ i) := h1234.add h₅
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hle hg
  calc ∑' i, f i ≤ ∑' i, (g₁ i + g₂ i + g₃ i + g₄ i + g₅ i) :=
        Summable.tsum_le_tsum hle hf hg
    _ = (∑' i, g₁ i) + (∑' i, g₂ i) + (∑' i, g₃ i) + (∑' i, g₄ i) + (∑' i, g₅ i) := by
        rw [Summable.tsum_add h1234 h₅, Summable.tsum_add ((h₁.add h₂).add h₃) h₄,
          Summable.tsum_add (h₁.add h₂) h₃, Summable.tsum_add h₁ h₂]

/-- Summability of a family dominated termwise by five summable families. -/
theorem summable_of_le_five {iota : Type*} {f g₁ g₂ g₃ g₄ g₅ : iota → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ g₁ i + g₂ i + g₃ i + g₄ i + g₅ i)
    (h₁ : Summable g₁) (h₂ : Summable g₂) (h₃ : Summable g₃) (h₄ : Summable g₄)
    (h₅ : Summable g₅) : Summable f :=
  Summable.of_nonneg_of_le hf0 hle ((((h₁.add h₂).add h₃).add h₄).add h₅)

/-! ## The resummation -/

/-- **The resummation, abstract-weight core.**

Summing the five-term ugly estimate over the guarded annular double sum
produces the five `pre.zero` terms: the first four keep their `(j,n)`-dependent
contents at the collapsed weight `v = w2 * W`, and the fifth, whose content
`gradM` is `(j,n)`-independent, is resummed against the weight sum of
`vg = w2 * Wg` over the whole annular region.

Stated over abstract weights so that no `Real.rpow` term is entered by a
numeric tactic; `annularResum` instantiates them at the manuscript's weights. -/
theorem annularResum_core {cstar gamma C₂ gradM Wsum : ℝ} {m : ℤ}
    {w2 W Wg v vg : ℤ → ℝ} {Jann E2 L2f gradNf : ℤ → ℤ → ℝ} {sig : ℤ → ℝ}
    (hw20 : ∀ n, 0 ≤ w2 n) (hb0 : 0 ≤ C₂ * cstar⁻¹ * gamma) (hgradM : 0 ≤ gradM)
    (hcol1 : ∀ n, w2 n * W n = v n) (hcol2 : ∀ n, w2 n * Wg n = vg n)
    (hJann0 : ∀ j n, 0 ≤ Jann j n)
    (hugly : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      Jann j n ≤ C₂ * W n * E2 j n + C₂ * W n * sig n
        + C₂ * cstar⁻¹ * gamma * W n * L2f j n
        + C₂ * cstar⁻¹ * gamma * W n * gradNf j n
        + C₂ * cstar⁻¹ * gamma * Wg n * gradM)
    (hsumE : Summable (annFam m (fun j n => v n * E2 j n)))
    (hsumS : Summable (annFam m (fun _ n => v n * sig n)))
    (hsumL : Summable (annFam m (fun j n => v n * L2f j n)))
    (hsumG : Summable (annFam m (fun j n => v n * gradNf j n)))
    (hsumW : Summable (annFam m (fun _ n => vg n)))
    (hWsum : (∑' p : ℤ × ℤ, annFam m (fun _ n => vg n) p) ≤ Wsum) :
    annDouble m (fun j n => w2 n * Jann j n)
      ≤ C₂ * annDouble m (fun j n => v n * E2 j n)
        + C₂ * annDouble m (fun _ n => v n * sig n)
        + C₂ * cstar⁻¹ * gamma * annDouble m (fun j n => v n * L2f j n)
        + C₂ * cstar⁻¹ * gamma * annDouble m (fun j n => v n * gradNf j n)
        + C₂ * cstar⁻¹ * gamma * Wsum * gradM := by
  classical
  have hbM0 : (0 : ℝ) ≤ C₂ * cstar⁻¹ * gamma * gradM := mul_nonneg hb0 hgradM
  have h₁ : Summable (fun p : ℤ × ℤ => C₂ * annFam m (fun j n => v n * E2 j n) p) :=
    hsumE.mul_left _
  have h₂ : Summable (fun p : ℤ × ℤ => C₂ * annFam m (fun _ n => v n * sig n) p) :=
    hsumS.mul_left _
  have h₃ : Summable (fun p : ℤ × ℤ =>
      C₂ * cstar⁻¹ * gamma * annFam m (fun j n => v n * L2f j n) p) := hsumL.mul_left _
  have h₄ : Summable (fun p : ℤ × ℤ =>
      C₂ * cstar⁻¹ * gamma * annFam m (fun j n => v n * gradNf j n) p) :=
    hsumG.mul_left _
  have h₅ : Summable (fun p : ℤ × ℤ =>
      C₂ * cstar⁻¹ * gamma * gradM * annFam m (fun _ n => vg n) p) := hsumW.mul_left _
  have hf0 : ∀ p : ℤ × ℤ, 0 ≤ annFam m (fun j n => w2 n * Jann j n) p :=
    annFam_nonneg (fun j n => mul_nonneg (hw20 n) (hJann0 j n))
  have hle : ∀ p : ℤ × ℤ, annFam m (fun j n => w2 n * Jann j n) p
      ≤ C₂ * annFam m (fun j n => v n * E2 j n) p
        + C₂ * annFam m (fun _ n => v n * sig n) p
        + C₂ * cstar⁻¹ * gamma * annFam m (fun j n => v n * L2f j n) p
        + C₂ * cstar⁻¹ * gamma * annFam m (fun j n => v n * gradNf j n) p
        + C₂ * cstar⁻¹ * gamma * gradM * annFam m (fun _ n => vg n) p := by
    rintro ⟨j, n⟩
    by_cases hg : j ≤ m ∧ n ≤ j - 1
    · simp only [annFam_apply, ite_eq_left hg]
      have hstep := mul_le_mul_of_nonneg_left (hugly j n hg.1 hg.2) (hw20 n)
      have hexp : w2 n * (C₂ * W n * E2 j n + C₂ * W n * sig n
            + C₂ * cstar⁻¹ * gamma * W n * L2f j n
            + C₂ * cstar⁻¹ * gamma * W n * gradNf j n
            + C₂ * cstar⁻¹ * gamma * Wg n * gradM)
          = C₂ * (v n * E2 j n) + C₂ * (v n * sig n)
            + C₂ * cstar⁻¹ * gamma * (v n * L2f j n)
            + C₂ * cstar⁻¹ * gamma * (v n * gradNf j n)
            + C₂ * cstar⁻¹ * gamma * gradM * vg n := by
        rw [← hcol1 n, ← hcol2 n]
        ring
      exact hstep.trans (le_of_eq hexp)
    · simp only [annFam_apply, ite_eq_right hg]
      simp
  have hkey := tsum_le_five hf0 hle h₁ h₂ h₃ h₄ h₅
  have hfsum : Summable (annFam m (fun j n => w2 n * Jann j n)) :=
    summable_of_le_five hf0 hle h₁ h₂ h₃ h₄ h₅
  have e₁ : (∑' p : ℤ × ℤ, C₂ * annFam m (fun j n => v n * E2 j n) p)
      = C₂ * annDouble m (fun j n => v n * E2 j n) := by
    rw [tsum_mul_left, tsum_annFam hsumE]
  have e₂ : (∑' p : ℤ × ℤ, C₂ * annFam m (fun _ n => v n * sig n) p)
      = C₂ * annDouble m (fun _ n => v n * sig n) := by
    rw [tsum_mul_left, tsum_annFam hsumS]
  have e₃ : (∑' p : ℤ × ℤ, C₂ * cstar⁻¹ * gamma * annFam m (fun j n => v n * L2f j n) p)
      = C₂ * cstar⁻¹ * gamma * annDouble m (fun j n => v n * L2f j n) := by
    rw [tsum_mul_left, tsum_annFam hsumL]
  have e₄ : (∑' p : ℤ × ℤ,
      C₂ * cstar⁻¹ * gamma * annFam m (fun j n => v n * gradNf j n) p)
      = C₂ * cstar⁻¹ * gamma * annDouble m (fun j n => v n * gradNf j n) := by
    rw [tsum_mul_left, tsum_annFam hsumG]
  have e₅ : (∑' p : ℤ × ℤ, C₂ * cstar⁻¹ * gamma * gradM * annFam m (fun _ n => vg n) p)
      = C₂ * cstar⁻¹ * gamma * gradM * ∑' p : ℤ × ℤ, annFam m (fun _ n => vg n) p :=
    tsum_mul_left
  rw [tsum_annFam hfsum, e₁, e₂, e₃, e₄, e₅] at hkey
  refine hkey.trans (add_le_add le_rfl ?_)
  calc C₂ * cstar⁻¹ * gamma * gradM * ∑' p : ℤ × ℤ, annFam m (fun _ n => vg n) p
      ≤ C₂ * cstar⁻¹ * gamma * gradM * Wsum := mul_le_mul_of_nonneg_left hWsum hbM0
    _ = C₂ * cstar⁻¹ * gamma * Wsum * gradM := by ring

/-- **The resummation at the manuscript's weights.**

The instantiation of `annularResum_core` at `w2 n = 3^(-2s(m-n))`, `W n =
3^(s(m-n))`, `Wg n = 3^((s+gamma)(m-n))`, with the fifth term's weight sum
bounded by `6 s^(-2)` (the multiplicity sum at `c = s - gamma >= 7s/8`, using
the standing hypothesis `s >= 8 gamma`).

The `sigma-bar` continuity term is produced as a **double** sum: it inherits the
annulus multiplicity that the printed `pre.zero` display omits (see the module
docstring). -/
theorem annularResum {s gamma cstar C₂ gradM : ℝ} {m : ℤ}
    {Jann E2 L2f gradNf : ℤ → ℤ → ℝ} {sig : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hcstar : 0 < cstar) (hC₂ : 0 ≤ C₂) (hgradM : 0 ≤ gradM)
    (hJann0 : ∀ j n, 0 ≤ Jann j n)
    (hugly : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      Jann j n ≤ C₂ * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * E2 j n
        + C₂ * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * sig n
        + C₂ * cstar⁻¹ * gamma * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * L2f j n
        + C₂ * cstar⁻¹ * gamma * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * gradNf j n
        + C₂ * cstar⁻¹ * gamma * (3 : ℝ) ^ ((s + gamma) * ((m - n : ℤ) : ℝ)) * gradM)
    (hsumE :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)))
    (hsumS :
      Summable (annFam m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)))
    (hsumL :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)))
    (hsumG :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n))) :
    annDouble m (fun j n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jann j n)
      ≤ C₂ * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + C₂ * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + C₂ * cstar⁻¹ * gamma
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + C₂ * cstar⁻¹ * gamma
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + C₂ * cstar⁻¹ * gamma * (6 * (s ^ 2)⁻¹) * gradM := by
  have hsg' : 0 < s - gamma := by linarith only [hs0, hsg, hgamma0]
  have hsg1 : s - gamma ≤ 1 := by linarith only [hs1, hgamma0]
  have hb0 : (0 : ℝ) ≤ C₂ * cstar⁻¹ * gamma :=
    mul_nonneg (mul_nonneg hC₂ (inv_nonneg.2 hcstar.le)) hgamma0
  have hW6 : (∑' p : ℤ × ℤ,
      annFam m (fun _ n => (3 : ℝ) ^ (-((s - gamma) * ((m - n : ℤ) : ℝ)))) p)
        ≤ 6 * (s ^ 2)⁻¹ := by
    have h1 := annWeightFam_tsum_le hsg' hsg1 m
    rw [annWeightFam_def] at h1
    refine h1.trans ?_
    have hs2 : (0 : ℝ) < s ^ 2 := pow_pos hs0 2
    have hsq : (0 : ℝ) < (s - gamma) ^ 2 := pow_pos hsg' 2
    rw [div_le_iff₀ hsq]
    have hmono : (7 * s / 8) ^ 2 ≤ (s - gamma) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hs0]) (by linarith only [hsg]) 2
    have hpos : (0 : ℝ) ≤ 6 * (s ^ 2)⁻¹ := by positivity
    have hcancel : (s ^ 2)⁻¹ * s ^ 2 = 1 := inv_mul_cancel₀ (ne_of_gt hs2)
    linarith only [mul_le_mul_of_nonneg_left hmono hpos, hcancel]
  exact annularResum_core
    (w2 := fun n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))))
    (W := fun n => (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
    (Wg := fun n => (3 : ℝ) ^ ((s + gamma) * ((m - n : ℤ) : ℝ)))
    (v := fun n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))))
    (vg := fun n => (3 : ℝ) ^ (-((s - gamma) * ((m - n : ℤ) : ℝ))))
    (fun _ => Real.rpow_nonneg (by norm_num) _) hb0 hgradM
    (fun n => weight_collapse_one s ((m - n : ℤ) : ℝ))
    (fun n => weight_collapse_two s gamma ((m - n : ℤ) : ℝ))
    hJann0 hugly hsumE hsumS hsumL hsumG (annWeightFam_summable hsg' m) hW6

/-! ## The Step-1 shape and the `pre.zero` composition -/

/-- A local abbreviation for the Step-1 shape: the full-grid weighted sum is
controlled by the annular double sum,

```
sum_{n <= m} 3^(-2s(m-n)) Jgrid n
  <= C sum_{j <= m} sum_{n <= j-1} 3^(-2s(m-n)) Jann j n .
```

This is a naming convenience inside this provider module.  It is **not** a
source-facing declaration and closes no node. -/
def IsAnnularDecompPre (s : ℝ) (m : ℤ) (Jgrid : ℤ → ℝ) (Jann : ℤ → ℤ → ℝ)
    (C : ℝ) : Prop :=
  ∑' n : ℤ, (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jgrid n else 0)
    ≤ C * ∑' j : ℤ, (if j ≤ m then
        ∑' n : ℤ, (if n ≤ j - 1 then
          (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jann j n else 0) else 0)

/-- **The five-term `pre.zero` shape, from Step 1 and the ugly estimate.**

Composition of three caller-supplied layers:

* `hess` -- the essential-sup prefactor bound: `Ecal2` is bounded by `Cess * s`
  times the full-grid weighted sum;
* `hpreA` -- the Step-1 shape;
* `hugly` with the four summability facts -- the ugly estimate, resummed by
  `annularResum`.

The output is the shape the Step-3 regrouping consumes.  Every hypothesis is a
conditional A obligation on the caller. -/
theorem preZero_of_pre_and_ugly {s gamma cstar Cess C₁ C₂ C gradM Ecal2 : ℝ} {m : ℤ}
    {Jgrid : ℤ → ℝ} {Jann E2 L2f gradNf : ℤ → ℤ → ℝ} {sig : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hcstar : 0 < cstar) (hCess : 0 ≤ Cess) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hgradM : 0 ≤ gradM)
    (hJann0 : ∀ j n, 0 ≤ Jann j n)
    (hE0 : ∀ j n, 0 ≤ E2 j n) (hsig0 : ∀ n, 0 ≤ sig n)
    (hL20 : ∀ j n, 0 ≤ L2f j n) (hgrad0 : ∀ j n, 0 ≤ gradNf j n)
    (hess : Ecal2 ≤ Cess * s
      * ∑' n : ℤ, (if n ≤ m then
          (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jgrid n else 0))
    (hpreA : IsAnnularDecompPre s m Jgrid Jann C₁)
    (hugly : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      Jann j n ≤ C₂ * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * E2 j n
        + C₂ * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * sig n
        + C₂ * cstar⁻¹ * gamma * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * L2f j n
        + C₂ * cstar⁻¹ * gamma * (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)) * gradNf j n
        + C₂ * cstar⁻¹ * gamma * (3 : ℝ) ^ ((s + gamma) * ((m - n : ℤ) : ℝ)) * gradM)
    (hsumE :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)))
    (hsumS :
      Summable (annFam m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)))
    (hsumL :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)))
    (hsumG :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)))
    (hCge : 6 * Cess * C₁ * C₂ ≤ C) :
    Ecal2
      ≤ C * s * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + C * s * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM := by
  have hcsinv : (0 : ℝ) ≤ cstar⁻¹ := inv_nonneg.2 hcstar.le
  have hresum := annularResum hs0 hs1 hgamma0 hsg hcstar hC₂ hgradM hJann0 hugly
    hsumE hsumS hsumL hsumG
  have hD1 : 0 ≤ annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n) :=
    annDouble_nonneg (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hE0 j n))
  have hD2 : 0 ≤ annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n) :=
    annDouble_nonneg (fun _ n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hsig0 n))
  have hD3 : 0 ≤ annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n) :=
    annDouble_nonneg (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hL20 j n))
  have hD4 :
      0 ≤ annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n) :=
    annDouble_nonneg (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hgrad0 j n))
  have hpre' : (∑' n : ℤ,
        (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jgrid n else 0))
      ≤ C₁ * annDouble m
          (fun j n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jann j n) := by
    rw [annDouble_def]
    exact hpreA
  have hCess_s : (0 : ℝ) ≤ Cess * s := mul_nonneg hCess hs0.le
  have hstep1 : Ecal2 ≤ Cess * s * C₁
      * annDouble m (fun j n => (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jann j n) := by
    rw [mul_assoc]
    exact hess.trans (mul_le_mul_of_nonneg_left hpre' hCess_s)
  have hCC : (0 : ℝ) ≤ Cess * s * C₁ := mul_nonneg hCess_s hC₁
  have hstep2 := mul_le_mul_of_nonneg_left hresum hCC
  have hbase : Ecal2
      ≤ (Cess * C₁ * C₂) * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + (Cess * C₁ * C₂) * s
            * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + (Cess * C₁ * C₂) * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + (Cess * C₁ * C₂) * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + (6 * (Cess * C₁ * C₂)) * cstar⁻¹ * gamma * (s * (s ^ 2)⁻¹) * gradM := by
    refine hstep1.trans (hstep2.trans (le_of_eq ?_))
    ring
  have hCC0 : (0 : ℝ) ≤ Cess * C₁ * C₂ := mul_nonneg (mul_nonneg hCess hC₁) hC₂
  have hCbase : Cess * C₁ * C₂ ≤ C := by linarith only [hCge, hCC0]
  have hfifth : (6 * (Cess * C₁ * C₂)) * cstar⁻¹ * gamma * (s * (s ^ 2)⁻¹) * gradM
      ≤ C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM := by
    have hs2 : (0 : ℝ) < (s ^ 2)⁻¹ := inv_pos.2 (pow_pos hs0 2)
    have hsinv : s * (s ^ 2)⁻¹ ≤ (s ^ 2)⁻¹ := by
      have h := mul_le_mul_of_nonneg_right hs1 hs2.le
      linarith only [h]
    have h60 : (0 : ℝ) ≤ 6 * (Cess * C₁ * C₂) := by linarith only [hCC0]
    have h6 : 6 * (Cess * C₁ * C₂) ≤ C := by linarith only [hCge]
    have hC0' : (0 : ℝ) ≤ C := le_trans h60 h6
    have hkey : (6 * (Cess * C₁ * C₂)) * (s * (s ^ 2)⁻¹) ≤ C * (s ^ 2)⁻¹ :=
      mul_le_mul h6 hsinv (mul_nonneg hs0.le hs2.le) hC0'
    have hK : (0 : ℝ) ≤ cstar⁻¹ * gamma * gradM :=
      mul_nonneg (mul_nonneg hcsinv hgamma0) hgradM
    calc (6 * (Cess * C₁ * C₂)) * cstar⁻¹ * gamma * (s * (s ^ 2)⁻¹) * gradM
        = ((6 * (Cess * C₁ * C₂)) * (s * (s ^ 2)⁻¹)) * (cstar⁻¹ * gamma * gradM) := by
          ring
      _ ≤ (C * (s ^ 2)⁻¹) * (cstar⁻¹ * gamma * gradM) :=
          mul_le_mul_of_nonneg_right hkey hK
      _ = C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM := by ring
  have hT1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbase hs0.le) hD1
  have hT2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbase hs0.le) hD2
  have hT3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbase hcsinv) hgamma0)
    hs0.le) hD3
  have hT4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbase hcsinv) hgamma0)
    hs0.le) hD4
  exact hbase.trans
    (add_le_add (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4) hfifth)

end

end Algsuperdiff.Section4.Provider.Annular
