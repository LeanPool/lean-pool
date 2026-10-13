/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.WindowRearrange
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# GeometricSums

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Geometric closures for the minimal-scale separation window sums

ABK26, `l.minimal.scale.sep` Steps 1--3.  This module collects the deterministic
geometric-series arithmetic those three steps consume, all of it carrier-free.

## The three series

* `∑_r 3^{−αr} = (1 − 3^{−α})⁻¹` — the plain closure constant `geomTailConst α`;
* `∑_r (r+1) 3^{−αr} = (1 − 3^{−α})⁻²` — the linear-weight closure;
* `∑_r √(r+1) 3^{−αr} ≤ (1 − 3^{−α})^{−3/2}` — the **sharp** `√`-weight closure
  `geomSqrtConst α`, obtained by Cauchy--Schwarz against the first two.

The crude `√(r+1) ≤ r+1` gives only `(1 − 3^{−α})^{−2}`, half a power of `α`
worse, which does *not* close the printed Step-3 envelope.

## The `min` companion of the window rearrangement

`min_div_le_sqrt_mul_rpow` (`min{N,C}/N ≤ √C · N^{−1/2}`) is the inequality that
turns the sharp `min{m − n + 1, Cgeo}` coefficient of
`Algsuperdiff.Probability.window_geom_tail_rearrange` into the printed
`(m − n)^{−1/2}` envelope, at cost `Cgeo^{3/2}` rather than `Cgeo²`. Without the
`min` the Step-1 envelope fails at `m − n = 1` by a power of the parameter.

## Also here

The one-sided/two-sided `O_{Γ_σ}` dictionary for nonnegative variables lets a
one-sided geometric tail closure feed a two-sided Cesàro engine.

## Main results

* `Algsuperdiff.Probability.min_div_le_sqrt_mul_rpow`
* `Algsuperdiff.Probability.geomTailConst`, `Algsuperdiff.Probability.geomSqrtConst`
* `Algsuperdiff.Probability.sum_threePow_neg_sqrt_le`
* `Algsuperdiff.Probability.tsum_threePow_neg_sqrt_le`

## References

* ABK26, `l.minimal.scale.sep`, Steps 1--3 (the `ℓ² ↪ ℓ¹` step).
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

noncomputable section

/-! ## The `min` companion of the window rearrangement -/

/-- `min{N, C}/N ≤ √C · N^{−1/2}` for `N > 0`, `C > 0` — the sharp form of the
inner window-sum bound that Step 1 needs, and the inequality that makes the
printed envelope close on the nose (see the module docstring). -/
theorem min_div_le_sqrt_mul_rpow {N C : ℝ} (hN : 0 < N) (hC : 0 < C) :
    (1 / N) * min N C ≤ Real.sqrt C * (N ^ (-(1 : ℝ) / 2)) := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hrp : N ^ (-(1 : ℝ) / 2) = Real.sqrt N / N := (sqrt_div_self_eq_rpow_neg_half hN).symm
  rw [hrp]
  rcases le_total C N with hle | hle
  · -- `min = C`
    rw [min_eq_right hle]
    have hsle : Real.sqrt C ≤ Real.sqrt N := Real.sqrt_le_sqrt hle
    have hgoal : Real.sqrt C * (Real.sqrt N / N) - (1 / N) * C
        = (Real.sqrt C * Real.sqrt N - C) / N := by field_simp
    have hCsq : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC.le
    have hstep : Real.sqrt C * Real.sqrt C ≤ Real.sqrt C * Real.sqrt N :=
      mul_le_mul_of_nonneg_left hsle hsC.le
    have hnum : 0 ≤ Real.sqrt C * Real.sqrt N - C := by
      linarith only [hstep, hCsq]
    have hdiv : 0 ≤ (Real.sqrt C * Real.sqrt N - C) / N := div_nonneg hnum hN.le
    linarith only [hgoal.le, hgoal.ge, hdiv]
  · -- `min = N`
    rw [min_eq_left hle]
    have hsle : Real.sqrt N ≤ Real.sqrt C := Real.sqrt_le_sqrt hle
    have hL : (1 / N) * N = 1 := by field_simp
    have hR : Real.sqrt C * (Real.sqrt N / N) = (Real.sqrt C * Real.sqrt N) / N := by ring
    have hstep : Real.sqrt N * Real.sqrt N ≤ Real.sqrt C * Real.sqrt N :=
      mul_le_mul_of_nonneg_right hsle hsN.le
    have h1 : N ≤ Real.sqrt C * Real.sqrt N := by linarith only [hstep, hsq]
    have h2 : 1 ≤ (Real.sqrt C * Real.sqrt N) / N := by
      rw [le_div_iff₀ hN]; linarith only [h1]
    linarith only [hL.le, hL.ge, hR.le, hR.ge, h2]

/-! ## The geometric closure constant -/

/-- The geometric closure constant `(1 − 3^{−α})⁻¹` of the layer tail. -/
def geomTailConst (α : ℝ) : ℝ := (1 - (3 : ℝ) ^ (-α))⁻¹

theorem three_rpow_neg_lt_one {α : ℝ} (hα : 0 < α) : (3 : ℝ) ^ (-α) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_iff_pos.mpr hα)

theorem one_sub_three_rpow_neg_pos {α : ℝ} (hα : 0 < α) :
    0 < 1 - (3 : ℝ) ^ (-α) := by
  have h := three_rpow_neg_lt_one hα
  linarith only [h]

theorem geomTailConst_pos {α : ℝ} (hα : 0 < α) : 0 < geomTailConst α :=
  inv_pos.mpr (one_sub_three_rpow_neg_pos hα)

/-! ## `IsBigO` ↔ `IsBigOWith` for nonnegative variables

`IsBigO μ Ψ X A` is by definition `IsBigOWith μ Ψ |X| A`, so for a nonnegative
`X` the two coincide. This is what lets a one-sided geometric tail closure
(one-sided precisely because it needs no summability) feed the two-sided Cesàro
engine. -/

section NonnegBigO

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- For a nonnegative variable, the one-sided and two-sided weak-Orlicz relations
agree. -/
theorem isBigO_iff_isBigOWith_of_nonneg {X : Ω → ℝ} {Ψ : ℝ → ℝ} {A : ℝ}
    (h0 : ∀ ω, 0 ≤ X ω) :
    IsBigO μ Ψ X A ↔ IsBigOWith μ Ψ X A := by
  have habs : (fun ω => |X ω|) = X := funext fun ω => abs_of_nonneg (h0 ω)
  constructor
  · intro h; rw [← habs]; exact h
  · intro h; show IsBigOWith μ Ψ (fun ω => |X ω|) A; rw [habs]; exact h

theorem isBigO_of_isBigOWith_of_nonneg {X : Ω → ℝ} {Ψ : ℝ → ℝ} {A : ℝ}
    (h0 : ∀ ω, 0 ≤ X ω) (h : IsBigOWith μ Ψ X A) : IsBigO μ Ψ X A :=
  (isBigO_iff_isBigOWith_of_nonneg h0).mpr h

theorem isBigOWith_of_isBigO_of_nonneg {X : Ω → ℝ} {Ψ : ℝ → ℝ} {A : ℝ}
    (h0 : ∀ ω, 0 ≤ X ω) (h : IsBigO μ Ψ X A) : IsBigOWith μ Ψ X A :=
  (isBigO_iff_isBigOWith_of_nonneg h0).mp h

/-- A variable that vanishes identically is `O_{Γ_σ}` at every nonnegative
scale — used for the empty-window layers. -/
theorem isBigO_gammaSigma_of_eq_zero [IsFiniteMeasure μ] {X : Ω → ℝ} {σ A : ℝ}
    (hA : 0 ≤ A) (hX : ∀ ω, X ω = 0) : IsBigO μ (gammaSigma σ) X A := by
  have h := HCPolySupport.Book.Ch04.isBigO_gammaSigma_const_of_abs_le
    (μ := μ) (σ := σ) (c := (0 : ℝ)) hA (by simpa using hA)
  have hfun : (fun _ : Ω => (0 : ℝ)) = X := (funext hX).symm
  rwa [hfun] at h

end NonnegBigO

/-! ## Elementary `√` bookkeeping -/

/-- `√x ≤ x` for `x ≥ 1`. -/
theorem sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  have h0 : (0 : ℝ) ≤ x := by linarith only [hx]
  have h1 : (1 : ℝ) ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    simpa using h
  have h2 : Real.sqrt x * 1 ≤ Real.sqrt x * Real.sqrt x :=
    mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
  have h3 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt h0
  linarith only [h2, h3]

/-- Subadditivity of `√` on nonnegative reals. -/
theorem sqrt_add_le_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hna : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hnb : (0 : ℝ) ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hcross : (0 : ℝ) ≤ Real.sqrt a * Real.sqrt b := mul_nonneg hna hnb
  have hexp : (Real.sqrt a + Real.sqrt b) ^ 2
      = Real.sqrt a ^ 2 + 2 * (Real.sqrt a * Real.sqrt b) + Real.sqrt b ^ 2 := by ring
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [hexp, hsa, hsb]
    linarith only [hcross]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt h1
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by linarith only [hna, hnb])

/-! ## Reindexing a `Finset.Icc` sum by its offset -/

/-- `∑_{k=i}^m w k = ∑_{r < (m−i+1)⁺} w (i+r)` — the offset reindexing that turns
every layer window sum into a `Finset.range` sum, where the geometric series
live. No hypothesis relating `i` and `m` is needed: for `m < i` both sides are
empty sums. -/
theorem sum_Icc_eq_sum_range_offset (i m : ℤ) (w : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc i m, w k
      = ∑ r ∈ Finset.range ((m - i + 1).toNat), w (i + (r : ℤ)) := by
  refine Finset.sum_nbij' (fun k => (k - i).toNat) (fun r => i + (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [Finset.mem_range]
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    simp only [Finset.mem_Icc]
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    congr 1
    omega

/-! ## The three geometric series -/

/-- `∑'_r 3^{−αr} = (1 − 3^{−α})⁻¹`, as a `HasSum`. -/
theorem hasSum_threePow_neg {α : ℝ} (hα : 0 < α) :
    HasSum (fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ)))) (geomTailConst α) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-α) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-α) < 1 := three_rpow_neg_lt_one hα
  have h := hasSum_geometric_of_lt_one hr0 hr1
  have heq : (fun r : ℕ => ((3 : ℝ) ^ (-α)) ^ r)
      = fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))) := by
    funext r
    rw [threePow_neg_natMul]
  rw [heq] at h
  exact h

/-- `∑'_r (r+1) 3^{−αr} = (1 − 3^{−α})⁻²`, as a `HasSum`. -/
theorem hasSum_threePow_neg_succ {α : ℝ} (hα : 0 < α) :
    HasSum (fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))) * ((r : ℝ) + 1))
      (geomTailConst α ^ 2) := by
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-α) < 1 := three_rpow_neg_lt_one hα
  have habs : ‖(3 : ℝ) ^ (-α)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 habs
  have heq : (fun r : ℕ => (((r + 1).choose 1 : ℕ) : ℝ) * ((3 : ℝ) ^ (-α)) ^ r)
      = fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))) * ((r : ℝ) + 1) := by
    funext r
    rw [Nat.choose_one_right, threePow_neg_natMul]
    push_cast
    ring
  rw [heq] at h
  have hc : (1 : ℝ) / (1 - (3 : ℝ) ^ (-α)) ^ (1 + 1) = geomTailConst α ^ 2 := by
    rw [geomTailConst, one_div, ← inv_pow]
  rwa [hc] at h

/-- Every partial geometric sum is below the closure constant. -/
theorem sum_threePow_neg_le {α : ℝ} (hα : 0 < α) (s : Finset ℕ) :
    ∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) ≤ geomTailConst α := by
  have hS := hasSum_threePow_neg hα
  have h := hS.summable.sum_le_tsum s
    (fun r _ => Real.rpow_nonneg (by norm_num) _)
  rwa [hS.tsum_eq] at h

/-- Every partial `(r+1)`-weighted geometric sum is below the squared closure
constant. -/
theorem sum_threePow_neg_succ_le {α : ℝ} (hα : 0 < α) (s : Finset ℕ) :
    ∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) * ((r : ℝ) + 1) ≤ geomTailConst α ^ 2 := by
  have hS := hasSum_threePow_neg_succ hα
  have h := hS.summable.sum_le_tsum s
    (fun r _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by positivity))
  rwa [hS.tsum_eq] at h

/-- **The sharp `√`-weighted geometric closure constant** `(1−3^{−α})^{−3/2}`.
The crude `√(r+1) ≤ r+1` would give `(1−3^{−α})^{−2} ≍ α^{−2}`, half a power of
`α` worse, and not enough for the printed Step-3 envelope. -/
def geomSqrtConst (α : ℝ) : ℝ := Real.sqrt (geomTailConst α ^ 3)

theorem geomSqrtConst_pos {α : ℝ} (hα : 0 < α) : 0 < geomSqrtConst α :=
  Real.sqrt_pos.mpr (pow_pos (geomTailConst_pos hα) 3)

/-- **`∑_r √(r+1) 3^{−αr} ≤ (1−3^{−α})^{−3/2}`**, by Cauchy--Schwarz against the
pure geometric series `∑ 3^{−αr} = (1−3^{−α})⁻¹` and the linear one `∑
(r+1)3^{−αr} = (1−3^{−α})⁻²`.  Stated for an arbitrary finite index set, so it
also bounds the `tsum`. -/
theorem sum_threePow_neg_sqrt_le {α : ℝ} (hα : 0 < α) (s : Finset ℕ) :
    ∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1)
      ≤ geomSqrtConst α := by
  have hnn : (0 : ℝ) ≤ ∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1) :=
    Finset.sum_nonneg fun r _ =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1))
    (f := fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))) * ((r : ℝ) + 1))
    (g := fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))))
    (fun r _ => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by positivity))
    (fun r _ => Real.rpow_nonneg (by norm_num) _)
    (fun r _ => le_of_eq (by
      have h1 : Real.sqrt ((r : ℝ) + 1) ^ 2 = (r : ℝ) + 1 := Real.sq_sqrt (by positivity)
      rw [mul_pow, h1]; ring))
  have hgnn : (0 : ℝ) ≤ ∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) :=
    Finset.sum_nonneg fun r _ => Real.rpow_nonneg (by norm_num) _
  have hprod : (∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) * ((r : ℝ) + 1))
        * (∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))))
      ≤ geomTailConst α ^ 2 * geomTailConst α :=
    mul_le_mul (sum_threePow_neg_succ_le hα s) (sum_threePow_neg_le hα s) hgnn
      (pow_pos (geomTailConst_pos hα) 2).le
  have hcube : geomTailConst α ^ 2 * geomTailConst α = geomTailConst α ^ 3 := by ring
  have hsq : (∑ r ∈ s, (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1)) ^ 2
      ≤ geomTailConst α ^ 3 := by
    linarith only [hcs, hprod, hcube.le, hcube.ge]
  have hfin := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hnn] at hfin
  exact hfin

/-- The `√`-weighted geometric series is summable. -/
theorem summable_threePow_neg_sqrt {α : ℝ} (hα : 0 < α) :
    Summable (fun r : ℕ => (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1)) := by
  refine Summable.of_nonneg_of_le
    (fun r => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _))
    (fun r => ?_) (hasSum_threePow_neg_succ hα).summable
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  exact mul_le_mul_of_nonneg_left (sqrt_le_self_of_one_le (by linarith only [hr0]))
    (Real.rpow_nonneg (by norm_num) _)

/-- The `tsum` form of the sharp `√`-weighted closure. -/
theorem tsum_threePow_neg_sqrt_le {α : ℝ} (hα : 0 < α) :
    ∑' r : ℕ, (3 : ℝ) ^ (-(α * (r : ℝ))) * Real.sqrt ((r : ℝ) + 1)
      ≤ geomSqrtConst α :=
  (summable_threePow_neg_sqrt hα).tsum_le_of_sum_le
    (fun s => sum_threePow_neg_sqrt_le hα s)

end

end Algsuperdiff.Probability
