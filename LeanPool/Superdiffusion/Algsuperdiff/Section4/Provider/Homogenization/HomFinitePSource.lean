/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourPairing

/-!
# HomFinitePSource

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# the general coarse-graining proposition at finite `p`: the printed vocabulary

## THE CONDITIONAL EDGE — `hCG'`, transcribed, NOT proved here

The general coarse-graining proposition is a declared dependency and a declared
source hypothesis of the Step-3a node of Theorem B. It is a **hypothesis** of
this tree, exactly as `hCG` and `hC` are entered elsewhere in it.  Nothing
below proves it; this file transcribes the vocabulary of its printed display —
the energy slot, the right-hand side and the geometric factor — and every
consumer carries the display itself as an explicit binder.

This file replaces the `hCG` hypothesis (the *`p → ∞`* reading) by the
**printed finite-`p` proposition**:

> Let `m,n ∈ ℤ` with `n < m`, `𝐚: □_m → ℝ^{d×d}_+` uniformly elliptic and
> `σ₀ ∈ (0,∞)`.  Fix `p ∈ [2,∞)` and `s, s₁, s₂ ∈ (0,1)` with `s₁ < s < s₂ < 1`.
> There is `C(p,d) < ∞` such that for every `𝐠 ∈ W^{s₂,p}(□_m;ℝ^d)` and every
> pair `u, v ∈ H¹(□_m)` with `-∇·𝐚∇u = ∇·𝐠`, `-∇·σ₀∇v = ∇·𝐠` in `□_m` and
> `u - v ∈ H¹₀(□_m)`,
>
> ```text
>   3^{-ms} σ₀ ‖∇u - ∇v‖_{W_hat^{-s,p}(□_m)} + 3^{-ms} ‖𝐚∇u - σ₀∇v‖_{W_hat^{-s,p}(□_m)}
>     ≤ C s^{-1} σ₀^{1/2} 𝓔_{s₁,∞,1}(□_m,n;𝐚,σ₀)
>         ( Σ_{k ≤ n} 3^{-(s-s₁)p(n-k)} avsum_{z ∈ 3^k ℤ^d ∩ □_m}
>              ‖σ^{1/2}∇u‖_{L²(z+□_k)}^p )^{1/p}
>       + C s^{-9/2} (s₂-s)^{-1} (1 + 𝓔²_{s₁/2,∞,2}(□_m,n;𝐚,σ₀))
>           3^{s₂ n} [𝐠]_{W^{s₂,p}(□_m)}.
> ```

No extension, no `p`-limit and no correction is used: `p = 4d` is inside the
printed range `[2,∞)`, and `C(p,d)` is the printed constant.

## Which parts are pinned, and which are carried abstractly

Following the established conditional-edge device, the objects this file does
**not** consume are carried as abstract reals: the coefficient field, the two `𝓔`
quantities (`E1`, `E2`), the forcing seminorm (`Dg`), the constant (`Ccg`) and
the elliptic pair itself.  Two things ARE pinned, because they are consumed:

* the **energy slot** — the printed `ℓ^p` sum over the printed grid, at
  `coarseGrainingEnergyPartial`: the grid of the sum is the pure lattice
  `3^k ℤ^d ∩ □_m`, i.e. `CoarseGraining`'s `descendantsAtDepth`, and the outer index is a
  partial sum (no summability side hypothesis);
* the **left-hand negative norms**, at BOTH readings — see next.

## TWO READINGS, both transcribed

The manuscript never defines `‖·‖_{W_hat^{-s,p}(□_m)}` (the manuscript defines
only the order `-1` duals).  The correction records — machine-checked  — that
the two consumption sites need **inequivalent** objects:

* Step 3c (the `L^∞` upgrade) needs the **multiscale** reading: a single-scale
  duality bound loses `r^{-d}`;
* Step 4 (the pairing) needs the **duality** reading:
  pairing a Hölder test field against the multiscale depth maxima diverges
  logarithmically over the triadic depths.

Neither implies the other.  An honest transcription of ONE printed display
whose symbol is undefined therefore has to carry **both** readings of that
display: a multiscale clause, at the finite-`p` grid carrier of
`HomFinitePGauge`, and two duality clauses, at the `WeakNegDualBoundOn` levels.
No clause is derived from another anywhere in this tree, and the disclosure
travels with every consumer.

## Main definitions and results

* `coarseGrainingEnergyPartial` — the printed `ℓ^p` mesoscale energy slot;
* `coarseGrainingFinitePRHS` — the printed right-hand side;
* `coarseGrainingGeomFactor` — the geometric factor `(1 - 3^{-wp})^{-1/p}` the
  energy slot is summed against, with the elementary `ℓ^p` geometric-sum bounds
  it needs.
-/

open HCPolySupport HCPolySupport.Book.Ch03

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The printed `ℓ^p` mesoscale energy slot -/

/-- **The printed energy slot**, as a partial sum.

With `k = n - i` and the mesoscale depth `jn = m - n`, the printed
`Σ_{k ≤ n} 3^{-(s-s₁)p(n-k)} avsum_{z ∈ 3^k ℤ^d ∩ □_m} G(z+□_k)^p` becomes a
sum over `i ≥ 0` of `3^{-(w p) i}` times the depth-`(jn + i)` grid average of
`G^p`, where `w = s - s₁`.  The grid is the printed one: the pure lattice,
i.e. `CoarseGraining`'s `descendantsAtDepth`. -/
def coarseGrainingEnergyPartial (Q : TriadicCube d) (p w : ℝ) (jn N : ℕ)
    (Gen : TriadicCube d → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p) ^ (1 / p)

theorem coarseGrainingEnergyPartial_def (Q : TriadicCube d) (p w : ℝ) (jn N : ℕ)
    (Gen : TriadicCube d → ℝ) :
    coarseGrainingEnergyPartial Q p w jn N Gen =
      (∑ i ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          descendantsAverage Q (jn + i) fun R => Gen R ^ p) ^ (1 / p) := rfl

/-- **The printed right-hand side**, with the energy slot
supplied as the abstract upper bound `S`.

Every factor is the printed one: `C s^{-1} σ₀^{1/2} 𝓔₁ · S` and
`C s^{-9/2} (s₂-s)^{-1} (1 + 𝓔₂²) · 3^{s₂ n} [𝐠]`. -/
def coarseGrainingFinitePRHS (Ccg s s2 sigma E1 E2 Dg S : ℝ) (n : ℤ) : ℝ :=
  Ccg * s⁻¹ * Real.sqrt sigma * E1 * S +
    Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
      ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg)

theorem coarseGrainingFinitePRHS_def (Ccg s s2 sigma E1 E2 Dg S : ℝ) (n : ℤ) :
    coarseGrainingFinitePRHS Ccg s s2 sigma E1 E2 Dg S n =
      Ccg * s⁻¹ * Real.sqrt sigma * E1 * S +
        Ccg * s ^ (-(9 / 2) : ℝ) * (s2 - s)⁻¹ * (1 + E2 ^ (2 : ℕ)) *
          ((3 : ℝ) ^ (s2 * ((n : ℤ) : ℝ)) * Dg) := rfl

/-! ## 3. The energy slot is fed by the SAME Step-2b datum as the `p = ∞` route -/

/-- The geometric factor the finite-`p` energy slot pays over the `p = ∞` sup:
`(1 - 3^{-(s-s₁)p})^{-1/p}`. -/
def coarseGrainingGeomFactor (p w : ℝ) : ℝ :=
  ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p)

theorem coarseGrainingGeomFactor_def (p w : ℝ) :
    coarseGrainingGeomFactor p w = ((1 - (3 : ℝ) ^ (-(w * p)))⁻¹) ^ (1 / p) := rfl

/-- The geometric ratio `3^{-(w p)}` lies in `(0,1)` when `w, p > 0`. -/
theorem three_rpow_neg_lt_one {t : ℝ} (ht : 0 < t) : (3 : ℝ) ^ (-t) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ht])

/-- The truncated geometric series is below `(1-r)^{-1}`. -/
theorem geom_sum_range_le_inv_one_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), r ^ i) ≤ (1 - r)⁻¹ := by
  have hden : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hid : (∑ i ∈ Finset.range (N + 1), r ^ i) * (1 - r) = 1 - r ^ (N + 1) := by
    have h := geom_sum_mul r (N + 1)
    have hneg : (∑ i ∈ Finset.range (N + 1), r ^ i) * (1 - r) =
        -((∑ i ∈ Finset.range (N + 1), r ^ i) * (r - 1)) := by ring
    rw [hneg, h]
    ring
  have hnn : (0 : ℝ) ≤ r ^ (N + 1) := pow_nonneg hr0 _
  rw [show (1 - r)⁻¹ = 1 / (1 - r) by rw [one_div], le_div_iff₀ hden, hid]
  linarith only [hnn]

/-- The weighted geometric sum bound used by the energy slot. -/
theorem sum_geom_weighted_le {r B : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hB : 0 ≤ B)
    {a : ℕ → ℝ} (haB : ∀ i, a i ≤ B) (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), r ^ i * a i) ≤ B * (1 - r)⁻¹ := by
  have hden : (0 : ℝ) < 1 - r := by linarith only [hr1]
  calc (∑ i ∈ Finset.range (N + 1), r ^ i * a i)
      ≤ ∑ i ∈ Finset.range (N + 1), r ^ i * B :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (haB i) (pow_nonneg hr0 i)
    _ = (∑ i ∈ Finset.range (N + 1), r ^ i) * B := by rw [Finset.sum_mul]
    _ ≤ (1 - r)⁻¹ * B :=
        mul_le_mul_of_nonneg_right (geom_sum_range_le_inv_one_sub hr0 hr1 N) hB
    _ = B * (1 - r)⁻¹ := by ring

end

end Algsuperdiff.Section4.Provider.Homogenization
