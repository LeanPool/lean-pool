/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.Step3Seams
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.WaveThirdTermSquared
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementConcentration

/-!
# ConclusionSeam2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Seam 2 of Step 3: the cube average over a Whitney layer, and the root

Step 3's *squared* three-term wave display is stated at an arbitrary outer-cube
scale `lout` and an arbitrary `ℓ`.  Two steps separate it from the printed
aggregation:

* the `ℓ`-instantiation `ℓ := n - k - h_k + h_hat_sep`, the manuscript's own `ℓ`,
  written just above the display, and
* the **cube average over the layer** `𝒲(□_n, k)` of the fourth `L⁴` mass,
  after a square root.

This module supplies the second of them.

## The printed aggregation is; the corrected one is what is proved

```
( ⨍_{□ ∈ 𝒲(□_n,k)} γ² 3^{-4γℓ} ‖k_L - k_{n-k-h_k}‖⁴_{L⁴(□)} )^{1/2}
      ≤  ⨍_{□ ∈ 𝒲(□_n,k)} γ 3^{-2γℓ} ‖k_L - k_{n-k-h_k}‖²_{L⁴(□)}
```

is the **false** inequality `√(av X²) ≤ av X` for nonnegative `X` (`\avsum` is
the cardinal average): a payload carried by one of `N` cubes loses a factor
`√N`, so no dimension-only constant rescues it.  Nothing below asserts it.

```
γ 3^{-2γℓ} ( ∑_{□ ∈ 𝒲(□_n,k)} (|□|/|□_n|) ⨍_□ |k_L - k_{n-k-h_k}|⁴ )^{1/2} ,
```

and dominate it before the root.  The domination *identity step* is exact: the
Whitney layer is a sub-family of the depth-`(k+h_k)` descendants of `□_n`, the
density is nonnegative, and the descendant identity
`Stream.streamIncrementLpMass_eq_descendantsAverage` says the full weighted sum
over that depth **is** the origin-cube mass `⨍_{□_n} |k_L - k_{n-k-h_k}|⁴`.
Hence

```
∑_{□ ∈ 𝒲(□_n,k)} (|□|/|□_n|) ⨍_□ |·|⁴  ≤  ⨍_{□_n} |·|⁴ ,
```

`sum_cubeMassRatio_mul_cubeAverage_le_streamIncrementLpMass`, and its square
root is `‖k_L - k_{n-k-h_k}‖²_{L⁴(□_n)}`
(`sqrt_streamIncrementLpMass_four_eq_streamIncrementLpNorm_sq`, the identity
`mass^{1/2} = (mass^{1/4})²`), which is *precisely* the left-hand side of the
proved squared display.  The printed step's defect is the Jensen/ reversal
(`√(av X²) ≤ av X` is false); the volume-weighted normalization is what makes
the weighted layer sum a genuine sub-sum of the descendant average.

**What this route does cost, stated plainly.**  Dominating the layer sum by the
*root* mass discards the layer's own mass fraction (`≈ 3^{-k}`), so the bound
proved below is **uniform in the layer index `k`, not decaying in it**.  At the
time this module proved, the Step-2 chain was defined on the origin cubes only.

There the layer's own mass fraction is kept in the `Γ₁` scale and bounded by
the proved `LayerMass.sum_cubeMassRatio_whitneyLayer_le`, so the recovered
factor is `√(6d) 3^{-k/2}` --- and that is *all* that is recovered.

The two routes are independent and neither implies the other: this module
dominates the layer object by the three squared wave terms after collapsing
onto the root; the per-cube module prices the same object in `Γ₁` at a
deterministic shell pair, paying `gammaTriangleConst (1/2)` for the normalized
triangle inequality.  The route taken here still collapses to the root: nothing
below claims a `k`-decaying per-layer bound, and the printed `3^{-3k/4}`
per-layer weight is not derivable in the corrected reading at all --- neither
here nor in the per-cube module.

## The `ℓ`-instantiation, and why it is not carried here

The instantiation reads `ℓ = m - k - h_k + h_hat_sep` with `h_k = ⌈b(1-b)⁻¹k⌉ +
h_hat_sep + k₀` (`e.SW.def`'s layer sequence).  Two arithmetic facts are all it
needs: `ℓ - h_hat_sep = m - k - h_k`, so that the shell index is *literally* the
manuscript's `k_{n-k-h_k}`; and `ℓ ≤ m - 1 < m` for `k ≥ 1`, because `h_k ≥
h_hat_sep + k₀` (`add_le_whitneyScaleSeq`) makes the `h_hat_sep` cancel.  That is why
`lout := m` is the right outer scale: `ℓ < m` is exactly the `hell : ell <
lout` binder of the squared display, with no extra hypothesis.  Layer `0` is
empty, so `k ≥ 1` is not a restriction.

The instantiation is `ω`-dependent through `h_hat_sep`, which is why it is kept
apart from the statements below: the *pointwise* leg of the squared display is
quantified over `ω` at a fixed `ℓ` and tolerates it, whereas the three *Orlicz*
legs are statements about the law and need a deterministic `ℓ`.  Reconciling
the two --- the `h_hat_sep`-decomposition of the manuscript --- is **seam 3**
(`ConclusionSeam3.lean`), and is *not* performed here.  Everything below is
stated at a free `ℓ` and does not mention the layer sequence at all.

## What is *not* proved

* The **first** printed inequality of the display, the per-*simplex* to
  per-cube conversion, is proved in `ConclusionSeam1PerCube`, in the corrected
  volume-weighted reading, at the dimension-only cost
  `simplexToCubeConst d = d⁴` and via an exact cell-weight regrouping identity
  (no cell-volume input).  This module still starts from the cube-level
  quantity, which is what the corrected route uses; the composition is in that
  file.
* Nothing below produces or uses it.
* Any **`k`-decaying** per-layer bound: see "What this route does cost" above.
  Nothing in this module consumes the translated per-cube `Γ₂` estimate, and
  the `√(6d) 3^{-k/2}` mass-fraction factor belongs to the per-cube route, not
  to this one.
* The identification of `waveTailGainScale²`'s `3^{-(d/4)(lout-ℓ)}` with the
  printed `C 3^{-(d/10)k₀}`, and of the squared upper-leg scale with the
  printed `γ(L-n)3^{2γ(L-n)}`: both are the consumer's, as
  `WaveThirdTermSquared.lean` already records.  The statements below carry the
  proved scales verbatim.

## Main results

* `sum_cubeMassRatio_mul_cubeAverage_le_streamIncrementLpMass`: the cube
  average, in the corrected volume-weighted form.
* `sqrt_streamIncrementLpMass_four_eq_streamIncrementLpNorm_sq`: the root.

## References

* ABK26, `p.bfA.multiscalebound`, Step 2 and Step 3's `|b_L|` branch;
  (`\avsum`); (the Whitney layers and `e.SW.def`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The manuscript's `ℓ` -/


/-! ## The cube average, in the corrected volume-weighted form -/

/-- **The layer's volume-weighted `L^p` mass is at most the root cube's** (
corrected route).  A Whitney layer is a sub-family of the depth-`j` descendants
of `□_m`, whose *full* weighted sum is the root mass by the descendant identity
`Stream.streamIncrementLpMass_eq_descendantsAverage`; the density is
nonnegative, so dropping the other descendants only decreases the sum. -/
theorem sum_cubeMassRatio_mul_cubeAverage_le_streamIncrementLpMass {p : ℝ}
    (hp : 0 < p) (m : ℤ) (j : ℕ) {S : Finset (TriadicCube d)}
    (hS : S ⊆ descendantsAtDepth (originCube d m) j) (n1 n2 : ℤ)
    (omega : ShellSeq d) :
    ∑ Q ∈ S, cubeMassRatio (originCube d m) Q *
        cubeAverage Q (streamIncrementLpDensity p n1 n2 omega)
      ≤ streamIncrementLpMass p m n1 n2 omega := by
  classical
  set F : TriadicCube d → ℝ :=
    fun R => cubeAverage R (streamIncrementLpDensity p n1 n2 omega) with hF
  have hF0 : ∀ R : TriadicCube d, 0 ≤ F R := fun R =>
    cubeAverage_nonneg_of_nonneg_on
      (fun x _ => streamIncrementLpDensity_nonneg p n1 n2 omega x)
  have hcard : ((descendantsAtDepth (originCube d m) j).card : ℝ)
      = ((3 : ℝ) ^ d) ^ j := by
    rw [card_descendantsAtDepth_originCube]
    push_cast
    rw [pow_mul]
  have hpos : (0 : ℝ) < ((3 : ℝ) ^ d) ^ j := by positivity
  have hmass : streamIncrementLpMass p m n1 n2 omega
      = (((3 : ℝ) ^ d) ^ j)⁻¹ * ∑ R ∈ descendantsAtDepth (originCube d m) j, F R := by
    rw [streamIncrementLpMass_eq_descendantsAverage hp m n1 n2 j omega,
      descendantsAverage, hcard]
  have hleft : ∑ Q ∈ S, cubeMassRatio (originCube d m) Q * F Q
      = (((3 : ℝ) ^ d) ^ j)⁻¹ * ∑ Q ∈ S, F Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun Q hQ => by
      rw [cubeMassRatio_of_mem_descendantsAtDepth (hS hQ)]
  have hsub : ∑ Q ∈ S, F Q
      ≤ ∑ R ∈ descendantsAtDepth (originCube d m) j, F R :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun R _ _ => hF0 R
  rw [hleft, hmass]
  exact mul_le_mul_of_nonneg_left hsub (inv_nonneg.2 hpos.le)

/-! ## The root -/

/-- **`(⨍ |·|⁴)^{1/2} = ‖·‖²_{L⁴}`.**  The `L⁴` norm is the fourth root of the
mass, so its square is the mass's square root.  This is the step that turns the
corrected volume-weighted quantity into the *left-hand side of the proved
squared display*. -/
theorem sqrt_streamIncrementLpMass_four_eq_streamIncrementLpNorm_sq (l n1 n2 : ℤ)
    (omega : ShellSeq d) :
    Real.sqrt (streamIncrementLpMass 4 l n1 n2 omega)
      = streamIncrementLpNorm 4 l n1 n2 omega ^ 2 := by
  have h0 : (0 : ℝ) ≤ streamIncrementLpMass 4 l n1 n2 omega :=
    streamIncrementLpMass_nonneg 4 l n1 n2 omega
  rw [streamIncrementLpNorm,
    ← Real.rpow_natCast (streamIncrementLpMass 4 l n1 n2 omega ^ (4 : ℝ)⁻¹) 2,
    ← Real.rpow_mul h0, Real.sqrt_eq_rpow]
  norm_num

/-! ## The seam at the manuscript's own `ℓ` -/


/-! ## The seam at a deterministic `ℓ`, with the three Orlicz legs -/


end

end Algsuperdiff.Section3.Provider.Multiscale
