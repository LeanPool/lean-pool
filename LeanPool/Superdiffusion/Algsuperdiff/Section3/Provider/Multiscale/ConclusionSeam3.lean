/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LayerMass
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.LayerPerCubePricing
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.HsepReduction

/-!
# ConclusionSeam3

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Seam 3: the `h_hat_sep` decomposition at the `b_L` seam

The per-cube `Γ₁` pricing of the seam's layer object is available at a
*deterministic* shell pair only, and supplying the deterministic index is what
**seam 3** means.  `Provider/Multiscale/ConclusionSeam2.lean` records the same
gap: `ℓ` and the shell index `ℓ − h_hat_sep` are sample-dependent, while a
weak-Orlicz statement needs a deterministic index.

This module fixes the carrier that seam 3 is stated at: the seam's layer object
read at a deterministic index.  The decomposition that would close the gap ---
split the sample space over the countably many values of `h_hat_sep`, apply the
deterministic-index estimate on each piece, and pay for the pieces above a
cut-off `H` with the proved tail of `h_hat_sep` --- is described below, so that the
carrier can be read against it; it is not performed here.

## The shape of the answer

There is no free lunch: the diagonal observable `ω ↦ X_{h_hat_sep(ω)}(ω)` is NOT
`Γ_σ` at the common scale of the family `X_h`, and nothing below claims it is.
What is true is the finite-cut-off tail bound

```
P[ X_{h_hat_sep(ω)}(ω) > A t ]  ≤  (H+1) e^{-t^σ}  +  P[ h_hat_sep > H ] ,
```

for every `H`, every `t ≥ 1` and every common scale `A` dominating the `H+1`
individual scales.  At an abstract family and an abstract `ℕ`-valued index this
is a pure measure-theoretic decomposition (the events `{h_hat_sep = h}` for `h ≤ H`
together with `{h_hat_sep > H}` cover, and the diagonal event meets the `h`-th
piece inside the `h`-th tail event); it needs NO measurability of the index and
NO independence, only monotonicity, countable subadditivity on a finite union
and finiteness of the measure.

Two remarks on why this is the honest shape.

* The naive `∑_h P[X_h > At]` over all `h` diverges: each term is bounded by
  `e^{-t^σ}` uniformly in `h`, so the sum over the infinitely many values of
  `h_hat_sep` is useless.  The cut-off `H` is what makes the decomposition
  summable, and the price is the second term.
* The second term is not an assumption: it is the proved
  `Percolation.measureReal_scaleSeparationFail_le_of_gates` (`e.hsep.tails`)
  read through `Percolation.scaleSeparationFail_eq`, giving `P[h_hat_sep > H] ≤
  C(σ,b) exp(−3^{(1−σ)bH})` for `H ≥ 1`
  (`RandomHsepAllLWaveEnvelope.measureReal_lt_hsep_le_of_gates`).  So the
  composed bound has NO undischarged probabilistic input.

## The instantiation at the seam

`seamLayerObject M m h k ℓ h' L` is the seam's own left-hand quantity

```
γ 3^{−2γℓ} ( ∑_{□ ∈ 𝒲(□_m,k)} (|□|/|□_m|) ⨍_□ |k_L − k_{ℓ−h'}|⁴ )^{1/2}
```

at the deterministic index `h'`.  It is exactly the quantity the per-cube `Γ₁`
pricing is stated at, with `n1 = ℓ − h'` and `n2 = L`, and its scale keeps the
layer's own mass fraction `6d·3^{−k}`; reading it at the DIAGONAL index
`h' = h_hat_sep(ω)` is what the decomposition above has to be applied to.

The composition itself is not carried out here.  Its one interface datum is
`hA`, a common scale dominating the `H+1` individual scales; that is a datum
and not a theorem because `streamIncrementLpMassScale M 4 (ℓ−h) L` varies with
`h` and this repository has no monotonicity statement for it (see "What is not
proved").

## The `3^{γ h_hat_sep}` re-pricing

The other half of the seam is the pointwise split, for every nonnegative `Y`,

```
3^{γ h_hat_sep} Y  ≤  2 Y + Z Y ,        Z = 3^{γ h_hat_sep} 1_{γ h_hat_sep > 3^{−4}} ,
```

with `Z` carried at `Γ_{(1−σ)σ₂/((1−σ)+σ₂)}` and at the explicit
`exp(−cγ^{−1})`-sized scale of `HsepReduction`, which is where that half is
proved.  It is the `HsepReduction` display multiplied by a nonnegative factor,
at the honest product index; neither `Γ₄` nor `Γ₂` is claimed anywhere, and no
new Orlicz input is used.

## What is *not* proved

* **`hA` is not discharged.**  A common scale for `h ≤ H` requires monotonicity
  (or an explicit envelope) of `h ↦ streamIncrementLpMassScale M 4 (ℓ−h) L`,
  which is not proved.  This is the precise missing input, named here rather
  than smuggled: it is a property of `e.kmn.bounds`' envelope, not of the seam.
* **No `Γ_σ` statement for the diagonal observable.**  The decomposition above
  yields a tail bound at a fixed `t`, not an `IsBigOWith`; converting it into
  one needs `H = H(t)`.  The optimization is not made in THIS file.
* **No `k`-decay and no printed per-layer weight**: blocks `3^{−3k/4}`
  independently, and nothing here approaches it.  The `6d·3^{−k}` inside the
  scale is the proved Whitney layer mass fraction
  `LayerMass.sum_cubeMassRatio_whitneyLayer_le`, unchanged.
* **The first printed inequality of the display** (per-simplex to per-cube)
  remains unlanded, exactly as `ConclusionSeam2` records.

## Main definitions

* `Algsuperdiff.Section3.Provider.Multiscale.seamLayerObject`

## References

* ABK26, `p.bfA.multiscalebound` Step 3, (the `3^{γh_hat_sep}` reduction) and the
  `b_L` branch; `e.hsep.tails`; `p.minimal.scale.separation`.
* `Provider/Multiscale/ConclusionSeam2.lean` (the layer fit and the `Γ₁`
  pricing), `Provider/Multiscale/HsepReduction.lean` (the Orlicz half),
  `Provider/Percolation/MinimalScaleSeparation.lean` (the `h_hat_sep` tail).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The abstract decomposition over the values of a random index -/


/-! ## The tail of the truncation depth -/


/-! ## The seam's layer object at a deterministic index -/

/-- **The seam's layer object at a D shell index** (ABK26, in the corrected
volume-weighted reading): `γ 3^{−2γℓ} (∑_{□ ∈ 𝒲(□_m,k)} (|□|/|□_m|) ⨍_□ |k_L −
k_{ℓ−h}|⁴)^{1/2}`. -/
def seamLayerObject (M : ABKModel d) (m : ℤ) (hn : ℕ → ℕ) (k : ℕ) (ell : ℤ) (h : ℕ)
    (L : ℤ) (omega : CutoffSample d) : ℝ :=
  M.gamma * (3 : ℝ) ^ (-(2 * M.gamma * (ell : ℝ))) *
    Real.sqrt (∑ Q ∈ whitneyLayer (d := d) m hn k,
      cubeMassRatio (originCube d m) Q *
        cubeAverage Q (streamIncrementLpDensity 4 (ell - (h : ℤ)) L omega.1))


/-! ## Seam 3 -/


/-! ## The `3^{gamma hsep}` re-pricing -/


end

end Algsuperdiff.Section3.Provider.Multiscale
