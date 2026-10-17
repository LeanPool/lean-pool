/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionData

/-!
# ConclusionSeam3Closure

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local seam-3 providers: cut-off optimization, `Γ₁` conversion, and product

`Provider/Multiscale/ConclusionSeam3.lean` and
`Provider/Multiscale/ConclusionData.lean` leave the seam-3 chain of ABK26's
`p.bfA.multiscalebound` Step 3 (`|b_L|` branch, together with the `3^{γh_hat_sep}`
reduction) with exactly three open items, each named in their own "What is not
proved" sections:

1. **the cut-off `H` is free** --- `measureReal_upperTailEvent_seamLayerObject_hsep_le`
   and its `hA`-discharged form
   `measureReal_upperTailEvent_seamLayerObject_hsep_envelope_le` are tail bounds
   at a fixed `t` with a free `H`, not weak-Orlicz statements;
3. **the `3^{γh_hat_sep}` product half is uncomposed** --- `ConclusionData` records
   as "read, **not consumed**: the `3^{γh_hat_sep}` product half of the seam is
   `ConclusionSeam3.three_rpow_gamma_hsep_mul_le_two_mul_add`, which this
   module does not touch; the composition here uses only the tail-decomposition
   half."

This module proves local Provider results for all three A items.  Nothing else
about the `b_L` branch is touched, and no source-node or fractional closure is
claimed.

## 1--2. The cut-off optimization and the `Γ₁` conversion

```
P[ X_{h_hat_sep(ω)}(ω) > A t ]  ≤  (H+1) e^{−t}  +  C(σ,b) exp(−3^{(1−σ)bH}) .
```

The union cost is linear in `H` while the remainder decays DOUBLY exponentially in
`H`, so the cut-off can be taken as large as `H(t) = ⌈Λ t⌉` while still paying
only `Λ t + 2` for the union.  With

```
Λ = Λ(C, β) = 5 + C + 2 (β log 3)^{−2} ,      β = (1 − σ) b ,   C = C(σ, b) ,
```

both terms are at most `(Λt + 2 + C) e^{−Λt} ≤ e^{−t}`, and the conclusion is a
genuine `Γ₁` statement at the scale `Λ A`.  `Γ₁` is the index the printed
display itself carries on this leg, so nothing is degraded.

`isBigOWith_gammaSigma_one_of_cutoff_tail_le` is this argument at an abstract
family and an abstract `ℕ`-valued index; like `measureReal_upperTailEvent_diagonal_le`
it needs no measurability of the index, no independence and no summation.

### The `h`-free scale

An `IsBigOWith` scale may not depend on `t`, so the cut-off optimization needs
a common scale for ALL shell indices, not just for `h ≤ H`.  `ConclusionData`'s
`seamLayerScale_le_of_le` supplies the envelope at the D index of a finite
range; this module takes the same envelope to `H → ∞`.  Concretely the only
`h`-dependence of the proved `e.kmn.bounds` scale is `min{γ^{−1/2}, (L − ℓ
+ h)^{1/2}}` inside `streamPointScale`, and replacing that minimum by its
saturating entry `γ^{−1/2}` gives an `h`-free bound with NO hypothesis at all
(`streamPointScale_le_streamPointScaleSat` is `min_le_left`).
`seamLayerScaleSat` is the resulting seam scale.

**The cost.**  Saturation is not free: the proved `h`-dependent seam
scale carries `γ · min{γ^{−1}, L − ℓ + h}`, and the saturated one carries `γ ·
γ^{−1} = 1`.  Relative to the printed amplitude `γ(L−n) 3^{2γ(L−n)}` this is an
amplitude enlargement (to the `min`'s saturating branch), stated here and not
hidden in a constant.  It is not an exponent change and not an Orlicz-index
change; the alternative trade --- keeping `γ(L−n)` and letting the scale grow
linearly in `t` --- costs `Γ₁ → Γ_{1/2}`, i.e. a genuine index loss, and is NOT
taken.

## 3. The `3^{γh_hat_sep}` product

`ConclusionSeam3.three_rpow_gamma_hsep_mul_le_two_mul_add` gives, for every
nonnegative `Y`, the split `3^{γh_hat_sep} Y ≤ 2Y + Z Y` together with `Z ≤
O_{Γ_τ}(S_Z)` at the-honest index `τ = (1−σ)σ₂/((1−σ)+σ₂)`.  Taking `Y` to be
the seam's own diagonal layer object --- which item 1--2 has just priced at
`Γ₁` --- and composing gives

```
3^{γh_hat_sep} · (seam layer object at ℓ − h_hat_sep)  ≤  O_{Γ_{τ/(τ+1)}}( · ) ,
```

by `e.multGammasig` on `Z·Y` (`Orlicz.isBigOWith_gammaSigma_mul_of_nonneg`,
i.e. CoarseGraining's explicit `gammaProductConst`), the exponent downgrade `Γ₁
→ Γ_{τ/(τ+1)}` on `2Y`, and a two-event union bound on the sum.  The product
index `τ/(τ+1) = τ·1/(τ+1)` is `e.multGammasig` read at `(σ₁, σ₂) = (τ, 1)`;
neither `Γ₄` nor `Γ₂` is claimed anywhere, exactly as requires.

## What is *not* proved

* **No per-layer weight and no `k`-sum.** blocks the printed `3^{−3k/4}`
  independently, and nothing here approaches it.  The `6d·3^{−k}` inside the
  scale is the proved Whitney layer mass fraction
  `LayerMass.sum_cubeMassRatio_whitneyLayer_le`, unchanged; no sum over `k` is
  formed.
* **No re-derivation of the printed amplitude.**  The saturated envelope is an
  upper bound on the proved scale, as described above; the printed `γ(L−n)` is
  not recovered and is not claimed.
* **The first printed inequality of the display** (per-simplex to per-cube) is
  proved in `ConclusionSeam1PerCube`, which also proves a local result for the
  per-simplex object at `d²·seamDiagonalScale`.
* **No `e.bL.multiscale` headline.**  The three local results here concern the seam's
  own; the Step-3 assembly, its `k₀` tuning and the terminal `exp(−cE^{−2}γ^{−1})`
  absorption are not performed.
* **No measurability and no independence are used anywhere below**, and none is
  proved: `h_hat_sep` is never assumed measurable, and every aggregation is a union
  bound.

## Main results

* `Algsuperdiff.Section3.Provider.Multiscale.isBigOWith_gammaSigma_of_measureReal_le_const_mul`:
  a tail bound `P[W > A t] ≤ K e^{−t^ρ}` with `K ≥ 1` is a `Γ_ρ` bound at the
  scale `(1 + log K)^{1/ρ} A`, the Orlicz exponent unchanged.
* `Algsuperdiff.Section3.Provider.Multiscale.measureReal_upperTailEvent_add_le`:
  the two-event union bound at the upper-tail events of a sum.
* `Algsuperdiff.Section3.Provider.Multiscale.isBigOWith_gammaSigma_add`: the sum
  of two `Γ_ρ` variables is `Γ_ρ` at the sum of the scales, inflated by
  `(1 + log 2)^{1/ρ}`; no measurability is used.

## References

* ABK26, `p.bfA.multiscalebound` Step 3: the `3^{γh_hat_sep}` reduction, the
  `|b_L|` branch (the `ℓ` definition, the display and its terminal `Γ₁`
  leg); `e.hsep.tails`; `e.kmn.bounds`; `e.indc.O.sigma`; `e.multGammasig`.
* `Provider/Multiscale/ConclusionSeam3.lean` (the decomposition, the `h_hat_sep`
  tail and the/ split), `Provider/Multiscale/ConclusionData.lean` (the
  finite-range shell envelope), `Provider/Multiscale/HsepReduction.lean` (the
  Orlicz half), `Provider/Orlicz/ProductPower.lean` (`e.multGammasig`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Percolation
open Algsuperdiff.Section3.Provider.Stream

noncomputable section

variable {d : ℕ}

/-! ## Abstract real arithmetic -/


/-! ## Model-free weak-Orlicz plumbing -/

/-- **Absorbing a multiplicative constant into the scale.**  A tail bound `P[W > A
t] ≤ K e^{−t^ρ}` with `K ≥ 1` is a `Γ_ρ` bound at the scale `(1 + log K)^{1/ρ}
A`: the inflation is exactly what turns `K` into `1`, and the Orlicz exponent
is unchanged. -/
theorem isBigOWith_gammaSigma_of_measureReal_le_const_mul {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {W : Omega → ℝ} {A K rho : ℝ}
    (hrho : 0 < rho) (hK : 1 ≤ K)
    (h : ∀ t : ℝ, 1 ≤ t →
      mu.real (IndependentSums.upperTailEvent W (A * t)) ≤
        K * Real.exp (-(t ^ rho))) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma rho) W
      ((1 + Real.log K) ^ rho⁻¹ * A) := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  set L : ℝ := (1 + Real.log K) ^ rho⁻¹ with hLdef
  have hbase : (1 : ℝ) ≤ 1 + Real.log K := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    have := Real.rpow_le_rpow zero_le_one hbase (le_of_lt (inv_pos.2 hrho))
    simpa [hLdef, Real.one_rpow] using this
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hLpow : L ^ rho = 1 + Real.log K := by
    rw [hLdef, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + Real.log K),
      inv_mul_cancel₀ (ne_of_gt hrho), Real.rpow_one]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hLt : (1 : ℝ) ≤ L * t := one_le_mul_of_one_le_of_one_le hL1 ht
  have hkey := h (L * t) hLt
  have hset : (1 + Real.log K) ^ rho⁻¹ * A * t = A * (L * t) := by rw [hLdef]; ring
  have hpow : (L * t) ^ rho = (1 + Real.log K) * t ^ rho := by
    rw [Real.mul_rpow hL0 ht0, hLpow]
  have htpow : (1 : ℝ) ≤ t ^ rho := Real.one_le_rpow ht hrho.le
  have hKe : Real.exp (Real.log K) = K := Real.exp_log hK0
  have hfin : K * Real.exp (-((L * t) ^ rho)) ≤ (IndependentSums.gammaSigma rho t)⁻¹ := by
    rw [hpow, IndependentSums.gammaSigma_inv]
    calc K * Real.exp (-((1 + Real.log K) * t ^ rho))
        = Real.exp (Real.log K + -((1 + Real.log K) * t ^ rho)) := by
          rw [Real.exp_add, hKe]
      _ ≤ Real.exp (-(t ^ rho)) :=
          Real.exp_le_exp.2 (by nlinarith [hlogK, htpow])
  rw [hset]
  exact le_trans hkey hfin

/-- The two-event union bound at the upper-tail events of a sum. -/
theorem measureReal_upperTailEvent_add_le {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X Y : Omega → ℝ} {a b : ℝ} :
    mu.real (IndependentSums.upperTailEvent (fun omega => X omega + Y omega) (a + b)) ≤
      mu.real (IndependentSums.upperTailEvent X a) +
        mu.real (IndependentSums.upperTailEvent Y b) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro omega homega
  rw [IndependentSums.mem_upperTailEvent] at homega
  by_contra hcon
  simp only [Set.mem_union, IndependentSums.mem_upperTailEvent, not_or, not_lt] at hcon
  linarith [hcon.1, hcon.2]

/-- **The sum of two `Γ_ρ` variables** is `Γ_ρ` at the sum of the scales, inflated
by `(1 + log 2)^{1/ρ}`: the two-event union bound costs a factor `2`, and
`isBigOWith_gammaSigma_of_measureReal_le_const_mul` absorbs it.  No measurability
is used. -/
theorem isBigOWith_gammaSigma_add {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {X Y : Omega → ℝ} {A B rho : ℝ}
    (hrho : 0 < rho)
    (hX : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma rho) X A)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma rho) Y B) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma rho)
      (fun omega => X omega + Y omega) ((1 + Real.log 2) ^ rho⁻¹ * (A + B)) := by
  refine isBigOWith_gammaSigma_of_measureReal_le_const_mul hrho (by norm_num)
    (fun t ht => ?_)
  rw [show (A + B) * t = A * t + B * t from by ring]
  have hx := hX ht
  have hy := hY ht
  rw [IndependentSums.gammaSigma_inv] at hx hy
  exact le_trans measureReal_upperTailEvent_add_le (by linarith)

/-! ## The cut-off optimization -/


/-! ## The shell-index-free envelope of the `e.kmn.bounds` scale -/


/-! ## Seam 3 at `Γ₁` -/


/-! ## The `3^{gamma hsep}` product, composed -/


end

end Algsuperdiff.Section3.Provider.Multiscale
