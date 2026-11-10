/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Series.FractionTopology
public import LeanPool.HyperellipticCurves.Series.LogIso

/-!
# Evaluating the scaled logarithm over the fraction field

The `π`-scaled logarithm `ChabautyColeman.FormalGroupLaw.scaledLog` of a formal group law
`Φ` over the DVR `O`, taken along a uniformizer `π` with `p ∣ π ^ e` and `p > e + 1`,
evaluates integrally: `evalT y (scaledLog i) ∈ O` represents the honest logarithm
`Λ = (Φ.map f).log` at the rescaled point `π·y`, the actual chart coordinates.

`ChabautyColeman.hasSum_algebraMap_evalT_scaledLog` transports this to the valued fraction
field `K = FractionRing O`: the image of the integral value `evalT y (scaledLog i)` is the
convergent sum of the honest logarithm series at `π·y`, over `K`. The `π`-scaling built into
`scaledLog` (the `f(π)^{deg d}` factor of
`ChabautyColeman.FormalGroupLaw.coeff_scaledLog_map`) is exactly what makes the `O`-level sum
converge and its `f`-image the honest `Λ`-value — the `Λ`-series itself carries `p`-power
denominators and only converges over `K` for arguments in the open unit disk. This realizes
the `p`-adic Coleman-integral value of the logarithm as the pushforward, along the continuous
inclusion `O ↪ K`, of the integral `O`-level value.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology
open ChabautyColeman.MvPSeries ChabautyColeman.FractionTopology

namespace ChabautyColeman

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [UniformSpace O] [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O]
  [CompleteSpace O] [IsTopologicalRing O]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {π : O} {p e : ℕ}

/-- **Transport of the scaled-logarithm evaluation to the fraction field**: the integral value
`evalT y (scaledLog i)` of the `π`-scaled logarithm at a point `y`, pushed into
`K = FractionRing O`, is the convergent sum of the honest logarithm series
`Λ_K = (Φ.map f).log` at the rescaled point `π·y` (the actual chart coordinates). The
`π`-scaling of `scaledLog` is exactly absorbed by the `f(π)^{deg d}` factor. This realizes the
`p`-adic Coleman-integral value of the logarithm as the image of the integral `O`-level
value. -/
theorem hasSum_algebraMap_evalT_scaledLog (Φ : FormalGroupLaw O ι)
    (hram : IsUniformizer π p e)
    (hpe : e + 1 < p) (hfp : algebraMap O (FractionRing O) (p : O) ≠ 0)
    (y : ι → O) (i : ι) :
    HasSum (fun d : ι →₀ ℕ ↦ coeff d ((Φ.map (algebraMap O (FractionRing O))).log i)
        * d.prod fun s k ↦ algebraMap O (FractionRing O) (π * y s) ^ k)
      (algebraMap O (FractionRing O)
        (evalT y (Φ.scaledLog hram hpe (algebraMap O (FractionRing O)) hfp i))) := by
  set f := algebraMap O (FractionRing O)
  refine ((hasSum_evalT y (Φ.decay_scaledLog hram hpe hfp i)).map f
    continuous_algebraMap).congr_fun fun d ↦ ?_
  simp only [Function.comp_apply, map_mul, map_finsuppProd, map_pow]
  rw [Φ.coeff_scaledLog_map hram hpe hfp i d]
  have hprod : (d.prod fun s k ↦ (f π * f (y s)) ^ k)
      = f π ^ d.degree * d.prod fun s k ↦ f (y s) ^ k := by
    simp only [Finsupp.prod, Finsupp.degree_apply, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
  rw [hprod]; ring

end ChabautyColeman

end
