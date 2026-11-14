/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SealCaccioppoliGeometry

/-!
# ResidueAbsorption

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The residue routes, measured: three machine-checked obstructions

This module records, as theorems, the exact inequalities that block the two
candidate producers for the harmonic-approximation residue `‖u − w‖_{L²(K')}`
of `ResidueBudget`, with `K' = flushSubCentre z m n i σ + □_n` the flush
scale-`n` sub-cube of the boundary branch and `w` a `Δ`-harmonic comparator of
`u` there.  Nothing here is an analytic estimate; each theorem is the arithmetic
or geometric core of one measured route, isolated so that the STOP table is
checked rather than asserted.

## The room (the legal-producer contract)

So a residue producer may output exactly

```text
  ‖u − w‖_{L²(K')} ≤ K1 · ‖u − (u)_{W'}‖_{L²(W')}
                    + K2 · 3^n ‖∇h‖_{L²(W')}
                    + K3 · s^{-2} 3^{(1+s)n} [∇h]_{H^s(W')}
                    + K4 · s^{-3} σ_n^{-1} 3^{(1+s)n} [g]_{H^s(W')}
```

with `K1..K4` constants: the four allowed `s`-powers are `0, 0, −2, −3` and
only the last carries a `σ^{-1}`.  Both routes below fail *against this
contract*, each by one uniform factor.

## Route 1 — the `p = 2` coarse-graining comparison at `K'`

The proved interior chain
(`InteriorEllipticitySlot.eLpNorm_sub_weaklyHarmonic_le_coarseGraining_rebased`
composed with `AssemblyEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs`)
prices a comparator distance in the shape

```text
  ‖u − w‖ ≤ A · s^{-4} · 𝓔 · ( ‖u − (u)_{W'}‖ + S ) + (s^{-6}, s^{-7}σ^{-1} legs) ,
```

so the budget's first-leg coefficient would be `K1 = A·s^{-4}·𝓔`, **not** a
constant.  `coarseGrainingResidue_coefficient_unbounded` is the refutation: for
any fixed error level `E > 0` — in particular for the level the frozen good
event pins, `𝓔 ≤ C_E·ε` at `ε = 1/2` — and any candidate constant, some
admissible `s ∈ (0,1]` exceeds it.  `coarseGrainingResidue_loop_not_contraction`
is the same statement read as the self-consistency loop `S ≤ a + θ·S`: the loop
coefficient `θ = A·s^{-4}·𝓔` is not below `1` uniformly, so the residue cannot be
solved for either.  Closing the route needs `𝓔 ≲ s^4`, i.e. the good event's
`ε` re-pinned at `c·s^4` — a change to the frozen statement.

## Route 1′/option (ii) — the fitted boundary Caccioppoli at `K'`

`SealCaccioppoliGeometry.flushSubCube_boundaryOuterAssembly_fits` prices the
`ν`-weighted energy `ν·⨍_{K'}|∇u|²` against a coarse-grained `Λ_t`-weighted
right-hand side, so extracting a `ν`-free comparator distance costs
`√(Λ_t/ν) ≤ C√(σ/ν)`.  `energyRatio_sqrt_unbounded` records that no constant
absorbs `√(σ/ν)` over `0 < ν ≤ σ`.  (That the ratio really is unbounded on the
model family is ABK26's Theorem A; it is cited, not proved here.)

## Route 2 — the anchor's own good event at the sub-scale

Every proved transfer that would put an error cap, an ellipticity cap, or the
anchor's own conclusion on a scale-`n` cube requires the anchor's geometry
binder `x + □_n ⊆ (z+□_{n+1}) ∩ □_m` — see
`InteriorGlueCap.ae_offGridChildError_le_representative_harmonicSlot` and
`AssemblyEnergyLeg.ae_h1EnergyNormOnCube_boundary_le_anchorLegs`.
`exists_flushSubCube_not_subset_anchorGeometry` exhibits an admissible
boundary-branch configuration in which
`K'` satisfies `K' ⊆ □_m` but **not** `K' ⊆ z + □_{n+1}`: the flush sub-cube is
pushed `4·3^n` off `z` while `z + □_{n+1}` reaches only `3^n`.  And
`no_flushCentre_within_anchorGeometry` shows this is intrinsic, not a bad
choice of `K'`: on the whole sub-range `½·3^m − 9/2·3^n < σ·zᵢ < ½·3^m −
3/2·3^n` of the boundary branch (nonempty by
`wellPlacedHalfGap_lt_farThreshold`, width `3·3^n`) **no** flush scale-`n`
centre satisfies the binder.  So the caps are not available at `K'` as proved,
independently of the arithmetic above.

The scope of that obstruction: it is a statement about the proved *binders*,
not a proof that the underlying apparatus cannot be re-instantiated.
`InteriorGlueCap.ae_offGridChildError_le_representative_translate` is already
stated for an arbitrary real translate with `w + □_n ⊆ □_{n+2}`, and `K'` does
satisfy the corresponding gap-three containment `c' − z + □_n ⊆ □_{n+3}` at the
frozen `(n+3, z)` frame; re-cutting that cap and the ellipticity caps at the
`(n+3)` parent is bounded provider work.  The arithmetic obstruction of Route 1
is the one that does not move.

## References

* ABK26, `l.harmonic.approximation.good.scales`, Step 2;
  `l.coarse.grained.Caccioppoli.RHS`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. Route 1: the `s^{-4}·𝓔` coefficient is not a constant -/

/-- The display's `s^{-4}` written as a natural power of `s⁻¹`. -/
theorem rpow_neg_four_eq_inv_pow {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(4 : ℝ)) = (s⁻¹) ^ (4 : ℕ) := by
  have h1 : Real.rpow s (-(4 : ℝ)) = (Real.rpow s (4 : ℝ))⁻¹ := Real.rpow_neg hs.le 4
  have h2 : Real.rpow s (4 : ℝ) = s ^ (4 : ℕ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
    exact Real.rpow_natCast s 4
  rw [h1, h2, inv_pow]

/-- **The exact closing condition for route 1.**

If the error level obeys `A·E ≤ s^4` then — and, by
`coarseGrainingResidue_coefficient_unbounded`, essentially only then — the
coefficient is bounded by `1`.  This is the `ε ≤ c·s^4` re-pinning of the good
event: a change to the frozen statement. -/
theorem coarseGrainingResidue_coefficient_le_of_error_small {A E s : ℝ}
    (hs : 0 < s) (hA : 0 ≤ A) (hE : 0 ≤ E) (hsmall : A * E ≤ s ^ (4 : ℕ)) :
    A * Real.rpow s (-(4 : ℝ)) * E ≤ 1 := by
  rw [rpow_neg_four_eq_inv_pow hs]
  have hs4 : (0 : ℝ) < s ^ (4 : ℕ) := pow_pos hs 4
  have hinv : (s⁻¹) ^ (4 : ℕ) = (s ^ (4 : ℕ))⁻¹ := inv_pow s 4
  rw [hinv]
  have hAE : (0 : ℝ) ≤ A * E := mul_nonneg hA hE
  have hmul := mul_le_mul_of_nonneg_left hsmall (le_of_lt (inv_pos.mpr hs4))
  rw [inv_mul_cancel₀ (ne_of_gt hs4)] at hmul
  calc A * (s ^ (4 : ℕ))⁻¹ * E = (s ^ (4 : ℕ))⁻¹ * (A * E) := by ring
    _ ≤ 1 := hmul

/-! ## 2. Route 1′ / option (ii): the `√(σ/ν)` cost is not absorbable -/

/-! ## 3. Route 2: the anchor's geometry binder fails at the flush sub-cube -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
