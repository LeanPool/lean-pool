/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionArithmetic
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.LayerDensity

/-!
# ConclusionAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The layer series of `p.bfA.multiscalebound`, Step 3, at the corrected density

ABK26, proof of Proposition `p.bfA.multiscalebound`, **Step 3**.  After the
per-layer estimates are in place the manuscript sums over the Whitney layer
index `k`,

```
  sum_k 3^{-k} ( C 3^{gamma (k + h_k)}
                 + C 3^{2 b (k + h_k)} ( bad density of layer k ) )
    <=  C 3^{gamma (hsep + k_0)} ( 1 + 3^{2 b (hsep + k_0)}
              ( exp(-c E^{-2} gamma^{-1}) + 3^{-k_0/2} ) ) ,
```

and then collapses the `k_0`-dependent factor.

## What changes against the printed Step 3

`l.bad.cubes.density` is available here only in its **mass** form,
`Provider.Whitney.sum_cubeMassRatio_badFamilyLayer_le`: the bad mass of layer
`k` *relative to* `cu_m`.  The printed Step 3 weights that quantity by the
layer's own mass fraction `3^{-k}` a second time, and with only the mass form
the resulting `k`-sum of the `exp(-c E^{-2} gamma^{-1})` leg diverges.
Concretely, `layerContrib` below weights

* the **good** leg by the layer's own mass `Mass k` (bounded by
  `Cmass 3^{-k}`), and
* the **collar** leg by the bad mass `Bad k` itself -- no second `3^{-k}` --
  using `Bad k <= min{Cmass 3^{-k}, eps + 3^{-(k + h_k)/2}}
        <= sqrt(Cmass) 3^{-k/2} (eps + 3^{-(k+h_k)/2})^{1/2}`.

The `3^{-k/2}` that survives degrades the series ratio from the printed
`3^{-3/4}` to `3^{-1/4}` (`three_rpow_layerQuantity_collar_decay`) and forces the
square-root collapse `k0_sqrt_collapse` with its exponent `1/36` in place of the
printed `1/4`.  Both are in `Provider.Multiscale.ConclusionArithmetic`.

## The layer-mass A input and its downstream producer

`LayerMassBound m hn Cmass` -- "the Whitney layer `k` carries mass at most
`Cmass 3^{-k}` inside `cu_m`" -- is not proved in this file and is carried as
an explicit A hypothesis wherever it is needed.  It is a purely combinatorial
statement about `Provider.Whitney.whitneyLayer`: the layer-`k` cubes sit under
the depth-`(k-1)` descendants of `cu_m` that touch `∂cu_m`, of which there are
at most `2 d 3^{(k-1)(d-1)}` out of `3^{d(k-1)}`, so the expected constant is
`Cmass = 6 d`.  The downstream file `LayerMass.lean` now proves and applies
this bound at that constant.  The declarations here retain the abstract input
and therefore remain conditional; the downstream discharge is not a premise of
the source statement and does not turn this file into a node closure.

## What is *not* here

In this file, the `3^{gamma hsep}` prefactor reduction stops after its
**deterministic** half's display `three_rpow_le_two_add_indicator` (in
`ConclusionArithmetic`), and the bridge from the manuscript's `3^{gamma hsep}`
to the proved tail `Provider.Percolation.isBigOWith_gammaSigma_three_rpow_hsep`
(which is stated at `3^{b hsep}`, at the amplitude `hsepAmplitude sigma b`
rather than the printed `1`) is `three_rpow_gamma_hsep_le_three_rpow_b_hsep`.
The remaining Orlicz half -- `e.indc.O.sigma` for the indicator and
`e.multGammasig` for the product -- is assembled only in later multiscale
providers.

## References

* ABK26, `p.bfA.multiscalebound`, Step 3.
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## The Whitney layer quantity `k + h_k` -/

/-- **ABK26's layer quantity `k + h_k`** as a real, at the proved scale profile
`Provider.Whitney.whitneyScaleSeq` (`h_k = ceil(b (1-b)^{-1} k) + hsep
+ k_0`). -/
def layerQuantity (b : ℝ) (hs k₀ k : ℕ) : ℝ :=
  (k : ℝ) + (whitneyScaleSeq b hs k₀ k : ℝ)

/-- Every Whitney layer sits above the tuning scale: `k + h_k >= k_0`. -/
theorem k0_le_layerQuantity (b : ℝ) (hs k₀ k : ℕ) :
    (k₀ : ℝ) ≤ layerQuantity b hs k₀ k := by
  have hnat : k₀ ≤ whitneyScaleSeq b hs k₀ k := by
    have := add_le_whitneyScaleSeq b hs k₀ k
    omega
  have h : (k₀ : ℝ) ≤ (whitneyScaleSeq b hs k₀ k : ℝ) := by exact_mod_cast hnat
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [layerQuantity]
  linarith

theorem layerQuantity_nonneg (b : ℝ) (hs k₀ k : ℕ) : 0 ≤ layerQuantity b hs k₀ k :=
  le_trans (Nat.cast_nonneg k₀) (k0_le_layerQuantity b hs k₀ k)

/-- **Slow growth of the layer quantity** (`e.hn.def` summed): from
`h_k = ceil(b (1-b)^{-1} k) + hsep + k_0` and `ceil t < t + 1`,
`k + h_k <= (1-b)^{-1} k + (hsep + k_0 + 1)`. -/
theorem layerQuantity_le {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (hs k₀ k : ℕ) :
    layerQuantity b hs k₀ k ≤ (1 - b)⁻¹ * (k : ℝ) + ((hs : ℝ) + (k₀ : ℝ) + 1) := by
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have hnn : (0 : ℝ) ≤ b * (1 - b)⁻¹ * (k : ℝ) :=
    mul_nonneg (mul_nonneg hb0.le (le_of_lt (inv_pos.2 h1b))) (Nat.cast_nonneg k)
  have hceil : (⌈b * (1 - b)⁻¹ * (k : ℝ)⌉₊ : ℝ) ≤ b * (1 - b)⁻¹ * (k : ℝ) + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hnn)
  have hcast : (whitneyScaleSeq b hs k₀ k : ℝ)
      = (⌈b * (1 - b)⁻¹ * (k : ℝ)⌉₊ : ℝ) + (hs : ℝ) + (k₀ : ℝ) := by
    rw [whitneyScaleSeq]
    push_cast
    ring
  have hcoef : (1 : ℝ) + b * (1 - b)⁻¹ = (1 - b)⁻¹ := by
    field_simp
    ring
  have hcombine : (k : ℝ) + b * (1 - b)⁻¹ * (k : ℝ) = (1 - b)⁻¹ * (k : ℝ) := by
    calc (k : ℝ) + b * (1 - b)⁻¹ * (k : ℝ) = ((1 : ℝ) + b * (1 - b)⁻¹) * (k : ℝ) := by ring
      _ = (1 - b)⁻¹ * (k : ℝ) := by rw [hcoef]
  rw [layerQuantity, hcast]
  linarith [hceil, hcombine]

/-! ## The two layer decays -/

theorem three_rpow_pow_eq (t : ℝ) (k : ℕ) :
    ((3 : ℝ) ^ t) ^ k = (3 : ℝ) ^ (t * (k : ℝ)) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ t) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- **The printed layer decay**.  For `alpha >= 0` with `4 alpha <= 1 - b`, the
layer mass `3^{-k}` beats the growth `3^{alpha (k+h_k)}` at the printed rate
`3^{-3k/4}`.  Applied at `alpha = gamma` (the good leg of
`e.good.simplex.consequence`) and at `alpha = 2 b` (the collar amplification of
`e.bounds.on.slopes.when.bad`). -/
theorem three_rpow_layerQuantity_decay {b α : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hα0 : 0 ≤ α) (hα : 4 * α ≤ 1 - b) (hs k₀ k : ℕ) :
    (3 : ℝ) ^ (-(k : ℝ)) * (3 : ℝ) ^ (α * layerQuantity b hs k₀ k)
      ≤ (3 : ℝ) ^ (α * ((hs : ℝ) + (k₀ : ℝ) + 1)) * ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcoef : α * (1 - b)⁻¹ ≤ 1 / 4 := by
    have h1 : α ≤ (1 - b) / 4 := by linarith
    have h2 : α * (1 - b)⁻¹ ≤ ((1 - b) / 4) * (1 - b)⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.2 h1b))
    have h3 : ((1 - b) / 4) * (1 - b)⁻¹ = 1 / 4 := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hmul : α * layerQuantity b hs k₀ k
      ≤ α * ((1 - b)⁻¹ * (k : ℝ) + ((hs : ℝ) + (k₀ : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (layerQuantity_le hb0 hb1 hs k₀ k) hα0
  have hexp : α * ((1 - b)⁻¹ * (k : ℝ) + ((hs : ℝ) + (k₀ : ℝ) + 1))
      = α * (1 - b)⁻¹ * (k : ℝ) + α * ((hs : ℝ) + (k₀ : ℝ) + 1) := by ring
  have hstep : α * (1 - b)⁻¹ * (k : ℝ) ≤ 1 / 4 * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hcoef hknn
  have hkey : α * layerQuantity b hs k₀ k - (k : ℝ)
      ≤ α * ((hs : ℝ) + (k₀ : ℝ) + 1) + (-(3 / 4 : ℝ)) * (k : ℝ) := by
    linarith [hmul, hstep, hexp.le, hexp.ge]
  calc (3 : ℝ) ^ (-(k : ℝ)) * (3 : ℝ) ^ (α * layerQuantity b hs k₀ k)
      = (3 : ℝ) ^ (α * layerQuantity b hs k₀ k - (k : ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
    _ ≤ (3 : ℝ) ^ (α * ((hs : ℝ) + (k₀ : ℝ) + 1) + (-(3 / 4 : ℝ)) * (k : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hkey
    _ = (3 : ℝ) ^ (α * ((hs : ℝ) + (k₀ : ℝ) + 1)) * ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3), three_rpow_pow_eq]

private theorem three_quarters_mul_half_pow (k : ℕ) :
    ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k * (3 : ℝ) ^ ((k : ℝ) / 2)
      = ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
  have hhalf : (3 : ℝ) ^ ((k : ℝ) / 2) = ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ k := by
    rw [three_rpow_pow_eq]
    congr 1
    ring
  rw [hhalf, ← mul_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 2
  ring

/-- **The corrected collar decay.**  After the Cauchy-Schwarz step only
*half* of the layer mass, `3^{-k/2}`, is available against the collar
amplification `3^{2 b (k+h_k)}`, and the surviving ratio is `3^{-1/4}` rather
than the printed `3^{-3/4}`.  The hypothesis `9 b <= 1` is exactly what
`4 (2 b) <= 1 - b` demands -- the same gate as `k0_sqrt_collapse`. -/
theorem three_rpow_layerQuantity_collar_decay {b : ℝ} (hb0 : 0 < b) (hb9 : 9 * b ≤ 1)
    (hs k₀ k : ℕ) :
    (3 : ℝ) ^ (-(k : ℝ) / 2) * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k)
      ≤ (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
  have hb1 : b < 1 := by linarith
  have hdec := three_rpow_layerQuantity_decay (α := 2 * b) hb0 hb1 (by linarith)
    (by linarith) hs k₀ k
  have hsplit : (3 : ℝ) ^ (-(k : ℝ) / 2)
      = (3 : ℝ) ^ ((k : ℝ) / 2) * (3 : ℝ) ^ (-(k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc (3 : ℝ) ^ (-(k : ℝ) / 2) * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k)
      = (3 : ℝ) ^ ((k : ℝ) / 2) *
          ((3 : ℝ) ^ (-(k : ℝ)) * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k)) := by
        rw [hsplit]; ring
    _ ≤ (3 : ℝ) ^ ((k : ℝ) / 2) *
          ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k) :=
        mul_le_mul_of_nonneg_left hdec (Real.rpow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
          (((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k * (3 : ℝ) ^ ((k : ℝ) / 2)) := by ring
    _ = (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
        rw [three_quarters_mul_half_pow]

/-! ## The per-layer contribution -/

/-- The printed Step 3 puts an extra `3^{-k}` in front of the collar leg shows it
is not available. -/
def layerContrib (b γ : ℝ) (hs k₀ : ℕ) (Ktot Ccol : ℝ) (Mass Bad : ℕ → ℝ) (k : ℕ) : ℝ :=
  Ktot * (Mass k * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k))
    + Ccol * ((3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) * Bad k)

theorem layerContrib_nonneg {b γ Ktot Ccol : ℝ} {hs k₀ : ℕ} {Mass Bad : ℕ → ℝ}
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hMass0 : ∀ j : ℕ, 0 ≤ Mass j)
    (hBad0 : ∀ j : ℕ, 0 ≤ Bad j) (k : ℕ) :
    0 ≤ layerContrib b γ hs k₀ Ktot Ccol Mass Bad k := by
  refine add_nonneg (mul_nonneg hK (mul_nonneg (hMass0 k) (Real.rpow_nonneg ?_ _))) ?_
  · norm_num
  · exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hBad0 k))

/-- **The termwise bound at the density.**  Each layer contributes at most an
explicit constant times `(3^{-1/4})^k`; the collar constant carries `(eps +
3^{-k_0/2})^{1/2}`, exponentially small in `k_0`. -/
theorem layerContrib_le {b γ ε Cmass Ktot Ccol : ℝ} {hs k₀ : ℕ} {Mass Bad : ℕ → ℝ}
    (hb0 : 0 < b) (hb9 : 9 * b ≤ 1) (hγ0 : 0 ≤ γ) (hγ : 4 * γ ≤ 1 - b)
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hCmass : 0 ≤ Cmass) (hε0 : 0 ≤ ε)
    (hMass : ∀ j : ℕ, Mass j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadMass : ∀ j : ℕ, Bad j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadDens : ∀ j : ℕ, Bad j ≤ ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ j / 2)))
    (k : ℕ) :
    layerContrib b γ hs k₀ Ktot Ccol Mass Bad k
      ≤ (Ktot * Cmass * (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1))
          + Ccol * (Real.sqrt Cmass *
              ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
                Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))))
        * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
  have hb1 : b < 1 := by linarith
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
  have hrnn : (0 : ℝ) ≤ ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
    pow_nonneg three_rpow_neg_quarter_nonneg k
  have hratio : ((3 : ℝ) ^ (-(3 / 4 : ℝ))) ^ k ≤ ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
    pow_le_pow_left₀ three_rpow_neg_three_quarters_nonneg
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)) k
  -- the good leg
  have hdecG := three_rpow_layerQuantity_decay hb0 hb1 hγ0 hγ hs k₀ k
  have hdecG' : (3 : ℝ) ^ (-(k : ℝ)) * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k)
      ≤ (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1)) * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
    le_trans hdecG (mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg h3nn _))
  have hgood : Mass k * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k)
      ≤ Cmass * (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
          ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    calc Mass k * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k)
        ≤ (Cmass * (3 : ℝ) ^ (-(k : ℝ))) * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k) :=
          mul_le_mul_of_nonneg_right (hMass k) (Real.rpow_nonneg h3nn _)
      _ = Cmass * ((3 : ℝ) ^ (-(k : ℝ)) * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k)) := by
          ring
      _ ≤ Cmass * ((3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k) := mul_le_mul_of_nonneg_left hdecG' hCmass
      _ = Cmass * (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by ring
  -- the collar leg: cap by the minimum, then Cauchy-Schwarz
  have humass : (0 : ℝ) ≤ Cmass * (3 : ℝ) ^ (-(k : ℝ)) :=
    mul_nonneg hCmass (Real.rpow_nonneg h3nn _)
  have hvnn : (0 : ℝ) ≤ ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ k / 2)) :=
    add_nonneg hε0 (Real.rpow_nonneg h3nn _)
  have hmin : Bad k ≤
      Real.sqrt ((Cmass * (3 : ℝ) ^ (-(k : ℝ))) *
        (ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ k / 2)))) :=
    le_trans (le_min (hBadMass k) (hBadDens k)) (min_le_sqrt_mul humass hvnn)
  have hsqrtsplit : Real.sqrt ((Cmass * (3 : ℝ) ^ (-(k : ℝ))) *
        (ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ k / 2))))
      = Real.sqrt Cmass * (3 : ℝ) ^ (-(k : ℝ) / 2) *
          Real.sqrt (ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ k / 2))) := by
    rw [Real.sqrt_mul humass, Real.sqrt_mul hCmass, sqrt_three_rpow]
  have hvle : ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ k / 2))
      ≤ ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)) := by
    have hexp : -(layerQuantity b hs k₀ k / 2) ≤ -((k₀ : ℝ) / 2) := by
      have := k0_le_layerQuantity b hs k₀ k
      linarith
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    linarith
  have hBadle : Bad k ≤ Real.sqrt Cmass * (3 : ℝ) ^ (-(k : ℝ) / 2) *
      Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) := by
    refine le_trans hmin ?_
    rw [hsqrtsplit]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvle)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg h3nn _))
  have hcolldec := three_rpow_layerQuantity_collar_decay hb0 hb9 hs k₀ k
  have hcol : (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) * Bad k
      ≤ Real.sqrt Cmass *
          ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))
          * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by
    have hstep : (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) * Bad k
        ≤ (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) *
            (Real.sqrt Cmass * (3 : ℝ) ^ (-(k : ℝ) / 2) *
              Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))) :=
      mul_le_mul_of_nonneg_left hBadle (Real.rpow_nonneg h3nn _)
    have hgrow : Real.sqrt Cmass *
          ((3 : ℝ) ^ (-(k : ℝ) / 2) * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k)) *
          Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))
        ≤ Real.sqrt Cmass *
          ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k) *
          Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcolldec (Real.sqrt_nonneg Cmass))
        (Real.sqrt_nonneg _)
    calc (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) * Bad k
        ≤ (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) *
            (Real.sqrt Cmass * (3 : ℝ) ^ (-(k : ℝ) / 2) *
              Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))) := hstep
      _ = Real.sqrt Cmass *
            ((3 : ℝ) ^ (-(k : ℝ) / 2) * (3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k)) *
            Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) := by ring
      _ ≤ Real.sqrt Cmass *
            ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
              ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k) *
            Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) := hgrow
      _ = Real.sqrt Cmass *
            ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
              Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))
            * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by ring
  calc layerContrib b γ hs k₀ Ktot Ccol Mass Bad k
      = Ktot * (Mass k * (3 : ℝ) ^ (γ * layerQuantity b hs k₀ k))
          + Ccol * ((3 : ℝ) ^ (2 * b * layerQuantity b hs k₀ k) * Bad k) := rfl
    _ ≤ Ktot * (Cmass * (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k)
          + Ccol * (Real.sqrt Cmass *
              ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
                Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))
              * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left hgood hK)
          (mul_le_mul_of_nonneg_left hcol hC)
    _ = (Ktot * Cmass * (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1))
          + Ccol * (Real.sqrt Cmass *
              ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
                Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))))
        * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := by ring

/-- **The layer series converges** at the ratio `3^{-1/4}`. -/
theorem summable_layerContrib {b γ ε Cmass Ktot Ccol : ℝ} {hs k₀ : ℕ} {Mass Bad : ℕ → ℝ}
    (hb0 : 0 < b) (hb9 : 9 * b ≤ 1) (hγ0 : 0 ≤ γ) (hγ : 4 * γ ≤ 1 - b)
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hCmass : 0 ≤ Cmass) (hε0 : 0 ≤ ε)
    (hMass0 : ∀ j : ℕ, 0 ≤ Mass j) (hBad0 : ∀ j : ℕ, 0 ≤ Bad j)
    (hMass : ∀ j : ℕ, Mass j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadMass : ∀ j : ℕ, Bad j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadDens : ∀ j : ℕ, Bad j ≤ ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ j / 2))) :
    Summable fun k : ℕ => layerContrib b γ hs k₀ Ktot Ccol Mass Bad k :=
  Summable.of_nonneg_of_le (fun k => layerContrib_nonneg hK hC hMass0 hBad0 k)
    (fun k => layerContrib_le hb0 hb9 hγ0 hγ hK hC hCmass hε0 hMass hBadMass hBadDens k)
    (summable_geometric_three_rpow_neg_quarter.mul_left _)

/-! ## The Step-3 payload -/

/-- Crucially it carries **no** `3^{2 b k_0}` — the load-bearing property of this constant. -/
def layerSumConst (b γ : ℝ) (k₀ : ℕ) (Ktot Ccol Cmass : ℝ) : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ *
    (Ktot * Cmass * (3 : ℝ) ^ (γ * ((k₀ : ℝ) + 1)) +
      2 * (Ccol * Real.sqrt Cmass) * (3 : ℝ) ^ (2 * b))

/-- The algebraic repackaging of the summed layer contributions into the Step-3
payload shape `C 3^{gamma hsep} (1 + 3^{2 b hsep} eps)`: the good leg pairs with the
`1`, the collar leg with the `3^{2 b hsep} eps`, using `3^{gamma hsep} >= 1` to
absorb the missing outer factor. -/
private theorem layerSum_repack {Ktot Ccol A B G Q ee I : ℝ}
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hA : 1 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hQ : 0 ≤ Q) (hee : 0 ≤ ee) (hI : 0 ≤ I) :
    (Ktot * (A * G) + Ccol * ((B * Q) * (2 * ee))) * I
      ≤ (I * (Ktot * G + 2 * Ccol * Q)) * (A * (1 + B * ee)) := by
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA
  have h2C : (0 : ℝ) ≤ 2 * Ccol := by linarith
  have h1 : 0 ≤ Ktot * G * (A * (B * ee)) :=
    mul_nonneg (mul_nonneg hK hG) (mul_nonneg hA0 (mul_nonneg hB hee))
  have h2 : 0 ≤ 2 * Ccol * Q * A := mul_nonneg (mul_nonneg h2C hQ) hA0
  have h3 : 0 ≤ 2 * Ccol * Q * (B * ee) * (A - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg h2C hQ) (mul_nonneg hB hee)) (by linarith)
  have hid : (Ktot * G + 2 * Ccol * Q) * (A * (1 + B * ee))
      - (Ktot * (A * G) + Ccol * ((B * Q) * (2 * ee)))
      = Ktot * G * (A * (B * ee)) + 2 * Ccol * Q * A
        + 2 * Ccol * Q * (B * ee) * (A - 1) := by ring
  have hmain : Ktot * (A * G) + Ccol * ((B * Q) * (2 * ee))
      ≤ (Ktot * G + 2 * Ccol * Q) * (A * (1 + B * ee)) := by
    linarith [h1, h2, h3, hid.le, hid.ge]
  calc (Ktot * (A * G) + Ccol * ((B * Q) * (2 * ee))) * I
      ≤ ((Ktot * G + 2 * Ccol * Q) * (A * (1 + B * ee))) * I :=
        mul_le_mul_of_nonneg_right hmain hI
    _ = (I * (Ktot * G + 2 * Ccol * Q)) * (A * (1 + B * ee)) := by ring

/-- ```
  sum_k (layer k)  <=  C ( 3^{gamma hsep} ( 1 + 3^{2 b hsep} exp(-k_0/36) ) ) ,
```

with `C = layerSumConst` free of `k_0` in its `3^{2b(.)}` factor.  Against the
printed display the only differences are the two recorded: the collapse
exponent `1/36` in place of `1/4` (absorbed by relabelling `c` in the
manuscript's own `k_0 := c E^{-2} gamma^{-1}`) and the absolute constant
inflation `geomSeriesInflation` from the ratio change `3^{-3/4} |-> 3^{-1/4}`.

The hypothesis `hεk0 : eps <= exp(-k_0)` *is* the manuscript's selection
`k_0 := c E^{-2} gamma^{-1}` read against the density constant. -/
theorem tsum_layerContrib_le_payload {b γ ε Cmass Ktot Ccol : ℝ} {hs k₀ : ℕ}
    {Mass Bad : ℕ → ℝ}
    (hb0 : 0 < b) (hb9 : 9 * b ≤ 1) (hγ0 : 0 ≤ γ) (hγ : 4 * γ ≤ 1 - b)
    (hK : 0 ≤ Ktot) (hC : 0 ≤ Ccol) (hCmass : 0 ≤ Cmass) (hε0 : 0 ≤ ε)
    (hεk0 : ε ≤ Real.exp (-(k₀ : ℝ)))
    (hMass0 : ∀ j : ℕ, 0 ≤ Mass j) (hBad0 : ∀ j : ℕ, 0 ≤ Bad j)
    (hMass : ∀ j : ℕ, Mass j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadMass : ∀ j : ℕ, Bad j ≤ Cmass * (3 : ℝ) ^ (-(j : ℝ)))
    (hBadDens : ∀ j : ℕ, Bad j ≤ ε + (3 : ℝ) ^ (-(layerQuantity b hs k₀ j / 2))) :
    ∑' k : ℕ, layerContrib b γ hs k₀ Ktot Ccol Mass Bad k
      ≤ layerSumConst b γ k₀ Ktot Ccol Cmass *
          ((3 : ℝ) ^ (γ * (hs : ℝ)) *
            (1 + (3 : ℝ) ^ (2 * b * (hs : ℝ)) * Real.exp (-((k₀ : ℝ) / 36)))) := by
  have h3nn : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
  have hr0 := three_rpow_neg_quarter_nonneg
  have hr1 := three_rpow_neg_quarter_lt_one
  have hIpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by linarith
  have hInn : (0 : ℝ) ≤ (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := le_of_lt (inv_pos.2 hIpos)
  set Cc : ℝ := Ktot * Cmass * (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1))
      + Ccol * (Real.sqrt Cmass *
          ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))))) with hCcdef
  have hterm : ∀ k : ℕ, layerContrib b γ hs k₀ Ktot Ccol Mass Bad k
      ≤ Cc * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k := fun k => by
    rw [hCcdef]
    exact layerContrib_le hb0 hb9 hγ0 hγ hK hC hCmass hε0 hMass hBadMass hBadDens k
  have hgeomsum : Summable fun k : ℕ => Cc * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
    summable_geometric_three_rpow_neg_quarter.mul_left _
  have hsum : Summable fun k : ℕ => layerContrib b γ hs k₀ Ktot Ccol Mass Bad k :=
    summable_layerContrib hb0 hb9 hγ0 hγ hK hC hCmass hε0 hMass0 hBad0 hMass hBadMass
      hBadDens
  -- the collapse of the `k_0`-dependent collar factor
  have hsqle : Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))
      ≤ Real.sqrt (Real.exp (-(k₀ : ℝ)) + (3 : ℝ) ^ (-((k₀ : ℝ) / 2))) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcollapse := k0_sqrt_collapse (b := b) (t := (k₀ : ℝ)) hb0.le hb9
    (Nat.cast_nonneg k₀)
  have hbadsplit : (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1))
      = ((3 : ℝ) ^ (2 * b * (hs : ℝ)) * (3 : ℝ) ^ (2 * b)) *
          (3 : ℝ) ^ (2 * b * (k₀ : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hgoodsplit : (3 : ℝ) ^ (γ * ((hs : ℝ) + (k₀ : ℝ) + 1))
      = (3 : ℝ) ^ (γ * (hs : ℝ)) * (3 : ℝ) ^ (γ * ((k₀ : ℝ) + 1)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hcol : (3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
        Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))
      ≤ ((3 : ℝ) ^ (2 * b * (hs : ℝ)) * (3 : ℝ) ^ (2 * b)) *
          (2 * Real.exp (-((k₀ : ℝ) / 36))) := by
    rw [hbadsplit, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (Real.rpow_nonneg h3nn _) (Real.rpow_nonneg h3nn _))
    exact le_trans (mul_le_mul_of_nonneg_left hsqle (Real.rpow_nonneg h3nn _)) hcollapse
  have hCcle : Cc
      ≤ (Ktot * Cmass) * ((3 : ℝ) ^ (γ * (hs : ℝ)) * (3 : ℝ) ^ (γ * ((k₀ : ℝ) + 1)))
        + (Ccol * Real.sqrt Cmass) *
            (((3 : ℝ) ^ (2 * b * (hs : ℝ)) * (3 : ℝ) ^ (2 * b)) *
              (2 * Real.exp (-((k₀ : ℝ) / 36)))) := by
    rw [hCcdef, hgoodsplit]
    refine add_le_add le_rfl ?_
    have := mul_le_mul_of_nonneg_left hcol
      (mul_nonneg hC (Real.sqrt_nonneg Cmass))
    calc Ccol * (Real.sqrt Cmass *
          ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
            Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))))
        = (Ccol * Real.sqrt Cmass) *
            ((3 : ℝ) ^ (2 * b * ((hs : ℝ) + (k₀ : ℝ) + 1)) *
              Real.sqrt (ε + (3 : ℝ) ^ (-((k₀ : ℝ) / 2)))) := by ring
      _ ≤ (Ccol * Real.sqrt Cmass) *
            (((3 : ℝ) ^ (2 * b * (hs : ℝ)) * (3 : ℝ) ^ (2 * b)) *
              (2 * Real.exp (-((k₀ : ℝ) / 36)))) := this
  have hA1 : (1 : ℝ) ≤ (3 : ℝ) ^ (γ * (hs : ℝ)) :=
    Percolation.one_le_three_rpow (mul_nonneg hγ0 (Nat.cast_nonneg hs))
  calc ∑' k : ℕ, layerContrib b γ hs k₀ Ktot Ccol Mass Bad k
      ≤ ∑' k : ℕ, Cc * ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ k :=
        Summable.tsum_le_tsum hterm hsum hgeomsum
    _ = Cc * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_three_rpow_neg_quarter]
    _ ≤ ((Ktot * Cmass) *
            ((3 : ℝ) ^ (γ * (hs : ℝ)) * (3 : ℝ) ^ (γ * ((k₀ : ℝ) + 1)))
          + (Ccol * Real.sqrt Cmass) *
              (((3 : ℝ) ^ (2 * b * (hs : ℝ)) * (3 : ℝ) ^ (2 * b)) *
                (2 * Real.exp (-((k₀ : ℝ) / 36)))))
        * (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := mul_le_mul_of_nonneg_right hCcle hInn
    _ ≤ layerSumConst b γ k₀ Ktot Ccol Cmass *
          ((3 : ℝ) ^ (γ * (hs : ℝ)) *
            (1 + (3 : ℝ) ^ (2 * b * (hs : ℝ)) * Real.exp (-((k₀ : ℝ) / 36)))) := by
        rw [layerSumConst]
        exact layerSum_repack (mul_nonneg hK hCmass)
          (mul_nonneg hC (Real.sqrt_nonneg Cmass)) hA1
          (Real.rpow_nonneg h3nn _) (Real.rpow_nonneg h3nn _)
          (Real.rpow_nonneg h3nn _) (Real.exp_pos _).le hInn

/-! ## Instantiation at the proved Whitney carriers -/


theorem cubeMassRatio_nonneg (Q R : TriadicCube d) : 0 ≤ cubeMassRatio Q R := by
  rw [cubeMassRatio]
  positivity


/-- **`l.bad.cubes.density` at the layer quantity.**  The proved mass form
`Provider.Whitney.sum_cubeMassRatio_badFamilyLayer_le`, with its threshold
rewritten at `k + h_k = layerQuantity` and in the exponent convention that
`layerContrib_le` consumes. -/
theorem sum_cubeMassRatio_badFamilyLayer_le_layerQuantity {M : ABKModel d} {m : ℤ}
    {E b : ℝ} {k₀ : ℕ} {omega : CutoffSample d}
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (k : ℕ) :
    ∑ Q ∈ badFamilyLayer M m (whitneyScale M m E b k₀ omega) k omega,
        cubeMassRatio (originCube d m) Q
      ≤ Real.exp (-(Percolation.siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)))
          + (3 : ℝ) ^
              (-(layerQuantity b (Percolation.hsep M m E b omega) k₀ k / 2)) := by
  have hbase := sum_cubeMassRatio_badFamilyLayer_le (k₀ := k₀) hne k
  refine le_trans hbase (le_of_eq ?_)
  have hcast : ((k + whitneyScale M m E b k₀ omega k : ℕ) : ℝ)
      = layerQuantity b (Percolation.hsep M m E b omega) k₀ k := by
    simp only [layerQuantity, whitneyScale]
    push_cast
    ring
  simp only [Percolation.scaleSeparationDensityThreshold, hcast]
  rw [neg_div]


/-! ## The bridge to the proved `e.hsep.tails` -/

/-- This is the `gamma <= b` step. -/
theorem three_rpow_gamma_hsep_le_three_rpow_b_hsep {M : ABKModel d} {m : ℤ}
    {E b γ : ℝ} (hγb : γ ≤ b) (omega : CutoffSample d) :
    (3 : ℝ) ^ (γ * (Percolation.hsep M m E b omega : ℝ))
      ≤ (3 : ℝ) ^ (b * (Percolation.hsep M m E b omega : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hnn : (0 : ℝ) ≤ (Percolation.hsep M m E b omega : ℝ) := Nat.cast_nonneg _
  nlinarith [hγb, hnn]

end

end Algsuperdiff.Section3.Provider.Multiscale
