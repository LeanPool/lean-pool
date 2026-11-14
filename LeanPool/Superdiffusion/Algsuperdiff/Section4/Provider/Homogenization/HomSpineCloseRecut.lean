/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepThreeCoarse
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePSource

/-!
# HomSpineCloseRecut

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the Step-2b/3b re-cuts (`hlevel`, `hS`)

## What this module is

The re-cut of the printed energy slot, needed because what Step 2b delivers is
weighted rather than uniform in the depth index.

### (a) The energy slot at the `s₁ = s/4` pin — A MEASURED PRINT DEFECT

The printed `ℓ^p` energy slot is fed from a UNIFORM bound `Gen R ≤ S`.  What Step 2b actually
delivers is a
WEIGHTED bound: at the §4.5 parameter web the family bound `F j z ≤
K·3^{(1-α)(m-j)}` (the Step-2b local family) grows
like `3^{a i}` in the depth index `i = (m-n)+i` with

```text
  a = 1 - α = s/2.
```

The printed weight of the energy slot is `3^{-(s-s₁)p i}`.  So the summand is
`3^{-((s-s₁)-a)p i}` and the slot converges **iff `s₁ < s - a = s/2`**.  The
manuscript's `s₁ = s/2` is EXACTLY the borderline: `(s - s₁) - a = 0`, every
summand is the same, the partial sums grow linearly in `N`, and NO `S`-bound
survives.  The `s₁ = s/2` gap is `0`, while the `s₁ = s/4` gap is `s/4 > 0`.

The choice below is free at the hypothesis level and stays inside the printed
range `s₁ ∈ (0,s)` of the source proposition itself — it is a choice the printed
statement already offers, i.e. pre-authorized `s`-power territory, not a
statement change:

```text
  s₁:= s/4    ⟹    (s - s₁) - a = 3s/4 - s/2 = s/4 > 0.
```

`coarseGrainingEnergyPartial_le_of_weightedBound` is the weighted-hypothesis
variant; `coarseGrainingEnergyPartial_le_at_quarterPin` is its instance at the
pin.  The price is the explicit geometric factor
`(1 - 3^{-((w-a)p)})^{-1/p}` in place of `(1 - 3^{-(wp)})^{-1/p}`, i.e. a
displayed constant and nothing else.

### (b) THE `ν` VERSUS `σ` SEAM — NOTED, NOT CONVERTED

The printed energy slot sums `‖σ^{1/2}∇u‖_{L²(z+□_k)}^p` (transcribed in
`HomFinitePSource`), while Step 2b's family is the
manuscript's `ν^{1/2}‖∇u‖_{L²(z+□_j)}`.  The printed `σ` of the energy slot
is UNSUBSCRIPTED and therefore ambiguous between

* the coefficient field's own symmetric part — here `symmPart a_L = ν Id`, in
  which case `‖σ^{1/2}∇u‖ = ν^{1/2}‖∇u‖` and the Step-2b family feeds the slot
  with NO conversion; and
* the constant comparator `σ₀ = σ_m`, in which case feeding the Step-2b family
  into the slot would require a `ν ↔ σ` conversion.

This module refuses the second reading and performs NO conversion: the per-cube
energy `Gen` is left ABSTRACT in every statement below (as it is in the
transcribed printed proposition), so the caller pins it, and the units doctrine
is not touched anywhere in this file.  The seam is reported, not crossed.
-/

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 3. The energy slot from a WEIGHTED Step-2b family bound -/

/-- **The finite-`p` energy slot from the WEIGHTED Step-2b datum.**

The unweighted form of the slot bound asks for a UNIFORM per-cube bound
`Gen R ≤ S`.  What Step 2b delivers is `Gen R ≤ S·3^{a i}` at depth `jn + i`.
As long as the printed weight strictly dominates that growth (`a < w`, i.e. `s₁
< s - (1-α)`), the slot is still bounded by `S` times an explicit geometric
factor, now at the GAP exponent `w - a`.

`Gen` is abstract here: no coefficient field, no `ν`, no `σ` (see the module
docstring's seam disclosure). -/
theorem coarseGrainingEnergyPartial_le_of_weightedBound {Q : TriadicCube d}
    {p w a S : ℝ} {jn N : ℕ} {Gen : TriadicCube d → ℝ}
    (hp : 0 < p) (haw : a < w) (hS : 0 ≤ S)
    (hG : ∀ i : ℕ, ∀ R ∈ descendantsAtDepth Q (jn + i),
      Gen R ≤ S * (3 : ℝ) ^ (a * (i : ℝ)))
    (hG0 : ∀ R : TriadicCube d, 0 ≤ Gen R) :
    coarseGrainingEnergyPartial Q p w jn N Gen ≤ S * coarseGrainingGeomFactor p (w - a) := by
  classical
  have hgap : 0 < w - a := by linarith only [haw]
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-((w - a) * p)) := three_rpow_pos _
  have hr1 : (3 : ℝ) ^ (-((w - a) * p)) < 1 :=
    three_rpow_neg_lt_one (mul_pos hgap hp)
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-((w - a) * p)) := by linarith only [hr1]
  have hSp : (0 : ℝ) ≤ S ^ p := Real.rpow_nonneg hS p
  /- each depth average is at most `S^p · 3^{a i p}` -/
  have hdepth : ∀ i : ℕ,
      (descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
        S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p) := by
    intro i
    have hcell : ∀ R ∈ descendantsAtDepth Q (jn + i),
        Gen R ^ p ≤ S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p) := by
      intro R hR
      have h1 : Gen R ^ p ≤ (S * (3 : ℝ) ^ (a * (i : ℝ))) ^ p :=
        Real.rpow_le_rpow (hG0 R) (hG i R hR) hp.le
      refine h1.trans (le_of_eq ?_)
      rw [Real.mul_rpow hS (three_rpow_nonneg _),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    have hmono := descendantsAverage_le_descendantsAverage Q (jn + i)
      (F := fun R => Gen R ^ p) (G := fun _ => S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p)) hcell
    rwa [descendantsAverage_const_eq Q (jn + i) (S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p))] at hmono
  have hdepth0 : ∀ i : ℕ, (0 : ℝ) ≤ descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
    fun i => descendantsAverage_nonneg Q (jn + i) _
      fun R _ => Real.rpow_nonneg (hG0 R) p
  /- the weighted summand is a geometric term at the GAP expone -/
  have hkey : ∀ i : ℕ,
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          (descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
        ((3 : ℝ) ^ (-((w - a) * p))) ^ i * S ^ p := by
    intro i
    have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(w * p) * (i : ℝ)) := three_rpow_nonneg _
    have hmerge : (3 : ℝ) ^ (-(w * p) * (i : ℝ)) * (3 : ℝ) ^ (a * (i : ℝ) * p) =
        ((3 : ℝ) ^ (-((w - a) * p))) ^ i := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_natCast ((3 : ℝ) ^ (-((w - a) * p))) i,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring
    calc (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
          (descendantsAverage Q (jn + i) fun R => Gen R ^ p)
        ≤ (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
            (S ^ p * (3 : ℝ) ^ (a * (i : ℝ) * p)) :=
          mul_le_mul_of_nonneg_left (hdepth i) hw0
      _ = ((3 : ℝ) ^ (-(w * p) * (i : ℝ)) * (3 : ℝ) ^ (a * (i : ℝ) * p)) * S ^ p := by ring
      _ = ((3 : ℝ) ^ (-((w - a) * p))) ^ i * S ^ p := by rw [hmerge]
  have hsum : (∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p) ≤
      S ^ p * (1 - (3 : ℝ) ^ (-((w - a) * p)))⁻¹ := by
    calc (∑ i ∈ Finset.range (N + 1),
          (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
            descendantsAverage Q (jn + i) fun R => Gen R ^ p)
        ≤ ∑ i ∈ Finset.range (N + 1),
            ((3 : ℝ) ^ (-((w - a) * p))) ^ i * S ^ p :=
          Finset.sum_le_sum fun i _ => hkey i
      _ ≤ S ^ p * (1 - (3 : ℝ) ^ (-((w - a) * p)))⁻¹ :=
          sum_geom_weighted_le hr0.le hr1 hSp (fun _ => le_rfl) N
  have hnnsum : (0 : ℝ) ≤ ∑ i ∈ Finset.range (N + 1),
      (3 : ℝ) ^ (-(w * p) * (i : ℝ)) *
        descendantsAverage Q (jn + i) fun R => Gen R ^ p :=
    Finset.sum_nonneg fun i _ => mul_nonneg (three_rpow_nonneg _) (hdepth0 i)
  have hfin : coarseGrainingEnergyPartial Q p w jn N Gen ≤
      (S ^ p * (1 - (3 : ℝ) ^ (-((w - a) * p)))⁻¹) ^ (1 / p) := by
    rw [coarseGrainingEnergyPartial_def]
    exact Real.rpow_le_rpow hnnsum hsum (one_div_nonneg.mpr hp.le)
  refine hfin.trans (le_of_eq ?_)
  rw [Real.mul_rpow hSp (inv_nonneg.mpr hden.le), ← Real.rpow_mul hS,
    mul_one_div_cancel (ne_of_gt hp), Real.rpow_one, coarseGrainingGeomFactor_def]

/-- **The energy slot at the `s₁ = s/4` pin.**

The Step-2b family grows like `3^{(s/2) i}` (the §4.5 web's `1 - α = s/2`), the
printed weight at `s₁ = s/4` is `3^{-(3s/4)p i}`, and the gap is `s/4 > 0`.
This is the instance of `coarseGrainingEnergyPartial_le_of_weightedBound` the
Step-3/Step-4 chain consumes; the printed `s₁ = s/2` would give gap `0` and no
bound. -/
theorem coarseGrainingEnergyPartial_le_at_quarterPin {Q : TriadicCube d}
    {p s S : ℝ} {jn N : ℕ} {Gen : TriadicCube d → ℝ}
    (hp : 0 < p) (hs : 0 < s) (hS : 0 ≤ S)
    (hG : ∀ i : ℕ, ∀ R ∈ descendantsAtDepth Q (jn + i),
      Gen R ≤ S * (3 : ℝ) ^ (s / 2 * (i : ℝ)))
    (hG0 : ∀ R : TriadicCube d, 0 ≤ Gen R) :
    coarseGrainingEnergyPartial Q p (s - s / 4) jn N Gen ≤
      S * coarseGrainingGeomFactor p (s / 4) := by
  have hgap : (s - s / 4) - s / 2 = s / 4 := by ring
  have haw : s / 2 < s - s / 4 := by linarith only [hs]
  have hmain := coarseGrainingEnergyPartial_le_of_weightedBound (Q := Q) (p := p)
    (w := s - s / 4) (a := s / 2) (S := S) (jn := jn) (N := N) (Gen := Gen) hp haw hS hG hG0
  rwa [hgap] at hmain

end

end Algsuperdiff.Section4.Provider.Homogenization
