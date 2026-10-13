/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomCGFinalLegs
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePSource

/-!
# HomCGCarrierEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `S`-slot carrier comparison: the printed energy slot at BOTH spellings

## What this file supplies

The obstruction was a single slot.  The printed right-hand side of the general
coarse-graining proposition carries the mesoscale energy

```text
  ( Σ_{k ≤ n} 3^{-(s-s₁)p(n-k)} avsum_{z ∈ 3^k ℤ^d ∩ □_m}
        ‖σ^{1/2}∇u‖_{L²(z+□_k)}^p )^{1/p},
```

and the two transcriptions of that ONE object are

* `CoarseGraining`'s `weightedLocalSymmetricEnergyLp Q n hn a u s₁ s p` — an `ℝ≥0∞`-valued
  `tsum` over ALL depths, with the per-cell energy given by
  `localSymmetricEnergyENorm` (the normalized `⟪∇u, 𝐚_sym ∇u⟫` integral);
* this repository's `coarseGrainingEnergyPartial Q p (s-s₁) jn N Gen` — a REAL-valued
  partial sum over the first `N+1` depths, with the per-cell energy carried
  abstractly as `Gen`.

`weightedLocalSymmetricEnergyLp_le_ofReal` is the comparison in the direction
the Step-4 consumption needs:

```text
  (∀ N, coarseGrainingEnergyPartial Q p wgap jn N Gen ≤ S)  ⟹
      weightedLocalSymmetricEnergyLp Q n hn a u s₁ s p ≤ ENNReal.ofReal S,
```

whenever `Gen` dominates the printed per-cell energy `printedLocalEnergy`,
`(jn: ℤ) = Q.scale - n`, and `wgap ≤ s - s₁`.  The domination hypothesis is
free: `printedLocalEnergy` is a DEFINITION (the `CoarseGraining` per-cell
energy extended by `0` off the subcubes of `Q`), and
`localSymmetricEnergyENorm_le_ofReal_printedLocalEnergy` proves the domination
at `Gen = printedLocalEnergy` outright, because the `CoarseGraining` energy is
finite (`localSymmetricEnergyENorm_ne_top`).

## THE ORDER CONSTRAINT (load-bearing, recorded here)

The two spellings carry comparable geometric weights only when their order gaps
do.  `CoarseGraining`'s series is weighted by `3^{-(s-s₁)pj}` at ITS pair `(s₁,
s)`; this repository's by `3^{-wgap·p·i}`.  So the comparison needs `wgap ≤ s -
s₁` — the hypothesis `hw` below.  Read at the spine's bundle, where this
repository's gap is the `s₁ = s/4` pin (`wgap = 3s/4`) and the display is
entered at a LOWER order `s′` with its own `s₁′`, this says

```text
  s′ - s₁′  ≥  s - s/4 = 3s/4,
```

which forces `s - s′ < s/4`.  The convenient choice `s′ = s/2` is therefore NOT
admissible for this route; `s′ = 7s/8`, `s₁′ = s/8` is, and the smaller order
loss `s - s′ = s/8` only improves the duality window `0 < (s-s′)p′ < d`.
-/

open HCPolySupport HCPolySupport.Book.Ch03 HCPolySupport.Book.Ch03.ABK26 MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The printed per-cell energy, as a total function on cubes -/

open Classical in
/-- **The printed per-cell energy `‖σ^{1/2}∇u‖_{L²(R)}`**, as a total function
of the cell `R`.

On a subcube of `Q` it is `CoarseGraining`'s `localSymmetricEnergyENorm` of the
restricted data; elsewhere it is `0`.  The `dite` is what turns the
`CoarseGraining` summand — which is indexed by a MEMBERSHIP proof — into a
function of the bare cube, so that it can sit in this repository's `Gen` slot. -/
def printedLocalEnergy {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q))
    (R : TriadicCube d) : ℝ :=
  if h : openCubeSet R ⊆ openCubeSet Q then
    (localSymmetricEnergyENorm R (a.restrictToSubcube h) (restrictH1ToSubcube u h)).toReal
  else 0

theorem printedLocalEnergy_nonneg {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q))
    (R : TriadicCube d) : 0 ≤ printedLocalEnergy a u R := by
  unfold printedLocalEnergy
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- **The domination is free.**  The `CoarseGraining` per-cell energy is finite, so it is
recovered exactly by `ENNReal.ofReal` of its own real value. -/
theorem localSymmetricEnergyENorm_le_ofReal_printedLocalEnergy {Q R : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q))
    (h : openCubeSet R ⊆ openCubeSet Q) :
    localSymmetricEnergyENorm R (a.restrictToSubcube h) (restrictH1ToSubcube u h) ≤
      ENNReal.ofReal (printedLocalEnergy a u R) := by
  unfold printedLocalEnergy
  rw [dite_eq_left h, ENNReal.ofReal_toReal (localSymmetricEnergyENorm_ne_top _ _ _)]

/-! ## 2. Two pieces of bookkeeping -/

/-- The attached sum of a dominated family, transferred to the bare grid. -/
private theorem attachSum_le {Q : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q))
    {Gen : TriadicCube d → ℝ} (hGen0 : ∀ R, 0 ≤ Gen R)
    (hGen : ∀ R, printedLocalEnergy a u R ≤ Gen R) {t : ℝ} (ht : 0 ≤ t)
    (D : Finset (TriadicCube d)) (E : {x // x ∈ D} → ℝ≥0∞)
    (hE : ∀ R : {x // x ∈ D}, E R ≤ ENNReal.ofReal (printedLocalEnergy a u R.1)) :
    ∑ R ∈ D.attach, E R ^ t ≤ ENNReal.ofReal (∑ R ∈ D, Gen R ^ t) := by
  classical
  calc ∑ R ∈ D.attach, E R ^ t
      ≤ ∑ R ∈ D.attach, ENNReal.ofReal (Gen R.1 ^ t) := by
        refine Finset.sum_le_sum fun R _ => ?_
        calc E R ^ t
            ≤ (ENNReal.ofReal (Gen R.1)) ^ t :=
              ENNReal.rpow_le_rpow
                ((hE R).trans (ENNReal.ofReal_le_ofReal (hGen R.1))) ht
          _ = ENNReal.ofReal (Gen R.1 ^ t) := ENNReal.ofReal_rpow_of_nonneg (hGen0 _) ht
    _ = ∑ R ∈ D, ENNReal.ofReal (Gen R ^ t) :=
        Finset.sum_attach D fun R => ENNReal.ofReal (Gen R ^ t)
    _ = ENNReal.ofReal (∑ R ∈ D, Gen R ^ t) :=
        (ENNReal.ofReal_sum_of_nonneg fun R _ => Real.rpow_nonneg (hGen0 R) t).symm

/-- The reciprocal cardinality of a depth grid, as an `ENNReal.ofReal`. -/
private theorem descendants_card_inv_eq {Q : TriadicCube d} (k : ℕ) :
    (((descendantsAtDepth Q k).card : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal (((descendantsAtDepth Q k).card : ℝ))⁻¹ := by
  have hcard : (descendantsAtDepth Q k).card = (3 ^ d) ^ k := descendantsAtDepth_card Q k
  have hnat : 0 < (descendantsAtDepth Q k).card := by
    rw [hcard]
    exact Nat.pow_pos (Nat.pow_pos (by norm_num))
  have hpos : (0 : ℝ) < ((descendantsAtDepth Q k).card : ℝ) := by exact_mod_cast hnat
  rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]

/-- The two spellings of the geometric weight agree. -/
private theorem three_rpow_neg_mul (w t : ℝ) (j : ℕ) :
    Real.rpow 3 (-(w * t * (j : ℝ))) = (3 : ℝ) ^ (-(w * t) * (j : ℝ)) :=
  congrArg (fun y : ℝ => (3 : ℝ) ^ y) (by ring)

/-! ## 3. THE CARRIER COMPARISON -/

/-- **The `S`-slot comparison, in the direction the Step-4 consumption needs.**

If this repository's abstract per-cell datum `Gen` dominates the printed
per-cell energy, and every partial `ℓ^p` sum of this repository's slot is below
`S`, then `CoarseGraining`'s `tsum` spelling of the SAME printed slot is below
`ENNReal.ofReal S`.

The hypothesis `hw` is the order constraint recorded in the module docstring:
the `CoarseGraining` pair `(s₁, s)` must have order gap at least this
repository pair's `wgap`. -/
theorem weightedLocalSymmetricEnergyLp_le_ofReal [NeZero d]
    {Q : TriadicCube d} {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (u : H1Function (openCubeSet Q))
    (s1 s : FractionalOrder) (p : FiniteLpExponent) {wgap : ℝ}
    (hw : wgap ≤ s.1 - s1.1)
    {jn : ℕ} (hjn : (jn : ℤ) = Q.scale - n) {Gen : TriadicCube d → ℝ} {S : ℝ}
    (hGen0 : ∀ R, 0 ≤ Gen R) (hGen : ∀ R, printedLocalEnergy a u R ≤ Gen R) (hS0 : 0 ≤ S)
    (hS : ∀ N : ℕ, coarseGrainingEnergyPartial Q p.exponent.toReal wgap jn N Gen ≤ S) :
    weightedLocalSymmetricEnergyLp Q n hn a u s1 s p ≤ ENNReal.ofReal S := by
  classical
  have hr : 0 < p.exponent.toReal := finiteLpExponent_toReal_pos p
  /- the two grids coincide layer by lay -/
  have hidx : ∀ j : ℕ, descendantsAtScale Q (n - (j : ℤ)) = descendantsAtDepth Q (jn + j) := by
    intro j
    have hle : n - (j : ℤ) ≤ Q.scale := by omega
    have hcast : (Q.scale - (n - (j : ℤ))).toNat = jn + j := by omega
    rw [descendantsAtScale_eq_descendantsAtDepth Q hle, hcast]
  have havg0 : ∀ j : ℕ,
      (0 : ℝ) ≤ descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal :=
    fun j => descendantsAverage_nonneg Q (jn + j) _
      fun R _ => Real.rpow_nonneg (hGen0 R) _
  /- the real-side partial sums are below `S ^ p` -/
  have hpartial : ∀ N : ℕ,
      (∑ j ∈ Finset.range N,
        Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
          descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal) ≤
        S ^ p.exponent.toReal := by
    intro N
    have hconv : ∀ j : ℕ,
        Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
            (descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal) =
          (3 : ℝ) ^ (-(wgap * p.exponent.toReal) * (j : ℝ)) *
            descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal :=
      fun j => congrArg (fun y : ℝ =>
        y * descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal)
        (three_rpow_neg_mul wgap p.exponent.toReal j)
    have hterm0 : ∀ j : ℕ, (0 : ℝ) ≤
        Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
          descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal :=
      fun j => mul_nonneg (three_rpow_nonneg _) (havg0 j)
    have hsub : (∑ j ∈ Finset.range N,
        Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
          descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal) ≤
        ∑ j ∈ Finset.range (N + 1),
          Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
            descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_range.mpr
          (Nat.lt_succ_of_lt (Finset.mem_range.mp hx))) fun j _ _ => hterm0 j
    have hcongr : (∑ j ∈ Finset.range (N + 1),
        Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
          descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal) =
        ∑ j ∈ Finset.range (N + 1),
          (3 : ℝ) ^ (-(wgap * p.exponent.toReal) * (j : ℝ)) *
            descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal :=
      Finset.sum_congr rfl fun j _ => hconv j
    have hA0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range (N + 1),
        (3 : ℝ) ^ (-(wgap * p.exponent.toReal) * (j : ℝ)) *
          descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal :=
      Finset.sum_nonneg fun j _ => mul_nonneg (three_rpow_nonneg _) (havg0 j)
    have hroot := hS N
    rw [coarseGrainingEnergyPartial_def] at hroot
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) hroot hr.le
    rw [← Real.rpow_mul hA0, one_div, inv_mul_cancel₀ (ne_of_gt hr), Real.rpow_one] at hpow
    exact hsub.trans (hcongr.le.trans hpow)
  /- the `ℝ≥0∞` si -/
  have hkey : (weightedLocalSymmetricEnergyLp Q n hn a u s1 s p) ^ p.exponent.toReal ≤
      ENNReal.ofReal (S ^ p.exponent.toReal) := by
    rw [weightedLocalSymmetricEnergyLp_rpow_eq_tsum, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    refine (Finset.sum_le_sum (g := fun j : ℕ => ENNReal.ofReal
      (Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
        descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal))
      (fun j _ => ?_)).trans ?_
    · /- one lay -/
      show _ ≤ ENNReal.ofReal (Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
        descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal)
      have hlayer := attachSum_le a u hGen0 hGen hr.le
        (descendantsAtScale Q (n - (j : ℤ)))
        (fun R => localSymmetricEnergyENorm R.1
          (a.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
          (restrictH1ToSubcube u
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2)))
        (fun R => localSymmetricEnergyENorm_le_ofReal_printedLocalEnergy a u _)
      refine le_trans (mul_le_mul' le_rfl hlayer) ?_
      rw [hidx j]
      have hW0 : (0 : ℝ) ≤
          Real.rpow 3 (-((s.1 - s1.1) * p.exponent.toReal * (j : ℝ))) :=
        three_rpow_nonneg _
      have hCinv : (0 : ℝ) ≤ (((descendantsAtDepth Q (jn + j)).card : ℝ))⁻¹ :=
        inv_nonneg.mpr (Nat.cast_nonneg _)
      have hSum0 : (0 : ℝ) ≤
          ∑ R ∈ descendantsAtDepth Q (jn + j), Gen R ^ p.exponent.toReal :=
        Finset.sum_nonneg fun R _ => Real.rpow_nonneg (hGen0 R) _
      have hweight : Real.rpow 3 (-((s.1 - s1.1) * p.exponent.toReal * (j : ℝ))) ≤
          Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have hmul : wgap * p.exponent.toReal * (j : ℝ) ≤
            (s.1 - s1.1) * p.exponent.toReal * (j : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw hr.le) hj
        linarith only [hmul]
      calc ENNReal.ofReal (Real.rpow 3 (-((s.1 - s1.1) * p.exponent.toReal * (j : ℝ)))) *
              (((descendantsAtDepth Q (jn + j)).card : ℝ≥0∞))⁻¹ *
            ENNReal.ofReal (∑ R ∈ descendantsAtDepth Q (jn + j), Gen R ^ p.exponent.toReal)
          = ENNReal.ofReal (Real.rpow 3 (-((s.1 - s1.1) * p.exponent.toReal * (j : ℝ))) *
              ((((descendantsAtDepth Q (jn + j)).card : ℝ))⁻¹ *
                ∑ R ∈ descendantsAtDepth Q (jn + j), Gen R ^ p.exponent.toReal)) := by
            rw [descendants_card_inv_eq, ← ENNReal.ofReal_mul hW0,
              ← ENNReal.ofReal_mul (mul_nonneg hW0 hCinv), mul_assoc]
        _ ≤ ENNReal.ofReal (Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
              descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right hweight (mul_nonneg hCinv hSum0))
    · /- the layers summ -/
      rw [← ENNReal.ofReal_sum_of_nonneg
        (f := fun j : ℕ => Real.rpow 3 (-(wgap * p.exponent.toReal * (j : ℝ))) *
          descendantsAverage Q (jn + j) fun R => Gen R ^ p.exponent.toReal)
        (fun j _ => mul_nonneg (three_rpow_nonneg _) (havg0 j))]
      exact ENNReal.ofReal_le_ofReal (hpartial N)
  /- undo the `p`-th pow -/
  have hfin := ENNReal.rpow_le_rpow hkey (inv_nonneg.mpr hr.le)
  rw [ENNReal.rpow_rpow_inv (ne_of_gt hr),
    ← ENNReal.ofReal_rpow_of_nonneg hS0 hr.le,
    ENNReal.rpow_rpow_inv (ne_of_gt hr)] at hfin
  exact hfin

end

end Algsuperdiff.Section4.Provider.Homogenization
