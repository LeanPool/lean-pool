/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.SeriesTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# LatticeCount

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The triadic lattice annulus is finite, with an explicit count

ABK26, §4.1, `l.good.scales.ratio.lambda`, the per-annulus atom tail: the
union-bound penalty `C(n−k+1)³` of the lattice maximum

```
max_{z ∈ 3^{k−2}ℤ^d ∩ (□_n ∖ □_{n−1})} ( … )_+
```

This module proves it.

## What is proved

* `abs_le_of_mem_latticeCubeSet` — a lattice point of spacing `3^j` inside `□_outer`
  has integer coordinates bounded by `3^{outer−j}` (crude by a factor `2`, which
  costs nothing downstream).
* `latticeAnnulusFinset` — the `Finset` of those index vectors, with
  `card_latticeAnnulusFinset_le` giving `# ≤ 3^{d(outer−j+1)}`.
* `log_card_latticeAnnulusFinset_le` — the form the union bound consumes, and
  `annulusPenalty` / `log_card_le_annulusPenalty_rpow_sub_one` — the admissible
  penalty `c` of `isBigOWith_fmax`, which at `σ = 1/3` is a *cubic* in
  `outer − j`, the manuscript's `C(n−k+1)³`.

## Scope

Provider material: proved local helpers.  Pure geometry and counting; no
probability, no model, no standing assumption.

## References

* ABK26, `l.good.scales.ratio.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open HCPolySupport
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The coordinate bound -/

/-- **A triadic lattice point of spacing `3^j` inside `□_outer` has bounded
index.**  The sharp bound is `(3^{outer−j} − 1)/2`; the crude `3^{outer−j}` used
here avoids an integer division and costs only a bounded factor in the
logarithm. -/
theorem abs_le_of_mem_latticeCubeSet {j outer : ℤ} (hj : j ≤ outer) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d j outer) (i : Fin d) :
    |v i| ≤ (3 : ℤ) ^ (outer - j).toNat := by
  have hp : ((outer - j).toNat : ℤ) = outer - j := Int.toNat_of_nonneg (by omega)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hsplit : (3 : ℝ) ^ outer = (3 : ℝ) ^ j * (3 : ℝ) ^ ((outer - j).toNat : ℕ) := by
    rw [← zpow_natCast (3 : ℝ) ((outer - j).toNat), hp, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hmem : Support.triadicLatticePoint j v ∈ openCubeSet (originCube d outer) := hv
  have hcoord := (mem_openCubeSet_originCube_iff.mp hmem) i
  rw [Support.triadicLatticePoint] at hcoord
  have hpow0 : (0 : ℝ) < (3 : ℝ) ^ ((outer - j).toNat : ℕ) := by positivity
  -- divide the two printed inequalities by `3^j`
  have hupper : ((v i : ℤ) : ℝ) < (3 : ℝ) ^ ((outer - j).toNat : ℕ) := by
    have h := hcoord.2
    rw [hsplit] at h
    have h' : (3 : ℝ) ^ j * ((v i : ℤ) : ℝ)
        < (3 : ℝ) ^ j * ((1 / 2 : ℝ) * (3 : ℝ) ^ ((outer - j).toNat : ℕ)) := by
      calc (3 : ℝ) ^ j * ((v i : ℤ) : ℝ) < 1 / 2 * ((3 : ℝ) ^ j * (3 : ℝ) ^ ((outer - j).toNat :
        ℕ)) :=
            h
        _ = (3 : ℝ) ^ j * ((1 / 2 : ℝ) * (3 : ℝ) ^ ((outer - j).toNat : ℕ)) := by ring
    have h'' := lt_of_mul_lt_mul_left h' h3.le
    linarith only [h'', hpow0]
  have hlower : -((3 : ℝ) ^ ((outer - j).toNat : ℕ)) < ((v i : ℤ) : ℝ) := by
    have h := hcoord.1
    rw [hsplit] at h
    have h' : (3 : ℝ) ^ j * (-((1 / 2 : ℝ) * (3 : ℝ) ^ ((outer - j).toNat : ℕ)))
        < (3 : ℝ) ^ j * ((v i : ℤ) : ℝ) := by
      calc (3 : ℝ) ^ j * (-((1 / 2 : ℝ) * (3 : ℝ) ^ ((outer - j).toNat : ℕ)))
          = -(1 / 2) * ((3 : ℝ) ^ j * (3 : ℝ) ^ ((outer - j).toNat : ℕ)) := by ring
        _ < (3 : ℝ) ^ j * ((v i : ℤ) : ℝ) := h
    have h'' := lt_of_mul_lt_mul_left h' h3.le
    linarith only [h'', hpow0]
  have hcast : ((3 : ℤ) ^ (outer - j).toNat : ℝ) = (3 : ℝ) ^ ((outer - j).toNat : ℕ) := by
    push_cast
    ring
  have hZ : |v i| < (3 : ℤ) ^ (outer - j).toNat := by
    have : (|v i| : ℝ) < ((3 : ℤ) ^ (outer - j).toNat : ℝ) := by
      rw [hcast]
      rw [abs_lt]
      exact ⟨hlower, hupper⟩
    exact_mod_cast this
  omega

/-! ## 2. The enclosing box and its cardinality -/

/-- The `Finset` of integer index vectors with all coordinates in `[-B, B]`. -/
def boxIndexFinset (d : ℕ) (B : ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-B) B

theorem mem_boxIndexFinset_iff {B : ℤ} {v : Fin d → ℤ} :
    v ∈ boxIndexFinset d B ↔ ∀ i, |v i| ≤ B := by
  simp only [boxIndexFinset, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem card_boxIndexFinset (d : ℕ) (B : ℤ) :
    (boxIndexFinset d B).card = (2 * B + 1).toNat ^ d := by
  rw [boxIndexFinset, Fintype.card_piFinset]
  have hcard : ∀ _i : Fin d, (Finset.Icc (-B) B).card = (2 * B + 1).toNat := by
    intro _i
    rw [Int.card_Icc]
    congr 1
    omega
  rw [Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ## 3. The annulus `Finset` -/

open Classical in
/-- **The lattice annulus as a `Finset`.**  The proved *set*
`Support.latticeAnnulusSet` cut out of the enclosing index box. -/
def latticeAnnulusFinset (d : ℕ) (j outer inner : ℤ) : Finset (Fin d → ℤ) :=
  (boxIndexFinset d ((3 : ℤ) ^ (outer - j).toNat)).filter fun v =>
    Support.triadicLatticePoint j v ∈
      openCubeSet (originCube d outer) \ openCubeSet (originCube d inner)

theorem mem_latticeAnnulusFinset_iff {j outer inner : ℤ} (hj : j ≤ outer)
    {v : Fin d → ℤ} :
    v ∈ latticeAnnulusFinset d j outer inner ↔
      v ∈ Support.latticeAnnulusSet d j outer inner := by
  classical
  rw [latticeAnnulusFinset, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨mem_boxIndexFinset_iff.2 fun i => ?_, h⟩
    exact abs_le_of_mem_latticeCubeSet hj
      (show v ∈ Support.latticeCubeSet d j outer from h.1) i

/-- **The count.**  `#(3^j ℤ^d ∩ (□_outer ∖ □_inner)) ≤ 3^{d(outer−j+1)}`. -/
theorem card_latticeAnnulusFinset_le (d : ℕ) {j outer inner : ℤ} :
    (latticeAnnulusFinset d j outer inner).card ≤ 3 ^ (d * ((outer - j).toNat + 1)) := by
  classical
  have hsub : (latticeAnnulusFinset d j outer inner).card
      ≤ (boxIndexFinset d ((3 : ℤ) ^ (outer - j).toNat)).card :=
    Finset.card_filter_le _ _
  rw [card_boxIndexFinset d ((3 : ℤ) ^ (outer - j).toNat)] at hsub
  refine le_trans hsub ?_
  have hstep : (2 * (3 : ℤ) ^ (outer - j).toNat + 1).toNat ≤ 3 ^ ((outer - j).toNat + 1) := by
    rw [Int.toNat_le]
    push_cast
    have h3 : (1 : ℤ) ≤ (3 : ℤ) ^ (outer - j).toNat := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith only [h3]
  calc (2 * (3 : ℤ) ^ (outer - j).toNat + 1).toNat ^ d
      ≤ (3 ^ ((outer - j).toNat + 1)) ^ d := Nat.pow_le_pow_left hstep d
    _ = 3 ^ (d * ((outer - j).toNat + 1)) := by
        rw [← pow_mul, Nat.mul_comm]

/-! ## 4. The union-bound penalty -/

/-- The logarithm of the count, in the form the union bound consumes. -/
theorem log_card_latticeAnnulusFinset_le (d : ℕ) {j outer inner : ℤ} :
    Real.log ((latticeAnnulusFinset d j outer inner).card : ℝ)
      ≤ (d : ℝ) * (((outer - j).toNat : ℝ) + 1) * Real.log 3 := by
  classical
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hRHS : (0 : ℝ) ≤ (d : ℝ) * (((outer - j).toNat : ℝ) + 1) * Real.log 3 := by positivity
  rcases Nat.eq_zero_or_pos (latticeAnnulusFinset d j outer inner).card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact hRHS
  · have hcardpos : (0 : ℝ) < ((latticeAnnulusFinset d j outer inner).card : ℝ) := by
      exact_mod_cast hpos
    have hle : ((latticeAnnulusFinset d j outer inner).card : ℝ)
        ≤ (3 : ℝ) ^ (d * ((outer - j).toNat + 1)) := by
      have hcard := card_latticeAnnulusFinset_le d (j := j) (outer := outer) (inner := inner)
      calc ((latticeAnnulusFinset d j outer inner).card : ℝ)
          ≤ ((3 ^ (d * ((outer - j).toNat + 1)) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ = (3 : ℝ) ^ (d * ((outer - j).toNat + 1)) := by push_cast; ring
    refine le_trans (Real.log_le_log hcardpos hle) ?_
    rw [Real.log_pow]
    have hcast : ((d * ((outer - j).toNat + 1) : ℕ) : ℝ)
        = (d : ℝ) * (((outer - j).toNat : ℝ) + 1) := by push_cast; ring
    rw [hcast]

/-- The annular counting penalty in the proportion tail estimate. -/
def annulusPenalty (d : ℕ) (sigma : ℝ) (p : ℕ) : ℝ :=
  (1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3) ^ sigma⁻¹

theorem annulusPenalty_base_nonneg (d : ℕ) (p : ℕ) :
    (0 : ℝ) ≤ 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  positivity

theorem one_le_annulusPenalty (d : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (p : ℕ) :
    1 ≤ annulusPenalty d sigma p := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine Real.one_le_rpow ?_ (inv_nonneg.2 hsigma.le)
  have : (0 : ℝ) ≤ (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by positivity
  linarith only [this]

/-- The penalty raised back to the power `σ` returns its base. -/
theorem annulusPenalty_rpow (d : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (p : ℕ) :
    annulusPenalty d sigma p ^ sigma = 1 + (d : ℝ) * ((p : ℝ) + 1) * Real.log 3 := by
  rw [annulusPenalty, ← Real.rpow_mul (annulusPenalty_base_nonneg d p),
    inv_mul_cancel₀ (ne_of_gt hsigma), Real.rpow_one]

/-- The defining property of the penalty: it clears the `isBigOWith_fmax`
interface `log(#S) ≤ c^σ − 1` at the lattice annulus. -/
theorem log_card_le_annulusPenalty_rpow_sub_one (d : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (j outer inner : ℤ) :
    Real.log ((latticeAnnulusFinset d j outer inner).card : ℝ)
      ≤ annulusPenalty d sigma (outer - j).toNat ^ sigma - 1 := by
  rw [annulusPenalty_rpow d hsigma]
  have h := log_card_latticeAnnulusFinset_le d (j := j) (outer := outer) (inner := inner)
  linarith only [h]

end

end Algsuperdiff.Section4.Provider.Proportion
