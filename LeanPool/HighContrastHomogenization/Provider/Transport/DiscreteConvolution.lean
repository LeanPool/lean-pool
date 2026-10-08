/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.Geometric

/-!
# High-contrast homogenization: Provider.Transport.DiscreteConvolution

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The discrete convolutions of the grid transport

The transport pays every source scale into every target scale, and the two
resulting sums are discrete convolutions against a geometric kernel.  This file
proves them, together with the one combinatorial fact they need.

The workhorse is a geometric bound with no interval hypothesis: an *arbitrary*
finite set of integers on one side of a threshold carries at most the full
geometric weight measured from that threshold.  The transport needs exactly
this generality, because the target scales that share a given auxiliary depth
do not form an interval.

Three displayed convolutions follow.  The bulk convolution
`e.two.grid.bulk.mean` is an identity: shifting a source scale
down by the auxiliary depth converts the row weight at the new terminal scale
into the row weight at the old one, at the exact cost `3^{a(ℓ₀+λ)}`, which the
bound `λ ≤ ℓ₀` turns into the buffer factor `3^{2aℓ₀}`.  The boundary
convolution `e.two.grid.boundary.mean` sums the conservative
row `3^{-(1-g)(j-r)}` against the same weights; the series converges precisely
because the derived exponent is below `1 - g`, and its exact value
`3^{-(1-g-a)λ}(1 - 3^{-(1-g-a)})^{-1}` is exhibited rather than named.  The
bridge error acquires neither buffer factor: both of its sums are bare
geometric series, the first because `Qρ_max - d = Qg + a` is positive and the
second because `a` is.

The combinatorial fact is the multiplicity of the auxiliary depth.  The depth
takes one of two values, so the map carrying a target scale to its bulk source
scale is at most two-to-one, and an adaptive bulk sum costs a factor two
against the sum over source scales.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

noncomputable section

/-! ## The geometric weight of an arbitrary finite set of scales -/

/-- **The geometric weight above a threshold.**  Any finite set of integers at
or above `lo`, weighted by the geometric decay measured from `lo`, carries at
most the total weight `(1 - 3^{-c})^{-1}` of the full series. -/
theorem sum_geom_above_le {c : ℝ} (hc : 0 < c) (lo : ℤ) (s : Finset ℤ)
    (hs : ∀ m ∈ s, lo ≤ m) :
    ∑ m ∈ s, (3 : ℝ) ^ (-c * ((m : ℝ) - (lo : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-c)) := by
  classical
  have hr1 : (3 : ℝ) ^ (-c) < 1 := PortableHistory.geom_ratio_lt_one hc
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ (-c) := PortableHistory.geom_ratio_pos c
  have hden : (0 : ℝ) < 1 - (3 : ℝ) ^ (-c) := by linarith only [hr1]
  have hpt : ∀ m ∈ s, (3 : ℝ) ^ (-c * ((m : ℝ) - (lo : ℝ))) =
      ((3 : ℝ) ^ (-c)) ^ (m - lo).toNat := by
    intro m hm
    have hle : lo ≤ m := hs m hm
    have hcast : (((m - lo).toNat : ℤ) : ℝ) = (m : ℝ) - (lo : ℝ) := by
      have hto : ((m - lo).toNat : ℤ) = m - lo := Int.toNat_of_nonneg (by omega)
      rw [hto]
      push_cast
      ring
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (-c)) ((m - lo).toNat),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    rw [← hcast]
    push_cast
    ring
  have hinj : Set.InjOn (fun m : ℤ => (m - lo).toNat) (s : Set ℤ) := by
    intro x hx y hy hxy
    have hx' : lo ≤ x := hs x (by simpa using hx)
    have hy' : lo ≤ y := hs y (by simpa using hy)
    simp only at hxy
    omega
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_image hinj]
  obtain ⟨N, hN⟩ :=
    Finset.exists_nat_subset_range (s.image fun m : ℤ => (m - lo).toNat)
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN
    (fun k _ _ => pow_nonneg hr0.le k)) ?_
  rw [geom_sum_eq (ne_of_lt hr1)]
  have hpow : (0 : ℝ) ≤ ((3 : ℝ) ^ (-c)) ^ N := pow_nonneg hr0.le _
  have heq : (((3 : ℝ) ^ (-c)) ^ N - 1) / ((3 : ℝ) ^ (-c) - 1) =
      (1 - ((3 : ℝ) ^ (-c)) ^ N) / (1 - (3 : ℝ) ^ (-c)) := by
    rw [div_eq_div_iff (by linarith only [hden]) (ne_of_gt hden)]
    ring
  rw [heq]
  gcongr
  linarith only [hpow]

/-- **The geometric weight below a threshold.**  The reflected form of
`sum_geom_above_le`: any finite set of integers at or below `hi`, weighted by
the geometric decay measured from `hi`, carries at most the total weight of the
full series. -/
theorem sum_geom_below_le {c : ℝ} (hc : 0 < c) (hi : ℤ) (s : Finset ℤ)
    (hs : ∀ j ∈ s, j ≤ hi) :
    ∑ j ∈ s, (3 : ℝ) ^ (-c * ((hi : ℝ) - (j : ℝ))) ≤
      1 / (1 - (3 : ℝ) ^ (-c)) := by
  classical
  have hinj : Set.InjOn (fun j : ℤ => -j) (s : Set ℤ) := by
    intro x _ y _ hxy
    simpa using hxy
  have hbound : ∀ m ∈ s.image fun j : ℤ => -j, -hi ≤ m := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    have := hs j hj
    omega
  have hkey := sum_geom_above_le hc (-hi) (s.image fun j : ℤ => -j) hbound
  rw [Finset.sum_image hinj] at hkey
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) hkey
  congr 1
  push_cast
  ring

/-! ## The bridge error -/

/-- **The bridge error of the nonlinear history.**  Here the weight is the
nonlinear row weight itself, and positivity of the derived exponent already
sums it. -/
theorem bridge_error_nonlinear {a etaX : ℝ} (ha : 0 < a) (heta : 0 ≤ etaX)
    (jStar n : ℤ) :
    ∑ j ∈ Finset.Ico jStar n,
        (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) * etaX ≤
      1 / (1 - (3 : ℝ) ^ (-a)) * etaX := by
  have hkey := sum_geom_below_le ha (n - 1) (Finset.Ico jStar n)
    (fun j hj => by have := (Finset.mem_Ico.mp hj).2; omega)
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ heta
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) hkey
  congr 1
  push_cast
  ring

/-! ## The bulk convolution -/

/-- **`e.two.grid.bulk.mean`, the exact ratio.**  Shifting the
source scale down by the auxiliary depth converts the row weight at the new
terminal scale into the row weight at the old one, at the cost
`3^{a(ℓ₀+λ)}`. -/
theorem bulk_convolution_eq {a : ℝ} (l0 lam n t j : ℝ) (ht : t = n + l0) :
    (3 : ℝ) ^ (-a * (n - 1 - j)) =
      (3 : ℝ) ^ (a * (l0 + lam)) * (3 : ℝ) ^ (-a * (t - 1 - (j - lam))) := by
  subst ht
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

/-- **`e.two.grid.bulk.mean`.**  The auxiliary depth never
exceeds the buffer, so the exact ratio is at most `3^{2aℓ₀}`, with equality on
the deep branch. -/
theorem bulk_convolution_le {a : ℝ} (ha : 0 ≤ a) {l0 lam n t j : ℝ}
    (ht : t = n + l0) (hlam : lam ≤ l0) :
    (3 : ℝ) ^ (-a * (n - 1 - j)) ≤
      (3 : ℝ) ^ (2 * a * l0) * (3 : ℝ) ^ (-a * (t - 1 - (j - lam))) := by
  have hdepth : a * (lam - l0) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha (by linarith only [hlam])
  rw [bulk_convolution_eq l0 lam n t j ht]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  linarith only [hdepth]

/-! ## The boundary convolution -/

/-- **`e.two.grid.boundary.mean`.**  Summing the conservative
boundary row `3^{-(1-g)(j-r)}` against the nonlinear row weights of the new
terminal scale, over any set of target scales at depth at least `λ` above the
source, costs one buffer factor `3^{aℓ₀}` and the geometric series of ratio
`3^{-(1-g-a)}` started at `λ`.  The series converges exactly because the
derived exponent is below `1 - g`. -/
theorem boundary_convolution {a g : ℝ} (hahi : a < 1 - g)
    {l0 n t : ℤ} (ht : t = n + l0) (lam r : ℤ) (s : Finset ℤ)
    (hs : ∀ j ∈ s, r + lam ≤ j) :
    ∑ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
        (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) ≤
      (3 : ℝ) ^ (a * (l0 : ℝ)) *
        ((3 : ℝ) ^ (-(1 - g - a) * (lam : ℝ)) /
          (1 - (3 : ℝ) ^ (-(1 - g - a)))) *
        (3 : ℝ) ^ (-a * ((t : ℝ) - 1 - (r : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hc : 0 < 1 - g - a := by linarith only [hahi]
  subst ht
  have hpt : ∀ j ∈ s, (3 : ℝ) ^ (-a * ((n : ℝ) - 1 - (j : ℝ))) *
      (3 : ℝ) ^ (-(1 - g) * ((j : ℝ) - (r : ℝ))) =
      ((3 : ℝ) ^ (a * (l0 : ℝ)) * (3 : ℝ) ^ (-(1 - g - a) * (lam : ℝ)) *
          (3 : ℝ) ^ (-a * (((n + l0 : ℤ) : ℝ) - 1 - (r : ℝ)))) *
        (3 : ℝ) ^ (-(1 - g - a) * ((j : ℝ) - ((r + lam : ℤ) : ℝ))) := by
    intro j _
    simp only [← Real.rpow_add h3]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
  have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (a * (l0 : ℝ)) *
      (3 : ℝ) ^ (-(1 - g - a) * (lam : ℝ)) *
      (3 : ℝ) ^ (-a * (((n + l0 : ℤ) : ℝ) - 1 - (r : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg h3.le _) (Real.rpow_nonneg h3.le _))
      (Real.rpow_nonneg h3.le _)
  refine le_trans (mul_le_mul_of_nonneg_left
    (sum_geom_above_le hc (r + lam) s hs) hfac) (le_of_eq ?_)
  ring

/-! ## The multiplicity of the auxiliary depth -/

/-- **The adaptive depth of the Whitney filling.**  The deterministic auxiliary
depth is either one or the full buffer, hence lies between one and the
buffer. -/
theorem one_le_depth_and_le {l0 : ℤ} (hl0 : 1 ≤ l0) {lam : ℤ → ℤ}
    (hlam : ∀ j, lam j = 1 ∨ lam j = l0) (j : ℤ) :
    1 ≤ lam j ∧ lam j ≤ l0 := by
  rcases hlam j with h | h <;> omega

/-- **The auxiliary depth is at most two-to-one.**  The deterministic depth
takes one of two values, so at most two target scales are carried to a given
bulk source scale. -/
theorem card_filter_sub_depth_le_two {l0 : ℤ} (lam : ℤ → ℤ)
    (hlam : ∀ j, lam j = 1 ∨ lam j = l0) (s : Finset ℤ) (m : ℤ) :
    (s.filter fun j => j - lam j = m).card ≤ 2 := by
  classical
  have hsub : (s.filter fun j => j - lam j = m) ⊆ ({m + 1, m + l0} : Finset ℤ) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨-, hj2⟩ := hj
    have hd := hlam j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  simp

/-- **The adaptive bulk sum costs a factor two.**  A sum over target scales of
a nonnegative quantity read at the bulk source scale is at most twice the sum
over source scales, by the multiplicity of the auxiliary depth. -/
theorem sum_comp_sub_depth_le {l0 : ℤ} (lam : ℤ → ℤ)
    (hlam : ∀ j, lam j = 1 ∨ lam j = l0) (s t : Finset ℤ) (F : ℤ → ℝ)
    (hF : ∀ m, 0 ≤ F m) (hmem : ∀ j ∈ s, j - lam j ∈ t) :
    ∑ j ∈ s, F (j - lam j) ≤ 2 * ∑ m ∈ t, F m := by
  classical
  have hsub : (s.image fun j => j - lam j) ⊆ t := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    exact hmem j hj
  rw [Finset.sum_comp F fun j => j - lam j, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum (fun m _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun m _ _ => mul_nonneg (by norm_num) (hF m))
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hF m)
  exact_mod_cast card_filter_sub_depth_le_two lam hlam s m

end

end Transport
end HighContrast
end HCPolySupport
