/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BadSetDefinitions

/-!
# LayerDensity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# `l.bad.cubes.density`: the density of bad cubes in a Whitney layer

```
∑_{□ ∈ 𝒲(□_m,n) ∩ ℐ} |□| / |□_m|  ≤  exp(-c E^{-2} γ^{-1}) + 3^{-(n+h_n)/2} .
```

## Why the mass form

The printed display is

```
3^{-n} ⨍_{□ ∈ 𝒲(□_m,n)} 1_{𝓑(□)}  ≤  exp(-c E^{-2} γ^{-1}) + 3^{-(n+h_n)/2}
```

and its proof is exactly: `𝒲(□_m,n) ⊆ {z + □_{m-n-h_n}: z ∈ 3^{m-n-h_n} ℤ^d ∩
□_m}`, `𝓑 ⊆ 𝓑^*`, then `e.density.deterministic` at `h = n + h_n`.  What that
argument produces is the *ambient* density — the bad mass of the layer relative
to `□_m` — and the `3^{-n}` prefactor is precisely the layer's own volume
fraction, already spent.  The literal `3^{-n} ⨍_{𝒲(□_m,n)}` reading is *not*
delivered here: it requires `#𝒲(□_m,n) ≥ 3^{-n}·3^{d(n+h_n)}`, which fails at
`n = 1` (where `#𝒲(□_m,1) = 3^{d h_1}` and `3^{-1}·3^{d(1+h_1)} = 3^{d-1}·3^{d
h_1}`) and at small `n` for large `d`.

## Where the constant comes from

`Percolation.scaleSeparationDensityThreshold M E h` is `exp(-(c(d) E^{-2}
γ^{-1})) + 3^{-h/2}` with the dimension-only witness `c(d) = siteRateBase d /
2` supplied by the proved density conclusion; this is the right side of
`e.bad.cubes.density` read at `h = n + h_n`.

## Main results

* `cubeMassRatio`: `|R| / |Q|` for triadic cubes.
* `sum_cubeMassRatio_badFamilyLayer_le`: `e.bad.cubes.density` in mass form.

## References

* ABK26, `l.bad.cubes.density`.
-/

namespace Algsuperdiff.Section3.Provider.Whitney

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Volume fractions -/

/-- `|R| / |Q|` for triadic cubes: the mass a cube carries inside its root. -/
def cubeMassRatio (Q R : TriadicCube d) : ℝ := ((3 : ℝ) ^ d) ^ (R.scale - Q.scale)

theorem cubeMassRatio_of_mem_descendantsAtDepth {Q R : TriadicCube d} {h : ℕ}
    (hR : R ∈ descendantsAtDepth Q h) :
    cubeMassRatio Q R = (((3 : ℝ) ^ d) ^ h)⁻¹ := by
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
  have h3 : ((3 : ℝ) ^ d) ≠ 0 := by positivity
  rw [cubeMassRatio, hscale, show Q.scale - (h : ℤ) - Q.scale = -(h : ℤ) from by ring,
    zpow_neg, zpow_natCast]

private theorem triadicCube_eq {Q R : TriadicCube d} (hs : Q.scale = R.scale)
    (hi : Q.index = R.index) : Q = R := by
  obtain ⟨qs, qi⟩ := Q
  obtain ⟨rs, ri⟩ := R
  simp only at hs hi
  subst hs
  subst hi
  rfl

/-! ## The layer sits inside the base lattice of its own depth -/

/-- The index of a depth-`h` descendant of `□_m` is a site of `□_h ∩ ℤ^d`, i.e.
the manuscript's base lattice `3^{m-h} ℤ^d ∩ □_m` in the cube-side units of
`Percolation.cubeFinset`. -/
theorem index_mem_cubeFinset_of_mem_descendantsAtDepth {m : ℤ} {h : ℕ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d m) h) :
    R.index ∈ Percolation.cubeFinset (d := d) h := by
  have hE : 2 * (extremeIdx h).toNat + 1 = 3 ^ h := by
    have h1 := two_mul_extremeIdx_add_one h
    have h2 := extremeIdx_nonneg h
    have h3 : ((3 ^ h : ℕ) : ℤ) = (3 : ℤ) ^ h := by push_cast; ring
    omega
  have hlat : Percolation.latDist 0 R.index ≤ (extremeIdx h).toNat := by
    refine Percolation.latDist_le_iff.mpr fun j => ?_
    have hj := abs_le.mp (abs_index_le_extremeIdx hR j)
    simp only [Pi.zero_apply]
    omega
  exact Percolation.mem_cubeFinset_iff.mpr (by omega)

/-- A depth-`h` descendant of `□_m` is the base cube of its own index. -/
theorem siteCube_index_of_mem_descendantsAtDepth {m : ℤ} {h : ℕ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d m) h) :
    Percolation.siteCube (m - (h : ℤ)) R.index = R := by
  have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
  simp only [originCube] at hscale
  exact triadicCube_eq hscale.symm rfl

/-- Distinct depth-`h` descendants of `□_m` have distinct indices. -/
theorem index_injOn_descendantsAtDepth (m : ℤ) (h : ℕ) :
    Set.InjOn (fun R : TriadicCube d => R.index)
      (descendantsAtDepth (originCube d m) h) := by
  intro R hR R' hR' hidx
  have h1 := scale_eq_sub_of_mem_descendantsAtDepth (Finset.mem_coe.mp hR)
  have h2 := scale_eq_sub_of_mem_descendantsAtDepth (Finset.mem_coe.mp hR')
  exact triadicCube_eq (by rw [h1, h2]) hidx

/-! ## The density estimate -/

/-- ```
∑_{□ ∈ 𝒲(□_m,n) ∩ ℐ} |□| / |□_m|
  ≤ exp(-c(d) E^{-2} γ^{-1}) + 3^{-(n+h_n)/2} .
```
-/
theorem sum_cubeMassRatio_badFamilyLayer_le {M : ABKModel d} {m : ℤ} {E b : ℝ}
    {k₀ : ℕ} {omega : CutoffSample d}
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (n : ℕ) :
    ∑ Q ∈ badFamilyLayer M m (whitneyScale M m E b k₀ omega) n omega,
        cubeMassRatio (originCube d m) Q ≤
      Percolation.scaleSeparationDensityThreshold M E
        (n + whitneyScale M m E b k₀ omega n) := by
  classical
  set hn := whitneyScale M m E b k₀ omega with hhn
  set h : ℕ := n + hn n with hh
  set S := badFamilyLayer M m hn n omega with hS
  -- every bad layer cube is a depth-`h` descendant of the root
  have hdesc : ∀ Q ∈ S, Q ∈ descendantsAtDepth (originCube d m) h := fun Q hQ =>
    mem_descendantsAtDepth_of_mem_whitneyLayer (mem_badFamilyLayer_iff.mp hQ).1
  -- the sum is the cardinality times the common mass
  have hsum : ∑ Q ∈ S, cubeMassRatio (originCube d m) Q =
      (S.card : ℝ) * (((3 : ℝ) ^ d) ^ h)⁻¹ := by
    rw [Finset.sum_congr rfl fun Q hQ =>
      cubeMassRatio_of_mem_descendantsAtDepth (hdesc Q hQ), Finset.sum_const,
      nsmul_eq_mul]
  -- the index map embeds the bad layer into the base lattice
  have hcard : (S.image fun Q => Q.index).card = S.card :=
    Finset.card_image_of_injOn fun Q hQ Q' hQ' hidx =>
      index_injOn_descendantsAtDepth m h (hdesc Q (Finset.mem_coe.mp hQ))
        (hdesc Q' (Finset.mem_coe.mp hQ')) hidx
  have hsub : (S.image fun Q => Q.index) ⊆ Percolation.cubeFinset (d := d) h := by
    intro u hu
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    exact index_mem_cubeFinset_of_mem_descendantsAtDepth (hdesc Q hQ)
  -- on that image the extended bad indicator equals one
  set ind : (Fin d → ℤ) → ℝ := fun u =>
    (BadEvents.badExtended M (Percolation.siteCube (m - (h : ℤ)) u)).indicator
      (fun _ => (1 : ℝ)) omega with hind
  have hind_nonneg : ∀ u, 0 ≤ ind u := fun u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) omega
  have hone : ∀ u ∈ (S.image fun Q => Q.index), ind u = 1 := by
    intro u hu
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hu
    have hQbad := (mem_badFamilyLayer_iff.mp hQ).2
    have hmem : omega ∈ BadEvents.badExtended M
        (Percolation.siteCube (m - (h : ℤ)) Q.index) := by
      rw [siteCube_index_of_mem_descendantsAtDepth (hdesc Q hQ)]
      exact BadEvents.bad_subset_badExtended M Q hQbad
    simp only [hind]
    rw [Set.indicator_of_mem hmem]
  have hcount : (S.card : ℝ) ≤ ∑ u ∈ Percolation.cubeFinset (d := d) h, ind u := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun u _ _ => hind_nonneg u)
    have heq : ∑ u ∈ (S.image fun Q => Q.index), ind u = (S.card : ℝ) := by
      rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, hcard, mul_one]
    rw [heq] at hle
    exact hle
  -- compare with the deterministic density conclusion
  have hNpos : (0 : ℝ) < ((3 : ℝ) ^ d) ^ h := by positivity
  have hNcard : ((Percolation.cubeFinset (d := d) h).card : ℝ) = ((3 : ℝ) ^ d) ^ h := by
    rw [Percolation.card_cubeFinset]
    push_cast
    rw [pow_mul]
  have hdens : (S.card : ℝ) * (((3 : ℝ) ^ d) ^ h)⁻¹ ≤
      Percolation.badExtendedDensity M m h omega := by
    rw [Percolation.badExtendedDensity, hNcard]
    rw [mul_comm ((((3 : ℝ) ^ d) ^ h)⁻¹) _]
    exact mul_le_mul_of_nonneg_right hcount (inv_nonneg.2 hNpos.le)
  have hhsep : Percolation.hsep M m E b omega ≤ h := by
    have hle := hsep_le_whitneyScale M m E b k₀ omega n
    rw [← hhn] at hle
    omega
  rw [hsum]
  exact le_trans hdens (Percolation.badExtendedDensity_le_of_hsep_le hne hhsep)

end

end Algsuperdiff.Section3.Provider.Whitney
