/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Multiscale.ConclusionCompetitor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance

/-!
# CollarMass

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The collar-vs-bad mass comparison: `hmasscol` discharged

`LayerUniform.sum_sum_ofReal_two_leg_le_ofReal_layerContrib` and its concrete
twin
`ConclusionCompetitor.toReal_tsum_simplexPartition_cutoff_two_leg_le_payload`
price the collar leg of `e.sum-of-a-decomp` (ABK26) by the free sequence
`Bad`, through the **caller-supplied** datum

```
hmasscol : ∀ n, ∑ □ ∈ collarLayer M m hn n omega, |□| / |□_m| ≤ Bad n .
```

`LayerUniform`'s module docstring discloses this as a remaining step of Step 3
("The **mass comparison**. is NOT proved here and is NOT assumed to be true").
This module proves it, at the proved carrier and with an explicit
dimension-only constant and an explicit layer window.

## The mathematics

The collar family of layer `n` is `collarLayer = 𝒩(ℐ) ∩ 𝒲(□_m,n)`, the Whitney
cubes of layer `n` that touch a bad cube (`e.neighborhood.def`, at the cubewise
reading `∃ □' ∈ ℐ, dist(□,□') = 0`; the printed reading agrees on the finite
families the manuscript uses, `ClusterLayerConstraint`'s reconciliation).  Two
geometric facts turn its mass into bad mass.

1. **The layer window.**  A layer-`n` cube touching a layer-`j` cube forces `|n
   - j| ≤ 1` --- `BoundaryDistance.whitneyLayer_index_close_of_cubeTouch`, the
   adjacency clause (second sentence; pin corrected), proved's two-sided
   boundary distance with **no** percolation input and **no** connectivity.
   With `e.hn.def`/`e.hn.gap` (/5937: `h` nondecreasing, `h_{j+1} ≤ h_j + 1`)
   the *depth* gap is then `|(n + h_n) - (j + h_j)| ≤ 2`
   (`layerDepth_sub_le_two`), which is exactly the `±2`-generation window, here
   derived from the touch relation rather than assumed from the scale.
2. **The bounded overlap.**  Fix a bad cube `R` of layer `j`.  Every layer-`n`
   cube `Q` touching `R` has, in every coordinate,
   `|Q.index i - R.index i · 3^{scale R - scale Q}| ≤ (1 + 3^{scale R - scale Q})/2 ≤ 5`
   (`abs_index_sub_mul_zpow_le_five`), so its index lies in an explicit box of
   `11` integers per coordinate; distinct cubes of one layer have distinct
   indices, whence at most `11^d` of them
   (`card_le_eleven_pow_of_forall_cubeTouch`).  Each of them carries mass at
   most `9^d` times the mass of `R` (`cubeMassRatio_le_nine_pow_mul`, the same
   `±2` depth window).  Choosing for each collar cube **one** bad cube it
   touches and summing fibrewise gives the constant `11^d · 9^d = 99^d`.

The conclusion (`sum_cubeMassRatio_collarLayer_le`) is

```
∑_{□ ∈ 𝒩(ℐ) ∩ 𝒲(□_m,n)} |□|/|□_m|
    ≤ 99^d · ∑_{j = n-1}^{n+1} ∑_{□ ∈ ℐ_j} |□|/|□_m| .
```

Composed with the proved mass form of `l.bad.cubes.density`
(`ConclusionAssembly.sum_cubeMassRatio_badFamilyLayer_le_layerQuantity`, i.e.)
and the same depth window, this becomes the consumer-shaped

```
∑_{□ ∈ 𝒩(ℐ) ∩ 𝒲(□_m,n)} |□|/|□_m|
    ≤ 9 · 99^d · ( exp(-c(d) E^{-2} γ^{-1}) + 3^{-(n+h_n)/2} )
```

(`sum_cubeMassRatio_collarLayer_le_layerQuantity`).  The sharper split the proof
actually establishes is `99^d · (3·exp(...) + 9·3^{-(n+h_n)/2})`; `9·99^d` is the
clean common majorant, and `9` is `3` (the three layers of the window) times `3`
(the at most two generations of depth a window layer can lose).

## What the consumer must do with it

`Bad` is a *free* sequence in
`toReal_tsum_simplexPartition_cutoff_two_leg_le_payload`, constrained there by
`hBad0`, `hBadMass : Bad j ≤ Cmass·3^{-j}` and `hBadDens: Bad j ≤ ε +
3^{-(j+h_j)/2}`.  Since `hmasscol : ∀ n, ∑_{collar} ≤ Bad n` does not mention
`Ccol`, the constant *cannot* be folded there; the route is

```
Bad j := 9·99^d · ( exp(-c(d) E^{-2} γ^{-1}) + 3^{-(j+h_j)/2} ) ,
```

with which `hmasscol` IS `sum_cubeMassRatio_collarLayer_le_layerQuantity`
verbatim.  The remaining bookkeeping, named and NOT discharged here:
(a) `hBadDens` carries coefficient exactly `1` on the `3^{-·/2}` term, so
re-establishing it at this `Bad` needs a shift of the consumer's own free
`(hs, k₀)` pair (the manuscript's `k₀ := c E^{-2} γ^{-1}` absorbs
dimension-only factors by shrinking `c`); (b) `hBadMass : Bad j ≤ Cmass·3^{-j}`
fails for large `j` at any `j`-constant
`ε`-term, and no `Cmass` re-selection and no per-binder split can restore it
--- the feasible route is `Bad j:= min(9·99^d·(A + 3^{-L_j/2}), Cmass·3^{-j})`,
whose second branch follows from `collarLayer_subset` + `hmassgood` + `hMass`,
all already in the consumer's slot.  Both are the consumer's, and the
dimension-only constant is absorbed by the `C_col ↦ C·C_col` reconciliation
(performed here on the `Bad` slot rather than on `Ccol`).  **No printed
density input is strengthened**: the right-hand side is the printed
`l.bad.cubes.density` threshold, read at the three layers of the window.

## Main results

* `abs_index_sub_mul_zpow_le_five`, `card_le_eleven_pow_of_forall_cubeTouch`:
  the dimension-only overlap count `11^d` at the cubewise touch relation.
* `layerDepth_sub_le_two`: the `±2` depth window.
* `sum_cubeMassRatio_collarLayer_le`: **the obligation**, at `99^d` and the
  three-layer window `n-1, n, n+1`.
* `sum_cubeMassRatio_collarLayer_le_layerQuantity`: the same priced by
  `l.bad.cubes.density`, in the `Bad n` shape the consumer instantiates.

## References

* ABK26, `sss.whitney.partition` (`e.hn.def`, `e.hn.gap`, `e.W.n.def`,
  `e.bad.cubes.in.partition`, `e.neighborhood.def`);
  `l.bad.clusters.geometry` (the adjacency clause); `l.bad.cubes.density`;
  Step 3 of `p.bfA.multiscalebound` (the collar family `𝒩(ℐ) ∩ 𝒲(□_n,k)`).
-/

namespace Algsuperdiff.Section3.Provider.Multiscale

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Whitney

noncomputable section

variable {d : ℕ}

/-! ## Index localization of a touching pair -/

private theorem cube_eq_of_scale_of_index {Q R : TriadicCube d}
    (hs : Q.scale = R.scale) (hi : Q.index = R.index) : Q = R := by
  obtain ⟨qs, qi⟩ := Q
  obtain ⟨rs, ri⟩ := R
  simp only at hs hi
  subst hs
  subst hi
  rfl

/-- **Index localization of a touching pair.**  If the closed cubes `□` and `□'`
meet (`e.neighborhood.def`'s `dist(□,□') = 0`) and `□'` is at most two
generations coarser, then the index of `□` sits within `5` of the rescaled
index of `□'` in every coordinate: the touch inequality `|x·3^{s} - y·3^{s'}| ≤
(3^{s} + 3^{s'})/2` divided by `3^{s}` reads `|x - y·3^{s'-s}| ≤ (1 +
3^{s'-s})/2 ≤ 5`. -/
theorem abs_index_sub_mul_zpow_le_five {Q R : TriadicCube d}
    (hsc : R.scale - Q.scale ≤ 2) (htouch : CubeTouch Q R) (i : Fin d) :
    |(Q.index i : ℝ) - (R.index i : ℝ) * (3 : ℝ) ^ (R.scale - Q.scale)| ≤ 5 := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hupos : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hw9 : (3 : ℝ) ^ (R.scale - Q.scale) ≤ 9 := by
    have h := zpow_le_zpow_right₀ (a := (3 : ℝ)) (by norm_num) hsc
    norm_num at h
    exact h
  have hsplit : (3 : ℝ) ^ R.scale
      = (3 : ℝ) ^ (R.scale - Q.scale) * (3 : ℝ) ^ Q.scale := by
    rw [← zpow_add₀ h3]
    congr 1
    ring
  have htc : |(Q.index i : ℝ) * (3 : ℝ) ^ Q.scale
        - (R.index i : ℝ) * (3 : ℝ) ^ R.scale|
      ≤ 1 / 2 * (3 : ℝ) ^ Q.scale + 1 / 2 * (3 : ℝ) ^ R.scale := by
    have h := (cubeTouch_iff.mp htouch) i
    simpa only [cubeCenter, HCPolySupport.cubeRadius, cubeScaleFactor] using h
  have hfac : (Q.index i : ℝ) - (R.index i : ℝ) * (3 : ℝ) ^ (R.scale - Q.scale)
      = ((Q.index i : ℝ) * (3 : ℝ) ^ Q.scale
          - (R.index i : ℝ) * (3 : ℝ) ^ R.scale) * ((3 : ℝ) ^ Q.scale)⁻¹ := by
    rw [hsplit]
    field_simp
  calc |(Q.index i : ℝ) - (R.index i : ℝ) * (3 : ℝ) ^ (R.scale - Q.scale)|
      = |(Q.index i : ℝ) * (3 : ℝ) ^ Q.scale
          - (R.index i : ℝ) * (3 : ℝ) ^ R.scale| * ((3 : ℝ) ^ Q.scale)⁻¹ := by
        rw [hfac, abs_mul, abs_of_pos (inv_pos.2 hupos)]
    _ ≤ (1 / 2 * (3 : ℝ) ^ Q.scale + 1 / 2 * (3 : ℝ) ^ R.scale)
          * ((3 : ℝ) ^ Q.scale)⁻¹ :=
        mul_le_mul_of_nonneg_right htc (inv_pos.2 hupos).le
    _ = (1 + (3 : ℝ) ^ (R.scale - Q.scale)) / 2 := by
        rw [hsplit]
        field_simp
    _ ≤ 5 := by linarith

/-- **The bounded-overlap count**, the dimension-only `C_d` the manuscript folds
into `#𝒩(ℐ) ≤ C_d·#ℐ`: at most `11^d` cubes of one common scale `sQ` can touch a
fixed cube `R` at most two generations coarser.  Their indices lie in an
explicit box of `11` integers per coordinate, and distinct cubes of a common
scale have distinct indices. -/
theorem card_le_eleven_pow_of_forall_cubeTouch {sQ : ℤ} {R : TriadicCube d}
    {A : Finset (TriadicCube d)} (hsc : R.scale - sQ ≤ 2)
    (hA : ∀ Q ∈ A, Q.scale = sQ ∧ CubeTouch Q R) :
    A.card ≤ 11 ^ d := by
  classical
  have hmaps : ∀ Q ∈ A, Q.index ∈ Fintype.piFinset (fun i : Fin d =>
      Finset.Icc (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ - 5)
        (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ + 5)) := by
    intro Q hQ
    obtain ⟨hQs, hQt⟩ := hA Q hQ
    refine Fintype.mem_piFinset.2 fun i => Finset.mem_Icc.2 ⟨?_, ?_⟩
    · have habs := abs_index_sub_mul_zpow_le_five (by rw [hQs]; exact hsc) hQt i
      rw [hQs] at habs
      have h1 := (abs_le.mp habs).1
      have hle : (R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ) ≤ ((Q.index i + 5 : ℤ) : ℝ) := by
        push_cast
        linarith
      have hceil := Int.ceil_le.2 hle
      omega
    · have habs := abs_index_sub_mul_zpow_le_five (by rw [hQs]; exact hsc) hQt i
      rw [hQs] at habs
      have h2 := (abs_le.mp habs).2
      have hceil : (R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)
          ≤ (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ : ℝ) := Int.le_ceil _
      have hfin : ((Q.index i : ℤ) : ℝ)
          ≤ ((⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ + 5 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hfin
  have hinj : Set.InjOn (fun Q : TriadicCube d => Q.index) A := by
    intro Q hQ Q' hQ' hidx
    exact cube_eq_of_scale_of_index
      (by rw [(hA Q (Finset.mem_coe.mp hQ)).1, (hA Q' (Finset.mem_coe.mp hQ')).1]) hidx
  have hcard : (Fintype.piFinset (fun i : Fin d =>
      Finset.Icc (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ - 5)
        (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ + 5))).card = 11 ^ d := by
    rw [Fintype.card_piFinset]
    have hone : ∀ i : Fin d,
        (Finset.Icc (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ - 5)
          (⌈(R.index i : ℝ) * (3 : ℝ) ^ (R.scale - sQ)⌉ + 5)).card = 11 := by
      intro i
      rw [Int.card_Icc]
      omega
    rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  exact le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) (le_of_eq hcard)

/-- **Mass at comparable scales.**  A cube at most two generations finer than
`R` carries at most `9^d = (3^d)^2` times the mass of `R` inside `□_m`. -/
theorem cubeMassRatio_le_nine_pow_mul (m : ℤ) {Q R : TriadicCube d}
    (h : Q.scale - R.scale ≤ 2) :
    cubeMassRatio (originCube d m) Q ≤ (9 : ℝ) ^ d * cubeMassRatio (originCube d m) R := by
  have hbase : (1 : ℝ) ≤ (3 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ d := by positivity
  have h9 : ((3 : ℝ) ^ d) ^ (2 : ℤ) = (9 : ℝ) ^ d := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, ← pow_mul, mul_comm, pow_mul]
    norm_num
  simp only [cubeMassRatio]
  calc ((3 : ℝ) ^ d) ^ (Q.scale - (originCube d m).scale)
      ≤ ((3 : ℝ) ^ d) ^ ((2 : ℤ) + (R.scale - (originCube d m).scale)) :=
        zpow_le_zpow_right₀ hbase (by omega)
    _ = (9 : ℝ) ^ d * ((3 : ℝ) ^ d) ^ (R.scale - (originCube d m).scale) := by
        rw [zpow_add₀ (ne_of_gt hpos), h9]

/-! ## The layer-index window -/

/-- **The `±2` depth window.**  For a nondecreasing scale profile obeying
`e.hn.gap`, neighbouring layer indices sit at depths `n + h_n` differing by at
most two: layer `n-1` is coarser by `1 + (h_n - h_{n-1}) ∈ {1,2}` and layer
`n+1` is finer by `1 + (h_{n+1} - h_n) ∈ {1,2}`. -/
theorem layerDepth_sub_le_two {hn : ℕ → ℕ} (hmono : Monotone hn)
    (hgap : ∀ j, hn (j + 1) ≤ hn j + 1) {n j : ℕ} (h1 : n ≤ j + 1) (h2 : j ≤ n + 1) :
    ((n : ℤ) + (hn n : ℤ)) - ((j : ℤ) + (hn j : ℤ)) ≤ 2 ∧
      -2 ≤ ((n : ℤ) + (hn n : ℤ)) - ((j : ℤ) + (hn j : ℤ)) := by
  rcases (show j = n ∨ j = n + 1 ∨ n = j + 1 by omega) with h | h | h
  · subst h
    omega
  · subst h
    have ha := hmono (show n ≤ n + 1 by omega)
    have hb := hgap n
    omega
  · subst h
    have ha := hmono (show j ≤ j + 1 by omega)
    have hb := hgap j
    omega

/-! ## The collar mass comparison -/

/-- **The collar-vs-bad mass comparison** --- the disclosed `hmasscol` obligation
of `LayerUniform` and `ConclusionCompetitor`, discharged at the proved carrier:

```
∑_{□ ∈ 𝒩(ℐ) ∩ 𝒲(□_m,n)} |□|/|□_m|
    ≤ 99^d · ∑_{j = n-1}^{n+1} ∑_{□ ∈ ℐ_j} |□|/|□_m| .
```

The constant is `11^d` (the overlap count) times `9^d` (the mass ratio across
the depth window) and is dimension-only; the window `n-1, n, n+1` is exact, and
comes from the adjacency clause through
`whitneyLayer_index_close_of_cubeTouch`.  No connectivity of `ℐ`, no
disjointness of component neighborhoods and no percolation input is used. -/
theorem sum_cubeMassRatio_collarLayer_le (M : ABKModel d) {m : ℤ} {hn : ℕ → ℕ}
    (hn1 : ∀ j, 1 ≤ hn j) (hmono : Monotone hn) (hgap : ∀ j, hn (j + 1) ≤ hn j + 1)
    (omega : CutoffSample d) (n : ℕ) :
    ∑ Q ∈ collarLayer M m hn n omega, cubeMassRatio (originCube d m) Q
      ≤ (99 : ℝ) ^ d * ∑ j ∈ Finset.Icc (n - 1) (n + 1),
          ∑ R ∈ badFamilyLayer M m hn j omega, cubeMassRatio (originCube d m) R := by
  classical
  have hwit : ∀ Q : TriadicCube d, ∃ x : (_ : ℕ) × TriadicCube d,
      Q ∈ collarLayer M m hn n omega →
        (x ∈ (Finset.Icc (n - 1) (n + 1)).sigma
            (fun j => badFamilyLayer M m hn j omega) ∧ CubeTouch Q x.2) := by
    intro Q
    by_cases hQ : Q ∈ collarLayer M m hn n omega
    · have hQ' : Q ∈ collarLayer M m hn n omega := hQ
      rw [collarLayer, Finset.mem_filter] at hQ'
      obtain ⟨hQlayer, -, R, hRbad, htouch⟩ := hQ'
      obtain ⟨j, hRj⟩ := hRbad.1
      have hclose := whitneyLayer_index_close_of_cubeTouch hn1 hQlayer hRj htouch
      have hmemj : j ∈ Finset.Icc (n - 1) (n + 1) :=
        Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hmemR : R ∈ badFamilyLayer M m hn j omega :=
        mem_badFamilyLayer_iff.2 ⟨hRj, hRbad.2⟩
      exact ⟨⟨j, R⟩, fun _ => ⟨Finset.mem_sigma.2 ⟨hmemj, hmemR⟩, htouch⟩⟩
    · exact ⟨⟨0, Q⟩, fun h => absurd h hQ⟩
  choose φ hφ using hwit
  have hmapsto : ∀ Q ∈ collarLayer M m hn n omega, φ Q ∈
      (Finset.Icc (n - 1) (n + 1)).sigma (fun j => badFamilyLayer M m hn j omega) :=
    fun Q hQ => (hφ Q hQ).1
  have hfib : ∀ x ∈ (Finset.Icc (n - 1) (n + 1)).sigma
      (fun j => badFamilyLayer M m hn j omega),
      ∑ Q ∈ (collarLayer M m hn n omega).filter (fun Q => φ Q = x),
          cubeMassRatio (originCube d m) Q
        ≤ (99 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sigma.mp hx
    have hxlayer : x.2 ∈ whitneyLayer (d := d) m hn x.1 :=
      badFamilyLayer_subset M m hn x.1 omega hx2
    have hxscale : x.2.scale = m - (x.1 : ℤ) - (hn x.1 : ℤ) :=
      scale_eq_of_mem_whitneyLayer hxlayer
    obtain ⟨hIcc1, hIcc2⟩ := Finset.mem_Icc.mp hx1
    have hwin := layerDepth_sub_le_two hmono hgap (n := n) (j := x.1) (by omega) (by omega)
    have hAmem : ∀ Q ∈ (collarLayer M m hn n omega).filter (fun Q => φ Q = x),
        Q.scale = m - (n : ℤ) - (hn n : ℤ) ∧ CubeTouch Q x.2 := by
      intro Q hQ
      obtain ⟨hQS, hQx⟩ := Finset.mem_filter.mp hQ
      refine ⟨scale_eq_of_mem_whitneyLayer (collarLayer_subset M m hn n omega hQS), ?_⟩
      have := (hφ Q hQS).2
      rwa [hQx] at this
    have hcard : ((collarLayer M m hn n omega).filter (fun Q => φ Q = x)).card ≤ 11 ^ d :=
      card_le_eleven_pow_of_forall_cubeTouch (sQ := m - (n : ℤ) - (hn n : ℤ))
        (by rw [hxscale]; omega) hAmem
    have hterm : ∀ Q ∈ (collarLayer M m hn n omega).filter (fun Q => φ Q = x),
        cubeMassRatio (originCube d m) Q
          ≤ (9 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2 := by
      intro Q hQ
      exact cubeMassRatio_le_nine_pow_mul m (by rw [(hAmem Q hQ).1, hxscale]; omega)
    have hnn : (0 : ℝ) ≤ (9 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2 :=
      mul_nonneg (by positivity) (cubeMassRatio_nonneg _ _)
    calc ∑ Q ∈ (collarLayer M m hn n omega).filter (fun Q => φ Q = x),
            cubeMassRatio (originCube d m) Q
        ≤ ((collarLayer M m hn n omega).filter (fun Q => φ Q = x)).card •
            ((9 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (((collarLayer M m hn n omega).filter (fun Q => φ Q = x)).card : ℝ) *
            ((9 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2) := by
          rw [nsmul_eq_mul]
      _ ≤ ((11 : ℝ) ^ d) * ((9 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          exact_mod_cast hcard
      _ = (99 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2 := by
          rw [← mul_assoc, ← mul_pow]
          norm_num
  calc ∑ Q ∈ collarLayer M m hn n omega, cubeMassRatio (originCube d m) Q
      = ∑ x ∈ (Finset.Icc (n - 1) (n + 1)).sigma
            (fun j => badFamilyLayer M m hn j omega),
          ∑ Q ∈ (collarLayer M m hn n omega).filter (fun Q => φ Q = x),
            cubeMassRatio (originCube d m) Q :=
        (Finset.sum_fiberwise_of_maps_to hmapsto _).symm
    _ ≤ ∑ x ∈ (Finset.Icc (n - 1) (n + 1)).sigma
            (fun j => badFamilyLayer M m hn j omega),
          (99 : ℝ) ^ d * cubeMassRatio (originCube d m) x.2 :=
        Finset.sum_le_sum hfib
    _ = (99 : ℝ) ^ d * ∑ x ∈ (Finset.Icc (n - 1) (n + 1)).sigma
            (fun j => badFamilyLayer M m hn j omega),
          cubeMassRatio (originCube d m) x.2 := by
        rw [Finset.mul_sum]
    _ = (99 : ℝ) ^ d * ∑ j ∈ Finset.Icc (n - 1) (n + 1),
          ∑ R ∈ badFamilyLayer M m hn j omega, cubeMassRatio (originCube d m) R := by
        rw [Finset.sum_sigma']

/-! ## The collar mass at the proved Whitney and percolation carriers -/

/-- **The collar mass priced by `l.bad.cubes.density`**, in the shape the Step-3
consumer instantiates `Bad n` at:

```
∑_{□ ∈ 𝒩(ℐ) ∩ 𝒲(□_m,n)} |□|/|□_m|
    ≤ 9·99^d · ( exp(-c(d) E^{-2} γ^{-1}) + 3^{-(n+h_n)/2} ) .
```

The three layers of the window contribute the threshold at their own depths;
each such depth is within two generations of `n + h_n`, costing a factor `3` on
`3^{-h/2}`, so the regrouping constant is `3·3 = 9` (the sharper split the
proof establishes is `3·exp(...) + 9·3^{-(n+h_n)/2}`).  The dimension-only
factor `9·99^d` is carried on the consumer's `Bad` slot (the `C·C_col`
reconciliation; it cannot literally fold into `Ccol` --- see the consumer note
above); the printed density input is not strengthened. -/
theorem sum_cubeMassRatio_collarLayer_le_layerQuantity {M : ABKModel d} {m : ℤ}
    {E b : ℝ} {k₀ : ℕ} {omega : CutoffSample d}
    (hb0 : 0 < b) (hb : b ≤ 1 / 8) (hk₀ : 1 ≤ k₀)
    (hne : (Percolation.hsepSet M m E b omega).Nonempty) (n : ℕ) :
    ∑ Q ∈ collarLayer M m (whitneyScale M m E b k₀ omega) n omega,
        cubeMassRatio (originCube d m) Q
      ≤ 9 * (99 : ℝ) ^ d *
          (Real.exp (-(Percolation.siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹)))
            + (3 : ℝ) ^
                (-(layerQuantity b (Percolation.hsep M m E b omega) k₀ n / 2))) := by
  classical
  have hws : whitneyScale M m E b k₀ omega
      = whitneyScaleSeq b (Percolation.hsep M m E b omega) k₀ := rfl
  have hn1 : ∀ j, 1 ≤ whitneyScale M m E b k₀ omega j := by
    intro j
    have h := add_le_whitneyScaleSeq b (Percolation.hsep M m E b omega) k₀ j
    rw [hws]
    omega
  have hmono : Monotone (whitneyScale M m E b k₀ omega) := by
    rw [hws]
    exact whitneyScaleSeq_mono hb0.le (by linarith) _ _
  have hgap : ∀ j, whitneyScale M m E b k₀ omega (j + 1)
      ≤ whitneyScale M m E b k₀ omega j + 1 := by
    intro j
    rw [hws]
    exact whitneyScaleSeq_succ_le hb0 hb _ _ j
  set A : ℝ := Real.exp (-(Percolation.siteRateBase d / 2 * (E⁻¹ ^ 2 * M.gamma⁻¹))) with hA
  set B : ℝ := (3 : ℝ) ^
      (-(layerQuantity b (Percolation.hsep M m E b omega) k₀ n / 2)) with hB
  have hA0 : (0 : ℝ) ≤ A := (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  have hstep : ∀ j ∈ Finset.Icc (n - 1) (n + 1),
      ∑ R ∈ badFamilyLayer M m (whitneyScale M m E b k₀ omega) j omega,
          cubeMassRatio (originCube d m) R ≤ A + 3 * B := by
    intro j hj
    refine le_trans (sum_cubeMassRatio_badFamilyLayer_le_layerQuantity hne j) ?_
    obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
    have hwin := (layerDepth_sub_le_two hmono hgap (n := n) (j := j)
      (by omega) (by omega)).1
    have hnat : n + whitneyScale M m E b k₀ omega n
        ≤ j + whitneyScale M m E b k₀ omega j + 2 := by omega
    have e1 : layerQuantity b (Percolation.hsep M m E b omega) k₀ n
        = (n : ℝ) + (whitneyScale M m E b k₀ omega n : ℝ) := rfl
    have e2 : layerQuantity b (Percolation.hsep M m E b omega) k₀ j
        = (j : ℝ) + (whitneyScale M m E b k₀ omega j : ℝ) := rfl
    have hlay : layerQuantity b (Percolation.hsep M m E b omega) k₀ n
        ≤ layerQuantity b (Percolation.hsep M m E b omega) k₀ j + 2 := by
      rw [e1, e2]
      have hcast : ((n + whitneyScale M m E b k₀ omega n : ℕ) : ℝ)
          ≤ ((j + whitneyScale M m E b k₀ omega j + 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at hcast
      linarith
    have hexp : -(layerQuantity b (Percolation.hsep M m E b omega) k₀ j / 2)
        ≤ 1 + -(layerQuantity b (Percolation.hsep M m E b omega) k₀ n / 2) := by
      linarith
    have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
    have h3 : (3 : ℝ) ^
        (1 + -(layerQuantity b (Percolation.hsep M m E b omega) k₀ n / 2)) = 3 * B := by
      rw [hB, Real.rpow_add (by norm_num : (0 : ℝ) < 3), Real.rpow_one]
    rw [h3] at hrpow
    linarith
  have hsum := Finset.sum_le_card_nsmul (Finset.Icc (n - 1) (n + 1))
    (fun j => ∑ R ∈ badFamilyLayer M m (whitneyScale M m E b k₀ omega) j omega,
      cubeMassRatio (originCube d m) R) (A + 3 * B) hstep
  rw [nsmul_eq_mul] at hsum
  have hcard : (((Finset.Icc (n - 1) (n + 1)).card : ℕ) : ℝ) ≤ 3 := by
    have : (Finset.Icc (n - 1) (n + 1)).card ≤ 3 := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast this
  have hAB : (0 : ℝ) ≤ A + 3 * B := by linarith
  have hsum3 : ∑ j ∈ Finset.Icc (n - 1) (n + 1),
      ∑ R ∈ badFamilyLayer M m (whitneyScale M m E b k₀ omega) j omega,
        cubeMassRatio (originCube d m) R ≤ 3 * (A + 3 * B) :=
    le_trans hsum (mul_le_mul_of_nonneg_right hcard hAB)
  have hpow : (0 : ℝ) ≤ (99 : ℝ) ^ d := by positivity
  refine le_trans (sum_cubeMassRatio_collarLayer_le M hn1 hmono hgap omega n) ?_
  have hfinal : (99 : ℝ) ^ d * (3 * (A + 3 * B)) ≤ 9 * (99 : ℝ) ^ d * (A + B) := by
    have h : 3 * (A + 3 * B) ≤ 9 * (A + B) := by linarith
    calc (99 : ℝ) ^ d * (3 * (A + 3 * B)) ≤ (99 : ℝ) ^ d * (9 * (A + B)) :=
          mul_le_mul_of_nonneg_left h hpow
      _ = 9 * (99 : ℝ) ^ d * (A + B) := by ring
  exact le_trans (mul_le_mul_of_nonneg_left hsum3 hpow) hfinal

end

end Algsuperdiff.Section3.Provider.Multiscale
