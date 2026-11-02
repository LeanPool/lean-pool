/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.SiteFamilyBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SiteFamilyFive

/-!
# SiteFamilyFiveIndep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Separated independence of the site family of Section 5.2

The abstract percolation path bound consumes a family `B : ℕ → Site d → Set Ω`
through three properties: measurability, a per-site tail bound, and the
separated independence `SepIndep`, which asks that blocks of sites at lattice
sup distance more than `3^l` carry independent information of the levels at most
`l`.  This module supplies the third one for the scale decomposition of the
event `Q`, from the finite range of dependence of the field alone.

## The scale shift

The level-`L` event of a site reads the shell of index `n + L` on the cube
`3^{n-1} z + □_n`, so the independence available is the one the cutoff range
lemma provides, at the Euclidean separation `sqrt(d) · 3^{n+L}`.  What the
percolation layer supplies is the lattice separation `3^L`, and the cubes
`3^{n-1} z + □_n` have side `3^n`, three times the lattice spacing `3^{n-1}`:
they overlap, and a lattice separation `D` only yields the Euclidean separation
`3^{n-1} (D - 3)`.  The family is therefore indexed with the same explicit scale
shift `sepShift d = d` that the Section 3 site family uses:

```
shiftedSiteBadEventFive … l z = ∅                       for l < sepShift d,
                              = siteBadEventFive … (l - sepShift d) z  otherwise.
```

The shift buys the factor `3^{d-1} ≥ sqrt(d) + 1`, which is exactly what the
overlap costs (`sqrt_add_one_le_three_pow_pred`), and it changes neither the
union over the levels (`badSet_shiftedSiteBadEventFive`) nor any event of the
family.  It costs a fixed `d`-dependent factor in the tail parameter and nothing
else.

## Main definitions

* `shiftedSiteBadEventFive` — the family as the path bound indexes it.
* `siteRegionFive` — the spatial region read by a set of sites.
* `sitePathExponent` — the exponent `a = 5/4` of the path bound.

## References

* ABK26, the chains of good cubes of Section 5.2 and the general percolation
  bound of the appendix.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open HCPolySupport MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 7. The shifted family and the observation region -/

/-- **The shifted site family.**  The levels below the scale shift are empty;
from the shift on, the level-`l` event is the level-`l - sepShift d` bad event
of the site.  The shift is what turns the lattice separation `3^l` supplied by
the percolation layer into the Euclidean separation demanded by the finite range
of dependence of the field; it changes neither the union over the levels nor any
event of the family. -/
def shiftedSiteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ) (l : ℕ)
    (z : Percolation.Site d) : Set (Cutoff.CutoffSample d) :=
  if l < Provider.Percolation.sepShift d then ∅
  else siteBadEventFive M Creg C0 ep n (l - Provider.Percolation.sepShift d) z

theorem measurableSet_shiftedSiteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    (l : ℕ) (z : Percolation.Site d) :
    MeasurableSet (shiftedSiteBadEventFive M Creg C0 ep n l z) := by
  rw [shiftedSiteBadEventFive]
  split
  · exact MeasurableSet.empty
  · exact measurableSet_siteBadEventFive M Creg C0 ep n _ z

theorem shiftedSiteBadEventFive_of_lt (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    {l : ℕ} (hl : l < Provider.Percolation.sepShift d) (z : Percolation.Site d) :
    shiftedSiteBadEventFive M Creg C0 ep n l z = ∅ := by
  rw [shiftedSiteBadEventFive, ite_eq_left hl]

theorem shiftedSiteBadEventFive_of_le (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    {l : ℕ} (hl : Provider.Percolation.sepShift d ≤ l) (z : Percolation.Site d) :
    shiftedSiteBadEventFive M Creg C0 ep n l z =
      siteBadEventFive M Creg C0 ep n (l - Provider.Percolation.sepShift d) z := by
  rw [shiftedSiteBadEventFive, ite_eq_right (by omega)]

/-- **The shift loses nothing**: the union over the shifted levels is the union
over the levels of the scale decomposition. -/
theorem badSet_shiftedSiteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ)
    (z : Percolation.Site d) :
    Percolation.badSet (shiftedSiteBadEventFive M Creg C0 ep n) z =
      ⋃ L : ℕ, siteBadEventFive M Creg C0 ep n L z := by
  ext omega
  simp only [Percolation.badSet, Set.mem_iUnion]
  constructor
  · rintro ⟨l, hl⟩
    rw [shiftedSiteBadEventFive] at hl
    split at hl
    · exact absurd hl (Set.notMem_empty _)
    · exact ⟨l - Provider.Percolation.sepShift d, hl⟩
  · rintro ⟨L, hL⟩
    refine ⟨L + Provider.Percolation.sepShift d, ?_⟩
    rw [shiftedSiteBadEventFive, ite_eq_right (by omega)]
    have hidx : L + Provider.Percolation.sepShift d - Provider.Percolation.sepShift d = L := by
      omega
    rw [hidx]
    exact hL

/-- **The scale decomposition, in the form the percolation layer consumes**: off
the union of the shifted bad events, the event `Q` of the site occurs. -/
theorem compl_badSet_subset_qEvent (M : ABKModel d) {Creg Cinj C0 ep : ℝ} (n : ℤ)
    (z : Percolation.Site d) (hC0 : 0 ≤ C0) (hep : 0 ≤ ep)
    (hthr : C0 * (1 - shellDecayBase)⁻¹ ≤ Cinj⁻¹) :
    (Percolation.badSet (shiftedSiteBadEventFive M Creg C0 ep n) z)ᶜ ⊆
      qEvent M Creg Cinj n (rescaledLatticePoint n z) ep := by
  rw [badSet_shiftedSiteBadEventFive]
  intro omega homega
  by_contra hcon
  exact homega (compl_qEvent_subset_iUnion_siteBadEventFive M n z hC0 hep hthr hcon)

/-- The spatial region read by the whole family at the sites of `Z`. -/
def siteRegionFive (n : ℤ) (Z : Set (Percolation.Site d)) : Set (Vec d) :=
  ⋃ z ∈ Z, closedCubeAt (rescaledLatticePoint n z) n

theorem measurableSet_siteRegionFive (n : ℤ) (Z : Set (Percolation.Site d)) :
    MeasurableSet (siteRegionFive n Z) :=
  MeasurableSet.biUnion (Set.to_countable Z) fun z _ =>
    (isClosed_closedCubeAt (rescaledLatticePoint n z) n).measurableSet

theorem closedCubeAt_subset_siteRegionFive {n : ℤ} {Z : Set (Percolation.Site d)}
    {z : Percolation.Site d} (hz : z ∈ Z) :
    closedCubeAt (rescaledLatticePoint n z) n ⊆ siteRegionFive n Z :=
  Set.subset_biUnion_of_mem
    (u := fun w : Percolation.Site d => closedCubeAt (rescaledLatticePoint n w) n) hz

/-! ## 8. The separation conversion -/

private theorem abs_le_vecNorm (v : Vec d) (i : Fin d) :
    |v i| ≤ HCPolySupport.Book.Ch02.vecNorm v := by
  have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ)
    (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i
  simpa only [HCPolySupport.Book.Ch02.vecNorm, ge_iff_le, Real.norm_eq_abs] using h

private theorem succ_le_three_pow_pred (hd : 2 ≤ d) : d + 1 ≤ 3 ^ (d - 1) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      calc m + 1 + 1 ≤ 3 * (m + 1) := by omega
        _ ≤ 3 * 3 ^ (m - 1) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (m - 1 + 1) := (pow_succ' 3 (m - 1)).symm
        _ = 3 ^ (m + 1 - 1) := by congr 1; omega

/-- **The dimensional slack of the scale shift.**  The shift `sepShift d = d`
buys the factor `3^{d-1} ≥ sqrt(d) + 1`, which is what the overlap of the cubes
`3^{n-1} z + □_n` (side `3^n` on a lattice of spacing `3^{n-1}`) costs. -/
theorem sqrt_add_one_le_three_pow_pred (hd : 2 ≤ d) :
    Real.sqrt (d : ℝ) + 1 ≤ (3 : ℝ) ^ (d - 1) := by
  have hnat : (d : ℝ) + 1 ≤ (3 : ℝ) ^ (d - 1) := by
    have h := succ_le_three_pow_pred hd
    calc (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((3 ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast h
      _ = (3 : ℝ) ^ (d - 1) := by push_cast; ring
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_of_lt hd
  have hsq : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
    have h2 : (d : ℝ) ≤ ((d : ℝ)) ^ 2 := le_self_pow₀ hd1 (by norm_num)
    calc Real.sqrt (d : ℝ) ≤ Real.sqrt (((d : ℝ)) ^ 2) := Real.sqrt_le_sqrt h2
      _ = (d : ℝ) := Real.sqrt_sq (by linarith only [hd1])
  linarith only [hnat, hsq]

/-- **The separation conversion.**  Two sites at lattice sup distance more than
`3^l`, with `l` at least the scale shift, carry closed cubes at Euclidean
distance at least `sqrt(d) 3^{n + l - sepShift d}`, the literal cutoff range of
the shells that the events of level at most `l` read.

The overlap of the cubes is what the shift pays for: the cube `3^{n-1} z + □_n`
has side `3^n`, three times the lattice spacing `3^{n-1}`, so a lattice
separation `D` only yields a Euclidean separation `3^{n-1}(D - 3)`. -/
theorem sqrt_mul_zpow_le_vecNorm_sub_of_siteDist (hd : 2 ≤ d) (n : ℤ) {l : ℕ}
    (hl : Provider.Percolation.sepShift d ≤ l)
    {Z Z' : Set (Percolation.Site d)}
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z', 3 ^ l < Percolation.siteDist z w)
    {x y : Vec d} (hx : x ∈ siteRegionFive n Z) (hy : y ∈ siteRegionFive n Z') :
    Real.sqrt (d : ℝ) *
        (3 : ℝ) ^ (n + ((l - Provider.Percolation.sepShift d : ℕ) : ℤ)) ≤
      HCPolySupport.Book.Ch02.vecNorm (x - y) := by
  classical
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨w, hw, hyw⟩ := Set.mem_iUnion₂.1 hy
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d))
    Finset.univ_nonempty (fun j => (z j - w j).natAbs)
  set L : ℕ := l - Provider.Percolation.sepShift d with hLdef
  have hlL : l = L + Provider.Percolation.sepShift d := by omega
  -- the two elementary positive quantities
  have hA : (0 : ℝ) < (3 : ℝ) ^ (n - 1) := zpow_pos (by norm_num) _
  set B : ℝ := (3 : ℝ) ^ (L + 1) with hBdef
  have hB3 : (3 : ℝ) ≤ B := by
    calc (3 : ℝ) = (3 : ℝ) ^ 1 := (pow_one 3).symm
      _ ≤ (3 : ℝ) ^ (L + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  -- the lattice separation
  have hlat : ((Percolation.siteDist z w : ℕ) : ℝ) = |(z i : ℝ) - (w i : ℝ)| := by
    rw [Percolation.siteDist, hi]
    have hcast : (((z i - w i).natAbs : ℕ) : ℝ) = |((z i - w i : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs]
      push_cast
      ring
    rw [hcast]
    push_cast
    ring_nf
  have hDge : B * (3 : ℝ) ^ (d - 1) + 1 ≤ ((Percolation.siteDist z w : ℕ) : ℝ) := by
    have hstep : (3 : ℕ) ^ l + 1 ≤ Percolation.siteDist z w := hsep z hz w hw
    have hreal : ((3 : ℝ)) ^ l + 1 ≤ ((Percolation.siteDist z w : ℕ) : ℝ) := by
      calc ((3 : ℝ)) ^ l + 1 = (((3 ^ l + 1 : ℕ)) : ℝ) := by push_cast; ring
        _ ≤ ((Percolation.siteDist z w : ℕ) : ℝ) := by exact_mod_cast hstep
    have hsplit : ((3 : ℝ)) ^ l = B * (3 : ℝ) ^ (d - 1) := by
      rw [hBdef, ← pow_add]
      congr 1
      have : Provider.Percolation.sepShift d = d := rfl
      omega
    rwa [hsplit] at hreal
  -- the sup-coordinate gap between the two cubes
  have hn3 : (3 : ℝ) ^ n = (3 : ℝ) ^ (n - 1) * 3 := by
    rw [← zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hxi := hxz i
  have hyi := hyw i
  rw [rescaledLatticePoint_apply] at hxi
  rw [rescaledLatticePoint_apply] at hyi
  have hax : |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - x i| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    rw [abs_sub_comm]
    exact hxi
  have hay : |y i - (3 : ℝ) ^ (n - 1) * (w i : ℝ)| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := hyi
  have htri : |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - (3 : ℝ) ^ (n - 1) * (w i : ℝ)| ≤
      |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - x i| + |x i - y i| +
        |y i - (3 : ℝ) ^ (n - 1) * (w i : ℝ)| := by
    calc |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - (3 : ℝ) ^ (n - 1) * (w i : ℝ)|
        = |((3 : ℝ) ^ (n - 1) * (z i : ℝ) - x i) + (x i - y i) +
            (y i - (3 : ℝ) ^ (n - 1) * (w i : ℝ))| := by ring_nf
      _ ≤ |((3 : ℝ) ^ (n - 1) * (z i : ℝ) - x i) + (x i - y i)| +
            |y i - (3 : ℝ) ^ (n - 1) * (w i : ℝ)| := abs_add_le _ _
      _ ≤ |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - x i| + |x i - y i| +
            |y i - (3 : ℝ) ^ (n - 1) * (w i : ℝ)| := by
          have := abs_add_le ((3 : ℝ) ^ (n - 1) * (z i : ℝ) - x i) (x i - y i)
          linarith only [this]
  have hcentre : |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - (3 : ℝ) ^ (n - 1) * (w i : ℝ)| =
      (3 : ℝ) ^ (n - 1) * ((Percolation.siteDist z w : ℕ) : ℝ) := by
    calc |(3 : ℝ) ^ (n - 1) * (z i : ℝ) - (3 : ℝ) ^ (n - 1) * (w i : ℝ)|
        = |(3 : ℝ) ^ (n - 1)| * |(z i : ℝ) - (w i : ℝ)| := by
          rw [← abs_mul]
          congr 1
          ring
      _ = (3 : ℝ) ^ (n - 1) * ((Percolation.siteDist z w : ℕ) : ℝ) := by
          rw [abs_of_pos hA, hlat]
  -- the arithmetic
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hpred := sqrt_add_one_le_three_pow_pred hd
  have hBpos : (0 : ℝ) < B := by linarith only [hB3]
  have hprod : B * (Real.sqrt (d : ℝ) + 1) ≤ B * (3 : ℝ) ^ (d - 1) :=
    mul_le_mul_of_nonneg_left hpred hBpos.le
  have hkey : Real.sqrt (d : ℝ) * B ≤
      ((Percolation.siteDist z w : ℕ) : ℝ) - 3 := by
    linarith only [hDge, hprod, hB3]
  have hzpow : (3 : ℝ) ^ (n + (L : ℤ)) = (3 : ℝ) ^ (n - 1) * B := by
    rw [hBdef, ← zpow_natCast (3 : ℝ) (L + 1), ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    push_cast
    ring
  have hgap : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + (L : ℤ)) ≤ |x i - y i| := by
    have hexp : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (n + (L : ℤ)) =
        (3 : ℝ) ^ (n - 1) * (Real.sqrt (d : ℝ) * B) := by
      rw [hzpow]; ring
    have hstep : (3 : ℝ) ^ (n - 1) * (Real.sqrt (d : ℝ) * B) ≤
        (3 : ℝ) ^ (n - 1) * (((Percolation.siteDist z w : ℕ) : ℝ) - 3) :=
      mul_le_mul_of_nonneg_left hkey hA.le
    have hfrom : (3 : ℝ) ^ (n - 1) * (((Percolation.siteDist z w : ℕ) : ℝ) - 3) ≤
        |x i - y i| := by
      rw [hcentre] at htri
      have hn3' : (1 / 2 : ℝ) * (3 : ℝ) ^ n = (3 : ℝ) ^ (n - 1) * (3 / 2) := by
        rw [hn3]; ring
      rw [hn3'] at hax hay
      linarith only [htri, hax, hay]
    rw [hexp]
    linarith only [hstep, hfrom]
  have hnorm : |x i - y i| ≤ HCPolySupport.Book.Ch02.vecNorm (x - y) := by
    have h := abs_le_vecNorm (x - y) i
    simpa only [ge_iff_le, Pi.sub_apply] using h
  linarith only [hgap, hnorm]

/-! ## 9. The two-block separated independence -/

/-- **The sigma-field bridge.**  Everything the shifted family at the sites of
`Z` carries up to level `l` is local information of the shells of index at most
`n + l - sepShift d` in the region read by those sites. -/
theorem generateFrom_shiftedSiteBadEventFive_le (M : ABKModel d) (Creg C0 ep : ℝ)
    (n : ℤ) (l : ℕ) (Z : Set (Percolation.Site d)) :
    MeasurableSpace.generateFrom
        {A | ∃ z ∈ Z, ∃ l' ≤ l, A = shiftedSiteBadEventFive M Creg C0 ep n l' z} ≤
      Cutoff.cutoffSampleLocalSigma M
        (n + ((l - Provider.Percolation.sepShift d : ℕ) : ℤ)) (siteRegionFive n Z) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro A ⟨z, hz, l', hl', rfl⟩
  rw [shiftedSiteBadEventFive]
  split
  · exact @MeasurableSet.empty (Cutoff.CutoffSample d)
      (Cutoff.cutoffSampleLocalSigma M
        (n + ((l - Provider.Percolation.sepShift d : ℕ) : ℤ)) (siteRegionFive n Z))
  · have hbase := measurableSet_siteBadEventFive_local M Creg C0 ep n
      (l' - Provider.Percolation.sepShift d) z
      (U := closedCubeAt (rescaledLatticePoint n z) n) subset_rfl
    refine Provider.BadEvents.cutoffSampleLocalSigma_mono M ?_
      (closedCubeAt_subset_siteRegionFive hz) _ hbase
    have hmono : l' - Provider.Percolation.sepShift d ≤
        l - Provider.Percolation.sepShift d := Nat.sub_le_sub_right hl' _
    omega

/-- **The two-block separated independence of the shifted family.**  Nothing is
assumed: two blocks of sites at lattice sup distance more than `3^l` generate
local information on two regions whose Euclidean separation exceeds the literal
cutoff range of the shells they read, and the proved cutoff range lemma supplies
the independence. -/
theorem sepTwoBlockIndep_shiftedSiteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ)
    (n : ℤ) :
    Percolation.SepTwoBlockIndep (Cutoff.cutoffSampleLaw M).toMeasure
      (shiftedSiteBadEventFive M Creg C0 ep n) := by
  intro l Z Z' hsep
  have hd : 2 ≤ d := M.shellPrefix.dimension
  by_cases hlq : l < Provider.Percolation.sepShift d
  · have htrivial : ∀ T : Set (Percolation.Site d),
        MeasurableSpace.generateFrom
          {A | ∃ z ∈ T, ∃ l' ≤ l, A = shiftedSiteBadEventFive M Creg C0 ep n l' z} ≤ ⊥ := by
      intro T
      refine MeasurableSpace.generateFrom_le ?_
      rintro A ⟨z, -, l', hl', rfl⟩
      rw [shiftedSiteBadEventFive, ite_eq_left (by omega)]
      exact @MeasurableSet.empty (Cutoff.CutoffSample d) ⊥
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left
        (ProbabilityTheory.indep_bot_left _) (htrivial Z)) (htrivial Z')
  · push Not at hlq
    have hEuclid : ∀ ⦃x y : Vec d⦄, x ∈ siteRegionFive n Z → y ∈ siteRegionFive n Z' →
        Real.sqrt (d : ℝ) *
            (3 : ℝ) ^ (n + ((l - Provider.Percolation.sepShift d : ℕ) : ℤ)) ≤
          HCPolySupport.Book.Ch02.vecNorm (x - y) :=
      fun _ _ hx hy => sqrt_mul_zpow_le_vecNorm_sub_of_siteDist hd n hlq hsep hx hy
    have hsource := Cutoff.indep_cutoffSampleLocalSigma_of_indep_completion M
      (n + ((l - Provider.Percolation.sepShift d : ℕ) : ℤ))
      (siteRegionFive n Z) (siteRegionFive n Z')
      (Cutoff.indep_lowerShellLocalCompletion_of_cutoff_separation M
        (n + ((l - Provider.Percolation.sepShift d : ℕ) : ℤ))
        (measurableSet_siteRegionFive n Z) (measurableSet_siteRegionFive n Z') hEuclid)
    exact ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hsource
        (generateFrom_shiftedSiteBadEventFive_le M Creg C0 ep n l Z))
      (generateFrom_shiftedSiteBadEventFive_le M Creg C0 ep n l Z')

/-- **The separated independence hypothesis of the path bound, discharged.** -/
theorem sepIndep_shiftedSiteBadEventFive (M : ABKModel d) (Creg C0 ep : ℝ) (n : ℤ) :
    Percolation.SepIndep (Cutoff.cutoffSampleLaw M).toMeasure
      (shiftedSiteBadEventFive M Creg C0 ep n) :=
  Percolation.sepIndep_of_twoBlock _
    (sepTwoBlockIndep_shiftedSiteBadEventFive M Creg C0 ep n)

/-! ## 10. The exponent at which the family is fed to the path bound -/

/-- **The exponent `a = 5/4`** at which the family is fed to the path bound.
The printed value `a = 2 - γ` is not attainable: summability of the thresholds
and the shell tail force `a < 2 (1 - γ)`, and with the decay exponent `δ = 1/8`
of `shellDecayBase` the largest admissible exponent at `γ = 1/4` is exactly
`2 (1 - γ - δ) = 5/4`. -/
def sitePathExponent : ℝ := 5 / 4

theorem one_lt_sitePathExponent : 1 < sitePathExponent := by
  rw [sitePathExponent]; norm_num

/-- The path bound's dimension gate `a ≤ d` holds in every dimension of the
model. -/
theorem sitePathExponent_le_dim (hd : 2 ≤ d) : sitePathExponent ≤ (d : ℝ) := by
  have h : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rw [sitePathExponent]
  linarith only [h]

/-- **The exponent and the threshold decay are consistent.**  The shell tail
produced by the threshold `C_0 ε γ^{-1/2} 3^{-L/8}` carries the exponent
`2 (1 - γ - 1/8)`, which is at least `a = 5/4` throughout the range of the
scaling parameter. -/
theorem sitePathExponent_le_two_mul_one_sub (M : ABKModel d) :
    sitePathExponent ≤ 2 * (1 - M.gamma - 1 / 8) := by
  have h := M.shellPrefix.gamma_le_quarter
  rw [sitePathExponent]
  linarith only [h]

end

end Algsuperdiff.Section5.Support
