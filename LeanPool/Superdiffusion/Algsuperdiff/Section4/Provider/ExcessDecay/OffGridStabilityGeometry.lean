/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridStabilityGrid
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMetric
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation

/-!
# OffGridStabilityGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The covering geometry of an off-grid cube

The printed proof of `l.lambdas.stability` (ABK26) controls a coarse-grained
quantity on an **off-grid** cube `x + □_k` by the same quantity on *grid*
cubes, through a greedy family

```
𝒢_n(U) = { z ∈ 3^n ℤ^d ∖ (already covered) : z + □_{n+1} ⊆ U }
```

together with the packing count `∑_{z ∈ 𝒢_n(y+□_k)} |□_n| / |□_k| ≤^{n-k}`.

This module proves that geometry.  The family used here is the equivalent
*maximal-cube* description

```
Q is selected for V  ↔  Q ⊆ V  and  parent(Q) ⊄ V,
```

which for the **half-open** realizations is an exact countable partition of any
bounded open `V` — no null set is discarded anywhere.  For `V` an arbitrary real
translate of a triadic cube the packing count is proved with the explicit
constant `2d`:

```
|⋃ {Q selected, scale Q = m}|  ≤  2 d · 3^{m + 1 - k} · |V| .
```

## What is proved and what is not

Only geometry.  No coefficient field, no response functional, no homogenization
error appears below; in particular nothing here is an instance of, or a
fraction of, any source node.  The analytic half of the off-grid stability
estimate — countable subadditivity of the response functional across this
family — is proved in `OffGridStabilitySubadditivity.lean` and lives in
`OffGridStabilitySubadditivity.lean`.

## Deviation from the printed family (recorded)

The printed `𝒢_n(U)` selects `z` with `z + □_{n+1} ⊆ U` and then removes cubes
already covered at coarser scales.  The maximal-cube family below selects `Q`
with `Q ⊆ V` and `parent(Q) ⊄ V`.  The two differ by at most one scale (the
printed family's selection test is the parent's containment, so its cubes are
one generation finer where both are nonempty), which changes the packing
constant by a factor `3` and nothing else; the printed count `C 3^{n-k}` is matched
with `C = 2d` for the maximal family.  The maximal family is used because it
partitions `V` **exactly** rather than up to a null set, which is what the
countable subadditivity consumes.

## Main results

* `exists_maximalCubeIn_mem` — every point of a bounded open set lies in a
  maximal grid cube of that set.
* `iUnion_maximalCubes_eq` — the exact partition.
* `scale_le_of_maximalCubeIn_offGridCube` — the selected scales are `≤ k`.
* `volume_iUnion_maximalCubesAtScale_toReal_le` — the packing count with the
  explicit constant `2d`.

## References

* ABK26, `l.lambdas.stability`.
* ABK26, `e.mathcalE.stability.applied`.
* CoarseGraining, `Homogenization/Geometry/BoundaryLayer.lean`,
  `Homogenization/Geometry/CubeMeasure.lean`,
  `Homogenization/Geometry/Translation.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## 1. The off-grid cube and the maximal-cube family -/

/-- The off-grid cube `w + □_k`, as the real translate of an open triadic cube.
No integrality is assumed of `w`. -/
def offGridCube (w : Vec d) (P : TriadicCube d) : Set (Vec d) :=
  translateSet w (openCubeSet P)

/-- `Q` is a **maximal grid cube of `V`**: it fits inside `V`, its parent does
not. -/
def MaximalCubeIn (V : Set (Vec d)) (Q : TriadicCube d) : Prop :=
  cubeSet Q ⊆ V ∧ ¬ cubeSet (parentCube Q) ⊆ V

/-- The set of maximal grid cubes of `V`. -/
def maximalCubes (V : Set (Vec d)) : Set (TriadicCube d) :=
  {Q | MaximalCubeIn V Q}

/-- The maximal grid cubes of `V` of one fixed scale. -/
def maximalCubesAtScale (V : Set (Vec d)) (m : ℤ) : Set (TriadicCube d) :=
  {Q | MaximalCubeIn V Q ∧ Q.scale = m}

/-! ## 2. The off-grid cube is open, and has the volume of its shape cube -/

theorem isOpen_offGridCube (w : Vec d) (P : TriadicCube d) :
    IsOpen (offGridCube w P) := by
  have hopen : IsOpen (openCubeSet P) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  rw [offGridCube, ← preimage_subRight_eq_translateSet]
  exact hopen.preimage (continuous_id.sub continuous_const)

theorem volume_offGridCube (w : Vec d) (P : TriadicCube d) :
    volume (offGridCube w P) = volume (openCubeSet P) :=
  volume_translateSet_eq w (openCubeSet P)

theorem volume_offGridCube_toReal (w : Vec d) (P : TriadicCube d) :
    (volume (offGridCube w P)).toReal = cubeVolume P := by
  rw [volume_offGridCube, volume_openCubeSet_toReal]

theorem volume_offGridCube_ne_top (w : Vec d) (P : TriadicCube d) :
    volume (offGridCube w P) ≠ ⊤ := by
  rw [volume_offGridCube]
  exact (volume_openCubeSet_lt_top P).ne

/-! ## 3. Existence of a maximal cube through every point -/

variable [NeZero d]

/-- A grid cube contained in the off-grid cube has scale at most the shape
cube's scale: its volume cannot exceed the volume of the off-grid cube. -/
theorem scale_le_of_cubeSet_subset_offGridCube {w : Vec d} {P Q : TriadicCube d}
    (h : cubeSet Q ⊆ offGridCube w P) : Q.scale ≤ P.scale := by
  have hvol : (volume (cubeSet Q)).toReal ≤ (volume (offGridCube w P)).toReal := by
    refine ENNReal.toReal_mono (volume_offGridCube_ne_top w P) (measure_mono h)
  rw [volume_cubeSet_toReal, volume_offGridCube_toReal] at hvol
  rw [cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale] at hvol
  by_contra hcon
  push Not at hcon
  have hlt : (3 : ℝ) ^ P.scale < (3 : ℝ) ^ Q.scale :=
    zpow_lt_zpow_right₀ (by norm_num) hcon
  have hPpos : (0 : ℝ) < (3 : ℝ) ^ P.scale := zpow_pos (by norm_num) P.scale
  have hpow : ((3 : ℝ) ^ P.scale) ^ d < ((3 : ℝ) ^ Q.scale) ^ d :=
    pow_lt_pow_left₀ hlt hPpos.le (NeZero.ne d)
  exact absurd hvol (not_le.2 hpow)

omit [NeZero d] in
/-- A grid cube of small enough scale around a point of an open set lies inside
that set. -/
private theorem exists_scale_cubeSet_subset {V : Set (Vec d)} (hV : IsOpen V) {x : Vec d}
    (hx : x ∈ V) : ∃ m : ℤ, cubeSet (cubeAt m x) ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV x hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (3 : ℝ) ^ m < ε := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (ε⁻¹ : ℝ) (by norm_num : (1 : ℝ) < 3)
    refine ⟨-(n : ℤ), ?_⟩
    have hεinv : (0 : ℝ) < ε⁻¹ := by positivity
    have hpow : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    rw [zpow_neg, zpow_natCast]
    rw [inv_lt_comm₀ hpow hε]
    exact hn
  refine ⟨m, ?_⟩
  intro y hy
  refine hball ?_
  have hspos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hcoord : ∀ i, dist (y i) (x i) < (3 : ℝ) ^ m := by
    intro i
    have hyi := hy i
    have hxi := mem_cubeSet_cubeAt m x i
    have hscale : cubeScaleFactor (cubeAt (d := d) m x) = (3 : ℝ) ^ m := rfl
    rw [hscale] at hyi hxi
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith only [hyi.1, hyi.2, hxi.1, hxi.2]
  exact lt_of_lt_of_le ((dist_pi_lt_iff hspos).2 hcoord) hm.le

/-- **Every point of a bounded open set lies in a maximal grid cube of it.**

The set of scales whose address cube fits inside `V` is downward closed,
nonempty because `V` is open, and bounded above because `V` has finite volume;
its greatest element gives the maximal cube. -/
theorem exists_maximalCubeIn_mem {w : Vec d} {P : TriadicCube d} {x : Vec d}
    (hx : x ∈ offGridCube w P) :
    ∃ Q : TriadicCube d, MaximalCubeIn (offGridCube w P) Q ∧ x ∈ cubeSet Q := by
  classical
  set V : Set (Vec d) := offGridCube w P with hV
  have hbdd : ∃ b : ℤ, ∀ m : ℤ, cubeSet (cubeAt m x) ⊆ V → m ≤ b := by
    refine ⟨P.scale, fun m hm => ?_⟩
    have := scale_le_of_cubeSet_subset_offGridCube (w := w) (P := P) (Q := cubeAt m x) hm
    simpa using this
  have hinh : ∃ m : ℤ, cubeSet (cubeAt m x) ⊆ V :=
    exists_scale_cubeSet_subset (isOpen_offGridCube w P) hx
  obtain ⟨M, hM, hMmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  refine ⟨cubeAt M x, ⟨hM, ?_⟩, mem_cubeSet_cubeAt M x⟩
  rw [parentCube_cubeAt]
  intro hsub
  have := hMmax (M + 1) hsub
  omega

/-! ## 4. The family is an exact partition -/

omit [NeZero d] in
/-- Distinct maximal cubes of `V` are disjoint. -/
theorem disjoint_cubeSet_of_maximalCubeIn {V : Set (Vec d)} {Q R : TriadicCube d}
    (hQ : MaximalCubeIn V Q) (hR : MaximalCubeIn V R) (hne : Q ≠ R) :
    Disjoint (cubeSet Q) (cubeSet R) := by
  rw [Set.disjoint_left]
  intro x hxQ hxR
  have key : ∀ {A B : TriadicCube d}, MaximalCubeIn V A → MaximalCubeIn V B →
      A.scale ≤ B.scale → x ∈ cubeSet A → x ∈ cubeSet B → A = B := by
    intro A B hA hB hle hxA hxB
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact eq_of_scale_eq_of_mem_of_mem heq hxA hxB
    · exfalso
      have hpar : (parentCube A).scale ≤ B.scale := by
        rw [parentCube_scale]; omega
      have hxpar : x ∈ cubeSet (parentCube A) := cubeSet_subset_cubeSet_parentCube A hxA
      have hsub : cubeSet (parentCube A) ⊆ cubeSet B :=
        cubeSet_subset_of_le_of_mem_of_mem hpar hxpar hxB
      exact hA.2 (hsub.trans hB.1)
  rcases le_total Q.scale R.scale with hle | hle
  · exact hne (key hQ hR hle hxQ hxR)
  · exact hne (key hR hQ hle hxR hxQ).symm

/-- **The maximal cubes tile the off-grid cube exactly** — not merely up to a
null set. -/
theorem iUnion_maximalCubes_eq (w : Vec d) (P : TriadicCube d) :
    (⋃ Q ∈ maximalCubes (offGridCube w P), cubeSet Q) = offGridCube w P := by
  refine Set.Subset.antisymm ?_ ?_
  · refine Set.iUnion₂_subset ?_
    intro Q hQ
    exact hQ.1
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := exists_maximalCubeIn_mem hx
    exact Set.mem_iUnion₂.2 ⟨Q, hQ, hxQ⟩

theorem scale_le_of_maximalCubeIn_offGridCube {w : Vec d} {P Q : TriadicCube d}
    (hQ : MaximalCubeIn (offGridCube w P) Q) : Q.scale ≤ P.scale :=
  scale_le_of_cubeSet_subset_offGridCube hQ.1

/-! ## 5. The packing count -/

omit [NeZero d] in
private theorem cubeShrunkSet_subset_openCubeSet {P : TriadicCube d} {t : ℝ} (ht : 0 < t) :
    cubeShrunkSet P t ⊆ openCubeSet P := by
  intro x hx i
  have hs : (0 : ℝ) < cubeScaleFactor P := cubeScaleFactor_pos' P
  obtain ⟨hlo, hhi⟩ := hx i
  have hts : 0 < t * cubeScaleFactor P := mul_pos ht hs
  constructor
  · nlinarith only [hlo, hts]
  · nlinarith only [hhi, hts]

omit [NeZero d] in
private theorem translateSet_mono {w : Vec d} {A B : Set (Vec d)} (h : A ⊆ B) :
    translateSet w A ⊆ translateSet w B := by
  intro x hx
  exact mem_translateSet_iff_sub_mem.2 (h (mem_translateSet_iff_sub_mem.1 hx))

omit [NeZero d] in
/-- **The separation step.**  A maximal cube of scale `m` cannot meet the
`3^{m+1}`-shrunk core of the off-grid cube: if it did, the witness point outside
`V` supplied by the failure of the parent's containment would itself land in
`V`. -/
private theorem disjoint_cubeSet_translateSet_cubeShrunkSet
    {w : Vec d} {P Q : TriadicCube d} (hQ : MaximalCubeIn (offGridCube w P) Q)
    {t : ℝ} (ht : (3 : ℝ) ^ (Q.scale + 1) = t * cubeScaleFactor P) :
    Disjoint (cubeSet Q) (translateSet w (cubeShrunkSet P t)) := by
  rw [Set.disjoint_left]
  intro y hyQ hyS
  obtain ⟨p, hpPar, hpV⟩ : ∃ p, p ∈ cubeSet (parentCube Q) ∧ p ∉ offGridCube w P := by
    by_contra hcon
    push Not at hcon
    exact hQ.2 hcon
  refine hpV ?_
  have hyPar : y ∈ cubeSet (parentCube Q) := cubeSet_subset_cubeSet_parentCube Q hyQ
  have hparScale : cubeScaleFactor (parentCube Q) = (3 : ℝ) ^ (Q.scale + 1) := rfl
  have hclose : ∀ i, |y i - p i| < (3 : ℝ) ^ (Q.scale + 1) := by
    intro i
    have hy := hyPar i
    have hp := hpPar i
    rw [hparScale] at hy hp
    rw [abs_lt]
    constructor <;> linarith only [hy.1, hy.2, hp.1, hp.2]
  have hyS' := mem_translateSet_iff_sub_mem.1 hyS
  refine mem_translateSet_iff_sub_mem.2 ?_
  intro i
  have hshr := hyS' i
  have hclosei := hclose i
  rw [abs_lt] at hclosei
  have hsub : (y - w) i = y i - w i := rfl
  have hsubp : (p - w) i = p i - w i := rfl
  rw [hsub] at hshr
  rw [hsubp]
  rw [ht] at hclosei
  constructor <;> nlinarith only [hshr.1, hshr.2, hclosei.1, hclosei.2]

/-- **The packing count.**

The maximal cubes of one scale `m` all sit in the `3^{m+1}`-boundary layer of
the off-grid cube, so their total volume is at most `2d·3^{m+1-k}` times the
volume of the off-grid cube.  This is the formalized `∑_{z ∈ 𝒢_n(y+□_k)}
|□_n|/|□_k| ≤^{n-k}` of the printed proof, with the explicit constant `C = 2d`. -/
theorem volume_iUnion_maximalCubesAtScale_toReal_le (w : Vec d) (P : TriadicCube d) (m : ℤ) :
    (volume (⋃ Q ∈ maximalCubesAtScale (offGridCube w P) m, cubeSet Q)).toReal ≤
      2 * (d : ℝ) * (3 : ℝ) ^ (m + 1 - P.scale) * cubeVolume P := by
  set A : Set (Vec d) := ⋃ Q ∈ maximalCubesAtScale (offGridCube w P) m, cubeSet Q with hA
  have hAsub : A ⊆ offGridCube w P := by
    refine Set.iUnion₂_subset ?_
    intro Q hQ
    exact hQ.1.1
  have hAtop : volume A ≠ ⊤ :=
    measure_ne_top_of_subset hAsub (volume_offGridCube_ne_top w P)
  have hAle : (volume A).toReal ≤ cubeVolume P := by
    rw [← volume_offGridCube_toReal w P]
    exact ENNReal.toReal_mono (volume_offGridCube_ne_top w P) (measure_mono hAsub)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hVolP : (0 : ℝ) < cubeVolume P := cubeVolume_pos P
  set t : ℝ := (3 : ℝ) ^ (m + 1 - P.scale) with hteq
  have htpos : 0 < t := zpow_pos (by norm_num) _
  by_cases hbig : (1 / 2 : ℝ) < t
  · refine le_trans hAle ?_
    have : (1 : ℝ) ≤ 2 * (d : ℝ) * t := by nlinarith only [hd1, hbig]
    nlinarith only [this, hVolP]
  · push Not at hbig
    have hscaleP : cubeScaleFactor P = (3 : ℝ) ^ P.scale := rfl
    set S : Set (Vec d) := translateSet w (cubeShrunkSet P t) with hS
    have hSsub : S ⊆ offGridCube w P :=
      translateSet_mono (cubeShrunkSet_subset_openCubeSet htpos)
    have hSmeas : MeasurableSet S := by
      rw [hS, ← preimage_subRight_eq_translateSet]
      exact (measurableSet_cubeShrunkSet P t).preimage (measurable_id.sub_const w)
    have hStop : volume S ≠ ⊤ := measure_ne_top_of_subset hSsub (volume_offGridCube_ne_top w P)
    have hdisj : Disjoint A S := by
      rw [hA, Set.disjoint_iUnion₂_left]
      intro Q hQ
      refine disjoint_cubeSet_translateSet_cubeShrunkSet hQ.1 ?_
      rw [hteq, hscaleP, ← zpow_add₀ (show (3 : ℝ) ≠ 0 by norm_num), hQ.2]
      ring_nf
    have hsum : volume A + volume S ≤ volume (offGridCube w P) := by
      rw [← measure_union hdisj hSmeas]
      exact measure_mono (Set.union_subset hAsub hSsub)
    have hsumReal : (volume A).toReal + (volume S).toReal ≤ cubeVolume P := by
      rw [← volume_offGridCube_toReal w P, ← ENNReal.toReal_add hAtop hStop]
      exact ENNReal.toReal_mono (volume_offGridCube_ne_top w P) hsum
    have hSreal : (volume S).toReal = ((1 - 2 * t) * cubeScaleFactor P) ^ d := by
      rw [hS, volume_translateSet_eq, volume_cubeShrunkSet_toReal_of_le_half P hbig]
    have hBern : (1 : ℝ) - 2 * t * (d : ℝ) ≤ (1 - 2 * t) ^ d := by
      have h := one_add_mul_le_pow (a := -(2 * t)) (by nlinarith only [hbig, htpos]) d
      have hrw : (1 : ℝ) + (d : ℝ) * -(2 * t) = 1 - 2 * t * (d : ℝ) := by ring
      have hrw2 : (1 : ℝ) + -(2 * t) = 1 - 2 * t := by ring
      rw [hrw, hrw2] at h
      exact h
    have hexp : ((1 - 2 * t) * cubeScaleFactor P) ^ d = (1 - 2 * t) ^ d * cubeVolume P := by
      rw [mul_pow, cubeVolume_eq_scaleFactor_pow]
    have hlow : cubeVolume P - 2 * t * (d : ℝ) * cubeVolume P ≤ (volume S).toReal := by
      rw [hSreal, hexp]
      nlinarith only [hBern, hVolP]
    nlinarith only [hsumReal, hlow]

omit [NeZero d] in
/-- Each scale-`m` union is finite in measure. -/
theorem volume_iUnion_maximalCubesAtScale_ne_top (w : Vec d) (P : TriadicCube d) (m : ℤ) :
    volume (⋃ Q ∈ maximalCubesAtScale (offGridCube w P) m, cubeSet Q) ≠ ⊤ := by
  refine measure_ne_top_of_subset ?_ (volume_offGridCube_ne_top w P)
  exact Set.iUnion₂_subset fun Q hQ => hQ.1.1

omit [NeZero d] in
/-- The scale-`m` union, as a genuinely countable sum of cube volumes. -/
theorem tsum_volume_maximalCubesAtScale (V : Set (Vec d)) (m : ℤ) :
    volume (⋃ Q ∈ maximalCubesAtScale V m, cubeSet Q) =
      ∑' Q : maximalCubesAtScale V m, volume (cubeSet (Q : TriadicCube d)) := by
  refine measure_biUnion (Set.to_countable _) ?_ fun Q _ => measurableSet_cubeSet Q
  intro Q hQ R hR hne
  exact disjoint_cubeSet_of_maximalCubeIn hQ.1 hR.1 hne

/-- **The packing count in summed form**, the shape the countable subadditivity
consumes. -/
theorem tsum_volume_maximalCubesAtScale_toReal_le (w : Vec d) (P : TriadicCube d) (m : ℤ) :
    (∑' Q : maximalCubesAtScale (offGridCube w P) m,
        volume (cubeSet (Q : TriadicCube d))).toReal ≤
      2 * (d : ℝ) * (3 : ℝ) ^ (m + 1 - P.scale) * cubeVolume P := by
  rw [← tsum_volume_maximalCubesAtScale]
  exact volume_iUnion_maximalCubesAtScale_toReal_le w P m

end

end Algsuperdiff.Section4.Provider.ExcessDecay
