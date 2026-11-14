/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Lattice
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Percolation.LatticeBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedFinite

/-!
# PercolationScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The event `Q`, the light-path events, and the percolation scale

Section 5.2 produces, for each maximal scale `m`, an `ℕ`-valued random variable
`Y_m` below which every rescaled lattice path from `□_{m-n}` to the complement
of `□_{m-n+1}` meets the good event `Q` at at least `(3/4) 3^{m-n}` of its
sites.
The reading is the strong one: for almost every sample a single `Y_m` precedes
all scales and all paths.

`Y_m` is defined here as a **total** `ℕ`-valued function of the sample, finite
in the sense of the source only almost surely: the defining property is
available exactly on the set of samples for which the light-path events stop
occurring, and the source asks only that this set carry full measure.  The
statements about `Y_m` are accordingly almost-everywhere statements, and the
value off that set does not enter them; `percolationScaleTotal_eq_zero_of_not`
records what that value is.  Nothing is hidden behind a caller hypothesis.

`Measurable Y` is a **strengthening** of the source, which asks only for a
random variable; it is stated explicitly and proved from the measurability of
the events `Q`.

## Main definitions

* `rescaledLatticePoint n z` — the point `3^{n-1} z` of `ℝ^d`.
* `qEvent M Creg Cinj n z ep` — `𝒢(z+□_n, ε) ∩ 𝒥(z+□_n, Cinj⁻¹ ε γ^{-1/2})`.
* `qSiteCount M Creg Cinj n ep S omega` — the number of sites of `S` at which
  `Q` occurs.
* `lightQPathEvent M Creg Cinj m ep k` — some path crosses from `□_k` to the
  complement of `□_{k+1}` meeting `Q` at fewer than `(3/4) 3^k` of its sites.
* `percolationScaleTotal M Creg Cinj m ep` — the total `Y_m`.

## References

* ABK26, the chains of good cubes of Section 5.2.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped BigOperators

noncomputable section

/-- The classical decidability instance used by the `Finset.filter` below.  The
counted quantity does not depend on it: `qSiteCount_eq_card_filter` identifies
the count with the filter formed by any other instance. -/
noncomputable local instance percolationScalePropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

variable {d : ℕ}

/-! ## 1. The event `Q` -/

/-- The rescaled lattice point `3^{n-1} z`. -/
def rescaledLatticePoint (n : ℤ) (z : Fin d → ℤ) : Vec d :=
  Real.rpow 3 ((n : ℝ) - 1) • fun j => (z j : ℝ)

/-- **The event `Q(z+□_n, ε)`**: the good cube event at `z + □_n` intersected
with the large-scale event at threshold `Cinj⁻¹ ε γ^{-1/2}`. -/
def qEvent (M : ABKModel d) (Creg Cinj : ℝ) (n : ℤ) (z : Vec d) (ep : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  goodCubeEvent M Creg n z ep ∩
    largeScaleEvent M n z (Cinj⁻¹ * ep * (Real.sqrt M.gamma)⁻¹)

/-- **The number of sites of `S` at which `Q` occurs**, at cube scale `n` and
after the rescaling `3^{n-1} ℤ^d ↦ ℤ^d`. -/
def qSiteCount (M : ABKModel d) (Creg Cinj : ℝ) (n : ℤ) (ep : ℝ)
    (S : Finset (Fin d → ℤ)) (omega : Cutoff.CutoffSample d) : ℕ :=
  (S.filter fun z => omega ∈ qEvent M Creg Cinj n (rescaledLatticePoint n z) ep).card

/-- **The count is insensitive to the decidability instance.**  Whatever
instance a consumer's `Finset.filter` carries, the resulting cardinality is the
one counted here. -/
theorem qSiteCount_eq_card_filter (M : ABKModel d) (Creg Cinj : ℝ) (n : ℤ) (ep : ℝ)
    (S : Finset (Fin d → ℤ)) (omega : Cutoff.CutoffSample d)
    [DecidablePred fun z : Fin d → ℤ =>
      omega ∈ qEvent M Creg Cinj n (rescaledLatticePoint n z) ep] :
    qSiteCount M Creg Cinj n ep S omega =
      (S.filter fun z =>
        omega ∈ qEvent M Creg Cinj n (rescaledLatticePoint n z) ep).card := by
  refine congrArg Finset.card ?_
  ext z
  simp only [Finset.mem_filter]

/-- **The site count as a sum of indicators.**  This is the form in which the
count is compared with a sum over the sites of a path, both here and where the
percolation estimate's count meets the count of the statement. -/
theorem qSiteCount_eq_sum_indicator (M : ABKModel d) (Creg Cinj : ℝ) (n : ℤ) (ep : ℝ)
    (S : Finset (Fin d → ℤ)) (omega : Cutoff.CutoffSample d) :
    ((qSiteCount M Creg Cinj n ep S omega : ℕ) : ℝ) =
      ∑ z ∈ S, (qEvent M Creg Cinj n (rescaledLatticePoint n z) ep).indicator
        (fun _ => (1 : ℝ)) omega := by
  rw [qSiteCount, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : omega ∈ qEvent M Creg Cinj n (rescaledLatticePoint n z) ep
  · simp only [h, ↓reduceIte, Set.indicator_of_mem]
  · simp only [h, ↓reduceIte, not_false_eq_true, Set.indicator_of_notMem]

/-! ## 2. The light-path events -/

/-- **The light-path event at scale `k`**: some lattice path starting in the
cube `□_k` and ending outside the cube `□_{k+1}` meets `Q` at fewer than
`(3/4) 3^k` of its sites.  The rescaling `3^{n-1} ℤ^d ↦ ℤ^d` at the cube scale
`n = m - k` turns the source's crossing of `□_{m-1}` to the complement of `□_m`
into this crossing of the unit lattice. -/
def lightQPathEvent (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ) (k : ℕ) :
    Set (Cutoff.CutoffSample d) :=
  {omega | ∃ (N : ℕ) (x : ℕ → Fin d → ℤ),
    Provider.Percolation.IsLatticePath x N ∧
      x 0 ∈ Provider.Percolation.cubeAt k 0 ∧
        x N ∉ Provider.Percolation.cubeAt (k + 1) 0 ∧
          ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
            (Percolation.pathSites N x) omega : ℕ) : ℝ) <
            (3 : ℝ) / 4 * (3 : ℝ) ^ k}

/-- The extension of a finite path to all of `ℕ`. -/
def pathExtend {N : ℕ} (p : Fin (N + 1) → Fin d → ℤ) : ℕ → Fin d → ℤ :=
  fun i => if h : i < N + 1 then p ⟨i, h⟩ else 0

theorem pathExtend_apply {N : ℕ} (p : Fin (N + 1) → Fin d → ℤ) {i : ℕ} (hi : i < N + 1) :
    pathExtend p i = p ⟨i, hi⟩ := by
  simp [pathExtend, hi]

/-- **The path quantifier is countable.**  Only the restriction of a path to its
first `N + 1` sites occurs in the light-path event, so the existential over
`ℕ → Fin d → ℤ` is a countable union over finite paths. -/
theorem lightQPathEvent_eq_iUnion (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    (k : ℕ) :
    lightQPathEvent M Creg Cinj m ep k =
      ⋃ N : ℕ, ⋃ p : Fin (N + 1) → Fin d → ℤ,
        {omega | Provider.Percolation.IsLatticePath (pathExtend p) N ∧
          pathExtend p 0 ∈ Provider.Percolation.cubeAt k 0 ∧
            pathExtend p N ∉ Provider.Percolation.cubeAt (k + 1) 0 ∧
              ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
                (Percolation.pathSites N (pathExtend p)) omega : ℕ) : ℝ) <
                (3 : ℝ) / 4 * (3 : ℝ) ^ k} := by
  ext omega
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, lightQPathEvent]
  constructor
  · rintro ⟨N, x, hpath, h0, hN, hcard⟩
    refine ⟨N, fun j => x j.1, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [pathExtend_apply _ (by omega), pathExtend_apply _ (by omega)]
      exact hpath i hi
    · rw [pathExtend_apply _ (by omega)]
      exact h0
    · rw [pathExtend_apply _ (by omega)]
      exact hN
    · have himage : Percolation.pathSites N (pathExtend (N := N) fun j => x j.1) =
          Percolation.pathSites N x := by
        refine Finset.image_congr fun i hi => ?_
        exact pathExtend_apply _ (by simpa using Finset.mem_range.1 (Finset.mem_coe.mp hi))
      rw [himage]
      exact hcard
  · rintro ⟨N, p, hpath, h0, hN, hcard⟩
    exact ⟨N, pathExtend p, hpath, h0, hN, hcard⟩

/-! ## 3. The total percolation scale -/

/-- The samples for which the light-path events eventually stop. -/
def eventuallyHeavyPaths (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  {omega | ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k}

/-- **The percolation scale `Y_m`**, as a total function of the sample: the least
scale beyond which no light path occurs.  On the exceptional set where light
paths occur at arbitrarily large scales there is no such scale; the value there
is `0` and no statement below uses it. -/
def percolationScaleTotal (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    (omega : Cutoff.CutoffSample d) : ℕ :=
  if h : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k then
    Nat.find h
  else 0

/-- **The defining property**, on the set where it is available. -/
theorem percolationScaleTotal_spec (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    {omega : Cutoff.CutoffSample d}
    (h : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k) :
    ∀ k : ℕ, percolationScaleTotal M Creg Cinj m ep omega ≤ k →
      omega ∉ lightQPathEvent M Creg Cinj m ep k := by
  intro k hk
  rw [percolationScaleTotal, dite_eq_left h] at hk
  exact Nat.find_spec h k hk

/-- **The value on the exceptional set.**  Nothing is hidden: where light paths
occur at arbitrarily large scales the scale is `0`.  The almost-everywhere
statements below do not use this value. -/
theorem percolationScaleTotal_eq_zero_of_not (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ)
    (ep : ℝ) {omega : Cutoff.CutoffSample d}
    (h : ¬ ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k) :
    percolationScaleTotal M Creg Cinj m ep omega = 0 :=
  dite_eq_right h

theorem le_percolationScaleTotal_iff (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    {omega : Cutoff.CutoffSample d}
    (h : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k) (N : ℕ) :
    N ≤ percolationScaleTotal M Creg Cinj m ep omega ↔
      ∀ j < N, ¬ ∀ k : ℕ, j ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k := by
  rw [percolationScaleTotal, dite_eq_left h]
  exact Nat.le_find_iff h N

/-! ## 4. The percolation scale almost surely -/

/-- **The crossing bound of the source, almost surely.**  For almost every
sample and every scale `n ≤ m - Y_m`, every lattice path from `□_{m-n}` to the
complement of `□_{m-n+1}` meets `Q` at at least `(3/4) 3^{m-n}` of its distinct
sites. -/
theorem percolationScaleTotal_ae_crossing (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ)
    (ep : ℝ) {P : Measure (Cutoff.CutoffSample d)}
    (hae : ∀ᵐ omega ∂P, omega ∈ eventuallyHeavyPaths M Creg Cinj m ep) :
    ∀ᵐ omega ∂P, ∀ n : ℤ,
      n ≤ m - (percolationScaleTotal M Creg Cinj m ep omega : ℤ) →
      ∀ (N : ℕ) (x : ℕ → Fin d → ℤ),
        Provider.Percolation.IsLatticePath x N →
        x 0 ∈ Provider.Percolation.cubeAt (m - n).toNat 0 →
        x N ∉ Provider.Percolation.cubeAt ((m - n).toNat + 1) 0 →
        (3 : ℝ) / 4 * (3 : ℝ) ^ (m - n).toNat ≤
          ((qSiteCount M Creg Cinj n ep (Percolation.pathSites N x) omega : ℕ) : ℝ) := by
  filter_upwards [hae] with omega homega
  intro n hn N x hpath h0 hN
  set k : ℕ := (m - n).toNat with hk
  have hle : percolationScaleTotal M Creg Cinj m ep omega ≤ k := by omega
  have hindex : m - (k : ℤ) = n := by omega
  have hnot := percolationScaleTotal_spec M Creg Cinj m ep homega k hle
  by_contra hlt
  push Not at hlt
  refine hnot ⟨N, x, hpath, h0, hN, ?_⟩
  rw [hindex]
  exact hlt

/-! ## 5. Measurability -/

/-- **The light-path events are measurable**, given the measurability of the
events `Q`.  The countable-union decomposition reduces the path quantifier to a
countable index, and on each finite path the count is a finite sum of
indicators. -/
theorem measurableSet_lightQPathEvent (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    (hq : ∀ (n : ℤ) (z : Vec d), MeasurableSet (qEvent M Creg Cinj n z ep)) (k : ℕ) :
    MeasurableSet (lightQPathEvent M Creg Cinj m ep k) := by
  rw [lightQPathEvent_eq_iUnion]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun p => ?_
  have hcount : Measurable fun omega : Cutoff.CutoffSample d =>
      ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
        (Percolation.pathSites N (pathExtend p)) omega : ℕ) : ℝ) := by
    have hsum : Measurable fun omega : Cutoff.CutoffSample d =>
        ∑ z ∈ Percolation.pathSites N (pathExtend p),
          (qEvent M Creg Cinj (m - (k : ℤ))
            (rescaledLatticePoint (m - (k : ℤ)) z) ep).indicator
            (fun _ => (1 : ℝ)) omega :=
      Finset.measurable_sum _ fun z _ => measurable_const.indicator (hq _ _)
    have hfun : (fun omega : Cutoff.CutoffSample d =>
        ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
          (Percolation.pathSites N (pathExtend p)) omega : ℕ) : ℝ)) =
        fun omega : Cutoff.CutoffSample d =>
          ∑ z ∈ Percolation.pathSites N (pathExtend p),
            (qEvent M Creg Cinj (m - (k : ℤ))
              (rescaledLatticePoint (m - (k : ℤ)) z) ep).indicator
              (fun _ => (1 : ℝ)) omega := by
      funext omega
      exact qSiteCount_eq_sum_indicator M Creg Cinj (m - (k : ℤ)) ep
        (Percolation.pathSites N (pathExtend p)) omega
    rw [hfun]
    exact hsum
  by_cases hgeom : Provider.Percolation.IsLatticePath (pathExtend p) N ∧
      pathExtend p 0 ∈ Provider.Percolation.cubeAt k 0 ∧
        pathExtend p N ∉ Provider.Percolation.cubeAt (k + 1) 0
  · have hset : {omega : Cutoff.CutoffSample d |
        Provider.Percolation.IsLatticePath (pathExtend p) N ∧
          pathExtend p 0 ∈ Provider.Percolation.cubeAt k 0 ∧
            pathExtend p N ∉ Provider.Percolation.cubeAt (k + 1) 0 ∧
              ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
                (Percolation.pathSites N (pathExtend p)) omega : ℕ) : ℝ) <
                (3 : ℝ) / 4 * (3 : ℝ) ^ k} =
        {omega : Cutoff.CutoffSample d |
          ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
            (Percolation.pathSites N (pathExtend p)) omega : ℕ) : ℝ) <
            (3 : ℝ) / 4 * (3 : ℝ) ^ k} := by
      ext omega
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => h.2.2.2, fun h => ⟨hgeom.1, hgeom.2.1, hgeom.2.2, h⟩⟩
    rw [hset]
    exact measurableSet_lt hcount measurable_const
  · have hset : {omega : Cutoff.CutoffSample d |
        Provider.Percolation.IsLatticePath (pathExtend p) N ∧
          pathExtend p 0 ∈ Provider.Percolation.cubeAt k 0 ∧
            pathExtend p N ∉ Provider.Percolation.cubeAt (k + 1) 0 ∧
              ((qSiteCount M Creg Cinj (m - (k : ℤ)) ep
                (Percolation.pathSites N (pathExtend p)) omega : ℕ) : ℝ) <
                (3 : ℝ) / 4 * (3 : ℝ) ^ k} = (∅ : Set (Cutoff.CutoffSample d)) := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hgeom ⟨h.1, h.2.1, h.2.2.1⟩
    rw [hset]
    exact MeasurableSet.empty

theorem measurableSet_eventuallyHeavyPaths (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ)
    (ep : ℝ) (hq : ∀ (n : ℤ) (z : Vec d), MeasurableSet (qEvent M Creg Cinj n z ep)) :
    MeasurableSet (eventuallyHeavyPaths M Creg Cinj m ep) := by
  have hE : ∀ k, MeasurableSet (lightQPathEvent M Creg Cinj m ep k) :=
    measurableSet_lightQPathEvent M Creg Cinj m ep hq
  have hrw : eventuallyHeavyPaths M Creg Cinj m ep =
      ⋃ N : ℕ, ⋂ k : ℕ, ⋂ _ : N ≤ k, (lightQPathEvent M Creg Cinj m ep k)ᶜ := by
    ext omega
    simp [eventuallyHeavyPaths]
  rw [hrw]
  exact MeasurableSet.iUnion fun _ =>
    MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hE k).compl

private theorem measurableSet_le_percolationScaleTotal (M : ABKModel d) (Creg Cinj : ℝ)
    (m : ℤ) (ep : ℝ)
    (hq : ∀ (n : ℤ) (z : Vec d), MeasurableSet (qEvent M Creg Cinj n z ep)) (N : ℕ) :
    MeasurableSet {omega | N ≤ percolationScaleTotal M Creg Cinj m ep omega} := by
  have hE : ∀ k, MeasurableSet (lightQPathEvent M Creg Cinj m ep k) :=
    measurableSet_lightQPathEvent M Creg Cinj m ep hq
  have hA := measurableSet_eventuallyHeavyPaths M Creg Cinj m ep hq
  have hrw : {omega | N ≤ percolationScaleTotal M Creg Cinj m ep omega} =
      (eventuallyHeavyPaths M Creg Cinj m ep ∩
          ⋂ j : ℕ, ⋂ _ : j < N, ⋃ k : ℕ, ⋃ _ : j ≤ k,
            lightQPathEvent M Creg Cinj m ep k) ∪
        ((eventuallyHeavyPaths M Creg Cinj m ep)ᶜ ∩ {_omega | N ≤ 0}) := by
    ext omega
    by_cases hA' : omega ∈ eventuallyHeavyPaths M Creg Cinj m ep
    · have hiff := le_percolationScaleTotal_iff M Creg Cinj m ep hA' N
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_iInter, Set.mem_iUnion, hA', true_and, not_true, false_and, or_false]
      rw [hiff]
      refine forall_congr' fun j => ?_
      refine forall_congr' fun _ => ?_
      constructor
      · intro h
        push Not at h
        obtain ⟨kk, hk1, hk2⟩ := h
        exact ⟨kk, hk1, hk2⟩
      · rintro ⟨kk, hk1, hk2⟩ hcon
        exact hcon kk hk1 hk2
    · have hzero := percolationScaleTotal_eq_zero_of_not M Creg Cinj m ep hA'
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        hA', false_and, false_or, not_false_eq_true, true_and, hzero]
  rw [hrw]
  refine MeasurableSet.union (hA.inter ?_) (hA.compl.inter (MeasurableSet.const _))
  exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hE k

/-- **The percolation scale is measurable.**  This is a disclosed strengthening
of the source, which asks only that `Y_m` be a random variable. -/
theorem measurable_percolationScaleTotal (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    (hq : ∀ (n : ℤ) (z : Vec d), MeasurableSet (qEvent M Creg Cinj n z ep)) :
    Measurable (percolationScaleTotal M Creg Cinj m ep) := by
  refine measurable_to_countable' fun N => ?_
  have h1 := measurableSet_le_percolationScaleTotal M Creg Cinj m ep hq N
  have h2 := measurableSet_le_percolationScaleTotal M Creg Cinj m ep hq (N + 1)
  have hrw : (percolationScaleTotal M Creg Cinj m ep) ⁻¹' {N} =
      {omega | N ≤ percolationScaleTotal M Creg Cinj m ep omega} \
        {omega | N + 1 ≤ percolationScaleTotal M Creg Cinj m ep omega} := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    omega
  rw [hrw]
  exact h1.diff h2

end

end Algsuperdiff.Section5.Support
