/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.LatticeTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Percolation.Iteration

/-!
# ClusterEventTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Distance-two cluster events and the scale-iteration inequality

`LatticeTwo.lean` supplied the geometry; this module transports the two
probabilistic steps of Step 3 of the proof of `l.percolation.bound.general` to
distance-two paths:

* `measure_iInter_clusterEvent₂_le_pow` — the factorisation of ABK26;
* `measure_clusterEvent₂_add_le` — the iteration inequality
  `e.paths.ready.for.iteration` of ABK26.

## What changes against the proved distance-one layer

Nothing structural.  The abstract σ-algebras `siteSigma` and the scale unions
`scaleUnion` of `ClusterEvent.lean` are *reused verbatim*, so the finite-range
independence hypothesis consumed here is literally the one the proved layer
consumes (`∀ u ∈ S, ∀ v ∈ S', 3 ^ l < latDist u v`).  Two numerical constants
move, both by a dimension-only factor:

* the localisation boxes are `locBox₂`, one triadic generation wider than the
  distance-one boxes, so the union-bound weight is `3 ^ (d (k + h + 2))`
  instead of `3 ^ (d (k + h + 1))` — one extra `3 ^ d`;
* the separation demanded of the extracted sites is `3 ^ (k+1) + 4` rather than
  `3 ^ (k+1) + 2`.

The number `3 ^ (h - 3)` of extracted sites, which is what the induction is
driven by, is unchanged.

## Main definitions

* `clusterEvent₂`: the event `𝒞_k(z)` of ABK26 with distance-two paths.

## Main results

* `clusterEvent₂_eq_loc`, `measurableSet_clusterEvent₂`: localisation.
* `measure_iInter_clusterEvent₂_le_pow`: ABK26.
* `clusterEvent₂_subset_union`, `measure_clusterEvent₂_add_le`: ABK26.

## References

* ABK26, `l.percolation.bound.general`, Step 3.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

open MeasureTheory ProbabilityTheory

variable {d : ℕ} {Ω : Type*}

/-! ### The distance-two cluster events -/

/-- The event `𝒞_k(z)` of ABK26, with the witnessing path allowed distance-two
steps. -/
def clusterEvent₂ (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) (z : Fin d → ℤ) : Set Ω :=
  {ω | ∃ (N : ℕ) (x : ℕ → Fin d → ℤ), x 0 = z ∧ IsLatticePath₂ x N ∧ x N ∉ cubeAt k z ∧
    ∀ i, i ≤ N → ω ∈ scaleUnion B k (x i)}

/-- The localised form of `𝒞_k(z)`, in which the witnessing distance-two path is
additionally required to stay inside `locBox₂ k z`. -/
def clusterEventLoc₂ (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) (z : Fin d → ℤ) : Set Ω :=
  {ω | ∃ (N : ℕ) (x : ℕ → Fin d → ℤ), x 0 = z ∧ IsLatticePath₂ x N ∧ x N ∉ cubeAt k z ∧
    (∀ i, i ≤ N → x i ∈ locBox₂ k z) ∧ ∀ i, i ≤ N → ω ∈ scaleUnion B k (x i)}


/-- Truncating a witnessing distance-two path at its first exit from `z + □_k`
shows that the distance-two cluster event is localised. -/
theorem clusterEvent₂_eq_loc (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ) (z : Fin d → ℤ) :
    clusterEvent₂ B k z = clusterEventLoc₂ B k z := by
  ext ω
  constructor
  · rintro ⟨N, x, h0, hpath, hout, hbad⟩
    obtain ⟨M, hMN, hMout, hloc⟩ := exists_truncated_path₂ h0 hpath hout
    exact ⟨M, x, h0, hpath.mono hMN, hMout,
      fun i hi => mem_locBox₂_of_two_mul_latDist_le (hloc i hi),
      fun i hi => hbad i (le_trans hi hMN)⟩
  · rintro ⟨N, x, h0, hpath, hout, -, hbad⟩
    exact ⟨N, x, h0, hpath, hout, hbad⟩

/-- The localised distance-two cluster event as a countable union of finite
intersections; the description used to establish measurability. -/
theorem clusterEventLoc₂_eq_iUnion (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ)
    (z : Fin d → ℤ) :
    clusterEventLoc₂ B k z =
      ⋃ (N : ℕ), ⋃ (x : Fin (N + 1) → (Fin d → ℤ)),
        ⋃ (_ : extendPath x 0 = z ∧ IsLatticePath₂ (extendPath x) N ∧
            extendPath x N ∉ cubeAt k z ∧ ∀ i : Fin (N + 1), x i ∈ locBox₂ k z),
          ⋂ (i : Fin (N + 1)), scaleUnion B k (x i) := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_iInter]
  constructor
  · rintro ⟨N, x, h0, hpath, hout, hloc, hbad⟩
    refine ⟨N, fun i => x i, ⟨?_, ?_, ?_, ?_⟩, fun i => hbad i (Nat.lt_succ_iff.mp i.isLt)⟩
    · rw [extendPath_apply _ (Nat.zero_le N)]; exact h0
    · intro i hi
      rw [extendPath_apply _ (le_of_lt hi), extendPath_apply _ hi]
      exact hpath i hi
    · rw [extendPath_apply _ (le_refl N)]; exact hout
    · exact fun i => hloc i (Nat.lt_succ_iff.mp i.isLt)
  · rintro ⟨N, x, ⟨h0, hpath, hout, hloc⟩, hbad⟩
    refine ⟨N, extendPath x, h0, hpath, hout, fun i hi => ?_, fun i hi => ?_⟩
    · rw [extendPath_apply _ hi]; exact hloc _
    · rw [extendPath_apply _ hi]; exact hbad _

/-- The distance-two cluster event `𝒞_k(z)` is measurable with respect to the
σ-algebra of the bad events of scale at most `k` at the sites of `locBox₂ k z`.
This is the localisation asserted at ABK26. -/
theorem measurableSet_clusterEvent₂ (B : ℕ → (Fin d → ℤ) → Set Ω) (k : ℕ)
    (z : Fin d → ℤ) :
    MeasurableSet[siteSigma B (↑(locBox₂ k z) : Set (Fin d → ℤ)) k] (clusterEvent₂ B k z) := by
  rw [clusterEvent₂_eq_loc, clusterEventLoc₂_eq_iUnion]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun x =>
    MeasurableSet.iUnion fun hx => MeasurableSet.iInter fun i => ?_
  exact measurableSet_scaleUnion (Finset.mem_coe.mpr (hx.2.2.2 i))

/-! ### The product bound -/

/-- **ABK26, for distance-two paths.**  If the finite-range independence
hypothesis holds at range `3 ^ k` — literally the hypothesis the proved
distance-one layer consumes — and every distance-two cluster event has
probability at most `p`, then for any `M` sites pairwise at sup distance at
least `3 ^ (k + 1) + 4` the probability that all the corresponding cluster
events occur is at most `p ^ M`. -/
theorem measure_iInter_clusterEvent₂_le_pow [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {k : ℕ} {p : ENNReal}
    (hindep : ∀ S S' : Set (Fin d → ℤ), (∀ u ∈ S, ∀ v ∈ S', 3 ^ k < latDist u v) →
      Indep (siteSigma B S k) (siteSigma B S' k) μ)
    (hp : ∀ z : Fin d → ℤ, μ (clusterEvent₂ B k z) ≤ p) :
    ∀ (M : ℕ) (y : ℕ → Fin d → ℤ),
      (∀ a b, a < M → b < M → a ≠ b → 3 ^ (k + 1) + 4 ≤ latDist (y a) (y b)) →
      μ (⋂ m ∈ Set.Iio M, clusterEvent₂ B k (y m)) ≤ p ^ M := by
  intro M
  induction M with
  | zero =>
      intro y _
      have hempty : Set.Iio (0 : ℕ) = ∅ := by ext m; simp
      rw [hempty]
      simp
  | succ M ih =>
      intro y hsep
      have hsplit : (⋂ m ∈ Set.Iio (M + 1), clusterEvent₂ B k (y m))
          = clusterEvent₂ B k (y 0) ∩ ⋂ m ∈ Set.Iio M, clusterEvent₂ B k (y (m + 1)) := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_Iio, Set.mem_inter_iff]
        constructor
        · intro hω
          exact ⟨hω 0 (by omega), fun m hm => hω (m + 1) (by omega)⟩
        · rintro ⟨h0, hrest⟩ m hm
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · exact h0
          · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
            exact hrest j (by omega)
      have hA : MeasurableSet[siteSigma B (↑(locBox₂ k (y 0)) : Set (Fin d → ℤ)) k]
          (clusterEvent₂ B k (y 0)) := measurableSet_clusterEvent₂ B k (y 0)
      have hC : MeasurableSet[siteSigma B
            (⋃ m ∈ Set.Iio M, (↑(locBox₂ k (y (m + 1))) : Set (Fin d → ℤ))) k]
          (⋂ m ∈ Set.Iio M, clusterEvent₂ B k (y (m + 1))) := by
        refine MeasurableSet.biInter (Set.to_countable _) fun m hm => ?_
        exact siteSigma_mono B (fun u hu => Set.mem_biUnion hm hu) k _
          (measurableSet_clusterEvent₂ B k (y (m + 1)))
      have hsep' : ∀ u ∈ (↑(locBox₂ k (y 0)) : Set (Fin d → ℤ)),
          ∀ v ∈ (⋃ m ∈ Set.Iio M, (↑(locBox₂ k (y (m + 1))) : Set (Fin d → ℤ))),
          3 ^ k < latDist u v := by
        intro u hu v hv
        obtain ⟨m, hm, hv⟩ := Set.mem_iUnion₂.mp hv
        exact three_pow_lt_latDist_of_mem_locBox₂
          (hsep 0 (m + 1) (by omega) (by simpa using hm) (by omega))
          (Finset.mem_coe.mp hu) (Finset.mem_coe.mp hv)
      have hprod := (Indep_iff _ _ μ).mp (hindep _ _ hsep') _ _ hA hC
      rw [hsplit, hprod]
      calc μ (clusterEvent₂ B k (y 0)) * μ (⋂ m ∈ Set.Iio M, clusterEvent₂ B k (y (m + 1)))
          ≤ p * p ^ M :=
            mul_le_mul' (hp _)
              (ih _ fun a b ha hb hab =>
                hsep (a + 1) (b + 1) (by omega) (by omega) (by omega))
        _ = p ^ (M + 1) := by rw [pow_succ]; exact mul_comm _ _

/-! ### The scale-iteration inequality -/

/-- **The dichotomy of ABK26, for distance-two paths.**  If `𝒞_{k+h}(z)` occurs
then either there are `3 ^ (h - 3)` sites in `locBox₂ (k + h) z`, pairwise at
sup distance at least `3 ^ (k + 1) + 4`, whose distance-two cluster events at
scale `k` all occur, or some site of `locBox₂ (k + h) z` carries a bad event of
a scale in `[k + 1, k + h]`. -/
theorem clusterEvent₂_subset_union {B : ℕ → (Fin d → ℤ) → Set Ω} {k h : ℕ}
    (hh : 3 ≤ h) (z : Fin d → ℤ) :
    clusterEvent₂ B (k + h) z ⊆
      (⋃ y ∈ Fintype.piFinset fun _ : Fin (3 ^ (h - 3)) => locBox₂ (k + h) z,
        ⋃ (_ : ∀ a b : Fin (3 ^ (h - 3)), a ≠ b →
            3 ^ (k + 1) + 4 ≤ latDist (y a) (y b)),
          ⋂ m ∈ Set.Iio (3 ^ (h - 3)), clusterEvent₂ B k (tupleFun y m))
      ∪ ⋃ z' ∈ locBox₂ (k + h) z, ⋃ l ∈ Finset.Icc (k + 1) (k + h), B l z' := by
  classical
  rintro ω ⟨N, x, h0, hpath, hout, hbad⟩
  obtain ⟨M₀, hM₀N, hM₀out, hM₀loc⟩ := exists_truncated_path₂ h0 hpath hout
  by_cases hcase : ∃ i, i ≤ M₀ ∧ ∃ l, k + 1 ≤ l ∧ l ≤ k + h ∧ ω ∈ B l (x i)
  · obtain ⟨i, hi, l, hl1, hl2, hmem⟩ := hcase
    refine Or.inr (Set.mem_iUnion₂.mpr ⟨x i, ?_, Set.mem_iUnion₂.mpr ⟨l, ?_, hmem⟩⟩)
    · exact mem_locBox₂_of_two_mul_latDist_le (hM₀loc i hi)
    · exact Finset.mem_Icc.mpr ⟨hl1, hl2⟩
  · push Not at hcase
    have hsmall : ∀ i, i ≤ M₀ → ω ∈ scaleUnion B k (x i) := by
      intro i hi
      obtain ⟨L, hL, hmem⟩ := mem_scaleUnion_iff.mp (hbad i (le_trans hi hM₀N))
      refine mem_scaleUnion_iff.mpr ⟨L, ?_, hmem⟩
      by_contra hcon
      exact absurd hmem (hcase i hi L (by omega) (by omega))
    obtain ⟨y, hyloc, hysep, hycluster⟩ :=
      exists_separated_subpaths₂ (P := fun w => ω ∈ scaleUnion B k w) hh h0
        (hpath.mono hM₀N) hM₀out hsmall
    refine Or.inl (Set.mem_iUnion₂.mpr ⟨fun m => y m.val, ?_, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩)
    · exact Fintype.mem_piFinset.mpr fun m => hyloc m.val m.isLt
    · intro a b hab
      exact hysep a.val b.val a.isLt b.isLt fun hcon => hab (Fin.eq_of_val_eq hcon)
    · refine Set.mem_iInter₂.mpr fun m hm => ?_
      have hmlt : m < 3 ^ (h - 3) := hm
      rw [tupleFun_apply _ hmlt]
      obtain ⟨N', x', hx0, hx'path, hx'out, hx'bad⟩ := hycluster m hmlt
      exact ⟨N', x', hx0, hx'path, hx'out, hx'bad⟩

/-- **The iteration inequality `e.paths.ready.for.iteration` of ABK26, for
distance-two paths.**

If every distance-two cluster event at scale `k` has probability at most `p`, and
every bad event `B_l(z)` with `k < l ≤ k + h` has probability at most `q`, then
the distance-two cluster event at scale `k + h` has probability at most
`(W * p) ^ (3 ^ (h - 3)) + W * h * q` with `W = 3 ^ (d * (k + h + 2))`.  The
distance-one layer has the same shape with `W = 3 ^ (d * (k + h + 1))`: the
step size costs exactly one factor `3 ^ d`. -/
theorem measure_clusterEvent₂_add_le [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℕ → (Fin d → ℤ) → Set Ω} {k h : ℕ} {p q : ENNReal} (hh : 3 ≤ h)
    (hindep : ∀ S S' : Set (Fin d → ℤ), (∀ u ∈ S, ∀ v ∈ S', 3 ^ k < latDist u v) →
      Indep (siteSigma B S k) (siteSigma B S' k) μ)
    (hp : ∀ w : Fin d → ℤ, μ (clusterEvent₂ B k w) ≤ p)
    (hq : ∀ (l : ℕ) (w : Fin d → ℤ), k + 1 ≤ l → l ≤ k + h → μ (B l w) ≤ q)
    (z : Fin d → ℤ) :
    μ (clusterEvent₂ B (k + h) z)
      ≤ ((3 : ENNReal) ^ (d * (k + h + 2)) * p) ^ (3 ^ (h - 3))
        + (3 : ENNReal) ^ (d * (k + h + 2)) * h * q := by
  classical
  set M : ℕ := 3 ^ (h - 3) with hM
  set T : Finset (Fin M → Fin d → ℤ) :=
    Fintype.piFinset fun _ : Fin M => locBox₂ (k + h) z with hT
  have hsub := clusterEvent₂_subset_union (B := B) (k := k) (h := h) hh z
  refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) (add_le_add ?_ ?_))
  · refine le_trans (measure_biUnion_finset_le T _) ?_
    have hterm : ∀ y ∈ T,
        μ (⋃ (_ : ∀ a b : Fin M, a ≠ b → 3 ^ (k + 1) + 4 ≤ latDist (y a) (y b)),
            ⋂ m ∈ Set.Iio M, clusterEvent₂ B k (tupleFun y m)) ≤ p ^ M := by
      intro y _
      by_cases hsep : ∀ a b : Fin M, a ≠ b → 3 ^ (k + 1) + 4 ≤ latDist (y a) (y b)
      · refine le_trans (measure_mono (Set.iUnion_subset fun _ => subset_rfl)) ?_
        refine measure_iInter_clusterEvent₂_le_pow hindep hp M (tupleFun y) ?_
        intro a b ha hb hab
        rw [tupleFun_apply _ ha, tupleFun_apply _ hb]
        exact hsep ⟨a, ha⟩ ⟨b, hb⟩ fun hcon => hab (congrArg Fin.val hcon)
      · have hempty : (⋃ (_ : ∀ a b : Fin M, a ≠ b →
            3 ^ (k + 1) + 4 ≤ latDist (y a) (y b)),
              ⋂ m ∈ Set.Iio M, clusterEvent₂ B k (tupleFun y m)) = (∅ : Set Ω) := by
          ext w
          simp [hsep]
        rw [hempty]
        simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_pow]
    refine mul_le_mul' ?_ (le_refl _)
    have hcardT : T.card = (locBox₂ (k + h) z).card ^ M := by
      rw [hT, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hle : T.card ≤ (3 ^ (d * (k + h + 2))) ^ M := by
      rw [hcardT]
      exact Nat.pow_le_pow_left (card_locBox₂_le (k + h) z) M
    exact_mod_cast hle
  · refine le_trans (measure_biUnion_finset_le (locBox₂ (k + h) z) _) ?_
    have hterm : ∀ w ∈ locBox₂ (k + h) z,
        μ (⋃ l ∈ Finset.Icc (k + 1) (k + h), B l w) ≤ (h : ENNReal) * q := by
      intro w _
      calc μ (⋃ l ∈ Finset.Icc (k + 1) (k + h), B l w)
          ≤ ∑ l ∈ Finset.Icc (k + 1) (k + h), μ (B l w) := measure_biUnion_finset_le _ _
        _ ≤ ∑ _l ∈ Finset.Icc (k + 1) (k + h), q :=
            Finset.sum_le_sum fun l hl =>
              hq l w (Finset.mem_Icc.mp hl).1 (Finset.mem_Icc.mp hl).2
        _ = (h : ENNReal) * q := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
              show k + h + 1 - (k + 1) = h from by omega]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    refine mul_le_mul' ?_ (le_refl _)
    exact_mod_cast card_locBox₂_le (k + h) z

end Algsuperdiff.Section3.Provider.Percolation
