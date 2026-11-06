/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof
public import LeanPool.RareSubtreePatterns.Bridge.WalkCalculus

/-!
# Tightness of the actual maximum of the walk's partial sums

The maximum here is evaluated on a single product-law walk path, rather than a maximum of
marginal probabilities. An Ottaviani first-exit decomposition and fresh-increment independence
upgrade the scalar tightness derived from `(H_α)` to maximal tightness. This is a consequence
of the functional convergence asserted at source lines 846–850, not a proof of that full
Skorokhod-topology convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace PoissonDeclumping.Stable

open Lukasiewicz

/-- A finite prefix first crosses the absolute threshold at its final position. -/
def FirstExit (R : ℝ) (x : List ℤ) : Prop :=
  R < |(x.sum : ℝ)| ∧ ∀ j : ℕ, j < x.length → |((x.take j).sum : ℝ)| ≤ R

private theorem exists_firstExit {x : List ℤ} {m : ℕ} (hm : m ≤ x.length) {R : ℝ}
    (h : ∃ k : ℕ, k ≤ m ∧ R < |((x.take k).sum : ℝ)|) :
    ∃ k : ℕ, k ≤ m ∧ FirstExit R (x.take k) := by
  classical
  let k := Nat.find h
  have hk : k ≤ m ∧ R < |((x.take k).sum : ℝ)| := Nat.find_spec h
  refine ⟨k, hk.1, hk.2, ?_⟩
  intro j hj
  have hlen : (x.take k).length = k := List.length_take_of_le (hk.1.trans hm)
  rw [hlen] at hj
  rw [List.take_take, min_eq_left hj.le]
  by_contra hbad
  have hj' : ∃ k' : ℕ, k' ≤ m ∧ R < |((x.take k').sum : ℝ)| := h
  have hkj : k ≤ j := Nat.find_min' h ⟨hj.le.trans hk.1, lt_of_not_ge hbad⟩
  omega

private theorem firstExit_prefix_disjoint {x : List ℤ} {i j : ℕ}
    (hi : i ≤ x.length) (hj : j ≤ x.length) (hij : i ≠ j) {R : ℝ}
    (hEi : FirstExit R (x.take i)) (hEj : FirstExit R (x.take j)) : False := by
  have aux (i j : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length) (hij : i < j)
      (hEi : FirstExit R (x.take i)) (hEj : FirstExit R (x.take j)) : False := by
    have hb := hEj.2 i (by rw [List.length_take_of_le hj]; exact hij)
    rw [List.take_take, min_eq_left hij.le] at hb
    exact (not_lt_of_ge hb) hEi.1
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact aux i j hi hj hij hEi hEj
  · exact aux j i hj hi hji hEj hEi

/-- Ottaviani's bound for the actual partial-sum maximum. The fresh remainder is within `R`
with probability at least `1/2`, uniformly over every possible first-exit time. -/
theorem maximal_le_two_mul_tail (μ : PMF ℕ) (m : ℕ) (R : ℝ)
    (hsafe : ∀ j : ℕ, j ≤ m → (1 / 2 : ℝ) ≤
      (walkLaw μ j).real {z : ℤ | |(z : ℝ)| ≤ R}) :
    (walkVecLaw μ m).real {ω | ∃ k : ℕ, k ≤ m ∧
      2 * R < |(((List.ofFn ω).take k).sum : ℝ)|} ≤
      2 * (walkLaw μ m).real {z : ℤ | R < |(z : ℝ)|} := by
  classical
  let E : ℕ → Set (Fin m → ℤ) := fun k =>
    {ω | FirstExit (2 * R) ((List.ofFn ω).take k)}
  let F : ℕ → Set (Fin m → ℤ) := fun k =>
    {ω | FirstExit (2 * R) ((List.ofFn ω).take k) ∧
      |(((List.ofFn ω).drop k).sum : ℝ)| ≤ R}
  have hdisjE : PairwiseDisjoint (↑(Finset.range (m + 1))) E := by
    intro i hi j hj hij
    refine disjoint_left.2 fun ω hωi hωj => ?_
    exact firstExit_prefix_disjoint
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hij hωi hωj
  have hdisjF : PairwiseDisjoint (↑(Finset.range (m + 1))) F := by
    intro i hi j hj hij
    exact (hdisjE hi hj hij).mono (fun _ h => h.1) (fun _ h => h.1)
  have hsub : {ω : Fin m → ℤ | ∃ k : ℕ, k ≤ m ∧
      2 * R < |(((List.ofFn ω).take k).sum : ℝ)|} ⊆ ⋃ k ∈ Finset.range (m + 1), E k := by
    intro ω hω
    obtain ⟨k, hkm, hk⟩ := exists_firstExit (by simp : m ≤ (List.ofFn ω).length) hω
    exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨Finset.mem_range.mpr (by omega), hk⟩⟩
  have hmul (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
      (walkVecLaw μ m).real (E k) ≤ 2 * (walkVecLaw μ m).real (F k) := by
    have hkm : k ≤ m := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hE : (walkVecLaw μ m).real (E k) =
        (walkVecLaw μ k).real {ω | FirstExit (2 * R) (List.ofFn ω)} := by
      unfold Measure.real
      rw [show E k = {ω | FirstExit (2 * R) ((List.ofFn ω).take k)} from rfl,
        Bridge.walkVecLaw_take μ hkm]
    have hF : (walkVecLaw μ m).real (F k) =
        (walkVecLaw μ k).real {ω | FirstExit (2 * R) (List.ofFn ω)} *
          (walkLaw μ (m - k)).real {z : ℤ | |(z : ℝ)| ≤ R} := by
      rw [measureReal_def, show F k = {ω | FirstExit (2 * R) ((List.ofFn ω).take k) ∧
        |(((List.ofFn ω).drop k).sum : ℝ)| ≤ R} from rfl,
        Bridge.walkVecLaw_take_inter_drop μ hkm (FirstExit (2 * R))
          (fun x => |(x.sum : ℝ)| ≤ R), ENNReal.toReal_mul]
      simp only [List.sum_ofFn, measureReal_def, walkLaw_apply]
      rfl
    rw [hE, hF]
    have h := hsafe (m - k) (Nat.sub_le _ _)
    have hnon : 0 ≤ (walkVecLaw μ k).real {ω | FirstExit (2 * R) (List.ofFn ω)} :=
      measureReal_nonneg
    nlinarith
  have hFsub : (⋃ k ∈ Finset.range (m + 1), F k) ⊆
      {ω : Fin m → ℤ | R < |((∑ i, ω i : ℤ) : ℝ)|} := by
    intro ω hω
    obtain ⟨k, hω⟩ := mem_iUnion.1 hω
    obtain ⟨hk, hE, htail⟩ := mem_iUnion.1 hω
    have heq : (((List.ofFn ω).take k).sum : ℝ) +
        (((List.ofFn ω).drop k).sum : ℝ) = ((∑ i, ω i : ℤ) : ℝ) := by
      rw [← Int.cast_add, ← List.sum_append, List.take_append_drop, List.sum_ofFn]
    have hab := abs_add_le (((∑ i, ω i : ℤ) : ℝ)) (-(((List.ofFn ω).drop k).sum : ℝ))
    simp only [abs_neg, ← sub_eq_add_neg] at hab
    rw [show ((∑ i, ω i : ℤ) : ℝ) - (((List.ofFn ω).drop k).sum : ℝ) =
      (((List.ofFn ω).take k).sum : ℝ) by linarith] at hab
    change R < |((∑ i, ω i : ℤ) : ℝ)|
    have hexit : 2 * R < |(((List.ofFn ω).take k).sum : ℝ)| := hE.1
    linarith
  calc (walkVecLaw μ m).real _ ≤ (walkVecLaw μ m).real (⋃ k ∈ Finset.range (m + 1), E k) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ = ∑ k ∈ Finset.range (m + 1), (walkVecLaw μ m).real (E k) :=
      measureReal_biUnion_finset hdisjE (fun _ _ => (Set.to_countable _).measurableSet)
        (fun _ _ => measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range (m + 1), 2 * (walkVecLaw μ m).real (F k) :=
      Finset.sum_le_sum hmul
    _ = 2 * (walkVecLaw μ m).real (⋃ k ∈ Finset.range (m + 1), F k) := by
      rw [measureReal_biUnion_finset hdisjF
        (fun _ _ => (Set.to_countable _).measurableSet) (fun _ _ => measure_ne_top _ _),
          Finset.mul_sum]
    _ ≤ 2 * (walkVecLaw μ m).real {ω | R < |((∑ i, ω i : ℤ) : ℝ)|} := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hFsub (measure_ne_top _ _)) (by norm_num)
    _ = 2 * (walkLaw μ m).real {z : ℤ | R < |(z : ℝ)|} := by
      rw [measureReal_def, measureReal_def, walkLaw_apply]
      rfl

/-- **Actual maximal tightness** of the Łukasiewicz walk: all partial sums are evaluated
on the same product-law path. The constant is uniform over every positive path length. -/
theorem maximal_tight {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ α a) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m →
      (walkVecLaw μ m).real {ω | ∃ k : ℕ, k ≤ m ∧
        K * a m < |(((List.ofFn ω).take k).sum : ℝ)|} ≤ ε := by
  let η : ℝ := min (ε / 2) (1 / 2)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  obtain ⟨K₀, hK₀⟩ := tight h hη
  let K : ℝ := max 1 K₀
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨2 * K, by positivity, fun m hm => ?_⟩
  have hR : 0 < K * a m := mul_pos hK (h.pos m hm)
  have htail (j : ℕ) (hj : j ≤ m) :
      (walkLaw μ j).real {z : ℤ | K * a m < |(z : ℝ)|} ≤ η := by
    by_cases hj0 : j = 0
    · subst j
      simp only [walkLaw, measureReal_def]
      have hz : (0 : ℤ) ∉ {z : ℤ | K * a m < |(z : ℝ)|} := by simpa using hR.le
      rw [Measure.dirac_apply, Set.indicator_of_notMem hz, ENNReal.toReal_zero]
      exact hη.le
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
      have hb : K₀ * a j ≤ K * a m :=
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (h.pos j hj1).le).trans
          (mul_le_mul_of_nonneg_left (h.monotone hj) hK.le)
      exact (measureReal_mono (fun z hz => hb.trans_lt hz) (measure_ne_top _ _)).trans (hK₀ j hj1)
  have hsafe (j : ℕ) (hj : j ≤ m) :
      (1 / 2 : ℝ) ≤ (walkLaw μ j).real {z : ℤ | |(z : ℝ)| ≤ K * a m} := by
    have he : {z : ℤ | |(z : ℝ)| ≤ K * a m} =
        {z : ℤ | K * a m < |(z : ℝ)|}ᶜ := by ext z; simp
    rw [he, measureReal_compl (Set.to_countable _).measurableSet, probReal_univ]
    have hh := htail j hj
    have hηhalf : η ≤ 1 / 2 := min_le_right _ _
    linarith
  have hmax := maximal_le_two_mul_tail μ m (K * a m) hsafe
  have hmax' : (walkVecLaw μ m).real {ω | ∃ k : ℕ, k ≤ m ∧
      (2 * K) * a m < |(((List.ofFn ω).take k).sum : ℝ)|} ≤
      2 * (walkLaw μ m).real {z : ℤ | K * a m < |(z : ℝ)|} := by
    simpa only [mul_assoc] using hmax
  refine hmax'.trans ?_
  have ht := htail m le_rfl
  have hηε : η ≤ ε / 2 := min_le_left _ _
  linarith

/-- Maxima stay below any radius that diverges relative to the normalizing scale. This
strengthens the marginal-probability consequence used at source lines 1763–1770 and 1912. -/
theorem tendsto_maximal_tail {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ α a) {M : ℕ → ℕ} {r : ℕ → ℝ}
    (hM : ∀ᶠ n : ℕ in atTop, 1 ≤ M n)
    (hr : Tendsto (fun n => r n / a (M n)) atTop atTop) :
    Tendsto (fun n => (walkVecLaw μ (M n)).real {ω | ∃ k : ℕ, k ≤ M n ∧
      r n < |(((List.ofFn ω).take k).sum : ℝ)|}) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro x hx
    exact Eventually.of_forall fun _ => hx.trans_le measureReal_nonneg
  · intro x hx
    obtain ⟨K, hK, htail⟩ := maximal_tight h (half_pos hx)
    filter_upwards [hM, hr.eventually_ge_atTop K] with n hn hrn
    have hb : K * a (M n) ≤ r n := (le_div_iff₀ (h.pos _ hn)).1 hrn
    have hsub : {ω : Fin (M n) → ℤ | ∃ k : ℕ, k ≤ M n ∧
        r n < |(((List.ofFn ω).take k).sum : ℝ)|} ⊆
        {ω : Fin (M n) → ℤ | ∃ k : ℕ, k ≤ M n ∧
          K * a (M n) < |(((List.ofFn ω).take k).sum : ℝ)|} := by
      rintro ω ⟨k, hk, hr⟩
      exact ⟨k, hk, hb.trans_lt hr⟩
    exact ((measureReal_mono hsub (measure_ne_top _ _)).trans (htail _ hn)).trans_lt (half_lt_self
      hx)

end PoissonDeclumping.Stable
