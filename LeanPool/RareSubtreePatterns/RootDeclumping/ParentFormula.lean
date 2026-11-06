/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bienayme.Normalization
public import LeanPool.RareSubtreePatterns.LeafHeight.Recursion
public import Mathlib.Analysis.Normed.Group.Tannery


/-!
# The root-declumping parent formula

Section 5.1 of the paper (source lines 2148–2229; inventory P15 and Lemma
`lem:root_declumping`(i),(ii)). For a critical offspring law `μ` with `μ_1 ≠ 1`, a set
`B ⊆ ℕ` and a mark `G`, write `π = P(G(𝒯) = 1)` and `π̂ = P(Ghat(𝒯) = 1)` for the declumped
mark `Ghat = declumpedMark B G` (root degree in `B` and some marked child).

* `parent_formula` (`eq:parent_formula`): by the branching property,
  `π̂ = E[1{D ∈ B}(1 - (1 - π)^D)] = F_B(π)`, `F_B(p) = ∑_{j ∈ B} μ_j (1 - (1 - p)^j)`;
  more generally `bienayme_real_rootDegree_mem_forall_exists` computes
  `P(k_∅ ∈ B, all children in A', some child in A)` for `A ⊆ A'`.
* `pointwise_bounds`: `p ≤ 1 - (1 - p)^d ≤ d p` for `d ≥ 1`, `p ∈ [0, 1]`; hence
  `bB_mul_le_declumped`, `declumped_le_cBReal_mul`: `b_B π ≤ π̂ ≤ c_B π`, with
  `b_B = P(D ∈ B, D ≥ 1)` (`bB_eq_prob`) and `c_B = ∑_{j ∈ B} j μ_j`; `b_B > 0 ↔ c_B > 0`.
* `tendsto_slopeFun`, `tendsto_parentFun_div`, `parentFun_sub_isLittleO`: the derivative of
  `F_B` at zero is `c_B`, by dominated convergence with the summable dominating sequence
  `j μ_j 1{j ∈ B}` (finite first moment only; no second moment is assumed).
* `root_declumping_bounded`, `root_declumping_divergent`: Lemma `lem:root_declumping`(i),(ii)
  along an arbitrary filter and an arbitrary scale `x → ∞`.

Part (iii) of Lemma `lem:root_declumping` needs forest and local-limit estimates and is not
proved here.
-/

@[expose] public section

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal

namespace PoissonDeclumping
namespace RootDeclumping

open PlaneTree LeafHeight

variable {μ : PMF ℕ}

/-- `P(k_∅ ∈ B, all children in A) = ∑_{d ∈ B} μ_d P(A)^d` (real form). -/
theorem bienayme_real_rootDegree_mem_forall (μ : PMF ℕ) (B : Set ℕ) (A : Set PlaneTree) :
    (bienayme μ).real {T | T.rootDegree ∈ B ∧ ∀ U ∈ T.children, U ∈ A} =
      ∑' d, B.indicator (fun d => mass μ d * (bienayme μ).real A ^ d) d := by
  have h := bienayme_eq_tsum_of_mem_iff μ {T | T.rootDegree ∈ B ∧ ∀ U ∈ T.children, U ∈ A} B
    (fun _ _ => A) (fun k f => by simp [List.mem_ofFn])
  have hfin : ∀ d, B.indicator (fun d => μ d * bienayme μ A ^ d) d ≠ ∞ := by
    intro d
    by_cases hd : d ∈ B
    · rw [Set.indicator_of_mem hd]
      exact ENNReal.mul_ne_top (μ.apply_ne_top d) (ENNReal.pow_ne_top (measure_ne_top _ _))
    · rw [Set.indicator_of_notMem hd]
      exact ENNReal.zero_ne_top
  have hprod : ∀ d, (∏ _i : Fin d, bienayme μ A) = bienayme μ A ^ d := fun d => by simp
  simp only [hprod] at h
  rw [measureReal_def, h, ENNReal.tsum_toReal_eq hfin]
  refine tsum_congr fun d => ?_
  by_cases hd : d ∈ B
  · simp [Set.indicator_of_mem hd, ENNReal.toReal_mul, ENNReal.toReal_pow, mass, measureReal_def]
  · simp [Set.indicator_of_notMem hd]


/-- Summability of `d ↦ 1_B(d) μ_d f(d)` for bounded `f`. -/
theorem summable_indicator_mass_mul (B : Set ℕ) {f : ℕ → ℝ} (h0 : ∀ d, 0 ≤ f d)
    (h1 : ∀ d, f d ≤ 1) : Summable (fun d => B.indicator (fun d => mass μ d * f d) d) := by
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) (summable_mass (μ := μ))
  · by_cases hd : d ∈ B
    · rw [Set.indicator_of_mem hd]; exact mul_nonneg (mass_nonneg d) (h0 d)
    · rw [Set.indicator_of_notMem hd]
  · by_cases hd : d ∈ B
    · rw [Set.indicator_of_mem hd]; exact mul_le_of_le_one_right (mass_nonneg d) (h1 d)
    · rw [Set.indicator_of_notMem hd]; exact mass_nonneg d

/-- General parent formula: for `A ⊆ A'`,
`P(k_∅ ∈ B, all children in A', some child in A) = ∑_{d ∈ B} μ_d (P(A')^d - P(A' \ A)^d)`. -/
theorem bienayme_real_rootDegree_mem_forall_exists (μ : PMF ℕ) (B : Set ℕ)
    {A A' : Set PlaneTree} (hAA' : A ⊆ A') :
    (bienayme μ).real {T | T.rootDegree ∈ B ∧ (∀ U ∈ T.children, U ∈ A') ∧
        ∃ U ∈ T.children, U ∈ A} =
      ∑' d, B.indicator (fun d => mass μ d *
        ((bienayme μ).real A' ^ d - ((bienayme μ).real A' - (bienayme μ).real A) ^ d)) d := by
  set P := bienayme μ
  have hsplit : {T : PlaneTree | T.rootDegree ∈ B ∧ (∀ U ∈ T.children, U ∈ A') ∧
        ∃ U ∈ T.children, U ∈ A} =
      {T | T.rootDegree ∈ B ∧ ∀ U ∈ T.children, U ∈ A'} \
        {T | T.rootDegree ∈ B ∧ ∀ U ∈ T.children, U ∈ A' \ A} := by
    ext T
    constructor
    · rintro ⟨hB, hA', U, hU, hUA⟩
      exact ⟨⟨hB, hA'⟩, fun h => (h.2 U hU).2 hUA⟩
    · rintro ⟨⟨hB, hA'⟩, h⟩
      refine ⟨hB, hA', ?_⟩
      by_contra hc
      push Not at hc
      exact h ⟨hB, fun U hU => ⟨hA' U hU, hc U hU⟩⟩
  have hsub : {T : PlaneTree | T.rootDegree ∈ B ∧ ∀ U ∈ T.children, U ∈ A' \ A} ⊆
      {T | T.rootDegree ∈ B ∧ ∀ U ∈ T.children, U ∈ A'} :=
    fun T hT => ⟨hT.1, fun U hU => (hT.2 U hU).1⟩
  have hdiff : P.real (A' \ A) = P.real A' - P.real A :=
    measureReal_sdiff hAA' (DiscreteMeasurableSpace.forall_measurableSet _)
  have hA'0 : 0 ≤ P.real A' := measureReal_nonneg
  have hA'1 : P.real A' ≤ 1 := by
    calc P.real A' ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ 1 := by
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using bienayme_univ_le_one μ)
  have hd0 : 0 ≤ P.real (A' \ A) := measureReal_nonneg
  have hd1 : P.real (A' \ A) ≤ 1 :=
    (measureReal_mono Set.sdiff_subset).trans hA'1
  rw [hsplit, measureReal_sdiff hsub (DiscreteMeasurableSpace.forall_measurableSet _),
    bienayme_real_rootDegree_mem_forall, bienayme_real_rootDegree_mem_forall, hdiff.symm,
    ← (summable_indicator_mass_mul B (fun d => pow_nonneg hA'0 d)
      (fun d => pow_le_one₀ hA'0 hA'1)).tsum_sub
      (summable_indicator_mass_mul B (fun d => pow_nonneg hd0 d)
        (fun d => pow_le_one₀ hd0 hd1))]
  refine tsum_congr fun d => ?_
  by_cases hd : d ∈ B
  · simp only [Set.indicator_of_mem hd]; ring
  · simp only [Set.indicator_of_notMem hd, sub_zero]

/-- The function `F_B(p) = ∑_{j ∈ B} μ_j (1 - (1 - p)^j)` of the parent formula
`eq:parent_formula`. -/
noncomputable def parentFun (μ : PMF ℕ) (B : Set ℕ) (p : ℝ) : ℝ :=
  ∑' j, B.indicator (fun j => mass μ j * (1 - (1 - p) ^ j)) j

/-- **Parent formula** `eq:parent_formula` (source lines 2219–2224, inventory P15): for a
critical `μ` with `μ_1 ≠ 1`, any `B ⊆ ℕ` and any mark `G`, with `π = P(G(𝒯) = 1)` and
`Ghat = declumpedMark B G`, `P(Ghat(𝒯) = 1) = E[1{D ∈ B}(1 - (1 - π)^D)] = ∑_{j ∈ B} μ_j
(1-(1-π)^j)`. -/
theorem parent_formula (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (B : Set ℕ) (G : PlaneTree → Prop) :
    (bienayme μ).real {T | declumpedMark B G T} =
      parentFun μ B ((bienayme μ).real {T | G T}) := by
  have h := bienayme_real_rootDegree_mem_forall_exists μ B (Set.subset_univ {T | G T})
  have hu : (bienayme μ).real Set.univ = 1 := by
    rw [measureReal_def, bienayme_univ hc h1, ENNReal.toReal_one]
  simp only [Set.mem_univ, implies_true, true_and, hu, one_pow] at h
  rw [parentFun, ← h]
  rfl


/-! ### Pointwise bounds and the constants `b_B`, `c_B` -/

/-- `0 ≤ 1 - (1 - p)^d` for `p ∈ [0, 1]`. -/
theorem one_sub_one_sub_pow_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (d : ℕ) :
    0 ≤ 1 - (1 - p) ^ d := by
  have := pow_le_one₀ (by linarith : 0 ≤ 1 - p) (by linarith : 1 - p ≤ 1) (n := d)
  linarith

/-- `p ≤ 1 - (1 - p)^d` for `d ≥ 1` and `p ∈ [0, 1]` (source line 2225). -/
theorem le_one_sub_one_sub_pow {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    p ≤ 1 - (1 - p) ^ d := by
  have := pow_le_of_le_one (by linarith : 0 ≤ 1 - p) (by linarith) (by omega : d ≠ 0)
  linarith

/-- `1 - (1 - p)^d ≤ d p` for `p ≤ 1` (Bernoulli; source line 2225). -/
theorem one_sub_one_sub_pow_le {p : ℝ} (hp1 : p ≤ 1) (d : ℕ) : 1 - (1 - p) ^ d ≤ d * p := by
  have h := one_add_mul_le_pow (a := -p) (by linarith) d
  rw [← sub_eq_add_neg] at h
  linarith

/-- The pointwise bounds `p ≤ 1 - (1 - p)^d ≤ d p` for `d ≥ 1`, `p ∈ [0, 1]`. -/
theorem pointwise_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {d : ℕ} (hd : 1 ≤ d) :
    p ≤ 1 - (1 - p) ^ d ∧ 1 - (1 - p) ^ d ≤ d * p :=
  ⟨le_one_sub_one_sub_pow hp0 hp1 hd, one_sub_one_sub_pow_le hp1 d⟩

/-- `1 - (1 - p)^d = p ∑_{i < d} (1 - p)^i`. -/
theorem one_sub_one_sub_pow_eq (p : ℝ) (d : ℕ) :
    1 - (1 - p) ^ d = p * ∑ i ∈ Finset.range d, (1 - p) ^ i := by
  have := geom_sum_mul (1 - p) d
  linear_combination this

/-- `0 ≤ ∑_{i < d} (1 - p)^i ≤ d` for `p ∈ [0, 1]`. -/
theorem geom_sum_one_sub_bounds {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (d : ℕ) :
    0 ≤ ∑ i ∈ Finset.range d, (1 - p) ^ i ∧ ∑ i ∈ Finset.range d, (1 - p) ^ i ≤ d := by
  refine ⟨Finset.sum_nonneg fun i _ => pow_nonneg (by linarith) i, ?_⟩
  calc ∑ i ∈ Finset.range d, (1 - p) ^ i ≤ ∑ _i ∈ Finset.range d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => pow_le_one₀ (by linarith) (by linarith)
    _ = d := by simp

variable (μ) in
/-- The constant `c_B = E[k_∅(𝒯) 1{k_∅(𝒯) ∈ B}] = ∑_{j ∈ B} j μ_j`, in real numbers. -/
noncomputable def cBReal (B : Set ℕ) : ℝ := ∑' j, B.indicator (fun j => (j : ℝ) * mass μ j) j

variable (μ) in
/-- The constant `b_B = P(k_∅(𝒯) ∈ B, k_∅(𝒯) ≥ 1) = ∑_{j ∈ B, j ≥ 1} μ_j`. -/
noncomputable def bB (B : Set ℕ) : ℝ := ∑' j, {j | j ∈ B ∧ 1 ≤ j}.indicator (mass μ) j

theorem summable_cB (hc : IsCritical μ) (B : Set ℕ) :
    Summable (fun j => B.indicator (fun j => (j : ℝ) * mass μ j) j) :=
  (hasSum_mean hc).summable.indicator B

theorem summable_bB (B : Set ℕ) : Summable (fun j => {j | j ∈ B ∧ 1 ≤ j}.indicator (mass μ) j) :=
  summable_mass.indicator _

theorem cBReal_nonneg (B : Set ℕ) : 0 ≤ cBReal μ B :=
  tsum_nonneg fun j => Set.indicator_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg j)
    (mass_nonneg j)) j

theorem bB_nonneg (B : Set ℕ) : 0 ≤ bB μ B :=
  tsum_nonneg fun j => Set.indicator_nonneg (fun j _ => mass_nonneg j) j

/-- `b_B ≤ c_B` (critical `μ`). -/
theorem bB_le_cBReal (hc : IsCritical μ) (B : Set ℕ) : bB μ B ≤ cBReal μ B := by
  refine (summable_bB B).tsum_le_tsum (fun j => ?_) (summable_cB hc B)
  by_cases hj : j ∈ B ∧ 1 ≤ j
  · rw [Set.indicator_of_mem (s := {j : ℕ | j ∈ B ∧ 1 ≤ j}) hj, Set.indicator_of_mem hj.1]
    exact le_mul_of_one_le_left (mass_nonneg j) (by exact_mod_cast hj.2)
  · rw [Set.indicator_of_notMem (s := {j : ℕ | j ∈ B ∧ 1 ≤ j}) hj]
    exact Set.indicator_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg j) (mass_nonneg j)) j

/-- `c_B ≤ 1` (critical `μ`). -/
theorem cBReal_le_one (hc : IsCritical μ) (B : Set ℕ) : cBReal μ B ≤ 1 := by
  rw [← (hasSum_mean hc).tsum_eq]
  refine (summable_cB hc B).tsum_le_tsum (fun j => ?_) (hasSum_mean hc).summable
  by_cases hj : j ∈ B
  · rw [Set.indicator_of_mem hj]
  · rw [Set.indicator_of_notMem hj]
    exact mul_nonneg (Nat.cast_nonneg j) (mass_nonneg j)

/-- `b_B > 0` if and only if `c_B > 0`: both say that `μ` charges some `j ∈ B` with `j ≥ 1`. -/
theorem bB_pos_iff_cBReal_pos (hc : IsCritical μ) (B : Set ℕ) :
    0 < bB μ B ↔ 0 < cBReal μ B := by
  constructor
  · intro h
    exact h.trans_le (bB_le_cBReal hc B)
  · intro h
    obtain ⟨j, hj⟩ : ∃ j, 0 < B.indicator (fun j => (j : ℝ) * mass μ j) j := by
      by_contra hne
      push Not at hne
      have : cBReal μ B ≤ 0 := tsum_nonpos hne
      linarith
    have hjB : j ∈ B := by
      by_contra hjB
      rw [Set.indicator_of_notMem hjB] at hj
      exact lt_irrefl _ hj
    rw [Set.indicator_of_mem hjB] at hj
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · simp at hj
      · exact h
    have hm : 0 < mass μ j := pos_of_mul_pos_right hj (Nat.cast_nonneg j)
    refine (summable_bB B).tsum_pos (fun i => Set.indicator_nonneg (fun i _ => mass_nonneg i) i)
      j ?_
    rwa [Set.indicator_of_mem (s := {j : ℕ | j ∈ B ∧ 1 ≤ j}) ⟨hjB, hj1⟩]

/-- `π ↦ F_B(π)` vanishes at zero. -/
@[simp] theorem parentFun_zero (B : Set ℕ) : parentFun μ B 0 = 0 := by
  simp [parentFun]

theorem parentFun_nonneg (B : Set ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ parentFun μ B p :=
  tsum_nonneg fun j => Set.indicator_nonneg (fun j _ => mul_nonneg (mass_nonneg j)
    (one_sub_one_sub_pow_nonneg hp0 hp1 j)) j

/-- Lower bound `b_B π ≤ F_B(π)` (source line 2226). -/
theorem bB_mul_le_parentFun (B : Set ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bB μ B * p ≤ parentFun μ B p := by
  rw [bB, ← tsum_mul_right]
  refine ((summable_bB B).mul_right p).tsum_le_tsum (fun j => ?_)
    (summable_indicator_mass_mul B (one_sub_one_sub_pow_nonneg hp0 hp1)
      (fun d => by have := pow_nonneg (by linarith : 0 ≤ 1 - p) d; linarith))
  by_cases hj : j ∈ B ∧ 1 ≤ j
  · rw [Set.indicator_of_mem (s := {j : ℕ | j ∈ B ∧ 1 ≤ j}) hj, Set.indicator_of_mem hj.1]
    exact mul_le_mul_of_nonneg_left (le_one_sub_one_sub_pow hp0 hp1 hj.2) (mass_nonneg j)
  · rw [Set.indicator_of_notMem (s := {j : ℕ | j ∈ B ∧ 1 ≤ j}) hj, zero_mul]
    exact Set.indicator_nonneg (fun j _ => mul_nonneg (mass_nonneg j)
      (one_sub_one_sub_pow_nonneg hp0 hp1 j)) j

/-- Upper bound `F_B(π) ≤ c_B π` (source line 2226). -/
theorem parentFun_le_cBReal_mul (hc : IsCritical μ) (B : Set ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : parentFun μ B p ≤ cBReal μ B * p := by
  rw [cBReal, ← tsum_mul_right]
  refine (summable_indicator_mass_mul B (one_sub_one_sub_pow_nonneg hp0 hp1)
      (fun d => by have := pow_nonneg (by linarith : 0 ≤ 1 - p) d; linarith)).tsum_le_tsum
    (fun j => ?_) ((summable_cB hc B).mul_right p)
  by_cases hj : j ∈ B
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj]
    calc mass μ j * (1 - (1 - p) ^ j) ≤ mass μ j * (j * p) :=
          mul_le_mul_of_nonneg_left (one_sub_one_sub_pow_le hp1 j) (mass_nonneg j)
      _ = j * mass μ j * p := by ring
  · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem hj, zero_mul]

/-! ### Derivative at zero, by dominated convergence (finite first moment only) -/

variable (μ) in
/-- `ψ_B(p) = ∑_{j ∈ B} μ_j ∑_{i < j} (1 - p)^i`, so that `F_B(p) = p ψ_B(p)` and
`ψ_B(0) = c_B`. -/
noncomputable def slopeFun (B : Set ℕ) (p : ℝ) : ℝ :=
  ∑' j, B.indicator (fun j => mass μ j * ∑ i ∈ Finset.range j, (1 - p) ^ i) j

theorem parentFun_eq_mul_slopeFun (hc : IsCritical μ) (B : Set ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : parentFun μ B p = p * slopeFun μ B p := by
  have hs : Summable (fun j => B.indicator
      (fun j => mass μ j * ∑ i ∈ Finset.range j, (1 - p) ^ i) j) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (summable_cB hc B)
    · exact Set.indicator_nonneg (fun j _ => mul_nonneg (mass_nonneg j)
        (geom_sum_one_sub_bounds hp0 hp1 j).1) j
    · by_cases hj : j ∈ B
      · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj, mul_comm (j : ℝ)]
        exact mul_le_mul_of_nonneg_left (geom_sum_one_sub_bounds hp0 hp1 j).2 (mass_nonneg j)
      · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem hj]
  rw [slopeFun, ← hs.tsum_mul_left, parentFun]
  refine tsum_congr fun j => ?_
  by_cases hj : j ∈ B
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj, one_sub_one_sub_pow_eq]
    ring
  · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem hj, mul_zero]

theorem slopeFun_zero (B : Set ℕ) : slopeFun μ B 0 = cBReal μ B := by
  refine tsum_congr fun j => ?_
  by_cases hj : j ∈ B
  · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj]
    simp [mul_comm]
  · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem hj]

/-- Dominated convergence (source lines 2226–2228), with the dominating sequence
`j μ_j 1{j ∈ B}`, which is summable by criticality (finite first moment); no second moment is
used: `ψ_B(p) → c_B` as `p ↓ 0`. -/
theorem tendsto_slopeFun (hc : IsCritical μ) (B : Set ℕ) :
    Tendsto (slopeFun μ B) (𝓝[≥] 0) (𝓝 (cBReal μ B)) := by
  rw [← slopeFun_zero (μ := μ) B]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j =>
      B.indicator (fun j => (j : ℝ) * mass μ j) j) (summable_cB hc B) (fun j => ?_) ?_
  · refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto ?_ 0)
    by_cases hj : j ∈ B
    · simp only [Set.indicator_of_mem hj]
      fun_prop
    · simp only [Set.indicator_of_notMem hj]
      exact continuous_const
  · filter_upwards [Ico_mem_nhdsGE (by norm_num : (0 : ℝ) < 1)] with p hp j
    have hp0 := hp.1
    have hp1 := hp.2.le
    by_cases hj : j ∈ B
    · rw [Set.indicator_of_mem hj, Set.indicator_of_mem hj, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mass_nonneg j) (geom_sum_one_sub_bounds hp0 hp1 j).1),
        mul_comm (j : ℝ)]
      exact mul_le_mul_of_nonneg_left (geom_sum_one_sub_bounds hp0 hp1 j).2 (mass_nonneg j)
    · rw [Set.indicator_of_notMem hj, Set.indicator_of_notMem hj, norm_zero]

/-- `F_B(π) / π → c_B` as `π ↓ 0` (source lines 2226–2228). -/
theorem tendsto_parentFun_div (hc : IsCritical μ) (B : Set ℕ) :
    Tendsto (fun p => parentFun μ B p / p) (𝓝[>] 0) (𝓝 (cBReal μ B)) := by
  refine ((tendsto_slopeFun hc B).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)).congr'
    ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with p hp
  rw [parentFun_eq_mul_slopeFun hc B hp.1.le hp.2.le, mul_div_cancel_left₀ _ hp.1.ne']

/-- `F_B(π) - c_B π = o(π)` as `π ↓ 0`, including `π = 0`. -/
theorem parentFun_sub_isLittleO (hc : IsCritical μ) (B : Set ℕ) :
    (fun p => parentFun μ B p - cBReal μ B * p) =o[𝓝[≥] 0] fun p => p := by
  have h : (fun p => slopeFun μ B p - cBReal μ B) =o[𝓝[≥] 0] (fun _ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    simpa using (tendsto_slopeFun hc B).sub_const (cBReal μ B)
  refine ((isBigO_refl (fun p : ℝ => p) _).mul_isLittleO h).congr' ?_ (by simp)
  filter_upwards [Ico_mem_nhdsGE (by norm_num : (0 : ℝ) < 1)] with p hp
  rw [parentFun_eq_mul_slopeFun hc B hp.1 hp.2.le]
  ring


/-! ### Probabilistic form: `b_B π ≤ π̂ ≤ c_B π` and Lemma `lem:root_declumping`(i),(ii) -/

/-- `b_B = P(k_∅(𝒯) ∈ B, k_∅(𝒯) ≥ 1)`. -/
theorem bB_eq_prob (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (B : Set ℕ) :
    bB μ B = (bienayme μ).real {T | T.rootDegree ∈ B ∧ 1 ≤ T.rootDegree} := by
  have h := bienayme_real_rootDegree_mem_forall μ {j | j ∈ B ∧ 1 ≤ j} Set.univ
  have hu : (bienayme μ).real Set.univ = 1 := by
    rw [measureReal_def, bienayme_univ hc h1, ENNReal.toReal_one]
  have hs : {T : PlaneTree | T.rootDegree ∈ {j | j ∈ B ∧ 1 ≤ j} ∧
      ∀ U ∈ T.children, U ∈ (Set.univ : Set PlaneTree)} =
      {T | T.rootDegree ∈ B ∧ 1 ≤ T.rootDegree} := by
    ext T; simp
  rw [hs, hu] at h
  simp only [one_pow, mul_one] at h
  rw [h, bB]

/-- `π̂ ≥ b_B π` (source line 2210): `P(Ghat(𝒯) = 1) ≥ b_B P(G(𝒯) = 1)`. -/
theorem bB_mul_le_declumped (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (B : Set ℕ)
    (G : PlaneTree → Prop) :
    bB μ B * (bienayme μ).real {T | G T} ≤ (bienayme μ).real {T | declumpedMark B G T} := by
  rw [parent_formula hc h1]
  have := bienayme_isProbabilityMeasure hc h1
  exact bB_mul_le_parentFun B measureReal_nonneg measureReal_le_one

/-- `π̂ ≤ c_B π` (source line 2226). -/
theorem declumped_le_cBReal_mul (hc : IsCritical μ) (h1 : μ 1 ≠ 1) (B : Set ℕ)
    (G : PlaneTree → Prop) :
    (bienayme μ).real {T | declumpedMark B G T} ≤ cBReal μ B * (bienayme μ).real {T | G T} := by
  rw [parent_formula hc h1]
  have := bienayme_isProbabilityMeasure hc h1
  exact parentFun_le_cBReal_mul hc B measureReal_nonneg measureReal_le_one

/-- **Lemma `lem:root_declumping`(i)** (source lines 2206–2207, 2226–2229), for an arbitrary
filter `l` and scale `x → ∞` (the paper: `x = n → ∞` along admissible sizes): if the raw mean
`x π` is eventually bounded, then `x π̂ - c_B x π → 0`. Only criticality (finite first moment)
is used; no second moment. -/
theorem root_declumping_bounded {ι : Type*} {l : Filter ι} (hc : IsCritical μ) (h1 : μ 1 ≠ 1)
    (B : Set ℕ) (G : ι → PlaneTree → Prop) (x : ι → ℝ) (hx : Tendsto x l atTop)
    (hbdd : ∃ C : ℝ, ∀ᶠ i in l, x i * (bienayme μ).real {T | G i T} ≤ C) :
    Tendsto (fun i => x i * (bienayme μ).real {T | declumpedMark B (G i) T} -
      cBReal μ B * (x i * (bienayme μ).real {T | G i T})) l (𝓝 0) := by
  have := bienayme_isProbabilityMeasure hc h1
  obtain ⟨C, hC⟩ := hbdd
  set π : ι → ℝ := fun i => (bienayme μ).real {T | G i T} with hπ
  have hπ0 : ∀ i, 0 ≤ π i := fun i => measureReal_nonneg
  have hπ1 : ∀ i, π i ≤ 1 := fun i => measureReal_le_one
  have hxpos : ∀ᶠ i in l, 0 < x i := hx.eventually_gt_atTop 0
  -- `π → 0` within `[0, ∞)`.
  have hπlim : Tendsto π l (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun i => hπ0 i⟩
    refine squeeze_zero' (Eventually.of_forall hπ0) ?_ ((tendsto_const_nhds (x := C)).div_atTop hx)
    filter_upwards [hC, hxpos] with i hi hxi
    rw [le_div_iff₀ hxi, mul_comm]
    exact hi
  have hslope : Tendsto (fun i => slopeFun μ B (π i) - cBReal μ B) l (𝓝 0) := by
    simpa using ((tendsto_slopeFun hc B).comp hπlim).sub_const (cBReal μ B)
  have hbound : IsBoundedUnder (· ≤ ·) l ((‖·‖) ∘ fun i => x i * π i) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hC, hxpos] with i hi hxi
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hxi.le (hπ0 i))]
    exact hi
  refine (isBoundedUnder_le_mul_tendsto_zero hbound hslope).congr fun i => ?_
  simp only [hπ, parent_formula hc h1]
  rw [parentFun_eq_mul_slopeFun hc B (hπ0 i) (hπ1 i)]
  ring

/-- **Lemma `lem:root_declumping`(ii)** (source line 2208), for an arbitrary filter: if
`b_B > 0` and the raw mean `x π` diverges, then the declumped mean `x π̂` diverges. -/
theorem root_declumping_divergent {ι : Type*} {l : Filter ι} (hc : IsCritical μ)
    (h1 : μ 1 ≠ 1) (B : Set ℕ) (hb : 0 < bB μ B) (G : ι → PlaneTree → Prop) (x : ι → ℝ)
    (hdiv : Tendsto (fun i => x i * (bienayme μ).real {T | G i T}) l atTop) :
    Tendsto (fun i => x i * (bienayme μ).real {T | declumpedMark B (G i) T}) l atTop := by
  have := bienayme_isProbabilityMeasure hc h1
  refine tendsto_atTop_mono' l ?_ (hdiv.const_mul_atTop hb)
  filter_upwards [hdiv.eventually_gt_atTop 0] with i hi
  have hπ0 : 0 ≤ (bienayme μ).real {T | G i T} := measureReal_nonneg
  have hxi : 0 < x i := pos_of_mul_pos_left hi hπ0
  calc bB μ B * (x i * (bienayme μ).real {T | G i T}) =
        x i * (bB μ B * (bienayme μ).real {T | G i T}) := by ring
    _ ≤ x i * (bienayme μ).real {T | declumpedMark B (G i) T} :=
        mul_le_mul_of_nonneg_left (bB_mul_le_declumped hc h1 B (G i)) hxi.le

end RootDeclumping
end PoissonDeclumping
