/-
Copyright (c) 2026 Gabriel Larotonda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Larotonda
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public import LeanPool.LCAnalysis.FundamentalTheorem

/-!
# Mackey completeness through Lipschitz curves

Glöckner–Neeb (Definition 1.1.17) call a curve `γ : [a, b] → E` *Lipschitz* if its difference
quotients `(γ s - γ t) / (s - t)` form a bounded set, and call `E` *Mackey complete* if every
Lipschitz curve has a weak integral. This file proves that this agrees with `MackeyComplete`,
defined through Mackey–Cauchy sequences (Glöckner–Neeb, Remark 1.1.18(e); Kriegl–Michor, 2.2 and
2.14):

* `MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve`: if Mackey–Cauchy sequences
  converge, Lipschitz curves have weak integrals (the dyadic Riemann sums of a Lipschitz curve
  form a Mackey–Cauchy sequence);
* `MackeyComplete.of_integratesLipschitzCurves`: conversely, if Lipschitz curves have weak
  integrals, Mackey–Cauchy sequences converge. Given a Mackey–Cauchy sequence `u`, we pass to a
  fast subsequence `u (n j)` and place the increments `u (n (j + 1)) - u (n j)` on tents supported
  on the intervals `[1 - 2⁻ʲ, 1 - 2⁻ʲ⁻¹]`. The resulting curve is Lipschitz on `[0, 1]`, and its
  weak integral is `lim u (n j) - u (n 0)`.
* `mackeyComplete_iff_integratesLipschitzCurves`: the equivalence.
-/

@[expose] public section

open Set Filter Function
open scoped Topology Pointwise

noncomputable section

namespace LCAnalysis

universe v

variable {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {γ : ℝ → F} {a b : ℝ}

/-- The difference quotients of `γ` on `[a, b]`. -/
def diffQuot (γ : ℝ → F) (a b : ℝ) : Set F :=
  {v | ∃ s ∈ Icc a b, ∃ t ∈ Icc a b, s ≠ t ∧ v = (s - t)⁻¹ • (γ s - γ t)}

/-- A Lipschitz curve on `[a, b]` (Glöckner–Neeb, Definition 1.1.17(a)): its difference quotients
form a bounded set. -/
def IsLipschitzCurve (γ : ℝ → F) (a b : ℝ) : Prop :=
  Bornology.IsVonNBounded ℝ (diffQuot γ a b)

/-- Mackey completeness in the sense of Glöckner–Neeb, Definition 1.1.17(b): Lipschitz curves
have weak integrals. -/
def IntegratesLipschitzCurves (F : Type v) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] :
    Prop :=
  ∀ (γ : ℝ → F) (a b : ℝ), a < b → IsLipschitzCurve γ a b → ∃ y, HasWeakIntegral γ a b y

omit [TopologicalSpace F] in
theorem sub_eq_smul_diffQuot {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≠ t) :
    ∃ q ∈ diffQuot γ a b, γ s - γ t = (s - t) • q :=
  ⟨(s - t)⁻¹ • (γ s - γ t), ⟨s, hs, t, ht, hst, rfl⟩,
    (smul_inv_smul₀ (sub_ne_zero.mpr hst) _).symm⟩

section Lipschitz

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [ContinuousSMul ℝ F] in
/-- Lipschitz curves are continuous. -/
theorem IsLipschitzCurve.continuousOn (h : IsLipschitzCurve γ a b) :
    ContinuousOn γ (Icc a b) := by
  intro t ht
  rw [ContinuousWithinAt, ← tendsto_sub_nhds_zero_iff]
  intro W hW
  rw [Filter.mem_map]
  have hev : ∀ᶠ c in 𝓝 (0 : ℝ), MapsTo (c • ·) (diffQuot γ a b) W :=
    (h hW).eventually_nhds_zero (mem_of_mem_nhds hW)
  have hlim : Tendsto (fun s : ℝ ↦ s - t) (𝓝[Icc a b] t) (𝓝 0) := by
    have : Tendsto (fun s : ℝ ↦ s - t) (𝓝 t) (𝓝 (t - t)) := tendsto_id.sub tendsto_const_nhds
    simpa using this.mono_left (nhdsWithin_le_nhds (s := Icc a b))
  filter_upwards [hlim.eventually hev, self_mem_nhdsWithin] with s hs hsI
  change γ s - γ t ∈ W
  rcases eq_or_ne s t with rfl | hne
  · rw [sub_self]; exact mem_of_mem_nhds hW
  · obtain ⟨q, hq, he⟩ := sub_eq_smul_diffQuot (γ := γ) hsI ht hne
    rw [he]
    exact hs hq

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [TopologicalSpace F] in
/-- Increments of a curve over steps of length at most `h` lie in `h • convexHull (insert 0 D)`,
where `D` is the set of difference quotients. -/
theorem sub_mem_smul_convexHull_diffQuot {h : ℝ} (hh : 0 < h) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (hts : t ≤ s) (hst : s - t ≤ h) :
    γ s - γ t ∈ h • convexHull ℝ (insert 0 (diffQuot γ a b)) := by
  have h0 : (0 : F) ∈ convexHull ℝ (insert 0 (diffQuot γ a b)) :=
    subset_convexHull ℝ _ (mem_insert _ _)
  rcases eq_or_ne s t with rfl | hne
  · rw [sub_self]; exact ⟨0, h0, smul_zero h⟩
  obtain ⟨q, hq, he⟩ := sub_eq_smul_diffQuot (γ := γ) hs ht hne
  have hmem : ((s - t) / h) • q ∈ convexHull ℝ (insert 0 (diffQuot γ a b)) :=
    (convex_convexHull ℝ _).smul_mem_of_zero_mem h0
      (subset_convexHull ℝ _ (mem_insert_of_mem _ hq))
      ⟨div_nonneg (sub_nonneg.mpr hts) hh.le, (div_le_one hh).mpr hst⟩
  convert smul_mem_smul_set (a := h) hmem using 1
  rw [he, smul_smul, mul_div_cancel₀ _ hh.ne']

variable [LocallyConvexSpace ℝ F] [T2Space F]

omit [T2Space F] in
/-- In a Mackey complete space, Lipschitz curves have weak integrals. -/
theorem MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve [MackeyComplete F]
    (hab : a < b) (hγ : IsLipschitzCurve γ a b) : ∃ y, HasWeakIntegral γ a b y := by
  set K := convexHull ℝ (insert 0 (diffQuot γ a b))
  have hK : Bornology.IsVonNBounded ℝ K := isVonNBounded_convexHull (hγ.insert 0)
  have hr : Tendsto (fun k : ℕ ↦ (b - a) * ((b - a) / 2 ^ k)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))))
  obtain ⟨y, hy⟩ := MackeyComplete.exists_tendsto (fun k : ℕ ↦ riemannSum γ a b (2 ^ k)) _ _ hK hr
    fun k l hkl ↦ by
      have hpow : (2 : ℕ) ^ l = 2 ^ k * 2 ^ (l - k) := by rw [← pow_add]; congr 1; omega
      have hk : (0 : ℝ) < (b - a) / 2 ^ k := div_pos (by linarith) (by positivity)
      have hmem := riemannSum_mul_sub_mem (γ := γ) hab.le (N := 2 ^ k) (m := 2 ^ (l - k))
        (by positivity) (by positivity) ((convex_convexHull ℝ _).smul ((b - a) / 2 ^ k))
        fun s hs t ht hts hst ↦ sub_mem_smul_convexHull_diffQuot hk hs ht hts
          (by push_cast at hst; exact hst)
      simp only [hpow]
      rwa [smul_smul] at hmem
  exact ⟨y, hasWeakIntegral_of_tendsto hab.le hγ.continuousOn hy⟩

omit [T2Space F] in
theorem MackeyComplete.integratesLipschitzCurves [MackeyComplete F] :
    IntegratesLipschitzCurves F :=
  fun _ _ _ hab hγ ↦ MackeyComplete.exists_hasWeakIntegral_of_isLipschitzCurve hab hγ

end Lipschitz

/-! ### Tents -/

/-- Left endpoint `1 - 2⁻ʲ` of the `j`-th interval. -/
def tentLeft (j : ℕ) : ℝ := 1 - (1 / 2) ^ j

/-- Width `2⁻ʲ⁻¹` of the `j`-th interval. -/
def tentWidth (j : ℕ) : ℝ := (1 / 2) ^ (j + 1)

/-- The tent of height `tentWidth j / 2` on `[tentLeft j, tentLeft (j + 1)]`. -/
def tent (j : ℕ) (t : ℝ) : ℝ := max 0 (tentWidth j / 2 - |t - (tentLeft j + tentWidth j / 2)|)

theorem tentLeft_succ (j : ℕ) : tentLeft (j + 1) = tentLeft j + tentWidth j := by
  simp only [tentLeft, tentWidth, pow_succ]; ring

theorem tentWidth_pos (j : ℕ) : 0 < tentWidth j := by unfold tentWidth; positivity

theorem tentWidth_le (j : ℕ) : tentWidth j ≤ 1 / 2 := by
  unfold tentWidth
  calc (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (by omega)
    _ = 1 / 2 := pow_one _

theorem tentLeft_mono : Monotone tentLeft := fun i j hij ↦ by
  unfold tentLeft
  linarith [pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hij]

theorem tentLeft_nonneg (j : ℕ) : 0 ≤ tentLeft j := by
  unfold tentLeft; linarith [pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (n := j)]

theorem tentLeft_lt_one (j : ℕ) : tentLeft j < 1 := by
  unfold tentLeft; linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) j]

theorem tent_nonneg (j : ℕ) (t : ℝ) : 0 ≤ tent j t := le_max_left _ _

theorem tent_le_one (j : ℕ) (t : ℝ) : tent j t ≤ 1 := by
  have h1 := abs_nonneg (t - (tentLeft j + tentWidth j / 2))
  have h2 := tentWidth_le j
  exact max_le zero_le_one (by linarith)

theorem tent_eq_zero_of_le {j : ℕ} {t : ℝ} (ht : t ≤ tentLeft j) : tent j t = 0 :=
  max_eq_left (by linarith [neg_le_abs (t - (tentLeft j + tentWidth j / 2))])

theorem tent_eq_zero_of_ge {j : ℕ} {t : ℝ} (ht : tentLeft (j + 1) ≤ t) : tent j t = 0 := by
  rw [tentLeft_succ] at ht
  exact max_eq_left (by linarith [le_abs_self (t - (tentLeft j + tentWidth j / 2))])

theorem abs_tent_sub_le (j : ℕ) (s t : ℝ) : |tent j s - tent j t| ≤ |s - t| := by
  set m := tentLeft j + tentWidth j / 2
  calc |tent j s - tent j t|
      ≤ |(tentWidth j / 2 - |s - m|) - (tentWidth j / 2 - |t - m|)| := by
        rw [tent, tent, max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ = abs (|t - m| - |s - m|) := by ring_nf
    _ ≤ |(t - m) - (s - m)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |s - t| := by rw [abs_sub_comm]; ring_nf

theorem tent_eq_left {j : ℕ} {t : ℝ} (ht : t ∈ Icc (tentLeft j) (tentLeft j + tentWidth j / 2)) :
    tent j t = t - tentLeft j := by
  rw [tent, abs_of_nonpos (by linarith [ht.2]), max_eq_right (by linarith [ht.1])]
  ring

theorem tent_eq_right {j : ℕ} {t : ℝ}
    (ht : t ∈ Icc (tentLeft j + tentWidth j / 2) (tentLeft j + tentWidth j)) :
    tent j t = tentLeft j + tentWidth j - t := by
  rw [tent, abs_of_nonneg (by linarith [ht.1]), max_eq_right (by linarith [ht.2])]
  ring

theorem continuous_tent (j : ℕ) : Continuous (tent j) :=
  continuous_const.max (continuous_const.sub ((continuous_id.sub continuous_const).abs))

theorem integral_tent (j : ℕ) : ∫ t in (0 : ℝ)..1, tent j t = tentWidth j ^ 2 / 4 := by
  have hw : 0 < tentWidth j := tentWidth_pos j
  have h0l : 0 ≤ tentLeft j := tentLeft_nonneg j
  set l := tentLeft j
  set w := tentWidth j
  set m := l + w / 2 with hm
  have hr1 : l + w ≤ 1 := by rw [← tentLeft_succ]; exact (tentLeft_lt_one _).le
  have ii : ∀ x y : ℝ, IntervalIntegrable (tent j) MeasureTheory.volume x y :=
    fun x y ↦ (continuous_tent j).intervalIntegrable x y
  have e1 : ∫ t in (0 : ℝ)..l, tent j t = 0 := by
    have : EqOn (tent j) (fun _ ↦ 0) (uIcc 0 l) := fun t ht ↦ by
      rw [uIcc_of_le h0l] at ht; exact tent_eq_zero_of_le ht.2
    rw [intervalIntegral.integral_congr this]; simp
  have e4 : ∫ t in (l + w)..1, tent j t = 0 := by
    have : EqOn (tent j) (fun _ ↦ 0) (uIcc (l + w) 1) := fun t ht ↦ by
      rw [uIcc_of_le hr1] at ht
      exact tent_eq_zero_of_ge (by rw [tentLeft_succ]; exact ht.1)
    rw [intervalIntegral.integral_congr this]; simp
  have e2 : ∫ t in l..m, tent j t = w ^ 2 / 8 := by
    have : EqOn (tent j) (fun t ↦ t - l) (uIcc l m) := fun t ht ↦ by
      rw [uIcc_of_le (by rw [hm]; linarith)] at ht
      exact tent_eq_left ht
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_comp_sub_right
      (fun x ↦ x), integral_id]
    rw [hm]; ring
  have e3 : ∫ t in m..(l + w), tent j t = w ^ 2 / 8 := by
    have : EqOn (tent j) (fun t ↦ (l + w) - t) (uIcc m (l + w)) := fun t ht ↦ by
      rw [uIcc_of_le (by rw [hm]; linarith)] at ht
      exact tent_eq_right ht
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_comp_sub_left
      (fun x ↦ x), integral_id]
    rw [hm]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (ii 0 l) (ii l 1),
    ← intervalIntegral.integral_add_adjacent_intervals (ii l m) (ii m 1),
    ← intervalIntegral.integral_add_adjacent_intervals (ii m (l + w)) (ii (l + w) 1),
    e1, e2, e3, e4]
  ring

/-- The partial sums `∑_{j < N} tent j t • e j`. -/
def tentSum (e : ℕ → F) (N : ℕ) (t : ℝ) : F := ∑ j ∈ Finset.range N, tent j t • e j

/-- The curve `∑_j tent j t • e j` (a finite sum for each `t`). -/
def tentCurve (e : ℕ → F) (t : ℝ) : F :=
  open Classical in
  if h : ∃ N, t ≤ tentLeft N then tentSum e (Nat.find h) t else 0

omit [TopologicalSpace F] in
theorem tentSum_stable (e : ℕ → F) {M N : ℕ} (hMN : M ≤ N) {t : ℝ} (ht : t ≤ tentLeft M) :
    tentSum e N t = tentSum e M t := by
  induction N, hMN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [tentSum, Finset.sum_range_succ, ← tentSum, ih,
      tent_eq_zero_of_le (ht.trans (tentLeft_mono hn)), zero_smul, add_zero]

omit [TopologicalSpace F] in
theorem tentSum_eq_zero_of_one_le (e : ℕ → F) (N : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    tentSum e N t = 0 :=
  Finset.sum_eq_zero fun j _ ↦ by
    rw [tent_eq_zero_of_ge ((tentLeft_lt_one _).le.trans ht), zero_smul]

omit [TopologicalSpace F] in
theorem eventually_tentCurve_eq (e : ℕ → F) (t : ℝ) :
    ∀ᶠ N in atTop, tentCurve e t = tentSum e N t := by
  rcases lt_or_ge t 1 with ht | ht
  · obtain ⟨N₀, hN₀⟩ : ∃ N, (1 / 2 : ℝ) ^ N < 1 - t :=
      exists_pow_lt_of_lt_one (by linarith) (by norm_num)
    have h : ∃ N, t ≤ tentLeft N := ⟨N₀, by unfold tentLeft; linarith⟩
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have htN : t ≤ tentLeft N := by
      have : t ≤ tentLeft N₀ := by unfold tentLeft; linarith
      exact this.trans (tentLeft_mono hN)
    rw [tentCurve, dite_eq_left_of_eq_true (eq_true h)]
    exact (tentSum_stable e (Nat.find_min' h htN) (Nat.find_spec h)).symm
  · refine Eventually.of_forall fun N ↦ ?_
    rw [tentSum_eq_zero_of_one_le e N ht, tentCurve]
    split_ifs with h
    · exact tentSum_eq_zero_of_one_le e _ ht
    · rfl

/-! ### Sums in multiples of a convex set -/

section ConvexSums

variable {K : Set F}

omit [TopologicalSpace F] in
theorem smul_mem_smul_of_abs_le (hK : Convex ℝ K) (h0 : (0 : F) ∈ K)
    (hneg : ∀ x ∈ K, -x ∈ K) {x : F} (hx : x ∈ K) {μ c : ℝ} (hμ : |μ| ≤ c) :
    μ • x ∈ c • K := by
  have hc : 0 ≤ c := (abs_nonneg μ).trans hμ
  rcases hc.eq_or_lt with rfl | hc
  · rw [abs_nonpos_iff.mp hμ, zero_smul]; exact zero_mem_smul_set h0
  have hμc : |μ / c| ≤ 1 := by rw [abs_div, abs_of_pos hc, div_le_one hc]; exact hμ
  have hmem : (μ / c) • x ∈ K := by
    rcases le_total 0 (μ / c) with h | h
    · exact hK.smul_mem_of_zero_mem h0 hx ⟨h, (le_abs_self _).trans hμc⟩
    · have := hK.smul_mem_of_zero_mem h0 (hneg x hx) ⟨neg_nonneg.mpr h,
        (neg_le_abs _).trans hμc⟩
      rwa [smul_neg, ← neg_smul, neg_neg] at this
  convert smul_mem_smul_set (a := c) hmem using 1
  rw [smul_smul, mul_div_cancel₀ _ hc.ne']

omit [TopologicalSpace F] in
theorem sum_mem_smul (hK : Convex ℝ K) (h0 : (0 : F) ∈ K) {ι : Type*} (s : Finset ι)
    {x : ι → F} {c : ι → ℝ} (hc : ∀ i ∈ s, 0 ≤ c i) (hx : ∀ i ∈ s, x i ∈ c i • K) :
    ∑ i ∈ s, x i ∈ (∑ i ∈ s, c i) • K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_smul_set (a := (0 : ℝ)) h0
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hK.add_smul (hc i (Finset.mem_insert_self i s))
        (Finset.sum_nonneg fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))]
    exact add_mem_add (hx i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
        fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

omit [TopologicalSpace F] in
theorem mem_smul_of_le (hK : Convex ℝ K) (h0 : (0 : F) ∈ K) {x : F} {c d : ℝ}
    (hx : x ∈ c • K) (hc : 0 ≤ c) (hcd : c ≤ d) : x ∈ d • K := by
  obtain ⟨k, hk, rfl⟩ := hx
  dsimp only
  rcases hc.eq_or_lt with rfl | hc'
  · rw [zero_smul]; exact zero_mem_smul_set h0
  have hd : 0 < d := hc'.trans_le hcd
  have hmem : (c / d) • k ∈ K := hK.smul_mem_of_zero_mem h0 hk
    ⟨div_nonneg hc hd.le, (div_le_one hd).mpr hcd⟩
  convert smul_mem_smul_set (a := d) hmem using 1
  simp only [smul_smul, mul_div_cancel₀ _ hd.ne']

end ConvexSums

theorem sum_Ico_half_pow {N M : ℕ} (h : N ≤ M) :
    ∑ j ∈ Finset.Ico N M, (1 / 2 : ℝ) ^ (j + 1) = (1 / 2) ^ N - (1 / 2) ^ M := by
  induction M, h using Nat.le_induction with
  | base => simp
  | succ M hM ih => rw [Finset.sum_Ico_succ_top hM, ih]; ring

/-! ### Mackey–Cauchy sequences with a convergent subsequence -/

section Converse

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

omit [ContinuousSMul ℝ F] in
/-- A Mackey–Cauchy sequence with a convergent subsequence converges. -/
theorem tendsto_of_mackeyCauchy_of_subseq {u : ℕ → F} {B : Set F} {r : ℕ → ℝ}
    (hB : Bornology.IsVonNBounded ℝ B) (hr : Tendsto r atTop (𝓝 0))
    (hu : ∀ k l, k ≤ l → u l - u k ∈ r k • B) {n : ℕ → ℕ} (hn : StrictMono n) {x : F}
    (hx : Tendsto (fun j ↦ u (n j)) atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) := by
  rw [← tendsto_sub_nhds_zero_iff]
  intro W hW
  rw [Filter.mem_map]
  obtain ⟨V, hV, hVW⟩ := exists_nhds_zero_half hW
  have hV' : V ∩ -V ∈ 𝓝 (0 : F) := inter_mem hV (neg_mem_nhds_zero F hV)
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hr.eventually ((hB hV').eventually_nhds_zero (mem_of_mem_nhds hV')))
  filter_upwards [eventually_ge_atTop K] with k hk
  have h1 : ∀ᶠ j in atTop, u (n j) - x ∈ V := (tendsto_sub_nhds_zero_iff.mpr hx) hV
  have h2 : ∀ᶠ j in atTop, k ≤ n j :=
    (tendsto_atTop_mono hn.id_le tendsto_id).eventually (eventually_ge_atTop k)
  obtain ⟨j, hj1, hj2⟩ := (h1.and h2).exists
  obtain ⟨b, hb, he⟩ := hu k (n j) hj2
  have hmem := hK k hk hb
  simp only at hmem he
  rw [he] at hmem
  have : u k - x = -(u (n j) - u k) + (u (n j) - x) := by abel
  change u k - x ∈ W
  rw [this]
  exact hVW _ hmem.2 _ hj1

variable [LocallyConvexSpace ℝ F] [T2Space F]

omit [T2Space F] in
/-- If Lipschitz curves have weak integrals, then Mackey–Cauchy sequences converge. -/
theorem MackeyComplete.of_integratesLipschitzCurves (h : IntegratesLipschitzCurves F) :
    MackeyComplete F where
  exists_tendsto u B r hB hr hu := by
    -- the absolutely convex hull `K` of `B`
    set K := convexHull ℝ (insert 0 (B ∪ -B))
    have hKc : Convex ℝ K := convex_convexHull ℝ _
    have h0 : (0 : F) ∈ K := subset_convexHull ℝ _ (mem_insert _ _)
    have hBK : B ⊆ K := fun x hx ↦ subset_convexHull ℝ _ (mem_insert_of_mem _ (Or.inl hx))
    have hneg : ∀ x ∈ K, -x ∈ K := fun x hx ↦ by
      have hs : -(insert (0 : F) (B ∪ -B)) = insert 0 (B ∪ -B) := by
        ext y; simp [or_comm]
      have : -x ∈ -K := Set.neg_mem_neg.mpr hx
      rwa [← convexHull_neg, hs] at this
    have hKb : Bornology.IsVonNBounded ℝ K :=
      isVonNBounded_convexHull ((hB.union hB.neg).insert 0)
    -- a fast subsequence
    set c : ℕ → ℝ := fun j ↦ (1 / 2) ^ (j + 1)
    have hc : ∀ j, 0 < c j := fun j ↦ by positivity
    set ε : ℕ → ℝ := fun j ↦ c j * tentWidth j ^ 2 / 4
    have hε : ∀ j, 0 < ε j := fun j ↦ by
      have := tentWidth_pos j; have := hc j; positivity
    obtain ⟨n, hn, hnε⟩ := extraction_forall_of_eventually (P := fun j k ↦ |r k| ≤ ε j)
      fun j ↦ by
        obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hr (ε j) (hε j)
        exact eventually_atTop.mpr ⟨N, fun k hk ↦ by
          have := hN k hk; rw [Real.dist_eq, sub_zero] at this; exact this.le⟩
    -- the increments, rescaled
    set d : ℕ → F := fun j ↦ u (n (j + 1)) - u (n j)
    set e : ℕ → F := fun j ↦ (4 / tentWidth j ^ 2) • d j
    have he : ∀ j, e j ∈ c j • K := fun j ↦ by
      obtain ⟨b, hb, hbe⟩ := hu (n j) (n (j + 1)) (hn (Nat.lt_succ_self j)).le
      have hw := tentWidth_pos j
      have hμ : |4 / tentWidth j ^ 2 * r (n j)| ≤ c j := by
        rw [abs_mul, abs_of_pos (by positivity)]
        calc 4 / tentWidth j ^ 2 * |r (n j)| ≤ 4 / tentWidth j ^ 2 * ε j := by
              gcongr; exact hnε j
          _ = c j := by simp only [ε]; field_simp
      have := smul_mem_smul_of_abs_le hKc h0 hneg (hBK hb) hμ
      simp only [e, d, ← hbe, smul_smul]
      exact this
    set γ := tentCurve e
    have hcont : ∀ N, Continuous (tentSum e N) := fun N ↦
      continuous_finsetSum _ fun j _ ↦ (continuous_tent j).smul continuous_const
    -- `γ` is a Lipschitz curve on `[0, 1]`
    have hdq : diffQuot γ 0 1 ⊆ K := by
      rintro _ ⟨s, -, t, -, hst, rfl⟩
      obtain ⟨N, hNs, hNt⟩ := ((eventually_tentCurve_eq e s).and
        (eventually_tentCurve_eq e t)).exists
      have hst' : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
      have hsum : (s - t)⁻¹ • (γ s - γ t) = ∑ j ∈ Finset.range N,
          ((s - t)⁻¹ * (tent j s - tent j t)) • e j := by
        simp only [γ, hNs, hNt, tentSum, ← Finset.sum_sub_distrib, Finset.smul_sum, ← sub_smul,
          smul_smul]
      rw [hsum]
      have hmem := sum_mem_smul hKc h0 (Finset.range N) (fun j _ ↦ (hc j).le)
        (x := fun j ↦ ((s - t)⁻¹ * (tent j s - tent j t)) • e j) fun j _ ↦ by
          obtain ⟨k, hk, hke⟩ := he j
          rw [← hke, smul_smul]
          refine smul_mem_smul_of_abs_le hKc h0 hneg hk ?_
          rw [abs_mul, abs_mul, abs_of_pos (hc j)]
          refine mul_le_of_le_one_left (hc j).le ?_
          rw [abs_inv, inv_mul_le_one₀ hst']
          exact abs_tent_sub_le j s t
      have hle : ∑ j ∈ Finset.range N, c j ≤ 1 := by
        have := sum_Ico_half_pow (Nat.zero_le N)
        rw [← Finset.range_eq_Ico] at this
        simp only [c, this]
        linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) N]
      simpa using mem_smul_of_le hKc h0 hmem
        (Finset.sum_nonneg fun j _ ↦ (hc j).le) hle
    have hLip : IsLipschitzCurve γ 0 1 := hKb.subset hdq
    obtain ⟨y, hy⟩ := h γ 0 1 zero_lt_one hLip
    have hγc : ContinuousOn γ (Icc 0 1) := hLip.continuousOn
    -- the weak integral of the partial sums is `u (n N) - u (n 0)`
    have hGint : ∀ N, HasWeakIntegral (tentSum e N) 0 1 (u (n N) - u (n 0)) := by
      intro N
      induction N with
      | zero =>
        have : tentSum e 0 = fun _ ↦ 0 := by funext t; simp [tentSum]
        rw [this, sub_self]
        simpa using hasWeakIntegral_const (0 : F) 0 1
      | succ N ih =>
        have hfun : tentSum e (N + 1) = fun t ↦ tentSum e N t + tent N t • e N := by
          funext t; simp only [tentSum, Finset.sum_range_succ]
        have hterm : HasWeakIntegral (fun t ↦ tent N t • e N) 0 1 (d N) := by
          intro φ
          simp only [map_smul, smul_eq_mul]
          rw [intervalIntegral.integral_mul_const, integral_tent]
          have hw := tentWidth_pos N
          simp only [e, map_smul, smul_eq_mul]
          field_simp
        have := ih.add (hcont N).continuousOn
          ((continuous_tent N).smul continuous_const).continuousOn hterm
        rw [hfun]
        convert this using 1
        simp only [d]; abel
    -- the subsequence converges to `u (n 0) + y`
    have hconv : Tendsto (fun N ↦ u (n N)) atTop (𝓝 (u (n 0) + y)) := by
      have hsmall : Tendsto (fun N ↦ y - (u (n N) - u (n 0))) atTop (𝓝 0) := by
        intro W hW
        rw [Filter.mem_map]
        obtain ⟨W', hW', hW'c, hW'conv, hW'W⟩ := exists_closed_convex_two_smul_subset hW
        have hev : ∀ᶠ N in atTop, MapsTo (((1 / 2 : ℝ) ^ N) • ·) K W' :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
            ((hKb hW').eventually_nhds_zero (mem_of_mem_nhds hW'))
        filter_upwards [hev] with N hN
        have hdiff := hy.sub zero_le_one hγc (hcont N).continuousOn (hGint N)
        have hmem := hdiff.mem_smul zero_le_one (hγc.sub (hcont N).continuousOn) hW'conv hW'c
          (mem_of_mem_nhds hW') fun t _ ↦ by
            obtain ⟨M, hM, hNM⟩ := ((eventually_tentCurve_eq e t).and
              (eventually_ge_atTop N)).exists
            have hIco : γ t - tentSum e N t = ∑ j ∈ Finset.Ico N M, tent j t • e j := by
              simp only [γ, hM, tentSum]
              rw [← Finset.sum_range_add_sum_Ico _ hNM, add_sub_cancel_left]
            rw [Pi.sub_apply, hIco]
            have hmem := sum_mem_smul hKc h0 (Finset.Ico N M) (fun j _ ↦ (hc j).le)
              (x := fun j ↦ tent j t • e j) fun j _ ↦ by
                obtain ⟨k, hk, hke⟩ := he j
                rw [← hke, smul_smul]
                refine smul_mem_smul_of_abs_le hKc h0 hneg hk ?_
                rw [abs_mul, abs_of_nonneg (tent_nonneg j t), abs_of_pos (hc j)]
                exact mul_le_of_le_one_left (hc j).le (tent_le_one j t)
            have hle : ∑ j ∈ Finset.Ico N M, c j ≤ (1 / 2) ^ N := by
              simp only [c, sum_Ico_half_pow hNM]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) M]
            obtain ⟨k, hk, hke⟩ := mem_smul_of_le hKc h0 hmem
              (Finset.sum_nonneg fun j _ ↦ (hc j).le) hle
            rw [← hke]
            exact hN hk
        exact hW'W (by norm_num at hmem ⊢; exact hmem)
      have := (tendsto_const_nhds (x := u (n 0) + y)).sub hsmall
      simp only [sub_zero] at this
      convert this using 2 with N
      abel
    exact ⟨u (n 0) + y, tendsto_of_mackeyCauchy_of_subseq hB hr hu hn hconv⟩

end Converse

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]

omit [T2Space F] in
/-- Mackey completeness through Mackey–Cauchy sequences agrees with the definition of
Glöckner–Neeb (Definition 1.1.17(b)) through Lipschitz curves. -/
theorem mackeyComplete_iff_integratesLipschitzCurves :
    MackeyComplete F ↔ IntegratesLipschitzCurves F :=
  ⟨fun _ ↦ MackeyComplete.integratesLipschitzCurves,
    MackeyComplete.of_integratesLipschitzCurves⟩

end LCAnalysis
