/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Setup.Toolkit
public import LeanPool.RareSubtreePatterns.Setup.Marks

import LeanPool.RareSubtreePatterns.Bienayme.Basic
import LeanPool.RareSubtreePatterns.Cyclic.UniformVertex
import LeanPool.RareSubtreePatterns.Cyclic.WalkBridge

/-!
# A criterion for Assumption (M): Lemma `lem:M`

Source lines 1015–1049 (Lemma 3.3 and its proof), 227–233 (Assumption (M)), inventory L3.3,
proof step P02. Notation: `Ψ_m(x) = walkProb μ m x`, `𝒯 ~ bienayme μ`, `𝒯^n_{U_n} ~
uniformFringeLaw μ n`.

Corollary `cor:cyclicshift` (`Cyclic.uniformFringeLaw_real_eq`) gives
`P(H(𝒯^n_{U_n})) = E[1_{H(𝒯)} R_n(|𝒯|)]` with `R_n(m) = Ψ_{n-m}(0) / Ψ_n(-1)`. The proof splits
marked trees at the cutoff:

* small trees (`|𝒯| ≤ m_n = o(n)`): `R_n(m) → 1` uniformly over **compatible** `m` (in the
  periodic case `R_n(m) = 0` at incompatible `m`, correction F4). Compatibility is automatic:
  `P(|𝒯| = m) > 0 → d ∣ m - 1` (`dvd_sub_one_of_admissible`, from `LatticeLocal.support` and
  Dwass), and `𝒯` has an admissible size almost surely (`ae_admissible_vertexCount`). Exports:
  `eventually_abs_walkProb_div_sub_one_le` (the ratio limit) and
  `eventually_abs_uniformFringeLaw_real_sub_le` (`|P(H(𝒯^n_{U_n})) - P(H(𝒯))| ≤ ε P(H(𝒯))`
  uniformly over properties `H` forcing `|T| ≤ m_n`);
* large trees: `R_n(m) ≤ Ψ_n(-1)⁻¹ ≤ a_n / c` (`uniformFringeLaw_real_le`,
  `exists_uniformFringeLaw_real_le_mul`, from `Ψ ≤ 1` and `exists_lower_bound_neg_one`).

`microscopic_of_tail` is Lemma `lem:M` without the hypothesis `π_n > 0`, which the proof does
not need: at `π_n = 0` both sides of the first half of (M) vanish and the conditional
probability of the second half is `0` (`cond` of a null event, correction F13).
`microscopic_of_tail_of_eventually_pos` is the statement with the source's hypothesis.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal

namespace PoissonDeclumping.Bridge

open PlaneTree

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

/-- `𝒯` has an admissible size almost surely. -/
theorem ae_admissible_vertexCount (μ : PMF ℕ) :
    ∀ᵐ T ∂bienayme μ, Admissible μ T.vertexCount := by
  rw [ae_iff]
  have hsub : {T : PlaneTree | ¬Admissible μ T.vertexCount} ⊆
      ⋃ m : ℕ, {T : PlaneTree | ¬Admissible μ m ∧ T.vertexCount = m} :=
    fun T hT => Set.mem_iUnion.2 ⟨T.vertexCount, hT, rfl⟩
  refine measure_mono_null hsub (measure_iUnion_null fun m => ?_)
  by_cases hm : Admissible μ m
  · simp [hm]
  · exact measure_mono_null (fun T hT => hT.2) (nonpos_iff_eq_zero.1 (not_lt.1 hm))

/-- Compatibility of admissible sizes with the lattice: `P(|𝒯| = m) > 0 → d ∣ m - 1`. -/
theorem dvd_sub_one_of_admissible {d : ℕ} {L : ℝ} (hloc : LatticeLocal μ a d L) {m : ℕ}
    (h : Admissible μ m) : (d : ℤ) ∣ (m : ℤ) - 1 := by
  have h1 := hloc.support m (-1) ((walkProb_neg_one_pos_iff μ m).2 h).ne'
  rwa [show (-1 : ℤ) + m = m - 1 by ring] at h1

/-- **Uniform ratio limit over compatible sizes** (TF5 with `x = 0`, `y = -1`, `N n = n`):
for `m_n = o(n)` and `ε > 0`, eventually along admissible sizes,
`|Ψ_{n-j}(0) / Ψ_n(-1) - 1| ≤ ε` for every admissible size `j ≤ m_n`. In the periodic case
the restriction to admissible `j` is necessary (source lines 1033, 965, 1293). -/
theorem eventually_abs_walkProb_div_sub_one_le (hT : StableToolkit μ α a) {m : ℕ → ℕ}
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (n : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ, ∀ j : ℕ, j ≤ m n → Admissible μ j →
      |walkProb μ ((n : ℤ) - j) 0 / walkProb μ n (-1) - 1| ≤ ε := by
  obtain ⟨d, L, hloc⟩ := hT.lattice
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  have hz : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n => a n) := by
    rw [isLittleO_one_left_iff]
    exact tendsto_abs_atTop_atTop.comp hT.tendsto_atTop
  have h := hT.eventually_abs_div_sub_one_le hloc (N := fun n => n) (m := m) tendsto_id hm hz hε
  have hmn : ∀ᶠ n in atTop, m n ≤ n := by
    filter_upwards [hm.bound one_pos] with n hn
    rw [Real.norm_natCast, Real.norm_natCast, one_mul] at hn
    exact_mod_cast hn
  filter_upwards [hl h, hl hmn, hadm] with n hn hmn hadmn j hj hadmj
  have hjn : j ≤ n := hj.trans hmn
  have hdn := dvd_sub_one_of_admissible hloc hadmn
  have hdj := dvd_sub_one_of_admissible hloc hadmj
  have hx : (d : ℤ) ∣ 0 + ((n - j : ℕ) : ℤ) := by
    have := Int.dvd_sub hdn hdj
    rwa [show (n : ℤ) - 1 - ((j : ℤ) - 1) = 0 + ((n - j : ℕ) : ℤ) by push_cast [hjn]; ring]
      at this
  have hy : (d : ℤ) ∣ -1 + (n : ℤ) := by rwa [show (-1 : ℤ) + n = n - 1 by ring]
  have := hn j hj 0 (-1) hx hy (by simp) (by simp)
  rwa [Nat.cast_sub hjn] at this

/-- A bounded real function of a tree is `bienayme μ`-integrable. -/
theorem integrable_bienayme_of_abs_le (μ : PMF ℕ) {f : PlaneTree → ℝ} (C : ℝ)
    (h : ∀ T, |f T| ≤ C) : Integrable f (bienayme μ) :=
  Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable C
    (Eventually.of_forall fun T => by rw [Real.norm_eq_abs]; exact h T)

/-- `P(H(𝒯^n_{U_n})) ≤ Ψ_n(-1)⁻¹ P(H(𝒯))`, for every `n` and every property `H` (from
Corollary `cor:cyclicshift` and `Ψ ≤ 1`; this is the bound `R_n(m) ≤ Ψ_n(-1)⁻¹` of source
line 1034). -/
theorem uniformFringeLaw_real_le (μ : PMF ℕ) (n : ℕ) (H : PlaneTree → Prop) :
    (uniformFringeLaw μ n).real {T | H T} ≤
      (walkProb μ n (-1))⁻¹ * (bienayme μ).real {T | H T} := by
  rw [Cyclic.uniformFringeLaw_real_eq, ← integral_indicator_one MeasurableSet.of_discrete]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (walkProb_nonneg μ _ _))
  refine integral_mono_of_nonneg (Eventually.of_forall fun T => ?_)
    ((integrable_const (1 : ℝ)).indicator MeasurableSet.of_discrete)
    (Eventually.of_forall fun T => ?_)
  · exact Set.indicator_nonneg (fun T _ => walkProb_nonneg μ _ _) T
  · exact Set.indicator_le_indicator (walkProb_le_one μ _ _)

/-- The large-tree bound of source line 1034 with a constant from the toolkit: at every
admissible `n` and for every `H`, `P(H(𝒯^n_{U_n})) ≤ C a_n P(H(𝒯))`. -/
theorem exists_uniformFringeLaw_real_le_mul (hT : StableToolkit μ α a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, Admissible μ n → ∀ H : PlaneTree → Prop,
      (uniformFringeLaw μ n).real {T | H T} ≤ C * a n * (bienayme μ).real {T | H T} := by
  obtain ⟨c, hc, hlow⟩ := hT.exists_lower_bound_neg_one
  refine ⟨1 / c, by positivity, fun n hn H => ?_⟩
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h0 => not_admissible_zero μ (h0 ▸ hn)
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hn
  have han : 0 < a n := hT.pos n hn1
  have hinv : (walkProb μ n (-1))⁻¹ ≤ 1 / c * a n := by
    calc (walkProb μ n (-1))⁻¹ ≤ (c / a n)⁻¹ := inv_anti₀ (by positivity) (hlow n hn1 hψ)
      _ = 1 / c * a n := by rw [inv_div]; ring
  exact (uniformFringeLaw_real_le μ n H).trans
    (mul_le_mul_of_nonneg_right hinv measureReal_nonneg)

/-- **Small fringe trees** (source lines 1031–1034, 965, 1293; P02, first half): for
`m_n = o(n)` and `ε > 0`, eventually along admissible sizes, uniformly over all properties `H`
that force `|T| ≤ m_n`, `|P(H(𝒯^n_{U_n})) - P(H(𝒯))| ≤ ε P(H(𝒯))`. -/
theorem eventually_abs_uniformFringeLaw_real_sub_le (hT : StableToolkit μ α a) {m : ℕ → ℕ}
    (hm : (fun n => (m n : ℝ)) =o[atTop] (fun n => (n : ℝ))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleSizes μ, ∀ H : PlaneTree → Prop, (∀ T, H T → T.vertexCount ≤ m n) →
      |(uniformFringeLaw μ n).real {T | H T} - (bienayme μ).real {T | H T}| ≤
        ε * (bienayme μ).real {T | H T} := by
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  filter_upwards [eventually_abs_walkProb_div_sub_one_le hT hm hε, hadm] with n hn hadmn H hH
  have hψ : 0 < walkProb μ n (-1) := (walkProb_neg_one_pos_iff μ n).2 hadmn
  set ψ := walkProb μ n (-1) with hψdef
  set g : PlaneTree → ℝ := {T | H T}.indicator
    (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) with hg
  set f : PlaneTree → ℝ := {T | H T}.indicator
    (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0 / ψ - 1) with hf
  have hg_int : Integrable g (bienayme μ) := by
    refine integrable_bienayme_of_abs_le μ 1 fun T => ?_
    rw [hg]
    by_cases hT' : T ∈ {T | H T}
    · rw [Set.indicator_of_mem hT', abs_of_nonneg (walkProb_nonneg μ _ _)]
      exact walkProb_le_one μ _ _
    · rw [Set.indicator_of_notMem hT', abs_zero]
      exact zero_le_one
  have h1_int : Integrable ({T | H T}.indicator (1 : PlaneTree → ℝ)) (bienayme μ) :=
    (integrable_const (1 : ℝ)).indicator MeasurableSet.of_discrete
  have key : (uniformFringeLaw μ n).real {T | H T} - (bienayme μ).real {T | H T} =
      ∫ T, f T ∂bienayme μ := by
    rw [Cyclic.uniformFringeLaw_real_eq, ← integral_indicator_one MeasurableSet.of_discrete,
      ← integral_const_mul, ← integral_sub (hg_int.const_mul _) h1_int]
    refine integral_congr_ae (Eventually.of_forall fun T => ?_)
    simp only [hf, hg]
    by_cases hT' : T ∈ {T | H T}
    · rw [Set.indicator_of_mem hT', Set.indicator_of_mem hT', Set.indicator_of_mem hT',
        Pi.one_apply, div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hT', Set.indicator_of_notMem hT',
        Set.indicator_of_notMem hT', mul_zero, sub_zero]
  rw [key, ← Real.norm_eq_abs, ← integral_indicator_one MeasurableSet.of_discrete,
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (h1_int.const_mul _) ?_
  filter_upwards [ae_admissible_vertexCount μ] with T hTadm
  simp only [hf]
  by_cases hT' : T ∈ {T | H T}
  · rw [Set.indicator_of_mem hT', Set.indicator_of_mem hT', Pi.one_apply, mul_one,
      Real.norm_eq_abs]
    exact hn _ (hH T hT') hTadm
  · rw [Set.indicator_of_notMem hT', Set.indicator_of_notMem hT', norm_zero, mul_zero]

/-- Splitting a property of trees at a size cutoff `m`. -/
theorem measureReal_split_vertexCount (ν : Measure PlaneTree) [IsFiniteMeasure ν]
    (H : PlaneTree → Prop) (m : ℕ) :
    ν.real {T | H T} =
      ν.real {T | H T ∧ T.vertexCount ≤ m} + ν.real {T | H T ∧ m < T.vertexCount} := by
  rw [← measureReal_union _ MeasurableSet.of_discrete]
  · congr 1
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases le_or_gt T.vertexCount m with h' | h'
      exacts [Or.inl ⟨h, h'⟩, Or.inr ⟨h, h'⟩]
    · rintro (h | h) <;> exact h.1
  · rw [Set.disjoint_left]
    intro T h1 h2
    exact absurd h2.2 (not_lt.2 h1.2)

/-- `ν(t | s) = ν(s)⁻¹ ν(s ∩ t)` in `ℝ` (both sides vanish when `ν(s) = 0`). -/
theorem cond_real_apply_of_discrete (ν : Measure PlaneTree) (s t : Set PlaneTree) :
    (cond ν s).real t = (ν.real s)⁻¹ * ν.real (s ∩ t) := by
  rw [measureReal_def, cond_apply MeasurableSet.of_discrete, ENNReal.toReal_mul,
    ENNReal.toReal_inv, measureReal_def, measureReal_def]

/-- **Lemma `lem:M`** (source lines 1015–1049), in a slightly stronger form: no positivity of
`π_n` is needed. If `a_n P(|𝒯| > M_n | G_{k_n}(𝒯) = 1) → 0` along admissible sizes, then
Assumption (M) holds. At indices with `π_n = 0` both sides of the first half vanish and the
conditional probability in the second half is `0` (`cond` of a null event). -/
theorem microscopic_of_tail (hT : StableToolkit μ α a) {G : ℕ → PlaneTree → Prop}
    {k M : ℕ → ℕ} (hM : IsCutoff M)
    (h : Tendsto (fun n => a n * (cond (bienayme μ) {T | G (k n) T}).real
      {T | M n < T.vertexCount}) (admissibleSizes μ) (𝓝 0)) :
    Microscopic μ G k M := by
  obtain ⟨C, hC, hCle⟩ := exists_uniformFringeLaw_real_le_mul hT
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hadm : ∀ᶠ n in admissibleSizes μ, Admissible μ n :=
    mem_inf_of_right (mem_principal_self _)
  set t : ℕ → ℝ := fun n => (cond (bienayme μ) {T | G (k n) T}).real
    {T | M n < T.vertexCount} with htdef
  set p : ℕ → ℝ := markProb μ G k with hpdef
  have hp0 : ∀ n, 0 ≤ p n := fun n => measureReal_nonneg
  have ht0 : ∀ n, 0 ≤ t n := fun n => measureReal_nonneg
  have hpn : ∀ n, p n = (bienayme μ).real {T | G (k n) T} := fun n => rfl
  have hq : ∀ n, (bienayme μ).real {T | G (k n) T ∧ M n < T.vertexCount} = t n * p n := by
    intro n
    simp only [htdef, hpdef, markProb]
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_mul,
      cond_mul_eq_inter MeasurableSet.of_discrete]
    rfl
  have ha1 : ∀ᶠ n in admissibleSizes μ, 1 ≤ a n := hl (hT.tendsto_atTop.eventually_ge_atTop 1)
  have ht : Tendsto t (admissibleSizes μ) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
      (Eventually.of_forall ht0) ?_
    filter_upwards [ha1] with n hn
    exact le_mul_of_one_le_left (ht0 n) hn
  -- large marked trees: `P(G(𝒯^n_{U_n}), |𝒯^n_{U_n}| > M_n) ≤ C a_n P(G(𝒯), |𝒯| > M_n)`
  have hlarge : ∀ᶠ n in admissibleSizes μ,
      (uniformFringeLaw μ n).real {T | G (k n) T ∧ M n < T.vertexCount} ≤
        C * (a n * t n) * p n := by
    filter_upwards [hadm] with n hn
    have := hCle n hn (fun T => G (k n) T ∧ M n < T.vertexCount)
    rw [hq] at this
    calc _ ≤ C * a n * (t n * p n) := this
      _ = _ := by ring
  -- both halves combined: `|P(G(𝒯^n_{U_n})) - π_n| ≤ ε π_n` eventually
  have hmain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in admissibleSizes μ,
      |(uniformFringeLaw μ n).real {T | G (k n) T} - p n| ≤ ε * p n := by
    intro ε hε
    have hlim : Tendsto (fun n => C * (a n * t n) + t n) (admissibleSizes μ) (𝓝 0) := by
      simpa using (h.const_mul C).add ht
    filter_upwards [eventually_abs_uniformFringeLaw_real_sub_le hT hM.isLittleO (half_pos hε),
      hlarge, hadm, hlim.eventually (ge_mem_nhds (half_pos hε))] with n hs hlg hn hlim'
    have := Cyclic.isProbabilityMeasure_uniformFringeLaw hn
    have hs' := hs (fun T => G (k n) T ∧ T.vertexCount ≤ M n) (fun T hT => hT.2)
    have hU := measureReal_split_vertexCount (uniformFringeLaw μ n) (G (k n)) (M n)
    have hP := measureReal_split_vertexCount (bienayme μ) (G (k n)) (M n)
    rw [hq, ← hpn] at hP
    have hPle : (bienayme μ).real {T | G (k n) T ∧ T.vertexCount ≤ M n} ≤ p n :=
      measureReal_mono (fun T hT => hT.1)
    have hPle' : ε / 2 * (bienayme μ).real {T | G (k n) T ∧ T.vertexCount ≤ M n} ≤
        ε / 2 * p n := mul_le_mul_of_nonneg_left hPle (by positivity)
    have hU0 : 0 ≤ (uniformFringeLaw μ n).real {T | G (k n) T ∧ M n < T.vertexCount} :=
      measureReal_nonneg
    have hkey : C * (a n * t n) * p n + t n * p n ≤ ε / 2 * p n := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right hlim' (hp0 n)
    have htp : 0 ≤ t n * p n := mul_nonneg (ht0 n) (hp0 n)
    rw [abs_le] at hs' ⊢
    constructor <;> linarith [hs'.1, hs'.2]
  refine ⟨?_, ?_⟩
  · refine isLittleO_iff.2 fun ε hε => ?_
    filter_upwards [hmain ε hε] with n hn
    rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp0 n)]
    exact hn
  · have hlim : Tendsto (fun n => 2 * C * (a n * t n)) (admissibleSizes μ) (𝓝 0) := by
      simpa using h.const_mul (2 * C)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun n => measureReal_nonneg) ?_
    filter_upwards [hmain (1 / 2) one_half_pos, hlarge, hadm, ha1] with n hn hlg hadmn ha1n
    have := Cyclic.isProbabilityMeasure_uniformFringeLaw hadmn
    have hCat : 0 ≤ C * (a n * t n) := mul_nonneg hC.le (mul_nonneg (by linarith) (ht0 n))
    rw [cond_real_apply_of_discrete, ← Set.ofPred_and]
    rcases (hp0 n).eq_or_lt with hp | hp
    · have h0 : (uniformFringeLaw μ n).real {T | G (k n) T ∧ M n < T.vertexCount} = 0 :=
        le_antisymm (by rw [← hp, mul_zero] at hlg; exact hlg) measureReal_nonneg
      rw [h0, mul_zero]
      linarith
    · rw [abs_le] at hn
      have hupos : 0 < (uniformFringeLaw μ n).real {T | G (k n) T} := by linarith [hn.1]
      rw [inv_mul_le_iff₀ hupos]
      calc _ ≤ C * (a n * t n) * p n := hlg
        _ ≤ C * (a n * t n) * (2 * (uniformFringeLaw μ n).real {T | G (k n) T}) :=
          mul_le_mul_of_nonneg_left (by linarith [hn.1]) hCat
        _ = _ := by ring

/-- **Lemma `lem:M`** exactly as stated in the source (line 1015–1026), with the hypothesis
"`π_n > 0` for all sufficiently large (admissible) `n`", which the proof does not need
(see `microscopic_of_tail`). -/
theorem microscopic_of_tail_of_eventually_pos (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k M : ℕ → ℕ} (hM : IsCutoff M)
    (_hpos : ∀ᶠ n in admissibleSizes μ, 0 < markProb μ G k n)
    (h : Tendsto (fun n => a n * (cond (bienayme μ) {T | G (k n) T}).real
      {T | M n < T.vertexCount}) (admissibleSizes μ) (𝓝 0)) :
    Microscopic μ G k M :=
  microscopic_of_tail hT hM h

end PoissonDeclumping.Bridge
