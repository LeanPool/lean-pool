/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import LeanPool.AbstractLinearControl.Definitions
public import LeanPool.AbstractLinearControl.Background.Phillips


/-!
# Every `L^∞` system is zero-class (Theorem 1.5)

**Theorem 1.5** (`thm:p-infty-zero-class`). Let `X`, `U` be Banach spaces and `(𝕋, Φ)`
an abstract linear control system with `p = ∞`. Then the system is of the zero-class,
i.e. `‖Φ_t‖ → 0` as `t → 0`.

The final statement is `ALCS.zero_class`, at the end of this file. The auxiliary
declarations live in the namespace `ALCS.ZeroClassProof` and follow § 2.3 of the paper:

* `ell` is the limit `ℓ = lim_{t → 0⁺} κ(t) = inf_{t > 0} κ(t)` (`eq:ell`), and
  `norm_Phi_tendsto` identifies it as the limit along any positive null sequence.
* Step 1, `doubling`: the doubling inequality `eq:doubling`,
  `2 ‖Φ_h u‖ ≤ κ(2h) + ‖(T_h - Id) Φ_h u‖` for `‖u‖ ≤ 1`.
* Step 2, `data`, `h`, `x`: nearly extremal pulses `u_n` on rapidly decreasing time
  scales `h_n`, with states `x_n = Φ_{h_n} u_n` (`eq:xn-extremal`, `eq:hn-fast`).
* Step 3, `packing`, `packedOperator`: the pulses are packed into one bounded operator
  `S : ℓ^∞ → X`, and `packedOperator_close` is `eq:Sen-xn`.
* Step 4, `x_moves_tendsto`: Lemma 2.3 (`Phillips.uniform`) gives
  `‖(T_{h_n} - Id) x_n‖ → 0`, which is the second half of `eq:goal`.

## Difference with the paper in Step 3

The paper plays the pulses one after the other on consecutive intervals
`[s_n, s_{n+1})` and evaluates at the accumulated time `H = Σ h_k`. Here each pulse
gets its own *free-evolution time* `r_n ∈ (0, h_n]`, chosen in Step 2 so that
`‖T_{r_n} x_n - x_n‖ ≤ 2^{-n}`, and the `n`-th pulse is played on
`[1 - r_n - h_n, 1 - r_n)`, with zero input in the gaps; the operator is evaluated at
time `1`. Then `S e_n = T_{r_n} x_n` exactly. This changes the bookkeeping, not the
argument. The scalar field is `ℝ` or `ℂ` (`RCLike 𝕜`), as required by Phillips' lemma.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

section Endpoint

open scoped BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]

namespace ALCS
namespace ZeroClassProof

/-! ### Step 1: the doubling inequality -/

variable (S : ALCS 𝕜 X U ∞)

/-- Step 1, the doubling inequality `eq:doubling`: for `h ≥ 0` and `‖u‖ ≤ 1`,
`2 ‖Φ_h u‖ ≤ κ(2h) + ‖T_h (Φ_h u) - Φ_h u‖`, obtained by playing `u` twice in a row. -/
lemma doubling {h : ℝ} (hh : 0 ≤ h) (u : Lp U ∞ muPlus)
    (hu : ‖u‖ ≤ 1) :
    2 * ‖S.Φ h u‖ ≤ ‖S.Φ (2 * h)‖ +
      ‖S.T h (S.Φ h u) - S.Φ h u‖ := by
  obtain ⟨w, hw, hcat⟩ := exists_concat h u u (by norm_num) hu hu
  have hcomp := S.composition h h hh hh u u w hcat
  have hnorm : ‖S.Φ (2 * h) w‖ ≤ ‖S.Φ (2 * h)‖ := by
    exact ((S.Φ (2 * h)).le_opNorm w).trans
      (by simpa using mul_le_mul_of_nonneg_left hw (norm_nonneg (S.Φ (2 * h))))
  let x := S.Φ h u
  have hid : x + x = S.Φ (2 * h) w - (S.T h x - x) := by
    rw [show 2 * h = h + h by ring, hcomp]
    dsimp [x]
    abel
  have htwo : ‖x + x‖ = 2 * ‖x‖ := by
    calc
      ‖x + x‖ = ‖(2 : 𝕜) • x‖ := by rw [two_smul]
      _ = ‖(2 : 𝕜)‖ * ‖x‖ := norm_smul _ _
      _ = 2 * ‖x‖ := by rw [show ‖(2 : 𝕜)‖ = 2 from RCLike.norm_natCast 2]
  calc
    2 * ‖S.Φ h u‖ = ‖x + x‖ := htwo.symm
    _ ≤ ‖S.Φ (2 * h) w‖ + ‖S.T h x - x‖ := by
      rw [hid]
      exact norm_sub_le _ _
    _ ≤ ‖S.Φ (2 * h)‖ + ‖S.T h x - x‖ := add_le_add hnorm le_rfl

/-! ### Step 2: nearly extremal pulses on rapidly decreasing time scales -/

/-- An input of norm at most one which almost realizes `κ(h) = ‖Φ h‖`. -/
lemma exists_near_extremal (h ε : ℝ) (hε : 0 < ε) :
    ∃ u : Lp U ∞ muPlus, ‖u‖ ≤ 1 ∧ ‖S.Φ h‖ - ε ≤ ‖S.Φ h u‖ := by
  by_cases hc : ‖S.Φ h‖ - ε ≤ 0
  · exact ⟨0, by simp, by simpa using hc⟩
  · by_contra hn
    have hbound : ‖S.Φ h‖ ≤ ‖S.Φ h‖ - ε := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm (le_of_lt (lt_of_not_ge hc))
      intro u hu
      exact (lt_of_not_ge (fun h => hn ⟨u, hu.le, h⟩)).le
    linarith

/-- A *pulse* of length `h`: a control of norm at most one, given by an actual
(everywhere defined) representative vanishing outside `[0, h)`. -/
structure Pulse (U : Type*) [NormedAddCommGroup U] (h : ℝ) where
  /-- the representative -/
  f : ℝ → U
  measurable : StronglyMeasurable f
  bound : ∀ t, ‖f t‖ ≤ 1
  off : ∀ t, t < 0 ∨ h ≤ t → f t = 0

namespace Pulse

variable {h : ℝ} (P : Pulse U h)

/-- The pulse, as an element of `L^∞(ℝ₊; U)`. -/
def input : Lp U ∞ muPlus :=
  (memLp_of_bound P.measurable P.bound).toLp P.f

lemma coe_input : ⇑P.input =ᵐ[muPlus] P.f :=
  (memLp_of_bound P.measurable P.bound).coeFn_toLp

lemma norm_input : ‖P.input‖ ≤ 1 :=
  norm_toLp_le _ (by norm_num) P.bound

/-- A pulse of length `h` is switched off after time `h`: `P = P ⋄_h 0`. -/
lemma free_rep : ⇑P.input =ᵐ[muPlus]
    concat h ⇑P.input ⇑(0 : Lp U ∞ muPlus) := by
  have hraw : P.f = concat h P.f (fun _ => (0 : U)) := by
    funext t
    by_cases ht : t < h
    · simp [concat, ht]
    · simp [concat, ht, P.off t (Or.inr (not_lt.1 ht))]
  exact P.coe_input.trans
    ((Filter.EventuallyEq.of_eq hraw).trans
      (concat_congr h P.coe_input (Lp.coeFn_zero U ∞ muPlus)).symm)

end Pulse

/-- A nearly extremal input can be chosen to be a pulse (by causality `eq:causality`,
truncating it at time `h` does not change `Φ_h u`). -/
lemma exists_pulse (h : ℝ) (hh : 0 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Pulse U h, ‖S.Φ h‖ - ε ≤ ‖S.Φ h P.input‖ := by
  obtain ⟨u, hu, hnear⟩ := exists_near_extremal S h ε hε
  obtain ⟨g, hg, hgb, hug⟩ := exists_bounded_rep u (by norm_num) hu
  let f := (Set.Ico 0 h).indicator g
  have hf : StronglyMeasurable f := hg.indicator measurableSet_Ico
  have hb : ∀ t, ‖f t‖ ≤ 1 := by
    intro t
    by_cases ht : t ∈ Set.Ico 0 h
    · simpa [f, Set.indicator_of_mem ht] using hgb t
    · simp [f, Set.indicator_of_notMem ht]
  have hoff : ∀ t, t < 0 ∨ h ≤ t → f t = 0 := by
    intro t ht
    have hnot : t ∉ Set.Ico 0 h := by
      intro hin
      rcases ht with ht | ht
      · exact (not_lt_of_ge hin.1) ht
      · exact (not_lt_of_ge ht) hin.2
    exact Set.indicator_of_notMem hnot g
  let P : Pulse U h := ⟨f, hf, hb, hoff⟩
  have hraw : f =ᵐ[muPlus] concat h g (fun _ => (0 : U)) := by
    have hpos : ∀ᵐ t ∂muPlus, t ∈ Set.Ici (0 : ℝ) :=
      ae_restrict_mem measurableSet_Ici
    filter_upwards [hpos] with t ht
    have ht0 : 0 ≤ t := ht
    by_cases hth : t < h
    · simp [f, concat, hth, Set.mem_Ico, ht0]
    · simp [f, concat, hth, Set.mem_Ico]
  have hcat : ⇑P.input =ᵐ[muPlus] concat h ⇑u ⇑(0 : Lp U ∞ muPlus) :=
    P.coe_input.trans (hraw.trans (concat_congr h hug (Lp.coeFn_zero U ∞ muPlus)).symm)
  refine ⟨P, ?_⟩
  rwa [S.causality h hh u 0 P.input hcat]

/-- The accuracy `2^{-n}` of the `n`-th selection. -/
def err (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

lemma err_pos (n : ℕ) : 0 < err n := by
  unfold err
  positivity

lemma err_tendsto : Tendsto err atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The data selected at step `n` of Step 2: a nearly extremal pulse of length `h`
(`eq:xn-extremal`), and a free-evolution time `r ∈ (0, h]` during which its state is
essentially frozen by the semigroup (the analogue of `eq:hn-fast`). -/
structure FrozenPulse (S : ALCS 𝕜 X U ∞) (n : ℕ) (h : ℝ) where
  /-- The bounded input pulse whose output nearly attains the operator norm. -/
  pulse : Pulse U h
  near : ‖S.Φ h‖ - err n ≤ ‖S.Φ h pulse.input‖
  /-- the free-evolution time -/
  r : ℝ
  r_pos : 0 < r
  r_le : r ≤ h
  close : ‖S.T r (S.Φ h pulse.input) - S.Φ h pulse.input‖ ≤ err n

lemma frozenPulse_nonempty (n : ℕ) (h : ℝ) (hh : 0 < h) :
    Nonempty (FrozenPulse S n h) := by
  obtain ⟨P, hP⟩ := exists_pulse S h hh.le (err n) (err_pos n)
  obtain ⟨δ, hδ, hc⟩ := Metric.tendsto_nhdsWithin_nhds.1
    (S.T_cont (S.Φ h P.input)) (err n) (err_pos n)
  let r := min h (δ / 2)
  have hr : 0 < r := lt_min hh (by positivity)
  have hrh : r ≤ h := min_le_left _ _
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨⟨P, hP, r, hr, hrh, ?_⟩⟩
  have hc' := hc (Set.mem_Ici.2 hr.le)
    (show dist r 0 < δ by simpa [Real.dist_eq, abs_of_pos hr] using hrδ)
  have hclose : ‖S.T r (S.Φ h P.input) - S.Φ h P.input‖ < err n := by
    simpa only [dist_eq_norm] using hc'
  exact hclose.le

/-- Classical choice is used only to choose actual witnesses to proved existences. -/
def choosePulse (n : ℕ) (h : ℝ) (hh : 0 < h) : FrozenPulse S n h :=
  Classical.choice (frozenPulse_nonempty S n h hh)

/-- The time scales, defined recursively: `h 0 = 1/4` and `h (n + 1) = r n / 4`, so that
the next pulse fits inside the free-evolution interval of the previous one. -/
def positiveTimes : ℕ → {h : ℝ // 0 < h} :=
  Nat.rec ⟨1 / 4, by norm_num⟩
    (fun n h =>
      ⟨(choosePulse S n h.1 h.2).r / 4,
        div_pos (choosePulse S n h.1 h.2).r_pos (by norm_num)⟩)

/-- The time scale `h_n`. -/
def h (n : ℕ) : ℝ := (positiveTimes S n).1

/-- The pulse `u_n` and the free-evolution time `r_n` selected at step `n`. -/
def data (n : ℕ) : FrozenPulse S n (h S n) :=
  choosePulse S n (h S n) (positiveTimes S n).2

/-- The free-evolution time `r_n ∈ (0, h_n]`. -/
def r (n : ℕ) : ℝ := (data S n).r

/-- The state `x_n = Φ_{h_n} u_n`. -/
def x (n : ℕ) : X := S.Φ (h S n) (data S n).pulse.input

lemma h_pos (n : ℕ) : 0 < h S n := (positiveTimes S n).2
lemma r_pos (n : ℕ) : 0 < r S n := (data S n).r_pos
lemma r_le_h (n : ℕ) : r S n ≤ h S n := (data S n).r_le
lemma h_zero : h S 0 = 1 / 4 := rfl
lemma h_succ (n : ℕ) : h S (n + 1) = r S n / 4 := rfl

lemma h_succ_le (n : ℕ) : h S (n + 1) ≤ h S n / 2 := by
  rw [h_succ]
  have := r_le_h S n
  have := (h_pos S n).le
  linarith

lemma h_le_quarter (n : ℕ) : h S n ≤ 1 / 4 := by
  induction n with
  | zero => simp [h_zero]
  | succ n ih =>
    have := h_succ_le S n
    linarith

lemma h_geometric (n : ℕ) : h S n ≤ err n / 4 := by
  induction n with
  | zero => simp [h_zero, err]
  | succ n ih =>
    have := h_succ_le S n
    dsimp [err] at ih ⊢
    rw [pow_succ]
    linarith

lemma h_tendsto : Tendsto (h S) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => (h_pos S n).le) (h_geometric S)
    (by simpa using err_tendsto.div_const 4)

lemma x_near (n : ℕ) : ‖S.Φ (h S n)‖ - err n ≤ ‖x S n‖ :=
  (data S n).near

lemma x_le (n : ℕ) : ‖x S n‖ ≤ ‖S.Φ (h S n)‖ := by
  exact ((S.Φ (h S n)).le_opNorm _).trans
    (by simpa using
      mul_le_mul_of_nonneg_left (data S n).pulse.norm_input (norm_nonneg (S.Φ (h S n))))

lemma x_frozen (n : ℕ) : ‖S.T (r S n) (x S n) - x S n‖ ≤ err n :=
  (data S n).close

/-! ### Step 3: packing the pulses into one bounded operator `ℓ^∞ → X` -/

/-- The `n`-th pulse is played on `window n = [start n, start n + h n)`, where
`start n = 1 - r n - h n`. These windows are pairwise disjoint subsets of `[0, 1)`. -/
def start (n : ℕ) : ℝ := 1 - r S n - h S n

/-- The interval on which the `n`-th pulse is played. -/
def window (n : ℕ) : Set ℝ := Set.Ico (start S n) (start S n + h S n)

/-- The `n`-th pulse, delayed so that it is played on `window n`. -/
def block (n : ℕ) (t : ℝ) : U := (data S n).pulse.f (t - start S n)

lemma start_nonneg (n : ℕ) : 0 ≤ start S n := by
  have := r_le_h S n
  have := h_le_quarter S n
  dsimp [start]
  linarith

lemma finish_le_next (n : ℕ) : start S n + h S n ≤ start S (n + 1) := by
  have h₁ := r_le_h S (n + 1)
  have h₂ := h_succ S n
  have h₃ := (r_pos S n).le
  dsimp [start]
  linarith

lemma start_mono : Monotone (start S) := by
  apply monotone_nat_of_le_succ
  intro n
  have := finish_le_next S n
  have := (h_pos S n).le
  linarith

lemma finish_le_start {i j : ℕ} (hij : i < j) :
    start S i + h S i ≤ start S j :=
  (finish_le_next S i).trans (start_mono S (Nat.succ_le_of_lt hij))

lemma window_unique {i j : ℕ} {t : ℝ}
    (hi : t ∈ window S i) (hj : t ∈ window S j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · have := finish_le_start S hij
    have hi' := hi.2
    have hj' := hj.1
    linarith
  · exact hij
  · have := finish_le_start S hji
    have hj' := hj.2
    have hi' := hi.1
    linarith

lemma block_measurable (n : ℕ) : StronglyMeasurable (block S n) :=
  (data S n).pulse.measurable.comp_measurable (measurable_id.sub_const _)

lemma block_bound (n : ℕ) (t : ℝ) : ‖block S n t‖ ≤ 1 :=
  (data S n).pulse.bound _

lemma block_off (n : ℕ) {t : ℝ} (ht : t ∉ window S n) : block S n t = 0 := by
  apply (data S n).pulse.off
  by_cases hs : t < start S n
  · left
    linarith
  · right
    by_contra hh
    apply ht
    constructor
    · exact not_lt.1 hs
    · change t < start S n + h S n
      linarith

/-- The packed control `u^α` (raw function): on `window n` it is `α_n` times the `n`-th
pulse, and it vanishes outside the windows. -/
def packRaw (a : Phillips.Linfty 𝕜) : ℝ → U := by
  classical
  exact fun t => if ht : ∃ n, t ∈ window S n then
    a (Classical.choose ht) • block S (Classical.choose ht) t else 0

lemma packRaw_on (a : Phillips.Linfty 𝕜) {n : ℕ} {t : ℝ}
    (ht : t ∈ window S n) : packRaw S a t = a n • block S n t := by
  classical
  have hex : ∃ j, t ∈ window S j := ⟨n, ht⟩
  have heq : Classical.choose hex = n :=
    window_unique S (Classical.choose_spec hex) ht
  simp only [packRaw, dite_eq_left hex, heq]

lemma packRaw_off (a : Phillips.Linfty 𝕜) {t : ℝ}
    (ht : ¬ ∃ n, t ∈ window S n) : packRaw S a t = 0 := by
  classical
  simp [packRaw, ht]

lemma packRaw_add (a b : Phillips.Linfty 𝕜) (t : ℝ) :
    packRaw S (a + b) t = packRaw S a t + packRaw S b t := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S (a + b) hn, packRaw_on S a hn, packRaw_on S b hn]
    simp only [BoundedContinuousFunction.add_apply, add_smul]
  · simp only [packRaw_off S (a + b) ht, packRaw_off S a ht,
      packRaw_off S b ht, add_zero]

lemma packRaw_smul (c : 𝕜) (a : Phillips.Linfty 𝕜) (t : ℝ) :
    packRaw S (c • a) t = c • packRaw S a t := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S (c • a) hn, packRaw_on S a hn]
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, smul_smul]
  · simp only [packRaw_off S (c • a) ht, packRaw_off S a ht, smul_zero]

lemma packRaw_bound (a : Phillips.Linfty 𝕜) (t : ℝ) :
    ‖packRaw S a t‖ ≤ ‖a‖ := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    rw [packRaw_on S a hn, norm_smul]
    have ha : ‖a n‖ ≤ ‖a‖ :=
      (BoundedContinuousFunction.norm_le (norm_nonneg a)).1 le_rfl n
    calc
      ‖a n‖ * ‖block S n t‖ ≤ ‖a n‖ * 1 :=
        mul_le_mul_of_nonneg_left (block_bound S n t) (norm_nonneg _)
      _ ≤ ‖a‖ := by simpa using ha
  · rw [packRaw_off S a ht, norm_zero]
    exact norm_nonneg _

/-- At every time the partial sums eventually equal the glued function.  This
uses pointwise disjointness, not convergence of a series in the L-infinity norm. -/
lemma partial_sums_eventually (a : Phillips.Linfty 𝕜) (t : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, a n • block S n t) = packRaw S a t := by
  classical
  by_cases ht : ∃ n, t ∈ window S n
  · obtain ⟨n, hn⟩ := ht
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    rw [packRaw_on S a hn]
    apply Finset.sum_eq_single n
    · intro j _ hjn
      have hj : t ∉ window S j :=
        fun hj => hjn (window_unique S hj hn)
      simp [block_off S j hj]
    · intro hnN
      exact (hnN (Finset.mem_range.2 (by omega))).elim
  · filter_upwards [] with N
    rw [packRaw_off S a ht]
    apply Finset.sum_eq_zero
    intro n _
    have hn : t ∉ window S n := fun hn => ht ⟨n, hn⟩
    simp [block_off S n hn]

lemma packRaw_measurable (a : Phillips.Linfty 𝕜) :
    StronglyMeasurable (packRaw S a) := by
  classical
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun N t => ∑ n ∈ Finset.range N, a n • block S n t)
  · intro N
    exact Finset.stronglyMeasurable_fun_sum (Finset.range N)
      (fun n _ => (block_measurable S n).const_smul (a n))
  · apply tendsto_pi_nhds.2
    intro t
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (partial_sums_eventually S a t))

lemma packRaw_memLp (a : Phillips.Linfty 𝕜) : MemLp (packRaw S a) ∞ muPlus :=
  memLp_of_bound (packRaw_measurable S a) (packRaw_bound S a)

/-- The packed control `u^α ∈ L^∞(ℝ₊; U)`. -/
def packedInput (a : Phillips.Linfty 𝕜) : Lp U ∞ muPlus :=
  (packRaw_memLp S a).toLp (packRaw S a)

lemma packedInput_ae (a : Phillips.Linfty 𝕜) :
    ⇑(packedInput S a) =ᵐ[muPlus] packRaw S a :=
  (packRaw_memLp S a).coeFn_toLp

lemma packedInput_norm (a : Phillips.Linfty 𝕜) : ‖packedInput S a‖ ≤ ‖a‖ :=
  norm_toLp_le _ (norm_nonneg _) (packRaw_bound S a)

lemma packedInput_add (a b : Phillips.Linfty 𝕜) :
    packedInput S (a + b) = packedInput S a + packedInput S b := by
  apply Lp.ext
  filter_upwards [packedInput_ae S (a + b), packedInput_ae S a,
    packedInput_ae S b, Lp.coeFn_add (packedInput S a) (packedInput S b)]
      with t hab ha hb hsum
  rw [hab, hsum]
  simpa only [Pi.add_apply, ha, hb] using packRaw_add S a b t

lemma packedInput_smul (c : 𝕜) (a : Phillips.Linfty 𝕜) :
    packedInput S (c • a) = c • packedInput S a := by
  apply Lp.ext
  filter_upwards [packedInput_ae S (c • a), packedInput_ae S a,
    Lp.coeFn_smul c (packedInput S a)] with t hca ha hsmul
  rw [hca, hsmul]
  simpa only [Pi.smul_apply, ha] using packRaw_smul S c a t

/-- The contraction `α ↦ u^α` from `ℓ^∞` to `L^∞(ℝ₊; U)`. -/
def packing : Phillips.Linfty 𝕜 →L[𝕜] Lp U ∞ muPlus :=
  LinearMap.mkContinuous
    { toFun := packedInput S
      map_add' := packedInput_add S
      map_smul' := fun c a => by
        simpa using packedInput_smul S c a }
    1 (fun a => by simpa using packedInput_norm S a)

lemma packing_ae (a : Phillips.Linfty 𝕜) :
    ⇑(packing S a) =ᵐ[muPlus] packRaw S a := packedInput_ae S a

lemma packRaw_e (n : ℕ) (t : ℝ) :
    packRaw S (Phillips.e n) t = block S n t := by
  classical
  by_cases hn : t ∈ window S n
  · rw [packRaw_on S _ hn]
    simp
  · rw [block_off S n hn]
    by_cases ht : ∃ j, t ∈ window S j
    · obtain ⟨j, hj⟩ := ht
      have hjn : j ≠ n := by
        intro heq
        subst j
        exact hn hj
      rw [packRaw_on S _ hj]
      simp [Phillips.e_apply, hjn]
    · exact packRaw_off S _ ht

/-- The operator `S : ℓ^∞ → X`, `S α = Φ_1 u^α`. -/
def packedOperator : Phillips.Linfty 𝕜 →L[𝕜] X :=
  (S.Φ 1).comp (packing S)

/-- `S e_n = T_{r_n} x_n`: the `n`-th state, after it has evolved freely during the
time `r_n` (by `eq:delay` and then `eq:free`). -/
lemma packedOperator_e (n : ℕ) :
    packedOperator S (Phillips.e n) = S.T (r S n) (x S n) := by
  let P := (data S n).pulse
  have hraw : packRaw S (Phillips.e n) =
      concat (start S n) (fun _ => (0 : U)) P.f := by
    funext t
    rw [packRaw_e]
    by_cases ht : t < start S n
    · have hoff : P.f (t - start S n) = 0 :=
        P.off _ (Or.inl (by linarith))
      simpa [concat, ht, block, P] using hoff
    · simp [concat, ht, block, P]
  have hw : ⇑(packing S (Phillips.e n)) =ᵐ[muPlus]
      concat (start S n) ⇑(0 : Lp U ∞ muPlus) ⇑P.input :=
    (packing_ae S _).trans
      ((Filter.EventuallyEq.of_eq hraw).trans
        (concat_congr (start S n) (Lp.coeFn_zero U ∞ muPlus) P.coe_input).symm)
  have hsum : start S n + (h S n + r S n) = 1 := by
    unfold start
    ring
  change S.Φ 1 (packing S (Phillips.e n)) = _
  rw [← hsum]
  rw [S.delay (start S n) (h S n + r S n) (start_nonneg S n)
    (add_nonneg (h_pos S n).le (r_pos S n).le) P.input _ hw]
  exact S.free (h S n) (r S n) (h_pos S n).le (r_pos S n).le
    P.input P.input P.free_rep

/-- `‖S e_n - x_n‖ ≤ 2^{-n}`, equation `eq:Sen-xn`. -/
lemma packedOperator_close (n : ℕ) :
    ‖packedOperator S (Phillips.e n) - x S n‖ ≤ err n := by
  rw [packedOperator_e]
  exact x_frozen S n

/-! ### The limit `ℓ` of `κ(t)` as `t → 0⁺` (`eq:ell`) -/

/-- The possible input-map norms at strictly positive times. -/
def normRange : Set ℝ := (fun t : ℝ => ‖S.Φ t‖) '' Set.Ioi 0

lemma normRange_nonempty : (normRange S).Nonempty :=
  ⟨‖S.Φ 1‖, 1, by norm_num, rfl⟩

lemma normRange_bddBelow : BddBelow (normRange S) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, _, rfl⟩
  exact norm_nonneg _

/-- `ℓ = inf_{t > 0} κ(t)`, equation `eq:ell`. -/
def ell : ℝ := sInf (normRange S)

lemma ell_nonneg : 0 ≤ ell S := by
  apply le_csInf (normRange_nonempty S)
  rintro y ⟨t, _, rfl⟩
  exact norm_nonneg _

lemma ell_le (t : ℝ) (ht : 0 < t) : ell S ≤ ‖S.Φ t‖ :=
  csInf_le (normRange_bddBelow S) ⟨t, ht, rfl⟩

lemma exists_norm_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ‖S.Φ t‖ < ell S + ε := by
  by_contra hn
  have hbad : ell S + ε ≤ ell S := by
    apply le_csInf (normRange_nonempty S)
    rintro y ⟨t, ht, rfl⟩
    exact le_of_not_gt (fun hlt => hn ⟨t, ht, hlt⟩)
  linarith

/-- Monotonicity identifies the norm limit along every positive null sequence. -/
lemma norm_Phi_tendsto (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ‖S.Φ (t n)‖) atTop (𝓝 (ell S)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨τ, hτ, hτnorm⟩ := exists_norm_lt S ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ht τ hτ
  refine ⟨N, fun n hn => ?_⟩
  have htn : t n < τ := by
    have hdist := hN n hn
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (htpos n)] using hdist
  have hupper := norm_Phi_mono S (htpos n).le htn.le
  have hlower := ell_le S (t n) (htpos n)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hlower)]
  linarith

/-- First half of `eq:goal`: `‖x_n‖ → ℓ`. -/
lemma x_norm_tendsto : Tendsto (fun n => ‖x S n‖) atTop (𝓝 (ell S)) := by
  have hk := norm_Phi_tendsto S (h S) (h_pos S) (h_tendsto S)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hk ε hε
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 err_tendsto ε hε
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hkdist := hN₁ n (le_trans (le_max_left _ _) hn)
  have hedist := hN₂ n (le_trans (le_max_right _ _) hn)
  have hkabs : |‖S.Φ (h S n)‖ - ell S| < ε := by
    simpa only [Real.dist_eq] using hkdist
  have he : err n < ε := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (err_pos n)] using hedist
  have hupper := x_le S n
  have hnear := x_near S n
  have hlower := ell_le S (h S n) (h_pos S n)
  rw [Real.dist_eq]
  obtain ⟨_, hkright⟩ := abs_lt.1 hkabs
  exact abs_lt.2 ⟨by linarith, by linarith⟩

/-! ### Step 4: conclusion with Lemma 2.3 -/

/-- Second half of `eq:goal`: `‖T_{h_n} x_n - x_n‖ → 0`. By Lemma 2.3
(`Phillips.uniform`), `‖(T_{h_n} - Id) S e_n‖ → 0`, and `S e_n` is `2^{-n}`-close to `x_n`. -/
lemma x_moves_tendsto [CompleteSpace X] :
    Tendsto (fun n => ‖S.T (h S n) (x S n) - x S n‖) atTop (𝓝 0) := by
  obtain ⟨ω, hω, M, hM, hbound⟩ := S.toC0Semigroup.exists_exp_bound
  let K : ℝ := M * Real.exp ω
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hK : 0 ≤ K := mul_nonneg hM0 (Real.exp_pos _).le
  have hTbound : ∀ n, ‖S.T (h S n)‖ ≤ K := by
    intro n
    calc
      ‖S.T (h S n)‖ ≤ M * Real.exp (ω * h S n) :=
        hbound _ (h_pos S n).le
      _ ≤ M * Real.exp ω := by
        apply mul_le_mul_of_nonneg_left _ hM0
        apply Real.exp_le_exp.2
        have hn : h S n ≤ 1 := le_trans (h_le_quarter S n) (by norm_num)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hω
      _ = K := rfl
  let A : ℕ → X →L[𝕜] X :=
    fun n => S.T (h S n) - ContinuousLinearMap.id 𝕜 X
  have hAbound : ∀ n, ‖A n‖ ≤ K + 1 := by
    intro n
    calc
      ‖A n‖ ≤ ‖S.T (h S n)‖ + ‖ContinuousLinearMap.id 𝕜 X‖ := norm_sub_le _ _
      _ ≤ K + 1 := add_le_add (hTbound n) (ContinuousLinearMap.norm_id_le)
  have hPhillips : Tendsto
      (fun n => ‖A n (packedOperator S (Phillips.e n))‖) atTop (𝓝 0) := by
    exact Phillips.uniform (packedOperator S) S.T S.T_cont
      (h S) (fun n => (h_pos S n).le) (h_tendsto S)
  have herror : ∀ n, ‖S.T (h S n) (x S n) - x S n‖ ≤
      ‖A n (packedOperator S (Phillips.e n))‖ + (K + 1) * err n := by
    intro n
    let y := packedOperator S (Phillips.e n)
    have hxy : ‖x S n - y‖ ≤ err n := by
      rw [norm_sub_rev]
      exact packedOperator_close S n
    have hsplit : A n (x S n) = A n y + A n (x S n - y) := by
      rw [map_sub]
      abel
    calc
      ‖S.T (h S n) (x S n) - x S n‖ = ‖A n (x S n)‖ := rfl
      _ = ‖A n y + A n (x S n - y)‖ := congrArg norm hsplit
      _ ≤ ‖A n y‖ + ‖A n (x S n - y)‖ := norm_add_le _ _
      _ ≤ ‖A n y‖ + ‖A n‖ * ‖x S n - y‖ :=
        add_le_add le_rfl ((A n).le_opNorm _)
      _ ≤ ‖A n y‖ + (K + 1) * err n := by
        apply add_le_add le_rfl
        exact mul_le_mul (hAbound n) hxy (norm_nonneg _) (by linarith)
  apply squeeze_zero (fun n => norm_nonneg _) herror
  simpa only [mul_zero, add_zero] using
    hPhillips.add (err_tendsto.const_mul (K + 1))

end ZeroClassProof

open ZeroClassProof

/-- **Theorem 1.5** (`thm:p-infty-zero-class`). Let `X`, `U` be real or complex Banach
spaces and `S = (𝕋, Φ)` an abstract linear control system with `p = ∞`. Then `S` is of
the zero-class: `‖Φ t‖ → 0` as `t → 0⁺`.

Proof: by Steps 2–4, `‖x_n‖ → ℓ` and `‖T_{h_n} x_n - x_n‖ → 0`; passing to the limit in
the doubling inequality of Step 1 gives `2ℓ ≤ ℓ`, hence `ℓ = 0`. -/
theorem zero_class [CompleteSpace X] (S : ALCS 𝕜 X U ∞) :
    S.IsZeroClass := by
  have hx := x_norm_tendsto S
  have hm := x_moves_tendsto S
  have htwo : Tendsto (fun n => ‖S.Φ (2 * h S n)‖) atTop (𝓝 (ell S)) :=
    norm_Phi_tendsto S (fun n => 2 * h S n)
      (fun n => mul_pos (by norm_num) (h_pos S n))
      (by simpa only [mul_zero] using (h_tendsto S).const_mul 2)
  have hineq : ∀ n, 2 * ‖x S n‖ ≤ ‖S.Φ (2 * h S n)‖ +
      ‖S.T (h S n) (x S n) - x S n‖ := by
    intro n
    exact doubling S (h_pos S n).le (data S n).pulse.input
      (data S n).pulse.norm_input
  have hlimit : 2 * ell S ≤ ell S := by
    have hleft := hx.const_mul 2
    have hright := htwo.add hm
    have hle := le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall hineq)
    simpa only [add_zero] using hle
  have hell : ell S = 0 := by
    have := ell_nonneg S
    linarith
  rw [IsZeroClass, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨τ, hτ, hnormτ⟩ := exists_norm_lt S ε hε
  rw [hell, zero_add] at hnormτ
  refine ⟨τ, hτ, fun t ht hdist => ?_⟩
  have ht0 : 0 ≤ t := ht
  have htτ : t < τ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht0] using hdist
  have hsmall : ‖S.Φ t‖ < ε :=
    lt_of_le_of_lt (norm_Phi_mono S ht0 htτ.le) hnormτ
  simpa using hsmall

end ALCS

end Endpoint

end

end

end AbstractLinearControl
