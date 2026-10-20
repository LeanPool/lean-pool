/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/

module

import Mathlib.Algebra.BigOperators.Field
public import LeanPool.GrahamLPT.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import LeanPool.GrahamLPT.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# CoffmanSethi

Chen's property of LPT schedules (Chen 1993, as Della Croce–Scatamacchia 2020 restate it,
Proposition 2): in an LPT
schedule the `j`-th job placed on a machine has length at most `C(τ)/j` for every assignment `τ`;
hence, when a
machine attaining the makespan holds `k` jobs, `k·m·C(σ) ≤ ((k + 1)m − 1)·C(τ)` (the Coffman–Sethi
form).
Helpers carry the prefix `cs_`.

The route (this development). Fix `P > 0` below every job placed so far and weigh a job `x` by
`⌊x/P⌋`. For two
machines `h, g` write `D` for the load of `h` minus the load of `g`, `Φ` for the weight of `h`
minus the number of
jobs on `g`, and `y` for the last job placed. The invariant `loadDifferenceInvariant` (`D ≥ 0 →
⌊D/P⌋ ≤ Φ`;
`D < 0 → −1 ≤ Φ ∧ ⌊(D + y)/P⌋ − 1 ≤ Φ`) holds at every step of a list schedule in nonincreasing
order, since a job
joins a least-loaded machine. With `g` the machine receiving job `k`, every machine weighs at
least the number of
jobs on `g` before `k`; summing over the machines and comparing with `τ`, where a machine's weight
is below `j`
when its load is below `j·p_k`, gives `j · p_k ≤ C(τ)`.
-/

@[expose] public section

namespace GrahamLPT

open Finset

/-- The number of jobs of index below `k` on machine `i`, as an integer. -/
def prefixJobCount {m n : ℕ} (σ : Fin n → Fin m) (k : ℕ) (i : Fin m) : ℤ :=
  ∑ _j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), (1 : ℤ)

/-- The weight `Σ ⌊p_j / P⌋` of the jobs of index below `k` on machine `i`. -/
noncomputable def prefixJobWeight {m n : ℕ} (p : Fin n → ℝ) (P : ℝ) (σ : Fin n → Fin m) (k : ℕ) (i
    : Fin m)
  : ℤ :=
  ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), ⌊p j / P⌋

/-- The two-machine invariant: `D` a load difference, `y` the last job, `Φ` a weight minus a
count. -/
def loadDifferenceInvariant (P D y : ℝ) (Φ : ℤ) : Prop :=
  (0 ≤ D → ⌊D / P⌋ ≤ Φ) ∧ (D < 0 → -1 ≤ Φ ∧ ⌊(D + y) / P⌋ - 1 ≤ Φ)

theorem cs_inv_mono {P D y y' : ℝ} {Φ : ℤ} (hP : 0 < P) (h : loadDifferenceInvariant P D y Φ) (hy
    : y' ≤ y) :
    loadDifferenceInvariant P D y' Φ := by
  refine ⟨h.1, fun hD => ⟨(h.2 hD).1, ?_⟩⟩
  have h1 : ⌊(D + y') / P⌋ ≤ ⌊(D + y) / P⌋ :=
    Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hP.le)
  have := (h.2 hD).2
  omega

theorem cs_inv_self {P y : ℝ} {Φ : ℤ} (hΦ : 0 ≤ Φ) : loadDifferenceInvariant P 0 y Φ := by
  refine ⟨fun _ => by simpa using hΦ, fun h => absurd h (lt_irrefl 0)⟩

/-- The receiving machine is the second of the pair (`D ≥ 0`): it gains a job of length `x ≥ P`. -/
theorem cs_inv_istep {P D y x : ℝ} {Φ : ℤ} (hP : 0 < P) (hx : P ≤ x) (hD : 0 ≤ D) (h :
    loadDifferenceInvariant P D
  y Φ) :
    loadDifferenceInvariant P (D - x) x (Φ - 1) := by
  have h0 := h.1 hD
  have hf0 : 0 ≤ ⌊D / P⌋ := Int.floor_nonneg.2 (div_nonneg hD hP.le)
  refine ⟨fun hD' => ?_, fun _ => ⟨by omega, ?_⟩⟩
  · have h1 : (D - x) / P ≤ D / P - 1 := by
      rw [div_sub_one hP.ne', div_le_div_iff_of_pos_right hP]
      linarith
    have h2 : ⌊(D - x) / P⌋ ≤ ⌊D / P - 1⌋ := Int.floor_le_floor h1
    rw [Int.floor_sub_one] at h2
    omega
  · have e : D - x + x = D := by ring
    rw [e]
    omega

/-- The receiving machine is the first of the pair (`D ≤ 0`): it gains a job `x` with `P ≤ x ≤ y`.
-/
theorem cs_inv_hstep {P D y x : ℝ} {Φ : ℤ} (hP : 0 < P) (hx : P ≤ x) (hxy : x ≤ y) (hD : D ≤ 0)
    (h : loadDifferenceInvariant P D y Φ) : loadDifferenceInvariant P (D + x) x (Φ + ⌊x / P⌋) := by
  have hf1 : 1 ≤ ⌊x / P⌋ := by
    rw [Int.le_floor, Int.cast_one, le_div_iff₀ hP]
    linarith
  rcases hD.lt_or_eq with hD | hD
  · obtain ⟨hm1, hy⟩ := h.2 hD
    refine ⟨fun hD' => ?_, fun hD' => ⟨by omega, ?_⟩⟩
    · have h1 : ⌊(D + x) / P⌋ ≤ ⌊(D + y) / P⌋ :=
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hP.le)
      omega
    · have h1 : ⌊(D + x + x) / P⌋ ≤ ⌊x / P⌋ :=
        Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith) hP.le)
      omega
  · subst hD
    have h0 := h.1 le_rfl
    simp only [zero_div, Int.floor_zero] at h0
    refine ⟨fun _ => ?_, fun hD' => absurd hD' (by linarith)⟩
    rw [zero_add]
    omega

theorem cs_cnt_le_fl {m n : ℕ} (p : Fin n → ℝ) {P : ℝ} (hP : 0 < P) (σ : Fin n → Fin m) (k : ℕ)
    (hk : ∀ j : Fin n, (j : ℕ) < k → P ≤ p j) (i : Fin m) : prefixJobCount σ k i ≤ prefixJobWeight
        p P σ k i := by
  unfold prefixJobCount prefixJobWeight
  refine Finset.sum_le_sum fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj
  rw [Int.le_floor, Int.cast_one, le_div_iff₀ hP, one_mul]
  exact hk j hj.1

theorem cs_cnt_zero {m n : ℕ} (σ : Fin n → Fin m) (i : Fin m) : prefixJobCount σ 0 i = 0 := by
  simp [prefixJobCount]

theorem cs_fl_zero {m n : ℕ} (p : Fin n → ℝ) (P : ℝ) (σ : Fin n → Fin m) (i : Fin m) :
    prefixJobWeight p P σ
  0 i = 0 := by
  simp [prefixJobWeight]

/-- The invariant along a list schedule in nonincreasing order, for every pair of machines. -/
theorem cs_inv_all {m n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (σ : Fin n → Fin m)
    (hσ : IsListSchedule p σ) {P : ℝ} (hP : 0 < P) :
    ∀ k : ℕ, k ≤ n → (∀ j : Fin n, (j : ℕ) < k → P ≤ p j) → ∀ h g : Fin m, ∀ y : ℝ,
      (∀ j : Fin n, (j : ℕ) + 1 = k → y ≤ p j) →
      loadDifferenceInvariant P (loadBefore p σ k h - loadBefore p σ k g) y (prefixJobWeight p P σ
          k h - prefixJobCount σ k g) := by
  intro k
  induction k with
  | zero =>
    intro _ _ h g y _
    rw [bs_loadBefore_zero, bs_loadBefore_zero, cs_fl_zero, cs_cnt_zero, sub_self, sub_self]
    exact cs_inv_self le_rfl
  | succ k ih =>
    intro hk hPk h g y hy
    set kk : Fin n := ⟨k, by omega⟩ with hkk
    have hkv : (kk : ℕ) = k := rfl
    have hPk' : ∀ j : Fin n, (j : ℕ) < k → P ≤ p j := fun j hj => hPk j (by omega)
    have hx : P ≤ p kk := hPk kk (by simp [kk])
    have hyx : y ≤ p kk := hy kk (by simp [kk])
    have IH := ih (by omega) hPk' h g (p kk) (fun j hj => hanti (show j ≤ kk from Fin.le_def.2
      (by omega)))
    by_cases hhg : h = g
    · subst hhg
      rw [sub_self]
      refine cs_inv_self ?_
      have := cs_cnt_le_fl p hP σ (k + 1) hPk h
      omega
    have eL : ∀ i, loadBefore p σ (k + 1) i = loadBefore p σ k i + if σ kk = i then p kk else 0 :=
      fun i => bs_loadBefore_succ p σ kk i
    have eF : ∀ i, prefixJobWeight p P σ (k + 1) i = prefixJobWeight p P σ k i + if σ kk = i then
        ⌊p kk / P⌋ else 0 :=
      fun i => sum_prefix_succ (fun j => ⌊p j / P⌋) σ kk i
    have eC : ∀ i, prefixJobCount σ (k + 1) i = prefixJobCount σ k i + if σ kk = i then 1 else 0 :=
      fun i => sum_prefix_succ (fun _ => (1 : ℤ)) σ kk i
    have hmin : ∀ i, loadBefore p σ k (σ kk) ≤ loadBefore p σ k i := fun i => hσ kk i
    rw [eL h, eL g, eF h, eC g]
    by_cases h1 : σ kk = h
    · have h2 : σ kk ≠ g := fun e => hhg (h1.symm.trans e)
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2, add_zero, add_zero]
      have hD : loadBefore p σ k h - loadBefore p σ k g ≤ 0 := by
        have := hmin g
        rw [h1] at this
        linarith
      have := cs_inv_hstep hP hx le_rfl hD IH
      have e1 : loadBefore p σ k h + p kk - loadBefore p σ k g =
          loadBefore p σ k h - loadBefore p σ k g + p kk := by ring
      have e2 : prefixJobWeight p P σ k h + ⌊p kk / P⌋ - prefixJobCount σ k g =
          prefixJobWeight p P σ k h - prefixJobCount σ k g + ⌊p kk / P⌋ := by ring
      rw [e1, e2]
      exact cs_inv_mono hP this hyx
    · rw [ite_eq_right h1, ite_eq_right h1, add_zero, add_zero]
      by_cases h2 : σ kk = g
      · rw [ite_eq_left h2, ite_eq_left h2]
        have hD : 0 ≤ loadBefore p σ k h - loadBefore p σ k g := by
          have := hmin h
          rw [h2] at this
          linarith
        have := cs_inv_istep hP hx hD IH
        have e1 : loadBefore p σ k h - (loadBefore p σ k g + p kk) =
            loadBefore p σ k h - loadBefore p σ k g - p kk := by ring
        have e2 : prefixJobWeight p P σ k h - (prefixJobCount σ k g + 1) = prefixJobWeight p P σ k
            h - prefixJobCount σ k g - 1 := by
          ring
        rw [e1, e2]
        exact cs_inv_mono hP this hyx
      · rw [ite_eq_right h2, ite_eq_right h2, add_zero, add_zero]
        exact cs_inv_mono hP IH hyx

/-- Every machine weighs at least the number of jobs on the machine that receives job `k`, before
`k`. -/
theorem cs_cnt_le_fl_of_min {m n : ℕ} (p : Fin n → ℝ) (hanti : Antitone p) (σ : Fin n → Fin m)
    (hσ : IsListSchedule p σ) {P : ℝ} (hP : 0 < P) (k : Fin n) (hk : ∀ j : Fin n, (j : ℕ) < k → P
      ≤ p j)
    (h : Fin m) : prefixJobCount σ k (σ k) ≤ prefixJobWeight p P σ k h := by
  have hI := cs_inv_all p hanti σ hσ hP k k.isLt.le hk h (σ k) P (fun j hj => hk j (by omega))
  have hD : 0 ≤ loadBefore p σ k h - loadBefore p σ k (σ k) := sub_nonneg.2 (hσ k h)
  have h1 := hI.1 hD
  have h2 : 0 ≤ ⌊(loadBefore p σ k h - loadBefore p σ k (σ k)) / P⌋ := Int.floor_nonneg.2
    (div_nonneg hD hP.le)
  omega

/-- Chen's property, sorted form: job `k` is the `(c + 1)`-th job on its machine, `c` the jobs of
smaller index
there; then `(c + 1) · p_k ≤ C(τ)` for every assignment `τ`. -/
theorem lpt_job_position_le {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (k : Fin n) (τ : Fin n → Fin m) :
    (((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = σ k)).card : ℝ) + 1) * p k ≤ makespan p τ
      := by
  set c := (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = σ k)).card with hc
  have hτ0 : 0 ≤ makespan p τ := bs_makespan_nonneg p hp τ
  rcases (hp k).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact hτ0
  by_contra hlt
  push Not at hlt
  have hk : ∀ j : Fin n, (j : ℕ) < (k : ℕ) + 1 → p k ≤ p j := fun j hj => hanti (Fin.le_def.2
    (by omega))
  have hk' : ∀ j : Fin n, (j : ℕ) < k → p k ≤ p j := fun j hj => hk j (by omega)
  have hcnt : prefixJobCount σ k (σ k) = (c : ℤ) := by simp [prefixJobCount, hc]
  have e : univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1) =
      insert k (univ.filter (fun j : Fin n => (j : ℕ) < k)) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro h1
      by_cases hjk : j = k
      · exact Or.inl hjk
      · have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
        exact Or.inr (by omega)
    · rintro (rfl | h1) <;> omega
  have hlow : (m : ℤ) * c + 1 ≤ ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1), ⌊p j /
    p k⌋ := by
    rw [e, sum_insert (by simp), div_self hpos.ne', Int.floor_one,
      ← sum_prefix_fiber (fun j => ⌊p j / p k⌋) σ k]
    have h1 : ∑ _i : Fin m, (c : ℤ) ≤
        ∑ i, ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i), ⌊p j / p k⌋ :=
      Finset.sum_le_sum fun i _ => by
        have := cs_cnt_le_fl_of_min p hanti σ hσ hpos k hk' i
        rw [hcnt] at this
        exact this
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    linarith
  have hfib : ∀ g : Fin m,
      ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ τ j = g), ⌊p j / p k⌋ ≤ (c : ℤ)
        := by
    intro g
    have h1 : ((∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ τ j = g), ⌊p j / p k⌋
      : ℤ) : ℝ) ≤
        loadBefore p τ ((k : ℕ) + 1) g / p k := by
      push_cast
      unfold loadBefore
      rw [sum_div]
      exact sum_le_sum fun j _ => Int.floor_le _
    have h2 := (bs_loadBefore_le_load p hp τ ((k : ℕ) + 1) g).trans (load_le_makespan p τ g)
    have h3 : loadBefore p τ ((k : ℕ) + 1) g / p k < (c : ℝ) + 1 := by
      rw [div_lt_iff₀ hpos]
      linarith
    have h4 : ((∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ τ j = g), ⌊p j / p k⌋
      : ℤ) : ℝ) <
        ((c : ℤ) : ℝ) + 1 := by
      have h5 := h1.trans_lt h3
      push_cast at h5 ⊢
      linarith
    have h5 : (∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1 ∧ τ j = g), ⌊p j / p k⌋ :
      ℤ) <
        (c : ℤ) + 1 := by exact_mod_cast h4
    omega
  have hup : ∑ j ∈ univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ) + 1), ⌊p j / p k⌋ ≤ (m : ℤ) * c
    := by
    rw [← sum_prefix_fiber (fun j => ⌊p j / p k⌋) τ ((k : ℕ) + 1)]
    have h1 := Finset.sum_le_sum fun g (_ : g ∈ (univ : Finset (Fin m))) => hfib g
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    exact h1
  omega

/-- The Coffman–Sethi form, sorted: a machine `i` attaining the makespan of a list schedule in
nonincreasing order,
holding `k` jobs, gives `k·m·C(σ) ≤ ((k + 1)m − 1)·C(τ)` for every assignment `τ`. -/
theorem cs_bound {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p)
    (σ : Fin n → Fin m) (hσ : IsListSchedule p σ) (τ : Fin n → Fin m) (i : Fin m)
    (hi : load p σ i = makespan p σ) :
    ((univ.filter (fun j : Fin n => σ j = i)).card : ℝ) * m * makespan p σ ≤
      (((univ.filter (fun j : Fin n => σ j = i)).card + 1) * m - 1) * makespan p τ := by
  have hm : (1 : ℝ) ≤ m := by
    have := NeZero.ne m
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hτ0 : 0 ≤ makespan p τ := bs_makespan_nonneg p hp τ
  rcases (univ.filter (fun j : Fin n => σ j = i)).eq_empty_or_nonempty with hE | hne
  · have h0 : makespan p σ = 0 := by
      rw [← hi]
      unfold load
      rw [hE, sum_empty]
    rw [hE, h0, card_empty, Nat.cast_zero, mul_zero]
    exact mul_nonneg (by linarith) hτ0
  · obtain ⟨k, hkF, hkmax⟩ := Finset.exists_max_image _ (fun j : Fin n => (j : ℕ)) hne
    have hki : σ k = i := by simpa using hkF
    have eF : univ.filter (fun j : Fin n => σ j = i) =
        insert k (univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · intro hj
        have h1 : (j : ℕ) ≤ k := hkmax j (by simp [hj])
        by_cases hjk : j = k
        · exact Or.inl hjk
        · have : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
          exact Or.inr ⟨by omega, hj⟩
      · rintro (rfl | ⟨_, h2⟩)
        · exact hki
        · exact h2
    have hknot : k ∉ univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = i) := by simp
    have hcard : (((univ.filter (fun j : Fin n => σ j = i)).card : ℕ) : ℝ) =
        ((univ.filter (fun j : Fin n => (j : ℕ) < k ∧ σ j = σ k)).card : ℝ) + 1 := by
      rw [eF, card_insert_of_notMem hknot, hki]
      push_cast
      ring
    have hload : makespan p σ = loadBefore p σ k (σ k) + p k := by
      rw [← hi, hki]
      unfold load loadBefore
      rw [eF, sum_insert hknot]
      ring
    have hchen := lpt_job_position_le p hp hanti σ hσ k τ
    rw [← hcard] at hchen
    have h1 := bs_mul_loadBefore_le p σ hσ k
    have h2 := bs_sum_filter_add_le p hp k
    have h3 := sum_le_mul_makespan p τ
    have hmC : (m : ℝ) * makespan p σ ≤ m * makespan p τ + (m - 1) * p k := by
      rw [hload]
      linarith
    have hc0 : (0 : ℝ) ≤ ((univ.filter (fun j : Fin n => σ j = i)).card : ℝ) := Nat.cast_nonneg _
    have h4 := mul_le_mul_of_nonneg_left hmC hc0
    have h5 := mul_le_mul_of_nonneg_left hchen (by linarith : (0 : ℝ) ≤ m - 1)
    nlinarith

/-- The Coffman–Sethi form of the LPT bound: if a machine `i` attaining the makespan of an LPT
schedule holds `q` jobs,
then `q·m · C(σ) ≤ ((q + 1)m − 1) · C(τ)` for every assignment `τ` (Coffman–Sethi 1976 as
corrected by Chen 1993, as
Della Croce and Scatamacchia restate it; the literature states it for `q ≥ 3`; for `m ≥ 2` it is
weaker than
`lpt_bound` at `q ≤ 2`, and its attainment is not proved here). -/
theorem lpt_bound_of_card {m n : ℕ} [NeZero m] (p : Fin n → ℝ) (hp : ∀ j, 0 ≤ p j)
    (σ : Fin n → Fin m) (hσ : IsLPTSchedule p σ) (τ : Fin n → Fin m) (i : Fin m)
    (hi : load p σ i = makespan p σ) :
    ((univ.filter (fun j : Fin n => σ j = i)).card : ℝ) * m * makespan p σ ≤
      (((univ.filter (fun j : Fin n => σ j = i)).card + 1) * m - 1) * makespan p τ := by
  obtain ⟨π, hanti, hl⟩ := hσ
  have hi' : load (p ∘ π) (σ ∘ π) i = makespan (p ∘ π) (σ ∘ π) := by
    rw [bs_load_comp, makespan_comp, hi]
  have h := cs_bound (p ∘ π) (fun j => hp _) hanti (σ ∘ π) hl (τ ∘ π) i hi'
  have hcard : (univ.filter (fun j : Fin n => (σ ∘ π) j = i)).card =
      (univ.filter (fun j : Fin n => σ j = i)).card :=
    Finset.card_equiv π (fun j => by simp)
  rwa [hcard, makespan_comp, makespan_comp] at h

end GrahamLPT
