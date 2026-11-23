/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.AsymptoticDefs
public import LeanPool.Egyptian.AsymRay
public import LeanPool.Egyptian.UnitBest
import Mathlib.Tactic.Positivity.Finset

/-! Constructing the infinite benchmark in the introduction from the compatible
optimal finite prefixes. Advancing by one greedy term also handles T = 1. -/

@[expose] public section

namespace Egyptian

open Filter
open scoped Topology

/-- The reciprocal series of the unshifted unit-fraction ray sums to `1/T`. -/
theorem unitRay_hasSum (T : ℕ) (hT : 1 ≤ T) :
    HasSum (fun i : ℕ => 1 / ((unitIter T i + 1 : ℕ) : ℝ)) (1 / (T:ℝ)) := by
  have h0 : Tendsto (fun i : ℕ => 1 / (unitIter T i : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (unitIter_strictMono hT).tendsto_atTop)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).2
  have h := (tendsto_const_nhds (x := 1/(T:ℝ)) (f := atTop)).sub h0
  rw [sub_zero] at h
  exact h.congr (fun i => by simpa only [Nat.cast_add, Nat.cast_one] using
    (unitPrefixSum T i hT).symm)

private theorem prepend_lower (p : List ℕ) (f : ℕ → ℕ) {k : ℕ}
    (hp : ∀ d ∈ p, k ≤ d) (hf : ∀ i, k ≤ f i) (i : ℕ) : k ≤ prepend p f i := by
  induction p generalizing i with
  | nil => exact hf i
  | cons d p ih =>
    cases i with
    | zero => exact hp d (by simp)
    | succ i => exact ih (fun x hx => hp x (by simp [hx])) i

private theorem prepend_mono (p : List ℕ) (f : ℕ → ℕ) (hp : p.Pairwise (· ≤ ·))
    (hf : Monotone f) (hc : ∀ d ∈ p, d ≤ f 0) : Monotone (prepend p f) := by
  induction p with
  | nil => exact hf
  | cons d p ih =>
    apply monotone_nat_of_le_succ
    intro i
    rcases i with _ | i
    · exact prepend_lower p f (List.pairwise_cons.mp hp).1
        (fun j => (hc d (by simp)).trans (hf (Nat.zero_le j))) 0
    · exact ih (List.pairwise_cons.mp hp).2 (fun x hx => hc x (by simp [hx])) (Nat.le_succ i)

/-- A legal prefix and its ordered greedy unit tail sum to exactly q. -/
theorem expansion_unitRay {q : ℚ} {ds : List ℕ} {T : ℕ} (hT : 1 ≤ T)
    (hds : Admissible .weak q ds.length ds) (hordered : ∀ d ∈ ds, d ≤ T + 1)
    (hsplit : q = recipSum ds + unit T) : Expansion q (unitRay ds T) := by
  have hp := unitIter_pos hT
  have hm : Monotone (fun j => unitIter T j + 1) :=
    fun _ _ h => Nat.add_le_add_right ((unitIter_strictMono hT).monotone h) 1
  refine ⟨prepend_lower _ _ hds.2.1 (fun j => by have := hp j; omega),
    prepend_mono _ _ hds.2.2.1 hm hordered, ?_⟩
  apply (hasSum_nat_add_iff' (f := fun i => 1/(unitRay ds T i : ℝ)) ds.length).mp
  have hz : prefixTuple (unitRay ds T) ds.length = ds := by
    simpa [prefixTuple, unitRay] using prefix_prepend ds (fun j => unitIter T j + 1) 0
  have hsum : (q:ℝ) - (∑ i ∈ Finset.range ds.length, 1/(unitRay ds T i : ℝ)) = 1/(T:ℝ) := by
    rw [← real_prefix_sum, hz, hsplit, Rat.cast_add, unit, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast]
    ring
  rw [hsum]
  convert unitRay_hasSum T hT using 1
  funext i
  rw [Nat.add_comm i ds.length]
  exact congrArg (fun x : ℕ => 1/(x:ℝ)) (prepend_tail ds _ i)

/-- All finite prefixes of a terminal ray beginning at the compatible prefix
are optimal, and together they give a nondecreasing expansion of q. -/
theorem exists_benchmark_of_compatible (h : CompatibleUnitTails) (q : ℚ) (hq : 0 < q) :
    ∃ b, Benchmark q b := by
  obtain ⟨N, T, p, hN, hT, hs, hp, htail⟩ := h .weak q hq
  let b := unitRay p T
  have hn : p.length = N := hp.1.1
  have hpre (j : ℕ) :
      prefixTuple b (N+j) = p ++ prefixTuple (fun i => unitIter T i + 1) j := by
    rw [← hn]
    exact prefix_prepend _ _ _
  have ht (j : ℕ) : b (N+j) = unitIter T j + 1 := by
    rw [← hn]
    exact prepend_tail _ _ _
  have hbest (n : ℕ) (hh : N ≤ n) : IsBest .weak q n (prefixTuple b n) := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hh
    rw [hpre, ← digits_eq_prefix, ← greedyTuple_unit .weak hT]
    cases j with
    | zero => simpa [greedyTuple, greedyFrom] using hp
    | succ j => exact htail _ (by omega)
  have hordered : ∀ d ∈ p, d ≤ T + 1 := by
    have hpair := (htail 1 le_rfl).1.2.2.1
    rw [greedyTuple_unit .weak hT 1] at hpair
    exact fun d hd => (List.pairwise_append.mp hpair).2.2 d hd (T + 1) (by simp [unitDigits])
  have expansion : Expansion q b := expansion_unitRay hT (hn ▸ hp.1) hordered hs
  refine ⟨b, expansion, N+1, T*(T+1), by omega, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hT, Nat.mul_pos hT hT]
  · rw [hpre, recipSum_append]
    have hunit := unit_sub_unit_succ hT
    have hz : recipSum (prefixTuple (fun i => unitIter T i + 1) 1) = unit (T + 1) := by
      simp [prefixTuple, recipSum, unitIter]
    rw [hz]
    linarith
  · intro j
    rw [show N+1+j=N+(j+1) by omega, ht, unitIter_step_start]
  · exact fun n h => hbest n (by omega)

end Egyptian
