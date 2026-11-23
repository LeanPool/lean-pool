/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.AsymRay
public import LeanPool.Egyptian.BellmanScore
public import LeanPool.Egyptian.TerminalTuples
public import LeanPool.Egyptian.UnitBest
import Mathlib.Tactic.Positivity.Finset

/-! The finite-ray induction in §4, including uniqueness at unit states. -/

@[expose] public section

namespace Egyptian.Control

/-- Stopping at two indices of the same infinite sequence gives the same ray. -/
def winningRays (s : State) : Set (ℕ → ℕ) :=
  {a | ∃ xs T, Wins .weak s xs T ∧ a = unitRay xs T}

/-- A finite union of the finite families of maximizing continuations. -/
theorem finite_rays_of_branches {s : State} {F : Set (List ℕ)} (hF : F.Finite)
    (hsub : ∀ b ∈ F, (winningRays (finish s b)).Finite)
    (hcover : ∀ xs T, Wins .weak s xs T →
      ∃ b ∈ F, ∃ ys, xs = b ++ ys ∧ Wins .weak (finish s b) ys T) :
    (winningRays s).Finite := by
  have hfin := hF.biUnion (t := fun b => prepend b '' winningRays (finish s b))
    (fun b hb => (hsub b hb).image (prepend b))
  apply hfin.subset
  rintro a ⟨xs,T,hw,rfl⟩
  obtain ⟨b,hb,ys,rfl,hs⟩ := hcover xs T hw
  exact Set.mem_iUnion.2 ⟨b,Set.mem_iUnion.2 ⟨hb,unitRay ys T, ⟨ys,T,hs,rfl⟩,
    (prepend_append b ys _).symm⟩⟩

/-- If the starting reciprocal is U, a terminal attaining the unit boundary
score has exactly the first r greedy digits, even for repeated denominators. -/
theorem greedy_ray_of_unit_score {s : State} {xs : List ℕ} {T U : ℕ}
    (hv : Valid s) (hU : 1 ≤ U) (hs : s.q = s.p * U)
    (ht : Terminal .weak s xs T) (hscore : score xs T = Payoff.value (U : ℝ)) :
    unitRay xs T = unitRay [] U := by
  have hreal (j : ℕ) : (1 : ℝ) ≤ unitIter U j := by
    exact_mod_cast unitIter_pos hU j
  have hg := (div_eq_iff (by positivity : (2 : ℝ)^xs.length ≠ 0)).1 hscore
  have hval : Payoff.value (T : ℝ) = Payoff.value (unitIter U xs.length : ℝ) := by
    rw [real_unitIter, Payoff.value_orbit (by exact_mod_cast hU : (1:ℝ) ≤ U), hg, mul_comm]
  have htone : (1:ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by have := ht.2.1; omega)
  have heq : (T : ℝ) = unitIter U xs.length :=
    Payoff.value_strictMonoOn.injOn htone (hreal _) hval
  have hT : T = unitIter U xs.length := by exact_mod_cast heq
  obtain ⟨had, _, hfrac⟩ := terminal_to_tuple hv ht
  have hratio : (s.p : ℚ) / s.q = unit U := by
    rw [hs, Nat.cast_mul, unit]
    have hp : (s.p : ℚ) ≠ 0 := by exact_mod_cast hv.1.ne'
    field_simp
  rw [hratio] at had hfrac
  let d := fun i => unitIter U i + 1
  have hsum : recipSum (prefixTuple d xs.length) = recipSum xs := by
    apply (Rat.cast_injective (α := ℝ))
    rw [real_prefix_sum]
    have hh := unitPrefixSum U xs.length (by omega)
    have hr := congrArg (fun z : ℚ => (z : ℝ)) hfrac
    simp only [unit, Rat.cast_one, Rat.cast_add, Rat.cast_div, Rat.cast_natCast, hT] at hr
    simpa only [d, Nat.cast_add, Nat.cast_one] using (hh.trans (by linarith))
  have hxs : xs = prefixTuple d xs.length := by
    by_cases hz : xs.length = 0
    · simp_all [prefixTuple]
    · obtain ⟨hg, huniq⟩ := uniqueUnitTails .weak U xs.length hU (by omega)
      rw [greedyTuple_unit .weak hU, digits_eq_prefix] at hg huniq
      apply huniq xs
      refine ⟨had, fun es he => ?_⟩
      exact (hg.2 es he).trans hsum.le
  have htail (j : ℕ) : unitIter T j + 1 = d (xs.length + j) := by
    simp only [d, hT, unitIter_add]
  have hprepend := prepend_prefix_cancel d xs.length
  change prepend xs (fun j => unitIter T j + 1) = d
  calc
    _ = prepend xs (fun j => d (xs.length+j)) := congrArg (prepend xs) (funext htail)
    _ = prepend (prefixTuple d xs.length) (fun j => d (xs.length+j)) :=
      congrArg (fun p => prepend p (fun j => d (xs.length+j))) hxs
    _ = d := hprepend

/-- At a divisible state, all maximizing decompositions give the unique greedy
ray, regardless of where they stop. -/
theorem finite_rays_unit {s : State} (hv : Valid s) (hd : s.p ∣ s.q)
    (heq : ∀ xs T, Wins .weak s xs T → score xs T = Payoff.value (inverseRemainder s)) :
    (winningRays s).Finite := by
  obtain ⟨U, hU⟩ := hd
  have hUpos : 1 ≤ U := by
    by_contra! h
    have hzero : U = 0 := by omega
    rw [hzero, Nat.mul_zero] at hU
    exact hv.2.ne' hU
  have hratio : inverseRemainder s = U := by
    have hp : (s.p : ℝ) ≠ 0 := by exact_mod_cast hv.1.ne'
    simp [inverseRemainder, hU, Nat.cast_mul, hp]
  apply (Set.finite_singleton (unitRay [] U)).subset
  rintro a ⟨xs,T,hw,rfl⟩
  exact greedy_ray_of_unit_score hv hUpos hU hw.1 (hratio ▸ heq xs T hw)

end Egyptian.Control
