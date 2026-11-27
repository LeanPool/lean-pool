/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageFiniteScan
import Mathlib.Tactic.Positivity

/-!
# Computable exact minimization over the finite syndrome space

The syndrome is recovered by finite search, not supplied as rank-many advice
bits. Ties retain the first minimizer in the explicit binary-word enumeration.
The computation is uniform in every parameter of the rational objective.
-/

@[expose] public section

namespace Klr.StageSyndrome

open SparseSearch RationalComputability

/-- The first index minimizing a rational cost on `0, ..., n`. -/
def minIndex (cost : ℕ → ℚ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if cost (minIndex cost n) ≤ cost (n + 1) then minIndex cost n else n + 1

theorem minIndex_le (cost : ℕ → ℚ) (n : ℕ) : minIndex cost n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [minIndex]; split <;> omega

theorem cost_minIndex_le (cost : ℕ → ℚ) (n k : ℕ) (hk : k ≤ n) :
    cost (minIndex cost n) ≤ cost k := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    rw [minIndex]
    split_ifs with h
    · rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact h
      · exact ih (by omega)
    · rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · rfl
      · exact (le_of_lt (lt_of_not_ge h)).trans (ih (by omega))

/-- Exact rational comparison makes the bounded minimization computable. -/
theorem computable_minIndex {α : Type*} [Primcodable α] {cost : α → ℕ → ℚ}
    (hc : Computable₂ cost) :
    Computable (fun p : α × ℕ => minIndex (cost p.1) p.2) := by
  have ha : Computable (fun p : (α × ℕ) × (ℕ × ℕ) => p.1.1) :=
    Computable.fst.comp Computable.fst
  have hp : Computable (fun p : (α × ℕ) × (ℕ × ℕ) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hn : Computable (fun p : (α × ℕ) × (ℕ × ℕ) => p.2.1 + 1) :=
    Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)
  have hle := primrec_rat_le.decide.to_comp.comp (hc.comp ha hp) (hc.comp ha hn)
  have hs := Computable.cond hle hp hn
  apply (Computable.nat_rec Computable.snd (Computable.const 0) hs.to₂).of_eq
  intro p
  induction p.2 with
  | zero => rfl
  | succ n ih =>
    simpa only [Nat.rec_add_one, Bool.cond_decide, minIndex] using
      congrArg (fun k => if cost p.1 k ≤ cost p.1 (n + 1) then k else n + 1) ih

/-- The finite syndrome minimizing the supplied exact rational objective. -/
def choose (r : ℕ) (cost : List Bool → ℚ) : List Bool :=
  let ys := words r
  ys.getD (minIndex (fun k => cost (ys.getD k [])) (ys.length - 1)) []

theorem choose_mem (r : ℕ) (cost : List Bool → ℚ) : choose r cost ∈ words r := by
  have hpos : 0 < (words r).length := by rw [PoolAdvice.length_words]; positivity
  have hk : minIndex (fun k => cost ((words r).getD k [])) ((words r).length - 1) <
      (words r).length := lt_of_le_of_lt (minIndex_le _ _) (by omega)
  unfold choose
  rw [List.getD_eq_getElem _ [] hk]
  exact List.getElem_mem _

@[simp] theorem length_choose (r : ℕ) (cost : List Bool → ℚ) :
    (choose r cost).length = r := (mem_words_iff _ _).mp (choose_mem r cost)

theorem choose_min (r : ℕ) (cost : List Bool → ℚ) (y : List Bool) (hy : y.length = r) :
    cost (choose r cost) ≤ cost y := by
  obtain ⟨k, hk, hky⟩ := List.getElem_of_mem ((mem_words_iff r y).mpr hy)
  have h := cost_minIndex_le (fun k => cost ((words r).getD k []))
    ((words r).length - 1) k (by omega)
  simpa only [choose, List.getD_eq_getElem _ [] hk, hky] using h

/-- The chosen cost is at most the average over every possible syndrome. -/
theorem choose_le_average (r : ℕ) (cost : List Bool → ℚ) :
    cost (choose r cost) ≤ PoolAdvice.average r cost := by
  have h := List.length_nsmul_le_sum ((words r).map cost) (cost (choose r cost)) (by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
    exact choose_min r cost y ((mem_words_iff _ _).mp hy))
  have hp : (0 : ℚ) < 2 ^ r := by positivity
  apply (le_div_iff₀ hp).mpr
  simpa [PoolAdvice.average, PoolAdvice.length_words, nsmul_eq_mul, mul_comm] using h

/-- The minimizer is a total computation, even when the number of syndrome
bits and the entire rational objective vary with the reconstruction input. -/
theorem computable_choose {α : Type*} [Primcodable α] {r : α → ℕ}
    {cost : α → List Bool → ℚ} (hr : Computable r) (hc : Computable₂ cost) :
    Computable (fun a => choose (r a) (cost a)) := by
  have hy := computable_words.comp hr
  have hg := (Primrec.list_getD []).to_comp.comp (hy.comp Computable.fst) Computable.snd
  have hf := hc.comp Computable.fst hg
  have hn := Primrec.nat_sub.to_comp.comp (Computable.list_length.comp hy) (Computable.const 1)
  have hk := (computable_minIndex (cost := fun a k => cost a ((words (r a)).getD k [])) hf).comp
    (Computable.id.pair hn)
  exact (Primrec.list_getD []).to_comp.comp hy hk

end Klr.StageSyndrome
