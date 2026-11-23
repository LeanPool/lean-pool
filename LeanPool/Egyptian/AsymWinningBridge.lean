/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BenchmarkBridge
public import LeanPool.Egyptian.WinningRays
public import LeanPool.Egyptian.Asymptotic
public import LeanPool.Egyptian.AsymGrowth

/-!
# Expansions sharing the benchmark tail are winning rays

Cut one step after a common tail point. The preceding denominator is then
strictly smaller than the new terminal reciprocal. The resulting terminal ray
has the benchmark limit. Any competing terminal ray is an expansion of the
same rational, and its known limit is bounded by that of the benchmark.
-/

public section

namespace Egyptian.Control

open Filter
open scoped Topology

private theorem rebase_iter (T i j : ℕ) :
    unitIter T (i+j) = unitIter (unitIter T i) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun z => z*(z+1)) ih

private theorem iter_ge_two {T : ℕ} (hT : 2 ≤ T) (j : ℕ) : 2 ≤ unitIter T j := by
  induction j with
  | zero => exact hT
  | succ j ih =>
    change 2 ≤ unitIter T j * (unitIter T j+1)
    exact ih.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

private theorem ray_limit (ds : List ℕ) {T : ℕ} (hT : 1 ≤ T) :
    Tendsto (growth (unitRay ds T)) atTop (𝓝 (Real.exp (score ds T / 2))) := by
  have h := terminal_growth (b := unitRay ds T) (N := ds.length) hT
    (fun j => prepend_tail ds _ j)
  simpa only [score, pow_succ, ← div_div] using h

theorem equal_tail_subset_winningRays (s : State) (hv : Valid s) (hzero : s.last = 0)
    {b : ℕ → ℕ} (hb : Benchmark ((s.p : ℚ) / s.q) b) :
    {c : ℕ → ℕ | Expansion ((s.p : ℚ)/s.q) c ∧ ∃ K, ∀ n, K ≤ n → c n = b n}
      ⊆ winningRays s := by
  rintro c ⟨hc, K, heq⟩
  obtain ⟨N,T,_,hT,_,htail,_⟩ := hb.2
  let P := N+K+1
  let U := unitIter T (K+1)
  let xs := prefixTuple c P
  have hp : xs.length = P := by simp [xs, prefixTuple]
  have hU : 2 ≤ U := iter_ge_two hT _
  have hlast : c (N+K) < U := by
    have htwo := iter_ge_two hT K
    rw [heq _ (by omega), htail]
    change unitIter T K + 1 < unitIter T K * (unitIter T K + 1)
    nlinarith [Nat.mul_le_mul_right (unitIter T K+1) htwo]
  have hxs : ∀ d ∈ xs, d < U := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
    have hi' : i < P := List.mem_range.mp hi
    exact (hc.2.1 (show i ≤ N+K by dsimp [P] at hi'; omega)).trans_lt hlast
  have ht (j : ℕ) : c (P+j) = unitIter U j+1 := by
    rw [heq _ (by dsimp [P]; omega), show P+j = N+((K+1)+j) by dsimp [P]; omega,
      htail, rebase_iter]
  have hrepr : c = unitRay xs U := by
    have hh := funext ht
    rw [← prepend_prefix_cancel c P, hh]
    rfl
  have hsum := (expansion_tail hc P).2.2.2
  have hsum' : HasSum (fun j : ℕ => 1/((unitIter U j+1 : ℕ):ℝ))
      ((↑((s.p:ℚ)/s.q - recipSum xs)) : ℝ) := by
    simpa only [ht] using hsum
  have he := hsum'.unique (unitRay_hasSum U (by omega))
  have he' : (s.p:ℚ)/s.q - recipSum xs = unit U := by
    apply (Rat.cast_injective (α := ℝ))
    simpa [unit] using he
  have had := admissible_prefix hc P
  have hterm := terminal_of_tuple (σ := .weak) hv hU (by omega) had.2.1
    (fun d hd => by change s.last ≤ d; omega) had.2.2.1 hxs
    (by linarith : (s.p:ℚ)/s.q = recipSum xs + unit U)
  refine ⟨xs, U, ⟨hterm, ?_⟩, hrepr⟩
  intro ys V hV
  obtain ⟨hy, hbound, hsplit⟩ := terminal_to_tuple hv hV
  have hVpos : 1 ≤ V := by have := hV.2.1; omega
  have hExp := expansion_unitRay hVpos hy (fun d hd => by have := hbound d hd; omega) hsplit
  have hlc : Tendsto (growth c) atTop (𝓝 (Real.exp (score xs U / 2))) := by
    exact hrepr ▸ ray_limit xs (by omega)
  have hlb : Tendsto (growth b) atTop (𝓝 (Real.exp (score xs U / 2))) := by
    apply hlc.congr'
    filter_upwards [eventually_ge_atTop K] with n hn
    simp only [growth, heq n hn]
  have hlow := lowerGrowth_le_benchmark hExp hb hlb
  have hlv := ray_limit ys hVpos
  have hlower : lowerGrowth (unitRay ys V) = (Real.exp (score ys V/2) : EReal) :=
    (EReal.tendsto_coe.2 hlv).liminf_eq
  rw [hlower] at hlow
  have := Real.exp_le_exp.mp (EReal.coe_le_coe_iff.mp hlow)
  linarith

end Egyptian.Control
