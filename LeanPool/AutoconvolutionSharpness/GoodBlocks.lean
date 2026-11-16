/-
Copyright (c) 2026 Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tonći Crmarić, Vjekoslav Kovač, Jelena Rupčić
-/
module

public import LeanPool.AutoconvolutionSharpness.BlockKeys
public import LeanPool.AutoconvolutionSharpness.Occupancy
public import LeanPool.AutoconvolutionSharpness.Estimate

/-!
# Enumerating the plateaus

The index of a plateau records its level and the sets of digits selected on
each side. Its start is `D * peakCode D x`, its width is `x.1`, and its
height is `Estimate.height n x.1`. `peakCode_injOn` and `peak_sum` let the
analysis use this family directly without listing any example numerically.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Autoconvolutions.Blocks

abbrev Peak (m : ℕ) := Σ _s : ℕ, (Fin m → ℕ) × (Fin m → ℕ)

/-- For each plateau use its level and the two zero / one multiplicity vectors. -/
noncomputable def peakSet {m : ℕ} (I J : Finset (Fin m)) (n K : ℕ) : Finset (Peak m) :=
  (range (K + 1)).sigma (fun s => goodVectors I (2 * n - s) ×ˢ goodVectors J (2 * n + s))

/-- Divide the block start by `D`, so a single unit of this index separates two blocks. -/
def peakCode {m : ℕ} (D : ℕ) (x : Peak m) : ℕ := code D x.2.1 + code D x.2.2

theorem peak_mem {m n K : ℕ} {I J : Finset (Fin m)} {x : Peak m} (hx : x ∈ peakSet I J n K) :
    x.1 ≤ K ∧ x.2.1 ∈ goodVectors I (2 * n - x.1) ∧ x.2.2 ∈ goodVectors J (2 * n + x.1) := by
  simpa only [peakSet, Finset.mem_sigma, Finset.mem_range, Nat.lt_succ_iff,
    Finset.mem_product] using hx

theorem peak_row {m n K D h : ℕ} {I J : Finset (Fin m)} {x : Peak m}
    (hx : x ∈ peakSet I J n K) (hh : h < D) :
    (x.2,h) ∈ rows I J (2 * n - x.1) (2 * n + x.1) D :=
  mem_rows.mpr ⟨(goodVectors_spec (peak_mem hx).2.1).1,
    (goodVectors_spec (peak_mem hx).2.2).1, hh⟩

@[simp] theorem peak_rowKey {m : ℕ} (x : Peak m) (D h : ℕ) :
    rowKey D (x.2,h) = D * peakCode D x + h := by
  simp [rowKey, key, peakCode, Nat.add_comm]

/-- Distinct peak indices have distinct starts, even when their levels differ. -/
theorem peakCode_injOn {m n K D : ℕ} {I J : Finset (Fin m)}
    (hD : 1 < D) (hd : Disjoint I J) (hK : K ≤ n) (hnD : 4 * n < D) :
    Set.InjOn (peakCode D) (↑(peakSet I J n K) : Set (Peak m)) := by
  intro x hx y hy he
  have hx' := peak_mem hx
  have hy' := peak_mem hy
  have ht := rowKey_determines_level hD hd (by omega : x.1 ≤ 2 * n) (by omega : y.1 ≤ 2 * n)
    hnD (peak_row hx (by omega : 0 < D)) (peak_row hy (by omega : 0 < D))
    (by simpa only [peak_rowKey, Nat.add_zero] using congrArg (D * ·) he)
  obtain ⟨s, a,b⟩ := x
  obtain ⟨t, c,d⟩ := y
  obtain ⟨hst, hab⟩ := ht
  have hh : (a,b) = (c,d) := congrArg Prod.fst hab
  cases hst
  cases hh
  rfl

/-- Summing `s A_s²` once per plateau gives exactly the binomial sum in §2. -/
theorem peak_sum {m : ℕ} (I J : Finset (Fin m)) (n K : ℕ) :
    (∑ x ∈ peakSet I J n K, (x.1 : ℝ) * (Estimate.height n x.1) ^ 2) =
      ∑ s ∈ range (K + 1), (s : ℝ) * Estimate.count n I.card J.card s * (Estimate.height n s) ^ 2
          := by
  rw [peakSet, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.sum_const, card_goodPairs, nsmul_eq_mul, Nat.cast_mul, Estimate.count]
  ring

end Autoconvolutions.Blocks
