/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Fresh
public import Mathlib.Data.Nat.Size


/-!
# Parameters for the cost proof

`proofParams N` follows `docs/PROOF.md` §2.9: `L = max 8 (bits of N)`, `G = 2L`, `T = 3L²`,
`θ = 2L²`, `groupBudget = chunkBudget = 4`. The label widths are chosen so that the label
  conditions hold by
construction: `D = 2^(halvings)` and `B = halvings + pushes + 2`. All widths are `O(L)`.
The top structure: `a = 8`, `s = 11`, `β = 64`, `H = ⌊L/3⌋ + 1`, and `reservationBudget = 8`
  reservation steps
per insertion (M5; `docs/LEAN.md` §14).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model

/-- `L` for capacity `N`. -/
def pL (N : Nat) : Nat := max 8 (Nat.size N)

/-- The parameters of a core of capacity `N`. The label widths are the smallest the conditions
allow: `elementBits − 1 > UG + log₂(G + kG)` and `groupBits − 1 > HC + log₂ PC` (`GParams.push`,
  `LParams.push`). -/
def proofParams (N : Nat) : Params :=
  let L := pL N
  let G := 2 * L
  let T := 3 * L * L
  let kG := G / 3 + 1
  let gmin := (G - 2) / 2
  let UG := G + kG + (kG - gmin)
  let unitsT := T / gmin + 1
  let kCT := unitsT / 3 + 1
  let Mu := unitsT + kCT
  let IC := T + 2 * kCT
  let csB := IC / gmin
  let rsB := 3 * Mu + 1
  let HC := 2 * (csB + rsB)
  let PC := 3 * Mu + rsB + csB
  { N := N
    L := L
    G := G
    T := T
    theta := 2 * L * L
    elementBits := UG + (Nat.log2 (G + kG) + 2)
    groupBits := HC + (Nat.log2 PC + 2)
    elementSpacing := 2 ^ UG
    groupSpacing := 2 ^ HC
    groupBudget := 4
    chunkBudget := 4
    reservationBudget := 8
    a := 8
    s := 11
    beta := 64
    H := L / 3 + 1 }

theorem pL_ge (N : Nat) : 8 ≤ pL N := le_max_left _ _

theorem pow_lt_two_pow (a b : Nat) (h : a < 2 ^ b) (c : Nat) : a * 2 ^ c < 2 ^ (c + b) := by
  rw [pow_add]; nlinarith [Nat.one_le_two_pow (n := c)]

theorem cE_eq (P : Params) : cE P = 2 ^ (P.elementBits - 1) := by
  unfold cE; simp [Nat.shiftLeft_eq]

theorem cG_eq (P : Params) : cG P = 2 ^ (P.groupBits - 1) := by
  unfold cG; simp [Nat.shiftLeft_eq]

/-- **The group-level conditions.** -/
theorem gparams_proof (N : Nat) : GParams (proofParams N) := by
  have hL := pL_ge N
  refine ⟨by simp [proofParams], by simp [proofParams]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [proofParams]; omega
  · simp only [proofParams]; exact Nat.one_le_two_pow
  · simp only [proofParams]; omega
  · rw [cE_eq]
    simp only [proofParams, kG]
    generalize hU : 2 * pL N + (2 * pL N / 3 + 1) + ((2 * pL N / 3 + 1) - (2 * pL N - 2) / 2) = U
    generalize hX : 2 * pL N + (2 * pL N / (4 - 1) + 1) = X
    have h1 : X < 2 ^ (Nat.log2 X + 1) := Nat.lt_log2_self
    have := pow_lt_two_pow _ _ h1 U
    rw [show U + (Nat.log2 X + 2) - 1 = U + (Nat.log2 X + 1) by omega]
    simpa [Nat.mul_comm] using this
  · simp only [proofParams, UG, kG, gmin]; exact le_rfl

/-- The quadratic workload divided by the minimum group size is linear in `L`. -/
theorem costParameterQuotient_le {L : Nat} (hL : 8 ≤ L) :
    3 * L * L / (L - 1) ≤ 3 * L + 4 := by
  apply Nat.div_le_of_le_mul
  have : (L - 1) * (3 * L + 4) = 3 * (L * L) + L - 4 := by
    cases L with
    | zero => omega
    | succ k => simp only [Nat.add_sub_cancel]; ring_nf; omega
  rw [this]; ring_nf; omega

/-- The third-share chunk index inherits the linear workload bound. -/
theorem chunkParameterIndex_le {L q : Nat} (hq : q ≤ 3 * L + 4) :
    (q + 1) / 3 + 1 ≤ L + 3 := by
  omega

/-- The split workload remains linear after adding the two chunk-index contributions. -/
theorem chunkParameterSplit_le {L k : Nat} (hL : 8 ≤ L) (hk : k ≤ L + 3) :
    (3 * L * L + 2 * k) / (L - 1) ≤ 3 * L + 7 := by
  apply Nat.div_le_of_le_mul
  have : (L - 1) * (3 * L + 7) = 3 * (L * L) + 4 * L - 7 := by
    cases L with
    | zero => omega
    | succ j => simp only [Nat.add_sub_cancel]; ring_nf; omega
  rw [this]
  have : 3 * L * L = 3 * (L * L) := by ring
  omega

/-- **The chunk-level conditions**: `c_max ≤ θ`. -/
theorem cparams_proof (N : Nat) : CParams (proofParams N) := by
  have hL := pL_ge N
  refine ⟨by simp [proofParams], ?_⟩
  simp only [cmax, kC, unitsOf, umax, kG, gmin, proofParams]
  generalize pL N = L at hL
  have hg : (2 * L - 2) / 2 = L - 1 := by omega
  rw [hg]
  have hM : 8 * L ≤ L * L := Nat.mul_le_mul_right L hL
  have hq := costParameterQuotient_le hL
  generalize 3 * L * L / (L - 1) = q at hq
  generalize hMM : L * L = M at hM
  have h3 : 3 * L * L = 3 * M := by rw [← hMM]; ring
  have h2 : 2 * L * L = 2 * M := by rw [← hMM]; ring
  rw [h3, h2]
  omega

/-- **The group-label conditions** (Lemma C3, in its coarser form). -/
theorem lparams_proof (N : Nat) : LParams (proofParams N) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [proofParams]; exact Nat.one_le_two_pow
  · simp only [proofParams]; omega
  · have hD : (proofParams N).groupSpacing = 2 ^ HC (proofParams N) := rfl
    have hB : (proofParams N).groupBits = HC (proofParams N) + (Nat.log2 (PC (proofParams N)) +
      2) := rfl
    rw [cG_eq, hB, hD]
    have h1 : PC (proofParams N) < 2 ^ (Nat.log2 (PC (proofParams N)) + 1) := Nat.lt_log2_self
    have := pow_lt_two_pow _ _ h1 (HC (proofParams N))
    rw [show HC (proofParams N) + (Nat.log2 (PC (proofParams N)) + 2) - 1 =
      HC (proofParams N) + (Nat.log2 (PC (proofParams N)) + 1) by omega]
    exact this
  · simp only [proofParams, HC, csB, rsB, Mu, IC, kC, unitsOf, gmin]; exact le_rfl

end OrderMaintenance.Proof
