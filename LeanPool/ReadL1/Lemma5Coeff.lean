/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.QPoly
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# The coefficients of `Qₙ e` (Śliwa's (2), (3) and the identity `y_{m,j} = aₙ eⱼ`)

Śliwa (p. 636) splits `Qₙ e = ∑_{j ≤ cₙ} y_{n,j} xʲ + ∑_{j ≤ vₙ₋₁} z_{n,j} xʲ`, with
`cₙ = (n - 1)aₙ`: the first sum is `∑_{l ≤ cₙ} eₗ fₗ` (`ReadL1.yCoeff`), the second comes from the
`Iₘ,ₘ₋ₙ` blocks above `cₙ` (`ReadL1.zCoeff`). Here:

* `ReadL1.qCoeffCLM_eq_add`: the `j`-th coefficient of `Qₙ e` is `y_{n,j} + z_{n,j}`;
* `ReadL1.zCoeff_eq_zero`: `z_{n,j} = 0` above `vₙ₋₁`;
* `ReadL1.hasSum_zCoeff`: Śliwa's (2), `z_{n,j} = -aₙ ∑_{m > n} e_{j + (m - n)aₘ}`;
* `ReadL1.yCoeff_of_window`: `y_{m,j} = aₙ eⱼ` on `M_{m,n} = ((m - n)aₘ + vₙ₋₂, (m - n)aₘ + vₙ₋₁]`
  (Śliwa p. 637).
-/

@[expose] public section

namespace ReadL1

open Polynomial Finsupp

variable {d : ℕ → ℕ}

/-- Śliwa's `y_{n,j}`: the `j`-th coefficient of `∑_{l ≤ (n - 1)aₙ} eₗ fₗ`. -/
noncomputable def yCoeff (d : ℕ → ℕ) (n j : ℕ) (e : L1) : ℂ :=
  ∑ l ∈ Finset.range ((n - 1) * seqA d n + 1), e l * (fPoly d l).coeff j

/-- Śliwa's `z_{n,j}`: the part of the `j`-th coefficient of `Qₙ e` from indices above
`(n - 1)aₙ`. -/
noncomputable def zCoeff (d : ℕ → ℕ) (n j : ℕ) (e : L1) : ℂ :=
  ∑' l, if (n - 1) * seqA d n < l then e l * (qPolyBasis d n l).coeff j else 0

/-- The index `j + (m - n)aₘ` with `m = n + t + 1`. -/
def zIdx (d : ℕ → ℕ) (n j t : ℕ) : ℕ := j + (t + 1) * seqA d (n + t + 1)

lemma summable_norm_qTerm (h : PartitionHyp d) (n j : ℕ) (e : L1) :
    Summable fun l ↦ ‖e l * (qPolyBasis d n l).coeff j‖ :=
  summable_norm_smul (fun l ↦ (norm_coeff_le_pnorm _ _).trans (pnorm_qPolyBasis_le h n l)) e

lemma summable_ite_of_norm {f : ℕ → ℂ} (hf : Summable fun l ↦ ‖f l‖) (p : ℕ → Prop)
    [DecidablePred p] : Summable fun l ↦ if p l then f l else 0 := by
  refine Summable.of_norm (hf.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun l ↦ ?_)
  split_ifs
  · exact le_rfl
  · rw [norm_zero]; exact norm_nonneg _

/-- **Śliwa's (3)**: the `j`-th coefficient of `Qₙ e` is `y_{n,j} + z_{n,j}`. -/
theorem qCoeffCLM_eq_add (h : PartitionHyp d) (n j : ℕ) (e : L1) :
    qCoeffCLM h n j e = yCoeff d n j e + zCoeff d n j e := by
  unfold yCoeff zCoeff
  set c := (n - 1) * seqA d n
  have hsplit : ∀ l, e l * (qPolyBasis d n l).coeff j =
      (if l ≤ c then e l * (fPoly d l).coeff j else 0) +
        (if c < l then e l * (qPolyBasis d n l).coeff j else 0) := fun l ↦ by
    by_cases hl : l ≤ c
    · rw [ite_eq_left hl, ite_eq_right (by omega), add_zero, qPolyBasis_of_le hl]
    · rw [ite_eq_right hl, ite_eq_left (by omega), zero_add]
  have hs1 : Summable fun l ↦ if l ≤ c then e l * (fPoly d l).coeff j else 0 :=
    summable_of_ne_finset_zero (s := Finset.range (c + 1)) fun l hl ↦ by
      rw [ite_eq_right (by simp at hl; omega)]
  rw [qCoeffCLM_apply, tsum_congr hsplit,
    Summable.tsum_add hs1 (summable_ite_of_norm (summable_norm_qTerm h n j e) _),
    tsum_eq_sum (s := Finset.range (c + 1))
      (fun l hl ↦ by rw [ite_eq_right (by simp at hl; omega)])]
  congr 1
  exact Finset.sum_congr rfl fun l hl ↦ by rw [ite_eq_left (by simp at hl; omega)]

/-- `z_{n,j} = 0` above `vₙ₋₁`. -/
lemma zCoeff_eq_zero (h : PartitionHyp d) {n j : ℕ} (hj : seqV d (n - 1) < j)
    (e : L1) : zCoeff d n j e = 0 := by
  unfold zCoeff
  refine (tsum_congr fun l ↦ ?_).trans tsum_zero
  split_ifs with hl
  · rw [qPolyBasis_of_gt h hl]
    split_ifs with hc
    · have := exponent_le_of_I h hc.1 hc.2 (by omega)
      rw [smul_eq_C_mul, coeff_C_mul, coeff_X_pow, ite_eq_right (by omega), mul_zero, mul_zero]
    · simp
  · rfl

/-- `zIdx n j t` lies in `Iₘ,ₜ₊₁` with `m = n + t + 1`, when `j ≤ vₙ₋₁`. -/
lemma zIdx_mem {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ seqV d (n - 1)) (t : ℕ) :
    (⟨n + t + 1, t + 1, .I⟩ : Block).Mem d (zIdx d n j t) := by
  refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
  · dsimp only [zIdx]; omega
  · dsimp only [zIdx]
    rw [show n + t + 1 - (t + 1) - 1 = n - 1 by omega]
    omega

lemma zIdx_injective (h : PartitionHyp d) {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ seqV d (n - 1)) :
    Function.Injective (zIdx d n j) := fun t t' htt ↦ by
  have hB1 := zIdx_mem (d := d) hn hj t
  rw [htt] at hB1
  have := congrArg Block.r (block_unique h hB1 (zIdx_mem hn hj t'))
  dsimp only at this
  omega

/-- **Śliwa's (2)**: `z_{n,j} = -aₙ ∑_{m > n} e_{j + (m - n)aₘ}` for `j ≤ vₙ₋₁`. -/
theorem hasSum_zCoeff (h : GrowthHyp d) {n j : ℕ} (hn : 2 ≤ n) (hj : j ≤ seqV d (n - 1))
    (e : L1) :
    HasSum (fun t ↦ -(seqA d n : ℂ) * e (zIdx d n j t)) (zCoeff d n j e) := by
  have hP := h.toPartitionHyp
  set c := (n - 1) * seqA d n with hc
  set F : ℕ → ℂ := fun l ↦ if c < l then e l * (qPolyBasis d n l).coeff j else 0 with hF
  have hcg : ∀ t, c < zIdx d n j t := fun t ↦ by
    have h1 := hP.v_lt_a (n + 1) n (by omega)
    have h2 : c ≤ seqV d n := by
      rw [hc]; unfold seqV; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have h3 : seqA d (n + 1) ≤ seqA d (n + t + 1) := seqA_mono h (by omega) (by omega)
    have h4 : seqA d (n + t + 1) ≤ (t + 1) * seqA d (n + t + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    simp only [zIdx]
    omega
  have hFg : ∀ t, F (zIdx d n j t) = -(seqA d n : ℂ) * e (zIdx d n j t) := fun t ↦ by
    simp only [hF, ite_eq_left (hcg t)]
    rw [qPolyBasis_of_gt hP (hcg t), block_eq hP (zIdx_mem (by omega) hj t)]
    dsimp only
    rw [ite_eq_left ⟨rfl, by omega⟩, show n + t + 1 - n = t + 1 by omega,
      show zIdx d n j t - (t + 1) * seqA d (n + t + 1) = j by simp [zIdx],
      smul_eq_C_mul, coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one]
    ring
  have hFoff : ∀ l, l ∉ Set.range (zIdx d n j) → F l = 0 := fun l hl ↦ by
    simp only [hF]
    split_ifs with hcl
    · rw [qPolyBasis_of_gt hP hcl]
      split_ifs with hk
      · rw [smul_eq_C_mul, coeff_C_mul, coeff_X_pow]
        split_ifs with hje
        · exfalso
          apply hl
          have hB := block_mem hP (i := l) (by omega)
          rcases hbl : block d l with ⟨n', r, k⟩
          rw [hbl] at hB hk hje
          dsimp only at hk hje
          obtain ⟨hk, hr⟩ := hk
          subst hk
          obtain ⟨hr1, hrn, hlo, hhi⟩ := hB
          dsimp only at hr1 hrn hlo hhi
          refine ⟨r - 1, ?_⟩
          simp only [zIdx]
          rw [show n + (r - 1) + 1 = n' by omega, show r - 1 + 1 = r by omega]
          rw [show n' - n = r by omega] at hje
          omega
        · simp
      · simp
    · rfl
  have hsF : Summable F := summable_ite_of_norm (summable_norm_qTerm hP n j e) _
  have key := ((zIdx_injective hP (by omega) hj).hasSum_iff hFoff).2 hsF.hasSum
  have hz : zCoeff d n j e = ∑' l, F l := rfl
  rw [hz]
  convert key using 1
  funext t
  exact (hFg t).symm

/-- The windows of the `zIdx`: `j ∈ (vₙ₋₂, vₙ₋₁]` lands in `M_{m,n}`. -/
lemma zIdx_mem_window {n j : ℕ} (hj1 : seqV d (n - 2) < j) (hj2 : j ≤ seqV d (n - 1)) (t : ℕ) :
    (n + t + 1 - n) * seqA d (n + t + 1) + seqV d (n - 2) < zIdx d n j t ∧
      zIdx d n j t ≤ (n + t + 1 - n) * seqA d (n + t + 1) + seqV d (n - 1) := by
  simp only [zIdx, show n + t + 1 - n = t + 1 by omega]
  omega

/-- And `j ≤ vₙ₋₁` lands in the level `(vₘ₋₁, vₘ]`, `m = n + t + 1`. -/
lemma zIdx_mem_level (h : PartitionHyp d) {n j : ℕ} (hn : 2 ≤ n) (hj : j ≤ seqV d (n - 1))
    (t : ℕ) :
    seqV d (n + t + 1 - 1) < zIdx d n j t ∧ zIdx d n j t ≤ seqV d (n + t + 1) := by
  have h1 := h.v_lt_a (n + t + 1) (n + t + 1 - 1) (by omega)
  have h2 := h.v_lt_a (n + t + 1) (n - 1) (by omega)
  have h3 : seqA d (n + t + 1) ≤ (t + 1) * seqA d (n + t + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h4 : (t + 1) * seqA d (n + t + 1) + seqA d (n + t + 1) ≤ seqV d (n + t + 1) :=
    calc (t + 1) * seqA d (n + t + 1) + seqA d (n + t + 1) = (t + 2) * seqA d (n + t + 1) := by
          ring
      _ ≤ (n + t) * seqA d (n + t + 1) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ (n + t) * (seqA d (n + t + 1) + seqB d (n + t + 1)) :=
          Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ = seqV d (n + t + 1) := by unfold seqV; rw [show n + t + 1 - 1 = n + t by omega]
  simp only [zIdx]
  omega

/- ### `y_{m,j} = aₙ eⱼ` on `M_{m,n}` -/

/-- On `M_{m,n}`, among `l ≤ (m - 1)aₘ` only `fⱼ` itself has an `xʲ` term, with coefficient
`aₙ` (`j ∈ Iₘ,ₘ₋ₙ`; the only other candidate `j + aₘ` lies in `Jₘ,ₘ₋ₙ₊₂`, needing `n > 2`). -/
lemma coeff_fPoly_of_window (h : PartitionHyp d) {m n j l : ℕ} (hn : 2 < n) (hnm : n < m)
    (hj1 : (m - n) * seqA d m + seqV d (n - 2) < j)
    (hj2 : j ≤ (m - n) * seqA d m + seqV d (n - 1)) (hl : l ≤ (m - 1) * seqA d m) :
    (fPoly d l).coeff j = if l = j then (seqA d n : ℂ) else 0 := by
  have ha := h.one_le_a m
  have hvn := h.v_lt_a m (n - 1) (by omega)
  have hvm := h.v_lt_a m (m - 1) (by omega)
  have hamn : seqA d m ≤ (m - n) * seqA d m := Nat.le_mul_of_pos_left _ (by omega)
  have hjI : (⟨m, m - n, .I⟩ : Block).Mem d j := by
    refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_⟩
    dsimp only
    rw [show m - (m - n) - 1 = n - 1 by omega]
    omega
  have hvmm : (m - 1) * seqA d m ≤ seqV d m := by
    unfold seqV; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  split_ifs with hlj
  · subst hlj
    rw [fPoly_of_I h hjI rfl]
    dsimp only
    rw [show m - (m - n) = n by omega, coeff_C_mul, coeff_sub, coeff_X_pow, coeff_X_pow,
      ite_eq_left rfl, ite_eq_right (by omega), sub_zero, mul_one]
  · rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [fPoly_zero, coeff_one, ite_eq_right (by omega)]
    have hB := block_mem h hl0
    rcases hbl : block d l with ⟨n', r, k⟩
    rw [hbl] at hB
    -- If `l` has an `xʲ` term below itself, `l > j`, so `l` is in level `m`.
    have hlev : j < l → n' = m := fun hjl ↦ by
      obtain ⟨hlo, hhi, -⟩ := Block.mem_level h hB
      have hr := hB.1
      have hrn := hB.2.1
      dsimp only at hlo hhi hr hrn
      exact level_unique h (by omega) (by omega) ⟨hlo, hhi⟩
        ⟨by omega, by omega⟩
    cases k with
    | J => rw [fPoly_of_J h hB rfl, coeff_C_mul_X_pow, ite_eq_right (fun h' ↦ hlj h'.symm)]
    | L => rw [fPoly_of_L h hB rfl, coeff_C_mul_X_pow, ite_eq_right (fun h' ↦ hlj h'.symm)]
    | I =>
      rw [fPoly_of_I h hB rfl, coeff_C_mul, coeff_sub, coeff_X_pow, coeff_X_pow,
        ite_eq_right (fun h' ↦ hlj h'.symm)]
      dsimp only
      rw [ite_eq_right, sub_zero, mul_zero]
      intro hje
      have ha' := h.one_le_a n'
      obtain rfl : m = n' := (hlev (by omega)).symm
      -- `l = j + aₘ` lies in `Jₘ,ₘ₋ₙ₊₂`, not in an `I` block.
      have hJ : (⟨m, m - n + 2, .J⟩ : Block).Mem d l := by
        refine ⟨by dsimp only; omega, by dsimp only; omega, ?_, ?_⟩
        · dsimp only
          rw [show m - (m - n + 2) = n - 2 by omega, show m - n + 2 - 1 = m - n + 1 by omega,
            add_one_mul]
          omega
        · dsimp only
          rw [show m - n + 2 = m - n + 1 + 1 by omega, add_one_mul, add_one_mul]
          omega
      exact absurd (congrArg Block.kind (block_unique h hB hJ)) (by simp)
    | K =>
      rw [fPoly_of_K h hB rfl, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_pow,
        ite_eq_right (fun h' ↦ hlj h'.symm)]
      dsimp only
      rw [ite_eq_right, mul_zero, sub_zero]
      intro hje
      have hb : 0 < seqB d n' := lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b n')
      obtain rfl : m = n' := (hlev (by omega)).symm
      obtain ⟨-, -, hX⟩ := Block.mem_level h hB
      dsimp only at hX
      rcases hX.1 hl with h' | h' <;> exact absurd h' (by decide)

/-- **`y_{m,j} = aₙ eⱼ` on `M_{m,n}`** (Śliwa p. 637), for `2 < n < m`. -/
theorem yCoeff_of_window (h : PartitionHyp d) {m n j : ℕ} (hn : 2 < n) (hnm : n < m)
    (hj1 : (m - n) * seqA d m + seqV d (n - 2) < j)
    (hj2 : j ≤ (m - n) * seqA d m + seqV d (n - 1)) (e : L1) :
    yCoeff d m j e = seqA d n * e j := by
  have hvn := h.v_lt_a m (n - 1) (by omega)
  have hle : (m - n + 1) * seqA d m ≤ (m - 1) * seqA d m := Nat.mul_le_mul_right _ (by omega)
  have hjc : j ≤ (m - 1) * seqA d m := by rw [add_one_mul] at hle; omega
  unfold yCoeff
  rw [Finset.sum_congr rfl fun l hl ↦ by
    rw [coeff_fPoly_of_window h hn hnm hj1 hj2 (by simp at hl; omega)]]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', ite_eq_left (by simp; omega), mul_comm]

end ReadL1
