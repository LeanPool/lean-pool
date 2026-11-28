/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Lemma4K

/-!
# Śliwa's Lemma 4: `‖Tˢ - Tˢ Qₘ‖ ≤ α`

For `m > 2` and `s ∈ Kₘ,₁` (Śliwa pp. 632–635). In coordinates it is the bound
`‖Tˢ (fᵢ - Qₘ fᵢ)‖ ≤ α` for every `i` (`ReadL1.lemma4_coord`), proved block by block in the
previous files; on ℓ¹ it is an operator-norm bound (`ReadL1.lemma4`), with `Qₘ` extended to ℓ¹ by
`l1Lift` (`ReadL1.readQ`).
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-- **Lemma 4 in coordinates:** `‖Tˢ (fᵢ - Qₘ fᵢ)‖ ≤ α` for every `i`. Below `(m - 1)aₘ` the
difference is `0`; above, the four cases. -/
theorem lemma4_coord (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) (i : ℕ) :
    nrm ((T₀ d ^ s) (single i 1 - qImage d m i)) ≤ alpha := by
  have hP := h.toPartitionHyp
  rcases le_or_gt i ((m - 1) * seqA d m) with hi | hi
  · rw [qImage, ite_eq_left hi, sub_self, map_zero, nrm_zero]; exact alpha_pos.le
  · have hB := block_mem hP (i := i) (by omega)
    rcases hbl : block d i with ⟨n, r, k⟩
    rw [hbl] at hB
    cases k with
    | J => exact lemma4_J h hm hs hB hi
    | I => exact lemma4_I h hm hs hB hi
    | L => exact lemma4_L h hm hs hB hi
    | K => exact lemma4_K h hm hs hB hi

/-- **`Qₘ` on ℓ¹**, for `m ≥ 2`, of norm at most `√Aₘ`. -/
noncomputable def readQ (h : GrowthHyp d) {m : ℕ} (hm : 2 ≤ m) : L1 →L[ℂ] L1 :=
  l1Lift (fun i ↦ toL1 (qImage d m i)) (alpha ^ (Real.sqrt (seqA d m) / 2))
    (fun i ↦ by rw [norm_toL1]; exact nrm_qImage_le h hm i)

lemma readQ_single (h : GrowthHyp d) {m : ℕ} (hm : 2 ≤ m) (i : ℕ) :
    readQ h hm (δ i) = toL1 (qImage d m i) :=
  l1Lift_single _ _ _ i

/-- **Śliwa's Lemma 4.** For `m > 2` and `s ∈ Kₘ,₁`, `‖Tˢ - Tˢ Qₘ‖ ≤ α`. -/
theorem lemma4 (h : GrowthHyp d) {m s : ℕ} (hm : 2 < m) (hs : InK1 d m s) :
    ‖readOp h ^ s - readOp h ^ s * readQ h hm.le‖ ≤ alpha := by
  refine opNorm_le_of_forall_single _ _ fun i ↦ ?_
  have hδ : δ i = toL1 (single i 1) := by rw [toL1_single, one_smul]
  rw [_root_.sub_apply, mul_apply_eq_comp, readQ_single, hδ,
    readOp_pow_toL1, readOp_pow_toL1, ← map_sub, ← map_sub, norm_toL1]
  exact lemma4_coord h hm hs i

end ReadL1
