/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec131OneExpansionAtFirstMatch.ChooseSchedule

/-!
# Independent support for the main attempt lift

Scalar, Fourier and first-cell support is separated from the finite lift
construction to avoid retaining its elaboration state in the construction module.
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ## The mode budget `D_*` (blueprint line 1934) -/

/-! ### The clearing integer `Q₀` (blueprint lines 1893 and 1934) -/

/-- The clearing integer of a rational matrix: the product of the denominators of its entries
(blueprint line 1893: "an integer `Q₀` in the main budget clearing `C_z`"). -/
def clearInt {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) : ℕ := ∏ a, ∏ b, (C a b).den

theorem clearInt_pos {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) : 0 < clearInt C :=
  Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => (C a b).den_pos

/-- The clearing integer clears every entry. -/
theorem clearInt_clears {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (a b : Fin d) :
    ∃ z : ℤ, (clearInt C : ℝ) * (C a b : ℝ) = z := by
  have hdvd : (C a b).den ∣ clearInt C :=
    (Finset.dvd_prod_of_mem (fun b' => (C a b').den) (Finset.mem_univ b)).trans
      (Finset.dvd_prod_of_mem (fun a' => ∏ b', (C a' b').den) (Finset.mem_univ a))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t * (C a b).num, ?_⟩
  have hq : ((C a b : ℚ) : ℝ) * ((C a b).den : ℝ) = ((C a b).num : ℝ) := by
    exact_mod_cast Rat.mul_den_eq_num (C a b)
  rw [ht]; push_cast
  linear_combination (t : ℝ) * hq

/-- The clearing integer is at most `H^(d²)` for entries of height at most `H`. -/
theorem clearInt_le {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) {Hed : ℝ}
    (hC : ∀ a b, (rationalHeight (C a b) : ℝ) ≤ Hed) : (clearInt C : ℝ) ≤ Hed ^ (d * d) := by
  unfold clearInt
  push_cast
  have hden : ∀ a b, ((C a b).den : ℝ) ≤ Hed := fun a b =>
    le_trans (by exact_mod_cast (by unfold rationalHeight; exact le_max_right _ _ :
      (C a b).den ≤ rationalHeight (C a b))) (hC a b)
  calc ∏ a, ∏ b, ((C a b).den : ℝ) ≤ ∏ _a : Fin d, ∏ _b : Fin d, Hed := by
        gcongr with a _ b _; exact hden a b
    _ = Hed ^ (d * d) := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-! ### Groups and main uses along a path (blueprint lines 1728-1730 and 1934) -/


namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-! ### The uniform first-match size and the budget `D_*` (blueprint line 1934) -/

/-- The edge height increases with the radius. -/
theorem ballEdgeH_mono (hHed : 2 ≤ fp.Hed) (dB : ℕ) {n n' : ℕ} (h : n ≤ n') :
    fp.ballEdgeH dB n ≤ fp.ballEdgeH dB n' := by
  unfold ballEdgeH
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log (2 * fp.Hed) := Real.log_nonneg (by linarith only [hHed])
  have hnn : (n : ℝ) ≤ n' := by exact_mod_cast h
  have h1 : ((n + 1) * (dB + 1) : ℝ) ≤ (n' + 1) * (dB + 1) :=
    mul_le_mul_of_nonneg_right (add_le_add hnn (le_refl (1 : ℝ))) (by positivity)
  have h2 := pow_le_pow_left₀ (by positivity) h1 8
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 100000)) hl

/-- The uniform first-match size of the attempt: the size `X` of `mainFirstMatch_finite` at the
largest ball radius `b₁ d₀ + b₁ + bbase 4 + P` of the four ball levels (blueprint line 1934: the
bounds are uniform in the groups and the branch offsets). -/
noncomputable def Xmax (dB : ℕ) (H : ℝ) : ℝ :=
  1 + Real.log (chartTranslationBudget (H ^ 6)) +
    Real.log (3 * fp.ballEdgeH dB (fp.K.b1 * fp.K.d0 + fp.K.b1 + fp.bbase 4 + fp.P))

/-- The first-match size of a role is at least one. -/
theorem one_le_X (hHed : 2 ≤ fp.Hed) (dB : ℕ) {H : ℝ} (hH : 1 ≤ H) (n : ℕ) :
    1 ≤ 1 + Real.log (chartTranslationBudget (H ^ 6)) + Real.log (3 * fp.ballEdgeH dB n) := by
  have h1 : 0 ≤ Real.log (chartTranslationBudget (H ^ 6)) := by
    unfold chartTranslationBudget
    rw [Real.log_exp]
    have : 0 ≤ logarithmicSize (H ^ 6) := by
      unfold logarithmicSize
      have := Real.log_nonneg (one_le_pow₀ hH : (1 : ℝ) ≤ H ^ 6)
      linarith
    positivity
  have h2 : 0 ≤ Real.log (3 * fp.ballEdgeH dB n) := by
    have := fp.two_le_ballEdgeH hHed dB n
    exact Real.log_nonneg (by linarith)
  linarith

/-- The mode budget `D_*` of the attempt (blueprint line 1934), for the first-match degree `D`,
the dimension bound `d_B`, the source complexity `H`, the precision `δ_c`, a bound `N` for the main
labels at one cell, and the parameter `k`. With `B = exp(D X_max^D)` and the count
`M₁ = B (4 max(1, 4B/δ_c) + 1)^(4 d_B)` of the modes of one primary at one branch, it is the sum of
`e^k`; the modes and main uses of all groups along a path, `D (potMax + 1) (N + 1) M₁`; the
rational heights of `eq:mode-differences`; the inverse private weights `colBudget² (B² + 1)`; the
bound `H_ed^(d_B²)` of the clearing integer `Q₀`; and the absolute coefficient sums
`(√N + 1) colBudget B` of the lifted main outputs on normalized cells. It does not depend on the
branch offsets. -/
noncomputable def modeStar (D dB : ℕ) (H δc N k : ℝ) : ℝ :=
  Real.exp k +
    A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
      (Real.exp (D * fp.Xmax dB H ^ D) *
        (4 * max 1 (4 * Real.exp (D * fp.Xmax dB H ^ D) / δc) + 1) ^ (4 * dB)) +
    Real.exp (D * fp.Xmax dB H ^ D) *
      (1 + 4 * (2 * dB + 1) * max 1 (4 * Real.exp (D * fp.Xmax dB H ^ D) / δc)) +
    A.colBudget ^ 2 * (Real.exp (D * fp.Xmax dB H ^ D) ^ 2 + 1) +
    fp.Hed ^ (dB * dB) +
    (Real.sqrt N + 1) * A.colBudget * Real.exp (D * fp.Xmax dB H ^ D)

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

theorem two_le_colBudget : (2 : ℝ) ≤ A.colBudget := by
  have := A.Dc_nonneg; unfold ActiveSetup.colBudget
  have : (0 : ℝ) ≤ Fintype.card A.L * (1 + A.Dc) := by positivity
  linarith

/-- The logarithm of the budget `D_*` in terms of `E` bounding `d_B`, `log H_ed`, `log colBudget`,
`log N` and `log (1/δ_c)`: `log D_* ≤ 4 (d_B + 1) (L_B + E + 6) + E³ + k + L_p + 2E + 7`, where
`L_B = D X_max^D` and `L_p = log (potMax + 1)` (blueprint line 1934). -/
theorem log_modeStar_le_aux (D dB : ℕ) {H δc N k E : ℝ} (hk : 0 ≤ k) (hE : 1 ≤ E)
    (hdB : (dB : ℝ) ≤ E) (hHed : 2 ≤ fp.Hed) (hHedE : Real.log fp.Hed ≤ E) (hH : 1 ≤ H)
    (hδcE : δc⁻¹ ≤ Real.exp E) (hN0 : 0 ≤ N) (hNE : N ≤ Real.exp E)
    (hcB : A.colBudget ≤ Real.exp E) :
    Real.log (fp.modeStar D dB H δc N k) ≤
      4 * (dB + 1) * (D * fp.Xmax dB H ^ D + E + 6) + E ^ 3 + k +
        Real.log (fp.K.potMax A.famVtxBound + 1) + 2 * E + 7 := by
  set LB := (D : ℝ) * fp.Xmax dB H ^ D with hLB
  set Lp := Real.log (fp.K.potMax A.famVtxBound + 1) with hLp
  set! T0 := 4 * (dB + 1) * (LB + E + 6) + E ^ 3 + k + Lp + 2 * E + 5 with hT0
  have hX1 : 1 ≤ fp.Xmax dB H := fp.one_le_X hHed dB hH _
  have hLB0 : 0 ≤ LB := by positivity
  have hLp0 : 0 ≤ Lp := Real.log_nonneg (by
    have : (0 : ℝ) ≤ fp.K.potMax A.famVtxBound := Nat.cast_nonneg _
    linarith)
  have hdB0 : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith only [h]
  have he3 : (9 : ℝ) ≤ Real.exp 3 := by
    have : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith only [he1, he2]
  have hexpE : 1 ≤ Real.exp E := Real.one_le_exp (by linarith)
  set! B := Real.exp LB with hB
  have hB1 : 1 ≤ B := Real.one_le_exp hLB0
  have hcb := two_le_colBudget (A := A)
  -- the vertex bound
  have hNv : (A.famVtxBound : ℝ) ≤ Real.exp (E + 3) := by
    have h1 : (A.famVtxBound : ℝ) ≤ 8 * A.colBudget + 1 := by
      unfold ActiveSetup.famVtxBound
      push_cast
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * A.colBudget)
      linarith
    rw [Real.exp_add]
    linarith [mul_le_mul_of_nonneg_left he3 (Real.exp_pos E).le]
  -- the factor `max 1 (4 B / δ_c)`
  have hmax : max 1 (4 * B / δc) ≤ Real.exp (LB + E + 2) := by
    have h4 : 4 * B / δc ≤ Real.exp (LB + E + 2) := by
      rw [div_eq_mul_inv, Real.exp_add, Real.exp_add]
      have : (4 : ℝ) ≤ Real.exp 2 := by linarith
      have hBE : 0 ≤ B * Real.exp E := by positivity
      calc 4 * B * δc⁻¹ ≤ 4 * B * Real.exp E :=
            mul_le_mul_of_nonneg_left hδcE (by positivity)
        _ = 4 * (B * Real.exp E) := by ring
        _ ≤ Real.exp 2 * (B * Real.exp E) := mul_le_mul_of_nonneg_right this hBE
        _ = B * Real.exp E * Real.exp 2 := by ring
    exact max_le (Real.one_le_exp (by linarith)) h4
  have hmax1 : 1 ≤ max 1 (4 * B / δc) := le_max_left _ _
  have hbase : 4 * max 1 (4 * B / δc) + 1 ≤ Real.exp (LB + E + 4) := by
    have : Real.exp (LB + E + 4) = Real.exp (LB + E + 2) * Real.exp 2 := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have hx := Real.one_le_exp (by linarith : (0 : ℝ) ≤ LB + E + 2)
    linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos (LB + E + 2)).le]
  have hpowb : (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤ Real.exp (4 * dB * (LB + E + 4)) := by
    calc (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤ Real.exp (LB + E + 4) ^ (4 * dB) :=
          pow_le_pow_left₀ (by linarith) hbase _
      _ = Real.exp (4 * dB * (LB + E + 4)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
  -- the comparison with `T0`
  have hdL : 0 ≤ (dB : ℝ) * LB := mul_nonneg hdB0 hLB0
  have hdE : 0 ≤ (dB : ℝ) * E := mul_nonneg hdB0 (by linarith)
  have hE3 : 0 ≤ E ^ 3 := by positivity
  have key : 4 * ((dB : ℝ) + 1) * (LB + E + 6) =
      4 * (dB * LB) + 4 * (dB * E) + 24 * dB + 4 * LB + 4 * E + 24 := by ring
  -- the six terms
  set! t1 := Real.exp k
  set! t2 := (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
    (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB))
  set! t3 := B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc))
  set! t4 := A.colBudget ^ 2 * (B ^ 2 + 1)
  set! t5 := fp.Hed ^ (dB * dB)
  set! t6 := (Real.sqrt N + 1) * A.colBudget * B
  have hS : fp.modeStar D dB H δc N k = t1 + t2 + t3 + t4 + t5 + t6 := rfl
  clear_value LB Lp B
  have hT1 : t1 ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hT2 : t2 ≤ Real.exp T0 := by
    have hp : (fp.K.potMax A.famVtxBound + 1 : ℝ) = Real.exp Lp := by
      rw [hLp, Real.exp_log (by positivity)]
    have hN1 : N + 1 ≤ Real.exp (E + 1) := by
      rw [Real.exp_add]; linarith [mul_le_mul_of_nonneg_left he1 (Real.exp_pos E).le]
    calc t2 ≤ Real.exp (E + 3) * Real.exp Lp * Real.exp (E + 1) *
          (B * Real.exp (4 * dB * (LB + E + 4))) := by
          simp only [t2]
          rw [hp]
          gcongr
      _ = Real.exp (E + 3 + Lp + (E + 1) + (LB + 4 * dB * (LB + E + 4))) := by
          simp only [hB, Real.exp_add]
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by
          have : 4 * (dB : ℝ) * (LB + E + 4) = 4 * (dB * LB) + 4 * (dB * E) + 16 * dB := by ring
          linarith)
  have hT3 : t3 ≤ Real.exp T0 := by
    have h2d : 2 * (dB : ℝ) + 1 ≤ Real.exp (2 * dB) := by
      have := Real.add_one_le_exp (2 * (dB : ℝ)); linarith
    have hin : 1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc) ≤
        Real.exp (2 * dB + 2) * Real.exp (LB + E + 2) := by
      have h5 : 1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc) ≤
          5 * (2 * dB + 1) * max 1 (4 * B / δc) := by
        have := one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ 2 * dB + 1) hmax1
        linarith
      have h6 : 5 * (2 * (dB : ℝ) + 1) ≤ Real.exp (2 * dB + 2) := by
        rw [Real.exp_add]
        linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos (2 * (dB : ℝ))).le,
          Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * dB)]
      calc _ ≤ 5 * (2 * dB + 1) * max 1 (4 * B / δc) := h5
        _ ≤ Real.exp (2 * dB + 2) * Real.exp (LB + E + 2) :=
            mul_le_mul h6 hmax (by linarith) (Real.exp_pos _).le
    calc t3 ≤ B * (Real.exp (2 * dB + 2) * Real.exp (LB + E + 2)) :=
          mul_le_mul_of_nonneg_left hin (by linarith)
      _ = Real.exp (LB + (2 * dB + 2) + (LB + E + 2)) := by simp only [hB, Real.exp_add]; try ring
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hT4 : t4 ≤ Real.exp T0 := by
    have hc2 : A.colBudget ^ 2 ≤ Real.exp (2 * E) := by
      rw [show 2 * E = E + E by ring, Real.exp_add, sq]
      exact mul_le_mul hcB hcB (by linarith) (Real.exp_pos _).le
    have hB2 : B ^ 2 + 1 ≤ Real.exp (2 * LB + 1) := by
      rw [Real.exp_add, show 2 * LB = LB + LB by ring, Real.exp_add, ← hB, sq]
      have hBB : 1 ≤ B * B := one_le_mul_of_one_le_of_one_le hB1 hB1
      linarith [mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ B * B)]
    calc t4 ≤ Real.exp (2 * E) * Real.exp (2 * LB + 1) :=
          mul_le_mul hc2 hB2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (2 * E + (2 * LB + 1)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hT5 : t5 ≤ Real.exp T0 := by
    have hl : 0 ≤ Real.log fp.Hed := Real.log_nonneg (by linarith)
    have : t5 = Real.exp ((dB * dB : ℕ) * Real.log fp.Hed) := by
      simp only [t5]
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [this]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    have h1 : (dB : ℝ) * dB ≤ E * E := mul_le_mul hdB hdB hdB0 (by linarith)
    have h2 : (dB : ℝ) * dB * Real.log fp.Hed ≤ E * E * E :=
      mul_le_mul h1 hHedE hl (by positivity)
    have : E ^ 3 = E * E * E := by ring
    linarith
  have hT6 : t6 ≤ Real.exp T0 := by
    have hsq : Real.sqrt N + 1 ≤ Real.exp (E + 2) := by
      have h1 : Real.sqrt N ≤ N + 1 := by
        have he : (Real.sqrt N - 1) ^ 2 = N - 2 * Real.sqrt N + 1 := by
          rw [sub_sq, Real.sq_sqrt hN0]; ring
        linarith [sq_nonneg (Real.sqrt N - 1), Real.sqrt_nonneg N]
      rw [Real.exp_add]; linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos E).le]
    calc t6 ≤ Real.exp (E + 2) * Real.exp E * B := by
          simp only [t6]; gcongr
      _ = Real.exp (E + 2 + E + LB) := by simp only [hB, Real.exp_add]
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 < fp.modeStar D dB H δc N k := by
    rw [hS]
    have : 0 ≤ t2 := by positivity
    have : 0 ≤ t3 := by positivity
    have : 0 ≤ t4 := by positivity
    have : 0 ≤ t5 := pow_nonneg (by linarith) _
    have : 0 ≤ t6 := by positivity
    have := Real.exp_pos k
    linarith
  clear_value t1 t2 t3 t4 t5 t6
  have hsum : fp.modeStar D dB H δc N k ≤ Real.exp (T0 + 2) := by
    rw [hS, Real.exp_add]
    have h7 := mul_le_mul_of_nonneg_left he2 (Real.exp_pos T0).le
    linarith only [hT1, hT2, hT3, hT4, hT5, hT6, h7, Real.exp_pos T0]
  calc Real.log (fp.modeStar D dB H δc N k) ≤ T0 + 2 := by
        rw [Real.log_le_iff_le_exp hpos]; exact hsum
    _ = _ := by simp only [hT0, hLB]; ring

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

theorem famVtxBound_le : (A.famVtxBound : ℝ) ≤ 8 * A.colBudget + 1 := by
  unfold ActiveSetup.famVtxBound
  push_cast
  have := Nat.floor_le (by linarith [two_le_colBudget (A := A)] : (0 : ℝ) ≤ 8 * A.colBudget)
  linarith

theorem famVtxBound_le_exp {E : ℝ} (hE : 1 ≤ E) (hcB : A.colBudget ≤ Real.exp E) :
    (A.famVtxBound : ℝ) ≤ Real.exp (E + 3) := by
  have he3 : (9 : ℝ) ≤ Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hexpE : 1 ≤ Real.exp E := Real.one_le_exp (by linarith)
  rw [Real.exp_add]
  linarith [famVtxBound_le (A := A), mul_le_mul_of_nonneg_left he3 (Real.exp_pos E).le]

/-- The number of color degrees is at most `5001 k^c` when `colBudget ≤ exp(k^c)`. -/
theorem d0_le {k : ℝ} {c : ℕ} (hk : 1 ≤ k) (hcB : A.colBudget ≤ Real.exp (k ^ c)) :
    (fp.K.d0 : ℝ) ≤ 5001 * k ^ c := by
  have hE1 : 1 ≤ k ^ c := one_le_pow₀ hk
  have hNv1 : (1 : ℝ) ≤ A.famVtxBound := by exact_mod_cast A.one_le_famVtxBound
  have hNv := famVtxBound_le_exp hE1 hcB
  have hlog : Real.log (2 * A.famVtxBound) ≤ k ^ c + 4 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.log A.famVtxBound ≤ k ^ c + 3 := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact hNv
    linarith
  have hl0 : 0 ≤ 1000 * Real.log (2 * A.famVtxBound) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * A.famVtxBound); linarith
  have hceil := Nat.ceil_lt_add_one hl0
  change ((colorDegree A.famVtxBound : ℕ) : ℝ) ≤ _
  unfold colorDegree
  linarith

/-- The logarithm of `potMax + 1` for the vertex bound: at most `2 d₀ (2 d₀ + 1) + d₀ + 2E + 9`. -/
theorem log_potMax_le {E : ℝ} (hE : 1 ≤ E) (hcB : A.colBudget ≤ Real.exp E) :
    Real.log (fp.K.potMax A.famVtxBound + 1) ≤
      2 * ((fp.K.d0 : ℝ) * (2 * fp.K.d0 + 1)) + fp.K.d0 + 2 * E + 9 := by
  set d := (fp.K.d0 : ℝ) with hd
  set Nv := A.famVtxBound
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hNv := famVtxBound_le_exp hE hcB
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hexp3 : 1 ≤ Real.exp (E + 3) := Real.one_le_exp (by linarith)
  have hNv1 : (Nv : ℝ) + 1 ≤ Real.exp (E + 4) := by
    rw [show E + 4 = (E + 3) + 1 by ring, Real.exp_add]
    linarith [mul_le_mul_of_nonneg_left he1 (Real.exp_pos (E + 3)).le]
  have ha : d * (2 * d + 1) + 1 ≤ Real.exp (d * (2 * d + 1)) := by
    have := Real.add_one_le_exp (d * (2 * d + 1)); linarith
  have hb : ((Nat.size Nv : ℕ) : ℝ) + 1 ≤ Real.exp (E + 4) := by
    have : Nat.size Nv ≤ Nv := Nat.size_le.mpr Nat.lt_two_pow_self
    have : ((Nat.size Nv : ℕ) : ℝ) ≤ Nv := by exact_mod_cast this
    linarith
  have hc : d * ((flog32 Nv : ℕ) : ℝ) + 1 ≤ Real.exp d * Real.exp (E + 4) := by
    have hf : ((flog32 Nv : ℕ) : ℝ) ≤ Nv := by exact_mod_cast flog32_le Nv
    have h1 : d * ((flog32 Nv : ℕ) : ℝ) + 1 ≤ (d + 1) * ((Nv : ℝ) + 1) := by
      have : d * ((flog32 Nv : ℕ) : ℝ) ≤ d * Nv := mul_le_mul_of_nonneg_left hf hd0
      have : (0 : ℝ) ≤ Nv := Nat.cast_nonneg _
      nlinarith only [hd, hf]
    have h2 : d + 1 ≤ Real.exp d := Real.add_one_le_exp d
    exact h1.trans (mul_le_mul h2 hNv1 (by positivity) (Real.exp_pos _).le)
  have hpm : ((fp.K.potMax Nv : ℕ) : ℝ) ≤
      Real.exp (2 * (d * (2 * d + 1)) + d + 2 * (E + 4)) := by
    unfold ColorSetup.potMax
    push_cast
    have e : Real.exp (2 * (d * (2 * d + 1)) + d + 2 * (E + 4)) =
        Real.exp (d * (2 * d + 1)) * Real.exp (E + 4) * (Real.exp d * Real.exp (E + 4)) *
          Real.exp (d * (2 * d + 1)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [e]
    have hp1 : (0 : ℝ) ≤ d * (2 * d + 1) + 1 := by positivity
    gcongr
  have hQ : 0 ≤ 2 * (d * (2 * d + 1)) + d + 2 * (E + 4) := by positivity
  have hpos : (0 : ℝ) < (fp.K.potMax Nv : ℕ) + 1 := by positivity
  rw [Real.log_le_iff_le_exp hpos]
  set Q' := 2 * (d * (2 * d + 1)) + d + 2 * (E + 4) with hQ'
  have h1 : 1 ≤ Real.exp Q' := Real.one_le_exp hQ
  have e2 : 2 * (d * (2 * d + 1)) + d + 2 * E + 9 = Q' + 1 := by rw [hQ']; ring
  rw [e2, Real.exp_add]
  linarith [mul_le_mul_of_nonneg_left he1 (Real.exp_pos Q').le]

end ActiveSetup.BasicFamilies.FamParams


/-! ### The Fourier expansion of the squared gauge `(ζ^ρ)²` (blueprint lines 1944 and 2056) -/

/-- The periodic branch profile `t ↦ b(fract t)`. -/
noncomputable def fractProfile (δ t : ℝ) : ℝ := branchProfile δ (Int.fract t)

/-- Near any point the periodic profile is a sum of two translates of the profile. -/
theorem fractProfile_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (t₀ : ℝ) :
    fractProfile δ =ᶠ[nhds t₀] fun t =>
      branchProfile δ (t - ⌊t₀⌋) + branchProfile δ (t - ⌊t₀⌋ + 1) := by
  have hU : Set.Ioo ((⌊t₀⌋ : ℝ) - 1) (⌊t₀⌋ + 1) ∈ nhds t₀ := by
    refine Ioo_mem_nhds ?_ ?_
    · linarith [Int.floor_le t₀]
    · exact Int.lt_floor_add_one t₀
  filter_upwards [hU] with t ht
  unfold fractProfile
  rcases le_or_gt (⌊t₀⌋ : ℝ) t with h | h
  · have hf : Int.fract t = t - ⌊t₀⌋ := by
      rw [Int.fract, Int.floor_eq_iff.mpr ⟨h, ht.2⟩]
    rw [hf, branchProfile_eq_zero_of_ge (s := t - ⌊t₀⌋ + 1) hδ (by linarith), add_zero]
  · have hfl : ⌊t⌋ = ⌊t₀⌋ - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [ht.1]
    have hf : Int.fract t = t - ⌊t₀⌋ + 1 := by
      rw [Int.fract, hfl]; push_cast; ring
    rw [hf, branchProfile_eq_zero_of_le (s := t - ⌊t₀⌋) hδ (by linarith), zero_add]

theorem fractProfile_contDiff {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fractProfile δ) := by
  refine contDiff_iff_contDiffAt.mpr fun t₀ => ?_
  refine ContDiffAt.congr_of_eventuallyEq ?_ (fractProfile_eventuallyEq hδ t₀)
  refine (ContDiff.add ?_ ?_).contDiffAt
  · exact (branchProfile_contDiff δ).comp (contDiff_id.sub contDiff_const)
  · exact (branchProfile_contDiff δ).comp ((contDiff_id.sub contDiff_const).add contDiff_const)

/-- Derivative bounds for the periodic profile: `|D^i| ≤ (2B)^i` for `i ≤ m`. -/
theorem fractProfile_deriv_le {δ : ℝ} (hδ : 0 < δ) {m i : ℕ} (hi : i ≤ m) (t₀ : ℝ) :
    |iteratedDeriv i (fractProfile δ) t₀| ≤
      (2 * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))) ^ i := by
  set B := bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ)
  have hB0 : 0 ≤ B := by have := one_le_bumpConst; positivity
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · simp only [iteratedDeriv_zero, pow_zero, fractProfile]
    have := branchProfile_mem δ (Int.fract t₀)
    rw [abs_of_nonneg this.1]; exact this.2
  rw [(fractProfile_eventuallyEq hδ t₀).iteratedDeriv_eq]
  have hs := branchProfile_contDiff δ
  have e : (fun t => branchProfile δ (t - ⌊t₀⌋) + branchProfile δ (t - ⌊t₀⌋ + 1)) =
      (fun t => branchProfile δ (t - ⌊t₀⌋)) + fun t => branchProfile δ (t - (⌊t₀⌋ - 1)) := by
    funext t; simp only [Pi.add_apply]; congr 2; ring
  have hc : ∀ c : ℝ, ContDiffAt ℝ i (fun t => branchProfile δ (t - c)) t₀ := fun c =>
    ((hs.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [e, iteratedDeriv_add (hc _) (hc _), iteratedDeriv_comp_sub_const,
    iteratedDeriv_comp_sub_const]
  have h1 := branchProfile_deriv_le hδ hi (t₀ - ⌊t₀⌋)
  have h2 := branchProfile_deriv_le hδ hi (t₀ - (⌊t₀⌋ - 1))
  have h3 : (2 : ℝ) ≤ 2 ^ i := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi1
  rw [mul_pow]
  calc _ ≤ |iteratedDeriv i (branchProfile δ) (t₀ - ⌊t₀⌋)| +
        |iteratedDeriv i (branchProfile δ) (t₀ - (⌊t₀⌋ - 1))| := abs_add_le _ _
    _ ≤ B ^ i + B ^ i := add_le_add h1 h2
    _ ≤ 2 ^ i * B ^ i := by nlinarith only [pow_nonneg hB0 i, h3]

/-- The squared periodic gauge `w ↦ (Π_i b({w_i - ρ_i}))²` on `ℝ^d`. -/
noncomputable def gaugeSq {d : ℕ} (δ : ℝ) (ρ : Fin d → ℝ) (w : Fin d → ℝ) : ℂ :=
  chartCoordinateProduct (fractProfile δ) (w - ρ) * chartCoordinateProduct (fractProfile δ) (w - ρ)

theorem centerCut_sq_eq (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (y : ℝ) :
    ((centerCut z δ ρ y : ℝ) : ℂ) ^ 2 = gaugeSq δ ρ (fun i => z.θ i * y) := by
  simp only [gaugeSq, centerCut, branchCutoffValue, chartCoordinateProduct, fractProfile,
    Pi.sub_apply]
  push_cast
  ring

theorem gaugeSq_periodic {d : ℕ} (δ : ℝ) (ρ w : Fin d → ℝ) (j : Fin d → ℤ) :
    gaugeSq δ ρ (w + fun i => (j i : ℝ)) = gaugeSq δ ρ w := by
  have : ∀ i, fractProfile δ ((w + fun i => (j i : ℝ)) i - ρ i) = fractProfile δ (w i - ρ i) :=
    fun i => by
      simp only [fractProfile, Pi.add_apply,
        show w i + (j i : ℝ) - ρ i = (w i - ρ i) + (j i : ℤ) by ring, Int.fract_add_intCast]
  simp only [gaugeSq, chartCoordinateProduct, Pi.sub_apply, this]

theorem gaugeSq_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (ρ : Fin d → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaugeSq δ ρ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin d → ℝ =>
      chartCoordinateProduct (fractProfile δ) (w - ρ) :=
    (chartCoordinateProduct_smooth (d := d) (fractProfile_contDiff hδ)).comp
      (contDiff_id.sub contDiff_const)
  exact h.mul h

theorem gaugeSq_norm_le {d : ℕ} (δ : ℝ) (ρ w : Fin d → ℝ) : ‖gaugeSq δ ρ w‖ ≤ 1 := by
  have h : ‖chartCoordinateProduct (fractProfile δ) (w - ρ)‖ ≤ 1 := by
    simp only [chartCoordinateProduct, norm_prod, Complex.norm_real, Real.norm_eq_abs]
    refine Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    have := branchProfile_mem δ (Int.fract ((w - ρ) i))
    rw [fractProfile, abs_of_nonneg this.1]; exact this.2
  simp only [gaugeSq, norm_mul]
  calc _ ≤ 1 * 1 := mul_le_mul h h (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The derivative bound `‖D^m (ζ²)‖ ≤ (4dB)^m` of the squared gauge. -/
theorem gaugeSq_iteratedFDeriv_le {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (ρ w : Fin d → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (gaugeSq δ ρ) w‖ ≤
      (2 * ((d : ℝ) * (2 * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))))) ^ m := by
  set R := 2 * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))
  have hR : 0 ≤ R := by have := one_le_bumpConst; positivity
  set F : (Fin d → ℝ) → ℂ := fun w => chartCoordinateProduct (fractProfile δ) (w - ρ)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (chartCoordinateProduct_smooth (d := d)
    (fractProfile_contDiff hδ)).comp (contDiff_id.sub contDiff_const)
  have hFi : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F w‖ ≤ ((d : ℝ) * R) ^ i := by
    intro i hi
    have e : F = fun w => chartCoordinateProduct (fractProfile δ) (w - ρ) := rfl
    rw [e, iteratedFDeriv_comp_sub]
    refine (chartCoordinateProduct_derivative_geometric (fractProfile_contDiff hδ) (w - ρ) hR
      fun j hj x => ?_)
    exact (fractProfile_deriv_le hδ (hj.trans hi) x).trans (le_of_eq rfl)
  have h := norm_iteratedFDeriv_mul_le (N := (⊤ : ℕ∞)) hF hF w (n := m) (by exact_mod_cast le_top)
  refine h.trans ?_
  have hdR : 0 ≤ (d : ℝ) * R := by positivity
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i F w‖ *
        ‖iteratedFDeriv ℝ (m - i) F w‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((d : ℝ) * R) ^ i *
        ((d : ℝ) * R) ^ (m - i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        gcongr
        · exact hFi i hi'
        · exact hFi (m - i) (Nat.sub_le _ _)
    _ = (2 * ((d : ℝ) * R)) ^ m := by
        rw [two_mul, add_pow]
        refine Finset.sum_congr rfl fun i _ => by ring

/-- The truncation error constant of the squared gauge (`gaugeSq_truncate`). -/
noncomputable def gaugeTail (d : ℕ) (δ : ℝ) : ℝ :=
  (7 : ℝ) ^ d * (2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
    (2 / δ))))) ^ (d + 1) * Real.sqrt d ^ (d + 1)

theorem gaugeTail_nonneg (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ gaugeTail d δ := by
  unfold gaugeTail; have := one_le_bumpConst; positivity

section GaugeExact
variable {d : ℕ}

/-- Blueprint lines 1942-1944 ("slightly enlarge the cutoffs inside each branch region, making them
one on the required supports, and extend by zero at its cuts"): the enlarged cutoff of parameter
`δ/2` is one wherever the true cutoff of parameter `δ` is nonzero (the true cutoff vanishes within
`δ` of each cut, `branchProfile_eq_zero_near_cut`) and zero at the cuts. Hence the four true
cutoffs times the four gauge phases `e(c_j p_{ρ_j}(y_j))` equal exactly the four true cutoffs times
the smooth periodic multiplier `gaugeMult (δ/2)` at the torus point. -/
theorem gauge_factors_eq_mult_exact {δ : ℝ} (hδ : 0 < δ) (θ : Fin d → ℝ)
    (C : Matrix (Fin d) (Fin d) ℚ) (lam : ℝ) {Q0 : ℕ} (hQ0 : 0 < Q0) (l' : Fin 4)
    (ρ : Fin 4 → Fin d → ℝ) (x t : ℝ) :
    (∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
        (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) * (lam * (x + ((j : ℕ) : ℝ) * t) ^ 2 +
          chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
            (branchLift (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))))) : ℂ) =
      (∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
        gaugeMult (δ / 2) Q0 l' C ρ (torusPt θ Q0 l' x t) := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  set s : Fin 4 → Fin d → ℝ := fun j a => Int.fract (θ a * (x + ((j : ℕ) : ℝ) * t) - ρ j a)
  have hW := fun j => torusW_torusPt θ hQ0 l' j x t
  have hWa : ∀ j a, torusW Q0 l' j (torusPt θ Q0 l' x t) a = θ a * (x + ((j : ℕ) : ℝ) * t) :=
    fun j a => congrFun (hW j) a
  have hM : gaugeMult (δ / 2) Q0 l' C ρ (torusPt θ Q0 l' x t) =
      (∏ j : Fin 4, ∏ a, (branchProfile (δ / 2) (s j a) : ℂ)) *
        (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
          chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
            (gaugeCarry θ ρ x t j)) : ℂ) := by
    unfold gaugeMult gaugeTerm
    simp only [gaugeCarry_eq_carryVec θ hQ0 l' ρ x t]
    simp only [hW]
    congr 1
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun a _ => ?_
    simp only [s, gaugeFloor, hWa, Int.fract]
  rw [gauge_cancel θ C lam ρ x t, hM]
  set E := (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
    chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) (gaugeCarry θ ρ x t j)) : ℂ)
  have hχ : ∀ j, branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) =
      ∏ a, branchProfile δ (s j a) := fun j => rfl
  by_cases hin : ∀ j a, δ < s j a ∧ s j a < 1 - δ
  · have hone : ∏ j : Fin 4, ∏ a, (branchProfile (δ / 2) (s j a) : ℂ) = 1 := by
      refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun a _ => ?_
      rw [branchProfile_eq_one hδ2 (by linarith [(hin j a).1]) (by linarith [(hin j a).2])]
      simp
    rw [hone, one_mul]
  · push Not at hin
    obtain ⟨j, a, hja⟩ := hin
    have hz : branchProfile δ (s j a) = 0 := by
      refine branchProfile_eq_zero_near_cut hδ ?_
      by_cases h : δ < s j a
      · exact Or.inr (hja h)
      · exact Or.inl (not_lt.mp h)
    have hχ0 : (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ) = 0 := by
      rw [hχ j, Finset.prod_eq_zero (Finset.mem_univ a) hz]; simp
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hχ0, zero_mul, zero_mul]

end GaugeExact

section GaugeFourier
variable {d : ℕ}

/-- The derivative constant of order `2d + 1` of the multiplier (`gaugeMult_deriv_le`), with
`Q₀` and the entry bound `C_m` as real parameters. -/
noncomputable def gaugeMultA (d : ℕ) (Q0 Cm δ : ℝ) : ℝ :=
  3 ^ (4 * d) * (4 * (4 * Q0 * (d * profR δ (d + d + 1))) +
    2 * Real.pi * (8 * ((d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0)))))) ^ (d + d + 1)

/-- The truncation constant of the multiplier. -/
noncomputable def gaugeMultTail (d : ℕ) (Q0 Cm δ : ℝ) : ℝ :=
  (7 : ℝ) ^ (d + d) * gaugeMultA d Q0 Cm δ * Real.sqrt (d + d : ℕ) ^ (d + d + 1)

/-- The full Fourier norm bound of the multiplier. -/
noncomputable def gaugeMultNorm (d : ℕ) (Q0 Cm δ : ℝ) : ℝ :=
  5 ^ (d + d) + 2 * gaugeMultTail d Q0 Cm δ

end GaugeFourier

/-- The full Fourier norm bound of the squared gauge `(ζ^ρ)²`. -/
noncomputable def gaugeSqNorm (d : ℕ) (δ : ℝ) : ℝ := 5 ^ d + 2 * gaugeTail d δ

theorem profR_mono {δ : ℝ} (hδ : 0 < δ) {m m' : ℕ} (h : m ≤ m') : profR δ m ≤ profR δ m' := by
  unfold profR
  have := one_le_bumpConst
  have hmm : (8 * ((m : ℝ) + 1)) ≤ 8 * ((m' : ℝ) + 1) := by
    have : (m : ℝ) ≤ m' := by exact_mod_cast h
    linarith
  gcongr

theorem one_le_profR {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ) : 1 ≤ profR δ m := by
  unfold profR
  have hb := one_le_bumpConst
  have h1 : (1 : ℝ) ≤ (8 * ((m : ℝ) + 1)) ^ 32 :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have h2 : (1 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb h1) h2

theorem gaugeMultA_nonneg {δ : ℝ} (hδ : 0 < δ) (d : ℕ) {Q0 Cm : ℝ} (hQ0 : 0 ≤ Q0)
    (hCm : 0 ≤ Cm) : 0 ≤ gaugeMultA d Q0 Cm δ := by
  unfold gaugeMultA; have := profR_nonneg hδ (d + d + 1); have := Real.pi_pos; positivity

theorem exp_bounds_small : (2 : ℝ) ≤ Real.exp 1 ∧ (7 : ℝ) ≤ Real.exp 2 ∧ (20 : ℝ) ≤ Real.exp 3 ∧
    (8000 : ℝ) ≤ Real.exp 9 := by
  have h := Real.exp_one_gt_d9
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have e3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have e9 : Real.exp 9 = Real.exp 3 * Real.exp 3 * Real.exp 3 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h2 : (7 : ℝ) ≤ Real.exp 2 := by rw [e2]; nlinarith
  have h3 : (20 : ℝ) ≤ Real.exp 3 := by rw [e3]; nlinarith
  refine ⟨h1, h2, h3, ?_⟩
  rw [e9]; nlinarith

/-- `x ≤ exp x` for real `x`, used for crude size bounds. -/
theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x; linarith

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-! ### The enlarged budget `D_*` and the common cutoff `B_*` (blueprint line 1944) -/

/-- The height bound of the key differences of the modes of every group (the bound `B_σ` of
`exists_mainModeSystem`), `max(1, B (1 + 4 (2 d_B + 1) max(1, 4B/δ_c)))` at the largest curvature
bound `B = exp(D X_max^D)`. -/
noncomputable def keyHgt (D dB : ℕ) (H δc : ℝ) : ℝ :=
  max 1 (Real.exp (D * fp.Xmax dB H ^ D) * (1 + 4 * (2 * dB + 1) *
    max 1 (4 * Real.exp (D * fp.Xmax dB H ^ D) / δc)))

/-- The heights of the rescaled differences of mode differences (blueprint line 1934: `D_*` covers
the rational heights of `eq:mode-differences` and `Q₀`): `2 (Q₀ (3 B_σ²)²)² + 1` with
`Q₀ ≤ H_ed^(d_B²) + 1`. -/
noncomputable def hgtStar (D dB : ℕ) (H δc : ℝ) : ℝ :=
  2 * ((fp.Hed ^ (dB * dB) + 1) * (3 * (fp.keyHgt D dB H δc * fp.keyHgt D dB H δc) ^ 2)) ^ 2 + 1

theorem one_le_keyHgt (D dB : ℕ) (H δc : ℝ) : 1 ≤ fp.keyHgt D dB H δc := le_max_left _ _

theorem one_le_hgtStar (D dB : ℕ) (H δc : ℝ) : 1 ≤ fp.hgtStar D dB H δc := by
  unfold hgtStar; have := sq_nonneg ((fp.Hed ^ (dB * dB) + 1) *
    (3 * (fp.keyHgt D dB H δc * fp.keyHgt D dB H δc) ^ 2)); linarith

/-- The key heights and the clearing bound are at most `modeStar + 1`. -/
theorem keyHgt_le_modeStar (D dB : ℕ) {H δc N : ℝ} (k : ℝ) (hHed : 2 ≤ fp.Hed) (_hH : 1 ≤ H)
    (_hδc : 0 < δc) (hN0 : 0 ≤ N) :
    fp.keyHgt D dB H δc ≤ fp.modeStar D dB H δc N k + 1 ∧
      fp.Hed ^ (dB * dB) + 1 ≤ fp.modeStar D dB H δc N k + 1 := by
  set Bm := Real.exp (D * fp.Xmax dB H ^ D)
  have hBm : 0 < Bm := Real.exp_pos _
  have hmax : 0 ≤ max 1 (4 * Bm / δc) := le_trans zero_le_one (le_max_left _ _)
  have hcb : (2 : ℝ) ≤ A.colBudget := by
    have := A.Dc_nonneg; unfold ActiveSetup.colBudget
    have : (0 : ℝ) ≤ Fintype.card A.L * (1 + A.Dc) := by positivity
    linarith
  have h1 : (0 : ℝ) ≤ A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
      (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) := by positivity
  have h2 : (0 : ℝ) ≤ A.colBudget ^ 2 * (Bm ^ 2 + 1) := by positivity
  have h3 : (0 : ℝ) ≤ (Real.sqrt N + 1) * A.colBudget * Bm := by positivity
  have h4 : (0 : ℝ) ≤ Bm * (1 + 4 * (2 * dB + 1) * max 1 (4 * Bm / δc)) := by positivity
  have h5 : (0 : ℝ) ≤ fp.Hed ^ (dB * dB) := pow_nonneg (by linarith) _
  have h6 := Real.exp_pos k
  unfold keyHgt modeStar
  refine ⟨max_le (by linarith) (by linarith), by linarith⟩

/-- Blueprint line 1944 ("enlarge `D_*` to cover these full Fourier norms, including `(ζ^ρ)²`"):
the budget `modeStar` of line 1934 plus the full Fourier norm bounds of the gauge multipliers
(enlarged cutoff `δ/2`, centers of dimension at most `d_B`, `Q₀ ≤ H_ed^(d_B²)`, entries at most
`H_ed`) and of the squared gauge `(ζ^ρ)²` (cutoff `δ`). -/
noncomputable def modeStarG (D dB : ℕ) (H δc N k δ : ℝ) : ℝ :=
  fp.modeStar D dB H δc N k + gaugeMultNorm dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) +
    gaugeSqNorm dB δ + fp.hgtStar D dB H δc

theorem gaugeMultNorm_nonneg (d : ℕ) {Q0 Cm δ : ℝ} (hδ : 0 < δ) (hQ0 : 0 ≤ Q0) (hCm : 0 ≤ Cm) :
    0 ≤ gaugeMultNorm d Q0 Cm δ := by
  unfold gaugeMultNorm gaugeMultTail
  have := gaugeMultA_nonneg hδ d hQ0 hCm
  positivity

theorem gaugeMultTail_nonneg (d : ℕ) {Q0 Cm δ : ℝ} (hδ : 0 < δ) (hQ0 : 0 ≤ Q0) (hCm : 0 ≤ Cm) :
    0 ≤ gaugeMultTail d Q0 Cm δ := by
  unfold gaugeMultTail
  have := gaugeMultA_nonneg hδ d hQ0 hCm
  positivity

theorem gaugeSqNorm_nonneg (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ gaugeSqNorm d δ := by
  unfold gaugeSqNorm; have := gaugeTail_nonneg d hδ; positivity

/-- The uniform truncation constant of the multipliers and of `(ζ^ρ)²`. -/
noncomputable def tailStar (dB : ℕ) (δ : ℝ) : ℝ :=
  gaugeMultTail dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) + gaugeTail dB δ

/-- The cutoff exponent `K_*` (blueprint line 1944): the least `K` with
`2^K ≥ 2 (T_* + 1) D_*^300`, `T_*` the uniform truncation constant. -/
noncomputable def Kstar (D dB : ℕ) (H δc N k δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (2 * (fp.tailStar dB δ + 1) * fp.modeStarG D dB H δc N k δ ^ 300)⌉₊

end ActiveSetup.BasicFamilies.FamParams

/-- The polynomial size of the Fourier exponents `T_G + T_S ≤ (5κ + 4682) E⁴` for `E ≥ 1`. -/
theorem fourier_exponents_le {E κb : ℝ} (hE1 : 1 ≤ E) (hκ : 0 ≤ κb) :
    (12 * E + (2 * E + 1) * (E ^ 3 + κb + 514 * E + 523) + 2 * E * (2 * E + 1)) +
      (2 * E + (E + 1) * (κb + 258 * E + 515) + E * (E + 1)) ≤ (5 * κb + 4682) * E ^ 4 := by
  have e : (12 * E + (2 * E + 1) * (E ^ 3 + κb + 514 * E + 523) + 2 * E * (2 * E + 1)) +
      (2 * E + (E + 1) * (κb + 258 * E + 515) + E * (E + 1)) =
      2 * E ^ 4 + E ^ 3 + 1291 * E ^ 2 + 2350 * E + 3 * (κb * E) + 2 * κb + 1038 := by ring
  rw [e]
  have h1 : E ≤ E ^ 4 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have h2 : E ^ 2 ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have h3 : E ^ 3 ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have h0 : 1 ≤ E ^ 4 := one_le_pow₀ hE1
  have h4 : κb * E ≤ κb * E ^ 4 := mul_le_mul_of_nonneg_left h1 hκ
  have h5 : κb ≤ κb * E ^ 4 := le_mul_of_one_le_right hκ h0
  linarith


namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- An actual use of the group `G` at a cell (blueprint line 1753: "a group has an actual use
only at a current central assignment"): the cell is active and carries a present central vertex
with successful color data whose group is `G`. -/
def ActualUse (G : bf.Grp) (I : ℤ × ℤ) : Prop :=
  I ∈ A.cells ∧ ∃ x ∈ bf.admT.X (bf.admAt I),
    fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) x) ∧
      fp.K.grp bf.admT A.famVtxBound (bf.admAt I) x = G

open Classical in
/-- Blueprint line 1967 (retention rule): the `v_b`-cells retained for the group `G` in the block
`[b, b + K)`: the cells of the attempt tree of depth `v_b = b - 2K` containing a cell with an
actual use of `G` at a depth of the block. -/
noncomputable def retainedV (G : bf.Grp) (b : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  (dyadicFiniteTree A.G A.R A.treeDepth).filter fun J => J.1 = b - 2 * K ∧
    ∃ I : ℤ × ℤ, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 ∧ b ≤ I.1 ∧
      I.1 < b + K ∧ fp.ActualUse G I

open Classical in
theorem mem_retainedV {G : bf.Grp} {b : ℤ} {K : ℕ} {J : ℤ × ℤ} :
    J ∈ fp.retainedV G b K ↔ J ∈ dyadicFiniteTree A.G A.R A.treeDepth ∧ J.1 = b - 2 * K ∧
      ∃ I : ℤ × ℤ, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 ∧ b ≤ I.1 ∧
        I.1 < b + K ∧ fp.ActualUse G I := by
  unfold retainedV; rw [Finset.mem_filter]

open Classical in
/-- Blueprint line 1967 ("a mode available at `u_b` has first match no later than `u_b`"): a
first-match cell of a primary at an active cell `a` that meets a subcell `U` of `a` contains `U`. -/
theorem firstCell_contains (l : Fin 4) (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ)
    (d : bf.Vtx) {Φ : bf.Lab ⊕ Fin fp.Mc} {a U I₀ : ℤ × ℤ} (ha : a ∈ A.cells)
    (hΦ : Φ ∈ fp.primaries l s G j d a)
    (hUa : dyadicGridCell A.G U.1 U.2 ⊆ dyadicGridCell A.G a.1 a.2)
    (hI₀ : I₀ ∈ fp.firstCells A.cells l s G j d Φ) {y : ℝ}
    (hyU : y ∈ dyadicGridCell A.G U.1 U.2) (hyI : y ∈ dyadicGridCell A.G I₀.1 I₀.2) :
    dyadicGridCell A.G U.1 U.2 ⊆ dyadicGridCell A.G I₀.1 I₀.2 := by
  obtain ⟨I₁, hI₁, haI₁⟩ := fp.exists_firstCell A.cells l s G j d ha hΦ
  have h := fp.firstCell_unique A.cells l s G j d hI₀ hI₁ hyI (haI₁ (hUa hyU))
  subst h
  exact hUa.trans haI₁

end ActiveSetup.BasicFamilies.FamParams

/-! ### The main-column mode systems (blueprint lines 1971-1975) -/


end TrilinearHT.Auto

end
