/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.Reflections

/-!
# Averages of reflections approximate self-adjoint contractions

Let `A` be a self-adjoint contraction of a von Neumann algebra `M` and suppose that
"threshold projections" `E u ∈ M` (`u : ℝ`) are given: self-adjoint idempotents commuting
with `A`, decreasing in `u`, with `(A - u) E u ≥ 0` and `(u - A) (1 - E u) ≥ 0`.
(Their existence is *assumed* in this file; it is the spectral theorem for `A`.)

For `N ≥ 1` and the thresholds `u_k = -1 + 2k/N` put `P_0 = 1`, `P_k = E u_k` for
`0 < k < N` and `P_N = 0`.  Then `A` is within `2/N` (in operator norm) of the average of the
`N` reflections `2 P_k - 1`, `k = 0, …, N-1` (`exists_reflection_average_near`), hence `A`
lies in the norm closure of the convex hull of the reflections of `M`
(`mem_closure_convexHull_reflections_of_thresholds`).
-/

@[expose] public section

open scoped ComplexOrder

namespace VacuumBellSeparation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ReflectionApprox

theorem isSelfAdjoint_one_op : IsSelfAdjoint (1 : H →L[ℂ] H) := by
  first | exact IsSelfAdjoint.one _

theorem isSelfAdjoint_zero_op : IsSelfAdjoint (0 : H →L[ℂ] H) := by
  first | exact IsSelfAdjoint.zero _

end ReflectionApprox

open ReflectionApprox

/-! ### Reflections from projections -/

/-- For a self-adjoint idempotent `P ∈ M`, the operator `P + P - 1` is a reflection in `M`. -/
theorem add_self_sub_one_mem_reflections {M : VonNeumannAlgebra H} {P : H →L[ℂ] H}
    (hPM : P ∈ M) (hsa : IsSelfAdjoint P) (hid : P * P = P) :
    P + P - 1 ∈ reflections M := by
  refine ⟨sub_mem (add_mem hPM hPM) (one_mem M), (hsa.add hsa).sub isSelfAdjoint_one_op, ?_⟩
  simp only [mul_sub, sub_mul, mul_add, add_mul, one_mul, mul_one, hid]
  abel

/-- For a self-adjoint idempotent `P ∈ M`, the operator `2 P - 1` is a reflection in `M`. -/
theorem two_smul_sub_one_mem_reflections {M : VonNeumannAlgebra H} {P : H →L[ℂ] H}
    (hPM : P ∈ M) (hsa : IsSelfAdjoint P) (hid : P * P = P) :
    (2 : ℂ) • P - 1 ∈ reflections M := by
  rw [two_smul]
  exact add_self_sub_one_mem_reflections hPM hsa hid

namespace ReflectionApprox

/-! ### Positivity of projections and a norm bound -/

/-- A self-adjoint idempotent is positive. -/
theorem isPositive_of_isSelfAdjoint_of_idem {P : H →L[ℂ] H} (hsa : IsSelfAdjoint P)
    (hid : P * P = P) : P.IsPositive := by
  have h : (0 : H →L[ℂ] H) ≤ star P * P := star_mul_self_nonneg P
  rw [hsa.star_eq, hid] at h
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp h

/-- The complement of a self-adjoint idempotent is positive. -/
theorem isPositive_one_sub_of_isSelfAdjoint_of_idem {Q : H →L[ℂ] H} (hsa : IsSelfAdjoint Q)
    (hid : Q * Q = Q) : (1 - Q).IsPositive := by
  refine isPositive_of_isSelfAdjoint_of_idem (isSelfAdjoint_one_op.sub hsa) ?_
  simp only [mul_sub, sub_mul, one_mul, mul_one, hid]
  abel

/-- A positive operator `G` with `c • 1 - G` positive has norm at most `c`. -/
theorem norm_le_of_isPositive_of_isPositive_sub {G : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (hG : G.IsPositive) (hcG : ((c : ℂ) • (1 : H →L[ℂ] H) - G).IsPositive) : ‖G‖ ≤ c := by
  have hG' : (0 : H →L[ℂ] H) ≤ G := ContinuousLinearMap.nonneg_iff_isPositive.mpr hG
  have hle : G ≤ (c : ℂ) • (1 : H →L[ℂ] H) := ContinuousLinearMap.le_def.mpr hcG
  have h1 : ‖G‖ ≤ ‖(c : ℂ) • (1 : H →L[ℂ] H)‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hG'
  have h2 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)
  calc ‖G‖ ≤ ‖(c : ℂ) • (1 : H →L[ℂ] H)‖ := h1
    _ = ‖(c : ℂ)‖ * ‖(1 : H →L[ℂ] H)‖ := norm_smul _ _
    _ = c * ‖(1 : H →L[ℂ] H)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hc]
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left h2 hc
    _ = c := mul_one c

/-- If `G` and `G'` are positive with `G + G' = c • 1`, then `‖G‖ ≤ c`. -/
theorem norm_le_of_add_eq_smul_one {G G' : H →L[ℂ] H} {c : ℝ} (hc : 0 ≤ c)
    (hG : G.IsPositive) (hG' : G'.IsPositive)
    (h : G + G' = (c : ℂ) • (1 : H →L[ℂ] H)) : ‖G‖ ≤ c := by
  refine norm_le_of_isPositive_of_isPositive_sub hc hG ?_
  have e : (c : ℂ) • (1 : H →L[ℂ] H) - G = G' := by
    rw [← h]
    abel
  rw [e]
  exact hG'

/-! ### Pieces of a decreasing chain -/

/-- If `B (1 - Q) ≥ 0`, `P ≥ 0` commutes with `B`, and `Q ≤ P` are projections
(`P Q = Q = Q P`), then `B (P - Q) ≥ 0`. -/
theorem isPositive_mul_sub_of_right {B P Q : H →L[ℂ] H} (hBQ : (B * (1 - Q)).IsPositive)
    (hP : P.IsPositive) (hPB : P * B = B * P) (hPQ : P * Q = Q) (hQP : Q * P = Q) :
    (B * (P - Q)).IsPositive := by
  have e1 : B * (1 - Q) * P = B * (P - Q) := by
    rw [mul_assoc, sub_mul, one_mul, hQP]
  have e2 : P * (B * (1 - Q)) = B * (P - Q) := by
    rw [← mul_assoc, hPB, mul_assoc, mul_sub, mul_one, hPQ]
  have h := isPositive_mul_of_commute hBQ hP (e1.trans e2.symm)
  rwa [e1] at h

/-- If `C P ≥ 0`, `1 - Q ≥ 0` with `Q` commuting with `C`, and `P Q = Q = Q P`, then
`C (P - Q) ≥ 0`. -/
theorem isPositive_mul_sub_of_left {C P Q : H →L[ℂ] H} (hCP : (C * P).IsPositive)
    (hQ : (1 - Q).IsPositive) (hQC : Q * C = C * Q) (hPQ : P * Q = Q) (hQP : Q * P = Q) :
    (C * (P - Q)).IsPositive := by
  have e1 : C * P * (1 - Q) = C * (P - Q) := by
    rw [mul_assoc, mul_sub, mul_one, hPQ]
  have e2 : (1 - Q) * (C * P) = C * (P - Q) := by
    rw [sub_mul, one_mul, ← mul_assoc, hQC, mul_assoc, hQP, mul_sub]
  have h := isPositive_mul_of_commute hCP hQ (e1.trans e2.symm)
  rwa [e1] at h

omit [CompleteSpace H] in
/-- Real and complex scalar multiplication agree on `B(H)`. -/
theorem real_smul_eq_complex_smul (r : ℝ) (T : H →L[ℂ] H) : r • T = (r : ℂ) • T := by
  first
    | exact (Complex.coe_smul r T).symm

omit [CompleteSpace H] in
/-- Sum of the two families of pieces: `∑ (u_{k+1} - A) F_k + ∑ (A - u_k) F_k = c (P_0 - P_n)`
when `u_{k+1} = u_k + c` and `F_k = P_k - P_{k+1}`. -/
theorem chain_sum_add (A : H →L[ℂ] H) (P : ℕ → (H →L[ℂ] H)) (u : ℕ → ℝ) (c : ℝ)
    (hu : ∀ k, u (k + 1) = u k + c) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((u (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (P k - P (k + 1)))
      + (∑ k ∈ Finset.range n, (A - (u k : ℂ) • (1 : H →L[ℂ] H)) * (P k - P (k + 1)))
      = (c : ℂ) • (P 0 - P n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcu : (u (n + 1) : ℂ) = (u n : ℂ) + (c : ℂ) := by
      rw [hu n, Complex.ofReal_add]
    have hterm : ((u (n + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (P n - P (n + 1))
        + (A - (u n : ℂ) • (1 : H →L[ℂ] H)) * (P n - P (n + 1))
        = (c : ℂ) • (P n - P (n + 1)) := by
      rw [← add_mul, hcu, add_smul]
      have h3 : (u n : ℂ) • (1 : H →L[ℂ] H) + (c : ℂ) • (1 : H →L[ℂ] H) - A
          + (A - (u n : ℂ) • (1 : H →L[ℂ] H)) = (c : ℂ) • (1 : H →L[ℂ] H) := by
        abel
      rw [h3, smul_mul_assoc, one_mul]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_add_add_comm, ih, hterm, ← smul_add]
    congr 1
    abel

omit [CompleteSpace H] in
/-- Closed form (Abel summation) of `∑ (u_{k+1} - A) (P_k - P_{k+1})`. -/
theorem chain_sum_closed (A : H →L[ℂ] H) (P : ℕ → (H →L[ℂ] H)) (u : ℕ → ℝ) (c : ℝ)
    (hu : ∀ k, u (k + 1) = u k + c) (n : ℕ) :
    (∑ k ∈ Finset.range n, ((u (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (P k - P (k + 1)))
      = (c : ℂ) • (∑ k ∈ Finset.range n, P k) + ((u 0 : ℂ) • P 0 - (u n : ℂ) • P n)
        - A * (P 0 - P n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcu : (u (n + 1) : ℂ) = (u n : ℂ) + (c : ℂ) := by
      rw [hu n, Complex.ofReal_add]
    have hPn : (u (n + 1) : ℂ) • P n = (u n : ℂ) • P n + (c : ℂ) • P n := by
      rw [hcu, add_smul]
    have e : ((u (n + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (P n - P (n + 1))
        = (u n : ℂ) • P n + (c : ℂ) • P n - (u (n + 1) : ℂ) • P (n + 1)
          - (A * P n - A * P (n + 1)) := by
      rw [sub_mul, smul_mul_assoc, one_mul, mul_sub, smul_sub, hPn]
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, e]
    simp only [mul_sub, smul_add]
    abel

omit [CompleteSpace H] in
/-- `∑_{k<n} (P_k + P_k - 1) = S + S - n • 1` with `S = ∑_{k<n} P_k`. -/
theorem sum_range_add_self_sub_one (P : ℕ → (H →L[ℂ] H)) (n : ℕ) :
    ∑ k ∈ Finset.range n, (P k + P k - 1)
      = (∑ k ∈ Finset.range n, P k) + (∑ k ∈ Finset.range n, P k)
        - (n : ℝ) • (1 : H →L[ℂ] H) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Nat.cast_add_one, add_smul, one_smul]
    abel

end ReflectionApprox

open ReflectionApprox

/-! ### The abstract statement for a finite decreasing chain -/

/-- **Finite decreasing chain.**  Let `P_0 = 1 ≥ P_1 ≥ … ≥ P_N = 0` be self-adjoint idempotents
commuting with `A`, and `u_0 = -1`, `u_{k+1} = u_k + c` thresholds with `(A - u_k) P_k ≥ 0`
(`k < N`) and `(u_{k+1} - A) (1 - P_{k+1}) ≥ 0` (`k < N`).  Then
`‖A - (c • ∑_{k<N} P_k - 1)‖ ≤ c`. -/
theorem norm_sub_chain_average_le {A : H →L[ℂ] H} (P : ℕ → (H →L[ℂ] H)) (u : ℕ → ℝ) (c : ℝ)
    (N : ℕ) (hc : 0 ≤ c) (hu : ∀ k, u (k + 1) = u k + c)
    (hPsa : ∀ k, IsSelfAdjoint (P k)) (hPid : ∀ k, P k * P k = P k)
    (hPA : ∀ k, P k * A = A * P k)
    (hPmono : ∀ k, P k * P (k + 1) = P (k + 1))
    (hpos : ∀ k, k < N → ((A - (u k : ℂ) • (1 : H →L[ℂ] H)) * P k).IsPositive)
    (hneg : ∀ k, k < N →
      (((u (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (1 - P (k + 1))).IsPositive)
    (h0 : P 0 = 1) (hN : P N = 0) (hu0 : u 0 = -1) :
    ‖A - (c • (∑ k ∈ Finset.range N, P k) - 1)‖ ≤ c := by
  have hmono' : ∀ k, P (k + 1) * P k = P (k + 1) := fun k => by
    have h := congrArg star (hPmono k)
    rwa [star_mul, (hPsa k).star_eq, (hPsa (k + 1)).star_eq] at h
  have hG : (∑ k ∈ Finset.range N,
      ((u (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (P k - P (k + 1))).IsPositive := by
    refine ContinuousLinearMap.isPositive_sum _ (fun k hk => ?_)
    have hk' : k < N := Finset.mem_range.mp hk
    refine isPositive_mul_sub_of_right (hneg k hk')
      (isPositive_of_isSelfAdjoint_of_idem (hPsa k) (hPid k)) ?_ (hPmono k) (hmono' k)
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hPA k]
  have hG' : (∑ k ∈ Finset.range N,
      (A - (u k : ℂ) • (1 : H →L[ℂ] H)) * (P k - P (k + 1))).IsPositive := by
    refine ContinuousLinearMap.isPositive_sum _ (fun k hk => ?_)
    have hk' : k < N := Finset.mem_range.mp hk
    refine isPositive_mul_sub_of_left (hpos k hk')
      (isPositive_one_sub_of_isSelfAdjoint_of_idem (hPsa (k + 1)) (hPid (k + 1))) ?_
      (hPmono k) (hmono' k)
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hPA (k + 1)]
  have hsum := chain_sum_add A P u c hu N
  rw [h0, hN, sub_zero] at hsum
  have hnorm := norm_le_of_add_eq_smul_one hc hG hG' hsum
  have hclosed := chain_sum_closed A P u c hu N
  rw [h0, hN, hu0] at hclosed
  simp only [smul_zero, sub_zero, mul_one, Complex.ofReal_neg, Complex.ofReal_one, neg_smul,
    one_smul] at hclosed
  have e : A - (c • (∑ k ∈ Finset.range N, P k) - 1)
      = -(∑ k ∈ Finset.range N,
        ((u (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A) * (P k - P (k + 1))) := by
    rw [hclosed, real_smul_eq_complex_smul]
    abel
  rw [e, norm_neg]
  exact hnorm

/-! ### Thresholds and the chain of threshold projections -/

namespace ReflectionApprox

/-- The thresholds `u_k = -1 + (2/N) k`. -/
noncomputable def threshold (N k : ℕ) : ℝ := -1 + 2 / (N : ℝ) * (k : ℝ)

theorem threshold_zero (N : ℕ) : threshold N 0 = -1 := by
  simp [threshold]

theorem threshold_succ (N k : ℕ) : threshold N (k + 1) = threshold N k + 2 / (N : ℝ) := by
  unfold threshold
  push_cast
  ring

theorem threshold_self {N : ℕ} (hN : 0 < N) : threshold N N = 1 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h : 2 / (N : ℝ) * (N : ℝ) = 2 := by
    first
      | exact div_mul_cancel₀ 2 hNne
  unfold threshold
  rw [h]
  norm_num

theorem threshold_le_succ (N k : ℕ) : threshold N k ≤ threshold N (k + 1) := by
  rw [threshold_succ]
  have h : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  linarith

/-- The decreasing chain `P_0 = 1`, `P_k = E u_k` (`0 < k < N`), `P_k = 0` (`k ≥ N`). -/
noncomputable def chainProj (E : ℝ → (H →L[ℂ] H)) (N k : ℕ) : H →L[ℂ] H :=
  if k = 0 then 1 else if k < N then E (threshold N k) else 0

omit [CompleteSpace H] in
theorem chainProj_zero (E : ℝ → (H →L[ℂ] H)) (N : ℕ) : chainProj E N 0 = 1 := by
  simp [chainProj]

omit [CompleteSpace H] in
theorem chainProj_of_lt (E : ℝ → (H →L[ℂ] H)) {N k : ℕ} (hk : k ≠ 0) (hkN : k < N) :
    chainProj E N k = E (threshold N k) := by
  simp [chainProj, hk, hkN]

omit [CompleteSpace H] in
theorem chainProj_of_not_lt (E : ℝ → (H →L[ℂ] H)) {N k : ℕ} (hk : k ≠ 0) (hkN : ¬ k < N) :
    chainProj E N k = 0 := by
  simp [chainProj, hk, hkN]

theorem chainProj_mem (M : VonNeumannAlgebra H) {E : ℝ → (H →L[ℂ] H)} (hEM : ∀ u, E u ∈ M)
    (N k : ℕ) : chainProj E N k ∈ M := by
  by_cases hk : k = 0
  · subst hk
    rw [chainProj_zero]
    exact one_mem M
  · by_cases hkN : k < N
    · rw [chainProj_of_lt E hk hkN]
      exact hEM _
    · rw [chainProj_of_not_lt E hk hkN]
      exact zero_mem M

theorem chainProj_isSelfAdjoint {E : ℝ → (H →L[ℂ] H)} (hEsa : ∀ u, IsSelfAdjoint (E u))
    (N k : ℕ) : IsSelfAdjoint (chainProj E N k) := by
  by_cases hk : k = 0
  · subst hk
    rw [chainProj_zero]
    exact isSelfAdjoint_one_op
  · by_cases hkN : k < N
    · rw [chainProj_of_lt E hk hkN]
      exact hEsa _
    · rw [chainProj_of_not_lt E hk hkN]
      exact isSelfAdjoint_zero_op

omit [CompleteSpace H] in
theorem chainProj_idem {E : ℝ → (H →L[ℂ] H)} (hEid : ∀ u, E u * E u = E u) (N k : ℕ) :
    chainProj E N k * chainProj E N k = chainProj E N k := by
  by_cases hk : k = 0
  · subst hk
    rw [chainProj_zero, mul_one]
  · by_cases hkN : k < N
    · rw [chainProj_of_lt E hk hkN]
      exact hEid _
    · rw [chainProj_of_not_lt E hk hkN, mul_zero]

omit [CompleteSpace H] in
theorem chainProj_comm {A : H →L[ℂ] H} {E : ℝ → (H →L[ℂ] H)}
    (hEA : ∀ u, E u * A = A * E u) (N k : ℕ) :
    chainProj E N k * A = A * chainProj E N k := by
  by_cases hk : k = 0
  · subst hk
    rw [chainProj_zero, one_mul, mul_one]
  · by_cases hkN : k < N
    · rw [chainProj_of_lt E hk hkN]
      exact hEA _
    · rw [chainProj_of_not_lt E hk hkN, zero_mul, mul_zero]

omit [CompleteSpace H] in
theorem chainProj_mono {E : ℝ → (H →L[ℂ] H)} (hmono : ∀ u v, u ≤ v → E u * E v = E v)
    (N k : ℕ) : chainProj E N k * chainProj E N (k + 1) = chainProj E N (k + 1) := by
  by_cases hk1 : k + 1 < N
  · rw [chainProj_of_lt E (show k + 1 ≠ 0 by omega) hk1]
    by_cases hk : k = 0
    · subst hk
      rw [chainProj_zero, one_mul]
    · rw [chainProj_of_lt E hk (show k < N by omega)]
      exact hmono _ _ (threshold_le_succ N k)
  · rw [chainProj_of_not_lt E (show k + 1 ≠ 0 by omega) hk1, mul_zero]

end ReflectionApprox

open ReflectionApprox

/-! ### The approximation theorems -/

/-- A self-adjoint contraction with threshold projections is within `2/N` of an average of `N`
reflections. -/
theorem exists_reflection_average_near (M : VonNeumannAlgebra H) {A : H →L[ℂ] H}
    (hA : A ∈ saContractions M)
    (E : ℝ → (H →L[ℂ] H))
    (hEM : ∀ u, E u ∈ M) (hEsa : ∀ u, IsSelfAdjoint (E u)) (hEid : ∀ u, E u * E u = E u)
    (hEA : ∀ u, E u * A = A * E u)
    (hpos : ∀ u : ℝ, ((A - (u : ℂ) • (1 : H →L[ℂ] H)) * E u).IsPositive)
    (hneg : ∀ u : ℝ, (((u : ℂ) • (1 : H →L[ℂ] H) - A) * (1 - E u)).IsPositive)
    (hmono : ∀ u v, u ≤ v → E u * E v = E v)
    (N : ℕ) (hN : 0 < N) :
    ∃ R : Fin N → (H →L[ℂ] H), (∀ k, R k ∈ reflections M) ∧
      ‖A - (1 / (N : ℝ)) • ∑ k, R k‖ ≤ 2 / (N : ℝ) := by
  have hA' : A ∈ M ∧ IsSelfAdjoint A ∧ ‖A‖ ≤ 1 := hA
  obtain ⟨_hAM, hAsa, hAn⟩ := hA'
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hposc : ∀ k, k < N →
      ((A - (threshold N k : ℂ) • (1 : H →L[ℂ] H)) * chainProj E N k).IsPositive := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      have e : A - ((-1 : ℝ) : ℂ) • (1 : H →L[ℂ] H) = 1 + A := by
        rw [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul]
        abel
      rw [chainProj_zero, threshold_zero, mul_one, e]
      exact isPositive_one_add_of_saContraction hAsa hAn
    · rw [chainProj_of_lt E hk0 hk]
      exact hpos _
  have hnegc : ∀ k, k < N →
      (((threshold N (k + 1) : ℂ) • (1 : H →L[ℂ] H) - A)
        * (1 - chainProj E N (k + 1))).IsPositive := by
    intro k hk
    by_cases hk1 : k + 1 < N
    · rw [chainProj_of_lt E (show k + 1 ≠ 0 by omega) hk1]
      exact hneg _
    · have hkN : k + 1 = N := by omega
      have hth : threshold N (k + 1) = 1 := by
        rw [hkN]
        exact threshold_self hN
      rw [chainProj_of_not_lt E (show k + 1 ≠ 0 by omega) hk1, hth, sub_zero, mul_one,
        Complex.ofReal_one, one_smul]
      exact isPositive_one_sub_of_saContraction hAsa hAn
  have hmain := norm_sub_chain_average_le (A := A) (chainProj E N) (threshold N)
    (2 / (N : ℝ)) N (by positivity) (threshold_succ N) (chainProj_isSelfAdjoint hEsa N)
    (chainProj_idem hEid N) (chainProj_comm hEA N) (chainProj_mono hmono N) hposc hnegc
    (chainProj_zero E N) (chainProj_of_not_lt E hN.ne' (lt_irrefl N)) (threshold_zero N)
  refine ⟨fun k : Fin N => chainProj E N k + chainProj E N k - 1, fun k => ?_, ?_⟩
  · exact add_self_sub_one_mem_reflections (chainProj_mem M hEM N k)
      (chainProj_isSelfAdjoint hEsa N k) (chainProj_idem hEid N k)
  · have hfin : ∑ k : Fin N, (chainProj E N k + chainProj E N k - 1)
        = ∑ k ∈ Finset.range N, (chainProj E N k + chainProj E N k - 1) :=
      Fin.sum_univ_eq_sum_range (fun k => chainProj E N k + chainProj E N k - 1) N
    have h2 : 1 / (N : ℝ) + 1 / (N : ℝ) = 2 / (N : ℝ) := by ring
    have e : (1 / (N : ℝ)) • ∑ k : Fin N, (chainProj E N k + chainProj E N k - 1)
        = (2 / (N : ℝ)) • (∑ k ∈ Finset.range N, chainProj E N k) - 1 := by
      rw [hfin, sum_range_add_self_sub_one (chainProj E N) N, smul_sub, smul_add, smul_smul,
        one_div_mul_cancel hNne, one_smul, ← add_smul, h2]
    change ‖A - (1 / (N : ℝ)) • ∑ k : Fin N, (chainProj E N k + chainProj E N k - 1)‖
      ≤ 2 / (N : ℝ)
    rw [e]
    exact hmain

/-- A self-adjoint contraction with threshold projections lies in the norm closure of the
convex hull of the reflections. -/
theorem mem_closure_convexHull_reflections_of_thresholds (M : VonNeumannAlgebra H)
    {A : H →L[ℂ] H} (hA : A ∈ saContractions M)
    (E : ℝ → (H →L[ℂ] H))
    (hEM : ∀ u, E u ∈ M) (hEsa : ∀ u, IsSelfAdjoint (E u)) (hEid : ∀ u, E u * E u = E u)
    (hEA : ∀ u, E u * A = A * E u)
    (hpos : ∀ u : ℝ, ((A - (u : ℂ) • (1 : H →L[ℂ] H)) * E u).IsPositive)
    (hneg : ∀ u : ℝ, (((u : ℂ) • (1 : H →L[ℂ] H) - A) * (1 - E u)).IsPositive)
    (hmono : ∀ u v, u ≤ v → E u * E v = E v) :
    A ∈ closure (convexHull ℝ (reflections M)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ε)
  have h2ε : (0 : ℝ) < 2 / ε := by positivity
  have hnpos : (0 : ℝ) < n := lt_trans h2ε hn
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hn0 : 0 < n := Nat.cast_pos.mp hnpos
  obtain ⟨R, hR, hnorm⟩ :=
    exists_reflection_average_near M hA E hEM hEsa hEid hEA hpos hneg hmono n hn0
  have hsum : ∑ _k : Fin n, (1 / (n : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel hnne
  have key : ∑ k : Fin n, (1 / (n : ℝ)) • R k ∈ convexHull ℝ (reflections M) :=
    (convex_convexHull ℝ (reflections M)).sum_mem (fun _ _ => by positivity) hsum
      (fun k _ => subset_convexHull ℝ _ (hR k))
  refine ⟨(1 / (n : ℝ)) • ∑ k, R k, ?_, ?_⟩
  · rw [Finset.smul_sum]
    exact key
  · rw [dist_eq_norm]
    exact lt_of_le_of_lt hnorm ((div_lt_comm₀ hnpos hε).mpr hn)

end VacuumBellSeparation
