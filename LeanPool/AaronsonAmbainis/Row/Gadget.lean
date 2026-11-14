/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import LeanPool.AaronsonAmbainis.Row.Extension
public import LeanPool.AaronsonAmbainis.Row.Degree

/-!
# The Chebyshev gadget

The function `G` of the proof of the block inequality (Lemma 6.4 of the paper).
For blocks `S b ⊆ ι` (`b : β`), a point `x` and coefficients `a_T`:
`cnt S i w = #{b : i ∈ S b, w b = true}`, `gate S m c i w = T_m (1 - c * cnt S i w)` and
`gadget a x S m c w = ∑_T a_T ∏_{i ∈ T} (sgn (x i) * gate S m c i w)`.
In the paper these are written `cnt_i(w)`, `θ_i(w)` and `G(w)`.

The lemmas `abs_gadget_le_one`, `hasDegreeLE_gadget`, `gadget_zero` and `gadget_unit` are the
properties (a)–(d) of `G` in that proof, each under the hypotheses it needs: `G` is bounded by
`1`, it has degree at most `d * m`, and it takes the value `∑_T a_T chi_T(x)` at `Row.zero β` and,
for `m ≥ 1` and `c = 1 - cos (π / m)`, the value `∑_T a_T chi_T(x^{S b})` at `Row.unit b`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Finset Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β]

/-- `cnt_i(w)`: the number of blocks `b ∋ i` with `w b = true`, as a real number. -/
noncomputable def cnt (S : β → Finset ι) (i : ι) (w : Cube β) : ℝ :=
  ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (if w b then (1 : ℝ) else 0)

/-- `θ_i(w) = T_m (1 - c cnt_i(w))`. -/
noncomputable def gate (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) (w : Cube β) : ℝ :=
  (Chebyshev.T ℝ m).eval (1 - c * cnt S i w)

/-- `G(w) = ∑_T a_T ∏_{i ∈ T} (sgn (x i) θ_i(w))`. -/
noncomputable def gadget (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ)
    (w : Cube β) : ℝ :=
  ∑ T : Finset ι, a T * ∏ i ∈ T, (sgn (x i) * gate S m c i w)

omit [Fintype ι] in
lemma cnt_nonneg (S : β → Finset ι) (i : ι) (w : Cube β) : 0 ≤ cnt S i w := by
  unfold cnt
  refine Finset.sum_nonneg (fun b _ => ?_)
  split_ifs <;> norm_num

omit [Fintype ι] in
lemma cnt_le (S : β → Finset ι) (N : ℕ)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (i : ι) (w : Cube β) :
    cnt S i w ≤ N := by
  unfold cnt
  calc ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (if w b then (1 : ℝ) else 0)
      ≤ ∑ b ∈ univ.filter (fun b : β => i ∈ S b), (1 : ℝ) := by
        refine Finset.sum_le_sum (fun b _ => ?_)
        split_ifs <;> norm_num
    _ = ((univ.filter fun b : β => i ∈ S b).card : ℝ) := by simp
    _ ≤ N := by exact_mod_cast hN i

omit [Fintype ι] in
lemma cnt_zero (S : β → Finset ι) (i : ι) : cnt S i (zero β) = 0 := by
  simp [cnt, zero]

omit [Fintype ι] in
lemma cnt_unit [DecidableEq β] (S : β → Finset ι) (i : ι) (b : β) :
    cnt S i (unit b) = if i ∈ S b then 1 else 0 := by
  simp [cnt, unit]

omit [Fintype ι] in
lemma hasDegreeLE_cnt (S : β → Finset ι) (i : ι) : HasDegreeLE (cnt S i) 1 :=
  hasDegreeLE_congr
    (hasDegreeLE_sum (univ.filter (fun b : β => i ∈ S b))
      (fun b w => if w b then (1 : ℝ) else 0) (fun b _ => hasDegreeLE_indicator b))
    (fun _ => rfl)

omit [Fintype ι] in
lemma abs_gate_le_one (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (i : ι) (w : Cube β) : |gate S m c i w| ≤ 1 := by
  unfold gate
  have h0 := cnt_nonneg S i w
  have h1 := cnt_le S N hN i w
  have h2 : c * cnt S i w ≤ c * N := mul_le_mul_of_nonneg_left h1 hc
  have h3 : 0 ≤ c * cnt S i w := mul_nonneg hc h0
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_le.mpr ⟨by linarith, by linarith⟩)

omit [Fintype ι] in
lemma hasDegreeLE_gate (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) :
    HasDegreeLE (gate S m c i) m := by
  have h1 : HasDegreeLE (fun w : Cube β => 1 + (-c) * cnt S i w) 1 :=
    hasDegreeLE_add (hasDegreeLE_const 1 1) (hasDegreeLE_const_mul (-c) (hasDegreeLE_cnt S i))
  have h2 := hasDegreeLE_polyEval (Chebyshev.T ℝ (m : ℤ)) h1
  have h3 : (Chebyshev.T ℝ (m : ℤ)).natDegree = m := by
    rw [Chebyshev.natDegree_T]
    simp
  rw [h3] at h2
  refine hasDegreeLE_congr h2 (fun w => ?_)
  unfold gate
  congr 1
  ring

omit [Fintype ι] in
lemma gate_zero (S : β → Finset ι) (m : ℕ) (c : ℝ) (i : ι) : gate S m c i (zero β) = 1 := by
  unfold gate
  rw [cnt_zero, mul_zero, sub_zero, Chebyshev.T_eval_one]

omit [Fintype ι] in
lemma gate_unit [DecidableEq β] (S : β → Finset ι) (m : ℕ) (hm : 0 < m) (i : ι) (b : β) :
    gate S m (1 - Real.cos (Real.pi / (m : ℝ))) i (unit b) = if i ∈ S b then -1 else 1 := by
  unfold gate
  rw [cnt_unit]
  split_ifs with h
  · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have harg : ((m : ℤ) : ℝ) * (Real.pi / (m : ℝ)) = Real.pi := by
      push_cast
      field_simp
    rw [mul_one, sub_sub_cancel, Chebyshev.T_real_cos, harg, Real.cos_pi]
  · rw [mul_zero, sub_zero, Chebyshev.T_eval_one]

lemma abs_gadget_le_one (a : Finset ι → ℝ) (ha : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1)
    (x : Cube ι) (S : β → Finset ι) (N m : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hN : ∀ i, (univ.filter fun b : β => i ∈ S b).card ≤ N) (hNc : (N : ℝ) * c ≤ 2)
    (w : Cube β) : |gadget a x S m c w| ≤ 1 := by
  refine abs_multilinear_le_one a ha (fun i => sgn (x i) * gate S m c i w) (fun i => ?_)
  rw [abs_mul, abs_sgn, one_mul]
  exact abs_gate_le_one S N m c hc hN hNc i w

lemma hasDegreeLE_gadget (a : Finset ι → ℝ) (d : ℕ) (ha : ∀ T : Finset ι, d < T.card → a T = 0)
    (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    HasDegreeLE (gadget a x S m c) (d * m) := by
  have key : HasDegreeLE (fun w : Cube β => ∑ T ∈ (univ : Finset (Finset ι)),
      a T * ∏ i ∈ T, (sgn (x i) * gate S m c i w)) (d * m) := by
    apply hasDegreeLE_sum
    intro T _
    by_cases hT : T.card ≤ d
    · refine hasDegreeLE_const_mul _ (hasDegreeLE_mono (Nat.mul_le_mul_right m hT) ?_)
      exact hasDegreeLE_prod T (fun i w => sgn (x i) * gate S m c i w)
        (fun i _ => hasDegreeLE_const_mul _ (hasDegreeLE_gate S m c i))
    · exact hasDegreeLE_congr (hasDegreeLE_zero _)
        (fun w => by simp [ha T (not_le.mp hT)])
  exact hasDegreeLE_congr key (fun _ => rfl)

lemma gadget_zero (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ) (c : ℝ) :
    gadget a x S m c (zero β) = ∑ T, a T * chi T x := by
  unfold gadget
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [chi_eq_prod_sgn]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gate_zero, mul_one]

lemma gadget_unit [DecidableEq β] (a : Finset ι → ℝ) (x : Cube ι) (S : β → Finset ι) (m : ℕ)
    (hm : 0 < m) (b : β) :
    gadget a x S m (1 - Real.cos (Real.pi / (m : ℝ))) (unit b)
      = ∑ T, a T * chi T (flipSet x (S b)) := by
  unfold gadget
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [chi_flipSet]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [gate_unit S m hm]

end Row
end AaronsonAmbainis
