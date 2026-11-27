/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.RandomMatrixAlgebra
public import LeanPool.KLRandomness.FiniteProbability
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Uniform binary matrices and rank failure

The probability space in this file consists of all binary matrices, with
the actual uniform counting probability. For every nonzero row functional,
its evaluations on any `N` selected columns are uniformly distributed in
`(ZMod 2)^N`. Union over the `2^r - 1` nonzero row functionals yields the
rank-failure estimate for an `r`-row matrix.
-/

@[expose] public section

namespace Klr.RandomMatrix

open scoped BigOperators
open FiniteProbability

section Fiber

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod 2) V] [Module (ZMod 2) W]
  [Fintype V] [Module.Finite (ZMod 2) V]

/-- Every fiber of a surjective binary linear map has the same exact
uniform counting probability. -/
theorem binary_fiber_probability (D : V →ₗ[ZMod 2] W)
    (hD : Function.Surjective D) (z : W) :
    probability {x | D x = z} = (1 / 2 : ℝ) ^ Module.finrank (ZMod 2) W := by
  have hd := D.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD, finrank_top] at hd
  have hr : Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) V := by omega
  rw [probability_eq_card]
  change (Nat.card (Affine.Fiber D z) : ℝ) / Fintype.card V = _
  rw [Affine.card_fiber_of_surjective D hD z, Module.card_eq_pow_finrank (K := ZMod 2)]
  simp only [Nat.card_zmod, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  have hp : (2 : ℝ) ^ Module.finrank (ZMod 2) V =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W) *
        2 ^ Module.finrank (ZMod 2) W := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [hp, div_mul_eq_div_div, div_self (by positivity)]
  simp

end Fiber

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

/-- The sample space of all binary `r`-row matrices with columns indexed by `ι`. -/
abbrev BinaryMatrix (ι : Type*) (r : ℕ) := ι → (Fin r → ZMod 2)

instance finiteBinaryDual : Finite (Module.Dual (ZMod 2) (Fin r → ZMod 2)) :=
  Finite.of_injective
    (fun φ : Module.Dual (ZMod 2) (Fin r → ZMod 2) => (φ : (Fin r → ZMod 2) → ZMod 2))
    DFunLike.coe_injective

/-- A fixed nonzero row combination vanishes on all selected columns with
probability exactly `2^(-T.card)`. -/
theorem annihilator_probability (φ : Module.Dual (ZMod 2) (Fin r → ZMod 2))
    (hφ : φ ≠ 0) (T : Finset ι) :
    probability {B : BinaryMatrix ι r | evaluationMap φ T B = 0} =
      (1 / 2 : ℝ) ^ T.card := by
  simpa using binary_fiber_probability (evaluationMap φ T)
    (evaluationMap_surjective hφ T) 0

/-- There are exactly `2^r - 1` nonzero row functionals. -/
theorem card_nonzero_dual :
    Nat.card {φ : Module.Dual (ZMod 2) (Fin r → ZMod 2) // φ ≠ 0} = 2 ^ r - 1 := by
  classical
  let _ := Fintype.ofFinite (Module.Dual (ZMod 2) (Fin r → ZMod 2))
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Module.card_eq_pow_finrank (K := ZMod 2)]
  simp [Subspace.dual_finrank_eq]

/-- The union bound for actual uniformly chosen binary matrices. It applies
to an arbitrary finite column type, including a sampled support subtype. -/
theorem restricted_failure_probability_le (T : Finset ι) :
    probability {B : BinaryMatrix ι r |
      ¬ Function.Surjective (restrictedMap B T (K := ZMod 2))} ≤
        ((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ T.card := by
  classical
  let Φ := {φ : Module.Dual (ZMod 2) (Fin r → ZMod 2) // φ ≠ 0}
  let _ : Fintype Φ := Fintype.ofFinite Φ
  have he : {B : BinaryMatrix ι r |
      ¬ Function.Surjective (restrictedMap B T (K := ZMod 2))} =
      ⋃ φ : Φ, {B | evaluationMap φ.val T B = 0} := by
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, restricted_not_surjective_iff]
    exact ⟨fun ⟨φ, hφ, hB⟩ => ⟨⟨φ, hφ⟩, hB⟩,
      fun ⟨φ, hB⟩ => ⟨φ.val, φ.property, hB⟩⟩
  rw [he]
  calc
    _ ≤ ∑ φ : Φ, probability {B : BinaryMatrix ι r | evaluationMap φ.val T B = 0} :=
      probability_iUnion_le _
    _ = (Fintype.card Φ : ℝ) * (1 / 2 : ℝ) ^ T.card := by
      calc
        _ = ∑ _φ : Φ, (1 / 2 : ℝ) ^ T.card :=
          Finset.sum_congr rfl (fun φ _ => annihilator_probability φ.val φ.property T)
        _ = _ := by simp
    _ = _ := by rw [← Nat.card_eq_fintype_card, card_nonzero_dual]

/-- A binary matrix has full row rank when its column map is surjective. -/
def FullRowRank (B : BinaryMatrix ι r) : Prop :=
  Function.Surjective (columnMap B (K := ZMod 2))

/-- The actual finite sample space used when the matrix is drawn uniformly
conditional on full row rank. -/
abbrev FullRankMatrix (ι : Type*) [Fintype ι] (r : ℕ) :=
  ↥{B : BinaryMatrix ι r | FullRowRank B}

noncomputable instance fullRankMatrixFintype : Fintype (FullRankMatrix ι r) :=
  Fintype.ofFinite _

/-- The full matrix itself fails full row rank with probability at most
`(2^r - 1) / 2^m`, where `m` is its number of columns. -/
theorem failure_probability_le :
    probability {B : BinaryMatrix ι r | ¬ FullRowRank B} ≤
      ((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ Fintype.card ι := by
  simpa only [FullRowRank, restricted_univ_surjective_iff, Finset.card_univ] using
    (restricted_failure_probability_le (r := r) (Finset.univ : Finset ι))

/-- The full-rank mass lower bound follows from the same union estimate. -/
theorem full_rank_probability_ge :
    1 - ((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ Fintype.card ι ≤
      probability {B : BinaryMatrix ι r | FullRowRank B} := by
  have h := failure_probability_le (ι := ι) (r := r)
  have hc := probability_compl {B : BinaryMatrix ι r | FullRowRank B}
  change probability {B : BinaryMatrix ι r | ¬ FullRowRank B} =
    1 - probability {B : BinaryMatrix ι r | FullRowRank B} at hc
  linarith

section Conditioning

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Uniformly sampling an event subtype is exactly conditioning uniform
counting probability on that event. This identity also holds for an empty
subtype, with the usual field convention for division by zero. -/
theorem probability_subtype (A H : Set Ω) [Fintype H] :
    probability {x : H | x.val ∈ A} = probability (A ∩ H) / probability H := by
  classical
  let e : ↥{x : H | x.val ∈ A} ≃ ↥(A ∩ H) :=
    { toFun := fun x => ⟨x.val.val, x.property, x.val.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [probability_eq_card, probability_eq_card, probability_eq_card,
    Nat.card_congr e, Nat.card_eq_fintype_card (α := H)]
  symm
  exact div_div_div_cancel_right₀ (ne_of_gt (card_pos (Ω := Ω))) _ _

/-- Conditioning on an event of mass at least one half increases the
probability of any event by at most a factor of two. -/
theorem probability_subtype_le_two (A H : Set Ω) [Fintype H]
    (hH : (1 / 2 : ℝ) ≤ probability H) :
    probability {x : H | x.val ∈ A} ≤ 2 * probability A := by
  rw [probability_subtype]
  apply (div_le_iff₀ (by linarith : 0 < probability H)).mpr
  have hi : probability (A ∩ H) ≤ probability A := probability_mono Set.inter_subset_left
  have hm := mul_le_mul_of_nonneg_left hH (probability_nonneg A)
  nlinarith

end Conditioning

/-- In the actual uniform full-rank matrix sample space, restricted rank
failure costs at most twice the unrestricted rank-failure estimate. -/
theorem full_rank_restricted_failure_probability_le (T : Finset ι)
    (hfull : (1 / 2 : ℝ) ≤ probability {B : BinaryMatrix ι r | FullRowRank B}) :
    probability {B : FullRankMatrix ι r |
      ¬ Function.Surjective (restrictedMap B.val T (K := ZMod 2))} ≤
        2 * (((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ T.card) := by
  calc
    _ ≤ 2 * probability {B : BinaryMatrix ι r |
        ¬ Function.Surjective (restrictedMap B T (K := ZMod 2))} :=
      probability_subtype_le_two _ _ hfull
    _ ≤ _ := by gcongr; exact restricted_failure_probability_le T

/-- The numerical rank-error hypothesis guarantees that the conditioning
event has mass at least one half. -/
theorem half_le_full_rank_probability
    (h : ((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ Fintype.card ι ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ probability {B : BinaryMatrix ι r | FullRowRank B} := by
  have hl := full_rank_probability_ge (ι := ι) (r := r)
  linarith

/-- A positive full-rank mass gives an actual full-rank matrix. -/
theorem nonempty_fullRankMatrix
    (h : 0 < probability {B : BinaryMatrix ι r | FullRowRank B}) :
    Nonempty (FullRankMatrix ι r) := by
  have hc := probability_compl {B : BinaryMatrix ι r | FullRowRank B}
  have hb : probability ({B : BinaryMatrix ι r | FullRowRank B}ᶜ) < 1 := by linarith
  obtain ⟨B, hB⟩ := exists_not_mem_of_probability_lt_one _ hb
  exact ⟨B, by simpa using hB⟩

/-- The rank-error expression loses one factor `2` per extra column,
uniformly in the number of rows. -/
theorem rank_error_le_pow (r n k : ℕ) (h : r + k ≤ n) :
    ((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ k := by
  have hc : ((2 ^ r - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast Nat.sub_le (2 ^ r) 1
  calc
    _ ≤ (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (r + k) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) (by positivity)
    _ = _ := by rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num

/-- One more column than rows suffices for full-rank mass at least one half. -/
theorem half_le_full_rank_probability_of_card (hm : r + 1 ≤ Fintype.card ι) :
    (1 / 2 : ℝ) ≤ probability {B : BinaryMatrix ι r | FullRowRank B} := by
  apply half_le_full_rank_probability
  simpa using rank_error_le_pow r (Fintype.card ι) 1 hm

omit [DecidableEq ι] in
/-- The full-rank matrix sample type is inhabited under the usual spare-column
condition. This supplies a genuine uniform finite experiment. -/
theorem nonempty_fullRankMatrix_of_card (hm : r + 1 ≤ Fintype.card ι) :
    Nonempty (FullRankMatrix ι r) := by
  classical
  apply nonempty_fullRankMatrix
  have h := half_le_full_rank_probability_of_card hm
  linarith

/-- With at least twice as many selected columns as rows, the full-rank
conditioned restriction fails with probability at most `2 * 2^(-r)`. -/
theorem full_rank_restricted_failure_probability_le_pow (T : Finset ι)
    (hfull : (1 / 2 : ℝ) ≤ probability {B : BinaryMatrix ι r | FullRowRank B})
    (hT : 2 * r ≤ T.card) :
    probability {B : FullRankMatrix ι r |
      ¬ Function.Surjective (restrictedMap B.val T (K := ZMod 2))} ≤
        2 * (1 / 2 : ℝ) ^ r := by
  calc
    _ ≤ 2 * (((2 ^ r - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ T.card) :=
      full_rank_restricted_failure_probability_le T hfull
    _ ≤ _ := mul_le_mul_of_nonneg_left (rank_error_le_pow r T.card r (by omega))
      (by norm_num)

omit [DecidableEq ι] in
/-- A version whose hypotheses are entirely column-count inequalities. -/
theorem full_rank_restricted_failure_probability_le_pow_of_card (T : Finset ι)
    (hm : r + 1 ≤ Fintype.card ι) (hT : 2 * r ≤ T.card) :
    probability {B : FullRankMatrix ι r |
      ¬ Function.Surjective (restrictedMap B.val T (K := ZMod 2))} ≤
        2 * (1 / 2 : ℝ) ^ r := by
  classical
  exact full_rank_restricted_failure_probability_le_pow T
    (half_le_full_rank_probability_of_card hm) hT

end Klr.RandomMatrix
