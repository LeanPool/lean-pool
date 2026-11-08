/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityIncrement
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Combinatorics.SetFamily.LYM

/-!
# Density Hales--Jewett: the base case and the inductive step

The binary base case, by Sperner's theorem, and the step from `k` to `k + 1` letters, by iterating
the density increment.

Both carry an explicit bound. For two letters it is `2 * ⌈1 / δ ^ 2⌉₊`. Passing from `k` to
`k + 1` letters with a bound `F` for `k` letters, `stepBound k F` iterates the dimension
`incrementBound k F` of one density increment once for each increment that fits below density
one. Shelah's bound `Combinatorics.Line.shelahBound` for the Hales--Jewett numbers enters it
through the Graham--Rothschild bound.

The induction is run in `DensityHalesJewett.isDHJBound_ack`, which bounds its result by the
Ackermann function.
-/

@[expose] public section

open Finset
open Combinatorics

namespace DensityHalesJewett

/-- Identify a binary word with the coordinates on which it equals `1`. -/
def binarySupport {ι : Type*} [Fintype ι] (w : ι → Fin 2) : Finset ι :=
  univ.filter fun i ↦ w i = 1

@[simp]
lemma mem_binarySupport {ι : Type*} [Fintype ι] {w : ι → Fin 2} {i : ι} :
    i ∈ binarySupport w ↔ w i = 1 := by
  simp [binarySupport]

/-- Two binary words are the ordered points of a combinatorial line exactly when their supports
are strictly comparable. -/
lemma binary_line_iff_ssubset {ι : Type*} [Fintype ι] (x y : ι → Fin 2) :
    (∃ l : Combinatorics.Line (Fin 2) ι, l 0 = x ∧ l 1 = y) ↔
      binarySupport x ⊂ binarySupport y := by
  constructor
  · rintro ⟨l, rfl, rfl⟩
    obtain ⟨i, hi⟩ := l.proper
    refine (ssubset_iff_of_subset ?_).2 ⟨i, by simp [hi], by simp [hi]⟩
    intro j hj
    cases hj' : l.idxFun j <;> simp_all
  · intro h
    obtain ⟨i, hiy, hix⟩ := exists_of_ssubset h
    rw [mem_binarySupport] at hiy hix
    have hsub (j : ι) (hj : x j = 1) : y j = 1 := by simpa using h.1 (mem_binarySupport.2 hj)
    clear h
    refine ⟨⟨fun j ↦ if x j = y j then some (x j) else none, i, by grind⟩, ?_, ?_⟩ <;>
      funext j <;> grind [Combinatorics.Line.coe_apply]

/-- A binary word is determined by its support. -/
lemma binarySupport_injective {ι : Type*} [Fintype ι] :
    Function.Injective (binarySupport : (ι → Fin 2) → Finset ι) := by
  intro x y hxy
  funext i
  have hi : x i = 1 ↔ y i = 1 := by simpa using Finset.ext_iff.mp hxy i
  grind

/-- A squared elementary upper bound for the normalized central binomial coefficient. -/
lemma centralBinom_ratio_sq_mul_le (m : ℕ) :
    ((Nat.centralBinom m : ℝ) / 4 ^ m) ^ 2 * (3 * m + 1) ≤ 1 := by
  induction m with
  | zero => norm_num [Nat.centralBinom]
  | succ m ih =>
      have hrec : ((m + 1 : ℕ) : ℝ) * Nat.centralBinom (m + 1) =
          2 * (2 * m + 1) * Nat.centralBinom m := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ m
      have hratio : (Nat.centralBinom (m + 1) : ℝ) / 4 ^ (m + 1) =
          ((Nat.centralBinom m : ℝ) / 4 ^ m) *
            ((2 * m + 1 : ℝ) / (2 * (m + 1))) := by
        rw [pow_succ]
        field_simp
        push_cast at hrec ⊢
        linear_combination 2 * hrec
      rw [hratio, mul_pow, mul_assoc]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) ih
      rw [div_pow, div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (by positivity))).mpr
      push_cast
      ring_nf
      nlinarith

/-- The middle binomial coefficient is at most the reciprocal square-root proportion of the
Boolean cube. -/
lemma centralBinom_ratio_le_inv_sqrt (m : ℕ) :
    (Nat.centralBinom m : ℝ) / 4 ^ m ≤ (√(3 * m + 1))⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (Real.sqrt_pos.2 (by positivity)),
    ← sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
  simpa [one_pow] using centralBinom_ratio_sq_mul_le m

/-- The two normalizations of the binomial denominator, one per half-dimension and one per
dimension, agree. -/
private lemma two_pow_two_mul (m : ℕ) : (2 : ℝ) ^ (2 * m) = 4 ^ m := by
  rw [pow_mul]
  norm_num

/-- Reduce the normalized middle binomial coefficient in any dimension to the central coefficient
in half that dimension. -/
lemma middleBinomial_ratio_le_central (n : ℕ) :
    (n.choose (n / 2) : ℝ) / 2 ^ n ≤
      (Nat.centralBinom (n / 2) : ℝ) / 4 ^ (n / 2) := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
  · subst n
    rw [Nat.mul_div_cancel_left m two_pos, Nat.centralBinom, two_pow_two_mul]
  · subst n
    rw [(by omega : (2 * m + 1) / 2 = m), Nat.centralBinom]
    cases m with
    | zero => norm_num
    | succ m =>
      have hchoose : (2 * (m + 1) + 1).choose (m + 1) ≤
          2 * Nat.centralBinom (m + 1) := by
        rw [Nat.choose_succ_left (2 * (m + 1)) (m + 1) (by grind)]
        simpa [Nat.add_sub_cancel, two_mul] using
          add_le_add (Nat.choose_le_centralBinom m (m + 1))
            (Nat.choose_le_centralBinom (m + 1) (m + 1))
      rw [pow_succ, two_pow_two_mul, mul_comm (4 ^ (m + 1) : ℝ) 2]
      apply le_trans (b := (2 * Nat.centralBinom (m + 1) : ℝ) /
        (2 * 4 ^ (m + 1)))
      · exact (div_le_div_iff_of_pos_right
          (by positivity : (0 : ℝ) < 2 * 4 ^ (m + 1))).mpr <| by
            exact_mod_cast hchoose
      · field_simp
        rfl

/-- Beyond an explicit dimension the middle layer occupies less than any prescribed positive
proportion of the Boolean cube. -/
lemma middleBinomial_lt {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 2 * ⌈1 / δ ^ 2⌉₊ ≤ n) :
    (n.choose (n / 2) : ℝ) < δ * 2 ^ n := by
  have hMn : ⌈1 / δ ^ 2⌉₊ ≤ n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by grind)
  have hsq : 1 / δ ^ 2 < 3 * ((n / 2 : ℕ) : ℝ) + 1 := by
    have hceil : 1 / δ ^ 2 ≤ ((n / 2 : ℕ) : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hMn)
    linarith [(Nat.cast_nonneg (n / 2) : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ))]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp
  apply (middleBinomial_ratio_le_central n).trans_lt
  apply (centralBinom_ratio_le_inv_sqrt (n / 2)).trans_lt
  rw [inv_lt_comm₀ (Real.sqrt_pos.2 (by positivity)) hδ]
  apply Real.lt_sqrt_of_sq_lt
  rwa [inv_pow, ← one_div]

/-- Density Hales--Jewett for the binary alphabet, beyond an explicit dimension. -/
lemma exists_line_of_binary_density {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 2 * ⌈1 / δ ^ 2⌉₊ ≤ n)
    {A : Finset (Fin n → Fin 2)} (hA : δ * (2 : ℝ) ^ n ≤ #A) :
    ∃ l : Combinatorics.Line (Fin 2) (Fin n), ∀ a, l a ∈ A := by
  by_contra hline
  have hB : IsAntichain (· ⊆ ·) (A.image binarySupport : Set (Finset (Fin n))) := by
    intro s hs t ht hst hsub
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    obtain ⟨y, hy, rfl⟩ := mem_image.mp ht
    obtain ⟨l, rfl, rfl⟩ :=
      (binary_line_iff_ssubset x y).2 (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hst⟩)
    exact hline ⟨l, Fin.forall_fin_two.2 ⟨hx, hy⟩⟩
  have hcard : #A ≤ n.choose (n / 2) := by
    rw [← card_image_of_injective A binarySupport_injective]
    simpa using hB.sperner
  exact (not_lt_of_ge (hA.trans <| by exact_mod_cast hcard)) (middleBinomial_lt hδ hn)

/-- The explicit bound for the binary alphabet. -/
lemma isDHJBound_two : IsDHJBound 2 fun δ ↦ 2 * ⌈1 / δ ^ 2⌉₊ :=
  fun δ hδ n hn A hA ↦ exists_line_of_binary_density hδ hn (by exact_mod_cast hA)

/-- The coordinate subspace obtained by fixing every coordinate after the first `m`. -/
def prefixCoordinateSubspace {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (y : Fin (n - m) → α) : Combinatorics.Subspace (Fin m) α (Fin n) where
  idxFun i := ((Subspace.cutEquiv (Nat.add_sub_of_le hmn)).symm i).elim Sum.inr (Sum.inl ∘ y)
  proper e := ⟨Subspace.cutEquiv (Nat.add_sub_of_le hmn) (Sum.inl e), by simp⟩

@[simp]
lemma prefixCoordinateSubspace_apply {α : Type*} {m n : ℕ} (hmn : m ≤ n)
    (y : Fin (n - m) → α) (x : Fin m → α) :
    prefixCoordinateSubspace hmn y x =
      Sum.elim x y ∘ (Subspace.cutEquiv (Nat.add_sub_of_le hmn)).symm := by
  funext i
  cases h : (Subspace.cutEquiv (Nat.add_sub_of_le hmn)).symm i <;>
    simp [prefixCoordinateSubspace, Combinatorics.Subspace.coe_apply, h]

/-- A coordinate subspace of any prescribed smaller dimension has relative density at least the
ambient density. -/
lemma exists_density_preserving_subspace_of_le {k m n : ℕ} (hmn : m ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      (A.dens : ℝ) ≤ (Subspace.relativeDensity V A : ℝ) := by
  let e := (Equiv.sumComm _ _).trans (Subspace.cutEquiv (Nat.add_sub_of_le hmn))
  obtain ⟨y, -, hy⟩ := exists_le_of_le_expect
    (f := fun y ↦ ((fiber (Subspace.splitWords e A) y).dens : ℝ)) univ_nonempty
    (by rw [average_density_fiber, Subspace.dens_splitWords])
  refine ⟨prefixCoordinateSubspace hmn y, hy.trans_eq ?_⟩
  congr 2
  ext x
  simp [e, ← Function.comp_assoc, Sum.elim_swap]

/-- One stage of the schedule: a subspace of dimension `d j` and relative density at least
`δ + j * (γ / 2)` gives a line or a subspace of dimension `d (j + 1)` and relative density at
least `δ + (j + 1) * (γ / 2)`, where `γ` is the increment at density `δ`. -/
lemma density_increment_chain_step {k R n j : ℕ} (hk : 2 ≤ k) {F : ℝ → ℕ}
    (hF : IsDHJBound k F) {δ : ℝ} (hδ : 0 < δ)
    {d : ℕ → ℕ} (hd : ∀ t, t ≤ R → 1 ≤ d t)
    (hstep : ∀ t, t < R → incrementBound k F (d (t + 1)) δ ≤ d t)
    (hj : j < R) {A : Finset (Fin n → Fin (k + 1))}
    {V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n)}
    (hV : δ + (j : ℝ) * (Parameters.γ k (F (δ / 4)) δ / 2) ≤
      (Subspace.relativeDensity V A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ W : Combinatorics.Subspace (Fin (d (j + 1))) (Fin (k + 1)) (Fin n),
        δ + ((j + 1 : ℕ) : ℝ) * (Parameters.γ k (F (δ / 4)) δ / 2) ≤
          (Subspace.relativeDensity W A : ℝ) := by
  have hγ := Parameters.γ_pos hk (F (δ / 4)) hδ
  have hδρ : δ ≤ δ + (j : ℝ) * (Parameters.γ k (F (δ / 4)) δ / 2) :=
    le_add_of_nonneg_right (by positivity)
  obtain ⟨l, hl⟩ | ⟨U, hU⟩ := density_increment hk hF
    (hd (j + 1) (Nat.succ_le_of_lt hj)) hδ hδρ
    (hV.trans (by rw [← dens_pullback]; exact_mod_cast dens_le_one (s := pullback V A)))
    (hstep j hj)
    (A := pullback V A) (by simpa [dens_pullback] using hV)
  · left
    use Subspace.mapLine V l
    intro a
    simpa [Subspace.mapLine_apply, pullback, parameterPreimage] using hl a
  · right
    use Subspace.compose V U
    rw [Subspace.relativeDensity_compose]
    push_cast
    linarith

/-- Iterating the one-step lemma along the schedule either finds a line or reaches the last
scheduled subspace with the accumulated density lower bound. -/
lemma line_or_density_increment_chain {k R n : ℕ} (hk : 2 ≤ k) {F : ℝ → ℕ}
    (hF : IsDHJBound k F) {δ : ℝ} (hδ : 0 < δ)
    {d : ℕ → ℕ} (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R → incrementBound k F (d (j + 1)) δ ≤ d j)
    {A : Finset (Fin n → Fin (k + 1))}
    {V₀ : Combinatorics.Subspace (Fin (d 0)) (Fin (k + 1)) (Fin n)}
    (hV₀ : δ ≤ (Subspace.relativeDensity V₀ A : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin (d R)) (Fin (k + 1)) (Fin n),
        δ + (R : ℝ) * (Parameters.γ k (F (δ / 4)) δ / 2) ≤
          (Subspace.relativeDensity V A : ℝ) := by
  suffices ∀ j, j ≤ R →
      (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
        ∃ V : Combinatorics.Subspace (Fin (d j)) (Fin (k + 1)) (Fin n),
          δ + (j : ℝ) * (Parameters.γ k (F (δ / 4)) δ / 2) ≤
            (Subspace.relativeDensity V A : ℝ) by
    exact this R le_rfl
  intro j hj
  induction j with
  | zero =>
      right
      exact ⟨V₀, by simpa using hV₀⟩
  | succ j ih =>
      obtain hline | ⟨V, hV⟩ := ih (Nat.le_of_succ_le hj)
      · left
        exact hline
      · exact density_increment_chain_step hk hF hδ hd hstep (Nat.lt_of_succ_le hj) hV

/-- Along a schedule of dimensions, a family of density at least `δ` contains a line or
`δ + R * (γ / 2) ≤ 1`, where `γ` is the increment at density `δ`.

Each increment is applied to the pullback of the family to the current subspace, and the subspaces
are composed. A line in a parameter cube gives a line of the family. Otherwise the relative
density rises by at least `γ / 2` per stage, and it is at most one. -/
lemma line_or_iterated_density_le_one {k R n : ℕ} (hk : 2 ≤ k) {F : ℝ → ℕ}
    (hF : IsDHJBound k F) {δ : ℝ} (hδ : 0 < δ) {d : ℕ → ℕ}
    (hd : ∀ j, j ≤ R → 1 ≤ d j)
    (hstep : ∀ j, j < R → incrementBound k F (d (j + 1)) δ ≤ d j)
    (hn : d 0 ≤ n) {A : Finset (Fin n → Fin (k + 1))} (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      δ + (R : ℝ) * (Parameters.γ k (F (δ / 4)) δ / 2) ≤ 1 := by
  obtain ⟨V₀, hV₀⟩ := exists_density_preserving_subspace_of_le hn A
  obtain hline | ⟨V, hV⟩ := line_or_density_increment_chain hk hF hδ hd hstep (hA.trans hV₀)
  · left
    exact hline
  · right
    apply hV.trans
    rw [← dens_pullback]
    exact_mod_cast dens_le_one (s := pullback V A)

/-- Every iterate of `max 1 ∘ f` from `1` is at least one. -/
lemma one_le_iterate_max_one (f : ℕ → ℕ) (t : ℕ) : 1 ≤ (fun d ↦ max 1 (f d))^[t] 1 := by
  cases t with
  | zero => rfl
  | succ t =>
    rw [Function.iterate_succ_apply']
    exact le_max_left _ _

/-- Along the backward schedule `j ↦ (max 1 ∘ f)^[R - j] 1`, each dimension bounds `f` of the
next. -/
lemma le_iterate_max_one_sub (f : ℕ → ℕ) {R j : ℕ} (hj : j < R) :
    f ((fun d ↦ max 1 (f d))^[R - (j + 1)] 1) ≤ (fun d ↦ max 1 (f d))^[R - j] 1 := by
  rw [(by omega : R - j = R - (j + 1) + 1), Function.iterate_succ_apply']
  exact le_max_right _ _

/-- The density Hales--Jewett bound for `k + 1` letters obtained from a bound `F` for `k` letters:
one density increment for each of the `⌈2 / γ⌉ + 1` stages, with the dimensions chosen backwards
from dimension one. -/
noncomputable def stepBound (k : ℕ) (F : ℝ → ℕ) (δ : ℝ) : ℕ :=
  (fun d ↦ max 1 (incrementBound k F d δ))^[⌈2 / Parameters.γ k (F (δ / 4)) δ⌉₊ + 1] 1

/-- A bound for `k` letters gives the bound `stepBound k F` for `k + 1` letters: run the density
increment along the backward schedule of dimensions until the density would exceed one. -/
lemma IsDHJBound.step {k : ℕ} (hk : 2 ≤ k) {F : ℝ → ℕ} (hF : IsDHJBound k F) :
    IsDHJBound (k + 1) (stepBound k F) := by
  intro δ hδ n hn A hA
  let R := ⌈2 / Parameters.γ k (F (δ / 4)) δ⌉₊ + 1
  refine (line_or_iterated_density_le_one hk hF hδ (R := R)
    (d := fun j ↦ (fun d ↦ max 1 (incrementBound k F d δ))^[R - j] 1)
    (fun _ _ ↦ one_le_iterate_max_one _ _)
    (fun _ ↦ le_iterate_max_one_sub (fun d ↦ incrementBound k F d δ)) hn
    (Subspace.density_le_of_card_le (Nat.zero_lt_succ k) (mod_cast hA))).resolve_right ?_
  intro h
  have hγ := Parameters.γ_pos hk (F (δ / 4)) hδ
  have hceil := (div_le_iff₀ hγ).1 (Nat.le_ceil (2 / Parameters.γ k (F (δ / 4)) δ))
  simp only [R, Nat.cast_add_one] at h
  nlinarith

end DensityHalesJewett
