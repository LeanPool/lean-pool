/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# The rank count behind interpolation determinants

* `row_mem_span`: for symmetric `m`-linear forms `Φ_λ` on `ℂ^n`, every row `(Φ_λ u)_λ` lies in the
  span of the rows `(Φ_λ(e_{j₁}, …, e_{j_m}))_λ` with `j` monotone.
* `card_monotone_le`: there are at most `(m+1)^{n-1}` monotone maps `Fin m → Fin n` (`n ≥ 1`).
* `card_fiber_le`: linearly independent rows with key `k`, all in the span of `β` vectors, number
  at most `card β`.
* `mul_sub_le_sum`: if each key value `k` occurs at most `(k+1)^{n-1}` times among `N` keys, then
  `M (N − Mⁿ) ≤ Σ keys` for every `M`.

Together: a non-zero determinant of derivative rows of orders `m_ν` forces
`Σ m_ν ≥ M (N − Mⁿ)`. This is the `Θ_n(N) ≫ N^{1+1/n}` count of Laurent's method, with
`n = dim V`.
-/

@[expose] public section

namespace LeanPool

open Finset Module

namespace StrongSix.Thm1

variable {n N m : ℕ}

/-- The standard basis vector `e_i` of `ℂ^n`. -/
noncomputable abbrev e (i : Fin n) : Fin n → ℂ := Pi.single i 1

theorem sum_smul_e (v : Fin n → ℂ) : ∑ i, v i • e i = v := by
  funext j
  simp [e, Finset.sum_apply, Pi.single_apply]

/-- **Rows of symmetric forms lie in the span of the monotone basis rows.** -/
theorem row_mem_span (Φ : Fin N → ContinuousMultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) ℂ)
    (hΦ : ∀ l (v : Fin m → Fin n → ℂ) (σ : Equiv.Perm (Fin m)), Φ l (v ∘ σ) = Φ l v)
    (u : Fin m → Fin n → ℂ) :
    (fun l => Φ l u) ∈ Submodule.span ℂ
      (Set.range fun j : {j : Fin m → Fin n // Monotone j} => fun l => Φ l (fun a => e (j.1 a)))
        := by
  classical
  have hexp : (fun l => Φ l u) =
      ∑ r : Fin m → Fin n, (∏ a, u a (r a)) • fun l => Φ l (fun a => e (r a)) := by
    funext l
    have hu : u = fun a => ∑ i, u a i • e i := funext fun a => (sum_smul_e (u a)).symm
    conv_lhs => rw [hu]
    rw [(Φ l).map_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [(Φ l).map_smul_univ]
    rfl
  rw [hexp]
  refine Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨⟨r ∘ Tuple.sort r, Tuple.monotone_sort r⟩, ?_⟩
  funext l
  exact hΦ l (fun a => e (r a)) (Tuple.sort r)

/-- `C(m + r, r) ≤ (m+1)^r`. -/
theorem choose_le_pow (m r : ℕ) : (m + r).choose r ≤ (m + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h := Nat.add_one_mul_choose_eq (m + r) r
    -- `(m + r + 1) * C(m+r, r) = C(m+r+1, r+1) * (r+1)`
    have hle : (m + (r + 1)).choose (r + 1) * (r + 1) ≤ (m + 1) ^ (r + 1) * (r + 1) := by
      rw [show m + (r + 1) = m + r + 1 by ring, ← h]
      calc (m + r + 1) * (m + r).choose r ≤ ((m + 1) * (r + 1)) * (m + 1) ^ r := by
            apply Nat.mul_le_mul _ ih
            nlinarith
        _ = (m + 1) ^ (r + 1) * (r + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hle (Nat.succ_pos r)

/-- At most `(m+1)^{n-1}` monotone maps `Fin m → Fin n`. -/
theorem card_monotone_le (hn : 1 ≤ n) :
    Fintype.card {j : Fin m → Fin n // Monotone j} ≤ (m + 1) ^ (n - 1) := by
  classical
  let f : {j : Fin m → Fin n // Monotone j} → Sym (Fin n) m :=
    fun j => ⟨(List.ofFn j.1 : Multiset (Fin n)), by simp⟩
  have hf : Function.Injective f := by
    rintro ⟨j, hj⟩ ⟨j', hj'⟩ h
    have hp : List.Perm (List.ofFn j) (List.ofFn j') := by
      have := congrArg Subtype.val h
      exact Multiset.coe_eq_coe.mp this
    have := hp.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr hj) (List.sortedLE_ofFn_iff.mpr hj')
    exact Subtype.ext (List.ofFn_injective this)
  calc Fintype.card {j : Fin m → Fin n // Monotone j} ≤ Fintype.card (Sym (Fin n) m) :=
        Fintype.card_le_of_injective f hf
    _ = (n + m - 1).choose m := by rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    _ = (m + (n - 1)).choose (n - 1) := by
        rw [show n + m - 1 = m + (n - 1) by omega, Nat.choose_symm_add]
    _ ≤ (m + 1) ^ (n - 1) := choose_le_pow m (n - 1)

/-- **Fibre bound.** Linearly independent rows with a given key, all in the span of `card β`
vectors, number at most `card β`. -/
theorem card_fiber_le {ι : Type*} [Fintype ι] {R : ι → Fin N → ℂ}
    (hR : LinearIndependent ℂ R) (key : ι → ℕ) (k : ℕ) {β : Type*} [Fintype β]
    (b : β → Fin N → ℂ) (hb : ∀ i, key i = k → R i ∈ Submodule.span ℂ (Set.range b)) :
    (univ.filter fun i => key i = k).card ≤ Fintype.card β := by
  classical
  let S := Submodule.span ℂ (Set.range b)
  let R' : {i // key i = k} → S := fun i => ⟨R i, hb i i.2⟩
  have hR' : LinearIndependent ℂ R' := by
    apply LinearIndependent.of_comp S.subtype
    exact hR.comp Subtype.val Subtype.val_injective
  calc (univ.filter fun i => key i = k).card = Fintype.card {i // key i = k} :=
        (Fintype.card_subtype _).symm
    _ ≤ finrank ℂ S := hR'.fintype_card_le_finrank
    _ ≤ Fintype.card β := finrank_range_le_card b

/-- **Counting.** If each value `k` occurs at most `(k+1)^{n-1}` times among the keys, then
`M (N − Mⁿ) ≤ Σ keys`. -/
theorem mul_sub_le_sum (hn : 1 ≤ n) (key : Fin N → ℕ)
    (h : ∀ k, (univ.filter fun ν => key ν = k).card ≤ (k + 1) ^ (n - 1)) (M : ℕ) :
    M * (N - M ^ n) ≤ ∑ ν, key ν := by
  classical
  set A := univ.filter fun ν => key ν < M with hA
  have hcardA : A.card ≤ M ^ n := by
    have h1 : A.card = ∑ k ∈ range M, (A.filter fun ν => key ν = k).card :=
      card_eq_sum_card_fiberwise (fun ν hν => by simpa [hA] using hν)
    have h2 : ∀ k ∈ range M, (A.filter fun ν => key ν = k).card ≤ M ^ (n - 1) := by
      intro k hk
      calc (A.filter fun ν => key ν = k).card ≤ (univ.filter fun ν => key ν = k).card :=
            card_le_card (filter_subset_filter _ (subset_univ _))
        _ ≤ (k + 1) ^ (n - 1) := h k
        _ ≤ M ^ (n - 1) := Nat.pow_le_pow_left (by simpa using hk) _
    calc A.card ≤ ∑ _k ∈ range M, M ^ (n - 1) := h1 ▸ sum_le_sum h2
      _ = M ^ n := by
        rw [sum_const, card_range, smul_eq_mul, ← pow_succ']
        congr 1; omega
  have hB : N - M ^ n ≤ (univ.filter fun ν => ¬ key ν < M).card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) (fun ν => key ν < M)
    rw [card_univ, Fintype.card_fin] at this
    have h2 : N - M ^ n ≤ N - A.card := Nat.sub_le_sub_left hcardA N
    rw [hA] at h2
    omega
  calc M * (N - M ^ n) ≤ M * (univ.filter fun ν => ¬ key ν < M).card := Nat.mul_le_mul_left _ hB
    _ = ∑ ν ∈ univ.filter (fun ν => ¬ key ν < M), M := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ ν ∈ univ.filter (fun ν => ¬ key ν < M), key ν :=
        sum_le_sum fun ν hν => by simp at hν; omega
    _ ≤ ∑ ν, key ν := sum_le_sum_of_subset (subset_univ _)

end StrongSix.Thm1

end LeanPool
