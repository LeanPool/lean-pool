/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Hubbard

/-!
# The second-moment theorem for arbitrary hopping amplitudes

The paper states the second-moment theorem for a general Hermitian hopping matrix,
`μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} |t_ij|²` (abstract, §5.2). Here:

* `second_moment_weighted`: for every operator with the properties of
  `IsWeightedProjectedHopping` (Hermitian; one hop `i → j` has modulus `w i j`; nothing else),
  `μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} w(i, j)²`;
* `hubbardHoppingWeighted_isHermitian`,
  `projectedHubbardWeighted_isWeightedProjectedHopping`: the hopping term
  `H_t = -∑_{i ≠ j, s} t_ij c†_{is} c_{js}` built from fermion operators, with
  `t_ji = conj(t_ij)`, is Hermitian, and `H∞ = P₀ H_t P₀` has those properties with
  `w i j = |t_ji|`;
* `secondMoment_projectedHubbardWeighted`: hence the paper's formula for `H∞` itself.

The hopping-operator proofs specialize the graph-amplitude results to the complete graph.
-/

@[expose] public section

namespace HubbardMoments

open Finset Complex
open scoped Matrix

variable {V σ : Type*} [Fintype V] [DecidableEq V]

/-! ### Weighted hop sums over subsets -/

theorem mem_arcs_top {p : V × V} : p ∈ arcs (⊤ : SimpleGraph V) ↔ p.1 ≠ p.2 := by
  simp [arcs]

/-- A sum over ordered pairs of distinct sites. -/
theorem sum_arcs_top (g : V → V → ℂ) :
    ∑ p ∈ arcs (⊤ : SimpleGraph V), g p.1 p.2 = ∑ i, ∑ j ∈ univ.erase i, g i j := by
  rw [arcs, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_filter]
  simp only [SimpleGraph.top_adj]
  rw [filter_ne]

/-- The same sum with the two sites exchanged. -/
theorem sum_arcs_top_swap (g : V → V → ℂ) :
    ∑ p ∈ arcs (⊤ : SimpleGraph V), g p.2 p.1 = ∑ p ∈ arcs (⊤ : SimpleGraph V), g p.1 p.2 := by
  refine sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · intro p hp
    simpa [mem_arcs_top, eq_comm] using hp
  · intro p hp
    simpa [mem_arcs_top, eq_comm] using hp

/-! ### The weighted second-moment theorem -/

variable [Fintype σ] [DecidableEq σ] {w : V → V → ℝ} {H : Matrix (Config V σ) (Config V σ) ℂ}

omit [Fintype V] [Fintype σ] [DecidableEq σ] in
theorem IsWeightedProjectedHopping.apply_self_eq_zero (hH : IsWeightedProjectedHopping w H)
    (c : Config V σ) : H c c = 0 :=
  hH.apply_eq_zero c c fun _ _ _ hi hj h => move_ne_self c hi hj h.symm

/-- **The diagonal of `H²`** is the sum of `w(i, j)²` over the hops `i → j` out of `c`. -/
theorem sum_mul_apply_self_weighted (hH : IsWeightedProjectedHopping w H) {n : σ → ℕ}
    {c : Config V σ} (hc : c ∈ basis V n) :
    ∑ b ∈ basis V n, H c b * H b c =
      ∑ p ∈ hops (⊤ : SimpleGraph V) (occ c), ((w p.1 p.2 : ℝ) : ℂ) ^ 2 := by
  exact sum_mul_apply_self_eq_sum_hops (G := ⊤) hc hH.isHermitian
    (hH.norm_apply_move c) (hH.apply_eq_zero c)

/-- **The exact second-moment theorem for arbitrary amplitudes.** On the nonempty
no-double-occupancy basis with `n = ∑ n_s` particles, `N ≥ 2` sites,
`μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} w(i, j)²`. -/
theorem second_moment_weighted (hH : IsWeightedProjectedHopping w H) (n : σ → ℕ)
    (hB : (basis V n).Nonempty) (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) H =
      (∑ s, n s : ℕ) * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
          ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) *
        ∑ i, ∑ j ∈ univ.erase i, ((w i j : ℝ) : ℂ) ^ 2 := by
  rw [← sum_arcs_top (fun i j => (w i j : ℂ) ^ 2)]
  exact secondMoment_eq_sum_arcs (G := ⊤) n hB hN hH.isHermitian
    hH.norm_apply_move hH.apply_eq_zero

/-! ### The fermionic hopping term with arbitrary amplitudes -/

variable (tt : V → V → ℂ) (ord : V × σ ↪ ℕ)

/-- The matrix elements of `H_t`. -/
theorem hubbardHoppingWeighted_apply (S' S : FockState V σ) :
    hubbardHoppingWeighted tt ord S' S = ∑ p ∈ arcs (⊤ : SimpleGraph V), ∑ s,
      (-tt p.2 p.1) *
        if (p.1, s) ∈ S ∧ (p.2, s) ∉ S.erase (p.1, s) ∧ S' = insert (p.2, s) (S.erase (p.1, s))
        then (-1) ^ (countBelow ord S (p.1, s) + countBelow ord (S.erase (p.1, s)) (p.2, s))
        else 0 :=
  fermionHopping_apply ⊤ _ ord S' S

/-- **`H_t` is Hermitian** when `t_ji = conj(t_ij)`. -/
theorem hubbardHoppingWeighted_isHermitian {tt : V → V → ℂ} (htt : ∀ i j, tt j i = star (tt i j)) :
    (hubbardHoppingWeighted tt ord).IsHermitian :=
  fermionHopping_isHermitian ⊤ (fun i j => -tt j i) ord
    (fun i j => by rw [star_neg, ← htt])

/-- **`H∞` with arbitrary amplitudes is a weighted projected hopping operator**, with
`w i j = |t_ji|`, for any ordering of the orbitals. -/
theorem projectedHubbardWeighted_isWeightedProjectedHopping {tt : V → V → ℂ}
    (htt : ∀ i j, tt j i = star (tt i j)) :
    IsWeightedProjectedHopping (fun i j => ‖tt j i‖) (projectedHubbardWeighted tt ord) := by
  have hstar (i j : V) : star (-tt j i) = -tt i j := by rw [star_neg, ← htt]
  refine ⟨projectedFermionHopping_isHermitian ⊤ _ ord hstar, ?_,
    projectedFermionHopping_apply_eq_zero ⊤ _ ord⟩
  intro c i j hij hci hcj
  simpa [projectedHubbardWeighted] using
    norm_projectedFermionHopping_move ⊤ (fun i j => -tt j i) ord hij hci hcj

/-- **The paper's second-moment formula for `H∞` itself** (abstract, §5.2): with
`H_t = -∑_{i ≠ j, s} t_ij c†_{is} c_{js}`, `t_ji = conj(t_ij)`,
`μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} |t_ij|²`. -/
theorem secondMoment_projectedHubbardWeighted {tt : V → V → ℂ}
    (htt : ∀ i j, tt j i = star (tt i j)) (n : σ → ℕ) (hB : (basis V n).Nonempty)
    (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) (projectedHubbardWeighted tt ord) =
      (∑ s, n s : ℕ) * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
          ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) *
        ∑ i, ∑ j ∈ univ.erase i, ((‖tt i j‖ : ℝ) : ℂ) ^ 2 := by
  rw [second_moment_weighted (projectedHubbardWeighted_isWeightedProjectedHopping ord htt) n hB hN,
    ← sum_arcs_top (fun i j => ((‖tt j i‖ : ℝ) : ℂ) ^ 2),
    ← sum_arcs_top (fun i j => ((‖tt i j‖ : ℝ) : ℂ) ^ 2),
    sum_arcs_top_swap (fun i j => ((‖tt i j‖ : ℝ) : ℂ) ^ 2)]

end HubbardMoments
