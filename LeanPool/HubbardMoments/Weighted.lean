/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Hubbard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

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

The proofs follow `HubbardMoments.ProjectedHopping` and `HubbardMoments.Hubbard`, with the
complete graph `⊤` in place of `G`: every ordered pair of distinct sites may carry a hop.
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

/-- **Weighted hop sums.** Summing a weight `g` over the hops out of every `n`-subset gives
`(∑_{i ≠ j} g) · n(N - n) C(N, n)/(N(N - 1))`, written without division. -/
theorem sum_hops_top_mul (g : V × V → ℂ) (n : ℕ) :
    (∑ S ∈ powersetCard n (univ : Finset V), ∑ p ∈ hops (⊤ : SimpleGraph V) S, g p) *
        ((Fintype.card V * (Fintype.card V - 1) : ℕ) : ℂ) =
      (∑ p ∈ arcs (⊤ : SimpleGraph V), g p) *
        ((n * (Fintype.card V - n) * (Fintype.card V).choose n : ℕ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hops]
  have hS : ∑ S ∈ powersetCard n (univ : Finset V), ∑ p ∈ hops (⊤ : SimpleGraph V) S, g p =
      (∑ p ∈ arcs (⊤ : SimpleGraph V), g p) * ((Fintype.card V - 2).choose (n - 1) : ℂ) := by
    simp only [hops, sum_filter]
    rw [sum_comm, sum_mul]
    refine sum_congr rfl fun p hp => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul, card_occupied_empty (mem_arcs_top.1 hp) n hn,
      mul_comm]
  rw [hS, mul_assoc, ← Nat.cast_mul, choose_sub_two_mul _ _ hn]

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
  have hsq : ∀ b, H c b * H b c = ((‖H b c‖ : ℝ) : ℂ) ^ 2 := by
    intro b
    rw [← hH.isHermitian.apply c b]
    exact Complex.conj_mul' (H b c)
  have hmem : ∀ p ∈ hops (⊤ : SimpleGraph V) (occ c), p.1 ≠ p.2 ∧ c p.1 ≠ none ∧ c p.2 = none := by
    intro p hp
    simp only [hops, arcs, mem_filter, mem_univ, true_and, mem_occ, not_not,
      SimpleGraph.top_adj] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2⟩
  have himage : (hops (⊤ : SimpleGraph V) (occ c)).image (fun p => move c p.1 p.2) ⊆
      basis V n := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    exact move_mem_basis hc (hmem p hp).2.1 (hmem p hp).2.2
  simp_rw [hsq]
  rw [← sum_subset himage]
  · rw [sum_image]
    · exact sum_congr rfl fun p hp => by
        rw [hH.norm_apply_move c p.1 p.2 (hmem p hp).1 (hmem p hp).2.1 (hmem p hp).2.2]
    · intro p hp q hq hpq
      have hp' := hmem p (mem_coe.mp hp)
      have hq' := hmem q (mem_coe.mp hq)
      obtain ⟨h1, h2⟩ := move_inj c hp'.2.1 hp'.2.2 hq'.2.1 hq'.2.2 hpq
      exact Prod.ext h1 h2
  · intro b _ hb
    have hzero : H b c = 0 := by
      refine hH.apply_eq_zero c b fun i j hij hi hj hbm => hb ?_
      refine mem_image.mpr ⟨(i, j), ?_, hbm.symm⟩
      simp only [hops, arcs, mem_filter, mem_univ, true_and, mem_occ, not_not,
        SimpleGraph.top_adj]
      exact ⟨hij, hi, hj⟩
    simp [hzero]

/-- **The exact second-moment theorem for arbitrary amplitudes.** On the nonempty
no-double-occupancy basis with `n = ∑ n_s` particles, `N ≥ 2` sites,
`μ₂ = n(N - n)/(N(N - 1)) · ∑_{i ≠ j} w(i, j)²`. -/
theorem second_moment_weighted (hH : IsWeightedProjectedHopping w H) (n : σ → ℕ)
    (hB : (basis V n).Nonempty) (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) H =
      (∑ s, n s : ℕ) * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
          ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) *
        ∑ i, ∑ j ∈ univ.erase i, ((w i j : ℝ) : ℂ) ^ 2 := by
  rw [secondMoment, ← sum_arcs_top (fun i j => ((w i j : ℝ) : ℂ) ^ 2)]
  obtain ⟨c₀, hc₀⟩ := hB
  have hmN : ∑ s, n s ≤ Fintype.card V := by
    rw [← card_occ hc₀]
    exact card_le_univ _
  have htr : ∑ c ∈ basis V n, H c c = 0 := sum_eq_zero fun c _ => hH.apply_self_eq_zero c
  set f : Finset V → ℂ := fun S => ∑ p ∈ hops (⊤ : SimpleGraph V) S, ((w p.1 p.2 : ℝ) : ℂ) ^ 2
  have hdiag : ∑ c ∈ basis V n, ∑ b ∈ basis V n, H c b * H b c = ∑ c ∈ basis V n, f (occ c) :=
    sum_congr rfl fun c hc => sum_mul_apply_self_weighted hH hc
  have hspin := sum_basis_comp_occ n f
  have hcount := sum_hops_top_mul (fun p => ((w p.1 p.2 : ℝ) : ℂ) ^ 2) (∑ s, n s)
  have hB0 : ((basis V n).card : ℂ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr ⟨c₀, hc₀⟩).ne'
  rw [htr, hdiag, zero_div, zero_pow two_ne_zero, sub_zero]
  set W := ∑ p ∈ arcs (⊤ : SimpleGraph V), ((w p.1 p.2 : ℝ) : ℂ) ^ 2
  generalize ∑ s, n s = m at hspin hcount hmN ⊢
  generalize Fintype.card V = N at hspin hcount hmN hN ⊢
  push_cast [Nat.cast_sub hmN, Nat.cast_sub (by omega : 1 ≤ N)] at hcount
  have hC0 : (N.choose m : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmN).ne'
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hN1 : (N : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (by omega : N ≠ 1)
  set A := ∑ c ∈ basis V n, f (occ c)
  have hkey : (N.choose m : ℂ) *
      (A * (N * (N - 1)) - (basis V n).card * (W * (m * (N - m)))) = 0 := by
    linear_combination ((N : ℂ) * (N - 1)) * hspin + ((basis V n).card : ℂ) * hcount
  have hkey' : A * (N * (N - 1)) = (basis V n).card * (W * (m * (N - m))) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left hC0)
  field_simp
  linear_combination hkey'

/-! ### The fermionic hopping term with arbitrary amplitudes -/

variable (tt : V → V → ℂ) (ord : V × σ ↪ ℕ)

/-- The matrix elements of `H_t`. -/
theorem hubbardHoppingWeighted_apply (S' S : FockState V σ) :
    hubbardHoppingWeighted tt ord S' S = ∑ p ∈ arcs (⊤ : SimpleGraph V), ∑ s,
      (-tt p.2 p.1) *
        if (p.1, s) ∈ S ∧ (p.2, s) ∉ S.erase (p.1, s) ∧ S' = insert (p.2, s) (S.erase (p.1, s))
        then (-1) ^ (countBelow ord S (p.1, s) + countBelow ord (S.erase (p.1, s)) (p.2, s))
        else 0 := by
  simp only [hubbardHoppingWeighted, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    create_mul_annihilate_apply]

/-- **`H_t` is Hermitian** when `t_ji = conj(t_ij)`. -/
theorem hubbardHoppingWeighted_isHermitian {tt : V → V → ℂ} (htt : ∀ i j, tt j i = star (tt i j)) :
    (hubbardHoppingWeighted tt ord).IsHermitian := by
  have hcr : ∀ o, (create ord o)ᴴ = annihilate ord o := fun o => by
    rw [← annihilate_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have hst : ∀ x y : V, star (-tt y x) = -tt x y := fun x y => by
    rw [star_neg, ← htt]
  unfold Matrix.IsHermitian hubbardHoppingWeighted
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    hcr, annihilate_conjTranspose, hst]
  refine sum_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · intro p hp
    simpa [mem_arcs_top, eq_comm] using hp
  · intro p hp
    simpa [mem_arcs_top, eq_comm] using hp

/-- **`H∞` with arbitrary amplitudes is a weighted projected hopping operator**, with
`w i j = |t_ji|`, for any ordering of the orbitals. -/
theorem projectedHubbardWeighted_isWeightedProjectedHopping {tt : V → V → ℂ}
    (htt : ∀ i j, tt j i = star (tt i j)) :
    IsWeightedProjectedHopping (fun i j => ‖tt j i‖) (projectedHubbardWeighted tt ord) := by
  refine ⟨?_, ?_, ?_⟩
  · ext c b
    exact (hubbardHoppingWeighted_isHermitian ord htt).apply (configState c) (configState b)
  · intro c i j hij hci hcj
    obtain ⟨s₀, hs₀⟩ := Option.ne_none_iff_exists'.1 hci
    have hmem : (i, s₀) ∈ configState c := mem_configState.2 hs₀
    have hnot : (j, s₀) ∉ configState c := by simp [mem_configState, hcj]
    simp only [projectedHubbardWeighted, configState_move hs₀ hcj hij,
      hubbardHoppingWeighted_apply]
    rw [sum_eq_single (i, j), sum_eq_single s₀]
    · have hnot' : (j, s₀) ∉ (configState c).erase (i, s₀) := fun h => hnot (mem_of_mem_erase h)
      simp only [hmem, hnot', not_false_eq_true, and_self, ↓reduceIte, norm_mul, norm_neg,
        norm_pow]
      simp
    · intro s _ hs
      rw [ite_eq_right_iff.2, mul_zero]
      rintro ⟨h₁, h₂, h₃⟩
      exfalso
      exact hs (Prod.mk.inj (hop_unique h₁ h₂ (by simp [hij]) hmem h₃.symm).1).2
    · intro h
      exact absurd (mem_univ s₀) h
    · intro p hp hpij
      refine sum_eq_zero fun s _ => ?_
      have hne' : p.1 ≠ p.2 := mem_arcs_top.1 hp
      rw [ite_eq_right_iff.2, mul_zero]
      rintro ⟨h₁, h₂, h₃⟩
      have hne : (p.1, s) ≠ (p.2, s) := fun h => hne' (congrArg Prod.fst h)
      obtain ⟨e₁, e₂⟩ := hop_unique h₁ h₂ hne hmem h₃.symm
      have e₁' : p.1 = i := congrArg Prod.fst e₁
      have e₂' : p.2 = j := congrArg Prod.fst e₂
      exact absurd (Prod.ext e₁' e₂') hpij
    · intro h
      exact absurd (mem_arcs_top.2 hij) h
  · intro c b hb
    simp only [projectedHubbardWeighted, hubbardHoppingWeighted_apply]
    refine sum_eq_zero fun p hp => sum_eq_zero fun s _ => ?_
    have hne : p.1 ≠ p.2 := mem_arcs_top.1 hp
    rw [ite_eq_right_iff.2, mul_zero]
    rintro ⟨h₁, h₂, h₃⟩
    obtain ⟨hci, hcj, hmove⟩ := config_eq_move_of_replace hne h₁ h₂ h₃
    exact (hb p.1 p.2 hne hci hcj hmove).elim

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
