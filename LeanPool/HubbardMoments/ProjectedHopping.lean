/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.SecondMoment
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The exact second-moment theorem

For a projected hopping operator `H` (`HubbardMoments.IsProjectedHopping`) on a finite
simple graph `G` with `N ≥ 2` vertices and `|E|` edges, and the no-double-occupancy basis
`B` with `n_s` particles of spin `s` and `n = ∑ n_s` particles in all:

* `apply_self_eq_zero`: every diagonal element of `H` vanishes, so `Tr_B H = 0`;
* `sum_mul_apply_self`: the diagonal element of `H²` at `c ∈ B` is `t² M(c)`, where `M(c)`
  is the number of hops out of `c`;
* `sum_basis_comp_occ`: averaging a function of the occupied sites over `B` is the same as
  averaging it over the `n`-subsets of the sites; spin plays no role;
* `second_moment`: the second spectral moment of `H` on `B` is
  `μ₂ = Tr_B(H²)/|B| - (Tr_B H/|B|)² = t² · 2|E| · n(N - n)/(N(N - 1))`.

This is the paper's exact second-moment theorem (§5.2). It holds on every finite simple
graph and does not depend on the spin composition `(n_s)`, only on `n`.

The theorem is proved for every operator with the three properties of `IsProjectedHopping`.
`HubbardMoments.Hubbard` shows that `H∞ = P₀ H_t P₀`, built from fermion operators, has
them (`projectedHubbard_isProjectedHopping`, `secondMoment_projectedHubbard`).
-/

public section

namespace HubbardMoments

open Finset

variable {V σ : Type*}

/-! ### Moving one particle -/

section Move

variable [DecidableEq V] (c : Config V σ) {i j : V}

theorem move_apply_left (hij : i ≠ j) : move c i j i = none := by
  simp [move, Function.update_of_ne hij]

theorem move_apply_right : move c i j j = c i := by
  simp [move]

theorem move_apply_of_ne {v : V} (hvi : v ≠ i) (hvj : v ≠ j) : move c i j v = c v := by
  simp [move, Function.update_of_ne hvi, Function.update_of_ne hvj]

/-- Moving a particle to an empty site is relabelling the sites by a transposition. -/
theorem move_eq_comp_swap (hij : i ≠ j) (hj : c j = none) :
    move c i j = c ∘ Equiv.swap i j := by
  funext v
  by_cases hvi : v = i
  · subst hvi
    simp [move_apply_left c hij, hj]
  · by_cases hvj : v = j
    · subst hvj
      simp [move_apply_right]
    · simp [move_apply_of_ne c hvi hvj, Equiv.swap_apply_of_ne_of_ne hvi hvj]

/-- A hop changes the configuration. -/
theorem move_ne_self (hi : c i ≠ none) (hj : c j = none) : move c i j ≠ c := by
  intro h
  have := congrFun h j
  rw [move_apply_right] at this
  exact hi (this.trans hj)

/-- Different hops out of the same configuration give different configurations. -/
theorem move_inj {i' j' : V} (hi : c i ≠ none) (hj : c j = none) (hi' : c i' ≠ none)
    (hj' : c j' = none) (h : move c i j = move c i' j') : i = i' ∧ j = j' := by
  have hij : i ≠ j := fun e => hi (e ▸ hj)
  have hij' : i' ≠ j' := fun e => hi' (e ▸ hj')
  have hjj : j = j' := by
    by_contra hne
    have h0 : move c i' j' j = none := by
      by_cases hji' : j = i'
      · subst hji'
        exact move_apply_left c hij'
      · exact (move_apply_of_ne c hji' hne).trans hj
    rw [← h, move_apply_right] at h0
    exact hi h0
  subst hjj
  refine ⟨?_, rfl⟩
  by_contra hne
  have h0 : move c i j i = none := move_apply_left c hij
  rw [h, move_apply_of_ne c hne hij] at h0
  exact hi h0

/-- Hopping back undoes a hop. -/
theorem move_move (hij : i ≠ j) (hj : c j = none) : move (move c i j) j i = c := by
  funext v
  by_cases hvi : v = i
  · rw [hvi, move_apply_right, move_apply_right]
  · by_cases hvj : v = j
    · rw [hvj, move_apply_left _ hij.symm, hj]
    · rw [move_apply_of_ne _ hvj hvi, move_apply_of_ne _ hvi hvj]

end Move

/-! ### Relabelling the sites -/

section Relabel

variable [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]

omit [DecidableEq V] [Fintype σ] in
theorem card_filter_comp_perm (c : Config V σ) (π : Equiv.Perm V) (s : σ) :
    (univ.filter (fun v => (c ∘ π) v = some s)).card =
      (univ.filter (fun v => c v = some s)).card :=
  card_equiv π (by simp)

/-- Relabelling the sites preserves the spin composition. -/
theorem comp_perm_mem_basis {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n)
    (π : Equiv.Perm V) : c ∘ π ∈ basis V n := by
  simp only [basis, mem_filter, mem_univ, true_and] at hc ⊢
  intro s
  rw [card_filter_comp_perm c π s, hc s]

/-- A hop preserves the spin composition. -/
theorem move_mem_basis {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n) {i j : V}
    (hi : c i ≠ none) (hj : c j = none) : move c i j ∈ basis V n := by
  have hij : i ≠ j := fun e => hi (e ▸ hj)
  rw [move_eq_comp_swap c hij hj]
  exact comp_perm_mem_basis hc _

omit [DecidableEq V] [Fintype σ] [DecidableEq σ] in
theorem occ_comp_symm (c : Config V σ) (π : Equiv.Perm V) :
    occ (c ∘ π.symm) = (occ c).map π.toEmbedding := by
  ext v
  simp [occ, mem_map_equiv]

/-- Two `n`-subsets of the sites carry the same number of configurations of the basis. -/
theorem card_fiber_eq {n : σ → ℕ} {S S' : Finset V} (h : S.card = S'.card) :
    ((basis V n).filter (fun c => occ c = S)).card =
      ((basis V n).filter (fun c => occ c = S')).card := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_map_finset_eq S S' h
  refine card_nbij' (fun c => c ∘ π.symm) (fun c => c ∘ π) ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_coe, mem_filter] at hc ⊢
    exact ⟨comp_perm_mem_basis hc.1 _, by rw [occ_comp_symm, hc.2, hπ]⟩
  · intro c hc
    simp only [mem_coe, mem_filter] at hc ⊢
    refine ⟨comp_perm_mem_basis hc.1 _, ?_⟩
    have h1 : (occ (c ∘ π)).map π.toEmbedding = occ c := by
      rw [← occ_comp_symm]
      congr 1
      funext v
      simp
    rw [hc.2, ← hπ] at h1
    exact map_injective _ h1
  · intro c _
    funext v
    simp
  · intro c _
    funext v
    simp

/-- The number of occupied sites is the total particle number. -/
theorem card_occ {n : σ → ℕ} {c : Config V σ} (hc : c ∈ basis V n) :
    (occ c).card = ∑ s, n s := by
  have hocc : occ c = univ.biUnion (fun s => univ.filter (fun v => c v = some s)) := by
    ext v
    simp [occ, Option.ne_none_iff_exists']
  rw [hocc, card_biUnion]
  · simp only [basis, mem_filter, mem_univ, true_and] at hc
    exact sum_congr rfl fun s _ => hc s
  · intro s _ s' _ hss'
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro v _ h1 h2
    rw [h1] at h2
    exact hss' (Option.some_injective _ h2)

/-- **Spin plays no role.** For any function `f` of the occupied sites,
`(∑_{c ∈ B} f(occ c)) · C(N, n) = |B| · ∑_{S ∈ P_n} f(S)`, where `n = ∑ n_s`. -/
theorem sum_basis_comp_occ (n : σ → ℕ) (f : Finset V → ℂ) :
    (∑ c ∈ basis V n, f (occ c)) * (Fintype.card V).choose (∑ s, n s) =
      ((basis V n).card : ℂ) * ∑ S ∈ powersetCard (∑ s, n s) (univ : Finset V), f S := by
  have hmaps : ∀ c ∈ basis V n, occ c ∈ powersetCard (∑ s, n s) (univ : Finset V) := by
    intro c hc
    rw [mem_powersetCard]
    exact ⟨subset_univ _, card_occ hc⟩
  have hmaps' : ((basis V n : Finset (Config V σ)) : Set (Config V σ)).MapsTo occ
      (powersetCard (∑ s, n s) (univ : Finset V)) := by
    intro c hc
    exact hmaps c (mem_coe.mp hc)
  rw [← sum_fiberwise_of_maps_to hmaps (fun c => f (occ c)),
    card_eq_sum_card_fiberwise hmaps']
  rcases (powersetCard (∑ s, n s) (univ : Finset V)).eq_empty_or_nonempty with he | ⟨S₀, hS₀⟩
  · simp [he]
  · have hk : ∀ S ∈ powersetCard (∑ s, n s) (univ : Finset V),
        ((basis V n).filter (fun c => occ c = S)).card =
          ((basis V n).filter (fun c => occ c = S₀)).card := fun S hS =>
      card_fiber_eq (by rw [(mem_powersetCard.mp hS).2, (mem_powersetCard.mp hS₀).2])
    have hinner : ∀ S ∈ powersetCard (∑ s, n s) (univ : Finset V),
        ∑ c ∈ (basis V n).filter (fun c => occ c = S), f (occ c) =
          ((basis V n).filter (fun c => occ c = S₀)).card * f S := by
      intro S hS
      rw [sum_congr rfl (fun c hc => by rw [(mem_filter.mp hc).2]), sum_const, hk S hS,
        nsmul_eq_mul]
    rw [sum_congr rfl hinner, sum_congr rfl hk, sum_const, card_powersetCard, card_univ,
      ← mul_sum]
    simp only [smul_eq_mul, Nat.cast_mul]
    ring

end Relabel

/-! ### The moments of a projected hopping operator -/

section Moments

variable [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]
  {G : SimpleGraph V} [DecidableRel G.Adj] {t : ℝ}
  {H : Matrix (Config V σ) (Config V σ) ℂ}

omit [Fintype V] [Fintype σ] [DecidableEq σ] [DecidableRel G.Adj] in
/-- Every diagonal element of a projected hopping operator vanishes. -/
theorem apply_self_eq_zero {w : V → V → ℝ} (hH : IsGraphProjectedHopping G w H)
    (c : Config V σ) : H c c = 0 :=
  hH.apply_eq_zero c c fun ⟨_, _, _, hi, hj, h⟩ => move_ne_self c hi hj h.symm

omit [DecidableEq V] [Fintype σ] [DecidableEq σ] in
theorem mem_occ {c : Config V σ} {v : V} : v ∈ occ c ↔ c v ≠ none := by
  simp [occ]

/-- For a Hermitian hopping matrix supported on graph moves out of a configuration, the diagonal
of its square on the spin basis is the sum of squared moduli of those moves. -/
theorem sum_mul_apply_self_eq_sum_hops {w : V → V → ℝ} {n : σ → ℕ} {c : Config V σ}
    (hc : c ∈ basis V n) (hH : IsGraphProjectedHopping G w H) :
    ∑ b ∈ basis V n, H c b * H b c =
      ∑ p ∈ hops G (occ c), (w p.1 p.2 : ℂ) ^ 2 := by
  have hsq : ∀ b, H c b * H b c = ((‖H b c‖ : ℝ) : ℂ) ^ 2 := by
    intro b
    rw [← hH.isHermitian.apply c b]
    change starRingEnd ℂ (H b c) * H b c = _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hmem (p : V × V) :
      p ∈ hops G (occ c) ↔ G.Adj p.1 p.2 ∧ c p.1 ≠ none ∧ c p.2 = none := by
    rw [mem_hops, mem_occ, mem_occ, not_not]
  have himage : (hops G (occ c)).image (fun p => move c p.1 p.2) ⊆ basis V n := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hb
    exact move_mem_basis hc ((hmem p).mp hp).2.1 ((hmem p).mp hp).2.2
  simp_rw [hsq]
  rw [← sum_subset himage]
  · rw [sum_image]
    · refine sum_congr rfl fun p hp => ?_
      obtain ⟨hadj, hoccupied, hempty⟩ := (hmem p).mp hp
      rw [hH.norm_apply_move c p.1 p.2 hadj hoccupied hempty]
    · intro p hp q hq hpq
      have hp' := (hmem p).mp (mem_coe.mp hp)
      have hq' := (hmem q).mp (mem_coe.mp hq)
      obtain ⟨h1, h2⟩ := move_inj c hp'.2.1 hp'.2.2 hq'.2.1 hq'.2.2 hpq
      exact Prod.ext h1 h2
  · intro b _ hb
    have hentry : H b c = 0 := by
      refine hH.apply_eq_zero c b fun ⟨i, j, hij, hi, hj, hbm⟩ => hb ?_
      exact mem_image.mpr ⟨(i, j), (hmem _).mpr ⟨hij, hi, hj⟩, hbm.symm⟩
    simp [hentry]

/-- **The diagonal of `H²`.** At a configuration `c` of the basis, the diagonal element of
`H²` (computed in the basis) is `t² M(c)`, where `M(c)` is the number of hops out of `c`. -/
theorem sum_mul_apply_self (hH : IsProjectedHopping G t H) {n : σ → ℕ} {c : Config V σ}
    (hc : c ∈ basis V n) :
    ∑ b ∈ basis V n, H c b * H b c = (t : ℂ) ^ 2 * (hops G (occ c)).card := by
  rw [sum_mul_apply_self_eq_sum_hops hc hH, sum_const, nsmul_eq_mul]
  ring

/-- The second moment of a projected hopping matrix with varying moduli is a uniform
occupation factor times the sum of the squared moduli over the graph's arcs. -/
theorem secondMoment_eq_sum_arcs {w : V → V → ℝ} (n : σ → ℕ)
    (hB : (basis V n).Nonempty) (hN : 2 ≤ Fintype.card V)
    (hH : IsGraphProjectedHopping G w H) :
    secondMoment (basis V n) H =
      (∑ s, n s : ℕ) * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
          ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) *
        ∑ p ∈ arcs G, (w p.1 p.2 : ℂ) ^ 2 := by
  obtain ⟨c₀, hc₀⟩ := hB
  have hmN : ∑ s, n s ≤ Fintype.card V := by
    rw [← card_occ hc₀]
    exact card_le_univ _
  have htr : ∑ c ∈ basis V n, H c c = 0 :=
    sum_eq_zero fun c _ => apply_self_eq_zero hH c
  let f : Finset V → ℂ := fun S => ∑ p ∈ hops G S, (w p.1 p.2 : ℂ) ^ 2
  have hdiag : ∑ c ∈ basis V n, ∑ b ∈ basis V n, H c b * H b c = ∑ c ∈ basis V n, f (occ c) :=
    sum_congr rfl fun c hc => sum_mul_apply_self_eq_sum_hops hc hH
  have hspin := sum_basis_comp_occ n f
  have hcount := sum_hops_mul G (fun p => (w p.1 p.2 : ℂ) ^ 2) (∑ s, n s)
  have hB0 : ((basis V n).card : ℂ) ≠ 0 := by
    exact_mod_cast (card_pos.mpr ⟨c₀, hc₀⟩).ne'
  rw [secondMoment, htr, hdiag, zero_div, zero_pow two_ne_zero, sub_zero]
  set W := ∑ p ∈ arcs G, (w p.1 p.2 : ℂ) ^ 2
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
  rw [div_mul_eq_mul_div, div_eq_div_iff hB0 (mul_ne_zero hN0 hN1)]
  linear_combination hkey'

/-- **The exact second-moment theorem.** On the no-double-occupancy basis `B` with `n_s`
particles of spin `s` (assumed nonempty) of a graph with `N ≥ 2` vertices, the second
spectral moment of a projected hopping operator is `t² · 2|E| · n(N - n)/(N(N - 1))`, with
`n = ∑ n_s`. -/
theorem second_moment (hH : IsProjectedHopping G t H) (n : σ → ℕ)
    (hB : (basis V n : Finset (Config V σ)).Nonempty) (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) H =
      (t : ℂ) ^ 2 * (2 * G.edgeFinset.card) * (∑ s, n s : ℕ) *
          ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
        ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) := by
  rw [secondMoment_eq_sum_arcs n hB hN hH,
    sum_const, nsmul_eq_mul, card_arcs]
  push_cast
  rw [div_mul_eq_mul_div]
  congr 1
  ring

/-- **On a `z`-regular graph**, `μ₂ = t² n z (N - n)/(N - 1)`: the form used throughout
the paper. -/
theorem second_moment_regular (hH : IsProjectedHopping G t H) {z : ℕ}
    (hz : G.IsRegularOfDegree z) (n : σ → ℕ) (hB : (basis V n : Finset (Config V σ)).Nonempty)
    (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) H =
      (t : ℂ) ^ 2 * (∑ s, n s : ℕ) * z * ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
        ((Fintype.card V : ℂ) - 1) := by
  rw [second_moment hH n hB hN]
  have hE := twice_card_edges_of_isRegularOfDegree G hz
  have hE' : (2 * G.edgeFinset.card : ℂ) = Fintype.card V * z := by exact_mod_cast hE
  have hN0 : (Fintype.card V : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card V ≠ 0)
  have hN1 : (Fintype.card V : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (by omega : Fintype.card V ≠ 1)
  rw [hE', div_eq_div_iff (mul_ne_zero hN0 hN1) hN1]
  ring

end Moments

/-! ### The hypotheses are satisfiable -/

section Witness

variable [DecidableEq V] (G : SimpleGraph V)

open Classical in
/-- The hop matrix with every sign `+` (hard-core bosons): the matrix element from `c` to
`b` is `t` when `b` is obtained from `c` by one hop along an edge, and `0` otherwise. -/
noncomputable def hopMatrix (t : ℝ) : Matrix (Config V σ) (Config V σ) ℂ := fun b c =>
  if IsProjectedHop G c b then (t : ℂ) else 0

/-- One hop leads from `c` to `b` exactly when one hop leads from `b` back to `c`. -/
theorem exists_hop_comm {b c : Config V σ} :
    IsProjectedHop G c b ↔ IsProjectedHop G b c := by
  have key : ∀ b c : Config V σ, IsProjectedHop G c b → IsProjectedHop G b c := by
    rintro b c ⟨i, j, hij, hi, hj, rfl⟩
    refine ⟨j, i, hij.symm, ?_, ?_, ?_⟩
    · rw [move_apply_right]
      exact hi
    · exact move_apply_left c hij.ne
    · exact (move_move c hij.ne hj).symm
  exact ⟨key b c, key c b⟩

/-- For `t ≥ 0`, the hop matrix is a projected hopping operator: the hypotheses of the
second-moment theorem can be met on every graph, so the theorem is not vacuous. -/
theorem isProjectedHopping_hopMatrix {t : ℝ} (ht : 0 ≤ t) :
    IsProjectedHopping G t (hopMatrix (σ := σ) G t) where
  isHermitian := by
    ext b c
    simp only [Matrix.conjTranspose_apply, hopMatrix]
    have hcomm := exists_hop_comm G (b := c) (c := b)
    split_ifs with h1 h2 h2
    · simp
    · exact absurd (hcomm.mp h1) h2
    · exact absurd (hcomm.mpr h2) h1
    · simp
  norm_apply_move := by
    intro c i j hij hi hj
    have hcond : IsProjectedHop G c (move c i j) := ⟨i, j, hij, hi, hj, rfl⟩
    simp only [hopMatrix, hcond, ↓reduceIte, Complex.norm_real, Real.norm_of_nonneg ht]
  apply_eq_zero := by
    intro c b h
    simp only [hopMatrix, h, ↓reduceIte]

end Witness

end HubbardMoments
