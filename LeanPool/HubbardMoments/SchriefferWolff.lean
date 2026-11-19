/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.Torus
public import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The Schrieffer–Wolff cross term

Truncating the effective Hamiltonian on the no-double-occupancy sector `P₀` through order
`1/U` gives `T₀ - V/U`, where `T₀ = P₀ H P₀`, `T₁ = Q₁ H P₀`, and `V = T₁† T₁`
(`HubbardMoments.virtualOp`). The central second moment of this truncated matrix is
`μ₂(T₀) - (2/U) ⟨T₀, V⟩ + Var(V)/U²`. The full expansion also has a third-order hopping
term at order `1/U²`, as described in the paper's §7.1, equations (16) and (17). Section 7
states that the cross term `⟨T₀, V⟩ = Tr(T₀ V)/|P₀|` vanishes for `L ≥ 4`.
For every hopping operator `H` on a graph `G`
(`HubbardMoments.IsHoppingOperator`):

* `apply_self_eq_zero`: the diagonal of `H` vanishes;
* `sum_mul_virtualOp_eq_zero`: if `G` has no triangle, `Tr(T₀ V) = 0`, term by term;
* `secondMoment_sub_virtualOp`: hence, on a triangle-free graph,
  `μ₂(T₀ - V/U) = μ₂(T₀) + Var(V)/U²` exactly: no `1/U` term;
* `secondMoment_sub_virtualOp_torus`: this holds on the `L × L` torus for `L ≥ 4`;
* `exists_crossTerm_ne_zero_torus_three`: on the `3 × 3` torus the hypothesis fails and the
  conclusion can too. Three states along one row of the torus, one hop apart pairwise,
  give a Hermitian hopping operator with `∑_{a, b ∈ B} H_{ab} V_{ba} = 2`.

The proof counts particles per site. A nonzero term `(T₀)_{ab} V_{ba}` needs one hop `b → a`
and two hops `a → m`, `b → m` into a state `m` with a doubly occupied site `w`. Counting
shows that the hop `b → a` goes from `i` to `j`, the hop `a → m` from `j` to `w` and the hop
`b → m` from `i` to `w`, so `i, j, w` form a triangle. The `3 × 3` torus has triangles
(`torus_three_not_cliqueFree`), which is why `L = 3` is excluded.

## Not covered

The expansion `H_eff = T₀ - V/U + O(1/U²)` itself (standard degenerate perturbation theory),
and the size of `Var(V)`.
-/

public section

namespace HubbardMoments

open Finset SimpleGraph

variable {V σ : Type*} [DecidableEq V] [DecidableEq σ] {G : SimpleGraph V}

/-- One hop from `i` to `j` removes a particle from `i` and adds one to `j`. -/
theorem IsHop.siteOcc_eq {a b : FockState V σ} (h : IsHop G a b) :
    ∃ i j, G.Adj i j ∧ ∀ v,
      siteOcc b v + (if i = v then 1 else 0) = siteOcc a v + (if j = v then 1 else 0) := by
  obtain ⟨i, j, s, hij, hi, hj, rfl⟩ := h
  refine ⟨i, j, hij, fun v => ?_⟩
  simp only [siteOcc, card_filter]
  rw [sum_insert (fun h => hj (mem_of_mem_erase h)), ← sum_erase_add a _ hi]
  ring

/-- A hop changes the state. -/
theorem IsHop.ne {a b : FockState V σ} (h : IsHop G a b) : a ≠ b := by
  obtain ⟨i, j, s, -, -, hj, rfl⟩ := h
  intro hab
  exact hj (hab ▸ mem_insert_self (j, s) _)

variable {H : Matrix (FockState V σ) (FockState V σ) ℂ}

/-- A nonzero matrix element of a hopping operator is a hop. -/
theorem IsHoppingOperator.isHop (hH : IsHoppingOperator G H) {a b : FockState V σ}
    (h : H b a ≠ 0) : IsHop G a b :=
  Classical.byContradiction fun h' => h (hH.apply_eq_zero a b h')

/-- **The diagonal of a hopping operator vanishes**, so `Tr T₀ = 0`. -/
theorem IsHoppingOperator.apply_self_eq_zero (hH : IsHoppingOperator G H) (a : FockState V σ) :
    H a a = 0 :=
  hH.apply_eq_zero a a fun h => h.ne rfl

/-- **The counting step.** If `a` and `b` have no doubly occupied site, `m` has one, and `a` is
one hop from `b` while `m` is one hop from both `a` and `b`, then `G` has a triangle. -/
theorem not_hop_triangle (hG : G.CliqueFree 3) {a b m : FockState V σ}
    (ha : ∀ v, siteOcc a v ≤ 1) (hb : ∀ v, siteOcc b v ≤ 1) (hm : ∃ w, 2 ≤ siteOcc m w)
    (hba : IsHop G b a) (hbm : IsHop G b m) (ham : IsHop G a m) : False := by
  obtain ⟨i, j, hij, e₁⟩ := hba.siteOcc_eq
  obtain ⟨i₂, w₂, h₂, e₂⟩ := hbm.siteOcc_eq
  obtain ⟨i₁, w₁, h₁, e₃⟩ := ham.siteOcc_eq
  obtain ⟨w, hw⟩ := hm
  have hne : i ≠ j := G.ne_of_adj hij
  -- The doubly occupied site of `m` is where both hops into `m` arrive.
  have hw₁ : w₁ = w := by
    by_contra hne₁
    have h3 := e₃ w
    have h4 := ha w
    simp only [hne₁, ↓reduceIte] at h3
    split_ifs at h3 <;> omega
  subst hw₁
  have hw₂ : w₂ = w₁ := by
    by_contra hne₂
    have h2 := e₂ w₁
    have h4 := hb w₁
    simp only [hne₂, ↓reduceIte] at h2
    split_ifs at h2 <;> omega
  subst hw₂
  -- The hop `a → m` starts at `j`, the hop `b → m` at `i`.
  have hi₁ : i₁ = j := by
    by_contra hne₁
    have h1 := e₁ j
    have h2 := e₂ j
    have h3 := e₃ j
    simp only [hne₁, hne, ↓reduceIte] at h1 h3
    split_ifs at h1 h2 h3 <;> omega
  subst hi₁
  have hi₂ : i₂ = i := by
    by_contra hne₂
    have h1 := e₁ i
    have h2 := e₂ i
    have h3 := e₃ i
    simp only [hne₂, hne.symm, ↓reduceIte] at h1 h2 h3
    split_ifs at h1 h2 h3 <;> omega
  subst hi₂
  exact hG {i₂, i₁, w₂} (is3Clique_triple_iff.2 ⟨hij, h₂, h₁⟩)

/-- **The cross term vanishes on a triangle-free graph.** Let `B` be a set of states without
doubly occupied sites (`P₀`, or one particle-number sector of it) and `Q` a set of states
with a doubly occupied site (`Q₁`). Then `Tr(T₀ V) = ∑_{a, b ∈ B} H_{ab} V_{ba} = 0`, term by
term. -/
theorem sum_mul_virtualOp_eq_zero (hH : IsHoppingOperator G H) (hG : G.CliqueFree 3)
    {B Q : Finset (FockState V σ)} (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1)
    (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) :
    ∑ a ∈ B, ∑ b ∈ B, H a b * virtualOp Q H b a = 0 := by
  refine sum_eq_zero fun a ha => sum_eq_zero fun b hb => ?_
  simp only [virtualOp, mul_sum]
  refine sum_eq_zero fun m hm => ?_
  by_contra hne
  have h₁ : H a b ≠ 0 := left_ne_zero_of_mul hne
  have h₂ : star (H m b) * H m a ≠ 0 := right_ne_zero_of_mul hne
  have h₃ : H m b ≠ 0 := fun h => h₂ (by rw [h, star_zero, zero_mul])
  have h₄ : H m a ≠ 0 := right_ne_zero_of_mul h₂
  exact not_hop_triangle hG (hB a ha) (hB b hb) (hQ m hm) (hH.isHop h₁) (hH.isHop h₃) (hH.isHop h₄)

/-- **No `1/U` correction to `μ₂` on a triangle-free graph.** With `B`, `Q` as in
`sum_mul_virtualOp_eq_zero`, the second moment of the second-order effective Hamiltonian
`T₀ - V/U` on `B` is `μ₂(T₀) + Var(V)/U²`, where `μ₂(T₀) = secondMoment B H` and
`Var(V) = secondMoment B V`. -/
theorem secondMoment_sub_virtualOp (hH : IsHoppingOperator G H) (hG : G.CliqueFree 3)
    {B Q : Finset (FockState V σ)} (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1)
    (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) (U : ℝ) :
    secondMoment B (H - (U : ℂ)⁻¹ • virtualOp Q H) =
      secondMoment B H + secondMoment B (virtualOp Q H) / (U : ℂ) ^ 2 := by
  set W := virtualOp Q H
  set c := (U : ℂ)⁻¹
  have h₁ : ∑ a ∈ B, ∑ b ∈ B, H a b * W b a = 0 := sum_mul_virtualOp_eq_zero hH hG hB hQ
  have h₂ : ∑ a ∈ B, ∑ b ∈ B, W a b * H b a = 0 := by
    rw [sum_comm]
    refine Eq.trans (sum_congr rfl fun a _ => sum_congr rfl fun b _ => mul_comm _ _) h₁
  have hd : ∑ a ∈ B, H a a = 0 := sum_eq_zero fun a _ => hH.apply_self_eq_zero a
  have expand : ∑ a ∈ B, ∑ b ∈ B, (H a b - c * W a b) * (H b a - c * W b a) =
      ∑ a ∈ B, ∑ b ∈ B, H a b * H b a - c * ∑ a ∈ B, ∑ b ∈ B, H a b * W b a -
        c * ∑ a ∈ B, ∑ b ∈ B, W a b * H b a + c ^ 2 * ∑ a ∈ B, ∑ b ∈ B, W a b * W b a := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have diag : ∑ a ∈ B, (H a a - c * W a a) = ∑ a ∈ B, H a a - c * ∑ a ∈ B, W a a := by
    rw [sum_sub_distrib, mul_sum]
  simp only [secondMoment, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [expand, diag, h₁, h₂, hd]
  ring

/-- **The torus form**: for `L ≥ 4` the `L × L` torus has no triangle, so
`μ₂(T₀ - V/U) = μ₂(T₀) + Var(V)/U²` on it. -/
theorem secondMoment_sub_virtualOp_torus {L : ℕ} (hL : 4 ≤ L)
    {H : Matrix (FockState (Fin L × Fin L) σ) (FockState (Fin L × Fin L) σ) ℂ}
    (hH : IsHoppingOperator (torus L) H) {B Q : Finset (FockState (Fin L × Fin L) σ)}
    (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) (U : ℝ) :
    secondMoment B (H - (U : ℂ)⁻¹ • virtualOp Q H) =
      secondMoment B H + secondMoment B (virtualOp Q H) / (U : ℂ) ^ 2 :=
  secondMoment_sub_virtualOp hH (torus_cliqueFree_three (by omega)) hB hQ U

/-! ### On the `3 × 3` torus the cross term can be nonzero -/

section TorusThree

/-- Up electron at `(0, 0)`, down electron at `(2, 0)`. -/
def rowState₀ : FockState (Fin 3 × Fin 3) (Fin 2) := {((0, 0), 0), ((2, 0), 1)}

/-- Up electron at `(1, 0)`, down electron at `(2, 0)`. -/
def rowState₁ : FockState (Fin 3 × Fin 3) (Fin 2) := {((1, 0), 0), ((2, 0), 1)}

/-- A doublon at `(2, 0)`. -/
def rowDoublon : FockState (Fin 3 × Fin 3) (Fin 2) := {((2, 0), 0), ((2, 0), 1)}

/-- The three row states. Since `(0, 0)`, `(1, 0)` and `(2, 0)` form a triangle of the
`3 × 3` torus, any two of them are one hop apart. -/
def rowStates : Finset (FockState (Fin 3 × Fin 3) (Fin 2)) := {rowState₀, rowState₁, rowDoublon}

/-- Matrix element `1` between any two distinct row states, `0` elsewhere. -/
noncomputable def rowHopping :
    Matrix (FockState (Fin 3 × Fin 3) (Fin 2)) (FockState (Fin 3 × Fin 3) (Fin 2)) ℂ :=
  fun x y => if x ≠ y ∧ x ∈ rowStates ∧ y ∈ rowStates then 1 else 0

theorem isHop_rowStates {x y : FockState (Fin 3 × Fin 3) (Fin 2)} (hx : x ∈ rowStates)
    (hy : y ∈ rowStates) (h : x ≠ y) : IsHop (torus 3) x y := by
  simp only [rowStates, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals try exact absurd rfl h
  · exact ⟨(0, 0), (1, 0), 0, by decide, by decide, by decide, by decide⟩
  · exact ⟨(0, 0), (2, 0), 0, by decide, by decide, by decide, by decide⟩
  · exact ⟨(1, 0), (0, 0), 0, by decide, by decide, by decide, by decide⟩
  · exact ⟨(1, 0), (2, 0), 0, by decide, by decide, by decide, by decide⟩
  · exact ⟨(2, 0), (0, 0), 0, by decide, by decide, by decide, by decide⟩
  · exact ⟨(2, 0), (1, 0), 0, by decide, by decide, by decide, by decide⟩

theorem isHoppingOperator_rowHopping : IsHoppingOperator (torus 3) rowHopping := by
  refine ⟨fun x y h => ?_⟩
  simp only [rowHopping]
  split_ifs with hc
  · exact absurd (isHop_rowStates hc.2.2 hc.2.1 (Ne.symm hc.1)) h
  · rfl

theorem rowHopping_isHermitian : rowHopping.IsHermitian := by
  ext x y
  have e : (y ≠ x ∧ y ∈ rowStates ∧ x ∈ rowStates) ↔ (x ≠ y ∧ x ∈ rowStates ∧ y ∈ rowStates) :=
    ⟨fun h => ⟨h.1.symm, h.2.2, h.2.1⟩, fun h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  simp only [Matrix.conjTranspose_apply, rowHopping, e]
  split_ifs <;> simp

/-- **The triangle-free hypothesis cannot be dropped.** On the `3 × 3` torus, with
`B = {rowState₀, rowState₁}` (no double occupancy) and `Q = {rowDoublon}`, the Hermitian
hopping operator `rowHopping` has `∑_{a, b ∈ B} H_{ab} V_{ba} = 2`. -/
theorem crossTerm_rowHopping :
    ∑ a ∈ {rowState₀, rowState₁}, ∑ b ∈ {rowState₀, rowState₁},
      rowHopping a b * virtualOp {rowDoublon} rowHopping b a = 2 := by
  have h₀₁ : rowState₀ ≠ rowState₁ := by decide
  have h₀d : rowState₀ ≠ rowDoublon := by decide
  have h₁d : rowState₁ ≠ rowDoublon := by decide
  simp [virtualOp, rowHopping, rowStates, sum_insert, h₀₁, h₀₁.symm, h₀d, h₁d, h₀d.symm,
    h₁d.symm]
  norm_num

theorem exists_crossTerm_ne_zero_torus_three :
    ∃ (H : Matrix (FockState (Fin 3 × Fin 3) (Fin 2)) (FockState (Fin 3 × Fin 3) (Fin 2)) ℂ)
      (B Q : Finset (FockState (Fin 3 × Fin 3) (Fin 2))),
      H.IsHermitian ∧ IsHoppingOperator (torus 3) H ∧ (∀ a ∈ B, ∀ v, siteOcc a v ≤ 1) ∧
        (∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) ∧ ∑ a ∈ B, ∑ b ∈ B, H a b * virtualOp Q H b a ≠ 0 :=
  ⟨rowHopping, {rowState₀, rowState₁}, {rowDoublon}, rowHopping_isHermitian,
    isHoppingOperator_rowHopping,
    by
      intro a ha
      simp only [mem_insert, mem_singleton] at ha
      rcases ha with rfl | rfl <;> decide,
    fun m hm => ⟨(2, 0), by rw [mem_singleton.1 hm]; decide⟩,
    by rw [crossTerm_rowHopping]; norm_num⟩

end TorusThree

end HubbardMoments
