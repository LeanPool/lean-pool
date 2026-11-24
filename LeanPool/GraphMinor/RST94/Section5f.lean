/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section5e
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Section 5 of "Quickly excluding a planar graph": (5.7)

The main result (5.7), page 344, for `g ≥ 3`, in the form `HasGrid`. We turn it into a grid minor in
`GraphMinor/RST94/Theorem23.lean`. The case `g = 2` in the paper uses Graph Minors X (8.3), and it
is not needed: XVI uses `g = 2θ + 1 ≥ 3`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β : Type*} {G : Hypergraph α β}

/-- The sets `U_{ij}` in the proof of (5.7), with `i` and `j` from `0`: the paper's `U_{i+1, j+1}`.
-/
def arrayU (A : ℕ → ℕ → Set α) (t i j : ℕ) : Set α :=
  {v | ∃ k, j * t ≤ k ∧ k < (j + 1) * t ∧ v ∈ A (i + 1) k} ∪ {v | Even (i + 1) ∧ v ∈ A 0 (j * t +
    (i + 1) / 2 - 1)}

/-- A block of consecutive sets of a row is connected. -/
theorem conn_block {m n : ℕ} {A : ℕ → ℕ → Set α} (hA : IsArray G m n A) {i : ℕ} (h₁ : 1 ≤ i)
  (h₂ : i ≤ m) (a s : ℕ) (hs : a + s + 1 ≤ n) :
    Conn G {v | ∃ k, a ≤ k ∧ k < a + s + 1 ∧ v ∈ A i k} := by
  induction s with
  | zero =>
    have : {v | ∃ k, a ≤ k ∧ k < a + 0 + 1 ∧ v ∈ A i k} = A i a := by
      ext v
      constructor
      · rintro ⟨k, h₃, h₄, h₅⟩
        obtain rfl : k = a := by omega
        exact h₅
      · exact fun h => ⟨a, le_rfl, by omega, h⟩
    rw [this]
    exact hA.conn i h₂ a (by omega)
  | succ s ih =>
    have h₃ := ih (by omega)
    obtain ⟨x, hx, y, hy, hxy⟩ := hA.row i h₁ h₂ (a + s) (by omega)
    have h₄ := h₃.union_adj (hA.conn i h₂ (a + s + 1) (by omega)) ⟨a + s, by omega, by omega, hx⟩
      hy hxy
    have : {v | ∃ k, a ≤ k ∧ k < a + (s + 1) + 1 ∧ v ∈ A i k} = {v | ∃ k, a ≤ k ∧ k < a + s + 1
      ∧ v ∈ A i k} ∪ A i (a + s + 1) := by
      ext v
      constructor
      · rintro ⟨k, h₅, h₆, h₇⟩
        rcases Nat.lt_or_ge k (a + s + 1) with h₈ | h₈
        · exact Or.inl ⟨k, h₅, h₈, h₇⟩
        · obtain rfl : k = a + s + 1 := by omega
          exact Or.inr h₇
      · rintro (⟨k, h₅, h₆, h₇⟩ | h₅)
        · exact ⟨k, h₅, by omega, h₇⟩
        · exact ⟨a + s + 1, by omega, by omega, h₅⟩
    rw [this]
    exact h₄

/-- The sets `U_{ij}` in the proof of (5.7) form a grid, with rows and columns exchanged. -/
theorem hasGrid_of_array {T : Set (Hypergraph α β × Hypergraph α β)} {θ g t : ℕ}
  (hT : IsTangle G θ T) {A : ℕ → ℕ → Set α} (hA : IsArray G g (g * t) A) (ht : 1 ≤ t) (htg : g
    ≤ 2 * t + 1)
    (hr : ∀ i ≤ g, min g (g * t) ≤ tangleRank T θ (⋃ j ∈ {j | j < g * t}, A i j)) : HasGrid G T θ g
      := by
  have hbound : ∀ {j}, j < g → (j + 1) * t ≤ g * t := fun {j} hj => Nat.mul_le_mul_right _ hj
  have hsucc : ∀ j, (j + 1) * t = j * t + t := fun j => Nat.succ_mul j t
  -- The index of the extra set.
  have hl : ∀ {i j}, i < g → j < g → Even (i + 1) → j * t ≤ j * t + (i + 1) / 2 - 1 ∧ j * t +
    (i + 1) / 2 - 1 < (j + 1) * t := fun {i j} hi hj he => by
    obtain ⟨c, hc⟩ := he
    rw [hsucc]
    omega
  have hlk : ∀ {j}, j < g → ∀ k, k < (j + 1) * t → k < g * t := fun hj k hk => hk.trans_le
    (hbound hj)
  have hconnU : ∀ i < g, ∀ j < g, Conn G (arrayU A t i j) := fun i hi j hj => by
    obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hbl := hbound hj
    rw [hsucc] at hbl
    have h₁ := conn_block hA (i := i + 1) (by omega) (by omega) (j * t) s (by omega)
    have heq : {v | ∃ k, j * t ≤ k ∧ k < (j + 1) * t ∧ v ∈ A (i + 1) k} = {v | ∃ k, j * t ≤ k
      ∧ k < j * t + s + 1 ∧ v ∈ A (i + 1) k} := by
      rw [hsucc, hs]
      rfl
    by_cases he : Even (i + 1)
    · have h₂ : arrayU A t i j = {v | ∃ k, j * t ≤ k ∧ k < (j + 1) * t ∧ v ∈ A (i + 1) k} ∪
        A 0 (j * t + (i + 1) / 2 - 1) := by
        ext v
        simp [arrayU, he]
      rw [h₂, heq]
      obtain ⟨hl₁, hl₂⟩ := hl hi hj he
      obtain ⟨x, hx, y, hy, hxy⟩ := hA.apex (i + 1) (by omega) (by omega) _ (hlk hj _ hl₂)
      refine h₁.union_adj (hA.conn 0 (Nat.zero_le _) _ (hlk hj _ hl₂)) (x := y) (y := x) ⟨_, hl₁,
        ?_, hy⟩ hx hxy.symm
      rw [hsucc] at hl₂
      omega
    · have h₂ : arrayU A t i j = {v | ∃ k, j * t ≤ k ∧ k < (j + 1) * t ∧ v ∈ A (i + 1) k} := by
        ext v
        simp [arrayU, he]
      rw [h₂, heq]
      exact h₁
  have hrange : ∀ {j j' k k' : ℕ}, j ≠ j' → j * t ≤ k → k < (j + 1) * t → j' * t ≤ k' → k' <
    (j' + 1) * t → k ≠ k' := fun {j j' k k'} hne h₁ h₂ h₃ h₄ e => by
    subst e
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.mul_le_mul_right t (show j + 1 ≤ j' from h)
      omega
    · have := Nat.mul_le_mul_right t (show j' + 1 ≤ j from h)
      omega
  have hdU : ∀ i < g, ∀ j < g, ∀ i' < g, ∀ j' < g, (i, j) ≠ (i', j') → Disjoint (arrayU A t i j)
    (arrayU A t i' j') := fun i hi j hj i' hi' j' hj' hne => by
    refine disjoint_left.2 ?_
    rintro v (⟨k, h₁, h₂, hv⟩ | ⟨he, hv⟩) (⟨k', h₃, h₄, hv'⟩ | ⟨he', hv'⟩)
    · refine disjoint_left.1 (hA.disj (i + 1) (by omega) k (hlk hj k h₂) (i' + 1) (by omega) k'
      (hlk hj' k' h₄) fun e => ?_) hv hv'
      have e₁ : i + 1 = i' + 1 := (Prod.ext_iff.1 e).1
      have e₂ : k = k' := (Prod.ext_iff.1 e).2
      have hii : i = i' := by omega
      subst hii
      exact hrange (fun hjj => hne (by rw [hjj])) h₁ h₂ h₃ h₄ e₂
    · obtain ⟨hl₁, hl₂⟩ := hl hi' hj' he'
      exact disjoint_left.1 (hA.disj (i + 1) (by omega) k (hlk hj k h₂) 0 (Nat.zero_le _) _
        (hlk hj' _ hl₂) fun e => by simpa using (Prod.ext_iff.1 e).1) hv hv'
    · obtain ⟨hl₁, hl₂⟩ := hl hi hj he
      exact disjoint_left.1 (hA.disj 0 (Nat.zero_le _) _ (hlk hj _ hl₂) (i' + 1) (by omega) k'
        (hlk hj' k' h₄) fun e => by simpa using (Prod.ext_iff.1 e).1) hv hv'
    · obtain ⟨hl₁, hl₂⟩ := hl hi hj he
      obtain ⟨hl₃, hl₄⟩ := hl hi' hj' he'
      refine disjoint_left.1 (hA.disj 0 (Nat.zero_le _) _ (hlk hj _ hl₂) 0 (Nat.zero_le _) _
        (hlk hj' _ hl₄) fun e => ?_) hv hv'
      have e₂ : j * t + (i + 1) / 2 - 1 = j' * t + (i' + 1) / 2 - 1 := (Prod.ext_iff.1 e).2
      by_cases hjj : j = j'
      · subst hjj
        obtain ⟨c, hc⟩ := he
        obtain ⟨c', hc'⟩ := he'
        have hii : i = i' := by omega
        exact hne (by rw [hii])
      · exact hrange hjj hl₁ hl₂ hl₃ hl₄ e₂
  refine ⟨fun a b => arrayU A t b a, ⟨fun a ha b hb => ?_, fun a ha b hb
    => hconnU b hb a ha, fun a ha b hb a' ha' b' hb' hne => hdU b hb a ha b' hb' a' ha' fun e
      => hne ?_, fun a ha b hb => ?_, fun a ha b hb => ?_, fun b hb => ?_⟩⟩
  · rintro v (⟨k, -, h₂, hv⟩ | ⟨he, hv⟩)
    · exact hA.sub (b + 1) (by omega) k (hlk ha k h₂) hv
    · exact hA.sub 0 (Nat.zero_le _) _ (hlk ha _ (hl hb ha he).2) hv
  · have e₁ : b = b' := (Prod.ext_iff.1 e).1
    have e₂ : a = a' := (Prod.ext_iff.1 e).2
    rw [e₁, e₂]
  · -- Adjacent rows of `U` meet the same set `W_{0,l}`.
    by_cases he : Even (b + 1)
    · obtain ⟨hl₁, hl₂⟩ := hl (i := b) (j := a) (by omega) ha he
      obtain ⟨x, hx, y, hy, hxy⟩ := hA.apex (b + 1 + 1) (by omega) (by omega) _ (hlk ha _ hl₂)
      exact ⟨x, Or.inr ⟨he, hx⟩, y, Or.inl ⟨_, hl₁, hl₂, hy⟩, hxy⟩
    · have he₂ : Even (b + 1 + 1) := by
        rcases Nat.even_or_odd (b + 1) with h | h
        · exact absurd h he
        · exact h.add_one
      obtain ⟨hl₁, hl₂⟩ := hl (i := b + 1) (j := a) hb ha he₂
      obtain ⟨x, hx, y, hy, hxy⟩ := hA.apex (b + 1) (by omega) (by omega) _ (hlk ha _ hl₂)
      exact ⟨y, Or.inl ⟨_, hl₁, hl₂, hy⟩, x, Or.inr ⟨he₂, hx⟩, hxy.symm⟩
  · -- Adjacent columns of `U` by the last and first sets of the two blocks.
    have h₁ := hbound ha
    have h₂ := hsucc (a + 1)
    have h₃ := hsucc a
    obtain ⟨x, hx, y, hy, hxy⟩ := hA.row (b + 1) (by omega) (by omega) ((a + 1) * t - 1) (by omega)
    refine ⟨x, Or.inl ⟨_, by omega, by omega, hx⟩, y, Or.inl ⟨_, ?_, ?_, hy⟩, hxy⟩ <;> omega
  · have hmin : min g (g * t) = g := min_eq_left (Nat.le_mul_of_pos_right g ht)
    have h₂ := hr (b + 1) (by omega)
    rw [hmin] at h₂
    refine h₂.trans (tangleRank_mono hT (iUnion₂_subset fun k hk v hv => ?_))
    have hk' : k < g * t := hk
    have htpos : 0 < t := ht
    have hdiv := Nat.div_add_mod k t
    have hmod := Nat.mod_lt k htpos
    have ha : k / t < g := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk')
    rw [Nat.mul_comm] at hdiv
    refine mem_iUnion₂.2 ⟨k / t, ha, Or.inl ⟨k, by omega, ?_, hv⟩⟩
    rw [hsucc]
    omega

/-- **(5.7)** (page 344), for `g ≥ 3`. -/
theorem theorem_5_7 (hG : G.IsGraph) {T : Set (Hypergraph α β × Hypergraph α β)} {θ g : ℕ}
  (hT : IsTangle G θ T) (hg : 3 ≤ g) (hθ : 20 ^ (g ^ 4 * (2 * g - 1)) ≤ θ) : HasGrid G T θ g := by
  by_contra hno
  obtain ⟨h, rfl⟩ : ∃ h, g = h + 3 := ⟨g - 3, by omega⟩
  set g := h + 3 with hgdef
  set t := g / 2 with ht
  have ht₁ : 1 ≤ t := by omega
  have ht₂ : g ≤ 2 * t + 1 := by omega
  have ht₃ : 2 * t ≤ g := by omega
  set N := (2 * g + 1) * (2 * g - 5) + 2 with hN
  set u := 2 * g * (g - 2) + N * (g + 1) with hu
  have hbound : g * t * u ≤ g ^ 4 * (2 * g - 1) := by
    have h₁ : u + 15 * h + 48 = 2 * g * g * (2 * g - 1) := by
      have e₁ : 2 * g - 5 = 2 * h + 1 := by omega
      have e₂ : g - 2 = h + 1 := by omega
      have e₃ : 2 * g - 1 = 2 * h + 5 := by omega
      rw [hu, hN, e₁, e₂, e₃, hgdef]
      ring
    have h₂ : 2 * (g * t * u) ≤ 2 * (g ^ 4 * (2 * g - 1)) := by
      calc 2 * (g * t * u) = g * (2 * t) * u := by ring
        _ ≤ g * g * u := by gcongr
        _ ≤ g * g * (2 * g * g * (2 * g - 1)) := by
          gcongr
          omega
        _ = 2 * (g ^ 4 * (2 * g - 1)) := by ring
    omega
  obtain ⟨A, hA, hr⟩ := theorem_5_6 hG hT (g := g) (m := g) (n := g * t) (N := N) (t := u)
    (by omega) hg (Nat.mul_pos (by omega) ht₁) hu hN ((Nat.pow_le_pow_right
      (by omega) hbound).trans hθ) hno
  exact hno (hasGrid_of_array hT hA ht₁ ht₂ hr)

end GraphMinor.RST94
