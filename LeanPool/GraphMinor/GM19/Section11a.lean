/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic.Push

/-!
# Graph Minors XIX, Section 11: the sequence argument of (11.2)

The proof of (11.2) walks along the edges `e₀, e₁, …, e_{k+1}` bordering a long side. It only uses
which intervals `[i, j]` of edges are covered by a short bite. This file does that part for an
abstract relation `N i j`, read as "`i ≪ j` fails". So `N i j` says that one short bite covers
`e_i, …, e_j`. The relation is monotone, and it holds for `i = j`. The paper uses that it holds for
neighbours, but `e_i, e_{i+1}` need not lie in one bite when the cuff has only these two edges, and
the argument does not need it if we allow `a_{i+1} = b_i` and `b_{p+1} = k + 1`.

Given a chain `0 = b₀ < a₁ < b₁ < ⋯ < b_p` as in the paper, `exists_step` either extends the chain,
or finishes with the last pair `a_{p+1}, b_{p+1}`. These are the steps (2) and (3) of the paper. The
result used later is `exists_final`.
-/

@[expose] public section

namespace GraphMinor.GM19

/-- The data `0 = b₀ ≤ a₁ < b₁ ≤ a₂ < ⋯ < b_p < k + 1` of the proof of (11.2). Here `P h j` says
that
`φ(e_j) ≥ ω_{h+1}`, and `N i j` says that `i ≪ j` fails. -/
structure SideChain (N : ℕ → ℕ → Prop) (P : ℕ → ℕ → Prop) (k p : ℕ) (a b : ℕ → ℕ) : Prop where
  b_zero : b 0 = 0
  b_le_a : ∀ i < p, b i ≤ a (i + 1)
  a_lt_b : ∀ i < p, a (i + 1) < b (i + 1)
  far : ∀ i < p, ¬ N (b i) (b (i + 1))
  near : ∀ i < p, N (b i) (a (i + 1))
  label : ∀ i < p, P i (b (i + 1))
  gap : ∀ i < p, ∀ j, a (i + 1) < j → j < b (i + 1) → ¬ P i j
  lt_end : b p < k + 1
  far_end : ¬ N (b p) (k + 1)

/-- The last pair `a_{p+1}, b_{p+1}`, as in (3) of the proof of (11.2). -/
structure SideFinal (N : ℕ → ℕ → Prop) (P : ℕ → ℕ → Prop) (k p : ℕ) (b₀ a' b' : ℕ) : Prop where
  le₁ : b₀ ≤ a'
  lt₂ : a' < b'
  le₃ : b' ≤ k + 1
  near₁ : N b₀ a'
  near₂ : N b' (k + 1)
  gap : ∀ j, a' < j → j < b' → ¬ P p j

variable {N : ℕ → ℕ → Prop} {P : ℕ → ℕ → Prop} {k : ℕ}

/-- A largest `i` in `[c, d)` with `N c i`, when `N c c` and `c < d`. -/
theorem exists_largest {c d : ℕ} (hc : N c c) (hd : c < d) :
    ∃ i, c ≤ i ∧ i < d ∧ N c i ∧ ∀ j, i < j → j < d → ¬ N c j := by
  classical
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hspec := Nat.findGreatest_spec (P := fun i ↦ c ≤ i ∧ N c i) (m := c) (n := d')
    (by omega) ⟨le_rfl, hc⟩
  have hle := Nat.findGreatest_le (P := fun i ↦ c ≤ i ∧ N c i) d'
  refine ⟨_, hspec.1, by omega, hspec.2, fun j hj hjd hN ↦ ?_⟩
  have := Nat.le_findGreatest (P := fun i ↦ c ≤ i ∧ N c i) (m := j) (n := d')
    (by omega) ⟨by omega, hN⟩
  omega

/-- A least `j` above `i` with the property `Q`, when some `j₀ > i` has it. -/
theorem exists_least {Q : ℕ → Prop} {i j₀ : ℕ} (hi : i < j₀) (hj₀ : Q j₀) :
    ∃ j, i < j ∧ j ≤ j₀ ∧ Q j ∧ ∀ l, i < l → l < j → ¬ Q l := by
  classical
  have hex : ∃ j, i < j ∧ Q j := ⟨j₀, hi, hj₀⟩
  obtain ⟨h₁, h₂⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, h₁, Nat.find_min' hex ⟨hi, hj₀⟩, h₂, fun l hl hlt hQ ↦ ?_⟩
  exact Nat.find_min hex hlt ⟨hl, hQ⟩

/-- One step of the proof of (11.2). A chain of length `p` extends to a chain of length `p + 1`, as
in
(2) of the paper, or it ends with a last pair, as in (3). -/
theorem exists_step (hmono : ∀ i j i' j', i ≤ i' → i' ≤ j' → j' ≤ j → N i j → N i' j')
    (hself : ∀ i ≤ k + 1, N i i) {p : ℕ} {a b : ℕ → ℕ} (hc : SideChain N P k p a b) :
    (∃ a' b', SideFinal N P k p (b p) a' b') ∨ ∃ a' b', SideChain N P k (p + 1) a' b' := by
  have hbk := hc.lt_end
  have hadjb := hself (b p) (by omega)
  by_cases h2 : ∃ j, b p < j ∧ j < k + 1 ∧ ¬ N (b p) j ∧ ¬ N j (k + 1) ∧ P p j
  · right
    obtain ⟨j, hj₁, hj₂, hj₃, hj₄, hj₅⟩ := h2
    obtain ⟨i, hi₁, hi₂, hi₃, hi₄⟩ := exists_largest hadjb hj₁
    obtain ⟨j', hj'₁, hj'₂, hj'₃, hj'₄⟩ := exists_least (Q := P p) hi₂ hj₅
    let a' : ℕ → ℕ := fun l ↦ if l = p + 1 then i else a l
    let b' : ℕ → ℕ := fun l ↦ if l = p + 1 then j' else b l
    have ha' : ∀ l ≤ p, a' l = a l := fun l hl ↦ ite_eq_right (by omega)
    have hb' : ∀ l ≤ p, b' l = b l := fun l hl ↦ ite_eq_right (by omega)
    have ha'p : a' (p + 1) = i := ite_eq_left rfl
    have hb'p : b' (p + 1) = j' := ite_eq_left rfl
    have hfar : ¬ N (b p) j' := by
      rcases Nat.lt_or_ge j' j with h | h
      · exact hi₄ j' hj'₁ h
      · have : j' = j := by omega
        exact this ▸ hj₃
    refine ⟨a', b', ?_⟩
    refine
      { b_zero := by rw [hb' 0 (by omega)]; exact hc.b_zero
        b_le_a := fun l hl ↦ ?_
        a_lt_b := fun l hl ↦ ?_
        far := fun l hl ↦ ?_
        near := fun l hl ↦ ?_
        label := fun l hl ↦ ?_
        gap := fun l hl m h₁ h₂ ↦ ?_
        lt_end := by rw [hb'p]; omega
        far_end := by
          rw [hb'p]
          exact fun h ↦ hj₄ (hmono _ _ _ _ hj'₂ (by omega) le_rfl h) }
    all_goals
      rcases Nat.lt_or_ge l p with hlp | hlp
    · rw [hb' l hlp.le, ha' (l + 1) hlp]
      exact hc.b_le_a l hlp
    · obtain rfl : l = p := by omega
      rw [hb' _ le_rfl, ha'p]
      exact hi₁
    · rw [ha' (l + 1) hlp, hb' (l + 1) hlp]
      exact hc.a_lt_b l hlp
    · obtain rfl : l = p := by omega
      rw [ha'p, hb'p]
      exact hj'₁
    · rw [hb' l hlp.le, hb' (l + 1) hlp]
      exact hc.far l hlp
    · obtain rfl : l = p := by omega
      rw [hb' _ le_rfl, hb'p]
      exact hfar
    · rw [hb' l hlp.le, ha' (l + 1) hlp]
      exact hc.near l hlp
    · obtain rfl : l = p := by omega
      rw [hb' _ le_rfl, ha'p]
      exact hi₃
    · rw [hb' (l + 1) hlp]
      exact hc.label l hlp
    · obtain rfl : l = p := by omega
      rw [hb'p]
      exact hj'₃
    · rw [ha' (l + 1) hlp] at h₁
      rw [hb' (l + 1) hlp] at h₂
      exact hc.gap l hlp m h₁ h₂
    · obtain rfl : l = p := by omega
      rw [ha'p] at h₁
      rw [hb'p] at h₂
      exact hj'₄ m h₁ h₂
  · left
    push Not at h2
    obtain ⟨i, hi₁, hi₂, hi₃, hi₄⟩ := exists_largest hadjb hbk
    obtain ⟨i', hi'₁, hi'₂, hi'₃, hi'₄⟩ :=
      exists_least (Q := fun j ↦ N j (k + 1)) hi₂ (hself (k + 1) le_rfl)
    refine ⟨i, i', ⟨hi₁, hi'₁, hi'₂, hi₃, hi'₃, fun j hj₁ hj₂ hP ↦ ?_⟩⟩
    have hj : j < k + 1 := by omega
    exact h2 j (by omega) hj (hi₄ j hj₁ hj) (hi'₄ j hj₁ hj₂) hP

/-- A number between `lo 0` and `hi (p + 1)` in none of the intervals `[lo i, hi i]` lies in a gap
between two of them. -/
theorem exists_gap {lo hi : ℕ → ℕ} {p j : ℕ} (h0 : lo 0 ≤ j) (hlast : j ≤ hi (p + 1)) (hn : ∀ i
  ≤ p + 1, ¬ (lo i ≤ j ∧ j ≤ hi i)) :
    ∃ i ≤ p, hi i < j ∧ j < lo (i + 1) := by
  classical
  have hspec := Nat.findGreatest_spec (P := fun i ↦ lo i ≤ j) (m := 0) (n := p + 1)
    (Nat.zero_le _) h0
  have hle := Nat.findGreatest_le (P := fun i ↦ lo i ≤ j) (p + 1)
  set i := Nat.findGreatest (fun i ↦ lo i ≤ j) (p + 1) with hi'
  have hlt : hi i < j := by
    by_contra hc
    exact hn i hle ⟨hspec, not_lt.1 hc⟩
  have hip : i ≠ p + 1 := by
    rintro he
    rw [he] at hlt
    omega
  refine ⟨i, by omega, hlt, ?_⟩
  by_contra hc
  have := Nat.le_findGreatest (P := fun i ↦ lo i ≤ j) (m := i + 1) (n := p + 1) (by omega)
    (not_lt.1 hc)
  omega

/-- The conclusion of the sequence argument of (11.2). If there is no chain of length `m` and `0 ≪ k
+ 1`
holds, then some chain of length `p < m` ends with a last pair. -/
theorem exists_final (hmono : ∀ i j i' j', i ≤ i' → i' ≤ j' → j' ≤ j → N i j → N i' j')
    (hself : ∀ i ≤ k + 1, N i i) (hstart : ¬ N 0 (k + 1)) {m : ℕ} (hno : ∀ a b, ¬ SideChain N P k m
      a b) :
    ∃ p < m, ∃ a b, SideChain N P k p a b ∧ ∃ a' b', SideFinal N P k p (b p) a' b' := by
  have hind : ∀ q ≤ m, (∃ p < q, ∃ a b, SideChain N P k p a b ∧
      ∃ a' b', SideFinal N P k p (b p) a' b') ∨ ∃ a b, SideChain N P k q a b := by
    intro q
    induction q with
    | zero =>
      intro _
      refine Or.inr ⟨fun _ ↦ 0, fun _ ↦ 0, ?_⟩
      exact ⟨rfl, fun _ h ↦ absurd h (by omega), fun _ h ↦ absurd h (by omega),
        fun _ h ↦ absurd h (by omega), fun _ h ↦ absurd h (by omega), fun _ h ↦ absurd h (by omega),
        fun _ h ↦ absurd h (by omega), by omega, hstart⟩
    | succ q ih =>
      intro hq
      rcases ih (by omega) with ⟨p, hp, h⟩ | ⟨a, b, hc⟩
      · exact Or.inl ⟨p, by omega, h⟩
      · rcases exists_step hmono hself hc with hf | hc'
        · exact Or.inl ⟨q, by omega, a, b, hc, hf⟩
        · exact Or.inr hc'
  rcases hind m le_rfl with h | ⟨a, b, hc⟩
  · exact h
  · exact absurd hc (hno a b)

end GraphMinor.GM19
