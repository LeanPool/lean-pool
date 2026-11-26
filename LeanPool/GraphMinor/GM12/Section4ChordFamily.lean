/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ChordAvoidance

/-!
# A finite family of chords in general position

For XII (4.5), page 253, prescribe an open circle arc for each end
of each chord. Add the chords one at a time, excluding old crossing
points. Their supporting lines are distinct, and no three of them
meet. The intervals for the ends can be made disjoint when choosing
the ports of the graph drawing.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem exists_castSucc_of_ne_last {n : ℕ} (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) : ∃ j : Fin n, j.castSucc = i := by
  refine Fin.lastCases ?_ (fun j => ?_) i hi
  · intro h
    exact (h rfl).elim
  · intro _
    exact ⟨j, rfl⟩

/-- The finite chord selection used for the crossing drawing of
XII (4.5), page 253. Ends lie in their prescribed arcs, supporting
lines are distinct, and three distinct supporting lines never meet. -/
theorem exists_chord_family_in_arcs (n : ℕ)
    (u v w z : Fin n → ℝ) (huv : ∀ i, u i < v i) (hlen : ∀ i, v i ≤ u i + 1)
    (hwz : ∀ i, w i < z i) (hlen' : ∀ i, z i ≤ w i + 1) :
    ∃ s t : Fin n → ℝ,
      (∀ i, s i ∈ Ioo (u i) (v i) ∧ t i ∈ Ioo (w i) (z i) ∧
        (ee (s i) : ℂ) ≠ (ee (t i) : ℂ)) ∧
      (∀ i j, i ≠ j → line[ℝ, (ee (s i) : ℂ), (ee (t i) : ℂ)] ≠
        line[ℝ, (ee (s j) : ℂ), (ee (t j) : ℂ)]) ∧
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x : ℂ,
        ¬ (x ∈ line[ℝ, (ee (s i) : ℂ), (ee (t i) : ℂ)] ∧
          x ∈ line[ℝ, (ee (s j) : ℂ), (ee (t j) : ℂ)] ∧
          x ∈ line[ℝ, (ee (s k) : ℂ), (ee (t k) : ℂ)]) := by
  classical
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨s, t, hst, hne, hthree⟩ := ih
      (fun i => u i.castSucc) (fun i => v i.castSucc)
      (fun i => w i.castSucc) (fun i => z i.castSucc)
      (fun i => huv i.castSucc) (fun i => hlen i.castSucc)
      (fun i => hwz i.castSucc) (fun i => hlen' i.castSucc)
    obtain ⟨s₀, hs₀, t₀, ht₀, hst₀, hnew, _, hcross⟩ :=
      exists_chord_avoiding_old_crossings
        (fun i => (ee (s i) : ℂ)) (fun i => (ee (t i) : ℂ))
        (by intro i; simp) hne (huv (Fin.last n)) (hlen (Fin.last n))
        (hwz (Fin.last n)) (hlen' (Fin.last n))
    refine ⟨Fin.snoc s s₀, Fin.snoc t t₀, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using And.intro hs₀ (And.intro ht₀ hst₀)
      · simpa using hst j
    · intro i j hij
      by_cases hi : i = Fin.last n
      · subst i
        obtain ⟨j, rfl⟩ := exists_castSucc_of_ne_last j hij.symm
        simpa using hnew j
      · obtain ⟨i, rfl⟩ := exists_castSucc_of_ne_last i hi
        by_cases hj : j = Fin.last n
        · subst j
          simpa using (hnew i).symm
        · obtain ⟨j, rfl⟩ := exists_castSucc_of_ne_last j hj
          simpa using hne i j (fun h => hij (congrArg Fin.castSucc h))
    · intro i j k hij hjk hik x hx
      by_cases hi : i = Fin.last n
      · subst i
        obtain ⟨j, rfl⟩ := exists_castSucc_of_ne_last j hij.symm
        obtain ⟨k, rfl⟩ := exists_castSucc_of_ne_last k hik.symm
        have h := hcross j k (fun h => hjk (congrArg Fin.castSucc h))
        exact Set.disjoint_left.mp h (by simpa using hx.1)
          ⟨by simpa using hx.2.1, by simpa using hx.2.2⟩
      · obtain ⟨i, rfl⟩ := exists_castSucc_of_ne_last i hi
        by_cases hj : j = Fin.last n
        · subst j
          obtain ⟨k, rfl⟩ := exists_castSucc_of_ne_last k hjk.symm
          have h := hcross i k (fun h => hik (congrArg Fin.castSucc h))
          exact Set.disjoint_left.mp h (by simpa using hx.2.1)
            ⟨by simpa using hx.1, by simpa using hx.2.2⟩
        · obtain ⟨j, rfl⟩ := exists_castSucc_of_ne_last j hj
          by_cases hk : k = Fin.last n
          · subst k
            have h := hcross i j (fun h => hij (congrArg Fin.castSucc h))
            exact Set.disjoint_left.mp h (by simpa using hx.2.2)
              ⟨by simpa using hx.1, by simpa using hx.2.1⟩
          · obtain ⟨k, rfl⟩ := exists_castSucc_of_ne_last k hk
            apply hthree i j k
              (fun h => hij (congrArg Fin.castSucc h))
              (fun h => hjk (congrArg Fin.castSucc h))
              (fun h => hik (congrArg Fin.castSucc h)) x
            simpa using hx

end GraphMinor.GM12
