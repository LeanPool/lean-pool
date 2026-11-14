/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Tactic

/-!
# Existence of stable matchings

An inductive proof of the Gale–Shapley theorem. If no two men share the same favourite woman,
matching every man to his favourite is stable. Otherwise two men `m₁ ≠ m₂` share the favourite
`w`; if `w` prefers `m₁`, the pair `(m₂, w)` may be deleted: in a stable matching of the smaller
instance, `w` is matched to someone at least as good as `m₁` (because `m₁` cannot prefer anybody
to `w`), so the deleted pair is blocked.
-/

@[expose] public section

namespace Galvin

/-- `IsTop E r m w`: `w` is an acceptable partner of `m` of minimal rank. -/
def IsTop {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W) : Prop :=
  E m w ∧ ∀ w', E m w' → rm m w ≤ rm m w'

/-- The stable matching property. -/
def IsStable {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (rw : W → M → ℕ)
    (μ : M → W → Prop) : Prop :=
  (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m)

theorem exists_isTop {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W)
    (h : E m w) : ∃ w', IsTop E rm m w' := by
  classical
  have hex : ∃ k, ∃ w, E m w ∧ rm m w = k := ⟨_, w, h, rfl⟩
  obtain ⟨w', hw', hk⟩ := Nat.find_spec hex
  refine ⟨w', hw', fun v hv => ?_⟩
  rw [hk]
  exact Nat.find_min' hex ⟨v, hv, rfl⟩

theorem isStable_of_removal {M W : Type*} (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ)
    {m₁ m₂ : M} {w : W} (h₁ : IsTop E rm m₁ w) (hlt : rw w m₁ < rw w m₂)
    (μ : M → W → Prop)
    (hμ : IsStable (fun m v => E m v ∧ ¬ (m = m₂ ∧ v = w)) rm rw μ) (hne : m₁ ≠ m₂) :
    IsStable E rm rw μ := by
  obtain ⟨hsub, hm, hw, hst⟩ := hμ
  refine ⟨fun m v h => (hsub m v h).1, hm, hw, fun m v hE hnot => ?_⟩
  by_cases hrem : m = m₂ ∧ v = w
  · obtain ⟨rfl, rfl⟩ := hrem
    right
    by_cases hμ₁ : μ m₁ v
    · exact ⟨m₁, hμ₁, hlt⟩
    · rcases hst m₁ v ⟨h₁.1, fun h => hne h.1⟩ hμ₁ with ⟨w', hw', hr⟩ | ⟨m', hm', hr⟩
      · exact absurd (h₁.2 w' (hsub _ _ hw').1) (not_le.mpr hr)
      · exact ⟨m', hm', hr.trans hlt⟩
  · exact hst m v ⟨hE, hrem⟩ hnot

theorem exists_isStable {M W : Type*} [Finite M] [Finite W]
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∀ (n : ℕ) (E : M → W → Prop), {p : M × W | E p.1 p.2}.ncard = n →
      ∃ μ, IsStable E rm rw μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hn
  by_cases hsh : ∃ m₁ m₂ w, m₁ ≠ m₂ ∧ IsTop E rm m₁ w ∧ IsTop E rm m₂ w
  · obtain ⟨m₁, m₂, w, hne, h₁, h₂⟩ := hsh
    have key : ∀ a b : M, a ≠ b → IsTop E rm a w → IsTop E rm b w → rw w a < rw w b →
        ∃ μ, IsStable E rm rw μ := by
      intro a b hab ha hb hlt
      let E' : M → W → Prop := fun m v => E m v ∧ ¬ (m = b ∧ v = w)
      have hlt' : {p : M × W | E' p.1 p.2}.ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ (Set.toFinite _)
        refine ⟨fun p hp => hp.1, fun h => ?_⟩
        have := h (show (b, w) ∈ {p : M × W | E p.1 p.2} from hb.1)
        exact this.2 ⟨rfl, rfl⟩
      obtain ⟨μ, hμ⟩ := ih _ hlt' E' rfl
      exact ⟨μ, isStable_of_removal E rm rw ha hlt μ hμ hab⟩
    rcases lt_or_gt_of_ne (fun h => hne (hrw w h)) with h | h
    · exact key m₁ m₂ hne h₁ h₂ h
    · exact key m₂ m₁ (Ne.symm hne) h₂ h₁ h
  · push Not at hsh
    refine ⟨IsTop E rm, fun m w h => h.1, fun m w w' h h' => ?_, fun m m' w h h' => ?_,
      fun m w hE hnot => ?_⟩
    · exact hrm m (le_antisymm (h.2 _ h'.1) (h'.2 _ h.1))
    · by_contra hc
      exact hsh m m' w hc h h'
    · obtain ⟨w', hw'⟩ := exists_isTop E rm m w hE
      left
      refine ⟨w', hw', lt_of_le_of_ne (hw'.2 w hE) fun heq => ?_⟩
      rw [hrm m heq] at hw'
      exact hnot hw'

end Galvin
