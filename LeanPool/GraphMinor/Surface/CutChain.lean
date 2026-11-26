/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CutGraph

/-!
# Arcs in a graph are chains of edges

An arc or an `O`-arc inside the union of the edges of a graph is a chain of edges (`exists_chain`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

local notation "𝕀" => unitInterval

variable {X : Type u} [TopologicalSpace X] [T2Space X] {V : Set X} {E : Set (Set X)}

/-- A path that is injective, or a loop, in the union of the edges of a graph runs through a chain
of edges. -/
theorem exists_chain (hg : IsGraph V E) (A : Set X → 𝕀 → X)
    (hA : ∀ e ∈ E, IsArcMap (A e) ∧ range (A e) = e ∧ e ∩ V = {A e 0, A e 1}) {ι : ℝ → X}
      (hιc : Continuous ι)
    (hinj : InjOn ι (Ico 0 1)) (hinj' : InjOn ι (Ioc 0 1)) (hG : ι '' Icc 0 1 ⊆ gr V E)
      (h0 : ι 0 ∈ V) (h1 : ι 1 ∈ V)
    (hne : ι 0 ≠ ι 1 ∨ ∃ x ∈ Ioo (0 : ℝ) 1, ι x ∈ V) :
    ∃ (m : ℕ) (t : ℕ → ℝ) (s : ℕ → Set X) (ε : ℕ → Bool), 0 < m ∧ t 0 = 0 ∧ t m = 1 ∧
      (∀ p < m, t p < t (p + 1)) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ι x ∈ V → ∃ p ≤ m, x = t p) ∧
      (∀ p < m, s p ∈ E ∧ ι '' Icc (t p) (t (p + 1)) = s p ∧ ι (t p) = extI (A (s p))
        (if ε p then 0 else 1) ∧
        ι (t (p + 1)) = extI (A (s p)) (if ε p then 1 else 0)) ∧
      ∀ p < m, ∀ q < m, p ≠ q → s p ≠ s q := by
  obtain ⟨m, t, s, ε, hm, ht0, htm, hlt, hmem, hall, hs⟩ :=
    hg.exists_edge_intervals A hA hιc hinj hinj' hG h0 h1 hne
  refine ⟨m, t, s, ε, hm, ht0, htm, hlt, ?_, hs, ?_⟩
  · intro x hx hxV
    obtain ⟨p, hp, e⟩ := hall x ⟨hx, hxV⟩
    exact ⟨p, hp, e.symm⟩
  · have hmono : ∀ p q, p + 1 ≤ q → q ≤ m → t (p + 1) ≤ t q := by
      intro p q hpq hq
      induction q, hpq using Nat.le_induction with
      | base => exact le_rfl
      | succ q hq' ih => exact (ih (by omega)).trans (hlt q (by omega)).le
    have key2 : ∀ p < m, ∀ q < m, p < q → s p ≠ s q := by
      intro p hp q hq hpq he
      have hab := hlt p hp
      have ha1 := hmem p hp.le
      have hb1 := hmem (p + 1) hp
      obtain ⟨x, hx⟩ : (Ioo (t p) (t (p + 1))).Nonempty := nonempty_Ioo.mpr hab
      have h1 : ι x ∈ s q := by
        rw [← he, ← (hs p hp).2.1]
        exact mem_image_of_mem ι ⟨hx.1.le, hx.2.le⟩
      rw [← (hs q hq).2.1] at h1
      obtain ⟨y, hy, hxy⟩ := h1
      have hxy2 : x < y := hx.2.trans_le ((hmono p q hpq hq.le).trans hy.1)
      have hx0 : 0 < x := ha1.1.1.trans_lt hx.1
      have hy1 : y ≤ 1 := hy.2.trans (hmem _ hq).1.2
      exact hxy2.ne (hinj' ⟨hx0, hx.2.le.trans hb1.1.2⟩ ⟨hx0.trans hxy2, hy1⟩ hxy.symm)
    intro p hp q hq hpq
    rcases lt_or_gt_of_ne hpq with h | h
    · exact key2 p hp q hq h
    · exact (key2 q hq p hp h).symm

end GraphMinor.Surface
