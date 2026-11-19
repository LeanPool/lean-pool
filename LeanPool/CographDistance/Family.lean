/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/
module

public import LeanPool.CographDistance.Definitions

import Mathlib.Tactic.SplitIfs

/-!
# The family `G_m = K₁ ∨ (K₁ ∪ m K₂)`

Vertices: `none` is the dominating vertex `c`; `some none` is the isolated vertex `z` of
`K₁ ∪ m K₂`; `some (some (i, b))` is the end `b` of the `i`-th copy of `K₂`.
-/

@[expose] public section

namespace CographDist

/-- The vertex type of `G_m`. -/
abbrev W (m : ℕ) := Option (Option (Fin m × Bool))

/-- Adjacency in `G_m`. -/
def famAdj (m : ℕ) : W m → W m → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some none, some _ => False
  | some (some _), some none => False
  | some (some p), some (some q) => p.1 = q.1 ∧ p.2 ≠ q.2

/-- The graph `G_m = K₁ ∨ (K₁ ∪ m K₂)`. -/
def fam (m : ℕ) : SimpleGraph (W m) where
  Adj := famAdj m
  symm := ⟨by
    intro u v h
    rcases u with _ | _ | p <;> rcases v with _ | _ | q <;> simp_all [famAdj, eq_comm]⟩
  loopless := ⟨by
    intro u h
    rcases u with _ | _ | p <;> simp_all [famAdj]⟩

@[simp] theorem fam_adj_none_some (m : ℕ) (v : Option (Fin m × Bool)) :
    (fam m).Adj none (some v) := by
  simp [fam, famAdj]

@[simp] theorem fam_adj_some_none (m : ℕ) (v : Option (Fin m × Bool)) :
    (fam m).Adj (some v) none := by
  cases v <;> simp [fam, famAdj]

@[simp] theorem fam_not_adj_z (m : ℕ) (v : Option (Fin m × Bool)) :
    ¬ (fam m).Adj (some none) (some v) := by
  simp [fam, famAdj]

@[simp] theorem fam_not_adj_to_z (m : ℕ) (p : Fin m × Bool) :
    ¬ (fam m).Adj (some (some p)) (some none) := by
  simp [fam, famAdj]

@[simp] theorem fam_adj_pair (m : ℕ) (p q : Fin m × Bool) :
    (fam m).Adj (some (some p)) (some (some q)) ↔ p.1 = q.1 ∧ p.2 ≠ q.2 := by
  simp [fam, famAdj]

theorem fam_adj_center {m : ℕ} {v : W m} (hv : v ≠ none) : (fam m).Adj none v := by
  rcases v with _ | v
  · exact absurd rfl hv
  · simp

theorem fam_connected (m : ℕ) : (fam m).Connected := by
  have h : ∀ v : W m, (fam m).Reachable none v := by
    intro v
    rcases v with _ | v
    · exact SimpleGraph.Reachable.refl _
    · exact (fam_adj_none_some m v).reachable
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

open Classical in
/-- Distances in `G_m`: `0` on the diagonal, `1` on edges, `2` otherwise. -/
theorem fam_dist {m : ℕ} (u v : W m) :
    (fam m).dist u v = if u = v then 0 else if (fam m).Adj u v then 1 else 2 := by
  split_ifs with h1 h2
  · subst h1; simp
  · exact SimpleGraph.dist_eq_one_iff_adj.2 h2
  · have hu : u ≠ none := by
      rintro rfl; exact h2 (fam_adj_center (Ne.symm h1))
    have hv : v ≠ none := by
      rintro rfl; exact h2 ((fam_adj_center hu).symm)
    have hle : (fam m).dist u v ≤ 2 := by
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons (fam_adj_center hu).symm
          (SimpleGraph.Walk.cons (fam_adj_center hv) SimpleGraph.Walk.nil))
      simpa using this
    have h0 : (fam m).dist u v ≠ 0 := by
      intro h
      exact h1 (((fam_connected m).preconnected u v).dist_eq_zero_iff.1 h)
    have h1' : (fam m).dist u v ≠ 1 := by
      intro h
      exact h2 (SimpleGraph.dist_eq_one_iff_adj.1 h)
    omega

/-- `G_m` is a cograph. -/
theorem fam_isCograph (m : ℕ) : ¬(SimpleGraph.pathGraph 4).IsIndContained (fam m) := by
  rintro ⟨f⟩
  have e01 : (fam m).Adj (f 0) (f 1) := f.map_adj_iff.mpr (by simp [SimpleGraph.pathGraph_adj])
  have e12 : (fam m).Adj (f 1) (f 2) := f.map_adj_iff.mpr (by simp [SimpleGraph.pathGraph_adj])
  have n13 : ¬ (fam m).Adj (f 1) (f 3) := by
    intro h
    simpa [SimpleGraph.pathGraph_adj] using f.map_adj_iff.mp h
  have n02 : ¬ (fam m).Adj (f 0) (f 2) := by
    intro h
    simpa [SimpleGraph.pathGraph_adj] using f.map_adj_iff.mp h
  have d02 : f 0 ≠ f 2 := fun h => absurd (f.injective h) (by decide)
  have d13 : f 1 ≠ f 3 := fun h => absurd (f.injective h) (by decide)
  rcases h1 : f 1 with _ | _ | p
  · -- `f 1` is the dominating vertex: it is adjacent to `f 3`
    rw [h1] at n13 d13
    exact n13 (fam_adj_center (Ne.symm d13))
  · -- `f 1` is the isolated vertex `z`: both `f 0` and `f 2` must be the centre
    rw [h1] at e01 e12
    rcases h0 : f 0 with _ | v0
    · rcases h2 : f 2 with _ | v2
      · exact d02 (h0.trans h2.symm)
      · rw [h2] at e12; exact fam_not_adj_z m v2 e12
    · rw [h0] at e01; exact fam_not_adj_z m v0 e01.symm
  · rw [h1] at e01 e12
    rcases h0 : f 0 with _ | _ | q0
    · -- `f 0` is the centre, adjacent to `f 2`
      rw [h0] at n02 d02
      exact n02 (fam_adj_center (Ne.symm d02))
    · rw [h0] at e01; exact fam_not_adj_z m _ e01
    · rcases h2 : f 2 with _ | _ | q2
      · rw [h2] at n02 d02
        exact n02 (fam_adj_center d02).symm
      · rw [h2] at e12; exact fam_not_adj_to_z m p e12
      · rw [h0] at e01; rw [h2] at e12
        rw [fam_adj_pair] at e01 e12
        apply d02
        rw [h0, h2]
        obtain ⟨a0, b0⟩ := q0
        obtain ⟨a2, b2⟩ := q2
        obtain ⟨a1, b1⟩ := p
        simp only at e01 e12
        obtain ⟨rfl, hb0⟩ := e01
        obtain ⟨rfl, hb2⟩ := e12
        have : b0 = b2 := by
          cases b0 <;> cases b1 <;> cases b2 <;> simp_all
        rw [this]

end CographDist
