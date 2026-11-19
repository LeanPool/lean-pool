/-
Copyright (c) 2026 Horace Dong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Horace Dong
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Metric

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

/-- Each matching endpoint is adjacent to exactly one other matching endpoint. -/
theorem fam_adj_pair_iff_eq_mate {m : ℕ} (p q : Fin m × Bool) :
    (fam m).Adj (some (some p)) (some (some q)) ↔ q = (p.1, !p.2) := by
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, c⟩
  cases b <;> cases c <;> simp [eq_comm]

private theorem eq_of_adj_of_ne_center {m : ℕ} {u v w : W m}
    (hu : u ≠ none) (hw : w ≠ none) (huv : (fam m).Adj u v) (hvw : (fam m).Adj v w)
    (hv : v ≠ none) : u = w := by
  rcases u with _ | u
  · exact (hu rfl).elim
  rcases w with _ | w
  · exact (hw rfl).elim
  rcases v with _ | _ | p
  · exact (hv rfl).elim
  · exact (fam_not_adj_z m w hvw).elim
  rcases u with _ | q
  · exact (fam_not_adj_z m _ huv).elim
  rcases w with _ | r
  · exact (fam_not_adj_to_z m p hvw).elim
  exact congrArg (fun z => some (some z))
    (((fam_adj_pair_iff_eq_mate p q).1 huv.symm).trans
      ((fam_adj_pair_iff_eq_mate p r).1 hvw).symm)

theorem fam_adj_center {m : ℕ} {v : W m} (hv : v ≠ none) : (fam m).Adj none v := by
  rcases v with _ | v
  · exact absurd rfl hv
  · simp

private theorem ne_center_of_not_adj {m : ℕ} {u v : W m}
    (hne : u ≠ v) (hn : ¬ (fam m).Adj u v) : u ≠ none := by
  rintro rfl
  exact hn (fam_adj_center hne.symm)

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
  · have hu := ne_center_of_not_adj h1 h2
    have hv := ne_center_of_not_adj (Ne.symm h1) (fun h => h2 h.symm)
    have hdist : (fam m).edist u v = 2 := SimpleGraph.edist_eq_two_iff.mpr
      ⟨h1, h2, ⟨none, (fam_adj_center hu).symm, (fam_adj_center hv).symm⟩⟩
    exact congrArg ENat.toNat hdist

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
  have h0 := ne_center_of_not_adj d02 n02
  have h1 := ne_center_of_not_adj d13 n13
  have h2 := ne_center_of_not_adj d02.symm (fun h => n02 h.symm)
  exact d02 (eq_of_adj_of_ne_center h0 h2 e01 e12 h1)

end CographDist
