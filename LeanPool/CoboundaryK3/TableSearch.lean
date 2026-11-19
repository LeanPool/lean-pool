/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley, Lean Pool contributors
-/
module

public import LeanPool.CoboundaryK3.Constant

/-!
# Table-driven branch-and-bound exhaustion of gauges

The exhaustions of `Basic` evaluate permutation products in the kernel at every node of the
search tree. This file gives a cheaper certificate for the same statements. A gauge is a list of
indices into `S3list`, and a cochain is replaced by a table of natural numbers: `tcost T u v i j`
is the moved count of the edge `u < v` when `u` carries `el i` and `v` carries `el j`. The table
is checked against the cochain once (`TableSpec`), and then the search only adds table entries.
The search also carries the cost of the assigned edges along, adding only the edges into the
newly assigned vertex.

* `tsearch_sound`: once the carried cost reaches `D`, every completion costs at least `D`;
* `tpcost_ofFn`: on a complete gauge the table cost is the cost of the cochain;
* `gauge_lower_table`: a successful search from `[0]` (the identity on vertex `0`) bounds every
  gauge from below.

This file was added in the Lean Pool port to keep each exhaustion within the per-file
compilation budget; the statements it proves are those of the upstream exhaustions.
-/

@[expose] public section

namespace CoboundaryK3

open Finset

/-- The element of `S3list` at position `i` (the identity past the end). -/
def el (i : ℕ) : S3 := S3list.getD i 1

/-- The position of `σ` in `S3list`. -/
def idx (σ : S3) : ℕ := S3list.idxOf σ

theorem el_idx : ∀ σ : S3, el (idx σ) = σ := by decide

theorem idx_lt : ∀ σ : S3, idx σ < 6 := by decide

theorem idx_one : idx 1 = 0 := by decide

/-- A cost table, read at row `v`, column `u` and entry `6 i + j`. -/
def tcost (T : List (List (List ℕ))) (u v i j : ℕ) : ℕ :=
  ((T.getD v []).getD u []).getD (6 * i + j) 0

/-- The table cost of the edges both of whose endpoints are assigned by the index list `g`. -/
def tpcost (T : List (List (List ℕ))) (g : List ℕ) : ℕ :=
  ∑ v ∈ range g.length, ∑ u ∈ range v, tcost T u v (g.getD u 0) (g.getD v 0)

/-- The table cost of the edges from the vertices assigned by `g` into the next vertex, when it
carries the index `a`. -/
def tinc (T : List (List (List ℕ))) (g : List ℕ) (a : ℕ) : ℕ :=
  ((List.range g.length).map fun u => tcost T u g.length (g.getD u 0) a).sum

/-- The table search: `true` means every completion of `g` by `fuel` more indices below `6` has
table cost at least `D`, where `acc` is the table cost of `g`. -/
def tsearch (T : List (List (List ℕ))) (D : ℕ) : ℕ → List ℕ → ℕ → Bool
  | 0, _, acc => decide (D ≤ acc)
  | f + 1, g, acc => decide (D ≤ acc) ||
      (List.range 6).all fun a => tsearch T D f (g ++ [a]) (acc + tinc T g a)

theorem sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ u ∈ range n, f u := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem tpcost_snoc (T : List (List (List ℕ))) (g : List ℕ) (a : ℕ) :
    tpcost T (g ++ [a]) = tpcost T g + tinc T g a := by
  have hl : (g ++ [a]).length = g.length + 1 := by simp
  have hg : ∀ u, u < g.length → (g ++ [a]).getD u 0 = g.getD u 0 := fun u hu =>
    List.getD_append _ _ _ _ hu
  have ha : (g ++ [a]).getD g.length 0 = a := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  unfold tpcost
  rw [hl, sum_range_succ, ha, tinc, sum_map_range]
  congr 1
  · refine sum_congr rfl fun v hv => sum_congr rfl fun u hu => ?_
    have hv' := mem_range.mp hv
    have hu' := mem_range.mp hu
    rw [hg v hv', hg u (hu'.trans hv')]
  · exact sum_congr rfl fun u hu => by rw [hg u (mem_range.mp hu)]

theorem tpcost_mono (T : List (List (List ℕ))) :
    ∀ (ext g : List ℕ), tpcost T g ≤ tpcost T (g ++ ext)
  | [], g => by simp
  | x :: ext, g => by
    have h := tpcost_mono T ext (g ++ [x])
    rw [List.append_assoc, List.singleton_append, tpcost_snoc] at h
    exact (Nat.le_add_right _ _).trans h

theorem tsearch_sound (T : List (List (List ℕ))) (D : ℕ) :
    ∀ (fuel : ℕ) (g : List ℕ), tsearch T D fuel g (tpcost T g) = true →
      ∀ ext : List ℕ, ext.length = fuel → (∀ x ∈ ext, x < 6) → D ≤ tpcost T (g ++ ext)
  | 0, g, h, ext, hl, _ => by
    rw [List.length_eq_zero_iff.mp hl, List.append_nil]
    simpa [tsearch] using h
  | f + 1, g, h, ext, hl, hx => by
    simp only [tsearch, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at h
    rcases h with h | h
    · exact h.trans (tpcost_mono T ext g)
    · obtain ⟨a, ext', rfl⟩ : ∃ a ext', ext = a :: ext' := by
        cases ext with
        | nil => simp at hl
        | cons a t => exact ⟨a, t, rfl⟩
      have ha : a < 6 := hx a (by simp)
      have hrec := h a ha
      rw [← tpcost_snoc] at hrec
      have := tsearch_sound T D f (g ++ [a]) hrec ext' (by simpa using hl)
        fun x hx' => hx x (by simp [hx'])
      simpa using this

/-- The table `T` records the moved counts of the cochain `α`. -/
def TableSpec {k : ℕ} (T : List (List (List ℕ))) (α : Fin k → Fin k → S3) : Prop :=
  ∀ u v : Fin k, u < v → ∀ i < 6, ∀ j < 6, tcost T u v i j = moved ((el i)⁻¹ * α u v * el j)

instance {k : ℕ} (T : List (List (List ℕ))) (α : Fin k → Fin k → S3) :
    Decidable (TableSpec T α) := by
  unfold TableSpec
  infer_instance

theorem sum_range_fin {k : ℕ} (F : Fin k → ℕ) (f : ℕ → ℕ) (hf : ∀ v : Fin k, f v = F v) :
    ∑ v ∈ range k, f v = ∑ v : Fin k, F v := by
  rw [sum_range]
  exact sum_congr rfl fun v _ => hf v

theorem sum_range_lt {k : ℕ} (v : Fin k) (F : Fin k → ℕ) (f : ℕ → ℕ)
    (hf : ∀ u : Fin k, u < v → f u = F u) :
    ∑ u ∈ range v, f u = ∑ u : Fin k, if u < v then F u else 0 := by
  have hr : range (v : ℕ) = (range k).filter (· < (v : ℕ)) := by
    ext u
    simp only [mem_range, mem_filter]
    omega
  rw [hr, sum_filter, sum_range]
  refine sum_congr rfl fun u _ => ?_
  by_cases h : u < v
  · rw [ite_eq_left (Fin.lt_def.mp h), ite_eq_left h, hf u h]
  · rw [ite_eq_right (fun h' => h (Fin.lt_def.mpr h')), ite_eq_right h]

/-- On a complete gauge, the table cost is the cost of the cochain. -/
theorem tpcost_ofFn {k : ℕ} {T : List (List (List ℕ))} {α : Fin k → Fin k → S3}
    (hT : TableSpec T α) (β : Fin k → S3) :
    tpcost T (List.ofFn fun v => idx (β v)) = cost α β := by
  have hg : ∀ v : Fin k, (List.ofFn fun v => idx (β v)).getD v 0 = idx (β v) := fun v => by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]
  rw [cost_eq_sum, sum_comm, tpcost, List.length_ofFn]
  refine sum_range_fin _ _ fun v => ?_
  refine sum_range_lt v _ _ fun u huv => ?_
  rw [hg u, hg v, hT u v huv _ (idx_lt _) _ (idx_lt _), el_idx, el_idx]

/-- **Exhaustion loses nothing**, table form. A successful table search from the identity on
vertex `0` bounds the cost of every gauge from below. -/
theorem gauge_lower_table {m : ℕ} {α : Fin (m + 1) → Fin (m + 1) → S3} {T : List (List (List ℕ))}
    (hT : TableSpec T α) (D : ℕ) (h : tsearch T D m [0] 0 = true) : ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have h1 : tpcost T [0] = 0 := by simp [tpcost]
  rw [← h1] at h
  have := tsearch_sound T D m [0] h (List.ofFn fun i : Fin m => idx (β' i.succ)) (by simp)
    (by simp [idx_lt])
  rw [← tpcost_ofFn hT]
  have e : (List.ofFn fun v => idx (β' v)) = [0] ++ List.ofFn fun i : Fin m => idx (β' i.succ) := by
    rw [List.ofFn_succ, h0, idx_one]
    rfl
  rw [e]
  exact this

theorem tsearch_split (T : List (List (List ℕ))) (D f : ℕ) (g : List ℕ) (acc : ℕ)
    (h : ∀ a < 6, tsearch T D f (g ++ [a]) (acc + tinc T g a) = true) :
    tsearch T D (f + 1) g acc = true := by
  simp only [tsearch, Bool.or_eq_true, List.all_eq_true, List.mem_range]
  exact Or.inr h

/-- Assemble a table search from its six children, one for each index of the next vertex. -/
theorem tsearch_split6 (T : List (List (List ℕ))) (D f : ℕ) (g : List ℕ) (acc : ℕ)
    (h0 : tsearch T D f (g ++ [0]) (acc + tinc T g 0) = true)
    (h1 : tsearch T D f (g ++ [1]) (acc + tinc T g 1) = true)
    (h2 : tsearch T D f (g ++ [2]) (acc + tinc T g 2) = true)
    (h3 : tsearch T D f (g ++ [3]) (acc + tinc T g 3) = true)
    (h4 : tsearch T D f (g ++ [4]) (acc + tinc T g 4) = true)
    (h5 : tsearch T D f (g ++ [5]) (acc + tinc T g 5) = true) :
    tsearch T D (f + 1) g acc = true :=
  tsearch_split T D f g acc fun a ha =>
    match a, ha with
    | 0, _ => h0
    | 1, _ => h1
    | 2, _ => h2
    | 3, _ => h3
    | 4, _ => h4
    | 5, _ => h5
    | n + 6, h => absurd h (by omega)

end CoboundaryK3
