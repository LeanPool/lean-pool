/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD

/-!
The permutation coboundary constant of the complete complex is k/3 for 4 ≤ k ≤ 8
(Jeromie Beasley, DOI 10.5281/zenodo.22090958): the machine-checked witnesses.

Conventions follow the paper (Section 1). Permutations of `{0,1,2}` act on points;
the Hamming count `moved σ` is the number of points `σ` moves. A 1-cochain on the complete
complex `K_k` assigns `α u v` to each edge `u < v`, with `α(v,u) = α(u,v)⁻¹`. Its triangle
defect is `N = Σ_{u<v<w} moved(α(u,v) α(v,w) α(w,u))` and the cost of a gauge
`β : Fin k → Sym(3)` is `Σ_{u<v} moved(β(u)⁻¹ α(u,v) β(v))`; `D` is the minimum cost over every
gauge. Both are counts of moved points, so `N/D` is the paper's counting ratio.

This file proves, for each witness of Appendix A, the defect `N`, that no gauge costs less than
`D`, and that `D` is attained, so that `N/D = k/3`: the upper half of Theorem 4. The lower half,
the paper's Proposition 1 (Chapman–Lubotzky's Proposition 3.2), is proved in `Constant.lean`.

The gauge minimum is checked by exhausting every gauge with `β(0) = 1`; `gauge_lower` proves that
this loses nothing, because right multiplication by a constant conjugates every edge term.
-/

@[expose] public section

namespace CoboundaryK3

open Equiv

/-- Permutations of three points. -/
abbrev S3 := Perm (Fin 3)

/-- The Hamming count: how many of the three points `σ` moves. -/
def moved (σ : S3) : ℕ := (List.finRange 3).countP fun i => σ i ≠ i

/-- The two transpositions and 3-cycles, in the paper's one-line notation. -/
def t01 : S3 := swap 0 1          -- (1 0 2)
def t12 : S3 := swap 1 2          -- (0 2 1)
def t02 : S3 := swap 0 2          -- (2 1 0)
def c1 : S3 := swap 0 1 * swap 1 2  -- (1 2 0)
def c2 : S3 := swap 1 2 * swap 0 1  -- (2 0 1)

/-- The six elements of `Sym(3)`. -/
def S3list : List S3 := [1, t01, t12, t02, c1, c2]

theorem mem_S3list : ∀ σ : S3, σ ∈ S3list := by decide

theorem one_line : (c1 0, c1 1, c1 2) = (1, 2, 0) ∧ (c2 0, c2 1, c2 2) = (2, 0, 1) ∧
    (t01 0, t01 1, t01 2) = (1, 0, 2) ∧ (t12 0, t12 1, t12 2) = (0, 2, 1) ∧
    (t02 0, t02 1, t02 2) = (2, 1, 0) := by decide

/-- The Hamming count is conjugation invariant (bi-invariance of the metric). -/
theorem moved_conj : ∀ c x : S3, moved (c⁻¹ * x * c) = moved x := by
  intro c x
  have hc := mem_S3list c
  have hx := mem_S3list x
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at hc hx
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Cochains on the complete complex -/

variable {k : ℕ}

/-- Oriented edges `u < v`. -/
def edges (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => ((List.finRange k).filter fun v => u < v).map fun v => (u, v)

/-- Triangles `u < v < w`. -/
def triangles (k : ℕ) : List (Fin k × Fin k × Fin k) :=
  (List.finRange k).flatMap fun u => (List.finRange k).flatMap fun v =>
    ((List.finRange k).filter fun w => u < v ∧ v < w).map fun w => (u, v, w)

/-- The value on an oriented edge, with `α(v,u) = α(u,v)⁻¹`. -/
def val (α : Fin k → Fin k → S3) (u v : Fin k) : S3 := if u < v then α u v else (α v u)⁻¹

/-- The triangle defect `N`: moved points of the holonomy, summed over triangles. -/
def defect (α : Fin k → Fin k → S3) : ℕ :=
  ((triangles k).map fun t => moved (val α t.1 t.2.1 * val α t.2.1 t.2.2 * val α t.2.2 t.1)).sum

/-- The cost of a gauge `β`: moved points of `β(u)⁻¹ α(u,v) β(v)`, summed over edges. -/
def cost (α : Fin k → Fin k → S3) (β : Fin k → S3) : ℕ :=
  ((edges k).map fun e => moved ((β e.1)⁻¹ * α e.1 e.2 * β e.2)).sum

/-- A constant right factor does not change the cost. -/
theorem cost_mul_const (α : Fin k → Fin k → S3) (β : Fin k → S3) (c : S3) :
    cost α (fun v => β v * c) = cost α β := by
  unfold cost
  congr 1
  apply List.map_congr_left
  intro e _
  have : (β e.1 * c)⁻¹ * α e.1 e.2 * (β e.2 * c) = c⁻¹ * ((β e.1)⁻¹ * α e.1 e.2 * β e.2) * c := by
    group
  rw [this, moved_conj]

/-- Every function `Fin n → Sym(3)`, as a list. -/
def funs : (n : ℕ) → List (Fin n → S3)
  | 0 => [Fin.elim0]
  | n + 1 => S3list.flatMap fun a => (funs n).map (Fin.cons a)

theorem mem_funs : ∀ (n : ℕ) (f : Fin n → S3), f ∈ funs n
  | 0, f => by simp [funs]; funext i; exact i.elim0
  | n + 1, f => by
    simp only [funs, List.mem_flatMap, List.mem_map]
    exact ⟨f 0, mem_S3list _, Fin.tail f, mem_funs n _, Fin.cons_self_tail f⟩

/-- **Exhaustion loses nothing.** If every gauge with `β(0) = 1` costs at least `D`, every
gauge does. -/
theorem gauge_lower {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : (funs m).all (fun t => decide (D ≤ cost α (Fin.cons 1 t))) = true) :
    ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have hcons : β' = Fin.cons 1 (Fin.tail β') := by
    rw [← h0]; exact (Fin.cons_self_tail β').symm
  rw [hcons]
  have := List.all_eq_true.mp h (Fin.tail β') (mem_funs m _)
  simpa using this


/-- Check a Boolean test on every function `Fin n → Sym(3)` without building the list. -/
def allG : (n : ℕ) → ((Fin n → S3) → Bool) → Bool
  | 0, p => p Fin.elim0
  | n + 1, p => S3list.all fun a => allG n (fun t => p (Fin.cons a t))

theorem allG_sound : ∀ (n : ℕ) (p : (Fin n → S3) → Bool), allG n p = true → ∀ f, p f = true
  | 0, p, h, f => by
    have : f = Fin.elim0 := funext fun i => i.elim0
    rw [this]; exact h
  | n + 1, p, h, f => by
    simp only [allG, List.all_eq_true] at h
    have := allG_sound n _ (h (f 0) (mem_S3list _)) (Fin.tail f)
    simpa [Fin.cons_self_tail] using this

/-- **Exhaustion loses nothing**, streamed form. -/
theorem gauge_lower' {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : allG m (fun t => decide (D ≤ cost α (Fin.cons 1 t))) = true) :
    ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have hcons : β' = Fin.cons 1 (Fin.tail β') := by
    rw [← h0]; exact (Fin.cons_self_tail β').symm
  rw [hcons]
  have := allG_sound m _ h (Fin.tail β')
  simpa using this


/-! ### Branch-and-bound exhaustion

Assign the gauge one vertex at a time. The cost of the edges whose endpoints are both assigned
can only grow as more vertices are assigned, so once it reaches `D` every completion costs at
least `D` and the branch is closed. `search_sound` proves this pruning loses nothing. -/

section Search

variable {k : ℕ} (α : Fin k → Fin k → S3)

/-- The term of edge `e` under a partial gauge `l` (vertex `v` gets `l[v]`). -/
def term (l : List S3) (e : Fin k × Fin k) : ℕ :=
  moved ((l.getD e.1 1)⁻¹ * α e.1 e.2 * l.getD e.2 1)

/-- The cost of the edges both of whose endpoints are assigned. -/
def pcost (l : List S3) : ℕ :=
  ((edges k).map fun e => if e.2.val < l.length then term α l e else 0).sum

theorem mem_edges {e : Fin k × Fin k} (h : e ∈ edges k) : e.1 < e.2 := by
  simp only [edges, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨u, _, v, ⟨_, huv⟩, rfl⟩ := h
  exact huv

theorem sum_map_le {ι : Type*} (l : List ι) (f g : ι → ℕ) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem pcost_mono (l ext : List S3) : pcost α l ≤ pcost α (l ++ ext) := by
  apply sum_map_le
  intro e he
  have h12 := mem_edges he
  split_ifs with h1 h2 h2
  · have h1' : e.1.val < l.length := lt_trans h12 h1
    simp only [term, List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1']
    exact le_refl _
  · exact absurd (by simp; omega) h2
  · exact Nat.zero_le _
  · exact le_refl _

/-- The branch-and-bound search: `true` means every completion of `l` by `fuel` more vertices
costs at least `D`. -/
def search (D : ℕ) : ℕ → List S3 → Bool
  | 0, l => decide (D ≤ pcost α l)
  | f + 1, l => decide (D ≤ pcost α l) || S3list.all fun a => search D f (l ++ [a])

theorem search_sound (D : ℕ) : ∀ (fuel : ℕ) (l : List S3), search α D fuel l = true →
    ∀ ext : List S3, ext.length = fuel → D ≤ pcost α (l ++ ext)
  | 0, l, h, ext, hl => by
    rw [List.length_eq_zero_iff.mp hl, List.append_nil]
    simpa [search] using h
  | f + 1, l, h, ext, hl => by
    simp only [search, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    rcases h with h | h
    · exact h.trans (pcost_mono α l ext)
    · obtain ⟨a, ext', rfl⟩ : ∃ a ext', ext = a :: ext' := by
        cases ext with
        | nil => simp at hl
        | cons a t => exact ⟨a, t, rfl⟩
      have := search_sound D f (l ++ [a]) (h a (mem_S3list a)) ext' (by simpa using hl)
      simpa using this

theorem search_step (D f : ℕ) (l : List S3)
    (h : ∀ a ∈ S3list, search α D f (l ++ [a]) = true) : search α D (f + 1) l = true := by
  simp only [search, Bool.or_eq_true, List.all_eq_true]
  exact Or.inr h

theorem search_split (D f : ℕ) (l : List S3)
    (h1 : search α D f (l ++ [1]) = true) (h2 : search α D f (l ++ [t01]) = true)
    (h3 : search α D f (l ++ [t12]) = true) (h4 : search α D f (l ++ [t02]) = true)
    (h5 : search α D f (l ++ [c1]) = true) (h6 : search α D f (l ++ [c2]) = true) :
    search α D (f + 1) l = true := by
  apply search_step
  intro a ha
  simp only [S3list, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem pcost_ofFn {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (β : Fin (m + 1) → S3) :
    pcost α (List.ofFn β) = cost α β := by
  have hg : ∀ i : Fin (m + 1), (List.ofFn β).getD i 1 = β i := fun i => by
    rw [List.getD_eq_getElem _ _ (by simp; exact Nat.lt_succ_iff.mp i.isLt), List.getElem_ofFn]
  unfold pcost cost
  congr 1
  apply List.map_congr_left
  intro e _
  rw [ite_cond_eq_true _ _ (eq_true (by rw [List.length_ofFn]; exact e.2.isLt))]
  simp only [term, hg]

/-- **Exhaustion loses nothing**, branch-and-bound form. -/
theorem gauge_lower_bb {m : ℕ} (α : Fin (m + 1) → Fin (m + 1) → S3) (D : ℕ)
    (h : search α D m [1] = true) : ∀ β, D ≤ cost α β := by
  intro β
  rw [← cost_mul_const α β (β 0)⁻¹]
  set β' : Fin (m + 1) → S3 := fun v => β v * (β 0)⁻¹ with hβ'
  have h0 : β' 0 = 1 := by simp [hβ']
  have := search_sound α D m [1] h (List.ofFn fun i : Fin m => β' i.succ) (by simp)
  rw [← pcost_ofFn]
  have e : List.ofFn β' = [1] ++ List.ofFn fun i : Fin m => β' i.succ := by
    rw [List.ofFn_succ, h0]; rfl
  rw [e]
  exact this

end Search

/-- A cochain from its list of non-identity edges. -/
def cochain (k : ℕ) (W : List ((ℕ × ℕ) × S3)) : Fin k → Fin k → S3 :=
  fun u v => ((W.lookup (u.val, v.val)).getD 1)

/-! ## The witnesses of Appendix A (gauged form) -/

def w4 : Fin 4 → Fin 4 → S3 := cochain 4 [((1, 2), t12), ((1, 3), t01), ((2, 3), t02)]

def w5 : Fin 5 → Fin 5 → S3 := cochain 5 [((0, 1), t01), ((1, 2), t01), ((2, 3), t01)]

def w6 : Fin 6 → Fin 6 → S3 :=
  cochain 6 [((0, 1), c1), ((1, 3), c1), ((0, 3), c2), ((0, 4), c2), ((1, 5), c2), ((4, 5), c2)]

def w7 : Fin 7 → Fin 7 → S3 :=
  cochain 7 [((0, 1), t01), ((0, 3), t01), ((0, 4), t01), ((1, 2), t01), ((1, 5), t01),
    ((2, 3), t01)]

def w8 : Fin 8 → Fin 8 → S3 :=
  cochain 8 [((0, 1), t12), ((0, 7), t12), ((1, 2), t12), ((2, 5), t12), ((2, 7), t12),
    ((1, 3), t01), ((1, 4), t01), ((1, 6), t01), ((3, 7), t01),
    ((0, 4), t02), ((2, 3), t02), ((2, 4), t02), ((4, 7), c2)]

/-- **Theorem 4, k = 4.** `N = 8`, every gauge costs at least `6`, and `6` is attained:
`N/D = 4/3`. -/
theorem witness_k4 :
    defect w4 = 8 ∧ (∀ β, 6 ≤ cost w4 β) ∧ cost w4 (fun _ => 1) = 6 ∧ 8 * 3 = 4 * 6 :=
  ⟨by decide +kernel, gauge_lower w4 6 (by decide +kernel), by decide +kernel, by norm_num⟩

/-- **Theorem 4, k = 5.** `N = 10`, `D = 6`: `N/D = 5/3`. -/
theorem witness_k5 :
    defect w5 = 10 ∧ (∀ β, 6 ≤ cost w5 β) ∧ cost w5 (fun _ => 1) = 6 ∧ 10 * 3 = 5 * 6 :=
  ⟨by decide +kernel, gauge_lower w5 6 (by decide +kernel), by decide +kernel, by norm_num⟩

/-! ### The k = 6, 7 and 8 exhaustions, split by the gauge on the first vertices -/

private theorem k6_leaf_0 : search w6 18 4 [1, 1] = true := by
  decide +kernel

private theorem k6_leaf_1 : search w6 18 4 [1, t01] = true := by
  decide +kernel

private theorem k6_leaf_2 : search w6 18 4 [1, t12] = true := by
  decide +kernel

private theorem k6_leaf_3 : search w6 18 4 [1, t02] = true := by
  decide +kernel

private theorem k6_leaf_4 : search w6 18 4 [1, c1] = true := by
  decide +kernel

private theorem k6_leaf_5 : search w6 18 4 [1, c2] = true := by
  decide +kernel

private theorem k6_root : search w6 18 5 [1] = true :=
  search_split w6 18 4 [1] k6_leaf_0 k6_leaf_1 k6_leaf_2 k6_leaf_3 k6_leaf_4 k6_leaf_5

private theorem k7_leaf_0_0 : search w7 12 4 [1, 1, 1] = true := by
  decide +kernel

private theorem k7_leaf_0_1 : search w7 12 4 [1, 1, t01] = true := by
  decide +kernel

private theorem k7_leaf_0_2 : search w7 12 4 [1, 1, t12] = true := by
  decide +kernel

private theorem k7_leaf_0_3 : search w7 12 4 [1, 1, t02] = true := by
  decide +kernel

private theorem k7_leaf_0_4 : search w7 12 4 [1, 1, c1] = true := by
  decide +kernel

private theorem k7_leaf_0_5 : search w7 12 4 [1, 1, c2] = true := by
  decide +kernel

private theorem k7_leaf_1_0 : search w7 12 4 [1, t01, 1] = true := by
  decide +kernel

private theorem k7_leaf_1_1 : search w7 12 4 [1, t01, t01] = true := by
  decide +kernel

private theorem k7_leaf_1_2 : search w7 12 4 [1, t01, t12] = true := by
  decide +kernel

private theorem k7_leaf_1_3 : search w7 12 4 [1, t01, t02] = true := by
  decide +kernel

private theorem k7_leaf_1_4 : search w7 12 4 [1, t01, c1] = true := by
  decide +kernel

private theorem k7_leaf_1_5 : search w7 12 4 [1, t01, c2] = true := by
  decide +kernel

private theorem k7_leaf_2_0 : search w7 12 4 [1, t12, 1] = true := by
  decide +kernel

private theorem k7_leaf_2_1 : search w7 12 4 [1, t12, t01] = true := by
  decide +kernel

private theorem k7_leaf_2_2 : search w7 12 4 [1, t12, t12] = true := by
  decide +kernel

private theorem k7_leaf_2_3 : search w7 12 4 [1, t12, t02] = true := by
  decide +kernel

private theorem k7_leaf_2_4 : search w7 12 4 [1, t12, c1] = true := by
  decide +kernel

private theorem k7_leaf_2_5 : search w7 12 4 [1, t12, c2] = true := by
  decide +kernel

private theorem k7_leaf_3_0 : search w7 12 4 [1, t02, 1] = true := by
  decide +kernel

private theorem k7_leaf_3_1 : search w7 12 4 [1, t02, t01] = true := by
  decide +kernel

private theorem k7_leaf_3_2 : search w7 12 4 [1, t02, t12] = true := by
  decide +kernel

private theorem k7_leaf_3_3 : search w7 12 4 [1, t02, t02] = true := by
  decide +kernel

private theorem k7_leaf_3_4 : search w7 12 4 [1, t02, c1] = true := by
  decide +kernel

private theorem k7_leaf_3_5 : search w7 12 4 [1, t02, c2] = true := by
  decide +kernel

private theorem k7_leaf_4_0 : search w7 12 4 [1, c1, 1] = true := by
  decide +kernel

private theorem k7_leaf_4_1 : search w7 12 4 [1, c1, t01] = true := by
  decide +kernel

private theorem k7_leaf_4_2 : search w7 12 4 [1, c1, t12] = true := by
  decide +kernel

private theorem k7_leaf_4_3 : search w7 12 4 [1, c1, t02] = true := by
  decide +kernel

private theorem k7_leaf_4_4 : search w7 12 4 [1, c1, c1] = true := by
  decide +kernel

private theorem k7_leaf_4_5 : search w7 12 4 [1, c1, c2] = true := by
  decide +kernel

private theorem k7_leaf_5_0 : search w7 12 4 [1, c2, 1] = true := by
  decide +kernel

private theorem k7_leaf_5_1 : search w7 12 4 [1, c2, t01] = true := by
  decide +kernel

private theorem k7_leaf_5_2 : search w7 12 4 [1, c2, t12] = true := by
  decide +kernel

private theorem k7_leaf_5_3 : search w7 12 4 [1, c2, t02] = true := by
  decide +kernel

private theorem k7_leaf_5_4 : search w7 12 4 [1, c2, c1] = true := by
  decide +kernel

private theorem k7_leaf_5_5 : search w7 12 4 [1, c2, c2] = true := by
  decide +kernel

private theorem k7_node_0 : search w7 12 5 [1, 1] = true :=
  search_split w7 12 4 [1, 1] k7_leaf_0_0 k7_leaf_0_1 k7_leaf_0_2 k7_leaf_0_3 k7_leaf_0_4
    k7_leaf_0_5

private theorem k7_node_1 : search w7 12 5 [1, t01] = true :=
  search_split w7 12 4 [1, t01] k7_leaf_1_0 k7_leaf_1_1 k7_leaf_1_2 k7_leaf_1_3 k7_leaf_1_4
    k7_leaf_1_5

private theorem k7_node_2 : search w7 12 5 [1, t12] = true :=
  search_split w7 12 4 [1, t12] k7_leaf_2_0 k7_leaf_2_1 k7_leaf_2_2 k7_leaf_2_3 k7_leaf_2_4
    k7_leaf_2_5

private theorem k7_node_3 : search w7 12 5 [1, t02] = true :=
  search_split w7 12 4 [1, t02] k7_leaf_3_0 k7_leaf_3_1 k7_leaf_3_2 k7_leaf_3_3 k7_leaf_3_4
    k7_leaf_3_5

private theorem k7_node_4 : search w7 12 5 [1, c1] = true :=
  search_split w7 12 4 [1, c1] k7_leaf_4_0 k7_leaf_4_1 k7_leaf_4_2 k7_leaf_4_3 k7_leaf_4_4
    k7_leaf_4_5

private theorem k7_node_5 : search w7 12 5 [1, c2] = true :=
  search_split w7 12 4 [1, c2] k7_leaf_5_0 k7_leaf_5_1 k7_leaf_5_2 k7_leaf_5_3 k7_leaf_5_4
    k7_leaf_5_5

private theorem k7_root : search w7 12 6 [1] = true :=
  search_split w7 12 5 [1] k7_node_0 k7_node_1 k7_node_2 k7_node_3 k7_node_4 k7_node_5

private theorem k8_leaf_0_0_0 : search w8 27 4 [1, 1, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_0_1 : search w8 27 4 [1, 1, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_0_2 : search w8 27 4 [1, 1, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_0_3 : search w8 27 4 [1, 1, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_0_4 : search w8 27 4 [1, 1, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_0_5 : search w8 27 4 [1, 1, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_1_0 : search w8 27 4 [1, 1, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_1_1 : search w8 27 4 [1, 1, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_1_2 : search w8 27 4 [1, 1, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_1_3 : search w8 27 4 [1, 1, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_1_4 : search w8 27 4 [1, 1, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_1_5 : search w8 27 4 [1, 1, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_2_0 : search w8 27 4 [1, 1, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_2_1 : search w8 27 4 [1, 1, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_2_2 : search w8 27 4 [1, 1, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_2_3 : search w8 27 4 [1, 1, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_2_4 : search w8 27 4 [1, 1, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_2_5 : search w8 27 4 [1, 1, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_3_0 : search w8 27 4 [1, 1, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_3_1 : search w8 27 4 [1, 1, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_3_2 : search w8 27 4 [1, 1, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_3_3 : search w8 27 4 [1, 1, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_3_4 : search w8 27 4 [1, 1, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_3_5 : search w8 27 4 [1, 1, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_4_0 : search w8 27 4 [1, 1, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_4_1 : search w8 27 4 [1, 1, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_4_2 : search w8 27 4 [1, 1, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_4_3 : search w8 27 4 [1, 1, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_4_4 : search w8 27 4 [1, 1, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_4_5 : search w8 27 4 [1, 1, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_0_5_0 : search w8 27 4 [1, 1, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_0_5_1 : search w8 27 4 [1, 1, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_0_5_2 : search w8 27 4 [1, 1, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_0_5_3 : search w8 27 4 [1, 1, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_0_5_4 : search w8 27 4 [1, 1, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_0_5_5 : search w8 27 4 [1, 1, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_0_0 : search w8 27 4 [1, t01, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_0_1 : search w8 27 4 [1, t01, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_0_2 : search w8 27 4 [1, t01, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_0_3 : search w8 27 4 [1, t01, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_0_4 : search w8 27 4 [1, t01, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_0_5 : search w8 27 4 [1, t01, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_1_0 : search w8 27 4 [1, t01, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_1_1 : search w8 27 4 [1, t01, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_1_2 : search w8 27 4 [1, t01, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_1_3 : search w8 27 4 [1, t01, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_1_4 : search w8 27 4 [1, t01, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_1_5 : search w8 27 4 [1, t01, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_2_0 : search w8 27 4 [1, t01, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_2_1 : search w8 27 4 [1, t01, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_2_2 : search w8 27 4 [1, t01, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_2_3 : search w8 27 4 [1, t01, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_2_4 : search w8 27 4 [1, t01, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_2_5 : search w8 27 4 [1, t01, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_3_0 : search w8 27 4 [1, t01, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_3_1 : search w8 27 4 [1, t01, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_3_2 : search w8 27 4 [1, t01, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_3_3 : search w8 27 4 [1, t01, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_3_4 : search w8 27 4 [1, t01, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_3_5 : search w8 27 4 [1, t01, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_4_0 : search w8 27 4 [1, t01, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_4_1 : search w8 27 4 [1, t01, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_4_2 : search w8 27 4 [1, t01, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_4_3 : search w8 27 4 [1, t01, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_4_4 : search w8 27 4 [1, t01, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_4_5 : search w8 27 4 [1, t01, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_1_5_0 : search w8 27 4 [1, t01, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_1_5_1 : search w8 27 4 [1, t01, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_1_5_2 : search w8 27 4 [1, t01, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_1_5_3 : search w8 27 4 [1, t01, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_1_5_4 : search w8 27 4 [1, t01, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_1_5_5 : search w8 27 4 [1, t01, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_0_0 : search w8 27 4 [1, t12, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_0_1 : search w8 27 4 [1, t12, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_0_2 : search w8 27 4 [1, t12, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_0_3 : search w8 27 4 [1, t12, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_0_4 : search w8 27 4 [1, t12, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_0_5 : search w8 27 4 [1, t12, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_1_0 : search w8 27 4 [1, t12, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_1_1 : search w8 27 4 [1, t12, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_1_2 : search w8 27 4 [1, t12, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_1_3 : search w8 27 4 [1, t12, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_1_4 : search w8 27 4 [1, t12, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_1_5 : search w8 27 4 [1, t12, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_2_0 : search w8 27 4 [1, t12, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_2_1 : search w8 27 4 [1, t12, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_2_2 : search w8 27 4 [1, t12, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_2_3 : search w8 27 4 [1, t12, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_2_4 : search w8 27 4 [1, t12, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_2_5 : search w8 27 4 [1, t12, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_3_0 : search w8 27 4 [1, t12, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_3_1 : search w8 27 4 [1, t12, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_3_2 : search w8 27 4 [1, t12, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_3_3 : search w8 27 4 [1, t12, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_3_4 : search w8 27 4 [1, t12, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_3_5 : search w8 27 4 [1, t12, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_4_0 : search w8 27 4 [1, t12, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_4_1 : search w8 27 4 [1, t12, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_4_2 : search w8 27 4 [1, t12, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_4_3 : search w8 27 4 [1, t12, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_4_4 : search w8 27 4 [1, t12, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_4_5 : search w8 27 4 [1, t12, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_2_5_0 : search w8 27 4 [1, t12, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_2_5_1 : search w8 27 4 [1, t12, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_2_5_2 : search w8 27 4 [1, t12, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_2_5_3 : search w8 27 4 [1, t12, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_2_5_4 : search w8 27 4 [1, t12, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_2_5_5 : search w8 27 4 [1, t12, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_0_0 : search w8 27 4 [1, t02, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_0_1 : search w8 27 4 [1, t02, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_0_2 : search w8 27 4 [1, t02, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_0_3 : search w8 27 4 [1, t02, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_0_4 : search w8 27 4 [1, t02, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_0_5 : search w8 27 4 [1, t02, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_1_0 : search w8 27 4 [1, t02, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_1_1 : search w8 27 4 [1, t02, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_1_2 : search w8 27 4 [1, t02, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_1_3 : search w8 27 4 [1, t02, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_1_4 : search w8 27 4 [1, t02, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_1_5 : search w8 27 4 [1, t02, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_2_0 : search w8 27 4 [1, t02, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_2_1 : search w8 27 4 [1, t02, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_2_2 : search w8 27 4 [1, t02, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_2_3 : search w8 27 4 [1, t02, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_2_4 : search w8 27 4 [1, t02, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_2_5 : search w8 27 4 [1, t02, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_3_0 : search w8 27 4 [1, t02, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_3_1 : search w8 27 4 [1, t02, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_3_2 : search w8 27 4 [1, t02, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_3_3 : search w8 27 4 [1, t02, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_3_4 : search w8 27 4 [1, t02, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_3_5 : search w8 27 4 [1, t02, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_4_0 : search w8 27 4 [1, t02, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_4_1 : search w8 27 4 [1, t02, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_4_2 : search w8 27 4 [1, t02, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_4_3 : search w8 27 4 [1, t02, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_4_4 : search w8 27 4 [1, t02, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_4_5 : search w8 27 4 [1, t02, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_3_5_0 : search w8 27 4 [1, t02, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_3_5_1 : search w8 27 4 [1, t02, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_3_5_2 : search w8 27 4 [1, t02, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_3_5_3 : search w8 27 4 [1, t02, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_3_5_4 : search w8 27 4 [1, t02, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_3_5_5 : search w8 27 4 [1, t02, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_0_0 : search w8 27 4 [1, c1, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_0_1 : search w8 27 4 [1, c1, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_0_2 : search w8 27 4 [1, c1, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_0_3 : search w8 27 4 [1, c1, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_0_4 : search w8 27 4 [1, c1, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_0_5 : search w8 27 4 [1, c1, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_1_0 : search w8 27 4 [1, c1, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_1_1 : search w8 27 4 [1, c1, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_1_2 : search w8 27 4 [1, c1, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_1_3 : search w8 27 4 [1, c1, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_1_4 : search w8 27 4 [1, c1, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_1_5 : search w8 27 4 [1, c1, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_2_0 : search w8 27 4 [1, c1, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_2_1 : search w8 27 4 [1, c1, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_2_2 : search w8 27 4 [1, c1, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_2_3 : search w8 27 4 [1, c1, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_2_4 : search w8 27 4 [1, c1, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_2_5 : search w8 27 4 [1, c1, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_3_0 : search w8 27 4 [1, c1, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_3_1 : search w8 27 4 [1, c1, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_3_2 : search w8 27 4 [1, c1, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_3_3 : search w8 27 4 [1, c1, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_3_4 : search w8 27 4 [1, c1, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_3_5 : search w8 27 4 [1, c1, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_4_0 : search w8 27 4 [1, c1, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_4_1 : search w8 27 4 [1, c1, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_4_2 : search w8 27 4 [1, c1, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_4_3 : search w8 27 4 [1, c1, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_4_4 : search w8 27 4 [1, c1, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_4_5 : search w8 27 4 [1, c1, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_4_5_0 : search w8 27 4 [1, c1, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_4_5_1 : search w8 27 4 [1, c1, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_4_5_2 : search w8 27 4 [1, c1, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_4_5_3 : search w8 27 4 [1, c1, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_4_5_4 : search w8 27 4 [1, c1, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_4_5_5 : search w8 27 4 [1, c1, c2, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_0_0 : search w8 27 4 [1, c2, 1, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_0_1 : search w8 27 4 [1, c2, 1, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_0_2 : search w8 27 4 [1, c2, 1, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_0_3 : search w8 27 4 [1, c2, 1, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_0_4 : search w8 27 4 [1, c2, 1, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_0_5 : search w8 27 4 [1, c2, 1, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_1_0 : search w8 27 4 [1, c2, t01, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_1_1 : search w8 27 4 [1, c2, t01, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_1_2 : search w8 27 4 [1, c2, t01, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_1_3 : search w8 27 4 [1, c2, t01, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_1_4 : search w8 27 4 [1, c2, t01, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_1_5 : search w8 27 4 [1, c2, t01, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_2_0 : search w8 27 4 [1, c2, t12, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_2_1 : search w8 27 4 [1, c2, t12, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_2_2 : search w8 27 4 [1, c2, t12, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_2_3 : search w8 27 4 [1, c2, t12, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_2_4 : search w8 27 4 [1, c2, t12, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_2_5 : search w8 27 4 [1, c2, t12, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_3_0 : search w8 27 4 [1, c2, t02, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_3_1 : search w8 27 4 [1, c2, t02, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_3_2 : search w8 27 4 [1, c2, t02, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_3_3 : search w8 27 4 [1, c2, t02, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_3_4 : search w8 27 4 [1, c2, t02, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_3_5 : search w8 27 4 [1, c2, t02, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_4_0 : search w8 27 4 [1, c2, c1, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_4_1 : search w8 27 4 [1, c2, c1, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_4_2 : search w8 27 4 [1, c2, c1, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_4_3 : search w8 27 4 [1, c2, c1, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_4_4 : search w8 27 4 [1, c2, c1, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_4_5 : search w8 27 4 [1, c2, c1, c2] = true := by
  decide +kernel

private theorem k8_leaf_5_5_0 : search w8 27 4 [1, c2, c2, 1] = true := by
  decide +kernel

private theorem k8_leaf_5_5_1 : search w8 27 4 [1, c2, c2, t01] = true := by
  decide +kernel

private theorem k8_leaf_5_5_2 : search w8 27 4 [1, c2, c2, t12] = true := by
  decide +kernel

private theorem k8_leaf_5_5_3 : search w8 27 4 [1, c2, c2, t02] = true := by
  decide +kernel

private theorem k8_leaf_5_5_4 : search w8 27 4 [1, c2, c2, c1] = true := by
  decide +kernel

private theorem k8_leaf_5_5_5 : search w8 27 4 [1, c2, c2, c2] = true := by
  decide +kernel

private theorem k8_node_0_0 : search w8 27 5 [1, 1, 1] = true :=
  search_split w8 27 4 [1, 1, 1] k8_leaf_0_0_0 k8_leaf_0_0_1 k8_leaf_0_0_2 k8_leaf_0_0_3
    k8_leaf_0_0_4 k8_leaf_0_0_5

private theorem k8_node_0_1 : search w8 27 5 [1, 1, t01] = true :=
  search_split w8 27 4 [1, 1, t01] k8_leaf_0_1_0 k8_leaf_0_1_1 k8_leaf_0_1_2 k8_leaf_0_1_3
    k8_leaf_0_1_4 k8_leaf_0_1_5

private theorem k8_node_0_2 : search w8 27 5 [1, 1, t12] = true :=
  search_split w8 27 4 [1, 1, t12] k8_leaf_0_2_0 k8_leaf_0_2_1 k8_leaf_0_2_2 k8_leaf_0_2_3
    k8_leaf_0_2_4 k8_leaf_0_2_5

private theorem k8_node_0_3 : search w8 27 5 [1, 1, t02] = true :=
  search_split w8 27 4 [1, 1, t02] k8_leaf_0_3_0 k8_leaf_0_3_1 k8_leaf_0_3_2 k8_leaf_0_3_3
    k8_leaf_0_3_4 k8_leaf_0_3_5

private theorem k8_node_0_4 : search w8 27 5 [1, 1, c1] = true :=
  search_split w8 27 4 [1, 1, c1] k8_leaf_0_4_0 k8_leaf_0_4_1 k8_leaf_0_4_2 k8_leaf_0_4_3
    k8_leaf_0_4_4 k8_leaf_0_4_5

private theorem k8_node_0_5 : search w8 27 5 [1, 1, c2] = true :=
  search_split w8 27 4 [1, 1, c2] k8_leaf_0_5_0 k8_leaf_0_5_1 k8_leaf_0_5_2 k8_leaf_0_5_3
    k8_leaf_0_5_4 k8_leaf_0_5_5

private theorem k8_node_1_0 : search w8 27 5 [1, t01, 1] = true :=
  search_split w8 27 4 [1, t01, 1] k8_leaf_1_0_0 k8_leaf_1_0_1 k8_leaf_1_0_2 k8_leaf_1_0_3
    k8_leaf_1_0_4 k8_leaf_1_0_5

private theorem k8_node_1_1 : search w8 27 5 [1, t01, t01] = true :=
  search_split w8 27 4 [1, t01, t01] k8_leaf_1_1_0 k8_leaf_1_1_1 k8_leaf_1_1_2 k8_leaf_1_1_3
    k8_leaf_1_1_4 k8_leaf_1_1_5

private theorem k8_node_1_2 : search w8 27 5 [1, t01, t12] = true :=
  search_split w8 27 4 [1, t01, t12] k8_leaf_1_2_0 k8_leaf_1_2_1 k8_leaf_1_2_2 k8_leaf_1_2_3
    k8_leaf_1_2_4 k8_leaf_1_2_5

private theorem k8_node_1_3 : search w8 27 5 [1, t01, t02] = true :=
  search_split w8 27 4 [1, t01, t02] k8_leaf_1_3_0 k8_leaf_1_3_1 k8_leaf_1_3_2 k8_leaf_1_3_3
    k8_leaf_1_3_4 k8_leaf_1_3_5

private theorem k8_node_1_4 : search w8 27 5 [1, t01, c1] = true :=
  search_split w8 27 4 [1, t01, c1] k8_leaf_1_4_0 k8_leaf_1_4_1 k8_leaf_1_4_2 k8_leaf_1_4_3
    k8_leaf_1_4_4 k8_leaf_1_4_5

private theorem k8_node_1_5 : search w8 27 5 [1, t01, c2] = true :=
  search_split w8 27 4 [1, t01, c2] k8_leaf_1_5_0 k8_leaf_1_5_1 k8_leaf_1_5_2 k8_leaf_1_5_3
    k8_leaf_1_5_4 k8_leaf_1_5_5

private theorem k8_node_2_0 : search w8 27 5 [1, t12, 1] = true :=
  search_split w8 27 4 [1, t12, 1] k8_leaf_2_0_0 k8_leaf_2_0_1 k8_leaf_2_0_2 k8_leaf_2_0_3
    k8_leaf_2_0_4 k8_leaf_2_0_5

private theorem k8_node_2_1 : search w8 27 5 [1, t12, t01] = true :=
  search_split w8 27 4 [1, t12, t01] k8_leaf_2_1_0 k8_leaf_2_1_1 k8_leaf_2_1_2 k8_leaf_2_1_3
    k8_leaf_2_1_4 k8_leaf_2_1_5

private theorem k8_node_2_2 : search w8 27 5 [1, t12, t12] = true :=
  search_split w8 27 4 [1, t12, t12] k8_leaf_2_2_0 k8_leaf_2_2_1 k8_leaf_2_2_2 k8_leaf_2_2_3
    k8_leaf_2_2_4 k8_leaf_2_2_5

private theorem k8_node_2_3 : search w8 27 5 [1, t12, t02] = true :=
  search_split w8 27 4 [1, t12, t02] k8_leaf_2_3_0 k8_leaf_2_3_1 k8_leaf_2_3_2 k8_leaf_2_3_3
    k8_leaf_2_3_4 k8_leaf_2_3_5

private theorem k8_node_2_4 : search w8 27 5 [1, t12, c1] = true :=
  search_split w8 27 4 [1, t12, c1] k8_leaf_2_4_0 k8_leaf_2_4_1 k8_leaf_2_4_2 k8_leaf_2_4_3
    k8_leaf_2_4_4 k8_leaf_2_4_5

private theorem k8_node_2_5 : search w8 27 5 [1, t12, c2] = true :=
  search_split w8 27 4 [1, t12, c2] k8_leaf_2_5_0 k8_leaf_2_5_1 k8_leaf_2_5_2 k8_leaf_2_5_3
    k8_leaf_2_5_4 k8_leaf_2_5_5

private theorem k8_node_3_0 : search w8 27 5 [1, t02, 1] = true :=
  search_split w8 27 4 [1, t02, 1] k8_leaf_3_0_0 k8_leaf_3_0_1 k8_leaf_3_0_2 k8_leaf_3_0_3
    k8_leaf_3_0_4 k8_leaf_3_0_5

private theorem k8_node_3_1 : search w8 27 5 [1, t02, t01] = true :=
  search_split w8 27 4 [1, t02, t01] k8_leaf_3_1_0 k8_leaf_3_1_1 k8_leaf_3_1_2 k8_leaf_3_1_3
    k8_leaf_3_1_4 k8_leaf_3_1_5

private theorem k8_node_3_2 : search w8 27 5 [1, t02, t12] = true :=
  search_split w8 27 4 [1, t02, t12] k8_leaf_3_2_0 k8_leaf_3_2_1 k8_leaf_3_2_2 k8_leaf_3_2_3
    k8_leaf_3_2_4 k8_leaf_3_2_5

private theorem k8_node_3_3 : search w8 27 5 [1, t02, t02] = true :=
  search_split w8 27 4 [1, t02, t02] k8_leaf_3_3_0 k8_leaf_3_3_1 k8_leaf_3_3_2 k8_leaf_3_3_3
    k8_leaf_3_3_4 k8_leaf_3_3_5

private theorem k8_node_3_4 : search w8 27 5 [1, t02, c1] = true :=
  search_split w8 27 4 [1, t02, c1] k8_leaf_3_4_0 k8_leaf_3_4_1 k8_leaf_3_4_2 k8_leaf_3_4_3
    k8_leaf_3_4_4 k8_leaf_3_4_5

private theorem k8_node_3_5 : search w8 27 5 [1, t02, c2] = true :=
  search_split w8 27 4 [1, t02, c2] k8_leaf_3_5_0 k8_leaf_3_5_1 k8_leaf_3_5_2 k8_leaf_3_5_3
    k8_leaf_3_5_4 k8_leaf_3_5_5

private theorem k8_node_4_0 : search w8 27 5 [1, c1, 1] = true :=
  search_split w8 27 4 [1, c1, 1] k8_leaf_4_0_0 k8_leaf_4_0_1 k8_leaf_4_0_2 k8_leaf_4_0_3
    k8_leaf_4_0_4 k8_leaf_4_0_5

private theorem k8_node_4_1 : search w8 27 5 [1, c1, t01] = true :=
  search_split w8 27 4 [1, c1, t01] k8_leaf_4_1_0 k8_leaf_4_1_1 k8_leaf_4_1_2 k8_leaf_4_1_3
    k8_leaf_4_1_4 k8_leaf_4_1_5

private theorem k8_node_4_2 : search w8 27 5 [1, c1, t12] = true :=
  search_split w8 27 4 [1, c1, t12] k8_leaf_4_2_0 k8_leaf_4_2_1 k8_leaf_4_2_2 k8_leaf_4_2_3
    k8_leaf_4_2_4 k8_leaf_4_2_5

private theorem k8_node_4_3 : search w8 27 5 [1, c1, t02] = true :=
  search_split w8 27 4 [1, c1, t02] k8_leaf_4_3_0 k8_leaf_4_3_1 k8_leaf_4_3_2 k8_leaf_4_3_3
    k8_leaf_4_3_4 k8_leaf_4_3_5

private theorem k8_node_4_4 : search w8 27 5 [1, c1, c1] = true :=
  search_split w8 27 4 [1, c1, c1] k8_leaf_4_4_0 k8_leaf_4_4_1 k8_leaf_4_4_2 k8_leaf_4_4_3
    k8_leaf_4_4_4 k8_leaf_4_4_5

private theorem k8_node_4_5 : search w8 27 5 [1, c1, c2] = true :=
  search_split w8 27 4 [1, c1, c2] k8_leaf_4_5_0 k8_leaf_4_5_1 k8_leaf_4_5_2 k8_leaf_4_5_3
    k8_leaf_4_5_4 k8_leaf_4_5_5

private theorem k8_node_5_0 : search w8 27 5 [1, c2, 1] = true :=
  search_split w8 27 4 [1, c2, 1] k8_leaf_5_0_0 k8_leaf_5_0_1 k8_leaf_5_0_2 k8_leaf_5_0_3
    k8_leaf_5_0_4 k8_leaf_5_0_5

private theorem k8_node_5_1 : search w8 27 5 [1, c2, t01] = true :=
  search_split w8 27 4 [1, c2, t01] k8_leaf_5_1_0 k8_leaf_5_1_1 k8_leaf_5_1_2 k8_leaf_5_1_3
    k8_leaf_5_1_4 k8_leaf_5_1_5

private theorem k8_node_5_2 : search w8 27 5 [1, c2, t12] = true :=
  search_split w8 27 4 [1, c2, t12] k8_leaf_5_2_0 k8_leaf_5_2_1 k8_leaf_5_2_2 k8_leaf_5_2_3
    k8_leaf_5_2_4 k8_leaf_5_2_5

private theorem k8_node_5_3 : search w8 27 5 [1, c2, t02] = true :=
  search_split w8 27 4 [1, c2, t02] k8_leaf_5_3_0 k8_leaf_5_3_1 k8_leaf_5_3_2 k8_leaf_5_3_3
    k8_leaf_5_3_4 k8_leaf_5_3_5

private theorem k8_node_5_4 : search w8 27 5 [1, c2, c1] = true :=
  search_split w8 27 4 [1, c2, c1] k8_leaf_5_4_0 k8_leaf_5_4_1 k8_leaf_5_4_2 k8_leaf_5_4_3
    k8_leaf_5_4_4 k8_leaf_5_4_5

private theorem k8_node_5_5 : search w8 27 5 [1, c2, c2] = true :=
  search_split w8 27 4 [1, c2, c2] k8_leaf_5_5_0 k8_leaf_5_5_1 k8_leaf_5_5_2 k8_leaf_5_5_3
    k8_leaf_5_5_4 k8_leaf_5_5_5

private theorem k8_node_0 : search w8 27 6 [1, 1] = true :=
  search_split w8 27 5 [1, 1] k8_node_0_0 k8_node_0_1 k8_node_0_2 k8_node_0_3 k8_node_0_4
    k8_node_0_5

private theorem k8_node_1 : search w8 27 6 [1, t01] = true :=
  search_split w8 27 5 [1, t01] k8_node_1_0 k8_node_1_1 k8_node_1_2 k8_node_1_3 k8_node_1_4
    k8_node_1_5

private theorem k8_node_2 : search w8 27 6 [1, t12] = true :=
  search_split w8 27 5 [1, t12] k8_node_2_0 k8_node_2_1 k8_node_2_2 k8_node_2_3 k8_node_2_4
    k8_node_2_5

private theorem k8_node_3 : search w8 27 6 [1, t02] = true :=
  search_split w8 27 5 [1, t02] k8_node_3_0 k8_node_3_1 k8_node_3_2 k8_node_3_3 k8_node_3_4
    k8_node_3_5

private theorem k8_node_4 : search w8 27 6 [1, c1] = true :=
  search_split w8 27 5 [1, c1] k8_node_4_0 k8_node_4_1 k8_node_4_2 k8_node_4_3 k8_node_4_4
    k8_node_4_5

private theorem k8_node_5 : search w8 27 6 [1, c2] = true :=
  search_split w8 27 5 [1, c2] k8_node_5_0 k8_node_5_1 k8_node_5_2 k8_node_5_3 k8_node_5_4
    k8_node_5_5

private theorem k8_root : search w8 27 7 [1] = true :=
  search_split w8 27 6 [1] k8_node_0 k8_node_1 k8_node_2 k8_node_3 k8_node_4 k8_node_5

/-- **Theorem 4, k = 6.** `N = 36`, `D = 18`: `N/D = 2 = 6/3`. -/
theorem witness_k6 :
    defect w6 = 36 ∧ (∀ β, 18 ≤ cost w6 β) ∧ cost w6 (fun _ => 1) = 18 ∧ 36 * 3 = 6 * 18 :=
  ⟨by decide +kernel, gauge_lower_bb w6 18 k6_root, by decide +kernel, by norm_num⟩

/-- **Theorem 4, k = 7.** `N = 28`, `D = 12`: `N/D = 7/3`. -/
theorem witness_k7 :
    defect w7 = 28 ∧ (∀ β, 12 ≤ cost w7 β) ∧ cost w7 (fun _ => 1) = 12 ∧ 28 * 3 = 7 * 12 :=
  ⟨by decide +kernel, gauge_lower_bb w7 12 k7_root, by decide +kernel, by norm_num⟩

/-- **Theorem 4, k = 8.** `N = 72`, `D = 27`: `N/D = 8/3`. The residual carries twelve
transpositions (all three of `Sym(3)`) and one 3-cycle. -/
theorem witness_k8 :
    defect w8 = 72 ∧ (∀ β, 27 ≤ cost w8 β) ∧ cost w8 (fun _ => 1) = 27 ∧ 72 * 3 = 8 * 27 :=
  ⟨by decide +kernel, gauge_lower_bb w8 27 k8_root, by decide +kernel, by norm_num⟩

/-! ## Proposition 5: the non-abelian mechanism at k = 4 -/

/-- **Proposition 5, mechanism.** Around the witness triangle the three distinct transpositions
compose to a transposition (2 moved points), while each adjacent product is a 3-cycle. -/
theorem k4_mechanism :
    moved (t12 * t02 * t01⁻¹) = 2 ∧ moved (t12 * t02) = 3 ∧ moved (t02 * t01) = 3 ∧
      moved (t01 * t12) = 3 := by decide

/-! ## Theorem 13: the displacement Gram and the cycle Laplacian -/

/-- The displacement `e_{π(i)} − e_i` of point `i`. -/
def disp {n : ℕ} (π : Perm (Fin n)) (i : Fin n) : Fin n → ℤ :=
  fun t => (if t = π i then 1 else 0) - (if t = i then 1 else 0)

theorem delta_prod {n : ℕ} (a b : Fin n) :
    ∑ t : Fin n, (if t = a then (1 : ℤ) else 0) * (if t = b then 1 else 0) =
      if a = b then 1 else 0 := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

/-- **Theorem 13.** `⟨e_{π i} − e_i, e_{π j} − e_j⟩ = 2[i = j] − [π i = j] − [π j = i]`, i.e.
the matrix of these inner products is `2I − A` for the adjacency `A` of the cycle graph of `π`,
the Laplacian of that graph; the Gram matrix normalised by `½` is half of it. -/
theorem disp_gram {n : ℕ} (π : Perm (Fin n)) (i j : Fin n) :
    ∑ t, disp π i t * disp π j t =
      (if i = j then 2 else 0) - (if π i = j then 1 else 0) - (if π j = i then 1 else 0) := by
  have hexp : ∀ t, disp π i t * disp π j t =
      (if t = π i then (1 : ℤ) else 0) * (if t = π j then 1 else 0)
      - (if t = π i then (1 : ℤ) else 0) * (if t = j then 1 else 0)
      - (if t = i then (1 : ℤ) else 0) * (if t = π j then 1 else 0)
      + (if t = i then (1 : ℤ) else 0) * (if t = j then 1 else 0) := by
    intro t
    simp only [disp]
    ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, delta_prod]
  have hπ : (π i = π j) ↔ i = j := π.injective.eq_iff
  by_cases hij : i = j
  · subst hij
    by_cases h : π i = i
    · simp [h]
    · have h' : ¬ i = π i := fun e => h e.symm
      simp [h, h']
  · have h1 : ¬ π i = π j := fun h => hij (hπ.mp h)
    by_cases h2 : π i = j <;> by_cases h3 : i = π j <;>
      simp [hij, h1, h2, h3, eq_comm] <;> omega

/-- **Theorem 13, cycle spectrum.** The identity `2 − 2cos 2x = 4 sin² x`, which rewrites the
Laplacian eigenvalue `2 − 2cos(2πj/ℓ)` of `C_ℓ` (cited, not proved here) as `4 sin²(πj/ℓ)`. -/
theorem cycle_laplacian_eigen (x : ℝ) : 2 - 2 * Real.cos (2 * x) = 4 * Real.sin x ^ 2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

end CoboundaryK3
