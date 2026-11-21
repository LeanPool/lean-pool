/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Dissection
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fill and operation bounds for nested dissection

Let `t` be a separator tree of a graph `G` on `n` vertices such that at every node with `m`
vertices

* the separator (at a leaf: the whole leaf set) has at most `α * √m` vertices,
* the boundary (the vertices outside the subtree adjacent to it) has at most `β * √m` vertices,
* each of the two parts has at most `2 * m / 3` vertices.

Then, in the nested dissection order of `t`,

* the filled graph has at most `α * (α + β) * n * (1 + log_{3/2} n)` edges
  (`card_edgeFinset_fill_le`),
* `∑ v, (deg⁺ v + 1) ^ 2 ≤ 6 * α * (α + β) ^ 2 * n ^ (3/2)` (`sum_sq_le`), so elimination
  restricted to the filled pattern costs at most `12 * α * (α + β) ^ 2 * n ^ (3/2)` arithmetic
  operations (`nestedDissection_elimination`).

This follows the analysis of Lipton, Rose and Tarjan [*Generalized nested dissection*, SIAM J.
Numer. Anal. 16 (1979), 346–358] for graphs with `√n`-separators, which generalizes George's
analysis of the regular grid [*Nested dissection of a regular finite element mesh*, SIAM J.
Numer. Anal. 10 (1973)].  The boundary bound is a hypothesis on the tree: it does not follow from
the separator bounds alone, and the generalized nested dissection algorithm obtains it by
splitting the boundary vertices as well as the vertex set at each step.

## Main definitions

These definitions are in `NestedDissection/Spec.lean`.

* `NestedDissection.SepTree.AllNodes P t`: `P` holds at every node of `t`.
* `NestedDissection.SepTree.Shrinks t`: the parts of the root have at most `2/3` of its vertices.
* `NestedDissection.SepTree.SqrtBound G α β t`: the separator and boundary bounds at the root.
-/

namespace NestedDissection

@[expose] public section

universe u

namespace SepTree

variable {V : Type u}

theorem AllNodes.self {P : SepTree V → Prop} {t : SepTree V} (h : AllNodes P t) : P t := by
  cases t with
  | leaf s => exact h
  | node s a b => exact h.1

theorem sumNodes_le_of_allNodes {P : SepTree V → Prop} {f g : SepTree V → ℝ}
    (hfg : ∀ s, P s → f s ≤ g s) {t : SepTree V} (h : AllNodes P t) :
    sumNodes f t ≤ sumNodes g t := by
  induction t with
  | leaf s => exact hfg _ h
  | node s a b iha ihb => exact add_le_add (add_le_add (hfg _ h.1) (iha h.2.1)) (ihb h.2.2)

theorem sumNodes_mul_left (c : ℝ) (f : SepTree V → ℝ) (t : SepTree V) :
    sumNodes (fun s => c * f s) t = c * sumNodes f t := by
  induction t with
  | leaf s => rfl
  | node s a b iha ihb => simp only [sumNodes, iha, ihb]; ring

theorem sumNodes_cast (f : SepTree V → ℕ) (t : SepTree V) :
    ((sumNodes f t : ℕ) : ℝ) = sumNodes (fun s => (f s : ℝ)) t := by
  induction t with
  | leaf s => rfl
  | node s a b iha ihb => simp only [sumNodes, Nat.cast_add, iha, ihb]

variable [DecidableEq V]

/-! ### Geometric sums over shrinking trees -/

theorem sqrt_le_of_shrink {ma m : ℕ} (h : 3 * ma ≤ 2 * m) : √(ma : ℝ) ≤ 5 / 6 * √(m : ℝ) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h' : (3 : ℝ) * ma ≤ 2 * m := by exact_mod_cast h
  calc √(ma : ℝ) ≤ √((5 / 6 * √(m : ℝ)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [mul_pow, Real.sq_sqrt hm]
        linarith
    _ = 5 / 6 * √(m : ℝ) := Real.sqrt_sq (by positivity)

/-- `∑ over nodes of m ^ (3/2) ≤ 6 * n ^ (3/2)` for shrinking trees. -/
theorem sumNodes_card_mul_sqrt_le {G : SimpleGraph V} {t : SepTree V} (hd : IsDissection G t)
    (hs : AllNodes Shrinks t) :
    sumNodes (fun s => (s.verts.card : ℝ) * √(s.verts.card)) t ≤
      6 * ((t.verts.card : ℝ) * √(t.verts.card)) := by
  induction t with
  | leaf s =>
    have : 0 ≤ (s.card : ℝ) * √(s.card) := by positivity
    simp only [sumNodes, verts]
    linarith
  | node s a b iha ihb =>
    simp only [sumNodes]
    have ha := iha hd.2.2.2.2.1 hs.2.1
    have hb := ihb hd.2.2.2.2.2 hs.2.2
    have hab : (a.verts.card : ℝ) + b.verts.card ≤ (node s a b).verts.card := by
      exact_mod_cast card_verts_node_le hd
    have sa := sqrt_le_of_shrink hs.1.1
    have sb := sqrt_le_of_shrink hs.1.2
    set m : ℝ := ((node s a b).verts.card : ℝ)
    set x : ℝ := √m
    have hx : 0 ≤ x := Real.sqrt_nonneg _
    have hma : (0 : ℝ) ≤ a.verts.card := Nat.cast_nonneg _
    have hmb : (0 : ℝ) ≤ b.verts.card := Nat.cast_nonneg _
    have e1 : (a.verts.card : ℝ) * √(a.verts.card) ≤ a.verts.card * (5 / 6 * x) :=
      mul_le_mul_of_nonneg_left sa hma
    have e2 : (b.verts.card : ℝ) * √(b.verts.card) ≤ b.verts.card * (5 / 6 * x) :=
      mul_le_mul_of_nonneg_left sb hmb
    have e3 : ((a.verts.card : ℝ) + b.verts.card) * x ≤ m * x :=
      mul_le_mul_of_nonneg_right hab hx
    nlinarith

theorem mul_logb_nonneg (m : ℕ) : 0 ≤ (m : ℝ) * Real.logb (3 / 2) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact mul_nonneg (Nat.cast_nonneg m)
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast hm))

/-- A part with at most `2/3` of the vertices: `ma * (1 + log ma) ≤ ma * log m`. -/
theorem mul_one_add_logb_le {ma m : ℕ} (h : 3 * ma ≤ 2 * m) :
    (ma : ℝ) * (1 + Real.logb (3 / 2) ma) ≤ ma * Real.logb (3 / 2) m := by
  rcases Nat.eq_zero_or_pos ma with rfl | hma
  · simp
  have hm : 0 < m := by omega
  have hma' : (0 : ℝ) < ma := by exact_mod_cast hma
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h' : (ma : ℝ) ≤ m / (3 / 2) := by
    have : (3 : ℝ) * ma ≤ 2 * m := by exact_mod_cast h
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hl : Real.logb (3 / 2) ma ≤ Real.logb (3 / 2) m - 1 := by
    calc Real.logb (3 / 2) ma ≤ Real.logb (3 / 2) (m / (3 / 2)) :=
          Real.logb_le_logb_of_le (by norm_num) hma' h'
      _ = Real.logb (3 / 2) m - 1 := by
          rw [Real.logb_div hm'.ne' (by norm_num), Real.logb_self_eq_one (by norm_num)]
  exact mul_le_mul_of_nonneg_left (by linarith) hma'.le

/-- `∑ over nodes of m ≤ n * (1 + log_{3/2} n)` for shrinking trees. -/
theorem sumNodes_card_le {G : SimpleGraph V} {t : SepTree V} (hd : IsDissection G t)
    (hs : AllNodes Shrinks t) :
    sumNodes (fun s => (s.verts.card : ℝ)) t ≤
      t.verts.card * (1 + Real.logb (3 / 2) t.verts.card) := by
  induction t with
  | leaf s =>
    have := mul_logb_nonneg s.card
    simp only [sumNodes, verts]
    linarith
  | node s a b iha ihb =>
    simp only [sumNodes]
    have ha := (iha hd.2.2.2.2.1 hs.2.1).trans (mul_one_add_logb_le hs.1.1)
    have hb := (ihb hd.2.2.2.2.2 hs.2.2).trans (mul_one_add_logb_le hs.1.2)
    have hab := card_verts_node_le hd
    set m := (node s a b).verts.card
    have key : ((a.verts.card : ℝ) + b.verts.card) * Real.logb (3 / 2) m ≤
        m * Real.logb (3 / 2) m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · have h0 : a.verts.card + b.verts.card = 0 := by omega
        have : (a.verts.card : ℝ) + b.verts.card = 0 := by exact_mod_cast h0
        rw [this, hm]; simp
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab)
          (Real.logb_nonneg (by norm_num) (by exact_mod_cast hm))
    nlinarith

/-! ### The bounds -/

section Bounds

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℕ} {α β : ℝ}

theorem own_mul_sq_le (hα : 0 ≤ α) {s : SepTree V} (h : SqrtBound G α β s) :
    ((s.own.card * (s.own.card + (bdry G s.verts).card) ^ 2 : ℕ) : ℝ) ≤
      α * (α + β) ^ 2 * ((s.verts.card : ℝ) * √(s.verts.card)) := by
  obtain ⟨h1, h2⟩ := h
  set x := √(s.verts.card : ℝ)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hxx : x ^ 2 = s.verts.card := Real.sq_sqrt (Nat.cast_nonneg _)
  have h3 : ((s.own.card : ℝ) + (bdry G s.verts).card) ^ 2 ≤ ((α + β) * x) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  push_cast
  calc (s.own.card : ℝ) * ((s.own.card : ℝ) + (bdry G s.verts).card) ^ 2
      ≤ (α * x) * ((α + β) * x) ^ 2 :=
        mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = α * (α + β) ^ 2 * (x ^ 2 * x) := by ring
    _ = _ := by rw [hxx]

theorem own_mul_le (hα : 0 ≤ α) {s : SepTree V} (h : SqrtBound G α β s) :
    ((s.own.card * (s.own.card + (bdry G s.verts).card) : ℕ) : ℝ) ≤
      α * (α + β) * (s.verts.card : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  set x := √(s.verts.card : ℝ)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hxx : x * x = s.verts.card := Real.mul_self_sqrt (Nat.cast_nonneg _)
  push_cast
  calc (s.own.card : ℝ) * ((s.own.card : ℝ) + (bdry G s.verts).card)
      ≤ (α * x) * ((α + β) * x) :=
        mul_le_mul h1 (by linarith) (by positivity) (by positivity)
    _ = α * (α + β) * (x * x) := by ring
    _ = _ := by rw [hxx]

variable [DecidableRel (fill G r).Adj]

/-- **Work bound for nested dissection**:
`∑ u, (deg⁺ u + 1) ^ 2 ≤ 6 * α * (α + β) ^ 2 * n ^ (3/2)`. -/
theorem sum_sq_le (hα : 0 ≤ α) (t : SepTree V) (hd : IsDissection G t)
    (hc : Consistent r t) (hb : BdryLater G r t) (hsq : AllNodes (SqrtBound G α β) t)
    (hs : AllNodes Shrinks t) :
    ((∑ u ∈ t.verts, ((laterNbrs r (fill G r) u).card + 1) ^ 2 : ℕ) : ℝ) ≤
      6 * α * (α + β) ^ 2 * ((t.verts.card : ℝ) * √(t.verts.card)) := by
  have h1 := sum_laterNbrs_le_sumNodes (fun k => k ^ 2) (fun a b h => Nat.pow_le_pow_left h 2)
    t hd hc hb
  have h1' : ((∑ u ∈ t.verts, ((laterNbrs r (fill G r) u).card + 1) ^ 2 : ℕ) : ℝ) ≤
      ((t.sumNodes fun s => s.own.card * (s.own.card + (bdry G s.verts).card) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [sumNodes_cast] at h1'
  have h2 := sumNodes_le_of_allNodes (fun s hs => own_mul_sq_le hα hs) hsq
  rw [sumNodes_mul_left] at h2
  have h3 := sumNodes_card_mul_sqrt_le hd hs
  have hc0 : 0 ≤ α * (α + β) ^ 2 := by positivity
  calc _ ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ α * (α + β) ^ 2 * (6 * ((t.verts.card : ℝ) * √(t.verts.card))) :=
        mul_le_mul_of_nonneg_left h3 hc0
    _ = _ := by ring

/-- **Fill bound for nested dissection**:
`∑ u, deg⁺ u ≤ α * (α + β) * n * (1 + log_{3/2} n)`. -/
theorem sum_card_laterNbrs_le (hα : 0 ≤ α) (hβ : 0 ≤ β) (t : SepTree V) (hd : IsDissection G t)
    (hc : Consistent r t) (hb : BdryLater G r t) (hsq : AllNodes (SqrtBound G α β) t)
    (hs : AllNodes Shrinks t) :
    ((∑ u ∈ t.verts, (laterNbrs r (fill G r) u).card : ℕ) : ℝ) ≤
      α * (α + β) * (t.verts.card * (1 + Real.logb (3 / 2) t.verts.card)) := by
  have h1 := sum_laterNbrs_le_sumNodes id monotone_id t hd hc hb
  have h0 : ∑ u ∈ t.verts, (laterNbrs r (fill G r) u).card ≤
      ∑ u ∈ t.verts, id ((laterNbrs r (fill G r) u).card + 1) :=
    Finset.sum_le_sum fun u _ => Nat.le_succ _
  have h1' : ((∑ u ∈ t.verts, (laterNbrs r (fill G r) u).card : ℕ) : ℝ) ≤
      ((t.sumNodes fun s => s.own.card * id (s.own.card + (bdry G s.verts).card) : ℕ) : ℝ) := by
    exact_mod_cast h0.trans h1
  rw [sumNodes_cast] at h1'
  have h2 := sumNodes_le_of_allNodes (fun s hs => own_mul_le hα hs) hsq
  rw [sumNodes_mul_left] at h2
  have h3 := sumNodes_card_le hd hs
  calc _ ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

end Bounds

end SepTree

end

end NestedDissection
