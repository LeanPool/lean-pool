/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.Vicious

/-!
# A vicious circle of `Φ(N)` comes from a vicious circle or a cut of `N`, and Proposition 3

Lafont 1997, page 80, third point of the proof of Proposition 3: "if `Φ(ν)` contains a vicious
circle, then `ν` contains a vicious circle or a cut". With the three other points
(`Translation.NetTr.hasCut_reflect`, `Translation.NetTr.hasCut_of_strict`,
`Translation.NetTr.hasVicious`) it gives Proposition 3: "If `ν` is a reduced net, then `Φ(ν)` is a
reduced net. The converse holds if `Φ` is strict."

## How the circle is followed back

A vicious circle of `Φ(N)` is written out (`Net.ChainVicious`) as equations `x₀ = t'₀, …,
xₖ = t'ₖ` with `xᵢ₊₁` a leaf of `t'ᵢ` and `x₀` a leaf of `t'ₖ`. Each of them translates an
equation `aᵢ = bᵢ` of `N`, with `aᵢ` translating to the name `xᵢ` and `bᵢ` to `t'ᵢ`.

* The link `xᵢ₊₁` occurs in `t'ᵢ` and once more in the circle, so only once in `t'ᵢ` by linearity.
  The names that an instance adds occur twice (`ViciousReflect.TermTr.count_parity`), so `xᵢ₊₁` is
  a leaf of the source tree `bᵢ`.
* `aᵢ` is the name `xᵢ`, or a cell whose translation is the wire from its root to its port, with
  `xᵢ` as a leaf. Likewise `bᵢ` is a cell or the name `xᵢ₊₁`.

So each equation of the circle of `N` goes forward (`xᵢ = bᵢ` with `xᵢ₊₁` a leaf of `bᵢ`), goes
backward (`xᵢ₊₁ = aᵢ` with `xᵢ` a leaf of `aᵢ`), or is a cut (`aᵢ` and `bᵢ` are cells). A wire
`xᵢ = xᵢ₊₁` goes both ways. If every equation goes forward, `N` has the same circle. Otherwise
some equation goes backward only: its cell `aᵢ` has its principal port on the wire `xᵢ₊₁`. Follow
the circle from there (`ViciousReflect.walkB`): either the next equations all go backward, and the
circle of `N` is the circle of `Φ(N)` read backwards, or a chain of wires leads from the principal
port of `aᵢ` to the principal port of a cell `bⱼ`, a cut. This is the case of the paper's warning
(`ViciousCheck.translation_circle_from_cut`).

Contents, in the order of the file:

1. Auxiliary lemmas, translated trees: `ViciousReflect.TermTr.count_parity` (the names an
   instance adds occur an even number of times), `ViciousReflect.TermTr.count_eq_of_le_one`,
   `ViciousReflect.TermTr.mem_of_var`.
2. Auxiliary lemmas, linearity: `ViciousReflect.linear_of_cons`,
   `ViciousReflect.linear_of_add_right`.
3. Auxiliary lemmas, chains and paths: `ViciousReflect.cons_chainCut`, `ViciousReflect.path_snoc`,
   `ViciousReflect.link_count`, `ViciousReflect.link_count₀`.
4. Auxiliary lemmas, following the circle back: `ViciousReflect.step` (one equation),
   `ViciousReflect.walkB` (a path, backwards), `ViciousReflect.walkF` (a path, forwards),
   `ViciousReflect.circle_reflect` (a whole circle).
5. Main results: `Translation.NetTr.hasVicious_reflect`, the third point of the proof of
   Proposition 3; `Translation.NetTr.isReduced` and `Translation.NetTr.isReduced_of_strict`,
   Proposition 3 and its converse (page 80).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term Vicious

namespace ViciousReflect

variable {Φ : Translation S S'}

-- ============================================================================================
-- 1. Auxiliary lemmas: translated trees
-- ============================================================================================

/-- The names added by an instance come in pairs (Lafont 1997, Section 1.7, page 80): a name
occurs in a translation as often as in the source tree, plus an even number of times. -/
theorem TermTr.count_parity
    -- a tree `t` and its translation `t'`
    {t : Term S ℕ}
    {t' : Term S' ℕ}
    (h : Φ.TermTr t t')
    -- a name
    (y : ℕ) :
    -- `y` occurs in `t'` as often as in `t`, plus `2 * k` times
    ∃ k, t'.vars.count y = t.vars.count y + 2 * k := by
  induction h with
  | var x => exact ⟨0, rfl⟩
  | app α ts ts' f _ ih =>
    choose k hk using ih
    refine ⟨∑ i, k i + ∑ w, if y = f w then 1 else 0, ?_⟩
    rw [PNet.count_vars_inst, Term.vars_app, Multiset.count_sum',
      Finset.sum_congr rfl fun i _ => hk i, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

/-- A name that occurs at most once in a translation occurs as often in the source tree. -/
theorem TermTr.count_eq_of_le_one
    -- a tree `t` and its translation `t'`
    {t : Term S ℕ}
    {t' : Term S' ℕ}
    (h : Φ.TermTr t t')
    -- a name that occurs at most once in `t'`
    {y : ℕ}
    (hy : t'.vars.count y ≤ 1) :
    t.vars.count y = t'.vars.count y := by
  obtain ⟨k, hk⟩ := TermTr.count_parity h y
  omega

/-- A tree translated to the name `y` has `y` as a leaf: it is `y`, or a tower of cells each
translated to a wire, above `y`. -/
theorem TermTr.mem_of_var
    -- a tree `a` translated to the name `y`
    {a : Term S ℕ}
    {y : ℕ}
    (h : Φ.TermTr a (var y)) :
    y ∈ a.vars := by
  have := TermTr.count_eq_of_le_one h (y := y) (by simp)
  simp only [Term.vars_var, Multiset.count_singleton_self] at this
  exact Multiset.one_le_count_iff_mem.1 this.ge

-- ============================================================================================
-- 2. Auxiliary lemmas: linearity
-- ============================================================================================

/-- A net contained in a linear net is linear. -/
theorem linear_of_cons
    -- an equation `e` and a net `M`, together linear
    {e : Sym2 (Term S' ℕ)}
    {M : Net S' ℕ}
    (h : Net.Linear (e ::ₘ M)) :
    M.Linear := fun v => by
  have := h v
  rw [Net.vars_cons, Multiset.count_add] at this
  omega

/-- A net contained in a linear net is linear. -/
theorem linear_of_add_right
    -- two nets `N` and `D`, together linear
    {N D : Net S' ℕ}
    (h : (N + D).Linear) :
    N.Linear := fun v => by
  have := h v
  rw [Net.vars_add, Multiset.count_add] at this
  omega

-- ============================================================================================
-- 3. Auxiliary lemmas: chains and paths
-- ============================================================================================

/-- A written cut stays one when an equation is added. -/
theorem cons_chainCut
    -- a net with a written cut
    {C : Net S ℕ}
    (h : C.ChainCut)
    -- the equation added
    (e : Sym2 (Term S ℕ)) :
    Net.ChainCut (e ::ₘ C) := by
  have := h.add_right {e}
  rwa [add_comm, Multiset.singleton_add] at this

/-- A path from `z` to `y₁`, followed by an equation `y₁ = r` with `y` a leaf of `r`, is a path
from `z` to `y`. -/
theorem path_snoc
    -- a path `C` from `z` to `y₁`
    {C : Net S ℕ}
    {z y₁ y : ℕ}
    {r : Term S ℕ}
    (hP : Path C z y₁)
    -- the equation `y₁ = r`, with `y` a leaf of `r`
    (hy : y ∈ r.vars) :
    Path (s(r, var y₁) ::ₘ C) z y := by
  have := Path.append (Path.cons hy (Path.nil y) : Path (s(var y₁, r) ::ₘ 0) y₁ y) hP
  rw [Multiset.add_cons, add_zero] at this
  rwa [Sym2.eq_swap]

/-- The link `y₁` after an equation `y = t` of a path occurs once in `t`: it occurs again in the
rest of the path, or it is the end `z`, which occurs in the equation `z = u`. -/
theorem link_count
    -- the rest `C₀` of the path, from `y₁` to `z`
    {C₀ : Net S' ℕ}
    {y y₁ z : ℕ}
    {t u : Term S' ℕ}
    (hC₀ : Path C₀ y₁ z)
    -- the equation `z = u`, the equation `y = t` and `C₀` are together linear
    (hlin : Net.Linear (s(var z, u) ::ₘ s(var y, t) ::ₘ C₀)) :
    t.vars.count y₁ ≤ 1 := by
  rcases hC₀.mem_vars with ⟨rfl, h1⟩ | ⟨hm, -⟩
  · have h := hlin z
    simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self, Net.vars_zero, Multiset.count_zero] at h
    rw [h1]
    omega
  · have h := hlin y₁
    have := Multiset.one_le_count_iff_mem.2 hm
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at h
    omega

/-- The first link `y` of a circle `x = t, …` occurs once in `t`. -/
theorem link_count₀
    -- the rest `C'` of the circle, a path from `y` back to `x`
    {C' : Net S' ℕ}
    {x y : ℕ}
    {t : Term S' ℕ}
    (hC : Path C' y x)
    -- the circle, `x = t` followed by `C'`, is linear
    (hlin : Net.Linear (s(var x, t) ::ₘ C')) :
    t.vars.count y ≤ 1 := by
  rcases hC.mem_vars with ⟨rfl, h1⟩ | ⟨hm, -⟩
  · have h := hlin x
    simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self, Net.vars_zero, Multiset.count_zero] at h
    rw [h1]
    omega
  · have h := hlin y
    have := Multiset.one_le_count_iff_mem.2 hm
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add] at h
    omega

-- ============================================================================================
-- 4. Auxiliary lemmas: following the circle back
-- ============================================================================================

/-- **One equation of a circle, followed back** (Lafont 1997, page 80). If `e` translates to
`y = t`, and the next link `y₁` is a leaf of `t` that occurs once in it, then `e` is `a = b` with
`y₁` a leaf of `b`, `a` the name `y` or a cell with leaf `y`, and `b` a cell or the name `y₁`. -/
theorem step
    -- an equation `e` of the source, translated to `y = t`
    {e : Sym2 (Term S ℕ)}
    {y y₁ : ℕ}
    {t : Term S' ℕ}
    (he : Φ.EqTr e s(var y, t))
    -- the next link `y₁`, a leaf of `t` that occurs once in it
    (hy₁ : y₁ ∈ t.vars)
    (hc : t.vars.count y₁ ≤ 1) :
    -- `e` is an equation `a = b` with `y₁` a leaf of `b`,
    ∃ a b, e = s(a, b) ∧ y₁ ∈ b.vars ∧
      -- `a` is the name `y`, or a cell with leaf `y`,
      (a = var y ∨ (a.IsCell ∧ y ∈ a.vars)) ∧
      -- and `b` is a cell, or the name `y₁` (and then `t` is `y₁` too)
      (b.IsCell ∨ (b = var y₁ ∧ t = var y₁)) := by
  obtain ⟨a, b, rfl, ha, hb⟩ := Cut.EqTr.inv he
  refine ⟨a, b, rfl, ?_, ?_, ?_⟩
  · rw [← Multiset.one_le_count_iff_mem, TermTr.count_eq_of_le_one hb hc]
    exact Multiset.one_le_count_iff_mem.2 hy₁
  · cases a with
    | var v => exact Or.inl (by rw [Cut.TermTr.var_var ha])
    | app α ts => exact Or.inr ⟨⟨α, ts, rfl⟩, TermTr.mem_of_var ha⟩
  · cases b with
    | var v =>
      cases hb
      have hv : y₁ = v := by simpa using hy₁
      subst hv
      exact Or.inr ⟨rfl, rfl⟩
    | app β us => exact Or.inl ⟨β, us, rfl⟩

/-- **Following a path backwards** (Lafont 1997, page 80). If the equations `C` translate a path
`y = t₁, y₁ = t₂, …` from `y` to `z`, then `C` has a written cut, or a chain of wires from the
name `y` to the principal port of a cell, or every equation goes backward and `C` is a path from
`z` to `y`. -/
theorem walkB
    -- a path `C'` of the translation, from `y` to `z`
    {C' : Net S' ℕ}
    {y z : ℕ}
    (hP : Path C' y z) :
    -- for source equations `C` translated to `C'`, and an equation `z = u`,
    ∀ (C : Net S ℕ) (u : Term S' ℕ), Multiset.Rel Φ.EqTr C C' →
      -- if `z = u` and `C'` are together linear,
      Net.Linear (s(var z, u) ::ₘ C') →
      -- then `C` has a written cut,
      C.ChainCut
      -- or a chain of wires `zs` from the name `y` to a cell `b`, and the rest `D`,
      ∨ (∃ zs b D, b.IsCell ∧ C = Cut.chain (var y) zs b + D)
      -- or `C` is a path from `z` back to `y`
      ∨ Path C z y := by
  induction hP with
  | nil x =>
    intro C u h _
    rw [Multiset.rel_zero_right] at h
    subst h
    exact Or.inr (Or.inr (.nil x))
  | @cons y y₁ z t C₀ hy₁ hC₀ ih =>
    intro C u h hlin
    rw [Multiset.rel_cons_right] at h
    obtain ⟨e, C₁, he, h₁, rfl⟩ := h
    have hlin₁ : Net.Linear (s(var z, u) ::ₘ C₀) :=
      linear_of_cons (hlin.cast (Multiset.cons_swap _ _ _))
    obtain ⟨a, b, rfl, hb₁, ha, hb⟩ := step he hy₁ (link_count hC₀ hlin)
    have IH := ih C₁ u h₁ hlin₁
    rcases ha with rfl | ⟨ha, hya⟩
    · rcases hb with hb | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨[], b, C₁, hb, by simp⟩)
      · rcases IH with hc | ⟨zs, b', D, hb', rfl⟩ | hP'
        · exact Or.inl (cons_chainCut hc _)
        · exact Or.inr (Or.inl ⟨y₁ :: zs, b', D, hb', by rw [Cut.chain_cons, Multiset.cons_add]⟩)
        · exact Or.inr (Or.inr (path_snoc hP' (by simp)))
    · rcases hb with hb | ⟨rfl, rfl⟩
      · obtain ⟨α, ts, rfl⟩ := ha
        obtain ⟨β, us, rfl⟩ := hb
        exact Or.inl (Net.chainCut_of_mem (Multiset.mem_cons_self _ _))
      · rcases IH with hc | ⟨zs, b', D, hb', rfl⟩ | hP'
        · exact Or.inl (cons_chainCut hc _)
        · exact Or.inl ⟨a, b', y₁ :: zs, D, ha, hb', by rw [Cut.chain_cons, Multiset.cons_add]⟩
        · exact Or.inr (Or.inr (path_snoc hP' hya))

/-- **Following a path forwards** (Lafont 1997, page 80). If the equations `C` translate a path
from `y` to `z`, then `C` has a written cut, or every equation goes forward and `C` is a path from
`y` to `z`, or some equation `a = w` goes backward only: `a` is a cell translated to the link
`x' = w` of the path, with `x'` a leaf of `a`. The path is then cut at that link into a path from
`y` to `x'` and a path from `w` to `z`, translated by the other equations. -/
theorem walkF
    -- a path `C'` of the translation, from `y` to `z`
    {C' : Net S' ℕ}
    {y z : ℕ}
    (hP : Path C' y z) :
    -- for source equations `C` translated to `C'`, and an equation `z = u`,
    ∀ (C : Net S ℕ) (u : Term S' ℕ), Multiset.Rel Φ.EqTr C C' →
      -- if `z = u` and `C'` are together linear,
      Net.Linear (s(var z, u) ::ₘ C') →
      -- then `C` has a written cut,
      C.ChainCut
      -- or `C` is a path from `y` to `z`,
      ∨ Path C y z
      -- or some equation `a = w` of `C` goes backward only, `a` a cell with leaf `x'`,
      ∨ ∃ (x' w : ℕ) (a : Term S ℕ) (C₁ : Net S ℕ) (C₁' C₂' : Net S' ℕ), a.IsCell ∧
          x' ∈ a.vars ∧ C = s(a, var w) ::ₘ C₁ ∧
          -- the other equations `C₁` translate two pieces `C₁'` and `C₂'` of the path,
          Multiset.Rel Φ.EqTr C₁ (C₁' + C₂') ∧
          -- a path `C₁'` from `y` to `x'` and a path `C₂'` from `w` to `z`,
          Path C₁' y x' ∧ Path C₂' w z ∧
          -- and the path `C'` is the two pieces joined by the link `x' = w`
          C' = s(var x', var w) ::ₘ (C₁' + C₂') := by
  induction hP with
  | nil x =>
    intro C u h _
    rw [Multiset.rel_zero_right] at h
    subst h
    exact Or.inr (Or.inl (.nil x))
  | @cons y y₁ z t C₀ hy₁ hC₀ ih =>
    intro C u h hlin
    rw [Multiset.rel_cons_right] at h
    obtain ⟨e, C₁, he, h₁, rfl⟩ := h
    have hlin₁ : Net.Linear (s(var z, u) ::ₘ C₀) :=
      linear_of_cons (hlin.cast (Multiset.cons_swap _ _ _))
    obtain ⟨a, b, rfl, hb₁, ha, hb⟩ := step he hy₁ (link_count hC₀ hlin)
    rcases ha with rfl | ⟨ha, hya⟩
    · rcases ih C₁ u h₁ hlin₁ with hc | hP' |
        ⟨x', w, a₂, C₂, C₁', C₂', ha₂, hx', rfl, hr, hP₁, hP₂, rfl⟩
      · exact Or.inl (cons_chainCut hc _)
      · exact Or.inr (Or.inl (.cons hb₁ hP'))
      · refine Or.inr (Or.inr ⟨x', w, a₂, s(var y, b) ::ₘ C₂, s(var y, t) ::ₘ C₁', C₂', ha₂, hx',
          Multiset.cons_swap _ _ _, ?_, .cons hy₁ hP₁, hP₂, ?_⟩)
        · rw [Multiset.cons_add]
          exact Multiset.Rel.cons he hr
        · rw [Multiset.cons_add, Multiset.cons_swap]
    · rcases hb with hb | ⟨rfl, rfl⟩
      · obtain ⟨α, ts, rfl⟩ := ha
        obtain ⟨β, us, rfl⟩ := hb
        exact Or.inl (Net.chainCut_of_mem (Multiset.mem_cons_self _ _))
      · exact Or.inr (Or.inr ⟨y, y₁, a, C₁, 0, C₀, ha, hya, rfl, by rwa [zero_add], .nil y, hC₀,
          by rw [zero_add]⟩)

/-- The source equations of a written vicious circle of the translation contain a written vicious
circle or a written cut (Lafont 1997, page 80). -/
theorem circle_reflect
    -- a written circle of the translation: `x = t`, a leaf `y` of `t`, a path `C'` from `y` to `x`
    {x y : ℕ}
    {t : Term S' ℕ}
    {C' : Net S' ℕ}
    (hy : y ∈ t.vars)
    (hC' : Path C' y x)
    -- the circle is linear
    (hlinK : Net.Linear (s(var x, t) ::ₘ C'))
    -- the source equations `C`, translated to the circle
    {C : Net S ℕ}
    (hC : Multiset.Rel Φ.EqTr C (s(var x, t) ::ₘ C')) :
    -- `C` has a written vicious circle or a written cut
    C.ChainVicious ∨ C.ChainCut := by
  rw [Multiset.rel_cons_right] at hC
  obtain ⟨e, C₁, he, h₁, rfl⟩ := hC
  obtain ⟨a₀, b₀, rfl, hb₀, ha₀, hb₀'⟩ := step he hy (link_count₀ hC' hlinK)
  rcases ha₀ with rfl | ⟨ha₀, hxa⟩
  · rcases walkF hC' C₁ t h₁ hlinK with hc | hP |
      ⟨x', w, a, C₂, C₁', C₂', ha, hx', rfl, hr, hP₁, hP₂, rfl⟩
    · exact Or.inr (cons_chainCut hc _)
    · exact Or.inl ⟨_, 0, ⟨x, y, b₀, C₁, hb₀, hP, rfl⟩, (add_zero _).symm⟩
    · have hP := Path.append (Path.cons hy hP₁ : Path (s(var x, t) ::ₘ C₁') x x') hP₂
      have hr' : Multiset.Rel Φ.EqTr (s(var x, b₀) ::ₘ C₂) (C₂' + s(var x, t) ::ₘ C₁') := by
        rw [Multiset.add_cons, add_comm]
        exact Multiset.Rel.cons he hr
      have hlin' : Net.Linear (s(var x', var w) ::ₘ (C₂' + s(var x, t) ::ₘ C₁')) := by
        refine hlinK.cast ?_
        rw [Multiset.add_cons, add_comm C₂' C₁', Multiset.cons_swap]
      rcases walkB hP _ _ hr' hlin' with hc | ⟨zs, b, D₀, hb, hD⟩ | hP'
      · refine Or.inr ?_
        rw [Multiset.cons_swap]
        exact cons_chainCut hc _
      · refine Or.inr ⟨a, b, w :: zs, D₀, ha, hb, ?_⟩
        rw [Multiset.cons_swap, hD, Cut.chain_cons, Multiset.cons_add]
      · refine Or.inl ⟨_, 0, ⟨w, x', a, _, hx', hP', rfl⟩, ?_⟩
        rw [add_zero, Multiset.cons_swap, Sym2.eq_swap (a := a)]
  · rcases hb₀' with hb | ⟨rfl, rfl⟩
    · obtain ⟨α, ts, rfl⟩ := ha₀
      obtain ⟨β, us, rfl⟩ := hb
      exact Or.inr (Net.chainCut_of_mem (Multiset.mem_cons_self _ _))
    · rcases walkB hC' C₁ (var y) h₁ hlinK with hc | ⟨zs, b, D₀, hb, rfl⟩ | hP
      · exact Or.inr (cons_chainCut hc _)
      · exact Or.inr ⟨a₀, b, y :: zs, D₀, ha₀, hb, by rw [Cut.chain_cons, Multiset.cons_add]⟩
      · exact Or.inl ⟨_, 0, ⟨y, x, a₀, C₁, hxa, hP, rfl⟩, by rw [add_zero, Sym2.eq_swap]⟩

end ViciousReflect

open ViciousReflect

-- ============================================================================================
-- 5. Main results: vicious circles are reflected, and Proposition 3
-- ============================================================================================

/-- **A vicious circle of the translation comes from a vicious circle or a cut** (Lafont 1997,
Proposition 3, third point of the proof, page 80): if `N'` translates `N` and `N'` has a vicious
circle, then `N` has a vicious circle or a cut. No strictness is needed.

The circle of `N'` is written out (`Net.HasVicious.chainVicious`) and followed back in `N`
(`ViciousReflect.circle_reflect`). Its links are leaves of the source trees, because the names an
instance adds occur twice in it. A cell of `N` translated to a wire can turn the circle around:
then a chain of wires joins its principal port to the principal port of another cell, a cut, or
the whole circle of `N` runs backwards. -/
theorem Translation.NetTr.hasVicious_reflect
    -- a translation, a net `N` and its translation `N'`
    {Φ : Translation S S'}
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `N'` has a vicious circle
    (hv : N'.HasVicious) :
    -- `N` has a vicious circle or a cut
    N.HasVicious ∨ N.HasCut := by
  obtain ⟨K', D', ⟨x, y, t, C', hy, hC', rfl⟩, hN'⟩ := hv.chainVicious
  have hrel := h.rel
  rw [hN'] at hrel
  obtain ⟨C, D, hC, -, rfl⟩ := Multiset.rel_add_right.1 hrel
  have hlinK : Net.Linear (s(var x, t) ::ₘ C') := linear_of_add_right (h.linear.cast hN')
  rcases circle_reflect hy hC' hlinK hC with hs | hs
  · exact Or.inl ((hs.add_right D).hasVicious h.linear_source)
  · exact Or.inr ((hs.add_right D).hasCut h.linear_source)

/-- **Proposition 3** (Lafont 1997, page 80): "If `ν` is a reduced net, then `Φ(ν)` is a reduced
net." Any translation: a cut of `Φ(ν)` comes from a cut of `ν` (`NetTr.hasCut_reflect`), a vicious
circle of `Φ(ν)` from a vicious circle or a cut of `ν` (`NetTr.hasVicious_reflect`). -/
theorem Translation.NetTr.isReduced
    -- a translation, a net `N` and its translation `N'`
    {Φ : Translation S S'}
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `N` is reduced
    (hN : N.IsReduced) :
    N'.IsReduced :=
  ⟨fun hc => hN.1 (h.hasCut_reflect hc), fun hv => (h.hasVicious_reflect hv).elim hN.2 hN.1⟩

/-- **Proposition 3, the converse** (Lafont 1997, page 80): "The converse holds if `Φ` is strict."
A cut of `ν` gives a cut of `Φ(ν)` when `Φ` is strict (`NetTr.hasCut_of_strict`), and a vicious
circle of `ν` gives one of `Φ(ν)` (`NetTr.hasVicious`). -/
theorem Translation.NetTr.isReduced_of_strict
    -- a strict translation
    {Φ : Translation S S'}
    (hΦ : Φ.Strict)
    -- a net `N` and its translation `N'`
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `N'` is reduced
    (hN' : N'.IsReduced) :
    N.IsReduced :=
  ⟨fun hc => hN'.1 (h.hasCut_of_strict hΦ hc), fun hv => hN'.2 (h.hasVicious hv)⟩

end INet
