/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.CutChain

/-!
# Vicious circles and reduced nets (page 79), and a translation keeps vicious circles (page 80)

Lafont 1997, page 79: "A principal path of length `n` consists of `n` cells `c₁, …, cₙ` such that
the principal port of `cᵢ` is connected to an auxiliary port of `cᵢ₊₁`. […] A vicious circle of
length `n` is a closed principal path of length `n`. In particular, a cyclic wire can be considered
as a vicious circle of length 0. […] Say that a net is reduced if it contains no cut and no vicious
circle."

## How a vicious circle is written

In a tree every cell has its principal port on the auxiliary port of the cell above it, so the path
from a leaf of a tree up to its root is a principal path. A vicious circle written directly is
therefore an equation

  `x = t`   with `x` a leaf of `t`,

the root of `t` being plugged into one of its own leaves. If `t` is a cell, the cells of `t` from
the leaf `x` up to the root are the circle; if `t` is the name `x` itself, the equation `x = x` is a
cyclic wire, a vicious circle of length 0. This is how a non-strict translation creates cyclic
wires (page 80): if `Φ(α)` is the wire from the root to the port, `x = α(x)` becomes `x = x`. The
equation `x = x` is linear and no wire substitution applies to it, so it stays in the net as a
closed loop.

Contents, in the order of the file:

1. Definitions: `Net.HasVicious` (some net equivalent to `N` has an equation `x = t` with `x` a
   leaf of `t`); `Net.IsReduced` (no cut and no vicious circle); `Vicious.Path`, a principal path
   written out; `Vicious.IsCircle`, a closed one; `Net.ChainVicious`, a vicious circle on the
   text itself: equations `x₀ = t₀, x₁ = t₁, …, xₖ = tₖ` with `xᵢ₊₁` a leaf of `tᵢ` and `x₀` a
   leaf of `tₖ`.
2. Auxiliary lemmas, vicious circles and reduced nets up to wires: `Net.hasVicious_of_mem`,
   `Net.HasVicious.of_equiv`, `Net.hasVicious_iff_of_equiv`, `Net.IsReduced.of_equiv`,
   `Net.isReduced_iff_of_equiv`.
3. Auxiliary lemmas, principal paths: `Vicious.mem_subst_of_ne`, `Vicious.mem_subst_of_mem`,
   `Vicious.Path.append`, `Vicious.Path.mem_vars`, `Vicious.Path.eq_of_zero`,
   `Vicious.Path.split`, `Vicious.Path.snoc`, `Vicious.Path.sub`, `Vicious.IsCircle.rotate`,
   `Vicious.circle_count`.
4. Auxiliary lemmas, written circles: `Net.chainVicious_of_mem`, `Net.ChainVicious.add_right`,
   `Net.hasVicious_contract`, `Net.ChainVicious.hasVicious` (in a linear net a written circle is
   a vicious circle).
5. Auxiliary lemmas, wire substitution: a wire substitution, in either direction, keeps a
   written circle (`Vicious.Wire.chainVicious`, `Vicious.chainVicious_unsub`,
   `Vicious.Wire.chainVicious_symm`, `Vicious.Equiv.chainVicious_iff`).
6. Main results: `Net.HasVicious.chainVicious` and `Net.hasVicious_iff_chainVicious` (for a
   linear net, a vicious circle is the same as a written one); `Net.isReduced_tree` (a tree
   plugged into a free port is reduced); `Translation.NetTr.hasVicious`, the fourth point of the
   proof of Proposition 3: if `N` has a vicious circle, so has `Φ(N)`, for any translation.
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace Net

/-- A net has a vicious circle (Lafont 1997, page 79): some net that is the same graph as `N` has
an equation `x = t` whose name `x` is a leaf of `t`. The leaves of `t` reach its root by a principal
path, so the root of `t`, plugged into `x`, closes it. With `t = x` it is a cyclic wire, a vicious
circle of length 0. -/
def HasVicious
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- there is a net `N'`, the same graph as `N`,
  ∃ N', Equiv N N' ∧
    -- with an equation `x = t` where `x` is a leaf of `t`
    ∃ (x : ℕ) (t : Term S ℕ), x ∈ t.vars ∧ s(var x, t) ∈ N'

/-- A reduced net (Lafont 1997, page 79): it contains no cut and no vicious circle. (Not to be
confused with `Rule.Reduced`, a syntactic form of the right members of rules.) -/
def IsReduced
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- no cut and no vicious circle
  ¬ N.HasCut ∧ ¬ N.HasVicious

end Net

namespace Vicious

/-- A principal path written out, between the names `x` and `z` (Lafont 1997, page 79): equations
`x = t₁, y₁ = t₂, …, yₖ₋₁ = tₖ` with `y₁` a leaf of `t₁`, `y₂` a leaf of `t₂`, …, and `z` a leaf
of `tₖ`. Read backwards it climbs from `z` to `x`: from a leaf of each tree to its root, then along
the wire to a leaf of the previous tree. With no equation, `x = z`. -/
inductive Path : Net S ℕ → ℕ → ℕ → Prop
  -- no equation: a path from `x` to itself
  | nil (x : ℕ) : Path 0 x x
  -- an equation `x = t` with `y` a leaf of `t`, followed by a path `C` from `y` to `z`
  | cons {x y z : ℕ} {t : Term S ℕ} {C : Net S ℕ} : y ∈ t.vars → Path C y z →
      Path (s(var x, t) ::ₘ C) x z

/-- A vicious circle written out (Lafont 1997, page 79): a closed path, `x = t` followed by a path
from a leaf `y` of `t` back to `x`. -/
def IsCircle
    -- the equations of the circle
    (K : Net S ℕ) :
    Prop :=
  -- there are an equation `x = t` and a leaf `y` of `t`
  ∃ x y t C, y ∈ t.vars ∧
    -- and a path `C` from `y` back to `x`
    Path C y x ∧
    -- and the circle is `x = t` followed by `C`
    K = s(var x, t) ::ₘ C

end Vicious

open Vicious

namespace Net

/-- A vicious circle written out on the text (Lafont 1997, page 79): equations
`x₀ = t₀, x₁ = t₁, …, xₖ = tₖ` among those of `N`, with `xᵢ₊₁` a leaf of `tᵢ` and `x₀` a leaf of
`tₖ`. -/
def ChainVicious
    -- the net
    (N : Net S ℕ) :
    Prop :=
  -- `N` is a written circle `K` together with the rest `D` of the net
  ∃ K D, IsCircle K ∧ N = K + D

-- ============================================================================================
-- 2. Auxiliary lemmas: vicious circles and reduced nets up to wires
-- ============================================================================================

/-- An equation `x = t` with `x` a leaf of `t` is a vicious circle (Lafont 1997, page 79). -/
theorem hasVicious_of_mem
    -- the net
    {N : Net S ℕ}
    -- an equation `x = t` of `N`, with `x` a leaf of `t`
    {x : ℕ}
    {t : Term S ℕ}
    (hx : x ∈ t.vars)
    (h : s(var x, t) ∈ N) :
    N.HasVicious :=
  ⟨N, Equiv.refl N, x, t, hx, h⟩

/-- Having a vicious circle is a property of the graph (Lafont 1997, page 79): it does not change
under wire substitution. -/
theorem HasVicious.of_equiv
    -- two nets, the first with a vicious circle
    {N M : Net S ℕ}
    (h : N.HasVicious)
    -- they are the same graph
    (e : Equiv N M) :
    M.HasVicious := by
  obtain ⟨N', hE, rest⟩ := h
  exact ⟨N', e.symm.trans hE, rest⟩

/-- Equivalent nets have a vicious circle together (Lafont 1997, page 79). -/
theorem hasVicious_iff_of_equiv
    -- two nets that are the same graph
    {N M : Net S ℕ}
    (e : Equiv N M) :
    N.HasVicious ↔ M.HasVicious :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

/-- Being reduced is a property of the graph (Lafont 1997, page 79). -/
theorem IsReduced.of_equiv
    -- two nets, the first reduced
    {N M : Net S ℕ}
    (h : N.IsReduced)
    -- they are the same graph
    (e : Equiv N M) :
    M.IsReduced :=
  ⟨fun hc => h.1 (hc.of_equiv e.symm), fun hv => h.2 (hv.of_equiv e.symm)⟩

/-- Equivalent nets are reduced together (Lafont 1997, page 79). -/
theorem isReduced_iff_of_equiv
    -- two nets that are the same graph
    {N M : Net S ℕ}
    (e : Equiv N M) :
    N.IsReduced ↔ M.IsReduced :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

end Net

-- ============================================================================================
-- 3. Auxiliary lemmas: principal paths
-- ============================================================================================

namespace Vicious

/-- A leaf of `r` other than `w` stays a leaf when a tree is plugged into `w`. -/
theorem mem_subst_of_ne
    -- the tree `r`, the name `w`, and a leaf `y` of `r` other than `w`
    {r : Term S ℕ}
    {w y : ℕ}
    -- the tree plugged into `w`
    (u : Term S ℕ)
    (hy : y ∈ r.vars)
    (h : y ≠ w) :
    y ∈ (r.subst w u).vars := by
  have h1 := Multiset.one_le_count_iff_mem.2 hy
  refine Multiset.one_le_count_iff_mem.1 ?_
  rw [Term.count_vars_subst, ite_eq_right_iff.2 (fun h' => absurd h' h)]
  omega

/-- Plugging `u` into a leaf `w` of `r` makes the leaves of `u` leaves of the result. -/
theorem mem_subst_of_mem
    -- the tree `r` with a leaf `w`, and the tree `u` with a leaf `y`
    {r u : Term S ℕ}
    {w y : ℕ}
    (hw : w ∈ r.vars)
    (hy : y ∈ u.vars) :
    y ∈ (r.subst w u).vars := by
  have h1 := Multiset.one_le_count_iff_mem.2 hw
  have h2 := Multiset.one_le_count_iff_mem.2 hy
  have := Nat.mul_le_mul h1 h2
  refine Multiset.one_le_count_iff_mem.1 ?_
  rw [Term.count_vars_subst]
  omega

/-- Two paths, end to end. -/
theorem Path.append
    -- the second path, from `y` to `z`
    {C' : Net S ℕ}
    {y z : ℕ}
    (h' : Path C' y z) :
    -- a path from `x` to `y`, followed by it, is a path from `x` to `z`
    ∀ {C : Net S ℕ} {x : ℕ}, Path C x y → Path (C + C') x z
  | _, _, .nil _ => by simpa using h'
  | _, _, .cons hy h => by rw [Multiset.cons_add]; exact .cons hy (Path.append h' h)

/-- The ends of a path are names of it, unless it is empty. -/
theorem Path.mem_vars
    -- a path from `y` to `z`
    {C : Net S ℕ}
    {y z : ℕ}
    (h : Path C y z) :
    -- either it is empty and `y = z`,
    (C = 0 ∧ y = z)
    -- or `y` and `z` are names of it
      ∨ (y ∈ Net.vars C ∧ z ∈ Net.vars C) := by
  induction h with
  | nil x => exact Or.inl ⟨rfl, rfl⟩
  | @cons x y z t C hy _ ih =>
    refine Or.inr ⟨by simp, ?_⟩
    rcases ih with ⟨rfl, rfl⟩ | ⟨-, hz⟩
    · simp [hy]
    · simp [hz]

/-- An empty path has equal ends. -/
theorem Path.eq_of_zero
    -- an empty path from `y` to `z`
    {y z : ℕ}
    (h : Path (0 : Net S ℕ) y z) :
    y = z := by
  rcases h.mem_vars with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · simp at h

/-- Cutting a path at one of its equations `x₁ = t₁`: a path before it, ending at `x₁`, and a path
after it, starting at a leaf `y₁` of `t₁`. -/
theorem Path.split
    -- an equation `e` of a path `C` from `x` to `z`
    {e : Sym2 (Term S ℕ)}
    {C : Net S ℕ}
    {x z : ℕ}
    (h : Path C x z)
    (he : e ∈ C) :
    -- `e` is an equation `x₁ = t` with a leaf `y₁` of `t`,
    ∃ x₁ y₁ t C₁ C₂, e = s(var x₁, t) ∧ y₁ ∈ t.vars ∧
      -- `C₁` is a path from `x` to `x₁` and `C₂` a path from `y₁` to `z`,
      Path C₁ x x₁ ∧ Path C₂ y₁ z ∧
      -- and `C` is made of `e`, `C₁` and `C₂`
      C = e ::ₘ (C₁ + C₂) := by
  induction h with
  | nil x => simp at he
  | @cons x y z t C hy hC ih =>
    rcases Multiset.mem_cons.1 he with rfl | he'
    · exact ⟨x, y, t, 0, C, rfl, hy, .nil x, hC, by simp⟩
    · obtain ⟨x₁, y₁, t₁, C₁, C₂, rfl, hy₁, hC₁, hC₂, rfl⟩ := ih he'
      refine ⟨x₁, y₁, t₁, s(var x, t) ::ₘ C₁, C₂, rfl, hy₁, .cons hy hC₁, hC₂, ?_⟩
      rw [Multiset.cons_swap, Multiset.cons_add]

/-- The last equation of a nonempty path. -/
theorem Path.snoc
    -- a nonempty path from `y` to `z`
    {C : Net S ℕ}
    {y z : ℕ}
    (h : Path C y z)
    (hC : C ≠ 0) :
    -- there is an equation `x₁ = t` with `z` a leaf of `t`,
    ∃ x₁ t C₁, z ∈ t.vars ∧
      -- after a path `C₁` from `y` to `x₁`,
      Path C₁ y x₁ ∧
      -- and `C` is `C₁` with that equation
      C = s(var x₁, t) ::ₘ C₁ := by
  induction h with
  | nil x => exact absurd rfl hC
  | @cons x y z t C hy hC' ih =>
    rcases hC' with _ | ⟨hy₂, hC₂⟩
    · exact ⟨x, t, 0, hy, .nil x, rfl⟩
    · obtain ⟨x₁, t₁, C₁, hz, hC₁, e⟩ := ih (Multiset.cons_ne_zero)
      refine ⟨x₁, t₁, s(var x, t) ::ₘ C₁, hz, .cons hy hC₁, ?_⟩
      rw [e, Multiset.cons_swap]

/-- Plugging a tree into a name of a path that is neither an end nor a link keeps the path. -/
theorem Path.sub
    -- a path from `y` to `z`, and the tree `u` plugged into `w`
    {C : Net S ℕ}
    {y z w : ℕ}
    (u : Term S ℕ)
    (h : Path C y z)
    -- `w` is not an end of the path, and occurs at most once in it
    (hy : w ≠ y)
    (hz : w ≠ z)
    (hc : (Net.vars C).count w ≤ 1) :
    Path (Cut.sub C w u) y z := by
  induction h with
  | nil x => simpa [Cut.sub] using Path.nil (S := S) x
  | @cons x y' z t C hy' hC ih =>
    rw [Net.vars_cons, eqVars_mk, Multiset.count_add, Multiset.count_add] at hc
    have hyw : y' ≠ w := by
      rintro rfl
      rcases hC.mem_vars with ⟨-, rfl⟩ | ⟨hm, -⟩
      · exact hz rfl
      · have := Multiset.one_le_count_iff_mem.2 hm
        have := Multiset.one_le_count_iff_mem.2 hy'
        omega
    rw [Cut.sub_cons, Cut.subst_var_ne (Ne.symm hy)]
    exact .cons (mem_subst_of_ne u hy' hyw) (ih (Ne.symm hyw) hz (by omega))

/-- A circle can start at any of its equations. -/
theorem IsCircle.rotate
    -- an equation `e` of a circle `K`
    {K : Net S ℕ}
    {e : Sym2 (Term S ℕ)}
    (h : IsCircle K)
    (he : e ∈ K) :
    -- `e` is an equation `x = t` with a leaf `y` of `t`,
    ∃ x y t C, e = s(var x, t) ∧ y ∈ t.vars ∧
      -- `C` is a path from `y` back to `x`,
      Path C y x ∧
      -- and the circle is `e` followed by `C`
      K = e ::ₘ C := by
  obtain ⟨x, y, t, C, hy, hC, rfl⟩ := h
  obtain ⟨x₁, y₁, t₁, C₁, C₂, rfl, hy₁, hC₁, hC₂, e⟩ := (Path.cons hy hC).split he
  exact ⟨x₁, y₁, t₁, C₂ + C₁, rfl, hy₁, hC₁.append hC₂, by rw [e, add_comm C₁]⟩

/-- The two names of the first equation `x = t` of a circle, its root `x` and the next link `y`,
occur twice in the circle. -/
theorem circle_count
    -- the circle: an equation `x = t`, a leaf `y` of `t`, and a path `C` from `y` back to `x`
    {x y : ℕ}
    {t : Term S ℕ}
    {C : Net S ℕ}
    (hy : y ∈ t.vars)
    (hC : Path C y x) :
    -- `x` occurs at least twice in the circle,
    2 ≤ (Net.vars (s(var x, t) ::ₘ C)).count x
    -- and so does `y`
      ∧ 2 ≤ (Net.vars (s(var x, t) ::ₘ C)).count y := by
  have h1 := Multiset.one_le_count_iff_mem.2 hy
  rcases hC.mem_vars with ⟨rfl, rfl⟩ | ⟨hm, hm'⟩
  · simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self, Net.vars_zero, Multiset.count_zero]
    omega
  · simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self]
    have := Multiset.one_le_count_iff_mem.2 hm
    have := Multiset.one_le_count_iff_mem.2 hm'
    omega

end Vicious

-- ============================================================================================
-- 4. Auxiliary lemmas: written circles
-- ============================================================================================

namespace Net

/-- An equation `x = t` with `x` a leaf of `t` is a written vicious circle. -/
theorem chainVicious_of_mem
    -- the net
    {N : Net S ℕ}
    -- an equation `x = t` of `N`, with `x` a leaf of `t`
    {x : ℕ}
    {t : Term S ℕ}
    (hx : x ∈ t.vars)
    (h : s(var x, t) ∈ N) :
    N.ChainVicious := by
  obtain ⟨D, rfl⟩ := Multiset.exists_cons_of_mem h
  exact ⟨{s(var x, t)}, D, ⟨x, x, t, 0, hx, .nil x, rfl⟩, by simp⟩

/-- A written vicious circle stays one when equations are added. -/
theorem ChainVicious.add_right
    -- a net with a written vicious circle
    {N : Net S ℕ}
    (h : N.ChainVicious)
    -- the equations added
    (D' : Net S ℕ) :
    (N + D').ChainVicious := by
  obtain ⟨K, D, hK, rfl⟩ := h
  exact ⟨K, D + D', hK, by rw [add_assoc]⟩

/-- Contracting a written circle into one equation. -/
theorem hasVicious_contract
    -- the root of the circle
    {x : ℕ} :
    -- for a path `C` from `y` back to `x`,
    ∀ {C : Net S ℕ} {y : ℕ}, Path C y x →
      -- an equation `x = t` with `y` a leaf of `t`, and the rest `D` of the net,
      ∀ (t : Term S ℕ) (D : Net S ℕ), y ∈ t.vars →
      -- if the net is linear, it has a vicious circle
      Net.Linear (s(var x, t) ::ₘ (C + D)) → HasVicious (s(var x, t) ::ₘ (C + D)) := by
  intro C y hC
  induction hC with
  | nil x => exact fun t D hy _ => hasVicious_of_mem hy (by simp)
  | @cons y y₂ x t₂ C₂ hy₂ _ ih =>
    intro t D hy hlin
    have e : s(var x, t) ::ₘ (s(var y, t₂) ::ₘ C₂ + D) =
        s(var y, t₂) ::ₘ s(var x, t) ::ₘ (C₂ + D) := by
      rw [Multiset.cons_add, Multiset.cons_swap]
    rw [e] at hlin ⊢
    have hyx : y ≠ x := by
      rintro rfl
      have := hlin y
      have h1 := Multiset.one_le_count_iff_mem.2 hy
      simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton_self] at this
      omega
    have W := Wire.mk y t₂ (var x) t (C₂ + D) hlin (by simp [hy])
    rw [Cut.subst_var_ne (Ne.symm hyx)] at W
    exact (ih _ D (mem_subst_of_mem hy hy₂) W.linear_right).of_equiv W.equiv.symm

/-- A written vicious circle of a linear net is a vicious circle (Lafont 1997, page 79): its
equations are contracted, by wire substitutions, into one equation `x = t` with `x` a leaf of
`t`. -/
theorem ChainVicious.hasVicious
    -- a net with a written vicious circle
    {N : Net S ℕ}
    (h : N.ChainVicious)
    -- the net is linear
    (hN : N.Linear) :
    N.HasVicious := by
  obtain ⟨K, D, ⟨x, y, t, C, hy, hC, rfl⟩, rfl⟩ := h
  rw [Multiset.cons_add] at hN ⊢
  exact hasVicious_contract hC t D hy hN

end Net

-- ============================================================================================
-- 5. Auxiliary lemmas: a wire substitution keeps a written vicious circle
-- ============================================================================================

namespace Vicious

/-- **A wire substitution keeps a written vicious circle** (Lafont 1997, page 79). If the wire
`w = u` is an equation of the circle, the circle gets shorter by one equation; otherwise `u` is
plugged into a leaf of a tree of the circle that is not a link of it. -/
theorem Wire.chainVicious
    -- `M` is `N` after one wire substitution
    {N M : Net S ℕ}
    (h : Wire N M)
    -- `N` has a written vicious circle
    (hc : N.ChainVicious) :
    M.ChainVicious := by
  obtain ⟨w, u, a, b, Δ, hlin, hw⟩ := h
  have hcw := hlin w
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcw
  have hw1 : 1 ≤ (a.vars + b.vars).count w := Multiset.one_le_count_iff_mem.2 hw
  rw [Multiset.count_add] at hw1
  have hu : u.vars.count w = 0 := by omega
  have hΔ : w ∉ Net.vars Δ := Multiset.count_eq_zero.1 (by omega)
  have hM : s(a.subst w u, b.subst w u) ::ₘ Δ = Cut.sub (s(a, b) ::ₘ Δ) w u := by
    rw [Cut.sub_cons, Cut.sub_of_notMem u hΔ]
  rw [hM]
  have hR : (Net.vars (s(a, b) ::ₘ Δ)).count w = 1 := by
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add]
    omega
  obtain ⟨K, D, hK, hN⟩ := hc
  generalize s(a, b) ::ₘ Δ = R at hR hlin hN ⊢
  by_cases hWK : s(var w, u) ∈ K
  · obtain ⟨x, y, t, C, he, hy, hC, rfl⟩ := hK.rotate hWK
    rw [Multiset.cons_add] at hN
    have hRD : R = C + D := (Multiset.cons_inj_right _).1 (hN.trans (by rw [he]))
    subst hRD
    have hcnt := circle_count hy hC
    rw [← he] at hcnt
    simp only [Net.vars_add, Multiset.count_add] at hR
    rcases Sym2.eq_iff.1 he with ⟨hwx, rfl⟩ | ⟨rfl, rfl⟩
    · cases hwx
      simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton_self, hu] at hcnt
      have hC0 : C ≠ 0 := by
        rintro rfl
        simp at hcnt
      obtain ⟨x₁, t₁, C₁, hz, hC₁, rfl⟩ := hC.snoc hC0
      simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton] at hR
      have h1 := Multiset.one_le_count_iff_mem.2 hz
      have hx₁ : x₁ ≠ w := by
        rintro rfl
        simp at hR
        omega
      have hC₁w : w ∉ Net.vars C₁ := Multiset.count_eq_zero.1 (by split_ifs at hR <;> omega)
      have hDw : w ∉ Net.vars D := Multiset.count_eq_zero.1 (by split_ifs at hR <;> omega)
      refine ⟨s(var x₁, t₁.subst w u) ::ₘ C₁, D, ⟨x₁, y, _, C₁, mem_subst_of_mem hz hy, hC₁, rfl⟩,
        ?_⟩
      rw [Multiset.cons_add, Cut.sub_cons, Cut.sub_add, Cut.sub_of_notMem u hC₁w,
        Cut.sub_of_notMem u hDw, Cut.subst_var_ne hx₁, Multiset.cons_add]
    · have hyw : y = w := by simpa using hy
      subst hyw
      simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
        Multiset.count_singleton_self, Multiset.count_singleton] at hcnt
      have hxy : x ≠ y := by
        rintro rfl
        simp at hu
      rcases hC with _ | ⟨hy₂, hC₂⟩
      · exact absurd rfl hxy
      · rename_i y₂ t₂ C₂
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hR
        have ht₂ : y ∉ t₂.vars := Multiset.count_eq_zero.1 (by omega)
        have hC₂w : y ∉ Net.vars C₂ := Multiset.count_eq_zero.1 (by omega)
        have hDw : y ∉ Net.vars D := Multiset.count_eq_zero.1 (by omega)
        refine ⟨s(var x, t₂) ::ₘ C₂, D, ⟨x, y₂, t₂, C₂, hy₂, hC₂, rfl⟩, ?_⟩
        rw [Multiset.cons_add, Cut.sub_cons, Cut.sub_add, Cut.sub_of_notMem _ hC₂w,
          Cut.sub_of_notMem _ hDw, Cut.subst_var_self, Term.subst_of_notMem ht₂,
          Multiset.cons_add]
  · have hWD : s(var w, u) ∈ D := by
      have : s(var w, u) ∈ K + D := hN ▸ Multiset.mem_cons_self _ _
      exact (Multiset.mem_add.1 this).resolve_left hWK
    obtain ⟨D', rfl⟩ := Multiset.exists_cons_of_mem hWD
    rw [Multiset.add_cons] at hN
    have hRD : R = K + D' := (Multiset.cons_inj_right _).1 hN
    subst hRD
    rw [Net.vars_add, Multiset.count_add] at hR
    obtain ⟨x, y, t, C, hy, hC, rfl⟩ := hK
    have hcnt := circle_count hy hC
    have hwx : w ≠ x := by rintro rfl; omega
    have hwy : w ≠ y := by rintro rfl; omega
    refine ⟨Cut.sub (s(var x, t) ::ₘ C) w u, Cut.sub D' w u, ?_, by rw [Cut.sub_add]⟩
    rw [Net.vars_cons, Multiset.count_add] at hR
    rw [Cut.sub_cons, Cut.subst_var_ne (Ne.symm hwx)]
    exact ⟨x, y, _, _, mem_subst_of_ne u hy (Ne.symm hwy), hC.sub u hwy hwx (by omega), rfl⟩

/-- A wire substitution undone keeps a written vicious circle, when `w` occurs in the left side
`a` of the equation it was plugged into. -/
theorem chainVicious_unsub
    -- the wire `w = u`, the equation `a = b` and the rest `Δ` of the net
    {w : ℕ}
    {u a b : Term S ℕ}
    {Δ : Net S ℕ}
    -- `w` is a leaf of the left side `a`
    (hwa : w ∈ a.vars)
    -- the net after the substitution has a written vicious circle
    (hc : Net.ChainVicious (s(a.subst w u, b) ::ₘ Δ)) :
    -- so has the net before it
    Net.ChainVicious (s(var w, u) ::ₘ s(a, b) ::ₘ Δ) := by
  obtain ⟨K, D, hK, hN⟩ := hc
  by_cases hE : s(a.subst w u, b) ∈ K
  · obtain ⟨x, y, t, C, he, hy, hC, rfl⟩ := hK.rotate hE
    rw [Multiset.cons_add] at hN
    have hΔ : Δ = C + D := (Multiset.cons_inj_right _).1 (hN.trans (by rw [he]))
    subst hΔ
    rcases Sym2.eq_iff.1 he with ⟨ha, rfl⟩ | ⟨rfl, rfl⟩
    · cases a with
      | var v =>
        have hv : w = v := by simpa using hwa
        subst hv
        rw [Cut.subst_var_self] at ha
        subst ha
        refine ⟨s(var x, var w) ::ₘ s(var w, b) ::ₘ C, D,
          ⟨x, w, var w, _, by simp, .cons hy hC, rfl⟩, ?_⟩
        rw [Multiset.cons_add, Multiset.cons_add, Sym2.eq_swap (a := var w) (b := var x)]
      | app α ts => cases ha
    · by_cases hyu : y ∈ u.vars
      · refine ⟨s(var x, a) ::ₘ s(var w, u) ::ₘ C, D,
          ⟨x, w, a, _, hwa, .cons hyu hC, rfl⟩, ?_⟩
        rw [Multiset.cons_add, Multiset.cons_add, Sym2.eq_swap (a := a) (b := var x)]
        exact Multiset.cons_swap _ _ _
      · have hcy := Multiset.one_le_count_iff_mem.2 hy
        rw [Term.count_vars_subst, Multiset.count_eq_zero.2 hyu, mul_zero, zero_add] at hcy
        have hya : y ∈ a.vars := by
          refine Multiset.one_le_count_iff_mem.1 ?_
          split_ifs at hcy <;> omega
        refine ⟨s(var x, a) ::ₘ C, s(var w, u) ::ₘ D, ⟨x, y, a, C, hya, hC, rfl⟩, ?_⟩
        rw [Multiset.cons_add, Multiset.add_cons, Sym2.eq_swap (a := a) (b := var x)]
        exact Multiset.cons_swap _ _ _
  · have hED : s(a.subst w u, b) ∈ D := by
      have : s(a.subst w u, b) ∈ K + D := hN ▸ Multiset.mem_cons_self _ _
      exact (Multiset.mem_add.1 this).resolve_left hE
    obtain ⟨D', rfl⟩ := Multiset.exists_cons_of_mem hED
    rw [Multiset.add_cons] at hN
    rw [(Multiset.cons_inj_right _).1 hN]
    exact ⟨K, s(var w, u) ::ₘ s(a, b) ::ₘ D', hK, by rw [Multiset.add_cons, Multiset.add_cons]⟩

/-- **A wire substitution undone keeps a written vicious circle** (Lafont 1997, page 79). If `M`
is `N` with the wire `w = u` contracted and `M` has a written vicious circle, so has `N`: the
circle gets the wire as a new equation, or keeps its equations with `u` unplugged. -/
theorem Wire.chainVicious_symm
    -- `M` is `N` after one wire substitution
    {N M : Net S ℕ}
    (h : Wire N M)
    -- `M` has a written vicious circle
    (hc : M.ChainVicious) :
    N.ChainVicious := by
  obtain ⟨w, u, a, b, Δ, hlin, hw⟩ := h
  have hcw := hlin w
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hcw
  rcases Multiset.mem_add.1 hw with hwa | hwb
  · have hb : w ∉ b.vars := by
      have := Multiset.one_le_count_iff_mem.2 hwa
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem hb] at hc
    exact chainVicious_unsub hwa hc
  · have ha : w ∉ a.vars := by
      have := Multiset.one_le_count_iff_mem.2 hwb
      exact Multiset.count_eq_zero.1 (by omega)
    rw [Term.subst_of_notMem ha, Sym2.eq_swap] at hc
    rw [Sym2.eq_swap (a := a)]
    exact chainVicious_unsub hwb hc

/-- Equivalent nets have a written vicious circle together. -/
theorem Equiv.chainVicious_iff
    -- two nets that are the same graph
    {N M : Net S ℕ}
    (h : Equiv N M) :
    N.ChainVicious ↔ M.ChainVicious := by
  induction h with
  | rel _ _ h => exact ⟨Wire.chainVicious h, Wire.chainVicious_symm h⟩
  | refl _ => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end Vicious

-- ============================================================================================
-- 6. Main results
-- ============================================================================================

namespace Net

/-- A vicious circle up to wires is written out in the net itself (Lafont 1997, page 79): a
closed chain of equations `x₀ = t₀, …, xₖ = tₖ`, each name a leaf of the previous tree. No linearity
is needed. -/
theorem HasVicious.chainVicious
    -- a net with a vicious circle
    {N : Net S ℕ}
    (h : N.HasVicious) :
    N.ChainVicious := by
  obtain ⟨N', hE, x, t, hx, hm⟩ := h
  exact (Vicious.Equiv.chainVicious_iff hE).2 (chainVicious_of_mem hx hm)

/-- **A vicious circle up to wires is a closed chain** (Lafont 1997, page 79). For a linear net, a
vicious circle of the graph is the same as equations `x₀ = t₀, x₁ = t₁, …, xₖ = tₖ` of the net
with `xᵢ₊₁` a leaf of `tᵢ` and `x₀` a leaf of `tₖ`. -/
theorem hasVicious_iff_chainVicious
    -- a linear net
    {N : Net S ℕ}
    (hN : N.Linear) :
    N.HasVicious ↔ N.ChainVicious :=
  ⟨HasVicious.chainVicious, fun h => h.hasVicious hN⟩

/-- **A tree plugged into a free port is reduced** (Lafont 1997, page 79: "trees […] are typical
examples of reduced nets"). The net `x = t`, with `x` not a leaf of `t`, has no cut and no vicious
circle. -/
theorem isReduced_tree
    -- the tree `t` and the free port `x`, not a leaf of `t`
    {x : ℕ}
    {t : Term S ℕ}
    (hx : x ∉ t.vars) :
    IsReduced ({s(var x, t)} : Net S ℕ) := by
  refine ⟨fun hc => ?_, fun hv => ?_⟩
  · obtain ⟨a, b, xs, D, ha, hb, h⟩ := hc.chainCut
    cases xs with
    | nil =>
      rw [Cut.chain_nil, Multiset.singleton_add, Multiset.singleton_eq_cons_iff] at h
      rcases Sym2.eq_iff.1 h.1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Cut.not_isCell_var x ha
      · exact Cut.not_isCell_var x hb
    | cons y ys =>
      rw [Cut.chain_cons, Multiset.cons_add, Multiset.singleton_eq_cons_iff] at h
      have h0 := (add_eq_zero.1 h.2).1
      cases ys with
      | nil => simp at h0
      | cons z zs => simp at h0
  · obtain ⟨K, D, ⟨x₀, y, t₀, C, hy, hC, rfl⟩, h⟩ := hv.chainVicious
    rw [Multiset.cons_add, Multiset.singleton_eq_cons_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hC0 : C = 0 := (add_eq_zero.1 h2).1
    subst hC0
    have hyx := hC.eq_of_zero
    subst hyx
    rcases Sym2.eq_iff.1 h1 with ⟨h3, rfl⟩ | ⟨rfl, rfl⟩
    · cases h3
      exact hx hy
    · have : y = x := by simpa using hy
      subst this
      simp at hx

end Net

/-- **A translation keeps vicious circles** (Lafont 1997, Proposition 3, fourth point of the proof,
page 80): if `N'` translates `N` and `N` has a vicious circle, so has `N'`. No strictness is
needed.

The circle of `N` is an equation `x = t` of a net equivalent to `N`, with `x` a leaf of `t`; a
translation of that net is equivalent to `N'` (`NetTr.of_equiv`). The translation of the equation
is `x = t'`, and `x` is still a leaf of `t'`: a translation keeps the names. This is where the
paper uses Lemma 1 (the root of `Φ(α)` reaches each auxiliary port by a principal path): here
`Φ(α)` is a tree, so the path is the branch of the tree from the port to the root. If the cells of
`t` all become wires, `x = t'` is the cyclic wire `x = x`. -/
theorem Translation.NetTr.hasVicious
    -- a translation, a net `N` and its translation `N'`
    {Φ : Translation S S'}
    {N : Net S ℕ}
    {N' : Net S' ℕ}
    (h : Φ.NetTr N N')
    -- `N` has a vicious circle
    (hv : N.HasVicious) :
    N'.HasVicious := by
  obtain ⟨N₁, hE, x, t, hx, hm⟩ := hv
  obtain ⟨N₁', h₁, hE'⟩ := h.of_equiv hE
  obtain ⟨Δ, rfl⟩ := Multiset.exists_cons_of_mem hm
  obtain ⟨e', Δ', he, -, rfl⟩ := Multiset.rel_cons_left.1 h₁.rel
  obtain ⟨a', b', rfl, ha, hb⟩ := Translation.EqTr.mk he
  cases ha
  exact ⟨_, hE', x, b', Multiset.one_le_count_iff_mem.1
    ((Multiset.one_le_count_iff_mem.2 hx).trans (hb.count_le x)), Multiset.mem_cons_self _ _⟩

end INet
