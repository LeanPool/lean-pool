/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Reduced.ReducedDecomp
public import LeanPool.InteractionCombinators.Reduced.ReducedDecompUnique
public import LeanPool.InteractionCombinators.Translations.SimulationStrict

/-!
# The syntactic form of right members is the reduced nets (page 79)

Lafont 1997, page 73, asks the right member of a rule to be a reduced net, and page 79 defines
reduced nets: no cut and no vicious circle (`Net.IsReduced`). The rules of the code are required
to be in a syntactic form instead, `Rule.Reduced`: every equation has an auxiliary port on one
side. This file shows that the two agree, on instances with distinct names on the ports.

Contents, in the order of the file:

1. Auxiliary lemmas: renaming. `Term.exists_bind_var_eq_of_range`,
   `Net.exists_bind_var_eq_of_range`: a tree, or a net, whose names all lie in the range of `β` is
   one renamed by `β`.
2. Auxiliary lemmas: counts on rule instances. `Rule.count_inst_xs` (a name on a port occurs
   once), `Rule.port_of_count_inst_eq_one` (a name that occurs once is on a port).
3. Main results.
   * `Rule.Reduced.isTreesOnWiring_inst`, `Rule.Reduced.isReduced_inst` — **forward**: an
     instance of a linear rule in the syntactic form is trees on a wiring (Proposition 2,
     page 79), hence reduced: no cut and no vicious circle.
   * `Rule.exists_reduced_of_isReduced` — **converse**: if the instance of a linear rule is
     reduced, then the same graph is the instance of a linear rule in the syntactic form. The new
     rule is read off the decomposition of Proposition 2 (`Net.IsReduced.exists_treesOnWiring`),
     its names renamed back to `Fin a ⊕ Fin b ⊕ Fin k`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas: renaming
-- ============================================================================================

/-- A tree whose names all lie in the range of `β` is a tree renamed by `β`. -/
theorem Term.exists_bind_var_eq_of_range
    -- the renaming
    {ν μ : Type}
    (β : ν → μ)
    -- the tree, every name of which is the image of a name by `β`
    (t : Term S μ)
    (h : ∀ x ∈ t.vars, ∃ v, β v = x) :
    -- there is a tree `t'` on the names `ν` which, renamed by `β`, is `t`
    ∃ t' : Term S ν, t'.bind (fun v => var (β v)) = t := by
  induction t with
  | var x =>
    obtain ⟨v, hv⟩ := h x (by simp)
    exact ⟨var v, by rw [← hv]; rfl⟩
  | app α ts ih =>
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and] at h
    have hi : ∀ i, ∃ t' : Term S ν, t'.bind (fun v => var (β v)) = ts i :=
      fun i => ih i fun x hx => h x ⟨i, hx⟩
    choose g hg using hi
    exact ⟨app α g, by rw [bind_app]; congr 1; funext i; exact hg i⟩

/-- A net whose names all lie in the range of `β` is a net renamed by `β`. -/
theorem Net.exists_bind_var_eq_of_range
    -- the renaming
    {ν μ : Type}
    (β : ν → μ)
    -- the net, every name of which is the image of a name by `β`
    (M : Net S μ)
    (h : ∀ x ∈ M.vars, ∃ v, β v = x) :
    -- there is a net `M'` on the names `ν` which, renamed by `β`, is `M`
    ∃ M' : Net S ν, M'.bind (fun v => var (β v)) = M := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨0, rfl⟩
  | cons e M ih =>
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Net.vars_cons, eqVars_mk, Multiset.mem_add] at h
      obtain ⟨a', ha⟩ := Term.exists_bind_var_eq_of_range β a fun x hx => h x (Or.inl (Or.inl hx))
      obtain ⟨b', hb⟩ := Term.exists_bind_var_eq_of_range β b fun x hx => h x (Or.inl (Or.inr hx))
      obtain ⟨M', hM⟩ := ih fun x hx => h x (Or.inr hx)
      exact ⟨s(a', b') ::ₘ M', by rw [Net.bind_cons, ha, hb, hM]⟩

namespace Rule

variable {a b : ℕ}

-- ============================================================================================
-- 2. Auxiliary lemmas: counts on rule instances
-- ============================================================================================

/-- In a linear instance of a linear rule, with distinct names on the ports, a name on a port
occurs exactly once: it is a free port (Lafont 1997, page 73). -/
theorem count_inst_xs
    -- the rule, linear
    {r : Rule S a b}
    (hrl : r.Linear)
    -- the names on the ports: injective, and no name on both sides
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires, such that the instance is linear
    {h : Fin r.internal → ℕ}
    (hl : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).Linear)
    -- a name on a port
    {p : ℕ}
    (hp : (∃ i, p = xs i) ∨ ∃ j, p = ys j) :
    -- occurs exactly once in the instance
    (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).vars.count p = 1 := by
  refine le_antisymm (count_inst_port hrl hx hy hxy hl hp) ?_
  rw [count_vars_inst r hrl]
  simp only [vars_var, Multiset.count_singleton]
  rcases hp with ⟨i₀, rfl⟩ | ⟨j₀, rfl⟩
  · have e1 : (∑ i, if xs i₀ = xs i then 1 else 0) = 1 := by
      simp only [hx.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    omega
  · have e1 : (∑ j, if ys j₀ = ys j then 1 else 0) = 1 := by
      simp only [hy.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    omega

/-- In an instance of a linear rule, a name that occurs once is one of the names put on the ports:
the internal wires of the rule occur twice (Lafont 1997, page 73). -/
theorem port_of_count_inst_eq_one
    -- the rule, linear
    {r : Rule S a b}
    (hrl : r.Linear)
    -- the names on the ports and on the internal wires
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    {h : Fin r.internal → ℕ}
    -- a name that occurs exactly once in the instance
    {p : ℕ}
    (h1 : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).vars.count p = 1) :
    -- is a name on a port
    (∃ i, p = xs i) ∨ ∃ j, p = ys j := by
  by_contra hne
  simp only [not_or, not_exists] at hne
  rw [count_vars_inst r hrl] at h1
  simp only [vars_var, Multiset.count_singleton, hne.1, hne.2, ite_false, Finset.sum_const_zero,
    zero_add] at h1
  omega

-- ============================================================================================
-- 3. Main results: the syntactic form and the reduced nets agree
-- ============================================================================================

/-- **The syntactic form gives trees on a wiring** (Lafont 1997, page 79, Proposition 2). An
instance of a linear rule in the form `Rule.Reduced`, linear, with distinct names on the ports, is
in the form `Net.IsTreesOnWiring`: every equation hangs a tree from a free port. -/
theorem Reduced.isTreesOnWiring_inst
    -- the rule, linear and in the syntactic form
    {r : Rule S a b}
    (hrl : r.Linear)
    (hr : r.Reduced)
    -- the names on the ports: injective, and no name on both sides
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires, such that the instance is linear
    {h : Fin r.internal → ℕ}
    (hl : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).Linear) :
    -- the instance is trees on a wiring
    (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).IsTreesOnWiring := by
  intro e he
  obtain ⟨p, t, rfl, hp⟩ := hr.mem_inst he
  exact ⟨p, t, rfl, count_inst_xs hrl hx hy hxy hl hp⟩

/-- **The syntactic form of right members is reduced** (Lafont 1997, page 79: a reduced net has
no cut and no vicious circle; page 73: the right member of a rule is reduced). An instance of a
linear rule in the form `Rule.Reduced`, linear, with distinct names on the ports, is
`Net.IsReduced`. This strengthens `Rule.not_hasCut_inst` from "no cut" to "reduced". -/
theorem Reduced.isReduced_inst
    -- the rule, linear and in the syntactic form
    {r : Rule S a b}
    (hrl : r.Linear)
    (hr : r.Reduced)
    -- the names on the ports: injective, and no name on both sides
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires, such that the instance is linear
    {h : Fin r.internal → ℕ}
    (hl : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).Linear) :
    -- the instance is reduced: no cut and no vicious circle
    (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).IsReduced :=
  (hr.isTreesOnWiring_inst hrl hx hy hxy hl).isReduced

/-- **Every reduced right member can be written in the syntactic form** (Lafont 1997, page 79,
Proposition 2; page 73). Let `r` be a linear rule whose instance, with distinct names `xs`, `ys`
on the ports, is linear and reduced (no cut, no vicious circle). Then there is a linear rule `r'`
in the form `Rule.Reduced`, with the same ports, and injective names `h'` for its internal wires,
whose instance is the same graph as that of `r`. The number of internal wires may differ. -/
theorem exists_reduced_of_isReduced
    -- the rule, linear
    {r : Rule S a b}
    (hrl : r.Linear)
    -- the names on the ports: injective, and no name on both sides
    {xs : Fin a → ℕ}
    {ys : Fin b → ℕ}
    (hx : Function.Injective xs)
    (hy : Function.Injective ys)
    (hxy : ∀ i j, xs i ≠ ys j)
    -- the names of the internal wires, such that the instance is linear and reduced
    {h : Fin r.internal → ℕ}
    (hl : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).Linear)
    (hR : (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h).IsReduced) :
    -- there are a rule `r'` with the same ports and names `h'` for its internal wires
    ∃ (r' : Rule S a b) (h' : Fin r'.internal → ℕ),
      -- such that `r'` is linear,
      r'.Linear ∧
      -- `r'` is in the syntactic form,
      r'.Reduced ∧
      -- the names `h'` are distinct,
      Function.Injective h' ∧
      -- and the instance of `r'`, with the same names on the ports, is the same graph as that
      -- of `r`
      Equiv (r.inst (fun i => var (xs i)) (fun j => var (ys j)) h)
        (r'.inst (fun i => var (xs i)) (fun j => var (ys j)) h') := by
  obtain ⟨M, hNM, hM⟩ := Net.IsReduced.exists_treesOnWiring hl hR
  have hML : M.Linear := hNM.linear hl
  -- the internal wires of `M`, numbered
  let W : Finset ℕ := M.vars.toFinset.filter fun x => M.vars.count x = 2
  let eW : W ≃ Fin W.card := W.equivFin
  let β : Fin a ⊕ Fin b ⊕ Fin W.card → ℕ := Sum.elim xs (Sum.elim ys fun w => (eW.symm w).1)
  have hfree : ∀ p, M.vars.count p = 1 → (∃ i, p = xs i) ∨ ∃ j, p = ys j := fun p hp =>
    port_of_count_inst_eq_one hrl ((hNM.free_iff p).2 hp)
  have hxs1 : ∀ i, M.vars.count (xs i) = 1 := fun i =>
    (hNM.free_iff _).1 (count_inst_xs hrl hx hy hxy hl (Or.inl ⟨i, rfl⟩))
  have hys1 : ∀ j, M.vars.count (ys j) = 1 := fun j =>
    (hNM.free_iff _).1 (count_inst_xs hrl hx hy hxy hl (Or.inr ⟨j, rfl⟩))
  have hW2 : ∀ w, M.vars.count (eW.symm w).1 = 2 := fun w =>
    (Finset.mem_filter.1 (eW.symm w).2).2
  have hWinj : Function.Injective fun w => (eW.symm w).1 := fun w w' e =>
    eW.symm.injective (Subtype.ext e)
  have hβ : Function.Injective β := by
    rintro (i | j | w) (i' | j' | w') e <;> simp only [β, Sum.elim_inl, Sum.elim_inr] at e
    · rw [hx e]
    · exact absurd e (hxy i j')
    · have := hxs1 i; rw [e, hW2] at this; omega
    · exact absurd e.symm (hxy i' j)
    · rw [hy e]
    · have := hys1 j; rw [e, hW2] at this; omega
    · have := hxs1 i'; rw [← e, hW2] at this; omega
    · have := hys1 j'; rw [← e, hW2] at this; omega
    · rw [hWinj e]
  have hcov : ∀ x ∈ M.vars, ∃ v, β v = x := by
    intro x hx'
    have h1 : 1 ≤ M.vars.count x := Multiset.one_le_count_iff_mem.2 hx'
    have h2 := hML x
    by_cases hc : M.vars.count x = 1
    · rcases hfree x hc with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨.inl i, rfl⟩
      · exact ⟨.inr (.inl j), rfl⟩
    · have hW : x ∈ W := Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx', by omega⟩
      exact ⟨.inr (.inr (eW ⟨x, hW⟩)), by simp [β]⟩
  obtain ⟨M', hM'⟩ := Net.exists_bind_var_eq_of_range β M hcov
  let r' : Rule S a b := ⟨W.card, M'⟩
  have hinst :
      r'.inst (fun i => var (xs i)) (fun j => var (ys j)) (fun w => (eW.symm w).1) = M := by
    rw [← hM']
    unfold Rule.inst
    congr 1
    funext v
    rcases v with i | j | w <;> rfl
  have hcount : ∀ v, M'.vars.count v = M.vars.count (β v) := fun v => by
    rw [← hM', Net.count_vars_bind_var β hβ]
  refine ⟨r', fun w => (eW.symm w).1, ⟨fun i => ?_, fun j => ?_, fun w => ?_⟩, ?_, hWinj,
    hNM.trans (Equiv.of_eq hinst.symm)⟩
  · exact (hcount (.inl i)).trans (hxs1 i)
  · exact (hcount (.inr (.inl j))).trans (hys1 j)
  · exact (hcount (.inr (.inr w))).trans (hW2 w)
  · intro e he
    have hm : Sym2.map (Term.bind fun v => var (β v)) e ∈ M := by
      rw [← hM']; exact Multiset.mem_map_of_mem _ he
    induction e using Sym2.ind with
    | _ a' b' =>
      obtain ⟨x, t, hxe, hx1⟩ := hM _ hm
      rw [Sym2.map_mk] at hxe
      have key : ∀ (u u' : Term S (Fin a ⊕ Fin b ⊕ Fin W.card)),
          u.bind (fun v => var (β v)) = var x → s(a', b') = s(u, u') →
          ∃ p t, s(a', b') = s(var p, t) ∧ ∀ w, p ≠ .inr (.inr w) := by
        intro u u' hu he'
        obtain ⟨p, rfl, hp⟩ := Term.exists_var_of_bind_eq_var hu
        refine ⟨p, u', he', ?_⟩
        rintro w rfl
        have hxw : (eW.symm w).1 = x := by injection hp
        have := hW2 w
        rw [hxw, hx1] at this
        omega
      rcases Sym2.eq_iff.1 hxe with ⟨ha, -⟩ | ⟨-, hb⟩
      · exact key a' b' ha rfl
      · exact key b' a' hb Sym2.eq_swap

end Rule

end INet
