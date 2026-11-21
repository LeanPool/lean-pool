/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.EquivAdd
public import LeanPool.InteractionCombinators.Text.RenameStep
import LeanPool.InteractionCombinators.Core.Combinators

/-!
# Reduction up to wires inside a larger net

Reduction is defined on graphs and is local: an interaction replaces an active pair and leaves
the rest of the net untouched (Lafont 1997, Section 1.2, page 73). In the text presentation, a
reduction `StepsE I N M` can be done beside a context `Γ` (`StepsE.add_right`).

The wires created by a rule, and the intermediate names of a wire substitution, may clash with
the names of `Γ`. Each step is therefore renamed first, by an injective `f` that fixes the names
of the starting net and sends every other name above all the names of the net and of `Γ`. The
result is the renamed net, which is `M` up to equivalence (`Net.equiv_bind_var`).

Contents, in the order of the file:

1. Auxiliary lemmas on the names of one interaction: `Step.count_vars` (every name keeps its
   number of occurrences, except the new wires) and `Step.free_iff` (the free ports are kept).
2. Auxiliary lemmas: renaming beside a context: `Net.Linear.bind_var_add_right` (a renamed net
   sits linearly beside `Γ`) and `StepE.of_equiv` (an equivalence before a step is absorbed).
3. Main results: `StepE.add_right` (one step beside `Γ`) and `StepsE.add_right` (a reduction
   beside `Γ`).
4. The hypotheses can hold: two `con` cells annihilate beside an `era` cell.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas on the names of one interaction
-- ============================================================================================

/-- One interaction keeps every name except the wires it creates, which were unused and occur
twice afterwards (Lafont 1997, Section 1.2, page 73: the right-hand side of a rule replaces the
active pair, its internal wires are new). -/
theorem Step.count_vars
    -- the interaction system, whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- one interaction from `N` to `M`
    {N M : Net S ℕ}
    (h : Step I N M)
    -- the name whose occurrences are counted
    (y : ℕ) :
    -- either `y` occurs in `M` as often as in `N`,
    M.vars.count y = N.vars.count y ∨
      -- or `y` is a new wire: unused in `N`, it occurs twice in `M`
      (N.vars.count y = 0 ∧ M.vars.count y = 2) := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := h
  simp only [Net.vars_cons, Net.vars_add, eqVars_mk, Term.vars_app, Multiset.count_add,
    Multiset.count_sum']
  rw [Rule.count_vars_inst r (hI _ _ _ hr)]
  by_cases hex : ∃ w, y = f w
  · obtain ⟨w0, rfl⟩ := hex
    have hsum : ∑ w, (if f w0 = f w then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single w0]
      · simp
      · intro w _ hw
        exact ite_eq_right fun h => hw (hf h).symm
      · simp
    have h0 := Multiset.count_eq_zero_of_notMem (hfresh w0)
    simp only [Net.vars_cons, eqVars_mk, Term.vars_app, Multiset.count_add,
      Multiset.count_sum'] at h0
    right
    omega
  · have hsum : ∑ w, (if y = f w then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun w _ => ite_eq_right fun h => hex ⟨w, h⟩
    left
    omega

/-- One interaction keeps the free ports (Lafont 1997, Section 1.2, page 73: the interface of
the active pair is the interface of the right-hand side). -/
theorem Step.free_iff
    -- the interaction system, whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- one interaction from `N` to `M`
    {N M : Net S ℕ}
    (h : Step I N M)
    -- the name looked at
    (y : ℕ) :
    -- `y` is a free port of `M` exactly when it is a free port of `N`
    M.vars.count y = 1 ↔ N.vars.count y = 1 := by
  rcases h.count_vars hI y with h | h <;> omega

-- ============================================================================================
-- 2. Auxiliary lemmas: renaming beside a context
-- ============================================================================================

/-- A renaming `f`, injective, fixing the names of `N₀` and sending the other names out of `Γ`,
places beside `Γ` every linear net with the free ports of `N₀`, when `N₀ + Γ` is linear
(Lafont 1997, Section 1.1, pages 71 to 72: `Γ` is plugged only into free ports). -/
theorem Net.Linear.bind_var_add_right
    -- the net `N₀`, the context `Γ` and the net `K` to be placed beside `Γ`
    {N₀ Γ K : Net S ℕ}
    -- the renaming: injective
    (f : ℕ → ℕ)
    (hf : Function.Injective f)
    -- `N₀` beside `Γ` is linear
    (hN₀ : (N₀ + Γ).Linear)
    -- the renaming fixes the names of `N₀` and sends the other names out of `Γ`
    (hfix : ∀ x ∈ N₀.vars, f x = x)
    (hout : ∀ x, x ∉ N₀.vars → f x ∉ Γ.vars)
    -- `K` is linear, with the free ports of `N₀`
    (hK : K.Linear)
    (hKf : ∀ y, K.vars.count y = 1 ↔ N₀.vars.count y = 1) :
    -- the renamed `K` beside `Γ` is linear
    ((K.bind fun y => var (f y)) + Γ).Linear := by
  intro z
  have hNz := hN₀ z
  rw [Net.vars_add, Multiset.count_add] at hNz ⊢
  rw [Net.vars_bind_var]
  by_cases hz : ∃ x, f x = z
  · obtain ⟨x, rfl⟩ := hz
    rw [Multiset.count_map_eq_count' f _ hf x]
    by_cases hx : x ∈ N₀.vars
    · rw [hfix x hx] at hNz ⊢
      have hKx := hK x
      have hKfx := hKf x
      have := Multiset.one_le_count_iff_mem.2 hx
      omega
    · rw [Multiset.count_eq_zero_of_notMem (hout x hx)]
      simpa using hK x
  · have hm : z ∉ K.vars.map f := fun hm => by
      obtain ⟨x, -, hx⟩ := Multiset.mem_map.1 hm
      exact hz ⟨x, hx⟩
    rw [Multiset.count_eq_zero_of_notMem hm]
    omega

/-- An equivalence followed by one interaction up to wires is one interaction up to wires
(Lafont 1997, Section 1.1, pages 71 to 72: nets are graphs, the names of wires do not
matter). -/
theorem StepE.of_equiv
    -- the interaction system
    {I : System S}
    -- `N` is equivalent to `K`, which reduces to `M` by one interaction up to wires
    {N K M : Net S ℕ}
    (hE : Equiv N K)
    (h : StepE I K M) :
    -- `N` reduces to `M` by one interaction up to wires
    StepE I N M := by
  obtain ⟨K', hK, hS⟩ := h
  exact ⟨K', hE.trans hK, hS⟩

-- ============================================================================================
-- 3. Main results: reduction beside a context
-- ============================================================================================

/-- **One interaction up to wires, inside a larger net.** If `N` reduces to `M` by one `StepE`
and `N + Γ` is linear, then `N + Γ` reduces by one `StepE` to `M' + Γ`, where `M'` is `M` with
its internal wires renamed away from the names of `Γ` (Lafont 1997, Section 1.2, page 73:
reduction is local; Section 1.1, pages 71 to 72: the names of wires do not matter). -/
theorem StepE.add_right
    -- the interaction system, whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- the nets `N` and `M`, and the context `Γ`
    {N M : Net S ℕ}
    (Γ : Net S ℕ)
    -- `N` reduces to `M` by one interaction up to wires
    (h : StepE I N M)
    -- the net we start from, `N` beside `Γ`, is linear
    (hN : (N + Γ).Linear) :
    -- there is a net `M'` such that
    ∃ M',
      -- `N` beside `Γ` reduces by one interaction up to wires to `M'` beside `Γ`,
      StepE I (N + Γ) (M' + Γ) ∧
      -- `M'` is the same graph as `M`,
      Equiv M' M ∧
      -- and `M'` beside `Γ` is linear
      (M' + Γ).Linear := by
  obtain ⟨N', hE, hS⟩ := h
  have hNl : N.Linear := fun y => by
    have := hN y
    rw [Net.vars_add, Multiset.count_add] at this
    omega
  have hN'l : N'.Linear := hE.linear hNl
  have hMl : M.Linear := hS.linear hI hN'l
  -- a bound on the names of `N` and `Γ`
  set B := (N.vars + Γ.vars).sup + 1 with hB
  have hlt : ∀ x ∈ N.vars + Γ.vars, x < B := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup hx)
  have hltN : ∀ x ∈ N.vars, x < B := fun x hx => hlt x (by simp [hx])
  have hltΓ : ∀ x ∈ Γ.vars, x < B := fun x hx => hlt x (by simp [hx])
  -- fix the names of `N`, send the others above `B`
  let f : ℕ → ℕ := fun x => if x ∈ N.vars then x else x + B
  have hfV : ∀ x ∈ N.vars, f x = x := fun x hx => by simp [f, hx]
  have hfO : ∀ x, x ∉ N.vars → f x = x + B := fun x hx => by simp [f, hx]
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x ∈ N.vars <;> by_cases hy : y ∈ N.vars
    · rwa [hfV x hx, hfV y hy] at hxy
    · rw [hfV x hx, hfO y hy] at hxy
      have := hltN x hx
      omega
    · rw [hfO x hx, hfV y hy] at hxy
      have := hltN y hy
      omega
    · rw [hfO x hx, hfO y hy] at hxy
      omega
  have hout : ∀ x, x ∉ N.vars → f x ∉ Γ.vars := fun x hx hm => by
    have := hltΓ _ hm
    rw [hfO x hx] at this
    omega
  have hfixN : (N.bind fun y => var (f y)) = N := by
    rw [Net.bind_congr (g := var) fun x hx => by rw [hfV x hx]]
    exact Net.bind_var_self N
  have hgood : ∀ K : Net S ℕ, K.Linear → (∀ y, K.vars.count y = 1 ↔ N.vars.count y = 1) →
      ((K.bind fun y => var (f y)) + Γ).Linear := fun K hK hKf =>
    Net.Linear.bind_var_add_right f hf hN hfV hout hK hKf
  have hMf : ∀ y, M.vars.count y = 1 ↔ N.vars.count y = 1 := fun y =>
    (hS.free_iff hI y).trans (hE.free_iff y).symm
  have hM'Γ := hgood M hMl hMf
  -- the equivalence, beside `Γ`
  have E := Equiv.bind_var_add_right f hf Γ hgood hE hNl fun _ => Iff.rfl
  rw [hfixN] at E
  -- the interaction, beside `Γ`
  have S' := (hS.bind_var f hf).add_right hI Γ hM'Γ
  refine ⟨M.bind fun y => var (f y), ⟨_, E, S'⟩, ?_, hM'Γ⟩
  -- the renaming moves only internal wires of `M`
  refine (Net.equiv_bind_var hMl f hf.injOn fun x hx => hfV x ?_).symm
  exact Multiset.one_le_count_iff_mem.1 (by have := (hMf x).1 hx; omega)

/-- **Reduction up to wires inside a larger net.** If `N` reduces to `M` (`StepsE`) and `N + Γ`
is linear, then `N + Γ` reduces to `M' + Γ`, where `M'` is equivalent to `M`: the wires created
along the way are given names that avoid those of `Γ`. Reduction is local and defined on graphs
(Lafont 1997, Section 1.2, page 73), so it can be done inside any context. -/
theorem StepsE.add_right
    -- the interaction system, whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- the nets `N` and `M`, and the context `Γ`
    {N M : Net S ℕ}
    (Γ : Net S ℕ)
    -- `N` reduces to `M` up to wires
    (h : StepsE I N M)
    -- the net we start from, `N` beside `Γ`, is linear
    (hN : (N + Γ).Linear) :
    -- there is a net `M'` such that
    ∃ M',
      -- `N` beside `Γ` reduces up to wires to `M'` beside `Γ`,
      StepsE I (N + Γ) (M' + Γ) ∧
      -- `M'` is the same graph as `M`,
      Equiv M' M ∧
      -- and `M'` beside `Γ` is linear
      (M' + Γ).Linear := by
  induction h with
  | refl => exact ⟨N, Relation.ReflTransGen.refl, Equiv.refl N, hN⟩
  | tail _ hstep ih =>
    obtain ⟨M₁, hs, hE, hl⟩ := ih
    obtain ⟨M₂, hs₂, hE₂, hl₂⟩ := (StepE.of_equiv hE hstep).add_right hI Γ hl
    exact ⟨M₂, hs.tail hs₂, hE₂, hl₂⟩

-- ============================================================================================
-- 4. The hypotheses can hold
-- ============================================================================================

section Example

open Comb

/-- Non-vacuity: two `con` cells annihilate beside a context `Γ` that plugs an `era` cell into
the free port `0` of the active pair. -/
example :
    ∃ M',
      StepsE system
        (({s(mkCon (var 0) (var 1), mkCon (var 2) (var 3))} : CNet) + {s(var 0, mkEra)})
        (M' + {s(var 0, mkEra)}) ∧
      Equiv M' {s(var 0, var 3), s(var 1, var 2)} ∧
      (M' + {s(var 0, mkEra)}).Linear := by
  refine StepsE.add_right system_wellFormed.linear _ ?_ ?_
  · have h := step_con_con (var 0) (var 1) (var 2) (var 3) 0
    simpa [Multiset.insert_eq_cons] using (Steps.single h).stepsE
  · intro y
    simp only [Multiset.singleton_add, Net.vars_cons, Net.vars_singleton, eqVars_mk,
      vars_mkCon, vars_mkEra, vars_var, Multiset.count_add, Multiset.count_singleton,
      Multiset.count_cons, Multiset.count_zero]
    split_ifs <;> omega

end Example

end INet
