/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Translations.SimulationInvertible
public import LeanPool.InteractionCombinators.Reduced.CutChain

/-!
# After one interaction up to wires, a pair of two cells leaves no cut (page 81)

Lafont 1997, page 81: "if `Φ` is invertible, the reduction must be of length 1", because after
the interaction of the two cells `α'`, `β'` the net is an instance of the right member of a rule,
which has no cut ("Remember that `ρ_{i,j}` is supposed to be reduced", page 81; the condition is
set on page 79).

In Lean the interaction is `StepE`: it happens on some net `K₀` that is the same graph as the pair
`P = {γ(u) = δ(v)}`, with `u`, `v` pairwise distinct names. This file shows that the net reached
has no cut (`System.WellFormed.stepE_pair_not_hasCut`), and then that an invertible compatible
translation simulates every rule in exactly one interaction
(`Translation.Invertible.compatibleWithin_one_of_wellFormed`).

The proof follows the shape of `K₀`.

* `K₀` has the two cells of `P` and no other (`Equiv.cells_eq`), so it is the cut
  `α(xs) = β(ys)` with names `xs`, `ys` on its ports, plus a net `Δ` of wires `a = b`
  (`PairStepE.Wires`). The interaction gives `r.inst xs ys f + Δ`.
* The wires of `Δ` are contracted, in the cut and in the instance at once
  (`PairStepE.contract`): both become their renaming by some `ρ`, plus a net `W` of wires whose
  names are not in the cut, and each name of a wire `a = b` of `W` with `a ≠ b` is free.
* A wire `a = b` of `W` with `a ≠ b` joins two free names. The solutions of a net where every cell
  has the value `true` (`PairStepE.BlindSol`) are the same for nets that are the same graph
  (`PairStepE.Equiv.blindSol_iff`); the pair `P` has every value on its free names as a solution,
  the net with the wire `a = b` does not. So `W` only has wires `a = a`.
* Then the free names of the cut renamed are the `n + m` free names of `P`, so the names `ρ ∘ xs`,
  `ρ ∘ ys` on its ports are pairwise distinct.
* The instance renamed, `r.inst (ρ ∘ xs) (ρ ∘ ys) f`, plus `W`, has no cut: a cut is a chain of
  wires from a cell (`Net.HasCut.chainCut`); its first equation is in the instance, and has a port
  on one side (the rule is reduced), which occurs once, not in `W`, so it cannot be a link of the
  chain. This is the argument of `Rule.not_hasCut_inst`.

Only the linearity and the reducedness of the rules are used
(`PairStepE.stepE_pair_not_hasCut_of`).

Contents, in the order of the file:

1. Nets of wires, and contracting them: `PairStepE.Wires`, `Wires.of_le`, `sub_var_eq`,
   `count_vars_rename`, `Wires.bind_var`, `wire_sub` (one wire substitution), `bind_var_id`, and
   `PairStepE.contract` (the wires of a net plugged into two nets, contracted at once).
2. Solutions where every cell is `true`: `PairStepE.blind`, `BlindSolves`, `BlindSol`,
   `blindSolves_cons`, `blind_subst`, `blind_congr`, `PairStepE.Wire.blindSol_iff`, and
   `PairStepE.Equiv.blindSol_iff` (nets that are the same graph have the same such solutions).
3. The pair of two cells: `PairStepE.pairNet`, `eq_var_of_cells`, `sum_ite_inj`, and
   `PairStepE.stepE_pair_not_hasCut_of` (no cut after one interaction, from linear and reduced
   rules).
4. Main results: `System.WellFormed.stepE_pair_not_hasCut` (page 81) and
   `Translation.Invertible.compatibleWithin_one_of_wellFormed` (`L = M = 1` if `Φ` is
   invertible, page 81).
-/

@[expose] public section

namespace INet

variable {S S' : Signature}

open Term

namespace PairStepE

-- ============================================================================================
-- 1. Nets of wires, and contracting them
-- ============================================================================================

/-- Every equation of the net is a wire `a = b` between two names. -/
def Wires
    -- the net
    (N : Net S ℕ) :
    Prop :=
  ∀ e ∈ N, ∃ a b : ℕ, e = s(var a, var b)

/-- A part of a net of wires is a net of wires. -/
theorem Wires.of_le
    -- a net of wires `M`, and a part `N` of it
    {N M : Net S ℕ}
    (h : Wires M)
    (hle : N ≤ M) :
    Wires N :=
  fun e he => h e (Multiset.mem_of_le hle he)

/-- Plugging the name `z` into the name `x` is renaming `x` to `z`. -/
theorem sub_var_eq
    -- the net, the name `x` and the name `z` plugged into it
    (N : Net S ℕ)
    (x z : ℕ) :
    Cut.sub N x (var z) = N.bind fun w => var (if w = x then z else w) := by
  have hf : (fun y => if y = x then var z else var y : ℕ → Term S ℕ) =
      fun w => var (if w = x then z else w) := by
    funext w
    split_ifs <;> rfl
  unfold Cut.sub Net.bind Term.subst
  rw [hf]

/-- The names of a net after renaming `x` to `z`. -/
theorem count_vars_rename
    -- the net, the name `x` renamed to `z`, and the name `y` counted
    (N : Net S ℕ)
    (x z y : ℕ) :
    -- `y` occurs once for each `x` if it is `z`, plus as often as before unless it is `x`
    (N.bind fun w => var (if w = x then z else w)).vars.count y =
      N.vars.count x * (if y = z then 1 else 0)
        + if y = x then 0 else N.vars.count y := by
  rw [Net.vars_bind]
  have hf : (fun w => ((var (if w = x then z else w) : Term S ℕ)).vars) =
      fun w => ((if w = x then var z else var w : Term S ℕ)).vars := by
    funext w
    split_ifs <;> rfl
  rw [hf, count_bind_ite]
  simp [Multiset.count_singleton]

/-- A net of wires stays one after renaming. -/
theorem Wires.bind_var
    -- the net of wires
    {N : Net S ℕ}
    (h : Wires N)
    -- the renaming
    (ρ : ℕ → ℕ) :
    Wires (N.bind fun w => var (ρ w)) := by
  intro e he
  rw [Net.bind, Multiset.mem_map] at he
  obtain ⟨e₀, he₀, rfl⟩ := he
  obtain ⟨a, b, rfl⟩ := h e₀ he₀
  exact ⟨ρ a, ρ b, rfl⟩

/-- **One wire substitution**, with `x` anywhere in the rest of the net: plugging `t` into the
other end of the wire `x = t`. -/
theorem wire_sub
    -- the wire `x = t`, the rest of the net `A`, and the net is linear
    {x : ℕ}
    {t : Term S ℕ}
    {A : Net S ℕ}
    (hlin : Net.Linear (s(var x, t) ::ₘ A))
    -- the other end of `x` is in `A`
    (hx : x ∈ A.vars) :
    -- the net reduces by a wire substitution to `A` with `t` plugged into `x`
    Wire (s(var x, t) ::ₘ A) (Cut.sub A x t) := by
  obtain ⟨g, hg, hxg⟩ := Multiset.mem_bind.1 hx
  obtain ⟨A', rfl⟩ := Multiset.exists_cons_of_mem hg
  induction g using Sym2.ind with
  | _ a b =>
    have hc := hlin x
    simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
      Multiset.count_singleton_self] at hc
    have h1 : 1 ≤ (a.vars + b.vars).count x := Multiset.one_le_count_iff_mem.2 hxg
    rw [Multiset.count_add] at h1
    have hA' : x ∉ Net.vars A' := Multiset.count_eq_zero.1 (by omega)
    rw [Cut.sub_cons, Cut.sub_of_notMem t hA']
    exact Wire.mk x t a b A' hlin hxg

/-- The net is not changed by the renaming that fixes every name. -/
theorem bind_var_id
    (N : Net S ℕ) :
    (N.bind fun w => var w) = N := by
  unfold Net.bind
  conv_rhs => rw [← Multiset.map_id N]
  refine Multiset.map_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => simp [Term.bind_var_self]

/-- **Contracting the wires of a net** `Δ` plugged into two nets `Γ₁`, `Γ₂` that have the same
names in common with `Δ` (Lafont 1997, Section 1.1, page 71: a wire with a free end elsewhere is
the same as plugging it there). The two nets `Γᵢ + Δ` are the same graphs as the renamings of
`Γᵢ` by one `ρ`, which fixes the names outside `Δ`, plus one net of wires `W`; no name of `W` is
in either renamed `Γᵢ`, and each name of a wire `a = b` of `W` with `a ≠ b` is free. -/
theorem contract :
    -- for every number `n`, net `Δ` of `n` wires, and two nets `Γ₁`, `Γ₂`:
    ∀ (n : ℕ) (Δ Γ₁ Γ₂ : Net S ℕ),
      Multiset.card Δ = n →
      Wires Δ →
      -- if `Γ₁ + Δ` and `Γ₂ + Δ` are linear,
      (Γ₁ + Δ).Linear →
      (Γ₂ + Δ).Linear →
      -- and each name of `Δ` occurs as often in `Γ₁` as in `Γ₂`,
      (∀ y ∈ Δ.vars, Γ₁.vars.count y = Γ₂.vars.count y) →
      -- then there are a renaming `ρ` and a net of wires `W` such that
      ∃ (ρ : ℕ → ℕ) (W : Net S ℕ),
        Wires W ∧
        -- `Γ₁ + Δ` is the same graph as `Γ₁` renamed by `ρ`, plus `W`,
        Equiv (Γ₁ + Δ) ((Γ₁.bind fun w => var (ρ w)) + W) ∧
        -- `Γ₂ + Δ` is the same graph as `Γ₂` renamed by `ρ`, plus `W`,
        Equiv (Γ₂ + Δ) ((Γ₂.bind fun w => var (ρ w)) + W) ∧
        -- `ρ` fixes the names outside `Δ`,
        (∀ y, y ∉ Δ.vars → ρ y = y) ∧
        -- no name of `W` is in `Γ₁` or `Γ₂` renamed,
        (∀ y ∈ W.vars,
          y ∉ (Γ₁.bind fun w => var (ρ w)).vars
            ∧ y ∉ (Γ₂.bind fun w => var (ρ w)).vars) ∧
        -- and each name of a wire `a = b` of `W` with `a ≠ b` is free
        (∀ a b, s(var a, var b) ∈ W → a ≠ b →
          ((Γ₁.bind fun w => var (ρ w)) + W).vars.count a = 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Δ Γ₁ Γ₂ hn hW hl₁ hl₂ hc
  classical
  by_cases hcon : ∃ x z Δ₁, Δ = s(var x, var z) ::ₘ Δ₁ ∧ x ∈ (Γ₁ + Δ₁).vars
  · obtain ⟨x, z, Δ₁, rfl, hx⟩ := hcon
    have hxΔ : x ∈ Net.vars (s(var x, var z) ::ₘ Δ₁) := by simp
    have hzΔ : z ∈ Net.vars (s(var x, var z) ::ₘ Δ₁) := by simp
    have hx₂ : x ∈ (Γ₂ + Δ₁).vars := by
      rw [Net.vars_add, Multiset.mem_add] at hx ⊢
      rcases hx with hx | hx
      · left
        rw [← Multiset.one_le_count_iff_mem, ← hc x hxΔ]
        exact Multiset.one_le_count_iff_mem.2 hx
      · exact Or.inr hx
    set g : ℕ → ℕ := fun w => if w = x then z else w with hg
    have hwire : ∀ Γ : Net S ℕ, Net.Linear (Γ + s(var x, var z) ::ₘ Δ₁) → x ∈ (Γ + Δ₁).vars →
        Wire (Γ + s(var x, var z) ::ₘ Δ₁)
          ((Γ.bind fun w => var (g w)) + Net.bind (fun w => var (g w)) Δ₁) := by
      intro Γ hl hxΓ
      rw [Multiset.add_cons] at hl ⊢
      have := wire_sub hl hxΓ
      rwa [Cut.sub_add, sub_var_eq, sub_var_eq] at this
    have hW₁ : Wires (Net.bind (fun w => var (g w)) Δ₁) :=
      (hW.of_le (Multiset.le_cons_self _ _)).bind_var g
    have hmem : ∀ y ∈ Net.vars (Net.bind (fun w => var (g w)) Δ₁),
        y ∈ Net.vars (s(var x, var z) ::ₘ Δ₁) ∧ y ≠ x := by
      intro y hy
      have h1 := Multiset.one_le_count_iff_mem.2 hy
      rw [count_vars_rename] at h1
      have hzx : z ≠ x := by
        intro e
        subst e
        have := hl₁ z
        simp only [Net.vars_add, Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at this
        have h2 := Multiset.one_le_count_iff_mem.2 hx
        rw [Net.vars_add, Multiset.count_add] at h2
        omega
      by_cases hyz : y = z
      · subst hyz
        exact ⟨hzΔ, hzx⟩
      · by_cases hyx : y = x
        · subst hyx
          simp [Ne.symm hzx] at h1
        · simp only [hyz, ite_false, mul_zero, hyx, zero_add] at h1
          refine ⟨?_, hyx⟩
          simp only [Net.vars_cons, Multiset.mem_add]
          exact Or.inr (Multiset.one_le_count_iff_mem.1 h1)
    have W₁ := hwire Γ₁ hl₁ hx
    have W₂ := hwire Γ₂ hl₂ hx₂
    obtain ⟨ρ, W, hWW, hE₁, hE₂, hfix, hnf, hfree⟩ :=
      ih (Multiset.card Δ₁) (by rw [← hn, Multiset.card_cons]; omega)
        (Net.bind (fun w => var (g w)) Δ₁) (Γ₁.bind fun w => var (g w))
        (Γ₂.bind fun w => var (g w)) (by simp [Net.bind]) hW₁ W₁.linear_right W₂.linear_right
        (by
          intro y hy
          obtain ⟨hyΔ, -⟩ := hmem y hy
          rw [count_vars_rename, count_vars_rename, hc x hxΔ]
          by_cases hyx : y = x
          · simp [hyx]
          · simp only [hyx, ite_false, hc y hyΔ])
    have hcomp : ∀ Γ : Net S ℕ, ((Γ.bind fun w => var (g w)).bind fun w => var (ρ w)) =
        Γ.bind fun w => var (ρ (g w)) := by
      intro Γ
      rw [Net.bind_bind]
      rfl
    refine ⟨fun w => ρ (g w), W, hWW, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hcomp]
      exact W₁.equiv.trans hE₁
    · rw [← hcomp]
      exact W₂.equiv.trans hE₂
    · intro y hy
      have hyx : y ≠ x := fun e => hy (e ▸ hxΔ)
      have hgy : g y = y := by simp [hg, hyx]
      change ρ (g y) = y
      rw [hgy]
      exact hfix y fun hm => hy (hmem y hm).1
    · intro y hy
      rw [← hcomp, ← hcomp]
      exact hnf y hy
    · intro a b hab hne
      rw [← hcomp]
      exact hfree a b hab hne
  · simp only [not_exists, not_and] at hcon
    have hno : ∀ e ∈ Δ, ∀ a b, e = s(var a, var b) → a ∉ (Γ₁ + Δ.erase e).vars := by
      intro e he a b rfl
      exact hcon a b _ (Multiset.cons_erase he).symm
    refine ⟨fun w => w, Δ, hW, ?_, ?_, fun _ _ => rfl, ?_, ?_⟩
    · rw [bind_var_id]; exact Equiv.refl _
    · rw [bind_var_id]; exact Equiv.refl _
    · intro y hy
      rw [bind_var_id, bind_var_id]
      obtain ⟨e, he, hye⟩ := Multiset.mem_bind.1 hy
      obtain ⟨a, b, rfl⟩ := hW e he
      have hy₁ : y ∉ Γ₁.vars := by
        simp only [eqVars_mk, Term.vars_var, Multiset.mem_add, Multiset.mem_singleton] at hye
        rcases hye with rfl | rfl
        · have := hno _ he y b rfl
          rw [Net.vars_add, Multiset.mem_add, not_or] at this
          exact this.1
        · have := hno _ he y a Sym2.eq_swap
          rw [Net.vars_add, Multiset.mem_add, not_or] at this
          exact this.1
      refine ⟨hy₁, ?_⟩
      rw [← Multiset.count_eq_zero, ← hc y hy]
      exact Multiset.count_eq_zero.2 hy₁
    · intro a b hab hne
      rw [bind_var_id]
      have h0 := hno _ hab a b rfl
      have h0' : (Γ₁ + Δ.erase s(var a, var b)).vars.count a = 0 := Multiset.count_eq_zero.2 h0
      rw [← Multiset.cons_erase hab, Multiset.add_cons, Net.vars_cons, Multiset.count_add, h0']
      simp [hne]

-- ============================================================================================
-- 2. Solutions where every cell is `true`
-- ============================================================================================

/-- The value of a tree when the names have the values `ρ` and every cell is `true`. -/
def blind
    -- the values of the names
    (ρ : ℕ → Bool) :
    Term S ℕ → Bool
  | .var x => ρ x
  | .app _ _ => true

/-- A name has its value. -/
@[simp] theorem blind_var
    (ρ : ℕ → Bool)
    (x : ℕ) :
    blind ρ (var x : Term S ℕ) = ρ x := rfl

/-- A cell has the value `true`. -/
@[simp] theorem blind_app
    -- the values of the names
    (ρ : ℕ → Bool)
    -- the cell `α` and the trees on its auxiliary ports
    (α : S.Sym)
    (ts : Fin (S.arity α) → Term S ℕ) :
    blind ρ (app α ts) = true := rfl

/-- `ρ` solves `N` when every cell is `true`: the two sides of each equation have the same value. -/
def BlindSolves
    -- the values of the names, and the net
    (ρ : ℕ → Bool)
    (N : Net S ℕ) :
    Prop :=
  ∀ a b, s(a, b) ∈ N → blind ρ a = blind ρ b

/-- The values on the free names of `N` that extend to a solution of `N` where every cell is
`true`. -/
def BlindSol
    -- the net, and the values on its free names
    (N : Net S ℕ)
    (s : ℕ → Bool) :
    Prop :=
  ∃ ρ, BlindSolves ρ N ∧ ∀ p, N.vars.count p = 1 → ρ p = s p

/-- `ρ` solves a net with one more equation when it solves the equation and the rest. -/
theorem blindSolves_cons
    -- the values of the names, the equation `c = d`, and the rest of the net
    {ρ : ℕ → Bool}
    {c d : Term S ℕ}
    {N : Net S ℕ} :
    BlindSolves ρ (s(c, d) ::ₘ N)
      ↔ blind ρ c = blind ρ d ∧ BlindSolves ρ N := by
  constructor
  · intro h
    exact ⟨h c d (Multiset.mem_cons_self _ _), fun a b hab => h a b (Multiset.mem_cons_of_mem hab)⟩
  · rintro ⟨h1, h2⟩ a b hab
    rcases Multiset.mem_cons.1 hab with e | hm
    · rcases Sym2.eq_iff.1 e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact h1.symm
    · exact h2 a b hm

/-- The value of a tree after plugging `t` into `x` is its value with `x` given the value of
`t`. -/
theorem blind_subst
    -- the values of the names
    (ρ : ℕ → Bool)
    -- the tree `a`, and the tree `t` plugged into its name `x`
    (a : Term S ℕ)
    (x : ℕ)
    (t : Term S ℕ) :
    blind ρ (a.subst x t) = blind (Function.update ρ x (blind ρ t)) a := by
  cases a with
  | var y =>
    by_cases h : y = x
    · subst h
      simp [Term.subst]
    · simp [Term.subst, h]
  | app α ts => rfl

/-- The value of a tree depends only on the values of its names. -/
theorem blind_congr
    -- two valuations that agree on the names of the tree `a`
    {ρ ρ' : ℕ → Bool}
    {a : Term S ℕ}
    (h : ∀ y ∈ a.vars, ρ y = ρ' y) :
    blind ρ a = blind ρ' a := by
  cases a with
  | var y => exact h y (by simp)
  | app α ts => rfl

/-- A wire substitution does not change the values on the free names that extend to a solution
where every cell is `true`. -/
theorem Wire.blindSol_iff
    -- one wire substitution from `N` to `M`
    {N M : Net S ℕ}
    (h : Wire N M)
    -- the values on the free names
    (s : ℕ → Bool) :
    BlindSol N s ↔ BlindSol M s := by
  have hfree := h.free_iff
  obtain ⟨x, t, a, b, Δ, hlin, hx⟩ := h
  have hc := hlin x
  have hx1 := Multiset.one_le_count_iff_mem.2 hx
  simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
    Multiset.count_singleton_self] at hc hx1
  have ht : x ∉ t.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  have hΔ : x ∉ Δ.vars := fun h => by
    have := Multiset.one_le_count_iff_mem.2 h; omega
  constructor
  · rintro ⟨ρ, hs, hp⟩
    rw [blindSolves_cons, blindSolves_cons] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    have hu : Function.update ρ x (blind ρ t) = ρ := by
      rw [Function.update_eq_self_iff]; exact h1.symm
    refine ⟨ρ, blindSolves_cons.2 ⟨?_, h3⟩, fun p hp1 => hp p ((hfree p).2 hp1)⟩
    rw [blind_subst, blind_subst, hu]
    exact h2
  · rintro ⟨ρ, hs, hp⟩
    rw [blindSolves_cons] at hs
    obtain ⟨h2, h3⟩ := hs
    set ρ' := Function.update ρ x (blind ρ t) with hρ'
    have hts : blind ρ' t = blind ρ t :=
      blind_congr fun y hy => Function.update_of_ne (fun e => ht (by rw [← e]; exact hy)) _ _
    refine ⟨ρ', ?_, fun p hp1 => ?_⟩
    · rw [blindSolves_cons, blindSolves_cons]
      refine ⟨by simp [ρ', hts], by rwa [blind_subst, blind_subst] at h2, ?_⟩
      intro c d hcd
      have hv : ∀ y ∈ c.vars + d.vars, y ≠ x := fun y hy e => hΔ (e ▸ Multiset.mem_bind.2
        ⟨s(c, d), hcd, by simpa using hy⟩)
      rw [blind_congr (ρ' := ρ) fun y hy => Function.update_of_ne
          (hv y (Multiset.mem_add.2 (Or.inl hy))) _ _,
        blind_congr (a := d) (ρ' := ρ) fun y hy => Function.update_of_ne
          (hv y (Multiset.mem_add.2 (Or.inr hy))) _ _]
      exact h3 c d hcd
    · have hpx : p ≠ x := by
        rintro rfl
        simp only [Net.vars_cons, eqVars_mk, Term.vars_var, Multiset.count_add,
          Multiset.count_singleton_self] at hp1
        omega
      rw [show ρ' p = ρ p from Function.update_of_ne hpx _ _]
      exact hp p ((hfree p).1 hp1)

/-- **Nets that are the same graph have the same solutions where every cell is `true`** (an
invariant of the equivalence of Lafont 1997, Section 1.1, page 71, which sees the wires between
free names and not the cells). -/
theorem Equiv.blindSol_iff
    -- two nets that are the same graph
    {N M : Net S ℕ}
    (h : Equiv N M)
    -- the values on the free names
    (s : ℕ → Bool) :
    BlindSol N s ↔ BlindSol M s := by
  induction h with
  | rel _ _ h => exact Wire.blindSol_iff h s
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

-- ============================================================================================
-- 3. The pair of two cells
-- ============================================================================================

/-- The pair `γ(u) = δ(v)` of two cells plugged by their principal ports. -/
def pairNet
    -- the two symbols
    (γ δ : S.Sym)
    -- the names on their auxiliary ports
    (u : Fin (S.arity γ) → ℕ)
    (v : Fin (S.arity δ) → ℕ) :
    Net S ℕ :=
  {s(.app γ fun i => .var (u i), .app δ fun j => .var (v j))}

/-- A tree without cells is a name. -/
theorem eq_var_of_cells
    {t : Term S ℕ}
    (h : t.cells = 0) :
    ∃ x, t = var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | app α ts => simp at h

/-- With distinct names, a name occurs at most once among them. -/
theorem sum_ite_inj
    -- `n` distinct names
    {n : ℕ}
    {u : Fin n → ℕ}
    (hu : Function.Injective u)
    -- the name counted
    (y : ℕ) :
    (∑ i, if y = u i then 1 else 0) = if ∃ i, y = u i then 1 else 0 := by
  split_ifs with h
  · obtain ⟨i₀, rfl⟩ := h
    simp only [hu.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · exact Finset.sum_eq_zero fun i _ => ite_eq_right_iff.2 fun e => absurd ⟨i, e⟩ h

/-- **After one interaction up to wires, a pair of two cells leaves no cut** (Lafont 1997,
page 81: "if `Φ` is invertible, the reduction must be of length 1", since "`ρ_{i,j}` is supposed
to be reduced"; page 79: the right member of a rule is a reduced net). Let the rules of `I` be
linear and reduced. If the pair `γ(u) = δ(v)`, with pairwise distinct names on the auxiliary
ports, reduces in one interaction up to wires to `K`, then `K` has no cut. The interaction may
happen on any net that is the same graph as the pair; such a net is the cut with wires joining its
ports to the free names, and closed wires `a = a` (see the module docstring). -/
theorem stepE_pair_not_hasCut_of
    -- a system whose rules are linear and reduced
    {I : System S}
    (hlin : ∀ α β r, I.rule α β = some r → r.Linear)
    (hred : ∀ α β r, I.rule α β = some r → r.Reduced)
    -- two symbols, and pairwise distinct names on their auxiliary ports
    {γ δ : S.Sym}
    {u : Fin (S.arity γ) → ℕ}
    {v : Fin (S.arity δ) → ℕ}
    (hu : Function.Injective u)
    (hv : Function.Injective v)
    (huv : ∀ i j, u i ≠ v j)
    -- the pair `γ(u) = δ(v)` reduces in one interaction, up to wires, to `K`
    {K : Net S ℕ}
    (h : StepE I {s(.app γ fun i => .var (u i), .app δ fun j => .var (v j))} K) :
    -- then `K` has no cut
    ¬ K.HasCut := by
  classical
  obtain ⟨K₀, hE, hs⟩ := h
  change Equiv (pairNet γ δ u v) K₀ at hE
  -- The pair: its names are `u` and `v`, each once.
  have hPc : ∀ y, (Net.vars (pairNet γ δ u v)).count y =
      (∑ i, if y = u i then 1 else 0) + ∑ j, if y = v j then 1 else 0 := by
    intro y
    simp [pairNet, Multiset.count_sum', Multiset.count_singleton]
  have hPlin : Net.Linear (pairNet γ δ u v) := by
    intro y
    rw [hPc, sum_ite_inj hu, sum_ite_inj hv]
    split_ifs <;> omega
  have hPsol : ∀ s, BlindSol (pairNet γ δ u v) s := by
    intro s
    refine ⟨s, fun c d hcd => ?_, fun _ _ => rfl⟩
    rw [pairNet, Multiset.mem_singleton] at hcd
    rcases Sym2.eq_iff.1 hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := hs
  have hrl := hlin α β r hr
  -- The net `K₀` has only the two cells of the cut.
  have hc := hE.cells_eq
  have hP0 : Net.cells (pairNet γ δ u v) = γ ::ₘ δ ::ₘ 0 := by simp [pairNet, Net.cells]
  rw [hP0, Net.cells_cons, eqCells_mk, Term.cells_app, Term.cells_app] at hc
  have hcard := congrArg Multiset.card hc
  simp only [Multiset.card_cons, Multiset.card_zero, Multiset.card_add, Multiset.card_sum]
    at hcard
  have has0 : ∀ i, (as i).cells = 0 := fun i => Multiset.card_eq_zero.1
    ((Finset.sum_eq_zero_iff.1 (show ∑ i, Multiset.card (as i).cells = 0 by omega)) i
      (Finset.mem_univ _))
  have hbs0 : ∀ j, (bs j).cells = 0 := fun j => Multiset.card_eq_zero.1
    ((Finset.sum_eq_zero_iff.1 (show ∑ j, Multiset.card (bs j).cells = 0 by omega)) j
      (Finset.mem_univ _))
  have hΔ0 : Δ.cells = 0 := Multiset.card_eq_zero.1 (by omega)
  choose xs hxs using fun i => eq_var_of_cells (has0 i)
  choose ys hys using fun j => eq_var_of_cells (hbs0 j)
  obtain rfl : as = fun i => var (xs i) := funext hxs
  obtain rfl : bs = fun j => var (ys j) := funext hys
  have hWΔ : Wires Δ := by
    intro e he
    have hle : eqCells e ≤ 0 := hΔ0 ▸ Multiset.le_bind Δ he
    induction e using Sym2.ind with
    | _ a b =>
      rw [eqCells_mk, Multiset.le_zero] at hle
      obtain ⟨x, rfl⟩ := eq_var_of_cells (add_eq_zero.1 hle).1
      obtain ⟨y, rfl⟩ := eq_var_of_cells (add_eq_zero.1 hle).2
      exact ⟨x, y, rfl⟩
  -- Contract the wires of `Δ`, in the cut and in the instance.
  have hK₀ : s(Term.app α (fun i => var (xs i)), Term.app β fun j => var (ys j)) ::ₘ Δ =
      (s(Term.app α (fun i => var (xs i)), Term.app β fun j => var (ys j)) ::ₘ 0) + Δ := by
    rw [Multiset.cons_add, zero_add]
  have hK₀lin := hE.linear hPlin
  have hKlin := (Step.mk α β r hr _ _ Δ f hf hfresh).linear hlin hK₀lin
  rw [hK₀] at hK₀lin
  have hnf : ∀ y ∈ Δ.vars, ∀ w, y ≠ f w := fun y hy w e => hfresh w (by
    rw [Net.vars_cons, Multiset.mem_add]; exact Or.inr (e ▸ hy))
  obtain ⟨ρ, W, hWW, hE₁, hE₂, hfix, hnfW, hfree⟩ :=
    contract _ Δ _ (r.inst (fun i => var (xs i)) (fun j => var (ys j)) f) rfl hWΔ hK₀lin hKlin
      (by
        intro y hy
        rw [Rule.count_vars_inst r hrl]
        simp [Multiset.count_sum', Multiset.count_singleton, hnf y hy])
  have hΓ₁ : (Net.bind (fun w => var (ρ w))
      (s(Term.app α (fun i => var (xs i)), Term.app β fun j => var (ys j)) ::ₘ 0)) =
      s(Term.app α (fun i => var (ρ (xs i))), Term.app β fun j => var (ρ (ys j))) ::ₘ 0 := by
    simp [Net.bind]
  have hΓ₂ : (Net.bind (fun w => var (ρ w))
      (r.inst (fun i => var (xs i)) (fun j => var (ys j)) f)) =
      r.inst (fun i => var (ρ (xs i))) (fun j => var (ρ (ys j))) f := by
    rw [Rule.inst_bind_var]
    simp only [Term.bind_var]
    congr 1
    funext w
    exact hfix _ fun hm => hnf _ hm w rfl
  rw [hΓ₁] at hE₁ hnfW hfree
  rw [hΓ₂] at hE₂ hnfW
  have hEP := hE.trans ((Equiv.of_eq hK₀).trans hE₁)
  -- The wires left are closed: `a = a`.
  have hloop : ∀ a b, s(var a, var b) ∈ W → a = b := by
    intro a b hab
    by_contra hne
    have ha := hfree a b hab hne
    have hb := hfree b a (by rwa [Sym2.eq_swap]) (Ne.symm hne)
    obtain ⟨ρ', hs', hp'⟩ := (Equiv.blindSol_iff hEP fun y => decide (y = a)).1 (hPsol _)
    have := hs' (var a) (var b) (Multiset.mem_add.2 (Or.inr hab))
    rw [blind_var, blind_var, hp' a ha, hp' b hb] at this
    simp [Ne.symm hne] at this
  -- The free names of `P` are on the ports of the cut renamed.
  set X : Fin (S.arity α) → ℕ := fun i => ρ (xs i) with hX
  set Y : Fin (S.arity β) → ℕ := fun j => ρ (ys j) with hY
  have hFG : Finset.univ.image u ∪ Finset.univ.image v ⊆
      Finset.univ.image X ∪ Finset.univ.image Y := by
    intro p hp
    have hp1 : (Net.vars (pairNet γ δ u v)).count p = 1 := by
      rw [hPc, sum_ite_inj hu, sum_ite_inj hv]
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · have h2 : ¬ ∃ j, u i = v j := fun ⟨j, e⟩ => huv i j e
        simp [h2]
      · have h2 : ¬ ∃ i, v j = u i := fun ⟨i, e⟩ => huv i j e.symm
        simp [h2]
    have hK1 := (hEP.free_iff p).1 hp1
    have hpW : p ∉ W.vars := by
      intro hm
      obtain ⟨e, he, hpe⟩ := Multiset.mem_bind.1 hm
      obtain ⟨a, b, rfl⟩ := hWW e he
      obtain rfl := hloop a b he
      have h2 := Multiset.count_le_of_le p
        (show eqVars s(var a, var a) ≤ Net.vars W from Multiset.le_bind W he)
      simp only [eqVars_mk, Term.vars_var, Multiset.mem_add, Multiset.mem_singleton,
        or_self] at hpe
      subst hpe
      simp only [eqVars_mk, Term.vars_var, Multiset.count_add, Multiset.count_singleton_self]
        at h2
      rw [Net.vars_add, Multiset.count_add] at hK1
      omega
    rw [Net.vars_add, Multiset.count_add, Multiset.count_eq_zero.2 hpW, add_zero] at hK1
    have hpΓ := Multiset.one_le_count_iff_mem.1 hK1.ge
    simp only [Net.vars_cons, Net.vars_zero, add_zero, eqVars_mk, Term.vars_app, Term.vars_var,
      Multiset.mem_add, Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_singleton] at hpΓ
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, hX, hY]
    rcases hpΓ with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨j, rfl⟩
  have hFcard : (Finset.univ.image u ∪ Finset.univ.image v).card =
      S.arity γ + S.arity δ := by
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ hu,
      Finset.card_image_of_injective _ hv, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    rintro p ⟨i, rfl⟩ j e
    exact huv i j e.symm
  -- `P` and the cut have the same number of ports (by the cells, `Equiv.cells_eq`)
  have hGle := Finset.card_le_card hFG
  have hU := Finset.card_union_add_card_inter (Finset.univ.image X) (Finset.univ.image Y)
  have hXle : (Finset.univ.image X).card ≤ S.arity α := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := X)
  have hYle : (Finset.univ.image Y).card ≤ S.arity β := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := Y)
  have harity : S.arity γ + S.arity δ = S.arity α + S.arity β := by
    have h := congrArg (fun m => (m.map S.arity).sum) hc
    simp only [Term.cells_var, Finset.sum_const_zero, hΔ0] at h
    simpa [add_comm] using h
  have hXc : (Finset.univ.image X).card = S.arity α := by omega
  have hYc : (Finset.univ.image Y).card = S.arity β := by omega
  have hXY0 : (Finset.univ.image X ∩ Finset.univ.image Y).card = 0 := by omega
  have hXinj : Function.Injective X := by
    have := Finset.card_image_iff.1 (hXc.trans (by simp))
    exact fun a b e => this (by simp) (by simp) e
  have hYinj : Function.Injective Y := by
    have := Finset.card_image_iff.1 (hYc.trans (by simp))
    exact fun a b e => this (by simp) (by simp) e
  have hXYne : ∀ i j, X i ≠ Y j := by
    intro i j e
    have hm : X i ∈ Finset.univ.image X ∩ Finset.univ.image Y := by
      rw [Finset.mem_inter]
      exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), e ▸ Finset.mem_image_of_mem _
        (Finset.mem_univ _)⟩
    rw [Finset.card_eq_zero] at hXY0
    rw [hXY0] at hm
    exact Finset.notMem_empty _ hm
  -- The instance renamed, plus the closed wires `W`, has no cut.
  have hlin₂ : Net.Linear (r.inst (fun i => var (X i)) (fun j => var (Y j)) f + W) :=
    hE₂.linear hKlin
  have hΓlin : Net.Linear (r.inst (fun i => var (X i)) (fun j => var (Y j)) f) := fun y =>
    (by rw [Net.vars_add, Multiset.count_add]; omega : _ ≤ _).trans (hlin₂ y)
  rw [Net.hasCut_iff_of_equiv (show Equiv _ (r.inst (fun i => var (X i)) (fun j => var (Y j)) f + W)
    from hE₂)]
  intro hcut
  obtain ⟨A, B, zs, D, hA, hB, hN⟩ := hcut.chainCut
  have hnW : ∀ c d, s(c, d) ∈ W → ¬ c.IsCell := by
    intro c d hcd hcc
    obtain ⟨a, b, e⟩ := hWW _ hcd
    rcases Sym2.eq_iff.1 e with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact Cut.not_isCell_var _ hcc
  cases zs with
  | nil =>
    have hm : s(A, B) ∈ r.inst (fun i => var (X i)) (fun j => var (Y j)) f + W := by
      rw [hN]; simp
    rcases Multiset.mem_add.1 hm with hm | hm
    · obtain ⟨p, t, he, -⟩ := (hred α β r hr).mem_inst hm
      rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact Cut.not_isCell_var p hA
      · exact Cut.not_isCell_var p hB
    · exact hnW A B hm hA
  | cons z zs =>
    have hm : s(A, var z) ∈ r.inst (fun i => var (X i)) (fun j => var (Y j)) f + W := by
      rw [hN]; simp
    rcases Multiset.mem_add.1 hm with hm | hm
    · obtain ⟨p, t, he, hp⟩ := (hred α β r hr).mem_inst hm
      rcases Sym2.eq_iff.1 he with ⟨rfl, -⟩ | ⟨-, hz⟩
      · exact Cut.not_isCell_var p hA
      · cases hz
        have h1 := Rule.count_inst_port hrl hXinj hYinj hXYne hΓlin hp
        have hzΓ : z ∈ Net.vars (r.inst (fun i => var (X i)) (fun j => var (Y j)) f) :=
          Multiset.mem_bind.2 ⟨_, hm, by simp⟩
        have hzW : z ∉ W.vars := fun hw => (hnfW z hw).2 hzΓ
        have h2 : (Net.vars (r.inst (fun i => var (X i)) (fun j => var (Y j)) f + W)).count z
            ≤ 1 := by
          rw [Net.vars_add, Multiset.count_add, Multiset.count_eq_zero.2 hzW]
          omega
        rw [hN, Net.vars_add, Multiset.count_add, Cut.count_vars_chain] at h2
        simp only [List.count_cons_self] at h2
        omega
    · exact hnW A _ hm hA

end PairStepE

-- ============================================================================================
-- 4. Main results: no cut after the interaction of a pair, and `L = M = 1`
-- ============================================================================================

/-- **After one interaction up to wires, a pair of two cells leaves no cut** (Lafont 1997,
page 81: "if `Φ` is invertible, the reduction must be of length 1", since "`ρ_{i,j}` is supposed
to be reduced"; page 79: the right member of a rule is a reduced net). In a well-formed system, if
the pair `γ(u) = δ(v)`, with pairwise distinct names on its auxiliary ports, reduces in one
interaction up to wires to `K`, then `K` has no cut. Only the linearity and the reducedness of
the rules are used (`PairStepE.stepE_pair_not_hasCut_of`). -/
theorem System.WellFormed.stepE_pair_not_hasCut
    -- a well-formed system
    {I : System S}
    (hI : I.WellFormed)
    -- two symbols, and pairwise distinct names on their auxiliary ports
    {γ δ : S.Sym}
    {u : Fin (S.arity γ) → ℕ}
    {v : Fin (S.arity δ) → ℕ}
    (hu : Function.Injective u)
    (hv : Function.Injective v)
    (huv : ∀ i j, u i ≠ v j)
    -- the pair `γ(u) = δ(v)` reduces in one interaction, up to wires, to `K`
    {K : Net S ℕ}
    (h : StepE I {s(.app γ fun i => .var (u i), .app δ fun j => .var (v j))} K) :
    -- then `K` has no cut
    ¬ K.HasCut :=
  PairStepE.stepE_pair_not_hasCut_of hI.linear hI.reduced hu hv huv h

namespace Translation

variable {Φ : Translation S S'}

/-- **`L = M = 1` if `Φ` is invertible** (Lafont 1997, page 81: "if `Φ` is invertible, the
reduction must be of length 1 … `L = M = 1` if `Φ` is invertible"). Let `Φ` be invertible and
compatible, with `I` and `I'` well-formed. Then `Φ` simulates every rule of `I` in exactly one
interaction up to wires. This is `Invertible.compatibleWithin_one`, whose hypothesis on the pairs
of two cells of `I'` is `System.WellFormed.stepE_pair_not_hasCut`. -/
theorem Invertible.compatibleWithin_one_of_wellFormed
    -- the two systems
    {I : System S}
    {I' : System S'}
    -- the translation is invertible
    (hΦ : Φ.Invertible)
    -- both systems are well formed
    (hI : I.WellFormed)
    (hI' : I'.WellFormed)
    -- the translation is compatible with reduction
    (h : Φ.Compatible I I') :
    -- then it simulates every rule of `I` in exactly one interaction of `I'`
    Φ.CompatibleWithin I I' 1 1 :=
  hΦ.compatibleWithin_one hI hI'.linear
    (fun _ _ _ _ hu hv huv _ hK => hI'.stepE_pair_not_hasCut hu hv huv hK) h

end Translation

end INet
