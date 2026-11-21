/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Text.Rename
public import LeanPool.InteractionCombinators.Core.Translation
public import Mathlib.Order.SuccPred.Nat

/-!
# Instances of a principal net

The names given to the internal wires of an instance of a principal net do not matter: two
instances of the same principal net, with the same trees plugged into the auxiliary ports, are the
same graph (`PNet.equiv_inst`).

The proof renames the internal wires one at a time, first to a block of unused names and from
there to the names of the other instance.

A net is a graph whose wires have no names (p. 72). A principal net (p. 79) is written here as a
tree over its auxiliary ports and some internal wires (`PNet`); an instance gives names to those
wires and plugs trees into the auxiliary ports.

Contents, in the order of the file:

1. Auxiliary lemmas on plugging: `Term.bind_bind` and `Net.bind_bind`, plugging twice is
   plugging the composite once.
2. Auxiliary lemmas on the names of an instance: `PNet.count_vars_inst`,
   `PNet.facts_of_linear` (in a linear net, the internal wires of an instance have distinct
   names used nowhere else), `PNet.facts_of_notMem`.
3. Auxiliary lemma: `PNet.equiv_inst_fresh`, renaming the internal wires to unused names.
4. Main result: `PNet.equiv_inst`, two instances of the same principal net with the same
   plugged trees are the same graph.
-/

@[expose] public section

namespace INet

variable {S : Signature} {n : ℕ}

open Term

-- ============================================================================================
-- 1. Auxiliary lemmas on plugging
-- ============================================================================================

/-- Plugging trees into the names of a tree twice is plugging the composite once. -/
theorem Term.bind_bind
    -- the names of the three trees
    {ν μ κ : Type}
    -- what is plugged first, then second
    (f : ν → Term S μ)
    (g : μ → Term S κ)
    -- the tree
    (t : Term S ν) :
    (t.bind f).bind g = t.bind fun x => (f x).bind g := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    change app α _ = app α _
    congr 1
    funext i
    exact ih i

/-- Plugging trees into the names of a net twice is plugging the composite once. -/
theorem Net.bind_bind
    -- the names of the three nets
    {ν μ κ : Type}
    -- what is plugged first, then second
    (f : ν → Term S μ)
    (g : μ → Term S κ)
    -- the net
    (N : Net S ν) :
    (N.bind f).bind g = N.bind fun x => (f x).bind g := by
  unfold Net.bind
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => simp [Term.bind_bind]

-- ============================================================================================
-- 2. Auxiliary lemmas on the names of an instance
-- ============================================================================================

namespace PNet

/-- The names of an instance: those of the trees plugged into the ports, and both ends of each
internal wire. -/
theorem count_vars_inst
    -- the principal net
    (p : PNet S n)
    -- the trees plugged into its auxiliary ports, and the names of its internal wires
    (args : Fin n → Term S ℕ)
    (F : Fin p.internal → ℕ)
    -- the name whose occurrences are counted
    (z : ℕ) :
    -- the occurrences in the plugged trees, and two for each internal wire named `z`
    (p.inst args F).vars.count z =
      ∑ i, (args i).vars.count z + 2 * ∑ w, if z = F w then 1 else 0 := by
  rw [inst, Term.vars_bind, Multiset.count_bind_fintype, Fintype.sum_sum_type]
  simp only [p.port_count, p.internal_count, one_mul, Sum.elim_inl, Sum.elim_inr, Term.vars_var,
    Multiset.count_singleton, Finset.mul_sum, mul_ite, mul_one, mul_zero]

variable
  -- the principal net, the trees plugged into its auxiliary ports, and two namings of its
  -- internal wires
  {p : PNet S n} {args : Fin n → Term S ℕ} {f h : Fin p.internal → ℕ}
  -- the tree on the other side of the equation of the instance, and the rest of the net
  {r : Term S ℕ}
  {Δ : Net S ℕ}

/-- In a linear net, the internal wires of an instance have pairwise distinct names, used nowhere
else. -/
theorem facts_of_linear
    -- the net `r = p.inst args f, Δ` is linear
    (hlin : Net.Linear (s(r, p.inst args f) ::ₘ Δ)) :
    -- the internal wires have pairwise distinct names
    Function.Injective f
      -- and the name of each of them occurs neither in `r`, nor in the plugged trees, nor in `Δ`
      ∧ ∀ w, f w ∉ r.vars ∧ (∀ i, f w ∉ (args i).vars) ∧ f w ∉ Δ.vars := by
  have key : ∀ w, r.vars.count (f w) + (∑ i, (args i).vars.count (f w) +
      2 * ∑ w', if f w = f w' then 1 else 0) + Δ.vars.count (f w) ≤ 2 := by
    intro w
    have := hlin (f w)
    simpa only [Net.vars_cons, eqVars_mk, Multiset.count_add, count_vars_inst] using this
  have one : ∀ w, 1 ≤ ∑ w', if f w = f w' then 1 else 0 := fun w =>
    calc 1 = if f w = f w then 1 else 0 := (ite_eq_left rfl).symm
      _ ≤ ∑ w', if f w = f w' then 1 else 0 :=
        Finset.single_le_sum (f := fun w' => if f w = f w' then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
  refine ⟨fun w₀ w₁ heq => ?_, fun w => ⟨?_, ?_, ?_⟩⟩
  · by_contra hne
    have h2 : ∑ w' ∈ ({w₀, w₁} : Finset _), (if f w₀ = f w' then 1 else 0) ≤
        ∑ w', if f w₀ = f w' then 1 else 0 :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_pair hne] at h2
    simp only [heq, ite_true] at h2
    have := key w₀
    simp only [heq] at this
    omega
  · exact Multiset.count_eq_zero.1 (by have := key w; have := one w; omega)
  · intro i
    refine Multiset.count_eq_zero.1 ?_
    have hle : (args i).vars.count (f w) ≤ ∑ i, (args i).vars.count (f w) :=
      Finset.single_le_sum (f := fun i => (args i).vars.count (f w))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := key w; have := one w; omega
  · exact Multiset.count_eq_zero.1 (by have := key w; have := one w; omega)

/-- A name that does not occur in the net is not a name of the instance. -/
theorem facts_of_notMem
    -- a name that does not occur in the net `r = p.inst args f, Δ`
    {y : ℕ}
    (hy : y ∉ Net.vars (s(r, p.inst args f) ::ₘ Δ)) :
    -- it occurs neither in `r`, nor in the plugged trees, it names no internal wire, and it
    -- does not occur in `Δ`
    y ∉ r.vars ∧ (∀ i, y ∉ (args i).vars) ∧ (∀ w, y ≠ f w) ∧ y ∉ Δ.vars := by
  have h0 := Multiset.count_eq_zero_of_notMem hy
  simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, count_vars_inst] at h0
  refine ⟨Multiset.count_eq_zero.1 (by omega), fun i => ?_, fun w hw => ?_,
    Multiset.count_eq_zero.1 (by omega)⟩
  · refine Multiset.count_eq_zero.1 ?_
    have hle : (args i).vars.count y ≤ ∑ i, (args i).vars.count y :=
      Finset.single_le_sum (f := fun i => (args i).vars.count y)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · have hle : (if y = f w then 1 else 0) ≤ ∑ w', if y = f w' then 1 else 0 :=
      Finset.single_le_sum (f := fun w' => if y = f w' then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
    rw [ite_eq_left hw] at hle
    omega

-- ============================================================================================
-- 3. Auxiliary lemma: renaming to unused names
-- ============================================================================================

/-- Renaming the internal wires of an instance to a family of unused names, one wire at a time. -/
theorem equiv_inst_fresh
    -- the net `r = p.inst args f, Δ` is linear
    (hlin : Net.Linear (s(r, p.inst args f) ::ₘ Δ))
    -- the new names are pairwise distinct and do not occur in the net
    (hh : Function.Injective h)
    (hfresh : ∀ w, h w ∉ Net.vars (s(r, p.inst args f) ::ₘ Δ)) :
    -- the instance with the new names is the same graph
    Equiv (s(r, p.inst args f) ::ₘ Δ) (s(r, p.inst args h) ::ₘ Δ) := by
  obtain ⟨hf, hff⟩ := facts_of_linear hlin
  have hhf := fun w => facts_of_notMem (hfresh w)
  -- after `k` wires have been renamed
  let F : ℕ → Fin p.internal → ℕ := fun k w => if (w : ℕ) < k then h w else f w
  have main : ∀ k, k ≤ p.internal →
      Equiv (s(r, p.inst args f) ::ₘ Δ) (s(r, p.inst args (F k)) ::ₘ Δ) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : F 0 = f := by funext w; simp [F]
      rw [this]
      exact Equiv.refl _
    | succ k ih =>
      intro hk
      have E := ih (by omega)
      have Lk := E.linear hlin
      let kk : Fin p.internal := ⟨k, by omega⟩
      -- the wire `f kk` has its two ends in the instance, and `h kk` is unused
      have hFx : ∀ w, (f kk = F k w) ↔ w = kk := by
        intro w
        simp only [F]
        constructor
        · intro heq
          split_ifs at heq with hw
          · exact absurd heq.symm ((hhf w).2.2.1 kk)
          · exact (hf heq).symm
        · rintro rfl
          simp [kk]
      have hFy : ∀ w, h kk ≠ F k w := by
        intro w heq
        simp only [F] at heq
        split_ifs at heq with hw
        · have := congrArg Fin.val (hh heq)
          simp only [kk] at this
          omega
        · exact (hhf kk).2.2.1 w heq
      have hx : (Net.vars (s(r, p.inst args (F k)) ::ₘ Δ)).count (f kk) = 2 := by
        simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, count_vars_inst]
        have hsum : ∑ w, (if f kk = F k w then 1 else 0) = 1 := by
          rw [Finset.sum_eq_single kk]
          · rw [ite_eq_left ((hFx kk).2 rfl)]
          · intro w _ hw
            exact ite_eq_right fun h => hw ((hFx w).1 h)
          · simp
        have hargs : ∑ i, (args i).vars.count (f kk) = 0 :=
          Finset.sum_eq_zero fun i _ => Multiset.count_eq_zero_of_notMem ((hff kk).2.1 i)
        rw [hsum, hargs, Multiset.count_eq_zero_of_notMem (hff kk).1,
          Multiset.count_eq_zero_of_notMem (hff kk).2.2]
      have hy : h kk ∉ Net.vars (s(r, p.inst args (F k)) ::ₘ Δ) := by
        refine Multiset.count_eq_zero.1 ?_
        simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, count_vars_inst]
        have hsum : ∑ w, (if h kk = F k w then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun w _ => ite_eq_right (hFy w)
        have hargs : ∑ i, (args i).vars.count (h kk) = 0 :=
          Finset.sum_eq_zero fun i _ => Multiset.count_eq_zero_of_notMem ((hhf kk).2.1 i)
        rw [hsum, hargs, Multiset.count_eq_zero_of_notMem (hhf kk).1,
          Multiset.count_eq_zero_of_notMem (hhf kk).2.2.2]
      have R := Net.equiv_rename Lk hx hy
      -- the renamed net is the next instance
      have hstep : (p.inst args (F k)).subst (f kk) (var (h kk)) = p.inst args (F (k + 1)) := by
        rw [inst, inst, Term.subst, Term.bind_bind]
        congr 1
        funext q
        cases q with
        | inl i => exact subst_of_notMem ((hff kk).2.1 i)
        | inr w =>
          change (if F k w = f kk then var (h kk) else var (F k w)) = var (F (k + 1) w)
          by_cases hw : w = kk
          · subst hw
            have : F k kk = f kk := ((hFx kk).2 rfl).symm
            simp [this, F, kk]
          · have hne : ¬ F k w = f kk := fun h => hw ((hFx w).1 h.symm)
            have hval : (w : ℕ) ≠ k := fun h => hw (Fin.ext h)
            rw [ite_eq_right hne]
            simp only [F]
            by_cases hlt : (w : ℕ) < k
            · rw [ite_eq_left hlt, ite_eq_left (by omega)]
            · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      rw [Net.rename_cons, subst_of_notMem (hff kk).1, hstep,
        Net.rename_of_notMem _ (hff kk).2.2] at R
      exact E.trans R
  have hend : F p.internal = h := by
    funext w
    simp [F]
  have := main p.internal le_rfl
  rwa [hend] at this

-- ============================================================================================
-- 4. Main result
-- ============================================================================================

/-- **Instances of a principal net are the same graph.** In linear nets, the names of the internal
wires of an instance do not matter: a net is a graph, its wires have no names (p. 72). -/
theorem equiv_inst
    -- a second naming of the internal wires
    {g : Fin p.internal → ℕ}
    -- the two nets `r = p.inst args f, Δ` and `r = p.inst args g, Δ` are linear
    (hf : Net.Linear (s(r, p.inst args f) ::ₘ Δ))
    (hg : Net.Linear (s(r, p.inst args g) ::ₘ Δ)) :
    -- they are the same graph
    Equiv (s(r, p.inst args f) ::ₘ Δ) (s(r, p.inst args g) ::ₘ Δ) := by
  -- a block of names above every name of both nets
  let K : ℕ := max (Net.vars (s(r, p.inst args f) ::ₘ Δ)).sup
    (Net.vars (s(r, p.inst args g) ::ₘ Δ)).sup + 1
  have hinj : Function.Injective fun w : Fin p.internal => K + (w : ℕ) :=
    fun a b hab => Fin.ext (by simpa using hab)
  have h1 := equiv_inst_fresh (h := fun w => K + (w : ℕ)) hf hinj fun w hw => by
    have := Multiset.le_sup hw
    simp only [K] at this
    omega
  have h2 := equiv_inst_fresh (h := fun w => K + (w : ℕ)) hg hinj fun w hw => by
    have := Multiset.le_sup hw
    simp only [K] at this
    omega
  exact h1.trans h2.symm

end PNet

end INet
