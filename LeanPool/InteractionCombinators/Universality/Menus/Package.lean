/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.Multiplexors.Multiplexor

/-!
# Lafont, "Interaction Combinators" (1997): packages and erasing them

A package (page 80) is a reduced net with one free port, which by Proposition 2 is a tree `τ`
whose leaves are joined in pairs by a wiring `ω`. In the text presentation it is a tree in which
every name occurs exactly twice; its root is the free port. The corollary of Lemma 2 (page 84)
says that a package plugged into an `era` reduces to the empty net.

Contents, in the order of the file:

1. Definition: `Term.IsPackage`, a tree in which every name occurs twice.
2. Auxiliary lemmas: packages: `isPackage_of_vars_eq_zero`, `IsPackage.vars_eq`,
   `isPackage_mkEra`, `IsPackage.mkCon`, `IsPackage.mkDup`, `isPackage_mkCon_var`.
3. Auxiliary lemmas: two `era` cells on a wire: `linear_of_add`, `stepE_era_wire`.
4. Main results: `erase_wiring`, Lemma 2 (ii) (page 85), a wiring with an `era` on each of its
   free ports reduces to the empty net; `erase_package`, the corollary on page 84, a package
   plugged into an `era` reduces to the empty net.
5. An example showing that the hypotheses of `erase_package` can hold.
-/

@[expose] public section

namespace INet

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- A package (Lafont, page 80): a tree whose leaves are joined in pairs by internal wires. In the
text presentation every name of the tree occurs exactly twice, and the root is the only free
port. -/
def Term.IsPackage
    -- the signature and the tree
    {S : Signature}
    (π : Term S ℕ) :
    Prop :=
  ∀ x ∈ π.vars, π.vars.count x = 2

-- ============================================================================================
-- 2. Auxiliary lemmas: packages
-- ============================================================================================

namespace Term

variable {S : Signature}

/-- A tree with no leaf is a package (page 80, the case of an empty wiring). -/
theorem isPackage_of_vars_eq_zero
    -- a tree with no name
    {π : Term S ℕ}
    (h : π.vars = 0) :
    π.IsPackage := by
  intro x hx
  simp [h] at hx

/-- The leaves of a package are its wires, each counted twice (page 80: the leaves of `τ` are
paired by the wiring `ω`). -/
theorem IsPackage.vars_eq
    -- the package
    {π : Term S ℕ}
    (hπ : π.IsPackage) :
    -- its names are its wires, each taken twice
    π.vars = π.vars.dedup + π.vars.dedup := by
  ext x
  rw [Multiset.count_add]
  by_cases hx : x ∈ π.vars
  · rw [hπ x hx, Multiset.count_eq_one_of_mem (Multiset.nodup_dedup _)
      (Multiset.mem_dedup.2 hx)]
  · rw [Multiset.count_eq_zero_of_notMem hx,
      Multiset.count_eq_zero_of_notMem (fun h => hx (Multiset.mem_dedup.1 h))]

end Term

namespace Comb

open Term

/-- An `era` is a package with no wire (page 80). -/
theorem isPackage_mkEra :
    (mkEra : Term sig ℕ).IsPackage :=
  isPackage_of_vars_eq_zero vars_mkEra

/-- Two packages with no common name, plugged into the auxiliary ports of a `con`, form a package
(page 80). -/
theorem IsPackage.mkCon
    -- the two packages
    {a b : Term sig ℕ}
    (ha : a.IsPackage)
    (hb : b.IsPackage)
    -- they have no common name
    (hab : ∀ x ∈ a.vars, x ∉ b.vars) :
    (mkCon a b).IsPackage := by
  intro x hx
  rw [vars_mkCon, Multiset.mem_add] at hx
  rw [vars_mkCon, Multiset.count_add]
  rcases hx with hx | hx
  · rw [ha x hx, Multiset.count_eq_zero_of_notMem (hab x hx)]
  · have : x ∉ a.vars := fun h => hab x h hx
    rw [hb x hx, Multiset.count_eq_zero_of_notMem this]

/-- Two packages with no common name, plugged into the auxiliary ports of a `dup`, form a package
(page 80). -/
theorem IsPackage.mkDup
    -- the two packages
    {a b : Term sig ℕ}
    (ha : a.IsPackage)
    (hb : b.IsPackage)
    -- they have no common name
    (hab : ∀ x ∈ a.vars, x ∉ b.vars) :
    (mkDup a b).IsPackage := by
  intro x hx
  rw [vars_mkDup, Multiset.mem_add] at hx
  rw [vars_mkDup, Multiset.count_add]
  rcases hx with hx | hx
  · rw [ha x hx, Multiset.count_eq_zero_of_notMem (hab x hx)]
  · have : x ∉ a.vars := fun h => hab x h hx
    rw [hb x hx, Multiset.count_eq_zero_of_notMem this]

/-- A `con` whose two auxiliary ports are joined by a wire is a package (page 80). -/
theorem isPackage_mkCon_var
    -- the wire joining the two auxiliary ports
    (x : ℕ) :
    (mkCon (var x) (var x) : Term sig ℕ).IsPackage := by
  intro y hy
  simp only [vars_mkCon, vars_var, Multiset.mem_add, Multiset.mem_singleton, or_self] at hy
  subst hy
  simp

-- ============================================================================================
-- 3. Auxiliary lemmas: two `era` cells on a wire
-- ============================================================================================

/-- A sub-net of a linear net is linear. -/
theorem linear_of_add
    -- the two parts of the net
    {N M : CNet}
    -- the whole net is linear
    (h : (N + M).Linear) :
    M.Linear := by
  intro x
  have := h x
  rw [Net.vars_add, Multiset.count_add] at this
  omega

/-- Two erasers joined by the wire `x` erase each other: a wire substitution makes them an active
pair, then they annihilate (page 85, one wire of Lemma 2 (ii)). -/
theorem stepE_era_wire
    -- the wire joining the two `era` cells
    (x : ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear
    (hlin : Net.Linear (s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ Δ)) :
    -- one interaction, after a wire substitution, leaves `Δ`
    StepE system (s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ Δ) Δ := by
  have e : (s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ Δ : CNet) =
      s(var x, mkEra) ::ₘ s(mkEra, var x) ::ₘ Δ := by rw [Sym2.eq_swap]
  have hw := Wire.mk x mkEra mkEra (var x) Δ (hlin.cast e) (by simp)
  rw [subst_var_self, subst_of_notMem (by simp)] at hw
  exact ⟨_, (hw.cast e.symm rfl).equiv, step_era_era Δ⟩

-- ============================================================================================
-- 4. Main results: erasing a wiring and a package
-- ============================================================================================

/-- Lafont's Lemma 2 (ii), page 85: a wiring `D` with an eraser on every free port reduces to the
empty net. Each wire `x` of `D` has an eraser at both ends; the two erasers are joined by a wire,
so they interact after a wire substitution, hence `StepsE`. -/
theorem erase_wiring
    -- the wires of the wiring; each has an `era` at both ends
    (D : Multiset ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear
    (hlin : Net.Linear ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ)) :
    -- the `era` cells erase each other, up to wires, and leave `Δ`
    StepsE system ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ) Δ := by
  induction D using Multiset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | cons x D ih =>
    have e : ((x ::ₘ D + x ::ₘ D).map (fun x => s(mkEra, Term.var x)) + Δ : CNet) =
        s(mkEra, var x) ::ₘ s(mkEra, var x) ::ₘ
          ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ) := by
      simp only [Multiset.add_cons, Multiset.cons_add, Multiset.map_cons]
    rw [e] at hlin ⊢
    have hrest : Net.Linear ((D + D).map (fun x => s(mkEra, Term.var x)) + Δ) :=
      linear_of_add (N := {s(mkEra, var x), s(mkEra, var x)})
        (hlin.cast (by simp only [Multiset.insert_eq_cons, Multiset.cons_add,
          Multiset.singleton_add]))
    exact Relation.ReflTransGen.head (stepE_era_wire x _ hlin) (ih hrest)

/-- The corollary of Lemma 2 on page 84: a package `π` plugged into an eraser reduces to the empty
net. Lemma 2 (i) leaves an eraser on each leaf of `π`; the leaves are joined in pairs, and
Lemma 2 (ii) erases the wiring. -/
theorem erase_package
    -- the package: every name occurs twice
    (π : Term sig ℕ)
    (hπ : π.IsPackage)
    -- the rest of the net
    (Δ : CNet)
    -- the net we start from is linear: the package plugged into an `era`, and `Δ`
    (hlin : Net.Linear (s(mkEra, π) ::ₘ Δ)) :
    -- the package is erased, up to wires, and `Δ` is left
    StepsE system (s(mkEra, π) ::ₘ Δ) Δ := by
  have h1 := erase_tree π Δ
  rw [hπ.vars_eq] at h1
  exact h1.stepsE.trans
    (erase_wiring _ Δ (h1.linear system_wellFormed.linear hlin))

-- ============================================================================================
-- 5. The hypotheses can hold
-- ============================================================================================

/-- The hypotheses of `erase_package` hold: a `con` whose auxiliary ports are joined by a wire,
plugged into an eraser, reduces to the empty net. -/
example :
    StepsE system ({s(mkEra, mkCon (var 0) (var 0))} : CNet) 0 := by
  have h := erase_package (mkCon (var 0) (var 0)) (isPackage_mkCon_var 0) 0 (by
    intro y
    simp only [Net.vars_cons, Net.vars_zero, eqVars_mk, vars_mkEra, vars_mkCon, vars_var,
      zero_add, add_zero, Multiset.count_add, Multiset.count_singleton]
    split_ifs <;> omega)
  simpa using h

end Comb

end INet
