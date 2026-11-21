/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Combinators

/-!
# Lafont, "Interaction Combinators" (1997): duplication of a tree

Lemma 3 (i), page 87: a `dup` plugged into the root of a tree without `dup` copies the tree,
leaving one `dup` on each leaf.

The proof has two halves. `dup_tree` is the reduction: interactions only, ending in a "flat" net
with one new cell per equation. `flat_equiv_nested` shows that the flat net is the same graph as
the one Lafont draws, by wire substitution only.

Contents, in the order of the file:

1. Definitions: `DupFree`, the trees without `dup`; `dupNet`, the flat net left by the
   duplication; `Copy` and `nested`, the net of Lafont's picture.
2. Auxiliary lemmas: the equations of the definitions, `dupFree_mkCon`, `dupFree_mkDup`,
   `dupNet_var`, `dupNet_mkEra`, `dupNet_mkCon`, `nested_var`, `nested_mkEra`, `nested_mkCon`.
3. The reduction: `dup_tree`, Lemma 3 (i) in flat form.
4. The flat net is the drawn net: `flat_equiv_nested`.
5. Main result: `dup_tree_nested`, Lemma 3 (i) as drawn.
-/

@[expose] public section

namespace INet.Comb

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- Trees built without `dup`. -/
def DupFree : Term sig ℕ → Prop
  | .var _ => True
  | .app .con ts => DupFree (ts (0 : Fin 2)) ∧ DupFree (ts (1 : Fin 2))
  | .app .dup _ => False
  | .app .era _ => True

/-- The net obtained by pushing a `dup` with auxiliary trees `u`, `v` through the tree `τ`,
together with the next unused name. New wires are numbered from `n`. -/
def dupNet
    -- the first name of the new wires
    (n : ℕ)
    -- the trees on the auxiliary ports of the `dup`
    (u v : Term sig ℕ) :
    -- the tree `τ` the `dup` is pushed through, to the net and the next unused name
    Term sig ℕ → CNet × ℕ
  | .var x => ({s(mkDup u v, var x)}, n)
  | .app .era _ => (s(mkEra, u) ::ₘ {s(mkEra, v)}, n)
  | .app .con ts =>
    let ra := dupNet (n + 4) (var n) (var (n + 1)) (ts (0 : Fin 2))
    let rb := dupNet ra.2 (var (n + 2)) (var (n + 3)) (ts (1 : Fin 2))
    (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
      (ra.1 + rb.1), rb.2)
  | .app .dup _ => (0, n)

/-- Two copies of a tree, the `dup` cells left on its leaves, and the next unused name. -/
structure Copy where
  /-- The first copy. -/
  l : Term sig ℕ
  /-- The second copy. -/
  r : Term sig ℕ
  /-- One `dup` on each original leaf, joining the two copies of the leaf. -/
  E : CNet
  /-- The next unused name. -/
  k : ℕ

/-- Lafont's picture for Lemma 3 (i): the copies of `τ` use new leaf names from `k` on, and each
original leaf `x` is plugged into a `dup` joining its two copies. -/
def nested
    -- the first name of the new leaves
    (k : ℕ) :
    -- the tree `τ` to its two copies
    Term sig ℕ → Copy
  | .var x => ⟨var k, var (k + 1), {s(var x, mkDup (var k) (var (k + 1)))}, k + 2⟩
  | .app .era _ => ⟨mkEra, mkEra, 0, k⟩
  | .app .con ts =>
    let rb := nested k (ts (1 : Fin 2))
    let ra := nested rb.k (ts (0 : Fin 2))
    ⟨mkCon ra.l rb.l, mkCon ra.r rb.r, ra.E + rb.E, ra.k⟩
  | .app .dup _ => ⟨mkEra, mkEra, 0, k⟩

-- ============================================================================================
-- 2. Auxiliary lemmas: the equations of the definitions
-- ============================================================================================

-- a `con` has no `dup` if and only if neither of its subtrees has one
@[simp] theorem dupFree_mkCon
    {a b : Term sig ℕ} :
    DupFree (mkCon a b) ↔ DupFree a ∧ DupFree b := Iff.rfl

-- a `dup` cell is not without `dup`
@[simp] theorem dupFree_mkDup
    {a b : Term sig ℕ} :
    ¬ DupFree (mkDup a b) := id

-- pushing a `dup` onto a leaf leaves the `dup` plugged into the leaf
theorem dupNet_var
    (n : ℕ)
    (u v : Term sig ℕ)
    (x : ℕ) :
    dupNet n u v (var x) = ({s(mkDup u v, var x)}, n) := rfl

-- pushing a `dup` through an `era` leaves one `era` on each auxiliary port
theorem dupNet_mkEra
    (n : ℕ)
    (u v : Term sig ℕ) :
    dupNet n u v mkEra = (s(mkEra, u) ::ₘ {s(mkEra, v)}, n) := rfl

-- pushing a `dup` through a `con` leaves two `con` cells, and pushes a `dup` through each
-- subtree: `a` with the names from `n + 4`, then `b` with the names left by `a`
theorem dupNet_mkCon
    (n : ℕ)
    (u v a b : Term sig ℕ) :
    dupNet n u v (mkCon a b) =
      (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
        ((dupNet (n + 4) (var n) (var (n + 1)) a).1 +
          (dupNet (dupNet (n + 4) (var n) (var (n + 1)) a).2 (var (n + 2)) (var (n + 3)) b).1),
        (dupNet (dupNet (n + 4) (var n) (var (n + 1)) a).2 (var (n + 2)) (var (n + 3)) b).2) :=
  rfl

-- the copies of a leaf are two new leaves, joined to the old one by a `dup`
theorem nested_var
    (k x : ℕ) :
    nested k (var x) = ⟨var k, var (k + 1), {s(var x, mkDup (var k) (var (k + 1)))}, k + 2⟩ := rfl

-- the copies of an `era` are two `era` cells
theorem nested_mkEra
    (k : ℕ) :
    nested k mkEra = ⟨mkEra, mkEra, 0, k⟩ := rfl

-- the copies of a `con` are two `con` cells on the copies of the subtrees: `b` with the names
-- from `k`, then `a` with the names left by `b`
theorem nested_mkCon
    (k : ℕ)
    (a b : Term sig ℕ) :
    nested k (mkCon a b) =
      ⟨mkCon (nested (nested k b).k a).l (nested k b).l,
        mkCon (nested (nested k b).k a).r (nested k b).r,
        (nested (nested k b).k a).E + (nested k b).E, (nested (nested k b).k a).k⟩ := rfl

-- ============================================================================================
-- 3. The reduction: Lemma 3 (i) in flat form
-- ============================================================================================

/-- Lafont's Lemma 3 (i), flat form. The names of the net are below `n`; the result uses names
below the returned counter. -/
theorem dup_tree
    -- the tree: no `dup` cell
    (τ : Term sig ℕ)
    (hτ : DupFree τ)
    -- the first fresh name
    (n : ℕ)
    -- the trees on the auxiliary ports of the `dup`
    (u v : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the names of the net, the `dup` on the root of `τ` and `Δ`, are below `n`
    (hb : Net.Below n (s(mkDup u v, τ) ::ₘ Δ)) :
    -- the net reduces, by interactions only, to the flat net `dupNet n u v τ` and `Δ`,
    Red (s(mkDup u v, τ) ::ₘ Δ) ((dupNet n u v τ).1 + Δ) ∧
      -- the returned counter is at least `n`,
      n ≤ (dupNet n u v τ).2 ∧
      -- and the names of the result are below it
      Net.Below (dupNet n u v τ).2 ((dupNet n u v τ).1 + Δ) := by
  induction τ using Comb.induction generalizing n u v Δ with
  | var x =>
    refine ⟨?_, le_rfl, ?_⟩
    · simpa [dupNet_var] using Relation.ReflTransGen.refl
    · simpa [dupNet_var] using hb
  | era =>
    refine ⟨?_, le_rfl, ?_⟩
    · refine (Steps.single (step_era_dup u v Δ)).cast ?_ ?_
      · rw [Sym2.eq_swap]
      · simp [dupNet_mkEra]
    · simp only [Net.below_cons, below_mkDup, below_mkEra] at hb
      simp [dupNet_mkEra, hb]
  | dup a b => exact absurd hτ dupFree_mkDup
  | con a b iha ihb =>
    obtain ⟨ha, hb'⟩ := dupFree_mkCon.1 hτ
    simp only [Net.below_cons, below_mkDup, below_mkCon] at hb
    obtain ⟨⟨hu, hv⟩, ⟨hba, hbb⟩, hΔ⟩ := hb
    have hBelow0 : Net.Below n (s(mkCon a b, mkDup u v) ::ₘ Δ) := by
      simp [hu, hv, hba, hbb, hΔ]
    have hstep := step_con_dup a b u v Δ n (n + 1) (n + 2) (n + 3) (by simp)
      (fun w hw => hBelow0.notMem (by simp at hw; omega))
    have h4 : n ≤ n + 4 := by omega
    -- duplicate `a`
    obtain ⟨sA, leA, bA⟩ := iha ha (n + 4) (var n) (var (n + 1))
      (s(b, mkDup (var (n + 2)) (var (n + 3))) ::ₘ s(u, mkCon (var n) (var (n + 2))) ::ₘ
        s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ Δ)
      (by simp [hba.mono h4, hbb.mono h4, hu.mono h4, hv.mono h4, hΔ.mono h4])
    -- duplicate `b`
    have e₁ : (dupNet (n + 4) (var n) (var (n + 1)) a).1 +
        (s(b, mkDup (var (n + 2)) (var (n + 3))) ::ₘ s(u, mkCon (var n) (var (n + 2))) ::ₘ
          s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ Δ) =
        s(mkDup (var (n + 2)) (var (n + 3)), b) ::ₘ
          ((dupNet (n + 4) (var n) (var (n + 1)) a).1 +
            (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
              Δ)) := by
      rw [Sym2.eq_swap (a := b)]
      ms
    obtain ⟨sB, leB, bB⟩ := ihb hb' (dupNet (n + 4) (var n) (var (n + 1)) a).2
      (var (n + 2)) (var (n + 3)) _ (bA.cast e₁)
    have e₂ : (dupNet (dupNet (n + 4) (var n) (var (n + 1)) a).2 (var (n + 2)) (var (n + 3)) b).1 +
        ((dupNet (n + 4) (var n) (var (n + 1)) a).1 +
          (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ Δ))
        = (dupNet n u v (mkCon a b)).1 + Δ := by
      rw [dupNet_mkCon]
      ms
    refine ⟨?_, ?_, ?_⟩
    · have hstep' : Step system (s(mkDup u v, mkCon a b) ::ₘ Δ)
          (s(a, mkDup (var n) (var (n + 1))) ::ₘ s(b, mkDup (var (n + 2)) (var (n + 3))) ::ₘ
            s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            Δ) := by
        rw [Sym2.eq_swap]; exact hstep
      refine Relation.ReflTransGen.head hstep' ?_
      exact (sA.cast (by rw [Sym2.eq_swap (a := a)]) e₁).trans (sB.cast rfl e₂)
    · rw [dupNet_mkCon]; omega
    · rw [← e₂]; rw [dupNet_mkCon]; exact bB

-- ============================================================================================
-- 4. The flat net is the net of Lafont's picture
-- ============================================================================================

/-- The flat net left by the duplication steps is the net of Lafont's picture, up to wire
substitution. The net must be linear, and the names from `k` on unused. -/
theorem flat_equiv_nested
    -- the tree: no `dup` cell
    (τ : Term sig ℕ)
    (hτ : DupFree τ)
    -- the first name of the flat net, and the first name of the copies
    (n k : ℕ)
    -- the trees on the auxiliary ports of the `dup`
    (u v : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the flat net with `Δ` is linear, and its names are below `k`
    (hlin : Net.Linear ((dupNet n u v τ).1 + Δ))
    (hbel : Net.Below k ((dupNet n u v τ).1 + Δ)) :
    -- the flat net with `Δ` is the same graph as the two copies of `τ` on `u` and `v`, the `dup`
    -- cells on the leaves, and `Δ`,
    Equiv ((dupNet n u v τ).1 + Δ)
        (s(u, (nested k τ).l) ::ₘ s(v, (nested k τ).r) ::ₘ ((nested k τ).E + Δ)) ∧
      -- the returned counter is at least `k`,
      k ≤ (nested k τ).k ∧
      -- and the names of the drawn net are below it
      Net.Below (nested k τ).k
        (s(u, (nested k τ).l) ::ₘ s(v, (nested k τ).r) ::ₘ ((nested k τ).E + Δ)) := by
  induction τ using Comb.induction generalizing n k u v Δ with
  | dup a b => exact absurd hτ dupFree_mkDup
  | era =>
    have e : (dupNet n u v mkEra).1 + Δ =
        s(u, (nested k mkEra).l) ::ₘ s(v, (nested k mkEra).r) ::ₘ ((nested k mkEra).E + Δ) := by
      rw [dupNet_mkEra, nested_mkEra]
      rw [Sym2.eq_swap (a := mkEra) (b := u), Sym2.eq_swap (a := mkEra) (b := v)]
      ms
    exact ⟨Equiv.of_eq e, le_rfl, hbel.cast e⟩
  | var x =>
    rw [dupNet_var] at hlin hbel
    rw [dupNet_var, nested_var]
    have hbel' := hbel
    simp only [Net.below_add, Net.below_singleton, below_mkDup, Term.below_var] at hbel'
    obtain ⟨⟨⟨hu, hv⟩, hx⟩, hΔ⟩ := hbel'
    have LA : Net.Linear (s(var k, u) ::ₘ s(var x, mkDup (var k) (var (k + 1))) ::ₘ
        (s(var (k + 1), v) ::ₘ Δ)) :=
      hlin.add_fresh ({k, k + 1} : Multiset ℕ) (by simp)
        (fun w hw => hbel.notMem (by simp at hw; omega))
        (by
          simp only [Net.vars_cons, Net.vars_add, Net.vars_singleton, eqVars_mk, vars_mkDup,
            vars_var, Multiset.insert_eq_cons]
          simp only [← Multiset.singleton_add]
          abel)
    have W1 : Wire (s(var k, u) ::ₘ s(var x, mkDup (var k) (var (k + 1))) ::ₘ
        (s(var (k + 1), v) ::ₘ Δ))
        (s(var x, mkDup u (var (k + 1))) ::ₘ (s(var (k + 1), v) ::ₘ Δ)) := wire_dup_left LA
    have W2 : Wire (s(var (k + 1), v) ::ₘ s(var x, mkDup u (var (k + 1))) ::ₘ Δ)
        (s(var x, mkDup u v) ::ₘ Δ) :=
      wire_dup_right (W1.linear_right.cast (Multiset.cons_swap _ _ _))
    have e0 : ({s(mkDup u v, var x)} : CNet) + Δ = s(var x, mkDup u v) ::ₘ Δ := by
      rw [Sym2.eq_swap]; simp
    have e1 : (s(var k, u) ::ₘ s(var x, mkDup (var k) (var (k + 1))) ::ₘ
        (s(var (k + 1), v) ::ₘ Δ) : CNet) =
        s(u, var k) ::ₘ s(v, var (k + 1)) ::ₘ
          (({s(var x, mkDup (var k) (var (k + 1)))} : CNet) + Δ) := by
      rw [Sym2.eq_swap (a := var k) (b := u), Sym2.eq_swap (a := var (k + 1)) (b := v)]
      ms
    refine ⟨(Equiv.of_eq e0).trans ((((W1.equiv.trans
      (Equiv.of_eq (Multiset.cons_swap _ _ _))).trans W2.equiv).symm).trans (Equiv.of_eq e1)),
      (by change k ≤ k + 2; omega), ?_⟩
    have h2 : k ≤ k + 2 := by omega
    simp only [Net.below_cons, Net.below_add, Net.below_singleton, below_mkDup, Term.below_var]
    exact ⟨hu.mono h2, by omega, hv.mono h2, by omega, ⟨by omega, by omega, by omega⟩,
      hΔ.mono h2⟩
  | con a b iha ihb =>
    obtain ⟨hda, hdb⟩ := dupFree_mkCon.1 hτ
    rw [dupNet_mkCon] at hlin hbel
    rw [dupNet_mkCon, nested_mkCon]
    set ra := dupNet (n + 4) (var n) (var (n + 1)) a with hra
    set rb := dupNet ra.2 (var (n + 2)) (var (n + 3)) b with hrb
    set Rb := nested k b with hRb
    set Ra := nested Rb.k a with hRa
    -- the call on `b`
    have e0 : (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          (ra.1 + rb.1) : CNet) + Δ =
        rb.1 + (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          (ra.1 + Δ)) := by ms
    obtain ⟨EB, leB, BB⟩ := ihb hdb ra.2 k (var (n + 2)) (var (n + 3))
      (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
        (ra.1 + Δ))
      (hlin.cast e0) (hbel.cast e0)
    have EB' : Equiv
        (rb.1 + (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          (ra.1 + Δ)))
        (s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ
          (Rb.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ (ra.1 + Δ)))) := EB
    have BB' : Net.Below Rb.k
        (s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ
          (Rb.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ (ra.1 + Δ)))) := BB
    have L1 : Net.Linear
        (s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ
          (Rb.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ (ra.1 + Δ)))) :=
      EB'.linear (hlin.cast e0)
    -- the call on `a`
    have e1 : ((s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ
          (Rb.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ (ra.1 + Δ)))) : CNet) =
        ra.1 + (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ)) := by ms
    obtain ⟨EA, leA, BA⟩ := iha hda (n + 4) Rb.k (var n) (var (n + 1))
      (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
        s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ))
      (L1.cast e1) (BB'.cast e1)
    have EA' : Equiv
        (ra.1 + (s(u, mkCon (var n) (var (n + 2))) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ)))
        (s(var n, Ra.l) ::ₘ s(var (n + 1), Ra.r) ::ₘ
          (Ra.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ)))) := EA
    have BA' : Net.Below Ra.k
        (s(var n, Ra.l) ::ₘ s(var (n + 1), Ra.r) ::ₘ
          (Ra.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ)))) := BA
    have L2 : Net.Linear
        (s(var n, Ra.l) ::ₘ s(var (n + 1), Ra.r) ::ₘ
          (Ra.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ)))) :=
      EA'.linear (L1.cast e1)
    -- plug the four wires created at the top
    have e2 : ((s(var n, Ra.l) ::ₘ s(var (n + 1), Ra.r) ::ₘ
          (Ra.E + (s(u, mkCon (var n) (var (n + 2))) ::ₘ
            s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Rb.E + Δ)))) : CNet) =
        (s(var n, Ra.l) ::ₘ s(u, mkCon (var n) (var (n + 2))) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) := by ms
    have W1 : Wire
        (s(var n, Ra.l) ::ₘ s(u, mkCon (var n) (var (n + 2))) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ)))
        (s(u, mkCon Ra.l (var (n + 2))) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) :=
      wire_con_left (L2.cast e2)
    have e3 : ((s(u, mkCon Ra.l (var (n + 2))) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 2), Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) : CNet) =
        (s(var (n + 2), Rb.l) ::ₘ s(u, mkCon Ra.l (var (n + 2))) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) := by ms
    have W2 : Wire
        (s(var (n + 2), Rb.l) ::ₘ s(u, mkCon Ra.l (var (n + 2))) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ)))
        (s(u, mkCon Ra.l Rb.l) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) :=
      wire_con_right (W1.linear_right.cast e3)
    have e4 : ((s(u, mkCon Ra.l Rb.l) ::ₘ
          (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
            s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) : CNet) =
        (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          (s(u, mkCon Ra.l Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) := by ms
    have W3 : Wire
        (s(var (n + 1), Ra.r) ::ₘ s(v, mkCon (var (n + 1)) (var (n + 3))) ::ₘ
          (s(u, mkCon Ra.l Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ)))
        (s(v, mkCon Ra.r (var (n + 3))) ::ₘ
          (s(u, mkCon Ra.l Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) :=
      wire_con_left (W2.linear_right.cast e4)
    have e5 : ((s(v, mkCon Ra.r (var (n + 3))) ::ₘ
          (s(u, mkCon Ra.l Rb.l) ::ₘ s(var (n + 3), Rb.r) ::ₘ (Ra.E + Rb.E + Δ))) : CNet) =
        (s(var (n + 3), Rb.r) ::ₘ s(v, mkCon Ra.r (var (n + 3))) ::ₘ
          (s(u, mkCon Ra.l Rb.l) ::ₘ (Ra.E + Rb.E + Δ))) := by ms
    have W4 : Wire
        (s(var (n + 3), Rb.r) ::ₘ s(v, mkCon Ra.r (var (n + 3))) ::ₘ
          (s(u, mkCon Ra.l Rb.l) ::ₘ (Ra.E + Rb.E + Δ)))
        (s(v, mkCon Ra.r Rb.r) ::ₘ (s(u, mkCon Ra.l Rb.l) ::ₘ (Ra.E + Rb.E + Δ))) :=
      wire_con_right (W3.linear_right.cast e5)
    have e6 : ((s(v, mkCon Ra.r Rb.r) ::ₘ (s(u, mkCon Ra.l Rb.l) ::ₘ (Ra.E + Rb.E + Δ))) : CNet) =
        (s(u, mkCon Ra.l Rb.l) ::ₘ s(v, mkCon Ra.r Rb.r) ::ₘ (Ra.E + Rb.E + Δ)) := by ms
    refine ⟨?_, leB.trans leA, ?_⟩
    · exact (Equiv.of_eq e0).trans <| EB'.trans <| (Equiv.of_eq e1).trans <| EA'.trans <|
        (Equiv.of_eq e2).trans <| W1.equiv.trans <| (Equiv.of_eq e3).trans <| W2.equiv.trans <|
        (Equiv.of_eq e4).trans <| W3.equiv.trans <| (Equiv.of_eq e5).trans <| W4.equiv.trans <|
        Equiv.of_eq e6
    · exact (W4.below ((W3.below ((W2.below ((W1.below (BA'.cast e2)).cast e3)).cast e4)).cast
        e5)).cast e6

-- ============================================================================================
-- 5. Main result: Lemma 3 (i) as drawn
-- ============================================================================================

/-- Lafont's Lemma 3 (i) as drawn: in a linear net, a `dup` plugged into the root of a tree without
`dup` reduces, by interactions only, to a net that is the same graph as two copies of the tree with
one `dup` on each leaf. -/
theorem dup_tree_nested
    -- the tree: no `dup` cell
    (τ : Term sig ℕ)
    (hτ : DupFree τ)
    -- the first fresh name
    (n : ℕ)
    -- the trees on the auxiliary ports of the `dup`
    (u v : Term sig ℕ)
    -- the rest of the net
    (Δ : CNet)
    -- the net, the `dup` on the root of `τ` and `Δ`, has its names below `n` and is linear
    (hb : Net.Below n (s(mkDup u v, τ) ::ₘ Δ))
    (hlin : Net.Linear (s(mkDup u v, τ) ::ₘ Δ)) :
    -- there is a net `N` such that
    ∃ N,
      -- the net reduces, by interactions only, to `N`,
      Red (s(mkDup u v, τ) ::ₘ Δ) N ∧
      -- and `N` is the same graph as: the two copies of `τ` on `u` and `v`, one `dup` on each
      -- leaf, and `Δ`
      Equiv N
        (s(u, (nested (dupNet n u v τ).2 τ).l) ::ₘ s(v, (nested (dupNet n u v τ).2 τ).r) ::ₘ
          ((nested (dupNet n u v τ).2 τ).E + Δ)) := by
  obtain ⟨hred, -, hbel⟩ := dup_tree τ hτ n u v Δ hb
  exact ⟨_, hred, (flat_equiv_nested τ hτ n _ u v Δ
    (Steps.linear system_wellFormed.linear hred hlin) hbel).1⟩

end INet.Comb
