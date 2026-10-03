/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLogicalWrappers

/-! NF weak partition development: NominalLogicalWrappersComplete. -/


public section

namespace NFChoice.DirectNominalPrf

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore

namespace Nominal

/-! Coincident-variable branches erased by the MM0 Lean exporter. -/


@[expose]
def impRefl {L : Fol.Language} (Γ : Set (Fol.formula L)) (p : Fol.formula L) :
    Γ ⊢ p ⟹ p := by
  apply Fol.prf.impI
  exact Fol.prf.axm (Set.mem_insert _ _)

/-- The `x = y` branch of quantifier commutation is implication reflexivity. -/
@[expose]
def ax7Same (x : Var) (p : Wff) : NPrf (.imp (.all x (.all x p)) (.all x (.all x p))) :=
  fun rho => impRefl LiteralHailperinNF.fst (lowerWff rho (.all x (.all x p)))

/-- Total `ax-7`: the emitter supplies only the noncoincident de-Bruijn swap
identity; the coincident branch is discharged here.
-/
@[expose]
def ax7 (x y : Var) (p : Wff)
    (hSwap : ∀ rho, y ≠ x → lowerWff (bindRho (bindRho rho y) x) p =
            GenericLogicalHandlers.swap01 (lowerWff (bindRho (bindRho rho x) y) p)) :
    NPrf (.imp (.all x (.all y p)) (.all y (.all x p))) :=
  by
  by_cases hxy : y = x
  · subst y
    exact ax7Same x p
  · exact ax7OfSwap x y p (fun rho => hSwap rho hxy)

/-- Equality existence when the source names in `ax-9` coincide. -/
@[expose]
def ax9SelfCore (Γ : Set (Fol.formula LNF)) : Γ ⊢ ∼(∀'(∼((&0) ≃ (&0)))) :=
  by
  apply Fol.prf.impI
  have hAll : Fol.prf (insert (∀'(∼((&0) ≃ (&0)))) Γ) (∀'(∼((&0) ≃ (&0)))) :=
    Fol.prf.axm (Set.mem_insert _ _)
  have hInst := Fol.prf.allE₂ (∼((&0) ≃ (&0))) (&0) hAll
  have hNotRef : Fol.prf (insert (∀'(∼((&0) ≃ (&0)))) Γ) (∼((&0) ≃ (&0))) := by
    simpa [Fol.not', Fol.subst_formula, Fol.subst_formula_equal,
      Fol.subst_term_var0] using hInst
  exact
    Fol.prf.impE ((&0) ≃ (&0)) hNotRef (Fol.prf.ref (insert (∀'(∼((&0) ≃ (&0)))) Γ) (&0))

/-- Total Metamath `ax-9`, including `x = y`. -/
@[expose]
def ax9 (x y : Var) : NPrf (Wff.neg (.all x (Wff.neg (.objEq x y)))) :=
  by
  by_cases hxy : y = x
  · subst y
    intro rho
    simpa [Wff.neg, lowerWff, neg, Fol.not', bindRho] using
      (ax9SelfCore LiteralHailperinNF.fst)
  · exact ax9OfNe x y hxy

/-- Ex falso branch of `ax-12` when `x = y`. -/
@[expose]
noncomputable def ax12SameXYCore (Γ : Set (Fol.formula LNF)) (s : Fol.term LNF)
    (q : Fol.formula LNF) : Γ ⊢ (∼(s ≃ s)) ⟹ q :=
  by
  apply Fol.prf.impI
  apply Fol.exfalso
  exact
    Fol.prf.impE (s ≃ s) (Fol.prf.axm (Set.mem_insert _ _))
      (Fol.prf.ref (insert (∼(s ≃ s)) Γ) s)

/-- Ex falso branch of `ax-12` when `x = z` but `x ≠ y`. -/
@[expose]
noncomputable def ax12SameXZCore (Γ : Set (Fol.formula LNF)) (s t : Fol.term LNF)
    (q : Fol.formula LNF) : Γ ⊢ (∼(s ≃ t)) ⟹ (t ≃ s) ⟹ q :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.exfalso
  apply Fol.prf.impE (s ≃ t)
  · exact Fol.prf.axm (Set.mem_insert_of_mem (t ≃ s) (Set.mem_insert _ _))
  · apply Fol.prf_symm
    exact Fol.prf.axm (Set.mem_insert _ _)

/-- Total Metamath `ax-12`, including every bundled-variable coincidence. -/
@[expose]
noncomputable def ax12 (x y z : Var) :
    NPrf (.imp (Wff.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z)))) :=
  by
  by_cases hxy : x = y
  · subst y
    intro rho
    simpa [Wff.neg, lowerWff, neg, Fol.not'] using
      (ax12SameXYCore LiteralHailperinNF.fst (&(rho x))
        (lowerWff rho (.imp (.objEq x z) (.all x (.objEq x z)))))
  · by_cases hxz : x = z
    · subst z
      intro rho
      simpa [Wff.neg, lowerWff, neg, Fol.not'] using
        (ax12SameXZCore LiteralHailperinNF.fst (&(rho x)) (&(rho y))
          (lowerWff rho (.all x (.objEq y x))))
    · apply ax12OfShift x y z
      intro rho
      simp [lowerWff, bindRho, Ne.symm hxy, Ne.symm hxz, Fol.lift_formula1,
        Fol.lift_formula_at, Fol.lift_term_at]

/-- `ax-11` when its two bundled source names coincide. -/
@[expose]
def ax11SameCore (Γ : Set (Fol.formula LNF)) (s : Fol.term LNF) (body : Fol.formula LNF) :
    Γ ⊢ (s ≃ s) ⟹ (∀'body) ⟹ ∀'(((&0) ≃ (&0)) ⟹ body) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.allI
  apply Fol.prf.impI
  let liftedContext : Set (Fol.formula LNF) :=
    Fol.lift_formula1 '' insert (∀'body) (insert (s ≃ s) Γ)
  have hAll : Fol.prf (insert ((&0) ≃ (&0)) liftedContext) (Fol.lift_formula1 (∀'body)) :=
    Fol.prf.axm
      (Set.mem_insert_of_mem ((&0) ≃ (&0))
        (Set.mem_image_of_mem Fol.lift_formula1 (Set.mem_insert _ _)))
  have hInst := Fol.prf.allE₂ (Fol.lift_formula_at body 1 1) (&0) hAll
  simpa only [Fol.lift_subst_formula_cancel] using hInst

/-- Nominal `ax-11` coincident branch. -/
@[expose]
def ax11Same (x : Var) (p : Wff) :
    NPrf (.imp (.objEq x x) (.imp (.all x p) (.all x (.imp (.objEq x x) p)))) :=
  fun rho => by
  simpa [lowerWff, bindRho] using
    (ax11SameCore LiteralHailperinNF.fst (&(rho x)) (lowerWff (bindRho rho x) p))

/-- Total `ax-11`: the emitter's template equalities are needed only when its
two bundled source names differ.
-/
@[expose]
noncomputable def ax11 (x y : Var) (p : Wff) (template : (Var → Nat) → Fol.formula LNF)
    (hSource : ∀ rho, y ≠ x →
          GenericLogicalHandlers.ax11Inst (lowerWff (bindRho rho y) p) (&(rho y)) =
            (template rho) [Fol.lift_term1 (&(rho x)) // 0]f)
    (hTarget : ∀ rho, y ≠ x → (template rho) [(&0) // 0]f = lowerWff (bindRho rho x) p) :
    NPrf (.imp (.objEq x y) (.imp (.all y p) (.all x (.imp (.objEq x y) p)))) :=
  by
  by_cases hxy : y = x
  · subst y
    exact ax11Same x p
  · exact
      ax11OfTemplate x y p hxy template (fun rho => hSource rho hxy)
        (fun rho => hTarget rho hxy)


end Nominal
end NFChoice.DirectNominalPrf
