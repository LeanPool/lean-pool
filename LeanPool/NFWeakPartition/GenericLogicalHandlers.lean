/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ExactLiteralTrial.NFChoiceExactLiteral

/-! NF weak partition development: GenericLogicalHandlers. -/


public section

namespace NFChoice.DirectNominalPrf.GenericLogicalHandlers

open scoped Fol
open NFChoice.Foundation

/-! Proof-producing counterparts of the propositional Metamath kernel leaves.
They are independent of the nominal syntax representation: the nominal
compiler only has to lower its instantiated formulas and call these terms.
-/


@[expose]
def ax1 {L : Fol.Language} (Γ : Set (Fol.formula L)) (p q : Fol.formula L) :
    Γ ⊢ p ⟹ q ⟹ p := by
  apply Fol.prf.impI
  apply Fol.prf.impI
  exact Fol.prf.axm (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

@[expose]
def ax2 {L : Fol.Language} (Γ : Set (Fol.formula L)) (p q r : Fol.formula L) :
    Γ ⊢ (p ⟹ q ⟹ r) ⟹ (p ⟹ q) ⟹ p ⟹ r :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.impE q
  · apply Fol.prf.impE p
    · exact Fol.prf.axm (by simp)
    · exact Fol.prf.axm (by simp)
  · apply Fol.prf.impE p
    · exact Fol.prf.axm (by simp)
    · exact Fol.prf.axm (by simp)

@[expose]
def ax3 {L : Fol.Language} (Γ : Set (Fol.formula L)) (p q : Fol.formula L) :
    Γ ⊢ ((∼p) ⟹ (∼q)) ⟹ q ⟹ p := by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.falsumE
  apply Fol.prf.impE q
  · apply Fol.prf.impE (∼p)
    · exact
        Fol.prf.axm
          (Set.mem_insert_of_mem (∼p) (Set.mem_insert_of_mem q (Set.mem_insert _ _)))
    · exact Fol.prf.axm (Set.mem_insert _ _)
  · exact Fol.prf.axm (Set.mem_insert_of_mem (∼p) (Set.mem_insert _ _))

@[expose]
def mp {L : Fol.Language} {Γ : Set (Fol.formula L)} {p q : Fol.formula L} (hp : Γ ⊢ p)
    (hpq : Γ ⊢ p ⟹ q) : Γ ⊢ q :=
  Fol.prf.impE p hpq hp

@[expose]
def ax5 {L : Fol.Language} (Γ : Set (Fol.formula L)) (p q : Fol.formula L) :
    Γ ⊢ (∀'(p ⟹ q)) ⟹ (∀'p) ⟹ ∀'q :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.allI
  apply Fol.prf.impE p
  · have hAll :
      Fol.prf (Fol.lift_formula1 '' insert (∀'p) (insert (∀'(p ⟹ q)) Γ))
        (Fol.lift_formula1 (∀'(p ⟹ q))) :=
      Fol.prf.axm
        (Set.mem_image_of_mem Fol.lift_formula1
          (Set.mem_insert_of_mem (∀'p) (Set.mem_insert _ _)))
    have hInst := Fol.prf.allE₂ (Fol.lift_formula_at (p ⟹ q) 1 1) (&0) hAll
    simpa only [Fol.lift_subst_formula_cancel] using hInst
  · have hAll :
      Fol.prf (Fol.lift_formula1 '' insert (∀'p) (insert (∀'(p ⟹ q)) Γ))
        (Fol.lift_formula1 (∀'p)) :=
      Fol.prf.axm (Set.mem_image_of_mem Fol.lift_formula1 (Set.mem_insert _ _))
    have hInst := Fol.prf.allE₂ (Fol.lift_formula_at p 1 1) (&0) hAll
    simpa only [Fol.lift_subst_formula_cancel] using hInst

@[expose]
def freshIntro {L : Fol.Language} (Γ : Set (Fol.formula L)) (p : Fol.formula L) :
    Γ ⊢ p ⟹ ∀'(Fol.lift_formula1 p) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.allI
  rw [Set.image_insert_eq]
  exact Fol.prf.axm (Set.mem_insert _ _)

@[expose]
def ax6Core {L : Fol.Language} (Γ : Set (Fol.formula L)) (p : Fol.formula L) :
    Γ ⊢ (∼p) ⟹ ∀'(∼(Fol.lift_formula1 p)) := by
  simpa only [Fol.lift_formula1, Fol.lift_formula_at, Fol.not'] using (freshIntro Γ (∼p))

@[expose]
def equalitySubst {L : Fol.Language} (Γ : Set (Fol.formula L)) (s t : Fol.term L)
    (p : Fol.formula L) : Γ ⊢ (s ≃ t) ⟹ (p [s // 0]f) ⟹ (p [t // 0]f) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.subst₂ s t p
  · exact Fol.prf.axm (Set.mem_insert_of_mem (p [s // 0]f) (Set.mem_insert _ _))
  · exact Fol.prf.axm (Set.mem_insert _ _)

@[expose]
noncomputable def ax8 {L : Fol.Language} (Γ : Set (Fol.formula L)) (s t u : Fol.term L) :
    Γ ⊢ (s ≃ t) ⟹ (s ≃ u) ⟹ (t ≃ u) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf_trans
  · apply Fol.prf_symm
    exact Fol.prf.axm (Set.mem_insert_of_mem (s ≃ u) (Set.mem_insert _ _))
  · exact Fol.prf.axm (Set.mem_insert _ _)

@[expose]
def ax9 {L : Fol.Language} (Γ : Set (Fol.formula L)) (t : Fol.term L) :
    Γ ⊢ ∼(∀'(∼((&0) ≃ Fol.lift_term1 t))) :=
  by
  apply Fol.prf.impI
  have hAll :
    Fol.prf (insert (∀'(∼((&0) ≃ Fol.lift_term1 t))) Γ)
      (∀'(∼((&0) ≃ Fol.lift_term1 t))) :=
    Fol.prf.axm (Set.mem_insert _ _)
  have hInst := Fol.prf.allE₂ (∼((&0) ≃ Fol.lift_term1 t)) t hAll
  have hEq : (∼((&0) ≃ Fol.lift_term1 t)) [t // 0]f = ∼(t ≃ t) := by
    simp [Fol.not', Fol.subst_formula, Fol.lift_term1_subst_term]
  have hNotRef : Fol.prf (insert (∀'(∼((&0) ≃ Fol.lift_term1 t))) Γ) (∼(t ≃ t)) :=
    by
    rw [hEq] at hInst
    exact hInst
  exact
    Fol.prf.impE (t ≃ t) hNotRef
      (Fol.prf.ref (insert (∀'(∼((&0) ≃ Fol.lift_term1 t))) Γ) t)

@[expose]
def nfMem (s t : Fol.term LNF) : Fol.formula LNF :=
  Fol.preformula.apprel (Fol.preformula.apprel (Fol.preformula.rel LNFRelation.mem) s) t

@[expose]
def ax13 (Γ : Set (Fol.formula LNF)) (s t u : Fol.term LNF) :
    Γ ⊢ (s ≃ t) ⟹ nfMem s u ⟹ nfMem t u := by
  simpa [nfMem, Fol.subst_formula, Fol.subst_term_var0, Fol.lift_term1_subst_term] using
    (equalitySubst Γ s t (nfMem (&0) (Fol.lift_term1 u)))

@[expose]
def ax14 (Γ : Set (Fol.formula LNF)) (s t u : Fol.term LNF) :
    Γ ⊢ (s ≃ t) ⟹ nfMem u s ⟹ nfMem u t := by
  simpa [nfMem, Fol.subst_formula, Fol.subst_term_var0, Fol.lift_term1_subst_term] using
    (equalitySubst Γ s t (nfMem (Fol.lift_term1 u) (&0)))

@[expose]
def ax12Core {L : Fol.Language} (Γ : Set (Fol.formula L)) (a p : Fol.formula L) :
    Γ ⊢ a ⟹ p ⟹ ∀'(Fol.lift_formula1 p) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.allI
  rw [Set.image_insert_eq, Set.image_insert_eq]
  exact Fol.prf.axm (Set.mem_insert _ _)

@[expose]
def swap01 {L : Fol.Language} (p : Fol.formula L) : Fol.formula L :=
  (((Fol.lift_formula_at (Fol.lift_formula_at p 1 2) 1 2) [(&0) // 1]f) [(&1) // 0]f)

@[expose]
def ax7Core {L : Fol.Language} (Γ : Set (Fol.formula L)) (p : Fol.formula L) :
    Γ ⊢ (∀'(∀'p)) ⟹ ∀'(∀'(swap01 p)) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.allI
  apply Fol.prf.allI
  have hAll :
    Fol.prf (Fol.lift_formula1 '' (Fol.lift_formula1 '' insert (∀'(∀'p)) Γ))
      (Fol.lift_formula1 (Fol.lift_formula1 (∀'(∀'p)))) :=
    Fol.prf.axm
      (Set.mem_image_of_mem Fol.lift_formula1
        (Set.mem_image_of_mem Fol.lift_formula1 (Set.mem_insert _ _)))
  have hOuter := Fol.prf.allE₂ _ (&0) hAll
  have hInner := Fol.prf.allE₂ _ (&1) hOuter
  change
    Fol.prf (Fol.lift_formula1 '' (Fol.lift_formula1 '' insert (∀'(∀'p)) Γ)) (swap01 p)
  simpa [swap01, Fol.lift_formula1, Fol.lift_formula_at, Fol.subst_formula,
    Fol.lift_term_at, Fol.subst_term] using hInner

@[expose]
def ax11Inst {L : Fol.Language} (body : Fol.formula L) (t : Fol.term L) : Fol.formula L :=
  (Fol.lift_formula_at body 1 1) [Fol.lift_term1 t // 0]f

@[expose]
noncomputable def ax11Core {L : Fol.Language} (Γ : Set (Fol.formula L)) (s t : Fol.term L)
    (allBody targetBody template : Fol.formula L)
    (hSource : ax11Inst allBody t = template [Fol.lift_term1 s // 0]f)
    (hTarget : template [(&0) // 0]f = targetBody) :
    Γ ⊢ (s ≃ t) ⟹ (∀'allBody) ⟹ ∀'(((&0) ≃ Fol.lift_term1 t) ⟹ targetBody) :=
  by
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.allI
  apply Fol.prf.impI
  let innerEq : Fol.formula L := (&0) ≃ Fol.lift_term1 t
  let liftedContext : Set (Fol.formula L) :=
    Fol.lift_formula1 '' insert (∀'allBody) (insert (s ≃ t) Γ)
  have hInner : Fol.prf (insert innerEq liftedContext) innerEq :=
    Fol.prf.axm (Set.mem_insert _ _)
  have hOuterEqLifted :
    Fol.prf (insert innerEq liftedContext) (Fol.lift_formula1 (s ≃ t)) :=
    Fol.prf.axm
      (Set.mem_insert_of_mem innerEq (Set.mem_image_of_mem Fol.lift_formula1
          (Set.mem_insert_of_mem (∀'allBody) (Set.mem_insert _ _))))
  have hOuterEq :
    Fol.prf (insert innerEq liftedContext) (Fol.lift_term1 s ≃ Fol.lift_term1 t) := by
    simpa [Fol.lift_formula1, Fol.lift_formula_at, Fol.not'] using hOuterEqLifted
  have hSeqCurrent : Fol.prf (insert innerEq liftedContext) (Fol.lift_term1 s ≃ (&0)) :=
    Fol.prf_trans hOuterEq (Fol.prf_symm hInner)
  have hAllLifted :
    Fol.prf (insert innerEq liftedContext) (Fol.lift_formula1 (∀'allBody)) :=
    Fol.prf.axm
      (Set.mem_insert_of_mem innerEq
        (Set.mem_image_of_mem Fol.lift_formula1 (Set.mem_insert _ _)))
  have hInstRaw :=
    Fol.prf.allE₂ (Fol.lift_formula_at allBody 1 1) (Fol.lift_term1 t) hAllLifted
  have hInst :
    Fol.prf (insert innerEq liftedContext) (template [Fol.lift_term1 s // 0]f) :=
    by
    change Fol.prf (insert innerEq liftedContext) (ax11Inst allBody t) at hInstRaw
    rw [hSource] at hInstRaw
    exact hInstRaw
  have hTransport := Fol.prf.subst₂ (Fol.lift_term1 s) (&0) template hSeqCurrent hInst
  rw [hTarget] at hTransport
  exact hTransport

@[expose]
def axMeredith {L : Fol.Language} (Γ : Set (Fol.formula L)) (p q r s t : Fol.formula L) :
    Γ ⊢ (((((p ⟹ q) ⟹ ((∼r) ⟹ (∼s))) ⟹ r) ⟹ t) ⟹ ((t ⟹ p) ⟹ (s ⟹ p))) :=
  by
  let C : Fol.formula L := (p ⟹ q) ⟹ ((∼r) ⟹ (∼s))
  let B : Fol.formula L := C ⟹ r
  let H : Fol.formula L := B ⟹ t
  change Γ ⊢ H ⟹ (t ⟹ p) ⟹ s ⟹ p
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.impI
  apply Fol.prf.falsumE
  apply Fol.prf.impE p
  · exact Fol.prf.axm (Set.mem_insert _ _)
  · apply Fol.prf.impE t
    · exact
        Fol.prf.axm
          (Set.mem_insert_of_mem (∼p) (Set.mem_insert_of_mem s (Set.mem_insert _ _)))
    · apply Fol.prf.impE B
      · exact
          Fol.prf.axm
            (Set.mem_insert_of_mem (∼p) (Set.mem_insert_of_mem s
                (Set.mem_insert_of_mem (t ⟹ p) (Set.mem_insert _ _))))
      · apply Fol.prf.impI
        apply Fol.prf.falsumE
        apply Fol.prf.impE s
        · apply Fol.prf.impE (∼r)
          · apply Fol.prf.impE (p ⟹ q)
            · exact Fol.prf.axm (Set.mem_insert_of_mem (∼r) (Set.mem_insert _ _))
            · apply Fol.prf.impI
              apply Fol.prf.falsumE
              apply Fol.prf.impE p
              · exact
                  Fol.prf.axm
                    (Set.mem_insert_of_mem (∼q) (Set.mem_insert_of_mem p
                        (Set.mem_insert_of_mem (∼r)
                          (Set.mem_insert_of_mem C (Set.mem_insert _ _)))))
              · exact Fol.prf.axm (Set.mem_insert_of_mem (∼q) (Set.mem_insert _ _))
          · exact Fol.prf.axm (Set.mem_insert _ _)
        · exact
            Fol.prf.axm
              (Set.mem_insert_of_mem (∼r) (Set.mem_insert_of_mem C
                  (Set.mem_insert_of_mem (∼p) (Set.mem_insert _ _))))


end NFChoice.DirectNominalPrf.GenericLogicalHandlers
