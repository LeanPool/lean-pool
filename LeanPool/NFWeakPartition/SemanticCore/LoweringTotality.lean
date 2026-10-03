/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.PartialLowering

/-! Totality of nominal lowering when every free variable is mapped. -/


public section

namespace NFChoice.SemanticCore.PartialLowering

open NFChoice.Foundation

def Mapped {n : Nat} (rho : Var → Option (Fin n)) (support : Finset Var) : Prop :=
  ∀ x ∈ support, ∃ i, rho x = some i

theorem Mapped.mono {n : Nat} {rho : Var → Option (Fin n)} {s t : Finset Var}
    (h : Mapped rho t) (hst : s ⊆ t) : Mapped rho s := fun x hx => h x (hst hx)

theorem Mapped.lift {n : Nat} {rho : Var → Option (Fin n)} {s : Finset Var}
    (h : Mapped rho s) : Mapped (liftRho? rho) s :=
  by
  intro x hx
  obtain ⟨i, hi⟩ := h x hx
  exact ⟨i.succ, by simp only [liftRho?, hi, Option.map_some]⟩

theorem Mapped.update {n : Nat} {rho : Var → Option (Fin n)} {s : Finset Var} (x : Var)
    (candidate : Fin n) (h : Mapped rho (s.erase x)) :
    Mapped (Function.update rho x (some candidate)) s :=
  by
  intro y hy
  by_cases hyx : y = x
  · subst y
    exact ⟨candidate, by simp only [Function.update_self]⟩
  · obtain ⟨i, hi⟩ := h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)
    exact ⟨i, by simpa only [Function.update_of_ne hyx] using hi⟩

mutual
  theorem lowerClassPred?_exists {n : Nat} (rho : Var → Option (Fin n))
      (candidate : Fin n) (A : Class) (h : Mapped rho A.fv) :
      ∃ f, lowerClassPred? rho candidate A = some f := by
    cases A with
    | cv x =>
      obtain ⟨i, hi⟩ := h x (by simp only [Class.fv, Finset.mem_singleton])
      exact
        ⟨.mem candidate i, by simp only [lowerClassPred?, hi, bind, Option.bind, pure]⟩
    | cab x p =>
      exact
        lowerWff?_exists (Function.update rho x (some candidate)) p
          (Mapped.update x candidate (by simpa only [Class.fv] using h))
  theorem lowerWff?_exists {n : Nat} (rho : Var → Option (Fin n)) (p : Wff)
      (h : Mapped rho p.fv) : ∃ f, lowerWff? rho p = some f := by
    cases p with
    | falsum => exact ⟨.falsum, rfl⟩
    | imp p
      q =>
      obtain ⟨p', hp⟩ :=
        lowerWff?_exists rho p
          (h.mono (by simp only [Wff.fv]; exact Finset.subset_union_left))
      obtain ⟨q', hq⟩ :=
        lowerWff?_exists rho q
          (h.mono (by simp only [Wff.fv]; exact Finset.subset_union_right))
      exact ⟨.imp p' q', by simp only [lowerWff?, hp, hq, bind, Option.bind, pure]⟩
    | all x
      p =>
      obtain ⟨p', hp⟩ :=
        lowerWff?_exists (bindRho? rho x) p
          (Mapped.update x 0 (Mapped.lift (by simpa only [Wff.fv] using h)))
      exact ⟨.all p', by simp only [lowerWff?, hp, bind, Option.bind, pure]⟩
    | objEq x y =>
      obtain ⟨i, hi⟩ := h x (by simp [Wff.fv])
      obtain ⟨j, hj⟩ := h y (by simp [Wff.fv])
      exact ⟨.equal i j, by simp only [lowerWff?, hi, hj, bind, Option.bind, pure]⟩
    | objMem x y =>
      obtain ⟨i, hi⟩ := h x (by simp [Wff.fv])
      obtain ⟨j, hj⟩ := h y (by simp [Wff.fv])
      exact ⟨.mem i j, by simp only [lowerWff?, hi, hj, bind, Option.bind, pure]⟩
    | classEq A
      B =>
      obtain ⟨A', hA⟩ :=
        lowerClassPred?_exists (liftRho? rho) 0 A
          (Mapped.lift (h.mono (by simp only [Wff.fv]; exact Finset.subset_union_left)))
      obtain ⟨B', hB⟩ :=
        lowerClassPred?_exists (liftRho? rho) 0 B
          (Mapped.lift (h.mono (by simp only [Wff.fv]; exact Finset.subset_union_right)))
      exact
        ⟨.all (Formula.biimp A' B'), by
          simp only [lowerWff?, hA, hB, bind, Option.bind, pure]⟩
    | classMem A
      B =>
      obtain ⟨A', hA⟩ :=
        lowerClassPred?_exists (liftRho? (liftRho? rho)) 0 A
          (Mapped.lift (Mapped.lift
              (h.mono (by simp only [Wff.fv]; exact Finset.subset_union_left))))
      obtain ⟨B', hB⟩ :=
        lowerClassPred?_exists (liftRho? rho) 0 B
          (Mapped.lift (h.mono (by simp only [Wff.fv]; exact Finset.subset_union_right)))
      exact
        ⟨Formula.ex (Formula.conj (.all (Formula.biimp (.mem 0 1) A')) B'), by
          simp only [lowerWff?, hA, hB, bind, Option.bind, pure]⟩
end

theorem lowerClosed_exists (p : Wff) (hp : p.fv = ∅) : ∃ f, lowerClosed p = some f :=
  lowerWff?_exists emptyRho p
    (by
      intro x hx
      simp only [hp, Finset.notMem_empty] at hx)

theorem option_eq_some_getD {α : Type*} (o : Option α) (fallback : α)
    (h : ∃ a, o = some a) : o = some (o.getD fallback) :=
  by
  obtain ⟨a, rfl⟩ := h
  rfl

end NFChoice.SemanticCore.PartialLowering
