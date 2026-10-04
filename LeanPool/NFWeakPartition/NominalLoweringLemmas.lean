/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLogicalWrappersComplete

/-! NF weak partition development: NominalLoweringLemmas. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore

/-! Structural facts used by the direct Metamath certificate compiler.  They
turn the source `$d x ph` check into the exact de-Bruijn lift equation needed
by Flypitch's quantifier rules.
-/


/-- Proof-translation construction identified upstream as `shiftIndexAt`. -/
@[expose]
def shiftIndexAt (cutoff index : Nat) : Nat :=
  if cutoff ≤ index then index + 1 else index

/-- Proof-translation construction identified upstream as `shiftRhoAt`. -/
@[expose]
def shiftRhoAt (rho : Var → Nat) (cutoff : Nat) : Var → Nat := fun x =>
  shiftIndexAt cutoff (rho x)

@[simp]
theorem shiftIndexAt_zero (index : Nat) : shiftIndexAt 0 index = index + 1 := by
  simp [shiftIndexAt]

@[simp]
theorem shiftIndexAt_succ_zero (cutoff : Nat) : shiftIndexAt (cutoff + 1) 0 = 0 := by
  simp [shiftIndexAt]

theorem shiftRhoAt_update (rho : Var → Nat) (cutoff : Nat) (x : Var) (candidate : Nat) :
    shiftRhoAt (updateRho rho x candidate) cutoff =
      updateRho (shiftRhoAt rho cutoff) x (shiftIndexAt cutoff candidate) :=
  by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [shiftRhoAt, updateRho]
  · simp [shiftRhoAt, updateRho, hy]

theorem shiftRhoAt_bind (rho : Var → Nat) (cutoff : Nat) (x : Var) :
    shiftRhoAt (bindRho rho x) (cutoff + 1) = bindRho (shiftRhoAt rho cutoff) x :=
  by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [shiftRhoAt, bindRho, shiftIndexAt]
  · simp [shiftRhoAt, bindRho, hy]
    by_cases hcut : cutoff ≤ rho y
    · simp [shiftIndexAt, hcut]
    · simp [shiftIndexAt, hcut]

theorem shiftRhoAt_lift (rho : Var → Nat) (cutoff : Nat) :
    shiftRhoAt (liftRho rho) (cutoff + 1) = liftRho (shiftRhoAt rho cutoff) :=
  by
  funext y
  simp [shiftRhoAt, liftRho]
  by_cases hcut : cutoff ≤ rho y
  · simp [shiftIndexAt, hcut]
  · simp [shiftIndexAt, hcut]

mutual
  theorem lowerClassPred_shiftAt (rho : Var → Nat) (candidate cutoff : Nat) (A : Class) :
      lowerClassPred (shiftRhoAt rho cutoff) (shiftIndexAt cutoff candidate) A =
        Fol.liftFormulaAt (lowerClassPred rho candidate A) 1 cutoff :=
    by
    cases A with
    | cv x =>
      simp [lowerClassPred, shiftRhoAt, shiftIndexAt, GenericLogicalHandlers.nfMem]
    | cab x p =>
      simp only [lowerClassPred]
      rw [← shiftRhoAt_update]
      exact lowerWff_shiftAt (updateRho rho x candidate) cutoff p
  theorem lowerWff_shiftAt (rho : Var → Nat) (cutoff : Nat) (p : Wff) :
      lowerWff (shiftRhoAt rho cutoff) p =
        Fol.liftFormulaAt (lowerWff rho p) 1 cutoff :=
    by
    cases p with
    | falsum => rfl
    | imp p q =>
      simp only [lowerWff, Fol.liftFormulaAt]
      rw [lowerWff_shiftAt rho cutoff p, lowerWff_shiftAt rho cutoff q]
    | all x p =>
      simp only [lowerWff, Fol.liftFormulaAt]
      rw [← shiftRhoAt_bind]
      exact congrArg Fol.preformula.all (lowerWff_shiftAt (bindRho rho x) (cutoff + 1) p)
    | objEq x y => simp [lowerWff, shiftRhoAt, shiftIndexAt]
    | objMem x y =>
      simp [lowerWff, shiftRhoAt, shiftIndexAt, GenericLogicalHandlers.nfMem]
    | classEq A
      B =>
      simp only [lowerWff, Fol.liftFormulaAt, biimp, conj, neg]
      rw [← shiftRhoAt_lift rho cutoff]
      have hA := lowerClassPred_shiftAt (liftRho rho) 0 (cutoff + 1) A
      have hB := lowerClassPred_shiftAt (liftRho rho) 0 (cutoff + 1) B
      simp only [shiftIndexAt_succ_zero] at hA hB
      rw [hA, hB]
    | classMem A
      B =>
      simp only [lowerWff, ex, conj, neg, biimp, Fol.liftFormulaAt]
      rw [← shiftRhoAt_lift rho cutoff]
      rw [← shiftRhoAt_lift (liftRho rho) (cutoff + 1)]
      have hA := lowerClassPred_shiftAt (liftRho (liftRho rho)) 0 (cutoff + 2) A
      have hB := lowerClassPred_shiftAt (liftRho rho) 0 (cutoff + 1) B
      simp only [shiftIndexAt_succ_zero] at hA hB
      rw [hA, hB]
      simp [GenericLogicalHandlers.nfMem, Nat.add_assoc]
end

mutual
  theorem _root_.NFChoice.DirectNominalPrf.Nominal.lowerClassPred_congr_fv
      (rho sigma : Var → Nat) (candidate : Nat) (A : Class)
      (h : ∀ x, x ∈ A.fv → rho x = sigma x) :
      lowerClassPred rho candidate A = lowerClassPred sigma candidate A := by
    cases A with
    | cv x =>
      simp only [Class.fv, Finset.mem_singleton] at h
      simp [lowerClassPred, h x rfl]
    | cab x p =>
      simp only [Class.fv] at h
      simp only [lowerClassPred]
      apply lowerWff_congr_fv
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        simp [updateRho]
      · simp [updateRho, hyx, h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)]
  theorem _root_.NFChoice.DirectNominalPrf.Nominal.lowerWff_congr_fv
      (rho sigma : Var → Nat) (p : Wff)
      (h : ∀ x, x ∈ p.fv → rho x = sigma x) : lowerWff rho p = lowerWff sigma p := by
    cases p with
    | falsum => rfl
    | imp p q =>
      simp only [Wff.fv, Finset.mem_union] at h
      simp only [lowerWff]
      rw [lowerWff_congr_fv rho sigma p (fun x hx => h x (Or.inl hx))]
      rw [lowerWff_congr_fv rho sigma q (fun x hx => h x (Or.inr hx))]
    | all x p =>
      simp only [Wff.fv] at h
      simp only [lowerWff]
      congr 1
      apply lowerWff_congr_fv
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        simp [bindRho]
      · simp [bindRho, hyx, h y (Finset.mem_erase.mpr ⟨hyx, hy⟩)]
    | objEq x
      y =>
      simp only [Wff.fv, Finset.mem_insert, Finset.mem_singleton] at h
      simp [lowerWff, h x (Or.inl rfl), h y (Or.inr rfl)]
    | objMem x
      y =>
      simp only [Wff.fv, Finset.mem_insert, Finset.mem_singleton] at h
      simp [lowerWff, h x (Or.inl rfl), h y (Or.inr rfl)]
    | classEq A B =>
      simp only [Wff.fv, Finset.mem_union] at h
      simp only [lowerWff]
      rw [lowerClassPred_congr_fv (liftRho rho) (liftRho sigma) 0 A
          (fun x hx => by simp [liftRho, h x (Or.inl hx)])]
      rw [lowerClassPred_congr_fv (liftRho rho) (liftRho sigma) 0 B
          (fun x hx => by simp [liftRho, h x (Or.inr hx)])]
    | classMem A B =>
      simp only [Wff.fv, Finset.mem_union] at h
      simp only [lowerWff]
      rw [lowerClassPred_congr_fv (liftRho (liftRho rho)) (liftRho (liftRho sigma)) 0 A
          (fun x hx => by simp [liftRho, h x (Or.inl hx)])]
      rw [lowerClassPred_congr_fv (liftRho rho) (liftRho sigma) 0 B
          (fun x hx => by simp [liftRho, h x (Or.inr hx)])]
end

theorem _root_.NFChoice.DirectNominalPrf.Nominal.bindRho_eq_shiftRhoAt_zero_of_ne
    (rho : Var → Nat) {x y : Var} (hyx : y ≠ x) :
    bindRho rho x y = shiftRhoAt rho 0 y := by
  simp [bindRho, shiftRhoAt, shiftIndexAt, hyx]

theorem _root_.NFChoice.DirectNominalPrf.Nominal.lowerWff_bind_eq_lift_of_not_mem_fv
    (rho : Var → Nat) (x : Var) (p : Wff)
    (hx : x ∉ p.fv) : lowerWff (bindRho rho x) p = Fol.liftFormula1 (lowerWff rho p) :=
  by
  calc
    lowerWff (bindRho rho x) p = lowerWff (shiftRhoAt rho 0) p :=
      by
      apply lowerWff_congr_fv
      intro y hy
      exact bindRho_eq_shiftRhoAt_zero_of_ne rho (fun hyx => hx (hyx ▸ hy))
    _ = Fol.liftFormulaAt (lowerWff rho p) 1 0 := (lowerWff_shiftAt rho 0 p)
    _ = Fol.liftFormula1 (lowerWff rho p) := rfl

/-- Proof-translation construction identified upstream as `ax17`. -/
@[expose]
def _root_.NFChoice.DirectNominalPrf.Nominal.ax17
    (p : Wff) (x : Var) (hx : x ∉ p.fv) : NPrf (.imp p (.all x p)) :=
  ax17OfShift p x (fun rho => lowerWff_bind_eq_lift_of_not_mem_fv rho x p hx)


end NFChoice.DirectNominalPrf.Nominal
