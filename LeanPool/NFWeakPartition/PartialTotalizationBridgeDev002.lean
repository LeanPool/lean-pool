/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalNFLiteralHandlers

/-! NF weak partition development: PartialTotalizationBridgeDev002. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.PartialTotalizationBridgeDev002

open NFChoice.Foundation
open NFChoice.SemanticCore

@[expose]
def totalizeRho {n : Nat} (rho : Var → Option (Fin n)) (default : Fin n) : Var → Fin n :=
  fun x => (rho x).getD default

theorem totalize_update_some {n : Nat} (rho : Var → Option (Fin n))
    (default value : Fin n) (x : Var) :
    totalizeRho (Function.update rho x (some value)) default =
      Function.update (totalizeRho rho default) x value :=
  by
  funext y
  by_cases hyx : y = x <;> simp [totalizeRho, Function.update, hyx]

theorem totalize_lift {n : Nat} (rho : Var → Option (Fin n)) (default : Fin n) :
    totalizeRho (SemanticCore.PartialLowering.liftRho? rho) (Fin.succ default) =
      SemanticCore.Lowering.liftRho (totalizeRho rho default) :=
  by
  funext x
  cases hx : rho x <;>
    simp [totalizeRho, SemanticCore.PartialLowering.liftRho?,
      SemanticCore.Lowering.liftRho, hx]

theorem totalize_bind {n : Nat} (rho : Var → Option (Fin n)) (default : Fin n) (x : Var) :
    totalizeRho (SemanticCore.PartialLowering.bindRho? rho x) (Fin.succ default) =
      SemanticCore.Lowering.bindRho (totalizeRho rho default) x :=
  by
  rw [SemanticCore.PartialLowering.bindRho?, SemanticCore.Lowering.bindRho,
    totalize_update_some, totalize_lift]

mutual
  theorem lowerClassPred?_some_totalize {n : Nat} (rho : Var → Option (Fin n))
      (default candidate : Fin n) (A : Class) (f : Formula n)
      (h : SemanticCore.PartialLowering.lowerClassPred? rho candidate A = some f) :
      SemanticCore.Lowering.lowerClassPred (totalizeRho rho default) candidate A = f := by
    cases A with
    | cv x =>
      cases hx : rho x with
      | none => simp [SemanticCore.PartialLowering.lowerClassPred?, hx] at h
      | some i =>
        simp [SemanticCore.PartialLowering.lowerClassPred?, hx] at h
        subst f
        simp [SemanticCore.Lowering.lowerClassPred, totalizeRho, hx]
    | cab x p =>
      simp only [SemanticCore.PartialLowering.lowerClassPred?] at h
      have ih :=
        lowerWff?_some_totalize (Function.update rho x (some candidate)) default p f h
      simpa [SemanticCore.Lowering.lowerClassPred, totalize_update_some] using ih
  theorem lowerWff?_some_totalize {n : Nat} (rho : Var → Option (Fin n)) (default : Fin n)
      (p : Wff) (f : Formula n)
      (h : SemanticCore.PartialLowering.lowerWff? rho p = some f) :
      SemanticCore.Lowering.lowerWff (totalizeRho rho default) p = f := by
    cases p with
    | falsum =>
      simp [SemanticCore.PartialLowering.lowerWff?] at h
      subst f
      rfl
    | imp p q =>
      cases hp : SemanticCore.PartialLowering.lowerWff? rho p with
      | none => simp [SemanticCore.PartialLowering.lowerWff?, hp] at h
      | some fp =>
        cases hq : SemanticCore.PartialLowering.lowerWff? rho q with
        | none => simp [SemanticCore.PartialLowering.lowerWff?, hp, hq] at h
        | some fq =>
          simp [SemanticCore.PartialLowering.lowerWff?, hp, hq] at h
          subst f
          simp [SemanticCore.Lowering.lowerWff,
            lowerWff?_some_totalize rho default p fp hp,
            lowerWff?_some_totalize rho default q fq hq]
    | all x p =>
      cases hp :
        SemanticCore.PartialLowering.lowerWff?
          (SemanticCore.PartialLowering.bindRho? rho x) p with
      | none => simp [SemanticCore.PartialLowering.lowerWff?, hp] at h
      | some fp =>
        simp [SemanticCore.PartialLowering.lowerWff?, hp] at h
        subst f
        have ih :=
          lowerWff?_some_totalize (SemanticCore.PartialLowering.bindRho? rho x)
            (Fin.succ default) p fp hp
        simpa [SemanticCore.Lowering.lowerWff, totalize_bind] using ih
    | objEq x y =>
      cases hx : rho x with
      | none => simp [SemanticCore.PartialLowering.lowerWff?, hx] at h
      | some ix =>
        cases hy : rho y with
        | none => simp [SemanticCore.PartialLowering.lowerWff?, hx, hy] at h
        | some iy =>
          simp [SemanticCore.PartialLowering.lowerWff?, hx, hy] at h
          subst f
          simp [SemanticCore.Lowering.lowerWff, totalizeRho, hx, hy]
    | objMem x y =>
      cases hx : rho x with
      | none => simp [SemanticCore.PartialLowering.lowerWff?, hx] at h
      | some ix =>
        cases hy : rho y with
        | none => simp [SemanticCore.PartialLowering.lowerWff?, hx, hy] at h
        | some iy =>
          simp [SemanticCore.PartialLowering.lowerWff?, hx, hy] at h
          subst f
          simp [SemanticCore.Lowering.lowerWff, totalizeRho, hx, hy]
    | classEq A B =>
      cases hA :
        SemanticCore.PartialLowering.lowerClassPred?
          (SemanticCore.PartialLowering.liftRho? rho) 0 A with
      | none => simp [SemanticCore.PartialLowering.lowerWff?, hA] at h
      | some fA =>
        cases hB :
          SemanticCore.PartialLowering.lowerClassPred?
            (SemanticCore.PartialLowering.liftRho? rho) 0 B with
        | none => simp [SemanticCore.PartialLowering.lowerWff?, hA, hB] at h
        | some fB =>
          simp [SemanticCore.PartialLowering.lowerWff?, hA, hB] at h
          subst f
          have ihA :=
            lowerClassPred?_some_totalize (SemanticCore.PartialLowering.liftRho? rho)
              (Fin.succ default) 0 A fA hA
          have ihB :=
            lowerClassPred?_some_totalize (SemanticCore.PartialLowering.liftRho? rho)
              (Fin.succ default) 0 B fB hB
          simp only [totalize_lift] at ihA ihB
          simp [SemanticCore.Lowering.lowerWff, ihA, ihB]
    | classMem A B =>
      cases hA :
        SemanticCore.PartialLowering.lowerClassPred?
          (SemanticCore.PartialLowering.liftRho? (SemanticCore.PartialLowering.liftRho? rho))
          0 A with
      | none => simp [SemanticCore.PartialLowering.lowerWff?, hA] at h
      | some fA =>
        cases hB :
          SemanticCore.PartialLowering.lowerClassPred?
            (SemanticCore.PartialLowering.liftRho? rho) 0 B with
        | none => simp [SemanticCore.PartialLowering.lowerWff?, hA, hB] at h
        | some fB =>
          simp [SemanticCore.PartialLowering.lowerWff?, hA, hB] at h
          subst f
          have ihA :=
            lowerClassPred?_some_totalize
              (SemanticCore.PartialLowering.liftRho?
                (SemanticCore.PartialLowering.liftRho? rho))
              (Fin.succ (Fin.succ default)) 0 A fA hA
          have ihB :=
            lowerClassPred?_some_totalize (SemanticCore.PartialLowering.liftRho? rho)
              (Fin.succ default) 0 B fB hB
          simp only [totalize_lift] at ihA ihB
          simp [SemanticCore.Lowering.lowerWff, ihA, ihB]
end


end NFChoice.DirectNominalPrf.Nominal.PartialTotalizationBridgeDev002
