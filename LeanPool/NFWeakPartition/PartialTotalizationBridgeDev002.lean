/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalNFLiteralHandlers

/-! NF weak partition development: PartialTotalizationBridgeDev002. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.Totalization

open NFChoice.Foundation
open NFChoice.SemanticCore

/-- Proof-translation construction identified upstream as `totalizeRho`. -/
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
    totalizeRho (SemanticCore.PartialLowering.liftRhoOption rho) (Fin.succ default) =
      SemanticCore.Lowering.liftRho (totalizeRho rho default) :=
  by
  funext x
  cases hx : rho x <;>
    simp [totalizeRho, SemanticCore.PartialLowering.liftRhoOption,
      SemanticCore.Lowering.liftRho, hx]

theorem totalize_bind {n : Nat} (rho : Var → Option (Fin n)) (default : Fin n) (x : Var) :
    totalizeRho (SemanticCore.PartialLowering.bindRhoOption rho x) (Fin.succ default) =
      SemanticCore.Lowering.bindRho (totalizeRho rho default) x :=
  by
  rw [SemanticCore.PartialLowering.bindRhoOption, SemanticCore.Lowering.bindRho,
    totalize_update_some, totalize_lift]

mutual
  theorem _root_.NFChoice.DirectNominalPrf.Nominal.Totalization.lowerClassPredOption_some_totalize
      {n : Nat} (rho : Var → Option (Fin n))
      (default candidate : Fin n) (A : Class) (f : Formula n)
      (h : SemanticCore.PartialLowering.lowerClassPredOption rho candidate A = some f) :
      SemanticCore.Lowering.lowerClassPred (totalizeRho rho default) candidate A = f := by
    cases A with
    | cv x =>
      cases hx : rho x with
      | none => simp [SemanticCore.PartialLowering.lowerClassPredOption, hx] at h
      | some i =>
        simp [SemanticCore.PartialLowering.lowerClassPredOption, hx] at h
        subst f
        simp [SemanticCore.Lowering.lowerClassPred, totalizeRho, hx]
    | cab x p =>
      simp only [SemanticCore.PartialLowering.lowerClassPredOption] at h
      have ih :=
        lowerWffOption_some_totalize (Function.update rho x (some candidate)) default p f h
      simpa [SemanticCore.Lowering.lowerClassPred, totalize_update_some] using ih
  theorem _root_.NFChoice.DirectNominalPrf.Nominal.Totalization.lowerWffOption_some_totalize
      {n : Nat} (rho : Var → Option (Fin n)) (default : Fin n)
      (p : Wff) (f : Formula n)
      (h : SemanticCore.PartialLowering.lowerWffOption rho p = some f) :
      SemanticCore.Lowering.lowerWff (totalizeRho rho default) p = f := by
    cases p with
    | falsum =>
      simp [SemanticCore.PartialLowering.lowerWffOption] at h
      subst f
      rfl
    | imp p q =>
      cases hp : SemanticCore.PartialLowering.lowerWffOption rho p with
      | none => simp [SemanticCore.PartialLowering.lowerWffOption, hp] at h
      | some fp =>
        cases hq : SemanticCore.PartialLowering.lowerWffOption rho q with
        | none => simp [SemanticCore.PartialLowering.lowerWffOption, hp, hq] at h
        | some fq =>
          simp [SemanticCore.PartialLowering.lowerWffOption, hp, hq] at h
          subst f
          simp [SemanticCore.Lowering.lowerWff,
            lowerWffOption_some_totalize rho default p fp hp,
            lowerWffOption_some_totalize rho default q fq hq]
    | all x p =>
      cases hp :
        SemanticCore.PartialLowering.lowerWffOption
          (SemanticCore.PartialLowering.bindRhoOption rho x) p with
      | none => simp [SemanticCore.PartialLowering.lowerWffOption, hp] at h
      | some fp =>
        simp [SemanticCore.PartialLowering.lowerWffOption, hp] at h
        subst f
        have ih :=
          lowerWffOption_some_totalize (SemanticCore.PartialLowering.bindRhoOption rho x)
            (Fin.succ default) p fp hp
        simpa [SemanticCore.Lowering.lowerWff, totalize_bind] using ih
    | objEq x y =>
      cases hx : rho x with
      | none => simp [SemanticCore.PartialLowering.lowerWffOption, hx] at h
      | some ix =>
        cases hy : rho y with
        | none => simp [SemanticCore.PartialLowering.lowerWffOption, hx, hy] at h
        | some iy =>
          simp [SemanticCore.PartialLowering.lowerWffOption, hx, hy] at h
          subst f
          simp [SemanticCore.Lowering.lowerWff, totalizeRho, hx, hy]
    | objMem x y =>
      cases hx : rho x with
      | none => simp [SemanticCore.PartialLowering.lowerWffOption, hx] at h
      | some ix =>
        cases hy : rho y with
        | none => simp [SemanticCore.PartialLowering.lowerWffOption, hx, hy] at h
        | some iy =>
          simp [SemanticCore.PartialLowering.lowerWffOption, hx, hy] at h
          subst f
          simp [SemanticCore.Lowering.lowerWff, totalizeRho, hx, hy]
    | classEq A B =>
      cases hA :
        SemanticCore.PartialLowering.lowerClassPredOption
          (SemanticCore.PartialLowering.liftRhoOption rho) 0 A with
      | none => simp [SemanticCore.PartialLowering.lowerWffOption, hA] at h
      | some fA =>
        cases hB :
          SemanticCore.PartialLowering.lowerClassPredOption
            (SemanticCore.PartialLowering.liftRhoOption rho) 0 B with
        | none => simp [SemanticCore.PartialLowering.lowerWffOption, hA, hB] at h
        | some fB =>
          simp [SemanticCore.PartialLowering.lowerWffOption, hA, hB] at h
          subst f
          have ihA :=
            lowerClassPredOption_some_totalize (SemanticCore.PartialLowering.liftRhoOption rho)
              (Fin.succ default) 0 A fA hA
          have ihB :=
            lowerClassPredOption_some_totalize (SemanticCore.PartialLowering.liftRhoOption rho)
              (Fin.succ default) 0 B fB hB
          simp only [totalize_lift] at ihA ihB
          simp [SemanticCore.Lowering.lowerWff, ihA, ihB]
    | classMem A B =>
      cases hA :
        SemanticCore.PartialLowering.lowerClassPredOption
          (SemanticCore.PartialLowering.liftRhoOption
            (SemanticCore.PartialLowering.liftRhoOption rho))
          0 A with
      | none => simp [SemanticCore.PartialLowering.lowerWffOption, hA] at h
      | some fA =>
        cases hB :
          SemanticCore.PartialLowering.lowerClassPredOption
            (SemanticCore.PartialLowering.liftRhoOption rho) 0 B with
        | none => simp [SemanticCore.PartialLowering.lowerWffOption, hA, hB] at h
        | some fB =>
          simp [SemanticCore.PartialLowering.lowerWffOption, hA, hB] at h
          subst f
          have ihA :=
            lowerClassPredOption_some_totalize
              (SemanticCore.PartialLowering.liftRhoOption
                (SemanticCore.PartialLowering.liftRhoOption rho))
              (Fin.succ (Fin.succ default)) 0 A fA hA
          have ihB :=
            lowerClassPredOption_some_totalize (SemanticCore.PartialLowering.liftRhoOption rho)
              (Fin.succ default) 0 B fB hB
          simp only [totalize_lift] at ihA ihB
          simp [SemanticCore.Lowering.lowerWff, ihA, ihB]
end


end NFChoice.DirectNominalPrf.Nominal.Totalization
