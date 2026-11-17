/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeMain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePrescribedProgram
public import LeanPool.TuringConeRigidity.SetModels.ValidFirstUncountable
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundGeneric

/-!
# Pairwise rigidity of principal Turing cones

A parameter-covering model includes any prescribed countable sequence and
representatives of e(a') and e^{-1}(b'). Its Cohen extension gives one program
correct on all sufficiently generic members of that sequence. Diagonalization
over the countably many candidates produces a global generic lift. Applying
the analytic theorem in both directions gives equal bases and pointwise identity.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeMain

open TransitiveNameModel BoundedSetTheory ElementaryModel RelationCollapse
open PersistentRestrictions OracleJump InternalCountableOrdinals
open CountableForcing TwoConeProgramGlobalization TwoConeRigidity
open TwoConeLocality (forwardAnchor inverseAnchor)

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

noncomputable section

theorem covering_model_with_omega_one {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (W : ℕ → Oracle) :
    ∃ M : ZFSet.{0}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        ∃ K : ZFSet.{0}, FirstUncountable M K ∧
          (∀ n, W n ∈ modelReals M) ∧
          forwardAnchor e ∈ (modelIdeal M hM hT).carrier ∧
          inverseAnchor e ∈ (modelIdeal M hM hT).carrier := by
  obtain ⟨B, hB⟩ := degree_surjective (forwardAnchor e)
  obtain ⟨C, hC⟩ := degree_surjective (inverseAnchor e)
  let S : ℕ → Oracle
    | 0 => B
    | 1 => C
    | n + 2 => W n
  let M := collapsed (ElementaryModel.hullSet (realSeed.{0} S))
  have hM : Transitive M := collapsed_transitive _
  have hT : SourceT M := collapsed_hull_sourceT _
  have hS (n : ℕ) : S n ∈ modelReals M :=
    (mem_collapsed _ _).mpr
      ⟨realCode (S n), seed_reals S n, (collapse_real_fixed S n).symm⟩
  obtain ⟨K, hK⟩ := ValidFirstUncountable.firstUncountable_exists M hM
    (collapsed_hull_valid (realSeed.{0} S)) ⟨realCode (S 0), hS 0⟩
  exact ⟨M, hM, hT, inferInstance, K, hK, (fun n => hS (n + 2)),
    ⟨B, hS 0, hB⟩, ⟨C, hS 1, hC⟩⟩

/-- Discharge countable tests for an arbitrary cone isomorphism. -/
theorem countable_tests {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) : CountableTests e := by
  intro W
  obtain ⟨M, hM, hT, hcount, K, hK, hWM, hpost, hpre⟩ :=
    covering_model_with_omega_one e W
  let := hcount
  have hcoords := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK.2.1 (sourceT_omega_mem M hM hT)
  obtain ⟨G, _, hG, hME, _, _, _⟩ :=
    CohenGroundGeneric.exists_extension M (ZFSet.prod K ZFSet.omega) hM hT hcoords ⊤
  obtain ⟨R, p, hR, hp⟩ :=
    TwoConePrescribedProgram.prescribed_program e M K hM hT hK hpost hpre G hG
  exact ⟨R, p, hR, fun n hn => hp (W n) (hME (hWM n)) hn⟩

/-- A finite program and fixed fifth-jump parameter work on every
arithmetic-generic input, not merely the reals of one countable model. -/
theorem arithmetic_inverse_program {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    ∃ (R : Oracle) (p : OracleCode), degree R = forwardAnchor e ∧
      ∀ X, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) X →
        RepresentsInverseAt e p (iterate R 5) X :=
  program_of_countable_tests e (countable_tests e)

theorem generic_inverse_program {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    InverseGenericProgramLift e :=
  generic_lift_of_countable_tests e (countable_tests e)

theorem inverse_borel_lift {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    InverseBorelLift e :=
  inverse_borel_lift_of_generic_program e (generic_inverse_program e)

/-- Different bases give nonisomorphic principal upper cones. -/
theorem cones_orderIso_iff (a b : Degree) :
    Nonempty (Set.Ici a ≃o Set.Ici b) ↔ a = b :=
  cones_orderIso_iff_of_generic_representation (fun _ _ e => generic_inverse_program e) a b

/-- Every cone isomorphism fixes every degree in its domain. -/
theorem cone_iso_apply_val {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (x : Set.Ici a) : (e x).val = x.val :=
  apply_val_eq_of_inverse_generic_programs e
    (generic_inverse_program e) (generic_inverse_program e.symm) x

theorem cone_automorphism_eq_refl {a : Degree} (e : Set.Ici a ≃o Set.Ici a) :
    e = OrderIso.refl (Set.Ici a) := by
  apply DFunLike.ext
  intro x
  exact Subtype.ext (cone_iso_apply_val e x)

theorem cone_iso_unique {a b : Degree} (e f : Set.Ici a ≃o Set.Ici b) : e = f := by
  apply DFunLike.ext
  intro x
  exact Subtype.ext ((cone_iso_apply_val e x).trans (cone_iso_apply_val f x).symm)

end
end OAI.TuringRigidity.TwoConeMain
