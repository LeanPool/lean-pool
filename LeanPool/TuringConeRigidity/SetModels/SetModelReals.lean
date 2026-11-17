/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelReals.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalInfinity
public import LeanPool.TuringConeRigidity.SetModels.SetPresentationDecoding

/-!
# Set Model Reals
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

def realSet (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ n, x = natSet n ∧ A n = true) ZFSet.omega

@[simp] theorem nat_mem_realSet (A : Oracle) (n : ℕ) :
    natSet.{u} n ∈ realSet A ↔ A n = true := by
  simp only [realSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,m,hm,hA⟩
    exact natSet_injective hm ▸ hA
  · intro hA
    exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,⟨n,rfl,hA⟩⟩

theorem realSet_subset (A : Oracle) : realSet.{u} A ⊆ ZFSet.omega :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem realSet_injective : Function.Injective realSet.{u} := by
  intro A B he
  funext n
  have h : A n = true ↔ B n = true := by rw [← nat_mem_realSet,he,nat_mem_realSet]
  cases ha : A n <;> cases hb : B n <;> simp_all

def oracleOf (x : ZFSet.{u}) : Oracle := by
  classical
  exact fun n => decide (natSet n ∈ x)

@[simp] theorem oracleOf_realSet (A : Oracle) : oracleOf (realSet.{u} A) = A := by
  funext n
  simp only [oracleOf,nat_mem_realSet]
  cases A n <;> rfl

theorem realSet_oracleOf {x : ZFSet.{u}} (hx : x ⊆ ZFSet.omega) :
    realSet (oracleOf x) = x := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨n,rfl⟩ := (mem_omega y).mp (realSet_subset _ hy)
    simpa [oracleOf] using (nat_mem_realSet _ n).mp hy
  · intro hy
    obtain ⟨n,rfl⟩ := (mem_omega y).mp (hx hy)
    apply (nat_mem_realSet _ _).mpr
    simpa [oracleOf] using hy

def reals (M : ZFSet.{u}) : Set Oracle := {A | realSet A ∈ M}

theorem internal_reals (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M) (hI : Infinity M) :
    ∃ r ∈ M, ∀ x, x ∈ r ↔ ∃ A ∈ reals M, x = realSet A := by
  obtain ⟨r,hr,hrdef⟩ := internal_power M hM hPow (omega_mem M hM hS hI)
  refine ⟨r,hr,fun x => ?_⟩
  rw [hrdef]
  constructor
  · rintro ⟨hxM,hx⟩
    exact ⟨oracleOf x,by simpa only [reals,Set.mem_ofPred_eq,realSet_oracleOf hx] using hxM,
      (realSet_oracleOf hx).symm⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨hA,realSet_subset A⟩

theorem omega_exists (P : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, P x) ↔ ∃ n, P (natSet n) := by
  constructor
  · rintro ⟨x,hx,hP⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,hP⟩
  · rintro ⟨n,hP⟩
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,hP⟩

theorem real_formula_absolute (M : ZFSet.{u}) (hM : Transitive M)
    (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    φ.Realize M e ↔ φ.Eval e := φ.absolute M hM e he

theorem real_comprehension (M : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hI : Infinity M)
    (A : Oracle) (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hφ : ∀ n, φ.Eval (cons (natSet n) e) ↔ A n = true) : A ∈ reals M := by
  have h := sep_mem M hM hS φ e he (omega_mem M hM hS hI)
  have eq : ZFSet.sep (fun x => φ.Eval (cons x e)) ZFSet.omega = realSet A := by
    apply ZFSet.ext
    intro x
    by_cases hx : x ∈ ZFSet.omega
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      simp only [ZFSet.mem_sep,hx,true_and,nat_mem_realSet,hφ]
    · simp only [ZFSet.mem_sep,hx,false_and]
      exact iff_false_intro (fun h => hx (realSet_subset A h)) |>.symm
  change realSet A ∈ M
  exact eq ▸ h

end
end TuringRigidity.SetModelReals

end OAI
