/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ElementaryRealModel.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.ParameterCoveringModels

/-!
# Elementary Real Model
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SentenceForm
universe u

theorem hull_real_fixed (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) {A : Oracle} (hA : realCode A ∈ hullSet a) :
    structureMap (hullSet a) (realCode A) = realCode A := by
  apply collapse_fixed _ _ hA
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset A hx)
  refine ⟨hn n,structureMap_fixed omega_transitive ?_ _ ((mem_omega _).mpr ⟨n,rfl⟩)⟩
  intro y hy
  obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
  exact hn m

theorem hull_omega_fixed (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a) :
    structureMap (hullSet a) ZFSet.omega = ZFSet.omega := by
  apply collapse_fixed _ _ hω
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  refine ⟨hn n,structureMap_fixed omega_transitive ?_ _ ((mem_omega _).mpr ⟨n,rfl⟩)⟩
  intro y hy
  obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
  exact hn m

theorem collapsed_hull_reals (a : ℕ → ZFSet.{u})
    (hn : ∀ n, natSet.{u} n ∈ hullSet a) (hω : ZFSet.omega ∈ hullSet a) (A : Oracle) :
    A ∈ modelReals (collapsed (hullSet a)) ↔ realCode A ∈ hullSet a := by
  constructor
  · intro hA
    obtain ⟨x,hx,heq⟩ := (mem_collapsed (hullSet a) (realCode A)).mp hA
    let e := cons x (fun _ => ZFSet.omega)
    have hen : ∀ i, e i ∈ hullSet a := by intro i; cases i <;> assumption
    let p := all (imp (.member 0 1) (.member 0 2))
    have hs : p.Sat (collapsed (hullSet a) : Set ZFSet) (fun i => structureMap (hullSet a) (e i))
      := by
      simp only [p,sat_all,sat_imp,Sat,cons_zero,cons_succ,e]
      intro y _ hy
      rw [←heq] at hy
      rw [hull_omega_fixed a hn hω]
      exact realCode_subset A hy
    have ht := (collapsed_hull_elementary a p e hen).mp hs
    simp only [p,sat_all,sat_imp,Sat,cons_zero,cons_succ,e,Set.mem_univ,forall_const] at ht
    have hxreal : realCode (decodeReal x) = x := realCode_decodeReal ht
    have hfix : structureMap (hullSet a) x = x := by
      rw [←hxreal]
      exact hull_real_fixed a hn (hxreal.symm ▸ hx)
    exact heq.symm ▸ hfix.symm ▸ hx
  · intro hA
    exact (mem_collapsed _ _).mpr ⟨realCode A,hA,(hull_real_fixed a hn hA).symm⟩

/-- A countable seed containing numerals, the supplied oracle codes, the supplied set
parameters, and omega. -/
noncomputable def mixedSeed (a : ℕ → ZFSet.{u}) (A : ℕ → Oracle) (n : ℕ) : ZFSet.{u} :=
  match n.unpair.1 with
  | 0 => natSet n.unpair.2
  | 1 => realCode (A n.unpair.2)
  | 2 => a n.unpair.2
  | _ => ZFSet.omega

theorem mixed_naturals (a : ℕ → ZFSet.{u}) (A : ℕ → Oracle) (n : ℕ) :
    natSet.{u} n ∈ hullSet (mixedSeed a A) := by
  apply (mem_hullSet _ _).mpr
  simpa [mixedSeed] using parameter_mem (mixedSeed a A) (Nat.pair 0 n)

theorem mixed_omega (a : ℕ → ZFSet.{u}) (A : ℕ → Oracle) :
    ZFSet.omega.{u} ∈ hullSet (mixedSeed a A) := by
  apply (mem_hullSet _ _).mpr
  simpa [mixedSeed] using parameter_mem (mixedSeed a A) (Nat.pair 3 0)

theorem parameter_models_with_elementarity (a : ℕ → ZFSet.{u}) (A : ℕ → Oracle) :
    ∃ d M : ZFSet.{u}, Transitive M ∧ SourceT M ∧ Countable (Conditions M) ∧
      StructureExtensional d ∧ (∀ n, a n ∈ d) ∧
      (∀ n, realCode (A n) ∈ d ∧ structureMap d (realCode (A n)) = realCode (A n)) ∧
      (∀ n, structureMap d (a n) ∈ M) ∧
      (∀ B : Oracle, B ∈ modelReals M ↔ realCode B ∈ d) ∧
      (∀ p : SentenceForm, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ d) →
        (p.Sat (M : Set ZFSet) (fun i => structureMap d (e i)) ↔ p.Sat Set.univ e)) := by
  let b := mixedSeed a A
  have hn := mixed_naturals a A
  have hω := mixed_omega a A
  have ha (n : ℕ) : a n ∈ hullSet b := by
    apply (mem_hullSet _ _).mpr
    simpa [b,mixedSeed] using parameter_mem b (Nat.pair 2 n)
  have hA (n : ℕ) : realCode (A n) ∈ hullSet b := by
    apply (mem_hullSet _ _).mpr
    simpa [b,mixedSeed] using parameter_mem b (Nat.pair 1 n)
  refine ⟨hullSet b,collapsed (hullSet b),collapsed_transitive _,collapsed_hull_sourceT _,
    inferInstance,hullSet_extensional _,ha,(fun n => ⟨hA n,hull_real_fixed b hn (hA n)⟩),
    (fun n => (mem_collapsed _ _).mpr ⟨a n,ha n,rfl⟩),collapsed_hull_reals b hn hω,?_⟩
  exact collapsed_hull_elementary b

end TuringRigidity.ElementaryModel

end OAI
