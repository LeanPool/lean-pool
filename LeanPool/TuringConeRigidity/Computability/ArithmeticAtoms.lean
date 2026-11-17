/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticAtoms.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticHierarchy
public import LeanPool.TuringConeRigidity.OrdinalCodes.IndexPresentation

/-!
# Arithmetic Atoms
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle IndexMatrix OrderNormalForm IndexPresentation

theorem exists_form {Y n P} (h : Pi Y n P) :
    Sigma Y (n+1) (fun x => ∃ a, P (Nat.pair x a)) := ⟨P, h, fun _ => Iff.rfl⟩

theorem forall_form {Y n P} (h : Sigma Y n P) :
    Pi Y (n+1) (fun x => ∀ a, P (Nat.pair x a)) := ⟨P, h, fun _ => Iff.rfl⟩

theorem dom_pi (Y : Oracle) {e : ℕ → ℕ} (he : Primrec e) :
    Pi Y 2 (fun x => Dom Y (e x)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hm := total_comp (validMatrix_recursive Y) (total_primrec
    (Primrec₂.natPair.comp (he.comp (f.comp f)) (Primrec₂.natPair.comp (s.comp f) s)))
  have h : RecursivePred Y (fun v => validMatrix Y (e (Nat.unpair (Nat.unpair v).1).1)
      (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2) := by
    exact hm.of_eq (fun v => by simp only [Nat.unpair_pair]; congr 1; split <;> rfl)
  exact (forall_form (exists_form (Y := Y) (n := 0) h)).congr
    (fun x => by simp only [Nat.unpair_pair]; exact (valid_normal_form Y (e x)).symm)

theorem le_sigma (Y : Oracle) {e f : ℕ → ℕ} (he : Primrec e) (hf : Primrec f) :
    Sigma Y 3 (fun x => LE Y (e x) (f x)) := by
  classical
  let a := Primrec.fst.comp Primrec.unpair
  let b := Primrec.snd.comp Primrec.unpair
  let x := a.comp (a.comp a)
  let d := b.comp (a.comp a)
  let q := b.comp a
  let r := b
  have hm := total_comp (orderMatrix_recursive Y) (total_primrec
    (Primrec₂.natPair.comp (he.comp x) (Primrec₂.natPair.comp (hf.comp x)
      (Primrec₂.natPair.comp d (Primrec₂.natPair.comp q r)))))
  have h : RecursivePred Y (fun v => orderMatrix Y
      (e (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1)
      (f (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1)
      (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2
      (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2) := by
    exact hm.of_eq (fun v => by simp only [Nat.unpair_pair]; congr 1; split <;> rfl)
  exact (exists_form (forall_form (exists_form (Y := Y) (n := 0) h))).congr
    (fun x => by simp only [Nat.unpair_pair]; rfl)

end TuringRigidity.ArithmeticHierarchy

end OAI
