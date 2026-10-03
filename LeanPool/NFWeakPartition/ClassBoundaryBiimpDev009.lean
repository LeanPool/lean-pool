/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ClassBoundaryCoreDev006

/-! NF weak partition development: ClassBoundaryBiimpDev009. -/


public section

namespace NFChoice.DirectCertificate.ClassBoundaryBiimpDev009

open scoped Fol

@[expose]
noncomputable def biimpForward {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p q : Fol.formula L} (h : Γ ⊢ p ⇔ q) (hp : Γ ⊢ p) : Γ ⊢ q :=
  Fol.prf.impE p (Fol.andE1 (q ⟹ p) h) hp

@[expose]
noncomputable def biimpBackward {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p q : Fol.formula L} (h : Γ ⊢ p ⇔ q) (hq : Γ ⊢ q) : Γ ⊢ p :=
  Fol.prf.impE q (Fol.andE2 (p ⟹ q) h) hq

@[expose]
noncomputable def biimpCongr {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p p' q q' : Fol.formula L} (hpEq : Γ ⊢ p ⇔ p') (hqEq : Γ ⊢ q ⇔ q') :
    Γ ⊢ (p ⇔ q) ⇔ (p' ⇔ q') := by
  apply Fol.biimpI
  · apply Fol.biimpI
    · have hSource : insert p' (insert (p ⇔ q) Γ) ⊢ p ⇔ q := Fol.prf.axm (by simp)
      have hpEq' : insert p' (insert (p ⇔ q) Γ) ⊢ p ⇔ p' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem p' (Set.mem_insert_of_mem (p ⇔ q) hf))
          hpEq
      have hqEq' : insert p' (insert (p ⇔ q) Γ) ⊢ q ⇔ q' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem p' (Set.mem_insert_of_mem (p ⇔ q) hf))
          hqEq
      have hp' : insert p' (insert (p ⇔ q) Γ) ⊢ p' := Fol.axm1
      exact biimpForward hqEq' (biimpForward hSource (biimpBackward hpEq' hp'))
    · have hSource : insert q' (insert (p ⇔ q) Γ) ⊢ p ⇔ q := Fol.prf.axm (by simp)
      have hpEq' : insert q' (insert (p ⇔ q) Γ) ⊢ p ⇔ p' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem q' (Set.mem_insert_of_mem (p ⇔ q) hf))
          hpEq
      have hqEq' : insert q' (insert (p ⇔ q) Γ) ⊢ q ⇔ q' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem q' (Set.mem_insert_of_mem (p ⇔ q) hf))
          hqEq
      have hq' : insert q' (insert (p ⇔ q) Γ) ⊢ q' := Fol.axm1
      exact biimpForward hpEq' (biimpBackward hSource (biimpBackward hqEq' hq'))
  · apply Fol.biimpI
    · have hSource : insert p (insert (p' ⇔ q') Γ) ⊢ p' ⇔ q' := Fol.prf.axm (by simp)
      have hpEq' : insert p (insert (p' ⇔ q') Γ) ⊢ p ⇔ p' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem p (Set.mem_insert_of_mem (p' ⇔ q') hf))
          hpEq
      have hqEq' : insert p (insert (p' ⇔ q') Γ) ⊢ q ⇔ q' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem p (Set.mem_insert_of_mem (p' ⇔ q') hf))
          hqEq
      have hp : insert p (insert (p' ⇔ q') Γ) ⊢ p := Fol.axm1
      exact biimpBackward hqEq' (biimpForward hSource (biimpForward hpEq' hp))
    · have hSource : insert q (insert (p' ⇔ q') Γ) ⊢ p' ⇔ q' := Fol.prf.axm (by simp)
      have hpEq' : insert q (insert (p' ⇔ q') Γ) ⊢ p ⇔ p' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem q (Set.mem_insert_of_mem (p' ⇔ q') hf))
          hpEq
      have hqEq' : insert q (insert (p' ⇔ q') Γ) ⊢ q ⇔ q' :=
        Fol.weakening
          (by
            intro f hf
            exact Set.mem_insert_of_mem q (Set.mem_insert_of_mem (p' ⇔ q') hf))
          hqEq
      have hq : insert q (insert (p' ⇔ q') Γ) ⊢ q := Fol.axm1
      exact biimpBackward hpEq' (biimpBackward hSource (biimpForward hqEq' hq))


end NFChoice.DirectCertificate.ClassBoundaryBiimpDev009
