/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.PartialLowering

/-! NF weak partition development: DefinitionLeaves.Basic. -/


public section

namespace NFChoice.DefinitionLeaves

open NFChoice.Foundation
open NFChoice.SemanticCore

namespace Wff

/-- Every ordinary wff definition becomes this shape after expansion. -/
theorem valid_biimp_refl {S : Fol.Structure LNF} (p : SemanticCore.Wff) :
    SemanticCore.Wff.Valid S (SemanticCore.Wff.biimp p p) :=
  by
  intro v
  simp

/-- Pointwise semantic equality is enough to discharge a normalized wff leaf. -/
theorem valid_biimp_of_holds_iff {S : Fol.Structure LNF} (p q : SemanticCore.Wff)
    (h : ∀ v : SemanticCore.Var → S,
        SemanticCore.Wff.Holds S v p ↔ SemanticCore.Wff.Holds S v q) :
    SemanticCore.Wff.Valid S (SemanticCore.Wff.biimp p q) :=
  by
  intro v
  simpa using h v

/-- `df-tru` after choosing `T.` to expand to `F. → F.`. -/
theorem valid_df_tru {S : Fol.Structure LNF} (p : SemanticCore.Wff) :
    SemanticCore.Wff.Valid S
      (SemanticCore.Wff.biimp (.imp .falsum .falsum) (SemanticCore.Wff.biimp p p)) :=
  by
  intro v
  simp [SemanticCore.Wff.Holds]

end Wff

namespace Class

/-- Every ordinary class definition without a generated dummy becomes this shape. -/
theorem valid_classEq_refl {S : Fol.Structure LNF} (A : SemanticCore.Class) :
    SemanticCore.Wff.Valid S (.classEq A A) :=
  by
  intro v z
  rfl

/-- Pointwise class-denotation equality discharges a normalized class leaf. -/
theorem valid_classEq_of_holds_iff {S : Fol.Structure LNF} (A B : SemanticCore.Class)
    (h : ∀ (v : SemanticCore.Var → S) (z : S),
        SemanticCore.Class.Holds S v A z ↔ SemanticCore.Class.Holds S v B z) :
    SemanticCore.Wff.Valid S (.classEq A B) :=
  by
  intro v z
  exact h v z

/-- Updating a name fresh for a class cannot change its denotation. -/
theorem holds_update_fresh {S : Fol.Structure LNF} (A : SemanticCore.Class)
    (v : SemanticCore.Var → S) {x : SemanticCore.Var} (hx : x ∉ A.fv) (a z : S) :
    SemanticCore.Class.Holds S (SemanticCore.update v x a) A z ↔
      SemanticCore.Class.Holds S v A z :=
  by
  apply SemanticCore.Class.holds_congr_fv A
  intro y hy
  have hyx : y ≠ x := by
    intro h
    subst y
    exact hx hy
  simp [SemanticCore.update_noteq, hyx]

end Class

namespace SemanticBoundary

/-- A set-variable class represents exactly the corresponding set. -/
theorem classMem_cv_iff_holds {S : Fol.Structure LNF} (hExt : SemanticCore.Extensional S)
    (v : SemanticCore.Var → S) (x : SemanticCore.Var) (B : SemanticCore.Class) :
    SemanticCore.Wff.Holds S v (.classMem (.cv x) B) ↔
      SemanticCore.Class.Holds S v B (v x) :=
  by
  simp only [SemanticCore.Wff.Holds]
  constructor
  · rintro ⟨a, ha, hB⟩
    have hax : a = v x := hExt a (v x) ha
    simpa [hax] using hB
  · intro hB
    exact ⟨v x, fun _ => Iff.rfl, hB⟩

/-- The exact normalized semantic leaf for source `df-clab`. -/
theorem valid_df_clab {S : Fol.Structure LNF} (hExt : SemanticCore.Extensional S)
    (x y : SemanticCore.Var) (p : SemanticCore.Wff) :
    SemanticCore.Wff.Valid S
      (SemanticCore.Wff.biimp (.classMem (.cv x) (.cab y p))
        (SemanticCore.sbDefiniens x y p)) :=
  by
  intro v
  simp only [SemanticCore.Wff.holds_biimp]
  exact
    (SemanticCore.df_clab_semantics hExt v x y p).trans
      (by
        simpa [SemanticCore.CvSubstHolds, SemanticCore.SubstHolds] using
          SemanticCore.df_sb_semantics v x y p)

/-- The exact normalized semantic leaf for source `df-cleq`. -/
theorem valid_df_cleq {S : Fol.Structure LNF} (hExt : SemanticCore.Extensional S)
    (x : SemanticCore.Var) (A B : SemanticCore.Class) (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    SemanticCore.Wff.Valid S
      (SemanticCore.Wff.biimp (.classEq A B)
        (.all x (SemanticCore.Wff.biimp (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  intro v
  apply SemanticCore.Wff.holds_biimp.mpr
  constructor
  · intro h a
    apply SemanticCore.Wff.holds_biimp.mpr
    let w := SemanticCore.update v x a
    have hmemA :
      SemanticCore.Wff.Holds S w (.classMem (.cv x) A) ↔
        SemanticCore.Class.Holds S v A a :=
      by
      rw [classMem_cv_iff_holds hExt]
      simpa [w] using Class.holds_update_fresh A v hxA a a
    have hmemB :
      SemanticCore.Wff.Holds S w (.classMem (.cv x) B) ↔
        SemanticCore.Class.Holds S v B a :=
      by
      rw [classMem_cv_iff_holds hExt]
      simpa [w] using Class.holds_update_fresh B v hxB a a
    exact hmemA.trans ((h a).trans hmemB.symm)
  · intro h a
    have ha := h a
    have ha' := SemanticCore.Wff.holds_biimp.mp ha
    let w := SemanticCore.update v x a
    have hmemA :
      SemanticCore.Wff.Holds S w (.classMem (.cv x) A) ↔
        SemanticCore.Class.Holds S v A a :=
      by
      rw [classMem_cv_iff_holds hExt]
      simpa [w] using Class.holds_update_fresh A v hxA a a
    have hmemB :
      SemanticCore.Wff.Holds S w (.classMem (.cv x) B) ↔
        SemanticCore.Class.Holds S v B a :=
      by
      rw [classMem_cv_iff_holds hExt]
      simpa [w] using Class.holds_update_fresh B v hxB a a
    exact hmemA.symm.trans (ha'.trans hmemB)

/-- The exact normalized semantic leaf for source `df-clel`. -/
theorem valid_df_clel {S : Fol.Structure LNF} (hExt : SemanticCore.Extensional S)
    (x : SemanticCore.Var) (A B : SemanticCore.Class) (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    SemanticCore.Wff.Valid S
      (SemanticCore.Wff.biimp (.classMem A B) (SemanticCore.Wff.ex x
          (SemanticCore.Wff.conj (.classEq (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  intro v
  apply SemanticCore.Wff.holds_biimp.mpr
  constructor
  · rintro ⟨a, hA, hB⟩
    apply SemanticCore.Wff.holds_ex.mpr
    refine ⟨a, SemanticCore.Wff.holds_conj.mpr ⟨?_, ?_⟩⟩
    · intro z
      have hz := (hA z).trans (Class.holds_update_fresh A v hxA a z).symm
      simpa [SemanticCore.Class.Holds] using hz
    · apply (classMem_cv_iff_holds hExt (SemanticCore.update v x a) x B).mpr
      simpa using (Class.holds_update_fresh B v hxB a a).mpr hB
  · intro h
    rcases SemanticCore.Wff.holds_ex.mp h with ⟨a, ha⟩
    rcases SemanticCore.Wff.holds_conj.mp ha with ⟨hA, hB⟩
    change
      ∃ a : S,
        (∀ z : S, SemanticCore.Mem S z a ↔ SemanticCore.Class.Holds S v A z) ∧
          SemanticCore.Class.Holds S v B a
    refine ⟨a, ?_, ?_⟩
    · intro z
      have hz := hA z
      simp only [SemanticCore.Class.Holds, SemanticCore.update_same] at hz
      exact hz.trans (Class.holds_update_fresh A v hxA a z)
    · have hB' := (classMem_cv_iff_holds hExt (SemanticCore.update v x a) x B).mp hB
      have hB'' : SemanticCore.Class.Holds S (SemanticCore.update v x a) B a := by
        simpa using hB'
      exact (Class.holds_update_fresh B v hxB a a).mp hB''

end SemanticBoundary

end NFChoice.DefinitionLeaves
