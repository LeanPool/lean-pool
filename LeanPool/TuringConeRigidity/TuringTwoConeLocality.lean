/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.PersistentLocality
public import LeanPool.TuringConeRigidity.TuringTwoConeIdealLocality
public import LeanPool.TuringConeRigidity.TuringTwoConePersistence

/-!
# Global two-cone locality with two fixed distinguished degrees

The distinguished degrees are `e(a')` and `e.symm(b')`. Every jump ideal
containing them is invariant in the two-cone sense; if countable, it carries a
persistent restriction of the original global map. The joined inverse also
has a pointwise fifth-jump bound with one fixed oracle representing `e(a')`.
This bound alone is not a Borel or uniform generic representative.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeLocality

open IdealInterpretation OracleJump ArithmeticHierarchy PersistentRestrictions
open TwoConeRigidity
open ConePersistence (Cone)

noncomputable section

/-- The degree ideal containing all ordinary Turing degrees. -/
def whole : DegreeIdeal where
  carrier := Set.univ
  nonempty := ⟨⊥, Set.mem_univ _⟩
  lower := fun _ _ => Set.mem_univ _
  join_mem := fun _ _ => Set.mem_univ _

/-- The degree `a` regarded as an element of the full ideal. -/
def wholeBase (a : Degree) : whole := ⟨a, Set.mem_univ _⟩

/-- The identity-on-values order isomorphism between the ambient cone and its full-ideal
representation. -/
def wholeBridge (a : Degree) : Set.Ici a ≃o Set.Ici (wholeBase a) where
  toFun x := ⟨⟨x.val, Set.mem_univ _⟩, Set.mem_Ici.mpr (Set.mem_Ici.mp x.property)⟩
  invFun x := ⟨x.val.val, Set.mem_Ici.mpr (Set.mem_Ici.mp x.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Transport an ambient two-cone isomorphism to the corresponding cones in the full ideal. -/
def liftGlobal {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) :
    Set.Ici (wholeBase a) ≃o Set.Ici (wholeBase b) :=
  (wholeBridge a).symm.trans (e.trans (wholeBridge b))

/-- The Turing jump of the base as an element of its principal cone. -/
def jumpPoint (a : Degree) : Set.Ici a :=
  ⟨degreeJump a, Set.mem_Ici.mpr (degree_le_jump a)⟩

/-- The image of the source base's jump under the cone isomorphism. -/
def forwardAnchor {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) : Degree :=
  (e (jumpPoint a)).val

/-- The inverse image of the target base's jump under the cone isomorphism. -/
def inverseAnchor {a b : Degree} (e : Set.Ici a ≃o Set.Ici b) : Degree :=
  (e.symm (jumpPoint b)).val

theorem image_le_fifth_jump {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (x : Set.Ici a) :
    (e x).val ≤ GlobalLocality.degreeIterate (x.val ⊔ inverseAnchor e) 5 :=
  TwoConeIdealLocality.image_le_fifth_jump (liftGlobal e)
    (wholeBridge b (jumpPoint b)) rfl (wholeBridge a x)

theorem inverse_le_fifth_jump {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (y : Set.Ici b) :
    (e.symm y).val ≤ GlobalLocality.degreeIterate (y.val ⊔ forwardAnchor e) 5 :=
  TwoConeIdealLocality.inverse_le_fifth_jump (liftGlobal e)
    (wholeBridge a (jumpPoint a)) rfl (wholeBridge b y)

/-- Every representative satisfies the same bound using a fixed old oracle.
The reduction index is not asserted to be uniform in the varying input. -/
theorem pullback_reduces_fifth_jump {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (P : Oracle) (hP : degree P = forwardAnchor e)
    (X Y : Oracle) (hX : degree X = pullback e (degree Y)) :
    Reduces X (iterate (join Y P) 5) := by
  have hb : b ≤ degree P := hP.symm ▸ Set.mem_Ici.mp (e (jumpPoint a)).property
  have h : pullback e (degree Y) ≤
      GlobalLocality.degreeIterate ((b ⊔ degree Y) ⊔ forwardAnchor e) 5 :=
    inverse_le_fifth_jump e (ConeRigidity.coneJoin b (degree Y))
  have he : (b ⊔ degree Y) ⊔ forwardAnchor e = degree (join Y P) := by
    rw [← hP]
    change (b ⊔ degree Y) ⊔ degree P = degree Y ⊔ degree P
    exact le_antisymm
      (sup_le (sup_le (hb.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  rw [he, GlobalLocality.degreeIterate_degree] at h
  change degree X ≤ degree (iterate (join Y P) 5)
  simpa only [hX] using h

theorem image_mem {a b : Degree} {J : DegreeIdeal} (e : Set.Ici a ≃o Set.Ici b)
    (hjump : IdealLocality.JumpClosed J) (hpre : inverseAnchor e ∈ J.carrier)
    (x : Set.Ici a) (hx : x.val ∈ J.carrier) : (e x).val ∈ J.carrier :=
  TwoConeIdealLocality.image_mem (liftGlobal e) (wholeBridge b (jumpPoint b)) rfl
    hjump hpre (wholeBridge a x) hx

theorem inverse_mem {a b : Degree} {J : DegreeIdeal} (e : Set.Ici a ≃o Set.Ici b)
    (hjump : IdealLocality.JumpClosed J) (hpost : forwardAnchor e ∈ J.carrier)
    (y : Set.Ici b) (hy : y.val ∈ J.carrier) : (e.symm y).val ∈ J.carrier :=
  TwoConeIdealLocality.inverse_mem (liftGlobal e) (wholeBridge a (jumpPoint a)) rfl
    hjump hpost (wholeBridge b y) hy

theorem imageJoin_mem {a b : Degree} {J : DegreeIdeal} (e : Set.Ici a ≃o Set.Ici b)
    (hjump : IdealLocality.JumpClosed J) (hpre : inverseAnchor e ∈ J.carrier)
    (x : Degree) (hx : x ∈ J.carrier) : imageJoin e x ∈ J.carrier := by
  have ha : a ∈ J.carrier :=
    J.lower (Set.mem_Ici.mp (e.symm (jumpPoint b)).property) hpre
  exact image_mem e hjump hpre (ConeRigidity.coneJoin a x) (J.join_mem ha hx)

theorem pullback_mem {a b : Degree} {J : DegreeIdeal} (e : Set.Ici a ≃o Set.Ici b)
    (hjump : IdealLocality.JumpClosed J) (hpost : forwardAnchor e ∈ J.carrier)
    (x : Degree) (hx : x ∈ J.carrier) : pullback e x ∈ J.carrier := by
  have hb : b ∈ J.carrier :=
    J.lower (Set.mem_Ici.mp (e (jumpPoint a)).property) hpost
  exact inverse_mem e hjump hpost (ConeRigidity.coneJoin b x) (J.join_mem hb hx)

/-- It suffices to include the two distinguished values, not the entire map,
in a countable jump ideal. The actual global restriction is persistent. -/
theorem global_jump_restriction {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (I : CountableIdeal) (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal I))
    (hpost : forwardAnchor e ∈ I.carrier) (hpre : inverseAnchor e ∈ I.carrier) :
    ∃ ρ : Cone I a ≃o Cone I b,
      TwoConePersistence.RestrictsTo e I ρ ∧ TwoConePersistence.Persistent I ρ := by
  have hf : ∀ x ∈ I.carrier, imageJoin e x ∈ I.carrier :=
    fun x hx => imageJoin_mem e hjump hpre x hx
  have hb : ∀ x ∈ I.carrier, pullback e x ∈ I.carrier :=
    fun x hx => pullback_mem e hjump hpost x hx
  let ρ := TwoConePersistence.restrict e I hf hb
  have hρ : TwoConePersistence.RestrictsTo e I ρ := fun _ => rfl
  exact ⟨ρ, hρ, TwoConePersistence.persistent_of_global_restriction e I ρ hρ⟩

end
end OAI.TuringRigidity.TwoConeLocality
