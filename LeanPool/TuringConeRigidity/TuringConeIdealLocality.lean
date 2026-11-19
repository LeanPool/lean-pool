/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeIdealLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRelativeUnary
public import LeanPool.TuringConeRigidity.TuringConeIdealForwardCoding
public import LeanPool.TuringConeRigidity.TuringConeLocality
public import LeanPool.TuringConeRigidity.SetModels.IdealLocality

/-!
# Two-sided locality for partial cone isomorphisms

The anchors on the two sides are different: the forward estimate uses the
preimage of a', whereas the inverse estimate uses the image of 0'. No jump
preservation is assumed. A jump ideal containing these anchors is invariant,
with its target interpreted as the part of the ideal above a.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeIdealLocality

open IdealInterpretation SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding
open OracleJump ArithmeticHierarchy ConeIdealCoding

noncomputable section

/-- Degree-level form of the relative localized-copy construction. -/
theorem relative_copy (a : Degree) (X : Oracle) :
    ∃ c : ConeCoding.Copy a (fun n => X n = true),
      ConeRelativeCoding.RelationAbove c.successor a ∧
      ConeRelativeCoding.RelationAbove c.predicate a ∧
      RelationBelow c.successor (degree X ⊔ degreeJump a) ∧
      RelationBelow c.predicate (degree X ⊔ degreeJump a) := by
  obtain ⟨A, rfl⟩ := degree_surjective a
  exact ConeRelativeCoding.localized_copy A X

/-- The forward value is arithmetic in the input joined with the preimage of a'. -/
theorem image_arithmetic {I : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (z : Set.Ici a) (hz : z.val.val = degreeJump a.val) (x : I) :
    ∃ X Y : Oracle, degree X = image ρ x ∧ degree Y = x.val ⊔ (ρ.symm z).val ∧
      Reduces X (iterate Y 5) := by
  obtain ⟨X, hX⟩ := degree_surjective (image ρ x)
  obtain ⟨c, haS, haP, hS, hP⟩ := relative_copy a.val X
  let b : Set.Ici a := ρ x ⊔ z
  have hb : degree X ⊔ degreeJump a.val = b.val.val := by
    change degree X ⊔ degreeJump a.val = image ρ x ⊔ z.val.val
    rw [hX, hz]
  obtain ⟨d, hdS, hdP⟩ := ConeIdealBackCoding.transport_copy ρ c b haS haP (hb ▸ hS) (hb ▸ hP)
  have he : (ρ.symm b).val = x.val ⊔ (ρ.symm z).val := by
    simp only [b, ρ.symm.map_sup, ρ.symm_apply_apply, coe_sup]
  obtain ⟨Y, hY⟩ := degree_surjective (ρ.symm b).val
  have hrec := (ArithmeticModelDecoding.unary_decoding Y d (hY.symm ▸ hdS) (hY.symm ▸ hdP)).2
  refine ⟨X, Y, hX, hY.trans he, ?_⟩
  apply RecursiveIn.iff_nat.mpr
  exact hrec.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction, hx])

/-- The inverse value is arithmetic in the target joined with the image of 0'. -/
theorem inverse_arithmetic {I : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (z : I) (hz : z.val = degree (jump FixedArithmetic.zero)) (y : Set.Ici a) :
    ∃ X Y : Oracle, degree X = (ρ.symm y).val ∧ degree Y = y.val.val ⊔ image ρ z ∧
      Reduces X (iterate Y 5) := by
  obtain ⟨X, hX⟩ := degree_surjective (ρ.symm y).val
  obtain ⟨c, hS, hP⟩ := LocalUnary.localized_copy X
  let b : I := ρ.symm y ⊔ z
  have hb : degree (join X (jump FixedArithmetic.zero)) = b.val := by
    change degree X ⊔ degree (jump FixedArithmetic.zero) = (ρ.symm y).val ⊔ z.val
    rw [hX, hz]
  obtain ⟨d, hdS, hdP⟩ := ConeIdealForwardCoding.transport_copy ρ c b (hb ▸ hS) (hb ▸ hP)
  have he : image ρ b = y.val.val ⊔ image ρ z := by
    rw [show b = ρ.symm y ⊔ z from rfl, image_sup]
    simp only [image, ρ.apply_symm_apply]
  obtain ⟨Y, hY⟩ := degree_surjective (image ρ b)
  have ha : a.val ≤ degree Y := hY.symm ▸ base_le_image ρ b
  have hrec := (ConeLocality.unary_decoding a.val Y ha d (hY.symm ▸ hdS) (hY.symm ▸ hdP)).2
  refine ⟨X, Y, hX, hY.trans he, ?_⟩
  apply RecursiveIn.iff_nat.mpr
  exact hrec.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction, hx])

theorem image_mem {I J : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (z : Set.Ici a) (hz : z.val.val = degreeJump a.val)
    (hjump : IdealLocality.JumpClosed J) (hpre : (ρ.symm z).val ∈ J.carrier)
    (x : I) (hx : x.val ∈ J.carrier) : image ρ x ∈ J.carrier := by
  obtain ⟨X, Y, hX, hY, hXY⟩ := image_arithmetic ρ z hz x
  have hbase : degree Y ∈ J.carrier := hY.symm ▸ J.join_mem hx hpre
  have hit (n : ℕ) : degree (iterate Y n) ∈ J.carrier := by
    induction n with
    | zero => exact hbase
    | succ n ih => exact hjump _ ih
  exact hX ▸ J.lower hXY (hit 5)

theorem inverse_mem {I J : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (z : I) (hz : z.val = degree (jump FixedArithmetic.zero))
    (hjump : IdealLocality.JumpClosed J) (hpost : image ρ z ∈ J.carrier)
    (y : Set.Ici a) (hy : y.val.val ∈ J.carrier) : (ρ.symm y).val ∈ J.carrier := by
  obtain ⟨X, Y, hX, hY, hXY⟩ := inverse_arithmetic ρ z hz y
  have hbase : degree Y ∈ J.carrier := hY.symm ▸ J.join_mem hy hpost
  have hit (n : ℕ) : degree (iterate Y n) ∈ J.carrier := by
    induction n with
    | zero => exact hbase
    | succ n ih => exact hjump _ ih
  exact hX ▸ J.lower hXY (hit 5)

/-- The cone analogue of the ordinary jump-ideal invariance lemma. -/
theorem invariant {I J : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (z₀ : I) (hz₀ : z₀.val = degree (jump FixedArithmetic.zero))
    (z₁ : Set.Ici a) (hz₁ : z₁.val.val = degreeJump a.val)
    (hjump : IdealLocality.JumpClosed J)
    (hpost : image ρ z₀ ∈ J.carrier) (hpre : (ρ.symm z₁).val ∈ J.carrier) (x : I) :
    image ρ x ∈ J.carrier ↔ x.val ∈ J.carrier := by
  constructor
  · intro h
    have hh := inverse_mem ρ z₀ hz₀ hjump hpost (ρ x) h
    simpa only [ρ.symm_apply_apply] using hh
  · exact image_mem ρ z₁ hz₁ hjump hpre x

/-- Restrict to a prescribed jump ideal, not merely a larger invariant hull. -/
theorem restrict_jump_ideal {I J : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (z₀ : I) (hz₀ : z₀.val = degree (jump FixedArithmetic.zero))
    (z₁ : Set.Ici a) (hz₁ : z₁.val.val = degreeJump a.val)
    (hJI : J.carrier ⊆ I.carrier) (haJ : a.val ∈ J.carrier)
    (hjump : IdealLocality.JumpClosed J)
    (hpost : image ρ z₀ ∈ J.carrier) (hpre : (ρ.symm z₁).val ∈ J.carrier) :
    ∃ σ : J ≃o Set.Ici (⟨a.val, haJ⟩ : J),
      ∀ x : J, image σ x = image ρ ⟨x.val, hJI x.property⟩ := by
  let aJ : J := ⟨a.val, haJ⟩
  let incl (x : J) : I := ⟨x.val, hJI x.property⟩
  let cincl (y : Set.Ici aJ) : Set.Ici a :=
    ⟨⟨y.val.val, hJI y.val.property⟩, y.property⟩
  let f (x : J) : Set.Ici aJ :=
    ⟨⟨image ρ (incl x), image_mem ρ z₁ hz₁ hjump hpre (incl x) x.property⟩,
      Set.mem_Ici.mpr (base_le_image ρ (incl x))⟩
  let g (y : Set.Ici aJ) : J :=
    ⟨(ρ.symm (cincl y)).val, inverse_mem ρ z₀ hz₀ hjump hpost (cincl y) y.val.property⟩
  have hgf (x : J) : g (f x) = x := by
    apply Element.ext
    change (ρ.symm (ρ (incl x))).val = x.val
    rw [ρ.symm_apply_apply]
  have hfg (y : Set.Ici aJ) : f (g y) = y := by
    apply Subtype.ext
    apply Element.ext
    change (ρ (ρ.symm (cincl y))).val.val = y.val.val
    rw [ρ.apply_symm_apply]
  let σ : J ≃o Set.Ici aJ :=
    { toEquiv := ⟨f, g, hgf, hfg⟩
      map_rel_iff' := by
        intro x y
        change ρ (incl x) ≤ ρ (incl y) ↔ incl x ≤ incl y
        exact ρ.le_iff_le }
  exact ⟨σ, fun _ => rfl⟩

end
end OAI.TuringRigidity.ConeIdealLocality
