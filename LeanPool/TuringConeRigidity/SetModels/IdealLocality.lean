/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IdealLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalUnary
public import LeanPool.TuringConeRigidity.SetModels.IdealCopy

/-!
# Ideal Locality
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IdealLocality
open OracleJump ArithmeticHierarchy ArithmeticModelDecoding BoundedDecoding IdealInterpretation
noncomputable section

/-- The degree ideal is closed under the Turing jump. -/
def JumpClosed (J : DegreeIdeal) : Prop := ∀ x, x ∈ J.carrier → degreeJump x ∈ J.carrier

theorem image_arithmetic {I : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (x : I) :
    ∃ X Y : Oracle, degree X = (ρ x).val ∧ degree Y = x.val ⊔ (ρ.symm z).val ∧
      Reduces X (iterate Y 5) := by
  obtain ⟨X,hX⟩ := degree_surjective (ρ x).val
  obtain ⟨c,hS,hP⟩ := LocalUnary.localized_copy X
  let b : I := ρ x ⊔ z
  have hb : degree (join X (jump FixedArithmetic.zero)) = b.val := by
    change degree X ⊔ degree (jump FixedArithmetic.zero) = (ρ x).val ⊔ z.val
    rw [hX,hz]
  obtain ⟨d,hdS,hdP⟩ := transport_copy ρ.symm c b (hb ▸ hS) (hb ▸ hP)
  have he : (ρ.symm b).val = x.val ⊔ (ρ.symm z).val := by
    simp only [b,ρ.symm.map_sup,ρ.symm_apply_apply,coe_sup]
  obtain ⟨Y,hY⟩ := degree_surjective (ρ.symm b).val
  have hY' : degree Y = x.val ⊔ (ρ.symm z).val := hY.trans he
  have hrec := (unary_decoding Y d (hY.symm ▸ hdS) (hY.symm ▸ hdP)).2
  have hXY : Reduces X (iterate Y 5) := by
    apply RecursiveIn.iff_nat.mpr
    exact hrec.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction,hx])
  exact ⟨X,Y,hX,hY',hXY⟩

theorem image_mem {I J : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (hjump : JumpClosed J)
    (hpre : (ρ.symm z).val ∈ J.carrier) (x : I) (hx : x.val ∈ J.carrier) :
    (ρ x).val ∈ J.carrier := by
  obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic ρ z hz x
  have hbase : degree Y ∈ J.carrier := hY.symm ▸ J.join_mem hx hpre
  have hit (n : ℕ) : degree (iterate Y n) ∈ J.carrier := by
    induction n with
    | zero => exact hbase
    | succ n ih => exact hjump _ ih
  exact hX ▸ J.lower hXY (hit 5)

theorem invariant {I J : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (hjump : JumpClosed J)
    (himages : (ρ z).val ⊔ (ρ.symm z).val ∈ J.carrier) (x : I) :
    (ρ x).val ∈ J.carrier ↔ x.val ∈ J.carrier := by
  have hforward := image_mem ρ z hz hjump (J.lower le_sup_right himages)
  have hback := image_mem ρ.symm z hz hjump (J.lower le_sup_left himages)
  exact ⟨fun h => by simpa only [ρ.symm_apply_apply] using hback (ρ x) h,hforward x⟩

theorem source_4_1_4 {I J : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (hJI : J.carrier ⊆ I.carrier)
    (hjump : JumpClosed J) (himages : (ρ z).val ⊔ (ρ.symm z).val ∈ J.carrier) :
    ∃ σ : J ≃o J, ∀ x : J, (σ x).val = (ρ ⟨x.val,hJI x.property⟩).val := by
  let incl : J → I := fun x => ⟨x.val,hJI x.property⟩
  let f : J → J := fun x => ⟨(ρ (incl x)).val,
    (invariant ρ z hz hjump himages (incl x)).mpr x.property⟩
  let g : J → J := fun x => ⟨(ρ.symm (incl x)).val,by
    apply (invariant ρ z hz hjump himages (ρ.symm (incl x))).mp
    simpa only [ρ.apply_symm_apply,incl] using x.property⟩
  have hfg (x : J) : f (g x) = x := by
    apply Element.ext
    change (ρ (ρ.symm (incl x))).val = x.val
    rw [ρ.apply_symm_apply]
  have hgf (x : J) : g (f x) = x := by
    apply Element.ext
    change (ρ.symm (ρ (incl x))).val = x.val
    rw [ρ.symm_apply_apply]
  let σ : J ≃o J :=
    { toEquiv := ⟨f,g,hgf,hfg⟩
      map_rel_iff' := by
        intro x y
        change ρ (incl x) ≤ ρ (incl y) ↔ incl x ≤ incl y
        exact ρ.le_iff_le }
  exact ⟨σ,fun _ => rfl⟩

end
end TuringRigidity.IdealLocality

end OAI
