/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConeIdealLocality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeIdealCopies
public import LeanPool.TuringConeRigidity.TuringConeIdealLocality
public import LeanPool.TuringConeRigidity.Representation.GlobalLocality

/-!
# Two-sided arithmetic locality for isomorphisms of two ideal cones

The source and target ideals may differ. Forward values are bounded by five
jumps of the input joined with the preimage of the target-base jump. The inverse
bound uses the image of the source-base jump. No jump preservation, persistence,
Borelness, or generic representation is assumed. These are pointwise estimates,
not a uniform program selecting a representative as the input varies.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeIdealLocality

open IdealInterpretation SetCoding RelationCoding BoundedDecoding
open OracleJump ArithmeticHierarchy TwoConeIdealCodes

noncomputable section

/-- Decode the target predicate after transporting its relative code backwards. -/
theorem image_arithmetic {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (z : Set.Ici b)
    (hz : val z = degreeJump b.val) (x : Set.Ici a) :
    ∃ X Y : Oracle, degree X = val (ρ x) ∧
      degree Y = val x ⊔ val (ρ.symm z) ∧ Reduces X (iterate Y 5) := by
  obtain ⟨X, hX⟩ := degree_surjective (val (ρ x))
  obtain ⟨c, haS, haP, hS, hP⟩ := ConeIdealLocality.relative_copy b.val X
  let w : Set.Ici b := ρ x ⊔ z
  have hw : degree X ⊔ degreeJump b.val = val w := by
    change degree X ⊔ degreeJump b.val = val (ρ x) ⊔ val z
    rw [hX, hz]
  obtain ⟨d, _, _, hdS, hdP⟩ := TwoConeIdealCodes.transport_copy ρ.symm c w
    haS haP (hw ▸ hS) (hw ▸ hP)
  have he : val (ρ.symm w) = val x ⊔ val (ρ.symm z) := by
    simp only [w, ρ.symm.map_sup, ρ.symm_apply_apply, val_sup]
  obtain ⟨Y, hY⟩ := degree_surjective (val (ρ.symm w))
  have ha : a.val ≤ degree Y := hY.symm ▸ base_le (ρ.symm w)
  have hrec := (ConeLocality.unary_decoding a.val Y ha d
    (hY.symm ▸ hdS) (hY.symm ▸ hdP)).2
  refine ⟨X, Y, hX, hY.trans he, ?_⟩
  apply RecursiveIn.iff_nat.mpr
  exact hrec.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction, hx])

/-- The inverse estimate is the same theorem with the two bases exchanged. -/
theorem inverse_arithmetic {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (z : Set.Ici a)
    (hz : val z = degreeJump a.val) (y : Set.Ici b) :
    ∃ X Y : Oracle, degree X = val (ρ.symm y) ∧
      degree Y = val y ⊔ val (ρ z) ∧ Reduces X (iterate Y 5) :=
  image_arithmetic ρ.symm z hz y

theorem image_le_fifth_jump {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (z : Set.Ici b)
    (hz : val z = degreeJump b.val) (x : Set.Ici a) :
    val (ρ x) ≤ GlobalLocality.degreeIterate (val x ⊔ val (ρ.symm z)) 5 := by
  obtain ⟨X, Y, hX, hY, hred⟩ := image_arithmetic ρ z hz x
  have h : degree X ≤ degree (iterate Y 5) := hred
  simpa only [← GlobalLocality.degreeIterate_degree, hX, hY] using h

theorem inverse_le_fifth_jump {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (z : Set.Ici a)
    (hz : val z = degreeJump a.val) (y : Set.Ici b) :
    val (ρ.symm y) ≤ GlobalLocality.degreeIterate (val y ⊔ val (ρ z)) 5 :=
  image_le_fifth_jump ρ.symm z hz y

theorem image_mem {I J K : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (z : Set.Ici b)
    (hz : val z = degreeJump b.val) (hjump : IdealLocality.JumpClosed K)
    (hpre : val (ρ.symm z) ∈ K.carrier) (x : Set.Ici a) (hx : val x ∈ K.carrier) :
    val (ρ x) ∈ K.carrier := by
  obtain ⟨X, Y, hX, hY, hred⟩ := image_arithmetic ρ z hz x
  have hbase : degree Y ∈ K.carrier := hY.symm ▸ K.join_mem hx hpre
  have hit (n : ℕ) : degree (iterate Y n) ∈ K.carrier := by
    induction n with
    | zero => exact hbase
    | succ n ih => exact hjump _ ih
  exact hX ▸ K.lower hred (hit 5)

theorem inverse_mem {I J K : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (z : Set.Ici a)
    (hz : val z = degreeJump a.val) (hjump : IdealLocality.JumpClosed K)
    (hpost : val (ρ z) ∈ K.carrier) (y : Set.Ici b) (hy : val y ∈ K.carrier) :
    val (ρ.symm y) ∈ K.carrier :=
  image_mem ρ.symm z hz hjump hpost y hy

/-- The two distinguished values force invariance of an intermediate jump ideal. -/
theorem invariant {I J K : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b)
    (za : Set.Ici a) (hza : val za = degreeJump a.val)
    (zb : Set.Ici b) (hzb : val zb = degreeJump b.val)
    (hjump : IdealLocality.JumpClosed K)
    (hpost : val (ρ za) ∈ K.carrier) (hpre : val (ρ.symm zb) ∈ K.carrier)
    (x : Set.Ici a) : val (ρ x) ∈ K.carrier ↔ val x ∈ K.carrier := by
  constructor
  · intro h
    have hh := inverse_mem ρ za hza hjump hpost (ρ x) h
    simpa only [ρ.symm_apply_apply] using hh
  · exact image_mem ρ zb hzb hjump hpre x

/-- Restrict to the prescribed ideal, with both the source and target cut at
its own base. No persistence of the larger map is required. -/
theorem restrict_jump_ideal {I J K : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b)
    (za : Set.Ici a) (hza : val za = degreeJump a.val)
    (zb : Set.Ici b) (hzb : val zb = degreeJump b.val)
    (hKI : K.carrier ⊆ I.carrier) (hKJ : K.carrier ⊆ J.carrier)
    (haK : a.val ∈ K.carrier) (hbK : b.val ∈ K.carrier)
    (hjump : IdealLocality.JumpClosed K)
    (hpost : val (ρ za) ∈ K.carrier) (hpre : val (ρ.symm zb) ∈ K.carrier) :
    ∃ σ : Set.Ici (⟨a.val, haK⟩ : K) ≃o Set.Ici (⟨b.val, hbK⟩ : K),
      ∀ x : Set.Ici (⟨a.val, haK⟩ : K),
        val (σ x) = val (ρ ⟨⟨val x, hKI x.val.property⟩, x.property⟩) := by
  let aK : K := ⟨a.val, haK⟩
  let bK : K := ⟨b.val, hbK⟩
  let incl (x : Set.Ici aK) : Set.Ici a :=
    ⟨⟨val x, hKI x.val.property⟩, x.property⟩
  let cincl (y : Set.Ici bK) : Set.Ici b :=
    ⟨⟨val y, hKJ y.val.property⟩, y.property⟩
  let f (x : Set.Ici aK) : Set.Ici bK :=
    ⟨⟨val (ρ (incl x)), image_mem ρ zb hzb hjump hpre (incl x) x.val.property⟩,
      Set.mem_Ici.mpr (base_le (ρ (incl x)))⟩
  let g (y : Set.Ici bK) : Set.Ici aK :=
    ⟨⟨val (ρ.symm (cincl y)), inverse_mem ρ za hza hjump hpost (cincl y) y.val.property⟩,
      Set.mem_Ici.mpr (base_le (ρ.symm (cincl y)))⟩
  have hgf (x : Set.Ici aK) : g (f x) = x := by
    apply Subtype.ext
    apply Element.ext
    change val (ρ.symm (ρ (incl x))) = val x
    rw [ρ.symm_apply_apply]
  have hfg (y : Set.Ici bK) : f (g y) = y := by
    apply Subtype.ext
    apply Element.ext
    change val (ρ (ρ.symm (cincl y))) = val y
    rw [ρ.apply_symm_apply]
  let σ : Set.Ici aK ≃o Set.Ici bK :=
    { toEquiv := ⟨f, g, hgf, hfg⟩
      map_rel_iff' := by
        intro x y
        change ρ (incl x) ≤ ρ (incl y) ↔ incl x ≤ incl y
        exact ρ.le_iff_le }
  exact ⟨σ, fun _ => rfl⟩

end
end OAI.TuringRigidity.TwoConeIdealLocality
