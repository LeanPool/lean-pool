/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Intervals.Maps

/-!
# Morphisms between interval representations

Morphisms between the intervals `Y` and `P i` are read off at the point `*`: their value there
is a scalar, multiplicative under composition, and it vanishes on `Y ⟶ P i` and on
`P j ⟶ P i` for `j < i` (table (2.2)). A morphism `A j ⟶ A i` is a scalar multiple of the
canonical map `a_{ji}`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

/-- A label whose interval contains `*` (the labels `Y` and `P i`). -/
def HasBot : IntervalCat k I → Prop
  | Y => True
  | A _ => False
  | P _ => True

lemma bot_mem_support {l : IntervalCat k I} (hl : HasBot l) : (⊥ : WithBot I) ∈ l.support := by
  rcases l with _ | i | i
  · exact Set.mem_Iic.mpr le_rfl
  · exact absurd hl id
  · exact Set.mem_Iic.mpr bot_le

lemma bot_not_mem_support_A (i : I) : (⊥ : WithBot I) ∉ (A i).support :=
  IntervalLabel.not_bot_mem_A i

/-- The value at `*` of a morphism between intervals containing `*`. -/
noncomputable def coeffBot {l l' : IntervalCat k I} (_hl : HasBot l) (hl' : HasBot l')
    (φ : l.rep k ⟶ l'.rep k) : k :=
  (φ.app ⊥).hom (fun _ => (1 : k)) ⟨(), bot_mem_support hl'⟩

/-- The constant function `1` at a point of an interval. -/
abbrev oneAt (U : Set (WithBot I)) [U.OrdConnected] (t : WithBot I) :
    (intervalRep U : Rep k I).obj t := fun _ => (1 : k)

lemma eq_smul_oneAt {U : Set (WithBot I)} [U.OrdConnected] {t : WithBot I} (ht : t ∈ U)
    (f : (intervalRep U : Rep k I).obj t) : f = f ⟨(), ht⟩ • oneAt U t := by
  funext x
  exact (mul_one _).symm

/-- A morphism of intervals acts at a common point by its value on `1`. -/
lemma app_apply_eq_mul {U V : Set (WithBot I)} [U.OrdConnected] [V.OrdConnected]
    (φ : (intervalRep U : Rep k I) ⟶ intervalRep V) {t : WithBot I} (ht : t ∈ U)
    (f : (intervalRep U : Rep k I).obj t) (x : {_x : Unit // t ∈ V}) :
    (φ.app t).hom f x = f ⟨(), ht⟩ * (φ.app t).hom (oneAt U t) x := by
  have h := congrArg (fun g => (φ.app t).hom g x) (eq_smul_oneAt ht f)
  refine h.trans ?_
  rw [LinearMap.map_smul]
  rfl

lemma coeffBot_comp {l l' l'' : IntervalCat k I} (hl : HasBot l) (hl' : HasBot l')
    (hl'' : HasBot l'') (φ : l.rep k ⟶ l'.rep k) (ψ : l'.rep k ⟶ l''.rep k) :
    coeffBot hl hl'' (φ ≫ ψ) = coeffBot hl hl' φ * coeffBot hl' hl'' ψ :=
  app_apply_eq_mul ψ (bot_mem_support hl') ((φ.app ⊥).hom (oneAt _ ⊥)) _

lemma coeffBot_comp_of_A {l l'' : IntervalCat k I} (hl : HasBot l) (hl'' : HasBot l'') (i : I)
    (φ : l.rep k ⟶ (A i).rep k) (ψ : (A i).rep k ⟶ l''.rep k) :
    coeffBot hl hl'' (φ ≫ ψ) = 0 := by
  have hg : (φ.app ⊥).hom (oneAt _ ⊥) = 0 :=
    intervalRep_obj_eq_zero (bot_not_mem_support_A i) _
  change (ψ.app ⊥).hom ((φ.app ⊥).hom (oneAt _ ⊥)) _ = 0
  rw [hg, map_zero]
  rfl

lemma coeffBot_id {l : IntervalCat k I} (hl : HasBot l) : coeffBot hl hl (𝟙 (l.rep k)) = 1 :=
  rfl

lemma coeffBot_add {l l' : IntervalCat k I} (hl : HasBot l) (hl' : HasBot l')
    (φ ψ : l.rep k ⟶ l'.rep k) : coeffBot hl hl' (φ + ψ) = coeffBot hl hl' φ + coeffBot hl hl' ψ :=
  rfl

lemma coeffBot_smul {l l' : IntervalCat k I} (hl : HasBot l) (hl' : HasBot l') (r : k)
    (φ : l.rep k ⟶ l'.rep k) : coeffBot hl hl' (r • φ) = r * coeffBot hl hl' φ :=
  rfl

/-- A morphism into `P i` from an interval containing `*` is determined by its value at
`*` restricted to `i`: if the source vanishes at `i`, the value at `*` is zero. -/
lemma coeffBot_eq_zero_of_P {l : IntervalCat k I} (hl : HasBot l) (i : I)
    (hi : (i : WithBot I) ∉ l.support) (φ : l.rep k ⟶ (P i).rep k) :
    coeffBot hl (show HasBot (P i) from trivial) φ = 0 := by
  have hbot : (⊥ : WithBot I) ≤ (i : WithBot I) := bot_le
  have hiP : (i : WithBot I) ∈ (P i).support := Set.mem_Iic.mpr le_rfl
  have hbP : (⊥ : WithBot I) ∈ (P i).support := Set.mem_Iic.mpr bot_le
  have h := congrArg (fun g => g.hom (oneAt l.support ⊥) ⟨(), hiP⟩)
    (φ.naturality (homOfLE hbot))
  have hz : ((l.rep k).map (homOfLE hbot)).hom (oneAt l.support ⊥) = 0 :=
    intervalRep_obj_eq_zero hi _
  change (φ.app (i : WithBot I)).hom (((l.rep k).map (homOfLE hbot)).hom (oneAt _ ⊥)) _ =
    (((P i).rep k).map (homOfLE hbot)).hom ((φ.app ⊥).hom (oneAt _ ⊥)) ⟨(), hiP⟩ at h
  rw [hz, map_zero] at h
  have h2 := (intervalRep_map_apply (k := k) (U := (P i).support) hbot
    ((φ.app ⊥).hom (oneAt _ ⊥)) ⟨(), hiP⟩).trans (dite_eq_left hbP)
  exact (h2.symm.trans h.symm).trans rfl

/-- A morphism `A j ⟶ A i` is `coeffRep φ • a_{ji}` when `i ≤ j`. -/
lemma eq_coeffRep_smul_aMap {i j : I} (hij : i ≤ j) (φ : (A j).rep k ⟶ (A i).rep k) :
    φ = coeffRep φ • aMap hij := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  by_cases hti : t ∈ (A i).support
  · apply intervalRep_obj_ext hti
    by_cases htj : t ∈ (A j).support
    · refine (app_apply_eq_mul φ htj f _).trans ?_
      have hc : (φ.app t).hom (oneAt _ t) ⟨(), hti⟩ = coeffRep φ := app_one_eq_coeffRep φ htj hti
      have ha : ((aMap hij).app t).hom f ⟨(), hti⟩ = f ⟨(), htj⟩ :=
        (intervalMap_app_apply (k := k) _ _ _ t f _).trans (dite_eq_left htj)
      calc f ⟨(), htj⟩ * (φ.app t).hom (oneAt _ t) ⟨(), hti⟩ = f ⟨(), htj⟩ * coeffRep φ := by
            rw [hc]
        _ = coeffRep φ * ((aMap hij).app t).hom f ⟨(), hti⟩ := by rw [ha, mul_comm]
        _ = _ := rfl
    · have hf0 : f = 0 := intervalRep_obj_eq_zero htj f
      rw [hf0, map_zero, map_zero]
  · exact (show Subsingleton (((A i).rep k).obj t) from
      ⟨fun _ _ => funext fun x => absurd x.2 hti⟩).elim _ _

lemma eq_zero_of_not_le {i j : I} (hij : ¬ i ≤ j) (φ : (A j).rep k ⟶ (A i).rep k) : φ = 0 := by
  apply NatTrans.ext
  funext t
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  by_cases hti : t ∈ (A i).support
  · exact app_eq_zero_of_not_le hij φ hti f
  · exact (show Subsingleton (((A i).rep k).obj t) from
      ⟨fun _ _ => funext fun x => absurd x.2 hti⟩).elim _ _

end ExtriangulatedRealization
