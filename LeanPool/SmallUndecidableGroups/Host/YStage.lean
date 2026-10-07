/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.FinalModel
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.InputsBridge

/-!
# The first compression HNN extension

This file formalizes Lemma 3.1 of the paper and the associated subgroup
isomorphism.  The ambient group `Gamma` is the semantic Borisov group.
The two associated subgroups are exactly

* `HMinus = ⟨d,e,c,t,s₁⟩`, and
* `HPlus  = ⟨d,e,c,k,s₂⟩`.

The subgroup isomorphism following Lemma 3.1 defines the proper `y`-stage
and its base embedding.  It is constructed below from restricted HNN extensions.
-/

@[expose] public section

namespace Undecidability
namespace HostYStage

open BorisovCStage
open BorisovConverseCore
open BorisovFinalModel
open BorisovG0HNN
open BorisovHNNModel
open BorisovInputsBridge
open HNNLemmas

noncomputable section

variable (datum : Thue.StandingDatum)

/-! ## The symmetry between `J₁` and `J₂`

The base change underlying the isomorphism following Lemma 3.1 is already
visible before adjoining `c`:
`d ↦ e⁻¹`, `e ↦ d`, `s₁ ↦ s₂⁻¹`.  We construct it as an
honest automorphism of the four-generator group `Gamma3`; its inverse sends
`d ↦ e`, `e ↦ d⁻¹` and has the same action on the stable letters.
-/

/-- The four generator images defining the twisting automorphism of the initial Borisov group. -/
def twistGenerator : Fin 4 → Gamma3 :=
  ![e3⁻¹, d3, secondStableInStageThree⁻¹, firstStableInStageThree⁻¹]

/-- The four generator images defining the inverse twisting automorphism. -/
def untwistGenerator : Fin 4 → Gamma3 :=
  ![e3, d3⁻¹, secondStableInStageThree⁻¹, firstStableInStageThree⁻¹]

private theorem stable_conjugates_d
    (s : Gamma3) (hs : d3 ^ 4 * s = s * d3) :
    s * d3 * s⁻¹ = d3 ^ 4 := by
  rw [← hs]
  simp

private theorem stable_conjugates_e_four
    (s : Gamma3) (hs : e3 * s = s * e3 ^ 4) :
    s * e3 ^ 4 * s⁻¹ = e3 := by
  rw [← hs]
  simp

private theorem stable_conjugates_e_inv_four
    (s : Gamma3) (hs : e3 * s = s * e3 ^ 4) :
    s * (e3⁻¹) ^ 4 * s⁻¹ = e3⁻¹ := by
  simpa [mul_inv_rev, inv_pow, mul_assoc] using
    congrArg Inv.inv (stable_conjugates_e_four s hs)

private theorem stable_conjugates_d_inv
    (s : Gamma3) (hs : d3 ^ 4 * s = s * d3) :
    s * d3⁻¹ * s⁻¹ = (d3⁻¹) ^ 4 := by
  simpa [mul_inv_rev, inv_pow, mul_assoc] using
    congrArg Inv.inv (stable_conjugates_d s hs)

theorem twist_relators :
    ∀ r ∈ BorisovIntersections.presentation.relSet,
      FreeGroup.lift twistGenerator r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s1Word, twistGenerator, mul_assoc] using
      stable_conjugates_e_inv_four secondStableInStageThree gamma3_e_mul_s2
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s1Word, twistGenerator, mul_assoc] using
      stable_conjugates_d secondStableInStageThree gamma3_d_four_mul_s2
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s2Word, twistGenerator, mul_assoc] using
      stable_conjugates_e_inv_four firstStableInStageThree gamma3_e_mul_s1
  · apply (Word.eval_relation_eq_one_iff twistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s2Word, twistGenerator, mul_assoc] using
      stable_conjugates_d firstStableInStageThree gamma3_d_four_mul_s1

theorem untwist_relators :
    ∀ r ∈ BorisovIntersections.presentation.relSet,
      FreeGroup.lift untwistGenerator r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s1Word, untwistGenerator, mul_assoc] using
      stable_conjugates_e_four secondStableInStageThree gamma3_e_mul_s2
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s1Word, untwistGenerator, mul_assoc] using
      stable_conjugates_d_inv secondStableInStageThree gamma3_d_four_mul_s2
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sDRelator, BorisovIntersections.dWord,
      BorisovIntersections.s2Word, untwistGenerator, mul_assoc] using
      stable_conjugates_e_four firstStableInStageThree gamma3_e_mul_s1
  · apply (Word.eval_relation_eq_one_iff untwistGenerator _ _).2
    simpa [BorisovIntersections.presentation,
      BorisovIntersections.sERelator, BorisovIntersections.eWord,
      BorisovIntersections.s2Word, untwistGenerator, mul_assoc] using
      stable_conjugates_d_inv firstStableInStageThree gamma3_d_four_mul_s1

/-- The twist interpreted as a homomorphism from the initial Borisov presentation. -/
def twistFromG0 : BorisovIntersections.G0 →* Gamma3 :=
  PresentedGroup.toGroup twist_relators

/-- The inverse twist interpreted as a homomorphism from the initial presentation. -/
def untwistFromG0 : BorisovIntersections.G0 →* Gamma3 :=
  PresentedGroup.toGroup untwist_relators

@[simp] private theorem twistFromG0_of (i : Fin 4) :
    twistFromG0 (PresentedGroup.of i) = twistGenerator i :=
  PresentedGroup.toGroup.of twist_relators

@[simp] private theorem untwistFromG0_of (i : Fin 4) :
    untwistFromG0 (PresentedGroup.of i) = untwistGenerator i :=
  PresentedGroup.toGroup.of untwist_relators

/-- The twisting endomorphism of the two-HNN-extension model. -/
def twistHom : Gamma3 →* Gamma3 :=
  twistFromG0.comp g0Equiv.symm.toMonoidHom

/-- The inverse twisting endomorphism of the two-HNN-extension model. -/
def untwistHom : Gamma3 →* Gamma3 :=
  untwistFromG0.comp g0Equiv.symm.toMonoidHom

private theorem gamma3_hom_ext {Q : Type*} [Group Q]
    {f g : Gamma3 →* Q}
    (hd : f d3 = g d3) (he : f e3 = g e3)
    (hs1 : f firstStableInStageThree = g firstStableInStageThree)
    (hs2 : f secondStableInStageThree = g secondStableInStageThree) : f = g := by
  apply HNNExtension.hom_ext
  · apply HNNExtension.hom_ext
    · apply FreeGroup.ext_hom
      intro i
      fin_cases i
      · exact hd
      · exact he
    · exact hs1
  · exact hs2

@[simp] theorem twistHom_d3 : twistHom d3 = e3⁻¹ := by
  change twistFromG0 (fromHNN hnnD) = _
  rw [fromHNN_hnnD, presentedD_eq_of, twistFromG0_of]
  rfl

@[simp] theorem twistHom_e3 : twistHom e3 = d3 := by
  change twistFromG0 (fromHNN hnnE) = _
  rw [fromHNN_hnnE, presentedE_eq_of, twistFromG0_of]
  rfl

@[simp] theorem twistHom_s1_3 : twistHom firstStableInStageThree = secondStableInStageThree⁻¹ := by
  change twistFromG0 (fromHNN hnnS1) = _
  rw [fromHNN_hnnS1, presentedS1_eq_of, twistFromG0_of]
  rfl

@[simp] theorem twistHom_s2_3 : twistHom secondStableInStageThree = firstStableInStageThree⁻¹ := by
  change twistFromG0 (fromHNN hnnS2) = _
  rw [fromHNN_hnnS2, presentedS2_eq_of, twistFromG0_of]
  rfl

@[simp] theorem untwistHom_d3 : untwistHom d3 = e3 := by
  change untwistFromG0 (fromHNN hnnD) = _
  rw [fromHNN_hnnD, presentedD_eq_of, untwistFromG0_of]
  rfl

@[simp] theorem untwistHom_e3 : untwistHom e3 = d3⁻¹ := by
  change untwistFromG0 (fromHNN hnnE) = _
  rw [fromHNN_hnnE, presentedE_eq_of, untwistFromG0_of]
  rfl

@[simp] theorem untwistHom_s1_3 :
    untwistHom firstStableInStageThree = secondStableInStageThree⁻¹ := by
  change untwistFromG0 (fromHNN hnnS1) = _
  rw [fromHNN_hnnS1, presentedS1_eq_of, untwistFromG0_of]
  rfl

@[simp] theorem untwistHom_s2_3 :
    untwistHom secondStableInStageThree = firstStableInStageThree⁻¹ := by
  change untwistFromG0 (fromHNN hnnS2) = _
  rw [fromHNN_hnnS2, presentedS2_eq_of, untwistFromG0_of]
  rfl

theorem untwist_comp_twist :
    untwistHom.comp twistHom = MonoidHom.id Gamma3 := by
  apply gamma3_hom_ext <;> simp

theorem twist_comp_untwist :
    twistHom.comp untwistHom = MonoidHom.id Gamma3 := by
  apply gamma3_hom_ext <;> simp

theorem twist_mem_J3 {x : Gamma3} (hx : x ∈ J3 0) :
    twistHom x ∈ J3 1 := by
  let K : Subgroup Gamma3 := (J3 1).comap twistHom
  have hle : J3 0 ≤ K := by
    rw [J3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · change twistHom d3 ∈ J3 1
      rw [twistHom_d3]
      exact (J3 1).inv_mem (Subgroup.subset_closure (by simp))
    · change twistHom e3 ∈ J3 1
      rw [twistHom_e3]
      exact Subgroup.subset_closure (by simp)
    · change twistHom (stable3 0) ∈ J3 1
      rw [show stable3 0 = firstStableInStageThree by rfl, twistHom_s1_3]
      exact (J3 1).inv_mem (Subgroup.subset_closure (by simp [stable3]))
  exact hle hx

theorem untwist_mem_J3 {x : Gamma3} (hx : x ∈ J3 1) :
    untwistHom x ∈ J3 0 := by
  let K : Subgroup Gamma3 := (J3 0).comap untwistHom
  have hle : J3 1 ≤ K := by
    rw [J3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · change untwistHom d3 ∈ J3 0
      rw [untwistHom_d3]
      exact Subgroup.subset_closure (by simp)
    · change untwistHom e3 ∈ J3 0
      rw [untwistHom_e3]
      exact (J3 0).inv_mem (Subgroup.subset_closure (by simp))
    · change untwistHom (stable3 1) ∈ J3 0
      rw [show stable3 1 = secondStableInStageThree by rfl, untwistHom_s2_3]
      exact (J3 0).inv_mem (Subgroup.subset_closure (by simp [stable3]))
  exact hle hx

/-- The base isomorphism `J₁ ≃ J₂` used by the restricted `c`-HNN
extensions. -/
def jEquiv : J3 0 ≃* J3 1 where
  toFun x := ⟨twistHom x, twist_mem_J3 x.property⟩
  invFun x := ⟨untwistHom x, untwist_mem_J3 x.property⟩
  left_inv x := Subtype.ext (DFunLike.congr_fun untwist_comp_twist (x : Gamma3))
  right_inv x := Subtype.ext (DFunLike.congr_fun twist_comp_untwist (x : Gamma3))
  map_mul' x y := Subtype.ext (map_mul twistHom (x : Gamma3) (y : Gamma3))

private theorem twist_mem_stableCyclic {x : Gamma3}
    (hx : x ∈ stableCyclic3 0) :
    twistHom x ∈ stableCyclic3 1 := by
  rcases Subgroup.mem_closure_singleton.mp hx with ⟨n, hn⟩
  rw [← hn, map_zpow, show stable3 0 = firstStableInStageThree by rfl, twistHom_s1_3]
  exact (stableCyclic3 1).zpow_mem
    ((stableCyclic3 1).inv_mem
      (Subgroup.subset_closure (Set.mem_singleton (stable3 1)))) n

private theorem untwist_mem_stableCyclic {x : Gamma3}
    (hx : x ∈ stableCyclic3 1) :
    untwistHom x ∈ stableCyclic3 0 := by
  rcases Subgroup.mem_closure_singleton.mp hx with ⟨n, hn⟩
  rw [← hn, map_zpow, show stable3 1 = secondStableInStageThree by rfl, untwistHom_s2_3]
  exact (stableCyclic3 0).zpow_mem
    ((stableCyclic3 0).inv_mem
      (Subgroup.subset_closure (Set.mem_singleton (stable3 0)))) n

theorem twist_mem_U {x : Gamma3}
    (hxU : x ∈ U datum) (hxJ : x ∈ J3 0) : twistHom x ∈ U datum := by
  apply stableCyclic3_le_U datum 1
  apply twist_mem_stableCyclic
  rw [← U_inf_J3 datum 0]
  exact ⟨hxU, hxJ⟩

theorem untwist_mem_U {x : Gamma3}
    (hxU : x ∈ U datum) (hxJ : x ∈ J3 1) : untwistHom x ∈ U datum := by
  apply stableCyclic3_le_U datum 0
  apply untwist_mem_stableCyclic
  rw [← U_inf_J3 datum 1]
  exact ⟨hxU, hxJ⟩

theorem twist_mem_V {x : Gamma3}
    (hxV : x ∈ V datum) (hxJ : x ∈ J3 0) : twistHom x ∈ V datum := by
  apply stableCyclic3_le_V datum 1
  apply twist_mem_stableCyclic
  rw [← V_inf_J3 datum 0]
  exact ⟨hxV, hxJ⟩

theorem untwist_mem_V {x : Gamma3}
    (hxV : x ∈ V datum) (hxJ : x ∈ J3 1) : untwistHom x ∈ V datum := by
  apply stableCyclic3_le_V datum 0
  apply untwist_mem_stableCyclic
  rw [← V_inf_J3 datum 1]
  exact ⟨hxV, hxJ⟩

/-- The source rule subgroup restricted to the selected three-generator subgroup. -/
abbrev CRestrictedA (beta : Fin 2) :=
  restrictedA (A := U datum) (J3 beta)

/-- The target rule subgroup restricted to the selected three-generator subgroup. -/
abbrev CRestrictedB (beta : Fin 2) :=
  restrictedB (B := V datum) (J3 beta)

/-- The rewriting-rule subgroup isomorphism restricted to the selected base subgroup. -/
def cRestrictedPhi (beta : Fin 2) :
    CRestrictedA datum beta ≃* CRestrictedB datum beta :=
  restrictedPhi (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)

/-- The exact restricted `c`-HNN extension over `J_beta`. -/
abbrev CRestricted (beta : Fin 2) :=
  HNNExtension (J3 beta) (CRestrictedA datum beta) (CRestrictedB datum beta)
    (cRestrictedPhi datum beta)

/-- The twisting equivalence between the two restricted source rule subgroups. -/
def cRestrictedAEquiv :
    CRestrictedA datum 0 ≃* CRestrictedA datum 1 where
  toFun a :=
    ⟨jEquiv (a : J3 0),
      twist_mem_U datum a.property (a : J3 0).property⟩
  invFun a :=
    ⟨(jEquiv).symm (a : J3 1),
      untwist_mem_U datum a.property (a : J3 1).property⟩
  left_inv a := Subtype.ext ((jEquiv).symm_apply_apply (a : J3 0))
  right_inv a := Subtype.ext ((jEquiv).apply_symm_apply (a : J3 1))
  map_mul' a b := Subtype.ext (map_mul jEquiv (a : J3 0) (b : J3 0))

/-- The twisting equivalence between the two restricted target rule subgroups. -/
def cRestrictedBEquiv :
    CRestrictedB datum 0 ≃* CRestrictedB datum 1 where
  toFun b :=
    ⟨jEquiv (b : J3 0),
      twist_mem_V datum b.property (b : J3 0).property⟩
  invFun b :=
    ⟨(jEquiv).symm (b : J3 1),
      untwist_mem_V datum b.property (b : J3 1).property⟩
  left_inv b := Subtype.ext ((jEquiv).symm_apply_apply (b : J3 0))
  right_inv b := Subtype.ext ((jEquiv).apply_symm_apply (b : J3 1))
  map_mul' a b := Subtype.ext (map_mul jEquiv (a : J3 0) (b : J3 0))

private theorem cEquiv_eq_on_J (beta : Fin 2) (a : U datum)
    (haJ : (a : Gamma3) ∈ J3 beta) :
    (cEquiv datum (rankFiveFree datum) a : Gamma3) = (a : Gamma3) := by
  have haC : (a : Gamma3) ∈ stableCyclic3 beta := by
    rw [← U_inf_J3 datum beta]
    exact ⟨a.property, haJ⟩
  rcases Subgroup.mem_closure_singleton.mp haC with ⟨n, hn⟩
  have ha : a = (uStable datum beta) ^ n := Subtype.ext hn.symm
  rw [ha, map_zpow]
  change
    (cEquiv datum (rankFiveFree datum) (uStable datum beta) : Gamma3) ^ n =
      (stable3 beta) ^ n
  rw [cEquiv_uStable]

theorem cRestricted_intertwines (a : CRestrictedA datum 0) :
    cRestrictedBEquiv datum (cRestrictedPhi datum 0 a) =
      cRestrictedPhi datum 1 (cRestrictedAEquiv datum a) := by
  apply Subtype.ext
  apply Subtype.ext
  change
    twistHom
        (cEquiv datum (rankFiveFree datum)
          (⟨((a : J3 0) : Gamma3), a.property⟩ : U datum) : Gamma3) =
      (cEquiv datum (rankFiveFree datum)
          (⟨twistHom ((a : J3 0) : Gamma3),
            twist_mem_U datum a.property (a : J3 0).property⟩ : U datum) : Gamma3)
  rw [cEquiv_eq_on_J datum 0 _ (a : J3 0).property]
  rw [cEquiv_eq_on_J datum 1 _
    (twist_mem_J3 (a : J3 0).property)]

/-- The exact `c`-stage symmetry, obtained by transporting both restricted
associated subgroups along `jEquiv`. -/
def cRestrictedEquiv : CRestricted datum 0 ≃* CRestricted datum 1 :=
  HNNLemmas.congr jEquiv (cRestrictedAEquiv datum) (cRestrictedBEquiv datum)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (cRestricted_intertwines datum)

@[simp] private theorem cRestrictedEquiv_of (x : J3 0) :
    cRestrictedEquiv datum (HNNExtension.of x) =
      HNNExtension.of (jEquiv x) := rfl

@[simp] private theorem cRestrictedEquiv_t :
    cRestrictedEquiv datum
        (HNNExtension.t : CRestricted datum 0) =
      (HNNExtension.t : CRestricted datum 1) := rfl

/-- The exact subgroup `⟨d,e,c,s_beta⟩` of `Gamma2`. -/
def CSubgroup (beta : Fin 2) : Subgroup (Gamma2 datum (rankFiveFree datum)) :=
  generatedWithStable (A := U datum) (B := V datum)
    (phi := cEquiv datum (rankFiveFree datum)) (J3 beta)

/-- The equivalence from the restricted HNN model onto its generated subgroup. -/
def cRestrictedRangeEquiv (beta : Fin 2) :
    CRestricted datum beta ≃* CSubgroup datum beta :=
  restrictedEquivGeneratedWithStable (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)

@[simp] private theorem cRestrictedRangeEquiv_of_coe
    (beta : Fin 2) (x : J3 beta) :
    ((cRestrictedRangeEquiv datum beta (HNNExtension.of x) :
        CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum)) =
      of3 datum (rankFiveFree datum) (x : Gamma3) := by
  change _ = (HNNExtension.of (x : Gamma3) :
    HNNExtension Gamma3 (U datum) (V datum)
      (cEquiv datum (rankFiveFree datum)))
  exact restrictedEquivGeneratedWithStable_coe (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)
    (HNNExtension.of x)

@[simp] private theorem cRestrictedRangeEquiv_t_coe (beta : Fin 2) :
    ((cRestrictedRangeEquiv datum beta
        (HNNExtension.t : CRestricted datum beta) : CSubgroup datum beta) :
      Gamma2 datum (rankFiveFree datum)) = HNNExtension.t := by
  change _ = (HNNExtension.t :
    HNNExtension Gamma3 (U datum) (V datum)
      (cEquiv datum (rankFiveFree datum)))
  exact restrictedEquivGeneratedWithStable_coe (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)
    (HNNExtension.t : CRestricted datum beta)

private theorem cRestrictedRangeEquiv_inv_t_coe (beta : Fin 2) :
    ((cRestrictedRangeEquiv datum beta
        ((HNNExtension.t : CRestricted datum beta)⁻¹) :
      CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum)) =
      BorisovCStage.c datum (rankFiveFree datum) := by
  change
    ((cRestrictedRangeEquiv datum beta
        ((HNNExtension.t : CRestricted datum beta)⁻¹) :
      CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum)) =
      (HNNExtension.t : Gamma2 datum (rankFiveFree datum))⁻¹
  rw [map_inv]
  exact congrArg Inv.inv (cRestrictedRangeEquiv_t_coe datum beta)

/-- The induced isomorphism
`⟨d,e,c,s₁⟩ ≃ ⟨d,e,c,s₂⟩`. -/
def cSubgroupEquiv : CSubgroup datum 0 ≃* CSubgroup datum 1 :=
  (cRestrictedRangeEquiv datum 0).symm.trans
    ((cRestrictedEquiv datum).trans (cRestrictedRangeEquiv datum 1))

theorem d3_mem_J3 (beta : Fin 2) : d3 ∈ J3 beta :=
  Subgroup.subset_closure (by simp)

theorem e3_mem_J3 (beta : Fin 2) : e3 ∈ J3 beta :=
  Subgroup.subset_closure (by simp)

theorem stable3_mem_J3 (beta : Fin 2) : stable3 beta ∈ J3 beta :=
  Subgroup.subset_closure (by simp)

/-- The generator `d` regarded as an element of the selected core subgroup. -/
def coreD (beta : Fin 2) : CSubgroup datum beta :=
  ⟨of3 datum (rankFiveFree datum) d3,
    Subgroup.subset_closure (Or.inl ⟨d3, d3_mem_J3 beta, rfl⟩)⟩

/-- The generator `e` regarded as an element of the selected core subgroup. -/
def coreE (beta : Fin 2) : CSubgroup datum beta :=
  ⟨of3 datum (rankFiveFree datum) e3,
    Subgroup.subset_closure (Or.inl ⟨e3, e3_mem_J3 beta, rfl⟩)⟩

/-- The selected stable generator regarded as an element of the core subgroup. -/
def coreStable (beta : Fin 2) : CSubgroup datum beta :=
  ⟨of3 datum (rankFiveFree datum) (stable3 beta),
    Subgroup.subset_closure
      (Or.inl ⟨stable3 beta, stable3_mem_J3 beta, rfl⟩)⟩

/-- The generator `c` regarded as an element of the core subgroup. -/
def coreC (beta : Fin 2) : CSubgroup datum beta :=
  ⟨BorisovCStage.c datum (rankFiveFree datum),
    (CSubgroup datum beta).inv_mem
      (Subgroup.subset_closure (Or.inr (Set.mem_singleton _)))⟩

private theorem cRestrictedRangeEquiv_symm_of (beta : Fin 2) (x : J3 beta) :
    (cRestrictedRangeEquiv datum beta).symm
        ⟨of3 datum (rankFiveFree datum) (x : Gamma3),
          Subgroup.subset_closure (Or.inl ⟨x, x.property, rfl⟩)⟩ =
      HNNExtension.of x := by
  apply (cRestrictedRangeEquiv datum beta).injective
  rw [(cRestrictedRangeEquiv datum beta).apply_symm_apply]
  apply Subtype.ext
  exact (restrictedEquivGeneratedWithStable_coe (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)
    (HNNExtension.of x)).symm

private theorem cRestrictedRangeEquiv_symm_c (beta : Fin 2) :
    (cRestrictedRangeEquiv datum beta).symm (coreC datum beta) =
      (HNNExtension.t : CRestricted datum beta)⁻¹ := by
  apply (cRestrictedRangeEquiv datum beta).injective
  rw [(cRestrictedRangeEquiv datum beta).apply_symm_apply]
  apply Subtype.ext
  change
    BorisovCStage.c datum (rankFiveFree datum) =
      ((cRestrictedRangeEquiv datum beta
          ((HNNExtension.t : CRestricted datum beta)⁻¹) :
        CSubgroup datum beta) : Gamma2 datum (rankFiveFree datum))
  exact (cRestrictedRangeEquiv_inv_t_coe datum beta).symm

private theorem cRestrictedRangeEquiv_symm_coreD :
    (cRestrictedRangeEquiv datum 0).symm (coreD datum 0) =
      HNNExtension.of (⟨d3, d3_mem_J3 0⟩ : J3 0) := by
  simpa [coreD] using cRestrictedRangeEquiv_symm_of datum 0
    (⟨d3, d3_mem_J3 0⟩ : J3 0)

private theorem cRestrictedRangeEquiv_symm_coreE :
    (cRestrictedRangeEquiv datum 0).symm (coreE datum 0) =
      HNNExtension.of (⟨e3, e3_mem_J3 0⟩ : J3 0) := by
  simpa [coreE] using cRestrictedRangeEquiv_symm_of datum 0
    (⟨e3, e3_mem_J3 0⟩ : J3 0)

private theorem cRestrictedRangeEquiv_symm_coreStable :
    (cRestrictedRangeEquiv datum 0).symm (coreStable datum 0) =
      HNNExtension.of (⟨stable3 0, stable3_mem_J3 0⟩ : J3 0) := by
  simpa [coreStable] using cRestrictedRangeEquiv_symm_of datum 0
    (⟨stable3 0, stable3_mem_J3 0⟩ : J3 0)

@[simp] theorem cSubgroupEquiv_coreD :
    cSubgroupEquiv datum (coreD datum 0) = (coreE datum 1)⁻¹ := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_coreD]
  change
    cRestrictedRangeEquiv datum 1
        (cRestrictedEquiv datum (HNNExtension.of
          (⟨d3, d3_mem_J3 0⟩ : J3 0))) = _
  rw [cRestrictedEquiv_of]
  apply Subtype.ext
  rw [cRestrictedRangeEquiv_of_coe]
  simp [coreE, jEquiv]

@[simp] theorem cSubgroupEquiv_coreE :
    cSubgroupEquiv datum (coreE datum 0) = coreD datum 1 := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_coreE]
  change
    cRestrictedRangeEquiv datum 1
        (cRestrictedEquiv datum (HNNExtension.of
          (⟨e3, e3_mem_J3 0⟩ : J3 0))) = _
  rw [cRestrictedEquiv_of]
  apply Subtype.ext
  rw [cRestrictedRangeEquiv_of_coe]
  simp [coreD, jEquiv]

@[simp] theorem cSubgroupEquiv_coreC :
    cSubgroupEquiv datum (coreC datum 0) = coreC datum 1 := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_c]
  rw [map_inv, cRestrictedEquiv_t]
  apply Subtype.ext
  rw [map_inv]
  simp [coreC, BorisovCStage.c]

@[simp] theorem cSubgroupEquiv_coreS1 :
    cSubgroupEquiv datum (coreStable datum 0) = (coreStable datum 1)⁻¹ := by
  simp only [cSubgroupEquiv, MulEquiv.trans_apply]
  rw [cRestrictedRangeEquiv_symm_coreStable]
  change
    cRestrictedRangeEquiv datum 1
        (cRestrictedEquiv datum (HNNExtension.of
          (⟨stable3 0, stable3_mem_J3 0⟩ : J3 0))) = _
  rw [cRestrictedEquiv_of]
  apply Subtype.ext
  rw [cRestrictedRangeEquiv_of_coe]
  simp [coreStable, jEquiv, stable3]

private theorem CD_le_CSubgroup :
    CD datum (rankFiveFree datum) ≤ CSubgroup datum 0 := by
  rw [CD, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact (coreC datum 0).property
  · exact (coreD datum 0).property

private theorem CE_le_CSubgroup :
    CE datum (rankFiveFree datum) ≤ CSubgroup datum 1 := by
  rw [CE, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact (coreC datum 1).property
  · exact (coreE datum 1).property

private theorem map_mem_of_mem_closure
    {G H : Type*} [Group G] [Group H] {S : Subgroup G} {s : Set G}
    (hs : Subgroup.closure s ≤ S) (f : S →* H) (T : Subgroup H)
    (hgen : ∀ x : S, (x : G) ∈ s → f x ∈ T)
    {x : S} (hx : (x : G) ∈ Subgroup.closure s) : f x ∈ T := by
  have hclosure : Subgroup.closure s ≤ (T.comap f).map S.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, hs (Subgroup.subset_closure hg)⟩, hgen _ hg, rfl⟩
  rcases hclosure hx with ⟨y, hy, heq⟩
  exact (Subtype.ext heq : y = x) ▸ hy

private theorem cSubgroupEquiv_mem_CE_of_mem_CD (x : CSubgroup datum 0)
    (hx : (x : Gamma2 datum (rankFiveFree datum)) ∈
      CD datum (rankFiveFree datum)) :
    ((cSubgroupEquiv datum x : CSubgroup datum 1) :
      Gamma2 datum (rankFiveFree datum)) ∈ CE datum (rankFiveFree datum) := by
  apply map_mem_of_mem_closure (CD_le_CSubgroup datum)
    ((CSubgroup datum 1).subtype.comp (cSubgroupEquiv datum).toMonoidHom)
    (CE datum (rankFiveFree datum)) ?_ hx
  intro y hy
  change ((cSubgroupEquiv datum y : CSubgroup datum 1) :
    Gamma2 datum (rankFiveFree datum)) ∈ CE datum (rankFiveFree datum)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hc | hd
  · have heq : y = coreC datum 0 := Subtype.ext hc
    rw [heq, cSubgroupEquiv_coreC]
    apply Subgroup.subset_closure
    simp [coreC]
  · have heq : y = coreD datum 0 := Subtype.ext hd
    rw [heq, cSubgroupEquiv_coreD]
    apply (CE datum (rankFiveFree datum)).inv_mem
    apply Subgroup.subset_closure
    simp [coreE]

private theorem cSubgroupEquiv_symm_coreC :
    (cSubgroupEquiv datum).symm (coreC datum 1) = coreC datum 0 := by
  apply (cSubgroupEquiv datum).injective
  rw [(cSubgroupEquiv datum).apply_symm_apply, cSubgroupEquiv_coreC]

private theorem cSubgroupEquiv_symm_coreE :
    (cSubgroupEquiv datum).symm (coreE datum 1) = (coreD datum 0)⁻¹ := by
  apply (cSubgroupEquiv datum).injective
  rw [(cSubgroupEquiv datum).apply_symm_apply, map_inv,
    cSubgroupEquiv_coreD]
  simp

private theorem cSubgroupEquiv_symm_mem_CD_of_mem_CE
    (x : CSubgroup datum 1)
    (hx : (x : Gamma2 datum (rankFiveFree datum)) ∈
      CE datum (rankFiveFree datum)) :
    (((cSubgroupEquiv datum).symm x : CSubgroup datum 0) :
      Gamma2 datum (rankFiveFree datum)) ∈ CD datum (rankFiveFree datum) := by
  apply map_mem_of_mem_closure (CE_le_CSubgroup datum)
    ((CSubgroup datum 0).subtype.comp (cSubgroupEquiv datum).symm.toMonoidHom)
    (CD datum (rankFiveFree datum)) ?_ hx
  intro y hy
  change (((cSubgroupEquiv datum).symm y : CSubgroup datum 0) :
    Gamma2 datum (rankFiveFree datum)) ∈ CD datum (rankFiveFree datum)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with hc | he
  · have heq : y = coreC datum 1 := Subtype.ext hc
    rw [heq, cSubgroupEquiv_symm_coreC]
    apply Subgroup.subset_closure
    simp [coreC]
  · have heq : y = coreE datum 1 := Subtype.ext he
    rw [heq, cSubgroupEquiv_symm_coreE]
    apply (CD datum (rankFiveFree datum)).inv_mem
    apply Subgroup.subset_closure
    simp [coreD]

theorem cSubgroupEquiv_mem_CD_iff (x : CSubgroup datum 0) :
    (x : Gamma2 datum (rankFiveFree datum)) ∈ CD datum (rankFiveFree datum) ↔
      ((cSubgroupEquiv datum x : CSubgroup datum 1) :
        Gamma2 datum (rankFiveFree datum)) ∈ CE datum (rankFiveFree datum) := by
  constructor
  · exact cSubgroupEquiv_mem_CE_of_mem_CD datum x
  · intro hx
    have h := cSubgroupEquiv_symm_mem_CD_of_mem_CE datum
      (cSubgroupEquiv datum x) hx
    rw [(cSubgroupEquiv datum).symm_apply_apply] at h
    exact h

/-! ## The outer `t`/`k` restricted HNN extensions -/

theorem toTStage_injective :
    Function.Injective (toTStage datum (rankFiveFree datum)) :=
  HNNExtension.of_injective (MulEquiv.refl (CD datum (rankFiveFree datum)))

/-- The plus-side four-generator base, embedded in the `t`-stage. -/
def PlusBase : Subgroup (TStage datum (rankFiveFree datum)) :=
  (CSubgroup datum 1).map (toTStage datum (rankFiveFree datum))

/-- The equivalence carrying the positive core subgroup into the final-stage base group. -/
def cSubgroupToPlusBase :
    CSubgroup datum 1 ≃* PlusBase datum :=
  (CSubgroup datum 1).equivMapOfInjective
    (toTStage datum (rankFiveFree datum)) (toTStage_injective datum)

/-- The base equivalence for the outer HNN congruence. -/
def outerBaseEquiv : CSubgroup datum 0 ≃* PlusBase datum :=
  (cSubgroupEquiv datum).trans (cSubgroupToPlusBase datum)

@[simp] theorem outerBaseEquiv_coe (x : CSubgroup datum 0) :
    ((outerBaseEquiv datum x : PlusBase datum) :
      TStage datum (rankFiveFree datum)) =
      toTStage datum (rankFiveFree datum)
        ((cSubgroupEquiv datum x : CSubgroup datum 1) :
          Gamma2 datum (rankFiveFree datum)) := rfl

private theorem mapped_CE_le_KSubgroup :
    (CE datum (rankFiveFree datum)).map (toTStage datum (rankFiveFree datum)) ≤
      KSubgroup datum (rankFiveFree datum) :=
  fun _ hx ↦ Subgroup.subset_closure (Or.inl hx)

private theorem toTStage_mem_KSubgroup_iff (x : CSubgroup datum 1) :
    toTStage datum (rankFiveFree datum)
        (x : Gamma2 datum (rankFiveFree datum)) ∈
          KSubgroup datum (rankFiveFree datum) ↔
      (x : Gamma2 datum (rankFiveFree datum)) ∈
        CE datum (rankFiveFree datum) := by
  constructor
  · intro hxK
    change
      centralizerOf (CD datum (rankFiveFree datum))
          (x : Gamma2 datum (rankFiveFree datum)) ∈
        generatedWith
          ((CE datum (rankFiveFree datum)).map
            (centralizerOf (CD datum (rankFiveFree datum))))
          (conjugatedStable (CD datum (rankFiveFree datum))
            (positive2 datum (rankFiveFree datum) datum.P)) at hxK
    have hxInter :
        centralizerOf (CD datum (rankFiveFree datum))
            (x : Gamma2 datum (rankFiveFree datum)) ∈
          (CE datum (rankFiveFree datum)).map
            (centralizerOf (CD datum (rankFiveFree datum))) := by
      have h := generatedWith_conjugatedStable_inf_base
        (CE datum (rankFiveFree datum)) (CD datum (rankFiveFree datum))
        (positive2 datum (rankFiveFree datum) datum.P)
      rw [← h]
      constructor
      · exact hxK
      · exact ⟨(x : Gamma2 datum (rankFiveFree datum)), rfl⟩
    rcases hxInter with ⟨g, hg, hgx⟩
    have hgx' : (g : Gamma2 datum (rankFiveFree datum)) =
        (x : Gamma2 datum (rankFiveFree datum)) :=
      toTStage_injective datum hgx
    exact hgx' ▸ hg
  · intro hxCE
    apply mapped_CE_le_KSubgroup datum
    exact ⟨(x : Gamma2 datum (rankFiveFree datum)), hxCE, rfl⟩

theorem outerBaseEquiv_mem_associated_iff (x : CSubgroup datum 0) :
    (x : Gamma2 datum (rankFiveFree datum)) ∈
        CD datum (rankFiveFree datum) ↔
      ((outerBaseEquiv datum x : PlusBase datum) :
        TStage datum (rankFiveFree datum)) ∈
        KSubgroup datum (rankFiveFree datum) := by
  rw [outerBaseEquiv_coe, toTStage_mem_KSubgroup_iff,
    cSubgroupEquiv_mem_CD_iff]

theorem minusCompatibility
    (a : CD datum (rankFiveFree datum)) :
    (a : Gamma2 datum (rankFiveFree datum)) ∈ CSubgroup datum 0 ↔
      ((MulEquiv.refl (CD datum (rankFiveFree datum))) a :
        Gamma2 datum (rankFiveFree datum)) ∈ CSubgroup datum 0 :=
  Iff.rfl

theorem plusCompatibility
    (a : KSubgroup datum (rankFiveFree datum)) :
    (a : TStage datum (rankFiveFree datum)) ∈ PlusBase datum ↔
      ((MulEquiv.refl (KSubgroup datum (rankFiveFree datum))) a :
        TStage datum (rankFiveFree datum)) ∈ PlusBase datum :=
  Iff.rfl

/-- The first centralizer-associated subgroup restricted to the negative core subgroup. -/
abbrev MinusA :=
  restrictedA (A := CD datum (rankFiveFree datum)) (CSubgroup datum 0)

/-- The second centralizer-associated subgroup restricted to the negative core subgroup. -/
abbrev MinusB :=
  restrictedB (B := CD datum (rankFiveFree datum)) (CSubgroup datum 0)

/-- The centralizer-subgroup isomorphism restricted to the negative core subgroup. -/
def minusPhi : MinusA datum ≃* MinusB datum :=
  restrictedPhi (CSubgroup datum 0) (minusCompatibility datum)

/-- Exact parameter group for `⟨d,e,c,t,s₁⟩` before its inclusion in
the final `k`-stage. -/
abbrev MinusRestricted :=
  HNNExtension (CSubgroup datum 0) (MinusA datum) (MinusB datum)
    (minusPhi datum)

/-- The first final-stage associated subgroup restricted to the positive base subgroup. -/
abbrev PlusA :=
  restrictedA (A := KSubgroup datum (rankFiveFree datum)) (PlusBase datum)

/-- The second final-stage associated subgroup restricted to the positive base subgroup. -/
abbrev PlusB :=
  restrictedB (B := KSubgroup datum (rankFiveFree datum)) (PlusBase datum)

/-- The final-stage associated-subgroup isomorphism restricted to the positive base. -/
def plusPhi : PlusA datum ≃* PlusB datum :=
  restrictedPhi (PlusBase datum) (plusCompatibility datum)

/-- Exact parameter group for `⟨d,e,c,k,s₂⟩`. -/
abbrev PlusRestricted :=
  HNNExtension (PlusBase datum) (PlusA datum) (PlusB datum) (plusPhi datum)

/-- The equivalence of the outer associated subgroups induced by the twisting base equivalence. -/
def outerAssociatedEquiv : MinusA datum ≃* PlusA datum where
  toFun a :=
    ⟨outerBaseEquiv datum (a : CSubgroup datum 0),
      (outerBaseEquiv_mem_associated_iff datum (a : CSubgroup datum 0)).mp
        a.property⟩
  invFun b :=
    ⟨(outerBaseEquiv datum).symm (b : PlusBase datum),
      (outerBaseEquiv_mem_associated_iff datum
        ((outerBaseEquiv datum).symm (b : PlusBase datum))).mpr (by
          rw [(outerBaseEquiv datum).apply_symm_apply]
          exact b.property)⟩
  left_inv a :=
    Subtype.ext ((outerBaseEquiv datum).symm_apply_apply (a : CSubgroup datum 0))
  right_inv b :=
    Subtype.ext ((outerBaseEquiv datum).apply_symm_apply (b : PlusBase datum))
  map_mul' a b :=
    Subtype.ext (map_mul (outerBaseEquiv datum) (a : CSubgroup datum 0)
      (b : CSubgroup datum 0))

theorem outerRestricted_intertwines (a : MinusA datum) :
    outerAssociatedEquiv datum (minusPhi datum a) =
      plusPhi datum (outerAssociatedEquiv datum a) := rfl

/-- The isomorphism of the exact restricted outer HNN extensions, fixing the
stable-letter orientation (`t ↦ k`). -/
def outerRestrictedEquiv : MinusRestricted datum ≃* PlusRestricted datum :=
  HNNLemmas.congr (outerBaseEquiv datum)
    (outerAssociatedEquiv datum) (outerAssociatedEquiv datum)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (outerRestricted_intertwines datum)

@[simp] private theorem outerRestrictedEquiv_of (x : CSubgroup datum 0) :
    outerRestrictedEquiv datum (HNNExtension.of x) =
      HNNExtension.of (outerBaseEquiv datum x) := rfl

@[simp] private theorem outerRestrictedEquiv_t :
    outerRestrictedEquiv datum
        (HNNExtension.t : MinusRestricted datum) =
      (HNNExtension.t : PlusRestricted datum) := rfl

/-- The embedding of the negative restricted model into the `t` HNN stage. -/
def minusEmbeddingToT :
    MinusRestricted datum →* TStage datum (rankFiveFree datum) :=
  restrictedEmbedding (CSubgroup datum 0) (minusCompatibility datum)

/-- The embedding of the positive restricted model into the final HNN stage. -/
def plusEmbedding :
    PlusRestricted datum →* FinalStage datum (rankFiveFree datum) :=
  restrictedEmbedding (PlusBase datum) (plusCompatibility datum)

/-- The embedding of the negative restricted model carried into the final HNN stage. -/
def minusEmbedding :
    MinusRestricted datum →* FinalStage datum (rankFiveFree datum) :=
  (toFinalStage datum (rankFiveFree datum)).comp (minusEmbeddingToT datum)

/-- The proved freeness witness supplying the concrete iterated-HNN model. -/
abbrev FreeInput : RankFiveFree datum := rankFiveFree datum

/-- The semantic Borisov group `Gamma`. -/
abbrev Gamma := FinalStage datum (FreeInput datum)

/-- The concrete generator `d` in the final Borisov model. -/
def d : Gamma datum := modelD datum (FreeInput datum)
/-- The concrete generator `e` in the final Borisov model. -/
def e : Gamma datum := modelE datum (FreeInput datum)
/-- The concrete first stable generator in the final Borisov model. -/
def s1 : Gamma datum := modelS1 datum (FreeInput datum)
/-- The concrete second stable generator in the final Borisov model. -/
def s2 : Gamma datum := modelS2 datum (FreeInput datum)
/-- The concrete generator `c` in the final Borisov model. -/
def c : Gamma datum := modelC datum (FreeInput datum)
/-- The concrete generator `t` in the final Borisov model. -/
def t : Gamma datum := modelT datum (FreeInput datum)
/-- The concrete generator `k` in the final Borisov model. -/
def k : Gamma datum := modelK datum (FreeInput datum)

/-- `H_y^- = ⟨d,e,c,t,s₁⟩`. -/
def HMinus : Subgroup (Gamma datum) :=
  Subgroup.closure ({d datum, e datum, c datum, t datum, s1 datum} : Set (Gamma datum))

/-- `H_y^+ = ⟨d,e,c,k,s₂⟩`. -/
def HPlus : Subgroup (Gamma datum) :=
  Subgroup.closure ({d datum, e datum, c datum, k datum, s2 datum} : Set (Gamma datum))

@[simp] theorem d_mem_HMinus : d datum ∈ HMinus datum :=
  Subgroup.subset_closure (Or.inl rfl)

@[simp] theorem e_mem_HMinus : e datum ∈ HMinus datum :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

@[simp] theorem c_mem_HMinus : c datum ∈ HMinus datum :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))

@[simp] theorem t_mem_HMinus : t datum ∈ HMinus datum :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

@[simp] theorem s1_mem_HMinus : s1 datum ∈ HMinus datum :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

@[simp] theorem d_mem_HPlus : d datum ∈ HPlus datum :=
  Subgroup.subset_closure (Or.inl rfl)

@[simp] theorem e_mem_HPlus : e datum ∈ HPlus datum :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

@[simp] theorem c_mem_HPlus : c datum ∈ HPlus datum :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl)))

@[simp] theorem k_mem_HPlus : k datum ∈ HPlus datum :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

@[simp] theorem s2_mem_HPlus : s2 datum ∈ HPlus datum :=
  Subgroup.subset_closure (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private theorem J3_zero_to_HMinus {x : Gamma3} (hx : x ∈ J3 0) :
    cStageToFinal datum (rankFiveFree datum)
        (of3 datum (rankFiveFree datum) x) ∈ HMinus datum := by
  let L : Subgroup Gamma3 :=
    (HMinus datum).comap
      ((cStageToFinal datum (rankFiveFree datum)).comp
        (of3 datum (rankFiveFree datum)))
  have hle : J3 0 ≤ L := by
    rw [J3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact d_mem_HMinus datum
    · exact e_mem_HMinus datum
    · exact s1_mem_HMinus datum
  exact hle hx

private theorem J3_one_to_HPlus {x : Gamma3} (hx : x ∈ J3 1) :
    cStageToFinal datum (rankFiveFree datum)
        (of3 datum (rankFiveFree datum) x) ∈ HPlus datum := by
  let L : Subgroup Gamma3 :=
    (HPlus datum).comap
      ((cStageToFinal datum (rankFiveFree datum)).comp
        (of3 datum (rankFiveFree datum)))
  have hle : J3 1 ≤ L := by
    rw [J3, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact d_mem_HPlus datum
    · exact e_mem_HPlus datum
    · exact s2_mem_HPlus datum
  exact hle hx

private theorem CSubgroup_zero_to_HMinus (x : CSubgroup datum 0) :
    toFinalStage datum (rankFiveFree datum)
        (toTStage datum (rankFiveFree datum)
          (x : Gamma2 datum (rankFiveFree datum))) ∈ HMinus datum := by
  let f : Gamma2 datum (rankFiveFree datum) →* Gamma datum :=
    (toFinalStage datum (rankFiveFree datum)).comp
      (toTStage datum (rankFiveFree datum))
  let L : Subgroup (Gamma2 datum (rankFiveFree datum)) :=
    (HMinus datum).comap f
  have hle : CSubgroup datum 0 ≤ L := by
    rw [CSubgroup, generatedWithStable, Subgroup.closure_le]
    rintro _ (⟨g, hg, rfl⟩ | rfl)
    · exact J3_zero_to_HMinus datum hg
    · change
        toFinalStage datum (rankFiveFree datum)
            (toTStage datum (rankFiveFree datum)
              (HNNExtension.t : Gamma2 datum (rankFiveFree datum))) ∈
          HMinus datum
      have hc := (HMinus datum).inv_mem (c_mem_HMinus datum)
      simpa [c, modelC, cStageToFinal, BorisovCStage.c,
        toTStage, toFinalStage, map_inv] using hc
  exact hle x.property

private theorem CSubgroup_one_to_HPlus (x : CSubgroup datum 1) :
    toFinalStage datum (rankFiveFree datum)
        (toTStage datum (rankFiveFree datum)
          (x : Gamma2 datum (rankFiveFree datum))) ∈ HPlus datum := by
  let f : Gamma2 datum (rankFiveFree datum) →* Gamma datum :=
    (toFinalStage datum (rankFiveFree datum)).comp
      (toTStage datum (rankFiveFree datum))
  let L : Subgroup (Gamma2 datum (rankFiveFree datum)) :=
    (HPlus datum).comap f
  have hle : CSubgroup datum 1 ≤ L := by
    rw [CSubgroup, generatedWithStable, Subgroup.closure_le]
    rintro _ (⟨g, hg, rfl⟩ | rfl)
    · exact J3_one_to_HPlus datum hg
    · change
        toFinalStage datum (rankFiveFree datum)
            (toTStage datum (rankFiveFree datum)
              (HNNExtension.t : Gamma2 datum (rankFiveFree datum))) ∈
          HPlus datum
      have hc := (HPlus datum).inv_mem (c_mem_HPlus datum)
      simpa [c, modelC, cStageToFinal, BorisovCStage.c,
        toTStage, toFinalStage, map_inv] using hc
  exact hle x.property

/-- The generated subgroup on the minus side, still inside the `t`-stage. -/
def MinusGenerated : Subgroup (TStage datum (rankFiveFree datum)) :=
  generatedWithStable
    (A := CD datum (rankFiveFree datum))
    (B := CD datum (rankFiveFree datum))
    (phi := MulEquiv.refl (CD datum (rankFiveFree datum)))
    (CSubgroup datum 0)

/-- The generated subgroup on the plus side, inside the final `k`-stage. -/
def PlusGenerated : Subgroup (Gamma datum) :=
  generatedWithStable
    (A := KSubgroup datum (rankFiveFree datum))
    (B := KSubgroup datum (rankFiveFree datum))
    (phi := MulEquiv.refl (KSubgroup datum (rankFiveFree datum)))
    (PlusBase datum)

/-- The equivalence from the negative restricted HNN model onto its generated subgroup. -/
def minusRestrictedRangeEquiv :
    MinusRestricted datum ≃* MinusGenerated datum :=
  restrictedEquivGeneratedWithStable (CSubgroup datum 0)
    (minusCompatibility datum)

/-- The equivalence from the positive restricted HNN model onto its generated subgroup. -/
def plusRestrictedRangeEquiv :
    PlusRestricted datum ≃* PlusGenerated datum :=
  restrictedEquivGeneratedWithStable (PlusBase datum)
    (plusCompatibility datum)

theorem MinusGenerated_map_eq_HMinus :
    (MinusGenerated datum).map
        (toFinalStage datum (rankFiveFree datum)) = HMinus datum := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    rw [MinusGenerated, generatedWithStable, Subgroup.closure_le]
    rintro _ (⟨x, hx, rfl⟩ | rfl)
    · exact CSubgroup_zero_to_HMinus datum ⟨x, hx⟩
    · exact t_mem_HMinus datum
  · rw [HMinus, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl | rfl | rfl)
    · refine ⟨toTStage datum (rankFiveFree datum) (coreD datum 0), ?_, ?_⟩
      · apply Subgroup.subset_closure
        exact Or.inl ⟨coreD datum 0, (coreD datum 0).property, rfl⟩
      · rfl
    · refine ⟨toTStage datum (rankFiveFree datum) (coreE datum 0), ?_, ?_⟩
      · apply Subgroup.subset_closure
        exact Or.inl ⟨coreE datum 0, (coreE datum 0).property, rfl⟩
      · rfl
    · refine ⟨toTStage datum (rankFiveFree datum) (coreC datum 0), ?_, ?_⟩
      · apply Subgroup.subset_closure
        exact Or.inl ⟨coreC datum 0, (coreC datum 0).property, rfl⟩
      · rfl
    · refine ⟨HNNExtension.t, Subgroup.subset_closure (Or.inr rfl), ?_⟩
      rfl
    · refine
        ⟨toTStage datum (rankFiveFree datum) (coreStable datum 0), ?_, ?_⟩
      · apply Subgroup.subset_closure
        exact Or.inl
          ⟨coreStable datum 0, (coreStable datum 0).property, rfl⟩
      · rfl

theorem PlusGenerated_eq_HPlus : PlusGenerated datum = HPlus datum := by
  apply le_antisymm
  · rw [PlusGenerated, generatedWithStable, Subgroup.closure_le]
    rintro _ (⟨b, hb, rfl⟩ | rfl)
    · rcases hb with ⟨x, hx, hxb⟩
      change toFinalStage datum (rankFiveFree datum) (b :
        TStage datum (rankFiveFree datum)) ∈ HPlus datum
      rw [← hxb]
      exact CSubgroup_one_to_HPlus datum ⟨x, hx⟩
    · exact k_mem_HPlus datum
  · rw [HPlus, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl | rfl | rfl)
    · apply Subgroup.subset_closure
      left
      refine ⟨cSubgroupToPlusBase datum (coreD datum 1), ?_, rfl⟩
      exact (cSubgroupToPlusBase datum (coreD datum 1)).property
    · apply Subgroup.subset_closure
      left
      refine ⟨cSubgroupToPlusBase datum (coreE datum 1), ?_, rfl⟩
      exact (cSubgroupToPlusBase datum (coreE datum 1)).property
    · apply Subgroup.subset_closure
      left
      refine ⟨cSubgroupToPlusBase datum (coreC datum 1), ?_, rfl⟩
      exact (cSubgroupToPlusBase datum (coreC datum 1)).property
    · exact Subgroup.subset_closure (Or.inr rfl)
    · apply Subgroup.subset_closure
      left
      refine ⟨cSubgroupToPlusBase datum (coreStable datum 1), ?_, rfl⟩
      exact (cSubgroupToPlusBase datum (coreStable datum 1)).property

/-- The equivalence onto the image of the negative generated subgroup in the final stage. -/
def minusGeneratedToImage :
    MinusGenerated datum ≃*
      (MinusGenerated datum).map
        (toFinalStage datum (rankFiveFree datum)) :=
  (MinusGenerated datum).equivMapOfInjective
    (toFinalStage datum (rankFiveFree datum))
    (HNNExtension.of_injective
      (MulEquiv.refl (KSubgroup datum (rankFiveFree datum))))

/-- Exact parametrization of `HMinus`. -/
def minusParamEquiv : MinusRestricted datum ≃* HMinus datum :=
  (minusRestrictedRangeEquiv datum).trans
    ((minusGeneratedToImage datum).trans
      (MulEquiv.subgroupCongr (MinusGenerated_map_eq_HMinus datum)))

/-- Exact parametrization of `HPlus`. -/
def plusParamEquiv : PlusRestricted datum ≃* HPlus datum :=
  (plusRestrictedRangeEquiv datum).trans
    (MulEquiv.subgroupCongr (PlusGenerated_eq_HPlus datum))

@[simp] theorem minusParamEquiv_coe (x : MinusRestricted datum) :
    ((minusParamEquiv datum x : HMinus datum) : Gamma datum) =
      minusEmbedding datum x := by
  simp only [minusParamEquiv, MulEquiv.trans_apply]
  change
    toFinalStage datum (rankFiveFree datum)
        (((minusRestrictedRangeEquiv datum x : MinusGenerated datum) :
          TStage datum (rankFiveFree datum))) = minusEmbedding datum x
  have h := restrictedEquivGeneratedWithStable_coe
    (CSubgroup datum 0) (minusCompatibility datum) x
  change
    ((minusRestrictedRangeEquiv datum x : MinusGenerated datum) :
      TStage datum (rankFiveFree datum)) = minusEmbeddingToT datum x at h
  exact congrArg (toFinalStage datum (rankFiveFree datum)) h

@[simp] theorem plusParamEquiv_coe (x : PlusRestricted datum) :
    ((plusParamEquiv datum x : HPlus datum) : Gamma datum) =
      plusEmbedding datum x := by
  simp only [plusParamEquiv, MulEquiv.trans_apply]
  change
    ((plusRestrictedRangeEquiv datum x : PlusGenerated datum) : Gamma datum) =
      plusEmbedding datum x
  exact restrictedEquivGeneratedWithStable_coe
    (PlusBase datum) (plusCompatibility datum) x

/-- The generator `d` in the negative restricted model. -/
def minusParamD : MinusRestricted datum :=
  HNNExtension.of (coreD datum 0)
/-- The generator `e` in the negative restricted model. -/
def minusParamE : MinusRestricted datum :=
  HNNExtension.of (coreE datum 0)
/-- The generator `c` in the negative restricted model. -/
def minusParamC : MinusRestricted datum :=
  HNNExtension.of (coreC datum 0)
/-- The first stable generator in the negative restricted model. -/
def minusParamS1 : MinusRestricted datum :=
  HNNExtension.of (coreStable datum 0)
/-- The centralizing stable generator `t` in the negative restricted model. -/
def minusParamT : MinusRestricted datum := HNNExtension.t

/-- The generator `d` in the positive restricted model. -/
def plusParamD : PlusRestricted datum :=
  HNNExtension.of (cSubgroupToPlusBase datum (coreD datum 1))
/-- The generator `e` in the positive restricted model. -/
def plusParamE : PlusRestricted datum :=
  HNNExtension.of (cSubgroupToPlusBase datum (coreE datum 1))
/-- The generator `c` in the positive restricted model. -/
def plusParamC : PlusRestricted datum :=
  HNNExtension.of (cSubgroupToPlusBase datum (coreC datum 1))
/-- The second stable generator in the positive restricted model. -/
def plusParamS2 : PlusRestricted datum :=
  HNNExtension.of (cSubgroupToPlusBase datum (coreStable datum 1))
/-- The stable generator `k` in the positive restricted model. -/
def plusParamK : PlusRestricted datum := HNNExtension.t

/-- The element `d` with its membership witness in the negative associated subgroup. -/
def minusD : HMinus datum := ⟨d datum, d_mem_HMinus datum⟩
/-- The element `e` with its membership witness in the negative associated subgroup. -/
def minusE : HMinus datum := ⟨e datum, e_mem_HMinus datum⟩
/-- The element `c` with its membership witness in the negative associated subgroup. -/
def minusC : HMinus datum := ⟨c datum, c_mem_HMinus datum⟩
/-- The element `t` with its membership witness in the negative associated subgroup. -/
def minusT : HMinus datum := ⟨t datum, t_mem_HMinus datum⟩
/-- The first stable element with its membership witness in the negative associated subgroup. -/
def minusS1 : HMinus datum := ⟨s1 datum, s1_mem_HMinus datum⟩

/-- The element `d` with its membership witness in the positive associated subgroup. -/
def plusD : HPlus datum := ⟨d datum, d_mem_HPlus datum⟩
/-- The element `e` with its membership witness in the positive associated subgroup. -/
def plusE : HPlus datum := ⟨e datum, e_mem_HPlus datum⟩
/-- The element `c` with its membership witness in the positive associated subgroup. -/
def plusC : HPlus datum := ⟨c datum, c_mem_HPlus datum⟩
/-- The element `k` with its membership witness in the positive associated subgroup. -/
def plusK : HPlus datum := ⟨k datum, k_mem_HPlus datum⟩
/-- The second stable element with its membership witness in the positive associated subgroup. -/
def plusS2 : HPlus datum := ⟨s2 datum, s2_mem_HPlus datum⟩

@[simp] private theorem minusParamEquiv_paramD :
    minusParamEquiv datum (minusParamD datum) = minusD datum := by
  apply Subtype.ext
  rw [minusParamEquiv_coe]
  rfl

@[simp] private theorem minusParamEquiv_paramE :
    minusParamEquiv datum (minusParamE datum) = minusE datum := by
  apply Subtype.ext
  rw [minusParamEquiv_coe]
  rfl

@[simp] private theorem minusParamEquiv_paramC :
    minusParamEquiv datum (minusParamC datum) = minusC datum := by
  apply Subtype.ext
  rw [minusParamEquiv_coe]
  rfl

@[simp] private theorem minusParamEquiv_paramT :
    minusParamEquiv datum (minusParamT datum) = minusT datum := by
  apply Subtype.ext
  rw [minusParamEquiv_coe]
  rfl

@[simp] private theorem minusParamEquiv_paramS1 :
    minusParamEquiv datum (minusParamS1 datum) = minusS1 datum := by
  apply Subtype.ext
  rw [minusParamEquiv_coe]
  rfl

@[simp] private theorem plusParamEquiv_paramD :
    plusParamEquiv datum (plusParamD datum) = plusD datum := by
  apply Subtype.ext
  rw [plusParamEquiv_coe]
  rfl

@[simp] private theorem plusParamEquiv_paramE :
    plusParamEquiv datum (plusParamE datum) = plusE datum := by
  apply Subtype.ext
  rw [plusParamEquiv_coe]
  rfl

@[simp] private theorem plusParamEquiv_paramC :
    plusParamEquiv datum (plusParamC datum) = plusC datum := by
  apply Subtype.ext
  rw [plusParamEquiv_coe]
  rfl

@[simp] private theorem plusParamEquiv_paramK :
    plusParamEquiv datum (plusParamK datum) = plusK datum := by
  apply Subtype.ext
  rw [plusParamEquiv_coe]
  rfl

@[simp] private theorem plusParamEquiv_paramS2 :
    plusParamEquiv datum (plusParamS2 datum) = plusS2 datum := by
  apply Subtype.ext
  rw [plusParamEquiv_coe]
  rfl

@[simp] private theorem outerBaseEquiv_coreD :
    outerBaseEquiv datum (coreD datum 0) =
      (cSubgroupToPlusBase datum (coreE datum 1))⁻¹ := by
  change cSubgroupToPlusBase datum
      (cSubgroupEquiv datum (coreD datum 0)) = _
  rw [cSubgroupEquiv_coreD, map_inv]

@[simp] private theorem outerBaseEquiv_coreE :
    outerBaseEquiv datum (coreE datum 0) =
      cSubgroupToPlusBase datum (coreD datum 1) := by
  change cSubgroupToPlusBase datum
      (cSubgroupEquiv datum (coreE datum 0)) = _
  rw [cSubgroupEquiv_coreE]

@[simp] private theorem outerBaseEquiv_coreC :
    outerBaseEquiv datum (coreC datum 0) =
      cSubgroupToPlusBase datum (coreC datum 1) := by
  change cSubgroupToPlusBase datum
      (cSubgroupEquiv datum (coreC datum 0)) = _
  rw [cSubgroupEquiv_coreC]

@[simp] private theorem outerBaseEquiv_coreS1 :
    outerBaseEquiv datum (coreStable datum 0) =
      (cSubgroupToPlusBase datum (coreStable datum 1))⁻¹ := by
  change cSubgroupToPlusBase datum
      (cSubgroupEquiv datum (coreStable datum 0)) = _
  rw [cSubgroupEquiv_coreS1, map_inv]

@[simp] private theorem outerRestrictedEquiv_paramD :
    outerRestrictedEquiv datum (minusParamD datum) = (plusParamE datum)⁻¹ := by
  rw [minusParamD, plusParamE, outerRestrictedEquiv_of,
    outerBaseEquiv_coreD, map_inv]

@[simp] private theorem outerRestrictedEquiv_paramE :
    outerRestrictedEquiv datum (minusParamE datum) = plusParamD datum := by
  rw [minusParamE, plusParamD, outerRestrictedEquiv_of,
    outerBaseEquiv_coreE]

@[simp] private theorem outerRestrictedEquiv_paramC :
    outerRestrictedEquiv datum (minusParamC datum) = plusParamC datum := by
  rw [minusParamC, plusParamC, outerRestrictedEquiv_of,
    outerBaseEquiv_coreC]

@[simp] private theorem outerRestrictedEquiv_paramT :
    outerRestrictedEquiv datum (minusParamT datum) = plusParamK datum :=
  outerRestrictedEquiv_t datum

@[simp] private theorem outerRestrictedEquiv_paramS1 :
    outerRestrictedEquiv datum (minusParamS1 datum) = (plusParamS2 datum)⁻¹ := by
  rw [minusParamS1, plusParamS2, outerRestrictedEquiv_of,
    outerBaseEquiv_coreS1, map_inv]

/-- The output interface of the subgroup isomorphism following Lemma 3.1. -/
structure ThetaData where
  /-- The associated-subgroup isomorphism satisfying the displayed generator images. -/
  equiv : HMinus datum ≃* HPlus datum
  map_d : equiv (minusD datum) = (plusE datum)⁻¹
  map_e : equiv (minusE datum) = plusD datum
  map_c : equiv (minusC datum) = plusC datum
  map_t : equiv (minusT datum) = plusK datum
  map_s1 : equiv (minusS1 datum) = (plusS2 datum)⁻¹

/-- The subgroup isomorphism following Lemma 3.1, constructed from the two
exact restricted-HNN parametrizations. -/
def thetaEquiv : HMinus datum ≃* HPlus datum :=
  (minusParamEquiv datum).symm.trans
    ((outerRestrictedEquiv datum).trans (plusParamEquiv datum))

@[simp] theorem thetaEquiv_minusD :
    thetaEquiv datum (minusD datum) = (plusE datum)⁻¹ := by
  change
    plusParamEquiv datum
        (outerRestrictedEquiv datum
          ((minusParamEquiv datum).symm (minusD datum))) = _
  rw [← minusParamEquiv_paramD,
    (minusParamEquiv datum).symm_apply_apply,
    outerRestrictedEquiv_paramD, map_inv, plusParamEquiv_paramE]

@[simp] theorem thetaEquiv_minusE :
    thetaEquiv datum (minusE datum) = plusD datum := by
  change
    plusParamEquiv datum
        (outerRestrictedEquiv datum
          ((minusParamEquiv datum).symm (minusE datum))) = _
  rw [← minusParamEquiv_paramE,
    (minusParamEquiv datum).symm_apply_apply,
    outerRestrictedEquiv_paramE, plusParamEquiv_paramD]

@[simp] theorem thetaEquiv_minusC :
    thetaEquiv datum (minusC datum) = plusC datum := by
  change
    plusParamEquiv datum
        (outerRestrictedEquiv datum
          ((minusParamEquiv datum).symm (minusC datum))) = _
  rw [← minusParamEquiv_paramC,
    (minusParamEquiv datum).symm_apply_apply,
    outerRestrictedEquiv_paramC, plusParamEquiv_paramC]

@[simp] theorem thetaEquiv_minusT :
    thetaEquiv datum (minusT datum) = plusK datum := by
  change
    plusParamEquiv datum
        (outerRestrictedEquiv datum
          ((minusParamEquiv datum).symm (minusT datum))) = _
  rw [← minusParamEquiv_paramT,
    (minusParamEquiv datum).symm_apply_apply,
    outerRestrictedEquiv_paramT, plusParamEquiv_paramK]

@[simp] theorem thetaEquiv_minusS1 :
    thetaEquiv datum (minusS1 datum) = (plusS2 datum)⁻¹ := by
  change
    plusParamEquiv datum
        (outerRestrictedEquiv datum
          ((minusParamEquiv datum).symm (minusS1 datum))) = _
  rw [← minusParamEquiv_paramS1,
    (minusParamEquiv datum).symm_apply_apply,
    outerRestrictedEquiv_paramS1, map_inv, plusParamEquiv_paramS2]

/-- The canonical HNN datum for the first compression. -/
def thetaData : ThetaData datum where
  equiv := thetaEquiv datum
  map_d := thetaEquiv_minusD datum
  map_e := thetaEquiv_minusE datum
  map_c := thetaEquiv_minusC datum
  map_t := thetaEquiv_minusT datum
  map_s1 := thetaEquiv_minusS1 datum

variable (theta : ThetaData datum)

/-- The proper HNN extension associated to a `ThetaData` witness. -/
abbrev YStage := HNNExtension (Gamma datum) (HMinus datum) (HPlus datum) theta.equiv

/-- The canonical inclusion `Gamma → G_y`. -/
def toYStage : Gamma datum →* YStage datum theta := HNNExtension.of

/-- The paper's `y`; Mathlib's stable letter is `y⁻¹`. -/
def yLetter : YStage datum theta := (HNNExtension.t : YStage datum theta)⁻¹

theorem toYStage_injective : Function.Injective (toYStage datum theta) :=
  HNNExtension.of_injective theta.equiv

private theorem y_conjugates (x : HMinus datum) :
    (yLetter datum theta)⁻¹ * toYStage datum theta (x : Gamma datum) *
        yLetter datum theta =
      toYStage datum theta ((theta.equiv x : HPlus datum) : Gamma datum) := by
  have h := HNNExtension.t_mul_of (φ := theta.equiv) x
  change HNNExtension.t * HNNExtension.of (x : Gamma datum) * HNNExtension.t⁻¹ = _
  rw [h]
  simp [toYStage]

theorem y_conjugates_d :
    (yLetter datum theta)⁻¹ * toYStage datum theta (d datum) * yLetter datum theta =
      (toYStage datum theta (e datum))⁻¹ := by
  rw [show d datum = (minusD datum : Gamma datum) by rfl]
  rw [y_conjugates, theta.map_d]
  rfl

theorem y_conjugates_e :
    (yLetter datum theta)⁻¹ * toYStage datum theta (e datum) * yLetter datum theta =
      toYStage datum theta (d datum) := by
  rw [show e datum = (minusE datum : Gamma datum) by rfl]
  rw [y_conjugates, theta.map_e]
  rfl

theorem y_conjugates_c :
    (yLetter datum theta)⁻¹ * toYStage datum theta (c datum) * yLetter datum theta =
      toYStage datum theta (c datum) := by
  rw [show c datum = (minusC datum : Gamma datum) by rfl]
  rw [y_conjugates, theta.map_c]
  rfl

theorem y_conjugates_t :
    (yLetter datum theta)⁻¹ * toYStage datum theta (t datum) * yLetter datum theta =
      toYStage datum theta (k datum) := by
  rw [show t datum = (minusT datum : Gamma datum) by rfl]
  rw [y_conjugates, theta.map_t]
  rfl

theorem y_conjugates_s1 :
    (yLetter datum theta)⁻¹ * toYStage datum theta (s1 datum) * yLetter datum theta =
      (toYStage datum theta (s2 datum))⁻¹ := by
  rw [show s1 datum = (minusS1 datum : Gamma datum) by rfl]
  rw [y_conjugates, theta.map_s1]
  rfl

end

end HostYStage
end Undecidability
