/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.ThetaCT

/-!
# The second compression HNN extension

This file formalizes Lemma 3.2 of the paper using Proposition 3.8.  The two
subgroups which are to be identified by the new stable letter are

* `DTC = ⟨d,t,c⟩`, and
* `TCY = ⟨t,c,y⟩`

inside the proper `y`-stage.  The first part of the file identifies `TCY`
with the HNN extension obtained by restricting the `y`-stage to
`Kc = ⟨t,c,k⟩`.  In particular, the apparently extra generator `k` is
eliminated by the defining equation `y⁻¹ t y = k`.
-/

@[expose] public section

namespace Undecidability
namespace HostZStage

open BorisovConverseCore
open BorisovCStage
open BorisovContextNormalForm
open BorisovFinalModel
open BorisovHNNModel
open BorisovInputsBridge
open HNNLemmas
open HostYStage
open HostKcModel
open HostThetaCT
open HostZIntersections

noncomputable section

variable (datum : Thue.StandingDatum) (theta : ThetaData datum)

/-- The underlying element is unchanged when a restricted attaching map is
the restriction of the identity.  Stating this over abstract groups avoids
unfolding the concrete HNN tower at every use below. -/
private theorem restrictedPhi_refl_coe
    {G : Type*} [Group G] (H K : Subgroup G)
    (hphi : ∀ a : K,
      (a : G) ∈ H ↔
        (((MulEquiv.refl K) a : K) : G) ∈ H)
    (a : restrictedA (A := K) H) :
    (((restrictedPhi H hphi) a : restrictedB (B := K) H) : H) =
      (a : H) := rfl

/-- The first compression HNN extension, adjoining the stable generator `y`. -/
abbrev Y := YStage datum theta

/-- The image of `d` in the first compression extension. -/
def dY : Y datum theta := toYStage datum theta (d datum)
/-- The image of `t` in the first compression extension. -/
def tY : Y datum theta := toYStage datum theta (t datum)
/-- The image of `c` in the first compression extension. -/
def cY : Y datum theta := toYStage datum theta (c datum)
/-- The image of `k` in the first compression extension. -/
def kY : Y datum theta := toYStage datum theta (k datum)
/-- The new stable generator `y` of the first compression extension. -/
def y : Y datum theta := yLetter datum theta

/-- The source subgroup for the second HNN extension: `⟨d,t,c⟩`. -/
def DTC : Subgroup (Y datum theta) :=
  Subgroup.closure ({dY datum theta, tY datum theta, cY datum theta} :
    Set (Y datum theta))

/-- The target subgroup for the second HNN extension: `⟨t,c,y⟩`. -/
def TCY : Subgroup (Y datum theta) :=
  Subgroup.closure ({tY datum theta, cY datum theta, y datum theta} :
    Set (Y datum theta))

@[simp] theorem dY_mem_DTC : dY datum theta ∈ DTC datum theta := by
  apply Subgroup.subset_closure
  simp

@[simp] theorem tY_mem_DTC : tY datum theta ∈ DTC datum theta := by
  apply Subgroup.subset_closure
  simp

@[simp] theorem cY_mem_DTC : cY datum theta ∈ DTC datum theta := by
  apply Subgroup.subset_closure
  simp

@[simp] theorem tY_mem_TCY : tY datum theta ∈ TCY datum theta := by
  apply Subgroup.subset_closure
  simp

@[simp] theorem cY_mem_TCY : cY datum theta ∈ TCY datum theta := by
  apply Subgroup.subset_closure
  simp

@[simp] theorem y_mem_TCY : y datum theta ∈ TCY datum theta := by
  apply Subgroup.subset_closure
  simp

theorem kY_eq_y_inv_tY_y :
    kY datum theta =
      (y datum theta)⁻¹ * tY datum theta * y datum theta :=
  (y_conjugates_t datum theta).symm

@[simp] theorem kY_mem_TCY : kY datum theta ∈ TCY datum theta := by
  rw [kY_eq_y_inv_tY_y]
  exact (TCY datum theta).mul_mem
    ((TCY datum theta).mul_mem
      ((TCY datum theta).inv_mem (y_mem_TCY datum theta))
      (tY_mem_TCY datum theta))
    (y_mem_TCY datum theta)

/-! ## Exact restricted presentation of `⟨t,c,y⟩` -/

/-- The first associated subgroup of the `y` extension restricted to the `k,c` subgroup. -/
abbrev YRestrictedA :=
  restrictedA (A := HMinus datum) (Kc datum)

/-- The second associated subgroup of the `y` extension restricted to the `k,c` subgroup. -/
abbrev YRestrictedB :=
  restrictedB (B := HPlus datum) (Kc datum)

/-- The restricted associated-subgroup isomorphism for the `y` extension. -/
def yRestrictedPhi :
    YRestrictedA datum ≃* YRestrictedB datum :=
  restrictedPhi (Kc datum) (theta_mem_Kc_iff datum theta)

/-- The HNN extension obtained by restricting the `y`-stage to
`Kc = ⟨t,c,k⟩`. -/
abbrev YRestricted :=
  HNNExtension (Kc datum) (YRestrictedA datum) (YRestrictedB datum)
    (yRestrictedPhi datum theta)

/-- The canonical embedding of the restricted model into the ambient
`y`-stage. -/
def yRestrictedEmbedding : YRestricted datum theta →* Y datum theta :=
  restrictedEmbedding (Kc datum) (theta_mem_Kc_iff datum theta)

theorem yRestrictedEmbedding_injective :
    Function.Injective (yRestrictedEmbedding datum theta) :=
  restrictedEmbedding_injective (Kc datum) (theta_mem_Kc_iff datum theta)

@[simp] theorem yRestrictedEmbedding_of (x : Kc datum) :
    yRestrictedEmbedding datum theta (HNNExtension.of x) =
      toYStage datum theta (x : HostYStage.Gamma datum) :=
  restrictedEmbedding_of
    (Kc datum) (theta_mem_Kc_iff datum theta) x

@[simp] theorem yRestrictedEmbedding_t :
    yRestrictedEmbedding datum theta HNNExtension.t =
      (HNNExtension.t : Y datum theta) :=
  restrictedEmbedding_t
    (Kc datum) (theta_mem_Kc_iff datum theta)

private theorem CTInGamma_maps_into_TCY :
    CTInGamma datum ≤
      (TCY datum theta).comap (toYStage datum theta) := by
  rw [CTInGamma, Subgroup.map_le_iff_le_comap]
  rw [HostZBaseIntersections.CT, generatedWith, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · rcases hx with ⟨a, ha, rfl⟩
    rcases Subgroup.mem_closure_singleton.mp ha with ⟨n, hn⟩
    rw [← hn]
    simpa [cY, HostYStage.c, BorisovFinalModel.modelC,
      BorisovFinalModel.cStageToFinal, map_zpow] using
      (TCY datum theta).zpow_mem (cY_mem_TCY datum theta) n
  · have hx' : x = tLetter datum (HostYStage.FreeInput datum) := by
      simpa using hx
    subst x
    exact tY_mem_TCY datum theta

private theorem Kc_maps_into_TCY :
    Kc datum ≤ (TCY datum theta).comap (toYStage datum theta) := by
  rw [Kc, generatedWith, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact CTInGamma_maps_into_TCY datum theta hx
  · have hx' : x = k datum := by simpa using hx
    subst x
    exact kY_mem_TCY datum theta

theorem restrictedGenerated_eq_TCY :
    generatedWithStable
        (A := HMinus datum) (B := HPlus datum) (phi := theta.equiv)
        (Kc datum) =
      TCY datum theta := by
  apply le_antisymm
  · rw [generatedWithStable, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨a, ha, rfl⟩
      exact Kc_maps_into_TCY datum theta ha
    · have hx' : x = (HNNExtension.t : Y datum theta) := by simpa using hx
      subst x
      change (y datum theta)⁻¹ ∈ TCY datum theta
      exact (TCY datum theta).inv_mem (y_mem_TCY datum theta)
  · rw [TCY, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · apply Subgroup.subset_closure
      left
      exact ⟨t datum, by
        exact CTInGamma_le_Kc datum (t_mem_CTInGamma datum), rfl⟩
    · apply Subgroup.subset_closure
      left
      exact ⟨c datum, by
        exact CTInGamma_le_Kc datum (c_mem_CTInGamma datum), rfl⟩
    · have ht : (HNNExtension.t : Y datum theta) ∈
          generatedWithStable
            (A := HMinus datum) (B := HPlus datum) (phi := theta.equiv)
            (Kc datum) := by
        apply Subgroup.subset_closure
        right
        rfl
      simpa [y, yLetter] using
        (generatedWithStable
          (A := HMinus datum) (B := HPlus datum) (phi := theta.equiv)
          (Kc datum)).inv_mem ht

/-- Exact subgroup-presentation equivalence for `⟨t,c,y⟩`.  This is
the formal Tietze elimination of the intermediate generator `k` at the
second HNN stage. -/
def yRestrictedEquivTCY : YRestricted datum theta ≃* TCY datum theta :=
  (restrictedEquivGeneratedWithStable (Kc datum)
      (theta_mem_Kc_iff datum theta)).trans
    (MulEquiv.subgroupCongr (restrictedGenerated_eq_TCY datum theta))

@[simp] theorem yRestrictedEquivTCY_coe (x : YRestricted datum theta) :
    ((yRestrictedEquivTCY datum theta x : TCY datum theta) :
        Y datum theta) =
      yRestrictedEmbedding datum theta x := by
  change
    (((MulEquiv.subgroupCongr (restrictedGenerated_eq_TCY datum theta))
        (restrictedEquivGeneratedWithStable (Kc datum)
          (theta_mem_Kc_iff datum theta) x) : TCY datum theta) :
      Y datum theta) = _
  rw [MulEquiv.subgroupCongr_apply]
  exact restrictedEquivGeneratedWithStable_coe
    (Kc datum) (theta_mem_Kc_iff datum theta) x

/-! ## Exact restricted presentation of `⟨d,t,c⟩` -/

/-- The first source-model associated subgroup restricted to the `c,d` subgroup. -/
abbrev SourceRestrictedA :=
  restrictedA
    (A := CD datum (HostYStage.FreeInput datum))
    (CD datum (HostYStage.FreeInput datum))

/-- The second source-model associated subgroup restricted to the `c,d` subgroup. -/
abbrev SourceRestrictedB :=
  restrictedB
    (B := CD datum (HostYStage.FreeInput datum))
    (CD datum (HostYStage.FreeInput datum))

theorem source_mem_iff
    (a : CD datum (HostYStage.FreeInput datum)) :
    (a : Gamma2 datum (HostYStage.FreeInput datum)) ∈
          CD datum (HostYStage.FreeInput datum) ↔
      (((MulEquiv.refl (CD datum (HostYStage.FreeInput datum))) a :
          CD datum (HostYStage.FreeInput datum)) :
            Gamma2 datum (HostYStage.FreeInput datum)) ∈
        CD datum (HostYStage.FreeInput datum) := by
  simp

/-- The source-model associated-subgroup isomorphism restricted to the `c,d` subgroup. -/
def sourceRestrictedPhi :
    SourceRestrictedA datum ≃* SourceRestrictedB datum :=
  restrictedPhi (CD datum (HostYStage.FreeInput datum))
    (source_mem_iff datum)

/-- The restriction of the `t`-centralizer HNN extension to `⟨c,d⟩`.
It is the exact semantic path group underlying `⟨d,t,c⟩`. -/
abbrev SourceModel :=
  HNNExtension
    (CD datum (HostYStage.FreeInput datum))
    (SourceRestrictedA datum) (SourceRestrictedB datum)
    (sourceRestrictedPhi datum)

/-- The embedding of the restricted source model into the `t` HNN stage. -/
def sourceToTStage :
    SourceModel datum →*
      TStage datum (HostYStage.FreeInput datum) :=
  restrictedEmbedding (CD datum (HostYStage.FreeInput datum))
    (source_mem_iff datum)

@[simp] private theorem sourceToTStage_of
    (h : CD datum (HostYStage.FreeInput datum)) :
    sourceToTStage datum (HNNExtension.of h) =
      toTStage datum (HostYStage.FreeInput datum) (h :
        Gamma2 datum (HostYStage.FreeInput datum)) :=
  restrictedEmbedding_of
    (CD datum (HostYStage.FreeInput datum)) (source_mem_iff datum) h

@[simp] private theorem sourceToTStage_t :
    sourceToTStage datum (HNNExtension.t : SourceModel datum) =
      tLetter datum (HostYStage.FreeInput datum) :=
  restrictedEmbedding_t
    (CD datum (HostYStage.FreeInput datum)) (source_mem_iff datum)

/-- The canonical realization of the source path model inside `G_y`. -/
def sourceEmbedding : SourceModel datum →* Y datum theta :=
  (toYStage datum theta).comp
    ((toFinalStage datum (HostYStage.FreeInput datum)).comp
      (sourceToTStage datum))

theorem sourceEmbedding_injective :
    Function.Injective (sourceEmbedding datum theta) :=
  (toYStage_injective datum theta).comp
    ((HNNExtension.of_injective
      (MulEquiv.refl (KSubgroup datum (HostYStage.FreeInput datum)))).comp
        (restrictedEmbedding_injective
          (CD datum (HostYStage.FreeInput datum))
          (source_mem_iff datum)))

private theorem CD_maps_into_DTC :
    CD datum (HostYStage.FreeInput datum) ≤
      (DTC datum theta).comap
        ((toYStage datum theta).comp
          ((toFinalStage datum (HostYStage.FreeInput datum)).comp
            (toTStage datum (HostYStage.FreeInput datum)))) := by
  change
    Subgroup.closure
        ({BorisovCStage.c datum (HostYStage.FreeInput datum),
          of3 datum (HostYStage.FreeInput datum) d3} :
          Set (Gamma2 datum (HostYStage.FreeInput datum))) ≤ _
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact cY_mem_DTC datum theta
  · exact dY_mem_DTC datum theta

theorem sourceEmbedding_range :
    MonoidHom.range (sourceEmbedding datum theta) = DTC datum theta := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using HNNExtension.induction_on with
    | of h =>
        exact CD_maps_into_DTC datum theta h.property
    | t =>
        exact tY_mem_DTC datum theta
    | mul x x' hx hx' =>
        simpa using (DTC datum theta).mul_mem hx hx'
    | inv x hx =>
        simpa using (DTC datum theta).inv_mem hx
  · rw [DTC, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine ⟨HNNExtension.of
          (⟨of3 datum (HostYStage.FreeInput datum) d3,
            Subgroup.subset_closure (by simp)⟩ :
              CD datum (HostYStage.FreeInput datum)), ?_⟩
      simp [sourceEmbedding, dY, HostYStage.d, modelD, cStageToFinal]
    · exact ⟨HNNExtension.t, by
        simp [sourceEmbedding, tY, HostYStage.t, modelT]⟩
    · refine ⟨HNNExtension.of
          (⟨BorisovCStage.c datum (HostYStage.FreeInput datum),
            Subgroup.subset_closure (by simp)⟩ :
              CD datum (HostYStage.FreeInput datum)), ?_⟩
      simp [sourceEmbedding, cY, HostYStage.c, modelC, cStageToFinal]

/-- Exact subgroup-presentation equivalence for `⟨d,t,c⟩`. -/
def sourceModelEquivDTC : SourceModel datum ≃* DTC datum theta :=
  (MonoidHom.ofInjective (sourceEmbedding_injective datum theta)).trans
    (MulEquiv.subgroupCongr (sourceEmbedding_range datum theta))

@[simp] theorem sourceModelEquivDTC_coe (x : SourceModel datum) :
    ((sourceModelEquivDTC datum theta x : DTC datum theta) :
        Y datum theta) = sourceEmbedding datum theta x := by
  rfl

/-- The generator `d` in the restricted source model. -/
def sourceModelD : SourceModel datum :=
  HNNExtension.of
    (⟨of3 datum (HostYStage.FreeInput datum) d3,
      Subgroup.subset_closure (by simp)⟩ :
        CD datum (HostYStage.FreeInput datum))

/-- The centralizing stable generator `t` in the restricted source model. -/
def sourceModelT : SourceModel datum := HNNExtension.t

/-- The generator `c` in the restricted source model. -/
def sourceModelC : SourceModel datum :=
  HNNExtension.of
    (⟨BorisovCStage.c datum (HostYStage.FreeInput datum),
      Subgroup.subset_closure (by simp)⟩ :
        CD datum (HostYStage.FreeInput datum))

@[simp] theorem sourceModelEquivDTC_d :
    sourceModelEquivDTC datum theta (sourceModelD datum) =
      ⟨dY datum theta, dY_mem_DTC datum theta⟩ := by
  apply Subtype.ext
  rw [sourceModelEquivDTC_coe]
  simp [sourceModelD, sourceEmbedding,
    dY, HostYStage.d, modelD, cStageToFinal]

@[simp] theorem sourceModelEquivDTC_t :
    sourceModelEquivDTC datum theta (sourceModelT datum) =
      ⟨tY datum theta, tY_mem_DTC datum theta⟩ := by
  apply Subtype.ext
  rw [sourceModelEquivDTC_coe]
  simp [sourceModelT, sourceEmbedding, tY, HostYStage.t, modelT]

@[simp] theorem sourceModelEquivDTC_c :
    sourceModelEquivDTC datum theta (sourceModelC datum) =
      ⟨cY datum theta, cY_mem_DTC datum theta⟩ := by
  apply Subtype.ext
  rw [sourceModelEquivDTC_coe]
  simp [sourceModelC, sourceEmbedding,
    cY, HostYStage.c, modelC, cStageToFinal]

/-- The generator `t` in the restricted `y`-extension model. -/
def yRestrictedT : YRestricted datum theta :=
  HNNExtension.of
    (⟨t datum, CTInGamma_le_Kc datum (t_mem_CTInGamma datum)⟩ : Kc datum)

/-- The generator `c` in the restricted `y`-extension model. -/
def yRestrictedC : YRestricted datum theta :=
  HNNExtension.of
    (⟨c datum, CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ : Kc datum)

/-- The inverse stable letter representing the generator `y` in the restricted HNN model. -/
def yRestrictedY : YRestricted datum theta := HNNExtension.t⁻¹

@[simp] theorem yRestrictedEquivTCY_t :
    yRestrictedEquivTCY datum theta (yRestrictedT datum theta) =
      ⟨tY datum theta, tY_mem_TCY datum theta⟩ := by
  apply Subtype.ext
  rw [yRestrictedEquivTCY_coe]
  exact restrictedEmbedding_of
    (Kc datum) (theta_mem_Kc_iff datum theta)
    (⟨t datum, CTInGamma_le_Kc datum (t_mem_CTInGamma datum)⟩ : Kc datum)

@[simp] theorem yRestrictedEquivTCY_c :
    yRestrictedEquivTCY datum theta (yRestrictedC datum theta) =
      ⟨cY datum theta, cY_mem_TCY datum theta⟩ := by
  apply Subtype.ext
  rw [yRestrictedEquivTCY_coe]
  exact restrictedEmbedding_of
    (Kc datum) (theta_mem_Kc_iff datum theta)
    (⟨c datum, CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ : Kc datum)

@[simp] theorem yRestrictedEquivTCY_y :
    yRestrictedEquivTCY datum theta (yRestrictedY datum theta) =
      ⟨y datum theta, y_mem_TCY datum theta⟩ := by
  apply Subtype.ext
  rw [yRestrictedEquivTCY_coe]
  exact congrArg Inv.inv
    (restrictedEmbedding_t
      (Kc datum) (theta_mem_Kc_iff datum theta))

/-! ## The forward path rotation on the exact source model -/

/-- The homomorphism sending the generator of the rank-one free group to `d₃`. -/
def dFreeToGamma3 : FreeGroup Unit →* Gamma3 :=
  FreeGroup.lift fun _ ↦ d3

@[simp] private theorem dFreeToGamma3_of :
    dFreeToGamma3 (FreeGroup.of ()) = d3 := by
  simp [dFreeToGamma3]

/-- The inclusion of the rank-one alphabet into the first generator of the rank-two alphabet. -/
def unitToBase : Unit → Fin 2 := fun _ ↦ 0

private theorem unitToBase_injective : Function.Injective unitToBase := by
  intro x y _
  exact Subsingleton.elim x y

private theorem dFreeToGamma3_eq :
    dFreeToGamma3 =
      (of1.comp of0).comp (FreeGroup.map unitToBase) := by
  apply FreeGroup.ext_hom
  intro u
  cases u
  simp [dFreeToGamma3, unitToBase, d3, BorisovHNNModel.d]

theorem dFreeToGamma3_injective :
    Function.Injective dFreeToGamma3 := by
  rw [dFreeToGamma3_eq]
  exact baseEmbedding_injective.comp
    (FreeGroup.map_injective unitToBase_injective)

theorem dFreeToGamma3_range :
    MonoidHom.range dFreeToGamma3 = dCyclic := by
  rw [dFreeToGamma3, FreeGroup.range_lift_eq_closure, dCyclic]
  congr 1
  ext x
  simp

/-- The equivalence between the rank-one free group and the cyclic subgroup generated by `d₃`. -/
def freeEquivDCyclic : FreeGroup Unit ≃* dCyclic :=
  (MonoidHom.ofInjective dFreeToGamma3_injective).trans
    (MulEquiv.subgroupCongr dFreeToGamma3_range)

/-- The generator `d₃`, regarded as an element of its cyclic subgroup. -/
def dInCyclic : dCyclic :=
  ⟨d3, Subgroup.subset_closure (by rfl)⟩

@[simp] private theorem freeEquivDCyclic_of :
    freeEquivDCyclic (FreeGroup.of ()) = dInCyclic := by
  apply Subtype.ext
  change
    (((MulEquiv.subgroupCongr dFreeToGamma3_range)
        ((MonoidHom.ofInjective dFreeToGamma3_injective)
          (FreeGroup.of ())) : dCyclic) : Gamma3) = d3
  rw [MulEquiv.subgroupCongr_apply]
  calc
    (((MonoidHom.ofInjective dFreeToGamma3_injective)
        (FreeGroup.of ())) : MonoidHom.range dFreeToGamma3) =
        dFreeToGamma3 (FreeGroup.of ()) :=
      MonoidHom.ofInjective_apply dFreeToGamma3_injective
    _ = d3 := dFreeToGamma3_of

/-- The homomorphism from the cyclic `d₃` subgroup to the restricted `y` model. -/
def dCyclicToYRestricted :
    dCyclic →* YRestricted datum theta :=
  (FreeGroup.lift fun _ ↦ yRestrictedT datum theta).comp
    (freeEquivDCyclic.symm.toMonoidHom)

@[simp] private theorem dCyclicToYRestricted_d :
    dCyclicToYRestricted datum theta dInCyclic =
      yRestrictedT datum theta := by
  have hpre : freeEquivDCyclic.symm dInCyclic = FreeGroup.of () := by
    rw [← freeEquivDCyclic_of]
    exact freeEquivDCyclic.symm_apply_apply (FreeGroup.of ())
  simp [dCyclicToYRestricted, hpre]

private theorem dRestrictedA_eq_one
    (a : restrictedA (A := U datum) dCyclic) : a = 1 := by
  have hbot := (baseIntersections datum).u_inf_DE
  have hx : ((a : dCyclic) : Gamma3) ∈ U datum ⊓ DE3 :=
    ⟨a.property, dCyclic_le_DE3 (a : dCyclic).property⟩
  rw [hbot] at hx
  apply Subtype.ext
  apply Subtype.ext
  simpa using hx

/-- The homomorphism from the restricted `d` subgroup to the restricted `y` model. -/
def dRestrictedToYRestricted :
    DRestricted datum (HostYStage.FreeInput datum) (baseIntersections datum) →*
      YRestricted datum theta :=
  HNNExtension.lift (dCyclicToYRestricted datum theta) HNNExtension.t (by
    intro a
    have ha : a = 1 := dRestrictedA_eq_one datum a
    subst a
    simp)

@[simp] private theorem dRestrictedToYRestricted_of (x : dCyclic) :
    dRestrictedToYRestricted datum theta (HNNExtension.of x) =
      dCyclicToYRestricted datum theta x := by
  simp [dRestrictedToYRestricted]

@[simp] private theorem dRestrictedToYRestricted_t :
    dRestrictedToYRestricted datum theta HNNExtension.t = HNNExtension.t := by
  simp [dRestrictedToYRestricted]

/-- The homomorphism from the `c,d` subgroup to the restricted `y` model. -/
def CDToYRestricted :
    CD datum (HostYStage.FreeInput datum) →* YRestricted datum theta :=
  (dRestrictedToYRestricted datum theta).comp
    ((dRestrictedEquivCD datum (HostYStage.FreeInput datum)
      (baseIntersections datum)).symm.toMonoidHom)

/-- The image of `d₃` in the subgroup generated by `c` and `d`. -/
def dInCD : CD datum (HostYStage.FreeInput datum) :=
  ⟨of3 datum (HostYStage.FreeInput datum) d3,
    Subgroup.subset_closure (by simp)⟩

/-- The element `c` in the subgroup generated by `c` and `d`. -/
def cInCD : CD datum (HostYStage.FreeInput datum) :=
  ⟨BorisovCStage.c datum (HostYStage.FreeInput datum),
    Subgroup.subset_closure (by simp)⟩

private theorem dRestrictedEquivCD_symm_d :
    (dRestrictedEquivCD datum (HostYStage.FreeInput datum)
        (baseIntersections datum)).symm (dInCD datum) =
      HNNExtension.of dInCyclic := by
  apply (dRestrictedEquivCD datum (HostYStage.FreeInput datum)
    (baseIntersections datum)).injective
  rw [(dRestrictedEquivCD datum (HostYStage.FreeInput datum)
    (baseIntersections datum)).apply_symm_apply]
  apply Subtype.ext
  exact dRestrictedEquivCD_of_coe datum (HostYStage.FreeInput datum)
    (baseIntersections datum) dInCyclic

private theorem dRestrictedEquivCD_symm_c :
    (dRestrictedEquivCD datum (HostYStage.FreeInput datum)
        (baseIntersections datum)).symm (cInCD datum) =
      (HNNExtension.t :
        DRestricted datum (HostYStage.FreeInput datum)
          (baseIntersections datum))⁻¹ := by
  apply (dRestrictedEquivCD datum (HostYStage.FreeInput datum)
    (baseIntersections datum)).injective
  rw [(dRestrictedEquivCD datum (HostYStage.FreeInput datum)
    (baseIntersections datum)).apply_symm_apply]
  apply Subtype.ext
  exact dRestrictedEquivCD_inv_t_coe datum (HostYStage.FreeInput datum)
    (baseIntersections datum)

@[simp] private theorem CDToYRestricted_d :
    CDToYRestricted datum theta (dInCD datum) =
      yRestrictedT datum theta := by
  change
    dRestrictedToYRestricted datum theta
      ((dRestrictedEquivCD datum (HostYStage.FreeInput datum)
        (baseIntersections datum)).symm (dInCD datum)) = _
  rw [dRestrictedEquivCD_symm_d]
  simp

@[simp] private theorem CDToYRestricted_c :
    CDToYRestricted datum theta (cInCD datum) =
      yRestrictedY datum theta := by
  change
    dRestrictedToYRestricted datum theta
      ((dRestrictedEquivCD datum (HostYStage.FreeInput datum)
        (baseIntersections datum)).symm (cInCD datum)) = _
  rw [dRestrictedEquivCD_symm_c, map_inv, dRestrictedToYRestricted_t]
  rfl

private theorem cY_commutes_tY :
    Commute (cY datum theta) (tY datum theta) := by
  have hc : BorisovCStage.c datum (HostYStage.FreeInput datum) ∈
      CD datum (HostYStage.FreeInput datum) :=
    Subgroup.subset_closure (by simp)
  have hct := (centralizerOf_commute_stable_iff
    (CD datum (HostYStage.FreeInput datum))
    (BorisovCStage.c datum (HostYStage.FreeInput datum))).2 hc
  have hfinal := hct.map (toFinalStage datum (HostYStage.FreeInput datum))
  have hy := hfinal.map (toYStage datum theta)
  simpa [cY, tY, HostYStage.c, HostYStage.t, modelC, modelT,
    cStageToFinal, toTStage, tLetter, centralizerOf,
    centralizerStable] using hy

private theorem cY_commutes_y :
    Commute (cY datum theta) (y datum theta) := by
  have hconj :
      (y datum theta)⁻¹ * cY datum theta * y datum theta =
        cY datum theta := by
    simpa [y, cY] using y_conjugates_c datum theta
  calc
    cY datum theta * y datum theta =
        y datum theta *
          ((y datum theta)⁻¹ * cY datum theta * y datum theta) := by
            simp [mul_assoc]
    _ = y datum theta * cY datum theta := by rw [hconj]

private theorem yRestrictedC_commutes_T :
    Commute (yRestrictedC datum theta) (yRestrictedT datum theta) := by
  apply yRestrictedEmbedding_injective datum theta
  rw [map_mul, map_mul]
  change
    yRestrictedEmbedding datum theta
        (HNNExtension.of
          (⟨c datum, CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ :
            Kc datum)) *
      yRestrictedEmbedding datum theta
        (HNNExtension.of
          (⟨t datum, CTInGamma_le_Kc datum (t_mem_CTInGamma datum)⟩ :
            Kc datum)) =
    yRestrictedEmbedding datum theta
        (HNNExtension.of
          (⟨t datum, CTInGamma_le_Kc datum (t_mem_CTInGamma datum)⟩ :
            Kc datum)) *
      yRestrictedEmbedding datum theta
        (HNNExtension.of
          (⟨c datum, CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ :
            Kc datum))
  rw [yRestrictedEmbedding_of]
  exact (cY_commutes_tY datum theta).eq

private theorem yRestrictedC_commutes_Y :
    Commute (yRestrictedC datum theta) (yRestrictedY datum theta) := by
  apply yRestrictedEmbedding_injective datum theta
  rw [map_mul, map_mul]
  change
    yRestrictedEmbedding datum theta
        (HNNExtension.of
          (⟨c datum, CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ :
            Kc datum)) *
      yRestrictedEmbedding datum theta HNNExtension.t⁻¹ =
    yRestrictedEmbedding datum theta HNNExtension.t⁻¹ *
      yRestrictedEmbedding datum theta
        (HNNExtension.of
          (⟨c datum, CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ :
            Kc datum))
  rw [map_inv, yRestrictedEmbedding_t, yRestrictedEmbedding_of]
  exact (cY_commutes_y datum theta).eq

private theorem yRestrictedC_commutes_dCyclic
    (x : dCyclic) :
    Commute (yRestrictedC datum theta)
      (dCyclicToYRestricted datum theta x) := by
  rcases Subgroup.mem_closure_singleton.mp x.property with ⟨n, hn⟩
  have hx : x = dInCyclic ^ n := by
    apply Subtype.ext
    exact hn.symm
  rw [hx, map_zpow, dCyclicToYRestricted_d]
  exact (yRestrictedC_commutes_T datum theta).zpow_right n

private theorem yRestrictedC_commutes_dRestricted
    (x : DRestricted datum (HostYStage.FreeInput datum)
      (baseIntersections datum)) :
    Commute (yRestrictedC datum theta)
      (dRestrictedToYRestricted datum theta x) := by
  induction x using HNNExtension.induction_on with
  | of x =>
      rw [dRestrictedToYRestricted_of]
      exact yRestrictedC_commutes_dCyclic datum theta x
  | t =>
      rw [dRestrictedToYRestricted_t]
      simpa [yRestrictedY] using
        (yRestrictedC_commutes_Y datum theta).inv_right
  | mul x x' hx hx' =>
      rw [map_mul]
      exact hx.mul_right hx'
  | inv x hx =>
      rw [map_inv]
      exact hx.inv_right

private theorem yRestrictedC_commutes_CD
    (x : CD datum (HostYStage.FreeInput datum)) :
    Commute (yRestrictedC datum theta) (CDToYRestricted datum theta x) :=
  yRestrictedC_commutes_dRestricted datum theta
    ((dRestrictedEquivCD datum (HostYStage.FreeInput datum)
      (baseIntersections datum)).symm x)

/-- The HNN-extension homomorphism from the source model to the restricted `y` model. -/
def sourceModelToYRestricted :
    SourceModel datum →* YRestricted datum theta :=
  HNNExtension.lift (CDToYRestricted datum theta)
    (yRestrictedC datum theta) (by
      intro a
      have hcomm := yRestrictedC_commutes_CD datum theta (a :
        CD datum (HostYStage.FreeInput datum))
      simpa [sourceRestrictedPhi, restrictedPhi] using hcomm.eq)

@[simp] private theorem sourceModelToYRestricted_of
    (x : CD datum (HostYStage.FreeInput datum)) :
    sourceModelToYRestricted datum theta (HNNExtension.of x) =
      CDToYRestricted datum theta x := by
  simp [sourceModelToYRestricted]

@[simp] private theorem sourceModelToYRestricted_t :
    sourceModelToYRestricted datum theta HNNExtension.t =
      yRestrictedC datum theta := by
  simp [sourceModelToYRestricted]

@[simp] private theorem sourceModelToYRestricted_d :
    sourceModelToYRestricted datum theta (sourceModelD datum) =
      yRestrictedT datum theta := by
  change sourceModelToYRestricted datum theta (HNNExtension.of (dInCD datum)) = _
  rw [sourceModelToYRestricted_of, CDToYRestricted_d]

@[simp] private theorem sourceModelToYRestricted_c :
    sourceModelToYRestricted datum theta (sourceModelC datum) =
      yRestrictedY datum theta := by
  change sourceModelToYRestricted datum theta (HNNExtension.of (cInCD datum)) = _
  rw [sourceModelToYRestricted_of, CDToYRestricted_c]

/-! ## The reverse map on the exact `CT` and `Kc` models -/

private theorem sourceModelT_commutes_base
    (x : CD datum (HostYStage.FreeInput datum)) :
    Commute (sourceModelT datum) (HNNExtension.of x : SourceModel datum) := by
  apply restrictedEmbedding_injective
    (CD datum (HostYStage.FreeInput datum)) (source_mem_iff datum)
  change sourceToTStage datum
      (sourceModelT datum * (HNNExtension.of x : SourceModel datum)) =
    sourceToTStage datum
      ((HNNExtension.of x : SourceModel datum) * sourceModelT datum)
  simp only [map_mul, sourceToTStage_of]
  exact ((centralizerOf_commute_stable_iff
    (CD datum (HostYStage.FreeInput datum))
    (x : Gamma2 datum (HostYStage.FreeInput datum))).2 x.property).symm.eq

private theorem sourceModelD_commutes_T :
    Commute (sourceModelD datum) (sourceModelT datum) :=
  (sourceModelT_commutes_base datum (dInCD datum)).symm

private theorem sourceModelT_commutes_C :
    Commute (sourceModelT datum) (sourceModelC datum) :=
  sourceModelT_commutes_base datum (cInCD datum)

/-- The cyclic base map `c ↦ T` for the exact `CT` model.  The sign in
the exponent homomorphism compensates for the convention that the paper's
`c` is Mathlib's first HNN stable letter inverse. -/
def C0ToSourceModel :
    HostZBaseIntersections.C0 datum →* SourceModel datum :=
  (zpowersHom (SourceModel datum) (sourceModelT datum)⁻¹).comp
    ((cExponent datum (HostYStage.FreeInput datum)).comp
      (HostZBaseIntersections.C0 datum).subtype)

@[simp] private theorem C0ToSourceModel_c :
    C0ToSourceModel datum (HostKcModel.cInC0 datum) =
      sourceModelT datum := by
  simp [C0ToSourceModel, HostKcModel.cInC0, sourceModelT]

private theorem sourceModelD_commutes_C0Image
    (x : HostZBaseIntersections.C0 datum) :
    Commute (sourceModelD datum) (C0ToSourceModel datum x) := by
  change Commute (sourceModelD datum)
    (((sourceModelT datum)⁻¹) ^
      Multiplicative.toAdd
        (cExponent datum (HostYStage.FreeInput datum) (x :
          Gamma2 datum (HostYStage.FreeInput datum))))
  exact ((sourceModelD_commutes_T datum).inv_right).zpow_right _

/-- The HNN-extension homomorphism from the `c,t` model to the source model. -/
def CTModelToSourceModel :
    HostKcModel.CTModel datum →* SourceModel datum :=
  HNNExtension.lift (C0ToSourceModel datum) (sourceModelD datum) (by
    intro a
    have hcomm := sourceModelD_commutes_C0Image datum (a :
      HostZBaseIntersections.C0 datum)
    simpa [restrictedPhi] using hcomm.eq)

@[simp] private theorem CTModelToSourceModel_of
    (x : HostZBaseIntersections.C0 datum) :
    CTModelToSourceModel datum (HNNExtension.of x) =
      C0ToSourceModel datum x := by
  simp [CTModelToSourceModel]

@[simp] private theorem CTModelToSourceModel_t :
    CTModelToSourceModel datum HNNExtension.t = sourceModelD datum := by
  simp [CTModelToSourceModel]

/-- The homomorphism from the `c,t` subgroup to the source model. -/
def CTToSourceModel :
    HostZBaseIntersections.CT datum →* SourceModel datum :=
  (CTModelToSourceModel datum).comp
    ((HostKcModel.ctModelEquivCT datum).symm.toMonoidHom)

@[simp] private theorem CTToSourceModel_c :
    CTToSourceModel datum (HostKcModel.baseC datum) =
      sourceModelT datum := by
  have hpre :
      (HostKcModel.ctModelEquivCT datum).symm
          (HostKcModel.baseC datum) =
        HostKcModel.ctModelC datum := by
    rw [← HostKcModel.ctModelEquivCT_c]
    exact (HostKcModel.ctModelEquivCT datum).symm_apply_apply _
  change CTModelToSourceModel datum
    ((HostKcModel.ctModelEquivCT datum).symm
      (HostKcModel.baseC datum)) = _
  rw [hpre]
  simp [HostKcModel.ctModelC]

@[simp] private theorem CTToSourceModel_t :
    CTToSourceModel datum (HostKcModel.baseT datum) =
      sourceModelD datum := by
  have hpre :
      (HostKcModel.ctModelEquivCT datum).symm
          (HostKcModel.baseT datum) =
        HostKcModel.ctModelT datum := by
    rw [← HostKcModel.ctModelEquivCT_t]
    exact (HostKcModel.ctModelEquivCT datum).symm_apply_apply _
  change CTModelToSourceModel datum
    ((HostKcModel.ctModelEquivCT datum).symm
      (HostKcModel.baseT datum)) = _
  rw [hpre]
  simp [HostKcModel.ctModelT]

/-- The homomorphism placing the cyclic `c` subgroup in the `c,t` subgroup. -/
def C0ToCT :
    HostZBaseIntersections.C0 datum →*
      HostZBaseIntersections.CT datum where
  toFun x :=
    ⟨toTStage datum (HostYStage.FreeInput datum)
        (x : Gamma2 datum (HostYStage.FreeInput datum)), by
      apply Subgroup.subset_closure
      left
      exact ⟨(x : Gamma2 datum (HostYStage.FreeInput datum)),
        x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (toTStage datum (HostYStage.FreeInput datum))
  map_mul' x x' := by
    apply Subtype.ext
    exact map_mul (toTStage datum (HostYStage.FreeInput datum))
      (x : Gamma2 datum (HostYStage.FreeInput datum))
      (x' : Gamma2 datum (HostYStage.FreeInput datum))

@[simp] private theorem ctModelEquivCT_of_C0
    (x : HostZBaseIntersections.C0 datum) :
    HostKcModel.ctModelEquivCT datum (HNNExtension.of x) =
      C0ToCT datum x := by
  apply Subtype.ext
  rw [HostKcModel.ctModelEquivCT_coe]
  simp [HostKcModel.ctModelEmbedding, C0ToCT, toTStage, centralizerOf]

@[simp] private theorem CTToSourceModel_C0
    (x : HostZBaseIntersections.C0 datum) :
    CTToSourceModel datum (C0ToCT datum x) =
      C0ToSourceModel datum x := by
  rw [← ctModelEquivCT_of_C0]
  change CTModelToSourceModel datum
    ((HostKcModel.ctModelEquivCT datum).symm
      (HostKcModel.ctModelEquivCT datum (HNNExtension.of x))) = _
  rw [(HostKcModel.ctModelEquivCT datum).symm_apply_apply]
  exact CTModelToSourceModel_of datum x

private theorem C0ToCT_cInC0 :
    C0ToCT datum (HostKcModel.cInC0 datum) =
      HostKcModel.baseC datum := by
  rw [← ctModelEquivCT_of_C0]
  simpa [HostKcModel.ctModelC] using
    HostKcModel.ctModelEquivCT_c datum

private theorem ctModelEquivCT_stable :
    HostKcModel.ctModelEquivCT datum HNNExtension.t =
      HostKcModel.baseT datum := by
  simpa [HostKcModel.ctModelT] using
    HostKcModel.ctModelEquivCT_t datum

private theorem restrictedA_element_eq_C0ToCT
    (a : restrictedA
      (A := KSubgroup datum (HostYStage.FreeInput datum))
      (HostZBaseIntersections.CT datum)) :
    ∃ x : HostZBaseIntersections.C0 datum,
      (a : HostZBaseIntersections.CT datum) = C0ToCT datum x := by
  have ha : (a : HostZBaseIntersections.CT datum) ∈
      HostKcModel.C0InCT datum :=
    (SetLike.ext_iff.mp (HostKcModel.restrictedA_eq_C0InCT datum)
      (a : HostZBaseIntersections.CT datum)).mp a.property
  change
    (((a : HostZBaseIntersections.CT datum) :
        TStage datum (HostYStage.FreeInput datum))) ∈
      HostZBaseIntersections.C0InT datum at ha
  rcases ha with ⟨x, hx, hxa⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxa.symm

/-- The conjugate `c⁻¹ d c` in the source model. -/
def sourceConjugatedD : SourceModel datum :=
  (sourceModelC datum)⁻¹ * sourceModelD datum * sourceModelC datum

private theorem sourceConjugatedD_commutes_T :
    Commute (sourceConjugatedD datum) (sourceModelT datum) :=
  ((sourceModelT_commutes_C datum).symm.inv_left.mul_left
    (sourceModelD_commutes_T datum)).mul_left
      (sourceModelT_commutes_C datum).symm

private theorem sourceConjugatedD_commutes_C0Image
    (x : HostZBaseIntersections.C0 datum) :
    Commute (sourceConjugatedD datum) (C0ToSourceModel datum x) := by
  change Commute (sourceConjugatedD datum)
    (((sourceModelT datum)⁻¹) ^
      Multiplicative.toAdd
        (cExponent datum (HostYStage.FreeInput datum) (x :
          Gamma2 datum (HostYStage.FreeInput datum))))
  exact ((sourceConjugatedD_commutes_T datum).inv_right).zpow_right _

/-- The homomorphism from the restricted `k,c` model to the source model. -/
def RestrictedToSourceModel :
    HostKcModel.Restricted datum →* SourceModel datum :=
  HNNExtension.lift (CTToSourceModel datum) (sourceConjugatedD datum) (by
    intro a
    rw [restrictedPhi_refl_coe]
    rcases restrictedA_element_eq_C0ToCT datum a with ⟨x, hx⟩
    have hcomm := sourceConjugatedD_commutes_C0Image datum x
    rw [hx, CTToSourceModel_C0]
    exact hcomm.eq)

@[simp] private theorem RestrictedToSourceModel_of
    (x : HostZBaseIntersections.CT datum) :
    RestrictedToSourceModel datum (HNNExtension.of x) =
      CTToSourceModel datum x := by
  simp [RestrictedToSourceModel]

@[simp] private theorem RestrictedToSourceModel_k :
    RestrictedToSourceModel datum HNNExtension.t =
      sourceConjugatedD datum := by
  simp [RestrictedToSourceModel]

@[simp] private theorem RestrictedToSourceModel_t :
    RestrictedToSourceModel datum (HostKcModel.restrictedT datum) =
      sourceModelD datum := by
  simp [HostKcModel.restrictedT]

@[simp] private theorem RestrictedToSourceModel_c :
    RestrictedToSourceModel datum (HostKcModel.restrictedC datum) =
      sourceModelT datum := by
  simp [HostKcModel.restrictedC]

/-- The generator `k` regarded as an element of the `k,c` subgroup. -/
def kInKc : Kc datum :=
  ⟨HostYStage.k datum, by
    apply Subgroup.subset_closure
    exact Or.inr rfl⟩

/-- The generator `t` regarded as an element of the `k,c` subgroup. -/
def tInKc : Kc datum :=
  ⟨HostYStage.t datum,
    CTInGamma_le_Kc datum (t_mem_CTInGamma datum)⟩

/-- The generator `c` regarded as an element of the `k,c` subgroup. -/
def cInKc : Kc datum :=
  ⟨HostYStage.c datum,
    CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩

/-- The homomorphism from the `k,c` subgroup to the source model. -/
def KcToSourceModel : Kc datum →* SourceModel datum :=
  (RestrictedToSourceModel datum).comp
    ((HostKcModel.restrictedEquivKc datum).symm.toMonoidHom)

@[simp] private theorem KcToSourceModel_t :
    KcToSourceModel datum (tInKc datum) = sourceModelD datum := by
  have hpre :
      (HostKcModel.restrictedEquivKc datum).symm (tInKc datum) =
        HostKcModel.restrictedT datum := by
    apply (HostKcModel.restrictedEquivKc datum).injective
    rw [(HostKcModel.restrictedEquivKc datum).apply_symm_apply]
    simp [tInKc]
  change RestrictedToSourceModel datum
    ((HostKcModel.restrictedEquivKc datum).symm (tInKc datum)) = _
  rw [hpre]
  exact RestrictedToSourceModel_t datum

@[simp] private theorem KcToSourceModel_c :
    KcToSourceModel datum (cInKc datum) = sourceModelT datum := by
  have hpre :
      (HostKcModel.restrictedEquivKc datum).symm (cInKc datum) =
        HostKcModel.restrictedC datum := by
    apply (HostKcModel.restrictedEquivKc datum).injective
    rw [(HostKcModel.restrictedEquivKc datum).apply_symm_apply]
    simp [cInKc]
  change RestrictedToSourceModel datum
    ((HostKcModel.restrictedEquivKc datum).symm (cInKc datum)) = _
  rw [hpre]
  exact RestrictedToSourceModel_c datum

@[simp] private theorem KcToSourceModel_k :
    KcToSourceModel datum (kInKc datum) = sourceConjugatedD datum := by
  have hpre :
      (HostKcModel.restrictedEquivKc datum).symm (kInKc datum) =
        HostKcModel.restrictedK datum := by
    apply (HostKcModel.restrictedEquivKc datum).injective
    rw [(HostKcModel.restrictedEquivKc datum).apply_symm_apply]
    simp [kInKc]
  change RestrictedToSourceModel datum
    ((HostKcModel.restrictedEquivKc datum).symm (kInKc datum)) = _
  rw [hpre]
  exact RestrictedToSourceModel_k datum

/-- The homomorphism obtained by composing the subgroup map `θ` with the source-model map. -/
def thetaThenKcToSourceModel :
    HostZBaseIntersections.CT datum →* SourceModel datum :=
  (KcToSourceModel datum).comp (HostThetaCT.thetaCTtoKc datum theta)

/-- The conjugated homomorphism from the `c,t` subgroup to the source model. -/
def conjugatedCTToSourceModel :
    HostZBaseIntersections.CT datum →* SourceModel datum :=
  ((MulAut.conj (sourceModelC datum)⁻¹).toMonoidHom).comp
    (CTToSourceModel datum)

private theorem thetaThenKcToSourceModel_c :
    thetaThenKcToSourceModel datum theta (HostKcModel.baseC datum) =
      sourceModelT datum := by
  change KcToSourceModel datum
    (HostThetaCT.thetaCTtoKc datum theta (HostKcModel.baseC datum)) = _
  rw [HostThetaCT.thetaCTtoKc_baseC]
  exact KcToSourceModel_c datum

private theorem thetaThenKcToSourceModel_t :
    thetaThenKcToSourceModel datum theta (HostKcModel.baseT datum) =
      sourceConjugatedD datum := by
  change KcToSourceModel datum
    (HostThetaCT.thetaCTtoKc datum theta (HostKcModel.baseT datum)) = _
  rw [HostThetaCT.thetaCTtoKc_baseT]
  exact KcToSourceModel_k datum

private theorem conjugatedCTToSourceModel_c :
    conjugatedCTToSourceModel datum (HostKcModel.baseC datum) =
      sourceModelT datum := by
  change
    (sourceModelC datum)⁻¹ *
        CTToSourceModel datum (HostKcModel.baseC datum) *
      ((sourceModelC datum)⁻¹)⁻¹ = _
  rw [CTToSourceModel_c]
  exact ((sourceModelT_commutes_C datum).symm.inv_left).mul_inv_cancel

private theorem conjugatedCTToSourceModel_t :
    conjugatedCTToSourceModel datum (HostKcModel.baseT datum) =
      sourceConjugatedD datum := by
  simp [conjugatedCTToSourceModel, sourceConjugatedD]

private theorem thetaThenKcToSourceModel_eq_conjugated :
    thetaThenKcToSourceModel datum theta =
      conjugatedCTToSourceModel datum := by
  have hmodel :
      (thetaThenKcToSourceModel datum theta).comp
          (HostKcModel.ctModelEquivCT datum).toMonoidHom =
        (conjugatedCTToSourceModel datum).comp
          (HostKcModel.ctModelEquivCT datum).toMonoidHom := by
    apply HNNExtension.hom_ext
    · apply MonoidHom.ext
      intro x
      rcases Subgroup.mem_closure_singleton.mp x.property with ⟨n, hn⟩
      have hx : x = HostKcModel.cInC0 datum ^ n := by
        apply Subtype.ext
        exact hn.symm
      rw [hx]
      simp only [map_zpow]
      apply congrArg (fun q : SourceModel datum ↦ q ^ n)
      change thetaThenKcToSourceModel datum theta
          (HostKcModel.ctModelEquivCT datum
            (HNNExtension.of (HostKcModel.cInC0 datum))) =
        conjugatedCTToSourceModel datum
          (HostKcModel.ctModelEquivCT datum
            (HNNExtension.of (HostKcModel.cInC0 datum)))
      rw [ctModelEquivCT_of_C0, C0ToCT_cInC0]
      exact (thetaThenKcToSourceModel_c datum theta).trans
        (conjugatedCTToSourceModel_c datum).symm
    · change thetaThenKcToSourceModel datum theta
          (HostKcModel.ctModelEquivCT datum HNNExtension.t) =
        conjugatedCTToSourceModel datum
          (HostKcModel.ctModelEquivCT datum HNNExtension.t)
      rw [ctModelEquivCT_stable]
      exact (thetaThenKcToSourceModel_t datum theta).trans
        (conjugatedCTToSourceModel_t datum).symm
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hmodel
    ((HostKcModel.ctModelEquivCT datum).symm x)
  simpa using hx

/-- The subgroup homomorphism from the `c,t` subgroup to the `k,c` subgroup. -/
def CTToKc :
    HostZBaseIntersections.CT datum →* Kc datum where
  toFun x :=
    ⟨toFinalStage datum (HostYStage.FreeInput datum)
        (x : TStage datum (HostYStage.FreeInput datum)), by
      apply CTInGamma_le_Kc datum
      exact ⟨(x : TStage datum (HostYStage.FreeInput datum)),
        x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (toFinalStage datum (HostYStage.FreeInput datum))
  map_mul' x x' := by
    apply Subtype.ext
    exact map_mul (toFinalStage datum (HostYStage.FreeInput datum))
      (x : TStage datum (HostYStage.FreeInput datum))
      (x' : TStage datum (HostYStage.FreeInput datum))

@[simp] private theorem restrictedEquivKc_of_CT
    (x : HostZBaseIntersections.CT datum) :
    HostKcModel.restrictedEquivKc datum (HNNExtension.of x) =
      CTToKc datum x := by
  apply Subtype.ext
  rw [HostKcModel.restrictedEquivKc_coe]
  simp [HostKcModel.restrictedEmbeddingToGamma, CTToKc,
    toFinalStage, centralizerOf]

private theorem CTToKc_t :
    CTToKc datum (HostKcModel.baseT datum) = tInKc datum := by
  rw [← restrictedEquivKc_of_CT]
  simpa [HostKcModel.restrictedT, tInKc] using
    HostKcModel.restrictedEquivKc_t datum

private theorem CTToKc_c :
    CTToKc datum (HostKcModel.baseC datum) = cInKc datum := by
  rw [← restrictedEquivKc_of_CT]
  simpa [HostKcModel.restrictedC, cInKc] using
    HostKcModel.restrictedEquivKc_c datum

private theorem restrictedEquivKc_stable :
    HostKcModel.restrictedEquivKc datum HNNExtension.t = kInKc datum := by
  simpa [HostKcModel.restrictedK, kInKc] using
    HostKcModel.restrictedEquivKc_k datum

@[simp] private theorem KcToSourceModel_CT
    (x : HostZBaseIntersections.CT datum) :
    KcToSourceModel datum (CTToKc datum x) =
      CTToSourceModel datum x := by
  rw [← restrictedEquivKc_of_CT]
  change RestrictedToSourceModel datum
    ((HostKcModel.restrictedEquivKc datum).symm
      (HostKcModel.restrictedEquivKc datum (HNNExtension.of x))) = _
  rw [(HostKcModel.restrictedEquivKc datum).symm_apply_apply]
  exact RestrictedToSourceModel_of datum x

private theorem yRestrictedA_eq_CTToKc
    (a : YRestrictedA datum) :
    ∃ x : HostZBaseIntersections.CT datum,
      (a : Kc datum) = CTToKc datum x := by
  have hpair : (((a : Kc datum) : HostYStage.Gamma datum)) ∈
      Kc datum ⊓ HMinus datum := ⟨(a : Kc datum).property, a.property⟩
  rw [Kc_inf_HMinus datum] at hpair
  rcases hpair with ⟨x, hx, hxa⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxa.symm

private theorem yRestrictedPhi_eq_thetaCT
    (a : YRestrictedA datum)
    (x : HostZBaseIntersections.CT datum)
    (hax : (a : Kc datum) = CTToKc datum x) :
    ((yRestrictedPhi datum theta a : YRestrictedB datum) : Kc datum) =
      HostThetaCT.thetaCTtoKc datum theta x := by
  have hminus :
      (⟨(((a : Kc datum) : HostYStage.Gamma datum)), a.property⟩ :
          HMinus datum) =
        HostThetaCT.ctToHMinus datum x := by
    apply Subtype.ext
    have hv := congrArg
      (fun q : Kc datum ↦ (q : HostYStage.Gamma datum)) hax
    simpa [CTToKc, HostThetaCT.ctToHMinus] using hv
  apply Subtype.ext
  change
    ((theta.equiv
      (⟨(((a : Kc datum) : HostYStage.Gamma datum)), a.property⟩ :
        HMinus datum) : HPlus datum) : HostYStage.Gamma datum) =
      ((theta.equiv (HostThetaCT.ctToHMinus datum x) : HPlus datum) :
        HostYStage.Gamma datum)
  rw [hminus]

theorem yRestrictedCompatibility
    (a : YRestrictedA datum) :
    (sourceModelC datum)⁻¹ *
        KcToSourceModel datum (a : Kc datum) =
      KcToSourceModel datum
          (((yRestrictedPhi datum theta a : YRestrictedB datum) : Kc datum)) *
        (sourceModelC datum)⁻¹ := by
  rcases yRestrictedA_eq_CTToKc datum a with ⟨x, hax⟩
  have hphi := yRestrictedPhi_eq_thetaCT datum theta a x hax
  have htheta := DFunLike.congr_fun
    (thetaThenKcToSourceModel_eq_conjugated datum theta) x
  rw [hax, hphi, KcToSourceModel_CT]
  change (sourceModelC datum)⁻¹ * CTToSourceModel datum x =
    thetaThenKcToSourceModel datum theta x * (sourceModelC datum)⁻¹
  rw [htheta]
  simp [conjugatedCTToSourceModel, mul_assoc]

/-- The HNN-extension homomorphism from the restricted `y` model to the source model. -/
def YRestrictedToSourceModel :
    YRestricted datum theta →* SourceModel datum :=
  HNNExtension.lift (KcToSourceModel datum) (sourceModelC datum)⁻¹
    (yRestrictedCompatibility datum theta)

@[simp] private theorem YRestrictedToSourceModel_of (x : Kc datum) :
    YRestrictedToSourceModel datum theta (HNNExtension.of x) =
      KcToSourceModel datum x := by
  simp [YRestrictedToSourceModel]

@[simp] private theorem YRestrictedToSourceModel_stable :
    YRestrictedToSourceModel datum theta HNNExtension.t =
      (sourceModelC datum)⁻¹ := by
  simp [YRestrictedToSourceModel]

@[simp] private theorem YRestrictedToSourceModel_t :
    YRestrictedToSourceModel datum theta (yRestrictedT datum theta) =
      sourceModelD datum := by
  change YRestrictedToSourceModel datum theta (HNNExtension.of (tInKc datum)) = _
  rw [YRestrictedToSourceModel_of, KcToSourceModel_t]

@[simp] private theorem YRestrictedToSourceModel_c :
    YRestrictedToSourceModel datum theta (yRestrictedC datum theta) =
      sourceModelT datum := by
  change YRestrictedToSourceModel datum theta (HNNExtension.of (cInKc datum)) = _
  rw [YRestrictedToSourceModel_of, KcToSourceModel_c]

@[simp] private theorem YRestrictedToSourceModel_y :
    YRestrictedToSourceModel datum theta (yRestrictedY datum theta) =
      sourceModelC datum := by
  simp [yRestrictedY]

private theorem CD_hom_ext {Q : Type*} [Group Q]
    {f g : CD datum (HostYStage.FreeInput datum) →* Q}
    (hd : f (dInCD datum) = g (dInCD datum))
    (hc : f (cInCD datum) = g (cInCD datum)) :
    f = g := by
  apply MonoidHom.ext
  intro x
  let p : (q : Gamma2 datum (HostYStage.FreeInput datum)) →
      q ∈ CD datum (HostYStage.FreeInput datum) → Prop :=
    fun q hq ↦ f ⟨q, hq⟩ = g ⟨q, hq⟩
  have hp : p (x : Gamma2 datum (HostYStage.FreeInput datum)) x.property := by
    apply Subgroup.closure_induction
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · simpa [p, cInCD] using hc
      · simpa [p, dInCD] using hd
    · change f 1 = g 1
      rw [map_one, map_one]
    · intro a b ha hb hpa hpb
      let aa : CD datum (HostYStage.FreeInput datum) :=
        ⟨a, show a ∈ CD datum (HostYStage.FreeInput datum) from ha⟩
      let bb : CD datum (HostYStage.FreeInput datum) :=
        ⟨b, show b ∈ CD datum (HostYStage.FreeInput datum) from hb⟩
      change f aa = g aa at hpa
      change f bb = g bb at hpb
      change f (aa * bb) = g (aa * bb)
      rw [map_mul, map_mul]
      exact congrArg₂ (fun u v : Q ↦ u * v) hpa hpb
    · intro a ha hpa
      let aa : CD datum (HostYStage.FreeInput datum) :=
        ⟨a, show a ∈ CD datum (HostYStage.FreeInput datum) from ha⟩
      change f aa = g aa at hpa
      change f aa⁻¹ = g aa⁻¹
      rw [map_inv, map_inv]
      exact congrArg (fun u : Q ↦ u⁻¹) hpa
  simpa [p] using hp

theorem YRestrictedToSourceModel_comp_sourceModelToYRestricted :
    (YRestrictedToSourceModel datum theta).comp
        (sourceModelToYRestricted datum theta) =
      MonoidHom.id (SourceModel datum) := by
  apply HNNExtension.hom_ext
  · apply CD_hom_ext datum
    · change YRestrictedToSourceModel datum theta
        (sourceModelToYRestricted datum theta (sourceModelD datum)) =
          sourceModelD datum
      rw [sourceModelToYRestricted_d, YRestrictedToSourceModel_t]
    · change YRestrictedToSourceModel datum theta
        (sourceModelToYRestricted datum theta (sourceModelC datum)) =
          sourceModelC datum
      rw [sourceModelToYRestricted_c, YRestrictedToSourceModel_y]
  · change YRestrictedToSourceModel datum theta
      (sourceModelToYRestricted datum theta (sourceModelT datum)) =
        sourceModelT datum
    change YRestrictedToSourceModel datum theta
      (sourceModelToYRestricted datum theta HNNExtension.t) =
        sourceModelT datum
    rw [sourceModelToYRestricted_t, YRestrictedToSourceModel_c]

private theorem CT_hom_ext {Q : Type*} [Group Q]
    {f g : HostZBaseIntersections.CT datum →* Q}
    (ht : f (HostKcModel.baseT datum) = g (HostKcModel.baseT datum))
    (hc : f (HostKcModel.baseC datum) = g (HostKcModel.baseC datum)) :
    f = g := by
  have hmodel :
      f.comp (HostKcModel.ctModelEquivCT datum).toMonoidHom =
        g.comp (HostKcModel.ctModelEquivCT datum).toMonoidHom := by
    apply HNNExtension.hom_ext
    · apply MonoidHom.ext
      intro x
      rcases Subgroup.mem_closure_singleton.mp x.property with ⟨n, hn⟩
      have hx : x = HostKcModel.cInC0 datum ^ n := by
        apply Subtype.ext
        exact hn.symm
      rw [hx]
      simp only [map_zpow]
      apply congrArg (fun q : Q ↦ q ^ n)
      change f (HostKcModel.ctModelEquivCT datum
          (HNNExtension.of (HostKcModel.cInC0 datum))) =
        g (HostKcModel.ctModelEquivCT datum
          (HNNExtension.of (HostKcModel.cInC0 datum)))
      rw [ctModelEquivCT_of_C0, C0ToCT_cInC0]
      exact hc
    · change f (HostKcModel.ctModelEquivCT datum HNNExtension.t) =
        g (HostKcModel.ctModelEquivCT datum HNNExtension.t)
      rw [ctModelEquivCT_stable]
      exact ht
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hmodel
    ((HostKcModel.ctModelEquivCT datum).symm x)
  simpa using hx

private theorem Kc_hom_ext {Q : Type*} [Group Q]
    {f g : Kc datum →* Q}
    (ht : f (tInKc datum) = g (tInKc datum))
    (hc : f (cInKc datum) = g (cInKc datum))
    (hk : f (kInKc datum) = g (kInKc datum)) :
    f = g := by
  have hmodel :
      f.comp (HostKcModel.restrictedEquivKc datum).toMonoidHom =
        g.comp (HostKcModel.restrictedEquivKc datum).toMonoidHom := by
    apply HNNExtension.hom_ext
    · apply CT_hom_ext datum
      · change f (HostKcModel.restrictedEquivKc datum
            (HNNExtension.of (HostKcModel.baseT datum))) =
          g (HostKcModel.restrictedEquivKc datum
            (HNNExtension.of (HostKcModel.baseT datum)))
        rw [restrictedEquivKc_of_CT, CTToKc_t]
        exact ht
      · change f (HostKcModel.restrictedEquivKc datum
            (HNNExtension.of (HostKcModel.baseC datum))) =
          g (HostKcModel.restrictedEquivKc datum
            (HNNExtension.of (HostKcModel.baseC datum)))
        rw [restrictedEquivKc_of_CT, CTToKc_c]
        exact hc
    · change f (HostKcModel.restrictedEquivKc datum HNNExtension.t) =
        g (HostKcModel.restrictedEquivKc datum HNNExtension.t)
      rw [restrictedEquivKc_stable]
      exact hk
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun hmodel
    ((HostKcModel.restrictedEquivKc datum).symm x)
  simpa using hx

private theorem yRestricted_conjugates_t :
    (yRestrictedY datum theta)⁻¹ * yRestrictedT datum theta *
        yRestrictedY datum theta =
      (HNNExtension.of (kInKc datum) : YRestricted datum theta) := by
  apply yRestrictedEmbedding_injective datum theta
  simp only [map_mul, map_inv]
  change (y datum theta)⁻¹ * tY datum theta * y datum theta =
    kY datum theta
  exact y_conjugates_t datum theta

theorem sourceModelToYRestricted_comp_YRestrictedToSourceModel :
    (sourceModelToYRestricted datum theta).comp
        (YRestrictedToSourceModel datum theta) =
      MonoidHom.id (YRestricted datum theta) := by
  apply HNNExtension.hom_ext
  · apply Kc_hom_ext datum
    · change sourceModelToYRestricted datum theta
        (YRestrictedToSourceModel datum theta
          (HNNExtension.of (tInKc datum))) =
        (HNNExtension.of (tInKc datum) : YRestricted datum theta)
      rw [YRestrictedToSourceModel_of, KcToSourceModel_t,
        sourceModelToYRestricted_d]
      rfl
    · change sourceModelToYRestricted datum theta
        (YRestrictedToSourceModel datum theta
          (HNNExtension.of (cInKc datum))) =
        (HNNExtension.of (cInKc datum) : YRestricted datum theta)
      rw [YRestrictedToSourceModel_of, KcToSourceModel_c,
        show sourceModelT datum = HNNExtension.t by rfl,
        sourceModelToYRestricted_t]
      rfl
    · change sourceModelToYRestricted datum theta
        (YRestrictedToSourceModel datum theta
          (HNNExtension.of (kInKc datum))) =
        (HNNExtension.of (kInKc datum) : YRestricted datum theta)
      rw [YRestrictedToSourceModel_of, KcToSourceModel_k]
      change sourceModelToYRestricted datum theta
          ((sourceModelC datum)⁻¹ * sourceModelD datum *
            sourceModelC datum) = _
      rw [map_mul, map_mul, map_inv, sourceModelToYRestricted_c,
        sourceModelToYRestricted_d]
      exact yRestricted_conjugates_t datum theta
  · change sourceModelToYRestricted datum theta
      (YRestrictedToSourceModel datum theta HNNExtension.t) =
        (HNNExtension.t : YRestricted datum theta)
    rw [YRestrictedToSourceModel_stable, map_inv,
      sourceModelToYRestricted_c]
    simp [yRestrictedY]

/-- The equivalence identifying the source model with the restricted `y` model. -/
def sourceModelEquivYRestricted :
    SourceModel datum ≃* YRestricted datum theta where
  toFun := sourceModelToYRestricted datum theta
  invFun := YRestrictedToSourceModel datum theta
  left_inv x := DFunLike.congr_fun
    (YRestrictedToSourceModel_comp_sourceModelToYRestricted datum theta) x
  right_inv x := DFunLike.congr_fun
    (sourceModelToYRestricted_comp_YRestrictedToSourceModel datum theta) x
  map_mul' x x' := map_mul (sourceModelToYRestricted datum theta) x x'

/-! ## Public interface for the path rotation -/

/-- The source generator `d` in the subgroup generated by `d,t,c`. -/
def sourceD : DTC datum theta := ⟨dY datum theta, dY_mem_DTC datum theta⟩
/-- The source generator `t` in the subgroup generated by `d,t,c`. -/
def sourceT : DTC datum theta := ⟨tY datum theta, tY_mem_DTC datum theta⟩
/-- The source generator `c` in the subgroup generated by `d,t,c`. -/
def sourceC : DTC datum theta := ⟨cY datum theta, cY_mem_DTC datum theta⟩

/-- The target generator `t` in the subgroup generated by `t,c,y`. -/
def targetT : TCY datum theta := ⟨tY datum theta, tY_mem_TCY datum theta⟩
/-- The target generator `c` in the subgroup generated by `t,c,y`. -/
def targetC : TCY datum theta := ⟨cY datum theta, cY_mem_TCY datum theta⟩
/-- The target generator `y` in the subgroup generated by `t,c,y`. -/
def targetY : TCY datum theta := ⟨y datum theta, y_mem_TCY datum theta⟩

/-- The path rotation following Lemma 3.2, obtained by transporting the exact
restricted presentations of `⟨d,t,c⟩` and `⟨t,c,y⟩`. -/
def pathEquiv : DTC datum theta ≃* TCY datum theta :=
  (sourceModelEquivDTC datum theta).symm.trans
    ((sourceModelEquivYRestricted datum theta).trans
      (yRestrictedEquivTCY datum theta))

@[simp] theorem pathEquiv_d :
    pathEquiv datum theta (sourceD datum theta) = targetT datum theta := by
  have hpre :
      (sourceModelEquivDTC datum theta).symm (sourceD datum theta) =
        sourceModelD datum := by
    apply (sourceModelEquivDTC datum theta).injective
    rw [(sourceModelEquivDTC datum theta).apply_symm_apply]
    simp [sourceD]
  change yRestrictedEquivTCY datum theta
    (sourceModelToYRestricted datum theta
      ((sourceModelEquivDTC datum theta).symm (sourceD datum theta))) = _
  rw [hpre, sourceModelToYRestricted_d, yRestrictedEquivTCY_t]
  rfl

@[simp] theorem pathEquiv_t :
    pathEquiv datum theta (sourceT datum theta) = targetC datum theta := by
  have hpre :
      (sourceModelEquivDTC datum theta).symm (sourceT datum theta) =
        sourceModelT datum := by
    apply (sourceModelEquivDTC datum theta).injective
    rw [(sourceModelEquivDTC datum theta).apply_symm_apply]
    simp [sourceT]
  change yRestrictedEquivTCY datum theta
    (sourceModelToYRestricted datum theta
      ((sourceModelEquivDTC datum theta).symm (sourceT datum theta))) = _
  rw [hpre, show sourceModelT datum = HNNExtension.t by rfl,
    sourceModelToYRestricted_t, yRestrictedEquivTCY_c]
  rfl

@[simp] theorem pathEquiv_c :
    pathEquiv datum theta (sourceC datum theta) = targetY datum theta := by
  have hpre :
      (sourceModelEquivDTC datum theta).symm (sourceC datum theta) =
        sourceModelC datum := by
    apply (sourceModelEquivDTC datum theta).injective
    rw [(sourceModelEquivDTC datum theta).apply_symm_apply]
    simp [sourceC]
  change yRestrictedEquivTCY datum theta
    (sourceModelToYRestricted datum theta
      ((sourceModelEquivDTC datum theta).symm (sourceC datum theta))) = _
  rw [hpre, sourceModelToYRestricted_c, yRestrictedEquivTCY_y]
  rfl

/-- The exact output of the path-presentation calculation in Lemma 3.2.
Keeping the generator equations with the equivalence makes all later
Tietze calculations independent of its normal-form implementation. -/
structure ZetaData where
  /-- The subgroup equivalence used to define the final HNN extension. -/
  equiv : DTC datum theta ≃* TCY datum theta
  map_d : equiv (sourceD datum theta) = targetT datum theta
  map_t : equiv (sourceT datum theta) = targetC datum theta
  map_c : equiv (sourceC datum theta) = targetY datum theta

/-- The canonical attaching equivalence for the second compression. -/
def zetaData : ZetaData datum theta where
  equiv := pathEquiv datum theta
  map_d := pathEquiv_d datum theta
  map_t := pathEquiv_t datum theta
  map_c := pathEquiv_c datum theta

variable (zeta : ZetaData datum theta)

/-- The proper second HNN extension, once the path rotation following
Lemma 3.2 has been constructed. -/
abbrev ZStage :=
  HNNExtension (Y datum theta) (DTC datum theta) (TCY datum theta) zeta.equiv

/-- The canonical inclusion `G_y → G_z`. -/
def toZStage : Y datum theta →* ZStage datum theta zeta := HNNExtension.of

/-- The paper's `z`; Mathlib's stable letter is `z⁻¹`. -/
def zLetter : ZStage datum theta zeta :=
  (HNNExtension.t : ZStage datum theta zeta)⁻¹

theorem toZStage_injective : Function.Injective (toZStage datum theta zeta) :=
  HNNExtension.of_injective zeta.equiv

private theorem z_conjugates (x : DTC datum theta) :
    (zLetter datum theta zeta)⁻¹ *
        toZStage datum theta zeta (x : Y datum theta) *
        zLetter datum theta zeta =
      toZStage datum theta zeta
        ((zeta.equiv x : TCY datum theta) : Y datum theta) := by
  have h := HNNExtension.t_mul_of (φ := zeta.equiv) x
  change HNNExtension.t * HNNExtension.of (x : Y datum theta) *
      HNNExtension.t⁻¹ = _
  rw [h]
  simp [toZStage]

theorem z_conjugates_d :
    (zLetter datum theta zeta)⁻¹ *
        toZStage datum theta zeta (dY datum theta) *
        zLetter datum theta zeta =
      toZStage datum theta zeta (tY datum theta) := by
  rw [show dY datum theta = (sourceD datum theta : Y datum theta) by rfl]
  rw [z_conjugates, zeta.map_d]
  rfl

theorem z_conjugates_t :
    (zLetter datum theta zeta)⁻¹ *
        toZStage datum theta zeta (tY datum theta) *
        zLetter datum theta zeta =
      toZStage datum theta zeta (cY datum theta) := by
  rw [show tY datum theta = (sourceT datum theta : Y datum theta) by rfl]
  rw [z_conjugates, zeta.map_t]
  rfl

theorem z_conjugates_c :
    (zLetter datum theta zeta)⁻¹ *
        toZStage datum theta zeta (cY datum theta) *
        zLetter datum theta zeta =
      toZStage datum theta zeta (y datum theta) := by
  rw [show cY datum theta = (sourceC datum theta : Y datum theta) by rfl]
  rw [z_conjugates, zeta.map_c]
  rfl

end

end HostZStage
end Undecidability
