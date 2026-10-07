/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.YStage
public import LeanPool.SmallUndecidableGroups.Host.ZBaseIntersections

/-!
# The subgroup intersections for the second compression HNN extension

This file proves Proposition 3.8 of the paper inside the semantic Borisov group
`Gamma`.  Put `Kc = ⟨t,c,k⟩`.  Then

* `Kc ∩ HMinus = ⟨t,c⟩`, and
* `Kc ∩ HPlus  = ⟨c,k⟩`.

The first equality is the base-intersection theorem for a restricted HNN
extension.  The second follows from Lemma B.5 of the paper, using the
double-coset identity established in `ZBaseIntersections`.
-/

@[expose] public section

namespace Undecidability
namespace HostZIntersections

open BorisovCStage
open BorisovConverseCore
open BorisovFinalModel
open BorisovHNNModel
open HNNLemmas
open HostYStage
open HostZBaseIntersections

noncomputable section

variable (datum : Thue.StandingDatum)

/-- The proved rank-five freeness witness for the concrete host model. -/
abbrev FreeInput : RankFiveFree datum := HostYStage.FreeInput datum

/-- The embedded subgroup `⟨t,c⟩` of `Gamma`. -/
def CTInGamma : Subgroup (Gamma datum) :=
  (CT datum).map (toFinalStage datum (FreeInput datum))

/-- The embedded subgroup `⟨c⟩` of `Gamma`. -/
def CInGamma : Subgroup (Gamma datum) :=
  (C0InT datum).map (toFinalStage datum (FreeInput datum))

/-- `K_c = ⟨t,c,k⟩` in the semantic Borisov group. -/
def Kc : Subgroup (Gamma datum) :=
  generatedWith (CTInGamma datum) (k datum)

/-- The subgroup `⟨c,k⟩` in the semantic Borisov group. -/
def CKInGamma : Subgroup (Gamma datum) :=
  generatedWith (CInGamma datum) (k datum)

theorem c_mem_CInGamma : HostYStage.c datum ∈ CInGamma datum := by
  refine ⟨toTStage datum (FreeInput datum)
      (BorisovCStage.c datum (FreeInput datum)), ?_, rfl⟩
  exact ⟨BorisovCStage.c datum (FreeInput datum),
    Subgroup.subset_closure (by rfl), rfl⟩

theorem c_mem_CTInGamma : HostYStage.c datum ∈ CTInGamma datum := by
  refine ⟨toTStage datum (FreeInput datum)
      (BorisovCStage.c datum (FreeInput datum)), ?_, rfl⟩
  apply Subgroup.subset_closure
  left
  exact ⟨BorisovCStage.c datum (FreeInput datum),
    Subgroup.subset_closure (by rfl), rfl⟩

theorem t_mem_CTInGamma : t datum ∈ CTInGamma datum := by
  refine ⟨tLetter datum (FreeInput datum), ?_, rfl⟩
  apply Subgroup.subset_closure
  right
  rfl

theorem CTInGamma_le_Kc : CTInGamma datum ≤ Kc datum := by
  intro x hx
  apply Subgroup.subset_closure
  exact Or.inl hx

theorem c_mem_CKInGamma : HostYStage.c datum ∈ CKInGamma datum := by
  apply Subgroup.subset_closure
  exact Or.inl (c_mem_CInGamma datum)

theorem k_mem_CKInGamma : k datum ∈ CKInGamma datum := by
  apply Subgroup.subset_closure
  exact Or.inr rfl

theorem CKInGamma_le_Kc : CKInGamma datum ≤ Kc datum := by
  rw [CKInGamma, generatedWith, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · apply CTInGamma_le_Kc datum
    rcases hx with ⟨u, hu, rfl⟩
    rcases hu with ⟨a, ha, rfl⟩
    have hc : HostYStage.c datum ∈ CTInGamma datum :=
      c_mem_CTInGamma datum
    let S : Subgroup (CStage datum) :=
      (CTInGamma datum).comap
        ((toFinalStage datum (FreeInput datum)).comp
          (toTStage datum (FreeInput datum)))
    have hC0 : C0 datum ≤ S := (C0_le_iff datum).2 hc
    exact hC0 ha
  · have hx' : x = k datum := by simpa using hx
    subst x
    apply Subgroup.subset_closure
    exact Or.inr rfl

private theorem CTInGamma_le_of (S : Subgroup (Gamma datum))
    (hc : HostYStage.c datum ∈ S) (ht : t datum ∈ S) :
    CTInGamma datum ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  let Cpre : Subgroup (CStage datum) :=
    S.comap
      ((toFinalStage datum (FreeInput datum)).comp
        (toTStage datum (FreeInput datum)))
  have hC0 : C0 datum ≤ Cpre := (C0_le_iff datum).2 hc
  let Tpre : Subgroup (TStage datum (FreeInput datum)) :=
    S.comap (toFinalStage datum (FreeInput datum))
  have hbase :
      (C0 datum).map (toTStage datum (FreeInput datum)) ≤ Tpre := by
    rintro _ ⟨a, ha, rfl⟩
    exact hC0 ha
  rw [CT, generatedWith] at hx
  exact (Subgroup.closure_le Tpre).2 (by
    intro a ha
    rcases ha with ha | ha
    · exact hbase ha
    · have ha' : a = tLetter datum (FreeInput datum) := by simpa using ha
      subst a
      exact ht) hx

private theorem CInGamma_le_of (S : Subgroup (Gamma datum))
    (hc : HostYStage.c datum ∈ S) : CInGamma datum ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨a, ha, rfl⟩
  let Cpre : Subgroup (CStage datum) :=
    S.comap
      ((toFinalStage datum (FreeInput datum)).comp
        (toTStage datum (FreeInput datum)))
  have hC0 : C0 datum ≤ Cpre := (C0_le_iff datum).2 hc
  exact hC0 ha

private theorem CKInGamma_le_of (S : Subgroup (Gamma datum))
    (hc : HostYStage.c datum ∈ S) (hk : k datum ∈ S) :
    CKInGamma datum ≤ S := by
  rw [CKInGamma, generatedWith, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact CInGamma_le_of datum S hc hx
  · have hx' : x = k datum := by simpa using hx
    simpa [hx'] using hk

private theorem C0_maps_into_HMinus :
    C0 datum ≤
      (HMinus datum).comap
        ((toFinalStage datum (FreeInput datum)).comp
          (toTStage datum (FreeInput datum))) := by
  rw [C0_le_iff]
  simpa [HostYStage.c, modelC, cStageToFinal]
    using c_mem_HMinus datum

private theorem CT_maps_into_HMinus :
    CT datum ≤
      (HMinus datum).comap (toFinalStage datum (FreeInput datum)) := by
  rw [CT, generatedWith, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · rcases hx with ⟨a, ha, rfl⟩
    exact C0_maps_into_HMinus datum ha
  · have hx' : x = tLetter datum (FreeInput datum) := by simpa using hx
    subst x
    simpa [HostYStage.t, modelT] using t_mem_HMinus datum

theorem CTInGamma_le_HMinus : CTInGamma datum ≤ HMinus datum := by
  rw [CTInGamma, Subgroup.map_le_iff_le_comap]
  exact CT_maps_into_HMinus datum

private theorem HMinus_le_finalRange :
    HMinus datum ≤
      MonoidHom.range (toFinalStage datum (FreeInput datum)) := by
  rw [HMinus, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact ⟨toTStage datum (FreeInput datum)
        (of3 datum (FreeInput datum) d3), rfl⟩
  · exact ⟨toTStage datum (FreeInput datum)
        (of3 datum (FreeInput datum) e3), rfl⟩
  · exact ⟨toTStage datum (FreeInput datum)
        (BorisovCStage.c datum (FreeInput datum)), rfl⟩
  · exact ⟨tLetter datum (FreeInput datum), rfl⟩
  · exact ⟨toTStage datum (FreeInput datum)
        (of3 datum (FreeInput datum) firstStableInStageThree), rfl⟩

/-- The first equality of Proposition 3.8 of the paper:
`K_c ∩ H_y^- = ⟨t,c⟩`. -/
theorem Kc_inf_HMinus :
    Kc datum ⊓ HMinus datum = CTInGamma datum := by
  have hrestricted :
      Kc datum ⊓
          MonoidHom.range (toFinalStage datum (FreeInput datum)) =
        CTInGamma datum := by
    simpa [Kc, CTInGamma, generatedWith, generatedWithStable,
      HostYStage.k, modelK, toFinalStage, kLetter,
      centralizerOf, centralizerStable] using
      (generatedWithStable_inf_base
        (A := KSubgroup datum (FreeInput datum))
        (B := KSubgroup datum (FreeInput datum))
        (phi := MulEquiv.refl (KSubgroup datum (FreeInput datum)))
        (CT datum) (by intro a; rfl))
  ext x
  constructor
  · intro hx
    have hx' : x ∈ Kc datum ⊓
        MonoidHom.range (toFinalStage datum (FreeInput datum)) :=
      ⟨hx.1, HMinus_le_finalRange datum hx.2⟩
    rw [hrestricted] at hx'
    exact hx'
  · intro hx
    exact ⟨by
      apply Subgroup.subset_closure
      exact Or.inl hx, CTInGamma_le_HMinus datum hx⟩

private theorem B0_maps_into_HPlus :
    HostZBaseIntersections.B0 datum ≤
      (HPlus datum).comap
        ((toFinalStage datum (FreeInput datum)).comp
          (toTStage datum (FreeInput datum))) := by
  rw [HostZBaseIntersections.B0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simpa [HostYStage.d, modelD, cStageToFinal]
      using d_mem_HPlus datum
  · simpa [HostYStage.e, modelE, cStageToFinal]
      using e_mem_HPlus datum
  · simpa [HostYStage.c, modelC, cStageToFinal]
      using c_mem_HPlus datum
  · simpa [HostYStage.s2, modelS2, cStageToFinal]
      using s2_mem_HPlus datum

private theorem HPlus_eq_generatedWith_B0_k :
    HPlus datum =
      generatedWith
        ((B0InT datum).map (toFinalStage datum (FreeInput datum)))
        (k datum) := by
  apply le_antisymm
  · rw [HPlus, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply Subgroup.subset_closure
      left
      exact ⟨toTStage datum (FreeInput datum)
          (of3 datum (FreeInput datum) d3),
        ⟨of3 datum (FreeInput datum) d3,
          Subgroup.subset_closure (by
            simp), rfl⟩, rfl⟩
    · apply Subgroup.subset_closure
      left
      exact ⟨toTStage datum (FreeInput datum)
          (of3 datum (FreeInput datum) e3),
        ⟨of3 datum (FreeInput datum) e3,
          Subgroup.subset_closure (by
            simp), rfl⟩, rfl⟩
    · apply Subgroup.subset_closure
      left
      exact ⟨toTStage datum (FreeInput datum)
          (BorisovCStage.c datum (FreeInput datum)),
        ⟨BorisovCStage.c datum (FreeInput datum),
          Subgroup.subset_closure (by
            simp), rfl⟩, rfl⟩
    · apply Subgroup.subset_closure
      right
      rfl
    · apply Subgroup.subset_closure
      left
      exact ⟨toTStage datum (FreeInput datum)
          (of3 datum (FreeInput datum) secondStableInStageThree),
        ⟨of3 datum (FreeInput datum) secondStableInStageThree,
          Subgroup.subset_closure (by
            simp), rfl⟩, rfl⟩
  · rw [generatedWith, Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨a, ha, rfl⟩
      rcases ha with ⟨b, hb, rfl⟩
      exact B0_maps_into_HPlus datum hb
    · have hx' : x = k datum := by simpa using hx
      subst x
      exact k_mem_HPlus datum

/-- The second equality of Proposition 3.8 of the paper:
`K_c ∩ H_y^+ = ⟨c,k⟩`. -/
theorem Kc_inf_HPlus :
    Kc datum ⊓ HPlus datum = CKInGamma datum := by
  have hdouble :
      ((CT datum : Subgroup
          (TStage datum (FreeInput datum))) :
            Set (TStage datum (FreeInput datum))) ∩
          deltaDoubleCoset
            (KSubgroup datum (FreeInput datum)) (B0InT datum) =
        (C0InT datum : Set (TStage datum (FreeInput datum))) := by
    simpa [HostZBaseIntersections.Delta] using
      CT_inter_deltaDoubleCoset_B0 datum
  have hinter := centralizer_intersection
    (KSubgroup datum (FreeInput datum))
    (CT datum) (B0InT datum) (C0InT datum)
    (by
      intro x hx
      apply Subgroup.subset_closure
      exact Or.inl hx)
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, (CD_le_B0 datum) (C0_le_CD datum hx), rfl⟩)
    hdouble
  rw [HPlus_eq_generatedWith_B0_k datum]
  simpa [Kc, CTInGamma, CKInGamma, CInGamma,
    HostYStage.k, modelK, toFinalStage, kLetter] using hinter

/-! ## Compatibility with the first-stage attaching map -/

/-- The copy of `⟨t,c⟩` as a subgroup of `HMinus`. -/
def CTInHMinus : Subgroup (HMinus datum) :=
  (CTInGamma datum).comap (HMinus datum).subtype

/-- The copy of `⟨c,k⟩` as a subgroup of `HPlus`. -/
def CKInHPlus : Subgroup (HPlus datum) :=
  (CKInGamma datum).comap (HPlus datum).subtype

/-- The isomorphism following Lemma 3.1 carries `⟨t,c⟩` exactly onto
`⟨k,c⟩`. -/
theorem theta_mem_CT_iff_CK (theta : ThetaData datum) (a : HMinus datum) :
    (a : Gamma datum) ∈ CTInGamma datum ↔
      ((theta.equiv a : HPlus datum) : Gamma datum) ∈ CKInGamma datum := by
  constructor
  · intro ha
    let Sminus : Subgroup (HMinus datum) :=
      (CKInHPlus datum).comap theta.equiv.toMonoidHom
    have hcS : HostYStage.c datum ∈
        Sminus.map (HMinus datum).subtype := by
      refine ⟨minusC datum, ?_, rfl⟩
      change ((theta.equiv (minusC datum) : HPlus datum) : Gamma datum) ∈
        CKInGamma datum
      rw [theta.map_c]
      exact c_mem_CKInGamma datum
    have htS : HostYStage.t datum ∈
        Sminus.map (HMinus datum).subtype := by
      refine ⟨minusT datum, ?_, rfl⟩
      change ((theta.equiv (minusT datum) : HPlus datum) : Gamma datum) ∈
        CKInGamma datum
      rw [theta.map_t]
      exact k_mem_CKInGamma datum
    have hle := CTInGamma_le_of datum
      (Sminus.map (HMinus datum).subtype) hcS htS
    rcases hle ha with ⟨b, hb, hba⟩
    have hba' : b = a := Subtype.ext hba
    subst b
    exact hb
  · intro ha
    let Splus : Subgroup (HPlus datum) :=
      (CTInHMinus datum).comap theta.equiv.symm.toMonoidHom
    have hsymm_c : theta.equiv.symm (plusC datum) = minusC datum := by
      apply theta.equiv.injective
      rw [theta.equiv.apply_symm_apply, theta.map_c]
    have hsymm_k : theta.equiv.symm (plusK datum) = minusT datum := by
      apply theta.equiv.injective
      rw [theta.equiv.apply_symm_apply, theta.map_t]
    have hcS : HostYStage.c datum ∈
        Splus.map (HPlus datum).subtype := by
      refine ⟨plusC datum, ?_, rfl⟩
      change ((theta.equiv.symm (plusC datum) : HMinus datum) :
        Gamma datum) ∈ CTInGamma datum
      rw [hsymm_c]
      exact c_mem_CTInGamma datum
    have hkS : HostYStage.k datum ∈
        Splus.map (HPlus datum).subtype := by
      refine ⟨plusK datum, ?_, rfl⟩
      change ((theta.equiv.symm (plusK datum) : HMinus datum) :
        Gamma datum) ∈ CTInGamma datum
      rw [hsymm_k]
      exact t_mem_CTInGamma datum
    have hle := CKInGamma_le_of datum
      (Splus.map (HPlus datum).subtype) hcS hkS
    rcases hle ha with ⟨b, hb, hba⟩
    have hba' : b = theta.equiv a := Subtype.ext hba
    subst b
    change ((theta.equiv.symm (theta.equiv a) : HMinus datum) :
      Gamma datum) ∈ CTInGamma datum at hb
    simpa using hb

/-- Membership in `K_c` is preserved by the first-stage attaching
isomorphism.  This is the compatibility hypothesis needed to restrict the
`y`-HNN extension to `K_c`. -/
theorem theta_mem_Kc_iff (theta : ThetaData datum) (a : HMinus datum) :
    (a : Gamma datum) ∈ Kc datum ↔
      ((theta.equiv a : HPlus datum) : Gamma datum) ∈ Kc datum := by
  constructor
  · intro ha
    have haCT : (a : Gamma datum) ∈ CTInGamma datum := by
      have hpair : (a : Gamma datum) ∈ Kc datum ⊓ HMinus datum :=
        ⟨ha, a.property⟩
      rw [Kc_inf_HMinus datum] at hpair
      exact hpair
    exact CKInGamma_le_Kc datum
      ((theta_mem_CT_iff_CK datum theta a).mp haCT)
  · intro ha
    have haCK : ((theta.equiv a : HPlus datum) : Gamma datum) ∈
        CKInGamma datum := by
      have hpair : ((theta.equiv a : HPlus datum) : Gamma datum) ∈
          Kc datum ⊓ HPlus datum := ⟨ha, (theta.equiv a).property⟩
      rw [Kc_inf_HPlus datum] at hpair
      exact hpair
    exact CTInGamma_le_Kc datum
      ((theta_mem_CT_iff_CK datum theta a).mpr haCK)

end

end HostZIntersections
end Undecidability
