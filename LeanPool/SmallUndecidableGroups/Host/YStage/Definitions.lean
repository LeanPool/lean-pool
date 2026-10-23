/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.FinalModel
public import LeanPool.SmallUndecidableGroups.Borisov.Assertions.InputsBridge

/-!
# Definitions for the first compression HNN extension

The semantic generators and restricted-model interfaces are separated from
construction of the twisting and associated-subgroup equivalences.
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

/-- The four generator images defining the twisting automorphism of the initial Borisov group. -/
def twistGenerator : Fin 4 → Gamma3 :=
  ![e3⁻¹, d3, secondStableInStageThree⁻¹, firstStableInStageThree⁻¹]

/-- The four generator images defining the inverse twisting automorphism. -/
def untwistGenerator : Fin 4 → Gamma3 :=
  ![e3, d3⁻¹, secondStableInStageThree⁻¹, firstStableInStageThree⁻¹]


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


/-- The exact subgroup `⟨d,e,c,s_beta⟩` of `Gamma2`. -/
def CSubgroup (beta : Fin 2) : Subgroup (Gamma2 datum (rankFiveFree datum)) :=
  generatedWithStable (A := U datum) (B := V datum)
    (phi := cEquiv datum (rankFiveFree datum)) (J3 beta)

/-- The equivalence from the restricted HNN model onto its generated subgroup. -/
def cRestrictedRangeEquiv (beta : Fin 2) :
    CRestricted datum beta ≃* CSubgroup datum beta :=
  restrictedEquivGeneratedWithStable (J3 beta)
    (cEquiv_mem_J3_iff datum (rankFiveFree datum) beta)


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

end

end HostYStage
end Undecidability
