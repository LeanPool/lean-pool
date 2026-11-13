/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.ThetaCT

/-!
# Definitions for the second compression HNN extension

The two restricted HNN models and their canonical generators are separated from
path-rotation proofs to bound the size of each compilation unit.
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



/-- The generator `d₃`, regarded as an element of its cyclic subgroup. -/
def dInCyclic : dCyclic :=
  ⟨d3, Subgroup.subset_closure (by rfl)⟩






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


end

end HostZStage
end Undecidability
