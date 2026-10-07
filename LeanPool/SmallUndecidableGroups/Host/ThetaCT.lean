/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.KcModel

/-!
# Restricting the first attaching map to `⟨t,c⟩`

The isomorphism following Lemma 3.1 sends the copy of `⟨t,c⟩` in `HMinus`
into `Kc = ⟨t,c,k⟩`.  This file packages that restriction as a homomorphism
whose source is the exact `CT` model used by the second compression stage.
-/

@[expose] public section

namespace Undecidability
namespace HostThetaCT

open BorisovFinalModel
open BorisovConverseCore
open HostYStage
open HostZIntersections

noncomputable section

variable (datum : Thue.StandingDatum) (theta : ThetaData datum)

/-- Regard the exact `⟨t,c⟩` subgroup of the `t`-stage as a subgroup of
`HMinus`, after applying the final-stage base embedding. -/
def ctToHMinus : HostZBaseIntersections.CT datum →* HMinus datum where
  toFun x :=
    ⟨toFinalStage datum (HostYStage.FreeInput datum)
        (x : HostKcModel.TBase datum), by
      apply CTInGamma_le_HMinus datum
      exact ⟨x, x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- The restriction of the attaching isomorphism following Lemma 3.1 to the
path base `⟨t,c⟩`, with codomain enlarged to `Kc = ⟨t,c,k⟩`. -/
def thetaCTtoKc :
    HostZBaseIntersections.CT datum →* Kc datum where
  toFun x :=
    ⟨((theta.equiv (ctToHMinus datum x) : HPlus datum) :
        HostYStage.Gamma datum), by
      apply (theta_mem_Kc_iff datum theta (ctToHMinus datum x)).mp
      apply CTInGamma_le_Kc datum
      exact ⟨x, x.property, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- Coercing the restricted map back to the ambient semantic Borisov group
is literally the original attaching map following Lemma 3.1 on the
corresponding element of `HMinus`. -/
@[simp] theorem thetaCTtoKc_coe
    (x : HostZBaseIntersections.CT datum) :
    ((thetaCTtoKc datum theta x : Kc datum) : HostYStage.Gamma datum) =
      ((theta.equiv (ctToHMinus datum x) : HPlus datum) :
        HostYStage.Gamma datum) :=
  rfl

@[simp] theorem ctToHMinus_baseT :
    ctToHMinus datum (HostKcModel.baseT datum) = minusT datum := by
  apply Subtype.ext
  rfl

@[simp] theorem ctToHMinus_baseC :
    ctToHMinus datum (HostKcModel.baseC datum) = minusC datum := by
  apply Subtype.ext
  rfl

/-- The path generator `t` is sent to `k`. -/
@[simp] theorem thetaCTtoKc_baseT :
    thetaCTtoKc datum theta (HostKcModel.baseT datum) =
      ⟨HostYStage.k datum, by
        apply Subgroup.subset_closure
        exact Or.inr rfl⟩ := by
  apply Subtype.ext
  rw [thetaCTtoKc_coe, ctToHMinus_baseT, theta.map_t]
  rfl

/-- The path generator `c` is fixed. -/
@[simp] theorem thetaCTtoKc_baseC :
    thetaCTtoKc datum theta (HostKcModel.baseC datum) =
      ⟨HostYStage.c datum,
        CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ := by
  apply Subtype.ext
  rw [thetaCTtoKc_coe, ctToHMinus_baseC, theta.map_c]
  rfl

end

end HostThetaCT
end Undecidability
