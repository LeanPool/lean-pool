/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Host.ZIntersections

/-!
# The exact path model for `K_c = ⟨t,c,k⟩`

The double-coset identity in the proof of Proposition 3.8 implies that
the subgroup `⟨c,t⟩` of the `t`-stage meets the subgroup centralized by `k`
in precisely `⟨c⟩`.  Consequently
the restriction of the final centralizer HNN extension to `⟨c,t⟩` is
the path HNN extension with base `⟨c,t⟩`, associated subgroup `⟨c⟩`,
and stable letter `k`.  This file identifies that model exactly with
`HostZIntersections.Kc`.
-/

@[expose] public section

namespace Undecidability
namespace HostKcModel

open BorisovCStage
open BorisovConverseCore
open BorisovFinalModel
open HNNLemmas
open HostYStage
open HostZBaseIntersections
open HostZIntersections

noncomputable section

variable (datum : Thue.StandingDatum)

/-- The proved rank-five freeness input used to construct the concrete host models. -/
abbrev FreeInput : RankFiveFree datum := HostYStage.FreeInput datum
/-- The HNN stage adjoining the centralizer generator `t`. -/
abbrev TBase := TStage datum (FreeInput datum)
/-- The final Borisov iterated-HNN model underlying the host. -/
abbrev Gamma := HostYStage.Gamma datum

private theorem C0InT_le_CT : C0InT datum ≤ CT datum := by
  rintro _ ⟨x, hx, rfl⟩
  apply Subgroup.subset_closure
  exact Or.inl ⟨x, hx, rfl⟩

private theorem C0_le_CE :
    C0 datum ≤ CE datum (FreeInput datum) := by
  rw [C0_le_iff]
  apply Subgroup.subset_closure
  simp

private theorem C0InT_le_Delta : C0InT datum ≤ Delta datum := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Delta, KSubgroup]
  apply Subgroup.subset_closure
  left
  exact ⟨x, C0_le_CE datum hx, rfl⟩

/-- A consequence of the double-coset identity in the proof of
Proposition 3.8: in the `t`-stage,
`⟨c,t⟩ ∩ Delta = ⟨c⟩`. -/
theorem CT_inf_Delta :
    CT datum ⊓ Delta datum = C0InT datum := by
  apply le_antisymm
  · intro x hx
    have hdouble : x ∈ deltaDoubleCoset (Delta datum) (B0InT datum) :=
      ⟨x, hx.2, 1, (B0InT datum).one_mem, 1, (Delta datum).one_mem,
        by simp⟩
    have hinter : x ∈
        ((CT datum : Subgroup (TBase datum)) : Set (TBase datum)) ∩
          deltaDoubleCoset (Delta datum) (B0InT datum) :=
      ⟨hx.1, hdouble⟩
    rw [CT_inter_deltaDoubleCoset_B0 datum] at hinter
    exact hinter
  · intro x hx
    exact ⟨C0InT_le_CT datum hx, C0InT_le_Delta datum hx⟩

/-- The copy of `⟨c⟩` regarded as a subgroup of the base `⟨c,t⟩`. -/
def C0InCT : Subgroup (CT datum) :=
  (C0InT datum).comap (CT datum).subtype

/-- The associated subgroup obtained by restricting `Delta` to `⟨c,t⟩`
is exactly the copy of `⟨c⟩` in that base. -/
theorem restrictedA_eq_C0InCT :
    restrictedA (A := KSubgroup datum (FreeInput datum)) (CT datum) =
      C0InCT datum := by
  ext x
  change (x : TBase datum) ∈ KSubgroup datum (FreeInput datum) ↔
    (x : TBase datum) ∈ C0InT datum
  have h := SetLike.ext_iff.mp (CT_inf_Delta datum) (x : TBase datum)
  simpa [Delta, and_comm] using h

/-- The base generator `t` as an element of `⟨c,t⟩`. -/
def baseT : CT datum :=
  ⟨tLetter datum (FreeInput datum), by
    apply Subgroup.subset_closure
    exact Or.inr rfl⟩

/-- The base generator `c` as an element of `⟨c,t⟩`. -/
def baseC : CT datum :=
  ⟨toTStage datum (FreeInput datum)
      (BorisovCStage.c datum (FreeInput datum)), by
    apply Subgroup.subset_closure
    left
    exact ⟨BorisovCStage.c datum (FreeInput datum),
      Subgroup.subset_closure (by rfl), rfl⟩⟩

/-! ## The exact `⟨c,t⟩` model

The preceding `t`-stage is itself a centralizer HNN extension, with stable
letter `t` centralizing `CD = ⟨c,d⟩`.  Restricting its base to `⟨c⟩`
therefore gives an exact presentation of `CT = ⟨c,t⟩`.  Since
`⟨c⟩ ≤ CD`, the associated subgroup in this restricted model is the
whole base `⟨c⟩`.
-/

theorem tCompatibility
    (a : CD datum (FreeInput datum)) :
    (a : Gamma2 datum (FreeInput datum)) ∈ C0 datum ↔
      ((MulEquiv.refl (CD datum (FreeInput datum)) a :
        CD datum (FreeInput datum)) : Gamma2 datum (FreeInput datum)) ∈
          C0 datum := Iff.rfl

/-- The literal restriction of the `t`-centralizer HNN extension to the
base `⟨c⟩`. -/
abbrev CTModel :=
  HNNExtension (C0 datum)
    (restrictedA (A := CD datum (FreeInput datum)) (C0 datum))
    (restrictedB (B := CD datum (FreeInput datum)) (C0 datum))
    (restrictedPhi (C0 datum) (tCompatibility datum))

/-- The canonical realization of `CTModel` in the semantic `t`-stage. -/
def ctModelEmbedding : CTModel datum →* TBase datum :=
  restrictedEmbedding (C0 datum) (tCompatibility datum)

theorem ctModelGenerated_eq_CT :
    generatedWithStable
        (A := CD datum (FreeInput datum))
        (B := CD datum (FreeInput datum))
        (phi := MulEquiv.refl (CD datum (FreeInput datum)))
        (C0 datum) =
      CT datum := rfl

/-- Exact parametrization of `CT = ⟨c,t⟩` by the restricted
`t`-centralizer model. -/
def ctModelEquivCT : CTModel datum ≃* CT datum :=
  (restrictedEquivGeneratedWithStable (C0 datum) (tCompatibility datum)).trans
    (MulEquiv.subgroupCongr (ctModelGenerated_eq_CT datum))

@[simp] theorem ctModelEquivCT_coe (x : CTModel datum) :
    ((ctModelEquivCT datum x : CT datum) : TBase datum) =
      ctModelEmbedding datum x := by
  change
    (((MulEquiv.subgroupCongr (ctModelGenerated_eq_CT datum))
      (restrictedEquivGeneratedWithStable (C0 datum)
        (tCompatibility datum) x) : CT datum) : TBase datum) = _
  rw [MulEquiv.subgroupCongr_apply]
  exact restrictedEquivGeneratedWithStable_coe
    (C0 datum) (tCompatibility datum) x

/-- The generator `c` in the base of `CTModel`. -/
def cInC0 : C0 datum :=
  ⟨BorisovCStage.c datum (FreeInput datum),
    Subgroup.subset_closure (by rfl)⟩

/-- The two displayed generators of the exact `CT` model. -/
def ctModelC : CTModel datum := HNNExtension.of (cInC0 datum)
/-- The stable generator `t` in the restricted `c,t` model. -/
def ctModelT : CTModel datum := HNNExtension.t

@[simp] theorem ctModelEquivCT_c :
    ctModelEquivCT datum (ctModelC datum) = baseC datum := by
  apply Subtype.ext
  simp [ctModelC, ctModelEquivCT_coe, ctModelEmbedding,
    cInC0, baseC, toTStage, centralizerOf]

@[simp] theorem ctModelEquivCT_t :
    ctModelEquivCT datum (ctModelT datum) = baseT datum := by
  apply Subtype.ext
  simp [ctModelT, ctModelEquivCT_coe, ctModelEmbedding,
    baseT, tLetter, centralizerStable]

theorem kCompatibility
    (a : KSubgroup datum (FreeInput datum)) :
    (a : TBase datum) ∈ CT datum ↔
      ((MulEquiv.refl (KSubgroup datum (FreeInput datum)) a :
        KSubgroup datum (FreeInput datum)) : TBase datum) ∈ CT datum := Iff.rfl

/-- The literal restricted HNN extension inside Borisov's final `k`-stage. -/
abbrev Restricted :=
  HNNExtension (CT datum)
    (restrictedA (A := KSubgroup datum (FreeInput datum)) (CT datum))
    (restrictedB (B := KSubgroup datum (FreeInput datum)) (CT datum))
    (restrictedPhi (CT datum) (kCompatibility datum))

/-- The canonical embedding of the literal restricted model in the final
`k`-stage. -/
def restrictedEmbeddingToGamma : Restricted datum →* Gamma datum :=
  restrictedEmbedding (CT datum) (kCompatibility datum)

theorem restrictedGenerated_eq_Kc :
    generatedWithStable
        (A := KSubgroup datum (FreeInput datum))
        (B := KSubgroup datum (FreeInput datum))
        (phi := MulEquiv.refl (KSubgroup datum (FreeInput datum)))
        (CT datum) =
      Kc datum := rfl

/-- Exact parametrization of `Kc = ⟨t,c,k⟩` by the literal restricted
final HNN extension. -/
def restrictedEquivKc : Restricted datum ≃* Kc datum :=
  (restrictedEquivGeneratedWithStable (CT datum) (kCompatibility datum)).trans
    (MulEquiv.subgroupCongr (restrictedGenerated_eq_Kc datum))

@[simp] theorem restrictedEquivKc_coe (x : Restricted datum) :
    ((restrictedEquivKc datum x : Kc datum) : Gamma datum) =
      restrictedEmbeddingToGamma datum x := by
  change
    (((MulEquiv.subgroupCongr (restrictedGenerated_eq_Kc datum))
      (restrictedEquivGeneratedWithStable (CT datum)
        (kCompatibility datum) x) : Kc datum) : Gamma datum) = _
  rw [MulEquiv.subgroupCongr_apply]
  exact restrictedEquivGeneratedWithStable_coe
    (CT datum) (kCompatibility datum) x

/-- The three path generators in the literal restricted model. -/
def restrictedT : Restricted datum := HNNExtension.of (baseT datum)
/-- The base generator `c` in the restricted `k,c` model. -/
def restrictedC : Restricted datum := HNNExtension.of (baseC datum)
/-- The stable generator `k` in the restricted `k,c` model. -/
def restrictedK : Restricted datum := HNNExtension.t

@[simp] theorem restrictedEquivKc_t :
    restrictedEquivKc datum (restrictedT datum) =
      ⟨HostYStage.t datum,
        CTInGamma_le_Kc datum (t_mem_CTInGamma datum)⟩ := by
  apply Subtype.ext
  simp [restrictedT, restrictedEquivKc_coe,
    restrictedEmbeddingToGamma, baseT, HostYStage.t,
    BorisovFinalModel.modelT, toFinalStage, centralizerOf]

@[simp] theorem restrictedEquivKc_c :
    restrictedEquivKc datum (restrictedC datum) =
      ⟨HostYStage.c datum,
        CTInGamma_le_Kc datum (c_mem_CTInGamma datum)⟩ := by
  apply Subtype.ext
  simp [restrictedC, restrictedEquivKc_coe,
    restrictedEmbeddingToGamma, baseC, HostYStage.c,
    BorisovFinalModel.modelC, BorisovFinalModel.cStageToFinal,
    toFinalStage, centralizerOf]

@[simp] theorem restrictedEquivKc_k :
    restrictedEquivKc datum (restrictedK datum) =
      ⟨HostYStage.k datum, by
        apply Subgroup.subset_closure
        exact Or.inr rfl⟩ := by
  apply Subtype.ext
  simp [restrictedK, restrictedEquivKc_coe,
    restrictedEmbeddingToGamma, HostYStage.k,
    BorisovFinalModel.modelK, kLetter, centralizerStable]

end

end HostKcModel
end Undecidability
