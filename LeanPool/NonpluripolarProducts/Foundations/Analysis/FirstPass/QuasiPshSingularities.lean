/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Plurisubharmonic
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Local quasi-PSH potentials and additive singularity comparison

[Xia's quasi-PSH definitions and singularity order](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_pshfunctions.tex#L1247-L1264)
use a smooth closed background on the manifold and a global additive order
on a compact manifold. Here the decomposition and comparison are local.
The local decomposition uses the existing extended-real PSH germs and a real
smooth summand. The raw criterion permits the identically negative-infinite
function, like `PlurisubharmonicAt`; `LocalQuasiPshPotentialOn` separately
excludes it on every open neighborhood. No current or global geometry is assumed.

`MoreSingularOn u v U` means `u ≤ v + C`, in Xia's direction.
Constants are always real, so these comparisons also make sense at poles.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis

section LocalPotentials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

/-- Locally the sum of an actual PSH germ and a smooth real function.
This raw local criterion allows the identically negative-infinite germ. -/
def QuasiPlurisubharmonicAt (u : E → EReal) (x : E) : Prop :=
  ∃ (p : E → EReal) (h : E → ℝ), PlurisubharmonicAt p x ∧
    (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ h y) ∧
    u =ᶠ[𝓝 x] (fun y => p y + (h y : EReal))

/-- Ambient quasi-PSH germs at all points of a set. -/
def QuasiPlurisubharmonicOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ x ∈ U, QuasiPlurisubharmonicAt u x

/-- A nondegenerate local quasi-PSH potential on an open domain: every
neighborhood of each domain point meets its finite locus. Thus no open
component is allowed to be identically negative infinity. -/
def LocalQuasiPshPotentialOn (u : E → EReal) (U : Set E) : Prop :=
  IsOpen U ∧ QuasiPlurisubharmonicOn u U ∧
    ∀ x ∈ U, ∀ V : Set E, IsOpen V → x ∈ V →
      ∃ y ∈ U ∩ V, u y ≠ ⊥

theorem PlurisubharmonicAt.quasiPlurisubharmonicAt {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) : QuasiPlurisubharmonicAt u x := by
  exact ⟨u, fun _ => 0, hu, Filter.Eventually.of_forall (fun _ => contDiffAt_const), by simp⟩

theorem QuasiPlurisubharmonicAt.congr {u v : E → EReal} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) (huv : u =ᶠ[𝓝 x] v) :
    QuasiPlurisubharmonicAt v x := by
  obtain ⟨p, h, hp, hh, heq⟩ := hu
  exact ⟨p, h, hp, hh, huv.symm.trans heq⟩

theorem QuasiPlurisubharmonicAt.ne_top {u : E → EReal} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) : u x ≠ ⊤ := by
  obtain ⟨p, h, hp, _, heq⟩ := hu
  rw [heq.eq_of_nhds]
  exact EReal.add_ne_top hp.ne_top (EReal.coe_ne_top _)

theorem QuasiPlurisubharmonicAt.add_smooth {u : E → EReal} {h : E → ℝ} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) (hh : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ h y) :
    QuasiPlurisubharmonicAt (fun y => u y + (h y : EReal)) x := by
  obtain ⟨p, g, hp, hg, heq⟩ := hu
  refine ⟨p, fun y => g y + h y, hp, ?_, ?_⟩
  · filter_upwards [hg, hh] with y hgy hhy
    exact hgy.add hhy
  filter_upwards [heq] with y hy
  rw [hy, EReal.coe_add, add_assoc]

theorem QuasiPlurisubharmonicOn.mono {u : E → EReal} {U V : Set E}
    (hu : QuasiPlurisubharmonicOn u U) (hVU : V ⊆ U) :
    QuasiPlurisubharmonicOn u V := fun x hx => hu x (hVU hx)

theorem QuasiPlurisubharmonicOn.add_smooth {u : E → EReal} {h : E → ℝ} {U : Set E}
    (hu : QuasiPlurisubharmonicOn u U)
    (hh : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ h y) :
    QuasiPlurisubharmonicOn (fun y => u y + (h y : EReal)) U :=
  fun x hx => (hu x hx).add_smooth (hh x hx)

theorem LocalQuasiPshPotentialOn.mono {u : E → EReal} {U V : Set E}
    (hu : LocalQuasiPshPotentialOn u U) (hV : IsOpen V) (hVU : V ⊆ U) :
    LocalQuasiPshPotentialOn u V := by
  refine ⟨hV, hu.2.1.mono hVU, ?_⟩
  intro x hx W hW hxW
  obtain ⟨y, hy, hfin⟩ := hu.2.2 x (hVU hx) (V ∩ W) (hV.inter hW) ⟨hx, hxW⟩
  exact ⟨y, hy.2, hfin⟩

theorem localQuasiPshPotentialOn_const (c : ℝ) {U : Set E} (hU : IsOpen U) :
    LocalQuasiPshPotentialOn (fun _ : E => (c : EReal)) U := by
  refine ⟨hU, fun x _ => (plurisubharmonicAt_const c (EReal.coe_ne_top c)
    x).quasiPlurisubharmonicAt, ?_⟩
  exact fun x hx V _ hxV => ⟨x, ⟨hx, hxV⟩, EReal.coe_ne_bot c⟩

end LocalPotentials

section SingularityOrder

variable {X : Type*}

/-- `u` is more singular than `v` on `U`, with one finite additive constant. -/
def MoreSingularOn (u v : X → EReal) (U : Set X) : Prop :=
  ∃ C : ℝ, ∀ x ∈ U, u x ≤ v x + (C : EReal)

/-- Equality of singularity type means two additive comparisons, not equality
of values and not subtraction of potentially infinite values. -/
def SameSingularityTypeOn (u v : X → EReal) (U : Set X) : Prop :=
  MoreSingularOn u v U ∧ MoreSingularOn v u U

theorem MoreSingularOn.of_le {u v : X → EReal} {U : Set X}
    (h : ∀ x ∈ U, u x ≤ v x) : MoreSingularOn u v U :=
  ⟨0, by simpa using h⟩

theorem MoreSingularOn.refl (u : X → EReal) (U : Set X) : MoreSingularOn u u U :=
  .of_le (fun _ _ => le_rfl)

theorem MoreSingularOn.trans {u v w : X → EReal} {U : Set X}
    (huv : MoreSingularOn u v U) (hvw : MoreSingularOn v w U) :
    MoreSingularOn u w U := by
  obtain ⟨C, hC⟩ := huv
  obtain ⟨D, hD⟩ := hvw
  refine ⟨D + C, fun x hx => ?_⟩
  calc
    u x ≤ v x + (C : EReal) := hC x hx
    _ ≤ (w x + (D : EReal)) + (C : EReal) := add_le_add (hD x hx) le_rfl
    _ = w x + ((D + C : ℝ) : EReal) := by rw [EReal.coe_add, add_assoc]

theorem MoreSingularOn.mono {u v : X → EReal} {U V : Set X}
    (h : MoreSingularOn u v U) (hVU : V ⊆ U) : MoreSingularOn u v V := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun x hx => hC x (hVU hx)⟩

/-- A pole of the less singular potential is necessarily a pole of the more
singular one. No subtraction or `toReal` operation is used. -/
theorem MoreSingularOn.eq_bot_of_eq_bot {u v : X → EReal} {U : Set X}
    (h : MoreSingularOn u v U) {x : X} (hx : x ∈ U) (hv : v x = ⊥) : u x = ⊥ := by
  obtain ⟨C, hC⟩ := h
  have h := hC x hx
  simpa [hv] using h

theorem SameSingularityTypeOn.refl (u : X → EReal) (U : Set X) :
    SameSingularityTypeOn u u U := ⟨.refl u U, .refl u U⟩

theorem SameSingularityTypeOn.symm {u v : X → EReal} {U : Set X}
    (h : SameSingularityTypeOn u v U) : SameSingularityTypeOn v u U := ⟨h.2, h.1⟩

theorem SameSingularityTypeOn.trans {u v w : X → EReal} {U : Set X}
    (huv : SameSingularityTypeOn u v U) (hvw : SameSingularityTypeOn v w U) :
    SameSingularityTypeOn u w U := ⟨huv.1.trans hvw.1, hvw.2.trans huv.2⟩

theorem sameSingularityTypeOn_add_const (u : X → EReal) (U : Set X) (c : ℝ) :
    SameSingularityTypeOn (fun x => u x + (c : EReal)) u U := by
  refine ⟨⟨c, fun _ _ => le_rfl⟩, ⟨-c, fun x _ => ?_⟩⟩
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

variable [TopologicalSpace X]

/-- Additive singularity comparison on some neighborhood, with one real constant. -/
def MoreSingularAt (u v : X → EReal) (x : X) : Prop :=
  ∃ C : ℝ, ∀ᶠ y in 𝓝 x, u y ≤ v y + (C : EReal)

theorem MoreSingularAt.refl (u : X → EReal) (x : X) : MoreSingularAt u u x :=
  ⟨0, Filter.Eventually.of_forall (fun _ => by simp)⟩

theorem MoreSingularAt.trans {u v w : X → EReal} {x : X}
    (huv : MoreSingularAt u v x) (hvw : MoreSingularAt v w x) :
    MoreSingularAt u w x := by
  obtain ⟨C, hC⟩ := huv
  obtain ⟨D, hD⟩ := hvw
  refine ⟨D + C, ?_⟩
  filter_upwards [hC, hD] with y hyC hyD
  simpa [EReal.coe_add, add_assoc] using hyC.trans (add_le_add hyD (le_rfl : (C : EReal) ≤ C))

theorem MoreSingularOn.moreSingularAt {u v : X → EReal} {U : Set X}
    (h : MoreSingularOn u v U) {x : X} (hU : U ∈ 𝓝 x) : MoreSingularAt u v x := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, Filter.eventually_of_mem hU (fun y hy => hC y hy)⟩

omit [TopologicalSpace X] in
/-- The global branch lies below its actual collar maximum. -/
theorem moreSingularOn_gluedMax (U V : Set X) (u v : X → EReal) :
    MoreSingularOn v (gluedMax U u v) V := by
  apply MoreSingularOn.of_le
  intro x _
  classical
  by_cases hx : x ∈ U
  · rw [gluedMax_eq_max hx]
    exact le_max_right _ _
  · simp [gluedMax, hx]

end SingularityOrder

end SGPT.Foundations.Analysis
