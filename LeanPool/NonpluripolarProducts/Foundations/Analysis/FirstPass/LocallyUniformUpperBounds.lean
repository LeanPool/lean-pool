/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic

/-!
# Locally uniform upper bounds

The local condition in this file is relative to the domain: at a point of
`Ω`, one asks for a member of `𝓝[Ω] x` and one real constant which bounds every
member of the family on the intersection of that neighbourhood with `Ω`.

The main result is the finite-subcover passage from this local condition to a
single real upper bound on an arbitrary compact subset of `Ω`.  No regularity
of the individual functions is needed.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

variable {X : Type*} [TopologicalSpace X]

/-- A family of extended-real functions is locally uniformly bounded above on
`Ω` if, near every point relative to `Ω`, one real constant bounds all members
of the family simultaneously. -/
def LocallyUniformlyBoundedAbove (F : Set (X → EReal)) (Ω : Set X) : Prop :=
  ∀ x ∈ Ω, ∃ U : Set X, U ∈ 𝓝[Ω] x ∧
    ∃ C : ℝ, ∀ f ∈ F, ∀ y ∈ U ∩ Ω, f y ≤ (C : EReal)

theorem LocallyUniformlyBoundedAbove.mono_family {F G : Set (X → EReal)}
    {Ω : Set X} (hF : LocallyUniformlyBoundedAbove F Ω) (hGF : G ⊆ F) :
    LocallyUniformlyBoundedAbove G Ω := by
  intro x hx
  obtain ⟨U, hU, C, hC⟩ := hF x hx
  exact ⟨U, hU, C, fun f hf => hC f (hGF hf)⟩

theorem LocallyUniformlyBoundedAbove.mono_domain {F : Set (X → EReal)}
    {Ω V : Set X} (hF : LocallyUniformlyBoundedAbove F Ω) (hVΩ : V ⊆ Ω) :
    LocallyUniformlyBoundedAbove F V := by
  intro x hx
  obtain ⟨U, hU, C, hC⟩ := hF x (hVΩ hx)
  refine ⟨U, ?_, C, ?_⟩
  · exact (nhdsWithin_mono x hVΩ) hU
  · intro f hf y hy
    exact hC f hf y ⟨hy.1, hVΩ hy.2⟩

/-- A locally uniform real upper bound becomes one uniform real upper bound on
every compact subset of the domain.  The proof chooses relative
neighbourhoods, extracts a finite subcover, and takes the maximum of their
constants. -/
theorem LocallyUniformlyBoundedAbove.exists_uniform_upper_bound_on_compact
    {F : Set (X → EReal)} {Ω K : Set X}
    (hF : LocallyUniformlyBoundedAbove F Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, ∀ f ∈ F, ∀ x ∈ K, f x ≤ (C : EReal) := by
  by_cases hKempty : K = ∅
  · exact ⟨0, by simp [hKempty]⟩
  choose U hU C hC using fun x : K => hF x (hKΩ x.property)
  have hUK : ∀ x (hx : x ∈ K), U ⟨x, hx⟩ ∈ 𝓝[K] x := by
    intro x hx
    exact (nhdsWithin_mono x hKΩ) (hU ⟨x, hx⟩)
  obtain ⟨t, hcover⟩ := hK.elim_nhdsWithin_subcover'
    (fun x hx => U ⟨x, hx⟩) hUK
  have ht : t.Nonempty := by
    obtain ⟨x, hx⟩ : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hKempty
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact ⟨i, hi⟩
  refine ⟨t.sup' ht C, ?_⟩
  intro f hf x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hlocal : f x ≤ (C i : EReal) :=
    hC i f hf x ⟨hxi, hKΩ hx⟩
  exact hlocal.trans <| EReal.coe_le_coe_iff.mpr (Finset.le_sup' C hi)

/-- Compact-image interface: a compact parameter space mapped continuously
into `Ω` inherits a common real upper bound for the whole family. -/
theorem LocallyUniformlyBoundedAbove.exists_uniform_upper_bound_on_compact_image
    {F : Set (X → EReal)} {Ω : Set X} {Y : Type*} [TopologicalSpace Y]
    (hF : LocallyUniformlyBoundedAbove F Ω) {L : Set Y} (hL : IsCompact L)
    {φ : Y → X} (hφ : ContinuousOn φ L) (hφΩ : MapsTo φ L Ω) :
    ∃ C : ℝ, ∀ f ∈ F, ∀ y ∈ L, f (φ y) ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := hF.exists_uniform_upper_bound_on_compact
    (hL.image_of_continuousOn hφ)
    (fun _ hz => by obtain ⟨y, hy, rfl⟩ := hz; exact hφΩ hy)
  exact ⟨C, fun f hf y hy => hC f hf (φ y) ⟨y, hy, rfl⟩⟩

end SGPT.Foundations.Analysis.FirstPass
