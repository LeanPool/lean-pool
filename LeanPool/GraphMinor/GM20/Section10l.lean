/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM20.Section10k
public import LeanPool.GraphMinor.GM20.Draw10

import LeanPool.GraphMinor.GM20.Section10iProved

import LeanPool.GraphMinor.GM17.Bridge

import LeanPool.GraphMinor.Surface.Classification

/-!
# Graph Minors XX, (10.3)

This file proves (10.3), from (14.2) of Graph Minors XVII and the results of Section 8, 9 and 11 of
that
paper. The proof takes the portrayal given by (14.2) and uses Section10f-Section10i.

The paper says that the set `𝒮` of graded surfaces with at most `q` cuffs, in which `H` cannot be
drawn,
and with `ρ ≤ p`, "is finite up to homeomorphism". We state this for surfaces as
`FiniteSurfaceTypesStatement`, and we prove it from the classification of surfaces: by `Draw8` a
surface
of large genus has a drawing of `H`, and by `Draw10` a surface with few cuffs is a model with small
`c`.
The gradings are counted here.
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10
open GraphMinor.GM20.GM17

universe u v

/-- For a graph `H` and an integer `q`, the connected surfaces with at most `q` cuffs in which `H`
cannot be drawn are finite in number up to homeomorphism. (Graph Minors XX, Section 10, page 354:
"Thus `𝒮` is finite up to homeomorphism.") It follows from the classification of surfaces, since a
surface of large genus has a drawing of `H`. -/
def FiniteSurfaceTypesStatement : Prop :=
  ∀ {α' β' : Type} (H : Hypergraph α' β'), H.IsGraph → ∀ q : ℕ,
    ∃ 𝒮₀ : Set GradedSurface, 𝒮₀.Finite ∧ ∀ (S : Type) [TopologicalSpace S], IsSurface S →
      ConnectedSpace S → (cuffs S).encard ≤ q → ¬ CanBeDrawn S H →
      ∃ X ∈ 𝒮₀, Nonempty (S ≃ₜ X.S)

/-- The surface of `X` with the grading `ρ`. -/
def GradedSurface.withGrading (X : GradedSurface) (ρ : Set X.S → ℕ) : GradedSurface where
  S := X.S
  isSurface := X.isSurface
  connected := X.connected
  ρ := ρ

/-- The gradings of the surface of `X` with values at most `p` on the cuffs, and `0` off the cuffs.
-/
def GradedSurface.gradings (X : GradedSurface) (p : ℕ) : Set GradedSurface :=
  X.withGrading '' {ρ | ∀ Θ, ρ Θ ≤ p ∧ (Θ ∉ cuffs X.S → ρ Θ = 0)}

theorem GradedSurface.finite_gradings (X : GradedSurface) (p : ℕ) : (X.gradings p).Finite := by
  obtain ⟨-, hfin, -⟩ := cuff_statement.{0} X.S X.isSurface
  have : Finite (cuffs X.S) := hfin
  refine Set.Finite.image _ ?_
  let f : (Set X.S → ℕ) → (cuffs X.S → Fin (p + 1)) := fun ρ Θ ↦ Fin.ofNat (p + 1) (ρ Θ.1)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro ρ hρ ρ' hρ' h
  funext Θ
  by_cases hΘ : Θ ∈ cuffs X.S
  · have h₁ := congrArg Fin.val (congrFun h ⟨Θ, hΘ⟩)
    simp only [f, Fin.val_ofNat] at h₁
    rwa [Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hρ Θ).1),
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hρ' Θ).1)] at h₁
  · rw [(hρ Θ).2 hΘ, (hρ' Θ).2 hΘ]

/-- `FiniteSurfaceTypesStatement` holds. By the classification of surfaces, a connected surface `S`
is
homeomorphic to some model `Σ(a, b, c)`. If `a` or `b` is large then `H` can be drawn in the model,
and
so in `S`. A model has at least `c` cuffs, so `c` is at most the number of cuffs of `S`. So there
are
finitely many possible triples `(a, b, c)`, and for each we keep one surface homeomorphic to the
model, if there is one. -/
theorem finiteSurfaceTypes : FiniteSurfaceTypesStatement := by
  classical
  intro α' β' H hH q
  obtain ⟨L, hL⟩ := Draw.exists_canBeDrawn H hH
  let T : Set (ℕ × ℕ × ℕ) := Iio L ×ˢ Iio L ×ˢ Iic q
  have hT : T.Finite := (finite_Iio L).prod ((finite_Iio L).prod (finite_Iic q))
  let rep : ℕ × ℕ × ℕ → Set GradedSurface := fun t ↦
    if h : ∃ X : GradedSurface, Nonempty (X.S ≃ₜ SurfaceModel t.1 t.2.1 t.2.2) then {h.choose}
    else ∅
  have hrep : ∀ t, (rep t).Finite := fun t ↦ by
    simp only [rep]
    split_ifs
    · exact finite_singleton _
    · exact finite_empty
  refine ⟨⋃ t ∈ T, rep t, hT.biUnion fun t _ ↦ hrep t, ?_⟩
  intro S _ hS hc hcuffs hdraw
  obtain ⟨a, b, c, ⟨ψ⟩⟩ := GraphMinor.Surface.classification.{0} S hS hc
  have : T2Space S := hS.2.1
  have : T2Space (SurfaceModel a b c) := ψ.t2Space
  have hab : a < L ∧ b < L := by
    by_contra hn
    refine hdraw (Draw.CanBeDrawn.map ψ.symm (hL a b c ?_))
    omega
  have hcq : c ≤ q := by
    have h₁ : (c : ℕ∞) ≤ (cuffs (SurfaceModel a b c)).encard := Draw.le_encard_cuffs
    rw [image_cuffs ψ] at h₁
    have h₂ := h₁.trans ((Set.encard_image_le _ _).trans hcuffs)
    exact_mod_cast h₂
  have h : ∃ X : GradedSurface, Nonempty (X.S ≃ₜ SurfaceModel a b c) :=
    ⟨{ S := S, isSurface := hS, connected := hc, ρ := fun _ ↦ 0 }, ⟨ψ⟩⟩
  refine ⟨h.choose, mem_biUnion (x := (a, b, c)) ⟨hab.1, hab.2, hcq⟩ ?_,
    ⟨ψ.trans h.choose_spec.some.symm⟩⟩
  simp only [rep]
  rw [dite_eq_left h]
  exact mem_singleton _

variable {α : Type u} {β : Type v}

/-- Graph Minors XX, (10.3) (page 354): "For every graph* $H$ *there exist* $\theta \ge 1$ *and a
set* $\mathcal{S}$ *of graded
surfaces, finite up to homeomorphism, with the following property. Let* $P = (G, \mu,
\Delta)$ *be a rootless free patchwork, and let* $\mathcal{T}$ *be a tangle in* $G$ *of
order* $\ge \theta$ *controlling no* $H$*-minor of* $sk(G)$. *Then there exist* $W \subseteq
V(G)$ *with* $|W| < \theta$ *and a fine rooted location* $\mathcal{L}$ *in* $G/W$, *such
that* * $(P/W, \mathcal{L})$ *is* $(\Sigma, \rho)$*-shelled for some* $(\Sigma, \rho) \in
\mathcal{S}$, *and* * $\mathcal{L}$ *is linked to* $\mathcal{T}/W$." Here `𝒮` is a finite set of
representatives, and the order `θ` is at least `z + 6p + 9`, so that the standing hypotheses of
Sections
8, 9, 11 of Graph Minors XVII hold.

Lean uses an infinite ambient edge type to provide fresh edge labels. -/
theorem theorem_10_3_proof
     : Theorem103Statement.{u, v} := by
  classical
  intro α' β' H hH
  obtain ⟨p, q, z, θ₀, hz, h⟩ := GraphMinor.GM17.gm17Theorem142.{u, v} H hH
  obtain ⟨𝒮₀, h𝒮₀, hrep⟩ := finiteSurfaceTypes H hH q
  refine ⟨max θ₀ (z + 6 * p + 9), ⋃ X ∈ 𝒮₀, X.gradings p, by omega,
    h𝒮₀.biUnion fun X _ ↦ X.finite_gradings p, ?_⟩
  intro α β _ P _ hroot θ' 𝒯 h𝒯 hθ' hnc
  have hθ₀ : θ₀ ≤ θ' := (le_max_left _ _).trans hθ'
  have hθ₁ : z + 6 * p + 9 ≤ θ' := (le_max_right _ _).trans hθ'
  obtain hctrl | ⟨Z, hZ, hZc, π, hw, hc, hnd, ht, hred⟩ := h P.G.toHypergraph θ' 𝒯 h𝒯 hθ₀
  · exact (hnc hctrl).elim
  have hZlt : Z.ncard < θ' := by omega
  have h𝒯' : IsTangle (quotientVertices P.G.toHypergraph Z) (θ' - Z.ncard)
      (quotientTangle P.G.toHypergraph 𝒯 Z) := GM10.theorem_6_2_proof h𝒯 hZ hZlt
  let π' : Portrayal (P.slash Z).G.toHypergraph := π
  have hs : Standing (quotientTangle P.G.toHypergraph 𝒯 Z) (θ' - Z.ncard) p (2 * p + 4)
      (6 * p + 8) π' :=
    { isTangle := h𝒯'
      isTrue := ht
      isRedundant := ⟨by have := hred.1; omega, fun Y hY hYc ↦ hred.2 Y hY (hYc.trans (by omega))⟩
      warp_le := hw
      lt := by omega }
  have hr : (P.slash Z).G.rootSet = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro v hv
    have := (mem_slash_rootSet.mp hv).1
    change v ∈ P.G.roots at this
    rw [hroot] at this
    simp at this
  have hs₈ := hs.mono (r' := 2 * p + 3) (t' := 4 * p + 5) (by omega) (by omega)
  have hshell := Portrayal.isShelled_of_standing hr hs₈
  have hlink := Portrayal.isLinkedTo_of_standing hr hs
  obtain ⟨X₀, hX₀, ⟨ψ⟩⟩ := hrep π.S π.isSurface π.connected
    (hc.trans (by norm_cast)) hnd
  let ρ : Set X₀.S → ℕ := fun Θ ↦ if Θ ∈ cuffs X₀.S then π.warpAt (ψ.symm '' Θ) else 0
  have hρ : ∀ Θ ∈ cuffs π.S, ρ (ψ '' Θ) = π.warpAt Θ := by
    intro Θ hΘ
    have hmem : ψ '' Θ ∈ cuffs X₀.S := by
      rw [image_cuffs ψ]
      exact ⟨Θ, hΘ, rfl⟩
    simp only [ρ, ite_eq_left hmem]
    rw [symm_image_image]
  have hY : X₀.withGrading ρ ∈ ⋃ X ∈ 𝒮₀, X.gradings p := by
    refine mem_biUnion hX₀ ⟨ρ, fun Θ ↦ ⟨?_, fun hΘ ↦ ite_eq_right hΘ⟩, rfl⟩
    by_cases hΘ : Θ ∈ cuffs X₀.S
    · simp only [ρ, ite_eq_left hΘ]
      have hmem : ψ.symm '' Θ ∈ cuffs π.S := by
        rw [image_cuffs ψ.symm]
        exact ⟨Θ, hΘ, rfl⟩
      exact (Portrayal.warpAt_le_warp_of_mem π hmem).trans hw
    · simp only [ρ, ite_eq_right hΘ]
      exact Nat.zero_le _
  exact ⟨Z, hZ, by omega, π'.cellLocation, Portrayal.isFine_cellLocation, ⟨_, hY,
    IsShelled.map (X := π'.gradedOf) (Y := X₀.withGrading ρ) (ψ := ψ) hρ hshell⟩, hlink⟩

end GraphMinor.GM20
