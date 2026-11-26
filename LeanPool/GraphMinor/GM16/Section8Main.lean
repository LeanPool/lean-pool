/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section8
public import LeanPool.GraphMinor.GM15.Section4
import LeanPool.GraphMinor.GM16.Section9Proof
import LeanPool.GraphMinor.GM16.Section8Proof
import LeanPool.GraphMinor.GM16.Section8Truncation
import LeanPool.GraphMinor.GM16.EnvelopeAnimal
import LeanPool.GraphMinor.GM16.SeparatedHairsCut
import LeanPool.GraphMinor.GM16.SpanSurface
import LeanPool.GraphMinor.GM16.Section5
import LeanPool.GraphMinor.GM09.Basic

import LeanPool.GraphMinor.GM09.Bridge

import LeanPool.GraphMinor.GM11.CitedResults

import LeanPool.GraphMinor.GM12.Section710

import LeanPool.GraphMinor.GM12.Section77

import LeanPool.GraphMinor.GM14.Section9a

import LeanPool.GraphMinor.GM14.Section9b

import LeanPool.GraphMinor.GM16.Theorem35Bridge

/-!
# Graph Minors XVI, (7.1)

Follow the proof on pages 69–70. Truncate and delete the horn centres,
then apply (8.1). The handle and extra-hair outcomes lift to the
original graph. In the envelope outcome, clear the horns and extend
the hairs to the boundary, producing the animal for (8.3). Its
close-pair outcome contradicts the separator. Its remaining outcomes
give either one more hair or the required level span.
-/

public section
namespace GraphMinor.GM16
open Set Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14 GraphMinor.GM15
universe u v w

/-- Graph Minors XVI, (7.1), pages 62 and 69–70, by the complete
proof using (8.1), (8.2), and (8.3), with all horns and hairs after
clearing constructed. No statement of XVI is assumed. -/
theorem theorem_7_1_proof
     : GM16Theorem71Statement.{u, v, w} := by
  classical
  intro S _ _ hS hConn τ χ δ lam θreq φ ψ hθreq hφ hψ
  let : ConnectedSpace S := hConn
  obtain ⟨γ, θ₁, hγ, hClear, h81⟩ := theorem_8_1_with_radius hS hConn δ φ ψ hφ hψ
  let ζ := χ + δ ^ 2 * φ ^ 2 / 2
  obtain ⟨θ₂, hLower, hζθ₂, h83⟩ := theorem_8_3_with_bound hS hConn
    (max (θreq + ζ) (4 * ψ + 2)) τ χ δ lam ζ ψ hψ
  have hReq : θreq + ζ ≤ θ₂ := (le_max_left _ _).trans hLower
  have hFour : 4 * ψ + 2 ≤ θ₂ := (le_max_right _ _).trans hLower
  have hθ₂ : 1 ≤ θ₂ := by omega
  let σ := δ + τ + ζ
  let θ := χ + θ₁ + 3 * γ + (4 * γ + 2) * δ + θ₂
  refine ⟨θ, σ, by dsimp [θ]; omega, ?_⟩
  intro α β G θ_star T_star hT hHas
  obtain ⟨H, η, θ_span, T, d, X, Y, hAnim⟩ := hHas
  have hSaved := hAnim
  obtain ⟨_, hθOrd, hSpan, hMet, hX, hXCard, hY, hYCard, _, _, _⟩ := hSaved
  let θ₀ := θ - χ
  have hθ₀ : θ₀ = θ₁ + 3 * γ + (4 * γ + 2) * δ + θ₂ := by dsimp [θ₀, θ]; omega
  have hθ₀pos : 1 ≤ θ₀ := by rw [hθ₀]; omega
  have hθ₀θ : θ₀ ≤ θ := Nat.sub_le _ _
  have hθ₁₀ : θ₁ ≤ θ₀ := by rw [hθ₀]; omega
  have hBudget : θ₂ + 3 * γ + (4 * γ + 2) * δ ≤ θ₀ := by rw [hθ₀]; omega
  let T₀ := truncation T θ₀
  let d₀ : Set S → Set S → ℕ := fun a b => min (d a b) θ₀
  have hNorm : IsAnimal G T_star θ_star H η θ₀ T₀ d₀ X Y χ δ θ₀ σ :=
    theorem_8_3_claim_1 (hAnim.mono hθ₀pos hθ₀θ le_rfl)
  have hNormSaved := hNorm
  obtain ⟨_, _, hSpan₀, hMet₀, _, _, _, _, _, _, hSep₀⟩ := hNormSaved
  have hXsub : X ⊆ V(G) := fun x hx => (hX hx).1
  have hXdis : Disjoint V(η.imageGraph) X := disjoint_left.mpr fun x hx hxX => (hX hxX).2 hx
  have hXlt : X.ncard < θ_span := by
    rw [hXCard]
    have hχθ : χ < θ := by dsimp [θ]; omega
    exact lt_of_lt_of_le hχθ hθOrd
  have hXltStar : X.ncard < θ_star := hXlt.trans_le hSpan.isControlling.theta_le
  let ηDel := restrictDeleteVertices η X hXdis
  let TstarDel := deleteGraphVerticesTangle G hT.finite_V hT.finite_E X T_star θ_star
  have hSpanDel : IsSigmaSpan (deleteVertices G X) H ηDel
      (θ_star - X.ncard) θ₀ TstarDel T₀ := theorem_8_2_proof G θ_star θ_span θ₀ T_star H η T X
    hSpan hXsub hXdis hXlt hθ₀pos (by rw [hXCard]; exact Nat.sub_le_sub_right hθOrd χ)
  have hYFin : Y.Finite := H.finite_V.subset hY
  let ys := hYFin.toFinset
  have hys : (ys : Set S) = Y := hYFin.coe_toFinset
  have hysCard : ys.card = δ := (ncard_eq_toFinset_card _ hYFin).symm.trans hYCard
  have hYS : (ys : Set S) ⊆ H.V := hys.symm ▸ hY
  have hYSCard : (ys : Set S).ncard = δ := by rw [ncard_coe_finset, hysCard]
  have hSepYS : ∀ y ∈ (ys : Set S), ∀ z ∈ (ys : Set S), y ≠ z → θ₁ ≤ d₀ {y} {z} := by
    intro y hy z hz hyz
    exact hθ₁₀.trans (hSep₀ y (hys ▸ hy) z (hys ▸ hz) hyz)
  rcases h81 (deleteVertices G X) (θ_star - X.ncard) θ₀ TstarDel H ηDel T₀ d₀
      (ys : Set S) hθ₁₀ hSpanDel hMet₀ hYS hYSCard hSepYS with hHandle | hOld | hEnvCase
  · obtain ⟨S', instS', instT2', H', η', θ', T', hHandle, hφ', hSpan'⟩ := hHandle
    obtain ⟨S'', instS'', instT2'', H'', η'', θ'', T'', hHandle'', hφ'', hSpan''⟩ :=
      theorem_7_1_claim_1 hT hXsub hXltStar
        ⟨S', instS', instT2', H', η', θ', T', hHandle, hφ', hSpan'⟩
    exact Or.inl ⟨S'', instS'', instT2'', H'', η'', θ'', T'', span_isClosedSurface hSpan'',
      hSpan''.isConnected, hHandle'', hφ'', hSpan''⟩
  · obtain ⟨P, s, t, hs, ht, hP, hst, hsy⟩ := hOld
    have hPG : IsHPathWithEnds G η.imageGraph P (η.vMap s) (η.vMap t) :=
      ⟨η.imageGraph_le, hP.2.1.mono (deleteVertices_le G X), hP.2.2⟩
    have hPX : Disjoint X V(P) := disjoint_left.mpr fun x hxX hxP =>
      (hP.2.1.1.vertexSet_mono hxP).2 hxX
    obtain ⟨_, hSelf, _, hSymm, _, _⟩ := GraphMinor.GM11.gm15_theorem_9_1.{w} H θ_span T d hS hConn
      hMet
    have hsyY : ∀ y ∈ Y, ψ ≤ d₀ {s} {y} := hys ▸ hsy
    have hstNe : s ≠ t := fun h => hP.2.2.1 (congrArg η.vMap h)
    refine Or.inr (Or.inl (theorem_7_1_claim_2 hAnim (by omega) ?_ ?_
      (fun _ _ _ _ => Nat.min_le_left _ _) hSymm hSelf hs ht hstNe hPG hPX hst hsyY))
    · dsimp [θ]
      omega
    · dsimp [σ]
      omega
  · obtain ⟨Λ, Z, Tc, dc, hEnv, hZsub, hZCard, _, hComp, hCut⟩ := hEnvCase
    let K := clearEnvelopeDrawing H (ys : Set S) Λ
    let ηK := restrictCleared η (⋃ y ∈ (ys : Set S), Λ y)
    have hCompYS : IsLambdaCompression H K θ₀
        ((4 * γ + 2) * ys.card) T₀ Tc d₀ dc := by simpa only [hysCard] using hComp
    have hAnimYS : IsAnimal G T_star θ_star H η θ₀ T₀ d₀ X (ys : Set S)
        χ ys.card θ₀ ((ζ + τ) + ys.card) := by
      rw [hys, hysCard]
      have hσ : σ = (ζ + τ) + δ := by dsimp [σ]; omega
      rw [← hσ]
      exact hNorm
    obtain ⟨Y', hNew⟩ := animal_after_clearFamily hS ys Λ hγ η
      hAnimYS hEnv hCompYS hθ₂ (by simpa only [hysCard] using hBudget)
    have hNew' : IsAnimal G T_star θ_star K ηK (θ₀ - (4 * γ + 2) * δ) Tc dc X Y'
        χ δ θ₂ (ζ + τ) := by simpa only [hysCard] using hNew
    have hNewSaved := hNew'
    obtain ⟨_, hθ₂Ord, hSpanK, hMetK, _, _, hY', _, _, _, hSep'⟩ := hNewSaved
    have hKDisX : Disjoint V(ηK.imageGraph) X := hXdis.mono
      (restrictCleared_imageGraph_le η (⋃ y ∈ (ys : Set S), Λ y)).vertexSet_mono Subset.rfl
    have hKDisZ : Disjoint V(ηK.imageGraph) Z := disjoint_left.mpr fun x hxK hxZ =>
      (hZsub hxZ).2 hxK
    let Ztot := X ∪ Z
    have hZtotSub : Ztot ⊆ V(G) := union_subset hXsub (fun x hx => (hZsub hx).1.1)
    have hZtotCard : Ztot.ncard ≤ ζ := by
      have hc := ncard_union_le X Z
      rw [hXCard] at hc
      dsimp [Ztot, ζ]
      omega
    have hZtotLt : Ztot.ncard < θ_star :=
      lt_of_le_of_lt hZtotCard (hζθ₂.trans_le (hθ₂Ord.trans hSpanK.isControlling.theta_le))
    have hKDisTot : Disjoint V(ηK.imageGraph) Ztot := hKDisX.union_right hKDisZ
    rcases h83 G θ_star (θ₀ - (4 * γ + 2) * δ) T_star K ηK Tc dc X Y' Ztot
        hNew' hZtotSub hKDisTot subset_union_left hZtotCard with hNext | hClose | hLevel
    · exact Or.inr (Or.inl hNext)
    · obtain ⟨P, s, t, y, z, hs, ht, hy, hz, hyz, hP, hsy, htz⟩ := hClose
      have hCut' : ∀ Q s t, s ∈ K.V → t ∈ K.V →
          IsHPathWithEnds (deleteVertices G X) ηK.imageGraph Q (ηK.vMap s) (ηK.vMap t) →
          2 * ψ ≤ dc {s} {t} → (Z ∩ V(Q)).Nonempty := hCut
      exact False.elim (close_pair_path_contradiction hS ηK hMetK hY' hSep'
        (by omega) hCut' hs ht hy hz hyz hP hsy htz)
    · obtain ⟨dLevel, hLevel⟩ := hLevel
      refine Or.inr (Or.inr ⟨Ztot, K, restrictDeleteVertices ηK Ztot hKDisTot,
        θ₂ - Ztot.ncard, truncation Tc (θ₂ - Ztot.ncard), dLevel,
        hZtotSub, hZtotCard, hZtotLt, ?_, hLevel⟩)
      omega

end GraphMinor.GM16
