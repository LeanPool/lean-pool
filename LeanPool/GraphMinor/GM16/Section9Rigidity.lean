/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Dials
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM16.Section9Circles
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.Section3

/-!
# Rigidity after clearing a family of zones

This proves Claim (2) in the proof of XVI (8.1). A normal circle can
enter at most one zone. Use rigidity after clearing that one zone,
then show that its dial misses all the other zones.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- Graph Minors XVI, proof of (8.1), Claim (2), page 71. Clearing
pairwise disjoint zones preserves rigidity when each single clearing does. -/
theorem clearFamily_isRigid {H : Drawing S} {d : Set S → Set S → ℕ}
    {Y : Set S} {γ : ℕ} {Λ : S → Set S} (hH : IsRigid H)
    (hZone : ∀ y ∈ Y, IsLambdaZoneAround H d γ {y} (Λ y))
    (hdis : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → Disjoint (closure (Λ y₁)) (closure (Λ y₂)))
    (hRigid : ∀ y ∈ Y, IsRigid (clearedSubdrawing H (Λ y))) :
    IsRigid (clearEnvelopeDrawing H Y Λ) := by
  classical
  by_cases hY : Y.Nonempty
  swap
  · have he : Y = ∅ := not_nonempty_iff_eq_empty.mp hY
    subst Y
    have heU : (⋃ y ∈ (∅ : Set S), Λ y) = ∅ := by simp
    change IsRigid (H.interSet (univ \ (⋃ y ∈ (∅ : Set S), Λ y)))
    rw [heU, sdiff_empty, drawing_interSet_univ]
    exact hH
  intro F hF hNormal hCard
  let K := clearEnvelopeDrawing H Y Λ
  have hKU : K.U = H.U \ (⋃ y ∈ Y, Λ y) := clearFamily_U hZone
  have hclosed : IsClosed (univ \ (⋃ y ∈ Y, Λ y)) :=
    isClosed_univ.sdiff (isOpen_iUnion fun y => isOpen_iUnion fun hy => (hZone y hy).isOpenDisc.1)
  obtain ⟨j, hj, hAvoid⟩ : ∃ j ∈ Y, ∀ k ∈ Y, k ≠ j → Disjoint F (Λ k) := by
    by_cases hm : ∃ j ∈ Y, (F ∩ Λ j).Nonempty
    · obtain ⟨j, hj, hm⟩ := hm
      refine ⟨j, hj, fun k hk hkj => ?_⟩
      apply disjoint_left.mpr
      intro x hxF hxk
      exact oArc_not_meet_two_discs hF (hZone j hj).isOpenDisc.1
        (hZone k hk).isOpenDisc.1 (hdis j hj k hk (Ne.symm hkj))
        (zone_boundary_subset_clearFamily hZone hdis hj)
        (zone_boundary_subset_clearFamily hZone hdis hk) hNormal hCard ⟨hm, x, hxF, hxk⟩
    · obtain ⟨j, hj⟩ := hY
      exact ⟨j, hj, fun k hk _ => disjoint_left.mpr fun x hxF hxk => hm ⟨k, hk, x, hxF, hxk⟩⟩
  let J := clearedSubdrawing H (Λ j)
  have hJU : J.U = H.U \ Λ j := clearedSubdrawing_U (hZone j hj)
  have hJclosed : IsClosed (univ \ Λ j) := isClosed_univ.sdiff (hZone j hj).isOpenDisc.1
  have hOut : ∀ x ∈ F, x ∉ Λ j → x ∉ ⋃ y ∈ Y, Λ y := by
    intro x hxF hxj hxU
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxU
    by_cases heq : k = j
    · exact hxj (heq ▸ hxk)
    · exact (hAvoid k hk heq).notMem_of_mem_left hxF hxk
  have hFV : F ∩ K.V = F ∩ J.V := by
    ext x
    simp only [K, J, clearEnvelopeDrawing, clearedSubdrawing,
      mem_inter_iff, mem_interSet_V_iff hclosed, mem_interSet_V_iff hJclosed]
    constructor
    · rintro ⟨hxF, hxH, _, hxU⟩
      exact ⟨hxF, hxH, mem_univ _, fun hxj => hxU (mem_iUnion₂.mpr ⟨j, hj, hxj⟩)⟩
    · rintro ⟨hxF, hxH, _, hxj⟩
      exact ⟨hxF, hxH, mem_univ _, hOut x hxF hxj⟩
  have hNormalJ : F ∩ J.U ⊆ J.V := by
    rintro x ⟨hxF, hxJ⟩
    have hx := hJU ▸ hxJ
    have hxK : x ∈ K.U := hKU ▸ ⟨hx.1, hOut x hxF hx.2⟩
    exact (congrArg (fun A : Set S => x ∈ A) hFV).mp ⟨hxF, hNormal ⟨hxF, hxK⟩⟩ |>.2
  obtain ⟨Δ, hDial⟩ := hRigid j hj F hF hNormalJ (hFV ▸ hCard)
  have hΔavoid : ∀ k ∈ Y, k ≠ j → Disjoint Δ (Λ k) := by
    intro k hk hkj
    apply dial_disjoint_open_disc hDial hNormalJ (hZone k hk).isOpenDisc
      (hZone k hk).isOArc_bd _ (hAvoid k hk hkj)
    apply oArc_subset_interSet_U (hZone k hk).isOArc_bd (hZone k hk).bd_subset_U
    intro x hx
    exact ⟨mem_univ _, fun hxj => (hdis k hk j hj hkj).notMem_of_mem_left hx.1 (subset_closure hxj)⟩
  have hSub : K.IsSubdrawing J := drawing_interSet_mono_closed H hclosed hJclosed
    (fun x hx => ⟨mem_univ _, fun hxj => hx.2 (mem_iUnion₂.mpr ⟨j, hj, hxj⟩)⟩)
  have hInter : J.interSet Δ = K.interSet Δ := by
    rw [show J = H.interSet (univ \ Λ j) from rfl,
      show K = H.interSet (univ \ ⋃ y ∈ Y, Λ y) from rfl,
      drawing_interSet_inter_closed H hJclosed hDial.1.isClosed,
      drawing_interSet_inter_closed H hclosed hDial.1.isClosed]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨_, hxj⟩, hxΔ⟩
      refine ⟨⟨mem_univ _, ?_⟩, hxΔ⟩
      intro hxU
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxU
      by_cases heq : k = j
      · exact hxj (heq ▸ hxk)
      · exact (hΔavoid k hk heq).notMem_of_mem_left hxΔ hxk
    · rintro ⟨⟨_, hxU⟩, hxΔ⟩
      exact ⟨⟨mem_univ _, fun hxj => hxU (mem_iUnion₂.mpr ⟨j, hj, hxj⟩)⟩, hxΔ⟩
  exact ⟨Δ, dial_of_subdrawing_same_inter hDial hSub hFV hInter⟩

/-- The battlefields chosen in XVI (8.1), page 71, form an envelope.
The rigidity clause holds for every subfamily by Claim (2). -/
theorem envelope_of_battlefields {H : Drawing S}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β : ℕ} {Y : Set S}
    {Λ : S → Set S} {C : S → Drawing S} {X : S → Set S}
    (hH : IsRigid H) (hY : Y ⊆ H.V)
    (hBattle : ∀ y ∈ Y, IsBattlefield H T d θ β {y} (Λ y) (C y) (X y))
    (hdis : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ ≠ y₂ → Disjoint (closure (Λ y₁)) (closure (Λ y₂))) :
    IsEnvelope H d Y (3 * β + 3) Λ := by
  refine ⟨hY, fun y hy => (hBattle y hy).isZone, hdis, ?_⟩
  intro Y' hYY
  exact clearFamily_isRigid hH (fun y hy => (hBattle y (hYY hy)).isZone)
    (fun y hy z hz hne => hdis y (hYY hy) z (hYY hz) hne)
    (fun y hy => (hBattle y (hYY hy)).isRigid_cleared)

end GraphMinor.GM16
