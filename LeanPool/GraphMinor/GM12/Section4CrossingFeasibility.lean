/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliqueCrossingSource
public import LeanPool.GraphMinor.GM12.Section4OneCrossingDiscSystem
public import LeanPool.GraphMinor.GM12.Section4EmbeddedOppositeContacts
public import LeanPool.GraphMinor.GM12.Section4QuadPartitionTransport
public import LeanPool.GraphMinor.GM12.Section4CrossingEndClasses
import LeanPool.GraphMinor.GM12.Section4PlaneChart
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.Surface.Wedge

/-!
# The feasible crossing partition of XII (4.5)

We assemble claim (1), page 253. Construct the one-crossing
subdivision of a clique, label its two edges at each crossing,
and choose the protected small crossing discs. Carry the plane
configuration into a surface chart and thicken its vertex
stars. Match the resulting four-marked disc family to any
prescribed family. The transported vertex discs witness the
feasibility condition, and the transported edge ends give the
required opposite pairs. The graph, crossing count, partition,
and all disc witnesses are constructed in the proof.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph Metric

/-- The ordered-parameter form of Graph Minors XII, (4.5), claim (1), page 253: the source
subdivision supplies a feasible endpoint partition on any
prescribed disjoint four-marked discs. The witness discs are
stated explicitly so that the vertex type can be relabelled
when applying (3.2). This source construction works for `p ≥ 4`.
The paper uses it after reducing to `p ≥ 5`. -/
theorem theorem_4_5_claim_1_ordered {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W E : Type) (L : Graph W E) (κ : E × Bool → W) (t : ℕ) (σ : Fin t × Bool ≃ E),
      Finite W ∧ Finite E ∧ IsIsoMinor (GM16.completeGraph p) L ∧
      L.vertexSet = univ ∧ L.edgeSet = univ ∧
      (∀ e, L.IsLink e (κ (e, false)) (κ (e, true))) ∧
      (∀ e, κ (e, false) ≠ κ (e, true)) ∧ 2 ≤ t ∧
      (∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
        κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w) ∧
      ∀ (Δ : Fin t → Set S) (q : Fin t → Circle → S) (β : Fin t → Fin 4 → ℝ),
        (∀ i, IsClosedDisc (Δ i)) → Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
        (∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (Δ i)) →
        (∀ i, StrictMono (β i)) → (∀ i j, β i j ∈ Ico 0 1) →
        ∃ (ends : E × Bool → S) (B : W → Set S), Function.Injective ends ∧
          (∀ w, IsClosedDisc (B w)) ∧ Pairwise (fun w z => Disjoint (B w) (B z)) ∧
          (∀ w, B w ∩ (⋃ i, Δ i) = edgeEndClass ends κ w) ∧
          (∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) =
            {q i (ee (β i 0)), q i (ee (β i 2))}) ∧
          (∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) =
            {q i (ee (β i 1)), q i (ee (β i 3))}) := by
  classical
  obtain ⟨W, E, L, v, κ, P, hW, hE, hminor, hvinj, hLV, hLE, hlink, hPline,
    hPV, _, htriple, hcross, htwo, hM, hMtwo, _, hlocal⟩ := exists_clique_one_crossing_source hp
  have hκne : ∀ e, κ (e, false) ≠ κ (e, true) := by
    intro e heq
    obtain ⟨g, hg, -, hg0, hg1⟩ := (hPline e).exists_arc
    have h01 : g 0 = g 1 := hg0.trans ((congrArg v heq).trans hg1.symm)
    exact (show (0 : unitInterval) ≠ 1 by norm_num) (hg.2 h01)
  let : Finite W := hW
  let : Finite E := hE
  let : Fintype W := Fintype.ofFinite W
  let : Fintype E := Fintype.ofFinite E
  let X := edgeMeetingPoints v P
  let : Fintype X := hM.fintype
  let t := Fintype.card X
  let ν : Fin t ≃ X := (Fintype.equivFin X).symm
  obtain ⟨σ₀, A, r, D, hpair, hpos, hD, hDD, hcentre, hDv, hDP, hleft, hright, hcoord⟩ :=
    exists_one_crossing_disc_system v P (fun e => (hPline e).isCompact.isClosed)
      hM htriple hcross hlocal
  let σ : Fin t × Bool ≃ E := (ν.prodCongr (Equiv.refl Bool)).trans σ₀
  have ht : 2 ≤ t := by
    have hcard : Fintype.card X = X.ncard := fintypeCard_eq_ncard X
    change 2 ≤ Fintype.card X
    rw [hcard]
    exact hMtwo
  have hxV : ∀ x : X, x.val ∉ range v := by
    intro x
    obtain ⟨_, _, _, _, hx⟩ := x.property
    exact hx
  have htwoX := two_crossing_classes_of_noncrossing_pairs v P κ Subtype.val σ₀ hxV hpair
    (fun e w hw => (hPV e w).mp hw) (fun w => by
      obtain ⟨e, f, _, hef⟩ := htwo w
      exact ⟨e, f, hef⟩)
  have htwoFin : ∀ w, ∃ i j : Fin t, i ≠ j ∧ ∃ b c d e : Bool,
      κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w := by
    intro w
    obtain ⟨i, j, hij, b, c, d, e, hκi, hκj⟩ := htwoX w
    refine ⟨ν.symm i, ν.symm j, (fun h => hij (ν.symm.injective h)), b, c, d, e, ?_, ?_⟩
    · simpa only [σ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
        ν.apply_symm_apply] using hκi
    · simpa only [σ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
        ν.apply_symm_apply] using hκj
  obtain ⟨f, hf⟩ := exists_plane_openEmbedding hS
  obtain ⟨ends₀, B₀, hends₀, hB₀, hB₀B₀, hcontact₀, hpair₀, hpair₁⟩ :=
    exists_embedded_opposite_contacts hS f hf v hvinj κ P hPline
      (fun e w hw => (hPV e w).mp hw) hcross hM σ₀ A r D hpair hD hcentre hDv hDP hleft hright
  let C : X → Set S := fun x => f '' D x
  let sourceParam : X → Circle → S := fun x w => f (crossDiscParam (A x) x.val (r x) w)
  have himage : ∀ x : X, IsClosedDisc (C x) ∧ discBd (C x) = f '' discBd (D x) :=
    fun x => Surface.isClosedDisc_image_injOn (hD x) (hD x).isCompact hf.continuous.continuousOn
      hf.injective.injOn
  have hCC : Pairwise (fun x y : X => Disjoint (C x) (C y)) :=
    fun x y hxy => (disjoint_image_iff hf.injective).mpr (hDD x y hxy)
  have hp : ∀ x : X, Continuous (sourceParam x) ∧ Function.Injective (sourceParam x) ∧
      range (sourceParam x) = discBd (C x) := by
    intro x
    have hp₀ := crossDiscParam_properties (A x) x.val (hpos x)
    rw [← hcoord x] at hp₀
    refine ⟨hf.continuous.comp hp₀.1, hf.injective.comp hp₀.2.1, ?_⟩
    change range (f ∘ crossDiscParam (A x) x.val (r x)) = _
    rw [range_comp, hp₀.2.2, (himage x).2]
  refine ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htwoFin, ?_⟩
  intro Δ q β hΔ hΔΔ htarget hβ hβ01
  have hβ03 : ∀ x : X, β (ν.symm x) 3 < β (ν.symm x) 0 + 1 := fun x => by
    linarith [(hβ01 (ν.symm x) 3).2, (hβ01 (ν.symm x) 0).1]
  obtain ⟨ends, B, hinj, hB, hBB, hcontact, h0, h1⟩ := exists_quad_partition_transport hS C
    (fun x : X => Δ (ν.symm x)) B₀ (fun x => (himage x).1) (fun x => hΔ (ν.symm x)) hCC
    (fun x y hxy => hΔΔ (fun h => hxy (ν.symm.injective h))) hB₀ hB₀B₀ sourceParam
    (fun x => q (ν.symm x)) hp (fun x => htarget (ν.symm x))
    σ₀ ends₀ κ hends₀ hcontact₀ hpair₀ hpair₁
    (fun x => β (ν.symm x) 0) (fun x => β (ν.symm x) 1)
    (fun x => β (ν.symm x) 2) (fun x => β (ν.symm x) 3)
    (fun x => hβ (ν.symm x) (by decide)) (fun x => hβ (ν.symm x) (by decide))
    (fun x => hβ (ν.symm x) (by decide)) hβ03
  have hunion : (⋃ x : X, Δ (ν.symm x)) = ⋃ i : Fin t, Δ i := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨ν.symm x, hx⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨ν i, by simpa only [ν.symm_apply_apply] using hi⟩
  refine ⟨ends, B, hinj, hB, hBB, ?_, ?_, ?_⟩
  · intro w
    rw [← hunion]
    exact hcontact w
  · intro i
    simpa only [σ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      ν.symm_apply_apply] using h0 (ν i)
  · intro i
    simpa only [σ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
      ν.symm_apply_apply] using h1 (ν i)

end GraphMinor.GM12
