/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46DeficientSeam
public import LeanPool.GraphMinor.GM07.Section2MinVal
public import LeanPool.GraphMinor.GM07.NetSwap
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeContacts
import LeanPool.GraphMinor.GM07.Section46EdgeSegments
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.Section3
import LeanPool.GraphMinor.GM07.Section46CentralLift
import LeanPool.GraphMinor.Surface.DiscFan
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.ChartCells
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.EdgeLoop

/-!
# Steps 9 and 10 of VII (4.6): the side of the disc

Pages 229-230. `F` cuts `Δ` into two discs. The disc of `Σ` is the image of one of them, so the
side `C` of that disc maps into `A ∩ U(J)`: this is claim (2). We prove here the parts of (3) and of
the last page that do not depend on the chosen numbers. If a point of `C` is `l(z)`, the paths at
`z` leave the disc through `A`. A connected part of `U(J)` that misses a vertex of `G` on each side
stays in one edge. A connected part of `bd(Δ)` over one edge lies in one side of a pair, and the
exchange lemma then gives the last inequality.
-/

public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A connected part of `U(J)` that passes through the piece of an edge `e` between two parameters,
and misses the ends of that piece, stays in that piece. -/
theorem subset_edge_piece [T2Space S] {J : Drawing S} {γ : Set S → unitInterval → S}
    (hγ : EdgePar J γ) {e : Set S} (he : e ∈ J.E) {p q : unitInterval} {X : Set S}
    (hX : IsPreconnected X) (hXU : X ⊆ J.U) (hp : γ e p ∉ X) (hq : γ e q ∉ X) {x : S}
    (hxX : x ∈ X) (hx : x ∈ γ e '' Ioo p q) : X ⊆ γ e '' Ioo p q := by
  by_contra hns
  obtain ⟨y, hy, hyn⟩ := not_subset.mp hns
  have hc := hγ.cont e he
  let e₁ : Set S := γ e '' Icc p q
  let E' : Set (Set S) := {g ∈ J.E | g ≠ e}
  let T : Set S := (J.V ∪ ⋃ g ∈ E', closure g) ∪ (γ e '' Iic p ∪ γ e '' Ici q)
  have hE' : E'.Finite := J.finite_edges.subset fun g hg => hg.1
  have hclosed₁ : IsClosed e₁ := (isCompact_Icc.image hc).isClosed
  have hclosedT : IsClosed T := by
    refine ((J.finite_V.isClosed).union (hE'.isClosed_biUnion fun _ _ => isClosed_closure)).union
      (((isClosed_Iic.isCompact).image hc).isClosed.union
        ((isClosed_Ici.isCompact).image hc).isClosed)
  have hopen : ∀ {r}, r ∈ Icc p q → γ e r ∈ X → r ∈ Ioo p q := by
    intro r hr hrX
    refine ⟨lt_of_le_of_ne hr.1 fun h => hp (h ▸ hrX), lt_of_le_of_ne hr.2 fun h => hq (h ▸ hrX)⟩
  have hcov : X ⊆ e₁ ∪ T := by
    intro z hz
    rcases (mem_U_iff_edge J).mp (hXU hz) with h | ⟨g, hg, hzg⟩
    · exact .inr (.inl (.inl h))
    · by_cases hge : g = e
      · subst hge
        obtain ⟨r, hr, rfl⟩ : z ∈ γ g '' Ioo 0 1 := (hγ.image g hg).symm ▸ hzg
        rcases le_total r p with h | h
        · exact .inr (.inr (.inl ⟨r, h, rfl⟩))
        · rcases le_total q r with h' | h'
          · exact .inr (.inr (.inr ⟨r, h', rfl⟩))
          · exact .inl ⟨r, ⟨h, h'⟩, rfl⟩
      · exact .inr (.inl (.inr (mem_iUnion₂.mpr ⟨g, ⟨hg, hge⟩, subset_closure hzg⟩)))
  have hyT : y ∈ T := by
    rcases hcov hy with h | h
    · obtain ⟨r, hr, rfl⟩ := h
      exact (hyn ⟨r, hopen hr hy, rfl⟩).elim
    · exact h
  have hx₁ : x ∈ e₁ := by
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩
  obtain ⟨z, hz, ⟨r, hr, rfl⟩, hzT⟩ := isPreconnected_closed_iff.mp hX e₁ T hclosed₁ hclosedT hcov
    ⟨x, hxX, hx₁⟩ ⟨y, hy, hyT⟩
  have hro := hopen hr hz
  have hr0 : 0 < r := lt_of_le_of_lt unitInterval.nonneg' hro.1
  have hr1 : r < 1 := lt_of_lt_of_le hro.2 unitInterval.le_one'
  have hre : γ e r ∈ e := (hγ.image e he).subset ⟨r, ⟨hr0, hr1⟩, rfl⟩
  have hoffV := (he.2.1 hre).2
  have hne : ∀ {r'}, r' ≠ r → γ e r' ≠ γ e r := by
    intro r' hn heq
    rcases edge_parameter_eq_or_ends hγ he heq with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact hn h
    · exact hr1.ne h
    · exact hr0.ne' h
  rcases hzT with (h | h) | ⟨r', hr', hrz⟩ | ⟨r', hr', hrz⟩
  · exact hoffV h
  · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp h
    rw [← edge_parameter_range hγ hg.1] at hzg
    obtain ⟨t, ht⟩ := hzg
    have ht0 : t ≠ 0 := fun h => hoffV (ht ▸ h ▸ hγ.zero g hg.1)
    have ht1 : t ≠ 1 := fun h => hoffV (ht ▸ h ▸ hγ.one g hg.1)
    have hmem : γ g t ∈ g := (hγ.image g hg.1).subset
      ⟨t, ⟨lt_of_le_of_ne unitInterval.nonneg' ht0.symm,
        lt_of_le_of_ne unitInterval.le_one' ht1⟩, rfl⟩
    exact hg.2 (J.edge_eq_of_mem hg.1 he hmem (ht ▸ hre))
  · exact hne (ne_of_lt (lt_of_le_of_lt hr' hro.1)) hrz
  · exact hne (ne_of_gt (lt_of_lt_of_le hro.2 hr')) hrz

/-- A connected part of `bd(Δ)`, off the ends of the sides and off `bd(Σ)`, lies in one side of a
pair. The closed sides cover it, and two of them meet only at their ends. -/
theorem Net.exists_side_of_connected [T2Space S] (N : Net S) {Y : Set N.D} (hY : IsPreconnected Y)
    (hne : Y.Nonempty) (hbd : Y ⊆ bd N.D) (hoffbd : ∀ y ∈ Y, N.φ y ∉ bd S)
    (hoffV : ∀ y ∈ Y, N.φ y ∉ N.seamV) :
    ∃ i, Y ⊆ range (N.f i) ∨ Y ⊆ range (N.g i) := by
  have : T2Space N.D := N.isSurface_D.2.1
  have : CompactSpace N.D := N.isSurface_D.1
  let T : Fin N.r ⊕ Fin N.r → Set N.D := Sum.elim (fun i => range (N.f i)) (fun i => range (N.g i))
  have hclosed : ∀ j, IsClosed (T j) := by
    rintro (i | i)
    · exact (isCompact_range (N.f i).continuous).isClosed
    · exact (isCompact_range (N.g i).continuous).isClosed
  have hcov : ∀ y ∈ Y, ∃ j, y ∈ T j := by
    intro y hy
    obtain ⟨i, w, -, -, hfib, -⟩ :=
      N.exists_mem_Ioo_of_mem_bd_of_notMem_bd_of_notMem_seamV (hbd hy) (hoffbd y hy) (hoffV y hy)
    have : y ∈ N.φ ⁻¹' {N.φ y} := rfl
    rw [hfib] at this
    rcases this with h | h
    · exact ⟨.inl i, w, h.symm⟩
    · exact ⟨.inr i, w, (mem_singleton_iff.mp h).symm⟩
  have hend : ∀ (i : Fin N.r) (x : unitInterval), x ∉ Ioo (0 : unitInterval) 1 →
      N.φ (N.f i x) ∈ N.seamV := by
    intro i x hx
    have hx' : x = 0 ∨ x = 1 := by
      by_contra hn
      push Not at hn
      exact hx ⟨lt_of_le_of_ne unitInterval.nonneg' hn.1.symm,
        lt_of_le_of_ne unitInterval.le_one' hn.2⟩
    rcases hx' with rfl | rfl
    · exact ⟨i, .inl rfl⟩
    · exact ⟨i, .inr rfl⟩
  have hsep : ∀ j k, j ≠ k → ∀ z ∈ Y, z ∈ T j → z ∉ T k := by
    rintro (i | i) (i' | i') hjk z hz hzj hzk
    · obtain ⟨x, rfl⟩ := hzj
      have hii : i ≠ i' := fun h => hjk (congrArg _ h)
      by_cases hx : x ∈ Ioo (0 : unitInterval) 1
      · exact N.internally_disjoint_ff i i' hii x hx hzk
      · exact hoffV _ hz (hend i x hx)
    · obtain ⟨x, rfl⟩ := hzj
      by_cases hx : x ∈ Ioo (0 : unitInterval) 1
      · exact N.internally_disjoint_fg i i' x hx hzk
      · exact hoffV _ hz (hend i x hx)
    · obtain ⟨x, rfl⟩ := hzj
      by_cases hx : x ∈ Ioo (0 : unitInterval) 1
      · exact N.internally_disjoint_gf i i' x hx hzk
      · exact hoffV _ hz (N.pasting_eq i x ▸ hend i x hx)
    · obtain ⟨x, rfl⟩ := hzj
      have hii : i ≠ i' := fun h => hjk (congrArg _ h)
      by_cases hx : x ∈ Ioo (0 : unitInterval) 1
      · exact N.internally_disjoint_gg i i' hii x hx hzk
      · exact hoffV _ hz (N.pasting_eq i x ▸ hend i x hx)
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨j, hj⟩ := hcov y₀ hy₀
  have hsub : Y ⊆ T j := by
    by_contra hns
    obtain ⟨y₁, hy₁, hy₁n⟩ := not_subset.mp hns
    let Q : Set N.D := ⋃ k ∈ {k | k ≠ j}, T k
    have hQ : IsClosed Q := (toFinite _).isClosed_biUnion fun k _ => hclosed k
    have hc : Y ⊆ T j ∪ Q := by
      intro y hy
      obtain ⟨k, hk⟩ := hcov y hy
      by_cases hkj : k = j
      · exact .inl (hkj ▸ hk)
      · exact .inr (mem_iUnion₂.mpr ⟨k, hkj, hk⟩)
    obtain ⟨k₁, hk₁⟩ := hcov y₁ hy₁
    have hk₁j : k₁ ≠ j := fun h => hy₁n (h ▸ hk₁)
    obtain ⟨z, hz, hzj, hzQ⟩ := isPreconnected_closed_iff.mp hY _ _ (hclosed j) hQ hc
      ⟨y₀, hy₀, hj⟩ ⟨y₁, hy₁, mem_iUnion₂.mpr ⟨k₁, hk₁j, hk₁⟩⟩
    obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp hzQ
    exact hsep j k (Ne.symm hk) z hz hzj hzk
  rcases j with i | i
  · exact ⟨i, .inl hsub⟩
  · exact ⟨i, .inr hsub⟩

/-- The exchange of page 230, for a line `Y` in the side `f i` with the ends of `F`: since the net
is minimal, the side carries at most as many vertices as `F`. -/
theorem Net.subarc_le_of_subset_side (hS : IsSurface S) (N : Net S) (i : Fin N.r) {G : Drawing S}
    (hmin : N.IsMinimalFor G) {F Y : Set N.D} {s t : N.D} (hEnds : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    (hFn : G_D.IsNormal F) (hY : IsLineWithEnds Y s t) (hsub : Y ⊆ range (N.f i))
    (h0 : N.f i 0 ∉ Y) (h1 : N.f i 1 ∉ Y) :
    (N.φ '' (Y \ {s, t}) ∩ G.V).ncard ≤ (N.φ '' (F \ {s, t}) ∩ G.V).ncard := by
  have : T2Space N.D := N.isSurface_D.2.1
  have hα : IsArcMap (N.f i) := ⟨(N.f i).continuous, N.injective_f i⟩
  have hemb : IsEmbedding (N.f i) :=
    ((N.f i).continuous.isClosedEmbedding (N.injective_f i)).isEmbedding
  have hP : IsPreconnected (N.f i ⁻¹' Y) := by
    refine hemb.isInducing.isPreconnected_image.mp ?_
    rw [image_preimage_eq_of_subset hsub]
    exact line_preconnected hY
  have key : ∀ {u v : unitInterval} {s' t' : N.D}, u < v → N.f i u = s' → N.f i v = t' →
      IsLineWithEnds F s' t' → F ∩ bd N.D = {s', t'} → IsLineWithEnds Y s' t' →
      (N.φ '' (Y \ {s', t'}) ∩ G.V).ncard ≤ (N.φ '' (F \ {s', t'}) ∩ G.V).ncard := by
    rintro u v _ _ huv rfl rfl hE hB hL
    have hIcc : Icc u v ⊆ N.f i ⁻¹' Y := hP.ordConnected.out hL.left_mem hL.right_mem
    have hYeq : N.f i '' Icc u v = Y := hL.eq_of_subset
      (isPreconnected_Icc.image _ (N.f i).continuous.continuousOn)
      (image_subset_iff.mpr hIcc) ⟨u, ⟨le_rfl, huv.le⟩, rfl⟩ ⟨v, ⟨huv.le, le_rfl⟩, rfl⟩
    have hu0 : 0 < u := lt_of_le_of_ne unitInterval.nonneg' fun h => h0 (h ▸ hL.left_mem)
    have hv1 : v < 1 := lt_of_le_of_ne unitInterval.le_one' fun h => h1 (h ▸ hL.right_mem)
    have := N.subarc_contacts_le_cutting_contacts hS i u v hu0 huv hv1 hmin hE hB hPull hFn
    rwa [hYeq] at this
  obtain ⟨u, hu⟩ : s ∈ range (N.f i) := hsub hY.left_mem
  obtain ⟨v, hv⟩ : t ∈ range (N.f i) := hsub hY.right_mem
  have hne : u ≠ v := fun h => hY.ne' (hu.symm.trans ((congrArg _ h).trans hv))
  rcases lt_or_gt_of_ne hne with h | h
  · exact key h hu hv hEnds hFbd hY
  · have := key h hv hu (GM07.IsLineWithEnds.symm hEnds) (by rw [pair_comm]; exact hFbd)
      (GM07.IsLineWithEnds.symm hY)
    rwa [pair_comm t s] at this

/-- On a part of a side that misses its ends, `φ` is injective. -/
theorem Net.injOn_of_subset_side (N : Net S) (i : Fin N.r) {Y : Set N.D}
    (hsub : Y ⊆ range (N.f i)) (h0 : N.f i 0 ∉ Y) (h1 : N.f i 1 ∉ Y) : InjOn N.φ Y := by
  intro x hx y hy hxy
  obtain ⟨a, rfl⟩ := hsub hx
  have ha : a ∈ Ioo (0 : unitInterval) 1 :=
    ⟨lt_of_le_of_ne unitInterval.nonneg' fun h => h0 (h ▸ hx),
      lt_of_le_of_ne unitInterval.le_one' fun h => h1 (h ▸ hx)⟩
  rcases N.eq_f_or_g_of_φ_eq_of_mem_Ioo i ha hxy with h | h
  · exact h.symm
  · obtain ⟨b, rfl⟩ := hsub hy
    exact (N.internally_disjoint_gf i i a ha ⟨b, h⟩).elim

/-- The exchange of page 230 for a line `Y` in either side of a pair, off the ends of the sides. -/
theorem Net.contacts_le_of_side (hS : IsSurface S) (N : Net S) (i : Fin N.r) {G : Drawing S}
    (hmin : N.IsMinimalFor G) {F Y : Set N.D} {s t : N.D} (hEnds : IsLineWithEnds F s t)
    (hFbd : F ∩ bd N.D = {s, t}) {G_D : Drawing N.D} (hPull : IsPullbackDrawing N.φ G G_D)
    (hFn : G_D.IsNormal F) (hY : IsLineWithEnds Y s t)
    (hside : Y ⊆ range (N.f i) ∨ Y ⊆ range (N.g i)) (hoff : ∀ y ∈ Y, N.φ y ∉ N.seamV) :
    (N.φ '' (Y \ {s, t}) ∩ G.V).ncard ≤ (N.φ '' (F \ {s, t}) ∩ G.V).ncard ∧ InjOn N.φ Y := by
  have : T2Space S := hS.2.1
  rcases hside with h | h
  · have h0 : N.f i 0 ∉ Y := fun hy => hoff _ hy ⟨i, .inl rfl⟩
    have h1 : N.f i 1 ∉ Y := fun hy => hoff _ hy ⟨i, .inr rfl⟩
    exact ⟨N.subarc_le_of_subset_side hS i hmin hEnds hFbd hPull hFn hY h h0 h1,
      N.injOn_of_subset_side i h h0 h1⟩
  · have h0 : N.g i 0 ∉ Y := fun hy => hoff _ hy ⟨i, .inl (N.pasting_eq i 0)⟩
    have h1 : N.g i 1 ∉ Y := fun hy => hoff _ hy ⟨i, .inr (N.pasting_eq i 1)⟩
    have hf : (N.swapPair i).f i = N.g i := (N.f_swapPair i i).trans (ite_eq_left rfl)
    have hsub : Y ⊆ range ((N.swapPair i).f i) := by rw [hf]; exact h
    have h0' : (N.swapPair i).f i 0 ∉ Y := by rw [hf]; exact h0
    have h1' : (N.swapPair i).f i 1 ∉ Y := by rw [hf]; exact h1
    exact ⟨(N.swapPair i).subarc_le_of_subset_side hS i
      ((N.isMinimalFor_swapPair i G).mpr hmin) hEnds hFbd hPull hFn hY hsub h0' h1',
      (N.swapPair i).injOn_of_subset_side i hsub h0' h1'⟩

/-- The side of the disc, page 229. `F` cuts `Δ` into two discs. One of them, `R`, maps its inside
into the disc `Z`, because the open disc misses `U(J)`. Its side `C` then maps into `A`. This is the
half of claim (2) that we use. -/
theorem Net.exists_disc_side (hS : IsSurface S) (N : Net S) {J : Drawing S}
    (hJ : N.IsSeamGraphFor J) {F : Set N.D} {s t : N.D} {C₁ C₂ : Set N.D}
    (hEnds : IsLineWithEnds F s t) (hFbd : F ∩ bd N.D = {s, t})
    (hC : componentsIn (bd N.D \ {s, t}) = {C₁, C₂}) {Z : Set S} (hZ : IsClosedDisc Z)
    (hmiss : Disjoint (discInt Z) J.U) (hFZ : N.φ '' F ⊆ discBd Z)
    (hZF : discBd Z ⊆ N.φ '' F ∪ J.U) :
    ∃ (R R' C : Set N.D), (C = C₁ ∨ C = C₂) ∧ IsClosedDisc R ∧ IsClosed R' ∧ R ∪ R' = univ ∧
      C ⊆ bd N.D ∧ C ⊆ R ∧ Disjoint C R' ∧ discBd R = C ∪ F ∧
      N.φ '' discInt R ⊆ discInt Z ∧ (∀ x ∈ C, N.φ x ∈ discBd Z) ∧
      IsLineWithEnds (C ∪ {s, t}) s t ∧ C ∩ {s, t} = ∅ := by
  have : T2Space S := hS.2.1
  have : T2Space N.D := N.isSurface_D.2.1
  have hman := hS.2.2
  have hst : s ≠ t := hEnds.ne'
  have hbdU : discBd (univ : Set N.D) = bd N.D := image_bd_homeomorph (Homeomorph.Set.univ N.D)
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hc, d₁, d₂, hu, hi, b₁, b₂, -⟩ := disc_iArc univ F s t
    N.isClosedDisc_D (subset_univ F) hst hEnds (by rw [hbdU]; exact hFbd)
  rw [hbdU] at hc
  have hsbd : s ∈ bd N.D := (hFbd.symm.subset (.inl rfl)).2
  have htbd : t ∈ bd N.D := (hFbd.symm.subset (.inr rfl)).2
  obtain ⟨B₁, B₂, hB, -, hBu, hL₁, hL₂⟩ := oArc_components_diff_pair N.isOArc_bd_D hsbd htbd hst
  have hparts : A₁ ∪ A₂ = bd N.D \ {s, t} ∧ IsLineWithEnds (A₁ ∪ {s, t}) s t ∧
      IsLineWithEnds (A₂ ∪ {s, t}) s t := by
    rcases pair_eq_pair_iff.mp (hc.symm.trans hB) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hBu.symm, hL₁, hL₂⟩
    · exact ⟨by rw [union_comm]; exact hBu.symm, hL₂, hL₁⟩
  obtain ⟨hcover, hline₁, hline₂⟩ := hparts
  have hA₁s : A₁ ⊆ bd N.D \ {s, t} := hcover ▸ subset_union_left
  have hA₂s : A₂ ⊆ bd N.D \ {s, t} := hcover ▸ subset_union_right
  have hsF : ({s, t} : Set N.D) ⊆ F := fun x hx => (hFbd.symm.subset hx).1
  have hmem : ∀ {A}, (A = A₁ ∨ A = A₂) → (A = C₁ ∨ A = C₂) := by
    intro A hAe
    have : A ∈ ({C₁, C₂} : Set (Set N.D)) := by
      rw [← hC, hc]
      rcases hAe with h | h
      · exact .inl h
      · exact .inr h
    exact this
  have key : ∀ {A₁ A₂ Δ₁ Δ₂ : Set N.D}, IsClosedDisc Δ₁ → IsClosedDisc Δ₂ → Δ₁ ∪ Δ₂ = univ →
      Δ₁ ∩ Δ₂ = F → discBd Δ₁ = A₁ ∪ F → discBd Δ₂ = A₂ ∪ F → A₁ ∪ A₂ = bd N.D \ {s, t} →
      A₁ ⊆ bd N.D \ {s, t} → (A₁ = C₁ ∨ A₁ = C₂) → IsLineWithEnds (A₁ ∪ {s, t}) s t →
      ∀ y₀ ∈ discInt Δ₁, N.φ y₀ ∈ discInt Z →
      ∃ (R R' C : Set N.D), (C = C₁ ∨ C = C₂) ∧ IsClosedDisc R ∧ IsClosed R' ∧ R ∪ R' = univ ∧
        C ⊆ bd N.D ∧ C ⊆ R ∧ Disjoint C R' ∧ discBd R = C ∪ F ∧
        N.φ '' discInt R ⊆ discInt Z ∧ (∀ x ∈ C, N.φ x ∈ discBd Z) ∧
        IsLineWithEnds (C ∪ {s, t}) s t ∧ C ∩ {s, t} = ∅ := by
    intro A₁ A₂ Δ₁ Δ₂ d₁ d₂ hu hi b₁ b₂ hcover hA₁s hAC hline y₀ hy₀ hy₀Z
    have hint : ∀ w ∈ discInt Δ₁, w ∉ bd N.D ∧ w ∉ F := by
      intro w hw
      have hwF : w ∉ F := fun h => hw.2 (b₁ ▸ .inr h)
      refine ⟨fun hb => ?_, hwF⟩
      have hws : w ∉ ({s, t} : Set N.D) := fun h => hwF (hsF h)
      rcases (hcover ▸ (⟨hb, hws⟩ : w ∈ bd N.D \ {s, t}) : w ∈ A₁ ∪ A₂) with h | h
      · exact hw.2 (b₁ ▸ .inl h)
      · have hw₂ : w ∈ Δ₂ := Surface.discBd_subset _ (b₂ ▸ .inl h)
        exact hwF (hi ▸ ⟨hw.1, hw₂⟩)
    have hoff : ∀ w ∈ discInt Δ₁, N.φ w ∉ discBd Z := by
      intro w hw hwA
      obtain ⟨hwb, hwF⟩ := hint w hw
      rcases hZF hwA with ⟨y, hy, hyw⟩ | h
      · exact hwF ((N.interior_inj w hwb y hyw.symm) ▸ hy)
      · exact hwb (N.preimage_seamU ▸ (hJ.2.1 ▸ h : N.φ w ∈ N.seamU))
    have hcon : IsPreconnected (N.φ '' discInt Δ₁) :=
      d₁.isPreconnected_discInt.image _ N.quotientMap_φ.continuous.continuousOn
    have hdis : Disjoint (N.φ '' discInt Δ₁) (discBd Z) := by
      rw [disjoint_left]
      rintro _ ⟨w, hw, rfl⟩
      exact hoff w hw
    have hsub : N.φ '' discInt Δ₁ ⊆ discInt Z := by
      rcases hZ.side hman hcon hdis with h | h
      · exact h
      · exact (disjoint_left.mp h (mem_image_of_mem _ hy₀) hy₀Z.1).elim
    have hΔ : N.φ '' Δ₁ ⊆ Z := by
      have h₁ := image_mono (f := N.φ) d₁.subset_closure_discInt
      have h₂ := image_closure_subset_closure_image (s := discInt Δ₁)
        N.quotientMap_φ.continuous
      exact (h₁.trans h₂).trans (closure_minimal (hsub.trans (discInt_subset Z)) hZ.isClosed)
    have hA₁Δ : A₁ ⊆ Δ₁ := fun x hx => Surface.discBd_subset _ (b₁ ▸ .inl hx)
    refine ⟨Δ₁, Δ₂, A₁, hAC, d₁, d₂.isClosed, hu, fun x hx => (hA₁s hx).1, hA₁Δ, ?_, b₁, hsub, ?_,
      hline, ?_⟩
    · rw [disjoint_left]
      intro x hx hx₂
      have hxF : x ∈ F := hi ▸ ⟨hA₁Δ hx, hx₂⟩
      exact (hA₁s hx).2 (hFbd ▸ ⟨hxF, (hA₁s hx).1⟩)
    · intro x hx
      have hxZ : N.φ x ∈ Z := hΔ (mem_image_of_mem _ (hA₁Δ hx))
      by_contra hn
      have hxU : N.φ x ∈ J.U := hJ.2.1 ▸ mem_image_of_mem N.φ (hA₁s hx).1
      exact disjoint_left.mp hmiss ⟨hxZ, hn⟩ hxU
    · exact eq_empty_of_forall_notMem fun x hx => (hA₁s hx.1).2 hx.2
  obtain ⟨x₀, hx₀⟩ := hZ.nonempty_discInt
  have hx₀U : x₀ ∉ J.U := fun h => disjoint_left.mp hmiss hx₀ h
  obtain ⟨y₀, rfl⟩ := N.quotientMap_φ.surjective x₀
  have hy₀b : y₀ ∉ bd N.D := fun h => hx₀U (hJ.2.1 ▸ mem_image_of_mem N.φ h)
  have hy₀F : y₀ ∉ F := fun h => hx₀.2 (hFZ (mem_image_of_mem _ h))
  have hy₀u : y₀ ∈ Δ₁ ∪ Δ₂ := hu ▸ mem_univ y₀
  rcases hy₀u with h | h
  · refine key d₁ d₂ hu hi b₁ b₂ hcover hA₁s (hmem (.inl rfl)) hline₁ y₀ ⟨h, ?_⟩ hx₀
    rintro hb
    rw [b₁] at hb
    rcases hb with h' | h'
    · exact hy₀b (hA₁s h').1
    · exact hy₀F h'
  · refine key d₂ d₁ (by rwa [union_comm]) (by rwa [inter_comm]) b₂ b₁ (by rwa [union_comm]) hA₂s
      (hmem (.inr rfl)) hline₂ y₀ ⟨h, ?_⟩ hx₀
    rintro hb
    rw [b₂] at hb
    rcases hb with h' | h'
    · exact hy₀b (hA₂s h').1
    · exact hy₀F h'

/-- A walk in a graph with edges off `A`, from a point of the open disc to a point outside it, has a
vertex on `A`. -/
private theorem exists_exit [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {Γ : Drawing S}
    {Z : Set S} (hZ : IsClosedDisc Z) (hnorm : ∀ e ∈ Γ.E, Disjoint e (discBd Z)) {u v : S}
    (W : GraphWalk Γ.toGraph u v) (hu : u ∈ discInt Z) (hv : v ∉ discInt Z) :
    ∃ y ∈ W.support, y ∈ discBd Z := by
  induction W with
  | nil h => exact (hv hu).elim
  | @cons a m b e hl r ih =>
    by_cases hm : m ∈ discInt Z
    · obtain ⟨y, hy, hyA⟩ := ih hm hv
      exact ⟨y, by simp [hy], hyA⟩
    · have hopen := hZ.isOpen_discInt hman
      have hau : a ∈ closure e := by
        have : a ∈ closure e ∩ Γ.V := hl.2.2.2.symm ▸ mem_insert a {m}
        exact this.1
      have hmc : m ∈ closure e := by
        have : m ∈ closure e ∩ Γ.V := hl.2.2.2.symm ▸ mem_insert_of_mem a (mem_singleton m)
        exact this.1
      obtain ⟨y, hyS, hye⟩ := mem_closure_iff.mp hau _ hopen hu
      have hsub : e ⊆ discInt Z := by
        rcases hZ.side hman hl.1.2.2.1.isConnected.isPreconnected (hnorm e hl.1) with h | h
        · exact h
        · exact (disjoint_left.mp h hye hyS.1).elim
      have hmZ : m ∈ Z := closure_minimal (hsub.trans (discInt_subset Z)) hZ.isClosed hmc
      have hmA : m ∈ discBd Z := by
        by_contra hn
        exact hm ⟨hmZ, hn⟩
      exact ⟨m, by simp [r.start_mem_support], hmA⟩

/-- Claim (3) of VII (4.6), page 229, its main step: the point `l(z)` is not on the side `C`. The
first edges of the `μ` paths at `z` lie in the open disc, and each path ends outside it. So each
path
meets `A` again. There are fewer than `μ` such vertices, so by (b) `A` meets another cuff, and this
contradicts (i). -/
theorem no_lift_on_side [T2Space S] (hman : ∀ x : S, IsManifoldPoint x) {G J : Drawing S}
    {Z : Set S} {μ v : ℕ} (hZ : IsClosedDisc Z) (hmiss : Disjoint (discInt Z) J.U)
    (hbdJ : bd S ⊆ J.U) (hAn : G.IsNormal (discBd Z)) (hAc : (discBd Z ∩ G.V).ncard ≤ μ)
    (hμv : μ ≤ v)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ v →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    {z : S} (hzV : z ∈ G.V) (hzA : z ∈ discBd Z) {C : Set S} (hC : C ∈ cuffs S) (hzC : z ∈ C)
    {n : ℕ} {P : Fin n → Drawing S} {e : Fin n → S}
    (hP : ∀ i, (P i).IsSubdrawing G ∧ e i ∈ G.V ∩ (bd S \ C) ∧ (P i).IsPathBetween z (e i))
    (hd : ∀ i j, i ≠ j → Disjoint ((P i).V \ {z, e i}) ((P j).V \ {z, e j}))
    {I : Finset (Fin n)} (hI : μ ≤ I.card)
    (hfirst : ∀ i ∈ I, ∃ f ∈ (P i).E, z ∈ closure f ∧ f ⊆ discInt Z) : False := by
  classical
  have hbdC : C ⊆ bd S := fun x hx => sUnion_cuffs (S := S) ▸ ⟨C, hC, hx⟩
  have hzbd : z ∈ bd S := hbdC hzC
  have hedgeoff : ∀ {Γ : Drawing S}, Γ.IsSubdrawing G → ∀ f ∈ Γ.E, Disjoint f (discBd Z) := by
    intro Γ hΓ f hf
    rw [disjoint_left]
    intro x hxf hxA
    have hfG := hΓ.2 hf
    have hxU : x ∈ G.U := (hfG.2.1 hxf).1
    exact (hfG.2.1 hxf).2 (hAn ⟨hxA, hxU⟩)
  have hexit : ∀ i ∈ I, ∃ y ∈ (P i).V, y ≠ z ∧ y ∈ discBd Z := by
    intro i hiI
    obtain ⟨f, hf, hzf, hfS⟩ := hfirst i hiI
    obtain ⟨hPs, hei, W, hW, hV, hE⟩ := hP i
    have heoff : e i ∉ discInt Z := fun h =>
      disjoint_left.mp hmiss h (hbdJ hei.2.1)
    have hfW : f ∈ W.edges := by
      have : f ∈ {e | e ∈ W.edges} := hE ▸ hf
      exact this
    cases W with
    | nil h => simp at hfW
    | @cons a m b f₀ hl r =>
      have hne : z ∉ r.support := (List.nodup_cons.mp hW).1
      have hf₀ : f₀ = f := by
        rcases List.mem_cons.mp hfW with h | h
        · exact h.symm
        · exfalso
          obtain ⟨p, q, hpq⟩ := ((P i).toGraph.edge_mem_iff_exists_isLink f).mp hf
          have hzV' : z ∈ (P i).V := hl.left_mem
          have hz' : z ∈ closure f ∩ (P i).V := ⟨hzf, hzV'⟩
          rw [hpq.2.2.2] at hz'
          rcases hz' with rfl | h'
          · exact hne (r.left_mem_support_of_mem_edges h hpq)
          · have hzq : z = q := h'
            rw [← hzq] at hpq
            exact hne (r.left_mem_support_of_mem_edges h hpq.symm)
      subst hf₀
      have hmc : m ∈ closure f₀ := by
        have : m ∈ closure f₀ ∩ (P i).V := hl.2.2.2.symm ▸ mem_insert_of_mem z (mem_singleton m)
        exact this.1
      have hmZ : m ∈ Z := closure_minimal (hfS.trans (discInt_subset Z)) hZ.isClosed hmc
      by_cases hmA : m ∈ discBd Z
      · refine ⟨m, ?_, fun h => hne (h ▸ r.start_mem_support), hmA⟩
        rw [hV]
        simp [r.start_mem_support]
      · obtain ⟨y, hy, hyA⟩ := exists_exit hman hZ (hedgeoff hPs) r ⟨hmZ, hmA⟩ heoff
        refine ⟨y, ?_, fun h => hne (h ▸ hy), hyA⟩
        rw [hV]
        simp [hy]
  have hexit' : ∀ i, ∃ y, i ∈ I → y ∈ (P i).V ∧ y ≠ z ∧ y ∈ discBd Z := fun i => by
    by_cases hiI : i ∈ I
    · obtain ⟨y, h₁, h₂, h₃⟩ := hexit i hiI
      exact ⟨y, fun _ => ⟨h₁, h₂, h₃⟩⟩
    · exact ⟨z, fun h => (hiI h).elim⟩
  choose y hy using hexit'
  have hyV : ∀ i ∈ I, y i ∈ (P i).V := fun i h => (hy i h).1
  have hyz : ∀ i ∈ I, y i ≠ z := fun i h => (hy i h).2.1
  have hyA : ∀ i ∈ I, y i ∈ discBd Z := fun i h => (hy i h).2.2
  have hfin : (discBd Z ∩ G.V).Finite := G.finite_V.subset inter_subset_right
  let Tg : Finset S := (hfin.toFinset).erase z
  have hTg : Tg.card < μ := by
    have hcard : hfin.toFinset.card = (discBd Z ∩ G.V).ncard :=
      (ncard_eq_toFinset_card _ hfin).symm
    have hz : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hzA, hzV⟩
    have := Finset.card_erase_lt_of_mem hz
    change (hfin.toFinset.erase z).card < μ
    omega
  have hmaps : ∀ i ∈ I, y i ∈ Tg := fun i hiI => Finset.mem_erase.mpr
    ⟨hyz i hiI, hfin.mem_toFinset.mpr ⟨hyA i hiI, (hP i).1.1 (hyV i hiI)⟩⟩
  obtain ⟨i, hiI, j, hjI, hij, hyy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (lt_of_lt_of_le hTg hI) hmaps
  have hyend : y i = e i ∨ y i = e j := by
    by_contra hn
    push Not at hn
    refine disjoint_left.mp (hd i j hij) ⟨hyV i hiI, ?_⟩ ⟨hyy ▸ hyV j hjI, ?_⟩
    · rintro (h | h)
      · exact hyz i hiI h
      · exact hn.1 h
    · rintro (h | h)
      · exact hyz i hiI h
      · exact hn.2 h
  have hyoff : y i ∈ bd S \ C := by
    rcases hyend with h | h
    · exact h ▸ ((hP i).2.1).2
    · exact h ▸ ((hP j).2.1).2
  obtain ⟨L₁, L₂, hL₁, -, hu, -⟩ := IsOArc.lines hZ.isOArc_discBd hzA (hyA i hiI)
    (hyz i hiI).symm
  have hsub : L₁ ⊆ discBd Z := fun x hx => hu ▸ Or.inl hx
  have hle : (G.V ∩ L₁).ncard ≤ v := by
    have h₁ : (G.V ∩ L₁).ncard ≤ (discBd Z ∩ G.V).ncard :=
      Set.ncard_le_ncard (fun x hx => ⟨hsub hx.2, hx.1⟩) hfin
    omega
  obtain ⟨C', hC', hends⟩ := hi L₁ (fun x hx => hAn ⟨hsub hx.1, hx.2⟩)
    ⟨z, y i, hzbd, hyoff.1, hL₁⟩ hle
  have hzC' : z ∈ C' := hends ⟨y i, hL₁⟩
  have hyC' : y i ∈ C' := hends ⟨z, GM07.IsLineWithEnds.symm hL₁⟩
  have hCC : C' = C := by
    by_contra hne
    exact disjoint_left.mp (cuffs_disjoint hC' hC hne) hzC' hzC
  exact hyoff.2 (hCC ▸ hyC')

end GraphMinor.GM07
