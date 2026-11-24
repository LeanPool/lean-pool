/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15o
public import LeanPool.GraphMinor.GM19.SideEdges

/-!
# Graph Minors XIX, (15.2): the metric of the skeleton and free sets

We check the last two hypotheses of (3.2) of Graph Minors XII for the discs of `exists_discFamily`.
If two regions of `sk(Γ)` meet two different discs, then they are far apart in the metric of `sk(Γ)`
(`le_skMetric`), since `dist_le_of_skMetric` compares that
metric with the metric of `Γ`. The set of vertices on each disc is free (`isFreeSet_discEnds`). This
is steps (5) and (6) of the paper.

We also read off the labels of a long side (`exists_isBorderLabels`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM14 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- The edges along a long side, in order, give the labels of the side. -/
theorem exists_isBorderLabels (hS : IsSurface S) (P : ColouredPainting χ) {side : Set S}
  (hside : side ∈ χ.Φ.longSides) : ∃ ω, IsBorderLabels P side ω := by
  classical
  obtain ⟨Θ, hΘ, f, a, b, k, t, e, hsΘ, h⟩ := exists_sideEdges hS χ P.fits hside
  have hkp := h.k_pos
  let g : Fin k → Set S := fun i => e (i.1 + 1)
  have hg : ∀ i, g i ∈ P.Γ.E ∧ g i ⊆ side := fun i =>
    ⟨h.mem _ (by omega), h.subset_side (by omega) (by have := i.2; omega)⟩
  have hlen : (List.ofFn fun i => P.φ (g i)).length = k := List.length_ofFn
  have hinj : Function.Injective g := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h' => hne (Fin.ext h') : i.1 ≠ j.1) with h' | h'
    · exact h.injOn_edges (l := i.1 + 1) (l' := j.1 + 1) (by omega) (by omega)
        (by have := j.2; omega) hij
    · exact h.injOn_edges (l := j.1 + 1) (l' := i.1 + 1) (by omega) (by omega)
        (by have := i.2; omega) hij.symm
  refine ⟨List.ofFn fun i => P.φ (g i), ?_, ?_, Θ, fun i => g (i.cast hlen), a, b, hΘ, hsΘ, ?_,
    ?_, ?_⟩
  · intro h₀
    have : k = 0 := by rw [← hlen, h₀]; rfl
    omega
  · intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hx
    obtain ⟨y, hy⟩ : (g i).Nonempty := (hg i).1.1
    exact P.border_mem _ (hg i).1 side hside.1 ⟨⟨y, hy, (hside.1.2.1 ((hg i).2 hy)).1⟩, (hg i).2⟩
  · refine ⟨h.head, h.last, fun i j hij => ?_, fun i => hg _, fun i j hij x hx y hy => ?_⟩
    · exact Fin.cast_injective hlen (hinj hij)
    · have hij' : i.1 < j.1 := hij
      have hj : j.1 < k := by simpa only [Fin.val_cast] using (j.cast hlen).2
      exact h.inOrder (l := i.1 + 1) (l' := j.1 + 1) (by omega) (by omega) (by omega) hx hy
  · intro c hc hcs
    obtain ⟨l, h₁, h₂, rfl⟩ := h.all c hc hcs
    exact ⟨Fin.cast hlen.symm ⟨l - 1, by omega⟩, by
      change e ((l - 1) + 1) = e l
      rw [Nat.sub_add_cancel h₁]⟩
  · intro i
    simp only [List.getElem_ofFn]
    rfl

variable {D : TangleDatum cap χ} {H G₃ : Drawing Shat}

namespace TangleDatum.SkData

/-- Two edges on the boundary of one region of `sk(Γ)` are close, by way of the centre of the
region. -/
theorem dist_le_of_same_region (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {r : Set Shat}
  (hr : r ∈ H.R) {f₁ c₁ f₂ c₂ : Set S} (hf₁ : D.P.Γ.IsSkEdgeIn f₁ c₁)
    (hfr₁ : cap.emb '' f₁ ⊆ closure r) (hf₂ : D.P.Γ.IsSkEdgeIn f₂ c₂)
    (hfr₂ : cap.emb '' f₂ ⊆ closure r) : D.dist (cap.emb '' c₁) (cap.emb '' c₂) ≤ 12 := by
  have hS := χ.isSurface
  obtain ⟨A, hA⟩ := hd.exists_isAnchors hrep
  obtain ⟨h, ⟨hhr, hhV⟩, -⟩ := hd.pre.2.2.2.1 r hr
  have key : ∀ {f c : Set S}, D.P.Γ.IsSkEdgeIn f c → cap.emb '' f ⊆ closure r → D.dist
    (cap.emb '' c) (A h) ≤ 6 := fun {f c} hf hfr => by
    have hc := hf.1
    obtain ⟨p, q, -, ht, htV, -⟩ := D.P.Γ.sk_line hf.mem
    have hp : p ∈ tilde f := ht ▸ .inl rfl
    have hpV : p ∈ D.P.Γ.V := htV hp
    have hpc : p ∈ tilde c := ⟨closure_minimal hf.subset_closure isClosed_closure hp.1, fun h'
      => D.P.Γ.disjoint_V hc h' hpV⟩
    have hpr : cap.emb p ∈ closure r := closure_minimal hfr isClosed_closure (by
      rw [(cap.isClosedEmbedding hS).closure_image_eq f]
      exact mem_image_of_mem _ hp.1)
    have hcp : D.dist (cap.emb '' c) {cap.emb p} ≤ 3 := by
      have := D.edgeVertDist_self_le hrep hc hpc hpV
      unfold edgeVertDist at this
      rwa [D.atomOf_emb hpV] at this
    have hsingle : ({cap.emb p} : Set Shat) ∈ D.P.Γ.atoms cap := Or.inl (Or.inl ⟨p, hpV, rfl⟩)
    have h₁ := hA.corner r hr h hhr hhV p hpV hpr
    have h₂ := D.dist_triangle hrep (a := cap.emb '' c) (c := A h) hsingle
    rw [D.dist_comm {cap.emb p} (A h)] at h₂
    omega
  have h₁ := key hf₁ hfr₁
  have h₂ := key hf₂ hfr₂
  have h₃ := D.dist_triangle hrep (a := cap.emb '' c₁) (c := cap.emb '' c₂) (hA.atom h hhV)
  rw [D.dist_comm (A h) (cap.emb '' c₂)] at h₃
  omega

/-- **Far in `Γ` means far in `sk(Γ)`.** -/
theorem le_skMetric (hd : D.SkData H G₃) (hrep : 4 ≤ D.rep) {m θ : ℕ} (hmr : m ≤ D.rep) (hm : 1
  ≤ m) (h3m : 3 * m < 2 * D.ord + 3) {ins : Drawing Shat → Set Shat}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) G₃ m (D.skTangle H m) ins) (hθ : θ
      ≤ m) {Δ₁ Δ₂ N₁ N₂ : Set Shat} {a₁ a₂ : Set S} (h₁ : IsAnchoredDisc cap D.P.Γ H Δ₁ N₁ a₁)
    (h₂ : IsAnchoredDisc cap D.P.Γ H Δ₂ N₂ a₂) (hfar : 16 * θ + 12 < D.dist (cap.emb '' a₁)
      (cap.emb '' a₂)) {r₁ r₂ : Set Shat} (hr₁ : r₁ ∈ H.R) (hm₁ : (r₁ ∩ Δ₁).Nonempty)
        (hr₂ : r₂ ∈ H.R)
    (hm₂ : (r₂ ∩ Δ₂).Nonempty) : θ ≤ GM14.tangleMetric H G₃ ins m r₁ r₂ := by
  by_contra hlt
  obtain ⟨-, f₁, hf₁, hfr₁⟩ := h₁.anchor r₁ hr₁ hm₁
  obtain ⟨-, f₂, hf₂, hfr₂⟩ := h₂.anchor r₂ hr₂ hm₂
  by_cases hne : r₁ = r₂
  · subst hne
    have := hd.dist_le_of_same_region hrep hr₁ hf₁ hfr₁ hf₂ hfr₂
    omega
  · have := hd.dist_le_of_skMetric hrep hmr hm h3m hins hr₁ hr₂ hne (by omega) hf₁ hfr₁ hf₂ hfr₂
    omega

end TangleDatum.SkData

namespace TangleDatum

variable {P₀ : ColouredPainting χ} {n : ℕ} {b : Set S → Set S}

/-- **The sets of ends are free.** -/
theorem IsMatchSetting.isFreeSet_discEnds (hM : D.IsMatchSetting P₀ n b)
  (hd : D.SkData H G₃) {m : ℕ} (hmr : m ≤ D.rep) (hm : 1 ≤ m) (h3m : 3 * m < 2 * D.ord + 3) {ins :
    Drawing Shat → Set Shat}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing H) G₃ m (D.skTangle H m) ins)
      (hmn : 2 * m + 12 ≤ n) (i : DiscIndex S P₀) {Δ : Set Shat} {a : Set S}
        (hA : IsAnchoredDisc cap D.P.Γ H Δ (discEnds cap b P₀ i) a)
    (hcard : (discEnds cap b P₀ i).ncard ≤ m) : IsFreeSet H.toHypergraph (D.skTangle H m) m
      (discEnds cap b P₀ i) := by
  classical
  have hS := χ.isSurface
  have hn := hM.large
  have hnr := hM.rep_gt
  have hrep : 4 ≤ D.rep := by omega
  refine ⟨hA.sub_V, hcard, fun A' B' hmem hXA => ?_⟩
  by_contra hord
  rw [not_le] at hord
  rcases i with Θ | e
  · obtain ⟨p, hp, hpΘ, hreg⟩ := D.rad.exists_pole hS Θ.2
    have hrh : D.rad.regionOf p ∈ D.P.Γ.hatRegions cap := (D.rad.regionOf_mem hp.1).1
    have hpr : p ∈ D.rad.regionOf p := (D.rad.regionOf_mem hp.1).2
    have hXr : discEnds cap b P₀ (.inl Θ) ⊆ closure (D.rad.regionOf p) := by
      rw [hreg]
      rintro _ ⟨y, hy, rfl⟩
      have hyΘ := (hM.cuffEnds_subset hS Θ.2 hy).1
      exact Surface.discBd_subset _ (cap.cuffDisc_bd Θ.1 Θ.2 ▸ mem_image_of_mem _ hyΘ)
    obtain ⟨F, hF, hl, hlt, hw⟩ := hd.exists_circuit_of_not_free hmr hm h3m hins
      (hd.sk.hatRegion_mem_R hS hrh) hpr (hd.sub.1 hp.1.1) hA.sub_V hXr hcard hmem hXA hord
    exact no_circuit_holds_cuffEnds hS hM.edge (by omega) hnr hM.free hM.far hp Θ.2 hreg hF
      (by omega) hw hlt
  · obtain ⟨r, hr, hrm⟩ := hA.exists_region
    obtain ⟨hXr, -⟩ := hA.anchor r hr hrm
    obtain ⟨w, ⟨hwr, hwV⟩, -⟩ := hd.pre.2.2.2.1 r hr
    obtain ⟨F, hF, hl, hlt, -⟩ := hd.exists_circuit_of_not_free hmr hm h3m hins hr hwr hwV
      hA.sub_V hXr hcard hmem hXA hord
    have hbm := hM.edge.mem _ e.2.1
    have h3c : (tilde (b e.1)).ncard ≤ 3 := by
      rcases D.P.Γ.size_cases hbm with h | h <;> omega
    exact no_circuit_holds_tilde hS (by omega) hrep hbm h3c (hM.edge.pole_far e.1 e.2.1 e.2.2) hF
      (by omega) hlt

end TangleDatum

end GraphMinor.GM19
