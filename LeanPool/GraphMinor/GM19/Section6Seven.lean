/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Rep
public import LeanPool.GraphMinor.GM11.Section64

/-!
# Graph Minors XIX, (6.7)

**(6.7)** (page 342): if `Γ` is an internally 3-connected painting in a surface `Σ`, then `sk(Γ)` is
a
block and `rep(sk(Γ)) = rep(Γ)`. The first part is `sk_isBlock`. For the second part, a
non-null-homotopic
circuit of `Γ*` with `2m` edges is an `sk(Γ)`-normal `O`-arc with `m` vertices. The converse is
`rep_le_sk`, which needs each vertex of `sk(Γ)` to have at least two half-edges. A block has this
property, unless it is one edge with its two ends. In that case each `O`-arc is null-homotopic,
since a
disc around the edge leaves only an open disc (`null_of_single_edge`).
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

theorem drawing_eq {T : Type} [TopologicalSpace T] {D D' : Drawing T} (hU : D.U = D'.U)
    (hV : D.V = D'.V) : D = D' := by
  cases D
  cases D'
  simp_all

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {Γ : Painting S} {D : Drawing Shat}

omit [T2Space Shat] in
theorem sk_loopFree (hS : IsSurface S) (hD : IsSkHat cap Γ D) : LoopFree D := by
  intro e he
  obtain ⟨u, w, huw, hset⟩ := hD.no_loops hS e he
  exact ⟨u, w, huw, by rw [tilde_eq_inter_V D he, hset], isLine_closure he huw hset⟩

omit [T2Space Shat] in
omit [T2Space S] in
/-- A radial drawing of `Γ` extends to a radial drawing of `sk(Γ)`. -/
theorem exists_sk_radial (rad : RadialDrawing cap Γ) (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) : ∃ G₃, PreRad (PaintingOrDrawing.drawing D) G₃ ∧
      RadMax (PaintingOrDrawing.drawing D) G₃ := by
  obtain ⟨D', G₃, hD', hpre, hmax, -, -⟩ := rad.exists_full hS (h3.hatRegions_isOpenDisc hS cap)
    h3.1
  obtain rfl : D = D' := drawing_eq (hD.hU.trans hD'.hU.symm) (hD.hV.trans hD'.hV.symm)
  exact ⟨G₃, hpre, hmax⟩

variable [ConnectedSpace Shat]

/-- **Graph Minors XIX, (6.7), first statement**: `sk(Γ)` is a block. -/
theorem sk_block (rad : RadialDrawing cap Γ) (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) : D.IsBlock := by
  obtain ⟨G₃, hpre, hmax⟩ := exists_sk_radial rad hS hD h3
  exact sk_isBlock hS hD h3 (sk_loopFree hS hD) hpre hmax

omit [T2Space S] [T2Space Shat] in
omit [ConnectedSpace Shat] in
/-- An `O`-arc off `sk(Γ)` lies in an open disc, so it is null-homotopic. -/
theorem null_of_disjoint (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) {F : Set Shat} (hF : IsOArc F) (hFU : Disjoint F D.U) :
    IsNullHomotopicOArc F := by
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace cap.isClosedSurface
  obtain ⟨φ⟩ := id hF
  have hFr : F = range fun z : Circle => (φ z).1 := by
    ext x
    constructor
    · intro hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
    · rintro ⟨z, rfl⟩
      exact (φ z).2
  have hFc : IsPreconnected F := by
    rw [hFr]
    exact isPreconnected_range (by fun_prop)
  have hy := (φ 1).2
  obtain ⟨ρ, hρ, hyρ⟩ := exists_region_of_notMem (disjoint_left.mp hFU hy)
  have hsub := subset_region hρ hFc hFU hy hyρ
  obtain ⟨x, hx, H, -, h0, h1⟩ := (sk_region_disc hS hD h3 hρ).isSimplyConnectedSet.2
    ⟨fun z => (φ z).1, by fun_prop⟩ (by
      rintro _ ⟨z, rfl⟩
      exact hsub (φ z).2)
  exact ⟨φ, x, mem_univ _, H, fun _ => mem_univ _, h0, h1⟩

omit [ConnectedSpace Shat] in
/-- If `sk(Γ)` is one edge with its ends, each `O`-arc is null-homotopic. A disc holds the edge off
its
boundary, and we reroute the `O`-arc along that boundary, off `sk(Γ)`. -/
theorem null_of_single_edge (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) {e : Set Shat} (he : D.U = closure e) (heE : e ∈ D.E)
    {F : Set Shat} (hF : IsOArc F) : IsNullHomotopicOArc F := by
  classical
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  by_contra hnn
  obtain ⟨u, v, huv, -, hL, -⟩ := exists_end D (sk_loopFree hS hD) heE
  obtain ⟨D₀, -, -, hD₀, hLD, -, -, -, -, -⟩ := exists_edge_lens hT hL huv isClosed_empty (by simp)
  obtain ⟨Δ, hΔ, hsub, -⟩ := Surface.exists_disc_around hman hD₀ (fun x _ => hT.2.2 x)
    isOpen_univ (subset_univ _)
  have hBU : Disjoint (discBd Δ) D.U := by
    rw [he]
    exact disjoint_left.mpr fun x hx hxL => (hsub (hLD hxL)).2 hx
  have hUΔ : D.U ⊆ Δ := by
    rw [he]
    exact fun x hx => (hsub (hLD hx)).1
  by_cases hm : (F ∩ Δ).Nonempty
  · have hex : ∀ a b : Shat, ∃ P : Set Shat, a ∈ discBd Δ → b ∈ discBd Δ →
        P ⊆ discBd Δ ∧ (a ≠ b → IsLineWithEnds P a b) ∧ (a = b → P = {a}) := by
      intro a b
      by_cases hab : a = b
      · exact ⟨{a}, fun ha _ => ⟨singleton_subset_iff.mpr ha, fun h => absurd hab h, fun _ => rfl⟩⟩
      by_cases h : a ∈ discBd Δ ∧ b ∈ discBd Δ
      · obtain ⟨A, B, hA, -, hU, -⟩ := hΔ.isOArc_discBd.lines h.1 h.2 hab
        exact ⟨A, fun _ _ => ⟨hU ▸ subset_union_left, fun _ => hA, fun h' => absurd h' hab⟩⟩
      · exact ⟨∅, fun ha hb => absurd ⟨ha, hb⟩ h⟩
    choose P hP using hex
    obtain ⟨C, a, b, hC, hCn, ha, hb, -, hCs⟩ := exists_reroute hT hΔ hF hnn hm P fun a ha b hb =>
      ⟨(hP a b ha hb).1.trans (Surface.discBd_subset _), (hP a b ha hb).2⟩
    refine hCn (null_of_disjoint hS hD h3 hC (disjoint_left.mpr fun x hx hxU => ?_))
    rcases hCs hx with h | h
    · exact h.2 (hUΔ hxU)
    · exact disjoint_left.mp hBU ((hP a b ha.2 hb.2).1 h) hxU
  · refine hnn (null_of_disjoint hS hD h3 hF (disjoint_left.mpr fun x hx hxU => ?_))
    exact hm ⟨x, hx, hUΔ hxU⟩

omit [T2Space Shat] [ConnectedSpace Shat] in
/-- Each vertex of a block lies on two edges, unless the block is one edge with its ends. -/
theorem two_edges_or_single {G : Drawing Shat} (hl : LoopFree G) (hb : G.IsBlock)
    (hE : G.E.Nonempty) : (∀ v ∈ G.V, ∃ e₁ ∈ G.E, ∃ e₂ ∈ G.E, e₁ ≠ e₂ ∧ v ∈ tilde e₁
      ∧ v ∈ tilde e₂) ∨
      ∃ e ∈ G.E, G.U = closure e := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨⟨v, hv, hnot⟩, hsingle⟩ := hno
  have hconn := (preconnected_iff_connIn G _).mp hb.connected
  have hcut : ∀ w ∈ G.V, ConnIn G (G.V \ {w}) := fun w hw =>
    (preconnected_iff_connIn G _).mp (hb.biconnected w hw)
  obtain ⟨e₀, he₀⟩ := hE
  have hend : ∀ e ∈ G.E, tilde e ⊆ G.V := fun e he x hx => by
    rw [tilde_eq_inter_V G he] at hx
    exact hx.2
  obtain ⟨p, q, hpq, htp, -⟩ := hl e₀ he₀
  have hne₂ : ∃ c ∈ G.V, c ≠ v := by
    by_cases hp : p = v
    · exact ⟨q, hend _ he₀ (htp ▸ .inr rfl), fun h => hpq (hp.trans h.symm)⟩
    · exact ⟨p, hend _ he₀ (htp ▸ .inl rfl), hp⟩
  obtain ⟨c, hc, hcv⟩ := hne₂
  obtain ⟨b, hbadj⟩ : ∃ b, G.adj.Adj v b := by
    by_contra hn
    push Not at hn
    have := hconn {v} (singleton_subset_iff.mpr hv) (singleton_nonempty v) fun a ha b _ hab => by
      rw [mem_singleton_iff.mp ha] at hab
      exact absurd hab (hn b)
    have hc' : c ∈ ({v} : Set Shat) := this ▸ hc
    exact hcv hc'
  obtain ⟨hvb, -, hbV, e₁, he₁, hv₁, hb₁⟩ := id hbadj
  obtain ⟨u₁, w₁, huw, ht₁, -⟩ := hl e₁ he₁
  have htv : tilde e₁ = {v, b} := by
    refine (eq_of_subset_of_ncard_le (s := {v, b}) ?_ ?_ (by rw [ht₁]; exact toFinite _)).symm
    · rintro y (rfl | rfl)
      · exact hv₁
      · exact hb₁
    · rw [ht₁, ncard_pair huw, ncard_pair hvb]
  have hall : ∀ e ∈ G.E, v ∈ tilde e → e = e₁ := fun e he hve => by
    by_contra hne
    obtain ⟨e', he', hne', hv'⟩ := hnot e₁ he₁ e he (Ne.symm hne) hv₁ |> fun h =>
      (⟨e, he, hne, hve, h⟩ : ∃ e' ∈ G.E, e' ≠ e₁ ∧ v ∈ tilde e' ∧ v ∉ tilde e)
    exact hv'.2 hve
  have hVsub : G.V ⊆ {v, b} := by
    have hY := (hcut b hbV) {v} (singleton_subset_iff.mpr ⟨hv, hvb⟩) (singleton_nonempty v)
      fun a ha y hy hay => by
        rw [mem_singleton_iff.mp ha] at hay
        obtain ⟨hne, -, -, e₂, he₂, hv₂, hy₂⟩ := hay
        rw [hall e₂ he₂ hv₂, htv] at hy₂
        rcases hy₂ with h | h
        · exact absurd h.symm hne
        · exact absurd h hy.2
    intro y hy
    by_cases hyb : y = b
    · exact .inr hyb
    · have : y ∈ ({v} : Set Shat) := hY ▸ ⟨hy, hyb⟩
      exact .inl this
  refine hsingle e₁ he₁ (Subset.antisymm (fun x hx => ?_) (G.closure_subset_U he₁))
  by_cases hxV : x ∈ G.V
  · have : x ∈ tilde e₁ := by
      rw [htv]
      exact hVsub hxV
    exact this.1
  · obtain ⟨e, he, hxe⟩ := exists_edge_of_mem G hx hxV
    obtain ⟨u₂, w₂, huw₂, ht₂, -⟩ := hl e he
    have h₁ : u₂ ∈ tilde e := ht₂ ▸ .inl rfl
    have h₂ : w₂ ∈ tilde e := ht₂ ▸ .inr rfl
    have hve : v ∈ tilde e := by
      rcases hVsub (hend e he h₁) with h | h
      · exact h ▸ h₁
      · rcases hVsub (hend e he h₂) with h' | h'
        · exact h' ▸ h₂
        · exact absurd (h.trans h'.symm) huw₂
    exact subset_closure (hall e he hve ▸ hxe)

/-- `rep(Γ) ≤ rep(sk(Γ))`. -/
theorem rep_le_sk' (rad : RadialDrawing cap Γ) (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) : Painting.rep rad ≤ D.rep := by
  classical
  have hl := sk_loopFree hS hD
  obtain ⟨γ, hγ⟩ := exists_edgePar D
  rcases two_edges_or_single hl (sk_block rad hS hD h3) (hD.E_nonempty hS h3.1) with hall | ⟨e, he,
    hU⟩
  · refine rep_le_sk rad hS hD h3 hγ fun v hv => ?_
    obtain ⟨e₁, he₁, e₂, he₂, hne, hv₁, hv₂⟩ := hall v hv
    have hcl : ∀ {e}, e ∈ D.E → v ∈ tilde e → v ∈ closure e := fun he h => by
      rw [tilde_eq_inter_V D he] at h
      exact h.1
    obtain ⟨b₁, hb₁⟩ := exists_end_eq hγ he₁ hv (hcl he₁ hv₁)
    obtain ⟨b₂, hb₂⟩ := exists_end_eq hγ he₂ hv (hcl he₂ hv₂)
    have hfin : Finite (halfEdges D γ v) := (finite_halfEdges D γ v).to_subtype
    have hnt : Nontrivial (halfEdges D γ v) :=
      ⟨⟨(e₁, b₁), he₁, hb₁⟩, ⟨(e₂, b₂), he₂, hb₂⟩, fun h => hne (congrArg (fun x => x.1.1) h)⟩
    exact Finite.one_lt_card_iff_nontrivial.mpr hnt
  · refine le_sInf ?_
    rintro _ ⟨F, hF, -, hnn, -⟩
    exact absurd (null_of_single_edge hS hD h3 hU he hF) hnn

omit [ConnectedSpace Shat] in
omit [T2Space S] in
/-- `rep(sk(Γ)) ≤ rep(Γ)`: a circuit of `Γ*` is an `sk(Γ)`-normal `O`-arc. -/
theorem sk_le_rep (rad : RadialDrawing cap Γ) (_hS : IsSurface S) (hD : IsSkHat cap Γ D) :
    D.rep ≤ Painting.rep rad := by
  have hVhat : D.V = Γ.hatV cap := hD.hV
  have hUhat : D.U ⊆ Γ.hatU cap := by
    rw [hD.hU]
    exact image_mono Γ.skU_subset
  have hb : ∀ e x y, rad.G.toGraph.IsLink e x y → (x ∈ D.V ↔ y ∉ D.V) := by
    intro e x y hl
    obtain ⟨v, hv, w, hw, hcap⟩ := rad.edge_ends hl.1
    have heq : ({x, y} : Set Shat) = {cap.emb v, w} := hl.2.2.2.symm.trans hcap
    have hx : x ∈ ({cap.emb v, w} : Set Shat) := heq ▸ mem_insert x _
    have hy : y ∈ ({cap.emb v, w} : Set Shat) := heq ▸ mem_insert_of_mem x rfl
    have hvD : cap.emb v ∈ D.V := by
      rw [hD.hV]
      exact mem_image_of_mem _ hv
    have hwD : w ∉ D.V := fun h => hw.2 (hVhat ▸ h)
    have hw' : w ∈ ({x, y} : Set Shat) := heq ▸ .inr rfl
    have hv' : cap.emb v ∈ ({x, y} : Set Shat) := heq ▸ .inl rfl
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exfalso
      rcases hw' with h | h
      · exact hwD (h.trans hx ▸ hvD)
      · exact hwD (h.trans hy ▸ hvD)
    · rw [hx, hy]
      exact ⟨fun _ => hwD, fun _ => hvD⟩
    · rw [hx, hy]
      exact ⟨fun h => absurd h hwD, fun h => absurd hvD h⟩
    · exfalso
      rcases hv' with h | h
      · exact hwD ((h.trans hx) ▸ hvD)
      · exact hwD ((h.trans hy) ▸ hvD)
  refine le_sInf ?_
  rintro _ ⟨C, ⟨hCs, hC⟩, hnn, rfl⟩
  have hN : D.IsNormal C.U := fun x hx => by
    have : x ∈ Γ.hatU cap ∩ rad.G.U := ⟨hUhat hx.2, hCs.U_subset hx.1⟩
    rw [rad.isPreRadial.1] at this
    exact hVhat ▸ this
  have h₁ : D.rep ≤ ((C.U ∩ D.V).ncard : ℕ∞) :=
    sInf_le ⟨C.U, IsCircuit.isOArc_U hC, hN, hnn, rfl⟩
  refine h₁.trans ?_
  have hsub : C.U ∩ D.V ⊆ D.V ∩ C.V := by
    rintro x ⟨hxC, hxV⟩
    refine ⟨hxV, ?_⟩
    by_contra hn
    obtain ⟨e, he, hxe⟩ := C.exists_edge_of_mem hxC hn
    exact ((hCs.2 he).2.1 hxe).2 (rad.isPreRadial.2.1 (hVhat ▸ hxV))
  have h₂ := two_mul_ncard_le_length D.V hb hC hCs
  have h₃ := ncard_le_ncard hsub (C.finite_V.subset inter_subset_right)
  have h₄ : (C.U ∩ D.V).ncard ≤ C.E.ncard / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : C.length = C.E.ncard := rfl
    omega
  exact_mod_cast h₄

/-- **Graph Minors XIX, (6.7)** (page 342): if `Γ` is an internally 3-connected painting in a
surface
`Σ`, then `sk(Γ)` is a block and `rep(sk(Γ)) = rep(Γ)`. -/
theorem theorem_6_7_proof (rad : RadialDrawing cap Γ) (hS : IsSurface S) (hD : IsSkHat cap Γ D)
    (h3 : Γ.IsInternallyThreeConnected) : D.IsBlock ∧ D.rep = Painting.rep rad :=
  ⟨sk_block rad hS hD h3, le_antisymm (sk_le_rep rad hS hD) (rep_le_sk' rad hS hD h3)⟩

end GraphMinor.GM19
