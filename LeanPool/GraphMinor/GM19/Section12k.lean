/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12j

/-!
# Graph Minors XIX, Section 12: steps (1)-(4) of (12.4)

Here `W` is the wheel around a centre, from `IsCentre.exists_wheel`, and the structure
`IsCentredWheel` records it. The
results are the steps (1), (2), (3) and (4) of the proof of (12.4). The paper keeps the maximal
wheels and says that it can
prove more: the wheels of the different centres are disjoint. This is what we prove, in
`IsCentredWheel.disjoint`, since it
is shorter.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

/-- The wheel `W` around a centre, with what the construction of (12.1) gives. -/
structure IsCentredWheel (D : TangleDatum cap χ) (t : ℕ) (x y : Shat) (C H : Drawing Shat)
  (A B W : Set Shat) (k : ℕ) :
    Prop where
  centre : IsCentre D t x y C H A B
  k_eq : k + 3 = 2 * t
  hub : D.IsWheelHubOfRadius W H (2 * t)
  zone : nearZone D H k ∪ (A ∪ B) ⊆ W \ discBd W
  far : ∀ p ∈ W, ∃ a ∈ D.P.Γ.atoms cap, p ∈ a ∧ D.dist (D.rad.atomOf x) a ≤ 11 * t + 13

namespace IsCentredWheel

variable {D : TangleDatum cap χ} {t k : ℕ} {x y : Shat} {C H : Drawing Shat} {A B W : Set Shat}
variable (h : IsCentredWheel D t x y C H A B W k)
include h

/-- Step (1): `x` lies inside the wheel. -/
theorem x_mem : x ∈ W \ discBd W := by
  rcases h.centre.x_cases with hx | ⟨-, rfl⟩
  · exact h.zone (.inr (.inl hx.1))
  · rcases h.centre.y_cases with hy | ⟨-, hy⟩
    · exact h.zone (.inr (.inr hy.1))
    · exact h.zone (.inl (subset_nearZone h.centre.hsub (H.V_subset_U hy)))

omit [T2Space S] in
/-- Step (1): the neighbours of `x` lie inside the wheel. -/
theorem nbr_mem {g : Set Shat} {n : Shat} (hl : D.rad.G.toGraph.IsLink g x n) : n ∈ W \ discBd W
  := by
  have ht := h.centre.four_le
  have hk := h.k_eq
  have hx₁ : x ∈ closure g ∩ D.rad.G.V := by
    rw [hl.2.2.2]
    exact .inl rfl
  have hn₁ : n ∈ closure g ∩ D.rad.G.V := by
    rw [hl.2.2.2]
    exact .inr rfl
  rcases h.centre.x_cases with hx | ⟨-, rfl⟩
  · have hgA := h.centre.patchC.edge_side_of_closure h.centre.rep₁ hl.1 hx hx₁.1
    exact h.zone (.inr (.inl (closure_minimal hgA (h.centre.patchC.closed h.centre.rep₁) hn₁.1)))
  · by_cases hnB : n ∈ B \ H.U
    · exact h.zone (.inr (.inr hnB.1))
    · have hlr : D.rad.G.toGraph.IsLink g n y := ⟨hl.1, hn₁.2, hx₁.2, by rw [hl.2.2.2, pair_comm]⟩
      have hN := h.centre.isNear_of_walk (.cons hlr (.nil hx₁.2)) hnB
      rw [GraphWalk.length_cons] at hN
      exact h.zone (.inl (IsCentre.mem_zone (k := k) hN (fun _ ↦ by change 0 + 1 ≤ k + 1; omega)
        (by change 0 + 1 ≤ k + 2; omega) (D.mem_atomOf hn₁.2)))

/-- Step (2): a vertex of `Γ` on the boundary of the wheel is close to `x`. -/
theorem dist_bd {v : Shat} (hv : v ∈ (cap.emb '' D.Γ.V) ∩ discBd W) :
    D.dist (D.rad.atomOf x) (D.rad.atomOf v) ≤ 7 * t + 2 := by
  have ht := h.centre.four_le
  have hre := h.centre.rep_ge
  have hr := h.centre.rep₀
  obtain ⟨⟨P, z, hz, hP, hle⟩, -⟩ := h.hub.bd_dist v hv
  obtain ⟨K, hK⟩ := GraphMinor.GM19.Drawing.IsPathOf.exists_walk hP
  have d₃ := D.dist_atomOf_le_of_walk K (by omega)
  rw [D.dist_comm] at d₃
  have d₁ := h.centre.dist_x_y
  have d₂ := h.centre.dist_h_y hz
  rw [D.dist_comm] at d₂
  have t₁ := D.dist_triangle hr (a := D.rad.atomOf x) (c := D.rad.atomOf v)
    (D.atomOf_mem h.centre.y_G)
  have t₂ := D.dist_triangle hr (a := D.rad.atomOf y) (c := D.rad.atomOf v) (D.atomOf_mem
    (h.centre.hsub.1 hz))
  omega

/-- A point of the boundary of the wheel lies in an atom close to `x`. -/
theorem exists_atom_bd {p : Shat} (hp : p ∈ discBd W) : ∃ a ∈ D.P.Γ.atoms cap, p ∈ a ∧
    D.dist (D.rad.atomOf x) a ≤ 7 * t + 3 := by
  have ht := h.centre.four_le
  have hre := h.centre.rep_ge
  have hr := h.centre.rep₀
  obtain ⟨v, hv, w, hpw, hwG, hcases⟩ := h.hub.exists_atom_on_bd hp
  refine ⟨D.rad.atomOf w, D.atomOf_mem hwG, hpw, ?_⟩
  have d := h.dist_bd hv
  rcases hcases with rfl | ⟨g, hl⟩
  · omega
  · have d₁ : D.dist (D.rad.atomOf v) (D.rad.atomOf w) ≤ 1 :=
      D.dist_atomOf_le_of_walk (.cons hl (.nil hwG)) (by
        rw [GraphWalk.length_cons]
        change 0 + 1 < D.rep
        omega)
    have t₁ := D.dist_triangle hr (a := D.rad.atomOf x) (c := D.rad.atomOf w) (D.atomOf_mem hl.2.1)
    omega

/-- Step (3): the boundary of the wheel avoids the capped part of `Σ̂` and `bd(Σ)`. -/
theorem bd_in_interior (hsep : ∀ p ∈ D.rad.poles, p ≠ x → 24 * t < D.vDist x p) :
    discBd W ⊆ cap.emb '' (univ \ bd S) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3c := D.P.fits.internally_three_connected
  have ht := h.centre.four_le
  have hre := h.centre.rep_ge
  have hr := h.centre.rep₀
  intro p hp
  by_contra hpn
  obtain ⟨v, hv, w, hpw, hwG, hcases⟩ := h.hub.exists_atom_on_bd hp
  -- a pole next to a vertex on the boundary is impossible
  have hno : ∀ {r v' : Shat} {g : Set Shat}, r ∈ D.rad.poles → v' ∈ (cap.emb '' D.Γ.V) ∩ discBd W →
      D.rad.G.toGraph.IsLink g v' r → False := by
    intro r v' g hrp hv' hl
    by_cases hrx : r = x
    · subst hrx
      have hl' : D.rad.G.toGraph.IsLink g r v' := ⟨hl.1, hl.2.2.1, hl.2.1, by rw [hl.2.2.2,
        pair_comm]⟩
      exact (h.nbr_mem hl').2 hv'.2
    · have hs := hsep r hrp (Ne.symm (Ne.symm hrx))
      change 24 * t < D.dist _ _ at hs
      have d := h.dist_bd hv'
      have d₁ : D.dist (D.rad.atomOf v') (D.rad.atomOf r) ≤ 1 :=
        D.dist_atomOf_le_of_walk (.cons hl (.nil hl.2.2.1)) (by
          rw [GraphWalk.length_cons]
          change 0 + 1 < D.rep
          omega)
      have t₁ := D.dist_triangle hr (a := D.rad.atomOf x) (c := D.rad.atomOf r)
        (D.atomOf_mem hl.2.1)
      omega
  by_cases hw : w ∈ D.P.Γ.hatV cap
  · -- `p = w` is a vertex of `Γ`, on `bd(Σ)`
    obtain ⟨a, haV, rfl⟩ := hw
    rw [D.atomOf_emb haV] at hpw
    obtain rfl : p = _ := hpw
    have hab : a ∈ bd S := by
      by_contra hn
      exact hpn ⟨a, ⟨mem_univ _, hn⟩, rfl⟩
    obtain ⟨Θ, hΘ, haΘ⟩ := mem_sUnion.mp ((sUnion_cuffs (S := S)).symm ▸ hab : a ∈ ⋃₀ cuffs S)
    obtain ⟨r, hrp, -, hreg⟩ := D.rad.exists_pole hΘ
    obtain ⟨g, hg, hcap⟩ := D.rad.exists_pole_edge hS h3c hrp hΘ hreg haV haΘ
    exact hno hrp ⟨mem_image_of_mem _ haV, hp⟩ ⟨hg, hwG, hrp.1.1, hcap⟩
  · -- `p` lies in a region of `Γ` that is not in `Σ`
    have hwR : w ∈ D.rad.Rstar := ⟨hwG, hw⟩
    rw [atomOf_Rstar D hwR] at hpw
    have hpU : p ∉ D.P.Γ.hatU cap := by
      have := (connectedComponentIn_subset _ _ hpw : p ∈ _)
      exact this
    have hpr : p ∉ range cap.emb := by
      rintro ⟨a, rfl⟩
      exact hpn ⟨a, ⟨mem_univ _, fun hb ↦ hpU (mem_image_of_mem _ (D.P.Γ.bd_subset hb))⟩, rfl⟩
    have hwp : w ∈ D.rad.poles := ⟨hwR, fun hsub ↦ hpr (hsub hpw)⟩
    rcases hcases with rfl | ⟨g, hl⟩
    · exact hw hv.1
    · exact hno hwp hv hl

/-- The last condition of a cover: the wheel has a vertex of `Γ` inside. -/
theorem interior_vertex : ((W \ discBd W) ∩ (cap.emb '' D.Γ.V)).Nonempty := by
  classical
  have ht := h.centre.four_le
  have hk := h.k_eq
  obtain ⟨p, -, -, hp, -⟩ := h.hub.is_disc.isOArc_discBd.exists_three
  obtain ⟨v, hv, -⟩ := h.hub.exists_atom_on_bd hp
  obtain ⟨⟨P, z, hz, hP, -⟩, -⟩ := h.hub.bd_dist v hv
  obtain ⟨K, -⟩ := GraphMinor.GM19.Drawing.IsPathOf.exists_walk hP
  have hzW := h.hub.H_in_int (H.V_subset_U hz)
  by_cases hzh : z ∈ D.P.Γ.hatV cap
  · exact ⟨z, hzW, hzh⟩
  have hne : z ≠ v := fun e ↦ hzW.2 (e ▸ hv.2)
  obtain ⟨T, -⟩ : ∃ T : GraphWalk D.rad.G.toGraph z v, T = K.reverse := ⟨_, rfl⟩
  cases T with
  | nil _ => exact absurd rfl hne
  | @cons _ n _ g hl r =>
    have hnh := hatV_of_not_hatV D hl.1 hl.2.2.2 hzh
    have hlr : D.rad.G.toGraph.IsLink g n z := ⟨hl.1, hl.2.2.1, hl.2.1, by rw [hl.2.2.2, pair_comm]⟩
    have hN : D.IsNear H (0 + 1) n := (isNear_self h.centre.hsub hz).step hlr
    exact ⟨n, h.zone (.inl (IsCentre.mem_zone (k := k) hN (fun _ ↦ by omega) (by omega)
      (D.mem_atomOf hl.2.2.1))), hnh⟩

end IsCentredWheel

omit [T2Space S] in
/-- A connected set that misses a short circuit lies inside it or misses its inside. -/
theorem side_of_ins (D : TangleDatum cap χ) {F : Drawing Shat} (hF : Drawing.IsCircuitOf F D.rad.G)
    (hlt : F.E.ncard < 2 * D.rep) {X : Set Shat} (hX : IsPreconnected X) (hdis : Disjoint X F.U) :
    X ⊆ D.ins F \ F.U ∨ Disjoint X (D.ins F) := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hs := D.ins_spec hF hlt
  have hbd : discBd (D.ins F) = F.U := hs.2.2.2.1
  rw [← hbd] at hdis ⊢
  exact hs.2.2.1.side hman hX hdis

namespace IsCentredWheel

variable {D : TangleDatum cap χ} {t k k' : ℕ} {x y x' y' : Shat} {C H C' H' : Drawing Shat} {A B W
  A' B' W' : Set Shat}

/-- The boundary of a wheel misses the wheel of another centre. -/
theorem disjoint_bd (h : IsCentredWheel D t x y C H A B W k) (h' : IsCentredWheel D t x' y' C' H'
  A' B' W' k')
    (hlt : 24 * t < D.vDist x x') : Disjoint (discBd W) W' := by
  have ht := h.centre.four_le
  have hr := h.centre.rep₀
  rw [disjoint_left]
  intro p hp hp'
  obtain ⟨a, ha, hpa, hd⟩ := h.exists_atom_bd hp
  obtain ⟨a', ha', hpa', hd'⟩ := h'.far p hp'
  obtain rfl := D.atom_eq_of_mem ha ha' hpa hpa'
  have t₁ := D.dist_triangle hr (a := D.rad.atomOf x) (c := D.rad.atomOf x') ha
  rw [D.dist_comm a] at t₁
  change 24 * t < D.dist _ _ at hlt
  omega

/-- The wheels of different centres are disjoint. -/
theorem disjoint (h : IsCentredWheel D t x y C H A B W k) (h' : IsCentredWheel D t x' y' C' H' A'
  B' W' k')
    (hlt : 24 * t < D.vDist x x') : Disjoint W W' := by
  have hT := cap.isClosedSurface
  have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
  have hlt' : 24 * t < D.vDist x' x := by
    change 24 * t < D.dist _ _ at hlt ⊢
    rwa [D.dist_comm]
  have hd := h'.hub.is_disc
  have hc : IsPreconnected W' := hd.isPreconnected_discInt.subset_closure sdiff_subset
    hd.subset_closure_discInt
  rcases h.hub.is_disc.side hman hc (h.disjoint_bd h' hlt).symm with hsub | hdis
  · exfalso
    obtain ⟨q, -, -, hq, -⟩ := hd.isOArc_discBd.exists_three
    exact disjoint_left.mp (h'.disjoint_bd h hlt') hq (hsub (Surface.discBd_subset _ hq)).1
  · exact hdis.symm

/-- Step (4): an edge of `Γ` within `t` of `x` lies in the wheel. The hypothesis says that `A` is
maximal. -/
theorem edge_subset (h : IsCentredWheel D t x y C H A B W k)
    (hmax : ∀ F : Drawing Shat, Drawing.IsCircuitOf F D.rad.G → F.E.ncard ≤ 2 * t
      → x ∈ D.ins F \ F.U →
      ¬ A ⊆ D.ins F \ F.U) {e : Set S} (he : e ∈ D.P.Γ.E) (hde : D.edgeVertDist e x
        ≤ t) : cap.emb '' e ⊆ W := by
  classical
  have : ConnectedSpace Shat := cap.connected
  have ht := h.centre.four_le
  have hre := h.centre.rep_ge
  have hr := h.centre.rep₀
  have hxG := h.centre.x_mem
  have hoff : Disjoint (cap.emb '' e) D.rad.G.U := disc_edge_disjoint D.rad ⟨subset_rfl,
    subset_rfl⟩ he
  have hne : cap.emb '' e ≠ D.rad.atomOf x := fun heq ↦ by
    have hx : x ∈ cap.emb '' e := heq ▸ D.mem_atomOf hxG
    exact disjoint_left.mp hoff hx (D.rad.G.V_subset_U hxG)
  obtain ⟨T, ha, hb, hT⟩ := D.exists_of_dist_lt hne (lt_of_le_of_lt hde (by omega))
  rw [D.ins_eq_insWalk T] at ha hb
  have hlen := T.walk_len
  change D.dist _ _ ≤ t at hde
  set K := walkDrawing D.rad.G T.walk with hKdef
  have hKs : K.IsSubdrawing D.rad.G := walkDrawing_isSubdrawing _ _
  have hKV : ∀ {u}, u ∈ K.V → u ∈ T.walk.support := fun {u} hu ↦ by
    rw [hKdef, walkDrawing_V] at hu
    exact hu
  have hEle : ∀ {F : Drawing Shat}, F.IsSubdrawing K → F.E.ncard ≤ 2 * t := by
    intro F hF
    have hle : F.E.ncard ≤ T.walk.edges.length := by
      refine (ncard_le_ncard ?_ (T.walk.edges.finite_toSet)).trans (ncard_mem_list_le T.walk.edges)
      intro g hg
      have := hF.2 hg
      rwa [hKdef, walkDrawing_E] at this
    have : T.walk.length = T.walk.edges.length := rfl
    omega
  have hmemIns : ∀ {X : Set Shat}, (X ∩ insWalk D.ins D.rad.G T.walk).Nonempty → Disjoint X K.U →
      ∃ F : Drawing Shat, F.IsCircuit ∧ F.IsSubdrawing K ∧ (X ∩ D.ins F).Nonempty := by
    rintro X ⟨z, hzX, hz⟩ hdis
    rcases hz with hz | hz
    · exact absurd hz (disjoint_left.mp hdis hzX)
    · obtain ⟨F, ⟨hFc, hFs⟩, hzF⟩ := mem_iUnion₂.mp hz
      exact ⟨F, hFc, hFs, z, hzX, hzF⟩
  obtain ⟨F, hFc, hFs, hzF⟩ := hmemIns ha (hoff.mono_right hKs.U_subset)
  have hFG : Drawing.IsCircuitOf F D.rad.G := ⟨hFs.trans hKs, hFc⟩
  have hFl : F.E.ncard < 2 * D.rep := lt_of_le_of_lt (hEle hFs) (by omega)
  obtain ⟨q, hq, heq⟩ := D.exists_region_of_edge he
  have hqF : q ⊆ D.ins F := by
    rcases region_subset_or_disjoint (D.isSlope (by omega)) hFG.2 hFG.1 hFl hq with h' | h'
    · exact h'
    · obtain ⟨z, hz₁, hz₂⟩ := hzF
      exact absurd hz₂ (disjoint_left.mp h' (heq hz₁))
  refine heq.trans (hqF.trans ?_)
  by_cases hm : ∃ m, m ∈ K.V ∧ m ∈ C.V
  · obtain ⟨m, hmK, hmC⟩ := hm
    refine h.hub.ins_subset_of_vertices hFG (by have := hEle hFs; omega) fun u hu huh ↦ ?_
    have huK := hFs.1 hu
    obtain ⟨W₁, hW₁⟩ := exists_walk_on_closed_walk T.walk (hKV huK) (hKV hmK)
    obtain ⟨W₂, hW₂⟩ := h.centre.exists_walk_C hmC
    by_cases huB : u ∈ B \ H.U
    · exact (h.zone (.inr (.inr huB.1))).1
    have hN := h.centre.isNear_of_walk (W₁.append W₂) huB
    rw [GraphWalk.length_append] at hN
    have hN' : D.IsNear H (2 * t) u := hN.mono (by omega)
    exact h.hub.close_in_W u huh (isNear_iff_exists_path.mp hN')
  have hUdis : Disjoint K.U C.U := by
    rw [disjoint_left]
    intro p hpK hpC
    by_cases hpG : p ∈ D.rad.G.V
    · exact hm ⟨p, mem_V_of_mem_U hKs hpK hpG, mem_V_of_mem_U h.centre.patchC.1 hpC hpG⟩
    · obtain ⟨f, hf, hpf⟩ := K.exists_edge_of_mem hpK fun h' ↦ hpG (hKs.1 h')
      obtain ⟨f', hf', hpf'⟩ := C.exists_edge_of_mem hpC fun h' ↦ hpG (h.centre.patchC.1.1 h')
      obtain rfl := D.rad.G.edge_eq_of_mem (hKs.2 hf) (h.centre.patchC.1.2 hf') hpf hpf'
      obtain ⟨a, ha', w₀, hw₀, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 f (hKs.2 hf)
      have ham : a ∈ closure f ∩ D.rad.G.V := by
        rw [hcap]
        exact .inl rfl
      exact hm ⟨a, ((hKs.closure_inter_V hf).symm ▸ ham : a ∈ closure f ∩ K.V).2,
        ((h.centre.patchC.1.closure_inter_V hf').symm ▸ ham : a ∈ closure f ∩ C.V).2⟩
  by_cases hKA : (K.U ∩ A).Nonempty
  · -- `K` lies inside `C`
    obtain ⟨-, -, -, ⟨hC, hle, rfl⟩ | ⟨rfl, -⟩⟩ := id h.centre.patchC
    · have hClt : C.E.ncard < 2 * D.rep := lt_of_le_of_lt hle h.centre.rep₁
      have hsl := D.isSlope (by omega)
      rcases side_of_ins D hC hClt (isPreconnected_walkDrawing_U T.walk) hUdis with h' | h'
      · have hsub : D.ins F ⊆ D.ins C := hsl.monotone F C hFG.2 hFG.1 hFl hC.2 hC.1 hClt
          (hFs.U_subset.trans (h'.trans sdiff_subset))
        exact hsub.trans fun z hz ↦ (h.zone (.inr (.inl hz))).1
      · obtain ⟨z, hz₁, hz₂⟩ := hKA
        exact absurd hz₂ (disjoint_left.mp h' hz₁)
    · simp at hKA
  -- then `x` is inside a circuit of `K`, against the choice of `C`
  exfalso
  have hxK : x ∉ K.U := by
    rcases h.centre.x_cases with hx | ⟨-, rfl⟩
    · exact fun h' ↦ hKA ⟨x, h', hx.1⟩
    · exact fun h' ↦ hm ⟨_, mem_V_of_mem_U hKs h' hxG, h.centre.y_mem⟩
  have hatom : Disjoint (D.rad.atomOf x) K.U := by
    rw [disjoint_left]
    intro p hpa hpK
    by_cases hxh : x ∈ D.P.Γ.hatV cap
    · obtain ⟨v, hv, rfl⟩ := hxh
      rw [D.atomOf_emb hv] at hpa
      obtain rfl : p = _ := hpa
      exact hxK hpK
    have hxR : x ∈ D.rad.Rstar := ⟨hxG, hxh⟩
    rw [atomOf_Rstar D hxR] at hpa
    have hreg := D.rad.regionOf_mem hxR
    have huniq : ∀ {w}, w ∈ D.rad.regionOf x → w ∈ D.rad.G.V → w = x := fun hw hwG ↦
      (D.rad.isPreRadial.2.2.1 _ hreg.1).unique ⟨hw, hwG⟩ ⟨hreg.2, hxG⟩
    by_cases hpG : p ∈ D.rad.G.V
    · exact hxK (huniq hpa hpG ▸ hpK)
    obtain ⟨f, hf, hpf⟩ := K.exists_edge_of_mem hpK fun h' ↦ hpG (hKs.1 h')
    obtain ⟨a, -, w, hw, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 f (hKs.2 hf)
    have hwm : w ∈ closure f ∩ D.rad.G.V := by
      rw [hcap]
      exact .inr rfl
    have hpw := edge_subset_regionOf D hw (hKs.2 hf) hwm.1 hpf
    have heqr : D.rad.regionOf x = D.rad.regionOf w :=
      (connectedComponentIn_eq hpa).trans (connectedComponentIn_eq hpw).symm
    have hwx : w = x := huniq (heqr ▸ (D.rad.regionOf_mem hw).2) hw.1
    have hxf : x ∈ K.V := ((hKs.closure_inter_V hf).symm ▸ (hwx ▸ hwm : x ∈ closure f ∩ D.rad.G.V) :
      x ∈ closure f ∩ K.V).2
    exact hxK (K.V_subset_U hxf)
  obtain ⟨F', hF'c, hF's, hzF'⟩ := hmemIns hb hatom
  have hF'G : Drawing.IsCircuitOf F' D.rad.G := ⟨hF's.trans hKs, hF'c⟩
  have hF'l : F'.E.ncard < 2 * D.rep := lt_of_le_of_lt (hEle hF's) (by omega)
  have hatomc : IsPreconnected (D.rad.atomOf x) := by
    by_cases hx : x ∈ D.P.Γ.hatV cap
    · obtain ⟨v, hv, rfl⟩ := hx
      rw [D.atomOf_emb hv]
      exact isPreconnected_singleton
    · rw [atomOf_Rstar D ⟨hxG, hx⟩]
      exact isPreconnected_connectedComponentIn
  have hxF' : x ∈ D.ins F' \ F'.U := by
    rcases side_of_ins D hF'G hF'l hatomc (hatom.mono_right hF's.U_subset) with h' | h'
    · exact h' (D.mem_atomOf hxG)
    · obtain ⟨z, hz₁, hz₂⟩ := hzF'
      exact absurd hz₂ (disjoint_left.mp h' hz₁)
  refine hmax F' hF'G (hEle hF's) hxF' ?_
  by_cases hAe : A = ∅
  · rw [hAe]
    exact empty_subset _
  have hxA : x ∈ A := by
    rcases h.centre.x_cases with hx | ⟨h', -⟩
    · exact hx.1
    · exact absurd h' hAe
  have hAdis : Disjoint A F'.U := by
    rw [disjoint_left]
    exact fun z hz hzU ↦ hKA ⟨z, hF's.U_subset hzU, hz⟩
  rcases side_of_ins D hF'G hF'l (h.centre.patchC.isPreconnected h.centre.rep₁) hAdis with h' | h'
  · exact h'
  · exact absurd hxF'.1 (disjoint_left.mp h' hxA)

end IsCentredWheel

end TangleDatum

end GraphMinor.GM19
