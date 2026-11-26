/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section12b
public import LeanPool.GraphMinor.GM19.Section10n
public import LeanPool.GraphMinor.GM19.FragmentForm

/-!
# Graph Minors XIX, Section 12: vertices near a hub

The proof of (12.1) measures walks of `Γ*` from the hub `H`. We say that a vertex of `Γ*` is
`k`-near `H` if a walk of
`Γ*` of length at most `k` joins it to `V(H)`. This file proves how nearness passes across the
regions of `Γ*`.

A region `q` of `Γ*` holds one edge `e` of `Γ`. If `q` meets a region `r` of `Γ` with `r*` being
`k`-near, then the ends
of `e` should be `(k + 1)`-near. This holds if `|eTilde| = 2`. If `|eTilde| = 3`, then `r` touches
`e` along
one side of the disc
`ē`, so `rBar` holds only two of the three ends for free. The fifth condition in the definition of
"fits" helps here: if
`ē` misses `bd(Σ)`, then these two ends are the only vertices of `Γ` in `rBar`. So a shortest walk
reaches `r*` through
one of them, and the third end is a further two steps away. The result is
`TangleDatum.IsNear.of_corner`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [TopologicalSpace Shat] [T2Space Shat] in
/-- A walk contains a simple walk with the same ends that is no longer. -/
theorem _root_.GraphMinor.Surface.GraphWalk.exists_isSimple_length_le {β : Type*} {G : Graph Shat
  β} {u v : Shat}
    (W : GraphWalk G u v) : ∃ W' : GraphWalk G u v, W'.IsSimple ∧ W'.length ≤ W.length := by
  classical
  induction W with
  | nil h => exact ⟨.nil h, by simp [GraphWalk.IsSimple], le_rfl⟩
  | @cons u v w e h r ih =>
    obtain ⟨R, hR, hl⟩ := ih
    by_cases hu : u ∈ R.support
    · obtain ⟨R₁, R₂, rfl⟩ := R.exists_append_of_mem hu
      have hR₂ : R₂.IsSimple := by
        have hn : (R₁.support ++ R₂.support.tail).Nodup := by
          have h' : (R₁.append R₂).support.Nodup := hR
          rwa [GraphWalk.support_append] at h'
        have hd := List.nodup_append.mp hn
        unfold GraphWalk.IsSimple
        rw [R₂.support_eq_cons]
        exact List.nodup_cons.mpr ⟨fun hx => hd.2.2 u R₁.end_mem_support u hx rfl, hd.2.1⟩
      refine ⟨R₂, hR₂, ?_⟩
      rw [GraphWalk.length_append] at hl
      rw [GraphWalk.length_cons]
      omega
    · refine ⟨.cons h R, List.nodup_cons.mpr ⟨hu, hR⟩, ?_⟩
      simpa using hl

omit [T2Space S] in
/-- Two ends of a disc edge lie on one side of the disc: a component of `bd(cBar) \ cTilde`. -/
theorem Painting.exists_side_between (Γ : Painting S) {c : Set S} (hc : c ∈ Γ.E) (h3 :
  (tilde c).ncard = 3) {u v : S}
    (hu : u ∈ tilde c) (hv : v ∈ tilde c) (huv : u ≠ v) :
    ∃ f, Γ.IsSkEdgeIn f c ∧ u ∈ closure f ∧ v ∈ closure f := by
  classical
  obtain ⟨hdisc, hT, hfin⟩ := Γ.isDisc_of_three hc h3
  -- the third end
  obtain ⟨t, ht, htu, htv⟩ : ∃ t ∈ tilde c, t ≠ u ∧ t ≠ v := by
    by_contra hno
    push Not at hno
    have hsub : tilde c ⊆ {u, v} := fun t ht ↦ by
      by_cases h : t = u
      · exact .inl h
      · exact .inr (hno t ht h)
    have := ncard_le_ncard hsub (toFinite _)
    rw [h3, ncard_pair huv] at this
    omega
  have hall : ∀ y ∈ tilde c, y = u ∨ y = v ∨ y = t := fun y hy ↦ by
    by_contra hno
    push Not at hno
    have hsub : ({u, v, t, y} : Set S) ⊆ tilde c := by
      rintro z (rfl | rfl | rfl | rfl)
      exacts [hu, hv, ht, hy]
    have h4 : ({u, v, t, y} : Set S).ncard = 4 := by
      rw [ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_pair] <;> simp_all [Ne.symm]
    have := ncard_le_ncard hsub hfin
    omega
  have key : ∀ a : unitInterval → S, IsArcMap a → a 0 = u → a 1 = v → range a ⊆ discBd (closure c) →
      (∀ s, a s = t → s = 0 ∨ s = 1) → ∃ f, Γ.IsSkEdgeIn f c ∧ u ∈ closure f ∧ v ∈ closure f := by
    intro a ha h0 h1 hsub ht'
    let b : ℝ → S := fun s ↦ a (projIcc 0 1 zero_le_one s)
    have hb : Continuous b := ha.1.comp continuous_projIcc
    let A : Set S := b '' Ioo 0 1
    have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, projIcc 0 1 zero_le_one s ≠ 0 ∧ projIcc 0 1 zero_le_one s ≠ 1
      := by
      intro s hs
      rw [projIcc_of_mem zero_le_one ⟨hs.1.le, hs.2.le⟩]
      exact ⟨fun h ↦ hs.1.ne' (congrArg Subtype.val h), fun h ↦ hs.2.ne (congrArg Subtype.val h)⟩
    have hAc : IsPathConnected A :=
      ((convex_Ioo (0 : ℝ) 1).isPathConnected (nonempty_Ioo.mpr zero_lt_one)).image hb
    have hAb : ∀ x ∈ A, x ∈ discBd (closure c) ∧ x ∉ tilde c := by
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨h₀, h₁⟩ := hopen s hs
      refine ⟨hsub ⟨_, rfl⟩, fun hx ↦ ?_⟩
      rcases hall _ hx with h | h | h
      · exact h₀ (ha.2 (h.trans h0.symm))
      · exact h₁ (ha.2 (h.trans h1.symm))
      · rcases ht' _ h with h | h
        exacts [h₀ h, h₁ h]
    have hAsub : A ⊆ discBd (closure c) \ tilde c := fun x hx ↦ hAb x hx
    obtain ⟨f, hf, hAf⟩ := exists_arcComp_superset hAc hAsub
    refine ⟨f, ⟨hc, .inr ⟨h3, hf⟩⟩, ?_, ?_⟩
    · have : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
        rw [closure_Ioo zero_ne_one]
        simp
      have h := image_closure_subset_closure_image hb (mem_image_of_mem b this)
      have hb0 : b 0 = u := by
        simp only [b, projIcc_left]
        exact h0
      rw [hb0] at h
      exact closure_mono hAf h
    · have : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
        rw [closure_Ioo zero_ne_one]
        simp
      have h := image_closure_subset_closure_image hb (mem_image_of_mem b this)
      have hb1 : b 1 = v := by
        simp only [b, projIcc_right]
        exact h1
      rw [hb1] at h
      exact closure_mono hAf h
  obtain ⟨a, b, hab, ha0, ha1, hun⟩ := hdisc.isOArc_discBd.exists_arcs (hT hu) (hT hv) huv
  rcases hun.symm.subset (hT ht) with ⟨s, hs⟩ | ⟨s, hs⟩
  · -- `t` lies on `a`, so `b` is the side
    refine key b hab.arc_right (hab.zero.trans ha0) (hab.one.trans ha1) ?_ ?_
    · rw [← hun]
      exact subset_union_right
    · intro s' hs'
      rcases hab.meet s s' (hs.trans hs'.symm) with h | h
      · exact .inl h.2
      · exact .inr h.2
  · refine key a hab.arc_left ha0 ha1 ?_ ?_
    · rw [← hun]
      exact subset_union_left
    · intro s' hs'
      rcases hab.meet s' s (hs'.trans hs.symm) with h | h
      · exact .inl h.1
      · exact .inr h.1

omit [T2Space S] in
/-- A side of a disc edge lies on the boundary of a region of `Γ` outside the disc. -/
theorem IsSkHat.exists_hatRegion_side {Γ : Painting S} {Sk : Drawing Shat} (hSk : IsSkHat cap Γ Sk)
  (hS : IsSurface S)
    {f c : Set S} (hf : Γ.IsSkEdgeIn f c) (h3 : (tilde c).ncard = 3) :
    ∃ r ∈ Γ.hatRegions cap, cap.emb '' f ⊆ closure r := by
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hc := hf.1
  have hfE : cap.emb '' f ∈ Sk.E := hSk.edge_iff.mpr ⟨f, hf.mem, rfl⟩
  obtain ⟨p, hp⟩ := hf.mem.1
  have hpb : p ∈ discBd (closure c) := by
    rcases hf.2 with ⟨h2, -⟩ | ⟨-, h⟩
    · omega
    · exact (h.2.1 hp).1
  have hpc : p ∈ c := hf.subset hp
  obtain ⟨hdisc, -⟩ := Γ.isDisc_of_three hc h3
  obtain ⟨hC, hCbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
  have hfr : cap.emb p ∈ closure (cap.emb '' closure c)ᶜ := by
    have : cap.emb p ∈ frontier (cap.emb '' closure c) := by
      rw [IsClosedDisc.frontier_eq_discBd hT hC, hCbd]
      exact mem_image_of_mem _ hpb
    rw [frontier_eq_closure_inter_closure] at this
    exact this.2
  obtain ⟨r, hr, hpr, y, hyr, hyO⟩ := exists_region_near hT Sk hC.isClosed.isOpen_compl hfr
  have hinc : cap.emb '' f ⊆ closure r :=
    edge_subset_closure_of_incident hT hfE hr ⟨_, mem_image_of_mem _ hp, hpr⟩
  rcases hSk.region_cases hr with hhat | ⟨c', hc', -, hsub⟩
  · exact ⟨r, hhat, hinc⟩
  · exfalso
    have hcl : IsClosed (cap.emb '' closure c') := (cap.isClosedEmbedding hS).isClosedMap _
      isClosed_closure
    have hp' : cap.emb p ∈ cap.emb '' closure c' := closure_minimal hsub hcl hpr
    obtain ⟨p', hp', hpp⟩ := hp'
    obtain rfl := cap.isEmbedding.injective hpp
    have hpc' : p' ∈ c' := by
      rcases Γ.closure_subset hc' hp' with h | h
      · exact h
      · exact absurd h (Γ.disjoint_V hc hpc)
    obtain rfl := arcComp_eq_of_mem hc hc' hpc hpc'
    exact hyO (hsub hyr)

namespace TangleDatum

variable (D : TangleDatum cap χ)

/-- A vertex `x` of `Γ*` is `k`-near `H` if a walk of `Γ*` of length at most `k` joins it to `V(H)`.
-/
def IsNear (H : Drawing Shat) (k : ℕ) (x : Shat) : Prop :=
  ∃ h ∈ H.V, ∃ W : GraphWalk D.rad.G.toGraph x h, W.length ≤ k

variable {D} {H : Drawing Shat} {k l : ℕ} {x y : Shat}

omit [T2Space S] [T2Space Shat] in
theorem IsNear.mono (h : D.IsNear H k x) (hkl : k ≤ l) : D.IsNear H l x := by
  obtain ⟨h, hh, W, hW⟩ := h
  exact ⟨h, hh, W, hW.trans hkl⟩

omit [T2Space S] [T2Space Shat] in
theorem IsNear.step (h : D.IsNear H k x) {e : Set Shat} (hl : D.rad.G.toGraph.IsLink e y x) :
    D.IsNear H (k + 1) y := by
  obtain ⟨h, hh, W, hW⟩ := h
  exact ⟨h, hh, .cons hl W, by simpa using hW⟩

omit [T2Space S] [T2Space Shat] in
theorem IsNear.mem_V (h : D.IsNear H k x) : x ∈ D.rad.G.V := by
  obtain ⟨h, hh, W, -⟩ := h
  cases W with
  | nil h' => exact h'
  | cons hl _ => exact hl.2.1

omit [T2Space S] [T2Space Shat] in
/-- Each vertex of `H` is `0`-near `H`. -/
theorem isNear_self (hH : H.IsSubdrawing D.rad.G) (hx : x ∈ H.V) : D.IsNear H 0 x :=
  ⟨x, hx, .nil (hH.1 hx), le_of_eq rfl⟩

omit [T2Space S] in
/-- A path from a vertex to `V(H)` gives nearness, and conversely. -/
theorem isNear_iff_exists_path :
    D.IsNear H k x ↔ ∃ P : Drawing Shat, ∃ h ∈ H.V, P.IsPathOf D.rad.G x h ∧ P.E.ncard ≤ k := by
  classical
  constructor
  · rintro ⟨h, hh, W, hW⟩
    obtain ⟨W', hs, hle⟩ := W.exists_isSimple_length_le
    refine ⟨walkDrawing D.rad.G W', h, hh, ⟨walkDrawing_isSubdrawing _ _,
      walkDrawing_isPathBetween _ hs⟩, ?_⟩
    rw [ncard_walk_E _ hs]
    omega
  · rintro ⟨P, h, hh, hP, hle⟩
    obtain ⟨W, hW, -, hE⟩ := hP.2
    obtain ⟨W', hs, he⟩ := hP.1.exists_walk_up W
    refine ⟨h, hh, W', ?_⟩
    have h₁ := ncard_walk_E P hW
    rw [walkDrawing_E, ← hE] at h₁
    have h₂ : W'.length = W.length := by rw [← edges_length, ← edges_length, he]
    omega

omit [T2Space Shat] in
/-- The region of a vertex of `R*` is open. -/
theorem isOpen_regionOf (D : TangleDatum cap χ) {w : Shat} (hw : w ∈ D.rad.Rstar) : IsOpen
  (D.rad.regionOf w) := by
  have hT := cap.isClosedSurface
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨Sk, hSk⟩ := exists_isSkHat χ.isSurface cap D.P.Γ
  exact region_isOpen (hSk.hatRegion_mem_R (D.rad.regionOf_mem hw).1)

omit [T2Space Shat] in
/-- An edge of `Γ*` at `w ∈ R*` lies in the region of `w`. -/
theorem edge_subset_regionOf (D : TangleDatum cap χ) {w : Shat} (hw : w ∈ D.rad.Rstar) {g : Set
  Shat}
    (hg : g ∈ D.rad.G.E) (hwg : w ∈ closure g) : g ⊆ D.rad.regionOf w := by
  have hT := cap.isClosedSurface
  obtain ⟨Sk, hSk⟩ := exists_isSkHat χ.isSurface cap D.P.Γ
  have hR := hSk.hatRegion_mem_R (D.rad.regionOf_mem hw).1
  obtain ⟨y, hyr, hyg⟩ := mem_closure_iff.mp hwg _ (isOpen_regionOf D hw) (D.rad.regionOf_mem hw).2
  have hdis : Disjoint g Sk.U := by
    rw [disjoint_left]
    intro z hz hzU
    have h₁ : z ∈ D.P.Γ.hatU cap := by
      rw [hSk.hU] at hzU
      exact image_mono D.P.Γ.skU_subset hzU
    have h₂ : z ∈ D.rad.G.U := by
      rw [D.rad.G.U_eq]
      exact .inr (mem_iUnion₂.mpr ⟨g, hg, subset_closure hz⟩)
    have h₃ : z ∈ D.P.Γ.hatV cap := D.rad.isPreRadial.1 ▸ ⟨h₁, h₂⟩
    exact (hg.2.1 hz).2 (D.rad.isPreRadial.2.1 h₃)
  exact subset_region hR hg.2.2.1.isConnected.isPreconnected hdis hyg hyr

omit [T2Space Shat] in
/-- Crossing a region of `Γ` from its centre to a vertex on its boundary is one step of `Γ*`. -/
theorem IsNear.of_closure_region (h : D.IsNear H k x) (hx : x ∈ D.rad.Rstar) {v : S}
  (hv : v ∈ D.P.Γ.V)
    (hcl : cap.emb v ∈ closure (D.rad.regionOf x)) : D.IsNear H (k + 1) (cap.emb v) := by
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨e, he, hcap⟩ := D.rad.exists_spoke hS (h3.hatRegions_isOpenDisc hS cap) h3.1 hx hv hcl
  exact h.step ⟨he, D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv), hx.1, hcap⟩

omit [T2Space Shat] in
/-- From a vertex of `Γ` on the boundary of a region of `Γ`, one step of `Γ*` reaches the centre of
the region. -/
theorem IsNear.to_centre {v : S} (h : D.IsNear H k (cap.emb v)) (hv : v ∈ D.P.Γ.V) {r : Set Shat}
    (hr : r ∈ D.P.Γ.hatRegions cap) (hcl : cap.emb v ∈ closure r) :
    ∃ w ∈ D.rad.Rstar, D.rad.regionOf w = r ∧ D.IsNear H (k + 1) w := by
  have hS := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  obtain ⟨w, ⟨hwr, hwG⟩, -⟩ := D.rad.isPreRadial.2.2.1 r hr
  have hwV : w ∉ D.P.Γ.hatV cap := fun hV ↦ by
    obtain ⟨y, hy, rfl⟩ := id hr
    exact (connectedComponentIn_subset _ _ hwr) (image_mono D.P.Γ.V_subset hV)
  have hw : w ∈ D.rad.Rstar := ⟨hwG, hwV⟩
  have hreg : D.rad.regionOf w = r := by
    obtain ⟨y, hy, rfl⟩ := id hr
    exact (connectedComponentIn_eq hwr).symm
  refine ⟨w, hw, hreg, ?_⟩
  obtain ⟨e, he, hcap⟩ := D.rad.exists_spoke hS (h3.hatRegions_isOpenDisc hS cap) h3.1 hw hv
    (hreg ▸ hcl)
  have hcap' : closure e ∩ D.rad.G.V = {w, cap.emb v} := by rw [hcap, pair_comm]
  exact h.step ⟨he, hwG, D.rad.isPreRadial.2.1 (mem_image_of_mem _ hv), hcap'⟩

/-- Two ends of a disc edge are two steps apart in `Γ*`, through the region on the side between
them. -/
theorem IsNear.across_side {c : Set S} (hc : c ∈ D.P.Γ.E) (h3 : (tilde c).ncard = 3) {u v : S}
  (hu : u ∈ tilde c)
    (hv : v ∈ tilde c) (huv : u ≠ v) (h : D.IsNear H k (cap.emb u)) : D.IsNear H (k + 2)
      (cap.emb v) := by
  have hS := χ.isSurface
  have hemb : ∀ {x : S} {f : Set S}, x ∈ closure f → cap.emb x ∈ closure (cap.emb '' f) := fun hx ↦
    image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hx)
  obtain ⟨f, hf, huf, hvf⟩ := D.P.Γ.exists_side_between hc h3 hu hv huv
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  obtain ⟨r, hr, hfr⟩ := hSk.exists_hatRegion_side hS hf h3
  have hcl : closure (cap.emb '' f) ⊆ closure r := closure_minimal hfr isClosed_closure
  obtain ⟨w, hw, hreg, hnear⟩ := h.to_centre (D.P.Γ.tilde_subset_V hc hu) hr (hcl (hemb huf))
  exact hnear.of_closure_region hw (D.P.Γ.tilde_subset_V hc hv) (hreg ▸ hcl (hemb hvf))

omit [T2Space Shat] in
/-- The last step of a walk to `w ∈ R*`: either `w` is in `H`, or some vertex of `Γ` on the boundary
of the region of
`w` is one step nearer. -/
theorem IsNear.exists_prev (h : D.IsNear H (k + 1) x) (hx : x ∈ D.rad.Rstar) :
    x ∈ H.V ∨ ∃ v ∈ D.P.Γ.V, cap.emb v ∈ closure (D.rad.regionOf x) ∧ D.IsNear H k (cap.emb v) := by
  obtain ⟨h, hh, W, hW⟩ := h
  cases W with
  | nil _ => exact .inl hh
  | @cons _ u _ e hl r =>
    right
    rw [GraphWalk.length_cons] at hW
    obtain ⟨_, ⟨v', hv', rfl⟩, w, ⟨-, hw⟩, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e hl.1
    have hxe : x ∈ closure e ∩ D.rad.G.V := by
      rw [hl.2.2.2]
      exact .inl rfl
    have hue : u ∈ closure e ∩ D.rad.G.V := by
      rw [hl.2.2.2]
      exact .inr rfl
    have huV : u ∈ D.P.Γ.hatV cap := by
      rw [hcap] at hxe hue
      rcases hxe with rfl | rfl
      · exact absurd (mem_image_of_mem _ hv') hx.2
      · rcases hue with rfl | rfl
        · exact mem_image_of_mem _ hv'
        · exfalso
          have hvm : cap.emb v' ∈ closure e ∩ D.rad.G.V := by
            rw [hcap]
            exact .inl rfl
          rw [hl.2.2.2] at hvm
          rcases hvm with h' | h'
          · exact hx.2 (h' ▸ mem_image_of_mem _ hv')
          · exact hx.2 (h' ▸ mem_image_of_mem _ hv')
    obtain ⟨y, hy, rfl⟩ := huV
    refine ⟨y, hy, ?_, ⟨h, hh, r, by omega⟩⟩
    exact closure_mono (edge_subset_regionOf D hx hl.1 hxe.1) hue.1

omit [T2Space S] [T2Space Shat] in
/-- A region of `Γ` in `Σ̂` that lies in `Σ` is the image of a region of `Γ` in `Σ`. -/
theorem _root_.GraphMinor.GM19.Painting.exists_region_of_hat {Γ : Painting S} {r : Set Shat}
  (hr : r ∈ Γ.hatRegions cap)
    (hsub : r ⊆ range cap.emb) : ∃ r₀ ∈ Γ.regions, cap.emb '' r₀ = r := by
  obtain ⟨y, hy, rfl⟩ := id hr
  obtain ⟨x, rfl⟩ := hsub (mem_connectedComponentIn hy)
  have hxU : x ∈ Γ.Uᶜ := fun h ↦ hy (mem_image_of_mem _ h)
  refine ⟨connectedComponentIn Γ.Uᶜ x, ⟨x, hxU, rfl⟩, ?_⟩
  rw [image_connectedComponentIn_of_isEmbedding cap.isEmbedding hxU]
  apply subset_antisymm
  · exact connectedComponentIn_mono _ fun z ⟨z', hz', hzz⟩ ↦ fun ⟨u, hu, huz⟩ ↦
      hz' ((cap.isEmbedding.injective (huz.trans hzz.symm)) ▸ hu)
  · have hs : connectedComponentIn (Γ.hatU cap)ᶜ (cap.emb x) ⊆ cap.emb '' Γ.Uᶜ := fun z hz ↦ by
      obtain ⟨z', rfl⟩ := hsub hz
      exact ⟨z', fun h ↦ (connectedComponentIn_subset _ _ hz) (mem_image_of_mem _ h), rfl⟩
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hy) hs

omit [T2Space S] [T2Space Shat] in
/-- **The fifth condition.** Let `e` be an edge of size 3 whose closure misses `bd(Σ)`, and let `f`
be a side of `e` on
the boundary of the region `r` of `Γ`. If `v₁, v₂` are the two ends of `f`, then they are the only
vertices of `Γ`
in `rBar`. -/
theorem vertex_mem_of_side (D : TangleDatum cap χ) {e f : Set S} {r : Set Shat}
  (hf : D.P.Γ.IsSkEdgeIn f e)
    (h3 : (tilde e).ncard = 3) (hoff : closure e ∩ bd S = ∅) (hr : r ∈ D.P.Γ.hatRegions cap)
    (hfr : cap.emb '' f ⊆ closure r) {x y v : S} (hxy : x ≠ y) (hxf : x ∈ closure f)
      (hyf : y ∈ closure f)
    (hxV : x ∈ D.P.Γ.V) (hyV : y ∈ D.P.Γ.V) (hv : v ∈ D.P.Γ.V) (hvr : cap.emb v ∈ closure r) : v
      = x ∨ v = y := by
  classical
  have hS := χ.isSurface
  have hc := cap.isClosedEmbedding hS
  obtain ⟨p, hp⟩ := hf.mem.1
  have hpe := hf.subset hp
  have hpr : cap.emb p ∈ closure r := hfr (mem_image_of_mem _ hp)
  rcases hatRegion_cases cap D.P.Γ hr with hsub | ⟨Θ, hΘ, rfl⟩
  · obtain ⟨r₀, hr₀, rfl⟩ := Painting.exists_region_of_hat hr hsub
    have hcl : ∀ {z : S}, cap.emb z ∈ closure (cap.emb '' r₀) → z ∈ closure r₀ := fun {z} hz ↦ by
      rw [hc.closure_image_eq] at hz
      obtain ⟨z', hz', hzz⟩ := hz
      exact cap.isEmbedding.injective hzz ▸ hz'
    by_contra hne
    push Not at hne
    have hf₁ : closure f ⊆ closure e := closure_mono hf.subset
    have hcard : 3 ≤ (closure r₀ ∩ D.P.Γ.V).ncard := by
      have hsub' : ({x, y, v} : Set S) ⊆ closure r₀ ∩ D.P.Γ.V := by
        have hfcl : closure f ⊆ closure r₀ := closure_minimal
          (fun z hz ↦ hcl (hfr (mem_image_of_mem _ hz))) isClosed_closure
        rintro z (rfl | rfl | rfl)
        · exact ⟨hfcl hxf, hxV⟩
        · exact ⟨hfcl hyf, hyV⟩
        · exact ⟨hcl hvr, hv⟩
      have h₃ : ({x, y, v} : Set S).ncard = 3 := by
        rw [ncard_eq_three]
        exact ⟨x, y, v, hxy, hne.1.symm, hne.2.symm, rfl⟩
      rw [← h₃]
      exact ncard_le_ncard hsub' (D.P.Γ.finite_V.subset inter_subset_right)
    have hmem : p ∈ e ∩ closure r₀ := ⟨hpe, hcl hpr⟩
    obtain ⟨z, hz, hzb⟩ := D.P.fits.size_three_region e hf.1 h3 r₀ hr₀ hcard
      (connectedComponentIn (e ∩ closure r₀) p) ⟨p, hmem, rfl⟩
    have : z ∈ closure e := closure_mono ((connectedComponentIn_subset _ _).trans
      inter_subset_left) hz
    have hemp : z ∈ closure e ∩ bd S := ⟨this, hzb⟩
    rw [hoff] at hemp
    exact hemp.elim
  · exfalso
    have hpΘ : p ∈ Θ := cap.mem_of_emb_mem hΘ hpr
    have : p ∈ closure e ∩ bd S := ⟨subset_closure hpe, cuff_subset_bd ⟨Θ, hΘ⟩ hpΘ⟩
    rw [hoff] at this
    exact this.elim

/-- If a region `q` of `Γ*` with edge `e` of `Γ` meets a region `r` of `Γ`, then a side of `e` lies
on the boundary of `r`.
For `|eTilde| = 2` the side is `e` itself. -/
theorem exists_side_of_meet (D : TangleDatum cap χ) {q : Set Shat} {e : Set S} (hq : q ∈ D.rad.G.R)
  (he : e ∈ D.P.Γ.E)
    (heq : cap.emb '' e ⊆ q) {w : Shat} (hw : w ∈ D.rad.Rstar) (hm : (q ∩ D.rad.regionOf
      w).Nonempty) :
    ∃ f, D.P.Γ.IsSkEdgeIn f e ∧ cap.emb '' f ⊆ closure (D.rad.regionOf w) := by
  classical
  have hT := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have hS := χ.isSurface
  have h3t := D.P.fits.internally_three_connected
  have hlc : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  obtain ⟨hf₁, hf₂, hf₃⟩ := D.rad.region_facts hS h3t
  set ρ := D.rad.regionOf w with hρdef
  have hρ : ρ ∈ D.P.Γ.hatRegions cap := (D.rad.regionOf_mem hw).1
  have hρR := hSk.hatRegion_mem_R hρ
  have hρU : Disjoint ρ (D.P.Γ.hatU cap) := by
    rw [disjoint_left]
    exact fun x hx ↦ connectedComponentIn_subset _ _ hx
  -- `q` meets the frontier of `ρ`
  obtain ⟨x₀, hx₀⟩ := he.1
  have hqne : (q ∩ ρᶜ).Nonempty := by
    refine ⟨cap.emb x₀, heq (mem_image_of_mem _ hx₀), fun h ↦ disjoint_left.mp hρU h ?_⟩
    exact mem_image_of_mem _ (he.2.1 hx₀).1
  obtain ⟨p, hpq, hpfr⟩ : (q ∩ frontier ρ).Nonempty := by
    by_contra hno
    have hq' : IsPreconnected q := region_isPreconnected hq
    have hO := isOpen_regionOf D hw
    have hsub : q ⊆ ρ := hq'.subset_left_of_subset_union hO isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x hx hn ↦ hn (subset_closure hx))
      (fun x hx ↦ by
        by_cases h : x ∈ closure ρ
        · refine .inl ?_
          by_contra hn
          exact hno ⟨x, hx, ⟨h, by rwa [hO.interior_eq]⟩⟩
        · exact .inr h) hm
    obtain ⟨y, hy, hyn⟩ := hqne
    exact hyn (hsub hy)
  have hpcl : p ∈ closure ρ := frontier_subset_closure hpfr
  have hpρ : p ∉ ρ := fun h ↦ by
    rw [(isOpen_regionOf D hw).frontier_eq] at hpfr
    exact hpfr.2 h
  have hpU : p ∈ D.P.Γ.hatU cap := by
    by_contra hn
    have hpSk : p ∉ Sk.U := fun h ↦ hn (by
      rw [hSk.hU] at h
      exact image_mono D.P.Γ.skU_subset h)
    exact hpρ ((closure_region_subset hρR hpcl).resolve_right hpSk)
  obtain ⟨z, hzU, rfl⟩ := hpU
  have hzV : z ∉ D.P.Γ.V := fun h ↦ region_subset hq hpq
    (D.rad.G.V_subset_U (D.rad.isPreRadial.2.1 (mem_image_of_mem _ h)))
  -- the point lies on `e`
  obtain ⟨c, hc, hzc⟩ := exists_arcComp_superset (F := D.P.Γ.U \ D.P.Γ.V)
    (isPathConnected_singleton z) (singleton_subset_iff.2 ⟨hzU, hzV⟩)
  have hzc' : z ∈ c := hzc rfl
  have hcq : cap.emb '' c ⊆ q := by
    refine subset_region hq (hc.2.2.1.image cap.isEmbedding.continuous).isConnected.isPreconnected
      ?_
      (mem_image_of_mem _ hzc') hpq
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hG
    have hm : cap.emb y ∈ D.P.Γ.hatV cap :=
      D.rad.isPreRadial.1 ▸ ⟨mem_image_of_mem _ (hc.2.1 hy).1, hG⟩
    obtain ⟨y', hy', hyy⟩ := hm
    exact (hc.2.1 hy).2 (cap.isEmbedding.injective hyy ▸ hy')
  obtain rfl : c = e := hf₂ q hq c hc e he hcq heq
  -- so `z` lies on an edge of `sk(Γ)` in `c`
  have hskz : z ∈ D.P.Γ.skU := by
    rcases D.P.Γ.size_cases hc with h2 | h3
    · exact .inl (.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h2⟩, hzc'⟩))
    · obtain ⟨hdisc, -⟩ := D.P.Γ.isDisc_of_three hc h3
      obtain ⟨hC, hCbd⟩ := isClosedDisc_image hdisc cap.isEmbedding
      have hman : ∀ x : Shat, IsManifoldPoint x := (Surface.IsClosedSurface.isSurface hT).2.2
      by_contra hn
      have hzb : z ∉ discBd (closure c) := fun h ↦ hn (.inr (mem_iUnion₂.2 ⟨c, ⟨hc, h3⟩, h⟩))
      have hint : cap.emb z ∈ discInt (cap.emb '' closure c) := by
        refine ⟨mem_image_of_mem _ (subset_closure hzc'), fun h ↦ ?_⟩
        rw [hCbd] at h
        obtain ⟨z', hz', hzz⟩ := h
        exact hzb (cap.isEmbedding.injective hzz ▸ hz')
      obtain ⟨y, hyO, hyρ⟩ := mem_closure_iff.mp hpcl _ (hC.isOpen_discInt hman) hint
      obtain ⟨y', hy', rfl⟩ := hyO.1
      exact disjoint_left.mp hρU hyρ (mem_image_of_mem _ (D.P.Γ.closure_subset_U hc hy'))
  obtain ⟨f, hfm, hzf⟩ := exists_arcComp_superset (F := D.P.Γ.skU \ D.P.Γ.V)
    (isPathConnected_singleton z) (singleton_subset_iff.2 ⟨hskz, hzV⟩)
  have hzf' : z ∈ f := hzf rfl
  obtain ⟨c', hf⟩ := D.P.Γ.exists_isSkEdgeIn hfm
  obtain rfl : c' = c := arcComp_eq_of_mem hf.1 hc (hf.subset hzf') hzc'
  have hfE : cap.emb '' f ∈ Sk.E := hSk.edge_iff.mpr ⟨f, hfm, rfl⟩
  exact ⟨f, hf, edge_subset_closure_of_incident hT hfE hρR ⟨_, mem_image_of_mem _ hzf', hpcl⟩⟩

/-- A side of an edge of size 3 has two different ends, among the ends of the edge. -/
theorem exists_side_ends (D : TangleDatum cap χ) {e f : Set S} (hf : D.P.Γ.IsSkEdgeIn f e) (h3 :
  (tilde e).ncard = 3) :
    ∃ a b, a ≠ b ∧ a ∈ closure f ∧ b ∈ closure f ∧ a ∈ tilde e ∧ b ∈ tilde e ∧
      closure f ⊆ f ∪ {a, b} := by
  classical
  have hS := χ.isSurface
  have he := hf.1
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨Sk, hSk⟩ := exists_isSkHat hS cap D.P.Γ
  have hfE : cap.emb '' f ∈ Sk.E := hSk.edge_iff.mpr ⟨f, hf.mem, rfl⟩
  have hc3 := D.P.Γ.isDisc_of_three he h3
  obtain ⟨hC, hCbd⟩ := isClosedDisc_image hc3.1 cap.isEmbedding
  have hcl : IsClosedEmbedding cap.emb := cap.isClosedEmbedding hS
  have hfb : closure (cap.emb '' f) ⊆ cap.emb '' discBd (closure e) := by
    have hclosed : IsClosed (cap.emb '' discBd (closure e)) := by
      rw [← hCbd]
      exact hC.isOArc_discBd.isCompact.isClosed
    refine closure_minimal ?_ hclosed
    rintro _ ⟨z, hz, rfl⟩
    rcases hf.2 with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact mem_image_of_mem _ (h.2.1 hz).1
  obtain ⟨a, b, hab, hcap⟩ : ∃ a b, a ≠ b ∧ closure (cap.emb '' f) ∩ Sk.V = {a, b} := by
    rcases Sk.edge_cond _ hfE with ⟨a, b, hab, hcap, -⟩ | ⟨u, hcap, hO⟩
    · exact ⟨a, b, hab, hcap⟩
    · exfalso
      have heq' : closure (cap.emb '' f) = discBd (cap.emb '' closure e) :=
        eq_of_oArc_subset hO hC.isOArc_discBd (hCbd ▸ hfb)
      have hsub : cap.emb '' tilde e ⊆ {u} := by
        rintro _ ⟨t, ht, rfl⟩
        rw [← hcap]
        refine ⟨heq' ▸ hCbd ▸ mem_image_of_mem _ (hc3.2.1 ht), ?_⟩
        rw [hSk.hV]
        exact mem_image_of_mem _ (D.P.Γ.tilde_subset_V he ht)
      have := ncard_le_ncard hsub (toFinite _)
      rw [ncard_image_of_injective _ cap.isEmbedding.injective, h3, ncard_singleton] at this
      omega
  have hend : ∀ {t}, t ∈ closure (cap.emb '' f) ∩ Sk.V → ∃ z ∈ closure f, z ∈ tilde e ∧ cap.emb z
    = t := by
    rintro t ⟨ht, htV⟩
    rw [hcl.closure_image_eq] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [hSk.hV] at htV
    obtain ⟨z', hz', hzz⟩ := htV
    obtain rfl := cap.isEmbedding.injective hzz
    exact ⟨z', hz, ⟨closure_mono hf.subset hz, fun h ↦ D.P.Γ.disjoint_V he h hz'⟩, rfl⟩
  obtain ⟨a', ha'f, ha't, rfl⟩ := (hend (t := a) (hcap ▸ mem_insert _ _))
  obtain ⟨b', hb'f, hb't, rfl⟩ := (hend (t := b) (hcap ▸ mem_insert_of_mem _ rfl))
  refine ⟨a', b', fun h ↦ hab (by rw [h]), ha'f, hb'f, ha't, hb't, fun t ht ↦ ?_⟩
  have htcl : cap.emb t ∈ closure (cap.emb '' f) :=
    image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ ht)
  rcases closure_edge_subset hfE htcl with ⟨t', ht', htt⟩ | htV
  · exact .inl (cap.isEmbedding.injective htt ▸ ht')
  · have hm : cap.emb t ∈ closure (cap.emb '' f) ∩ Sk.V := ⟨htcl, htV⟩
    rw [hcap] at hm
    rcases hm with hm | hm
    · exact .inr (.inl (cap.isEmbedding.injective hm))
    · exact .inr (.inr (cap.isEmbedding.injective hm))

/-- **The corner lemma.** Let `q` be a region of `Γ*` with edge `e` of `Γ`, and let `q` meet the
region of `w ∈ R*`, where
`w` is `k`-near `H`, for `k ≥ 2`. If `ē` misses `bd(Σ)` or `|eTilde| = 2`, then each end of `e` is
`(k +
1)`-near `H`. -/
theorem IsNear.of_corner (hnear : D.IsNear H (k + 2) x) (hH : H.IsSubdrawing D.rad.G) {q : Set
  Shat} {e : Set S}
    (hq : q ∈ D.rad.G.R) (he : e ∈ D.P.Γ.E) (heq : cap.emb '' e ⊆ q) (hx : x ∈ D.rad.Rstar)
    (hm : (q ∩ D.rad.regionOf x).Nonempty) (hoff : (tilde e).ncard = 3 → closure e ∩ bd S = ∅)
    {v : S} (hv : v ∈ tilde e) : D.IsNear H (k + 3) (cap.emb v) := by
  classical
  have hS := χ.isSurface
  have hvV := D.P.Γ.tilde_subset_V he hv
  obtain ⟨f, hf, hfr⟩ := exists_side_of_meet D hq he heq hx hm
  have hemb : ∀ {z : S}, z ∈ closure f → cap.emb z ∈ closure (D.rad.regionOf x) := fun hz ↦ by
    have := image_closure_subset_closure_image cap.isEmbedding.continuous (mem_image_of_mem _ hz)
    exact closure_minimal hfr isClosed_closure this
  rcases D.P.Γ.size_cases he with h2 | h3
  · have hfe : f = e := by
      rcases hf.2 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    subst hfe
    exact hnear.of_closure_region hx hvV (hemb hv.1)
  obtain ⟨a', b', hab', ha'f, hb'f, ha't, hb't, -⟩ := D.exists_side_ends hf h3
  have hoff' := hoff h3
  by_cases hva : v = a'
  · subst hva
    exact hnear.of_closure_region hx hvV (hemb ha'f)
  by_cases hvb : v = b'
  · subst hvb
    exact hnear.of_closure_region hx hvV (hemb hb'f)
  have hV' := D.P.Γ.tilde_subset_V he
  rcases IsNear.exists_prev (k := k + 1) hnear hx with hmem | ⟨u, hu, hucl, hun⟩
  · have h₁ := (isNear_self hH hmem).of_closure_region hx (hV' ha't) (hemb ha'f)
    exact (IsNear.across_side he h3 ha't hv (Ne.symm hva) h₁).mono (by omega)
  · rcases D.vertex_mem_of_side hf h3 hoff' (D.rad.regionOf_mem hx).1 hfr hab' ha'f hb'f (hV' ha't)
      (hV' hb't) hu hucl
      with rfl | rfl
    · exact IsNear.across_side he h3 ha't hv (Ne.symm hva) hun
    · exact IsNear.across_side he h3 hb't hv (Ne.symm hvb) hun

end TangleDatum




end GraphMinor.GM19
