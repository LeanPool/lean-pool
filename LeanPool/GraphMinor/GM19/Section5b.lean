/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.PullPainting
public import LeanPool.GraphMinor.GM19.Sides
public import LeanPool.GraphMinor.GM19.FrameExists

/-!
# Graph Minors XIX, (5.3): the first steps

We start the proof of (5.3). An `O`-arc `F₁` in the fragment that is `Γ₁`-normal, with at most two
points
counted in `|F₁ ∩ V(Γ₁)| + |F₁ ∩ bd(Σ₁)|`, has at most one point on `bd(Σ₁)`. So `ψ` is injective on
it,
and `F = ψ(F₁)` is a `Γ`-normal `O`-arc of `Σ` with the same bound.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface

variable {S S₁ : Type} [TopologicalSpace S] [TopologicalSpace S₁] [T2Space S] [T2Space S₁]
  {Γ : Painting S} {K : Drawing S} {ψ : S₁ → S}

namespace PullData

variable (d : PullData Γ K ψ)
include d

omit [T2Space S] [T2Space S₁] in
/-- A set that meets `V₁` and `bd(Σ₁)` as in the definition of internally 3-connected has at most
one
point on the boundary. Each point of the boundary on `F₁` lies in `U₁`, so by normality it lies in
`V₁`,
and it counts twice. -/
theorem subsingleton_bd {F₁ : Set S₁} (hn : F₁ ∩ pullU Γ ψ ⊆ pullV Γ K ψ) (hfin :
  (F₁ ∩ bd S₁).Finite)
    (hc : (F₁ ∩ pullV Γ K ψ).ncard + (F₁ ∩ bd S₁).ncard ≤ 2) : (F₁ ∩ bd S₁).Subsingleton := by
  have hsub : F₁ ∩ bd S₁ ⊆ F₁ ∩ pullV Γ K ψ := fun x hx ↦ ⟨hx.1, hn ⟨hx.1, Or.inr hx.2⟩⟩
  have hfinV : (F₁ ∩ pullV Γ K ψ).Finite := d.finite_pullV.subset inter_subset_right
  have hle := ncard_le_ncard hsub hfinV
  have h1 : (F₁ ∩ bd S₁).ncard ≤ 1 := by omega
  rw [ncard_le_one hfin] at h1
  exact fun a ha b hb ↦ h1 a ha b hb

omit [T2Space S] [T2Space S₁] in
/-- `ψ` is injective on a set with at most one point on the boundary. A point of the interior maps
into `R`, and a point of the boundary does not. -/
theorem injOn_of_subsingleton {F₁ : Set S₁} (hs : (F₁ ∩ bd S₁).Subsingleton) : InjOn ψ F₁ := by
  intro a ha b hb hab
  by_cases hab₁ : a ∈ bd S₁
  · by_cases hbb : b ∈ bd S₁
    · exact hs ⟨ha, hab₁⟩ ⟨hb, hbb⟩
    · exact absurd (hab ▸ mem_image_of_mem ψ hbb) (d.frag.notMem_R_of_bd hab₁)
  · by_cases hbb : b ∈ bd S₁
    · exact absurd (hab ▸ mem_image_of_mem ψ hab₁) (d.frag.notMem_R_of_bd hbb)
    · exact d.frag.injOn_interior hab₁ hbb hab

omit [T2Space S₁] in
/-- **The image of `F₁`.** It is an `O`-arc, it is `Γ`-normal, and it satisfies the same bound. -/
theorem image_oArc {F₁ : Set S₁} (hO : IsOArc F₁) (hn : F₁ ∩ pullU Γ ψ ⊆ pullV Γ K ψ)
    (hfin : (F₁ ∩ bd S₁).Finite)
    (hc : (F₁ ∩ pullV Γ K ψ).ncard + (F₁ ∩ bd S₁).ncard ≤ 2) :
    IsOArc (ψ '' F₁) ∧ ψ '' F₁ ∩ Γ.U ⊆ Γ.V ∧ (ψ '' F₁ ∩ bd S).Finite ∧
      (ψ '' F₁ ∩ Γ.V).ncard + (ψ '' F₁ ∩ bd S).ncard ≤ 2 := by
  have hs := d.subsingleton_bd hn hfin hc
  have hinj := d.injOn_of_subsingleton hs
  have hfinV : (F₁ ∩ pullV Γ K ψ).Finite := d.finite_pullV.subset inter_subset_right
  have hV : ψ '' F₁ ∩ Γ.V ⊆ ψ '' (F₁ ∩ pullV Γ K ψ) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxV⟩
    exact mem_image_of_mem ψ ⟨hx, Or.inl hxV⟩
  have hb : ψ '' F₁ ∩ bd S ⊆ ψ '' (F₁ ∩ bd S₁) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxb⟩
    exact mem_image_of_mem ψ ⟨hx, d.mem_bd_of_notMem_R (Or.inl hxb)⟩
  refine ⟨?_, ?_, (hfin.image ψ).subset hb, ?_⟩
  · obtain ⟨f⟩ := hO
    have : CompactSpace F₁ := f.compactSpace
    have hcont : Continuous fun x : F₁ ↦ (⟨ψ x.1, mem_image_of_mem ψ x.2⟩ : ↥(ψ '' F₁)) :=
      (d.frag.continuous_ψ.comp continuous_subtype_val).subtype_mk _
    have hbij : Function.Bijective fun x : F₁ ↦ (⟨ψ x.1, mem_image_of_mem ψ x.2⟩ : ↥(ψ '' F₁)) := by
      constructor
      · intro a b hab
        exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
      · rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    exact ⟨f.trans (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) hcont)⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hxU⟩
    rcases hn ⟨hx, Or.inl hxU⟩ with h | h
    · exact h
    · exact (d.inter ⟨hxU, K.V_subset_U h⟩).1
  · have h₁ : (ψ '' F₁ ∩ Γ.V).ncard ≤ (F₁ ∩ pullV Γ K ψ).ncard :=
      (ncard_le_ncard hV (hfinV.image ψ)).trans (ncard_image_le hfinV)
    have h₂ : (ψ '' F₁ ∩ bd S).ncard ≤ (F₁ ∩ bd S₁).ncard :=
      (ncard_le_ncard hb (hfin.image ψ)).trans (ncard_image_le hfin)
    omega

omit [T2Space S] [T2Space S₁] in
/-- A connected set off `bd(Σ) ∪ U(K)` that meets `R` lies in `R`. -/
theorem subset_R_of_preconnected {A : Set S} (hAc : IsPreconnected A) (hoff : Disjoint A
  (bd S ∪ K.U))
    (hne : (A ∩ IsCuttingFragment.R ψ).Nonempty) : A ⊆ IsCuttingFragment.R ψ := by
  obtain ⟨z, hzA, hzR⟩ := hne
  obtain ⟨w, hw, hcomp⟩ := d.frag.interior_component
  have hzc : z ∈ connectedComponentIn (bd S ∪ K.U)ᶜ w := hcomp ▸ hzR
  have hsub : A ⊆ connectedComponentIn (bd S ∪ K.U)ᶜ z := hAc.subset_connectedComponentIn hzA
    (fun x hx hxb ↦ disjoint_left.mp hoff hx hxb)
  rw [← connectedComponentIn_eq hzc, hcomp] at hsub
  exact hsub

end PullData

/-! ### Discs -/

/-- The interior of the unit disc, seen in the disc, is connected near each point of the circle: the
intersection of the open disc with a small ball is convex. -/
theorem connected_near_disc (p : ClosedUnitDisc) :
    ∀ W ∈ 𝓝 p, ∃ B ⊆ {x : ClosedUnitDisc | x.1 ∉ UnitCircle} ∩ W, IsPreconnected B ∧
      ∃ W' ∈ 𝓝 p, {x : ClosedUnitDisc | x.1 ∉ UnitCircle} ∩ W' ⊆ B := by
  intro W hW
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hW
  have hopen : ∀ x : ClosedUnitDisc, x.1 ∉ UnitCircle → x.1 ∈ Metric.ball (0 : EuclideanPlane) 1
    := by
    intro x hx
    have h₁ : dist x.1 0 ≤ 1 := x.2
    exact Metric.mem_ball.mpr (lt_of_le_of_ne h₁ hx)
  refine ⟨Metric.ball p ε ∩ {x | x.1 ∉ UnitCircle}, ?_, ?_, Metric.ball p ε,
    Metric.ball_mem_nhds p hε, ?_⟩
  · exact fun x hx ↦ ⟨hx.2, hsub hx.1⟩
  · rw [← IsInducing.subtypeVal.isPreconnected_image]
    have himg : Subtype.val '' (Metric.ball p ε ∩ {x : ClosedUnitDisc | x.1 ∉ UnitCircle}) =
        Metric.ball (0 : EuclideanPlane) 1 ∩ Metric.ball p.1 ε := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy, hyc⟩, rfl⟩
        exact ⟨hopen y hyc, hy⟩
      · rintro ⟨hx, hx'⟩
        have hx₀ : x ∈ ClosedUnitDisc := Metric.ball_subset_closedBall hx
        refine ⟨⟨x, hx₀⟩, ⟨hx', ?_⟩, rfl⟩
        exact (Metric.mem_ball.mp hx).ne
    rw [himg]
    exact ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  · exact fun x hx ↦ ⟨hx.2, hx.1⟩

/-- The inside of a closed disc is connected near each boundary point. -/
theorem isConnectedNear_discInt.{u} {S : Type u} [TopologicalSpace S] [T2Space S] {Δ : Set S}
  (hΔ : IsClosedDisc Δ)
    {v : S} (hv : v ∈ discBd Δ) : IsConnectedNear (discInt Δ) v := by
  obtain ⟨φ⟩ := id hΔ
  have hbd := disc_boundary Δ φ
  rw [hbd] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have himg : (fun x ↦ (φ x).1) '' {x : ClosedUnitDisc | x.1 ∉ UnitCircle} = discInt Δ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(φ x).2, ?_⟩
      rw [hbd]
      rintro ⟨x', hx', he⟩
      have : x' = x := φ.injective (Subtype.ext he)
      exact hx (this ▸ hx')
    · rintro ⟨hy, hyb⟩
      refine ⟨φ.symm ⟨y, hy⟩, ?_, by simp⟩
      intro hc
      apply hyb
      rw [hbd]
      exact ⟨_, hc, by simp⟩
  have h := isConnectedNear_of_homeo φ (connected_near_disc p)
  rwa [himg] at h

/-- **Lifting a disc.** Let `F₁` be an `O`-arc in the fragment with at most one point on the
boundary, and
let `Δ` be a disc of `Σ` bounded by `ψ(F₁)` whose inside misses `bd(Σ) ∪ U(K)`. Then the closure of
the
lift of the inside of `Δ` is a disc of `Σ₁` bounded by `F₁`. The point on the boundary needs an
argument,
since the fragment may have several points over its image: the rest of `F₁` lies in the closed disc
and
accumulates at that point. -/
theorem PullData.exists_disc_lift (d : PullData Γ K ψ) {F₁ : Set S₁}
    {Δ : Set S} (hO : IsOArc F₁) (hs : (F₁ ∩ bd S₁).Subsingleton) (hΔ : IsClosedDisc Δ)
    (hF : discBd Δ = ψ '' F₁) (hoff : Disjoint (discInt Δ) (bd S ∪ K.U)) :
    ∃ Δ₁ : Set S₁, IsClosedDisc Δ₁ ∧ discBd Δ₁ = F₁ ∧ ψ '' Δ₁ = Δ ∧ InjOn ψ Δ₁ := by
  obtain ⟨f⟩ := id hO
  have hpi := Real.pi_pos
  have hnear : ∀ u ∈ F₁, u ∈ closure (F₁ \ bd S₁) := by
    intro u hu
    by_cases hub : u ∈ bd S₁
    · obtain ⟨t, -, ht⟩ := exists_angle_in f 0 ⟨u, hu⟩
      change cuffPoint f t = u at ht
      have hsub : arcOf f t (t + Real.pi) ⊆ F₁ \ bd S₁ := by
        rintro _ ⟨s, hs', rfl⟩
        refine ⟨cuffPoint_mem f s, fun hb ↦ ?_⟩
        have he : cuffPoint f s = cuffPoint f t := by
          rw [ht]
          exact hs ⟨cuffPoint_mem f s, hb⟩ ⟨hu, hub⟩
        have := cuffPoint_injOn f (a := t) (b := t + 2 * Real.pi) le_rfl
          ⟨hs'.1.le, by linarith [hs'.2]⟩ ⟨le_rfl, by linarith⟩ he
        linarith [hs'.1]
      refine closure_mono hsub ?_
      rw [closure_arcOf f (by linarith)]
      exact ⟨t, ⟨le_rfl, by linarith⟩, ht⟩
    · exact subset_closure ⟨hu, hub⟩
  have hR := d.isOpen_R
  have hbd := d.isClosed_bd
  have hAsub : discInt Δ ⊆ Δ := discInt_subset Δ
  have hcl : closure (discInt Δ) = Δ :=
    Subset.antisymm (closure_minimal hAsub hΔ.isClosed) hΔ.subset_closure_discInt
  obtain ⟨x₀, hx₀⟩ : (F₁ \ bd S₁).Nonempty :=
    closure_nonempty_iff.mp ⟨_, hnear _ (f 1).2⟩
  have hbdΔ : ψ x₀ ∈ Δ := Surface.discBd_subset _ (hF ▸ mem_image_of_mem ψ hx₀.1)
  have hAR : discInt Δ ⊆ IsCuttingFragment.R ψ := by
    refine d.subset_R_of_preconnected hΔ.isPreconnected_discInt hoff ?_
    obtain ⟨z, hzR, hzA⟩ := mem_closure_iff.mp (hcl.symm ▸ hbdΔ) _ hR
      (mem_image_of_mem ψ hx₀.2)
    exact ⟨z, hzA, hzR⟩
  have hloc : ∀ v ∈ tilde (discInt Δ), IsConnectedNear (discInt Δ) v := by
    rintro v ⟨hv, hvn⟩
    rw [hcl] at hv
    refine isConnectedNear_discInt hΔ ?_
    by_contra hvb
    exact hvn ⟨hv, hvb⟩
  have himg : ψ '' closure (ψ ⁻¹' discInt Δ) = Δ := by
    rw [d.frag.image_closure_preimage hAR, hcl]
  have hinj : InjOn ψ (closure (ψ ⁻¹' discInt Δ)) := by
    intro x hx y hy hxy
    have h := (d.frag.bijective_closureMap hbd hR hAR hloc).1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩)
      (Subtype.ext hxy)
    exact congrArg Subtype.val h
  let H := (d.frag.homeoClosure hbd hR hAR hloc).trans (Homeomorph.setCongr hcl)
  have hH : ∀ x, (H x).1 = ψ x.1 := fun _ ↦ rfl
  -- The points of `F₁` off the boundary lie in the closed disc, and so does the rest.
  have hin : F₁ ⊆ closure (ψ ⁻¹' discInt Δ) := by
    have hoffb : F₁ \ bd S₁ ⊆ closure (ψ ⁻¹' discInt Δ) := by
      rintro x ⟨hx, hxb⟩
      have hxΔ : ψ x ∈ Δ := Surface.discBd_subset _ (hF ▸ mem_image_of_mem ψ hx)
      rw [← himg] at hxΔ
      obtain ⟨w, hw, hwx⟩ := hxΔ
      have hwb : w ∉ bd S₁ := fun hb ↦
        d.frag.notMem_R_of_bd hb (hwx ▸ mem_image_of_mem ψ hxb)
      rw [← d.frag.injOn_interior hwb hxb hwx]
      exact hw
    exact fun u hu ↦ closure_minimal hoffb isClosed_closure (hnear u hu)
  refine ⟨_, ?_, ?_, himg, hinj⟩
  · obtain ⟨φ⟩ := id hΔ
    exact ⟨φ.trans H.symm⟩
  · ext z
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : H b ∈ bd Δ := by
        rw [← image_bd H]
        exact mem_image_of_mem _ hb
      have hm : ψ b.1 ∈ ψ '' F₁ := by
        rw [← hF, ← hH]
        exact ⟨_, hb', rfl⟩
      obtain ⟨x, hx, hxb⟩ := hm
      rw [← hinj (hin hx) b.2 hxb]
      exact hx
    · intro hz
      have hm : ψ z ∈ discBd Δ := hF ▸ mem_image_of_mem ψ hz
      obtain ⟨y, hy, hyz⟩ := hm
      refine ⟨H.symm y, ?_, ?_⟩
      · rw [← image_bd H.symm]
        exact mem_image_of_mem _ hy
      · refine hinj (Subtype.property _) (hin hz) ?_
        rw [← hH, Homeomorph.apply_symm_apply, hyz]

/-- No part of `K` is hidden behind one point. Every point `x` of `U(K)`, once a point `u ≠ x` is
removed,
is joined inside `U(K) \ {u}` to a vertex of `Γ`. This follows from the hypothesis of (5.3) when `K`
is
a line whose two ends are vertices of `Γ`, or an `O`-arc with two vertices of `Γ`. Those are the
only
drawings along which we cut. For them no local study near `u` is needed, unlike the proof in the
paper
for a general `K`. -/
def IsAnchored (Γ : Painting S) (K : Drawing S) : Prop :=
  ∀ u x, x ∈ K.U → x ≠ u → ∃ C ⊆ K.U \ {u}, x ∈ C ∧ IsPreconnected C ∧ (C ∩ Γ.V).Nonempty

/-- **The fourth condition of (5.3).** The disc bounded by the image of `F₁` has nothing of `K`
inside,
since `K` would have to reach a vertex of `Γ` inside the disc. So the disc lifts. -/
theorem PullData.exists_disc (d : PullData Γ K ψ)
    (hΓ : Γ.IsInternallyThreeConnected) (hA : IsAnchored Γ K) {F₁ : Set S₁} (hO : IsOArc F₁)
    (hn : F₁ ∩ pullU Γ ψ ⊆ pullV Γ K ψ) (hfin : (F₁ ∩ bd S₁).Finite)
    (hc : (F₁ ∩ pullV Γ K ψ).ncard + (F₁ ∩ bd S₁).ncard ≤ 2) :
    ∃ Δ₁ : Set S₁, IsClosedDisc Δ₁ ∧ discBd Δ₁ = F₁ ∧ Δ₁ ∩ pullV Γ K ψ ⊆ F₁ := by
  have hs := d.subsingleton_bd hn hfin hc
  obtain ⟨hO', hn', hfin', hc'⟩ := d.image_oArc hO hn hfin hc
  obtain ⟨Δ, hΔ, hbdΔ, hV⟩ := hΓ.2 _ hO' hn' hfin' hc'
  have hman : ∀ x : S, IsManifoldPoint x := d.surface.2.2
  -- `F` meets `U(K)` in at most one point.
  obtain ⟨u, huF, hu⟩ : ∃ u ∈ ψ '' F₁, ψ '' F₁ ∩ K.U ⊆ {u} := by
    by_cases hne : (ψ '' F₁ ∩ K.U).Nonempty
    · obtain ⟨u, hu⟩ := hne
      refine ⟨u, hu.1, ?_⟩
      rintro _ ⟨⟨a, ha, rfl⟩, haK⟩
      obtain ⟨⟨b, hb, rfl⟩, hbK⟩ := hu
      have ha' : a ∈ bd S₁ := d.mem_bd_of_notMem_R (Or.inr haK)
      have hb' : b ∈ bd S₁ := d.mem_bd_of_notMem_R (Or.inr hbK)
      rw [hs ⟨ha, ha'⟩ ⟨hb, hb'⟩]
      rfl
    · obtain ⟨f⟩ := hO
      exact ⟨_, mem_image_of_mem ψ (f 1).2, fun z hz ↦ (hne ⟨z, hz⟩).elim⟩
  have hoffK : Disjoint (discInt Δ) K.U := by
    refine disjoint_left.mpr fun x hx hxK ↦ ?_
    have hxF : x ∉ ψ '' F₁ := hbdΔ ▸ hx.2
    have hxu : x ≠ u := fun h ↦ hxF (h ▸ huF)
    obtain ⟨C, hCsub, hxC, hCc, v, hvC, hvV⟩ := hA u x hxK hxu
    have hCF : Disjoint C (ψ '' F₁) := by
      refine disjoint_left.mpr fun y hyC hyF ↦ (hCsub hyC).2 (hu ⟨hyF, (hCsub hyC).1⟩)
    have hCin : C ⊆ discInt Δ := by
      refine hCc.subset_left_of_subset_union (hΔ.isOpen_discInt hman) hΔ.isClosed.isOpen_compl
        (disjoint_left.mpr fun w hw hn ↦ hn hw.1) (fun y hy ↦ ?_) ⟨x, hxC, hx⟩
      by_cases hyΔ : y ∈ Δ
      · exact Or.inl ⟨hyΔ, fun hb ↦ disjoint_left.mp hCF hy (hbdΔ ▸ hb)⟩
      · exact Or.inr hyΔ
    exact (hCin hvC).2 (hbdΔ ▸ hV ⟨(hCin hvC).1, hvV⟩)
  have hoff : Disjoint (discInt Δ) (bd S ∪ K.U) := by
    refine disjoint_left.mpr ?_
    rintro x hx (hxb | hxK)
    · exact hxb (isInteriorPoint_of_mem_discInt hman hΔ hx)
    · exact disjoint_left.mp hoffK hx hxK
  obtain ⟨Δ₁, hΔ₁, hbd₁, himg, hinj⟩ := d.exists_disc_lift hO hs hΔ hbdΔ hoff
  refine ⟨Δ₁, hΔ₁, hbd₁, ?_⟩
  rintro x ⟨hxΔ, hxV⟩
  have hxF : ψ x ∈ ψ '' F₁ := by
    have hxD : ψ x ∈ Δ := himg ▸ mem_image_of_mem ψ hxΔ
    rcases hxV with h | h
    · exact hV ⟨hxD, h⟩
    · by_contra hn'
      exact disjoint_left.mp hoffK ⟨hxD, fun hb ↦ hn' (hbdΔ ▸ hb)⟩ (K.V_subset_U h)
  obtain ⟨y, hy, hyx⟩ := hxF
  have hyΔ : y ∈ Δ₁ := Surface.discBd_subset _ (hbd₁ ▸ hy)
  exact hinj hyΔ hxΔ hyx ▸ hy

omit [T2Space S] [T2Space S₁] in
/-- A cuff has a point off the finite set `V₁`, so the boundary gives an edge. -/
theorem PullData.nonempty_pieces (d : PullData Γ K ψ) (hne : (bd S₁).Nonempty) :
    (arcComponentsIn (bd S₁ \ pullV Γ K ψ)).Nonempty := by
  have hSur := d.frag.isSurface
  have hpi := Real.pi_pos
  obtain ⟨x, hx⟩ := hne
  obtain ⟨C, hC, -⟩ := sUnion_cuffs (S := S₁) ▸ hx
  let C' : cuffs S₁ := ⟨C, hC⟩
  obtain ⟨f⟩ := (cuff_statement S₁ hSur).2.2 C hC
  have hinf : (cuffPoint f '' Ico 0 (2 * Real.pi)).Infinite :=
    (Ico_infinite (by linarith)).image fun a ha b hb h ↦
      cuffPoint_injOn f (a := 0) (by linarith) ha hb h
  obtain ⟨y, hy, hyV⟩ := hinf.exists_notMem_finite d.finite_pullV
  obtain ⟨t, -, rfl⟩ := hy
  obtain ⟨p, hp, -⟩ := exists_arcComp_superset (F := bd S₁ \ pullV Γ K ψ)
    (isPathConnected_singleton (cuffPoint f t))
    (singleton_subset_iff.mpr ⟨cuff_subset_bd C' (cuffPoint_mem f t), hyV⟩)
  exact ⟨p, hp⟩

omit [T2Space S₁] in
/-- `Γ₁` has an edge. If the fragment has boundary this comes from `PullData.nonempty_pieces`. If
not, the fragment
fills all of the connected surface `Σ`, and each edge of `Γ` lifts. -/
theorem PullData.nonempty_pullPieces [Nonempty S₁] [ConnectedSpace S] (d : PullData Γ K ψ)
  (hE : Γ.E.Nonempty) :
    (pullPieces Γ K ψ).Nonempty := by
  by_cases hne : (bd S₁).Nonempty
  · obtain ⟨p, hp⟩ := d.nonempty_pieces hne
    exact ⟨p, Or.inl hp⟩
  · have hemp : bd S₁ = ∅ := not_nonempty_iff_eq_empty.mp hne
    have hR : IsCuttingFragment.R ψ = range ψ := by
      rw [IsCuttingFragment.R, hemp, compl_empty, image_univ]
    have hclo : IsClopen (IsCuttingFragment.R ψ) :=
      ⟨hR ▸ d.frag.isClosedMap.isClosed_range, d.isOpen_R⟩
    obtain ⟨x⟩ := ‹Nonempty S₁›
    have huniv := hclo.eq_univ ⟨ψ x, by rw [hR]; exact mem_range_self x⟩
    obtain ⟨e, he⟩ := hE
    obtain ⟨z, hz⟩ := he.1
    have hb : ¬ Painting.IsBorder e := by
      rintro ⟨w, -, hw⟩
      have hwR : w ∈ IsCuttingFragment.R ψ := huniv ▸ mem_univ w
      exact disjoint_left.mp d.frag.disjoint_R hwR (Or.inl hw)
    have hzR : z ∈ IsCuttingFragment.R ψ := huniv ▸ mem_univ z
    obtain ⟨z₁, -, hz₁⟩ := hzR
    exact ⟨ψ ⁻¹' e, Or.inr ⟨e, he, hb, ⟨z₁, by rw [mem_preimage, hz₁]; exact hz⟩, rfl⟩⟩

/-- **The fourth condition in the definition of "fit", for the pull-back** (Graph Minors XIX,
(5.3)). -/
theorem PullData.isInternallyThreeConnected [Nonempty S₁] [ConnectedSpace S] (d : PullData Γ K ψ)
    (γb : Set S₁ → List S₁)
    (hγ₁ : ∀ p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ), (γb p).Nodup)
    (hγ₂ : ∀ p ∈ arcComponentsIn (bd S₁ \ pullV Γ K ψ), {v | v ∈ γb p} = tilde p)
    (hΓ : Γ.IsInternallyThreeConnected) (hA : IsAnchored Γ K) :
    (pullPainting d γb hγ₁ hγ₂).IsInternallyThreeConnected := by
  refine ⟨?_, fun F₁ hO hn hfin hc ↦ d.exists_disc hΓ hA hO hn hfin hc⟩
  obtain ⟨p, hp⟩ := d.nonempty_pullPieces hΓ.1
  refine ⟨p, ?_⟩
  change p ∈ arcComponentsIn (pullU Γ ψ \ pullV Γ K ψ)
  rw [d.arcComponentsIn_eq]
  exact hp

end GraphMinor.GM19
