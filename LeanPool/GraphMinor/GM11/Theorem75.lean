/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Nice73
public import LeanPool.GraphMinor.GM11.PerimeterWalk
public import LeanPool.GraphMinor.GM11.RadialChord
public import LeanPool.GraphMinor.GM11.Rotation
public import LeanPool.GraphMinor.GM11.PaintingFacts
public import LeanPool.GraphMinor.GM11.Section5

/-!
# (7.5) of Graph Minors XI

The paper cuts discs around the points of `Y` out of `Σ`, and applies Graph Minors VII, (11.10) to
the
result. We work in the open set `W = Σ - Y` instead. `exists_open_around` needs a connected set. So
we first join
the components of `X` by lines `T` off `X` and off `Y`, one line at a time (`exists_bridge`). An
`O`-arc in `X ∪ T` lies
in `X` (`oArc_subset_of_bridge`), and `X ∪ T` is nice, so that the hypothesis stays true.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S]

section Line

variable [T2Space S]

/-- An `O`-arc does not lie in a line. -/
theorem not_oArc_subset_arc {e : I → S} (he : Continuous e) (hi : Function.Injective e) {F : Set S}
    (hF : IsOArc F) (hsub : F ⊆ range e) : False := by
  have hemb := he.isClosedEmbedding hi
  have hinf := infinite_of_isOArc hF
  have hFc : IsCompact F := by
    obtain ⟨f⟩ := id hF
    exact isCompact_iff_compactSpace.mpr f.compactSpace
  have hprec : ∀ {A : Set S}, A ⊆ F → IsPreconnected A → IsPreconnected (e ⁻¹' A) := by
    intro A hA hp
    refine hemb.isInducing.isPreconnected_image.mp ?_
    rwa [image_preimage_eq_of_subset (hA.trans hsub)]
  let C : Set I := e ⁻¹' F
  have hCc : IsCompact C := (hFc.isClosed.preimage he).isCompact
  have hCinf : C.Infinite := fun h => hinf ((h.image e).subset fun x hx => by
    obtain ⟨t, rfl⟩ := hsub hx
    exact ⟨t, hx, rfl⟩)
  obtain ⟨s, hs⟩ := hCc.exists_isLeast hCinf.nonempty
  obtain ⟨t, ht⟩ := hCc.exists_isGreatest hCinf.nonempty
  obtain ⟨m, hm, hmn⟩ := hCinf.exists_notMem_finset {s, t}
  have hms : m ≠ s := fun h => hmn (by simp [h])
  have hmt : m ≠ t := fun h => hmn (by simp [h])
  have hsm : s < m := lt_of_le_of_ne (hs.2 hm) hms.symm
  have hmt' : m < t := lt_of_le_of_ne (ht.2 hm) hmt
  have hc := hprec (A := F \ {e m}) sdiff_subset (isPathConnected_oArc_diff hF
    hm).isConnected.isPreconnected
  have hsmem : s ∈ e ⁻¹' (F \ {e m}) := ⟨hs.1, fun h => hsm.ne (hi h)⟩
  have htmem : t ∈ e ⁻¹' (F \ {e m}) := ⟨ht.1, fun h => hmt'.ne' (hi h)⟩
  exact (hc.Icc_subset hsmem htmem ⟨hsm.le, hmt'.le⟩).2 rfl

/-- **An `O`-arc in `X₁ ∪ X₂ ∪ T` lies in `X₁ ∪ X₂`**, if the line `T` joins the disjoint closed
sets `X₁` and
`X₂`, and its inside misses them. -/
theorem oArc_subset_of_bridge {X₁ X₂ : Set S} (h₁ : IsClosed X₁) (h₂ : IsClosed X₂)
  (hd : Disjoint X₁ X₂)
    {e : I → S} (he : Continuous e) (hi : Function.Injective e) (h0 : e 0 ∈ X₁) (h1 : e 1 ∈ X₂)
    (hin : ∀ t, t ≠ 0 → t ≠ 1 → e t ∉ X₁ ∪ X₂) {F : Set S} (hF : IsOArc F)
    (hsub : F ⊆ X₁ ∪ X₂ ∪ range e) : F ⊆ X₁ ∪ X₂ := by
  by_contra hnot
  obtain ⟨y, hyF, hyX⟩ := not_subset.mp hnot
  -- If `e t ∈ F`, then `F - {e t}` lies on one side of `e t`.
  have hside : ∀ t, t ≠ 0 → t ≠ 1 → e t ∈ F → F ⊆ X₁ ∪ e '' Iic t ∨ F ⊆ X₂ ∪ e '' Ici t := by
    intro t ht0 ht1 htF
    have hc₁ : IsClosed (X₁ ∪ e '' Iic t) := h₁.union (isClosed_Iic.isCompact.image he).isClosed
    have hc₂ : IsClosed (X₂ ∪ e '' Ici t) := h₂.union (isClosed_Ici.isCompact.image he).isClosed
    have hp := (isPathConnected_oArc_diff hF htF).isConnected.isPreconnected
    have hcov : F \ {e t} ⊆ (X₁ ∪ e '' Iic t) ∪ (X₂ ∪ e '' Ici t) := by
      rintro x ⟨hx, -⟩
      rcases hsub hx with (h | h) | ⟨u, rfl⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · rcases le_total u t with h | h
        · exact Or.inl (Or.inr ⟨u, h, rfl⟩)
        · exact Or.inr (Or.inr ⟨u, h, rfl⟩)
    have hmeet : Disjoint ((X₁ ∪ e '' Iic t) ∩ (X₂ ∪ e '' Ici t)) (F \ {e t}) := by
      refine disjoint_left.mpr ?_
      rintro x ⟨h₃ | ⟨u, hu, rfl⟩, h₄ | ⟨v, hv, h'⟩⟩ ⟨-, hne⟩
      · exact disjoint_left.mp hd h₃ h₄
      · subst h'
        have huv : v = 0 := by
          by_contra hv0
          refine hin v hv0 ?_ (Or.inl h₃)
          exact fun hv1 => absurd (hv1 ▸ h₃) (disjoint_right.mp hd h1)
        rw [huv] at hv
        exact ht0 (le_antisymm hv zero_le)
      · have hu1 : u = 1 := by
          by_contra hu1
          refine hin u ?_ hu1 (Or.inr h₄)
          exact fun hu0 => absurd h₄ (hu0 ▸ disjoint_left.mp hd h0)
        rw [hu1] at hu
        exact ht1 (le_antisymm unitInterval.le_one' hu)
      · have : u = v := hi h'.symm
        subst this
        exact hne (mem_singleton_iff.mpr (congrArg e (le_antisymm hu hv)))
    by_contra hno
    rw [not_or] at hno
    have hA : (F \ {e t} ∩ (X₁ ∪ e '' Iic t)).Nonempty := by
      by_contra hne
      refine hno.2 fun x hx => ?_
      by_cases hxt : x = e t
      · exact hxt ▸ Or.inr ⟨t, self_mem_Ici, rfl⟩
      · rcases hcov ⟨hx, hxt⟩ with h | h
        · exact absurd ⟨x, ⟨hx, hxt⟩, h⟩ hne
        · exact h
    have hB : (F \ {e t} ∩ (X₂ ∪ e '' Ici t)).Nonempty := by
      by_contra hne
      refine hno.1 fun x hx => ?_
      by_cases hxt : x = e t
      · exact hxt ▸ Or.inr ⟨t, self_mem_Iic, rfl⟩
      · rcases hcov ⟨hx, hxt⟩ with h | h
        · exact h
        · exact absurd ⟨x, ⟨hx, hxt⟩, h⟩ hne
    obtain ⟨x, hx, hx'⟩ := isPreconnected_closed_iff.mp hp _ _ hc₁ hc₂ hcov hA hB
    exact disjoint_left.mp hmeet hx' hx
  -- If `F` lies on both sides, then it lies in the line.
  have hboth : ∀ {t u : I}, F ⊆ X₁ ∪ e '' Iic t → F ⊆ X₂ ∪ e '' Ici u → False := by
    intro t u hl hr
    refine not_oArc_subset_arc he hi hF fun x hx => ?_
    rcases hl hx with h | ⟨v, -, rfl⟩
    · rcases hr hx with h' | ⟨v, -, rfl⟩
      · exact absurd h' (disjoint_left.mp hd h)
      · exact mem_range_self v
    · exact mem_range_self v
  obtain ⟨t, rfl⟩ : y ∈ range e := by
    rcases hsub hyF with h | h
    · exact absurd h hyX
    · exact h
  have ht0 : t ≠ 0 := fun h => hyX (Or.inl (h ▸ h0))
  have ht1 : t ≠ 1 := fun h => hyX (Or.inr (h ▸ h1))
  -- A second such point gives both sides or a contradiction.
  have hone : ∀ u, u ≠ 0 → u ≠ 1 → e u ∈ F → u = t := by
    intro u hu0 hu1 huF
    by_contra hne
    rcases hside t ht0 ht1 hyF with h | h <;> rcases hside u hu0 hu1 huF with h' | h'
    · rcases lt_or_gt_of_ne hne with hlt | hlt
      · rcases h' hyF with h₃ | ⟨v, hv, h₃⟩
        · exact hyX (Or.inl h₃)
        · exact absurd (hi h₃ ▸ hv) (not_le.mpr hlt)
      · rcases h huF with h₃ | ⟨v, hv, h₃⟩
        · exact hin u hu0 hu1 (Or.inl h₃)
        · exact absurd (hi h₃ ▸ hv) (not_le.mpr hlt)
    · exact hboth h h'
    · exact hboth h' h
    · rcases lt_or_gt_of_ne hne with hlt | hlt
      · rcases h huF with h₃ | ⟨v, hv, h₃⟩
        · exact hin u hu0 hu1 (Or.inr h₃)
        · exact absurd (hi h₃ ▸ hv) (not_le.mpr hlt)
      · rcases h' hyF with h₃ | ⟨v, hv, h₃⟩
        · exact hyX (Or.inr h₃)
        · exact absurd (hi h₃ ▸ hv) (not_le.mpr hlt)
  -- So `e t` is alone in `F` among the points off `X₁ ∪ X₂`, and it is isolated in `F`.
  have hrest : F \ {e t} ⊆ X₁ ∪ X₂ := by
    rintro x ⟨hx, hxt⟩
    rcases hsub hx with h | ⟨u, rfl⟩
    · exact h
    · by_cases hu0 : u = 0
      · exact Or.inl (hu0 ▸ h0)
      · by_cases hu1 : u = 1
        · exact Or.inr (hu1 ▸ h1)
        · exact absurd (mem_singleton_iff.mpr (congrArg e (hone u hu0 hu1 hx))) hxt
  have hcl : IsClosed (X₁ ∪ X₂) := h₁.union h₂
  have hp := hF.isPreconnected
  have hcov : F ⊆ (X₁ ∪ X₂) ∪ {e t} := fun x hx => by
    by_cases hxt : x = e t
    · exact Or.inr hxt
    · exact Or.inl (hrest ⟨hx, hxt⟩)
  have hAne : (F ∩ (X₁ ∪ X₂)).Nonempty := by
    obtain ⟨x, hx, hxt⟩ := (infinite_of_isOArc hF).exists_notMem_finset {e t}
    exact ⟨x, hx, hrest ⟨hx, by simpa using hxt⟩⟩
  obtain ⟨x, -, hx₁, hx₂⟩ := isPreconnected_closed_iff.mp hp _ _ hcl isClosed_singleton hcov hAne
    ⟨e t, hyF, rfl⟩
  exact hyX (hx₂ ▸ hx₁)

end Line

section Surface

variable [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- A compact subset of an open disc lies in a closed disc in the open disc. -/
theorem exists_closedDisc_of_isCompact [T2Space S] {A C : Set S} (hA : IsOpenDisc A)
  (hC : IsCompact C)
    (hCA : C ⊆ A) : ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ A ∧ C ⊆ Δ := by
  obtain ⟨-, ⟨ψ⟩⟩ := hA
  let K : Set OpenUnitDisc := ψ.symm '' (Subtype.val ⁻¹' C)
  have hK : IsCompact K := by
    refine IsCompact.image ?_ ψ.symm.continuous
    exact (IsInducing.subtypeVal.isCompact_preimage_iff (by simpa using hCA)).mpr hC
  -- A radius below `1` that bounds `K`.
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ x ∈ K, ‖x.1‖ ≤ ρ := by
    by_cases hne : K.Nonempty
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (f := fun x : OpenUnitDisc => ‖x.1‖)
        (by fun_prop)
      have hlt : ‖x.1‖ < 1 := by simpa [OpenUnitDisc] using x.2
      exact ⟨max (1 / 2) ‖x.1‖, by positivity, max_lt (by norm_num) hlt,
        fun y hy => (hmax hy).trans (le_max_right _ _)⟩
    · exact ⟨1 / 2, by norm_num, by norm_num, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hin : ∀ x : ClosedUnitDisc, ρ • x.1 ∈ OpenUnitDisc := by
    intro x
    have hx : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
    simp only [OpenUnitDisc, Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ0]
    nlinarith [norm_nonneg x.1]
  let G : ClosedUnitDisc → S := fun x => (ψ ⟨ρ • x.1, hin x⟩).1
  have hG : Continuous G := by
    refine continuous_subtype_val.comp (ψ.continuous.comp (Continuous.subtype_mk ?_ _))
    fun_prop
  have hGi : Function.Injective G := by
    intro x y h
    have h₁ := ψ.injective (Subtype.ext h)
    have h₂ : ρ • x.1 = ρ • y.1 := congrArg Subtype.val h₁
    exact Subtype.ext (smul_right_injective _ hρ0.ne' h₂)
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hemb := hG.isClosedEmbedding hGi
  refine ⟨range G, ⟨hemb.isEmbedding.toHomeomorph⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (ψ _).2
  · intro c hc
    let z : OpenUnitDisc := ψ.symm ⟨c, hCA hc⟩
    have hz : z ∈ K := ⟨⟨c, hCA hc⟩, hc, rfl⟩
    have hn := hρ z hz
    have hmem : ρ⁻¹ • z.1 ∈ ClosedUnitDisc := by
      simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hρ0]
      rw [inv_mul_le_iff₀ hρ0]
      linarith
    refine ⟨⟨_, hmem⟩, ?_⟩
    have he : (⟨ρ • (ρ⁻¹ • z.1), hin ⟨_, hmem⟩⟩ : OpenUnitDisc) = z :=
      Subtype.ext (by simp [smul_smul, hρ0.ne'])
    change (ψ ⟨ρ • (ρ⁻¹ • z.1), hin ⟨_, hmem⟩⟩).1 = c
    rw [he]
    simp [z]

omit [ConnectedSpace S] in
/-- A path from a point `a` of a closed surface, into a given open set near `a`. -/
theorem exists_path_from_point (hS : IsClosedSurface S) {O : Set S} (hO : IsOpen O) {a : S}
  (ha : a ∈ O) :
    ∃ g : I → S, Continuous g ∧ g 0 = a ∧ ∀ t, 0 < t → g t ∈ O \ {a} := by
  have : T2Space S := hS.2.1
  obtain ⟨D, D', hD, -, ha', hsub, hDO, -⟩ := exists_closedDisc_nbhd hS hO ha
  obtain ⟨φ⟩ := id hD
  have haD : a ∈ D := hsub ha'
  let q : ClosedUnitDisc := φ.symm ⟨a, haD⟩
  obtain ⟨u, hu⟩ : ∃ u : ClosedUnitDisc, u ≠ q := by
    have h0 : (0 : EuclideanPlane) ∈ ClosedUnitDisc := by simp [ClosedUnitDisc]
    have h1 : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈ ClosedUnitDisc := by simp [ClosedUnitDisc]
    by_cases h : (⟨0, h0⟩ : ClosedUnitDisc) = q
    · refine ⟨⟨_, h1⟩, fun h' => ?_⟩
      have := congrArg Subtype.val (h'.trans h.symm)
      simp at this
    · exact ⟨_, h⟩
  have hmem : ∀ t : I, (1 - t.1) • q.1 + t.1 • u.1 ∈ ClosedUnitDisc := by
    intro t
    exact (convex_closedBall (0 : EuclideanPlane) 1) q.2 u.2 (by linarith [t.2.2]) t.2.1 (by ring)
  let g : I → S := fun t => (φ ⟨_, hmem t⟩).1
  refine ⟨g, ?_, ?_, ?_⟩
  · refine continuous_subtype_val.comp (φ.continuous.comp (Continuous.subtype_mk ?_ _))
    fun_prop
  · have : (⟨_, hmem 0⟩ : ClosedUnitDisc) = q := Subtype.ext (by simp)
    change (φ ⟨_, hmem 0⟩).1 = a
    rw [this]
    simp [q]
  · intro t ht
    refine ⟨hDO (φ _).2, fun h => hu ?_⟩
    have h₁ : φ ⟨_, hmem t⟩ = φ q := Subtype.ext (by simpa [q] using h)
    have h₂ : (1 - t.1) • q.1 + t.1 • u.1 = q.1 := congrArg Subtype.val (φ.injective h₁)
    have ht' : t.1 ≠ 0 := (show (0 : ℝ) < t.1 from ht).ne'
    have h₃ : t.1 • (u.1 - q.1) = 0 := by
      rw [smul_sub]
      rw [sub_smul, one_smul] at h₂
      have : q.1 - t.1 • q.1 + t.1 • u.1 - q.1 = 0 := by rw [h₂, sub_self]
      rw [← this]
      abel
    exact Subtype.ext (sub_eq_zero.mp ((smul_eq_zero.mp h₃).resolve_left ht'))

/-- The two parts of a closed set. A region off `X` touches both of them, for otherwise `Σ` splits.
-/
theorem exists_region_between (hS : IsClosedSurface S) {N : Drawing S} {X₁ X₂ : Set S}
  (h₁ : IsClosed X₁)
    (h₂ : IsClosed X₂) (hd : Disjoint X₁ X₂) (hN : N.U ⊆ X₁ ∪ X₂) (hne₁ : X₁.Nonempty)
      (hne₂ : X₂.Nonempty)
    (hreg : ∀ q ∈ N.R, q ⊆ X₁ ∪ X₂ ∨ Disjoint q (X₁ ∪ X₂)) :
    ∃ q ∈ N.R, Disjoint q (X₁ ∪ X₂) ∧ (closure q ∩ X₁).Nonempty ∧ (closure q ∩ X₂).Nonempty := by
  classical
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hfin := finite_R hS N
  let P : Set (Set S) := {q ∈ N.R | Disjoint q (X₁ ∪ X₂)}
  have hPf : P.Finite := hfin.subset fun _ h => h.1
  let P₁ : Set (Set S) := {q ∈ P | (closure q ∩ X₁).Nonempty}
  let P₂ : Set (Set S) := {q ∈ P | ¬ (closure q ∩ X₁).Nonempty}
  let B₁ : Set S := X₁ ∪ ⋃ q ∈ P₁, closure q
  let B₂ : Set S := X₂ ∪ ⋃ q ∈ P₂, closure q
  have hP₁_finite : P₁.Finite := hPf.subset fun _ h => h.1
  have hP₂_finite : P₂.Finite := hPf.subset fun _ h => h.1
  have hB₁ : IsClosed B₁ := h₁.union (hP₁_finite.isClosed_biUnion fun _ _ => isClosed_closure)
  have hB₂ : IsClosed B₂ := h₂.union (hP₂_finite.isClosed_biUnion fun _ _ => isClosed_closure)
  have hcov : (univ : Set S) ⊆ B₁ ∪ B₂ := by
    intro x _
    by_cases hx : x ∈ X₁ ∪ X₂
    · rcases hx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · have hxU : x ∉ N.U := fun h => hx (hN h)
      obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
      have hrP : r ∈ P := by
        refine ⟨hr, (hreg r hr).resolve_left fun h => hx (h hxr)⟩
      by_cases h : (closure r ∩ X₁).Nonempty
      · exact Or.inl (Or.inr (mem_biUnion (show r ∈ P₁ from ⟨hrP, h⟩) (subset_closure hxr)))
      · exact Or.inr (Or.inr (mem_biUnion (show r ∈ P₂ from ⟨hrP, h⟩) (subset_closure hxr)))
  obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp isPreconnected_univ _ _ hB₁ hB₂ hcov
    (by obtain ⟨x, hx⟩ := hne₁; exact ⟨x, mem_univ x, Or.inl hx⟩)
    (by obtain ⟨x, hx⟩ := hne₂; exact ⟨x, mem_univ x, Or.inl hx⟩)
  rcases hz₁ with hz₁ | hz₁
  · rcases hz₂ with hz₂ | hz₂
    · exact absurd hz₂ (disjoint_left.mp hd hz₁)
    · obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hz₂
      exact absurd ⟨z, hzq, hz₁⟩ hq.2
  · obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hz₁
    rcases hz₂ with hz₂ | hz₂
    · exact ⟨q, hq.1.1, hq.1.2, hq.2, z, hzq, hz₂⟩
    · obtain ⟨q', hq', hzq'⟩ := mem_iUnion₂.mp hz₂
      by_cases hz : z ∈ X₁ ∪ X₂
      · rcases hz with hz | hz
        · exact absurd ⟨z, hzq', hz⟩ hq'.2
        · exact ⟨q, hq.1.1, hq.1.2, hq.2, z, hzq, hz⟩
      · have hzU : z ∉ N.U := fun h => hz (hN h)
        obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
        have hro := region_isOpen hr
        obtain ⟨a, har, haq⟩ := mem_closure_iff.mp hzq r hro hzr
        obtain ⟨b, hbr, hbq⟩ := mem_closure_iff.mp hzq' r hro hzr
        have e₁ : r = q := region_eq_of_mem hr hq.1.1 har haq
        have e₂ : r = q' := region_eq_of_mem hr hq'.1.1 hbr hbq
        have e₃ : q = q' := e₁.symm.trans e₂
        exact absurd (e₃ ▸ hq.2) hq'.2

omit [ConnectedSpace S] in
/-- A vertex of `N` in the closure of a region off `X₁ ∪ X₂`, in the part that the closure meets. -/
theorem exists_vertex_of_closure (hS : IsClosedSurface S) {N : Drawing S} {X₁ X₂ : Set S}
  (h₁ : IsClosed X₁)
    (h₂ : IsClosed X₂) (hd : Disjoint X₁ X₂) (hN : N.U ⊆ X₁ ∪ X₂) {q : Set S} (hq : q ∈ N.R)
    (hdq : Disjoint q (X₁ ∪ X₂)) (hne : (closure q ∩ X₁).Nonempty) : ∃ a ∈ N.V, a ∈ closure q
      ∧ a ∈ X₁ := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨z, hzq, hz⟩ := hne
  have hzU : z ∈ N.U := by
    by_contra hzU
    obtain ⟨r, hr, hzr⟩ := exists_region_of_notMem hzU
    obtain ⟨a, har, haq⟩ := mem_closure_iff.mp hzq r (region_isOpen hr) hzr
    have e : r = q := region_eq_of_mem hr hq har haq
    exact disjoint_left.mp hdq (e ▸ hzr) (Or.inl hz)
  by_cases hzV : z ∈ N.V
  · exact ⟨z, hzV, hzq, hz⟩
  obtain ⟨e, he, hze⟩ := N.exists_edge_of_mem hzU hzV
  have hes : e ⊆ closure q := edge_subset_closure_of_incident hS he hq ⟨z, hze, hzq⟩
  have hcl : closure e ⊆ closure q := closure_minimal hes isClosed_closure
  have hp : IsPreconnected (closure e) := (he.2.2.1.isConnected.isPreconnected).closure
  have hsub : closure e ⊆ X₁ ∪ X₂ := (N.closure_subset_U he).trans hN
  have hin : closure e ⊆ X₁ := by
    intro x hx
    by_contra hxn
    obtain ⟨w, -, hw₁, hw₂⟩ := isPreconnected_closed_iff.mp hp _ _ h₁ h₂ hsub ⟨z, subset_closure
      hze, hz⟩
      ⟨x, hx, (hsub hx).resolve_left hxn⟩
    exact disjoint_left.mp hd hw₁ hw₂
  rcases N.edge_cond e he with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
  · have hu : u ∈ closure e ∩ N.V := hcap ▸ mem_insert u _
    exact ⟨u, hu.2, hcl hu.1, hin hu.1⟩
  · have hu : u ∈ closure e ∩ N.V := hcap ▸ rfl
    exact ⟨u, hu.2, hcl hu.1, hin hu.1⟩

omit [ConnectedSpace S] in
/-- A path from a vertex in the closure of a region into the region. -/
theorem exists_path_into_region (hS : IsClosedSurface S) (N : Drawing S) {x : S}
  (hx : x ∈ N.V) {p : Set S}
    (hp : p ∈ N.R) (hxp : x ∈ closure p) :
    ∃ g : I → S, Continuous g ∧ g 0 = x ∧ ∀ t, 0 < t → g t ∈ p := by
  classical
  have : T2Space S := hS.2.1
  have : Nonempty S := ⟨x⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar N
  by_cases hne : (halfEdges N γ x).Nonempty
  · exact exists_access hS N hγ hx hne hp hxp
  -- `x` is an isolated vertex.
  have hoff : ∀ f ∈ N.E, x ∉ closure f := by
    intro f hf hxf
    obtain ⟨c, hc⟩ := exists_end_eq hγ hf hx hxf
    exact hne ⟨(f, c), hf, hc⟩
  have hcl : IsClosed ((N.V \ {x}) ∪ ⋃ e ∈ N.E, closure e) :=
    (N.finite_V.subset sdiff_subset).isClosed.union
      (N.finite_edges.isClosed_biUnion fun _ _ => isClosed_closure)
  have hxO : x ∈ ((N.V \ {x}) ∪ ⋃ e ∈ N.E, closure e)ᶜ := by
    rintro (h | h)
    · exact h.2 rfl
    · obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp h
      exact hoff f hf hxf
  obtain ⟨Z, hZ, hxZ, hZO, hZc, -⟩ := exists_punctured_nbhd hS hcl.isOpen_compl hxO
  have hdis : Disjoint (Z \ {x}) N.U := by
    refine disjoint_left.mpr ?_
    rintro y ⟨hyZ, hyx⟩ hyU
    rw [N.U_eq] at hyU
    rcases hyU with h | h
    · exact hZO hyZ (Or.inl ⟨h, hyx⟩)
    · exact hZO hyZ (Or.inr h)
  obtain ⟨y, hyZ, hyp⟩ := mem_closure_iff.mp hxp Z hZ hxZ
  have hyx : y ≠ x := fun h => by
    have := region_subset hp hyp
    exact this (N.V_subset_U (h ▸ hx))
  have hsub : Z \ {x} ⊆ p := subset_region hp hZc hdis ⟨hyZ, hyx⟩ hyp
  obtain ⟨g, hg, h0, ht⟩ := exists_path_from_point hS hZ hxZ
  exact ⟨g, hg, h0, fun t h => hsub (ht t h)⟩

/-- **A line joining the two parts of `X`**, off `X` and off the finite set `Y`, between vertices of
`N`. -/
theorem exists_bridge (hS : IsClosedSurface S) {N : Drawing S} {X₁ X₂ Y : Set S} (h₁ : IsClosed X₁)
    (h₂ : IsClosed X₂) (hd : Disjoint X₁ X₂) (hN : N.U ⊆ X₁ ∪ X₂) (hne₁ : X₁.Nonempty)
      (hne₂ : X₂.Nonempty)
    (hreg : ∀ q ∈ N.R, q ⊆ X₁ ∪ X₂ ∨ Disjoint q (X₁ ∪ X₂)) (hY : Y.Finite) (hXY : Disjoint
      (X₁ ∪ X₂) Y) :
    ∃ e : I → S, Continuous e ∧ Function.Injective e ∧ e 0 ∈ N.V ∧ e 1 ∈ N.V ∧ e 0 ∈ X₁ ∧ e 1 ∈ X₂ ∧
      ∀ t, t ≠ 0 → t ≠ 1 → e t ∉ X₁ ∪ X₂ ∧ e t ∉ Y := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨q, hq, hdq, hc₁, hc₂⟩ := exists_region_between hS h₁ h₂ hd hN hne₁ hne₂ hreg
  obtain ⟨a, haV, haq, haX⟩ := exists_vertex_of_closure hS h₁ h₂ hd hN hq hdq hc₁
  have hN' : N.U ⊆ X₂ ∪ X₁ := by rwa [union_comm]
  obtain ⟨b, hbV, hbq, hbX⟩ := exists_vertex_of_closure hS h₂ h₁ hd.symm hN' hq
    (by rwa [union_comm]) hc₂
  have hab : a ≠ b := fun h => disjoint_left.mp hd haX (h ▸ hbX)
  have hqo := region_isOpen hq
  have hq₀ : IsPathConnected (q \ Y) := by
    refine isPathConnected_of_isOpen hS (hqo.sdiff hY.isClosed) (isPreconnected_sdiff_finite hS hqo
      ?_ hY) ?_
    · exact region_isPreconnected hq
    · obtain ⟨g, hg, h0, ht⟩ := exists_path_into_region hS N haV hq haq
      obtain ⟨u, hu, -, hs⟩ := exists_pos_le hg hY.isClosed.isOpen_compl
        (h0 ▸ disjoint_left.mp hXY (Or.inl haX)) one_pos
      exact ⟨g u, ht u hu, hs u le_rfl⟩
  -- Paths from `a` and `b` into `q - Y`.
  have hinto : ∀ {x : S}, x ∈ N.V → x ∈ closure q → x ∉ Y → ∃ g : I → S, Continuous g ∧ g 0 = x ∧
      ∀ t, 0 < t → g t ∈ q \ Y := by
    intro x hxV hxq hxY
    obtain ⟨g, hg, h0, ht⟩ := exists_path_into_region hS N hxV hq hxq
    obtain ⟨u, hu, -, hs⟩ := exists_pos_le hg hY.isClosed.isOpen_compl (h0 ▸ hxY) one_pos
    refine ⟨fun t => g (t * u), hg.comp (by fun_prop), by simpa using h0, fun t ht₀ => ?_⟩
    have hp : 0 < t * u := show (0 : ℝ) < t.1 * u.1 from mul_pos ht₀ hu
    exact ⟨ht _ hp, hs _ (unitInterval.mul_le_right)⟩
  obtain ⟨g₁, hg₁, h₁0, ht₁⟩ := hinto haV haq (disjoint_left.mp hXY (Or.inl haX))
  obtain ⟨g₂, hg₂, h₂0, ht₂⟩ := hinto hbV hbq (disjoint_left.mp hXY (Or.inr hbX))
  have haq' : a ∉ q \ Y := fun h => disjoint_left.mp hdq h.1 (Or.inl haX)
  obtain ⟨e, he, hi, he0, he1, hin, -⟩ := exists_chord hq₀ hab haq' hg₁ hg₂ h₁0 h₂0 ht₁ ht₂
  refine ⟨e, he, hi, he0 ▸ haV, he1 ▸ hbV, he0 ▸ haX, he1 ▸ hbX, fun t h0' h1' => ?_⟩
  have := hin t h0' h1'
  exact ⟨disjoint_left.mp hdq this.1, this.2⟩

theorem ncard_image_lt {α β : Type*} {A : Set α} {φ φ' : α → β} (hA : A.Finite)
    (hmono : ∀ v ∈ A, ∀ w ∈ A, φ v = φ w → φ' v = φ' w) {a b : α} (ha : a ∈ A) (hb : b ∈ A)
    (hne : φ a ≠ φ b) (heq : φ' a = φ' b) : (φ' '' A).ncard < (φ '' A).ncard := by
  classical
  have : Nonempty α := ⟨a⟩
  let B : Set β := φ '' A \ {φ b}
  have hBf : B.Finite := (hA.image φ).subset sdiff_subset
  choose! ρ hρ using (fun c (hc : c ∈ B) => (show ∃ v ∈ A, φ v = c from hc.1))
  have hsub : φ' '' A ⊆ (φ' ∘ ρ) '' B := by
    rintro _ ⟨v, hv, rfl⟩
    by_cases h : φ v = φ b
    · refine ⟨φ a, ⟨⟨a, ha, rfl⟩, hne⟩, ?_⟩
      have h₁ := hρ (φ a) ⟨⟨a, ha, rfl⟩, hne⟩
      rw [Function.comp, hmono _ h₁.1 _ ha h₁.2, heq, hmono _ hv _ hb h]
    · have hc : φ v ∈ B := ⟨⟨v, hv, rfl⟩, h⟩
      refine ⟨φ v, hc, ?_⟩
      exact hmono _ (hρ _ hc).1 _ hv (hρ _ hc).2
  calc (φ' '' A).ncard ≤ ((φ' ∘ ρ) '' B).ncard := ncard_le_ncard hsub (hBf.image _)
    _ ≤ B.ncard := ncard_image_le hBf
    _ < (φ '' A).ncard := ncard_sdiff_singleton_lt_of_mem ⟨b, hb, rfl⟩ (hA.image φ)

omit [ConnectedSpace S] in
/-- A connected closed locally arc-connected set is path-connected. -/
theorem isPathConnected_of_locallyArc {X : Set S} (hl : IsLocallyArcConnected X)
  (hp : IsPreconnected X)
    (hne : X.Nonempty) : IsPathConnected X := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hstep : ∀ z ∈ X, ∃ A : Set S, IsOpen A ∧ z ∈ A ∧ ∀ y ∈ X ∩ A, JoinedIn X z y := by
    intro z hz
    obtain ⟨A, -, hzA, hA, harc⟩ := hl z hz univ isOpen_univ (mem_univ z)
    refine ⟨A, hA, hzA, fun y hy => ?_⟩
    by_cases hyz : z = y
    · exact hyz ▸ JoinedIn.refl hz
    obtain ⟨L, hL, hline⟩ := harc z ⟨hz, hzA⟩ y hy hyz
    obtain ⟨f, h0, h1⟩ := hline
    have hc : Continuous fun t => (f t).1 := continuous_subtype_val.comp f.continuous
    exact ⟨⟨⟨fun t => (f t).1, hc⟩, h0, h1⟩, fun t => (hL (f t).2).1⟩
  let J : Set S := {y | y ∈ X ∧ JoinedIn X x y}
  choose! B hBo hBm hBj using hstep
  have hsub : X ⊆ J := by
    have hcov : X ⊆ (⋃ z ∈ J, B z) ∪ (⋃ z ∈ X \ J, B z) := by
      intro z hz
      by_cases hzJ : z ∈ J
      · exact Or.inl (mem_biUnion hzJ (hBm z hz))
      · exact Or.inr (mem_biUnion ⟨hz, hzJ⟩ (hBm z hz))
    have hdis : X ∩ ((⋃ z ∈ J, B z) ∩ (⋃ z ∈ X \ J, B z)) = ∅ := by
      refine subset_empty_iff.mp ?_
      rintro y ⟨hy, h₁, h₂⟩
      obtain ⟨z, hzJ, hyz⟩ := mem_iUnion₂.mp h₁
      obtain ⟨z', hz', hyz'⟩ := mem_iUnion₂.mp h₂
      exact hz'.2 ⟨hz'.1, (hzJ.2.trans (hBj z hzJ.1 y ⟨hy, hyz⟩)).trans
        (hBj z' hz'.1 y ⟨hy, hyz'⟩).symm⟩
    have hopen₁ : IsOpen (⋃ z ∈ J, B z) := isOpen_biUnion fun z hz => hBo z hz.1
    have hopen₂ : IsOpen (⋃ z ∈ X \ J, B z) := isOpen_biUnion fun z hz => hBo z hz.1
    rcases isPreconnected_iff_subset_of_disjoint.mp hp _ _ hopen₁ hopen₂ hcov hdis with h | h
    · intro y hy
      obtain ⟨z, hzJ, hyz⟩ := mem_iUnion₂.mp (h hy)
      exact ⟨hy, hzJ.2.trans (hBj z hzJ.1 y ⟨hy, hyz⟩)⟩
    · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (h hx)
      exact absurd ⟨hz.1, (hBj z hz.1 x ⟨hx, hxz⟩).symm⟩ hz.2
  exact ⟨x, hx, fun _ hy => (hsub hy).2⟩

omit [ConnectedSpace S] in
/-- In a sphere, a closed connected set other than the sphere lies in an open disc: take an `O`-arc
off
the set. -/
theorem exists_openDisc_of_sphere (hS : IsClosedSurface S) (hsph : IsSphere S) {X : Set S}
  (hXc : IsClosed X)
    (hXp : IsPreconnected X) (hu : X ≠ univ) : ∃ A, IsOpenDisc A ∧ X ⊆ A := by
  have : T2Space S := hS.2.1
  obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem X).mp hu
  obtain ⟨D, D', hD, -, -, -, hDX, -⟩ := exists_closedDisc_nbhd hS hXc.isOpen_compl hz
  obtain ⟨F, hF⟩ : ∃ F, F = discBd D := ⟨_, rfl⟩
  have hFO : IsOArc F := hF ▸ IsClosedDisc.isOArc_discBd hD
  have hFX : Disjoint X F := disjoint_left.mpr fun x hx hxF =>
    hDX (discBd_subset D (hF ▸ hxF)) hx
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, -⟩ := sphere_disc S hsph F hFO
  have hint₁ : IsOpen (Δ₁ \ discBd Δ₁) := (isOpenDisc_interior hS hΔ₁).1
  have hint₂ : IsOpen (Δ₂ \ discBd Δ₂) := (isOpenDisc_interior hS hΔ₂).1
  have hdis : Disjoint (Δ₁ \ discBd Δ₁) (Δ₂ \ discBd Δ₂) := disjoint_left.mpr fun x h₁ h₂ =>
    h₁.2 (by rw [hb₁, ← hcap]; exact ⟨h₁.1, h₂.1⟩)
  have hcover : X ⊆ (Δ₁ \ discBd Δ₁) ∪ (Δ₂ \ discBd Δ₂) := fun x hx => by
    have hxF : x ∉ F := disjoint_left.mp hFX hx
    have hxu : x ∈ Δ₁ ∪ Δ₂ := hcup ▸ mem_univ x
    rcases hxu with h' | h'
    · exact Or.inl ⟨h', by rwa [hb₁]⟩
    · exact Or.inr ⟨h', by rwa [hb₂]⟩
  rcases hXp.subset_or_subset hint₁ hint₂ hdis hcover with h' | h'
  · exact ⟨_, isOpenDisc_interior hS hΔ₁, h'⟩
  · exact ⟨_, isOpenDisc_interior hS hΔ₂, h'⟩

/-- (7.5) for a connected set. -/
theorem closedDisc_of_connected (hS : IsClosedSurface S) {Y X : Set S} (hY : Y.Finite)
    {N : Drawing S} (hXc : IsClosed X) (hNX : N.U ⊆ X) (hfr : frontier X ⊆ N.U) (hu : X ≠ univ)
    (hXY : Disjoint X Y) (hall : ∀ F : Set S, F ⊆ X → IsOArc F → IsNullHomotopicOArcIn (univ \ Y) F)
    (hp : IsPreconnected X) (hne : X.Nonempty) : ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ univ \ Y ∧ X ⊆ Δ := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hK : CompactSpace S := hS.1
  have hn : IsGammaNice N X := isGammaNice_of_frontier (Drawing.IsSubdrawing.refl N) hNX hfr
  have hl := (isSolid_of_nice hS hXc hn).1
  have hW : IsOpen (univ \ Y) := isOpen_univ.sdiff hY.isClosed
  have hXW : X ⊆ univ \ Y := fun x hx => ⟨mem_univ x, disjoint_left.mp hXY hx⟩
  have hf := flat_of_null_oArcs hS hXc hn hXW hall
  obtain ⟨A, hXA, hAW, h | h⟩ := exists_open_around hS hW hXW hXc hl
    (isPathConnected_of_locallyArc hl hp hne) hf
  · obtain ⟨A', hA', hXA'⟩ := exists_openDisc_of_sphere hS h.1 hXc hp hu
    obtain ⟨Δ, hΔ, -, hXΔ⟩ := exists_closedDisc_of_isCompact hA' hXc.isCompact hXA'
    exact ⟨Δ, hΔ, (subset_univ _).trans (h.2 ▸ hAW), hXΔ⟩
  · obtain ⟨Δ, hΔ, hΔA, hXΔ⟩ := exists_closedDisc_of_isCompact h hXc.isCompact hXA
    exact ⟨Δ, hΔ, hΔA.trans hAW, hXΔ⟩

/-- The induction of (7.5): join the components of `X`. -/
theorem closedDisc_of_invariant (hS : IsClosedSurface S) {Y : Set S} (hY : Y.Finite)
    (n : ℕ) : ∀ (N : Drawing S) (X : Set S), IsClosed X → N.U ⊆ X → frontier X ⊆ N.U → X ≠ univ
      → Disjoint X Y →
      (∀ F : Set S, F ⊆ X → IsOArc F → IsNullHomotopicOArcIn (univ \ Y) F) → X.Nonempty →
      (connectedComponentIn X '' N.V).ncard = n → ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ univ \ Y ∧ X ⊆ Δ := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N X hXc hNX hfr hu hXY hall hne hn
    by_cases hp : IsPreconnected X
    · exact closedDisc_of_connected hS hY hXc hNX hfr hu hXY hall hp hne
    -- Split `X` into two closed parts.
    obtain ⟨t₁, t₂, ht₁, ht₂, hcov, hm₁, hm₂, hdis⟩ : ∃ t₁ t₂ : Set S, IsClosed t₁ ∧ IsClosed t₂ ∧
        X ⊆ t₁ ∪ t₂ ∧ (X ∩ t₁).Nonempty ∧ (X ∩ t₂).Nonempty ∧ ¬ (X ∩ (t₁ ∩ t₂)).Nonempty := by
      by_contra hno
      push Not at hno
      exact hp (isPreconnected_closed_iff.mpr fun t t' h₁ h₂ h₃ h₄ h₅ => hno t t' h₁ h₂ h₃ h₄ h₅)
    let X₁ := X ∩ t₁
    let X₂ := X ∩ t₂
    have hX₁ : IsClosed X₁ := hXc.inter ht₁
    have hX₂ : IsClosed X₂ := hXc.inter ht₂
    have hd : Disjoint X₁ X₂ := disjoint_left.mpr fun x h₁ h₂ => hdis ⟨x, h₁.1, h₁.2, h₂.2⟩
    have hXe : X₁ ∪ X₂ = X := by
      ext x
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        rcases hcov h with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
    have hreg : ∀ q ∈ N.R, q ⊆ X₁ ∪ X₂ ∨ Disjoint q (X₁ ∪ X₂) := by
      intro q hq
      rw [hXe]
      have hqU : Disjoint q N.U := disjoint_left.mpr fun x hx => region_subset hq hx
      have hsplit : q ⊆ interior X ∪ Xᶜ := by
        intro x hx
        by_cases hxX : x ∈ X
        · refine Or.inl ?_
          by_contra hint
          exact disjoint_left.mp hqU hx (hfr ⟨subset_closure hxX, hint⟩)
        · exact Or.inr hxX
      rcases (region_isPreconnected hq).subset_or_subset isOpen_interior hXc.isOpen_compl
        (disjoint_left.mpr fun x h₁ h₂ => h₂ (interior_subset h₁)) hsplit with h | h
      · exact Or.inl (h.trans interior_subset)
      · exact Or.inr (disjoint_left.mpr fun x hx hxX => h hx hxX)
    obtain ⟨e, he, hi, h0V, h1V, h0, h1, hin⟩ := exists_bridge hS hX₁ hX₂ hd
      (hXe ▸ hNX) hm₁ hm₂ hreg hY (hXe ▸ hXY)
    have hline : IsLineWithEnds (range e) (e 0) (e 1) := isLine_range he hi
    have hab : e 0 ≠ e 1 := fun h => disjoint_left.mp hd h0 (h ▸ h1)
    have hmeet : N.U ∩ (lineDrawing hline hab).U ⊆ N.V ∩ (lineDrawing hline hab).V := by
      rintro _ ⟨hx, t, rfl⟩
      by_cases ht0 : t = 0
      · subst ht0
        exact ⟨h0V, Or.inl rfl⟩
      by_cases ht1 : t = 1
      · subst ht1
        exact ⟨h1V, Or.inr rfl⟩
      exact absurd (hXe ▸ hNX hx) (hin t ht0 ht1).1
    let N' := N.glue (lineDrawing hline hab) hmeet
    let X' := X ∪ range e
    have hX'c : IsClosed X' := hXc.union (isCompact_range he).isClosed
    have hNU' : N'.U = N.U ∪ range e := rfl
    have hNV' : N'.V = N.V := by
      refine subset_antisymm ?_ subset_union_left
      rintro x (h | rfl | rfl)
      · exact h
      · exact h0V
      · exact h1V
    have hnotS : X' ≠ univ := by
      obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem X).mp hu
      obtain ⟨y, hyO, hyU⟩ := exists_notMem_U (Γ := N') hS hXc.isOpen_compl ⟨z, hz⟩
      refine (ne_univ_iff_exists_notMem _).mpr ⟨y, ?_⟩
      rintro (h | ⟨t, rfl⟩)
      · exact hyO h
      · exact hyU (Or.inr ⟨t, rfl⟩)
    have hX'Y : Disjoint X' Y := by
      refine disjoint_left.mpr ?_
      rintro _ (h | ⟨t, rfl⟩)
      · exact disjoint_left.mp hXY h
      · by_cases ht0 : t = 0
        · subst ht0
          exact disjoint_left.mp hXY (hXe ▸ Or.inl h0)
        by_cases ht1 : t = 1
        · subst ht1
          exact disjoint_left.mp hXY (hXe ▸ Or.inr h1)
        exact (hin t ht0 ht1).2
    have hall' : ∀ F : Set S, F ⊆ X' → IsOArc F → IsNullHomotopicOArcIn (univ \ Y) F := by
      intro F hF hO
      refine hall F ?_ hO
      rw [← hXe]
      refine oArc_subset_of_bridge hX₁ hX₂ hd he hi h0 h1 (fun t h₁' h₂' => (hin t h₁' h₂').1) hO ?_
      rwa [hXe]
    have hlt : (connectedComponentIn X' '' N'.V).ncard < n := by
      rw [← hn, hNV']
      refine ncard_image_lt N.finite_V ?_ h0V h1V ?_ ?_
      · intro v hv w hw h
        have hvX : v ∈ X := hNX (N.V_subset_U hv)
        have hwc : w ∈ connectedComponentIn X v := h ▸ mem_connectedComponentIn (hNX
          (N.V_subset_U hw))
        have hsub : connectedComponentIn X v ⊆ connectedComponentIn X' v :=
          isPreconnected_connectedComponentIn.subset_connectedComponentIn
            (mem_connectedComponentIn hvX) (connectedComponentIn_subset _ _ |>.trans
              subset_union_left)
        exact (connectedComponentIn_eq (hsub hwc))
      · intro h
        have hb : e 1 ∈ connectedComponentIn X (e 0) := h ▸ mem_connectedComponentIn
          (hXe ▸ Or.inr h1)
        have hin₁ : connectedComponentIn X (e 0) ⊆ X₁ := by
          intro x hx
          by_contra hxn
          have hsub : connectedComponentIn X (e 0) ⊆ X₁ ∪ X₂ :=
            hXe ▸ connectedComponentIn_subset _ _
          obtain ⟨w, -, hw₁, hw₂⟩ := isPreconnected_closed_iff.mp
            isPreconnected_connectedComponentIn _ _ hX₁ hX₂
            hsub ⟨_, mem_connectedComponentIn (hXe ▸ Or.inl h0), h0⟩ ⟨x, hx,
              (hsub hx).resolve_left hxn⟩
          exact disjoint_left.mp hd hw₁ hw₂
        exact disjoint_left.mp hd (hin₁ hb) h1
      · exact connectedComponentIn_eq ((isPreconnected_range he).subset_connectedComponentIn
          (mem_range_self 0) subset_union_right (mem_range_self 1))
    obtain ⟨Δ, hΔ, hΔY, hsub⟩ := ih _ hlt N' X' hX'c
      (by rw [hNU']; exact union_subset_union_left _ hNX)
      ((frontier_union_subset _ _).trans (union_subset
        ((inter_subset_left.trans hfr).trans subset_union_left)
        ((inter_subset_right.trans (frontier_subset_closure.trans
          (isCompact_range he).isClosed.closure_eq.subset)).trans subset_union_right)))
      hnotS hX'Y hall' (hne.mono subset_union_left) rfl
    exact ⟨Δ, hΔ, hΔY, subset_union_left.trans hsub⟩

/-- **(7.5)** of Graph Minors XI (page 94): "If $\Sigma$ is connected, $X \subseteq \Sigma$ is
closed and nice and $X \ne \Sigma$, and $Y
\subseteq \Sigma$ is finite, and $X \cap Y = \emptyset$, and every $O$-arc in $X$ is
null-homotopic in $\Sigma - Y$, then there is a closed disc $\Delta \subseteq \Sigma - Y$
with $X \subseteq \Delta$." -/
theorem theorem_7_5_proof (hS : IsClosedSurface S) {X Y : Set S} (hXc : IsClosed X)
    (hXn : IsNice X) (hu : X ≠ univ) (hY : Y.Finite) (hXY : Disjoint X Y)
    (hall : ∀ F : Set S, F ⊆ X → IsOArc F → IsNullHomotopicOArcIn (univ \ Y) F) :
    ∃ Δ, IsClosedDisc Δ ∧ Δ ⊆ univ \ Y ∧ X ⊆ Δ := by
  have : T2Space S := hS.2.1
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  by_cases hne : X.Nonempty
  · obtain ⟨Γ, hΓ⟩ := hXn
    have hU := frontier_interSet hS hXc hΓ
    exact closedDisc_of_invariant hS hY _ _ X hXc (hU.subset.trans hXc.frontier_subset)
      hU.symm.subset hu hXY
      hall hne rfl
  · -- For the empty set, take a small disc off `Y`.
    obtain ⟨x⟩ : Nonempty S := inferInstance
    obtain ⟨D, D', hD, -, -, -, -, -⟩ := exists_closedDisc_nbhd hS isOpen_univ (mem_univ x)
    obtain ⟨z, -, hz⟩ := (infinite_of_isOArc (IsClosedDisc.isOArc_discBd hD)).exists_notMem_finite
      hY
    obtain ⟨E, E', hE, -, -, -, hEO, -⟩ := exists_closedDisc_nbhd hS hY.isClosed.isOpen_compl hz
    exact ⟨E, hE, fun y hy => ⟨mem_univ y, hEO hy⟩, by
      rw [not_nonempty_iff_eq_empty.mp hne]
      exact empty_subset _⟩

end Surface

end GraphMinor.GM11
