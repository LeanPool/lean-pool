/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section4b
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.Disc

/-!
# The two sides of an edge

Graph Minors XI uses without comment that an edge of a drawing has two sides. This file proves it.

The first lemma, `exists_half_nbhd`, looks at a point `p` of the boundary of a closed disc `Δ`,
and a closed set `B` missing `p`. Near `p`, the interior of `Δ` lies in one connected set that
avoids `B`, because in the unit disc a small ball around a boundary point cuts the open disc in a
convex set. The second, `exists_closedDisc_nbhd`, gives small closed discs around a point of a
closed
surface. The main result is `exists_edge_sides`. It cuts a small disc around `p ∈ e` along a piece
of `e`, by `DiscIArcStatement`, and applies the first lemma to the two halves.
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Near a point `p` of the boundary of a closed disc `Δ`, the interior of `Δ` lies in one connected
set that avoids a given closed set `B` missing `p`. Each point of `bd(Δ)` near `p` is a limit of
that connected set. -/
theorem exists_half_nbhd {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {X : Set S} (hX : IsClosed X) {p : S} (hp : p ∈ discBd Δ) (hpX : p ∉ X) :
    ∃ A W : Set S, IsOpen W ∧ p ∈ W ∧ IsPreconnected A ∧ A ⊆ Δ ∧ Disjoint A (discBd Δ) ∧
      Disjoint A X ∧ (W ∩ Δ) \ discBd Δ ⊆ A ∧ W ∩ discBd Δ ⊆ closure A := by
  obtain ⟨φ⟩ := hΔ
  have hbd := disc_boundary Δ φ
  rw [hbd] at hp ⊢
  obtain ⟨c, hc, rfl⟩ := hp
  let f : ClosedUnitDisc → S := fun x => (φ x).1
  have hf : Continuous f := continuous_subtype_val.comp φ.continuous
  have hfinj : Function.Injective f := fun x y h => φ.injective (Subtype.ext h)
  have hopen : IsOpen {x : ClosedUnitDisc | f x ∉ X} := (hX.preimage hf).isOpen_compl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen c hpX
  -- The set of points of the closed disc in the small ball, and its image in `S`.
  let N : Set ClosedUnitDisc := {x | dist x c < δ}
  have hNopen : IsOpen N := isOpen_lt (continuous_id.dist continuous_const) continuous_const
  have hfopen : IsOpen ((fun y : Δ => (φ.symm y)) ⁻¹' N) := hNopen.preimage φ.symm.continuous
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp hfopen
  have hmemW : ∀ x : ClosedUnitDisc, f x ∈ W ↔ x ∈ N := by
    intro x
    have := congrArg (fun T : Set Δ => φ x ∈ T) hWeq
    simpa [f] using this
  let O : Set EuclideanPlane := Metric.ball (c : EuclideanPlane) δ ∩ OpenUnitDisc
  have hOconv : Convex ℝ O := (convex_ball _ _).inter convex_openUnitDisc
  have hOsub : O ⊆ ClosedUnitDisc := fun x hx => Metric.ball_subset_closedBall hx.2
  let O' : Set ClosedUnitDisc := Subtype.val ⁻¹' O
  have hO'conn : IsPreconnected O' := by
    have hemb : IsInducing (Subtype.val : ClosedUnitDisc → EuclideanPlane) := IsInducing.subtypeVal
    refine hemb.isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hOsub]
    exact hOconv.isPreconnected
  refine ⟨f '' O', W, hW, ?_, hO'conn.image _ hf.continuousOn, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hmemW c).mpr (by simp [N, hδ])
  · rintro _ ⟨x, -, rfl⟩
    exact (φ x).2
  · refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have heq : y = x := hfinj hxy
    subst heq
    have h₁ : ‖y.1‖ < 1 := by simpa [OpenUnitDisc] using hx.2
    have h₂ : ‖y.1‖ = 1 := by simpa [UnitCircle] using hy
    linarith
  · refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ hxX
    exact hball (show dist x c < δ from hx.1) hxX
  · rintro q ⟨⟨hqW, hqΔ⟩, hqbd⟩
    let y : ClosedUnitDisc := φ.symm ⟨q, hqΔ⟩
    have hqy : f y = q := by simp [f, y]
    rw [← hqy] at hqW hqbd
    have hyN := (hmemW y).mp hqW
    refine ⟨y, ⟨hyN, ?_⟩, hqy⟩
    have hle : ‖y.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using y.2
    have hne : ‖y.1‖ ≠ 1 := by
      intro h
      exact hqbd ⟨y, by simpa [UnitCircle] using h, rfl⟩
    simpa [OpenUnitDisc] using lt_of_le_of_ne hle hne
  · rintro _ ⟨hqW, x, hx, rfl⟩
    have hxN := (hmemW x).mp hqW
    refine image_closure_subset_closure_image hf ⟨x, ?_, rfl⟩
    -- `x` is a limit of points of the open disc inside the small ball.
    rw [closure_subtype]
    have hxc : (x : EuclideanPlane) ∈ Metric.ball (c : EuclideanPlane) δ := hxN
    have hcl : (x : EuclideanPlane) ∈ closure (OpenUnitDisc : Set EuclideanPlane) := by
      have : closure (OpenUnitDisc : Set EuclideanPlane) = ClosedUnitDisc :=
        closure_ball _ one_ne_zero
      rw [this]
      exact x.2
    have := Metric.isOpen_ball.inter_closure ⟨hxc, hcl⟩
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hOsub]

/-- Small closed discs around a point of a closed surface. Inside any open set around `p` there is a
closed disc with an open core around `p`, whose boundary is the rest of the disc. -/
theorem exists_closedDisc_nbhd (hS : IsClosedSurface S) {O : Set S}
    (hO : IsOpen O) {p : S} (hp : p ∈ O) :
    ∃ D D' : Set S, IsClosedDisc D ∧ IsOpen D' ∧ p ∈ D' ∧ D' ⊆ D ∧ D ⊆ O ∧ D \ D' = discBd D := by
  obtain ⟨V, hV, hpV, ⟨h⟩⟩ := hS.2.2 p
  have : T2Space S := hS.2.1
  let c : OpenUnitDisc := h ⟨p, hpV⟩
  -- The open set in the plane that corresponds to `O ∩ V`.
  let P : Set OpenUnitDisc := {x | (h.symm x).1 ∈ O}
  have hP : IsOpen P := hO.preimage (continuous_subtype_val.comp h.symm.continuous)
  have hP' : IsOpen (Subtype.val '' P : Set EuclideanPlane) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap _ hP
  have hc : (c : EuclideanPlane) ∈ (Subtype.val '' P : Set EuclideanPlane) :=
    ⟨c, by simpa [P, c] using hp, rfl⟩
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hP' _ hc
  let ρ : ℝ := ρ' / 2
  have hρ : 0 < ρ := half_pos hρ'
  have hclosed : Metric.closedBall (c : EuclideanPlane) ρ ⊆ Subtype.val '' P :=
    (Metric.closedBall_subset_ball (half_lt_self hρ')).trans hball
  have hto : Metric.closedBall (c : EuclideanPlane) ρ ⊆ OpenUnitDisc := by
    rintro x hx
    obtain ⟨y, -, rfl⟩ := hclosed hx
    exact y.2
  -- The map from the unit disc to the plane.
  let g : EuclideanPlane → EuclideanPlane := fun x => (c : EuclideanPlane) + ρ • x
  have hg : Continuous g := by fun_prop
  have hgin : ∀ x : EuclideanPlane, g x ∈ Metric.closedBall (c : EuclideanPlane) ρ ↔
      x ∈ ClosedUnitDisc := by
    intro x
    simp only [g, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, ClosedUnitDisc,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨fun h' => le_of_mul_le_mul_left (by simpa using h') hρ,
      fun h' => by nlinarith⟩
  have hgball : ∀ x : EuclideanPlane, g x ∈ Metric.ball (c : EuclideanPlane) ρ ↔
      x ∈ OpenUnitDisc := by
    intro x
    simp only [g, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, OpenUnitDisc,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    exact ⟨fun h' => lt_of_mul_lt_mul_left (by simpa using h') hρ.le,
      fun h' => by nlinarith⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    have := add_left_cancel hxy
    exact smul_right_injective _ hρ.ne' this
  let k : ClosedUnitDisc → S := fun x =>
    (h.symm ⟨g x.1, hto ((hgin x.1).mpr x.2)⟩).1
  have hk : Continuous k := by
    refine continuous_subtype_val.comp (h.symm.continuous.comp ?_)
    exact Continuous.subtype_mk (hg.comp continuous_subtype_val) _
  have hkinj : Function.Injective k := by
    intro x y hxy
    have h₁ := h.symm.injective (Subtype.ext hxy)
    exact Subtype.ext (hginj (congrArg Subtype.val h₁))
  have : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanPlane) 1)
  -- `D` is the image of `k`, and `D'` the image of the open ball.
  let D : Set S := range k
  have hk' : Continuous (rangeFactorization k) := hk.rangeFactorization
  let E : ClosedUnitDisc ≃ₜ D :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective k hkinj) hk'
  have hEv : ∀ x, (E x : S) = k x := fun _ => rfl
  let D' : Set S := Subtype.val '' ((fun y : V => (h y : EuclideanPlane)) ⁻¹'
    Metric.ball (c : EuclideanPlane) ρ)
  have hD'open : IsOpen D' := by
    refine hV.isOpenEmbedding_subtypeVal.isOpenMap _ (Metric.isOpen_ball.preimage ?_)
    exact continuous_subtype_val.comp h.continuous
  have hkD' : ∀ x : ClosedUnitDisc, k x ∈ D' ↔ x.1 ∈ OpenUnitDisc := by
    intro x
    rw [← hgball]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = h.symm ⟨g x.1, hto ((hgin x.1).mpr x.2)⟩ := Subtype.ext hyx
      rw [this] at hy
      simpa using hy
    · intro hx
      refine ⟨h.symm ⟨g x.1, hto ((hgin x.1).mpr x.2)⟩, ?_, rfl⟩
      simpa using hx
  have hbd := disc_boundary D E
  refine ⟨D, D', ⟨E⟩, hD'open, ⟨⟨p, hpV⟩, by simp [c, hρ], rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (h y : EuclideanPlane) ∈ Metric.ball (c : EuclideanPlane) ρ := hy
    let x : EuclideanPlane := ρ⁻¹ • ((h y : EuclideanPlane) - c)
    have hgx : g x = (h y : EuclideanPlane) := by
      simp only [g, x, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
    have hxm : x ∈ OpenUnitDisc := by
      rw [← hgball, hgx]
      exact hy'
    refine ⟨⟨x, Metric.ball_subset_closedBall hxm⟩, ?_⟩
    have : (⟨g x, hto ((hgin x).mpr (Metric.ball_subset_closedBall hxm))⟩ : OpenUnitDisc) = h y :=
      Subtype.ext hgx
    simp only [k, this, Homeomorph.symm_apply_apply]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hclosed ((hgin x.1).mpr x.2)
    have : y = ⟨g x.1, hto ((hgin x.1).mpr x.2)⟩ := Subtype.ext hyx
    rw [this] at hy
    exact hy
  · rw [hbd]
    ext q
    constructor
    · rintro ⟨⟨x, rfl⟩, hq⟩
      refine ⟨x, ?_, rfl⟩
      have hle : ‖x.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using x.2
      have hne : ¬ ‖x.1‖ < 1 := fun hlt => hq ((hkD' x).mpr (by simpa [OpenUnitDisc] using hlt))
      have : ‖x.1‖ = 1 := le_antisymm hle (not_lt.mp hne)
      simpa [UnitCircle] using this
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, rfl⟩, fun hin => ?_⟩
      have h₁ : ‖x.1‖ < 1 := by simpa [OpenUnitDisc] using (hkD' x).mp hin
      have h₂ : ‖x.1‖ = 1 := by simpa [UnitCircle] using hx
      linarith

variable [T2Space S]

/-- `U(Γ)` minus an edge is closed. -/
theorem isClosed_U_sdiff_edge (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) : IsClosed (Γ.U \ e) := by
  have hEq : Γ.U \ e = Γ.V ∪ ⋃ f ∈ Γ.E \ {e}, closure f := by
    ext x
    constructor
    · rintro ⟨hx, hxe⟩
      by_cases hxV : x ∈ Γ.V
      · exact Or.inl hxV
      rw [Γ.U_eq] at hx
      rcases hx with hx | hx
      · exact absurd hx hxV
      obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp hx
      refine Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, ?_⟩, hxf⟩)
      rintro rfl
      exact hxe (by rw [← Γ.closure_diff_V hf]; exact ⟨hxf, hxV⟩)
    · rintro (hx | hx)
      · exact ⟨Γ.V_subset_U hx, fun hxe => (he.2.1 hxe).2 hx⟩
      · obtain ⟨f, ⟨hf, hfe⟩, hxf⟩ := mem_iUnion₂.mp hx
        refine ⟨Γ.closure_subset_U hf hxf, fun hxe => ?_⟩
        have hxV : x ∉ Γ.V := (he.2.1 hxe).2
        have hxf' : x ∈ f := by rw [← Γ.closure_diff_V hf]; exact ⟨hxf, hxV⟩
        exact hfe (Γ.edge_eq_of_mem hf he hxf' hxe)
  rw [hEq]
  exact Γ.finite_V.isClosed.union
    ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)

omit [T2Space S] in
/-- Every edge is the image of the open unit interval under a map of the closed interval that is
injective on the open interval and sends both ends to vertices. For a loop the map runs once around
the circle, starting at the vertex. -/
theorem exists_edge_param (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) :
    ∃ γ : unitInterval → S, Continuous γ ∧ γ 0 ∈ Γ.V ∧ γ 1 ∈ Γ.V ∧ InjOn γ (Ioo 0 1) ∧
      γ '' Ioo 0 1 = e := by
  rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, f, hf0, hf1⟩ | ⟨u, hcap, ⟨g⟩⟩
  · have hu : u ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    have hv : v ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    have hinj : Function.Injective fun t => (f t).1 := fun x y h => f.injective (Subtype.ext h)
    refine ⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous, ?_, ?_,
      hinj.injOn, ?_⟩
    · simpa [hf0] using hu.2
    · simpa [hf1] using hv.2
    · have hE := Γ.closure_diff_V he
      ext x
      constructor
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        refine hE.subset ⟨(f t).2, fun hx => ?_⟩
        have hx' : (f t).1 ∈ closure e ∩ Γ.V := ⟨(f t).2, hx⟩
        rw [hcap] at hx'
        rcases hx' with hx' | hx'
        · exact ht0.ne' (f.injective (Subtype.ext (hx'.trans hf0.symm)))
        · exact ht1.ne (f.injective (Subtype.ext ((mem_singleton_iff.mp hx').trans hf1.symm)))
      · intro hx
        have hx' : x ∈ closure e \ Γ.V := by rw [hE]; exact hx
        refine ⟨f.symm ⟨x, hx'.1⟩, ⟨?_, ?_⟩, by simp⟩
        · refine unitInterval.pos_iff_ne_zero.mpr fun h => hx'.2 ?_
          have : x = u := by
            have h₂ := congrArg (fun t => (f t).1) h
            simpa [hf0] using h₂
          exact this ▸ hu.2
        · refine unitInterval.lt_one_iff_ne_one.mpr fun h => hx'.2 ?_
          have : x = v := by
            have h₂ := congrArg (fun t => (f t).1) h
            simpa [hf1] using h₂
          exact this ▸ hv.2
  · have hu : u ∈ closure e ∩ Γ.V := by rw [hcap]; simp
    let z₀ : Circle := g.symm ⟨u, hu.1⟩
    let w : unitInterval → Circle := fun t => z₀ * Circle.exp (2 * Real.pi * t.1)
    have hw : Continuous w := by fun_prop
    have hw0 : w 0 = z₀ := by simp [w]
    have hw1 : w 1 = z₀ := by simp [w]
    have hg0 : (g z₀).1 = u := by simp [z₀]
    have hE := Γ.closure_diff_V he
    have hwinj : InjOn w (Ioo 0 1) := by
      have key : ∀ s t : unitInterval, s < t → t < 1 → 0 < s → w s ≠ w t := by
        intro s t hst ht _ h
        have h₁ : Circle.exp (2 * Real.pi * s.1) = Circle.exp (2 * Real.pi * t.1) :=
          mul_left_cancel h
        have hlt : (s : ℝ) < t := hst
        have ht1 : (t : ℝ) < 1 := ht
        have hs0 : (0 : ℝ) ≤ s := s.2.1
        have hpi := Real.pi_pos
        have hmono : 2 * Real.pi * (s : ℝ) < 2 * Real.pi * t :=
          mul_lt_mul_of_pos_left hlt (by positivity)
        have hb : 2 * Real.pi * (t : ℝ) - 2 * Real.pi * s < 2 * Real.pi := by nlinarith
        have := Circle.exp_injOn_Icc hb ⟨le_rfl, hmono.le⟩ ⟨hmono.le, le_rfl⟩ h₁
        exact hmono.ne this
      intro s hs t ht h
      rcases lt_trichotomy s t with hst | hst | hst
      · exact absurd h (key s t hst ht.2 hs.1)
      · exact hst
      · exact absurd h.symm (key t s hst hs.2 ht.1)
    refine ⟨fun t => (g (w t)).1, continuous_subtype_val.comp (g.continuous.comp hw), ?_, ?_, ?_,
      ?_⟩
    · simpa [hw0, hg0] using hu.2
    · simpa [hw1, hg0] using hu.2
    · exact fun s hs t ht h => hwinj hs ht (g.injective (Subtype.ext h))
    · ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine hE.subset ⟨(g (w t)).2, fun hx => ?_⟩
        have hx' : (g (w t)).1 ∈ closure e ∩ Γ.V := ⟨(g (w t)).2, hx⟩
        rw [hcap] at hx'
        have h₁ : w t = z₀ := g.injective (Subtype.ext (hx'.trans hg0.symm))
        -- `w t = w 0` with `0 < t < 1` is impossible, by the same computation.
        have h₂ : Circle.exp (2 * Real.pi * t.1) = Circle.exp 0 := by
          rw [Circle.exp_zero]
          exact mul_left_cancel (a := z₀) (by rw [mul_one]; exact h₁)
        have ht0 : (0 : ℝ) < t := ht.1
        have ht1 : (t : ℝ) < 1 := ht.2
        have hpi := Real.pi_pos
        have hb : 2 * Real.pi * (t : ℝ) - 0 < 2 * Real.pi := by nlinarith
        have hpos : 0 < 2 * Real.pi * (t : ℝ) := by positivity
        have := Circle.exp_injOn_Icc hb ⟨hpos.le, le_rfl⟩ ⟨le_rfl, hpos.le⟩ h₂
        exact hpos.ne' this
      · intro hx
        have hx' : x ∈ closure e \ Γ.V := by rw [hE]; exact hx
        let y : Circle := g.symm ⟨x, hx'.1⟩
        let q : Circle := z₀⁻¹ * y
        have hq : z₀ * q = y := by simp [q]
        have hq1 : q ≠ 1 := by
          intro h
          rw [h, mul_one] at hq
          have h' : (⟨u, hu.1⟩ : closure e) = ⟨x, hx'.1⟩ := g.symm.injective hq
          have hux : u = x := congrArg Subtype.val h'
          exact hx'.2 (hux ▸ hu.2)
        -- The angle of `q`, moved into `(0, 2π)`.
        have hθ : ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ Circle.exp θ = q := by
          have harg : Complex.arg q ≠ 0 := fun h => hq1 (Circle.arg_eq_zero.mp h)
          have hexp := Circle.exp_arg q
          have h₁ := Complex.neg_pi_lt_arg (q : ℂ)
          have h₂ := Complex.arg_le_pi (q : ℂ)
          have hpi := Real.pi_pos
          rcases lt_or_gt_of_ne harg with h | h
          · exact ⟨Complex.arg q + 2 * Real.pi, by linarith, by linarith,
              by rw [Circle.exp_add_two_pi, hexp]⟩
          · exact ⟨Complex.arg q, h, by linarith, hexp⟩
        obtain ⟨θ, hθ₀, hθ₁, hθq⟩ := hθ
        have hpi := Real.pi_pos
        have htm : θ / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by positivity, (div_le_one (by positivity)).mpr hθ₁.le⟩
        refine ⟨⟨θ / (2 * Real.pi), htm⟩, ⟨?_, ?_⟩, ?_⟩
        · exact Subtype.mk_lt_mk.mpr (by positivity)
        · exact Subtype.mk_lt_mk.mpr ((div_lt_one (by positivity)).mpr hθ₁)
        · have hmul : 2 * Real.pi * (θ / (2 * Real.pi)) = θ := by field_simp
          have hwt : w ⟨θ / (2 * Real.pi), htm⟩ = y := by
            simp only [w, hmul, hθq, hq]
          simp only [hwt, y, Homeomorph.apply_symm_apply]

/-- A piece `γ([a, b])` of an edge around `γ t₀`, as a chord of a small closed disc `D`. -/
theorem exists_edge_piece (hS : IsClosedSurface S)
    (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {γ : unitInterval → S} (hγ : Continuous γ)
    (hγ0 : γ 0 ∈ Γ.V) (hγ1 : γ 1 ∈ Γ.V) (hinj : InjOn γ (Ioo 0 1)) (hγe : γ '' Ioo 0 1 = e)
    {t₀ : unitInterval} (ht₀ : t₀ ∈ Ioo (0 : unitInterval) 1) {O : Set S} (hO : IsOpen O)
    (hpO : γ t₀ ∈ O) (hOdis : Disjoint O (Γ.U \ e)) :
    ∃ (D D' : Set S) (a b : unitInterval), IsClosedDisc D ∧ IsOpen D' ∧ γ t₀ ∈ D' ∧ D' ⊆ D ∧ D ⊆ O ∧
      D \ D' = discBd D ∧ a < t₀ ∧ t₀ < b ∧ Icc a b ⊆ Ioo 0 1 ∧ (∀ t, a < t → t < b → γ t ∈ D') ∧
      IsLineWithEnds (γ '' Icc a b) (γ a) (γ b) ∧ γ '' Icc a b ⊆ D ∧
      (γ '' Icc a b) ∩ discBd D = {γ a, γ b} ∧ γ a ≠ γ b := by
  have hpe : γ t₀ ∈ e := hγe ▸ mem_image_of_mem γ ht₀
  obtain ⟨D, D', hD, hD', hpD', hD'D, hDO, hbdD⟩ :=
    exists_closedDisc_nbhd hS hO hpO
  have hVout : ∀ x ∈ Γ.V, x ∉ D := fun x hx hxD =>
    disjoint_left.mp hOdis (hDO hxD) ⟨Γ.V_subset_U hx, fun hxe => (he.2.1 hxe).2 hx⟩
  have hDclosed : IsClosed D := hD.isClosed
  obtain ⟨ht₀0, ht₀1⟩ := ht₀
  -- The last exit `a` before `t₀`, and the first exit `b` after it.
  have hC₁ : IsCompact {t : unitInterval | t ≤ t₀ ∧ γ t ∉ D'} :=
    (isClosed_Iic.inter (hD'.isClosed_compl.preimage hγ)).isCompact
  have hC₂ : IsCompact {t : unitInterval | t₀ ≤ t ∧ γ t ∉ D'} :=
    (isClosed_Ici.inter (hD'.isClosed_compl.preimage hγ)).isCompact
  obtain ⟨a, ⟨hat, hagamma⟩, hamax⟩ := hC₁.exists_isGreatest
    ⟨0, unitInterval.nonneg _, fun h => hVout _ hγ0 (hD'D h)⟩
  obtain ⟨b, ⟨htb, hbgamma⟩, hbmin⟩ := hC₂.exists_isLeast
    ⟨1, unitInterval.le_one _, fun h => hVout _ hγ1 (hD'D h)⟩
  have hat' : a < t₀ := lt_of_le_of_ne hat fun h => hagamma (h ▸ hpD')
  have htb' : t₀ < b := lt_of_le_of_ne htb fun h => hbgamma (h ▸ hpD')
  have hIoo : ∀ t, a < t → t < b → γ t ∈ D' := by
    intro t h₁ h₂
    by_contra hcon
    rcases le_total t t₀ with h | h
    · exact absurd (hamax ⟨h, hcon⟩) (not_le.mpr h₁)
    · exact absurd (hbmin ⟨h, hcon⟩) (not_le.mpr h₂)
  have hab : a < b := hat'.trans htb'
  -- The ends of the piece lie in `D`, so they are not vertices.
  have hclosure : ∀ t ∈ closure (Ioo a b), γ t ∈ D := by
    intro t ht
    have h₁ : γ t ∈ closure (γ '' Ioo a b) := image_closure_subset_closure_image hγ ⟨t, ht, rfl⟩
    have h₂ : γ '' Ioo a b ⊆ D := by
      rintro _ ⟨u, hu, rfl⟩
      exact hD'D (hIoo u hu.1 hu.2)
    exact hDclosed.closure_subset_iff.mpr h₂ h₁
  have hamem : γ a ∈ D := hclosure a (by rw [closure_Ioo hab.ne]; exact ⟨le_rfl, hab.le⟩)
  have hbmem : γ b ∈ D := hclosure b (by rw [closure_Ioo hab.ne]; exact ⟨hab.le, le_rfl⟩)
  have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h => hVout _ hγ0 (h ▸ hamem)
  have hb1 : b < 1 := unitInterval.lt_one_iff_ne_one.mpr fun h => hVout _ hγ1 (h ▸ hbmem)
  have hIcc : Icc a b ⊆ Ioo 0 1 := fun t ht => ⟨ha0.trans_le ht.1, ht.2.trans_lt hb1⟩
  -- The piece `F` of `e` from `γ a` to `γ b`.
  have habR : (a : ℝ) < b := hab
  have hρmem : ∀ u : unitInterval, (a : ℝ) + u.1 * (b - a) ∈ Set.Icc (0 : ℝ) 1 := by
    intro u
    have hu₀ := u.2.1
    have hu₁ := u.2.2
    have ha' := a.2.1
    have hb' := b.2.2
    constructor
    · have : 0 ≤ u.1 * ((b : ℝ) - a) := mul_nonneg hu₀ (by linarith)
      linarith
    · have : u.1 * ((b : ℝ) - a) ≤ 1 * ((b : ℝ) - a) :=
        mul_le_mul_of_nonneg_right hu₁ (by linarith)
      linarith
  let ρ : unitInterval → unitInterval := fun u => ⟨(a : ℝ) + u.1 * (b - a), hρmem u⟩
  have hρ : Continuous ρ := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  have hρIcc : ∀ u, ρ u ∈ Icc a b := by
    intro u
    have hu₀ := u.2.1
    have hu₁ := u.2.2
    constructor
    · have : 0 ≤ u.1 * ((b : ℝ) - a) := mul_nonneg hu₀ (by linarith)
      exact Subtype.mk_le_mk.mpr (by linarith)
    · have : u.1 * ((b : ℝ) - a) ≤ 1 * ((b : ℝ) - a) :=
        mul_le_mul_of_nonneg_right hu₁ (by linarith)
      exact Subtype.mk_le_mk.mpr (by linarith)
  have hρsurj : ∀ t ∈ Icc a b, ∃ u, ρ u = t := by
    intro t ht
    have ht₁ : (a : ℝ) ≤ t := ht.1
    have ht₂ : (t : ℝ) ≤ b := ht.2
    have hd : (0 : ℝ) < b - a := by linarith
    have hu : ((t : ℝ) - a) / (b - a) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩
    refine ⟨⟨_, hu⟩, Subtype.ext ?_⟩
    change (a : ℝ) + ((t : ℝ) - a) / (b - a) * (b - a) = t
    field_simp
    ring
  have hρ0 : ρ 0 = a := Subtype.ext (by simp [ρ])
  have hρ1 : ρ 1 = b := Subtype.ext (by simp [ρ])
  have hρinj : Function.Injective ρ := by
    intro u v h
    have h₁ : (a : ℝ) + u.1 * (b - a) = a + v.1 * (b - a) := congrArg Subtype.val h
    have hd : ((b : ℝ) - a) ≠ 0 := by linarith
    exact Subtype.ext (mul_right_cancel₀ hd (add_left_cancel h₁))
  let k : unitInterval → S := fun u => γ (ρ u)
  have hk : Continuous k := hγ.comp hρ
  have hkinj : Function.Injective k := fun u v h =>
    hρinj (hinj (hIcc (hρIcc u)) (hIcc (hρIcc v)) h)
  let F : Set S := range k
  have hFmem : ∀ x, x ∈ F ↔ ∃ t ∈ Icc a b, γ t = x := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨ρ u, hρIcc u, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨u, rfl⟩ := hρsurj t ht
      exact ⟨u, rfl⟩
  have hFline : IsLineWithEnds F (γ a) (γ b) := by
    refine ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective k hkinj)
      hk.rangeFactorization, ?_, ?_⟩
    · change k 0 = γ a
      simp [k, hρ0]
    · change k 1 = γ b
      simp [k, hρ1]
  have hFD : F ⊆ D := by
    rintro x hx
    obtain ⟨t, ht, rfl⟩ := (hFmem x).mp hx
    rcases eq_or_lt_of_le ht.1 with rfl | h₁
    · exact hamem
    rcases eq_or_lt_of_le ht.2 with rfl | h₂
    · exact hbmem
    exact hD'D (hIoo t h₁ h₂)
  have hst : γ a ≠ γ b := fun h => hab.ne (hinj (hIcc ⟨le_rfl, hab.le⟩) (hIcc ⟨hab.le, le_rfl⟩) h)
  have hFcap : F ∩ discBd D = {γ a, γ b} := by
    rw [← hbdD]
    ext x
    constructor
    · rintro ⟨hx, -, hxD'⟩
      obtain ⟨t, ht, rfl⟩ := (hFmem x).mp hx
      rcases eq_or_lt_of_le ht.1 with rfl | h₁
      · exact Or.inl rfl
      rcases eq_or_lt_of_le ht.2 with rfl | h₂
      · exact Or.inr rfl
      exact absurd (hIoo t h₁ h₂) hxD'
    · rintro (rfl | hx)
      · exact ⟨(hFmem _).mpr ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩, hamem, hagamma⟩
      · rw [mem_singleton_iff.mp hx]
        exact ⟨(hFmem _).mpr ⟨b, ⟨hab.le, le_rfl⟩, rfl⟩, hbmem, hbgamma⟩
  have hFeq : F = γ '' Icc a b := by
    ext x
    rw [hFmem]
    rfl
  rw [hFeq] at hFline hFD hFcap
  exact ⟨D, D', a, b, hD, hD', hpD', hD'D, hDO, hbdD, hat', htb', hIcc, hIoo, hFline, hFD, hFcap,
    hst⟩

/-- **Two sides of an edge, away from a closed set.** Let `p` be a point of an edge `e` of a drawing
in a
closed surface, and `Z` a closed set missing `p`. Then `p` has an open neighbourhood `W` that meets
`U(Γ)`
only in `e`, and `W - U(Γ)` lies in the union of two connected subsets of `Σ - (U(Γ) ∪ Z)`. Every
point of
`e` in `W` is a limit of both of them. -/
theorem exists_edge_sides_off (hS : IsClosedSurface S)
    (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {p : S} (hp : p ∈ e)
    {Z : Set S} (hZ : IsClosed Z) (hpZ : p ∉ Z) :
    ∃ W A₁ A₂ Δ₁ Δ₂ : Set S, IsOpen W ∧ p ∈ W ∧ W ∩ Γ.U ⊆ e ∧ W \ Γ.U ⊆ A₁ ∪ A₂ ∧
      IsPreconnected A₁ ∧ IsPreconnected A₂ ∧ Disjoint A₁ Γ.U ∧ Disjoint A₂ Γ.U ∧
      e ∩ W ⊆ closure A₁ ∧ e ∩ W ⊆ closure A₂ ∧ IsClosed Δ₁ ∧ IsClosed Δ₂ ∧ A₁ ⊆ Δ₁ ∧ A₂ ⊆ Δ₂ ∧
      W ⊆ Δ₁ ∪ Δ₂ ∧ Δ₁ ∩ Δ₂ ⊆ Γ.U ∧ Disjoint A₁ Z ∧ Disjoint A₂ Z := by
  obtain ⟨γ, hγ, hγ0, hγ1, hinj, hγe⟩ := exists_edge_param Γ he
  have hX₀ := isClosed_U_sdiff_edge Γ he
  have hpX₀ : p ∉ Γ.U \ e := fun h => h.2 hp
  obtain ⟨t₀, ht₀, rfl⟩ : p ∈ γ '' Ioo 0 1 := by rw [hγe]; exact hp
  obtain ⟨D, D', a, b, hD, hD', hpD', hD'D, -, hbdD, hat', htb', hIcc, hIoo, hFline, hFD, hFcap,
    hst⟩ :=
    exists_edge_piece hS Γ he hγ hγ0 hγ1 hinj hγe ht₀ hX₀.isOpen_compl hpX₀ disjoint_compl_left
  obtain ⟨ht₀0, ht₀1⟩ := ht₀
  have hat : a ≤ t₀ := hat'.le
  have htb : t₀ ≤ b := htb'.le
  set F : Set S := γ '' Icc a b with hF
  have hFmem : ∀ x, x ∈ F ↔ ∃ t ∈ Icc a b, γ t = x := fun x => Iff.rfl
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hΔ₁, hΔ₂, hunion, hmeet, hbd₁, hbd₂, -⟩ :=
    disc_iArc D F (γ a) (γ b) hD hFD hst hFline hFcap
  have hAsub : ∀ A ∈ componentsIn (discBd D \ {γ a, γ b}), A ⊆ discBd D := by
    rintro _ ⟨x, -, rfl⟩
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hA₁ : A₁ ⊆ discBd D := hAsub _ (by rw [hcomp]; simp)
  have hA₂ : A₂ ⊆ discBd D := hAsub _ (by rw [hcomp]; simp)
  have hFU : F ⊆ Γ.U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (hFmem x).mp hx
    have hmem : γ t ∈ e := by rw [← hγe]; exact ⟨t, hIcc ht, rfl⟩
    exact (he.2.1 hmem).1
  -- The closed set to avoid near `p`.
  let Y : Set S := D'ᶜ ∪ (Γ.U \ e) ∪ γ '' {t | t ≤ a ∨ b ≤ t} ∪ Z
  have hY : IsClosed Y := by
    refine ((hD'.isClosed_compl.union hX₀).union ?_).union hZ
    exact ((isClosed_Iic.union isClosed_Ici).isCompact.image hγ).isClosed
  have hpY : γ t₀ ∉ Y := by
    rintro (((h | h) | ⟨t, ht, hteq⟩) | h)
    · exact h hpD'
    · exact h.2 hp
    · have hpV : t ∈ Ioo (0 : unitInterval) 1 := by
        refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
        · rintro rfl
          exact (he.2.1 hp).2 (hteq ▸ hγ0)
        · rintro rfl
          exact (he.2.1 hp).2 (hteq ▸ hγ1)
      have := hinj hpV ⟨ht₀0, ht₀1⟩ hteq
      subst this
      rcases ht with h | h
      · exact absurd h (not_le.mpr hat')
      · exact absurd h (not_le.mpr htb')
    · exact hpZ h
  have hpF : γ t₀ ∈ F := (hFmem _).mpr ⟨t₀, ⟨hat, htb⟩, rfl⟩
  have hFsub : ∀ x ∈ e, x ∉ Y → x ∈ F := by
    intro x hx hxY
    obtain ⟨t, -, rfl⟩ : x ∈ γ '' Ioo 0 1 := by rw [hγe]; exact hx
    refine (hFmem _).mpr ⟨t, ?_, rfl⟩
    have hn : ¬ (t ≤ a ∨ b ≤ t) := fun h => hxY (Or.inl (Or.inr ⟨t, h, rfl⟩))
    push Not at hn
    exact ⟨hn.1.le, hn.2.le⟩
  have side : ∀ Δ A₀ : Set S, IsClosedDisc Δ → discBd Δ = A₀ ∪ F → A₀ ⊆ discBd D →
      ∃ A W : Set S, IsOpen W ∧ γ t₀ ∈ W ∧ IsPreconnected A ∧ A ⊆ Δ ∧ Disjoint A Γ.U ∧ Disjoint A Y
        ∧
        (∀ x ∈ W, x ∈ D' → x ∈ Δ → x ∉ Γ.U → x ∈ A) ∧
        (∀ x ∈ W, x ∈ e → x ∉ Y → x ∈ closure A) := by
    intro Δ A₀ hΔ hbdΔ hA₀
    have hpbd : γ t₀ ∈ discBd Δ := by rw [hbdΔ]; exact Or.inr hpF
    obtain ⟨A, W, hW, hpW, hconn, hAΔ, hAbd, hAY, hin, hcl⟩ :=
      exists_half_nbhd hΔ hY hpbd hpY
    refine ⟨A, W, hW, hpW, hconn, hAΔ, ?_, hAY, ?_, ?_⟩
    · refine disjoint_left.mpr fun x hxA hxU => ?_
      have hxY : x ∉ Y := disjoint_left.mp hAY hxA
      have hxe : x ∈ e := by
        by_contra hxe
        exact hxY (Or.inl (Or.inl (Or.inr ⟨hxU, hxe⟩)))
      refine disjoint_left.mp hAbd hxA ?_
      rw [hbdΔ]
      exact Or.inr (hFsub x hxe hxY)
    · intro x hxW hxD' hxΔ hxU
      refine hin ⟨⟨hxW, hxΔ⟩, ?_⟩
      rw [hbdΔ]
      rintro (h | h)
      · have hx' := hA₀ h
        rw [← hbdD] at hx'
        exact hx'.2 hxD'
      · exact hxU (hFU h)
    · intro x hxW hxe hxY
      refine hcl ⟨hxW, ?_⟩
      rw [hbdΔ]
      exact Or.inr (hFsub x hxe hxY)
  obtain ⟨S₁, W₁, hW₁, hpW₁, hconn₁, hs₁, hdis₁, hY₁, hin₁, hcl₁⟩ := side Δ₁ A₁ hΔ₁ hbd₁ hA₁
  obtain ⟨S₂, W₂, hW₂, hpW₂, hconn₂, hs₂, hdis₂, hY₂, hin₂, hcl₂⟩ := side Δ₂ A₂ hΔ₂ hbd₂ hA₂
  refine ⟨W₁ ∩ W₂ ∩ Yᶜ, S₁, S₂, Δ₁, Δ₂, (hW₁.inter hW₂).inter hY.isOpen_compl, ⟨⟨hpW₁, hpW₂⟩, hpY⟩,
    ?_, ?_, hconn₁, hconn₂, hdis₁, hdis₂, ?_, ?_, hΔ₁.isCompact.isClosed, hΔ₂.isCompact.isClosed,
      hs₁,
    hs₂, ?_, ?_, hY₁.mono_right subset_union_right, hY₂.mono_right subset_union_right⟩
  · rintro x ⟨⟨-, hxY⟩, hxU⟩
    by_contra hxe
    exact hxY (Or.inl (Or.inl (Or.inr ⟨hxU, hxe⟩)))
  · rintro x ⟨⟨⟨hx₁, hx₂⟩, hxY⟩, hxU⟩
    have hxD' : x ∈ D' := by
      by_contra h
      exact hxY (Or.inl (Or.inl (Or.inl h)))
    have hxD : x ∈ Δ₁ ∪ Δ₂ := by rw [hunion]; exact hD'D hxD'
    rcases hxD with h | h
    · exact Or.inl (hin₁ x hx₁ hxD' h hxU)
    · exact Or.inr (hin₂ x hx₂ hxD' h hxU)
  · rintro x ⟨hxe, ⟨hx₁, -⟩, hxY⟩
    exact hcl₁ x hx₁ hxe hxY
  · rintro x ⟨hxe, ⟨-, hx₂⟩, hxY⟩
    exact hcl₂ x hx₂ hxe hxY
  · rintro x ⟨-, hxY⟩
    have hxD' : x ∈ D' := by
      by_contra h
      exact hxY (Or.inl (Or.inl (Or.inl h)))
    rw [hunion]
    exact hD'D hxD'
  · rw [hmeet]
    exact hFU

/-- **Two sides of an edge.** Let `p` be a point of an edge `e` of a drawing in a closed surface.
Then `p` has an open neighbourhood `W` that meets `U(Γ)` only in `e`, and `W - U(Γ)` lies in the
union
of two connected subsets of `Σ - U(Γ)`. Every point of `e` in `W` is a limit of both of them. -/
theorem exists_edge_sides_split (hS : IsClosedSurface S)
    (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {p : S} (hp : p ∈ e) :
    ∃ W A₁ A₂ Δ₁ Δ₂ : Set S, IsOpen W ∧ p ∈ W ∧ W ∩ Γ.U ⊆ e ∧ W \ Γ.U ⊆ A₁ ∪ A₂ ∧
      IsPreconnected A₁ ∧ IsPreconnected A₂ ∧ Disjoint A₁ Γ.U ∧ Disjoint A₂ Γ.U ∧
      e ∩ W ⊆ closure A₁ ∧ e ∩ W ⊆ closure A₂ ∧ IsClosed Δ₁ ∧ IsClosed Δ₂ ∧ A₁ ⊆ Δ₁ ∧ A₂ ⊆ Δ₂ ∧
      W ⊆ Δ₁ ∪ Δ₂ ∧ Δ₁ ∩ Δ₂ ⊆ Γ.U := by
  obtain ⟨W, A₁, A₂, Δ₁, Δ₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆,
    -, -⟩ :=
    exists_edge_sides_off hS Γ he hp isClosed_empty (notMem_empty p)
  exact ⟨W, A₁, A₂, Δ₁, Δ₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆⟩

/-- The two sides of an edge near a point of the edge. -/
theorem exists_edge_sides (hS : IsClosedSurface S)
    (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {p : S} (hp : p ∈ e) :
    ∃ W A₁ A₂ : Set S, IsOpen W ∧ p ∈ W ∧ W ∩ Γ.U ⊆ e ∧ W \ Γ.U ⊆ A₁ ∪ A₂ ∧
      IsPreconnected A₁ ∧ IsPreconnected A₂ ∧ Disjoint A₁ Γ.U ∧ Disjoint A₂ Γ.U ∧
      e ∩ W ⊆ closure A₁ ∧ e ∩ W ⊆ closure A₂ := by
  obtain ⟨W, A₁, A₂, -, -, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, -⟩ :=
    exists_edge_sides_split hS Γ he hp
  exact ⟨W, A₁, A₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩

end GraphMinor.GM11
