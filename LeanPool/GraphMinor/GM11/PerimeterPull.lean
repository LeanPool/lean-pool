/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.SphereRegion
public import LeanPool.GraphMinor.GM11.GlueDiscs
public import LeanPool.GraphMinor.Surface.Jordan
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Carrying a collar and a walk from a sphere back to a surface

An open disc in a surface collapses onto a sphere minus a point. `pull_collar` carries a collar back
from
the sphere to the surface, after shrinking it to miss the point at infinity, and `walk_pull` carries
a walk.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S S' : Type u} [TopologicalSpace S] [TopologicalSpace S']

/-- A walk moves along a map of the vertices and the edges. -/
theorem walk_pull {D : Drawing S'} {Γ : Drawing S} {g : S' → S} {G : Set S' → Set S}
    (hl : ∀ e x y, D.toGraph.IsLink e x y → Γ.toGraph.IsLink (G e) (g x) (g y))
    (hV : ∀ v ∈ D.V, g v ∈ Γ.V) (hinj : ∀ e ∈ D.E, InjOn g e) (himg : ∀ e ∈ D.E, g '' e = G e)
    {φ : ℝ → S'} {u v : S'} (W : GraphWalk D.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn D φ a b W →
      ∃ W' : GraphWalk Γ.toGraph (g u) (g v), RunsAlongOn Γ (g ∘ φ) a b W' ∧
        W'.edges = W.edges.map G := by
  induction W with
  | nil hv =>
    intro a b h
    exact ⟨.nil (hV _ hv), ⟨h.1, congrArg g h.2⟩, rfl⟩
  | @cons x y w e hlink rest ih =>
    rintro a b ⟨c, hac, hu, hi, him, hrest⟩
    obtain ⟨W', hW', hedges⟩ := ih hrest
    have he : e ∈ D.E := hlink.1
    refine ⟨.cons (hl _ _ _ hlink) W', ⟨c, hac, congrArg g hu, ?_, ?_, hW'⟩, ?_⟩
    · rintro s hs t ht hst
      exact hi hs ht (hinj e he (him ▸ mem_image_of_mem φ hs) (him ▸ mem_image_of_mem φ ht) hst)
    · rw [← himg e he, ← him, image_comp]
    · simp [GraphWalk.edges, hedges]

/-- A small height at which a collar still misses a point. -/
theorem exists_height (h : C(Circle × I, S')) [T1Space S'] {z₀ : S'} (hz : ∀ z, h (z, 0) ≠ z₀) :
    ∃ ε : I, 0 < ε ∧ ∀ z t, t ≤ ε → h (z, t) ≠ z₀ := by
  have hK : IsCompact (h ⁻¹' {z₀}) := (isClosed_singleton.preimage h.continuous).isCompact
  have hT : IsCompact (Prod.snd '' (h ⁻¹' {z₀})) := hK.image continuous_snd
  have h0 : (0 : I) ∉ Prod.snd '' (h ⁻¹' {z₀}) := by
    rintro ⟨⟨z, t⟩, hp, rfl⟩
    exact hz z hp
  have hnhds : (Prod.snd '' (h ⁻¹' {z₀}))ᶜ ∈ 𝓝 (0 : I) := hT.isClosed.isOpen_compl.mem_nhds h0
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let ε : I := ⟨min (δ / 2) 1, by positivity, min_le_right _ _⟩
  refine ⟨ε, ?_, ?_⟩
  · change (0 : ℝ) < min (δ / 2) 1
    positivity
  · intro z t ht hzt
    have ht' : t.1 ≤ min (δ / 2) 1 := ht
    have hmem : t ∈ Metric.ball (0 : I) δ := by
      rw [Metric.mem_ball, Subtype.dist_eq, Icc.coe_zero, Real.dist_eq, sub_zero,
        abs_of_nonneg t.2.1]
      linarith [min_le_left (δ / 2) (1 : ℝ)]
    exact hball hmem ⟨(z, t), hzt, rfl⟩

/-- A shorter collar still fills a neighbourhood. -/
theorem isOpen_shrink [T2Space S'] {Q : Set S'} (_hQ : IsClosed Q) (h : C(Circle × I, S'))
    (hinj : InjOn h {p | 0 < p.2}) (hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ Q)
    (hbot : ∀ z, h (z, 0) ∈ Q) (hop : IsOpen (Q ∪ h '' {p | p.2 < 1})) {ε : I} (hε : 0 < ε) :
    IsOpen (Q ∪ h '' {p | p.2 < ε}) := by
  have hK : IsClosed (Q ∪ h '' {p | p.2 < 1})ᶜ := hop.isClosed_compl
  have hT : IsClosed (h '' {p | ε ≤ p.2}) :=
    ((isClosed_le continuous_const continuous_snd).isCompact.image h.continuous).isClosed
  have heq : (Q ∪ h '' {p | p.2 < ε})ᶜ = (Q ∪ h '' {p | p.2 < 1})ᶜ ∪ h '' {p | ε ≤ p.2} := by
    ext y
    constructor
    · intro hy
      by_cases hin : y ∈ Q ∪ h '' {p | p.2 < 1}
      · refine Or.inr ?_
        rcases hin with hin | ⟨p, hp, rfl⟩
        · exact (hy (Or.inl hin)).elim
        · refine ⟨p, ?_, rfl⟩
          by_contra hlt
          exact hy (Or.inr ⟨p, not_le.mp (show ¬ ε ≤ p.2 from hlt), rfl⟩)
      · exact Or.inl hin
    · rintro (hy | ⟨p, hp, rfl⟩) (hin | ⟨q, hq, hqe⟩)
      · exact hy (Or.inl hin)
      · exact hy (Or.inr ⟨q, lt_of_lt_of_le hq (unitInterval.le_one ε), hqe⟩)
      · exact hoff p (lt_of_lt_of_le hε hp) hin
      · have hp0 : 0 < p.2 := lt_of_lt_of_le hε hp
        by_cases hq0 : 0 < q.2
        · have := hinj hq0 hp0 hqe
          subst this
          exact not_le.mpr (show q.2 < ε from hq) hp
        · have ht0 : q.2 = 0 := le_antisymm (not_lt.mp hq0) (unitInterval.nonneg _)
          have hq' : q = (q.1, 0) := Prod.ext rfl ht0
          exact hoff p hp0 (hqe ▸ hq' ▸ hbot q.1)
  rw [← isClosed_compl_iff, heq]
  exact hK.union hT

/-- **Carrying a collar back from the sphere.** The map `f` collapses `S` to `S'`, and it has an
inverse
`g` away from the point `z₀`. A collar of `Q` in `S'` gives a collar of `f⁻¹(Q)` in `S`. -/
theorem pull_collar [T2Space S'] {f : S → S'} {g : S' → S} {z₀ : S'}
  (hfc : Continuous f)
    (hgc : ∀ y, y ≠ z₀ → ContinuousAt g y) (hgf : ∀ x, f x ≠ z₀ → g (f x) = x)
    (hfg : ∀ y, y ≠ z₀ → f (g y) = y) {Q : Set S'} (hQ : IsClosed Q) (hz₀ : z₀ ∉ Q)
    (h' : C(Circle × I, S')) (hinj : InjOn h' {p | 0 < p.2}) (hoff : ∀ p : Circle × I, 0 < p.2
      → h' p ∉ Q)
    (hbot : ∀ z, h' (z, 0) ∈ Q) (hop : IsOpen (Q ∪ h' '' {p | p.2 < 1})) :
    ∃ h : C(Circle × I, S), InjOn h {p | 0 < p.2} ∧ (∀ p : Circle × I, 0 < p.2 → f (h p) ∉ Q) ∧
      (∀ z, h (z, 0) = g (h' (z, 0))) ∧ IsOpen (f ⁻¹' Q ∪ h '' {p | p.2 < 1}) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_height h' (z₀ := z₀) fun z h => hz₀ (h ▸ hbot z)
  have hmul : ∀ t : I, ε * t ≤ ε := fun t => unitInterval.mul_le_left
  have hne : ∀ p : Circle × I, h' (p.1, ε * p.2) ≠ z₀ := fun p => hsmall _ _ (hmul _)
  let k : Circle × I → Circle × I := fun p => (p.1, ε * p.2)
  have hkc : Continuous k := by fun_prop
  let h : C(Circle × I, S) := ⟨fun p => g (h' (k p)), by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hk : ContinuousAt (fun p => h' (k p)) p := (h'.continuous.comp hkc).continuousAt
    exact ContinuousAt.comp (f := fun p => h' (k p)) (hgc _ (hne p)) hk⟩
  have hfh : ∀ p, f (h p) = h' (k p) := fun p => hfg _ (hne p)
  have hpos : ∀ {t : I}, 0 < t → 0 < ε * t := fun {t} ht => by
    change (0 : ℝ) < ε.1 * t.1
    exact mul_pos hε ht
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · rintro ⟨z, t⟩ ht ⟨z', t'⟩ ht' heq
    have h₁ : h' (k (z, t)) = h' (k (z', t')) := by rw [← hfh, ← hfh, heq]
    have h₂ := hinj (hpos ht) (hpos ht') h₁
    have h₃ : z = z' := congrArg Prod.fst h₂
    have h₄ : ε * t = ε * t' := congrArg Prod.snd h₂
    have h₅ : ε.1 * t.1 = ε.1 * t'.1 := congrArg Subtype.val h₄
    have h₆ : t.1 = t'.1 := mul_left_cancel₀ (ne_of_gt hε) h₅
    exact Prod.ext h₃ (Subtype.ext h₆)
  · intro p hp
    rw [hfh]
    exact hoff _ (hpos hp)
  · intro z
    change g (h' (z, ε * 0)) = _
    rw [mul_zero]
  · have hshrink := isOpen_shrink hQ h' hinj hoff hbot hop hε
    have heq : f ⁻¹' Q ∪ h '' {p | p.2 < 1} = f ⁻¹' (Q ∪ h' '' {p | p.2 < ε}) := by
      ext x
      constructor
      · rintro (hx | ⟨p, hp, rfl⟩)
        · exact Or.inl hx
        · refine Or.inr ⟨k p, ?_, (hfh p).symm⟩
          have hp' : p.2.1 < 1 := hp
          change ε.1 * p.2.1 < ε.1
          have hε' : (0 : ℝ) < ε.1 := hε
          nlinarith
      · rintro (hx | ⟨p, hp, hpe⟩)
        · exact Or.inl hx
        · refine Or.inr ?_
          have hp' : p.2.1 < ε.1 := hp
          have hε' : (0 : ℝ) < ε.1 := hε
          let t : I := ⟨p.2.1 / ε.1, div_nonneg p.2.2.1 hε'.le, (div_le_one hε').mpr hp'.le⟩
          have hk : k (p.1, t) = p := by
            refine Prod.ext rfl (Subtype.ext ?_)
            change ε.1 * (p.2.1 / ε.1) = p.2.1
            field_simp
          refine ⟨(p.1, t), (div_lt_one hε').mpr hp', ?_⟩
          change g (h' (k (p.1, t))) = x
          rw [hk, hpe]
          refine hgf x fun hxz => ?_
          have hsm : p.2 ≤ ε := le_of_lt hp'
          exact hsmall p.1 p.2 hsm (by rw [show (p.1, p.2) = p from rfl, hpe, hxz])
    rw [heq]
    exact hshrink.preimage hfc

/-- A sphere is a connected closed surface. -/
theorem IsSphere.isClosedSurface (hS : IsSphere S) : IsClosedSurface S ∧ ConnectedSpace S := by
  obtain ⟨e⟩ := id hS
  have hT2 : T2Space S := e.symm.t2Space
  refine ⟨⟨e.symm.compactSpace, hT2, fun x => ?_⟩, e.symm.surjective.connectedSpace
    e.symm.continuous⟩
  obtain ⟨w, hw⟩ : ∃ w : OnePoint EuclideanPlane, w ≠ e x := by
    by_cases h : e x = OnePoint.infty
    · refine ⟨((0 : EuclideanPlane) : OnePoint EuclideanPlane), ?_⟩
      rw [h]
      exact OnePoint.coe_ne_infty _
    · exact ⟨_, Ne.symm h⟩
  obtain ⟨h, hh⟩ := exists_homeomorph_onePoint w
  let T : S ≃ₜ OnePoint EuclideanPlane := e.trans h
  have hTx : T x ≠ OnePoint.infty := fun hx => hw (h.injective (hh.trans hx.symm))
  have hemb : IsOpenEmbedding (fun z : EuclideanPlane => T.symm (z : OnePoint EuclideanPlane)) :=
    T.symm.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  obtain ⟨z, hz⟩ : ∃ z : EuclideanPlane, (z : OnePoint EuclideanPlane) = T x :=
    OnePoint.ne_infty_iff_exists.mp hTx
  refine ⟨range fun z : EuclideanPlane => T.symm (z : OnePoint EuclideanPlane), hemb.isOpen_range,
    ⟨z, by simp [hz]⟩, ?_⟩
  have hb : OpenUnitDisc ≃ₜ EuclideanPlane := (Homeomorph.unitBall (E := EuclideanPlane)).symm
  exact ⟨(hemb.isEmbedding.toHomeomorph.symm).trans hb.symm⟩

end GraphMinor.GM11
