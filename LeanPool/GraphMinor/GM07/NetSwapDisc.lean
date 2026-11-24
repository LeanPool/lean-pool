/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.Surface.DiscUnion

/-!
# A model for pasting two closed discs along boundary arcs

In the net exchange of VII (2.6), page 218, cutting along the
proper line gives two discs. Pasting the selected side to its
mate joins those discs along a boundary arc. Map each disc to
one half of the unit disc, sending the pasted arc to the same
diameter. This gives an explicit disc model, with exactly the
prescribed identifications between the two pieces.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

universe u v

variable {S : Type u} [TopologicalSpace S]

private theorem exists_pasting_half_coordinates {Δ : Set S} (hΔ : IsClosedDisc Δ) {ℓ : 𝕀 → S}
  (hℓ : Continuous ℓ)
    (hinj : Function.Injective ℓ) (hr : range ℓ ⊆ discBd Δ) {a e : 𝕀 → ℂ} (ha : IsArcMap a)
    (he : IsArcMap e) (h0 : a 0 = e 0) (h1 : a 1 = e 1)
    (hm : ∀ s t, a s = e t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ (p : S → ℂ) (q : ℂ → S), ContinuousOn p Δ ∧ ContinuousOn q (closedInner (side a e)) ∧
      MapsTo p Δ (closedInner (side a e)) ∧ MapsTo q (closedInner (side a e)) Δ ∧
      LeftInvOn q p Δ ∧ LeftInvOn p q (closedInner (side a e)) ∧ (∀ u, p (ℓ u) = e u) ∧
      discBd Δ = q '' side a e := by
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hrΔ : ∀ u, ℓ u ∈ Δ := fun u => discBd_subset Δ (hr ⟨u, rfl⟩)
  let c₀ : 𝕀 → ℂ := fun u => h (ℓ u)
  have hc₀ : IsArcMap c₀ := ⟨c.hc.comp_continuous hℓ hrΔ, fun u v huv =>
    hinj (c.gh.injOn (hrΔ u) (hrΔ v) huv)⟩
  have hsub : range c₀ ⊆ sphere 0 1 := by
    rintro _ ⟨u, rfl⟩
    rw [← c.bd]
    exact mem_image_of_mem h (hr ⟨u, rfl⟩)
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨d, hd, d0, d1, hu, hmd⟩ := exists_other_arc φ₀ hc₀ hsub
  obtain ⟨h₀, k₀, m, -, v2⟩ := exists_bdMatch_of_arcs hd hc₀ ha he d0.symm d1.symm h0.symm h1.symm
    (fun s t hst => (hmd t s hst.symm).imp And.symm And.symm) hm
  rw [union_comm (range d), hu] at m
  have hO : Nonempty (Circle ≃ₜ side a e) := oArc_of_two_arcs ha he h0 h1 hm
  obtain ⟨ψ, χ, m', hψ⟩ := exists_bdMatch_closedInner ⟨φ₀⟩ hO m
  rw [closedInner_sphere] at m'
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := id m'
  refine ⟨ψ ∘ h, g ∘ χ, n5.comp c.hc c.hm, c.gc.comp n6 n2, n1.comp c.hm, c.gm.comp n2, ?_, ?_, ?_,
    ?_⟩
  · intro x hx
    change g (χ (ψ (h x))) = x
    rw [n3 (c.hm hx)]
    exact c.gh hx
  · intro z hz
    change ψ (h (g (χ z))) = z
    rw [c.hg (n2 hz)]
    exact n4 hz
  · intro u
    change ψ (c₀ u) = e u
    rw [hψ (hsub ⟨u, rfl⟩), v2]
  · rw [← show h₀ '' sphere 0 1 = side a e from m.image_eq, ← hψ.image_eq, image_image]
    rw [← c.g_sphere]
    refine image_congr fun z hz => ?_
    change g z = g (χ (ψ z))
    rw [n3 (sphere_subset_closedBall hz)]

private noncomputable def diameter (u : 𝕀) : ℂ := ((2 * u.1 - 1 : ℝ) : ℂ)

private theorem isArcMap_diameter : IsArcMap diameter := by
  refine ⟨Complex.continuous_ofReal.comp (by fun_prop), fun u v h => ?_⟩
  have h1 : 2 * u.1 - 1 = 2 * v.1 - 1 := Complex.ofReal_injective h
  exact Subtype.ext (by linarith)

private theorem exists_cut_diameter : ∃ a b, IsCut (sphere (0 : ℂ) 1) a b diameter := by
  obtain ⟨φ₀⟩ := oArc_sphere
  refine exists_isCut φ₀ isArcMap_diameter ?_ ?_ ?_ ?_
  · intro h
    have h1 : 2 * (0 : ℝ) - 1 = 2 * 1 - 1 := Complex.ofReal_injective h
    norm_num at h1
  · rw [mem_sphere_zero_iff_norm, diameter, Complex.norm_real]
    simp
  · rw [mem_sphere_zero_iff_norm, diameter, Complex.norm_real]
    norm_num
  · intro t h0 h1
    rw [inner_sphere, mem_ball_zero_iff, diameter, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have h2 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
    have h3 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
    constructor <;> linarith


/-- The disc model for the pasting step in VII (2.6), page 218.
The images of the pieces cover the closed unit disc, and a
point of one piece equals a point of the other precisely at
the paired boundary parameters. -/
theorem exists_disc_pasting_model
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set X} {B : Set Y} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (f : 𝕀 → X) (g : 𝕀 → Y) (hf : IsArcMap f) (hg : IsArcMap g)
    (hfbd : range f ⊆ discBd A) (hgbd : range g ⊆ discBd B) :
    ∃ (p : X → ℂ) (q : Y → ℂ),
      ContinuousOn p A ∧ ContinuousOn q B ∧ InjOn p A ∧ InjOn q B ∧
      p '' A ∪ q '' B = closedBall 0 1 ∧
      (∀ x ∈ A, ∀ y ∈ B, p x = q y ↔ ∃ t, x = f t ∧ y = g t) ∧
      ∀ t, p (f t) = q (g t) := by
  obtain ⟨a, b, cut⟩ := exists_cut_diameter
  obtain ⟨p, p', hpc, hp'c, hpm, hp'm, hpi, hp'i, hpf, hpbd⟩ :=
    exists_pasting_half_coordinates hA hf.1 hf.2 hfbd cut.arc_a cut.arc_e
      cut.a_zero cut.a_one cut.a_eq_e
  obtain ⟨q, q', hqc, hq'c, hqm, hq'm, hqi, hq'i, hqg, hqbd⟩ :=
    exists_pasting_half_coordinates hB hg.1 hg.2 hgbd cut.arc_b cut.arc_e
      cut.b_zero cut.b_one cut.symm.a_eq_e
  obtain ⟨φ⟩ := oArc_sphere
  obtain ⟨hunion, -, -, hmeet, -, -⟩ := cut.closedInner_facts (isJordanParts φ)
  rw [closedInner_sphere] at hunion
  have hpimage : p '' A = closedInner (side a diameter) :=
    Subset.antisymm hpm.image_subset (fun z hz => ⟨p' z, hp'm hz, hp'i hz⟩)
  have hqimage : q '' B = closedInner (side b diameter) :=
    Subset.antisymm hqm.image_subset (fun z hz => ⟨q' z, hq'm hz, hq'i hz⟩)
  have hfA : ∀ t, f t ∈ A := fun t => discBd_subset A (hfbd ⟨t, rfl⟩)
  have hgB : ∀ t, g t ∈ B := fun t => discBd_subset B (hgbd ⟨t, rfl⟩)
  refine ⟨p, q, hpc, hqc, hpi.injOn, hqi.injOn, ?_, ?_, ?_⟩
  · rw [hpimage, hqimage]
    exact hunion
  · intro x hx y hy
    constructor
    · intro hxy
      have hm : p x ∈ closedInner (side a diameter) ∩ closedInner (side b diameter) :=
        ⟨hpm hx, hxy.symm ▸ hqm hy⟩
      obtain ⟨t, ht⟩ := hmeet hm
      refine ⟨t, hpi.injOn hx (hfA t) ?_, hqi.injOn hy (hgB t) ?_⟩
      · exact ht.symm.trans (hpf t).symm
      · exact hxy.symm.trans (ht.symm.trans (hqg t).symm)
    · rintro ⟨t, rfl, rfl⟩
      exact (hpf t).trans (hqg t).symm
  · intro t
    exact (hpf t).trans (hqg t).symm

end GraphMinor.GM07
