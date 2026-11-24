/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Union and difference of closed discs

* `disc_union : DiscUnionStatement`: two closed discs that meet exactly in a line of both boundaries
  have a closed disc as union.
* `disc_difference : DiscDifferenceStatement`: the difference form.

For the union, cut the unit disc of `ℂ` along a diameter. By the extension theorem
`exists_bdMatch_closedInner`, each of the two discs has a homeomorphism onto one half that sends the
common line to the diameter by the same parametrization. These two maps agree on the line, so they
paste, since closed discs are closed in a Hausdorff space.

For the difference, take a chart of the larger disc. The boundary of the smaller disc is the line,
on the unit circle, together with a cross-cut of the circle. So the smaller disc is one side of the
cut, and the closure of the difference is the other side.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

local notation "𝕀" => unitInterval

universe u

/-- Two arcs with the same ends match any other two such arcs. -/
theorem exists_bdMatch_of_arcs {c d c' d' : 𝕀 → ℂ} (hc : IsArcMap c) (hd : IsArcMap d)
    (hc' : IsArcMap c') (hd' : IsArcMap d') (h0 : d 0 = c 0) (h1 : d 1 = c 1) (h0' : d' 0 = c' 0)
    (h1' : d' 1 = c' 1) (hm : ∀ s t, c s = d t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hm' : ∀ s t, c' s = d' t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ h k : ℂ → ℂ, BdMatch (range c ∪ range d) (range c' ∪ range d') h k ∧
      (∀ s, h (c s) = c' s) ∧ ∀ s, h (d s) = d' s := by
  classical
  have key : ∀ {c d c' d' : 𝕀 → ℂ}, IsArcMap c → IsArcMap d → d 0 = c 0 → d 1 = c 1 →
      d' 0 = c' 0 → d' 1 = c' 1 → (∀ s t, c s = d t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) →
      ∃ h : ℂ → ℂ, (∀ s, h (c s) = c' s) ∧ ∀ s, h (d s) = d' s := by
    intro c d c' d' hc hd h0 h1 h0' h1' hm
    obtain ⟨ι, hι, -⟩ := hc.exists_inv
    obtain ⟨κ, hκ, -⟩ := hd.exists_inv
    refine ⟨fun z => if z ∈ range c then c' (ι z) else d' (κ z), fun s => ?_, fun s => ?_⟩
    · have : c s ∈ range c := ⟨s, rfl⟩
      simp only [this, ite_true, hι]
    · by_cases hs : d s ∈ range c
      · obtain ⟨r, hr⟩ := hs
        have hin : d s ∈ range c := ⟨r, hr⟩
        simp only [hin, ite_true]
        rw [← hr, hι]
        rcases hm r s hr with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · rw [h2, h3, h0']
        · rw [h2, h3, h1']
      · simp only [hs, ite_false, hκ]
  obtain ⟨h, h2, h3⟩ := key (c' := c') (d' := d') hc hd h0 h1 h0' h1' hm
  obtain ⟨k, k2, k3⟩ := key (c' := c) (d' := d) hc' hd' h0' h1' h0 h1 hm'
  exact ⟨h, k, bdMatch_of_arcs hc hd hc' hd' h2 h3 k2 k3, h2, h3⟩

variable {S : Type u} [TopologicalSpace S]

/-- A closed disc has a homeomorphism onto the closed domain of two arcs with the same ends, taking
a given line of the boundary to one of the arcs. -/
private theorem exists_half {Δ : Set S} (hΔ : IsClosedDisc Δ) {ℓ : 𝕀 → S} (hℓ : Continuous ℓ)
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

theorem IsChart.isCompact {D : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart D h g) : IsCompact D :=
  c.g_closedBall ▸ (isCompact_closedBall 0 1).image_of_continuousOn c.gc

theorem IsClosedDisc.isCompact {D : Set S} (hD : IsClosedDisc D) : IsCompact D := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  exact c.isCompact

/-- The diameter of the unit disc of `ℂ`. -/
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

/-- **The union of two closed discs that meet in a line of both boundaries.** See the module
docstring for the route. -/
theorem disc_union : DiscUnionStatement.{u} := by
  classical
  intro S _ _ Δ₁ Δ₂ L s t h₁ h₂ hL hmeet hL₁ hL₂
  obtain ⟨f, hf0, hf1⟩ := hL
  let ℓ : 𝕀 → S := fun u => (f u).1
  have hℓ : Continuous ℓ := continuous_subtype_val.comp f.continuous
  have hinj : Function.Injective ℓ := fun u v h => f.injective (Subtype.ext h)
  have hrL : range ℓ = L := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact (f u).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp [ℓ]⟩
  obtain ⟨a, b, cut⟩ := exists_cut_diameter
  let e : 𝕀 → ℂ := diameter
  obtain ⟨p₁, q₁, pc₁, qc₁, pm₁, qm₁, l₁, r₁, v₁, b₁⟩ := exists_half h₁ hℓ hinj
    (hrL ▸ hL₁) cut.arc_a
    cut.arc_e cut.a_zero cut.a_one cut.a_eq_e
  obtain ⟨p₂, q₂, pc₂, qc₂, pm₂, qm₂, l₂, r₂, v₂, b₂⟩ := exists_half h₂ hℓ hinj
    (hrL ▸ hL₂) cut.arc_b
    cut.arc_e cut.b_zero cut.b_one cut.symm.a_eq_e
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨f1, -, -, f4, -, -⟩ := cut.closedInner_facts (isJordanParts φ₀)
  rw [closedInner_sphere] at f1
  set H₁ := closedInner (side a diameter) with hH₁
  set H₂ := closedInner (side b diameter) with hH₂
  have hcl₁ : IsClosed H₁ := by
    obtain ⟨φ⟩ := cut.oArc_side
    exact (isJordanParts φ).isCompact_closure_inner.isClosed
  have hcl₂ : IsClosed H₂ := by
    obtain ⟨φ⟩ := cut.symm.oArc_side
    exact (isJordanParts φ).isCompact_closure_inner.isClosed
  have hLΔ₁ : ∀ u, ℓ u ∈ Δ₁ := fun u => discBd_subset _ (hL₁ (f u).2)
  have hLΔ₂ : ∀ u, ℓ u ∈ Δ₂ := fun u => discBd_subset _ (hL₂ (f u).2)
  have hq₁ : ∀ u, q₁ (diameter u) = ℓ u := fun u => by rw [← v₁ u, l₁ (hLΔ₁ u)]
  have hq₂ : ∀ u, q₂ (diameter u) = ℓ u := fun u => by rw [← v₂ u, l₂ (hLΔ₂ u)]
  let P : S → ℂ := fun x => if x ∈ Δ₁ then p₁ x else p₂ x
  let Q : ℂ → S := fun z => if z ∈ H₁ then q₁ z else q₂ z
  have Pon₁ : EqOn P p₁ Δ₁ := fun x hx => by simp only [P, hx, ite_true]
  have Pon₂ : EqOn P p₂ Δ₂ := fun x hx => by
    by_cases h : x ∈ Δ₁
    · have hxL : x ∈ range ℓ := hrL ▸ hmeet ▸ ⟨h, hx⟩
      obtain ⟨u, rfl⟩ := hxL
      rw [Pon₁ h, v₁, v₂]
    · simp only [P, h, ite_false]
  have Qon₁ : EqOn Q q₁ H₁ := fun z hz => by simp only [Q, hz, ite_true]
  have Qon₂ : EqOn Q q₂ H₂ := fun z hz => by
    by_cases h : z ∈ H₁
    · obtain ⟨u, rfl⟩ := f4 ⟨h, hz⟩
      rw [Qon₁ h, hq₁, hq₂]
    · simp only [Q, h, ite_false]
  have Pc : ContinuousOn P (Δ₁ ∪ Δ₂) := (pc₁.congr Pon₁).union_of_isClosed (pc₂.congr Pon₂)
    h₁.isCompact.isClosed h₂.isCompact.isClosed
  have Qc : ContinuousOn Q (closedBall 0 1) := f1 ▸ (qc₁.congr Qon₁).union_of_isClosed
    (qc₂.congr Qon₂) hcl₁ hcl₂
  have hl : LeftInvOn P Q (closedBall 0 1) := by
    intro z hz
    rw [← f1] at hz
    show P (Q z) = z
    rcases hz with hz | hz
    · rw [Qon₁ hz, Pon₁ (qm₁ hz)]
      exact r₁ hz
    · rw [Qon₂ hz, Pon₂ (qm₂ hz)]
      exact r₂ hz
  have hr : LeftInvOn Q P (Δ₁ ∪ Δ₂) := by
    rintro x (hx | hx)
    · show Q (P x) = x
      rw [Pon₁ hx, Qon₁ (pm₁ hx)]
      exact l₁ hx
    · show Q (P x) = x
      rw [Pon₂ hx, Qon₂ (pm₂ hx)]
      exact l₂ hx
  have himg : Q '' closedBall 0 1 = Δ₁ ∪ Δ₂ := by
    refine Subset.antisymm ?_ fun x hx => ?_
    · rw [← f1]
      rintro _ ⟨z, hz | hz, rfl⟩
      · rw [Qon₁ hz]
        exact Or.inl (qm₁ hz)
      · rw [Qon₂ hz]
        exact Or.inr (qm₂ hz)
    · refine ⟨P x, ?_, hr hx⟩
      rw [← f1]
      rcases hx with hx | hx
      · rw [Pon₁ hx]
        exact Or.inl (pm₁ hx)
      · rw [Pon₂ hx]
        exact Or.inr (pm₂ hx)
  obtain ⟨r1, r2⟩ := isClosedDisc_closedBall.1.image (f := Q) (f' := P) Qc (himg ▸ Pc) hl
  rw [himg, isClosedDisc_closedBall.2] at r2
  rw [himg] at r1
  refine ⟨r1, r2.trans ?_⟩
  have hLe : ∀ {x}, x ∈ L → ∃ u, ℓ u = x := by
    intro x hx
    rw [← hrL] at hx
    exact hx
  have hs0 : ℓ 0 = s := hf0
  have ht1 : ℓ 1 = t := hf1
  have hae : ∀ v u, a v = diameter u → ℓ u ∈ ({s, t} : Set S) := fun v u h => by
    rcases cut.a_eq_e v u h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl hs0
    · exact Or.inr ht1
  have hbe : ∀ v u, b v = diameter u → ℓ u ∈ ({s, t} : Set S) := fun v u h => by
    rcases cut.symm.a_eq_e v u h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl hs0
    · exact Or.inr ht1
  have hma : ∀ v, a v ∈ H₁ := fun v => Or.inr (Or.inl ⟨v, rfl⟩)
  have hmb : ∀ v, b v ∈ H₂ := fun v => Or.inr (Or.inl ⟨v, rfl⟩)
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← cut.union] at hz
    rcases hz with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [Qon₁ (hma v)]
      refine ⟨Or.inl (b₁ ▸ ⟨a v, Or.inl ⟨v, rfl⟩, rfl⟩), ?_⟩
      rintro ⟨hx, hn⟩
      obtain ⟨u, hu⟩ := hLe hx
      refine hn ?_
      rw [← hu]
      refine hae v u ?_
      rw [← v₁ u, hu, r₁ (hma v)]
    · rw [Qon₂ (hmb v)]
      refine ⟨Or.inr (b₂ ▸ ⟨b v, Or.inl ⟨v, rfl⟩, rfl⟩), ?_⟩
      rintro ⟨hx, hn⟩
      obtain ⟨u, hu⟩ := hLe hx
      refine hn ?_
      rw [← hu]
      refine hbe v u ?_
      rw [← v₂ u, hu, r₂ (hmb v)]
  · rintro ⟨hx, hn⟩
    have hend : x ∈ L → x ∈ ({s, t} : Set S) := fun hL' => by
      by_contra h
      exact hn ⟨hL', h⟩
    have hs : s ∈ Q '' sphere 0 1 := ⟨diameter 0, cut.a_zero ▸ cut.a_mem 0, by
      rw [Qon₁ (show diameter 0 ∈ H₁ from Or.inr (Or.inr ⟨0, rfl⟩)), hq₁, hs0]⟩
    have ht : t ∈ Q '' sphere 0 1 := ⟨diameter 1, cut.a_one ▸ cut.a_mem 1, by
      rw [Qon₁ (show diameter 1 ∈ H₁ from Or.inr (Or.inr ⟨1, rfl⟩)), hq₁, ht1]⟩
    have hLcase : x ∈ L → x ∈ Q '' sphere 0 1 := fun hL' => by
      rcases hend hL' with rfl | h'
      · exact hs
      · rw [mem_singleton_iff.mp h']
        exact ht
    rcases hx with hx | hx
    · rw [b₁] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rcases hz with ⟨v, rfl⟩ | ⟨u, rfl⟩
      · exact ⟨a v, cut.a_mem v, Qon₁ (hma v)⟩
      · exact hLcase (by rw [hq₁]; exact (f u).2)
    · rw [b₂] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rcases hz with ⟨v, rfl⟩ | ⟨u, rfl⟩
      · exact ⟨b v, cut.b_mem v, Qon₂ (hmb v)⟩
      · exact hLcase (by rw [hq₂]; exact (f u).2)

/-- Removing the open arc `e` from `e ∪ m`. -/
private theorem sdiff_open_arc {e m : 𝕀 → ℂ} (h0 : m 0 = e 0) (h1 : m 1 = e 1)
    (hm : ∀ s t, e s = m t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    (range e ∪ range m) \ (range e \ {e 0, e 1}) = range m := by
  ext z
  constructor
  · rintro ⟨hz | hz, hn⟩
    · by_cases hend : z ∈ ({e 0, e 1} : Set ℂ)
      · rcases hend with rfl | rfl
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      · exact absurd ⟨hz, hend⟩ hn
    · exact hz
  · rintro ⟨t, rfl⟩
    refine ⟨Or.inr ⟨t, rfl⟩, ?_⟩
    rintro ⟨⟨s, hs⟩, hn⟩
    rcases hm s t hs with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hn (Or.inl h0)
    · exact hn (Or.inr h1)

/-- **The difference of two closed discs whose boundaries meet in a line.** See the module docstring
for the route. -/
theorem disc_difference : DiscDifferenceStatement.{u} := by
  intro S _ _ Δ₁ Δ₂ L s t h₁ h₂ hsub hL hmeet
  obtain ⟨h, g, c⟩ := h₂.exists_isChart
  obtain ⟨f, hf0, hf1⟩ := hL
  have hLb : ∀ {x}, x ∈ L → x ∈ discBd Δ₁ ∧ x ∈ discBd Δ₂ := by
    intro x hx
    rw [← hmeet] at hx
    exact hx
  have hLD : ∀ u, (f u).1 ∈ Δ₂ := fun u => discBd_subset _ (hLb (f u).2).2
  have hbd₁ : discBd Δ₁ ⊆ Δ₂ := (discBd_subset _).trans hsub
  have hhinj : InjOn h Δ₂ := c.gh.injOn
  let e : 𝕀 → ℂ := fun u => h (f u).1
  have he : IsArcMap e := ⟨c.hc.comp_continuous (continuous_subtype_val.comp f.continuous) hLD,
    fun u v huv => f.injective (Subtype.ext (hhinj (hLD u) (hLD v) huv))⟩
  have hrange : range e = h '' L := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨_, (f u).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨f.symm ⟨x, hx⟩, by simp [e]⟩
  obtain ⟨φ⟩ := c.oArc_h hbd₁ h₁.isOArc_discBd
  obtain ⟨φ₀⟩ := oArc_sphere
  have hsub1 : range e ⊆ h '' discBd Δ₁ := by
    rw [hrange]
    exact image_mono fun x hx => (hLb hx).1
  have hsub2 : range e ⊆ sphere 0 1 := by
    rw [hrange, ← c.bd]
    exact image_mono fun x hx => (hLb hx).2
  obtain ⟨m, hm, m0, m1, hum, hmm⟩ := exists_other_arc φ he hsub1
  obtain ⟨b, hb, b0, b1, hub, hmb⟩ := exists_other_arc φ₀ he hsub2
  have hmsub : range m ⊆ h '' discBd Δ₁ := hum ▸ subset_union_right
  have hinside : ∀ u : 𝕀, u ≠ 0 → u ≠ 1 → m u ∈ inner (sphere (0 : ℂ) 1) := by
    intro u h0 h1
    rw [inner_sphere, mem_ball_zero_iff]
    obtain ⟨x, hx, hxu⟩ := hmsub ⟨u, rfl⟩
    refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp ?_) fun hn => ?_
    · rw [← hxu]
      exact c.hm (hbd₁ hx)
    · have hz : m u ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hn
      rw [← c.bd] at hz
      obtain ⟨y, hy, hyu⟩ := hz
      have hxy : y = x := hhinj (discBd_subset _ hy) (hbd₁ hx) (hyu.trans hxu.symm)
      have hxL : x ∈ L := hmeet ▸ ⟨hx, hxy ▸ hy⟩
      have hme : m u ∈ range e := by
        rw [hrange, ← hxu]
        exact mem_image_of_mem h hxL
      obtain ⟨r, hr⟩ := hme
      rcases hmm r u hr with ⟨-, h'⟩ | ⟨-, h'⟩
      · exact h0 h'
      · exact h1 h'
  have hne : m 0 ≠ m 1 := fun h' => zero_ne_one (hm.2 h')
  have cut : IsCut (sphere (0 : ℂ) 1) e b m := ⟨he, hb, hm, m0.symm, m1.symm, b0.trans m0.symm,
    b1.trans m1.symm, hne, hub, by
      intro s t hst
      exact hmb s t hst, hinside⟩
  have hside : side e m = h '' discBd Δ₁ := hum
  have J₀ := isJordanParts φ₀
  obtain ⟨f1, f2, f3, f4, -, -⟩ := cut.closedInner_facts J₀
  rw [closedInner_sphere] at f1 f2 f3
  have hG : Nonempty (Circle ≃ₜ side e m) := cut.oArc_side
  have hG' : Nonempty (Circle ≃ₜ side b m) := cut.symm.oArc_side
  obtain ⟨d1, d2⟩ := c.disc_h hsub h₁
  have hΔ₁ : g '' closedInner (side e m) = Δ₁ := by
    rw [hside, ← eq_closedInner_of_discBd (by rw [← hside]; exact hG) d1 d2]
    exact c.g_h hsub
  obtain ⟨d3, d4⟩ := isClosedDisc_closedInner hG'
  obtain ⟨d5, d6⟩ := c.disc_g f3 d3
  rw [d4] at d6
  have hmH : range m ⊆ closedInner (side e m) := fun z hz => Or.inr (Or.inr hz)
  have hmH' : range m ⊆ closedInner (side b m) := fun z hz => Or.inr (Or.inr hz)
  have hdiff : Δ₂ \ Δ₁ = g '' (closedInner (side b m) \ range m) := by
    have hset : closedBall 0 1 \ closedInner (side e m) =
        closedInner (side b m) \ range m := by
      ext z
      constructor
      · rintro ⟨hz, hn⟩
        rw [← f1] at hz
        rcases hz with hz | hz
        · exact absurd hz hn
        · exact ⟨hz, fun h' => hn (hmH h')⟩
      · rintro ⟨hz, hn⟩
        exact ⟨f3 hz, fun h' => hn (f4 ⟨h', hz⟩)⟩
    rw [← hset, c.g_sdiff Subset.rfl f2, c.g_closedBall, hΔ₁]
  obtain ⟨φ'⟩ := id hG'
  have J' := isJordanParts φ'
  have hclosure : closure (Δ₂ \ Δ₁) = g '' closedInner (side b m) := by
    refine Subset.antisymm ?_ ?_
    · refine closure_minimal ?_ ?_
      · rw [hdiff]
        exact image_mono sdiff_subset
      · exact (J'.isCompact_closure_inner.image_of_continuousOn (c.gc.mono f3)).isClosed
    · have hin : inner (side b m) ⊆ closedInner (side b m) \ range m := fun z hz =>
        ⟨Or.inl hz, fun h' => J'.inner_subset_compl hz (Or.inr h')⟩
      have hcl : closure (inner (side b m)) = closedInner (side b m) := J'.closure_inner
      calc g '' closedInner (side b m) = g '' closure (inner (side b m)) := by rw [hcl]
        _ ⊆ closure (g '' inner (side b m)) :=
          ContinuousOn.image_closure (by rw [hcl]; exact c.gc.mono f3)
        _ ⊆ closure (Δ₂ \ Δ₁) := closure_mono (by
          rw [hdiff]
          exact image_mono hin)
  have he0 : g (e 0) = s := by
    change g (h (f 0).1) = s
    rw [c.gh (hLD 0), hf0]
  have he1 : g (e 1) = t := by
    change g (h (f 1).1) = t
    rw [c.gh (hLD 1), hf1]
  have hLg : L = g '' range e := by
    rw [hrange, c.g_h fun x hx => discBd_subset _ (hLb hx).2]
  have hG₁ : discBd Δ₁ = g '' (range e ∪ range m) := by
    rw [hum, c.g_h hbd₁]
  have hG₂ : discBd Δ₂ = g '' (range e ∪ range b) := by
    rw [hub, c.g_sphere]
  have hrsub : range e ⊆ closedBall 0 1 := hsub2.trans sphere_subset_closedBall
  have hmsub' : range m ⊆ closedBall 0 1 := hmH.trans f2
  have hbsub : range b ⊆ closedBall 0 1 :=
    (hub ▸ subset_union_right : range b ⊆ sphere 0 1).trans sphere_subset_closedBall
  have hpsub : ({e 0, e 1} : Set ℂ) ⊆ closedBall 0 1 := by
    rintro z (rfl | rfl)
    · exact hrsub ⟨0, rfl⟩
    · exact hrsub ⟨1, rfl⟩
  have hopen : L \ {s, t} = g '' (range e \ {e 0, e 1}) := by
    rw [c.g_sdiff hrsub hpsub, ← hLg, image_pair, he0, he1]
  have s1 := sdiff_open_arc m0 m1 hmm
  have s2 := sdiff_open_arc b0 b1 hmb
  refine ⟨?_, ?_, ?_⟩
  · rw [hclosure]
    exact d5
  · rw [hclosure, d6, hopen, hG₁, hG₂, ← image_union, ← c.g_sdiff
      (union_subset (union_subset hrsub hmsub') (union_subset hrsub hbsub))
        (sdiff_subset.trans hrsub)]
    congr 1
    rw [show range e ∪ range m ∪ (range e ∪ range b) = (range e ∪ range m) ∪
      (range e ∪ range b) from
      rfl, union_sdiff_distrib, s1, s2, side, union_comm]
  · rw [hclosure, hopen, hG₁, ← c.g_sdiff (union_subset hrsub hmsub')
    (sdiff_subset.trans hrsub), s1]
    conv_lhs => rw [← hΔ₁]
    rw [← c.g_inter f3 f2]
    congr 1
    rw [inter_comm]
    exact Subset.antisymm f4 fun z hz => ⟨hmH hz, hmH' hz⟩

end GraphMinor.Surface
