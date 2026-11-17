/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Caffarelli.Contact

/-! # Sublevel in convex Monge--Ampere analysis

Caffarelli contact geometry supporting Letwin arXiv:2607.24164v1
Lemma 2.2 through BB arXiv:1207.6128v1 Theorem 2.24(ii).
The declarations retain their given-source hypotheses; domain contact
rigidity and moment-source regularity have separate consumers.
-/

@[expose] public section

noncomputable section

section SublevelContactLemma

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology

/-! The contact lemma on sublevel sets. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma supporting_affine_convex (c : ℝ) (p x : E) :
    ConvexOn ℝ univ (fun w => c + ⟪p, w - x⟫) := by
  refine (((innerSL ℝ p).toLinearMap.convexOn
    (convex_univ : Convex ℝ (univ : Set E))).add_const (c - ⟪p, x⟫)).congr ?_
  intro w _
  change ⟪p, w⟫ + (c - ⟪p, x⟫) = c + ⟪p, w - x⟫
  rw [inner_sub_right]
  ring

private lemma subgradient_of_local_agreement {u v : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {U : Set E} (hU : IsOpen U) {x q : E} (hx : x ∈ U) (heq : ∀ ⦃w⦄, w ∈ U → v w = u w)
    (hq : ∀ w, v x + ⟪q, w - x⟫ ≤ v w) : ∀ w, u x + ⟪q, w - x⟫ ≤ u w := by
  have hlocal : ∀ w ∈ U, u x + ⟪q, w - x⟫ ≤ u w := by
    intro w hw
    simpa only [heq hx, heq hw] using hq w
  exact fun w => subgradient_le_on_of_isOpen hconv hU (subset_univ _) hx hlocal w (mem_univ w)

private lemma subgradientImage_of_local_agreement {u v : E → ℝ}
    (hconv : ConvexOn ℝ univ u) (huv : ∀ x, u x ≤ v x)
    {U : Set E} (hU : IsOpen U) (heq : ∀ ⦃x⦄, x ∈ U → v x = u x)
    {G : Set E} (hGU : G ⊆ U) :
    subgradientImage v G = subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨x, hx, hq⟩
    exact ⟨x, hx, subgradient_of_local_agreement hconv hU (hGU hx) heq hq⟩
  · rintro ⟨x, hx, hq⟩
    refine ⟨x, hx, ?_⟩
    intro w
    rw [heq (hGU hx)]
    exact (hq w).trans (huv w)

section FiniteDimensional

variable [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

private lemma eq_of_two_contacts_below {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ x, u x₀ + ⟪p, x - x₀⟫ ≤ u x) {R : ℝ}
    (hK : IsCompact {x | u x ≤ R})
    (hB : ∀ Q : Set E, IsCompact Q → Q ⊆ {x | u x < R} →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage u G) ∧
        (volume : Measure E) (subgradientImage u G) ≤
          ENNReal.ofReal b * (volume : Measure E) G)
    (hxR : u x₀ < R) {y : E} (hyR : u y < R)
    (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by
  classical
  by_contra hne
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨r, hr, hrR⟩ := exists_between (max_lt hxR hyR)
  have hx_r : u x₀ < r := (le_max_left _ _).trans_lt hr
  have hy_r : u y < r := (le_max_right _ _).trans_lt hr
  have hKr : IsCompact {x | u x ≤ r} :=
    hK.of_isClosed_subset (isClosed_le hu continuous_const)
      (fun _ hx => hx.trans hrR.le)
  obtain ⟨z, θ₀, hz, hzr, hexp₀⟩ :=
    exists_exposed_contact_of_lt hconv hp hx_r hKr
  have hθ₀ : θ₀ ≠ 0 := by
    intro hzero
    by_cases hxz : x₀ = z
    · have hyz : y ≠ z := by
        intro hyz
        exact hne (hyz.trans hxz.symm)
      have hh := hexp₀ y hy hy_r.le hyz
      simp [hzero] at hh
    · have hxcontact : u x₀ = u x₀ + ⟪p, x₀ - x₀⟫ := by simp
      have hh := hexp₀ x₀ hxcontact hx_r.le hxz
      simp [hzero] at hh
  have hn : 0 < ‖θ₀‖ := norm_pos_iff.mpr hθ₀
  let θ : E := ‖θ₀‖⁻¹ • θ₀
  have hθ : ‖θ‖ = 1 := by
    dsimp only [θ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ (ne_of_gt hn)]
  let ℓ : E → ℝ := fun x => u x₀ + ⟪p, x - x₀⟫
  have hℓ : ConvexOn ℝ univ ℓ := supporting_affine_convex (u x₀) p x₀
  have hℓcont : Continuous ℓ := by
    exact continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const))
  have hℓ0 : ℓ x₀ = u x₀ := by simp [ℓ]
  have hℓu (x : E) : ℓ x ≤ u x := hp x
  let v : E → ℝ := fun x => max (u x) (ℓ x + 2 * (ℓ x - r))
  have hvconv : ConvexOn ℝ univ v := by
    exact hconv.sup
      (hℓ.add (ConvexOn.smul (by norm_num : (0 : ℝ) ≤ 2)
        (hℓ.sub (concaveOn_const r convex_univ))))
  have hvcont : Continuous v :=
    continuousOn_univ.mp (hvconv.continuousOn isOpen_univ)
  have huv (x : E) : u x ≤ v x := le_max_left _ _
  have hv0 : v x₀ = u x₀ := by
    change max (u x₀) (ℓ x₀ + 2 * (ℓ x₀ - r)) = u x₀
    rw [hℓ0]
    apply max_eq_left
    linarith
  have hvp : ∀ x, v x₀ + ⟪p, x - x₀⟫ ≤ v x := by
    intro x
    rw [hv0]
    exact (hp x).trans (huv x)
  have hcontact (x : E) :
      v x = v x₀ + ⟪p, x - x₀⟫ ↔ u x = ℓ x ∧ ℓ x ≤ r := by
    rw [hv0]
    change max (u x) (ℓ x + 2 * (ℓ x - r)) = ℓ x ↔
      u x = ℓ x ∧ ℓ x ≤ r
    constructor
    · intro hx
      have hfirst : u x ≤ ℓ x :=
        (le_max_left (u x) (ℓ x + 2 * (ℓ x - r))).trans_eq hx
      have hsecond : ℓ x + 2 * (ℓ x - r) ≤ ℓ x :=
        (le_max_right (u x) (ℓ x + 2 * (ℓ x - r))).trans_eq hx
      exact ⟨le_antisymm hfirst (hℓu x), by linarith⟩
    · rintro ⟨hx, hxr⟩
      rw [hx]
      apply max_eq_left
      linarith
  let C : Set E := {x | v x = v x₀ + ⟪p, x - x₀⟫}
  have hC : IsCompact C := by
    apply hKr.of_isClosed_subset
    · exact isClosed_eq hvcont
        (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)))
    · intro x hx
      obtain ⟨hxu, hxr⟩ := (hcontact x).mp hx
      exact hxu.trans_le hxr
  have hzC : z ∈ C := (hcontact z).mpr ⟨hz, hz.symm.trans_le hzr.le⟩
  have hxC : x₀ ∈ C := by
    apply (hcontact x₀).mpr
    exact ⟨hℓ0.symm, hℓ0.trans_le hx_r.le⟩
  have hyC : y ∈ C := (hcontact y).mpr ⟨hy, hy.symm.trans_le hy_r.le⟩
  have hexp : ∀ x ∈ C, x ≠ z → ⟪x - z, θ⟫ < 0 := by
    intro x hx hxz
    obtain ⟨hxu, hxr⟩ := (hcontact x).mp hx
    have hh := hexp₀ x hxu (hxu.trans_le hxr) hxz
    change ⟪x - z, ‖θ₀‖⁻¹ • θ₀⟫ < 0
    rw [inner_smul_right]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hn) hh
  let U : Set E := {x | ℓ x < r} ∩ {x | u x < R}
  have hU : IsOpen U :=
    (isOpen_lt hℓcont continuous_const).inter (isOpen_lt hu continuous_const)
  have hzU : z ∈ U := by
    exact ⟨hz.symm.trans_lt hzr, hzr.trans hrR⟩
  have hvU : ∀ ⦃x⦄, x ∈ U → v x = u x := by
    intro x hx
    change max (u x) (ℓ x + 2 * (ℓ x - r)) = u x
    apply max_eq_left
    have hlt : ℓ x < r := hx.1
    have hle := hℓu x
    linarith
  have hwidth : ∃ h : ℝ, 0 < h ∧ C ∩ {x | -h ≤ ⟪x - z, θ⟫} ⊆ U := by
    let D : Set E := C ∩ Uᶜ
    have hD : IsCompact D := hC.inter_right hU.isClosed_compl
    have hf : Continuous (fun x : E => ⟪x - z, θ⟫) :=
      (continuous_id.sub continuous_const).inner continuous_const
    by_cases hDne : D.Nonempty
    · obtain ⟨d, hd, hmax⟩ := hD.exists_isMaxOn hDne hf.continuousOn
      have hdz : d ≠ z := by
        intro hdZ
        exact hd.2 (hdZ.symm ▸ hzU)
      have hdneg := hexp d hd.1 hdz
      refine ⟨-⟪d - z, θ⟫ / 2, by linarith, ?_⟩
      intro x hx
      by_contra hxU
      have hxd : x ∈ D := ⟨hx.1, hxU⟩
      have hh : ⟪x - z, θ⟫ ≤ ⟪d - z, θ⟫ := hmax hxd
      have hcap := hx.2
      change -(-⟪d - z, θ⟫ / 2) ≤ ⟪x - z, θ⟫ at hcap
      linarith
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx
      by_contra hxU
      exact hDne ⟨x, hx.1, hxU⟩
  obtain ⟨h, hh, hCU⟩ := hwidth
  have hvB : ∀ Q : Set E, IsCompact Q → Q ⊆ U →
      ∃ a b : ℝ, 0 < a ∧ ∀ G : Set E, IsOpen G → closure G ⊆ Q →
        ENNReal.ofReal a * (volume : Measure E) G ≤
          (volume : Measure E) (subgradientImage v G) ∧
        (volume : Measure E) (subgradientImage v G) ≤
          ENNReal.ofReal b * (volume : Measure E) G := by
    intro Q hQ hQU
    obtain ⟨a, b, ha, hab⟩ := hB Q hQ (fun x hx => (hQU hx).2)
    refine ⟨a, b, ha, ?_⟩
    intro G hG hGQ
    have hGU : G ⊆ U := fun _ hx => hQU (hGQ (subset_closure hx))
    rw [subgradientImage_of_local_agreement hconv huv hU hvU hGU]
    exact hab G hG hGQ
  have hsingle : C = {z} :=
    contactSet_eq_singleton_of_exposed_of_local_bounds hvconv hvp hC hzC
      hθ hexp hh hU hCU hvB
  have hxz : x₀ = z := mem_singleton_iff.mp (hsingle ▸ hxC)
  have hyz : y = z := mem_singleton_iff.mp (hsingle ▸ hyC)
  exact hne (hyz.trans hxz.symm)

/--
**Caffarelli's contact-set lemma below a level**: if `{u ≤ R}` is compact and the convex `u` has
two-sided Alexandrov bounds on compact subsets of `{u < R}`, then a supporting affine function at
`x₀`
(`u x₀ < R`) touches the graph of `u` at no other point of `{u < R}`. No compactness of the full
contact set
is assumed. -/
theorem eq_of_contact_of_sublevel_bounds {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {x₀ p : E}
    (hp : ∀ y, u x₀ + ⟪p, y - x₀⟫ ≤ u y) {R : ℝ} (hK : IsCompact {y | u y ≤ R})
    (hB :
      ∀ Q : Set E,
        IsCompact Q →
          Q ⊆ {y | u y < R} →
            ∃ a b : ℝ,
              0 < a ∧
                ∀ G : Set E,
                  IsOpen G →
                    closure G ⊆ Q →
                      ENNReal.ofReal a * (volume : Measure E) G ≤
                          (volume : Measure E) (subgradientImage u G) ∧
                        (volume : Measure E) (subgradientImage u G) ≤
                          ENNReal.ofReal b * (volume : Measure E) G)
    {y : E} (hyR : u y < R) (hy : u y = u x₀ + ⟪p, y - x₀⟫) : y = x₀ := by
  classical
  by_contra hne
  have hpy : ∀ w, u y + ⟪p, w - y⟫ ≤ u w := by
    intro w
    have hh := hp w
    have hy' := hy
    simp only [inner_sub_right] at hh hy' ⊢
    linarith
  have hxcontact : u x₀ = u y + ⟪p, x₀ - y⟫ := by
    have hy' := hy
    simp only [inner_sub_right] at hy' ⊢
    linarith
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let f : ℝ → E := AffineMap.lineMap y x₀
  have hf : Continuous f := AffineMap.lineMap_continuous
  have hf0 : f 0 = y := AffineMap.lineMap_apply_zero y x₀
  have htend : Tendsto (fun t => u (f t)) (𝓝 0) (𝓝 (u y)) := by
    have hh : Tendsto (fun t => u (f t)) (𝓝 0) (𝓝 (u (f 0))) := (hu.comp hf).tendsto 0
    rw [hf0] at hh
    exact hh
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), u (f t) < R := htend.eventually (eventually_lt_nhds hyR)
  obtain ⟨t, ht, htR, ht1⟩ :=
    (hnear.and (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one))).exists_gt
  have htcontact : u (f t) = u y + ⟪p, f t - y⟫ := by
    have hh :=
      hconv.2 (mem_univ y) (mem_univ x₀) (sub_nonneg.mpr ht1.le) ht.le (by ring : 1 - t + t = 1)
    have hl := hpy (f t)
    have hx' := hxcontact
    have hft : f t = (1 - t) • y + t • x₀ := AffineMap.lineMap_apply_module y x₀ t
    rw [hft] at hl ⊢
    simp only [smul_eq_mul] at hh
    simp only [inner_sub_right, inner_add_right, inner_smul_right] at hl hx' ⊢
    nlinarith
  have he : f t = y := eq_of_two_contacts_below hconv hpy hK hB hyR htR htcontact
  have htzero : t = 0 := (AffineMap.lineMap_injective ℝ hne) (he.trans hf0.symm)
  exact (ne_of_gt ht) htzero

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end SublevelContactLemma
