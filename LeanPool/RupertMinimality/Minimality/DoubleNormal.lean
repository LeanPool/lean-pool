/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Basic

/-! # Double Normal -/

@[expose] public section

namespace RupertMinimality

/-!
# L3 (and the transfer step of L4): double normals of a convex polygon

Part of step 2 of `minimality.md`.  `F = convexHull ℝ W` for a finite
`W ⊆ ℝ²` with nonempty interior, and `u ≠ 0` a screen direction.  An affine
screen field `p ↦ M p + b` is *admissible for `u`* if `⟪u, M u⟫ = 0`: by L2
(`Coplanar.lean`), these are the screen motions that a first-order motion
realizes on a plane whose iso-depth direction is `u`.

* `exists_admissible_inward_field` (L3, construction direction): if `u` is not
  a double-normal direction of `F`, some admissible field is strictly inward
  at every point of `W`.  (The converse obstruction direction of L3 is not
  needed for any Rupert theorem and is not formalized.)
* `isDoubleNormalDir_convexHull_cases` (Lemma 3.0, finiteness, in the form
  used by L4), `exists_isDoubleNormalDir` (diameters).
* `isDoubleNormalDir_proj_iff'` (L4): for a set in a non-vertical plane, a
  horizontal direction in the plane is a double-normal direction of the set
  iff its projection is one of the shadow.

Note.  For a triangle, a side whose two angles are both ≤ π/2 is itself a
vertex–vertex double normal (e.g. every triangle's longest side), so the
double normals of a triangle are not just its altitudes.  No triangle special
case is stated here; the general definition `IsDoubleNormalDir` covers all
cases.
-/

namespace Minimality

open scoped RealInnerProductSpace Matrix

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point of `conv W` outside `W` minimizing a linear functional `ℓ` over
`W` is a combination of at least two distinct minimizers. -/
theorem exists_two_of_mem_convexHull_of_isMin (W : Finset E) (ℓ : E →ₗ[ℝ] ℝ) {x : E}
    (hx : x ∈ convexHull ℝ (W : Set E)) (hxW : x ∉ W) (hmin : ∀ y ∈ W, ℓ x ≤ ℓ y) :
    ∃ y₁ ∈ W, ∃ y₂ ∈ W, y₁ ≠ y₂ ∧ ℓ y₁ = ℓ x ∧ ℓ y₂ = ℓ x := by
  classical
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull.mp hx
  set W₀ := W.filter (fun y => ℓ y = ℓ x) with hW₀
  -- the weights vanish off the level set
  have hsum : ∑ y ∈ W, w y * (ℓ y - ℓ x) = 0 := by
    have h1 : ℓ x = ∑ y ∈ W, w y * ℓ y := by
      rw [← hwx, Finset.centerMass_eq_of_sum_1 _ _ hw1, map_sum]
      simp [map_smul]
    rw [Finset.sum_congr rfl (fun y _ => mul_sub (w y) (ℓ y) (ℓ x)), Finset.sum_sub_distrib,
      ← Finset.sum_mul, hw1, one_mul, ← h1, sub_self]
  have hzero : ∀ y ∈ W, w y * (ℓ y - ℓ x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
      mul_nonneg (hw0 y hy) (sub_nonneg.mpr (hmin y hy))).mp hsum
  have hoff : ∀ y ∈ W, y ∉ W₀ → w y = 0 := by
    intro y hy hy0
    have hne : ℓ y - ℓ x ≠ 0 := by
      intro h0; exact hy0 (Finset.mem_filter.mpr ⟨hy, by linarith⟩)
    exact (mul_eq_zero.mp (hzero y hy)).resolve_right hne
  have hx0 : x ∈ convexHull ℝ (W₀ : Set E) := by
    refine Finset.mem_convexHull.mpr ⟨w, fun y hy => hw0 y (Finset.filter_subset _ _ hy), ?_, ?_⟩
    · rw [← hw1]; exact Finset.sum_subset (Finset.filter_subset _ _) hoff
    · rw [← hwx]; exact Finset.centerMass_subset _ (Finset.filter_subset _ _) hoff
  by_contra hcon
  push Not at hcon
  have hcard : W₀.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro y₁ h₁ y₂ h₂
    rw [Finset.mem_filter] at h₁ h₂
    by_contra hne
    exact hcon y₁ h₁.1 y₂ h₂.1 hne h₁.2 |>.elim h₂.2
  rcases Finset.card_le_one_iff_subset_singleton.mp hcard with ⟨y, hy⟩
  have : x ∈ convexHull ℝ ({y} : Set E) :=
    convexHull_mono (by rw [← Finset.coe_singleton]; exact Finset.coe_subset.mpr hy) hx0
  rw [convexHull_singleton, Set.mem_singleton_iff] at this
  subst this
  rcases Finset.eq_empty_or_nonempty W₀ with h | h
  · rw [h, Finset.coe_empty, convexHull_empty] at hx0; exact hx0
  · obtain ⟨z, hz⟩ := h
    have := hy hz
    rw [Finset.mem_singleton] at this
    subst this
    exact hxW (Finset.filter_subset _ _ hz)

/-- **Lemma 3.0, finiteness (form used in L4).** A double normal of the hull of a
finite set `W` is either parallel to `w' - w`, or perpendicular to `w' - w`,
for two distinct points `w, w'` of `W`: if the chord's end `a` is not in `W`,
the points of `W` carrying `a`'s convex weights all minimize `⟪u, ·⟫`. -/
theorem isDoubleNormalDir_convexHull_cases (W : Finset E) (u : E)
    (h : IsDoubleNormalDir (convexHull ℝ (W : Set E)) u) :
    ∃ w ∈ W, ∃ w' ∈ W, w ≠ w' ∧ ((∃ t : ℝ, w' - w = t • u) ∨ ⟪u, w' - w⟫ = 0) := by
  obtain ⟨a, ha, b, hb, hab, ⟨t, ht⟩, hB, hA⟩ := h
  have ht0 : t ≠ 0 := by
    rintro rfl; apply hab; rw [zero_smul, sub_eq_zero] at ht; exact ht.symm
  -- `ℓ = ⟪b - a, ·⟫` is minimized at `a` and maximized at `b`
  let ℓ : E →ₗ[ℝ] ℝ := (innerₛₗ ℝ (b - a))
  have hℓ : ∀ x, ℓ x = ⟪b - a, x⟫ := fun x => rfl
  have hperp : ∀ y₁ y₂ : E, ℓ y₁ = ℓ y₂ → ⟪u, y₂ - y₁⟫ = 0 := by
    intro y₁ y₂ h
    rw [hℓ, hℓ, ht, inner_smul_left, inner_smul_left] at h
    have : ⟪u, y₂⟫ = ⟪u, y₁⟫ := by
      simpa [ht0] using h.symm
    rw [inner_sub_right, this, sub_self]
  by_cases haW : a ∈ W
  · by_cases hbW : b ∈ W
    · exact ⟨a, haW, b, hbW, hab, Or.inl ⟨t, ht⟩⟩
    · obtain ⟨y₁, h₁, y₂, h₂, hne, e₁, e₂⟩ := exists_two_of_mem_convexHull_of_isMin W (-ℓ) hb hbW
        (fun y hy => by
          have := hB y (subset_convexHull ℝ _ hy)
          simp only [LinearMap.neg_apply, hℓ, neg_le_neg_iff]
          rw [inner_sub_right] at this; linarith)
      exact ⟨y₁, h₁, y₂, h₂, hne, Or.inr (hperp _ _ (by
        simp only [LinearMap.neg_apply, neg_inj] at e₁ e₂; rw [e₁, e₂]))⟩
  · obtain ⟨y₁, h₁, y₂, h₂, hne, e₁, e₂⟩ := exists_two_of_mem_convexHull_of_isMin W ℓ ha haW
      (fun y hy => by
        have := hA y (subset_convexHull ℝ _ hy)
        rw [hℓ, hℓ]
        rw [show a - b = -(b - a) by abel, inner_neg_left, inner_sub_right] at this; linarith)
    exact ⟨y₁, h₁, y₂, h₂, hne, Or.inr (hperp _ _ (by rw [e₁, e₂]))⟩

/-- A diameter is a double normal: every compact set with two points has a
double-normal direction. -/
theorem exists_isDoubleNormalDir {F : Set E} (hF : IsCompact F) (hF2 : F.Nontrivial) :
    ∃ u, IsDoubleNormalDir F u := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hF2
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hmax⟩ := (hF.prod hF).exists_isMaxOn ⟨(x, y), hx, hy⟩
    (continuous_norm.comp (continuous_snd.sub continuous_fst)).continuousOn
  have hmax' : ∀ p ∈ F, ∀ q ∈ F, ‖q - p‖ ≤ ‖b - a‖ := fun p hp q hq =>
    hmax (show (p, q) ∈ F ×ˢ F from ⟨hp, hq⟩)
  have hab : a ≠ b := by
    intro h
    have := hmax' x hx y hy
    rw [h, sub_self, norm_zero] at this
    exact hxy (by rw [← sub_eq_zero, ← norm_eq_zero]; exact le_antisymm (by
      have := norm_nonneg (y - x); linarith [norm_sub_rev x y]) (norm_nonneg _))
  refine ⟨b - a, a, ha, b, hb, hab, ⟨1, by rw [one_smul]⟩, fun q hq => ?_, fun q hq => ?_⟩
  · have h1 := hmax' a ha q hq
    have h2 : ‖q - a‖ ^ 2 = ‖q - b‖ ^ 2 + 2 * ⟪b - a, q - b⟫ + ‖b - a‖ ^ 2 := by
      rw [show q - a = (q - b) + (b - a) by abel, norm_add_sq_real, real_inner_comm]
    nlinarith [norm_nonneg (q - a), norm_nonneg (b - a), sq_nonneg ‖q - b‖]
  · have h1 := hmax' q hq b hb
    have h2 : ‖b - q‖ ^ 2 = ‖a - q‖ ^ 2 + 2 * ⟪a - b, q - a⟫ + ‖b - a‖ ^ 2 := by
      rw [show b - q = (a - q) + (b - a) by abel, norm_add_sq_real]
      rw [show a - q = -(q - a) by abel, inner_neg_left, show a - b = -(b - a) by abel,
        inner_neg_left, real_inner_comm]
    nlinarith [norm_nonneg (b - q), norm_nonneg (b - a), sq_nonneg ‖a - q‖]

end General

section Helpers

theorem inner_rot90_left_self (u : ℝ²) : ⟪rot90 u, u⟫ = 0 := by
  simp [rot90, PiLp.inner_apply, Fin.sum_univ_two]; ring

theorem inner_rot90_right_self (u : ℝ²) : ⟪u, rot90 u⟫ = 0 := by
  rw [real_inner_comm]; exact inner_rot90_left_self u

/-- Orthogonal decomposition along `u` and `J u`. -/
theorem norm_sq_smul_eq (u p : ℝ²) :
    ‖u‖ ^ 2 • p = ⟪u, p⟫ • u + ⟪rot90 u, p⟫ • rot90 u := by
  have hn : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ext i
  fin_cases i <;> simp [rot90, PiLp.inner_apply, Fin.sum_univ_two, hn] <;> ring

theorem inner_rot90_rot90 (u : ℝ²) : ⟪rot90 u, rot90 u⟫ = ‖u‖ ^ 2 := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [rot90]; ring

theorem eq_of_inner_eq_of_inner_rot90_eq {u : ℝ²} (hu : u ≠ 0) {p q : ℝ²}
    (hx : ⟪u, p⟫ = ⟪u, q⟫) (hy : ⟪rot90 u, p⟫ = ⟪rot90 u, q⟫) : p = q := by
  have hn : ‖u‖ ^ 2 ≠ 0 := by positivity
  have := norm_sq_smul_eq u p
  rw [hx, hy, ← norm_sq_smul_eq u q] at this
  exact (smul_right_injective _ hn this.symm).symm

/-- Disjoint compact convex nonempty subsets of `ℝ` are strictly separated
by a point `y₀`, with orientation `κ`. -/
theorem exists_strict_separation_real {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hAc : Convex ℝ A) (hBc : Convex ℝ B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hdisj : Disjoint A B) :
    ∃ κ y₀ : ℝ, (∀ y ∈ A, 0 < κ * (y₀ - y)) ∧ (∀ y ∈ B, κ * (y₀ - y) < 0) := by
  have hA1 := hA.sInf_mem hAn
  have hA2 := hA.sSup_mem hAn
  have hB1 := hB.sInf_mem hBn
  have hB2 := hB.sSup_mem hBn
  have hAb := hA.bddBelow; have hAa := hA.bddAbove
  have hBb := hB.bddBelow; have hBa := hB.bddAbove
  by_cases h1 : sSup A < sInf B
  · refine ⟨1, (sSup A + sInf B) / 2, fun y hy => ?_, fun y hy => ?_⟩
    · have := le_csSup hAa hy; linarith
    · have := csInf_le hBb hy; linarith
  by_cases h2 : sSup B < sInf A
  · refine ⟨-1, (sSup B + sInf A) / 2, fun y hy => ?_, fun y hy => ?_⟩
    · have := csInf_le hAb hy; linarith
    · have := le_csSup hBa hy; linarith
  exfalso
  push Not at h1 h2
  set m := max (sInf A) (sInf B)
  have hmA : m ∈ A := hAc.ordConnected.out hA1 hA2
    ⟨le_max_left _ _, max_le (csInf_le_csSup hAn hAb hAa) h1⟩
  have hmB : m ∈ B := hBc.ordConnected.out hB1 hB2
    ⟨le_max_right _ _, max_le h2 (csInf_le_csSup hBn hBb hBa)⟩
  exact Set.disjoint_left.mp hdisj hmA hmB

/-- If `f ≤ 0` on a compact set and `g < 0` wherever `f = 0`, then
`f + δ g < 0` for some `δ > 0`. -/
theorem exists_pos_add_smul_neg {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {f g : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ n ∈ K, f n ≤ 0)
    (hfg : ∀ n ∈ K, f n = 0 → g n < 0) :
    ∃ δ > (0 : ℝ), ∀ n ∈ K, f n + δ * g n < 0 := by
  set K' := K ∩ {n | 0 ≤ g n}
  have hK' : IsCompact K' := hK.inter_right (isClosed_le continuous_const hg)
  rcases K'.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun n hn => ?_⟩
    have hgn : g n < 0 := by
      by_contra hc; push Not at hc
      exact (Set.eq_empty_iff_forall_notMem.mp he) n ⟨hn, hc⟩
    linarith [hf0 n hn]
  obtain ⟨n₁, hn₁, hmax₁⟩ := hK'.exists_isMaxOn hne hf.continuousOn
  obtain ⟨n₂, hn₂, hmax₂⟩ := hK'.exists_isMaxOn hne hg.continuousOn
  have hm : f n₁ < 0 := lt_of_le_of_ne (hf0 n₁ hn₁.1) (fun h => by
    have := hfg n₁ hn₁.1 h; linarith [hn₁.2.out])
  have hG : 0 ≤ g n₂ := hn₂.2
  refine ⟨-f n₁ / (g n₂ + 1), div_pos (by linarith) (by linarith), fun n hn => ?_⟩
  by_cases hgn : 0 ≤ g n
  · have h1 : f n ≤ f n₁ := hmax₁ (show n ∈ K' from ⟨hn, hgn⟩)
    have h2 : g n ≤ g n₂ := hmax₂ (show n ∈ K' from ⟨hn, hgn⟩)
    have h3 : -f n₁ / (g n₂ + 1) * g n ≤ -f n₁ / (g n₂ + 1) * g n₂ :=
      mul_le_mul_of_nonneg_left h2 (div_pos (by linarith) (by linarith)).le
    have h4 : -f n₁ / (g n₂ + 1) * g n₂ < -f n₁ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
    linarith
  · push Not at hgn
    have := mul_neg_of_pos_of_neg (div_pos (by linarith : 0 < -f n₁) (by linarith : 0 < g n₂ +
      1)) hgn
    linarith [hf0 n hn]

end Helpers

/-- A supporting normal tangent to the squash field sees a strictly inward shear. -/
private theorem shear_inner_neg_of_squash_tangent {F : Set ℝ²}
    {u a b c : ℝ²} (hu : u ≠ 0) {L μa μb : ℝ}
    {σ : ℝ² → ℝ} {w z : ℝ² → ℝ²} (haF : a ∈ F) (hbF : b ∈ F)
    (hmin' : ∀ q ∈ F, ⟪u, a⟫ ≤ ⟪u, q⟫) (hmax' : ∀ q ∈ F, ⟪u, q⟫ ≤ ⟪u, b⟫)
    (hinw : ∀ p ∈ F, ∀ μ > (0 : ℝ), IsInwardAt F p (μ • (c - p)))
    (hσa : ∀ p ∈ F, ⟪u, p⟫ = ⟪u, a⟫ → 0 < σ p)
    (hσb : ∀ p ∈ F, ⟪u, p⟫ = ⟪u, b⟫ → σ p < 0)
    (hμa0 : 0 < μa) (hμb0 : 0 < μb)
    (hza : z a = μa • (c - a)) (hzb : z b = μb • (c - b))
    (hwx : ∀ p, ⟪u, w p⟫ = 0) (hzu : ∀ p, ⟪u, z p⟫ = σ p)
    (hθ : ∀ p ∈ F, 0 ≤ (⟪u, p⟫ - ⟪u, a⟫) / L ∧ (⟪u, p⟫ - ⟪u, a⟫) / L ≤ 1)
    (hchord : ∀ p, p + w p =
      (1 - (⟪u, p⟫ - ⟪u, a⟫) / L) • a + ((⟪u, p⟫ - ⟪u, a⟫) / L) • b)
    (hzaff : ∀ θ : ℝ, z ((1 - θ) • a + θ • b) = (1 - θ) • z a + θ • z b) :
    ∀ p ∈ F, ∀ n : ℝ², ‖n‖ = 1 → (∀ q ∈ F, ⟪n, q - p⟫ ≤ 0) →
      ⟪n, w p⟫ = 0 → ⟪n, z p⟫ < 0 := by
  set ŵ := rot90 u with hŵ
  have hu2 : 0 < ‖u‖ ^ 2 := by positivity
  intro p hp n hn1 hN hf
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn1
  have hdec := norm_sq_smul_eq u n
  have hinner : ∀ x, ‖u‖ ^ 2 * ⟪n, x⟫ = ⟪u, n⟫ * ⟪u, x⟫ + ⟪ŵ, n⟫ * ⟪ŵ, x⟫ := by
    intro x
    rw [← real_inner_smul_left, hdec, inner_add_left, real_inner_smul_left,
      real_inner_smul_left]
  by_cases hy : ⟪ŵ, n⟫ = 0
  · have hx : ⟪u, n⟫ ≠ 0 := by
      intro hx
      apply hn0
      have := hdec
      rw [hx, hy, zero_smul, zero_smul, add_zero] at this
      exact (smul_eq_zero.mp this).resolve_left hu2.ne'
    have hz' : ‖u‖ ^ 2 * ⟪n, z p⟫ = ⟪u, n⟫ * σ p := by rw [hinner, hy, hzu]; ring
    have hq : ∀ q ∈ F, ⟪u, n⟫ * (⟪u, q⟫ - ⟪u, p⟫) ≤ 0 := by
      intro q hq
      have := hinner (q - p)
      rw [hy, zero_mul, add_zero] at this
      rw [← inner_sub_right, ← this]
      exact mul_nonpos_of_nonneg_of_nonpos hu2.le (hN q hq)
    have hfin : ‖u‖ ^ 2 * ⟪n, z p⟫ < 0 → ⟪n, z p⟫ < 0 := fun h => by
      by_contra hc; push Not at hc; have := mul_nonneg hu2.le hc; linarith
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have h1 := hq a haF
      have hpa : ⟪u, p⟫ = ⟪u, a⟫ := by
        refine le_antisymm ?_ (hmin' p hp)
        by_contra hc; push Not at hc
        have := mul_pos_of_neg_of_neg hneg (show ⟪u, a⟫ - ⟪u, p⟫ < 0 by linarith); linarith
      have h2 := hσa p hp hpa
      exact hfin (by rw [hz']; exact mul_neg_of_neg_of_pos hneg h2)
    · have h1 := hq b hbF
      have hpb : ⟪u, p⟫ = ⟪u, b⟫ := by
        refine le_antisymm (hmax' p hp) ?_
        by_contra hc; push Not at hc
        have := mul_pos hpos (show 0 < ⟪u, b⟫ - ⟪u, p⟫ by linarith); linarith
      have h2 := hσb p hp hpb
      exact hfin (by rw [hz']; exact mul_neg_of_pos_of_neg hpos h2)
  · -- `p` lies on the chord `[a, b]`
    have hwy : ⟪ŵ, w p⟫ = 0 := by
      have := hinner (w p)
      rw [hf, hwx] at this
      simp only [mul_zero, zero_add] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hy
    have hw0 : w p = 0 := eq_of_inner_eq_of_inner_rot90_eq hu (by rw [hwx, inner_zero_right])
      (by rw [← hŵ, hwy, inner_zero_right])
    obtain ⟨hθ0, hθ1⟩ := hθ p hp
    have hpw := hchord p
    generalize (⟪u, p⟫ - ⟪u, a⟫) / L = θ at hθ0 hθ1 hpw
    have hpθ : p = (1 - θ) • a + θ • b := by rwa [hw0, add_zero] at hpw
    set sn := ⟪n, b - a⟫
    have hna : ⟪n, a - p⟫ = -θ * sn := by
      rw [hpθ, show a - ((1 - θ) • a + θ • b) = -θ • (b - a) by module, real_inner_smul_right]
    have hnb : ⟪n, b - p⟫ = (1 - θ) * sn := by
      rw [hpθ, show b - ((1 - θ) • a + θ • b) = (1 - θ) • (b - a) by module,
        real_inner_smul_right]
    have h1 := hN a haF
    have h2 := hN b hbF
    rw [hna] at h1
    rw [hnb] at h2
    have hA : θ < 1 → ⟪n, z a⟫ < 0 := by
      intro hlt
      have hs : sn ≤ 0 := by
        by_contra hc; push Not at hc
        have := mul_pos (show 0 < 1 - θ by linarith) hc; linarith
      rw [hza]
      refine (hinw a haF μa hμa0).inner_neg hn0 (fun q hq => ?_)
      have := hN q hq
      rw [show q - a = (q - p) - (a - p) by abel, inner_sub_right, hna]
      have := mul_nonpos_of_nonneg_of_nonpos hθ0 hs
      linarith
    have hB : 0 < θ → ⟪n, z b⟫ < 0 := by
      intro hgt
      have hs : 0 ≤ sn := by
        by_contra hc; push Not at hc
        have := mul_pos hgt (show 0 < -sn by linarith); linarith
      rw [hzb]
      refine (hinw b hbF μb hμb0).inner_neg hn0 (fun q hq => ?_)
      have := hN q hq
      rw [show q - b = (q - p) - (b - p) by abel, inner_sub_right, hnb]
      have := mul_nonneg (show 0 ≤ 1 - θ by linarith) hs
      linarith
    rw [hpθ, hzaff, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rcases eq_or_lt_of_le hθ0 with h0 | h0
    · rw [← h0]; simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact hA (by rw [← h0]; exact zero_lt_one)
    rcases eq_or_lt_of_le hθ1 with h1' | h1'
    · rw [h1']; simp only [sub_self, zero_mul, one_mul, zero_add]
      exact hB (by rw [h1']; exact zero_lt_one)
    have h3 := mul_neg_of_pos_of_neg (show 0 < 1 - θ by linarith) (hA h1')
    have h4 := mul_neg_of_pos_of_neg h0 (hB h0)
    linarith

/-- Compactness of the unit normal sets gives one perturbation for all the vertices. -/
private theorem exists_uniform_inward_perturbation (W : Finset ℝ²) {F : Set ℝ²}
    (hW : (W : Set ℝ²) ⊆ F) {w z : ℝ² → ℝ²} (hwc : Continuous w) (hzc : Continuous z)
    (hwF : ∀ p ∈ F, p + w p ∈ F)
    (hdefect : ∀ p ∈ F, ∀ n : ℝ², ‖n‖ = 1 → (∀ q ∈ F, ⟪n, q - p⟫ ≤ 0) →
      ⟪n, w p⟫ = 0 → ⟪n, z p⟫ < 0) :
    ∃ δ > (0 : ℝ), ∀ p ∈ W, ∀ n : ℝ², n ≠ 0 →
      (∀ q ∈ F, ⟪n, q - p⟫ ≤ 0) → ⟪n, w p + δ • z p⟫ < 0 := by
  set Kp : ℝ² → Set ℝ² := fun p => {n | ‖n‖ = 1} ∩ ⋂ q ∈ F, {n | ⟪n, q - p⟫ ≤ 0} with hKp
  have hKpc : ∀ p, IsCompact (Kp p) := fun p =>
    (isCompact_sphere (0 : ℝ²) 1).of_isClosed_subset
      ((isClosed_eq continuous_norm continuous_const).inter
        (isClosed_biInter fun q _ => isClosed_le (continuous_id.inner continuous_const)
          continuous_const))
      (fun n hn => by simpa using hn.1)
  set K : Set (ℝ² × ℝ²) := ⋃ p ∈ (W : Set ℝ²), {p} ×ˢ Kp p
  have hKc : IsCompact K := W.finite_toSet.isCompact_biUnion fun p _ =>
    isCompact_singleton.prod (hKpc p)
  obtain ⟨δ, hδ, hδK⟩ := exists_pos_add_smul_neg hKc
    (f := fun x => ⟪x.2, w x.1⟫) (g := fun x => ⟪x.2, z x.1⟫)
    (continuous_snd.inner (hwc.comp continuous_fst))
    (continuous_snd.inner (hzc.comp continuous_fst))
    (by
      rintro ⟨p, n⟩ hx
      simp only [K, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff] at hx
      obtain ⟨p', hp', rfl, hn⟩ := hx
      have hpF : p ∈ F := hW hp'
      have := (Set.mem_iInter₂.mp hn.2) _ (hwF p hpF)
      simpa using this)
    (by
      rintro ⟨p, n⟩ hx hf
      simp only [K, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff] at hx
      obtain ⟨p', hp', rfl, hn⟩ := hx
      exact hdefect p (hW hp') n hn.1
        (fun q hq => Set.mem_iInter₂.mp hn.2 q hq) hf)
  refine ⟨δ, hδ, ?_⟩
  intro p hp n hn hN
  have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
  set n' := (1 / ‖n‖) • n
  have hn' : n' ∈ Kp p := by
    refine ⟨by simp [n', norm_smul, hnpos.ne'], Set.mem_iInter₂.mpr fun q hq => ?_⟩
    simp only [Set.mem_ofPred_eq, n', real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hN q hq)
  have := hδK (p, n') (Set.mem_biUnion hp ⟨rfl, hn'⟩)
  simp only [n', real_inner_smul_left] at this
  rw [inner_add_right, real_inner_smul_right]
  have h2 : 1 / ‖n‖ * (⟪n, w p⟫ + δ * ⟪n, z p⟫) < 0 := by linarith
  by_contra hc
  push Not at hc
  have := mul_nonneg (show 0 ≤ 1 / ‖n‖ by positivity) hc
  linarith

/-- **Lemma 3 (construction direction).** If `u` is not a double-normal
direction of the polygon `F = conv W`, there is an affine field
`p ↦ M p + b` with `⟪u, M u⟫ = 0` that points strictly into `F` at every
point of `W` (hence, being affine, at every point of `F`).

Construction (coordinates `x = ⟪u, ·⟫`, `y = ⟪rot90 u, ·⟫`): squash
vertically onto a chord `[a, b]` joining the two `x`-extreme faces, plus a
small multiple of a shear `(σ(y), τ(x, y))` with `σ(y) = κ (y₀ - y)`, `y₀`
strictly between the `y`-ranges of the two extreme faces. -/
theorem exists_admissible_inward_field (W : Finset ℝ²)
    (hW : (interior (convexHull ℝ (W : Set ℝ²))).Nonempty) (u : ℝ²) (hu : u ≠ 0)
    (hnd : ¬ IsDoubleNormalDir (convexHull ℝ (W : Set ℝ²)) u) :
    ∃ (M : ℝ² →ₗ[ℝ] ℝ²) (b : ℝ²), ⟪u, M u⟫ = 0 ∧
      ∀ p ∈ W, IsInwardAt (convexHull ℝ (W : Set ℝ²)) p (M p + b) := by
  set F := convexHull ℝ (W : Set ℝ²) with hFdef
  set ŵ := rot90 u with hŵ
  have hFc : IsCompact F := W.finite_toSet.isCompact_convexHull ℝ
  have hFconv : Convex ℝ F := convex_convexHull ℝ (W : Set ℝ²)
  obtain ⟨c, hc⟩ := hW
  have hcF : c ∈ F := interior_subset hc
  have huu : ⟪u, u⟫ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have huw : ⟪u, ŵ⟫ = 0 := inner_rot90_right_self u
  have hwu : ⟪ŵ, u⟫ = 0 := inner_rot90_left_self u
  have hww : ⟪ŵ, ŵ⟫ = ‖u‖ ^ 2 := inner_rot90_rot90 u
  -- every direction towards the interior point `c` is inward
  have hinw : ∀ p ∈ F, ∀ μ > (0 : ℝ), IsInwardAt F p (μ • (c - p)) := by
    intro p hp μ hμ
    refine ⟨min 1 (1 / μ), lt_min one_pos (by positivity), ?_⟩
    have h1 : p + min 1 (1 / μ) • μ • (c - p) =
        (1 - min 1 (1 / μ) * μ) • p + (min 1 (1 / μ) * μ) • c := by
      rw [smul_smul]; module
    rw [h1]
    have hle : min 1 (1 / μ) * μ ≤ 1 := by
      calc min 1 (1 / μ) * μ ≤ 1 / μ * μ := by gcongr; exact min_le_right _ _
        _ = 1 := by field_simp
    exact hFconv.combo_closure_interior_mem_interior (subset_closure hp) hc
      (by linarith) (mul_pos (lt_min one_pos (by positivity)) hμ) (by ring)
  have hcont : Continuous fun p : ℝ² => ⟪u, p⟫ := continuous_const.inner continuous_id
  obtain ⟨a, haF, hmin⟩ := hFc.exists_isMinOn ⟨c, hcF⟩ hcont.continuousOn
  obtain ⟨b, hbF, hmax⟩ := hFc.exists_isMaxOn ⟨c, hcF⟩ hcont.continuousOn
  have hmin' : ∀ q ∈ F, ⟪u, a⟫ ≤ ⟪u, q⟫ := fun q hq => hmin hq
  have hmax' : ∀ q ∈ F, ⟪u, q⟫ ≤ ⟪u, b⟫ := fun q hq => hmax hq
  have hca : ⟪u, a⟫ < ⟪u, c⟫ := by
    have := (hinw a haF 1 one_pos).inner_neg (neg_ne_zero.mpr hu) (fun q hq => by
      rw [inner_neg_left, inner_sub_right]; linarith [hmin' q hq])
    rw [one_smul, inner_neg_left, inner_sub_right] at this; linarith
  have hcb : ⟪u, c⟫ < ⟪u, b⟫ := by
    have := (hinw b hbF 1 one_pos).inner_neg hu (fun q hq => by
      rw [inner_sub_right]; linarith [hmax' q hq])
    rw [one_smul, inner_sub_right] at this; linarith
  set L := ⟪u, b⟫ - ⟪u, a⟫ with hL
  have hLpos : 0 < L := by linarith
  -- the two extreme faces and their `ŵ`-ranges
  set FA := F ∩ {p | ⟪u, p⟫ = ⟪u, a⟫}
  set FB := F ∩ {p | ⟪u, p⟫ = ⟪u, b⟫}
  have hFAc : IsCompact FA := hFc.inter_right (isClosed_eq hcont continuous_const)
  have hFBc : IsCompact FB := hFc.inter_right (isClosed_eq hcont continuous_const)
  have hFAv : Convex ℝ FA := hFconv.inter (convex_hyperplane
    (innerₛₗ ℝ u).isLinear _)
  have hFBv : Convex ℝ FB := hFconv.inter (convex_hyperplane
    (innerₛₗ ℝ u).isLinear _)
  obtain ⟨κ, y₀, hκA, hκB⟩ := exists_strict_separation_real
    (hFAc.image (innerₛₗ ℝ ŵ).continuous_of_finiteDimensional)
    (hFBc.image (innerₛₗ ℝ ŵ).continuous_of_finiteDimensional)
    (hFAv.linear_image (innerₛₗ ℝ ŵ)) (hFBv.linear_image (innerₛₗ ℝ ŵ))
    ⟨_, ⟨a, ⟨haF, rfl⟩, rfl⟩⟩ ⟨_, ⟨b, ⟨hbF, rfl⟩, rfl⟩⟩ (by
      rw [Set.disjoint_left]
      rintro _ ⟨a', ⟨ha'F, ha'⟩, rfl⟩ ⟨b', ⟨hb'F, hb'⟩, hy⟩
      simp only [innerₛₗ_apply_apply, Set.mem_ofPred_eq] at hy ha' hb'
      apply hnd
      have hba : b' - a' = (L / ‖u‖ ^ 2) • u := by
        apply eq_of_inner_eq_of_inner_rot90_eq hu
        · rw [inner_sub_right, inner_smul_right, huu, ha', hb']; field_simp; exact hL.symm
        · rw [inner_sub_right, inner_smul_right, hy, ← hŵ, hwu]; ring
      have hc0 : 0 ≤ L / ‖u‖ ^ 2 := by positivity
      refine ⟨a', ha'F, b', hb'F, fun h => by rw [h] at ha'; linarith,
        ⟨L / ‖u‖ ^ 2, hba⟩, fun q hq => ?_, fun q hq => ?_⟩
      · rw [hba, real_inner_smul_left, inner_sub_right]
        exact mul_nonpos_of_nonneg_of_nonpos hc0 (by linarith [hmax' q hq])
      · rw [show a' - b' = -(b' - a') by abel, hba, inner_neg_left, real_inner_smul_left,
          inner_sub_right]
        have := mul_nonneg hc0 (show 0 ≤ ⟪u, q⟫ - ⟪u, a'⟫ by linarith [hmin' q hq])
        linarith)
  -- the construction
  set σ : ℝ² → ℝ := fun p => κ * (y₀ - ⟪ŵ, p⟫) with hσ
  have hσa : ∀ p ∈ F, ⟪u, p⟫ = ⟪u, a⟫ → 0 < σ p := fun p hp hpa =>
    hκA _ ⟨p, ⟨hp, hpa⟩, rfl⟩
  have hσb : ∀ p ∈ F, ⟪u, p⟫ = ⟪u, b⟫ → σ p < 0 := fun p hp hpb =>
    hκB _ ⟨p, ⟨hp, hpb⟩, rfl⟩
  set μa := σ a / (⟪u, c⟫ - ⟪u, a⟫) with hμa
  set μb := σ b / (⟪u, c⟫ - ⟪u, b⟫) with hμb
  have hμa0 : 0 < μa := div_pos (hσa a haF rfl) (by linarith)
  have hμb0 : 0 < μb := div_pos_of_neg_of_neg (hσb b hbF rfl) (by linarith)
  set da := μa • (c - a)
  set db := μb • (c - b)
  have hab : a ≠ b := fun h => by rw [h] at hca; linarith
  have hab2 : 0 < ‖b - a‖ ^ 2 := by
    have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    positivity
  set k := (⟪ŵ, db⟫ - ⟪ŵ, da⟫) / ‖b - a‖ ^ 2
  -- squash `w` and shear `z`
  set w : ℝ² → ℝ² := fun p => a + ((⟪u, p⟫ - ⟪u, a⟫) / L) • (b - a) - p with hw
  set z : ℝ² → ℝ² := fun p => (σ p / ‖u‖ ^ 2) • u +
    ((⟪ŵ, da⟫ + k * ⟪b - a, p - a⟫) / ‖u‖ ^ 2) • ŵ with hz
  have hcaL : ⟪u, c⟫ - ⟪u, a⟫ ≠ 0 := by linarith
  have hcbL : ⟪u, c⟫ - ⟪u, b⟫ ≠ 0 := by linarith
  have hbaN : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hza : z a = da := by
    apply eq_of_inner_eq_of_inner_rot90_eq hu
    · simp only [hz, inner_add_right, real_inner_smul_right, huu, huw]
      simp only [da, real_inner_smul_right, inner_sub_right, hμa]
      field_simp
      ring
    · simp only [hz, ← hŵ, inner_add_right, real_inner_smul_right, hwu, hww, sub_self,
        inner_zero_right]
      field_simp
      ring
  have hzb : z b = db := by
    apply eq_of_inner_eq_of_inner_rot90_eq hu
    · simp only [hz, inner_add_right, real_inner_smul_right, huu, huw]
      simp only [db, real_inner_smul_right, inner_sub_right, hμb]
      field_simp
      ring
    · simp only [hz, ← hŵ, inner_add_right, real_inner_smul_right, hwu, hww,
        real_inner_self_eq_norm_sq]
      simp only [k, ← inner_sub_right]
      field_simp
      rw [inner_sub_right]
      ring
  -- basic facts about `w` and `z`
  have hubaL : ⟪u, b - a⟫ = L := by rw [inner_sub_right]
  have hwx : ∀ p, ⟪u, w p⟫ = 0 := by
    intro p
    simp only [hw, inner_add_right, inner_sub_right, real_inner_smul_right]
    rw [← hL]
    field_simp
    ring
  have hθ : ∀ p ∈ F, 0 ≤ (⟪u, p⟫ - ⟪u, a⟫) / L ∧ (⟪u, p⟫ - ⟪u, a⟫) / L ≤ 1 := by
    intro p hp
    refine ⟨div_nonneg (by linarith [hmin' p hp]) hLpos.le, ?_⟩
    rw [div_le_one hLpos]; linarith [hmax' p hp]
  have hchord (p : ℝ²) :
      p + w p = (1 - (⟪u, p⟫ - ⟪u, a⟫) / L) • a + ((⟪u, p⟫ - ⟪u, a⟫) / L) • b := by
    simp only [hw]
    module
  have hwF : ∀ p ∈ F, p + w p ∈ F := by
    intro p hp
    obtain ⟨h0, h1⟩ := hθ p hp
    rw [hchord]
    exact hFconv haF hbF (by linarith) h0 (by ring)
  have hzu : ∀ p, ⟪u, z p⟫ = σ p := by
    intro p
    simp only [hz, inner_add_right, real_inner_smul_right, huu, huw]
    field_simp
    ring
  have hzw : ∀ p, ⟪ŵ, z p⟫ = ⟪ŵ, da⟫ + k * ⟪b - a, p - a⟫ := by
    intro p
    simp only [hz, inner_add_right, real_inner_smul_right, hwu, hww]
    field_simp
    ring
  have hzaff : ∀ θ : ℝ, z ((1 - θ) • a + θ • b) = (1 - θ) • z a + θ • z b := by
    intro θ
    apply eq_of_inner_eq_of_inner_rot90_eq hu
    · simp only [inner_add_right, real_inner_smul_right, hzu, hσ]; ring
    · simp only [← hŵ, inner_add_right, real_inner_smul_right, hzw, inner_sub_right]; ring
  have hdefect := shear_inner_neg_of_squash_tangent hu haF hbF hmin' hmax' hinw
    hσa hσb hμa0 hμb0 hza hzb hwx hzu hθ hchord hzaff
  have hwc : Continuous w := by simp only [hw]; fun_prop
  have hzc : Continuous z := by simp only [hz, hσ]; fun_prop
  obtain ⟨δ, _, hδW⟩ := exists_uniform_inward_perturbation W (subset_convexHull ℝ _)
    hwc hzc hwF hdefect
  -- the linear part and the constant
  set M : ℝ² →ₗ[ℝ] ℝ² := (1 / L) • (innerₛₗ ℝ u).smulRight (b - a) - LinearMap.id +
    δ • ((-κ / ‖u‖ ^ 2) • (innerₛₗ ℝ ŵ).smulRight u +
      (k / ‖u‖ ^ 2) • (innerₛₗ ℝ (b - a)).smulRight ŵ) with hMdef
  have hM : ∀ p, M p = (⟪u, p⟫ / L) • (b - a) - p +
      δ • ((-κ * ⟪ŵ, p⟫ / ‖u‖ ^ 2) • u + (k * ⟪b - a, p⟫ / ‖u‖ ^ 2) • ŵ) := by
    intro p
    simp only [hMdef, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.smulRight_apply, innerₛₗ_apply_apply, LinearMap.id_apply]
    simp only [smul_smul]
    congr 1
    · congr 1; ring_nf
    · congr 1; congr 1 <;> congr 1 <;> ring
  have hv : ∀ p, M p + (w 0 + δ • z 0) = w p + δ • z p := by
    intro p
    rw [hM]
    simp only [hw, hz, hσ, inner_zero_right, inner_sub_right, sub_zero, zero_sub]
    module
  refine ⟨M, w 0 + δ • z 0, ?_, fun p hp => ?_⟩
  · rw [hM]
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right, huu, huw, hwu, hubaL]
    field_simp
    ring
  · rw [hv]
    have hpF : p ∈ F := subset_convexHull ℝ _ hp
    refine isInwardAt_of_forall_normal hFconv ⟨c, hc⟩ (subset_closure hpF) _ (fun n hn hN => ?_)
    exact hδW p hp n hn hN


/-- **L4, transfer step, normal-vector form** (what the proofs use): `F` lies
in the plane `⟪N, x⟫ = h` with `N 2 ≠ 0` (not vertical), and `δ` is a
horizontal direction of that plane. -/
theorem isDoubleNormalDir_proj_iff' (N : ℝ³) (hN : N 2 ≠ 0) (h : ℝ) (F : Set ℝ³)
    (hF : ∀ x ∈ F, ⟪N, x⟫ = h) (δ : ℝ³) (hδ : ⟪N, δ⟫ = 0) (hδ2 : δ 2 = 0) :
    IsDoubleNormalDir F δ ↔ IsDoubleNormalDir (projXy '' F) (projXy δ) := by
  have hsub : ∀ x ∈ F, ∀ y ∈ F, ⟪N, y - x⟫ = 0 := fun x hx y hy => by
    rw [inner_sub_right, hF x hx, hF y hy, sub_self]
  constructor
  · rintro ⟨a, ha, b, hb, hab, ⟨t, ht⟩, hB, hA⟩
    have hh : (b - a) 2 = 0 := by rw [ht]; simp [hδ2]
    have hh' : (a - b) 2 = 0 := by
      rw [show a - b = -(b - a) by abel]; simp only [PiLp.neg_apply, hh, neg_zero]
    refine ⟨projXy a, ⟨a, ha, rfl⟩, projXy b, ⟨b, hb, rfl⟩, fun h => hab ?_,
      ⟨t, by rw [← proj_xy_sub', ht, proj_xy_smul']⟩, ?_, ?_⟩
    · have := eq_zero_of_proj_xy_eq_zero hN (hsub a ha b hb)
        (by rw [proj_xy_sub', h, sub_self])
      exact (sub_eq_zero.mp this).symm
    · rintro _ ⟨q, hq, rfl⟩
      rw [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh]; exact hB q hq
    · rintro _ ⟨q, hq, rfl⟩
      rw [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh']; exact hA q hq
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hab, ⟨t, ht⟩, hB, hA⟩
    have hba : b - a = t • δ := by
      have := eq_zero_of_proj_xy_eq_zero (z := b - a - t • δ) hN
        (by rw [inner_sub_right, inner_smul_right, hsub a ha b hb, hδ, mul_zero, sub_zero])
        (by rw [proj_xy_sub', proj_xy_sub', proj_xy_smul', ht, sub_self])
      exact sub_eq_zero.mp this
    have hh : (b - a) 2 = 0 := by rw [hba]; simp [hδ2]
    have hh' : (a - b) 2 = 0 := by
      rw [show a - b = -(b - a) by abel]; simp only [PiLp.neg_apply, hh, neg_zero]
    refine ⟨a, ha, b, hb, fun h => hab (by rw [h]), ⟨t, hba⟩, fun q hq => ?_, fun q hq => ?_⟩
    · have := hB (projXy q) ⟨q, hq, rfl⟩
      rwa [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh] at this
    · have := hA (projXy q) ⟨q, hq, rfl⟩
      rwa [← proj_xy_sub', ← proj_xy_sub', inner_proj_xy_of_horizontal hh'] at this

end Minimality

end RupertMinimality
