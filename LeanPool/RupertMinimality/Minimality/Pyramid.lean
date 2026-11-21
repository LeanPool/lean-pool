/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Coplanar

/-! # Pyramid -/

@[expose] public section

namespace RupertMinimality

/-!
# The waist lemma and the bipyramid theorem

`isRupert_of_waist`: Theorem 5 when the silhouette plane is `z = 0`: the
points of `Q` project, along an oblique direction `u₀`, into the interior of
the waist polygon `conv (projXy P)`.  The proof tilts `u₀` to a nearby
generic view (avoiding the finitely many bad planes `badNormals`), rotates it
to the standard view, and applies `exists_firstOrderInward_of_plane` (L2, L3,
L4) and L1.  `isRupert_bipyramid` is the case `Q = {D, E}`, `u₀ = E - D`.
The frame-free form is `isRupert_of_crossing` (Crossing.lean).
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Filter

/-! ### Helpers for the bipyramid theorem -/

/-- The horizontal lift `q ↦ (q, 0)`. -/
noncomputable def liftL : ℝ² →ₗ[ℝ] ℝ³ where
  toFun q := !₂[q 0, q 1, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

theorem liftL_proj_xy {p : ℝ³} (hp : p 2 = 0) : liftL (projXy p) = p := by
  ext i; fin_cases i <;> simp [liftL, projXy, hp]

theorem proj_xy_ez : projXy ez = 0 := by
  ext i; fin_cases i <;> simp [projXy, ez]

theorem inner_ez (x : ℝ³) : ⟪x, ez⟫ = x 2 := by
  simp [ez, PiLp.inner_apply]

/-- Horizontal rotation by +90° of the horizontal part. -/
noncomputable def rot90h (d : ℝ³) : ℝ³ := !₂[-d 1, d 0, 0]

/-- The finitely many normals of the planes of bad views of a waist `P`. -/
noncomputable def badNormals (P : Finset ℝ³) : Finset ℝ³ :=
  (((P ×ˢ P).filter (fun q => q.1 ≠ q.2)).image (fun q => q.2 - q.1)) ∪
  (((P ×ˢ P).filter (fun q => q.1 ≠ q.2)).image (fun q => rot90h (q.2 - q.1)))

theorem badNormals_spec {P : Finset ℝ³} (hP : ∀ p ∈ P, p 2 = 0) :
    ∀ l ∈ badNormals P, l 2 = 0 ∧ (l 0 ≠ 0 ∨ l 1 ≠ 0) := by
  intro l hl
  simp only [badNormals, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product] at hl
  rcases hl with ⟨⟨w, w'⟩, ⟨⟨hw, hw'⟩, hne⟩, rfl⟩ | ⟨⟨w, w'⟩, ⟨⟨hw, hw'⟩, hne⟩, rfl⟩
  · refine ⟨by simp [hP w hw, hP w' hw'], ?_⟩
    by_contra hc
    push Not at hc
    apply hne
    have h0 := hc.1; have h1 := hc.2
    simp only [PiLp.sub_apply] at h0 h1
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
    · simp [hP w hw, hP w' hw']
  · refine ⟨by simp [rot90h], ?_⟩
    by_contra hc
    push Not at hc
    apply hne
    have h0 := hc.1; have h1 := hc.2
    simp only [rot90h, PiLp.sub_apply] at h0 h1
    simp at h0 h1
    ext i; fin_cases i
    · simp; linarith
    · simp; linarith
    · simp [hP w hw, hP w' hw']

/-- A view avoiding the bad planes is orthogonal to no double normal of the
waist. -/
theorem inner_ne_zero_of_badNormals {P : Finset ℝ³} (hP : ∀ p ∈ P, p 2 = 0) (u : ℝ³)
    (hu : ∀ l ∈ badNormals P, ⟪l, u⟫ ≠ 0) (δ : ℝ³)
    (hδ : IsDoubleNormalDir (convexHull ℝ (P : Set ℝ³)) δ) : ⟪δ, u⟫ ≠ 0 := by
  have hδ' := hδ
  obtain ⟨w, hw, w', hw', hne, hcase⟩ := isDoubleNormalDir_convexHull_cases P δ hδ
  have hmem : ∀ {f : ℝ³ × ℝ³ → ℝ³}, f (w, w') ∈ ((P ×ˢ P).filter (fun q => q.1 ≠ q.2)).image f :=
    fun {f} => Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw, hw'⟩,
      hne⟩)
  rcases hcase with ⟨t, ht⟩ | hperp
  · have h1 := hu (w' - w) (Finset.mem_union_left _ hmem)
    rw [ht, real_inner_smul_left] at h1
    exact right_ne_zero_of_mul h1
  · -- `δ` is horizontal
    obtain ⟨a, ha, b, hb, hab, ⟨s, hs⟩, _⟩ := hδ'
    have hconv : convexHull ℝ (P : Set ℝ³) ⊆ {x | x 2 = 0} :=
      convexHull_min (fun p hp => hP p hp)
        (convex_hyperplane (show IsLinearMap ℝ (fun x : ℝ³ => x 2) from
          ⟨fun x y => rfl, fun c x => rfl⟩) 0)
    have hs0 : s ≠ 0 := by rintro rfl; apply hab; rw [zero_smul, sub_eq_zero] at hs; exact hs.symm
    have hδ2 : δ 2 = 0 := by
      have := congrArg (fun v : ℝ³ => v 2) hs
      have ha2 : a 2 = 0 := hconv ha
      have hb2 : b 2 = 0 := hconv hb
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, ha2, hb2, sub_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hs0
    have h2 := hu (rot90h (w' - w)) (Finset.mem_union_right _ hmem)
    set d := w' - w
    have hd2 : d 2 = 0 := by simp [d, hP w hw, hP w' hw']
    have hdne : d 0 ≠ 0 ∨ d 1 ≠ 0 := by
      by_contra hc; push Not at hc
      have h0 := hc.1; have h1 := hc.2
      simp only [d, PiLp.sub_apply] at h0 h1
      exact hne (by
        ext i; fin_cases i
        · simp; linarith
        · simp; linarith
        · simp [hP w hw, hP w' hw'])
    have hN : d 0 ^ 2 + d 1 ^ 2 ≠ 0 := by
      rcases hdne with h | h <;> positivity
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial,
      hδ2, hd2] at hperp ⊢
    intro h0
    -- `δ ⟂ d` and `δ ⟂ u` force `δ = 0`
    have hp' : δ 0 * d 0 + δ 1 * d 1 = 0 := by linear_combination hperp
    have h0' : δ 0 * u 0 + δ 1 * u 1 = 0 := by linear_combination h0
    have h2' : -(d 1 * u 0) + d 0 * u 1 ≠ 0 := by
      intro h
      apply h2
      simpa [rot90h, PiLp.inner_apply, Fin.sum_univ_three, mul_comm] using h
    have key : (-(δ 0 * d 1) + δ 1 * d 0) * (-(d 1 * u 0) + d 0 * u 1) = 0 := by
      linear_combination (d 0 ^ 2 + d 1 ^ 2) * h0' - (d 0 * u 0 + d 1 * u 1) * hp'
    have hc : -(δ 0 * d 1) + δ 1 * d 0 = 0 := (mul_eq_zero.mp key).resolve_right h2'
    have e0 : δ 0 = 0 := by
      have : δ 0 * (d 0 ^ 2 + d 1 ^ 2) = 0 := by
        linear_combination d 0 * hp' - d 1 * hc
      exact (mul_eq_zero.mp this).resolve_right hN
    have e1 : δ 1 = 0 := by
      have : δ 1 * (d 0 ^ 2 + d 1 ^ 2) = 0 := by
        linear_combination d 1 * hp' + d 0 * hc
      exact (mul_eq_zero.mp this).resolve_right hN
    apply hab
    have : δ = 0 := by ext i; fin_cases i <;> simp [e0, e1, hδ2]
    rw [this, smul_zero, sub_eq_zero] at hs
    exact hs.symm

/-- Some horizontal direction is off all bad planes. -/
theorem exists_avoid_badNormals {P : Finset ℝ³} (hP : ∀ p ∈ P, p 2 = 0) :
    ∃ ζ : ℝ³, ∀ l ∈ badNormals P, ⟪l, ζ⟫ ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset ((badNormals P).image (fun l => -(l 0) / l 1))
  refine ⟨!₂[1, s, 0], fun l hl => ?_⟩
  obtain ⟨h2, h01⟩ := badNormals_spec hP l hl
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  simp only [Fin.isValue, Matrix.cons_val_zero, one_mul, Matrix.cons_val_one,
    Matrix.cons_val, zero_mul, add_zero, ne_eq]
  intro h0
  by_cases h1 : l 1 = 0
  · rw [h1, mul_zero, add_zero] at h0
    rcases h01 with h | h
    · exact h h0
    · exact h h1
  · apply hs
    refine Finset.mem_image.mpr ⟨l, hl, ?_⟩
    field_simp
    linarith

/-- **Waist lemma** (Theorem 5 with the plane `z = 0`, frame-specific form).
`P` lies in `z = 0`, and along the oblique direction `u₀` every point of `Q`
projects into the interior of the waist polygon `conv (projXy P)`.  Then
`P ∪ Q` is Rupert (at a slightly tilted generic view). -/
theorem isRupert_of_waist (P Q : Finset ℝ³) (hP : ∀ p ∈ P, p 2 = 0)
    (hint : (interior (convexHull ℝ ((P.image projXy : Finset ℝ²) : Set ℝ²))).Nonempty)
    (u₀ : ℝ³) (hu₀ : u₀ 2 ≠ 0)
    (hQ : ∀ q ∈ Q, projXy (q - (q 2 / u₀ 2) • u₀) ∈
      interior (convexHull ℝ ((P.image projXy : Finset ℝ²) : Set ℝ²))) :
    IsRupert (P ∪ Q) := by
  classical
  set V := P ∪ Q with hVdef
  set Fp := convexHull ℝ ((P.image projXy : Finset ℝ²) : Set ℝ²) with hFp
  set I := interior Fp with hI
  -- parallel projection along `u` onto the waist plane, in screen coordinates
  set π : ℝ³ → ℝ³ → ℝ² := fun u x => projXy (x - (x 2 / u 2) • u) with hπ
  have hc2 : Continuous fun u : ℝ³ => u 2 := (EuclideanSpace.proj (2 : Fin 3)).continuous
  have hcπ : ∀ x : ℝ³, ContinuousAt (fun u => π u x) u₀ := by
    intro x
    have h1 : ContinuousAt (fun u : ℝ³ => x - (x 2 / u 2) • u) u₀ :=
      continuousAt_const.sub ((continuousAt_const.div hc2.continuousAt
        hu₀).smul continuousAt_id)
    exact (projL.continuous_of_finiteDimensional.continuousAt).comp h1
  have hev : ∀ᶠ u in 𝓝 u₀, u 2 ≠ 0 ∧ ∀ q ∈ Q, π u q ∈ I := by
    refine (hc2.continuousAt.eventually_ne hu₀).and ?_
    rw [eventually_all_finset]
    exact fun q hq => (hcπ q).eventually (isOpen_interior.mem_nhds (hQ q hq))
  -- a generic tilt
  obtain ⟨ζ, hζ⟩ := exists_avoid_badNormals hP
  have hline : Tendsto (fun t : ℝ => u₀ + t • ζ) (𝓝 0) (𝓝 u₀) := by
    have : Continuous fun t : ℝ => u₀ + t • ζ := by fun_prop
    simpa using this.tendsto 0
  have hgen_ev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ l ∈ badNormals P, ⟪l, u₀ + t • ζ⟫ ≠ 0 := by
    rw [eventually_all_finset]
    intro l hl
    set t₀ := -⟪l, u₀⟫ / ⟪l, ζ⟫
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ t₀ := by
      by_cases h0 : t₀ = 0
      · rw [h0]; exact self_mem_nhdsWithin
      · exact (eventually_ne_nhds (Ne.symm h0)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev'] with t ht
    rw [inner_add_right, real_inner_smul_right]
    intro h0
    apply ht
    have := hζ l hl
    simp only [t₀]
    field_simp
    linarith
  obtain ⟨t, hgen_t, hu2, hπQ⟩ :=
    (hgen_ev.and ((hline.eventually hev).filter_mono nhdsWithin_le_nhds)).exists
  set u := u₀ + t • ζ with hu
  have hu0 : u ≠ 0 := fun h => hu2 (by rw [h]; rfl)
  -- rotate the view `u` to the standard view
  obtain ⟨R, hR, r, hr, hRu⟩ := exists_rotation_to_ez u hu0
  set f := so3Isometry hR with hf
  have hfx : ∀ x, f x = R.toEuclideanLin x := fun x => rfl
  have hfinv : f (r⁻¹ • u) = ez := by
    rw [map_smul, hfx, hRu, smul_smul, inv_mul_cancel₀ hr, one_smul]
  have inner_ez' : ∀ x : ℝ³, ⟪ez, x⟫ = x 2 := fun x => by rw [real_inner_comm, inner_ez]
  set N := f ez with hN
  have hN2 : N 2 ≠ 0 := by
    rw [← inner_ez, ← hfinv, hN, f.inner_map_map, real_inner_smul_right, inner_ez']
    exact mul_ne_zero (inv_ne_zero hr) hu2
  -- the screen map of the waist plane
  set T : ℝ² →ₗ[ℝ] ℝ² := projL ∘ₗ f.toLinearEquiv.toLinearMap ∘ₗ liftL with hT
  have hTapp : ∀ q, T q = projXy (f (liftL q)) := fun q => rfl
  have hTπ : ∀ x : ℝ³, projXy (R.toEuclideanLin x) = T (π u x) := by
    intro x
    have hz : (x - (x 2 / u 2) • u) 2 = 0 := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; field_simp; ring
    rw [hTapp, liftL_proj_xy hz, map_sub, map_smul, hfx, hfx, hRu, proj_xy_sub',
      proj_xy_smul', proj_xy_smul', proj_xy_ez, smul_zero, smul_zero, sub_zero]
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have hq' : projXy (f (liftL q)) = 0 := hq
    set y := f (liftL q)
    have hy : y = y 2 • ez := by
      have h0 := congrArg (fun v : ℝ² => v 0) hq'
      have h1 := congrArg (fun v : ℝ² => v 1) hq'
      simp [projXy] at h0 h1
      ext i; fin_cases i <;> simp [ez, h0, h1]
    have hlift : liftL q = (y 2 * r⁻¹) • u := by
      apply f.injective
      rw [show (y 2 * r⁻¹) • u = y 2 • (r⁻¹ • u) by rw [smul_smul], map_smul, hfinv]
      exact hy
    have hl2 : (liftL q) 2 = 0 := by simp [liftL]
    rw [hlift] at hl2
    simp only [PiLp.smul_apply, smul_eq_mul] at hl2
    have hc : y 2 * r⁻¹ = 0 := (mul_eq_zero.mp hl2).resolve_right hu2
    have : liftL q = 0 := by rw [hlift, hc, zero_smul]
    have h0 := congrArg (fun v : ℝ³ => v 0) this
    have h1 := congrArg (fun v : ℝ³ => v 1) this
    simp [liftL] at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  set Te : ℝ² ≃L[ℝ] ℝ² :=
    (LinearMap.linearEquivOfInjective T hTinj rfl).toContinuousLinearEquiv with hTe
  have hTe : ∀ q, Te q = T q := fun q => rfl
  -- the rotated waist polygon is `T '' Fp`
  have hW'img : (((P.image R.toEuclideanLin).image projXy : Finset ℝ²) : Set ℝ²) =
      T '' ((P.image projXy : Finset ℝ²) : Set ℝ²) := by
    ext y
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨projXy p, ⟨p, hp, rfl⟩, ?_⟩
      rw [hTapp, liftL_proj_xy (hP p hp)]; rfl
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨R.toEuclideanLin p, ⟨p, hp, rfl⟩, ?_⟩
      rw [hTapp, liftL_proj_xy (hP p hp)]; rfl
  have hconvW' : convexHull ℝ (((P.image R.toEuclideanLin).image projXy : Finset ℝ²) : Set ℝ²)
      = Te '' Fp := by
    rw [hW'img, ← LinearMap.image_convexHull, hFp]
    rfl
  have hintW' : interior (convexHull ℝ
      (((P.image R.toEuclideanLin).image projXy : Finset ℝ²) : Set ℝ²)) = Te '' I := by
    rw [hconvW', hI]
    exact (Te.toHomeomorph.image_interior Fp).symm
  -- apply the plane form of Theorem 5 to the rotated solid
  have hsub : P.image R.toEuclideanLin ⊆ V.image R.toEuclideanLin :=
    Finset.image_subset_image Finset.subset_union_left
  obtain ⟨ω, τ, hfo⟩ := exists_firstOrderInward_of_plane (V.image R.toEuclideanLin)
    (P.image R.toEuclideanLin) hsub N 0 hN2
    (by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      rw [hN, ← hfx, f.inner_map_map, inner_ez', hP p hp])
    (by rw [hintW']; obtain ⟨x, hx⟩ := hint; exact ⟨_, Set.mem_image_of_mem _ hx⟩)
    (by
      intro v hv hvW
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      have hxP : x ∉ P := fun h => hvW (Finset.mem_image_of_mem _ h)
      rw [hintW', hTπ x]
      refine ⟨π u x, ?_, hTe _⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · exact absurd hx hxP
      · exact hπQ x hx)
    (by
      intro δ' hδ'
      have hconv : convexHull ℝ ((P.image R.toEuclideanLin : Finset ℝ³) : Set ℝ³) =
          f '' convexHull ℝ (P : Set ℝ³) := by
        rw [Finset.coe_image]
        exact (f.toLinearEquiv.toLinearMap.image_convexHull _).symm
      rw [hconv, show δ' = f (f.symm δ') by simp,
        isDoubleNormalDir_image_iff] at hδ'
      rw [show δ' = f (f.symm δ') by simp, ← inner_ez, ← hfinv, f.inner_map_map,
        real_inner_smul_right]
      exact mul_ne_zero (inv_ne_zero hr)
        (inner_ne_zero_of_badNormals hP u hgen_t _ hδ'))
  exact isRupert_of_firstOrderInward_image V R hR ω τ hfo

/-- **Bipyramid theorem** (Tom's challenge; Cor. 5.4 with the waist in
`z = 0`).  `P` is a finite set in the plane `z = 0`, `D` is above and `E`
below it, and the point `X = D + (D₂ / (D₂ - E₂)) (E - D)` where the segment
`DE` crosses the plane projects into the interior of the waist polygon
`conv (projXy P)`.  Then `insert D (insert E P)` is Rupert, for any number of
waist points.  (The view `E - D` itself may be face-on, `g = 0`; the proof
uses a slightly tilted generic view `E - D + t ζ`.) -/
theorem isRupert_bipyramid (P : Finset ℝ³) (hP : ∀ p ∈ P, p 2 = 0) (D E : ℝ³)
    (hD : 0 < D 2) (hE : E 2 < 0)
    (hX : projXy (D + (D 2 / (D 2 - E 2)) • (E - D)) ∈
      interior (convexHull ℝ ((P.image projXy : Finset ℝ²) : Set ℝ²))) :
    IsRupert (insert D (insert E P)) := by
  classical
  have hne : E 2 - D 2 ≠ 0 := by linarith
  have hne' : -E 2 + D 2 ≠ 0 := by linarith
  have hne'' : D 2 - E 2 ≠ 0 := by linarith
  have hu2 : (E - D) 2 = E 2 - D 2 := by simp
  have hV : insert D (insert E P) = P ∪ {D, E} := by
    ext x; simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]; tauto
  rw [hV]
  refine isRupert_of_waist P {D, E} hP ⟨_, hX⟩ (E - D) (by rw [hu2]; exact hne) ?_
  intro q hq
  rw [Finset.mem_insert, Finset.mem_singleton] at hq
  convert hX using 2
  rcases hq with rfl | rfl <;>
    (rw [hu2]; ext i; fin_cases i <;> simp <;> field_simp <;> ring)

end Minimality

end RupertMinimality
