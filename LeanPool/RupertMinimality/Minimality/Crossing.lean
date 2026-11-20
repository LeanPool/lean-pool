/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Pyramid
public import LeanPool.RupertMinimality.Minimality.Planes

/-! # Crossing -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 5 in an arbitrary frame; pyramids (Cor. 5.3) and Cor. 5.4

`isRupert_of_crossing` is the coplanar-silhouette theorem in the form used by
all corollaries: `W ⊆ V` lies on a plane `⟪N, x⟫ = c` and contains an
affinely independent triple, `u₀` is not parallel to the plane, and the line
through every other point of `V` in direction `u₀` meets the plane in a
combination of `W` with all weights positive (a point of `relint (conv W)`).
It is reduced to the waist lemma `isRupert_of_waist` by a rigid motion taking
the plane to `z = 0`.
-/

namespace Minimality

open scoped RealInnerProductSpace
open Module

/-- **Theorem 5, frame-free form.** -/
theorem isRupert_of_crossing (V W : Finset ℝ³) (hWV : W ⊆ V) (N : ℝ³) (c : ℝ)
    (hWN : ∀ w ∈ W, ⟪N, w⟫ = c) {a b d : ℝ³} (ha : a ∈ W) (hb : b ∈ W) (hd : d ∈ W)
    (hind : AffineIndependent ℝ ![a, b, d]) (u₀ : ℝ³) (hu₀ : ⟪N, u₀⟫ ≠ 0)
    (hcross : ∀ v ∈ V, v ∉ W → ∃ t : ℝ, ∃ μ : ℝ³ → ℝ, (∀ w ∈ W, 0 < μ w) ∧
      ∑ w ∈ W, μ w = 1 ∧ v + t • u₀ = ∑ w ∈ W, μ w • w) :
    IsRupert V := by
  classical
  have hN0 : N ≠ 0 := by rintro rfl; simp at hu₀
  obtain ⟨R, hR, n, hn, hRN⟩ := exists_rotation_to_ez N hN0
  set f := so3Isometry hR with hf
  have hfx : ∀ x, f x = R.toEuclideanLin x := fun x => rfl
  have hfN : f (n⁻¹ • N) = ez := by
    rw [map_smul, hfx, hRN, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hz : ∀ x : ℝ³, (f x) 2 = n⁻¹ * ⟪N, x⟫ := by
    intro x
    rw [← inner_ez, ← hfN, f.inner_map_map, real_inner_smul_right, real_inner_comm]
  set k : ℝ := -(n⁻¹ * c) with hk
  let G : ℝ³ →ᵃ[ℝ] ℝ³ := (AffineEquiv.constVAdd ℝ ℝ³ (k • ez)).toAffineMap.comp
    f.toLinearEquiv.toLinearMap.toAffineMap
  have hG : ∀ x, G x = k • ez + f x := fun x => by simp [G, vadd_eq_add]
  have hGinj : Function.Injective G := by
    intro x y h; rw [hG, hG] at h; exact f.injective (add_left_cancel h)
  have hez2 : ez 2 = 1 := by simp [ez]
  have hGz : ∀ w ∈ W, (G w) 2 = 0 := by
    intro w hw
    rw [hG, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hez2, hz, hWN w hw, hk]
    try ring
  -- reduce to the rigidly moved solid
  apply isRupert_of_isRupert_image_rotation R hR
  apply isRupert_of_isRupert_image_add (k • ez)
  have hVimg : (V.image R.toEuclideanLin).image (fun x => k • ez + x) = V.image G := by
    rw [Finset.image_image]; congr 1
  rw [hVimg]
  set P := W.image G
  set Q := (V.filter (· ∉ W)).image G
  have hPQ : V.image G = P ∪ Q := by
    rw [← Finset.image_union]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx; by_cases hxW : x ∈ W
      · exact Or.inl hxW
      · exact Or.inr ⟨hx, hxW⟩
    · rintro (hx | ⟨hx, _⟩)
      · exact hWV hx
      · exact hx
  rw [hPQ]
  have hP : ∀ p ∈ P, p 2 = 0 := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp
    exact hGz w hw
  -- the waist polygon is solid
  have hint : (interior (convexHull ℝ ((P.image projXy : Finset ℝ²) : Set ℝ²))).Nonempty := by
    have h1 : AffineIndependent ℝ (G ∘ ![a, b, d]) := hind.map' G hGinj
    have hcomp : (liftL.toAffineMap ∘ (projXy ∘ G ∘ ![a, b, d])) = G ∘ ![a, b, d] := by
      funext i
      fin_cases i <;>
        simp [liftL_proj_xy (hGz _ ha), liftL_proj_xy (hGz _ hb), liftL_proj_xy (hGz _ hd)]
    have h2 : AffineIndependent ℝ (projXy ∘ G ∘ ![a, b, d]) :=
      AffineIndependent.of_comp liftL.toAffineMap (by rw [hcomp]; exact h1)
    have hspan : affineSpan ℝ (Set.range (projXy ∘ G ∘ ![a, b, d])) = ⊤ :=
      (h2.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp)
    have := (interior_convexHull_nonempty_iff_affineSpan_eq_top).mpr hspan
    refine this.mono (interior_mono (convexHull_mono ?_))
    rintro _ ⟨i, rfl⟩
    simp only [Finset.coe_image, Function.comp_apply]
    refine ⟨G (![a, b, d] i), Finset.mem_coe.mpr (Finset.mem_image_of_mem G ?_), rfl⟩
    fin_cases i <;> simp [ha, hb, hd]
  have hu₀' : (f u₀) 2 ≠ 0 := by rw [hz]; exact mul_ne_zero (inv_ne_zero hn) hu₀
  refine isRupert_of_waist P Q hP hint (f u₀) hu₀' ?_
  intro q hq
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hvV, hvW⟩ := Finset.mem_filter.mp hv
  obtain ⟨t, μ, hμ, hμ1, hvt⟩ := hcross v hvV hvW
  have key : G v + t • f u₀ = ∑ w ∈ W, μ w • G w := by
    simp only [hG, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hμ1, one_smul]
    rw [add_assoc, ← map_smul, ← map_add, hvt, map_sum]
    simp only [map_smul]
  have hz0 : (G v) 2 + t * (f u₀) 2 = 0 := by
    have := congrArg (fun x : ℝ³ => x 2) key
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    rw [this]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_zero fun w hw => by rw [hGz w hw, mul_zero]
  have ht : t = -((G v) 2 / (f u₀) 2) := by field_simp; linarith
  have hpt : G v - ((G v) 2 / (f u₀) 2) • f u₀ = ∑ w ∈ W, μ w • G w := by
    rw [← key, ht, neg_smul, sub_eq_add_neg]
  rw [hpt, show projXy (∑ w ∈ W, μ w • G w) = ∑ w ∈ W, μ w • (projXy ∘ G) w by
    rw [← projL_apply, map_sum]; simp [map_smul, projL_apply]]
  have := sum_smul_mem_interior_convexHull_image W (projXy ∘ G) μ hμ hμ1
    (by rwa [← Finset.image_image])
  rwa [← Finset.image_image] at this

/-- **Corollary 5.3 (pyramids).** If all points of `V` but one are coplanar
(and `conv V` is solid), `V` is Rupert. -/
theorem isRupert_of_pyramid (V : Finset ℝ³) (E : ℝ³)
    (hint : (interior (convexHull ℝ (V : Set ℝ³))).Nonempty)
    (hplane : Coplanar ℝ ((V.erase E : Finset ℝ³) : Set ℝ³)) :
    IsRupert V := by
  classical
  set W := V.erase E with hW
  have hVnc := not_coplanar_of_interior_nonempty hint
  have hE : E ∈ V := by
    by_contra hE; rw [hW, Finset.erase_eq_of_notMem hE] at hplane; exact hVnc hplane
  have hVW : (V : Set ℝ³) = insert E (W : Set ℝ³) := by
    rw [hW, Finset.coe_erase, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using hE)]
  obtain ⟨N, hN, c, hNc⟩ := exists_plane_of_coplanar hplane
  have hEc : ⟪N, E⟫ ≠ c := by
    intro h
    apply hVnc
    refine coplanar_of_plane hN (c := c) ?_
    rw [hVW]
    rintro x (rfl | hx)
    · exact h
    · exact hNc x hx
  have hWnc : ¬ Collinear ℝ (W : Set ℝ³) := fun hcol => hVnc (by
    rw [hVW]; exact hcol.coplanar_insert E)
  obtain ⟨a, ha, b, hb, d, hd, hind⟩ := exists_affineIndependent_triple hWnc
  have hWne : W.Nonempty := ⟨a, ha⟩
  have hcard : (0 : ℝ) < W.card := by exact_mod_cast hWne.card_pos
  set C := ∑ w ∈ W, (1 / (W.card : ℝ)) • w
  have hNC : ⟪N, C⟫ = c := by
    simp only [C, inner_sum, real_inner_smul_right]
    rw [Finset.sum_congr rfl fun w hw => by rw [hNc w hw], Finset.sum_const, nsmul_eq_mul]
    field_simp
  refine isRupert_of_crossing V W (Finset.erase_subset E V) N c hNc ha hb hd hind (C - E)
    (by rw [inner_sub_right, hNC]; exact sub_ne_zero.mpr (Ne.symm hEc)) ?_
  intro v hv hvW
  have hvE : v = E := by
    by_contra h; exact hvW (Finset.mem_erase.mpr ⟨h, hv⟩)
  refine ⟨1, fun _ => 1 / (W.card : ℝ), fun _ _ => by positivity, ?_, ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  · rw [hvE, one_smul, add_sub_cancel]

/-- The view `u = c - E` from the apex through a relative-interior point `c`
of the base is admissible. -/
theorem sub_mem_admissibleViews_of_pyramid (V : Finset ℝ³) (E : ℝ³)
    (hE : E ∉ affineSpan ℝ ((V.erase E : Finset ℝ³) : Set ℝ³)) (c : ℝ³)
    (hc : c ∈ intrinsicInterior ℝ (convexHull ℝ ((V.erase E : Finset ℝ³) : Set ℝ³))) :
    c - E ∈ admissibleViews V (V.erase E) := by
  have hcA : c ∈ affineSpan ℝ ((V.erase E : Finset ℝ³) : Set ℝ³) := by
    have := subset_affineSpan ℝ _ (intrinsicInterior_subset hc)
    rwa [affineSpan_convexHull] at this
  refine ⟨fun h => hE ?_, fun v hv hvW => ⟨1, ?_⟩⟩
  · have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.neg_mem _ h) hcA
    simpa [vadd_eq_add] using this
  · have hvE : v = E := by
      by_contra h; exact hvW (Finset.mem_erase.mpr ⟨h, hv⟩)
    rw [hvE, one_smul, add_sub_cancel]
    exact hc

/-- A point of the relative interior of a polytope is a combination of all its
points with positive weights. -/
theorem exists_pos_weights_of_mem_intrinsicInterior (W : Finset ℝ³) {x : ℝ³}
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))) :
    ∃ μ : ℝ³ → ℝ, (∀ w ∈ W, 0 < μ w) ∧ ∑ w ∈ W, μ w = 1 ∧ x = ∑ w ∈ W, μ w • w := by
  classical
  set s := convexHull ℝ (W : Set ℝ³)
  have hxs : x ∈ s := intrinsicInterior_subset hx
  have hWne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with h | h
    · rw [show s = ∅ by simp [s, h]] at hxs; exact absurd hxs (Set.notMem_empty x)
    · exact h
  have hn : (0 : ℝ) < W.card := by exact_mod_cast hWne.card_pos
  set c := ∑ w ∈ W, (1 / (W.card : ℝ)) • w with hc
  have hcs : c ∈ s := (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun w hw => subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
  have hcA : c ∈ affineSpan ℝ s := subset_affineSpan ℝ s hcs
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hx
  have hmemA : ∀ ε : ℝ, (y : ℝ³) + ε • ((y : ℝ³) - c) ∈ affineSpan ℝ s := fun ε => by
    have := AffineSubspace.vadd_mem_of_mem_direction
      (Submodule.smul_mem _ ε (AffineSubspace.vsub_mem_direction y.2 hcA)) y.2
    simpa [vadd_eq_add, vsub_eq_sub, add_comm] using this
  let γ : ℝ → affineSpan ℝ s := fun ε => ⟨(y : ℝ³) + ε • ((y : ℝ³) - c), hmemA ε⟩
  have hγc : Continuous γ := by
    apply Continuous.subtype_mk; fun_prop
  have hγ0 : γ 0 = y := by ext; simp [γ]
  have hev : ∀ᶠ ε in nhds (0 : ℝ), γ ε ∈ interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) :=
    hγc.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact isOpen_interior.mem_nhds hy)
  obtain ⟨ε, hε, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0))).exists
  have hys : (y : ℝ³) + ε • ((y : ℝ³) - c) ∈ s :=
    (interior_subset hε : γ ε ∈ ((↑) ⁻¹' s : Set (affineSpan ℝ s)))
  have hεp : 0 < ε := hεpos
  obtain ⟨ν, hν0, hν1, hνy⟩ := Finset.mem_convexHull.mp hys
  rw [Finset.centerMass_eq_of_sum_1 _ _ hν1] at hνy
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  refine ⟨fun w => ν w / (1 + ε) + ε / ((1 + ε) * W.card), fun w hw => ?_, ?_, ?_⟩
  · have := hν0 w hw
    positivity
  · rw [Finset.sum_add_distrib, ← Finset.sum_div, hν1, Finset.sum_const, nsmul_eq_mul]
    field_simp
  · simp only [add_smul, Finset.sum_add_distrib]
    have h1 : ∑ w ∈ W, (ν w / (1 + ε)) • w = (1 / (1 + ε)) • ((y : ℝ³) + ε • ((y : ℝ³) - c)) := by
      rw [← hνy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [id, smul_smul]; congr 1; field_simp
    have h2 : ∑ w ∈ W, (ε / ((1 + ε) * W.card)) • w = (ε / (1 + ε)) • c := by
      rw [hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [smul_smul]; congr 1; field_simp
    rw [h1, h2]
    have hsplit : (1 / (1 + ε)) • ((y : ℝ³) + ε • ((y : ℝ³) - c)) + (ε / (1 + ε)) • c =
        (1 / (1 + ε) + 1 / (1 + ε) * ε) • (y : ℝ³) + (ε / (1 + ε) - 1 / (1 + ε) * ε) • c := by
      module
    have e1 : 1 / (1 + ε) + 1 / (1 + ε) * ε = 1 := by field_simp
    have e2 : ε / (1 + ε) - 1 / (1 + ε) * ε = 0 := by ring
    rw [hsplit, e1, e2, one_smul, zero_smul, add_zero]

/-- **Theorem 5 (coplanar-silhouette theorem).**  If some subset `W ⊆ V`,
not collinear, has an admissible view (`U_Π ≠ ∅` for `Π = affineSpan W`),
then `V` is Rupert. -/
theorem isRupert_of_admissibleViews_nonempty (V W : Finset ℝ³) (hWV : W ⊆ V)
    (hW : ¬ Collinear ℝ (W : Set ℝ³)) (hU : (admissibleViews V W).Nonempty) :
    IsRupert V := by
  classical
  obtain ⟨u, hu, hcross⟩ := hU
  rw [direction_affineSpan] at hu
  -- `W` is planar, with normal `N`
  have hfin : finrank ℝ (vectorSpan ℝ (W : Set ℝ³)) ≤ 2 := by
    have := Submodule.finrank_lt (s := vectorSpan ℝ (W : Set ℝ³)) (fun h => hu (by simp [h]))
    rw [finrank_euclideanSpace, Fintype.card_fin] at this
    omega
  have hcop : Coplanar ℝ (W : Set ℝ³) := by
    unfold Coplanar; rw [← finrank_eq_rank]; exact_mod_cast hfin
  obtain ⟨N, hN, c, hNc⟩ := exists_plane_of_coplanar hcop
  have hle : vectorSpan ℝ (W : Set ℝ³) ≤ (ℝ ∙ N)ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    change ⟪N, x - y⟫ = 0
    rw [inner_sub_right, hNc x hx, hNc y hy, sub_self]
  have : Fact (finrank ℝ ℝ³ = 2 + 1) := ⟨by simp⟩
  have h2 : finrank ℝ (ℝ ∙ N)ᗮ = 2 := Submodule.finrank_orthogonal_span_singleton hN
  have hge : 2 ≤ finrank ℝ (vectorSpan ℝ (W : Set ℝ³)) := by
    by_contra hc; push Not at hc
    exact hW ((collinear_iff_finrank_le_one).mpr (by omega))
  have heq : vectorSpan ℝ (W : Set ℝ³) = (ℝ ∙ N)ᗮ :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have hNu : ⟪N, u⟫ ≠ 0 := by
    intro h0
    apply hu
    rw [heq, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact h0
  obtain ⟨a, ha, b, hb, d, hd, hind⟩ := exists_affineIndependent_triple hW
  refine isRupert_of_crossing V W hWV N c (fun w hw => hNc w hw) ha hb hd hind u hNu ?_
  intro v hv hvW
  obtain ⟨t, ht⟩ := hcross v hv hvW
  obtain ⟨μ, hμ, hμ1, hx⟩ := exists_pos_weights_of_mem_intrinsicInterior W ht
  exact ⟨t, μ, hμ, hμ1, hx⟩

/-- **Corollary 5.4 (bipyramid lemma), crossing form.** If every point of
`V \ W` is `D` or `E`, `D` is off the plane of `W`, and the segment `DE` meets
`relint (conv W)`, then `u = E - D` is admissible and `V` is Rupert. -/
theorem isRupert_of_segment_crossing (V W : Finset ℝ³) (D E : ℝ³) (hWV : W ⊆ V)
    (hVW : ∀ v ∈ V, v ∉ W → v = D ∨ v = E) (hW : ¬ Collinear ℝ (W : Set ℝ³))
    (hD : D ∉ affineSpan ℝ (W : Set ℝ³))
    (hX : (segment ℝ D E ∩ intrinsicInterior ℝ (convexHull ℝ (W : Set ℝ³))).Nonempty) :
    IsRupert V := by
  obtain ⟨X, hXs, hXi⟩ := hX
  rw [segment_eq_image'] at hXs
  obtain ⟨s, -, rfl⟩ := hXs
  have hXA : D + s • (E - D) ∈ affineSpan ℝ (W : Set ℝ³) := by
    have := subset_affineSpan ℝ _ (intrinsicInterior_subset hXi)
    rwa [affineSpan_convexHull] at this
  refine isRupert_of_admissibleViews_nonempty V W hWV hW ⟨E - D, fun h => hD ?_, fun v hv hvW => ?_⟩
  · have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ (-s) h) hXA
    convert this using 1
    rw [vadd_eq_add]; module
  · rcases hVW v hv hvW with rfl | rfl
    · exact ⟨s, hXi⟩
    · exact ⟨s - 1, by convert hXi using 1; module⟩



end Minimality

end RupertMinimality
