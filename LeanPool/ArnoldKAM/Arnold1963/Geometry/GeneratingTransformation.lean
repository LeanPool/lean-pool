/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingEquivariance

/-!
Analytic canonical transformations on shrunken domains and analytic Hamiltonian pullbacks.
-/

@[expose] public section
noncomputable section
open Set
open scoped NNReal Topology
namespace KamProject.Arnold1963

theorem phaseDomain_subset_generatingTarget {n : ℕ} (G : Set (ComplexSpace n))
    {ρ r : ℝ≥0} (hρ : r + r + r ≤ ρ) :
    phaseDomain (erosion G (r + r)) (ρ - (r + r + r)) ⊆
      generatingTarget G (angleStrip n ρ) r := by
  intro y hy
  exact ⟨hy.1, fun _ hz => mem_angleStrip_of_dist_le hρ hy.2 hz⟩

/-- An analytic canonical transformation with analytic inverse and displacement control. -/
structure AnalyticCanonicalTransformation {n : ℕ}
    (D V : Set (ComplexPhaseSpace n)) (ε : ℝ) where
  /-- The forward complex phase transformation. -/
  toFun : ComplexPhaseSpace n → ComplexPhaseSpace n
  /-- The inverse function on the forward transformation's image. -/
  invFun : ComplexPhaseSpace n → ComplexPhaseSpace n
  analytic : AnalyticOnNhd ℂ toFun D
  inverse_analytic : AnalyticOnNhd ℂ invFun (toFun '' D)
  mapsTo : MapsTo toFun D V
  left_inv : LeftInvOn invFun toFun D
  right_inv : RightInvOn invFun toFun (toFun '' D)
  inverse_mapsTo : MapsTo invFun (toFun '' D) D
  canonical : CanonicalOn toFun D
  inverse_canonical : CanonicalOn invFun (toFun '' D)
  displacement : NormBoundOn (fun x => toFun x - x) D ε
  derivative_bound : ∀ x ∈ D, ‖fderiv ℂ toFun x‖ < 2

namespace AnalyticCanonicalTransformation
variable {n : ℕ} {D V : Set (ComplexPhaseSpace n)} {ε : ℝ}

theorem injOn (B : AnalyticCanonicalTransformation D V ε) : InjOn B.toFun D :=
  B.left_inv.injOn

theorem bijOn_image (B : AnalyticCanonicalTransformation D V ε) :
    BijOn B.toFun D (B.toFun '' D) :=
  ⟨mapsTo_image _ _, B.injOn, surjOn_image _ _⟩

/-- The transformation as a homeomorphism between its source and its actual image. -/
def homeomorph (B : AnalyticCanonicalTransformation D V ε) : D ≃ₜ (B.toFun '' D) where
  toFun x := ⟨B.toFun x, mem_image_of_mem _ x.property⟩
  invFun z := ⟨B.invFun z, B.inverse_mapsTo z.property⟩
  left_inv x := Subtype.ext (B.left_inv x.property)
  right_inv z := Subtype.ext (B.right_inv z.property)
  continuous_toFun := (B.analytic.continuousOn.domRestrict).subtype_mk _
  continuous_invFun := (B.inverse_analytic.continuousOn.domRestrict).subtype_mk _

/-- Restriction of the canonical transformation to a smaller source domain. -/
def restrict (B : AnalyticCanonicalTransformation D V ε)
    {D' : Set (ComplexPhaseSpace n)} (hD : D' ⊆ D) : AnalyticCanonicalTransformation D' V ε where
  toFun := B.toFun
  invFun := B.invFun
  analytic := B.analytic.mono hD
  inverse_analytic := B.inverse_analytic.mono (image_mono hD)
  mapsTo := fun _ hx => B.mapsTo (hD hx)
  left_inv := fun _ hx => B.left_inv (hD hx)
  right_inv := fun _ hx => B.right_inv (image_mono hD hx)
  inverse_mapsTo := by
    rintro z ⟨x, hx, rfl⟩
    rw [B.left_inv (hD hx)]
    exact hx
  canonical := fun _ hx => B.canonical _ (hD hx)
  inverse_canonical := fun _ hx => B.inverse_canonical _ (image_mono hD hx)
  displacement := ⟨B.displacement.nonneg, fun _ hx => B.displacement.norm_le (hD hx)⟩
  derivative_bound := fun _ hx => B.derivative_bound _ (hD hx)

end AnalyticCanonicalTransformation

namespace GeneratingData
variable {n : ℕ} {S : ComplexPhaseSpace n → ℂ} {G U : Set (ComplexSpace n)}
  {r : ℝ≥0} {M : ℝ} (d : GeneratingData S G U r M)

theorem of_arnold (hn : 0 < n) (hr : 0 < r) (hS : AnalyticOnNhd ℂ S (G ×ˢ U))
    (hb : NormBoundOn S (G ×ˢ U) M) (hM : M < (r : ℝ) ^ 2 / (16 * n)) :
    GeneratingData S G U r M :=
  ⟨hr, hS, hb, generating_small_sixteenth hn hr hM⟩

include d

/-- The canonical transformation constructed from analytic generating data. -/
def transformation : AnalyticCanonicalTransformation (generatingTarget G U r) (G ×ˢ U) (M / r) where
  toFun := generatingTransform S G U r
  invFun := generatingTransformInv S G U r
  analytic := d.transform_analytic
  inverse_analytic := d.transformInv_analytic
  mapsTo := d.transform_mapsTo
  left_inv := fun _ hy => d.transform_left_inv hy
  right_inv := fun _ hz => d.transform_right_inv hz
  inverse_mapsTo := by
    rintro z ⟨y, hy, rfl⟩
    simpa only [d.transform_left_inv hy] using hy
  canonical := d.transform_canonical
  inverse_canonical := d.transformInv_canonical
  displacement := d.displacement_bound
  derivative_bound := fun _ hy => (d.derivative_bound hy).trans_lt (by norm_num)

theorem action_displacement {δ : ℝ≥0} (hδ : 0 < δ) {y : ComplexPhaseSpace n}
    (hP : y.1 ∈ erosion G (r + r)) (hQ : y.2 ∈ erosion U ((r + r + r) + δ)) :
    ‖(generatingTransform S G U r y).1 - y.1‖ ≤ M / δ := by
  have hy : y ∈ generatingTarget G U r :=
    ⟨hP, erosion_antitone_radius U (show r + r + r ≤ (r + r + r) + δ from le_self_add) hQ⟩
  have hp := (d.inverse_spec hy).2.2.1
  have hpair : generatingInverse S G U r y = (y.1, (generatingInverse S G U r y).2) :=
    Prod.ext hp rfl
  change ‖(generatingOutput S (generatingInverse S G U r y)).1 - y.1‖ ≤ _
  rw [hpair]
  exact generating_action_displacement_le hδ d.analytic d.bounded
    (erosion_subset _ _ hP) hQ (d.inverse_spec hy).2.2.2

end GeneratingData

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0} {M : ℝ}

theorem generatingData (S : AnalyticPhaseFunction n G ρ) (hn : 0 < n) (hr : 0 < r)
    (hM : S.uniformNorm < (r : ℝ) ^ 2 / (16 * n)) :
    GeneratingData S.toFun G (angleStrip n ρ) r S.uniformNorm :=
  ⟨hr, S.analytic, S.norm_le_iff.mp le_rfl, generating_small_sixteenth hn hr hM⟩

/-- Pullback of an analytic Hamiltonian through a generating transformation on a smaller domain. -/
def pullbackGenerating (H S : AnalyticPhaseFunction n G ρ)
    (d : GeneratingData S.toFun G (angleStrip n ρ) r M)
    (hρ : r + r + r ≤ ρ) :
    AnalyticPhaseFunction n (erosion G (r + r)) (ρ - (r + r + r)) where
  toFun z := H.toFun (generatingTransform S.toFun G (angleStrip n ρ) r z)
  domain_conj := fun _ hp => star_mem_erosion S.domain_conj hp
  analytic := fun z hz => (H.analytic _ (d.transform_mapsTo
    (phaseDomain_subset_generatingTarget G hρ hz))).comp
      (d.transform_analytic z (phaseDomain_subset_generatingTarget G hρ hz))
  periodic := by
    intro p hp q hq k
    have hz := phaseDomain_subset_generatingTarget G hρ (show (p, q) ∈
      phaseDomain (erosion G (r + r)) (ρ - (r + r + r)) from ⟨hp, hq⟩)
    change H.toFun (generatingTransform S.toFun G (angleStrip n ρ) r (phaseShift k (p, q))) = _
    rw [S.generatingTransform_shift d hz k]
    exact H.periodic _ (d.transform_mapsTo hz).1 _ (d.transform_mapsTo hz).2 k
  conj_compatible := by
    intro z hz
    have hy := phaseDomain_subset_generatingTarget G hρ hz
    change H.toFun (generatingTransform S.toFun G (angleStrip n ρ) r (conjPhase z)) = _
    rw [S.generatingTransform_conj d hy]
    exact H.conj_compatible _ (d.transform_mapsTo hy)
  bounded := ⟨H.uniformNorm, (H.norm_le_iff.mp le_rfl).nonneg,
    fun z hz => (H.norm_le_iff.mp le_rfl).norm_le
      (d.transform_mapsTo (phaseDomain_subset_generatingTarget G hρ hz))⟩

theorem uniformNorm_pullbackGenerating_le (H S : AnalyticPhaseFunction n G ρ)
    (d : GeneratingData S.toFun G (angleStrip n ρ) r M)
    (hρ : r + r + r ≤ ρ) :
    (H.pullbackGenerating S d hρ).uniformNorm ≤ H.uniformNorm :=
  ((H.pullbackGenerating S d hρ).norm_le_iff).2
    ⟨(H.norm_le_iff.mp le_rfl).nonneg, fun _ hz => (H.norm_le_iff.mp le_rfl).norm_le
      (d.transform_mapsTo (phaseDomain_subset_generatingTarget G hρ hz))⟩

end AnalyticPhaseFunction
end KamProject.Arnold1963
