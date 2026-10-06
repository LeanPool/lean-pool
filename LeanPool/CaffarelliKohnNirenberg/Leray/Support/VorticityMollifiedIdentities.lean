/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityWeakLimit

/-!
# Pointwise identities for backward mollifications

Constant-coefficient weak identities on an open set hold pointwise for the backward
mollifications at every point whose kernel support lies inside the set. These are the smooth
forms of the weak vorticity equation, of weak derivatives, and of the divergence and curl
constraints used in the bootstrap of `thm:vorticity-regularity` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A second coordinate derivative of a smooth space-time function is an iterated directional
derivative. -/
theorem vorticity_spatialSecondPartial_eq_fderiv {F : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (j k : Fin 3) (z : Vec3 × ℝ) :
    spatialSecondPartial F j k z =
      (fderiv ℝ (fun y => (fderiv ℝ F y) (basisVec j, 0)) z) (basisVec k, 0) := by
  have hfirst : (fun y : ParabolicPoint => spatialPartial F j y) =
      fun y : Vec3 × ℝ => (fderiv ℝ F y) (basisVec j, 0) := by
    funext y
    exact spatialPartial_eq_product_fderiv (hF.differentiable (by simp) y) j
  unfold spatialSecondPartial
  rw [hfirst]
  apply spatialPartial_eq_product_fderiv
  exact ((vorticityKernelDeriv_contDiff hF (basisVec j, 0)).differentiable (by simp)) z

/-- The backward test is admissible on an open set containing the closed kernel ball. -/
theorem vorticityBackTest_admissible {W : Set (Vec3 × ℝ)} {ε : ℝ} (hε : 0 < ε)
    {z : Vec3 × ℝ} (hz : Metric.closedBall (z - vorticityBackShift ε) ε ⊆ W) :
    ContDiff ℝ (⊤ : ℕ∞) (vorticityBackTest ε hε z) ∧
      HasCompactSupport (vorticityBackTest ε hε z) ∧
      tsupport (vorticityBackTest ε hε z) ⊆ W :=
  ⟨vorticityBackTest_contDiff hε z, vorticityBackTest_hasCompactSupport hε z,
    (vorticityBackTest_tsupport_subset hε z).trans hz⟩

private theorem vorticity_integrableOn_mul_of_continuous_compact
    {W : Set (Vec3 × ℝ)} {f d : Vec3 × ℝ → ℝ} (hf : IntegrableOn f W)
    (hd : Continuous d) (hdc : HasCompactSupport d) :
    IntegrableOn (fun y => f y * d y) W := by
  obtain ⟨C, hC⟩ := hd.bounded_above_of_compact_support hdc
  exact Integrable.mul_bdd hf hd.aestronglyMeasurable.restrict
    (Eventually.of_forall fun y => hC y)

/-- Pairing with a spatial derivative of the backward test. -/
theorem vorticityBackTest_pairing_spatialPartial {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {f : Vec3 × ℝ → ℝ} (hf : IntegrableOn f W) {ε : ℝ} (hε : 0 < ε) (z : Vec3 × ℝ)
    (j : Fin 3) :
    ∫ y in W, f y * spatialPartial (vorticityBackTest ε hε z) j y =
      -spatialPartial (vorticityBackMollify W f ε hε) j z := by
  have hloc : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) :=
    ((integrable_indicator_iff hW).2 hf).locallyIntegrable
  have htest : ∀ y, spatialPartial (vorticityBackTest ε hε z) j y =
      (fderiv ℝ (vorticityBackTest ε hε z) y) (basisVec j, 0) := fun y =>
    spatialPartial_eq_product_fderiv
      ((vorticityBackTest_contDiff hε z).differentiable (by simp) y) j
  have hfun : (fun y => f y * spatialPartial (vorticityBackTest ε hε z) j y) =
      fun y => f y * (fderiv ℝ (vorticityBackTest ε hε z) y) (basisVec j, 0) := by
    funext y
    rw [htest y]
  rw [hfun, vorticityBackTest_pairing_fderiv hW hε hloc z (basisVec j, 0),
    spatialPartial_eq_product_fderiv
      ((vorticityBackMollify_contDiff hε hloc).differentiable (by simp) z) j]

/-- Pairing with the time derivative of the backward test. -/
theorem vorticityBackTest_pairing_timePartial {W : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    {f : Vec3 × ℝ → ℝ} (hf : IntegrableOn f W) {ε : ℝ} (hε : 0 < ε) (z : Vec3 × ℝ) :
    ∫ y in W, f y * timePartial (vorticityBackTest ε hε z) y =
      -timePartial (vorticityBackMollify W f ε hε) z := by
  have hloc : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) :=
    ((integrable_indicator_iff hW).2 hf).locallyIntegrable
  have htest : ∀ y, timePartial (vorticityBackTest ε hε z) y =
      (fderiv ℝ (vorticityBackTest ε hε z) y) (0, 1) := fun y =>
    timePartial_eq_product_fderiv
      ((vorticityBackTest_contDiff hε z).differentiable (by simp) y)
  have hfun : (fun y => f y * timePartial (vorticityBackTest ε hε z) y) =
      fun y => f y * (fderiv ℝ (vorticityBackTest ε hε z) y) (0, 1) := by
    funext y
    rw [htest y]
  rw [hfun, vorticityBackTest_pairing_fderiv hW hε hloc z (0, 1),
    timePartial_eq_product_fderiv
      ((vorticityBackMollify_contDiff hε hloc).differentiable (by simp) z)]

/-- Pairing with a second spatial derivative of the backward test. -/
theorem vorticityBackTest_pairing_spatialSecondPartial {W : Set (Vec3 × ℝ)}
    (hW : MeasurableSet W) {f : Vec3 × ℝ → ℝ} (hf : IntegrableOn f W) {ε : ℝ} (hε : 0 < ε)
    (z : Vec3 × ℝ) (j k : Fin 3) :
    ∫ y in W, f y * spatialSecondPartial (vorticityBackTest ε hε z) j k y =
      spatialSecondPartial (vorticityBackMollify W f ε hε) j k z := by
  have hloc : LocallyIntegrable (W.indicator f) (volume : Measure (Vec3 × ℝ)) :=
    ((integrable_indicator_iff hW).2 hf).locallyIntegrable
  have htest : ∀ y, spatialSecondPartial (vorticityBackTest ε hε z) j k y =
      (fderiv ℝ (fun q => (fderiv ℝ (vorticityBackTest ε hε z) q) (basisVec j, 0)) y)
        (basisVec k, 0) := fun y =>
    vorticity_spatialSecondPartial_eq_fderiv (vorticityBackTest_contDiff hε z) j k y
  have hfun : (fun y => f y * spatialSecondPartial (vorticityBackTest ε hε z) j k y) =
      fun y => f y * (fderiv ℝ (fun q => (fderiv ℝ (vorticityBackTest ε hε z) q)
        (basisVec j, 0)) y) (basisVec k, 0) := by
    funext y
    rw [htest y]
  rw [hfun, vorticityBackTest_pairing_fderiv_fderiv hW hε hloc z (basisVec j, 0) (basisVec k, 0),
    vorticity_spatialSecondPartial_eq_fderiv (vorticityBackMollify_contDiff hε hloc) j k z]

/-- A weak spatial derivative on an open set commutes with backward mollification at points whose
kernel support lies inside the set. -/
theorem vorticityBackMollify_spatialPartial_of_weak {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {f g : Vec3 × ℝ → ℝ} (hf : IntegrableOn f W) {j : Fin 3}
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, f y * spatialPartial ψ j y = -∫ y in W, g y * ψ y)
    {ε : ℝ} (hε : 0 < ε) {z : Vec3 × ℝ}
    (hz : Metric.closedBall (z - vorticityBackShift ε) ε ⊆ W) :
    spatialPartial (vorticityBackMollify W f ε hε) j z = vorticityBackMollify W g ε hε z := by
  obtain ⟨h1, h2, h3⟩ := vorticityBackTest_admissible hε hz
  have h := hweak _ h1 h2 h3
  rw [vorticityBackTest_pairing_spatialPartial hW.measurableSet hf hε z j,
    vorticityBackTest_pairing hW.measurableSet hε z] at h
  linarith only [h]

/-- The weak heat equation with a divergence-form source holds pointwise for backward
mollifications at points whose kernel support lies inside the domain. -/
theorem vorticityBackMollify_heat_of_weak {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {w : Vec3 × ℝ → ℝ} {F : Fin 3 → Vec3 × ℝ → ℝ} (hw : IntegrableOn w W)
    (hF : ∀ j, IntegrableOn (F j) W)
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
        -∫ y in W, ∑ j : Fin 3, F j y * spatialPartial ψ j y)
    {ε : ℝ} (hε : 0 < ε) {z : Vec3 × ℝ}
    (hz : Metric.closedBall (z - vorticityBackShift ε) ε ⊆ W) :
    timePartial (vorticityBackMollify W w ε hε) z -
        ∑ j : Fin 3, spatialSecondPartial (vorticityBackMollify W w ε hε) j j z =
      ∑ j : Fin 3, spatialPartial (vorticityBackMollify W (F j) ε hε) j z := by
  obtain ⟨h1, h2, h3⟩ := vorticityBackTest_admissible hε hz
  set ψ := vorticityBackTest ε hε z with hψdef
  have h := hweak ψ h1 h2 h3
  have hint_t : IntegrableOn (fun y => w y * timePartial ψ y) W :=
    vorticity_integrableOn_mul_of_continuous_compact hw (CKN.contDiff_timePartial h1).continuous
      (CKN.hasCompactSupport_timePartial h2)
  have hint_s : ∀ j : Fin 3, IntegrableOn (fun y => w y * spatialSecondPartial ψ j j y) W := by
    intro j
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 × ℝ => spatialSecondPartial ψ j j y) :=
      CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff h1 j) j
    have hcs : HasCompactSupport (fun y : Vec3 × ℝ => spatialSecondPartial ψ j j y) :=
      CKN.hasCompactSupport_spatialPartial (CKN.hasCompactSupport_spatialPartial h2 j) j
    exact vorticity_integrableOn_mul_of_continuous_compact hw hc.continuous hcs
  have hint_F : ∀ j : Fin 3, IntegrableOn (fun y => F j y * spatialPartial ψ j y) W := by
    intro j
    exact vorticity_integrableOn_mul_of_continuous_compact (hF j)
      (CKN.spatialPartial_contDiff h1 j).continuous (CKN.hasCompactSupport_spatialPartial h2 j)
  have hlhs : ∫ y in W, w y * (-timePartial ψ y - ∑ j : Fin 3, spatialSecondPartial ψ j j y) =
      -(∫ y in W, w y * timePartial ψ y) -
        ∑ j : Fin 3, ∫ y in W, w y * spatialSecondPartial ψ j j y := by
    have hsplit : (fun y => w y * (-timePartial ψ y - ∑ j : Fin 3,
        spatialSecondPartial ψ j j y)) = fun y => -(w y * timePartial ψ y) -
          ∑ j : Fin 3, w y * spatialSecondPartial ψ j j y := by
      funext y
      simp only [mul_sub, mul_neg, Finset.mul_sum]
    rw [hsplit]
    calc
      _ = (∫ y in W, -(w y * timePartial ψ y)) -
          ∫ y in W, ∑ j : Fin 3, w y * spatialSecondPartial ψ j j y :=
        integral_sub (show IntegrableOn (fun y => -(w y * timePartial ψ y)) W volume from
          hint_t.neg)
          (integrable_finsetSum (μ := volume.restrict W) _ fun j _ => hint_s j)
      _ = _ := by
        congr 1
        · exact integral_neg _
        · exact integral_finsetSum _ fun j _ => hint_s j
  have hrhs : ∫ y in W, ∑ j : Fin 3, F j y * spatialPartial ψ j y =
      ∑ j : Fin 3, ∫ y in W, F j y * spatialPartial ψ j y :=
    integral_finsetSum _ fun j _ => hint_F j
  have hS : ∑ j : Fin 3, ∫ y in W, w y * spatialSecondPartial ψ j j y =
      ∑ j : Fin 3, spatialSecondPartial (vorticityBackMollify W w ε hε) j j z :=
    Finset.sum_congr rfl fun j _ =>
      vorticityBackTest_pairing_spatialSecondPartial hW.measurableSet hw hε z j j
  have hFs : ∑ j : Fin 3, ∫ y in W, F j y * spatialPartial ψ j y =
      ∑ j : Fin 3, -spatialPartial (vorticityBackMollify W (F j) ε hε) j z :=
    Finset.sum_congr rfl fun j _ =>
      vorticityBackTest_pairing_spatialPartial hW.measurableSet (hF j) hε z j
  rw [hlhs, hrhs, vorticityBackTest_pairing_timePartial hW.measurableSet hw hε z, hS, hFs,
    Finset.sum_neg_distrib] at h
  linarith only [h]

/-- A weak divergence constraint holds pointwise for backward mollifications. -/
theorem vorticityBackMollify_div_of_weak {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {Y : Fin 3 → Vec3 × ℝ → ℝ} (hY : ∀ i, IntegrableOn (Y i) W)
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∫ y in W, ∑ i : Fin 3, Y i y * spatialPartial ψ i y = 0)
    {ε : ℝ} (hε : 0 < ε) {z : Vec3 × ℝ}
    (hz : Metric.closedBall (z - vorticityBackShift ε) ε ⊆ W) :
    ∑ i : Fin 3, spatialPartial (vorticityBackMollify W (Y i) ε hε) i z = 0 := by
  obtain ⟨h1, h2, h3⟩ := vorticityBackTest_admissible hε hz
  have h := hweak _ h1 h2 h3
  rw [integral_finsetSum _ fun i _ => vorticity_integrableOn_mul_of_continuous_compact (hY i)
    (CKN.spatialPartial_contDiff h1 i).continuous (CKN.hasCompactSupport_spatialPartial h2 i)] at h
  have hS : ∑ i : Fin 3, ∫ y in W, Y i y * spatialPartial (vorticityBackTest ε hε z) i y =
      ∑ i : Fin 3, -spatialPartial (vorticityBackMollify W (Y i) ε hε) i z :=
    Finset.sum_congr rfl fun i _ =>
      vorticityBackTest_pairing_spatialPartial hW.measurableSet (hY i) hε z i
  rw [hS, Finset.sum_neg_distrib] at h
  linarith only [h]

/-- A weak antisymmetric derivative identity holds pointwise for backward mollifications. -/
theorem vorticityBackMollify_curl_of_weak {W : Set (Vec3 × ℝ)} (hW : IsOpen W)
    {Ya Yb Ω : Vec3 × ℝ → ℝ} (hYa : IntegrableOn Ya W) (hYb : IntegrableOn Yb W)
    {a b : Fin 3}
    (hweak : ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W →
      ∫ y in W, (Yb y * spatialPartial ψ a y - Ya y * spatialPartial ψ b y) =
        -∫ y in W, Ω y * ψ y)
    {ε : ℝ} (hε : 0 < ε) {z : Vec3 × ℝ}
    (hz : Metric.closedBall (z - vorticityBackShift ε) ε ⊆ W) :
    spatialPartial (vorticityBackMollify W Yb ε hε) a z -
        spatialPartial (vorticityBackMollify W Ya ε hε) b z =
      vorticityBackMollify W Ω ε hε z := by
  obtain ⟨h1, h2, h3⟩ := vorticityBackTest_admissible hε hz
  have h := hweak _ h1 h2 h3
  rw [integral_sub
    (vorticity_integrableOn_mul_of_continuous_compact hYb
      (CKN.spatialPartial_contDiff h1 a).continuous (CKN.hasCompactSupport_spatialPartial h2 a))
    (vorticity_integrableOn_mul_of_continuous_compact hYa
      (CKN.spatialPartial_contDiff h1 b).continuous (CKN.hasCompactSupport_spatialPartial h2 b)),
    vorticityBackTest_pairing_spatialPartial hW.measurableSet hYb hε z,
    vorticityBackTest_pairing_spatialPartial hW.measurableSet hYa hε z,
    vorticityBackTest_pairing hW.measurableSet hε z] at h
  linarith only [h]

end CKN
