/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.AffineResponseCell
public import LeanPool.HighContrastHomogenization.Provider.Response.ResponseCongruence
public import LeanPool.HighContrastHomogenization.Provider.Response.AnnealedCutoffEnergy
public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormState
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Provider.Response.LocalizedOptimizerObservables
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.Dilation

/-!
# High-contrast homogenization: Provider.Response.AffineResponseCongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Stationary cancellation after affine normalization

At an aligned scale, multiplying the adapted grid by the corresponding triadic
factor gives an integer matrix.  Affine normalization by that matrix therefore
conjugates integer translations to integer translations and pushes a stationary
coefficient law to another stationary law.  The unconditional response
congruence on ordinary triadic cubes can then be applied before transporting
the response and cutoff averages back to the adapted affine family.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02 Book.Ch05.Section53.JUpperBoundWeakNorms
open scoped Pointwise

noncomputable section

variable {d : ℕ}

private theorem quasiMeasurePreserving_matVecMul_of_isUnitDet
    (L : Mat d) (hL : IsUnit L.det) :
    Measure.QuasiMeasurePreserving (matVecMul L) volume volume := by
  refine ⟨(continuous_matVecMul L).measurable, ?_⟩
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := L) hL.ne_zero
  change Measure.map (Matrix.toLin' L) volume ≪ volume
  rw [hmap]
  exact Measure.smul_absolutelyContinuous

private theorem aestronglyMeasurable_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (affineCoefficient L hL b) volume := by
  have hcomp : AEStronglyMeasurable (fun y : Vec d => b (matVecMul L y)) volume :=
    hb.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL)
  have hcont : Continuous fun A : Mat d => L⁻¹ * A * matTranspose L⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact hcont.comp_aestronglyMeasurable hcomp

private theorem isEllipticMatrix_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    {lam Lam : ℝ} {y : Vec d}
    (hb : IsEllipticMatrix lam Lam (b (matVecMul L y))) :
    IsEllipticMatrix
      (lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)))
      (max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam))
      (affineCoefficient L hL b y) := by
  let K := max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L))
  let lam' := lam / K
  let Lam' := max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKone : 1 ≤ K := le_max_left _ _
  have hlam' : 0 < lam' := div_pos hb.1 hK
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  rw [isEllipticMatrix_iff_isEllipticEntryLU]
  refine ⟨hlam', (div_le_self hb.1.le hKone).trans
    (hb.2.1.trans (le_max_left _ _)), ?_, ?_⟩
  · intro x
    let xi := matVecMul (matTranspose L)⁻¹ x
    have hx : matVecMul (matTranspose L) xi = x := by
      rw [show xi = matVecMul (matTranspose L)⁻¹ x from rfl,
        matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
      exact matVecMul_one x
    have hxnorm : vecNormSq x ≤ K * vecNormSq xi := by
      calc
        vecNormSq x = vecNormSq (matVecMul (matTranspose L) xi) := by rw [hx]
        _ ≤ Book.Ch02.matrixFrobeniusNormSq (matTranspose L) * vecNormSq xi :=
          Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq _ _
        _ ≤ K * vecNormSq xi := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (vecNormSq_nonneg xi)
    have hscaled : lam' * vecNormSq x ≤ lam * vecNormSq xi := by
      calc
        lam' * vecNormSq x ≤ lam' * (K * vecNormSq xi) :=
          mul_le_mul_of_nonneg_left hxnorm hlam'.le
        _ = lam * vecNormSq xi := by
          dsimp [lam', K]
          field_simp [hK.ne']
    calc
      lam' * vecNormSq x ≤ lam * vecNormSq xi := hscaled
      _ ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) := hb.2.2.1 xi
      _ = vecDot x (matVecMul (affineCoefficient L hL b y) x) := by
        rw [← affineCoefficient_energy hL b y xi, hx]
  · intro x
    let xi := matVecMul (matTranspose L)⁻¹ x
    have hx : matVecMul (matTranspose L) xi = x := by
      rw [show xi = matVecMul (matTranspose L)⁻¹ x from rfl,
        matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
      exact matVecMul_one x
    have himage :=
      ((isEllipticMatrix_iff_isEllipticEntryLU (b (matVecMul L y))).mp hb).2.2.2 xi
    have hnormInv : 0 ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ :=
      Book.Ch02.matrixFrobeniusNormSq_nonneg L⁻¹
    have henergy : 0 ≤ vecDot xi (matVecMul (b (matVecMul L y)) xi) :=
      (mul_nonneg hb.1.le (vecNormSq_nonneg xi)).trans (hb.2.2.1 xi)
    calc
      vecNormSq (matVecMul (affineCoefficient L hL b y) x) =
          vecNormSq (matVecMul L⁻¹ (matVecMul (b (matVecMul L y)) xi)) := by
        rw [← hx, affineCoefficient_flux hL]
      _ ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ *
          vecNormSq (matVecMul (b (matVecMul L y)) xi) :=
        Book.Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq _ _
      _ ≤ Book.Ch02.matrixFrobeniusNormSq L⁻¹ *
          (Lam * vecDot xi (matVecMul (b (matVecMul L y)) xi)) :=
        mul_le_mul_of_nonneg_left himage hnormInv
      _ = (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam) *
          vecDot xi (matVecMul (b (matVecMul L y)) xi) := by ring
      _ ≤ Lam' * vecDot xi (matVecMul (b (matVecMul L y)) xi) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) henergy
      _ = Lam' * vecDot x (matVecMul (affineCoefficient L hL b y) x) := by
        rw [← affineCoefficient_energy hL b y xi, hx]

private theorem isAELocallyUniformlyElliptic_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b) :
    IsAELocallyUniformlyElliptic (affineCoefficient L hL b) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
    hb.comp_matVecMul L (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL) R hR
  have hK : 0 < max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨lam / max 1 (Book.Ch02.matrixFrobeniusNormSq (matTranspose L)),
    max Lam (Book.Ch02.matrixFrobeniusNormSq L⁻¹ * Lam), div_pos hlam hK,
    (div_le_self hlam.le (le_max_left _ _)).trans (hle.trans (le_max_left _ _)),
    ?_⟩
  filter_upwards [hell] with y hy hyb
  exact isEllipticMatrix_affineCoefficient L hL (hy hyb)

theorem exists_affineCoeffSpace (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffSpace d) :
    ∃ b : CoeffSpace d,
      (⇑b.1 : CoeffField d) =ᵐ[volume] affineCoefficient L hL (⇑a.1) := by
  let f : CoeffField d := affineCoefficient L hL (⇑a.1)
  have hf : AEStronglyMeasurable f volume :=
    aestronglyMeasurable_affineCoefficient L hL a.1.aestronglyMeasurable
  exact ⟨⟨AEEqFun.mk f hf,
    (isAELocallyUniformlyElliptic_affineCoefficient L hL a.2).congr
      (AEEqFun.coeFn_mk f hf).symm⟩, AEEqFun.coeFn_mk f hf⟩

@[expose]
public noncomputable def affineCoeffSpace (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffSpace d) : CoeffSpace d :=
  (exists_affineCoeffSpace L hL a).choose

private theorem affineCoeffSpace_ae (L : Mat d) (hL : IsUnit L.det)
    (a : CoeffSpace d) :
    (⇑(affineCoeffSpace L hL a).1 : CoeffField d) =ᵐ[volume]
      affineCoefficient L hL (⇑a.1) :=
  (exists_affineCoeffSpace L hL a).choose_spec

private theorem affineCoefficient_pairing
    (L : Mat d) (hL : IsUnit L.det) (a : CoeffField d)
    (y e e' : Vec d) :
    vecDot e' (matVecMul (affineCoefficient L hL a y) e) =
      vecDot (matVecMul (matTranspose L)⁻¹ e')
        (matVecMul (a (matVecMul L y))
          (matVecMul (matTranspose L)⁻¹ e)) := by
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  let u := matVecMul (matTranspose L)⁻¹ e
  let u' := matVecMul (matTranspose L)⁻¹ e'
  have he : matVecMul (matTranspose L) u = e := by
    rw [show u = matVecMul (matTranspose L)⁻¹ e from rfl,
      matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
    exact matVecMul_one e
  have he' : matVecMul (matTranspose L) u' = e' := by
    rw [show u' = matVecMul (matTranspose L)⁻¹ e' from rfl,
      matVecMul_mul, Matrix.mul_nonsing_inv (matTranspose L) hLT]
    exact matVecMul_one e'
  calc
    vecDot e' (matVecMul (affineCoefficient L hL a y) e) =
        vecDot (matVecMul (matTranspose L) u')
          (matVecMul (affineCoefficient L hL a y)
            (matVecMul (matTranspose L) u)) := by rw [he, he']
    _ = vecDot (matVecMul (matTranspose L) u')
          (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) u)) := by
      rw [affineCoefficient_flux hL]
    _ = vecDot (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) u))
          (matVecMul (matTranspose L) u') := vecDot_comm _ _
    _ = vecDot
          (matVecMul L (matVecMul L⁻¹ (matVecMul (a (matVecMul L y)) u))) u' :=
      vecDot_matVecMul_transpose _ _ L
    _ = vecDot (matVecMul (a (matVecMul L y)) u) u' := by
      rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one]
    _ = vecDot u' (matVecMul (a (matVecMul L y)) u) := vecDot_comm _ _

private theorem affineCoeffSpace_pairing
    (L : Mat d) (hL : IsUnit L.det) (a : CoeffSpace d)
    (e e' : Vec d) (phi : Vec d → ℝ) :
    coeffPairing e e' phi (affineCoeffSpace L hL a) =
      coeffPairing (matVecMul (matTranspose L)⁻¹ e)
        (matVecMul (matTranspose L)⁻¹ e')
        (fun x ↦ |L.det|⁻¹ * phi (matVecMul L⁻¹ x)) a := by
  let u := matVecMul (matTranspose L)⁻¹ e
  let u' := matVecMul (matTranspose L)⁻¹ e'
  let psi : Vec d → ℝ := fun x ↦ |L.det|⁻¹ * phi (matVecMul L⁻¹ x)
  let chi : Vec d → ℝ := fun x ↦ phi (matVecMul L⁻¹ x)
  have hdet : |L.det| ≠ 0 := abs_ne_zero.mpr hL.ne_zero
  have huniv : matImage L (Set.univ : Set (Vec d)) = Set.univ := by
    rw [matImage_eq_preimage hL]
    simp
  have hchange := setIntegral_matImage hL MeasurableSet.univ
    (fun x : Vec d ↦ vecDot u' (matVecMul (a.1 x) u) * chi x)
  have hchange' :
      (∫ x, vecDot u' (matVecMul (a.1 x) u) * chi x ∂volume) =
        |L.det| * ∫ y, vecDot u' (matVecMul (a.1 (matVecMul L y)) u) *
          chi (matVecMul L y) ∂volume := by
    simpa [huniv] using hchange
  have hpoint : ∀ᵐ y ∂volume,
      vecDot e'
          (matVecMul ((affineCoeffSpace L hL a).1 y) e) * phi y =
        vecDot u' (matVecMul (a.1 (matVecMul L y)) u) *
          chi (matVecMul L y) := by
    filter_upwards [affineCoeffSpace_ae L hL a] with y hy
    rw [hy, affineCoefficient_pairing L hL]
    dsimp [u, u', chi]
    have hinv : matVecMul L⁻¹ (matVecMul L y) = y := by
      rw [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
    rw [hinv]
  rw [coeffPairing, coeffPairing]
  calc
    ∫ y, vecDot e' (matVecMul ((affineCoeffSpace L hL a).1 y) e) * phi y
        ∂volume =
        ∫ y, vecDot u' (matVecMul (a.1 (matVecMul L y)) u) *
          chi (matVecMul L y) ∂volume := integral_congr_ae hpoint
    _ = |L.det|⁻¹ * ∫ x, vecDot u' (matVecMul (a.1 x) u) * chi x ∂volume := by
      calc
        (∫ y, vecDot u' (matVecMul (a.1 (matVecMul L y)) u) *
            chi (matVecMul L y) ∂volume) =
            |L.det|⁻¹ * (|L.det| *
              ∫ y, vecDot u' (matVecMul (a.1 (matVecMul L y)) u) *
                chi (matVecMul L y) ∂volume) := by field_simp [hdet]
        _ = |L.det|⁻¹ *
            ∫ x, vecDot u' (matVecMul (a.1 x) u) * chi x ∂volume := by
          rw [hchange']
    _ = ∫ x, vecDot u' (matVecMul (a.1 x) u) *
          (|L.det|⁻¹ * phi (matVecMul L⁻¹ x)) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [chi]
      ring

private theorem isLocalTest_affinePullback
    (L : Mat d) (hL : IsUnit L.det) {phi : Vec d → ℝ}
    (hphi : IsLocalTest Set.univ phi) :
    IsLocalTest Set.univ
      (fun x ↦ |L.det|⁻¹ * phi (matVecMul L⁻¹ x)) := by
  have hcomp : IsLocalTest Set.univ (fun x ↦ phi (matVecMul L⁻¹ x)) := by
    apply isLocalTest_comp_matVecMul_inv hL
    have hU : matImage L⁻¹ (Set.univ : Set (Vec d)) = Set.univ := by
      rw [matImage_inv_eq_preimage hL]
      simp
    rw [hU]
    exact hphi
  refine ⟨contDiff_const.mul hcomp.contDiff, ?_, Set.subset_univ _⟩
  simpa [Pi.smul_apply, smul_eq_mul] using!
    hcomp.hasCompactSupport.smul_left (f := fun _ : Vec d ↦ |L.det|⁻¹)

theorem measurable_affineCoeffSpace (L : Mat d) (hL : IsUnit L.det) :
    Measurable (affineCoeffSpace L hL : CoeffSpace d → CoeffSpace d) := by
  change @Measurable (CoeffSpace d) (CoeffSpace d) (coeffSigma d Set.univ)
    (MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (phi : Vec d → ℝ), IsLocalTest Set.univ phi ∧
        ∃ u : Set ℝ, MeasurableSet u ∧ s = coeffPairing e e' phi ⁻¹' u})
    (affineCoeffSpace L hL)
  apply measurable_generateFrom
  rintro s ⟨e, e', phi, hphi, u, hu, rfl⟩
  let eL := matVecMul (matTranspose L)⁻¹ e
  let eL' := matVecMul (matTranspose L)⁻¹ e'
  let psi : Vec d → ℝ := fun x ↦ |L.det|⁻¹ * phi (matVecMul L⁻¹ x)
  have hpsi : IsLocalTest Set.univ psi := isLocalTest_affinePullback L hL hphi
  have hset : affineCoeffSpace L hL ⁻¹' (coeffPairing e e' phi ⁻¹' u) =
      coeffPairing eL eL' psi ⁻¹' u := by
    ext a
    change coeffPairing e e' phi (affineCoeffSpace L hL a) ∈ u ↔ _
    rw [affineCoeffSpace_pairing]
    rfl
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom ⟨eL, eL', psi, hpsi, u, hu, rfl⟩

private theorem matVecMul_intTranslation_eq
    (L : Mat d) (n : Fin d → Fin d → ℤ)
    (hL : ∀ i k, L i k = (n i k : ℝ)) (z : Fin d → ℤ) :
    matVecMul L (Source.AKL.intTranslation z) =
      Source.AKL.intTranslation (fun i ↦ ∑ k, n i k * z k) := by
  funext i
  simp only [matVecMul, Source.AKL.intTranslation]
  push_cast
  apply Finset.sum_congr rfl
  intro k _hk
  rw [hL]

private theorem translateCoeff_affineCoeffSpace
    (L : Mat d) (hL : IsUnit L.det) {z v : Fin d → ℤ}
    (hLv : matVecMul L (Source.AKL.intTranslation z) =
      Source.AKL.intTranslation v) (a : CoeffSpace d) :
    translateCoeff z (affineCoeffSpace L hL a) =
      affineCoeffSpace L hL (translateCoeff v a) := by
  have hshift :=
    (measurePreserving_add_right (volume : Measure (Vec d))
      (Source.AKL.intTranslation z)).quasiMeasurePreserving.tendsto_ae
        (affineCoeffSpace_ae L hL a)
  have hlinear :=
    (quasiMeasurePreserving_matVecMul_of_isUnitDet L hL).tendsto_ae
      (Source.AKL.translateField_ae v a.1)
  apply Subtype.ext
  apply AEEqFun.ext
  filter_upwards [Source.AKL.translateField_ae z (affineCoeffSpace L hL a).1,
    hshift, affineCoeffSpace_ae L hL (translateCoeff v a), hlinear]
      with y hleft hsource hright htranslated
  change (affineCoeffSpace L hL a).1
      (y + Source.AKL.intTranslation z) =
    affineCoefficient L hL (⇑a.1) (y + Source.AKL.intTranslation z) at hsource
  change (translateCoeff v a).1 (matVecMul L y) =
    a.1 (matVecMul L y + Source.AKL.intTranslation v) at htranslated
  change (Source.AKL.translateField z (affineCoeffSpace L hL a).1) y =
    (affineCoeffSpace L hL (translateCoeff v a)).1 y
  rw [hleft, hsource, hright]
  unfold affineCoefficient
  rw [htranslated, matVecMul_add, hLv]

private theorem stationaryLaw_map_affineCoeffSpace
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (L : Mat d) (hL : IsUnit L.det) (n : Fin d → Fin d → ℤ)
    (hLint : ∀ i k, L i k = (n i k : ℝ)) :
    HCPoly.Frozen.IsStationaryLaw
      (Measure.map (affineCoeffSpace L hL) P) := by
  intro z
  let v : Fin d → ℤ := fun i ↦ ∑ k, n i k * z k
  have hLv : matVecMul L (Source.AKL.intTranslation z) =
      Source.AKL.intTranslation v := matVecMul_intTranslation_eq L n hLint z
  have hcomm : translateCoeff z ∘ affineCoeffSpace L hL =
      affineCoeffSpace L hL ∘ translateCoeff v := by
    funext a
    exact translateCoeff_affineCoeffSpace L hL hLv a
  calc
    Measure.map (translateCoeff z) (Measure.map (affineCoeffSpace L hL) P) =
        Measure.map (translateCoeff z ∘ affineCoeffSpace L hL) P := by
      rw [Measure.map_map (measurable_translateCoeff z)
        (measurable_affineCoeffSpace L hL)]
    _ = Measure.map (affineCoeffSpace L hL ∘ translateCoeff v) P := by rw [hcomm]
    _ = Measure.map (affineCoeffSpace L hL) (Measure.map (translateCoeff v) P) := by
      rw [Measure.map_map (measurable_affineCoeffSpace L hL)
        (measurable_translateCoeff v)]
    _ = Measure.map (affineCoeffSpace L hL) P := by rw [hP v]

private theorem stationaryLaw_map_of_commutes
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    (S : CoeffSpace d → CoeffSpace d) (hSmeas : Measurable S)
    (hS : ∀ z a, translateCoeff z (S a) = S (translateCoeff z a)) :
    HCPoly.Frozen.IsStationaryLaw (Measure.map S P) := by
  intro z
  have hcomm : translateCoeff z ∘ S = S ∘ translateCoeff z := by
    funext a
    exact hS z a
  calc
    Measure.map (translateCoeff z) (Measure.map S P) =
        Measure.map (translateCoeff z ∘ S) P := by
      rw [Measure.map_map (measurable_translateCoeff z) hSmeas]
    _ = Measure.map (S ∘ translateCoeff z) P := by rw [hcomm]
    _ = Measure.map S (Measure.map (translateCoeff z) P) := by
      rw [Measure.map_map hSmeas (measurable_translateCoeff z)]
    _ = Measure.map S P := by rw [hP z]

private theorem zpow_smul_posDef (q : Mat d) (hq : q.PosDef) (l : ℤ) :
    (((3 : ℝ) ^ l) • q).PosDef :=
  hq.smul (by positivity)

private theorem dilateCube_translate_origin_sub
    (l k : ℤ) (w : Fin d → ℤ) :
    dilateCube l (translateCube w (originCube d (k - l))) =
      translateCube w (originCube d k) := by
  apply congrArg₂ TriadicCube.mk
  · simp [translateCube, originCube]
  · funext i
    simp [translateCube, originCube]

private theorem standardCell_dilate
    (l k : ℤ) (w : Fin d → ℤ) :
    Book.Ch02.dilateVec l '' standardCell d (k - l) w =
      standardCell d k w := by
  rw [standardCell, standardCell, ← dilateCube_translate_origin_sub l k w,
    Book.Ch02.openCubeSet_dilateCube]
  rfl

private theorem adaptedCellAt_zpow_smul_sub
    (q : Mat d) (l k : ℤ) (w : Fin d → ℤ) :
    adaptedCellAt (((3 : ℝ) ^ l) • q) (k - l) w =
      adaptedCellAt q k w := by
  rw [Recurrence.adaptedCellAt_eq_image, Recurrence.adaptedCellAt_eq_image,
    ← standardCell_dilate l k w, Set.image_image]
  apply Set.image_congr'
  intro y
  funext i
  simp only [matVecMul, Pi.smul_apply, Matrix.smul_apply,
    Book.Ch02.dilateVec, Book.Ch02.triadicDilationFactor,
    smul_eq_mul]
  ring_nf

private theorem adaptedDomainAt_zpow_smul_sub
    (q : Mat d) (hq : q.PosDef) (l k : ℤ) (w : Fin d → ℤ) :
    adaptedDomainAt (zpow_smul_posDef q hq l) (k - l) w =
      adaptedDomainAt hq k w := by
  have hcarrier :
      (adaptedDomainAt (zpow_smul_posDef q hq l) (k - l) w).carrier =
        (adaptedDomainAt hq k w).carrier := by
    simpa only [adaptedDomainAt_carrier] using
      adaptedCellAt_zpow_smul_sub q l k w
  cases hleft : adaptedDomainAt (zpow_smul_posDef q hq l) (k - l) w with
  | mk U hU hUne =>
    cases hright : adaptedDomainAt hq k w with
    | mk V hV hVne =>
      have hUV : U = V := by simpa [hleft, hright] using hcarrier
      subst V
      rfl

private theorem responseJ_affineCoeffSpace_eq_adapted
    (L : Mat d) (hL : L.PosDef) (T k : ℤ) (w : Fin d → ℤ)
    (a : CoeffSpace d) (p r : Vec d) :
    ResponseJ
        (openCubeSet (translateCube w (originCube d k)))
        (matVecMul (matTranspose L) p) (matVecMul L⁻¹ r)
        (⇑(affineCoeffSpace L
          ((Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit) a).1 : CoeffField d) =
      Book.Ch02.responseJ (adaptedDomainAt hL k w)
        (a.coeffOn (adaptedDomainAt hL k w)) p r := by
  let hLdet : IsUnit L.det :=
    (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
  obtain ⟨aRef, haRef⟩ := exists_adaptedReferenceCoeffFamily hL T a
  let R := translateCube w (originCube d k)
  have hcoeff :
      (⇑(affineCoeffSpace L hLdet a).1 : CoeffField d) =ᵐ[volume]
        (aRef.coeffOn R).toCoeffField := by
    have href := haRef R
    simp only [CoeffSpace.coeffOn_toCoeffField] at href
    filter_upwards [affineCoeffSpace_ae L hLdet a] with y hy
    rw [hy, href]
  calc
    ResponseJ (openCubeSet R)
        (matVecMul (matTranspose L) p) (matVecMul L⁻¹ r)
        (⇑(affineCoeffSpace L hLdet a).1 : CoeffField d) =
      ResponseJ (openCubeSet R)
        (matVecMul (matTranspose L) p) (matVecMul L⁻¹ r)
        (aRef.coeffOn R).toCoeffField :=
          ResponseJ_congr_of_ae_eq _ _ _ hcoeff
    _ = Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (aRef.coeffOn R)
        (matVecMul (matTranspose L) p) (matVecMul L⁻¹ r) := by
      simpa only [Book.Ch02.cubeDomain_coe] using
        (Internal.Ch02.book_responseJ_eq_ResponseJ
          (Book.Ch02.cubeDomain R) (aRef.coeffOn R)
          (matVecMul (matTranspose L) p) (matVecMul L⁻¹ r)).symm
    _ = Book.Ch02.responseJ (adaptedDomainAt hL k w)
        (a.coeffOn (adaptedDomainAt hL k w)) p r :=
      responseJ_affineResponseCell hL T k w a aRef haRef p r

private theorem normalizedResponseJ_eq_affineFamilyResponseJ
    {q : Mat d} (hq : q.PosDef) (s t k : ℤ) (w : Fin d → ℤ)
    (S : CoeffSpace d → CoeffSpace d)
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((S a).coeffOn (adaptedDomain hq t)).toCoeffField)
    (a : CoeffSpace d) (p r : Vec d) :
    let L := ((3 : ℝ) ^ s) • q
    let hL := zpow_smul_posDef q hq s
    ResponseJ
        (openCubeSet (translateCube w (originCube d (k - s))))
        (matVecMul (matTranspose L) p) (matVecMul L⁻¹ r)
        (⇑(affineCoeffSpace L
          ((Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit) (S a)).1 :
            CoeffField d) =
      Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) := by
  dsimp only
  calc
    ResponseJ
        (openCubeSet (translateCube w (originCube d (k - s))))
        (matVecMul (matTranspose (((3 : ℝ) ^ s) • q)) p)
        (matVecMul (((3 : ℝ) ^ s) • q)⁻¹ r)
        (⇑(affineCoeffSpace (((3 : ℝ) ^ s) • q)
          ((Matrix.isUnit_iff_isUnit_det (((3 : ℝ) ^ s) • q)).mp
            (zpow_smul_posDef q hq s).isUnit) (S a)).1 : CoeffField d) =
      Book.Ch02.responseJ
        (adaptedDomainAt (zpow_smul_posDef q hq s) (k - s) w)
        ((S a).coeffOn
          (adaptedDomainAt (zpow_smul_posDef q hq s) (k - s) w)) p r :=
      responseJ_affineCoeffSpace_eq_adapted
        (((3 : ℝ) ^ s) • q) (zpow_smul_posDef q hq s) (t - s) (k - s)
          w (S a) p r
    _ = Book.Ch02.responseJ (adaptedDomainAt hq k w)
        ((S a).coeffOn (adaptedDomainAt hq k w)) p r := by
      rw [adaptedDomainAt_zpow_smul_sub q hq s k w]
    _ = Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (translateCube w (originCube d k)))
        ((A a).coeffOn (translateCube w (originCube d k)))
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) :=
      (responseJ_affineResponseCell hq t k w (S a) (A a) (hA a) p r).symm

private theorem matImage_smul_one_eq_smul_set
    (c : ℝ) (U : Set (Vec d)) :
    matImage (c • (1 : Mat d)) U = c • U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    exact (Internal.Ch02.BookCh02.matVecMul_smul_one c y).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    exact Internal.Ch02.BookCh02.matVecMul_smul_one c y

private theorem integrableOn_dilatePullback
    (s : ℤ) (Q : TriadicCube d) {phi : Vec d → ℝ}
    (hphi : IntegrableOn phi (cubeSet (dilateCube s Q)) volume) :
    IntegrableOn (fun y ↦ phi (Book.Ch02.dilateVec s y)) (cubeSet Q) volume := by
  let c : ℝ := Book.Ch02.triadicDilationFactor s
  let M : Mat d := c • (1 : Mat d)
  have hc : 0 < c := Book.Ch02.triadicDilationFactor_pos s
  have hMpd : M.PosDef := Matrix.PosDef.one.smul hc
  have hMdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).mp hMpd.isUnit
  have himage : matImage M (openCubeSet Q) =
      openCubeSet (dilateCube s Q) := by
    rw [Book.Ch02.openCubeSet_dilateCube]
    exact matImage_smul_one_eq_smul_set c (openCubeSet Q)
  have hopen : IntegrableOn phi (openCubeSet (dilateCube s Q)) volume :=
    hphi.congr_set_ae (cubeSet_ae_eq_openCubeSet (dilateCube s Q)).symm
  have hpull : IntegrableOn (fun y ↦ phi (matVecMul M y))
      (openCubeSet Q) volume := by
    apply (integrableOn_matImage_iff hMdet
      (measurableSet_openCubeSet Q) phi).mp
    rwa [himage]
  have hpull' : IntegrableOn (fun y ↦ phi (Book.Ch02.dilateVec s y))
      (openCubeSet Q) volume := by
    convert hpull using 1
    funext y
    exact congrArg phi (Internal.Ch02.BookCh02.matVecMul_smul_one c y).symm
  exact hpull'.congr_set_ae (cubeSet_ae_eq_openCubeSet Q)

private theorem cubeAverage_dilatePullback
    (s : ℤ) (Q : TriadicCube d) (phi : Vec d → ℝ) :
    cubeAverage Q (fun y ↦ phi (Book.Ch02.dilateVec s y)) =
      cubeAverage (dilateCube s Q) phi := by
  have h := Book.Ch02.average_dilate_comp_undilate s Q
    (fun y ↦ phi (Book.Ch02.dilateVec s y))
  rw [Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage,
    Book.Ch05.Section53.JUpperBoundWeakNorms.ch02_average_cubeDomain_eq_cubeAverage]
      at h
  simpa [Book.Ch02.dilateVec, Book.Ch02.undilateVec,
    Book.Ch02.triadicDilationFactor_ne_zero s] using h.symm

private theorem affineCoefficient_inv_affineCoefficient
    (L : Mat d) (hL : IsUnit L.det) (b : CoeffField d) (x : Vec d) :
    affineCoefficient L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL)
        (affineCoefficient L hL b) x = b x := by
  rw [affineCoefficient_apply, affineCoefficient_apply,
    Matrix.nonsing_inv_nonsing_inv L hL]
  have hLT : IsUnit (matTranspose L).det := by
    simpa [matTranspose] using Matrix.isUnit_det_transpose L hL
  have hinvT : matTranspose L⁻¹ = (matTranspose L)⁻¹ := by
    simpa [matTranspose] using Matrix.transpose_nonsing_inv (A := L)
  rw [matVecMul_mul, Matrix.mul_nonsing_inv L hL, matVecMul_one, hinvT,
    ← Matrix.mul_assoc L (L⁻¹ * b x) (matTranspose L)⁻¹,
    ← Matrix.mul_assoc L L⁻¹ (b x),
    Matrix.mul_assoc ((L * L⁻¹) * b x) (matTranspose L)⁻¹ (matTranspose L),
    Matrix.nonsing_inv_mul _ hLT, Matrix.mul_one, Matrix.mul_nonsing_inv L hL,
    Matrix.one_mul]

theorem affineCoeffSpace_inv_affineCoeffSpace
    (L : Mat d) (hL : IsUnit L.det) (a : CoeffSpace d) :
    affineCoeffSpace L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL)
        (affineCoeffSpace L hL a) = a := by
  apply Subtype.ext
  apply AEEqFun.ext
  have hinner :=
    (quasiMeasurePreserving_matVecMul_of_isUnitDet L⁻¹
      (Matrix.isUnit_nonsing_inv_det L hL)).tendsto_ae
        (affineCoeffSpace_ae L hL a)
  filter_upwards [affineCoeffSpace_ae L⁻¹
      (Matrix.isUnit_nonsing_inv_det L hL) (affineCoeffSpace L hL a),
    hinner] with x houter hinnerx
  rw [houter, affineCoefficient_apply, hinnerx]
  exact affineCoefficient_inv_affineCoefficient L hL (⇑a.1) x

@[expose]
public noncomputable def affineCoeffSpaceEquiv
    (L : Mat d) (hL : IsUnit L.det) : CoeffSpace d ≃ᵐ CoeffSpace d where
  toFun := affineCoeffSpace L hL
  invFun := affineCoeffSpace L⁻¹ (Matrix.isUnit_nonsing_inv_det L hL)
  left_inv := affineCoeffSpace_inv_affineCoeffSpace L hL
  right_inv := by
    intro a
    simpa only [Matrix.nonsing_inv_nonsing_inv L hL] using
      affineCoeffSpace_inv_affineCoeffSpace L⁻¹
        (Matrix.isUnit_nonsing_inv_det L hL) a
  measurable_toFun := measurable_affineCoeffSpace L hL
  measurable_invFun := measurable_affineCoeffSpace L⁻¹
    (Matrix.isUnit_nonsing_inv_det L hL)

private theorem descendantsAverage_dilateCube
    (s : ℤ) (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage (dilateCube s Q) j F =
      descendantsAverage Q j (fun R ↦ F (dilateCube s R)) := by
  classical
  change
    ((descendantsAtDepth (dilateCube s Q) j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (dilateCube s Q) j, F R =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, F (dilateCube s R)
  rw [Book.Ch02.descendantsAtDepth_dilateCube,
    Finset.card_image_of_injective _ (Book.Ch02.dilateCube_injective s),
    Finset.sum_image]
  exact fun _ _ _ _ h ↦ Book.Ch02.dilateCube_injective s h

/-- A stationary affine family inherits the exact cutoff-weighted response
cancellation from the unconditional triadic response congruence. -/
theorem integral_cutoffWeighted_affineResponseJ_eq_zero_of_stationarity
    {P : Measure (CoeffSpace d)} (hP : HCPoly.Frozen.IsStationaryLaw P)
    {q : Mat d} (hq : q.PosDef) {l s t : ℤ} (hqGrid : IsRoundedGrid l q)
    (j : ℕ) (hscale : t - (j : ℤ) = s) (hls : l ≤ s)
    (E : CoeffSpace d ≃ᵐ CoeffSpace d)
    (hE : ∀ z a, translateCoeff z (E a) = E (translateCoeff z a))
    (A : CoeffSpace d → Book.Ch02.TriadicCoeffFamily d)
    (hA : ∀ a Q, ((A a).coeffOn Q).toCoeffField = affineCoefficient q
      ((Matrix.isUnit_iff_isUnit_det q).mp hq.isUnit)
      ((E a).coeffOn (adaptedDomain hq t)).toCoeffField)
    (p r : Vec d) {phi : Vec d → ℝ}
    (hint : ∀ R ∈ descendantsAtDepth (originCube d t) j,
      Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
        (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
        (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hbase : Integrable (fun a : CoeffSpace d ↦ Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d s))
      ((A a).coeffOn (originCube d s))
      (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) P)
    (hphi : IntegrableOn phi (cubeSet (originCube d t)) volume)
    (hmean : cubeAverage (originCube d t) phi = 1) :
    ∫ a, descendantsAverage (originCube d t) j (fun R ↦
        (1 - cubeAverage R phi) * Book.Ch02.responseJ
          (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) ∂P = 0 := by
  let L : Mat d := ((3 : ℝ) ^ s) • q
  let hL : L.PosDef := zpow_smul_posDef q hq s
  let hLdet : IsUnit L.det :=
    (Matrix.isUnit_iff_isUnit_det L).mp hL.isUnit
  let eL : CoeffSpace d ≃ᵐ CoeffSpace d := affineCoeffSpaceEquiv L hLdet
  let P1 : Measure (CoeffSpace d) := Measure.map E P
  let P0 : Measure (CoeffSpace d) := Measure.map eL P1
  let Q0 : TriadicCube d := originCube d (t - s)
  let phi0 : Vec d → ℝ := fun y ↦ phi (Book.Ch02.dilateVec s y)
  let p0 : Vec d := matVecMul (matTranspose L) p
  let r0 : Vec d := matVecMul L⁻¹ r
  let rawJ : TriadicCube d → CoeffSpace d → ℝ :=
    fun R b ↦ ResponseJ (openCubeSet R) p0 r0 (⇑b.1 : CoeffField d)
  have hQ : dilateCube s Q0 = originCube d t := by
    dsimp only [Q0]
    exact dilateCube_translate_origin_sub s t (0 : Fin d → ℤ)
  have hP1 : HCPoly.Frozen.IsStationaryLaw P1 :=
    stationaryLaw_map_of_commutes hP E E.measurable hE
  obtain ⟨n, hn⟩ := Recurrence.exists_int_zpow_smul_of_isRoundedGrid hqGrid hls
  have hLint : ∀ i k, L i k = (n i k : ℝ) := by
    intro i k
    exact hn i k
  have hP0 : HCPoly.Frozen.IsStationaryLaw P0 :=
    stationaryLaw_map_affineCoeffSpace hP1 L hLdet n hLint
  have hchildScale : 0 ≤ Q0.scale - (j : ℤ) := by
    dsimp only [Q0, originCube]
    omega
  have hmember (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q0 j) :
      dilateCube s R ∈ descendantsAtDepth (originCube d t) j := by
    rw [← hQ, Book.Ch02.descendantsAtDepth_dilateCube]
    exact Finset.mem_image.mpr ⟨R, hR, rfl⟩
  have hRscale (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q0 j) :
      R.scale = 0 := by
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
    dsimp only [Q0, originCube]
    omega
  have hresponse (R : TriadicCube d)
      (hR : R ∈ descendantsAtDepth Q0 j) (a : CoeffSpace d) :
      rawJ R (eL (E a)) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (dilateCube s R))
          ((A a).coeffOn (dilateCube s R))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) := by
    have hcanon : translateCube R.index (originCube d 0) = R := by
      rw [← hRscale R hR]
      cases R
      simp only [translateCube, originCube, Pi.zero_apply, zero_add]
    have hdilate : translateCube R.index (originCube d s) = dilateCube s R := by
      calc
        translateCube R.index (originCube d s) =
            dilateCube s (translateCube R.index (originCube d (s - s))) :=
          (dilateCube_translate_origin_sub s s R.index).symm
        _ = dilateCube s (translateCube R.index (originCube d 0)) := by
          rw [sub_self]
        _ = dilateCube s R := congrArg (dilateCube s) hcanon
    have hnorm := normalizedResponseJ_eq_affineFamilyResponseJ
      hq s t s R.index E A hA a p r
    rw [sub_self, hcanon, hdilate] at hnorm
    dsimp only [rawJ, p0, r0, L]
    simpa [eL, hLdet, affineCoeffSpaceEquiv] using hnorm
  have hint0 : ∀ R ∈ descendantsAtDepth Q0 j,
      Integrable (rawJ R) P0 := by
    intro R hR
    dsimp only [P0, P1]
    refine (integrable_map_equiv eL (rawJ R)).mpr ?_
    refine (integrable_map_equiv E (rawJ R ∘ eL)).mpr ?_
    have ht := hint (dilateCube s R) (hmember R hR)
    simpa only [Function.comp_apply] using!
      ht.congr (Filter.Eventually.of_forall fun a ↦ (hresponse R hR a).symm)
  have hbaseResponse (a : CoeffSpace d) :
      rawJ (originCube d 0) (eL (E a)) =
        Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d s))
          ((A a).coeffOn (originCube d s))
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r) := by
    dsimp only [rawJ, p0, r0, eL, L, hLdet]
    simpa only [sub_self, translateCube, originCube, Pi.zero_apply, zero_add] using!
      normalizedResponseJ_eq_affineFamilyResponseJ
        hq s t s (0 : Fin d → ℤ) E A hA a p r
  have hbase0 : Integrable (rawJ (originCube d 0)) P0 := by
    dsimp only [P0, P1]
    refine (integrable_map_equiv eL (rawJ (originCube d 0))).mpr ?_
    refine (integrable_map_equiv E (rawJ (originCube d 0) ∘ eL)).mpr ?_
    simpa only [Function.comp_apply] using! hbase.congr
      (Filter.Eventually.of_forall fun a ↦ (hbaseResponse a).symm)
  have hphi0 : IntegrableOn phi0 (cubeSet Q0) volume := by
    dsimp only [phi0]
    apply integrableOn_dilatePullback s Q0
    rwa [hQ]
  have hmean0 : cubeAverage Q0 phi0 = 1 := by
    dsimp only [phi0]
    rw [cubeAverage_dilatePullback, hQ, hmean]
  have hvanish :
      ∫ b, descendantsAverage Q0 j (fun R ↦
        (1 - cubeAverage R phi0) * rawJ R b) ∂P0 = 0 := by
    have hzero : Q0.scale - (j : ℤ) = 0 := by
      dsimp only [Q0, originCube]
      omega
    have hbase0' : Integrable (fun a : CoeffSpace d ↦
        ResponseJ (openCubeSet (originCube d (Q0.scale - (j : ℤ))))
          p0 r0 (⇑a.1 : CoeffField d)) P0 := by
      simpa only [hzero, rawJ] using hbase0
    simpa only [rawJ] using
      integral_descendantsAverage_cutoffWeighted_ResponseJ_eq_zero
        hP0 Q0 j hchildScale p0 r0 hint0 hbase0' hphi0 hmean0
  have hintegrand (a : CoeffSpace d) :
      descendantsAverage Q0 j (fun R ↦
          (1 - cubeAverage R phi0) * rawJ R (eL (E a))) =
        descendantsAverage (originCube d t) j (fun R ↦
          (1 - cubeAverage R phi) * Book.Ch02.responseJ
            (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
            (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) := by
    rw [← hQ, descendantsAverage_dilateCube]
    apply descendantsAverage_congr_of_eq_on_descendants
    intro R hR
    rw [cubeAverage_dilatePullback]
    exact congrArg ((1 - cubeAverage (dilateCube s R) phi) * ·)
      (hresponse R hR a)
  calc
    ∫ a, descendantsAverage (originCube d t) j (fun R ↦
        (1 - cubeAverage R phi) * Book.Ch02.responseJ
          (Book.Ch02.cubeDomain R) ((A a).coeffOn R)
          (matVecMul (matTranspose q) p) (matVecMul q⁻¹ r)) ∂P =
      ∫ a, descendantsAverage Q0 j (fun R ↦
        (1 - cubeAverage R phi0) * rawJ R (eL (E a))) ∂P := by
          exact integral_congr_ae
            (Filter.Eventually.of_forall fun a ↦ (hintegrand a).symm)
    _ = ∫ b, descendantsAverage Q0 j (fun R ↦
        (1 - cubeAverage R phi0) * rawJ R b) ∂P0 := by
      dsimp only [P0, P1]
      rw [integral_map_equiv, integral_map_equiv]
    _ = 0 := hvanish

end

end HCPolySupport.HighContrast.Response
