/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Setup.Moments
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.DilationLaw

/-!
# High-contrast homogenization: Provider.Quenched.PhysicalScaleTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Physical-scale coefficient transport

Triadic restoration acts on the a.e.-quotient coefficient space by the
pullback `a ↦ (x ↦ a(3^N x))`.  It is measurable for the coefficient-space
sigma-field, and a coarse block on a restored cell is exactly the original
coarse block at the generation shifted by `N`.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory Book.Ch02

noncomputable section

variable {d : ℕ}

private theorem quasiMeasurePreserving_triadicDilateVec (N : ℕ) :
    Measure.QuasiMeasurePreserving (triadicDilateVec (d := d) N) volume volume := by
  simpa [triadicDilateVec, Pi.smul_apply, smul_eq_mul] using!
    (Measure.quasiMeasurePreserving_smul (μ := volume)
      (pow_ne_zero N (by norm_num : (3 : ℝ) ≠ 0)))

private theorem norm_triadicDilateVec_le (N : ℕ) (x : Vec d) :
    ‖triadicDilateVec (d := d) N x‖ ≤ (3 : ℝ) ^ N * ‖x‖ := by
  have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ N := by positivity
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg h3 (norm_nonneg x))).2 fun i => ?_
  have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  calc ‖triadicDilateVec (d := d) N x i‖ = (3 : ℝ) ^ N * ‖x i‖ := by
        rw [show triadicDilateVec (d := d) N x i = (3 : ℝ) ^ N * x i from rfl,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg h3, Real.norm_eq_abs]
    _ ≤ (3 : ℝ) ^ N * ‖x‖ := mul_le_mul_of_nonneg_left hxi h3

/-- The triadic dilation carries the ball of radius `R` into the ball of radius
`3^N R`, so a locally uniformly elliptic field stays one under rescaling. -/
private theorem isAELocallyUniformlyElliptic_rescaleCoeffField (N : ℕ)
    (a : CoeffSpace d) :
    IsAELocallyUniformlyElliptic (rescaleCoeffField N (⇑a.1)) := by
  intro R hR
  obtain ⟨lam, Lam, hlam, hle, hell⟩ := a.2 (((3 : ℝ) ^ N) * R) (by positivity)
  refine ⟨lam, Lam, hlam, hle, ?_⟩
  filter_upwards [(quasiMeasurePreserving_triadicDilateVec (d := d) N).tendsto_ae
    hell] with x hx hxb
  refine hx (mem_ball_zero_iff.2 ?_)
  have hxn : ‖x‖ < R := mem_ball_zero_iff.1 hxb
  have h3 : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  exact lt_of_le_of_lt (norm_triadicDilateVec_le N x)
    (mul_lt_mul_of_pos_left hxn h3)

/-- The triadic dilation carries the open cube shrunk by `N` generations into
the open cube. -/
private theorem triadicDilateVec_mem_openCubeSet (N : ℕ) (Q : TriadicCube d)
    {x : Vec d} (hx : x ∈ openCubeSet (dilateCube (-(N : ℤ)) Q)) :
    triadicDilateVec N x ∈ openCubeSet Q := by
  intro i
  have h3 : (0 : ℝ) < (3 : ℝ) ^ N := by positivity
  have hscale : cubeScaleFactor (dilateCube (-(N : ℤ)) Q) * (3 : ℝ) ^ N =
      cubeScaleFactor Q := by
    simp only [cubeScaleFactor, dilateCube]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, zpow_natCast]
    field_simp
  have hi := hx i
  have hlow := (mul_lt_mul_of_pos_right hi.1 h3)
  have hhigh := (mul_lt_mul_of_pos_right hi.2 h3)
  rw [mul_assoc, hscale] at hlow hhigh
  refine ⟨?_, ?_⟩
  · have hval : triadicDilateVec (d := d) N x i = x i * (3 : ℝ) ^ N := by
      rw [show triadicDilateVec (d := d) N x i = (3 : ℝ) ^ N * x i from rfl]
      ring
    rw [hval, show ((Q.index i : ℝ) - 1 / 2) * cubeScaleFactor Q =
      ((dilateCube (-(N : ℤ)) Q).index i - 1 / 2) * cubeScaleFactor Q from rfl]
    exact hlow
  · have hval : triadicDilateVec (d := d) N x i = x i * (3 : ℝ) ^ N := by
      rw [show triadicDilateVec (d := d) N x i = (3 : ℝ) ^ N * x i from rfl]
      ring
    rw [hval, show ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q =
      ((dilateCube (-(N : ℤ)) Q).index i + 1 / 2) * cubeScaleFactor Q from rfl]
    exact hhigh

/-- The coefficient restored at generation `N`, represented by
`x ↦ a(3^N x)` on the a.e.-quotient coefficient space. -/
@[expose]
def physical_scale_coeff (N : ℕ) (a : CoeffSpace d) : CoeffSpace d := by
  let f : CoeffField d := rescaleCoeffField N (⇑a.1)
  have hf : AEStronglyMeasurable f volume :=
    a.1.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_triadicDilateVec N)
  exact ⟨AEEqFun.mk f hf,
    (isAELocallyUniformlyElliptic_rescaleCoeffField N a).congr
      (AEEqFun.coeFn_mk f hf).symm⟩

/-- The quotient representative of the restored coefficient is the literal
triadic rescaling of the original representative almost everywhere. -/
theorem physical_scale_coeff_ae (N : ℕ) (a : CoeffSpace d) :
    (⇑(physical_scale_coeff N a).1 : CoeffField d) =ᵐ[volume]
      rescaleCoeffField N (⇑a.1) := by
  dsimp [physical_scale_coeff]
  exact AEEqFun.coeFn_mk _ _

private theorem coeffPairing_physical_scale_coeff (N : ℕ)
    (e e' : Vec d) (phi : Vec d → ℝ) (a : CoeffSpace d) :
    coeffPairing e e' phi (physical_scale_coeff N a) =
      (((3 : ℝ) ^ N) ^ d)⁻¹ *
        coeffPairing e e' (fun y => phi (((3 : ℝ) ^ N)⁻¹ • y)) a := by
  rw [coeffPairing]
  calc
    (∫ x, vecDot e' (matVecMul ((physical_scale_coeff N a).1 x) e) * phi x
        ∂volume) =
        localTestObservable e e' phi (rescaleCoeffField N (⇑a.1)) := by
      unfold localTestObservable
      apply integral_congr_ae
      filter_upwards [physical_scale_coeff_ae N a] with x hx
      rw [hx]
    _ = (((3 : ℝ) ^ N) ^ d)⁻¹ *
        localTestObservable e e'
          (fun y => phi (((3 : ℝ) ^ N)⁻¹ • y)) (⇑a.1) :=
      localTestObservable_rescaleCoeffField_eq_const_mul N e e' phi (⇑a.1)
    _ = (((3 : ℝ) ^ N) ^ d)⁻¹ *
        coeffPairing e e' (fun y => phi (((3 : ℝ) ^ N)⁻¹ • y)) a := by
      rfl

private theorem isLocalTest_triadic_inv_smul (N : ℕ) {phi : Vec d → ℝ}
    (hphi : IsLocalTest Set.univ phi) :
    IsLocalTest Set.univ (fun y => phi (((3 : ℝ) ^ N)⁻¹ • y)) := by
  have hscale : ((3 : ℝ) ^ N)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  refine ⟨by
      simpa [Function.comp_def] using
        hphi.contDiff.comp (contDiff_const_smul (((3 : ℝ) ^ N)⁻¹)), ?_,
    Set.subset_univ _⟩
  show HasCompactSupport
    (phi ∘ Homeomorph.smulOfNeZero (((3 : ℝ) ^ N)⁻¹) hscale)
  simpa [Function.comp_def] using
    hphi.hasCompactSupport.comp_homeomorph
      (Homeomorph.smulOfNeZero (((3 : ℝ) ^ N)⁻¹) hscale)

/-- Triadic restoration is measurable on the a.e.-quotient coefficient
space, so its pushforward law is well-defined. -/
theorem measurable_physical_scale_coeff (N : ℕ) :
    Measurable (physical_scale_coeff (d := d) N) := by
  change @Measurable (CoeffSpace d) (CoeffSpace d) (coeffSigma d Set.univ)
    (MeasurableSpace.generateFrom
      {s | ∃ (e e' : Vec d) (phi : Vec d → ℝ), IsLocalTest Set.univ phi ∧
        ∃ u : Set ℝ, MeasurableSet u ∧ s = coeffPairing e e' phi ⁻¹' u})
    (physical_scale_coeff N)
  apply measurable_generateFrom
  rintro s ⟨e, e', phi, hphi, u, hu, rfl⟩
  let psi : Vec d → ℝ := fun y => phi (((3 : ℝ) ^ N)⁻¹ • y)
  let c : ℝ := (((3 : ℝ) ^ N) ^ d)⁻¹
  let u' : Set ℝ := (fun z : ℝ => c * z) ⁻¹' u
  have hpsi : IsLocalTest Set.univ psi := isLocalTest_triadic_inv_smul N hphi
  have hu' : MeasurableSet u' :=
    hu.preimage ((continuous_const.mul continuous_id).measurable)
  have hset : physical_scale_coeff (d := d) N ⁻¹'
      (coeffPairing e e' phi ⁻¹' u) = coeffPairing e e' psi ⁻¹' u' := by
    ext a
    change coeffPairing e e' phi (physical_scale_coeff N a) ∈ u ↔ _
    rw [coeffPairing_physical_scale_coeff]
    rfl
  rw [hset]
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨e, e', psi, hpsi, u', hu', rfl⟩

/-- The rescaled coefficient, read on the cube shrunk by `N` generations, with
the ellipticity constants the sample carries on the original cube. -/
@[expose]
public def physical_scale_coeffOn (N : ℕ) (a : CoeffSpace d)
    (Q : TriadicCube d) : CoeffOn (cubeDomain (dilateCube (-(N : ℤ)) Q)) where
  toCoeffField := rescaleCoeffField N (⇑a.1)
  lam := (a.coeffOn (cubeDomain Q)).lam
  Lam := (a.coeffOn (cubeDomain Q)).Lam
  lam_pos := (a.coeffOn (cubeDomain Q)).lam_pos
  lam_le_Lam := (a.coeffOn (cubeDomain Q)).lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hbase : AEStronglyMeasurable
        (fun x : Vec d => rescaleCoeffField N (⇑a.1) x i j) volume :=
      (continuous_id.matrix_elem i j).comp_aestronglyMeasurable
        (a.1.aestronglyMeasurable.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_triadicDilateVec N))
    refine hbase.restrict.congr ?_
    filter_upwards [ae_restrict_mem
      (cubeDomain (dilateCube (-(N : ℤ)) Q)).measurableSet] with x hx
    change x ∈ openCubeSet (dilateCube (-(N : ℤ)) Q) at hx
    simp [restrictCoeffField, hx]
  aeElliptic := by
    have hsrc : ∀ᵐ y ∂volume, y ∈ openCubeSet Q →
        IsEllipticMatrix (a.coeffOn (cubeDomain Q)).lam
          (a.coeffOn (cubeDomain Q)).Lam ((⇑a.1 : CoeffField d) y) := by
      have h := (a.coeffOn (cubeDomain Q)).aeElliptic
      rw [show volumeMeasureOn ((cubeDomain Q : Domain d) : Set (Vec d)) =
        volume.restrict (openCubeSet Q) from rfl] at h
      exact (ae_restrict_iff' (measurableSet_openCubeSet Q)).1 h
    have hpull := (quasiMeasurePreserving_triadicDilateVec (d := d) N).tendsto_ae hsrc
    have hmem : ∀ᵐ x ∂ volumeMeasureOn
        ((cubeDomain (dilateCube (-(N : ℤ)) Q) : Domain d) : Set (Vec d)),
        x ∈ openCubeSet (dilateCube (-(N : ℤ)) Q) := by
      simpa only [volumeMeasureOn, Book.Ch02.cubeDomain_coe] using
        MeasureTheory.ae_restrict_mem
          (measurableSet_openCubeSet (dilateCube (-(N : ℤ)) Q))
    filter_upwards [ae_restrict_of_ae hpull, hmem] with x hx hxQ
    exact hx (triadicDilateVec_mem_openCubeSet N Q hxQ)

private theorem dilateCube_neg_nat_translate_origin_add
    (N : ℕ) (m : ℤ) (w : Fin d → ℤ) :
    dilateCube (-(N : ℤ))
        (translateCube w (originCube d ((N : ℤ) + m))) =
      translateCube w (originCube d m) := by
  apply congrArg₂ TriadicCube.mk
  · simp [translateCube, originCube]
  · funext i
    simp [translateCube, originCube]

/-- Coarse blocks on a hatted scale are exactly coarse blocks of the original
coefficient at the corresponding physical generation. -/
theorem coarseBlock_standardCell_physical_scale_coeff
    (N : ℕ) (m : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d) :
    coarseBlock (standardCell d m w) (physical_scale_coeff N a) =
      coarseBlock (standardCell d ((N : ℤ) + m) w) a := by
  let Qsrc : TriadicCube d := translateCube w (originCube d ((N : ℤ) + m))
  let Qtgt : TriadicCube d := dilateCube (-(N : ℤ)) Qsrc
  have hcube : Qtgt = translateCube w (originCube d m) := by
    simpa [Qsrc, Qtgt] using
      dilateCube_neg_nat_translate_origin_add (d := d) N m w
  let Usrc : Book.Ch02.Domain d := cubeDomain Qsrc
  let Utgt : Book.Ch02.Domain d := cubeDomain Qtgt
  have hDilation : CoeffOn.IsCubeDilation (-(N : ℤ))
      (a.coeffOn Usrc) (physical_scale_coeffOn N a Qsrc) := by
    change CoeffOn.IsCubeDilation (-(N : ℤ))
      (a.coeffOn (cubeDomain Qsrc))
      (physical_scale_coeffOn N a Qsrc)
    refine ⟨?_, ?_, ?_⟩
    · rfl
    · rfl
    · filter_upwards with x
      rw [CoeffSpace.coeffOn_toCoeffField]
      change rescaleCoeffField N (⇑a.1) x =
        dilateCoeffField (-(N : ℤ)) (⇑a.1) x
      rw [Book.Ch04.rescaleCoeffField_eq_dilateCoeffField_neg_nat (d := d) N]
  have htarget : CoeffOn.AEEq
      ((physical_scale_coeff N a).coeffOn Utgt)
      (physical_scale_coeffOn N a Qsrc) := by
    exact ae_restrict_of_ae (physical_scale_coeff_ae N a)
  have hcov := Book.Ch02.coarseBlockMatrix_dilate hDilation
  calc
    coarseBlock (standardCell d m w) (physical_scale_coeff N a) =
        Book.Ch02.coarseBlockMatrix Utgt
          ((physical_scale_coeff N a).coeffOn Utgt) := by
      simpa [standardCell, Utgt, Book.Ch02.cubeDomain_coe, hcube] using
        coarseBlock_eq_coarseBlockMatrix (physical_scale_coeff N a) Utgt
    _ = Book.Ch02.coarseBlockMatrix Utgt
        (physical_scale_coeffOn N a Qsrc) :=
      Book.Ch02.coarseBlockMatrix_eq_ofAEEq htarget
    _ = Book.Ch02.coarseBlockMatrix Usrc (a.coeffOn Usrc) := by
      simpa [Usrc, Utgt, Qtgt] using hcov
    _ = coarseBlock (standardCell d ((N : ℤ) + m) w) a := by
      simpa [standardCell, Qsrc, Usrc, Book.Ch02.cubeDomain_coe] using
        (coarseBlock_eq_coarseBlockMatrix a Usrc).symm

/-- The normalized positive excess is unchanged by the physical-scale
coarse-block transport. -/
theorem blockExcess_coarseBlock_standardCell_physical_scale_coeff
    (N : ℕ) (m : ℤ) (w : Fin d → ℤ) (a : CoeffSpace d)
    (Abar : BlockMat d) :
    blockExcess (coarseBlock (standardCell d m w) (physical_scale_coeff N a)) Abar =
      blockExcess (coarseBlock (standardCell d ((N : ℤ) + m) w) a) Abar := by
  rw [coarseBlock_standardCell_physical_scale_coeff]

end

end HCPolySupport.HighContrast.Quenched
