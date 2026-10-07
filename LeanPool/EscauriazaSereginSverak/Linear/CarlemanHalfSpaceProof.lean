/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradient
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanCore
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanCoreIntegrability
public import LeanPool.EscauriazaSereginSverak.Linear.CarlemanHalfWeights
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The half-space Carleman inequality

The componentwise conjugation and commutator identities for
`prop:carleman-halfspace`.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS.Main

/-- The product norm on parabolic space-time used for classical differentiation. -/
local instance : NormedAddCommGroup ParabolicPoint :=
  CKN.carlemanProductNormedAddCommGroup

/-- The real scalar action compatible with the product norm on parabolic space-time. -/
local instance : NormedSpace ℝ ParabolicPoint :=
  CKN.carlemanProductNormedSpace

/-- A component of a smooth compactly supported space-time vector field has
the same regularity and lies in the same support. -/
theorem testFunction_component
    {Ω : Set Vec3} {I : Set ℝ}
    {w : ParabolicPoint → Vec3}
    (hw : w ∈ spaceTimeTestFunction Ω I) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => w z i) ∧
      HasCompactSupport (fun z => w z i) ∧
      tsupport (fun z => w z i) ⊆ spaceTimeSet Ω I := by
  rcases hw with ⟨hsmooth, hcompact, hsupport⟩
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun z => w z i) := by
    fun_prop (disch := assumption)
  have hc' : HasCompactSupport ((fun x : Vec3 => x i) ∘ w) :=
    hcompact.comp_left (by simp)
  have hc : HasCompactSupport (fun z => w z i) := by
    simpa only [Function.comp_def] using hc'
  have hs : tsupport (fun z => w z i) ⊆ tsupport w :=
    tsupport_comp_subset (g := fun x : Vec3 => x i) (by simp) w
  exact ⟨hcomp, hc, hs.trans hsupport⟩

/-- The Euclidean norm on three components squares to the coordinate sum. -/
theorem vec3EuclideanNorm_sq (x : Vec3) :
    vec3EuclideanNorm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold vec3EuclideanNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- The vector spatial-gradient density is the sum of its scalar component
densities. -/
theorem spatialGradientSq_eq_sum_scalarGradSq
    (w : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    spatialGradientSq w (spatialGradient w) z =
      ∑ i, CKN.scalarGradSq (fun y => w y i) z := by
  rfl

/-- The squared Euclidean norm of the componentwise heat operator is the
sum of the scalar squares. -/
theorem heatVectorSq_eq_sum
    (w : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    vec3EuclideanNorm (fun i =>
      timePartial (fun y => w y i) z +
        ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 =
      ∑ i, (timePartial (fun y => w y i) z +
        CKN.scalarLaplacian (fun y => w y i) z) ^ 2 := by
  rw [vec3EuclideanNorm_sq]
  rfl

private theorem setIntegral_eq_integral_of_tsupport_subset
    {s : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hfs : tsupport f ⊆ s) :
    (∫ z in s, f z ∂volume) = ∫ z, f z ∂volume := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [] with z
  intro hz
  exact image_eq_zero_of_notMem_tsupport (fun h => hz (hfs h))

private theorem component_conjugation
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    {w : ParabolicPoint → Vec3}
    (hw : w ∈ spaceTimeTestFunction
      {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (hUeq : U = spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (i : Fin 3) :
    let v : ParabolicPoint → ℝ :=
      fun z => Real.exp (φ z) * w z i
    ContDiff ℝ (⊤ : ℕ∞) v ∧
      HasCompactSupport v ∧
      tsupport v ⊆ U ∧
      ∀ z ∈ U,
        carlemanConj φ v z =
          Real.exp (φ z) *
            (timePartial (fun y => w y i) z +
              scalarLaplacian (fun y => w y i) z) := by
  dsimp only
  obtain ⟨hs, hc, hsupp⟩ := testFunction_component hw i
  have hsuppU : tsupport (fun z => w z i) ⊆ U := by
    simpa only [hUeq] using hsupp
  refine ⟨contDiff_exp_mul_of_tsupport hU hφ hs hsuppU,
    hasCompactSupport_exp_mul φ (fun z => w z i) hc,
    (tsupport_exp_mul_subset φ (fun z => w z i)).trans hsuppU, ?_⟩
  intro z hz
  exact carlemanConj_exp_mul hU hφ hs hz

private theorem exp_two_mul (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [show 2 * x = x + x by ring, Real.exp_add]
  ring

private theorem component_mass_sum
    (φ : ParabolicPoint → ℝ) (w : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    (∑ i, (Real.exp (φ z) * w z i) ^ 2) =
      Real.exp (2 * φ z) * vec3EuclideanNorm (w z) ^ 2 := by
  rw [exp_two_mul, vec3EuclideanNorm_sq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem component_gradient_sum
    (φ : ParabolicPoint → ℝ) (w : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    (∑ i, Real.exp (φ z) ^ 2 * scalarGradSq (fun y => w y i) z) =
      Real.exp (2 * φ z) *
        spatialGradientSq w (spatialGradient w) z := by
  rw [exp_two_mul, spatialGradientSq_eq_sum_scalarGradSq, Finset.mul_sum]

private theorem component_heat_sum
    (φ : ParabolicPoint → ℝ) (w : ParabolicPoint → Vec3)
    (z : ParabolicPoint) :
    (∑ i, (Real.exp (φ z) *
      (timePartial (fun y => w y i) z +
        scalarLaplacian (fun y => w y i) z)) ^ 2) =
      Real.exp (2 * φ z) *
        vec3EuclideanNorm (fun i =>
          timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  rw [exp_two_mul, heatVectorSq_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem integral_mul_abs_le_sqrt
    (f g : ParabolicPoint → ℝ)
    (hfm : AEStronglyMeasurable f volume)
    (hgm : AEStronglyMeasurable g volume)
    (hfi : Integrable (fun z => f z ^ 2) volume)
    (hgi : Integrable (fun z => g z ^ 2) volume) :
    |∫ z, f z * g z ∂volume| ≤
      Real.sqrt ((∫ z, f z ^ 2 ∂volume) *
        (∫ z, g z ^ 2 ∂volume)) := by
  have hflp : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hfm).2 hfi
  have hglp : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq hgm).2 hgi
  have hnorm : |∫ z, f z * g z ∂volume| ≤
      ∫ z, |f z| * |g z| ∂volume := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (norm_integral_le_integral_norm (μ := volume)
        (f := fun z => f z * g z))
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume) (f := f) (g := g)
    (Real.holderConjugate_iff.mpr
      (by norm_num : (1 : ℝ) < 2 ∧
        (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1))
    (by convert hflp using 1; norm_num)
    (by convert hglp using 1; norm_num)
  simp_rw [Real.norm_eq_abs, Real.rpow_two, sq_abs] at hholder
  have hV : 0 ≤ ∫ z, f z ^ 2 ∂volume :=
    integral_nonneg (fun z => sq_nonneg _)
  calc
    |∫ z, f z * g z ∂volume| ≤
        ∫ z, |f z| * |g z| ∂volume := hnorm
    _ ≤ (∫ z, f z ^ 2 ∂volume) ^ ((1 : ℝ) / 2) *
      (∫ z, g z ^ 2 ∂volume) ^ ((1 : ℝ) / 2) := hholder
    _ = Real.sqrt ((∫ z, f z ^ 2 ∂volume) *
        (∫ z, g z ^ 2 ∂volume)) := by
      rw [Real.sqrt_mul hV]
      simp only [Real.sqrt_eq_rpow]

private theorem tsupport_subset_of_zero_off
    {E : Type*} [Zero E]
    {f : ParabolicPoint → ℝ} {g : ParabolicPoint → E}
    (h : ∀ z, z ∉ tsupport g → f z = 0) :
    tsupport f ⊆ tsupport g := by
  rw [tsupport]
  apply closure_minimal _ (isClosed_tsupport g)
  intro z hz
  by_contra hn
  exact hz (h z hn)

private theorem carlemanConj_tsupport_subset
    (φ v : ParabolicPoint → ℝ) :
    tsupport (carlemanConj φ v) ⊆ tsupport v := by
  apply tsupport_subset_of_zero_off
  intro z hz
  have hv : v z = 0 := image_eq_zero_of_notMem_tsupport hz
  have ht : timePartial v z = 0 :=
    CKN.timePartial_eq_zero_off_tsupport hz
  have hg (i : Fin 3) : spatialPartial v i z = 0 :=
    CKN.spatialPartial_eq_zero_off_tsupport hz i
  have h2 (i j : Fin 3) : spatialSecondPartial v i j z = 0 :=
    CKN.spatialSecondPartial_eq_zero_off_tsupport hz i j
  simp [carlemanConj, scalarLaplacian, hv, ht, hg, h2]

private theorem carlemanConj_contDiff_compact
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (carlemanConj φ v) ∧
      HasCompactSupport (carlemanConj φ v) ∧
      tsupport (carlemanConj φ v) ⊆ U := by
  have hs := carlemanConj_tsupport_subset φ v
  exact ⟨contDiff_of_local_and_tsupport hU
      (contDiffOn_carlemanConj hU hφ hv) (hs.trans hvU),
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hvU⟩

private theorem conjugated_cross_bound
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    |∫ z, z.2 * v z * carlemanConj φ v z ∂volume| ≤
      Real.sqrt ((∫ z, v z ^ 2 ∂volume) *
        (∫ z, z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume)) := by
  obtain ⟨hcs, hcc, _⟩ := carlemanConj_contDiff_compact hU hφ hv hvc hvU
  let q : ParabolicPoint → ℝ := fun z => z.2 * carlemanConj φ v z
  have hqs : ContDiff ℝ (⊤ : ℕ∞) q := by
    dsimp [q]
    fun_prop (disch := assumption)
  have hqc : HasCompactSupport q := hcc.mul_left
  have hvi : Integrable (fun z => v z ^ 2) volume :=
    integrable_sq_smooth_compact hv hvc
  have hqi : Integrable (fun z => q z ^ 2) volume :=
    integrable_sq_smooth_compact hqs hqc
  have hvm : AEStronglyMeasurable v volume := by
    change AEStronglyMeasurable (fun z : Vec3 × ℝ => v z) volume
    have hcont : Continuous (fun z : Vec3 × ℝ => v z) := hv.continuous
    exact hcont.aestronglyMeasurable
  have hqm : AEStronglyMeasurable q volume := by
    change AEStronglyMeasurable (fun z : Vec3 × ℝ => q z) volume
    have hcont : Continuous (fun z : Vec3 × ℝ => q z) := hqs.continuous
    exact hcont.aestronglyMeasurable
  have hbound := integral_mul_abs_le_sqrt v q hvm hqm hvi hqi
  have hX : (∫ z, z.2 * v z * carlemanConj φ v z ∂volume) =
      ∫ z, v z * q z ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [q]
    ring
  rw [hX]
  convert hbound using 1
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp [q]
  ring

private theorem integrable_conjugated_heat_square
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    Integrable (fun z => z.2 ^ 2 * carlemanConj φ v z ^ 2) volume := by
  obtain ⟨hcs, hcc, _⟩ := carlemanConj_contDiff_compact hU hφ hv hvc hvU
  have hqs : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 * carlemanConj φ v z) := by
    fun_prop (disch := assumption)
  have hqc : HasCompactSupport
      (fun z : ParabolicPoint => z.2 * carlemanConj φ v z) := hcc.mul_left
  have h := integrable_sq_smooth_compact hqs hqc
  change Integrable (fun z : Vec3 × ℝ =>
    z.2 ^ 2 * carlemanConj φ v z ^ 2) volume
  have h' : Integrable (fun z : Vec3 × ℝ =>
      (z.2 * carlemanConj φ v z) ^ 2) volume := h
  simpa only [mul_pow] using h'

private theorem integrable_local_coeff_sq
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {f v : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    Integrable (fun z => f z * v z ^ 2) volume := by
  have hs : tsupport (fun z => v z ^ 2) ⊆ tsupport v := by
    have hs' : tsupport (fun z => v z * v z) ⊆ tsupport v :=
      tsupport_mul_subset_right
    simpa only [pow_two] using hs'
  have hvc2 : HasCompactSupport (fun z => v z ^ 2) :=
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs
  have hvU2 : tsupport (fun z => v z ^ 2) ⊆ U := hs.trans hvU
  change Integrable (fun z : Vec3 × ℝ => f z * v z ^ 2) volume
  exact integrable_mul_of_tsupport hU hf (hv.pow 2) hvc2 hvU2

private theorem conjugated_gradient_pointwise
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    {z : ParabolicPoint} (hz : z ∈ U) (ht : 0 ≤ z.2) :
    z.2 / 2 * Real.exp (2 * φ z) * scalarGradSq w z ≤
      z.2 * scalarGradSq (fun y => Real.exp (φ y) * w y) z +
        z.2 * (Real.exp (φ z) * w z) ^ 2 * scalarGradSq φ z := by
  have h := exp_sq_scalarGradSq_le hU hφ hw hz
  rw [exp_two_mul]
  nlinarith only [mul_nonneg ht (sub_nonneg.mpr h)]

private theorem scalarGradSq_contDiff_compact
    {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarGradSq v) ∧
      HasCompactSupport (scalarGradSq v) ∧
      tsupport (scalarGradSq v) ⊆ tsupport v := by
  have hs : tsupport (scalarGradSq v) ⊆ tsupport v := by
    apply tsupport_subset_of_zero_off
    intro z hz
    have hq (i : Fin 3) : spatialPartial v i z = 0 :=
      CKN.spatialPartial_eq_zero_off_tsupport hz i
    simp [scalarGradSq, hq]
  exact ⟨contDiffOn_univ.mp
      (contDiffOn_scalarGradSq isOpen_univ hv.contDiffOn),
    hvc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs,
    hs⟩

private theorem integrable_time_scalarGradSq
    {v : ParabolicPoint → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) :
    Integrable (fun z => z.2 * scalarGradSq v z) volume := by
  obtain ⟨hgs, hgc, _⟩ := scalarGradSq_contDiff_compact hv hvc
  have ht : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2) Set.univ := by fun_prop
  change Integrable (fun z : Vec3 × ℝ => z.2 * scalarGradSq v z) volume
  exact integrable_mul_of_tsupport isOpen_univ ht hgs hgc (Set.subset_univ _)

private theorem integrable_weighted_scalarGradSq
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    Integrable (fun z => z.2 / 2 * Real.exp (2 * φ z) *
      scalarGradSq w z) volume := by
  obtain ⟨hgs, hgc, hgsupp⟩ := scalarGradSq_contDiff_compact hw hwc
  have hf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 / 2 * Real.exp (2 * φ z)) U := by
    fun_prop (disch := assumption)
  change Integrable (fun z : Vec3 × ℝ =>
    (z.2 / 2 * Real.exp (2 * φ z)) * scalarGradSq w z) volume
  exact integrable_mul_of_tsupport hU hf hgs hgc (hgsupp.trans hwU)

private theorem integrated_conjugated_gradient_bound
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (ht : ∀ z ∈ U, 0 ≤ z.2)
    {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    let v : ParabolicPoint → ℝ :=
      fun z => Real.exp (φ z) * w z
    (∫ z, z.2 / 2 * Real.exp (2 * φ z) *
        scalarGradSq w z ∂volume) ≤
      (∫ z, z.2 * scalarGradSq v z ∂volume) +
      (∫ z, z.2 * v z ^ 2 * scalarGradSq φ z ∂volume) := by
  dsimp only
  let v : ParabolicPoint → ℝ := fun z => Real.exp (φ z) * w z
  have hvs : ContDiff ℝ (⊤ : ℕ∞) v :=
    contDiff_exp_mul_of_tsupport hU hφ hw hwU
  have hvc : HasCompactSupport v := hasCompactSupport_exp_mul φ w hwc
  have hvU : tsupport v ⊆ U :=
    (tsupport_exp_mul_subset φ w).trans hwU
  have hphi : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        z.2 * scalarGradSq φ z) U := by
    have htcd : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => z.2) U := by fun_prop
    exact htcd.mul (contDiffOn_scalarGradSq hU hφ)
  have hleft : Integrable (fun z => z.2 / 2 * Real.exp (2 * φ z) *
      scalarGradSq w z) volume :=
    integrable_weighted_scalarGradSq hU hφ hw hwc hwU
  have hgrad : Integrable (fun z => z.2 * scalarGradSq v z) volume :=
    integrable_time_scalarGradSq hvs hvc
  have hphase : Integrable (fun z =>
      z.2 * v z ^ 2 * scalarGradSq φ z) volume := by
    have h := integrable_local_coeff_sq hU hphi hvs hvc hvU
    convert h using 1
    ext z
    ring
  have hpoint (z : ParabolicPoint) :
      z.2 / 2 * Real.exp (2 * φ z) * scalarGradSq w z ≤
        z.2 * scalarGradSq v z +
          z.2 * v z ^ 2 * scalarGradSq φ z := by
    by_cases hz : z ∈ U
    · exact conjugated_gradient_pointwise hU hφ hw hz (ht z hz)
    · have hzw : z ∉ tsupport w := fun h => hz (hwU h)
      have hzv : z ∉ tsupport v := fun h => hz (hvU h)
      have hgw (i : Fin 3) : spatialPartial w i z = 0 :=
        CKN.spatialPartial_eq_zero_off_tsupport hzw i
      have hgv (i : Fin 3) : spatialPartial v i z = 0 :=
        CKN.spatialPartial_eq_zero_off_tsupport hzv i
      have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hzv
      simp [scalarGradSq, hgw, hgv, hv0]
  have h := integral_mono_ae hleft (hgrad.add hphase)
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at h
  rw [integral_add hgrad hphase] at h
  exact h

private theorem integrated_gradient_rewrite
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U) :
    (∫ z, z.2 * scalarGradSq v z ∂volume) +
      (∫ z, z.2 * v z ^ 2 * scalarGradSq φ z ∂volume) =
      -(1 / 2 : ℝ) * (∫ z, v z ^ 2 ∂volume) -
      (∫ z, z.2 * v z * carlemanConj φ v z ∂volume) +
      (∫ z, (z.2 * (2 * scalarGradSq φ z - timePartial φ z)) *
        v z ^ 2 ∂volume) := by
  have htcd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2) U := by fun_prop
  have hgcd := contDiffOn_scalarGradSq hU hφ
  have hdtcd := contDiffOn_timePartial hU hφ
  have hQcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        z.2 * (scalarGradSq φ z - timePartial φ z)) U :=
    htcd.mul (hgcd.sub hdtcd)
  have hHcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2 * scalarGradSq φ z) U :=
    htcd.mul hgcd
  have hQ : Integrable (fun z =>
      z.2 * v z ^ 2 * (scalarGradSq φ z - timePartial φ z)) volume := by
    convert integrable_local_coeff_sq hU hQcoeff hv hvc hvU using 1
    ext z
    ring
  have hH : Integrable (fun z =>
      z.2 * v z ^ 2 * scalarGradSq φ z) volume := by
    convert integrable_local_coeff_sq hU hHcoeff hv hvc hvU using 1
    ext z
    ring
  have hR :
      (∫ z, (z.2 * (2 * scalarGradSq φ z - timePartial φ z)) *
        v z ^ 2 ∂volume) =
      (∫ z, z.2 * v z ^ 2 *
        (scalarGradSq φ z - timePartial φ z) ∂volume) +
      (∫ z, z.2 * v z ^ 2 * scalarGradSq φ z ∂volume) := by
    rw [← integral_add hQ hH]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  have hG := carleman_gradient_identity 1 hU hφ hv hvc hvU
  simp only [pow_one, Nat.reduceSub, pow_zero, one_mul, Nat.cast_one] at hG
  have hG' :
      (∫ z : ParabolicPoint, z.2 * scalarGradSq v z ∂volume) =
        -(1 / 2 : ℝ) * (∫ z : ParabolicPoint, v z ^ 2 ∂volume) -
        (∫ z : ParabolicPoint,
          z.2 * v z * carlemanConj φ v z ∂volume) +
        (∫ z : ParabolicPoint, z.2 * v z ^ 2 *
          (scalarGradSq φ z - timePartial φ z) ∂volume) := hG
  rw [hR]
  rw [hG']
  ring

private theorem integrated_gradient_coefficient_bound
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v g u : ParabolicPoint → ℝ} (a : ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U)
    (hphase : ∀ z ∈ U,
      z.2 * (2 * scalarGradSq φ z - timePartial φ z) ≤
        2 * g z + a * u z) :
    (∫ z, z.2 * scalarGradSq v z ∂volume) +
      (∫ z, z.2 * v z ^ 2 * scalarGradSq φ z ∂volume) ≤
      |∫ z, z.2 * v z * carlemanConj φ v z ∂volume| +
      2 * (∫ z, g z * v z ^ 2 ∂volume) +
      a * (∫ z, u z * v z ^ 2 ∂volume) := by
  have htcd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint => z.2) U := by fun_prop
  have hRcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ParabolicPoint =>
        z.2 * (2 * scalarGradSq φ z - timePartial φ z)) U := by
    have hgrad := contDiffOn_scalarGradSq hU hφ
    have hdt := contDiffOn_timePartial hU hφ
    fun_prop (disch := assumption)
  have hR : Integrable (fun z =>
      (z.2 * (2 * scalarGradSq φ z - timePartial φ z)) * v z ^ 2) volume :=
    integrable_local_coeff_sq hU hRcoeff hv hvc hvU
  have hGI : Integrable (fun z => g z * v z ^ 2) volume :=
    integrable_local_coeff_sq hU hg hv hvc hvU
  have hUI : Integrable (fun z => u z * v z ^ 2) volume :=
    integrable_local_coeff_sq hU hu hv hvc hvU
  have hRight : Integrable (fun z =>
      (2 * g z + a * u z) * v z ^ 2) volume := by
    have hcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => 2 * g z + a * u z) U :=
      by fun_prop (disch := assumption)
    exact integrable_local_coeff_sq hU hcoeff hv hvc hvU
  have hRI :
      (∫ z, (2 * g z + a * u z) * v z ^ 2 ∂volume) =
      2 * (∫ z, g z * v z ^ 2 ∂volume) +
      a * (∫ z, u z * v z ^ 2 ∂volume) := by
    have hsum : Integrable (fun z =>
        2 * (g z * v z ^ 2) + a * (u z * v z ^ 2)) volume :=
      (hGI.const_mul 2).add (hUI.const_mul a)
    have heq : (∫ z, (2 * g z + a * u z) * v z ^ 2 ∂volume) =
        ∫ z, 2 * (g z * v z ^ 2) + a * (u z * v z ^ 2) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    rw [heq, integral_add (hGI.const_mul 2) (hUI.const_mul a)]
    simp only [integral_const_mul]
  have hpoint (z : ParabolicPoint) :
      (z.2 * (2 * scalarGradSq φ z - timePartial φ z)) * v z ^ 2 ≤
        (2 * g z + a * u z) * v z ^ 2 := by
    by_cases hz : z ∈ U
    · exact mul_le_mul_of_nonneg_right (hphase z hz) (sq_nonneg _)
    · have hv0 : v z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz (hvU h))
      simp [hv0]
  have hRL := integral_mono_ae hR hRight
    (Filter.Eventually.of_forall hpoint)
  have hrewrite := integrated_gradient_rewrite hU hφ hv hvc hvU
  rw [hRI] at hRL
  have hV0 : 0 ≤ ∫ z, v z ^ 2 ∂volume :=
    integral_nonneg (fun z => sq_nonneg _)
  have hX := neg_le_abs (∫ z, z.2 * v z * carlemanConj φ v z ∂volume)
  linarith only [hrewrite, hRL, hV0, hX]

private theorem integrated_weighted_gradient_estimate
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (ht : ∀ z ∈ U, 0 ≤ z.2)
    {φ w g u : ParabolicPoint → ℝ} (a : ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U)
    (hphase : ∀ z ∈ U,
      z.2 * (2 * scalarGradSq φ z - timePartial φ z) ≤
        2 * g z + a * u z) :
    let v : ParabolicPoint → ℝ :=
      fun z => Real.exp (φ z) * w z
    (∫ z, z.2 / 2 * Real.exp (2 * φ z) *
        scalarGradSq w z ∂volume) ≤
      |∫ z, z.2 * v z * carlemanConj φ v z ∂volume| +
      2 * (∫ z, g z * v z ^ 2 ∂volume) +
      a * (∫ z, u z * v z ^ 2 ∂volume) := by
  dsimp only
  let v : ParabolicPoint → ℝ := fun z => Real.exp (φ z) * w z
  have hvs : ContDiff ℝ (⊤ : ℕ∞) v :=
    contDiff_exp_mul_of_tsupport hU hφ hw hwU
  have hvc : HasCompactSupport v := hasCompactSupport_exp_mul φ w hwc
  have hvU : tsupport v ⊆ U :=
    (tsupport_exp_mul_subset φ w).trans hwU
  exact (integrated_conjugated_gradient_bound hU ht hφ hw hwc hwU).trans
    (integrated_gradient_coefficient_bound hU a hφ hg hu hvs hvc hvU hphase)

private theorem integrated_commutator_mass_bound
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ v g u : ParabolicPoint → ℝ} (a θ : ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U)
    (hpoint : ∀ z ∈ U,
      (a * θ * u z + g z) * v z ^ 2 ≤
        carlemanCommutatorDensity φ v z) :
    a * θ * (∫ z, u z * v z ^ 2 ∂volume) +
      (∫ z, g z * v z ^ 2 ∂volume) ≤
      ∫ z, z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume := by
  have huc : Integrable (fun z => u z * v z ^ 2) volume :=
    integrable_local_coeff_sq hU hu hv hvc hvU
  have hgc : Integrable (fun z => g z * v z ^ 2) volume :=
    integrable_local_coeff_sq hU hg hv hvc hvU
  have hmc : Integrable (fun z =>
      (a * θ * u z + g z) * v z ^ 2) volume := by
    have hc : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ParabolicPoint => a * θ * u z + g z) U := by
      fun_prop (disch := assumption)
    exact integrable_local_coeff_sq hU hc hv hvc hvU
  have hdc : Integrable (carlemanCommutatorDensity φ v) volume :=
    integrable_carlemanCommutatorDensity hU hφ hv hvc hvU
  have hglobal (z : ParabolicPoint) :
      (a * θ * u z + g z) * v z ^ 2 ≤
        carlemanCommutatorDensity φ v z := by
    by_cases hz : z ∈ U
    · exact hpoint z hz
    · have hzs : z ∉ tsupport v := fun h => hz (hvU h)
      have hv0 : v z = 0 := image_eq_zero_of_notMem_tsupport hzs
      have hd0 : carlemanCommutatorDensity φ v z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h => hzs (carlemanCommutatorDensity_tsupport_subset φ v h))
      simp [hv0, hd0]
  have hM := integral_mono_ae hmc hdc
    (Filter.Eventually.of_forall hglobal)
  have hM' : a * θ * (∫ z, u z * v z ^ 2 ∂volume) +
      (∫ z, g z * v z ^ 2 ∂volume) ≤
      ∫ z, carlemanCommutatorDensity φ v z ∂volume := by
    have heq :
        (∫ z, (a * θ * u z + g z) * v z ^ 2 ∂volume) =
        ∫ z, (a * θ) * (u z * v z ^ 2) + g z * v z ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    rw [heq, integral_add (huc.const_mul (a * θ)) hgc] at hM
    simpa only [integral_const_mul] using hM
  have hcore : (∫ z : ParabolicPoint,
      carlemanCommutatorDensity φ v z ∂volume) ≤
      ∫ z : ParabolicPoint,
        z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume :=
    carleman_commutator_le hU hφ hv hvc hvU
  exact hM'.trans hcore

private theorem integrated_mass_factor_bound
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {u v : ParabolicPoint → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvc : HasCompactSupport v) (hvU : tsupport v ⊆ U)
    (hfactor : ∀ z ∈ U, 1 ≤ u z) :
    (∫ z, v z ^ 2 ∂volume) ≤
      ∫ z, u z * v z ^ 2 ∂volume := by
  have hvi : Integrable (fun z => v z ^ 2) volume :=
    integrable_sq_smooth_compact hv hvc
  have hui : Integrable (fun z => u z * v z ^ 2) volume :=
    integrable_local_coeff_sq hU hu hv hvc hvU
  apply integral_mono_ae hvi hui
  filter_upwards [] with z
  by_cases hz : z ∈ U
  · simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (hfactor z hz) (sq_nonneg (v z)))
  · have hv0 : v z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hz (hvU h))
    simp [hv0]

private theorem component_derivatives_zero_off_vector_support
    (w : ParabolicPoint → Vec3) {z : ParabolicPoint}
    (hz : z ∉ tsupport w) (i : Fin 3) :
    w z i = 0 ∧
      timePartial (fun y => w y i) z = 0 ∧
      (∀ j, spatialPartial (fun y => w y i) j z = 0) ∧
      (∀ j k, spatialSecondPartial (fun y => w y i) j k z = 0) := by
  have hs : tsupport (fun y => w y i) ⊆ tsupport w :=
    tsupport_comp_subset (g := fun x : Vec3 => x i) (by simp) w
  have hzi : z ∉ tsupport (fun y => w y i) := fun h => hz (hs h)
  exact ⟨(image_eq_zero_of_notMem_tsupport
      (f := fun y : ParabolicPoint => w y i) (x := z) hzi),
    CKN.timePartial_eq_zero_off_tsupport hzi,
    CKN.spatialPartial_eq_zero_off_tsupport hzi,
    CKN.spatialSecondPartial_eq_zero_off_tsupport hzi⟩

private theorem halfSpace_left_tsupport_subset
    (a : ℝ) (φ : ParabolicPoint → ℝ)
    (w : ParabolicPoint → Vec3) :
    tsupport (fun z => z.2 ^ 2 * Real.exp (2 * φ z) *
      (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq w (spatialGradient w) z / z.2)) ⊆
      tsupport w := by
  apply tsupport_subset_of_zero_off
  intro z hz
  have hw0 : w z = 0 := image_eq_zero_of_notMem_tsupport hz
  have hg0 : spatialGradientSq w (spatialGradient w) z = 0 := by
    rw [spatialGradientSq_eq_sum_scalarGradSq]
    apply Finset.sum_eq_zero
    intro i _
    have hi := (component_derivatives_zero_off_vector_support w hz i).2.2.1
    unfold scalarGradSq
    apply Finset.sum_eq_zero
    intro j _
    rw [hi j]
    simp
  simp [hw0, hg0, vec3EuclideanNorm]

private theorem halfSpace_right_tsupport_subset
    (φ : ParabolicPoint → ℝ)
    (w : ParabolicPoint → Vec3) :
    tsupport (fun z => z.2 ^ 2 * Real.exp (2 * φ z) *
      vec3EuclideanNorm (fun i =>
        timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) ⊆
      tsupport w := by
  apply tsupport_subset_of_zero_off
  intro z hz
  have hheat : (fun i =>
        timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) =
      (0 : Vec3) := by
    funext i
    obtain ⟨_, ht, _, hsecond⟩ :=
      component_derivatives_zero_off_vector_support w hz i
    simp [ht, hsecond]
  rw [hheat]
  simp [vec3EuclideanNorm]

private theorem vector_left_density_eq_component_sum
    {U : Set ParabolicPoint}
    (ht : ∀ z ∈ U, 0 < z.2)
    (a : ℝ) (φ : ParabolicPoint → ℝ)
    (w : ParabolicPoint → Vec3)
    (hwU : tsupport w ⊆ U) (z : ParabolicPoint) :
    z.2 ^ 2 * Real.exp (2 * φ z) *
      (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq w (spatialGradient w) z / z.2) =
      ∑ i, (a * (Real.exp (φ z) * w z i) ^ 2 +
        z.2 * Real.exp (2 * φ z) *
          scalarGradSq (fun y => w y i) z) := by
  by_cases hz : z ∈ U
  · have ht0 : z.2 ≠ 0 := ne_of_gt (ht z hz)
    have hmass := component_mass_sum φ w z
    have hgrad : (∑ i, Real.exp (2 * φ z) *
        scalarGradSq (fun y => w y i) z) =
        Real.exp (2 * φ z) *
          spatialGradientSq w (spatialGradient w) z := by
      simpa only [exp_two_mul] using component_gradient_sum φ w z
    calc
      _ = a * Real.exp (2 * φ z) * vec3EuclideanNorm (w z) ^ 2 +
          z.2 * Real.exp (2 * φ z) *
            spatialGradientSq w (spatialGradient w) z := by
        field_simp [ht0]
      _ = a * (∑ i, (Real.exp (φ z) * w z i) ^ 2) +
          z.2 * (∑ i, Real.exp (2 * φ z) *
            scalarGradSq (fun y => w y i) z) := by
        rw [hmass, hgrad]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp_rw [← Finset.mul_sum]
        ring
  · have hzw : z ∉ tsupport w := fun h => hz (hwU h)
    have htarget : z ∉ tsupport (fun z => z.2 ^ 2 *
        Real.exp (2 * φ z) *
          (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
            spatialGradientSq w (spatialGradient w) z / z.2)) :=
      fun h => hzw (halfSpace_left_tsupport_subset a φ w h)
    have hleft : z.2 ^ 2 * Real.exp (2 * φ z) *
        (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
          spatialGradientSq w (spatialGradient w) z / z.2) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : ParabolicPoint => y.2 ^ 2 * Real.exp (2 * φ y) *
          (a * vec3EuclideanNorm (w y) ^ 2 / y.2 ^ 2 +
            spatialGradientSq w (spatialGradient w) y / y.2))
        (x := z) htarget
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨hwi, _, hgrad, _⟩ :=
      component_derivatives_zero_off_vector_support w hzw i
    have hgi : scalarGradSq (fun y => w y i) z = 0 := by
      unfold scalarGradSq
      apply Finset.sum_eq_zero
      intro j _
      rw [hgrad j]
      simp
    simp [hwi, hgi]

private theorem vector_right_density_eq_component_sum
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    {w : ParabolicPoint → Vec3}
    (hw : w ∈ spaceTimeTestFunction
      {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (hUeq : U = spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (z : ParabolicPoint) :
    z.2 ^ 2 * Real.exp (2 * φ z) *
      vec3EuclideanNorm (fun i =>
        timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 =
      ∑ i, z.2 ^ 2 *
        carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2 := by
  have hwU : tsupport w ⊆ U := by
    rw [hUeq]
    exact hw.2.2
  by_cases hz : z ∈ U
  · calc
      _ = z.2 ^ 2 *
          (∑ i, (Real.exp (φ z) *
            (timePartial (fun y => w y i) z +
              scalarLaplacian (fun y => w y i) z)) ^ 2) := by
        rw [component_heat_sum]
        ring
      _ = ∑ i, z.2 ^ 2 *
          (Real.exp (φ z) *
            (timePartial (fun y => w y i) z +
              scalarLaplacian (fun y => w y i) z)) ^ 2 := by
        rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        obtain ⟨hs, _, _⟩ := testFunction_component hw i
        rw [carlemanConj_exp_mul hU hφ hs hz]
  · have hzw : z ∉ tsupport w := fun h => hz (hwU h)
    have htarget : z ∉ tsupport (fun z => z.2 ^ 2 *
        Real.exp (2 * φ z) *
          vec3EuclideanNorm (fun i =>
            timePartial (fun y => w y i) z +
              ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2) :=
      fun h => hzw (halfSpace_right_tsupport_subset φ w h)
    have hleft : z.2 ^ 2 * Real.exp (2 * φ z) *
        vec3EuclideanNorm (fun i =>
          timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y : ParabolicPoint => y.2 ^ 2 *
          Real.exp (2 * φ y) *
            vec3EuclideanNorm (fun i =>
              timePartial (fun q => w q i) y +
                ∑ j, spatialSecondPartial (fun q => w q i) j j y) ^ 2)
        (x := z) htarget
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hs : tsupport (fun y => w y i) ⊆ tsupport w :=
      tsupport_comp_subset (g := fun x : Vec3 => x i) (by simp) w
    have hvi : tsupport (fun y => Real.exp (φ y) * w y i) ⊆ tsupport w :=
      (tsupport_exp_mul_subset φ (fun y => w y i)).trans hs
    have hconj0 : carlemanConj φ
        (fun y => Real.exp (φ y) * w y i) z = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := carlemanConj φ (fun y => Real.exp (φ y) * w y i))
        (x := z) (fun h => hzw
          (hvi (carlemanConj_tsupport_subset φ
            (fun y => Real.exp (φ y) * w y i) h)))
    simp [hconj0]

private theorem vector_left_integral_eq_component_sum
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (ht : ∀ z ∈ U, 0 < z.2)
    (a : ℝ) {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    {w : ParabolicPoint → Vec3}
    (hw : w ∈ spaceTimeTestFunction
      {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (hUeq : U = spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1)) :
    (∫ z in U, z.2 ^ 2 * Real.exp (2 * φ z) *
      (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq w (spatialGradient w) z / z.2) ∂volume) =
      ∑ i, ∫ z, a * (Real.exp (φ z) * w z i) ^ 2 +
        z.2 * Real.exp (2 * φ z) *
          scalarGradSq (fun y => w y i) z ∂volume := by
  have hwU : tsupport w ⊆ U := by
    rw [hUeq]
    exact hw.2.2
  have hLI (i : Fin 3) : Integrable (fun z =>
      a * (Real.exp (φ z) * w z i) ^ 2 +
        z.2 * Real.exp (2 * φ z) *
          scalarGradSq (fun y => w y i) z) volume := by
    obtain ⟨hs, hc, hsupp⟩ := testFunction_component hw i
    have hsuppU : tsupport (fun z => w z i) ⊆ U := by
      rw [hUeq]
      exact hsupp
    have hvs := contDiff_exp_mul_of_tsupport hU hφ hs hsuppU
    have hvc := hasCompactSupport_exp_mul φ (fun z => w z i) hc
    have hmass := integrable_sq_smooth_compact hvs hvc
    have hgrad := integrable_weighted_scalarGradSq hU hφ hs hc hsuppU
    have hgrad' : Integrable (fun z => z.2 * Real.exp (2 * φ z) *
        scalarGradSq (fun y => w y i) z) volume := by
      convert hgrad.const_mul 2 using 1
      ext z
      ring
    exact (hmass.const_mul a).add hgrad'
  have hset : (∫ z in U, z.2 ^ 2 * Real.exp (2 * φ z) *
      (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq w (spatialGradient w) z / z.2) ∂volume) =
      ∫ z, z.2 ^ 2 * Real.exp (2 * φ z) *
        (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
          spatialGradientSq w (spatialGradient w) z / z.2) ∂volume :=
    setIntegral_eq_integral_of_tsupport_subset
      ((halfSpace_left_tsupport_subset a φ w).trans hwU)
  rw [hset]
  have hpoint (z : ParabolicPoint) :=
    vector_left_density_eq_component_sum ht a φ w hwU z
  calc
    _ = ∫ z, ∑ i, (a * (Real.exp (φ z) * w z i) ^ 2 +
        z.2 * Real.exp (2 * φ z) *
          scalarGradSq (fun y => w y i) z) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z
    _ = _ := integral_finsetSum Finset.univ (fun i _ => hLI i)

private theorem vector_right_integral_eq_component_sum
    {U : Set ParabolicPoint} (hU : IsOpen U)
    {φ : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    {w : ParabolicPoint → Vec3}
    (hw : w ∈ spaceTimeTestFunction
      {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (hUeq : U = spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1)) :
    (∫ z in U, z.2 ^ 2 * Real.exp (2 * φ z) *
      vec3EuclideanNorm (fun i =>
        timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 ∂volume) =
      ∑ i, ∫ z, z.2 ^ 2 *
        carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2 ∂volume := by
  have hwU : tsupport w ⊆ U := by
    rw [hUeq]
    exact hw.2.2
  have hRI (i : Fin 3) : Integrable (fun z => z.2 ^ 2 *
      carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2) volume := by
    obtain ⟨hvs, hvc, hvU, _⟩ :=
      component_conjugation hU hφ hw hUeq i
    exact integrable_conjugated_heat_square hU hφ hvs hvc hvU
  have hset : (∫ z in U, z.2 ^ 2 * Real.exp (2 * φ z) *
      vec3EuclideanNorm (fun i =>
        timePartial (fun y => w y i) z +
          ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 ∂volume) =
      ∫ z, z.2 ^ 2 * Real.exp (2 * φ z) *
        vec3EuclideanNorm (fun i =>
          timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 ∂volume :=
    setIntegral_eq_integral_of_tsupport_subset
      ((halfSpace_right_tsupport_subset φ w).trans hwU)
  rw [hset]
  have hpoint (z : ParabolicPoint) :=
    vector_right_density_eq_component_sum hU hφ hw hUeq z
  calc
    _ = ∫ z, ∑ i, z.2 ^ 2 *
        carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z
    _ = _ := integral_finsetSum Finset.univ (fun i _ => hRI i)

private theorem scalar_left_integral_eq_mass_gradient
    {U : Set ParabolicPoint} (hU : IsOpen U)
    (a : ℝ) {φ w : ParabolicPoint → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    (∫ z, a * (Real.exp (φ z) * w z) ^ 2 +
      z.2 * Real.exp (2 * φ z) * scalarGradSq w z ∂volume) =
      a * (∫ z, (Real.exp (φ z) * w z) ^ 2 ∂volume) +
      2 * (∫ z, z.2 / 2 * Real.exp (2 * φ z) *
        scalarGradSq w z ∂volume) := by
  have hvs := contDiff_exp_mul_of_tsupport hU hφ hw hwU
  have hvc := hasCompactSupport_exp_mul φ w hwc
  have hvU : tsupport (fun z => Real.exp (φ z) * w z) ⊆ U :=
    (tsupport_exp_mul_subset φ w).trans hwU
  have hmass : Integrable
      (fun z => (Real.exp (φ z) * w z) ^ 2) volume := by
    have hcoeff : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun _ : ParabolicPoint => (1 : ℝ)) U := contDiffOn_const
    simpa only [one_mul] using
      (integrable_local_coeff_sq hU hcoeff hvs hvc hvU)
  have hgrad := integrable_weighted_scalarGradSq hU hφ hw hwc hwU
  have hgrad' : Integrable (fun z => z.2 * Real.exp (2 * φ z) *
      scalarGradSq w z) volume := by
    convert hgrad.const_mul 2 using 1
    ext z
    ring
  have hscale :
      (∫ z, z.2 * Real.exp (2 * φ z) * scalarGradSq w z ∂volume) =
      2 * (∫ z, z.2 / 2 * Real.exp (2 * φ z) *
        scalarGradSq w z ∂volume) := by
    calc
      _ = ∫ z, 2 * (z.2 / 2 * Real.exp (2 * φ z) *
          scalarGradSq w z) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = _ := integral_const_mul 2 _
  rw [integral_add (hmass.const_mul a) hgrad', integral_const_mul, hscale]

/-- The mass weight `x₃^{2α} t^{-α}` of `prop:carleman-halfspace`. -/
@[expose] noncomputable def halfSpaceMassFactor (α : ℝ) (z : ParabolicPoint) : ℝ :=
  z.1 2 ^ (2 * α) / z.2 ^ α

/-- The normal gradient energy `t |∇φ⁽²⁾|²` of `prop:carleman-halfspace`. -/
@[expose] noncomputable def halfSpaceNormalEnergy (a α : ℝ) (z : ParabolicPoint) : ℝ :=
  z.2 * halfSpaceGradientTwo a α z ^ 2

private theorem halfSpaceMassFactor_contDiffOn (α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (halfSpaceMassFactor α) halfSpaceDomain := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  have hx0 : z.1 2 ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
  have ht0 : z.2 ≠ 0 := ne_of_gt ht.1
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht.1 α)
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y : ParabolicPoint => y.1 2 ^ (2 * α) / y.2 ^ α)
    halfSpaceDomain z
  have hs : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ParabolicPoint => y.1 2 ^ (2 * α) / y.2 ^ α) z := by
    fun_prop
  exact hs.contDiffWithinAt

private theorem halfSpaceNormalEnergy_contDiffOn (a α : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (halfSpaceNormalEnergy a α) halfSpaceDomain := by
  intro z hz
  rcases hz with ⟨hx, ht⟩
  have hx0 : z.1 2 ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
  have ht0 : z.2 ≠ 0 := ne_of_gt ht.1
  have hpow : z.2 ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht.1 α)
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun y : ParabolicPoint =>
      y.2 * (2 * α * a * (1 - y.2) * y.1 2 ^ (2 * α - 1) / y.2 ^ α) ^ 2)
    halfSpaceDomain z
  have hs : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ParabolicPoint =>
        y.2 * (2 * α * a * (1 - y.2) *
          y.1 2 ^ (2 * α - 1) / y.2 ^ α) ^ 2) z := by
    fun_prop
  exact hs.contDiffWithinAt

private theorem halfSpace_scalar_estimate_of_commutator_bound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (a : ℝ) (ha : 2 ≤ a)
    {w : ParabolicPoint → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w)
    (hwU : tsupport w ⊆ halfSpaceDomain)
    (hcomm : ∀ z ∈ halfSpaceDomain,
      (a * (2 * α - 1) * halfSpaceMassFactor α z +
        halfSpaceNormalEnergy a α z) *
        (Real.exp (halfSpacePhase a α z) * w z) ^ 2 ≤
        carlemanCommutatorDensity (halfSpacePhase a α)
          (fun y => Real.exp (halfSpacePhase a α y) * w y) z) :
    (∫ z, a * (Real.exp (halfSpacePhase a α z) * w z) ^ 2 +
      z.2 * Real.exp (2 * halfSpacePhase a α z) *
        scalarGradSq w z ∂volume) ≤
      (5 + 7 / (2 * (2 * α - 1))) *
        (∫ z, z.2 ^ 2 * carlemanConj (halfSpacePhase a α)
          (fun y => Real.exp (halfSpacePhase a α y) * w y) z ^ 2 ∂volume) := by
  let φ := halfSpacePhase a α
  let u := halfSpaceMassFactor α
  let g := halfSpaceNormalEnergy a α
  let v : ParabolicPoint → ℝ := fun z => Real.exp (φ z) * w z
  let V : ℝ := ∫ z, v z ^ 2 ∂volume
  let U : ℝ := ∫ z, u z * v z ^ 2 ∂volume
  let G : ℝ := ∫ z, g z * v z ^ 2 ∂volume
  let D : ℝ := ∫ z, z.2 / 2 * Real.exp (2 * φ z) *
    scalarGradSq w z ∂volume
  let X : ℝ := ∫ z, z.2 * v z * carlemanConj φ v z ∂volume
  let P : ℝ := ∫ z, z.2 ^ 2 * carlemanConj φ v z ^ 2 ∂volume
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ halfSpaceDomain :=
    halfSpacePhase_contDiffOn a α
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) u halfSpaceDomain :=
    halfSpaceMassFactor_contDiffOn α
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g halfSpaceDomain :=
    halfSpaceNormalEnergy_contDiffOn a α
  have hvs : ContDiff ℝ (⊤ : ℕ∞) v :=
    contDiff_exp_mul_of_tsupport isOpen_halfSpaceDomain hφ hw hwU
  have hvc : HasCompactSupport v := hasCompactSupport_exp_mul φ w hwc
  have hvU : tsupport v ⊆ halfSpaceDomain :=
    (tsupport_exp_mul_subset φ w).trans hwU
  have hθ : 0 < 2 * α - 1 := by linarith only [hα]
  have hα0 : 0 < α := by linarith only [hα]
  have hV0 : 0 ≤ V := integral_nonneg (fun z => sq_nonneg _)
  have hVU : V ≤ U :=
    integrated_mass_factor_bound isOpen_halfSpaceDomain hu hvs hvc hvU
      (fun z hz => halfSpacePhase_anisotropicFactor_ge_one α hz hα0)
  have hG0 : 0 ≤ G := by
    apply integral_nonneg
    intro z
    by_cases hz : z ∈ halfSpaceDomain
    · have ht : 0 ≤ z.2 := hz.2.1.le
      dsimp [g, halfSpaceNormalEnergy]
      positivity
    · have hv0 : v z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz (hvU h))
      simp [hv0]
  have hMass : a * (2 * α - 1) * U + G ≤ P :=
    integrated_commutator_mass_bound isOpen_halfSpaceDomain
      a (2 * α - 1) hφ hg hu hvs hvc hvU hcomm
  have hphase (z : ParabolicPoint) (hz : z ∈ halfSpaceDomain) :
      z.2 * (2 * scalarGradSq φ z - timePartial φ z) ≤
        2 * g z + a * u z := by
    convert halfSpacePhase_timeGradient_bound a α hz ha hα0 hα1.le using 1
    dsimp [φ, g, u, halfSpaceNormalEnergy, halfSpaceMassFactor]
    ring
  have ht : ∀ z ∈ halfSpaceDomain, 0 ≤ z.2 :=
    fun z hz => hz.2.1.le
  have hD : D ≤ |X| + 2 * G + a * U :=
    integrated_weighted_gradient_estimate isOpen_halfSpaceDomain ht
      a hφ hg hu hw hwc hwU hphase
  have hX : |X| ≤ Real.sqrt (V * P) :=
    conjugated_cross_bound isOpen_halfSpaceDomain hφ hvs hvc hvU
  have hAbs := halfSpaceAbsorption P U V G D X a (2 * α - 1)
    hθ ha hV0 hVU hG0 hMass hX hD
  have hleft := scalar_left_integral_eq_mass_gradient
    isOpen_halfSpaceDomain a hφ hw hwc hwU
  change (∫ z, a * v z ^ 2 + z.2 * Real.exp (2 * φ z) *
      scalarGradSq w z ∂volume) ≤
    (5 + 7 / (2 * (2 * α - 1))) * P
  rw [hleft]
  exact hAbs

private theorem halfSpace_vector_estimate_of_commutator_bound
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1)
    (a : ℝ) (ha : 2 ≤ a)
    {w : ParabolicPoint → Vec3}
    (hw : w ∈ spaceTimeTestFunction
      {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1))
    (hcomm : ∀ i : Fin 3, ∀ z ∈ halfSpaceDomain,
      (a * (2 * α - 1) * halfSpaceMassFactor α z +
        halfSpaceNormalEnergy a α z) *
        (Real.exp (halfSpacePhase a α z) * w z i) ^ 2 ≤
        carlemanCommutatorDensity (halfSpacePhase a α)
          (fun y => Real.exp (halfSpacePhase a α y) * w y i) z) :
    (∫ z in halfSpaceDomain, z.2 ^ 2 *
      Real.exp (2 * halfSpacePhase a α z) *
      (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq w (spatialGradient w) z / z.2) ∂volume) ≤
      (5 + 7 / (2 * (2 * α - 1))) *
        (∫ z in halfSpaceDomain, z.2 ^ 2 *
          Real.exp (2 * halfSpacePhase a α z) *
          vec3EuclideanNorm (fun i =>
            timePartial (fun y => w y i) z +
              ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 ∂volume) := by
  let φ := halfSpacePhase a α
  have hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ halfSpaceDomain :=
    halfSpacePhase_contDiffOn a α
  have hUeq : halfSpaceDomain = spaceTimeSet
      {x : Vec3 | 1 < x 2} (Ioo (0 : ℝ) 1) := rfl
  have ht : ∀ z ∈ halfSpaceDomain, 0 < z.2 := fun z hz => hz.2.1
  have hLI := vector_left_integral_eq_component_sum
    isOpen_halfSpaceDomain ht a hφ hw hUeq
  have hRI := vector_right_integral_eq_component_sum
    isOpen_halfSpaceDomain hφ hw hUeq
  have hscalar (i : Fin 3) :
      (∫ z, a * (Real.exp (φ z) * w z i) ^ 2 +
        z.2 * Real.exp (2 * φ z) *
          scalarGradSq (fun y => w y i) z ∂volume) ≤
      (5 + 7 / (2 * (2 * α - 1))) *
        (∫ z, z.2 ^ 2 *
          carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2
          ∂volume) := by
    obtain ⟨hs, hc, hsupp⟩ := testFunction_component hw i
    have hsuppU : tsupport (fun z => w z i) ⊆ halfSpaceDomain := by
      rw [hUeq]
      exact hsupp
    exact halfSpace_scalar_estimate_of_commutator_bound
      α hα hα1 a ha hs hc hsuppU (hcomm i)
  change (∫ z in halfSpaceDomain, z.2 ^ 2 * Real.exp (2 * φ z) *
      (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
        spatialGradientSq w (spatialGradient w) z / z.2) ∂volume) ≤
    (5 + 7 / (2 * (2 * α - 1))) *
      (∫ z in halfSpaceDomain, z.2 ^ 2 * Real.exp (2 * φ z) *
        vec3EuclideanNorm (fun i =>
          timePartial (fun y => w y i) z +
            ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 ∂volume)
  calc
    _ = ∑ i, ∫ z, a * (Real.exp (φ z) * w z i) ^ 2 +
          z.2 * Real.exp (2 * φ z) *
            scalarGradSq (fun y => w y i) z ∂volume := hLI
    _ ≤ ∑ i, (5 + 7 / (2 * (2 * α - 1))) *
          (∫ z, z.2 ^ 2 *
            carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2
            ∂volume) := Finset.sum_le_sum (fun i _ => hscalar i)
    _ = (5 + 7 / (2 * (2 * α - 1))) *
          (∑ i, ∫ z, z.2 ^ 2 *
            carlemanConj φ (fun y => Real.exp (φ y) * w y i) z ^ 2
            ∂volume) := by rw [Finset.mul_sum]
    _ = _ := by rw [hRI]

private theorem halfSpaceConstant_pos (α : ℝ) (hα : 1 / 2 < α) :
    0 < 5 + 7 / (2 * (2 * α - 1)) := by
  have hθ : 0 < 2 * α - 1 := by linarith only [hα]
  positivity

/-- The half-space Carleman estimate of `prop:carleman-halfspace` (with
threshold two and constant `5 + 7/(2(2α − 1))` as witnesses), from the
pointwise lower bound of the commutator density for `halfSpacePhase`. -/
theorem halfSpace_estimate_of_pointwise_bound
    (hbound : ∀ (α : ℝ), 1 / 2 < α → α < 1 →
      ∀ (a : ℝ), 2 ≤ a → ∀ (v : ParabolicPoint → ℝ),
        ∀ z ∈ halfSpaceDomain,
          (a * (2 * α - 1) * halfSpaceMassFactor α z +
            halfSpaceNormalEnergy a α z) * v z ^ 2 ≤
            carlemanCommutatorDensity (halfSpacePhase a α) v z) :
    ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ a₀ c : ℝ, 0 < a₀ ∧ 0 < c ∧
      ∀ a : ℝ, a₀ < a → ∀ w : ParabolicPoint → Vec3,
        w ∈ spaceTimeTestFunction (V := Vec3) {x : Vec3 | 1 < x 2} (Ioo 0 1) →
        ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              (a * vec3EuclideanNorm (w z) ^ 2 / z.2 ^ 2 +
                spatialGradientSq w (spatialGradient w) z / z.2) ≤
          c * ∫ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
            z.2 ^ 2 *
              Real.exp (2 * (-(z.1 0 ^ 2 + z.1 1 ^ 2) / (8 * z.2) +
                a * (1 - z.2) * z.1 2 ^ (2 * α) / z.2 ^ α)) *
              vec3EuclideanNorm (fun i => timePartial (fun y => w y i) z +
                ∑ j, spatialSecondPartial (fun y => w y i) j j z) ^ 2 := by
  intro α hα hα1
  refine ⟨2, 5 + 7 / (2 * (2 * α - 1)), by norm_num,
    halfSpaceConstant_pos α hα, ?_⟩
  intro a ha w hw
  have ha2 : 2 ≤ a := ha.le
  have hcomm (i : Fin 3) (z : ParabolicPoint)
      (hz : z ∈ halfSpaceDomain) :
      (a * (2 * α - 1) * halfSpaceMassFactor α z +
        halfSpaceNormalEnergy a α z) *
        (Real.exp (halfSpacePhase a α z) * w z i) ^ 2 ≤
        carlemanCommutatorDensity (halfSpacePhase a α)
          (fun y => Real.exp (halfSpacePhase a α y) * w y i) z :=
    hbound α hα hα1 a ha2
      (fun y => Real.exp (halfSpacePhase a α y) * w y i) z hz
  exact halfSpace_vector_estimate_of_commutator_bound
    α hα hα1 a ha2 hw hcomm

end ESS.Main
