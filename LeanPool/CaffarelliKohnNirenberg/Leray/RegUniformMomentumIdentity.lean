/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Reg Uniform Momentum Identity

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Topology ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The product topology on parabolic space-time points used in this weak identity. -/
abbrev regUniformParabolicTopologyMomentumIdentity : TopologicalSpace ParabolicPoint :=
  inferInstance

/-- The product homeomorphism identifying parabolic points with space-time pairs. -/
@[expose]
def regUniformParabolicHomeomorph : ParabolicPoint ≃ₜ Vec3 × ℝ := by
  exact parabolicHomeomorph

@[simp] private theorem regUniformParabolicHomeomorph_apply
    (z : ParabolicPoint) :
    regUniformParabolicHomeomorph z = (z.1, z.2) := rfl

@[simp] private theorem regUniformParabolicHomeomorph_symm_apply
    (z : Vec3 × ℝ) :
    regUniformParabolicHomeomorph.symm z = ((z.1, z.2) : ParabolicPoint) := rfl

/-- The product normed additive group used for spatial and temporal regularity. -/
local instance : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The product real normed space used for spatial and temporal derivatives. -/
local instance : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The product topology on parabolic space-time points used in this weak identity. -/
local instance (priority := 10000) : TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

private structure RegUniformScalarTestCalculus
    (S : Set (Vec3 × ℝ)) (Phi : Vec3 × ℝ → ℝ) : Prop where
  continuous : ContinuousOn Phi S
  spatialContinuous : ∀ j : Fin 3, ContinuousOn (fun z => spatialPartial Phi j z) S
  timeContinuous : ContinuousOn (fun z => timePartial Phi z) S
  spatialDifferentiable : ∀ z ∈ S,
    DifferentiableAt ℝ (fun x : Vec3 => Phi (x, z.2)) z.1
  timeDifferentiable : ∀ z ∈ S,
    DifferentiableAt ℝ (fun t : ℝ => Phi (z.1, t)) z.2
  compact : HasCompactSupport Phi
  support : tsupport Phi ⊆ S
  spatialCompact : ∀ j : Fin 3, HasCompactSupport (fun z => spatialPartial Phi j z)
  spatialSupport : ∀ j : Fin 3, tsupport (fun z => spatialPartial Phi j z) ⊆ S
  timeCompact : HasCompactSupport (fun z => timePartial Phi z)
  timeSupport : tsupport (fun z => timePartial Phi z) ⊆ S

private structure RegUniformMomentumCalculus
    (S : Set (Vec3 × ℝ)) (Ui p : Vec3 × ℝ → ℝ)
    (J : Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3) : Prop where
  velocityContinuous : ContinuousOn Ui S
  gradientContinuous : ∀ j : Fin 3, ContinuousOn (fun z => spatialPartial Ui j z) S
  secondContinuous : ∀ j : Fin 3, ContinuousOn
    (fun z => spatialPartial (fun y => spatialPartial Ui j y) j z) S
  timeContinuous : ContinuousOn (fun z => timePartial Ui z) S
  pressureContinuous : ContinuousOn p S
  pressureGradientContinuous : ContinuousOn (fun z => spatialPartial p i z) S
  velocitySpatialDifferentiable : ∀ z ∈ S,
    DifferentiableAt ℝ (fun x : Vec3 => Ui (x, z.2)) z.1
  velocityTimeDifferentiable : ∀ z ∈ S,
    DifferentiableAt ℝ (fun t : ℝ => Ui (z.1, t)) z.2
  gradientDifferentiable : ∀ j : Fin 3, ∀ z ∈ S,
    DifferentiableAt ℝ (fun x : Vec3 => spatialPartial Ui j (x, z.2)) z.1
  pressureDifferentiable : ∀ z ∈ S,
    DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1
  mollifiedContinuous : ∀ j : Fin 3, ContinuousOn (J j) S
  mollifiedGradientContinuous : ∀ j : Fin 3,
    ContinuousOn (fun z => spatialPartial (J j) j z) S
  mollifiedDifferentiable : ∀ z ∈ S, ∀ j : Fin 3,
    DifferentiableAt ℝ (fun x : Vec3 => J j (x, z.2)) z.1
  mollifiedDivergence : ∀ z ∈ S, ∑ j : Fin 3, spatialPartial (J j) j z = 0

private structure RegUniformMomentumIntegrability
    (Ui Phi p : Vec3 × ℝ → ℝ) (J : Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3) : Prop where
  testedTime : Integrable (fun z => Ui z * timePartial Phi z) volume
  testedGradient : ∀ j : Fin 3,
    Integrable (fun z => spatialPartial Ui j z * spatialPartial Phi j z) volume
  testedConvection : ∀ j : Fin 3,
    Integrable (fun z => J j z * Ui z * spatialPartial Phi j z) volume
  testedPressure : Integrable (fun z => p z * spatialPartial Phi i z) volume
  equationConvection : ∀ j : Fin 3,
    Integrable (fun z => J j z * spatialPartial Ui j z * Phi z) volume
  equationTime : Integrable (fun z => timePartial Ui z * Phi z) volume
  equationDiffusion : ∀ j : Fin 3, Integrable
    (fun z => spatialPartial (fun y => spatialPartial Ui j y) j z * Phi z) volume
  equationPressure : Integrable (fun z => spatialPartial p i z * Phi z) volume

private theorem regUniform_setIntegral_eq_zero_of_forall_eq_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hs : MeasurableSet s) (f : α → ℝ) (hf : ∀ x ∈ s, f x = 0) :
    (∫ x in s, f x ∂μ) = 0 := by
  rw [setIntegral_congr_fun hs hf]
  simp

private theorem regUniform_integral_sum_neg_of_parts
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (f g a b : Fin 3 → α → ℝ)
    (hf : ∀ j, Integrable (f j) (μ.restrict s))
    (hg : ∀ j, Integrable (g j) (μ.restrict s))
    (ha : ∀ j, Integrable (a j) (μ.restrict s))
    (hb : ∀ j, Integrable (b j) (μ.restrict s))
    (hparts : ∀ j,
      (∫ x in s, f j x ∂μ) =
        (∫ x in s, a j x ∂μ) + (∫ x in s, b j x ∂μ))
    (hibp : ∀ j,
      (∫ x in s, f j x ∂μ) = -(∫ x in s, g j x ∂μ))
    (hzero : (∫ x in s, ∑ j : Fin 3, g j x ∂μ) = 0) :
    (∫ x in s, ∑ j : Fin 3, a j x ∂μ) =
      -(∫ x in s, ∑ j : Fin 3, b j x ∂μ) := by
  have hsumF : (∫ x in s, ∑ j : Fin 3, f j x ∂μ) =
      ∑ j : Fin 3, ∫ x in s, f j x ∂μ := by
    apply integral_finsetSum
    intro j hj
    exact hf j
  have hsumG : (∫ x in s, ∑ j : Fin 3, g j x ∂μ) =
      ∑ j : Fin 3, ∫ x in s, g j x ∂μ := by
    apply integral_finsetSum
    intro j hj
    exact hg j
  have hsumA : (∫ x in s, ∑ j : Fin 3, a j x ∂μ) =
      ∑ j : Fin 3, ∫ x in s, a j x ∂μ := by
    apply integral_finsetSum
    intro j hj
    exact ha j
  have hsumB : (∫ x in s, ∑ j : Fin 3, b j x ∂μ) =
      ∑ j : Fin 3, ∫ x in s, b j x ∂μ := by
    apply integral_finsetSum
    intro j hj
    exact hb j
  have hsumParts :
      (∑ j : Fin 3, ∫ x in s, f j x ∂μ) =
        (∑ j : Fin 3, ∫ x in s, a j x ∂μ) +
          ∑ j : Fin 3, ∫ x in s, b j x ∂μ := by
    calc
      _ = ∑ j : Fin 3,
          ((∫ x in s, a j x ∂μ) + (∫ x in s, b j x ∂μ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hparts j
      _ = _ := Finset.sum_add_distrib
  have hsumIBP :
      (∑ j : Fin 3, ∫ x in s, f j x ∂μ) =
        -(∑ j : Fin 3, ∫ x in s, g j x ∂μ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact hibp j
  have hsumGzero : (∑ j : Fin 3, ∫ x in s, g j x ∂μ) = 0 := by
    rw [← hsumG]
    exact hzero
  have hsumABzero :
      (∑ j : Fin 3, ∫ x in s, a j x ∂μ) +
        ∑ j : Fin 3, ∫ x in s, b j x ∂μ = 0 := by
    rw [← hsumParts, hsumIBP, hsumGzero]
    simp
  rw [hsumA, hsumB]
  exact eq_neg_of_add_eq_zero_left hsumABzero

private theorem regUniform_integral_add_sub_add_of_pointwise_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hs : MeasurableSet s) (q a b c d : α → ℝ)
    (ha : Integrable a (μ.restrict s)) (hb : Integrable b (μ.restrict s))
    (hc : Integrable c (μ.restrict s)) (hd : Integrable d (μ.restrict s))
    (hpoint : ∀ x ∈ s, q x = a x - b x + c x + d x) :
    (∫ x in s, q x ∂μ) =
      (∫ x in s, a x ∂μ) - (∫ x in s, b x ∂μ) +
        (∫ x in s, c x ∂μ) + (∫ x in s, d x ∂μ) := by
  rw [setIntegral_congr_fun hs (fun x hx => hpoint x hx)]
  calc
    _ = (∫ x in s, a x - b x + c x ∂μ) +
        (∫ x in s, d x ∂μ) :=
      integral_add ((ha.sub hb).add hc) hd
    _ = ((∫ x in s, a x ∂μ) - (∫ x in s, b x ∂μ)) +
        (∫ x in s, c x ∂μ) + (∫ x in s, d x ∂μ) := by
      calc
        _ = ((∫ x in s, a x - b x ∂μ) +
            (∫ x in s, c x ∂μ)) + (∫ x in s, d x ∂μ) :=
          congrArg (fun value => value + (∫ x in s, d x ∂μ))
            (integral_add (ha.sub hb) hc)
        _ = _ := congrArg (fun value =>
          value + (∫ x in s, c x ∂μ) + (∫ x in s, d x ∂μ))
            (integral_sub ha hb)

private theorem regUniform_combine_tested_momentum_integrals
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (q t c l p k a b d e : α → ℝ)
    (hq : (∫ x in s, q x ∂μ) =
      -(∫ x in s, t x ∂μ) - (∫ x in s, c x ∂μ) +
        (∫ x in s, l x ∂μ) - (∫ x in s, p x ∂μ))
    (ht : -(∫ x in s, t x ∂μ) = (∫ x in s, a x ∂μ))
    (hc : -(∫ x in s, c x ∂μ) = (∫ x in s, b x ∂μ))
    (hl : (∫ x in s, l x ∂μ) = -(∫ x in s, d x ∂μ))
    (hp : -(∫ x in s, p x ∂μ) = (∫ x in s, e x ∂μ))
    (hdecomp : (∫ x in s, k x ∂μ) =
      (∫ x in s, a x ∂μ) - (∫ x in s, d x ∂μ) +
        (∫ x in s, b x ∂μ) + (∫ x in s, e x ∂μ))
    (hzero : (∫ x in s, k x ∂μ) = 0) :
    (∫ x in s, q x ∂μ) = 0 := by
  rw [hq]
  simp only [sub_eq_add_neg]
  rw [ht, hc, hl, hp]
  calc
    _ = (∫ x in s, a x ∂μ) - (∫ x in s, d x ∂μ) +
        (∫ x in s, b x ∂μ) + (∫ x in s, e x ∂μ) := by ring
    _ = ∫ x in s, k x ∂μ := hdecomp.symm
    _ = 0 := hzero

private theorem regUniform_product_spatial_test_properties
    (Ui Phi : Vec3 × ℝ → ℝ) (S : Set (Vec3 × ℝ))
    (hUiCont : ContinuousOn Ui S) (hPhiCont : ContinuousOn Phi S)
    (hUiDCont : ∀ j : Fin 3, ContinuousOn (fun z => spatialPartial Ui j z) S)
    (hPhiDCont : ∀ j : Fin 3,
      ContinuousOn (fun z => spatialPartial Phi j z) S)
    (hUiDiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => Ui (x, z.2)) z.1)
    (hPhiDiff : ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => Phi (x, z.2)) z.1)
    (hPhiCompact : HasCompactSupport Phi) (hPhiSupport : tsupport Phi ⊆ S) :
    ContinuousOn (fun z => Ui z * Phi z) S ∧
    (∀ j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => Ui y * Phi y) j z) S) ∧
    (∀ z ∈ S, ∀ j : Fin 3,
      spatialPartial (fun y => Ui y * Phi y) j z =
        Ui z * spatialPartial Phi j z + Phi z * spatialPartial Ui j z) ∧
    (∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => Ui (x, z.2) * Phi (x, z.2)) z.1) ∧
    HasCompactSupport (fun z => Ui z * Phi z) ∧
      tsupport (fun z => Ui z * Phi z) ⊆ S := by
  refine ⟨hUiCont.mul hPhiCont, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    apply ContinuousOn.congr
      ((hUiCont.mul (hPhiDCont j)).add (hPhiCont.mul (hUiDCont j)))
    intro z hz
    exact regUniform_spatialPartial_mul z.1 z.2 j (hUiDiff z hz) (hPhiDiff z hz)
  · intro z hz j
    exact regUniform_spatialPartial_mul z.1 z.2 j (hUiDiff z hz) (hPhiDiff z hz)
  · intro z hz
    exact (hUiDiff z hz).mul (hPhiDiff z hz)
  · exact hPhiCompact.mul_left (f := Ui)
  · exact tsupport_mul_subset_right.trans hPhiSupport

private theorem regUniform_convection_tested_identity
    (S : Set (Vec3 × ℝ)) (hSopen : IsOpen S) (hSmeas : MeasurableSet S)
    (Ui Phi : Vec3 × ℝ → ℝ) (J : Fin 3 → Vec3 × ℝ → ℝ)
    (hGCont : ContinuousOn (fun z => Ui z * Phi z) S)
    (hGdCont : ∀ j : Fin 3,
      ContinuousOn (fun z => spatialPartial (fun y => Ui y * Phi y) j z) S)
    (hGformula : ∀ z ∈ S, ∀ j : Fin 3,
      spatialPartial (fun y => Ui y * Phi y) j z =
        Ui z * spatialPartial Phi j z + Phi z * spatialPartial Ui j z)
    (hGdiff : ∀ z ∈ S,
      DifferentiableAt ℝ
        (fun x : Vec3 => Ui (x, z.2) * Phi (x, z.2)) z.1)
    (hGcompact : HasCompactSupport (fun z => Ui z * Phi z))
    (hGsupport : tsupport (fun z => Ui z * Phi z) ⊆ S)
    (hJcont : ∀ j : Fin 3, ContinuousOn (J j) S)
    (hJdCont : ∀ j : Fin 3,
      ContinuousOn (fun z => spatialPartial (J j) j z) S)
    (hJdiff : ∀ z ∈ S, ∀ j : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => J j (x, z.2)) z.1)
    (hDiv : ∀ z ∈ S, ∑ j : Fin 3, spatialPartial (J j) j z = 0)
    (hTestInt : ∀ j : Fin 3, Integrable
      (fun z => J j z * Ui z * spatialPartial Phi j z) volume)
    (hRhsInt : ∀ j : Fin 3, Integrable
      (fun z => J j z * spatialPartial Ui j z * Phi z) volume) :
    (∫ z in S, ∑ j : Fin 3,
      J j z * Ui z * spatialPartial Phi j z ∂volume) =
    -∫ z in S, ∑ j : Fin 3,
      J j z * spatialPartial Ui j z * Phi z ∂volume := by
  have hGpartialCompact (j : Fin 3) : HasCompactSupport
    (fun z => spatialPartial (fun y => Ui y * Phi y) j z) :=
    CKN.hasCompactSupport_spatialPartial hGcompact j
  have hGpartialSupport (j : Fin 3) : tsupport
      (fun z => spatialPartial (fun y => Ui y * Phi y) j z) ⊆ S :=
    (CKN.tsupport_spatialPartial_subset j).trans hGsupport
  have hGint (j : Fin 3) : Integrable
      (fun z => J j z * spatialPartial (fun y => Ui y * Phi y) j z) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hJcont j)
      (hGdCont j) (hGpartialCompact j) (hGpartialSupport j)
  have hJpartialGint (j : Fin 3) : Integrable
      (fun z => spatialPartial (J j) j z * (Ui z * Phi z)) volume :=
    regUniform_integrable_mul_of_tsupport_subset hSopen (hJdCont j)
      hGCont hGcompact hGsupport
  have hJpartialGintS (j : Fin 3) : Integrable
      (fun z => spatialPartial (J j) j z * (Ui z * Phi z))
        (volume.restrict S) :=
    (hJpartialGint j).mono_measure Measure.restrict_le_self
  have hJpartialSumZero :
      (∫ z in S, ∑ j : Fin 3,
        spatialPartial (J j) j z * (Ui z * Phi z) ∂volume) = 0 := by
    apply regUniform_setIntegral_eq_zero_of_forall_eq_zero volume S hSmeas
    intro z hz
    rw [← Finset.sum_mul, hDiv z hz]
    simp
  have hIBP (j : Fin 3) :
      (∫ z in S, J j z * spatialPartial (fun y => Ui y * Phi y) j z ∂volume) =
        -∫ z in S, spatialPartial (J j) j z * (Ui z * Phi z) ∂volume :=
    regUniform_integral_mul_spatialPartial_eq_neg j hSopen
      (hJcont j) (hJdCont j) (fun z hz => hJdiff z hz j)
      hGCont (hGdCont j) (fun z hz => hGdiff z hz)
      hGcompact hGsupport
  have hIBPSum :
      (∫ z in S, ∑ j : Fin 3,
        J j z * spatialPartial (fun y => Ui y * Phi y) j z ∂volume) = 0 := by
    calc
      _ = ∑ j : Fin 3, ∫ z in S,
          J j z * spatialPartial (fun y => Ui y * Phi y) j z ∂volume := by
        apply integral_finsetSum
        intro j hj
        exact (hGint j).mono_measure Measure.restrict_le_self
      _ = -∑ j : Fin 3, ∫ z in S,
          spatialPartial (J j) j z * (Ui z * Phi z) ∂volume := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact hIBP j
      _ = -(∫ z in S, ∑ j : Fin 3,
          spatialPartial (J j) j z * (Ui z * Phi z) ∂volume) := by
        congr 1
        symm
        apply integral_finsetSum
        intro j hj
        exact hJpartialGintS j
      _ = 0 := by rw [hJpartialSumZero]; simp
  have hExpansion (j : Fin 3) :
      (∫ z in S, J j z * spatialPartial (fun y => Ui y * Phi y) j z ∂volume) =
        (∫ z in S, J j z * Ui z * spatialPartial Phi j z ∂volume) +
          ∫ z in S, J j z * spatialPartial Ui j z * Phi z ∂volume := by
    have hpoint (z : Vec3 × ℝ) (hz : z ∈ S) :
        J j z * spatialPartial (fun y => Ui y * Phi y) j z =
          J j z * Ui z * spatialPartial Phi j z +
            J j z * spatialPartial Ui j z * Phi z := by
      rw [hGformula z hz j]
      ring
    have hsum := setIntegral_congr_fun (μ := volume) hSmeas hpoint
    rw [integral_add
      ((hTestInt j).mono_measure Measure.restrict_le_self)
      ((hRhsInt j).mono_measure Measure.restrict_le_self)] at hsum
    exact hsum
  exact regUniform_integral_sum_neg_of_parts volume S
    (fun j z => J j z * spatialPartial (fun y => Ui y * Phi y) j z)
    (fun j z => spatialPartial (J j) j z * (Ui z * Phi z))
    (fun j z => J j z * Ui z * spatialPartial Phi j z)
    (fun j z => J j z * spatialPartial Ui j z * Phi z)
    (fun j => (hGint j).mono_measure Measure.restrict_le_self)
    (fun j => hJpartialGintS j)
    (fun j => (hTestInt j).mono_measure Measure.restrict_le_self)
    (fun j => (hRhsInt j).mono_measure Measure.restrict_le_self)
    hExpansion hIBP hJpartialSumZero

private theorem regUniform_momentum_calculus
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceL2 : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeakDivFree : ∀ t : ℝ, 0 ≤ t →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hUcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial
        (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn
      (fun z => timePartial (fun y => u y i) z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hPcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ContinuousOn p
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial p i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUcontDiff : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      ∀ i j : Fin 3, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) :
    ∀ i : Fin 3, RegUniformMomentumCalculus
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) (fun z => u z i) (fun z => p z)
      (fun j z => regUniformMollifiedVelocity ρ ε hε u z j) i := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  have hSopen : IsOpen S := by
    exact isOpen_univ.prod isOpen_Ioi
  let Smetric : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  have hJcontMetric := regUniform_mollified_velocity_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJpartialMetric := regUniform_mollified_velocity_spatialPartial_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJdiv : ∀ z ∈ S, ∑ j : Fin 3,
      spatialPartial (fun y => regUniformMollifiedVelocity ρ ε hε u y j)
        j z = 0 := by
    intro z hz
    exact regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u z.2
      (hWeakDivFree z.2 (le_of_lt hz.2)) z.1
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => u y i) j z
  let DD (i j k : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
  let Dt (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => timePartial (fun y => u y i) z
  let Dp (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial p i z
  let J (j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => regUniformMollifiedVelocity ρ ε hε u z j
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈ Smetric := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  have hJcont (j : Fin 3) : ContinuousOn (J j) S := by
    simpa [J] using hJcontMetric j
  have hJpartialCont (i j : Fin 3) : ContinuousOn
      (fun z => spatialPartial (J i) j z) S := by
    change ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (fun y : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u y i) j z) S
    exact hJpartialMetric i j
  have hJdiff : ∀ z ∈ S, ∀ j : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => J j (x, z.2)) z.1 := by
    intro z hz j
    let aₜ : Vec3 → Vec3 := fun x => u (x, z.2)
    have hJₜ : CKN.IsInJ aₜ := CKN.weakDivFreeL2_isInJ
      (hWeakDivFree z.2 (le_of_lt hz.2))
    have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε hJₜ
    have hcoord : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε aₜ x j) := by
      exact hsmooth.continuousLinearMap_comp
        (ContinuousLinearMap.proj (R := ℝ) j)
    have hdiff := hcoord.differentiable (by norm_num) z.1
    have heq : (fun x : Vec3 => J j (x, z.2)) =
        fun x => regUniformMollifiedInitial ρ ε hε aₜ x j := by
      funext x
      rfl
    rw [heq]
    exact hdiff
  have hUiSpatialDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := by
    exact regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      (hUcontDiff i) hz
  have hUiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := by
    exact regUniform_contDiffOn_timeSlice_differentiableAt hSopen
      (hUcontDiff i) hz
  have hUiCont (i : Fin 3) : ContinuousOn (Ui i) S := by
    simpa [Ui, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hUcont i) hSsymm
  have hDCont (i j : Fin 3) : ContinuousOn (D i j) S := by
    simpa [D, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDcont i j) hSsymm
  have hDDCont (i j k : Fin 3) : ContinuousOn (DD i j k) S := by
    simpa [DD, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDDcont i j k) hSsymm
  have hDtCont (i : Fin 3) : ContinuousOn (Dt i) S := by
    simpa [Dt, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDtcont i) hSsymm
  have hDpCont (i : Fin 3) : ContinuousOn (Dp i) S := by
    simpa [Dp, S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          (hDpcont i) hSsymm
  have hPcont' : ContinuousOn p S := by
    change ContinuousOn (fun z : Vec3 × ℝ => p z) S
    simpa [S, CKN.spaceTimeSet,
      regUniformParabolicHomeomorph_symm_apply] using
        regUniform_continuousOn_pullback (S := Smetric) (Sprod := S)
          hPcont hSsymm
  intro i
  exact ⟨hUiCont i, hDCont i, (fun j => hDDCont i j j), hDtCont i,
    hPcont', hDpCont i, (fun z hz => hUiSpatialDiff z hz i),
    (fun z hz => hUiTimeDiff z hz i),
    (fun j z hz => hDdiff z hz i j), hPdiff, hJcont,
    (fun j => hJpartialCont j j), hJdiff, hJdiv⟩

private theorem regUniform_scalar_test_calculus
    (S : Set (Vec3 × ℝ)) (hSopen : IsOpen S) (Phi : Vec3 × ℝ → ℝ)
    (hSmooth : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hCompact : HasCompactSupport Phi) (hSupport : tsupport Phi ⊆ S) :
    RegUniformScalarTestCalculus S Phi := by
  exact ⟨hSmooth.continuous.continuousOn,
    (fun j => (spatialPartial_contDiff hSmooth j).continuous.continuousOn),
    (CKN.Core.Step3.timePartial_contDiff_full hSmooth).continuous.continuousOn,
    (fun z hz => regUniform_contDiffOn_spatialSlice_differentiableAt hSopen
      ((hSmooth.of_le (by norm_num)).contDiffOn) hz),
    (fun z hz => regUniform_contDiffOn_timeSlice_differentiableAt hSopen
      ((hSmooth.of_le (by norm_num)).contDiffOn) hz),
    hCompact, hSupport, (fun j => CKN.hasCompactSupport_spatialPartial hCompact j),
    (fun j => (CKN.tsupport_spatialPartial_subset j).trans hSupport),
    CKN.hasCompactSupport_timePartial hCompact,
    (CKN.tsupport_timePartial_subset Phi).trans hSupport⟩

private theorem regUniform_momentum_integrability
    (S : Set (Vec3 × ℝ)) (hSopen : IsOpen S)
    (Ui Phi p : Vec3 × ℝ → ℝ) (J : Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3)
    (hCalculus : RegUniformMomentumCalculus S Ui p J i)
    (hTest : RegUniformScalarTestCalculus S Phi) :
    RegUniformMomentumIntegrability Ui Phi p J i := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact regUniform_integrable_mul_of_tsupport_subset hSopen
      hCalculus.velocityContinuous hTest.timeContinuous hTest.timeCompact hTest.timeSupport
  · intro j
    exact regUniform_integrable_mul_of_tsupport_subset hSopen
      (hCalculus.gradientContinuous j) (hTest.spatialContinuous j)
      (hTest.spatialCompact j) (hTest.spatialSupport j)
  · intro j
    exact regUniform_integrable_mul_of_tsupport_subset hSopen
      ((hCalculus.mollifiedContinuous j).mul hCalculus.velocityContinuous)
      (hTest.spatialContinuous j) (hTest.spatialCompact j) (hTest.spatialSupport j)
  · exact regUniform_integrable_mul_of_tsupport_subset hSopen
      hCalculus.pressureContinuous (hTest.spatialContinuous i)
      (hTest.spatialCompact i) (hTest.spatialSupport i)
  · intro j
    exact regUniform_integrable_mul_of_tsupport_subset hSopen
      ((hCalculus.mollifiedContinuous j).mul (hCalculus.gradientContinuous j))
      hTest.continuous hTest.compact hTest.support
  · exact regUniform_integrable_mul_of_tsupport_subset hSopen
      hCalculus.timeContinuous hTest.continuous hTest.compact hTest.support
  · intro j
    exact regUniform_integrable_mul_of_tsupport_subset hSopen
      (hCalculus.secondContinuous j) hTest.continuous hTest.compact hTest.support
  · exact regUniform_integrable_mul_of_tsupport_subset hSopen
      hCalculus.pressureGradientContinuous hTest.continuous hTest.compact hTest.support

private theorem regUniform_momentum_spatial_ibp
    (S : Set (Vec3 × ℝ)) (hSopen : IsOpen S) (hSmeas : MeasurableSet S)
    (Ui Phi p : Vec3 × ℝ → ℝ) (J : Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3)
    (hCalculus : RegUniformMomentumCalculus S Ui p J i)
    (hTest : RegUniformScalarTestCalculus S Phi)
    (hInt : RegUniformMomentumIntegrability Ui Phi p J i) :
    ((∫ z in S, ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z ∂volume) =
      -∫ z in S, ∑ j : Fin 3, J j z * spatialPartial Ui j z * Phi z ∂volume) ∧
    ((∫ z in S, ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z ∂volume) =
      -∫ z in S, ∑ j : Fin 3,
        spatialPartial (fun y => spatialPartial Ui j y) j z * Phi z ∂volume) ∧
    ((∫ z in S, p z * spatialPartial Phi i z ∂volume) =
      -∫ z in S, spatialPartial p i z * Phi z ∂volume) := by
  have hProduct := regUniform_product_spatial_test_properties Ui Phi S
    hCalculus.velocityContinuous hTest.continuous hCalculus.gradientContinuous
    hTest.spatialContinuous hCalculus.velocitySpatialDifferentiable
    hTest.spatialDifferentiable hTest.compact hTest.support
  refine ⟨?_, ?_, ?_⟩
  · exact regUniform_convection_tested_identity S hSopen hSmeas Ui Phi J
      hProduct.1 hProduct.2.1 hProduct.2.2.1 hProduct.2.2.2.1
      hProduct.2.2.2.2.1 hProduct.2.2.2.2.2
      hCalculus.mollifiedContinuous hCalculus.mollifiedGradientContinuous
      hCalculus.mollifiedDifferentiable hCalculus.mollifiedDivergence
      hInt.testedConvection hInt.equationConvection
  · calc
      _ = ∑ j : Fin 3, ∫ z in S,
          spatialPartial Ui j z * spatialPartial Phi j z ∂volume := by
        apply integral_finsetSum
        intro j hj
        exact (hInt.testedGradient j).mono_measure Measure.restrict_le_self
      _ = -∑ j : Fin 3, ∫ z in S,
          spatialPartial (fun y => spatialPartial Ui j y) j z * Phi z ∂volume := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        exact regUniform_integral_mul_spatialPartial_eq_neg j hSopen
          (hCalculus.gradientContinuous j) (hCalculus.secondContinuous j)
          (hCalculus.gradientDifferentiable j) hTest.continuous
          (hTest.spatialContinuous j) hTest.spatialDifferentiable hTest.compact hTest.support
      _ = _ := by
        congr 1
        symm
        apply integral_finsetSum
        intro j hj
        exact (hInt.equationDiffusion j).mono_measure Measure.restrict_le_self
  · exact regUniform_integral_mul_spatialPartial_eq_neg i hSopen
      hCalculus.pressureContinuous hCalculus.pressureGradientContinuous
      hCalculus.pressureDifferentiable hTest.continuous (hTest.spatialContinuous i)
      hTest.spatialDifferentiable hTest.compact hTest.support

private theorem regUniform_scalar_momentum_assembly
    (S : Set (Vec3 × ℝ)) (hSopen : IsOpen S) (hSmeas : MeasurableSet S)
    (Ui Phi p : Vec3 × ℝ → ℝ) (J : Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3)
    (hCalculus : RegUniformMomentumCalculus S Ui p J i)
    (hTest : RegUniformScalarTestCalculus S Phi)
    (hEquation : ∀ z ∈ S,
      timePartial Ui z - (∑ j : Fin 3, spatialPartial
        (fun y => spatialPartial Ui j y) j z) +
        (∑ j : Fin 3, J j z * spatialPartial Ui j z) + spatialPartial p i z = 0) :
    let Q : Vec3 × ℝ → ℝ := fun z =>
      -(Ui z * timePartial Phi z) - ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z
        + ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z
        - p z * spatialPartial Phi i z
    Integrable Q (volume.restrict S) ∧ (∫ z in S, Q z ∂volume) = 0 := by
  let Q : Vec3 × ℝ → ℝ := fun z =>
    -(Ui z * timePartial Phi z) - ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z
      + ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z
      - p z * spatialPartial Phi i z
  let A : Vec3 × ℝ → ℝ := fun z => timePartial Ui z * Phi z
  let B : Vec3 × ℝ → ℝ := fun z => ∑ j : Fin 3,
    spatialPartial (fun y => spatialPartial Ui j y) j z * Phi z
  let C : Vec3 × ℝ → ℝ := fun z => ∑ j : Fin 3, J j z * spatialPartial Ui j z * Phi z
  let E : Vec3 × ℝ → ℝ := fun z => spatialPartial p i z * Phi z
  let K : Vec3 × ℝ → ℝ := fun z =>
    (timePartial Ui z - (∑ j : Fin 3, spatialPartial
      (fun y => spatialPartial Ui j y) j z) +
      (∑ j : Fin 3, J j z * spatialPartial Ui j z) + spatialPartial p i z) * Phi z
  have hInt := regUniform_momentum_integrability S hSopen Ui Phi p J i hCalculus hTest
  have hSpatial := regUniform_momentum_spatial_ibp S hSopen hSmeas
    Ui Phi p J i hCalculus hTest hInt
  have hTimeInt : Integrable (fun z => Ui z * timePartial Phi z) (volume.restrict S) :=
    hInt.testedTime.mono_measure Measure.restrict_le_self
  have hConvInt : Integrable
      (fun z => ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z)
      (volume.restrict S) :=
    integrable_finsetSum Finset.univ (fun j hj =>
      (hInt.testedConvection j).mono_measure Measure.restrict_le_self)
  have hDiffInt : Integrable
      (fun z => ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z)
      (volume.restrict S) :=
    integrable_finsetSum Finset.univ (fun j hj =>
      (hInt.testedGradient j).mono_measure Measure.restrict_le_self)
  have hPressureInt : Integrable (fun z => p z * spatialPartial Phi i z)
      (volume.restrict S) := hInt.testedPressure.mono_measure Measure.restrict_le_self
  have hAInt : Integrable A (volume.restrict S) :=
    hInt.equationTime.mono_measure Measure.restrict_le_self
  have hBInt : Integrable B (volume.restrict S) :=
    integrable_finsetSum Finset.univ (fun j hj =>
      (hInt.equationDiffusion j).mono_measure Measure.restrict_le_self)
  have hCInt : Integrable C (volume.restrict S) :=
    integrable_finsetSum Finset.univ (fun j hj =>
      (hInt.equationConvection j).mono_measure Measure.restrict_le_self)
  have hEInt : Integrable E (volume.restrict S) :=
    hInt.equationPressure.mono_measure Measure.restrict_le_self
  have hQdecomp : (∫ z in S, Q z ∂volume) =
      -(∫ z in S, Ui z * timePartial Phi z ∂volume) -
        (∫ z in S, ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z ∂volume) +
        (∫ z in S, ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z ∂volume) -
        (∫ z in S, p z * spatialPartial Phi i z ∂volume) := by
    have hDecomposition := regUniform_integral_add_sub_add_of_pointwise_eq volume S hSmeas
      Q (fun z => -(Ui z * timePartial Phi z))
      (fun z => ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z)
      (fun z => ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z)
      (fun z => -(p z * spatialPartial Phi i z))
      hTimeInt.neg hConvInt hDiffInt hPressureInt.neg
      (fun z hz => by dsimp [Q]; ring)
    simpa only [integral_neg, sub_eq_add_neg] using hDecomposition
  have hTime : -(∫ z in S, Ui z * timePartial Phi z ∂volume) =
      ∫ z in S, A z ∂volume := by
    rw [regUniform_integral_mul_timePartial_eq_neg hSopen
      hCalculus.velocityContinuous hCalculus.timeContinuous
      hCalculus.velocityTimeDifferentiable hTest.continuous hTest.timeContinuous
      hTest.timeDifferentiable hTest.compact hTest.support]
    simp [A]
  have hConv : -(∫ z in S, ∑ j : Fin 3,
      J j z * Ui z * spatialPartial Phi j z ∂volume) = ∫ z in S, C z ∂volume := by
    rw [hSpatial.1]
    simp [C]
  have hPressure : -(∫ z in S, p z * spatialPartial Phi i z ∂volume) =
      ∫ z in S, E z ∂volume := by
    rw [hSpatial.2.2]
    simp [E]
  have hKdecomp : (∫ z in S, K z ∂volume) =
      (∫ z in S, A z ∂volume) - (∫ z in S, B z ∂volume) +
        (∫ z in S, C z ∂volume) + (∫ z in S, E z ∂volume) := by
    apply regUniform_integral_add_sub_add_of_pointwise_eq volume S hSmeas
      K A B C E hAInt hBInt hCInt hEInt
    intro z hz
    simp only [K, A, B, C, E, sub_mul, add_mul, Finset.sum_mul]
  have hKzero : (∫ z in S, K z ∂volume) = 0 := by
    apply regUniform_setIntegral_eq_zero_of_forall_eq_zero volume S hSmeas
    intro z hz
    dsimp [K]
    rw [hEquation z hz, zero_mul]
  refine ⟨((hTimeInt.neg.sub hConvInt).add hDiffInt).sub hPressureInt, ?_⟩
  exact regUniform_combine_tested_momentum_integrals volume S Q
    (fun z => Ui z * timePartial Phi z)
    (fun z => ∑ j : Fin 3, J j z * Ui z * spatialPartial Phi j z)
    (fun z => ∑ j : Fin 3, spatialPartial Ui j z * spatialPartial Phi j z)
    (fun z => p z * spatialPartial Phi i z) K A C B E
    hQdecomp hTime hConv hSpatial.2.1 hPressure hKdecomp hKzero

/-- The pointwise equation (R3), positive-time regularity (R1)–(R2), and
weak solenoidality imply the regularized momentum identity in
`lem:reg-momentum`. -/
theorem regUniform_momentum_identity
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceL2 : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeakDivFree : ∀ t : ℝ, 0 ≤ t →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hUcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i j : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => u y i) j z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i j k : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => spatialPartial
        (fun x => u x i) j y) k z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn
      (fun z => timePartial (fun y => u y i) z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hPcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ContinuousOn p
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyMomentumIdentity
      ∀ i : Fin 3, ContinuousOn
      (fun z => spatialPartial (fun y => p y) i z)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUcontDiff : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      ∀ i j : Fin 3, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (hEquation : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => u y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) j z) +
        (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
          spatialPartial (fun y => u y i) j z) +
        spatialPartial (fun y => p y) i z = 0)
    (φ : ParabolicPoint → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioi 0)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * u z i *
            spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j z *
            spatialPartial (fun y => φ y i) j z
        - p z * (∑ i : Fin 3,
          spatialPartial (fun y => φ y i) i z)) = 0 := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioi
  have hSmeas : MeasurableSet S :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let Phi (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => φ z i
  let J (j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => regUniformMollifiedVelocity ρ ε hε u z j
  let Q (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    -(Ui i z * timePartial (Phi i) z)
      - ∑ j : Fin 3, J j z * Ui i z * spatialPartial (Phi i) j z
      + ∑ j : Fin 3, spatialPartial (Ui i) j z * spatialPartial (Phi i) j z
      - p z * spatialPartial (Phi i) i z
  have hCalculus := regUniform_momentum_calculus ρ ε hε u p
    hSliceL2 hWeakDivFree hUcont hDcont hDDcont hDtcont hPcont hDpcont
    hUcontDiff hDdiff hPdiff
  have hScalar (i : Fin 3) :
      Integrable (Q i) (volume.restrict S) ∧ (∫ z in S, Q i z ∂volume) = 0 := by
    have hφi := CKN.component_mem_spaceTimeTestFunction hφ i
    have hTest : RegUniformScalarTestCalculus S (Phi i) :=
      regUniform_scalar_test_calculus S hSopen (Phi i) hφi.1 hφi.2.1 hφi.2.2
    exact regUniform_scalar_momentum_assembly S hSopen hSmeas
      (Ui i) (Phi i) (fun z => p z) J i (hCalculus i) hTest
      (fun z hz => hEquation z hz.2 i)
  change (∫ z : Vec3 × ℝ in S,
    (-(∑ i : Fin 3, Ui i z * timePartial (Phi i) z)
      - ∑ i : Fin 3, ∑ j : Fin 3,
        J j z * Ui i z * spatialPartial (Phi i) j z
      + ∑ i : Fin 3, ∑ j : Fin 3,
        spatialPartial (Ui i) j z * spatialPartial (Phi i) j z
      - p z * (∑ i : Fin 3, spatialPartial (Phi i) i z))) = 0
  rw [setIntegral_congr_fun
    (g := fun z : Vec3 × ℝ => ∑ i : Fin 3, Q i z) hSmeas (fun z hz => by
    simp [Q, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum])]
  rw [integral_finsetSum Finset.univ (fun i hi => (hScalar i).1)]
  simp_rw [(hScalar _).2]
  simp
end CKN.Leray
end
