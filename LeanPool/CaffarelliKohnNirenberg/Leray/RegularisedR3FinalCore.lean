/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalWeak
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationIntervalComponent
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEquationResidual
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedConvolutionSmooth
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# The regularized momentum equation on a finite interval: the core

(R3) of `thm:regularised` on `[0, T]`: a velocity that satisfies the regularized
mild equation `eq:reg-mild` on `[0, T]`, and has continuous slices and classical
regularity on `(0, T]`, solves the regularized momentum equation pointwise on
`(0, T)`. This holds in divergence form and, since `J_ε u` is divergence
free, in transport form. The pressure is the canonical Riesz pressure of each
slice, as in (R4). The interval weak momentum identity is tested against scalar
components. After integration by parts, the continuous residual vanishes.
-/

public section

open MeasureTheory Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The product topology on parabolic space-time points used in this weak identity. -/
abbrev regularisedR3FinalBaseTopology :
    TopologicalSpace ParabolicPoint := inferInstance

section ProductRegularity

/-- The product normed additive group used for spatial and temporal regularity. -/
local instance regularisedR3FinalProductNormedAddCommGroup :
    NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The product real normed space used for spatial and temporal derivatives. -/
local instance regularisedR3FinalProductNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))


private theorem regularisedR3Final_contDiffOn_mono
    {S S' : Set (Vec3 × ℝ)} {f : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ 1 f S') (hSS' : S ⊆ S') : ContDiffOn ℝ 1 f S :=
  hf.mono hSS'

private theorem regularisedR3Final_contDiffOn_congr
    {S : Set (Vec3 × ℝ)} {f g : ParabolicPoint → ℝ}
    (hf : ContDiffOn ℝ 1 f S) (hfg : ∀ z ∈ S, f z = g z) :
    ContDiffOn ℝ 1 g S :=
  ContDiffOn.congr hf (fun z hz => (hfg z hz).symm)

end ProductRegularity

/-- Mollification is continuous on the open finite slab, using zero extension only after T. -/
private theorem regularisedR3Final_mollified_continuousOn
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (T : ℝ)
    (hSlice : ∀ t ∈ Set.Icc 0 T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hUjoint : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => regUniformMollifiedVelocity ρ ε hε u z j)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T) := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T
  let uExt : ParabolicPoint → Vec3 := fun z => if z.2 ≤ T then u z else 0
  have hSliceExt (t : ℝ) (ht : 0 < t) :
      MemLp (fun x : Vec3 => uExt (x, t)) 2 volume := by
    by_cases htT : t ≤ T
    · have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht, htT⟩
      simpa [uExt, htT] using hSlice t htIcc
    · simp [uExt, htT]
  have hExtSliceEq (t : ℝ) (htT : t ≤ T) :
      regUniformVelocitySlice uExt t = regUniformVelocitySlice u t := by
    funext x
    simp [regUniformVelocitySlice, uExt, htT]
  have hUExtContDiff (i : Fin 3) :
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 (fun z : ParabolicPoint => uExt z i) S := by
    apply regularisedR3Final_contDiffOn_congr (hUjoint i)
    intro z hz
    simp [uExt, hz.2.2.le]
  have hSpositive : ∀ z ∈ S, 0 < z.2 := fun z hz => hz.2.1
  have hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S := by
    intro z hz y
    exact ⟨Set.mem_univ _, hz.2⟩
  have hJcont := regUniform_mollified_velocity_continuousOn
    ρ ε hε (u := uExt) (S := S) hSliceExt hUExtContDiff
    hSpositive hSshift
  apply (hJcont j).congr
  intro z hz
  change regUniformMollifiedVelocity ρ ε hε u
      ((z.1, z.2) : ParabolicPoint) j =
    regUniformMollifiedVelocity ρ ε hε uExt
      ((z.1, z.2) : ParabolicPoint) j
  unfold regUniformMollifiedVelocity
  rw [hExtSliceEq z.2 hz.2.2.le]

/-- Spatial derivatives of the mollified velocity are continuous on the open finite slab. -/
private theorem regularisedR3Final_mollified_partial_continuousOn
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (T : ℝ)
    (hSlice : ∀ t ∈ Set.Icc 0 T, MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hUjoint : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (j k : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y => regUniformMollifiedVelocity ρ ε hε u y j) k z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T) := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T
  let uExt : ParabolicPoint → Vec3 := fun z => if z.2 ≤ T then u z else 0
  have hSliceExt (t : ℝ) (ht : 0 < t) :
      MemLp (fun x : Vec3 => uExt (x, t)) 2 volume := by
    by_cases htT : t ≤ T
    · have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht, htT⟩
      simpa [uExt, htT] using hSlice t htIcc
    · simp [uExt, htT]
  have hExtSliceEq (t : ℝ) (htT : t ≤ T) :
      regUniformVelocitySlice uExt t = regUniformVelocitySlice u t := by
    funext x
    simp [regUniformVelocitySlice, uExt, htT]
  have hUExtContDiff (i : Fin 3) :
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 (fun z : ParabolicPoint => uExt z i) S := by
    apply regularisedR3Final_contDiffOn_congr (hUjoint i)
    intro z hz
    simp [uExt, hz.2.2.le]
  have hSpositive : ∀ z ∈ S, 0 < z.2 := fun z hz => hz.2.1
  have hSshift : ∀ z ∈ S, ∀ y : Vec3, (z.1 - y, z.2) ∈ S := by
    intro z hz y
    exact ⟨Set.mem_univ _, hz.2⟩
  have hJpartialCont := regUniform_mollified_velocity_spatialPartial_continuousOn
    ρ ε hε (u := uExt) (S := S) hSliceExt hUExtContDiff
    hSpositive hSshift
  apply (hJpartialCont j k).congr
  intro z hz
  change (fderiv ℝ (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε u (x, z.2) j) z.1)
        (basisVec k) =
    (fderiv ℝ (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε uExt (x, z.2) j) z.1)
        (basisVec k)
  have hfun : (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε u (x, z.2) j) =
    (fun x : Vec3 =>
      regUniformMollifiedVelocity ρ ε hε uExt (x, z.2) j) := by
    funext x
    unfold regUniformMollifiedVelocity
    rw [hExtSliceEq z.2 hz.2.2.le]
  rw [hfun]

private theorem regularisedR3Final_mollified_differentiableAt
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hat : MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (x : Vec3) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) j) x := by
  let sliceU : Vec3 → Vec3 := fun x => u (x, t)
  have hsmooth := regUniformMollifiedInitial_contDiff_of_memLp ρ ε hε hat
  have hcoord : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => regUniformMollifiedInitial ρ ε hε sliceU x j) :=
    hsmooth.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) j)
  have hdiff := hcoord.differentiable (by norm_num) x
  have heq : (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) j) =
      fun x => regUniformMollifiedInitial ρ ε hε sliceU x j := by
    funext x
    rfl
  rw [heq]
  exact hdiff

private theorem regularisedR3Final_test_time_continuous
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from ψ) z) := by
  have hfd : Continuous (fun z : Vec3 × ℝ => (fderiv ℝ ψ z) (0, 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply hfd.congr
  intro z
  exact (timePartial_eq_joint_fderiv hψ z).symm

private theorem regularisedR3Final_test_spatial_continuous
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin 3) :
    Continuous (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from ψ) j z) := by
  have hfd : Continuous (fun z : Vec3 × ℝ => (fderiv ℝ ψ z) (basisVec j, 0)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply hfd.congr
  intro z
  exact (spatialPartial_eq_joint_fderiv hψ z j).symm

private theorem regularisedR3Final_test_mul_integrable
    {F ψ : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hF : ContinuousOn F S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ S) :
    Integrable (fun z => F z * ψ z) (volume.restrict S) := by
  exact (regUniform_integrable_mul_of_tsupport_subset hS hF
    hψ.continuous.continuousOn hψc hψs).mono_measure Measure.restrict_le_self

private theorem regularisedR3Final_test_time_mul_integrable
    {F ψ : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hF : ContinuousOn F S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ S) :
    Integrable (fun z => F z * timePartial
      (show ParabolicPoint → ℝ from ψ) z) (volume.restrict S) := by
  exact (regUniform_integrable_mul_of_tsupport_subset hS hF
    (regularisedR3Final_test_time_continuous hψ).continuousOn
    (CKN.hasCompactSupport_timePartial hψc)
    ((CKN.tsupport_timePartial_subset ψ).trans hψs)).mono_measure
      Measure.restrict_le_self

private theorem regularisedR3Final_test_spatial_mul_integrable
    {F ψ : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hF : ContinuousOn F S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ S) (j : Fin 3) :
    Integrable (fun z => F z * spatialPartial
      (show ParabolicPoint → ℝ from ψ) j z) (volume.restrict S) := by
  exact (regUniform_integrable_mul_of_tsupport_subset hS hF
    (regularisedR3Final_test_spatial_continuous hψ j).continuousOn
    (CKN.hasCompactSupport_spatialPartial hψc j)
    ((CKN.tsupport_spatialPartial_subset j).trans hψs)).mono_measure
      Measure.restrict_le_self

private theorem regularisedR3Final_test_time_integrationByParts
    {F ψ : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)}
    (hS : IsOpen S) (hF : ContinuousOn F S)
    (hDt : ContinuousOn (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from F) z) S)
    (hFdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ S) :
    (∫ z in S, F z * timePartial (show ParabolicPoint → ℝ from ψ) z) =
      -∫ z in S, timePartial (show ParabolicPoint → ℝ from F) z * ψ z := by
  exact regUniform_integral_mul_timePartial_eq_neg hS hF hDt hFdiff
    hψ.continuous.continuousOn
    (regularisedR3Final_test_time_continuous hψ).continuousOn
    (fun z hz => regUniform_contDiffOn_timeSlice_differentiableAt hS
      (hψ.of_le (by norm_num)).contDiffOn hz) hψc hψs

private theorem regularisedR3Final_test_spatial_integrationByParts
    {F ψ : Vec3 × ℝ → ℝ} {S : Set (Vec3 × ℝ)} (j : Fin 3)
    (hS : IsOpen S) (hF : ContinuousOn F S)
    (hD : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from F) j z) S)
    (hFdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ S) :
    (∫ z in S, F z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z) =
      -∫ z in S, spatialPartial (show ParabolicPoint → ℝ from F) j z * ψ z := by
  exact regUniform_integral_mul_spatialPartial_eq_neg j hS hF hD hFdiff
    hψ.continuous.continuousOn
    (regularisedR3Final_test_spatial_continuous hψ j).continuousOn
    (fun z hz => regUniform_contDiffOn_spatialSlice_differentiableAt hS
      (hψ.of_le (by norm_num)).contDiffOn hz) hψc hψs

/-- Expand the pairing of a finite-sum residual when each summand is integrable. -/
private theorem regularisedR3Final_integral_residual_expansion
    {S : Set (Vec3 × ℝ)} {A E ψ : Vec3 × ℝ → ℝ}
    {B C : Fin 3 → Vec3 × ℝ → ℝ}
    (hA : Integrable (fun z => A z * ψ z) (volume.restrict S))
    (hB : ∀ j, Integrable (fun z => B j z * ψ z) (volume.restrict S))
    (hC : ∀ j, Integrable (fun z => C j z * ψ z) (volume.restrict S))
    (hE : Integrable (fun z => E z * ψ z) (volume.restrict S)) :
    (∫ z in S, (A z - ∑ j : Fin 3, B j z + ∑ j : Fin 3, C j z + E z) * ψ z) =
      (∫ z in S, A z * ψ z) - (∑ j : Fin 3, ∫ z in S, B j z * ψ z) +
        (∑ j : Fin 3, ∫ z in S, C j z * ψ z) + (∫ z in S, E z * ψ z) := by
  have hBsum := integrable_finsetSum Finset.univ (fun j _ => hB j)
  have hCsum := integrable_finsetSum Finset.univ (fun j _ => hC j)
  have hAB : Integrable (fun z => A z * ψ z - ∑ j : Fin 3, B j z * ψ z)
      (volume.restrict S) := hA.sub hBsum
  have hABC : Integrable (fun z => A z * ψ z - ∑ j : Fin 3, B j z * ψ z +
      ∑ j : Fin 3, C j z * ψ z) (volume.restrict S) := hAB.add hCsum
  simp only [sub_mul, add_mul, Finset.sum_mul]
  rw [integral_add hABC hE, integral_add hAB hCsum, integral_sub hA hBsum,
    integral_finsetSum Finset.univ (fun j _ => hB j),
    integral_finsetSum Finset.univ (fun j _ => hC j)]

/-- Scalar weak momentum gives zero residual pairing after compact-test integration by parts. -/
private theorem regularisedR3Final_scalar_residual_pairing
    {S : Set (Vec3 × ℝ)} (hS : IsOpen S)
    (U P : Vec3 × ℝ → ℝ) (G D : Fin 3 → Vec3 × ℝ → ℝ) (i : Fin 3)
    (hU : ContinuousOn U S) (hP : ContinuousOn P S)
    (hG : ∀ j, ContinuousOn (G j) S) (hD : ∀ j, ContinuousOn (D j) S)
    (hDt : ContinuousOn (fun z : Vec3 × ℝ => timePartial
      (show ParabolicPoint → ℝ from U) z) S)
    (hDp : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from P) i z) S)
    (hDG : ∀ j, ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from G j) j z) S)
    (hDD : ∀ j, ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from D j) j z) S)
    (hUdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun t : ℝ => U (z.1, t)) z.2)
    (hPdiff : ∀ z ∈ S, DifferentiableAt ℝ (fun x : Vec3 => P (x, z.2)) z.1)
    (hGdiff : ∀ j, ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => G j (x, z.2)) z.1)
    (hDdiff : ∀ j, ∀ z ∈ S,
      DifferentiableAt ℝ (fun x : Vec3 => D j (x, z.2)) z.1)
    (ψ : Vec3 × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ S)
    (hWeak : (∫ z in S,
      (-(U z * timePartial (show ParabolicPoint → ℝ from ψ) z)
        - ∑ j : Fin 3, G j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
        + ∑ j : Fin 3, D j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
        - P z * spatialPartial (show ParabolicPoint → ℝ from ψ) i z)) = 0) :
    (∫ z in S,
      (timePartial (show ParabolicPoint → ℝ from U) z
        - ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from D j) j z
        + ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G j) j z
        + spatialPartial (show ParabolicPoint → ℝ from P) i z) * ψ z) = 0 := by
  have hA := regularisedR3Final_test_time_mul_integrable hS hU hψ hψc hψs
  have hB (j : Fin 3) :=
    regularisedR3Final_test_spatial_mul_integrable hS (hG j) hψ hψc hψs j
  have hC (j : Fin 3) :=
    regularisedR3Final_test_spatial_mul_integrable hS (hD j) hψ hψc hψs j
  have hE := regularisedR3Final_test_spatial_mul_integrable hS hP hψ hψc hψs i
  have hR1 := regularisedR3Final_test_mul_integrable hS hDt hψ hψc hψs
  have hR2 (j : Fin 3) := regularisedR3Final_test_mul_integrable hS (hDG j) hψ hψc hψs
  have hR3 (j : Fin 3) := regularisedR3Final_test_mul_integrable hS (hDD j) hψ hψc hψs
  have hR4 := regularisedR3Final_test_mul_integrable hS hDp hψ hψc hψs
  have hBsum := integrable_finsetSum Finset.univ (fun j _ => hB j)
  have hCsum := integrable_finsetSum Finset.univ (fun j _ => hC j)
  have hTime := regularisedR3Final_test_time_integrationByParts
    hS hU hDt hUdiff hψ hψc hψs
  have hConv (j : Fin 3) := regularisedR3Final_test_spatial_integrationByParts
    j hS (hG j) (hDG j) (hGdiff j) hψ hψc hψs
  have hDiff (j : Fin 3) := regularisedR3Final_test_spatial_integrationByParts
    j hS (hD j) (hDD j) (hDdiff j) hψ hψc hψs
  have hPressure := regularisedR3Final_test_spatial_integrationByParts
    i hS hP hDp hPdiff hψ hψc hψs
  have hNegA : Integrable (fun z : Vec3 × ℝ =>
      -(U z * timePartial (show ParabolicPoint → ℝ from ψ) z))
      (volume.restrict S) := hA.neg
  have hAB : Integrable (fun z : Vec3 × ℝ =>
      -(U z * timePartial (show ParabolicPoint → ℝ from ψ) z) -
        ∑ j : Fin 3, G j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
      (volume.restrict S) := hNegA.sub hBsum
  have hABC : Integrable (fun z : Vec3 × ℝ =>
      -(U z * timePartial (show ParabolicPoint → ℝ from ψ) z) -
        ∑ j : Fin 3, G j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z +
        ∑ j : Fin 3, D j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z)
      (volume.restrict S) := hAB.add hCsum
  rw [integral_sub hABC hE,
    integral_add hAB hCsum, integral_sub hNegA hBsum,
    integral_neg, integral_finsetSum Finset.univ (fun j _ => hB j),
    integral_finsetSum Finset.univ (fun j _ => hC j)] at hWeak
  simp only [hTime, hConv, hDiff, hPressure, Finset.sum_neg_distrib] at hWeak
  have hExpand := regularisedR3Final_integral_residual_expansion hR1 hR3 hR2 hR4
  linarith only [hWeak, hExpand]

/-- A classically regular velocity satisfying weak momentum solves the equation pointwise. -/
private theorem regularisedR3Final_pointwise_of_weakMomentum
    (T : ℝ) (u J : ParabolicPoint → Vec3) (P : ParabolicPoint → ℝ)
    (hUiCont : ∀ i : Fin 3, ContinuousOn (fun z : Vec3 × ℝ => u z i)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hDCont : ∀ i j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => u y i) j z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hDDCont : ∀ i j k : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y => spatialPartial (fun x => u x i) j y) k z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hDtCont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => timePartial (fun y => u y i) z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hPCont : ContinuousOn (fun z : Vec3 × ℝ => P z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hDpCont : ∀ i : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial P i z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hUjointS : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hDdiff' : ∀ z ∈ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T,
      ∀ i j : Fin 3, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff' : ∀ z ∈ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T,
      DifferentiableAt ℝ (fun x : Vec3 => P (x, z.2)) z.1)
    (hJCont : ∀ j : Fin 3, ContinuousOn (fun z : Vec3 × ℝ => J z j)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hJpartialC : ∀ j k : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (fun y => J y j) k z)
      ((Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T))
    (hJdiff : ∀ z ∈ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T,
      ∀ j : Fin 3, DifferentiableAt ℝ (fun x : Vec3 => J (x, z.2) j) z.1)
    (hWeakVector : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T),
        (-(∑ k : Fin 3, u z k * timePartial (fun y => φ y k) z)
          - ∑ k : Fin 3, ∑ j : Fin 3,
            J z j * u z k * spatialPartial (fun y => φ y k) j z
          + ∑ k : Fin 3, ∑ j : Fin 3,
            spatialPartial (fun y => u y k) j z * spatialPartial (fun y => φ y k) j z
          - P z * (∑ k : Fin 3, spatialPartial (fun y => φ y k) k z)) = 0) :
    ∀ z : ParabolicPoint,
      z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∀ i : Fin 3,
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, spatialPartial (fun y => J y j * u y i) j z) +
          spatialPartial P i z = 0 := by
  classical
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => u y i) j z
  let DD (i j k : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
  let Dt (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => timePartial (fun y => u y i) z
  let Dp (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => spatialPartial P i z
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  have hUiSpaceDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := by
    simpa [Ui] using regUniform_contDiffOn_spatialSlice_differentiableAt
      hSopen (hUjointS i) hz
  have hUiTimeDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun t : ℝ => Ui i (z.1, t)) z.2 := by
    simpa [Ui] using regUniform_contDiffOn_timeSlice_differentiableAt
      hSopen (hUjointS i) hz
  let G (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z => J (z.1, z.2) j * Ui i z
  have hGcont (i j : Fin 3) : ContinuousOn (G i j) S := by
    change ContinuousOn
      ((fun z : Vec3 × ℝ => J (z.1, z.2) j) * Ui i) S
    exact (hJCont j).mul (hUiCont i)
  have hGpartialFormula (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      spatialPartial (show ParabolicPoint → ℝ from G i j) j z =
        J (z.1, z.2) j * D i j z +
          Ui i z * spatialPartial (fun y => J y j) j z := by
    change spatialPartial
        (fun y : Vec3 × ℝ => J (y.1, y.2) j * Ui i y) j z = _
    exact regUniform_spatialPartial_mul z.1 z.2 j
      (hJdiff z hz j) (hUiSpaceDiff z hz i)
  have hGpartialCont (i j : Fin 3) : ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from G i j) j z) S := by
    apply ContinuousOn.congr
      ((hJCont j).mul (hDCont i j) |>.add ((hUiCont i).mul (hJpartialC j j)))
    intro z hz
    exact hGpartialFormula i j z hz
  have hGdiff (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => G i j (x, z.2)) z.1 := by
    change DifferentiableAt ℝ
      (fun x : Vec3 => J (x, z.2) j * Ui i (x, z.2)) z.1
    exact (hJdiff z hz j).mul (hUiSpaceDiff z hz i)
  have hzero : ∀ i : Fin 3, ∀ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T →
    ∫ z in S,
        (timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, spatialPartial
            (fun y => J y j * u y i) j z) +
          spatialPartial (fun y => P y) i z) * ψ z = 0 := by
    intro i ψ hψ hψc hψs
    have hψTest : ψ ∈ spaceTimeTestFunction (V := ℝ)
        (Set.univ : Set Vec3) (Set.Ioo 0 T) := ⟨hψ, hψc, hψs⟩
    have hscalar := regularisedInterval_scalarWeakMomentum_of_vector
      T u J (fun z i j => spatialPartial (fun y => u y i) j z) P
      hWeakVector i ψ hψTest
    let hscalarPairIntegrand : Vec3 × ℝ → ℝ := fun z =>
        (-(u (parabolicHomeomorph.symm z) i *
            timePartial (show ParabolicPoint → ℝ from ψ) (parabolicHomeomorph.symm z))
          - ∑ j : Fin 3, J (parabolicHomeomorph.symm z) j *
              u (parabolicHomeomorph.symm z) i *
            spatialPartial (show ParabolicPoint → ℝ from ψ) j (parabolicHomeomorph.symm z)
          + ∑ j : Fin 3,
            spatialPartial (fun y => u y i) j (parabolicHomeomorph.symm z) *
              spatialPartial (show ParabolicPoint → ℝ from ψ) j (parabolicHomeomorph.symm z)
          - P (parabolicHomeomorph.symm z) *
            spatialPartial (show ParabolicPoint → ℝ from ψ) i (parabolicHomeomorph.symm z))
    have hscalarS : ∫ z in S, hscalarPairIntegrand z = 0 := by
      have hbridge := CKN.setIntegral_parabolic_to_product
        (Ω := (Set.univ : Set Vec3)) (I := Set.Ioo 0 T)
        (F := fun z : ParabolicPoint =>
          (-(u z i * timePartial (show ParabolicPoint → ℝ from ψ) z)
            - ∑ j : Fin 3, J z j * u z i * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
            + ∑ j : Fin 3, spatialPartial (fun y => u y i) j z *
              spatialPartial (show ParabolicPoint → ℝ from ψ) j z
            - P z * spatialPartial (show ParabolicPoint → ℝ from ψ) i z))
      simpa [hscalarPairIntegrand, S, CKN.spaceTimeSet,
        parabolicHomeomorph_symm_apply] using hbridge.symm.trans hscalar
    have hscalarConverted :
        (∫ z in S,
          (-(Ui i z * timePartial (show ParabolicPoint → ℝ from ψ) z)
            - ∑ j : Fin 3, G i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
            + ∑ j : Fin 3, D i j z * spatialPartial (show ParabolicPoint → ℝ from ψ) j z
            - P z * spatialPartial (show ParabolicPoint → ℝ from ψ) i z)) = 0 := by
      simpa [hscalarPairIntegrand, Ui, G, D] using hscalarS
    exact regularisedR3Final_scalar_residual_pairing hSopen
      (Ui i) (fun z : Vec3 × ℝ => P z) (G i) (D i) i
      (hUiCont i) hPCont (hGcont i) (hDCont i) (hDtCont i) (hDpCont i)
      (hGpartialCont i) (fun j => hDDCont i j j)
      (fun z hz => hUiTimeDiff z hz i) hPdiff' (hGdiff i)
      (fun j z hz => hDdiff' z hz i j) ψ hψ hψc hψs hscalarConverted
  intro z hz i
  let R : Vec3 × ℝ → ℝ := fun z =>
    Dt i z - ∑ j : Fin 3, DD i j j z +
      ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z + Dp i z
  have hRcont : ContinuousOn R S := by
    dsimp [R]
    apply ContinuousOn.add
    · apply ContinuousOn.add
      · exact (hDtCont i).sub (continuousOn_finsetSum _ fun j hj => hDDCont i j j)
      · exact continuousOn_finsetSum _ fun j hj => hGpartialCont i j
    · exact hDpCont i
  have hzeroR : ∀ ψ : Vec3 × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T →
      ∫ z in S, R z * ψ z = 0 := by
    intro ψ hψ hψc hψs
    exact hzero i ψ hψ hψc hψs
  have hpoint := regularised_continuousResidual_eq_zero_of_tests
    T R hRcont hzeroR
  have hz' : ((z.1, z.2) : Vec3 × ℝ) ∈ S := by
    exact ⟨Set.mem_univ _, hz.2⟩
  exact hpoint (z.1, z.2) hz'

/-- The interval weak momentum identity determines the pointwise equation
and the canonical pressure of the regularized mild path (thm:regularised). -/
theorem regularisedR3Final_core
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a)
    (u : ParabolicPoint → Vec3) (T : ℝ) (hT : 0 < T)
    (hSlice : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hL2Continuous : Continuous (fun t : Set.Icc (0 : ℝ) T =>
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)))
    (hDivFree : ∀ t : ℝ, t ∈ Set.Icc 0 T →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hMild : ∀ t : ℝ, (ht : t ∈ Set.Icc 0 T) →
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) =
      realHeatOperator t ht.1
        (realVectorL2OfCoordinateFunction
          (regUniformMollifiedInitial ρ ε hε a)
          (regMollifiedInitial_isInJ ρ ε hε ha).1) -
      regularizedMildStokesIntegral
        (regularizedMildTensorTrajectory ρ ε hε
          (regularisedIntervalMildCurve u T hT.le hSlice)) t)
    (hUcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDDcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i j k : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) k z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDtcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i : Fin 3, ContinuousOn
        (fun z => timePartial (fun y => u y i) z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hPcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ContinuousOn
        (regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDpcontinuous : letI : TopologicalSpace ParabolicPoint :=
      regularisedR3FinalBaseTopology
      ∀ i : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => regularisedIntervalCanonicalPressure
            ρ ε hε u T hT.le hSlice y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hUjoint : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T),
      ∀ i j : Fin 3, DifferentiableAt ℝ
        (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T),
      DifferentiableAt ℝ
        (fun x : Vec3 => regularisedIntervalCanonicalPressure
          ρ ε hε u T hT.le hSlice (x, z.2)) z.1) :
    (∀ z : ParabolicPoint,
      z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∀ i : Fin 3,
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3,
            spatialPartial
              (fun y => regUniformMollifiedVelocity ρ ε hε u y j * u y i) j z) +
          spatialPartial
            (fun y => regularisedIntervalCanonicalPressure
              ρ ε hε u T hT.le hSlice y) i z = 0) ∧
    (∀ z : ParabolicPoint,
      z ∈ spaceTimeSet (Set.univ : Set Vec3) (Set.Ioo 0 T) →
      ∀ i : Fin 3,
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
            spatialPartial (fun y => u y i) j z) +
          spatialPartial
            (fun y => regularisedIntervalCanonicalPressure
              ρ ε hε u T hT.le hSlice y) i z = 0) ∧
    (∀ t : ℝ, ∀ ht : t ∈ Set.Icc 0 T,
      (fun x : Vec3 => regularisedIntervalCanonicalPressure
        ρ ε hε u T hT.le hSlice (x, t)) =ᵐ[volume]
      rieszPressureSliceRepresentative 2 (by norm_num)
        (forcedPressureTensorLp (regularizedMildTensor ρ ε hε
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t))
            (hSlice t ht))))) := by
  classical
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Set.Ioo 0 T
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈
      spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T) := by
    intro z hz
    exact ⟨Set.mem_univ _, ⟨hz.2.1, le_of_lt hz.2.2⟩⟩
  let J : ParabolicPoint → Vec3 :=
    regUniformMollifiedVelocity ρ ε hε u
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => u y i) j z
  let DD (i j k : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
  let Dt (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    timePartial (fun y => u y i) z
  let P : ParabolicPoint → ℝ :=
    regularisedIntervalCanonicalPressure ρ ε hε u T hT.le hSlice
  let Dp (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    spatialPartial (fun y => P y) i z
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  have hUiCont (i : Fin 3) : ContinuousOn (Ui i) S := by
    simpa [Ui, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hUcontinuous i) hSsymm
  have hDCont (i j : Fin 3) : ContinuousOn (D i j) S := by
    simpa [D, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDcontinuous i j) hSsymm
  have hDDCont (i j k : Fin 3) : ContinuousOn (DD i j k) S := by
    simpa [DD, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDDcontinuous i j k) hSsymm
  have hDtCont (i : Fin 3) : ContinuousOn (Dt i) S := by
    simpa [Dt, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDtcontinuous i) hSsymm
  have hPCont : ContinuousOn (fun z : Vec3 × ℝ => P z) S := by
    simpa [P, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) hPcontinuous hSsymm
  have hDpCont (i : Fin 3) : ContinuousOn (Dp i) S := by
    simpa [Dp, P, S, CKN.spaceTimeSet] using
      regUniform_continuousOn_pullback
        (S := spaceTimeSet (Set.univ : Set Vec3) (Set.Ioc 0 T))
        (Sprod := S) (hDpcontinuous i) hSsymm
  have hUjointS (i : Fin 3) :
      letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ContDiffOn ℝ 1 (fun z : ParabolicPoint => u z i) S := by
    exact regularisedR3Final_contDiffOn_mono (hUjoint i)
      (fun z hz => hSsymm z hz)
  have hJCont := regularisedR3Final_mollified_continuousOn ρ ε hε u T hSlice hUjointS
  have hJpartialC :=
    regularisedR3Final_mollified_partial_continuousOn ρ ε hε u T hSlice hUjointS
  have hJdiff (z : Vec3 × ℝ) (hz : z ∈ S) (j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => J (x, z.2) j) z.1 :=
    regularisedR3Final_mollified_differentiableAt ρ ε hε u z.2
      (hSlice z.2 ⟨hz.2.1.le, hz.2.2.le⟩) z.1 j
  have hUiSpaceDiff (z : Vec3 × ℝ) (hz : z ∈ S) (i : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => Ui i (x, z.2)) z.1 := by
    simpa [Ui] using regUniform_contDiffOn_spatialSlice_differentiableAt
      hSopen (hUjointS i) hz
  have hDdiff' (z : Vec3 × ℝ) (hz : z ∈ S) (i j : Fin 3) :
      DifferentiableAt ℝ (fun x : Vec3 => D i j (x, z.2)) z.1 := by
    simpa [D] using hDdiff ((z.1, z.2) : ParabolicPoint) (by
      exact ⟨Set.mem_univ _, hz.2.1, hz.2.2.le⟩) i j
  have hPdiff' (z : Vec3 × ℝ) (hz : z ∈ S) :
      DifferentiableAt ℝ (fun x : Vec3 => P (x, z.2)) z.1 := by
    simpa [P] using hPdiff ((z.1, z.2) : ParabolicPoint) (by
      exact ⟨Set.mem_univ _, hz.2.1, hz.2.2.le⟩)
  have hDivPoint := regularisedR3Final_pointwise_of_weakMomentum T u J P
    hUiCont hDCont hDDCont hDtCont hPCont hDpCont hUjointS hDdiff' hPdiff'
    hJCont hJpartialC hJdiff
    (fun φ hφ => regularisedInterval_weakMomentum ρ ε hε a ha u T hT hSlice
      hL2Continuous hMild hUcontinuous hDcontinuous hPcontinuous hUjoint φ hφ)
  let G (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z => J z j * Ui i z
  have hGpartialFormula (i j : Fin 3) (z : Vec3 × ℝ) (hz : z ∈ S) :
      spatialPartial (show ParabolicPoint → ℝ from G i j) j z =
        J z j * D i j z + Ui i z * spatialPartial (fun y => J y j) j z :=
    regUniform_spatialPartial_mul z.1 z.2 j (hJdiff z hz j) (hUiSpaceDiff z hz i)
  refine ⟨hDivPoint, ?_, ?_⟩
  · intro z hz i
    have hzProd : ((z.1, z.2) : Vec3 × ℝ) ∈ S := ⟨Set.mem_univ _, hz.2⟩
    have ht : z.2 ∈ Set.Icc 0 T := ⟨le_of_lt hz.2.1, le_of_lt hz.2.2⟩
    have hJdiv : ∑ j : Fin 3, spatialPartial (fun y => J y j) j z = 0 :=
      regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u z.2 (hDivFree z.2 ht) z.1
    have hGsum : ∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z =
        ∑ j : Fin 3, J z j * D i j z := by
      calc
        _ = ∑ j : Fin 3,
            (J z j * D i j z + Ui i z * spatialPartial (fun y => J y j) j z) :=
          Finset.sum_congr rfl fun j _ => hGpartialFormula i j z hzProd
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hJdiv, mul_zero, add_zero]
    have hdivG :
        timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, spatialPartial (show ParabolicPoint → ℝ from G i j) j z) +
          spatialPartial (fun y => P y) i z = 0 := hDivPoint z hz i
    rw [hGsum] at hdivG
    exact hdivG
  · intro t ht
    exact regularisedIntervalCanonicalPressure_slice ρ ε hε u T hT.le hSlice t ht

end CKN.Leray

end
