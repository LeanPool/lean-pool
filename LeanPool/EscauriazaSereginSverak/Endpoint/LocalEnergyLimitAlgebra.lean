/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyEquality
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Local Energy Limit Algebra

Local energy identities and limit passages for the endpoint regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

local instance localEnergyLimitAlgebraHolderTripleFourFourTwo :
    ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  have hreal : Real.HolderTriple 4 4 2 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitAlgebraHolderTripleFourFourFourThirds :
    ENNReal.HolderTriple 2 4 (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hreal : Real.HolderTriple 2 4 (4 / 3) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitAlgebraHolderTripleFourThirdsFourOne :
    ENNReal.HolderTriple (ENNReal.ofReal (4 / 3 : ℝ)) 4 1 := by
  have hreal : Real.HolderTriple (4 / 3) 4 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitAlgebraHolderTripleThreeHalvesFourTwelveElevenths :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 4
      (ENNReal.ofReal (12 / 11 : ℝ)) := by
  have hreal : Real.HolderTriple (3 / 2) 4 (12 / 11) := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitAlgebraHolderTripleTwelveEleventhsTwelveOne :
    ENNReal.HolderTriple (ENNReal.ofReal (12 / 11 : ℝ)) 12 1 := by
  have hreal : Real.HolderTriple (12 / 11) 12 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

local instance localEnergyLimitAlgebraHolderTripleTwoTwoOne :
    ENNReal.HolderTriple 2 2 1 := by
  have hreal : Real.HolderTriple 2 2 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  simpa using hreal.ennrealOfReal

/-- The product-space direction corresponding to the `j`th spatial coordinate. -/
@[expose] def localEnergyLimitSpatialDir (j : Fin 3) : Vec3 × ℝ := spatialDir j

/-- The product-space direction corresponding to the time coordinate. -/
@[expose] def localEnergyLimitTimeDir : Vec3 × ℝ := timeDir

private theorem localEnergy_timePartial_eq_fderiv_apply
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : Vec3 × ℝ) :
    timePartial (show ParabolicPoint → ℝ from ψ) z =
      (fderiv ℝ ψ z) localEnergyLimitTimeDir := by
  have hinner : HasFDerivAt (fun t : ℝ => (z.1, t))
      (ContinuousLinearMap.inr ℝ Vec3 ℝ) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have houter : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
    (hψ.differentiable (by norm_num) z).hasFDerivAt
  have hcomp := houter.comp z.2 hinner
  have hfd : fderiv ℝ (fun t : ℝ => ψ (z.1, t)) z.2 =
      (fderiv ℝ ψ z).comp (ContinuousLinearMap.inr ℝ Vec3 ℝ) := hcomp.fderiv
  change (fderiv ℝ (fun t : ℝ => ψ (z.1, t)) z.2) 1 = _
  rw [hfd]
  change (fderiv ℝ ψ z) (0, 1) = (fderiv ℝ ψ z) (0, 1)
  rfl

private theorem localEnergy_spatialPartial_eq_fderiv_apply
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (show ParabolicPoint → ℝ from ψ) j z =
      (fderiv ℝ ψ z) (localEnergyLimitSpatialDir j) := by
  have hinner : HasFDerivAt (fun x : Vec3 => (x, z.2))
      (ContinuousLinearMap.inl ℝ Vec3 ℝ) z.1 :=
    hasFDerivAt_prodMk_left z.1 z.2
  have houter : HasFDerivAt ψ (fderiv ℝ ψ z) z :=
    (hψ.differentiable (by norm_num) z).hasFDerivAt
  have hcomp := houter.comp z.1 hinner
  have hfd : fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1 =
      (fderiv ℝ ψ z).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ) := hcomp.fderiv
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec j) = _
  rw [hfd]
  change (fderiv ℝ ψ z) (basisVec j, 0) =
    (fderiv ℝ ψ z) (basisVec j, 0)
  rfl

private theorem localEnergy_spatialSecondPartial_eq_dirDeriv
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (z : Vec3 × ℝ) :
    spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i j z =
      dirDeriv (fun y => spatialPartial (show ParabolicPoint → ℝ from ψ) i y)
        (localEnergyLimitSpatialDir j) z := by
  have hpartial : ContDiff ℝ (⊤ : ℕ∞)
      (show Vec3 × ℝ → ℝ from
        fun y => spatialPartial (show ParabolicPoint → ℝ from ψ) i y) := by
    exact CKN.spatialPartial_contDiff hψ i
  change spatialPartial
    (show ParabolicPoint → ℝ from
      (fun y : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from ψ) i y))
    j z = _
  rw [localEnergy_spatialPartial_eq_fderiv_apply
    (ψ := fun y : Vec3 × ℝ => spatialPartial
      (show ParabolicPoint → ℝ from ψ) i y) hpartial j z]
  rfl

/-- The unexpanded local energy density used by the smooth identity. -/
@[expose] def localEnergyLimitBaseIntegrand
    (u : Vec3 × ℝ → Vec3) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p ψ : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ :=
  smoothEnergyBaseIntegrand u R G p ψ

/-- The componentwise expansion of the local energy density. -/
@[expose] def localEnergyLimitExpandedBaseIntegrand
    (u : Vec3 × ℝ → Vec3) (R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ)
    (p : Vec3 × ℝ → ℝ) (ψ : ParabolicPoint → ℝ) : Vec3 × ℝ → ℝ := fun z =>
  -(∑ i : Fin 3, u z i * u z i) *
      (timePartial ψ (parabolicHomeomorph.symm z) +
        ∑ i : Fin 3, spatialSecondPartial ψ i i (parabolicHomeomorph.symm z))
    - ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z i * u z j * spatialPartial ψ j (parabolicHomeomorph.symm z)
    - ∑ i : Fin 3, p z * u z i *
        (2 * spatialPartial ψ i (parabolicHomeomorph.symm z))
    - ∑ i : Fin 3, ∑ j : Fin 3,
        R z i j * (2 *
          (u z i * spatialPartial ψ j (parabolicHomeomorph.symm z) +
            ψ (parabolicHomeomorph.symm z) * G z i j))
    + ∑ i : Fin 3, ∑ j : Fin 3,
        G z i j * G z i j * (2 * ψ (parabolicHomeomorph.symm z))

/-- The smooth local energy density agrees pointwise with its componentwise expansion. -/
theorem localEnergy_smoothBase_eq_expanded
    {u : Vec3 × ℝ → Vec3} {R G : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ}
    {p ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    localEnergyLimitBaseIntegrand u R G p ψ =
      localEnergyLimitExpandedBaseIntegrand u R G p
        (show ParabolicPoint → ℝ from ψ) := by
  funext z
  have htime : timePartial (show ParabolicPoint → ℝ from ψ) z =
      dirDeriv ψ localEnergyLimitTimeDir z := by
    simpa [dirDeriv, localEnergyLimitTimeDir, timeDir] using
      (localEnergy_timePartial_eq_fderiv_apply (ψ := ψ) hψ z)
  have hspatial (i : Fin 3) :
      spatialPartial (show ParabolicPoint → ℝ from ψ) i z =
        dirDeriv ψ (localEnergyLimitSpatialDir i) z := by
    simpa [dirDeriv, localEnergyLimitSpatialDir, spatialDir, basisVec] using
      (localEnergy_spatialPartial_eq_fderiv_apply (ψ := ψ) hψ i z)
  have hspatialAll (i : Fin 3) (y : Vec3 × ℝ) :
      spatialPartial (show ParabolicPoint → ℝ from ψ) i y =
        dirDeriv ψ (localEnergyLimitSpatialDir i) y := by
    simpa [dirDeriv, localEnergyLimitSpatialDir, spatialDir, basisVec] using
      (localEnergy_spatialPartial_eq_fderiv_apply (ψ := ψ) hψ i y)
  have hpartial (i : Fin 3) :
      (fun y : Vec3 × ℝ => spatialPartial (show ParabolicPoint → ℝ from ψ) i y) =
        fun y => dirDeriv ψ (localEnergyLimitSpatialDir i) y := by
    funext y
    exact hspatialAll i y
  have hsecond (i : Fin 3) :
      spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z =
        dirDeriv (fun y => dirDeriv ψ (localEnergyLimitSpatialDir i) y)
          (localEnergyLimitSpatialDir i) z := by
    calc
      _ = dirDeriv
          (fun y => spatialPartial (show ParabolicPoint → ℝ from ψ) i y)
          (localEnergyLimitSpatialDir i) z :=
            localEnergy_spatialSecondPartial_eq_dirDeriv hψ i i z
      _ = _ := by rw [hpartial i]
  have hconv :
      (∑ i : Fin 3, u z i * u z i) *
        (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z i * u z j * dirDeriv ψ (spatialDir j) z := by
    calc
      _ = ∑ i : Fin 3, (u z i * u z i) *
          (∑ j : Fin 3, u z j * dirDeriv ψ (spatialDir j) z) := by
            rw [Finset.sum_mul]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          u z i * u z i * u z j * dirDeriv ψ (spatialDir j) z := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
  have hpressureConv :
      (2 * p z) *
        (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) =
      ∑ i : Fin 3, p z * u z i * (2 * dirDeriv ψ (spatialDir i) z) := by
    calc
      _ = ∑ i : Fin 3,
          (2 * p z) * (u z i * dirDeriv ψ (spatialDir i) z) := by
            rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have henergyConv :
      ((∑ j : Fin 3, u z j * u z j) + 2 * p z) *
        (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z i * u z j * dirDeriv ψ (spatialDir j) z) +
        ∑ i : Fin 3, p z * u z i * (2 * dirDeriv ψ (spatialDir i) z) := by
    calc
      _ = (∑ j : Fin 3, u z j * u z j) *
            (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) +
            (2 * p z) *
              (∑ i : Fin 3, u z i * dirDeriv ψ (spatialDir i) z) := by ring
      _ = _ := by
        rw [hconv, hpressureConv]
  have hstressConv :
      2 * (∑ i : Fin 3, ∑ j : Fin 3,
        R z i j * (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        R z i j * (2 *
          (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) := by
    calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          2 * (R z i j *
            (u z i * dirDeriv ψ (spatialDir j) z + ψ z * G z i j)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hgradConv :
      2 * (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j) * ψ z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        G z i j * G z i j * (2 * ψ z) := by
    calc
      _ = (∑ i : Fin 3, ∑ j : Fin 3, G z i j * G z i j) *
          (2 * ψ z) := by ring
      _ = _ := by
        simp_rw [Finset.sum_mul]
  simp only [spatialDir, basisVec] at hconv hpressureConv henergyConv hstressConv
  simp only [localEnergyLimitBaseIntegrand, localEnergyLimitExpandedBaseIntegrand,
    smoothEnergyBaseIntegrand, velocitySq, htime, hspatial, hsecond,
    localEnergyLimitTimeDir, localEnergyLimitSpatialDir, timeDir, spatialDir,
    basisVec, parabolicHomeomorph_symm_apply]
  rw [henergyConv, hstressConv, hgradConv]
  ring

/-- Finite double sums preserve convergence in an `Lᵖ` seminorm for `p ≥ 1`. -/
theorem localEnergy_tendsto_eLpNorm_double_sum_sub
    {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp : 1 ≤ p) [Fintype ι] [Fintype κ]
    {fn : ℕ → ι → κ → α → ℝ} {f : ι → κ → α → ℝ}
    (hconv : ∀ i j, Tendsto
      (fun n => eLpNorm (fun x => fn n i j x - f i j x) p μ) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => (∑ i, ∑ j, fn n i j x) - ∑ i, ∑ j, f i j x) p μ)
      atTop (nhds 0) := by
  have hinner (i : ι) : Tendsto
      (fun n => eLpNorm
        (fun x => (∑ j ∈ Finset.univ, fn n i j x) - ∑ j ∈ Finset.univ, f i j x)
        p μ) atTop (nhds 0) := by
    exact localEnergy_tendsto_eLpNorm_finset_sum_sub hp Finset.univ
      (fun n j x => fn n i j x) (fun j x => f i j x)
      (by intro j hj; exact hconv i j)
  have houter := localEnergy_tendsto_eLpNorm_finset_sum_sub hp Finset.univ
    (fun n i x => ∑ j ∈ Finset.univ, fn n i j x)
    (fun i x => ∑ j ∈ Finset.univ, f i j x)
    (by intro i hi; simpa using hinner i)
  simpa using houter

/-- Multiplication by a fixed `Lᵖ` function preserves the corresponding Hölder convergence. -/
theorem localEnergy_tendsto_eLpNorm_mul_fixed
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hr : 1 ≤ r) {f g : α → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ)
    {fn : ℕ → α → ℝ} (hfn : ∀ n, MemLp (fn n) p μ)
    (hfnLim : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => fn n x * g x - f x * g x) r μ)
      atTop (nhds 0) := by
  have hconst : Tendsto (fun n : ℕ => eLpNorm (fun x => g x - g x) q μ)
      atTop (nhds 0) := by simp
  exact localEnergy_tendsto_eLpNorm_mul_sub hr hf hg hfn (fun _ => hg)
    hfnLim hconst

/-- Constant scalar multiplication preserves convergence in an `Lᵖ` seminorm. -/
theorem localEnergy_tendsto_eLpNorm_const_smul_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    {f : α → ℝ} {fn : ℕ → α → ℝ} (c : ℝ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => fn n x - f x) p μ)
      atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => c * fn n x - c * f x) p μ)
      atTop (nhds 0) := by
  have hscaled : Tendsto (fun n => ‖c‖ₑ *
      eLpNorm (fun x => fn n x - f x) p μ) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv
      (Or.inr (by simp : ‖c‖ₑ ≠ ⊤))
  apply hscaled.congr'
  filter_upwards [] with n
  have heq : (fun x => c * fn n x - c * f x) =
      c • (fun x => fn n x - f x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq, eLpNorm_const_smul]

/-- `L¹` convergence implies convergence of Bochner integrals. -/
theorem localEnergy_integral_tendsto_of_L1
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {f : α → E} {fn : ℕ → α → E}
    (hfn : ∀ n, MemLp (fn n) 1 μ)
    (hconv : Tendsto (fun n => eLpNorm (fn n - f) 1 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (nhds (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_L1' f
    (Filter.Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hfn n)) hconv

/-- A finite double sum of `Lᵖ` functions belongs to `Lᵖ`. -/
theorem localEnergy_memLp_double_sum
    {α ι κ : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    [Fintype ι] [Fintype κ] {f : ι → κ → α → ℝ}
    (hf : ∀ i j, MemLp (f i j) p μ) :
    MemLp (fun x => ∑ i, ∑ j, f i j x) p μ := by
  have hinner (i : ι) : MemLp (fun x => ∑ j ∈ Finset.univ, f i j x) p μ :=
    memLp_finsetSum Finset.univ (by intro j hj; exact hf i j)
  have houter : MemLp (fun x => ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, f i j x)
      p μ := memLp_finsetSum Finset.univ (by intro i hi; exact hinner i)
  simpa using houter

end ESS
