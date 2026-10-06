/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.ClassicalIBPIntegrability
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ClassicalBridge
public import LeanPool.CIVAxisymmetric.Identities.VorticityEquation
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import LeanPool.CaffarelliKohnNirenberg.Setting.PressureGaugeSlices
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# Changing the pressure and the force by a smooth gauge

A suitable weak solution on the unit cylinder `Q` whose velocity is smooth and divergence
free there stays suitable when the pressure `π` and the force `f` are replaced by smooth
fields `π'` and `f'` with `∇π' - ∇π = f' - f` on `Q`. The weak momentum equation and the local
energy inequality change by the pairings of `π' - π` with `div φ` and with `u · ∇ψ`, which
integration by parts on `Q` turns into the pairings of `f' - f` with `φ` and with `u ψ`. This
is the form in which the averaged system of the proof of `thm:main` is shown to be suitable.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- Integration by parts in one spatial direction against a test function supported in `Q`,
for a field smooth on `Q` whose partial derivative is identified there with a continuous
field `k`. -/
theorem integral_mul_spatialPartial_eq_neg {h k ψ : Vec3 × ℝ → ℝ} (i : Fin 3)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h unitCylinder)
    (hk : ContinuousOn k unitCylinder)
    (hhk : ∀ z ∈ unitCylinder, spatialPartial h i z = k z)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball 0 1) (Ioo (-1) 0)) :
    Integrable (fun z => h z * spatialPartial ψ i z) ∧ Integrable (fun z => k z * ψ z) ∧
      ∫ z, h z * spatialPartial ψ i z = - ∫ z, k z * ψ z := by
  have : (volume : Measure (Vec3 × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨hψs, hψc, hψsupp⟩ := hψ
  have hsub : tsupport ψ ⊆ (unitCylinder : Set (Vec3 × ℝ)) := hψsupp
  have hK : IsCompact (tsupport ψ) := hψc
  have hψeq : ∀ z : Vec3 × ℝ, spatialPartial ψ i z = fderiv ℝ ψ z (basisVec i, 0) := fun z =>
    spatialPartial_eq_jointFDeriv ((hψs.differentiable (by simp)).differentiableAt) i
  have hkeq : ∀ z : Vec3 × ℝ, fderiv ℝ h z (basisVec i, 0) * ψ z = k z * ψ z := by
    intro z
    by_cases hz : z ∈ (unitCylinder : Set (Vec3 × ℝ))
    · rw [← hhk z hz, spatialPartial_eq_jointFDeriv
        ((hh.differentiableOn (by simp) z hz).differentiableAt
          (isOpen_unitCylinder_prod.mem_nhds hz)) i]
    · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun hm => hz (hsub hm)
      rw [h0, mul_zero, mul_zero]
  have hint1 : Integrable (fun z => h z * fderiv ℝ ψ z (basisVec i, 0)) :=
    integrable_mul_fderiv_of_continuousOn hK hsub hh.continuousOn hψs hψc subset_rfl
  have hint2 : Integrable (fun z => k z * ψ z) :=
    integrableOn_mul_of_continuousOn_of_tsupport_subset hK hsub hk hψs.continuous subset_rfl
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_continuousOn (μ := volume)
    (v := ((basisVec i, 0) : Vec3 × ℝ)) isOpen_unitCylinder_prod hK hsub hh hψs hψc subset_rfl
  have e1 : ∫ z, h z * spatialPartial ψ i z = ∫ z, h z * fderiv ℝ ψ z (basisVec i, 0) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => congrArg (h z * ·) (hψeq z))
  have e2 : ∫ z, fderiv ℝ h z (basisVec i, 0) * ψ z = ∫ z, k z * ψ z :=
    integral_congr_ae (Filter.Eventually.of_forall hkeq)
  refine ⟨hint1.congr (Filter.Eventually.of_forall fun z =>
    (congrArg (h z * ·) (hψeq z)).symm), hint2, ?_⟩
  rw [e1, hibp, e2]

/-- The spatial partial derivative of a difference of smooth fields on `Q`. -/
theorem spatialPartial_sub_of_mem_unitCylinder {a b : ParabolicPoint → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => a z) unitCylinder)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => b z) unitCylinder)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) (i : Fin 3) :
    spatialPartial (fun w => a w - b w) i z = spatialPartial a i z - spatialPartial b i z := by
  have hda : DifferentiableAt ℝ (fun w : Vec3 × ℝ => a w) z :=
    (ha.differentiableOn (by simp) z hz).differentiableAt (isOpen_unitCylinder_prod.mem_nhds hz)
  have hdb : DifferentiableAt ℝ (fun w : Vec3 × ℝ => b w) z :=
    (hb.differentiableOn (by simp) z hz).differentiableAt (isOpen_unitCylinder_prod.mem_nhds hz)
  have hd : DifferentiableAt ℝ (fun w : Vec3 × ℝ => a w - b w) z := hda.sub hdb
  refine (spatialPartial_eq_jointFDeriv hd i).trans ?_
  rw [spatialPartial_eq_jointFDeriv hda i,
    spatialPartial_eq_jointFDeriv hdb i]
  have hF := congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L (basisVec i, 0))
    (hda.hasFDerivAt.sub hdb.hasFDerivAt).fderiv
  exact hF

/-- A field continuous on `Q` lies in every `L^r` on a local box of `Q`. -/
theorem memLp_of_continuousOn_localBox {β : Type*} [NormedAddCommGroup β]
    {v : ParabolicPoint → β} (hv : ContinuousOn (fun z : Vec3 × ℝ => v z) unitCylinder)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox (vec3Ball 0 1) (Ioo (-1) 0) Ω' J)
    (r : ℝ≥0∞) :
    MemLp v r (volume.restrict (spaceTimeSet Ω' J)) := by
  obtain ⟨_, hΩc, hΩsub, _, hJc, hJsub⟩ := hbox
  set K : Set (Vec3 × ℝ) := closure Ω' ×ˢ closure J with hKdef
  have hKc : IsCompact K := hΩc.prod hJc
  have hKsub : K ⊆ (unitCylinder : Set (Vec3 × ℝ)) := prod_mono hΩsub hJsub
  have hKm : MeasurableSet (K : Set ParabolicPoint) := hKc.isClosed.measurableSet
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hv.mono hKsub)
  have hKfin : (volume : Measure ParabolicPoint) K < ⊤ :=
    hKc.measure_lt_top (μ := (volume : Measure (Vec3 × ℝ)))
  have : IsFiniteMeasure ((volume : Measure ParabolicPoint).restrict K) :=
    isFiniteMeasure_restrict.2 hKfin.ne
  have hmeas : AEStronglyMeasurable v ((volume : Measure ParabolicPoint).restrict K) :=
    (hv.mono hKsub).aestronglyMeasurable hKm
  have hmem : MemLp v r ((volume : Measure ParabolicPoint).restrict K) := by
    refine MemLp.of_bound hmeas C ?_
    exact (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun z hz => hC z hz)
  have hsubK : (spaceTimeSet Ω' J : Set ParabolicPoint) ⊆ K :=
    prod_mono subset_closure subset_closure
  exact hmem.mono_measure (Measure.restrict_mono hsubK le_rfl)

/-- A component of a vector test function supported in `Q` is a scalar test function
supported in `Q`. -/
theorem component_mem_spaceTimeTestFunction {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball 0 1) (Ioo (-1) 0)) (i : Fin 3) :
    (fun w => φ w i) ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball 0 1) (Ioo (-1) 0) := by
  obtain ⟨hs, hc, hsupp⟩ := hφ
  refine ⟨contDiff_pi.1 hs i, hc.comp_left (g := fun v : Vec3 => v i) rfl, ?_⟩
  refine (tsupport_component_subset (ι := Fin 3) φ i ?_).trans hsupp
  intro z hz
  rw [hz]
  rfl

/-- The momentum pairing of a smooth gauge: if `∇π' - ∇π = f' - f` on `Q`, the pairing
`∫ (π' - π) div φ + (f' - f) · φ` vanishes for every test field `φ` supported in `Q`. -/
theorem integral_pressureGauge_momentum_eq_zero {p p' : ParabolicPoint → ℝ}
    {f f' : ParabolicPoint → Vec3}
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hp' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p' z) unitCylinder)
    (hf' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f' z) unitCylinder)
    (hgrad : ∀ z ∈ unitCylinder, ∀ i : Fin 3,
      spatialPartial p' i z - spatialPartial p i z = f' z i - f z i)
    {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball 0 1) (Ioo (-1) 0)) :
    Integrable (fun z : Vec3 × ℝ => (p' z - p z) * ∑ i, spatialPartial (fun w => φ w i) i z +
        ∑ i, (f' z i - f z i) * φ z i) ∧
      ∫ z : Vec3 × ℝ, ((p' z - p z) * ∑ i, spatialPartial (fun w => φ w i) i z +
        ∑ i, (f' z i - f z i) * φ z i) = 0 := by
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p' z - p z) unitCylinder := hp'.sub hp
  have hibp : ∀ i : Fin 3, _ := fun i =>
    integral_mul_spatialPartial_eq_neg (h := fun z : Vec3 × ℝ => p' z - p z)
      (k := fun z : Vec3 × ℝ => f' z i - f z i) i hg
      (((contDiffOn_pi.1 hf') i).continuousOn.sub ((contDiffOn_pi.1 hf) i).continuousOn)
      (fun z hz => (spatialPartial_sub_of_mem_unitCylinder hp' hp hz i).trans (hgrad z hz i))
      (component_mem_spaceTimeTestFunction hφ i)
  have hpt : (fun z : Vec3 × ℝ => (p' z - p z) * ∑ i, spatialPartial (fun w => φ w i) i z +
      ∑ i, (f' z i - f z i) * φ z i) = fun z => ∑ i, ((p' z - p z) *
        spatialPartial (fun w => φ w i) i z + (f' z i - f z i) * φ z i) := by
    funext z
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z : Vec3 × ℝ =>
      (p' z - p z) * spatialPartial (fun w => φ w i) i z + (f' z i - f z i) * φ z i) :=
    fun i _ => (hibp i).1.add (hibp i).2.1
  have hsum := integral_finsetSum (μ := (volume : Measure (Vec3 × ℝ))) Finset.univ hint
  have hzero : ∑ i, ∫ z : Vec3 × ℝ, ((p' z - p z) * spatialPartial (fun w => φ w i) i z +
      (f' z i - f z i) * φ z i) = 0 :=
    Finset.sum_eq_zero fun i _ => (integral_add (hibp i).1 (hibp i).2.1).trans (by
      rw [(hibp i).2.2, neg_add_cancel])
  refine ⟨(integrable_finsetSum _ hint).congr
    (Filter.Eventually.of_forall fun z => (congrFun hpt z).symm), ?_⟩
  exact (integral_congr_ae (Filter.Eventually.of_forall fun z => congrFun hpt z)).trans
    (hsum.trans hzero)

/-- The energy pairing of a smooth gauge: if `∇π' - ∇π = f' - f` on `Q` and `u` is smooth and
divergence free there, the pairing `∫ (π' - π) u · ∇ψ + ((f' - f) · u) ψ` vanishes for every
test function `ψ` supported in `Q`. -/
theorem integral_pressureGauge_energy_eq_zero {u : ParabolicPoint → Vec3}
    {p p' : ParabolicPoint → ℝ} {f f' : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hp' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p' z) unitCylinder)
    (hf' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f' z) unitCylinder)
    (hdiv : ∀ z ∈ unitCylinder, ∑ j, spatialPartial (fun w => u w j) j z = 0)
    (hgrad : ∀ z ∈ unitCylinder, ∀ i : Fin 3,
      spatialPartial p' i z - spatialPartial p i z = f' z i - f z i)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball 0 1) (Ioo (-1) 0)) :
    Integrable (fun z : Vec3 × ℝ => (p' z - p z) * ∑ i, u z i * spatialPartial ψ i z +
        (∑ i, (f' z i - f z i) * u z i) * ψ z) ∧
      ∫ z : Vec3 × ℝ, ((p' z - p z) * ∑ i, u z i * spatialPartial ψ i z +
        (∑ i, (f' z i - f z i) * u z i) * ψ z) = 0 := by
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p' z - p z) unitCylinder := hp'.sub hp
  have hui : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z i) unitCylinder :=
    fun i => contDiffOn_pi.1 hu i
  have hfi : ∀ i : Fin 3, ContinuousOn (fun z : Vec3 × ℝ => f' z i - f z i) unitCylinder :=
    fun i => ((contDiffOn_pi.1 hf') i).continuousOn.sub ((contDiffOn_pi.1 hf) i).continuousOn
  have hibp : ∀ i : Fin 3, _ := fun i =>
    integral_mul_spatialPartial_eq_neg (h := fun z : Vec3 × ℝ => (p' z - p z) * u z i)
      (k := fun z : Vec3 × ℝ => (f' z i - f z i) * u z i +
        (p' z - p z) * spatialPartial (fun w => u w i) i z) i (hg.mul (hui i))
      (((hfi i).mul (hui i).continuousOn).add
        (hg.continuousOn.mul (contDiffOn_spatialPartial (hui i) i).continuousOn))
      (fun z hz => (spatialPartial_mul_of_mem_unitCylinder (a := fun w => p' w - p w)
          (b := fun w => u w i) hg (hui i) hz i).trans (by
            rw [spatialPartial_sub_of_mem_unitCylinder hp' hp hz i, hgrad z hz i]))
      hψ
  have hWc : ContinuousOn (fun z : Vec3 × ℝ => ∑ i, (f' z i - f z i) * u z i) unitCylinder :=
    continuousOn_finsetSum _ fun i _ => (hfi i).mul (hui i).continuousOn
  have : (volume : Measure (Vec3 × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨hψs, hψc, hψsupp⟩ := hψ
  have hsub : tsupport ψ ⊆ (unitCylinder : Set (Vec3 × ℝ)) := hψsupp
  have hWint : Integrable (fun z : Vec3 × ℝ => (∑ i, (f' z i - f z i) * u z i) * ψ z) :=
    integrableOn_mul_of_continuousOn_of_tsupport_subset (μ := volume) hψc hsub hWc
      hψs.continuous subset_rfl
  have hint1 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z : Vec3 × ℝ =>
      (p' z - p z) * u z i * spatialPartial ψ i z) := fun i _ => (hibp i).1
  have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun z : Vec3 × ℝ =>
      ((f' z i - f z i) * u z i + (p' z - p z) * spatialPartial (fun w => u w i) i z) *
        ψ z) := fun i _ => (hibp i).2.1
  have hpt : (fun z : Vec3 × ℝ => (p' z - p z) * ∑ i, u z i * spatialPartial ψ i z) =
      fun z => ∑ i, (p' z - p z) * u z i * spatialPartial ψ i z := by
    funext z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hS1 : Integrable (fun z : Vec3 × ℝ => (p' z - p z) * ∑ i, u z i * spatialPartial ψ i z) :=
    (integrable_finsetSum _ hint1).congr
      (Filter.Eventually.of_forall fun z => (congrFun hpt z).symm)
  have hsumk : ∫ z : Vec3 × ℝ, ∑ i, ((f' z i - f z i) * u z i +
      (p' z - p z) * spatialPartial (fun w => u w i) i z) * ψ z =
      ∫ z : Vec3 × ℝ, (∑ i, (f' z i - f z i) * u z i) * ψ z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ (unitCylinder : Set (Vec3 × ℝ))
    · have hd := hdiv z hz
      simp only
      rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hd, mul_zero, add_zero]
    · have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun hm => hz (hsub hm)
      simp only [h0, mul_zero, Finset.sum_const_zero]
  have hA : ∫ z : Vec3 × ℝ, (p' z - p z) * ∑ i, u z i * spatialPartial ψ i z =
      - ∫ z : Vec3 × ℝ, (∑ i, (f' z i - f z i) * u z i) * ψ z := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun z => congrFun hpt z)).trans ?_
    refine (integral_finsetSum (μ := (volume : Measure (Vec3 × ℝ))) Finset.univ hint1).trans ?_
    refine (Finset.sum_congr rfl fun i _ => (hibp i).2.2).trans ?_
    rw [Finset.sum_neg_distrib, ← hsumk]
    congr 1
    exact (integral_finsetSum (μ := (volume : Measure (Vec3 × ℝ))) Finset.univ hint2).symm
  refine ⟨hS1.add hWint, ?_⟩
  refine (integral_add hS1 hWint).trans ?_
  rw [hA, neg_add_cancel]

/-- Changing the pressure and the force of a suitable weak solution on `Q` by a smooth gauge:
if the velocity, pressure and force are smooth on `Q`, the velocity is divergence free there,
and the smooth fields `π'`, `f'` satisfy `∇π' - ∇π = f' - f` on `Q`, then `(u, π')` is a
suitable weak solution with the force `f'`. This is the form of the CKN library class
`CKN.IsSuitableWeakSolutionIntegrable`. -/
theorem isSuitableWeakSolutionIntegrable_of_pressureGauge {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p p' : ParabolicPoint → ℝ}
    {f f' : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hp' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p' z) unitCylinder)
    (hf' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f' z) unitCylinder)
    (hdiv : ∀ z ∈ unitCylinder, ∑ j, spatialPartial (fun w => u w j) j z = 0)
    (hgrad : ∀ z ∈ unitCylinder, ∀ i : Fin 3,
      spatialPartial p' i z - spatialPartial p i z = f' z i - f z i) :
    IsSuitableWeakSolutionIntegrable (vec3Ball 0 1) (Ioo (-1) 0) q u Du p' f' := by
  obtain ⟨hΩ, hI, hIord, hq, _, hmeas, hS2, hmom, hen⟩ := hsol
  have hcyl : spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) = (unitCylinder : Set ParabolicPoint) :=
    rfl
  refine ⟨hΩ, hI, hIord, hq, ?_, ?_, hS2, ?_, ?_⟩
  · intro Ω' J hbox i
    exact memLp_of_continuousOn_localBox ((contDiffOn_pi.1 hf') i).continuousOn hbox _
  · intro Ω' J hbox
    obtain ⟨h1, h2, _, _, h5, h6, _, _, h9⟩ := hmeas Ω' J hbox
    have hP := memLp_of_continuousOn_localBox hp'.continuousOn hbox (ENNReal.ofReal (3 / 2))
    have hF := memLp_of_continuousOn_localBox hf'.continuousOn hbox (ENNReal.ofReal q)
    exact ⟨h1, h2, hP.aestronglyMeasurable, hF.aestronglyMeasurable, h5, h6, hP, hF, h9⟩
  · -- the momentum equation
    intro φ hφ
    obtain ⟨hOldInt, hOldZero⟩ := hmom φ hφ
    obtain ⟨hXint, hXzero⟩ := integral_pressureGauge_momentum_eq_zero hp hf hp' hf' hgrad hφ
    have hcompsupp : ∀ i : Fin 3, tsupport (fun w => φ w i) ⊆ tsupport φ := fun i =>
      tsupport_component_subset (ι := Fin 3) φ i (fun z hz => by rw [hz]; rfl)
    have hoff : ∀ z : Vec3 × ℝ, z ∉ tsupport φ →
        (∀ i : Fin 3, timePartial (fun w => φ w i) z = 0) ∧
        (∀ i j : Fin 3, spatialPartial (fun w => φ w i) j z = 0) ∧ (∀ i : Fin 3, φ z i = 0) := by
      intro z hz
      refine ⟨fun i => timePartial_eq_zero_off_tsupport (ψ := fun w : Vec3 × ℝ => φ w i)
          (fun hm => hz (hcompsupp i hm)),
        fun i j => spatialPartial_eq_zero_off_tsupport (ψ := fun w : Vec3 × ℝ => φ w i)
          (fun hm => hz (hcompsupp i hm)) j,
        fun i => image_eq_zero_of_notMem_tsupport (f := fun w => φ w i)
          fun hm => hz (hcompsupp i hm)⟩
    have hOldSupp : Function.support
        (fun z => -∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i) ⊆ tsupport φ := by
      intro z hz
      by_contra hcon
      rw [tsupport_parabolic_eq] at hcon
      obtain ⟨h1, h2, h3⟩ := hoff z hcon
      exact hz (by simp [h1, h2, h3])
    have hOldFull := (integrableOn_iff_integrable_of_support_subset hOldSupp).mp hOldInt
    have hpt : ∀ z : Vec3 × ℝ,
        (-∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - p' z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f' z i * φ z i)
          = (-∑ i, u z i * timePartial (fun w => φ w i) z
            - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i, spatialPartial (fun w => φ w i) i z
            - ∑ i, f z i * φ z i)
              - ((p' z - p z) * ∑ i, spatialPartial (fun w => φ w i) i z +
                ∑ i, (f' z i - f z i) * φ z i) := by
      intro z
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have hXoff : ∀ z : Vec3 × ℝ, z ∉ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) →
        ((p' z - p z) * ∑ i, spatialPartial (fun w => φ w i) i z +
          ∑ i, (f' z i - f z i) * φ z i) = 0 := by
      intro z hz
      obtain ⟨_, h2, h3⟩ := hoff z (fun hm => hz (hφ.2.2 hm))
      simp [h2, h3]
    refine ⟨(hOldInt.sub hXint.integrableOn).congr
      (Filter.Eventually.of_forall fun z => (hpt z).symm), ?_⟩
    calc _ = ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
            ((-∑ i, u z i * timePartial (fun w => φ w i) z
              - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
              + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
              - p z * ∑ i, spatialPartial (fun w => φ w i) i z
              - ∑ i, f z i * φ z i)
              - ((p' z - p z) * ∑ i, spatialPartial (fun w => φ w i) i z +
                ∑ i, (f' z i - f z i) * φ z i)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = _ := integral_sub hOldFull.integrableOn hXint.integrableOn
      _ = 0 := by
          have e := (setIntegral_eq_integral_of_forall_compl_eq_zero hXoff).trans hXzero
          rw [hOldZero]
          exact (congrArg (fun x : ℝ => 0 - x) e).trans (sub_zero 0)
  · -- the local energy inequality
    intro ψ hψ hψnn
    obtain ⟨hGradInt, hOldInt, hOldIneq⟩ := hen ψ hψ hψnn
    obtain ⟨hYint, hYzero⟩ :=
      integral_pressureGauge_energy_eq_zero hu hp hf hp' hf' hdiv hgrad hψ
    have hOldSupp : Function.support
        (fun z => vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f z i * u z i) * ψ z) ⊆ tsupport ψ := by
      intro z hz
      by_contra hcon
      rw [tsupport_parabolic_eq] at hcon
      have h1 : timePartial ψ z = 0 := timePartial_eq_zero_off_tsupport hcon
      have h2 : ∀ i : Fin 3, spatialSecondPartial ψ i i z = 0 := fun i =>
        spatialPartial_eq_zero_off_tsupport
          (fun hm => hcon (CKN.tsupport_spatialPartial_subset i hm)) i
      have h3 : ∀ i : Fin 3, spatialPartial ψ i z = 0 := fun i =>
        spatialPartial_eq_zero_off_tsupport hcon i
      have h4 : ψ z = 0 := image_eq_zero_of_notMem_tsupport (f := (ψ : Vec3 × ℝ → ℝ)) hcon
      exact hz (by simp [h1, h2, h3, h4])
    have hOldFull := (integrableOn_iff_integrable_of_support_subset hOldSupp).mp hOldInt
    have hpt : ∀ z : Vec3 × ℝ,
        (vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p' z) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f' z i * u z i) * ψ z)
          = (vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + (2 * ∑ i, f z i * u z i) * ψ z)
              + 2 * ((p' z - p z) * ∑ i, u z i * spatialPartial ψ i z +
                (∑ i, (f' z i - f z i) * u z i) * ψ z) := by
      intro z
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    have hYoff : ∀ z : Vec3 × ℝ, z ∉ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) →
        2 * ((p' z - p z) * ∑ i, u z i * spatialPartial ψ i z +
          (∑ i, (f' z i - f z i) * u z i) * ψ z) = 0 := by
      intro z hz
      have hz' : z ∉ tsupport ψ := fun hm => hz (hψ.2.2 hm)
      have h3 : ∀ i : Fin 3, spatialPartial ψ i z = 0 := fun i =>
        spatialPartial_eq_zero_off_tsupport hz' i
      have h4 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hz'
      simp [h3, h4]
    have h2Y := hYint.const_mul (2 : ℝ)
    refine ⟨hGradInt, (hOldInt.add h2Y.integrableOn).congr
      (Filter.Eventually.of_forall fun z => (hpt z).symm), ?_⟩
    have hsplit : ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
          (vec3EuclideanNorm (u z) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + (vec3EuclideanNorm (u z) ^ 2 + 2 * p' z) *
                  ∑ i, u z i * spatialPartial ψ i z
              + (2 * ∑ i, f' z i * u z i) * ψ z)
        = ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
          (vec3EuclideanNorm (u z) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                  ∑ i, u z i * spatialPartial ψ i z
              + (2 * ∑ i, f z i * u z i) * ψ z) := by
      calc _ = ∫ z in spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0),
            ((vec3EuclideanNorm (u z) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                  ∑ i, u z i * spatialPartial ψ i z
              + (2 * ∑ i, f z i * u z i) * ψ z)
              + 2 * ((p' z - p z) * ∑ i, u z i * spatialPartial ψ i z +
                (∑ i, (f' z i - f z i) * u z i) * ψ z)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = _ := integral_add hOldFull.integrableOn h2Y.integrableOn
        _ = _ := by
            have e := (setIntegral_eq_integral_of_forall_compl_eq_zero hYoff).trans
              (by rw [integral_const_mul, hYzero, mul_zero])
            exact (congrArg (fun x : ℝ => _ + x) e).trans (add_zero _)
    rw [hsplit]
    exact hOldIneq

/-- Changing the pressure and the force of a suitable weak solution on `Q` by a smooth gauge:
if the velocity, pressure and force are smooth on `Q`, the velocity is divergence free there,
and the smooth fields `π'`, `f'` satisfy `∇π' - ∇π = f' - f` on `Q`, then `(u, π')` is a
suitable weak solution with the force `f'`. -/
theorem isSuitableWeakSolution_of_pressureGauge {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p p' : ParabolicPoint → ℝ}
    {f f' : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hp' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p' z) unitCylinder)
    (hf' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f' z) unitCylinder)
    (hdiv : ∀ z ∈ unitCylinder, ∑ j, spatialPartial (fun w => u w j) j z = 0)
    (hgrad : ∀ z ∈ unitCylinder, ∀ i : Fin 3,
      spatialPartial p' i z - spatialPartial p i z = f' z i - f z i) :
    IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p' f' :=
  isSuitableWeakSolution_of_integrable
    (isSuitableWeakSolutionIntegrable_of_pressureGauge
      (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) hu hp hf hp' hf' hdiv hgrad)

end CIV
