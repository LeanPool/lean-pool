/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.WeakToClassicalCore
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.WeakGradientPairing
public import LeanPool.CIVAxisymmetric.Prerequisites.Vorticity.ScalarTestFunctionLift

/-!
# A suitable weak solution that is smooth on the unit cylinder is a classical solution

Testing the weak momentum equation with `ψ eₖ` isolates its `k`-th component; integrating by
parts back (in time, in space, and twice for the viscous term through the weak-gradient pairing
identity) shows that the classical momentum residual integrates to zero against every test
function supported in the cylinder, so it vanishes there. Together with the pointwise divergence
equation this gives `IsClassicalSolutionOn u p f unitCylinder`, the passage from the weak to the
classical equations used in the proof of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- Testing with `ψ eₖ` collapses the weak momentum integrand to its `k`-th component. -/
theorem momentum_integrand_basisVec {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (ψ : Vec3 × ℝ → ℝ) (k : Fin 3) (z : ParabolicPoint) :
    (-(∑ i, u z i * timePartial (fun w => (fun z' => ψ z' • basisVec k) w i) z))
        - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => (fun z' => ψ z' • basisVec k) w i) j z
        + ∑ i, ∑ j, (Du z i j) * spatialPartial (fun w => (fun z' => ψ z' • basisVec k) w i) j z
        - p z * ∑ i, spatialPartial (fun w => (fun z' => ψ z' • basisVec k) w i) i z
        - ∑ i, f z i * (fun z' => ψ z' • basisVec k) z i =
      -(u z k * timePartial ψ z) - ∑ j, u z k * u z j * spatialPartial ψ j z
        + ∑ j, Du z k j * spatialPartial ψ j z - p z * spatialPartial ψ k z - f z k * ψ z := by
  fin_cases k <;> simp [Fin.sum_univ_three, basisVec_apply, spatialPartial, timePartial]

/-- A function continuous on the unit cylinder times a spatial partial of a test function
supported in the cylinder is integrable. -/
theorem integrable_mul_spatialPartial_of_test {g : ParabolicPoint → ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hg : ContinuousOn (fun z : Vec3 × ℝ => g z) unitCylinder) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ unitCylinder) (j : Fin 3) :
    Integrable (fun z : Vec3 × ℝ => g z * spatialPartial ψ j z) := by
  have h := integrable_mul_spatialPartial_test hg hψ hψc hsupp ((basisVec j : Vec3), (0 : ℝ))
  refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [spatialPartial_test_eq_fderiv hψ j z]

/-- A function continuous on the unit cylinder times the time partial of a test function
supported in the cylinder is integrable. -/
theorem integrable_mul_timePartial_of_test {g : ParabolicPoint → ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hg : ContinuousOn (fun z : Vec3 × ℝ => g z) unitCylinder) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ unitCylinder) :
    Integrable (fun z : Vec3 × ℝ => g z * timePartial ψ z) := by
  have h := integrable_mul_spatialPartial_test hg hψ hψc hsupp ((0 : Vec3), (1 : ℝ))
  refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [timePartial_test_eq_fderiv hψ z]

/-- A function continuous on the unit cylinder times a test function supported in the
cylinder is integrable. -/
theorem integrable_mul_of_test {g : ParabolicPoint → ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hg : ContinuousOn (fun z : Vec3 × ℝ => g z) unitCylinder) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ unitCylinder) :
    Integrable (fun z : Vec3 × ℝ => g z * ψ z) :=
  integrable_mul_of_continuousOn_of_tsupport_subset_prod hg hψ.continuous hψc hsupp

/-- The product rule for a spatial partial at a point of the unit cylinder. -/
theorem spatialPartial_mul_of_mem_unitCylinder {a b : ParabolicPoint → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => a z) unitCylinder)
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => b z) unitCylinder)
    {z : Vec3 × ℝ} (hz : z ∈ unitCylinder) (j : Fin 3) :
    spatialPartial (fun w => a w * b w) j z =
      spatialPartial a j z * b z + a z * spatialPartial b j z := by
  have hnhds := isOpen_unitCylinder_prod.mem_nhds hz
  have hda : DifferentiableAt ℝ (fun w : Vec3 × ℝ => a w) z :=
    (ha.contDiffAt hnhds).differentiableAt (by simp)
  have hdb : DifferentiableAt ℝ (fun w : Vec3 × ℝ => b w) z :=
    (hb.contDiffAt hnhds).differentiableAt (by simp)
  have e1 : spatialPartial (fun w => a w * b w) j z =
      fderiv ℝ (fun w : Vec3 × ℝ => a w * b w) z ((basisVec j : Vec3), (0 : ℝ)) :=
    spatialPartial_eq_jointFDeriv (g := fun w => a w * b w) (hda.mul hdb) j
  have e2 := spatialPartial_eq_jointFDeriv (g := a) hda j
  have e3 := spatialPartial_eq_jointFDeriv (g := b) hdb j
  have e5 : fderiv ℝ (fun w : Vec3 × ℝ => a w * b w) z ((basisVec j : Vec3), (0 : ℝ)) =
      a z * fderiv ℝ (fun w : Vec3 × ℝ => b w) z ((basisVec j : Vec3), (0 : ℝ)) +
        b z * fderiv ℝ (fun w : Vec3 × ℝ => a w) z ((basisVec j : Vec3), (0 : ℝ)) := by
    have h := congrArg (fun L : (Vec3 × ℝ) →L[ℝ] ℝ => L ((basisVec j : Vec3), (0 : ℝ)))
      (fderiv_mul hda hdb)
    exact h.trans (by simp only [add_apply, smul_apply,
      smul_eq_mul])
  linear_combination e1 + e5 - b z * e2 - a z * e3

/-- The convective term: `∫ u_k u_j ∂ⱼψ = -∫ (∂ⱼu_k u_j + u_k ∂ⱼu_j) ψ`. -/
theorem integral_convective_pairing {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ unitCylinder) (k j : Fin 3) :
    ∫ z : Vec3 × ℝ, u z k * u z j * spatialPartial ψ j z =
      -∫ z : Vec3 × ℝ, (spatialPartial (fun w => u w k) j z * u z j +
        u z k * spatialPartial (fun w => u w j) j z) * ψ z := by
  have hcomp : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z i) unitCylinder :=
    fun i => (contDiffOn_pi.mp hu) i
  have h := integral_mul_spatialPartial_eq_neg_of_contDiffOn (h := fun w => u w k * u w j)
    (ψ := ψ) ((hcomp k).mul (hcomp j)) hψ hψc hsupp j
  refine h.trans ?_
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  by_cases hz : z ∈ unitCylinder
  · change spatialPartial (fun w => u w k * u w j) j z * ψ z = _
    rw [spatialPartial_mul_of_mem_unitCylinder (hcomp k) (hcomp j) hz j]
    rfl
  · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hz (hsupp h'))
    change spatialPartial (fun w => u w k * u w j) j z * ψ z = _
    beta_reduce
    rw [this, mul_zero, mul_zero]

/-- The viscous term: `∫ Du_{kj} ∂ⱼψ = -∫ ∂ⱼ∂ⱼu_k ψ`. -/
theorem integral_viscous_pairing {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ unitCylinder) (k j : Fin 3) :
    ∫ z : Vec3 × ℝ, Du z k j * spatialPartial ψ j z =
      -∫ z : Vec3 × ℝ, spatialSecondPartial (fun w => u w k) j j z * ψ z := by
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z k) unitCylinder :=
    (contDiffOn_pi.mp hu) k
  set ψ' : Vec3 × ℝ → ℝ := fun z => spatialPartial ψ j z with hψ'
  have hψ's : ContDiff ℝ (⊤ : ℕ∞) ψ' := contDiff_spatialPartial_of_contDiff hψ j
  have hψ'c : HasCompactSupport ψ' :=
    HasCompactSupport.intro hψc (fun z hz => spatialPartial_eq_zero_of_notMem_tsupport hz j)
  have hψ'supp : tsupport ψ' ⊆ unitCylinder := by
    refine (closure_minimal (fun z hz => ?_) (isClosed_tsupport ψ)).trans hsupp
    by_contra hzn
    exact hz (spatialPartial_eq_zero_of_notMem_tsupport hzn j)
  have h1 := integral_weakGradient_mul_spatialPartial_eq hsol hψ hψc hsupp k j
  have h2 := integral_mul_spatialPartial_eq_neg_of_contDiffOn (h := fun w => u w k)
    (ψ := ψ') hcomp hψ's hψ'c hψ'supp j
  have h3 := integral_mul_spatialPartial_eq_neg_of_contDiffOn
    (h := fun w => spatialPartial (fun w' => u w' k) j w) (ψ := ψ)
    (contDiffOn_spatialPartial hcomp j) hψ hψc hsupp j
  have e : ∫ z : Vec3 × ℝ, u z k * spatialSecondPartial ψ j j z =
      ∫ z : Vec3 × ℝ, u z k * spatialPartial ψ' j z := rfl
  rw [h1, e, h2, neg_neg]
  exact h3

/-- The time partial of a smooth function vanishes off its topological support. -/
theorem timePartial_test_eq_zero_of_notMem_tsupport {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) : timePartial ψ z = 0 := by
  rw [timePartial_test_eq_fderiv hψ z]
  have : fderiv ℝ ψ z = 0 :=
    Function.notMem_support.mp (fun h' => hz (support_fderiv_subset ℝ h'))
  rw [this, zero_apply]

/-- The weak momentum equation tested with `ψ eₖ`, as a whole-space integral of the collapsed
integrand. -/
theorem integral_momentum_component_eq_zero {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ unitCylinder) (k : Fin 3) :
    ∫ z : Vec3 × ℝ, (-(u z k * timePartial ψ z) - ∑ j, u z k * u z j * spatialPartial ψ j z
        + ∑ j, Du z k j * spatialPartial ψ j z - p z * spatialPartial ψ k z - f z k * ψ z) = 0 := by
  have hφ := smul_basisVec_mem_spaceTimeTestFunction (Ω := vec3Ball 0 1) (I := Ioo (-1) 0)
    ⟨hψ, hψc, hsupp⟩ k
  have hmom := hsol.2.2.2.2.2.2.2.1 _ hφ
  have hmom2 : ∫ z : Vec3 × ℝ in vec3Ball 0 1 ×ˢ Ioo (-1) 0,
      (-(u z k * timePartial ψ z) - ∑ j, u z k * u z j * spatialPartial ψ j z
        + ∑ j, Du z k j * spatialPartial ψ j z - p z * spatialPartial ψ k z - f z k * ψ z) = 0 :=
    (integral_congr_ae (ae_of_all _ (fun z => (momentum_integrand_basisVec (u := u) (Du := Du)
      (p := p) (f := f) ψ k z).symm))).trans hmom
  have hsupp2 : tsupport ψ ⊆ vec3Ball 0 1 ×ˢ Ioo (-1) 0 := hsupp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := vec3Ball 0 1 ×ˢ Ioo (-1) 0)]
  · exact hmom2
  · intro z hz
    have hzt : z ∉ tsupport ψ := fun h => hz (hsupp2 h)
    have h0 : ψ z = 0 := image_eq_zero_of_notMem_tsupport hzt
    have h1 : ∀ j, spatialPartial ψ j z = 0 := fun j =>
      spatialPartial_eq_zero_of_notMem_tsupport hzt j
    have h2 : timePartial ψ z = 0 := timePartial_test_eq_zero_of_notMem_tsupport hψ hzt
    simp only [h0, h1, h2, mul_zero, neg_zero, Finset.sum_const_zero, sub_zero, add_zero]

/-- The classical momentum residual of a suitable weak solution smooth on the unit cylinder
integrates to zero against every test function supported in the cylinder. -/
theorem integral_momentum_residual_mul_eq_zero {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) (k : Fin 3)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ unitCylinder) :
    ∫ z : Vec3 × ℝ, (timePartial (fun w => u w k) z +
        ∑ j, u z j * spatialPartial (fun w => u w k) j z -
        ∑ j, spatialSecondPartial (fun w => u w k) j j z + spatialPartial p k z - f z k) * ψ z =
          0 := by
  have hcomp : ∀ i : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z i) unitCylinder :=
    fun i => (contDiffOn_pi.mp hu) i
  have hfk : ContinuousOn (fun z : Vec3 × ℝ => f z k) unitCylinder :=
    ((contDiffOn_pi.mp hf) k).continuousOn
  have cu : ∀ i, ContinuousOn (fun z : Vec3 × ℝ => u z i) unitCylinder :=
    fun i => (hcomp i).continuousOn
  have cdu : ∀ i j, ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (fun w => u w i) j z)
      unitCylinder := fun i j => (contDiffOn_spatialPartial (hcomp i) j).continuousOn
  have cddu : ∀ i j, ContinuousOn
      (fun z : Vec3 × ℝ => spatialSecondPartial (fun w => u w i) j j z) unitCylinder :=
    fun i j => (contDiffOn_spatialPartial (contDiffOn_spatialPartial (hcomp i) j) j).continuousOn
  have ctu : ContinuousOn (fun z : Vec3 × ℝ => timePartial (fun w => u w k) z) unitCylinder :=
    (contDiffOn_timePartial (hcomp k)).continuousOn
  have cdp : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial p k z) unitCylinder :=
    (contDiffOn_spatialPartial hp k).continuousOn
  -- integrability of the pieces
  have iA := integrable_mul_of_test ctu hψ hψc hsupp
  have iB : ∀ j, Integrable (fun z : Vec3 × ℝ =>
      (spatialPartial (fun w => u w k) j z * u z j) * ψ z) := fun j =>
    integrable_mul_of_test ((cdu k j).mul (cu j)) hψ hψc hsupp
  have iBd : ∀ j, Integrable (fun z : Vec3 × ℝ =>
      (u z k * spatialPartial (fun w => u w j) j z) * ψ z) := fun j =>
    integrable_mul_of_test ((cu k).mul (cdu j j)) hψ hψc hsupp
  have iC : ∀ j, Integrable (fun z : Vec3 × ℝ =>
      spatialSecondPartial (fun w => u w k) j j z * ψ z) := fun j =>
    integrable_mul_of_test (cddu k j) hψ hψc hsupp
  have iP := integrable_mul_of_test cdp hψ hψc hsupp
  have iF := integrable_mul_of_test hfk hψ hψc hsupp
  have iT := integrable_mul_timePartial_of_test (cu k) hψ hψc hsupp
  have iU : ∀ j, Integrable (fun z : Vec3 × ℝ => u z k * u z j * spatialPartial ψ j z) :=
    fun j => integrable_mul_spatialPartial_of_test ((cu k).mul (cu j)) hψ hψc hsupp j
  have iD : ∀ j, Integrable (fun z : Vec3 × ℝ => Du z k j * spatialPartial ψ j z) :=
    fun j => (integrable_and_integral_weakGradient_mul_spatialPartial hsol hψ hψc hsupp k j).1
  have iPk := integrable_mul_spatialPartial_of_test hp.continuousOn hψ hψc hsupp k
  -- the integrations by parts
  have rT := integral_mul_timePartial_eq_neg_of_contDiffOn (h := fun w => u w k) (ψ := ψ)
    (hcomp k) hψ hψc hsupp
  have rU : ∀ j, ∫ z : Vec3 × ℝ, u z k * u z j * spatialPartial ψ j z =
      -((∫ z : Vec3 × ℝ, (spatialPartial (fun w => u w k) j z * u z j) * ψ z) +
        ∫ z : Vec3 × ℝ, (u z k * spatialPartial (fun w => u w j) j z) * ψ z) := by
    intro j
    rw [integral_convective_pairing hu hψ hψc hsupp k j, ← integral_add (iB j) (iBd j)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only
    ring
  have rD : ∀ j, ∫ z : Vec3 × ℝ, Du z k j * spatialPartial ψ j z =
      -∫ z : Vec3 × ℝ, spatialSecondPartial (fun w => u w k) j j z * ψ z := fun j =>
    integral_viscous_pairing hsol hu hψ hψc hsupp k j
  have rP := integral_mul_spatialPartial_eq_neg_of_contDiffOn (h := p) (ψ := ψ) hp hψ hψc hsupp k
  have rBd : ∑ j, ∫ z : Vec3 × ℝ, (u z k * spatialPartial (fun w => u w j) j z) * ψ z = 0 := by
    rw [← integral_finsetSum _ (fun j _ => iBd j)]
    refine (integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))).trans (integral_zero _ _)
    change ∑ j, (u z k * spatialPartial (fun w => u w j) j z) * ψ z = 0
    by_cases hz : z ∈ unitCylinder
    · have hdiv := classical_divergence_free_of_suitable hsol hu z hz
      calc ∑ j, (u z k * spatialPartial (fun w => u w j) j z) * ψ z
          = u z k * (∑ j, spatialPartial (fun w => u w j) j z) * ψ z := by
            rw [Finset.mul_sum, Finset.sum_mul]
        _ = 0 := by rw [hdiv, mul_zero, zero_mul]
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hz (hsupp h'))
      simp [this]
  -- expand the tested identity
  have hN := integral_momentum_component_eq_zero hsol hψ hψc hsupp k
  rw [integral_sub, integral_sub, integral_add, integral_sub, integral_neg,
    integral_finsetSum _ (fun j _ => iU j), integral_finsetSum _ (fun j _ => iD j)] at hN
  rotate_left
  · exact iT.neg
  · exact integrable_finsetSum _ (fun j _ => iU j)
  · exact iT.neg.sub (integrable_finsetSum _ (fun j _ => iU j))
  · exact integrable_finsetSum _ (fun j _ => iD j)
  · exact (iT.neg.sub (integrable_finsetSum _ (fun j _ => iU j))).add
      (integrable_finsetSum _ (fun j _ => iD j))
  · exact iPk
  · exact ((iT.neg.sub (integrable_finsetSum _ (fun j _ => iU j))).add
      (integrable_finsetSum _ (fun j _ => iD j))).sub iPk
  · exact iF
  -- expand the target
  have hT : ∫ z : Vec3 × ℝ, (timePartial (fun w => u w k) z +
        ∑ j, u z j * spatialPartial (fun w => u w k) j z -
        ∑ j, spatialSecondPartial (fun w => u w k) j j z + spatialPartial p k z - f z k) * ψ z =
      ∫ z : Vec3 × ℝ, ((((timePartial (fun w => u w k) z * ψ z +
        ∑ j, (spatialPartial (fun w => u w k) j z * u z j) * ψ z) -
        ∑ j, spatialSecondPartial (fun w => u w k) j j z * ψ z) +
        spatialPartial p k z * ψ z) - f z k * ψ z) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Fin.sum_univ_three]
    ring
  rw [hT, integral_sub, integral_add, integral_sub, integral_add,
    integral_finsetSum _ (fun j _ => iB j), integral_finsetSum _ (fun j _ => iC j)]
  rotate_left
  · exact iA
  · exact integrable_finsetSum _ (fun j _ => iB j)
  · exact iA.add (integrable_finsetSum _ (fun j _ => iB j))
  · exact integrable_finsetSum _ (fun j _ => iC j)
  · exact (iA.add (integrable_finsetSum _ (fun j _ => iB j))).sub
      (integrable_finsetSum _ (fun j _ => iC j))
  · exact iP
  · exact ((iA.add (integrable_finsetSum _ (fun j _ => iB j))).sub
      (integrable_finsetSum _ (fun j _ => iC j))).add iP
  · exact iF
  simp only [rU, rD, Finset.sum_neg_distrib, Finset.sum_add_distrib] at hN
  rw [rT, rP] at hN
  linarith only [hN, rBd]

/-- A suitable weak solution on the unit cylinder whose velocity, pressure and force are smooth
there is a classical solution there. -/
theorem isClassicalSolutionOn_of_suitable {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder) :
    IsClassicalSolutionOn u p f unitCylinder := by
  have hcomp : ∀ j : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z j) unitCylinder :=
    fun j => (contDiffOn_pi.mp hu) j
  have hfcomp : ∀ j : Fin 3, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z j) unitCylinder :=
    fun j => (contDiffOn_pi.mp hf) j
  refine ⟨hu, hp, hf, ?_, classical_divergence_free_of_suitable hsol hu⟩
  intro z hz k
  have hres := eq_zero_on_unitCylinder_of_forall_test
    (F := fun z => timePartial (fun w => u w k) z +
        ∑ j, u z j * spatialPartial (fun w => u w k) j z -
        ∑ j, spatialSecondPartial (fun w => u w k) j j z + spatialPartial p k z - f z k)
    ?_ (fun ψ hψ hψc hsupp => integral_momentum_residual_mul_eq_zero hsol hu hp hf k hψ hψc hsupp)
    z hz
  · exact sub_eq_zero.mp hres
  · have ht : ContinuousOn (fun z : Vec3 × ℝ => timePartial (fun w => u w k) z) unitCylinder :=
      (contDiffOn_timePartial (hcomp k)).continuousOn
    have hs1 : ∀ j, ContinuousOn (fun z : Vec3 × ℝ => spatialPartial (fun w => u w k) j z)
        unitCylinder := fun j => (contDiffOn_spatialPartial (hcomp k) j).continuousOn
    have hs2 : ∀ j, ContinuousOn (fun z : Vec3 × ℝ => spatialSecondPartial (fun w => u w k) j j z)
        unitCylinder := fun j =>
      (contDiffOn_spatialPartial (contDiffOn_spatialPartial (hcomp k) j) j).continuousOn
    have hsp : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial p k z) unitCylinder :=
      (contDiffOn_spatialPartial hp k).continuousOn
    exact ((((ht.add (continuousOn_finsetSum _ (fun j _ =>
      ((hcomp j).continuousOn.mul (hs1 j))))).sub
      (continuousOn_finsetSum _ (fun j _ => hs2 j))).add hsp).sub (hfcomp k).continuousOn)

end CIV
