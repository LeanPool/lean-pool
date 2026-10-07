/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakCalculus
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityWeakEquation
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.LocalBox
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# The starting data of the vorticity bootstrap

For a suitable weak solution on a neighbourhood of the closed unit past cylinder, the velocity,
its gradient, the weak vorticity and the vorticity flux are square integrable on the open unit
box below the top, the gradient is the weak spatial gradient of the velocity there, the velocity
is weakly divergence free, and each vorticity component solves the weak heat equation with a
divergence-form source (`lem:vorticity-weak-eq`, used in `thm:vorticity-regularity`).
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The open unit box below the top of the unit past cylinder lies in that cylinder. -/
theorem vorticityUnitBox_subset_cylinder (x₀ : Vec3) (t₀ : ℝ) :
    (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) ⊆ parabolicCylinder x₀ t₀ 1 := by
  rintro ⟨x, t⟩ ⟨hx, ht1, ht2⟩
  exact ⟨hx, by simpa using ht1, le_of_lt ht2⟩

/-- A local box of a suitable solution containing the closed unit cylinder. -/
theorem vorticity_exists_localBox_of_closure {Ω : Set Vec3} {I : Set ℝ} (hΩ : IsOpen Ω)
    (hI : IsOpen I) (hIord : I.OrdConnected) {x₀ : Vec3} {t₀ : ℝ}
    (hcl : closure (parabolicCylinder x₀ t₀ 1) ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧
      (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) ⊆ spaceTimeSet Ω' J := by
  have hcpt : IsCompact (closure (parabolicCylinder x₀ t₀ 1)) := by
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)]
    have hball : IsCompact {y : Vec3 | vec3EuclideanNorm (y - x₀) ≤ 1} := by
      have hbd : Bornology.IsBounded {y : Vec3 | vec3EuclideanNorm (y - x₀) ≤ 1} := by
        refine (Metric.isBounded_closedBall (x := x₀) (r := 1)).subset ?_
        intro y hy
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact (norm_le_vec3EuclideanNorm _).trans hy
      have hcl' : IsClosed {y : Vec3 | vec3EuclideanNorm (y - x₀) ≤ 1} := by
        refine isClosed_le ?_ continuous_const
        unfold vec3EuclideanNorm
        fun_prop
      exact Metric.isCompact_of_isClosed_isBounded hcl' hbd
    have hprod := hball.prod (isCompact_Icc (a := t₀ - 1 ^ 2) (b := t₀))
    exact (parabolicHomeomorph.isCompact_preimage).2 hprod
  obtain ⟨Ω', J, hbox, hK⟩ :=
    caccioppoli_localBox_of_compact_subset hΩ hI hIord hcpt hcl
  exact ⟨Ω', J, hbox, (vorticityUnitBox_subset_cylinder x₀ t₀).trans
    (subset_closure.trans hK)⟩

/-- Square integrability of the velocity and gradient components on the open unit box. -/
theorem vorticityBase_memLp {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : IsSuitableWeakSolution Ω I q u Du p (fun _ => 0)) (hΩ : IsOpen Ω) (hI : IsOpen I)
    {x₀ : Vec3} {t₀ : ℝ} (hcl : closure (parabolicCylinder x₀ t₀ 1) ⊆ spaceTimeSet Ω I) :
    (∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2
      (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) ∧
    (∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀))) := by
  obtain ⟨Ω', J, hbox, hsub⟩ := vorticity_exists_localBox_of_closure hΩ hI h.2.2.1 hcl
  have hdata := h.2.2.2.2.2.1 Ω' J hbox
  have hLp := CKN.Core.Step3.local_memLp_two_of_energy (u := u) (Du := Du) (hu := hdata.1)
    (hDu := hdata.2.1) hdata.2.2.2.2.2.1
  have hu : MemLp u 2 (volume.restrict (spaceTimeSet Ω' J)) := hLp.1
  have hDu : MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)) := hLp.2
  have hmono : (volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀) ≤
      (volume : Measure ParabolicPoint).restrict (spaceTimeSet Ω' J) :=
    Measure.restrict_mono hsub le_rfl
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · exact ((memLp_pi_iff.mp hu) i).mono_measure hmono
  · exact ((memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j).mono_measure hmono

/-- The bound of the velocity components on the open unit box. -/
theorem vorticityBase_bound {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ M : ℝ}
    (hM : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ 1)),
      vec3EuclideanNorm (u z) ≤ M) :
    ∀ᵐ z ∂((volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀)),
      ∀ i, |u z i| ≤ M := by
  have hmono : (volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀) ≤
      (volume : Measure ParabolicPoint).restrict (parabolicCylinder x₀ t₀ 1) :=
    Measure.restrict_mono (vorticityUnitBox_subset_cylinder x₀ t₀) le_rfl
  filter_upwards [ae_mono hmono hM] with z hz i
  refine le_trans ?_ hz
  have hsq : u z i ^ 2 ≤ ∑ k : Fin 3, u z k ^ 2 :=
    Finset.single_le_sum (f := fun k => u z k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  rw [vec3EuclideanNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-- The gradient energy on the open unit box is controlled by the energy on the cylinder. -/
theorem vorticityBase_energy {Du : ParabolicPoint → Fin 3 → Vec3} {x₀ : Vec3} {t₀ E : ℝ}
    (hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀)))
    (hE : (∫⁻ z in parabolicCylinder x₀ t₀ 1, ‖Du z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2)) :
    ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2 ≤
      9 * E ^ 2 := by
  set W := (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ))
  have hint : ∀ i j, Integrable (fun z : Vec3 × ℝ => Du z i j ^ 2) (volume.restrict W) :=
    fun i j => (memLp_two_iff_integrable_sq (hDu i j).aestronglyMeasurable).1 (hDu i j)
  have hsum : Integrable (fun z : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2)
      (volume.restrict W) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  have hpt : ∀ z : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2 ≤ 9 * ‖Du z‖ ^ 2 := by
    intro z
    have hij : ∀ i j, Du z i j ^ 2 ≤ ‖Du z‖ ^ 2 := by
      intro i j
      have h1 : ‖Du z i j‖ ≤ ‖Du z‖ := (norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm _ i)
      have h2 : |Du z i j| ≤ ‖Du z‖ := by rwa [Real.norm_eq_abs] at h1
      nlinarith only [h2, abs_nonneg (Du z i j), sq_abs (Du z i j)]
    calc
      ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2 ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
      _ = 9 * ‖Du z‖ ^ 2 := by simp; ring
  have hlin : ENNReal.ofReal (∫ z in W, ∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2) ≤
      ENNReal.ofReal (9 * E ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hsum
      (Eventually.of_forall fun z => by positivity)]
    calc
      ∫⁻ z in W, ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, Du z i j ^ 2) ≤
          ∫⁻ z in W, 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have : ‖Du z‖ ^ (2 : ℝ) = ‖Du z‖ ^ (2 : ℕ) := by
          exact_mod_cast Real.rpow_natCast _ 2
        rw [this]
        exact hpt z
      _ = 9 * ∫⁻ z in W, ‖Du z‖ₑ ^ (2 : ℝ) := lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 9 * ∫⁻ z in parabolicCylinder x₀ t₀ 1, ‖Du z‖ₑ ^ (2 : ℝ) := by
        gcongr
        exact lintegral_mono_set (vorticityUnitBox_subset_cylinder x₀ t₀)
      _ ≤ 9 * ENNReal.ofReal (E ^ 2) := by gcongr
      _ = ENNReal.ofReal (9 * E ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hlin

/-- Set integrals of functions vanishing off a subset agree. -/
theorem vorticity_setIntegral_congr_of_vanish {S T : Set (Vec3 × ℝ)} {h : Vec3 × ℝ → ℝ}
    (hST : S ⊆ T) (hzero : ∀ z, z ∉ S → h z = 0) :
    ∫ z in S, h z = ∫ z in T, h z := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hzero z fun hzS => hz (hST hzS)]

/-- The gradient is the weak spatial gradient of the velocity on the open unit box. -/
theorem vorticityBase_weakGradient {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : IsSuitableWeakSolution Ω I q u Du p (fun _ => 0)) (hΩ : IsOpen Ω) (hI : IsOpen I)
    {x₀ : Vec3} {t₀ : ℝ} (hcl : closure (parabolicCylinder x₀ t₀ 1) ⊆ spaceTimeSet Ω I)
    (i j : Fin 3) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, u z i * spatialPartial ψ j z =
        -∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, Du z i j * ψ z := by
  intro ψ hψ hψc hψW
  obtain ⟨Ω', J, hbox, hsub⟩ := vorticity_exists_localBox_of_closure hΩ hI h.2.2.1 hcl
  have hdata : IsSuitableWeakSolutionData Ω I q u Du p (fun _ => 0) :=
    (isSuitableWeakSolution_iff_integrable.mp h).toData
  have hW0 : (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) ⊆ spaceTimeSet Ω I :=
    (vorticityUnitBox_subset_cylinder x₀ t₀).trans (subset_closure.trans hcl)
  have hψtest : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I := ⟨hψ, hψc, hψW.trans hW0⟩
  have hibp := suitableWeakSpatialIntegrationByParts h Ω' J hbox hψ hψc (hψW.trans hsub) i j
  have hint1 : IntegrableOn (fun z : Vec3 × ℝ => Du z i j * ψ z) (Ω' ×ˢ J) :=
    suitableWeakGradientTestIntegrableOnBox hdata hbox hψtest i j
  have hint2 : IntegrableOn (fun z : Vec3 × ℝ => u z i * spatialPartial ψ j z) (Ω' ×ˢ J) := by
    have hψ' : (fun z : Vec3 × ℝ => spatialPartial ψ j z) ∈
        spaceTimeTestFunction (V := ℝ) Ω I :=
      ⟨CKN.spatialPartial_contDiff hψ j, CKN.hasCompactSupport_spatialPartial hψc j,
        (CKN.tsupport_spatialPartial_subset j).trans (hψW.trans hW0)⟩
    exact suitableWeakVelocityTestIntegrableOnBox hdata hbox hψ' i
  rw [← vorticity_setIntegral_prod_time hint1, ← vorticity_setIntegral_prod_time hint2] at hibp
  have hvan1 : ∀ z, z ∉ (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) →
      Du z i j * ψ z = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport (fun h' => hz (hψW h')), mul_zero]
  have hvan2 : ∀ z, z ∉ (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) →
      u z i * spatialPartial ψ j z = 0 := fun z hz => by
    have hz' : z ∉ tsupport (fun z : Vec3 × ℝ => spatialPartial ψ j z) := fun h' =>
      hz (hψW (CKN.tsupport_spatialPartial_subset j h'))
    rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
  have hsub' : (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) ⊆ Ω' ×ˢ J := hsub
  rw [vorticity_setIntegral_congr_of_vanish hsub' hvan1,
    vorticity_setIntegral_congr_of_vanish hsub' hvan2]
  linarith only [hibp]

/-- The velocity is weakly divergence free on the open unit box. -/
theorem vorticityBase_div {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : IsSuitableWeakSolution Ω I q u Du p (fun _ => 0))
    {x₀ : Vec3} {t₀ : ℝ} (hcl : closure (parabolicCylinder x₀ t₀ 1) ⊆ spaceTimeSet Ω I) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀, ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
  intro ψ hψ hψc hψW
  have hW0 : (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) ⊆ spaceTimeSet Ω I :=
    (vorticityUnitBox_subset_cylinder x₀ t₀).trans (subset_closure.trans hcl)
  have hS2 := h.2.2.2.2.2.2.1 ψ ⟨hψ, hψc, hψW.trans hW0⟩
  have hvan : ∀ z, z ∉ (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) →
      ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := fun z hz => by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz' : z ∉ tsupport (fun z : Vec3 × ℝ => spatialPartial ψ i z) := fun h' =>
      hz (hψW (CKN.tsupport_spatialPartial_subset i h'))
    rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
  rw [vorticity_setIntegral_congr_of_vanish hW0 hvan]
  exact hS2

/-- Coordinate derivatives of the zero function vanish. -/
theorem vorticity_partials_zero (z : Vec3 × ℝ) (j : Fin 3) :
    timePartial (fun _ : Vec3 × ℝ => (0 : ℝ)) z = 0 ∧
      spatialPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j z = 0 ∧
      spatialSecondPartial (fun _ : Vec3 × ℝ => (0 : ℝ)) j j z = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [timePartial]
  · simp [spatialPartial]
  · simp [spatialSecondPartial, spatialPartial]

/-- Each vorticity component solves the weak heat equation with the divergence-form source
given by the vorticity flux on the open unit box (`lem:vorticity-weak-eq`). -/
theorem vorticityBase_heat {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (h : IsSuitableWeakSolution Ω I q u Du p (fun _ => 0)) (hΩ : IsOpen Ω) (hI : IsOpen I)
    {x₀ : Vec3} {t₀ : ℝ} (hcl : closure (parabolicCylinder x₀ t₀ 1) ⊆ spaceTimeSet Ω I)
    (i : Fin 3) :
    ∀ ψ : Vec3 × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ →
      ∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀,
          weakVorticity Du z i * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        -∫ z in vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀,
          ∑ j : Fin 3, -vorticityFlux u Du z j i * spatialPartial ψ j z := by
  intro ψ hψ hψc hψW
  have hW0 : (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) ⊆ spaceTimeSet Ω I :=
    (vorticityUnitBox_subset_cylinder x₀ t₀).trans (subset_closure.trans hcl)
  set ψv : Vec3 × ℝ → Vec3 := fun z k => if k = i then ψ z else 0 with hψvdef
  have hcomp : ∀ k, (fun w : Vec3 × ℝ => ψv w k) = if k = i then ψ else fun _ => 0 := by
    intro k
    by_cases hk : k = i
    · subst hk; funext w; simp [ψv]
    · funext w; simp [ψv, hk]
  have hψvtest : ψv ∈ spaceTimeTestFunction (V := Vec3) Ω I := by
    refine ⟨?_, ?_, ?_⟩
    · rw [contDiff_pi]
      intro k
      rw [hcomp k]
      split_ifs
      · exact hψ
      · exact contDiff_const
    · apply HasCompactSupport.intro' hψc.isCompact (isClosed_tsupport ψ)
      intro z hz
      funext k
      simp [ψv, image_eq_zero_of_notMem_tsupport hz]
    · have hsupp : Function.support ψv ⊆ Function.support ψ := by
        intro z hz
        by_contra hψz
        apply hz
        funext k
        simp only [Function.mem_support, not_not] at hψz
        simp [ψv, hψz]
      exact (closure_mono hsupp).trans (hψW.trans hW0)
  have heq := suitableWeakVorticityEquation hΩ hI h.2.2.1 h hψvtest
  have hTD : ∀ z : Vec3 × ℝ, ∀ k, vorticityTestTimeDerivative ψv z k =
      if k = i then timePartial ψ z else 0 := by
    intro z k
    change timePartial (fun w : Vec3 × ℝ => ψv w k) z = _
    rw [hcomp k]
    split_ifs
    · rfl
    · exact (vorticity_partials_zero z 0).1
  have hLap : ∀ z : Vec3 × ℝ, ∀ k, vorticityTestLaplacian ψv z k =
      if k = i then ∑ j : Fin 3, spatialSecondPartial ψ j j z else 0 := by
    intro z k
    change ∑ j : Fin 3, spatialSecondPartial (fun w : Vec3 × ℝ => ψv w k) j j z = _
    rw [hcomp k]
    split_ifs
    · rfl
    · exact Finset.sum_eq_zero fun j _ => (vorticity_partials_zero z j).2.2
  have hSP : ∀ z : Vec3 × ℝ, ∀ j k, spatialPartial (fun w : Vec3 × ℝ => ψv w k) j z =
      if k = i then spatialPartial ψ j z else 0 := by
    intro z j k
    rw [hcomp k]
    split_ifs
    · rfl
    · exact (vorticity_partials_zero z j).2.1
  have hlhs : ∀ z : Vec3 × ℝ,
      -(∑ k : Fin 3, weakVorticity Du z k * vorticityTestTimeDerivative ψv z k) -
          ∑ k : Fin 3, weakVorticity Du z k * vorticityTestLaplacian ψv z k =
        weakVorticity Du z i * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) := by
    intro z
    simp only [hTD, hLap, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hrhs : ∀ z : Vec3 × ℝ,
      ∑ j : Fin 3, ∑ k : Fin 3,
          vorticityFlux u Du z j k * spatialPartial (fun w : Vec3 × ℝ => ψv w k) j z =
        -∑ j : Fin 3, -vorticityFlux u Du z j i * spatialPartial ψ j z := by
    intro z
    simp only [hSP, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have heq' : ∫ z in spaceTimeSet Ω I, weakVorticity Du z i *
        (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
      ∫ z in spaceTimeSet Ω I,
        -∑ j : Fin 3, -vorticityFlux u Du z j i * spatialPartial ψ j z := by
    calc
      _ = ∫ z in spaceTimeSet Ω I,
          (-(∑ k : Fin 3, weakVorticity Du z k * vorticityTestTimeDerivative ψv z k) -
            ∑ k : Fin 3, weakVorticity Du z k * vorticityTestLaplacian ψv z k) :=
        integral_congr_ae (Eventually.of_forall fun z => (hlhs z).symm)
      _ = _ := heq
      _ = _ := integral_congr_ae (Eventually.of_forall hrhs)
  have hvanL : ∀ z, z ∉ (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) →
      weakVorticity Du z i * (-timePartial ψ z - ∑ j : Fin 3, spatialSecondPartial ψ j j z) =
        0 := by
    intro z hz
    have hzψ : z ∉ tsupport ψ := fun h' => hz (hψW h')
    have ht : timePartial ψ z = 0 := by
      by_contra hne
      exact hzψ (CKN.tsupport_timePartial_subset ψ (subset_tsupport _ hne))
    have hs : ∀ j : Fin 3, spatialSecondPartial ψ j j z = 0 := fun j =>
      CKN.spatialSecondPartial_eq_zero_off_tsupport hzψ j j
    simp [ht, hs]
  have hvanR : ∀ z, z ∉ (vec3Ball x₀ 1 ×ˢ Ioo (t₀ - 1) t₀ : Set (Vec3 × ℝ)) →
      -∑ j : Fin 3, -vorticityFlux u Du z j i * spatialPartial ψ j z = 0 := by
    intro z hz
    have hzψ : z ∉ tsupport ψ := fun h' => hz (hψW h')
    have hs : ∀ j : Fin 3, spatialPartial ψ j z = 0 := fun j => by
      have hz' : z ∉ tsupport (fun z : Vec3 × ℝ => spatialPartial ψ j z) := fun h' =>
        hzψ (CKN.tsupport_spatialPartial_subset j h')
      exact image_eq_zero_of_notMem_tsupport hz'
    simp [hs]
  rw [vorticity_setIntegral_congr_of_vanish hW0 hvanL, ← integral_neg,
    vorticity_setIntegral_congr_of_vanish hW0 hvanR]
  exact heq'

end ESS
