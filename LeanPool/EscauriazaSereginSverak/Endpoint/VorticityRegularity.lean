/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularityBox
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityBase
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs

/-!
# The vorticity regularity theorem

`thm:vorticity-regularity`: for a suitable weak solution with zero force whose velocity is
bounded by `M` on `Q₁(x₀, t₀)` and whose gradient has energy at most `E²` there, the vorticity has
on `Q_{1/2}(x₀, t₀)` a representative which is continuous up to the top time, has space-time
weak derivatives in `L²`, is bounded, and satisfies `|∂ₜω - Δω| ≤ C (|ω| + |∇ω|)`, with `C`
depending only on `M` and `E`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Restricted to the half cylinder, Lebesgue measure does not see the top time. -/
theorem vorticity_restrict_cylinder_half (x₀ : Vec3) (t₀ : ℝ) :
    (volume : Measure ParabolicPoint).restrict (parabolicCylinder x₀ t₀ (1 / 2)) =
      (volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀) := by
  have e : t₀ - (1 / 2 : ℝ) ^ 2 = t₀ - 1 / 4 := by norm_num
  have hQS : (vec3Ball x₀ (1 / 2) ×ˢ Ioc (t₀ - (1 / 2) ^ 2) t₀ : Set (Vec3 × ℝ)) =ᵐ[volume]
      (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ : Set (Vec3 × ℝ)) := by
    rw [e]
    exact Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Ioc.symm
  exact Measure.restrict_congr_set hQS

/-- The finiteness of the integral of the squared norm of a square-integrable field. -/
theorem vorticity_lintegral_sq_lt_top {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) : ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero
    ENNReal.ofNat_ne_top hf.eLpNorm_lt_top

/-- The finiteness of the sum of the squared norms of four square-integrable fields. -/
theorem vorticity_lintegral_four_lt_top {α E₁ E₂ E₃ E₄ : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
    [NormedAddCommGroup E₄] {μ : Measure α} {f₁ : α → E₁} {f₂ : α → E₂} {f₃ : α → E₃}
    {f₄ : α → E₄} (h₁ : MemLp f₁ 2 μ) (h₂ : MemLp f₂ 2 μ) (h₃ : MemLp f₃ 2 μ)
    (h₄ : MemLp f₄ 2 μ) :
    (∫⁻ a, ‖f₁ a‖ₑ ^ (2 : ℝ) + ‖f₂ a‖ₑ ^ (2 : ℝ) + ‖f₃ a‖ₑ ^ (2 : ℝ) + ‖f₄ a‖ₑ ^ (2 : ℝ) ∂μ) <
      ⊤ := by
  rw [lintegral_add_right' _ (h₄.aestronglyMeasurable.enorm.pow_const (2 : ℝ)),
    lintegral_add_right' _ (h₃.aestronglyMeasurable.enorm.pow_const (2 : ℝ)),
    lintegral_add_right' _ (h₂.aestronglyMeasurable.enorm.pow_const (2 : ℝ))]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
    ⟨vorticity_lintegral_sq_lt_top h₁, vorticity_lintegral_sq_lt_top h₂⟩,
    vorticity_lintegral_sq_lt_top h₃⟩, vorticity_lintegral_sq_lt_top h₄⟩

/-- `thm:vorticity-regularity`. -/
theorem vorticityRegularity : ∀ (q M E : ℝ), 5 / 2 < q → 0 ≤ M → 0 ≤ E →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (v : ParabolicPoint → Vec3)
        (Dv : ParabolicPoint → Fin 3 → Vec3)
        (pv : ParabolicPoint → ℝ) (x₀ : Vec3) (t₀ : ℝ),
        IsOpen Ω → IsOpen I →
        IsSuitableWeakSolution Ω I q v Dv pv
          (0 : ParabolicPoint → Vec3) →
        closure (parabolicCylinder x₀ t₀ 1) ⊆ spaceTimeSet Ω I →
        (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ 1)),
          vec3EuclideanNorm (v z) ≤ M) →
        (∫⁻ z in parabolicCylinder x₀ t₀ 1,
          ‖Dv z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2) →
        ∃ (ω : ParabolicPoint → Vec3)
          (Dω : ParabolicPoint → Fin 3 → Vec3)
          (D2ω : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
          (Dtω : ParabolicPoint → Vec3),
          ω =ᵐ[volume.restrict (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))]
            weakVorticity Dv ∧
          ContinuousOn ω (closure (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))) ∧
          HasSpaceTimeWeakDerivs (vec3Ball x₀ (1 / 2 : ℝ))
            (Ioo (t₀ - (1 / 4 : ℝ)) t₀) ω Dω D2ω Dtω ∧
          (∫⁻ z in parabolicCylinder x₀ t₀ (1 / 2 : ℝ),
            ‖ω z‖ₑ ^ (2 : ℝ) + ‖Dω z‖ₑ ^ (2 : ℝ) +
              ‖D2ω z‖ₑ ^ (2 : ℝ) + ‖Dtω z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
          (∀ᵐ z ∂(volume.restrict
              (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))),
            vec3EuclideanNorm
              (fun i => Dtω z i - ∑ j, D2ω z i j j) ≤
              C * (vec3EuclideanNorm (ω z) +
                Real.sqrt (spatialGradientSq ω Dω z))) ∧
          (∀ᵐ z ∂(volume.restrict
              (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))),
            vec3EuclideanNorm (ω z) ≤ C) := by
  rintro q M E - hM -
  obtain ⟨C, hC, hbox⟩ := vorticityRegularity_box M (9 * E ^ 2) hM
  refine ⟨27 * C, by positivity, ?_⟩
  intro Ω I v Dv pv x₀ t₀ hΩ hI hsws hcl hvM hE
  obtain ⟨hU, hG⟩ := vorticityBase_memLp hsws hΩ hI hcl
  obtain ⟨ω, Ω1, Ω2, Dt, hωc, hωb, hωae, hωL, hΩ1L, hΩ2L, hDtL, hdw, hdΩ, hdt, hineq⟩ :=
    hbox x₀ t₀ (fun i z => v z i) (fun i j z => Dv z i j) hU hG (vorticityBase_bound hvM)
      (vorticityBase_energy hG hE) (fun i j => vorticityBase_weakGradient hsws hΩ hI hcl i j)
      (vorticityBase_div hsws hcl) (fun i => vorticityBase_heat hsws hΩ hI hcl i)
  have hkey := vorticity_restrict_cylinder_half x₀ t₀
  have hSm : MeasurableSet (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀ : Set (Vec3 × ℝ)) :=
    (vorticityBox_isOpen x₀ _ _ t₀).measurableSet
  have hSb := vorticityBox_isBounded x₀ (1 / 2) _ (Metric.isBounded_Ioo (t₀ - 1 / 4) t₀)
  have : IsFiniteMeasure (volume.restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) :=
    isFiniteMeasure_restrict.2 hSb.measure_lt_top.ne
  have hωV : MemLp (fun z : ParabolicPoint => fun i => ω i z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) :=
    MemLp.of_eval hωL
  have hDωV : MemLp (fun z : ParabolicPoint => fun i j => Ω1 i j z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) :=
    MemLp.of_eval fun i => MemLp.of_eval fun j => hΩ1L i j
  have hD2ωV : MemLp (fun z : ParabolicPoint => fun i j k => Ω2 i j k z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) :=
    MemLp.of_eval fun i => MemLp.of_eval fun j => MemLp.of_eval fun k => hΩ2L i j k
  have hDtV : MemLp (fun z : ParabolicPoint => fun i => Dt i z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) :=
    MemLp.of_eval hDtL
  refine ⟨fun z i => ω i z, fun z i j => Ω1 i j z, fun z i j k => Ω2 i j k z, fun z i => Dt i z,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ∀ᵐ z ∂((volume : Measure ParabolicPoint).restrict (parabolicCylinder x₀ t₀ (1 / 2))),
      (fun i => ω i z) = weakVorticity Dv z
    rw [hkey]
    filter_upwards [ae_all_iff.2 hωae] with z hz
    funext i
    exact hz i
  · have e : t₀ - (1 / 2 : ℝ) ^ 2 = t₀ - 1 / 4 := by norm_num
    rw [closure_parabolicCylinder (by norm_num), e]
    exact (continuousOn_pi.2 hωc).comp parabolicHomeomorph.continuous.continuousOn
      fun p hp => hp
  · have loc : ∀ {F : Type} [NormedAddCommGroup F] {f : ParabolicPoint → F},
        MemLp f 2 ((volume : Measure (Vec3 × ℝ)).restrict
          (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) →
        LocallyIntegrableOn f (spaceTimeSet (vec3Ball x₀ (1 / 2)) (Ioo (t₀ - 1 / 4) t₀))
          (volume : Measure ParabolicPoint) := fun {F} _ {f} hf => by
      have hf' : MemLp (fun z : Vec3 × ℝ => f z) 2 ((volume : Measure (Vec3 × ℝ)).restrict
          (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀)) := hf
      have hi := hf'.integrable (by norm_num)
      exact IntegrableOn.locallyIntegrableOn hi
    refine ⟨loc hωV, loc hDωV, loc hD2ωV, loc hDtV, fun φ hφ => ⟨fun i j => ?_,
        fun i j k => ?_, fun i => ?_⟩⟩
    · exact hdw i j φ hφ.1 hφ.2.1 hφ.2.2
    · exact hdΩ i j k φ hφ.1 hφ.2.1 hφ.2.2
    · exact hdt i φ hφ.1 hφ.2.1 hφ.2.2
  · rw [hkey]
    exact vorticity_lintegral_four_lt_top hωV hDωV hD2ωV hDtV
  · rw [hkey]
    filter_upwards [hineq] with z hz
    show vec3EuclideanNorm (fun i => Dt i z - ∑ j : Fin 3, Ω2 i j j z) ≤
      27 * C * (vec3EuclideanNorm (fun i => ω i z) +
        Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2))
    have hN := vec3EuclideanNorm_nonneg (fun i => ω i z)
    have hA : ∑ l : Fin 3, |ω l z| ≤ 3 * vec3EuclideanNorm (fun i => ω i z) := by
      calc
        _ ≤ ∑ _l : Fin 3, vec3EuclideanNorm (fun i => ω i z) :=
          Finset.sum_le_sum fun l _ => abs_apply_le_vec3EuclideanNorm (fun i => ω i z) l
        _ = 3 * vec3EuclideanNorm (fun i => ω i z) := by
          rw [Fin.sum_univ_three]
          ring
    have hB : ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z| ≤
        9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) := by
      calc
        _ ≤ ∑ _a : Fin 3, ∑ _b : Fin 3, Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
            Real.abs_le_sqrt (vorticity_sq_le_sum_two (fun i j => Ω1 i j z) a b)
        _ = 9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2) := by
          rw [Fin.sum_univ_three, Fin.sum_univ_three]
          ring
    have hsum : ∑ i : Fin 3, |Dt i z - ∑ j : Fin 3, Ω2 i j j z| ≤
        3 * (C * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|)) := by
      calc
        _ ≤ ∑ _i : Fin 3, C * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) :=
          Finset.sum_le_sum fun i _ => hz i
        _ = _ := by
          rw [Fin.sum_univ_three]
          ring
    have hmono := mul_le_mul_of_nonneg_left (add_le_add hA hB) hC
    have e1 : 27 * C * (vec3EuclideanNorm (fun i => ω i z) +
        Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2)) =
        3 * (C * (3 * vec3EuclideanNorm (fun i => ω i z) +
          9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2))) +
          18 * (C * vec3EuclideanNorm (fun i => ω i z)) := by ring
    have p := mul_nonneg hC hN
    exact (vec3EuclideanNorm_le_sum_abs _).trans (by linarith only [hsum, hmono, e1, p])
  · rw [hkey]
    filter_upwards [ae_restrict_mem hSm] with z hz
    have hzK : z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 1 / 2} ×ˢ Icc (t₀ - 1 / 4) t₀ :
        Set (Vec3 × ℝ)) :=
      ⟨show vec3EuclideanNorm (z.1 - x₀) ≤ 1 / 2 from le_of_lt hz.1, le_of_lt hz.2.1,
        le_of_lt hz.2.2⟩
    refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    have h3 : ∑ i : Fin 3, |ω i z| ≤ 3 * C := by
      calc
        _ ≤ ∑ _i : Fin 3, C := Finset.sum_le_sum fun i _ => hωb i z hzK
        _ = 3 * C := by
          rw [Fin.sum_univ_three]
          ring
    exact h3.trans (by linarith only [hC])

end ESS
