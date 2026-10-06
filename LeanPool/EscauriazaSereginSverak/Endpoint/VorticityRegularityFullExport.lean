/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularitySource
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularityBoxQuantified

/-!
# Quantitative vorticity regularity on a past half-cylinder

The box construction exports a continuous vorticity representative together with the stage
constants, a quantitative spacetime `W^{2,1}_2` bound, and time-slice `H²` estimates. This module
transfers those conclusions to the parabolic cylinder in `thm:vorticity-regularity`.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- `thm:vorticity-regularity`. -/
theorem vorticityRegularity_full_quantified : ∀ (q M E : ℝ), 5 / 2 < q → 0 ≤ M → 0 ≤ E →
    ∃ Kw K1 K2 C Cslice : ℝ, 0 ≤ C ∧ 0 ≤ Cslice ∧
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
          (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))),
            vec3EuclideanNorm (v z) + Real.sqrt (spatialGradientSq v Dv z) ≤ C) ∧
          ω =ᵐ[volume.restrict (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))]
            weakVorticity Dv ∧
          ContinuousOn ω (closure (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))) ∧
          (∀ z ∈ closure (parabolicCylinder x₀ t₀ (1 / 2 : ℝ)),
            vec3EuclideanNorm (ω z) ≤ C) ∧
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
            vec3EuclideanNorm (ω z) ≤ C) ∧
          Real.sqrt (∫ z in parabolicCylinder x₀ t₀ (1 / 2 : ℝ),
            (∑ i : Fin 3, (ω z i) ^ 2) +
              (∑ i : Fin 3, ∑ j : Fin 3, (Dω z i j) ^ 2) +
              (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, (D2ω z i j k) ^ 2) +
            (∑ i : Fin 3, (Dtω z i) ^ 2)) ≤ C ∧
          (∀ t ∈ Icc (t₀ - 1 / 4 : ℝ) t₀, ∀ i : Fin 3,
            ∃ Gt : Fin 3 → Vec3 → ℝ, ∃ Ht : Fin 3 → Fin 3 → Vec3 → ℝ,
              (∀ j, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) j
                (fun x => ω (x, t) i) (Gt j)) ∧
              (∀ j k, HasWeakPartialDerivOn (vec3Ball x₀ (38 / 64)) k
                (Gt j) (Ht j k)) ∧
              ∫ x in vec3Ball x₀ (38 / 64),
                ((ω (x, t) i) ^ 2 + ∑ j : Fin 3, Gt j x ^ 2 +
                  ∑ j : Fin 3, ∑ k : Fin 3, Ht j k x ^ 2) ≤
                  Cslice * (|Kw| + |K1| + |K2| + 1) ∧
              Real.sqrt (∫ x in vec3Ball x₀ (38 / 64),
                ((ω (x, t) i) ^ 2 + ∑ j : Fin 3, Gt j x ^ 2 +
                  ∑ j : Fin 3, ∑ k : Fin 3, Ht j k x ^ 2)) ≤ C) := by
  rintro q M E _ hM hE
  obtain ⟨Kw, K1, K2, Cb, Cslice, C21, hCb, hCslice, hC21, hbox⟩ :=
    vorticityRegularity_box_quantified M (9 * E ^ 2) hM
  obtain ⟨Kg, hKg, hgrad⟩ := vorticityRegularity_gradient_box M (9 * E ^ 2) hM
  set C : ℝ := M + 3 * Kg + 27 * Cb + 3 * Cb + C21 +
    3 * Cslice * (|Kw| + |K1| + |K2| + 1) + 1
  have hC : 0 ≤ C := by positivity
  have hX : 0 ≤ Cslice * (|Kw| + |K1| + |K2| + 1) := by positivity
  have hCess : M + 3 * Kg ≤ C := by
    dsimp [C]
    nlinarith only [hM, hKg, hCb, hC21, hX]
  have hCbox : 3 * Cb ≤ C := by
    dsimp [C]
    nlinarith only [hM, hKg, hCb, hC21, hX]
  have hCineq : 27 * Cb ≤ C := by
    dsimp [C]
    nlinarith only [hM, hKg, hCb, hC21, hX]
  have hC21' : C21 ≤ C := by
    dsimp [C]
    nlinarith only [hM, hKg, hCb, hC21, hX]
  have hCstage : Cslice * (|Kw| + |K1| + |K2| + 1) + 1 ≤ C := by
    dsimp [C]
    nlinarith only [hM, hKg, hCb, hC21, hX]
  refine ⟨Kw, K1, K2, C, Cslice, hC, hCslice, ?_⟩
  intro Ω I v Dv pv x₀ t₀ hΩ hI hsws hcl hvM hE
  obtain ⟨hU, hG⟩ := vorticityBase_memLp hsws hΩ hI hcl
  have hrootBox := hgrad x₀ t₀ (fun i z => v z i) (fun i j z => Dv z i j) hU hG
    (vorticityBase_bound hvM) (vorticityBase_energy hG hE)
    (fun i j => vorticityBase_weakGradient hsws hΩ hI hcl i j)
    (vorticityBase_div hsws hcl) (fun i => vorticityBase_heat hsws hΩ hI hcl i)
  obtain ⟨ω, Ω1, Ω2, Dt, hωc, hωb, hωae, hωL, hΩ1L, hΩ2L, hDtL,
      hdw, hdΩ, hdt, hineqBox, hslice, hW21⟩ :=
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
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · let Sprod : Set (Vec3 × ℝ) := vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀
    let Spara : Set ParabolicPoint := spaceTimeSet (vec3Ball x₀ (1 / 2))
      (Ioo (t₀ - 1 / 4) t₀)
    have hSm' : MeasurableSet Sprod := by
      dsimp [Sprod]
      exact (vorticityBox_isOpen x₀ (1 / 2) (t₀ - 1 / 4) t₀).measurableSet
    have hpre : parabolicHomeomorph ⁻¹' Sprod = Spara := by
      ext z
      rfl
    have hmp := parabolicHomeomorph_measurePreserving.restrict_preimage hSm'
    rw [hpre] at hmp
    have ht : Filter.Tendsto parabolicHomeomorph
        (ae (volume.restrict Spara)) (ae (volume.restrict Sprod)) := by
      have ht' := Measure.tendsto_ae_map (μ := volume.restrict Spara)
        hmp.measurable.aemeasurable
      rw [hmp.map_eq] at ht'
      exact ht'
    have hrootOpen : ∀ᵐ z ∂(volume.restrict Spara),
        Real.sqrt (spatialGradientSq v Dv z) ≤ 3 * Kg := by
      have hmapped := ht.eventually hrootBox
      filter_upwards [hmapped] with z hz
      change Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Dv z i j ^ 2) ≤ 3 * Kg
      convert hz using 1
      rfl
    have hbottom : t₀ - (1 / 2 : ℝ) ^ 2 = t₀ - 1 / 4 := by norm_num
    have hset : Spara =ᵐ[volume] parabolicCylinder x₀ t₀ (1 / 2 : ℝ) := by
      change (vec3Ball x₀ (1 / 2) ×ˢ Ioo (t₀ - 1 / 4) t₀) =ᵐ[volume]
        (vec3Ball x₀ (1 / 2) ×ˢ Ioc (t₀ - (1 / 2 : ℝ) ^ 2) t₀)
      rw [hbottom]
      exact Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Ioc
    have hrootMeasure : volume.restrict Spara =
        volume.restrict (parabolicCylinder x₀ t₀ (1 / 2 : ℝ)) :=
      Measure.restrict_congr_set hset
    have hroot : ∀ᵐ z ∂(volume.restrict
        (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))),
        Real.sqrt (spatialGradientSq v Dv z) ≤ 3 * Kg := by
      rw [← hrootMeasure]
      exact hrootOpen
    have hsub := parabolicCylinder_mono (x := x₀) (t := t₀)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hvel : ∀ᵐ z ∂(volume.restrict
        (parabolicCylinder x₀ t₀ (1 / 2 : ℝ))), vec3EuclideanNorm (v z) ≤ M :=
      ae_mono (Measure.restrict_mono hsub le_rfl) hvM
    filter_upwards [hvel, hroot] with z hv hg
    calc
      vec3EuclideanNorm (v z) + Real.sqrt (spatialGradientSq v Dv z) ≤ M + 3 * Kg :=
        add_le_add hv hg
      _ ≤ C := hCess
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
  · have e : t₀ - (1 / 2 : ℝ) ^ 2 = t₀ - 1 / 4 := by norm_num
    rw [closure_parabolicCylinder (by norm_num), e]
    intro z hz
    refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    have h3 : ∑ i : Fin 3, |ω i z| ≤ 3 * Cb := by
      calc
        _ ≤ ∑ _i : Fin 3, Cb := Finset.sum_le_sum fun i _ => hωb i z hz
        _ = 3 * Cb := by rw [Fin.sum_univ_three]; ring
    exact h3.trans hCbox
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
    filter_upwards [hineqBox] with z hz
    have hspatial : spatialGradientSq (fun z i => ω i z)
        (fun z i j => Ω1 i j z) z = ∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2 := by
      simp [spatialGradientSq]
    rw [hspatial]
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
        3 * (Cb * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|)) := by
      calc
        _ ≤ ∑ _i : Fin 3, Cb * (∑ l : Fin 3, |ω l z| + ∑ a : Fin 3, ∑ b : Fin 3, |Ω1 a b z|) :=
          Finset.sum_le_sum fun i _ => hz i
        _ = _ := by
          rw [Fin.sum_univ_three]
          ring
    have hmono := mul_le_mul_of_nonneg_left (add_le_add hA hB) hCb
    have e1 : 27 * Cb * (vec3EuclideanNorm (fun i => ω i z) +
        Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2)) =
        3 * (Cb * (3 * vec3EuclideanNorm (fun i => ω i z) +
          9 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2))) +
          18 * (Cb * vec3EuclideanNorm (fun i => ω i z)) := by ring
    have p := mul_nonneg hCb hN
    have hsumBd : ∑ i : Fin 3, |Dt i z - ∑ j : Fin 3, Ω2 i j j z| ≤
        27 * Cb * (vec3EuclideanNorm (fun i => ω i z) +
          Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2)) := by
      linarith only [hsum, hmono, e1, p]
    have hineqSmall : vec3EuclideanNorm (fun i => Dt i z - ∑ j : Fin 3, Ω2 i j j z) ≤
        27 * Cb * (vec3EuclideanNorm (fun i => ω i z) +
          Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, Ω1 i j z ^ 2)) :=
      (vec3EuclideanNorm_le_sum_abs _).trans hsumBd
    exact hineqSmall.trans (mul_le_mul_of_nonneg_right hCineq
      (add_nonneg (vec3EuclideanNorm_nonneg _) (Real.sqrt_nonneg _)))
  · rw [hkey]
    filter_upwards [ae_restrict_mem hSm] with z hz
    have hzK : z ∈ ({x : Vec3 | vec3EuclideanNorm (x - x₀) ≤ 1 / 2} ×ˢ Icc (t₀ - 1 / 4) t₀ :
        Set (Vec3 × ℝ)) :=
      ⟨show vec3EuclideanNorm (z.1 - x₀) ≤ 1 / 2 from le_of_lt hz.1, le_of_lt hz.2.1,
        le_of_lt hz.2.2⟩
    refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    have h3 : ∑ i : Fin 3, |ω i z| ≤ 3 * Cb := by
      calc
        _ ≤ ∑ _i : Fin 3, Cb := Finset.sum_le_sum fun i _ => hωb i z hzK
        _ = 3 * Cb := by
          rw [Fin.sum_univ_three]
          ring
    exact h3.trans hCbox
  · rw [hkey]
    exact hW21.trans hC21'
  · intro t ht i
    obtain ⟨Gt, Ht, hGt, hHt, hbound⟩ := hslice i t ht
    refine ⟨Gt, Ht, hGt, hHt, hbound, ?_⟩
    let Xslice : ℝ := Cslice * (|Kw| + |K1| + |K2| + 1)
    have hXslice : 0 ≤ Xslice := by positivity
    have hrootX : Real.sqrt Xslice ≤ Xslice + 1 := by
      have hsquare := Real.sq_sqrt hXslice
      nlinarith only [hsquare, sq_nonneg (Real.sqrt Xslice - (1 / 2 : ℝ))]
    calc
      Real.sqrt (∫ x in vec3Ball x₀ (38 / 64),
          ((ω i (x, t)) ^ 2 + ∑ j : Fin 3, Gt j x ^ 2 +
            ∑ j : Fin 3, ∑ k : Fin 3, Ht j k x ^ 2)) ≤ Real.sqrt Xslice := by
        apply Real.sqrt_le_sqrt
        simpa [Xslice] using hbound
      _ ≤ Xslice + 1 := hrootX
      _ ≤ C := hCstage


end ESS
