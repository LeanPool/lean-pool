/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.Stationarity
public import LeanPool.HighContrastHomogenization.Frozen.UnitRange
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicDilationCoeff

/-!
# High-contrast homogenization: Provider.Quenched.TriadicRebasedLaw

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Triadic rebasing of coefficient laws

The rebased law is the pushforward by the quotient-level coefficient dilation.
The probability, stationarity, and unit-range properties are transported
directly on the coefficient-space carrier.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The coefficient law viewed at the triadically dilated spatial scale. -/
@[expose]
noncomputable def triadicRebasedLaw (n : ℕ) (P : Measure (CoeffSpace d)) :
    Measure (CoeffSpace d) :=
  Measure.map (CoeffSpace.triadicDilation n) P

/-- A triadically rebased probability law is again a probability law. -/
theorem isProbabilityMeasure_triadicRebasedLaw (n : ℕ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (triadicRebasedLaw n P) := by
  unfold triadicRebasedLaw
  infer_instance

private theorem indep_map_measurableEquiv
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {m₁ m₂ : MeasurableSpace β}
    (h : @ProbabilityTheory.Indep α
      (MeasurableSpace.comap (fun x : α => e x) m₁)
      (MeasurableSpace.comap (fun x : α => e x) m₂) mα μ) :
    @ProbabilityTheory.Indep β m₁ m₂ mβ
      (@Measure.map α β mα mβ (fun x : α => e x) μ) := by
  refine (ProbabilityTheory.Indep_iff
    (m₁ := m₁) (m₂ := m₂) (_mΩ := mβ)
    (μ := @Measure.map α β mα mβ (fun x : α => e x) μ)).2 ?_
  intro s t hs ht
  have hemb : @MeasurableEmbedding α β mα mβ (fun x : α => e x) :=
    @MeasurableEquiv.measurableEmbedding α β mα mβ e
  have hindep := (ProbabilityTheory.Indep_iff
    (m₁ := MeasurableSpace.comap (fun x : α => e x) m₁)
    (m₂ := MeasurableSpace.comap (fun x : α => e x) m₂)
    (_mΩ := mα) (μ := μ)).1 h
  have hsPre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m₁)
      ((fun x : α => e x) ⁻¹' s) := ⟨s, hs, rfl⟩
  have htPre : @MeasurableSet α
      (MeasurableSpace.comap (fun x : α => e x) m₂)
      ((fun x : α => e x) ⁻¹' t) := ⟨t, ht, rfl⟩
  have hst := hindep ((fun x : α => e x) ⁻¹' s)
    ((fun x : α => e x) ⁻¹' t) hsPre htPre
  have hmapInter :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ (s ∩ t)
  have hmapS :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) s =
        μ ((fun x : α => e x) ⁻¹' s) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ s
  have hmapT :
      (@Measure.map α β mα mβ (fun x : α => e x) μ) t =
        μ ((fun x : α => e x) ⁻¹' t) :=
    @MeasurableEmbedding.map_apply α β mα mβ
      (fun x : α => e x) hemb μ t
  calc
    (@Measure.map α β mα mβ (fun x : α => e x) μ) (s ∩ t) =
        μ ((fun x : α => e x) ⁻¹' (s ∩ t)) := hmapInter
    _ = μ (((fun x : α => e x) ⁻¹' s) ∩
          ((fun x : α => e x) ⁻¹' t)) := rfl
    _ = μ ((fun x : α => e x) ⁻¹' s) *
          μ ((fun x : α => e x) ⁻¹' t) := hst
    _ = (@Measure.map α β mα mβ (fun x : α => e x) μ) s *
          (@Measure.map α β mα mβ (fun x : α => e x) μ) t := by
      rw [hmapS, hmapT]

/-- Frozen integer stationarity is preserved by triadic rebasing. -/
theorem stationaryLaw_triadicRebasedLaw {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsStationaryLaw P) (n : ℕ) :
    HCPoly.Frozen.IsStationaryLaw (triadicRebasedLaw n P) := by
  intro z
  rw [triadicRebasedLaw,
    Measure.map_map (measurable_translateCoeff z)
      (CoeffSpace.measurable_triadicDilation n),
    show translateCoeff z ∘ CoeffSpace.triadicDilation n =
        CoeffSpace.triadicDilation n ∘
          translateCoeff (triadicScaleIntShift n z) by
      funext a
      exact CoeffSpace.translateCoeff_triadicDilation n z a,
    ← Measure.map_map (CoeffSpace.measurable_triadicDilation n)
      (measurable_translateCoeff (triadicScaleIntShift n z)),
    hP (triadicScaleIntShift n z)]

private theorem supDist_triadicDilateVec (n : ℕ) (x y : Vec d) :
    Source.AKL.supDist (triadicDilateVec n x) (triadicDilateVec n y) =
      (3 : ℝ) ^ n * Source.AKL.supDist x y := by
  unfold Source.AKL.supDist
  have hsub : triadicDilateVec n x - triadicDilateVec n y =
      ((3 : ℝ) ^ n) • (x - y) := by
    ext i
    simp only [triadicDilateVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- Triadic dilation preserves unit separation of ambient sets. -/
theorem UnitSeparated.triadicDilateSet {U V : Set (Vec d)}
    (hUV : UnitSeparated U V) (n : ℕ) :
    UnitSeparated (triadicDilateSet n U) (triadicDilateSet n V) := by
  intro x y hx hy
  rcases hx with ⟨x₀, hx₀, rfl⟩
  rcases hy with ⟨y₀, hy₀, rfl⟩
  rw [supDist_triadicDilateVec]
  have hscale : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  calc
    1 = (1 : ℝ) * 1 := by ring
    _ ≤ (3 : ℝ) ^ n * Source.AKL.supDist x₀ y₀ :=
      mul_le_mul hscale (hUV hx₀ hy₀) zero_le_one (by positivity)

private theorem measurableSet_triadicDilateSet_local (n : ℕ)
    {U : Set (Vec d)} (hU : MeasurableSet U) :
    MeasurableSet (triadicDilateSet n U) := by
  have hc : ((3 : ℝ) ^ n) ≠ 0 := by positivity
  have hg : Measurable
      (fun x : Vec d => fun i => ((3 : ℝ) ^ n)⁻¹ * x i) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).const_mul _
  have hset : triadicDilateSet n U =
      (fun x : Vec d => fun i => ((3 : ℝ) ^ n)⁻¹ * x i) ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hxy :
          (fun i => ((3 : ℝ) ^ n)⁻¹ * triadicDilateVec n y i) = y := by
        funext i
        simp only [triadicDilateVec]
        rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
      simpa only [Set.mem_preimage, hxy] using hy
    · intro hx
      refine ⟨fun i => ((3 : ℝ) ^ n)⁻¹ * x i, hx, ?_⟩
      funext i
      simp only [triadicDilateVec]
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [hset]
  exact hg hU

/-- Frozen unit-range dependence is preserved by triadic rebasing. -/
theorem unitRangeLaw_triadicRebasedLaw {P : Measure (CoeffSpace d)}
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) (n : ℕ) :
    HCPoly.Frozen.IsUnitRangeLaw (triadicRebasedLaw n P) := by
  intro U V hU hV hUV
  have hDU : MeasurableSet (triadicDilateSet n U) :=
    measurableSet_triadicDilateSet_local n hU
  have hDV : MeasurableSet (triadicDilateSet n V) :=
    measurableSet_triadicDilateSet_local n hV
  let e := CoeffSpace.triadicDilationMeasurableEquiv (d := d) n
  have hIndepDilated : ProbabilityTheory.Indep
      (coeffSigma d (triadicDilateSet n U))
      (coeffSigma d (triadicDilateSet n V)) P :=
    hP (triadicDilateSet n U) (triadicDilateSet n V) hDU hDV
      (hUV.triadicDilateSet n)
  have hUle : MeasurableSpace.comap
      (fun a : CoeffSpace d => CoeffSpace.triadicDilation n a) (coeffSigma d U) ≤
        coeffSigma d (triadicDilateSet n U) :=
    (CoeffSpace.measurable_triadicDilation_coeffSigma n U).comap_le
  have hVle : MeasurableSpace.comap
      (fun a : CoeffSpace d => CoeffSpace.triadicDilation n a) (coeffSigma d V) ≤
        coeffSigma d (triadicDilateSet n V) :=
    (CoeffSpace.measurable_triadicDilation_coeffSigma n V).comap_le
  have hComap : ProbabilityTheory.Indep
      (MeasurableSpace.comap
        (fun a : CoeffSpace d => CoeffSpace.triadicDilation n a) (coeffSigma d U))
      (MeasurableSpace.comap
        (fun a : CoeffSpace d => CoeffSpace.triadicDilation n a) (coeffSigma d V)) P :=
    ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hIndepDilated hUle) hVle
  have hMap := indep_map_measurableEquiv (μ := P) e hComap
  simpa [triadicRebasedLaw, e] using! hMap

end

end HighContrast
end HCPolySupport
