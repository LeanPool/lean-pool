/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicPullback
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# SGPT circle means and source PSH conventions

The actual nonnegative Lebesgue deficit integral is reused from the main
branch. Its conversion to an upper-bounded extended-real circle integral
retains negative infinity; no distribution or current certificate is used.
-/

@[expose] public section

namespace SGPT.PSH

open Set Metric MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The actual upper-bounded extended circle integral, normalized by `2π`.
For a genuine disc upper bound `C`, this is the integral of the obstacle,
including a bottom value when its negative part has infinite integral. -/
noncomputable def circleMean (u : E → EReal) (x v : E) (r C : ℝ) : EReal :=
  (C : EReal) - (SGPT.Foundations.Analysis.circleDeficit u x v r C /
    ENNReal.ofReal (2 * Real.pi) : ℝ≥0∞)

/-- The finite strictly positive angular measure used in every actual mean. -/
theorem angularMeasure_ne_zero : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

/-- The extended circle mean criterion is exactly the existing deficit
criterion, including bottom centers and infinite integrals. -/
theorem le_circleMean_iff {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C : ℝ)
    (hC : ∀ y ∈ SGPT.Foundations.Analysis.affineClosedDisc x v r, u y ≤ (C : EReal)) :
    u x ≤ circleMean u x v r C ↔
      SGPT.Foundations.Analysis.circleDeficit u x v r C ≤
        ENNReal.ofReal (2 * Real.pi) * ((C : EReal) - u x).toENNReal := by
  have hn : 0 ≤ (C : EReal) - u x :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).mpr
      (hC x (SGPT.Foundations.Analysis.center_mem_affineClosedDisc x v hr))
  unfold circleMean
  rw [EReal.le_sub_iff_add_le (Or.inr (EReal.coe_ne_bot C))
      (Or.inr (EReal.coe_ne_top C)), add_comm,
    ← EReal.le_sub_iff_add_le (Or.inr (EReal.coe_ne_bot C))
      (Or.inr (EReal.coe_ne_top C))]
  rw [← EReal.coe_toENNReal hn, EReal.coe_ennreal_le_coe_ennreal_iff]
  simp only [EReal.toENNReal_coe]
  exact ENNReal.div_le_iff' angularMeasure_ne_zero ENNReal.ofReal_ne_top

/-- Increasing the finite majorant does not change the actual extended mean. -/
theorem circleMean_add_bound {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C a : ℝ) (ha : 0 ≤ a)
    (hC : ∀ y ∈ SGPT.Foundations.Analysis.affineClosedDisc x v r, u y ≤ (C : EReal)) :
    circleMean u x v r (C + a) = circleMean u x v r C := by
  unfold circleMean
  rw [SGPT.Foundations.Analysis.circleDeficit_add_bound x v hr C a ha hC,
    ENNReal.add_div, mul_comm (ENNReal.ofReal (2 * Real.pi)) (ENNReal.ofReal a),
    ENNReal.mul_div_cancel_right angularMeasure_ne_zero ENNReal.ofReal_ne_top,
    EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal,
    max_eq_left ha, EReal.coe_add, add_comm (C : EReal) (a : EReal),
    EReal.add_sub_add_comm (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))]
  simp

/-- The source integral is independent of both possible finite upper bounds. -/
theorem circleMean_eq_of_bounds {u : E → EReal} (x v : E) {r : ℝ}
    (hr : 0 ≤ r) (C D : ℝ)
    (hC : ∀ y ∈ SGPT.Foundations.Analysis.affineClosedDisc x v r, u y ≤ (C : EReal))
    (hD : ∀ y ∈ SGPT.Foundations.Analysis.affineClosedDisc x v r, u y ≤ (D : EReal)) :
    circleMean u x v r C = circleMean u x v r D := by
  have hC' := circleMean_add_bound x v hr C (max C D - C)
    (sub_nonneg.mpr (le_max_left C D)) hC
  have hD' := circleMean_add_bound x v hr D (max C D - D)
    (sub_nonneg.mpr (le_max_right C D)) hD
  have hCsum : C + (max C D - C) = max C D := by ring
  have hDsum : D + (max C D - D) = max C D := by ring
  rw [hCsum] at hC'
  rw [hDsum] at hD'
  exact hC'.symm.trans hD'

/-- The actual circle mean of a constant below its bound recovers that
constant, including negative infinity. -/
theorem circleMean_const (a : EReal) (x v : E) (r C : ℝ) (ha : a ≤ (C : EReal)) :
    circleMean (fun _ ↦ a) x v r C = a := by
  have hn : 0 ≤ (C : EReal) - a :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).mpr ha
  unfold circleMean
  rw [SGPT.Foundations.Analysis.circleDeficit_const,
    mul_comm (ENNReal.ofReal (2 * Real.pi)),
    ENNReal.mul_div_cancel_right angularMeasure_ne_zero ENNReal.ofReal_ne_top,
    EReal.coe_toENNReal hn]
  cases a using EReal.rec <;> simp [← EReal.coe_sub]

/-- The unit-direction affine disc is the actual source closed complex ball. -/
theorem affineClosedDisc_one (a : ℂ) (r : ℝ) :
    SGPT.Foundations.Analysis.affineClosedDisc a 1 r = closedBall a r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [smul_eq_mul, dist_eq_norm] using hw
  · intro hz
    refine ⟨z - a, ?_, ?_⟩
    · simpa [dist_eq_norm] using hz
    · simp [smul_eq_mul]

/-- The source circle-mean inequality on the actual closed complex balls.
Every possible finite upper bound gives the same actual extended integral. -/
def HasCircleMeanOn (u : ℂ → EReal) (U : Set ℂ) : Prop :=
  ∀ a : ℂ, ∀ r : ℝ, 0 < r → closedBall a r ⊆ U →
    ∀ C : ℝ, (∀ z ∈ closedBall a r, u z ≤ (C : EReal)) →
      u a ≤ circleMean u a 1 r C

/-- The actual source `def:subhar1`, in ambient representatives on a domain.
The non-bottom clause is retained separately from the disc submean property. -/
structure SubharmonicOn (u : ℂ → EReal) (U : Set ℂ) : Prop where
  ne_top : ∀ z ∈ U, u z ≠ ⊤
  upperSemicontinuousOn : UpperSemicontinuousOn u U
  nontrivial : ∃ z ∈ U, u z ≠ ⊥
  submean : HasCircleMeanOn u U

/-- Reuse of the actual main-branch disc theorem gives source subharmonicity
as soon as its required non-bottom point exists. -/
theorem subharmonicOn_of_disc {u : ℂ → EReal} {U : Set ℂ}
    (hu : SGPT.Foundations.Analysis.DiscPshOn u U) (hn : ∃ z ∈ U, u z ≠ ⊥) :
    SubharmonicOn u U := by
  refine ⟨hu.ne_top, hu.upperSemicontinuousOn, hn, ?_⟩
  intro a r hr hD C hC
  have hD' : SGPT.Foundations.Analysis.affineClosedDisc a 1 r ⊆ U := by
    rwa [affineClosedDisc_one]
  have hC' : ∀ z ∈ SGPT.Foundations.Analysis.affineClosedDisc a 1 r, u z ≤ (C : EReal) := by
    rwa [affineClosedDisc_one]
  exact (le_circleMean_iff a 1 hr.le C hC').mpr (hu.submean a 1 r hr hD' C hC')

/-- The actual source complex-line criterion, using nonzero affine complex
parameterizations and the actual connected components of their preimages. -/
def LineCriterion (u : E → EReal) (U : Set E) : Prop :=
  ∀ b v : E, v ≠ 0 → ∀ z ∈ (fun t : ℂ ↦ b + t • v) ⁻¹' U,
    SubharmonicOn (fun t : ℂ ↦ u (b + t • v))
        (connectedComponentIn ((fun t : ℂ ↦ b + t • v) ⁻¹' U) z) ∨
      EqOn (fun t : ℂ ↦ u (b + t • v)) (fun _ ↦ ⊥)
        (connectedComponentIn ((fun t : ℂ ↦ b + t • v) ⁻¹' U) z)

/-- Source PSH with its line criterion, upper semicontinuity, never-top values,
and non-bottom clause. In dimension zero the line criterion is vacuous. -/
structure LinePSHOn (u : E → EReal) (U : Set E) : Prop where
  ne_top : ∀ z ∈ U, u z ≠ ⊤
  upperSemicontinuousOn : UpperSemicontinuousOn u U
  nontrivial : ∃ z ∈ U, u z ≠ ⊥
  lines : LineCriterion u U

/-- The existing genuine disc criterion with the source's non-bottom clause. -/
structure PSHOn (u : E → EReal) (U : Set E) : Prop where
  disc : SGPT.Foundations.Analysis.DiscPshOn u U
  nontrivial : ∃ z ∈ U, u z ≠ ⊥

/-- Every actual affine-line component has the source subharmonic-or-bottom
dichotomy, by reuse of genuine extended-real affine pullback and restriction. -/
theorem linePSHOn_of_pshOn {u : E → EReal} {U : Set E} (hu : PSHOn u U) :
    LinePSHOn u U := by
  classical
  refine ⟨hu.disc.ne_top, hu.disc.upperSemicontinuousOn, hu.nontrivial, ?_⟩
  intro b v _ z _
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hline : SGPT.Foundations.Analysis.DiscPshOn (fun t : ℂ ↦ u (b + t • v))
      ((fun t : ℂ ↦ b + t • v) ⁻¹' U) := by
    simpa [L] using hu.disc.comp_affine L b
  have hcomponent := hline.mono (connectedComponentIn_subset _ z)
  by_cases hn : ∃ t ∈ connectedComponentIn ((fun t : ℂ ↦ b + t • v) ⁻¹' U) z,
      u (b + t • v) ≠ ⊥
  · exact Or.inl (subharmonicOn_of_disc hcomponent hn)
  · right
    intro t ht
    by_contra h
    exact hn ⟨t, ht, h⟩

/-- The actual source line conditions imply every genuine affine-disc
inequality, since its connected parameter ball lies in an actual component. -/
theorem pshOn_of_linePSHOn {u : E → EReal} {U : Set E} (hu : LinePSHOn u U) :
    PSHOn u U := by
  refine ⟨⟨hu.ne_top, hu.upperSemicontinuousOn, ?_⟩, hu.nontrivial⟩
  intro x v r hr hD C hC
  by_cases hv : v = 0
  · subst v
    simpa only [SGPT.Foundations.Analysis.circleDeficit, smul_zero, add_zero] using
      (SGPT.Foundations.Analysis.circleDeficit_const (u x) x (0 : E) r C).le
  · let Ω : Set ℂ := (fun t : ℂ ↦ x + t • v) ⁻¹' U
    have hzero : (0 : ℂ) ∈ Ω := by
      simpa [Ω] using hD (SGPT.Foundations.Analysis.center_mem_affineClosedDisc x v hr.le)
    have hball : closedBall (0 : ℂ) r ⊆ Ω := by
      intro z hz
      exact hD ⟨z, hz, rfl⟩
    have hcomponent : closedBall (0 : ℂ) r ⊆ connectedComponentIn Ω 0 :=
      isPreconnected_closedBall.subset_connectedComponentIn (mem_closedBall_self hr.le) hball
    rcases hu.lines x v hv 0 hzero with hs | hb
    · have hbound : ∀ z ∈ closedBall (0 : ℂ) r, u (x + z • v) ≤ (C : EReal) := by
        intro z hz
        exact hC _ ⟨z, hz, rfl⟩
      have hunit : ∀ z ∈ SGPT.Foundations.Analysis.affineClosedDisc (0 : ℂ) 1 r,
          u (x + z • v) ≤ (C : EReal) := by
        rwa [affineClosedDisc_one]
      have hmean := hs.submean 0 r hr hcomponent C hbound
      have hdef := (le_circleMean_iff (u := fun z : ℂ ↦ u (x + z • v))
        0 1 hr.le C hunit).mp hmean
      simpa only [SGPT.Foundations.Analysis.circleDeficit, smul_eq_mul, mul_one,
        zero_add, zero_smul, add_zero] using hdef
    · have hbot : u x = ⊥ := by
        simpa using hb (mem_connectedComponentIn hzero)
      rw [hbot, EReal.coe_sub_bot, EReal.toENNReal_top,
        ENNReal.mul_top angularMeasure_ne_zero]
      exact le_top

/-- Exact source-to-main-branch bridge; the non-bottom point is essential. -/
theorem linePSHOn_iff_pshOn (u : E → EReal) (U : Set E) :
    LinePSHOn u U ↔ PSHOn u U := ⟨pshOn_of_linePSHOn, linePSHOn_of_pshOn⟩

/-- Every finite real constant satisfies the genuine source PSH criterion. -/
theorem pshOn_real_const (a : ℝ) {U : Set E} (hU : U.Nonempty) :
    PSHOn (fun _ : E ↦ (a : EReal)) U := by
  obtain ⟨z, hz⟩ := hU
  exact ⟨SGPT.Foundations.Analysis.discPshOn_const (a : EReal) (EReal.coe_ne_top a) U,
    ⟨z, hz, EReal.coe_ne_bot a⟩⟩

/-- The source zero-dimensional condition is exactly finite real constancy
on the one-point complex vector space; negative infinity is excluded. -/
theorem pshOn_univ_iff_real_const [Subsingleton E] [Nonempty E] (u : E → EReal) :
    PSHOn u univ ↔ ∃ a : ℝ, u = fun _ ↦ (a : EReal) := by
  constructor
  · intro hu
    obtain ⟨z, _, hz⟩ := hu.nontrivial
    refine ⟨(u z).toReal, ?_⟩
    funext t
    rw [Subsingleton.elim t z]
    exact (EReal.coe_toReal (hu.disc.ne_top z (mem_univ z)) hz).symm
  · rintro ⟨a, rfl⟩
    exact pshOn_real_const a univ_nonempty

/-- The actual function subtype in the zero-dimensional source example is
canonically equivalent to the real numbers by evaluation and constants. -/
noncomputable def zeroDimensionalEquiv :
    {u : (Fin 0 → ℂ) → EReal // PSHOn u univ} ≃ ℝ where
  toFun u := (u.1 0).toReal
  invFun a := ⟨fun _ ↦ (a : EReal), pshOn_real_const a univ_nonempty⟩
  left_inv u := by
    obtain ⟨a, ha⟩ := (pshOn_univ_iff_real_const u.1).mp u.2
    apply Subtype.ext
    funext t
    simp [ha]
  right_inv a := by simp

end SGPT.PSH
