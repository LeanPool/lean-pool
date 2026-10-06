/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.TestNorms
public import LeanPool.HighContrastHomogenization.Analytic.ConvexDomains
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# High-contrast homogenization: Consistency.AdmissibleTests

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The admissible-test family of the dual norms is not empty

This module checks the definition `IsLocalVecTest` of an admissible test field:
the class of smooth compactly supported vector fields on a domain over which the
two dual norms `negSobolevNorm` and `negOneNorm` of `e.physical.negative.norm`
take their suprema.  Were that check to fail — were the admissible tests of
`hsNormSq` (respectively `h1NormSq`) at most `1` to contain only the zero field,
or to be empty — then each of those two suprema would be `0` for a reason that
has nothing to do with the field `F` it measures, and every estimate written
with them, among them the Dirichlet estimate `e.random.dirichlet` and the
corrector estimate `e.random.corrector` of `t.random.homogenization`, would be
vacuous: satisfied by the absence of anything to estimate.  This module is a
consistency check of that definition and is not a result of the paper.

The dual norms `‖F‖_{H^{-s}(V)}` and `‖F‖_{H̲^{-1}(V)}` of
`e.physical.negative.norm` are suprema over the smooth compactly supported
fields on `V` whose normalized norm is at most `1`.  This module shows that this
failure does not occur: over any domain containing a ball, each of the two
families contains a **nonzero** field.

The witness is a Mathlib smooth bump supported in a ball inside the domain,
pointed along a fixed coordinate direction.  It is nonzero because the bump
equals `1` at its centre.  Its normalized norm is finite by the finiteness
statements for the normalized norms, so if it is nonzero it can be rescaled to
norm exactly `1` by the quadratic homogeneity, and if it is zero it already
satisfies the constraint.

The hypothesis `0 < d` is necessary and is not a convenience: for `d = 0` the
only field `Vec 0 → Vec 0` is the zero field, so the family really does contain
nothing else and every such supremum vanishes.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A nonzero local test on any nonempty open set -/

theorem exists_nonzero_isLocalVecTest {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    (hUball : ∃ (c : Vec d) (ε : ℝ), 0 < ε ∧ Metric.ball c ε ⊆ U) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest U ψ ∧ ψ ≠ 0 := by
  obtain ⟨c₀, ε, hε, hball⟩ := hUball
  let f : ContDiffBump c₀ :=
    { rIn := ε / 4
      rOut := ε / 2
      rIn_pos := by linarith only [hε]
      rIn_lt_rOut := by linarith only [hε] }
  set i₀ : Fin d := ⟨0, hd⟩
  refine ⟨fun x => (f x) • (basisVec i₀ : Vec d), ?_, ?_⟩
  · have hsupp : Function.support (fun x => (f x) • (basisVec i₀ : Vec d))
        ⊆ Function.support (f : Vec d → ℝ) := by
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      exact hx (by rw [h, zero_smul])
    have htsupp : tsupport (fun x => (f x) • (basisVec i₀ : Vec d))
        ⊆ tsupport (f : Vec d → ℝ) := closure_mono hsupp
    have hrOut : f.rOut = ε / 2 := rfl
    refine ⟨f.contDiff.smul contDiff_const, ?_, ?_⟩
    · exact IsCompact.of_isClosed_subset f.hasCompactSupport isClosed_closure htsupp
    · refine htsupp.trans ?_
      rw [f.tsupport_eq, hrOut]
      refine subset_trans ?_ hball
      exact Metric.closedBall_subset_ball (by linarith only [hε])
  · intro hzero
    have hval : (f c₀) • (basisVec i₀ : Vec d) = 0 := by
      have := congrFun hzero c₀
      simpa using this
    have hf1 : f c₀ = 1 :=
      f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)
    rw [hf1, one_smul] at hval
    have : (basisVec i₀ : Vec d) i₀ = 0 := by rw [hval]; rfl
    rw [basisVec_apply] at this
    simp at this

/-! ## The headline statements -/

/-- The rescaling identity used to normalize a finite nonzero norm to `1`. -/
theorem ofReal_one_div_toReal_mul_self {M : ℝ≥0∞} (h0 : M ≠ 0) (hT : M ≠ ⊤) :
    ENNReal.ofReal (1 / M.toReal) * M = 1 := by
  have hpos : 0 < M.toReal := ENNReal.toReal_pos h0 hT
  have h1 : ENNReal.ofReal (1 / M.toReal) * ENNReal.ofReal M.toReal = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div,
      inv_mul_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one]
  rwa [ENNReal.ofReal_toReal hT] at h1

/-- **The admissible-test family of the `H^{-s}` dual norm contains a nonzero
field.**  Only openness, boundedness and nonemptiness of `U` are used; `0 < d`
is necessary, since `Vec 0 → Vec 0` has `0` as its only element. -/
theorem exists_nonzero_admissible_test_of_ball {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    (hUm : MeasurableSet U) (hUb : IsBoundedDomain U)
    (hUball : ∃ (c : Vec d) (ε : ℝ), 0 < ε ∧ Metric.ball c ε ⊆ U)
    {s : ℝ} (hs0 : 0 ≤ (d : ℝ) + 2 * s) (hs1 : s < 1) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest U ψ ∧ ψ ≠ 0 ∧ hsNormSq U s ψ ≤ 1 := by
  have hV0 : volume U ≠ 0 := by
    obtain ⟨c, ε, hε, hsub⟩ := hUball
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub))
    rw [Real.volume_pi_ball c hε]
    exact ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨ψ₀, hψ₀, hne₀⟩ := exists_nonzero_isLocalVecTest hd hUball
  have hM : hsNormSq U s ψ₀ ≠ ⊤ := hsNormSq_ne_top hUm hUb hV0 hs0 hs1 hψ₀
  rcases eq_or_ne (hsNormSq U s ψ₀) 0 with hM0 | hM0
  · exact ⟨ψ₀, hψ₀, hne₀, by rw [hM0]; exact zero_le_one⟩
  · have hMpos : 0 < (hsNormSq U s ψ₀).toReal := ENNReal.toReal_pos hM0 hM
    set c : ℝ := Real.sqrt (1 / (hsNormSq U s ψ₀).toReal) with hcdef
    have hcpos : 0 < c := by
      rw [hcdef]
      exact Real.sqrt_pos.mpr (by positivity)
    have hcsq : c ^ 2 = 1 / (hsNormSq U s ψ₀).toReal := by
      rw [hcdef]; exact Real.sq_sqrt (by positivity)
    refine ⟨fun x => c • ψ₀ x, ?_, ?_, ?_⟩
    · have hsupp : Function.support (fun x => c • ψ₀ x) ⊆ Function.support ψ₀ := by
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h
        exact hx (by rw [h, smul_zero])
      have htsupp : tsupport (fun x => c • ψ₀ x) ⊆ tsupport ψ₀ := closure_mono hsupp
      exact ⟨ContDiff.const_smul c hψ₀.contDiff,
        IsCompact.of_isClosed_subset hψ₀.hasCompactSupport isClosed_closure htsupp,
        htsupp.trans hψ₀.tsupport_subset⟩
    · intro hzero
      refine hne₀ (funext fun x => ?_)
      have := congrFun hzero x
      simp only [Pi.zero_apply] at this
      have hc : c ≠ 0 := ne_of_gt hcpos
      have := congrArg (fun v : Vec d => c⁻¹ • v) this
      simpa [smul_smul, inv_mul_cancel₀ hc] using this
    · rw [hsNormSq_smul, hcsq]
      exact le_of_eq (ofReal_one_div_toReal_mul_self hM0 hM)

/-- The same statement on a bounded open convex domain. -/
theorem exists_nonzero_admissible_test {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest U ψ ∧ ψ ≠ 0 ∧ hsNormSq U s ψ ≤ 1 := by
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU.isOpen c₀ hc₀
  refine exists_nonzero_admissible_test_of_ball hd hU.isOpen.measurableSet
    hU.isBoundedDomain ⟨c₀, ε, hε, hball⟩ ?_ ?_
  · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [h1, hs.1]
  · linarith only [hs.2]

/-- **The admissible-test family of the `H̲^{-1}` dual norm contains a nonzero
field.**  Only openness, boundedness and nonemptiness of `U` are used, together
with `0 < d`. -/
theorem exists_nonzero_admissible_test_h1_of_ball {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    (hUb : IsBoundedDomain U)
    (hUball : ∃ (c : Vec d) (ε : ℝ), 0 < ε ∧ Metric.ball c ε ⊆ U) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest U ψ ∧ ψ ≠ 0 ∧ h1NormSq U ψ ≤ 1 := by
  have hone : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hV0 : volume U ≠ 0 := by
    obtain ⟨c, ε, hε, hsub⟩ := hUball
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsub))
    rw [Real.volume_pi_ball c hε]
    exact ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨ψ₀, hψ₀, hne₀⟩ := exists_nonzero_isLocalVecTest hd hUball
  have hM : h1NormSq U ψ₀ ≠ ⊤ := h1NormSq_ne_top hUb hV0 hψ₀
  have hdiff : Differentiable ℝ ψ₀ := hψ₀.contDiff.differentiable hone
  rcases eq_or_ne (h1NormSq U ψ₀) 0 with hM0 | hM0
  · exact ⟨ψ₀, hψ₀, hne₀, by rw [hM0]; exact zero_le_one⟩
  · have hMpos : 0 < (h1NormSq U ψ₀).toReal := ENNReal.toReal_pos hM0 hM
    set c : ℝ := Real.sqrt (1 / (h1NormSq U ψ₀).toReal) with hcdef
    have hcpos : 0 < c := by
      rw [hcdef]
      exact Real.sqrt_pos.mpr (by positivity)
    have hcsq : c ^ 2 = 1 / (h1NormSq U ψ₀).toReal := by
      rw [hcdef]; exact Real.sq_sqrt (by positivity)
    refine ⟨fun x => c • ψ₀ x, ?_, ?_, ?_⟩
    · have hsupp : Function.support (fun x => c • ψ₀ x) ⊆ Function.support ψ₀ := by
        intro x hx
        simp only [Function.mem_support] at hx ⊢
        intro h
        exact hx (by rw [h, smul_zero])
      have htsupp : tsupport (fun x => c • ψ₀ x) ⊆ tsupport ψ₀ := closure_mono hsupp
      exact ⟨ContDiff.const_smul c hψ₀.contDiff,
        IsCompact.of_isClosed_subset hψ₀.hasCompactSupport isClosed_closure htsupp,
        htsupp.trans hψ₀.tsupport_subset⟩
    · intro hzero
      refine hne₀ (funext fun x => ?_)
      have := congrFun hzero x
      simp only [Pi.zero_apply] at this
      have hc : c ≠ 0 := ne_of_gt hcpos
      have := congrArg (fun v : Vec d => c⁻¹ • v) this
      simpa [smul_smul, inv_mul_cancel₀ hc] using this
    · rw [h1NormSq_smul U c hdiff, hcsq]
      exact le_of_eq (ofReal_one_div_toReal_mul_self hM0 hM)

/-- The same statement on a bounded open convex domain. -/
theorem exists_nonzero_admissible_test_h1 {d : ℕ} (hd : 0 < d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    ∃ ψ : Vec d → Vec d, IsLocalVecTest U ψ ∧ ψ ≠ 0 ∧ h1NormSq U ψ ≤ 1 := by
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU.isOpen c₀ hc₀
  exact exists_nonzero_admissible_test_h1_of_ball hd hU.isBoundedDomain
    ⟨c₀, ε, hε, hball⟩

end

end HighContrast
end HCPolySupport
