/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MollifierPeanoHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MaximalPsh

/-!
# Maximal plurisubharmonic functions have degenerate second-order expansions

If `u` is maximal on `Ω` and has a second-order (Peano) expansion at `z₀ ∈ Ω` whose Levi form
is positive definite, then the pluriharmonic part of the Taylor polynomial, raised by a small
constant, is a competitor contradicting maximality: it lies below `u` on a small sphere
around `z₀` but strictly above `u` at `z₀`.

Source: Błocki, *The complex Monge–Ampère operator in pluripotential theory*, lecture notes,
proof of Theorem 2.3.1.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

theorem coe_max_eq_max_coe (a b : ℝ) : ((max a b : ℝ) : EReal) = max (a : EReal) (b : EReal) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
  · rw [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]

/-- **No positive definite second-order expansion at a point of maximality.** -/
theorem false_of_isMaximalPshOn_of_hasPeanoExpansion
    {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hmax : BedfordTaylor.IsMaximalPshOn Ω u)
    {z₀ : ComplexModel n} (hz₀ : z₀ ∈ Ω)
    {L : ComplexModel n →L[ℝ] ℝ} {A : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ}
    (hsymm : ∀ v w, A v w = A w v) (hpeano : HasPeanoExpansionAt u z₀ L A)
    {c : ℝ} (hc : 0 < c)
    (hlevi : ∀ v : ComplexModel n,
      c * ‖v‖ ^ 2 ≤ (A v v + A (Complex.I • v) (Complex.I • v)) / 4) : False := by
  classical
  set J : ComplexModel n →L[ℝ] ComplexModel n :=
    (Complex.I • ContinuousLinearMap.id ℂ (ComplexModel n)).restrictScalars ℝ with hJdef
  have hJ : ∀ z : ComplexModel n, J z = Complex.I • z := fun z ↦ rfl
  set A' : ComplexModel n →L[ℝ] ComplexModel n →L[ℝ] ℝ :=
    (2⁻¹ : ℝ) • (A - A.bilinearComp J J) with hA'def
  have hA'apply : ∀ v w : ComplexModel n,
      A' v w = (A v w - A (Complex.I • v) (Complex.I • w)) / 2 := by
    intro v w
    simp only [hA'def, _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.bilinearComp_apply, smul_eq_mul, hJ]
    ring
  have hA'symm : ∀ v w : ComplexModel n, A' v w = A' w v := by
    intro v w
    rw [hA'apply, hA'apply, hsymm v w, hsymm (Complex.I • v) (Complex.I • w)]
  -- the Peano estimate with `ε = c / 2`
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff_ball.mp (hpeano (c / 2) (by positivity))
  obtain ⟨r0, hr0, hr0Ω⟩ := Metric.isOpen_iff.mp Ω.isOpen z₀ hz₀
  set r := min (ρ / 2) (r0 / 2) with hrdef
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hballΩ : closedBall z₀ r ⊆ (Ω : Set (ComplexModel n)) := by
    refine subset_trans (closedBall_subset_ball ?_) hr0Ω
    calc r ≤ r0 / 2 := min_le_right _ _
      _ < r0 := by linarith
  set ε := c * r ^ 2 / 4 with hεdef
  have hε : 0 < ε := by positivity
  set p : ComplexModel n → ℝ :=
    fun z ↦ (u z₀ + L (z - z₀) + A' (z - z₀) (z - z₀) / 2) + ε with hpdef
  -- `p` is pluriharmonic, in particular plurisubharmonic
  have hlinsmooth : ContDiff ℝ 2 (fun z : ComplexModel n ↦ z - z₀) :=
    contDiff_id.sub contDiff_const
  have hpsmooth : ContDiff ℝ 2 p := by
    have hquad : ContDiff ℝ 2 fun z : ComplexModel n ↦ A' (z - z₀) (z - z₀) :=
      ContDiff.clm_apply (A'.contDiff.comp hlinsmooth) hlinsmooth
    have hlin : ContDiff ℝ 2 fun z : ComplexModel n ↦ L (z - z₀) :=
      L.contDiff.comp hlinsmooth
    exact ((contDiff_const.add hlin).add (hquad.div_const 2)).add contDiff_const
  have hphess : ∀ x v w : ComplexModel n, realHessian p x v w = A' v w := fun x v w ↦
    realHessian_quadratic hA'symm x v w
  have hplevi : ∀ (x : ComplexModel n) (v : ComplexModel n), leviForm p x v = 0 := by
    intro x v
    have hII : Complex.I • (Complex.I • v) = -v := by
      rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    have h1 : A' v v = (A v v - A (Complex.I • v) (Complex.I • v)) / 2 := hA'apply v v
    have h2 : A' (Complex.I • v) (Complex.I • v)
        = (A (Complex.I • v) (Complex.I • v) - A (-v) (-v)) / 2 := by
      rw [hA'apply, hII]
    have h3 : A (-v) (-v) = A v v := by simp
    rw [leviForm, hphess, hphess, h1, h2, h3]
    ring
  have hppsh : PlurisubharmonicOn (fun z ↦ (p z : EReal)) (Ω : Set (ComplexModel n)) :=
    plurisubharmonicOn_of_levi_nonneg hpsmooth Ω.isOpen fun x _ v ↦ (hplevi x v).ge
  -- the key estimate
  have hkey : ∀ h : ComplexModel n, ‖h‖ < ρ →
      c / 2 * ‖h‖ ^ 2 - ε ≤ u (z₀ + h) - p (z₀ + h) := by
    intro h hh
    have hpe := hρball h (by simpa [mem_ball, dist_zero_right] using hh)
    have hplus : p (z₀ + h) = (u z₀ + L h + A' h h / 2) + ε := by
      simp only [hpdef, add_sub_cancel_left]
    have hlev := hlevi h
    have hA'hh : A' h h = (A h h - A (Complex.I • h) (Complex.I • h)) / 2 := hA'apply h h
    have hbound := abs_le.mp hpe
    rw [hplus, hA'hh]
    linarith [hbound.1, hbound.2, hlev]
  -- `p` is strictly below `u` on the outer annulus
  have hannulus : ∀ z : ComplexModel n, 3 / 4 * r ≤ ‖z - z₀‖ → ‖z - z₀‖ ≤ r → p z < u z := by
    intro z h1 h2
    have hzr : ‖z - z₀‖ < ρ := lt_of_le_of_lt h2 hrρ
    have hz : z₀ + (z - z₀) = z := by abel
    have hk := hkey (z - z₀) hzr
    rw [hz] at hk
    have hsq : (3 / 4 * r) ^ 2 ≤ ‖z - z₀‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have : c / 2 * ((3 / 4 * r) ^ 2) - ε ≤ c / 2 * ‖z - z₀‖ ^ 2 - ε := by
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ c / 2)
      linarith
    have hpos : 0 < c / 2 * ((3 / 4 * r) ^ 2) - ε := by
      rw [hεdef]
      nlinarith [hc, hr, sq_nonneg r]
    linarith
  -- the competitor
  set comp : ComplexModel n → ℝ := fun z ↦ if z ∈ ball z₀ r then max (u z) (p z) else u z
    with hcompdef
  have hcompeq : ∀ z : ComplexModel n, 3 / 4 * r < ‖z - z₀‖ → comp z = u z := by
    intro z hz
    by_cases hzb : z ∈ ball z₀ r
    · have h2 : ‖z - z₀‖ ≤ r := by
        have := mem_ball.mp hzb
        rw [dist_eq_norm] at this
        exact this.le
      have := hannulus z hz.le h2
      simp only [hcompdef, ite_eq_left hzb]
      exact max_eq_left this.le
    · simp only [hcompdef, ite_eq_right hzb]
  have hcomppsh : PlurisubharmonicOn (fun z ↦ (comp z : EReal)) (Ω : Set (ComplexModel n)) := by
    intro y hy
    by_cases hyr : y ∈ ball z₀ r
    · have hmaxpsh : PlurisubharmonicAt
          (fun z ↦ max ((u z : EReal)) ((p z : EReal))) y :=
        (hmax.1 y hy).max (hppsh y hy)
      refine hmaxpsh.congr ?_
      filter_upwards [isOpen_ball.mem_nhds hyr] with z hz
      rw [hcompdef]
      simp only [ite_eq_left hz]
      exact (coe_max_eq_max_coe (u z) (p z)).symm
    · have hyfar : 3 / 4 * r < ‖y - z₀‖ := by
        have : r ≤ ‖y - z₀‖ := by
          by_contra hcon
          push Not at hcon
          exact hyr (mem_ball.mpr (by rwa [dist_eq_norm]))
        nlinarith [hr]
      have hopen : IsOpen {z : ComplexModel n | 3 / 4 * r < ‖z - z₀‖} :=
        isOpen_lt continuous_const (by fun_prop)
      refine (hmax.1 y hy).congr ?_
      filter_upwards [hopen.mem_nhds hyfar] with z hz
      exact congrArg (fun t : ℝ ↦ (t : EReal)) (hcompeq z hz).symm
  -- maximality forces `comp ≤ u`, contradicting `comp z₀ ≥ p z₀ > u z₀`
  have houtside : ∀ z ∈ (Ω : Set (ComplexModel n)) \ closedBall z₀ r, comp z ≤ u z := by
    intro z hz
    have hzb : z ∉ ball z₀ r := fun h ↦ hz.2 (ball_subset_closedBall h)
    simp only [hcompdef, ite_eq_right hzb]
    exact le_rfl
  have hle := hmax.2 comp hcomppsh (closedBall z₀ r) (isCompact_closedBall _ _) hballΩ
    houtside z₀ hz₀
  have hz₀ball : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hcompz₀ : comp z₀ = max (u z₀) (p z₀) := by
    simp only [hcompdef, ite_eq_left hz₀ball]
  have hpz₀ : p z₀ = u z₀ + ε := by
    simp only [hpdef, sub_self, map_zero]
    ring
  rw [hcompz₀, hpz₀] at hle
  linarith [le_max_right (u z₀) (u z₀ + ε), hε]

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
