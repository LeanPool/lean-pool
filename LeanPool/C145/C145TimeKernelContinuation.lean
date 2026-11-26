/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DelayKernelTransfer
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Finite first/delay time kernels are determined at every nonnegative delay by
one positive observed interval/square. The proof uses finite resonance-safe
sector formulas and the real analytic identity theorem separately in each
coordinate. It needs no nonlinear response at later times and no spectral,
cyclicity, graph, positivity, or nonresonance assumptions.
-/

@[expose] public section

noncomputable section
namespace C145.TimeKernelContinuation
open MeasureTheory Set Filter
open scoped BigOperators Topology
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid
  NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace
  UniformSpace.toTopologicalSpace

/-- Resonance-safe primitive of `exp (q*x)`, with its resonant value explicit. -/
def expPrimitive (q x : ℝ) : ℝ :=
  if q = 0 then x else (Real.exp (q * x) - 1) / q

theorem integral_exp_eq_expPrimitive (q u : ℝ) :
    (∫ a in (0 : ℝ)..u, Real.exp (q * a)) = expPrimitive q u := by
  by_cases hq : q = 0
  · simp [expPrimitive, hq]
  · rw [expPrimitive, ite_eq_right hq]
    have hSubstitution := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.exp) (a := (0 : ℝ)) (b := u) q
    simp only [mul_zero, _root_.integral_exp, Real.exp_zero] at hSubstitution
    apply (eq_div_iff hq).2
    simpa only [mul_comm] using hSubstitution

/-- Exact scalar formula, valid also at additive resonance and on the diagonal. -/
theorem scalarDelay_formula (α β γ r₁ r₂ : ℝ) :
    C145.DelayKernel.scalarDelay α β γ r₁ r₂ =
      Real.exp (-α * r₁ - β * r₂) *
        expPrimitive (α + β - γ) (min r₁ r₂) := by
  rw [← integral_exp_eq_expPrimitive]
  unfold C145.DelayKernel.scalarDelay
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro a ha
  simp only [← Real.exp_add]
  congr 1
  ring

/-- The finite formula on either ordered sector, extended to the entire plane.
`first = true` is the sector r₁ ≤ r₂; `false` is r₂ ≤ r₁. -/
def sectorKernel {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (first : Bool) (r₁ r₂ : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    C145PhysicalFrame.T Q (C145.Pulse.modalOverlap Q b) i j k *
      (Real.exp (-rates i * r₁ - rates j * r₂) *
        expPrimitive (rates i + rates j - rates k) (if first then r₁ else r₂))

theorem delayKernel_eq_sectorKernel {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (first : Bool) (r₁ r₂ : ℝ)
    (hsector : if first then r₁ ≤ r₂ else r₂ ≤ r₁) :
    C145.DelayKernel.delayKernel Q rates b r₁ r₂ = sectorKernel Q rates b first r₁ r₂ := by
  rw [C145.DelayKernel.delayKernel_expansion]
  simp_rw [scalarDelay_formula]
  cases first
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsector ⊢
    simp only [sectorKernel, Bool.false_eq_true, ↓reduceIte, min_eq_right hsector]
  · simp only [↓reduceIte] at hsector ⊢
    simp only [sectorKernel, ↓reduceIte, min_eq_left hsector]

theorem expPrimitive_analytic {q : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun y => expPrimitive q (f y)) x := by
  by_cases hq : q = 0
  · simpa only [expPrimitive, ite_eq_left hq] using hf
  · simp only [expPrimitive, ite_eq_right hq]
    exact ((analyticAt_const.mul hf).rexp.sub analyticAt_const).div
      analyticAt_const hq

theorem firstKernel_analytic {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) :
    AnalyticOnNhd ℝ (C145.DelayKernel.firstKernel Q rates b) univ := by
  intro x hx
  change AnalyticAt ℝ (fun t => C145.DelayKernel.firstKernel Q rates b t) x
  simp_rw [C145.DelayKernel.firstKernel_expansion]
  fun_prop

theorem sectorKernel_analytic_first {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (first : Bool) (r₂ : ℝ) :
    AnalyticOnNhd ℝ (fun r₁ => sectorKernel Q rates b first r₁ r₂) univ := by
  intro x hx
  unfold sectorKernel
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  apply Finset.analyticAt_fun_sum
  intro k hk
  apply AnalyticAt.mul analyticAt_const
  apply AnalyticAt.mul
  · fun_prop
  · apply expPrimitive_analytic
    cases first
    · exact analyticAt_const
    · exact analyticAt_id

theorem sectorKernel_analytic_second {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (rates b : Fin (n + 1) → ℝ) (first : Bool) (r₁ : ℝ) :
    AnalyticOnNhd ℝ (fun r₂ => sectorKernel Q rates b first r₁ r₂) univ := by
  intro x hx
  unfold sectorKernel
  apply Finset.analyticAt_fun_sum
  intro i hi
  apply Finset.analyticAt_fun_sum
  intro j hj
  apply Finset.analyticAt_fun_sum
  intro k hk
  apply AnalyticAt.mul analyticAt_const
  apply AnalyticAt.mul
  · fun_prop
  · apply expPrimitive_analytic
    cases first
    · exact analyticAt_id
    · exact analyticAt_const

/-- One-variable identity theorem from any nonempty open interval. -/
theorem analytic_eq_of_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : AnalyticOnNhd ℝ f univ) (hg : AnalyticOnNhd ℝ g univ)
    (heq : EqOn f g (Ioo a b)) : f = g := by
  apply hf.eq_of_eventuallyEq hg (z₀ := (a + b) / 2)
  have ha : a < (a + b) / 2 := by linarith
  have hb : (a + b) / 2 < b := by linarith
  filter_upwards [Ioo_mem_nhds ha hb] with x hx
  exact heq hx

/-- Two successive one-variable identity theorems, with only a rectangle of data. -/
theorem separately_analytic_eq_of_rectangle {f g : ℝ → ℝ → ℝ}
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hf₁ : ∀ y, AnalyticOnNhd ℝ (fun x => f x y) univ)
    (hg₁ : ∀ y, AnalyticOnNhd ℝ (fun x => g x y) univ)
    (hf₂ : ∀ x, AnalyticOnNhd ℝ (f x) univ)
    (hg₂ : ∀ x, AnalyticOnNhd ℝ (g x) univ)
    (heq : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d, f x y = g x y) :
    ∀ x y, f x y = g x y := by
  have hstrip : ∀ y ∈ Ioo c d, ∀ x, f x y = g x y := by
    intro y hy x
    exact congrFun (analytic_eq_of_Ioo hab (hf₁ y) (hg₁ y) (fun z hz => heq z hz y hy)) x
  intro x y
  exact congrFun (analytic_eq_of_Ioo hcd (hf₂ x) (hg₂ x) (fun z hz => hstrip z hz x)) y

/-- First-kernel continuation needs no common modal indexing or physical premise. -/
theorem firstKernel_eq_of_observed_interval {m n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q₀ : Fin (m + 1) → Fin (m + 1) → ℝ) (rates₀ b₀ : Fin (m + 1) → ℝ)
    (Q₁ : Fin (n + 1) → Fin (n + 1) → ℝ) (rates₁ b₁ : Fin (n + 1) → ℝ)
    (heq : ∀ r ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.firstKernel Q₀ rates₀ b₀ r =
        C145.DelayKernel.firstKernel Q₁ rates₁ b₁ r) :
    ∀ r : ℝ, C145.DelayKernel.firstKernel Q₀ rates₀ b₀ r =
      C145.DelayKernel.firstKernel Q₁ rates₁ b₁ r := by
  intro r
  exact congrFun (analytic_eq_of_Ioo hT (firstKernel_analytic Q₀ rates₀ b₀)
    (firstKernel_analytic Q₁ rates₁ b₁) (fun x hx => heq x ⟨hx.1.le, hx.2.le⟩)) r

/-- Continue each ordered sector from an interior rectangle of the observed square. -/
theorem sectorKernel_eq_of_observed_square {m n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q₀ : Fin (m + 1) → Fin (m + 1) → ℝ) (rates₀ b₀ : Fin (m + 1) → ℝ)
    (Q₁ : Fin (n + 1) → Fin (n + 1) → ℝ) (rates₁ b₁ : Fin (n + 1) → ℝ)
    (heq : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.delayKernel Q₀ rates₀ b₀ r s =
        C145.DelayKernel.delayKernel Q₁ rates₁ b₁ r s)
    (first : Bool) :
    ∀ r s : ℝ, sectorKernel Q₀ rates₀ b₀ first r s =
      sectorKernel Q₁ rates₁ b₁ first r s := by
  let a := if first then T / 8 else T / 2
  let b := if first then T / 4 else 3 * T / 4
  let c := if first then T / 2 else T / 8
  let d := if first then 3 * T / 4 else T / 4
  have hab : a < b := by cases first <;> dsimp [a, b] <;> linarith
  have hcd : c < d := by cases first <;> dsimp [c, d] <;> linarith
  apply separately_analytic_eq_of_rectangle hab hcd
    (sectorKernel_analytic_first Q₀ rates₀ b₀ first)
    (sectorKernel_analytic_first Q₁ rates₁ b₁ first)
    (sectorKernel_analytic_second Q₀ rates₀ b₀ first)
    (sectorKernel_analytic_second Q₁ rates₁ b₁ first)
  intro r hr s hs
  have hrT : r ∈ Icc (0 : ℝ) T := by
    cases first <;> dsimp [a, b] at hr <;> constructor <;> linarith [hr.1, hr.2]
  have hsT : s ∈ Icc (0 : ℝ) T := by
    cases first <;> dsimp [c, d] at hs <;> constructor <;> linarith [hs.1, hs.2]
  have hsector : if first then r ≤ s else s ≤ r := by
    cases first <;> dsimp [a, b, c, d] at hr hs ⊢ <;> linarith [hr.1, hr.2, hs.1, hs.2]
  rw [← delayKernel_eq_sectorKernel Q₀ rates₀ b₀ first r s hsector,
    ← delayKernel_eq_sectorKernel Q₁ rates₁ b₁ first r s hsector]
  exact heq r hrT s hsT

/-- Both sectors include their diagonal, so their exact formulas also cover
endpoints; no extra response or boundary-data assumption is needed. -/
theorem delayKernel_eq_of_observed_square {m n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q₀ : Fin (m + 1) → Fin (m + 1) → ℝ) (rates₀ b₀ : Fin (m + 1) → ℝ)
    (Q₁ : Fin (n + 1) → Fin (n + 1) → ℝ) (rates₁ b₁ : Fin (n + 1) → ℝ)
    (heq : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.delayKernel Q₀ rates₀ b₀ r s =
        C145.DelayKernel.delayKernel Q₁ rates₁ b₁ r s) :
    ∀ r s : ℝ, C145.DelayKernel.delayKernel Q₀ rates₀ b₀ r s =
      C145.DelayKernel.delayKernel Q₁ rates₁ b₁ r s := by
  intro r s
  by_cases hrs : r ≤ s
  · rw [delayKernel_eq_sectorKernel Q₀ rates₀ b₀ true r s hrs,
      delayKernel_eq_sectorKernel Q₁ rates₁ b₁ true r s hrs]
    exact sectorKernel_eq_of_observed_square hT Q₀ rates₀ b₀ Q₁ rates₁ b₁ heq true r s
  · have hsr : s ≤ r := (lt_of_not_ge hrs).le
    rw [delayKernel_eq_sectorKernel Q₀ rates₀ b₀ false r s hsr,
      delayKernel_eq_sectorKernel Q₁ rates₁ b₁ false r s hsr]
    exact sectorKernel_eq_of_observed_square hT Q₀ rates₀ b₀ Q₁ rates₁ b₁ heq false r s

/-- The intended finite continuation checkpoint, for unrelated finite systems.
The hypotheses are precisely the observed first interval and delay square
identities; no later-time response, size bound, or spectral restriction enters. -/
theorem observed_time_kernels_determine_all_nonnegative_delays
    {m n : ℕ} {T : ℝ} (hT : 0 < T)
    (Q₀ : Fin (m + 1) → Fin (m + 1) → ℝ) (rates₀ b₀ : Fin (m + 1) → ℝ)
    (Q₁ : Fin (n + 1) → Fin (n + 1) → ℝ) (rates₁ b₁ : Fin (n + 1) → ℝ)
    (hfirst : ∀ r ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.firstKernel Q₀ rates₀ b₀ r =
        C145.DelayKernel.firstKernel Q₁ rates₁ b₁ r)
    (hdelay : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) T,
      C145.DelayKernel.delayKernel Q₀ rates₀ b₀ r s =
        C145.DelayKernel.delayKernel Q₁ rates₁ b₁ r s) :
    (∀ r : ℝ, 0 ≤ r → C145.DelayKernel.firstKernel Q₀ rates₀ b₀ r =
      C145.DelayKernel.firstKernel Q₁ rates₁ b₁ r) ∧
    (∀ r s : ℝ, 0 ≤ r → 0 ≤ s → C145.DelayKernel.delayKernel Q₀ rates₀ b₀ r s =
      C145.DelayKernel.delayKernel Q₁ rates₁ b₁ r s) := by
  exact ⟨fun r _ => firstKernel_eq_of_observed_interval hT Q₀ rates₀ b₀ Q₁ rates₁ b₁ hfirst r,
    fun r s _ _ => delayKernel_eq_of_observed_square hT Q₀ rates₀ b₀ Q₁ rates₁ b₁ hdelay r s⟩

end C145.TimeKernelContinuation

end
