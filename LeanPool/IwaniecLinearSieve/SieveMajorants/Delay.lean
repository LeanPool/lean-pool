/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.Definitions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.Chebyshev

/-!
# Linear delay equations with unit delay

For continuous `k y₀ : ℝ → ℝ`, `y = Delay.sol k y₀` (defined in `IwaniecLinearSieve.Definitions`)
is the continuous function with

* `y s = y₀ s` for `s ≤ 3`,
* `y s = y₀ 3 + ∫ x in 3..s, k x * y (x - 1)` for `s ≥ 3`,

so that `y' s = k s * y (s - 1)` for `s > 3`. This is the shape of the equations defining
Iwaniec's functions `𝔐`, `𝔚` in [I71, §3].

We also record a "first crossing" principle used for the comparison arguments of [I71, §3].
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace IwaniecLinearSieve

namespace Delay

variable {k y₀ : ℝ → ℝ}

theorem step_of_le {y : ℝ → ℝ} {s : ℝ} (hs : s ≤ 3) : step k y₀ y s = y₀ s := by
  simp [step, min_eq_left hs, max_eq_right hs]

theorem step_of_ge {y : ℝ → ℝ} {s : ℝ} (hs : 3 ≤ s) :
    step k y₀ y s = y₀ 3 + ∫ x in (3 : ℝ)..s, k x * y (x - 1) := by
  simp [step, min_eq_right hs, max_eq_left hs]

/-- `step` only looks one unit back. -/
theorem step_congr {y y' : ℝ → ℝ} {m : ℝ} (h : ∀ x ≤ m, y x = y' x) {s : ℝ} (hs : s ≤ m + 1) :
    step k y₀ y s = step k y₀ y' s := by
  rcases le_total s 3 with h3 | h3
  · rw [step_of_le h3, step_of_le h3]
  · rw [step_of_ge h3, step_of_ge h3]
    congr 1
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le h3] at hx
    rw [h (x - 1) (by linarith [hx.2])]

theorem iter_succ_eq (n : ℕ) {s : ℝ} (hs : s ≤ n + 3) :
    iter k y₀ (n + 1) s = iter k y₀ n s := by
  induction n generalizing s with
  | zero =>
    simp only [Nat.cast_zero, zero_add] at hs
    exact step_of_le hs
  | succ n ih =>
    change step k y₀ (iter k y₀ (n + 1)) s = step k y₀ (iter k y₀ n) s
    refine step_congr (m := n + 3) (fun x hx => ih hx) ?_
    push_cast at hs
    linarith

theorem iter_add_eq (n j : ℕ) {s : ℝ} (hs : s ≤ n + 3) :
    iter k y₀ (n + j) s = iter k y₀ n s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, iter_succ_eq _ (by push_cast; linarith), ih]

theorem iter_eq_of_le {m n : ℕ} (hmn : m ≤ n) {s : ℝ} (hs : s ≤ m + 3) :
    iter k y₀ n s = iter k y₀ m s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact iter_add_eq m j hs

theorem sol_eq_iter {n : ℕ} {s : ℝ} (hs : s ≤ n + 3) : sol k y₀ s = iter k y₀ n s := by
  unfold sol
  rcases le_total n ⌈s⌉₊ with h | h
  · exact iter_eq_of_le h hs
  · exact (iter_eq_of_le h (by linarith [Nat.le_ceil s])).symm

/-- `sol` is a fixed point of `step`. -/
theorem sol_eq_step (s : ℝ) : sol k y₀ s = step k y₀ (sol k y₀) s := by
  set n := ⌈s⌉₊
  have hn : s ≤ n := Nat.le_ceil s
  rw [sol_eq_iter (n := n + 1) (by push_cast; linarith)]
  change step k y₀ (iter k y₀ n) s = _
  exact step_congr (m := n + 3) (fun x hx => (sol_eq_iter hx).symm) (by linarith)

theorem sol_of_le {s : ℝ} (hs : s ≤ 3) : sol k y₀ s = y₀ s := by
  rw [sol_eq_step, step_of_le hs]

theorem sol_of_ge {s : ℝ} (hs : 3 ≤ s) :
    sol k y₀ s = y₀ 3 + ∫ x in (3 : ℝ)..s, k x * sol k y₀ (x - 1) := by
  rw [sol_eq_step, step_of_ge hs]

theorem continuous_step (hk : Continuous k) (hy₀ : Continuous y₀) {y : ℝ → ℝ}
    (hy : Continuous y) : Continuous (step k y₀ y) := by
  have hF : Continuous fun x => k x * y (x - 1) := hk.mul (hy.comp (continuous_sub_right 1))
  have hP : Continuous fun b => ∫ x in (3 : ℝ)..b, k x * y (x - 1) :=
    intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable a b) 3
  exact (hy₀.comp (continuous_id.min continuous_const)).add
    (hP.comp (continuous_id.max continuous_const))

theorem continuous_iter (hk : Continuous k) (hy₀ : Continuous y₀) (n : ℕ) :
    Continuous (iter k y₀ n) := by
  induction n with
  | zero => exact hy₀
  | succ n ih => exact continuous_step hk hy₀ ih

theorem continuous_sol (hk : Continuous k) (hy₀ : Continuous y₀) : Continuous (sol k y₀) := by
  rw [continuous_iff_continuousAt]
  intro s
  set n := ⌈s⌉₊
  have hn : s ≤ n := Nat.le_ceil s
  have hev : iter k y₀ n =ᶠ[𝓝 s] sol k y₀ := by
    filter_upwards [Iio_mem_nhds (show s < n + 3 by linarith)] with x hx
    exact (sol_eq_iter hx.le).symm
  exact ((continuous_iter hk hy₀ n).continuousAt).congr hev

/-- For `s ≥ 3`, `sol` agrees with `y₀ 3 + ∫_3^s k x y(x-1) dx`, a function with derivative
`k s * y (s - 1)` everywhere. -/
theorem hasDerivAt_primitive (hk : Continuous k) (hy₀ : Continuous y₀) (s : ℝ) :
    HasDerivAt (fun t => y₀ 3 + ∫ x in (3 : ℝ)..t, k x * sol k y₀ (x - 1))
      (k s * sol k y₀ (s - 1)) s := by
  have hF : Continuous fun x => k x * sol k y₀ (x - 1) :=
    hk.mul ((continuous_sol hk hy₀).comp (continuous_sub_right 1))
  exact ((hF.integral_hasStrictDerivAt 3 s).hasDerivAt).const_add _

theorem hasDerivAt_sol (hk : Continuous k) (hy₀ : Continuous y₀) {s : ℝ} (hs : 3 < s) :
    HasDerivAt (sol k y₀) (k s * sol k y₀ (s - 1)) s := by
  refine (hasDerivAt_primitive hk hy₀ s).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact sol_of_ge hx.out.le

theorem hasDerivWithinAt_sol_Ici (hk : Continuous k) (hy₀ : Continuous y₀) {s : ℝ}
    (hs : 3 ≤ s) : HasDerivWithinAt (sol k y₀) (k s * sol k y₀ (s - 1)) (Ici s) s := by
  refine (hasDerivAt_primitive hk hy₀ s).hasDerivWithinAt.congr (fun x hx => ?_) ?_
  · exact sol_of_ge (hs.trans hx)
  · exact sol_of_ge hs

end Delay

/-- First-crossing principle. If `f` is continuous on `[a, ∞)`, nonnegative on `[a₀, a]`,
positive at `a`, and `f s > 0` whenever `s > a` and `f ≥ 0` on `[a₀, s]`, `f > 0` on `[a, s)`,
then `f > 0` on `[a, ∞)`. -/
theorem pos_of_first_crossing {f : ℝ → ℝ} {a₀ a : ℝ} (hf : ContinuousOn f (Ici a))
    (hinit : ∀ x ∈ Icc a₀ a, 0 ≤ f x) (ha : 0 < f a)
    (hstep : ∀ s > a, (∀ x ∈ Icc a₀ s, 0 ≤ f x) → (∀ x ∈ Ico a s, 0 < f x) → 0 < f s) :
    ∀ s, a ≤ s → 0 < f s := by
  by_contra hcon
  push Not at hcon
  set B := Ici a ∩ f ⁻¹' Iic 0 with hB
  have hBne : B.Nonempty := by
    obtain ⟨s, hs, hfs⟩ := hcon
    exact ⟨s, hs, hfs⟩
  have hBc : IsClosed B := hf.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  have hBb : BddBelow B := ⟨a, fun x hx => hx.1⟩
  set t := sInf B
  have htB : t ∈ B := hBc.csInf_mem hBne hBb
  have hat : a ≤ t := htB.1
  have hft : f t ≤ 0 := htB.2
  have hat' : a < t := lt_of_le_of_ne hat fun h => by rw [← h] at hft; linarith
  have hpos : ∀ x ∈ Ico a t, 0 < f x := by
    intro x hx
    by_contra hx'
    push Not at hx'
    have : t ≤ x := csInf_le hBb ⟨hx.1, hx'⟩
    exact absurd hx.2 (not_lt.2 this)
  have hnn : ∀ x ∈ Icc a t, 0 ≤ f x := by
    have hcl : closure (Ico a t) = Icc a t := closure_Ico hat'.ne
    have hcont : ContinuousOn f (closure (Ico a t)) := by
      rw [hcl]; exact hf.mono Icc_subset_Ici_self
    have := le_on_closure (f := fun _ => (0 : ℝ)) (g := f) (fun x hx => (hpos x hx).le)
      continuousOn_const hcont
    rwa [hcl] at this
  have hall : ∀ x ∈ Icc a₀ t, 0 ≤ f x := by
    intro x hx
    rcases le_total x a with hxa | hxa
    · exact hinit x ⟨hx.1, hxa⟩
    · exact hnn x ⟨hxa, hx.2⟩
  linarith [hstep t hat' hall hpos]

end IwaniecLinearSieve
