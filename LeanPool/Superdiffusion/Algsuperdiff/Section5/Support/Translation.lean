/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.ShellNorms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.Translate
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HolderGauge
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Translation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra.H1Function

/-!
# Translation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Transporting the Section 5 objects between `y + □_n` and `□_n`

Every Section 5 object attached to the cube `y + □_n` is realized by moving the
*sample*, never the cube: the coefficient field satisfies
`a_m(x, τ_y ω) = a_m(x + y, ω)` exactly, the Dirichlet problem on `y + □_n`
becomes the Dirichlet problem on `□_n` for the pulled-back data, and the two
gauges of `HolderGauge.lean` are invariant under the same change of variables.
This module supplies those transports and the resulting statement of the
large-scale event `𝒥(y + □_n, θ)` as a translate preimage.

## Main definitions

* `IsDirichletSolutionAt a y n u g` — the zero-boundary weak solution of
  `-∇·a∇u = ∇·g` on `y + □_n`.
* `originPullback y n u` — the same solution read on `□_n`, `x ↦ u(x + y)`.
* `largeScaleEventBase M n θ`, `largeScaleEvent M n y θ` — the event
  `Σ_{k ≥ n} 3^{(2-γ)n} ‖∇ j_k‖_{W^{1,∞}(□_n)} ≤ θ` at the origin, and its
  translate to `y + □_n`.  The weight is fixed at the cube scale `n`, as in the
  first condition of the Section 4 good event `𝒢₁(m; s, T)` on `□_m`.

## References

* ABK26, the localized Dirichlet problems and the large-scale good event of
  Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Transporting a Sobolev witness along an equality of domains

`cubeSetAt y n` is the image of `□_n` under `x ↦ y + x`, and the ambient Sobolev
transport API is stated for `translateSet`.  The two sets are equal but not
definitionally so, so the witnesses are moved along the equality. -/

/-- Transport an `H¹` witness along an equality of its domain. -/
def castH1 {U V : Set (Vec d)} (h : U = V) (u : H1Function U) : H1Function V := h ▸ u

@[simp] theorem castH1_toFun {U V : Set (Vec d)} (h : U = V) (u : H1Function U) (x : Vec d) :
    (castH1 h u).toFun x = u.toFun x := by
  subst h; rfl

@[simp] theorem castH1_grad {U V : Set (Vec d)} (h : U = V) (u : H1Function U) (x : Vec d) :
    (castH1 h u).grad x = u.grad x := by
  subst h; rfl

/-- Transport an `H¹₀` witness along an equality of its domain. -/
def castH10 {U V : Set (Vec d)} (h : U = V) (u : H10Function U) : H10Function V := h ▸ u

@[simp] theorem castH10_toFun {U V : Set (Vec d)} (h : U = V) (u : H10Function U) (x : Vec d) :
    (castH10 h u).toH1Function.toFun x = u.toH1Function.toFun x := by
  subst h; rfl

@[simp] theorem castH10_grad {U V : Set (Vec d)} (h : U = V) (u : H10Function U) (x : Vec d) :
    (castH10 h u).toH1Function.grad x = u.toH1Function.grad x := by
  subst h; rfl

/-! ## 2. The Dirichlet problem on `y + □_n` -/

/-- **The Dirichlet problem on `y + □_n`**: `u` agrees with a zero-trace witness
and solves `-∇·a∇u = ∇·g` weakly on `y + □_n`. -/
def IsDirichletSolutionAt (a : CoeffField d) (y : Vec d) (n : ℤ)
    (u : H1Function (cubeSetAt y n)) (g : Vec d → Vec d) : Prop :=
  (∃ w : H10Function (cubeSetAt y n),
      (∀ x, u.toFun x = w.toH1Function.toFun x) ∧
        (∀ x, u.grad x = w.toH1Function.grad x)) ∧
    Section4.Support.IsDivFormWeakSolutionOn a (cubeSetAt y n) u g

theorem isDirichletSolutionAt_def {a : CoeffField d} {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {g : Vec d → Vec d} :
    IsDirichletSolutionAt a y n u g ↔
      (∃ w : H10Function (cubeSetAt y n),
          (∀ x, u.toFun x = w.toH1Function.toFun x) ∧
            (∀ x, u.grad x = w.toH1Function.grad x)) ∧
        Section4.Support.IsDivFormWeakSolutionOn a (cubeSetAt y n) u g :=
  Iff.rfl

/-- The solution on `y + □_n`, read on `□_n` as `x ↦ u(x + y)`. -/
def originPullback (y : Vec d) (n : ℤ) (u : H1Function (cubeSetAt y n)) :
    H1Function (openCubeSet (originCube d n)) :=
  H1Function.untranslate y (castH1 (cubeSetAt_eq_translateSet y n) u)

@[simp] theorem originPullback_toFun (y : Vec d) (n : ℤ) (u : H1Function (cubeSetAt y n))
    (x : Vec d) : (originPullback y n u).toFun x = u.toFun (x + y) := by
  simp [originPullback]

@[simp] theorem originPullback_grad (y : Vec d) (n : ℤ) (u : H1Function (cubeSetAt y n))
    (x : Vec d) : (originPullback y n u).grad x = u.grad (x + y) := by
  simp [originPullback]

/-! ### The change of variables in the weak equation -/

private theorem setIntegral_vecDot_translateSet (y : Vec d) (U : Set (Vec d))
    (A p : Vec d → Vec d) :
    ∫ x in translateSet y U, vecDot (A x) (p x) ∂volume =
      ∫ x in U, vecDot (A (x + y)) (p (x + y)) ∂volume :=
  (setIntegral_comp_addRight_translateSet y U (fun x => vecDot (A x) (p x))).symm

/-- **The weak equation transports exactly.**  The test functions on the two
domains correspond bijectively under `H10Function.translate` and
`H10Function.untranslate`, and the change of variables is measure preserving. -/
theorem isDivFormWeakSolutionOn_translateSet_iff {U : Set (Vec d)} (y : Vec d)
    (a : CoeffField d) (u : H1Function (translateSet y U)) (g : Vec d → Vec d) :
    Section4.Support.IsDivFormWeakSolutionOn a (translateSet y U) u g ↔
      Section4.Support.IsDivFormWeakSolutionOn (fun x => a (x + y)) U
        (H1Function.untranslate y u) (fun x => g (x + y)) := by
  constructor
  · intro h psi
    have hkey := h (H10Function.translate psi y)
    rw [setIntegral_vecDot_translateSet y U
        (fun x => matVecMul (a x) (u.grad x))
        (fun x => (H10Function.translate psi y).toH1Function.grad x),
      setIntegral_vecDot_translateSet y U (fun x => g x)
        (fun x => (H10Function.translate psi y).toH1Function.grad x)] at hkey
    simpa [H1Function.untranslate, add_sub_cancel_right] using hkey
  · intro h phi
    have hkey := h (H10Function.untranslate y phi)
    rw [setIntegral_vecDot_translateSet y U
        (fun x => matVecMul (a x) (u.grad x))
        (fun x => phi.toH1Function.grad x),
      setIntegral_vecDot_translateSet y U (fun x => g x)
        (fun x => phi.toH1Function.grad x)]
    simpa [H1Function.untranslate] using hkey

/-- **The zero boundary condition transports exactly.** -/
theorem zeroTrace_translateSet_iff {U : Set (Vec d)} (y : Vec d)
    (u : H1Function (translateSet y U)) :
    (∃ w : H10Function (translateSet y U),
        (∀ x, u.toFun x = w.toH1Function.toFun x) ∧
          (∀ x, u.grad x = w.toH1Function.grad x)) ↔
      Section4.Support.HasZeroTraceDifferenceOn U (H1Function.untranslate y u) 0 := by
  constructor
  · rintro ⟨w, hfun, hgrad⟩
    refine ⟨H10Function.untranslate y w, fun x => ?_, fun x => ?_⟩
    · simpa using hfun (x + y)
    · simpa using hgrad (x + y)
  · rintro ⟨w, hfun, hgrad⟩
    refine ⟨H10Function.translate w y, fun x => ?_, fun x => ?_⟩
    · have := hfun (x - y)
      simp only [H1Function.untranslate_toFun, sub_add_cancel] at this
      simpa using this
    · have := hgrad (x - y)
      simp only [H1Function.untranslate_grad, sub_add_cancel] at this
      simpa using this

/-- **The origin-cube reading of the Dirichlet problem on `y + □_n`.** -/
theorem isDirichletSolutionAt_iff_origin (a : CoeffField d) (y : Vec d) (n : ℤ)
    (u : H1Function (cubeSetAt y n)) (g : Vec d → Vec d) :
    IsDirichletSolutionAt a y n u g ↔
      Section4.Support.IsDirichletSolutionOn (fun x => a (y + x)) (originCube d n)
        (originPullback y n u) 0 (fun x => g (y + x)) := by
  have hset := cubeSetAt_eq_translateSet y n
  have ha : (fun x : Vec d => a (x + y)) = fun x : Vec d => a (y + x) := by
    funext x; rw [add_comm]
  have hg : (fun x : Vec d => g (x + y)) = fun x : Vec d => g (y + x) := by
    funext x; rw [add_comm]
  constructor
  · rintro ⟨htr, heq⟩
    refine ⟨?_, ?_⟩
    · refine (zeroTrace_translateSet_iff y (castH1 hset u)).1 ?_
      obtain ⟨w, hfun, hgrad⟩ := htr
      exact ⟨castH10 hset w, fun x => by simpa using hfun x, fun x => by simpa using hgrad x⟩
    · have := (isDivFormWeakSolutionOn_translateSet_iff y a (castH1 hset u) g).1 (by
        intro phi
        have := heq (castH10 hset.symm phi)
        simpa [hset] using this)
      rwa [ha, hg] at this
  · rintro ⟨htr, heq⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨w, hfun, hgrad⟩ := (zeroTrace_translateSet_iff y (castH1 hset u)).2 htr
      exact ⟨castH10 hset.symm w, fun x => by simpa using hfun x, fun x => by simpa using hgrad x⟩
    · have hback : Section4.Support.IsDivFormWeakSolutionOn (fun x => a (x + y))
          (openCubeSet (originCube d n)) (H1Function.untranslate y (castH1 hset u))
          (fun x => g (x + y)) := by
        rw [ha, hg]; exact heq
      have := (isDivFormWeakSolutionOn_translateSet_iff y a (castH1 hset u) g).2 hback
      intro phi
      have := this (castH10 hset phi)
      simpa [hset] using this

/-! ## 3. The two gauges transport -/

theorem holderSeminormOn_cubeSetAt_eq {E : Type*} [NormedAddCommGroup E] (y : Vec d) (n : ℤ)
    (alpha : ℝ) (f : Vec d → E) :
    holderSeminormOn (cubeSetAt y n) alpha f =
      holderSeminormOn (openCubeSet (originCube d n)) alpha (fun x => f (y + x)) := by
  refine le_antisymm ?_ ?_
  · simp only [holderSeminormOn, iSup_le_iff]
    intro x hx z hz hne
    have hx' : x - y ∈ openCubeSet (originCube d n) := mem_cubeSetAt_iff.1 hx
    have hz' : z - y ∈ openCubeSet (originCube d n) := mem_cubeSetAt_iff.1 hz
    have hne' : x - y ≠ z - y := fun h => hne (by
      have := congrArg (fun t : Vec d => t + y) h
      simpa using this)
    have h1 : y + (x - y) = x := by rw [add_comm]; exact sub_add_cancel x y
    have h2 : y + (z - y) = z := by rw [add_comm]; exact sub_add_cancel z y
    have h3 : (x - y) - (z - y) = x - z := by ring
    have hle := le_holderSeminormOn (f := fun t : Vec d => f (y + t)) (alpha := alpha)
      hx' hz' hne'
    simp only [h1, h2, h3] at hle
    simpa only [holderSeminormOn] using hle
  · simp only [holderSeminormOn, iSup_le_iff]
    intro x hx z hz hne
    have hx' : y + x ∈ cubeSetAt y n := by
      rw [mem_cubeSetAt_iff]; simpa [add_comm] using hx
    have hz' : y + z ∈ cubeSetAt y n := by
      rw [mem_cubeSetAt_iff]; simpa [add_comm] using hz
    have hne' : y + x ≠ y + z := fun h => hne (by
      have := congrArg (fun t : Vec d => t - y) h
      simpa [add_comm] using this)
    have h3 : (y + x) - (y + z) = x - z := by ring
    have hle := le_holderSeminormOn (f := f) (alpha := alpha) hx' hz' hne'
    simp only [h3] at hle
    simpa only [holderSeminormOn] using hle

/-! ## 4. The coefficient covariance -/

/-- **The cutoff coefficient of the translated sample is the coefficient field
recentred at `y`**, in the form the origin-cube reading of the Dirichlet problem
consumes. -/
theorem coefficientCutoff_add_eq_translateCutoffSample (M : ABKModel d) (m : ℤ)
    (y : Vec d) (omega : Cutoff.CutoffSample d) :
    (fun x : Vec d =>
        (Cutoff.coefficientCutoff M.nu m omega).toCoeffField (y + x)) =
      (Cutoff.coefficientCutoff M.nu m (Cutoff.translateCutoffSample y omega)).toCoeffField := by
  funext x
  have h := congrArg (fun A : RegCoeffField d => A x)
    (Cutoff.coefficientCutoff_translateCutoffSample M.nu m y omega)
  simp only [translateReg_apply] at h
  rw [add_comm y x]
  exact h.symm

/-! ## 5. The large-scale event `𝒥` -/

/-- **The large-scale event at the origin**: the tail sum
`Σ_{k ≥ n} 3^{(2-γ)n} ‖∇ j_k‖_{W^{1,∞}(□_n)}` does not exceed `θ`.

The weight `3^{(2-γ)n}` is fixed at the cube scale `n` and does not run with the
summation index `k`.  This is the shape of the first condition of the Section 4
good event `𝒢₁(m; s, T)`, whose weight `3^{(2-γ)m}` is likewise fixed at the
cube scale, and it is the shape the size of the summand demands: the increment
`j_k` obeys `j_k ≃ 3^{γk} j_0(3^{-k} ·)`, so
`‖∇ j_k‖_{W^{1,∞}(□_n)} ≃ max(3^{(γ-2)k}, 3^{-n} 3^{(γ-1)k})` and the `k`-th
term of the fixed-weight series is of order `3^{-(1-γ)(k-n)}`.  The series is
then geometric for `γ < 1`, and the event has positive measure at every
threshold `θ` above the typical value of the sum.  A weight `3^{(2-γ)k}` running
with `k` would instead make the `k`-th term of order `max(1, 3^{k-n})`, the
series divergent almost surely, and the event a null set at every finite `θ`. -/
def largeScaleEventBase (M : ABKModel d) (n : ℤ) (theta : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  {omega | (∑' k : {k : ℤ // n ≤ k},
      ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (n : ℝ)) *
        Section4.Support.shellW1InfGradNorm n (omega.1 k.1))) ≤ ENNReal.ofReal theta}

/-- **The large-scale event on `y + □_n`**, realized by translating the sample. -/
def largeScaleEvent (M : ABKModel d) (n : ℤ) (y : Vec d) (theta : ℝ) :
    Set (Cutoff.CutoffSample d) :=
  Cutoff.translateCutoffSample y ⁻¹' largeScaleEventBase M n theta

theorem mem_largeScaleEvent_iff (M : ABKModel d) (n : ℤ) (y : Vec d) (theta : ℝ)
    (omega : Cutoff.CutoffSample d) :
    omega ∈ largeScaleEvent M n y theta ↔
      Cutoff.translateCutoffSample y omega ∈ largeScaleEventBase M n theta :=
  Iff.rfl

private theorem measurable_shellTailSum (M : ABKModel d) (n : ℤ) :
    Measurable fun omega : Cutoff.CutoffSample d =>
      ∑' k : {k : ℤ // n ≤ k},
        ENNReal.ofReal (Real.rpow (3 : ℝ) ((2 - M.gamma) * (n : ℝ)) *
          Section4.Support.shellW1InfGradNorm n (omega.1 k.1)) := by
  refine Measurable.tsum ?_
  intro k
  refine ENNReal.measurable_ofReal.comp ?_
  refine measurable_const.mul ?_
  exact (Section4.Support.measurable_shellW1InfGradNorm n).comp
    ((measurable_pi_apply k.1).comp measurable_subtype_coe)

theorem measurableSet_largeScaleEventBase (M : ABKModel d) (n : ℤ) (theta : ℝ) :
    MeasurableSet (largeScaleEventBase M n theta) :=
  measurableSet_le (measurable_shellTailSum M n) measurable_const

theorem measurableSet_largeScaleEvent (M : ABKModel d) (n : ℤ) (y : Vec d) (theta : ℝ) :
    MeasurableSet (largeScaleEvent M n y theta) :=
  (measurableSet_largeScaleEventBase M n theta).preimage
    (Cutoff.measurable_translateCutoffSample y)

end

end Algsuperdiff.Section5.Support
