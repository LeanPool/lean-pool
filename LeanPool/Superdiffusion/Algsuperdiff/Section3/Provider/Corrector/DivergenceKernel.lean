/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifierScaling
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.SolenoidalStream

/-!
# DivergenceKernel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: an explicit divergence kernel for a difference of tensor densities

Several smoothing arguments in Section 3 need to compare the *same* field
averaged at two different scales, i.e. they need to control a difference of two
product densities

`χ_a(x) − χ_b(x) = ∏ᵢ a(xᵢ) − ∏ᵢ b(xᵢ)`,

where `a` and `b` are one-dimensional smooth compactly supported probability
densities (in practice `a = φ_ε` and `b = φ_R`, the one-dimensional factors of
`Algsuperdiff/Section3/Provider/Corrector/MollifierScaling.lean`'s
`productDensity`).  What makes such a difference small when tested against a
solenoidal or mean-zero field is that it is a *divergence* of a smooth
compactly supported vector field.

This file writes that vector field down explicitly.  With

`G(t) = ∫_{-T}^{t} (a(s) − b(s)) ds`  (`kernelPrimitive`),

`g_k(x) = G(x_k) · ∏_{i < k} b(x_i) · ∏_{i > k} a(x_i)`  (`divKernel`),

the fundamental theorem of calculus gives `∂_k g_k(x) = (a(x_k) − b(x_k)) ·
∏_{i<k} b(x_i) · ∏_{i>k} a(x_i)`, because neither product involves the
coordinate `x_k`.  In terms of the interpolating densities

`χ_m(x) = ∏_{i.val < m} b(x_i) · ∏_{m ≤ i.val} a(x_i)`  (`mixedDensity`),

this reads `∂_k g_k = χ_{k.val} − χ_{k.val + 1}`, so the sum over `k`
telescopes:

`Σ_k ∂_k g_k = χ_0 − χ_d = χ_a − χ_b`  (`coordDeriv_sum_divKernel`).

Nothing deeper is used: no Newtonian potential, no Newton theorem, no elliptic
solve and no Fourier analysis.  The construction is elementary and completely
explicit, and the divergence is phrased with
`Algsuperdiff/Section3/Provider/Corrector/SolenoidalStream.lean`'s `coordDeriv`,
so it composes with the stream-tensor layer used there.

Support and smoothness are recorded as well: each component `g_k` is `C^∞`
(`contDiff_divKernel_apply`) and vanishes off the closed sup-norm ball of radius
`T` (`hasCompactSupport_divKernel_apply`, `tsupport_divKernel_apply_subset`),
provided `a` and `b` are unit-mass densities vanishing for `T ≤ |s|`.  The
concrete two-scale instance `a = scaledBump hε`, `b = scaledBump hR`,
`T = ε + R` is recorded at the end of the file.

**Disclosure.**  Nothing in this file realizes any source node.  It is an
elementary explicit construction offered as a local helper, and it claims no
node status.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

variable {d : ℕ}

/-! ### Coordinate derivatives along a single coordinate line -/

/-- Moving the `k`th coordinate of `x` to `t` is the same as translating `x`
along the `k`th basis vector. -/
theorem update_eq_add_smul_basisVec (x : Vec d) (k : Fin d) (t : ℝ) :
    Function.update x k t = x + (t - x k) • basisVec k := by
  funext i
  by_cases h : i = k
  · subst h
    simp
  · simp [h]

/-- **Coordinate derivatives are one-dimensional derivatives.**  If restricting a
field differentiable at `x` to the `k`th coordinate line through `x` produces the
one-dimensional function `h`, then the `k`th coordinate derivative of the field
at `x` is the derivative of `h` at `x k`. -/
theorem coordDeriv_eq_of_hasDerivAt_update {F : Vec d → ℝ} {h : ℝ → ℝ} {x : Vec d}
    {k : Fin d} {c : ℝ} (hF : DifferentiableAt ℝ F x)
    (hupd : ∀ t : ℝ, F (Function.update x k t) = h t) (hh : HasDerivAt h c (x k)) :
    coordDeriv F k x = c := by
  have hline : HasDerivAt (fun t : ℝ => x + (t - x k) • basisVec k) (basisVec k) (x k) := by
    have h1 : HasDerivAt (fun t : ℝ => t - x k) (1 : ℝ) (x k) :=
      (hasDerivAt_id (x k)).sub_const (x k)
    have h2 := HasDerivAt.const_add x (h1.smul_const (basisVec k))
    rwa [one_smul] at h2
  have hcomp : HasDerivAt (F ∘ fun t : ℝ => x + (t - x k) • basisVec k)
      (fderiv ℝ F x (basisVec k)) (x k) := by
    have hFA : HasFDerivAt F (fderiv ℝ F x)
        ((fun t : ℝ => x + (t - x k) • basisVec k) (x k)) := by
      change HasFDerivAt F (fderiv ℝ F x) (x + (x k - x k) • basisVec k)
      rw [show x + (x k - x k) • basisVec k = x by simp]
      exact hF.hasFDerivAt
    exact hFA.comp_hasDerivAt (x k) hline
  have hfun : (F ∘ fun t : ℝ => x + (t - x k) • basisVec k) = h := by
    funext t
    rw [Function.comp_apply, ← update_eq_add_smul_basisVec, hupd]
  rw [hfun] at hcomp
  change fderiv ℝ F x (basisVec k) = c
  exact hcomp.unique hh

/-! ### The index blocks of the telescoping -/

/-- The coordinates strictly below the level `m`. -/
def idxBelow (d m : ℕ) : Finset (Fin d) := Finset.univ.filter fun i : Fin d => (i : ℕ) < m

/-- The coordinates at or above the level `m`. -/
def idxAbove (d m : ℕ) : Finset (Fin d) := Finset.univ.filter fun i : Fin d => m ≤ (i : ℕ)

@[simp] theorem mem_idxBelow {m : ℕ} {i : Fin d} : i ∈ idxBelow d m ↔ (i : ℕ) < m := by
  simp [idxBelow]

@[simp] theorem mem_idxAbove {m : ℕ} {i : Fin d} : i ∈ idxAbove d m ↔ m ≤ (i : ℕ) := by
  simp [idxAbove]

/-- No coordinate lies below level `0`. -/
theorem idxBelow_zero (d : ℕ) : idxBelow d 0 = (∅ : Finset (Fin d)) := by
  ext i
  simp

/-- Every coordinate lies at or above level `0`. -/
theorem idxAbove_zero (d : ℕ) : idxAbove d 0 = (Finset.univ : Finset (Fin d)) := by
  ext i
  simp

/-- Every coordinate lies below level `d`. -/
theorem idxBelow_self (d : ℕ) : idxBelow d d = (Finset.univ : Finset (Fin d)) := by
  ext i
  simp

/-- No coordinate lies at or above level `d`. -/
theorem idxAbove_self (d : ℕ) : idxAbove d d = (∅ : Finset (Fin d)) := by
  ext i
  simp

/-- The level-`k` upper block is the level-`(k+1)` upper block with `k` restored. -/
theorem idxAbove_val_eq_insert (k : Fin d) :
    idxAbove d (k : ℕ) = insert k (idxAbove d ((k : ℕ) + 1)) := by
  classical
  ext i
  simp only [Finset.mem_insert, mem_idxAbove]
  constructor
  · intro hi
    rcases Nat.lt_or_ge (i : ℕ) ((k : ℕ) + 1) with hlt | hge
    · exact Or.inl (Fin.val_injective (by omega))
    · exact Or.inr hge
  · rintro (rfl | hge)
    · exact le_rfl
    · omega

/-- The level-`(k+1)` lower block is the level-`k` lower block with `k` adjoined. -/
theorem idxBelow_succ_eq_insert (k : Fin d) :
    idxBelow d ((k : ℕ) + 1) = insert k (idxBelow d (k : ℕ)) := by
  classical
  ext i
  simp only [Finset.mem_insert, mem_idxBelow]
  constructor
  · intro hi
    rcases Nat.lt_or_ge (i : ℕ) (k : ℕ) with hlt | hge
    · exact Or.inr hlt
    · exact Or.inl (Fin.val_injective (by omega))
  · rintro (rfl | hlt)
    · omega
    · omega

theorem notMem_idxAbove_succ (k : Fin d) : k ∉ idxAbove d ((k : ℕ) + 1) := by
  simp

theorem notMem_idxBelow_val (k : Fin d) : k ∉ idxBelow d (k : ℕ) := by
  simp

/-! ### The one-dimensional primitive of the difference -/

section Primitive

variable {a b : ℝ → ℝ} {T : ℝ}

/-- The primitive `G(t) = ∫_{-T}^{t}(a − b)` of the difference of the two
one-dimensional densities. -/
def kernelPrimitive (a b : ℝ → ℝ) (T t : ℝ) : ℝ := ∫ s in (-T)..t, (a s - b s)

theorem kernelPrimitive_apply (a b : ℝ → ℝ) (T t : ℝ) :
    kernelPrimitive a b T t = ∫ s in (-T)..t, (a s - b s) := rfl

/-- **Fundamental theorem of calculus for the primitive**: `G' = a − b`. -/
theorem hasDerivAt_kernelPrimitive (ha : Continuous a) (hb : Continuous b) (t : ℝ) :
    HasDerivAt (kernelPrimitive a b T) (a t - b t) t := by
  have hc : Continuous fun s => a s - b s := ha.sub hb
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (-T) t)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt

theorem differentiable_kernelPrimitive (ha : Continuous a) (hb : Continuous b) :
    Differentiable ℝ (kernelPrimitive a b T) := fun t =>
  (hasDerivAt_kernelPrimitive (T := T) ha hb t).differentiableAt

theorem deriv_kernelPrimitive (ha : Continuous a) (hb : Continuous b) :
    deriv (kernelPrimitive a b T) = fun t => a t - b t := by
  funext t
  exact (hasDerivAt_kernelPrimitive (T := T) ha hb t).deriv

/-- The primitive of a difference of smooth densities is smooth. -/
theorem contDiff_kernelPrimitive (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (kernelPrimitive a b T) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨differentiable_kernelPrimitive ha.continuous hb.continuous, ?_⟩
  rw [deriv_kernelPrimitive ha.continuous hb.continuous]
  exact ha.sub hb

/-- A continuous function vanishing for `T ≤ |s|` is integrable: it is supported
in the compact interval `[-T, T]`. -/
theorem integrable_of_eq_zero_of_abs_le (ha : Continuous a)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0) : Integrable a volume := by
  refine ha.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc fun s hs => ?_)
  rw [Set.mem_Icc] at hs
  push Not at hs
  rcases le_or_gt (-T) s with hle | hlt
  · exact haT s (le_trans (hs hle).le (le_abs_self s))
  · exact haT s (le_trans (by linarith : T ≤ -s) (neg_le_abs s))

/-- **The primitive vanishes outside `(-T, T)`.**  To the left of `-T` the
integrand vanishes identically; to the right of `T` the integral over `[-T, T]`
is the full integral of `a − b`, which is `1 − 1 = 0`. -/
theorem kernelPrimitive_eq_zero_of_le (ha : Continuous a) (hb : Continuous b)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0) (hbT : ∀ s : ℝ, T ≤ |s| → b s = 0)
    (ha1 : ∫ s, a s = 1) (hb1 : ∫ s, b s = 1) {t : ℝ} (ht : T ≤ |t|) :
    kernelPrimitive a b T t = 0 := by
  have hzero : ∀ s : ℝ, T ≤ |s| → a s - b s = 0 := fun s hs => by
    rw [haT s hs, hbT s hs, sub_zero]
  have hc : Continuous fun s => a s - b s := ha.sub hb
  rw [kernelPrimitive_apply]
  rcases le_abs.mp ht with hpos | hneg
  · have hsplit : (∫ s in (-T)..T, (a s - b s)) + ∫ s in T..t, (a s - b s)
        = ∫ s in (-T)..t, (a s - b s) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hc.intervalIntegrable (-T) T) (hc.intervalIntegrable T t)
    have hfull : (∫ s in (-T)..T, (a s - b s)) = 0 := by
      have hsupp : Function.support (fun s => a s - b s) ⊆ Set.Ioc (-T) T := by
        intro s hs
        by_contra hmem
        rw [Set.mem_Ioc] at hmem
        push Not at hmem
        rcases lt_or_ge (-T) s with hlt | hge
        · exact hs (hzero s (le_trans (hmem hlt).le (le_abs_self s)))
        · exact hs (hzero s (le_trans (by linarith : T ≤ -s) (neg_le_abs s)))
      rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp,
        integral_sub (integrable_of_eq_zero_of_abs_le ha haT)
          (integrable_of_eq_zero_of_abs_le hb hbT), ha1, hb1, sub_self]
    have htail : (∫ s in T..t, (a s - b s)) = 0 := by
      have hcongr : (∫ s in T..t, (a s - b s)) = ∫ _s in T..t, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le hpos, Set.mem_Icc] at hs
        exact hzero s (le_trans hs.1 (le_abs_self s))
      rw [hcongr, intervalIntegral.integral_zero]
    rw [← hsplit, hfull, htail, add_zero]
  · have hle : t ≤ -T := by linarith
    have hcongr : (∫ s in (-T)..t, (a s - b s)) = ∫ _s in (-T)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_ge hle, Set.mem_Icc] at hs
      exact hzero s (le_trans (by linarith [hs.2] : T ≤ -s) (neg_le_abs s))
    rw [hcongr, intervalIntegral.integral_zero]

end Primitive

/-! ### The tensor densities and the divergence kernel -/

section Kernel

variable {a b : ℝ → ℝ} {T : ℝ}

/-- The tensor-product density `χ_a(x) = ∏ᵢ a(xᵢ)`. -/
def tensorDensity (a : ℝ → ℝ) (x : Vec d) : ℝ := ∏ i : Fin d, a (x i)

theorem tensorDensity_apply (a : ℝ → ℝ) (x : Vec d) :
    tensorDensity a x = ∏ i : Fin d, a (x i) := rfl

/-- The interpolating density at level `m`: the first `m` coordinates carry the
density `b`, the remaining coordinates carry the density `a`. -/
def mixedDensity (a b : ℝ → ℝ) (m : ℕ) (x : Vec d) : ℝ :=
  (∏ i ∈ idxBelow d m, b (x i)) * (∏ i ∈ idxAbove d m, a (x i))

theorem mixedDensity_apply (a b : ℝ → ℝ) (m : ℕ) (x : Vec d) :
    mixedDensity a b m x = (∏ i ∈ idxBelow d m, b (x i)) * (∏ i ∈ idxAbove d m, a (x i)) := rfl

/-- At level `0` the interpolating density is `χ_a`. -/
theorem mixedDensity_zero (a b : ℝ → ℝ) (x : Vec d) :
    mixedDensity a b 0 x = tensorDensity a x := by
  rw [mixedDensity_apply, idxBelow_zero, idxAbove_zero, Finset.prod_empty, one_mul,
    tensorDensity_apply]

/-- At level `d` the interpolating density is `χ_b`. -/
theorem mixedDensity_card (a b : ℝ → ℝ) (x : Vec d) :
    mixedDensity a b d x = tensorDensity b x := by
  rw [mixedDensity_apply, idxBelow_self, idxAbove_self, Finset.prod_empty, mul_one,
    tensorDensity_apply]

/-- **The divergence kernel.**  Its `k`th component carries the primitive `G` in
the `k`th coordinate, the density `b` in the coordinates below `k` and the
density `a` in the coordinates above `k`. -/
def divKernel (a b : ℝ → ℝ) (T : ℝ) (x : Vec d) : Vec d := fun k =>
  kernelPrimitive a b T (x k) * (∏ i ∈ idxBelow d (k : ℕ), b (x i))
    * (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i))

theorem divKernel_apply (a b : ℝ → ℝ) (T : ℝ) (x : Vec d) (k : Fin d) :
    divKernel a b T x k = kernelPrimitive a b T (x k) * (∏ i ∈ idxBelow d (k : ℕ), b (x i))
      * (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i)) := rfl

/-- Every component of the divergence kernel is smooth. -/
theorem contDiff_divKernel_apply (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => divKernel a b T x k := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => kernelPrimitive a b T (x k) :=
    (contDiff_kernelPrimitive ha hb).comp (contDiff_apply ℝ ℝ k)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => ∏ i ∈ idxBelow d (k : ℕ), b (x i) :=
    contDiff_prod fun i _ => hb.comp (contDiff_apply ℝ ℝ i)
  have h3 : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d => ∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i) :=
    contDiff_prod fun i _ => ha.comp (contDiff_apply ℝ ℝ i)
  exact (h1.mul h2).mul h3

/-- The divergence kernel vanishes outside the closed sup-norm ball of radius
`T`: some coordinate of `x` then has modulus at least `T`, and whichever of the
three factors sits at that coordinate vanishes. -/
theorem divKernel_apply_eq_zero_of_le (ha : Continuous a) (hb : Continuous b)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0) (hbT : ∀ s : ℝ, T ≤ |s| → b s = 0)
    (ha1 : ∫ s, a s = 1) (hb1 : ∫ s, b s = 1) (hT : 0 < T) {x : Vec d} (hx : T ≤ ‖x‖)
    (k : Fin d) : divKernel a b T x k = 0 := by
  classical
  have hex : ∃ i : Fin d, T ≤ |x i| := by
    by_contra hcon
    push Not at hcon
    have hlt : ‖x‖ < T := (pi_norm_lt_iff hT).2 fun i => by
      rw [Real.norm_eq_abs]
      exact hcon i
    linarith
  obtain ⟨i, hi⟩ := hex
  rw [divKernel_apply]
  rcases lt_trichotomy (i : ℕ) (k : ℕ) with hlt | heq | hgt
  · rw [Finset.prod_eq_zero (mem_idxBelow.mpr hlt) (hbT (x i) hi)]
    ring
  · have hik : i = k := Fin.val_injective heq
    subst hik
    rw [kernelPrimitive_eq_zero_of_le ha hb haT hbT ha1 hb1 hi]
    ring
  · rw [Finset.prod_eq_zero (mem_idxAbove.mpr (by omega)) (haT (x i) hi)]
    ring

/-- Every component of the divergence kernel is compactly supported. -/
theorem hasCompactSupport_divKernel_apply (ha : Continuous a) (hb : Continuous b)
    (haT : ∀ s : ℝ, T ≤ |s| → a s = 0) (hbT : ∀ s : ℝ, T ≤ |s| → b s = 0)
    (ha1 : ∫ s, a s = 1) (hb1 : ∫ s, b s = 1) (hT : 0 < T) (k : Fin d) :
    HasCompactSupport fun x : Vec d => divKernel a b T x k := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) T) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  push Not at hx
  exact divKernel_apply_eq_zero_of_le ha hb haT hbT ha1 hb1 hT hx.le k

/-! ### The telescoping divergence identity -/

/-- **The `k`th coordinate derivative of the `k`th component.**  Only the factor
`G(x_k)` depends on the coordinate `x_k`, and `G' = a − b`. -/
theorem coordDeriv_divKernel_apply (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (k : Fin d) (x : Vec d) :
    coordDeriv (fun y : Vec d => divKernel a b T y k) k x
      = (a (x k) - b (x k)) * (∏ i ∈ idxBelow d (k : ℕ), b (x i))
          * (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i)) := by
  classical
  have hdiff : DifferentiableAt ℝ (fun y : Vec d => divKernel a b T y k) x :=
    ((contDiff_divKernel_apply ha hb k).differentiable (by simp)).differentiableAt
  have hupd : ∀ t : ℝ, divKernel a b T (Function.update x k t) k
      = kernelPrimitive a b T t * (∏ i ∈ idxBelow d (k : ℕ), b (x i))
          * (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i)) := by
    intro t
    have hP : (∏ i ∈ idxBelow d (k : ℕ), b (Function.update x k t i))
        = ∏ i ∈ idxBelow d (k : ℕ), b (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [mem_idxBelow] at hi
      have hne : i ≠ k := fun hik => by rw [hik] at hi; omega
      rw [Function.update_of_ne hne]
    have hQ : (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (Function.update x k t i))
        = ∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [mem_idxAbove] at hi
      have hne : i ≠ k := fun hik => by rw [hik] at hi; omega
      rw [Function.update_of_ne hne]
    rw [divKernel_apply, Function.update_self, hP, hQ]
  have hh : HasDerivAt (fun t : ℝ => kernelPrimitive a b T t
        * (∏ i ∈ idxBelow d (k : ℕ), b (x i)) * (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i)))
      ((a (x k) - b (x k)) * (∏ i ∈ idxBelow d (k : ℕ), b (x i))
        * (∏ i ∈ idxAbove d ((k : ℕ) + 1), a (x i))) (x k) :=
    ((hasDerivAt_kernelPrimitive ha.continuous hb.continuous (x k)).mul_const _).mul_const _
  exact coordDeriv_eq_of_hasDerivAt_update hdiff hupd hh

/-- **The `k`th coordinate derivative is one telescoping step.** -/
theorem coordDeriv_divKernel_apply_eq_sub (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (k : Fin d) (x : Vec d) :
    coordDeriv (fun y : Vec d => divKernel a b T y k) k x
      = mixedDensity a b (k : ℕ) x - mixedDensity a b ((k : ℕ) + 1) x := by
  classical
  rw [coordDeriv_divKernel_apply ha hb k x, mixedDensity_apply, mixedDensity_apply,
    idxAbove_val_eq_insert k, Finset.prod_insert (notMem_idxAbove_succ k),
    idxBelow_succ_eq_insert k, Finset.prod_insert (notMem_idxBelow_val k)]
  ring

/-- **The divergence identity.**  The divergence of the explicit smooth
compactly supported vector field `divKernel a b T` is the difference of the two
tensor-product densities:

`Σ_k ∂_k g_k(x) = ∏ᵢ a(xᵢ) − ∏ᵢ b(xᵢ)`.

Only smoothness of the two one-dimensional densities is used; support and unit
mass enter nowhere. -/
theorem coordDeriv_sum_divKernel (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (x : Vec d) :
    ∑ k : Fin d, coordDeriv (fun y : Vec d => divKernel a b T y k) k x
      = tensorDensity a x - tensorDensity b x := by
  classical
  calc ∑ k : Fin d, coordDeriv (fun y : Vec d => divKernel a b T y k) k x
      = ∑ k : Fin d, (mixedDensity a b (k : ℕ) x - mixedDensity a b ((k : ℕ) + 1) x) :=
        Finset.sum_congr rfl fun k _ => coordDeriv_divKernel_apply_eq_sub ha hb k x
    _ = ∑ m ∈ Finset.range d, (mixedDensity a b m x - mixedDensity a b (m + 1) x) :=
        Fin.sum_univ_eq_sum_range
          (fun m => mixedDensity a b m x - mixedDensity a b (m + 1) x) d
    _ = mixedDensity a b 0 x - mixedDensity a b d x :=
        Finset.sum_range_sub' (fun m => mixedDensity a b m x) d
    _ = tensorDensity a x - tensorDensity b x := by
        rw [mixedDensity_zero, mixedDensity_card]

end Kernel

/-! ### The two-scale instance -/

section Bumps

variable {ε R : ℝ}

/-- Every component of the two-scale divergence kernel is smooth. -/
theorem contDiff_divKernel_scaledBump_apply (hε : 0 < ε) (hR : 0 < R) (k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x : Vec d =>
      divKernel (scaledBump hε) (scaledBump hR) (ε + R) x k :=
  contDiff_divKernel_apply (contDiff_scaledBump hε) (contDiff_scaledBump hR) k

/-- Every component of the two-scale divergence kernel is compactly supported in
the closed sup-norm ball of radius `ε + R`. -/
theorem hasCompactSupport_divKernel_scaledBump_apply (hε : 0 < ε) (hR : 0 < R) (k : Fin d) :
    HasCompactSupport fun x : Vec d =>
      divKernel (scaledBump hε) (scaledBump hR) (ε + R) x k := by
  refine hasCompactSupport_divKernel_apply (continuous_scaledBump hε)
    (continuous_scaledBump hR) (fun s hs => scaledBump_eq_zero hε (by linarith))
    (fun s hs => scaledBump_eq_zero hR (by linarith)) (integral_scaledBump hε)
    (integral_scaledBump hR) (by linarith) k

/-- **The two-scale divergence identity.**  The difference of the product
densities at the scales `ε` and `R` is the divergence of the explicit smooth
vector field `divKernel (scaledBump hε) (scaledBump hR) (ε + R)`, whose
components are supported in the closed sup-norm ball of radius `ε + R`. -/
theorem coordDeriv_sum_divKernel_scaledBump (hε : 0 < ε) (hR : 0 < R) (x : Vec d) :
    ∑ k : Fin d, coordDeriv
        (fun y : Vec d => divKernel (scaledBump hε) (scaledBump hR) (ε + R) y k) k x
      = productDensity d hε x - productDensity d hR x :=
  coordDeriv_sum_divKernel (contDiff_scaledBump hε) (contDiff_scaledBump hR) x

end Bumps

end

end Algsuperdiff.Section3.Provider.Corrector
