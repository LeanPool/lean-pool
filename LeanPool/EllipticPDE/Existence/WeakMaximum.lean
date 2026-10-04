/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Existence.Garding
public import LeanPool.EllipticPDE.Embedding.ChainRule
public import LeanPool.EllipticPDE.Extension.GlobalApproximation


/-!
# Weak maximum principle

A weak subsolution of a transport-free divergence-form equation with nonnegative zeroth-order
coefficient is bounded above by its boundary values. The boundary inequality `u ≤ k on ∂Ω`
for a Sobolev class is read, following Gilbarg and Trudinger, as membership of `(u - k)⁺` in
`H₀¹(Ω)`, and the conclusion is `u ≤ k` almost everywhere for every `k ≥ 0` with that
property, which is the inequality `sup_Ω u ≤ sup_∂Ω u⁺` between the essential supremum and
the infimum of such `k`.

The proof is the transport-free case the source singles out. Testing the subsolution
inequality against `v = (u - k)⁺`, the zeroth-order term is nonnegative because `u v ≥ 0`, so
the principal term is nonpositive. The weak gradient of `v` is the gradient of `u` where
`u > k` and zero elsewhere, so the principal term is the energy of `v` itself, which
ellipticity bounds below by the gradient norm. The gradient of `v` therefore vanishes, and the
Poincaré inequality on `H₀¹` of a bounded domain makes `v` vanish.

The subsolution inequality is taken against every nonnegative element of `H₀¹(Ω)`, which is
the form the source uses in the proof, having extended the inequality from `C¹` test functions
by density.

## Main declarations

* `EllipticPdes.Sobolev.weak_maximum_principle`: the weak maximum principle for a
  transport-free operator with nonnegative zeroth-order coefficient.

## References

D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§8.1 Theorem 8.1 (p. 179);
L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.1 Theorem 2 (p. 346).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding EllipticPdes.Extension EllipticPdes.Poincare

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- **Weak maximum principle** (Gilbarg and Trudinger Theorem 8.1, in the transport-free
case). Let `Ω` be a bounded open set, `L` a divergence-form operator with no transport term and
nonnegative zeroth-order coefficient, and `U ∈ H¹(Ω)` a weak subsolution, meaning the bilinear
pairing of `U` against every nonnegative `V ∈ H₀¹(Ω)` is nonpositive. If `k ≥ 0` and
`(u - k)⁺` is the function coordinate of some element of `H₀¹(Ω)`, then `u ≤ k` almost
everywhere on `Ω`. -/
theorem weak_maximum_principle (hd : 0 < d) (hΩopen : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (Op : FullEllipticOp d) (hb : ∀ x i, Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ Op.c x)
    {U : H1amb Ω} (hU : U ∈ W12 Ω)
    (hsub : ∀ V : H01 Ω, (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ)) →
      (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : H1amb Ω) j.succ⟫)
        + (∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫)
        + ⟪Op.cAct (U 0), (V : H1amb Ω) 0⟫ ≤ 0)
    {k : ℝ} (hk : 0 ≤ k)
    (hbd : ∃ V : H01 Ω, ((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max ((U 0 x : ℝ) - k) 0) :
    ∀ᵐ x ∂(volume.restrict Ω), (U 0 x : ℝ) ≤ k := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict_of_isBounded hΩb
  obtain ⟨V, hV0⟩ := hbd
  -- the class and its weak gradient
  set u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => (U 0 x : ℝ) with hudef
  set g : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun i x => (U i.succ x : ℝ) with hgdef
  have hwg : HasWeakGradOn Ω u g := hasWeakGradOn_of_mem_W12 hU
  have huint : IntegrableOn u Ω volume := (Lp.memLp (U 0)).integrable one_le_two
  have hgint : ∀ i, IntegrableOn (g i) Ω volume := fun i =>
    (Lp.memLp (U i.succ)).integrable one_le_two
  have hum : Measurable u := (Lp.stronglyMeasurable (U 0)).measurable
  -- the truncation and its weak gradient
  set w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => max (u x - k) 0 with hwdef
  set h : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun i x => if k < u x then g i x else 0 with hhdef
  have hw : HasWeakGradOn Ω w h :=
    hasWeakGradOn_posPart_sub_const hΩopen huint.locallyIntegrableOn
      (fun i => (hgint i).locallyIntegrableOn) hwg k
  have hS : MeasurableSet {x | k < u x} := measurableSet_lt measurable_const hum
  have hhint : ∀ i, IntegrableOn (h i) Ω volume := fun i => by
    have : h i = {x | k < u x}.indicator (g i) := by
      funext x
      simp only [hhdef, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [this]
    exact (hgint i).indicator hS
  -- `V` is the truncation together with its gradient
  have hVW : (V : H1amb Ω) ∈ W12 Ω := H01_le_W12 Ω V.2
  have hwgV' : HasWeakGradOn Ω w fun i x => ((V : H1amb Ω) i.succ x : ℝ) :=
    (hasWeakGradOn_of_mem_W12 hVW).congr_ae hV0 fun _ => EventuallyEq.rfl
  have hVgrad : ∀ i, (fun x => ((V : H1amb Ω) i.succ x : ℝ)) =ᵐ[volume.restrict Ω] h i :=
    fun i => hasWeakGradOn_unique_ae hΩopen hΩopen.measurableSet
      (fun i => (Lp.memLp ((V : H1amb Ω) i.succ)).integrable one_le_two) hhint hwgV' hw i
  -- the test is nonnegative
  have hVnn : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ ((V : H1amb Ω) 0 x : ℝ) := by
    filter_upwards [hV0] with x hx
    rw [hx]
    exact le_max_right _ _
  have hineq := hsub V hVnn
  -- the transport term vanishes
  have hbsum : (∑ i, ⟪Op.bAct i (U i.succ), (V : H1amb Ω) 0⟫) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [FullEllipticOp.bAct, inner_mulCoeffL_eq, hb, zero_mul, integral_zero]
  -- the zeroth-order term is nonnegative
  have hcterm : 0 ≤ ⟪Op.cAct (U 0), (V : H1amb Ω) 0⟫ := by
    simp only [FullEllipticOp.cAct, inner_mulCoeffL_eq]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_of_ae hc, hV0] with x hcx hx
    rw [hx]
    simp only [Pi.zero_apply, hwdef]
    by_cases hxk : k < u x
    · have hu0 : 0 ≤ u x := hk.trans hxk.le
      exact mul_nonneg (mul_nonneg hcx hu0) (le_max_right _ _)
    · have hle : u x ≤ k := not_lt.mp hxk
      rw [max_eq_right (by linarith), mul_zero]
  -- the principal term is the energy of `V`
  have hprin : (∑ i, ∑ j, ⟪Op.toEllipticCoeff.actL i j (U i.succ), (V : H1amb Ω) j.succ⟫)
      = Op.toEllipticCoeff.bilin Ω V V := by
    rw [EllipticCoeff.bilin_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [EllipticCoeff.inner_actL_eq, EllipticCoeff.inner_actL_eq]
    refine integral_congr_ae ?_
    filter_upwards [hVgrad i, hVgrad j] with x hi hj
    have hi' : ((V : H1amb Ω) i.succ x : ℝ) = h i x := hi
    have hj' : ((V : H1amb Ω) j.succ x : ℝ) = h j x := hj
    rw [hi', hj']
    simp only [hhdef, hgdef]
    split_ifs <;> simp
  rw [hprin, hbsum, add_zero] at hineq
  have henergy := Op.toEllipticCoeff.bilin_self_ge V
  have hS0 : ∑ i : Fin (n + 1), ‖(V : H1amb Ω) i.succ‖ ^ 2 ≤ 0 := by
    have hlam := Op.lam_pos
    have : Op.lam * ∑ i : Fin (n + 1), ‖(V : H1amb Ω) i.succ‖ ^ 2 ≤ Op.lam * 0 := by
      rw [mul_zero]; linarith
    exact le_of_mul_le_mul_left this hlam
  -- Poincaré forces the truncation to vanish
  obtain ⟨C, hC, hpoin⟩ := poincare_H01_of_bounded hΩb
  have hV0norm : ‖(V : H1amb Ω) 0‖ ^ 2 ≤ 0 := (hpoin V V.2).trans (by nlinarith)
  have hV0zero : (V : H1amb Ω) 0 = 0 := by
    have : ‖(V : H1amb Ω) 0‖ = 0 := by nlinarith [norm_nonneg ((V : H1amb Ω) 0)]
    exact norm_eq_zero.mp this
  have hzero : ((V : H1amb Ω) 0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict Ω] 0 := by
    rw [hV0zero]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hV0, hzero] with x hx hx0
  rw [hx0, Pi.zero_apply] at hx
  simp only [hwdef] at hx
  rcases le_or_gt (u x) k with hle | hlt
  · exact hle
  · exfalso
    rw [max_eq_left (by linarith)] at hx
    linarith

end EllipticPdes.Sobolev
