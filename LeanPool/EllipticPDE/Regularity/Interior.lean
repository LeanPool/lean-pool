/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Interior.NormBound


/-!
# Interior H² estimate

The capstone of the interior regularity chain. This file passes to the limit in the uniform
difference-quotient bound of `EllipticPdes.Regularity.Interior.NormBound` to produce the
second weak derivative, then assembles the coordinates into the interior H² estimate.

This module keeps the import path `EllipticPdes.Regularity.Interior` and re-exports the whole
chain, so dependents see the same API as before the file was split.

## Main declarations

* `interior_secondWeakDeriv`: existence of the interior second weak derivative.
* `HasWeakDerivOn`: the region-restricted weak derivative.
* `interior_H2_estimate`: the interior H² estimate.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-! ### Existence of the second weak derivative -/

/-- **Existence of the interior second weak derivative (Evans §6.3.1, VIII.2.1).** For each
`(k, i)` there is a constant `Cd`, fixed before the solution and the datum, such that for every
weak solution `u` of `L u = f` the whole-space extension of `ζ · ∂ᵢu` has an
`L²` weak `k`-derivative `w` with `‖w‖ ≤ Cd (‖f‖ + ‖u₀‖)`: this is the weak-limit converse
`weakDeriv_of_diffQuot_bounded` fed with the uniform difference-quotient bound
`interior_diffQuot_norm_bound`. Because `ζ ≡ 1` on `V`, the restriction of `w` to `V` is
`∂ₖ∂ᵢu` there. -/
theorem interior_secondWeakDeriv (Op : FullEllipticOp d) (hΩm : MeasurableSet Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin d))} (T : CutoffTower Ω V) (k i : Fin d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ w : EucL2 d,
        HasWeakDeriv k (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))) w
        ∧ ‖w‖ ≤ Cd * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  obtain ⟨Cd, hCd0, hCd⟩ := interior_diffQuot_norm_bound Op hΩm hA T k i
  refine ⟨Cd, hCd0, fun u f hu => ?_⟩
  obtain ⟨M, _hM0, hMbd, hMCd⟩ := hCd u f hu
  obtain ⟨w, hw, hwn⟩ :=
    weakDeriv_of_diffQuot_bounded k (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))) M hMbd
  exact ⟨w, hw, le_trans hwn hMCd⟩

/-! ### Assembly of the interior H² estimate -/

/-- **Weak derivative on an open region.** `g'` is the weak `k`-derivative of `g` on `V` if
the integration by parts identity is satisfied against every test function in `V`. This is the
`V`-restricted analogue of `HasWeakDeriv`, and is the `L²`-level statement of `∂ₖ g = g'` on
`V`. -/
def HasWeakDerivOn (V : Set (EuclideanSpace ℝ (Fin d))) (k : Fin d)
    (g g' : Lp ℝ 2 (volume.restrict V)) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ V →
    ∫ x in V, (g x : ℝ) * partialD k φ x = - ∫ x in V, (g' x : ℝ) * φ x

/-- A whole-space weak derivative restricts to a weak derivative on any measurable `V`: test
functions supported in `V` see only the restricted classes, and the whole-space
integration-by-parts identity localises because both integrands vanish off `V`. -/
theorem hasWeakDerivOn_of_hasWeakDeriv {V : Set (EuclideanSpace ℝ (Fin d))}
    (k : Fin d) {g w : EucL2 d} (h : HasWeakDeriv k g w) :
    HasWeakDerivOn V k (restrictL2 g) (restrictL2 w) := by
  intro φ hφc hφcs hφV
  have hzero_dk : ∀ x ∉ V, (g x : ℝ) * partialD k φ x = 0 := by
    intro x hx
    rw [show partialD k φ x = 0 from image_eq_zero_of_notMem_tsupport
      (fun hc => hx (hφV (tsupport_partialD_subset k φ hc))), mul_zero]
  have hzero_phi : ∀ x ∉ V, (w x : ℝ) * φ x = 0 := by
    intro x hx
    rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hφV hc)), mul_zero]
  calc ∫ x in V, (restrictL2 g x : ℝ) * partialD k φ x
      = ∫ x in V, (g x : ℝ) * partialD k φ x := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_restrictL2 g] with x hx; rw [hx]
    _ = ∫ x, (g x : ℝ) * partialD k φ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero_dk
    _ = - ∫ x, (w x : ℝ) * φ x := h φ hφc hφcs
    _ = - ∫ x in V, (w x : ℝ) * φ x := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero_phi]
    _ = - ∫ x in V, (restrictL2 w x : ℝ) * φ x := by
        refine congrArg Neg.neg (integral_congr_ae ?_)
        filter_upwards [coeFn_restrictL2 w] with x hx; rw [hx]

/-- **Interior H² estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg-Trudinger, *Elliptic Partial Differential Equations of Second Order*, Theorem 8.8).**
For a weak solution `u ∈ H₀¹(Ω)` of `L u = f` with `W^{1,∞}` principal coefficients,
in the pointwise form of `IsLipCoeff`, and bounded transport and zeroth-order coefficients,
    and for any compact `V ⋐ Ω`,
the second weak derivatives exist in `L²(V)` and are bounded by the data: for every direction
pair `(k, i)` there is a weak `k`-derivative `wki` of `∂ᵢu` on `V` (that is, `∂ₖ∂ᵢu ∈ L²(V)`)
with `‖∂ₖ∂ᵢu‖_{L²(V)} + ‖∂ᵢu‖_{L²(V)} + ‖u‖_{L²(V)} ≤ C (‖f‖ + ‖u‖)`. The constant is
quantified before the solution and the datum, so it depends only on the data
(`λ, Λ, A₁, d, ‖b‖∞, ‖c‖∞`, the cutoff tower for `V ⋐ Ω`) and on neither `u` nor `f`. This is
the `L²`-level statement that `u ∈ H²_loc(Ω)` with the interior estimate. -/
theorem interior_H2_estimate {n : ℕ} (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsLipCoeff Op.toEllipticCoeff)
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∀ k i : Fin (n + 1),
      ∃ wki : Lp ℝ 2 (volume.restrict V),
        HasWeakDerivOn V k
            (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
          ‖wki‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
            + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ C * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
  classical
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  set T := cutoffTowerOfIsCompactSubsetIsOpen hVc hΩo hVΩ with hT
  set dcoef : ℝ := Real.sqrt ((1 + 4 * Op.gardingγ) / (2 * Op.lam)) with hdcoefdef
  have hdcoef0 : (0 : ℝ) ≤ dcoef := Real.sqrt_nonneg _
  -- Per-`(k, i)` localised statement with a data-only growth constant. The `V`-restriction of
  -- the cutoff class `ζ · ∂ᵢu` coincides with that of `∂ᵢu`, because `ζ ≡ 1` on `V`.
  have hstep : ∀ k i : Fin (n + 1), ∃ G : ℝ, ∀ (u : H01 Ω) (f : L2D Ω),
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ wki : Lp ℝ 2 (volume.restrict V),
      HasWeakDerivOn V k (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))) wki ∧
      ‖wki‖ + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
          + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
        ≤ G * (‖f‖ + ‖(u : H1amb Ω) 0‖) := by
    intro k i
    obtain ⟨Cd, _hCd0, hCd⟩ := interior_secondWeakDeriv Op hΩm hA T k i
    refine ⟨Cd + dcoef + 1, fun u f hu => ?_⟩
    obtain ⟨w, hw, hwCd⟩ := hCd u f hu
    let P: ℝ := ‖f‖ + ‖(u : H1amb Ω) 0‖
    have hPdef : P = ‖f‖ + ‖(u : H1amb Ω) 0‖ := rfl
    have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; positivity
    have hdiu : ∀ j : Fin (n + 1), ‖(u : H1amb Ω) j.succ‖ ≤ dcoef * P := fun j =>
      firstOrder_gradNorm_le Op u f hu j
    have hAB : (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))
          : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
        =ᵐ[volume.restrict V]
        (extendL2 hΩm ((u : H1amb Ω) i.succ) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := by
      have hmt : (mulTest T.hζ ((u : H1amb Ω) i.succ)
            : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          =ᵐ[volume.restrict V] fun x => T.ζ x * ((u : H1amb Ω) i.succ x : ℝ) :=
        (mulTest_coeFn T.hζ ((u : H1amb Ω) i.succ)).filter_mono
          (ae_mono (Measure.restrict_mono hVΩ le_rfl))
      filter_upwards [ae_restrict_of_ae
          (coeFn_extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))),
        ae_restrict_of_ae (coeFn_extendL2 hΩm ((u : H1amb Ω) i.succ)), hmt,
        ae_restrict_mem hVm] with x he1 he2 hmtx hxV
      rw [he1, he2, Set.indicator_of_mem (hVΩ hxV), Set.indicator_of_mem (hVΩ hxV), hmtx]
      simp [T.zeta_eqOn_one hxV]
    have hDiuEq : restrictL2 (Ω := V) (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ)))
        = restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)) := by
      apply Lp.ext
      filter_upwards [coeFn_restrictL2 (Ω := V)
          (extendL2 hΩm (mulTest T.hζ ((u : H1amb Ω) i.succ))),
        coeFn_restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ)), hAB] with x h1 h2 h3
      rw [h1, h2, h3]
    refine ⟨restrictL2 w, ?_, ?_⟩
    · rw [← hDiuEq]; exact hasWeakDerivOn_of_hasWeakDeriv k hw
    · have h1 : ‖restrictL2 (Ω := V) w‖ ≤ Cd * P := le_trans (norm_restrictL2_le w) hwCd
      have h2 : ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖ ≤ dcoef * P := by
        refine le_trans (norm_restrictL2_le _) ?_
        rw [norm_extendL2]; exact hdiu i
      have h3 : ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖ ≤ 1 * P := by
        refine le_trans (norm_restrictL2_le _) ?_
        rw [norm_extendL2, one_mul, hPdef]
        linarith only [norm_nonneg f]
      calc ‖restrictL2 (Ω := V) w‖ + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))‖
              + ‖restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))‖
          ≤ Cd * P + dcoef * P + 1 * P := add_le_add (add_le_add h1 h2) h3
        _ = (Cd + dcoef + 1) * P := by ring
  choose G hG using hstep
  refine ⟨∑ k : Fin (n + 1), ∑ i : Fin (n + 1), |G k i|,
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro u f hu k i
  obtain ⟨wki, hHWD, hbound⟩ := hG k i u f hu
  refine ⟨wki, hHWD, le_trans hbound ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc G k i ≤ |G k i| := le_abs_self _
    _ ≤ ∑ i' : Fin (n + 1), |G k i'| :=
        Finset.single_le_sum (f := fun i' => |G k i'|)
          (fun i' _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ k' : Fin (n + 1), ∑ i' : Fin (n + 1), |G k' i'| :=
        Finset.single_le_sum (f := fun k' => ∑ i' : Fin (n + 1), |G k' i'|)
          (fun k' _ => Finset.sum_nonneg (fun i' _ => abs_nonneg _)) (Finset.mem_univ k)

end EllipticPdes.Regularity
