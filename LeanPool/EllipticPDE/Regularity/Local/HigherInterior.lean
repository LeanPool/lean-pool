/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Regularity.Local.Datum


/-!
# Higher interior regularity for a weak solution in `H¹`

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 (p. 332): for
`a^{ij}, b^i, c ∈ C^{m+1}(U)`, `f ∈ H^m(U)` and a weak solution `u ∈ H¹(U)` of `L u = f`,
`u ∈ H^{m+2}_loc(U)` with `‖u‖_{H^{m+2}(V)} ≤ C (‖f‖_{H^m(U)} + ‖u‖_{L²(U)})` for `V ⋐ U`.

The statement here is for a local weak solution `U ∈ W12 Ω` with no boundary condition. It is
read off `higher_interior_regularity`, stated for `H₀¹` solutions, through the cutoff reduction,
by induction on the order.

* Order `k` at `V`. Take `η = 1` near `V`, supported in `Ω`. `η U ∈ H₀¹(Ω)` solves an equation
  whose datum pairs `f` and the coordinates of `U` against weights supported in `tsupport η`
  (`reduction_testFn`). If every coordinate of `U` has `k` weak derivatives on `tsupport η`, the
  datum has `k` weak derivatives on `Ω` (`exists_reductionDatum`), the `H₀¹` theorem at order
  `k` gives `η U₀` in `H^{k+2}(V)`, and `η = 1` on `V`
  (`restrictL2_extendL2_cutoffMul`) makes that `U₀`.
* The hypothesis at order `k + 1` on a compact `W` is the conclusion at order `k` on
  `tsupport θ` for `θ = 1` near `W`: `U₀` has `k + 2` weak derivatives there, and on `W` the
  first of them are the gradient coordinates of `U` by uniqueness of the weak derivative after
  the cutoff `θ` (`exists_collarFamily_of_weakDerivOn`). At order `0` the hypothesis asks for
  the `L²` norms of the coordinates on `W`, which the Caccioppoli estimate
  `exists_norm_mulTest_grad_le` bounds by `‖f‖ + ‖U₀‖`.

The bound has `‖U₀‖_{L²(Ω)}` on the right, as in Evans.

## Main declarations

* `LocalRegularityAt`: the order-`k` conclusion for local weak solutions.
* `LocalFamiliesAt`: the order-`k` hypothesis on the coordinates of the solution.
* `localRegularityAt_of_localFamiliesAt`, `localFamiliesAt_zero`, `localFamiliesAt_succ`.
* `higher_interior_regularity_W12`: the theorem, with `a^{ij} ∈ W^{k+1,∞}` and `C¹`, and
  `b^i, c ∈ W^{k,∞}`.
* `localRegularityAt_zero_of_isC1Coeff`: order zero from `C¹` principal coefficients alone.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Order-`k` interior conclusion for local weak solutions.** For every compact `V ⊆ Ω` there
is a constant, quantified before the solution and the datum, bounding every weak derivative of
`U₀` of order at most `k + 2` on `V` by `M + ‖U₀‖`, for a datum with `k` weak derivatives
bounded by `M`. -/
def LocalRegularityAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact V → V ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      IsLocalWeakSolution Op Ω U f →
      ∃ hu : HasIteratedWeakDerivOn V (k + 2) (restrictL2 (Ω := V) (extendL2 hΩm (U 0))),
        IteratedL2Bound hu (C * (M + ‖U 0‖))

/-- **Order-`k` hypothesis on the coordinates.** For every compact `W ⊆ Ω` every coordinate of
a local weak solution, the function and its gradient alike, has `k` weak derivatives on `W`,
bounded by `M + ‖U₀‖` with a constant quantified before the solution and the datum. -/
def LocalFamiliesAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {W : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact W → W ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      IsLocalWeakSolution Op Ω U f →
      ∀ j : Fin (n + 2),
        ∃ H : HasIteratedWeakDerivOn W k (restrictL2 (Ω := W) (extendL2 hΩm (U j))),
          IteratedL2Bound H (C * (M + ‖U 0‖))

/-- **Invisibility of a cutoff on a set where it is one.** For `ζ = 1` on `W ⊆ Ω`, cutting
`ζ g` down to `W` is cutting `g` down to `W`. -/
theorem restrictL2_extendL2_mulTest_of_eqOn {Ω W : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩm : MeasurableSet Ω) (hWm : MeasurableSet W) (hWΩ : W ⊆ Ω)
    {ζ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hζ : IsTestFn Ω ζ) (hζW : Set.EqOn ζ 1 W)
    (g : L2D Ω) :
    restrictL2 (Ω := W) (extendL2 hΩm (mulTest hζ g))
      = restrictL2 (Ω := W) (extendL2 hΩm g) := by
  apply Lp.ext
  filter_upwards [coeFn_restrictL2 (Ω := W) (extendL2 hΩm (mulTest hζ g)),
    coeFn_restrictL2 (Ω := W) (extendL2 hΩm g),
    ae_restrict_of_ae (coeFn_extendL2 hΩm (mulTest hζ g)),
    ae_restrict_of_ae (coeFn_extendL2 hΩm g),
    ae_restrict_of_ae_restrict_of_subset hWΩ (mulTest_coeFn hζ g), ae_restrict_mem hWm]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, Set.indicator_of_mem (hWΩ h6), Set.indicator_of_mem (hWΩ h6), h5,
    hζW h6, Pi.one_apply, one_mul]

/-- **Hypothesis at order zero.** At order zero the hypothesis on the coordinates asks only for
their `L²` norms on `W`. `‖U₀‖` bounds the function, and the gradient, cut off by `ζ = 1` near
`W`, is bounded by `‖f‖ + ‖U₀‖` through the Caccioppoli estimate. -/
theorem localFamiliesAt_zero (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω) :
    LocalFamiliesAt Op hΩm 0 := by
  intro W hWc hWΩ
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  obtain ⟨ζ, hζ, hζ1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hWc hΩo hWΩ
  have hζW : Set.EqOn ζ 1 W := fun x hx => hζ1.self_of_nhdsSet x hx
  obtain ⟨Cg, hCg0, hCg⟩ := exists_norm_mulTest_grad_le Op hΩo hζ
  refine ⟨1 + Cg, by linarith, fun U f M hfk hM hsol j =>
    ⟨HasIteratedWeakDerivOn.zero _, ?_⟩⟩
  intro α _
  have hM0 : 0 ≤ M := le_trans (norm_nonneg f) hM.norm_le
  have hU0 := norm_nonneg (U 0)
  have hfM : ‖f‖ ≤ M := hM.norm_le
  change ‖restrictL2 (Ω := W) (extendL2 hΩm (U j))‖ ≤ _
  refine Fin.cases ?_ (fun i => ?_) j
  · calc ‖restrictL2 (Ω := W) (extendL2 hΩm (U 0))‖ ≤ ‖extendL2 hΩm (U 0)‖ :=
          norm_restrictL2_le _
      _ = ‖U 0‖ := norm_extendL2 hΩm _
      _ ≤ (1 + Cg) * (M + ‖U 0‖) := by nlinarith
  · rw [← restrictL2_extendL2_mulTest_of_eqOn hΩm hWm hWΩ hζ hζW (U i.succ)]
    have hg := hCg U f hsol i
    calc ‖restrictL2 (Ω := W) (extendL2 hΩm (mulTest hζ (U i.succ)))‖
        ≤ ‖extendL2 hΩm (mulTest hζ (U i.succ))‖ := norm_restrictL2_le _
      _ = ‖mulTest hζ (U i.succ)‖ := norm_extendL2 hΩm _
      _ ≤ Cg * (‖f‖ + ‖U 0‖) := hg
      _ ≤ (1 + Cg) * (M + ‖U 0‖) := by nlinarith

/-- **Hypothesis at `k + 1` from the conclusion at `k`.** For a compact `W`, the conclusion at
order `k` on `tsupport θ`, with `θ = 1` near `W`, gives `U₀` its `k + 2` weak derivatives on
`W`, whose first entries are the gradient coordinates of `U` by
`exists_collarFamily_of_weakDerivOn`. Each coordinate then has `k + 1`. -/
theorem localFamiliesAt_succ (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    {k : ℕ} (hk : LocalRegularityAt Op hΩm k) :
    LocalFamiliesAt Op hΩm (k + 1) := by
  classical
  intro W hWc hWΩ
  obtain ⟨θ, hθ, hθ1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hWc hΩo hWΩ
  have hθN : Set.EqOn θ 1 W := fun x hx => hθ1.self_of_nhdsSet x hx
  have hWT : W ⊆ tsupport θ := fun x hx =>
    subset_tsupport _ (by rw [Function.mem_support, hθN hx]; exact one_ne_zero)
  have hTm : MeasurableSet (tsupport θ) := (isClosed_tsupport θ).measurableSet
  have hWm : MeasurableSet W := hWc.isClosed.measurableSet
  have hθT : IsTestFn (tsupport θ) θ := ⟨hθ.1, hθ.2.1, subset_rfl⟩
  obtain ⟨C, hC0, hC⟩ := hk hθ.2.1 hθ.2.2
  refine ⟨C, hC0, fun U f M hfk hM hsol j => ?_⟩
  obtain ⟨HuT, hHuT⟩ :=
    hC U f M (hfk.mono (Nat.le_succ k)) (hM.mono_order (Nat.le_succ k)) hsol
  have hDT : ∀ i : Fin (n + 1), HasWeakDerivOn (tsupport θ) i
      (restrictL2 (Ω := tsupport θ) (extendL2 hΩm (U 0)))
      (restrictL2 (Ω := tsupport θ) (extendL2 hΩm (U i.succ))) := fun i =>
    (hasWeakDerivOn_of_mem_W12 hsol.1 i).restrict hΩm hTm hθ.2.2
  obtain ⟨HuW, hHuW, hDW⟩ := exists_collarFamily_of_weakDerivOn (Dg := fun i => U i.succ)
    hΩm hTm hWm hWT hθT hθN hDT (m := k + 1) HuT hHuT
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨HuW.mono (Nat.le_succ _), hHuW.mono_order (Nat.le_succ _)⟩
  · exact ⟨(HuW.deriv i).congr (hDW i), (hHuW.deriv i).congr⟩

/-- **Conclusion at order `k` from the hypothesis at order `k`.** The step that reads the
`H₀¹` theorem `higher_interior_regularity` off the cutoff reduction: for `η = 1` near `V`, the
datum of `η U` has `k` weak derivatives once the coordinates of `U` have them on `tsupport η`,
and the conclusion for `η U` on `V` is the conclusion for `U`. -/
theorem localRegularityAt_of_localFamiliesAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1)) (hbc : IsWkInftyLower Op k)
    (hfam : LocalFamiliesAt Op hΩm k) :
    LocalRegularityAt Op hΩm k := by
  classical
  intro V hVc hVΩ
  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  obtain ⟨η, hη, hη1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hVc hΩo hVΩ
  have hWm : MeasurableSet (tsupport η) := (isClosed_tsupport η).measurableSet
  have hηW : IsTestFn (tsupport η) η := ⟨hη.1, hη.2.1, subset_rfl⟩
  obtain ⟨CW, hCW0, hW⟩ := hfam hη.2.1 hη.2.2
  obtain ⟨K, hK0, hDat⟩ :=
    exists_reductionDatum Op hΩm hWm hη.2.2 hA hbc hηW
  obtain ⟨CV, hCV0, hH01⟩ := higher_interior_regularity Op hΩm hΩo hA1.toIsLipCoeff k hA hbc hVc hVΩ
  obtain ⟨Mη, hMη⟩ := exists_abs_bound hη
  have hMη0 : 0 ≤ Mη := le_trans (abs_nonneg _) (hMη 0)
  refine ⟨CV * (K * (CW + 1) + Mη),
    mul_nonneg hCV0 (add_nonneg (mul_nonneg hK0 (by linarith)) hMη0),
    fun U f M hfk hM hsol => ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg f) hM.norm_le
  have hU0 : 0 ≤ ‖U 0‖ := norm_nonneg (U 0)
  have hMU : 0 ≤ M + ‖U 0‖ := add_nonneg hM0 hU0
  set B : ℝ := (CW + 1) * (M + ‖U 0‖) with hB
  choose H hH using hW U f M hfk hM hsol
  obtain ⟨F, HF, hFbd, hFpair⟩ := hDat U f H hfk B
    (fun j => (hH j).mono_const (by rw [hB]; nlinarith))
    (hM.mono_const (by rw [hB]; nlinarith))
  have hweak : ∀ w : H01 Ω,
      Op.fullBilin Ω ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ w
        = ∫ x in Ω, (F x : ℝ) * ((w : H1amb Ω) 0 x : ℝ) := by
    refine weakForm_of_testFn Op _ F (fun v hv => ?_)
    rw [reduction_testFn Op hΩo hA.coeffWeakGrad hsol hη hv, hFpair v hv.1 hv.2.1]
  obtain ⟨hu, hub⟩ := hH01 ⟨cutoffMul hη U, cutoffMul_mem_H01_of_mem_W12 hΩo hη hsol.1⟩ F
    (K * B) HF hFbd hweak
  refine ⟨hu.congr (restrictL2_extendL2_cutoffMul hΩm hVm hVΩ hη hη1 U 0), ?_⟩
  refine hub.congr.mono_const ?_
  have hη0 : ‖(cutoffMul hη U) 0‖ ≤ Mη * ‖U 0‖ := by
    rw [cutoffMul_apply_zero]
    exact norm_le_of_ae_mul hη.continuous.measurable (Eventually.of_forall hMη)
      (mulTest_coeFn hη (U 0))
  change CV * (K * B + ‖(cutoffMul hη U) 0‖) ≤ _
  have h1 : K * B + ‖(cutoffMul hη U) 0‖ ≤ (K * (CW + 1) + Mη) * (M + ‖U 0‖) := by
    rw [hB]
    nlinarith [mul_nonneg hMη0 hM0]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 hCV0

/-- An essentially bounded measurable function is in `W^{0,∞}`: the family is constant and no
weak derivative is asked. -/
def isWkInftyZero {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : Measurable f) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))), |f x| ≤ M) :
    IsWkInfty f 0 where
  D _ := f
  D_nil := rfl
  D_meas _ _ := hf
  D_step _ _ h := absurd h (Nat.not_lt_zero _)
  bound _ := M
  bound_nonneg _ := hM0
  ess_bdd _ _ := hM

/-- The lower-order coefficients of every `FullEllipticOp` are in `W^{0,∞}`. -/
def isWkInftyLowerZero (Op : FullEllipticOp (n + 1)) : IsWkInftyLower Op 0 where
  bReg i := isWkInftyZero (Op.b_meas i) Op.Bsup_nonneg (Op.b_bdd i)
  cReg := isWkInftyZero Op.c_meas Op.Csup_nonneg Op.c_bdd
  bound _ := max Op.Bsup Op.Csup
  bound_nonneg _ := le_max_of_le_left Op.Bsup_nonneg
  b_le _ _ := le_max_left _ _
  c_le _ := le_max_right _ _

/-- **Higher interior regularity for a weak solution in `H¹` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 2, p. 332).** A local weak solution `U ∈ W12 Ω` of
`L U = f`, with no boundary condition, `W^{k+1,∞}` principal coefficients of class `C¹`,
`W^{k,∞}` lower-order coefficients and a datum with `k` weak derivatives bounded by `M`, has weak
derivatives of every order up to `k + 2` on each compact `V ⊆ Ω`, bounded by `C (M + ‖U₀‖)`
with `C` quantified before the solution and the datum. -/
theorem higher_interior_regularity_W12 (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 1))
    (hbc : IsWkInftyLower Op k) :
    LocalRegularityAt Op hΩm k := by
  induction k with
  | zero =>
    exact localRegularityAt_of_localFamiliesAt Op hΩm hΩo hA1 hA hbc
      (localFamiliesAt_zero Op hΩm hΩo)
  | succ j ih =>
    exact localRegularityAt_of_localFamiliesAt Op hΩm hΩo hA1 hA hbc
      (localFamiliesAt_succ Op hΩm hΩo (ih (hA.mono (by omega)) (hbc.mono (by omega))))

/-- **Order zero with `C¹` principal coefficients alone.** The interior `H²` conclusion for a
local weak solution asks nothing of the lower-order coefficients beyond `FullEllipticOp`, and
nothing of the principal part beyond a bounded derivative (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1, Theorem 1, p. 327). -/
theorem localRegularityAt_zero_of_isC1Coeff (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) :
    LocalRegularityAt Op hΩm 0 :=
  higher_interior_regularity_W12 Op hΩm hΩo hA1 0 hA1.toIsCkCoeff.toIsWkInftyCoeff
    (isWkInftyLowerZero Op)

end EllipticPdes.Regularity
