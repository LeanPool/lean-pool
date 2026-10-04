/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.Local.HigherInterior
public import LeanPool.EllipticPDE.Regularity.Localise.FiniteOrder
public import LeanPool.EllipticPDE.Regularity.IteratedNorm


/-!
# Interior regularity with coefficients on the domain

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1 poses its interior regularity theorems
on a bounded open `U ⊂ ℝⁿ` for coefficients given on `U` alone, with no bound on `a^{ij}` over
`U`, and for `u ∈ H¹(U)` with no boundary condition. The local chain of this development
(`higher_interior_regularity_W12`) runs on a global `FullEllipticOp`. This file reads the local
chain back on plain functions on `U`.

For an open `V` with `closure V` compact in `U`, `exists_localOp_C1` or `exists_localOp_Ck` gives an
open `W` between `closure V` and `U` and a global operator agreeing with the given coefficients on
`W`. The solution restricted to `W` is a local weak solution of that operator in `W12 W`
(`isLocalWeakSolution_of_localWeakSol`), and the local chain on `W` at the compact `closure V`
gives the family on `V` (`exists_family_of_localWeakSol`). The constant is fixed by `V`, `U` and
the coefficients before the solution and the datum are, as in Evans.

## Main declarations

* `exists_family_of_localWeakSol`: the transfer from a global operator agreeing with the
  coefficients near `closure V`.
* `interior_H2_regularity_evans`: Theorem 1 with the unnecessary boundedness and symmetry
  assumptions omitted.
* `higher_interior_regularity_evans`: Theorem 2 with the unnecessary boundedness and symmetry
  assumptions omitted.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {d : ℕ}

/-- Extending the class of `g` on `U` by zero and restricting to `V ⊆ U` gives the class of `g`
on `V`. -/
theorem restrictL2_extendL2_toLp {U V : Set (EuclideanSpace ℝ (Fin d))} (hUm : MeasurableSet U)
    (hVm : MeasurableSet V) (hVU : V ⊆ U) {g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : MemLp g 2 (volume.restrict U)) (hV : MemLp g 2 (volume.restrict V)) :
    restrictL2 (Ω := V) (extendL2 hUm (hU.toLp g)) = hV.toLp g := by
  apply Lp.ext
  filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hUm (hU.toLp g)),
    ae_restrict_of_ae (coeFn_extendL2 hUm (hU.toLp g)),
    ae_restrict_of_ae_restrict_of_subset hVU hU.coeFn_toLp, hV.coeFn_toLp,
    ae_restrict_mem hVm] with x h1 h2 h3 h4 h5
  rw [h1, h2, Set.indicator_of_mem (hVU h5), h3, h4]

/-- The `L²` norm over a smaller set is smaller. -/
theorem norm_toLp_le_of_subset {U V : Set (EuclideanSpace ℝ (Fin d))} (hVU : V ⊆ U)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hU : MemLp g 2 (volume.restrict U))
    (hV : MemLp g 2 (volume.restrict V)) : ‖hV.toLp g‖ ≤ ‖hU.toLp g‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hU.eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl))

/-- A function in `L^∞(U)` is essentially bounded on `U`. -/
theorem exists_ae_abs_le_of_memLp_top {U : Set (EuclideanSpace ℝ (Fin d))}
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : MemLp g ⊤ (volume.restrict U)) :
    ∃ B : ℝ, ∀ᵐ x ∂(volume.restrict U), |g x| ≤ B := by
  refine ⟨(eLpNorm g ⊤ (volume.restrict U)).toReal, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := volume.restrict U)] with x hx
  rw [← eLpNorm_exponent_top hg.aestronglyMeasurable] at hx
  have h := ENNReal.toReal_mono hg.eLpNorm_ne_top hx
  rwa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] at h

/-- **Transfer of the local chain to plain functions on `U`.** Let `Op` agree with `a, b, c` on an
open `W ⊆ U` (everywhere for `a`, almost everywhere for `b` and `c`) and satisfy the order-`k`
conclusion of the local chain on `W`. For a compact `K ⊆ W` and a measurable `V ⊆ K` there is a
constant such that every `u` with weak gradient `G`, both in `L²(U)`, solving the local weak
formulation on `U` with a datum `f` whose family of `k` weak derivatives on `U` is bounded by
`M`, has weak derivatives up to order `k + 2` on `V`, bounded by `C (M + ‖u‖_{L²(U)})`. -/
theorem exists_family_of_localWeakSol {n : ℕ} {U W K V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U) (hWo : IsOpen W) (hWU : W ⊆ U) (hK : IsCompact K) (hKW : K ⊆ W)
    (hVm : MeasurableSet V) (hVK : V ⊆ K) (Op : FullEllipticOp (n + 1)) {k : ℕ}
    (hreg : LocalRegularityAt Op hWo.measurableSet k)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Fin (n + 1) → Fin (n + 1) → ℝ}
    {b : EuclideanSpace ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ} {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (ha : ∀ x ∈ W, Op.a x = a x) (hb : ∀ i, ∀ᵐ x ∂(volume.restrict W), Op.b x i = b x i)
    (hc : ∀ᵐ x ∂(volume.restrict W), Op.c x = c x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      (G : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      (hf : MemLp f 2 (volume.restrict U)) (hu : MemLp u 2 (volume.restrict U)),
      (∀ i, MemLp (G i) 2 (volume.restrict U)) →
      ∀ (Hf : HasIteratedWeakDerivOn U k (hf.toLp f)) (M : ℝ), IteratedL2Bound Hf M →
      HasWeakGradOn U u G → LocalWeakSol U a b c f u G →
      ∃ H : HasIteratedWeakDerivOn V (k + 2)
          ((hu.mono_measure (Measure.restrict_mono (hVK.trans (hKW.trans hWU)) le_rfl)).toLp u),
        IteratedL2Bound H (C * (M + ‖hu.toLp u‖)) := by
  have hUm := hU.measurableSet
  have hWm := hWo.measurableSet
  have hKm := hK.isClosed.measurableSet
  obtain ⟨C, hC0, hCK⟩ := hreg hK hKW
  refine ⟨C, hC0, fun f u G hf hu hG Hf M hM hgrad hsol => ?_⟩
  have hWr : volume.restrict W ≤ volume.restrict U := Measure.restrict_mono hWU le_rfl
  have hfW : MemLp f 2 (volume.restrict W) := hf.mono_measure hWr
  have huW : MemLp u 2 (volume.restrict W) := hu.mono_measure hWr
  have hGW : ∀ i, MemLp (G i) 2 (volume.restrict W) := fun i => (hG i).mono_measure hWr
  have hsolW : LocalWeakSol W Op.a Op.b Op.c f u G :=
    (hsol.mono hWU).congr_ae
      (fun i j => by
        filter_upwards [ae_restrict_mem hWm] with x hx
        rw [ha x hx])
      (fun i => by filter_upwards [hb i] with x hx; rw [hx])
      (by filter_upwards [hc] with x hx; rw [hx]) (Eventually.of_forall fun _ => rfl)
  have hsolA := isLocalWeakSolution_of_localWeakSol Op huW hGW hfW (hgrad.mono hWU) hsolW
  -- The datum's family on `W`.
  have hfeq := restrictL2_extendL2_toLp hUm hWm hWU hf hfW
  obtain ⟨HK, hHK⟩ := hCK _ (hfW.toLp f) M ((Hf.restrict hUm hWm hWU).congr hfeq)
    (IteratedL2Bound.restrict hM).congr hsolA
  -- The family on `V`, identified with the class of `u` there.
  have h0 : ((WithLp.toLp 2 (Fin.cons (huW.toLp u) fun k => (hGW k).toLp (G k)) : H1amb W) 0)
      = huW.toLp u := by
    change ((Fin.cons (huW.toLp u) fun k => (hGW k).toLp (G k) : Fin (n + 2) → L2D W) 0) = _
    rw [Fin.cons_zero]
  have hid : restrictL2 (Ω := V) (extendL2 hKm (restrictL2 (Ω := K) (extendL2 hWm
      ((WithLp.toLp 2 (Fin.cons (huW.toLp u) fun k => (hGW k).toLp (G k)) : H1amb W) 0))))
      = (hu.mono_measure (Measure.restrict_mono (hVK.trans (hKW.trans hWU)) le_rfl)).toLp u := by
    rw [h0, restrictL2_extendL2_toLp hWm hKm hKW huW (huW.mono_measure
        (Measure.restrict_mono hKW le_rfl)),
      restrictL2_extendL2_toLp hKm hVm hVK]
  refine ⟨(HK.restrict hKm hVm hVK).congr hid, (IteratedL2Bound.restrict hHK).congr.mono_const ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM.norm_le
  have hnorm : ‖(WithLp.toLp 2 (Fin.cons (huW.toLp u) fun k => (hGW k).toLp (G k)) : H1amb W) 0‖
      ≤ ‖hu.toLp u‖ := by
    rw [h0]; exact norm_toLp_le_of_subset hWU hu huW
  exact mul_le_mul_of_nonneg_left (by linarith) hC0

/-- In dimension zero every class has a family of every order, the family being constant, since
there is no direction to differentiate in. -/
def HasIteratedWeakDerivOn.ofFinZero {V : Set (EuclideanSpace ℝ (Fin 0))} (k : ℕ) (u : L2D V) :
    HasIteratedWeakDerivOn V k u where
  D _ := u
  D_nil := rfl
  D_step m := m.elim0

/-- The coefficients of Theorem 1 as a `C1OpOn`, with one essential bound for all transport
components. -/
def C1OpOn.ofMemLp {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    (hb : ∀ i, MemLp (fun x => b x i) ⊤ (volume.restrict U))
    (hc : MemLp c ⊤ (volume.restrict U)) {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Fin d → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) : C1OpOn d U where
  a := a
  lam := θ
  lam_pos := hθ
  contDiffOn := ha
  elliptic := hell
  b := b
  c := c
  Bsup := ∑ i, max (Classical.choose (exists_ae_abs_le_of_memLp_top (hb i))) 0
  Csup := Classical.choose (exists_ae_abs_le_of_memLp_top hc)
  b_aesm i := (hb i).aestronglyMeasurable
  c_aesm := hc.aestronglyMeasurable
  b_bdd i := by
    filter_upwards [Classical.choose_spec (exists_ae_abs_le_of_memLp_top (hb i))] with x hx
    exact (hx.trans (le_max_left _ 0)).trans (Finset.single_le_sum
      (f := fun i => max (Classical.choose (exists_ae_abs_le_of_memLp_top (hb i))) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ i))
  c_bdd := Classical.choose_spec (exists_ae_abs_le_of_memLp_top hc)

/-- **Interior `H²`-regularity (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 1, p. 327), with the unnecessary boundedness and symmetry assumptions omitted.** `U ⊆ ℝᵈ` is
  open,
`a^{ij} ∈ C¹(U)`, `b^i, c ∈ L^∞(U)`, the operator is uniformly elliptic with a constant `θ > 0`
for almost every `x ∈ U` (§6.1.1, (4)). For each open `V ⊂⊂ U` there is
a constant `C`, depending on `V`, `U` and the coefficients alone, such that every
`u ∈ H¹(U)`, given as `u` and its weak gradient `G` in `L²(U)`, that is a weak solution of
`L u = f` in `U` for `f ∈ L²(U)` has weak derivatives up to order two in `L²(V)`, which is
`u ∈ H²(V)`, with

`‖u‖_{H²(V)} ≤ C (‖f‖_{L²(U)} + ‖u‖_{L²(U)})`.

Since every `V ⊂⊂ U` is covered, this is also `u ∈ H²_loc(U)`. The norm is `iteratedNorm`, the
sum over lists of directions. The weak formulation is tested against `C_c^∞(U)`, as in Remark
(ii) after the theorem; a solution tested against `H₀¹(U)` is one. The boundedness of `U` and
  symmetry of `a^{ij}` assumed by Evans are unnecessary here. -/
theorem interior_H2_regularity_evans {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    (hb : ∀ i, MemLp (fun x => b x i) ⊤ (volume.restrict U))
    (hc : MemLp c ⊤ (volume.restrict U)) {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Fin d → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hVo : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f u : EuclideanSpace ℝ (Fin d) → ℝ)
      (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
      (hf : MemLp f 2 (volume.restrict U)) (hu : MemLp u 2 (volume.restrict U)),
      (∀ i, MemLp (G i) 2 (volume.restrict U)) → HasWeakGradOn U u G →
      LocalWeakSol U a b c f u G →
      ∃ H : HasIteratedWeakDerivOn V 2
          ((hu.mono_measure (Measure.restrict_mono (subset_closure.trans hVU) le_rfl)).toLp u),
        iteratedNorm H ≤ C * (‖hf.toLp f‖ + ‖hu.toLp u‖) := by
  have hVU' : V ⊆ U := subset_closure.trans hVU
  cases d with
  | zero =>
    refine ⟨Real.sqrt (listCount 0 2), Real.sqrt_nonneg _,
      fun f u G hf hu _ _ _ => ⟨HasIteratedWeakDerivOn.ofFinZero 2 _, ?_⟩⟩
    have hB : IteratedL2Bound (HasIteratedWeakDerivOn.ofFinZero 2
        ((hu.mono_measure (Measure.restrict_mono hVU' le_rfl)).toLp u)) ‖hu.toLp u‖ :=
      fun _ _ => norm_toLp_le_of_subset hVU' hu
        (hu.mono_measure (Measure.restrict_mono hVU' le_rfl))
    refine (iteratedNorm_le hB).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    linarith [norm_nonneg (hf.toLp f)]
  | succ n =>
    obtain ⟨Op, W, hWo, hKW, hWU, ⟨hA1⟩, ha', hb', hc'⟩ :=
      exists_localOp_C1 (C1OpOn.ofMemLp ha hb hc hθ hell) hU hVc hVU
    obtain ⟨C, hC0, hCf⟩ := exists_family_of_localWeakSol hU hWo hWU hVc hKW hVo.measurableSet
      subset_closure Op (localRegularityAt_zero_of_isC1Coeff Op hWo.measurableSet hWo hA1)
      ha' hb' hc'
    refine ⟨Real.sqrt (listCount (n + 1) 2) * C, mul_nonneg (Real.sqrt_nonneg _) hC0,
      fun f u G hf hu hG hgrad hsol => ?_⟩
    obtain ⟨H, hH⟩ := hCf f u G hf hu hG (HasIteratedWeakDerivOn.zero _) ‖hf.toLp f‖
      (fun _ _ => le_rfl) hgrad hsol
    exact ⟨H, (iteratedNorm_le hH).trans (le_of_eq (by ring))⟩

/-- **Higher interior regularity (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1,
Theorem 2, p. 332), with the unnecessary boundedness and symmetry assumptions omitted.** Let `m` be
  a nonnegative integer, `U ⊆ ℝᵈ`
open, `a^{ij}, b^i, c ∈ C^{m+1}(U)`, the operator uniformly elliptic with a constant
`θ > 0` for almost every `x ∈ U` (§6.1.1, (4)). For each open `V ⊂⊂ U`
there is a constant `C`, depending on `m`, `U`, `V` and the coefficients alone, such that every
`u ∈ H¹(U)` that is a weak solution of `L u = f` in `U` for `f ∈ H^m(U)` has weak derivatives up
to order `m + 2` in `L²(V)`, which is `u ∈ H^{m+2}(V)`, with

`‖u‖_{H^{m+2}(V)} ≤ C (‖f‖_{H^m(U)} + ‖u‖_{L²(U)})`.

Since every `V ⊂⊂ U` is covered, this is also `u ∈ H^{m+2}_loc(U)`. `f ∈ H^m(U)` is `f ∈ L²(U)`
with a family `Hf` of weak derivatives up to order `m` in `L²(U)`, and both norms are
`iteratedNorm`. The weak formulation is tested against `C_c^∞(U)`. The boundedness of `U` and
  symmetry of `a^{ij}` assumed by Evans are unnecessary here. -/
theorem higher_interior_regularity_evans {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (m : ℕ)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ (m + 1 : ℕ) (fun x => a x i j) U)
    (hb : ∀ i, ContDiffOn ℝ (m + 1 : ℕ) (fun x => b x i) U)
    (hc : ContDiffOn ℝ (m + 1 : ℕ) c U) {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ᵐ x ∂(volume.restrict U), ∀ ξ : Fin d → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    {V : Set (EuclideanSpace ℝ (Fin d))} (hVo : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f u : EuclideanSpace ℝ (Fin d) → ℝ)
      (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
      (hf : MemLp f 2 (volume.restrict U)) (hu : MemLp u 2 (volume.restrict U)),
      (∀ i, MemLp (G i) 2 (volume.restrict U)) →
      ∀ Hf : HasIteratedWeakDerivOn U m (hf.toLp f), HasWeakGradOn U u G →
      LocalWeakSol U a b c f u G →
      ∃ H : HasIteratedWeakDerivOn V (m + 2)
          ((hu.mono_measure (Measure.restrict_mono (subset_closure.trans hVU) le_rfl)).toLp u),
        iteratedNorm H ≤ C * (iteratedNorm Hf + ‖hu.toLp u‖) := by
  have hVU' : V ⊆ U := subset_closure.trans hVU
  cases d with
  | zero =>
    refine ⟨Real.sqrt (listCount 0 (m + 2)), Real.sqrt_nonneg _,
      fun f u G hf hu _ Hf _ _ => ⟨HasIteratedWeakDerivOn.ofFinZero (m + 2) _, ?_⟩⟩
    have hB : IteratedL2Bound (HasIteratedWeakDerivOn.ofFinZero (m + 2)
        ((hu.mono_measure (Measure.restrict_mono hVU' le_rfl)).toLp u)) ‖hu.toLp u‖ :=
      fun _ _ => norm_toLp_le_of_subset hVU' hu
        (hu.mono_measure (Measure.restrict_mono hVU' le_rfl))
    refine (iteratedNorm_le hB).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    linarith [iteratedNorm_nonneg Hf]
  | succ n =>
    let P : CkOpOn (n + 1) U (m + 1) :=
      { a := a, lam := θ, lam_pos := hθ, contDiffOn := ha, elliptic := hell, b := b, c := c
        b_contDiffOn := hb, c_contDiffOn := hc }
    obtain ⟨Op, W, hWo, hKW, hWU, ⟨hCk⟩, ⟨hbc⟩, ha', hb', hc'⟩ :=
      exists_localOp_Ck P hU hVc hVU
    obtain ⟨C, hC0, hCf⟩ := exists_family_of_localWeakSol hU hWo hWU hVc hKW hVo.measurableSet
      subset_closure Op (higher_interior_regularity_W12 Op hWo.measurableSet hWo
        (hCk.toIsC1Coeff (by omega)) m hCk.toIsWkInftyCoeff (hbc.mono (Nat.le_succ m)))
      ha' hb' hc'
    refine ⟨Real.sqrt (listCount (n + 1) (m + 2)) * C, mul_nonneg (Real.sqrt_nonneg _) hC0,
      fun f u G hf hu hG Hf hgrad hsol => ?_⟩
    obtain ⟨H, hH⟩ := hCf f u G hf hu hG Hf (iteratedNorm Hf) (iteratedL2Bound_iteratedNorm Hf)
      hgrad hsol
    exact ⟨H, (iteratedNorm_le hH).trans (le_of_eq (by ring))⟩

end EllipticPdes.Regularity
