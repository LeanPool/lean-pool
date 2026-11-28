/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.PiecewisePoly
public import LeanPool.FunctionSpaces.Domains.Interval.SplineJackson

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Tensor splines on the cube

The spline quasi-interpolant `Q_k g = ∑_n λ_n(g) N_r(2^k x - n)` of
`FunctionSpaces.Domains.Interval.QuasiInterp` is a finite-rank kernel operator (`Cube.qiKernel`,
`Cube.qiKernel_apply`): its coefficients `λ_n` are combinations of the coefficients of the local
projection on one interval (`Interval.qiCoeff_eq_sum`), so `λ_n(g) = ∫_0^1 g κ_n` with a bounded
kernel `κ_n`, and its functions are the B-splines `N_r(2^k x - n)` on `[0, 1)`. It is bounded on
`L_p[0, 1]` uniformly in `k` (`Cube.exists_eLpNorm_qiKernel_apply_le`).

A function on the cube `Q = [0, 1]^d` is a **spline of order `r` and level `k` in each variable**
(`Cube.IsCubeSpline`) if it is bounded and measurable and every slice in every coordinate is a
dyadic spline of order `r` and level `k` on `[0, 1]`. These functions form subspaces of `L_p(Q)`
increasing in `k` (`Cube.cubeSplineSpace`) and the scheme `Cube.cubeSplineScheme`; at level `0`
they contain the polynomials of degree `< r` in each variable (`Cube.IsCubePP.isCubeSpline_zero`).
The **tensor quasi-interpolant** `Q_k^{(0)} ⋯ Q_k^{(d-1)} g` (`Cube.cubeQI`) has the form of `Q_k`
in every coordinate, so its slices are combinations of B-splines (`Cube.isCubeSpline_cubeQI`).

Since `Q_k` reproduces the splines (`Interval.ppFun_qiPieces_ppFun`), in particular its own
B-splines (`Cube.qiKernel_reproduces`), the splines on the cube are the **tensor products** of the
splines in one variable: the combinations of products `∏_i u_i(x_i)` of dyadic splines `u_i` on
`[0, 1]` (`Cube.isCubeSpline_iff_mem_span_prod_ppFun`), or of products of B-splines
(`Cube.isCubeSpline_iff_mem_span`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Cube

open Interval

/-! ### The quasi-interpolant as a kernel operator -/

/-- The interval `J(n) = I_{k, max(n, 0)}` of a coefficient `λ_n`, `-r < n < 2^k`, lies in
`[0, 1)`. -/
theorem toNat_lt_of_mem_qiIdx {r k : ℕ} {n : ℤ} (hn : n ∈ qiIdx r (2 ^ k)) : n.toNat < 2 ^ k := by
  rw [qiIdx, Finset.mem_Ioo] at hn
  have h2 : 0 < 2 ^ k := Nat.two_pow_pos k
  generalize 2 ^ k = N at hn h2 ⊢
  omega

/-- The **quasi-interpolant of level `k` as a kernel operator**, indexed by the B-splines
`-r < n < 2^k`: the kernel `κ_n = ∑_i β_{n,i} κ_{J(n),i}` combines the kernels of the local
projection on `J(n)` (`Cube.ppKernel`), and `φ_n` is the B-spline `N_r(2^k x - n)` on `[0, 1)`. -/
noncomputable def qiKernel {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : KernelOp (qiIdx r (2 ^ k)) where
  kernel n s := ∑ i : Fin r, bsplineCoef hr (qiBasisPoly r k (n : ℤ).toNat i) n *
    (ppKernel r k).kernel (⟨(n : ℤ).toNat, toNat_lt_of_mem_qiIdx n.2⟩, i) s
  rangeFn n := ppFun k (bsplinePieces r k n)
  bddMeas_kernel _ := bddMeas_sum _ fun _ _ => ((ppKernel r k).bddMeas_kernel _).const_mul _
  bddMeas_rangeFn _ := bddMeas_ppFun k _

/-- The coefficients of the kernel operator are the quasi-interpolant coefficients, for `g`
integrable on `[0, 1]`. -/
theorem qiKernel_coef {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Icc (0 : ℝ) 1)) (n : qiIdx r (2 ^ k)) :
    (qiKernel hr k).coef g n = qiCoeff hr k g n := by
  calc (qiKernel hr k).coef g n
      = ∫ s in Icc (0 : ℝ) 1, ∑ i : Fin r, bsplineCoef hr (qiBasisPoly r k (n : ℤ).toNat i) n *
          (g s * (ppKernel r k).kernel (⟨(n : ℤ).toNat, toNat_lt_of_mem_qiIdx n.2⟩, i) s) := by
        rw [KernelOp.coef]
        congr 1
        funext s
        simp only [qiKernel]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin r, ∫ s in Icc (0 : ℝ) 1, bsplineCoef hr (qiBasisPoly r k (n : ℤ).toNat i) n *
          (g s * (ppKernel r k).kernel (⟨(n : ℤ).toNat, toNat_lt_of_mem_qiIdx n.2⟩, i) s) :=
        integral_finsetSum _ fun i _ =>
          ((ppKernel r k).integrableOn_mul_kernel hg _).const_mul _
    _ = ∑ i : Fin r, bsplineCoef hr (qiBasisPoly r k (n : ℤ).toNat i) n *
          locCoeff r k g (n : ℤ).toNat i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, ← KernelOp.coef, ppKernel_coef]
    _ = qiCoeff hr k g n := by
        rw [qiCoeff_eq_sum]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **The kernel operator is the quasi-interpolant**: `(qiKernel hr k).apply g = Q_k g` for `g`
integrable on `[0, 1]`. -/
theorem qiKernel_apply {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {g : ℝ → ℂ}
    (hg : IntegrableOn g (Icc (0 : ℝ) 1)) :
    (qiKernel hr k).apply g = ppFun k (qiPieces hr k (2 ^ k) g) := by
  funext t
  rw [KernelOp.apply, qiPieces, ppFun_sum, Finset.sum_apply,
    ← Finset.sum_coe_sort (qiIdx r (2 ^ k))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [qiKernel_coef hr k hg n, ppFun_const_mul]
  rfl

/-- **The quasi-interpolant is bounded on `L_p[0, 1]`** as a kernel operator, uniformly in the
level: there is `C < ∞` with `‖Q_k u‖_{L_p[0,1]} ≤ C ‖u‖_{L_p[0,1]}` for all `k` and all
measurable `u`. -/
theorem exists_eLpNorm_qiKernel_apply_le {r : ℕ} (hr : 1 ≤ r) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (k : ℕ) (u : ℝ → ℂ), Measurable u →
      eLpNorm ((qiKernel hr k).apply u) p unitVol ≤ C * eLpNorm u p unitVol := by
  obtain ⟨C, hC, hCb⟩ := exists_eLpNorm_qi_le (p := p) hr hp
  refine ⟨C + 1, ENNReal.add_ne_top.2 ⟨hC, ENNReal.one_ne_top⟩, fun k u hu => ?_⟩
  rcases eq_or_ne (eLpNorm u p unitVol) ∞ with hinf | hfin
  · rw [hinf, ENNReal.mul_top (ne_of_gt (lt_of_lt_of_le zero_lt_one le_add_self))]
    exact le_top
  · have hmem : MemLp u p unitVol := lt_top_iff_ne_top.2 hfin
    have hint : IntegrableOn u (Icc (0 : ℝ) 1) := (hmem.integrable Fact.out : Integrable u unitVol)
    rw [qiKernel_apply hr k hint]
    exact (hCb k hu fun m hm => hint.mono_set
      ((dyadicIco_subset hm).trans Ico_subset_Icc_self)).trans (mul_le_mul' le_self_add le_rfl)

/-! ### Splines on the cube -/

variable {d : ℕ}

/-- A function on the cube is a **spline of order `r` and level `k` in each variable**: bounded
and measurable, and every slice in every coordinate is a dyadic spline of order `r` and level `k`
on `[0, 1]`. -/
def IsCubeSpline (r k : ℕ) (g : (Fin d → ℝ) → ℂ) : Prop :=
  BddMeas g ∧ ∀ (i : Fin d) (x : Fin d → ℝ), ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧
    SplineJoins r k Q ∧ slice g x i = ppFun k Q

/-- Splines of level `k` are splines of level `k + 1`. -/
theorem IsCubeSpline.succ {r k : ℕ} {g : (Fin d → ℝ) → ℂ} (h : IsCubeSpline r k g) :
    IsCubeSpline r (k + 1) g :=
  ⟨h.1, fun i x => by
    obtain ⟨Q, hQ, hJ, hs⟩ := h.2 i x
    exact ⟨fun m => Q (m / 2), fun m => hQ _, hJ.refine, hs.trans (ppFun_refine_eq k Q).symm⟩⟩

/-- Sums of splines on the cube. -/
theorem IsCubeSpline.add {r k : ℕ} {f g : (Fin d → ℝ) → ℂ} (hf : IsCubeSpline r k f)
    (hg : IsCubeSpline r k g) : IsCubeSpline r k (f + g) :=
  ⟨hf.1.add hg.1, fun i x => by
    obtain ⟨Q, hQ, hJ, hs⟩ := hf.2 i x
    obtain ⟨Q', hQ', hJ', hs'⟩ := hg.2 i x
    refine ⟨Q + Q', fun n => Submodule.add_mem _ (hQ n) (hQ' n), hJ.add hJ', ?_⟩
    rw [ppFun_add, ← hs, ← hs']
    rfl⟩

/-- Constant multiples of splines on the cube. -/
theorem IsCubeSpline.const_mul {r k : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : IsCubeSpline r k g)
    (a : ℂ) : IsCubeSpline r k (fun x => a * g x) :=
  ⟨hg.1.const_mul a, fun i x => by
    obtain ⟨Q, hQ, hJ, hs⟩ := hg.2 i x
    refine ⟨fun n => C a * Q n, fun n => by
      change C a * Q n ∈ degreeLT ℂ r
      rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (hQ n), hJ.const_mul a, ?_⟩
    rw [ppFun_const_mul, ← hs]
    rfl⟩

/-- The zero function is a spline on the cube. -/
theorem isCubeSpline_zero (r k : ℕ) : IsCubeSpline (d := d) r k 0 :=
  ⟨bddMeas_zero, fun _ _ => ⟨0, fun _ => Submodule.zero_mem _, splineJoins_zero r k, by
    rw [ppFun_zero]; rfl⟩⟩

/-- **At level `0` the piecewise polynomials are splines**: there are no interior knots. -/
theorem IsCubePP.isCubeSpline_zero {r : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : IsCubePP r 0 g) :
    IsCubeSpline r 0 g :=
  ⟨hg.1, fun i x => by
    obtain ⟨Q, hQ, hs⟩ := hg.exists_slice_eq_ppFun i x
    exact ⟨Q, hQ, fun n hn hn1 => absurd hn1 (by rw [pow_zero]; omega), hs⟩⟩

/-- The **tensor quasi-interpolant**: the quasi-interpolant `Q_k` applied in all coordinates,
`Q_k^{(0)} ∘ ⋯ ∘ Q_k^{(d-1)}`. -/
noncomputable def cubeQI {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : (Fin d → ℝ) → ℂ) :
    (Fin d → ℝ) → ℂ :=
  (qiKernel hr k).foldSlicewise (List.finRange d) g

/-- **The forms of the quasi-interpolant are splines on the cube**: a bounded measurable function
with the form of `Q_k` in every coordinate has slices that are combinations of B-splines. -/
theorem isCubeSpline_of_isForm {r : ℕ} (hr : 1 ≤ r) {k : ℕ} {g : (Fin d → ℝ) → ℂ}
    (hg : BddMeas g) (hform : ∀ i, (qiKernel hr k).IsForm i g) : IsCubeSpline r k g := by
  refine ⟨hg, fun i x => ?_⟩
  obtain ⟨a, ha⟩ := (hform i).slice_eq _ x
  refine ⟨∑ n : qiIdx r (2 ^ k), fun m => C (a n) * bsplinePieces r k n m, fun m => ?_, ?_, ?_⟩
  · rw [Finset.sum_apply]
    exact Submodule.sum_mem _ fun n _ => by
      rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (bsplinePieces_mem hr k n m)
  · exact SplineJoins.sum _ fun n _ => (splineJoins_bsplinePieces hr k n).const_mul (a n)
  · rw [ha, ppFun_sum]
    funext t
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ppFun_const_mul]
    rfl

/-- **The tensor quasi-interpolant is a spline on the cube**: it has the form of `Q_k` in every
coordinate, so its slices are combinations of B-splines. -/
theorem isCubeSpline_cubeQI {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {g : (Fin d → ℝ) → ℂ}
    (hg : BddMeas g) : IsCubeSpline r k (cubeQI hr k g) :=
  isCubeSpline_of_isForm hr ((qiKernel hr k).bddMeas_foldSlicewise _ hg)
    fun i => (qiKernel hr k).isForm_foldSlicewise _ hg (List.mem_finRange i)

/-! ### Tensor products -/

/-- The quasi-interpolant reproduces its B-splines `N_r(2^k x - n)`. -/
theorem qiKernel_reproduces {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : (qiKernel hr k).Reproduces :=
  fun n => by
    change (qiKernel hr k).apply (ppFun k (bsplinePieces r k n)) = ppFun k (bsplinePieces r k n)
    rw [qiKernel_apply hr k (bddMeas_ppFun k _).integrableOn_Icc,
      ppFun_qiPieces_ppFun hr (bsplinePieces_mem hr k n) (splineJoins_bsplinePieces hr k n)]

/-- **The quasi-interpolant reproduces splines on the cube**: `Q_k^{(i)} g = g` in every
coordinate `i`, since it reproduces the slices. -/
theorem IsCubeSpline.slicewise_qiKernel {r k : ℕ} (hr : 1 ≤ r) {g : (Fin d → ℝ) → ℂ}
    (hg : IsCubeSpline r k g) (i : Fin d) : (qiKernel hr k).slicewise i g = g := by
  funext x
  obtain ⟨Q, hQ, hJ, hs⟩ := hg.2 i x
  rw [KernelOp.slicewise, hs, qiKernel_apply hr k (bddMeas_ppFun k Q).integrableOn_Icc,
    ppFun_qiPieces_ppFun hr hQ hJ, ← hs]
  simp only [slice, Function.update_eq_self]

/-- Splines on the cube have the form of `Q_k` in every coordinate. -/
theorem IsCubeSpline.isForm {r k : ℕ} (hr : 1 ≤ r) {g : (Fin d → ℝ) → ℂ}
    (hg : IsCubeSpline r k g) (i : Fin d) : (qiKernel hr k).IsForm i g :=
  KernelOp.IsForm.congr (qiKernel hr k) ((qiKernel hr k).isForm_slicewise hg.1 i)
    (hg.slicewise_qiKernel hr i)

/-- **Splines on the cube are tensor products of B-splines**: `g` is a spline of order `r` and
level `k` in each variable iff it is a combination of the products `∏_i N_r(2^k x_i - n_i)` of the
B-splines that meet `[0, 1)`. -/
theorem isCubeSpline_iff_mem_span {r k : ℕ} (hr : 1 ≤ r) {g : (Fin d → ℝ) → ℂ} :
    IsCubeSpline r k g ↔ g ∈ Submodule.span ℂ (Set.range fun j : Fin d → qiIdx r (2 ^ k) =>
      fun x => ∏ i, (qiKernel hr k).rangeFn (j i) (x i)) := by
  have : Nonempty (qiIdx r (2 ^ k)) := ⟨⟨0, by
    rw [qiIdx, Finset.mem_Ioo]
    exact ⟨by omega, by exact_mod_cast Nat.two_pow_pos k⟩⟩⟩
  exact ⟨fun h => (qiKernel hr k).mem_span_prod_of_isForm (qiKernel_reproduces hr k) h.1
      (h.isForm hr),
    fun h => isCubeSpline_of_isForm hr ((qiKernel hr k).isForm_of_mem_span_prod h).1
      ((qiKernel hr k).isForm_of_mem_span_prod h).2⟩

/-- **Splines on the cube are the tensor products of splines in one variable**: the splines of
order `r` and level `k` in each variable are the combinations of products `∏_i u_i(x_i)` of dyadic
splines `u_i` of order `r` and level `k` on `[0, 1]`. -/
theorem isCubeSpline_iff_mem_span_prod_ppFun {r k : ℕ} (hr : 1 ≤ r) {g : (Fin d → ℝ) → ℂ} :
    IsCubeSpline r k g ↔ g ∈ Submodule.span ℂ {G | ∃ Q : Fin d → ℕ → ℂ[X],
      (∀ i n, Q i n ∈ degreeLT ℂ r) ∧ (∀ i, SplineJoins r k (Q i)) ∧
        G = fun x => ∏ i, ppFun k (Q i) (x i)} := by
  rw [isCubeSpline_iff_mem_span hr]
  constructor
  · refine fun h => Submodule.span_mono ?_ h
    rintro _ ⟨j, rfl⟩
    exact ⟨fun i => bsplinePieces r k (j i), fun i n => bsplinePieces_mem hr k _ n,
      fun i => splineJoins_bsplinePieces hr k _, rfl⟩
  · refine fun h => (Submodule.span_le.2 ?_) h
    rintro _ ⟨Q, hQ, hJ, rfl⟩
    have hexp : ∀ i (t : ℝ), ppFun k (Q i) t =
        ∑ m, (qiKernel hr k).coef (ppFun k (Q i)) m * (qiKernel hr k).rangeFn m t := fun i t => by
      have h := congrFun (qiKernel_apply hr k (bddMeas_ppFun k (Q i)).integrableOn_Icc) t
      rw [ppFun_qiPieces_ppFun hr (hQ i) (hJ i)] at h
      rw [← h]
      rfl
    have hG : (fun x : Fin d → ℝ => ∏ i, ppFun k (Q i) (x i)) =
        ∑ j : Fin d → qiIdx r (2 ^ k), (∏ i, (qiKernel hr k).coef (ppFun k (Q i)) (j i)) •
          fun x : Fin d → ℝ => ∏ i, (qiKernel hr k).rangeFn (j i) (x i) := by
      funext x
      simp only [hexp, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    rw [hG]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The space of **splines of order `r` and level `k` in each variable** in `L_p(Q)`. -/
noncomputable def cubeSplineSpace (r k : ℕ) : Submodule ℝ (Lp ℂ p (cubeVol d)) where
  carrier := {f | ∃ g, IsCubeSpline r k g ∧ (f : (Fin d → ℝ) → ℂ) =ᵐ[cubeVol d] g}
  add_mem' := by
    rintro f f' ⟨g, hg, hfg⟩ ⟨g', hg', hfg'⟩
    exact ⟨g + g', hg.add hg', (Lp.coeFn_add f f').trans (hfg.add hfg')⟩
  zero_mem' := ⟨0, isCubeSpline_zero r k, Lp.coeFn_zero ℂ p (cubeVol d)⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hfg⟩
    refine ⟨fun x => (c : ℂ) * g x, hg.const_mul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hfg] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Complex.real_smul]

omit [Fact (1 ≤ p)] in
/-- The spline spaces on the cube increase with the level. -/
theorem cubeSplineSpace_mono (r : ℕ) : Monotone (cubeSplineSpace (d := d) p r) :=
  monotone_nat_of_le_succ fun _ _ ⟨g, hg, hfg⟩ => ⟨g, hg.succ, hfg⟩

variable (p) in
/-- The **scheme of tensor splines on the cube**: `{0}` at complexity `0` and the splines of
level `⌊log₂ n⌋` in each variable at complexity `n ≥ 1`. -/
noncomputable def cubeSplineScheme (d r : ℕ) : ApproximationScheme (Lp ℂ p (cubeVol d)) :=
  ApproximationScheme.ofMonotoneSubmodules (cubeSplineSpace p r) (cubeSplineSpace_mono r)

/-- The approximants of complexity `2^k` are the splines of level `k`. -/
theorem mem_cubeSplineScheme_two_pow {r k : ℕ} {g : Lp ℂ p (cubeVol d)} :
    g ∈ cubeSplineScheme p d r (2 ^ k) ↔ g ∈ cubeSplineSpace p r k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

/-- The scheme of tensor splines is linear. -/
theorem cubeSplineScheme_isLinear (r : ℕ) : (cubeSplineScheme p d r).IsLinear :=
  ApproximationScheme.isLinear_ofMonotoneSubmodules _ _

/-- At complexity `1` the tensor splines contain the polynomials of degree `< r` in each
variable, so their error is at most that of the piecewise polynomials. -/
theorem approxError_cubeSplineScheme_one_le (r : ℕ) (f : Lp ℂ p (cubeVol d)) :
    (cubeSplineScheme p d r).approxError f 1 ≤ (cubePPScheme p d r).approxError f 1 := by
  have hsub : (cubePPScheme p d r 1 : Set (Lp ℂ p (cubeVol d))) ⊆ cubeSplineScheme p d r 1 := by
    intro g hg
    obtain ⟨g', hg', hgg'⟩ := (mem_cubePPScheme_two_pow (k := 0)).1 hg
    exact (mem_cubeSplineScheme_two_pow (k := 0)).2 ⟨g', hg'.isCubeSpline_zero, hgg'⟩
  rw [ApproximationScheme.approxError, ApproximationScheme.approxError]
  exact Metric.infEDist_anti hsub

end Cube
