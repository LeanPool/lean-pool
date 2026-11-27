/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.SlicewiseOperators
public import LeanPool.FunctionSpaces.Domains.Interval.LocalProjection

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Dyadic piecewise polynomials on the cube

The local projection onto the piecewise polynomials of level `k` and degree `< r` on `[0, 1]` is a
finite-rank kernel operator (`Cube.ppKernel`, `Cube.ppKernel_apply`): with the monomials `b_l` and
their dual basis `d_l`,
`P_k g(t) = ∑_{n < 2^k} ∑_{l < r} (2^k ∫_{I_{k,n}} g b_l(2^k s - n) ds) 1_{I_{k,n}}(t) d_l(2^k t
- n)`.
The functions of level `k` are combinations of those of level `k + 1`, since `P_{k+1}` reproduces
the piecewise polynomials of level `k` (`Cube.ppKernel_rangeFn_eq_sum`).

A function on the cube `Q = [0, 1]^d` is a **piecewise polynomial of level `k` and degree `< r`
in each variable** (`Cube.IsCubePP`) if it is bounded and measurable and has, in every coordinate
`i`, the form `∑_j c_j(x) φ_j(x_i)` of `P_k` with coefficients independent of `x_i`: on every
dyadic cube of level `k` it is a polynomial of degree `< r` in each variable separately. These
functions form subspaces `V_k^d` of `L_p(Q)` increasing in `k` (`Cube.cubePPSpace`) and the scheme
`Cube.cubePPScheme`. Applying `P_k` in all coordinates (`Cube.cubeProj`) maps bounded measurable
functions into `V_k^d` (`Cube.isCubePP_cubeProj`), and the slices of a function in `V_k^d` are
piecewise polynomials of level `k` on `[0, 1]` (`Cube.IsCubePP.exists_slice_eq_ppFun`).

Since `P_k` reproduces the piecewise polynomials (`Cube.ppKernel_reproduces`), `V_k^d` is the
**tensor product** of the one-dimensional spaces: its functions are the combinations of products
`∏_i u_i(x_i)` of piecewise polynomials `u_i` of level `k` and degree `< r` on `[0, 1]`
(`Cube.isCubePP_iff_mem_span_prod_ppFun`, `Cube.isCubePP_iff_mem_span`). The definition through
slices is the one used in the proofs: it describes `V_k^d` without choosing a basis.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Cube

open Interval

/-! ### The local projection as a kernel operator -/

/-- The polynomials `b_l(2^k s - n)` and `d_l(2^k t - n)` on `I_{k,n}` are bounded by the bound
of the
bases on `[0, 1]`. -/
theorem norm_indicator_polyFun_le (k : ℕ) (n : ℕ) (P : ℂ[X]) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hPB : ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun P t‖ₑ ≤ B) (c : ℂ) (s : ℝ) :
    ‖(dyadicIco k n).indicator (fun s => c * polyFun P (-(n : ℝ) + 2 ^ k * s)) s‖ ≤
      ‖c‖ * B.toReal := by
  by_cases hs : s ∈ dyadicIco k n
  · rw [indicator_of_mem hs, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
    have ht : -(n : ℝ) + 2 ^ k * s ∈ Icc (0 : ℝ) 1 := by
      rw [mem_dyadicIco] at hs
      constructor <;> linarith [hs.1, hs.2]
    have h := hPB _ ht
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 h
  · rw [indicator_of_notMem hs, norm_zero]
    positivity

/-- The **local projection onto piecewise polynomials of level `k`** as a kernel operator, indexed
by `(n, l)`: `κ_{n,l}(s) = 1_{I_{k,n}}(s) 2^k b_l(2^k s - n)`, `φ_{n,l}(t) = 1_{I_{k,n}}(t)
d_l(2^k t - n)`. -/
noncomputable def ppKernel (r k : ℕ) : KernelOp (Fin (2 ^ k) × Fin r) where
  kernel j := (dyadicIco k j.1).indicator fun s =>
    (((2 : ℝ) ^ k : ℝ) : ℂ) * polyFun (monoBasis r j.2) (-(j.1 : ℝ) + 2 ^ k * s)
  rangeFn j := (dyadicIco k j.1).indicator fun t =>
    (1 : ℂ) * polyFun (dualPoly r j.2) (-(j.1 : ℝ) + 2 ^ k * t)
  bddMeas_kernel j := ⟨(measurable_const.mul ((measurable_polyFun _).comp
    (by fun_prop))).indicator (measurableSet_dyadicIco _ _), _,
    norm_indicator_polyFun_le k j.1 _ (basisBound_ne_top r) (fun t ht => enorm_monoBasis_le r
      j.2 ht)
      _⟩
  bddMeas_rangeFn j := ⟨(measurable_const.mul ((measurable_polyFun _).comp
    (by fun_prop))).indicator (measurableSet_dyadicIco _ _), _,
    norm_indicator_polyFun_le k j.1 _ (basisBound_ne_top r) (fun t ht => enorm_dualPoly_le r j.2 ht)
      _⟩

/-- The coefficients of the kernel operator are the local coefficients. -/
theorem ppKernel_coef (r k : ℕ) (g : ℝ → ℂ) (j : Fin (2 ^ k) × Fin r) :
    (ppKernel r k).coef g j = locCoeff r k g j.1 j.2 := by
  have hsub : dyadicIco k j.1 ⊆ Icc (0 : ℝ) 1 :=
    (dyadicIco_subset j.1.isLt).trans Ico_subset_Icc_self
  have hfun : (fun s => g s * (ppKernel r k).kernel j s) = (dyadicIco k j.1).indicator
      (fun s => (((2 : ℝ) ^ k : ℝ) : ℂ) *
        (g s * polyFun (monoBasis r j.2) (-(j.1 : ℝ) + 2 ^ k * s))) := by
    funext s
    simp only [ppKernel]
    by_cases hs : s ∈ dyadicIco k j.1
    · rw [indicator_of_mem hs, indicator_of_mem hs]; ring
    · rw [indicator_of_notMem hs, indicator_of_notMem hs, mul_zero]
  rw [KernelOp.coef, hfun, setIntegral_indicator (measurableSet_dyadicIco _ _),
    Set.inter_eq_right.2 hsub, integral_const_mul, locCoeff]

/-- **The kernel operator is the local projection**: `(ppKernel r k).apply g = P_k g`. -/
theorem ppKernel_apply (r k : ℕ) (g : ℝ → ℂ) :
    (ppKernel r k).apply g = ppFun k (locProj r k g) := by
  funext t
  simp only [KernelOp.apply, ppKernel_coef, Fintype.sum_prod_type, ppFun]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases ht : t ∈ dyadicIco k n
  · simp only [ppKernel, indicator_of_mem ht, one_mul]
    rw [polyFun_locProj]
  · simp only [ppKernel, indicator_of_notMem ht, mul_zero, Finset.sum_const_zero]

/-- The kernel operator is bounded on `L_p[0, 1]` by the bound of the local projections. -/
theorem eLpNorm_ppKernel_apply_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (r k : ℕ) {u : ℝ → ℂ}
    (hu : Measurable u) :
    eLpNorm ((ppKernel r k).apply u) p unitVol ≤ ppProjConst r * eLpNorm u p unitVol := by
  rw [ppKernel_apply]
  exact eLpNorm_ppFun_locProj_le hp hp' r k hu.aestronglyMeasurable

/-- The local projection reproduces the piecewise polynomials of its level. -/
theorem ppKernel_apply_ppFun {r k : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r) :
    (ppKernel r k).apply (ppFun k Q) = ppFun k Q := by
  rw [ppKernel_apply, ppFun_locProj_ppFun hQ]

/-- Piecewise polynomials are bounded and measurable (`Interval.measurable_ppFun`,
`Interval.exists_norm_ppFun_le`). -/
theorem bddMeas_ppFun (k : ℕ) (Q : ℕ → ℂ[X]) : BddMeas (ppFun k Q) :=
  ⟨measurable_ppFun k Q, exists_norm_ppFun_le k Q⟩

/-- **Lebesgue's inequality for the local projection**: for `u` integrable on `[0, 1]` and every
piecewise polynomial `S` of level `k` and degree `< r`,
`‖u - P_k u‖_{L_p[0,1]} ≤ (1 + C_r) ‖u - S‖_{L_p[0,1]}`. Since `P_k S = S`, the error is
`u - P_k u = (u - S) - P_k (u - S)`. -/
theorem eLpNorm_sub_ppKernel_apply_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {r k : ℕ}
    {u : ℝ → ℂ} (hu : Measurable u) (hui : IntegrableOn u (Icc (0 : ℝ) 1)) {Q : ℕ → ℂ[X]}
    (hQ : ∀ n, Q n ∈ degreeLT ℂ r) :
    eLpNorm (fun t => u t - (ppKernel r k).apply u t) p unitVol ≤
      (1 + ppProjConst r) * eLpNorm (fun t => u t - ppFun k Q t) p unitVol := by
  have heq : (fun t => u t - (ppKernel r k).apply u t) =
      (fun t => u t - ppFun k Q t) - (ppKernel r k).apply (fun s => u s - ppFun k Q s) := by
    funext t
    rw [Pi.sub_apply, KernelOp.apply_sub _ hui (integrableOn_ppFun k Q), ppKernel_apply_ppFun hQ]
    ring
  rw [heq, add_mul, one_mul]
  exact (eLpNorm_sub_le hp).trans (add_le_add le_rfl
    (eLpNorm_ppKernel_apply_le hp hp' r k (hu.sub (measurable_ppFun k Q))))

/-- The function `φ_{n,l}` of level `k` is the piecewise polynomial with the single piece
`d_l(2^k t - n)` on `I_{k,n}`. -/
theorem ppKernel_rangeFn_eq_ppFun (r k : ℕ) (j : Fin (2 ^ k) × Fin r) :
    (ppKernel r k).rangeFn j = ppFun k (fun m => if m = j.1 then
      (dualPoly r j.2 : ℂ[X]).comp (C ((-(j.1 : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X)
      else 0) := by
  funext t
  simp only [ppKernel, ppFun]
  rw [Finset.sum_eq_single (j.1 : ℕ) (fun m _ hm => by simp [hm, polyFun_zero])
    (fun h => absurd (Finset.mem_range.2 j.1.isLt) h)]
  simp only [↓reduceIte, one_mul]
  by_cases ht : t ∈ dyadicIco k j.1
  · rw [indicator_of_mem ht, indicator_of_mem ht, polyFun_comp_affine]
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]

/-- **Refinement**: the functions of level `k` are combinations of those of level `k + 1`,
`φ^{(k)}_j = P_{k+1} φ^{(k)}_j = ∑_{j'} (∫_0^1 φ^{(k)}_j κ^{(k+1)}_{j'}) φ^{(k+1)}_{j'}`. -/
theorem ppKernel_rangeFn_eq_sum (r k : ℕ) (j : Fin (2 ^ k) × Fin r) (t : ℝ) :
    (ppKernel r k).rangeFn j t = ∑ j', (ppKernel r (k + 1)).coef ((ppKernel r k).rangeFn j) j' *
      (ppKernel r (k + 1)).rangeFn j' t := by
  set Q : ℕ → ℂ[X] := fun m => if m = j.1 then
    (dualPoly r j.2 : ℂ[X]).comp (C ((-(j.1 : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X)
    else 0
  have hQ : ∀ m, Q m ∈ degreeLT ℂ r := fun m => by
    simp only [Q]
    split_ifs
    · exact comp_affine_mem_degreeLT (dualPoly r j.2).2 _ _
    · exact Submodule.zero_mem _
  have h := ppKernel_rangeFn_eq_ppFun r k j
  have hrep : (ppKernel r k).rangeFn j = (ppKernel r (k + 1)).apply ((ppKernel r k).rangeFn j) := by
    rw [ppKernel_apply, h, ← ppFun_refine_eq k Q, ppFun_locProj_ppFun fun m => hQ (m / 2)]
  exact congrFun hrep t

/-! ### Piecewise polynomials on the cube -/

variable {d : ℕ}

/-- A function on the cube is a **piecewise polynomial of level `k` and degree `< r` in each
variable**: bounded and measurable with the form of the local projection `P_k` in every
coordinate, so that on every dyadic cube of level `k` it is a polynomial of degree `< r` in each
variable separately. -/
def IsCubePP (r k : ℕ) (g : (Fin d → ℝ) → ℂ) : Prop :=
  BddMeas g ∧ ∀ i, (ppKernel r k).IsForm i g

/-- Piecewise polynomials of level `k` are piecewise polynomials of level `k + 1`. -/
theorem IsCubePP.succ {r k : ℕ} {g : (Fin d → ℝ) → ℂ} (h : IsCubePP r k g) :
    IsCubePP r (k + 1) g :=
  ⟨h.1, fun i => KernelOp.IsForm.refine (ppKernel r k) (h.2 i) _ (ppKernel_rangeFn_eq_sum r k)⟩

/-- Sums of piecewise polynomials. -/
theorem IsCubePP.add {r k : ℕ} {f g : (Fin d → ℝ) → ℂ} (hf : IsCubePP r k f)
    (hg : IsCubePP r k g) : IsCubePP r k (f + g) :=
  ⟨hf.1.add hg.1, fun i => (hf.2 i).add _ (hg.2 i)⟩

/-- Constant multiples of piecewise polynomials. -/
theorem IsCubePP.const_mul {r k : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : IsCubePP r k g) (a : ℂ) :
    IsCubePP r k (fun x => a * g x) :=
  ⟨hg.1.const_mul a, fun i => (hg.2 i).const_mul _ a⟩

/-- The zero function is a piecewise polynomial. -/
theorem isCubePP_zero (r k : ℕ) : IsCubePP (d := d) r k 0 :=
  ⟨bddMeas_zero, fun i => (ppKernel r k).isForm_zero i⟩

/-- **The slices of a piecewise polynomial on the cube** are piecewise polynomials of the same
level and degree on `[0, 1]`. -/
theorem IsCubePP.exists_slice_eq_ppFun {r k : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : IsCubePP r k g)
    (i : Fin d) (x : Fin d → ℝ) :
    ∃ Q : ℕ → ℂ[X], (∀ n, Q n ∈ degreeLT ℂ r) ∧ slice g x i = ppFun k Q := by
  obtain ⟨a, ha⟩ := (hg.2 i).slice_eq _ x
  refine ⟨fun m => ∑ l : Fin r, if h : m < 2 ^ k then a (⟨m, h⟩, l) •
      (dualPoly r l : ℂ[X]).comp (C ((-(m : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X)
      else 0, fun m => Submodule.sum_mem _ fun l _ => ?_, ?_⟩
  · split_ifs
    · exact Submodule.smul_mem _ _ (comp_affine_mem_degreeLT (dualPoly r l).2 _ _)
    · exact Submodule.zero_mem _
  · rw [ha]
    funext t
    simp only [ppFun, Fintype.sum_prod_type]
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases ht : t ∈ dyadicIco k n
    · rw [indicator_of_mem ht]
      conv_rhs => rw [polyFun, eval_finsetSum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dite_eq_left n.isLt, eval_smul, smul_eq_mul, ← polyFun, polyFun_comp_affine, Fin.eta]
      simp only [ppKernel, indicator_of_mem ht, one_mul]
    · simp only [ppKernel, indicator_of_notMem ht, mul_zero, Finset.sum_const_zero]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The space `V_k^d` of **piecewise polynomials of level `k` and degree `< r` in each variable**
in `L_p(Q)`. -/
noncomputable def cubePPSpace (r k : ℕ) : Submodule ℝ (Lp ℂ p (cubeVol d)) where
  carrier := {f | ∃ g, IsCubePP r k g ∧ (f : (Fin d → ℝ) → ℂ) =ᵐ[cubeVol d] g}
  add_mem' := by
    rintro f f' ⟨g, hg, hfg⟩ ⟨g', hg', hfg'⟩
    exact ⟨g + g', hg.add hg', (Lp.coeFn_add f f').trans (hfg.add hfg')⟩
  zero_mem' := ⟨0, isCubePP_zero r k, Lp.coeFn_zero ℂ p (cubeVol d)⟩
  smul_mem' := by
    rintro c f ⟨g, hg, hfg⟩
    refine ⟨fun x => (c : ℂ) * g x, hg.const_mul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hfg] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Complex.real_smul]

omit [Fact (1 ≤ p)] in
/-- The spaces `V_k^d` increase with the level. -/
theorem cubePPSpace_mono (r : ℕ) : Monotone (cubePPSpace (d := d) p r) :=
  monotone_nat_of_le_succ fun _ _ ⟨g, hg, hfg⟩ => ⟨g, hg.succ, hfg⟩

variable (p) in
/-- The **scheme of dyadic piecewise polynomials on the cube**: `{0}` at complexity `0` and
`V_{⌊log₂ n⌋}^d` at complexity `n ≥ 1`. -/
noncomputable def cubePPScheme (d r : ℕ) : ApproximationScheme (Lp ℂ p (cubeVol d)) :=
  ApproximationScheme.ofMonotoneSubmodules (cubePPSpace p r) (cubePPSpace_mono r)

/-- The approximants of complexity `2^k` are the piecewise polynomials of level `k`. -/
theorem mem_cubePPScheme_two_pow {r k : ℕ} {g : Lp ℂ p (cubeVol d)} :
    g ∈ cubePPScheme p d r (2 ^ k) ↔ g ∈ cubePPSpace p r k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

/-- The scheme of piecewise polynomials on the cube is linear. -/
theorem cubePPScheme_isLinear (r : ℕ) : (cubePPScheme p d r).IsLinear :=
  ApproximationScheme.isLinear_ofMonotoneSubmodules _ _

/-! ### The tensor projection -/

/-- The **tensor projection**: the local projection `P_k` applied in all coordinates,
`P_k^{(0)} ∘ ⋯ ∘ P_k^{(d-1)}`. -/
noncomputable def cubeProj (r k : ℕ) (g : (Fin d → ℝ) → ℂ) : (Fin d → ℝ) → ℂ :=
  (ppKernel r k).foldSlicewise (List.finRange d) g

/-- The tensor projection of a bounded measurable function is a piecewise polynomial on the
cube. -/
theorem isCubePP_cubeProj (r k : ℕ) {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g) :
    IsCubePP r k (cubeProj r k g) :=
  ⟨(ppKernel r k).bddMeas_foldSlicewise _ hg,
    fun i => (ppKernel r k).isForm_foldSlicewise _ hg (List.mem_finRange i)⟩

/-! ### Tensor products -/

omit [Fact (1 ≤ p)] in
/-- The local projection reproduces its functions `φ_{n,l}`. -/
theorem ppKernel_reproduces (r k : ℕ) : (ppKernel r k).Reproduces := fun j => by
  rw [ppKernel_rangeFn_eq_ppFun, ppKernel_apply_ppFun fun m => ?_]
  split_ifs
  · exact comp_affine_mem_degreeLT (dualPoly r j.2).2 _ _
  · exact Submodule.zero_mem _

omit [Fact (1 ≤ p)] in
/-- **Piecewise polynomials on the cube are tensor products**: `g` is a piecewise polynomial of
level `k` and degree `< r` in each variable iff it is a combination of the products
`∏_i φ_{j_i}(x_i)` of the functions `φ_{n,l}(t) = 1_{I_{k,n}}(t) d_l(2^k t - n)` of the local
projection. -/
theorem isCubePP_iff_mem_span {r k : ℕ} (hr : 1 ≤ r) {g : (Fin d → ℝ) → ℂ} :
    IsCubePP r k g ↔ g ∈ Submodule.span ℂ (Set.range fun j : Fin d → Fin (2 ^ k) × Fin r =>
      fun x => ∏ i, (ppKernel r k).rangeFn (j i) (x i)) := by
  have : Nonempty (Fin (2 ^ k) × Fin r) := ⟨(⟨0, Nat.two_pow_pos k⟩, ⟨0, hr⟩)⟩
  exact ⟨fun h => (ppKernel r k).mem_span_prod_of_isForm (ppKernel_reproduces r k) h.1 h.2,
    fun h => (ppKernel r k).isForm_of_mem_span_prod h⟩

omit [Fact (1 ≤ p)] in
/-- **Piecewise polynomials on the cube are the tensor products of those in one variable**: the
piecewise polynomials of level `k` and degree `< r` in each variable are the combinations of
products `∏_i u_i(x_i)` of piecewise polynomials `u_i` of level `k` and degree `< r` on
`[0, 1]`. -/
theorem isCubePP_iff_mem_span_prod_ppFun {r k : ℕ} (hr : 1 ≤ r) {g : (Fin d → ℝ) → ℂ} :
    IsCubePP r k g ↔ g ∈ Submodule.span ℂ {G | ∃ Q : Fin d → ℕ → ℂ[X],
      (∀ i n, Q i n ∈ degreeLT ℂ r) ∧ G = fun x => ∏ i, ppFun k (Q i) (x i)} := by
  rw [isCubePP_iff_mem_span hr]
  constructor
  · refine fun h => Submodule.span_mono ?_ h
    rintro _ ⟨j, rfl⟩
    refine ⟨fun i m => if m = ((j i).1 : ℕ) then (dualPoly r (j i).2 : ℂ[X]).comp
      (C ((-((j i).1 : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ k : ℝ) : ℂ) * X) else 0,
      fun i n => ?_, ?_⟩
    · dsimp only
      split_ifs
      · exact comp_affine_mem_degreeLT (dualPoly r (j i).2).2 _ _
      · exact Submodule.zero_mem _
    · funext x
      exact Finset.prod_congr rfl fun i _ => congrFun (ppKernel_rangeFn_eq_ppFun r k (j i)) (x i)
  · refine fun h => (Submodule.span_le.2 ?_) h
    rintro _ ⟨Q, hQ, rfl⟩
    have hexp : ∀ i (t : ℝ), ppFun k (Q i) t =
        ∑ m, (ppKernel r k).coef (ppFun k (Q i)) m * (ppKernel r k).rangeFn m t := fun i t =>
      (congrFun (ppKernel_apply_ppFun (r := r) (k := k) (hQ i)) t).symm
    have hG : (fun x : Fin d → ℝ => ∏ i, ppFun k (Q i) (x i)) =
        ∑ j : Fin d → Fin (2 ^ k) × Fin r, (∏ i, (ppKernel r k).coef (ppFun k (Q i)) (j i)) •
          fun x : Fin d → ℝ => ∏ i, (ppKernel r k).rangeFn (j i) (x i) := by
      funext x
      simp only [hexp, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    rw [hG]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end Cube
