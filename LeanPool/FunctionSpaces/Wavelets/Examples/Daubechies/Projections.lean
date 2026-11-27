/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.PolynomialReproduction
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Projection

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The projections of the multiresolution analysis

For a Daubechies mask of order `N ≥ 2` with scaling function `φ` (`Daubechies.scalingFun`) and
the functions `φ_{j,k}(x) = 2^(j/2) φ(2^j x - k)` of level `j ∈ ℕ` and position `k ∈ ℤ`
(`Daubechies.scaled`), the **projection of level `j`** is

`P_j f(x) = ∑_{k ∈ ℤ} ⟨f, φ_{j,k}⟩ φ_{j,k}(x)`, with `⟨f, φ_{j,k}⟩ = ∫ f(y) conj φ_{j,k}(y) dy`,

defined at every point for every `f` (`Daubechies.projFun`); only finitely many terms are nonzero
at each point.

* **Bounds.** `‖P_j f‖_p ≤ C ‖f‖_p` for `1 ≤ p < ∞`, with `C = 2N ‖φ‖_p ‖φ‖_{p'}` independent of
  the level (`Daubechies.eLpNorm_projFun_le`, `Daubechies.projConst`), from the stability of the
  expansions (`FunctionSpaces.Wavelets.Examples.Daubechies.Expansion`). On a dyadic cell
  `I = [k/2^j, (k + 1)/2^j)` with the window `W = [(k - 2N + 2)/2^j, (k + 2N - 1)/2^j]`,
  `‖P_j f‖_{L_p(I)} ≤ (2N - 1) ‖φ‖_p ‖φ‖_{p'} ‖f‖_{L_p(W)}` for every `f` and `1 ≤ p ≤ ∞`
  (`Daubechies.eLpNorm_projFun_cell_le`). The projections reproduce the polynomials of degree
  `< N` (`Daubechies.projFun_poly`).
* **Projections and scaling spaces.** On `L_p`, `1 ≤ p < ∞`, the classes of the `P_j f` form
  bounded operators (`Daubechies.proj`, `Daubechies.norm_proj_le`) with `P_j P_j = P_j`
  (`Daubechies.proj_proj`), by coefficient recovery. Their ranges, the **scaling spaces** `V_j`
  (`Daubechies.scalingSpace`), increase with the level (`Daubechies.scalingSpace_mono`): by the
  refinement equation an expansion of level `j` is one of level `j + 1`
  (`Daubechies.expand_eq_expand_succ`, for any finite real filter
  `Daubechies.expand_eq_tsum_refine_of_filter`), so `P_{j+1} P_j = P_j`.
* **Density.** The partition of unity `∑_k φ(x - k) = 1` gives the kernel form
  `P_j f(x) - f(x) = ∑_k φ_{j,k}(x) ∫ (f(y) - f(x)) conj φ_{j,k}(y) dy`
  (`Daubechies.projFun_sub_eq_tsum`), and for continuous `f` with compact support uniform
  continuity gives `‖f - P_j f‖_p → 0` (`Daubechies.tendsto_eLpNorm_sub_projFun`). Hence
  `⋃_j V_j` is dense in `L_p` (`Daubechies.closure_iUnion_scalingSpace`), and `P_j f → f` for every
  `f ∈ L_p` (`Daubechies.tendsto_proj`).
* **Schemes.** The scaling spaces form the approximation scheme `Daubechies.scheme` (`{0}` at
  complexity `0`, `V_{⌊log₂ n⌋}` at complexity `n ≥ 1`), dense in `L_p`
  (`Daubechies.closure_iUnion_scheme`), with the projection scheme
  `Daubechies.projectionScheme` (`0` at complexity `0`, `P_{⌊log₂ n⌋}` at complexity `n ≥ 1`).
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal ComplexConjugate
open ENNReal (dyadicWeight)

namespace Daubechies

variable {N : ℕ} (m : Mask N)

/-! ### The projection of level `j`, pointwise -/

/-- **The projection of level `j`, pointwise**: for every function `f : ℝ → ℂ`,
`P_j f(x) = ∑_{k ∈ ℤ} ⟨f, φ_{j,k}⟩ φ_{j,k}(x)`, with the coefficients
`⟨f, φ_{j,k}⟩ = ∫ f(y) conj φ_{j,k}(y) dy` (`Daubechies.coeffFun`) and the functions
`φ_{j,k}(x) = 2^(j/2) φ(2^j x - k)` (`Daubechies.scaled`). Only finitely many terms are nonzero at
each point, so the sum is meaningful for every `f`; for locally integrable `f` the coefficients
are genuine integrals. -/
noncomputable def projFun (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  expand (scalingFun m) j (coeffFun (scalingFun m) j f)

/-- `P_j f(x) = ∑_{k ∈ ℤ} ⟨f, φ_{j,k}⟩ φ_{j,k}(x)`, by definition. -/
theorem projFun_apply (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    projFun m j f x = ∑' k : ℤ, coeffFun (scalingFun m) j f k * scaled m j k x := rfl

/-- **The projection is continuous**: for `N ≥ 2`, `P_j f` is continuous for every level `j` and
every `f`, as an expansion in the continuous functions `φ_{j,k}`
(`Daubechies.continuous_expand`). -/
theorem continuous_projFun (hN : 2 ≤ N) (j : ℕ) (f : ℝ → ℂ) : Continuous (projFun m j f) :=
  continuous_expand (continuous_scalingFun m hN) (fun _ hx => scalingFun_eq_zero m hN hx) j _

/-- **The projection depends only on the class of `f`**: if `f = f'` almost everywhere, then
`P_j f = P_j f'` at every point, since the coefficients agree
(`Daubechies.coeffFun_congr_ae`). -/
theorem projFun_congr_ae {f f' : ℝ → ℂ} (h : f =ᵐ[volume] f') (j : ℕ) :
    projFun m j f = projFun m j f' := by
  rw [projFun, projFun, show coeffFun (scalingFun m) j f = coeffFun (scalingFun m) j f' from
    funext fun k => coeffFun_congr_ae h j k]

/-- **The coefficient integrands of locally integrable functions are integrable**: for `N ≥ 2`
and locally integrable `f`, the function `y ↦ f(y) conj φ_{j,k}(y)` is integrable, since
`φ_{j,k}` is continuous with compact support (Mathlib's
`MeasureTheory.LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`). -/
theorem integrable_mul_conj_scaled (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (j : ℕ) (k : ℤ) : Integrable fun y => f y * conj (scaled m j k y) := by
  have h := hf.integrable_smul_right_of_hasCompactSupport
    (Complex.continuous_conj.comp (continuous_scaledFun (continuous_scalingFun m hN) j k))
    ((hasCompactSupport_scaledFun (fun _ hx => scalingFun_eq_zero m hN hx) j k).comp_left
      (map_zero _))
  simpa only [smul_eq_mul, Function.comp_apply] using h

/-- **The projection is additive** on locally integrable functions: for `N ≥ 2`,
`P_j (f + g) = P_j f + P_j g` at every point (`Daubechies.coeffFun_add`,
`Daubechies.expand_add`). -/
theorem projFun_add (hN : 2 ≤ N) {f g : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (j : ℕ) :
    projFun m j (fun y => f y + g y) = fun x => projFun m j f x + projFun m j g x := by
  funext x
  have hc : coeffFun (scalingFun m) j (fun y => f y + g y) =
      fun k => coeffFun (scalingFun m) j f k + coeffFun (scalingFun m) j g k :=
    funext fun k => coeffFun_add (integrable_mul_conj_scaled m hN hf j k)
      (integrable_mul_conj_scaled m hN hg j k)
  rw [projFun, hc]
  exact expand_add (fun _ hx => scalingFun_eq_zero m hN hx) j _ _ x

/-- **The projection is homogeneous**: `P_j (z f) = z P_j f` for every `z ∈ ℂ` and every `f`
(`Daubechies.coeffFun_const_mul`, `Daubechies.expand_const_mul`). -/
theorem projFun_const_mul (z : ℂ) (f : ℝ → ℂ) (j : ℕ) :
    projFun m j (fun y => z * f y) = fun x => z * projFun m j f x := by
  funext x
  have hc : coeffFun (scalingFun m) j (fun y => z * f y) =
      fun k => z * coeffFun (scalingFun m) j f k :=
    funext fun k => coeffFun_const_mul z f j k
  rw [projFun, hc]
  exact expand_const_mul j z _ x

/-- **The projection is subtractive** on locally integrable functions: for `N ≥ 2`,
`P_j (f - g) = P_j f - P_j g` at every point (`Daubechies.projFun_add` and
`Daubechies.projFun_const_mul` with `z = -1`). -/
theorem projFun_sub (hN : 2 ≤ N) {f g : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (j : ℕ) :
    projFun m j (fun y => f y - g y) = fun x => projFun m j f x - projFun m j g x := by
  have hg' : LocallyIntegrable (fun y => (-1 : ℂ) * g y) volume := by
    simpa only [neg_one_mul, Pi.neg_def] using hg.neg
  have h := projFun_add m hN hf hg' j
  rw [projFun_const_mul] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

/-! ### The uniform bound -/

/-- **The bound of the projections**: the real number
`M^(1 - 1/p) ‖φ‖_p · M^(1/p) ‖φ‖_{p'} = 2N ‖φ‖_p ‖φ‖_{p'}` with the overlap number
`M = ⌈2N - 1⌉ + 1 = 2N` (for `N ≥ 1`) and the conjugate exponent `p'`, the product of the
constants of the upper estimate and of the coefficient estimate of the expansions
(`Daubechies.expandConst`, `Daubechies.coeffConst`, with the support interval `[0, 2N - 1]` of
`φ`). It is the same for every level. -/
noncomputable def projConst (p : ℝ≥0∞) : ℝ :=
  (expandConst (scalingFun m) 0 (2 * N - 1) p * coeffConst (scalingFun m) 0 (2 * N - 1) p).toReal

/-- The bound `projConst m p` is nonnegative. -/
theorem projConst_nonneg (p : ℝ≥0∞) : 0 ≤ projConst m p := ENNReal.toReal_nonneg

/-- For `N ≥ 2` the bound `projConst m p` is the product of the (finite) constants of the upper
estimate and of the coefficient estimate (`Daubechies.expandConst_ne_top`,
`Daubechies.coeffConst_ne_top`). -/
theorem ofReal_projConst (hN : 2 ≤ N) (p : ℝ≥0∞) :
    ENNReal.ofReal (projConst m p) =
      expandConst (scalingFun m) 0 (2 * N - 1) p * coeffConst (scalingFun m) 0 (2 * N - 1) p :=
  ENNReal.ofReal_toReal (ENNReal.mul_ne_top (expandConst_ne_top _ _ (memLp_scalingFun m hN p))
    (coeffConst_ne_top _ _ (memLp_scalingFun m hN _)))

/-- **The projections are bounded on `L_p`, uniformly in the level**: for `N ≥ 2`, `1 ≤ p < ∞`,
every a.e. strongly measurable `f` and every level `j`, `‖P_j f‖_p ≤ C ‖f‖_p` with
`C = projConst m p`, from the upper estimate of the expansions and the coefficient estimate,
whose dyadic weights cancel (`Daubechies.eLpNorm_expand_coeffFun_le`). -/
theorem eLpNorm_projFun_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) :
    eLpNorm (projFun m j f) p volume ≤ ENNReal.ofReal (projConst m p) * eLpNorm f p volume := by
  rw [ofReal_projConst m hN]
  exact eLpNorm_expand_coeffFun_le (continuous_scalingFun m hN).aestronglyMeasurable
    (fun _ hx => scalingFun_eq_zero m hN hx) hp1 hp hf j

/-- **The projection of an `L_p` function lies in `L_p`**: for `N ≥ 2`, `1 ≤ p < ∞`, `f ∈ L_p`
and every level `j` (`Daubechies.memLp_expand_coeffFun`). -/
theorem memLp_projFun (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {f : ℝ → ℂ}
    (hf : MemLp f p volume) (j : ℕ) : MemLp (projFun m j f) p volume :=
  memLp_expand_coeffFun (continuous_scalingFun m hN) (fun _ hx => scalingFun_eq_zero m hN hx)
    hp1 hp hf j

/-! ### The local bound on a dyadic cell -/

/-- **Only the positions `k - (2N - 2) ≤ l ≤ k` meet a dyadic cell**: for `N ≥ 2`, if `x` lies in
the dyadic cell `[k/2^j, (k + 1)/2^j)` and `l` lies outside `[k - (2N - 2), k]`, then
`φ_{j,l}(x) = 0`. Indeed `φ` vanishes outside the open interval `(0, 2N - 1)`
(`Daubechies.scalingFun_eq_zero_of_notMem_Ioo`), and `0 < 2^j x - l < 2N - 1` together with
`k ≤ 2^j x < k + 1` forces `k - (2N - 1) < l < k + 1`. -/
theorem scaled_eq_zero_of_mem_cell (hN : 2 ≤ N) {j : ℕ} {k l : ℤ} {x : ℝ}
    (hx : x ∈ Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j))
    (hl : l ∉ Finset.Icc (k - (2 * N - 2)) k) : scaled m j l x = 0 := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hx1 : (k : ℝ) ≤ 2 ^ j * x := (div_le_iff₀' h2).1 hx.1
  have hx2 : 2 ^ j * x < (k : ℝ) + 1 := (lt_div_iff₀' h2).1 hx.2
  refine mul_eq_zero_of_right _ (scalingFun_eq_zero_of_notMem_Ioo m hN fun ht => hl ?_)
  obtain ⟨ht1, ht2⟩ := ht
  have hl1 : ((k - (2 * N - 1) : ℤ) : ℝ) < l := by
    push_cast
    linarith
  have hl2 : (l : ℝ) < ((k + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hl1' := Int.cast_lt.1 hl1
  have hl2' := Int.cast_lt.1 hl2
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- **The projection on a dyadic cell is a finite sum**: for `N ≥ 2`, every `f` and every `x` in
the dyadic cell `[k/2^j, (k + 1)/2^j)`,
`P_j f(x) = ∑_{l = k - (2N - 2)}^{k} ⟨f, φ_{j,l}⟩ φ_{j,l}(x)`
(`Daubechies.scaled_eq_zero_of_mem_cell`). -/
theorem projFun_eq_sum_of_mem_cell (hN : 2 ≤ N) (j : ℕ) (f : ℝ → ℂ) {k : ℤ} {x : ℝ}
    (hx : x ∈ Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j)) :
    projFun m j f x =
      ∑ l ∈ Finset.Icc (k - (2 * N - 2)) k, coeffFun (scalingFun m) j f l * scaled m j l x :=
  tsum_eq_sum fun l hl => by
    rw [show scaledFun (scalingFun m) j l x = 0 from scaled_eq_zero_of_mem_cell m hN hx hl,
      mul_zero]

/-- **The positions meeting a cell have their supports in one window**: for
`k - (2N - 2) ≤ l ≤ k`, the support window `[l/2^j, (l + 2N - 1)/2^j]` of `φ_{j,l}` lies in the
window `[(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]`. -/
theorem supportWindow_subset_of_mem_Icc {j : ℕ} {k l : ℤ}
    (hl : l ∈ Finset.Icc (k - (2 * N - 2)) k) :
    supportWindow 0 (2 * N - 1) j l ⊆
      Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j) := by
  rw [supportWindow_eq_Icc]
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hl
  have h1' : (k : ℝ) - (2 * N - 2) ≤ l := by exact_mod_cast h1
  have h2' : (l : ℝ) ≤ k := by exact_mod_cast h2
  exact Set.Icc_subset_Icc (by gcongr; linarith) (by gcongr)

/-- The number of positions meeting a cell: `[k - (2N - 2), k]` contains `2N - 1` integers, for
`N ≥ 1`. -/
theorem card_Icc_sub_two_mul_sub_two (hN : 1 ≤ N) (k : ℤ) :
    (Finset.Icc (k - (2 * N - 2)) k).card = 2 * N - 1 := by
  rw [Int.card_Icc]
  omega

/-- **The constant of the local bound**: `(2N - 1) ‖φ‖_p ‖φ‖_{p'}` with the conjugate exponent
`p'` (`Daubechies.eLpNorm_projFun_cell_le`). -/
noncomputable def cellConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  ((2 * N - 1 : ℕ) : ℝ≥0∞) *
    (eLpNorm (scalingFun m) p volume * eLpNorm (scalingFun m) (ENNReal.conjExponent p) volume)

/-- The constant of the local bound is finite for `N ≥ 2`, since `φ` lies in every `L_p`. -/
theorem cellConst_ne_top (hN : 2 ≤ N) (p : ℝ≥0∞) : cellConst m p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
    (memLp_scalingFun m hN p).eLpNorm_ne_top (memLp_scalingFun m hN _).eLpNorm_ne_top)

/-- **One term of the projection, bounded on a window**: let `N ≥ 2`, `1 ≤ p`, let `f` be a.e.
strongly measurable, and let the set `W` contain the support window of `φ_{j,l}`. Then
`‖⟨f, φ_{j,l}⟩ φ_{j,l}‖_p ≤ ‖φ‖_p ‖φ‖_{p'} ‖f‖_{L_p(W)}`, from Hölder's inequality on the support
window (`Daubechies.enorm_coeffFun_le`) and the norms `‖φ_{j,l}‖_p = 2^(j(1/2 - 1/p)) ‖φ‖_p` and
`‖φ_{j,l}‖_{p'} = 2^(-j(1/2 - 1/p)) ‖φ‖_{p'}` (`Daubechies.eLpNorm_const_mul_scaledFun`,
`Daubechies.eLpNorm_scaledFun_conjExponent`), whose dyadic weights cancel. -/
theorem eLpNorm_coeffFun_mul_scaled_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) (l : ℤ) {W : Set ℝ}
    (hW : supportWindow 0 (2 * N - 1) j l ⊆ W) :
    eLpNorm (fun x => coeffFun (scalingFun m) j f l * scaled m j l x) p volume ≤
      eLpNorm (scalingFun m) p volume * eLpNorm (scalingFun m) (ENNReal.conjExponent p) volume *
        eLpNorm f p (volume.restrict W) := by
  have hφ := (continuous_scalingFun m hN).aestronglyMeasurable (μ := volume)
  have hc := enorm_coeffFun_le hφ (fun _ ht => scalingFun_eq_zero m hN ht) hp1 hf j l
  rw [eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_supportWindow _ _ j l).nullMeasurableSet,
    eLpNorm_scaledFun_conjExponent hφ hp1] at hc
  have hW' : eLpNorm f p (volume.restrict (supportWindow 0 (2 * N - 1) j l)) ≤
      eLpNorm f p (volume.restrict W) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hW le_rfl)
  rw [eLpNorm_const_mul_scaledFun hφ]
  calc ‖coeffFun (scalingFun m) j f l‖ₑ *
        (dyadicWeight (1 / 2 - 1 / p.toReal) j * eLpNorm (scalingFun m) p volume)
      ≤ eLpNorm f p (volume.restrict W) * (dyadicWeight (-(1 / 2 - 1 / p.toReal)) j *
          eLpNorm (scalingFun m) (ENNReal.conjExponent p) volume) *
        (dyadicWeight (1 / 2 - 1 / p.toReal) j * eLpNorm (scalingFun m) p volume) := by
        gcongr
        exact hc.trans (by gcongr)
    _ = eLpNorm (scalingFun m) p volume * eLpNorm (scalingFun m) (ENNReal.conjExponent p) volume *
          eLpNorm f p (volume.restrict W) * (dyadicWeight (1 / 2 - 1 / p.toReal) j *
            dyadicWeight (-(1 / 2 - 1 / p.toReal)) j) := by ring
    _ = _ := by rw [ENNReal.dyadicWeight_mul_neg_self, mul_one]

/-- **The local bound on a dyadic cell**: for `N ≥ 2`, `1 ≤ p ≤ ∞`, every a.e. strongly measurable
`f`, every level `j` and every `k ∈ ℤ`, the projection on the dyadic cell
`I = [k/2^j, (k + 1)/2^j)` is controlled by `f` on the window
`W = [(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]`:
`‖P_j f‖_{L_p(I)} ≤ (2N - 1) ‖φ‖_p ‖φ‖_{p'} ‖f‖_{L_p(W)}` (the constant `Daubechies.cellConst`
is the same for every `j` and `k`). On `I` only the `2N - 1` positions `k - (2N - 2) ≤ l ≤ k`
contribute (`Daubechies.projFun_eq_sum_of_mem_cell`), the support windows of their `φ_{j,l}` lie
in `W` (`Daubechies.supportWindow_subset_of_mem_Icc`), and each term is bounded by
`Daubechies.eLpNorm_coeffFun_mul_scaled_le`. -/
theorem eLpNorm_projFun_cell_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) (j : ℕ) (k : ℤ) :
    eLpNorm (projFun m j f) p (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j))) ≤
      cellConst m p * eLpNorm f p (volume.restrict
        (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) := by
  rw [eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_Ico
    fun x hx => projFun_eq_sum_of_mem_cell m hN j f hx), ← Finset.sum_fn]
  refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_card_nsmul _ _ _ fun l hl =>
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (eLpNorm_coeffFun_mul_scaled_le m hN hp1 hf j l (supportWindow_subset_of_mem_Icc hl))).trans
    (le_of_eq ?_))
  rw [nsmul_eq_mul, card_Icc_sub_two_mul_sub_two (by omega), cellConst]
  ring

/-! ### Reproduction of expansions and refinement -/

/-- **The projection reproduces expansions**: for `N ≥ 2`, every level `j` and every coefficient
sequence `a : ℤ → ℂ`, `P_j (∑_k a_k φ_{j,k}) = ∑_k a_k φ_{j,k}` at every point, since the
coefficients are recovered, `⟨∑_l a_l φ_{j,l}, φ_{j,k}⟩ = a_k`
(`Daubechies.coeffFun_expand_scalingFun`). -/
theorem projFun_expand (hN : 2 ≤ N) (j : ℕ) (a : ℤ → ℂ) :
    projFun m j (expand (scalingFun m) j a) = expand (scalingFun m) j a := by
  rw [projFun, show coeffFun (scalingFun m) j (expand (scalingFun m) j a) = a from
    funext (coeffFun_expand_scalingFun m hN j a)]

/-- **The pointwise projection is idempotent**: `P_j (P_j f) = P_j f` at every point, for `N ≥ 2`
and every `f`, since `P_j f` is an expansion of level `j` (`Daubechies.projFun_expand`). -/
theorem projFun_projFun (hN : 2 ≤ N) (j : ℕ) (f : ℝ → ℂ) :
    projFun m j (projFun m j f) = projFun m j f :=
  projFun_expand m hN j _

/-- **The projection reproduces polynomials**: for `N ≥ 2`, every complex polynomial `Q` of
degree `< N` and every level `j`, `P_j Q = Q` at every point. This is the dyadic polynomial
reproduction `∑_k 2^j (∫ Q(y) conj φ(2^j y - k) dy) φ(2^j x - k) = Q(x)`
(`Daubechies.sum_inner_poly_mul_scalingFun_two_pow`), since
`⟨Q, φ_{j,k}⟩ φ_{j,k}(x) = 2^j (∫ Q(y) conj φ(2^j y - k) dy) φ(2^j x - k)`. -/
theorem projFun_poly (hN : 2 ≤ N) {Q : Polynomial ℂ} (hQ : Q ∈ Polynomial.degreeLT ℂ N)
    (j : ℕ) : projFun m j (fun y => Q.eval (y : ℂ)) = fun x : ℝ => Q.eval (x : ℂ) := by
  funext x
  rw [projFun_apply, ← sum_inner_poly_mul_scalingFun_two_pow m hN hQ j x]
  refine tsum_congr fun k => ?_
  have hc : coeffFun (scalingFun m) j (fun y => Q.eval (y : ℂ)) k =
      (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) *
        ∫ y : ℝ, Q.eval (y : ℂ) * conj (scalingFun m (2 ^ j * y - k)) := by
    rw [coeffFun, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [scaledFun, map_mul, Complex.conj_ofReal]
    ring
  rw [hc, show scaled m j k x = (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * scalingFun m (2 ^ j * x - k)
    from rfl, ← ofReal_two_rpow_half_mul_self j]
  ring

/-- **The refined coefficients**: for coefficients `a : ℤ → ℂ` of level `j`, the coefficients
`a'_n = ∑_{k ∈ ℤ} a_k c_{n-2k}/√2` of level `j + 1`, with the filter coefficients `c_i`
(`Daubechies.coeff`); only the `k` with `0 ≤ n - 2k ≤ 2N - 1` contribute. They express an
expansion of level `j` as one of level `j + 1`, `∑_k a_k φ_{j,k} = ∑_n a'_n φ_{j+1,n}`
(`Daubechies.expand_eq_expand_succ`). -/
noncomputable def refineCoeff (a : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' k : ℤ, a k * ((coeff m (n - 2 * k) / √2 : ℝ) : ℂ)

/-- **Support of the filter**: if the filter coefficient `c_i` is nonzero, then
`0 ≤ i ≤ 2N - 1` (`Daubechies.coeff_eq_zero`). -/
theorem mem_Icc_of_coeff_ne_zero {i : ℤ} (h : coeff m i ≠ 0) : 0 ≤ i ∧ i ≤ 2 * N - 1 := by
  by_contra h'
  exact h (coeff_eq_zero m (by omega))

/-- **The double sum of a refinement has finitely many terms**: for `N ≥ 2`, a real filter `h`
vanishing outside `[a, b]`, a level `j`, coefficients `c : ℤ → ℂ` and a point `x`, the family
`(k, n) ↦ c_k (h_{n-2k}/√2) φ_{j+1,n}(x)` is summable over `ℤ × ℤ`. A nonzero term needs
`a ≤ n - 2k ≤ b` and `0 ≤ 2^(j+1) x - n ≤ 2N - 1`, which leaves finitely many pairs
(`Daubechies.mem_Icc_ceil_floor`). -/
theorem summable_refine_of_filter (hN : 2 ≤ N) {h : ℤ → ℝ} {a b : ℤ}
    (hh : ∀ i, h i ≠ 0 → a ≤ i ∧ i ≤ b) (j : ℕ) (c : ℤ → ℂ) (x : ℝ) :
    Summable (Function.uncurry fun k n : ℤ =>
      c k * (((h (n - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) n x)) := by
  refine summable_of_ne_finset_zero
    (s := Finset.Icc ⌈2 ^ j * x - (b + (2 * N - 1)) / 2⌉ ⌊2 ^ j * x - a / 2⌋ ×ˢ
      Finset.Icc ⌈2 ^ (j + 1) * x - (2 * N - 1)⌉ ⌊2 ^ (j + 1) * x - 0⌋) fun kn hkn => ?_
  obtain ⟨k, n⟩ := kn
  by_contra hne
  refine hkn ?_
  simp only [Function.uncurry_apply_pair] at hne
  obtain ⟨-, h'⟩ := mul_ne_zero_iff.1 hne
  obtain ⟨hc, hs⟩ := mul_ne_zero_iff.1 h'
  have hc' : h (n - 2 * k) ≠ 0 := fun h0 => hc (by rw [h0, zero_div, Complex.ofReal_zero])
  obtain ⟨h1, h2⟩ := hh _ hc'
  have hw := mem_supportWindow_of_scaledFun_ne_zero (fun _ hy => scalingFun_eq_zero m hN hy) hs
  refine Finset.mem_product.2 ⟨mem_Icc_ceil_floor ?_, mem_Icc_ceil_floor hw⟩
  have h1' : (a : ℝ) ≤ n - 2 * k := by exact_mod_cast h1
  have h2' : (n : ℝ) - 2 * k ≤ b := by exact_mod_cast h2
  obtain ⟨hw1, hw2⟩ := hw
  rw [pow_succ] at hw1 hw2
  constructor <;> linarith

/-- **Refining an expansion through a filter**: if `N ≥ 2`, the real filter `h` vanishes outside
`[a, b]` and `g_{j,k} = ∑_n (h_{n-2k}/√2) φ_{j+1,n}` for every `k`, then
`∑_k c_k g_{j,k}(x) = ∑_n (∑_k c_k h_{n-2k}/√2) φ_{j+1,n}(x)` for all `c` and `x`; the two sums
may be exchanged (`Daubechies.summable_refine_of_filter`). -/
theorem expand_eq_tsum_refine_of_filter (hN : 2 ≤ N) {g : ℝ → ℂ} {h : ℤ → ℝ} {a b : ℤ}
    (hh : ∀ i, h i ≠ 0 → a ≤ i ∧ i ≤ b) (j : ℕ)
    (hg : ∀ (k : ℤ) (x : ℝ), scaledFun g j k x =
      expand (scalingFun m) (j + 1) (fun n => ((h (n - 2 * k) / √2 : ℝ) : ℂ)) x)
    (c : ℤ → ℂ) (x : ℝ) :
    expand g j c x = ∑' n : ℤ,
      (∑' k : ℤ, c k * ((h (n - 2 * k) / √2 : ℝ) : ℂ)) * scaled m (j + 1) n x := by
  calc expand g j c x
      = ∑' k : ℤ, ∑' n : ℤ,
          c k * (((h (n - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) n x) := by
        refine tsum_congr fun k => ?_
        rw [hg k x, expand, ← tsum_mul_left]
    _ = ∑' n : ℤ, ∑' k : ℤ,
          c k * (((h (n - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) n x) :=
        (summable_refine_of_filter m hN hh j c x).tsum_comm.symm
    _ = _ := by
        refine tsum_congr fun n => ?_
        rw [← tsum_mul_right]
        exact tsum_congr fun k => (mul_assoc _ _ _).symm

/-- **The double sum of the refinement has finitely many terms**: for `N ≥ 2` the family
`(k, n) ↦ a_k (c_{n-2k}/√2) φ_{j+1,n}(x)` is summable over `ℤ × ℤ`
(`Daubechies.summable_refine_of_filter`, `Daubechies.mem_Icc_of_coeff_ne_zero`). -/
theorem summable_refine (hN : 2 ≤ N) (j : ℕ) (a : ℤ → ℂ) (x : ℝ) :
    Summable (Function.uncurry fun k n : ℤ =>
      a k * (((coeff m (n - 2 * k) / √2 : ℝ) : ℂ) * scaled m (j + 1) n x)) :=
  summable_refine_of_filter m hN (h := coeff m) (fun _ hi => mem_Icc_of_coeff_ne_zero m hi)
    j a x

/-- **Expansions of level `j` are expansions of level `j + 1`**: for `N ≥ 2`, every level `j`,
coefficients `a : ℤ → ℂ` and point `x`, `∑_k a_k φ_{j,k}(x) = ∑_n a'_n φ_{j+1,n}(x)` with the
refined coefficients `a'_n = ∑_k a_k c_{n-2k}/√2` (`Daubechies.refineCoeff`), by
`Daubechies.expand_eq_tsum_refine_of_filter` and `Daubechies.scaled_eq_expand`. -/
theorem expand_eq_expand_succ (hN : 2 ≤ N) (j : ℕ) (a : ℤ → ℂ) (x : ℝ) :
    expand (scalingFun m) j a x = expand (scalingFun m) (j + 1) (refineCoeff m a) x :=
  expand_eq_tsum_refine_of_filter m hN (h := coeff m)
    (fun _ hi => mem_Icc_of_coeff_ne_zero m hi) j (scaled_eq_expand m hN j) a x

/-- **The projections of consecutive levels**: `P_{j+1} (P_j f) = P_j f` at every point, for
`N ≥ 2` and every `f`. The function `P_j f` is an expansion of level `j + 1`
(`Daubechies.expand_eq_expand_succ`), which `P_{j+1}` reproduces
(`Daubechies.projFun_expand`). -/
theorem projFun_succ_projFun (hN : 2 ≤ N) (j : ℕ) (f : ℝ → ℂ) :
    projFun m (j + 1) (projFun m j f) = projFun m j f := by
  have h : projFun m j f =
      expand (scalingFun m) (j + 1) (refineCoeff m (coeffFun (scalingFun m) j f)) :=
    funext (expand_eq_expand_succ m hN j _)
  rw [h, projFun_expand m hN]

/-! ### Convergence for continuous functions with compact support -/

/-- **Points of one support window are close**: if `x` and `y` both lie in the support window
`{t : 2^j t - k ∈ [a, b]}`, then `|y - x| ≤ (b - a)/2^j`. -/
theorem abs_sub_le_of_mem_supportWindow {a b : ℝ} {j : ℕ} {k : ℤ} {x y : ℝ}
    (hx : x ∈ supportWindow a b j k) (hy : y ∈ supportWindow a b j k) :
    |y - x| ≤ (b - a) / 2 ^ j := by
  rw [supportWindow_eq_Icc] at hx hy
  have h : (b - a) / 2 ^ j = (k + b) / 2 ^ j - (k + a) / 2 ^ j := by ring
  rw [h, abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- **A pointwise bound of `φ_{j,k}`**: if `‖φ(t)‖ ≤ C` for every `t`, then
`‖φ_{j,k}(x)‖ ≤ 2^(j/2) C` for every level `j`, position `k` and point `x`. -/
theorem enorm_scaled_le {C : ℝ≥0∞} (hC : ∀ t, ‖scalingFun m t‖ₑ ≤ C) (j : ℕ) (k : ℤ) (x : ℝ) :
    ‖scaled m j k x‖ₑ ≤ dyadicWeight (1 / 2) j * C := by
  rw [show scaled m j k x = (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * scalingFun m (2 ^ j * x - k)
    from rfl, eNorm_mul, enorm_two_rpow_half]
  gcongr
  exact hC _

/-- `conj φ_{j,k}` is integrable for `N ≥ 2`: it is continuous with compact support. -/
theorem integrable_conj_scaled (hN : 2 ≤ N) (j : ℕ) (k : ℤ) :
    Integrable fun y => conj (scaled m j k y) :=
  (Complex.continuous_conj.comp (continuous_scaledFun (continuous_scalingFun m hN) j k)
    ).integrable_of_hasCompactSupport
    ((hasCompactSupport_scaledFun (fun _ hx => scalingFun_eq_zero m hN hx) j k).comp_left
      (map_zero _))

/-- **`φ_{j,k}` times its integral**: `φ_{j,k}(x) ∫ conj φ_{j,k} = φ(2^j x - k)` for `N ≥ 2`, every
level `j`, position `k` and point `x`. The scaling function is real with `∫ φ = 1`
(`Daubechies.conj_scalingFun`, `Daubechies.integral_scalingFun`), so the substitution `u = 2^j y`
(`Daubechies.integral_eq_two_pow_mul_integral_comp`) gives
`∫ conj φ_{j,k} = 2^(j/2) 2^(-j)`, and `2^(j/2) 2^(j/2) 2^(-j) = 1`. -/
theorem scaled_mul_integral_conj (hN : 2 ≤ N) (j : ℕ) (k : ℤ) (x : ℝ) :
    scaled m j k x * ∫ y, conj (scaled m j k y) = scalingFun m (2 ^ j * x - k) := by
  have h1 : (2 : ℂ) ^ j * ∫ y, scalingFun m (2 ^ j * y - k) = 1 := by
    have h := integral_eq_two_pow_mul_integral_comp (fun u => scalingFun m (u - k)) j
    rw [integral_sub_right_eq_self, integral_scalingFun m hN] at h
    exact h.symm
  have h2 : (fun y => conj (scaled m j k y)) =
      fun y => (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * scalingFun m (2 ^ j * y - k) := by
    funext y
    rw [show scaled m j k y = (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * scalingFun m (2 ^ j * y - k)
      from rfl, map_mul, Complex.conj_ofReal, conj_scalingFun]
  rw [h2, integral_const_mul, show scaled m j k x =
    (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * scalingFun m (2 ^ j * x - k) from rfl]
  calc (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * scalingFun m (2 ^ j * x - k) *
        ((((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * ∫ y, scalingFun m (2 ^ j * y - k))
      = scalingFun m (2 ^ j * x - k) * ((((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) *
          (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * ∫ y, scalingFun m (2 ^ j * y - k)) := by ring
    _ = scalingFun m (2 ^ j * x - k) := by rw [ofReal_two_rpow_half_mul_self, h1, mul_one]

/-- **Partition of unity at level `j`**: for `N ≥ 2`, every level `j` and point `x`,
`∑_{k ∈ ℤ} φ_{j,k}(x) ∫ conj φ_{j,k} = ∑_k φ(2^j x - k) = 1`
(`Daubechies.scaled_mul_integral_conj`, `Daubechies.sum_scalingFun_translate`). -/
theorem tsum_scaled_mul_integral_conj (hN : 2 ≤ N) (j : ℕ) (x : ℝ) :
    ∑' k : ℤ, scaled m j k x * ∫ y, conj (scaled m j k y) = 1 := by
  simp only [scaled_mul_integral_conj m hN]
  exact sum_scalingFun_translate m hN (2 ^ j * x)

/-- **The positions contributing at a point**: for `N ≥ 2`, `φ_{j,k}(x) = 0` unless
`⌈2^j x - (2N - 1)⌉ ≤ k ≤ ⌊2^j x⌋` (`Daubechies.scaledFun_eq_zero`,
`Daubechies.mem_Icc_ceil_floor`). -/
theorem scaled_eq_zero_of_notMem_Icc (hN : 2 ≤ N) {j : ℕ} {k : ℤ} {x : ℝ}
    (hk : k ∉ Finset.Icc ⌈2 ^ j * x - (2 * N - 1)⌉ ⌊2 ^ j * x⌋) : scaled m j k x = 0 :=
  scaledFun_eq_zero (fun _ hy => scalingFun_eq_zero m hN hy) fun hx =>
    hk (by simpa only [sub_zero] using mem_Icc_ceil_floor hx)

/-- **Sums over the positions at a point are finite**: for `N ≥ 2`, a level `j`, a point `x` and
a family `F : ℤ → ℂ` with `F k = 0` whenever `φ_{j,k}(x) = 0`,
`∑_{k ∈ ℤ} F k = ∑_{k = ⌈2^j x - (2N - 1)⌉}^{⌊2^j x⌋} F k`
(`Daubechies.scaled_eq_zero_of_notMem_Icc`). -/
theorem tsum_eq_sum_of_scaled_eq_zero (hN : 2 ≤ N) {j : ℕ} {x : ℝ} {F : ℤ → ℂ}
    (hF : ∀ k, scaled m j k x = 0 → F k = 0) :
    ∑' k, F k = ∑ k ∈ Finset.Icc ⌈2 ^ j * x - (2 * N - 1)⌉ ⌊2 ^ j * x⌋, F k :=
  tsum_eq_sum fun k hk => hF k (scaled_eq_zero_of_notMem_Icc m hN hk)

/-- The families of `Daubechies.tsum_eq_sum_of_scaled_eq_zero` are summable: they have only
finitely many nonzero terms. -/
theorem summable_of_scaled_eq_zero (hN : 2 ≤ N) {j : ℕ} {x : ℝ} {F : ℤ → ℂ}
    (hF : ∀ k, scaled m j k x = 0 → F k = 0) : Summable F :=
  summable_of_ne_finset_zero fun k hk => hF k (scaled_eq_zero_of_notMem_Icc m hN hk)

/-- **Counting the contributing positions**: for `N ≥ 1` and every `t ∈ ℝ`, the interval
`[⌈t - (2N - 1)⌉, ⌊t⌋]` contains at most `2N` integers (`Daubechies.card_Icc_ceil_floor_le`). -/
theorem card_Icc_ceil_floor_le_two_mul (hN : 1 ≤ N) (t : ℝ) :
    (Finset.Icc ⌈t - (2 * N - 1)⌉ ⌊t⌋).card ≤ 2 * N := by
  have h := card_Icc_ceil_floor_le t 0 (2 * N - 1)
  simp only [sub_zero] at h
  have hc : ⌈(2 * N - 1 : ℝ)⌉₊ ≤ 2 * N - 1 :=
    Nat.ceil_le.2 (le_of_eq (by rw [Nat.cast_sub (by omega : 1 ≤ 2 * N)]; push_cast; ring))
  omega

/-- **The kernel form of `P_j f - f`**: for `N ≥ 2`, locally integrable `f`, every level `j` and
point `x`, `P_j f(x) - f(x) = ∑_{k ∈ ℤ} φ_{j,k}(x) ∫ (f(y) - f(x)) conj φ_{j,k}(y) dy`. Subtract
`f(x) = ∑_k φ_{j,k}(x) f(x) ∫ conj φ_{j,k}` (`Daubechies.tsum_scaled_mul_integral_conj`) term by
term; both sums have only finitely many nonzero terms. -/
theorem projFun_sub_eq_tsum (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (j : ℕ)
    (x : ℝ) :
    projFun m j f x - f x =
      ∑' k : ℤ, scaled m j k x * ∫ y, (f y - f x) * conj (scaled m j k y) := by
  have hint : ∀ k : ℤ, ∫ y, (f y - f x) * conj (scaled m j k y) =
      coeffFun (scalingFun m) j f k - f x * ∫ y, conj (scaled m j k y) := fun k => by
    simp only [sub_mul]
    rw [integral_sub (integrable_mul_conj_scaled m hN hf j k)
      ((integrable_conj_scaled m hN j k).const_mul (f x)), integral_const_mul]
    rfl
  have hs1 : Summable fun k : ℤ => scaled m j k x * coeffFun (scalingFun m) j f k :=
    summable_of_scaled_eq_zero m hN fun k hk => by rw [hk, zero_mul]
  have hs2 : Summable fun k : ℤ => scaled m j k x * (f x * ∫ y, conj (scaled m j k y)) :=
    summable_of_scaled_eq_zero m hN fun k hk => by rw [hk, zero_mul]
  simp only [hint, mul_sub]
  rw [hs1.tsum_sub hs2]
  congr 1
  · rw [projFun_apply]
    exact tsum_congr fun k => mul_comm _ _
  · rw [show (fun k : ℤ => scaled m j k x * (f x * ∫ y, conj (scaled m j k y))) =
      fun k => f x * (scaled m j k x * ∫ y, conj (scaled m j k y)) from
        funext fun k => mul_left_comm _ _ _, tsum_mul_left, tsum_scaled_mul_integral_conj m hN,
      mul_one]

/-- **A local bound for one kernel term**: let `N ≥ 2`, `‖φ(t)‖ ≤ C` for all `t`, and let `η`
bound `‖f(y) - f(x)‖` for all `y` with `|y - x| ≤ (2N - 1)/2^j`. Then
`‖φ_{j,k}(x) ∫ (f(y) - f(x)) conj φ_{j,k}(y) dy‖ ≤ C ‖φ‖_1 η` for every position `k`. The term
vanishes unless `x` lies in the support window of `φ_{j,k}`; then every `y` of that window has
`|y - x| ≤ (2N - 1)/2^j` (`Daubechies.abs_sub_le_of_mem_supportWindow`), so the integral is at
most `η ‖φ_{j,k}‖_1 = η 2^(-j/2) ‖φ‖_1` (`Daubechies.eLpNorm_scaledFun`), while
`‖φ_{j,k}(x)‖ ≤ 2^(j/2) C` (`Daubechies.enorm_scaled_le`). -/
theorem enorm_scaled_mul_integral_sub_le (hN : 2 ≤ N) {f : ℝ → ℂ} {C : ℝ≥0∞}
    (hC : ∀ t, ‖scalingFun m t‖ₑ ≤ C) (j : ℕ) (k : ℤ) (x : ℝ) {η : ℝ≥0∞}
    (hη : ∀ y, |y - x| ≤ (2 * N - 1) / 2 ^ j → ‖f y - f x‖ₑ ≤ η) :
    ‖scaled m j k x * ∫ y, (f y - f x) * conj (scaled m j k y)‖ₑ ≤
      C * eLpNorm (scalingFun m) 1 volume * η := by
  have hsupp : ∀ t ∉ Set.Icc (0 : ℝ) (2 * N - 1), scalingFun m t = 0 :=
    fun _ ht => scalingFun_eq_zero m hN ht
  by_cases hx : scaled m j k x = 0
  · rw [hx, zero_mul, eNorm_zero]
    positivity
  have hxw := mem_supportWindow_of_scaledFun_ne_zero hsupp hx
  have hs := continuous_scaledFun (continuous_scalingFun m hN) j k
  have h1 : ∫⁻ y, ‖(f y - f x) * conj (scaled m j k y)‖ₑ ≤ ∫⁻ y, η * ‖scaled m j k y‖ₑ := by
    refine lintegral_mono fun y => ?_
    rw [eNorm_mul, RCLike.eNorm_conj]
    by_cases hy : scaled m j k y = 0
    · rw [hy, eNorm_zero, mul_zero, mul_zero]
    · gcongr
      exact hη y ((abs_sub_le_of_mem_supportWindow hxw
        (mem_supportWindow_of_scaledFun_ne_zero hsupp hy)).trans_eq (by rw [sub_zero]))
  have h2 : ‖∫ y, (f y - f x) * conj (scaled m j k y)‖ₑ ≤
      η * (dyadicWeight (-(1 / 2)) j * eLpNorm (scalingFun m) 1 volume) := by
    have hw : (1 : ℝ) / 2 - 1 / (1 : ℝ≥0∞).toReal = -(1 / 2) := by norm_num
    calc ‖∫ y, (f y - f x) * conj (scaled m j k y)‖ₑ
        ≤ ∫⁻ y, ‖(f y - f x) * conj (scaled m j k y)‖ₑ := eNorm_integral_le_lintegral_eNorm _
      _ ≤ ∫⁻ y, η * ‖scaled m j k y‖ₑ := h1
      _ = η * ∫⁻ y, ‖scaled m j k y‖ₑ := lintegral_const_mul η hs.measurable.eNorm
      _ = η * (dyadicWeight (-(1 / 2)) j * eLpNorm (scalingFun m) 1 volume) := by
          rw [← eLpNorm_one_eq_lintegral_eNorm hs.aestronglyMeasurable,
            eLpNorm_scaledFun (continuous_scalingFun m hN).aestronglyMeasurable, hw]
  calc ‖scaled m j k x * ∫ y, (f y - f x) * conj (scaled m j k y)‖ₑ
      = ‖scaled m j k x‖ₑ * ‖∫ y, (f y - f x) * conj (scaled m j k y)‖ₑ := eNorm_mul _ _
    _ ≤ (dyadicWeight (1 / 2) j * C) *
          (η * (dyadicWeight (-(1 / 2)) j * eLpNorm (scalingFun m) 1 volume)) :=
        mul_le_mul' (enorm_scaled_le m hC j k x) h2
    _ = C * eLpNorm (scalingFun m) 1 volume * η *
          (dyadicWeight (1 / 2) j * dyadicWeight (-(1 / 2)) j) := by ring
    _ = C * eLpNorm (scalingFun m) 1 volume * η := by
        rw [ENNReal.dyadicWeight_mul_neg_self, mul_one]

/-- **A pointwise bound for `P_j f - f`**: let `N ≥ 2`, let `f` be locally integrable, let
`‖φ(t)‖ ≤ C` for all `t`, and let `η` bound `‖f(y) - f(x)‖` for all `y` with
`|y - x| ≤ (2N - 1)/2^j`. Then `‖P_j f(x) - f(x)‖ ≤ 2N C ‖φ‖_1 η`. The kernel form
(`Daubechies.projFun_sub_eq_tsum`) has at most `2N` nonzero terms at `x`
(`Daubechies.card_Icc_ceil_floor_le_two_mul`), each bounded by
`Daubechies.enorm_scaled_mul_integral_sub_le`. -/
theorem enorm_projFun_sub_le (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : LocallyIntegrable f volume)
    {C : ℝ≥0∞} (hC : ∀ t, ‖scalingFun m t‖ₑ ≤ C) (j : ℕ) (x : ℝ) {η : ℝ≥0∞}
    (hη : ∀ y, |y - x| ≤ (2 * N - 1) / 2 ^ j → ‖f y - f x‖ₑ ≤ η) :
    ‖projFun m j f x - f x‖ₑ ≤ 2 * N * (C * eLpNorm (scalingFun m) 1 volume * η) := by
  rw [projFun_sub_eq_tsum m hN hf j x,
    tsum_eq_sum_of_scaled_eq_zero m hN fun k hk => by rw [hk, zero_mul]]
  refine (eNorm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ fun k _ =>
    enorm_scaled_mul_integral_sub_le m hN hC j k x hη).trans ?_)
  rw [nsmul_eq_mul]
  gcongr
  exact_mod_cast card_Icc_ceil_floor_le_two_mul (by omega) _

/-- **The `L_p` error of `P_j f` for a continuous function with compact support**: let `N ≥ 2`,
let `f` be continuous with `f(x) = 0` for `|x| ≥ R`, let `‖φ(t)‖ ≤ C` for all `t`, and let `η`
bound `‖f(y) - f(x)‖` for all `x, y` with `|y - x| ≤ (2N - 1)/2^j`. Then for every exponent `p`,
`‖f - P_j f‖_p ≤ 2N C ‖φ‖_1 η |[-R - 2N, R + 2N]|^(1/p)`. The pointwise bound
`Daubechies.enorm_projFun_sub_le` holds everywhere, and `P_j f - f` vanishes for
`|x| > R + 2N`, where the same bound holds with `η = 0`. -/
theorem eLpNorm_sub_projFun_le (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ x : ℝ, R ≤ ‖x‖ → f x = 0) {C : ℝ≥0∞} (hC : ∀ t, ‖scalingFun m t‖ₑ ≤ C) (j : ℕ)
    {η : ℝ≥0∞} (hη : ∀ x y : ℝ, |y - x| ≤ (2 * N - 1) / 2 ^ j → ‖f y - f x‖ₑ ≤ η)
    (p : ℝ≥0∞) :
    eLpNorm (f - projFun m j f) p volume ≤ 2 * N * (C * eLpNorm (scalingFun m) 1 volume * η) *
      volume (Metric.closedBall (0 : ℝ) (R + 2 * N)) ^ p.toReal⁻¹ := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmeas : AEStronglyMeasurable (f - projFun m j f) volume :=
    (hf.sub (continuous_projFun m hN j f)).aestronglyMeasurable
  have hsupp : Function.support (f - projFun m j f) ⊆ Metric.closedBall 0 (R + 2 * N) := by
    intro x hx
    by_contra hxK
    rw [Metric.mem_closedBall, dist_zero_right, not_le, Real.norm_eq_abs] at hxK
    refine hx ?_
    have hfx : f x = 0 := hR x (by rw [Real.norm_eq_abs]; linarith)
    have h0 := enorm_projFun_sub_le m hN hf.locallyIntegrable hC j x (η := 0) fun y hy => by
      have h2 : (2 * N - 1 : ℝ) / 2 ^ j ≤ 2 * N - 1 :=
        div_le_self (by linarith) (one_le_pow₀ one_le_two)
      have h3 := abs_sub_abs_le_abs_sub x y
      rw [abs_sub_comm x y] at h3
      rw [hfx, hR y (by rw [Real.norm_eq_abs]; linarith), sub_zero, eNorm_zero]
    rw [mul_zero, mul_zero, nonpos_iff_eq_zero, eNorm_eq_zero, sub_eq_zero, hfx] at h0
    rw [Pi.sub_apply, h0, hfx, sub_self]
  rw [← eLpNorm_restrict_eq_of_support_subset hmeas hsupp]
  refine (eLpNorm_le_of_ae_eNorm_bound (C := 2 * N * (C * eLpNorm (scalingFun m) 1 volume * η))
    hmeas.restrict (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Pi.sub_apply, eNorm_sub_rev]
    exact enorm_projFun_sub_le m hN hf.locallyIntegrable hC j x (hη x)
  · rw [Measure.restrict_apply_univ, smul_eq_mul]

/-- **Dyadic scales become small**: for every `c ∈ ℝ` and `δ > 0` there is a level `J` with
`c/2^J < δ`. -/
theorem exists_div_two_pow_lt (c : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ J : ℕ, c / 2 ^ J < δ := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (c / δ)
  refine ⟨J, ?_⟩
  have h2 : (J : ℝ) < 2 ^ J := by exact_mod_cast Nat.lt_two_pow_self
  have h3 : (J : ℝ) * δ < 2 ^ J * δ := mul_lt_mul_of_pos_right h2 hδ
  rw [div_lt_iff₀ hδ] at hJ
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- **`P_j f → f` for continuous functions with compact support**: for `N ≥ 2`, every continuous
`f` with compact support and every exponent `p`, `‖f - P_j f‖_p → 0` as `j → ∞`. The function
`f` is uniformly continuous, so `‖f(y) - f(x)‖ ≤ η` once `|y - x| ≤ (2N - 1)/2^j` and `j` is
large; `φ` is bounded; and `Daubechies.eLpNorm_sub_projFun_le` bounds the error by a fixed
multiple of `η`. -/
theorem tendsto_eLpNorm_sub_projFun (hN : 2 ≤ N) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (p : ℝ≥0∞) :
    Tendsto (fun j => eLpNorm (f - projFun m j f) p volume) atTop (𝓝 0) := by
  obtain ⟨R, -, hR⟩ := hfc.exists_pos_le_norm
  obtain ⟨C, hC⟩ := (continuous_scalingFun m hN).bounded_above_of_compact_support
    (hasCompactSupport_scalingFun m hN)
  have hC' : ∀ t, ‖scalingFun m t‖ₑ ≤ ENNReal.ofReal C := fun t => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC t)
  have hA : 2 * N * (ENNReal.ofReal C * eLpNorm (scalingFun m) 1 volume) *
      volume (Metric.closedBall (0 : ℝ) (R + 2 * N)) ^ p.toReal⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (memLp_scalingFun m hN 1).eLpNorm_ne_top))
      (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (by rw [Real.volume_closedBall]; exact ENNReal.ofReal_ne_top))
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hA hε.ne'
  obtain ⟨δ, hδ0, hδ⟩ :=
    Metric.uniformContinuous_iff.1 (hfc.uniformContinuous_of_continuous hf) η hη0
  obtain ⟨J, hJ⟩ := exists_div_two_pow_lt (2 * N - 1) hδ0
  refine ⟨J, fun j hj => (eLpNorm_sub_projFun_le m hN hf hR hC' j (η := η)
    (fun x y hxy => ?_) p).trans ?_⟩
  · have hjJ : (2 * N - 1 : ℝ) / 2 ^ j ≤ (2 * N - 1) / 2 ^ J :=
      div_le_div_of_nonneg_left (by linarith [show (2 : ℝ) ≤ N by exact_mod_cast hN])
        (by positivity) (pow_le_pow_right₀ one_le_two hj)
    have hd : dist y x < δ := by
      rw [Real.dist_eq]
      linarith
    rw [← eDist_eq_eNorm_sub, edist_dist]
    exact (ENNReal.ofReal_le_ofReal (hδ hd).le).trans_eq ENNReal.ofReal_coe_nnreal
  · calc 2 * N * (ENNReal.ofReal C * eLpNorm (scalingFun m) 1 volume * η) *
          volume (Metric.closedBall (0 : ℝ) (R + 2 * N)) ^ p.toReal⁻¹
        = η * (2 * N * (ENNReal.ofReal C * eLpNorm (scalingFun m) 1 volume) *
            volume (Metric.closedBall (0 : ℝ) (R + 2 * N)) ^ p.toReal⁻¹) := by ring
      _ ≤ ε := hηε.le

/-! ### The projection of level `j` on `L_p` -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- **The projection of level `j` as a linear map on `L_p`**, for `N ≥ 2` and `1 ≤ p < ∞`: the
class of the pointwise projection `P_j f` (`Daubechies.projFun`) of a representative of `f`. -/
noncomputable def projLinear (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    Lp ℂ p (volume : Measure ℝ) →ₗ[ℝ] Lp ℂ p (volume : Measure ℝ) where
  toFun f := (memLp_projFun m hN Fact.out hp (Lp.memLp f) j).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    rw [projFun_congr_ae m (Lp.coeFn_add f g) j]
    exact congrFun (projFun_add m hN ((Lp.memLp f).locallyIntegrable Fact.out)
      ((Lp.memLp g).locallyIntegrable Fact.out) j) x
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    have hcf : ⇑(c • f) =ᵐ[volume] fun y => (c : ℂ) * f y :=
      (Lp.coeFn_smul c f).mono fun y hy => by rw [hy, Pi.smul_apply, Complex.real_smul]
    rw [projFun_congr_ae m hcf j, projFun_const_mul, Pi.smul_apply, Complex.real_smul]

variable (p) in
/-- **The projection of level `j` on `L_p`**, for `N ≥ 2` and `1 ≤ p < ∞`:
`P_j f = ∑_{k ∈ ℤ} ⟨f, φ_{j,k}⟩ φ_{j,k}`, a bounded operator whose norm is at most
`projConst m p` for every level (`Daubechies.norm_proj_le`). -/
noncomputable def proj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    Lp ℂ p (volume : Measure ℝ) →L[ℝ] Lp ℂ p (volume : Measure ℝ) :=
  LinearMap.mkContinuous (projLinear m p hN hp j) (projConst m p) fun f => by
    have hmem := memLp_projFun m hN Fact.out hp (Lp.memLp f) j
    rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal (projConst_nonneg m p),
      ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) ?_
    rw [show projLinear m p hN hp j f = hmem.toLp _ from rfl,
      eLpNorm_congr_ae (MemLp.coeFn_toLp hmem)]
    exact eLpNorm_projFun_le m hN Fact.out hp (Lp.aestronglyMeasurable f) j

/-- **The projection is the pointwise projection almost everywhere**:
`P_j f = ∑_k ⟨f, φ_{j,k}⟩ φ_{j,k}` almost everywhere, for every `f ∈ L_p`. -/
theorem proj_apply_ae (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure ℝ)) :
    proj m p hN hp j f =ᵐ[volume] projFun m j f :=
  MemLp.coeFn_toLp (memLp_projFun m hN Fact.out hp (Lp.memLp f) j)

/-- **The projections are uniformly bounded**: `‖P_j‖ ≤ projConst m p` for every level `j`. -/
theorem norm_proj_le (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) : ‖proj m p hN hp j‖ ≤ projConst m p :=
  LinearMap.mkContinuous_norm_le _ (projConst_nonneg m p) _

/-- **The uniform bound in extended norms**: `‖P_j f‖_p ≤ C ‖f‖_p` with `C = projConst m p`, for
every `f ∈ L_p` and every level `j` (`Daubechies.eLpNorm_projFun_le`). -/
theorem enorm_proj_le (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure ℝ)) :
    ‖proj m p hN hp j f‖ₑ ≤ ENNReal.ofReal (projConst m p) * ‖f‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (proj_apply_ae m hN hp j f)]
  exact eLpNorm_projFun_le m hN Fact.out hp (Lp.aestronglyMeasurable f) j

/-! ### The scaling spaces -/

/-- **`P_j` is a projection**: `P_j (P_j f) = P_j f` for every `f ∈ L_p`, for `N ≥ 2` and
`1 ≤ p < ∞` (`Daubechies.projFun_projFun`). -/
theorem proj_proj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure ℝ)) :
    proj m p hN hp j (proj m p hN hp j f) = proj m p hN hp j f := by
  refine Lp.ext ((proj_apply_ae m hN hp j _).trans ?_)
  rw [projFun_congr_ae m (proj_apply_ae m hN hp j f) j, projFun_projFun m hN]
  exact (proj_apply_ae m hN hp j f).symm

/-- **The projections of consecutive levels**: `P_{j+1} (P_j f) = P_j f` for every `f ∈ L_p`, for
`N ≥ 2` and `1 ≤ p < ∞` (`Daubechies.projFun_succ_projFun`). -/
theorem proj_succ_proj (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) (f : Lp ℂ p (volume : Measure ℝ)) :
    proj m p hN hp (j + 1) (proj m p hN hp j f) = proj m p hN hp j f := by
  refine Lp.ext ((proj_apply_ae m hN hp (j + 1) _).trans ?_)
  rw [projFun_congr_ae m (proj_apply_ae m hN hp j f) (j + 1), projFun_succ_projFun m hN]
  exact (proj_apply_ae m hN hp j f).symm

variable (p) in
/-- **The scaling space of level `j`**: the range `V_j` of the projection `P_j` in `L_p`, for
`N ≥ 2` and `1 ≤ p < ∞`, a real subspace of `L_p`. It consists of the classes of the expansions
`∑_k ⟨f, φ_{j,k}⟩ φ_{j,k}`, `f ∈ L_p`, and `P_j` is the identity on it
(`Daubechies.proj_eq_self_of_mem`). -/
noncomputable def scalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    Submodule ℝ (Lp ℂ p (volume : Measure ℝ)) :=
  LinearMap.range (proj m p hN hp j).toLinearMap

/-- `a ∈ V_j` iff `a = P_j f` for some `f ∈ L_p`. -/
theorem mem_scalingSpace {hN : 2 ≤ N} {hp : p ≠ ∞} {j : ℕ} {a : Lp ℂ p (volume : Measure ℝ)} :
    a ∈ scalingSpace m p hN hp j ↔ ∃ f, proj m p hN hp j f = a :=
  LinearMap.mem_range

/-- The projection `P_j f` lies in the scaling space `V_j`. -/
theorem proj_mem_scalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ)
    (f : Lp ℂ p (volume : Measure ℝ)) : proj m p hN hp j f ∈ scalingSpace m p hN hp j :=
  LinearMap.mem_range_self _ f

/-- **The projection fixes the scaling space**: `P_j a = a` for every `a ∈ V_j`
(`Daubechies.proj_proj`). -/
theorem proj_eq_self_of_mem (hN : 2 ≤ N) (hp : p ≠ ∞) {j : ℕ} {a : Lp ℂ p (volume : Measure ℝ)}
    (ha : a ∈ scalingSpace m p hN hp j) : proj m p hN hp j a = a := by
  obtain ⟨f, rfl⟩ := (mem_scalingSpace m).1 ha
  exact proj_proj m hN hp j f

/-- **The scaling spaces are nested**: `V_j ⊆ V_{j+1}`, since `P_j f = P_{j+1} (P_j f)`
(`Daubechies.proj_succ_proj`), a consequence of the refinement equation. -/
theorem scalingSpace_le_succ (hN : 2 ≤ N) (hp : p ≠ ∞) (j : ℕ) :
    scalingSpace m p hN hp j ≤ scalingSpace m p hN hp (j + 1) := fun a ha => by
  obtain ⟨f, rfl⟩ := (mem_scalingSpace m).1 ha
  exact (mem_scalingSpace m).2 ⟨proj m p hN hp j f, proj_succ_proj m hN hp j f⟩

/-- **The scaling spaces increase with the level**: `V_i ⊆ V_j` for `i ≤ j`
(`Daubechies.scalingSpace_le_succ`). -/
theorem scalingSpace_mono (hN : 2 ≤ N) (hp : p ≠ ∞) : Monotone (scalingSpace m p hN hp) :=
  monotone_nat_of_le_succ (scalingSpace_le_succ m hN hp)

/-! ### The approximation scheme and the projection scheme -/

variable (p) in
/-- **The Daubechies scheme** in `L_p`, for `N ≥ 2` and `1 ≤ p < ∞`: `{0}` at complexity `0` and
the scaling space `V_{⌊log₂ n⌋}` at complexity `n ≥ 1`, so that `V_k` is the set of approximants
of complexity `2^k` (`ApproximationScheme.ofMonotoneSubmodules`). -/
noncomputable def scheme (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ApproximationScheme (Lp ℂ p (volume : Measure ℝ)) :=
  ApproximationScheme.ofMonotoneSubmodules (scalingSpace m p hN hp) (scalingSpace_mono m hN hp)

/-- The approximants of complexity `0` are `{0}`. -/
theorem mem_scheme_zero {hN : 2 ≤ N} {hp : p ≠ ∞} {a : Lp ℂ p (volume : Measure ℝ)} :
    a ∈ scheme m p hN hp 0 ↔ a = 0 :=
  ApproximationScheme.mem_ofMonotoneSubmodules_zero

/-- The approximants of complexity `n ≥ 1` are the elements of the scaling space
`V_{⌊log₂ n⌋}`. -/
theorem mem_scheme {hN : 2 ≤ N} {hp : p ≠ ∞} {n : ℕ} (hn : n ≠ 0)
    {a : Lp ℂ p (volume : Measure ℝ)} :
    a ∈ scheme m p hN hp n ↔ a ∈ scalingSpace m p hN hp (Nat.log 2 n) :=
  ApproximationScheme.mem_ofMonotoneSubmodules hn

/-- The approximants of complexity `2^k` are the elements of the scaling space `V_k`. -/
theorem mem_scheme_two_pow {hN : 2 ≤ N} {hp : p ≠ ∞} {k : ℕ} {a : Lp ℂ p (volume : Measure ℝ)} :
    a ∈ scheme m p hN hp (2 ^ k) ↔ a ∈ scalingSpace m p hN hp k :=
  ApproximationScheme.mem_ofMonotoneSubmodules_two_pow

variable (p) in
/-- **The projection scheme of the Daubechies scaling spaces** in `L_p`, for `N ≥ 2` and
`1 ≤ p < ∞`: the projection of complexity `n ≥ 1` is `P_{⌊log₂ n⌋}`, the one of complexity `0`
is `0` (the approximants of complexity `0` are `{0}`), and all are bounded by `projConst m p`. -/
noncomputable def projectionScheme (hN : 2 ≤ N) (hp : p ≠ ∞) :
    (scheme m p hN hp).ProjectionScheme :=
  ApproximationScheme.ProjectionScheme.ofMonotone (scalingSpace m p hN hp)
    (scalingSpace_mono m hN hp) (proj m p hN hp) (proj_mem_scalingSpace m hN hp)
    (fun _ _ ha => proj_eq_self_of_mem m hN hp ha) (projConst m p) (norm_proj_le m hN hp)

/-- The projection of complexity `2^k` is `P_k`. -/
theorem projectionScheme_two_pow (hN : 2 ≤ N) (hp : p ≠ ∞) (k : ℕ) :
    (projectionScheme m p hN hp).P (2 ^ k) = proj m p hN hp k :=
  ApproximationScheme.ProjectionScheme.ofMonotone_two_pow k

/-! ### Density of the scaling spaces -/

/-- **The scaling spaces are dense** in `L_p`, for `N ≥ 2` and `1 ≤ p < ∞`: the closure of
`⋃_j V_j` is all of `L_p`. Approximate `F ∈ L_p` by a continuous function `g` with compact
support (Mathlib's `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), and `g` by
`P_j g ∈ V_j` (`Daubechies.tendsto_eLpNorm_sub_projFun`). -/
theorem closure_iUnion_scalingSpace (hN : 2 ≤ N) (hp : p ≠ ∞) :
    closure (⋃ j, (scalingSpace m p hN hp j : Set (Lp ℂ p (volume : Measure ℝ)))) = Set.univ := by
  refine Set.eq_univ_of_forall fun F => EMetric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨g, hgc, hFg, hg, hgp⟩ :=
    (Lp.memLp F).exists_hasCompactSupport_eLpNorm_sub_le hp (ENNReal.half_pos hε.ne').ne'
  obtain ⟨j, hj⟩ := ((tendsto_eLpNorm_sub_projFun m hN hg hgc p).eventually
    (gt_mem_nhds (ENNReal.half_pos hε.ne'))).exists
  refine ⟨proj m p hN hp j (hgp.toLp g),
    Set.mem_iUnion.2 ⟨j, proj_mem_scalingSpace m hN hp j _⟩, ?_⟩
  have hP : ⇑(proj m p hN hp j (hgp.toLp g)) =ᵐ[volume] projFun m j g :=
    (proj_apply_ae m hN hp j _).trans
      (EventuallyEq.of_eq (projFun_congr_ae m (MemLp.coeFn_toLp hgp) j))
  rw [Lp.edist_def, eLpNorm_congr_ae ((EventuallyEq.refl _ (⇑F)).sub hP)]
  calc eLpNorm (⇑F - projFun m j g) p volume
      = eLpNorm ((⇑F - g) + (g - projFun m j g)) p volume := by rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (⇑F - g) p volume + eLpNorm (g - projFun m j g) p volume :=
        eLpNorm_add_le Fact.out
    _ < ε / 2 + ε / 2 :=
        ENNReal.add_lt_add_of_le_of_lt ((Lp.memLp F).sub hgp).eLpNorm_ne_top hFg hj
    _ = ε := ENNReal.add_halves ε

/-- **The Daubechies scheme is dense** in `L_p`, for `N ≥ 2` and `1 ≤ p < ∞`: the closure of the
union of its approximants is all of `L_p`, since `V_j` is the set of approximants of complexity
`2^j` (`Daubechies.mem_scheme_two_pow`, `Daubechies.closure_iUnion_scalingSpace`). -/
theorem closure_iUnion_scheme (hN : 2 ≤ N) (hp : p ≠ ∞) :
    closure (⋃ n, scheme m p hN hp n) = Set.univ := by
  refine Set.eq_univ_of_univ_subset
    ((closure_iUnion_scalingSpace m hN hp).symm.subset.trans (closure_mono fun a ha => ?_))
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 ha
  exact Set.mem_iUnion.2 ⟨2 ^ j, (mem_scheme_two_pow m).2 hj⟩

/-- **The projections converge**: `P_j f → f` in `L_p` as `j → ∞`, for every `f ∈ L_p`, `N ≥ 2`
and `1 ≤ p < ∞`. The projections are uniformly bounded and `⋃_j V_j` is dense
(`Daubechies.closure_iUnion_scheme`), so the projection scheme converges
(`ApproximationScheme.ProjectionScheme.tendsto_of_dense`) along the complexities `2^j`
(`Daubechies.projectionScheme_two_pow`). -/
theorem tendsto_proj (hN : 2 ≤ N) (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure ℝ)) :
    Tendsto (fun j => proj m p hN hp j f) atTop (𝓝 f) := by
  have h := ((projectionScheme m p hN hp).tendsto_of_dense (closure_iUnion_scheme m hN hp)
    f).comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  simpa only [Function.comp_def, projectionScheme_two_pow] using h

end Lp

end Daubechies
