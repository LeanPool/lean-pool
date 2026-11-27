/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Taylor
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.JacksonSmoothing
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Projections

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Jackson's inequality for the Daubechies projections

For a Daubechies mask of order `N ≥ 2` with scaling function `φ`, the projections
`P_j f = ∑_{k ∈ ℤ} ⟨f, φ_{j,k}⟩ φ_{j,k}` (`Daubechies.projFun`, `Daubechies.proj`) and the
scaling spaces `V_j` satisfy **Jackson's inequality**: for `1 ≤ p < ∞`, every `f ∈ L_p(ℝ)` and
every level `j ∈ ℕ`, the error of best approximation from `V_j` obeys

`E_{2^j}(f)_p ≤ C_J ω_N(f, 2^(-j))_p`,

with the modulus of smoothness `ω_N(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^N f‖_{L_p(ℝ)}` (`Rd.modulus`) and
a constant `C_J` that depends only on the mask and on `p` (`Daubechies.jacksonConst`,
`Daubechies.approxError_scheme_le_jacksonConst_mul`). This is the Jackson inequality of the
Daubechies scheme (`Daubechies.approxError_scheme_le`). With the uniform bound `C` of the
projections it gives `‖f - P_j f‖_p ≤ (1 + C) C_J ω_N(f, 2^(-j))_p`
(`Daubechies.enorm_sub_proj_le`), and for continuous `f` directly
`‖f - P_j f‖_p ≤ C_J ω_N(f, 2^(-j))_p` (`Daubechies.eLpNorm_sub_projFun_le_modulus`).

The proof has three steps.

* **Smooth functions.** The dyadic cells `I_k = [k/2^j, (k + 1)/2^j)` cover `ℝ`
  (`Daubechies.iUnion_Ico_div_two_pow`), and each lies in its window
  `W_k = [(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]` of length `(4N - 3)/2^j`; every point lies in
  at most `4N - 2` windows (`Daubechies.card_le_of_forall_mem_window`), so
  `∑_k ‖G‖_{L_p(W_k)}^p ≤ (4N - 2) ‖G‖_p^p` (`Daubechies.tsum_eLpNorm_window_rpow_le`). For
  `S ∈ C^N` Taylor's theorem gives a polynomial `Q_k` of degree `< N` with
  `‖S - Q_k‖_{L_p(W_k)} ≤ |W_k|^N ‖S^(N)‖_{L_p(W_k)}` (`Interval.exists_eLpNorm_sub_polyFun_le`).
  The projection reproduces `Q_k`, so `S - P_j S = (S - Q_k) - P_j (S - Q_k)`
  (`Daubechies.sub_projFun_eq_sub_projFun_sub`), and on `I_k` the projection only sees the
  function on `W_k` (`Daubechies.eLpNorm_projFun_cell_le`). Hence
  `‖S - P_j S‖_{L_p(I_k)} ≤ (1 + C) (4N - 3)^N 2^(-jN) ‖S^(N)‖_{L_p(W_k)}`
  (`Daubechies.eLpNorm_sub_projFun_cell_le`), and summing over the cells
  (`MeasureTheory.eLpNorm_le_of_forall_eLpNorm_restrict_le`) gives
  `‖S - P_j S‖_p ≤ C_S 2^(-jN) ‖S^(N)‖_p` (`Daubechies.eLpNorm_sub_projFun_le_of_contDiff`).
* **Continuous functions.** For continuous `f` and the Steklov smoothing `S = S_δ f` at the step
  `δ = 1/(N 2^j)`, `‖f - S‖_p ≤ ω_N(f, 2^(-j))_p` and
  `‖S^(N)‖_p ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p`
  (`FunctionSpaces.Wavelets.Examples.Daubechies.JacksonSmoothing`), while
  `‖f - P_j f‖_p ≤ (1 + C) ‖f - S‖_p + ‖S - P_j S‖_p` with the uniform bound `C` of the
  projections (`Daubechies.eLpNorm_sub_projFun_le_add`). Together:
  `‖f - P_j f‖_p ≤ C_J ω_N(f, 2^(-j))_p` (`Daubechies.eLpNorm_sub_projFun_le_modulus`), and the
  same for every `f ∈ L_p` with a continuous representative
  (`Daubechies.enorm_sub_proj_le_of_continuous`).
* **All of `L_p`.** The functions with a bounded continuous representative are dense in `L_p`
  (Mathlib's `MeasureTheory.Lp.boundedContinuousFunction_dense`), and the error of best
  approximation and the modulus are both controlled by `‖f‖_p`, so the inequality for
  `E_{2^j}(f)_p ≤ ‖f - P_j f‖_p` extends by density
  (`ApproximationScheme.approxError_le_of_dense`). The Lebesgue inequality
  `‖f - P_j f‖_p ≤ (1 + C) E_{2^j}(f)_p` returns to the projections.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal

namespace MeasureTheory

/-- **Summing local bounds over a cover**: let `I_i`, `i ∈ ι`, be countably many sets covering
`α`, let `W_i` be sets, and let `0 < p < ∞`. Let `F : α → ℂ` be a.e. strongly measurable and
`G : α → ℂ` a function whose local norms satisfy the window inequality
`∑_i ‖G‖_{L_p(W_i)}^p ≤ M ‖G‖_p^p`. If `‖F‖_{L_p(I_i)} ≤ B ‖G‖_{L_p(W_i)}` for every `i`, then
`‖F‖_p ≤ M^(1/p) B ‖G‖_p`. Indeed
`‖F‖_p^p = ∫ |F|^p ≤ ∑_i ∫_{I_i} |F|^p ≤ B^p ∑_i ‖G‖_{L_p(W_i)}^p ≤ M B^p ‖G‖_p^p` by the
countable subadditivity of the integral (Mathlib's `MeasureTheory.lintegral_iUnion_le`), which
holds for arbitrary sets `I_i`. -/
theorem eLpNorm_le_of_forall_eLpNorm_restrict_le {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {μ : Measure α} {I W : ι → Set α} (hI : ⋃ i, I i = Set.univ) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) {F G : α → ℂ} (hF : AEStronglyMeasurable F μ) {M B : ℝ≥0∞}
    (hW : ∑' i, eLpNorm G p (μ.restrict (W i)) ^ p.toReal ≤ M * eLpNorm G p μ ^ p.toReal)
    (h : ∀ i, eLpNorm F p (μ.restrict (I i)) ≤ B * eLpNorm G p (μ.restrict (W i))) :
    eLpNorm F p μ ≤ M ^ (1 / p.toReal) * B * eLpNorm G p μ := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hk : ∀ i, ∫⁻ x in I i, ‖F x‖ₑ ^ p.toReal ∂μ ≤
      B ^ p.toReal * eLpNorm G p (μ.restrict (W i)) ^ p.toReal := fun i => by
    rw [← eLpNorm_rpow_eq hF.restrict hp0 hp, ← ENNReal.mul_rpow_of_nonneg _ _ hr.le]
    exact ENNReal.rpow_le_rpow (h i) hr.le
  rw [← ENNReal.rpow_le_rpow_iff hr, eLpNorm_rpow_eq hF hp0 hp]
  calc ∫⁻ x, ‖F x‖ₑ ^ p.toReal ∂μ = ∫⁻ x in ⋃ i, I i, ‖F x‖ₑ ^ p.toReal ∂μ := by
        rw [hI, Measure.restrict_univ]
    _ ≤ ∑' i, ∫⁻ x in I i, ‖F x‖ₑ ^ p.toReal ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' i, B ^ p.toReal * eLpNorm G p (μ.restrict (W i)) ^ p.toReal :=
        tsum_le_tsum hk
    _ = B ^ p.toReal * ∑' i, eLpNorm G p (μ.restrict (W i)) ^ p.toReal := ENNReal.tsum_mul_left
    _ ≤ B ^ p.toReal * (M * eLpNorm G p μ ^ p.toReal) := by gcongr
    _ = (M ^ (1 / p.toReal) * B * eLpNorm G p μ) ^ p.toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
          ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
        ring

end MeasureTheory

namespace Daubechies

variable {N : ℕ} (m : Mask N)

/-! ### Dyadic cells and their windows -/

/-- **The dyadic cells of level `j` cover the line**: every `x ∈ ℝ` lies in the cell
`[k/2^j, (k + 1)/2^j)` with `k = ⌊2^j x⌋`. -/
theorem iUnion_Ico_div_two_pow (j : ℕ) :
    ⋃ k : ℤ, Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌊2 ^ j * x⌋, ?_⟩
  have h : (0 : ℝ) < 2 ^ j := by positivity
  rw [Set.mem_Ico, div_le_iff₀' h, lt_div_iff₀' h]
  exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- **A cell lies in its window**: for `N ≥ 1`, the dyadic cell `[k/2^j, (k + 1)/2^j)` lies in
the window `[(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]`. -/
theorem Ico_subset_window (hN : 1 ≤ N) (j : ℕ) (k : ℤ) :
    Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j) ⊆
      Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine Set.Ico_subset_Icc_self.trans (Set.Icc_subset_Icc ?_ ?_)
  · gcongr
    linarith
  · gcongr
    linarith

/-- The window `[(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]` is the support window
`{x : 2^j x - k ∈ [-(2N - 2), 2N - 1]}` (`Daubechies.supportWindow_eq_Icc`). -/
theorem window_eq_supportWindow (N j : ℕ) (k : ℤ) :
    Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j) =
      supportWindow (-(2 * N - 2)) (2 * N - 1) j k := by
  rw [supportWindow_eq_Icc, sub_eq_add_neg]

/-- **Bounded overlap of the windows**: for `N ≥ 1`, every point `x` lies in at most `4N - 2`
of the windows `[(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]`, `k ∈ ℤ`, of one level `j`. The windows
are the support windows of an interval of length `4N - 3`
(`Daubechies.card_le_of_forall_mem_supportWindow`). -/
theorem card_le_of_forall_mem_window (hN : 1 ≤ N) {j : ℕ} (x : ℝ) (S : Finset ℤ)
    (hS : ∀ k ∈ S,
      x ∈ Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j)) :
    S.card ≤ 4 * N - 2 := by
  have h := card_le_of_forall_mem_supportWindow (a := -(2 * N - 2)) (b := 2 * N - 1) x S
    fun k hk => by
      rw [← window_eq_supportWindow]
      exact hS k hk
  have hc : (2 * (N : ℝ) - 1) - (-(2 * N - 2)) = ((4 * N - 3 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hc, Nat.ceil_natCast] at h
  omega

/-- **Window summation**: for `N ≥ 1`, `0 < p < ∞`, every a.e. strongly measurable `G : ℝ → ℂ`
and every level `j`, the windows `W_k = [(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]` satisfy
`∑_{k ∈ ℤ} ‖G‖_{L_p(W_k)}^p ≤ (4N - 2) ‖G‖_p^p`. This is the window inequality
`∑_k ∫_{W_k} |G|^p ≤ M ∫ |G|^p` (`MeasureTheory.tsum_setLIntegral_le_mul_lintegral`) with the
overlap number `M = 4N - 2` (`Daubechies.card_le_of_forall_mem_window`). -/
theorem tsum_eLpNorm_window_rpow_le (hN : 1 ≤ N) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {G : ℝ → ℂ} (hG : AEStronglyMeasurable G volume) (j : ℕ) :
    ∑' k : ℤ, eLpNorm G p (volume.restrict
        (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) ^ p.toReal ≤
      ((4 * N - 2 : ℕ) : ℝ≥0∞) * eLpNorm G p volume ^ p.toReal := by
  have hk : ∀ k : ℤ, eLpNorm G p (volume.restrict
      (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) ^ p.toReal =
      ∫⁻ x in Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j),
        ‖G x‖ₑ ^ p.toReal := fun k => eLpNorm_rpow_eq hG.restrict hp0 hp
  rw [tsum_congr hk, eLpNorm_rpow_eq hG hp0 hp]
  exact tsum_setLIntegral_le_mul_lintegral (fun k => measurableSet_Icc)
    (fun x T hT => card_le_of_forall_mem_window hN x T hT) (hG.eNorm.pow_const _)

/-- **The length of a window**: `|W_k|^N = (4N - 3)^N 2^(-jN)` for the window
`W_k = [(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]` of length `(4N - 3)/2^j`, `N ≥ 1`. -/
theorem ofReal_window_length_pow (hN : 1 ≤ N) (j : ℕ) (k : ℤ) :
    ENNReal.ofReal (((k : ℝ) + (2 * N - 1)) / 2 ^ j - ((k : ℝ) - (2 * N - 2)) / 2 ^ j) ^ N =
      ((4 * N - 3 : ℕ) : ℝ≥0∞) ^ N * (2 ^ (j * N))⁻¹ := by
  have h : ((k : ℝ) + (2 * N - 1)) / 2 ^ j - ((k : ℝ) - (2 * N - 2)) / 2 ^ j =
      ((4 * N - 3 : ℕ) : ℝ) * ((2 : ℝ) ^ j)⁻¹ := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    field_simp
    ring
  rw [h, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat, mul_pow, ← ENNReal.inv_pow, ← pow_mul]

/-! ### Jackson's inequality for smooth functions -/

/-- **Subtracting a reproduced polynomial**: for `N ≥ 2`, a locally integrable `S : ℝ → ℂ`, a
complex polynomial `Q` of degree `< N` and every level `j`,
`S - P_j S = (S - Q) - P_j (S - Q)` at every point, since `P_j` is linear on locally integrable
functions (`Daubechies.projFun_sub`) and reproduces `Q` (`Daubechies.projFun_poly`). -/
theorem sub_projFun_eq_sub_projFun_sub (hN : 2 ≤ N) {S : ℝ → ℂ}
    (hS : LocallyIntegrable S volume) {Q : Polynomial ℂ} (hQ : Q ∈ Polynomial.degreeLT ℂ N)
    (j : ℕ) :
    (fun x => S x - projFun m j S x) = fun x =>
      (S x - Q.eval (x : ℂ)) - projFun m j (fun y => S y - Q.eval (y : ℂ)) x := by
  have hQc : Continuous fun y : ℝ => Q.eval (y : ℂ) := Interval.continuous_polyFun Q
  rw [projFun_sub m hN hS hQc.locallyIntegrable j, projFun_poly m hN hQ j]
  funext x
  ring

/-- **The error on a cell through a polynomial**: let `N ≥ 2`, `1 ≤ p ≤ ∞`, let `S : ℝ → ℂ` be
locally integrable and `Q` a complex polynomial of degree `< N`. Then on the dyadic cell
`I = [k/2^j, (k + 1)/2^j)` with the window `W = [(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]`,
`‖S - P_j S‖_{L_p(I)} ≤ (1 + C) ‖S - Q‖_{L_p(W)}` with the constant `C = cellConst m p` of the
local bound. Indeed `S - P_j S = (S - Q) - P_j (S - Q)`
(`Daubechies.sub_projFun_eq_sub_projFun_sub`), `I ⊆ W` (`Daubechies.Ico_subset_window`), and
`‖P_j (S - Q)‖_{L_p(I)} ≤ C ‖S - Q‖_{L_p(W)}` (`Daubechies.eLpNorm_projFun_cell_le`). -/
theorem eLpNorm_sub_projFun_cell_le_of_poly (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    {S : ℝ → ℂ} (hS : LocallyIntegrable S volume) {Q : Polynomial ℂ}
    (hQ : Q ∈ Polynomial.degreeLT ℂ N) (j : ℕ) (k : ℤ) :
    eLpNorm (fun x => S x - projFun m j S x) p
        (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j))) ≤
      (1 + cellConst m p) * eLpNorm (fun x => S x - Q.eval (x : ℂ)) p (volume.restrict
        (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) := by
  have hR : AEStronglyMeasurable (fun x : ℝ => S x - Q.eval (x : ℂ)) volume :=
    hS.aestronglyMeasurable.sub (Interval.continuous_polyFun Q).aestronglyMeasurable
  rw [sub_projFun_eq_sub_projFun_sub m hN hS hQ j]
  calc eLpNorm (fun x => (S x - Q.eval (x : ℂ)) - projFun m j (fun y => S y - Q.eval (y : ℂ)) x)
        p (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j)))
      ≤ eLpNorm (fun x => S x - Q.eval (x : ℂ)) p
          (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j))) +
        eLpNorm (projFun m j (fun y => S y - Q.eval (y : ℂ))) p
          (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j))) :=
        eLpNorm_sub_le hp1
    _ ≤ eLpNorm (fun x => S x - Q.eval (x : ℂ)) p (volume.restrict
          (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) +
        cellConst m p * eLpNorm (fun x => S x - Q.eval (x : ℂ)) p (volume.restrict
          (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) :=
        add_le_add (eLpNorm_mono_measure _
          (Measure.restrict_mono (Ico_subset_window (by omega) j k) le_rfl))
          (eLpNorm_projFun_cell_le m hN hp1 hR j k)
    _ = _ := by ring

/-- **The error on a cell for a smooth function**: let `N ≥ 2`, `1 ≤ p ≤ ∞` and `S ∈ C^N(ℝ)`.
Then on the dyadic cell `I = [k/2^j, (k + 1)/2^j)` with the window
`W = [(k - (2N - 2))/2^j, (k + 2N - 1)/2^j]`,
`‖S - P_j S‖_{L_p(I)} ≤ (1 + C) (4N - 3)^N 2^(-jN) ‖S^(N)‖_{L_p(W)}` with `C = cellConst m p`.
Taylor's theorem on `W` gives a polynomial `Q` of degree `< N` with
`‖S - Q‖_{L_p(W)} ≤ |W|^N ‖S^(N)‖_{L_p(W)}` (`Interval.exists_eLpNorm_sub_polyFun_le`), and
`|W| = (4N - 3)/2^j` (`Daubechies.ofReal_window_length_pow`); then
`Daubechies.eLpNorm_sub_projFun_cell_le_of_poly` applies. -/
theorem eLpNorm_sub_projFun_cell_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) {S : ℝ → ℂ}
    (hS : ContDiff ℝ N S) (j : ℕ) (k : ℤ) :
    eLpNorm (fun x => S x - projFun m j S x) p
        (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j))) ≤
      (1 + cellConst m p) * (((4 * N - 3 : ℕ) : ℝ≥0∞) ^ N * (2 ^ (j * N))⁻¹) *
        eLpNorm (iteratedDeriv N S) p (volume.restrict
          (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have huv : ((k : ℝ) - (2 * N - 2)) / 2 ^ j ≤ ((k : ℝ) + (2 * N - 1)) / 2 ^ j := by
    gcongr
    linarith
  obtain ⟨Q, hQ, hT⟩ := Interval.exists_eLpNorm_sub_polyFun_le hp1 N hS huv
  rw [ofReal_window_length_pow (by omega) j k] at hT
  calc eLpNorm (fun x => S x - projFun m j S x) p
        (volume.restrict (Set.Ico ((k : ℝ) / 2 ^ j) ((k + 1) / 2 ^ j)))
      ≤ (1 + cellConst m p) * eLpNorm (fun x => S x - Q.eval (x : ℂ)) p (volume.restrict
          (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j))) :=
        eLpNorm_sub_projFun_cell_le_of_poly m hN hp1 hS.continuous.locallyIntegrable hQ j k
    _ ≤ (1 + cellConst m p) * (((4 * N - 3 : ℕ) : ℝ≥0∞) ^ N * (2 ^ (j * N))⁻¹ *
          eLpNorm (iteratedDeriv N S) p (volume.restrict
            (Set.Icc (((k : ℝ) - (2 * N - 2)) / 2 ^ j) ((k + (2 * N - 1)) / 2 ^ j)))) := by
        gcongr
        exact hT
    _ = _ := by ring

/-- **The constant of Jackson's inequality for smooth functions**:
`(4N - 2)^(1/p) (1 + C) (4N - 3)^N` with the constant `C = cellConst m p` of the local bound, the
overlap number `4N - 2` of the windows and their length `(4N - 3)/2^j`
(`Daubechies.eLpNorm_sub_projFun_le_of_contDiff`). -/
noncomputable def smoothJacksonConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  ((4 * N - 2 : ℕ) : ℝ≥0∞) ^ (1 / p.toReal) * (1 + cellConst m p) *
    ((4 * N - 3 : ℕ) : ℝ≥0∞) ^ N

/-- The constant `smoothJacksonConst m p` is finite for `N ≥ 2` (`Daubechies.cellConst_ne_top`).
-/
theorem smoothJacksonConst_ne_top (hN : 2 ≤ N) (p : ℝ≥0∞) : smoothJacksonConst m p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.natCast_ne_top _))
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, cellConst_ne_top m hN p⟩))
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- **Jackson's inequality for smooth functions**: for `N ≥ 2`, `1 ≤ p < ∞`, `S ∈ C^N(ℝ)` and
every level `j`, `‖S - P_j S‖_p ≤ C_S 2^(-jN) ‖S^(N)‖_p` with `C_S = smoothJacksonConst m p`.
The cell bound `Daubechies.eLpNorm_sub_projFun_cell_le` holds on every dyadic cell of level `j`,
the cells cover `ℝ` (`Daubechies.iUnion_Ico_div_two_pow`), and the windows satisfy the window
summation `Daubechies.tsum_eLpNorm_window_rpow_le`, so the summation lemma
`MeasureTheory.eLpNorm_le_of_forall_eLpNorm_restrict_le` applies. The inequality holds in
`[0, ∞]` for every `S ∈ C^N(ℝ)`. -/
theorem eLpNorm_sub_projFun_le_of_contDiff (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {S : ℝ → ℂ} (hS : ContDiff ℝ N S) (j : ℕ) :
    eLpNorm (fun x => S x - projFun m j S x) p volume ≤
      smoothJacksonConst m p * (2 ^ (j * N))⁻¹ * eLpNorm (iteratedDeriv N S) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have h := eLpNorm_le_of_forall_eLpNorm_restrict_le (μ := volume) (iUnion_Ico_div_two_pow j)
    hp0 hp (hS.continuous.sub (continuous_projFun m hN j S)).aestronglyMeasurable
    (tsum_eLpNorm_window_rpow_le (by omega) hp0 hp
      (hS.continuous_iteratedDeriv' N).aestronglyMeasurable j)
    (fun k => eLpNorm_sub_projFun_cell_le m hN hp1 hS j k)
  refine h.trans (le_of_eq ?_)
  rw [smoothJacksonConst]
  ring

/-! ### Jackson's inequality for continuous functions -/

/-- **Comparing the errors of two functions**: for `N ≥ 2`, `1 ≤ p < ∞`, locally integrable
`f, S : ℝ → ℂ` and every level `j`,
`‖f - P_j f‖_p ≤ (1 + C) ‖f - S‖_p + ‖S - P_j S‖_p` with the uniform bound `C = projConst m p` of
the projections. Indeed `f - P_j f = (f - S) + (S - P_j S) + P_j (S - f)` by the linearity of
`P_j` (`Daubechies.projFun_sub`), and `‖P_j (S - f)‖_p ≤ C ‖S - f‖_p`
(`Daubechies.eLpNorm_projFun_le`). -/
theorem eLpNorm_sub_projFun_le_add (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f S : ℝ → ℂ} (hf : LocallyIntegrable f volume) (hS : LocallyIntegrable S volume) (j : ℕ) :
    eLpNorm (fun x => f x - projFun m j f x) p volume ≤
      (1 + ENNReal.ofReal (projConst m p)) * eLpNorm (fun x => f x - S x) p volume +
        eLpNorm (fun x => S x - projFun m j S x) p volume := by
  have heq : (fun x => f x - projFun m j f x) = (fun x => f x - S x) +
      (fun x => S x - projFun m j S x) + projFun m j (fun y => S y - f y) := by
    rw [projFun_sub m hN hS hf j]
    funext x
    simp only [Pi.add_apply]
    ring
  have hP : eLpNorm (projFun m j (fun y => S y - f y)) p volume ≤
      ENNReal.ofReal (projConst m p) * eLpNorm (fun x => f x - S x) p volume := by
    refine (eLpNorm_projFun_le m hN hp1 hp
      (hS.aestronglyMeasurable.sub hf.aestronglyMeasurable) j).trans (le_of_eq ?_)
    rw [← eLpNorm_neg]
    congr 2
    funext x
    simp
  rw [heq]
  calc eLpNorm ((fun x => f x - S x) + (fun x => S x - projFun m j S x) +
        projFun m j (fun y => S y - f y)) p volume
      ≤ eLpNorm (fun x => f x - S x) p volume +
          eLpNorm (fun x => S x - projFun m j S x) p volume +
        eLpNorm (projFun m j (fun y => S y - f y)) p volume :=
        (eLpNorm_add_le hp1).trans (add_le_add_left (eLpNorm_add_le hp1) _)
    _ ≤ eLpNorm (fun x => f x - S x) p volume +
          eLpNorm (fun x => S x - projFun m j S x) p volume +
        ENNReal.ofReal (projConst m p) * eLpNorm (fun x => f x - S x) p volume := by gcongr
    _ = _ := by ring

/-- **The constant of Jackson's inequality**: `C_J = 1 + C + C_S 2^N N^N` with the uniform bound
`C = projConst m p` of the projections and the constant `C_S = smoothJacksonConst m p` for smooth
functions (`Daubechies.eLpNorm_sub_projFun_le_modulus`). It depends only on the mask and on
`p`. -/
noncomputable def jacksonConst (p : ℝ≥0∞) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (projConst m p) + smoothJacksonConst m p * (2 ^ N * (N : ℝ≥0∞) ^ N)

/-- The constant `jacksonConst m p` is finite for `N ≥ 2`
(`Daubechies.smoothJacksonConst_ne_top`). -/
theorem jacksonConst_ne_top (hN : 2 ≤ N) (p : ℝ≥0∞) : jacksonConst m p ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩,
    ENNReal.mul_ne_top (smoothJacksonConst_ne_top m hN p)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top N)))⟩

/-- **Jackson's inequality for continuous functions**: for `N ≥ 2`, `1 ≤ p < ∞`, every continuous
`f : ℝ → ℂ` and every level `j`,
`‖f - P_j f‖_p ≤ C_J ω_N(f, 2^(-j))_p` with `C_J = jacksonConst m p` and the modulus of
smoothness `ω_N(f, t)_p = sup_{|h| ≤ t} ‖Δ_h^N f‖_{L_p(ℝ)}` (`Rd.modulus volume`). With the
Steklov smoothing `S = S_δ f` at the step `δ = 1/(N 2^j)`, which lies in `C^N`
(`Interval.contDiff_smooth`): `‖f - S‖_p ≤ ω_N(f, 2^(-j))_p`
(`Daubechies.eLpNorm_sub_smooth_le_dyadic`), `‖S^(N)‖_p ≤ 2^N N^N 2^(jN) ω_N(f, 2^(-j))_p`
(`Daubechies.eLpNorm_iteratedDeriv_smooth_le_dyadic`), hence
`‖S - P_j S‖_p ≤ C_S 2^N N^N ω_N(f, 2^(-j))_p` (`Daubechies.eLpNorm_sub_projFun_le_of_contDiff`),
and `Daubechies.eLpNorm_sub_projFun_le_add` combines the two bounds. The inequality holds in
`[0, ∞]` for every continuous `f`. -/
theorem eLpNorm_sub_projFun_le_modulus (hN : 2 ≤ N) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞)
    {f : ℝ → ℂ} (hf : Continuous f) (j : ℕ) :
    eLpNorm (fun x => f x - projFun m j f x) p volume ≤
      jacksonConst m p * Rd.modulus volume N p f (1 / 2 ^ j) := by
  have hS := Interval.contDiff_smooth hf N (1 / (N * 2 ^ j))
  have h0 : (2 : ℝ≥0∞) ^ (j * N) ≠ 0 := pow_ne_zero _ two_ne_zero
  have htop : (2 : ℝ≥0∞) ^ (j * N) ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc eLpNorm (fun x => f x - projFun m j f x) p volume
      ≤ (1 + ENNReal.ofReal (projConst m p)) *
          eLpNorm (fun x => f x - Interval.smooth N (1 / (N * 2 ^ j)) f x) p volume +
        eLpNorm (fun x => Interval.smooth N (1 / (N * 2 ^ j)) f x -
          projFun m j (Interval.smooth N (1 / (N * 2 ^ j)) f) x) p volume :=
        eLpNorm_sub_projFun_le_add m hN hp1 hp hf.locallyIntegrable
          hS.continuous.locallyIntegrable j
    _ ≤ (1 + ENNReal.ofReal (projConst m p)) * Rd.modulus volume N p f (1 / 2 ^ j) +
        smoothJacksonConst m p * (2 ^ (j * N))⁻¹ *
          (2 ^ N * (N : ℝ≥0∞) ^ N * 2 ^ (j * N) * Rd.modulus volume N p f (1 / 2 ^ j)) := by
        gcongr
        · exact eLpNorm_sub_smooth_le_dyadic hf (by omega) j hp1 hp
        · exact (eLpNorm_sub_projFun_le_of_contDiff m hN hp1 hp hS j).trans (by
            gcongr
            exact eLpNorm_iteratedDeriv_smooth_le_dyadic hf (by omega) j hp1)
    _ = (1 + ENNReal.ofReal (projConst m p)) * Rd.modulus volume N p f (1 / 2 ^ j) +
        smoothJacksonConst m p * (2 ^ N * (N : ℝ≥0∞) ^ N) *
          Rd.modulus volume N p f (1 / 2 ^ j) * ((2 ^ (j * N))⁻¹ * 2 ^ (j * N)) := by ring
    _ = jacksonConst m p * Rd.modulus volume N p f (1 / 2 ^ j) := by
        rw [ENNReal.inv_mul_cancel h0 htop, mul_one, jacksonConst]
        ring

/-! ### Jackson's inequality on `L_p` -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Jackson's inequality for a continuous representative**: for `N ≥ 2`, `1 ≤ p < ∞`, every
`f ∈ L_p(ℝ)` that agrees almost everywhere with a continuous function `g`, and every level `j`,
`‖f - P_j f‖_p ≤ C_J ω_N(f, 2^(-j))_p` with `C_J = jacksonConst m p`
(`Daubechies.eLpNorm_sub_projFun_le_modulus` for `g`; both sides depend only on the class of
`f`, `Daubechies.projFun_congr_ae` and `Rd.modulus_congr_ae`). -/
theorem enorm_sub_proj_le_of_continuous (hN : 2 ≤ N) (hp : p ≠ ∞)
    {f : Lp ℂ p (volume : Measure ℝ)} {g : ℝ → ℂ} (hg : Continuous g) (hfg : ⇑f =ᵐ[volume] g)
    (j : ℕ) : ‖f - proj m p hN hp j f‖ₑ ≤ jacksonConst m p * Rd.lpModulus p N f j := by
  have hP : ⇑(proj m p hN hp j f) =ᵐ[volume] projFun m j g :=
    (proj_apply_ae m hN hp j f).trans (EventuallyEq.of_eq (projFun_congr_ae m hfg j))
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (hfg.sub hP)), Rd.lpModulus,
    Rd.modulus_congr_ae hfg]
  exact eLpNorm_sub_projFun_le_modulus m hN Fact.out hp hg j

/-- **Jackson's inequality for the Daubechies scheme, with its constant**: for `N ≥ 2`,
`1 ≤ p < ∞`, every `f ∈ L_p(ℝ)` and every level `j`, the error of best approximation from the
scaling space `V_j` (the approximants of complexity `2^j`, `Daubechies.mem_scheme_two_pow`)
satisfies `E_{2^j}(f)_p ≤ C_J ω_N(f, 2^(-j))_p` with `C_J = jacksonConst m p`. For `f` with a
bounded continuous representative, `P_j f ∈ V_j` gives `E_{2^j}(f)_p ≤ ‖f - P_j f‖_p`
(`Daubechies.enorm_sub_proj_le_of_continuous`); these `f` are dense in `L_p` (Mathlib's
`MeasureTheory.Lp.boundedContinuousFunction_dense`), and both sides are controlled by `‖f‖_p`
(`Rd.lpModulus_add_le`, `Rd.lpModulus_le`), so the bound extends to all of `L_p`
(`ApproximationScheme.approxError_le_of_dense`). -/
theorem approxError_scheme_le_jacksonConst_mul (hN : 2 ≤ N) (hp : p ≠ ∞)
    (f : Lp ℂ p (volume : Measure ℝ)) (j : ℕ) :
    (scheme m p hN hp).approxError f (2 ^ j) ≤ jacksonConst m p * Rd.lpModulus p N f j := by
  refine ApproximationScheme.approxError_le_of_dense
    (Lp.boundedContinuousFunction_dense ℂ volume hp) (fun f g => Rd.lpModulus_add_le N f g j)
    (C0 := 2 ^ N) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (fun f => Rd.lpModulus_le N f j)
    (jacksonConst_ne_top m hN p) (fun g hg => ?_) f
  obtain ⟨g₀, hg₀⟩ := Lp.mem_boundedContinuousFunction_iff.1 hg
  have hae : ⇑g =ᵐ[volume] g₀ := by
    have h := g₀.toContinuousMap.coeFn_toAEEqFun volume
    rw [hg₀] at h
    exact h
  exact ((scheme m p hN hp).approxError_le_of_mem
    ((mem_scheme_two_pow m).2 (proj_mem_scalingSpace m hN hp j g)) g).trans
    (enorm_sub_proj_le_of_continuous m hN hp g₀.continuous hae j)

/-- **Jackson's inequality for the Daubechies scheme**: for `N ≥ 2` and `1 ≤ p < ∞` there is a
constant `C_J < ∞` such that for every `f ∈ L_p(ℝ)` and every level `j` the error of best
approximation from the scaling space `V_j` satisfies `E_{2^j}(f)_p ≤ C_J ω_N(f, 2^(-j))_p`, the
Jackson inequality of an approximation scheme with modulus `ω_N` at the dyadic scales. The
constant `C_J = jacksonConst m p` serves (`Daubechies.approxError_scheme_le_jacksonConst_mul`). -/
theorem approxError_scheme_le (hN : 2 ≤ N) (hp : p ≠ ∞) :
    ∃ C_J : ℝ≥0∞, C_J ≠ ∞ ∧ ∀ (f : Lp ℂ p (volume : Measure ℝ)) (j : ℕ),
      (scheme m p hN hp).approxError f (2 ^ j) ≤ C_J * Rd.lpModulus p N f j :=
  ⟨jacksonConst m p, jacksonConst_ne_top m hN p, approxError_scheme_le_jacksonConst_mul m hN hp⟩

/-- **Jackson's inequality for the projections**: for `N ≥ 2`, `1 ≤ p < ∞`, every `f ∈ L_p(ℝ)` and
every level `j`, `‖f - P_j f‖_p ≤ (1 + C) C_J ω_N(f, 2^(-j))_p` with the uniform bound
`C = projConst m p` of the projections and `C_J = jacksonConst m p`. This is the Lebesgue
inequality `‖f - P_j f‖_p ≤ (1 + C) E_{2^j}(f)_p`
(`ApproximationScheme.ProjectionScheme.enorm_sub_le_approxError` for the projection scheme
`Daubechies.projectionScheme`, whose projection of complexity `2^j` is `P_j`,
`Daubechies.projectionScheme_two_pow`) combined with
`Daubechies.approxError_scheme_le_jacksonConst_mul`. -/
theorem enorm_sub_proj_le (hN : 2 ≤ N) (hp : p ≠ ∞) (f : Lp ℂ p (volume : Measure ℝ)) (j : ℕ) :
    ‖f - proj m p hN hp j f‖ₑ ≤
      (1 + ENNReal.ofReal (projConst m p)) * jacksonConst m p * Rd.lpModulus p N f j := by
  have h := (projectionScheme m p hN hp).enorm_sub_le_approxError (2 ^ j) f
  rw [projectionScheme_two_pow] at h
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_right (approxError_scheme_le_jacksonConst_mul m hN hp f j) _

end Lp

end Daubechies
