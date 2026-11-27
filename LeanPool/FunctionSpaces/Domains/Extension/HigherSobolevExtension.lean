/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Extension.SobolevExtension
public import LeanPool.FunctionSpaces.Domains.Extension.HigherDivergenceKernels
public import LeanPool.FunctionSpaces.Rd.Sobolev.WeakDerivativeLeibniz

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The extension theorem for Sobolev spaces of higher order

Let `Ω` be a bounded Lipschitz domain in a finite-dimensional real inner product space `V` of
dimension `n`, `1 < p < ∞` and `m ∈ ℕ`. Every `f ∈ W^m_p(Ω)` agrees on `Ω` with some
`F ∈ W^m_p(V)` (`Rd.BoundedLipschitzDomain.memWeakSobolev_iff_exists_memSobolev_order`), for
`n ≥ 1` with `‖F‖_{W^m_p(V)} ≤ C ‖f‖_{W^m_p(Ω)}`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder`). A word `w : Fin k → Fin n` stands for
the derivative `∂^{e_w} = ∂_{e_{w_0}} ⋯ ∂_{e_{w_{k-1}}}` along the orthonormal basis
`e_i = Rd.gridBasis V i`, and `‖f‖_{W^m_p(O)} = ∑_{k ≤ m} ∑_w ‖∂^{e_w} f‖_{L_p(O)}`.

* **Local means by the derivatives of order `m`**: for the smoothed bump `b'` of a bump `b` and
  `m ≤ L`, the local means kernels of order `L` are `k_{j+1} = 2^{-jm} ∑_i ∂^{e_i} (K_i)_{2^j}`
  with the higher divergence kernels `K_i` of `b`, so
  `(k_{j+1} ⋆ 1_T f)(x) = 2^{-jm} ∑_i ((K_i)_{2^j} ⋆ 1_T ∂^{e_i} f)(x)`
  (`Rd.LocalMeansBump.conv_kernel_succ_eq_sum_higherKernel`, by the general identity for kernels
  that are sums of derivatives, `Rd.conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp`).
  For `m < L` the strong type of the Calderón–Zygmund families `((K_i)_{2^j})_j` bounds the
  local means quasi-norm of Triebel–Lizorkin type with smoothness `m` on a set by
  `‖f‖_{L_p(T)} + ∑_i ‖∂^{e_i} f‖_{L_p(T)}`
  (`Rd.LocalMeansBump.tlLocalNormOn_le_higherPatchConst`).
* **One patch** (`Rd.LocalMeansBump.extendsSobolevOrder`): for `m ≥ 1` the local extension of
  order `L = m + 1` lies in `F^m_{p,2}(V) = W^m_p(V)` and agrees with `f` on the patch;
  `Rd.ExtendsSobolevOrder p m O U C` says that such extensions from `U` exist with the constant
  `C`.
* **Pasting** (`Rd.extendsSobolevOrder_of_cover`): a smooth resolution of unity pastes the local
  extensions in `W^m_p(V)`, by the Leibniz rule
  (`Rd.exists_hasWeakLineDeriv_mul_of_tsupport_subset`).
* **Bounded Lipschitz domains**: the boundary patches extend by the local extension of the smoothed
  cone bump (`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder_boundary`), the inner patch by a
  cutoff (`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder_interior`, for every `1 ≤ p ≤ ∞`),
  and `W^0_p = L_p` by zero (`Rd.extendsSobolevOrder_zero`).
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Local means by the derivatives of order `m` -/

namespace LocalMeansBump

variable (b : LocalMeansBump V) {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Local means of order `L` by the derivatives of order `m ≤ L`, at one point**: let
`g_i = ∂^{e_i} f` weakly on an open set `T` for every word `i` of length `m`, `f ∈ L_p(T)`, and let
`x - y ∈ T` for every `y` in the support of every `(K_i)_{2^j}`, with the higher divergence kernels
`K_i` of `b`. Then the local means kernels of the smoothed bump satisfy
`(k_{j+1} ⋆ 1_T f)(x) = 2^{-jm} ∑_i ((K_i)_{2^j} ⋆ 1_T g_i)(x)`
(`Rd.LocalMeansBump.kernel_succ_eq_sum_higherKernel`; each derivative moves to `f` by
`Rd.conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp`). -/
theorem conv_kernel_succ_eq_sum_higherKernel {L m : ℕ} (hmL : m ≤ L) {T : Opens V}
    {f : V → ℂ} {g : (Fin m → Fin (finrank ℝ V)) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun l => gridBasis V (i l)) f (g i)) (j : ℕ) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)), x - y ∈ T) :
    conv (b.dilationSmoothed.kernel L (j + 1)) ((T : Set V).indicator f) volume x =
      ((2 : ℂ) ^ (j * m))⁻¹ * ∑ i, conv (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ))
        ((T : Set V).indicator (g i)) volume x :=
  conv_indicator_eq_mul_sum_of_eq_sum_iteratedLineDerivOp hf hfg
    (b.hasCompactSupport_higherKernel L m) (by positivity) (b.kernel_succ_eq_sum_higherKernel hmL j)
    hx

/-- **One local mean by the derivatives of order `m`**: under the hypotheses of
`Rd.LocalMeansBump.conv_kernel_succ_eq_sum_higherKernel`,
`2^{(j+1)m} |(k_{j+1} ⋆ 1_T f)(x)| ≤ 2^m ∑_i |((K_i)_{2^j} ⋆ 1_T g_i)(x)|`. -/
theorem dyadicWeight_mul_enorm_conv_kernel_succ_le {L m : ℕ} (hmL : m ≤ L) {T : Opens V}
    {f : V → ℂ} {g : (Fin m → Fin (finrank ℝ V)) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun l => gridBasis V (i l)) f (g i)) (j : ℕ) {x : V}
    (hx : ∀ i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)), x - y ∈ T) :
    dyadicWeight (m : ℝ) (j + 1) *
        ‖conv (b.dilationSmoothed.kernel L (j + 1)) ((T : Set V).indicator f) volume x‖ₑ ≤
      2 ^ m * ∑ i, ‖conv (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ))
        ((T : Set V).indicator (g i)) volume x‖ₑ := by
  have hw : dyadicWeight (m : ℝ) (j + 1) * ‖((2 : ℂ) ^ (j * m))⁻¹‖ₑ = 2 ^ m := by
    have h2 : ‖(2 : ℂ)‖ₑ = 2 := by
      rw [← ofReal_norm, Complex.norm_two, ENNReal.ofReal_ofNat]
    rw [ENNReal.dyadicWeight_natCast, eNorm_inv (pow_ne_zero _ two_ne_zero), eNorm_pow, h2,
      add_mul, one_mul, pow_add, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel
        (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top), one_mul]
  rw [b.conv_kernel_succ_eq_sum_higherKernel hmL hf hfg j hx, eNorm_mul, ← mul_assoc, hw]
  gcongr
  exact eNorm_sum_le _ _

/-- **The local means of order `L` by the derivatives of order `m ≤ L`, pointwise**: let `m ≤ L`,
`f ∈ L_p(T)` on an open set `T` with weak derivatives `g_i = ∂^{e_i} f` on `T` for the words `i`
of length `m`, let `x - y ∈ T` for `x ∈ W`, every level `j` and every `y` in the support of
`(K_i)_{2^j}`, with the higher divergence kernels `K_i` of `b`, and let `F = 1_T f` in `L_p`.
Then almost everywhere, for the smoothed bump,
`‖(2^{jm} |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ≤ |1_W (k_0 ⋆ F)(x)| +
2^m ∑_i ‖(((K_i)_{2^j} ⋆ 1_T g_i)(x))_j‖_{ℓ_2}`
(`Rd.LocalMeansBump.ae_lqNorm_le_of_pointwise`). -/
theorem ae_lqNorm_le_of_hasWeakLineDeriv_words (hp : p ≠ ∞) {L m : ℕ} (hmL : m ≤ L) {W : Set V}
    (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ} {g : (Fin m → Fin (finrank ℝ V)) → V → ℂ}
    (hf : MemLp f p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun l => gridBasis V (i l)) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)),
      x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    ∀ᵐ x ∂volume, lqNorm 2 (fun j => dyadicWeight (m : ℝ) j *
        ‖(indicatorLp hW (b.dilationSmoothed.localMean hp L j F) : V → ℂ) x‖ₑ) ≤
      ‖(indicatorLp hW (b.dilationSmoothed.localMean hp L 0 F) : V → ℂ) x‖ₑ +
        2 ^ m * ∑ i, lqNorm 2 (fun j => ‖conv (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ))
          ((T : Set V).indicator (g i)) volume x‖ₑ) :=
  b.dilationSmoothed.ae_lqNorm_le_of_pointwise hp L m hW (b.higherKernel L m)
    (fun i => (T : Set V).indicator (g i)) (2 ^ m)
    (fun x hx j => b.dyadicWeight_mul_enorm_conv_kernel_succ_le hmL hf hfg j (hsupp x hx j)) hF

omit [Fact (1 ≤ p)] in
/-- The square functions of the higher divergence kernels: for `m < L` and `1 < p < ∞`,
`‖ x ↦ ‖(((K_i)_{2^j} ⋆ 1_T g)(x))_j‖_{ℓ_2} ‖_p ≤ C_p(K_i) ‖g‖_{L_p(T)}`
(`Rd.LocalMeansBump.isCZFamily_higherKernel`, `Rd.IsCZFamily.eLpNorm_lqNorm_conv_le`). -/
theorem eLpNorm_lqNorm_conv_higherKernel_le [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {L m : ℕ}
    (hmL : m < L) {T : Opens V} {g : V → ℂ} (hg : MemLp g p (volume.restrict T))
    (i : Fin m → Fin (finrank ℝ V)) :
    eLpNorm (fun x => lqNorm 2 (fun j => ‖conv (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ))
        ((T : Set V).indicator g) volume x‖ₑ)) p volume ≤
      czConst V p (meanZeroOverlap (b.higherKernel L m i))
        (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.higherKernel L m i)) *
        eLpNorm g p (volume.restrict T) := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict T.isOpen.measurableSet.nullMeasurableSet]
  exact (b.isCZFamily_higherKernel hmL i).eLpNorm_lqNorm_conv_le hp1 hp
    ((memLp_indicator_iff_restrict T.isOpen.measurableSet.nullMeasurableSet).2 hg)

/-- The constant `∑_i C_p(K_i)` of the bound of the local means by the derivatives of order `m`,
with the constants `C_p(K_i) = Rd.czConst V p B_i H_i` of the Calderón–Zygmund families of the
higher divergence kernels (`Rd.LocalMeansBump.isCZFamily_higherKernel`). -/
noncomputable def higherGradientConst (L m : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : Fin m → Fin (finrank ℝ V), czConst V p (meanZeroOverlap (b.higherKernel L m i))
    (4 * familyHormanderConst V fun k l => SchwartzMap.seminorm ℝ k l (b.higherKernel L m i))

omit [Fact (1 ≤ p)] in
/-- The constant of the bound by the derivatives of order `m` is finite for `1 < p < ∞`. -/
theorem higherGradientConst_ne_top (L m : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞) :
    b.higherGradientConst L m p ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ => czConst_ne_top hp1 hp (meanZeroOverlap_ne_top _)
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (familyHormanderConst_ne_top _))

/-- **The local means of Triebel–Lizorkin type by the derivatives of order `m`**: let
`g_i = ∂^{e_i} f` weakly on an open set `T` for the words `i` of length `m < L`, with
`f, g_i ∈ L_p(T)` and `1 < p < ∞`, let `x - y ∈ T` for every `x ∈ W`, every level `j` and every `y`
in the support of `(K_i)_{2^j}`, and let `F = 1_T f` in `L_p`. Then, for the smoothed bump `b'`,
`‖ x ↦ ‖(2^{jm} |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ ‖m_L‖_1 ‖f‖_{L_p(T)} +
2^m ∑_i C_p(K_i) ‖g_i‖_{L_p(T)}`, with the moment kernel `m_L` of `b'`
(`Rd.LocalMeansBump.tlLocalNormOn_le_of_pointwise`). -/
theorem tlLocalNormOn_le_of_hasWeakLineDeriv_words [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {L m : ℕ} (hmL : m < L) {W : Set V} (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ}
    {g : (Fin m → Fin (finrank ℝ V)) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hg : ∀ i, MemLp (g i) p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun l => gridBasis V (i l)) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)),
      x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    b.dilationSmoothed.tlLocalNormOn hp hW L m 2 F ≤
      eLpNorm (momentKernel b.dilationSmoothed.toFun L) 1 volume *
        eLpNorm f p (volume.restrict T) +
        2 ^ m * ∑ i, czConst V p (meanZeroOverlap (b.higherKernel L m i))
          (4 * familyHormanderConst V fun k l =>
            SchwartzMap.seminorm ℝ k l (b.higherKernel L m i)) *
          eLpNorm (g i) p (volume.restrict T) := by
  have hT := T.isOpen.measurableSet
  have hFn : ‖F‖ₑ = eLpNorm f p (volume.restrict T) := by
    rw [Lp.eNorm_def, eLpNorm_congr_ae hF,
      eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet]
  refine (b.dilationSmoothed.tlLocalNormOn_le_of_pointwise hp L m hW (b.higherKernel L m)
    (fun i => (T : Set V).indicator (g i))
    (fun i => ((memLp_indicator_iff_restrict hT.nullMeasurableSet).2 (hg i)).aestronglyMeasurable)
      (2 ^ m)
    (fun x hx j => b.dyadicWeight_mul_enorm_conv_kernel_succ_le hmL.le hf hfg j (hsupp x hx j))
    hF).trans ?_
  rw [hFn]
  gcongr with i
  exact b.eLpNorm_lqNorm_conv_higherKernel_le hp1 hp hmL (hg i) i

/-- The constant `‖m_L‖_1 + 2^m ∑_i C_p(K_i)` of the local means of the smoothed bump by the
derivatives of order `m`, with the moment kernel `m_L` of order `L` of the smoothed bump and
`∑_i C_p(K_i) = Rd.LocalMeansBump.higherGradientConst b L m p`. -/
noncomputable def higherPatchConst (L m : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (momentKernel b.dilationSmoothed.toFun L) 1 volume + 2 ^ m * b.higherGradientConst L m p

omit [Fact (1 ≤ p)] in
/-- The constant of the local means by the derivatives of order `m` is finite for `1 < p < ∞`. -/
theorem higherPatchConst_ne_top (L m : ℕ) (hp1 : 1 < p) (hp : p ≠ ∞) :
    b.higherPatchConst L m p ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨eLpNorm_momentKernel_ne_top b.dilationSmoothed.integrable L,
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (b.higherGradientConst_ne_top L m hp1 hp)⟩

/-- **The local means of Triebel–Lizorkin type by the derivatives of order `m`, with one
constant**: under the hypotheses of `Rd.LocalMeansBump.tlLocalNormOn_le_of_hasWeakLineDeriv_words`,
`‖ x ↦ ‖(2^{jm} |1_W (k_j ⋆ F)(x)|)_j‖_{ℓ_2} ‖_p ≤ C (‖f‖_{L_p(T)} + ∑_i ‖g_i‖_{L_p(T)})` with
`C = Rd.LocalMeansBump.higherPatchConst b L m p`. -/
theorem tlLocalNormOn_le_higherPatchConst [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {L m : ℕ}
    (hmL : m < L) {W : Set V} (hW : MeasurableSet W) {T : Opens V} {f : V → ℂ}
    {g : (Fin m → Fin (finrank ℝ V)) → V → ℂ} (hf : MemLp f p (volume.restrict T))
    (hg : ∀ i, MemLp (g i) p (volume.restrict T))
    (hfg : ∀ i, HasWeakLineDeriv T (fun l => gridBasis V (i l)) f (g i))
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)),
      x - y ∈ T)
    {F : Lp ℂ p (volume : Measure V)} (hF : (F : V → ℂ) =ᵐ[volume] (T : Set V).indicator f) :
    b.dilationSmoothed.tlLocalNormOn hp hW L m 2 F ≤ b.higherPatchConst L m p *
      (eLpNorm f p (volume.restrict T) + ∑ i, eLpNorm (g i) p (volume.restrict T)) := by
  refine (b.tlLocalNormOn_le_of_hasWeakLineDeriv_words hp1 hp hmL hW hf hg hfg hsupp hF).trans ?_
  rw [higherPatchConst, add_mul, mul_assoc (2 ^ m), higherGradientConst]
  refine add_le_add (mul_le_mul_right le_self_add _) (mul_le_mul_right ?_ _)
  exact (ENNReal.sum_mul_le_sum_mul_sum _ _ _).trans (mul_le_mul_right le_add_self _)

end LocalMeansBump

/-! ### Bounded extensions of order `m` from a set -/

variable {p : ℝ≥0∞}

variable (p) in
/-- **Sobolev functions of order `m` on `O` extend from `U` with constant `C`**: for every `f` with
weak derivatives `g_{k,w} = ∂^{e_w} f ∈ L_p(O)` on `O` along all words `w` of length `k ≤ m` there
are `F ∈ W^m_p(V)` with `F = f` almost everywhere on `U` and weak derivatives
`G_{k,w} = ∂^{e_w} F ∈ L_p(V)` on `V` with
`∑_{k ≤ m} ∑_w ‖G_{k,w}‖_p ≤ C ∑_{k ≤ m} ∑_w ‖g_{k,w}‖_{L_p(O)}`. The words of length `0` give
`g_{0,∅} = f` on `O` and `G_{0,∅} = F`, so both sides are the norms of `W^m_p`. For `m = 1` this is
the content of `Rd.ExtendsSobolev`. -/
def ExtendsSobolevOrder (m : ℕ) (O : Opens V) (U : Set V) (C : ℝ≥0∞) : Prop :=
  ∀ (f : V → ℂ) (g : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ),
    (∀ k ≤ m, ∀ w, MemLp (g k w) p (volume.restrict O)) →
    (∀ k ≤ m, ∀ w, HasWeakLineDeriv O (fun l => gridBasis V (w l)) f (g k w)) →
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev m F ∧ (∀ᵐ x ∂volume, x ∈ U → F x = f x) ∧
      ∃ G : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V),
        (∀ k ≤ m, ∀ w, HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) F (G k w)) ∧
        ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V), ‖G k w‖ₑ ≤
          C * ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
            eLpNorm (g k w) p (volume.restrict O)

/-- **Larger domains**: an extension of order `m` from `U` for Sobolev functions on `T` serves for
Sobolev functions on every open `O ⊇ T`, with the same constant, since
`‖h‖_{L_p(T)} ≤ ‖h‖_{L_p(O)}` and weak derivatives restrict to `T` (`Rd.HasWeakLineDeriv.mono`). -/
theorem ExtendsSobolevOrder.of_le {m : ℕ} {T O : Opens V} {U : Set V} {C : ℝ≥0∞}
    (h : ExtendsSobolevOrder p m T U C) (hTO : T ≤ O) : ExtendsSobolevOrder p m O U C := by
  intro f g hg hfg
  have hμ : volume.restrict (T : Set V) ≤ volume.restrict O :=
    Measure.restrict_mono (show (T : Set V) ⊆ O from hTO) le_rfl
  obtain ⟨F, hF, hFf, G, hG, hb⟩ := h f g (fun k hk w => (hg k hk w).mono_measure hμ)
    fun k hk w => (hfg k hk w).mono hTO
  refine ⟨F, hF, hFf, G, hG, hb.trans ?_⟩
  gcongr

/-- **Extensions of order `m` from `L_p` bounds**: Sobolev functions of order `m` on `O` extend from
`U` with constant `C` (`Rd.ExtendsSobolevOrder`) as soon as every such `f` agrees almost everywhere
on `U` with a function `F` on `V` with weak derivatives `G_{k,w} = ∂^{e_w} F` on `V`, `k ≤ m`, and
`∑_{k ≤ m} ∑_w ‖G_{k,w}‖_p ≤ C ∑_{k ≤ m} ∑_w ‖g_{k,w}‖_{L_p(O)}`. The bound puts the `G_{k,w}`
into `L_p(V)`, and `F = G_{0,∅}`; then `F ∈ W^m_p(V)` by
`Rd.memSobolev_of_forall_gridBasis_words`. -/
theorem extendsSobolevOrder_of_eLpNorm_le [Fact (1 ≤ p)] {m : ℕ} {O : Opens V} {U : Set V}
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ (f : V → ℂ) (g : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ),
      (∀ k ≤ m, ∀ w, MemLp (g k w) p (volume.restrict O)) →
      (∀ k ≤ m, ∀ w, HasWeakLineDeriv O (fun l => gridBasis V (w l)) f (g k w)) →
      ∃ (F : V → ℂ) (G : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ),
        (∀ k ≤ m, ∀ w, HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) F (G k w)) ∧
        (∀ᵐ x ∂volume, x ∈ U → F x = f x) ∧
        ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V), eLpNorm (G k w) p volume ≤
          C * ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
            eLpNorm (g k w) p (volume.restrict O)) :
    ExtendsSobolevOrder p m O U C := by
  intro f g hg hfg
  obtain ⟨F, G, hG, hFf, hb⟩ := h f g hg hfg
  have hfin : C * ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
      eLpNorm (g k w) p (volume.restrict O) < ∞ :=
    ENNReal.mul_lt_top hC.lt_top (ENNReal.sum_lt_top.2 fun k hk => ENNReal.sum_lt_top.2 fun w _ =>
      (hg k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) w).eLpNorm_lt_top)
  have hGm : ∀ k ≤ m, ∀ w, MemLp (G k w) p volume := fun k hk w => memLp_iff.2
    (((le_sum_range_sum_words (fun k w => eLpNorm (G k w) p volume) hk w).trans hb).trans_lt hfin)
  have hG0 := hG 0 (Nat.zero_le m) Fin.elim0
  have hF0 : F =ᵐ[volume] G 0 Fin.elim0 := by
    have h0 := (hasWeakLineDeriv_fin_zero _ hG0.1).unique hG0
    rwa [volume_restrict_top] at h0
  have hFm : MemLp F p volume := (hGm 0 (Nat.zero_le m) Fin.elim0).ae_eq hF0.symm
  let GLp : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V) := fun k w =>
    if hk : k ≤ m then (hGm k hk w).toLp (G k w) else 0
  have hGL : ∀ k (hk : k ≤ m) w, GLp k w = (hGm k hk w).toLp (G k w) := fun k hk w => by
    simp only [GLp, hk, ↓reduceDIte]
  have hW : ∀ k ≤ m, ∀ w, HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) (hFm.toLp F)
      (GLp k w) := fun k hk w => by
    rw [hGL k hk w]
    exact (hG k hk w).congr_ae (by rw [volume_restrict_top]; exact hFm.coeFn_toLp.symm)
      (by rw [volume_restrict_top]; exact (hGm k hk w).coeFn_toLp.symm)
  refine ⟨hFm.toLp F, memSobolev_of_forall_gridBasis_words fun k hk w =>
    ⟨_, Lp.memLp (GLp k w), hW k hk w⟩, ?_, GLp, hW, ?_⟩
  · filter_upwards [hFm.coeFn_toLp, hFf] with x h1 h2 hx
    rw [h1, h2 hx]
  · refine le_trans (le_of_eq ?_) hb
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun w _ => ?_
    rw [hGL k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) w, Lp.eNorm_toLp]

/-- **Order zero**: `W^0_p(O) = L_p(O)` extends from `O` by zero, with constant `1`: `F = 1_O f`,
and `‖F‖_p = ‖f‖_{L_p(O)} = ‖g_{0,∅}‖_{L_p(O)}`. -/
theorem extendsSobolevOrder_zero [Fact (1 ≤ p)] (O : Opens V) : ExtendsSobolevOrder p 0 O O 1 := by
  refine extendsSobolevOrder_of_eLpNorm_le ENNReal.one_ne_top fun f g hg hfg => ?_
  have hO := O.isOpen.measurableSet
  have h0 := hfg 0 le_rfl Fin.elim0
  have hfg0 : f =ᵐ[volume.restrict O] g 0 Fin.elim0 := (hasWeakLineDeriv_fin_zero _ h0.1).unique h0
  have hf : MemLp ((O : Set V).indicator f) p volume :=
    (memLp_indicator_iff_restrict hO.nullMeasurableSet).2 ((hg 0 le_rfl Fin.elim0).ae_eq hfg0.symm)
  refine ⟨(O : Set V).indicator f, fun _ _ => (O : Set V).indicator f, fun k hk w => ?_,
    ae_of_all _ fun x hx => Set.indicator_of_mem hx f, ?_⟩
  · obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact hasWeakLineDeriv_fin_zero _
      (locallyIntegrableOn_of_memLp Fact.out (by rw [volume_restrict_top]; exact hf))
  · simp only [zero_add, Finset.range_one, Finset.sum_singleton, one_mul]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hO.nullMeasurableSet, Subsingleton.elim w Fin.elim0,
      eLpNorm_congr_ae hfg0]

/-- **The value and the derivatives of top order by the norm of `W^m_p`**: for `m ≥ 1`, if
`g_{0,∅} = f` on `O` (the derivative along the empty word), then
`‖f‖_{L_p(O)} + ∑_i ‖g_{m,i}‖_{L_p(O)} ≤ ∑_{k ≤ m} ∑_w ‖g_{k,w}‖_{L_p(O)}`, since the words of
length `0` and those of length `m` are different summands on the right. -/
theorem eLpNorm_add_sum_le_sum_words {O : Opens V} {m : ℕ} (hm : 0 < m) {f : V → ℂ}
    {g : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ}
    (h0 : HasWeakLineDeriv O (fun l => gridBasis V ((Fin.elim0 : Fin 0 → Fin (finrank ℝ V)) l)) f
      (g 0 Fin.elim0)) :
    eLpNorm f p (volume.restrict O) + ∑ i, eLpNorm (g m i) p (volume.restrict O) ≤
      ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
        eLpNorm (g k w) p (volume.restrict O) := by
  rw [eLpNorm_congr_ae ((hasWeakLineDeriv_fin_zero _ h0.1).unique h0)]
  have hsub : ({0, m} : Finset ℕ) ⊆ Finset.range (m + 1) := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_range]
    omega
  refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
  rw [Finset.sum_pair hm.ne]
  gcongr
  exact Finset.single_le_sum (f := fun w => eLpNorm (g 0 w) p (volume.restrict O))
    (fun _ _ => zero_le) (Finset.mem_univ _)

/-! ### One patch -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- The constant `(∑_{k ≤ m} ∑_w C_w) A C_b` of the extension of order `m` from one patch,
with the constants `C_w = Rd.tlToSobolevConst p e_w` of the weak derivatives of `F^m_{p,2}`
functions, `A = Rd.LocalMeansBump.tlUpperConst b' (m + 1) p 2 m` of the smoothed bump `b'` and
`C_b = Rd.LocalMeansBump.higherPatchConst b (m + 1) m p`. -/
noncomputable def higherExtensionConst (m : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  (∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
    tlToSobolevConst p (fun l => gridBasis V (w l))) *
    b.dilationSmoothed.tlUpperConst (m + 1) p 2 m * b.higherPatchConst (m + 1) m p

/-- The constant of the extension of order `m ≥ 1` from one patch is finite for `1 < p < ∞`. -/
theorem higherExtensionConst_ne_top {m : ℕ} (hm : 0 < m) (hp1 : 1 < p) (hp : p ≠ ∞) :
    b.higherExtensionConst m p ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.sum_ne_top.2 fun _ _ => ENNReal.sum_ne_top.2 fun _ _ =>
      tlToSobolevConst_ne_top hp1 hp _)
    (b.dilationSmoothed.tlUpperConst_ne_top _ hp1 hp ENNReal.one_lt_two (Nat.cast_pos.2 hm)))
    (b.higherPatchConst_ne_top _ _ hp1 hp)

/-- **The extension of order `m` from one patch** (Rychkov's local extension with the local means
of the derivatives of order `m`): let `m ≥ 1`, `U ⊆ T` with `T` open, let the dual kernels of
order `m + 1` of the smoothed bump `b'` at points of `U` only see `W`, and let `x - y ∈ T` for
every `x ∈ W`, every level `j` and every `y` in the support of the dilated higher divergence
kernels `(K_i)_{2^j}` of `b`. Then for `1 < p < ∞` the local extension
`F = ∑_j η_j ⋆ 1_W (k_j ⋆ 1_T f)` of order `m + 1` of `b'` lies in `F^m_{p,2}(V) = W^m_p(V)` and
agrees with `f` on `U`, with the constant `Rd.LocalMeansBump.higherExtensionConst b m p`
(`Rd.LocalMeansBump.tlLocalNormOn_le_higherPatchConst`,
`Rd.LocalMeansBump.triebelLizorkinNorm_localExtension_le`,
`Rd.exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le`). -/
theorem extendsSobolevOrder [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ} (hm : 0 < m)
    {U W : Set V} (hU : MeasurableSet U) (hW : MeasurableSet W) {T : Opens V} (hUT : U ⊆ T)
    (hUW : ∀ x ∈ U, ∀ j y, b.dilationSmoothed.dual (m + 1) j y ≠ 0 → x - y ∈ W)
    (hsupp : ∀ x ∈ W, ∀ j i, ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel (m + 1) m i : V → ℂ)),
      x - y ∈ T) :
    ExtendsSobolevOrder p m T U (b.higherExtensionConst m p) := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  intro f g hg hfg
  have h0 := hfg 0 (Nat.zero_le m) Fin.elim0
  have hf : MemLp f p (volume.restrict T) :=
    (hg 0 (Nat.zero_le m) Fin.elim0).ae_eq ((hasWeakLineDeriv_fin_zero _ h0.1).unique h0).symm
  have hf₀ := (memLp_indicator_iff_restrict T.isOpen.measurableSet.nullMeasurableSet).2 hf
  have hY : ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
      eLpNorm (g k w) p (volume.restrict T) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun k hk => ENNReal.sum_ne_top.2 fun w _ =>
      (hg k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) w).eLpNorm_ne_top
  have hX := (b.tlLocalNormOn_le_higherPatchConst hp1 hp (Nat.lt_succ_self m) hW hf (hg m le_rfl)
    (hfg m le_rfl) hsupp hf₀.coeFn_toLp).trans
      (mul_le_mul_right (eLpNorm_add_sum_le_sum_words hm h0) _)
  have hXf := hX.trans_lt (ENNReal.mul_lt_top (b.higherPatchConst_ne_top _ _ hp1 hp).lt_top
    hY.lt_top)
  have hs : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hTL := b.dilationSmoothed.triebelLizorkinNorm_localExtension_le hp1 hp hW (m + 1) hs
    ENNReal.one_lt_two hXf
  have hmem : MemTriebelLizorkin (m : ℝ) 2 (b.dilationSmoothed.localExtension hp hW (m + 1)
      (hf₀.toLp _)) := hTL.trans_lt (ENNReal.mul_lt_top
    (b.dilationSmoothed.tlUpperConst_ne_top _ hp1 hp ENNReal.one_lt_two hs).lt_top hXf)
  obtain ⟨G, hG⟩ := exists_forall_words_of_forall_le (m := m)
    (P := fun k w (G : Lp ℂ p (volume : Measure V)) => HasWeakLineDeriv ⊤
      (fun l => gridBasis V (w l))
        (b.dilationSmoothed.localExtension hp hW (m + 1) (hf₀.toLp _)) G ∧
      ‖G‖ₑ ≤ tlToSobolevConst p (fun l => gridBasis V (w l)) * triebelLizorkinNorm (m : ℝ) 2
        (b.dilationSmoothed.localExtension hp hW (m + 1) (hf₀.toLp _)))
    fun k hk _ => exists_hasWeakLineDeriv_of_memTriebelLizorkin_of_le hp1 hp hk _ hmem
  refine ⟨_, memSobolev_of_memTriebelLizorkin hp1 hp hmem,
    b.dilationSmoothed.ae_localExtension_eq_of_ae_eq_indicator hp (Nat.le_add_left 1 m) hU hW hUT
      hUW hf₀.coeFn_toLp (b.dilationSmoothed.summable_localExtTerm_of_tlLocalNormOn hp hW (m + 1)
        hs two_ne_zero hXf), G, fun k hk w => (hG k hk w).1, ?_⟩
  calc ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V), ‖G k w‖ₑ
      ≤ ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
          tlToSobolevConst p (fun l => gridBasis V (w l)) * triebelLizorkinNorm (m : ℝ) 2
            (b.dilationSmoothed.localExtension hp hW (m + 1) (hf₀.toLp _)) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun w _ =>
          (hG k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) w).2
    _ = (∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
          tlToSobolevConst p (fun l => gridBasis V (w l))) * triebelLizorkinNorm (m : ℝ) 2
            (b.dilationSmoothed.localExtension hp hW (m + 1) (hf₀.toLp _)) := by
        simp_rw [Finset.sum_mul]
    _ ≤ (∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
          tlToSobolevConst p (fun l => gridBasis V (w l))) *
          (b.dilationSmoothed.tlUpperConst (m + 1) p 2 m * (b.higherPatchConst (m + 1) m p *
            ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
              eLpNorm (g k w) p (volume.restrict T))) := by
        gcongr
        exact hTL.trans (mul_le_mul_right hX _)
    _ = _ := by rw [higherExtensionConst]; ring

end LocalMeansBump

/-! ### Pasting in `W^m_p(V)` -/

/-- **The Leibniz rule with a bound, on all of `V`**: let `G_{k,w} = ∂^{e_w} F` weakly on an open
set `B` for all words of length `k ≤ m`, and let `χ` be smooth with compact support in `B`. Then
`χ F` has a weak derivative `H` on `V` along every word of length `k ≤ m`, with
`‖H‖_p ≤ C_k(χ) ∑_{k' ≤ m} ∑_{w'} ‖G_{k',w'}‖_{L_p(B)}`
(`Rd.exists_hasWeakLineDeriv_mul_of_tsupport_subset` with `O = V`). -/
theorem exists_hasWeakLineDeriv_top_mul_le [Fact (1 ≤ p)] {m : ℕ} {B : Opens V} {F : V → ℂ}
    {G : (k : ℕ) → (Fin k → Fin (finrank ℝ V)) → V → ℂ}
    (hG : ∀ k ≤ m, ∀ w, HasWeakLineDeriv B (fun l => gridBasis V (w l)) F (G k w))
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχB : tsupport χ ⊆ B) {k : ℕ} (hk : k ≤ m) (w : Fin k → Fin (finrank ℝ V)) :
    ∃ H : V → ℂ, HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l)) (fun x => (χ x : ℂ) * F x) H ∧
      eLpNorm H p volume ≤ leibnizConst χ k * ∑ k' ∈ Finset.range (m + 1),
        ∑ w' : Fin k' → Fin (finrank ℝ V), eLpNorm (G k' w') p (volume.restrict B) := by
  obtain ⟨H, hH, hHb⟩ := exists_hasWeakLineDeriv_mul_of_tsupport_subset (p := p) (O := ⊤) (B := B)
    G (fun k hk w => by rw [top_inf_eq]; exact hG k hk w) hχ hχc hχB hk w
  refine ⟨H, hH, ?_⟩
  rw [volume_restrict_top, top_inf_eq] at hHb
  exact hHb.trans (mul_le_mul_right (sum_range_sum_words_mono
    (fun k' w' => eLpNorm (G k' w') p (volume.restrict B)) hk) _)

/-- **Pasting bounded extensions of order `m`**: let `(U_i)` be a finite cover of `Ō` by bounded
open sets and let Sobolev functions of order `m` on `O` extend from every `O ∩ U_i` with finite
constants. Then they extend from `O` with a finite constant: for a smooth resolution of unity
`(ψ_i)` subordinate to `(U_i)` (`Rd.exists_smooth_partition`), `F = ∑_i ψ_i F_i` agrees with `f`
on `O` (`Rd.ae_sum_mul_eq`), and its derivatives along words come from the Leibniz rule
(`Rd.exists_hasWeakLineDeriv_top_mul_le`). -/
theorem extendsSobolevOrder_of_cover [Fact (1 ≤ p)] {m : ℕ} {ι : Type*} [Finite ι] {O : Opens V}
    (U : ι → Set V) (hUo : ∀ i, IsOpen (U i)) (hUb : ∀ i, Bornology.IsBounded (U i))
    (hcov : closure (O : Set V) ⊆ ⋃ i, U i) {C : ι → ℝ≥0∞} (hC : ∀ i, C i ≠ ∞)
    (hext : ∀ i, ExtendsSobolevOrder p m O ((O : Set V) ∩ U i) (C i)) :
    ∃ C' : ℝ≥0∞, C' ≠ ∞ ∧ ExtendsSobolevOrder p m O O C' := by
  let := Fintype.ofFinite ι
  classical
  obtain ⟨ψ, hψ, hψU, hψ1, -⟩ := exists_smooth_partition isClosed_closure U hUo hcov
  have hcs : ∀ i, HasCompactSupport (ψ i) := fun i =>
    isCompact_of_isClosed_isBounded (isClosed_tsupport _) ((hUb i).subset (hψU i))
  have hC' : ∑ i, (∑ k ∈ Finset.range (m + 1), ∑ _w : Fin k → Fin (finrank ℝ V),
      leibnizConst (ψ i) k) * C i ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.mul_ne_top (ENNReal.sum_ne_top.2 fun k _ =>
      ENNReal.sum_ne_top.2 fun _ _ => leibnizConst_ne_top (hψ i) (hcs i) k) (hC i)
  refine ⟨_, hC', extendsSobolevOrder_of_eLpNorm_le hC' fun f g hg hfg => ?_⟩
  choose F hF hFf G hG hb using fun i => hext i f g hg hfg
  choose H hH using fun i => exists_forall_words_of_forall_le (m := m)
    (P := fun k w (H : V → ℂ) => HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l))
      (fun x => (ψ i x : ℂ) * F i x) H ∧
      eLpNorm H p volume ≤ leibnizConst (ψ i) k * (C i * ∑ k ∈ Finset.range (m + 1),
        ∑ w : Fin k → Fin (finrank ℝ V), eLpNorm (g k w) p (volume.restrict O))) fun k hk w => by
    obtain ⟨H, hH, hHb⟩ := exists_hasWeakLineDeriv_top_mul_le (p := p) (B := ⊤)
      (G := fun k w => (G i k w : V → ℂ)) (hG i) (hψ i) (hcs i) (Set.subset_univ _) hk w
    refine ⟨H, hH, hHb.trans (mul_le_mul_right ?_ _)⟩
    simpa only [volume_restrict_top, ← Lp.eNorm_def] using hb i
  refine ⟨fun x => ∑ i, (ψ i x : ℂ) * F i x, fun k w => ∑ i, H i k w, fun k hk w => ?_,
    ae_sum_mul_eq hψU (fun x hx => hψ1 x (subset_closure hx)) hFf, ?_⟩
  · refine (HasWeakLineDeriv.sum (s := Finset.univ) fun i _ => (hH i k hk w).1).congr_ae ?_ ?_ <;>
      exact ae_of_all _ fun x => by simp only [Finset.sum_apply]
  · calc _ ≤ ∑ k ∈ Finset.range (m + 1), ∑ _w : Fin k → Fin (finrank ℝ V), ∑ i,
          leibnizConst (ψ i) k * (C i * ∑ k ∈ Finset.range (m + 1),
            ∑ w : Fin k → Fin (finrank ℝ V), eLpNorm (g k w) p (volume.restrict O)) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun w _ =>
            (eLpNorm_sum_le Fact.out).trans
              (Finset.sum_le_sum fun i _ => (hH i k (Nat.lt_succ_iff.1
                (Finset.mem_range.1 hk)) w).2)
      _ = _ := by rw [sum_range_sum_words_sum_mul, Finset.sum_mul]; simp_rw [mul_assoc]

/-! ### The supports of the higher divergence kernels in the patches -/

namespace LipschitzGraph

variable (G : LipschitzGraph V)

/-- **Boundary patches, the support condition for the higher divergence kernels**: for a bump
supported in `-K`, `L ≥ 1` and `L R ≤ ε`, `x - y ∈ Ω ∩ B(c, ρ)` for `x ∈ Ω ∩ B(c, ρ - ε)` and `y`
in the support of a dilated higher divergence kernel
(`Rd.LipschitzGraph.tsupport_dilate_higherKernel_subset`,
`Rd.LipschitzGraph.sub_mem_patch_of_mem_closedCone`). -/
theorem patch_support_higherKernel {b : LocalMeansBump V} (hb : G.ConeSupported b.toFun)
    {L m : ℕ} (hL : 1 ≤ L) {ε ρ : ℝ} {c : V} (hR : L * b.radius ≤ ε) :
    ∀ x ∈ G.domain ∩ ball c (ρ - ε), ∀ (j : ℕ) (i : Fin m → Fin (finrank ℝ V)),
      ∀ y ∈ tsupport (dilate (2 ^ j) (b.higherKernel L m i : V → ℂ)),
        x - y ∈ G.domain ∩ ball c ρ := by
  intro x hx j i y hy
  obtain ⟨hyK, hyR⟩ := G.tsupport_dilate_higherKernel_subset hb hL i j hy
  rw [mem_closedBall, dist_zero_right] at hyR
  exact G.sub_mem_patch_of_mem_closedCone hx hyK (hyR.trans hR)

end LipschitzGraph

/-! ### The extension theorem of higher order -/

/-- **A small radius**: for every `m ∈ ℕ` and `ε > 0`, the radius `R = (1/2) / ((m + 1)(1 + 1/ε))`
satisfies `(m + 1) R ≤ ε`, since `(m + 1) R = ε / (2 (ε + 1))`. -/
theorem natCast_succ_mul_half_div_le {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ((m + 1 : ℕ) : ℝ) * (1 / 2 / (((m + 1 : ℕ) : ℝ) * (1 + 1 / ε))) ≤ ε := by
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [show ((m + 1 : ℕ) : ℝ) * (1 / 2 / (((m + 1 : ℕ) : ℝ) * (1 + 1 / ε))) = ε / (2 * (ε + 1)) by
    field_simp]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

namespace BoundedLipschitzDomain

variable (Ω : BoundedLipschitzDomain V)

/-- **The boundary patches of order `m ≥ 1`**: Sobolev functions of order `m` on `Ω` extend from
`Ω ∩ B(c_j, ρ_j - 2ε)` with a finite constant, by the extension from one patch
(`Rd.LocalMeansBump.extendsSobolevOrder`) with a cone bump of `Ω_j` of radius `R ≤ ε / (m + 1)`
(`Rd.LipschitzGraph.exists_coneBump_radius_le`, `Rd.LipschitzGraph.patch_support`,
`Rd.LipschitzGraph.patch_support_higherKernel`). -/
theorem exists_extendsSobolevOrder_boundary [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (j : Fin Ω.N) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolevOrder p m Ω.toOpens
      (Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε)) C := by
  obtain ⟨b, hb, -, hR⟩ :=
    (Ω.graph j).exists_coneBump_radius_le (a := ((m + 1 : ℕ) : ℝ)) (Nat.cast_nonneg _) hε
  have hTo : IsOpen ((Ω.graph j).domain ∩ ball (Ω.center j) (Ω.radius j)) :=
    (Ω.graph j).isOpen_domain.inter isOpen_ball
  have hTΩ : (⟨_, hTo⟩ : Opens V) ≤ Ω.toOpens := by
    change (Ω.graph j).domain ∩ ball (Ω.center j) (Ω.radius j) ⊆ Ω.carrier
    rw [← Ω.inter_ball_eq j le_rfl]
    exact Set.inter_subset_left
  have hU : Ω.carrier ∩ ball (Ω.center j) (Ω.radius j - 2 * ε) =
      (Ω.graph j).domain ∩ ball (Ω.center j) (Ω.radius j - 2 * ε) :=
    Ω.inter_ball_eq j (by linarith)
  refine ⟨_, b.higherExtensionConst_ne_top hm hp1 hp, ?_⟩
  rw [hU]
  exact (b.extendsSobolevOrder hp1 hp hm
    (((Ω.graph j).isOpen_domain.inter isOpen_ball).measurableSet)
    (((Ω.graph j).isOpen_domain.inter isOpen_ball).measurableSet) (T := ⟨_, hTo⟩)
    (Set.inter_subset_inter_right _ (ball_subset_ball (by linarith)))
    ((Ω.graph j).patch_support ((Ω.graph j).coneSupported_dilationSmoothed hb) hR)
    ((Ω.graph j).patch_support_higherKernel hb (Nat.le_add_left 1 m) hR)).of_le hTΩ

/-- **The inner patch of order `m`, for every `1 ≤ p ≤ ∞`**: Sobolev functions of order `m` on `Ω`
extend from `{infDist(·, Ωᶜ) > 2δ}` with a finite constant. The proof takes a smooth cutoff `χ`
with compact support in `Ω` and `χ = 1` near `{infDist(·, Ωᶜ) ≥ 2δ}`
(`Rd.BoundedLipschitzDomain.exists_cutoff_interior`); then `χ f` has the derivatives of the
Leibniz rule (`Rd.exists_hasWeakLineDeriv_top_mul_le`), and the constant is `∑_{k ≤ m} ∑_w C_k(χ)`
(`Rd.leibnizConst`). -/
theorem exists_extendsSobolevOrder_interior [Fact (1 ≤ p)] (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolevOrder p m Ω.toOpens
      (Ω.carrier ∩ {x : V | 2 * δ < infDist x Ω.carrierᶜ}) C := by
  obtain ⟨χ, hχ, hχc, hχΩ, -, hχ1⟩ := Ω.exists_cutoff_interior hδ
  have hC : ∑ k ∈ Finset.range (m + 1), ∑ _w : Fin k → Fin (finrank ℝ V), leibnizConst χ k ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.sum_ne_top.2 fun _ _ => leibnizConst_ne_top hχ hχc k
  refine ⟨_, hC, extendsSobolevOrder_of_eLpNorm_le hC fun f g hg hfg => ?_⟩
  obtain ⟨H, hH⟩ := exists_forall_words_of_forall_le (m := m)
    (P := fun k w (H : V → ℂ) => HasWeakLineDeriv ⊤ (fun l => gridBasis V (w l))
      (fun x => (χ x : ℂ) * f x) H ∧
      eLpNorm H p volume ≤ leibnizConst χ k * ∑ k ∈ Finset.range (m + 1),
        ∑ w : Fin k → Fin (finrank ℝ V), eLpNorm (g k w) p (volume.restrict Ω.toOpens))
    fun k hk w => exists_hasWeakLineDeriv_top_mul_le (p := p) hfg hχ hχc hχΩ hk w
  refine ⟨fun x => (χ x : ℂ) * f x, H, fun k hk w => (hH k hk w).1, ae_of_all _ fun x hx => ?_, ?_⟩
  · change (χ x : ℂ) * f x = f x
    rw [hχ1.self_of_nhdsSet x (show 2 * δ ≤ infDist x Ω.carrierᶜ from hx.2.le), Complex.ofReal_one,
      one_mul]
  · calc _ ≤ ∑ k ∈ Finset.range (m + 1), ∑ _w : Fin k → Fin (finrank ℝ V), leibnizConst χ k *
          ∑ k ∈ Finset.range (m + 1), ∑ w : Fin k → Fin (finrank ℝ V),
            eLpNorm (g k w) p (volume.restrict Ω.toOpens) :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun w _ =>
            (hH k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) w).2
      _ = _ := by simp_rw [Finset.sum_mul]

/-- **The extension theorem of order `m` with a bound**: for a bounded Lipschitz domain `Ω` in
dimension `n ≥ 1`, `1 < p < ∞` and `m ∈ ℕ` there is a finite constant `C` such that every `f`
with weak derivatives `g_{k,w} = ∂^{e_w} f ∈ L_p(Ω)` along all words `w` of length `k ≤ m` agrees
on `Ω` with some `F ∈ W^m_p(V)` whose weak derivatives `G_{k,w} = ∂^{e_w} F` satisfy
`∑_{k ≤ m} ∑_w ‖G_{k,w}‖_p ≤ C ∑_{k ≤ m} ∑_w ‖g_{k,w}‖_{L_p(Ω)}`. The patches
`Rd.BoundedLipschitzDomain.patch` cover `ΩBar`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder_boundary`,
`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder_interior`), pasted by
`Rd.extendsSobolevOrder_of_cover` (`Rd.BoundedLipschitzDomain.exists_of_patches`); for `m = 0`,
`Rd.extendsSobolevOrder_zero`. -/
theorem exists_extendsSobolevOrder [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) (m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ExtendsSobolevOrder p m Ω.toOpens Ω.carrier C := by
  have : Fact (1 ≤ p) := ⟨hp1.le⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, ENNReal.one_ne_top, extendsSobolevOrder_zero Ω.toOpens⟩
  exact Ω.exists_of_patches (fun U C => ExtendsSobolevOrder p m Ω.toOpens U C)
    (fun U hUo hUb hcov _ hC hext =>
      extendsSobolevOrder_of_cover (O := Ω.toOpens) U hUo hUb hcov hC hext)
    (fun _ hε j => Ω.exists_extendsSobolevOrder_boundary hp1 hp hm hε j)
    (fun _ hδ => Ω.exists_extendsSobolevOrder_interior (p := p) m hδ)

/-- **The extension theorem of order `m`** (the extension theorem of Calderón and Stein for
`1 < p < ∞`, by Rychkov's local extension and the local means of the derivatives of order `m`):
for a bounded Lipschitz domain `Ω`, `1 < p < ∞` and `m ∈ ℕ`, every `f ∈ W^m_p(Ω)` agrees almost
everywhere on `Ω` with some `F ∈ W^m_p(V)`
(`Rd.BoundedLipschitzDomain.exists_extendsSobolevOrder` in dimension `n ≥ 1`,
`Rd.exists_memSobolev_of_memWeakSobolev_of_subsingleton` in dimension `0`). -/
theorem exists_memSobolev_of_memWeakSobolev_order (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : V → ℂ} (hf : MemWeakSobolev Ω.toOpens m p f) :
    ∃ F : Lp ℂ p (volume : Measure V), MemSobolev m F ∧
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact exists_memSobolev_of_memWeakSobolev_of_subsingleton hf
  obtain ⟨C, -, hC⟩ := Ω.exists_extendsSobolevOrder hp1 hp m
  obtain ⟨g, hg⟩ := exists_forall_words_of_forall_le (m := m)
    (P := fun k w (g : V → ℂ) => MemLp g p (volume.restrict Ω.toOpens) ∧
      HasWeakLineDeriv Ω.toOpens (fun l => gridBasis V (w l)) f g)
    fun k hk w => hf.2 k hk fun l => gridBasis V (w l)
  obtain ⟨F, hF, hFf, -⟩ := hC f g (fun k hk w => (hg k hk w).1) fun k hk w => (hg k hk w).2
  exact ⟨F, hF, (ae_restrict_iff' Ω.measurableSet).2 hFf⟩

/-- **`W^m_p(Ω)` is the space of restrictions of `W^m_p(V)`**: for a bounded Lipschitz domain `Ω`,
`1 < p < ∞` and `m ∈ ℕ`, `f` lies in `W^m_p(Ω)` iff it agrees almost everywhere on `Ω` with some
`F ∈ W^m_p(V)` (`Rd.BoundedLipschitzDomain.exists_memSobolev_of_memWeakSobolev_order`; the converse
restricts the weak derivatives, `Rd.MemWeakSobolev.mono_set`). -/
theorem memWeakSobolev_iff_exists_memSobolev_order (hp1 : 1 < p) (hp : p ≠ ∞) (m : ℕ)
    (f : V → ℂ) :
    MemWeakSobolev Ω.toOpens m p f ↔ ∃ F : Lp ℂ p (volume : Measure V), MemSobolev m F ∧
      (F : V → ℂ) =ᵐ[volume.restrict Ω.carrier] f := by
  refine ⟨Ω.exists_memSobolev_of_memWeakSobolev_order hp1 hp, ?_⟩
  rintro ⟨F, hF, hFf⟩
  exact (MemWeakSobolev.mono_set hF le_top).congr_ae hFf

end BoundedLipschitzDomain

end Rd
