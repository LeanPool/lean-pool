/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Atoms.AtomSynthesis

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Atomic decompositions

Each local-means term of `F ∈ L_p(V)`, `1 ≤ p < ∞`, has a cell-atom expansion. This
construction proves the forward direction of the regular-atom characterization below.
For a kernel `K` and `g ∈ L_p`, the dyadic cells
`P_{j,m}` split the convolution into **cell atoms** (`Rd.cellAtom`):

`K ⋆ g = ∑_m λ_{j,m} a_{j,m}`,  `λ_{j,m} = 2^(jn/p) ‖1_{P_{j,m}} g‖_p`,
`a_{j,m} = λ_{j,m}⁻¹ K ⋆ (1_{P_{j,m}} g)`

(`Rd.conv_eq_tsum_cellAtom`), with `‖λ_{j,·}‖_{ℓ_p} = 2^(jn/p) ‖g‖_p`, since the cells partition
`V` (`Rd.levelNorm_cellCoef`). Coefficients and atoms of a cell depend only on `g` on that cell,
so the decomposition holds as soon as every `1_{P_{j,m}} g` lies in `L_p`
(`Rd.conv_eq_tsum_cellAtom_of_indicator`, from the termwise convolution of locally finite series
`Rd.conv_tsum_of_finset`); the cells have finite volume, so this holds with `p = 1` for every
`g ∈ L_p` (`Rd.memLp_one_indicator_cell`), and then the coefficients are at most the averages
`2^(jn) ∫_{P_{j,m}} |g|` (`Rd.enorm_cellCoef_one_le`). If `K` vanishes outside
`B(0, ρ 2^(-j))` and `|Δ_h^l K| ≤ A 2^(jn) min(1, (2^j ‖h‖)^l)` for `l ≤ r`, Hölder's
inequality on balls (`Rd.enorm_conv_le_of_bound`) and `Δ_h^r (K ⋆ g) = (Δ_h^r K) ⋆ g`
(`Rd.higherDiff_conv_apply`) give the pointwise bounds of atoms of order and exponent `r`
(`Rd.enorm_higherDiff_cellAtom_le`); by `Rd.isRegularAtom_of_pointwise` the cell atoms are
regular atoms (`Rd.isRegularAtom_cellAtom`).
The dual kernels `η_j` of a bump satisfy these bounds
(`Rd.LocalMeansBump.exists_higherDiff_dual_bound`).

**Atomic characterisation** (`Rd.LocalMeansBump.besov_iff_atomic`): for `0 < s < L`,
`F ∈ B^s_{p,q}(V)` iff `F = ∑_j ∑_m λ_{j,m} a_{j,m}`
with regular atoms of order and exponent `L`, centres of bounded overlap and
`‖λ‖_{b^s_{p,q}} < ∞`. This is a regular-atom variant of Schneider–Vybíral
([arXiv:1201.2280](https://arxiv.org/abs/1201.2280), Theorem 2.6). Their Corollary 2.8 treats
Lipschitz atoms for `0 < s < 1`. The atoms of `F` here are the cell atoms of `η_j ⋆ (k_j ⋆ F)`
(`Rd.LocalMeansBump.atomic_decomposition`); their coefficients have
`‖λ‖_{b^s_{p,q}} = ‖(2^(js) ‖k_j ⋆ F‖_p)_j‖_{ℓ_q}`, the local means quasi-norm.
-/

@[expose] public section

open MeasureTheory Filter Topology Module Metric
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Cell atoms -/

/-- The **coefficient of a cell**, `λ_{j,m} = 2^(jn/p) ‖1_{P_{j,m}} g‖_p`. -/
noncomputable def cellCoef (p : ℝ≥0∞) (j : ℕ) (g : V → ℂ) (m : Fin (finrank ℝ V) → ℤ) : ℂ :=
  ((dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm ((cell j m).indicator g) p volume).toReal :
    ℂ)

/-- The **cell atom** `a_{j,m} = λ_{j,m}⁻¹ K ⋆ (1_{P_{j,m}} g)` (zero if `λ_{j,m} = 0`). -/
noncomputable def cellAtom (p : ℝ≥0∞) (K : V → ℂ) (j : ℕ) (g : V → ℂ)
    (m : Fin (finrank ℝ V) → ℤ) (x : V) : ℂ :=
  (cellCoef p j g m)⁻¹ * conv K ((cell j m).indicator g) volume x

/-- `|λ_{j,m}| = 2^(jn/p) ‖1_{P_{j,m}} g‖_p` for `g ∈ L_p`. -/
theorem enorm_cellCoef {p : ℝ≥0∞} {g : V → ℂ} (hg : MemLp g p volume) (j : ℕ)
    (m : Fin (finrank ℝ V) → ℤ) :
    ‖cellCoef p j g m‖ₑ =
      dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm ((cell j m).indicator g) p volume := by
  have hfin : dyadicWeight (finrank ℝ V / p.toReal) j *
      eLpNorm ((cell j m).indicator g) p volume ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.dyadicWeight_ne_top _ _)
      (hg.indicator (measurableSet_cell j m).nullMeasurableSet).eLpNorm_ne_top
  rw [cellCoef, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]

/-- The coefficients with exponent one are averages: `|λ_{j,m}| ≤ 2^(jn) ∫_{P_{j,m}} |g|` for the
coefficients `Rd.cellCoef 1` of an almost everywhere strongly measurable `g` (equality for
`g ∈ L_1` is `Rd.enorm_cellCoef`). -/
theorem enorm_cellCoef_one_le (j : ℕ) {g : V → ℂ} (hg : AEStronglyMeasurable g volume)
    (m : Fin (finrank ℝ V) → ℤ) :
    ‖cellCoef 1 j g m‖ₑ ≤ dyadicWeight (finrank ℝ V : ℝ) j * ∫⁻ y in cell j m, ‖g y‖ₑ := by
  rw [cellCoef, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_toReal_le.trans_eq ?_
  rw [ENNReal.toReal_one, div_one, eLpNorm_one_eq_lintegral_eNorm
    (hg.indicator (measurableSet_cell j m))]
  simp_rw [eNorm_indicator_eq_indicator_eNorm]
  rw [lintegral_indicator (measurableSet_cell j m)]

/-- `λ_{j,m} a_{j,m} = K ⋆ (1_{P_{j,m}} g)`. -/
theorem cellCoef_mul_cellAtom {p : ℝ≥0∞} (hp0 : p ≠ 0) {g : V → ℂ} (hg : MemLp g p volume)
    (K : V → ℂ) (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) (x : V) :
    cellCoef p j g m * cellAtom p K j g m x = conv K ((cell j m).indicator g) volume x := by
  by_cases h0 : cellCoef p j g m = 0
  · have hn : eLpNorm ((cell j m).indicator g) p volume = 0 := by
      have h1 := enorm_cellCoef hg j m
      rw [h0, eNorm_zero, eq_comm, mul_eq_zero] at h1
      exact h1.resolve_left (ENNReal.dyadicWeight_ne_zero _ _)
    have hae : (cell j m).indicator g =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff hp0).1 hn
    rw [h0, zero_mul, conv_congr_ae hae, conv_apply]
    simp
  · rw [cellAtom, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]

/-- The cells have finite volume: `P_{j,m}` lies in the closed ball `closedBall(c_{j,m}, n
2^(-j))`. -/
theorem volume_cell_ne_top (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) : volume (cell (V := V) j m) ≠ ∞ :=
  ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono fun _ hx => by
    rw [mem_closedBall, dist_eq_norm]
    exact norm_sub_cellCenter_le hx)

/-- The coefficient of a cell depends only on `g` on that cell:
`λ_{j,m}(1_{P_{j,m}} g) = λ_{j,m}(g)`. -/
theorem cellCoef_indicator (p : ℝ≥0∞) (j : ℕ) (g : V → ℂ) (m : Fin (finrank ℝ V) → ℤ) :
    cellCoef p j ((cell j m).indicator g) m = cellCoef p j g m := by
  rw [cellCoef, cellCoef, Set.indicator_indicator, Set.inter_self]

/-- The atom of a cell depends only on `g` on that cell:
`a_{j,m}(1_{P_{j,m}} g) = a_{j,m}(g)`. -/
theorem cellAtom_indicator (p : ℝ≥0∞) (K : V → ℂ) (j : ℕ) (g : V → ℂ)
    (m : Fin (finrank ℝ V) → ℤ) :
    cellAtom p K j ((cell j m).indicator g) m = cellAtom p K j g m := by
  funext x
  rw [cellAtom, cellAtom, cellCoef_indicator, Set.indicator_indicator, Set.inter_self]

/-- On a cell, `L_p` functions are integrable: `1_{P_{j,m}} g ∈ L_1` for `g ∈ L_p`, `p ≥ 1`,
since the cell has finite volume. -/
theorem memLp_one_indicator_cell {p : ℝ≥0∞} (hp1 : 1 ≤ p) {g : V → ℂ} (hg : MemLp g p volume)
    (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) : MemLp ((cell j m).indicator g) 1 volume :=
  (hg.indicator (measurableSet_cell j m).nullMeasurableSet).mono_exponent_of_measure_support_ne_top
    (fun _ hx => Set.indicator_of_notMem hx g) (volume_cell_ne_top j m) hp1

/-- `λ_{j,m} a_{j,m} = K ⋆ (1_{P_{j,m}} g)` as soon as `1_{P_{j,m}} g ∈ L_p`. -/
theorem cellCoef_mul_cellAtom_of_indicator {p : ℝ≥0∞} (hp0 : p ≠ 0) {g : V → ℂ} {j : ℕ}
    {m : Fin (finrank ℝ V) → ℤ} (hg : MemLp ((cell j m).indicator g) p volume) (K : V → ℂ)
    (x : V) :
    cellCoef p j g m * cellAtom p K j g m x = conv K ((cell j m).indicator g) volume x := by
  have h := cellCoef_mul_cellAtom hp0 hg K j m x
  rwa [cellCoef_indicator, cellAtom_indicator, Set.indicator_indicator, Set.inter_self] at h

/-- **Convolution with a locally finite series, term by term**: for a continuous kernel `K` with
compact support and locally integrable `u_m`, if only the indices of a finite set `T` have
`u_m(x - y) ≠ 0` for some `y` with `K(y) ≠ 0`, then `K ⋆ (∑_m u_m)(x) = ∑_m (K ⋆ u_m)(x)`. -/
theorem conv_tsum_of_finset {ι : Type*} {K : V → ℂ} (hKc : Continuous K)
    (hKs : HasCompactSupport K) {u : ι → V → ℂ} (hu : ∀ m, LocallyIntegrable (u m) volume)
    (x : V) (T : Finset ι) (hT : ∀ m ∉ T, ∀ y, K y ≠ 0 → u m (x - y) = 0) :
    conv K (fun y => ∑' m, u m y) volume x = ∑' m, conv K (u m) volume x := by
  have hvanish : ∀ m ∉ T, ∀ y, K y * u m (x - y) = 0 := fun m hm y => by
    by_cases hy : K y = 0
    · rw [hy, zero_mul]
    · rw [hT m hm y hy, mul_zero]
  have hzero : ∀ m ∉ T, conv K (u m) volume x = 0 := fun m hm => by
    rw [conv_apply]
    simp only [hvanish m hm, integral_zero]
  rw [tsum_eq_sum hzero, conv_apply]
  have hpt : ∀ y, K y * ∑' m, u m (x - y) = ∑ m ∈ T, K y * u m (x - y) := fun y => by
    by_cases hy : K y = 0
    · simp [hy]
    · rw [tsum_eq_sum fun m hm => hT m hm y hy, Finset.mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun m _ => by
    simpa using integrable_translate_mul_of_locallyIntegrable hKc hKs (hu m) 0 x]
  exact Finset.sum_congr rfl fun m _ => (conv_apply _ _ _ _).symm

omit [MeasurableSpace V] [BorelSpace V] in
/-- The cells split every function: `g(y) = ∑_m (1_{P_{j,m}} g)(y)`, where only the cell
containing `y` contributes. -/
theorem tsum_indicator_cell (j : ℕ) (g : V → ℂ) (y : V) :
    ∑' m, (cell j m).indicator g y = g y := by
  rw [tsum_eq_single (f := fun m => (cell j m).indicator g y) (cellIndex j y) fun m hm =>
    Set.indicator_of_notMem (fun hy : y ∈ cell j m => hm (show cellIndex j y = m from hy).symm) _]
  exact Set.indicator_of_mem (mem_cell_cellIndex j y) g

/-- **Cell decomposition of a convolution, cellwise hypothesis**: `K ⋆ g = ∑_m λ_{j,m} a_{j,m}` at
every point, with finitely many nonzero terms, for a continuous `K` that vanishes outside
`closedBall(0, ρ)`, as soon as `1_{P_{j,m}} g ∈ L_p` for every cell. -/
theorem conv_eq_tsum_cellAtom_of_indicator {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ}
    (hKc : Continuous K) {ρ : ℝ} (hρ : 0 ≤ ρ) (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) {j : ℕ}
    (hg : ∀ m, MemLp ((cell j m).indicator g) p volume) (x : V) :
    conv K g volume x = ∑' m, cellCoef p j g m * cellAtom p K j g m x := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hKs : HasCompactSupport K := HasCompactSupport.intro (isCompact_closedBall 0 ρ)
    fun y hy => hKρ y (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)
  set R := ρ * 2 ^ j + finrank ℝ V
  have hR : 0 ≤ R := by positivity
  -- the cells near `x`
  have hnear : ∀ m y, K y ≠ 0 → x - y ∈ cell j m → ‖x - cellCenter j m‖ ≤ R / 2 ^ j :=
    fun m y hy hxy => by
      have h1 : ‖y‖ ≤ ρ := not_lt.1 fun h => hy (hKρ y h)
      have h2 := norm_sub_cellCenter_le hxy
      calc ‖x - cellCenter j m‖ ≤ ‖x - (x - y)‖ + ‖x - y - cellCenter j m‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ρ + finrank ℝ V / 2 ^ j := by rw [sub_sub_cancel]; exact add_le_add h1 h2
        _ = R / 2 ^ j := by
            simp only [R]
            field_simp
  obtain ⟨T, hT, -⟩ := exists_finset_of_card_le
    (P := fun m => ‖x - cellCenter j m‖ ≤ R / 2 ^ j)
    fun S hS => card_le_of_norm_sub_cellCenter_le j hR x S hS
  calc conv K g volume x = conv K (fun y => ∑' m, (cell j m).indicator g y) volume x := by
        simp only [tsum_indicator_cell]
    _ = ∑' m, conv K ((cell j m).indicator g) volume x :=
        conv_tsum_of_finset hKc hKs (fun m => (hg m).locallyIntegrable hp1) x T
          fun m hm y hy => Set.indicator_of_notMem (fun hxy => hm (hT m (hnear m y hy hxy))) _
    _ = _ := tsum_congr fun m => (cellCoef_mul_cellAtom_of_indicator hp0 (hg m) K x).symm

/-- **Cell decomposition of a convolution**: `K ⋆ g = ∑_m λ_{j,m} a_{j,m}` at every point, with
finitely many nonzero terms, for a continuous `K` that vanishes outside `closedBall(0, ρ)`. -/
theorem conv_eq_tsum_cellAtom {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ} (hKc : Continuous K)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hKρ : ∀ y, ρ < ‖y‖ → K y = 0) (hg : MemLp g p volume) (j : ℕ)
    (x : V) :
    conv K g volume x = ∑' m, cellCoef p j g m * cellAtom p K j g m x :=
  conv_eq_tsum_cellAtom_of_indicator hp1 hKc hρ hKρ
    (fun m => hg.indicator (measurableSet_cell j m).nullMeasurableSet) x

/-- Cell atoms are continuous for a continuous kernel with compact support. -/
theorem continuous_cellAtom {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ} (hKc : Continuous K)
    (hKs : HasCompactSupport K) (hg : MemLp g p volume) (j : ℕ) (m : Fin (finrank ℝ V) → ℤ) :
    Continuous (cellAtom p K j g m) :=
  continuous_const.mul (hKs.continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ) hKc
    ((hg.indicator (measurableSet_cell j m).nullMeasurableSet).locallyIntegrable hp1))

/-- Cell atoms vanish outside `closedBall(c_{j,m}, (ρ + n) 2^(-j))` if `K` vanishes outside
`closedBall(0, ρ 2^(-j))`. -/
theorem cellAtom_eq_zero {p : ℝ≥0∞} {K g : V → ℂ} {ρ : ℝ} {j : ℕ}
    (hKρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K y = 0) (m : Fin (finrank ℝ V) → ℤ) {x : V}
    (hx : (ρ + finrank ℝ V) / 2 ^ j < ‖x - cellCenter j m‖) : cellAtom p K j g m x = 0 := by
  rw [cellAtom, conv_apply]
  have : ∀ y, K y * (cell j m).indicator g (x - y) = 0 := fun y => by
    by_cases hy : ρ / 2 ^ j < ‖y‖
    · rw [hKρ y hy, zero_mul]
    · have hxy : x - y ∉ cell j m := fun hmem => by
        have h1 := norm_sub_cellCenter_le hmem
        have : ‖x - cellCenter j m‖ ≤ (ρ + finrank ℝ V) / 2 ^ j := by
          calc ‖x - cellCenter j m‖ = ‖(x - y - cellCenter j m) + y‖ := by congr 1; abel
            _ ≤ ‖x - y - cellCenter j m‖ + ‖y‖ := norm_add_le _ _
            _ ≤ finrank ℝ V / 2 ^ j + ρ / 2 ^ j := add_le_add h1 (not_lt.1 hy)
            _ = (ρ + finrank ℝ V) / 2 ^ j := by ring
        linarith
      rw [Set.indicator_of_notMem hxy, mul_zero]
  simp only [this, integral_zero, mul_zero]

/-- `|closedBall(0, ρ 2^(-j))|^t = (ρ^n |B_1|)^t 2^(-jnt)`. -/
theorem volume_closedBall_div_two_pow_rpow {ρ : ℝ} (hρ : 0 ≤ ρ) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    volume (closedBall (0 : V) (ρ / 2 ^ j)) ^ t =
      (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ t *
        dyadicWeight (-(finrank ℝ V * t)) j := by
  rw [volume_closedBall_div_two_pow hρ j, ENNReal.mul_rpow_of_nonneg _ _ ht,
    ENNReal.dyadicWeight_rpow, neg_mul]

/-- **The scaling of cell atoms**: if `K'` vanishes outside `closedBall(0, ρ 2^(-j))` and
`|K'| ≤ A 2^(jn)`, then `|λ_{j,m}⁻¹ (K' ⋆ (1_{P_{j,m}} g))(x)| ≤ A (ρ^n |B_1|)^(1-1/p)`:
the factors `2^(jn)`, `2^(-jn(1-1/p))` and `2^(-jn/p)` cancel. -/
theorem enorm_inv_cellCoef_mul_conv_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {g : V → ℂ}
    (hg : MemLp g p volume) {j : ℕ} (m : Fin (finrank ℝ V) → ℤ) {K' : V → ℂ} {A : ℝ≥0∞}
    (hK' : ∀ y, ‖K' y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hK'ρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K' y = 0) (x : V) :
    ‖(cellCoef p j g m)⁻¹ * conv K' ((cell j m).indicator g) volume x‖ₑ ≤
      A * (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal) := by
  by_cases h0 : cellCoef p j g m = 0
  · rw [h0, inv_zero, zero_mul, eNorm_zero]
    exact zero_le
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  set e := eLpNorm ((cell j m).indicator g) p volume
  set W := dyadicWeight (finrank ℝ V / p.toReal) j
  set X := ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)
  have he : e ≠ ∞ := (hg.indicator (measurableSet_cell j m).nullMeasurableSet).eLpNorm_ne_top
  have he0 : e ≠ 0 := fun he0 => h0 (by simp [cellCoef, e, he0])
  have hconv := enorm_conv_le_of_bound hp1
    (hg.indicator (measurableSet_cell j m).nullMeasurableSet).aestronglyMeasurable hK' hK'ρ x
  rw [volume_closedBall_div_two_pow_rpow hρ j ht] at hconv
  have hW : W⁻¹ * dyadicWeight (finrank ℝ V) j *
      dyadicWeight (-(finrank ℝ V * (1 - 1 / p.toReal))) j = 1 := by
    rw [← ENNReal.dyadicWeight_neg, ← ENNReal.dyadicWeight_add, ← ENNReal.dyadicWeight_add]
    convert ENNReal.dyadicWeight_zero_left j using 2
    ring
  rw [eNorm_mul, eNorm_inv h0, enorm_cellCoef hg j m]
  calc (W * e)⁻¹ * ‖conv K' ((cell j m).indicator g) volume x‖ₑ
      ≤ (W * e)⁻¹ * (A * dyadicWeight (finrank ℝ V) j *
          (X ^ (1 - 1 / p.toReal) * dyadicWeight (-(finrank ℝ V * (1 - 1 / p.toReal))) j) * e) :=
        mul_le_mul' le_rfl hconv
    _ = A * X ^ (1 - 1 / p.toReal) * ((W⁻¹ * dyadicWeight (finrank ℝ V) j *
          dyadicWeight (-(finrank ℝ V * (1 - 1 / p.toReal))) j) * (e⁻¹ * e)) := by
        rw [ENNReal.mul_inv (Or.inl (ENNReal.dyadicWeight_ne_zero _ _))
          (Or.inl (ENNReal.dyadicWeight_ne_top _ _))]
        ring
    _ = A * X ^ (1 - 1 / p.toReal) := by
        rw [hW, ENNReal.inv_mul_cancel he0 he, mul_one, mul_one]

/-- **Cell atoms are bounded**: `|a_{j,m}| ≤ A (ρ^n |B_1|)^(1-1/p)` if `|K| ≤ A 2^(jn)` and `K`
vanishes outside `closedBall(0, ρ 2^(-j))`. -/
theorem enorm_cellAtom_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ} (hg : MemLp g p volume)
    {j : ℕ} (m : Fin (finrank ℝ V) → ℤ) {A : ℝ≥0∞}
    (hK : ∀ y, ‖K y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K y = 0) (x : V) :
    ‖cellAtom p K j g m x‖ₑ ≤
      A * (ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal) :=
  enorm_inv_cellCoef_mul_conv_le hp1 hg m hK hρ hKρ x

/-- **Differences of cell atoms**: if `K` is continuous with `|K| ≤ A 2^(jn)`,
`|Δ_h^r K| ≤ A 2^(jn) min(1, (2^j ‖h‖)^r)` and `K = 0` outside `closedBall(0, ρ 2^(-j))`, then
`|Δ_h^r a_{j,m}| ≤ 2^r A ((ρ + r)^n |B_1|)^(1-1/p) min(1, (2^j ‖h‖)^r)`. For `‖h‖ ≤ 2^(-j)` the
kernel `Δ_h^r K` of `Δ_h^r a_{j,m}` vanishes outside `closedBall(0, (ρ + r) 2^(-j))`; for larger
`h` the
bound `2^r sup |a_{j,m}|` suffices. -/
theorem enorm_higherDiff_cellAtom_le {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ} (hKc : Continuous K)
    (hg : MemLp g p volume) {j : ℕ} (m : Fin (finrank ℝ V) → ℤ) {A : ℝ≥0∞} {r : ℕ}
    (hK : ∀ y, ‖K y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j)
    (hKr : ∀ h y, ‖(fwdDiff h)^[r] K y‖ₑ ≤
      A * dyadicWeight (finrank ℝ V) j * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hKρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K y = 0) (h x : V) :
    ‖(fwdDiff h)^[r] (cellAtom p K j g m) x‖ₑ ≤
      2 ^ r * A * (ENNReal.ofReal ((ρ + r) ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
        (1 - 1 / p.toReal) * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)) := by
  have hKs : HasCompactSupport K := HasCompactSupport.intro (isCompact_closedBall 0 (ρ / 2 ^ j))
    fun y hy => hKρ y (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  have hρr : 0 ≤ ρ + r := add_nonneg hρ (Nat.cast_nonneg r)
  set Y := ENNReal.ofReal ((ρ + r) ^ finrank ℝ V) * volume (ball (0 : V) 1)
  set X := ENNReal.ofReal (ρ ^ finrank ℝ V) * volume (ball (0 : V) 1)
  set M := min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ))
  have hXY : X ^ (1 - 1 / p.toReal) ≤ Y ^ (1 - 1 / p.toReal) :=
    ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ hρ (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) _)) le_rfl) ht
  by_cases hh : ‖h‖ ≤ 1 / 2 ^ j
  · have hconv : (fwdDiff h)^[r] (cellAtom p K j g m) x = (cellCoef p j g m)⁻¹ *
        conv ((fwdDiff h)^[r] K) ((cell j m).indicator g) volume x := by
      rw [show cellAtom p K j g m =
          (cellCoef p j g m)⁻¹ • conv K ((cell j m).indicator g) volume from rfl,
        fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul,
        higherDiff_conv_apply (fun v x => integrable_translate_mul_of_locallyIntegrable hKc hKs
          ((hg.indicator (measurableSet_cell j m).nullMeasurableSet).locallyIntegrable hp1) v x)]
    have hsupp : ∀ y, (ρ + r) / 2 ^ j < ‖y‖ → (fwdDiff h)^[r] K y = 0 := fun y hy => by
      rw [higherDiff_apply]
      refine Finset.sum_eq_zero fun l hl => ?_
      rw [hKρ _ ?_, mul_zero]
      have hl' : (l : ℝ) ≤ r := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have h2 : ‖(l : ℝ) • h‖ ≤ r / 2 ^ j := by
        rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg l)]
        calc (l : ℝ) * ‖h‖ ≤ r * (1 / 2 ^ j) :=
              mul_le_mul hl' hh (norm_nonneg h) (Nat.cast_nonneg r)
          _ = r / 2 ^ j := by ring
      have h3 : ‖y‖ - ‖(l : ℝ) • h‖ ≤ ‖y + (l : ℝ) • h‖ := by
        have := norm_sub_norm_le y (-((l : ℝ) • h))
        rw [sub_neg_eq_add, norm_neg] at this
        linarith
      have h4 : ρ / 2 ^ j = (ρ + r) / 2 ^ j - r / 2 ^ j := by ring
      linarith
    rw [hconv]
    refine (enorm_inv_cellCoef_mul_conv_le hp1 hg m (A := A * M)
      (fun y => (hKr h y).trans_eq (by ring)) hρr hsupp x).trans ?_
    calc A * M * Y ^ (1 - 1 / p.toReal) = 1 * A * Y ^ (1 - 1 / p.toReal) * M := by ring
      _ ≤ 2 ^ r * A * Y ^ (1 - 1 / p.toReal) * M := by
          gcongr
          exact one_le_pow₀ one_le_two
  · have hmin : M = 1 := by
      refine min_eq_left ?_
      have h1 : 1 ≤ 2 ^ j * ‖h‖ := by
        rw [not_le, div_lt_iff₀ (by positivity)] at hh
        linarith
      calc (1 : ℝ≥0∞) = 1 ^ (r : ℝ) := (ENNReal.one_rpow _).symm
        _ ≤ ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ) :=
            ENNReal.rpow_le_rpow (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1)
              (Nat.cast_nonneg r)
    rw [hmin, mul_one]
    refine (enorm_higherDiff_le_of_bound (fun y => enorm_cellAtom_le hp1 hg m hK hρ hKρ y) r h
      x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hXY)

variable (V) in
/-- The constant of the cell atoms as regular atoms:
`2^r A ((ρ + r)^n |B_1|)^(1-1/p) ((r + 1) (ρ + n)^n |B_1|)^(1/p)`. -/
noncomputable def cellAtomConst (p A : ℝ≥0∞) (ρ : ℝ) (r : ℕ) : ℝ≥0∞ :=
  2 ^ r * A * (ENNReal.ofReal ((ρ + r) ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
    (1 - 1 / p.toReal) * (((r + 1 : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal ((ρ + finrank ℝ V) ^ finrank ℝ V) * volume (ball (0 : V) 1))) ^ (1 / p.toReal)

/-- The constant of the cell atoms is finite. -/
theorem cellAtomConst_ne_top {p : ℝ≥0∞} (hp1 : 1 ≤ p) {A : ℝ≥0∞} (hA : A ≠ ∞) (ρ : ℝ) (r : ℕ) :
    cellAtomConst V p A ρ r ≠ ∞ := by
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  have hball : volume (ball (0 : V) 1) ≠ ∞ := measure_ball_lt_top.ne
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA)
    (ENNReal.rpow_ne_top_of_nonneg ht (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hball)))
    (ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one ENNReal.toReal_nonneg)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hball)))

/-- **Cell atoms are regular atoms** of order and exponent `r`, with radius factor `ρ + n` and the
constant `Rd.cellAtomConst`, for a continuous kernel `K` with `|Δ_h^l K| ≤ A 2^(jn) min(1,
(2^j ‖h‖)^l)` (`l = 0, r`) that vanishes outside `closedBall(0, ρ 2^(-j))`. -/
theorem isRegularAtom_cellAtom {p : ℝ≥0∞} (hp1 : 1 ≤ p) {K g : V → ℂ} (hKc : Continuous K)
    (hg : MemLp g p volume) {j : ℕ} (m : Fin (finrank ℝ V) → ℤ) {A : ℝ≥0∞} {r : ℕ}
    (hK : ∀ y, ‖K y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j)
    (hKr : ∀ h y, ‖(fwdDiff h)^[r] K y‖ₑ ≤
      A * dyadicWeight (finrank ℝ V) j * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (r : ℝ)))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hKρ : ∀ y, ρ / 2 ^ j < ‖y‖ → K y = 0) :
    IsRegularAtom p r r (ρ + finrank ℝ V) (cellAtomConst V p A ρ r) j (cellCenter j m)
      (cellAtom p K j g m) := by
  have hKs : HasCompactSupport K := HasCompactSupport.intro (isCompact_closedBall 0 (ρ / 2 ^ j))
    fun y hy => hKρ y (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  have hsup : ∀ x, ‖cellAtom p K j g m x‖ₑ ≤ 2 ^ r * A *
      (ENNReal.ofReal ((ρ + r) ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^ (1 - 1 / p.toReal) :=
    fun x => by
      refine (enorm_cellAtom_le hp1 hg m hK hρ hKρ x).trans ?_
      rw [mul_assoc]
      refine le_mul_of_one_le_of_le (one_le_pow₀ one_le_two) (mul_le_mul' le_rfl ?_)
      exact ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ hρ (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) _)) le_rfl) ht
  unfold cellAtomConst
  exact isRegularAtom_of_pointwise (add_nonneg hρ (Nat.cast_nonneg _))
    (continuous_cellAtom hp1 hKc hKs hg j m).aestronglyMeasurable
    (fun x hx => cellAtom_eq_zero hKρ m hx) hsup
    (fun h x => enorm_higherDiff_cellAtom_le hp1 hKc hg m hK hKr hρ hKρ h x)

/-! ### The coefficients of the cells -/

/-- **The coefficients of one level**: `‖λ_{j,·}‖_{ℓ_p} = 2^(jn/p) ‖g‖_p`, since the cells
partition `V`. -/
theorem levelNorm_cellCoef {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : V → ℂ}
    (hg : MemLp g p volume) (j : ℕ) :
    levelNorm p (cellCoef p j g) = dyadicWeight (finrank ℝ V / p.toReal) j * eLpNorm g p volume
      := by
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [levelNorm_eq_tsum hp0 hp]
  simp_rw [enorm_cellCoef hg j, ENNReal.mul_rpow_of_nonneg _ _ hpos.le]
  rw [ENNReal.tsum_mul_left, ← eLpNorm_rpow_eq_tsum_cell hp0 hp hg.aestronglyMeasurable j,
    ← ENNReal.mul_rpow_of_nonneg _ _ hpos.le, one_div, ENNReal.rpow_rpow_inv hpos.ne']

/-- **The coefficient quasi-norm of cell coefficients**:
`‖λ‖_{b^s_{p,q}} = ‖(2^(js) ‖g_j‖_p)_j‖_{ℓ_q}` for the cell coefficients of `g_j ∈ L_p`. -/
theorem coeffNorm_cellCoef {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : ℕ → V → ℂ}
    (hg : ∀ j, MemLp (g j) p volume) (s : ℝ) (q : ℝ≥0∞) :
    coeffNorm p (finrank ℝ V) s q (fun j => cellCoef p j (g j)) =
      lqNorm q (fun j => dyadicWeight s j * eLpNorm (g j) p volume) := by
  rw [coeffNorm]
  congr 1
  funext j
  rw [levelNorm_cellCoef hp0 hp (hg j) j, ← mul_assoc, ← ENNReal.dyadicWeight_add, sub_add_cancel]

/-! ### The dual kernels -/

namespace LocalMeansBump

variable (b : LocalMeansBump V)

/-- **Pointwise bounds of the dual kernels**: for every order `r` there is `A < ∞` with
`|Δ_h^l η_j| ≤ A 2^(jn) min(1, (2^j ‖h‖)^l)` for `l ≤ r`, from the bounded derivatives of the
moment kernel (`Rd.enorm_higherDiff_le_of_iteratedFDeriv`) and the scaling of differences of
dilations (`Rd.higherDiff_dilate`). -/
theorem exists_higherDiff_dual_bound (L r : ℕ) : ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ l ≤ r, ∀ j h y,
    ‖(fwdDiff h)^[l] (b.dual L j) y‖ₑ ≤
      A * dyadicWeight (finrank ℝ V) j * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ)) := by
  obtain ⟨C, hC⟩ := exists_iteratedFDeriv_bound (b.contDiff_momentKernel L)
    (b.hasCompactSupport_momentKernel L) r
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le r) 0)
  have hscaled : ∀ l ≤ r, ∀ i j : ℕ, i ≤ j → ∀ h y, ‖(fwdDiff h)^[l] (b.scaled L i) y‖ₑ ≤
      ENNReal.ofReal (2 ^ r * C) * dyadicWeight (finrank ℝ V) j *
        min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ)) := by
    intro l hl i j hij h y
    rw [scaled, higherDiff_dilate, dilate, eNorm_mul]
    have h1 := enorm_higherDiff_le_of_iteratedFDeriv (b.contDiff_momentKernel L) (r := l) (j := 0)
      hC0 (fun l' hl' x => by simpa using hC l' (hl'.trans hl) x) ((2 : ℝ) ^ i • h)
      ((2 : ℝ) ^ i • y)
    have h2 : ‖((((2 : ℝ) ^ i) ^ finrank ℝ V : ℝ) : ℂ)‖ₑ ≤ dyadicWeight (finrank ℝ V) j := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        ENNReal.ofReal_two_pow_pow]
      exact ENNReal.dyadicWeight_mono (Nat.cast_nonneg _) hij
    have h3 : min 1 (ENNReal.ofReal (2 ^ 0 * ‖(2 : ℝ) ^ i • h‖) ^ (l : ℝ)) ≤
        min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ)) := by
      refine min_le_min le_rfl (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ?_)
        (Nat.cast_nonneg l))
      rw [pow_zero, one_mul, norm_smul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hij) (norm_nonneg h)
    have h4 : ENNReal.ofReal (2 ^ l * C) ≤ ENNReal.ofReal (2 ^ r * C) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ one_le_two hl) hC0)
    calc ‖((((2 : ℝ) ^ i) ^ finrank ℝ V : ℝ) : ℂ)‖ₑ *
          ‖(fwdDiff ((2 : ℝ) ^ i • h))^[l] (momentKernel b.toFun L) ((2 : ℝ) ^ i • y)‖ₑ
        ≤ dyadicWeight (finrank ℝ V) j * (ENNReal.ofReal (2 ^ r * C) *
            min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ))) :=
          mul_le_mul' h2 (h1.trans (mul_le_mul' h4 h3))
      _ = _ := by ring
  refine ⟨2 * ENNReal.ofReal (2 ^ r * C), ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
    fun l hl j h y => ?_⟩
  cases j with
  | zero =>
    refine (hscaled l hl 0 0 le_rfl h y).trans ?_
    gcongr
    exact le_mul_of_one_le_left' one_le_two
  | succ j =>
    rw [show b.dual L (j + 1) = b.scaled L (j + 1) + b.scaled L j from rfl, fwdDiff_iter_add,
      Pi.add_apply]
    refine (eNorm_add_le _ _).trans ?_
    calc ‖(fwdDiff h)^[l] (b.scaled L (j + 1)) y‖ₑ + ‖(fwdDiff h)^[l] (b.scaled L j) y‖ₑ
        ≤ ENNReal.ofReal (2 ^ r * C) * dyadicWeight (finrank ℝ V) (j + 1) *
            min 1 (ENNReal.ofReal (2 ^ (j + 1) * ‖h‖) ^ (l : ℝ)) +
          ENNReal.ofReal (2 ^ r * C) * dyadicWeight (finrank ℝ V) (j + 1) *
            min 1 (ENNReal.ofReal (2 ^ (j + 1) * ‖h‖) ^ (l : ℝ)) :=
          add_le_add (hscaled l hl _ _ le_rfl h y) (hscaled l hl _ _ (Nat.le_succ j) h y)
      _ = _ := by ring

/-- **Uniform pointwise bounds of the cell atoms**: for every order `r` there is `A < ∞` such that
the cell atoms of `η_j ⋆ g`, `g ∈ L_p`, satisfy `|Δ_h^l a_{j,m}| ≤ A min(1, (2^j ‖h‖)^l)` for all
`l ≤ r`, `j`, `m`. -/
theorem exists_cellAtom_pointwise_bound {p : ℝ≥0∞} (hp1 : 1 ≤ p) (L r : ℕ) :
    ∃ A : ℝ≥0∞, A ≠ ∞ ∧ ∀ (j : ℕ) {g : V → ℂ}, MemLp g p volume → ∀ m, ∀ l ≤ r, ∀ h x,
      ‖(fwdDiff h)^[l] (cellAtom p (b.dual L j) j g m) x‖ₑ ≤
        A * min 1 (ENNReal.ofReal (2 ^ j * ‖h‖) ^ (l : ℝ)) := by
  obtain ⟨A, hA, hb⟩ := b.exists_higherDiff_dual_bound L r
  have ht : 0 ≤ 1 - 1 / p.toReal := one_sub_one_div_toReal_nonneg hp1
  set ρ := 2 * (L : ℝ) * b.radius
  have hρ : 0 ≤ ρ := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg
  refine ⟨2 ^ r * A * (ENNReal.ofReal ((ρ + r) ^ finrank ℝ V) * volume (ball (0 : V) 1)) ^
      (1 - 1 / p.toReal), ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA)
        (ENNReal.rpow_ne_top_of_nonneg ht (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          measure_ball_lt_top.ne)), fun j g hg m l hl h x => ?_⟩
  have hK : ∀ y, ‖b.dual L j y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j := fun y => by
    simpa using hb 0 (Nat.zero_le r) j 0 y
  have h1 := enorm_higherDiff_cellAtom_le hp1 (b.continuous_dual L j) hg m hK (hb l hl j) hρ
    (fun y hy => b.dual_eq_zero_of_lt L j hy) h x
  refine h1.trans (mul_le_mul' ?_ le_rfl)
  refine mul_le_mul' (mul_le_mul' (pow_le_pow_right₀ one_le_two hl) le_rfl)
    (ENNReal.rpow_le_rpow (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (add_nonneg hρ (Nat.cast_nonneg l)) ?_ _)) le_rfl) ht)
  exact add_le_add_right (Nat.cast_le.2 hl) ρ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Cell-atom decomposition of the local-means terms**. This gives the analysis step in
`Rd.LocalMeansBump.besov_iff_atomic`. For every order `r` there is `C < ∞` such that for
every `F ∈ L_p` the terms of the reproducing formula
`F = ∑_j η_j ⋆ (k_j ⋆ F)` (`Rd.LocalMeansBump.tendsto_sum_dual_localMean`) are
`η_j ⋆ (k_j ⋆ F) = ∑_m λ_{j,m} a_{j,m}` with the cell atoms, regular atoms of order and exponent
`r` with radius factor `2LR + n` and constant `C`; the coefficients have
`‖λ‖_{b^s_{p,q}} = ‖(2^(js) ‖k_j ⋆ F‖_p)_j‖_{ℓ_q}`, the local means quasi-norm. -/
theorem atomic_decomposition (hp : p ≠ ∞) (L r : ℕ) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ F : Lp ℂ p (volume : Measure V),
      (∀ j m, IsRegularAtom p r r (2 * L * b.radius + finrank ℝ V) C j (cellCenter j m)
        (cellAtom p (b.dual L j) j (b.localMean hp L j F) m)) ∧
      (∀ j, ∀ᵐ x ∂volume, convLp hp (b.integrable_dual L j) (b.localMean hp L j F) x =
        ∑' m, cellCoef p j (b.localMean hp L j F) m *
          cellAtom p (b.dual L j) j (b.localMean hp L j F) m x) ∧
      ∀ s q, coeffNorm p (finrank ℝ V) s q (fun j => cellCoef p j (b.localMean hp L j F)) =
        b.localMeansNorm hp L s q F := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  obtain ⟨A, hA, hb⟩ := b.exists_higherDiff_dual_bound L r
  have hρ : 0 ≤ 2 * (L : ℝ) * b.radius :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L)) b.radius_nonneg
  have hK : ∀ j y, ‖b.dual L j y‖ₑ ≤ A * dyadicWeight (finrank ℝ V) j := fun j y => by
    simpa using hb 0 (Nat.zero_le r) j 0 y
  refine ⟨cellAtomConst V p A (2 * L * b.radius) r, cellAtomConst_ne_top hp1 hA _ r,
    fun F => ⟨fun j m => ?_, fun j => ?_, fun s q => ?_⟩⟩
  · exact isRegularAtom_cellAtom hp1 (b.continuous_dual L j) (Lp.memLp _) m (hK j)
      (hb r le_rfl j) hρ fun y hy => b.dual_eq_zero_of_lt L j hy
  · filter_upwards [convLp_apply_ae hp (b.integrable_dual L j) (b.localMean hp L j F)] with x hx
    rw [hx]
    exact conv_eq_tsum_cellAtom hp1 (b.continuous_dual L j) (by positivity)
      (fun y hy => b.dual_eq_zero_of_lt L j hy) (Lp.memLp _) j x
  · rw [coeffNorm_cellCoef hp0 hp (fun j => Lp.memLp _), localMeansNorm]
    simp_rw [Lp.eNorm_def]

include b in
/-- **Atomic characterisation of Besov spaces** with regular atoms and bounded overlap.
For `1 ≤ p < ∞`, `0 < s < L` and `1 ≤ q ≤ ∞`, `F ∈ B^s_{p,q}(V)` iff `F = ∑_j f_j` in `L_p` with
`f_j = ∑_m λ_{j,m} a_{j,m}` for regular atoms of order and exponent `L` whose centres have
bounded overlap, and `‖λ‖_{b^s_{p,q}} < ∞`. The atoms of `F` are its cell atoms
(`Rd.LocalMeansBump.atomic_decomposition`); the converse is the synthesis
`Rd.modNorm_le_coeffNorm`. The bump `b` only enters the proof. -/
theorem besov_iff_atomic (hp : p ≠ ∞) {L : ℕ} (hL : 1 ≤ L) {s : ℝ} (hs : 0 < s) (hsL : s < L)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (F : Lp ℂ p (volume : Measure V)) :
    ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p L F k) < ∞ ↔
      ∃ (d : ℝ) (C : ℝ≥0∞) (N : ℕ) (c : ℕ → (Fin (finrank ℝ V) → ℤ) → V)
        (a : ℕ → (Fin (finrank ℝ V) → ℤ) → V → ℂ) (coef : ℕ → (Fin (finrank ℝ V) → ℤ) → ℂ)
        (f : ℕ → Lp ℂ p (volume : Measure V)), C ≠ ∞ ∧
        (∀ j m, IsRegularAtom p L L d C j (c j m) (a j m)) ∧
        (∀ j x (S : Finset (Fin (finrank ℝ V) → ℤ)),
          (∀ m ∈ S, coef j m ≠ 0 ∧ ‖x - c j m‖ ≤ (d + L) / 2 ^ j) → S.card ≤ N) ∧
        (∀ j, ∀ᵐ x ∂volume, f j x = ∑' m, coef j m * a j m x) ∧
        Tendsto (fun J => ∑ j ∈ Finset.range (J + 1), f j) atTop (𝓝 F) ∧
        coeffNorm p (finrank ℝ V) s q coef < ∞ := by
  have hp1 : 1 ≤ p := Fact.out
  constructor
  · intro hF
    obtain ⟨C, hC, hdec⟩ := b.atomic_decomposition hp L L
    obtain ⟨hatom, hsum, hcoef⟩ := hdec F
    have hd : 0 ≤ 2 * (L : ℝ) * b.radius + finrank ℝ V + L :=
      add_nonneg (add_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg L))
        b.radius_nonneg) (Nat.cast_nonneg _)) (Nat.cast_nonneg L)
    refine ⟨2 * L * b.radius + finrank ℝ V, C,
      ⌈(2 * (2 * L * b.radius + finrank ℝ V + L) + 2) ^ finrank ℝ V⌉₊,
      fun j m => cellCenter j m, fun j => cellAtom p (b.dual L j) j (b.localMean hp L j F),
      fun j => cellCoef p j (b.localMean hp L j F),
      fun j => convLp hp (b.integrable_dual L j) (b.localMean hp L j F), hC, hatom,
      fun j x S hS => card_le_of_norm_sub_cellCenter_le j hd x S fun m hm => (hS m hm).2, hsum,
      b.tendsto_sum_dual_localMean hp hL F, ?_⟩
    rw [hcoef]
    exact (b.localMeansNorm_le hp L s hq F).trans_lt
      (ENNReal.mul_lt_top (b.upperConst_ne_top L s).lt_top hF)
  · rintro ⟨d, C, N, c, a, coef, f, hC, ha, hN, hf, hFt, hcoef⟩
    exact (modNorm_le_coeffNorm hp c a coef hN ha hf hFt hs hsL hq).trans_lt
      (ENNReal.mul_lt_top (atomSynthConst_ne_top hp1 N hC L hs hsL).lt_top hcoef)

end LocalMeansBump

end Rd
