/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.TorusBackgroundMultiplierCell
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# The background multiplier `β_n = F(s_n)`

`eq:background-multiplier` (in the proof of `prop:background-resolvent`) defines

`s_n(y) = Σ_m r_m ϑ(|y - p_m|/R_m)`,  `r_m = K_n/K_m = ℓ_m/ℓ_n`,  `β_n = F(s_n)`.

Since `s_n = (2πK_n/τ)(u^ax)_3` is the constructed added axial velocity renormalised,
`β_n` carries **no `τ`**; this is what makes the order "`τ` first, then `K_0`" of
`eq:axial-separation-choice` and `eq:background-diffusion-small` non-circular.

The multiplier is assembled here as the placed disjoint-support series

`β_n + 1 = Σ_m (F(r_m ϑ_m) + 1)`

of `Global/TorusBackgroundMultiplierCell.lean`, whose summands vanish off their own buffer
discs; no `W^{1,∞}` chain rule is used.  The module proves
`eq:background-multiplier-bounds` in the explicit form

* `|β_n| ≤ 1` (in fact pointwise, from `|F| ≤ 1` on `[0,∞)`), and
* `‖∂_j β_n‖_∞ ≤ 3 ‖ϑ'‖_∞ R_0 / ℓ_n`, i.e. `√ε ‖∇_⊥ β_n‖_∞ ≤ 3√2 ‖ϑ'‖_∞ √δ_+ d(K_0)` once
  `√ε ≤ √δ_+ ℓ_n` and `d(K_0) = sup_m ℓ_m/R_m = R_0`,

together with the pointwise identification `β_n = F((2πK_n/τ)(u^ax)_3)`, which feeds the phase
inequality `eq:background-phase-positive` through the indicator bridge of
`Global/BackgroundMultiplierScalarAlgebra.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-- The paper's ratio `r_m = K_n/K_m = ℓ_m/ℓ_n` (proof of `prop:background-resolvent`). -/
def cellRatio (f : ScaleFamily r) (n m : ℕ) : ℝ := f.ell m / f.ell n

/-- Ratios are positive. -/
theorem cellRatio_pos (f : ScaleFamily r) (n m : ℕ) : 0 < f.cellRatio n m :=
  div_pos (f.ell_pos m) (f.ell_pos n)

/-- Ratios are nonnegative. -/
theorem cellRatio_nonneg (f : ScaleFamily r) (n m : ℕ) : 0 ≤ f.cellRatio n m :=
  (f.cellRatio_pos n m).le

/-- The selected cell has ratio one, so `s_n = 1` and `β_n = F(1) = 0` on its own core. -/
@[simp] theorem cellRatio_self (f : ScaleFamily r) (n : ℕ) : f.cellRatio n n = 1 :=
  div_self (f.ell_pos n).ne'

/-- The ratios are summable: `Σ_m r_m = (Σ_m ℓ_m)/ℓ_n`. -/
theorem summable_cellRatio (f : ScaleFamily r) (n : ℕ) :
    Summable (f.cellRatio n) := by
  have h : f.cellRatio n = fun m ↦ (f.ell n)⁻¹ * f.ell m := by
    funext m
    rw [cellRatio, div_eq_inv_mul]
  rw [h]
  exact f.summable_ell.mul_left _

/-- `r_m / R_m = R_m / ℓ_n`, the quantity `d(K_0)/ℓ_n` of the gradient bound
(`eq:background-multiplier-bounds`). -/
theorem cellRatio_div_bufferRadius (f : ScaleFamily r) (n m : ℕ) :
    f.cellRatio n m / f.bufferRadius m = f.bufferRadius m / f.ell n := by
  have hR := f.bufferRadius_pos m
  have hl := f.ell_pos n
  rw [cellRatio]
  field_simp
  nlinarith [f.bufferRadius_sq m]

/-- `r_m / R_m ≤ R_0 / ℓ_n`: the paper's `d(K_0) = sup_m ℓ_m/R_m = √ℓ_0`. -/
theorem cellRatio_div_bufferRadius_le (f : ScaleFamily r) (n m : ℕ) :
    f.cellRatio n m / f.bufferRadius m ≤ f.bufferRadius 0 / f.ell n := by
  rw [f.cellRatio_div_bufferRadius n m, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (f.bufferRadius_le_bufferRadius_zero m)
    (inv_nonneg.mpr (f.ell_pos n).le)

/-- The sequence `m ↦ r_m ‖ϑ'‖_∞/R_m` of gradient scales is summable. -/
theorem summable_cellRatio_div_bufferRadius (f : ScaleFamily r) (n : ℕ) :
    Summable (fun m ↦ f.cellRatio n m / f.bufferRadius m) := by
  have h : (fun m ↦ f.cellRatio n m / f.bufferRadius m) =
      fun m ↦ (f.ell n)⁻¹ * f.bufferRadius m := by
    funext m
    rw [f.cellRatio_div_bufferRadius n m, div_eq_inv_mul]
  rw [h]
  exact f.summable_bufferRadius.mul_left _

/-- **`s_n = (2πK_n/τ)(u^ax)_3`**, at the level of amplitudes:
`2πK_n a_m = τ r_m` (the paper's `2πK_n ℓ_m = 2π r_m` before
`eq:background-local-coefficients`; with `ℓ_m = k_*/K_m` it reads `2πK_n ℓ_m = N r_m`). -/
theorem axialAmplitude_eq_tau_mul_cellRatio (f : ScaleFamily r) (tau : ℝ)
    (n m : ℕ) :
    2 * Real.pi * (f.fourierIndex n : ℝ) * f.axialAmplitude tau m =
      tau * f.cellRatio n m := by
  have hmatch := f.axial_wavenumber_match n
  have hwave : p.wavenumber ≠ 0 := p.wavenumber_pos.ne'
  have hell : f.ell n ≠ 0 := (f.ell_pos n).ne'
  rw [axialAmplitude, cellRatio]
  field_simp
  linear_combination (tau * f.ell m) * hmatch

/-! ## The constant function one -/

/-- The constant function `1` as an essentially bounded transverse scalar. -/
def transverseConstOneLInf : TransverseScalarLInf :=
  (memLp_top_const (1 : ℂ)).toLp (fun _ ↦ (1 : ℂ))

/-- Its representative is the constant one. -/
theorem transverseConstOneLInf_coe_ae :
    (transverseConstOneLInf : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] fun _ ↦ (1 : ℂ) :=
  MemLp.coeFn_toLp _

/-- The constant one is the zero-frequency Fourier monomial in `L²`. -/
theorem transverseScalarLInfToL2_transverseConstOne :
    transverseScalarLInfToL2 transverseConstOneLInf = transverseMonomialL2 0 := by
  apply Lp.ext
  filter_upwards [transverseScalarLInfToL2_coe_ae transverseConstOneLInf,
    transverseConstOneLInf_coe_ae, transverseMonomialL2_coe_ae 0] with q h1 h2 h3
  rw [h1, h2, h3, UnitAddTorus.mFourier_zero]
  rfl

/-- The Fourier coefficients of the constant one vanish at every nonzero frequency. -/
theorem transverseScalarCoeffCLM_transverseConstOne_of_ne
    {ν : TransverseFrequency} (hν : ν ≠ 0) :
    transverseScalarCoeffCLM ν
      (transverseScalarLInfToL2 transverseConstOneLInf) = 0 := by
  rw [transverseScalarLInfToL2_transverseConstOne]
  change (transverseScalarFourierBasis.repr (transverseScalarFourierBasis 0)) ν = 0
  rw [HilbertBasis.repr_self]
  simp [hν]

/-- The constant one has vanishing transverse Fourier weak derivative. -/
theorem transverseFourierDerivMultiplier_mul_transverseConstOne (j : Fin 2)
    (ν : TransverseFrequency) :
    transverseFourierDerivMultiplier j ν *
        transverseScalarCoeffCLM ν
          (transverseScalarLInfToL2 transverseConstOneLInf) = 0 := by
  by_cases hν : ν = 0
  · subst hν
    simp [transverseFourierDerivMultiplier]
  · rw [transverseScalarCoeffCLM_transverseConstOne_of_ne hν, mul_zero]

namespace TorusCellPlacement

variable {supportRadius : ℝ} (P : TorusCellPlacement (r := r) supportRadius)

/-! ## The placed disjoint-support series -/

/-- The `m`-th summand `F(r_m ϑ_m) + 1` of `β_n + 1`, on the torus. -/
def backgroundShiftedCellTorus (n m : ℕ) : TransverseTorus → ℂ :=
  P.backgroundCellTorus (P.scaleFamily.cellRatio n m) m

/-- Its displayed transverse derivative. -/
def backgroundShiftedCellTorusDeriv (n m : ℕ) (j : Fin 2) : TransverseTorus → ℂ :=
  P.backgroundCellTorusDeriv (P.scaleFamily.cellRatio n m) m j

/-- Distinct placed torus buffer discs are disjoint, in either order. -/
theorem notMem_torusBufferDisk_of_mem_of_ne' {m k : ℕ} (hmk : m ≠ k)
    {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk k) :
    q ∉ P.torusBufferDisk m := by
  intro hm
  rcases lt_or_gt_of_ne hmk with hlt | hgt
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hlt)) hm hq
  · exact (Set.disjoint_left.mp (P.disjoint_torusBufferDisk hgt)) hq hm

/-- The summand vanishes on the buffer disc of a different cell. -/
theorem backgroundShiftedCellTorus_eq_zero_on_other_buffer (n : ℕ) {m k : ℕ}
    (hmk : m ≠ k) {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk k) :
    P.backgroundShiftedCellTorus n m q = 0 :=
  P.backgroundCellTorus_eq_zero_of_not_mem_buffer _ m
    (P.notMem_torusBufferDisk_of_mem_of_ne' hmk hq)

/-- The displayed derivative vanishes on the buffer disc of a different cell. -/
theorem backgroundShiftedCellTorusDeriv_eq_zero_on_other_buffer (n : ℕ) {m k : ℕ}
    (hmk : m ≠ k) (j : Fin 2) {q : TransverseTorus}
    (hq : q ∈ P.torusBufferDisk k) :
    P.backgroundShiftedCellTorusDeriv n m j q = 0 :=
  P.backgroundCellTorusDeriv_eq_zero_of_not_mem_buffer _ m j
    (P.notMem_torusBufferDisk_of_mem_of_ne' hmk hq)

/-- The pointwise value of the placed series `β_n + 1 = Σ_m (F(r_m ϑ_m) + 1)`. -/
def backgroundShiftedGlobalTorus (n : ℕ) (q : TransverseTorus) : ℂ :=
  ∑' m : ℕ, P.backgroundShiftedCellTorus n m q

/-- The pointwise value of the differentiated series. -/
def backgroundShiftedGlobalTorusDeriv (n : ℕ) (j : Fin 2) (q : TransverseTorus) : ℂ :=
  ∑' m : ℕ, P.backgroundShiftedCellTorusDeriv n m j q

/-- Inside the buffer disc of cell `k` the series reduces to that single summand. -/
theorem backgroundShiftedGlobalTorus_eq_cell_of_mem_buffer (n : ℕ) {k : ℕ}
    {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk k) :
    P.backgroundShiftedGlobalTorus n q = P.backgroundShiftedCellTorus n k q := by
  unfold backgroundShiftedGlobalTorus
  exact tsum_eq_single k fun m hmk ↦
    P.backgroundShiftedCellTorus_eq_zero_on_other_buffer n hmk hq

/-- Inside the buffer disc of cell `k` the differentiated series reduces to that summand. -/
theorem backgroundShiftedGlobalTorusDeriv_eq_cell_of_mem_buffer (n : ℕ) (j : Fin 2)
    {k : ℕ} {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk k) :
    P.backgroundShiftedGlobalTorusDeriv n j q =
      P.backgroundShiftedCellTorusDeriv n k j q := by
  unfold backgroundShiftedGlobalTorusDeriv
  exact tsum_eq_single k fun m hmk ↦
    P.backgroundShiftedCellTorusDeriv_eq_zero_on_other_buffer n hmk j hq

/-- Off every buffer disc the series vanishes, so `β_n = -1 = F(0)` there. -/
theorem backgroundShiftedGlobalTorus_eq_zero_of_outside_buffers (n : ℕ)
    {q : TransverseTorus} (hq : ∀ k : ℕ, q ∉ P.torusBufferDisk k) :
    P.backgroundShiftedGlobalTorus n q = 0 := by
  unfold backgroundShiftedGlobalTorus
  simp_rw [backgroundShiftedCellTorus,
    P.backgroundCellTorus_eq_zero_of_not_mem_buffer _ _ (hq _)]
  exact tsum_zero

/-- Off every buffer disc the differentiated series vanishes. -/
theorem backgroundShiftedGlobalTorusDeriv_eq_zero_of_outside_buffers (n : ℕ)
    (j : Fin 2) {q : TransverseTorus} (hq : ∀ k : ℕ, q ∉ P.torusBufferDisk k) :
    P.backgroundShiftedGlobalTorusDeriv n j q = 0 := by
  unfold backgroundShiftedGlobalTorusDeriv
  simp_rw [backgroundShiftedCellTorusDeriv,
    P.backgroundCellTorusDeriv_eq_zero_of_not_mem_buffer _ _ j (hq _)]
  exact tsum_zero

/-- Every value of one placed summand is `Ψ_ρ(t)` for some `t ∈ [0,1]`: either the cut-off
value at the canonical representative, or `t = 0` off the buffer. -/
theorem exists_backgroundCellTorus_eq (ρ : ℝ) (m : ℕ) (q : TransverseTorus) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      P.backgroundCellTorus ρ m q = ((backgroundCellProfile ρ t : ℝ) : ℂ) := by
  classical
  by_cases hq : q ∈ P.torusBufferDisk m
  · refine ⟨P.axialCellCutoff m (P.periodizationRepresentative m q hq),
      (P.axialCellCutoff_mem_Icc m _).1, (P.axialCellCutoff_mem_Icc m _).2, ?_⟩
    rw [backgroundCellTorus, torusPeriodizedExtension, dite_eq_left hq]
    rfl
  · exact ⟨0, le_rfl, zero_le_one, by
      rw [P.backgroundCellTorus_eq_zero_of_not_mem_buffer ρ m hq,
        backgroundCellProfile_zero]
      simp⟩

/-- The placed summand is pointwise real. -/
theorem backgroundShiftedCellTorus_im (n m : ℕ) (q : TransverseTorus) :
    (P.backgroundShiftedCellTorus n m q).im = 0 :=
  P.backgroundCellTorus_im _ m q

/-- The placed series is pointwise real. -/
theorem backgroundShiftedGlobalTorus_im (n : ℕ) (q : TransverseTorus) :
    (P.backgroundShiftedGlobalTorus n q).im = 0 := by
  by_cases hb : ∃ k : ℕ, q ∈ P.torusBufferDisk k
  · obtain ⟨k, hk⟩ := hb
    rw [P.backgroundShiftedGlobalTorus_eq_cell_of_mem_buffer n hk]
    exact P.backgroundShiftedCellTorus_im n k q
  · push Not at hb
    rw [P.backgroundShiftedGlobalTorus_eq_zero_of_outside_buffers n hb]
    simp

/-- Pointwise bound `|β_n + 1| ≤ 2` on the placed series, from `|F| ≤ 1`. -/
theorem norm_backgroundShiftedGlobalTorus_sub_one_le (n : ℕ) (q : TransverseTorus) :
    ‖P.backgroundShiftedGlobalTorus n q - 1‖ ≤ 1 := by
  by_cases hb : ∃ k : ℕ, q ∈ P.torusBufferDisk k
  · obtain ⟨k, hk⟩ := hb
    obtain ⟨t, ht0, _, hEq⟩ := P.exists_backgroundCellTorus_eq
      (P.scaleFamily.cellRatio n k) k q
    rw [P.backgroundShiftedGlobalTorus_eq_cell_of_mem_buffer n hk,
      backgroundShiftedCellTorus, hEq, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      backgroundCellProfile_sub_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_backgroundMultiplierF_le_one
      (mul_nonneg (P.scaleFamily.cellRatio_nonneg n k) ht0)
  · push Not at hb
    rw [P.backgroundShiftedGlobalTorus_eq_zero_of_outside_buffers n hb]
    simp

/-- Pointwise bound on the differentiated series: at most one summand is nonzero, and it obeys
`3 r_k ‖ϑ'‖_∞/R_k ≤ 3 ‖ϑ'‖_∞ R_0/ℓ_n` (`eq:background-multiplier-bounds`). -/
theorem norm_backgroundShiftedGlobalTorusDeriv_le (n : ℕ) (j : Fin 2)
    (q : TransverseTorus) :
    ‖P.backgroundShiftedGlobalTorusDeriv n j q‖ ≤
      3 * (axialPlateauLipschitzConstant : ℝ) *
        (P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n) := by
  have hconst : (0 : ℝ) ≤ 3 * (axialPlateauLipschitzConstant : ℝ) :=
    by positivity
  by_cases hb : ∃ k : ℕ, q ∈ P.torusBufferDisk k
  · obtain ⟨k, hk⟩ := hb
    rw [P.backgroundShiftedGlobalTorusDeriv_eq_cell_of_mem_buffer n j hk,
      backgroundShiftedCellTorusDeriv]
    have hcell := P.norm_backgroundCellTorusDeriv_le
      (P.scaleFamily.cellRatio_nonneg n k) k j q
    have hratio := P.scaleFamily.cellRatio_div_bufferRadius_le n k
    have heq : 3 * P.scaleFamily.cellRatio n k *
        ((axialPlateauLipschitzConstant : ℝ) / P.scaleFamily.bufferRadius k) =
        3 * (axialPlateauLipschitzConstant : ℝ) *
          (P.scaleFamily.cellRatio n k / P.scaleFamily.bufferRadius k) := by
      field_simp
    rw [heq] at hcell
    have hmono : 3 * (axialPlateauLipschitzConstant : ℝ) *
        (P.scaleFamily.cellRatio n k / P.scaleFamily.bufferRadius k) ≤
        3 * (axialPlateauLipschitzConstant : ℝ) *
          (P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n) :=
      mul_le_mul_of_nonneg_left hratio hconst
    linarith
  · push Not at hb
    rw [P.backgroundShiftedGlobalTorusDeriv_eq_zero_of_outside_buffers n j hb,
      norm_zero]
    have h0 : (0 : ℝ) ≤ P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n :=
      div_nonneg (P.scaleFamily.bufferRadius_pos 0).le (P.scaleFamily.ell_pos n).le
    positivity

/-! ## The bundled `L∞` series -/

/-- The `m`-th summand of `β_n + 1` as an `L∞` class. -/
def backgroundShiftedCellValueLInf (n m : ℕ) : TransverseScalarLInf :=
  P.backgroundCellValueLInf (P.scaleFamily.cellRatio_nonneg n m) m

/-- Its displayed derivative as an `L∞` class. -/
def backgroundShiftedCellDerivLInf (n m : ℕ) (j : Fin 2) : TransverseScalarLInf :=
  P.backgroundCellDerivLInf (P.scaleFamily.cellRatio_nonneg n m) m j

/-- The `L∞` class of the summand is represented by the pointwise field. -/
theorem backgroundShiftedCellValueLInf_coe_ae (n m : ℕ) :
    (P.backgroundShiftedCellValueLInf n m : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] P.backgroundShiftedCellTorus n m :=
  P.backgroundCellValueLInf_coe_ae _ m

/-- The `L∞` class of the derivative is represented by the pointwise field. -/
theorem backgroundShiftedCellDerivLInf_coe_ae (n m : ℕ) (j : Fin 2) :
    (P.backgroundShiftedCellDerivLInf n m j : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] P.backgroundShiftedCellTorusDeriv n m j :=
  P.backgroundCellDerivLInf_coe_ae _ m j

/-- `‖Ψ_{r_m} ∘ ϑ_m‖_∞ ≤ 3 r_m`, the summable majorant of the placed series. -/
theorem norm_backgroundShiftedCellValueLInf_le (n m : ℕ) :
    ‖P.backgroundShiftedCellValueLInf n m‖ ≤ 3 * P.scaleFamily.cellRatio n m :=
  P.norm_backgroundCellValueLInf_le _ m

/-- `‖∂_j(Ψ_{r_m} ∘ ϑ_m)‖_∞ ≤ 3‖ϑ'‖_∞ (r_m/R_m)`, the summable majorant of the
differentiated series. -/
theorem norm_backgroundShiftedCellDerivLInf_le (n m : ℕ) (j : Fin 2) :
    ‖P.backgroundShiftedCellDerivLInf n m j‖ ≤
      3 * (axialPlateauLipschitzConstant : ℝ) *
        (P.scaleFamily.cellRatio n m / P.scaleFamily.bufferRadius m) := by
  have hcell := P.norm_backgroundCellDerivLInf_le
    (P.scaleFamily.cellRatio_nonneg n m) m j
  have heq : 3 * P.scaleFamily.cellRatio n m *
      ((axialPlateauLipschitzConstant : ℝ) / P.scaleFamily.bufferRadius m) =
      3 * (axialPlateauLipschitzConstant : ℝ) *
        (P.scaleFamily.cellRatio n m / P.scaleFamily.bufferRadius m) := by
    field_simp
  rw [heq] at hcell
  exact hcell

/-- The placed series converges absolutely in `L∞`. -/
theorem summable_backgroundShiftedCellValueLInf (n : ℕ) :
    Summable (fun m : ℕ ↦ P.backgroundShiftedCellValueLInf n m) :=
  ((P.scaleFamily.summable_cellRatio n).mul_left 3).of_norm_bounded
    (fun m ↦ P.norm_backgroundShiftedCellValueLInf_le n m)

/-- The differentiated placed series converges absolutely in `L∞`. -/
theorem summable_backgroundShiftedCellDerivLInf (n : ℕ) (j : Fin 2) :
    Summable (fun m : ℕ ↦ P.backgroundShiftedCellDerivLInf n m j) :=
  (((P.scaleFamily.summable_cellRatio_div_bufferRadius n).mul_left
    (3 * (axialPlateauLipschitzConstant : ℝ))).of_norm_bounded
      (fun m ↦ P.norm_backgroundShiftedCellDerivLInf_le n m j))

/-- `β_n + 1` as an `L∞` class. -/
def backgroundShiftedValueLInf (n : ℕ) : TransverseScalarLInf :=
  ∑' m : ℕ, P.backgroundShiftedCellValueLInf n m

/-- One derivative of `β_n` as an `L∞` class. -/
def backgroundShiftedDerivLInf (n : ℕ) (j : Fin 2) : TransverseScalarLInf :=
  ∑' m : ℕ, P.backgroundShiftedCellDerivLInf n m j

/-- The `L∞` sum is represented by the pointwise disjoint-support series. -/
theorem backgroundShiftedValueLInf_coe_ae (n : ℕ) :
    (P.backgroundShiftedValueLInf n : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] P.backgroundShiftedGlobalTorus n := by
  have hnorm : Summable (fun m : ℕ ↦ ‖P.backgroundShiftedCellValueLInf n m‖) :=
    ((P.scaleFamily.summable_cellRatio n).mul_left 3).of_nonneg_of_le
      (fun m ↦ norm_nonneg _) (fun m ↦ P.norm_backgroundShiftedCellValueLInf_le n m)
  have henorm : ∑' m : ℕ, ‖P.backgroundShiftedCellValueLInf n m‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hcoe := Lp.coeFn_tsum henorm
  have hcell : ∀ᵐ q ∂transverseMeasure, ∀ m : ℕ,
      (P.backgroundShiftedCellValueLInf n m : TransverseTorus → ℂ) q =
        P.backgroundShiftedCellTorus n m q :=
    ae_all_iff.mpr fun m ↦ P.backgroundShiftedCellValueLInf_coe_ae n m
  filter_upwards [hcoe, hcell] with q hsum hq
  change (((∑' m : ℕ, P.backgroundShiftedCellValueLInf n m) : TransverseScalarLInf) :
      TransverseTorus → ℂ) q = _
  rw [hsum]
  unfold backgroundShiftedGlobalTorus
  exact tsum_congr fun m ↦ hq m

/-- The differentiated `L∞` sum is represented by the pointwise series. -/
theorem backgroundShiftedDerivLInf_coe_ae (n : ℕ) (j : Fin 2) :
    (P.backgroundShiftedDerivLInf n j : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] P.backgroundShiftedGlobalTorusDeriv n j := by
  have hnorm : Summable
      (fun m : ℕ ↦ ‖P.backgroundShiftedCellDerivLInf n m j‖) :=
    ((P.scaleFamily.summable_cellRatio_div_bufferRadius n).mul_left
      (3 * (axialPlateauLipschitzConstant : ℝ))).of_nonneg_of_le
        (fun m ↦ norm_nonneg _)
        (fun m ↦ P.norm_backgroundShiftedCellDerivLInf_le n m j)
  have henorm : ∑' m : ℕ, ‖P.backgroundShiftedCellDerivLInf n m j‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hcoe := Lp.coeFn_tsum henorm
  have hcell : ∀ᵐ q ∂transverseMeasure, ∀ m : ℕ,
      (P.backgroundShiftedCellDerivLInf n m j : TransverseTorus → ℂ) q =
        P.backgroundShiftedCellTorusDeriv n m j q :=
    ae_all_iff.mpr fun m ↦ P.backgroundShiftedCellDerivLInf_coe_ae n m j
  filter_upwards [hcoe, hcell] with q hsum hq
  change (((∑' m : ℕ, P.backgroundShiftedCellDerivLInf n m j) :
      TransverseScalarLInf) : TransverseTorus → ℂ) q = _
  rw [hsum]
  unfold backgroundShiftedGlobalTorusDeriv
  exact tsum_congr fun m ↦ hq m

/-- The differentiated series is the Fourier weak derivative of the series: the coefficient
functional is continuous, so it commutes with the absolutely convergent `L∞` sums. -/
theorem backgroundShifted_hasFourierWeakDerivative (n : ℕ) (j : Fin 2) :
    HasTransverseScalarFourierDerivative j
      (transverseScalarLInfToL2 (P.backgroundShiftedValueLInf n))
      (transverseScalarLInfToL2 (P.backgroundShiftedDerivLInf n j)) := by
  intro frequency
  set L := (transverseScalarCoeffCLM frequency).comp transverseScalarLInfToL2 with hL
  calc
    transverseScalarCoeffCLM frequency
        (transverseScalarLInfToL2 (P.backgroundShiftedDerivLInf n j)) =
        ∑' m : ℕ, L (P.backgroundShiftedCellDerivLInf n m j) :=
      L.map_tsum (P.summable_backgroundShiftedCellDerivLInf n j)
    _ = ∑' m : ℕ, transverseFourierDerivMultiplier j frequency *
          L (P.backgroundShiftedCellValueLInf n m) := by
      refine tsum_congr fun m ↦ ?_
      exact P.backgroundCell_hasFourierWeakDerivative
        (P.scaleFamily.cellRatio_nonneg n m) m j frequency
    _ = transverseFourierDerivMultiplier j frequency *
          ∑' m : ℕ, L (P.backgroundShiftedCellValueLInf n m) := tsum_mul_left
    _ = transverseFourierDerivMultiplier j frequency *
          transverseScalarCoeffCLM frequency
            (transverseScalarLInfToL2 (P.backgroundShiftedValueLInf n)) := by
      rw [← L.map_tsum (P.summable_backgroundShiftedCellValueLInf n)]
      rfl

/-! ## The multiplier `β_n` -/

/-- `β_n = (Σ_m (F(r_m ϑ_m) + 1)) - 1` as an `L∞` class. -/
def backgroundMultiplierValueLInf (n : ℕ) : TransverseScalarLInf :=
  P.backgroundShiftedValueLInf n - transverseConstOneLInf

/-- Its representative is the pointwise series minus one. -/
theorem backgroundMultiplierValueLInf_coe_ae (n : ℕ) :
    (P.backgroundMultiplierValueLInf n : TransverseTorus → ℂ)
      =ᵐ[transverseMeasure] fun q ↦ P.backgroundShiftedGlobalTorus n q - 1 := by
  filter_upwards [Lp.coeFn_sub (P.backgroundShiftedValueLInf n) transverseConstOneLInf,
    P.backgroundShiftedValueLInf_coe_ae n, transverseConstOneLInf_coe_ae]
    with q h1 h2 h3
  change ((P.backgroundShiftedValueLInf n - transverseConstOneLInf :
    TransverseScalarLInf) : TransverseTorus → ℂ) q = _
  rw [h1]
  change (P.backgroundShiftedValueLInf n : TransverseTorus → ℂ) q -
    (transverseConstOneLInf : TransverseTorus → ℂ) q = _
  rw [h2, h3]

/--
**The background multiplier `β_n = F(s_n)`** of `eq:background-multiplier`
(proof of `prop:background-resolvent`), as a scalar periodic `W^{1,∞}` field.

It is built as the placed disjoint-support series `β_n + 1 = Σ_m (F(r_m ϑ_m) + 1)` minus the
constant one; no `W^{1,∞}` chain rule is used.
-/
def backgroundMultiplier (n : ℕ) : TransverseScalarW1Inf where
  value := P.backgroundMultiplierValueLInf n
  grad := fun j ↦ P.backgroundShiftedDerivLInf n j
  value_isReal := by
    filter_upwards [P.backgroundMultiplierValueLInf_coe_ae n] with q hq
    rw [hq]
    apply Complex.conj_eq_iff_im.mpr
    simp [P.backgroundShiftedGlobalTorus_im n q]
  hasFourierDeriv := by
    intro j ν
    have hsub : transverseScalarLInfToL2 (P.backgroundMultiplierValueLInf n) =
        transverseScalarLInfToL2 (P.backgroundShiftedValueLInf n) -
          transverseScalarLInfToL2 transverseConstOneLInf := by
      rw [backgroundMultiplierValueLInf, map_sub]
    rw [hsub, map_sub, mul_sub,
      transverseFourierDerivMultiplier_mul_transverseConstOne, sub_zero]
    exact P.backgroundShifted_hasFourierWeakDerivative n j ν

/-- The value field of `β_n`. -/
@[simp] theorem backgroundMultiplier_value (n : ℕ) :
    (P.backgroundMultiplier n).value = P.backgroundMultiplierValueLInf n := rfl

/-- The gradient fields of `β_n`. -/
@[simp] theorem backgroundMultiplier_grad (n : ℕ) (j : Fin 2) :
    (P.backgroundMultiplier n).grad j = P.backgroundShiftedDerivLInf n j := rfl

/-- **`|β_n| ≤ 1`** (`eq:background-multiplier-bounds`). -/
theorem norm_backgroundMultiplier_value_le_one (n : ℕ) :
    ‖(P.backgroundMultiplier n).value‖ ≤ 1 := by
  apply TransverseScalarW1Inf.norm_value_le_one_of_ae_bound
  filter_upwards [P.backgroundMultiplierValueLInf_coe_ae n] with q hq
  change ‖(P.backgroundMultiplierValueLInf n : TransverseTorus → ℂ) q‖ ≤ 1
  rw [hq]
  exact P.norm_backgroundShiftedGlobalTorus_sub_one_le n q

/--
**`√ε ‖∇_⊥ β_n‖_∞ ≤ C √δ_+ d(K_0)`** (`eq:background-multiplier-bounds`), in the `gradSupNormSq`
form consumed by `eq:background-coercivity`:

`Σ_j ‖∂_j β_n‖_∞² ≤ 2 (3 ‖ϑ'‖_∞ R_0/ℓ_n)²`.

Multiplying by `ε = δ_n ℓ_n²` and using `R_0 = d(K_0)` gives
`ε ‖∇β_n‖_∞² ≤ 18 ‖ϑ'‖_∞² δ_+ d(K_0)²`, i.e. `C = 3√2 ‖ϑ'‖_∞`.
-/
theorem gradSupNormSq_backgroundMultiplier_le (n : ℕ) :
    (P.backgroundMultiplier n).gradSupNormSq ≤
      2 * (3 * (axialPlateauLipschitzConstant : ℝ) *
        (P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n)) ^ 2 := by
  have h0 : (0 : ℝ) ≤ P.scaleFamily.bufferRadius 0 / P.scaleFamily.ell n :=
    div_nonneg (P.scaleFamily.bufferRadius_pos 0).le (P.scaleFamily.ell_pos n).le
  apply TransverseScalarW1Inf.gradSupNormSq_le_of_ae_bound _ (by positivity)
  intro j
  filter_upwards [P.backgroundShiftedDerivLInf_coe_ae n j] with q hq
  change ‖(P.backgroundShiftedDerivLInf n j : TransverseTorus → ℂ) q‖ ≤ _
  rw [hq]
  exact P.norm_backgroundShiftedGlobalTorusDeriv_le n j q

/-! ## The pointwise identification `β_n = F(s_n)` with `2πK_n (u^ax)_3 = τ s_n` -/

/-- Inside the buffer of cell `k`, the placed series is the profile value at the cut-off. -/
theorem backgroundShiftedGlobalTorus_eq_profile_of_mem_buffer (n : ℕ) {k : ℕ}
    {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk k) :
    P.backgroundShiftedGlobalTorus n q =
      ((backgroundCellProfile (P.scaleFamily.cellRatio n k)
        (P.axialCellCutoff k (P.periodizationRepresentative k q hq)) : ℝ) : ℂ) := by
  classical
  rw [P.backgroundShiftedGlobalTorus_eq_cell_of_mem_buffer n hq,
    backgroundShiftedCellTorus, backgroundCellTorus, torusPeriodizedExtension,
    dite_eq_left hq]
  rfl

/-- Inside the buffer of cell `k`, the axial coordinate of the added axial velocity is
`a_k ϑ_k` at the same representative. -/
theorem axialOffsetGlobalTorus_apply_two_of_mem_buffer (tau : ℝ) {k : ℕ}
    {q : TransverseTorus} (hq : q ∈ P.torusBufferDisk k) :
    P.axialOffsetGlobalTorus tau q 2 =
      P.scaleFamily.axialAmplitude tau k *
        P.axialCellCutoff k (P.periodizationRepresentative k q hq) := by
  classical
  rw [P.axialOffsetGlobalTorus_eq_cell_of_mem_buffer tau hq, axialOffsetTorus,
    torusPeriodizedExtension, dite_eq_left hq]
  simp [axialOffsetEuclidean]

/--
**The pointwise identification `β_n = F(s_n)` with `2πK_n (u^ax)_3 = τ s_n`**
(`eq:background-multiplier`, together with the relation `2πK_n ℓ_m = 2π r_m` stated before
`eq:background-local-coefficients`, read as `2πK_n ℓ_m = N r_m` with `ℓ_m = k_*/K_m`).

At every torus point there is a single `s ≥ 0` — namely `s_n(q) = r_k ϑ_k(q)` if `q` lies in
the buffer of cell `k`, and `0` otherwise — with `β_n(q) = F(s)` and
`2πK_n (u^ax)_3(q) = τ s`.  This is what the phase inequality
`eq:background-phase-positive` consumes: on a nonselected
core the plateau gives `ϑ_k = 1`, so `s = r_k` and the ratio gap applies; elsewhere only
`s ≥ 0` is used.
-/
theorem exists_backgroundShiftedGlobalTorus_sub_one_eq (tau : ℝ) (n : ℕ)
    (q : TransverseTorus) :
    ∃ s : ℝ, 0 ≤ s ∧
      P.backgroundShiftedGlobalTorus n q - 1 = ((backgroundMultiplierF s : ℝ) : ℂ) ∧
      2 * Real.pi * (P.scaleFamily.fourierIndex n : ℝ) *
        P.axialOffsetGlobalTorus tau q 2 = tau * s := by
  by_cases hb : ∃ k : ℕ, q ∈ P.torusBufferDisk k
  · obtain ⟨k, hk⟩ := hb
    refine ⟨P.scaleFamily.cellRatio n k *
      P.axialCellCutoff k (P.periodizationRepresentative k q hk),
      mul_nonneg (P.scaleFamily.cellRatio_nonneg n k)
        (P.axialCellCutoff_mem_Icc k _).1, ?_, ?_⟩
    · rw [P.backgroundShiftedGlobalTorus_eq_profile_of_mem_buffer n hk,
        ← Complex.ofReal_one, ← Complex.ofReal_sub, backgroundCellProfile_sub_one]
    · rw [P.axialOffsetGlobalTorus_apply_two_of_mem_buffer tau hk,
        ← mul_assoc, P.scaleFamily.axialAmplitude_eq_tau_mul_cellRatio tau n k,
        mul_assoc]
  · push Not at hb
    refine ⟨0, le_rfl, ?_, ?_⟩
    · rw [P.backgroundShiftedGlobalTorus_eq_zero_of_outside_buffers n hb,
        backgroundMultiplierF]
      norm_num
    · rw [P.axialOffsetGlobalTorus_eq_zero_of_outside_buffers tau hb]
      simp

end TorusCellPlacement

end ScaleFamily

end

end FastDynamo
