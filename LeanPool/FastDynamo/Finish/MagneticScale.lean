/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.ReducedInductionEnergyIdentity
public import LeanPool.FastDynamo.Global.MatchingCellScalingParameters
public import LeanPool.FastDynamo.Global.TorusChartL2Operators
public import LeanPool.FastDynamo.Global.LocalizedSummandAlgebra
public import LeanPool.FastDynamo.Global.CorrectedRieszProjectionSpectralCalculus
public import LeanPool.FastDynamo.Global.TorusFullVelocityConcrete
public import LeanPool.FastDynamo.Finish.RealSolution

/-!
# Axial index and magnetic-length bounds (towards `cor:magnetic-scale`)

Corollary 8.3 (`cor:magnetic-scale`) asserts that the axial Fourier index and the
`H¹`-based magnetic length `L_B^ε = ‖V^ε‖₂ / ‖∇V^ε‖₂` of the magnetic eigenmode `V^ε`
of Theorem 1.2 (`thm:main`) obey, with constants `c, C > 0` independent of `ε`,

`c ε^{-1/2} ≤ |K_ε| ≤ C ε^{-1/2}`  and  `c √ε ≤ L_B^ε ≤ C √ε`   (`0 < ε ≤ ε₀`),

and that the real datum `B_in^ε` has the same magnetic length.  This module proves the
ingredients of the paper's proof as separate statements:

* **Index bounds at a matching cell** (`ScaleFamily.matching_fourierIndex_sq_bounds`,
  `matching_fourierIndex_sq_div_bounds`, `matching_fourierIndex_lower`,
  `matching_fourierIndex_upper`): if the rescaled diffusivity `ε/ℓ_n²` lies in
  `[δ₋, δ₊]`, then `δ₋ k⋆² ≤ ε K_n² ≤ δ₊ k⋆²`, and `√(δ₋/ε) k⋆ ≤ K_n ≤ √(δ₊/ε) k⋆`.  The
  paper has `K_n ℓ_n = 1`; here `ℓ_n = k⋆/K_n` for the seed integer `k⋆`.
* **Upper bound** (`complexAxialMagneticLength_le`): on a non-zero axial sector `K` the axial
  derivative has norm exactly `2π|K|` times the field norm, so `L_B ≤ 1/(2π|K|)` for every
  non-zero mode; `realPhaseAxialMagneticLength_le` gives the same bound for every real phase.
* **Real datum** (`realPhaseAxialMagneticLength_eq_complex`): the real part of the mode at any
  phase, in particular `B_in = re V` (phase `0`), has the same magnetic length.  Its gradient
  `phaseAxialGradientL2` is the weak gradient of the real `H²` field
  (`complexifyProductR3L2_phaseAxialGradientL2`).
* **Lower bound** (`ReducedInductionMagneticScale.complexAxialMagneticLength_lower`): for a
  reduced eigenpair `(λ, b)` with `0 ≤ Re λ`, `b ≠ 0`, `0 < ε`, `K ≠ 0` at a transversely
  divergence-free velocity `u`, `√(ε/M) ≤ L_B` with `M` the `L∞` norm of the stretching
  coefficient of `u`.  This is the bound `√(ε/M_u) ≤ L_B` of the paper's proof (with
  `M_u = ess sup ‖∇u‖_op`); it rests on the energy inequality `ε ‖∇B‖² ≤ M ‖B‖²`
  (`epsilon_mul_norm_sq_productGradient_le_stretching`) and on the algebraic step
  `magneticLength_lower_of_energy`.

The corollary for the eigenmodes of Theorem 1.2 is `main_theorem_magnetic_scale`
(`FastDynamo/Finish/MagneticScaleMain.lean`), which instantiates these bounds at the matching
cell of the parameter chain.
-/

@[expose] public section

/-!
## Axial index and magnetic-length estimates

The reusable, velocity-independent part of Corollary 8.3 (`cor:magnetic-scale`).

There are three independent ingredients.

* The matching-scale arithmetic gives two-sided bounds for the square of the
  selected integer Fourier index.
* On a fixed nonzero axial sector, the axial derivative has the exact norm
  `2 * pi * |K|` times the field norm. Consequently the full gradient gives
  the paper's upper bound for the magnetic length.
* A generic energy inequality
  `epsilon * ||grad B||^2 <= M * ||B||^2` gives the complementary lower
  bound `sqrt (epsilon / M) <= ||B|| / ||grad B||`.

The last ingredient is stated with the energy inequality as a
hypothesis, so that this section stays independent of any particular velocity.
The global velocity and the growing eigenmode are constructed in
`FastDynamo/MainTheorem.lean` (`mainPhysicalConclusion_holds`), and the energy
inequality for a reduced eigenpair is proved in the last section below.
-/

namespace FastDynamo

noncomputable section

/-! ## Matching-index arithmetic -/

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-- Exact cancellation behind
`epsilon K_n^2 = (epsilon / ell_n^2) kStar^2`.

This identity does not need the admissible-window hypothesis; it only uses
the definition `ell_n = kStar / K_n` and positivity of both integers. -/
theorem epsilon_mul_fourierIndex_sq
    (f : ScaleFamily r) (n : ℕ) (epsilon : ℝ) :
    epsilon * (f.fourierIndex n : ℝ) ^ 2 =
      (epsilon / f.ell n ^ 2) * (p.kStar : ℝ) ^ 2 := by
  rw [f.ell_formula, div_pow]
  have hK : (f.fourierIndex n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.2 (f.fourierIndex_pos n))
  have hk : (p.kStar : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.2 p.kStar_pos)
  field_simp [hK, hk]

/-- Squared two-sided form of the paper's estimate
`K_epsilon \asymp epsilon^(-1/2)`.

Writing the result after multiplication by `epsilon` avoids artificial
division-by-zero side conditions and is exactly what follows from membership
of the rescaled diffusivity in `[deltaMinus, deltaPlus]`. -/
theorem matching_fourierIndex_sq_bounds
    (f : ScaleFamily r) (n : ℕ) (epsilon : ℝ)
    (hmatch : epsilon / f.ell n ^ 2 ∈ p.interval) :
    p.deltaMinus * (p.kStar : ℝ) ^ 2 ≤
        epsilon * (f.fourierIndex n : ℝ) ^ 2 ∧
      epsilon * (f.fourierIndex n : ℝ) ^ 2 ≤
        p.deltaPlus * (p.kStar : ℝ) ^ 2 := by
  rw [f.epsilon_mul_fourierIndex_sq n epsilon]
  constructor
  · exact mul_le_mul_of_nonneg_right hmatch.1 (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right hmatch.2 (sq_nonneg _)

/-- Division form of `matching_fourierIndex_sq_bounds`, valid for positive
physical diffusivity. -/
theorem matching_fourierIndex_sq_div_bounds
    (f : ScaleFamily r) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hmatch : epsilon / f.ell n ^ 2 ∈ p.interval) :
    p.deltaMinus * (p.kStar : ℝ) ^ 2 / epsilon ≤
        (f.fourierIndex n : ℝ) ^ 2 ∧
      (f.fourierIndex n : ℝ) ^ 2 ≤
        p.deltaPlus * (p.kStar : ℝ) ^ 2 / epsilon := by
  obtain ⟨hlower, hupper⟩ :=
    f.matching_fourierIndex_sq_bounds n epsilon hmatch
  constructor
  · exact (div_le_iff₀ hepsilon).2 (by simpa [mul_comm] using hlower)
  · exact (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hupper)

/-- Literal square-root lower bound for the selected Fourier index. -/
theorem matching_fourierIndex_lower
    (f : ScaleFamily r) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hmatch : epsilon / f.ell n ^ 2 ∈ p.interval) :
    (p.kStar : ℝ) * Real.sqrt (p.deltaMinus / epsilon) ≤
      (f.fourierIndex n : ℝ) := by
  have hratio : 0 ≤ p.deltaMinus / epsilon :=
    div_nonneg p.deltaMinus_pos.le hepsilon.le
  have hleft : 0 ≤
      (p.kStar : ℝ) * Real.sqrt (p.deltaMinus / epsilon) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hK : 0 ≤ (f.fourierIndex n : ℝ) :=
    (Nat.cast_pos.2 (f.fourierIndex_pos n)).le
  apply (sq_le_sq₀ hleft hK).1
  rw [mul_pow, Real.sq_sqrt hratio]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (f.matching_fourierIndex_sq_div_bounds n hepsilon hmatch).1

/-- Literal square-root upper bound for the selected Fourier index. -/
theorem matching_fourierIndex_upper
    (f : ScaleFamily r) (n : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hmatch : epsilon / f.ell n ^ 2 ∈ p.interval) :
    (f.fourierIndex n : ℝ) ≤
      (p.kStar : ℝ) * Real.sqrt (p.deltaPlus / epsilon) := by
  have hratio : 0 ≤ p.deltaPlus / epsilon :=
    div_nonneg p.deltaPlus_pos.le hepsilon.le
  have hright : 0 ≤
      (p.kStar : ℝ) * Real.sqrt (p.deltaPlus / epsilon) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  have hK : 0 ≤ (f.fourierIndex n : ℝ) :=
    (Nat.cast_pos.2 (f.fourierIndex_pos n)).le
  apply (sq_le_sq₀ hK hright).1
  rw [mul_pow, Real.sq_sqrt hratio]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (f.matching_fourierIndex_sq_div_bounds n hepsilon hmatch).2

end ScaleFamily

/-! ## The product-torus gradient and its fixed-sector norm -/

/-- Hilbert target for the three directional weak derivatives of a
`C3`-valued product-torus field. -/
abbrev ProductGradientL2 :=
  PiLp 2 (fun _ : Fin 3 ↦ ProductC3L2)

/-- The complete weak gradient of a product Fourier `H²` field, ordered as
`(partial_1 B, partial_2 B, partial_3 B)`. -/
def productGradientFromH2 (B : ProductC3H2) : ProductGradientL2 :=
  WithLp.toLp 2 ![
    productTransverseDerivFromH2 0 B,
    productTransverseDerivFromH2 1 B,
    productAxialDerivFromH2 B]

/-- Squared norm of the complete product-torus gradient. -/
theorem norm_sq_productGradientFromH2 (B : ProductC3H2) :
    ‖productGradientFromH2 B‖ ^ 2 =
      ‖productTransverseDerivFromH2 0 B‖ ^ 2 +
      ‖productTransverseDerivFromH2 1 B‖ ^ 2 +
      ‖productAxialDerivFromH2 B‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [productGradientFromH2, Fin.sum_univ_succ]
  ring

/-- Exact `L²` norm of the axial derivative on a fixed Fourier sector. -/
theorem norm_productAxialDerivFromH2_axialLiftH2
    (K : ℤ) (b : TransverseC3H2) :
    ‖productAxialDerivFromH2 (axialLiftH2 K b)‖ =
      (2 * Real.pi * |(K : ℝ)|) * ‖transverseH2Embedding b‖ := by
  rw [productAxialDerivFromH2_axialLiftH2,
    axialDerivFromH2_apply, norm_smul, norm_axialMultiplier,
    norm_axialLiftL2]
  rfl

/-- Exact fixed-sector squared-gradient identity. In particular, the axial
contribution is `(2 pi K)^2 ||B||_2^2`. -/
theorem norm_sq_productGradientFromH2_axialLiftH2
    (K : ℤ) (b : TransverseC3H2) :
    ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 =
      ‖transverseDerivFromH2 0 b‖ ^ 2 +
      ‖transverseDerivFromH2 1 b‖ ^ 2 +
      (2 * Real.pi * (K : ℝ)) ^ 2 *
        ‖transverseH2Embedding b‖ ^ 2 := by
  rw [norm_sq_productGradientFromH2,
    productTransverseDerivFromH2_axialLiftH2 0 K b,
    productTransverseDerivFromH2_axialLiftH2 1 K b,
    axialTransverseDerivFromH2_apply K 0 b,
    axialTransverseDerivFromH2_apply K 1 b,
    norm_axialLiftL2 K (transverseDerivFromH2 0 b),
    norm_axialLiftL2 K (transverseDerivFromH2 1 b),
    norm_productAxialDerivFromH2_axialLiftH2]
  have hwave_sq :
      (2 * Real.pi * |(K : ℝ)|) ^ 2 =
        (2 * Real.pi * (K : ℝ)) ^ 2 := by
    calc
      (2 * Real.pi * |(K : ℝ)|) ^ 2 =
          (2 * Real.pi) ^ 2 * |(K : ℝ)| ^ 2 := by ring
      _ = (2 * Real.pi) ^ 2 * (K : ℝ) ^ 2 := by rw [sq_abs]
      _ = (2 * Real.pi * (K : ℝ)) ^ 2 := by ring
  rw [mul_pow, hwave_sq]

/-- The full gradient controls the exact axial derivative norm. -/
theorem axial_wave_mul_norm_le_gradient
    (K : ℤ) (b : TransverseC3H2) :
    (2 * Real.pi * |(K : ℝ)|) * ‖transverseH2Embedding b‖ ≤
      ‖productGradientFromH2 (axialLiftH2 K b)‖ := by
  have hleft : 0 ≤
      (2 * Real.pi * |(K : ℝ)|) * ‖transverseH2Embedding b‖ := by
    positivity
  rw [← sq_le_sq₀ hleft (norm_nonneg _),
    norm_sq_productGradientFromH2_axialLiftH2]
  have hwave_sq :
      (2 * Real.pi * |(K : ℝ)|) ^ 2 =
        (2 * Real.pi * (K : ℝ)) ^ 2 := by
    calc
      (2 * Real.pi * |(K : ℝ)|) ^ 2 =
          (2 * Real.pi) ^ 2 * |(K : ℝ)| ^ 2 := by ring
      _ = (2 * Real.pi) ^ 2 * (K : ℝ) ^ 2 := by rw [sq_abs]
      _ = (2 * Real.pi * (K : ℝ)) ^ 2 := by ring
  rw [mul_pow, hwave_sq]
  nlinarith [sq_nonneg ‖transverseDerivFromH2 0 b‖,
    sq_nonneg ‖transverseDerivFromH2 1 b‖]

/-! ## Magnetic length -/

/-- The paper's `H¹`-based magnetic length for a complex fixed-sector
field. -/
def complexAxialMagneticLength (K : ℤ) (b : TransverseC3H2) : ℝ :=
  ‖productH2Embedding (axialLiftH2 K b)‖ /
    ‖productGradientFromH2 (axialLiftH2 K b)‖

/-- A nonzero fixed axial mode has nonzero complete gradient. -/
theorem norm_productGradientFromH2_axialLiftH2_pos
    (K : ℤ) (hK : K ≠ 0) {b : TransverseC3H2} (hb : b ≠ 0) :
    0 < ‖productGradientFromH2 (axialLiftH2 K b)‖ := by
  have hwave : 0 < 2 * Real.pi * |(K : ℝ)| := by
    have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast hK
    positivity
  have hfield : 0 < ‖transverseH2Embedding b‖ := by
    exact norm_pos_iff.mpr (fun hzero ↦ hb
      (transverseH2Embedding_injective (by simpa using hzero)))
  exact (mul_pos hwave hfield).trans_le
    (axial_wave_mul_norm_le_gradient K b)

/-- The axial derivative gives the upper magnetic-length bound
`L_B <= (2 pi |K|)^(-1)`. -/
theorem complexAxialMagneticLength_le
    (K : ℤ) (hK : K ≠ 0) {b : TransverseC3H2} (hb : b ≠ 0) :
    complexAxialMagneticLength K b ≤
      1 / (2 * Real.pi * |(K : ℝ)|) := by
  have hwave : 0 < 2 * Real.pi * |(K : ℝ)| := by
    have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast hK
    positivity
  have hgrad := norm_productGradientFromH2_axialLiftH2_pos K hK hb
  rw [complexAxialMagneticLength,
    norm_productH2Embedding_axialLiftH2]
  apply (div_le_div_iff₀ hgrad hwave).2
  simpa [mul_comm] using axial_wave_mul_norm_le_gradient K b

/-! ## The phase-rotated real field -/

/-- Hilbert target for the three directional weak derivatives of a real
product-torus field. -/
abbrev ProductRealGradientL2 :=
  PiLp 2 (fun _ : Fin 3 ↦ ProductR3L2)

/-- Gradient represented by the phase-rotated real parts of the three
fixed-sector derivative amplitudes.  It is the weak gradient of the real field
`Re(e^{iθ} e^{2πiKx₃} b)`: `complexifyProductR3L2_phaseAxialGradientL2` identifies each
component, complexified, with the corresponding component of
`productGradientFromH2 (productRealPartH2 (e^{iθ} • axialLiftH2 K b))`. -/
def phaseAxialGradientL2
    (K : ℤ) (phase : ℝ) (b : TransverseC3H2) : ProductRealGradientL2 :=
  WithLp.toLp 2 ![
    phaseAxialFieldL2 K phase (transverseDerivFromH2 0 b),
    phaseAxialFieldL2 K phase (transverseDerivFromH2 1 b),
    phaseAxialFieldL2 K phase
      (axialMultiplier K • transverseH2Embedding b)]

/-- A complex-linear map from `H²` to `L²` that commutes with conjugation commutes with the
real-part projection. -/
private theorem map_productRealPartH2_of_conj (D : ProductC3H2 →L[ℂ] ProductC3L2)
    (hD : ∀ B, productConjL2 (D B) = D (productConjH2 B)) (B : ProductC3H2) :
    D (productRealPartH2 B) = productRealPartL2 (D B) := by
  rw [productRealPartH2_apply, productRealPartL2_apply, D.map_smul_of_tower, map_add, hD]

/-- **`phaseAxialGradientL2` is the weak gradient of the real field.**  For every phase `θ`,
the `i`-th component of `phaseAxialGradientL2 K θ b`, complexified, is the `i`-th weak
derivative of the real `H²` field `Re(e^{iθ} V)` of the mode `V = e^{2πiKx₃} b`:

```
  complexify (∇_real (Re(e^{iθ} V)))_i = ∂_i (Re(e^{iθ} V)) .
```

The weak derivatives `productTransverseDerivFromH2`, `productAxialDerivFromH2` commute with
conjugation, hence with the real part, and on the axial sector they are the derivative
amplitudes of `b` (`productTransverseDerivFromH2_axialLiftH2`,
`productAxialDerivFromH2_axialLiftH2`). -/
theorem complexifyProductR3L2_phaseAxialGradientL2 (K : ℤ) (phase : ℝ) (b : TransverseC3H2)
    (i : Fin 3) :
    complexifyProductR3L2 (phaseAxialGradientL2 K phase b i) =
      productGradientFromH2
        (productRealPartH2 (Complex.exp ((phase : ℂ) * Complex.I) • axialLiftH2 K b)) i := by
  fin_cases i
  · change complexifyProductR3L2 (phaseAxialFieldL2 K phase (transverseDerivFromH2 0 b)) =
      productTransverseDerivFromH2 0 _
    rw [map_productRealPartH2_of_conj _ (productConjL2_productTransverseDerivFromH2 0), map_smul,
      productTransverseDerivFromH2_axialLiftH2, axialTransverseDerivFromH2_apply,
      phaseAxialFieldL2, complexifyProductR3L2_realPartL2]
  · change complexifyProductR3L2 (phaseAxialFieldL2 K phase (transverseDerivFromH2 1 b)) =
      productTransverseDerivFromH2 1 _
    rw [map_productRealPartH2_of_conj _ (productConjL2_productTransverseDerivFromH2 1), map_smul,
      productTransverseDerivFromH2_axialLiftH2, axialTransverseDerivFromH2_apply,
      phaseAxialFieldL2, complexifyProductR3L2_realPartL2]
  · change complexifyProductR3L2
        (phaseAxialFieldL2 K phase (axialMultiplier K • transverseH2Embedding b)) =
      productAxialDerivFromH2 _
    rw [map_productRealPartH2_of_conj _ productConjL2_productAxialDerivFromH2, map_smul,
      productAxialDerivFromH2_axialLiftH2, axialDerivFromH2_apply,
      phaseAxialFieldL2, complexifyProductR3L2_realPartL2,
      show axialLiftL2 K (axialMultiplier K • transverseH2Embedding b) =
        axialMultiplier K • axialLiftL2 K b.1.1 from map_smul _ _ _]

/-- Every derivative of a nonzero axial mode obeys the same half-norm law as
the field itself. Thus the full real gradient has exactly half the squared
norm of the complex gradient, independently of phase. -/
theorem phaseAxialGradientL2_norm_sq
    (K : ℤ) (hK : K ≠ 0) (phase : ℝ) (b : TransverseC3H2) :
    ‖phaseAxialGradientL2 K phase b‖ ^ 2 =
      (1 / 2 : ℝ) *
        ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 3, ‖![
    phaseAxialFieldL2 K phase (transverseDerivFromH2 0 b),
    phaseAxialFieldL2 K phase (transverseDerivFromH2 1 b),
    phaseAxialFieldL2 K phase
      (axialMultiplier K • transverseH2Embedding b)] i‖ ^ 2) = _
  rw [Fin.sum_univ_three]
  change ‖phaseAxialFieldL2 K phase (transverseDerivFromH2 0 b)‖ ^ 2 +
      ‖phaseAxialFieldL2 K phase (transverseDerivFromH2 1 b)‖ ^ 2 +
      ‖phaseAxialFieldL2 K phase (axialMultiplier K • transverseH2Embedding b)‖ ^ 2 = _
  rw [phaseAxialFieldL2_norm_sq K hK phase
      (transverseDerivFromH2 0 b),
    phaseAxialFieldL2_norm_sq K hK phase
      (transverseDerivFromH2 1 b),
    phaseAxialFieldL2_norm_sq K hK phase
      (axialMultiplier K • transverseH2Embedding b),
    norm_sq_productGradientFromH2_axialLiftH2,
    norm_smul, norm_axialMultiplier, mul_pow]
  have hwave_sq :
      (2 * Real.pi * |(K : ℝ)|) ^ 2 =
        (2 * Real.pi * (K : ℝ)) ^ 2 := by
    calc
      (2 * Real.pi * |(K : ℝ)|) ^ 2 =
          (2 * Real.pi) ^ 2 * |(K : ℝ)| ^ 2 := by ring
      _ = (2 * Real.pi) ^ 2 * (K : ℝ) ^ 2 := by rw [sq_abs]
      _ = (2 * Real.pi * (K : ℝ)) ^ 2 := by ring
  rw [hwave_sq]
  simp only [transverseH2Embedding_apply]
  ring

/-- Magnetic length formed from a phase-rotated real axial field and the
phase-rotated real parts of its three complex weak-derivative fields. -/
def realPhaseAxialMagneticLength
    (K : ℤ) (phase : ℝ) (b : TransverseC3H2) : ℝ :=
  ‖phaseAxialFieldL2 K phase (transverseH2Embedding b)‖ /
    ‖phaseAxialGradientL2 K phase b‖

/-- The real phase-gradient of a nonzero nonconstant axial mode is nonzero. -/
theorem norm_phaseAxialGradientL2_pos
    (K : ℤ) (hK : K ≠ 0) (phase : ℝ)
    {b : TransverseC3H2} (hb : b ≠ 0) :
    0 < ‖phaseAxialGradientL2 K phase b‖ := by
  have hcomplex := norm_productGradientFromH2_axialLiftH2_pos K hK hb
  have hsq := phaseAxialGradientL2_norm_sq K hK phase b
  nlinarith [sq_pos_of_pos hcomplex, norm_nonneg
    (phaseAxialGradientL2 K phase b)]

/-- Taking a real part at any phase changes both the field norm and its
gradient norm by the same factor. Hence the magnetic length is unchanged. -/
theorem realPhaseAxialMagneticLength_eq_complex
    (K : ℤ) (hK : K ≠ 0) (phase : ℝ)
    {b : TransverseC3H2} (hb : b ≠ 0) :
    realPhaseAxialMagneticLength K phase b =
      complexAxialMagneticLength K b := by
  have hrealGrad := norm_phaseAxialGradientL2_pos K hK phase hb
  have hcomplexGrad :=
    norm_productGradientFromH2_axialLiftH2_pos K hK hb
  rw [realPhaseAxialMagneticLength, complexAxialMagneticLength]
  apply (div_eq_div_iff hrealGrad.ne' hcomplexGrad.ne').2
  rw [← sq_eq_sq₀
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    (‖phaseAxialFieldL2 K phase (transverseH2Embedding b)‖ *
        ‖productGradientFromH2 (axialLiftH2 K b)‖) ^ 2 =
        ‖phaseAxialFieldL2 K phase (transverseH2Embedding b)‖ ^ 2 *
          ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 := by ring
    _ = ((1 / 2 : ℝ) * ‖transverseH2Embedding b‖ ^ 2) *
          ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 := by
        rw [phaseAxialFieldL2_norm_sq K hK phase
          (transverseH2Embedding b)]
    _ = ‖transverseH2Embedding b‖ ^ 2 *
          ((1 / 2 : ℝ) *
            ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2) := by ring
    _ = ‖transverseH2Embedding b‖ ^ 2 *
          ‖phaseAxialGradientL2 K phase b‖ ^ 2 := by
        rw [phaseAxialGradientL2_norm_sq K hK phase b]
    _ = (‖productH2Embedding (axialLiftH2 K b)‖ *
          ‖phaseAxialGradientL2 K phase b‖) ^ 2 := by
        rw [norm_productH2Embedding_axialLiftH2]
        ring

/-- The same axial upper bound holds for every real phase, including the
real initial datum (`phase = 0`). -/
theorem realPhaseAxialMagneticLength_le
    (K : ℤ) (hK : K ≠ 0) (phase : ℝ)
    {b : TransverseC3H2} (hb : b ≠ 0) :
    realPhaseAxialMagneticLength K phase b ≤
      1 / (2 * Real.pi * |(K : ℝ)|) := by
  rw [realPhaseAxialMagneticLength_eq_complex K hK phase hb]
  exact complexAxialMagneticLength_le K hK hb

/-- Pure algebraic endpoint of the eigenvalue energy argument. It is useful
independently of the particular induction operator. -/
theorem magneticLength_sq_lower_of_energy
    {epsilon M fieldNorm gradientNorm : ℝ}
    (hM : 0 < M) (hgradient : 0 < gradientNorm)
    (henergy : epsilon * gradientNorm ^ 2 ≤ M * fieldNorm ^ 2) :
    epsilon / M ≤ (fieldNorm / gradientNorm) ^ 2 := by
  rw [div_pow]
  exact (div_le_div_iff₀ hM (sq_pos_of_pos hgradient)).2 (by
    simpa [mul_comm] using henergy)

/-- Square-root form of `magneticLength_sq_lower_of_energy`. -/
theorem magneticLength_lower_of_energy
    {epsilon M fieldNorm gradientNorm : ℝ}
    (_hepsilon : 0 ≤ epsilon) (hM : 0 < M)
    (hfield : 0 ≤ fieldNorm) (hgradient : 0 < gradientNorm)
    (henergy : epsilon * gradientNorm ^ 2 ≤ M * fieldNorm ^ 2) :
    Real.sqrt (epsilon / M) ≤ fieldNorm / gradientNorm := by
  have hratio : 0 ≤ fieldNorm / gradientNorm :=
    div_nonneg hfield hgradient.le
  rw [← Real.sqrt_sq hratio]
  exact Real.sqrt_le_sqrt
    (magneticLength_sq_lower_of_energy hM hgradient henergy)

/-- Conditional lower bound for a complex fixed-sector magnetic length once
the eigenvalue energy estimate has been supplied. -/
theorem complexAxialMagneticLength_lower_of_energy
    (K : ℤ) (hK : K ≠ 0) {b : TransverseC3H2} (hb : b ≠ 0)
    {epsilon M : ℝ} (hepsilon : 0 ≤ epsilon) (hM : 0 < M)
    (henergy :
      epsilon * ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 ≤
        M * ‖productH2Embedding (axialLiftH2 K b)‖ ^ 2) :
    Real.sqrt (epsilon / M) ≤ complexAxialMagneticLength K b := by
  exact magneticLength_lower_of_energy hepsilon hM (norm_nonneg _)
    (norm_productGradientFromH2_axialLiftH2_pos K hK hb) henergy

end

end FastDynamo

/-!
## The magnetic-length lower bound for a reduced eigenpair

The real part of the reduced eigenpair identity gives the global
energy estimate directly.  Transverse and axial transport are skew, diffusion
is the negative full fixed-sector gradient energy, and stretching is bounded
by the `L∞` norm of the literal stretching matrix.  Consequently

`epsilon * ‖∇B‖² ≤ ‖∇u‖_stretch * ‖B‖²`.

For positive diffusivity and a non-zero sector and eigenvector the energy estimate also proves
that the stretching norm is strictly positive, so the exact (unregularized) magnetic lower bound
applies.
-/

namespace FastDynamo

noncomputable section

open Complex

namespace ReducedInductionMagneticScale

/-! ## The eigenpair energy estimate -/

/-- A reduced eigenpair in the closed right half-plane satisfies the exact
energy inequality needed for the magnetic-length lower bound. -/
theorem epsilon_mul_norm_sq_productGradient_le_stretching
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (hEpsilon : 0 ≤ epsilon) (K : ℤ)
    (eigenvalue : ℂ) (hEigenvalue : 0 ≤ eigenvalue.re)
    (b : TransverseC3H2)
    (hEigen :
      (reducedInductionOperator u epsilon K).IsEigenpair eigenvalue b) :
    epsilon * ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 ≤
      ‖transverseStretchingCoefficient u‖ *
        ‖productH2Embedding (axialLiftH2 K b)‖ ^ 2 := by
  have hAction := re_inner_reducedInductionAction_eq
    u hu epsilon K b
  have hStretch := re_inner_reducedInductionStretching_le u b
  have hEigenPairing :
      (inner ℂ (transverseH2Embedding b)
        (reducedInductionAction u epsilon K b)).re =
      eigenvalue.re * ‖transverseH2Embedding b‖ ^ 2 := by
    have hEigenAction := hEigen.2
    change reducedInductionAction u epsilon K b =
      eigenvalue • transverseH2Embedding b at hEigenAction
    have hSelfRe :
        (inner ℂ (transverseH2Embedding b)
          (transverseH2Embedding b)).re =
        ‖transverseH2Embedding b‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (transverseH2Embedding b)
    have hSelfIm :
        (inner ℂ (transverseH2Embedding b)
          (transverseH2Embedding b)).im = 0 :=
      by
        change RCLike.im (inner ℂ (transverseH2Embedding b)
          (transverseH2Embedding b)) = 0
        exact inner_self_im (transverseH2Embedding b)
    rw [hEigenAction, inner_smul_right, Complex.mul_re, hSelfRe, hSelfIm]
    ring
  have hActionNonneg : 0 ≤
      (inner ℂ (transverseH2Embedding b)
        (reducedInductionAction u epsilon K b)).re := by
    rw [hEigenPairing]
    exact mul_nonneg hEigenvalue (sq_nonneg _)
  have hAxialNonneg :
      0 ≤ (2 * Real.pi * (K : ℝ)) ^ 2 := sq_nonneg _
  have hTotalEnergyNonneg :
      0 ≤ reducedTransverseGradientEnergy b +
        (2 * Real.pi * (K : ℝ)) ^ 2 *
          ‖transverseH2Embedding b‖ ^ 2 :=
    add_nonneg (reducedTransverseGradientEnergy_nonneg b)
      (mul_nonneg hAxialNonneg (sq_nonneg _))
  have hReducedEnergy :
      epsilon * (reducedTransverseGradientEnergy b +
        (2 * Real.pi * (K : ℝ)) ^ 2 *
          ‖transverseH2Embedding b‖ ^ 2) ≤
        ‖transverseStretchingCoefficient u‖ *
          ‖transverseH2Embedding b‖ ^ 2 := by
    have hDiffusionNonneg := mul_nonneg hEpsilon hTotalEnergyNonneg
    nlinarith
  have hGradientIdentity :
      reducedTransverseGradientEnergy b +
          (2 * Real.pi * (K : ℝ)) ^ 2 *
            ‖transverseH2Embedding b‖ ^ 2 =
        ‖productGradientFromH2 (axialLiftH2 K b)‖ ^ 2 := by
    rw [norm_sq_productGradientFromH2_axialLiftH2]
    simp only [reducedTransverseGradientEnergy, Fin.sum_univ_two]
  rw [← hGradientIdentity,
    norm_productH2Embedding_axialLiftH2]
  exact hReducedEnergy

/-- With positive diffusivity and a nonzero fixed sector, existence of the
eigenpair forces the stretching coefficient norm itself to be positive. -/
theorem norm_transverseStretchingCoefficient_pos_of_reducedEigenpair
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) (K : ℤ) (hK : K ≠ 0)
    (eigenvalue : ℂ) (hEigenvalue : 0 ≤ eigenvalue.re)
    (b : TransverseC3H2) (hb : b ≠ 0)
    (hEigen :
      (reducedInductionOperator u epsilon K).IsEigenpair eigenvalue b) :
    0 < ‖transverseStretchingCoefficient u‖ := by
  have hEnergy := epsilon_mul_norm_sq_productGradient_le_stretching
    u hu epsilon hEpsilon.le K eigenvalue hEigenvalue b hEigen
  have hGradient :
      0 < ‖productGradientFromH2 (axialLiftH2 K b)‖ :=
    norm_productGradientFromH2_axialLiftH2_pos K hK hb
  have hPositiveProduct :
      0 < ‖transverseStretchingCoefficient u‖ *
        ‖productH2Embedding (axialLiftH2 K b)‖ ^ 2 :=
    (mul_pos hEpsilon (sq_pos_of_pos hGradient)).trans_le hEnergy
  rcases (mul_pos_iff.mp hPositiveProduct) with hPositive | hNegative
  · exact hPositive.1
  · exact False.elim
      ((not_lt_of_ge (norm_nonneg (transverseStretchingCoefficient u)))
        hNegative.1)

/-- Under positive diffusivity the exact stretching norm, without a `+1`,
is a valid magnetic-scale denominator. -/
theorem complexAxialMagneticLength_lower
    (u : TransverseRealW1Inf) (hu : IsTransverseDivergenceFree u)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) (K : ℤ) (hK : K ≠ 0)
    (eigenvalue : ℂ) (hEigenvalue : 0 ≤ eigenvalue.re)
    (b : TransverseC3H2) (hb : b ≠ 0)
    (hEigen :
      (reducedInductionOperator u epsilon K).IsEigenpair eigenvalue b) :
    Real.sqrt
        (epsilon / ‖transverseStretchingCoefficient u‖) ≤
      complexAxialMagneticLength K b := by
  have hEnergy := epsilon_mul_norm_sq_productGradient_le_stretching
    u hu epsilon hEpsilon.le K eigenvalue hEigenvalue b hEigen
  have hStretching :=
    norm_transverseStretchingCoefficient_pos_of_reducedEigenpair
      u hu epsilon hEpsilon K hK eigenvalue hEigenvalue b hb hEigen
  exact complexAxialMagneticLength_lower_of_energy K hK hb hEpsilon.le
    hStretching hEnergy

end ReducedInductionMagneticScale

end

end FastDynamo
