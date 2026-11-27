/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Sobolev
public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.Blocks

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Fourier-coefficient characterisations on the torus

For `f ∈ L_2(𝕋^d)` with Fourier coefficients `f̂(k)`, and `s > 0`:

* **`B^s_{2,2}(𝕋^d) = H^s(𝕋^d)`** (`Torus.memBesov_two_two_iff`):
  `f ∈ B^s_{2,2}` iff `∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞`;
* **the Littlewood–Paley characterisation of `B^s_{2,q}`** with sharp dyadic cut-offs
  (`Torus.memBesov_two_iff_blockNorm_lt_top`): `f ∈ B^s_{2,q}` iff
  `(2^(ks) (∑_{2^k ≤ max_i |k_i| < 2^(k+1)} |f̂(k)|²)^(1/2))_k ∈ ℓ_q`, the block norms being
  `Torus.enorm_fourierBlock_sq`.

Both are the spectral statements of `FunctionSpaces.MeasureSpaces.Spectral.Blocks` for the Fourier
basis, transported along `Torus.toLp_trigScheme_eq`. The smooth Littlewood–Paley blocks
`Torus.lpBlock` describe `B^s_{p,q}(𝕋^d)` for every `1 ≤ p < ∞`
(`Torus.memBesov_iff_littlewoodPaleyNorm_lt_top`), and for `1 < p < ∞` the Littlewood–Paley
identity `F^0_{p,2}(𝕋^d) = L_p(𝕋^d)` holds (`Torus.triebelLizorkinSpace_zero_two_eq_top`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus
open scoped ENNReal BoundedContinuousFunction TorusHaar lp

namespace Torus

variable {d : Type*} [Fintype d] {s : ℝ} {q : ℝ≥0∞}

/-- **`B^s_{2,2}(𝕋^d) = H^s(𝕋^d)`**: for `s > 0`, `f ∈ L_2(𝕋^d)` lies in `B^s_{2,2}` iff
`∑_k (1 + max_i |k_i|)^(2s) |f̂(k)|² < ∞`. -/
theorem memBesov_two_two_iff (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (trigScheme d).MemBesov volume 2 s 2 f ↔
      Memℓp (fun k => ((((1 + deg k : ℕ) : ℝ) ^ s : ℝ) : ℂ) * mFourierCoeff f k) 2 := by
  have h := (fourierScheme d).memApprox_two_iff hs f
  simp only [fourierScheme, mFourierBasis_repr] at h
  change ((trigScheme d).toLp volume 2).MemApprox s 2 f ↔ _
  rw [toLp_trigScheme_eq]
  exact h

/-- The **dyadic Fourier block** `Δ_k f = ∑_{2^k ≤ max_i |k_i| < 2^(k+1)} f̂(k) e_k`. -/
noncomputable abbrev fourierBlock (k : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    Lp ℂ 2 (volume : Measure (UnitAddTorus d)) :=
  (fourierScheme d).projectionScheme.block k f

/-- `‖Δ_k f‖² = ∑_{2^k ≤ max_i |k_i| < 2^(k+1)} |f̂(k)|²`. -/
theorem enorm_fourierBlock_sq (k : ℕ) (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖fourierBlock k f‖ₑ ^ 2 = ∑' n : d → ℤ,
      if 2 ^ k ≤ deg n ∧ deg n < 2 ^ (k + 1) then ‖mFourierCoeff f n‖ₑ ^ 2 else 0 := by
  rw [fourierBlock, (fourierScheme d).enorm_block_sq k f]
  congr 1; funext n
  change (if 2 ^ k ≤ deg n ∧ deg n < 2 ^ (k + 1) then ‖mFourierBasis.repr f n‖ₑ ^ 2 else 0) = _
  rw [mFourierBasis_repr]

/-- **The Littlewood–Paley characterisation of `B^s_{2,q}(𝕋^d)`** with sharp dyadic cut-offs:
for `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}` iff
`‖P_1 f‖ + ‖(2^(ks) ‖Δ_k f‖_2)_k‖_{ℓ_q} < ∞`, where `P_1 f` is the mean of `f`. -/
theorem memBesov_two_iff_blockNorm_lt_top (hs : 0 < s) (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (trigScheme d).MemBesov volume 2 s q f ↔
      (fourierScheme d).projectionScheme.blockNorm s q f < ∞ := by
  change ((trigScheme d).toLp volume 2).MemApprox s q f ↔ _
  rw [toLp_trigScheme_eq]
  exact (fourierScheme d).memApprox_iff_blockNorm_lt_top hs hq

end Torus
