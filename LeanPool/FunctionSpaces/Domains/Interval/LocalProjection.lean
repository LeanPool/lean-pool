/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.PiecewisePoly
public import LeanPool.FunctionSpaces.Domains.Interval.Smoothing
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Projection

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Local projections onto polynomials

The **local projection** of a function `g` on an interval onto the polynomials of degree `< r`
is computed from the moments of `g`. On `[0, 1]` the pairing `⟨P, Q⟩ = ∫_0^1 P Q` of
polynomials of degree `< r` is nondegenerate (`Interval.polyPairing_nondegenerate`): pairing `P`
with its conjugate `PBar` gives `∫_0^1 |P|²`. So the monomial basis `b_i` has a dual basis `d_i`,
`⟨d_i, b_k⟩ = δ_{ik}` (Mathlib's `LinearMap.BilinForm.dualBasis`), and every `P` of degree `< r`
is `P = ∑_i ⟨P, b_i⟩ d_i` (`Interval.sum_polyPairing_smul_dualPoly`). For any function `g`,
`Π g = ∑_i (∫_0^1 g b_i) d_i` is therefore a projection onto the polynomials, the
`L_2[0, 1]`-orthogonal projection.

On a dyadic interval `I_{j,m}` the local projection is `Π g(x) = ∑_i c_i d_i(2^j x - m)` with
`c_i = 2^j ∫_{I_{j,m}} g(y) b_i(2^j y - m) dy` (`Interval.locProj`). It reproduces polynomials
(`Interval.polyFun_locProj_of_eqOn`, by the change of variables `y = (m + t) 2^(-j)`) and is
bounded in `L_p(I_{j,m})` by `r M²`, with `M` a bound of the `b_i` and `d_i` on `[0, 1]`
(`Interval.eLpNorm_locProj_le`): Hölder's inequality gives `|c_i| ≤ M 2^(j/p) ‖g‖_{L_p(I_{j,m})}`,
and the interval has length `2^(-j)`. Applied on all intervals of level `j` it is the
projection `P_j` of `L_p[0, 1]`, `1 ≤ p < ∞`, onto the piecewise polynomials of level `j`
(`Interval.ppProj`), with `‖P_j‖ ≤ r M²` for every `j`. So the dyadic piecewise polynomials form
a projection scheme (`Interval.ppProjectionScheme`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

/-- The product of two polynomials is integrable on `[0, 1]`. -/
theorem integrableOn_polyFun_mul (P Q : ℂ[X]) :
    IntegrableOn (fun x => polyFun P x * polyFun Q x) (Icc (0 : ℝ) 1) :=
  ((continuous_polyFun P).mul (continuous_polyFun Q)).integrableOn_Icc

/-- The **pairing** `⟨P, Q⟩ = ∫_0^1 P Q` of polynomials of degree `< r`, a bilinear form. -/
noncomputable def polyPairing (r : ℕ) : LinearMap.BilinForm ℂ (degreeLT ℂ r) :=
  LinearMap.mk₂ ℂ (fun P Q => ∫ x in Icc (0 : ℝ) 1, polyFun P x * polyFun Q x)
    (fun P₁ P₂ Q => by
      simp only [Submodule.coe_add, polyFun_add, add_mul]
      exact integral_add (integrableOn_polyFun_mul _ _) (integrableOn_polyFun_mul _ _))
    (fun c P Q => by
      simp only [Submodule.coe_smul, polyFun_smul, mul_assoc, smul_eq_mul]
      exact integral_const_mul c _)
    (fun P Q₁ Q₂ => by
      simp only [Submodule.coe_add, polyFun_add, mul_add]
      exact integral_add (integrableOn_polyFun_mul _ _) (integrableOn_polyFun_mul _ _))
    (fun c P Q => by
      simp only [Submodule.coe_smul, polyFun_smul, mul_left_comm _ c, smul_eq_mul]
      exact integral_const_mul c _)

/-- `⟨P, Q⟩ = ∫_0^1 P Q`. -/
theorem polyPairing_apply (r : ℕ) (P Q : degreeLT ℂ r) :
    polyPairing r P Q = ∫ x in Icc (0 : ℝ) 1, polyFun P x * polyFun Q x := rfl

/-- The pairing is symmetric. -/
theorem polyPairing_comm (r : ℕ) (P Q : degreeLT ℂ r) : polyPairing r P Q = polyPairing r Q P := by
  simp only [polyPairing_apply, mul_comm]

/-- **The pairing separates points**: if `∫_0^1 P Q = 0` for all `Q`, then `P = 0`; take
`Q = PBar`, so that `∫_0^1 |P|² = 0`. -/
theorem polyPairing_separatingLeft (r : ℕ) : (polyPairing r).SeparatingLeft := by
  intro P hP
  have hmem : (P : ℂ[X]).map (starRingEnd ℂ) ∈ degreeLT ℂ r :=
    mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 P.2))
  have h := hP ⟨_, hmem⟩
  rw [polyPairing_apply] at h
  simp only [polyFun_map_conj, Complex.mul_conj] at h
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hint : IntegrableOn (fun x => Complex.normSq (polyFun P x)) (Icc (0 : ℝ) 1) :=
    (Complex.continuous_normSq.comp (continuous_polyFun P)).integrableOn_Icc
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _) hint).1 h
  have hP0 : polyFun P =ᵐ[volume.restrict (Icc 0 1)] 0 :=
    hae.mono fun x hx => Complex.normSq_eq_zero.1 hx
  exact Subtype.ext (eq_zero_of_ae_eq_zero zero_lt_one hP0)

/-- The pairing is nondegenerate. -/
theorem polyPairing_nondegenerate (r : ℕ) : (polyPairing r).Nondegenerate :=
  ⟨polyPairing_separatingLeft r, fun P hP =>
    polyPairing_separatingLeft r P fun Q => by rw [polyPairing_comm]; exact hP Q⟩

/-- The **monomial basis** `b_i = X^i` of the polynomials of degree `< r`. -/
noncomputable def monoBasis (r : ℕ) : Module.Basis (Fin r) ℂ (degreeLT ℂ r) :=
  Module.Basis.ofEquivFun (degreeLTEquiv ℂ r)

/-- The **dual basis** `d_i` of the monomials for the pairing `∫_0^1 P Q`. -/
noncomputable def dualPoly (r : ℕ) : Module.Basis (Fin r) ℂ (degreeLT ℂ r) :=
  (polyPairing r).dualBasis (polyPairing_nondegenerate r) (monoBasis r)

/-- **Expansion in the dual basis**: `P = ∑_i ⟨P, b_i⟩ d_i` for every `P` of degree `< r`. -/
theorem sum_polyPairing_smul_dualPoly (r : ℕ) (P : degreeLT ℂ r) :
    ∑ i, polyPairing r P (monoBasis r i) • dualPoly r i = P := by
  conv_rhs => rw [← (dualPoly r).sum_repr P]
  simp only [dualPoly, LinearMap.BilinForm.dualBasis_repr_apply]

/-- The expansion at a point: `P(x) = ∑_i (∫_0^1 P b_i) d_i(x)`. -/
theorem polyFun_eq_sum_dualPoly (r : ℕ) (P : degreeLT ℂ r) (x : ℝ) :
    polyFun P x = ∑ i, (∫ t in Icc (0 : ℝ) 1, polyFun P t * polyFun (monoBasis r i) t) *
      polyFun (dualPoly r i) x := by
  conv_lhs => rw [← sum_polyPairing_smul_dualPoly r P]
  simp only [Submodule.coe_sum, Submodule.coe_smul, polyFun, eval_finsetSum, eval_smul,
    smul_eq_mul, polyPairing_apply]

/-! ### Local projections on dyadic intervals -/

/-- A finite family of polynomials is bounded on `[0, 1]`. -/
theorem exists_enorm_polyFun_le_of_fintype {ι : Type*} [Finite ι] (P : ι → ℂ[X]) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun (P i) t‖ₑ ≤ M := by
  let := Fintype.ofFinite ι
  choose C hC using fun i => (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_polyFun (P i)).continuousOn
  refine ⟨∑ i, ENNReal.ofReal (C i), ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top,
    fun i t ht => ?_⟩
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal (hC i t ht)).trans (Finset.single_le_sum
    (f := fun i => ENNReal.ofReal (C i)) (fun _ _ => zero_le) (Finset.mem_univ i))

/-- The coefficients of the local projection of `g` on `I_{j,m}`,
`c_i = 2^j ∫_{I_{j,m}} g(y) b_i(2^j y - m) dy`. -/
noncomputable def locCoeff (r j : ℕ) (g : ℝ → ℂ) (m : ℕ) (i : Fin r) : ℂ :=
  (((2 : ℝ) ^ j : ℝ) : ℂ) *
    ∫ y in dyadicIco j m, g y * polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y)

/-- The **local projection** of `g` on `I_{j,m}`, the polynomial `∑_i c_i d_i(2^j x - m)`. -/
noncomputable def locProj (r j : ℕ) (g : ℝ → ℂ) (m : ℕ) : ℂ[X] :=
  ∑ i, locCoeff r j g m i •
    (dualPoly r i : ℂ[X]).comp (C ((-(m : ℝ) : ℝ) : ℂ) + C (((2 : ℝ) ^ j : ℝ) : ℂ) * X)

/-- The local projection has degree `< r`. -/
theorem locProj_mem (r j : ℕ) (g : ℝ → ℂ) (m : ℕ) : locProj r j g m ∈ degreeLT ℂ r :=
  Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (comp_affine_mem_degreeLT (dualPoly r i).2 _ _)

/-- The values of the local projection, `Π g(x) = ∑_i c_i d_i(2^j x - m)`. -/
theorem polyFun_locProj (r j : ℕ) (g : ℝ → ℂ) (m : ℕ) (x : ℝ) :
    polyFun (locProj r j g m) x =
      ∑ i, locCoeff r j g m i * polyFun (dualPoly r i) (-(m : ℝ) + 2 ^ j * x) := by
  rw [locProj, polyFun, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_smul, smul_eq_mul, ← polyFun, polyFun_comp_affine]

/-- **Polynomials are reproduced**: if `g = Q` on `I_{j,m}` with `Q` of degree `< r`, then the
local projection of `g` on `I_{j,m}` is `Q`. -/
theorem polyFun_locProj_of_eqOn {r j m : ℕ} {g : ℝ → ℂ} {Q : ℂ[X]} (hQ : Q ∈ degreeLT ℂ r)
    (hg : ∀ y ∈ dyadicIco j m, g y = polyFun Q y) (x : ℝ) :
    polyFun (locProj r j g m) x = polyFun Q x := by
  have hQt : Q.comp (C (((m : ℝ) / 2 ^ j : ℝ) : ℂ) + C ((1 / 2 ^ j : ℝ) : ℂ) * X) ∈
      degreeLT ℂ r := comp_affine_mem_degreeLT hQ _ _
  have hcoeff : ∀ i, locCoeff r j g m i = ∫ t in Icc (0 : ℝ) 1,
      polyFun (Q.comp (C (((m : ℝ) / 2 ^ j : ℝ) : ℂ) + C ((1 / 2 ^ j : ℝ) : ℂ) * X)) t *
        polyFun (monoBasis r i) t := fun i => by
    have hcongr : ∫ y in dyadicIco j m, g y * polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y) =
        ∫ y in dyadicIco j m, polyFun Q y * polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y) :=
      setIntegral_congr_fun (measurableSet_dyadicIco j m) fun y hy => by simp only [hg y hy]
    rw [locCoeff, hcongr, integral_dyadicIco_eq]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
    simp only [polyFun_comp_affine]
    rw [show -(m : ℝ) + 2 ^ j * (t / 2 ^ j + m / 2 ^ j) = t by field_simp; ring,
      show (m : ℝ) / 2 ^ j + 1 / 2 ^ j * t = t / 2 ^ j + m / 2 ^ j by ring]
  have hexp := polyFun_eq_sum_dualPoly r ⟨_, hQt⟩ (-(m : ℝ) + 2 ^ j * x)
  simp only at hexp
  rw [polyFun_locProj]
  simp only [hcoeff]
  rw [← hexp, polyFun_comp_affine]
  congr 1
  field_simp
  ring

/-- `2^j (2^(-j))^(1-θ) = 2^(jθ)`. -/
theorem ofReal_two_pow_mul_inv_rpow (j : ℕ) (θ : ℝ) :
    ENNReal.ofReal (2 ^ j) * ENNReal.ofReal (1 / 2 ^ j) ^ (1 - θ) =
      ENNReal.ofReal (2 ^ j) ^ θ := by
  have hx0 : ENNReal.ofReal (2 ^ j) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hxt : ENNReal.ofReal (2 ^ j) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  calc ENNReal.ofReal (2 ^ j) * ENNReal.ofReal (2 ^ j) ^ (-(1 - θ))
      = ENNReal.ofReal (2 ^ j) ^ (1 : ℝ) * ENNReal.ofReal (2 ^ j) ^ (-(1 - θ)) := by
        rw [ENNReal.rpow_one]
    _ = ENNReal.ofReal (2 ^ j) ^ (1 + -(1 - θ)) := (ENNReal.rpow_add _ _ hx0 hxt).symm
    _ = ENNReal.ofReal (2 ^ j) ^ θ := by congr 1; ring

/-- **Bound for the local coefficients**: `|c_i| ≤ M 2^(j/p) ‖g‖_{L_p(I_{j,m})}` when the
monomials are bounded by `M` on `[0, 1]`. -/
theorem enorm_locCoeff_le {r : ℕ} {M : ℝ≥0∞}
    (hM : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun (monoBasis r i) t‖ₑ ≤ M) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (j m : ℕ) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (dyadicIco j m)))
    (i : Fin r) :
    ‖locCoeff r j g m i‖ₑ ≤
      M * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * eLpNorm g p (volume.restrict (dyadicIco j
        m)) := by
  have h1 : ‖∫ y in dyadicIco j m, g y * polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y)‖ₑ ≤
      (∫⁻ y in dyadicIco j m, ‖g y‖ₑ) * M := by
    refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
    rw [← lintegral_mul_const'' M hg.eNorm]
    refine setLIntegral_mono' (measurableSet_dyadicIco j m) fun y hy => ?_
    rw [eNorm_mul]
    gcongr
    refine hM i _ ⟨?_, ?_⟩ <;> rw [mem_dyadicIco] at hy <;> linarith [hy.1, hy.2]
  have h2 : ∫⁻ y in dyadicIco j m, ‖g y‖ₑ ≤
      eLpNorm g p (volume.restrict (dyadicIco j m)) * ENNReal.ofReal (1 / 2 ^ j) ^ (1 - 1 /
        p.toReal) := by
    rw [← eLpNorm_one_eq_lintegral_eNorm hg]
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg
    rwa [Measure.restrict_apply_univ, volume_dyadicIco, ENNReal.toReal_one, div_one] at this
  rw [locCoeff, eNorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  calc ENNReal.ofReal (2 ^ j) * ‖∫ y in dyadicIco j m,
        g y * polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y)‖ₑ
      ≤ ENNReal.ofReal (2 ^ j) * ((eLpNorm g p (volume.restrict (dyadicIco j m)) *
          ENNReal.ofReal (1 / 2 ^ j) ^ (1 - 1 / p.toReal)) * M) := by
        gcongr
        exact h1.trans (mul_le_mul' h2 le_rfl)
    _ = M * (ENNReal.ofReal (2 ^ j) * ENNReal.ofReal (1 / 2 ^ j) ^ (1 - 1 / p.toReal)) *
          eLpNorm g p (volume.restrict (dyadicIco j m)) := by ring
    _ = _ := by rw [ofReal_two_pow_mul_inv_rpow]

/-- **Pointwise bound for the local projection**: on `I_{j,m}`,
`|Π g(x)| ≤ r M² 2^(j/p) ‖g‖_{L_p(I_{j,m})}` when the monomials and the dual basis are bounded by
`M` on `[0, 1]`. -/
theorem enorm_polyFun_locProj_le {r : ℕ} {M : ℝ≥0∞}
    (hMb : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun (monoBasis r i) t‖ₑ ≤ M)
    (hMd : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun (dualPoly r i) t‖ₑ ≤ M) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (j m : ℕ) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (dyadicIco j m)))
    {x : ℝ} (hx : x ∈ dyadicIco j m) :
    ‖polyFun (locProj r j g m) x‖ₑ ≤
      r * M * M * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
        eLpNorm g p (volume.restrict (dyadicIco j m)) := by
  have hxt : -(m : ℝ) + 2 ^ j * x ∈ Icc (0 : ℝ) 1 := by
    rw [mem_dyadicIco] at hx
    constructor <;> linarith [hx.1, hx.2]
  rw [polyFun_locProj]
  refine (eNorm_sum_le _ _).trans ?_
  calc ∑ i, ‖locCoeff r j g m i * polyFun (dualPoly r i) (-(m : ℝ) + 2 ^ j * x)‖ₑ
      ≤ ∑ _i : Fin r, M * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
          eLpNorm g p (volume.restrict (dyadicIco j m)) * M :=
        Finset.sum_le_sum fun i _ => by
          rw [eNorm_mul]
          exact mul_le_mul' (enorm_locCoeff_le hMb hp j m hg i) (hMd i _ hxt)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The local projection is bounded in `L_p(I_{j,m})`**:
`‖Π g‖_{L_p(I_{j,m})} ≤ r M² ‖g‖_{L_p(I_{j,m})}`, with a constant independent of `j` and `m`. -/
theorem eLpNorm_locProj_le {r : ℕ} {M : ℝ≥0∞}
    (hMb : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun (monoBasis r i) t‖ₑ ≤ M)
    (hMd : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ‖polyFun (dualPoly r i) t‖ₑ ≤ M) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (j m : ℕ) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (dyadicIco j m))) :
    eLpNorm (polyFun (locProj r j g m)) p (volume.restrict (dyadicIco j m)) ≤
      r * M * M * eLpNorm g p (volume.restrict (dyadicIco j m)) := by
  have hθ : 0 ≤ 1 / p.toReal := by positivity
  refine (eLpNorm_le_of_ae_eNorm_bound (measurable_polyFun _).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_dyadicIco j m)).2 (Filter.Eventually.of_forall
      fun x hx => enorm_polyFun_locProj_le hMb hMd hp j m hg hx))).trans_eq ?_
  rw [Measure.restrict_apply_univ, volume_dyadicIco, smul_eq_mul, ← one_div]
  have h1 : ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) * ENNReal.ofReal (1 / 2 ^ j) ^ (1 / p.toReal) =
      1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ, ← ENNReal.ofReal_mul (by positivity),
      mul_one_div_cancel (by positivity), ENNReal.ofReal_one, ENNReal.one_rpow]
  calc r * M * M * ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
        eLpNorm g p (volume.restrict (dyadicIco j m)) * ENNReal.ofReal (1 / 2 ^ j) ^ (1 / p.toReal)
      = r * M * M * (ENNReal.ofReal (2 ^ j) ^ (1 / p.toReal) *
          ENNReal.ofReal (1 / 2 ^ j) ^ (1 / p.toReal)) *
          eLpNorm g p (volume.restrict (dyadicIco j m)) := by ring
    _ = _ := by rw [h1, mul_one]

/-! ### Linearity of the local projection -/

/-- The local integrands `g(y) b_i(2^j y - m)` are integrable on `I_{j,m}`. -/
theorem integrableOn_mul_monoBasis {r j m : ℕ} {g : ℝ → ℂ} (hg : IntegrableOn g (dyadicIco j m))
    (i : Fin r) :
    IntegrableOn (fun y => g y * polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y))
      (dyadicIco j m) := by
  obtain ⟨M, hM, hMb⟩ := exists_enorm_polyFun_le_of_fintype (fun i => (monoBasis r i : ℂ[X]))
  have hc : Continuous fun y : ℝ => polyFun (monoBasis r i) (-(m : ℝ) + 2 ^ j * y) :=
    (continuous_polyFun _).comp (by fun_prop)
  refine hg.mul_bdd (c := M.toReal) hc.aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_dyadicIco j m)).2 (Filter.Eventually.of_forall
      fun y hy => ?_))
  have hyt : -(m : ℝ) + 2 ^ j * y ∈ Icc (0 : ℝ) 1 := by
    rw [mem_dyadicIco] at hy
    constructor <;> linarith [hy.1, hy.2]
  have h := hMb i _ hyt
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hM).1 h

/-- The local coefficients are additive. -/
theorem locCoeff_add {r j m : ℕ} {g₁ g₂ : ℝ → ℂ} (h₁ : IntegrableOn g₁ (dyadicIco j m))
    (h₂ : IntegrableOn g₂ (dyadicIco j m)) (i : Fin r) :
    locCoeff r j (g₁ + g₂) m i = locCoeff r j g₁ m i + locCoeff r j g₂ m i := by
  simp only [locCoeff, Pi.add_apply, add_mul]
  rw [integral_add (integrableOn_mul_monoBasis h₁ i) (integrableOn_mul_monoBasis h₂ i), mul_add]

/-- The local coefficients are homogeneous. -/
theorem locCoeff_const_mul (r j m : ℕ) (c : ℂ) (g : ℝ → ℂ) (i : Fin r) :
    locCoeff r j (fun y => c * g y) m i = c * locCoeff r j g m i := by
  simp only [locCoeff, mul_assoc]
  rw [integral_const_mul]
  ring

/-- The local coefficients only see `g` almost everywhere on `I_{j,m}`. -/
theorem locCoeff_congr {r j m : ℕ} {g₁ g₂ : ℝ → ℂ}
    (h : g₁ =ᵐ[volume.restrict (dyadicIco j m)] g₂) (i : Fin r) :
    locCoeff r j g₁ m i = locCoeff r j g₂ m i := by
  rw [locCoeff, locCoeff]
  congr 1
  refine integral_congr_ae (h.mono fun y hy => ?_)
  simp only [hy]

/-- The local projection is additive. -/
theorem locProj_add {r j m : ℕ} {g₁ g₂ : ℝ → ℂ} (h₁ : IntegrableOn g₁ (dyadicIco j m))
    (h₂ : IntegrableOn g₂ (dyadicIco j m)) :
    locProj r j (g₁ + g₂) m = locProj r j g₁ m + locProj r j g₂ m := by
  simp only [locProj, locCoeff_add h₁ h₂, add_smul, Finset.sum_add_distrib]

/-- The local projection is homogeneous. -/
theorem locProj_const_mul (r j m : ℕ) (c : ℂ) (g : ℝ → ℂ) :
    locProj r j (fun y => c * g y) m = C c * locProj r j g m := by
  rw [locProj, locProj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [locCoeff_const_mul, mul_smul, smul_eq_C_mul c]

/-- The local projection only sees `g` almost everywhere on `I_{j,m}`. -/
theorem locProj_congr {r j m : ℕ} {g₁ g₂ : ℝ → ℂ}
    (h : g₁ =ᵐ[volume.restrict (dyadicIco j m)] g₂) : locProj r j g₁ m = locProj r j g₂ m := by
  simp only [locProj, locCoeff_congr h]

/-! ### Orthogonality of the local projection -/

/-- **The moments of the local projection**: `Π g` and `g` have the same moments
`∫_{I_{j,m}} · b_l(2^j x - m)` against the monomials `b_l` in the coordinate of the interval,
since `⟨d_i, b_l⟩ = δ_{il}`. -/
theorem integral_locProj_mul_monoBasis (r j m : ℕ) (g : ℝ → ℂ) (l : Fin r) :
    ∫ x in dyadicIco j m, polyFun (locProj r j g m) x *
        polyFun (monoBasis r l) (-(m : ℝ) + 2 ^ j * x) =
      ∫ x in dyadicIco j m, g x * polyFun (monoBasis r l) (-(m : ℝ) + 2 ^ j * x) := by
  have h2 : (((2 : ℝ) ^ j : ℝ) : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
  refine mul_left_cancel₀ h2 ?_
  rw [show (((2 : ℝ) ^ j : ℝ) : ℂ) * ∫ x in dyadicIco j m, g x *
      polyFun (monoBasis r l) (-(m : ℝ) + 2 ^ j * x) = locCoeff r j g m l from rfl,
    integral_dyadicIco_eq]
  have ht : ∀ t : ℝ, -(m : ℝ) + 2 ^ j * (t / 2 ^ j + m / 2 ^ j) = t := fun t => by
    field_simp
    ring
  simp only [polyFun_locProj, ht, Finset.sum_mul]
  have hdual : ∀ i, ∫ t in Icc (0 : ℝ) 1, polyFun (dualPoly r i) t * polyFun (monoBasis r l) t =
      if l = i then 1 else 0 := fun i =>
    LinearMap.BilinForm.apply_dualBasis_left (polyPairing_nondegenerate r) (monoBasis r) i l
  rw [integral_finsetSum _ fun i _ => by
    simpa only [mul_assoc] using (integrableOn_polyFun_mul (dualPoly r i : ℂ[X])
      (monoBasis r l : ℂ[X])).const_mul (locCoeff r j g m i)]
  simp only [mul_assoc, integral_const_mul, hdual, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **The local projection is the `L_2(I_{j,m})`-orthogonal projection** onto the polynomials of
degree `< r`: `∫_{I_{j,m}} (g - Π g) Q = 0` for every polynomial `Q` of degree `< r`, since `Q`
is a combination of the monomials in the coordinate of the interval. -/
theorem integral_sub_locProj_mul {r j m : ℕ} {g : ℝ → ℂ} (hg : IntegrableOn g (dyadicIco j m))
    {Q : ℂ[X]} (hQ : Q ∈ degreeLT ℂ r) :
    ∫ x in dyadicIco j m, (g x - polyFun (locProj r j g m) x) * polyFun Q x = 0 := by
  set R : ℂ[X] := Q.comp (C ((((m : ℝ) / 2 ^ j : ℝ)) : ℂ) + C (((1 / 2 ^ j : ℝ)) : ℂ) * X)
  have hR : R ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hQ _ _
  set a := (monoBasis r).repr ⟨R, hR⟩
  have hQx : ∀ x : ℝ, polyFun Q x =
      ∑ l, a l * polyFun (monoBasis r l) (-(m : ℝ) + 2 ^ j * x) := fun x => by
    have hval : polyFun R (-(m : ℝ) + 2 ^ j * x) = polyFun Q x := by
      rw [polyFun_comp_affine]
      congr 1
      field_simp
      ring
    rw [← hval]
    conv_lhs => rw [show R = ((⟨R, hR⟩ : degreeLT ℂ r) : ℂ[X]) from rfl,
      ← (monoBasis r).sum_repr ⟨R, hR⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, polyFun, eval_finsetSum, eval_smul,
      smul_eq_mul, a]
  have hPg : IntegrableOn (polyFun (locProj r j g m)) (dyadicIco j m) :=
    integrableOn_dyadicIco_of_continuous (continuous_polyFun _) j m
  have hint : ∀ l, IntegrableOn (fun x => (g x - polyFun (locProj r j g m) x) *
      polyFun (monoBasis r l) (-(m : ℝ) + 2 ^ j * x)) (dyadicIco j m) := fun l => by
    simp only [sub_mul]
    exact (integrableOn_mul_monoBasis hg l).sub (integrableOn_mul_monoBasis hPg l)
  simp only [hQx, Finset.mul_sum]
  rw [integral_finsetSum _ fun l _ => by
    simpa only [mul_left_comm _ (a l)] using (hint l).const_mul (a l)]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [mul_left_comm _ (a l)]
  rw [integral_const_mul, mul_eq_zero]
  right
  simp only [sub_mul]
  rw [integral_sub (integrableOn_mul_monoBasis hg l) (integrableOn_mul_monoBasis hPg l),
    integral_locProj_mul_monoBasis, sub_self]

/-- **The local projections reproduce piecewise polynomials exactly**:
`P_j (ppFun j Q) = ppFun j Q` as functions, for pieces of degree `< r`. -/
theorem ppFun_locProj_ppFun {r j : ℕ} {Q : ℕ → ℂ[X]} (hQ : ∀ n, Q n ∈ degreeLT ℂ r) :
    ppFun j (locProj r j (ppFun j Q)) = ppFun j Q :=
  ppFun_congr fun n hn => by
    funext x
    exact polyFun_locProj_of_eqOn (hQ n) (fun y hy => ppFun_eq_of_mem Q hn hy) x

/-! ### The projections onto piecewise polynomials -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common bound for the monomials and the dual basis on `[0, 1]`. -/
noncomputable def basisBound (r : ℕ) : ℝ≥0∞ :=
  (exists_enorm_polyFun_le_of_fintype (fun i : Fin r ⊕ Fin r =>
    Sum.elim (fun i => (monoBasis r i : ℂ[X])) (fun i => (dualPoly r i : ℂ[X])) i)).choose

/-- The basis bound is finite. -/
theorem basisBound_ne_top (r : ℕ) : basisBound r ≠ ∞ :=
  (exists_enorm_polyFun_le_of_fintype _).choose_spec.1

/-- The monomials are bounded by `basisBound r` on `[0, 1]`. -/
theorem enorm_monoBasis_le (r : ℕ) (i : Fin r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖polyFun (monoBasis r i) t‖ₑ ≤ basisBound r :=
  (exists_enorm_polyFun_le_of_fintype (fun i : Fin r ⊕ Fin r =>
    Sum.elim (fun i => (monoBasis r i : ℂ[X])) (fun i => (dualPoly r i : ℂ[X])) i)).choose_spec.2
      (Sum.inl i) t ht

/-- The dual basis is bounded by `basisBound r` on `[0, 1]`. -/
theorem enorm_dualPoly_le (r : ℕ) (i : Fin r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖polyFun (dualPoly r i) t‖ₑ ≤ basisBound r :=
  (exists_enorm_polyFun_le_of_fintype (fun i : Fin r ⊕ Fin r =>
    Sum.elim (fun i => (monoBasis r i : ℂ[X])) (fun i => (dualPoly r i : ℂ[X])) i)).choose_spec.2
      (Sum.inr i) t ht

/-- The bound of the projections onto piecewise polynomials, `r M²`. -/
noncomputable def ppProjConst (r : ℕ) : ℝ≥0∞ := r * basisBound r * basisBound r

/-- The bound of the projections is finite. -/
theorem ppProjConst_ne_top (r : ℕ) : ppProjConst r ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top r) (basisBound_ne_top r))
    (basisBound_ne_top r)

omit [Fact (1 ≤ p)] in
/-- **The projections onto piecewise polynomials are uniformly bounded**:
`‖P_j g‖_{L_p[0,1]} ≤ r M² ‖g‖_{L_p[0,1]}` for `1 ≤ p < ∞`, with `P_j g` the local projections
of `g` on the dyadic intervals of level `j`. -/
theorem eLpNorm_ppFun_locProj_le (hp : 1 ≤ p) (hp' : p ≠ ∞) (r j : ℕ) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g unitVol) :
    eLpNorm (ppFun j (locProj r j g)) p unitVol ≤ ppProjConst r * eLpNorm g p unitVol := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  refine eLpNorm_le_of_lintegral_le (measurable_ppFun _ _).aestronglyMeasurable hp0 hp' ?_
  have hpiece : ∀ n ∈ Finset.range (2 ^ j),
      ∫⁻ x in dyadicIco j n, ‖ppFun j (locProj r j g) x‖ₑ ^ p.toReal ≤
        ppProjConst r ^ p.toReal * ∫⁻ x in dyadicIco j n, ‖g x‖ₑ ^ p.toReal := fun n hn => by
    have hn' := Finset.mem_range.1 hn
    have hgI : AEStronglyMeasurable g (volume.restrict (dyadicIco j n)) :=
      hg.mono_measure (Measure.restrict_mono
        ((dyadicIco_subset hn').trans Ico_subset_Icc_self) le_rfl)
    rw [setLIntegral_congr_fun (measurableSet_dyadicIco j n)
        (fun x hx => by rw [ppFun_eq_of_mem _ hn' hx]),
      ← eLpNorm_rpow_eq (measurable_polyFun _).aestronglyMeasurable hp0 hp',
      ← eLpNorm_rpow_eq hgI hp0 hp', ← ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    exact ENNReal.rpow_le_rpow (eLpNorm_locProj_le (enorm_monoBasis_le r) (enorm_dualPoly_le r)
      hp j n hgI) hq.le
  calc ∫⁻ x, ‖ppFun j (locProj r j g) x‖ₑ ^ p.toReal ∂unitVol
      ≤ ∑ n ∈ Finset.range (2 ^ j),
          ∫⁻ x in dyadicIco j n, ‖ppFun j (locProj r j g) x‖ₑ ^ p.toReal :=
        lintegral_Icc_le_sum_dyadicIco _ j
    _ ≤ ∑ n ∈ Finset.range (2 ^ j), ppProjConst r ^ p.toReal *
          ∫⁻ x in dyadicIco j n, ‖g x‖ₑ ^ p.toReal := Finset.sum_le_sum hpiece
    _ ≤ ppProjConst r ^ p.toReal * ∫⁻ x in Icc (0 : ℝ) 1, ‖g x‖ₑ ^ p.toReal := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_lintegral_dyadicIco_le _ j
    _ = (ppProjConst r * eLpNorm g p unitVol) ^ p.toReal := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, eLpNorm_rpow_eq hg hp0 hp']

variable (p) in
/-- The projection onto the piecewise polynomials of level `j`, as a linear map on `L_p[0, 1]`:
on every dyadic interval of level `j` it is the local projection. -/
noncomputable def ppProjLinear (r j : ℕ) : Lp ℂ p unitVol →ₗ[ℝ] Lp ℂ p unitVol where
  toFun f := (memLp_ppFun j (locProj r j f) p).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    rw [← ppFun_add]
    refine congrFun (ppFun_congr fun n hn => ?_) x
    rw [Pi.add_apply, locProj_congr (ae_dyadicIco_of_unitVol (Lp.coeFn_add f g) hn),
      locProj_add (integrableOn_dyadicIco f hn) (integrableOn_dyadicIco g hn)]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
    have hcf : ⇑(c • f) =ᵐ[unitVol] fun y => (c : ℂ) * f y :=
      (Lp.coeFn_smul c f).mono fun y hy => by rw [hy, Pi.smul_apply, Complex.real_smul]
    rw [Pi.smul_apply, Complex.real_smul, show (c : ℂ) * ppFun j (locProj r j f) x =
      ppFun j (fun n => C (c : ℂ) * locProj r j f n) x from
        (congrFun (ppFun_const_mul j (c : ℂ) _) x).symm]
    refine congrFun (ppFun_congr fun n hn => ?_) x
    rw [locProj_congr (ae_dyadicIco_of_unitVol hcf hn), locProj_const_mul]

variable (p) in
/-- The **projection onto the piecewise polynomials of level `j`** in `L_p[0, 1]`,
`1 ≤ p < ∞`, a bounded operator with norm at most `r M²`. -/
noncomputable def ppProj (hp : p ≠ ∞) (r j : ℕ) : Lp ℂ p unitVol →L[ℝ] Lp ℂ p unitVol :=
  LinearMap.mkContinuous (ppProjLinear p r j) (ppProjConst r).toReal fun f => by
    rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ppProjConst_ne_top r)
      (Lp.eLpNorm_ne_top f)) ?_
    rw [show (ppProjLinear p r j) f = (memLp_ppFun j (locProj r j f) p).toLp _ from rfl,
      eLpNorm_congr_ae (MemLp.coeFn_toLp (memLp_ppFun j (locProj r j f) p))]
    exact eLpNorm_ppFun_locProj_le Fact.out hp r j (Lp.aestronglyMeasurable f)

/-- The projection agrees almost everywhere with the piecewise local projections. -/
theorem coeFn_ppProj (hp : p ≠ ∞) (r j : ℕ) (f : Lp ℂ p unitVol) :
    ppProj p hp r j f =ᵐ[unitVol] ppFun j (locProj r j f) :=
  MemLp.coeFn_toLp (memLp_ppFun j (locProj r j f) p)

/-- The projection has norm at most `r M²`. -/
theorem norm_ppProj_le (hp : p ≠ ∞) (r j : ℕ) : ‖ppProj p hp r j‖ ≤ (ppProjConst r).toReal :=
  LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

/-- The projection maps into the piecewise polynomials of level `j`. -/
theorem ppProj_mem (hp : p ≠ ∞) (r j : ℕ) (f : Lp ℂ p unitVol) :
    ppProj p hp r j f ∈ ppSpace p r j :=
  ⟨locProj r j f, fun m => locProj_mem r j f m, coeFn_ppProj hp r j f⟩

/-- **The projection fixes the piecewise polynomials of level `j`.** -/
theorem ppProj_of_mem (hp : p ≠ ∞) {r j : ℕ} {a : Lp ℂ p unitVol} (ha : a ∈ ppSpace p r j) :
    ppProj p hp r j a = a := by
  obtain ⟨Q, hQ, hae⟩ := ha
  have hfun : ppFun j (locProj r j a) = ppFun j Q := ppFun_congr fun n hn => by
    funext x
    rw [locProj_congr (ae_dyadicIco_of_unitVol hae hn)]
    exact polyFun_locProj_of_eqOn (hQ n) (fun y hy => ppFun_eq_of_mem Q hn hy) x
  exact Lp.ext ((coeFn_ppProj hp r j a).trans ((Filter.EventuallyEq.of_eq hfun).trans hae.symm))

/-- **The projection scheme of dyadic piecewise polynomials** in `L_p[0, 1]`, `1 ≤ p < ∞`: the
projection of complexity `n ≥ 1` is the one onto the piecewise polynomials of level
`⌊log₂ n⌋`, and all are bounded by `r M²`. -/
noncomputable def ppProjectionScheme (hp : p ≠ ∞) (r : ℕ) : (ppScheme p r).ProjectionScheme :=
  ApproximationScheme.ProjectionScheme.ofMonotone (ppSpace p r) (ppSpace_mono r) (ppProj p hp r)
    (ppProj_mem hp r) (fun _ _ ha => ppProj_of_mem hp ha) (ppProjConst r).toReal
    (norm_ppProj_le hp r)

/-- The projection of complexity `2^k` is the one onto the piecewise polynomials of level `k`. -/
theorem ppProjectionScheme_two_pow (hp : p ≠ ∞) (r k : ℕ) :
    (ppProjectionScheme hp r).P (2 ^ k) = ppProj p hp r k :=
  ApproximationScheme.ProjectionScheme.ofMonotone_two_pow k

end Interval
