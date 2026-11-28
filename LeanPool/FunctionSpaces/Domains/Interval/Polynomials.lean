/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Modulus
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Polynomials on intervals

The polynomials of degree `< r` with complex coefficients, `Polynomial.degreeLT ℂ r`, evaluated
at real points (`Interval.polyFun`), form a space of dimension `r` (`Interval.finrank_degreeLT`,
from Mathlib's monomial basis `Polynomial.degreeLT.basis`).  On such a space all norms are
equivalent, and with an affine change of variables this gives the **Nikolskii inequality for
polynomials on intervals** (`Interval.enorm_polyFun_le`): for `1 ≤ p < ∞` there is `K` with

`|P(x)| ≤ K L^(-1/p) ‖P‖_{L_p[u, u + L]}`   for `x ∈ [u, u + 2L]`, `P` of degree `< r`

(`Interval.NikolskiiBound`).  The bound reaches the doubled interval, so that one piece of a
piecewise polynomial also controls its values on the neighbouring interval.

The equivalence of norms is Mathlib's `LinearMap.injective_iff_antilipschitz` for the injective
map from the coefficients to `L_p[α, β]` (a nonzero polynomial has only finitely many zeros,
`Polynomial.eq_zero_of_infinite_isRoot`). In coordinates every linear map `Φ` of the polynomials
of degree `< r` into themselves is a linear map of `ℂ^r`, so
`|Φ P(x)| ≤ K ‖P‖_{L_p[α, β]}` for `x ∈ [0, 1]` (`Interval.exists_enorm_linearMap_le_eLpNorm`);
`Φ = id` is the equivalence of norms (`Interval.exists_enorm_le_eLpNorm`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal NNReal

namespace Interval

/-- The function `x ↦ P(x)` on `ℝ` of a complex polynomial `P`. -/
noncomputable def polyFun (P : ℂ[X]) (x : ℝ) : ℂ := P.eval (x : ℂ)

/-- Evaluation is additive. -/
theorem polyFun_add (P Q : ℂ[X]) (x : ℝ) : polyFun (P + Q) x = polyFun P x + polyFun Q x := by
  simp [polyFun]

/-- Evaluation is homogeneous. -/
theorem polyFun_smul (c : ℂ) (P : ℂ[X]) (x : ℝ) : polyFun (c • P) x = c * polyFun P x := by
  simp [polyFun]

/-- Polynomials are continuous. -/
theorem continuous_polyFun (P : ℂ[X]) : Continuous (polyFun P) :=
  (Polynomial.continuous P).comp Complex.continuous_ofReal

/-- Polynomials are measurable. -/
theorem measurable_polyFun (P : ℂ[X]) : Measurable (polyFun P) :=
  (continuous_polyFun P).measurable

/-- The polynomials of degree `< r` form a space of dimension `r` (with Mathlib's monomial basis
`Polynomial.degreeLT.basis`). -/
theorem finrank_degreeLT (r : ℕ) : Module.finrank ℂ (degreeLT ℂ r) = r := by
  rw [Module.finrank_eq_card_basis (degreeLT.basis ℂ r), Fintype.card_fin]

/-- `(P ∘ (u + v X))(y) = P(u + v y)`. -/
theorem polyFun_comp_affine (P : ℂ[X]) (u v y : ℝ) :
    polyFun (P.comp (C (u : ℂ) + C (v : ℂ) * X)) y = polyFun P (u + v * y) := by
  simp [polyFun, eval_comp]

/-- A polynomial vanishing almost everywhere on an interval of positive length is zero. -/
theorem eq_zero_of_ae_eq_zero {P : ℂ[X]} {α β : ℝ} (hαβ : α < β)
    (h : polyFun P =ᵐ[volume.restrict (Icc α β)] 0) : P = 0 := by
  by_contra hP
  have hfin : {x : ℝ | P.eval (x : ℂ) = 0}.Finite := by
    have hroots : {z : ℂ | P.IsRoot z}.Finite := by
      by_contra hinf
      exact hP (P.eq_zero_of_infinite_isRoot hinf)
    exact (hroots.preimage (Complex.ofReal_injective.injOn)).subset fun x hx => hx
  have h0 : volume.restrict (Icc α β) {x : ℝ | P.eval (x : ℂ) = 0}ᶜ = 0 := by
    change volume.restrict (Icc α β) {x : ℝ | ¬ (P.eval (x : ℂ) = 0)} = 0
    rw [← ae_iff]
    filter_upwards [h] with x hx
    simpa [polyFun] using hx
  have h1 : volume.restrict (Icc α β) {x : ℝ | P.eval (x : ℂ) = 0} = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans (hfin.measure_zero volume).le) bot_le
  have htot : volume.restrict (Icc α β) univ = 0 := by
    rw [← union_compl_self {x : ℝ | P.eval (x : ℂ) = 0}]
    exact le_antisymm ((measure_union_le _ _).trans (by rw [h0, h1, add_zero])) bot_le
  rw [Measure.restrict_apply_univ, Real.volume_Icc, ENNReal.ofReal_eq_zero] at htot
  linarith

/-- Polynomials lie in `L_p` of a bounded interval. -/
theorem memLp_polyFun (P : ℂ[X]) (p : ℝ≥0∞) (α β : ℝ) :
    MemLp (polyFun P) p (volume.restrict (Icc α β)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_polyFun P).continuousOn
  refine MemLp.of_bound (measurable_polyFun P).aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hC x hx

/-- The value of the polynomial with coefficients `c`: `∑_i c_i x^i` (Mathlib's
`Polynomial.eval_eq_sum_degreeLTEquiv`). -/
theorem polyFun_degreeLTEquiv_symm (r : ℕ) (c : Fin r → ℂ) (x : ℝ) :
    polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) x = ∑ i : Fin r, c i * (x : ℂ) ^ (i : ℕ) := by
  rw [polyFun, eval_eq_sum_degreeLTEquiv ((degreeLTEquiv ℂ r).symm c).2, Subtype.coe_eta,
    LinearEquiv.apply_symm_apply]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The map from the coefficients of a polynomial of degree `< r` to its class in
`L_p[α, β]`. -/
noncomputable def coeffToLp (r : ℕ) (α β : ℝ) :
    (Fin r → ℂ) →ₗ[ℂ] Lp ℂ p (volume.restrict (Icc α β)) where
  toFun c := (memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) p α β).toLp _
  map_add' c d := by
    ext1
    filter_upwards [MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm (c + d) : ℂ[X]) p
      α β), Lp.coeFn_add ((memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) p α β).toLp _)
      ((memLp_polyFun ((degreeLTEquiv ℂ r).symm d : ℂ[X]) p α β).toLp _),
      MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) p α β),
      MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm d : ℂ[X]) p α β)]
      with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, polyFun_degreeLTEquiv_symm, polyFun_degreeLTEquiv_symm,
      polyFun_degreeLTEquiv_symm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, add_mul]
  map_smul' a c := by
    ext1
    filter_upwards [MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm (a • c) : ℂ[X]) p
      α β), Lp.coeFn_smul a ((memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) p α β).toLp _),
      MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) p α β)]
      with x h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, polyFun_degreeLTEquiv_symm,
      polyFun_degreeLTEquiv_symm, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The norm of `coeffToLp` is the `L_p` norm of the polynomial. -/
theorem enorm_coeffToLp (r : ℕ) (α β : ℝ) (c : Fin r → ℂ) :
    ‖coeffToLp p r α β c‖ₑ =
      eLpNorm (polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X])) p (volume.restrict (Icc α β)) := by
  rw [Lp.eNorm_def]
  exact eLpNorm_congr_ae (MemLp.coeFn_toLp (memLp_polyFun _ p α β))

omit [Fact (1 ≤ p)] in
/-- `coeffToLp` is injective on an interval of positive length. -/
theorem coeffToLp_injective (r : ℕ) {α β : ℝ} (hαβ : α < β) :
    Function.Injective (coeffToLp p r α β) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have hae : polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) =ᵐ[volume.restrict (Icc α β)] 0 := by
    have h := MemLp.coeFn_toLp (memLp_polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) p α β)
    have h0 : (coeffToLp p r α β c : ℝ → ℂ) =ᵐ[volume.restrict (Icc α β)] 0 := by
      rw [hc]; exact Lp.coeFn_zero _ _ _
    exact h.symm.trans h0
  have hP := eq_zero_of_ae_eq_zero hαβ hae
  have : (degreeLTEquiv ℂ r).symm c = 0 := Subtype.ext hP
  simpa using congrArg (degreeLTEquiv ℂ r) this

/-- The value of a polynomial with coefficients `c` at `x ∈ [0, 1]` is at most `r ‖c‖`. -/
theorem norm_polyFun_degreeLTEquiv_symm_le (r : ℕ) (c : Fin r → ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖polyFun ((degreeLTEquiv ℂ r).symm c : ℂ[X]) x‖ ≤ r * ‖c‖ := by
  have hx1 : ‖(x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]; exact hx.2
  rw [polyFun_degreeLTEquiv_symm]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin r, ‖c i * (x : ℂ) ^ (i : ℕ)‖ ≤ ∑ _i : Fin r, ‖c‖ :=
        Finset.sum_le_sum fun i _ => by
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx1)
            |>.trans (norm_le_pi_norm c i)
    _ = r * ‖c‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Linear maps of polynomials are bounded by the norm**: let `Φ` be a linear map of the
polynomials that preserves the degree bound `< r`, and `[α, β]` an interval of positive length.
There is `K` with `|Φ P(x)| ≤ K ‖P‖_{L_p[α, β]}` for all `x ∈ [0, 1]` and `P` of degree `< r`. In
coordinates `Φ` is a linear map of `ℂ^r`, hence bounded, and the coordinates are bounded by the
`L_p` norm, since `coeffToLp` is injective on a space of finite dimension. -/
theorem exists_enorm_linearMap_le_eLpNorm (r : ℕ) (Φ : ℂ[X] →ₗ[ℂ] ℂ[X])
    (hΦ : ∀ P ∈ degreeLT ℂ r, Φ P ∈ degreeLT ℂ r) {α β : ℝ} (hαβ : α < β) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ P ∈ degreeLT ℂ r, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖polyFun (Φ P) x‖ₑ ≤ K * eLpNorm (polyFun P) p (volume.restrict (Icc α β)) := by
  obtain ⟨K, -, hK⟩ := (coeffToLp p r α β).injective_iff_antilipschitz.1
    (coeffToLp_injective r hαβ)
  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) := (degreeLTEquiv ℂ r).toLinearMap ∘ₗ
    (Φ.restrict hΦ) ∘ₗ (degreeLTEquiv ℂ r).symm.toLinearMap
  let T' := LinearMap.toContinuousLinearMap T
  refine ⟨r * (‖T'‖ₑ * K), ENNReal.mul_ne_top (ENNReal.natCast_ne_top r)
    (ENNReal.mul_ne_top eNorm_ne_top ENNReal.coe_ne_top), fun P hP x hx => ?_⟩
  set c := degreeLTEquiv ℂ r ⟨P, hP⟩
  have hPc : ((degreeLTEquiv ℂ r).symm c : ℂ[X]) = P := by simp [c]
  have hΦc : ((degreeLTEquiv ℂ r).symm (T c) : ℂ[X]) = Φ P := by
    simp [T, c, LinearMap.restrict_apply]
  have hbound : ‖c‖ ≤ K * ‖coeffToLp p r α β c‖ :=
    ZeroHomClass.bound_of_antilipschitz (coeffToLp p r α β) hK c
  have hT : ‖T c‖ ≤ ‖T'‖ * ‖c‖ := T'.le_opNorm c
  have hval : ‖polyFun (Φ P) x‖ ≤ r * (‖T'‖ * (K * ‖coeffToLp p r α β c‖)) := by
    rw [← hΦc]
    refine (norm_polyFun_degreeLTEquiv_symm_le r (T c) hx).trans ?_
    gcongr
    exact hT.trans (by gcongr)
  have hval' : ‖polyFun (Φ P) x‖ₑ ≤ r * (‖T'‖ₑ * (K * ‖coeffToLp p r α β c‖ₑ)) := by
    rw [← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖polyFun (Φ P) x‖
        ≤ ENNReal.ofReal (r * (‖T'‖ * (K * ‖coeffToLp p r α β c‖))) := ENNReal.ofReal_le_ofReal hval
      _ = _ := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (norm_nonneg _),
          ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_coe_nnreal, ofReal_norm, ofReal_norm]
  rw [enorm_coeffToLp, hPc] at hval'
  calc ‖polyFun (Φ P) x‖ₑ ≤ r * (‖T'‖ₑ * (K * eLpNorm (polyFun P) p
        (volume.restrict (Icc α β)))) := hval'
    _ = _ := by ring

/-- **Equivalence of norms on polynomials**: for an interval `[α, β]` of positive length there
is `K` with `|P(x)| ≤ K ‖P‖_{L_p[α, β]}` for all `x ∈ [0, 1]` and `P` of degree `< r`, the
case `Φ = id` of `Interval.exists_enorm_linearMap_le_eLpNorm`. -/
theorem exists_enorm_le_eLpNorm (r : ℕ) {α β : ℝ} (hαβ : α < β) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ P ∈ degreeLT ℂ r, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖polyFun P x‖ₑ ≤ K * eLpNorm (polyFun P) p (volume.restrict (Icc α β)) :=
  exists_enorm_linearMap_le_eLpNorm (p := p) r LinearMap.id (fun _ hP => hP) hαβ

/-- **Affine change of variables in `L_p`**: for `L > 0` and `p ≠ ∞`,
`‖g(u + L ·)‖_{L_p[α, β]} = L^(-1/p) ‖g‖_{L_p[u + Lα, u + Lβ]}`. -/
theorem eLpNorm_comp_affine {g : ℝ → ℂ} (hg : Measurable g) {q : ℝ≥0∞} (hq : q ≠ ∞)
    (u : ℝ) {L : ℝ} (hL : 0 < L) (α β : ℝ) :
    eLpNorm (fun y => g (u + L * y)) q (volume.restrict (Icc α β)) =
      ENNReal.ofReal L⁻¹ ^ (1 / q.toReal) *
        eLpNorm g q (volume.restrict (Icc (u + L * α) (u + L * β))) := by
  set φ : ℝ → ℝ := fun y => u + L * y
  have hφ : Measurable φ := (measurable_const_mul L).const_add u
  have hmap : Measure.map φ volume = ENNReal.ofReal L⁻¹ • volume := by
    have h1 : φ = (fun x => u + x) ∘ (fun y => L * y) := rfl
    rw [h1, ← Measure.map_map (measurable_const_add u) (measurable_const_mul L),
      Real.map_volume_mul_left hL.ne', Measure.map_smul, map_add_left_eq_self,
      abs_of_pos (inv_pos.2 hL)]
    exact (measurable_const_add u).aemeasurable
  have hpre : φ ⁻¹' Icc (u + L * α) (u + L * β) = Icc α β := by
    ext y
    simp only [φ, mem_preimage, mem_Icc]
    constructor
    · intro h
      exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
    · intro h
      exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩
  have hres : Measure.map φ (volume.restrict (Icc α β)) =
      ENNReal.ofReal L⁻¹ • volume.restrict (Icc (u + L * α) (u + L * β)) := by
    rw [← hpre, ← Measure.restrict_map hφ measurableSet_Icc, hmap, Measure.restrict_smul]
  have h := eLpNorm_map_measure (g := g) (p := q) (f := φ) (μ := volume.restrict (Icc α β))
    hg.aestronglyMeasurable hφ.aemeasurable
  rw [hres, eLpNorm_smul_measure_of_ne_top hq _ _ hg.aestronglyMeasurable, smul_eq_mul,
    ENNReal.toReal_div, ENNReal.toReal_one] at h
  exact h.symm

omit [Fact (1 ≤ p)] in
variable (p) in
/-- **Nikolskii's bound** with constant `K` for the polynomials of degree `< r`:
`|P(x)| ≤ K L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `x ∈ [u, u + 2L]`. -/
def NikolskiiBound (r : ℕ) (K : ℝ≥0∞) : Prop :=
  ∀ P ∈ degreeLT ℂ r, ∀ (u : ℝ) {L : ℝ}, 0 < L → ∀ x ∈ Icc u (u + 2 * L),
    ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) *
      eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L)))

omit [Fact (1 ≤ p)] in
/-- Nikolskii's bound on the interval `[u, u + L]` itself. -/
theorem NikolskiiBound.enorm_le {r : ℕ} {K : ℝ≥0∞} (hK : NikolskiiBound p r K) {P : ℂ[X]}
    (hP : P ∈ degreeLT ℂ r) (u : ℝ) {L : ℝ} (hL : 0 < L) {x : ℝ} (hx : x ∈ Icc u (u + L)) :
    ‖polyFun P x‖ₑ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) *
      eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) :=
  hK P hP u hL x ⟨hx.1, by linarith [hx.2]⟩

/-- **Nikolskii inequality for polynomials on intervals**: for `1 ≤ p < ∞` there is `K` with
`|P(x)| ≤ K L^(-1/p) ‖P‖_{L_p[u, u + L]}` for `x ∈ [u, u + 2L]` and `P` of degree `< r`. The values
on `[0, 1]` are bounded by the norm on `[0, 1/2]`, and `x ↦ u + 2L x` rescales. -/
theorem enorm_polyFun_le (r : ℕ) (hp : p ≠ ∞) : ∃ K : ℝ≥0∞, K ≠ ∞ ∧ NikolskiiBound p r K := by
  obtain ⟨K, hK, hP⟩ := exists_enorm_le_eLpNorm (p := p) r (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨K, hK, fun P hPr u L hL x hx => ?_⟩
  have h2L : 0 < 2 * L := by positivity
  set Q := P.comp (C (u : ℂ) + C ((2 * L : ℝ) : ℂ) * X)
  have hQ : Q ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hPr _ _
  have hy : (x - u) / (2 * L) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hx.1]) h2L.le
    · rw [div_le_one h2L]; linarith [hx.2]
  have hQx : polyFun Q ((x - u) / (2 * L)) = polyFun P x := by
    rw [polyFun_comp_affine]; congr 1; field_simp; ring
  have hnorm := eLpNorm_comp_affine (measurable_polyFun P) hp u h2L 0 (1 / 2)
  rw [mul_zero, add_zero, show 2 * L * (1 / 2) = L by ring] at hnorm
  have hQfun : (fun y => polyFun P (u + 2 * L * y)) = polyFun Q :=
    funext fun y => (polyFun_comp_affine P u (2 * L) y).symm
  rw [hQfun] at hnorm
  calc ‖polyFun P x‖ₑ = ‖polyFun Q ((x - u) / (2 * L))‖ₑ := by rw [hQx]
    _ ≤ K * eLpNorm (polyFun Q) p (volume.restrict (Icc 0 (1 / 2))) := hP Q hQ _ hy
    _ = K * ENNReal.ofReal (2 * L)⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        rw [hnorm, mul_assoc]
    _ ≤ K * ENNReal.ofReal L⁻¹ ^ (1 / p.toReal) *
          eLpNorm (polyFun P) p (volume.restrict (Icc u (u + L))) := by
        gcongr
        linarith

/-- The polynomial `PBar` with conjugate coefficients takes the values `PBar(x) = conj P(x)` at real
points. -/
theorem polyFun_map_conj (P : ℂ[X]) (x : ℝ) :
    polyFun (P.map (starRingEnd ℂ)) x = starRingEnd ℂ (polyFun P x) := by
  have h : (x : ℂ) = starRingEnd ℂ (x : ℂ) := (Complex.conj_ofReal x).symm
  calc polyFun (P.map (starRingEnd ℂ)) x = P.eval₂ (starRingEnd ℂ) (starRingEnd ℂ (x : ℂ)) := by
        rw [polyFun, eval_map, ← h]
    _ = starRingEnd ℂ (polyFun P x) := eval₂_at_apply _ _

end Interval
