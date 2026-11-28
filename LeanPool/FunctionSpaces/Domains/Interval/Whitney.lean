/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Smoothing

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Whitney's inequality on `[0, 1]`

**Whitney's inequality**: for `1 ≤ p < ∞`, `r ≥ 1` and `0 < t ≤ 1/3` there is `W < ∞` such
that every continuous `F` has a polynomial `P` of degree `< r` with

`‖F - P‖_{L_p[0, 1]} ≤ W ω_r(F, t, [0, 1])_p`

(`Interval.exists_eLpNorm_sub_polyFun_le_modulus`). The best approximation by polynomials on
the whole interval is controlled by the modulus at a single scale `t`.

The proof uses two one-sided smoothings with `L = t` (`Interval.exists_left_smoothing`,
`Interval.exists_right_smoothing`). Together with Taylor's theorem they give polynomials `T₁`
and `T₂` with `‖F - T₁‖ ≤ A ω` on `[0, 1 - t]` and `‖F - T₂‖ ≤ A ω` on `[t, 1]`,
`A = 1 + t^(-r) 2^r r^(2r)` (`Interval.eLpNorm_sub_polyFun_le_of_smoothing`). Both parts contain
`[1/3, 2/3]`, where `T₁` and `T₂` differ by at most `2A ω`; since all norms on the polynomials of
degree `< r` are equivalent, they differ by at most `2K A ω` on `[0, 1]`
(`Interval.exists_eLpNorm_le_middle`). Splitting `[0, 1]` at `1/2` gives `W = (1 + K) 2A`. The
gluing step is stated for any function and any two polynomials
(`Interval.exists_eLpNorm_sub_polyFun_le_glue`), so that the slices of functions on the cube use
it too.

For the dyadic piecewise polynomials and splines of level `0`, the approximants are exactly the
polynomials of degree `< r`, so Whitney's inequality is their Jackson inequality at level `0`.
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Polynomials are controlled by their middle third**: there is `K'` with
`‖P‖_{L_p[0, 1]} ≤ K' ‖P‖_{L_p[1/3, 2/3]}` for every polynomial `P` of degree `< r`, by the
equivalence of norms on the polynomials of degree `< r`. -/
theorem exists_eLpNorm_le_middle (r : ℕ) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ P ∈ degreeLT ℂ r,
      eLpNorm (polyFun P) p (volume.restrict (Icc 0 1)) ≤
        K * eLpNorm (polyFun P) p (volume.restrict (Icc (1 / 3) (2 / 3))) := by
  obtain ⟨K, hK, hKb⟩ := exists_enorm_le_eLpNorm (p := p) r (by norm_num : (1 / 3 : ℝ) < 2 / 3)
  refine ⟨K, hK, fun P hP => ?_⟩
  refine (eLpNorm_le_of_ae_eNorm_bound (measurable_polyFun P).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun x hx => hKb P hP x hx))).trans_eq ?_
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, ENNReal.one_rpow,
    smul_eq_mul, mul_one]

/-- **Taylor approximation on one part**: if `‖g - T‖_{L_p[a,b]} ≤ (b - a)^r ‖D‖_{L_p[a,b]}` and
`b - a ≤ 1`, then `‖F - T‖_{L_p[a,b]} ≤ ‖F - g‖_{L_p[a,b]} + ‖D‖_{L_p[a,b]}`. -/
theorem eLpNorm_sub_polyFun_le_add {F g D : ℝ → ℂ} {r : ℕ} {a b : ℝ} (hab : b - a ≤ 1)
    {T : ℂ[X]}
    (h3 : eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b))) :
    eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
        eLpNorm D p (volume.restrict (Icc a b)) := by
  have hp1 : 1 ≤ p := Fact.out
  have hle : ENNReal.ofReal (b - a) ^ r ≤ 1 := pow_le_one₀ zero_le (ENNReal.ofReal_le_one.2 hab)
  calc eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b))
      = eLpNorm ((fun x => F x - g x) + fun x => g x - polyFun T x) p
          (volume.restrict (Icc a b)) := by congr 1; funext x; simp
    _ ≤ eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) +
          eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) := eLpNorm_add_le hp1
    _ ≤ _ := add_le_add le_rfl (h3.trans (mul_le_of_le_one_left zero_le hle))

/-- **Smoothing and Taylor on one part**: if `‖F - g‖_{L_p[a,b]} ≤ ω`, `‖D‖_{L_p[a,b]} ≤ c ω`,
`‖g - T‖_{L_p[a,b]} ≤ (b - a)^r ‖D‖_{L_p[a,b]}` and `b - a ≤ 1`, then
`‖F - T‖_{L_p[a,b]} ≤ (1 + c) ω`. -/
theorem eLpNorm_sub_polyFun_le_of_smoothing {F g D : ℝ → ℂ} {r : ℕ} {a b : ℝ} (hab : b - a ≤ 1)
    {T : ℂ[X]} {ω c : ℝ≥0∞}
    (h1 : eLpNorm (fun x => F x - g x) p (volume.restrict (Icc a b)) ≤ ω)
    (h2 : eLpNorm D p (volume.restrict (Icc a b)) ≤ c * ω)
    (h3 : eLpNorm (fun x => g x - polyFun T x) p (volume.restrict (Icc a b)) ≤
      ENNReal.ofReal (b - a) ^ r * eLpNorm D p (volume.restrict (Icc a b))) :
    eLpNorm (fun x => F x - polyFun T x) p (volume.restrict (Icc a b)) ≤ (1 + c) * ω :=
  (eLpNorm_sub_polyFun_le_add hab h3).trans ((add_le_add h1 h2).trans_eq (by ring))

/-- **Gluing two polynomial approximations**: there is `K < ∞` such that for measurable `u` and
polynomials `T₁`, `T₂` of degree `< r`,
`‖u - T₁‖_{L_p[0, 1]} ≤ (1 + K) (‖u - T₁‖_{L_p[0, 2/3]} + ‖u - T₂‖_{L_p[1/3, 1]})`. On the
middle third `T₁` and `T₂` are close, hence on all of `[0, 1]`
(`Interval.exists_eLpNorm_le_middle`). -/
theorem exists_eLpNorm_sub_polyFun_le_glue (r : ℕ) (hp : p ≠ ∞) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ {u : ℝ → ℂ}, Measurable u → ∀ {T₁ T₂ : ℂ[X]},
      T₁ ∈ degreeLT ℂ r → T₂ ∈ degreeLT ℂ r →
      eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc 0 1)) ≤
        (1 + K) * (eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc 0 (2 / 3))) +
          eLpNorm (fun x => u x - polyFun T₂ x) p (volume.restrict (Icc (1 / 3) 1))) := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hKb⟩ := exists_eLpNorm_le_middle (p := p) r
  refine ⟨K, hK, fun {u} hu {T₁ T₂} hT₁ hT₂ => ?_⟩
  set E₁ := eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc 0 (2 / 3)))
  set E₂ := eLpNorm (fun x => u x - polyFun T₂ x) p (volume.restrict (Icc (1 / 3) 1))
  have hmid : eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc (1 / 3) (2 / 3))) ≤
      E₂ + E₁ := by
    calc eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc (1 / 3) (2 / 3)))
        = eLpNorm ((fun x => u x - polyFun T₂ x) - fun x => u x - polyFun T₁ x) p
            (volume.restrict (Icc (1 / 3) (2 / 3))) := by
          congr 1; funext x; simp only [Pi.sub_apply, polyFun, eval_sub]; ring
      _ ≤ eLpNorm (fun x => u x - polyFun T₂ x) p (volume.restrict (Icc (1 / 3) (2 / 3))) +
            eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc (1 / 3) (2 / 3))) :=
          eLpNorm_sub_le hp1
      _ ≤ E₂ + E₁ := add_le_add (eLpNorm_Icc_mono _ p le_rfl (by norm_num))
          (eLpNorm_Icc_mono _ p (by norm_num) le_rfl)
  have hdiff : eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc 0 1)) ≤ K * (E₂ + E₁) :=
    (hKb _ (Submodule.sub_mem _ hT₁ hT₂)).trans (mul_le_mul' le_rfl hmid)
  have hL : eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc 0 (1 / 2))) ≤ E₁ :=
    eLpNorm_Icc_mono _ p le_rfl (by norm_num)
  have hR : eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc (1 / 2) 1)) ≤
      E₂ + K * (E₂ + E₁) := by
    calc eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc (1 / 2) 1))
        = eLpNorm ((fun x => u x - polyFun T₂ x) - polyFun (T₁ - T₂)) p
            (volume.restrict (Icc (1 / 2) 1)) := by
          congr 1; funext x; simp only [Pi.sub_apply, polyFun, eval_sub]; ring
      _ ≤ eLpNorm (fun x => u x - polyFun T₂ x) p (volume.restrict (Icc (1 / 2) 1)) +
            eLpNorm (polyFun (T₁ - T₂)) p (volume.restrict (Icc (1 / 2) 1)) := eLpNorm_sub_le hp1
      _ ≤ E₂ + K * (E₂ + E₁) := add_le_add (eLpNorm_Icc_mono _ p (by norm_num) le_rfl)
          ((eLpNorm_Icc_mono _ p (by norm_num) le_rfl).trans hdiff)
  calc eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc 0 1))
      ≤ eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc 0 (1 / 2))) +
          eLpNorm (fun x => u x - polyFun T₁ x) p (volume.restrict (Icc (1 / 2) 1)) :=
        eLpNorm_Icc_split (hu.sub (measurable_polyFun _)) hp1 hp (by norm_num) (by norm_num)
    _ ≤ E₁ + (E₂ + K * (E₂ + E₁)) := add_le_add hL hR
    _ = (1 + K) * (E₁ + E₂) := by ring

/-- **Whitney's inequality for continuous functions**: for `1 ≤ p < ∞`, `r ≥ 1` and
`0 < t ≤ 1/3` there is `W < ∞` such that every continuous `F` has a polynomial `P` of degree
`< r` with `‖F - P‖_{L_p[0, 1]} ≤ W ω_r(F, t, [0, 1])_p`. -/
theorem exists_eLpNorm_sub_polyFun_le_modulus {r : ℕ} (hr : 1 ≤ r) (hp : p ≠ ∞) {t : ℝ}
    (ht : 0 < t) (ht3 : t ≤ 1 / 3) :
    ∃ W : ℝ≥0∞, W ≠ ∞ ∧ ∀ F : ℝ → ℂ, Continuous F → ∃ P ∈ degreeLT ℂ r,
      eLpNorm (fun x => F x - polyFun P x) p (volume.restrict (Icc 0 1)) ≤
        W * modulus r p 0 1 F t := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨K, hK, hKb⟩ := exists_eLpNorm_sub_polyFun_le_glue (p := p) r hp
  set c : ℝ≥0∞ := ENNReal.ofReal t⁻¹ ^ r * (2 ^ r * (r : ℝ≥0∞) ^ (2 * r))
  have hc : c ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top r)))
  refine ⟨(1 + K) * (2 * (1 + c)), ENNReal.mul_ne_top (ENNReal.add_ne_top.2
    ⟨ENNReal.one_ne_top, hK⟩) (ENNReal.mul_ne_top (by simp)
      (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hc⟩)), fun F hF => ?_⟩
  set ω := modulus r p 0 1 F t
  have hwL : (1 - t) + t ≤ 1 := by linarith
  -- the left polynomial, on `[0, 1 - t] ⊇ [0, 2/3]`
  obtain ⟨gl, Dl, -, -, hl1, hl2, hl3⟩ := exists_left_smoothing hF hr hp1 hp ht hwL
  obtain ⟨T₁, hT₁, hT₁b⟩ := hl3 0 (1 - t) (by linarith)
  have hE₁ : eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc 0 (2 / 3))) ≤
      (1 + c) * ω := (eLpNorm_Icc_mono _ p le_rfl (by linarith)).trans
    (eLpNorm_sub_polyFun_le_of_smoothing (by linarith) hl1 hl2 hT₁b)
  -- the right polynomial, on `[t, 1] ⊇ [1/3, 1]`
  obtain ⟨gr, Dr, -, -, hr1, hr2, hr3⟩ := exists_right_smoothing hF hr hp1 hp ht hwL
  rw [sub_sub_cancel] at hr1 hr2
  obtain ⟨T₂, hT₂, hT₂b⟩ := hr3 t 1 (by linarith)
  have hE₂ : eLpNorm (fun x => F x - polyFun T₂ x) p (volume.restrict (Icc (1 / 3) 1)) ≤
      (1 + c) * ω := (eLpNorm_Icc_mono _ p ht3 le_rfl).trans
    (eLpNorm_sub_polyFun_le_of_smoothing (by linarith) hr1 hr2 hT₂b)
  refine ⟨T₁, hT₁, (hKb hF.measurable hT₁ hT₂).trans ?_⟩
  calc (1 + K) * (eLpNorm (fun x => F x - polyFun T₁ x) p (volume.restrict (Icc 0 (2 / 3))) +
        eLpNorm (fun x => F x - polyFun T₂ x) p (volume.restrict (Icc (1 / 3) 1)))
      ≤ (1 + K) * ((1 + c) * ω + (1 + c) * ω) := mul_le_mul' le_rfl (add_le_add hE₁ hE₂)
    _ = (1 + K) * (2 * (1 + c)) * ω := by ring

end Interval
