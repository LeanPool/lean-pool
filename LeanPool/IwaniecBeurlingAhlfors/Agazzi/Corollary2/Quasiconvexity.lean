/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Bridges
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Theorem1
public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.External.BaernsteinMontgomerySmith.Basic

/-!
# Corollary 2, first part: the quasiconvexity of the Burkholder integrand

**Corollary 2** (`cor:Bp-BA`), first assertion: for every `1 < p < ∞`, every `A ∈ ℝ^{2×2}` and every
`φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`.

The paper derives it from Theorem 1 "by the arguments in [Baernstein1997a] (see also [Guerra2026b])"
(TeX line 301). Those arguments: `B_p` is a positive multiple of the Mellin transform
`∫_0^∞ t^{p−1} L (A / t) dt` for `1 < p < 2` (Baernstein–Montgomery-Smith (1.2a)), and of
`∫_0^∞ t^{p−1} (L − det) (A / t) dt` for `2 < p < ∞` ((1.2b)); `B_2 = −det`. Each `A ↦ L (A / t)`
is quasiconvex (Theorem 1 applied to `A / t` and `φ / t`), `det` is a null Lagrangian, and Fubini's
theorem gives the inequality for `B_p`.

As for Theorem 1, `corollary2_lipschitz` states the inequality for Lipschitz periodic `φ`, by the
same argument from `theorem1_lipschitz`, and `corollary2` is the paper's statement.

The steps:

* `burkholderB_eq_mellin_of_lt_two`: `B_p (A) = (p (2 − p)/2) ∫_0^∞ t^{p−1} L (A / t) dt` for
  `1 < p < 2`;
* `burkholderB_eq_mellin_of_two_lt`:
  `B_p (A) = (p (p − 1)(p − 2)/2) ∫_0^∞ t^{p−1} (L − det) (A / t) dt` for `2 < p`;
* `burkholderB_two`: `B_2 = −det`;
* `setIntegral_sub_nonneg_of_mellin` (private): the Fubini step;
* `continuous_integrandL`, `continuous_burkholderB`: used for the quasiconvexity in the sense of
  `CalculusOfVariations` (`Agazzi.Quasiconvex`).
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Agazzi

/-- `L (A) = L_BMS (a₊, a₋)`: the paper's `L` is the function of Baernstein and Montgomery-Smith
in conformal coordinates. -/
theorem integrandL_eq_bms (A : Matrix (Fin 2) (Fin 2) ℝ) :
    integrandL A = External.BaernsteinMontgomerySmith.L (conformalPart A) (anticonformalPart A) :=
  rfl

/-! ### The conformal coordinates: continuity and homogeneity -/

theorem conformalPart_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    conformalPart A =
      (((A 0 0 + A 1 1) / 2 : ℝ) : ℂ) + (((A 1 0 - A 0 1) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [conformalPart]

theorem anticonformalPart_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    anticonformalPart A =
      (((A 0 0 - A 1 1) / 2 : ℝ) : ℂ) + (((A 1 0 + A 0 1) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [anticonformalPart]

theorem continuous_conformalPart : Continuous conformalPart := by
  rw [show conformalPart = _ from funext conformalPart_eq]
  fun_prop

theorem continuous_anticonformalPart : Continuous anticonformalPart := by
  rw [show anticonformalPart = _ from funext anticonformalPart_eq]
  fun_prop

/-- `(c A)₊ = c a₊` for real `c`. -/
theorem conformalPart_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    conformalPart (c • A) = (c : ℂ) * conformalPart A := by
  apply Complex.ext <;> simp [conformalPart] <;> ring

/-- `(c A)₋ = c a₋` for real `c`. -/
theorem anticonformalPart_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    anticonformalPart (c • A) = (c : ℂ) * anticonformalPart A := by
  apply Complex.ext <;> simp [anticonformalPart] <;> ring

/-- `L` is continuous: the two expressions agree on `|a₊| + |a₋| = 1`. -/
theorem continuous_integrandL : Continuous integrandL := by
  have h1 := continuous_conformalPart.norm
  have h2 := continuous_anticonformalPart.norm
  refine continuous_if_le (h1.add h2) continuous_const ((h1.pow 2).sub (h2.pow 2)).continuousOn
    ((continuous_const.mul h1).sub continuous_const).continuousOn fun A hA => ?_
  have : ‖anticonformalPart A‖ = 1 - ‖conformalPart A‖ := by linarith
  rw [this]; ring

/-- `B_p` is continuous for `1 < p`. -/
theorem continuous_burkholderB {p : ℝ} (hp : 1 < p) : Continuous (burkholderB p) := by
  have h1 := continuous_conformalPart.norm
  have h2 := continuous_anticonformalPart.norm
  have h3 : Continuous fun A => (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) :=
    (h1.add h2).rpow_const fun _ => Or.inr (by linarith)
  unfold burkholderB
  split_ifs
  · exact ((continuous_const.mul h1).sub h2).mul h3
  · exact ((continuous_const.mul h2).sub h1).mul h3

/-- `D (c φ) = c D φ`. -/
theorem jacobian_smul (c : ℝ) (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    jacobian (fun y => c • φ y) x = c • jacobian φ x := by
  ext i j
  simp only [jacobian, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun y => c * φ y i) = c • fun y => φ y i := rfl
  rw [this, fderiv_const_smul_field]
  rfl

/-- `|(c A)₊| = |c| |a₊|`. -/
theorem norm_conformalPart_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖conformalPart (c • A)‖ = |c| * ‖conformalPart A‖ := by
  rw [conformalPart_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- `|(c A)₋| = |c| |a₋|`. -/
theorem norm_anticonformalPart_smul (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖anticonformalPart (c • A)‖ = |c| * ‖anticonformalPart A‖ := by
  rw [anticonformalPart_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- `L (A / t) = L_BMS (a₊ / t, a₋ / t)`. -/
theorem integrandL_inv_smul (t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    integrandL (t⁻¹ • A) =
      External.BaernsteinMontgomerySmith.L (conformalPart A / t) (anticonformalPart A / t) := by
  rw [integrandL_eq_bms, conformalPart_smul, anticonformalPart_smul, Complex.ofReal_inv,
    inv_mul_eq_div, inv_mul_eq_div]

/-! ### The Mellin representations of `B_p` (Baernstein–Montgomery-Smith (1.2a), (1.2b)) -/

/-- For `1 < p < 2`, `B_p (A) = (p (2 − p) / 2) ∫_0^∞ t^{p−1} L (A / t) dt`: Baernstein and
Montgomery-Smith's (1.2a) at `z = a₊`, `w = a₋`, where
`β_p Φ_p (a₊, a₋) = (2 / (p (2 − p))) B_p (A)`. -/
theorem burkholderB_eq_mellin_of_lt_two {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderB p A =
      p * (2 - p) / 2 * ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * integrandL (t⁻¹ • A) := by
  simp_rw [integrandL_inv_smul]
  rw [External.BaernsteinMontgomerySmith.equation1_2a hp1 hp2,
    External.BaernsteinMontgomerySmith.beta, External.BaernsteinMontgomerySmith.Phi]
  have hα := (External.BaernsteinMontgomerySmith.alpha_pos hp1).ne'
  have hp0 : p ≠ 0 := by linarith
  have hp2' : 2 - p ≠ 0 := by linarith
  unfold burkholderB pStar External.BaernsteinMontgomerySmith.pStar
  rw [ite_eq_left hp2]
  field_simp

/-- For `2 < p`, `B_p (A) = (p (p − 1)(p − 2) / 2) ∫_0^∞ t^{p−1} (L − det) (A / t) dt`: Baernstein
and Montgomery-Smith's (1.2b) at `z = a₋`, `w = a₊`, where `M (a₊ / t, a₋ / t) = (L − det) (A / t)`
(`det_eq`) and `γ_p Φ_p (a₋, a₊) = (2 / (p (p − 1)(p − 2))) B_p (A)`. -/
theorem burkholderB_eq_mellin_of_two_lt {p : ℝ} (hp : 2 < p) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    burkholderB p A = p * (p - 1) * (p - 2) / 2 *
      ∫ t in Set.Ioi (0 : ℝ), t ^ (p - 1) * (integrandL (t⁻¹ • A) - (t⁻¹ • A).det) := by
  have hM : ∀ t : ℝ, integrandL (t⁻¹ • A) - (t⁻¹ • A).det =
      External.BaernsteinMontgomerySmith.M (conformalPart A / t) (anticonformalPart A / t) := by
    intro t
    rw [det_eq, integrandL_inv_smul, External.BaernsteinMontgomerySmith.M, conformalPart_smul,
      anticonformalPart_smul, Complex.ofReal_inv, inv_mul_eq_div, inv_mul_eq_div]
  simp_rw [hM]
  rw [External.BaernsteinMontgomerySmith.equation1_2b hp, External.BaernsteinMontgomerySmith.gamma,
    External.BaernsteinMontgomerySmith.Phi]
  have hα := (External.BaernsteinMontgomerySmith.alpha_pos (by linarith : (1 : ℝ) < p)).ne'
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp2' : p - 2 ≠ 0 := by linarith
  unfold burkholderB pStar External.BaernsteinMontgomerySmith.pStar
  rw [ite_eq_right (by linarith : ¬ p < 2), add_comm ‖anticonformalPart A‖]
  field_simp

/-- `B_2 = −det`. -/
theorem burkholderB_two (A : Matrix (Fin 2) (Fin 2) ℝ) : burkholderB 2 A = -A.det := by
  have h : pStar 2 = 2 := by norm_num [pStar]
  rw [det_eq]
  unfold burkholderB
  rw [ite_eq_right (lt_irrefl 2), h]
  norm_num
  ring

/-! ### Bounds for the Fubini step -/

/-- `|L (A)| ≤ 3 |A|` and `|L (A)| ≤ 3 |A|²`, with `|A| = |a₊| + |a₋|`. -/
private theorem abs_integrandL_le (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |integrandL A| ≤ 3 * (‖conformalPart A‖ + ‖anticonformalPart A‖) ∧
      |integrandL A| ≤ 3 * (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ 2 := by
  have hs := norm_nonneg (conformalPart A)
  have hr := norm_nonneg (anticonformalPart A)
  unfold integrandL
  split_ifs with h
  · constructor <;> rw [abs_le] <;> constructor <;> nlinarith
  · constructor <;> rw [abs_le] <;> constructor <;> nlinarith

/-- `|L (A) − det A| ≤ 4 |A|²`, and `L (A) = det A` for `|A| ≤ 1`. -/
private theorem abs_integrandL_sub_det_le (A : Matrix (Fin 2) (Fin 2) ℝ) :
    |integrandL A - A.det| ≤ 4 * (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ 2 ∧
      (‖conformalPart A‖ + ‖anticonformalPart A‖ ≤ 1 → integrandL A - A.det = 0) := by
  have hs := norm_nonneg (conformalPart A)
  have hr := norm_nonneg (anticonformalPart A)
  rw [det_eq]
  unfold integrandL
  split_ifs with h
  · simp only [sub_self, abs_zero, implies_true, and_true]
    positivity
  · refine ⟨?_, fun h' => absurd h' h⟩
    rw [abs_le]
    constructor <;> nlinarith

private lemma rpow_sub_one'' {t : ℝ} (ht : 0 < t) (a : ℝ) : t ^ (a - 1) = t ^ a * t⁻¹ := by
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]

private lemma rpow_sub_two'' {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t ^ (a - 2) = t ^ a * (t ^ 2)⁻¹ := by
  rw [Real.rpow_sub ht, div_eq_mul_inv]
  norm_cast

private lemma measurableSet_unitSquare : MeasurableSet unitSquare :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- `|Q| = 1`, from the package `CalculusOfVariations`. -/
private lemma volume_unitSquare' : volume unitSquare = 1 :=
  CalculusOfVariations.rd_volume_unitCube 2

/-- For a continuous `f` and a Lipschitz `φ`, `x ↦ f (A + Dφ (x))` is integrable on `Q`. -/
private lemma integrableOn_comp_add_jacobian {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    (hf : Continuous f) (A : Matrix (Fin 2) (Fin 2) ℝ) {φ : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {C : NNReal} (hφ : LipschitzWith C φ) :
    IntegrableOn (fun x => f (A + jacobian φ x)) unitSquare :=
  CalculusOfVariations.rd_integrableOn hf.measurable
    (CalculusOfVariations.isLocallyBounded_of_continuous hf) A hφ (by rw [volume_unitSquare']; simp)

/-! ### The Fubini step -/

/-- The Fubini step of the arguments of Baernstein and Montgomery-Smith: if
`f (B) = c ∫_0^∞ k (B, t) dt` with `c ≥ 0`, `k` jointly measurable, `|k (g (x), t)| ≤ G (t)` with
`G` integrable on `(0, ∞)`, and `k (A, t) ≤ ∫_Q k (g (x), t) dx` for every `t > 0`, then
`∫_Q [f (g (x)) − f (A)] dx ≥ 0`. -/
private theorem setIntegral_sub_nonneg_of_mellin {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ}
    {k : Matrix (Fin 2) (Fin 2) ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hk : Measurable (Function.uncurry k))
    (hrep : ∀ B, f B = c * ∫ t in Set.Ioi (0 : ℝ), k B t)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hkA : IntegrableOn (k A) (Set.Ioi 0))
    {g : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ} (hg : Measurable g)
    {G : ℝ → ℝ} (hG : IntegrableOn G (Set.Ioi 0))
    (hbound : ∀ x t, 0 < t → |k (g x) t| ≤ G t)
    (hineq : ∀ t, 0 < t → k A t ≤ ∫ x in unitSquare, k (g x) t) :
    0 ≤ ∫ x in unitSquare, (f (g x) - f A) := by
  have : IsFiniteMeasure (volume.restrict unitSquare) :=
    isFiniteMeasure_restrict.2 (by rw [volume_unitSquare']; simp)
  have hF : Integrable (Function.uncurry fun x t => k (g x) t)
      ((volume.restrict unitSquare).prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    refine Integrable.mono' ((hG : Integrable G _).comp_snd _) ?_ ?_
    · exact (hk.comp ((hg.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_unitSquare.prod measurableSet_Ioi) ?_
      rintro ⟨x, t⟩ ⟨-, ht⟩
      rw [Real.norm_eq_abs]
      exact hbound x t ht
  have h1 := hF.integral_prod_left
  have h2 := hF.integral_prod_right
  have hswap := integral_integral_swap hF
  have hfg : (fun x => f (g x)) = fun x => c * ∫ t in Set.Ioi (0 : ℝ), k (g x) t :=
    funext fun x => hrep (g x)
  have hint : IntegrableOn (fun x => f (g x)) unitSquare := by
    rw [hfg]; exact h1.const_mul c
  rw [integral_sub hint (integrableOn_const (by rw [volume_unitSquare']; simp)), setIntegral_const,
    Measure.real, volume_unitSquare', ENNReal.toReal_one, one_smul, hfg, integral_const_mul,
    hswap, hrep A, ← mul_sub]
  exact mul_nonneg hc (sub_nonneg.2 (setIntegral_mono_on hkA h2 measurableSet_Ioi hineq))

/-! ### Corollary 2 -/

/-- **Corollary 2** (`cor:Bp-BA`), first assertion, for Lipschitz periodic test maps: for `1 < p`,
`∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`.

Proof: the arguments of Baernstein and Montgomery-Smith. For `1 < p < 2`,
`B_p (A) = (p (2 − p)/2) ∫_0^∞ t^{p−1} L (A / t) dt` (`burkholderB_eq_mellin_of_lt_two`, from
(1.2a)); for `2 < p`, `B_p (A) = (p (p − 1)(p − 2)/2) ∫_0^∞ t^{p−1} (L − det) (A / t) dt`
(`burkholderB_eq_mellin_of_two_lt`, from (1.2b)); `B_2 = −det`. For each `t > 0`, Theorem 1 at
`A / t` with the test map `φ / t` (`theorem1_lipschitz`) gives `∫_Q L ((A + Dφ) / t) ≥ L (A / t)`,
and `det` is a null Lagrangian (`setIntegral_unitCube_det_add_grad`); integrating in `t` against
`t^{p−1}` and exchanging the integrals (Fubini, `setIntegral_sub_nonneg_of_mellin`: the integrands
are bounded by `|L (B / t)| ≤ 3 |B| / t`, `3 |B|² / t²` and `|(L − det) (B / t)| ≤ 4 |B|² / t²`,
vanishing for `t ≥ |B|`, with `|A + Dφ|` bounded) gives the inequality. -/
theorem corollary2_lipschitz {p : ℝ} (hp : 1 < p) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} {C : NNReal} (hφ : LipschitzWith C φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (burkholderB p (A + jacobian φ x) - burkholderB p A) := by
  -- the bound `|A + Dφ (x)| ≤ N`
  have hn : Continuous fun B : Matrix (Fin 2) (Fin 2) ℝ =>
      ‖conformalPart B‖ + ‖anticonformalPart B‖ :=
    continuous_conformalPart.norm.add continuous_anticonformalPart.norm
  obtain ⟨N, hN0, hN⟩ := CalculusOfVariations.rd_bound_near
    (CalculusOfVariations.isLocallyBounded_of_continuous hn) A C
  have hNx : ∀ x, ‖conformalPart (A + jacobian φ x)‖ + ‖anticonformalPart (A + jacobian φ x)‖ ≤ N :=
    fun x => (le_abs_self _).trans (hN _ fun i k => CalculusOfVariations.rd_grad_abs_le hφ x i k)
  have hscale : ∀ (t : ℝ) (x : Fin 2 → ℝ), 0 < t →
      ‖conformalPart (t⁻¹ • (A + jacobian φ x))‖ + ‖anticonformalPart (t⁻¹ • (A + jacobian φ x))‖
        ≤ t⁻¹ * N := by
    intro t x ht
    rw [norm_conformalPart_smul, norm_anticonformalPart_smul, abs_of_pos (inv_pos.2 ht), ← mul_add]
    exact mul_le_mul_of_nonneg_left (hNx x) (inv_pos.2 ht).le
  have hg : Measurable fun x => A + jacobian φ x := CalculusOfVariations.rd_measurable_add_grad A φ
  -- the test maps `φ / t`
  have hφt : ∀ t : ℝ, LipschitzWith (‖t⁻¹‖₊ * C) (fun y => t⁻¹ • φ y) := fun t =>
    (lipschitzWith_smul (t⁻¹ : ℝ)).comp hφ
  have hpert : ∀ t : ℝ, IsPeriodic (fun y => t⁻¹ • φ y) := fun t x k => by
    simp only [hper x k]
  have hjt : ∀ (t : ℝ) (x : Fin 2 → ℝ),
      t⁻¹ • (A + jacobian φ x) = t⁻¹ • A + jacobian (fun y => t⁻¹ • φ y) x := fun t x => by
    rw [jacobian_smul, smul_add]
  -- Theorem 1 at `A / t` with `φ / t`
  have hL : ∀ t : ℝ, integrandL (t⁻¹ • A) ≤
      ∫ x in unitSquare, integrandL (t⁻¹ • (A + jacobian φ x)) := by
    intro t
    have h := theorem1_lipschitz (t⁻¹ • A) (hφt t) (hpert t)
    rw [integral_sub (integrableOn_comp_add_jacobian continuous_integrandL _ (hφt t))
      (integrableOn_const (by rw [volume_unitSquare']; simp)), setIntegral_const, Measure.real,
      volume_unitSquare', ENNReal.toReal_one, one_smul, sub_nonneg] at h
    simpa only [hjt] using h
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · -- `1 < p < 2`: (1.2a)
    refine setIntegral_sub_nonneg_of_mellin (k := fun B t => t ^ (p - 1) * integrandL (t⁻¹ • B))
      (c := p * (2 - p) / 2) (by nlinarith) ?_ (burkholderB_eq_mellin_of_lt_two hp hp2) A ?_ hg
      (G := fun t => if t ≤ 1 then 3 * N * t ^ (p - 2) else 3 * N ^ 2 * t ^ (p - 3)) ?_ ?_ ?_
    · exact (measurable_snd.pow_const (p - 1)).mul
        (continuous_integrandL.measurable.comp (measurable_snd.inv.smul measurable_fst))
    · simp_rw [integrandL_inv_smul]
      exact External.BaernsteinMontgomerySmith.integrableOn_equation1_2a hp hp2 _ _
    · rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
      refine IntegrableOn.union ?_ ?_
      · refine IntegrableOn.congr_fun ?_ (fun t ht => (ite_eq_left ht.2).symm) measurableSet_Ioc
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
          ((intervalIntegral.intervalIntegrable_rpow' (r := p - 2) (by linarith)).const_mul _)
      · refine IntegrableOn.congr_fun ?_ (fun t ht => (ite_eq_right (not_le.2 ht)).symm)
          measurableSet_Ioi
        exact (integrableOn_Ioi_rpow_of_lt (a := p - 3) (by linarith) one_pos).const_mul _
    · intro x t ht
      have hb := abs_integrandL_le (t⁻¹ • (A + jacobian φ x))
      have hs := hscale t x ht
      have hn0 : 0 ≤ ‖conformalPart (t⁻¹ • (A + jacobian φ x))‖ +
          ‖anticonformalPart (t⁻¹ • (A + jacobian φ x))‖ := by positivity
      have htp : 0 < t ^ (p - 1) := Real.rpow_pos_of_pos ht _
      rw [abs_mul, abs_of_pos htp]
      split_ifs with h1
      · rw [show p - 2 = p - 1 - 1 by ring, rpow_sub_one'' ht (p - 1)]
        calc t ^ (p - 1) * |integrandL (t⁻¹ • (A + jacobian φ x))|
            ≤ t ^ (p - 1) * (3 * (t⁻¹ * N)) :=
              mul_le_mul_of_nonneg_left (hb.1.trans (by linarith)) htp.le
          _ = 3 * N * (t ^ (p - 1) * t⁻¹) := by ring
      · rw [show p - 3 = p - 1 - 2 by ring, rpow_sub_two'' ht (p - 1)]
        calc t ^ (p - 1) * |integrandL (t⁻¹ • (A + jacobian φ x))|
            ≤ t ^ (p - 1) * (3 * (t⁻¹ * N) ^ 2) :=
              mul_le_mul_of_nonneg_left (hb.2.trans (by gcongr)) htp.le
          _ = 3 * N ^ 2 * (t ^ (p - 1) * (t ^ 2)⁻¹) := by ring
    · intro t ht
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hL t) (Real.rpow_pos_of_pos ht _).le
  · -- `p = 2`: `B_2 = −det`, a null Lagrangian
    have hdet : ∫ x in unitSquare, (A + jacobian φ x).det = A.det :=
      CalculusOfVariations.setIntegral_unitCube_det_add_grad hφ hper A
    simp_rw [burkholderB_two]
    rw [integral_sub (integrableOn_comp_add_jacobian (f := fun B => -B.det)
        (continuous_id.matrix_det.neg) A hφ)
      (integrableOn_const (by rw [volume_unitSquare']; simp)), setIntegral_const, Measure.real,
      volume_unitSquare', ENNReal.toReal_one, one_smul, integral_neg, hdet]
    simp
  · -- `2 < p`: (1.2b)
    have hc : 0 ≤ p * (p - 1) * (p - 2) / 2 := by
      have : 0 < p * (p - 1) := by nlinarith
      have : 0 < p * (p - 1) * (p - 2) := by nlinarith
      linarith
    refine setIntegral_sub_nonneg_of_mellin
      (k := fun B t => t ^ (p - 1) * (integrandL (t⁻¹ • B) - (t⁻¹ • B).det))
      (c := p * (p - 1) * (p - 2) / 2) hc ?_ (burkholderB_eq_mellin_of_two_lt hp2) A ?_ hg
      (G := fun t => if t ≤ N then 4 * N ^ 2 * t ^ (p - 3) else 0) ?_ ?_ ?_
    · exact (measurable_snd.pow_const (p - 1)).mul
        ((continuous_integrandL.measurable.comp (measurable_snd.inv.smul measurable_fst)).sub
          ((continuous_id.matrix_det).measurable.comp (measurable_snd.inv.smul measurable_fst)))
    · have hM : ∀ t : ℝ, integrandL (t⁻¹ • A) - (t⁻¹ • A).det =
          External.BaernsteinMontgomerySmith.M (conformalPart A / t) (anticonformalPart A / t) := by
        intro t
        rw [det_eq, integrandL_inv_smul, External.BaernsteinMontgomerySmith.M, conformalPart_smul,
          anticonformalPart_smul, Complex.ofReal_inv, inv_mul_eq_div, inv_mul_eq_div]
      simp_rw [hM]
      exact External.BaernsteinMontgomerySmith.integrableOn_equation1_2b hp2 _ _
    · rw [← Set.Ioc_union_Ioi_eq_Ioi hN0]
      refine IntegrableOn.union ?_ ?_
      · refine IntegrableOn.congr_fun ?_ (fun t ht => (ite_eq_left ht.2).symm) measurableSet_Ioc
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hN0).1
          ((intervalIntegral.intervalIntegrable_rpow' (r := p - 3) (by linarith)).const_mul _)
      · exact integrableOn_zero.congr_fun (fun t ht => (ite_eq_right (not_le.2 ht)).symm)
          measurableSet_Ioi
    · intro x t ht
      have hb := abs_integrandL_sub_det_le (t⁻¹ • (A + jacobian φ x))
      have hs := hscale t x ht
      have hn0 : 0 ≤ ‖conformalPart (t⁻¹ • (A + jacobian φ x))‖ +
          ‖anticonformalPart (t⁻¹ • (A + jacobian φ x))‖ := by positivity
      have htp : 0 < t ^ (p - 1) := Real.rpow_pos_of_pos ht _
      rw [abs_mul, abs_of_pos htp]
      split_ifs with h1
      · rw [show p - 3 = p - 1 - 2 by ring, rpow_sub_two'' ht (p - 1)]
        calc t ^ (p - 1) * |integrandL (t⁻¹ • (A + jacobian φ x)) - (t⁻¹ • (A + jacobian φ x)).det|
            ≤ t ^ (p - 1) * (4 * (t⁻¹ * N) ^ 2) :=
              mul_le_mul_of_nonneg_left (hb.1.trans (by gcongr)) htp.le
          _ = 4 * N ^ 2 * (t ^ (p - 1) * (t ^ 2)⁻¹) := by ring
      · have hlt : t⁻¹ * N ≤ 1 := by
          rw [inv_mul_le_iff₀ ht, mul_one]; exact (not_le.1 h1).le
        rw [hb.2 (hs.trans hlt), abs_zero, mul_zero]
    · intro t ht
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos ht _).le
      have hdet : ∫ x in unitSquare, (t⁻¹ • A + jacobian (fun y => t⁻¹ • φ y) x).det =
          (t⁻¹ • A).det :=
        CalculusOfVariations.setIntegral_unitCube_det_add_grad (hφt t) (hpert t) (t⁻¹ • A)
      have h := hL t
      simp_rw [hjt t] at h ⊢
      rw [integral_sub (integrableOn_comp_add_jacobian continuous_integrandL _ (hφt t))
        (integrableOn_comp_add_jacobian (f := fun B => B.det) (continuous_id.matrix_det) _ (hφt t)),
        hdet]
      linarith

/-- **Corollary 2** (`cor:Bp-BA`), first assertion. For every `1 < p < ∞`, every `A ∈ ℝ^{2×2}` and
every `φ ∈ C^∞_per (Q; ℝ²)`, `∫_Q [B_p (A + Dφ) − B_p (A)] dx ≥ 0`. -/
theorem corollary2 {p : ℝ} (hp : 1 < p) (A : Matrix (Fin 2) (Fin 2) ℝ)
    {φ : (Fin 2 → ℝ) → Fin 2 → ℝ} (hφ : ContDiff ℝ ∞ φ) (hper : IsPeriodic φ) :
    0 ≤ ∫ x in unitSquare, (burkholderB p (A + jacobian φ x) - burkholderB p A) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_contDiff_of_isPeriodic hφ hper
  exact corollary2_lipschitz hp A hC hper

end Agazzi
