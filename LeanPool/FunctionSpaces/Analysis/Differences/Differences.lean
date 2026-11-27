/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Differences and the modulus of smoothness

For `f : V → ℂ`, a step `h ∈ V` and `r ∈ ℕ`, the **difference** of order `r` is
`Δ_h^r f = (Δ_h)^r f` with `Δ_h f(x) = f(x + h) - f(x)` (Mathlib's `fwdDiff`), named
`Rd.higherDiff r h f` on every additive monoid.  The statements on `V` use the iterate
`(fwdDiff h)^[r] f` itself, for which Mathlib has its lemmas; the files on intervals and cubes use
the name.  Expanded, `Δ_h^r f(x) = ∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)`
(`Rd.higherDiff_apply`); hence `|Δ_h^r f(x)| ≤ ∑_{l ≤ r} C(r, l) |f(x + l h)|`
(`Rd.enorm_higherDiff_le_sum`), so `|Δ_h^r f(x)| ≤ 2^r B` if `|f| ≤ B` at the points `x + l h`
(`Rd.enorm_higherDiff_le_of_bound_steps`), and `(x, h) ↦ |Δ_h^r f(x)|` is measurable for
measurable `f`
(`Rd.measurable_enorm_higherDiff_uncurry`). A negative step reflects the difference:
`Δ_{-h}^r f(x) = (-1)^r Δ_h^r f(x - r h)` (`Rd.higherDiff_neg`). For a Haar
measure `μ` the **modulus of smoothness** in `L_p(μ)` is
`ω_r(f, t)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r f‖_p` (`Rd.modulus`). It increases in `t`, is subadditive and
homogeneous in `f` (`Rd.modulus_const_smul`), is bounded by `2^r ‖f‖_p` (`Rd.modulus_le`), and
depends only on the class of `f` modulo null sets (`Rd.modulus_congr_ae`).

**Dilating the step** (`Rd.modulus_mul_le`): `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` for
`c, t ≥ 0`. For an integer `m ≥ 1`, `Δ_{mh} = ∑_{i<m} τ_{ih} Δ_h` with the translations
`τ_a g = g(· + a)` (`Rd.fwdDiff_nsmul`), translations commute with differences
(`Rd.higherDiff_comp_add`), and translations keep `L_p` norms, so
`‖Δ_{mh}^r f‖_p ≤ m^r ‖Δ_h^r f‖_p` (`Rd.eLpNorm_higherDiff_nsmul_higherDiff_le`). The two steps,
from steps `m h'` to the scale `m t` and from integers to real dilations
(`Rd.modulus_nat_mul_le_of_forall_exists_nsmul`, `Rd.modulus_mul_le_of_nat_mul_le`), hold on
every normed group, the torus included.

`Rd.lpModulus` samples the modulus of `f ∈ L_p` at the dyadic scales `2^(-k)`.  The file needs
only Mathlib; differences of convolutions and dilations are in
`FunctionSpaces.Rd.Differences.DilatedDifferences`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-! ### Differences and translations -/

/-- The **difference of order `r`** with step `h`: `Δ_h^r f = (Δ_h)^r f`, the `r`-th iterate of
Mathlib's forward difference `fwdDiff h`. -/
noncomputable def higherDiff {W : Type*} [AddCommMonoid W] (r : ℕ) (h : W) (f : W → ℂ) : W → ℂ :=
  (fwdDiff h)^[r] f

/-- The difference of order `r` is the `r`-th iterate of `fwdDiff h`. -/
theorem higherDiff_def {W : Type*} [AddCommMonoid W] (r : ℕ) (h : W) (f : W → ℂ) :
    higherDiff r h f = (fwdDiff h)^[r] f :=
  rfl

/-- Differences of measurable functions are measurable. -/
theorem measurable_higherDiff {W : Type*} [AddCommMonoid W] [MeasurableSpace W]
    [MeasurableAdd W] {f : W → ℂ} (hf : Measurable f) (r : ℕ) (h : W) :
    Measurable (higherDiff r h f) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [higherDiff_def, Function.iterate_succ_apply']
    exact (ih.comp (measurable_add_const h)).sub ih

/-- `(-1)^r (-1)^(r-m) = (-1)^m` for `m ≤ r`. -/
theorem neg_one_pow_mul_neg_one_pow_sub {r m : ℕ} (hm : m ≤ r) :
    (-1 : ℂ) ^ r * (-1) ^ (r - m) = (-1) ^ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, mul_one]

/-- **Negative steps**: `Δ_{-h}^r f(x) = (-1)^r Δ_h^r f(x - r h)`, by reflecting the sum
`∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)` at `l ↦ r - l`. -/
theorem higherDiff_neg {W : Type*} [AddCommGroup W] (r : ℕ) (h : W) (f : W → ℂ) (x : W) :
    (fwdDiff (-h))^[r] f x = (-1 : ℂ) ^ r * (fwdDiff h)^[r] f (x - r • h) := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift, Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hx : x + (r - k) • -h = x - r • h + k • h := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk'
    rw [Nat.add_sub_cancel_left, smul_neg, add_nsmul]
    abel
  rw [show r + 1 - 1 - k = r - k by omega, Nat.choose_symm hk', show r - (r - k) = k by omega, hx]
  simp only [zsmul_eq_mul]
  push_cast
  rw [← neg_one_pow_mul_neg_one_pow_sub hk']
  ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `Δ_h f = f(· + h) - f`. -/
theorem fwdDiff_eq_sub (h : V) (f : V → ℂ) : fwdDiff h f = (fun x => f (x + h)) - f :=
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `Δ_h^r f(x) = ∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)` (Mathlib's
`fwdDiff_iter_eq_sum_shift`). -/
theorem higherDiff_apply (r : ℕ) (h : V) (f : V → ℂ) (x : V) :
    (fwdDiff h)^[r] f x = ∑ l ∈ Finset.range (r + 1),
      ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) * f (x + (l : ℝ) • h) := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [zsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  push_cast
  ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences commute with translations**: `Δ_h^r (f(· + c)) = (Δ_h^r f)(· + c)`. -/
theorem higherDiff_comp_add (r : ℕ) (h c : V) (f : V → ℂ) :
    (fwdDiff h)^[r] (fun x => f (x + c)) = fun x => (fwdDiff h)^[r] f (x + c) :=
  funext fun x => fwdDiff_iter_comp_add h f c r x

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Differences with a multiple step telescope**: `Δ_{mh} f = ∑_{i<m} (Δ_h f)(· + i h)`. -/
theorem fwdDiff_nsmul (m : ℕ) (h : V) (f : V → ℂ) :
    fwdDiff (m • h) f = ∑ i ∈ Finset.range m, fun x => fwdDiff h f (x + i • h) := by
  induction m with
  | zero =>
    funext x
    simp [fwdDiff]
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    funext x
    simp only [fwdDiff, Pi.add_apply, succ_nsmul, ← add_assoc]
    ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|Δ_h^r f(x)| ≤ ∑_{l ≤ r} C(r, l) |f(x + l h)|`, from the expansion of the difference. -/
theorem enorm_higherDiff_le_sum (r : ℕ) (h : V) (f : V → ℂ) (x : V) :
    ‖(fwdDiff h)^[r] f x‖ₑ ≤
      ∑ l ∈ Finset.range (r + 1), (r.choose l : ℝ≥0∞) * ‖f (x + (l : ℝ) • h)‖ₑ := by
  rw [higherDiff_apply]
  refine (eNorm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => le_of_eq ?_)
  rw [eNorm_mul, eNorm_mul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul,
    ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|Δ_h^r f(x)| ≤ 2^r B` if `|f(x + l h)| ≤ B` at the points `l = 0, …, r` of the difference:
the binomial weights of `Rd.enorm_higherDiff_le_sum` sum to `2^r` (Mathlib's
`Nat.sum_range_choose`). -/
theorem enorm_higherDiff_le_of_bound_steps {f : V → ℂ} {B : ℝ≥0∞} {r : ℕ} {h x : V}
    (hf : ∀ l ≤ r, ‖f (x + (l : ℝ) • h)‖ₑ ≤ B) : ‖(fwdDiff h)^[r] f x‖ₑ ≤ 2 ^ r * B := by
  refine (enorm_higherDiff_le_sum r h f x).trans ((Finset.sum_le_sum fun l hl =>
    mul_le_mul' le_rfl (hf l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))).trans_eq ?_)
  rw [← Finset.sum_mul]
  congr 1
  exact_mod_cast Nat.sum_range_choose r

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- `|Δ_h^r f| ≤ 2^r B` for `|f| ≤ B` (`Rd.enorm_higherDiff_le_of_bound_steps`). -/
theorem enorm_higherDiff_le_of_bound {f : V → ℂ} {B : ℝ≥0∞}
    (hf : ∀ y, ‖f y‖ₑ ≤ B) (r : ℕ) (h x : V) : ‖(fwdDiff h)^[r] f x‖ₑ ≤ 2 ^ r * B :=
  enorm_higherDiff_le_of_bound_steps fun _ _ => hf _

/-- For measurable `f` the differences `(x, h) ↦ |Δ_h^r f(x)|` are jointly measurable, by the
expansion `Δ_h^r f(x) = ∑_{l ≤ r} (-1)^(r-l) C(r, l) f(x + l h)`. -/
theorem measurable_enorm_higherDiff_uncurry {f : V → ℂ} (hf : Measurable f) (r : ℕ) :
    Measurable fun z : V × V => ‖(fwdDiff z.2)^[r] f z.1‖ₑ := by
  have heq : (fun z : V × V => (fwdDiff z.2)^[r] f z.1) = fun z =>
      ∑ l ∈ Finset.range (r + 1), ((-1 : ℂ) ^ (r - l) * (r.choose l : ℂ)) *
        f (z.1 + (l : ℝ) • z.2) := funext fun z => higherDiff_apply r z.2 f z.1
  refine Measurable.eNorm ?_
  rw [heq]
  exact Finset.measurable_sum _ fun l _ => measurable_const.mul
    (hf.comp (measurable_fst.add (measurable_snd.const_smul _)))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Translates of a.e. strongly measurable functions are a.e. strongly measurable. -/
theorem aestronglyMeasurable_comp_add {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (c : V) :
    AEStronglyMeasurable (fun x => f (x + c)) μ :=
  hf.comp_measurePreserving (measurePreserving_add_right μ c)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Translations keep `L_p` norms**: `‖f(· + c)‖_p = ‖f‖_p`. -/
theorem eLpNorm_comp_add_right {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) (c : V) :
    eLpNorm (fun x => f (x + c)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_add_right μ c)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Translates of functions that agree almost everywhere agree almost everywhere. -/
theorem ae_comp_add_right {f g : V → ℂ} (hfg : f =ᵐ[μ] g) (c : V) :
    (fun x => f (x + c)) =ᵐ[μ] fun x => g (x + c) :=
  (measurePreserving_add_right μ c).quasiMeasurePreserving.ae_eq_comp hfg

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Differences of a.e. strongly measurable functions are a.e. strongly measurable. -/
theorem aestronglyMeasurable_higherDiff {f : V → ℂ} (hf : AEStronglyMeasurable f μ) (r : ℕ)
    (h : V) : AEStronglyMeasurable ((fwdDiff h)^[r] f) μ := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub]
    exact (aestronglyMeasurable_comp_add ih h).sub ih

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Differences of functions that agree almost everywhere agree almost everywhere. -/
theorem higherDiff_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[μ] g) (r : ℕ) (h : V) :
    (fwdDiff h)^[r] f =ᵐ[μ] (fwdDiff h)^[r] g := by
  induction r with
  | zero => exact hfg
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fwdDiff_eq_sub,
      fwdDiff_eq_sub]
    exact (ae_comp_add_right ih h).sub ih

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **`‖Δ_h^r f‖_p ≤ 2^r ‖f‖_p`**, from `‖Δ_h g‖_p ≤ ‖g(· + h)‖_p + ‖g‖_p = 2 ‖g‖_p`. -/
theorem eLpNorm_higherDiff_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (r : ℕ) (h : V) :
    eLpNorm ((fwdDiff h)^[r] f) p μ ≤ 2 ^ r * eLpNorm f p μ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub]
    calc eLpNorm ((fun x => (fwdDiff h)^[r] f (x + h)) - (fwdDiff h)^[r] f) p μ
        ≤ eLpNorm (fun x => (fwdDiff h)^[r] f (x + h)) p μ + eLpNorm ((fwdDiff h)^[r] f) p μ :=
          eLpNorm_sub_le hp
      _ = 2 * eLpNorm ((fwdDiff h)^[r] f) p μ := by
          rw [eLpNorm_comp_add_right (aestronglyMeasurable_higherDiff hf r h), two_mul]
      _ ≤ 2 * (2 ^ r * eLpNorm f p μ) := by gcongr
      _ = 2 ^ (r + 1) * eLpNorm f p μ := by rw [pow_succ]; ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Multiples of the step**: `‖Δ_{mh}^a Δ_h^b f‖_p ≤ m^a ‖Δ_h^(a+b) f‖_p`, by induction on
`a`, with `Δ_{mh} = ∑_{i<m} τ_{ih} Δ_h`. -/
theorem eLpNorm_higherDiff_nsmul_higherDiff_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (m : ℕ) (h : V) (a : ℕ) :
    ∀ b, eLpNorm ((fwdDiff (m • h))^[a] ((fwdDiff h)^[b] f)) p μ ≤
      (m : ℝ≥0∞) ^ a * eLpNorm ((fwdDiff h)^[a + b] f) p μ := by
  induction a with
  | zero => intro b; simp
  | succ a ih =>
    intro b
    have hsplit : (fwdDiff (m • h))^[a + 1] ((fwdDiff h)^[b] f) =
        ∑ i ∈ Finset.range m,
          fun x => (fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f) (x + i • h) := by
      rw [Function.iterate_succ_apply, fwdDiff_nsmul, fwdDiff_iter_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [higherDiff_comp_add, ← Function.iterate_succ_apply' (fwdDiff h) b f]
    have hmeas : AEStronglyMeasurable ((fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f)) μ :=
      aestronglyMeasurable_higherDiff (aestronglyMeasurable_higherDiff hf (b + 1) h) a (m • h)
    rw [hsplit]
    calc eLpNorm (∑ i ∈ Finset.range m,
          fun x => (fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f) (x + i • h)) p μ
        ≤ ∑ i ∈ Finset.range m,
            eLpNorm (fun x => (fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f) (x + i • h)) p μ :=
          eLpNorm_sum_le hp
      _ = ∑ _i ∈ Finset.range m,
            eLpNorm ((fwdDiff (m • h))^[a] ((fwdDiff h)^[b + 1] f)) p μ :=
          Finset.sum_congr rfl fun i _ => eLpNorm_comp_add_right hmeas p _
      _ ≤ ∑ _i ∈ Finset.range m,
            (m : ℝ≥0∞) ^ a * eLpNorm ((fwdDiff h)^[a + (b + 1)] f) p μ :=
          Finset.sum_le_sum fun i _ => ih (b + 1)
      _ = (m : ℝ≥0∞) ^ (a + 1) * eLpNorm ((fwdDiff h)^[a + 1 + b] f) p μ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            show a + (b + 1) = a + 1 + b by omega, pow_succ]
          ring

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Differences of integrable functions are integrable. -/
theorem integrable_higherDiff {K : V → ℂ} (hK : Integrable K μ) (r : ℕ) (h : V) :
    Integrable ((fwdDiff h)^[r] K) μ := by
  induction r with
  | zero => exact hK
  | succ r ih =>
    rw [Function.iterate_succ_apply', fwdDiff_eq_sub]
    exact (ih.comp_add_right h).sub ih

/-! ### The modulus of smoothness -/

variable (μ) in
/-- The **modulus of smoothness** `ω_r(f, t)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r f‖_p`. -/
noncomputable def modulus (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (h : V) (_ : ‖h‖ ≤ t), eLpNorm ((fwdDiff h)^[r] f) p μ

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- `‖Δ_h^r f‖_p ≤ ω_r(f, t)_p` for `‖h‖ ≤ t`. -/
theorem eLpNorm_higherDiff_le_modulus {r : ℕ} {p : ℝ≥0∞} {f : V → ℂ} {t : ℝ}
    {h : V} (hh : ‖h‖ ≤ t) : eLpNorm ((fwdDiff h)^[r] f) p μ ≤ modulus μ r p f t :=
  le_iSup₂ (f := fun (h : V) (_ : ‖h‖ ≤ t) => eLpNorm ((fwdDiff h)^[r] f) p μ) h hh

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The modulus increases in `t`. -/
theorem modulus_mono (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) :
    Monotone (modulus μ r p f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_higherDiff_le_modulus (hh.trans hst)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The modulus is subadditive. -/
theorem modulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (f g : V → ℂ)
    (t : ℝ) : modulus μ r p (f + g) t ≤ modulus μ r p f t + modulus μ r p g t := by
  refine iSup₂_le fun h hh => ?_
  rw [fwdDiff_iter_add]
  exact (eLpNorm_add_le hp).trans
    (add_le_add (eLpNorm_higherDiff_le_modulus hh) (eLpNorm_higherDiff_le_modulus hh))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `ω_r(f, t)_p ≤ 2^r ‖f‖_p`. -/
theorem modulus_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) (t : ℝ) : modulus μ r p f t ≤ 2 ^ r * eLpNorm f p μ :=
  iSup₂_le fun h _ => eLpNorm_higherDiff_le hf hp r h

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The modulus depends only on the class modulo null sets.** -/
theorem modulus_congr_ae {f g : V → ℂ} (hfg : f =ᵐ[μ] g) (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulus μ r p f t = modulus μ r p g t := by
  simp only [modulus]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_congr_ae (higherDiff_congr_ae hfg r h)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- **The modulus is homogeneous**: `ω_r(c f, t)_p = |c| ω_r(f, t)_p`, since
`Δ_h^r (c f) = c Δ_h^r f` (Mathlib's `fwdDiff_iter_const_smul`, `eLpNorm_const_smul`). -/
theorem modulus_const_smul (r : ℕ) (p : ℝ≥0∞) (c : ℂ) (f : V → ℂ) (t : ℝ) :
    modulus μ r p (c • f) t = ‖c‖ₑ * modulus μ r p f t := by
  simp only [modulus, fwdDiff_iter_const_smul, eLpNorm_const_smul, ENNReal.mul_iSup]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Integer multiples of the scale, for divisible steps**: if every step `h` with
`‖h‖ ≤ m t` is `m h'` for a step `h'` with `‖h'‖ ≤ t`, then `ω_r(f, m t)_p ≤ m^r ω_r(f, t)_p`,
since `‖Δ^r_{m h'} f‖_p ≤ m^r ‖Δ^r_{h'} f‖_p` (`Rd.eLpNorm_higherDiff_nsmul_higherDiff_le`). The
hypothesis holds on every normed space and on the torus. -/
theorem modulus_nat_mul_le_of_forall_exists_nsmul {f : V → ℂ} (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {m : ℕ} {t : ℝ}
    (hdiv : ∀ h : V, ‖h‖ ≤ m * t → ∃ h' : V, ‖h'‖ ≤ t ∧ h = m • h') :
    modulus μ r p f (m * t) ≤ (m : ℝ≥0∞) ^ r * modulus μ r p f t := by
  refine iSup₂_le fun h hh => ?_
  obtain ⟨h', hh', rfl⟩ := hdiv h hh
  have h1 := eLpNorm_higherDiff_nsmul_higherDiff_le hf hp m h' r 0
  simp only [Function.iterate_zero, id_eq, add_zero] at h1
  exact h1.trans (by gcongr; exact eLpNorm_higherDiff_le_modulus hh')

omit [FiniteDimensional ℝ V] in
/-- **Integer multiples of the scale**: `ω_r(f, m t)_p ≤ m^r ω_r(f, t)_p` for `m ≥ 1`. -/
theorem modulus_nat_mul_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    modulus μ r p f (m * t) ≤ (m : ℝ≥0∞) ^ r * modulus μ r p f t := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine modulus_nat_mul_le_of_forall_exists_nsmul hf hp r fun h hh => ⟨(m : ℝ)⁻¹ • h, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hm0.le), inv_mul_le_iff₀ hm0]
    exact hh
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀ hm0.ne']

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- **From integer to real dilations of the scale**: if `ω_r(f, m t)_p ≤ m^r ω_r(f, t)_p` for
every integer `m ≥ 1`, then `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` for every `c ≥ 0`, with the
integer `m = ⌊c⌋ + 1 ≤ 1 + c` and the monotonicity of the modulus. -/
theorem modulus_mul_le_of_nat_mul_le {r : ℕ} {p : ℝ≥0∞} {f : V → ℂ} {c t : ℝ} (hc : 0 ≤ c)
    (ht : 0 ≤ t)
    (hnat : ∀ m : ℕ, 1 ≤ m → modulus μ r p f (m * t) ≤ (m : ℝ≥0∞) ^ r * modulus μ r p f t) :
    modulus μ r p f (c * t) ≤ ENNReal.ofReal (1 + c) ^ r * modulus μ r p f t := by
  have hm : 1 ≤ ⌊c⌋₊ + 1 := Nat.le_add_left 1 _
  have hcm : c ≤ ((⌊c⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact (Nat.lt_floor_add_one c).le
  have hm1 : (((⌊c⌋₊ + 1 : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal (1 + c) := by
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith [Nat.floor_le hc]
  calc modulus μ r p f (c * t) ≤ modulus μ r p f ((⌊c⌋₊ + 1 : ℕ) * t) :=
        modulus_mono r p f (mul_le_mul_of_nonneg_right hcm ht)
    _ ≤ ((⌊c⌋₊ + 1 : ℕ) : ℝ≥0∞) ^ r * modulus μ r p f t := hnat _ hm
    _ ≤ ENNReal.ofReal (1 + c) ^ r * modulus μ r p f t := by gcongr

omit [FiniteDimensional ℝ V] in
/-- **Dilating the scale**: `ω_r(f, c t)_p ≤ (1 + c)^r ω_r(f, t)_p` for `c, t ≥ 0`
(`Rd.modulus_nat_mul_le`, `Rd.modulus_mul_le_of_nat_mul_le`). -/
theorem modulus_mul_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (r : ℕ) {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    modulus μ r p f (c * t) ≤ ENNReal.ofReal (1 + c) ^ r * modulus μ r p f t :=
  modulus_mul_le_of_nat_mul_le hc ht fun _ hm => modulus_nat_mul_le hf hp r hm t

/-! ### The modulus on `L_p` at dyadic scales -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- The modulus of an element of `L_p` at the dyadic scale `2^(-k)`. -/
noncomputable def lpModulus (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) : ℝ≥0∞ :=
  modulus μ r p (f : V → ℂ) (1 / 2 ^ k)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The modulus on `L_p` is subadditive. -/
theorem lpModulus_add_le (r : ℕ) (f g : Lp ℂ p μ) (k : ℕ) :
    lpModulus p r (f + g) k ≤ lpModulus p r f k + lpModulus p r g k := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_add f g)]
  exact modulus_add_le Fact.out r _ _ _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `ω_r(f, 2^(-k))_p ≤ 2^r ‖f‖_p` on `L_p`. -/
theorem lpModulus_le (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) : lpModulus p r f k ≤ 2 ^ r * ‖f‖ₑ := by
  rw [Lp.eNorm_def]
  exact modulus_le (Lp.aestronglyMeasurable f) Fact.out r _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `ω_{r+l}(f, t)_p ≤ 2^l ω_r(f, t)_p`. -/
theorem lpModulus_add_order_le (r l : ℕ) (f : Lp ℂ p μ)
    (k : ℕ) : lpModulus p (r + l) f k ≤ 2 ^ l * lpModulus p r f k := by
  change modulus μ (r + l) p (f : V → ℂ) (1 / 2 ^ k) ≤
    2 ^ l * modulus μ r p (f : V → ℂ) (1 / 2 ^ k)
  refine iSup₂_le fun h hh => ?_
  rw [add_comm r l, Function.iterate_add_apply]
  exact (eLpNorm_higherDiff_le (aestronglyMeasurable_higherDiff (Lp.aestronglyMeasurable f) r h)
    Fact.out l h).trans (mul_le_mul' le_rfl (eLpNorm_higherDiff_le_modulus hh))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The modulus of `0` vanishes. -/
theorem lpModulus_zero (r k : ℕ) : lpModulus p r (0 : Lp ℂ p μ) k = 0 :=
  le_antisymm ((lpModulus_le r 0 k).trans (by simp)) bot_le

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Fact (1 ≤ p)] in
/-- The dyadic moduli are homogeneous: `ω_r(c f, 2^(-k))_p = |c| ω_r(f, 2^(-k))_p`
(`Rd.modulus_const_smul`). -/
theorem lpModulus_const_smul (r : ℕ) (c : ℂ) (f : Lp ℂ p μ) (k : ℕ) :
    lpModulus p r (c • f) k = ‖c‖ₑ * lpModulus p r f k := by
  rw [lpModulus, modulus_congr_ae (Lp.coeFn_smul c f), modulus_const_smul]
  rfl

end Rd
