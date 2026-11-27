/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.Differences
public import LeanPool.FunctionSpaces.Analysis.Lp.IndicatorOperator
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Moduli of smoothness on subsets of `V`

For `U ⊆ V`, a step `h ∈ V` and `r ∈ ℕ`, the points `x` with `x, x + h, …, x + r h ∈ U` form the
set `U_{rh}` (`Rd.stepSet`, a subset of `U`). The **restricted difference** is
`Δ_h^r(f, x, U) = Δ_h^r f(x)` for `x ∈ U_{rh}` and `0` otherwise, and the **modulus of
smoothness on `U`** is

`ω_r(f, t, U)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r(f, ·, U)‖_{L_p(U)}`

(DeVore–Sharpley, (2.1); `Rd.modulusOn`). The steps `h` and `-h` give the same norm, since
`Δ_{-h}^r(f, x, U) = (-1)^r Δ_h^r(f, x - r h, U)` (`Rd.eLpNorm_indicator_stepSet_neg`). The
modulus uses only the values of `f` on `U` (`Rd.modulusOn_indicator`, `Rd.modulusOn_congr_ae`),
increases in `t`, is subadditive, is bounded by `2^r ‖f‖_{L_p(U)}` (`Rd.modulusOn_le`) and by
the modulus on `V` (`Rd.modulusOn_le_modulus`), and on `U = V` it is the modulus on `V`
(`Rd.modulusOn_univ`). `Rd.lpModulusOn` samples it for `f ∈ L_p` at the dyadic scales `2^(-k)`;
for every `G ∈ L_p`, `ω_r(f, 2^(-k), Ω)_p ≤ 2^r ‖1_Ω (f - G)‖_p + ω_r(G, 2^(-k))_p`
(`Rd.lpModulusOn_le_add_lpModulus`).
The **intrinsic Besov quasi-norm** on a measurable set `Ω` is
`N_Ω(G) = ‖1_Ω G‖_p + ‖(2^(ks) ω_r(G, 2^(-k), Ω)_p)_k‖_{ℓ_q}` (`Rd.modNormOn`); it depends only
on `1_Ω G` (`Rd.modNormOn_congr`), is subadditive for `q ≥ 1` and homogeneous
(`Rd.modNormOn_add_le`, `Rd.modNormOn_finsetSum_le`, `Rd.modNormOn_const_smul`), and grows with
the set (`Rd.modNormOn_mono_set`). If
`1_O F = 1_O f`, the intrinsic quasi-norm of `f` on `O` is at most that of `F` on `V`
(`Rd.modNormOn_le_modNorm_of_indicatorLp`), and on `O = V` the two agree (`Rd.modNormOn_univ`).

On `V` with Lebesgue measure, sets that agree up to a null set have almost equal step sets
(`Rd.stepSet_ae_eq`), the same moduli (`Rd.modulusOn_congr_set`, `Rd.lpModulusOn_congr_set`), the
same cut-offs (`Rd.indicatorLp_congr_set`) and the same intrinsic quasi-norms
(`Rd.modNormOn_congr_set`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

open ENNReal (lqNorm dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Points whose steps stay in a set -/

/-- The set `U_{rh}` of the points `x` with `x, x + h, …, x + r h ∈ U`. -/
def stepSet (U : Set V) (r : ℕ) (h : V) : Set V := {x | ∀ l ≤ r, x + (l : ℝ) • h ∈ U}

/-- `U_{rh} ⊆ U` (the case `l = 0`). -/
theorem stepSet_subset (U : Set V) (r : ℕ) (h : V) : stepSet U r h ⊆ U := fun x hx => by
  simpa using hx 0 (Nat.zero_le r)

/-- `U_{rh} ⊆ O_{rh}` for `U ⊆ O`. -/
theorem stepSet_mono {U O : Set V} (hUO : U ⊆ O) (r : ℕ) (h : V) : stepSet U r h ⊆ stepSet O r h :=
  fun _ hx l hl => hUO (hx l hl)

/-- `V_{rh} = V`. -/
@[simp]
theorem stepSet_univ (r : ℕ) (h : V) : stepSet (Set.univ : Set V) r h = Set.univ :=
  Set.eq_univ_of_forall fun _ _ _ => Set.mem_univ _

/-- **Restricted differences use only the values on `U`**:
`1_{U_{rh}} Δ_h^r (1_U f) = 1_{U_{rh}} Δ_h^r f`. -/
theorem indicator_stepSet_higherDiff_indicator (U : Set V) (r : ℕ) (h : V) (f : V → ℂ) :
    (stepSet U r h).indicator ((fwdDiff h)^[r] (U.indicator f)) =
      (stepSet U r h).indicator ((fwdDiff h)^[r] f) := by
  funext x
  by_cases hx : x ∈ stepSet U r h
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, higherDiff_apply, higherDiff_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Set.indicator_of_mem (hx l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)))]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- **Negative steps**: `x ∈ U_{r(-h)}` iff `x - r h ∈ U_{rh}`, by `l ↦ r - l`. -/
theorem mem_stepSet_neg {U : Set V} {r : ℕ} {h x : V} :
    x ∈ stepSet U r (-h) ↔ x - (r : ℝ) • h ∈ stepSet U r h := by
  have key : ∀ l ≤ r, x - (r : ℝ) • h + ((r - l : ℕ) : ℝ) • h = x + (l : ℝ) • -h :=
    fun l hl => by
      rw [Nat.cast_sub hl, smul_neg, sub_smul]
      abel
  constructor
  · intro hx l hl
    have := hx (r - l) (Nat.sub_le r l)
    rwa [← key (r - l) (Nat.sub_le r l), Nat.sub_sub_self hl] at this
  · intro hx l hl
    simpa only [key l hl] using hx (r - l) (Nat.sub_le r l)

/-- **Restricted differences with a negative step**:
`Δ_{-h}^r(f, x, U) = (-1)^r Δ_h^r(f, x - r h, U)`, from `Rd.higherDiff_neg`. -/
theorem indicator_stepSet_neg (U : Set V) (r : ℕ) (h : V) (f : V → ℂ) (x : V) :
    (stepSet U r (-h)).indicator ((fwdDiff (-h))^[r] f) x =
      (-1 : ℂ) ^ r * (stepSet U r h).indicator ((fwdDiff h)^[r] f) (x - (r : ℝ) • h) := by
  by_cases hx : x ∈ stepSet U r (-h)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_stepSet_neg.1 hx), higherDiff_neg,
      Nat.cast_smul_eq_nsmul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt mem_stepSet_neg.2 hx), mul_zero]

/-! ### The modulus of smoothness on a set -/

variable [MeasurableSpace V] {μ : Measure V}

variable (μ) in
/-- The **modulus of smoothness on `U`**, `ω_r(f, t, U)_p = sup_{‖h‖ ≤ t} ‖Δ_h^r(f, ·, U)‖_p`,
with the restricted difference `Δ_h^r(f, ·, U) = 1_{U_{rh}} Δ_h^r f`. -/
noncomputable def modulusOn (U : Set V) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (h : V) (_ : ‖h‖ ≤ t), eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ

/-- `‖Δ_h^r(f, ·, U)‖_p ≤ ω_r(f, t, U)_p` for `‖h‖ ≤ t`. -/
theorem eLpNorm_indicator_higherDiff_le_modulusOn {U : Set V} {r : ℕ} {p : ℝ≥0∞} {f : V → ℂ}
    {t : ℝ} {h : V} (hh : ‖h‖ ≤ t) :
    eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ ≤ modulusOn μ U r p f t :=
  le_iSup₂ (f := fun (h : V) (_ : ‖h‖ ≤ t) =>
    eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ) h hh

/-- The modulus on `U` increases in `t`. -/
theorem modulusOn_mono (U : Set V) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) :
    Monotone (modulusOn μ U r p f) :=
  fun _ _ hst => iSup₂_le fun _ hh => eLpNorm_indicator_higherDiff_le_modulusOn (hh.trans hst)

/-- The modulus on `V` is the modulus. -/
@[simp]
theorem modulusOn_univ (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) :
    modulusOn μ Set.univ r p f t = modulus μ r p f t := by
  simp [modulusOn, modulus]

/-- **The modulus on `U` uses only the values on `U`**: `ω_r(1_U f, t, U)_p = ω_r(f, t, U)_p`. -/
theorem modulusOn_indicator (U : Set V) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ) (t : ℝ) :
    modulusOn μ U r p (U.indicator f) t = modulusOn μ U r p f t := by
  simp only [modulusOn, indicator_stepSet_higherDiff_indicator]

/-- The modulus on `U` is subadditive. -/
theorem modulusOn_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (U : Set V) (r : ℕ) (f g : V → ℂ) (t : ℝ) :
    modulusOn μ U r p (f + g) t ≤ modulusOn μ U r p f t + modulusOn μ U r p g t := by
  refine iSup₂_le fun h hh => ?_
  rw [fwdDiff_iter_add, Set.indicator_add']
  exact (eLpNorm_add_le hp).trans (add_le_add (eLpNorm_indicator_higherDiff_le_modulusOn hh)
    (eLpNorm_indicator_higherDiff_le_modulusOn hh))

variable [BorelSpace V]

/-- `U_{rh}` is measurable for measurable `U`. -/
theorem measurableSet_stepSet {U : Set V} (hU : MeasurableSet U) (r : ℕ) (h : V) :
    MeasurableSet (stepSet U r h) := by
  simp only [stepSet, Set.ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ => measurable_add_const _ hU

/-- **A restricted difference has the same norm for the steps `h` and `-h`**:
`‖Δ_{-h}^r(f, ·, U)‖_p = ‖Δ_h^r(f, ·, U)‖_p` for a translation-invariant `μ`, by the substitution
`x ↦ x - r h` (Mathlib's `MeasurableEmbedding.eLpNorm_map_measure`). -/
theorem eLpNorm_indicator_stepSet_neg [μ.IsAddRightInvariant] (U : Set V) (r : ℕ) (p : ℝ≥0∞)
    (h : V) (f : V → ℂ) :
    eLpNorm ((stepSet U r (-h)).indicator ((fwdDiff (-h))^[r] f)) p μ =
      eLpNorm ((stepSet U r h).indicator ((fwdDiff h)^[r] f)) p μ := by
  set G := (stepSet U r h).indicator ((fwdDiff h)^[r] f)
  have hemb : MeasurableEmbedding fun x : V => x - (r : ℝ) • h :=
    (MeasurableEquiv.subRight ((r : ℝ) • h)).measurableEmbedding
  have hfun : (stepSet U r (-h)).indicator ((fwdDiff (-h))^[r] f) =
      ((-1 : ℂ) ^ r) • (G ∘ fun x => x - (r : ℝ) • h) :=
    funext fun x => indicator_stepSet_neg U r h f x
  rw [hfun, eLpNorm_const_smul, eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul,
    ← hemb.eLpNorm_map_measure, map_sub_right_eq_self]

/-- **The modulus on `U` is at most the modulus on `V`**, `ω_r(f, t, U)_p ≤ ω_r(f, t)_p`. -/
theorem modulusOn_le_modulus {U : Set V} (hU : MeasurableSet U) (r : ℕ) (p : ℝ≥0∞) (f : V → ℂ)
    (t : ℝ) : modulusOn μ U r p f t ≤ modulus μ r p f t :=
  iSup₂_mono fun h _ => eLpNorm_indicator_le _ (measurableSet_stepSet hU r h).nullMeasurableSet

variable [μ.IsAddHaarMeasure]

/-- **The modulus on a set grows with the set**: `ω_r(f, t, U)_p ≤ ω_r(f, t, O)_p` for `U ⊆ O`. -/
theorem modulusOn_mono_set {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {U O : Set V}
    (hU : MeasurableSet U) (hUO : U ⊆ O) (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulusOn μ U r p f t ≤ modulusOn μ O r p f t :=
  iSup₂_mono fun h _ => eLpNorm_mono
    ((aestronglyMeasurable_higherDiff hf r h).indicator (measurableSet_stepSet hU r h))
    fun x => norm_indicator_le_of_subset (stepSet_mono hUO r h) _ x

/-- `ω_r(f, t, U)_p ≤ 2^r ‖f‖_{L_p(U)}`. -/
theorem modulusOn_le {f : V → ℂ} (hf : AEStronglyMeasurable f μ) {U : Set V}
    (hU : MeasurableSet U) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (t : ℝ) :
    modulusOn μ U r p f t ≤ 2 ^ r * eLpNorm (U.indicator f) p μ := by
  rw [← modulusOn_indicator]
  exact (modulusOn_le_modulus hU r p _ t).trans (modulus_le (hf.indicator hU) hp r t)

/-- **The modulus on `U` depends only on the class of `f` on `U`**: if `1_U f = 1_U g` almost
everywhere, then `ω_r(f, t, U)_p = ω_r(g, t, U)_p`. -/
theorem modulusOn_congr_ae {U : Set V} {f g : V → ℂ} (hfg : U.indicator f =ᵐ[μ] U.indicator g)
    (r : ℕ) (p : ℝ≥0∞) (t : ℝ) : modulusOn μ U r p f t = modulusOn μ U r p g t := by
  rw [← modulusOn_indicator U r p f, ← modulusOn_indicator U r p g]
  simp only [modulusOn]
  congr 1
  funext h
  congr 1
  funext _
  refine eLpNorm_congr_ae ?_
  filter_upwards [higherDiff_congr_ae hfg r h] with x hx
  by_cases hxU : x ∈ stepSet U r h
  · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, hx]
  · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]

/-! ### The modulus on a set at dyadic scales -/

variable {p : ℝ≥0∞}

variable (p) in
/-- The modulus on `U` of an element of `L_p` at the dyadic scale `2^(-k)`. -/
noncomputable def lpModulusOn (U : Set V) (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) : ℝ≥0∞ :=
  modulusOn μ U r p (f : V → ℂ) (1 / 2 ^ k)

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The modulus on `U` decreases along the dyadic scales. -/
theorem lpModulusOn_succ_le (U : Set V) (r : ℕ) (f : Lp ℂ p μ) (k : ℕ) :
    lpModulusOn p U r f (k + 1) ≤ lpModulusOn p U r f k :=
  modulusOn_mono U r p _ (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ one_le_two (Nat.le_succ k)))

omit [μ.IsAddHaarMeasure] in
/-- `ω_r(f, 2^(-k), U)_p ≤ ω_r(f, 2^(-k))_p` on `L_p`. -/
theorem lpModulusOn_le_lpModulus {U : Set V} (hU : MeasurableSet U) (r : ℕ)
    (f : Lp ℂ p μ) (k : ℕ) : lpModulusOn p U r f k ≤ lpModulus p r f k :=
  modulusOn_le_modulus hU r p _ _

/-- The modulus on a set at the dyadic scales grows with the set. -/
theorem lpModulusOn_mono_set {U O : Set V} (hU : MeasurableSet U) (hUO : U ⊆ O) (r : ℕ)
    (f : Lp ℂ p μ) (k : ℕ) : lpModulusOn p U r f k ≤ lpModulusOn p O r f k :=
  modulusOn_mono_set (Lp.aestronglyMeasurable f) hU hUO r p _

/-- Elements of `L_p` that agree on `U` have the same moduli on `U`. -/
theorem lpModulusOn_congr {U : Set V} {f g : Lp ℂ p μ}
    (hfg : U.indicator f =ᵐ[μ] U.indicator g) (r k : ℕ) :
    lpModulusOn p U r f k = lpModulusOn p U r g k :=
  modulusOn_congr_ae hfg r p _

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- `ω_r(c f, t, U)_p = |c| ω_r(f, t, U)_p`. -/
theorem modulusOn_const_smul (U : Set V) (r : ℕ) (p : ℝ≥0∞) (c : ℂ) (f : V → ℂ) (t : ℝ) :
    modulusOn μ U r p (c • f) t = ‖c‖ₑ * modulusOn μ U r p f t := by
  simp only [modulusOn, fwdDiff_iter_const_smul, ENNReal.mul_iSup]
  congr 1
  funext h
  congr 1
  funext _
  rw [← eLpNorm_const_smul]
  congr 1
  funext x
  by_cases hx : x ∈ stepSet U r h
  · simp only [Set.indicator_of_mem hx, Pi.smul_apply]
  · simp only [Set.indicator_of_notMem hx, Pi.smul_apply, smul_zero]

/-- The dyadic moduli on `U` are homogeneous: `ω_r(c f, 2^(-k), U)_p = |c| ω_r(f, 2^(-k), U)_p`. -/
theorem lpModulusOn_const_smul (U : Set V) (r : ℕ) (c : ℂ) (f : Lp ℂ p μ) (k : ℕ) :
    lpModulusOn p U r (c • f) k = ‖c‖ₑ * lpModulusOn p U r f k := by
  have h : U.indicator ((c • f : Lp ℂ p μ) : V → ℂ) =ᵐ[μ] U.indicator (c • (f : V → ℂ)) := by
    filter_upwards [Lp.coeFn_smul c f] with x hx
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, hx]
    · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]
  rw [lpModulusOn, modulusOn_congr_ae h, modulusOn_const_smul]
  rfl

/-- The modulus on `U` of elements of `L_p` is subadditive. -/
theorem lpModulusOn_add_le [Fact (1 ≤ p)] (U : Set V) (r : ℕ) (f g : Lp ℂ p μ) (k : ℕ) :
    lpModulusOn p U r (f + g) k ≤ lpModulusOn p U r f k + lpModulusOn p U r g k := by
  rw [lpModulusOn, modulusOn_congr_ae (g := (f : V → ℂ) + (g : V → ℂ)) ?_ r p _]
  · exact modulusOn_add_le Fact.out U r _ _ _
  · filter_upwards [Lp.coeFn_add f g] with x hx
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, hx]
    · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]

/-- `ω_r(f, 2^(-k), U)_p ≤ 2^r ‖f‖_p` on `L_p`. -/
theorem lpModulusOn_le [Fact (1 ≤ p)] {U : Set V} (hU : MeasurableSet U) (r : ℕ) (f : Lp ℂ p μ)
    (k : ℕ) : lpModulusOn p U r f k ≤ 2 ^ r * ‖f‖ₑ :=
  (modulusOn_le (Lp.aestronglyMeasurable f) hU Fact.out r _).trans
    (mul_le_mul' le_rfl
      ((eLpNorm_indicator_le _ hU.nullMeasurableSet).trans_eq (Lp.eNorm_def f).symm))

/-- **The modulus on `Ω` through a function on `V`**: for a measurable `Ω`, `p ≥ 1` and
`f, G ∈ L_p`, `ω_r(f, 2^(-k), Ω)_p ≤ 2^r ‖1_Ω (f - G)‖_p + ω_r(G, 2^(-k))_p`. Split
`f = (f - G) + G` (`Rd.lpModulusOn_add_le`); the modulus of `f - G` on `Ω` sees only
`1_Ω (f - G)` (`Rd.lpModulusOn_congr`, `Rd.lpModulusOn_le`), and that of `G` is at most its
modulus on `V` (`Rd.lpModulusOn_le_lpModulus`). -/
theorem lpModulusOn_le_add_lpModulus [Fact (1 ≤ p)] {Ω : Set V} (hΩ : MeasurableSet Ω) (r : ℕ)
    (f G : Lp ℂ p μ) (k : ℕ) :
    lpModulusOn p Ω r f k ≤ 2 ^ r * ‖indicatorLp hΩ (f - G)‖ₑ + lpModulus p r G k := by
  have hfG : Ω.indicator ((f - G : Lp ℂ p μ) : V → ℂ) =ᵐ[μ]
      Ω.indicator (indicatorLp hΩ (f - G) : V → ℂ) := by
    filter_upwards [indicatorLp_apply_ae hΩ (f - G)] with x hx
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ, hx, Set.indicator_of_mem hxΩ]
    · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ]
  calc lpModulusOn p Ω r f k = lpModulusOn p Ω r ((f - G) + G) k := by rw [sub_add_cancel]
    _ ≤ lpModulusOn p Ω r (f - G) k + lpModulusOn p Ω r G k := lpModulusOn_add_le Ω r _ _ k
    _ ≤ 2 ^ r * ‖indicatorLp hΩ (f - G)‖ₑ + lpModulus p r G k := by
        gcongr
        · rw [lpModulusOn_congr hfG r k]
          exact lpModulusOn_le hΩ r _ k
        · exact lpModulusOn_le_lpModulus hΩ r G k

/-! ### The intrinsic quasi-norm -/

section ModNormOn

variable [Fact (1 ≤ p)] {Ω : Set V} (hΩ : MeasurableSet Ω)

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- The **intrinsic Besov quasi-norm** on a measurable set `Ω`:
`N_Ω(G) = ‖1_Ω G‖_p + ‖(2^(ks) ω_r(G, 2^(-k), Ω)_p)_k‖_{ℓ_q}`. -/
noncomputable def modNormOn (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (G : Lp ℂ p μ) : ℝ≥0∞ :=
  ‖indicatorLp hΩ G‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r G k)

/-- **The intrinsic quasi-norm sees only `1_Ω G`**: equal cut-offs give equal quasi-norms. -/
theorem modNormOn_congr {r : ℕ} {s : ℝ} {q : ℝ≥0∞} {G₁ G₂ : Lp ℂ p μ}
    (h : indicatorLp hΩ G₁ = indicatorLp hΩ G₂) :
    modNormOn hΩ r s q G₁ = modNormOn hΩ r s q G₂ := by
  have hae : Ω.indicator G₁ =ᵐ[μ] Ω.indicator G₂ := by
    filter_upwards [indicatorLp_apply_ae hΩ G₁, indicatorLp_apply_ae hΩ G₂] with x h1 h2
    rw [← h1, ← h2, h]
  simp only [modNormOn, h, lpModulusOn_congr hae]

/-- `N_Ω(0) = 0`. -/
theorem modNormOn_zero (r : ℕ) (s : ℝ) (q : ℝ≥0∞) :
    modNormOn hΩ r s q (0 : Lp ℂ p μ) = 0 := by
  have h : ∀ k, lpModulusOn p Ω r (0 : Lp ℂ p μ) k = 0 := fun k =>
    le_antisymm ((lpModulusOn_le_lpModulus hΩ r 0 k).trans_eq (lpModulus_zero r k)) zero_le
  simp only [modNormOn, map_zero, eNorm_zero, h, mul_zero, ENNReal.lqNorm_zero_right, add_zero]

/-- **The intrinsic quasi-norm is subadditive** for `q ≥ 1`. -/
theorem modNormOn_add_le (r : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) (G G' : Lp ℂ p μ) :
    modNormOn hΩ r s q (G + G') ≤ modNormOn hΩ r s q G + modNormOn hΩ r s q G' := by
  have h1 : ‖indicatorLp hΩ (G + G')‖ₑ ≤ ‖indicatorLp hΩ G‖ₑ + ‖indicatorLp hΩ G'‖ₑ := by
    rw [map_add]
    exact eNorm_add_le _ _
  have h2 : lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r (G + G') k) ≤
      lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r G k) +
        lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r G' k) :=
    (ENNReal.lqNorm_mono fun k => (mul_le_mul' le_rfl (lpModulusOn_add_le Ω r G G' k)).trans_eq
      (mul_add _ _ _)).trans (ENNReal.lqNorm_add_le hq _ _)
  calc modNormOn hΩ r s q (G + G')
      ≤ (‖indicatorLp hΩ G‖ₑ + ‖indicatorLp hΩ G'‖ₑ) +
          (lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r G k) +
            lqNorm q (fun k => dyadicWeight s k * lpModulusOn p Ω r G' k)) := add_le_add h1 h2
    _ = modNormOn hΩ r s q G + modNormOn hΩ r s q G' := by
        simp only [modNormOn]
        ring

/-- **The intrinsic quasi-norm is homogeneous**: `N_Ω(c G) = |c| N_Ω(G)`. -/
theorem modNormOn_const_smul (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (c : ℂ) (G : Lp ℂ p μ) :
    modNormOn hΩ r s q (c • G) = ‖c‖ₑ * modNormOn hΩ r s q G := by
  have h : (fun k => dyadicWeight s k * lpModulusOn p Ω r (c • G) k) =
      fun k => ‖c‖ₑ * (dyadicWeight s k * lpModulusOn p Ω r G k) := funext fun k => by
    rw [lpModulusOn_const_smul]
    ring
  simp only [modNormOn, map_smul, eNorm_smul, h, ENNReal.lqNorm_const_mul, mul_add]

/-- **The intrinsic quasi-norm of a finite sum** is at most the sum of the quasi-norms. -/
theorem modNormOn_finsetSum_le (r : ℕ) (s : ℝ) {q : ℝ≥0∞} (hq : 1 ≤ q) {ι : Type*}
    (t : Finset ι) (G : ι → Lp ℂ p μ) :
    modNormOn hΩ r s q (∑ i ∈ t, G i) ≤ ∑ i ∈ t, modNormOn hΩ r s q (G i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [modNormOn_zero]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (modNormOn_add_le hΩ r s hq _ _).trans (add_le_add le_rfl ih)

end ModNormOn

/-- **The intrinsic quasi-norm grows with the set**: for measurable `T ⊆ U`,
`N_T(f) ≤ N_U(f)`, where `N_U(f) = ‖1_U f‖_p + ‖(2^(ks) ω_r(f, 2^(-k), U)_p)_k‖_{ℓ_q}`
(`Rd.lpModulusOn_mono_set`). -/
theorem modNormOn_mono_set [Fact (1 ≤ p)] {T U : Set V} (hT : MeasurableSet T)
    (hU : MeasurableSet U) (hTU : T ⊆ U) (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) :
    modNormOn hT r s q f ≤ modNormOn hU r s q f := by
  unfold modNormOn
  refine add_le_add ?_ (ENNReal.lqNorm_mono fun k =>
    mul_le_mul' le_rfl (lpModulusOn_mono_set hT hTU r f k))
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hT f),
    eLpNorm_congr_ae (indicatorLp_apply_ae hU f)]
  exact eLpNorm_mono ((Lp.aestronglyMeasurable f).indicator hT)
    fun x => norm_indicator_le_of_subset hTU _ x

/-- **Restrictions have finite intrinsic moduli**: if `1_O F = 1_O f` for a measurable `O`, the
intrinsic quasi-norm of `f` on `O` is at most the quasi-norm of `F` on `V`. -/
theorem modNormOn_le_modNorm_of_indicatorLp [Fact (1 ≤ p)] {O : Set V} (hO : MeasurableSet O)
    (r : ℕ) (s : ℝ) (q : ℝ≥0∞) {F f : Lp ℂ p μ} (hFf : indicatorLp hO F = indicatorLp hO f) :
    modNormOn hO r s q f ≤ ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k) := by
  have hae : O.indicator F =ᵐ[μ] O.indicator f := by
    filter_upwards [indicatorLp_apply_ae hO F, indicatorLp_apply_ae hO f] with x h1 h2
    rw [← h1, ← h2, hFf]
  unfold modNormOn
  refine add_le_add ?_ (ENNReal.lqNorm_mono fun k => mul_le_mul' le_rfl ?_)
  · rw [← hFf]
    exact enorm_indicatorLp_le hO F
  · rw [← lpModulusOn_congr hae r k]
    exact lpModulusOn_le_lpModulus hO r F k

omit [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- On `U = V` the intrinsic quasi-norm is the quasi-norm of `V`:
`N_V(f) = ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}` (`Rd.modulusOn_univ`). -/
theorem modNormOn_univ [Fact (1 ≤ p)] (r : ℕ) (s : ℝ) (q : ℝ≥0∞) (f : Lp ℂ p μ) :
    modNormOn MeasurableSet.univ r s q f =
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) := by
  have h1 : ‖indicatorLp MeasurableSet.univ f‖ₑ = ‖f‖ₑ := by
    rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae _ f),
      Set.indicator_univ]
  have h2 : ∀ k, lpModulusOn p (Set.univ : Set V) r f k = lpModulus p r f k := fun k => by
    rw [lpModulusOn, modulusOn_univ, lpModulus]
  simp_rw [modNormOn, h1, h2]

end Rd

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Changing the set by a null set -/

/-- **Step sets of almost equal sets are almost equal**: the translates by `l h` of almost equal
sets are almost equal, by the translation invariance of the Lebesgue measure. -/
theorem stepSet_ae_eq {U U' : Set V} (hUU' : U =ᵐ[volume] U') (r : ℕ) (h : V) :
    stepSet U r h =ᵐ[volume] stepSet U' r h := by
  have hl : ∀ l : ℕ, ∀ᵐ x ∂(volume : Measure V),
      (x + (l : ℝ) • h ∈ U) = (x + (l : ℝ) • h ∈ U') := fun l =>
    (measurePreserving_add_right volume ((l : ℝ) • h)).quasiMeasurePreserving.ae_eq_comp
      (hUU'.mono fun _ hx => propext hx)
  filter_upwards [ae_all_iff.2 hl] with x hx
  exact forall₂_congr fun l _ => (hx l).to_iff

/-- **The modulus on a set does not see null sets**: `ω_r(f, t, U)_p = ω_r(f, t, U')_p` if `U`
and `U'` agree up to a null set. -/
theorem modulusOn_congr_set {U U' : Set V} (hUU' : U =ᵐ[volume] U') (r : ℕ) (p : ℝ≥0∞)
    (f : V → ℂ) (t : ℝ) : modulusOn volume U r p f t = modulusOn volume U' r p f t := by
  simp only [modulusOn]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_congr_ae (indicator_ae_eq_of_ae_eq_set (stepSet_ae_eq hUU' r h))

/-- The dyadic moduli on almost equal sets agree. -/
theorem lpModulusOn_congr_set {p : ℝ≥0∞} {U U' : Set V} (hUU' : U =ᵐ[volume] U') (r : ℕ)
    (f : Lp ℂ p (volume : Measure V)) (k : ℕ) :
    lpModulusOn p U r f k = lpModulusOn p U' r f k :=
  modulusOn_congr_set hUU' r p _ _

/-- The cut-offs to almost equal sets agree. -/
theorem indicatorLp_congr_set {p : ℝ≥0∞} [Fact (1 ≤ p)] {U U' : Set V} (hU : MeasurableSet U)
    (hU' : MeasurableSet U') (hUU' : U =ᵐ[volume] U') (f : Lp ℂ p (volume : Measure V)) :
    indicatorLp hU f = indicatorLp hU' f := by
  refine Lp.ext ?_
  filter_upwards [indicatorLp_apply_ae hU f, indicatorLp_apply_ae hU' f,
    indicator_ae_eq_of_ae_eq_set (f := (f : V → ℂ)) hUU'] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **Sets that agree up to a null set have the same intrinsic quasi-norm**: `N_U(G) = N_{U'}(G)`
if `U` and `U'` agree up to a null set (`Rd.indicatorLp_congr_set`, `Rd.lpModulusOn_congr_set`). -/
theorem modNormOn_congr_set {p : ℝ≥0∞} [Fact (1 ≤ p)] {U U' : Set V} (hU : MeasurableSet U)
    (hU' : MeasurableSet U') (hUU' : U =ᵐ[volume] U') (r : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (G : Lp ℂ p (volume : Measure V)) : modNormOn hU r s q G = modNormOn hU' r s q G := by
  simp only [modNormOn, indicatorLp_congr_set hU hU' hUU' G, lpModulusOn_congr_set hUU' r G]

end Rd
