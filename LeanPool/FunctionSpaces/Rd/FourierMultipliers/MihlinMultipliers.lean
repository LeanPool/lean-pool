/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.BesselPotentials.BesselPotentialDistributions

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Mihlin's multiplier theorem for symbols of order `0`

Let `V` have dimension `n ≥ 1` and `1 < p < ∞`. A symbol `m` of order `0` (`Rd.HasSymbolGrowth 0 m`,
Hörmander's class `S^0_{1,0}`) is a bounded Fourier multiplier on `L_p(V)`: for every `f ∈ L_p(V)`
the tempered distribution `m(D) f` is an `L_p` function `g` with `‖g‖_p ≤ C ‖f‖_p`, with an
existential constant (`Rd.exists_fourierMultiplier_eq_of_hasSymbolGrowth`). The symbols of order
`0` satisfy Mihlin's condition, so this is a case of Mihlin's theorem; TauCeti proves the theorem
for symbols satisfying Mihlin's condition with finitely many derivatives
(`TauCeti.exists_fourierMultiplierCLM_eq_and_norm_le_of_norm_iteratedFDeriv_le`).

The proof uses `L_p = F^0_{p,2}`: `f` lies in `F^0_{p,2}` by the square function theorem, `m(D)`
maps `F^0_{p,2}` into itself (`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le`), and
`F^0_{p,2} = H^{0,p} = L_p` (`Rd.exists_besselPotential_eq_of_memTriebelLizorkinDistr` with
`s = 0`). The multiplier is a bounded linear operator `Rd.symbolLp` on `L_p(V)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] {p : ℝ≥0∞} [Fact (1 ≤ p)] {m : V → ℂ}

/-- **Mihlin's multiplier theorem for symbols of order `0`**: in dimension `n ≥ 1`, for
`1 < p < ∞` and a symbol `m` of order `0` there is a finite constant `C` such that for every
`f ∈ L_p(V)` the tempered distribution `m(D) f` is an `L_p` function `g` with
`‖g‖_p ≤ C ‖f‖_p`; the constant is existential. By the square function theorem
`‖f‖_{F^0_{p,2}} ≤ Q_{V,p} ‖f‖_p` (`Rd.triebelLizorkinNorm_zero_two_le`), `m(D)` maps `F^0_{p,2}`
into itself (`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le`), and every tempered
distribution in `F^0_{p,2}` is an `L_p` function
(`Rd.exists_besselPotential_eq_of_memTriebelLizorkinDistr` with `s = 0`, Mathlib's
`TemperedDistribution.besselPotential_zero`). -/
theorem exists_fourierMultiplier_eq_of_hasSymbolGrowth (hp1 : 1 < p) (hp : p ≠ ∞)
    (hm : HasSymbolGrowth 0 m) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp ℂ p (volume : Measure V), ∃ g : Lp ℂ p (volume : Measure V),
      TemperedDistribution.fourierMultiplierCLM ℂ m (f : 𝓢'(V, ℂ)) = g ∧ ‖g‖ₑ ≤ C * ‖f‖ₑ := by
  obtain ⟨C₁, hC₁, hm₁⟩ := exists_triebelLizorkinNormDistr_fourierMultiplier_le (p := p) hp1 hp
    ENNReal.one_lt_two hm 0
  obtain ⟨C₂, hC₂, hb⟩ := exists_besselPotential_eq_of_memTriebelLizorkinDistr (V := V) hp1 hp 0
  refine ⟨C₂ * (C₁ * squareFunctionConst V p), ENNReal.mul_ne_top hC₂
    (ENNReal.mul_ne_top hC₁ (squareFunctionConst_ne_top hp1 hp)), fun f => ?_⟩
  have hf : triebelLizorkinNormDistr p 0 2
      (TemperedDistribution.fourierMultiplierCLM ℂ m (f : 𝓢'(V, ℂ))) ≤
        C₁ * squareFunctionConst V p * ‖f‖ₑ := by
    have h := hm₁ (f : 𝓢'(V, ℂ))
    rw [sub_zero, triebelLizorkinNormDistr_toTemperedDistribution hp] at h
    refine h.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (triebelLizorkinNorm_zero_two_le hp1 hp f) (zero_le (a := C₁))
  obtain ⟨g, hg, hgn⟩ := hb _ (hf.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hC₁.lt_top (squareFunctionConst_ne_top hp1 hp).lt_top) eNorm_lt_top))
  rw [TemperedDistribution.besselPotential_zero, ContinuousLinearMap.id_apply] at hg
  refine ⟨g, hg, hgn.trans ?_⟩
  rw [mul_assoc C₂]
  exact mul_le_mul_of_nonneg_left hf (zero_le (a := C₂))

/-- The **constant of Mihlin's theorem** for the symbol `m` of order `0`: a finite constant of
`Rd.exists_fourierMultiplier_eq_of_hasSymbolGrowth`, chosen once. -/
noncomputable def symbolLpConst (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m) : ℝ≥0∞ :=
  (exists_fourierMultiplier_eq_of_hasSymbolGrowth (V := V) hp1 hp hm).choose

/-- The constant `Rd.symbolLpConst hp1 hp hm` is finite. -/
theorem symbolLpConst_ne_top (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m) :
    symbolLpConst hp1 hp hm ≠ ∞ :=
  (exists_fourierMultiplier_eq_of_hasSymbolGrowth (V := V) hp1 hp hm).choose_spec.1

/-- For every `f ∈ L_p(V)`, `m(D) f` is an `L_p` function `g` with
`‖g‖_p ≤ Rd.symbolLpConst hp1 hp hm · ‖f‖_p`. -/
theorem exists_fourierMultiplier_eq_symbolLpConst (hp1 : 1 < p) (hp : p ≠ ∞)
    (hm : HasSymbolGrowth 0 m) (f : Lp ℂ p (volume : Measure V)) :
    ∃ g : Lp ℂ p (volume : Measure V),
      TemperedDistribution.fourierMultiplierCLM ℂ m (f : 𝓢'(V, ℂ)) = g ∧
        ‖g‖ₑ ≤ symbolLpConst hp1 hp hm * ‖f‖ₑ :=
  (exists_fourierMultiplier_eq_of_hasSymbolGrowth (V := V) hp1 hp hm).choose_spec.2 f

/-- The **`L_p` function of `m(D) f`** for a symbol `m` of order `0`, `1 < p < ∞`, `n ≥ 1` and
`f ∈ L_p(V)`, chosen by `Rd.exists_fourierMultiplier_eq_symbolLpConst`. -/
noncomputable def symbolLpFun (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m)
    (f : Lp ℂ p (volume : Measure V)) : Lp ℂ p (volume : Measure V) :=
  (exists_fourierMultiplier_eq_symbolLpConst hp1 hp hm f).choose

/-- The tempered distribution of `Rd.symbolLpFun hp1 hp hm f` is `m(D) f`, written with Mathlib's
embedding `MeasureTheory.Lp.toTemperedDistributionCLM` of `L_p` into `𝓢'`. -/
theorem toTemperedDistributionCLM_symbolLpFun (hp1 : 1 < p) (hp : p ≠ ∞)
    (hm : HasSymbolGrowth 0 m) (f : Lp ℂ p (volume : Measure V)) :
    Lp.toTemperedDistributionCLM ℂ volume p (symbolLpFun hp1 hp hm f) =
      TemperedDistribution.fourierMultiplierCLM ℂ m (Lp.toTemperedDistributionCLM ℂ volume p f) :=
  (exists_fourierMultiplier_eq_symbolLpConst hp1 hp hm f).choose_spec.1.symm

/-- **The norm bound of `Rd.symbolLpFun`** in real norms:
`‖m(D) f‖_p ≤ (Rd.symbolLpConst hp1 hp hm) ‖f‖_p`. -/
theorem norm_symbolLpFun_le (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m)
    (f : Lp ℂ p (volume : Measure V)) :
    ‖symbolLpFun hp1 hp hm f‖ ≤ (symbolLpConst hp1 hp hm).toReal * ‖f‖ := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (symbolLpConst_ne_top hp1 hp hm) eNorm_ne_top)
    (exists_fourierMultiplier_eq_symbolLpConst hp1 hp hm f).choose_spec.2
  rwa [ENNReal.toReal_mul, toReal_eNorm, toReal_eNorm] at h

/-- The **Fourier multiplier `m(D)` on `L_p(V)`** for a symbol `m` of order `0`, `1 < p < ∞`,
`n ≥ 1`: the `L_p` function of the tempered distribution `m(D) f` (`Rd.symbolLpFun`). It is
linear since `L_p` functions are determined by their tempered distributions
(`Rd.eq_of_toTemperedDistribution_eq`), and bounded with norm at most
`Rd.symbolLpConst hp1 hp hm` (Mathlib's `LinearMap.mkContinuous`). -/
noncomputable def symbolLp (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m) :
    Lp ℂ p (volume : Measure V) →L[ℂ] Lp ℂ p (volume : Measure V) :=
  LinearMap.mkContinuous
    { toFun := symbolLpFun hp1 hp hm
      map_add' := fun f g => eq_of_toTemperedDistribution_eq (by
        change Lp.toTemperedDistributionCLM ℂ volume p _ =
          Lp.toTemperedDistributionCLM ℂ volume p _
        rw [map_add, toTemperedDistributionCLM_symbolLpFun, toTemperedDistributionCLM_symbolLpFun,
          toTemperedDistributionCLM_symbolLpFun, map_add, map_add])
      map_smul' := fun c f => eq_of_toTemperedDistribution_eq (by
        change Lp.toTemperedDistributionCLM ℂ volume p _ =
          Lp.toTemperedDistributionCLM ℂ volume p _
        rw [map_smul, toTemperedDistributionCLM_symbolLpFun, toTemperedDistributionCLM_symbolLpFun,
          map_smul, map_smul, RingHom.id_apply]) }
    (symbolLpConst hp1 hp hm).toReal (norm_symbolLpFun_le hp1 hp hm)

/-- `Rd.symbolLp` is the Fourier multiplier `m(D)`: the tempered distribution of
`Rd.symbolLp hp1 hp hm f` is `m(D) f`. -/
theorem toTemperedDistribution_symbolLp (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m)
    (f : Lp ℂ p (volume : Measure V)) :
    (symbolLp hp1 hp hm f : 𝓢'(V, ℂ)) =
      TemperedDistribution.fourierMultiplierCLM ℂ m (f : 𝓢'(V, ℂ)) :=
  toTemperedDistributionCLM_symbolLpFun hp1 hp hm f

/-- **The norm bound of `Rd.symbolLp`**: `‖m(D) f‖_p ≤ Rd.symbolLpConst hp1 hp hm · ‖f‖_p`. -/
theorem enorm_symbolLp_le (hp1 : 1 < p) (hp : p ≠ ∞) (hm : HasSymbolGrowth 0 m)
    (f : Lp ℂ p (volume : Measure V)) :
    ‖symbolLp hp1 hp hm f‖ₑ ≤ symbolLpConst hp1 hp hm * ‖f‖ₑ :=
  (exists_fourierMultiplier_eq_symbolLpConst hp1 hp hm f).choose_spec.2

end Rd
