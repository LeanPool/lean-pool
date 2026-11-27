/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.FourierMultipliers.TriebelLizorkinMultipliers
public import LeanPool.FunctionSpaces.Rd.BesselPotentials.BesselPotentialLifting

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bessel potential spaces of tempered distributions `H^{s,p} = F^s_{p,2}`

Let `V` have dimension `n ≥ 1` and `1 < p < ∞`. A tempered distribution `u` lies in Mathlib's
Bessel potential space `H^{s,p}(V)` (`TemperedDistribution.MemSobolev s p`) iff it lies in
`F^s_{p,2}` of tempered distributions (`Rd.MemTriebelLizorkinDistr`), for every real `s`
(`Rd.memSobolev_bessel_iff_memTriebelLizorkinDistr`), with existential constants in both
directions, also for Mathlib's bundled space.

* **`H^{s,p} ⊆ F^s_{p,2}`**: if `J_s u = h ∈ L_p`, then `u = J_{-s} h` is the Fourier multiplier
  of order `-s` applied to `h ∈ L_p = F^0_{p,2}`, so `‖u‖_{F^s_{p,2}} ≤ C ‖h‖_p`
  (`Rd.exists_triebelLizorkinNormDistr_le_of_besselPotential_eq`).
* **`F^s_{p,2} ⊆ H^{s,p}`**: if the blocks of `u` are `L_p` functions `g_j`, the blocks of `J_s u`
  are `(J_s ψTilde_j) ⋆ g_j` (`Rd.distribBlock_besselPotential`), whose partial sums converge in
  `L_p`
  by the synthesis bound of the Calderón–Zygmund family of the dilated Bessel kernels
  (`Rd.eLpNorm_sum_conv_besselSchwartz_le`, `Rd.exists_tendsto_sum_convLp`); their limit is
  `J_s u` (`Rd.eq_of_tendsto_sum_distribBlock`), so
  `‖J_s u‖_p ≤ C ‖u‖_{F^s_{p,2}}` (`Rd.exists_besselPotential_eq_of_memTriebelLizorkinDistr`).
-/

@[expose] public section

open MeasureTheory Filter Module
open scoped ENNReal Topology SchwartzMap FourierTransform BesselPotentialSpace
open ENNReal (lqNorm dyadicWeight)
open TemperedDistribution (besselPotential)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Synthesis sums of families in `L_p` -/

/-- **Convergent synthesis sums of `L_p` families**: let `1 ≤ p < ∞`, `σ` real, `g_j ∈ L_p(V)`
with `‖ x ↦ ‖(2^{jσ} |g_j(x)|)_j‖_{ℓ_2} ‖_p < ∞`, and `K_j` Schwartz kernels with
`‖∑_{j ∈ t} K_j ⋆ g_j‖_p ≤ C ‖ x ↦ ‖(1_t(j) 2^{jσ} |g_j(x)|)_j‖_{ℓ_2} ‖_p` for every finite `t` and
some finite `C`. Then the partial sums `∑_{j < J} K_j ⋆ g_j` converge in `L_p(V)` to some `h`
with `‖h‖_p ≤ C ‖ x ↦ ‖(2^{jσ} |g_j(x)|)_j‖_{ℓ_2} ‖_p`. Their differences are bounded by the
tails of the weighted family, which tend to zero
(`MeasureTheory.cauchySeq_of_edist_le_lqNorm_ite`). This is the general form of
`Rd.exists_tendsto_sum_conv_blockFun`, whose families are the blocks `ψ_j ⋆ f`. -/
theorem exists_tendsto_sum_convLp (hp : p ≠ ∞) {σ : ℝ} {K : ℕ → 𝓢(V, ℂ)} {C : ℝ≥0∞}
    (hC : C ≠ ∞) {g : ℕ → Lp ℂ p (volume : Measure V)}
    (hG : eLpNorm (fun x => lqNorm 2 fun j => dyadicWeight σ j * ‖g j x‖ₑ) p volume ≠ ∞)
    (hK : ∀ t : Finset ℕ, eLpNorm (fun x => ∑ j ∈ t, conv (K j) (g j) volume x) p volume ≤
      C * eLpNorm (fun x => lqNorm 2 fun j =>
        if j ∈ t then dyadicWeight σ j * ‖g j x‖ₑ else 0) p volume) :
    ∃ h : Lp ℂ p (volume : Measure V),
      Tendsto (fun J => ∑ j ∈ Finset.range J, convLp hp (K j).integrable (g j)) atTop (𝓝 h) ∧
      ‖h‖ₑ ≤ C * eLpNorm (fun x => lqNorm 2 fun j => dyadicWeight σ j * ‖g j x‖ₑ) p volume := by
  have hmeas : ∀ j, AEMeasurable (fun x => dyadicWeight σ j * ‖g j x‖ₑ) volume := fun j =>
    (Lp.aestronglyMeasurable (g j)).eNorm.const_mul _
  have hS : CauchySeq fun J => ∑ j ∈ Finset.range J, convLp hp (K j).integrable (g j) := by
    refine cauchySeq_of_edist_le_lqNorm_ite (p := p) (q := 2) hC
      (zero_lt_one.trans_le Fact.out).ne' hp two_ne_zero ENNReal.ofNat_ne_top hmeas hG
      fun N N' hNN' => ?_
    have hd : edist (∑ j ∈ Finset.range N', convLp hp (K j).integrable (g j))
        (∑ j ∈ Finset.range N, convLp hp (K j).integrable (g j)) =
        eLpNorm (fun x => ∑ j ∈ Finset.Ico N N', conv (K j) (g j) volume x) p volume := by
      rw [eDist_eq_eNorm_sub, ← Finset.sum_Ico_eq_sub _ hNN', Lp.eNorm_def]
      exact eLpNorm_congr_ae (coeFn_sum_convLp_ae hp K g _)
    rw [hd]
    exact (hK _).trans (mul_le_mul_of_nonneg_left (eLpNorm_lqNorm_ite_mono hmeas
      fun j hj => (Finset.mem_Ico.1 hj).1) (zero_le (a := C)))
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete hS
  refine ⟨h, hh, le_of_tendsto' hh.eNorm fun J => ?_⟩
  rw [Lp.eNorm_def, eLpNorm_congr_ae (coeFn_sum_convLp_ae hp K g _)]
  exact (hK _).trans
    (mul_le_mul_of_nonneg_left (eLpNorm_lqNorm_ite_le hmeas) (zero_le (a := C)))

/-! ### The blocks of a Bessel potential -/

/-- **The blocks of a Bessel potential**: for `1 ≤ p < ∞`, real `s` and a tempered distribution
`u` whose block `Δ_j u` is an `L_p` function `g`, the block `Δ_j(J_s u)` is the `L_p` function
`(J_s ψTilde_j) ⋆ g` (`Rd.distribBlock_fourierMultiplierCLM_eq_convLp` for the Bessel weight). -/
theorem distribBlock_besselPotential (hp : p ≠ ∞) (s : ℝ) {u : 𝓢'(V, ℂ)} {j : ℕ}
    {g : Lp ℂ p (volume : Measure V)} (hg : distribBlock j u = (g : 𝓢'(V, ℂ))) :
    distribBlock j (besselPotential V ℂ s u) =
      (convLp hp (besselSchwartz s (psiDualS j)).integrable g : 𝓢'(V, ℂ)) :=
  distribBlock_fourierMultiplierCLM_eq_convLp hp (hasTemperateGrowth_besselWeight s) hg

/-! ### `H^{s,p} ⊆ F^s_{p,2}` -/

/-- **`H^{s,p} ⊆ F^s_{p,2}` for tempered distributions, with norm bound**: in dimension `n ≥ 1`,
for `1 < p < ∞` and every real `s` there is a finite constant `C` such that
`‖u‖_{F^s_{p,2}} ≤ C ‖h‖_p` for every tempered distribution `u` and `h ∈ L_p(V)` with
`J_s u = h`; the constant is existential. Here `u = J_{-s} h` (Mathlib's
`TemperedDistribution.besselPotential_neg_apply_eq_iff`) is the Fourier multiplier with the
symbol `⟨ξ⟩^{-s}` of order `-s` (`Rd.hasSymbolGrowth_besselWeight`) applied to `h`, so
`Rd.exists_triebelLizorkinNormDistr_fourierMultiplier_le` with `s = 0` and the square function
bound `‖h‖_{F^0_{p,2}} ≤ Q_{V,p} ‖h‖_p` (`Rd.triebelLizorkinNorm_zero_two_le`) apply. -/
theorem exists_triebelLizorkinNormDistr_le_of_besselPotential_eq [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (u : 𝓢'(V, ℂ)) (h : Lp ℂ p (volume : Measure V)),
      besselPotential V ℂ s u = h → triebelLizorkinNormDistr p s 2 u ≤ C * ‖h‖ₑ := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNormDistr_fourierMultiplier_le (V := V) hp1 hp
    ENNReal.one_lt_two (hasSymbolGrowth_besselWeight (-s)) 0
  refine ⟨C * squareFunctionConst V p, ENNReal.mul_ne_top hC (squareFunctionConst_ne_top hp1 hp),
    fun u h huh => ?_⟩
  have hu : besselPotential V ℂ (-s) (h : 𝓢'(V, ℂ)) = u :=
    (TemperedDistribution.besselPotential_neg_apply_eq_iff s _ _).2 huh
  have hb := hCu (h : 𝓢'(V, ℂ))
  rw [zero_sub, neg_neg, triebelLizorkinNormDistr_toTemperedDistribution hp] at hb
  calc triebelLizorkinNormDistr p s 2 u = triebelLizorkinNormDistr p s 2
        (TemperedDistribution.fourierMultiplierCLM ℂ (fun ξ => (besselWeight (-s) ξ : ℂ))
          (h : 𝓢'(V, ℂ))) := by rw [← hu]; rfl
    _ ≤ C * triebelLizorkinNorm 0 2 h := hb
    _ ≤ C * (squareFunctionConst V p * ‖h‖ₑ) := by
        exact mul_le_mul_of_nonneg_left (triebelLizorkinNorm_zero_two_le hp1 hp h)
          (zero_le (a := C))
    _ = C * squareFunctionConst V p * ‖h‖ₑ := (mul_assoc _ _ _).symm

/-! ### `F^s_{p,2} ⊆ H^{s,p}` -/

/-- **`F^s_{p,2} ⊆ H^{s,p}` for tempered distributions, with norm bound**: in dimension `n ≥ 1`,
for `1 < p < ∞` and every real `s` there is a finite constant `C` such that for every tempered
distribution `u ∈ F^s_{p,2}` the Bessel potential `J_s u` is an `L_p` function `h` with
`‖h‖_p ≤ C ‖u‖_{F^s_{p,2}}`; the constant is existential. If the blocks of `u` are the `L_p`
functions `g_j`, the blocks of `J_s u` are `(J_s ψTilde_j) ⋆ g_j`
(`Rd.distribBlock_besselPotential`);
their partial sums converge in `L_p` (`Rd.exists_tendsto_sum_convLp`, with the synthesis bound
`Rd.eLpNorm_sum_conv_besselSchwartz_le` of the Calderón–Zygmund family
`Rd.exists_isCZFamily_besselBase_psiDualBase`), and the limit is `J_s u`
(`Rd.eq_of_tendsto_sum_distribBlock`). -/
theorem exists_besselPotential_eq_of_memTriebelLizorkinDistr [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ u : 𝓢'(V, ℂ), MemTriebelLizorkinDistr p s 2 u →
      ∃ h : Lp ℂ p (volume : Measure V), besselPotential V ℂ s u = h ∧
        ‖h‖ₑ ≤ C * triebelLizorkinNormDistr p s 2 u := by
  obtain ⟨B, H, hB, hH, hθ⟩ := exists_isCZFamily_besselBase_psiDualBase (V := V) s
  refine ⟨czConst V p B H, czConst_ne_top hp1 hp hB hH, fun u hu => ?_⟩
  obtain ⟨g, hg⟩ := hu.exists_blocks
  have hnorm := triebelLizorkinNormDistr_eq (s := s) (q := 2) hg
  obtain ⟨h, hlim, hh⟩ := exists_tendsto_sum_convLp hp (K := fun j => besselSchwartz s (psiDualS j))
    (czConst_ne_top hp1 hp hB hH) (hnorm ▸ hu.ne)
    fun t => eLpNorm_sum_conv_besselSchwartz_le hp1 hp hθ t fun j => Lp.memLp (g j)
  exact ⟨h, eq_of_tendsto_sum_distribBlock (fun j => distribBlock_besselPotential hp s (hg j)) hlim,
    hnorm ▸ hh⟩

/-- **`F^s_{p,2} ⊆ H^{s,p}`**: in dimension `n ≥ 1`, for `1 < p < ∞` and real `s`, every tempered
distribution `u ∈ F^s_{p,2}` lies in Mathlib's Bessel potential space: `J_s u ∈ L_p(V)`
(`Rd.exists_besselPotential_eq_of_memTriebelLizorkinDistr`). -/
theorem memSobolev_bessel_of_memTriebelLizorkinDistr [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {s : ℝ} {u : 𝓢'(V, ℂ)} (hu : MemTriebelLizorkinDistr p s 2 u) :
    TemperedDistribution.MemSobolev s p u := by
  obtain ⟨C, -, hC⟩ := exists_besselPotential_eq_of_memTriebelLizorkinDistr (V := V) hp1 hp s
  obtain ⟨h, hh, -⟩ := hC u hu
  exact ⟨h, hh⟩

/-! ### `H^{s,p} = F^s_{p,2}` -/

/-- **`H^{s,p} = F^s_{p,2}` for every real `s`**: in dimension `n ≥ 1`, for `1 < p < ∞`, real `s`
and every tempered distribution `u` on `V`, `u` lies in Mathlib's Bessel potential space
`H^{s,p}(V)` iff it lies in `F^s_{p,2}` of tempered distributions
(`Rd.exists_triebelLizorkinNormDistr_le_of_besselPotential_eq`,
`Rd.memSobolev_bessel_of_memTriebelLizorkinDistr`). -/
theorem memSobolev_bessel_iff_memTriebelLizorkinDistr [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    (s : ℝ) (u : 𝓢'(V, ℂ)) :
    TemperedDistribution.MemSobolev s p u ↔ MemTriebelLizorkinDistr p s 2 u := by
  refine ⟨fun ⟨h, hh⟩ => ?_, memSobolev_bessel_of_memTriebelLizorkinDistr hp1 hp⟩
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNormDistr_le_of_besselPotential_eq (V := V) hp1 hp s
  exact (hCu u h hh).trans_lt (ENNReal.mul_lt_top hC.lt_top eNorm_lt_top)

/-- **`H^{s,p} ⊆ F^s_{p,2}` in Mathlib's bundled space**: in dimension `n ≥ 1`, for `1 < p < ∞`
and every real `s` there is a finite constant `C` with `‖F‖_{F^s_{p,2}} ≤ C ‖F‖_{H^{s,p}}` for
every element `F` of Mathlib's `H^{s,p}(V)`, as a tempered distribution; the constant is
existential (`Rd.exists_triebelLizorkinNormDistr_le_of_besselPotential_eq`,
`BesselPotentialSpace.enorm_toLp_eq`). -/
theorem exists_triebelLizorkinNormDistr_le_besselPotentialSpace [Nontrivial V] (hp1 : 1 < p)
    (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : H^{s, p}(V, ℂ),
      triebelLizorkinNormDistr p s 2 F.toDistr ≤ C * ‖F‖ₑ := by
  obtain ⟨C, hC, hCu⟩ := exists_triebelLizorkinNormDistr_le_of_besselPotential_eq (V := V) hp1 hp s
  refine ⟨C, hC, fun F => ?_⟩
  rw [← BesselPotentialSpace.enorm_toLp_eq]
  exact hCu F.toDistr F.toLp F.bessel_toDistr_eq_toLp

/-- **`F^s_{p,2} ⊆ H^{s,p}` in Mathlib's bundled space**: in dimension `n ≥ 1`, for `1 < p < ∞`
and every real `s` there is a finite constant `C` such that every tempered distribution
`u ∈ F^s_{p,2}`, as an element of Mathlib's `H^{s,p}(V)`, has
`‖u‖_{H^{s,p}} ≤ C ‖u‖_{F^s_{p,2}}`; the constant is existential. The `L_p` function of the bundled
element is the function `h` of `Rd.exists_besselPotential_eq_of_memTriebelLizorkinDistr`, since
both represent `J_s u` (`Rd.eq_of_toTemperedDistribution_eq`,
`BesselPotentialSpace.enorm_toLp_eq`). -/
theorem exists_enorm_besselPotentialSpace_le_triebelLizorkinNormDistr [Nontrivial V]
    (hp1 : 1 < p) (hp : p ≠ ∞) (s : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (u : 𝓢'(V, ℂ)) (hu : MemTriebelLizorkinDistr p s 2 u),
      ‖(memSobolev_bessel_of_memTriebelLizorkinDistr hp1 hp hu).toBesselPotentialSpace‖ₑ ≤
        C * triebelLizorkinNormDistr p s 2 u := by
  obtain ⟨C, hC, hCu⟩ := exists_besselPotential_eq_of_memTriebelLizorkinDistr (V := V) hp1 hp s
  refine ⟨C, hC, fun u hu => ?_⟩
  obtain ⟨h, hh, hnorm⟩ := hCu u hu
  set X := (memSobolev_bessel_of_memTriebelLizorkinDistr hp1 hp hu).toBesselPotentialSpace
  have hX : X.toLp = h := eq_of_toTemperedDistribution_eq (by
    rw [← X.bessel_toDistr_eq_toLp, ← hh,
      TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr])
  rw [← BesselPotentialSpace.enorm_toLp_eq, hX]
  exact hnorm

end Rd
