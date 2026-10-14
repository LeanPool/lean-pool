/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationLemmaProviderBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.WeightedGoodRunAssembly

/-!
# IterationLemmaProvider

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The provider theorem for the frozen iteration anchor (both conclusions)

## What is proved, and out of what

Both conclusions of `l.iteration.lemma` at the anchor's exact statement, with
the explicit `C(d) = iterConst d`:

* **Conclusion (i)** (`e.iteration.slope.lemma`) in the `exp` product form:
  the proved deterministic engine `IterationLemma.iterationSlopeBound` applied
  to the **capped** window family, with all six interface slots discharged by
  the proved producers (`hmono` from `QuasiMonotone.lean`, `hstab` from
  `SlopeStability.lean`, `hlo`/`hhi` from `SlopeStabilityEndpoints.lean`, the
  two side conditions from the sandwich), then the normalizer bridges of
  `IterationLemmaProviderGeometry.lean` and the prefactor budget
  `iterPrefactorOne_le`.
* **Conclusion (ii)** (`e.excess.decay.lemma`) in the corrected shape: the
  `θ`-weighted good-run iterate and the decay-carrying run assembly
  (`WeightedGoodRun*.lean`) at the error scale `Mp = M · Λ · (9 Ci · osc_m +
  ∑δ)`, where `Λ` is the `e.combined.bound` prefactor of the same engine.  The
  middle slot's **single** power of `M` is exactly what the weighted iterate
  buys; the `θ`-power prefactor absorbs the division remainder and the
  crossings, and the leftover `M ∑δ` proves in the `(1+M) ∑δ` slot.

The conclusion-side `∀ M` binder needs no `0 ≤ M` hypothesis: `M ≥ ε n ≥ 0` is derived
from the anchor's own sign hypothesis at `j = n` (available because `n < m`).

## Faithfulness

Every hypothesis of `iteration_lemma_provider` is a hypothesis of the frozen
theorem, character for character.  Attainment is not needed as a producer at
all: the anchor supplies the minimizer family `(c j, g j)` as a source premise,
which is the tex's own `ℓ(u, U_j)` (the standing frame).  The `j ≤ m` cap  is
honoured: no window, minimizer, or sign datum is ever read above `m`, the
capped family being constant there.

## References

* ABK26, `l.iteration.lemma`; proof Steps 1--4.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec axisCube openCubeSet originCube volumeAverage)
open Algsuperdiff.Section4.Support

noncomputable section

/-! ### Slot algebra (pure algebra over abstract reals) -/

/-- The oscillation slot of conclusion (i): the factor `9` from the normalizer bridge is
paid on the whole bracket. -/
private theorem oscSlotCollapse {Q O Sd : ℝ} (hQ : 0 ≤ Q) (hSd : 0 ≤ Sd) :
    Q * (9 * O + Sd) ≤ 9 * Q * (O + Sd) := by
  have h := mul_le_mul_of_nonneg_left (by linarith only [hSd] : Sd ≤ 9 * Sd) hQ
  have he1 : 9 * Q * (O + Sd) = Q * (9 * O) + Q * (9 * Sd) := by ring
  have he2 : Q * (9 * O + Sd) = Q * (9 * O) + Q * Sd := by ring
  have he3 : Q * (9 * Sd) = Q * (9 * Sd) := rfl
  have he4 : Q * Sd ≤ Q * (9 * Sd) := h
  linarith only [he1, he2, he3, he4]

/-- **The three slots of conclusion (ii).**  The weighted assembly's error budget
`(5/2) M Λ (9 Ci · O + Sd)` splits into the `M · O` slot and the `M · Sd` half of the
`(1+M) Sd` slot, at the common factor `K = 1 + (45/2) Ci Λ`. -/
private theorem slotCollapse {X O Sd Lam Ci M : ℝ} (hX : 0 ≤ X) (hO : 0 ≤ O)
    (hSd : 0 ≤ Sd) (hM : 0 ≤ M) (hLam : 1 ≤ Lam) (hCi : 1 ≤ Ci) :
    X + 5 / 2 * (M * (Lam * (9 * Ci * O + Sd))) + Sd
      ≤ (1 + 45 / 2 * Ci * Lam) * (X + M * O + (1 + M) * Sd) := by
  have hLam0 : (0 : ℝ) ≤ Lam := by linarith only [hLam]
  have hMO : (0 : ℝ) ≤ M * O := mul_nonneg hM hO
  have hMSd : (0 : ℝ) ≤ M * Sd := mul_nonneg hM hSd
  have hCiLam : (1 : ℝ) ≤ Ci * Lam := by
    have h := mul_le_mul hCi hLam (by norm_num) (by linarith only [hCi])
    linarith only [h]
  have hK1 : (1 : ℝ) ≤ 1 + 45 / 2 * Ci * Lam := by
    have he : 45 / 2 * Ci * Lam = 45 / 2 * (Ci * Lam) := by ring
    linarith only [hCiLam, he]
  have t1 : X ≤ (1 + 45 / 2 * Ci * Lam) * X := by
    have h := mul_le_mul_of_nonneg_right hK1 hX
    linarith only [h]
  have t2 : 5 / 2 * (M * (Lam * (9 * Ci * O))) ≤ (1 + 45 / 2 * Ci * Lam) * (M * O) := by
    have he1 : 5 / 2 * (M * (Lam * (9 * Ci * O))) = 45 / 2 * Ci * Lam * (M * O) := by ring
    have he2 : (1 + 45 / 2 * Ci * Lam) * (M * O)
        = M * O + 45 / 2 * Ci * Lam * (M * O) := by ring
    linarith only [he1, he2, hMO]
  have t3 : 5 / 2 * (M * (Lam * Sd)) ≤ (1 + 45 / 2 * Ci * Lam) * (M * Sd) := by
    have hcoef : 5 / 2 * Lam ≤ 1 + 45 / 2 * Ci * Lam := by
      have h := mul_nonneg hLam0 (by linarith only [hCi] : (0 : ℝ) ≤ 45 / 2 * Ci - 5 / 2)
      have he : Lam * (45 / 2 * Ci - 5 / 2) = 45 / 2 * Ci * Lam - 5 / 2 * Lam := by ring
      linarith only [h, he]
    have h := mul_le_mul_of_nonneg_right hcoef hMSd
    have he1 : 5 / 2 * (M * (Lam * Sd)) = 5 / 2 * Lam * (M * Sd) := by ring
    linarith only [h, he1]
  have t4 : Sd ≤ (1 + 45 / 2 * Ci * Lam) * Sd := by
    have h := mul_le_mul_of_nonneg_right hK1 hSd
    linarith only [h]
  have hexpL : X + 5 / 2 * (M * (Lam * (9 * Ci * O + Sd))) + Sd
      = X + (5 / 2 * (M * (Lam * (9 * Ci * O))) + 5 / 2 * (M * (Lam * Sd))) + Sd := by
    ring
  have hexpR : (1 + 45 / 2 * Ci * Lam) * (X + M * O + (1 + M) * Sd)
      = (1 + 45 / 2 * Ci * Lam) * X + (1 + 45 / 2 * Ci * Lam) * (M * O)
        + (1 + 45 / 2 * Ci * Lam) * Sd + (1 + 45 / 2 * Ci * Lam) * (M * Sd) := by ring
  linarith only [t1, t2, t3, t4, hexpL, hexpR]

/-- Composing a bound `q ≤ P·W` with `W ≤ K·V` and a prefactor budget `P·K ≤ R`. -/
private theorem prefactorAbsorb {q P W K V R : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hq : q ≤ P * W) (hW : W ≤ K * V) (hpref : P * K ≤ R) : q ≤ R * V := by
  have h1 : P * W ≤ P * (K * V) := mul_le_mul_of_nonneg_left hW hP
  have h2 : P * (K * V) = P * K * V := by ring
  have h3 : P * K * V ≤ R * V := mul_le_mul_of_nonneg_right hpref hV
  linarith only [hq, h1, h2, h3]

/-! ### The provider theorem -/

private theorem iterationLemmaProvider_comparisonBounds1 :
    ∀ (d : ℕ) (_ : d ≠ (0 : ℕ)) (h : ℕ) (θ : ℝ) (n m : ℤ) (U : ℤ → Set (Vec d))
      (_ : ∀ j ≤ m, U (j - (1 : ℤ)) ⊆ U j) (u : Vec d → ℝ) (_ : MemLp u (2 : ENNReal)
        (volume.restrict (U m)))
      (B : Finset ℤ) (ε δ cc : ℤ → ℝ) (gg : ℤ → Vec d) (_ : ∀ j ≤ m, IsAffineMinimizer (U j) u (cc
        j) (gg j))
      (_ :
        ∀ (j : ℤ),
          n ≤ j →
            j ≤ m →
              j ∉ B → affineExcess (U (j - (↑h : ℤ))) u ≤ θ ^ h * affineExcess (U j) u + ε j *
                slopeMagnitude (gg j) + δ j)
      (_ : (0 : ℕ) < d) (_ : (1 : ℕ) ≤ h) (_ : n ≤ m) (εt : ℤ → ℝ) (_ : ∀ (j : ℤ), n ≤ j → j ≤ m →
        εt j = ε j)
      (δt : ℤ → ℝ) (_ : ∀ (j : ℤ), n ≤ j → j ≤ m → δt j = δ j) (z : (k : ℤ) → Vec d × Vec d)
      (_ : ∀ (k : ℤ), axisCube (z k).1 ((3 : ℝ) ^ (min k m - (2 : ℤ))) ⊆ cappedWindows U m k)
      (_ : ∀ (k : ℤ), cappedWindows U m k ⊆ axisCube (z k).2 ((3 : ℝ) ^ min k m))
      (_ : ∀ (k : ℤ), MeasurableSet (cappedWindows U m k))
      (_ : ∀ (k : ℤ), cappedWindows U m k ⊆ cappedWindows U m (k + (1 : ℤ))),
      (∀ (k : ℤ), (0 : ℝ) ≤ affineExcess (cappedWindows U m k) u) ∧
        (∀ (k : ℤ), (0 : ℝ) ≤ slopeMagnitude (gg (min k m))) ∧
          (1 : ℝ) ≤ iterKappa d ∧
            (0 : ℝ) ≤ iterCstab d ∧
              (1 : ℝ) ≤ iterCi d ∧
                (0 : ℝ) ≤ iterCi d ∧
                  (∀ (k : ℤ),
                      affineExcess (cappedWindows U m k) u ≤
                        iterKappa d * affineExcess (cappedWindows U m (k + (1 : ℤ))) u) ∧
                    (∀ (k : ℤ),
                        |slopeMagnitude (gg (min k m)) - slopeMagnitude (gg (min (k - (1 : ℤ))
                          m))| ≤
                          iterCstab d *
                            (affineExcess (cappedWindows U m k) u + affineExcess (cappedWindows U
                              m (k - (1 : ℤ))) u)) ∧
                      (∀ (k : ℤ),
                          oscillationOn (cappedWindows U m k) u ≤
                              iterCi d * (affineExcess (cappedWindows U m k) u + slopeMagnitude
                                (gg (min k m))) ∧
                            affineExcess (cappedWindows U m k) u + slopeMagnitude (gg (min k m)) ≤
                              iterCi d * oscillationOn (cappedWindows U m k) u) ∧
                        (∀ (j : ℤ),
                            n ≤ j →
                              j ≤ m →
                                j ∉ B →
                                  affineExcess (cappedWindows U m (j - (↑h : ℤ))) u ≤
                                    θ ^ h * affineExcess (cappedWindows U m j) u + εt j *
                                      slopeMagnitude (gg (min j m)) +
                                      δt j) ∧
                          cappedWindows U m n = U n ∧
                            cappedWindows U m m = U m ∧
                              oscillationScaled n (U n) u ≤ oscillationOn (U n) u ∧
                                oscillationOn (U m) u ≤ (9 : ℝ) * oscillationScaled m (U m) u ∧
                                  (0 : ℝ) ≤ oscillationScaled m (U m) u ∧
                                    (1 : ℝ) ≤
                                        goodConst h (iterKappa d) (iterCstab d) * badConst
                                          (iterKappa d) (iterCstab d) ∧
                                      (0 : ℝ) ≤
                                        goodConst h (iterKappa d) (iterCstab d) * badConst
                                          (iterKappa d) (iterCstab d) := by
  intro d hd h θ n m U hnest u hu B _ _ cc gg hmin hdec hd0 _ hnmle εt hεteq δt hδteq z hqin hqout
    hmeasc hnestc
  have huc : ∀ k : ℤ, MemLp u 2 (volume.restrict (cappedWindows U m k)) :=
    fun k => memLp_restrict_of_subset (cappedWindows_subset_top hnest k) hu
  have hminc : ∀ k : ℤ,
      IsAffineMinimizer (cappedWindows U m k) u (cc (min k m)) (gg (min k m)) :=
    fun k => hmin (min k m) (min_le_right _ _)
  have hLin : ∀ k : ℤ, (0 : ℝ) < (3 : ℝ) ^ (min k m - 2) :=
    fun k => zpow_pos (by norm_num) _
  have hLout : ∀ k : ℤ, (0 : ℝ) < (3 : ℝ) ^ (min k m) :=
    fun k => zpow_pos (by norm_num) _
  have hasp : ∀ k : ℤ, (1 / 9 : ℝ) * (3 : ℝ) ^ (min k m) ≤ (3 : ℝ) ^ (min k m - 2) :=
    fun k => le_of_eq (triadic_aspect (min k m))
  have hratio : ∀ k : ℤ,
      ((volume (cappedWindows U m (k + 1))).toReal
          / (volume (cappedWindows U m k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
        ≤ iterKappa d :=
    volumeRatio_le_of_axisCubeSandwich (s := fun k => min k m)
      (fun k => by
        show min (k + 1) m ≤ min k m + 1
        omega) hqin hqout
  have hvolc : ∀ k : ℤ, 0 < (volume (cappedWindows U m k)).toReal :=
    fun k => volume_toReal_pos_of_sandwich (hLin k) (hqin k) (hqout k)
  have hintc : ∀ (k : ℤ) (a : ℝ) (b : Vec d),
      IntegrableOn (fun x => (u x - affineEval a b x) ^ 2) (cappedWindows U m k) :=
    fun k a b =>
      integrableOn_sub_affineEval_sq_of_axisCubeSandwich (hLout k) (hmeasc k) (hqout k)
        (huc k) a b
  -- the six interface slots, all discharged from the sandwich
  have hEnn : ∀ k : ℤ, (0 : ℝ) ≤ affineExcess (cappedWindows U m k) u :=
    fun k => affineExcess_nonneg _ _
  have hpnn : ∀ k : ℤ, (0 : ℝ) ≤ slopeMagnitude (gg (min k m)) :=
    fun k => slopeMagnitude_nonneg _
  have hκ1 : (1 : ℝ) ≤ iterKappa d := one_le_iterKappa d
  have hCs0 : (0 : ℝ) ≤ iterCstab d := iterCstab_nonneg d
  have hCi1 : (1 : ℝ) ≤ iterCi d := one_le_iterCi d
  have hCi0 : (0 : ℝ) ≤ iterCi d := by linarith only [hCi1]
  have hmonoE : ∀ k : ℤ, affineExcess (cappedWindows U m k) u
      ≤ iterKappa d * affineExcess (cappedWindows U m (k + 1)) u :=
    affineExcess_quasiMonotone_of_nested (cappedWindows U m) u hnestc hvolc hintc hratio
  have hstabE : ∀ k : ℤ,
      |slopeMagnitude (gg (min k m)) - slopeMagnitude (gg (min (k - 1) m))|
        ≤ iterCstab d * (affineExcess (cappedWindows U m k) u
          + affineExcess (cappedWindows U m (k - 1)) u) :=
    slopeStability_of_axisCubeSandwich (cappedWindows U m) u (fun k => cc (min k m))
      (fun k => gg (min k m)) (θ := (1 / 9 : ℝ)) (κ := iterKappa d) hd0 hLin hLout
      (by norm_num) hasp hqin hqout hmeasc hnestc huc hminc hratio
  have hend : ∀ k : ℤ,
      oscillationOn (cappedWindows U m k) u
          ≤ iterCi d * (affineExcess (cappedWindows U m k) u
            + slopeMagnitude (gg (min k m)))
        ∧ affineExcess (cappedWindows U m k) u + slopeMagnitude (gg (min k m))
          ≤ iterCi d * oscillationOn (cappedWindows U m k) u :=
    fun k => endpoint_comparisons_of_axisCubeSandwich (θ := (1 / 9 : ℝ)) hd0 (hLin k)
      (hLout k) (by norm_num) (hasp k) (hmeasc k) (hqin k) (hqout k) (huc k) (hminc k)
  -- the decay hypothesis on the capped data
  have hdecayt : ∀ j : ℤ, n ≤ j → j ≤ m → j ∉ B →
      affineExcess (cappedWindows U m (j - (h : ℤ))) u
        ≤ θ ^ h * affineExcess (cappedWindows U m j) u
          + εt j * slopeMagnitude (gg (min j m)) + δt j := by
    intro j hj1 hj2 hjB
    have hjhm : min (j - (h : ℤ)) m = j - (h : ℤ) := by
      have hnn : (0 : ℤ) ≤ (h : ℤ) := Int.natCast_nonneg h
      exact min_eq_left (by omega)
    simp only [cappedWindows]
    rw [min_eq_left hj2, hjhm, hεteq j hj1 hj2, hδteq j hj1 hj2]
    exact hdec j hj1 hj2 hjB
  -- the window identifications at the two endpoints
  have hUn : cappedWindows U m n = U n := cappedWindows_of_le hnmle
  have hUm : cappedWindows U m m = U m := cappedWindows_of_le le_rfl
  have hqinN : axisCube (z n).1 ((3 : ℝ) ^ (n - 2)) ⊆ U n := by
    have hx := hqin n
    rw [min_eq_left hnmle, hUn] at hx
    exact hx
  have hqoutN : U n ⊆ axisCube (z n).2 ((3 : ℝ) ^ n) := by
    have hx := hqout n
    rw [min_eq_left hnmle, hUn] at hx
    exact hx
  have hqinM : axisCube (z m).1 ((3 : ℝ) ^ (m - 2)) ⊆ U m := by
    have hx := hqin m
    rw [min_self, hUm] at hx
    exact hx
  have hqoutM : U m ⊆ axisCube (z m).2 ((3 : ℝ) ^ m) := by
    have hx := hqout m
    rw [min_self, hUm] at hx
    exact hx
  have hlowN : oscillationScaled n (U n) u ≤ oscillationOn (U n) u :=
    oscillationScaled_le_oscillationOn_of_axisCubeSandwich hd hqinN hqoutN u
  have hhighM : oscillationOn (U m) u ≤ 9 * oscillationScaled m (U m) u :=
    oscillationOn_le_oscillationScaled_of_axisCubeSandwich hd hqinM hqoutM u
  have hO0 : (0 : ℝ) ≤ oscillationScaled m (U m) u := oscillationScaled_nonneg _ _ _
  -- the two constants of the run assembly
  have hgcbc1 : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by
    have hg := one_le_goodConst h hκ1 hCs0
    have hb := one_le_badConst hκ1 hCs0
    have hm := mul_le_mul_of_nonneg_left hb (by linarith only [hg] :
      (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d))
    linarith only [hm, hg]
  have hgcbc0 : (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d)
      * badConst (iterKappa d) (iterCstab d) := by linarith only [hgcbc1]
  exact ⟨hEnn, hpnn, hκ1, hCs0, hCi1, hCi0, hmonoE, hstabE, hend, hdecayt, hUn, hUm, hlowN,
    hhighM, hO0, hgcbc1, hgcbc0⟩

private theorem iterationLemmaProvider_estimate1 :
    ∀ (d h : ℕ) (n m : ℤ) (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
      (B : Finset ℤ) (gg : ℤ → Vec d) (εt : ℤ → ℝ) (_ : ∀ (k : ℤ), (0 : ℝ) ≤ εt k) (δt : ℤ → ℝ)
      (_ : ∀ (k : ℤ), (0 : ℝ) ≤ δt k) (_ : ∀ (k : ℤ), (0 : ℝ) ≤ affineExcess (cappedWindows U m k)
        u)
      (_ : ∀ (k : ℤ), (0 : ℝ) ≤ slopeMagnitude (gg (min k m))) (_ : (0 : ℝ) ≤ iterCstab d)
      (_ : (1 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d))
      (_ : (0 : ℝ) ≤ goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d))
      (_ :
        (0 : ℝ) ≤
          (goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^ ((3 :
            ℕ) * B.card + (3 : ℕ)) *
            Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
      (_ :
        affineExcess (cappedWindows U m m) u + slopeMagnitude (gg (min m m)) ≤
          (9 : ℝ) * iterCi d * oscillationScaled m (U m) u)
      (_ :
        ∀ (k : ℤ),
          n ≤ k →
            k ≤ m →
              affineExcess (cappedWindows U m k) u + slopeMagnitude (gg (min k m)) ≤
                (goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^
                      ((3 : ℕ) * (B ∩ Finset.Icc k m).card + (3 : ℕ)) *
                    Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc k m, εt j) *
                  (affineExcess (cappedWindows U m m) u + slopeMagnitude (gg (min m m)) + ∑ j ∈
                    Finset.Icc k m, δt j))
      (j : ℤ),
      n ≤ j →
        j ≤ m →
          slopeMagnitude (gg (min j m)) ≤
            (goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^
                  ((3 : ℕ) * B.card + (3 : ℕ)) *
                Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j) *
              ((9 : ℝ) * iterCi d * oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δt j) := by
  intro d h n m U u B gg εt hεt0 δt hδt0 hEnn hpnn hCs0 hgcbc1 hgcbc0 hΛ0 hEpm hcbk j hj1 hj2
  have hk := hcbk j hj1 hj2
  have hcard : 3 * (B ∩ Finset.Icc j m).card + 3 ≤ 3 * B.card + 3 := by
    have hsub : B ∩ Finset.Icc j m ⊆ B := Finset.inter_subset_left
    have hc := Finset.card_le_card hsub
    omega
  have hpowmono : (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * (B ∩ Finset.Icc j m).card + 3)
      ≤ (goodConst h (iterKappa d) (iterCstab d)
        * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3) :=
    pow_le_pow_right₀ hgcbc1 hcard
  have hsubset : Finset.Icc j m ⊆ Finset.Icc n m := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hεsub : ∑ x ∈ Finset.Icc j m, εt x ≤ ∑ x ∈ Finset.Icc n m, εt x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun x _ _ => hεt0 x
  have hδsub : ∑ x ∈ Finset.Icc j m, δt x ≤ ∑ x ∈ Finset.Icc n m, δt x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset fun x _ _ => hδt0 x
  have hexpmono : Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc j m, εt x)
      ≤ Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc n m, εt x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hεsub (goodRate_nonneg hCs0))
  have hpref : (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d))
          ^ (3 * (B ∩ Finset.Icc j m).card + 3)
        * Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc j m, εt x)
      ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
        * Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc n m, εt x) :=
    mul_le_mul hpowmono hexpmono (le_of_lt (Real.exp_pos _)) (pow_nonneg hgcbc0 _)
  have hbase : affineExcess (cappedWindows U m m) u + slopeMagnitude (gg (min m m))
        + ∑ x ∈ Finset.Icc j m, δt x
      ≤ 9 * iterCi d * oscillationScaled m (U m) u
        + ∑ x ∈ Finset.Icc n m, δt x := by
    linarith only [hEpm, hδsub]
  have hbase0 : (0 : ℝ) ≤ affineExcess (cappedWindows U m m) u
      + slopeMagnitude (gg (min m m)) + ∑ x ∈ Finset.Icc j m, δt x := by
    have h1 := hEnn m
    have h2 := hpnn m
    have h3 : (0 : ℝ) ≤ ∑ x ∈ Finset.Icc j m, δt x :=
      Finset.sum_nonneg fun x _ => hδt0 x
    linarith only [h1, h2, h3]
  calc slopeMagnitude (gg (min j m))
      ≤ affineExcess (cappedWindows U m j) u + slopeMagnitude (gg (min j m)) := by
        linarith only [hEnn j]
    _ ≤ (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d))
            ^ (3 * (B ∩ Finset.Icc j m).card + 3)
          * Real.exp (goodRate (iterCstab d) * ∑ x ∈ Finset.Icc j m, εt x)
          * (affineExcess (cappedWindows U m m) u + slopeMagnitude (gg (min m m))
            + ∑ x ∈ Finset.Icc j m, δt x) := hk
    _ ≤ ((goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
          * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
          * (9 * iterCi d * oscillationScaled m (U m) u
            + ∑ j ∈ Finset.Icc n m, δt j) :=
        mul_le_mul hpref hbase hbase0 hΛ0

private theorem iterationLemmaProvider_estimate2 :
    ∀ (d h : ℕ) (n m : ℤ) (U : ℤ → Set (Vec d)) (u : Vec d → ℝ)
      (B : Finset ℤ) (ε δ : ℤ → ℝ) (_ : oscillationScaled n (U n) u ≤ oscillationOn (U n) u)
      (_ : oscillationOn (U m) u ≤ (9 : ℝ) * oscillationScaled m (U m) u)
      (_ :
        oscillationOn (U n) u ≤
          iterCi d ^ (2 : ℕ) *
                (goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^
                  ((3 : ℕ) * B.card + (3 : ℕ)) *
              Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j) *
            (oscillationOn (U m) u + ∑ j ∈ Finset.Icc n m, δ j))
      (_ :
        (0 : ℝ) ≤
          iterCi d ^ (2 : ℕ) *
              (goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^
                ((3 : ℕ) * B.card + (3 : ℕ)) *
            Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j))
      (_ : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, δ j)
      (_ :
        (9 : ℝ) * iterCi d ^ (2 : ℕ) *
            ((goodConst h (iterKappa d) (iterCstab d) * badConst (iterKappa d) (iterCstab d)) ^
                ((3 : ℕ) * B.card + (3 : ℕ)) *
              Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j)) ≤
          Real.exp
            (iterConst d * ((↑h : ℝ) + (1 : ℝ)) * ((↑B.card : ℝ) + (1 : ℝ)) + iterConst d * ∑ j ∈
              Finset.Icc n m, ε j))
      (_ : (0 : ℝ) ≤ oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j),
      oscillationScaled n (U n) u ≤
        Real.exp
            (iterConst d * ((↑h : ℝ) + (1 : ℝ)) * ((↑B.card : ℝ) + (1 : ℝ)) + iterConst d * ∑ j ∈
              Finset.Icc n m, ε j) *
          (oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j) := by
  intro d h n m U u B ε δ hlowN hhighM hcbi hQ0 hSdε0 hb1 hV0
  calc oscillationScaled n (U n) u ≤ oscillationOn (U n) u := hlowN
    _ ≤ iterCi d ^ 2
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
          * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j)
          * (oscillationOn (U m) u + ∑ j ∈ Finset.Icc n m, δ j) := hcbi
    _ ≤ iterCi d ^ 2
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
          * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j)
          * (9 * oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j) :=
        mul_le_mul_of_nonneg_left (by linarith only [hhighM]) hQ0
    _ ≤ 9 * (iterCi d ^ 2
          * (goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
          * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j))
          * (oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j) :=
        oscSlotCollapse hQ0 hSdε0
    _ = 9 * iterCi d ^ 2
          * ((goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
            * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j))
          * (oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j) := by ring
    _ ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((B.card : ℝ) + 1)
          + iterConst d * ∑ j ∈ Finset.Icc n m, ε j)
          * (oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j) :=
        mul_le_mul_of_nonneg_right hb1 hV0

private theorem iterationLemmaProvider_comparisonBounds2 :
    ∀ (d : ℕ) (_ : d ≠ (0 : ℕ)) (h : ℕ) (θ : ℝ) (_ : θ ∈ Set.Ioo (0 : ℝ) (1 : ℝ))
      (_ : θ ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5 : ℝ)) (n m : ℤ) (_ : n < m) (U : ℤ → Set (Vec d))
      (_ :
        ∀ j ≤ m,
          ∃ (x : Vec d) (y : Vec d),
            (fun (v : Vec d) => x + v) '' openCubeSet (originCube d (j - (2 : ℤ))) ⊆ U j ∧
              U j ⊆ (fun (v : Vec d) => y + v) '' openCubeSet (originCube d j))
      (ε δ : ℤ → ℝ) (_ : ∀ (j : ℤ), n ≤ j → j ≤ m → (0 : ℝ) ≤ ε j) (_ : ∀ (j : ℤ), n ≤ j → j ≤ m →
        (0 : ℝ) ≤ δ j),
      ∃ (_ : (0 : ℕ) < d) (_ : (0 : ℝ) < θ) (_ : θ ≤ (1 : ℝ)) (_ : θ ^ h < (3 / 5 : ℝ)) (_ : (1 :
        ℕ) ≤ h) (_ : n ≤ m) (εt :
        ℤ → ℝ) (_ : ∀ (k : ℤ), (0 : ℝ) ≤ εt k) (_ : ∀ (j : ℤ), n ≤ j → j ≤ m → εt j = ε j) (δt : ℤ
          → ℝ) (_ :
        ∀ (k : ℤ), (0 : ℝ) ≤ δt k) (_ : ∀ (j : ℤ), n ≤ j → j ≤ m → δt j = δ j) (_ :
        ∑ j ∈ Finset.Icc n m, εt j = ∑ j ∈ Finset.Icc n m, ε j) (_ : ∑ j ∈ Finset.Icc n m, δt j =
          ∑ j ∈ Finset.Icc n m, δ j)
        (_ : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, εt j) (_ : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, δt j),
        ∀ (k : ℤ),
          ∃ (z : Vec d × Vec d),
            axisCube z.1 ((3 : ℝ) ^ (min k m - (2 : ℤ))) ⊆ cappedWindows U m k ∧
              cappedWindows U m k ⊆ axisCube z.2 ((3 : ℝ) ^ min k m) := by
  classical
  intro d hd h θ hθ01 hθh n m hnm U hsand ε δ hε hδ
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  have hθ0 : (0 : ℝ) < θ := hθ01.1
  have hθ1 : θ ≤ 1 := le_of_lt hθ01.2
  have hθh35 : θ ^ h < 3 / 5 := hθh.2
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0, pow_zero] at hθh35
      exact absurd hθh35 (by norm_num)
    · exact hpos
  have hnmle : n ≤ m := le_of_lt hnm
  -- the engine's sign slots are stated for all `k : ℤ`: truncate the error data
  obtain ⟨εt, hεt0, hεteq⟩ : ∃ f : ℤ → ℝ, (∀ k : ℤ, 0 ≤ f k)
      ∧ ∀ j : ℤ, n ≤ j → j ≤ m → f j = ε j := by
    refine ⟨fun j => if n ≤ j ∧ j ≤ m then ε j else 0, fun k => ?_, fun j hj1 hj2 => ?_⟩
    · change (0 : ℝ) ≤ if n ≤ k ∧ k ≤ m then ε k else 0
      split_ifs with hcase
      · exact hε k hcase.1 hcase.2
      · exact le_rfl
    · change (if n ≤ j ∧ j ≤ m then ε j else 0) = ε j
      rw [ite_eq_left (⟨hj1, hj2⟩ : n ≤ j ∧ j ≤ m)]
  obtain ⟨δt, hδt0, hδteq⟩ : ∃ f : ℤ → ℝ, (∀ k : ℤ, 0 ≤ f k)
      ∧ ∀ j : ℤ, n ≤ j → j ≤ m → f j = δ j := by
    refine ⟨fun j => if n ≤ j ∧ j ≤ m then δ j else 0, fun k => ?_, fun j hj1 hj2 => ?_⟩
    · change (0 : ℝ) ≤ if n ≤ k ∧ k ≤ m then δ k else 0
      split_ifs with hcase
      · exact hδ k hcase.1 hcase.2
      · exact le_rfl
    · change (if n ≤ j ∧ j ≤ m then δ j else 0) = δ j
      rw [ite_eq_left (⟨hj1, hj2⟩ : n ≤ j ∧ j ≤ m)]
  have hSe : ∑ j ∈ Finset.Icc n m, εt j = ∑ j ∈ Finset.Icc n m, ε j :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact hεteq j hj.1 hj.2
  have hSd : ∑ j ∈ Finset.Icc n m, δt j = ∑ j ∈ Finset.Icc n m, δ j :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.mem_Icc] at hj
      exact hδteq j hj.1 hj.2
  have hSe0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, εt j :=
    Finset.sum_nonneg fun j _ => hεt0 j
  have hSd0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, δt j :=
    Finset.sum_nonneg fun j _ => hδt0 j
  -- the capped window family, with its axis-cube sandwich at every scale
  have hsandc : ∀ k : ℤ, ∃ z : Vec d × Vec d,
      axisCube z.1 ((3 : ℝ) ^ (min k m - 2)) ⊆ cappedWindows U m k ∧
        cappedWindows U m k ⊆ axisCube z.2 ((3 : ℝ) ^ (min k m)) := by
    intro k
    obtain ⟨x, y, hin, hout⟩ := hsand (min k m) (min_le_right _ _)
    obtain ⟨zin, zout, h1, h2⟩ := axisCube_sandwich_of_translateSandwich hin hout
    exact ⟨(zin, zout), h1, h2⟩
  exact ⟨hd0, hθ0, hθ1, hθh35, hh, hnmle, εt, hεt0, hεteq, δt, hδt0, hδteq, hSe, hSd, hSe0, hSd0,
    hsandc⟩

/-- **The provider for `Algsuperdiff.Frozen.Section4.iteration_lemma`.**

The frozen theorem's statement verbatim, at the explicit witness `C = iterConst
d`. -/
theorem iteration_lemma_provider
    (d : ℕ) (hd : d ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℕ) (θ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → θ ^ h ∈ Set.Ioo (0 : ℝ) (3 / 5) →
        ∀ n m : ℤ, n < m →
          ∀ U : ℤ → Set (HCPolySupport.Vec d),
            (∀ j : ℤ, j ≤ m → MeasurableSet (U j)) →
            (∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) →
            (∀ j : ℤ, j ≤ m →
                ∃ x y : HCPolySupport.Vec d,
                  (fun v => x + v) ''
                      HCPolySupport.openCubeSet
                        (HCPolySupport.originCube d (j - 2)) ⊆ U j ∧
                    U j ⊆
                      (fun v => y + v) ''
                        HCPolySupport.openCubeSet (HCPolySupport.originCube d j)) →
            ∀ u : HCPolySupport.Vec d → ℝ,
              MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict (U m)) →
              ∀ B : Finset ℤ, B ⊆ Finset.Icc n m →
                ∀ ε δ : ℤ → ℝ,
                  (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ ε j) →
                  (∀ j : ℤ, n ≤ j → j ≤ m → 0 ≤ δ j) →
                  ∀ (c : ℤ → ℝ) (g : ℤ → HCPolySupport.Vec d),
                    (∀ j : ℤ, j ≤ m →
                        Algsuperdiff.Section4.Support.IsAffineMinimizer
                          (U j) u (c j) (g j)) →
                    (∀ j : ℤ, n ≤ j → j ≤ m → j ∉ B →
                        Algsuperdiff.Section4.Support.affineExcess
                            (U (j - (h : ℤ))) u ≤
                          θ ^ h *
                              Algsuperdiff.Section4.Support.affineExcess (U j) u +
                            ε j *
                              Algsuperdiff.Section4.Support.slopeMagnitude (g j) +
                            δ j) →
                    ((3 : ℝ) ^ (-n) *
                        Algsuperdiff.Section4.Support.normalizedL2On (U n)
                          (fun x => u x - HCPolySupport.volumeAverage (U n) u) ≤
                      Real.exp
                          (C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) +
                            C * ∑ j ∈ Finset.Icc n m, ε j) *
                        ((3 : ℝ) ^ (-m) *
                            Algsuperdiff.Section4.Support.normalizedL2On (U m)
                              (fun x => u x - HCPolySupport.volumeAverage (U m) u) +
                          ∑ j ∈ Finset.Icc n m, δ j)) ∧
                      ∀ M : ℝ, (∀ j : ℤ, n ≤ j → j ≤ m → ε j ≤ M) →
                          Algsuperdiff.Section4.Support.affineExcess (U n) u ≤
                            Real.rpow θ
                                  (-(C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1))) *
                                Real.exp
                                  (C * ((h : ℝ) + 1) * ((B.card : ℝ) + 1) +
                                    C * ∑ j ∈ Finset.Icc n m, ε j) *
                              (θ ^ (m - n) *
                                  Algsuperdiff.Section4.Support.affineExcess (U m) u +
                                M *
                                    ((3 : ℝ) ^ (-m) *
                                      Algsuperdiff.Section4.Support.normalizedL2On (U m)
                                        (fun x => u x - HCPolySupport.volumeAverage (U m) u)) +
                                (1 + M) * ∑ j ∈ Finset.Icc n m, δ j)
    := by
  classical
  refine ⟨iterConst d, iterConst_pos d, ?_⟩
  intro h θ hθ01 hθh n m hnm U hmeas hnest hsand u hu B hB ε δ hε hδ cc gg hmin hdec
  obtain ⟨hd0, hθ0, hθ1, hθh35, hh, hnmle, εt, hεt0, hεteq, δt, hδt0, hδteq, hSe, hSd, hSe0, hSd0,
    hsandc⟩ :=
    @iterationLemmaProvider_comparisonBounds2 (d) (hd) (h) (θ) (hθ01) (hθh) (n) (m) (hnm) (U)
      (hsand) (ε) (δ) (hε) (hδ)
  choose z hqin hqout using hsandc
  have hmeasc : ∀ k : ℤ, MeasurableSet (cappedWindows U m k) :=
    fun k => hmeas (min k m) (min_le_right _ _)
  have hnestc : ∀ k : ℤ, cappedWindows U m k ⊆ cappedWindows U m (k + 1) :=
    cappedWindows_nest hnest
  obtain ⟨hEnn, hpnn, hκ1, hCs0, hCi1, hCi0, hmonoE, hstabE, hend, hdecayt, hUn, hUm, hlowN,
    hhighM, hO0, hgcbc1, hgcbc0⟩ :=
    @iterationLemmaProvider_comparisonBounds1 (d) (hd) (h) (θ) (n) (m) (U) (hnest) (u) (hu) (B)
      (ε) (δ) (cc) (gg) (hmin) (hdec) (hd0) (hh) (hnmle) (εt) (hεteq) (δt) (hδteq) (z) (hqin)
        (hqout) (hmeasc) (hnestc)
  refine ⟨?_, ?_⟩
  · -- conclusion (i): the engine plus the normalizer bridges and the prefactor budget
    have hcbi : oscillationOn (cappedWindows U m n) u
        ≤ iterCi d ^ 2
            * (goodConst h (iterKappa d) (iterCstab d)
              * badConst (iterKappa d) (iterCstab d))
              ^ (3 * (B ∩ Finset.Icc n m).card + 3)
            * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j)
            * (oscillationOn (cappedWindows U m m) u + ∑ j ∈ Finset.Icc n m, δt j) :=
      iterationSlopeBound (E := fun k => affineExcess (cappedWindows U m k) u)
        (p := fun k => slopeMagnitude (gg (min k m))) (ε := εt) (δ := δt) (θ := θ)
        (h := h) (κ := iterKappa d) (Cstab := iterCstab d) hθ0 hθh35 hEnn hpnn hεt0
        hδt0 hκ1 hCs0 hmonoE hstabE hnmle B hdecayt
        (fun k => oscillationOn (cappedWindows U m k) u) hCi1 (hend n).1 (hend m).2
    rw [hUn, hUm, hSe, hSd, Finset.inter_eq_left.2 hB] at hcbi
    have hQ0 : (0 : ℝ) ≤ iterCi d ^ 2
        * (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
        * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, ε j) := by
      have h1 : (0 : ℝ) ≤ iterCi d ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3) :=
        pow_nonneg hgcbc0 _
      exact mul_nonneg (mul_nonneg h1 h2) (le_of_lt (Real.exp_pos _))
    have hSdε0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, δ j := by
      rw [← hSd]
      exact hSd0
    have hSeε0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Icc n m, ε j := by
      rw [← hSe]
      exact hSe0
    have hb1 := iterPrefactorOne_le d hh B.card (Se := ∑ j ∈ Finset.Icc n m, ε j) hSeε0
    have hV0 : (0 : ℝ) ≤ oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j := by
      linarith only [hO0, hSdε0]
    have hgoal : oscillationScaled n (U n) u
        ≤ Real.exp (iterConst d * ((h : ℝ) + 1) * ((B.card : ℝ) + 1)
            + iterConst d * ∑ j ∈ Finset.Icc n m, ε j)
          * (oscillationScaled m (U m) u + ∑ j ∈ Finset.Icc n m, δ j)  :=
            @iterationLemmaProvider_estimate2 (d) (h) (n) (m) (U) (u) (B) (ε) (δ) (hlowN) (hhighM)
              (hcbi) (hQ0) (hSdε0) (hb1) (hV0)
    exact hgoal
  · -- conclusion (ii): the weighted assembly at the error scale `M · Λ · (9 Ci osc_m + ∑δ)`
    intro M hMle
    have hM0 : (0 : ℝ) ≤ M := le_trans (hε n le_rfl hnmle) (hMle n le_rfl hnmle)
    have hΛ1 : (1 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
        * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j) := by
      have h1 : (1 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3) :=
        one_le_pow₀ hgcbc1
      have h2 : (1 : ℝ) ≤ Real.exp (goodRate (iterCstab d)
          * ∑ j ∈ Finset.Icc n m, εt j) := by
        rw [Real.one_le_exp_iff]
        exact mul_nonneg (goodRate_nonneg hCs0) hSe0
      have hm := mul_le_mul h1 h2 (by norm_num) (by linarith only [h1])
      linarith only [hm]
    have hΛ0 : (0 : ℝ) ≤ (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
        * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j) := by
      linarith only [hΛ1]
    have hTop0 : (0 : ℝ) ≤ 9 * iterCi d * oscillationScaled m (U m) u
        + ∑ j ∈ Finset.Icc n m, δt j := by
      have h1 : (0 : ℝ) ≤ 9 * iterCi d * oscillationScaled m (U m) u :=
        mul_nonneg (by linarith only [hCi0]) hO0
      linarith only [h1, hSd0]
    -- the top-scale endpoint bound feeding the error scale
    have hEpm : affineExcess (cappedWindows U m m) u + slopeMagnitude (gg (min m m))
        ≤ 9 * iterCi d * oscillationScaled m (U m) u := by
      have h1 := (hend m).2
      have h2 : oscillationOn (cappedWindows U m m) u
          ≤ 9 * oscillationScaled m (U m) u := by
        rw [hUm]
        exact hhighM
      have h3 := mul_le_mul_of_nonneg_left h2 hCi0
      have h4 : iterCi d * (9 * oscillationScaled m (U m) u)
          = 9 * iterCi d * oscillationScaled m (U m) u := by ring
      linarith only [h1, h3, h4]
    -- the uniform slope bound on `[n,m]`, from `e.combined.bound`
    have hcbk := combinedBound (E := fun k => affineExcess (cappedWindows U m k) u)
      (p := fun k => slopeMagnitude (gg (min k m))) (ε := εt) (δ := δt) (θ := θ) (h := h)
      (κ := iterKappa d) (Cstab := iterCstab d) hθ0 hθh35 hEnn hpnn hεt0 hδt0 hκ1 hCs0
      hmonoE hstabE B hdecayt
    have hpQ : ∀ j : ℤ, n ≤ j → j ≤ m →
        slopeMagnitude (gg (min j m))
          ≤ ((goodConst h (iterKappa d) (iterCstab d)
                * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
              * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
            * (9 * iterCi d * oscillationScaled m (U m) u
              + ∑ j ∈ Finset.Icc n m, δt j)  := @iterationLemmaProvider_estimate1 (d) (h) (n) (m)
                (U) (u) (B) (gg) (εt) (hεt0) (δt) (hδt0) (hEnn) (hpnn) (hCs0) (hgcbc1) (hgcbc0)
                  (hΛ0) (hEpm) (hcbk)
    -- the error scale, and the weighted assembly
    have hwM : ∀ j : ℤ, n ≤ j → j ≤ m →
        εt j * slopeMagnitude (gg (min j m))
          ≤ M * (((goodConst h (iterKappa d) (iterCstab d)
                * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
              * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
            * (9 * iterCi d * oscillationScaled m (U m) u
              + ∑ j ∈ Finset.Icc n m, δt j)) := by
      intro j hj1 hj2
      have h1 : εt j ≤ M := by
        rw [hεteq j hj1 hj2]
        exact hMle j hj1 hj2
      exact mul_le_mul h1 (hpQ j hj1 hj2) (hpnn j) hM0
    have hMp0 : (0 : ℝ) ≤ M * (((goodConst h (iterKappa d) (iterCstab d)
            * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
          * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
        * (9 * iterCi d * oscillationScaled m (U m) u
          + ∑ j ∈ Finset.Icc n m, δt j)) :=
      mul_nonneg hM0 (mul_nonneg hΛ0 hTop0)
    have hasm : affineExcess (cappedWindows U m n) u
        ≤ (2 * (iterKappa d * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Finset.Icc n m).card + 1)
          * (θ ^ (m - n) * affineExcess (cappedWindows U m m) u
            + 5 / 2 * (M * (((goodConst h (iterKappa d) (iterCstab d)
                  * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
                * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
              * (9 * iterCi d * oscillationScaled m (U m) u
                + ∑ j ∈ Finset.Icc n m, δt j)))
            + ∑ j ∈ Finset.Icc n m, δt j) :=
      weightedAssemble (E := fun k => affineExcess (cappedWindows U m k) u)
        (δ := δt) (w := fun j => εt j * slopeMagnitude (gg (min j m))) (θ := θ) (h := h)
        (κ := iterKappa d) hθ0 hθ1 hθh35 hEnn hδt0 hMp0 hκ1 hmonoE B hwM hdecayt n le_rfl
        hnmle
    rw [hUn, hUm, Finset.inter_eq_left.2 hB] at hasm
    -- the three slots, then the prefactor budget
    have hX0 : (0 : ℝ) ≤ θ ^ (m - n) * affineExcess (U m) u :=
      mul_nonneg (le_of_lt (zpow_pos hθ0 _)) (affineExcess_nonneg _ _)
    have hslot := slotCollapse (X := θ ^ (m - n) * affineExcess (U m) u)
      (O := oscillationScaled m (U m) u) (Sd := ∑ j ∈ Finset.Icc n m, δt j)
      (Lam := (goodConst h (iterKappa d) (iterCstab d)
          * badConst (iterKappa d) (iterCstab d)) ^ (3 * B.card + 3)
        * Real.exp (goodRate (iterCstab d) * ∑ j ∈ Finset.Icc n m, εt j))
      (Ci := iterCi d) (M := M) hX0 hO0 hSd0 hM0 hΛ1 hCi1
    have hpref2 := iterPrefactorTwo_le d hh B.card hθ0 hθ1 hSe0
    have hP0 : (0 : ℝ) ≤ (2 * (iterKappa d * θ⁻¹) ^ (h + 2)) ^ (B.card + 1) := by
      have hinv : (1 : ℝ) ≤ θ⁻¹ := one_le_inv_of_le_one hθ0 hθ1
      have hb : (0 : ℝ) ≤ 2 * (iterKappa d * θ⁻¹) ^ (h + 2) := by
        have h1 : (1 : ℝ) ≤ (iterKappa d * θ⁻¹) ^ (h + 2) :=
          one_le_pow₀ (one_le_mul_inv hκ1 hθ0 hθ1)
        linarith only [h1]
      exact pow_nonneg hb _
    have hV0 : (0 : ℝ) ≤ θ ^ (m - n) * affineExcess (U m) u
        + M * oscillationScaled m (U m) u
        + (1 + M) * ∑ j ∈ Finset.Icc n m, δt j := by
      have h1 : (0 : ℝ) ≤ M * oscillationScaled m (U m) u := mul_nonneg hM0 hO0
      have h2 : (0 : ℝ) ≤ (1 + M) * ∑ j ∈ Finset.Icc n m, δt j :=
        mul_nonneg (by linarith only [hM0]) hSd0
      linarith only [hX0, h1, h2]
    have hfinal := prefactorAbsorb hP0 hV0 hasm hslot hpref2
    rw [hSe, hSd] at hfinal
    exact hfinal

end

end Algsuperdiff.Section4.Provider.ExcessDecay
