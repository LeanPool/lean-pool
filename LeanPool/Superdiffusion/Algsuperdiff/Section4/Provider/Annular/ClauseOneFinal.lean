/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseTwo
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.FinalStitch

/-!
# ClauseOneFinal

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The clause-(i) endpoint with `huglyf` stitched in

The clause-(i) endpoint at the honest event reduces to the four slots
`hpref`, `hpret`, `huglyf`, `huglyt` at
`𝒢₀(m) ∩ 𝒢₁(m; s, √c⋆ γ^{−1/2})`.  `FinalStitch` produces the `huglyf` slot from
the lattice chain, at the annulus family `annularResponseMax`.  This module
runs the composition, so that the endpoint's remaining inputs are

* `hpref`, `hpret`, `huglyt` — three hypotheses left as binders, unchanged;
  **and**
* `hlam`, `hsignlow` — the two obligations `FinalStitch` does not discharge (at
  the relaxed constant `¼`; see `FinalStitch` and `SigmaBarBudget`).
  `SignLowDischarge` removes `hsignlow` from this list.

Three differences from the un-stitched composite, all forced by the
producer:

1. `K_tail = 2` and `gradNf = 2 · annularGradBlock` (so `K_gn = 162`).  The
   lattice chain's fourth slot is the gauge of the *whole* increment `k_L −
   k_{n−2}`, and splitting it at `m` costs `(X+Y)² ≤ 2X² + 2Y²`; no choice of
   `K_tail` makes the coefficient of `annularGradBlock` equal to `1`.  The
   output constant is unaffected: `clauseOneOutConstant C₁ C_shom` still
   dominates `2 C_leg (4608 K_l2 + 576 K_gn)` because `C_shom ≥ 6`.
2. `Jannf` is *pinned* to `annularResponseMax`, so `hpref` becomes a comparison
   of `jLegField` with a family of the same shape (a lattice maximum of
   `scalarResponseMax`).
3. The `(2,2)` slot is bridged from the literal atom to the measurable
   observable by `annularErrorAtomMax_ae_le_annularErrorLatticeMax`, one a.e.
   step at the display level — which is where the display already lives.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Frozen.Section24
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the atom-to-observable bridge for the `(2,2)` slot -/

/-- **The reconciliation.**  The annulus maximum of the *literal* `(2,2)` error
atom is almost surely below the annulus maximum of the measurable observable —
indeed the two agree a.s.  The null set is the representative-choice set of
the `𝒢₂` lane, taken over the countable family of scales and lattice indices. -/
theorem annularErrorAtomMax_ae_le_annularErrorLatticeMax [NeZero d] (M : ABKModel d)
    (s : {s : ℝ // 0 < s}) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ j n : ℤ, n ≤ j - 1 →
        annularErrorAtomMax M (s : ℝ) omega j n
          ≤ annularErrorLatticeMax M s omega j n := by
  classical
  have hpt : ∀ p : ℤ × (Fin d → ℤ),
      ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        Support.annularErrorAtom M p.1 (s : ℝ)
            (Cutoff.translateCutoffSample
              (Support.triadicLatticePoint p.1 p.2) omega)
          = Support.annularErrorObservable M p.1 s
            (Cutoff.translateCutoffSample
              (Support.triadicLatticePoint p.1 p.2) omega) := by
    intro p
    exact (GoodEvents.measurePreserving_translateCutoffSample M
        (Support.triadicLatticePoint p.1 p.2)).quasiMeasurePreserving.ae_eq_comp
      (Support.annularErrorAtom_ae_eq_annularErrorObservable M p.1 s)
  rw [← MeasureTheory.ae_all_iff] at hpt
  filter_upwards [hpt] with omega hom
  intro j n hnj
  rw [annularErrorAtomMax]
  refine Proportion.fmax_le (annularErrorLatticeMax_nonneg M s omega j n) ?_
  intro v hv
  have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
    (Proportion.mem_latticeAnnulusFinset_iff (by omega)).mp hv
  rw [hom (n, v)]
  exact le_annularErrorLatticeMax M s omega (by omega : n ≤ j) hvset

/-! ## Part B -- the summability of the doubled gradient family -/

/-- The `hsumG` binder at the doubled head-block gradient family. -/
theorem summable_annFam_two_annularGradBlock_of_eventG1 (M : ABKModel d) (m : ℤ)
    {s T : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hT : 0 ≤ T)
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T) :
    Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * (2 * annularGradBlock M m omega j n))) := by
  classical
  have hbase := (summable_annFam_annularGradBlock_of_eventG1 M m hs0 hs1 hT
    homega).mul_left 2
  refine hbase.congr fun p => ?_
  show (2 : ℝ) * annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * annularGradBlock M m omega j n) p
    = annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
      * (2 * annularGradBlock M m omega j n)) p
  unfold annFam
  split_ifs with h
  · ring
  · ring

/-! ## Part C -- the clause-(i) composite at the lattice-chain pinning -/

/-- **The clause-(i) composite with `Jannf` pinned and `K_tail = 2`.**  This is
the honest-event clause-(i) composite re-run at the pinning the lattice chain
produces: `gradNf = 2 · annularGradBlock`, `K_gn = 162`,
`K_tail = 2`, `Jannf = annularResponseMax`.  The output constant is the same
`clauseOneOutConstant`. -/
theorem clauseOne_bound_final [NeZero d] (M : ABKModel d) (L m : ℤ)
    (s : {s : ℝ // 0 < s}) (omega : Cutoff.CutoffSample d)
    (hs1 : (s : ℝ) ≤ 1) (hsg : 8 * M.gamma ≤ (s : ℝ))
    (hcstar4 : Disorder.cstar M ^ 4 ≤ 6) (hlog : 1 ≤ |Real.log M.gamma|)
    (hG1 : omega ∈ Support.eventG1 M m (s : ℝ)
      (Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹))
    (hsumE : Summable (annFam m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
      * annularErrorLatticeMax M s omega j n)))
    {Cshom : ℝ} (hCshom : 6 ≤ Cshom)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      ((Annealed.sigmaBar M m : ℝ) * ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2
        ≤ (Cshom * M.gamma * ((m - n : ℤ) : ℝ)
            + Cshom * (2 * M.gamma
              + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2
          * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)))
    {Jannt : ℤ → ℤ → ℝ} {C₁ C : ℝ} (hC₁ : 0 ≤ C₁) (hC0 : 0 ≤ C)
    (hJannt0 : ∀ j n, 0 ≤ Jannt j n)
    (hpref : IsAnnularDecompPre (s : ℝ) m (jLegField M L m omega)
      (annularResponseMax M L m omega) C₁)
    (hpret : IsAnnularDecompPre (s : ℝ) m (jLegTranspose M L m omega) Jannt C₁)
    (huglyf : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (annularResponseMax M L m omega j n)
        (annularErrorLatticeMax M s omega j n)
        (((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
        (annularL2Block M m omega j n)
        (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
        (gradTailSq M m omega) (Disorder.cstar M) M.gamma
        ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C)
    (huglyt : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jannt j n)
        (annularErrorLatticeMax M s omega j n)
        (((Annealed.sigmaBar M m : ℝ) *
          ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
        (annularL2Block M m omega j n)
        (2 * annularGradBlock M m omega j n + 2 * gradTailSq M m omega)
        (gradTailSq M m omega) (Disorder.cstar M) M.gamma
        ((3 : ℝ) ^ ((s : ℝ) * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ (((s : ℝ) + M.gamma) * ((m - n : ℤ) : ℝ))) C) :
    IsClauseOneBound (Support.fluxCorrectedError M L m (s : ℝ) omega ^ 2)
      (annDouble m (fun j n => (3 : ℝ) ^ (-((s : ℝ) * ((m - n : ℤ) : ℝ)))
        * annularErrorLatticeMax M s omega j n))
      (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
      (∑' v : ℕ, (3 : ℝ) ^ (-((s : ℝ) / 2) * (v : ℝ))
        * shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
      (s : ℝ) (Disorder.cstar M) M.gamma
      (clauseOneOutConstant C₁ C 2 Cshom) := by
  have hgam0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hT0 : (0 : ℝ) ≤ Real.sqrt (Disorder.cstar M) * (Real.sqrt M.gamma)⁻¹ :=
    (annularEventAmplitude_pos M).le
  have hCshom0 : (0 : ℝ) ≤ Cshom := by linarith only [hCshom]
  have ha0 : (0 : ℝ) ≤ Cshom * M.gamma := mul_nonneg hCshom0 hgam0.le
  have hB0 : (0 : ℝ) ≤ Cshom * (2 * M.gamma
      + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2)) := by
    have h1 : (0 : ℝ) ≤ 2 * M.gamma := by linarith only [hgam0]
    have h2 : (0 : ℝ) ≤ (Disorder.cstar M ^ 2)⁻¹
        * (M.gamma * |Real.log M.gamma| ^ 2) :=
      mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (mul_nonneg hgam0.le (sq_nonneg _))
    exact mul_nonneg hCshom0 (by linarith only [h1, h2])
  -- the constant bookkeeping at `Cbf = 1`, `Kl2 = 1`, `Kgn = 162`, `Ktail = 2`
  have hCleg0 : (0 : ℝ) ≤ clauseOneLegConstant C₁ C 2 :=
    clauseOneLegConstant_nonneg hC₁ hC0 (by norm_num)
  have hCleg2 : (0 : ℝ) ≤ 2 * clauseOneLegConstant C₁ C 2 := by
    linarith only [hCleg0]
  have hCs2 : (36 : ℝ) ≤ Cshom ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6) hCshom 2
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ Cshom ^ 2 := h
  have hbig : (252000 : ℝ) ≤ 7000 * Cshom ^ 2 := by linarith only [hCs2]
  have hCleg : 24 * 1 * C₁ * ((1 + 2) * C) ≤ clauseOneLegConstant C₁ C 2 := by
    refine le_of_eq ?_
    unfold clauseOneLegConstant
    ring
  have hCout1 : 2 * clauseOneLegConstant C₁ C 2
      ≤ clauseOneOutConstant C₁ C 2 Cshom := by
    unfold clauseOneOutConstant
    calc 2 * clauseOneLegConstant C₁ C 2
        = 2 * clauseOneLegConstant C₁ C 2 * 1 := (mul_one _).symm
      _ ≤ 2 * clauseOneLegConstant C₁ C 2 * (7000 * Cshom ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith only [hbig]) hCleg2
  have hCout2 : 2 * clauseOneLegConstant C₁ C 2 * (7000 * Cshom ^ 2)
      ≤ clauseOneOutConstant C₁ C 2 Cshom := le_of_eq rfl
  have hCout3 : 2 * clauseOneLegConstant C₁ C 2 * (4608 * 1 + 576 * 162)
      ≤ clauseOneOutConstant C₁ C 2 Cshom := by
    unfold clauseOneOutConstant
    have h51 : (4608 * 1 + 576 * 162 : ℝ) ≤ 7000 * Cshom ^ 2 := by
      have hval : (4608 * 1 + 576 * 162 : ℝ) = 97920 := by norm_num
      rw [hval]
      linarith only [hbig]
    exact mul_le_mul_of_nonneg_left h51 hCleg2
  exact clauseOne_bound M L m s.2 hs1 hsg omega
    (Jlegf := jLegField M L m omega) (Jlegt := jLegTranspose M L m omega)
    (Jannf := annularResponseMax M L m omega) (Jannt := Jannt)
    (E2 := fun j n => annularErrorLatticeMax M s omega j n)
    (sig := fun n => ((Annealed.sigmaBar M m : ℝ) *
      ((Annealed.sigmaBar M (n - 2) : ℝ))⁻¹ - 1) ^ 2)
    (L2f := annularL2Block M m omega)
    (gradNf := fun j n => 2 * annularGradBlock M m omega j n)
    (A := shellBlockLatticeReal M m omega)
    (Cbf := 1) (Kl2 := 1) (Kgn := 162) (Ktail := 2) (Cshom := Cshom)
    (by norm_num) hC₁ hC0 (by norm_num) (by norm_num) (by norm_num)
    (jLegField_nonneg M L m omega) (jLegTranspose_nonneg M L m omega)
    (annularResponseMax_nonneg M L m omega) hJannt0
    (fun j n => annularErrorLatticeMax_nonneg M s omega j n)
    (fun _n => sq_nonneg _)
    (annularL2Block_nonneg M m omega)
    (fun j n => by
      have h := annularGradBlock_nonneg M m omega j n
      linarith only [h])
    (hbfJ_latticeMax M L m omega le_rfl)
    (summable_jLegField M L m omega s.2) (summable_jLegTranspose M L m omega s.2)
    hpref hpret huglyf huglyt hsumE
    (summable_annFam_sig (a := Cshom * M.gamma)
      (B := Cshom * (2 * M.gamma
        + (Disorder.cstar M ^ 2)⁻¹ * (M.gamma * |Real.log M.gamma| ^ 2)))
      s.2 hs1 hgam0.le hsg ha0 hB0 (fun _n => sq_nonneg _) hshom)
    (summable_annFam_annularL2Block_of_eventG1 M m s.2 hs1 hsg hT0 hG1)
    (summable_annFam_two_annularGradBlock_of_eventG1 M m s.2 hs1 hT0 hG1)
    hcstar4 hlog hshom
    (summable_shellBlockLatticeReal_of_eventG1 M m s.2.le hG1)
    (fun j n hj hn => annularL2Block_le M m omega j n hj hn)
    (fun j n hj hn => by
      have hb := annularGradBlock_le M m omega j n hj hn
      have hid : (162 : ℝ) * (((m - n : ℤ) : ℝ) + 2)
            * ∑ v ∈ Finset.range ((m - n).toNat + 2),
              shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2
          = 2 * (81 * (((m - n : ℤ) : ℝ) + 2)
            * ∑ v ∈ Finset.range ((m - n).toNat + 2),
              shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2) := by ring
      rw [hid]
      linarith only [hb])
    hCleg hCout1 hCout2 hCout3

end

end Algsuperdiff.Section4.Provider.Annular
