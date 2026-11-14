/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.OscillationGrid
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.OffGridTransfer

/-!
# CampanatoFeed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The oscillation family in the shape a Campanato characterisation consumes

The Campanato characterisation of Hölder spaces on a cube reads a scale-indexed
family of clipped windows: at window index `j` the admissible centres are the
points of the lattice of spacing `3 ^ (m-j-1)` inside the cube, and the estimate
required is

`‖u - (u)_W‖_{L²(W)} ≤ K (3 ^ (m-j) / 2) ^ alpha`,  `W = (z + □_{m-j}) ∩ □_m`,

with one constant `K` serving every index and every centre.  This module turns
the two-parameter family of `OscillationGrid.lean` into exactly that predicate.

Two things happen here.  The bottom scale is chosen: `n = m-j-1` while that is
admissible, and `n = m - X` for the top `X` window indices, which is what
creates the factor `3 ^ ((1-alpha) X / 2)` in `K`.  And the seed is made
independent of the centre: the window `(z + □_m) ∩ □_m` is compared with the
cube itself at the volume price `2 ^ (d/2)`.

## Main definitions

* `campanatoGridConstant` — the constant `K` produced, written out.

## Main results

* `hasClipGridOscillationDecay_zeroDatum` — the family in the consumed shape.

## References

* [ABK], `ss.proof.regularity` Step 3 and display `e.oscillation.Holder.bound`.
-/

namespace Algsuperdiff.Section4.Provider.Holder

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Regularity
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The window and grid dictionaries -/

/-- The clipped window of index `j` about `z` in the cube `□_m` is the truncated
window of scale `m - j` about `z`. -/
theorem clipBall_zero_eq_truncatedWindow (m : ℤ) (z : Vec d) (j : ℕ) :
    clipBall (0 : Vec d) ((3 : ℝ) ^ m / 2) z (triadicRadius ((3 : ℝ) ^ m / 2) j) =
      truncatedWindow z m (m - (j : ℤ)) := by
  rw [truncatedWindow_eq_ball_inter_ball, clipBall, triadicRadius_half_zpow]

/-- The top truncated window is the clipped window of index `0`. -/
theorem truncatedWindow_top_eq_clipBall (m : ℤ) (z : Vec d) : truncatedWindow z m m =
      clipBall (0 : Vec d) ((3 : ℝ) ^ m / 2) z ((3 : ℝ) ^ m / 2) := by
  rw [truncatedWindow_eq_ball_inter_ball, clipBall]

/-- The clipped window at the centre of the cube is the cube. -/
theorem clipBall_centre_eq_openCubeSet (m : ℤ) :
    clipBall (0 : Vec d) ((3 : ℝ) ^ m / 2) 0 ((3 : ℝ) ^ m / 2) =
      openCubeSet (originCube d m) := by
  rw [clipBall, Set.inter_self, openCubeSet_originCube_eq_ball_zero]

/-- The spacing of the admissible centres at window index `j` is `3 ^ (m-j-1)`. -/
theorem two_mul_triadicRadius_succ (m : ℤ) (j : ℕ) :
    2 * triadicRadius ((3 : ℝ) ^ m / 2) (j + 1) = (3 : ℝ) ^ (m - (j : ℤ) - 1) := by
  rw [triadicRadius_half_zpow]
  push_cast
  ring_nf

/-- An admissible centre at window index `j` is a point of the triadic lattice of
scale `m - j - 1`. -/
theorem exists_index_of_mem_centredTriadicGrid (m : ℤ) (j : ℕ) {z : Vec d}
    (hz : z ∈ centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2) j) :
    ∃ v : Fin d → ℤ, z = triadicLatticePoint (m - (j : ℤ) - 1) v := by
  have hlat : ∀ i, ∃ n : ℤ,
      (z - (0 : Vec d)) i = 2 * triadicRadius ((3 : ℝ) ^ m / 2) (j + 1) * (n : ℝ) := hz.1
  have hmem : ∀ i, ∃ n : ℤ, z i = (3 : ℝ) ^ (m - (j : ℤ) - 1) * (n : ℝ) := by
    intro i
    obtain ⟨n, hn⟩ := hlat i
    exact ⟨n, by simpa [two_mul_triadicRadius_succ] using hn⟩
  choose v hv using hmem
  exact ⟨v, funext fun i => hv i⟩

/-- An admissible centre lies in the cube. -/
theorem mem_openCubeSet_of_mem_centredTriadicGrid (m : ℤ) (j : ℕ) {z : Vec d}
    (hz : z ∈ centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2) ((3 : ℝ) ^ m / 2) j) :
    z ∈ openCubeSet (originCube d m) := by
  rw [openCubeSet_originCube_eq_ball_zero]
  exact hz.2

/-! ## 2. The centre-free seed -/

/-- **The seed comparison.**  The oscillation on the top truncated window about a
centre of the cube is at most `2 ^ (d/2)` times the oscillation on the cube. -/
theorem normalizedL2On_truncatedWindow_top_le {m : ℤ} {z : Vec d}
    {f : Vec d → ℝ} (hz : z ∈ openCubeSet (originCube d m))
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m)))) :
    normalizedL2On (truncatedWindow z m m)
        (fun y => f y - volumeAverage (truncatedWindow z m m) f) ≤
      ballVolumePrice 2 d *
        normalizedL2On (openCubeSet (originCube d m))
          (fun y => f y - volumeAverage (openCubeSet (originCube d m)) f) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hR : (0 : ℝ) < (3 : ℝ) ^ m / 2 := by linarith only [h3]
  have hzb : z ∈ Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2) := by
    rwa [openCubeSet_originCube_eq_ball_zero] at hz
  have hfb : MemLp f 2 (volume.restrict (Metric.ball (0 : Vec d) ((3 : ℝ) ^ m / 2))) := by
    rwa [openCubeSet_originCube_eq_ball_zero] at hf
  have hsub : clipBall (0 : Vec d) ((3 : ℝ) ^ m / 2) z ((3 : ℝ) ^ m / 2) ⊆
      clipBall (0 : Vec d) ((3 : ℝ) ^ m / 2) 0 ((3 : ℝ) ^ m / 2) :=
    Set.subset_inter (clipBall_subset_ambient _ _ _ _) (clipBall_subset_ambient _ _ _ _)
  have h := oscillation_clipBall_le_of_subset (kappa := 2) (f := f) hR le_rfl hzb hR
    le_rfl (Metric.mem_ball_self hR) hsub (by linarith only []) hfb
  rw [clipBall_centre_eq_openCubeSet] at h
  rwa [truncatedWindow_top_eq_clipBall]

/-! ## 3. The constant -/

/-- **The Campanato constant produced by the choice of bottom scale.**  The
factor `3 ^ ((1-alpha)(X+1)/2)` is the price of the top `X` window indices, at
which the bottom scale is frozen at `m - X`, together with the one triadic scale
between a centre's own lattice and its window; the factor `3 ^ ((1-alpha) m)`
is the normalization of the seed, and `2 ^ alpha` the half-side dictionary. -/
def campanatoGridConstant (alpha : ℝ) (m : ℤ) (Xn : ℕ) (Cosc D : ℝ) : ℝ :=
  Real.rpow 2 alpha * Cosc *
    Real.rpow 3 ((1 - alpha) * ((m : ℝ) + ((Xn : ℝ) + 1) / 2)) * D

theorem campanatoGridConstant_nonneg {alpha : ℝ} (m : ℤ) (Xn : ℕ) {Cosc D : ℝ}
    (hCosc : 0 ≤ Cosc) (hD : 0 ≤ D) :
    0 ≤ campanatoGridConstant alpha m Xn Cosc D :=
  mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hCosc)
    (Real.rpow_nonneg (by norm_num) _)) hD

/-- The scale bookkeeping of the constant: an identity between powers of `3` and
`2`, with no estimate. -/
private theorem campanatoGridConstant_regroup (alpha : ℝ) (m : ℤ) (j : ℕ)
    (q Cosc D : ℝ) :
    (3 : ℝ) ^ (m - (j : ℤ)) *
        (Cosc * Real.rpow 3 ((1 - alpha) * ((j : ℝ) + q)) * D) =
      (Real.rpow 2 alpha * Cosc *
          Real.rpow 3 ((1 - alpha) * ((m : ℝ) + q)) * D) *
        Real.rpow ((3 : ℝ) ^ (m - (j : ℤ)) / 2) alpha := by
  have hrfl : ∀ a b : ℝ, Real.rpow a b = a ^ b := fun _ _ => rfl
  have h2 : ((2 : ℝ) ^ alpha) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (m - (j : ℤ)) := zpow_pos (by norm_num) _
  have hbase : (3 : ℝ) ^ (m - (j : ℤ)) = (3 : ℝ) ^ ((m : ℝ) - (j : ℝ)) := by
    rw [← Real.rpow_intCast (3 : ℝ) (m - (j : ℤ))]
    push_cast
    rfl
  simp only [hrfl]
  rw [Real.div_rpow h3.le (by norm_num : (0 : ℝ) ≤ 2), hbase,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp
  rw [show (3 : ℝ) ^ ((m : ℝ) - (j : ℝ)) * Cosc *
          (3 : ℝ) ^ ((1 - alpha) * ((j : ℝ) + q)) * D
        = Cosc * D *
            ((3 : ℝ) ^ ((m : ℝ) - (j : ℝ)) *
              (3 : ℝ) ^ ((1 - alpha) * ((j : ℝ) + q))) from by ring,
    show Cosc * D * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) + q)) *
          (3 : ℝ) ^ (((m : ℝ) - (j : ℝ)) * alpha)
        = Cosc * D *
            ((3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) + q)) *
              (3 : ℝ) ^ (((m : ℝ) - (j : ℝ)) * alpha)) from by ring,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    show ((m : ℝ) - (j : ℝ)) + (1 - alpha) * ((j : ℝ) + q)
        = (1 - alpha) * ((m : ℝ) + q) + ((m : ℝ) - (j : ℝ)) * alpha from by ring]

/-! ## 4. The feed -/

/-- **[ABK] `e.oscillation.Holder.bound`, in the shape a Campanato
characterisation of Hölder spaces on the cube consumes.**

For a disorder model of strength `gamma` small enough and every Hölder exponent
`alpha` below `1 - C sqrt gamma`, and for every scale `m`, there is a minimal
scale `X` -- measurable, with the exponential tail of the regularity theorem --
such that, almost surely, for every natural bound `Xn` on `X`, every truncation
index `L ≥ m`, and every zero-datum Dirichlet solution `u` on `□_m` with force
`g` of `C^{0,1/2}` seminorm at most `K_g`, the clipped-window oscillation decay
of exponent `alpha` holds at every index of the triadic family of centres
inside `□_m`, with the single constant `campanatoGridConstant` and the seed read
on the cube itself.

The bottom scale is chosen by the two-case rule of the source's scale range:
`n = m-j-1` while that is admissible, `n = m - X` above it. -/
theorem hasClipGridOscillationDecay_zeroDatum (d : ℕ) [NeZero d] (hd : d ≠ 0)
    (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C Cosc Cdata : ℝ, 0 < gamma0 ∧ 0 < C ∧ 0 ≤ Cosc ∧ 0 ≤ Cdata ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 - C * Real.sqrt M.gamma →
          ∀ m : ℤ, ∃ X : Cutoff.CutoffSample d → ℕ∞,
            Measurable X ∧
            (∀ N : ℕ,
                (Cutoff.cutoffSampleLaw M).toMeasure {omega | (N : ℕ∞) ≤ X omega} ≤
                  ENNReal.ofReal
                    (C * Real.exp
                      (-((1 - alpha) ^ (2 : ℕ) * ((N : ℝ) - C)) / (C * M.gamma)))) ∧
            ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
              ∀ Xn : ℕ, X omega ≤ (Xn : ℕ∞) →
                ∀ L : ℤ, m ≤ L →
                  ∀ (u : H1Function (openCubeSet (originCube d m)))
                    (g : Vec d → Vec d) (Kg : ℝ), 0 ≤ Kg →
                    IsDirichletSolutionOn
                        (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                        (originCube d m) u 0 g →
                    HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
                      HasClipGridOscillationDecay (0 : Vec d) ((3 : ℝ) ^ m / 2)
                        (centredTriadicGrid (0 : Vec d) ((3 : ℝ) ^ m / 2)
                          ((3 : ℝ) ^ m / 2))
                        ((3 : ℝ) ^ m / 2) alpha
                        (campanatoGridConstant alpha m Xn Cosc
                          ((3 : ℝ) ^ (-m) *
                              (ballVolumePrice 2 d *
                                normalizedL2On (openCubeSet (originCube d m))
                                  (fun y => u.toFun y -
                                    volumeAverage (openCubeSet (originCube d m))
                                      u.toFun)) +
                            Cdata *
                              (((Annealed.sigmaBar M m : ℝ))⁻¹ *
                                Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg)))
                        0 u.toFun := by
  classical
  obtain ⟨gamma0, C, Cosc, Cdata, hgamma0, hC, hCosc, hCdata, hmain⟩ :=
    oscillationHolderBound_zeroDatum_grid d hd cstar hcstar
  refine ⟨gamma0, C, Cosc, Cdata, hgamma0, hC, hCosc, hCdata, ?_⟩
  intro M hcs hgamma alpha halpha0 halpha m
  obtain ⟨X, hXmeas, hXtail, hXae⟩ := hmain M hcs hgamma alpha halpha0 halpha m
  refine ⟨X, hXmeas, hXtail, ?_⟩
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have halpha1 : alpha ≤ 1 := by
    have h : 0 < C * Real.sqrt M.gamma := mul_pos hC (Real.sqrt_pos.mpr hgpos)
    linarith only [halpha, h]
  have hA : (0 : ℝ) ≤ 1 - alpha := by linarith only [halpha1]
  filter_upwards [hXae] with omega hom
  intro Xn hXn L hmL u g Kg hKg hsol hgHol
  set S : ℝ := normalizedL2On (openCubeSet (originCube d m))
      (fun y => u.toFun y - volumeAverage (openCubeSet (originCube d m)) u.toFun) with hSdef
  set leg : ℝ :=
    ((Annealed.sigmaBar M m : ℝ))⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg with hlegdef
  set D : ℝ := (3 : ℝ) ^ (-m) * (ballVolumePrice 2 d * S) + Cdata * leg with hDdef
  have hSnn : (0 : ℝ) ≤ S := normalizedL2On_nonneg _ _
  have hlegnn : (0 : ℝ) ≤ leg :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Annealed.sigmaBar M m).2.le)
      (Real.rpow_nonneg (by norm_num) _)) hKg
  have hDnn : (0 : ℝ) ≤ D := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-m) * (ballVolumePrice 2 d * S) :=
      mul_nonneg (zpow_nonneg (by norm_num) _)
        (mul_nonneg (ballVolumePrice_nonneg 2 d) hSnn)
    have h2 : (0 : ℝ) ≤ Cdata * leg := mul_nonneg hCdata hlegnn
    rw [hDdef]
    linarith only [h1, h2]
  intro jN _hj0 z hz
  set n : ℤ := min (m - (jN : ℤ) - 1) (m - (Xn : ℤ)) with hndef
  have hnk : n ≤ m - (jN : ℤ) - 1 := min_le_left _ _
  have hnX : n ≤ m - (Xn : ℤ) := min_le_right _ _
  have hkm : m - (jN : ℤ) ≤ m := by omega
  have hgate : X omega ≤ (((m - n).toNat : ℕ) : ℕ∞) := by
    refine le_trans hXn ?_
    exact_mod_cast Nat.cast_le.mpr (by omega : Xn ≤ (m - n).toNat)
  have hzcube : z ∈ openCubeSet (originCube d m) :=
    mem_openCubeSet_of_mem_centredTriadicGrid m jN hz
  obtain ⟨v, hv⟩ := exists_index_of_mem_centredTriadicGrid m jN hz
  have hfam := hom L hmL u g Kg hKg hsol hgHol n (m - (jN : ℤ)) m hnk hkm le_rfl hgate z
    hzcube ⟨v, hv⟩
  -- the centre-free seed
  have hseed := normalizedL2On_truncatedWindow_top_le hzcube u.memL2
  have hbracket :
      (3 : ℝ) ^ (-m) *
            normalizedL2On (truncatedWindow z m m)
              (fun y => u.toFun y - volumeAverage (truncatedWindow z m m) u.toFun) +
          Cdata * leg ≤ D := by
    have h := mul_le_mul_of_nonneg_left hseed
      (zpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (-m))
    rw [hDdef]
    linarith only [h]
  -- the choice of bottom scale
  have hint : (m : ℤ) - n ≤ (jN : ℤ) + 1 + (Xn : ℤ) := by omega
  have ht : (m : ℝ) - (n : ℝ) ≤ (jN : ℝ) + 1 + (Xn : ℝ) := by exact_mod_cast hint
  have hjnn : (0 : ℝ) ≤ (jN : ℝ) := Nat.cast_nonneg jN
  have hexp : 1 / 2 * ((1 - alpha) * ((m : ℝ) - (n : ℝ))) ≤
      (1 - alpha) * ((jN : ℝ) + ((Xn : ℝ) + 1) / 2) := by
    have key : (1 / 2 : ℝ) * ((m : ℝ) - (n : ℝ)) ≤ (jN : ℝ) + ((Xn : ℝ) + 1) / 2 := by
      linarith only [ht, hjnn]
    have h := mul_le_mul_of_nonneg_left key hA
    linarith only [h]
  have hPQ : Real.rpow (3 : ℝ) (1 / 2 * ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) ≤
      Real.rpow (3 : ℝ) ((1 - alpha) * ((jN : ℝ) + ((Xn : ℝ) + 1) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hPnn : (0 : ℝ) ≤ Real.rpow (3 : ℝ) (1 / 2 * ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) :=
    Real.rpow_nonneg (by norm_num) _
  -- assembling
  set O : ℝ := normalizedL2On (truncatedWindow z m (m - (jN : ℤ)))
      (fun y => u.toFun y -
        volumeAverage (truncatedWindow z m (m - (jN : ℤ))) u.toFun) with hOdef
  have hstep :
      (3 : ℝ) ^ (-(m - (jN : ℤ))) * O ≤
        Cosc * Real.rpow (3 : ℝ) ((1 - alpha) * ((jN : ℝ) + ((Xn : ℝ) + 1) / 2)) * D := by
    have h1 := mul_le_mul_of_nonneg_left hbracket
      (mul_nonneg hCosc hPnn)
    have h2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPQ hCosc) hDnn
    linarith only [hfam, h1, h2]
  have hOeq : O = (3 : ℝ) ^ (m - (jN : ℤ)) * ((3 : ℝ) ^ (-(m - (jN : ℤ))) * O) := by
    rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  have hfinal : O ≤
      campanatoGridConstant alpha m Xn Cosc D *
        Real.rpow ((3 : ℝ) ^ (m - (jN : ℤ)) / 2) alpha := by
    calc O = (3 : ℝ) ^ (m - (jN : ℤ)) * ((3 : ℝ) ^ (-(m - (jN : ℤ))) * O) := hOeq
      _ ≤ (3 : ℝ) ^ (m - (jN : ℤ)) *
            (Cosc *
              Real.rpow (3 : ℝ) ((1 - alpha) * ((jN : ℝ) + ((Xn : ℝ) + 1) / 2)) * D) :=
          mul_le_mul_of_nonneg_left hstep (zpow_nonneg (by norm_num) _)
      _ = campanatoGridConstant alpha m Xn Cosc D *
            Real.rpow ((3 : ℝ) ^ (m - (jN : ℤ)) / 2) alpha := by
          rw [campanatoGridConstant]
          exact campanatoGridConstant_regroup alpha m jN (((Xn : ℝ) + 1) / 2) Cosc D
  rw [clipBall_zero_eq_truncatedWindow, triadicRadius_half_zpow]
  exact hfinal

end

end Algsuperdiff.Section4.Provider.Holder
