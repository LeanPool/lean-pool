/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseLoadMeas
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoGrid
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseDisplayTwoMoment
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellL8
public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.External.CalderonZygmund
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# PrincipalResponseIndepAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
NOTE: this module is an ordinary Provider helper / conditional A.  The binder
inventories below are informal descriptions only.

# The second moment's gauged load

MODULE.  It is not imported by `Algsuperdiff/Section3.lean` and is not part of
any build closure.

Sources in ABK26:

* The sentence "Therefore, by independence of `bfA_{m-h}` and
  `G_{-(h)_{z+cu_n}} P_z` (the latter is a function of `k_m - k_{m-h}`),
  increasing `M` in `\eqref{e.cgamma.constraints}` if necessary,";
* `e.nablaw.in.L.eight` (label; display);
* `e.Pz.def` (label; display), the load;
* `e.Gh.def`, the doubled shear that gauges it;
* `e.recurrence.params` (label; display).

## What this module supplies

Exactly one input of the factorization
`ApproximateRecurrence.PrincipalResponseLegsIndep`
`integral_blockQuadratic_shellSplit_eq`, namely `hW`: the second-moment
integrability, against `M.P.toMeasure`, of every product of two doubled
coordinates of the gauged load `G_{-(h)_{z+cu_n}} P_z`.  It is the input that
`ApproximateRecurrence.PrincipalResponseLoadMeas`
`integral_blockQuadratic_shellSplit_eq_gaugedPrincipalLoadShell` still carries
as a binder.

`hW` is **not** supplied unconditionally.  It is supplied under the parameter
gates the manuscript's own display `e.nablaw.in.L.eight` is stated under: a
threshold `gamma0`, the induction state `S(m0, E)`, and the three scale gates
`m - h <= m0`, `h <= 6 cstar gamma^{-1}`, `K >= m + 10^10 gamma^{-1}` of
`e.recurrence.params`.  That is the shape in which the corrector moment exists
in this repository at all.

## The route, factor by factor

The gauged load is `(P_z, -(h)_^{(1)} + P_z^{(2)})`.  Four quantities enter its
squared coordinates, and each is reduced to the volume-normalized Euclidean
`L^8` norm on the large cube `cu_K`:

1. the averaged Dirichlet gradient `(grad w_D)_R`, by the vector Jensen
   inequality on `R` and the grid re-assembly
   `descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le` read at the single
   cube `R` (`le_card_mul_descendantsAverage`);
2. the averaged flux `(grad w_N + shom^{-1} h e')_R`, by the same route after
   the Minkowski step `cubeEuclideanLpNorm_add_le`;
3. the averaged fresh shell `(h)_R`, column by column: the `j`-th column of
   `freshShellCubeAverage` is `cubeAverageVec R` of the field
   `x |-> (k_m - k_n)(x) e_j`, i.e. of `streamForcing 1` at the direction
   `Pi.single j 1`, so the same grid bound applies and
   `cubeEuclideanLpNorm_streamForcing_le` converts it to the stream-increment
   `L^8` norm.  The passage from the columns to the matrix is the Frobenius
   bound `vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq`, so no
   operator-norm-of-an-average estimate is needed;
4. the `L^8` membership of the two corrector gradients, which is **not** a
   consequence of the `H^1` structure and is taken from the frozen external
   anchor `Algsuperdiff.Frozen.External.calderon_zygmund` directly: the anchor
   returns `MemLp grad p` alongside the norm bound, and `Corrector.FreshShellCZ`
   discards the membership.

The two random inputs are then the head-plus-tail displays
`Corrector.exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow`
(gated; `e.nablaw.in.L.eight`) and
`Corrector.exists_streamIncrementLpNormSq_head_tail` (ungated; `e.km.kn.Lp` at
`p = 8`).  Neither fluctuation is measurable, so the integrability is obtained
through the measurable-proxy device already used by
`PrincipalResponseDisplayTwoMoment.integral_le_of_le_shift_add_kappa_sq`:
`integrable_of_abs_le_shift_add_kappa_sq` below runs CoarseGraining's
`IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma` on `sqrt(max(|f| -
B, 0)/kappa)` and dominates.  The two `Gamma_1` lanes are merged by
`isBigOWith_gammaSigma_one_add`.

## What this module does NOT supply

It does not assemble `hindep`, and it does not re-state any consumer with
`hindep` removed.  `hindep` remains a binder of
`ApproximateRecurrence.PrincipalResponseBudgetWire`
`exists_smallCoupling_principalEnergy_bound_of_centering`
and of its predecessors, untouched by anything below.  In particular no
declaration below mentions `gaugedPrincipalLoadShell_val` or any matrix-side
declaration of `PrincipalResponseLowerShellMeas`: the whole file is on the load
side of the factorization.

The matrix side of that module is now its representative interface:
`exists_measurable_representative_switchCubeMatrix` produces some
`B : Cutoff.ShellSeq d → BlockMat d` that is entrywise
`Cutoff.lowerShellLocalCompletion M L U`-measurable and agrees with
`PrincipalResponseIndepWire.switchCubeMatrix` almost everywhere under
`Cutoff.cutoffSampleLaw M`, and its consumers carry that pair as binders.  An
earlier version of this paragraph named the pre-redesign zero-extension surface
`switchCubeMatrixShell` and its `_val` bridge; those two declarations are
`private` to `PrincipalResponseLowerShellMeas`, are not part of any interface,
and the reference to them is withdrawn here in favour of the representative
interface that replaced them.

It supplies no measurability of the load (that is
`PrincipalResponseLoadMeas.measurable_shellIndexSigma_gaugedPrincipalLoadShell`,
used here only to obtain the ambient measurability the integrability needs), no
moment bound (only finiteness of the second moment is proved; no numerical
constant is asserted), and no statement about `hBmeas`.

## Main results

* `exists_kappa_abs_gaugedLoad_mul_le` -- the pathwise bound; sorry-free.
* `exists_gamma0_integrable_toFullBlockVec_gaugedPrincipalLoadShell_mul` -- the
  `hW` input, under the gates.

## References

* ABK26; `e.nablaw.in.L.eight` (label); `e.km.kn.Lp`; `e.Pz.def` (label);
  `e.Gh.def`; `e.recurrence.params` (label).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Cross-term absorption over abstract reals: two squares bounded by the same
quantity bound their product.  Extracted so that the applications below never
enter a nonlinear arithmetic tactic. -/
private theorem mul_le_of_sq_le_of_sq_le {x y S : ℝ}
    (hx : x ^ (2 : ℕ) ≤ S) (hy : y ^ (2 : ℕ) ≤ S) : x * y ≤ S := by
  have hsq : (0 : ℝ) ≤ (x - y) ^ (2 : ℕ) := sq_nonneg _
  have hexp : (x - y) ^ (2 : ℕ) = x ^ (2 : ℕ) + y ^ (2 : ℕ) - 2 * (x * y) := by ring
  linarith only [hx, hy, hsq, hexp]

private theorem abs_toFullBlockVec_mul_le (X : BlockVec d) (alpha beta : BlockCoord d) :
    |toFullBlockVec X alpha * toFullBlockVec X beta| ≤ vecNormSq X.1 + vecNormSq X.2 := by
  have key : ∀ a : BlockCoord d,
      toFullBlockVec X a ^ (2 : ℕ) ≤ vecNormSq X.1 + vecNormSq X.2 := by
    intro a
    cases a with
    | inl i =>
        have h1 : X.1 i ^ (2 : ℕ) ≤ vecNormSq X.1 := sq_apply_le_vecNormSq X.1 i
        have h2 : (0 : ℝ) ≤ vecNormSq X.2 := vecNormSq_nonneg X.2
        change X.1 i ^ (2 : ℕ) ≤ _
        linarith only [h1, h2]
    | inr i =>
        have h1 : X.2 i ^ (2 : ℕ) ≤ vecNormSq X.2 := sq_apply_le_vecNormSq X.2 i
        have h2 : (0 : ℝ) ≤ vecNormSq X.1 := vecNormSq_nonneg X.1
        change X.2 i ^ (2 : ℕ) ≤ _
        linarith only [h1, h2]
  rw [abs_mul]
  have ha := key alpha
  have hb := key beta
  have hsa : |toFullBlockVec X alpha| ^ (2 : ℕ) ≤ vecNormSq X.1 + vecNormSq X.2 := by
    rw [sq_abs]; exact ha
  have hsb : |toFullBlockVec X beta| ^ (2 : ℕ) ≤ vecNormSq X.1 + vecNormSq X.2 := by
    rw [sq_abs]; exact hb
  exact mul_le_of_sq_le_of_sq_le hsa hsb

private theorem abs_toFullBlockVec_gauge_mul_le (sigma : PositiveScalar) (Hm : Mat d)
    (p q : Vec d) (alpha beta : BlockCoord d) :
    |toFullBlockVec (blockMatVecMul (blockGauge (-Hm))
          (principalLoad sigma (p, q))) alpha *
        toFullBlockVec (blockMatVecMul (blockGauge (-Hm))
          (principalLoad sigma (p, q))) beta| ≤
      (1 + 2 * Ch02.matrixFrobeniusNormSq Hm) * ((sigma : ℝ)⁻¹ * vecNormSq p) +
        2 * ((sigma : ℝ) * vecNormSq q) := by
  have hsi : (0 : ℝ) < (sigma : ℝ) := sigma.2
  set P1 : Vec d := inverseSqrtLoad sigma p with hP1
  set P2 : Vec d := sqrtLoad sigma q with hP2
  have hload : principalLoad sigma (p, q) = (P1, P2) := principalLoad_eq sigma (p, q)
  have hX : blockMatVecMul (blockGauge (-Hm)) (principalLoad sigma (p, q)) =
      (P1, matVecMul (-Hm) P1 + P2) := by
    rw [hload, blockMatVecMul_blockGauge]
  rw [hX]
  refine le_trans (abs_toFullBlockVec_mul_le (P1, matVecMul (-Hm) P1 + P2) alpha beta) ?_
  have hfst : vecNormSq P1 = (sigma : ℝ)⁻¹ * vecNormSq p := by
    rw [hP1, inverseSqrtLoad, vecNormSq_smul]
    congr 1
    rw [← Real.sqrt_inv, Real.sq_sqrt (inv_nonneg.2 hsi.le)]
  have hsnd : vecNormSq P2 = (sigma : ℝ) * vecNormSq q := by
    rw [hP2, sqrtLoad, vecNormSq_smul, Real.sq_sqrt hsi.le]
  have hsplit : vecNormSq (matVecMul (-Hm) P1 + P2) ≤
      2 * (vecNormSq (matVecMul (-Hm) P1) + vecNormSq P2) :=
    vecNormSq_add_le _ _
  have hfrob : vecNormSq (matVecMul (-Hm) P1) ≤
      Ch02.matrixFrobeniusNormSq (-Hm) * vecNormSq P1 :=
    Ch02.vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq (-Hm) P1
  have hneg : Ch02.matrixFrobeniusNormSq (-Hm) = Ch02.matrixFrobeniusNormSq Hm := by
    simp [Ch02.matrixFrobeniusNormSq]
  rw [hneg] at hfrob
  change vecNormSq P1 + vecNormSq (matVecMul (-Hm) P1 + P2) ≤ _
  rw [hfst] at hfrob ⊢
  rw [hsnd] at hsplit
  linarith only [hsplit, hfrob]

private theorem matrixFrobeniusNormSq_eq_sum_col (A : Mat d) :
    Ch02.matrixFrobeniusNormSq A = ∑ j, vecNormSq (fun i => A i j) := by
  have hcol : ∀ j : Fin d, vecNormSq (fun i => A i j) = ∑ i, A i j ^ (2 : ℕ) := by
    intro j
    change ∑ i, A i j * A i j = ∑ i, A i j ^ (2 : ℕ)
    exact Finset.sum_congr rfl fun i _ => (pow_two (A i j)).symm
  rw [Ch02.matrixFrobeniusNormSq]
  simp only [hcol]
  exact Finset.sum_comm

private theorem matVecMul_single_one (A : Mat d) (i j : Fin d) :
    matVecMul A (Pi.single j (1 : ℝ)) i = A i j := by
  simp [matVecMul, Pi.single_apply, Finset.sum_ite_eq']

private theorem col_freshShellCubeAverage_eq (R : TriadicCube d)
    (omega : Cutoff.ShellSeq d) (L Hi : ℤ) (j : Fin d) :
    (fun i => freshShellCubeAverage R omega L Hi i j) =
      cubeAverageVec R (streamForcing 1 omega L Hi (Pi.single j 1)) := by
  funext i
  change cubeAverage R (fun x => Cutoff.finiteShellIncrement omega L Hi x i j) =
    cubeAverage R (fun x => streamForcing 1 omega L Hi (Pi.single j 1) x i)
  refine congrArg (cubeAverage R) (funext fun x => ?_)
  change Cutoff.finiteShellIncrement omega L Hi x i j =
    ((1 : ℝ) • matVecMul (Cutoff.finiteShellIncrement omega L Hi x) (Pi.single j 1)) i
  rw [Pi.smul_apply, smul_eq_mul, one_mul,
    matVecMul_single_one (Cutoff.finiteShellIncrement omega L Hi x) i j]

private theorem le_card_mul_descendantsAverage {Q : TriadicCube d} {jd : ℕ}
    {F : TriadicCube d → ℝ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q jd)
    (hF : ∀ S ∈ descendantsAtDepth Q jd, 0 ≤ F S) :
    F R ≤ ((descendantsAtDepth Q jd).card : ℝ) * descendantsAverage Q jd F := by
  classical
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q jd).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨R, hR⟩
  have hsum : F R ≤ ∑ S ∈ descendantsAtDepth Q jd, F S := Finset.single_le_sum hF hR
  have hdef : descendantsAverage Q jd F =
      ((descendantsAtDepth Q jd).card : ℝ)⁻¹ * ∑ S ∈ descendantsAtDepth Q jd, F S := rfl
  rw [hdef, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcard), one_mul]
  exact hsum

private theorem sq_vecNormSq_add_cubeAverageVec_le_card (Q : TriadicCube d) (jd : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q jd) (c : Vec d)
    (u : Vec d → Vec d) (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    vecNormSq (c + cubeAverageVec R u) ^ (2 : ℕ) ≤
      ((descendantsAtDepth Q jd).card : ℝ) *
        (8 * vecNormSq c ^ (2 : ℕ) + 8 * cubeEuclideanLpNorm Q 8 u ^ (4 : ℕ)) := by
  refine le_trans (le_card_mul_descendantsAverage
    (F := fun S => vecNormSq (c + cubeAverageVec S u) ^ (2 : ℕ)) hR
    (fun S _ => by positivity)) ?_
  refine mul_le_mul_of_nonneg_left
    (descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le Q jd c u hu) (by positivity)

private theorem le_half_one_add_mul_of_sq_le {x C W : ℝ} (hW : 1 ≤ W)
    (h : x ^ (2 : ℕ) ≤ C * W) : x ≤ ((1 + C) / 2) * W := by
  have hsq : (0 : ℝ) ≤ (x - 1) ^ (2 : ℕ) := sq_nonneg _
  have hexp : (x - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 2 * x + 1 := by ring
  linarith only [h, hW, hsq, hexp]

private theorem mul_le_half_add_of_sq_le {x y C1 C2 W : ℝ}
    (h1 : x ^ (2 : ℕ) ≤ C1 * W) (h2 : y ^ (2 : ℕ) ≤ C2 * W) :
    x * y ≤ ((C1 + C2) / 2) * W := by
  have hsq : (0 : ℝ) ≤ (x - y) ^ (2 : ℕ) := sq_nonneg _
  have hexp : (x - y) ^ (2 : ℕ) = x ^ (2 : ℕ) + y ^ (2 : ℕ) - 2 * (x * y) := by ring
  linarith only [h1, h2, hsq, hexp]

private theorem gaugedLoad_coordinate_abs_bound :
    ∀ {d : ℕ} (K : ℤ) (jd : ℕ) {R : TriadicCube d},
      R ∈ descendantsAtDepth (originCube d K) jd →
        ∀ (L Hi : ℤ) (crd : ℝ),
          crd = (↑(descendantsAtDepth (originCube d K) jd).card : ℝ) →
            (0 : ℝ) ≤ crd →
              ∀ (omega : Cutoff.ShellSeq d) (S : ℝ),
                S = Stream.streamIncrementLpNorm (8 : ℝ) K L Hi omega →
                  ∀ (Wl : ℝ),
                    S ^ (4 : ℕ) ≤ Wl ^ (2 : ℕ) →
                      ∀ (j : Fin d),
                        (vecNormSq fun (i : Fin d) => freshShellCubeAverage R omega L Hi i j) ^ (2 : ℕ) ≤
                          (8 : ℝ) * crd * Wl ^ (2 : ℕ) := by
  intro d K jd R hR L Hi crd hcrd hcrd0 omega S hS Wl hS4 j
  have hFjmem : MemLp (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ)))
      (8 : ℝ≥0∞) (normalizedCubeMeasure (originCube d K)) :=
    memLp_normalizedCubeMeasure_of_continuous _ _ (continuous_streamForcing _ _ _ _ _)
  have hsingle : Ch02.vecNorm (Pi.single j (1 : ℝ) : Vec d) ≤ 1 := by
    have hz : vecNormSq (Pi.single j (1 : ℝ) : Vec d) = 1 := by
      change ∑ i, (Pi.single j (1 : ℝ) : Vec d) i * (Pi.single j (1 : ℝ) : Vec d) i = 1
      simp [Pi.single_apply]
    rw [vecNorm_eq_sqrt_vecNormSq, hz, Real.sqrt_one]
  have hFj0 : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d K) 8
      (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ))) :=
    cubeEuclideanLpNorm_nonneg _ _ _
  have hFjnorm : cubeEuclideanLpNorm (originCube d K) 8
      (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ))) ≤ S := by
    have hstr := cubeEuclideanLpNorm_streamForcing_le
      (sigmaInv := (1 : ℝ)) zero_le_one K L Hi omega hsingle
    rw [← hS] at hstr
    linarith only [hstr]
  have hFj4 : cubeEuclideanLpNorm (originCube d K) 8
      (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ))) ^ (4 : ℕ) ≤
        Wl ^ (2 : ℕ) := le_trans (pow_le_pow_left₀ hFj0 hFjnorm 4) hS4
  have h := sq_vecNormSq_add_cubeAverageVec_le_card (originCube d K) jd hR
    (0 : Vec d) (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ))) hFjmem
  rw [← hcrd, zero_add] at h
  have hz0 : vecNormSq (0 : Vec d) = 0 := by
    change ∑ i, (0 : Vec d) i * (0 : Vec d) i = 0
    simp
  rw [hz0] at h
  rw [col_freshShellCubeAverage_eq R omega L Hi j]
  calc vecNormSq (cubeAverageVec R
          (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ)))) ^ (2 : ℕ)
      ≤ crd * (8 * (0 : ℝ) ^ (2 : ℕ) + 8 * cubeEuclideanLpNorm (originCube d K) 8
          (streamForcing 1 omega L Hi (Pi.single j (1 : ℝ))) ^ (4 : ℕ)) := h
    _ ≤ crd * (8 * (0 : ℝ) ^ (2 : ℕ) + 8 * Wl ^ (2 : ℕ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcrd0
        linarith only [hFj4]
    _ = 8 * crd * Wl ^ (2 : ℕ) := by ring

private theorem gaugedLoad_rescaledForcingBound :
    ∀ {d : ℕ} {R : TriadicCube d} (L Hi : ℤ) (crd : ℝ)
      (omega : Cutoff.ShellSeq d) (Wl : ℝ),
      (∀ (j : Fin d),
          (vecNormSq fun (i : Fin d) => freshShellCubeAverage R omega L Hi i j) ^ (2 : ℕ) ≤ (8 : ℝ) * crd * Wl ^ (2 : ℕ)) →
        Ch02.matrixFrobeniusNormSq (freshShellCubeAverage R omega L Hi) ^ (2 : ℕ) ≤
          (8 : ℝ) * (↑d : ℝ) ^ (2 : ℕ) * crd * Wl ^ (2 : ℕ) := by
  intro d R L Hi crd omega Wl hcolbd
  rw [matrixFrobeniusNormSq_eq_sum_col]
  have hcard : ((Finset.univ : Finset (Fin d)).card : ℝ) = (d : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hcs : (∑ j, vecNormSq (fun i => freshShellCubeAverage R omega L Hi i j))
        ^ (2 : ℕ) ≤
      ((Finset.univ : Finset (Fin d)).card : ℝ) *
        ∑ j, vecNormSq (fun i => freshShellCubeAverage R omega L Hi i j) ^ (2 : ℕ) :=
    sq_sum_le_card_mul_sum_sq
  rw [hcard] at hcs
  have hsum : ∑ j, vecNormSq (fun i => freshShellCubeAverage R omega L Hi i j)
        ^ (2 : ℕ) ≤ (d : ℝ) * (8 * crd * Wl ^ (2 : ℕ)) := by
    calc ∑ j, vecNormSq (fun i => freshShellCubeAverage R omega L Hi i j) ^ (2 : ℕ)
        ≤ ∑ _j : Fin d, (8 * crd * Wl ^ (2 : ℕ)) :=
          Finset.sum_le_sum fun j _ => hcolbd j
      _ = (d : ℝ) * (8 * crd * Wl ^ (2 : ℕ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  calc (∑ j, vecNormSq (fun i => freshShellCubeAverage R omega L Hi i j)) ^ (2 : ℕ)
      ≤ (d : ℝ) * ∑ j,
          vecNormSq (fun i => freshShellCubeAverage R omega L Hi i j) ^ (2 : ℕ) := hcs
    _ ≤ (d : ℝ) * ((d : ℝ) * (8 * crd * Wl ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hsum hd0
    _ = 8 * (d : ℝ) ^ (2 : ℕ) * crd * Wl ^ (2 : ℕ) := by ring

private theorem exists_kappa_abs_gaugedLoad_mul_le (K : ℤ) (jd : ℕ)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth (originCube d K) jd)
    (sigma : PositiveScalar) (L Hi : ℤ) {e e' : Vec d}
    (he : Ch02.vecNorm e ≤ 1) (he' : Ch02.vecNorm e' ≤ 1) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ (omega : Cutoff.ShellSeq d)
        (wD : H10Function (openCubeSet (originCube d K)))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d K))),
        MemLp wD.toH1Function.grad (8 : ℝ≥0∞)
            (normalizedCubeMeasure (originCube d K)) →
        MemLp wN.toH1Function.grad (8 : ℝ≥0∞)
            (normalizedCubeMeasure (originCube d K)) →
        ∀ alpha beta : BlockCoord d,
          |toFullBlockVec (blockMatVecMul
                (blockGauge (-freshShellCubeAverage R omega L Hi))
                (principalPz sigma omega L Hi e e' R wD wN)) alpha *
              toFullBlockVec (blockMatVecMul
                (blockGauge (-freshShellCubeAverage R omega L Hi))
                (principalPz sigma omega L Hi e e' R wD wN)) beta| ≤
            kappa *
              (1 +
                cubeEuclideanLpNorm (originCube d K) 8 wD.toH1Function.grad ^ (2 : ℕ) +
                cubeEuclideanLpNorm (originCube d K) 8 wN.toH1Function.grad ^ (2 : ℕ) +
                Stream.streamIncrementLpNorm 8 K L Hi omega
                  ^ (2 : ℕ)) ^ (2 : ℕ) := by
  classical
  have hsi : (0 : ℝ) < (sigma : ℝ) := sigma.2
  have hsiInv : (0 : ℝ) < ((sigma : ℝ))⁻¹ := inv_pos.2 hsi
  set crd : ℝ := ((descendantsAtDepth (originCube d K) jd).card : ℝ) with hcrd
  have hcrd0 : (0 : ℝ) ≤ crd := by rw [hcrd]; positivity
  clear_value crd
  set CN : ℝ := 4 * (1 + ((sigma : ℝ))⁻¹ ^ (2 : ℕ)) ^ (2 : ℕ) with hCN
  have hCN0 : (0 : ℝ) ≤ CN := by rw [hCN]; positivity
  clear_value CN
  set CU : ℝ := (1 + 16 * crd) / 2 with hCU
  set CFU : ℝ := (8 * (d : ℝ) ^ (2 : ℕ) * crd + 16 * crd) / 2 with hCFU
  set CV : ℝ := (1 + crd * (8 + 8 * CN)) / 2 with hCV
  have hCUpos : (0 : ℝ) < CU := by rw [hCU]; linarith only [hcrd0]
  have hCFU0 : (0 : ℝ) ≤ CFU := by rw [hCFU]; positivity
  have hCV0 : (0 : ℝ) ≤ CV := by rw [hCV]; positivity
  clear_value CU CFU CV
  refine ⟨((sigma : ℝ))⁻¹ * CU + 2 * ((sigma : ℝ))⁻¹ * CFU + 2 * (sigma : ℝ) * CV, ?_, ?_⟩
  · have t1 : (0 : ℝ) < ((sigma : ℝ))⁻¹ * CU := mul_pos hsiInv hCUpos
    have t2 : (0 : ℝ) ≤ 2 * ((sigma : ℝ))⁻¹ * CFU :=
      mul_nonneg (by linarith only [hsiInv]) hCFU0
    have t3 : (0 : ℝ) ≤ 2 * (sigma : ℝ) * CV := mul_nonneg (by linarith only [hsi]) hCV0
    linarith only [t1, t2, t3]
  intro omega wD wN hD hN alpha beta
  have hesq : vecNormSq e ≤ 1 := by
    have h := Ch02.vecNorm_sq_eq_vecNormSq e
    have h0 := Ch02.vecNorm_nonneg e
    have hpw : Ch02.vecNorm e ^ (2 : ℕ) ≤ 1 := by
      calc Ch02.vecNorm e ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := pow_le_pow_left₀ h0 he 2
        _ = 1 := one_pow 2
    linarith only [h, hpw]
  have hesq' : vecNormSq e' ≤ 1 := by
    have h := Ch02.vecNorm_sq_eq_vecNormSq e'
    have h0 := Ch02.vecNorm_nonneg e'
    have hpw : Ch02.vecNorm e' ^ (2 : ℕ) ≤ 1 := by
      calc Ch02.vecNorm e' ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := pow_le_pow_left₀ h0 he' 2
        _ = 1 := one_pow 2
    linarith only [h, hpw]
  set ND : ℝ := cubeEuclideanLpNorm (originCube d K) 8 wD.toH1Function.grad with hND
  set NN : ℝ := cubeEuclideanLpNorm (originCube d K) 8 wN.toH1Function.grad with hNN
  set S : ℝ := Stream.streamIncrementLpNorm 8 K L Hi omega
    with hS
  have hND0 : (0 : ℝ) ≤ ND := by rw [hND]; exact cubeEuclideanLpNorm_nonneg _ _ _
  have hNN0 : (0 : ℝ) ≤ NN := by rw [hNN]; exact cubeEuclideanLpNorm_nonneg _ _ _
  have hS0 : (0 : ℝ) ≤ S := by
    rw [hS]
    exact Stream.streamIncrementLpNorm_nonneg _ _ _ _ _
  clear_value ND NN S
  set Wl : ℝ := 1 + ND ^ (2 : ℕ) + NN ^ (2 : ℕ) + S ^ (2 : ℕ) with hWl
  have hWl1 : (1 : ℝ) ≤ Wl := by
    rw [hWl]; linarith only [sq_nonneg ND, sq_nonneg NN, sq_nonneg S]
  have hWlND : ND ^ (2 : ℕ) ≤ Wl := by
    rw [hWl]; linarith only [sq_nonneg NN, sq_nonneg S]
  have hWlNN : NN ^ (2 : ℕ) ≤ Wl := by
    rw [hWl]; linarith only [sq_nonneg ND, sq_nonneg S]
  have hWlS : S ^ (2 : ℕ) ≤ Wl := by
    rw [hWl]; linarith only [sq_nonneg ND, sq_nonneg NN]
  clear_value Wl
  have hWlsq1 : (1 : ℝ) ≤ Wl ^ (2 : ℕ) := one_le_pow₀ hWl1
  have hND4 : ND ^ (4 : ℕ) ≤ Wl ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ (sq_nonneg ND) hWlND 2
    calc ND ^ (4 : ℕ) = (ND ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ Wl ^ (2 : ℕ) := h
  have hS4 : S ^ (4 : ℕ) ≤ Wl ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ (sq_nonneg S) hWlS 2
    calc S ^ (4 : ℕ) = (S ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ Wl ^ (2 : ℕ) := h
  -- the Dirichlet leg
  have hUb : vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ (2 : ℕ) ≤
      16 * crd * Wl ^ (2 : ℕ) := by
    have h := sq_vecNormSq_add_cubeAverageVec_le_card (originCube d K) jd hR e'
      (fun x => wD.toH1Function.grad x) hD
    rw [← hcrd, ← hND] at h
    have h1 : vecNormSq e' ^ (2 : ℕ) ≤ 1 := by
      simpa using pow_le_pow_left₀ (vecNormSq_nonneg e') hesq' 2
    have h2 : 8 * vecNormSq e' ^ (2 : ℕ) + 8 * ND ^ (4 : ℕ) ≤ 16 * Wl ^ (2 : ℕ) := by
      linarith only [h1, hND4, hWlsq1]
    calc vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x)) ^ (2 : ℕ)
        ≤ crd * (8 * vecNormSq e' ^ (2 : ℕ) + 8 * ND ^ (4 : ℕ)) := h
      _ ≤ crd * (16 * Wl ^ (2 : ℕ)) := mul_le_mul_of_nonneg_left h2 hcrd0
      _ = 16 * crd * Wl ^ (2 : ℕ) := by ring
  -- the Neumann leg
  have hFmem : MemLp (streamForcing ((sigma : ℝ))⁻¹ omega L Hi e') (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d K)) :=
    memLp_normalizedCubeMeasure_of_continuous _ _ (continuous_streamForcing _ _ _ _ _)
  have hGNeq : neumannFluxField sigma omega L Hi e' wN =
      fun x => wN.toH1Function.grad x +
        streamForcing ((sigma : ℝ))⁻¹ omega L Hi e' x := rfl
  have hGNmem : MemLp (neumannFluxField sigma omega L Hi e' wN) (8 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d K)) := by
    rw [hGNeq]; exact hN.add hFmem
  have hNFle : cubeEuclideanLpNorm (originCube d K) 8
      (neumannFluxField sigma omega L Hi e' wN) ≤ NN + ((sigma : ℝ))⁻¹ * S := by
    have hadd := cubeEuclideanLpNorm_add_le (originCube d K)
      (by norm_num : (1 : ℝ≥0∞) ≤ 8) (fun x => wN.toH1Function.grad x)
      (streamForcing ((sigma : ℝ))⁻¹ omega L Hi e')
      (memLp_vecNorm_of_memLp _ hN) (memLp_vecNorm_of_memLp _ hFmem)
    have hstr := cubeEuclideanLpNorm_streamForcing_le hsiInv.le K L Hi omega he'
    rw [← hS] at hstr
    rw [← hNN] at hadd
    rw [hGNeq]
    linarith only [hadd, hstr]
  have hNF0 : (0 : ℝ) ≤ cubeEuclideanLpNorm (originCube d K) 8
      (neumannFluxField sigma omega L Hi e' wN) := cubeEuclideanLpNorm_nonneg _ _ _
  have hNFsq : cubeEuclideanLpNorm (originCube d K) 8
        (neumannFluxField sigma omega L Hi e' wN) ^ (2 : ℕ) ≤
      2 * (1 + ((sigma : ℝ))⁻¹ ^ (2 : ℕ)) * Wl := by
    have h2 := pow_le_pow_left₀ hNF0 hNFle 2
    have h3 : (NN + ((sigma : ℝ))⁻¹ * S) ^ (2 : ℕ) ≤
        2 * NN ^ (2 : ℕ) + 2 * (((sigma : ℝ))⁻¹ ^ (2 : ℕ) * S ^ (2 : ℕ)) := by
      have hsq : (0 : ℝ) ≤ (NN - ((sigma : ℝ))⁻¹ * S) ^ (2 : ℕ) := sq_nonneg _
      have hexp : (NN + ((sigma : ℝ))⁻¹ * S) ^ (2 : ℕ) =
          2 * NN ^ (2 : ℕ) + 2 * (((sigma : ℝ))⁻¹ ^ (2 : ℕ) * S ^ (2 : ℕ)) -
            (NN - ((sigma : ℝ))⁻¹ * S) ^ (2 : ℕ) := by ring
      linarith only [hsq, hexp]
    have h4 : ((sigma : ℝ))⁻¹ ^ (2 : ℕ) * S ^ (2 : ℕ) ≤
        ((sigma : ℝ))⁻¹ ^ (2 : ℕ) * Wl :=
      mul_le_mul_of_nonneg_left hWlS (by positivity)
    linarith only [h2, h3, h4, hWlNN]
  have hNF4 : cubeEuclideanLpNorm (originCube d K) 8
        (neumannFluxField sigma omega L Hi e' wN) ^ (4 : ℕ) ≤ CN * Wl ^ (2 : ℕ) := by
    have h5 := pow_le_pow_left₀
      (sq_nonneg (cubeEuclideanLpNorm (originCube d K) 8
        (neumannFluxField sigma omega L Hi e' wN))) hNFsq 2
    calc cubeEuclideanLpNorm (originCube d K) 8
          (neumannFluxField sigma omega L Hi e' wN) ^ (4 : ℕ)
        = (cubeEuclideanLpNorm (originCube d K) 8
            (neumannFluxField sigma omega L Hi e' wN) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ ≤ (2 * (1 + ((sigma : ℝ))⁻¹ ^ (2 : ℕ)) * Wl) ^ (2 : ℕ) := h5
      _ = CN * Wl ^ (2 : ℕ) := by rw [hCN]; ring
  have hVb : vecNormSq (e + cubeAverageVec R
        (neumannFluxField sigma omega L Hi e' wN)) ^ (2 : ℕ) ≤
      crd * (8 + 8 * CN) * Wl ^ (2 : ℕ) := by
    have h := sq_vecNormSq_add_cubeAverageVec_le_card (originCube d K) jd hR e
      (neumannFluxField sigma omega L Hi e' wN) hGNmem
    rw [← hcrd] at h
    have h1 : vecNormSq e ^ (2 : ℕ) ≤ 1 := by
      simpa using pow_le_pow_left₀ (vecNormSq_nonneg e) hesq 2
    have h2 : 8 * vecNormSq e ^ (2 : ℕ) + 8 * cubeEuclideanLpNorm (originCube d K) 8
          (neumannFluxField sigma omega L Hi e' wN) ^ (4 : ℕ) ≤
        8 * Wl ^ (2 : ℕ) + 8 * (CN * Wl ^ (2 : ℕ)) := by
      linarith only [h1, hWlsq1, hNF4]
    calc vecNormSq (e + cubeAverageVec R
            (neumannFluxField sigma omega L Hi e' wN)) ^ (2 : ℕ)
        ≤ crd * (8 * vecNormSq e ^ (2 : ℕ) + 8 * cubeEuclideanLpNorm (originCube d K) 8
            (neumannFluxField sigma omega L Hi e' wN) ^ (4 : ℕ)) := h
      _ ≤ crd * (8 * Wl ^ (2 : ℕ) + 8 * (CN * Wl ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left h2 hcrd0
      _ = crd * (8 + 8 * CN) * Wl ^ (2 : ℕ) := by ring
  -- the gauge matrix
  have hcolbd := @gaugedLoad_coordinate_abs_bound (d) (K) (jd) (R) (hR) (L) (Hi) (crd) (hcrd)
    (hcrd0) (omega) (S) (hS) (Wl) (hS4)
  have hFrb := @gaugedLoad_rescaledForcingBound (d) (R) (L) (Hi) (crd) (omega) (Wl) (hcolbd)
  -- assembly
  clear hD hN hFmem hGNmem hGNeq hNFle hNF0 hNFsq hNF4 hcolbd hesq hesq' hWl
  refine le_trans (abs_toFullBlockVec_gauge_mul_le sigma
    (freshShellCubeAverage R omega L Hi)
    (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x))
    (e + cubeAverageVec R (neumannFluxField sigma omega L Hi e' wN)) alpha beta) ?_
  set U : ℝ := vecNormSq (e' + cubeAverageVec R (fun x => wD.toH1Function.grad x))
    with _hU
  set V : ℝ := vecNormSq (e + cubeAverageVec R
    (neumannFluxField sigma omega L Hi e' wN)) with _hV
  set Fr : ℝ := Ch02.matrixFrobeniusNormSq (freshShellCubeAverage R omega L Hi)
    with _hFr
  clear_value U V Fr
  have hUle : U ≤ CU * Wl ^ (2 : ℕ) := by
    rw [hCU]; exact le_half_one_add_mul_of_sq_le hWlsq1 hUb
  have hVle : V ≤ CV * Wl ^ (2 : ℕ) := by
    rw [hCV]; exact le_half_one_add_mul_of_sq_le hWlsq1 hVb
  have hFrUle : Fr * U ≤ CFU * Wl ^ (2 : ℕ) := by
    rw [hCFU]; exact mul_le_half_add_of_sq_le hFrb hUb
  have b1 : ((sigma : ℝ))⁻¹ * U ≤ ((sigma : ℝ))⁻¹ * (CU * Wl ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hUle hsiInv.le
  have b2 : 2 * ((sigma : ℝ))⁻¹ * (Fr * U) ≤
      2 * ((sigma : ℝ))⁻¹ * (CFU * Wl ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hFrUle (by linarith only [hsiInv])
  have b3 : 2 * (sigma : ℝ) * V ≤ 2 * (sigma : ℝ) * (CV * Wl ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hVle (by linarith only [hsi])
  calc (1 + 2 * Fr) * (((sigma : ℝ))⁻¹ * U) + 2 * ((sigma : ℝ) * V)
      = ((sigma : ℝ))⁻¹ * U + 2 * ((sigma : ℝ))⁻¹ * (Fr * U) +
        2 * (sigma : ℝ) * V := by ring
    _ ≤ ((sigma : ℝ))⁻¹ * (CU * Wl ^ (2 : ℕ)) +
        2 * ((sigma : ℝ))⁻¹ * (CFU * Wl ^ (2 : ℕ)) +
        2 * (sigma : ℝ) * (CV * Wl ^ (2 : ℕ)) := by linarith only [b1, b2, b3]
    _ = (((sigma : ℝ))⁻¹ * CU + 2 * ((sigma : ℝ))⁻¹ * CFU + 2 * (sigma : ℝ) * CV) *
        Wl ^ (2 : ℕ) := by ring

private theorem isBigOWith_posPart_load {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {Psi : ℝ → ℝ}
    {Y : Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hY : IndependentSums.IsBigOWith mu Psi Y A) :
    IndependentSums.IsBigOWith mu Psi (fun omega => max (Y omega) 0) A := by
  intro t ht
  have hAt : (0 : ℝ) < A * t := mul_pos hA (lt_of_lt_of_le zero_lt_one ht)
  have hset :
      IndependentSums.upperTailEvent (fun omega => max (Y omega) 0) (A * t) =
        IndependentSums.upperTailEvent Y (A * t) := by
    ext omega
    simp only [IndependentSums.mem_upperTailEvent, lt_max_iff]
    constructor
    · rintro (hlt | hlt)
      · exact hlt
      · exact absurd hlt (not_lt.2 hAt.le)
    · exact fun hlt => Or.inl hlt
  rw [hset]
  exact hY ht

private theorem rpow_two_eq_pow_load (y : ℝ) : y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem integrable_of_abs_le_shift_add_kappa_sq {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {f W Y : Omega → ℝ}
    {B kappa b A sigma : ℝ}
    (hsigma : 0 < sigma) (hA : 0 < A) (hb : 0 ≤ b) (hkappa : 0 < kappa)
    (hfm : Measurable f) (hWnn : ∀ omega, 0 ≤ W omega)
    (hfW : ∀ omega, |f omega| ≤ B + kappa * W omega ^ (2 : ℕ))
    (hWY : ∀ omega, W omega ≤ b + Y omega)
    (hY : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Y A) :
    Integrable f mu := by
  classical
  set P : Omega → ℝ := fun omega => max (|f omega| - B) 0 with hPdef
  have hPnn : ∀ omega, 0 ≤ P omega := fun omega => le_max_right _ _
  set W0 : Omega → ℝ := fun omega => Real.sqrt (P omega / kappa) with hW0def
  have hW0nn : ∀ omega, 0 ≤ W0 omega := fun omega => Real.sqrt_nonneg _
  have hW0m : Measurable W0 :=
    Real.continuous_sqrt.measurable.comp
      ((((continuous_abs.measurable.comp hfm).sub measurable_const).max
        measurable_const).div measurable_const)
  have hW0sq : ∀ omega, kappa * W0 omega ^ (2 : ℕ) = P omega := by
    intro omega
    rw [hW0def]
    have hnn : (0 : ℝ) ≤ P omega / kappa := div_nonneg (hPnn omega) hkappa.le
    rw [Real.sq_sqrt hnn]
    field_simp
  have hXle : ∀ omega, |f omega| ≤ B + kappa * W0 omega ^ (2 : ℕ) := by
    intro omega
    rw [hW0sq omega, hPdef]
    have h : |f omega| - B ≤ max (|f omega| - B) 0 := le_max_left _ _
    simp only
    linarith only [h]
  have hW0leW : ∀ omega, W0 omega ≤ W omega := by
    intro omega
    have hP : P omega ≤ kappa * W omega ^ (2 : ℕ) := by
      rw [hPdef]
      refine max_le ?_ (by positivity)
      linarith only [hfW omega]
    have hsq : W0 omega ^ (2 : ℕ) ≤ W omega ^ (2 : ℕ) := by
      have hid := hW0sq omega
      have hmul : kappa * W0 omega ^ (2 : ℕ) ≤ kappa * W omega ^ (2 : ℕ) :=
        by linarith only [hid, hP]
      exact le_of_mul_le_mul_left hmul hkappa
    exact le_of_sq_le_sq hsq (hWnn omega)
  set Yt : Omega → ℝ := fun omega => W0 omega - b with hYtdef
  have hYtm : Measurable Yt := hW0m.sub measurable_const
  have hYt : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) Yt A :=
    hY.of_le fun omega => by
      have h1 := hW0leW omega
      have h2 := hWY omega
      rw [hYtdef]
      simp only
      linarith only [h1, h2]
  have hmax := isBigOWith_posPart_load hA hYt
  have hIY : Integrable
      (fun omega => max (Yt omega) 0 ^ (2 : ℕ)) mu := by
    have h := IndependentSums.integrable_rpow_of_isBigOWith_gammaSigma
      (p := (2 : ℝ)) hsigma hA (by norm_num) (fun omega => le_max_right _ _)
      (hYtm.max measurable_const).aemeasurable hmax
    simpa only [rpow_two_eq_pow_load] using h
  have hdom2 : ∀ omega,
      W0 omega ^ (2 : ℕ) ≤ 2 * b ^ (2 : ℕ) + 2 * max (Yt omega) 0 ^ (2 : ℕ) := by
    intro omega
    have hle : W0 omega ≤ b + max (Yt omega) 0 := by
      have hm : Yt omega ≤ max (Yt omega) 0 := le_max_left _ _
      rw [hYtdef] at hm
      simp only at hm
      linarith only [hm]
    have hnn : (0 : ℝ) ≤ max (Yt omega) 0 := le_max_right _ _
    have hbm : (0 : ℝ) ≤ b + max (Yt omega) 0 := add_nonneg hb hnn
    have hmul : W0 omega * W0 omega ≤
        (b + max (Yt omega) 0) * (b + max (Yt omega) 0) :=
      mul_le_mul hle hle (hW0nn omega) hbm
    have hexp : (b + max (Yt omega) 0) * (b + max (Yt omega) 0) =
        2 * b ^ (2 : ℕ) + 2 * max (Yt omega) 0 ^ (2 : ℕ) -
          (b - max (Yt omega) 0) ^ (2 : ℕ) := by ring
    have hw : W0 omega ^ (2 : ℕ) = W0 omega * W0 omega := by ring
    linarith only [hmul, hexp, hw, sq_nonneg (b - max (Yt omega) 0)]
  have hIW0 : Integrable (fun omega => W0 omega ^ (2 : ℕ)) mu := by
    refine Integrable.mono'
      ((integrable_const (2 * b ^ (2 : ℕ))).add (hIY.const_mul 2))
      ((hW0m.pow_const 2).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun omega => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ W0 omega ^ (2 : ℕ))]
    exact hdom2 omega
  refine Integrable.mono'
    ((integrable_const B).add (hIW0.const_mul kappa))
    hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs]
  exact hXle omega

private theorem measurable_toFullBlockVec_apply_load {Omega : Type*}
    {mOmega : MeasurableSpace Omega} {W : Omega → BlockVec d}
    (hW : Measurable W) (a : BlockCoord d) :
    Measurable fun omega => toFullBlockVec (W omega) a := by
  cases a with
  | inl i => exact (measurable_pi_apply i).comp hW.fst
  | inr i => exact (measurable_pi_apply i).comp hW.snd


/-! ## The `L^8` membership of the two corrector gradients -/

/-- Internal.  The `L^8` membership of a Dirichlet corrector gradient on the
large cube, read off the frozen external anchor
`Algsuperdiff.Frozen.External.calderon_zygmund` directly.

`Corrector.FreshShellCZ` uses the anchor's norm bound and discards its `MemLp`
conclusion; the vector Jensen inequality on a subcube needs the membership, so
it is taken here from the same anchor and from nothing else. -/
private theorem memLp_eight_grad_dirichlet (hd : 2 ≤ d)
    (Q : TriadicCube d) (f : Vec d → Vec d) (hf : Continuous f)
    (w : H10Function (openCubeSet Q))
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -f x)) :
    MemLp w.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  obtain ⟨_, _, hCZ⟩ := Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd
    (8 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact ((hCZ Q f (memLp_normalizedCubeMeasure_of_continuous Q _ hf)).1 w hw).1

/-- Internal.  The Neumann half of `memLp_eight_grad_dirichlet`. -/
private theorem memLp_eight_grad_neumann (hd : 2 ≤ d)
    (Q : TriadicCube d) (f : Vec d → Vec d) (hf : Continuous f)
    (w : H1MeanZeroFunction (openCubeSet Q))
    (hw : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ)) (openCubeSet Q) w
      (fun x => -f x)) :
    MemLp w.toH1Function.grad (8 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  obtain ⟨_, _, hCZ⟩ := Algsuperdiff.Frozen.External.calderon_zygmund (d := d) hd
    (8 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact ((hCZ Q f (memLp_normalizedCubeMeasure_of_continuous Q _ hf)).2 w hw).1

/-! ## The `hW` input of the factorization -/

/-- **The second-moment integrability of the gauged load `G_{-(h)_R} P_z`.**

Every product of two doubled coordinates of the gauged load is integrable
against `M.P.toMeasure`.  This is the `hW` input of
`ApproximateRecurrence.PrincipalResponseLegsIndep`
`integral_blockQuadratic_shellSplit_eq`, hence the last integrability binder of
`ApproximateRecurrence.PrincipalResponseLoadMeas`
`integral_blockQuadratic_shellSplit_eq_gaugedPrincipalLoadShell`.

: this statement holds only under the propositions supplied by its binders,
which are

* `hd` -- the paper-wide `2 <= d`;
* `M.gamma <= gamma0` for the produced threshold, and the induction state
  `Algsuperdiff.Frozen.Section3.inductionState M m0 Eind`;
* `0 < hgap`, `m - hgap <= m0`, `hgap <= 6 cstar cgamma^{-1}` (/7183) and
  `10^10 cgamma^{-1} <= K - m` (`e.recurrence.params`);
* the two direction bounds `vecNorm e <= 1`, `vecNorm e' <= 1`;
* `hR`, the geometric membership of the localization cube;
* `hwD`, `hwN`, the two weak-solution properties of `e.def.w` (label) for the
  two families, at every shell sequence.

The first four groups are exactly the gates of `e.nablaw.in.L.eight` (label);
they are inherited, not added, and no numerical bound is asserted: only
finiteness of the second moment.  It is a provider A, not a source-facing
frozen declaration.

Reaches exactly the one permitted frozen theorem
`Algsuperdiff.Frozen.External.calderon_zygmund` (through the `L^8` membership
of the two corrector gradients and through `e.nablaw.in.L.eight`), a **proved**
external.  The route through `e.km.kn.Lp` at `p = 8` reaches
`Algsuperdiff.Frozen.Section3.stream_increment_lp_large_cube_bound`, also
**proved**. -/
theorem exists_gamma0_integrable_toFullBlockVec_gaugedPrincipalLoadShell_mul
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (hgap : ℕ), 0 < hgap → m - (hgap : ℤ) ≤ m0 →
            (hgap : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Ch02.vecNorm e ≤ 1 → Ch02.vecNorm e' ≤ 1 →
              ∀ (jd : ℕ) (R : TriadicCube d),
                R ∈ descendantsAtDepth (originCube d K) jd →
                ∀ (wD : Cutoff.ShellSeq d →
                    H10Function (openCubeSet (originCube d K)))
                  (wN : Cutoff.ShellSeq d →
                    H1MeanZeroFunction (openCubeSet (originCube d K))),
                  (∀ omega : Cutoff.ShellSeq d,
                    IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD omega)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                        (m - (hgap : ℤ)) m e x)) →
                  (∀ omega : Cutoff.ShellSeq d,
                    IsMeanZeroNeumannRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wN omega)
                      (fun x => -streamForcing
                        ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹ omega
                        (m - (hgap : ℤ)) m e' x)) →
                  ∀ alpha beta : BlockCoord d,
                    Integrable
                      (fun omega : Cutoff.ShellSeq d =>
                        toFullBlockVec (gaugedPrincipalLoadShell
                            (Annealed.sigmaBar M (m - (hgap : ℤ))) R
                            (m - (hgap : ℤ)) m e e' wD wN omega) alpha *
                          toFullBlockVec (gaugedPrincipalLoadShell
                            (Annealed.sigmaBar M (m - (hgap : ℤ))) R
                            (m - (hgap : ℤ)) m e e' wD wN omega) beta)
                      M.P.toMeasure := by
  classical
  obtain ⟨Chead, hChead0, gamma0, hg0pos, hg0quarter, hL8⟩ :=
    exists_cubeEuclideanL8_gradient_sq_sum_le_const_add_gammaPow d hd
  obtain ⟨Clp, hClp0, hLP⟩ := exists_streamIncrementLpNormSq_head_tail d
  refine ⟨gamma0, hg0pos, hg0quarter, ?_⟩
  intro M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he' jd R hR wD wN
    hwD hwN alpha beta
  have : NeZero d := ⟨by omega⟩
  have hgamma : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hnm : m - (hgap : ℤ) < m := by omega
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by positivity
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith only [hK, hpos]
    exact_mod_cast hle
  obtain ⟨Tfl, hTfl0, hTfltail, hTflbd⟩ :=
    hL8 M hMgamma m0 Eind hstate m K hgap hhpos hm hh hK e e' he he'
  obtain ⟨T, hT0, hTbd, hTtail⟩ := hLP M K (m - (hgap : ℤ)) m hnm hmK
  obtain ⟨kappa, hkappa0, hkappa⟩ := exists_kappa_abs_gaugedLoad_mul_le K jd hR
    (Annealed.sigmaBar M (m - (hgap : ℤ))) (m - (hgap : ℤ)) m he he'
  have hDmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_dirichlet hd (originCube d K) _
      (continuous_streamForcing _ _ _ _ _) (wD omega) (hwD omega)
  have hNmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wN omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_neumann hd (originCube d K) _
      (continuous_streamForcing _ _ _ _ _) (wN omega) (hwN omega)
  have hWmeas : Measurable
      (gaugedPrincipalLoadShell (Annealed.sigmaBar M (m - (hgap : ℤ))) R
        (m - (hgap : ℤ)) m e e' wD wN) :=
    (measurable_shellIndexSigma_gaugedPrincipalLoadShell hR
      (Annealed.sigmaBar M (m - (hgap : ℤ)))
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      ((Annealed.sigmaBar M (m - (hgap : ℤ)) : ℝ))⁻¹
      (m - (hgap : ℤ)) m e e' e e' wD wN hwD hwN).mono
      (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hfmeas : Measurable (fun omega : Cutoff.ShellSeq d =>
      toFullBlockVec (gaugedPrincipalLoadShell
          (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e'
          wD wN omega) alpha *
        toFullBlockVec (gaugedPrincipalLoadShell
          (Annealed.sigmaBar M (m - (hgap : ℤ))) R (m - (hgap : ℤ)) m e e'
          wD wN omega) beta) :=
    (measurable_toFullBlockVec_apply_load hWmeas alpha).mul
      (measurable_toFullBlockVec_apply_load hWmeas beta)
  have hcast : (m : ℝ) - ((m - (hgap : ℤ) : ℤ) : ℝ) = (hgap : ℝ) := by push_cast; ring
  have hhgapR : (0 : ℝ) < (hgap : ℝ) := by exact_mod_cast hhpos
  set A0 : ℝ := min M.gamma⁻¹ ((m : ℝ) - ((m - (hgap : ℤ) : ℤ) : ℝ)) *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hA0
  have hA0pos : (0 : ℝ) < A0 := by
    rw [hA0, hcast]
    exact mul_pos (lt_min (inv_pos.2 hgamma) hhgapR)
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hAmp0 : (0 : ℝ) ≤ Clp * A0 *
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ))) :=
    mul_nonneg (mul_nonneg hClp0.le hA0pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hApos : (0 : ℝ) < 2 * (M.gamma ^ (100 : ℕ) + Clp * A0 *
      (3 : ℝ) ^ (-((d : ℝ) / 8) * ((K : ℝ) - (m : ℝ)))) := by
    have h1 : (0 : ℝ) < M.gamma ^ (100 : ℕ) := pow_pos hgamma 100
    linarith only [h1, hAmp0]
  refine integrable_of_abs_le_shift_add_kappa_sq (B := 0)
    (W := fun omega : Cutoff.ShellSeq d => 1 +
      cubeEuclideanLpNorm (originCube d K) 8 (wD omega).toH1Function.grad ^ (2 : ℕ) +
      cubeEuclideanLpNorm (originCube d K) 8 (wN omega).toH1Function.grad ^ (2 : ℕ) +
      Stream.streamIncrementLpNorm 8 K (m - (hgap : ℤ)) m omega ^ (2 : ℕ))
    (b := 1 + Chead + Clp * A0) one_pos hApos
    (by
      have h := mul_nonneg hClp0.le hA0pos.le
      linarith only [h, hChead0]) hkappa0 hfmeas
    (fun omega => by positivity) (fun omega => ?_) (fun omega => ?_)
    (isBigOWith_gammaSigma_one_add hTfltail hTtail)
  · rw [zero_add]
    exact hkappa omega (wD omega) (wN omega) (hDmem omega) (hNmem omega) alpha beta
  · have h1 := hTflbd omega (wD omega) (hwD omega) (wN omega) (hwN omega)
    have h2 := hTbd omega
    linarith only [h1, h2]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
