/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.TraceDiff
public import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
public import LeanPool.HyperellipticCurves.ForMathlib.MvPowerSeriesPDeriv
public import LeanPool.HyperellipticCurves.Log.Fold.FtauFoldBasic
public import LeanPool.HyperellipticCurves.Series.FormalGroupLaw.Basic

import LeanPool.HyperellipticCurves.ForMathlib.Units
import LeanPool.HyperellipticCurves.Log.Trace.TraceFtau

/-!
# The fold-side inputs of the trace assembly

The three fold-shaped facts the trace-form derivation
(`LeanPool.HyperellipticCurves.Log.Trace.TraceAssemble`) reads off the fold pipeline of `F_τ`, and
the fold
form of `F_τ` as a formal group law.

* `ChabautyColeman.sum_traceMat_mul_setYZero_pderiv_FtauFold` (and its `_eq_C` form):
  the invariance identity of the trace form specialized at `Y = 0`, where `∂F/∂Y(X, 0)` is the
  differential matrix `M(X)` of the formal group law and the right-hand side is the
  constant trace matrix of the `τ`-datum — `C(X)·M(X) = C(0)`.
* `ChabautyColeman.bezout_ftauFoldPipe_map_setYZero`: the `Y = 0` image of a Bézout
  cofactor of the fold pipeline's output is one for the chart datum, by the unit law
  `ChabautyColeman.ftauFoldPipe_map_setYZero`.
* `ChabautyColeman.ftauFoldFGL`: the fold form of `F_τ` as a `ChabautyColeman.FormalGroupLaw`,
  packaging its centre value, unit laws, commutativity and associativity.
* `ChabautyColeman.ftauFoldFGLFrac`: its base change to `Frac O`, the form every downstream
  disk and counting statement uses, taking the uniformizer as the bundled
  `IsLocalRing.IsUniformizer` datum.

Blueprint nodes: `lem:Ftau-basic`, `thm:Ftau-assoc`, `thm:omega-prime-global` clause (c).
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

section Assemble

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsDomain O]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
  (hfdeg' : (f.map (algebraMap O (FractionRing O))).natDegree = 2 * n + 1)
  (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
  (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
  (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
  {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)

section YZero

variable {i : ℕ} {k : Fin n} {cY sY cP sP : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)}

include hf hfdeg hroot hcc ha hb hd hπ hπ0 in
/-- **The trace-form invariance identity at `Y = 0` for the fold pipeline**: specializing the
invariance identity along `Y ↦ 0` turns `∂F_j/∂Y_k` into the differential matrix `M` of the
formal group law and the right-hand side into the matrix of the constant `τ`-datum, so
`C(X)·M(X) = C(0)`. -/
theorem sum_traceMat_mul_setYZero_pderiv_FtauFold
    (hsplit : u = ∏ m : Fin n, (X - C (a m))) (hainj : Function.Injective a)
    (hinv : ∑ j : Fin n, traceMat (ftauFoldPipe A a b hu hne hv hw hbez d).1 sP i j
        * MvPowerSeries.pderiv (Sum.inr k) (FtauFold A a b hu hne hv hw hbez d j)
      = traceMat (ftauUY u n) sY i k) :
    ∑ j : Fin n, traceMat (chartU u n) (sP.map setYZero) i j
        * setYZero (MvPowerSeries.pderiv (Sum.inr k) (FtauFold A a b hu hne hv hw hbez d j))
      = traceMat (u.map MvPowerSeries.C) (sY.map setYZero) i k := by
  have hYm : (ftauUY u n).Monic := chartU_map_rename_monic Sum.inr hu hne.ge
  have hPm : (ftauFoldPipe A a b hu hne hv hw hbez d).1.Monic :=
    (hd.isFoldState (hf.map _) ((hf.natDegree_map _).trans hfdeg)
      (isFoldState_ftauUX hu hne hv hw hbez)
      (fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb hj) le_rfl).monicU
  have hfst := congrArg Prod.fst (ftauFoldPipe_map_setYZero hu hne hv hw hbez hf hfdeg
    hsplit hainj hroot hcc hb hd hπ hπ0)
  dsimp only at hfst
  have h := congrArg (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)
    hinv
  rw [map_sum, ← traceMat_map setYZero hYm sY i k, ftauUY_map_setYZero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, ← traceMat_map setYZero hPm sP i j, hfst]

include hf hfdeg hroot hcc ha hb hd hπ hπ0 in
/-- **`C(X)·M(X) = C(0)` with `C(0)` constant** at the fold pipeline: the invariance
identity at `Y = 0`, with its right-hand side identified as the trace matrix of the
`τ`-datum over `O`. -/
theorem sum_traceMat_mul_setYZero_pderiv_FtauFold_eq_C
    (hsplit : u = ∏ m : Fin n, (X - C (a m))) (hainj : Function.Injective a)
    (hsY : cY * ftauUY u n + sY * (2 * ftauVY hu hne hv hw hbez) = 1)
    (hinv : ∑ j : Fin n, traceMat (ftauFoldPipe A a b hu hne hv hw hbez d).1 sP i j
        * MvPowerSeries.pderiv (Sum.inr k) (FtauFold A a b hu hne hv hw hbez d j)
      = traceMat (ftauUY u n) sY i k) :
    ∑ j : Fin n, traceMat (chartU u n) (sP.map setYZero) i j
        * setYZero (MvPowerSeries.pderiv (Sum.inr k) (FtauFold A a b hu hne hv hw hbez d j))
      = MvPowerSeries.C (traceMat u c₂ i k) :=
  (sum_traceMat_mul_setYZero_pderiv_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd
    hπ hπ0 hsplit hainj hinv).trans (traceMat_map_setYZero_eq_C hsY k)

include hf hfdeg hroot hcc hb hd hπ hπ0 in
/-- The `Y = 0` image of a Bézout cofactor of the fold pipeline's output is one for the
chart datum: this is what lets the formal identity be read at the universal chart datum. -/
theorem bezout_ftauFoldPipe_map_setYZero
    (hsplit : u = ∏ m : Fin n, (X - C (a m))) (hainj : Function.Injective a)
    (hsP : cP * (ftauFoldPipe A a b hu hne hv hw hbez d).1
      + sP * (2 * (ftauFoldPipe A a b hu hne hv hw hbez d).2) = 1) :
    cP.map setYZero * chartU u n
      + sP.map setYZero * (2 * chartV hu hne.ge hv hw hbez) = 1 := by
  have hpair := ftauFoldPipe_map_setYZero hu hne hv hw hbez hf hfdeg hsplit hainj hroot hcc
    hb hd hπ hπ0
  have hfst := congrArg Prod.fst hpair
  have hsnd := congrArg Prod.snd hpair
  dsimp only at hfst hsnd
  have h := map_bezout
    (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O) hsP
  rwa [hfst, hsnd] at h

end YZero

/-- **The fold form of the translated Cantor addition is a formal group law**: `F_τ` in its fold
form, with its unit laws, commutativity and associativity. -/
noncomputable def ftauFoldFGL (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j)) :
    FormalGroupLaw O (Fin n) where
  F := FtauFold A a b hu hne hv hw hbez d
  zero_constantCoeff :=
    constantCoeff_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd
  add_zero' i := by
    have hainj := Function.injective_of_isUnit_sub hunit
    rw [← setYZero_apply]
    exact setYZero_FtauFold hu hne hv hw hbez hf hfdeg hsplit hainj hroot hcc hb hd hπ hπ0 i
  zero_add' i := by
    rw [← setXZero_apply]
    exact setXZero_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit
      hπ hπ0 i
  comm' i := by
    rw [show (fun s : Fin n ⊕ Fin n ↦
          (MvPowerSeries.X s.swap : MvPowerSeries (Fin n ⊕ Fin n) O))
        = MvPowerSeries.X ∘ Sum.swap from rfl, ← MvPowerSeries.rename_eq_subst]
    exact rename_swap_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit
      hπ hπ0 i
  assoc' i := by
    have hL : assocLeftFam (FtauFold A a b hu hne hv hw hbez d)
        = Sum.elim
          (fun j ↦ MvPowerSeries.rename (Sum.map id Sum.inl)
            (FtauFold A a b hu hne hv hw hbez d j))
          (fun j ↦ (MvPowerSeries.X (Sum.inr (Sum.inr j)) :
            MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) O)) := by
      funext s
      cases s with
      | inl j =>
        rw [assocLeftFam, Sum.elim_inl, Sum.elim_inl, MvPowerSeries.rename_eq_subst]
        congr 1
        funext t
        cases t <;> rfl
      | inr j => rfl
    have hR : assocRightFam (FtauFold A a b hu hne hv hw hbez d)
        = Sum.elim
          (fun j ↦ (MvPowerSeries.X (Sum.inl j) :
            MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) O))
          (fun j ↦ MvPowerSeries.rename
            (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))
            (FtauFold A a b hu hne hv hw hbez d j)) := by
      funext s
      cases s with
      | inl j => rfl
      | inr j =>
        rw [assocRightFam, Sum.elim_inr, Sum.elim_inr, MvPowerSeries.rename_eq_subst]
        congr 1
        funext t
        cases t <;> rfl
    rw [hL, hR]
    exact FtauFold_assoc hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit hπ hπ0 i

variable {p e : ℕ} (hram : IsUniformizer π p e)

/-- **The fold form of `F_τ` over the fraction field**: `ChabautyColeman.ftauFoldFGL` base
changed along `O → Frac O`, which is the shape the disk analysis and the counting arguments
consume. Its uniformizer datum is the bundled `hram`, and its degree hypothesis `hfdeg'` is
already stated for the mapped polynomial, so no unpacking is needed at the use sites. -/
noncomputable def ftauFoldFGLFrac [CharZero (FractionRing O)]
    (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j)) :
    FormalGroupLaw (FractionRing O) (Fin n) :=
  have : CharZero O := (algebraMap O (FractionRing O)).charZero
  (ftauFoldFGL hu hne hv hw hbez hf ((hf.natDegree_map _).symm.trans hfdeg') hroot hcc ha hb hd
    hram.maximalIdeal_eq hram.ne_zero hsplit hunit).map (algebraMap O (FractionRing O))

/-- `ChabautyColeman.ftauFoldFGLFrac` is the base change of `ChabautyColeman.ftauFoldFGL`;
the two spellings of the uniformizer and of the degree hypothesis agree by proof irrelevance. -/
theorem ftauFoldFGLFrac_eq [CharZero (FractionRing O)]
    (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j)) :
    ftauFoldFGLFrac hu hne hv hw hbez hf hfdeg' hroot hcc ha hb hd hram hsplit hunit
      = (ftauFoldFGL hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hπ hπ0 hsplit hunit).map
        (algebraMap O (FractionRing O)) := rfl

end Assemble

end ChabautyColeman

end
