/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.CuspMirror
public import LeanPool.HyperellipticCurves.Log.Fold.FoldCorrect
public import LeanPool.HyperellipticCurves.Log.Fold.FoldUniversal

/-!
# The cusp instance of the numerator fold: `P_q ≠ 0`

The step (P) of the fold-witness route: the numerator fold run at the cuspidal inputs
`(tᵢ², tᵢ^N)` over the function field is the denominator-scaled witness chain of
`thm:cusp-witness`, so its step-condition numerators — and hence the cuspidal numerators
`ChabautyColeman.cuspNum` — are nonzero.

* `ChabautyColeman.isScaledState_foldBase_gen`: the interpolating numerator base is the
  scaled generic cuspidal base datum `(genU₀, genV₀)`.
* `ChabautyColeman.genFoldH_eq_foldGenH`: the witness's scalar sequence coincides with
  the computed division scalars of the honest fold chain — the doubling scalar is pinned
  to the tangent value by `ChabautyColeman.foldH_eq_of_dvd_double` via
  `ChabautyColeman.cuspStep_mumford`, and the later scalars agree by the chain
  identification `ChabautyColeman.cuspChain_eq_foldChain`.
* `ChabautyColeman.foldCondNum_cusp_ne_zero`: the step-condition numerators of the
  cuspidal fold are nonzero — `ChabautyColeman.foldCondNum_eq_den_mul` identifies each
  with the accumulated denominator times a disjointness value of the witness chain
  (`ChabautyColeman.exists_genCuspFold_witness`).
* `ChabautyColeman.cuspNum_ne_zero`: **`P_q ≠ 0`** — the cuspidal numerators of the
  condition quantities, mapped into the function field along the variable embedding, are
  the cuspidal fold's condition numerators; this is the nonvanishing hypothesis the
  descent (`ChabautyColeman.aeval_family_ne_zero`) consumes.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

variable {k : Type*} [Field k] {g : ℕ}

/-! ### The scaled base pack -/

/-- **The scaled base state of the cuspidal numerator fold** represents the generic
cuspidal base datum: the interpolating numerator base is the denominator-scaled honest
Mumford datum `(genU₀, genV₀)`. -/
theorem isScaledState_foldBase_gen :
    IsScaledState g (X ^ (2 * g + 1))
      (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1))
      (genU₀ k g) (genV₀ k g) := by
  have hinj : Function.Injective fun i : Fin g ↦ genNode k i ^ 2 := genNode_sq_injective
  have hnd : nodeDen (fun i : Fin g ↦ genNode k i ^ 2) ≠ 0 := nodeDen_ne_zero hinj
  have hint : Polynomial.C (nodeDen fun i : Fin g ↦ genNode k i ^ 2)
      * tupleV (fun i : Fin g ↦ genNode k i ^ 2) (fun i ↦ genNode k i ^ (2 * g + 1))
      = tupleInterp (fun i : Fin g ↦ genNode k i ^ 2) fun i ↦ genNode k i ^ (2 * g + 1) := by
    rw [tupleV, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hnd, map_one, one_mul]
  have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
    isCuspState_base genNode_sq_injective
  refine ⟨hbase.toFoldState, pow_ne_zero 2 hnd, rfl, ?_, ?_⟩
  · change Polynomial.C (nodeDen _) * tupleInterp _ _ = Polynomial.C (nodeDen _ ^ 2) * _
    rw [genV₀, ← hint, ← mul_assoc, ← map_mul, ← sq]
  · change tupleWNum _ _ _
      = Polynomial.C (nodeDen (fun i : Fin g ↦ genNode k i ^ 2) ^ 2)
        * cantorCofactor (X ^ (2 * g + 1)) (genU₀ k g) (genV₀ k g)
    have hdvd : genU₀ k g ∣ genV₀ k g ^ 2 - X ^ (2 * g + 1) := hbase.dvd_sq
    have hspec := cantorCofactor_spec (X ^ (2 * g + 1)) (monic_tupleU _) (by
      rw [genU₀, genV₀] at hdvd
      exact hdvd)
    rw [tupleWNum, genU₀, genV₀]
    refine divByMonic_eq_of_eq_add (monic_tupleU _) (r := 0) ?_ ?_
    · simp only [map_pow]
      rw [← hint]
      linear_combination (Polynomial.C (nodeDen fun i : Fin g ↦ genNode k i ^ 2)) ^ 2
        * hspec
    · rw [degree_zero]
      exact bot_lt_iff_ne_bot.mpr fun h ↦
        (monic_tupleU _).ne_zero (degree_eq_bot.mp h)

/-! ### Identification of the witness scalars with the computed scalars -/

variable {H₀ : FractionRing (MvPolynomial ℕ k)}

/-- **The witness scalars are the computed generic scalars**: given the doubling
condition at stage `0`, the scalar sequence of the generic full cuspidal fold coincides
with the field-division scalars of the honest fold chain. -/
theorem genFoldH_eq_foldGenH [NeZero (2 : k)] (hg : 0 < g)
    (hok0 : (genCuspFold k g H₀ 0).2.2 * (X - Polynomial.C (foldNodes g (genNode k) 0))
      ∣ X ^ (2 * g + 1) - ((genCuspFold k g H₀ 0).2.1
        + Polynomial.C (genFoldH k g H₀ 0) * (genCuspFold k g H₀ 0).1).comp (X ^ 2))
    (j : ℕ) :
    genFoldH k g H₀ j
      = foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
        (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g) (genV₀ k g) j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases j with _ | j
    · -- stage 0: the doubling scalar is pinned to the tangent value
      have hT0 : foldNodes g (genNode k) 0 = genNode k 0 := foldNodes_of_lt hg
      have hH0 : genFoldH k g H₀ 0 = H₀ := cuspGenH_zero
      have hbase : IsCuspState g (genU₀ k g) (genV₀ k g) (genA₀ k g) :=
        isCuspState_base genNode_sq_injective
      have hMum := cuspStep_mumford hbase (hH0 ▸ hok0)
      rw [foldGenH_zero, hH0]
      refine foldH_eq_of_dvd_double ?_ ?_ ?_ two_ne_zero_fractionRing ?_ ?_
      · rw [hT0]
        exact eval_tupleU_self (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩
      · rw [hT0]
        exact eval_tupleV genNode_sq_injective ⟨0, hg⟩
      · exact pow_ne_zero _ (by rw [hT0]; exact genNode_ne_zero 0)
      · have h : (tupleU fun i : Fin g ↦ genNode k i ^ 2).derivative.eval (genNode k 0 ^ 2)
            = nodeDiff (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩ :=
          derivative_tupleU_eval (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩
        rw [hT0, genU₀, h]
        exact nodeDiff_ne_zero genNode_sq_injective ⟨0, hg⟩
      · exact hMum
    · -- later stages: both scalars are the division values of the identified chains
      have hch : cuspChain g (genU₀ k g) (genV₀ k g) (genA₀ k g)
            (foldNodes g (genNode k)) (genFoldH k g H₀) (j + 1)
          = ((foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
              (foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
                (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g)
                (genV₀ k g)) (genU₀ k g) (genV₀ k g) (j + 1)).1,
            (foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
              (foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
                (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g)
                (genV₀ k g)) (genU₀ k g) (genV₀ k g) (j + 1)).2,
            (cuspChain g (genU₀ k g) (genV₀ k g) (genA₀ k g)
              (foldNodes g (genNode k)) (genFoldH k g H₀) (j + 1)).2.2) := by
        have h1 := cuspChain_eq_foldChain (U₀ := genU₀ k g) (V₀ := genV₀ k g)
          (H := genFoldH k g H₀) g (genA₀ k g) (foldNodes g (genNode k)) (j + 1)
        have h2 : foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
            (genFoldH k g H₀) (genU₀ k g) (genV₀ k g) (j + 1)
            = foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
              (foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
                (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g)
                (genV₀ k g)) (genU₀ k g) (genV₀ k g) (j + 1) :=
          foldChain_congr_H fun i hi ↦ ih i hi
        have hu := congrArg Prod.fst h1
        have hv := congrArg Prod.snd h1
        rw [h2] at hu hv
        exact Prod.ext hu (Prod.ext hv rfl)
      have hgs : genFoldH k g H₀ (j + 1)
          = (foldNodes g (genNode k) (j + 1) ^ (2 * g + 1)
              - (cuspChain g (genU₀ k g) (genV₀ k g) (genA₀ k g)
                (foldNodes g (genNode k)) (genFoldH k g H₀) (j + 1)).2.1.eval
                  (foldNodes g (genNode k) (j + 1) ^ 2))
            / (cuspChain g (genU₀ k g) (genV₀ k g) (genA₀ k g)
                (foldNodes g (genNode k)) (genFoldH k g H₀) (j + 1)).1.eval
                  (foldNodes g (genNode k) (j + 1) ^ 2) := cuspGenH_succ j
      rw [hgs, foldGenH_succ, hch]

/-! ### The cuspidal step-condition numerators are nonzero -/

/-- **The step-condition numerators of the cuspidal numerator fold are nonzero**:
correctness identifies each with the accumulated denominator times the honest condition
value of the witness chain. -/
theorem foldCondNum_cusp_ne_zero [NeZero (2 : k)] (hg2 : 2 ≤ g) {j : ℕ} (hj : j < 2 * g) :
    foldCondNum (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
      (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1))
      (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1)) j ≠ 0 := by
  have hg : 0 < g := by lia
  obtain ⟨H₀, hwit⟩ := exists_genCuspFold_witness (k := k) hg2
  have hH := genFoldH_eq_foldGenH hg ((hwit 0 (by lia)).2.2.1 (by lia))
  have hT0 : foldNodes g (genNode k) 0 = genNode k 0 := foldNodes_of_lt hg
  have hbaseS := isScaledState_foldBase_gen (k := k) (g := g)
  have hcurve : ∀ i, (foldNodes g (genNode k) i ^ (2 * g + 1)) ^ 2
      = (X ^ (2 * g + 1) : (FractionRing (MvPolynomial ℕ k))[X]).eval
        (foldNodes g (genNode k) i ^ 2) := fun i ↦ by
    rw [eval_pow, eval_X, ← pow_mul, ← pow_mul, mul_comm (2 * g + 1) 2]
  have hx₀ : (genU₀ k g).eval (foldNodes g (genNode k) 0 ^ 2) = 0 := by
    rw [hT0]
    exact eval_tupleU_self (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩
  have hV₀ : (genV₀ k g).eval (foldNodes g (genNode k) 0 ^ 2)
      = foldNodes g (genNode k) 0 ^ (2 * g + 1) := by
    rw [hT0]
    exact eval_tupleV genNode_sq_injective ⟨0, hg⟩
  have main : ∀ j, j < 2 * g → foldCondNum (X ^ (2 * g + 1))
      (fun i ↦ foldNodes g (genNode k) i ^ 2)
      (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1))
      (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1)) j ≠ 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjlt
      have hc : ∀ i < j, foldCondNum (X ^ (2 * g + 1))
          (fun i ↦ foldNodes g (genNode k) i ^ 2)
          (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1))
          (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
            fun i ↦ genNode k i ^ (2 * g + 1)) i ≠ 0 := fun i hi ↦ ih i hi (by lia)
      rw [foldCondNum_eq_den_mul (monic_X_pow _) (natDegree_X_pow _) hbaseS hx₀ hV₀
        (fun i _ ↦ hcurve i) hc]
      refine mul_ne_zero ?_ ?_
      · rw [den_foldNum]
        exact mul_ne_zero hbaseS.den_ne (Finset.prod_ne_zero_iff.mpr fun i hi ↦
          pow_ne_zero _ (hc i (Finset.mem_range.mp hi)))
      · rcases j with _ | j
        · rw [foldCond_zero]
          refine mul_ne_zero (mul_ne_zero two_ne_zero_fractionRing
            (pow_ne_zero _ (by rw [hT0]; exact genNode_ne_zero 0))) ?_
          have h : (tupleU fun i : Fin g ↦ genNode k i ^ 2).derivative.eval
              (genNode k 0 ^ 2) = nodeDiff (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩ :=
            derivative_tupleU_eval (fun i : Fin g ↦ genNode k i ^ 2) ⟨0, hg⟩
          rw [hT0, genU₀, h]
          exact nodeDiff_ne_zero genNode_sq_injective ⟨0, hg⟩
        · rw [foldCond_succ]
          have h1 := cuspChain_eq_foldChain (U₀ := genU₀ k g) (V₀ := genV₀ k g)
            (H := genFoldH k g H₀) g (genA₀ k g) (foldNodes g (genNode k)) (j + 1)
          have h2 : foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
              (genFoldH k g H₀) (genU₀ k g) (genV₀ k g) (j + 1)
              = foldChain (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
                (foldGenH (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
                  (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1)) (genU₀ k g)
                  (genV₀ k g)) (genU₀ k g) (genV₀ k g) (j + 1) :=
            foldChain_congr_H fun i _ ↦ hH i
          have hu := congrArg Prod.fst h1
          rw [h2] at hu
          rw [← hu]
          exact (hwit (j + 1) (by lia)).2.2.2 (by lia) (by lia)
  exact main j hj

/-! ### The cuspidal numerators are nonzero -/

/-- **`P_q ≠ 0`**: the cuspidal numerators of the condition quantities of the `2g`-step
fold are nonzero — `thm:cusp-witness` in the numerator currency consumed by the descent
(`ChabautyColeman.aeval_family_ne_zero`). -/
theorem cuspNum_ne_zero [NeZero (2 : k)] (hg2 : 2 ≤ g) {j : ℕ} (hj : j < 2 * g) :
    cuspNum k g j ≠ 0 := by
  have hg : 0 < g := by lia
  set φP : MvPolynomial (Fin g) k →+* FractionRing (MvPolynomial ℕ k) :=
    (algebraMap (MvPolynomial ℕ k) (FractionRing (MvPolynomial ℕ k))).comp
      (MvPolynomial.rename (Fin.val : Fin g → ℕ)).toRingHom with hφdef
  have hφX : ∀ i : Fin g, φP (MvPolynomial.X i) = genNode k i := fun i ↦ by
    rw [hφdef]
    simp [genNode]
  have hfmap : ((X : (MvPolynomial (Fin g) k)[X]) ^ (2 * g + 1)).map φP
      = X ^ (2 * g + 1) := by
    rw [Polynomial.map_pow, Polynomial.map_X]
  have hbaseB : (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ MvPolynomial.X i ^ 2)
        fun i ↦ MvPolynomial.X i ^ (2 * g + 1)).map φP
      = foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1) := by
    rw [map_foldBase, hfmap]
    congr 1
    · funext i
      rw [map_pow, hφX]
    · funext i
      rw [map_pow, hφX]
  intro h0
  have hmap := congrArg φP (cuspNum_eq_foldCondNum (K := k) (g := g) j)
  rw [h0, map_zero, map_foldCondNum, hfmap, hbaseB] at hmap
  have hchain : foldCondNum (X ^ (2 * g + 1))
      (fun i ↦ φP (if h : i < g then MvPolynomial.X (⟨i, h⟩ : Fin g) ^ 2
        else if h' : i - g < g then MvPolynomial.X (Fin.rev ⟨i - g, h'⟩ : Fin g) ^ 2
        else 0))
      (fun i ↦ φP (if h : i < g then MvPolynomial.X (⟨i, h⟩ : Fin g) ^ (2 * g + 1)
        else if h' : i - g < g
          then -MvPolynomial.X (Fin.rev ⟨i - g, h'⟩ : Fin g) ^ (2 * g + 1)
        else 0))
      (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
        fun i ↦ genNode k i ^ (2 * g + 1)) j
      = foldCondNum (X ^ (2 * g + 1)) (fun i ↦ foldNodes g (genNode k) i ^ 2)
        (fun i ↦ foldNodes g (genNode k) i ^ (2 * g + 1))
        (foldBase (X ^ (2 * g + 1)) (fun i : Fin g ↦ genNode k i ^ 2)
          fun i ↦ genNode k i ^ (2 * g + 1)) j := by
    refine foldCondNum_congr (fun i hi ↦ ?_) fun i hi ↦ ?_
    · rcases Nat.lt_or_ge i g with hig | hig
      · rw [dite_eq_left hig, map_pow, hφX, foldNodes_of_lt hig]
      · rw [dite_eq_right (by lia), dite_eq_left (show i - g < g by lia), map_pow, hφX,
          foldNodes, ite_eq_right (by lia), neg_sq, Fin.val_rev, Fin.val_mk,
          show g - (i - g + 1) = g - 1 - (i - g) by lia]
    · rcases Nat.lt_or_ge i g with hig | hig
      · rw [dite_eq_left hig, map_pow, hφX, foldNodes_of_lt hig]
      · rw [dite_eq_right (by lia), dite_eq_left (show i - g < g by lia), map_neg, map_pow, hφX,
          foldNodes, ite_eq_right (by lia), Odd.neg_pow ⟨g, by ring⟩, Fin.val_rev,
          Fin.val_mk, show g - (i - g + 1) = g - 1 - (i - g) by lia]
  rw [hchain] at hmap
  exact foldCondNum_cusp_ne_zero hg2 hj hmap.symm

end ChabautyColeman

end
