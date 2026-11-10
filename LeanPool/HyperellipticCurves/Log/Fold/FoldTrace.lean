/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FtauFold
public import LeanPool.HyperellipticCurves.Log.Trace.TraceFtau

/-!
# The trace form along the fold pipeline

The invariance identity of the trace form along the point-by-point fold pipeline of `F_τ`.

The pipeline half (`ChabautyColeman.traceDiff_foldPipe`) runs the trace-form differential
along the fold: each composition step adds the added point's contribution
(`ChabautyColeman.traceDiff_cantorCompose`) and each `(-1)`-reduction preserves the
functional (`ChabautyColeman.traceDiff_cantorReduce`, with the reduction certificate from
`ChabautyColeman.foldPipeStep_cofactor_lc`); the certificates at the intermediate states
come from the fold avoidance `ChabautyColeman.IsFoldAvoid`.

At the fold-`F_τ` configuration (`ChabautyColeman.sum_traceMat_ftauFoldPipe`) the
`X`-side chart start and the constant involuted `τ`-points contribute nothing, and the
moving points aggregate back to the `k`-th column of the `Y`-side chart block's trace
matrix: the `Y`-side chart splits into the linear factors at the moving points
(`ChabautyColeman.ftauUY_eq_prod`), so the aggregation is the split-datum sum formula
`ChabautyColeman.traceDiff_prod` — with the *same* per-point certificates
`C (sY.eval (A j))` on both sides, since the trace-form differential never reads the
`v`-part a certificate was stated against.

The script `prototype/tracefold.m` checks numerically at `g = 2, 3` that the invariance
identity, the aggregation over the moving points, and the per-step conservation hold on a
truncated power-series model.

The file also holds the avoidance descent: fold avoidance descends stage by stage along any base
change reflecting coprimality (`ChabautyColeman.isFoldAvoid_of_map`), so at the fold-`F_τ`
configuration it is a residue-field condition on the centre fold
(`ChabautyColeman.isFtauFoldAvoid_of_center`).

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Pipe

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] (d : Derivation S R R)
  [Nontrivial R] [NoZeroDivisors R]
  {f U₀ V₀ : R[X]} {xs ys : ℕ → R} {ds : ℕ → FoldTriple R} {g k : ℕ}
  {cy sy : ℕ → R[X]} {cu₀ s₀ cuP sP : R[X]}

/-- **The trace-form differential along the fold pipeline** (the pipeline half of the invariance
identity at the fold shape, the counterpart of `ChabautyColeman.traceDiff_cantorPipeline`): each
composition step adds the added point's contribution and each `(-1)`-reduction preserves the
functional, so the output's differential is the start's plus the sum over the added points. -/
theorem traceDiff_foldPipe (hf : f.Monic) (hfdeg : f.natDegree = 2 * g + 1)
    (h₀ : IsFoldState g f U₀ V₀) {m : ℕ}
    (hbez : ∀ j < m, (ds j).s₁ * (foldPipe f xs ys ds U₀ V₀ j).1
      + (ds j).s₂ * (X - C (xs j))
      + (ds j).s₃ * ((foldPipe f xs ys ds U₀ V₀ j).2 + C (ys j)) = 1)
    (hcv : ∀ j < m, ys j ^ 2 = f.eval (xs j))
    (hav : ∀ j ≤ m, IsCoprime (foldPipe f xs ys ds U₀ V₀ j).1
      (2 * (foldPipe f xs ys ds U₀ V₀ j).2))
    (hpt : ∀ j < m, cy j * (X - C (xs j)) + sy j * (2 * C (ys j)) = 1)
    (hfc : ∀ i, d (f.coeff i) = 0) (hk : k < g)
    (hs₀ : cu₀ * U₀ + s₀ * (2 * V₀) = 1)
    (hsP : cuP * (foldPipe f xs ys ds U₀ V₀ m).1
      + sP * (2 * (foldPipe f xs ys ds U₀ V₀ m).2) = 1) :
    traceDiff d (foldPipe f xs ys ds U₀ V₀ m).1 sP k
      = traceDiff d U₀ s₀ k
        + ∑ j ∈ Finset.range m, traceDiff d (X - C (xs j)) (sy j) k := by
  induction m generalizing cuP sP with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, add_zero]
    exact traceDiff_congr d h₀.monicU hsP hs₀ k
  | succ m ih =>
    have hstate := isFoldState_foldPipe (m := m) hf hfdeg h₀
      (fun j hj ↦ hbez j (by lia)) fun j hj ↦ hcv j (by lia)
    have hSdvd := hstate.dvd_sq
    have hPdvd := X_sub_C_dvd_of_sq_eq (f := f) (hcv m (by lia))
    obtain ⟨cS, sS, hsS⟩ := hav m (by lia)
    obtain ⟨cC, sC, hsC⟩ := isCoprime_cantorCompose (hbez m (by lia)) hSdvd hPdvd
      (hav m (by lia)) ⟨cy m, sy m, hpt m (by lia)⟩
    have hqm : (cantorCompose f (foldPipe f xs ys ds U₀ V₀ m).1
        (foldPipe f xs ys ds U₀ V₀ m).2 (X - C (xs m)) (C (ys m))
        (ds m).s₁ (ds m).s₂ (ds m).s₃).1.Monic :=
      cantorCompose_monic f hstate.monicU (monic_X_sub_C (xs m))
    have hqdvd := cantorCompose_dvd f (hbez m (by lia)) hSdvd hPdvd
    obtain ⟨hc, -⟩ := foldPipeStep_cofactor_lc hf hfdeg hstate (hbez m (by lia))
      (hcv m (by lia))
    have hred := traceDiff_cantorReduce d hqm hqdvd hc hfc hfdeg hk hsC hsP
    have hcomp := traceDiff_cantorCompose d hstate.monicU (monic_X_sub_C (xs m))
      (hbez m (by lia)) hSdvd hPdvd hsS (hpt m (by lia)) hsC k
    rw [Finset.sum_range_succ, ← add_assoc,
      ← ih (fun j hj ↦ hbez j (by lia)) (fun j hj ↦ hcv j (by lia))
        (fun j hj ↦ hav j (by lia)) (fun j hj ↦ hpt j (by lia)) hsS]
    exact hred.trans hcomp

end Pipe

section Descent

variable {R A : Type*} [CommRing R] [CommRing A] [Nontrivial R] {φ : R →+* A}
  {f U₀ V₀ : R[X]} {xs ys : ℕ → R} {n g : ℕ} {d : FoldCertData R n}

/-- **Fold avoidance descends along a base change that reflects coprimality**, stage by stage: the
stage coprimalities are conditions on the image configuration. -/
theorem isFoldAvoid_of_map (hrefl : ReflectsCoprime φ) (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * g + 1) (h₀ : IsFoldState g f U₀ V₀)
    (hcv : ∀ j < 2 * n, ys j ^ 2 = f.eval (xs j))
    (hd : IsFoldCerts f xs ys U₀ V₀ d)
    (hav : IsFoldAvoid (f.map φ) (fun j ↦ φ (xs j)) (fun j ↦ φ (ys j)) (U₀.map φ)
      (V₀.map φ) (d.map φ)) :
    IsFoldAvoid f xs ys U₀ V₀ d := by
  intro j hj
  have hstate := isFoldState_foldPipe (m := j) hf hfdeg h₀
    (fun i hi ↦ hd.bezout (by lia)) fun i hi ↦ hcv i (by lia)
  have hpipe := map_foldPipe (m := j) φ hf hfdeg h₀
    (fun i hi ↦ hd.bezout (by lia)) fun i hi ↦ hcv i (by lia)
  have h := hav j hj
  rw [FoldCertData.seq_map] at h
  have h1 := congrArg Prod.fst hpipe
  have h2 := congrArg Prod.snd hpipe
  dsimp only at h1 h2
  rw [← h1, ← h2] at h
  refine hrefl _ _ hstate.monicU ?_
  rwa [Polynomial.map_mul, Polynomial.map_ofNat]

end Descent

section Ftau

variable {O : Type*} [CommRing O] [Nontrivial O] [NoZeroDivisors O] {n : ℕ}
  {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}

/-- **The invariance identity for the trace form, at the fold pipeline**: running the
trace-form differential for `∂/∂Y_k` along the fold, the `X`-side start and the constant involuted
`τ`-points contribute nothing, and the moving points aggregate to the `k`-th column of the `Y`-side
chart block's trace matrix, so

`∑_j C_ij(F(X,Y))·∂F_j/∂Y_k = C_ik(Y)`.

Specializing at `Y = 0`, where `∂F/∂Y(X,0)` is the differential matrix `M(X)`, turns
this into `C(X)M(X) = C(0)`. -/
theorem sum_traceMat_ftauFoldPipe (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    (hav : IsFtauFoldAvoid A a b hu hne hv hw hbez d)
    (k : Fin n) {i : ℕ} (hi : i < n)
    {cY sY cP sP : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)}
    (hsY : cY * ftauUY u n + sY * (2 * ftauVY hu hne hv hw hbez) = 1)
    (hsP : cP * (ftauFoldPipe A a b hu hne hv hw hbez d).1
      + sP * (2 * (ftauFoldPipe A a b hu hne hv hw hbez d).2) = 1) :
    ∑ j : Fin n, traceMat (ftauFoldPipe A a b hu hne hv hw hbez d).1 sP i j
        * MvPowerSeries.pderiv (Sum.inr k) (FtauFold A a b hu hne hv hw hbez d j)
      = traceMat (ftauUY u n) sY i k := by
  classical
  -- `sY` evaluated at a moving point inverts twice the chart square root's value there
  have hyval (j : Fin n) : sY.eval (A j)
      * (2 * (ftauVY hu hne hv hw hbez).eval (A j)) = 1 := by
    have h := congrArg (Polynomial.eval (A j)) hsY
    simpa [hroot j] using h
  -- the residue Bézout value at the `τ`-roots
  have hbval (m : Fin n) : c₂.eval (a m) * (2 * b m) = 1 := by
    have h := congrArg (Polynomial.eval (a m)) hbez
    simpa [ha m, hb m] using h
  -- the phase-1 point-block certificates
  have hcert1 (j : Fin n) : (0 : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O))
      * (X - C (A j))
      + C (sY.eval (A j)) * (2 * C ((ftauVY hu hne hv hw hbez).eval (A j))) = 1 := by
    rw [zero_mul, zero_add, ← map_ofNat (C : MvPowerSeries (Fin n ⊕ Fin n) O →+* _) 2,
      ← map_mul, ← map_mul, hyval j, map_one]
  -- the certificate family of the fold's point blocks
  have hpt : ∀ j < 2 * n, (0 : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O))
      * (X - C (ftauFoldXs A a j))
      + phaseSeq (fun j ↦ C (sY.eval (A j)))
          (fun m ↦ -C (MvPowerSeries.C (c₂.eval (a m)))) j
        * (2 * C (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j)) = 1 := by
    intro j hj
    rcases lt_or_ge j n with h1 | h1
    · rw [ftauFoldXs, ftauFoldYs, phaseSeq_of_lt _ _ h1, phaseSeq_of_lt _ _ h1,
        phaseSeq_of_lt _ _ h1]
      exact hcert1 ⟨j, h1⟩
    · have h2 : j - n < n := by lia
      rw [ftauFoldXs, ftauFoldYs, phaseSeq_of_ge _ _ h1 h2, phaseSeq_of_ge _ _ h1 h2,
        phaseSeq_of_ge _ _ h1 h2, zero_mul, zero_add]
      have h : (C (MvPowerSeries.C (c₂.eval (a (Fin.rev ⟨j - n, h2⟩))))
            : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O))
          * (2 * C (MvPowerSeries.C (b (Fin.rev ⟨j - n, h2⟩)))) = 1 := by
        rw [← map_ofNat (C : MvPowerSeries (Fin n ⊕ Fin n) O →+* _) 2,
          ← map_ofNat (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O) 2,
          ← map_mul, ← map_mul, ← map_mul, ← map_mul, hbval (Fin.rev ⟨j - n, h2⟩), map_one,
          map_one]
      simp only [map_neg]
      linear_combination h
  -- the start certificate, from the avoidance at stage `0`
  obtain ⟨c₀, s₀, hs₀⟩ := hav 0 (by lia)
  -- the pipeline half: the trace-form differential along the fold
  rw [ftauFoldPipe_def] at hsP
  have key := traceDiff_foldPipe (ds := d.seq)
    (MvPowerSeries.pderiv (Sum.inr k)) (hf.map _)
    ((hf.natDegree_map _).trans hfdeg) (isFoldState_ftauUX hu hne hv hw hbez)
    (fun j hj ↦ hd.bezout hj)
    (fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb hj)
    hav hpt (pderiv_coeff_map_C_eq_zero k f) hi hs₀ hsP
  -- the start contributes nothing; split the point sum at the phase boundary
  rw [traceDiff_ftauUX_eq_zero k s₀ i, zero_add,
    show Finset.range (2 * n) = Finset.range (n + n) by rw [two_mul],
    Finset.sum_range_add] at key
  -- the constant involuted points contribute nothing
  have hzero : ∑ j ∈ Finset.range n,
      traceDiff (MvPowerSeries.pderiv (Sum.inr k))
        (X - C (ftauFoldXs A a (n + j)))
        (phaseSeq (fun j ↦ C (sY.eval (A j)))
          (fun m ↦ -C (MvPowerSeries.C (c₂.eval (a m)))) (n + j)) i = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    have hxc : X - C (ftauFoldXs A a (n + j))
        = (X - C (a (Fin.rev ⟨j, hj'⟩))).map
          (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O) := by
      rw [ftauFoldXs, phaseSeq_add _ _ hj']
      simp
    rw [hxc]
    exact traceDiff_eq_zero_of_dotDer_eq_zero _ (pderiv_coeff_map_C_eq_zero k _) _ _
  rw [hzero, add_zero] at key
  -- the moving points, as a sum over the component indices
  have hphase1 : ∑ j ∈ Finset.range n,
      traceDiff (MvPowerSeries.pderiv (Sum.inr k))
        (X - C (ftauFoldXs A a j))
        (phaseSeq (fun j ↦ C (sY.eval (A j)))
          (fun m ↦ -C (MvPowerSeries.C (c₂.eval (a m)))) j) i
      = ∑ j : Fin n, traceDiff (MvPowerSeries.pderiv (Sum.inr k))
          (X - C (A j)) (C (sY.eval (A j))) i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ftauFoldXs, phaseSeq_of_lt _ _ j.isLt, Fin.eta, phaseSeq_of_lt _ _ j.isLt, Fin.eta]
  rw [hphase1] at key
  -- the aggregation: the moving points reassemble the `Y`-side chart block
  have hagg : traceDiff (MvPowerSeries.pderiv (Sum.inr k)) (ftauUY u n) sY i
      = ∑ j : Fin n, traceDiff (MvPowerSeries.pderiv (Sum.inr k))
          (X - C (A j)) (C (sY.eval (A j))) i := by
    have hsu : cY * (∏ j : Fin n, (X - C (A j)))
        + sY * (2 * ftauVY hu hne hv hw hbez) = 1 := by
      rwa [← ftauUY_eq_prod hu hne hroot hcc hunit]
    rw [ftauUY_eq_prod hu hne hroot hcc hunit]
    exact traceDiff_prod _ hsu (fun j _ ↦ hcert1 j)
      (fun j _ ↦ X_sub_C_dvd_sub_C_eval) i
  rw [← hagg, traceDiff_ftauUY k sY i] at key
  -- unfold the output's differential along its chart shape
  rw [← ftauFoldPipe_def, traceDiff_eq_sum _ (pderiv_coeff_map_C_eq_zero k u)
    (ftauFoldPipe_fst_eq hu hne hv hw hbez hf hfdeg hroot ha hb hd) sP i] at key
  exact key

end Ftau

section FtauDescent

open IsLocalRing

variable {O : Type*} [CommRing O] [IsLocalRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}

/-- **Fold-`F_τ` Weierstrass avoidance is a residue-field condition**: it is fold avoidance for the
residue centre fold `τ_bar + τ_bar - τ_bar` at the residues of the `τ`-points. -/
theorem isFtauFoldAvoid_of_center (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (hav : IsFoldAvoid (f.map (residue O)) (foldXs fun i ↦ residue O (a i))
      (foldYs fun i ↦ residue O (b i)) (u.map (residue O)) (v.map (residue O))
      (d.map (mvSeriesResidue _ O))) :
    IsFtauFoldAvoid A a b hu hne hv hw hbez d := by
  refine isFoldAvoid_of_map (φ := mvSeriesResidue _ O)
    (reflectsCoprime_of_ker_le_jacobson (mvSeriesResidue_surjective _ O)
      (ker_mvSeriesResidue_le_jacobson _ O))
    (hf.map _) ((hf.natDegree_map _).trans hfdeg) (isFoldState_ftauUX hu hne hv hw hbez)
    (fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb hj) hd ?_
  have hmapφ (p : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) :
      p.map (mvSeriesResidue (Fin n ⊕ Fin n) O)
        = (p.map (MvPowerSeries.constantCoeff :
            MvPowerSeries (Fin n ⊕ Fin n) O →+* O)).map (residue O) :=
    (Polynomial.map_map _ _ p).symm
  have hU : (ftauUX u n).map (mvSeriesResidue (Fin n ⊕ Fin n) O)
      = u.map (residue O) := by
    rw [hmapφ, ftauUX_map_constantCoeff]
  have hV : (ftauVX hu hne hv hw hbez).map (mvSeriesResidue (Fin n ⊕ Fin n) O)
      = v.map (residue O) := by
    rw [hmapφ, ftauVX_map_constantCoeff]
  have hF : (f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map
      (mvSeriesResidue (Fin n ⊕ Fin n) O) = f.map (residue O) := by
    rw [hmapφ, map_C_map_constantCoeff]
  have hxs : (fun j ↦ mvSeriesResidue (Fin n ⊕ Fin n) O (ftauFoldXs A a j))
      = foldXs fun i ↦ residue O (a i) :=
    ftauFoldXs_map (fun _ ↦ rfl) hcc
  have hys : (fun j ↦ mvSeriesResidue (Fin n ⊕ Fin n) O
        (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))
      = foldYs fun i ↦ residue O (b i) :=
    ftauFoldYs_map hu hne hv hw hbez (fun _ ↦ rfl) hcc hb
  rwa [hxs, hys, hU, hV, hF]

end FtauDescent

end ChabautyColeman

end
