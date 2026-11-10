/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Fold.FoldClass
public import LeanPool.HyperellipticCurves.Log.Fold.FtauFold
public import LeanPool.HyperellipticCurves.Log.Ftau.FtauAssoc
public import LeanPool.HyperellipticCurves.Log.Ftau.FtauBasic

import LeanPool.HyperellipticCurves.ForMathlib.Units
import LeanPool.HyperellipticCurves.Series.Interpolation

/-!
# Basic identities of the fold form of the translated law

The centre value, pack-independence and group-law identities of the fold pipeline of `F_τ`, proved
pointwise by the field-level class engine of `LeanPool.HyperellipticCurves.Log.Fold.FoldClass` and
upgraded
to identities over the power-series ring by interpolation.

## Main statements

* `ChabautyColeman.ftauFoldPipe_constantCoeff_eq`: **the centre of the fold pipeline is the
  `τ`-datum** — at `X = Y = 0` the moving points degenerate onto the `τ`-points, the point block
  cancels pair by pair in the class group, and the pipeline returns `(u, v)` itself; hence the fold
  form of `F_τ` has no constant term (`ChabautyColeman.constantCoeff_FtauFold`).
* `ChabautyColeman.ftauFoldPipe_eq_of_certs`: **the fold pipeline is pack-independent** — at every
  point of the polydisk both evaluated outputs are the reduced representative of the same class,
  and interpolation upgrades pointwise agreement to an identity over the power-series ring; hence
  `ChabautyColeman.FtauFold_eq_of_certs`.
* `ChabautyColeman.ftauFoldPipe_map_setYZero`: **the unit law** — at `Y = 0` the moving points
  degenerate onto the `τ`-points (`ChabautyColeman.setYZero_eq_C_of_root`) and the pipeline returns
  the `X`-side chart datum; in group-law form `ChabautyColeman.setYZero_FtauFold`.
* The remaining group-law axioms: the evaluated pipeline is the chart at the evaluated coordinates
  (`ChabautyColeman.eval_ftauFoldPipe_eq`), the moving points assemble the `Y`-side chart class and
  the involuted `τ`-points the negated `τ`-class (`ChabautyColeman.prod_mk0_eval_points`), so the
  chart at `F_τ(x)` represents `ch(x_L) + ch(x_R) - τ` (`ChabautyColeman.mk0_chart_eval_fold`) —
  whence commutativity (`ChabautyColeman.rename_swap_FtauFold`), the symmetric unit law
  (`ChabautyColeman.setXZero_FtauFold`) and associativity (`ChabautyColeman.FtauFold_assoc`).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Center

variable {O : Type*} [CommRing O] [IsDomain O]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]

/-- **The centre of the fold pipeline is the `τ`-datum**: at `X = Y = 0` the pipeline folds `τ`'s
points onto the `X`-side chart's centre and returns `(u, v)` itself — by the class computation over
the fraction field (the moving points degenerate onto the `τ`-points, so the point block cancels
pair by pair) and uniqueness of reduced representatives. -/
theorem ftauFoldPipe_constantCoeff_eq (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d) :
    ((ftauFoldPipe A a b hu hne hv hw hbez d).1.map
          (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O),
      (ftauFoldPipe A a b hu hne hv hw hbez d).2.map
          (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O))
      = (u, v) := by
  rw [ftauFoldPipe_def]
  set K := FractionRing O
  set φK : MvPowerSeries (Fin n ⊕ Fin n) O →+* K := (algebraMap O K).comp
    (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O)
  have hmapφ (p : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) :
      p.map φK = (p.map (MvPowerSeries.constantCoeff :
        MvPowerSeries (Fin n ⊕ Fin n) O →+* O)).map (algebraMap O K) :=
    (Polynomial.map_map _ _ p).symm
  -- the pipeline hypotheses upstairs
  have hfC : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).Monic := hf.map _
  have hfCdeg : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).natDegree = 2 * n + 1 :=
    (hf.natDegree_map _).trans hfdeg
  have h₀ := isFoldState_ftauUX hu hne hv hw hbez
  have hcv := fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb (j := j) hj
  -- the pipeline and the pack under `φK`, at the collapsed centre configuration
  have hpipe := map_foldPipe (m := 2 * n) φK hfC hfCdeg h₀ (fun j hj ↦ hd.bezout hj) hcv
  have hdK := hd.map φK hfC hfCdeg h₀ hcv
  have hxs : (fun j ↦ φK (ftauFoldXs A a j)) = foldXs fun i ↦ algebraMap O K (a i) :=
    ftauFoldXs_map (fun _ ↦ rfl) hcc
  have hys : (fun j ↦ φK (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))
      = foldYs fun i ↦ algebraMap O K (b i) :=
    ftauFoldYs_map hu hne hv hw hbez (fun _ ↦ rfl) hcc hb
  have hU : (ftauUX u n).map φK = u.map (algebraMap O K) := by rw [hmapφ, ftauUX_map_constantCoeff]
  have hV : (ftauVX hu hne hv hw hbez).map φK = v.map (algebraMap O K) := by
    rw [hmapφ, ftauVX_map_constantCoeff]
  have hF : (f.map (MvPowerSeries.C :
        O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map φK = f.map (algebraMap O K) := by
    rw [hmapφ, map_C_map_constantCoeff]
  rw [hxs, hys, hU, hV, hF, ← FoldCertData.seq_map] at hpipe
  rw [hxs, hys, hU, hV, hF] at hdK
  -- the `K`-level pipeline collapses to the `τ`-datum
  have hself := fold_pipeline_eq_self (hf.map _) ((hf.natDegree_map _).trans hfdeg)
    ((isFoldState_of_datum hu hne hv hw).map (algebraMap O K))
    (fun i ↦ sq_eq_map_of_sq_eq _ (hb i ▸ eval_sq_eq_of_root hw (ha i)))
    fun j hj ↦ hdK.bezout hj
  have hfinal := hpipe.trans hself
  -- descend along the injective coefficient embedding
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hfinal
  dsimp only at h1 h2
  rw [hmapφ] at h1 h2
  have hinj := Polynomial.map_injective (algebraMap O K) (IsFractionRing.injective O K)
  exact Prod.ext (hinj h1) (hinj h2)

/-- The fold form of the translated group law has no constant term. -/
theorem constantCoeff_FtauFold (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d) (i : Fin n) :
    MvPowerSeries.constantCoeff (FtauFold A a b hu hne hv hw hbez d i) = 0 := by
  have h1 := congrArg Prod.fst
    (ftauFoldPipe_constantCoeff_eq hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd)
  dsimp only at h1
  have h2 : ((ftauFoldPipe A a b hu hne hv hw hbez d).1 - u.map MvPowerSeries.C).map
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n ⊕ Fin n) O →+* O) = 0 := by
    rw [Polynomial.map_sub, h1, map_C_map_constantCoeff, sub_self]
  have h3 := congrArg (fun q : O[X] ↦ q.coeff (i : ℕ)) h2
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h3
  exact h3

end Center

section PackIndep

open IsLocalRing

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

/-- **The fold pipeline is pack-independent**: two valid fold packs at the fold-`F_τ` configuration
produce the same pipeline output — at every point of the polydisk both evaluated outputs are the
reduced representative of the same class, and interpolation upgrades pointwise agreement to an
identity of polynomials over the power-series ring. -/
theorem ftauFoldPipe_eq_of_certs (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d e : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (he : IsFtauFoldCerts A a b hu hne hv hw hbez e)
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0) :
    ftauFoldPipe A a b hu hne hv hw hbez d = ftauFoldPipe A a b hu hne hv hw hbez e := by
  simp only [ftauFoldPipe_def]
  classical
  have hπu : ¬IsUnit π := fun hunit ↦ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    (Ideal.eq_top_of_isUnit_mem _ (hπ ▸ Ideal.mem_span_singleton_self π) hunit)
  have : Infinite O := Infinite.of_injective (π ^ ·)
    (pow_injective_of_not_isUnit hπu hπ0)
  set K := FractionRing O
  have hfC : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).Monic := hf.map _
  have hfCdeg : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).natDegree = 2 * n + 1 :=
    (hf.natDegree_map _).trans hfdeg
  have h₀ := isFoldState_ftauUX hu hne hv hw hbez
  have hcv := fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb (j := j) hj
  -- pointwise: both evaluated pipelines are the reduced representative of one class
  have key : ∀ (x : Fin n ⊕ Fin n → O) (hx : ∀ s, x s ∈ maximalIdeal O),
      ((foldPipe (f.map MvPowerSeries.C) (ftauFoldXs A a)
          (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) d.seq (ftauUX u n)
          (ftauVX hu hne hv hw hbez) (2 * n)).1.map
            ((algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx))),
        (foldPipe (f.map MvPowerSeries.C) (ftauFoldXs A a)
          (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) d.seq (ftauUX u n)
          (ftauVX hu hne hv hw hbez) (2 * n)).2.map
            ((algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx))))
      = ((foldPipe (f.map MvPowerSeries.C) (ftauFoldXs A a)
          (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) e.seq (ftauUX u n)
          (ftauVX hu hne hv hw hbez) (2 * n)).1.map
            ((algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx))),
        (foldPipe (f.map MvPowerSeries.C) (ftauFoldXs A a)
          (ftauFoldYs (ftauVY hu hne hv hw hbez) A b) e.seq (ftauUX u n)
          (ftauVX hu hne hv hw hbez) (2 * n)).2.map
            ((algebraMap O K).comp
              (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)))) := by
    intro x hx
    set ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* K :=
      (algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx))
      with hψdef
    have hψC : ψ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
        = algebraMap O K :=
      hψdef ▸ MvPSeries.comp_evalRingHom_comp_C _ _
    have hF : (f.map (MvPowerSeries.C :
          O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map ψ = f.map (algebraMap O K) := by
      rw [Polynomial.map_map, hψC]
    -- the two image pipelines and packs over `K`
    have hpiped := map_foldPipe (m := 2 * n) ψ hfC hfCdeg h₀ (fun j hj ↦ hd.bezout hj) hcv
    have hpipee := map_foldPipe (m := 2 * n) ψ hfC hfCdeg h₀ (fun j hj ↦ he.bezout hj) hcv
    have hdK := hd.map ψ hfC hfCdeg h₀ hcv
    have heK := he.map ψ hfC hfCdeg h₀ hcv
    rw [← FoldCertData.seq_map] at hpiped hpipee
    rw [hF] at hpiped hpipee hdK heK
    have h₀K := h₀.map ψ
    rw [hF] at h₀K
    have hcvK : ∀ j < 2 * n,
        ψ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j) ^ 2
          = (f.map (algebraMap O K)).eval (ψ (ftauFoldXs A a j)) := by
      intro j hj
      have h := sq_eq_map_of_sq_eq ψ (hcv j hj)
      rwa [hF] at h
    -- both image pipelines compute the same class
    have heq := fold_pipeline_eq_of_mk0_eq (hf.map (algebraMap O K))
      ((hf.natDegree_map _).trans hfdeg) h₀K h₀K
      (fun j hj ↦ hdK.bezout hj) hcvK (fun j hj ↦ heK.bezout hj) hcvK rfl
    exact hpiped.trans (heq.trans hpipee.symm)
  refine Prod.ext ?_ ?_
  · exact MvPSeries.polynomial_eq_of_forall_eval_eq hπ hπ0 fun x hx ↦
      congrArg Prod.fst (key x hx)
  · exact MvPSeries.polynomial_eq_of_forall_eval_eq hπ hπ0 fun x hx ↦
      congrArg Prod.snd (key x hx)

/-- **Pack-independence of the fold form of the translated law**: the coordinates of `F_τ` do not
depend on the choice of valid fold pack. -/
theorem FtauFold_eq_of_certs (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
    {d e : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    (he : IsFtauFoldCerts A a b hu hne hv hw hbez e)
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0) :
    FtauFold A a b hu hne hv hw hbez d = FtauFold A a b hu hne hv hw hbez e := by
  funext i
  exact congrArg
    (fun p : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)
        × Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O) ↦
      (p.1 - u.map MvPowerSeries.C).coeff (i : ℕ))
    (ftauFoldPipe_eq_of_certs hu hne hv hw hbez hf hfdeg hroot ha hb hd he hπ hπ0)

end PackIndep

section Degeneration

variable {O : Type*} [CommRing O] [IsDomain O] {n : ℕ} {u : O[X]} {a : Fin n → O}

/-- **The moving points degenerate onto the `τ`-points at `Y = 0`**: when `u` splits
with pairwise distinct roots, the `Y = 0` specialization of a root of the `Y`-side chart
is the constant series at the `τ`-root marked by its constant coefficient. -/
theorem setYZero_eq_C_of_root (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hainj : Function.Injective a) {P : MvPowerSeries (Fin n ⊕ Fin n) O} {j : Fin n}
    (hP : (ftauUY u n).eval P = 0) (hccP : MvPowerSeries.constantCoeff P = a j) :
    setYZero P = MvPowerSeries.C (a j) := by
  -- the specialization is a root of the split `u`
  have h0 : (u.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)).eval
      (setYZero P) = 0 := by
    have h := congrArg setYZero hP
    rwa [map_zero, ← Polynomial.eval_map_apply, ftauUY_map_setYZero] at h
  rw [hsplit] at h0
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, map_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    at h0
  obtain ⟨m, -, hm⟩ := Finset.prod_eq_zero_iff.mp h0
  have hm' : setYZero P = MvPowerSeries.C (a m) := sub_eq_zero.mp hm
  -- pin the root by the constant coefficient
  have h := congrArg MvPowerSeries.constantCoeff hm'
  rw [constantCoeff_setYZero, hccP, MvPowerSeries.constantCoeff_C] at h
  rw [hm', hainj h]

end Degeneration

section UnitLaw

open IsLocalRing

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

/-- The pointwise form of `ChabautyColeman.ftauFoldPipe_map_setYZero`: at a point `z` of the
polydisk, the fold pipeline with `Y = 0`, evaluated at `z` over `Frac O`, is the evaluated
chart — the `K`-level pipeline starts at a fold state, so it collapses to that state. -/
private theorem map_evalRingHom_ftauFoldPipe_map_setYZero (hf : f.Monic)
    (hfdeg : f.natDegree = 2 * n + 1) (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hainj : Function.Injective a) (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i) (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    {z : Fin n → O} (hz : ∀ s, z s ∈ maximalIdeal O) :
    (((ftauFoldPipe A a b hu hne hv hw hbez d).1.map
        (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)).map
          ((algebraMap O (FractionRing O)).comp
            (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))),
      ((ftauFoldPipe A a b hu hne hv hw hbez d).2.map
        (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)).map
          ((algebraMap O (FractionRing O)).comp
            (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))))
    = ((chartU u n).map ((algebraMap O (FractionRing O)).comp
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))),
        (chartV hu hne.ge hv hw hbez).map ((algebraMap O (FractionRing O)).comp
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz)))) := by
  classical
  set K := FractionRing O
  have ha : ∀ i, u.eval (a i) = 0 := fun i ↦ by
    rw [hsplit, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hfC : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).Monic := hf.map _
  have hfCdeg : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).natDegree = 2 * n + 1 :=
    (hf.natDegree_map _).trans hfdeg
  have h₀ := isFoldState_ftauUX hu hne hv hw hbez
  have hcv := fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb (j := j) hj
  set φO : MvPowerSeries (Fin n) O →+* K :=
    (algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))
    with hφOdef
  set ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* K := φO.comp setYZero with hψdef
  have hfuse (p : Polynomial (MvPowerSeries (Fin n ⊕ Fin n) O)) :
      (p.map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+*
        MvPowerSeries (Fin n) O)).map φO = p.map ψ := by
    rw [Polynomial.map_map, hψdef]
  have hφOC : φO.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O) = algebraMap O K :=
    hφOdef ▸ MvPSeries.comp_evalRingHom_comp_C _ _
  have hψC : ψ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O K := by
    rw [hψdef, RingHom.comp_assoc, setYZero_comp_C, hφOC]
  -- the point sequences degenerate onto the mirrored `τ`-points
  have hAj (i : Fin n) : ψ (A i) = algebraMap O K (a i) := by
    rw [hψdef, RingHom.comp_apply,
      setYZero_eq_C_of_root hsplit hainj (hroot i) (hcc i), ← RingHom.comp_apply, hφOC]
  have hxs : (fun j ↦ ψ (ftauFoldXs A a j)) = foldXs fun i ↦ algebraMap O K (a i) :=
    ftauFoldXs_map_of_eq (funext hAj) (funext fun i ↦ (RingHom.congr_fun hψC (a i) :))
  have hys : (fun j ↦ ψ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))
      = foldYs fun i ↦ algebraMap O K (b i) :=
    ftauFoldYs_map_of_eq
      (funext fun i ↦ by
        rw [hψdef, RingHom.comp_apply, ← Polynomial.eval_map_apply, ftauVY_map_setYZero,
          setYZero_eq_C_of_root hsplit hainj (hroot i) (hcc i), Polynomial.eval_map_apply,
          hb i, ← RingHom.comp_apply, hφOC])
      (funext fun i ↦ by rw [map_neg, ← RingHom.comp_apply, hψC]; rfl)
  -- the chart data evaluate through `ψ` to the evaluated chart
  have hcomp : ψ.comp
      (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom = φO := by
    rw [hψdef, RingHom.comp_assoc, setYZero_comp_rename_inl, RingHom.comp_id]
  have hUX : (ftauUX u n).map ψ = (chartU u n).map φO := by rw [ftauUX, Polynomial.map_map, hcomp]
  have hVX : (ftauVX hu hne hv hw hbez).map ψ
      = (chartV hu hne.ge hv hw hbez).map φO := by
    rw [ftauVX, Polynomial.map_map, hcomp]
  have hF : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map ψ = f.map (algebraMap O K) := by
    rw [Polynomial.map_map, hψC]
  -- the pipeline and the pack under `ψ`
  have hpipe := map_foldPipe (m := 2 * n) ψ hfC hfCdeg h₀ (fun j hj ↦ hd.bezout hj) hcv
  have hdK := hd.map ψ hfC hfCdeg h₀ hcv
  rw [← ftauFoldPipe_def, hxs, hys, hUX, hVX, hF, ← FoldCertData.seq_map] at hpipe
  rw [hxs, hys, hUX, hVX, hF] at hdK
  -- the evaluated chart start is a fold state over `K`
  have h₀K : IsFoldState n (f.map (algebraMap O K)) ((chartU u n).map φO)
      ((chartV hu hne.ge hv hw hbez).map φO) := by
    have hchart : IsFoldState n (f.map (MvPowerSeries.C :
        O →+* MvPowerSeries (Fin n) O)) (chartU u n) (chartV hu hne.ge hv hw hbez) :=
      ⟨chartU_monic hu hne.ge, natDegree_eq_of_degree_eq_some
          ((chartU_degree hu hne.ge).trans
            (by rw [degree_eq_natDegree hu.ne_zero, hne])),
        chartU_dvd_chartV_sq_sub hu hne.ge hv hw hbez,
        (chartV_degree_lt hu hne.ge hv hw hbez).trans_eq
          (by rw [degree_eq_natDegree hu.ne_zero, hne])⟩
    have h := hchart.map φO
    rwa [Polynomial.map_map, hφOC] at h
  -- the `K`-level pipeline collapses to its start
  have hself := fold_pipeline_eq_self (hf.map _) ((hf.natDegree_map _).trans hfdeg)
    h₀K (fun i ↦ sq_eq_map_of_sq_eq _ (hb i ▸ eval_sq_eq_of_root hw (ha i)))
    fun j hj ↦ hdK.bezout hj
  have hfinal := hpipe.trans hself
  have h1 := congrArg Prod.fst hfinal
  have h2 := congrArg Prod.snd hfinal
  dsimp only at h1 h2
  rw [← hfuse] at h1 h2
  exact Prod.ext h1 h2


/-- **The unit law of the fold pipeline**: setting `Y = 0` degenerates the moving points onto the
`τ`-points, the point block cancels pair by pair, and the pipeline returns the `X`-side chart datum
— at every point of the polydisk by the class computation, and as an identity of polynomials by
interpolation. -/
theorem ftauFoldPipe_map_setYZero (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hsplit : u = ∏ m : Fin n, (X - C (a m))) (hainj : Function.Injective a)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0) :
    ((ftauFoldPipe A a b hu hne hv hw hbez d).1.map
        (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O),
      (ftauFoldPipe A a b hu hne hv hw hbez d).2.map
        (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O))
      = (chartU u n, chartV hu hne.ge hv hw hbez) := by
  have hπu : ¬IsUnit π := fun hunit ↦ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    (Ideal.eq_top_of_isUnit_mem _ (hπ ▸ Ideal.mem_span_singleton_self π) hunit)
  have : Infinite O := Infinite.of_injective (π ^ ·)
    (pow_injective_of_not_isUnit hπu hπ0)
  refine Prod.ext ?_ ?_
  · exact MvPSeries.polynomial_eq_of_forall_eval_eq hπ hπ0 fun z hz ↦ congrArg Prod.fst
      (map_evalRingHom_ftauFoldPipe_map_setYZero hu hne hv hw hbez hf hfdeg hsplit hainj
        hroot hcc hb hd hz)
  · exact MvPSeries.polynomial_eq_of_forall_eval_eq hπ hπ0 fun z hz ↦ congrArg Prod.snd
      (map_evalRingHom_ftauFoldPipe_map_setYZero hu hne hv hw hbez hf hfdeg hsplit hainj
        hroot hcc hb hd hz)

/-- **The unit law of the fold form of the translated law** (group-law form): setting `Y = 0`
returns the `X`-coordinates, `F_τ(X, 0) = X`. -/
theorem setYZero_FtauFold (hf : f.Monic) (hfdeg : f.natDegree = 2 * n + 1)
    (hsplit : u = ∏ m : Fin n, (X - C (a m))) (hainj : Function.Injective a)
    (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
    (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
    (hb : ∀ i, v.eval (a i) = b i)
    {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
    (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π}) (hπ0 : π ≠ 0)
    (i : Fin n) :
    setYZero (FtauFold A a b hu hne hv hw hbez d i) = MvPowerSeries.X i := by
  have hpair := congrArg Prod.fst (ftauFoldPipe_map_setYZero hu hne hv hw hbez hf hfdeg
    hsplit hainj hroot hcc hb hd hπ hπ0)
  dsimp only at hpair
  have hcoeff := coeff_map_chartU (RingHom.id (MvPowerSeries (Fin n) O))
    (RingHom.id_comp _) u i
  rw [Polynomial.map_id] at hcoeff
  have h2 : (((ftauFoldPipe A a b hu hne hv hw hbez d).1
      - u.map MvPowerSeries.C).map
        (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)).coeff
        (i : ℕ) = MvPowerSeries.X i := by
    rw [Polynomial.map_sub, hpair, Polynomial.map_map, setYZero_comp_C,
      Polynomial.coeff_sub, hcoeff]
    exact add_sub_cancel_left _ _
  rwa [Polynomial.coeff_map] at h2

end UnitLaw

section TauPoints

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsDomain O]
  {n : ℕ} {f u v w c₁ c₂ : O[X]}
  {A : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O} {a b : Fin n → O}
  (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)
  [NeZero (2 : FractionRing O)]
  [Fact (Odd (f.map (algebraMap O (FractionRing O))).natDegree)]
  [Fact (Squarefree (f.map (algebraMap O (FractionRing O))))]
  (hb : ∀ i, v.eval (a i) = b i)

include hb in
/-- **The involuted `τ`-points of the fold assemble the negated `τ`-class**: phase 2 of
`ChabautyColeman.prod_mk0_eval_points`. They come in reverse order, so the product is
reflected before the `τ`-datum is split into its points over `Frac O`. -/
private theorem prod_mk0_tauPoints (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {φ : MvPowerSeries (Fin n ⊕ Fin n) O →+* FractionRing O}
    (hφC : φ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O (FractionRing O)) :
    ∏ j ∈ Finset.range n,
        ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (φ (ftauFoldXs A a (n + j))))
            (C (φ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b (n + j)))),
          mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
      = tauClassNeg (f := f) (v := v) hu := by
  classical
  set K := FractionRing O
  -- the involuted points come in reverse order: reflect the product
  rw [← Finset.prod_range_reflect _ n, Finset.prod_range]
  have hxval (i : Fin n) : φ (ftauFoldXs A a (n + (n - 1 - (i : ℕ))))
      = algebraMap O K (a i) := by
    have h1 : ftauFoldXs A a (n + (n - 1 - (i : ℕ))) = MvPowerSeries.C (a i) := by
      rw [ftauFoldXs, phaseSeq_of_ge _ _ (by lia) (by lia)]
      exact congrArg (fun m ↦ MvPowerSeries.C (a m))
        (Fin.ext (by simp only [Fin.val_rev]; lia))
    rw [h1]
    exact RingHom.congr_fun hφC (a i)
  have hyval (i : Fin n) :
      φ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b (n + (n - 1 - (i : ℕ))))
        = -(algebraMap O K (b i)) := by
    have h1 : ftauFoldYs (ftauVY hu hne hv hw hbez) A b (n + (n - 1 - (i : ℕ)))
        = -MvPowerSeries.C (b i) := by
      rw [ftauFoldYs, phaseSeq_of_ge _ _ (by lia) (by lia)]
      exact congrArg (fun m ↦ -MvPowerSeries.C (b m))
        (Fin.ext (by simp only [Fin.val_rev]; lia))
    rw [h1, map_neg]
    exact congrArg Neg.neg (RingHom.congr_fun hφC (b i))
  rw [Finset.prod_congr rfl fun i _ ↦ mk0_point_congr (hxval i) (hyval i)]
  -- the `τ`-datum splits into its points over `K`
  have huprod : u.map (algebraMap O K) = ∏ i : Fin n, (X - C (algebraMap O K (a i))) := by
    rw [hsplit, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hinj : Set.InjOn (fun i ↦ algebraMap O K (a i)) (Finset.univ : Finset (Fin n)) :=
    (Function.injective_of_isUnit_sub (a := fun i ↦ algebraMap O K (a i))
      fun i j hij ↦ by rw [← map_sub]; exact (hunit i j hij).map _).injOn
  have hdneg : (∏ i : Fin n, (X - C (algebraMap O K (a i))))
      ∣ (-(v.map (algebraMap O K))) ^ 2 - f.map (algebraMap O K) := by
    have h2 : (-(v.map (algebraMap O K))) ^ 2 - f.map (algebraMap O K)
        = (v.map (algebraMap O K)) ^ 2 - f.map (algebraMap O K) := by ring
    rw [← huprod, h2]
    have h := Polynomial.map_dvd (algebraMap O K) (Dvd.intro w hw.symm)
    rwa [Polynomial.map_sub, Polynomial.map_pow] at h
  have hcls := mk0_mumfordIdeal_prod (f := f.map (algebraMap O K)) hinj hdneg
  have hVeval (i : Fin n) : (-(v.map (algebraMap O K))).eval (algebraMap O K (a i))
      = -(algebraMap O K (b i)) := by
    rw [Polynomial.eval_neg, Polynomial.eval_map_apply, hb i]
  rw [Finset.prod_congr rfl fun i _ ↦ mk0_point_congr rfl (hVeval i).symm, ← hcls,
    tauClassNeg]
  exact congrArg ClassGroup.mk0 (Subtype.ext (by
    change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
    rw [← huprod]))

end TauPoints

section EvalChart

open IsLocalRing

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
  (hroot : ∀ i, (ftauUY u n).eval (A i) = 0)
  (hcc : ∀ i, MvPowerSeries.constantCoeff (A i) = a i)
  (ha : ∀ i, u.eval (a i) = 0) (hb : ∀ i, v.eval (a i) = b i)
  {d : FoldCertData (MvPowerSeries (Fin n ⊕ Fin n) O) n}
  (hd : IsFtauFoldCerts A a b hu hne hv hw hbez d)

include hf hfdeg hroot hcc ha hb hd in
/-- The values of the fold form of the translated group law at a point of the maximal
ideal lie in the maximal ideal. -/
theorem eval_FtauFold_mem {x : Fin n ⊕ Fin n → O} (hx : ∀ s, x s ∈ maximalIdeal O)
    (i : Fin n) :
    MvPSeries.eval x (FtauFold A a b hu hne hv hw hbez d i) ∈ maximalIdeal O :=
  MvPSeries.eval_mem_maximalIdeal (MvPSeries.hasEval_of_mem hx) hx _
    (by rw [constantCoeff_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd i]
        exact Ideal.zero_mem _)

include hf hfdeg hroot hcc ha hb hd in
/-- **The evaluated fold pipeline is the chart at the evaluated coordinates**: at a
point `x` of the polydisk, the final datum of the fold-`F_τ` pipeline is the chart datum
at `e = F_τ(x)` — the `u`-parts agree by the shape of the result, and the `v`-parts by
uniqueness of the square root (both reduce to `v_bar`, and `ū` is coprime to `2v_bar`). -/
theorem eval_ftauFoldPipe_eq {x : Fin n ⊕ Fin n → O}
    (hx : ∀ s, x s ∈ maximalIdeal O) {e : Fin n → O}
    (hedef : e = fun j ↦ MvPSeries.eval x (FtauFold A a b hu hne hv hw hbez d j))
    (he : ∀ j, e j ∈ maximalIdeal O) :
    ((ftauFoldPipe A a b hu hne hv hw hbez d).1.map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)),
      (ftauFoldPipe A a b hu hne hv hw hbez d).2.map
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)))
      = ((chartU u n).map (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem he)),
        (chartV hu hne.ge hv hw hbez).map
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem he))) := by
  classical
  have hstate : IsFoldState n (f.map MvPowerSeries.C)
      (ftauFoldPipe A a b hu hne hv hw hbez d).1
      (ftauFoldPipe A a b hu hne hv hw hbez d).2 :=
    hd.isFoldState (hf.map _) ((hf.natDegree_map _).trans hfdeg)
      (isFoldState_ftauUX hu hne hv hw hbez)
      (fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb hj) le_rfl
  set εx := MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx) with hεx
  set εe := MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem he) with hεe
  -- the evaluation homomorphisms fix constants
  have hεxC : εx.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = RingHom.id O := MvPSeries.evalRingHom_comp_C _
  have hεeC : εe.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n) O)
      = RingHom.id O := MvPSeries.evalRingHom_comp_C _
  have hCx (g : O[X]) : (g.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map εx = g := by
    rw [Polynomial.map_map, hεxC, Polynomial.map_id]
  have hCe (g : O[X]) : (g.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n) O)).map εe = g := by
    rw [Polynomial.map_map, hεeC, Polynomial.map_id]
  -- the `u`-parts agree: both are `u` displaced by the coordinates `e`
  have hfst : (ftauFoldPipe A a b hu hne hv hw hbez d).1.map εx
      = u + ∑ j : Fin n, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ) := by
    have h := congrArg (Polynomial.map εx)
      (ftauFoldPipe_fst_eq hu hne hv hw hbez hf hfdeg hroot ha hb hd)
    rw [Polynomial.map_add, Polynomial.map_sum, hCx] at h
    rw [h]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      hεx, MvPSeries.evalRingHom_apply, hedef]
  have hcfst : (chartU u n).map εe
      = u + ∑ j : Fin n, Polynomial.C (e j) * Polynomial.X ^ (j : ℕ) := by
    rw [chartU, Polynomial.map_add, Polynomial.map_sum, hCe]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      hεe, MvPSeries.evalRingHom_apply, MvPSeries.eval_X]
  refine Prod.ext (by dsimp only; rw [hfst, hcfst]) ?_
  -- the `v`-parts agree by square-root uniqueness
  dsimp only
  set U := (ftauFoldPipe A a b hu hne hv hw hbez d).1.map εx with hU
  set W := (ftauFoldPipe A a b hu hne hv hw hbez d).2.map εx with hW
  set V' := (chartV hu hne.ge hv hw hbez).map εe with hV'
  have hUm : U.Monic := hstate.monicU.map _
  have hWd : U ∣ W ^ 2 - f := by
    have h := Polynomial.map_dvd εx hstate.dvd_sq
    rwa [Polynomial.map_sub, Polynomial.map_pow, hCx] at h
  have hVd : U ∣ V' ^ 2 - f := by
    have h := chartU_map_dvd_chartV_map_sq_sub hu hne.ge hv hw hbez hεeC
    rw [Polynomial.map_id] at h
    rwa [hcfst, ← hfst] at h
  have hWdeg : W.degree < U.degree :=
    Polynomial.degree_map_le.trans_lt
      (hstate.degree_V_lt.trans_eq (hstate.monicU.degree_map _).symm)
  have hVdeg : V'.degree < U.degree := by
    have h1 : ((chartU u n).map εe).degree = U.degree := by rw [hcfst, ← hfst]
    rw [← h1, (chartU_monic hu hne.ge).degree_map, chartU_degree hu hne.ge]
    exact Polynomial.degree_map_le.trans_lt (chartV_degree_lt hu hne.ge hv hw hbez)
  -- residues: `Ū = ū`, and both square roots reduce to `v_bar`
  have hccp := ftauFoldPipe_constantCoeff_eq hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd
  have hUbar : U.map (residue O) = u.map (residue O) := by
    rw [hU, map_residue_eval_eq hx,
      congrArg (Polynomial.map (residue O)) (congrArg Prod.fst hccp)]
  have hWbar : W.map (residue O) = v.map (residue O) := by
    rw [hW, map_residue_eval_eq hx,
      congrArg (Polynomial.map (residue O)) (congrArg Prod.snd hccp)]
  have hVbar : V'.map (residue O) = v.map (residue O) := by
    rw [hV', map_residue_eval_eq he,
      congrArg (Polynomial.map (residue O))
        (chartV_map_constantCoeff hu hne.ge hv hw hbez)]
  -- the Bézout certificate at the common residue datum, lifted from `hbez`
  refine eq_of_dvd_sq_sub_of_residue_bezout (c₁ := c₁.map (residue O))
    (c₂ := c₂.map (residue O)) hUm hWd hVd hWdeg hVdeg ?_ hWbar hVbar
  rw [hUbar]
  exact map_bezout (residue O) hbez

include hroot hcc in
/-- **The moving points of the fold assemble the `Y`-side chart class**: phase 1 of
`ChabautyColeman.prod_mk0_eval_points`. Only the two compatibilities of `φ` with the
constant and the `Y`-rename are used, so the statement is free of the evaluation map. -/
private theorem prod_mk0_movingPoints
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {φ : MvPowerSeries (Fin n ⊕ Fin n) O →+* FractionRing O}
    (hφC : φ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O (FractionRing O))
    {z : Fin n → O} (hz : ∀ s, z s ∈ maximalIdeal O)
    (hφr : φ.comp (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom
      = (algebraMap O (FractionRing O)).comp
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))) :
    ∏ j ∈ Finset.range n,
        ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (φ (ftauFoldXs A a j)))
            (C (φ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))),
          mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
      = chartClass hu hne hv hw hbez hz := by
  classical
  set K := FractionRing O
  rw [Finset.prod_range]
  have hxval (i : Fin n) : φ (ftauFoldXs A a (i : ℕ)) = φ (A i) := by
    rw [ftauFoldXs, phaseSeq_of_lt _ _ i.isLt, Fin.eta]
  have hyval (i : Fin n) : φ (ftauFoldYs (ftauVY hu hne hv hw hbez) A b (i : ℕ))
      = φ ((ftauVY hu hne hv hw hbez).eval (A i)) := by
    rw [ftauFoldYs, phaseSeq_of_lt _ _ i.isLt, Fin.eta]
  rw [Finset.prod_congr rfl fun i _ ↦ mk0_point_congr (hxval i) (hyval i)]
  -- the moving points are pairwise distinct over `K`
  have hAunit (i j : Fin n) (hij : i ≠ j) : IsUnit (A i - A j) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub, hcc i, hcc j]
    exact hunit i j hij
  have hinj : Set.InjOn (fun i ↦ φ (A i)) (Finset.univ : Finset (Fin n)) :=
    (Function.injective_of_isUnit_sub (a := fun i ↦ φ (A i))
      fun i j hij ↦ by rw [← map_sub]; exact (hAunit i j hij).map φ).injOn
  -- the chart data images
  have hUb : (ftauUY u n).map φ = (chartU u n).map ((algebraMap O K).comp
      (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))) := by
    rw [ftauUY, Polynomial.map_map, hφr]
  have hVb : (ftauVY hu hne hv hw hbez).map φ
      = (chartV hu hne.ge hv hw hbez).map ((algebraMap O K).comp
        (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hz))) := by
    rw [ftauVY, Polynomial.map_map, hφr]
  -- the evaluated chart splits into the evaluated moving points
  have hprod : (ftauUY u n).map φ = ∏ i : Fin n, (X - C (φ (A i))) := by
    rw [ftauUY_eq_prod hu hne hroot hcc hunit, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hdUb : (∏ i : Fin n, (X - C (φ (A i))))
      ∣ ((ftauVY hu hne hv hw hbez).map φ) ^ 2 - f.map (algebraMap O K) := by
    rw [← hprod]
    obtain ⟨q, hq⟩ := chartV_map_rename_dvd hu hne hv hw hbez Sum.inr
    have hq' : ftauVY hu hne hv hw hbez ^ 2
        - f.map (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
        = ftauUY u n * q := hq
    have h := congrArg (Polynomial.map φ) hq'
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
      Polynomial.map_map, hφC] at h
    exact ⟨q.map φ, h⟩
  have hcls := mk0_mumfordIdeal_prod (f := f.map (algebraMap O K)) hinj hdUb
  have hVeval (i : Fin n) : ((ftauVY hu hne hv hw hbez).map φ).eval (φ (A i))
      = φ ((ftauVY hu hne hv hw hbez).eval (A i)) := Polynomial.eval_map_apply _ _
  rw [Finset.prod_congr rfl fun i _ ↦ mk0_point_congr rfl (hVeval i).symm, ← hcls,
    chartClass]
  exact congrArg ClassGroup.mk0 (Subtype.ext (by
    change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
    rw [← hprod, hUb, hVb]))

include hroot hcc hb in
/-- **The product of the evaluated point classes of the fold**: the moving points
assemble the `Y`-side chart class at the component point, and the involuted `τ`-points
assemble the negated `τ`-class. -/
theorem prod_mk0_eval_points (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {x : Fin n ⊕ Fin n → O} (hx : ∀ s, x s ∈ maximalIdeal O) :
    ∏ j ∈ Finset.range (2 * n),
        ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O (FractionRing O)))
            (X - C (((algebraMap O (FractionRing O)).comp
                (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)))
              (ftauFoldXs A a j)))
            (C (((algebraMap O (FractionRing O)).comp
                (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)))
              (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))),
          mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
      = chartClass hu hne hv hw hbez (z := x ∘ Sum.inr) (fun s ↦ hx (Sum.inr s))
        * tauClassNeg (f := f) (v := v) hu := by
  set ψ : MvPowerSeries (Fin n ⊕ Fin n) O →+* FractionRing O :=
    (algebraMap O (FractionRing O)).comp
      (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)) with hψ
  have hψC : ψ.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O (FractionRing O) :=
    hψ ▸ MvPSeries.comp_evalRingHom_comp_C _ _
  have hψr : ψ.comp (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom
      = (algebraMap O (FractionRing O)).comp (MvPSeries.evalRingHom
          (MvPSeries.hasEval_of_mem fun s ↦ hx (Sum.inr s))) := by
    rw [hψ]
    exact comp_evalRingHom_comp_rename (MvPSeries.hasEval_of_mem hx)
      Sum.inr (MvPSeries.hasEval_of_mem fun s ↦ hx (Sum.inr s)) _
  rw [two_mul, Finset.prod_range_add,
    prod_mk0_movingPoints hu hne hv hw hbez hroot hcc hunit hψC
      (fun s ↦ hx (Sum.inr s)) hψr,
    prod_mk0_tauPoints hu hne hv hw hbez hb hsplit hunit hψC]

include hf hfdeg hroot hcc ha hb hd in
/-- **The chart at `F_τ(x)` represents the sum of the classes** (the pointwise class
representation): for `x` in the polydisk, the chart datum at the evaluated coordinates
`e = F_τ(x)` represents `ch(x_L) + ch(x_R) - τ` in the class group over the fraction
field — the fold pipeline composes the `X`-side chart with the moving points (which
assemble the `Y`-side chart) and the involuted `τ`-points (which assemble `⊖τ`). -/
theorem mk0_chart_eval_fold (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {x : Fin n ⊕ Fin n → O} (hx : ∀ s, x s ∈ maximalIdeal O) {e : Fin n → O}
    (hedef : e = fun j ↦ MvPSeries.eval x (FtauFold A a b hu hne hv hw hbez d j))
    (he : ∀ j, e j ∈ maximalIdeal O) :
    chartClass hu hne hv hw hbez he
      = chartClass hu hne hv hw hbez (z := x ∘ Sum.inl) (fun s ↦ hx (Sum.inl s))
        * chartClass hu hne hv hw hbez (z := x ∘ Sum.inr) (fun s ↦ hx (Sum.inr s))
        * tauClassNeg (f := f) (v := v) hu := by
  classical
  set K := FractionRing O
  set ψx : MvPowerSeries (Fin n ⊕ Fin n) O →+* K :=
    (algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)) with hψx
  have hψxC : ψx.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O K :=
    hψx ▸ MvPSeries.comp_evalRingHom_comp_C _ _
  have hψxl : ψx.comp (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom
      = (algebraMap O K).comp (MvPSeries.evalRingHom
          (MvPSeries.hasEval_of_mem fun s ↦ hx (Sum.inl s))) := by
    rw [hψx]
    exact comp_evalRingHom_comp_rename (MvPSeries.hasEval_of_mem hx)
      Sum.inl (MvPSeries.hasEval_of_mem fun s ↦ hx (Sum.inl s)) _
  -- the pipeline data over `K`
  have hfC : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).Monic := hf.map _
  have hfCdeg : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).natDegree = 2 * n + 1 :=
    (hf.natDegree_map _).trans hfdeg
  have h₀ := isFoldState_ftauUX hu hne hv hw hbez
  have hcv := fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb (j := j) hj
  have hF : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map ψx = f.map (algebraMap O K) := by
    rw [Polynomial.map_map, hψxC]
  have hpipe := map_foldPipe (m := 2 * n) ψx hfC hfCdeg h₀ (fun j hj ↦ hd.bezout hj) hcv
  have hdK := hd.map ψx hfC hfCdeg h₀ hcv
  rw [← FoldCertData.seq_map, ← ftauFoldPipe_def] at hpipe
  rw [hF] at hpipe hdK
  have h₀K := h₀.map ψx
  rw [hF] at h₀K
  have hcvK : ∀ j < 2 * n, ψx (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j) ^ 2
      = (f.map (algebraMap O K)).eval (ψx (ftauFoldXs A a j)) := by
    intro j hj
    have h := sq_eq_map_of_sq_eq ψx (hcv j hj)
    rwa [hF] at h
  have hstK := isFoldState_foldPipe (m := 2 * n) (hf.map _)
    ((hf.natDegree_map _).trans hfdeg) h₀K (fun j hj ↦ hdK.bezout hj) hcvK
  -- the class of the evaluated pipeline
  have hmk := mk0_foldPipe (hf.map _) ((hf.natDegree_map _).trans hfdeg) h₀K
    (fun j hj ↦ hdK.bezout hj) hcvK hstK.monicU
  beta_reduce at hmk
  have hC := prod_mk0_eval_points hu hne hv hw hbez hroot hcc hb hsplit hunit hx
  rw [← hψx] at hC
  rw [hC] at hmk
  -- the start is the chart class at the left component
  have hstart : ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
      ((ftauUX u n).map ψx) ((ftauVX hu hne hv hw hbez).map ψx),
      mumfordIdeal_mem_nonZeroDivisors _ h₀K.monicU.ne_zero _⟩
      = chartClass hu hne hv hw hbez (z := x ∘ Sum.inl) (fun s ↦ hx (Sum.inl s)) := by
    rw [chartClass]
    refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
    change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
    rw [ftauUX, ftauVX, Polynomial.map_map, Polynomial.map_map, hψxl]
  rw [hstart] at hmk
  -- the evaluated pipeline is the chart at `e`
  have hpair := eval_ftauFoldPipe_eq hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hx
    hedef he
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpair
  dsimp only at h1 h2
  have hbr1 : (ftauFoldPipe A a b hu hne hv hw hbez d).1.map ψx
      = (chartU u n).map ((algebraMap O K).comp
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem he))) := by
    rw [hψx, ← Polynomial.map_map, h1, Polynomial.map_map]
  have hbr2 : (ftauFoldPipe A a b hu hne hv hw hbez d).2.map ψx
      = (chartV hu hne.ge hv hw hbez).map ((algebraMap O K).comp
          (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem he))) := by
    rw [hψx, ← Polynomial.map_map, h2, Polynomial.map_map]
  obtain ⟨hp1, hp2⟩ := Prod.ext_iff.mp hpipe
  dsimp only at hp1 hp2
  refine Eq.trans ?_ (hmk.trans (mul_assoc _ _ _).symm)
  rw [chartClass]
  refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
  change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
  rw [← hbr1, ← hbr2, hp1, hp2]

include hf hfdeg hroot hcc ha hb hd in
/-- **Evaluations of the fold form of `F_τ` at points with the same class are equal**:
if the products of the chart classes at the two component points agree, both evaluated
pipelines produce the reduced representative of the same class, so the coordinates
agree. The engine for associativity and commutativity. -/
theorem eval_FtauFold_eq_of_mk0_eq (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {x y : Fin n ⊕ Fin n → O}
    (hx : ∀ s, x s ∈ maximalIdeal O) (hy : ∀ s, y s ∈ maximalIdeal O)
    (hmk : chartClass hu hne hv hw hbez (z := x ∘ Sum.inl) (fun s ↦ hx (Sum.inl s))
        * chartClass hu hne hv hw hbez (z := x ∘ Sum.inr) (fun s ↦ hx (Sum.inr s))
      = chartClass hu hne hv hw hbez (z := y ∘ Sum.inl) (fun s ↦ hy (Sum.inl s))
        * chartClass hu hne hv hw hbez (z := y ∘ Sum.inr) (fun s ↦ hy (Sum.inr s)))
    (i : Fin n) :
    MvPSeries.eval x (FtauFold A a b hu hne hv hw hbez d i)
      = MvPSeries.eval y (FtauFold A a b hu hne hv hw hbez d i) := by
  classical
  set K := FractionRing O
  set ψx : MvPowerSeries (Fin n ⊕ Fin n) O →+* K :=
    (algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hx)) with hψx
  set ψy : MvPowerSeries (Fin n ⊕ Fin n) O →+* K :=
    (algebraMap O K).comp (MvPSeries.evalRingHom (MvPSeries.hasEval_of_mem hy)) with hψy
  have hψxC : ψx.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O K :=
    hψx ▸ MvPSeries.comp_evalRingHom_comp_C _ _
  have hψyC : ψy.comp (MvPowerSeries.C : O →+* MvPowerSeries (Fin n ⊕ Fin n) O)
      = algebraMap O K :=
    hψy ▸ MvPSeries.comp_evalRingHom_comp_C _ _
  have hψxl : ψx.comp (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom
      = (algebraMap O K).comp (MvPSeries.evalRingHom
          (MvPSeries.hasEval_of_mem fun s ↦ hx (Sum.inl s))) := by
    rw [hψx]
    exact comp_evalRingHom_comp_rename (MvPSeries.hasEval_of_mem hx)
      Sum.inl (MvPSeries.hasEval_of_mem fun s ↦ hx (Sum.inl s)) _
  have hψyl : ψy.comp (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom
      = (algebraMap O K).comp (MvPSeries.evalRingHom
          (MvPSeries.hasEval_of_mem fun s ↦ hy (Sum.inl s))) := by
    rw [hψy]
    exact comp_evalRingHom_comp_rename (MvPSeries.hasEval_of_mem hy)
      Sum.inl (MvPSeries.hasEval_of_mem fun s ↦ hy (Sum.inl s)) _
  -- the pipeline data over `K`, for both points
  have hfC : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).Monic := hf.map _
  have hfCdeg : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).natDegree = 2 * n + 1 :=
    (hf.natDegree_map _).trans hfdeg
  have h₀ := isFoldState_ftauUX hu hne hv hw hbez
  have hcv := fun j hj ↦ ftauFoldYs_sq hu hne hv hw hbez hroot ha hb (j := j) hj
  have hFx : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map ψx = f.map (algebraMap O K) := by
    rw [Polynomial.map_map, hψxC]
  have hFy : (f.map (MvPowerSeries.C :
      O →+* MvPowerSeries (Fin n ⊕ Fin n) O)).map ψy = f.map (algebraMap O K) := by
    rw [Polynomial.map_map, hψyC]
  have hpipex := map_foldPipe (m := 2 * n) ψx hfC hfCdeg h₀ (fun j hj ↦ hd.bezout hj) hcv
  have hpipey := map_foldPipe (m := 2 * n) ψy hfC hfCdeg h₀ (fun j hj ↦ hd.bezout hj) hcv
  have hdKx := hd.map ψx hfC hfCdeg h₀ hcv
  have hdKy := hd.map ψy hfC hfCdeg h₀ hcv
  rw [← FoldCertData.seq_map, ← ftauFoldPipe_def] at hpipex hpipey
  rw [hFx] at hpipex hdKx
  rw [hFy] at hpipey hdKy
  have h₀Kx := h₀.map ψx
  have h₀Ky := h₀.map ψy
  rw [hFx] at h₀Kx
  rw [hFy] at h₀Ky
  have hcvKx : ∀ j < 2 * n, ψx (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j) ^ 2
      = (f.map (algebraMap O K)).eval (ψx (ftauFoldXs A a j)) := by
    intro j hj
    have h := sq_eq_map_of_sq_eq ψx (hcv j hj)
    rwa [hFx] at h
  have hcvKy : ∀ j < 2 * n, ψy (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j) ^ 2
      = (f.map (algebraMap O K)).eval (ψy (ftauFoldXs A a j)) := by
    intro j hj
    have h := sq_eq_map_of_sq_eq ψy (hcv j hj)
    rwa [hFy] at h
  -- the start classes are the left chart classes
  have hstartx : ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
      ((ftauUX u n).map ψx) ((ftauVX hu hne hv hw hbez).map ψx),
      mumfordIdeal_mem_nonZeroDivisors _ h₀Kx.monicU.ne_zero _⟩
      = chartClass hu hne hv hw hbez (z := x ∘ Sum.inl) (fun s ↦ hx (Sum.inl s)) := by
    rw [chartClass]
    refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
    change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
    rw [ftauUX, ftauVX, Polynomial.map_map, Polynomial.map_map, hψxl]
  have hstarty : ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
      ((ftauUX u n).map ψy) ((ftauVX hu hne hv hw hbez).map ψy),
      mumfordIdeal_mem_nonZeroDivisors _ h₀Ky.monicU.ne_zero _⟩
      = chartClass hu hne hv hw hbez (z := y ∘ Sum.inl) (fun s ↦ hy (Sum.inl s)) := by
    rw [chartClass]
    refine congrArg ClassGroup.mk0 (Subtype.ext ?_)
    change mumfordIdeal _ _ _ = mumfordIdeal _ _ _
    rw [ftauUX, ftauVX, Polynomial.map_map, Polynomial.map_map, hψyl]
  -- the point-class products
  have hCx := prod_mk0_eval_points hu hne hv hw hbez hroot hcc hb hsplit hunit hx
  have hCy := prod_mk0_eval_points hu hne hv hw hbez hroot hcc hb hsplit hunit hy
  rw [← hψx] at hCx
  rw [← hψy] at hCy
  -- the two pipelines agree: their inputs represent the same class
  have hmk' : ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
        ((ftauUX u n).map ψx) ((ftauVX hu hne hv hw hbez).map ψx),
        mumfordIdeal_mem_nonZeroDivisors _ h₀Kx.monicU.ne_zero _⟩
      * ∏ j ∈ Finset.range (2 * n),
          ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
              (X - C (ψx (ftauFoldXs A a j)))
              (C (ψx (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))),
            mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
          ((ftauUX u n).map ψy) ((ftauVX hu hne hv hw hbez).map ψy),
          mumfordIdeal_mem_nonZeroDivisors _ h₀Ky.monicU.ne_zero _⟩
        * ∏ j ∈ Finset.range (2 * n),
            ClassGroup.mk0 ⟨mumfordIdeal (f.map (algebraMap O K))
                (X - C (ψy (ftauFoldXs A a j)))
                (C (ψy (ftauFoldYs (ftauVY hu hne hv hw hbez) A b j))),
              mumfordIdeal_mem_nonZeroDivisors _ (monic_X_sub_C _).ne_zero _⟩ := by
    rw [hstartx, hstarty, hCx, hCy, ← mul_assoc, ← mul_assoc, hmk]
  have heq := fold_pipeline_eq_of_mk0_eq (hf.map (algebraMap O K))
    ((hf.natDegree_map _).trans hfdeg) h₀Kx h₀Ky
    (fun j hj ↦ hdKx.bezout hj) hcvKx (fun j hj ↦ hdKy.bezout hj) hcvKy hmk'
  -- compare the `i`-th coefficients of the two `u`-parts
  obtain ⟨hp1x, -⟩ := Prod.ext_iff.mp hpipex
  obtain ⟨hp1y, -⟩ := Prod.ext_iff.mp hpipey
  dsimp only at hp1x hp1y
  have hcoeff := congrArg (fun q : Polynomial K ↦ q.coeff (i : ℕ))
    (hp1x.trans ((congrArg Prod.fst heq).trans hp1y.symm))
  rw [coeff_map_ftauFoldPipe_fst hu hne hv hw hbez hf hfdeg hroot ha hb hd ψx hψxC,
    coeff_map_ftauFoldPipe_fst hu hne hv hw hbez hf hfdeg hroot ha hb hd ψy hψyC]
    at hcoeff
  have hψxval : ψx (FtauFold A a b hu hne hv hw hbez d i)
      = algebraMap O K (MvPSeries.eval x (FtauFold A a b hu hne hv hw hbez d i)) := by
    rw [hψx, RingHom.comp_apply, MvPSeries.evalRingHom_apply]
  have hψyval : ψy (FtauFold A a b hu hne hv hw hbez d i)
      = algebraMap O K (MvPSeries.eval y (FtauFold A a b hu hne hv hw hbez d i)) := by
    rw [hψy, RingHom.comp_apply, MvPSeries.evalRingHom_apply]
  rw [hψxval, hψyval] at hcoeff
  exact IsFractionRing.injective O K (add_left_cancel hcoeff)

include hf hfdeg hroot hcc ha hb hd in
/-- **Commutativity**: `F_τ(X, Y) = F_τ(Y, X)` — swapping the two variable blocks presents the same
pair of chart classes, so both orders evaluate to the same reduced representative. -/
theorem rename_swap_FtauFold (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (hπ0 : π ≠ 0) (i : Fin n) :
    MvPowerSeries.rename (Sum.swap : Fin n ⊕ Fin n → Fin n ⊕ Fin n)
        (FtauFold A a b hu hne hv hw hbez d i)
      = FtauFold A a b hu hne hv hw hbez d i := by
  have hπu : ¬IsUnit π := fun hπ' ↦ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    (Ideal.eq_top_of_isUnit_mem _ (hπ ▸ Ideal.mem_span_singleton_self π) hπ')
  have : Infinite O := Infinite.of_injective (π ^ ·)
    (pow_injective_of_not_isUnit hπu hπ0)
  refine sub_eq_zero.mp (MvPSeries.eq_zero_of_forall_eval_zero hπ hπ0 fun z hz ↦ ?_)
  have hevz : MvPowerSeries.HasEval z := MvPSeries.hasEval_of_mem hz
  have hevs : MvPowerSeries.HasEval (z ∘ Sum.swap) :=
    MvPSeries.hasEval_of_mem fun s ↦ hz _
  rw [← MvPSeries.evalRingHom_apply hevz, map_sub, MvPSeries.evalRingHom_apply,
    MvPSeries.evalRingHom_apply, sub_eq_zero]
  rw [eval_rename hevz Sum.swap hevs]
  refine eval_FtauFold_eq_of_mk0_eq hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit
    (x := z ∘ Sum.swap) (y := z) (fun s ↦ hz _) hz ?_ i
  rw [chartClass_congr hu hne hv hw hbez
      (show (z ∘ Sum.swap) ∘ Sum.inl = z ∘ Sum.inr from rfl) (fun s ↦ hz _) (fun s ↦ hz _),
    chartClass_congr hu hne hv hw hbez
      (show (z ∘ Sum.swap) ∘ Sum.inr = z ∘ Sum.inl from rfl) (fun s ↦ hz _) (fun s ↦ hz _),
    mul_comm]

include hf hfdeg hroot hcc ha hb hd in
/-- **The symmetric unit law**: setting `X = 0` in the fold form of the translated group law
returns the `Y`-coordinates, `F_τ(0, Y) = Y` — the unit law after the swap. -/
theorem setXZero_FtauFold (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (hπ0 : π ≠ 0) (i : Fin n) :
    setXZero (FtauFold A a b hu hne hv hw hbez d i) = MvPowerSeries.X i := by
  have hainj := Function.injective_of_isUnit_sub hunit
  rw [← setYZero_comp_rename_swap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, rename_swap_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd
      hsplit hunit hπ hπ0 i]
  exact setYZero_FtauFold hu hne hv hw hbez hf hfdeg hsplit hainj hroot hcc hb hd hπ hπ0 i

include hf hfdeg hroot hcc ha hb hd in
/-- **Associativity by interpolation**: `F_τ(F_τ(X, Y), Z) = F_τ(X, F_τ(Y, Z))` for the fold form
of the translated law — at every point of the polydisk both sides are the chart coordinates of the
reduced representative of `ch(x) + ch(y) + ch(z) - 2τ` (the pointwise class representation twice,
and uniqueness of reduced representatives), and interpolation upgrades pointwise agreement to an
identity of power series. -/
theorem FtauFold_assoc (hsplit : u = ∏ m : Fin n, (X - C (a m)))
    (hunit : ∀ i j : Fin n, i ≠ j → IsUnit (a i - a j))
    {π : O} (hπ : IsLocalRing.maximalIdeal O = Ideal.span {π})
    (hπ0 : π ≠ 0) (i : Fin n) :
    MvPowerSeries.subst (Sum.elim
        (fun j ↦ MvPowerSeries.rename (Sum.map id Sum.inl) (FtauFold A a b hu hne hv hw hbez d j))
        (fun j ↦ (MvPowerSeries.X (Sum.inr (Sum.inr j)) :
          MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) O)))
      (FtauFold A a b hu hne hv hw hbez d i)
      = MvPowerSeries.subst (Sum.elim
          (fun j ↦ (MvPowerSeries.X (Sum.inl j) :
            MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) O))
          (fun j ↦ MvPowerSeries.rename
            (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))
            (FtauFold A a b hu hne hv hw hbez d j)))
        (FtauFold A a b hu hne hv hw hbez d i) := by
  classical
  have hπu : ¬IsUnit π := fun hunit ↦ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    (Ideal.eq_top_of_isUnit_mem _ (hπ ▸ Ideal.mem_span_singleton_self π) hunit)
  have : Infinite O := Infinite.of_injective (π ^ ·)
    (pow_injective_of_not_isUnit hπu hπ0)
  set ιxy : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n) := Sum.map id Sum.inl
  set sL := Sum.elim
      (fun j ↦ MvPowerSeries.rename ιxy (FtauFold A a b hu hne hv hw hbez d j))
      (fun j ↦ (MvPowerSeries.X (Sum.inr (Sum.inr j)) :
        MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) O)) with hsLdef
  set sR := Sum.elim
      (fun j ↦ (MvPowerSeries.X (Sum.inl j) :
        MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) O))
      (fun j ↦ MvPowerSeries.rename (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))
        (FtauFold A a b hu hne hv hw hbez d j)) with hsRdef
  have hccF (j : Fin n) := constantCoeff_FtauFold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd j
  have hsubL : MvPowerSeries.HasSubst sL := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    rintro (j | j) <;>
      simp [hsLdef, MvPowerSeries.constantCoeff_rename, hccF]
  have hsubR : MvPowerSeries.HasSubst sR := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    rintro (j | j) <;>
      simp [hsRdef, MvPowerSeries.constantCoeff_rename, hccF]
  refine sub_eq_zero.mp (MvPSeries.eq_zero_of_forall_eval_zero hπ hπ0 fun w' hw' ↦ ?_)
  have hevw : MvPowerSeries.HasEval w' := MvPSeries.hasEval_of_mem hw'
  rw [← MvPSeries.evalRingHom_apply hevw, map_sub, MvPSeries.evalRingHom_apply,
    MvPSeries.evalRingHom_apply, sub_eq_zero, MvPSeries.eval_subst hevw hsubL,
    MvPSeries.eval_subst hevw hsubR]
  set p := fun s ↦ MvPSeries.eval w' (sL s) with hpdef
  set q := fun s ↦ MvPSeries.eval w' (sR s) with hqdef
  -- the component points and the evaluated inner coordinates
  have hwxy : ∀ s, (w' ∘ ιxy) s ∈ maximalIdeal O := fun s ↦ hw' _
  have hwyz : ∀ s, (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))) s
      ∈ maximalIdeal O := fun s ↦ hw' _
  have hevxy : MvPowerSeries.HasEval (w' ∘ ιxy) := MvPSeries.hasEval_of_mem hwxy
  have hevyz : MvPowerSeries.HasEval
      (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))) :=
    MvPSeries.hasEval_of_mem hwyz
  have hrenxy (j : Fin n) := eval_rename hevw ιxy hevxy (FtauFold A a b hu hne hv hw hbez d j)
  have hrenyz (j : Fin n) := eval_rename hevw
    (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)) hevyz
    (FtauFold A a b hu hne hv hw hbez d j)
  -- the canonical component families
  set wx : Fin n → O := fun j ↦ w' (Sum.inl j) with hwxdef
  set wy : Fin n → O := fun j ↦ w' (Sum.inr (Sum.inl j))
  set wz : Fin n → O := fun j ↦ w' (Sum.inr (Sum.inr j)) with hwzdef
  have hwxm : ∀ j, wx j ∈ maximalIdeal O := fun j ↦ hw' _
  have hwym : ∀ j, wy j ∈ maximalIdeal O := fun j ↦ hw' _
  have hwzm : ∀ j, wz j ∈ maximalIdeal O := fun j ↦ hw' _
  have hexym : ∀ j, MvPSeries.eval (w' ∘ ιxy) (FtauFold A a b hu hne hv hw hbez d j)
      ∈ maximalIdeal O := fun j ↦
    eval_FtauFold_mem hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hwxy j
  have heyzm : ∀ j, MvPSeries.eval
      (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)))
      (FtauFold A a b hu hne hv hw hbez d j) ∈ maximalIdeal O :=
    fun j ↦ eval_FtauFold_mem hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hwyz j
  -- normalize the four chart classes to the canonical families
  have hp1 : p ∘ Sum.inl
      = fun j ↦ MvPSeries.eval (w' ∘ ιxy) (FtauFold A a b hu hne hv hw hbez d j) := by
    funext j
    rw [Function.comp_apply, hpdef]
    exact hrenxy j
  have hp2 : p ∘ Sum.inr = wz := by
    funext j
    rw [Function.comp_apply, hpdef, hwzdef]
    exact MvPSeries.eval_X w' _
  have hq1 : q ∘ Sum.inl = wx := by
    funext j
    rw [Function.comp_apply, hqdef, hwxdef]
    exact MvPSeries.eval_X w' _
  have hq2 : q ∘ Sum.inr
      = fun j ↦ MvPSeries.eval
          (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)))
          (FtauFold A a b hu hne hv hw hbez d j) := by
    funext j
    rw [Function.comp_apply, hqdef]
    exact hrenyz j
  -- memberships for the two evaluated substituend families, read off the normalizations
  have hp : ∀ s, p s ∈ maximalIdeal O := by
    rintro (j | j)
    · rw [show p (Sum.inl j) = _ from congrFun hp1 j]
      exact hexym j
    · rw [show p (Sum.inr j) = _ from congrFun hp2 j]
      exact hwzm j
  have hq : ∀ s, q s ∈ maximalIdeal O := by
    rintro (j | j)
    · rw [show q (Sum.inl j) = _ from congrFun hq1 j]
      exact hwxm j
    · rw [show q (Sum.inr j) = _ from congrFun hq2 j]
      exact heyzm j
  refine eval_FtauFold_eq_of_mk0_eq hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd
    hsplit hunit hp hq ?_ i
  -- the class representations of the two inner evaluations
  have hmkL := mk0_chart_eval_fold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit hwxy
    (e := fun j ↦ MvPSeries.eval (w' ∘ ιxy) (FtauFold A a b hu hne hv hw hbez d j)) rfl hexym
  have hmkR := mk0_chart_eval_fold hu hne hv hw hbez hf hfdeg hroot hcc ha hb hd hsplit hunit hwyz
    (e := fun j ↦ MvPSeries.eval
      (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n)))
      (FtauFold A a b hu hne hv hw hbez d j)) rfl heyzm
  rw [chartClass_congr hu hne hv hw hbez (funext fun j ↦ rfl : (w' ∘ ιxy) ∘ Sum.inl = wx)
      _ hwxm,
    chartClass_congr hu hne hv hw hbez (funext fun j ↦ rfl : (w' ∘ ιxy) ∘ Sum.inr = wy)
      _ hwym] at hmkL
  rw [chartClass_congr hu hne hv hw hbez
      (funext fun j ↦ rfl :
        (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))) ∘ Sum.inl = wy)
      _ hwym,
    chartClass_congr hu hne hv hw hbez
      (funext fun j ↦ rfl :
        (w' ∘ (Sum.inr : Fin n ⊕ Fin n → Fin n ⊕ (Fin n ⊕ Fin n))) ∘ Sum.inr = wz)
      _ hwzm] at hmkR
  rw [chartClass_congr hu hne hv hw hbez hp1 _ hexym,
    chartClass_congr hu hne hv hw hbez hp2 _ hwzm,
    chartClass_congr hu hne hv hw hbez hq1 _ hwxm,
    chartClass_congr hu hne hv hw hbez hq2 _ heyzm, hmkL, hmkR]
  -- commutative-group bookkeeping
  rw [mul_assoc, mul_assoc, mul_comm (tauClassNeg (f := f) (v := v) hu)
    (chartClass hu hne hv hw hbez hwzm), ← mul_assoc (chartClass hu hne hv hw hbez hwym)]

end EvalChart

end ChabautyColeman

end
