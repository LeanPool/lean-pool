/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageAgreement
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.ExtensionPairing

/-!
# The distributional sign of pressure

The pressure convention in `def:riesz-pressure` is the negative of CKN's raw
second derivative operator.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The raw `L^r` extension input for the `i,j` Riesz pressure component. -/
@[expose]
noncomputable def rieszPressureRawExtensionInput
    (r : ℝ) (hr : 1 < r) (i j : Fin 3) :
    CKN.Foundation.Euclidean.LpExtensionInput (ENNReal.ofReal r)
      (rieszPressureOperatorBound r hr) := by
  let p : ℝ≥0∞ := ENNReal.ofReal r
  let hL2 := CKN.Foundation.Euclidean.rieszSecondL2Input i j
  haveI : Fact (1 ≤ p) := by
    dsimp [p]
    rw [← ENNReal.ofReal_one]
    exact ⟨ENNReal.ofReal_le_ofReal hr.le⟩
  have hC : 0 ≤ rieszPressureOperatorBound r hr := by
    have h := rieszPressureOperator_norm_le r hr i j
    exact le_trans (norm_nonneg _) h
  refine
    { T := fun f => -CKN.Foundation.Euclidean.rieszSecondL2RawOperator hL2 f
      measurable := ?_
      output_mem := ?_
      congr_ae := ?_
      add_ae := ?_
      smul_ae := ?_
      bound := ?_ }
  · intro f hf
    exact (CKN.Foundation.Euclidean.rieszSecondL2RawOperator_measurable hL2 hf).neg
  · intro f hf hf2
    have hOp := rieszPressureOperator_ae_eq_negRaw r hr i j f hf hf2
    exact (memLp_congr_ae hOp).mp (Lp.memLp (rieszPressureOperator r hr i j (hf.toLp f)))
  · intro f g hf hg hfg
    exact (CKN.Core.Endgame.raw_rieszSecond_congr_ae hL2 hf hg hfg).neg
  · intro f g hf hg
    have h := CKN.Core.Endgame.raw_rieszSecond_add_ae hL2 hf hg
    simpa only [Pi.neg_apply, neg_add] using h.neg
  · intro c f hf
    have h := CKN.Core.Endgame.raw_rieszSecond_smul_ae hL2 c hf
    simpa only [smul_neg] using h.neg
  · intro f hf hf2
    have hOp := rieszPressureOperator_ae_eq_negRaw r hr i j f hf hf2
    have hRawMem : MemLp (-CKN.Foundation.Euclidean.rieszSecondL2RawOperator hL2 f) p volume :=
      (memLp_congr_ae hOp).mp (Lp.memLp (rieszPressureOperator r hr i j (hf.toLp f)))
    have hClass : hRawMem.toLp
        (-CKN.Foundation.Euclidean.rieszSecondL2RawOperator hL2 f) =
        rieszPressureOperator r hr i j (hf.toLp f) := by
      apply Lp.ext
      filter_upwards [hRawMem.coeFn_toLp, hOp] with x hx hRx
      exact hx.trans hRx.symm
    calc
      ‖hRawMem.toLp (-CKN.Foundation.Euclidean.rieszSecondL2RawOperator hL2 f)‖ =
          ‖rieszPressureOperator r hr i j (hf.toLp f)‖ := congrArg norm hClass
      _ ≤ ‖rieszPressureOperator r hr i j‖ * ‖hf.toLp f‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ rieszPressureOperatorBound r hr * ‖hf.toLp f‖ :=
        mul_le_mul_of_nonneg_right (rieszPressureOperator_norm_le r hr i j)
          (norm_nonneg _)

private theorem rieszPressureRawExtensionCore_eq_operator
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    [Fact (1 ≤ ENNReal.ofReal r)] :
    CKN.Foundation.Euclidean.lpExtensionCore
        (ENNReal.ofReal_ne_top) (rieszPressureRawExtensionInput r hr i j) =
      rieszPressureOperator r hr i j := by
  let p : ℝ≥0∞ := ENNReal.ofReal r
  let hInput := rieszPressureRawExtensionInput r hr i j
  have hDense : Dense {u : Lp ℝ p (volume : Measure Vec3) |
      u ∈ CKN.Foundation.Euclidean.lpInterL2Submodule p} := by
    apply (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := p) (μ := (volume : Measure Vec3)) ENNReal.ofReal_ne_top).mono
    rintro u ⟨f, huf, hfc, hfd⟩
    exact (memLp_congr_ae huf).2
      (hfd.continuous.memLp_of_hasCompactSupport hfc)
  apply ContinuousLinearMap.ext
  intro u
  have hfun : (fun v : Lp ℝ p (volume : Measure Vec3) =>
      CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top hInput v) =
      fun v => rieszPressureOperator r hr i j v := by
    apply Continuous.ext_on hDense
      (CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top hInput).continuous
      (rieszPressureOperator r hr i j).continuous
    intro v hv
    let uL : CKN.Foundation.Euclidean.lpInterL2Submodule p := ⟨v, hv⟩
    let hf : MemLp (v : Vec3 → ℝ) p volume := Lp.memLp v
    have hRaw := rieszPressureOperator_ae_eq_negRaw r hr i j
      (v : Vec3 → ℝ) hf hv
    have hvClass : hf.toLp (v : Vec3 → ℝ) = v := Lp.ext hf.coeFn_toLp
    have hCoreClass := CKN.Foundation.Euclidean.lpExtensionCore_agrees
      ENNReal.ofReal_ne_top hInput uL
    have hCoreOut :
        CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top hInput v =
          (hInput.output_mem hf hv).toLp (hInput.T (v : Vec3 → ℝ)) := by
      change CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top hInput v =
        (hInput.output_mem hf hv).toLp (hInput.T (v : Vec3 → ℝ)) at hCoreClass
      exact hCoreClass
    apply Lp.ext
    have hCoreAE :
        (CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top hInput v :
          Vec3 → ℝ) =ᵐ[volume] hInput.T (v : Vec3 → ℝ) := by
      rw [hCoreOut]
      exact (hInput.output_mem hf hv).coeFn_toLp
    have hOpAE :
        (rieszPressureOperator r hr i j v : Vec3 → ℝ) =ᵐ[volume]
          hInput.T (v : Vec3 → ℝ) := by
      change (fun x => rieszPressureOperator r hr i j v x) =ᵐ[volume]
        fun x => -CKN.Foundation.Euclidean.rieszSecondL2RawOperator
          (CKN.Foundation.Euclidean.rieszSecondL2Input i j) (v : Vec3 → ℝ) x
      simpa only [hvClass] using hRaw
    exact hCoreAE.trans hOpAE.symm
  exact congrFun hfun u

/-- The signed Laplacian pairing holds on the full `L^r` domain. -/
theorem rieszPressureOperator_laplacian_pairing_of_memLp
    (r : ℝ) (hr : 1 < r) (i j : Fin 3)
    (g : Vec3 → ℝ)
    (hgr : MemLp g (ENNReal.ofReal r) (volume : Measure Vec3))
    (ψ : Vec3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, rieszPressureOperator r hr i j (hgr.toLp g) x * CKN.spatialLaplacian ψ x =
      -∫ x, g x * CKN.mixedSecond ψ i j x := by
  let q : ℝ := Real.conjExponent r
  have hq : 1 < q := by
    dsimp [q, Real.conjExponent]
    rw [lt_div_iff₀ (sub_pos.mpr hr)]
    linarith only [hr]
  have hHolder : r.HolderConjugate q := by
    exact Real.HolderConjugate.conjExponent hr
  have hlapc : HasCompactSupport (CKN.spatialLaplacian ψ) := by
    change HasCompactSupport (fun x => ∑ k : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv ψ k) k x)
    have hdc : ∀ {f : Vec3 → ℝ}, HasCompactSupport f → ∀ k : Fin 3,
        HasCompactSupport (CKN.spatialDeriv f k) :=
      fun hf k => hf.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k)
    convert
      ((hdc (hdc hψc 0) 0).add
        ((hdc (hdc hψc 1) 1).add
          (hdc (hdc hψc 2) 2))) using 1
    funext x
    simp [Fin.sum_univ_succ, Pi.add_apply]
  have hrhessc : HasCompactSupport (CKN.mixedSecond ψ i j) := by
    have hdc : ∀ {f : Vec3 → ℝ}, HasCompactSupport f → ∀ k : Fin 3,
        HasCompactSupport (CKN.spatialDeriv f k) :=
      fun hf k => hf.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k)
    exact hdc (hdc hψc j) i
  have hlap : MemLp (CKN.spatialLaplacian ψ) (ENNReal.ofReal q) volume :=
    (CKN.contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport hlapc
  have hhessMem : MemLp (CKN.mixedSecond ψ i j) (ENNReal.ofReal q) volume :=
    (CKN.contDiff_mixedSecond_smooth hψ i j).continuous.memLp_of_hasCompactSupport hrhessc
  have hrhs : MemLp (-CKN.mixedSecond ψ i j) (ENNReal.ofReal q) volume := hhessMem.neg
  let hInput := rieszPressureRawExtensionInput r hr i j
  let _ : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let _ : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq.le⟩
  let _ : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal q) :=
    hHolder.ennrealOfReal
  have hPairL2 := CKN.Core.Endgame.lpExtension_pairing_of_l2_identity
    (p := ENNReal.ofReal r) (q := ENNReal.ofReal q) ENNReal.ofReal_ne_top
    hInput hlap hrhs ?_ hgr
  · have hRep := CKN.Foundation.Euclidean.lpExtensionRepresentative_ae_eq_core
      ENNReal.ofReal_ne_top hInput hgr
    have hCoreOp := rieszPressureRawExtensionCore_eq_operator r hr i j
    have hCoreOpFun :
        (CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top hInput
          (hgr.toLp g) : Vec3 → ℝ) =ᵐ[volume]
          (rieszPressureOperator r hr i j (hgr.toLp g) : Vec3 → ℝ) :=
      (Lp.ext_iff).mp (congrArg (fun T => T (hgr.toLp g)) hCoreOp)
    calc
      ∫ x, rieszPressureOperator r hr i j (hgr.toLp g) x * CKN.spatialLaplacian ψ x =
          ∫ x, CKN.Foundation.Euclidean.lpExtensionRepresentative ENNReal.ofReal_ne_top
            hInput g x * CKN.spatialLaplacian ψ x := by
              apply integral_congr_ae
              filter_upwards [hRep, hCoreOpFun] with x hRepX hCoreX
              calc
                rieszPressureOperator r hr i j (hgr.toLp g) x * CKN.spatialLaplacian ψ x =
                    (CKN.Foundation.Euclidean.lpExtensionCore ENNReal.ofReal_ne_top
                      hInput (hgr.toLp g) : Vec3 → ℝ) x * CKN.spatialLaplacian ψ x := by
                        rw [← hCoreX]
                _ = CKN.Foundation.Euclidean.lpExtensionRepresentative ENNReal.ofReal_ne_top
                    hInput g x * CKN.spatialLaplacian ψ x := by rw [← hRepX]
      _ = ∫ x, g x * (-CKN.mixedSecond ψ i j x) := hPairL2
      _ = ∫ x, -(g x * CKN.mixedSecond ψ i j x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = -∫ x, g x * CKN.mixedSecond ψ i j x := integral_neg _
  · intro v hv2
    let hf : MemLp (v : Vec3 → ℝ) (ENNReal.ofReal r) volume := Lp.memLp v
    have hDist := rieszPressureOperator_laplacian_pairing r hr i j
      (v : Vec3 → ℝ) hf hv2 ψ hψ hψc
    have hRaw := rieszPressureOperator_ae_eq_negRaw r hr i j
      (v : Vec3 → ℝ) hf hv2
    have hTae : hInput.T (v : Vec3 → ℝ) =ᵐ[volume]
        fun x => rieszPressureOperator r hr i j (hf.toLp (v : Vec3 → ℝ)) x := by
      change (fun x => -CKN.Foundation.Euclidean.rieszSecondL2RawOperator
          (CKN.Foundation.Euclidean.rieszSecondL2Input i j) (v : Vec3 → ℝ) x) =ᵐ[volume]
        fun x => rieszPressureOperator r hr i j (hf.toLp (v : Vec3 → ℝ)) x
      exact hRaw.symm
    calc
      ∫ x, hInput.T (v : Vec3 → ℝ) x * CKN.spatialLaplacian ψ x =
          ∫ x, rieszPressureOperator r hr i j (hf.toLp (v : Vec3 → ℝ)) x *
            CKN.spatialLaplacian ψ x := by
              apply integral_congr_ae
              filter_upwards [hTae] with x hx
              rw [hx]
      _ = -∫ x, (v : Vec3 → ℝ) x * CKN.mixedSecond ψ i j x := hDist
      _ = ∫ x, (v : Vec3 → ℝ) x * (-CKN.mixedSecond ψ i j x) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with x
        ring

theorem rieszPressureSlice_laplacian_identity_of_memLp
    (r : ℝ) (hr : 1 < r) (F : Fin 3 → Fin 3 → Vec3 → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r) (volume : Measure Vec3))
    (ψ : Vec3 → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ x, (rieszPressureSlice r hr
        (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) x *
          (-CKN.spatialLaplacian ψ x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * CKN.mixedSecond ψ i j x := by
  let q : ℝ := Real.conjExponent r
  have hq : 1 < q := by
    dsimp [q, Real.conjExponent]
    rw [lt_div_iff₀ (sub_pos.mpr hr)]
    linarith only [hr]
  have hHolder : r.HolderConjugate q := Real.HolderConjugate.conjExponent hr
  have hlapc : HasCompactSupport (CKN.spatialLaplacian ψ) := by
    change HasCompactSupport (fun x => ∑ k : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv ψ k) k x)
    have hdc : ∀ {f : Vec3 → ℝ}, HasCompactSupport f → ∀ k : Fin 3,
        HasCompactSupport (CKN.spatialDeriv f k) :=
      fun hf k => hf.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k)
    convert
      ((hdc (hdc hψc 0) 0).add
        ((hdc (hdc hψc 1) 1).add
          (hdc (hdc hψc 2) 2))) using 1
    funext x
    simp [Fin.sum_univ_succ, Pi.add_apply]
  have hlap : MemLp (CKN.spatialLaplacian ψ) (ENNReal.ofReal q) volume :=
    (CKN.contDiff_spatialLaplacian_smooth hψ).continuous.memLp_of_hasCompactSupport hlapc
  have hInt (i j : Fin 3) : Integrable
      (fun x : Vec3 => rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
        CKN.spatialLaplacian ψ x) volume := by
    have : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hr.le⟩
    have : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hq.le⟩
    have : (ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q) :=
      hHolder.ennrealOfReal
    exact (Lp.memLp (rieszPressureOperator r hr i j ((hF i j).toLp (F i j)))).integrable_mul hlap
  have hInner (i : Fin 3) : Integrable
      (fun x : Vec3 => ∑ j : Fin 3,
        rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
          CKN.spatialLaplacian ψ x) volume := by
    rw [show (fun x : Vec3 => ∑ j : Fin 3,
      rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
        CKN.spatialLaplacian ψ x) =
      fun x => ∑ j ∈ Finset.univ,
        rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
          CKN.spatialLaplacian ψ x by simp]
    exact integrable_finsetSum Finset.univ (fun j hj => hInt i j)
  have hPsum :
      ∫ x, (rieszPressureSlice r hr
          (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) x *
            CKN.spatialLaplacian ψ x =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
          rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
            CKN.spatialLaplacian ψ x := by
    have hInnerAE (i : Fin 3) :
        (∑ j : Fin 3,
          rieszPressureOperator r hr i j ((hF i j).toLp (F i j))) =ᵐ[volume]
          fun x : Vec3 => ∑ j : Fin 3,
            rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x := by
      simpa using Lp.coeFn_fun_finsetSum Finset.univ
        (fun j => rieszPressureOperator r hr i j ((hF i j).toLp (F i j)))
    have hOuterAE :
        (rieszPressureSlice r hr
          (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) =ᵐ[volume]
          fun x : Vec3 => ∑ i : Fin 3,
            (∑ j : Fin 3,
              rieszPressureOperator r hr i j ((hF i j).toLp (F i j))) x := by
      simpa [rieszPressureSlice] using Lp.coeFn_fun_finsetSum Finset.univ
        (fun i => ∑ j : Fin 3,
          rieszPressureOperator r hr i j ((hF i j).toLp (F i j)))
    have hPae :
        (rieszPressureSlice r hr
          (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) =ᵐ[volume]
          fun x : Vec3 => ∑ i : Fin 3, ∑ j : Fin 3,
            rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x := by
      filter_upwards [hOuterAE, ae_all_iff.2 hInnerAE] with x hx hxi
      rw [hx]
      exact Finset.sum_congr rfl (fun i hi => hxi i)
    calc
      _ = ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
            rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
              CKN.spatialLaplacian ψ x := by
        apply integral_congr_ae
        filter_upwards [hPae] with x hx
        rw [hx, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ = ∑ i : Fin 3, ∫ x, ∑ j : Fin 3,
            rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
              CKN.spatialLaplacian ψ x := by
        rw [integral_finsetSum (s := Finset.univ) (f := fun i x =>
          ∑ j : Fin 3,
            rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
              CKN.spatialLaplacian ψ x) (fun i hi => hInner i)]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
            rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
              CKN.spatialLaplacian ψ x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum (s := Finset.univ) (f := fun j x =>
          rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
            CKN.spatialLaplacian ψ x) (fun j hj => hInt i j)]
  have hComp (i j : Fin 3) := rieszPressureOperator_laplacian_pairing_of_memLp
    r hr i j (F i j) (hF i j) ψ hψ hψc
  have hSum :
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
          rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
            CKN.spatialLaplacian ψ x =
        ∑ i : Fin 3, ∑ j : Fin 3, -∫ x, F i j x * CKN.mixedSecond ψ i j x := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hComp i j
  calc
    ∫ x, (rieszPressureSlice r hr
        (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) x *
          (-CKN.spatialLaplacian ψ x) =
        -∫ x, (rieszPressureSlice r hr
          (fun i j => (hF i j).toLp (F i j)) : Vec3 → ℝ) x *
            CKN.spatialLaplacian ψ x := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = -(∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
          rieszPressureOperator r hr i j ((hF i j).toLp (F i j)) x *
            CKN.spatialLaplacian ψ x) := by rw [hPsum]
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
          F i j x * CKN.mixedSecond ψ i j x := by
      rw [hSum]
      simp only [Finset.sum_neg_distrib, neg_neg]

end CKN.Leray

end
