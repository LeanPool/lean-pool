/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Ftau.Ftau
public import LeanPool.HyperellipticCurves.Series.Interpolation
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Towards the basic laws of the translated group law (blueprint `lem:Ftau-basic`)

The `Y = 0` specialization of the `F_τ` pipeline: `ChabautyColeman.setYZero` substitutes
`X i` for the `inl` variables and `0` for the `inr` variables (built on the substitution
API — `MvPowerSeries.killCompl` is `no_expose`, so its coefficient formula is not usable
here). Under `setYZero` the transported chart data specialize to `(chartU, chartV)` on the
`X`-side and to the constant `τ`-datum on the `Y`-side
(`ChabautyColeman.ftauUX_map_setYZero` … `ChabautyColeman.ftauVY_map_setYZero`): at
`Y = 0` the pipeline computes `ch(X) + τ - τ`.

The unit law `F_τ(X, 0) = X` is established at the fold
(`ChabautyColeman.setYZero_FtauFold`, `LeanPool.HyperellipticCurves.Log.Fold.FtauFoldBasic`). The
mirror
specialization `ChabautyColeman.setXZero` needs no separate analysis: it is `setYZero`
after swapping the two variable blocks (`ChabautyColeman.setYZero_comp_rename_swap`), so
the symmetric unit law comes from the unit law and commutativity.
-/

@[expose] public section

open Polynomial MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

namespace ChabautyColeman

section SubstZero

variable {O : Type*} [CommRing O]

/-- Substituting `0` for every variable extracts the constant term. -/
theorem subst_zero_eq_C_constantCoeff {σ τ : Type*} [Finite σ] (f : MvPowerSeries σ O) :
    MvPowerSeries.subst (fun _ : σ ↦ (0 : MvPowerSeries τ O)) f
      = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
  ext e
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero f e]
  classical
  rw [finsum_eq_single _ (0 : σ →₀ ℕ) ?_]
  · rcases eq_or_ne e 0 with rfl | he
    · simp [MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.constantCoeff_C]
    · simp [MvPowerSeries.coeff_one, MvPowerSeries.coeff_C, he]
  · intro d hd
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
    have h0 : (d.prod fun _ k ↦ (0 : MvPowerSeries τ O) ^ k) = 0 :=
      Finset.prod_eq_zero hi (zero_pow (Finsupp.mem_support_iff.mp hi))
    rw [h0, map_zero, smul_zero]

end SubstZero

section SetYZero

variable {O : Type*} [CommRing O] {n : ℕ}

theorem hasSubst_elim_X_zero :
    MvPowerSeries.HasSubst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
        Fin n ⊕ Fin n → MvPowerSeries (Fin n) O) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)

/-- The `Y = 0` specialization: substitute `X i` for the `inl` variables and `0` for the
`inr` variables. -/
noncomputable def setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O :=
  (MvPowerSeries.substAlgHom hasSubst_elim_X_zero).toRingHom

theorem setYZero_apply (p : MvPowerSeries (Fin n ⊕ Fin n) O) :
    setYZero p = MvPowerSeries.subst (Sum.elim MvPowerSeries.X (fun _ ↦ 0)) p :=
  MvPowerSeries.substAlgHom_apply hasSubst_elim_X_zero p

theorem setYZero_comp_rename_inl :
    (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O).comp
        (MvPowerSeries.rename (Sum.inl : Fin n → Fin n ⊕ Fin n)).toRingHom
      = RingHom.id (MvPowerSeries (Fin n) O) := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    setYZero_apply, MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.X_comp Sum.inl :
        MvPowerSeries.HasSubst (MvPowerSeries.X ∘ (Sum.inl : Fin n → Fin n ⊕ Fin n) :
          Fin n → MvPowerSeries (Fin n ⊕ Fin n) O)) hasSubst_elim_X_zero]
  have hfam : (fun i : Fin n ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
        Fin n ⊕ Fin n → MvPowerSeries (Fin n) O)
      ((MvPowerSeries.X ∘ Sum.inl : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O) i))
      = MvPowerSeries.X := by
    funext i
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_elim_X_zero]
    rfl
  rw [hfam, ← MvPowerSeries.map_algebraMap_eq_subst_X]
  simp [MvPowerSeries.map_id]

theorem setYZero_comp_rename_inr :
    (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O).comp
        (MvPowerSeries.rename (Sum.inr : Fin n → Fin n ⊕ Fin n)).toRingHom
      = (MvPowerSeries.C).comp (MvPowerSeries.constantCoeff) := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, setYZero_apply,
    MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.X_comp Sum.inr :
        MvPowerSeries.HasSubst (MvPowerSeries.X ∘ (Sum.inr : Fin n → Fin n ⊕ Fin n) :
          Fin n → MvPowerSeries (Fin n ⊕ Fin n) O)) hasSubst_elim_X_zero]
  have hfam : (fun i : Fin n ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
        Fin n ⊕ Fin n → MvPowerSeries (Fin n) O)
      ((MvPowerSeries.X ∘ Sum.inr : Fin n → MvPowerSeries (Fin n ⊕ Fin n) O) i))
      = fun _ ↦ (0 : MvPowerSeries (Fin n) O) := by
    funext i
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_elim_X_zero]
    rfl
  rw [hfam, subst_zero_eq_C_constantCoeff]
  rfl

theorem setYZero_comp_C :
    (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O).comp
        MvPowerSeries.C = MvPowerSeries.C := by
  refine RingHom.ext fun a ↦ ?_
  simp [setYZero_apply]

/-- The constant coefficient is unchanged by setting `Y = 0`. -/
theorem constantCoeff_setYZero (p : MvPowerSeries (Fin n ⊕ Fin n) O) :
    MvPowerSeries.constantCoeff (setYZero p) = MvPowerSeries.constantCoeff p := by
  rw [setYZero_apply]
  exact MvPowerSeries.constantCoeff_subst_of_constantCoeff_zero hasSubst_elim_X_zero
    (by rintro (j | j) <;> simp) p

end SetYZero

section YZeroData

variable {O : Type*} [CommRing O] {n : ℕ} {f u v w c₁ c₂ : O[X]}

theorem ftauUX_map_setYZero :
    (ftauUX u n).map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)
      = chartU u n := by
  rw [ftauUX, Polynomial.map_map, setYZero_comp_rename_inl, Polynomial.map_id]

theorem ftauUY_map_setYZero :
    (ftauUY u n).map (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)
      = u.map MvPowerSeries.C := by
  rw [ftauUY, Polynomial.map_map, setYZero_comp_rename_inr, ← Polynomial.map_map,
    chartU_map_constantCoeff]

variable [Nontrivial O] (hu : u.Monic) (hne : u.natDegree = n) (hv : v.degree < u.degree)
  (hw : v ^ 2 - f = u * w) (hbez : c₁ * u + c₂ * (2 * v) = 1)

theorem ftauVX_map_setYZero :
    (ftauVX hu hne hv hw hbez).map
      (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)
      = chartV hu hne.ge hv hw hbez := by
  rw [ftauVX, Polynomial.map_map, setYZero_comp_rename_inl, Polynomial.map_id]

theorem ftauVY_map_setYZero :
    (ftauVY hu hne hv hw hbez).map
      (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O)
      = v.map MvPowerSeries.C := by
  rw [ftauVY, Polynomial.map_map, setYZero_comp_rename_inr, ← Polynomial.map_map,
    chartV_map_constantCoeff]

end YZeroData

section SetXZero

variable {O : Type*} [CommRing O] {n : ℕ}

theorem hasSubst_elim_zero_X :
    MvPowerSeries.HasSubst
      (Sum.elim (fun _ ↦ 0) MvPowerSeries.X :
        Fin n ⊕ Fin n → MvPowerSeries (Fin n) O) :=
  hasSubst_of_constantCoeff_zero (by rintro (i | i) <;> simp)

/-- The `X = 0` specialization: substitute `0` for the `inl` variables and `X i` for the
`inr` variables. -/
noncomputable def setXZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O :=
  (MvPowerSeries.substAlgHom hasSubst_elim_zero_X).toRingHom

theorem setXZero_apply (p : MvPowerSeries (Fin n ⊕ Fin n) O) :
    setXZero p = MvPowerSeries.subst (Sum.elim (fun _ ↦ 0) MvPowerSeries.X) p :=
  MvPowerSeries.substAlgHom_apply hasSubst_elim_zero_X p

/-- Setting `X = 0` is setting `Y = 0` after swapping the two variable blocks. -/
theorem setYZero_comp_rename_swap :
    (setYZero : MvPowerSeries (Fin n ⊕ Fin n) O →+* MvPowerSeries (Fin n) O).comp
        (MvPowerSeries.rename (Sum.swap : Fin n ⊕ Fin n → Fin n ⊕ Fin n)).toRingHom
      = setXZero := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, setYZero_apply,
    MvPowerSeries.rename_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.HasSubst.X_comp Sum.swap :
        MvPowerSeries.HasSubst (MvPowerSeries.X ∘
          (Sum.swap : Fin n ⊕ Fin n → Fin n ⊕ Fin n) :
          Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) O)) hasSubst_elim_X_zero,
    setXZero_apply]
  have hfam : (fun s : Fin n ⊕ Fin n ↦ MvPowerSeries.subst
      (Sum.elim MvPowerSeries.X (fun _ ↦ 0) :
        Fin n ⊕ Fin n → MvPowerSeries (Fin n) O)
      ((MvPowerSeries.X ∘ Sum.swap : Fin n ⊕ Fin n → MvPowerSeries (Fin n ⊕ Fin n) O) s))
      = Sum.elim (fun _ ↦ 0) MvPowerSeries.X := by
    funext s
    rw [Function.comp_apply, MvPowerSeries.subst_X hasSubst_elim_X_zero]
    cases s <;> rfl
  rw [hfam]

end SetXZero

section RenameCont

variable {O : Type*} [CommRing O] [UniformSpace O] [IsTopologicalRing O]

/-- Renaming variables is continuous for the product topologies. -/
theorem continuous_rename' {σ τ : Type*} (e : σ → τ) [Filter.TendstoCofinite e] :
    Continuous (MvPowerSeries.rename (R := O) e :
      MvPowerSeries σ O → MvPowerSeries τ O) := by
  refine continuous_pi fun x ↦ ?_
  change Continuous fun h : MvPowerSeries σ O ↦
    MvPowerSeries.coeff x (MvPowerSeries.rename e h)
  have heq : (fun h : MvPowerSeries σ O ↦
        MvPowerSeries.coeff x (MvPowerSeries.rename e h))
      = fun h ↦ ∑ d ∈ (Filter.TendstoCofinite.finite_preimage_singleton
          (Finsupp.mapDomain e) x).toFinset, MvPowerSeries.coeff d h := by
    funext h
    exact MvPowerSeries.coeff_rename _ h x
  rw [heq]
  exact continuous_finsetSum _ fun d _ ↦ MvPowerSeries.WithPiTopology.continuous_coeff O d

end RenameCont

section EvalRename

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (IsLocalRing.maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O]

/-- Evaluation after a variable rename is evaluation at the composed point. -/
theorem evalRingHom_comp_rename {σ τ : Type*} {z : τ → O} (hz : MvPowerSeries.HasEval z)
    (e : σ → τ) [Filter.TendstoCofinite e] (hze : MvPowerSeries.HasEval (z ∘ e)) :
    (MvPSeries.evalRingHom hz).comp (MvPowerSeries.rename (R := O) e).toRingHom
      = MvPSeries.evalRingHom hze := by
  refine RingHom.ext fun p ↦ ?_
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPSeries.evalRingHom_apply, MvPSeries.evalRingHom_apply]
  have h := MvPSeries.eval_algHom hz (continuous_rename' e) p
  have hfam : (fun s ↦ MvPSeries.eval z ((MvPowerSeries.rename (R := O) e)
      (MvPowerSeries.X s))) = z ∘ e := by
    funext s
    rw [MvPowerSeries.rename_X, MvPSeries.eval_X]
    rfl
  rwa [hfam] at h

/-- Evaluation after a variable rename, followed by a coefficient map, is evaluation at the
composed point. -/
theorem comp_evalRingHom_comp_rename {σ τ : Type*} {z : τ → O} (hz : MvPowerSeries.HasEval z)
    (e : σ → τ) [Filter.TendstoCofinite e] (hze : MvPowerSeries.HasEval (z ∘ e))
    {A : Type*} [CommRing A] (φ : O →+* A) :
    (φ.comp (MvPSeries.evalRingHom hz)).comp (MvPowerSeries.rename (R := O) e).toRingHom
      = φ.comp (MvPSeries.evalRingHom hze) := by
  rw [RingHom.comp_assoc, evalRingHom_comp_rename hz e hze]

/-- Evaluation after a variable rename is evaluation at the composed point, on elements. -/
theorem eval_rename {σ τ : Type*} {z : τ → O} (hz : MvPowerSeries.HasEval z) (e : σ → τ)
    [Filter.TendstoCofinite e] (hze : MvPowerSeries.HasEval (z ∘ e)) (p : MvPowerSeries σ O) :
    MvPSeries.eval z (MvPowerSeries.rename e p) = MvPSeries.eval (z ∘ e) p := by
  have h := RingHom.congr_fun (evalRingHom_comp_rename hz e hze) p
  rwa [RingHom.comp_apply, MvPSeries.evalRingHom_apply, MvPSeries.evalRingHom_apply] at h

end EvalRename

end ChabautyColeman

end
