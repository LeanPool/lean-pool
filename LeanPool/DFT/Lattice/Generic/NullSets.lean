/-
Copyright (c) 2026 Miguel A. L. Marques. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel A. L. Marques
-/

-- Modified for Lean Pool.

module

public import LeanPool.DFT.Lattice.Generic.Krylov
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Zero sets of polynomials are null; generic Hohenberg–Kohn (measure version)

* `volume_zeroSet`: the zero set of a nonzero real polynomial in finitely many variables is
  Lebesgue-null (Fubini induction on the number of variables).
* `generic_hk_ae`: under (H*), non-uniquely-v-representable potentials lie in a closed, nowhere
  dense, Lebesgue-null set.
-/

@[expose] public section

namespace DFT

section

open MeasureTheory MvPolynomial

theorem volume_zeroSet_fin : ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℝ), P ≠ 0 →
    volume {x : Fin n → ℝ | eval x P = 0} = 0
  | 0, P, hP => by
    have h : {x : Fin 0 → ℝ | eval x P = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hP
      apply MvPolynomial.funext
      intro y
      have hy : y = x := Subsingleton.elim _ _
      subst hy
      simp [hx]
    simp [h]
  | n + 1, P, hP => by
    set Q := finSuccEquiv ℝ n P with hQdef
    have hQ : Q ≠ 0 := by
      intro h
      apply hP
      have : finSuccEquiv ℝ n P = finSuccEquiv ℝ n 0 := by rw [← hQdef, h, map_zero]
      exact (finSuccEquiv ℝ n).injective this
    set q := Q.leadingCoeff
    have hq : q ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have ih := volume_zeroSet_fin n q hq
    -- the set in product coordinates
    have hcont : Continuous fun p : ℝ × (Fin n → ℝ) => eval
        (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) P := by
      refine (MvPolynomial.continuous_eval P).comp ?_
      refine continuous_pi fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
    set T : Set (ℝ × (Fin n → ℝ)) := {p | eval (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) P = 0}
    have hT : MeasurableSet T := (isClosed_eq hcont continuous_const).measurableSet
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he : ∀ x : Fin (n + 1) → ℝ, (Fin.cons (e x).1 (e x).2 : Fin (n + 1) → ℝ) = x := by
      intro x
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, MeasurableEquiv.piFinSuccAbove]
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.tail]
    have hS : {x : Fin (n + 1) → ℝ | eval x P = 0} = e ⁻¹' T := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, T, he]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0
    rw [hS, volume_pi, hmp.measure_preimage hT.nullMeasurableSet,
      Measure.prod_apply_symm hT]
    have hae : ∀ᵐ y ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)),
        volume ((fun x => (x, y)) ⁻¹' T) = 0 := by
      rw [← volume_pi]
      have hy0 : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)), eval y q ≠ 0 := by
        rw [ae_iff]; simpa using ih
      filter_upwards [hy0] with y hy
      have hmap : Polynomial.map (eval y) Q ≠ 0 := by
        intro h0
        have h1 := congrArg (fun p : Polynomial ℝ => p.coeff Q.natDegree) h0
        simp only [Polynomial.coeff_map, Polynomial.coeff_natDegree, Polynomial.coeff_zero] at h1
        exact hy h1
      apply Set.Finite.measure_zero
      apply (Polynomial.finite_setOfPred_isRoot hmap).subset
      intro x hx
      simp only [Set.mem_preimage, T, Set.mem_ofPred_eq] at hx
      rw [eval_eq_eval_mv_eval'] at hx
      exact hx
    rw [lintegral_congr_ae hae, lintegral_zero]

theorem volume_zeroSet {V : Type*} [Fintype V] {P : MvPolynomial V ℝ} (hP : P ≠ 0) :
    volume {x : V → ℝ | eval x P = 0} = 0 := by
  let f : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  set P' := rename f P with hP'def
  have hP' : P' ≠ 0 := by
    intro h
    apply hP
    apply rename_injective f f.injective
    rw [← hP'def, h, map_zero]
  have h0 := volume_zeroSet_fin _ P' hP'
  set g := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card V) => ℝ) f
  have key : {x : V → ℝ | eval x P = 0} = g ⁻¹' {y | eval y P' = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hP'def, eval_rename]
    have : ((g x : Fin (Fintype.card V) → ℝ) ∘ ⇑f) = x := by
      funext v
      change (g x) (f v) = x v
      simp [g, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [this]
  have hmeas : MeasurableSet {y : Fin (Fintype.card V) → ℝ | eval y P' = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P') continuous_const).measurableSet
  rw [key, volume_pi,
    (measurePreserving_piCongrLeft
        (fun _ : Fin (Fintype.card V) => (volume : Measure ℝ)) f).measure_preimage
      hmeas.nullMeasurableSet, ← volume_pi, h0]

variable {C V : Type*} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- **Generic Hohenberg–Kohn modulo trivial shifts, measure version (conditional on (H*)).** -/
theorem generic_hk_ae_mod {Tr : Set (V → ℝ)} {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm)
    {n : V → C → ℝ} (hR : RigidMod Tr n) (ord : C → ℕ) (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧
      {v | NonUVMod Tr H0 n v} ⊆ Z := by
  set Q := ∏ c, krylovPoly H0 n c ord
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hstar c)
  obtain ⟨hcl, hint⟩ := zeroSet_closed_nowhere hQ
  refine ⟨_, hcl, hint, volume_zeroSet hQ, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := nonUVMod_imp_krylov_zero hH0 hR hv ord
  change MvPolynomial.eval v Q = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) hc

omit [DecidableEq V] in
/-- **Generic Hohenberg–Kohn, measure version (conditional on (H*)).** Non-uniquely-v-representable
potentials lie in a closed, nowhere dense, Lebesgue-null set. -/
theorem generic_hk_ae {H0 : Matrix C C ℝ} (hH0 : H0.IsSymm) {n : V → C → ℝ} (hR : Rigid n)
    (ord : C → ℕ) (hstar : ∀ c, krylovPoly H0 n c ord ≠ 0) :
    ∃ Z : Set (V → ℝ), IsClosed Z ∧ interior Z = ∅ ∧ volume Z = 0 ∧ {v | NonUV H0 n v} ⊆ Z :=
  generic_hk_ae_mod (Tr := constPot) hH0 hR ord hstar

end

end DFT
