/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145H2NumeratorData
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
C145 ordinary H2: actual fixed-three-variable grid unisolvence and the
literal numerator/residue inverse.

The public polynomial domain is the accepted support predicate Box n F.
The n=0 case is retained separately. Coordinates remain z=X 0, x=X 1,
y=X 2; tensor entry i j k therefore uses the vector ![-rates k,-rates i,-rates j].
Only injectivity of the individual real rates is needed. Neither positivity,
additive nonresonance, supplied reconstruction nor supplied grid uniqueness
occurs as a premise. The accepted numerator, gap product, Box, tensor symmetry
and polynomial symmetry definitions are imported unchanged.

This module does not yet join Xi quotients to the response kernel, derive
moment cancellations or assert any physical/continuum recovery theorem.
-/

@[expose] public section

noncomputable section

namespace C145.H2

open MvPolynomial C145.ThreePlane
open scoped BigOperators

variable {n : ℕ}

/-- The actual support Box is stable under subtraction, including n=0. -/
theorem box_sub {F G : P3} (hF : Box n F) (hG : Box n G) : Box n (F - G) := by
  classical
  intro m hm r
  rcases Finset.mem_union.mp (MvPolynomial.support_sub (Fin 3) F G hm) with hmF | hmG
  · exact hF m hmF r
  · exact hG m hmG r

/-- Isolate coordinate zero after a permutation, then evaluate the other
two variables in ℝ. This helper is confined to the accepted fixed Fin 3 ring. -/
private def realSlice (e : Equiv.Perm (Fin 3)) (F : P3) (v : Fin 2 → ℝ) :
    Polynomial ℝ :=
  Polynomial.map (MvPolynomial.eval v) (finSuccEquiv ℝ 2 (rename e F))

private theorem eval_realSlice (e : Equiv.Perm (Fin 3)) (F : P3)
    (v : Fin 2 → ℝ) (u : ℝ) :
    (realSlice e F v).eval u =
      MvPolynomial.eval ((Fin.cons u v : Fin 3 → ℝ) ∘ e) F := by
  unfold realSlice
  rw [← MvPolynomial.eval_eq_eval_mv_eval', MvPolynomial.eval_rename]

/-- Partial real evaluation cannot increase the isolated coordinate degree.
No coefficient-bound hypothesis is introduced: the bound comes from Box. -/
private theorem realSlice_natDegree_lt (hn : 0 < n) (F : P3) (hF : Box n F)
    (e : Equiv.Perm (Fin 3)) (v : Fin 2 → ℝ) :
    (realSlice e F v).natDegree < n := by
  have he : degreeOf (0 : Fin 3) (rename e F) = degreeOf (e.symm 0) F := by
    simpa only [e.apply_symm_apply] using
      (degreeOf_rename_of_injective (p := F) e.injective (e.symm 0))
  calc
    (realSlice e F v).natDegree ≤
        (finSuccEquiv ℝ 2 (rename e F)).natDegree := Polynomial.natDegree_map_le
    _ = degreeOf (0 : Fin 3) (rename e F) := natDegree_finSuccEquiv _
    _ = degreeOf (e.symm 0) F := he
    _ < n := (box_iff_degree_lt hn F).mp hF (e.symm 0)

/-- One real line is determined by its n distinct negative-rate nodes.
The finset cardinal is the actual n; no selected/root-list premise occurs. -/
private theorem realLine_zero (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hn : 0 < n) (F : P3) (hF : Box n F)
    (e : Equiv.Perm (Fin 3)) (v : Fin 2 → ℝ)
    (hnode : ∀ i : Fin n,
      MvPolynomial.eval ((Fin.cons (-rates i) v : Fin 3 → ℝ) ∘ e) F = 0)
    (u : ℝ) :
    MvPolynomial.eval ((Fin.cons u v : Fin 3 → ℝ) ∘ e) F = 0 := by
  classical
  have hi : Function.Injective (fun i : Fin n => -rates i) := by
    intro i j hij
    exact hRates (neg_injective hij)
  have hp : realSlice e F v = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      (Finset.univ : Finset (Fin n)) hi.injOn
    · have hnat := realSlice_natDegree_lt hn F hF e v
      have hcast : ((realSlice e F v).natDegree : WithBot ℕ) < (n : WithBot ℕ) :=
        WithBot.coe_lt_coe.mpr hnat
      have hdeg := (Polynomial.degree_le_natDegree (p := realSlice e F v)).trans_lt hcast
      simpa only [Finset.card_univ, Fintype.card_fin] using hdeg
    · intro i hi
      rw [eval_realSlice]
      exact hnode i
  rw [← eval_realSlice, hp, Polynomial.eval_zero]

/-- Actual all-n finite-grid unisolvence in the fixed three-variable ring.
Three successive finite-root arguments free z, then x, then y. -/
theorem box_grid_eq_zero (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (F : P3) (hF : Box n F)
    (hgrid : ∀ i j k : Fin n,
      MvPolynomial.eval ![-rates k, -rates i, -rates j] F = 0) : F = 0 := by
  by_cases hn : n = 0
  · subst n
    exact (box_zero_iff F).mp hF
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hz (i j : Fin n) (u : ℝ) :
        MvPolynomial.eval ![u, -rates i, -rates j] F = 0 := by
      have hnode (k : Fin n) :
          MvPolynomial.eval
            ((Fin.cons (-rates k) ![-rates i, -rates j] : Fin 3 → ℝ) ∘
              Equiv.refl (Fin 3)) F = 0 := by
        have hv :
            (Fin.cons (-rates k) ![-rates i, -rates j] : Fin 3 → ℝ) ∘
                Equiv.refl (Fin 3) = ![-rates k, -rates i, -rates j] := by
          funext r
          fin_cases r <;> rfl
        rw [hv]
        exact hgrid i j k
      have h := realLine_zero rates hRates hnpos F hF
        (Equiv.refl (Fin 3)) ![-rates i, -rates j] hnode u
      have hv : (Fin.cons u ![-rates i, -rates j] : Fin 3 → ℝ) ∘
          Equiv.refl (Fin 3) = ![u, -rates i, -rates j] := by
        funext r
        fin_cases r <;> rfl
      rw [hv] at h
      exact h
    have hx (j : Fin n) (u v : ℝ) :
        MvPolynomial.eval ![u, v, -rates j] F = 0 := by
      have hnode (i : Fin n) :
          MvPolynomial.eval
            ((Fin.cons (-rates i) ![u, -rates j] : Fin 3 → ℝ) ∘
              Equiv.swap 0 1) F = 0 := by
        have hv : (Fin.cons (-rates i) ![u, -rates j] : Fin 3 → ℝ) ∘
            Equiv.swap 0 1 = ![u, -rates i, -rates j] := by
          funext r
          fin_cases r <;> simp [Function.comp_apply, Equiv.swap_apply_def]
        rw [hv]
        exact hz i j u
      have h := realLine_zero rates hRates hnpos F hF
        (Equiv.swap 0 1) ![u, -rates j] hnode v
      have hv : (Fin.cons v ![u, -rates j] : Fin 3 → ℝ) ∘
          Equiv.swap 0 1 = ![u, v, -rates j] := by
        funext r
        fin_cases r <;> simp [Function.comp_apply, Equiv.swap_apply_def]
      rw [hv] at h
      exact h
    have hy (u v w : ℝ) : MvPolynomial.eval ![u, v, w] F = 0 := by
      have hnode (j : Fin n) :
          MvPolynomial.eval
            ((Fin.cons (-rates j) ![v, u] : Fin 3 → ℝ) ∘
              Equiv.swap 0 2) F = 0 := by
        have hv : (Fin.cons (-rates j) ![v, u] : Fin 3 → ℝ) ∘
            Equiv.swap 0 2 = ![u, v, -rates j] := by
          funext r
          fin_cases r <;> simp [Function.comp_apply, Equiv.swap_apply_def]
        rw [hv]
        exact hx j u v
      have h := realLine_zero rates hRates hnpos F hF
        (Equiv.swap 0 2) ![v, u] hnode w
      have hv : (Fin.cons w ![v, u] : Fin 3 → ℝ) ∘
          Equiv.swap 0 2 = ![u, v, w] := by
        funext r
        fin_cases r <;> simp [Function.comp_apply, Equiv.swap_apply_def]
      rw [hv] at h
      exact h
    apply MvPolynomial.funext
    intro w
    have hw : w = ![w 0, w 1, w 2] := by
      funext r
      fin_cases r <;> rfl
    rw [hw, map_zero]
    exact hy (w 0) (w 1) (w 2)

/-- Box polynomials agreeing on all n^3 actual negative-node values agree. -/
theorem box_grid_ext (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    {F G : P3} (hF : Box n F) (hG : Box n G)
    (hgrid : ∀ i j k : Fin n,
      MvPolynomial.eval ![-rates k, -rates i, -rates j] F =
        MvPolynomial.eval ![-rates k, -rates i, -rates j] G) : F = G := by
  apply sub_eq_zero.mp
  apply box_grid_eq_zero rates hRates (F - G) (box_sub hF hG)
  intro i j k
  rw [map_sub, hgrid i j k, sub_self]

/-- The literal source residue inverse, with x-input/y-input/z-output order.
Its denominator is the accepted oriented product, equal to D' at the node. -/
def gridResidue (rates : Fin n → ℝ) (F : P3) : Tensor n :=
  fun i j k => MvPolynomial.eval ![-rates k, -rates i, -rates j] F /
    (di rates i * di rates j * di rates k)

/-- Direct grid evaluation proves the tensor-side inverse. -/
theorem gridResidue_numerator (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) :
    gridResidue rates (numerator rates E) = E := by
  funext i j k
  unfold gridResidue
  rw [numerator_eval_grid]
  field_simp [di_ne_zero rates hRates i, di_ne_zero rates hRates j,
    di_ne_zero rates hRates k]


/-- The actual Box condition and finite-grid theorem prove the polynomial
side inverse. Reconstruction is a conclusion, including n=0. -/
theorem numerator_gridResidue (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (F : P3) (hF : Box n F) :
    numerator rates (gridResidue rates F) = F := by
  apply box_grid_ext rates hRates (numerator_box rates _) hF
  intro i j k
  rw [numerator_eval_grid]
  unfold gridResidue
  field_simp [di_ne_zero rates hRates i, di_ne_zero rates hRates j,
    di_ne_zero rates hRates k]


/-- Uniqueness in the actual Box domain, without tensor symmetry. -/
theorem gridResidue_injective_on_box (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) {F G : P3} (hF : Box n F) (hG : Box n G)
    (h : gridResidue rates F = gridResidue rates G) : F = G := by
  calc
    F = numerator rates (gridResidue rates F) := (numerator_gridResidue rates hRates F hF).symm
    _ = numerator rates (gridResidue rates G) := congrArg (numerator rates) h
    _ = G := numerator_gridResidue rates hRates G hG

/-- Exact forward/backward inverse characterization on the actual domain. -/
theorem numerator_eq_iff_gridResidue (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) (F : P3) (hF : Box n F) :
    numerator rates E = F ↔ E = gridResidue rates F := by
  constructor
  · intro h
    calc
      E = gridResidue rates (numerator rates E) := (gridResidue_numerator rates hRates E).symm
      _ = gridResidue rates F := congrArg (gridResidue rates) h
  · rintro rfl
    exact numerator_gridResidue rates hRates F hF

theorem existsUnique_numerator (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (F : P3) (hF : Box n F) :
    ∃! E : Tensor n, numerator rates E = F := by
  refine ⟨gridResidue rates F, numerator_gridResidue rates hRates F hF, ?_⟩
  intro E hE
  exact (numerator_eq_iff_gridResidue rates hRates E F hF).mp hE

private theorem gridVector_eq (rates : Fin n → ℝ) (a : Fin 3 → Fin n) :
    ![-rates (a 0), -rates (a 1), -rates (a 2)] =
      (fun r : Fin 3 => -rates (a r)) := by
  funext r
  fin_cases r <;> rfl

private theorem gapDen_eq_prod (rates : Fin n → ℝ) (a : Fin 3 → Fin n) :
    di rates (a 1) * di rates (a 2) * di rates (a 0) =
      ∏ r : Fin 3, di rates (a r) := by
  simp [Fin.prod_univ_succ]; ring

/-- The three-gap denominator is fully symmetric even before injection. -/
theorem gapDen_permute (rates : Fin n → ℝ) (e : Equiv.Perm (Fin 3))
    (a : Fin 3 → Fin n) :
    di rates ((a ∘ e) 1) * di rates ((a ∘ e) 2) * di rates ((a ∘ e) 0) =
      di rates (a 1) * di rates (a 2) * di rates (a 0) := by
  rw [gapDen_eq_prod, gapDen_eq_prod]
  exact _root_.Equiv.prod_comp e (fun r => di rates (a r))

/-- Polynomial symmetry transfers to every tensor slot of the actual
residue. No Box/injection premise is needed just to establish symmetry. -/
theorem gridResidue_symmetric (rates : Fin n → ℝ) (F : P3) (hF : SymPoly F) :
    FullSymTensor (gridResidue rates F) := by
  intro e a
  change
    MvPolynomial.eval
        ![-rates ((a ∘ e) 0), -rates ((a ∘ e) 1), -rates ((a ∘ e) 2)] F /
        (di rates ((a ∘ e) 1) * di rates ((a ∘ e) 2) * di rates ((a ∘ e) 0)) =
      MvPolynomial.eval ![-rates (a 0), -rates (a 1), -rates (a 2)] F /
        (di rates (a 1) * di rates (a 2) * di rates (a 0))
  have heval :
      MvPolynomial.eval (fun r : Fin 3 => -rates ((a ∘ e) r)) F =
        MvPolynomial.eval (fun r : Fin 3 => -rates (a r)) F := by
    have h := congrArg (MvPolynomial.eval (fun r : Fin 3 => -rates (a r))) (hF e)
    rw [MvPolynomial.eval_rename] at h
    exact h
  rw [gridVector_eq, gridVector_eq, heval, gapDen_permute]

/-- The accepted forward symmetry and the new actual inverse give the
exact full-symmetry correspondence. -/
theorem numerator_symmetric_iff (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (E : Tensor n) :
    SymPoly (numerator rates E) ↔ FullSymTensor E := by
  constructor
  · intro h
    have hsym := gridResidue_symmetric rates (numerator rates E) h
    rw [gridResidue_numerator rates hRates E] at hsym
    exact hsym
  · exact numerator_symmetric rates E

/-- Every symmetric actual Box polynomial has exactly one fully symmetric
tensor preimage, supplied by its explicit negative-node residues. -/
theorem existsUnique_symmetric_numerator (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (F : P3) (hBox : Box n F) (hSym : SymPoly F) :
    ∃! E : Tensor n, FullSymTensor E ∧ numerator rates E = F := by
  refine ⟨gridResidue rates F,
    ⟨gridResidue_symmetric rates F hSym, numerator_gridResidue rates hRates F hBox⟩, ?_⟩
  intro E hE
  exact (numerator_eq_iff_gridResidue rates hRates E F hBox).mp hE.2


end C145.H2

end
