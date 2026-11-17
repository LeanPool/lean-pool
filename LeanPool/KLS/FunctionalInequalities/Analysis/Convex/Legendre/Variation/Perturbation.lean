/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.Basic

/-!
# Bounded perturbations of the Legendre transform

For a proper extended-real `φ`, a real perturbation `b` with `|b| ≤ M` and `t ∈ ℝ`, the actual
extended-real Legendre
supremum moves by at most `|t| M` in both directions, `φ* q − |t|M ≤ (φ + t b)* q ≤ φ* q + |t|M`,
with the whole `EReal`
supremum kept, infinite values included (`legendre_bounded_perturbation`); consequently, at a point
where `φ*` is finite, the
perturbed conjugates form a finite real curve within `|t| M` of `φ* y`
(`legendre_bounded_perturbation_finite_curve`), and
the effective domain of the conjugate is unchanged (`legendre_add_smul_ne_top_iff`). No
convexity or global finiteness of `φ` is assumed. Pointwise prerequisites of
Cordero-Erausquin–Klartag, arXiv:1304.0630v1,
(42).
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis

section BoundedPerturbation

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem legendre_bounded_perturbation_terms
    (φ : E → EReal) (hφ : ProperPotential φ) (b : E → ℝ)
    (t c : ℝ) (z q : E) (hc : |t * b z| ≤ c) :
    (inner ℝ z q : EReal) - (φ z + ((t * b z : ℝ) : EReal)) ≤
        (inner ℝ z q : EReal) - φ z + (c : EReal) ∧
      (inner ℝ z q : EReal) - φ z ≤
        (inner ℝ z q : EReal) - (φ z + ((t * b z : ℝ) : EReal)) +
          (c : EReal) := by
  have hupper : t * b z ≤ c := (abs_le.mp hc).2
  have hlower : -c ≤ t * b z := (abs_le.mp hc).1
  by_cases ht : φ z = ⊤
  · simp only [ht, EReal.top_add_coe, EReal.sub_top, EReal.bot_add, le_refl, and_self]
  · have hbot : φ z ≠ ⊥ := hφ.1 z
    let r : ℝ := (φ z).toReal
    have hr : (r : EReal) = φ z := EReal.coe_toReal ht hbot
    constructor
    · calc
        (inner ℝ z q : EReal) - (φ z + ((t * b z : ℝ) : EReal)) =
            ((inner ℝ z q - (r + t * b z) : ℝ) : EReal) := by
              rw [← hr, ← EReal.coe_add, ← EReal.coe_sub]
        _ ≤ ((inner ℝ z q - r + c : ℝ) : EReal) := by
              exact EReal.coe_le_coe_iff.mpr (by linarith)
        _ = (inner ℝ z q : EReal) - φ z + (c : EReal) := by
              rw [← hr, ← EReal.coe_sub, ← EReal.coe_add]
    · calc
        (inner ℝ z q : EReal) - φ z =
            ((inner ℝ z q - r : ℝ) : EReal) := by
              rw [← hr, ← EReal.coe_sub]
        _ ≤ ((inner ℝ z q - (r + t * b z) + c : ℝ) : EReal) := by
              exact EReal.coe_le_coe_iff.mpr (by linarith)
        _ = (inner ℝ z q : EReal) -
              (φ z + ((t * b z : ℝ) : EReal)) + (c : EReal) := by
              rw [← hr, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]


/-- An actual uniformly bounded real perturbation shifts the actual entire
Legendre sup by at most |t|M, without primal convexity or global finiteness. -/
theorem legendre_bounded_perturbation
    (φ : E → EReal) (hφ : ProperPotential φ)
    (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z : E, |b z| ≤ M) :
    ∀ (t : ℝ) (q : E),
      legendre φ q - ((|t| * M : ℝ) : EReal) ≤
          legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ∧
        legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
          legendre φ q + ((|t| * M : ℝ) : EReal) := by
    intro t q
    let c : ℝ := |t| * M
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    have hterm :
        ∀ z : E,
          (inner ℝ z q : EReal) -
                (φ z + ((t * b z : ℝ) : EReal)) ≤
              (inner ℝ z q : EReal) - φ z + (c : EReal) ∧
            (inner ℝ z q : EReal) - φ z ≤
              (inner ℝ z q : EReal) -
                  (φ z + ((t * b z : ℝ) : EReal)) + (c : EReal) := by
      intro z
      apply legendre_bounded_perturbation_terms φ hφ b t c z q ?_
      dsimp [c]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb z) (abs_nonneg t)
    constructor
    · apply
        (EReal.sub_le_iff_le_add
          (Or.inl (EReal.coe_ne_bot c))
          (Or.inl (EReal.coe_ne_top c))).2
      apply iSup_le
      intro z
      change (inner ℝ z q : EReal) - φ z ≤
        legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q + (c : EReal)
      exact (hterm z).2 |>.trans <|
        add_le_add (le_iSup (fun w : E =>
          (inner ℝ w q : EReal) -
            (φ w + ((t * b w : ℝ) : EReal))) z) le_rfl
    · change
        legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) q ≤
          legendre φ q + (c : EReal)
      apply iSup_le
      intro z
      change (inner ℝ z q : EReal) -
          (φ z + ((t * b z : ℝ) : EReal)) ≤
        legendre φ q + (c : EReal)
      exact (hterm z).1 |>.trans <|
        add_le_add (le_iSup (fun w : E =>
          (inner ℝ w q : EReal) - φ w) z) le_rfl

end InnerProduct

end BoundedPerturbation

section FiniteCurve

open Set

/-- A bounded real perturbation produces a finite real Legendre curve and its
real values remain within the actual uniform shift bound. -/
theorem legendre_bounded_perturbation_finite_curve {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (φ : E → EReal) (hφ : ProperPotential φ) (y : E)
    (hy : legendre φ y ≠ ⊤) (b : E → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ z : E, |b z| ≤ M) :
    ∀ t : ℝ,
      let ψ := legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
      ψ ≠ ⊤ ∧ ψ ≠ ⊥ ∧ |ψ.toReal - (legendre φ y).toReal| ≤ |t| * M := by
  intro t
  let c : ℝ := |t| * M
  let A : EReal := legendre φ y
  let P : EReal := legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
  change P ≠ ⊤ ∧ P ≠ ⊥ ∧ |P.toReal - A.toReal| ≤ c
  have hAbot : A ≠ ⊥ := legendre_ne_bot φ hφ y
  have hAcoe : (A.toReal : EReal) = A := EReal.coe_toReal hy hAbot
  have hsandwich := legendre_bounded_perturbation φ hφ b M hM hb t y
  have hlower : A - (c : EReal) ≤ P := by simpa [A, P, c] using hsandwich.1
  have hupper : P ≤ A + (c : EReal) := by simpa [A, P, c] using hsandwich.2
  have hlower' : ((A.toReal - c : ℝ) : EReal) ≤ P := by
    calc
      ((A.toReal - c : ℝ) : EReal) = A - (c : EReal) := by rw [EReal.coe_sub, hAcoe]
      _ ≤ P := hlower
  have hupper' : P ≤ ((A.toReal + c : ℝ) : EReal) := by
    calc
      P ≤ A + (c : EReal) := hupper
      _ = ((A.toReal + c : ℝ) : EReal) := by
        exact
          (congrArg (fun q : EReal => q + (c : EReal)) hAcoe).symm.trans
            (EReal.coe_add _ _).symm
  have hPtop : P ≠ ⊤ := by
    intro hP
    rw [hP] at hupper'
    exact (not_le_of_gt (EReal.coe_lt_top _)) hupper'
  have hPbot : P ≠ ⊥ := by
    intro hP
    rw [hP] at hlower'
    exact (not_le_of_gt (EReal.bot_lt_coe _)) hlower'
  have hlowerReal : A.toReal - c ≤ P.toReal := by
    have h := EReal.toReal_le_toReal hlower' (EReal.coe_ne_bot _) hPtop
    simpa only [EReal.toReal_coe] using h
  have hupperReal : P.toReal ≤ A.toReal + c := by
    have h := EReal.toReal_le_toReal hupper' hPbot (EReal.coe_ne_top _)
    simpa only [EReal.toReal_coe] using h
  refine ⟨hPtop, hPbot, ?_⟩
  rw [abs_le]
  constructor <;> linarith

end FiniteCurve

section Domain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A uniformly bounded real perturbation leaves the effective domain of the Legendre transform
unchanged: for a proper `φ`, `|b| ≤ M` and `t ∈ ℝ`, `(φ + t b)* x ≠ ⊤ ↔ φ* x ≠ ⊤`. -/
theorem legendre_add_smul_ne_top_iff {φ : E → EReal} (hφ : ProperPotential φ) {b : E → ℝ}
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z, |b z| ≤ M) (t : ℝ) (x : E) :
    legendre (fun z => φ z + ((t * b z : ℝ) : EReal)) x ≠ ⊤ ↔ legendre φ x ≠ ⊤ := by
  constructor
  · intro h htop
    have hlow := (legendre_bounded_perturbation φ hφ b M hM0 hM t x).1
    rw [htop, EReal.top_sub_coe] at hlow
    exact h (top_le_iff.mp hlow)
  · intro h
    exact (legendre_bounded_perturbation_finite_curve φ hφ x h b M hM0 hM t).1

end Domain

end FunctionalInequalities.Analysis
