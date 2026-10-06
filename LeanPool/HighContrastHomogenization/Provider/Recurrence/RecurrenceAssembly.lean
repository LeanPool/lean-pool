/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Recurrence.FiniteRangeAveraging
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.PositiveGapClosure

/-!
# High-contrast homogenization: Provider.Recurrence.RecurrenceAssembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `p.fixed.geometry.parent.child.recurrence`

The fixed-grid recurrence is assembled here from the estimates of the section.
On one deterministic rounded adapted grid `q` of alignment `ℓ`, at a child scale
`j ≥ ℓ` and a parent scale `p = j + h` above it, the parent cell is partitioned
by `3^{dh}` aligned children; write `Ĝ` for the average of the responses over
those children, `E_j` and `E_p` for the two adapted means and
`Δ = Δ_{j,p}^q` for the determinant increment.

Four displays are composed.

*The averaging step.*  The centred average `Ĝ - E_j`, normalized by the child
mean, has mixed norm at most `C(d,Q) 3^{-hd/2}` times the child moment `v_j^q`;
this is `l.fixed.geometry.matrix.averaging` read at the aligned subdivision,
whose cardinality `3^{dh}` supplies the printed gain.

*The transport of the normalization.*  The mean order `E_p ≤ E_j` and the ideal
property of the Schatten norm carry that estimate from the child normalization
to the parent one, at the cost of `(2d)^{1/Q}e^{Δ}`.

*The positive gap.*  Pathwise `0 ≤ 𝐀_p ≤ Ĝ`, so the normalized excess
`D = (Ĝ - 𝐀_p)^~` is positive with mean `B = P_{j,p}^q - I`; the determinant
transport bounds the spectral size of `P_{j,p}^q` by `e^{Δ}` and its trace gap by
`e^{Δ} - 1`.  The positive-gap estimate then bounds the parent moment by
`C(y + Φ_Q(Δ))`, where `y` is the transported mixed norm of the centred average.

*The gain.*  Substituting the transported bound for `y` produces the printed
contraction: a geometric factor `3^{-hd/2}e^{Δ}` on the child moment plus the
increment's own gain `Φ_Q(Δ)`, both carrying one constant `C_rec(d, Q)`.

The mixed norms are `ℝ≥0∞`-valued, and the passage to the real inequalities the
positive-gap estimate is stated in is made on the finiteness hypotheses the
proposition carries.  The exponent `Q` is an even integer, which is what makes
the Schatten size a continuous function of the entries: the inner power `Q/2` of
`|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}` is then an integer, the functional calculus
collapses to a matrix power and the trace is a polynomial.  That is the content
of the opening section.
-/

namespace HCPolySupport
namespace HighContrast
namespace Recurrence

open MeasureTheory

open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator Matrix

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the Schatten size at an even exponent -/

section Entries

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The entries of a matrix power are polynomials in the entries. -/
theorem aestronglyMeasurable_entry_pow {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) :
    ∀ (k : ℕ) (i j : n), AEStronglyMeasurable (fun a => (F a ^ k) i j) μ := by
  intro k
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero]
      exact aestronglyMeasurable_const
  | succ k ih =>
      intro i j
      simp only [pow_succ]
      exact aestronglyMeasurable_entry_mul ih h i j

omit [DecidableEq n] in
/-- The entries of a two-sided constant congruence are linear in the entries. -/
theorem aestronglyMeasurable_entry_conj (S : Matrix n n ℝ) {F : Ω → Matrix n n ℝ}
    (h : ∀ i j, AEStronglyMeasurable (fun a => F a i j) μ) (i j : n) :
    AEStronglyMeasurable (fun a => (S * F a * S) i j) μ := by
  have hS : ∀ i j : n, AEStronglyMeasurable (fun _ : Ω => S i j) μ :=
    fun _ _ => aestronglyMeasurable_const
  have hSF : ∀ i j : n, AEStronglyMeasurable (fun a => (S * F a) i j) μ :=
    aestronglyMeasurable_entry_mul (F := fun _ => S) (G := F) hS h
  exact aestronglyMeasurable_entry_mul (F := fun a => S * F a) (G := fun _ => S) hSF hS i j

end Entries

/-- The entries of a normalized difference of two random doubled blocks are
measurable as soon as the entries of the two blocks are: normalization and
subtraction are a fixed real-linear map of the entries. -/
theorem aestronglyMeasurable_entry_normalizedBlock_blockSub {P : Measure (CoeffSpace d)}
    {X Y : CoeffSpace d → BlockMat d} (F : BlockMat d)
    (hX : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => toFullBlockMat (X a) α β) P)
    (hY : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => toFullBlockMat (Y a) α β) P)
    (α β : BlockCoord d) :
    AEStronglyMeasurable
      (fun a => toFullBlockMat (normalizedBlock (blockSub (X a) (Y a)) F) α β) P := by
  have hsub : ∀ γ δ : BlockCoord d, AEStronglyMeasurable
      (fun a => (toFullBlockMat (X a) - toFullBlockMat (Y a)) γ δ) P := by
    intro γ δ
    simpa only [Matrix.sub_apply] using! (hX γ δ).sub (hY γ δ)
  have hfun : (fun a : CoeffSpace d =>
        toFullBlockMat (normalizedBlock (blockSub (X a) (Y a)) F) α β)
      = fun a : CoeffSpace d => (matSqrt (toFullBlockMat F)⁻¹ *
          (toFullBlockMat (X a) - toFullBlockMat (Y a)) *
          matSqrt (toFullBlockMat F)⁻¹) α β := by
    funext a
    rw [toFullBlockMat_normalizedBlock, toFullBlockMat_blockSub]
  rw [hfun]
  exact aestronglyMeasurable_entry_conj _ hsub α β

/-- The trace of a random doubled block is measurable as soon as its entries
are. -/
theorem aestronglyMeasurable_blockTrace {P : Measure (CoeffSpace d)}
    {W : CoeffSpace d → BlockMat d}
    (hW : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun a => toFullBlockMat (W a) α β) P) :
    AEStronglyMeasurable (fun a => blockTrace (W a)) P := by
  simp only [blockTrace, Matrix.trace, Matrix.diag]
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hW i i

/-- At an even natural exponent the Schatten trace of a self-adjoint matrix is
the trace of a matrix power: the spectral power `x ↦ x^{Q/2}` is then a natural
power, and the functional calculus of a natural power is that power. -/
theorem trace_cfc_rpow_eq_trace_pow {A : FullBlockMat d} (hA : IsSelfAdjoint A) {Q : ℕ}
    (hQ : Even Q) :
    Matrix.trace (cfc (fun x : ℝ => x ^ ((Q : ℝ) / 2)) A) = Matrix.trace (A ^ (Q / 2)) := by
  obtain ⟨m, hm⟩ := hQ
  have hmnat : Q / 2 = m := by omega
  have hmR : (Q : ℝ) / 2 = (m : ℝ) := by
    have hcast : (Q : ℝ) = (m : ℝ) + (m : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hm
    rw [hcast]
    ring
  have hfun : (fun x : ℝ => x ^ ((Q : ℝ) / 2)) = fun x : ℝ => x ^ (m : ℕ) := by
    funext x
    rw [hmR, Real.rpow_natCast]
  have hpow := cfc_pow (R := ℝ) (fun x : ℝ => x) m A
  rw [cfc_id' ℝ A hA] at hpow
  rw [hfun, hpow, hmnat]

/-- **The Schatten size at an even exponent is an algebraic function of the
entries**: `|H|_{S_Q} = (tr((H²)^{Q/2}))^{1/Q}` with `Q/2` an integer power. -/
theorem schattenNorm_natCast_eq {H : BlockMat d} (hH : IsSymmetricBlockMat H) {Q : ℕ}
    (hQ : Even Q) :
    schattenNorm (Q : ℝ) H =
      Matrix.trace ((toFullBlockMat H * toFullBlockMat H) ^ (Q / 2)) ^ ((Q : ℝ))⁻¹ := by
  rw [schattenNorm,
    trace_cfc_rpow_eq_trace_pow (isSelfAdjoint_mul_self (isSelfAdjoint_toFullBlockMat hH)) hQ]

/-- **The Schatten size of a random symmetric doubled block is measurable** at an
even exponent, with no hypothesis beyond measurability of the entries: the
Schatten trace is then a polynomial in them and the `Q`-th root is continuous. -/
theorem aestronglyMeasurable_schattenNorm {P : Measure (CoeffSpace d)}
    {H : CoeffSpace d → BlockMat d} (hH : ∀ a, IsSymmetricBlockMat (H a)) {Q : ℕ}
    (hQeven : Even Q)
    (hmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a => toFullBlockMat (H a) α β) P) :
    AEStronglyMeasurable (fun a => schattenNorm (Q : ℝ) (H a)) P := by
  have hsq : ∀ α β : BlockCoord d, AEStronglyMeasurable
      (fun a => (toFullBlockMat (H a) * toFullBlockMat (H a)) α β) P :=
    aestronglyMeasurable_entry_mul hmeas hmeas
  have hpow := aestronglyMeasurable_entry_pow hsq (Q / 2)
  have htr : AEStronglyMeasurable
      (fun a => Matrix.trace ((toFullBlockMat (H a) * toFullBlockMat (H a)) ^ (Q / 2))) P := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hpow i i
  have hcont : Continuous fun t : ℝ => t ^ ((Q : ℝ))⁻¹ :=
    continuous_iff_continuousAt.mpr fun t =>
      Real.continuousAt_rpow_const t _ (Or.inr (by positivity))
  exact (hcont.comp_aestronglyMeasurable htr).congr
    (_root_.Filter.Eventually.of_forall fun a => (schattenNorm_natCast_eq (hH a) hQeven).symm)

/-! ## The recurrence -/

end

end Recurrence
end HighContrast
end HCPolySupport
