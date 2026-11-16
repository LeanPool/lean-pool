/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import LeanPool.KnillLaflamme.QuantumInfo.Channel
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# The Knill–Laflamme conditions

A **code** is an orthogonal projector `P` on a finite-dimensional Hilbert space; a family of
**error operators** `E i` is **correctable** on the code when some quantum channel `R` (the
recovery) undoes every error on every code state: `R (E i ρ E iᴴ) = λ i • ρ` whenever
`ρ = P ρ P`. The **Knill–Laflamme condition** is the algebraic criterion

  `P E iᴴ E j P = c i j • P`   for some matrix `c`,

and the theorem is that the two are equivalent (Knill–Laflamme 1997; Nielsen–Chuang Thm 10.1):

* `exists_recovery_of_knillLaflamme` — **the recovery map exists**: from the condition, with
  `c` Hermitian (`KnillLaflamme.isHermitian`), diagonalise `c = U D U*` (Mathlib's
  `Matrix.IsHermitian.spectral_theorem`; `U = klUnitary`); the **canonical errors**
  `F k = ∑ᵢ U i k • E i`
  satisfy `P F kᴴ F l P = d k δ_kl P` with `d k ≥ 0` (`knillLaflamme_canonicalError`), so their
  images of the code are orthogonal; the Kraus operators `R k = d k^{−1/2} P F kᴴ` (for `d k ≠ 0`)
  have `R kᴴ R k = d k⁻¹ F k P F kᴴ`, orthogonal projectors summing to `Q`, and `1 − Q` completes
  the channel (`recoveryChannel`); on a code state `R (F k ρ F lᴴ) = d k δ_kl ρ`
  (`recoveryChannel_apply`), hence `R (E i ρ E jᴴ) = c j i • ρ`;
* `exists_recovery_channel_of_knillLaflamme` — for a noise **channel** `𝓔` with Kraus operators
  `E`, `R (𝓔 ρ) = ρ` on the code: trace preservation makes `tr c = 1`;
* `knillLaflamme_of_recovery` — **the converse**: if a channel corrects the errors up to
  scalars, the condition holds. Each `R k E i P` maps every code vector to a multiple of itself
  (`exists_smul_of_sum_conj_eq`: the sandwiched identity `∑ₖ |⟨u, R k E i v⟩|² = λ |⟨u, v⟩|²`
  with `u` the component of `R k E i v` orthogonal to `v`), hence is a scalar on the code
  (`exists_smul_of_forall_smul`), and `P E iᴴ E j P = ∑ₖ (R k E i P)ᴴ (R k E j P)` by trace
  preservation; `exists_kraus_mul_mul_eq_smul` — the first half on its own, for one error: **a
  recovery that undoes `F` up to a scalar does so Kraus operator by Kraus operator**;
* `knillLaflamme_iff` — the equivalence;
* `recovery_apply_lin_comb` — **discretization**: the correction property is sesquilinear in
  the two error slots (conjugate-linear in the second) and a channel is linear, so a recovery
  corrects every linear combination of the family, up to the scalar the coefficients give
  (`exists_smul_recovery_apply_of_eq_lin_comb` is the existential form). Correcting the four
  Paulis on a qubit therefore corrects every operator on that qubit.

## Scope

Matrices over `ℂ` on a finite index type; the code is a projector, not a subspace, and no
stabiliser structure is assumed. Degenerate codes are covered (`c` need not be invertible:
`d k = 0` errors act as `0` on the code). The recovery is constructed, not shown unique.

References: E. Knill, R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55
(1997) 900; M. Nielsen, I. Chuang, *Quantum Computation and Quantum Information*, Thm 10.1.

*Provenance:* copied from csd-lean4 (`zblore/csd-lean4`, commit `db586e88`), file
`CsdLean4/Mathlib/QuantumInfo/KnillLaflamme.lean`, with imports renamed from `CsdLean4.Mathlib` to
`KnillLaflammeLean`. The Lean Pool port removes redundant instances and shares
the scalar-Kraus reconstruction.
The upstream comments were edited to
remove csd-lean4's internal notes and references to files that are not here.
-/

@[expose] public section

open Matrix Unitary
open scoped ComplexOrder ComplexConjugate

namespace QuantumInfo

variable {n : Type*} [Fintype n]

/-! ### Code projectors -/

/-- A **code projector**: an orthogonal projector `P` (Hermitian and idempotent). -/
structure IsCodeProjector (P : Matrix n n ℂ) : Prop where
  conjTranspose_eq : Pᴴ = P
  mul_self : P * P = P

namespace IsCodeProjector

variable {P : Matrix n n ℂ} (hP : IsCodeProjector P)
include hP

theorem posSemidef : P.PosSemidef := by
  have h : P = Pᴴ * P := by rw [hP.conjTranspose_eq, hP.mul_self]
  rw [h]
  exact posSemidef_conjTranspose_mul_self P

theorem trace_pos (hP0 : P ≠ 0) : 0 < P.trace :=
  lt_of_le_of_ne hP.posSemidef.trace_nonneg
    fun h => hP0 (hP.posSemidef.trace_eq_zero_iff.mp h.symm)

omit [Fintype n] hP in
/-- A nonzero matrix determines the scalar multiplying it. -/
theorem smul_injective (hP0 : P ≠ 0) {a b : ℂ} (h : a • P = b • P) : a = b := by
  have h1 : (a - b) • P = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact sub_eq_zero.mp h2
  · exact absurd h2 hP0

/-- A real scalar `a` with `a • P` positive semidefinite is nonnegative. -/
theorem nonneg_of_smul_posSemidef (hP0 : P ≠ 0) {a : ℝ}
    (h : ((a : ℂ) • P).PosSemidef) : 0 ≤ a := by
  have h1 := h.trace_nonneg
  rw [trace_smul, smul_eq_mul, Complex.nonneg_iff] at h1
  have h2 := hP.trace_pos hP0
  rw [Complex.pos_iff] at h2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h1
  exact (mul_nonneg_iff_of_pos_right h2.1).mp h1.1

end IsCodeProjector

/-! ### The Knill–Laflamme condition -/

variable [DecidableEq n] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Knill–Laflamme condition** for the errors `E` on the code `P`, with matrix `c`:
`P E iᴴ E j P = c i j • P`. -/
def KnillLaflamme (P : Matrix n n ℂ) (E : ι → Matrix n n ℂ) (c : Matrix ι ι ℂ) : Prop :=
  ∀ i j, P * (E i)ᴴ * E j * P = c i j • P

variable {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {c : Matrix ι ι ℂ}

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
/-- The Knill–Laflamme matrix of a nonzero code is Hermitian. -/
theorem KnillLaflamme.isHermitian (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (hc : KnillLaflamme P E c) : c.IsHermitian := by
  refine IsHermitian.ext fun i j => ?_
  have h3 : (P * (E j)ᴴ * E i * P)ᴴ = P * (E i)ᴴ * E j * P := by
    simp [conjTranspose_mul, hP.conjTranspose_eq, Matrix.mul_assoc]
  rw [hc j i, conjTranspose_smul, hP.conjTranspose_eq, hc i j] at h3
  exact IsCodeProjector.smul_injective hP0 h3

omit [Fintype ι] [DecidableEq ι] in
/-- A channel applied to a finite sum. -/
theorem Channel.apply_sum {m κ : Type*} [Fintype m] [Fintype κ] (Φ : Channel n m κ)
    {α : Type*} (s : Finset α) (f : α → Matrix n n ℂ) :
    Φ.apply (∑ a ∈ s, f a) = ∑ a ∈ s, Φ.apply (f a) := by
  simp only [Channel.apply_def, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

/-! ### The recovery channel of an orthogonal error family -/

section Orthogonal

omit [Fintype ι] [DecidableEq ι]

variable {κ : Type*} [DecidableEq κ]
variable (P : Matrix n n ℂ) (F : κ → Matrix n n ℂ) (d : κ → ℝ)

/-- The recovery Kraus operator of the `k`-th orthogonal error: `d k^{−1/2} P F kᴴ`, or `0` when
`d k = 0`. -/
noncomputable def recoveryOp (k : κ) : Matrix n n ℂ :=
  if d k = 0 then 0 else (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) • (P * (F k)ᴴ)

/-- The projector `d k⁻¹ F k P F kᴴ` onto the image of the code under the `k`-th error. -/
noncomputable def errorImageProj (k : κ) : Matrix n n ℂ :=
  if d k = 0 then 0 else (((d k)⁻¹ : ℝ) : ℂ) • (F k * P * (F k)ᴴ)

variable [Fintype κ]

/-- The projector onto the span of all error images: `∑ₖ R kᴴ R k`. -/
noncomputable def recoveryProj : Matrix n n ℂ :=
  ∑ k, (recoveryOp P F d k)ᴴ * recoveryOp P F d k

/-- The recovery Kraus family: the `R k`, completed by `1 − ∑ₖ R kᴴ R k`. -/
noncomputable def recoveryKraus : Option κ → Matrix n n ℂ
  | some k => recoveryOp P F d k
  | none => 1 - recoveryProj P F d

variable {P F d}

omit [DecidableEq n] [Fintype κ] in
/-- An error with `d k = 0` kills the code. -/
theorem mul_codeProj_eq_zero_of_eq_zero (hP : IsCodeProjector P)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {k : κ} (hk : d k = 0) : F k * P = 0 := by
  have h := hF k k
  rw [ite_eq_left rfl, hk, Complex.ofReal_zero, zero_smul] at h
  have h2 : (F k * P)ᴴ * (F k * P) = 0 := by
    rw [conjTranspose_mul, hP.conjTranspose_eq, ← h]
    simp only [Matrix.mul_assoc]
  exact conjTranspose_mul_self_eq_zero.mp h2

omit [DecidableEq n] [Fintype κ] [DecidableEq κ] in
theorem recoveryOp_conjTranspose_mul_self (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k) (k : κ) :
    (recoveryOp P F d k)ᴴ * recoveryOp P F d k = errorImageProj P F d k := by
  unfold recoveryOp errorImageProj
  split_ifs with hk
  · simp
  · rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, conjTranspose_mul,
      conjTranspose_conjTranspose, hP.conjTranspose_eq]
    congr 1
    · rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
        Real.mul_self_sqrt (hd k)]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hP.mul_self, ← Matrix.mul_assoc]

omit [DecidableEq n] [Fintype κ] in
theorem errorImageProj_mul
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (k l : κ) :
    errorImageProj P F d k * errorImageProj P F d l
      = if k = l then errorImageProj P F d k else 0 := by
  unfold errorImageProj
  by_cases hk : d k = 0
  · simp [hk]
  by_cases hl : d l = 0
  · have hkl : k ≠ l := fun h => hk (h ▸ hl)
    simp [hl, hkl]
  rw [ite_eq_right hk, ite_eq_right hl, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have key : F k * P * (F k)ᴴ * (F l * P * (F l)ᴴ) = F k * (P * (F k)ᴴ * F l * P) * (F l)ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [key, hF k l]
  split_ifs with hkl
  · subst hkl
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    exact_mod_cast (by field_simp : (d k)⁻¹ * (d k)⁻¹ * d k = (d k)⁻¹)
  · simp

omit [DecidableEq n] [Fintype κ] [DecidableEq κ] in
theorem errorImageProj_conjTranspose (hP : IsCodeProjector P) (k : κ) :
    (errorImageProj P F d k)ᴴ = errorImageProj P F d k := by
  unfold errorImageProj
  split_ifs
  · simp
  · rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, conjTranspose_mul,
      conjTranspose_mul, conjTranspose_conjTranspose, hP.conjTranspose_eq, Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq κ] in
theorem recoveryProj_eq (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k) :
    recoveryProj P F d = ∑ k, errorImageProj P F d k := by
  unfold recoveryProj
  exact Finset.sum_congr rfl fun k _ => recoveryOp_conjTranspose_mul_self hP hd k

omit [DecidableEq n] in
theorem recoveryProj_mul_self (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) :
    recoveryProj P F d * recoveryProj P F d = recoveryProj P F d := by
  rw [recoveryProj_eq hP hd, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum]
  simp only [errorImageProj_mul hF]
  simp

omit [DecidableEq n] [DecidableEq κ] in
theorem recoveryProj_conjTranspose (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k) :
    (recoveryProj P F d)ᴴ = recoveryProj P F d := by
  rw [recoveryProj_eq hP hd, conjTranspose_sum]
  exact Finset.sum_congr rfl fun k _ => errorImageProj_conjTranspose hP k

/-- The recovery Kraus family is trace preserving. -/
theorem recoveryKraus_tp (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) :
    ∑ o : Option κ, (recoveryKraus P F d o)ᴴ * recoveryKraus P F d o = 1 := by
  rw [Fintype.sum_option]
  have h1 : ∑ k, (recoveryKraus P F d (some k))ᴴ * recoveryKraus P F d (some k)
      = recoveryProj P F d := rfl
  rw [h1]
  change (1 - recoveryProj P F d)ᴴ * (1 - recoveryProj P F d) + recoveryProj P F d = 1
  rw [conjTranspose_sub, conjTranspose_one, recoveryProj_conjTranspose hP hd]
  have hQ := recoveryProj_mul_self hP hd hF
  simp only [sub_mul, mul_sub, one_mul, mul_one, hQ]
  abel

/-- **The recovery channel** of an orthogonal error family. -/
noncomputable def recoveryChannel (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) :
    Channel n n (Option κ) where
  kraus := recoveryKraus P F d
  tp := recoveryKraus_tp hP hd hF

omit [DecidableEq n] [Fintype κ] in
theorem recoveryOp_mul_mul_codeProj
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (m k : κ) :
    recoveryOp P F d m * F k * P
      = if m = k ∧ d m ≠ 0 then ((Real.sqrt (d m) : ℝ) : ℂ) • P else 0 := by
  unfold recoveryOp
  by_cases hm : d m = 0
  · simp [hm]
  rw [ite_eq_right hm, Matrix.smul_mul, Matrix.smul_mul, hF m k]
  by_cases hmk : m = k
  · subst hmk
    rw [ite_eq_left rfl, ite_eq_left ⟨rfl, hm⟩, smul_smul, ← Complex.ofReal_mul, inv_mul_eq_div,
      Real.div_sqrt]
  · simp [hmk]

omit [DecidableEq n] [Fintype κ] in
/-- The action of one recovery operator on an error term of a code state. -/
theorem recoveryOp_conj (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) (m k l : κ) :
    recoveryOp P F d m * (F k * ρ * (F l)ᴴ) * (recoveryOp P F d m)ᴴ
      = if m = k ∧ m = l ∧ d m ≠ 0 then ((d m : ℝ) : ℂ) • ρ else 0 := by
  have h1 : recoveryOp P F d m * (F k * ρ * (F l)ᴴ) * (recoveryOp P F d m)ᴴ
      = (recoveryOp P F d m * F k * P) * ρ * (recoveryOp P F d m * F l * P)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq]
    conv_lhs => rw [hρ]
    simp only [Matrix.mul_assoc]
  rw [h1, recoveryOp_mul_mul_codeProj hF m k, recoveryOp_mul_mul_codeProj hF m l]
  by_cases hmk : m = k
  · by_cases hml : m = l
    · by_cases hm : d m = 0
      · simp [hm]
      · rw [ite_eq_left ⟨hmk, hm⟩, ite_eq_left ⟨hml, hm⟩,
          ite_eq_left ⟨hmk, hml, hm⟩, conjTranspose_smul,
          Complex.star_def, Complex.conj_ofReal, hP.conjTranspose_eq]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd m), ← hρ]
    · simp [hml]
  · simp [hmk]

/-- The completion `1 − Q` kills every error image of the code. -/
theorem one_sub_recoveryProj_mul (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0) (k : κ) :
    (1 - recoveryProj P F d) * F k * P = 0 := by
  have hF' : ∀ k l, P * ((F k)ᴴ * (F l * P)) = if k = l then ((d k : ℝ) : ℂ) • P else 0 :=
    fun k l => by simpa only [Matrix.mul_assoc] using hF k l
  have h : recoveryProj P F d * F k * P = F k * P := by
    rw [recoveryProj_eq hP hd, Finset.sum_mul, Finset.sum_mul, Finset.sum_eq_single k]
    · unfold errorImageProj
      split_ifs with hk
      · rw [mul_codeProj_eq_zero_of_eq_zero hP hF hk]
        simp
      · simp only [Matrix.smul_mul, Matrix.mul_assoc]
        rw [hF' k k, ite_eq_left rfl, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
          inv_mul_cancel₀ hk, Complex.ofReal_one, one_smul]
    · intro m _ hmk
      unfold errorImageProj
      split_ifs with hm
      · simp
      · simp only [Matrix.smul_mul, Matrix.mul_assoc]
        rw [hF' m k, ite_eq_right hmk]
        simp
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [sub_mul, sub_mul, one_mul, h, sub_self]

/-- **The recovery channel undoes an orthogonal error family on the code**:
`R (F k ρ F lᴴ) = d k δ_kl • ρ` for `ρ = P ρ P`. -/
theorem recoveryChannel_apply (hP : IsCodeProjector P) (hd : ∀ k, 0 ≤ d k)
    (hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0)
    {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) (k l : κ) :
    (recoveryChannel hP hd hF).apply (F k * ρ * (F l)ᴴ)
      = if k = l then ((d k : ℝ) : ℂ) • ρ else 0 := by
  rw [Channel.apply_def]
  change ∑ o : Option κ, recoveryKraus P F d o * (F k * ρ * (F l)ᴴ) * (recoveryKraus P F d o)ᴴ = _
  rw [Fintype.sum_option]
  have hnone : recoveryKraus P F d none * (F k * ρ * (F l)ᴴ) * (recoveryKraus P F d none)ᴴ
      = 0 := by
    change (1 - recoveryProj P F d) * (F k * ρ * (F l)ᴴ) * (1 - recoveryProj P F d)ᴴ = 0
    have h : (1 - recoveryProj P F d) * (F k * ρ * (F l)ᴴ)
        = ((1 - recoveryProj P F d) * F k * P) * (ρ * P * (F l)ᴴ) := by
      conv_lhs => rw [hρ]
      simp only [Matrix.mul_assoc]
    rw [h, one_sub_recoveryProj_mul hP hd hF, zero_mul, zero_mul]
  rw [hnone, zero_add]
  have hsome : ∀ m, recoveryKraus P F d (some m) * (F k * ρ * (F l)ᴴ)
      * (recoveryKraus P F d (some m))ᴴ
      = if m = k ∧ m = l ∧ d m ≠ 0 then ((d m : ℝ) : ℂ) • ρ else 0 :=
    fun m => recoveryOp_conj hP hd hF hρ m k l
  simp only [hsome]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl, Finset.sum_eq_single k]
    · by_cases hk : d k = 0
      · simp [hk]
      · rw [ite_eq_left ⟨rfl, rfl, hk⟩]
    · intro m _ hmk
      simp [hmk]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · rw [ite_eq_right hkl]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [ite_eq_right]
    rintro ⟨rfl, rfl, -⟩
    exact hkl rfl

end Orthogonal

/-! ### Diagonalising the Knill–Laflamme matrix -/

section Canonical

variable (hc' : c.IsHermitian)

/-- The eigenvector unitary of the Knill–Laflamme matrix, as a matrix. -/
noncomputable def klUnitary : Matrix ι ι ℂ := hc'.eigenvectorUnitary

theorem klUnitary_star_mul : star (klUnitary hc') * klUnitary hc' = 1 :=
  coe_star_mul_self hc'.eigenvectorUnitary

theorem klUnitary_mul_star : klUnitary hc' * star (klUnitary hc') = 1 :=
  coe_mul_star_self hc'.eigenvectorUnitary

theorem eq_klUnitary_mul_diagonal :
    c = klUnitary hc' * diagonal (RCLike.ofReal ∘ hc'.eigenvalues) * star (klUnitary hc') := by
  have := hc'.spectral_theorem
  rwa [conjStarAlgAut_apply] at this

/-- The **canonical errors** `F k = ∑ᵢ U i k • E i`, `U` the eigenvector unitary of `c`. -/
noncomputable def canonicalError (E : ι → Matrix n n ℂ) (k : ι) : Matrix n n ℂ :=
  ∑ i, klUnitary hc' i k • E i

theorem star_klUnitary_mul_mul :
    star (klUnitary hc') * c * klUnitary hc' = diagonal (RCLike.ofReal ∘ hc'.eigenvalues) := by
  calc star (klUnitary hc') * c * klUnitary hc'
      = star (klUnitary hc') * (klUnitary hc' * diagonal (RCLike.ofReal ∘ hc'.eigenvalues)
          * star (klUnitary hc')) * klUnitary hc' := by rw [← eq_klUnitary_mul_diagonal]
    _ = diagonal (RCLike.ofReal ∘ hc'.eigenvalues) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, klUnitary_star_mul, Matrix.mul_one,
          ← Matrix.mul_assoc, klUnitary_star_mul, Matrix.one_mul]

omit [DecidableEq n] in
/-- The canonical errors satisfy the **diagonal** Knill–Laflamme condition. -/
theorem knillLaflamme_canonicalError (hc : KnillLaflamme P E c) (k l : ι) :
    P * (canonicalError hc' E k)ᴴ * canonicalError hc' E l * P
      = if k = l then ((hc'.eigenvalues k : ℝ) : ℂ) • P else 0 := by
  have h1 : P * (canonicalError hc' E k)ᴴ * canonicalError hc' E l * P
      = ∑ j, ∑ i, (klUnitary hc' j l * star (klUnitary hc' i k) * c i j) • P := by
    unfold canonicalError
    rw [conjTranspose_sum]
    simp only [conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hc i j, smul_smul]
  rw [h1]
  have h2 : ∑ j, ∑ i, (klUnitary hc' j l * star (klUnitary hc' i k) * c i j) • P
      = (star (klUnitary hc') * c * klUnitary hc') k l • P := by
    simp only [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.star_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h2, star_klUnitary_mul_mul, diagonal_apply]
  split_ifs <;> simp

omit [Fintype n] [DecidableEq n] in
/-- The errors in terms of the canonical ones: `E i = ∑ₖ conj(U i k) • F k`. -/
theorem eq_sum_canonicalError (i : ι) :
    E i = ∑ k, star (klUnitary hc' i k) • canonicalError hc' E k := by
  unfold canonicalError
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ k, (star (klUnitary hc' i k) * klUnitary hc' j k) • E j
      = ((klUnitary hc' * star (klUnitary hc')) j i) • E j := by
    intro j
    rw [← Finset.sum_smul]
    congr 1
    simp only [Matrix.mul_apply, Matrix.star_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [h, klUnitary_mul_star, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The Knill–Laflamme matrix in terms of the eigen-data: `c j i = ∑ₖ U j k d k conj(U i k)`. -/
theorem knillLaflamme_matrix_apply (i j : ι) :
    c j i = ∑ k, klUnitary hc' j k * (hc'.eigenvalues k : ℂ) * star (klUnitary hc' i k) := by
  conv_lhs => rw [eq_klUnitary_mul_diagonal hc']
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
  rfl

end Canonical

/-! ### The Knill–Laflamme theorem -/

omit [DecidableEq ι] in
/-- **The Knill–Laflamme theorem (recovery exists).** If the errors `E` satisfy the
Knill–Laflamme condition on the nonzero code `P`, there is a channel `R` with
`R (E i ρ E jᴴ) = c j i • ρ` on every code state `ρ = P ρ P`; in particular
`R (E i ρ E iᴴ) = c i i • ρ`. -/
theorem exists_recovery_of_knillLaflamme (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (hc : KnillLaflamme P E c) :
    ∃ R : Channel n n (Option ι), ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ := by
  classical
  have hc' := hc.isHermitian hP hP0
  set U : Matrix ι ι ℂ := klUnitary hc' with hU
  set F := canonicalError hc' E with hFdef
  set d := hc'.eigenvalues with hddef
  have hF : ∀ k l, P * (F k)ᴴ * F l * P = if k = l then ((d k : ℝ) : ℂ) • P else 0 :=
    fun k l => knillLaflamme_canonicalError hc' hc k l
  have hd : ∀ k, 0 ≤ d k := by
    intro k
    refine hP.nonneg_of_smul_posSemidef hP0 ?_
    have h := hF k k
    rw [ite_eq_left rfl] at h
    rw [← h]
    have h2 : P * (F k)ᴴ * F k * P = (F k * P)ᴴ * (F k * P) := by
      rw [conjTranspose_mul, hP.conjTranspose_eq]
      simp only [Matrix.mul_assoc]
    rw [h2]
    exact posSemidef_conjTranspose_mul_self _
  refine ⟨recoveryChannel hP hd hF, fun ρ hρ i j => ?_⟩
  have hE : ∀ i, E i = ∑ k, star (U i k) • F k := fun i => eq_sum_canonicalError hc' i
  have hEH : ∀ j, (E j)ᴴ = ∑ l, U j l • (F l)ᴴ := by
    intro j
    rw [hE j, conjTranspose_sum]
    simp only [conjTranspose_smul, star_star]
  rw [hE i, hEH j]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Channel.apply_sum, Channel.apply_smul, recoveryChannel_apply hP hd hF hρ]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, smul_smul]
  rw [← Finset.sum_smul, knillLaflamme_matrix_apply hc' i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

omit [DecidableEq ι] in
/-- **A noise channel satisfying Knill–Laflamme is corrected on the code**: for a channel `𝓔`
whose Kraus operators satisfy the condition, `R (𝓔 ρ) = ρ` for every `ρ = P ρ P`. -/
theorem exists_recovery_channel_of_knillLaflamme (hP : IsCodeProjector P) (hP0 : P ≠ 0)
    (𝓔 : Channel n n ι) (hc : KnillLaflamme P 𝓔.kraus c) :
    ∃ R : Channel n n (Option ι), ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      R.apply (𝓔.apply ρ) = ρ := by
  classical
  obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme hP hP0 hc
  refine ⟨R, fun ρ hρ => ?_⟩
  rw [Channel.apply_def 𝓔 ρ, Channel.apply_sum]
  simp only [hR ρ hρ]
  rw [← Finset.sum_smul]
  have htr : ∑ i, c i i = 1 := by
    have h1 : P = (∑ i, c i i) • P := by
      calc P = P * (∑ i, (𝓔.kraus i)ᴴ * 𝓔.kraus i) * P := by
              rw [𝓔.tp, Matrix.mul_one, hP.mul_self]
        _ = ∑ i, P * (𝓔.kraus i)ᴴ * 𝓔.kraus i * P := by
              simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = ∑ i, c i i • P := Finset.sum_congr rfl fun i _ => hc i i
        _ = (∑ i, c i i) • P := Finset.sum_smul.symm
    exact (IsCodeProjector.smul_injective hP0 (by rw [one_smul, ← h1])).symm
  rw [htr, one_smul]

/-! ### Discretization: the recovery corrects the whole span of the errors -/

omit [DecidableEq ι] in
/-- **The recovery corrects every linear combination of the error operators**, up to the scalar
its coefficients give. This is the discretization step: a code that corrects finitely many errors
corrects the whole subspace they span, because the correction property is sesquilinear in the two
error slots (conjugate-linear in the second) and the recovery is linear. Correcting the four Paulis
on a qubit therefore corrects *every* operator on that qubit. -/
theorem recovery_apply_lin_comb {κ : Type*} [Fintype κ] {R : Channel n n κ}
    (hR : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ)
    (a : ι → ℂ) {ρ : Matrix n n ℂ} (hρ : ρ = P * ρ * P) :
    R.apply ((∑ i, a i • E i) * ρ * (∑ i, a i • E i)ᴴ)
      = (∑ i, ∑ j, star (a i) * a j * c i j) • ρ := by
  rw [conjTranspose_sum]
  simp only [conjTranspose_smul, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Channel.apply_sum, Channel.apply_smul, hR ρ hρ, smul_smul, ← Finset.sum_smul]
  refine congrArg (fun t : ℂ => t • ρ) (Finset.sum_congr rfl fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq ι] in
/-- The same statement for an error given as a linear combination: if `F` is a combination of the
`E i`, the recovery returns a multiple of the code state. -/
theorem exists_smul_recovery_apply_of_eq_lin_comb {κ : Type*} [Fintype κ] {R : Channel n n κ}
    (hR : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P →
      ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ)
    {F : Matrix n n ℂ} {a : ι → ℂ} (hF : F = ∑ i, a i • E i) :
    ∃ γ : ℂ, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (F * ρ * Fᴴ) = γ • ρ := by
  refine ⟨∑ i, ∑ j, star (a i) * a j * c i j, fun ρ hρ => ?_⟩
  rw [hF]
  exact recovery_apply_lin_comb hR a hρ

/-! ### The converse: a recovery forces the condition -/

section Converse

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
/-- A matrix mapping every vector `w` to a multiple of `P w`, and vanishing off the code, is a
scalar multiple of `P`. -/
theorem exists_smul_of_forall_smul {A : Matrix n n ℂ}
    (hAP : A * P = A) (h : ∀ w : n → ℂ, ∃ α : ℂ, A *ᵥ w = α • (P *ᵥ w)) :
    ∃ μ : ℂ, A = μ • P := by
  classical
  by_cases hP0 : P = 0
  · exact ⟨0, by rw [← hAP, hP0, Matrix.mul_zero, zero_smul]⟩
  have hw₀ : ∃ w₀ : n → ℂ, P *ᵥ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP0
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa [mulVec_single_one] using this
  obtain ⟨w₀, hw₀⟩ := hw₀
  obtain ⟨μ, hμ⟩ := h w₀
  have hAw : ∀ w, A *ᵥ w = A *ᵥ (P *ᵥ w) := fun w => by rw [mulVec_mulVec, hAP]
  have key : ∀ w, A *ᵥ w = μ • (P *ᵥ w) := by
    intro w
    obtain ⟨α, hα⟩ := h w
    by_cases hdep : ∃ t : ℂ, P *ᵥ w = t • (P *ᵥ w₀)
    · obtain ⟨t, ht⟩ := hdep
      rw [hAw, ht, mulVec_smul, ← hAw, hμ, smul_comm]
    · push Not at hdep
      obtain ⟨β, hβ⟩ := h (w + w₀)
      rw [mulVec_add, mulVec_add, hα, hμ, smul_add] at hβ
      have hli : LinearIndependent ℂ ![P *ᵥ w, P *ᵥ w₀] := by
        rw [linearIndependent_fin2]
        exact ⟨hw₀, fun t ht => hdep t ht.symm⟩
      have := hli.eq_of_pair (s := α) (t := μ) (s' := β) (t' := β) hβ
      rw [hα, this.1, this.2]
  refine ⟨μ, Matrix.ext fun i j => ?_⟩
  have := congrFun (key (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
/-- **Kraus operators of a scalar map on the code are scalars.** If
`∑ₖ A k X (A k)ᴴ = λ • P X P` for every `X`, and each `A k` vanishes off the code, then every
`A k` is a scalar multiple of `P`. -/
theorem exists_smul_of_sum_conj_eq {κ : Type*} [Fintype κ] (hP : IsCodeProjector P)
    (A : κ → Matrix n n ℂ) (lam : ℂ) (hA : ∀ k, A k * P = A k)
    (h : ∀ X : Matrix n n ℂ, ∑ k, A k * X * (A k)ᴴ = lam • (P * X * P)) (k : κ) :
    ∃ μ : ℂ, A k = μ • P := by
  classical
  refine exists_smul_of_forall_smul (hA k) fun w => ?_
  set v := P *ᵥ w with hv
  set a : κ → n → ℂ := fun k' => A k' *ᵥ w with ha
  have hav : ∀ k', A k' *ᵥ v = a k' := fun k' => by
    rw [hv, mulVec_mulVec, hA k']
  have hPv : P *ᵥ v = v := by rw [hv, mulVec_mulVec, hP.mul_self]
  -- the identity on the rank-one state `v vᴴ`
  have hX := h (vecMulVec v (star v))
  have hL : ∀ k', A k' * vecMulVec v (star v) * (A k')ᴴ = vecMulVec (a k') (star (a k')) := by
    intro k'
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hav]
  have hR : P * vecMulVec v (star v) * P = vecMulVec v (star v) := by
    rw [mul_vecMulVec, vecMulVec_mul, hPv]
    congr 1
    conv_lhs => rw [← hP.conjTranspose_eq]
    rw [← star_mulVec, hPv]
  simp only [hL, hR] at hX
  -- the sandwiched scalar identity
  have h2 : ∀ u x : n → ℂ, (star u ⬝ᵥ x) * (star x ⬝ᵥ u)
      = ((Complex.normSq (star u ⬝ᵥ x) : ℝ) : ℂ) := by
    intro u x
    rw [star_dotProduct (v := x) (w := u), Complex.star_def, Complex.mul_conj]
  have hq : ∀ u : n → ℂ, ∑ k', ((Complex.normSq (star u ⬝ᵥ a k') : ℝ) : ℂ)
      = lam * ((Complex.normSq (star u ⬝ᵥ v) : ℝ) : ℂ) := by
    intro u
    have h1 := congrArg (fun M : Matrix n n ℂ => star u ⬝ᵥ (M *ᵥ u)) hX
    simp only [dotProduct_mulVec, Matrix.vecMul_sum, sum_dotProduct, Matrix.vecMul_smul,
      vecMul_vecMulVec, smul_dotProduct, smul_eq_mul, h2] at h1
    exact h1
  by_cases hv0 : v = 0
  · refine ⟨0, ?_⟩
    have hw : A k *ᵥ w = A k *ᵥ v := by rw [hv, mulVec_mulVec, hA k]
    rw [hw, hv0, mulVec_zero, zero_smul]
  have hvv : star v ⬝ᵥ v ≠ 0 := fun h0 => hv0 (dotProduct_star_self_eq_zero.mp h0)
  set α : ℂ := (star v ⬝ᵥ a k) / (star v ⬝ᵥ v) with hα
  set u : n → ℂ := a k - α • v with hu
  have huv : star u ⬝ᵥ v = 0 := by
    rw [hu, star_sub, star_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul, hα,
      star_div₀, star_dotProduct (v := a k) (w := v), ← star_dotProduct (v := v) (w := v),
      div_mul_cancel₀ _ hvv, sub_self]
  have hsum := hq u
  rw [huv, Complex.normSq_zero, Complex.ofReal_zero, mul_zero, ← Complex.ofReal_sum,
    Complex.ofReal_eq_zero] at hsum
  have hk : Complex.normSq (star u ⬝ᵥ a k) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k' _ => Complex.normSq_nonneg _).mp hsum k
      (Finset.mem_univ k)
  rw [Complex.normSq_eq_zero] at hk
  have huu : star u ⬝ᵥ u = 0 := by
    have h3 : star u ⬝ᵥ u = star u ⬝ᵥ (a k - α • v) := by rw [hu]
    rw [h3, dotProduct_sub, dotProduct_smul, hk, huv, smul_zero, sub_zero]
  have hu0 : u = 0 := dotProduct_star_self_eq_zero.mp huu
  refine ⟨α, ?_⟩
  rw [hu] at hu0
  exact sub_eq_zero.mp hu0

omit [Fintype ι] [DecidableEq ι] in
/-- **A recovery that undoes an error up to a scalar does so Kraus operator by Kraus operator**:
if `R (F ρ Fᴴ) = λ • ρ` on code states, every `R.kraus k * F` acts on the code as a scalar. -/
theorem exists_kraus_mul_mul_eq_smul (hP : IsCodeProjector P) {κ : Type*} [Fintype κ]
    (R : Channel n n κ) {F : Matrix n n ℂ} {lam : ℂ}
    (h : ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (F * ρ * Fᴴ) = lam • ρ) (k : κ) :
    ∃ μ : ℂ, R.kraus k * F * P = μ • P := by
  refine exists_smul_of_sum_conj_eq hP (fun k => R.kraus k * F * P) lam
    (fun k => by rw [Matrix.mul_assoc, hP.mul_self]) (fun X => ?_) k
  have hX : P * X * P = P * (P * X * P) * P := by
    conv_rhs => rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self,
      Matrix.mul_assoc (P * X), hP.mul_self]
  have h1 := h (P * X * P) hX
  rw [Channel.apply_def] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conjTranspose_mul, conjTranspose_mul, hP.conjTranspose_eq]
  simp only [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
/-- Scalar Kraus actions on the code determine its Knill–Laflamme matrix. -/
theorem knillLaflamme_of_kraus_scalars (hP : IsCodeProjector P)
    {κ : Type*} [Fintype κ] (R : Channel n n κ) (μ : ι → κ → ℂ)
    (hμ : ∀ i k, R.kraus k * E i * P = μ i k • P) :
    KnillLaflamme P E (fun i j => ∑ k, star (μ i k) * μ j k) := by
  intro i j
  calc P * (E i)ᴴ * E j * P
      = P * (E i)ᴴ * (∑ k, (R.kraus k)ᴴ * R.kraus k) * E j * P := by
        rw [R.tp, Matrix.mul_one]
    _ = ∑ k, (R.kraus k * E i * P)ᴴ * (R.kraus k * E j * P) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, conjTranspose_mul, hP.conjTranspose_eq,
          Matrix.mul_assoc]
    _ = ∑ k, (star (μ i k) * μ j k) • P := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hμ i k, hμ j k, conjTranspose_smul, hP.conjTranspose_eq, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, hP.mul_self]
    _ = (∑ k, star (μ i k) * μ j k) • P := by rw [Finset.sum_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- **The Knill–Laflamme theorem (the condition is necessary).** If a channel `R` corrects the
errors `E` on the code `P` up to scalars — `R (E i ρ E iᴴ) = λ i • ρ` on code states — then the
errors satisfy the Knill–Laflamme condition. -/
theorem knillLaflamme_of_recovery (hP : IsCodeProjector P) {κ : Type*} [Fintype κ]
    (R : Channel n n κ) (lam : ι → ℂ)
    (h : ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme P E c := by
  have hscal : ∀ i k, ∃ μ : ℂ, R.kraus k * E i * P = μ • P := fun i k =>
    exists_kraus_mul_mul_eq_smul hP R (h i) k
  choose μ hμ using hscal
  exact ⟨_, knillLaflamme_of_kraus_scalars hP R μ hμ⟩

omit [DecidableEq ι] in
/-- **The Knill–Laflamme theorem**: the errors `E` are correctable on the nonzero code `P` — some
channel inverts every error on the code up to a scalar — if and only if they satisfy the
Knill–Laflamme condition for some matrix `c`. -/
theorem knillLaflamme_iff (hP : IsCodeProjector P) (hP0 : P ≠ 0) :
    (∃ c : Matrix ι ι ℂ, KnillLaflamme P E c) ↔
      ∃ (R : Channel n n (Option ι)) (lam : ι → ℂ),
        ∀ i, ∀ ρ : Matrix n n ℂ, ρ = P * ρ * P → R.apply (E i * ρ * (E i)ᴴ) = lam i • ρ := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme hP hP0 hc
    exact ⟨R, fun i => c i i, fun i ρ hρ => hR ρ hρ i i⟩
  · rintro ⟨R, lam, h⟩
    exact knillLaflamme_of_recovery hP R lam h

end Converse

/-! ### The condition in encoder form -/

section Encoder

variable {L : Type*} [Fintype L] [DecidableEq L] {V : Matrix n L ℂ}

omit [DecidableEq n] in
/-- An isometric encoder gives a code projector: `P = V Vᴴ` for `Vᴴ V = 1`. -/
theorem isCodeProjector_mul_conjTranspose (hV : Vᴴ * V = 1) : IsCodeProjector (V * Vᴴ) where
  conjTranspose_eq := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  mul_self := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V Vᴴ, hV, Matrix.one_mul]

omit [DecidableEq n] in
/-- The code of an isometric encoder is nonzero as soon as it encodes something. -/
theorem mul_conjTranspose_ne_zero [Nonempty L] (hV : Vᴴ * V = 1) : V * Vᴴ ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty L›
  have h1 : (1 : Matrix L L ℂ) = 0 := by
    calc (1 : Matrix L L ℂ) = Vᴴ * V * (Vᴴ * V) := by rw [hV, Matrix.one_mul]
      _ = Vᴴ * (V * Vᴴ) * V := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  have h2 : (1 : ℂ) = 0 := by
    have h3 := congrFun (congrFun h1 i) i
    rwa [Matrix.one_apply_eq, Matrix.zero_apply] at h3
  exact one_ne_zero h2

omit [DecidableEq n] in
theorem mul_conjTranspose_mul_encoder (hV : Vᴴ * V = 1) : V * Vᴴ * V = V := by
  rw [Matrix.mul_assoc, hV, Matrix.mul_one]

omit [DecidableEq n] in
theorem conjTranspose_mul_mul_conjTranspose (hV : Vᴴ * V = 1) : Vᴴ * (V * Vᴴ) = Vᴴ := by
  rw [← Matrix.mul_assoc, hV, Matrix.one_mul]

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
/-- **Encoder form implies projector form.** If the errors are scalar on the encoded space,
`Vᴴ Eᵢᴴ Eⱼ V = cᵢⱼ • 1`, they satisfy Knill–Laflamme on the code `V Vᴴ`. This needs no rank
statement about `V Vᴴ`, and not even that `V` is an isometry. -/
theorem knillLaflamme_of_encoder
    (h : ∀ i j, Vᴴ * (E i)ᴴ * E j * V = c i j • 1) :
    KnillLaflamme (V * Vᴴ) E c := by
  intro i j
  calc V * Vᴴ * (E i)ᴴ * E j * (V * Vᴴ)
      = V * (Vᴴ * (E i)ᴴ * E j * V) * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = V * (c i j • (1 : Matrix L L ℂ)) * Vᴴ := by rw [h i j]
    _ = c i j • (V * Vᴴ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype L] in
/-- **Projector form implies encoder form**, for an encoder whose columns are code states. -/
theorem encoder_of_knillLaflamme (hP : IsCodeProjector P) (hV : Vᴴ * V = 1) (hPV : P * V = V)
    (hc : KnillLaflamme P E c) (i j : ι) : Vᴴ * (E i)ᴴ * E j * V = c i j • 1 := by
  have hVP : Vᴴ * P = Vᴴ := by
    conv_lhs => rw [← hP.conjTranspose_eq]
    rw [← conjTranspose_mul, hPV]
  have h := congrArg (fun M : Matrix n n ℂ => Vᴴ * M * V) (hc i j)
  simp only [← Matrix.mul_assoc, hVP] at h
  simpa only [Matrix.smul_mul, Matrix.mul_assoc, hPV, Matrix.mul_smul, hV] using h

omit [Fintype ι] [DecidableEq ι] [Fintype L] in
/-- The logical action of a single error, for a family containing the identity: the identity's row
of the Knill–Laflamme matrix. -/
theorem encoder_apply_of_eq_one (hP : IsCodeProjector P) (hV : Vᴴ * V = 1) (hPV : P * V = V)
    (hc : KnillLaflamme P E c) {i₀ : ι} (hi₀ : E i₀ = 1) (j : ι) :
    Vᴴ * E j * V = c i₀ j • 1 := by
  have h := encoder_of_knillLaflamme hP hV hPV hc i₀ j
  rwa [hi₀, conjTranspose_one, Matrix.mul_one] at h

/-- **The Knill–Laflamme condition in encoder form**, existential in the scalars: every pair of
errors acts on the encoded space as *some* scalar. -/
def EncoderKL (V : Matrix n L ℂ) (E : ι → Matrix n n ℂ) : Prop :=
  ∀ i j, ∃ γ : ℂ, Vᴴ * (E i)ᴴ * E j * V = γ • 1

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype L] in
theorem encoderKL_iff {E : ι → Matrix n n ℂ} :
    EncoderKL V E ↔ ∀ i j, ∃ γ : ℂ, Vᴴ * (E i)ᴴ * E j * V = γ • 1 := Iff.rfl

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
theorem exists_knillLaflamme_of_encoderKL (h : EncoderKL V E) :
    ∃ c : Matrix ι ι ℂ, KnillLaflamme (V * Vᴴ) E c :=
  ⟨Matrix.of fun i j => ((encoderKL_iff.mp h) i j).choose,
    knillLaflamme_of_encoder fun i j => ((encoderKL_iff.mp h) i j).choose_spec⟩

omit [DecidableEq ι] in
/-- **A recovery from the encoder form**: errors that act as scalars on the encoded space are
corrected by one channel. -/
theorem exists_recovery_of_encoderKL [Nonempty L] (hV : Vᴴ * V = 1) (h : EncoderKL V E) :
    ∃ (c : Matrix ι ι ℂ) (R : Channel n n (Option ι)),
      ∀ ρ : Matrix n n ℂ, ρ = V * Vᴴ * ρ * (V * Vᴴ) →
        ∀ i j, R.apply (E i * ρ * (E j)ᴴ) = c j i • ρ := by
  classical
  obtain ⟨c, hc⟩ := exists_knillLaflamme_of_encoderKL h
  obtain ⟨R, hR⟩ := exists_recovery_of_knillLaflamme (isCodeProjector_mul_conjTranspose hV)
    (mul_conjTranspose_ne_zero hV) hc
  exact ⟨c, R, hR⟩

/-- **A unitary error is undone exactly**: if a recovery returns a code state with nonzero trace up
to a scalar and the error is unitary, that scalar is `1`, because both the error and the channel
preserve the trace. -/
theorem smul_eq_one_of_unitary {κ : Type*} [Fintype κ] (R : Channel n n κ)
    {E ρ : Matrix n n ℂ} (hE : Eᴴ * E = 1) {γ : ℂ}
    (h : R.apply (E * ρ * Eᴴ) = γ • ρ) (hρ : ρ.trace ≠ 0) : γ = 1 := by
  have h1 : (E * ρ * Eᴴ).trace = ρ.trace := by
    rw [Matrix.trace_mul_cycle, hE, Matrix.one_mul]
  refine mul_right_cancel₀ hρ ?_
  calc γ * ρ.trace = (γ • ρ).trace := by rw [Matrix.trace_smul, smul_eq_mul]
    _ = (R.apply (E * ρ * Eᴴ)).trace := by rw [h]
    _ = (E * ρ * Eᴴ).trace := R.apply_trace _
    _ = ρ.trace := h1
    _ = 1 * ρ.trace := (one_mul _).symm

end Encoder

end QuantumInfo

end
