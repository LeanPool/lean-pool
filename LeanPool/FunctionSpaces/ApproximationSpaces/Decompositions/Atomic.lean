/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Synthesis

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Atomic decompositions

An atomic decomposition writes `f = ∑_j ∑_m λ_{j,m} a_{j,m}` with atoms `a_{j,m}` of level `j`
at finitely many positions `m ∈ M j`, and measures `f` by the coefficients alone.  On a domain
of dimension `d` in `L_p` the positions are the dyadic cubes of side `2^(-j)` and the
coefficients are measured in the sequence space `b^s_{p,q}`,

`‖λ‖_{b^s_{p,q}} = ‖(2^(j(s - δ)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}`,   `δ = d/p`

(`ApproximationScheme.bNorm`), as in Schneider–Vybíral, *Non-smooth atomic decompositions*.

An **atomic system** (`ApproximationScheme.AtomicSystem`) records two properties of the atoms of
one level, for all coefficients `c`:

* **size**: `‖∑_m c_m a_m‖ ≤ C 2^(-jδ) ‖c‖_{ℓ_p}`, which expresses the normalisation and the
  bounded overlap of the supports;
* **decay**: `E_{2^k}(∑_m c_m a_m) ≤ C 2^(-(k-j)σ) 2^(-jδ) ‖c‖_{ℓ_p}` for `k ≥ j`, which
  expresses the smoothness `σ` of the atoms relative to the scheme (for instance `σ = 1` for
  atoms with a Lipschitz bound and trigonometric approximation in `L_2`).

**Synthesis** (`AtomicSystem.approxNormDyadic_le_bNorm`): for a linear scheme and `0 < s < σ`,
every atomic sum lies in `A^s_q` with `‖f‖_{A^s_q} ≲ ‖λ‖_{b^s_{p,q}}`; this is synthesis with
decay (`ApproximationSpaces.Decompositions.Synthesis`) with `ε_j = C 2^(-jδ) ‖λ_j‖_{ℓ_p}`.

**Analysis** (`AtomicSystem.exists_atomic_decomposition`): if every approximant
`x ∈ A (2^j)` expands in atoms of level `j` with `‖c‖_{ℓ_p} ≤ C' 2^(jδ) ‖x‖`
(`AtomicSystem.StableExpansion`, a stable local basis such as the Haar functions), then every
`f ∈ A^s_q`, `s > 0`, has an atomic decomposition with `‖λ‖_{b^s_{p,q}} ≲ ‖f‖_{A^s_q}`: expand
the blocks of a block decomposition of `f`.  Together:
`A^s_q` is the space of atomic sums with coefficients in `b^s_{p,q}`
(`AtomicSystem.memApprox_iff_exists_atomic`).
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- The quasi-norm of the **sequence space** `b^s_{p,q}`:
`‖(2^(j(s - δ)) ‖λ_{j,·}‖_{ℓ_p})_j‖_{ℓ_q}` for coefficients `λ_{j,m}`, `m ∈ M j`. -/
noncomputable def bNorm (M : ℕ → Type*) [∀ j, MeasurableSpace (M j)]
    (s δ : ℝ) (p q : ℝ≥0∞)
    (c : ∀ j, M j → ℝ) : ℝ≥0∞ :=
  lqNorm q (fun j => dyadicWeight (s - δ) j * lqNorm p (fun m => ‖c j m‖ₑ))

/-- A **system of atoms** for the scheme `A`, with positions `M j` at level `j`, size exponent `δ`
and smoothness `σ`: admissible atoms `adm j m` (containing `0`) such that every combination
`∑_m c_m a_m` of atoms of level `j` has size `≤ C 2^(-jδ) ‖c‖_{ℓ_p}` and error
`E_{2^k} ≤ C 2^(-(k-j)σ) 2^(-jδ) ‖c‖_{ℓ_p}` for `k ≥ j`. -/
structure AtomicSystem (A : ApproximationScheme X) (M : ℕ → Type*) [∀ j, Fintype (M j)]
    [∀ j, MeasurableSpace (M j)]
    (p : ℝ≥0∞) (δ σ : ℝ) where
  /-- The admissible atoms of level `j` at position `m`. -/
  adm : ∀ j, M j → Set X
  zero_mem : ∀ j m, (0 : X) ∈ adm j m
  /-- The constant of the size and decay bounds. -/
  C : ℝ≥0∞
  C_ne_top : C ≠ ∞
  size : ∀ j (a : M j → X), (∀ m, a m ∈ adm j m) → ∀ c : M j → ℝ,
    ‖∑ m, c m • a m‖ₑ ≤ C * (dyadicWeight (-δ) j * lqNorm p (fun m => ‖c m‖ₑ))
  decay : ∀ j (a : M j → X), (∀ m, a m ∈ adm j m) → ∀ c : M j → ℝ, ∀ k, j ≤ k →
    A.approxError (∑ m, c m • a m) (2 ^ k) ≤
      dyadicWeight (-σ) (k - j) * (C * (dyadicWeight (-δ) j * lqNorm p (fun m => ‖c m‖ₑ)))

namespace AtomicSystem

variable {M : ℕ → Type*} [∀ j, Fintype (M j)] [∀ j, MeasurableSpace (M j)] {p : ℝ≥0∞}
  {δ σ : ℝ}
  (AS : A.AtomicSystem M p δ σ)

/-- The constant `(2 (1 - 2^(-s))⁻¹ + (1 - 2^(-(σ-s)))⁻¹) C` of atomic synthesis. -/
noncomputable def synthConst (s : ℝ) : ℝ≥0∞ :=
  (2 * (1 - (2 : ℝ≥0∞) ^ (-s))⁻¹ + (1 - (2 : ℝ≥0∞) ^ (-(σ - s)))⁻¹) * AS.C

/-- The constant of atomic synthesis is finite for `0 < s < σ`. -/
theorem synthConst_ne_top (hs : 0 < s) (hsσ : s < σ) : AS.synthConst s ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num)
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top hs),
    ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 hsσ)⟩) AS.C_ne_top

/-- **Atomic synthesis**: for a linear scheme, every atomic sum
`f = ∑_j ∑_m λ_{j,m} a_{j,m}` (series over `j` converging in `X`) satisfies
`‖f‖_{A^s_q} ≤ K ‖λ‖_{b^s_{p,q}}` in the dyadic quasi-norm, `K = synthConst s`, finite for
`0 < s < σ`. -/
theorem approxNormDyadic_le_bNorm (hA : A.IsLinear) (hq : 1 ≤ q) {a : ∀ j, M j → X}
    (ha : ∀ j m, a j m ∈ AS.adm j m) {c : ∀ j, M j → ℝ} {f : X}
    (hf : HasSum (fun j => ∑ m, c j m • a j m) f) :
    A.approxNormDyadic s q f ≤ AS.synthConst s * bNorm M s δ p q c := by
  set ε : ℕ → ℝ≥0∞ := fun j => AS.C * (dyadicWeight (-δ) j * lqNorm p (fun m => ‖c j m‖ₑ))
  have h := approxNormDyadic_le_of_hasSum_decay (s := s) (C := 1) hA hq hf (ε := ε)
    (fun j => AS.size j _ (ha j) _) (fun j k hjk => by
      rw [one_mul]; exact AS.decay j _ (ha j) _ k hjk)
  refine h.trans_eq ?_
  have hw : (fun j => dyadicWeight s j * ε j) = fun j =>
      AS.C * (dyadicWeight (s - δ) j * lqNorm p (fun m => ‖c j m‖ₑ)) := funext fun j => by
    simp only [ε]
    rw [show s - δ = s + -δ by ring, ENNReal.dyadicWeight_add]; ring
  rw [hw, ENNReal.lqNorm_const_mul, one_mul, synthConst, bNorm]
  ring

/-- **Atomic synthesis**, membership form: atomic sums with `‖λ‖_{b^s_{p,q}} < ∞` lie in
`A^s_q`, for `0 < s < σ`. -/
theorem memApprox_of_bNorm_lt_top (hA : A.IsLinear) (hs : 0 < s) (hsσ : s < σ) (hq : 1 ≤ q)
    {a : ∀ j, M j → X} (ha : ∀ j m, a j m ∈ AS.adm j m) {c : ∀ j, M j → ℝ} {f : X}
    (hf : HasSum (fun j => ∑ m, c j m • a j m) f) (hc : bNorm M s δ p q c < ∞) :
    A.MemApprox s q f :=
  (memApprox_iff_approxNormDyadic_lt_top hq hs.le).2
    ((AS.approxNormDyadic_le_bNorm hA hq ha hf).trans_lt
      (ENNReal.mul_lt_top (AS.synthConst_ne_top hs hsσ).lt_top hc))

/-- **Stable expansion in atoms**: every approximant `x ∈ A (2^j)` is `∑_m c_m a_m` with atoms
`a_m ∈ adm j m` of the same level and `‖c‖_{ℓ_p} ≤ C' 2^(jδ) ‖x‖`.  Local bases such as the
Haar functions have this property. -/
def StableExpansion (C' : ℝ≥0∞) : Prop :=
  ∀ j, ∀ x ∈ A (2 ^ j), ∃ a : M j → X, (∀ m, a m ∈ AS.adm j m) ∧ ∃ c : M j → ℝ,
    x = ∑ m, c m • a m ∧ lqNorm p (fun m => ‖c m‖ₑ) ≤ C' * dyadicWeight δ j * ‖x‖ₑ

/-- **Atomic analysis**: in a Banach space, under a stable expansion, every `f ∈ A^s_q`, `s > 0`,
is an atomic sum `f = ∑_j ∑_m λ_{j,m} a_{j,m}` with
`‖λ‖_{b^s_{p,q}} ≤ C' (3·2^s + 4·4^s) ‖f‖^dyadic_{A^s_q}`. -/
theorem exists_atomic_decomposition [CompleteSpace X] {C' : ℝ≥0∞}
    (hstab : AS.StableExpansion C') (hs : 0 < s) (hq : 1 ≤ q) {f : X} (hf : A.MemApprox s q f) :
    ∃ (a : ∀ j, M j → X) (c : ∀ j, M j → ℝ), (∀ j m, a j m ∈ AS.adm j m) ∧
      HasSum (fun j => ∑ m, c j m • a j m) f ∧
      bNorm M s δ p q c ≤ C' * (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by
  obtain ⟨b, hb_mem, hb_sum, -, hb_lq⟩ := exists_blocks hs hq hf
  choose a ha c hc hcle using fun j => hstab j (b j) (hb_mem j)
  refine ⟨a, c, ha, ?_, ?_⟩
  · have : (fun j => ∑ m, c j m • a j m) = b := funext fun j => (hc j).symm
    rw [this]; exact hb_sum
  · calc bNorm M s δ p q c
        = lqNorm q (fun j => dyadicWeight (s - δ) j * lqNorm p (fun m => ‖c j m‖ₑ)) := rfl
      _ ≤ lqNorm q (fun j => C' * (dyadicWeight s j * ‖b j‖ₑ)) := ENNReal.lqNorm_mono fun j => by
          calc dyadicWeight (s - δ) j * lqNorm p (fun m => ‖c j m‖ₑ)
              ≤ dyadicWeight (s - δ) j * (C' * dyadicWeight δ j * ‖b j‖ₑ) := by
                gcongr; exact hcle j
            _ = C' * ((dyadicWeight (s - δ) j * dyadicWeight δ j) * ‖b j‖ₑ) := by ring
            _ = C' * (dyadicWeight s j * ‖b j‖ₑ) := by
                rw [← ENNReal.dyadicWeight_add, sub_add_cancel]
      _ = C' * lqNorm q (fun j => dyadicWeight s j * ‖b j‖ₑ) := ENNReal.lqNorm_const_mul _ _
      _ ≤ C' * ((3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f) := by gcongr
      _ = C' * (3 * 2 ^ s + 4 * dyadicWeight s 2) * A.approxNormDyadic s q f := by ring

/-- **The atomic characterisation of `A^s_q`**: for a linear scheme in a Banach space with a
stable expansion, `0 < s < σ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff `f` is an atomic sum with
coefficients in `b^s_{p,q}`. -/
theorem memApprox_iff_exists_atomic [CompleteSpace X] (hA : A.IsLinear) {C' : ℝ≥0∞}
    (hC' : C' ≠ ∞) (hstab : AS.StableExpansion C') (hs : 0 < s) (hsσ : s < σ) (hq : 1 ≤ q)
    {f : X} :
    A.MemApprox s q f ↔ ∃ (a : ∀ j, M j → X) (c : ∀ j, M j → ℝ), (∀ j m, a j m ∈ AS.adm j m) ∧
      HasSum (fun j => ∑ m, c j m • a j m) f ∧ bNorm M s δ p q c < ∞ := by
  constructor
  · intro hf
    obtain ⟨a, c, ha, hsum, hle⟩ := AS.exists_atomic_decomposition hstab hs hq hf
    refine ⟨a, c, ha, hsum, hle.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC'.lt_top ?_)
      ((memApprox_iff_approxNormDyadic_lt_top hq hs.le).1 hf))⟩
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
      (ENNReal.two_rpow_ne_top _).lt_top,
      ENNReal.mul_lt_top (by norm_num) (ENNReal.dyadicWeight_lt_top s 2)⟩
  · rintro ⟨a, c, ha, hsum, hc⟩
    exact AS.memApprox_of_bNorm_lt_top hA hs hsσ hq ha hsum hc

end AtomicSystem

end ApproximationScheme
