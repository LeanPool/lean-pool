/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Transfer
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Intrinsic norms: the retract theorem

Let `R : X → Y` be a bounded linear map with `R (A n) ⊆ B n`; the model is the restriction
`L_p(ℝ^d) → L_p(Ω)` to a domain `Ω`.  The **restriction quasi-norm** of `g ∈ Y` is
`inf { ‖f‖_{A^s_q} : R f = g }` (`ApproximationScheme.restrictionNorm`).  The approximation
quasi-norm `‖g‖_{B^s_q}` uses only `g` and the scheme on `Y`, so it is *intrinsic*.

By functoriality the intrinsic quasi-norm is at most `‖R‖` times the quasi-norm of every
preimage (`ApproximationScheme.approxNormDyadic_le_iInf_restrict`).  The reverse holds as soon
as there is an **approximation-preserving extension**: a map `E : Y → X`, not necessarily
linear, with `R (E g) = g`, `‖E g‖ ≤ C ‖g‖` and `E^A_{2^(k+γ)}(E g) ≤ C E^B_{2^k}(g)` for all `k`
(`ApproximationScheme.ApproxExtension`).  Then `‖E g‖_{A^s_q} ≤ K ‖g‖_{B^s_q}`
(`ApproximationScheme.approxNormDyadic_extension_le`), so the two quasi-norms are equivalent
and `B^s_q = R(A^s_q)` (`ApproximationScheme.memApprox_iff_exists_restrict`).

On Lipschitz domains such an extension is built from near-best local polynomial approximations
on Whitney cubes (DeVore–Sharpley).  The extension may be nonlinear on purpose: in parts of the
quasi-Banach range no linear extension exists.
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {A : ApproximationScheme X} {B : ApproximationScheme Y} {s : ℝ} {q : ℝ≥0∞}

/-- An **approximation-preserving extension** for `R : X → Y`: a map `E : Y → X`, not
necessarily linear, with `R (E g) = g`, `‖E g‖ ≤ C ‖g‖` and
`E^A_{2^(k+γ)}(E g) ≤ C E^B_{2^k}(g)`. -/
structure ApproxExtension (R : X →L[ℝ] Y) (A : ApproximationScheme X)
    (B : ApproximationScheme Y) where
  /-- The extension. -/
  E : Y → X
  right_inv : ∀ g, R (E g) = g
  /-- The constant of the extension. -/
  C : ℝ≥0∞
  C_ne_top : C ≠ ∞
  /-- The loss `γ` in complexity: `2^k` becomes `2^(k+γ)`. -/
  loss : ℕ
  enorm_le : ∀ g, ‖E g‖ₑ ≤ C * ‖g‖ₑ
  approxError_le : ∀ g k, A.approxError (E g) (2 ^ (k + loss)) ≤ C * B.approxError g (2 ^ k)

/-- The constant `C (1 + (γ + 1) 2^(γs))` of the extension bound. -/
noncomputable def extensionConst (C : ℝ≥0∞) (γ : ℕ) (s : ℝ) : ℝ≥0∞ :=
  C * (1 + (γ + 1) * dyadicWeight s γ)

/-- The constant of the extension bound is finite. -/
theorem extensionConst_ne_top {C : ℝ≥0∞} (hC : C ≠ ∞) (γ : ℕ) (s : ℝ) :
    extensionConst C γ s ≠ ∞ :=
  ENNReal.mul_ne_top hC (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
    (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top γ, ENNReal.one_ne_top⟩)
    (ENNReal.dyadicWeight_ne_top s γ)⟩)

/-- **The extension preserves the approximation quasi-norm**: for `s ≥ 0` and `1 ≤ q ≤ ∞`,
`‖E g‖_{A^s_q} ≤ C (1 + (γ + 1) 2^(γs)) ‖g‖_{B^s_q}` in the dyadic quasi-norms. -/
theorem approxNormDyadic_extension_le {R : X →L[ℝ] Y} (Ex : ApproxExtension R A B) (hs : 0 ≤ s)
    (hq : 1 ≤ q) (g : Y) :
    A.approxNormDyadic s q (Ex.E g) ≤ extensionConst Ex.C Ex.loss s * B.approxNormDyadic s q g := by
  set γ := Ex.loss
  set C := Ex.C
  set w := dyadicWeight s γ
  set L := lqNorm q (B.approxSeqDyadic s g)
  set u : ℕ → ℝ≥0∞ := fun k => if k < γ then w * (C * ‖g‖ₑ) else 0
  set v : ℕ → ℝ≥0∞ := fun k => if γ ≤ k then w * C * B.approxSeqDyadic s g (k - γ) else 0
  have hpt : ∀ k, A.approxSeqDyadic s (Ex.E g) k ≤ u k + v k := fun k => by
    rcases lt_or_ge k γ with hk | hk
    · calc A.approxSeqDyadic s (Ex.E g) k
          = dyadicWeight s k * A.approxError (Ex.E g) (2 ^ k) := rfl
        _ ≤ w * (C * ‖g‖ₑ) := by
            gcongr
            · exact ENNReal.dyadicWeight_mono hs hk.le
            · exact (approxError_le_enorm _ _).trans (Ex.enorm_le g)
        _ ≤ u k + v k := by simp only [u, hk, ↓reduceIte]; exact le_self_add
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
      calc A.approxSeqDyadic s (Ex.E g) (j + γ)
          = dyadicWeight s (j + γ) * A.approxError (Ex.E g) (2 ^ (j + γ)) := rfl
        _ ≤ dyadicWeight s (j + γ) * (C * B.approxError g (2 ^ j)) := by
            gcongr; exact Ex.approxError_le g j
        _ = w * C * B.approxSeqDyadic s g j := by
            rw [ENNReal.dyadicWeight_add_nat, approxSeqDyadic]; ring
        _ ≤ u (j + γ) + v (j + γ) := by
            simp only [v, hk, ↓reduceIte, Nat.add_sub_cancel]; exact le_add_self
  have hu : lqNorm q u ≤ γ * (w * (C * ‖g‖ₑ)) := by
    refine (ENNReal.lqNorm_le_sum_of_eq_zero hq (range γ) fun k hk => by
      simp only [u, Finset.mem_range.not.1 hk, ↓reduceIte]).trans_eq ?_
    calc ∑ k ∈ range γ, u k = ∑ _k ∈ range γ, w * (C * ‖g‖ₑ) :=
          Finset.sum_congr rfl fun k hk => by simp only [u, Finset.mem_range.1 hk, ↓reduceIte]
      _ = γ * (w * (C * ‖g‖ₑ)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hv : lqNorm q v ≤ w * C * L := by
    calc lqNorm q v ≤ lqNorm q (fun j => w * C * B.approxSeqDyadic s g j) :=
          ENNReal.lqNorm_shiftRight_le γ (fun j => w * C * B.approxSeqDyadic s g j)
      _ = w * C * L := ENNReal.lqNorm_const_mul _ _
  have hgN : ‖g‖ₑ ≤ B.approxNormDyadic s q g := enorm_le_approxNormDyadic g
  have hLN : L ≤ B.approxNormDyadic s q g := lqNorm_le_approxNormDyadic g
  calc A.approxNormDyadic s q (Ex.E g)
      = ‖Ex.E g‖ₑ + lqNorm q (A.approxSeqDyadic s (Ex.E g)) := rfl
    _ ≤ C * ‖g‖ₑ + (lqNorm q u + lqNorm q v) := by
        gcongr
        · exact Ex.enorm_le g
        · exact (ENNReal.lqNorm_mono hpt).trans (ENNReal.lqNorm_add_le hq u v)
    _ ≤ C * ‖g‖ₑ + (γ * (w * (C * ‖g‖ₑ)) + w * C * L) := by gcongr
    _ ≤ C * B.approxNormDyadic s q g + (γ * (w * (C * B.approxNormDyadic s q g)) +
          w * C * B.approxNormDyadic s q g) := by gcongr
    _ = extensionConst C γ s * B.approxNormDyadic s q g := by
        simp only [extensionConst, w]; ring

/-- The **restriction quasi-norm** `inf { ‖f‖_{A^s_q} : R f = g }` (dyadic form), an infimum
over all preimages; it is `∞` when `g` has no preimage. -/
noncomputable def restrictionNorm (R : X →L[ℝ] Y) (A : ApproximationScheme X) (s : ℝ)
    (q : ℝ≥0∞) (g : Y) : ℝ≥0∞ :=
  ⨅ (f : X) (_ : R f = g), A.approxNormDyadic s q f

/-- **The intrinsic quasi-norm is at most the norm of every preimage**: for `R (A n) ⊆ B n`,
`‖g‖_{B^s_q} ≤ inf { ‖R‖ ‖f‖_{A^s_q} : R f = g }`. -/
theorem approxNormDyadic_le_iInf_restrict {R : X →L[ℝ] Y} (hR : ∀ n, ∀ a ∈ A n, R a ∈ B n)
    (g : Y) :
    B.approxNormDyadic s q g ≤ ⨅ (f : X) (_ : R f = g), ‖R‖ₑ * A.approxNormDyadic s q f :=
  le_iInf₂ fun f hf => hf ▸ approxNormDyadic_map_le R hR f

/-- **The restriction quasi-norm is at most the intrinsic one** when an approximation-preserving
extension exists: `inf { ‖f‖_{A^s_q} : R f = g } ≤ K ‖g‖_{B^s_q}`. -/
theorem restrictionNorm_le_approxNormDyadic {R : X →L[ℝ] Y} (Ex : ApproxExtension R A B)
    (hs : 0 ≤ s) (hq : 1 ≤ q) (g : Y) :
    restrictionNorm R A s q g ≤ extensionConst Ex.C Ex.loss s * B.approxNormDyadic s q g :=
  (iInf₂_le (Ex.E g) (Ex.right_inv g)).trans (approxNormDyadic_extension_le Ex hs hq g)

/-- **Intrinsic description of the restricted space**: with an approximation-preserving
extension, `g ∈ B^s_q` iff `g = R f` for some `f ∈ A^s_q`. -/
theorem memApprox_iff_exists_restrict {R : X →L[ℝ] Y} (hR : ∀ n, ∀ a ∈ A n, R a ∈ B n)
    (Ex : ApproxExtension R A B) (hs : 0 ≤ s) (hq : 1 ≤ q) {g : Y} :
    B.MemApprox s q g ↔ ∃ f, R f = g ∧ A.MemApprox s q f := by
  constructor
  · intro hg
    refine ⟨Ex.E g, Ex.right_inv g, (memApprox_iff_approxNormDyadic_lt_top hq hs).2 ?_⟩
    exact (approxNormDyadic_extension_le Ex hs hq g).trans_lt (ENNReal.mul_lt_top
      (extensionConst_ne_top Ex.C_ne_top Ex.loss s).lt_top
      ((memApprox_iff_approxNormDyadic_lt_top hq hs).1 hg))
  · rintro ⟨f, rfl, hf⟩
    exact hf.map R hR

end ApproximationScheme
