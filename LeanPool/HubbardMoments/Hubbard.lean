/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import LeanPool.HubbardMoments.PeierlsModel
public import LeanPool.HubbardMoments.FermionHopping
public import LeanPool.HubbardMoments.SchriefferWolff
public import LeanPool.HubbardMoments.TorusMoments
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The Hubbard hopping term and `H∞` from fermion operators

`HubbardMoments.hubbardHopping` is the hopping term `H_t = -t ∑ e^{iA} c†_{y s} c_{x s}` built
from the fermion operators of `HubbardMoments.Fermions`, for an arbitrary ordering `ord` of
the orbitals (any fermionic sign convention). `HubbardMoments.projectedHubbard` is
`H∞ = P₀ H_t P₀` in the configuration basis.

* `hubbardHopping_isHermitian`: `H_t` is Hermitian when `A` is antisymmetric;
* `hubbardHopping_isHoppingOperator`: `H_t` only connects Fock states one hop apart;
* `projectedHubbard_isProjectedHopping`: `H∞` has the three properties of
  `IsProjectedHopping`, for `t ≥ 0`;
* consequently the exact second-moment theorem holds for `H∞` itself
  (`secondMoment_projectedHubbard`, `secondMoment_projectedHubbard_torus`), and the
  Schrieffer–Wolff cross term vanishes for `H_t` itself
  (`secondMoment_hubbardHopping_sub_virtualOp`, `…_torus` for `L ≥ 4`).

This closes the gap stated in the documentation of `IsProjectedHopping` and
`IsHoppingOperator`.
-/

@[expose] public section

namespace HubbardMoments

open Finset Complex
open scoped Matrix

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ] [DecidableEq σ]

/-! ### Hubbard hopping with Peierls phases -/

variable (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (A : V → V → ℝ) (ord : V × σ ↪ ℕ)

/-- The matrix elements of `H_t`. -/
theorem hubbardHopping_apply (S' S : FockState V σ) :
    hubbardHopping G t A ord S' S = ∑ p ∈ arcs G, ∑ s,
      (-(t : ℂ) * exp (A p.2 p.1 * I)) *
        if (p.1, s) ∈ S ∧ (p.2, s) ∉ S.erase (p.1, s) ∧ S' = insert (p.2, s) (S.erase (p.1, s))
        then (-1) ^ (countBelow ord S (p.1, s) + countBelow ord (S.erase (p.1, s)) (p.2, s))
        else 0 :=
  fermionHopping_apply G _ ord S' S

/-- **`H_t` is Hermitian** when the Peierls phases are antisymmetric. -/
theorem hubbardHopping_isHermitian {A : V → V → ℝ} (hA : ∀ x y, G.Adj x y → A y x = -A x y) :
    (hubbardHopping G t A ord).IsHermitian :=
  fermionHopping_isHermitian G _ ord (fun i j hij => by rw [star_peierlsAmplitude, hA j i hij.symm])

/-- **`H_t` is a hopping operator**: it connects only Fock states one hop apart. -/
theorem hubbardHopping_isHoppingOperator : IsHoppingOperator G (hubbardHopping G t A ord) :=
  fermionHopping_isHoppingOperator G _ ord

/-! ### `H∞ = P₀ H_t P₀` -/

/-- **`H∞` built from fermion operators is a projected hopping operator.** For `t ≥ 0` and
antisymmetric Peierls phases, with any ordering of the orbitals. -/
theorem projectedHubbard_isProjectedHopping (ht : 0 ≤ t) {A : V → V → ℝ}
    (hA : ∀ x y, G.Adj x y → A y x = -A x y) :
    IsProjectedHopping G t (projectedHubbard G t A ord) := by
  refine ⟨projectedFermionHopping_isHermitian G _ ord ?_, ?_,
    projectedFermionHopping_apply_eq_zero G _ ord⟩
  · intro i j hij
    rw [star_peierlsAmplitude, hA j i hij.symm]
  · intro c i j hadj hci hcj
    simpa [projectedHubbard, peierlsAmplitude, Complex.norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht] using norm_projectedFermionHopping_move G
        (fun i j => peierlsAmplitude t (A j i)) ord hadj hci hcj

/-! ### Consequences -/

/-- **The exact second-moment theorem for `H∞` itself.** -/
theorem secondMoment_projectedHubbard (ht : 0 ≤ t) {A : V → V → ℝ}
    (hA : ∀ x y, G.Adj x y → A y x = -A x y) (n : σ → ℕ) (hB : (basis V n).Nonempty)
    (hN : 2 ≤ Fintype.card V) :
    secondMoment (basis V n) (projectedHubbard G t A ord) =
      (t : ℂ) ^ 2 * (2 * G.edgeFinset.card) * (∑ s, n s : ℕ) *
          ((Fintype.card V : ℂ) - (∑ s, n s : ℕ)) /
        ((Fintype.card V : ℂ) * ((Fintype.card V : ℂ) - 1)) :=
  second_moment (projectedHubbard_isProjectedHopping G t ord ht hA) n hB hN

/-- **No `1/U` correction for the Hubbard hopping term on a triangle-free graph.** -/
theorem secondMoment_hubbardHopping_sub_virtualOp (hG : G.CliqueFree 3)
    {B Q : Finset (FockState V σ)} (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1)
    (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) (U : ℝ) :
    secondMoment B (hubbardHopping G t A ord - (U : ℂ)⁻¹ • virtualOp Q (hubbardHopping G t A ord)) =
      secondMoment B (hubbardHopping G t A ord) +
        secondMoment B (virtualOp Q (hubbardHopping G t A ord)) / (U : ℂ) ^ 2 :=
  secondMoment_sub_virtualOp (hubbardHopping_isHoppingOperator G t A ord) hG hB hQ U

/-- **The second moment of `H∞` on the `L × L` torus** (`L ≥ 3`):
`μ₂ = t² · 4n(L² - n)/(L² - 1)`. -/
theorem secondMoment_projectedHubbard_torus {L : ℕ} (hL : 3 ≤ L) (ht : 0 ≤ t)
    {A : Fin L × Fin L → Fin L × Fin L → ℝ} (hA : ∀ x y, (torus L).Adj x y → A y x = -A x y)
    (ord : (Fin L × Fin L) × σ ↪ ℕ) (n : σ → ℕ) (hB : (basis (Fin L × Fin L) n).Nonempty) :
    secondMoment (basis (Fin L × Fin L) n) (projectedHubbard (torus L) t A ord) =
      (t : ℂ) ^ 2 * 4 * (∑ s, n s : ℕ) * ((L : ℂ) * L - (∑ s, n s : ℕ)) / ((L : ℂ) * L - 1) :=
  second_moment_torus hL (projectedHubbard_isProjectedHopping (torus L) t ord ht hA) n hB

/-- **No `1/U` correction for the Hubbard hopping term on the `L × L` torus**, `L ≥ 4`. -/
theorem secondMoment_hubbardHopping_sub_virtualOp_torus {L : ℕ} (hL : 4 ≤ L)
    (A : Fin L × Fin L → Fin L × Fin L → ℝ) (ord : (Fin L × Fin L) × σ ↪ ℕ)
    {B Q : Finset (FockState (Fin L × Fin L) σ)} (hB : ∀ a ∈ B, ∀ v, siteOcc a v ≤ 1)
    (hQ : ∀ m ∈ Q, ∃ w, 2 ≤ siteOcc m w) (U : ℝ) :
    secondMoment B (hubbardHopping (torus L) t A ord -
        (U : ℂ)⁻¹ • virtualOp Q (hubbardHopping (torus L) t A ord)) =
      secondMoment B (hubbardHopping (torus L) t A ord) +
        secondMoment B (virtualOp Q (hubbardHopping (torus L) t A ord)) / (U : ℂ) ^ 2 :=
  secondMoment_sub_virtualOp_torus hL (hubbardHopping_isHoppingOperator (torus L) t A ord) hB hQ U

end HubbardMoments
