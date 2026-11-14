/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.NormNum
public import LeanPool.RoyStrongSix.M2.MainB
public import LeanPool.RoyStrongSix.Thm1.Main

/-!
# The multiplicity estimate, Waldschmidt's Theorem 1, and the strong six exponentials theorem

* `DwL_liftP`: on `K[X, Y]`, the derivations `D_w` along a list are `StrongSix.Thm1.invDers`
(reversed list).
* **`multEst_of_isAlgClosed`**: `MultEst K` for every algebraically closed `K` of characteristic `0`
  (Philippon 1986, Thm. 2.1, in the form proved by Roy, DALAG Ch. 8).
* **`multEst_Qb`**: `MultEst Qb`.
* **`waldschmidtTheorem1`**: Waldschmidt's Theorem 1, unconditionally.
* **`strongSixExponentials`**: Roy's strong six exponentials theorem, unconditionally.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module Submodule StrongSix.Thm1 StrongSix.Roy

namespace StrongSix.M2

variable {K : Type*} [Field K] {d0 d1 : ℕ}

theorem DwL_liftP (l : List (LieG K d0 d1)) (P : MvPolynomial (Var d0 d1) K) :
    DwL l (liftP P) = liftP (invDers l.reverse P) := by
  induction l generalizing P with
  | nil => rfl
  | cons w l ih =>
    rw [DwL_cons, Dw_liftP, ih, List.reverse_cons]
    simp only [invDers, List.foldr_append, List.foldr_cons, List.foldr_nil]

/-- **Philippon's multiplicity estimate** over an algebraically closed field of characteristic
  `0`. -/
theorem multEst_of_isAlgClosed [CharZero K] [IsAlgClosed K] : MultEst K := by
  intro d0 d1
  refine ⟨(Cst d0 d1 : ℝ), fun W S P T D0 D1 hS hP hPD _ hD0 hD1 hvan => ?_⟩
  have hPt : liftP P ∉ vanish (Set.univ : Set (GPt K d0 d1)) := by
    obtain ⟨g, hg⟩ := exists_coords_ne_zero hP
    intro h
    exact hg (by rw [← eval_liftP]; exact h g (Set.mem_univ _))
  have hvan' : ∀ g ∈ sig S (d0 + d1), ∀ l : List (LieG K d0 d1), (∀ w ∈ l, w ∈ W) →
      l.length ≤ (d0 + d1) * T → eval (pt g) (DwL l (liftP P)) = 0 := by
    rintro _ ⟨σ, hσ, rfl⟩ l hlW hl
    rw [DwL_liftP, eval_liftP]
    exact hvan σ hσ l.reverse (fun w hw => hlW w (List.mem_reverse.mp hw)) (by simp; omega)
  obtain ⟨h0, U, hprop, hbound⟩ :=
    multEstB W S hS (liftP P) hPt hD0 hD1 (liftP_mem_FLE hPD) hvan'
  refine ⟨h0, U, hprop, fun F hFS hFd => ?_⟩
  have h' := (Nat.cast_le (α := ℤ)).mp (hbound F hFS hFd)
  exact_mod_cast h'

/-- **The multiplicity estimate over `Qbar`.** -/
theorem multEst_Qb : MultEst Qb := by
  have : IsAlgClosed Qb := IsAlgClosure.isAlgClosed ℚ
  exact multEst_of_isAlgClosed

/-- **Waldschmidt's Theorem 1**, unconditionally. -/
theorem waldschmidtTheorem1 : WaldschmidtTheorem1 :=
  theorem1_of_multEst multEst_Qb

/-- **Roy's strong six exponentials theorem.** -/
theorem strongSixExponentials : StrongSixExponentials :=
  strongSix_of_multEst multEst_Qb

end StrongSix.M2

end LeanPool
