/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Fields.Basic
public import LeanPool.CompositionAlgebrasOverRings.Composition.Tower

/-!
# Surjective quaternion norms split the octonions (`GPR 23.21`)

*If every quaternion algebra over `F` has surjective norm, then every octonion algebra over `F` is
split.*

The mechanism is the Cayley–Dickson description of an octonion algebra. By `GPR 19.17` an
eight-dimensional composition algebra over a field is `Cay(B, μ)` for a four-dimensional
composition subalgebra `B` — a quaternion algebra — and a scalar `μ = -n(v) ∈ F ˣ`. The norm of the
double is

  `n(b₁ + b₂ v) = n_B(b₁) - μ n_B(b₂)`,

so a solution of `n_B(b) = μ` produces the nonzero null vector `b + v`. Surjectivity of `n_B`
supplies that solution, and `GPR 22.18` turns the null vector into splitness. In the language of
Pfister forms: the octonion norm is the three-fold form `⟪μ⟫ ⊗ n_B` obtained by doubling the
two-fold form `n_B`, and a form `n_B ⊥ (-μ) n_B` is isotropic as soon as `n_B` represents `μ`.

The hypothesis is stated for the four-dimensional subalgebras the proof actually consumes, rather
than for every quaternion algebra over `F` — the same discipline as
`Composition/Reduced/Capstone.lean`. Nothing is lost: the subalgebras produced by `GPR 19.17` are
quaternion algebras in the ordinary sense.

## Main results

* `ConicAlgebra.IsComposition.isSplitOfRank_eight_of_forall_surjective_norm` : **`GPR 23.21`**.

## Not formalized here

`GPR 23.21` is applied in the literature to fields for which surjectivity of quaternion norms is
known: totally imaginary number fields and global fields with no real places (via `GPR 23.22`, the
Albert–Jacobson refinement), and `ℂ(x, y)`. Each of these inputs is a substantial theorem of number
theory or of the theory of function fields — the number-field case rests on the Hasse–Minkowski
theorem, which is out of scope here — and none of them is available in mathlib. The
mechanism above is therefore stated with surjectivity as a hypothesis, which is the part of
`GPR 23.21` that belongs to the theory of composition algebras.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 19.17, 22.18,
  23.21, 23.22.
-/

@[expose] public section

universe u v

open QuadraticMap (polar)

namespace ConicAlgebra

variable {K : Type u} {A : Type v} [Field K] [NonAssocRing A] [Module K A]
  [SMulCommClass K A A] [IsScalarTower K A A] [Module.Finite K A] [Module.Projective K A]
  {C : ConicAlgebra K A}

/-- **`GPR 23.21`.** Let `C` be an eight-dimensional composition algebra over a field `K` and
suppose that every four-dimensional composition subalgebra of `C` with regular restricted norm has
surjective norm. Then `C` is split.

`GPR 19.17` writes `C` as `Cay(B, -n(v))` for such a subalgebra `B`; a vector of `B` whose norm is
`-n(v)` gives, together with `v`, a nonzero null vector of the norm of `C`. -/
theorem IsComposition.isSplitOfRank_eight_of_forall_surjective_norm
    (h : C.IsComposition.{u, v, u}) (hA : Module.finrank K A = 8)
    (hsurj : ∀ B : NonAssocSubalgebra K A, Module.finrank K B = 4 →
      QuadraticForm.IsGPRRegular (C.restrict B).norm →
      Function.Surjective (C.restrict B).norm) :
    C.IsSplitOfRank 8 := by
  have := nontrivial_of_conicAlgebra C
  have := h.isAlternative
  obtain ⟨B, v, s, hs2, hsrank, -, hBreg, hbij, -, -, hnorm⟩ :=
    h.exists_bijective_cayToAlgebra (isLGRing_of_field K)
      (Module.rankAtStalk_eq_of_finrank_eq hA) (by omega)
  have hBfin : Module.finrank K B = 4 :=
    Module.finrank_of_rankAtStalk_eq ((rankAtStalk_toSubmodule B) ▸ hsrank) |>.trans (by omega)
  obtain ⟨x, hx⟩ := hsurj B hBfin hBreg (-C.norm v)
  set p : Cay (C.restrict B) (-C.norm v) := ((x, (1 : B)) : B × B) with hp
  -- The Cayley–Dickson norm of `(x, 1)` is `n_B(x) + n(v)`, which vanishes by the choice of `x`.
  have hpnorm : ((C.restrict B).cay (-C.norm v)).norm p = 0 := by
    rw [cay_norm_apply]
    change (C.restrict B).norm x - -C.norm v * (C.restrict B).norm 1 = 0
    rw [(C.restrict B).norm_one, hx]
    ring
  -- `(x, 1)` is nonzero because its second coordinate is the identity of `B`.
  have hp0 : p ≠ 0 := by
    intro hzero
    have h1 : ((1 : B) : A) = ((0 : B) : A) :=
      congrArg (fun z : B ↦ (z : A)) (congrArg Prod.snd hzero)
    simp only [OneMemClass.coe_one, ZeroMemClass.coe_zero] at h1
    exact one_ne_zero h1
  refine h.isSplitOfRank_of_exists_ne_zero_norm_eq_zero hA (Or.inr (Or.inr rfl))
    (x := cayToAlgebra C B v p) ?_ ((hnorm p).trans hpnorm)
  intro hzero
  exact hp0 (hbij.1 (hzero.trans (map_zero (cayToAlgebra C B v)).symm))

end ConicAlgebra
