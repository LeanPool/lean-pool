/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnCohomologyRingBridge
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.ConstructRPAlpha
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.SphereTopHomology
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.ModTwoDegreeComparison
import Mathlib.Tactic.Positivity.Finset
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.RPnTopClassAlphaPower

/-!
# Conditional odd-map cohomological comparison

Proves the double-cover naturality square on mod-two cohomology and derives odd integer degree of
an odd sphere self-map from an orientation and two named inputs, `ModTwoTopClassComparison` and
`OddMapFixesTopClass`. Neither input is proved in this project, so `oddMap_degree_odd_final` is a
conditional statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereOddDegree

/-! ## 1. Element-level double-cover naturality -/

/-- **Element-level naturality square of the double cover** at degree `k`.
Applying the morphism identity `inducedOnRP_pullback_naturality` to a cohomology
class `a ∈ Hᵏ(RPⁿ; F₂)` gives

```text
proj^*(fbar^* a) = f^*(proj^* a) in Hᵏ(Sⁿ; F₂).
```
-/
theorem inducedOnRP_pullback_naturality_apply {n : ℕ} (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (k : ℕ) (a : rpCohomology n k) :
    projPullback n k (inducedOnRPPullback f hf k a)
      = spherePullback f k (projPullback n k a) := by
  have h := inducedOnRP_pullback_naturality f hf k
  have happ := congrArg (fun φ : rpCohomology n k ⟶ sphereCohomology n k => φ a) h
  simpa only [ModuleCat.comp_apply] using happ

/-- **`f^*` fixes the pulled-back top class.** If the descended odd map `fbar`
fixes a top class `a ∈ Hⁿ(RPⁿ; F₂)` (`fbar^* a = a`), then the sphere self-map
`f` fixes its image `proj^* a ∈ Hⁿ(Sⁿ; F₂)` under the double-cover pullback:

```text
f^*(proj^* a) = proj^* a.
```

This pushes `fbar^* a = a` across the double-cover naturality square. For `n ≥ 1`
the class `proj^* a` vanishes, so the identity then carries no degree information. -/
theorem spherePullback_fixes_projPullback {n : ℕ} (f : C(Sphere n, Sphere n))
    (hf : IsOddMap f) (a : rpCohomology n n)
    (ha : inducedOnRPPullback f hf n a = a) :
    spherePullback f n (projPullback n n a) = projPullback n n a := by
  have h := inducedOnRP_pullback_naturality_apply f hf n a
  rw [ha] at h
  exact h.symm

/-! ## 2. The mod-two top-class comparison

`ModTwoTopClassComparison e` is a single named predicate, uniform over all sphere self-maps and
all nonzero top `F₂`-classes. It is an input of the theorem in §3 and is not proved in this
project. -/

/-- **The mod-two top-class / degree comparison.** Relative to a chosen
identification
`e : SphereTopHomologyIso n` (which fixes the integer degree `degreeOfIso e`), it
asserts: whenever a self-map `f` of `Sⁿ` **fixes a nonzero top class**
`c ∈ Hⁿ(Sⁿ; F₂)` (`f^* c = c`, `c ≠ 0`), its integer degree is **odd mod 2**
(`(degree f : ZMod 2) = 1`).

It states that the action on a nonzero top mod-two cohomology class determines
the parity of the integer degree. `modTwoTopClassComparison_of_topHomologyScalar`
reduces it to `ModTwoTopHomologyScalar`. -/
def ModTwoTopClassComparison {n : ℕ} (e : SphereTopHomologyIso n) : Prop :=
  ∀ (f : C(Sphere n, Sphere n)) (c : sphereCohomology n n),
    spherePullback f n c = c → c ≠ 0 → (degreeOfIso e f : ZMod 2) = 1

/-! ### Reduction of the comparison to the top `F₂`-homology scalar action

The comparison `ModTwoTopClassComparison e` is here reduced — fully formalized,
using only the library's *proved* universal-coefficient machinery over `F₂`
(`kroneckerMap_naturality_apply` and `kroneckerMap_injective`) — to the single,
precise statement that the `F₂` pushforward on the top homology `Hₙ(Sⁿ; F₂)` acts
as the scalar `(degree f mod 2)`. This isolates the exact homological scalar statement from which
the comparison
follows. -/

/-- **The top `F₂`-homology scalar action.** Relative to a chosen integral
identification `e : SphereTopHomologyIso n`, this asserts that the `F₂` homology
pushforward `f_* : Hₙ(Sⁿ; F₂) → Hₙ(Sⁿ; F₂)` of every self-map `f` acts as the
scalar `(degreeOfIso e f : ZMod 2)`.

Mathematically this is the conjunction of (i) `Hₙ(Sⁿ; F₂)` being one-dimensional
over `F₂` (so `f_*` is a scalar) and (ii) that scalar being the mod-`2` reduction
of the integer degree (coefficient-change compatibility `Hₙ(-;ℤ)⊗F₂ → Hₙ(-;F₂)`).
This project does not prove it. -/
def ModTwoTopHomologyScalar {n : ℕ} (e : SphereTopHomologyIso n) : Prop :=
  ∀ (f : C(Sphere n, Sphere n)) (z : homologyZMod2 (TopCat.of (Sphere n)) n),
    (homologyPushZMod2 (TopCat.ofHom f) n).hom z = (degreeOfIso e f : ZMod 2) • z

/-- **The comparison follows from the top `F₂`-homology scalar action.** This is a
proved, formalized reduction: it derives `ModTwoTopClassComparison e` from
`ModTwoTopHomologyScalar e` using only the library's proved `F₂` universal
coefficient theorem (the Kronecker classifier's naturality and injectivity).

Given a self-map `f` fixing a nonzero top class `c ∈ Hⁿ(Sⁿ; F₂)`, the Kronecker
functional `ψ = ⟨c, ·⟩` is nonzero (injectivity) and `f_*`-invariant (naturality
plus `f^* c = c`); the scalar hypothesis turns invariance into `ψ z = d · ψ z`
for `d = degree f mod 2`, and since some `ψ z = 1` in `F₂` we get `d = 1`. -/
theorem modTwoTopClassComparison_of_topHomologyScalar {n : ℕ}
    (e : SphereTopHomologyIso n) (h : ModTwoTopHomologyScalar e) :
    ModTwoTopClassComparison e := by
  intro f c hfix hc
  set X : TopCat := TopCat.of (Sphere n) with hX
  set ψ := (kroneckerMap X n).hom c with hψ
  have hψne : ψ ≠ 0 := by
    intro hcontra
    apply hc
    have hinj := kroneckerMap_injective (TopCat.of (Sphere n)) n
    exact hinj (hcontra.trans (map_zero (kroneckerMap (TopCat.of (Sphere n)) n).hom).symm)
  have hnat := kroneckerMap_naturality_apply (TopCat.ofHom f) n c
  have hfix' : (cohPullback (TopCat.ofHom f) n).hom c = c := hfix
  rw [hfix'] at hnat
  set d : ZMod 2 := (degreeOfIso e f : ZMod 2) with hd
  have key : ∀ z, ψ z = d * ψ z := by
    intro z
    have h1 : ψ z = ψ ((homologyPushZMod2 (TopCat.ofHom f) n).hom z) := by
      have := DFunLike.congr_fun hnat z
      simpa [LinearMap.comp_apply] using this
    rw [h f z, map_smul, smul_eq_mul] at h1
    exact h1
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hψne
  rw [LinearMap.zero_apply] at hz
  have hw1 : ψ z = 1 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (ψ z) with h0 | h0
    · exact absurd h0 hz
    · exact h0
  have hk := key z
  rw [hw1, mul_one] at hk
  exact hk.symm

/-! ## 3. Conditional odd-map degree theorem

For `n ≥ 1`, the class `proj^* α` in `H¹(Sⁿ; F₂)` vanishes. For `n > 1` this group is zero. For
`n = 1` the double cover has degree two and induces the zero map on `H¹(-; F₂)`. Thus
`proj^*(αⁿ) = 0`, so pullback along the double cover cannot detect the top class and the comparison
has to go through the double-cover *transfer*. The theorem below takes an orientation and two named
predicates as inputs and does not mention `proj^*`. -/

/-- **Odd self-maps fix a nonzero top `F₂`-class.** This is the RPⁿ / double-cover
descent half of the argument: every odd self-map `f` of `Sⁿ` fixes some nonzero class
`c ∈ Hⁿ(Sⁿ; F₂)` (`f^* c = c`, `c ≠ 0`).

Mathematically this holds because `f` descends to `fbar : RPⁿ → RPⁿ`, which acts
as the identity on the one-dimensional top group `Hⁿ(RPⁿ; F₂) = ⟨αⁿ⟩` (the unique
nonzero element is fixed by any ring map), and the double-cover *transfer*
homomorphism transports this to the nonzero sphere top class. That argument uses the
`F₂` transfer/Gysin sequence of the double cover `Sⁿ → RPⁿ`, which this project does not
formalize, so the property is an explicit input. -/
def OddMapFixesTopClass (n : ℕ) : Prop :=
  ∀ f : C(Sphere n, Sphere n), IsOddMap f →
    ∃ c : sphereCohomology n n, c ≠ 0 ∧ spherePullback f n c = c

/-- **Conditional odd-map degree theorem.**

```text
f odd ⇒ Odd (degree f),
```

assuming three inputs:

* `e : SphereTopHomologyIso n` — the integral top-homology identification
 `Hₙ(Sⁿ; ℤ) ≅ ℤ` that pins the integer degree `degreeOfIso e`. It exists for `n ≥ 1`
 (`sphereOrientationPosUnconditional`) and not for `n = 0`, where `H₀(S⁰; ℤ) ≅ ℤ²`;
* `hcmp : ModTwoTopClassComparison e` — a self-map fixing a nonzero top
 `F₂`-class has odd integer degree;
* `htop : OddMapFixesTopClass n` — an odd self-map fixes a nonzero top `F₂`-class.

The inputs `hcmp` and `htop` are not proved in this project. The remaining step is the
parity bridge `degreeOfIso_intCast_zmodTwo_eq_one_iff_odd`. -/
theorem oddMap_degree_odd_final {n : ℕ}
    (e : SphereTopHomologyIso n) (hcmp : ModTwoTopClassComparison e)
    (htop : OddMapFixesTopClass n)
    (f : C(Sphere n, Sphere n)) (hf : IsOddMap f) :
    Odd (degreeOfIso e f) := by
  obtain ⟨c, hc, hfix⟩ := htop f hf
  exact (degreeOfIso_intCast_zmodTwo_eq_one_iff_odd e f).mp (hcmp f c hfix hc)

/-! ## 4. Sanity specializations -/

/-- Sanity check: for the identity map every top class is fixed, so the
naturality core fires trivially — `f^*` fixes `proj^*` of any top class. -/
theorem spherePullback_fixes_projPullback_id {n : ℕ} (a : rpCohomology n n) :
    spherePullback (ContinuousMap.id (Sphere n)) n (projPullback n n a)
      = projPullback n n a :=
  spherePullback_fixes_projPullback (ContinuousMap.id (Sphere n)) (isOddMap_id n) a
    (by rw [inducedOnRPPullback_id]; rfl)

/-- Sanity check: for the antipodal map (which descends to the identity on
`RPⁿ`) every top class is fixed, so `(antipodal)^*` fixes `proj^*` of any top
class. -/
theorem spherePullback_fixes_projPullback_antipodal {n : ℕ} (a : rpCohomology n n) :
    spherePullback (antipodal n) n (projPullback n n a) = projPullback n n a :=
  spherePullback_fixes_projPullback (antipodal n) (isOddMap_antipodal n) a
    (by rw [inducedOnRPPullback_antipodal]; rfl)

end SphereOddDegree
