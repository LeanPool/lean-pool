/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.HorrocksRankOne
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.Module

/-!
# Monic lattices in projective `A[X]`-modules over a local ring

Let `A` be a local ring and `P` a finitely generated projective `A[X]`-module. A *monic lattice*
of rank `n` in `P` is an injective `A[X]`-linear map `F : A[X]ⁿ → P` whose image contains `s • P`
for a monic polynomial `s`; equivalently, the images of the standard basis vectors form a basis of
`P` after inverting the monic polynomials. This file proves that a projective module with a monic
lattice is free, following the proof of the local Horrocks theorem of Nashier and Nichols as
presented by Lombardi and Quitté (Theorem XVI.4.3): by induction on `n`, a monic lattice of rank
`n ≥ 2` can be modified so that its first vector `z` is unimodular in `P` (the "little lemma",
together with the comaximality of the monic polynomials and `1 + m[X]`), and then
`P ≅ A[X] ⊕ ker φ` with `φ z = 1` carries a monic lattice of rank `n - 1`. The rank one case is
`exists_monic_eq_span`.

## Main results

* `exists_functional_map_eq`: for a monic lattice of rank at least two there is a functional
  `φ : P → A[X]` killing the first lattice vector modulo `m[X]` and taking the value `1` modulo
  `m[X]` somewhere.
* `exists_unimodular_lattice`: the little lemma; the first vector of a modified lattice is
  unimodular.
* `free_of_lattice`: a finitely generated projective module with a monic lattice is free.

## References

* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
* B. Nashier, W. Nichols, *A note on projective modules over polynomial rings*, 1987.
-/

@[expose] public section

universe u v

open Polynomial IsLocalRing

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]
variable {P : Type v} [AddCommGroup P] [Module A[X] P]

/-- A monic polynomial acts injectively on a projective `A[X]`-module. -/
theorem eq_zero_of_monic_smul_eq_zero [Module.Projective A[X] P] {s : A[X]} (hs : s.Monic)
    {p : P} (h : s • p = 0) : p = 0 :=
  Module.Flat.isSMulRegular_of_nonZeroDivisors hs.mem_nonZeroDivisors
    (h.trans (smul_zero s).symm)

/-- The coordinates of `s • p` with respect to an injective `F : A[X]ⁿ → P` whose image contains
`s • P`. -/
theorem exists_coord {n : ℕ} {F : (Fin n → A[X]) →ₗ[A[X]] P} (hF : Function.Injective F)
    {s : A[X]} (hsF : ∀ p, s • p ∈ LinearMap.range F) :
    ∃ G : P →ₗ[A[X]] (Fin n → A[X]), (∀ p, F (G p) = s • p) ∧ ∀ c, G (F c) = s • c := by
  let G := (LinearEquiv.ofInjective F hF).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range F) (s • LinearMap.id) hsF
  have hG : ∀ p, F (G p) = s • p := fun p => by
    simp only [G, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.ofInjective_symm_apply, LinearMap.codRestrict_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
  exact ⟨G, hG, fun c => hF (by rw [hG, map_smul])⟩

section Local

variable [IsLocalRing A]

/-- A finitely generated projective `A[X]`-module with a monic lattice of rank one is free: it is
isomorphic to a projective ideal containing a monic polynomial, which is principal
(`exists_monic_eq_span`). -/
theorem free_of_lattice_one [Module.Finite A[X] P] [Module.Projective A[X] P]
    (F : (Fin 1 → A[X]) →ₗ[A[X]] P) (hF : Function.Injective F) {s : A[X]} (hs : s.Monic)
    (hsF : ∀ p, s • p ∈ LinearMap.range F) : Module.Free A[X] P := by
  obtain ⟨G, hG, hGF⟩ := exists_coord hF hsF
  let G0 := LinearMap.proj (R := A[X]) (φ := fun _ : Fin 1 => A[X]) 0 ∘ₗ G
  have hG0 : Function.Injective G0 := by
    intro p q hpq
    have h1 : G p = G q := funext fun i => by
      rw [Subsingleton.elim i 0]
      exact hpq
    have h2 := congrArg F h1
    rw [hG, hG, ← sub_eq_zero, ← smul_sub] at h2
    exact sub_eq_zero.mp (eq_zero_of_monic_smul_eq_zero hs h2)
  let e := LinearEquiv.ofInjective G0 hG0
  have : Module.Projective A[X] (LinearMap.range G0) := Module.Projective.of_equiv e
  have hfg : (LinearMap.range G0).FG := Module.Finite.iff_fg.mp (Module.Finite.equiv e)
  have hsb : s ∈ LinearMap.range G0 := ⟨F (Pi.single 0 1), by simp [G0, hGF]⟩
  obtain ⟨g, hg, hbg⟩ := exists_monic_eq_span (LinearMap.range G0) hfg hs hsb
  have hinj : Function.Injective (LinearMap.toSpanSingleton A[X] A[X] g) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hg.mem_nonZeroDivisors).mp hr
  let e' := LinearEquiv.ofInjective _ hinj ≪≫ₗ LinearEquiv.ofEq _ _
    ((LinearMap.span_singleton_eq_range A[X] A[X] g).symm.trans hbg.symm)
  exact Module.Free.of_equiv (e' ≪≫ₗ e.symm)

/-- For a monic lattice of rank at least two there is a functional `φ : P → A[X]` whose value at
the first lattice vector lies in `m[X]` and which takes a value congruent to `1` modulo `m[X]`:
the second coordinate functional, reduced modulo `m[X]` and divided by a generator of its image
in the principal ideal ring `k[X]`, lifted along `A[X] → k[X]` by projectivity. -/
theorem exists_functional_map_eq [Module.Projective A[X] P] {m : ℕ}
    (F : (Fin (m + 2) → A[X]) →ₗ[A[X]] P) (hF : Function.Injective F) {s : A[X]} (hs : s.Monic)
    (hsF : ∀ p, s • p ∈ LinearMap.range F) :
    ∃ (φ : P →ₗ[A[X]] A[X]) (w : P), (φ (F (Pi.single 0 1))).map (residue A) = 0 ∧
      (φ w).map (residue A) = 1 := by
  classical
  obtain ⟨G, -, hGF⟩ := exists_coord hF hsF
  let _ : Algebra A[X] (ResidueField A)[X] := (mapRingHom (residue A)).toAlgebra
  let π : A[X] →ₗ[A[X]] (ResidueField A)[X] := Algebra.linearMap _ _
  have hπ : ∀ x, π x = x.map (residue A) := fun _ => rfl
  have hπs : Function.Surjective π := map_surjective _ residue_surjective
  let χ := π ∘ₗ LinearMap.proj (R := A[X]) (φ := fun _ : Fin (m + 2) => A[X]) 1 ∘ₗ G
  have hχ : ∀ c, χ (F c) = (s * c 1).map (residue A) := fun c => by
    simp [χ, hGF, hπ]
  set J := Submodule.span (ResidueField A)[X] (Set.range χ)
  have hJ : ∀ y ∈ J, ∃ p, χ p = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, rfl⟩ := hy
      obtain ⟨q, rfl⟩ := hz
      exact ⟨p + q, map_add _ _ _⟩
    | smul c y _ hy =>
      obtain ⟨p, rfl⟩ := hy
      obtain ⟨c', rfl⟩ := hπs c
      exact ⟨c' • p, by rw [map_smul]; rfl⟩
  set γ := Submodule.IsPrincipal.generator J
  have hγ0 : γ ≠ 0 := by
    intro h0
    rw [← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at h0
    have h1 : χ (F (Pi.single 1 1)) ∈ J := Submodule.subset_span ⟨_, rfl⟩
    rw [h0, Submodule.mem_bot, hχ] at h1
    simp only [Pi.single_eq_same, mul_one] at h1
    exact (hs.map (residue A)).ne_zero h1
  have hdvd : ∀ p, γ ∣ χ p := fun p =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd J).mp (Submodule.subset_span ⟨p, rfl⟩)
  have hc : ∀ p, γ * (χ p / γ) = χ p := fun p => EuclideanDomain.mul_div_cancel' hγ0 (hdvd p)
  let c : P →ₗ[A[X]] (ResidueField A)[X] :=
    { toFun := fun p => χ p / γ
      map_add' := fun p q => mul_left_cancel₀ hγ0 (by rw [mul_add, hc, hc, hc, map_add])
      map_smul' := fun r p => mul_left_cancel₀ hγ0 (by
        rw [hc, RingHom.id_apply, map_smul, Algebra.smul_def, Algebra.smul_def, mul_left_comm,
          hc]) }
  obtain ⟨w, hw⟩ := hJ γ (Submodule.IsPrincipal.generator_mem J)
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property π c hπs
  refine ⟨φ, w, ?_, ?_⟩
  · rw [← hπ, ← LinearMap.comp_apply, hφ]
    refine mul_left_cancel₀ hγ0 ?_
    rw [show c (F (Pi.single 0 1)) = χ (F (Pi.single 0 1)) / γ from rfl, hc, hχ, mul_zero]
    simp
  · rw [← hπ, ← LinearMap.comp_apply, hφ]
    refine mul_left_cancel₀ hγ0 ?_
    rw [show c w = χ w / γ from rfl, hc, hw, mul_one]

/-- **Little lemma** (Lombardi–Quitté, proof of Theorem XVI.4.3). A monic lattice of rank at least
two can be modified so that its first vector `z` is unimodular, `φ z = 1` for a functional `φ`.
With `w` and `φ₀` from `exists_functional_map_eq` and `s • w = F β`, the vector
`z = w + Xʳ • F e₀`, for `r > deg β₀`, replaces the first lattice vector, the polynomial
`β₀ + s Xʳ` being monic; the values of functionals at `z` then form an ideal containing a monic
polynomial and an element `φ₀ z` of `1 + m[X]`, which is the unit ideal. -/
theorem exists_unimodular_lattice [Module.Projective A[X] P] {m : ℕ}
    (F : (Fin (m + 2) → A[X]) →ₗ[A[X]] P) (hF : Function.Injective F) {s : A[X]} (hs : s.Monic)
    (hsF : ∀ p, s • p ∈ LinearMap.range F) :
    ∃ (F' : (Fin (m + 2) → A[X]) →ₗ[A[X]] P) (s' : A[X]) (φ : P →ₗ[A[X]] A[X]),
      Function.Injective F' ∧ s'.Monic ∧ (∀ p, s' • p ∈ LinearMap.range F') ∧
        φ (F' (Pi.single 0 1)) = 1 := by
  classical
  obtain ⟨φ₀, w, hφ₀, hφw⟩ := exists_functional_map_eq F hF hs hsF
  obtain ⟨G, hG, -⟩ := exists_coord hF hsF
  set e₀ : Fin (m + 2) → A[X] := Pi.single 0 1
  set y₀ := F e₀
  set β := G w
  set r := (β 0).natDegree + 1
  set z := w + (X ^ r : A[X]) • y₀
  set t := β 0 + s * X ^ r
  have hsX : (s * X ^ r).Monic := hs.mul (monic_X_pow r)
  have ht : t.Monic := by
    refine hsX.add_of_right ?_
    rw [degree_eq_natDegree hsX.ne_zero, hs.natDegree_mul (monic_X_pow r), natDegree_X_pow]
    refine degree_le_natDegree.trans_lt ?_
    exact_mod_cast (by omega : (β 0).natDegree < s.natDegree + r)
  let F' := F +
    (LinearMap.proj (R := A[X]) (φ := fun _ : Fin (m + 2) => A[X]) 0).smulRight (z - y₀)
  have hF'a : ∀ c, F' c = F c + c 0 • (z - y₀) := fun c => rfl
  have hF'0 : F' e₀ = z := by
    rw [hF'a]
    simp [e₀, y₀]
  have hsz : s • (z - y₀) = F (β + (s * X ^ r - s) • e₀) := by
    rw [map_add, map_smul, hG]
    simp only [z, y₀, smul_sub, smul_add, smul_smul, sub_smul]
    abel
  have hs' : ∀ c, s • F' c = F (s • c + c 0 • (β + (s * X ^ r - s) • e₀)) := by
    intro c
    rw [hF'a, smul_add, smul_comm s (c 0), hsz]
    simp only [map_add, map_smul]
  have hinj : Function.Injective F' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : s • c + c 0 • (β + (s * X ^ r - s) • e₀) = 0 :=
      hF (by rw [← hs', hc, smul_zero, map_zero])
    have h2 := congrFun h1 0
    simp only [e₀, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
      Pi.zero_apply] at h2
    have hc0 : c 0 = 0 := by
      have : c 0 * t = 0 := by
        rw [← h2]
        ring
      exact (mul_right_mem_nonZeroDivisors_eq_zero_iff ht.mem_nonZeroDivisors).mp this
    rw [hc0, zero_smul, add_zero] at h1
    funext i
    have := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hs.mem_nonZeroDivisors).mp this
  set γ' : Fin (m + 2) → A[X] := Function.update (-β) 0 s
  have hγ' : F' γ' = t • y₀ := by
    rw [hF'a, show γ' 0 = s from Function.update_self .., hsz, ← map_add]
    have : γ' + (β + (s * X ^ r - s) • e₀) = t • e₀ := by
      funext i
      by_cases hi : i = 0
      · subst hi
        simp only [γ', e₀, t, Pi.add_apply, Function.update_self, Pi.smul_apply,
          Pi.single_eq_same, smul_eq_mul, mul_one]
        ring
      · simp [γ', e₀, hi, Function.update_of_ne]
    rw [this, map_smul]
  have htF : ∀ c, t • F c = F' (t • c + c 0 • (γ' - t • e₀)) := by
    intro c
    rw [map_add, map_smul, map_smul, map_sub, map_smul, hγ', hF'0, hF'a]
    module
  have hsF' : ∀ p, (t * s) • p ∈ LinearMap.range F' := fun p =>
    ⟨t • G p + G p 0 • (γ' - t • e₀), by rw [← htF, hG, smul_smul]⟩
  obtain ⟨G', -, hG'F⟩ := exists_coord hinj hsF'
  let J : Ideal A[X] := LinearMap.range
    (LinearMap.applyₗ (R := A[X]) (M₂ := A[X]) z : (P →ₗ[A[X]] A[X]) →ₗ[A[X]] A[X])
  have hJ1 : t * s ∈ J := ⟨LinearMap.proj (R := A[X]) (φ := fun _ : Fin (m + 2) => A[X]) 0 ∘ₗ G',
    by simp [← hF'0, hG'F, e₀]⟩
  have hJ2 : φ₀ z ∈ J := ⟨φ₀, rfl⟩
  have hφz : (φ₀ z).map (residue A) = 1 := by
    simp only [z, map_add, map_smul, smul_eq_mul, Polynomial.map_add, Polynomial.map_mul, hφw,
      y₀, e₀, hφ₀, mul_zero, add_zero]
  have h1 : (1 : A[X]) ∈ J := by
    rw [eq_top_of_monic_mem_of_map_eq_one (ht.mul hs) hJ1 hJ2 hφz]
    exact Submodule.mem_top
  obtain ⟨φ, hφ⟩ := h1
  exact ⟨F', t * s, φ, hinj, ht.mul hs, hsF', by rw [hF'0]; exact hφ⟩

omit [IsLocalRing A] in
/-- If the first vector `z` of a monic lattice of rank `m + 2` in `P` satisfies `φ z = 1`, then
`ker φ` carries a monic lattice of rank `m + 1` and `P ≅ A[X] × ker φ`; so `P` is free as soon as
modules with monic lattices of rank `m + 1` are. -/
theorem free_of_lattice_of_unimodular [Module.Finite A[X] P] [Module.Projective A[X] P] {m : ℕ}
    (ih : ∀ (Q : Type v) [AddCommGroup Q] [Module A[X] Q] [Module.Finite A[X] Q]
      [Module.Projective A[X] Q] (F : (Fin (m + 1) → A[X]) →ₗ[A[X]] Q) (s : A[X]),
      Function.Injective F → s.Monic → (∀ q : Q, s • q ∈ LinearMap.range F) → Module.Free A[X] Q)
    (F : (Fin (m + 2) → A[X]) →ₗ[A[X]] P) (s : A[X]) (φ : P →ₗ[A[X]] A[X])
    (hF : Function.Injective F) (hs : s.Monic) (hsF : ∀ p, s • p ∈ LinearMap.range F)
    (hφ : φ (F (Pi.single 0 1)) = 1) : Module.Free A[X] P := by
  classical
  set z := F (Pi.single 0 1)
  set K := LinearMap.ker φ
  let ρ : P →ₗ[A[X]] K := LinearMap.codRestrict K (LinearMap.id - φ.smulRight z)
    (fun p => LinearMap.mem_ker.mpr (by simp [hφ]))
  have hρ : ∀ p, (ρ p : P) = p - φ p • z := fun _ => rfl
  have hρK : ∀ k : K, ρ k = k := fun k =>
    Subtype.ext (by rw [hρ, LinearMap.mem_ker.mp k.2, zero_smul, sub_zero])
  have : Module.Projective A[X] K := Module.Projective.of_split K.subtype ρ (LinearMap.ext hρK)
  have : Module.Finite A[X] K := Module.Finite.of_surjective ρ fun k => ⟨k, hρK k⟩
  let ι : (Fin (m + 1) → A[X]) →ₗ[A[X]] (Fin (m + 2) → A[X]) :=
    { toFun := fun c => Fin.cons 0 c
      map_add' := fun c d => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      map_smul' := fun a c => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  have hι : ∀ c, ι c = Fin.cons 0 c := fun _ => rfl
  let F'' := ρ ∘ₗ F ∘ₗ ι
  have hF'' : ∀ c, (F'' c : P) = F (ι c) - φ (F (ι c)) • z := fun _ => rfl
  have hinj : Function.Injective F'' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : F (ι c) = F (φ (F (ι c)) • Pi.single 0 1) := by
      have := congrArg Subtype.val hc
      rw [hF''] at this
      rw [map_smul]
      exact sub_eq_zero.mp this
    have h2 := hF h1
    funext j
    have := congrFun h2 j.succ
    simpa [hι] using this
  have hrange : ∀ k : K, s • k ∈ LinearMap.range F'' := by
    intro k
    obtain ⟨δ, hδ⟩ := hsF k
    refine ⟨Fin.tail δ, Subtype.ext ?_⟩
    have hdec : δ = δ 0 • Pi.single 0 1 + ι (Fin.tail δ) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [hι, Fin.tail]
    have hφk : φ (F δ) = 0 := by rw [hδ, map_smul, LinearMap.mem_ker.mp k.2, smul_zero]
    rw [hdec, map_add, map_smul, map_add, map_smul, hφ, smul_eq_mul, mul_one] at hφk
    rw [hF'', SetLike.val_smul, ← hδ]
    conv_rhs => rw [hdec, map_add, map_smul]
    rw [eq_neg_of_add_eq_zero_right hφk]
    module
  have : Module.Free A[X] K := ih K F'' s hinj hs hrange
  let e : P ≃ₗ[A[X]] A[X] × K := LinearEquiv.ofLinearMap (φ.prod ρ)
    ((LinearMap.toSpanSingleton A[X] P z).coprod K.subtype)
    (by
      refine LinearMap.prod_ext (LinearMap.ext fun a => ?_) (LinearMap.ext fun k => ?_)
      · refine Prod.ext ?_ (Subtype.ext ?_)
        · simp [hφ]
        · simp [hρ, hφ]
      · refine Prod.ext ?_ (Subtype.ext ?_)
        · simp [LinearMap.mem_ker.mp k.2]
        · simp [hρK])
    (LinearMap.ext fun p => by simp [hρ])
  exact Module.Free.of_equiv e.symm

/-- A finitely generated projective `A[X]`-module over a local ring `A` with a monic lattice is
free (Lombardi–Quitté, Theorem XVI.4.3, in its lattice form). -/
theorem free_of_lattice : ∀ (n : ℕ) {P : Type v} [AddCommGroup P] [Module A[X] P]
    [Module.Finite A[X] P] [Module.Projective A[X] P] (F : (Fin n → A[X]) →ₗ[A[X]] P)
    (s : A[X]), Function.Injective F → s.Monic → (∀ p : P, s • p ∈ LinearMap.range F) →
      Module.Free A[X] P
  | 0, P, _, _, _, _, F, s, _, hs, hsF => by
    have h : ∀ p : P, p = 0 := fun p => by
      obtain ⟨c, hc⟩ := hsF p
      refine eq_zero_of_monic_smul_eq_zero hs ?_
      rw [← hc, Subsingleton.elim c 0, map_zero]
    have : Subsingleton P := ⟨fun p q => by rw [h p, h q]⟩
    infer_instance
  | 1, _, _, _, _, _, F, _, hF, hs, hsF => free_of_lattice_one F hF hs hsF
  | m + 2, _, _, _, _, _, F, _, hF, hs, hsF => by
    obtain ⟨F', s', φ, hF', hs', hsF', hφ⟩ := exists_unimodular_lattice F hF hs hsF
    exact free_of_lattice_of_unimodular
      (fun _ _ _ _ _ G t hG ht htG => free_of_lattice (m + 1) G t hG ht htG) F' s' φ hF' hs'
      hsF' hφ

end Local

end LeanPool.QuillenSuslin
