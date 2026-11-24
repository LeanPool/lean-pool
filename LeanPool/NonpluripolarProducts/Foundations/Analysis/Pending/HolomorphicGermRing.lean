/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Germ
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The ring of holomorphic germs at the origin

For a complex normed space `E`, we define the ring `HolGerm E = 𝒪_{E,0}` of germs at `0` of
functions `E → ℂ` which are complex differentiable at every point of a neighbourhood of `0`
(no analyticity is assumed). It is realised as a subring `holGermSubring E` of the ring of
all germs `Filter.Germ (𝓝 0) ℂ`.

## Main declarations

* `eventually_differentiableAt_add`, `…_mul`, `…_inv`, `…_comp_clm`, … : closure properties of
  the predicate `∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z`.
* `holGermSubring E`, `HolGerm E` : the ring of holomorphic germs at `0`.
* `HolGerm.mk f hf` : the germ of `f`, with `HolGerm.mk_eq_mk_iff`, `HolGerm.exists_eq_mk`
  and the algebraic `mk_*` lemmas.
* `HolGerm.eval` : evaluation at `0`, a ring homomorphism to `ℂ`.
* `HolGerm.isUnit_iff_eval_ne_zero`, the `IsLocalRing` instance and
  `HolGerm.mem_maximalIdeal_iff`.
* `HolGerm.comap L`, `HolGerm.comapEquiv L` : pull back along continuous linear maps
  (equivalences).
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending

open Filter Topology

section Differentiability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eventually_differentiableAt_const (c : ℂ) :
    ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (fun _ : E => c) z :=
  Eventually.of_forall fun _ => differentiableAt_const c

theorem eventually_differentiableAt_zero :
    ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (0 : E → ℂ) z :=
  eventually_differentiableAt_const 0

theorem eventually_differentiableAt_one :
    ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℂ (1 : E → ℂ) z :=
  eventually_differentiableAt_const 1

theorem eventually_differentiableAt_add {f g : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => f z + g z) z :=
  hf.and hg |>.mono fun _ h => h.1.add h.2

theorem eventually_differentiableAt_sub {f g : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => f z - g z) z :=
  hf.and hg |>.mono fun _ h => h.1.sub h.2

theorem eventually_differentiableAt_neg {f : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => -f z) z :=
  hf.mono fun _ h => h.neg

theorem eventually_differentiableAt_mul {f g : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => f z * g z) z :=
  hf.and hg |>.mono fun _ h => h.1.mul h.2

theorem eventually_differentiableAt_pow {f : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (n : ℕ) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => f z ^ n) z :=
  hf.mono fun _ h => h.fun_pow n

theorem eventually_differentiableAt_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℂ}
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => ∑ i ∈ s, f i z) z :=
  ((eventually_all_finset s).2 fun i _ => hf i).mono fun _ h => DifferentiableAt.fun_sum h

/-- A function differentiable near `0` is continuous at `0`. -/
theorem continuousAt_zero_of_eventually_differentiableAt {f : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) : ContinuousAt f 0 :=
  hf.self_of_nhds.continuousAt

theorem eventually_differentiableAt_inv {f : E → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (h0 : f 0 ≠ 0) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (fun z => (f z)⁻¹) z := by
  have hne : ∀ᶠ z in 𝓝 (0 : E), f z ≠ 0 :=
    (continuousAt_zero_of_eventually_differentiableAt hf).eventually_ne h0
  exact hf.and hne |>.mono fun _ h => h.1.inv h.2

/-- Differentiability near `0` transfers along a continuous linear map. -/
theorem eventually_differentiableAt_comp_clm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (L : E →L[ℂ] F) {f : F → ℂ}
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f ∘ L) z := by
  have hL : Tendsto L (𝓝 0) (𝓝 0) := by
    simpa using L.continuous.tendsto (0 : E)
  exact (hL.eventually hf).mono fun z h => h.comp z L.differentiableAt

end Differentiability

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Germs at `0` of functions complex differentiable on a neighbourhood of `0`. -/
def holGermSubring : Subring (Germ (𝓝 (0 : E)) ℂ) where
  carrier := {g | ∃ f : E → ℂ, (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) ∧
    (f : Germ (𝓝 (0 : E)) ℂ) = g}
  zero_mem' := ⟨0, eventually_differentiableAt_zero, rfl⟩
  one_mem' := ⟨1, eventually_differentiableAt_one, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun z => f z + g z, eventually_differentiableAt_add hf hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨fun z => f z * g z, eventually_differentiableAt_mul hf hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun z => -f z, eventually_differentiableAt_neg hf, rfl⟩

/-- The ring `𝒪_{E,0}` of holomorphic germs at `0`. -/
abbrev HolGerm : Type _ := holGermSubring E

namespace HolGerm

variable {E}

/-- The holomorphic germ at `0` of a function differentiable near `0`. -/
def mk (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) : HolGerm E :=
  ⟨(f : Germ (𝓝 (0 : E)) ℂ), f, hf, rfl⟩

@[simp]
theorem coe_mk (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    ((mk f hf : HolGerm E) : Germ (𝓝 (0 : E)) ℂ) = f :=
  rfl

theorem mk_eq_mk_iff {f g : E → ℂ} {hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z}
    {hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z} : mk f hf = mk g hg ↔ f =ᶠ[𝓝 0] g :=
  Subtype.ext_iff.trans Germ.coe_eq

theorem exists_eq_mk (g : HolGerm E) :
    ∃ (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z), g = mk f hf := by
  obtain ⟨g, f, hf, rfl⟩ := g
  exact ⟨f, hf, rfl⟩

/-- Induction principle: to prove a statement about all holomorphic germs, it suffices to
prove it for germs of the form `mk f hf`. -/
@[elab_as_elim]
theorem induction_on {p : HolGerm E → Prop} (g : HolGerm E)
    (h : ∀ (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z), p (mk f hf)) : p g := by
  obtain ⟨f, hf, rfl⟩ := exists_eq_mk g
  exact h f hf

theorem mk_zero : mk (0 : E → ℂ) eventually_differentiableAt_zero = 0 :=
  rfl

theorem mk_one : mk (1 : E → ℂ) eventually_differentiableAt_one = 1 :=
  rfl

theorem mk_add (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (fun z => f z + g z) (eventually_differentiableAt_add hf hg) = mk f hf + mk g hg :=
  rfl

theorem mk_add' (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (f + g) (eventually_differentiableAt_add hf hg) = mk f hf + mk g hg :=
  rfl

theorem mk_sub (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (fun z => f z - g z) (eventually_differentiableAt_sub hf hg) = mk f hf - mk g hg :=
  rfl

theorem mk_sub' (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (f - g) (eventually_differentiableAt_sub hf hg) = mk f hf - mk g hg :=
  rfl

theorem mk_neg (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    mk (fun z => -f z) (eventually_differentiableAt_neg hf) = -mk f hf :=
  rfl

theorem mk_neg' (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    mk (-f) (eventually_differentiableAt_neg hf) = -mk f hf :=
  rfl

theorem mk_mul (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (fun z => f z * g z) (eventually_differentiableAt_mul hf hg) = mk f hf * mk g hg :=
  rfl

theorem mk_mul' (f g : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z)
    (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z) :
    mk (f * g) (eventually_differentiableAt_mul hf hg) = mk f hf * mk g hg :=
  rfl

theorem mk_pow (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (n : ℕ) :
    mk (fun z => f z ^ n) (eventually_differentiableAt_pow hf n) = mk f hf ^ n := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_mk, coe_mk, ← Germ.coe_pow]
  rfl

theorem mk_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (f i) z) :
    mk (fun z => ∑ i ∈ s, f i z) (eventually_differentiableAt_sum s hf) =
      ∑ i ∈ s, mk (f i) (hf i) := by
  apply Subtype.ext
  rw [coe_mk, AddSubmonoidClass.coe_finsetSum]
  simp only [coe_mk]
  have h := map_sum (Germ.coeRingHom (𝓝 (0 : E)) : (E → ℂ) →+* Germ (𝓝 (0 : E)) ℂ) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.sum_fn]

/-- Constant germs, as a ring homomorphism `ℂ →+* 𝒪_{E,0}`. -/
def constHom : ℂ →+* HolGerm E where
  toFun c := mk (fun _ => c) (eventually_differentiableAt_const c)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem constHom_apply (c : ℂ) :
    constHom c = mk (fun _ : E => c) (eventually_differentiableAt_const c) :=
  rfl

theorem mk_const (c : ℂ) :
    mk (fun _ : E => c) (eventually_differentiableAt_const c) = constHom c :=
  rfl

/-- Evaluation of a holomorphic germ at `0`. -/
def eval : HolGerm E →+* ℂ :=
  Germ.valueRingHom.comp (holGermSubring E).subtype

@[simp]
theorem eval_mk (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    eval (mk f hf) = f 0 :=
  rfl

@[simp]
theorem eval_constHom (c : ℂ) : eval (constHom c : HolGerm E) = c :=
  rfl

instance : Nontrivial (HolGerm E) :=
  (eval : HolGerm E →+* ℂ).domain_nontrivial

/-- Holomorphic germs have no nonzero nilpotents.  This only uses the
pointwise fact that a complex number whose power vanishes is zero; it does
not use an identity theorem or the stronger domain property for holomorphic
germs. -/
theorem isReduced : IsReduced (HolGerm E) := by
  constructor
  intro g hg
  obtain ⟨n, hn⟩ := hg
  induction g using induction_on with
  | h f hf =>
    rw [← mk_zero]
    apply mk_eq_mk_iff.mpr
    have hn' : mk (fun z : E => f z ^ n) (eventually_differentiableAt_pow hf n) =
        mk (fun _ : E => 0) eventually_differentiableAt_zero := by
      calc
        mk (fun z : E => f z ^ n) (eventually_differentiableAt_pow hf n) =
            mk f hf ^ n := mk_pow f hf n
        _ = 0 := hn
        _ = mk (fun _ : E => 0) eventually_differentiableAt_zero := mk_zero.symm
    have hfn : ∀ᶠ z in 𝓝 (0 : E), f z ^ n = 0 := mk_eq_mk_iff.mp hn'
    filter_upwards [hfn] with z hz
    exact eq_zero_of_pow_eq_zero hz

/-- The preceding pointwise theorem supplies the standard reduced-ring
instance for holomorphic germs. -/
instance : IsReduced (HolGerm E) := isReduced

theorem isUnit_iff_eval_ne_zero (g : HolGerm E) : IsUnit g ↔ eval g ≠ 0 := by
  refine ⟨fun h => (h.map eval).ne_zero, fun h => ?_⟩
  induction g using induction_on with
  | h f hf =>
    rw [eval_mk] at h
    refine IsUnit.of_mul_eq_one (mk _ (eventually_differentiableAt_inv hf h)) ?_
    rw [← mk_mul, ← mk_one, mk_eq_mk_iff]
    have hne : ∀ᶠ z in 𝓝 (0 : E), f z ≠ 0 :=
      (continuousAt_zero_of_eventually_differentiableAt hf).eventually_ne h
    exact hne.mono fun z hz => mul_inv_cancel₀ hz

instance : IsLocalRing (HolGerm E) :=
  IsLocalRing.of_nonunits_add fun a b ha hb => by
    simp only [mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not, map_add] at ha hb ⊢
    rw [ha, hb, add_zero]

theorem mem_maximalIdeal_iff (g : HolGerm E) :
    g ∈ IsLocalRing.maximalIdeal (HolGerm E) ↔ eval g = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_eval_ne_zero, not_not]

section Comap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem tendsto_clm_nhds_zero (L : E →L[ℂ] F) : Tendsto L (𝓝 0) (𝓝 0) := by
  simpa using L.continuous.tendsto (0 : E)

/-- Pull back holomorphic germs at `0` along a continuous linear map. -/
def comap (L : E →L[ℂ] F) : HolGerm F →+* HolGerm E where
  toFun g := ⟨(g : Germ (𝓝 (0 : F)) ℂ).compTendsto L (tendsto_clm_nhds_zero L), by
    obtain ⟨_, f, hf, rfl⟩ := g
    exact ⟨f ∘ L, eventually_differentiableAt_comp_clm L hf, rfl⟩⟩
  map_one' := rfl
  map_mul' g h := by
    induction g using induction_on with
    | h f hf =>
      induction h using induction_on with
      | h g hg => rfl
  map_zero' := rfl
  map_add' g h := by
    induction g using induction_on with
    | h f hf =>
      induction h using induction_on with
      | h g hg => rfl

theorem comap_mk (L : E →L[ℂ] F) (f : F → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    comap L (mk f hf) = mk (f ∘ L) (eventually_differentiableAt_comp_clm L hf) :=
  rfl

@[simp]
theorem eval_comap (L : E →L[ℂ] F) (g : HolGerm F) : eval (comap L g) = eval g := by
  induction g using induction_on with
  | h f hf => simp [comap_mk]

/-- Pull back holomorphic germs at `0` along a continuous linear equivalence. -/
def comapEquiv (L : E ≃L[ℂ] F) : HolGerm F ≃+* HolGerm E :=
  RingEquiv.ofRingHom (comap (L : E →L[ℂ] F)) (comap (L.symm : F →L[ℂ] E))
    (by
      ext g
      induction g using induction_on with
      | h f hf =>
        simp only [RingHom.comp_apply, comap_mk, RingHom.id_apply]
        exact congrArg Subtype.val (mk_eq_mk_iff.2 (Eventually.of_forall fun z => by simp)))
    (by
      ext g
      induction g using induction_on with
      | h f hf =>
        simp only [RingHom.comp_apply, comap_mk, RingHom.id_apply]
        exact congrArg Subtype.val (mk_eq_mk_iff.2 (Eventually.of_forall fun z => by simp)))

theorem comapEquiv_mk (L : E ≃L[ℂ] F) (f : F → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    comapEquiv L (mk f hf) =
      mk (f ∘ L) (eventually_differentiableAt_comp_clm (L : E →L[ℂ] F) hf) :=
  rfl

theorem comapEquiv_symm_mk (L : E ≃L[ℂ] F) (f : E → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    (comapEquiv L).symm (mk f hf) =
      mk (f ∘ L.symm) (eventually_differentiableAt_comp_clm (L.symm : F →L[ℂ] E) hf) :=
  rfl

@[simp]
theorem eval_comapEquiv (L : E ≃L[ℂ] F) (g : HolGerm F) : eval (comapEquiv L g) = eval g :=
  eval_comap (L : E →L[ℂ] F) g

end Comap

end HolGerm

end SGPT.Foundations.Analysis.Pending
