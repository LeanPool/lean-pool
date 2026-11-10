/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.TraceDiff
public import LeanPool.HyperellipticCurves.Log.Cantor.PipelineCerts

/-!
# The trace-form differential along the Cantor pipeline

The four claims of `LeanPool.HyperellipticCurves.Curve.TraceDiff` instantiated at the steps of the
generic
Cantor pipeline (`ChabautyColeman.cantorPipeline`), and assembled: the trace-form differential of
the reduced output of `D₁ + D₂ + D₃` is the **sum** of its values on the three input data
(`ChabautyColeman.traceDiff_cantorPipeline`).

Composition contributes the congruences `V ≡ vᵢ mod uᵢ` of the Cantor numerator
(`ChabautyColeman.dvd_cantorCompose_sub_left` and `_right`), reduction the sign flip
`v_tilde ≡ -v mod u_tilde` (`ChabautyColeman.dvd_cantorReduce_add`); the rest is (T1) and (T2).

Beyond the pipeline's own certificate pack the assembly needs only **Weierstrass avoidance**:
each `v`-part must be invertible modulo its `u`-part, which for a datum on the curve means
that the divisor contains no Weierstrass point.  For the three input data this is a hypothesis
(a Bézout certificate); at the two reduced data it is the bundle
`ChabautyColeman.IsPipelineAvoid`, the avoidance counterpart of the certificate pack
`ChabautyColeman.IsPipelineCerts` (the `F_τ` pipeline's counterpart lives at the fold,
`ChabautyColeman.IsFtauFoldAvoid`), and it is *not* implied by the composition certificates.
Everywhere else avoidance propagates for free: `ChabautyColeman.isCoprime_cantorCompose`
carries it through a composition, and the pipeline output's avoidance *is* the bundle's second
condition (`ChabautyColeman.isCoprime_cantorPipeline`).

For a pipeline whose **third block is `d`-constant and contains a Weierstrass point** — the
Weierstrass-centred global pipeline — the stage-3 composite has no Bézout certificate at all,
and `ChabautyColeman.traceDiff_cantorPipeline_of_dvd_dotDer` applies instead: the second
reduction step crosses the singular datum by (T2′)
(`ChabautyColeman.traceDiff_reduce_of_dvd_dotDer`), and the third block contributes nothing.
Note that `ChabautyColeman.IsPipelineAvoid` constrains only the *reduced* data, never the
composites, so the bundle remains satisfiable in this configuration.  And it *descends* along
any base change reflecting coprimality of monic polynomials
(`ChabautyColeman.isCoprime_two_mul_of_map`), so over a residue-style map it is a condition on
the reduced configuration only — see `LeanPool.HyperellipticCurves.Log.Trace.TraceChain`.

Blueprint node: `thm:omega-prime-global`, clause (c).
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Compose

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]
  {f u₁ v₁ u₂ v₂ t₁ t₂ t₃ c₁ c₂ c₃ s₁ s₂ s₃ : R[X]} (d : Derivation S R R)

/-- The composed `v`-part is congruent to each block's `v`-part modulo that block's `u`-part. -/
theorem dvd_cantorCompose_sub_left (hbez : t₁ * u₁ + t₂ * u₂ + t₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) :
    u₁ ∣ (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2 - v₁ := by
  obtain ⟨w₁, hw₁⟩ := hd₁
  have h : (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2 - v₁
      = (cantorV f u₁ v₁ u₂ v₂ t₁ t₂ t₃ %ₘ (u₁ * u₂) - cantorV f u₁ v₁ u₂ v₂ t₁ t₂ t₃)
        + (cantorV f u₁ v₁ u₂ v₂ t₁ t₂ t₃ - v₁) := by
    rw [cantorCompose_snd]
    ring
  rw [h]
  exact dvd_add ((dvd_mul_right u₁ u₂).trans (dvd_modByMonic_sub _ _))
    ⟨_, cantorV_sub_left f hbez hw₁⟩

theorem dvd_cantorCompose_sub_right (hbez : t₁ * u₁ + t₂ * u₂ + t₃ * (v₁ + v₂) = 1)
    (hd₂ : u₂ ∣ v₂ ^ 2 - f) :
    u₂ ∣ (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2 - v₂ := by
  obtain ⟨w₂, hw₂⟩ := hd₂
  have h : (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2 - v₂
      = (cantorV f u₁ v₁ u₂ v₂ t₁ t₂ t₃ %ₘ (u₁ * u₂) - cantorV f u₁ v₁ u₂ v₂ t₁ t₂ t₃)
        + (cantorV f u₁ v₁ u₂ v₂ t₁ t₂ t₃ - v₂) := by
    rw [cantorCompose_snd]
    ring
  rw [h]
  exact dvd_add ((dvd_mul_left u₂ u₁).trans (dvd_modByMonic_sub _ _))
    ⟨_, cantorV_sub_right f hbez hw₂⟩

/-- Weierstrass avoidance is inherited by a composed datum: the composed `v`-part is congruent
to each block's, so it is invertible modulo each block's `u`-part, hence modulo the product. -/
theorem isCoprime_cantorCompose (hbez : t₁ * u₁ + t₂ * u₂ + t₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f) (h₁ : IsCoprime u₁ (2 * v₁))
    (h₂ : IsCoprime u₂ (2 * v₂)) :
    IsCoprime (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).1
      (2 * (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2) := by
  obtain ⟨a₁, b₁, hb₁⟩ := h₁
  obtain ⟨a₂, b₂, hb₂⟩ := h₂
  obtain ⟨e₁, he₁⟩ := exists_bezout_of_dvd_sub hb₁
    (dvd_sub_comm.mpr (dvd_cantorCompose_sub_left hbez hd₁))
  obtain ⟨e₂, he₂⟩ := exists_bezout_of_dvd_sub hb₂
    (dvd_sub_comm.mpr (dvd_cantorCompose_sub_right hbez hd₂))
  exact IsCoprime.mul_left ⟨e₁, b₁, he₁⟩ ⟨e₂, b₂, he₂⟩

variable [Nontrivial R]

/-- **(T1) at a Cantor composition step**: the trace-form differential of the composed datum
is the sum of those of the two blocks. -/
theorem traceDiff_cantorCompose (hu₁ : u₁.Monic) (hu₂ : u₂.Monic)
    (hbez : t₁ * u₁ + t₂ * u₂ + t₃ * (v₁ + v₂) = 1)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f)
    (hs₁ : c₁ * u₁ + s₁ * (2 * v₁) = 1) (hs₂ : c₂ * u₂ + s₂ * (2 * v₂) = 1)
    (hs₃ : c₃ * (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).1
      + s₃ * (2 * (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2) = 1) (k : ℕ) :
    traceDiff d (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).1 s₃ k
      = traceDiff d u₁ s₁ k + traceDiff d u₂ s₂ k :=
  traceDiff_mul d hu₁ hu₂ hs₁ hs₂ hs₃ (dvd_cantorCompose_sub_left hbez hd₁)
    (dvd_cantorCompose_sub_right hbez hd₂) k

end Compose

section ComposeUnique

variable {R : Type*} [CommRing R] [Nontrivial R] {f u₁ v₁ u₂ v₂ s₁ s₂ s₃ t₁ t₂ t₃ : R[X]}

/-- **The composed datum does not depend on the composition certificate**, provided the two
blocks avoid the Weierstrass points: both composed `v`-parts are square roots of `f` modulo
`u₁u₂` of degree `< deg u₁u₂` whose residues at each block agree, and avoidance makes such a
square root unique (`ChabautyColeman.eq_of_dvd_sq_sub_of_bezout`). -/
theorem cantorCompose_eq_of_bezout (hu₁ : u₁.Monic) (hu₂ : u₂.Monic) (hd₁ : u₁ ∣ v₁ ^ 2 - f)
    (hd₂ : u₂ ∣ v₂ ^ 2 - f) (h₁ : IsCoprime u₁ (2 * v₁)) (h₂ : IsCoprime u₂ (2 * v₂))
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hbez' : t₁ * u₁ + t₂ * u₂ + t₃ * (v₁ + v₂) = 1) :
    cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃ = cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃ := by
  set W := (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2
  set V := (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2
  -- the sum of the two composed `v`-parts is coprime to each block, hence to the product
  have hsum (u v : R[X]) (h : IsCoprime u (2 * v)) (hWv : u ∣ W - v) (hVv : u ∣ V - v) :
      IsCoprime u (W + V) := by
    obtain ⟨t, ht⟩ : u ∣ 2 * v - (W + V) := by
      have h' : 2 * v - (W + V) = -((W - v) + (V - v)) := by ring
      rw [h']
      exact dvd_neg.mpr (dvd_add hWv hVv)
    have h' := h.add_mul_left_right (-t)
    rwa [show 2 * v + u * -t = W + V by linear_combination ht] at h'
  have hc₁ : IsCoprime u₁ (W + V) := hsum u₁ v₁ h₁
    (dvd_cantorCompose_sub_left hbez hd₁) (dvd_cantorCompose_sub_left hbez' hd₁)
  have hc₂ : IsCoprime u₂ (W + V) := hsum u₂ v₂ h₂
    (dvd_cantorCompose_sub_right hbez hd₂) (dvd_cantorCompose_sub_right hbez' hd₂)
  obtain ⟨p, q, hpq⟩ := hc₁.mul_left hc₂
  refine Prod.ext rfl (eq_of_dvd_sq_sub_of_bezout (f := f) (hu₁.mul hu₂)
    (cantorCompose_dvd f hbez hd₁ hd₂) (cantorCompose_dvd f hbez' hd₁ hd₂)
    (cantorCompose_degree_lt f hu₁ hu₂) (cantorCompose_degree_lt f hu₁ hu₂) hpq)

/-- **The composed datum does not depend on the composition certificate, CRT form**: in
place of Weierstrass avoidance of the two blocks, plain coprimality of the two `u`-parts
suffices — the composed `v`-part is determined modulo each block, hence modulo the product.
This is the form that serves a constant block *containing* a Weierstrass point, where no
certificate inverting `2v₃` exists. -/
theorem cantorCompose_eq_of_isCoprime (hu₁ : u₁.Monic) (hu₂ : u₂.Monic)
    (hd₁ : u₁ ∣ v₁ ^ 2 - f) (hd₂ : u₂ ∣ v₂ ^ 2 - f) (hcop : IsCoprime u₁ u₂)
    (hbez : s₁ * u₁ + s₂ * u₂ + s₃ * (v₁ + v₂) = 1)
    (hbez' : t₁ * u₁ + t₂ * u₂ + t₃ * (v₁ + v₂) = 1) :
    cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃ = cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃ := by
  set W := (cantorCompose f u₁ v₁ u₂ v₂ s₁ s₂ s₃).2
  set V := (cantorCompose f u₁ v₁ u₂ v₂ t₁ t₂ t₃).2
  have h₁ : u₁ ∣ W - V := by
    simpa using dvd_sub (dvd_cantorCompose_sub_left hbez hd₁)
      (dvd_cantorCompose_sub_left hbez' hd₁)
  have h₂ : u₂ ∣ W - V := by
    simpa using dvd_sub (dvd_cantorCompose_sub_right hbez hd₂)
      (dvd_cantorCompose_sub_right hbez' hd₂)
  have h0 : W - V = 0 := by
    have hdeg : (W - V).degree < (u₁ * u₂).degree :=
      (degree_sub_le W V).trans_lt (max_lt (cantorCompose_degree_lt f hu₁ hu₂)
        (cantorCompose_degree_lt f hu₁ hu₂))
    rw [← (modByMonic_eq_self_iff (hu₁.mul hu₂)).mpr hdeg]
    exact (modByMonic_eq_zero_iff_dvd (hu₁.mul hu₂)).mpr (hcop.mul_dvd h₁ h₂)
  exact Prod.ext_iff.mpr ⟨rfl, sub_eq_zero.mp h0⟩

end ComposeUnique

section Reduce

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] (d : Derivation S R R)
  {f u v s s' cu cu' : R[X]} {c : R} {g k : ℕ}

/-- Reduction flips the sign of the `v`-part: the reduced `v` is `-v` modulo the reduced `u`. -/
theorem dvd_cantorReduce_add : (cantorReduce f u v c).1 ∣ (cantorReduce f u v c).2 + v := by
  have h := dvd_modByMonic_sub (-v) (cantorReduce f u v c).1
  rwa [sub_neg_eq_add] at h

/-- **(T2) at a Cantor reduction step.** -/
theorem traceDiff_cantorReduce [Nontrivial R] [NoZeroDivisors R] (hu : u.Monic)
    (hdvd : u ∣ v ^ 2 - f) (hc : c * (cantorCofactor f u v).leadingCoeff = 1)
    (hfc : ∀ i, d (f.coeff i) = 0)
    (hf : f.natDegree = 2 * g + 1) (hk : k < g) (hs : cu * u + s * (2 * v) = 1)
    (hs' : cu' * (cantorReduce f u v c).1 + s' * (2 * (cantorReduce f u v c).2) = 1) :
    traceDiff d (cantorReduce f u v c).1 s' k = traceDiff d u s k := by
  refine traceDiff_reduce d hu (cantorReduce_monic f hc) hc ?_ hfc hf hk hs hs'
    dvd_cantorReduce_add
  simp only [cantorReduce, cantorCofactor_spec f hu hdvd]
  ring

/-- **Weierstrass avoidance is a condition against the curve, not against the datum.** For a
Mumford datum `(u, v)` the `v`-part is invertible modulo the `u`-part exactly when the
`u`-part is coprime to `f` — that is, when the divisor misses the Weierstrass points: a
common root of `u` and `v` is a root of `f` because `u ∣ v² - f`, and conversely a common
root of `u` and `f` is a root of `v²`, hence of `v`. -/
theorem isCoprime_two_mul_iff (h2 : IsUnit (2 : R[X])) (hdvd : u ∣ v ^ 2 - f) :
    IsCoprime u (2 * v) ↔ IsCoprime u f := by
  obtain ⟨w, hw⟩ := hdvd
  rw [isCoprime_mul_unit_left_right h2]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = v ^ 2 + u * -w by linear_combination -hw]
    exact (h.pow_right (n := 2)).add_mul_left_right _
  · have hv2 : IsCoprime u (v ^ 2) := by
      rw [show v ^ 2 = f + u * w by linear_combination hw]
      exact h.add_mul_left_right w
    exact (IsCoprime.pow_right_iff two_pos).mp hv2

/-- **(T2′) at a Cantor reduction step** of a datum `(u·B, v)` with a `d`-constant monic
factor `B ∣ v_dot`: a Bézout certificate is needed only for the moving part `u`. -/
theorem traceDiff_cantorReduce_of_dvd_dotDer [Nontrivial R] [NoZeroDivisors R] {B : R[X]}
    (hu : u.Monic) (hB : B.Monic) (hdvd : u * B ∣ v ^ 2 - f)
    (hc : c * (cantorCofactor f (u * B) v).leadingCoeff = 1)
    (hfc : ∀ i, d (f.coeff i) = 0) (hf : f.natDegree = 2 * g + 1) (hk : k < g)
    (hBd : ∀ i, d (B.coeff i) = 0) (hvB : B ∣ d.dotDer v)
    (hs : cu * u + s * (2 * v) = 1)
    (hs' : cu' * (cantorReduce f (u * B) v c).1 + s' * (2 * (cantorReduce f (u * B) v c).2) = 1) :
    traceDiff d (cantorReduce f (u * B) v c).1 s' k = traceDiff d u s k := by
  refine traceDiff_reduce_of_dvd_dotDer d hu hB (cantorReduce_monic f hc) hc ?_ hfc hf hk
    hBd hvB hs hs' dvd_cantorReduce_add
  simp only [cantorReduce, cantorCofactor_spec f (hu.mul hB) hdvd]
  ring

end Reduce

section AvoidDescent

variable {R A : Type*} [CommRing R] [CommRing A] {φ : R →+* A} {u v : R[X]}

/-- **Weierstrass avoidance is preserved by base change.** -/
theorem isCoprime_two_mul_map (h : IsCoprime u (2 * v)) (φ : R →+* A) :
    IsCoprime (u.map φ) (2 * v.map φ) := by
  simpa only [coe_mapRingHom, Polynomial.map_mul, Polynomial.map_ofNat] using
    h.map (Polynomial.mapRingHom φ)

/-- `φ` **reflects coprimality**: coprimality of a *monic* polynomial with another one
descends along the base change `φ`. This holds for a residue-style map by Nakayama
(`ChabautyColeman.reflectsCoprime_of_ker_le_jacobson`) and for any base change of fields
(`ChabautyColeman.reflectsCoprime_of_field`), which is what makes Weierstrass avoidance a
condition on the *reduced* configuration. -/
def ReflectsCoprime (φ : R →+* A) : Prop :=
  ∀ p q : R[X], p.Monic → IsCoprime (p.map φ) (q.map φ) → IsCoprime p q

theorem reflectsCoprime_of_ker_le_jacobson (hsurj : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ Ideal.jacobson ⊥) : ReflectsCoprime φ :=
  fun _ _ hp hpq ↦ isCoprime_of_map hsurj hker hp hpq

theorem reflectsCoprime_of_field {K L : Type*} [Field K] [Field L] (φ : K →+* L) :
    ReflectsCoprime φ := fun _ _ _ hpq ↦ (Polynomial.isCoprime_map φ).mp hpq

/-- **Weierstrass avoidance descends along a base change that reflects coprimality**: for a
monic `u`, invertibility of `v` modulo `u` is a condition on the image configuration. -/
theorem isCoprime_two_mul_of_map (hrefl : ReflectsCoprime φ) (hu : u.Monic)
    (h : IsCoprime (u.map φ) (2 * v.map φ)) : IsCoprime u (2 * v) :=
  hrefl _ _ hu (by simpa only [Polynomial.map_mul, Polynomial.map_ofNat] using h)

end AvoidDescent

section AvoidBundle

variable {R : Type*} [CommRing R] (f : R[X]) (D : PipelineData R) (d : CantorCertData R)

/-- **Weierstrass avoidance along the generic Cantor pipeline**: the two reduced data of the
pack `d` avoid the Weierstrass points, i.e. each has its `v`-part invertible modulo its
`u`-part.  Together with the certificate pack
(`ChabautyColeman.IsPipelineCerts`) this is everything the trace-form additivity
`ChabautyColeman.traceDiff_cantorPipeline` needs. -/
structure IsPipelineAvoid : Prop where
  /-- Avoidance at the reduced datum of `D₁ + D₂`. -/
  hcop₁ : IsCoprime (cantorStage₂ f D d).1 (2 * (cantorStage₂ f D d).2)
  /-- Avoidance at the reduced datum of `(D₁ + D₂) + D₃`, the pipeline output. -/
  hcop₂ : IsCoprime (cantorPipeline f D d).1 (2 * (cantorPipeline f D d).2)

end AvoidBundle

section Pipeline

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R] [Nontrivial R]
  [NoZeroDivisors R] (d : Derivation S R R)
  {f c₁ c₂ c₃ cP s₁ s₂ s₃ sP : R[X]} {D : PipelineData R}
  {dt : CantorCertData R} {n g k : ℕ}

/-- **The trace-form differential is additive along the whole Cantor pipeline**: the value on
the reduced output of `D₁ + D₂ + D₃` is the sum of the values on the three blocks.  Beyond the
pipeline's own certificate pack the only hypotheses are Weierstrass avoidance: each block's
`v`-part invertible modulo its `u`-part, and the same at every intermediate reduced datum. -/
theorem traceDiff_cantorPipeline (hu₁ : D.u₁.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hu₂ : D.u₂.Monic)
    (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hu₃ : D.u₃.Monic) (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f)
    (hcerts : IsPipelineCerts f D dt n)
    (hav : IsPipelineAvoid f D dt)
    (hfc : ∀ i, d (f.coeff i) = 0) (hf : f.natDegree = 2 * g + 1) (hk : k < g)
    (hs₁ : c₁ * D.u₁ + s₁ * (2 * D.v₁) = 1) (hs₂ : c₂ * D.u₂ + s₂ * (2 * D.v₂) = 1)
    (hs₃ : c₃ * D.u₃ + s₃ * (2 * D.v₃) = 1)
    (hsP : cP * (cantorPipeline f D dt).1 + sP * (2 * (cantorPipeline f D dt).2) = 1) :
    traceDiff d (cantorPipeline f D dt).1 sP k
      = traceDiff d D.u₁ s₁ k + traceDiff d D.u₂ s₂ k + traceDiff d D.u₃ s₃ k := by
  set S₁ := cantorStage₁ f D dt
  set S₂ := cantorStage₂ f D dt
  set S₃ := cantorStage₃ f D dt
  set P := cantorPipeline f D dt
  have hS₁m : S₁.1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₁d : S₁.1 ∣ S₁.2 ^ 2 - f := cantorCompose_dvd f hcerts.hbez₁ hd₁ hd₂
  obtain ⟨cS₁, sS₁, hsS₁⟩ : IsCoprime S₁.1 (2 * S₁.2) :=
    isCoprime_cantorCompose hcerts.hbez₁ hd₁ hd₂ ⟨c₁, s₁, hs₁⟩ ⟨c₂, s₂, hs₂⟩
  have hS₂m : S₂.1.Monic := cantorReduce_monic f hcerts.hc₁
  have hS₂d : S₂.1 ∣ S₂.2 ^ 2 - f := cantorReduce_dvd f hS₁m hS₁d hcerts.hc₁
  obtain ⟨cS₂, sS₂, hsS₂⟩ : IsCoprime S₂.1 (2 * S₂.2) := hav.hcop₁
  have hS₃m : S₃.1.Monic := cantorCompose_monic f hS₂m hu₃
  have hS₃d : S₃.1 ∣ S₃.2 ^ 2 - f := cantorCompose_dvd f hcerts.hbez₂ hS₂d hd₃
  obtain ⟨cS₃, sS₃, hsS₃⟩ : IsCoprime S₃.1 (2 * S₃.2) :=
    isCoprime_cantorCompose hcerts.hbez₂ hS₂d hd₃ ⟨cS₂, sS₂, hsS₂⟩ ⟨c₃, s₃, hs₃⟩
  have e₄ : traceDiff d P.1 sP k = traceDiff d S₃.1 sS₃ k :=
    traceDiff_cantorReduce d hS₃m hS₃d hcerts.hc₂ hfc hf hk hsS₃ hsP
  have e₃ : traceDiff d S₃.1 sS₃ k = traceDiff d S₂.1 sS₂ k + traceDiff d D.u₃ s₃ k :=
    traceDiff_cantorCompose d hS₂m hu₃ hcerts.hbez₂ hS₂d hd₃ hsS₂ hs₃ hsS₃ k
  have e₂ : traceDiff d S₂.1 sS₂ k = traceDiff d S₁.1 sS₁ k :=
    traceDiff_cantorReduce d hS₁m hS₁d hcerts.hc₁ hfc hf hk hsS₁ hsS₂
  have e₁ : traceDiff d S₁.1 sS₁ k = traceDiff d D.u₁ s₁ k + traceDiff d D.u₂ s₂ k :=
    traceDiff_cantorCompose d hu₁ hu₂ hcerts.hbez₁ hd₁ hd₂ hs₁ hs₂ hsS₁ k
  rw [e₄, e₃, e₂, e₁]

/-- **The trace-form differential along the Cantor pipeline with a `d`-constant third
block.** When the third block `(D.u₃, D.v₃)` has `d`-constant coefficients — the situation of a
centre pair block containing a Weierstrass point — no Bézout certificate for it (nor for the
stage-3 composite) is needed: the second reduction step crosses the singular datum by
`ChabautyColeman.traceDiff_reduce_of_dvd_dotDer`. The third block contributes nothing to the
differential, so the output value is the sum over the first two blocks alone. -/
theorem traceDiff_cantorPipeline_of_dvd_dotDer (hu₁ : D.u₁.Monic)
    (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hu₂ : D.u₂.Monic) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hu₃ : D.u₃.Monic)
    (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f)
    (hcerts : IsPipelineCerts f D dt n)
    (hav : IsPipelineAvoid f D dt)
    (hfc : ∀ i, d (f.coeff i) = 0) (hf : f.natDegree = 2 * g + 1) (hk : k < g)
    (hBd : ∀ i, d (D.u₃.coeff i) = 0) (hv₃d : ∀ i, d (D.v₃.coeff i) = 0)
    (hs₁ : c₁ * D.u₁ + s₁ * (2 * D.v₁) = 1) (hs₂ : c₂ * D.u₂ + s₂ * (2 * D.v₂) = 1)
    (hsP : cP * (cantorPipeline f D dt).1 + sP * (2 * (cantorPipeline f D dt).2) = 1) :
    traceDiff d (cantorPipeline f D dt).1 sP k
      = traceDiff d D.u₁ s₁ k + traceDiff d D.u₂ s₂ k := by
  set S₁ := cantorStage₁ f D dt
  set S₂ := cantorStage₂ f D dt
  set S₃ := cantorStage₃ f D dt
  have hS₁m : S₁.1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₁d : S₁.1 ∣ S₁.2 ^ 2 - f := cantorCompose_dvd f hcerts.hbez₁ hd₁ hd₂
  obtain ⟨cS₁, sS₁, hsS₁⟩ : IsCoprime S₁.1 (2 * S₁.2) :=
    isCoprime_cantorCompose hcerts.hbez₁ hd₁ hd₂ ⟨c₁, s₁, hs₁⟩ ⟨c₂, s₂, hs₂⟩
  have hS₂m : S₂.1.Monic := cantorReduce_monic f hcerts.hc₁
  have hS₂d : S₂.1 ∣ S₂.2 ^ 2 - f := cantorReduce_dvd f hS₁m hS₁d hcerts.hc₁
  obtain ⟨cS₂, sS₂, hsS₂⟩ : IsCoprime S₂.1 (2 * S₂.2) := hav.hcop₁
  have hS₃d : S₃.1 ∣ S₃.2 ^ 2 - f := cantorCompose_dvd f hcerts.hbez₂ hS₂d hd₃
  have hS₃fst : S₃.1 = S₂.1 * D.u₃ := rfl
  -- the composed `v`-part has `D.u₃`-divisible derivative and a certificate at the moving part
  have hvB : D.u₃ ∣ d.dotDer S₃.2 :=
    d.dvd_dotDer_of_dvd_sub hBd hv₃d (dvd_cantorCompose_sub_right hcerts.hbez₂ hd₃)
  obtain ⟨cS₃, hsS₃⟩ : ∃ c', c' * S₂.1 + sS₂ * (2 * S₃.2) = 1 :=
    exists_bezout_of_dvd_sub hsS₂ (dvd_sub_comm.mp (dvd_cantorCompose_sub_left hcerts.hbez₂ hS₂d))
  -- the second reduction step, crossed by (T2′)
  have hc₂ := hcerts.hc₂
  have hsP' := hsP
  rw [cantorPipeline_def] at hsP'
  have e₄ : traceDiff d (cantorPipeline f D dt).1 sP k = traceDiff d S₂.1 sS₂ k := by
    rw [cantorPipeline_def]
    rw [hS₃fst] at hc₂ hsP' ⊢
    exact traceDiff_cantorReduce_of_dvd_dotDer d hS₂m hu₃ (hS₃fst ▸ hS₃d) hc₂ hfc hf hk hBd hvB
      hsS₃ hsP'
  have e₂ : traceDiff d S₂.1 sS₂ k = traceDiff d S₁.1 sS₁ k :=
    traceDiff_cantorReduce d hS₁m hS₁d hcerts.hc₁ hfc hf hk hsS₁ hsS₂
  have e₁ : traceDiff d S₁.1 sS₁ k = traceDiff d D.u₁ s₁ k + traceDiff d D.u₂ s₂ k :=
    traceDiff_cantorCompose d hu₁ hu₂ hcerts.hbez₁ hd₁ hd₂ hs₁ hs₂ hsS₁ k
  rw [e₄, e₂, e₁]

end Pipeline

section PipelineCoprime

variable {R : Type*} [CommRing R] {f : R[X]} {D : PipelineData R} {dt : CantorCertData R}

/-- **The pipeline output avoids the Weierstrass points** as soon as the avoidance bundle
holds — it is the bundle's second condition; no coprimality of the input blocks (in particular
none of a singular constant block) is needed. -/
theorem isCoprime_cantorPipeline (hav : IsPipelineAvoid f D dt) :
    IsCoprime (cantorPipeline f D dt).1 (2 * (cantorPipeline f D dt).2) :=
  hav.hcop₂

end PipelineCoprime

section PipelineDescent

variable {R A : Type*} [CommRing R] [CommRing A] {φ : R →+* A} {f : R[X]}
  {D : PipelineData R} {dt : CantorCertData R} {n : ℕ}

/-- **Avoidance at the first reduced datum is a condition on the image configuration.** -/
theorem isCoprime_cantorStage₂_of_map (hrefl : ReflectsCoprime φ) (hu₁ : D.u₁.Monic)
    (hu₂ : D.u₂.Monic)
    (hc₁ : dt.c₁ * (cantorCofactor f (cantorStage₁ f D dt).1 (cantorStage₁ f D dt).2).leadingCoeff
      = 1)
    (h : IsCoprime (cantorStage₂ (f.map φ) (D.map φ) (dt.map φ)).1
      (2 * (cantorStage₂ (f.map φ) (D.map φ) (dt.map φ)).2)) :
    IsCoprime (cantorStage₂ f D dt).1 (2 * (cantorStage₂ f D dt).2) := by
  obtain ⟨e₁, e₂⟩ := Prod.ext_iff.mp (cantorStage₂_map φ hu₁ hu₂ hc₁)
  dsimp only at e₁ e₂
  exact isCoprime_two_mul_of_map hrefl (cantorReduce_monic f hc₁) (by rwa [e₁, e₂])

/-- **Avoidance at the pipeline output is a condition on the image configuration.** -/
theorem isCoprime_cantorPipeline_of_map (hrefl : ReflectsCoprime φ) (hu₁ : D.u₁.Monic)
    (hu₂ : D.u₂.Monic) (hu₃ : D.u₃.Monic) (hcerts : IsPipelineCerts f D dt n)
    (h : IsCoprime (cantorPipeline (f.map φ) (D.map φ) (dt.map φ)).1
      (2 * (cantorPipeline (f.map φ) (D.map φ) (dt.map φ)).2)) :
    IsCoprime (cantorPipeline f D dt).1 (2 * (cantorPipeline f D dt).2) := by
  obtain ⟨e₁, e₂⟩ := Prod.ext_iff.mp (map_cantorPipeline_generic φ hu₁ hu₂ hu₃ hcerts)
  dsimp only at e₁ e₂
  exact isCoprime_two_mul_of_map hrefl (cantorReduce_monic f hcerts.hc₂) (by rwa [e₁, e₂])

/-- **Weierstrass avoidance of a pipeline is preserved by base change.** -/
theorem IsPipelineAvoid.map (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic) (hu₃ : D.u₃.Monic)
    (hcerts : IsPipelineCerts f D dt n) (hav : IsPipelineAvoid f D dt) :
    IsPipelineAvoid (f.map φ) (D.map φ) (dt.map φ) := by
  obtain ⟨h2a, h2b⟩ := Prod.ext_iff.mp (cantorStage₂_map φ hu₁ hu₂ hcerts.hc₁)
  obtain ⟨h4a, h4b⟩ := Prod.ext_iff.mp (map_cantorPipeline_generic φ hu₁ hu₂ hu₃ hcerts)
  dsimp only at h2a h2b h4a h4b
  refine ⟨?_, ?_⟩
  · have h := isCoprime_two_mul_map hav.hcop₁ φ
    rwa [h2a, h2b] at h
  · have h := isCoprime_two_mul_map hav.hcop₂ φ
    rwa [h4a, h4b] at h

end PipelineDescent

end ChabautyColeman

end
