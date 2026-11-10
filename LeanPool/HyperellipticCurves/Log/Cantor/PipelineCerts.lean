/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Ftau.Ftau

/-!
# The generic two-composition Cantor pipeline and certificate lifting

The Cantor pipeline computing `D₁ + D₂ + D₃` for three Mumford data — compose, reduce,
compose, reduce, steered by a certificate pack `ChabautyColeman.CantorCertData` — in its
natural generality: over any commutative ring, with arbitrary data. The disk expansion
of `def:phiD` (`D₁` the moving pair datum over `O⟦z⟧`, `D₂ = τ`, `D₃` a constant pair datum) is an
instance.

* `ChabautyColeman.PipelineData`: the three Mumford data the pipeline adds, as one object;
* `ChabautyColeman.cantorStage₁` … `ChabautyColeman.cantorPipeline`: the four stages;
* `ChabautyColeman.IsPipelineCerts`: validity of a certificate pack (Bézout certificates,
  reduction certificates, final degree);
* `ChabautyColeman.IsPipelineCenterCerts`: validity plus the "no degree drop" genericity
  (the cofactor attains its generic degree) at both reduction steps;
* `ChabautyColeman.exists_isPipelineCerts_of_center`: **certificate-pack lifting** — a
  valid and generic pack over the image of a residue-style map `ψ` (surjective,
  unit-detecting, kernel inside the Jacobson radical) lifts to a valid pack upstairs, by
  prescribed-residue Bézout lifting (Nakayama) and the reduction-certificate degree squeeze.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Configuration

/-- A **three-block Mumford configuration**: the three Mumford data `D₁ = (u₁, v₁)`,
`D₂ = (u₂, v₂)`, `D₃ = (u₃, v₃)` that the generic Cantor pipeline adds. The curve
polynomial `f` is deliberately not part of it: `f` is fixed by the ambient curve, while the
blocks vary — and are transported — independently of it. -/
structure PipelineData (R : Type*) [Semiring R] where
  /-- The `u`-part of the first datum. -/
  u₁ : R[X]
  /-- The `v`-part of the first datum. -/
  v₁ : R[X]
  /-- The `u`-part of the second datum. -/
  u₂ : R[X]
  /-- The `v`-part of the second datum. -/
  v₂ : R[X]
  /-- The `u`-part of the third datum. -/
  u₃ : R[X]
  /-- The `v`-part of the third datum. -/
  v₃ : R[X]

namespace PipelineData

variable {R S : Type*} [Semiring R] [Semiring S]

/-- The **two-block configuration** `D₁ + D₂`, as used by the chart at infinity: a
three-block configuration whose third block carries the junk value `(1, 0)`. Stages 1 and 2
of the pipeline — the only ones a two-block addition runs — do not read it. -/
@[simps] noncomputable def ofPair (u₁ v₁ u₂ v₂ : R[X]) : PipelineData R := ⟨u₁, v₁, u₂, v₂, 1, 0⟩

variable (φ : R →+* S)

/-- Base change of a three-block configuration along a ring homomorphism. -/
noncomputable def map (D : PipelineData R) : PipelineData S :=
  ⟨D.u₁.map φ, D.v₁.map φ, D.u₂.map φ, D.v₂.map φ, D.u₃.map φ, D.v₃.map φ⟩

@[simp] theorem map_u₁ (D : PipelineData R) : (D.map φ).u₁ = D.u₁.map φ := rfl
@[simp] theorem map_v₁ (D : PipelineData R) : (D.map φ).v₁ = D.v₁.map φ := rfl
@[simp] theorem map_u₂ (D : PipelineData R) : (D.map φ).u₂ = D.u₂.map φ := rfl
@[simp] theorem map_v₂ (D : PipelineData R) : (D.map φ).v₂ = D.v₂.map φ := rfl
@[simp] theorem map_u₃ (D : PipelineData R) : (D.map φ).u₃ = D.u₃.map φ := rfl
@[simp] theorem map_v₃ (D : PipelineData R) : (D.map φ).v₃ = D.v₃.map φ := rfl

variable {φ}

/-- **An identification of two configurations is six blockwise identifications.** Stated as
a conjunction because that is how it is consumed: transporting a pipeline needs all six at
once, and one hypothesis `D.map φ = D'.map ψ` replaces the six at every call site. -/
theorem blocks_of_map_eq {T : Type*} [Semiring T] {ψ : T →+* S} {D : PipelineData R}
    {D' : PipelineData T} (h : D.map φ = D'.map ψ) :
    D.u₁.map φ = D'.u₁.map ψ ∧ D.v₁.map φ = D'.v₁.map ψ ∧ D.u₂.map φ = D'.u₂.map ψ
      ∧ D.v₂.map φ = D'.v₂.map ψ ∧ D.u₃.map φ = D'.u₃.map ψ ∧ D.v₃.map φ = D'.v₃.map ψ :=
  ⟨congrArg u₁ h, congrArg v₁ h, congrArg u₂ h, congrArg v₂ h, congrArg u₃ h, congrArg v₃ h⟩

/-- Two configurations agree as soon as their six blocks do. -/
theorem map_eq_of_blocks {T : Type*} [Semiring T] {ψ : T →+* S} {D : PipelineData R}
    {D' : PipelineData T} (hu₁ : D.u₁.map φ = D'.u₁.map ψ) (hv₁ : D.v₁.map φ = D'.v₁.map ψ)
    (hu₂ : D.u₂.map φ = D'.u₂.map ψ) (hv₂ : D.v₂.map φ = D'.v₂.map ψ)
    (hu₃ : D.u₃.map φ = D'.u₃.map ψ) (hv₃ : D.v₃.map φ = D'.v₃.map ψ) :
    D.map φ = D'.map ψ := by
  simp only [map, hu₁, hv₁, hu₂, hv₂, hu₃, hv₃]

end PipelineData

end Configuration

section GenericPipeline

variable {R : Type*} [CommRing R] (f : R[X]) (D : PipelineData R) (d : CantorCertData R)

/-- Stage 1 of the generic Cantor pipeline: compose the first two Mumford data. -/
noncomputable def cantorStage₁ : R[X] × R[X] :=
  cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ d.s₁ d.s₂ d.s₃

/-- Stage 2 of the generic Cantor pipeline: reduce with the first certificate. -/
noncomputable def cantorStage₂ : R[X] × R[X] :=
  cantorReduce f (cantorStage₁ f D d).1 (cantorStage₁ f D d).2 d.c₁

/-- Stage 3 of the generic Cantor pipeline: compose with the third Mumford datum. -/
noncomputable def cantorStage₃ : R[X] × R[X] :=
  cantorCompose f (cantorStage₂ f D d).1 (cantorStage₂ f D d).2 D.u₃ D.v₃ d.t₁ d.t₂ d.t₃

/-- The full generic Cantor pipeline: `D₁ + D₂ + D₃` as a reduced Mumford datum. -/
noncomputable def cantorPipeline : R[X] × R[X] :=
  cantorReduce f (cantorStage₃ f D d).1 (cantorStage₃ f D d).2 d.c₂

theorem cantorStage₁_def :
    cantorStage₁ f D d = cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ d.s₁ d.s₂ d.s₃ := rfl

theorem cantorStage₂_def : cantorStage₂ f D d
    = cantorReduce f (cantorStage₁ f D d).1 (cantorStage₁ f D d).2 d.c₁ := rfl

theorem cantorStage₃_def : cantorStage₃ f D d
    = cantorCompose f (cantorStage₂ f D d).1 (cantorStage₂ f D d).2 D.u₃ D.v₃
      d.t₁ d.t₂ d.t₃ := rfl

theorem cantorPipeline_def : cantorPipeline f D d
    = cantorReduce f (cantorStage₃ f D d).1 (cantorStage₃ f D d).2 d.c₂ := rfl

/-- Validity of a certificate pack for the generic Cantor pipeline on the configuration
`D`: the two Bézout certificates hold, the two reduction certificates invert the leading
coefficients of their cofactors, and the final `u`-part has the expected degree `n`. -/
structure IsPipelineCerts (n : ℕ) : Prop where
  /-- The Bézout certificate of the first composition step. -/
  hbez₁ : d.s₁ * D.u₁ + d.s₂ * D.u₂ + d.s₃ * (D.v₁ + D.v₂) = 1
  /-- The inverse of the leading coefficient of the first cofactor. -/
  hc₁ : d.c₁ * (cantorCofactor f (cantorStage₁ f D d).1 (cantorStage₁ f D d).2).leadingCoeff = 1
  /-- The Bézout certificate of the second composition step. -/
  hbez₂ : d.t₁ * (cantorStage₂ f D d).1 + d.t₂ * D.u₃
    + d.t₃ * ((cantorStage₂ f D d).2 + D.v₃) = 1
  /-- The inverse of the leading coefficient of the second cofactor. -/
  hc₂ : d.c₂ * (cantorCofactor f (cantorStage₃ f D d).1 (cantorStage₃ f D d).2).leadingCoeff = 1
  /-- The output support has the prescribed degree. -/
  hdeg : (cantorPipeline f D d).1.natDegree = n

/-- A valid certificate pack for the generic Cantor pipeline that in addition attains the
generic cofactor degree bound `max (2·(deg u - 1)) (deg f) - deg u` at both reduction steps
(the "no degree drop" genericity). Over the residue field of a local-style base this is
what lets the pack lift (`ChabautyColeman.exists_isPipelineCerts_of_center`). -/
structure IsPipelineCenterCerts (n : ℕ) : Prop extends IsPipelineCerts f D d n where
  /-- The first reduction attains the generic cofactor degree. -/
  hfull₁ : (cantorCofactor f (cantorStage₁ f D d).1 (cantorStage₁ f D d).2).natDegree
    = max (2 * ((cantorStage₁ f D d).1.natDegree - 1)) f.natDegree
      - (cantorStage₁ f D d).1.natDegree
  /-- The second reduction attains the generic cofactor degree. -/
  hfull₂ : (cantorCofactor f (cantorStage₃ f D d).1 (cantorStage₃ f D d).2).natDegree
    = max (2 * ((cantorStage₃ f D d).1.natDegree - 1)) f.natDegree
      - (cantorStage₃ f D d).1.natDegree

end GenericPipeline

section PipelineInvariants

variable {R : Type*} [CommRing R] [Nontrivial R] {f : R[X]} {D : PipelineData R}
  {d : CantorCertData R} {n : ℕ}

/-- The output of the generic Cantor pipeline along a valid certificate pack is a
reduced Mumford datum: monic `u`-part dividing `v² - f`, with `deg v < deg u`. -/
theorem cantorPipeline_monic_dvd_degree_lt (hu₁ : D.u₁.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f)
    (hu₂ : D.u₂.Monic) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hu₃ : D.u₃.Monic)
    (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f) (hcerts : IsPipelineCerts f D d n) :
    (cantorPipeline f D d).1.Monic
      ∧ (cantorPipeline f D d).1 ∣ (cantorPipeline f D d).2 ^ 2 - f
      ∧ (cantorPipeline f D d).2.degree < (cantorPipeline f D d).1.degree := by
  have hS₁monic : (cantorStage₁ f D d).1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₁dvd : (cantorStage₁ f D d).1 ∣ (cantorStage₁ f D d).2 ^ 2 - f :=
    cantorCompose_dvd f hcerts.hbez₁ hd₁ hd₂
  have hS₂monic : (cantorStage₂ f D d).1.Monic := cantorReduce_monic f hcerts.hc₁
  have hS₂dvd : (cantorStage₂ f D d).1 ∣ (cantorStage₂ f D d).2 ^ 2 - f :=
    cantorReduce_dvd f hS₁monic hS₁dvd hcerts.hc₁
  have hS₃monic : (cantorStage₃ f D d).1.Monic := cantorCompose_monic f hS₂monic hu₃
  have hS₃dvd : (cantorStage₃ f D d).1 ∣ (cantorStage₃ f D d).2 ^ 2 - f :=
    cantorCompose_dvd f hcerts.hbez₂ hS₂dvd hd₃
  exact ⟨cantorReduce_monic f hcerts.hc₂, cantorReduce_dvd f hS₃monic hS₃dvd hcerts.hc₂,
    cantorReduce_degree_lt f hcerts.hc₂⟩

end PipelineInvariants

section PipelineMap

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Base change of a certificate pack along a ring homomorphism. -/
noncomputable def CantorCertData.map (d : CantorCertData R) : CantorCertData S :=
  ⟨d.s₁.map φ, d.s₂.map φ, d.s₃.map φ, φ d.c₁, d.t₁.map φ, d.t₂.map φ, d.t₃.map φ, φ d.c₂⟩

@[simp] theorem CantorCertData.map_s₁ (d : CantorCertData R) : (d.map φ).s₁ = d.s₁.map φ := rfl
@[simp] theorem CantorCertData.map_s₂ (d : CantorCertData R) : (d.map φ).s₂ = d.s₂.map φ := rfl
@[simp] theorem CantorCertData.map_s₃ (d : CantorCertData R) : (d.map φ).s₃ = d.s₃.map φ := rfl
@[simp] theorem CantorCertData.map_c₁ (d : CantorCertData R) : (d.map φ).c₁ = φ d.c₁ := rfl
@[simp] theorem CantorCertData.map_t₁ (d : CantorCertData R) : (d.map φ).t₁ = d.t₁.map φ := rfl
@[simp] theorem CantorCertData.map_t₂ (d : CantorCertData R) : (d.map φ).t₂ = d.t₂.map φ := rfl
@[simp] theorem CantorCertData.map_t₃ (d : CantorCertData R) : (d.map φ).t₃ = d.t₃.map φ := rfl
@[simp] theorem CantorCertData.map_c₂ (d : CantorCertData R) : (d.map φ).c₂ = φ d.c₂ := rfl

variable {f : R[X]} {D : PipelineData R} {d : CantorCertData R} {n : ℕ}

/-- Stage 1 commutes with base change. -/
theorem cantorStage₁_map (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic) :
    ((cantorStage₁ f D d).1.map φ, (cantorStage₁ f D d).2.map φ)
      = cantorStage₁ (f.map φ) (D.map φ) (d.map φ) :=
  map_cantorCompose φ f hu₁ hu₂ D.v₁ D.v₂ d.s₁ d.s₂ d.s₃

/-- Stage 2 commutes with base change, given a valid first reduction certificate. -/
theorem cantorStage₂_map (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic)
    (hc₁ : d.c₁ * (cantorCofactor f (cantorStage₁ f D d).1 (cantorStage₁ f D d).2).leadingCoeff
      = 1) :
    ((cantorStage₂ f D d).1.map φ, (cantorStage₂ f D d).2.map φ)
      = cantorStage₂ (f.map φ) (D.map φ) (d.map φ) := by
  obtain ⟨e₁, e₂⟩ := Prod.ext_iff.mp (cantorStage₁_map φ (f := f) (D := D) (d := d) hu₁ hu₂)
  dsimp only at e₁ e₂
  have hS₁ : (cantorStage₁ f D d).1.Monic := cantorCompose_monic f hu₁ hu₂
  rw [cantorStage₂_def, map_cantorReduce φ f hS₁ hc₁, e₁, e₂, cantorStage₂_def]
  rfl

/-- Stage 3 commutes with base change, given a valid first reduction certificate. -/
theorem cantorStage₃_map (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic)
    (hc₁ : d.c₁ * (cantorCofactor f (cantorStage₁ f D d).1 (cantorStage₁ f D d).2).leadingCoeff
      = 1) (hu₃ : D.u₃.Monic) :
    ((cantorStage₃ f D d).1.map φ, (cantorStage₃ f D d).2.map φ)
      = cantorStage₃ (f.map φ) (D.map φ) (d.map φ) := by
  obtain ⟨e₁, e₂⟩ := Prod.ext_iff.mp (cantorStage₂_map φ hu₁ hu₂ hc₁)
  dsimp only at e₁ e₂
  have hS₂ : (cantorStage₂ f D d).1.Monic := cantorReduce_monic f hc₁
  rw [cantorStage₃_def, map_cantorCompose φ f hS₂ hu₃, e₁, e₂, cantorStage₃_def]
  rfl

/-- **The generic Cantor pipeline commutes with base change** along a valid certificate
pack. -/
theorem map_cantorPipeline_generic (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic)
    (hu₃ : D.u₃.Monic) (hcerts : IsPipelineCerts f D d n) :
    ((cantorPipeline f D d).1.map φ, (cantorPipeline f D d).2.map φ)
      = cantorPipeline (f.map φ) (D.map φ) (d.map φ) := by
  obtain ⟨h3a, h3b⟩ := Prod.ext_iff.mp (cantorStage₃_map φ hu₁ hu₂ hcerts.hc₁ hu₃)
  dsimp only at h3a h3b
  have hS₃monic : (cantorStage₃ f D d).1.Monic :=
    cantorCompose_monic f (cantorReduce_monic f hcerts.hc₁) hu₃
  rw [cantorPipeline_def, map_cantorReduce φ f hS₃monic hcerts.hc₂, h3a, h3b, cantorPipeline_def]
  rfl

/-- **A valid certificate pack stays valid under base change** (into a nontrivial
ring). -/
theorem IsPipelineCerts.map [Nontrivial S] (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic)
    (hu₃ : D.u₃.Monic) (hcerts : IsPipelineCerts f D d n) :
    IsPipelineCerts (f.map φ) (D.map φ) (d.map φ) n := by
  have hS₁monic : (cantorStage₁ f D d).1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₃monic : (cantorStage₃ f D d).1.Monic :=
    cantorCompose_monic f (cantorReduce_monic f hcerts.hc₁) hu₃
  have hfinm : (cantorPipeline f D d).1.Monic := cantorReduce_monic f hcerts.hc₂
  obtain ⟨h1a, h1b⟩ := Prod.ext_iff.mp (cantorStage₁_map φ (D := D) (d := d) hu₁ hu₂)
  dsimp only at h1a h1b
  obtain ⟨h2a, h2b⟩ := Prod.ext_iff.mp (cantorStage₂_map φ hu₁ hu₂ hcerts.hc₁)
  dsimp only at h2a h2b
  obtain ⟨h3a, h3b⟩ := Prod.ext_iff.mp (cantorStage₃_map φ hu₁ hu₂ hcerts.hc₁ hu₃)
  dsimp only at h3a h3b
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      CantorCertData.map_s₁, CantorCertData.map_s₂, CantorCertData.map_s₃,
      PipelineData.map_u₁, PipelineData.map_u₂, PipelineData.map_v₁,
      PipelineData.map_v₂] using congrArg (Polynomial.map φ) hcerts.hbez₁
  · have h := map_reduceCert φ f hS₁monic hcerts.hc₁
    rwa [h1a, h1b] at h
  · have := congrArg (Polynomial.map φ) hcerts.hbez₂
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at this
    rwa [h2a, h2b] at this
  · have h := map_reduceCert φ f hS₃monic hcerts.hc₂
    rwa [h3a, h3b] at h
  · obtain ⟨h4a, -⟩ := Prod.ext_iff.mp (map_cantorPipeline_generic φ hu₁ hu₂ hu₃ hcerts)
    dsimp only at h4a
    rw [← h4a, hfinm.natDegree_map]
    exact hcerts.hdeg

end PipelineMap

section PipelineLift

variable {R κ : Type*} [CommRing R] [CommRing κ] [Nontrivial κ] {ψ : R →+* κ}

/-- **Certificate-pack lifting for the generic Cantor pipeline**: a valid and generic
certificate pack over the image ring lifts to a valid pack over `R`, provided `ψ` is
surjective, `ψ`-nonvanishing detects units, and the kernel of `ψ` lies in the Jacobson
radical (as for the residue map of a local ring). The Bézout certificates lift with
prescribed residues by Nakayama (`ChabautyColeman.exists_bezout_lift_map`), and the
reduction certificates lift by the degree squeeze
(`ChabautyColeman.exists_reduceCert_map`). Both liftings prescribe residues, so the
lifted pack reduces to the given one — which is what carries residue-field conditions on the
pack (Weierstrass avoidance) up to the lift. -/
theorem exists_isPipelineCerts_of_center (hsurj : Function.Surjective ψ)
    (hdet : ∀ x : R, ψ x ≠ 0 → IsUnit x) (hker : RingHom.ker ψ ≤ Ideal.jacobson ⊥)
    {f : R[X]} {D : PipelineData R} (hf : f.Monic) (hu₁ : D.u₁.Monic) (hu₂ : D.u₂.Monic)
    (hu₃ : D.u₃.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f)
    (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f) {n : ℕ} (d' : CantorCertData κ)
    (hd' : IsPipelineCenterCerts (f.map ψ) (D.map ψ) d' n) :
    ∃ d : CantorCertData R, IsPipelineCerts f D d n ∧ d.map ψ = d' := by
  have := ψ.domain_nontrivial
  -- stage 1: lift the first composition certificate with prescribed residues
  have habc1 : d'.s₁ * D.u₁.map ψ + d'.s₂ * D.u₂.map ψ + d'.s₃ * ((D.v₁ + D.v₂).map ψ) = 1 := by
    rw [Polynomial.map_add]
    exact hd'.hbez₁
  obtain ⟨s₁, s₂, s₃, hs, hs₁, hs₂, hs₃⟩ := exists_bezout_lift_map hsurj hker hu₁ habc1
  set S₁ := cantorCompose f D.u₁ D.v₁ D.u₂ D.v₂ s₁ s₂ s₃
  have hS₁monic : S₁.1.Monic := cantorCompose_monic f hu₁ hu₂
  have hS₁dvd : S₁.1 ∣ S₁.2 ^ 2 - f := cantorCompose_dvd f hs hd₁ hd₂
  have hS₁lt : S₁.2.degree < S₁.1.degree := cantorCompose_degree_lt f hu₁ hu₂
  obtain ⟨hS₁ψ₁, hS₁ψ₂⟩ := Prod.ext_iff.mp (map_cantorCompose ψ f hu₁ hu₂ D.v₁ D.v₂ s₁ s₂ s₃)
  dsimp only at hS₁ψ₁ hS₁ψ₂
  rw [hs₁, hs₂, hs₃] at hS₁ψ₁ hS₁ψ₂
  -- stage 2: lift the first reduction certificate
  obtain ⟨c₁, hc₁map, hc₁⟩ := exists_reduceCert_map hdet hf hS₁monic hS₁lt hS₁dvd
    (by rw [hS₁ψ₁, hS₁ψ₂]; exact hd'.hc₁) (by rw [hS₁ψ₁, hS₁ψ₂]; exact hd'.hfull₁)
  set S₂ := cantorReduce f S₁.1 S₁.2 c₁
  have hS₂monic : S₂.1.Monic := cantorReduce_monic f hc₁
  have hS₂dvd : S₂.1 ∣ S₂.2 ^ 2 - f := cantorReduce_dvd f hS₁monic hS₁dvd hc₁
  obtain ⟨hS₂ψ₁, hS₂ψ₂⟩ := Prod.ext_iff.mp (map_cantorReduce ψ f hS₁monic hc₁)
  dsimp only at hS₂ψ₁ hS₂ψ₂
  rw [hS₁ψ₁, hS₁ψ₂, hc₁map] at hS₂ψ₁ hS₂ψ₂
  -- stage 3: lift the second composition certificate with prescribed residues
  have habc2 : d'.t₁ * S₂.1.map ψ + d'.t₂ * D.u₃.map ψ + d'.t₃ * ((S₂.2 + D.v₃).map ψ) = 1 := by
    rw [hS₂ψ₁, Polynomial.map_add, hS₂ψ₂]
    exact hd'.hbez₂
  obtain ⟨t₁, t₂, t₃, ht, ht₁, ht₂, ht₃⟩ := exists_bezout_lift_map hsurj hker hS₂monic habc2
  set S₃ := cantorCompose f S₂.1 S₂.2 D.u₃ D.v₃ t₁ t₂ t₃
  have hS₃monic : S₃.1.Monic := cantorCompose_monic f hS₂monic hu₃
  have hS₃dvd : S₃.1 ∣ S₃.2 ^ 2 - f := cantorCompose_dvd f ht hS₂dvd hd₃
  have hS₃lt : S₃.2.degree < S₃.1.degree := cantorCompose_degree_lt f hS₂monic hu₃
  obtain ⟨hS₃ψ₁, hS₃ψ₂⟩ := Prod.ext_iff.mp (map_cantorCompose ψ f hS₂monic hu₃ S₂.2 D.v₃ t₁ t₂ t₃)
  dsimp only at hS₃ψ₁ hS₃ψ₂
  rw [hS₂ψ₁, hS₂ψ₂, ht₁, ht₂, ht₃] at hS₃ψ₁ hS₃ψ₂
  -- stage 4: lift the second reduction certificate
  obtain ⟨c₂, hc₂map, hc₂⟩ := exists_reduceCert_map hdet hf hS₃monic hS₃lt hS₃dvd
    (by rw [hS₃ψ₁, hS₃ψ₂]; exact hd'.hc₂) (by rw [hS₃ψ₁, hS₃ψ₂]; exact hd'.hfull₂)
  -- the final degree matches the center by monicity
  obtain ⟨hfinψ₁, -⟩ := Prod.ext_iff.mp (map_cantorReduce ψ f hS₃monic hc₂)
  dsimp only at hfinψ₁
  rw [hS₃ψ₁, hS₃ψ₂, hc₂map] at hfinψ₁
  have hdeg : (cantorReduce f S₃.1 S₃.2 c₂).1.natDegree = n := by
    rw [← (cantorReduce_monic f hc₂).natDegree_map ψ, hfinψ₁]
    exact hd'.hdeg
  exact ⟨⟨s₁, s₂, s₃, c₁, t₁, t₂, t₃, c₂⟩, ⟨hs, hc₁, ht, hc₂, hdeg⟩,
    by simp only [CantorCertData.map, hs₁, hs₂, hs₃, hc₁map, ht₁, ht₂, ht₃, hc₂map]⟩

end PipelineLift

section PipelineClass

open nonZeroDivisors

variable {K : Type*} [Field K] {f : K[X]} [NeZero (2 : K)] [Fact (Odd f.natDegree)]
  [Fact (Squarefree f)] {D : PipelineData K} {d : CantorCertData K} {n : ℕ}

/-- **The generic Cantor pipeline computes the product of the three input classes.** -/
theorem mk0_cantorPipeline_generic (hu₁ : D.u₁.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f)
    (hu₂ : D.u₂.Monic) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hu₃ : D.u₃.Monic) (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f)
    (hcerts : IsPipelineCerts f D d n)
    (hfinm : (cantorPipeline f D d).1.Monic) :
    ClassGroup.mk0 ⟨mumfordIdeal f (cantorPipeline f D d).1 (cantorPipeline f D d).2,
        mumfordIdeal_mem_nonZeroDivisors f hfinm.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f D.u₁ D.v₁,
            mumfordIdeal_mem_nonZeroDivisors f hu₁.ne_zero D.v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₂ D.v₂,
            mumfordIdeal_mem_nonZeroDivisors f hu₂.ne_zero D.v₂⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₃ D.v₃,
            mumfordIdeal_mem_nonZeroDivisors f hu₃.ne_zero D.v₃⟩ := by
  have hD₃ : cantorStage₃ f D d
      = cantorCompose f (cantorStage₂ f D d).1 (cantorStage₂ f D d).2
        D.u₃ (- -D.v₃) d.t₁ d.t₂ d.t₃ := by rw [neg_neg]; exact cantorStage₃_def ..
  have hbez₂ : d.t₁ * (cantorStage₂ f D d).1 + d.t₂ * D.u₃
      + d.t₃ * ((cantorStage₂ f D d).2 + - -D.v₃) = 1 := by
    rw [neg_neg]; exact hcerts.hbez₂
  have hdu₃ : D.u₃ ∣ (-D.v₃) ^ 2 - f := by rwa [neg_pow_two]
  have h := mk0_cantorPipeline f (cantorStage₁_def f D d)
    (cantorStage₂_def f D d) hD₃ (cantorPipeline_def f D d)
    hu₁ hd₁ hu₂ hd₂ hu₃ hdu₃ hcerts.hbez₁ hcerts.hc₁ hbez₂ hcerts.hc₂ hfinm
  rwa [neg_neg] at h

variable {D' : PipelineData K} {d' : CantorCertData K}

/-- **Two generic pipelines whose inputs have the same class product have the same
output**: both outputs are reduced representatives of that class. This is the
auxiliary-point independence mechanism of `thm:omega-prime-global`(a). -/
theorem cantorPipeline_eq_cantorPipeline_of_mk0_eq (hu₁ : D.u₁.Monic)
    (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f) (hu₂ : D.u₂.Monic) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hu₃ : D.u₃.Monic)
    (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f) (hu₁' : D'.u₁.Monic) (hd₁' : D'.u₁ ∣ D'.v₁ ^ 2 - f)
    (hu₂' : D'.u₂.Monic) (hd₂' : D'.u₂ ∣ D'.v₂ ^ 2 - f) (hu₃' : D'.u₃.Monic)
    (hd₃' : D'.u₃ ∣ D'.v₃ ^ 2 - f)
    (hcerts : IsPipelineCerts f D d n)
    (hcerts' : IsPipelineCerts f D' d' n)
    (hg : 2 * n < f.natDegree)
    (hmk : ClassGroup.mk0 ⟨mumfordIdeal f D.u₁ D.v₁,
          mumfordIdeal_mem_nonZeroDivisors f hu₁.ne_zero D.v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₂ D.v₂,
          mumfordIdeal_mem_nonZeroDivisors f hu₂.ne_zero D.v₂⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₃ D.v₃,
          mumfordIdeal_mem_nonZeroDivisors f hu₃.ne_zero D.v₃⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f D'.u₁ D'.v₁,
          mumfordIdeal_mem_nonZeroDivisors f hu₁'.ne_zero D'.v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D'.u₂ D'.v₂,
          mumfordIdeal_mem_nonZeroDivisors f hu₂'.ne_zero D'.v₂⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D'.u₃ D'.v₃,
          mumfordIdeal_mem_nonZeroDivisors f hu₃'.ne_zero D'.v₃⟩) :
    cantorPipeline f D d = cantorPipeline f D' d' := by
  obtain ⟨hm₁, hdvd₁, hlt₁⟩ :=
    cantorPipeline_monic_dvd_degree_lt hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts
  obtain ⟨hm₂, hdvd₂, hlt₂⟩ :=
    cantorPipeline_monic_dvd_degree_lt hu₁' hd₁' hu₂' hd₂' hu₃' hd₃' hcerts'
  have hcl : ClassGroup.mk0 ⟨mumfordIdeal f (cantorPipeline f D d).1 (cantorPipeline f D d).2,
        mumfordIdeal_mem_nonZeroDivisors f hm₁.ne_zero _⟩
      = ClassGroup.mk0 ⟨mumfordIdeal f (cantorPipeline f D' d').1 (cantorPipeline f D' d').2,
        mumfordIdeal_mem_nonZeroDivisors f hm₂.ne_zero _⟩ := by
    rw [mk0_cantorPipeline_generic hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts hm₁,
      mk0_cantorPipeline_generic hu₁' hd₁' hu₂' hd₂' hu₃' hd₃' hcerts' hm₂]
    exact hmk
  obtain ⟨h1, h2⟩ := mumfordIdeal_reduced_unique f hm₁ hm₂ hlt₁ hlt₂
    (hcerts.hdeg ▸ hg) (hcerts'.hdeg ▸ hg) hdvd₁ hdvd₂ hcl
  exact Prod.ext h1 h2

/-- **A pipeline whose outer blocks cancel returns its middle datum.** The output is a
reduced Mumford datum in the class of the middle one, and reduced representatives are unique
(`ChabautyColeman.mumfordIdeal_reduced_unique`). For the per-disk configuration
`[P₀ + ι Q] + τ + [Q + ι P₀]` the outer blocks are inverse classes, so the pipeline returns
`τ` — which makes the avoidance condition of its second chain free. -/
theorem cantorPipeline_eq_middle (hu₁ : D.u₁.Monic) (hd₁ : D.u₁ ∣ D.v₁ ^ 2 - f)
    (hu₂ : D.u₂.Monic) (hd₂ : D.u₂ ∣ D.v₂ ^ 2 - f) (hu₃ : D.u₃.Monic) (hd₃ : D.u₃ ∣ D.v₃ ^ 2 - f)
    (hcerts : IsPipelineCerts f D d n)
    (hcancel : ClassGroup.mk0 ⟨mumfordIdeal f D.u₁ D.v₁,
          mumfordIdeal_mem_nonZeroDivisors f hu₁.ne_zero D.v₁⟩
        * ClassGroup.mk0 ⟨mumfordIdeal f D.u₃ D.v₃,
          mumfordIdeal_mem_nonZeroDivisors f hu₃.ne_zero D.v₃⟩ = 1)
    (hv₂ : D.v₂.degree < D.u₂.degree) (hg₂ : 2 * D.u₂.natDegree < f.natDegree)
    (hgn : 2 * n < f.natDegree) :
    cantorPipeline f D d = (D.u₂, D.v₂) := by
  obtain ⟨hfinm, hfind, hfinlt⟩ :=
    cantorPipeline_monic_dvd_degree_lt hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts
  have hcl := mk0_cantorPipeline_generic hu₁ hd₁ hu₂ hd₂ hu₃ hd₃ hcerts hfinm
  rw [mul_right_comm, hcancel, one_mul] at hcl
  obtain ⟨hu, hv⟩ := mumfordIdeal_reduced_unique f hfinm hu₂ hfinlt hv₂
    (by rw [hcerts.hdeg]; exact hgn) hg₂ hfind hd₂ hcl
  exact Prod.ext hu hv

end PipelineClass

end ChabautyColeman

end
