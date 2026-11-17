/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeRepresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRigidity
public import LeanPool.TuringConeRigidity.Representation.GenericRepresentation

/-!
# From a generic inverse representative to cone rigidity

A continuous representative of `pullback e` on sufficiently generic oracles is
enough. We upgrade it to an `InverseBorelLift` using the existing generic coding
and Borel selection of principal ideal intersections.

The necessary modification to the automorphism argument is in the choice of the
two auxiliary generics. For an input `X`, choose a minimal pair over `A ⊕ X`,
where `degree A = a`, rather than over `X`. This gives the common-lower-bound
identity in the cone before transporting it through `e.symm`.

The existence of such a generic representative for an arbitrary cone isomorphism
remains an explicit hypothesis. No global cone representation theorem is asserted.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeRigidity

open FiniteShuffle ShuffleRequirements PairGenericSelection

theorem le_pullback_iff {a : Degree} (e : Degree ≃o Set.Ici a) (y x : Degree) :
    y ≤ pullback e x ↔ (e y).val ≤ a ⊔ x := by
  constructor
  · intro h
    have hmap : (e y).val ≤ (e (pullback e x)).val := e.monotone h
    simpa only [apply_pullback_val] using hmap
  · intro h
    apply e.le_iff_le.mp
    change (e y).val ≤ (e (pullback e x)).val
    simpa only [apply_pullback_val] using h

/-- An inverse representative continuous on a set of sufficiently generic oracles. -/
def InverseGenericContinuousLift {a : Degree} (e : Degree ≃o Set.Ici a) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ F : Oracle → Oracle, ContinuousOn F {X | GenericFor D X} ∧
      ∀ X, GenericFor D X → degree (F X) = pullback e (degree X)

/-- One oracle program, with one fixed parameter, represents the inverse on
sufficiently generic inputs. -/
def InverseGenericProgramLift {a : Degree} (e : Degree ≃o Set.Ici a) : Prop :=
  ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
    ∃ P : Oracle, ∃ p : OracleCode, ∀ X, GenericFor D X →
      ∃ Y, OracleCode.eval (oracleFunction (join X P)) p = oracleFunction Y ∧
        degree Y = pullback e (degree X)

theorem inverse_generic_program_of_continuous {a : Degree}
    (e : Degree ≃o Set.Ici a) (h : InverseGenericContinuousLift e) :
    InverseGenericProgramLift e := by
  obtain ⟨D, hD, F, hF, hrep⟩ := h
  obtain ⟨P, p, hp⟩ := ContinuousCode.continuous_uniform_program
    {X | GenericFor D X} F hF
  exact ⟨D, hD, P, p, fun X hX => ⟨F X, hp X hX, hrep X hX⟩⟩

/-- A generic program suffices for a global Borel inverse lift. The minimal pairs
used in this proof are chosen over the joined base `A ⊕ X`. -/
theorem inverse_borel_lift_of_generic_program {a : Degree}
    (e : Degree ≃o Set.Ici a) (h : InverseGenericProgramLift e) :
    InverseBorelLift e := by
  obtain ⟨A, hA⟩ := degree_surjective a
  obtain ⟨D, hD, P, p, hp⟩ := h
  let F : Oracle → Oracle := fun Y => programOutput p (join Y P)
  have hFmeas : Measurable F := (programOutput_measurable p).comp
    (join_measurable _ _ measurable_id measurable_const)
  have hF : ∀ Y, GenericFor D Y → degree (F Y) = pullback e (degree Y) := by
    intro Y hY
    obtain ⟨Z, hpZ, hZ⟩ := hp Y hY
    change degree (programOutput p (join Y P)) = _
    rw [programOutput_eq p _ Z hpZ]
    exact hZ
  obtain ⟨G, hG, hgeneric, hideal⟩ := selected_generic_ideal D hD
  let K : Bool → Oracle → Oracle := fun b X => G b (join A X)
  have hK (b : Bool) : Measurable (K b) :=
    (hG b).comp (join_measurable _ _ measurable_const measurable_id)
  have hKgen (X : Oracle) (b : Bool) :
      GenericFor D (K b X) ∧ GenericCoding.InfiniteOdd (K b X) ∧
        ∀ Y, GenericFor D (GenericCoding.code Y (K b X)) :=
    hgeneric (join A X) b
  let L : Bool → Oracle → Oracle := fun b X =>
    join (F (GenericCoding.code X (K b X))) (F (K b X))
  have hL (b : Bool) : Measurable (L b) :=
    join_measurable _ _
      (hFmeas.comp (GenericCoding.code_measurable.comp (measurable_id.prodMk (hK b))))
      (hFmeas.comp (hK b))
  have hdegree (X : Oracle) (b : Bool) :
      degree (L b X) = pullback e (degree (join X (K b X))) := by
    change degree (F (GenericCoding.code X (K b X))) ⊔ degree (F (K b X)) = _
    rw [hF _ ((hKgen X b).2.2 X), hF _ (hKgen X b).1, ← pullback_sup]
    exact congrArg (pullback e)
      (GenericCoding.join_degree_eq X (K b X) (hKgen X b).2.1)
  apply borel_of_ideal_intersection (L false) (L true) (hL false) (hL true)
    (fun X => pullback e (degree X))
  intro X b
  rw [hdegree X false, hdegree X true]
  simp only [le_pullback_iff]
  have hbase := hideal (join A X) (e b).val
  change ((e b).val ≤ degree A ⊔ degree X ↔
    (e b).val ≤ (degree A ⊔ degree X) ⊔ degree (K false X) ∧
    (e b).val ≤ (degree A ⊔ degree X) ⊔ degree (K true X)) at hbase
  change (e b).val ≤ a ⊔ degree X ↔
    (e b).val ≤ a ⊔ (degree X ⊔ degree (K false X)) ∧
    (e b).val ≤ a ⊔ (degree X ⊔ degree (K true X))
  simpa only [hA, sup_assoc] using hbase

/-- Continuous generic inverse representations already imply triviality of the
cone base; a global Borel representative need not be assumed separately. -/
theorem eq_bot_of_inverse_generic_continuous_lift {a : Degree}
    (e : Degree ≃o Set.Ici a) (h : InverseGenericContinuousLift e) : a = ⊥ :=
  eq_bot_of_inverse_borel_lift e
    (inverse_borel_lift_of_generic_program e (inverse_generic_program_of_continuous e h))

theorem eq_bot_of_inverse_generic_program_lift {a : Degree}
    (e : Degree ≃o Set.Ici a) (h : InverseGenericProgramLift e) : a = ⊥ :=
  eq_bot_of_inverse_borel_lift e (inverse_borel_lift_of_generic_program e h)

end OAI.TuringRigidity.ConeRigidity
