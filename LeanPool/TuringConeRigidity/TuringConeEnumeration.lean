/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeIdealCoding
public import LeanPool.TuringConeRigidity.TuringConeLocality
public import LeanPool.TuringConeRigidity.SetModels.EnumerationDecoding
public import LeanPool.TuringConeRigidity.SetModels.IdealLift

/-!
# Enumeration graphs in a principal cone

Unlike pointwise unary decoding, this decodes one relation simultaneously for
all positions of an enumeration. The output is a Sigma-5 index graph relative
to an oracle bounding the transported coding parameters and the comparison
sequence. No uniform representative of the whole degree structure is assumed.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeEnumeration

open IndexPresentation IndexTuples ArithmeticHierarchy
open ArithmeticModelDecoding (two twoIndex twoIndex_primrec)
open SetCoding RelationCoding BoundedDecoding OracleJump ConeLocality

/-- A degree enumeration with successor and payload relations interpreted relative to the cone
base. -/
structure Enumeration (a : Degree) where
  /-- The injective degree sequence indexing the cone-relative enumeration. -/
  node : ℕ → Degree
  injective : Function.Injective node
  /-- The degree value attached to each cone-relative enumeration node. -/
  output : ℕ → Degree
  /-- The cone-relative relation code representing successor on the node sequence. -/
  successor : RelationCode 2
  /-- The cone-relative relation code pairing nodes with their output degrees. -/
  payload : RelationCode 2
  successor_spec : ∀ x y, ConeCoding.Holds a successor (two x y) ↔
    ∃ k, x = node k ∧ y = node (k + 1)
  payload_spec : ∀ x y, ConeCoding.Holds a payload (two x y) ↔
    ∃ k, x = node k ∧ y = output k

theorem path_node {a Y} (c : Enumeration a) {z : ℕ}
    (hz : Dom Y z) (he : value Y z = c.node 0)
    {n t : ℕ} (hpath : Path a Y c.successor z n t) :
    ∀ i, i ≤ n → Dom Y (item t i) ∧ value Y (item t i) = c.node i := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨hpath.1, (le_antisymm ((le_iff hpath.1 hz).mp hpath.2.1)
      ((le_iff hz hpath.1).mp hpath.2.2.1)).trans he⟩
  | succ i ih =>
    have hprev := ih (by omega)
    have hs := hpath.2.2.2 i (by omega)
    have hnext : Dom Y (item t (i + 1)) := by
      simpa [twoIndex, entry] using hs.1 (1 : Fin 2)
    obtain ⟨k, hk, hkn⟩ := (c.successor_spec _ _).mp
      ((presented_two hprev.1 hnext).mp hs)
    have hki : k = i := c.injective (hk.symm.trans hprev.2)
    exact ⟨hnext, by simpa only [hki] using hkn⟩

theorem node_below {a} (Y : Oracle) (c : Enumeration a)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) : c.node n ≤ degree Y := by
  obtain ⟨d, hd, _⟩ := (c.successor_spec (c.node n) (c.node (n + 1))).mpr ⟨n, rfl, rfl⟩
  exact (hd 0).2.1.trans (hS.1 0).1

theorem path_sigma (a : Degree) (Y : Oracle) (ha : a ≤ degree Y)
    (S : RelationCode 2) (z : ℕ) (hS : RelationBelow S (degree Y)) :
    Sigma Y 5 (fun v => Path a Y S z (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let start := item_primrec.comp r (Primrec.const 0)
  have hd : Sigma Y 5 (fun v => Dom Y (item (Nat.unpair v).2 0)) :=
    (dom_pi Y start).switch.raise.raise
  have hl := (le_sigma Y start (Primrec.const z)).raise.raise
  have hr := (le_sigma Y (Primrec.const z) start).raise.raise
  have hs := ((ConeArithmetic.sigma5_decoding a Y ha S hS).comp
    (twoIndex_primrec.comp (item_primrec.comp (r.comp f) r)
      (item_primrec.comp (r.comp f) (Primrec.succ.comp r)))).bounded_all f
  exact (hd.and (hl.and (hr.and hs))).congr (fun v => by
    simp only [Nat.unpair_pair]; rfl)

/-- A cone-relative successor path ends at a node with the degree represented by index `j` as
payload. -/
def Defined (a : Degree) (Y : Oracle) (S P : RelationCode 2) (z n j : ℕ) : Prop :=
  ∃ t, Path a Y S z n t ∧ Presented a Y P (twoIndex (item t n) j)

theorem defined_sigma (a : Degree) (Y : Oracle) (ha : a ≤ degree Y)
    (S P : RelationCode 2) (z : ℕ)
    (hS : RelationBelow S (degree Y)) (hP : RelationBelow P (degree Y)) :
    Sigma Y 5 (fun v => Defined a Y S P z (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hs := (path_sigma a Y ha S z hS).comp (Primrec₂.natPair.comp (f.comp f) r)
  have hp := (ConeArithmetic.sigma5_decoding a Y ha P hP).comp
    (twoIndex_primrec.comp (item_primrec.comp r (f.comp f)) (r.comp f))
  exact ((hs.and hp).ex).congr (fun v => by
    simp only [Defined, Presented, Nat.unpair_pair])

theorem defined_iff {a Y} (c : Enumeration a) {z j : ℕ}
    (hz : Dom Y z) (hj : Dom Y j) (he : value Y z = c.node 0)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) :
    Defined a Y c.successor c.payload z n j ↔ c.output n = value Y j := by
  constructor
  · rintro ⟨t, hpath, hp⟩
    have hn := path_node c hz he hpath n le_rfl
    obtain ⟨k, hk, hv⟩ := (c.payload_spec _ _).mp ((presented_two hn.1 hj).mp hp)
    have hkn := c.injective (hk.symm.trans hn.2)
    exact hkn ▸ hv.symm
  · intro hU
    choose e hd hev using fun i => value_surjective Y (c.node i) (node_below Y c hS i)
    obtain ⟨t, ht⟩ := (exists_items (n + 1) (fun i j => j = e i)).mp
      (fun i _ => ⟨e i, rfl⟩)
    have hdom (i : ℕ) (hi : i ≤ n) : Dom Y (item t i) := by
      rw [ht i (by omega)]; exact hd i
    have hval (i : ℕ) (hi : i ≤ n) : value Y (item t i) = c.node i := by
      rw [ht i (by omega), hev i]
    refine ⟨t, ⟨hdom 0 (by omega), ?_, ?_, ?_⟩, ?_⟩
    · apply (le_iff (hdom 0 (by omega)) hz).mpr
      rw [hval 0 (by omega), he]
    · apply (le_iff hz (hdom 0 (by omega))).mpr
      rw [hval 0 (by omega), he]
    · intro i hi
      apply (presented_two (hdom i (by omega)) (hdom (i + 1) (by omega))).mpr
      exact (c.successor_spec _ _).mpr ⟨i, hval i (by omega), hval (i + 1) (by omega)⟩
    · apply (presented_two (hdom n le_rfl) hj).mpr
      exact (c.payload_spec _ _).mpr ⟨n, hval n le_rfl, hU.symm⟩

/-- A single arithmetic predicate describes all entries of the enumeration graph. -/
theorem graph_sigma {a : Degree} {H Y : Oracle} (ha : a ≤ degree Y)
    (hHY : Reduces H Y) (c : Enumeration a)
    (hS : RelationBelow c.successor (degree Y)) (hP : RelationBelow c.payload (degree Y)) :
    Sigma Y 5 (fun v => c.output (Nat.unpair v).1 =
      degree (EncodedForcing.columns H (Nat.unpair v).2)) := by
  obtain ⟨z, hz, he⟩ := value_surjective Y (c.node 0) (node_below Y c hS 0)
  obtain ⟨idx, hidx, hrep⟩ := LocalColumnIndices.uniform_indices hHY
  have hi := (defined_sigma a Y ha c.successor c.payload z hS hP).comp
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (hidx.comp (Primrec.snd.comp Primrec.unpair)))
  apply hi.congr
  intro v
  simp only [Nat.unpair_pair]
  rw [defined_iff c hz ((TableIndices.valid_iff_represents _ _).mpr ⟨_, hrep _⟩) he hS]
  rw [value_eq (hrep _)]

open IdealInterpretation ConeIdealCoding

/-- Transport an entire coded sequence through an isomorphism of an ideal onto
its principal cone. Only degrees below the code bound are used. -/
theorem transport_enumeration {I : DegreeIdeal} {a : I} (ρ : I ≃o Set.Ici a)
    (c : EnumerationDecoding.Enumeration) (b : I)
    (hS : RelationBelow c.successor b.val) (hP : RelationBelow c.payload b.val)
    (v : ℕ → I) (hv : ∀ n, (v n).val = c.output n) :
    ∃ d : Enumeration a.val, (∀ n, d.output n = image ρ (v n)) ∧
      RelationBelow d.successor (image ρ b) ∧ RelationBelow d.payload (image ρ b) := by
  let S := RCode.ofBelow c.successor b hS
  let P := RCode.ofBelow c.payload b hP
  have hn (n : ℕ) : c.node n ∈ I.carrier := by
    have hh : S.external.Holds (two (c.node n) (c.node (n + 1))) := by
      simpa only [S, RCode.external_ofBelow] using (c.successor_spec _ _).mpr ⟨n, rfl, rfl⟩
    exact S.coordinates_mem hh 0
  let node : ℕ → I := fun n => ⟨c.node n, hn n⟩
  have hi : Function.Injective (fun n => image ρ (node n)) := by
    intro i j he
    have h : ρ (node i) = ρ (node j) := Subtype.ext (Element.ext _ _ he)
    exact c.injective (congrArg Element.val (ρ.injective h))
  have hs (x y : Set.Ici a) :
      ConeCoding.Holds a.val (mapRelation ρ S) (two x.val.val y.val.val) ↔
        ∃ k, x = ρ (node k) ∧ y = ρ (node (k + 1)) := by
    have hh := map_relation_two ρ S (ρ.symm x) (ρ.symm y)
    simp only [image, ρ.apply_symm_apply, S, RCode.external_ofBelow] at hh
    rw [hh, c.successor_spec]
    constructor
    · rintro ⟨k, hk, hl⟩
      have h₀ : ρ.symm x = node k := Element.ext _ _ hk
      have h₁ : ρ.symm y = node (k + 1) := Element.ext _ _ hl
      exact ⟨k, by rw [← h₀, ρ.apply_symm_apply], by rw [← h₁, ρ.apply_symm_apply]⟩
    · rintro ⟨k, rfl, rfl⟩
      exact ⟨k, by simp only [ρ.symm_apply_apply, node],
        by simp only [ρ.symm_apply_apply, node]⟩
  have hp (x y : Set.Ici a) :
      ConeCoding.Holds a.val (mapRelation ρ P) (two x.val.val y.val.val) ↔
        ∃ k, x = ρ (node k) ∧ y = ρ (v k) := by
    have hh := map_relation_two ρ P (ρ.symm x) (ρ.symm y)
    simp only [image, ρ.apply_symm_apply, P, RCode.external_ofBelow] at hh
    rw [hh, c.payload_spec]
    constructor
    · rintro ⟨k, hk, hl⟩
      have h₀ : ρ.symm x = node k := Element.ext _ _ hk
      have h₁ : ρ.symm y = v k := Element.ext _ _ (hl.trans (hv k).symm)
      exact ⟨k, by rw [← h₀, ρ.apply_symm_apply], by rw [← h₁, ρ.apply_symm_apply]⟩
    · rintro ⟨k, rfl, rfl⟩
      exact ⟨k, by simp only [ρ.symm_apply_apply, node],
        by simpa only [ρ.symm_apply_apply] using hv k⟩
  have hs' (x y : Degree) : ConeCoding.Holds a.val (mapRelation ρ S) (two x y) ↔
      ∃ k, x = image ρ (node k) ∧ y = image ρ (node (k + 1)) := by
    constructor
    · intro h
      have hx := coordinates_mem ρ S h 0
      have hy := coordinates_mem ρ S h 1
      obtain ⟨k, hk, hl⟩ := (hs ⟨⟨x, hx.2⟩, Set.mem_Ici.mpr hx.1⟩
        ⟨⟨y, hy.2⟩, Set.mem_Ici.mpr hy.1⟩).mp h
      exact ⟨k, congrArg (fun z : Set.Ici a => z.val.val) hk,
        congrArg (fun z : Set.Ici a => z.val.val) hl⟩
    · rintro ⟨k, rfl, rfl⟩
      exact (hs _ _).mpr ⟨k, rfl, rfl⟩
  have hp' (x y : Degree) : ConeCoding.Holds a.val (mapRelation ρ P) (two x y) ↔
      ∃ k, x = image ρ (node k) ∧ y = image ρ (v k) := by
    constructor
    · intro h
      have hx := coordinates_mem ρ P h 0
      have hy := coordinates_mem ρ P h 1
      obtain ⟨k, hk, hl⟩ := (hp ⟨⟨x, hx.2⟩, Set.mem_Ici.mpr hx.1⟩
        ⟨⟨y, hy.2⟩, Set.mem_Ici.mpr hy.1⟩).mp h
      exact ⟨k, congrArg (fun z : Set.Ici a => z.val.val) hk,
        congrArg (fun z : Set.Ici a => z.val.val) hl⟩
    · rintro ⟨k, rfl, rfl⟩
      exact (hp _ _).mpr ⟨k, rfl, rfl⟩
  let d : Enumeration a.val := ⟨fun k => image ρ (node k), hi,
    fun k => image ρ (v k), mapRelation ρ S, mapRelation ρ P, hs', hp'⟩
  refine ⟨d, fun _ => rfl, map_relation_below ρ S b ?_, map_relation_below ρ P b ?_⟩
  · simpa only [S, RCode.external_ofBelow] using hS
  · simpa only [P, RCode.external_ofBelow] using hP

end OAI.TuringRigidity.ConeEnumeration
