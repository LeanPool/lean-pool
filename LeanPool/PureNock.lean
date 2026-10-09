/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.FingerprintLayer

/-!
# Pure Nock semantics, trace certificates, and polynomial fingerprints

Source: url:https://github.com/nockchain/pure-nock-lean
Authors: Pure Nock formalization contributors
Status: verified
Main declarations: `Nock.Verb.runProgram_adequate_complete`, `Nock.Verb.runTraceProgram_certificate`, `Nock.paper_field_bridge`, `Nock.NPR.collision_prob_le`, `Nock.NPR.fnHorner_eq_fn`
Tags: operational-semantics, verified-evaluation, execution-traces, finite-fields, polynomial-fingerprints
MSC: 68Q55, 68Q60, 11T71
-/

/-!
# Pure Nock semantics, trace certificates, and polynomial fingerprints

The source is `nockchain/pure-nock-lean` at Apache-2.0 commit
`4838863baa2d49e38573efa3474e77bf1154f300`, first publicly released on 26 August 2026.
The original release commit credits Akis (Assimakis A. Kattis); the upstream NOTICE attributes
copyright to the formalization contributors. This port retains that collective attribution.

The imported scope is the 23-module fingerprint release closure: language semantics,
modular evaluation, guarded bridges, execution trace certificates, and polynomial fingerprints.
Upstream audit programs, differential test corpora, C extraction, branding, and patches are omitted.
The bundled manuscript draft v0.1.6 is the source for `main.tex` line references in the modules:
https://github.com/nockchain/pure-nock-lean/blob/4838863baa2d49e38573efa3474e77bf1154f300/paper/main.tex.

The bridge identifies natural-number and modular evaluation only on guarded executions.
Fingerprint distinctness is equality of field-valued coefficient data and tree shape; casting
natural-number leaves can identify different natural-number nouns. The table estimate is a union
bound with shared randomness. These results cover the language and fingerprint layers of the
compilation framework; the zkVM, AIR, RAP, table security theorem, and concrete Goldilocks field
are outside this import. The opcode-11 hint extension is separate from the paper opcode domain.
-/
