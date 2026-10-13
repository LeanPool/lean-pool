/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module




public import LeanPool.Superdiffusion.Algsuperdiff.MainTheorems
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Measurability.DisplacementExpectations
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.DisplacementIntegrability

/-!
# Superdiffusion and anomalous regularization in self-similar random flows

Source: arxiv:2601.22142, url:https://github.com/scottnarmstrong/Superdiffusion/tree/7f20476385d4af418f110303085ad0740c9eba46
Authors: Scott Armstrong, Tuomo Kuusi
Status: verified
Main declarations: `Algsuperdiff.superdiffusivity`, `Algsuperdiff.generator_renormalization`, `Algsuperdiff.anomalous_regularity`
Tags: superdiffusion, stochastic-homogenization, random-incompressible-flows, anomalous-regularity
MSC: 60K37, 35B27, 60J60
-/
