/-
Copyright (c) 2026 Statlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Likelihood-ratio facts

Pushforward of `Q` under `dP/dQ`, and the Neyman–Pearson set `{dP/dQ ≤ c} ∩ S`
(with `S` a `ν`-conull set carrying no mass of the singular part of `μ`),
whose `μ`-mass is at most `c * ν {dP/dQ ≤ c} ≤ c`.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- The pushforward of `Q` under the Radon–Nikodym derivative `f = P.rnDeriv Q`
gives `Q {f < ε}` for the open down-set `Iio ε`. -/
lemma pushforward_rnDeriv_apply_Iio {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ProbabilityMeasure Ω) (ε : ℝ≥0∞) :
    (Q.map (fun x => (P : Measure Ω).rnDeriv (Q : Measure Ω) x)) (Iio ε) =
      Q {x | (P : Measure Ω).rnDeriv (Q : Measure Ω) x < ε} :=
  ProbabilityMeasure.map_apply Q
    ((Measure.measurable_rnDeriv (P : Measure Ω) (Q : Measure Ω)).aemeasurable)
    (measurableSet_Iio (a := ε))

/-- Neyman–Pearson set, sharp form: for any threshold `c` there is a measurable set `s` with
`μ s ≤ c * ν s` which has the same `ν`-mass as the likelihood-ratio level set
`{dμ/dν ≤ c}`. Only the Lebesgue decomposition of `μ` with respect to `ν` is needed. -/
lemma exists_neymanPearson_set_le_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν] (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c * ν s ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  have hms := μ.mutuallySingular_singularPart ν
  set t := {x | μ.rnDeriv ν x ≤ c} ∩ hms.nullSet
  have ht : MeasurableSet t :=
    (measurableSet_le (μ.measurable_rnDeriv ν) measurable_const).inter hms.measurableSet_nullSet
  refine ⟨t, ht, ?_, measure_inter_conull hms.measure_compl_nullSet⟩
  -- On `hms.nullSet` the singular part vanishes, so `μ t = ∫⁻ x in t, dμ/dν x ∂ν`.
  calc μ t = μ.singularPart ν t + ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
        conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
        rw [Measure.add_apply, withDensity_apply _ ht]
    _ = ∫⁻ x in t, μ.rnDeriv ν x ∂ν := by
        rw [measure_mono_null inter_subset_right hms.measure_nullSet, zero_add]
    _ ≤ ∫⁻ _ in t, c ∂ν := setLIntegral_mono measurable_const fun _ hx => hx.1
    _ = c * ν t := setLIntegral_const _ _

/-- General version for measures (Neyman–Pearson set). -/
lemma exists_neymanPearson_set {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [μ.HaveLebesgueDecomposition ν] [IsProbabilityMeasure ν]
    (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  obtain ⟨s, hs, hμ, hν⟩ := exists_neymanPearson_set_le_mul μ ν c
  exact ⟨s, hs, hμ.trans (mul_le_of_le_one_right' prob_le_one), hν⟩

end Statlib.Contiguity
