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

Pushforward of `Q` under `dP/dQ`, and the Neyman–Pearson set `{dP/dQ ≤ c} ∩ S`,
whose `P`-mass is at most `c`.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- The pushforward of `Q` under the Radon–Nikodym derivative `f = P.rnDeriv Q` under `Q`
gives `Q {f < ε}` for the open down-set `Iio ε`. -/
lemma pushforward_rnDeriv_apply_Iio {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ProbabilityMeasure Ω) (ε : ℝ≥0∞) (_hε : 0 < ε) :
    (Q.map (fun x => (P : Measure Ω).rnDeriv (Q : Measure Ω) x)) (Iio ε) =
      Q {x | (P : Measure Ω).rnDeriv (Q : Measure Ω) x < ε} := by
  let f := fun x => (P : Measure Ω).rnDeriv (Q : Measure Ω) x
  have hf : AEMeasurable f (Q : Measure Ω) :=
    (Measure.measurable_rnDeriv (P : Measure Ω) (Q : Measure Ω)).aemeasurable
  rw [ProbabilityMeasure.map_apply Q hf (measurableSet_Iio (a := ε))]
  rfl


/-- General version for measures (Neyman–Pearson set). -/
lemma exists_neymanPearson_set {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      μ s ≤ c ∧
      ν s = ν {x | μ.rnDeriv ν x ≤ c} := by
  set f := μ.rnDeriv ν
  have hf : Measurable f := Measure.measurable_rnDeriv μ ν
  have hms := Measure.mutuallySingular_singularPart μ ν
  set S := hms.nullSet
  have hS : MeasurableSet S := hms.measurableSet_nullSet
  have hsing : μ.singularPart ν S = 0 := hms.measure_nullSet
  have hνc : ν Sᶜ = 0 := hms.measure_compl_nullSet
  have hle : MeasurableSet {x | f x ≤ c} := measurableSet_le hf measurable_const
  refine ⟨{x | f x ≤ c} ∩ S, hle.inter hS, ?_, measure_inter_conull hνc⟩
  have key : μ.restrict S = (ν.restrict S).withDensity f := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]
    rw [Measure.restrict_add, Measure.restrict_eq_zero.2 hsing, zero_add, restrict_withDensity hS]
  calc μ ({x | f x ≤ c} ∩ S)
      = μ.restrict S ({x | f x ≤ c} ∩ S) := by
          rw [Measure.restrict_apply (hle.inter hS), Set.inter_assoc, Set.inter_self]
    _ = ∫⁻ x in {x | f x ≤ c} ∩ S, f x ∂ν := by
          rw [key, withDensity_apply _ (hle.inter hS), Measure.restrict_restrict (hle.inter hS),
            Set.inter_assoc, Set.inter_self]
    _ ≤ ∫⁻ _ in {x | f x ≤ c} ∩ S, c ∂ν := setLIntegral_mono measurable_const (fun x hx => hx.1)
    _ = c * ν ({x | f x ≤ c} ∩ S) := setLIntegral_const _ _
    _ ≤ c * 1 := by gcongr; exact prob_le_one
    _ = c := mul_one c

/-- Exact ProbabilityMeasure statement. -/
lemma exists_neymanPearson_set_prob {Ω : Type*} [MeasurableSpace Ω]
    (P Q : ProbabilityMeasure Ω) (c : ℝ≥0∞) :
    ∃ s : Set Ω, MeasurableSet s ∧
      (P : Measure Ω) s ≤ c ∧
      (Q : Measure Ω) s = (Q : Measure Ω) {x | (P : Measure Ω).rnDeriv (Q : Measure Ω) x ≤ c} := by
  exact exists_neymanPearson_set (P : Measure Ω) (Q : Measure Ω) c

end Statlib.Contiguity
