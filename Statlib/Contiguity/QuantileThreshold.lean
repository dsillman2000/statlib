/-
Copyright (c) 2026 Statlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Continuity from above at a quantile threshold

If `η < ν {f < c + 1/(n+1)}` for all `n`, then `η ≤ ν {f ≤ c}`.

The measure-theoretic part is `Antitone.measure_iInter` (continuity from above); the purely
order-theoretic part is that the thresholds `c + 1/(n+1)` decrease to `c`.

As a consequence, the lower quantile `sInf {ε | η < ν {f < ε}}` is attained in the sense that
`η ≤ ν {f ≤ sInf {ε | η < ν {f < ε}}}` (`le_measure_le_sInf`).
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- If `x ≤ c + 1/(n+1)` for every `n`, then `x ≤ c`.

The thresholds `c + 1/(n+1)` tend to `c`, so anything below all of them is below `c`. -/
lemma le_of_le_add_one_div_nat {x c : ℝ≥0∞}
    (h : ∀ n : ℕ, x ≤ c + 1 / (n + 1 : ℝ≥0∞)) : x ≤ c := by
  have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ≥0∞) + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  exact ge_of_tendsto' (by simpa using tendsto_const_nhds.add h0) h

/-- Continuity from above at a quantile threshold.

If `η < ν {f < c + 1/(n+1)}` for every `n`, then `η ≤ ν {f ≤ c}`. -/
lemma le_measure_le_of_lt_thresholds {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ≥0∞) (η c : ℝ≥0∞)
    (hf : Measurable f)
    (h : ∀ n : ℕ, η < ν {x | f x < c + 1 / (n + 1 : ℝ≥0∞)}) :
    η ≤ ν {x | f x ≤ c} := by
  -- the decreasing sequence of level sets `A n = {f ≤ c + 1/(n+1)}`
  let A : ℕ → Set Ω := fun n => {x | f x ≤ c + 1 / (n + 1 : ℝ≥0∞)}
  have hA_anti : Antitone A := fun m n hmn x (hx : f x ≤ _) => hx.trans (by gcongr)
  -- continuity from above: `ν (⋂ n, A n) = ⨅ n, ν (A n)`
  have hlim : ν (⋂ n, A n) = ⨅ n, ν (A n) :=
    hA_anti.measure_iInter (fun n => (measurableSet_le hf measurable_const).nullMeasurableSet)
      ⟨0, measure_ne_top ν _⟩
  -- `⋂ n, A n ⊆ {f ≤ c}`
  have hsubset : (⋂ n, A n) ⊆ {x | f x ≤ c} := fun x hx =>
    le_of_le_add_one_div_nat fun n => Set.mem_iInter.1 hx n
  calc η ≤ ν (⋂ n, A n) :=
        hlim ▸ le_iInf fun n => (h n).le.trans (measure_mono fun x (hx : f x < _) => hx.le)
    _ ≤ ν {x | f x ≤ c} := measure_mono hsubset

/-- The lower quantile `sInf {ε | η < ν {f < ε}}` is attained:
`η ≤ ν {f ≤ sInf {ε | η < ν {f < ε}}}`, as soon as the defining set is nonempty. -/
lemma le_measure_le_sInf {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ≥0∞) (η : ℝ≥0∞)
    (hf : Measurable f) (hne : ∃ ε, η < ν {x | f x < ε}) :
    η ≤ ν {x | f x ≤ sInf {ε | η < ν {x | f x < ε}}} := by
  set c := sInf {ε | η < ν {x | f x < ε}}
  obtain ⟨ε₀, hε₀⟩ := hne
  by_cases hc : c = ∞
  · -- the defining set is nonempty, so `η < ν {f < ε₀} ≤ ν {f ≤ ∞}`
    simpa [hc] using hε₀.le.trans (measure_mono (subset_univ _))
  refine le_measure_le_of_lt_thresholds ν f η c hf fun n => ?_
  obtain ⟨ε, hεη, hεlt⟩ := sInf_lt_iff.1 (ENNReal.lt_add_right hc (by simp) :
    c < c + 1 / (n + 1 : ℝ≥0∞))
  exact hεη.trans_le (measure_mono fun x (hx : f x < ε) => hx.trans hεlt)

end Statlib.Contiguity
