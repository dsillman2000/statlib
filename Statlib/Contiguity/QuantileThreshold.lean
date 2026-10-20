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

The measure-theoretic part is `MeasureTheory.tendsto_measure_iInter_atTop` (continuity from
above); the purely order-theoretic part is that the thresholds `c + 1/(n+1)` decrease to `c`.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- If `x ≤ c + 1/(n+1)` for every `n`, then `x ≤ c`.

This is the order-theoretic heart of the argument: the thresholds `c + 1/(n+1)` decrease to `c`,
so anything below all of them is below `c`. -/
lemma le_of_le_add_one_div_nat {x c : ℝ≥0∞}
    (h : ∀ n : ℕ, x ≤ c + 1 / (n + 1 : ℝ≥0∞)) : x ≤ c := by
  by_cases htop : c = ∞
  · rw [htop]
    exact le_top
  · by_contra hx
    have hxc : c < x := lt_of_not_ge hx
    have hd : 0 < x - c := tsub_pos_iff_lt.mpr hxc
    have hsub : ∀ n : ℕ, x - c ≤ 1 / (n + 1 : ℝ≥0∞) := by
      intro n
      rw [tsub_le_iff_left]
      exact h n
    -- `(x - c)⁻¹ < ∞`, so `(x - c)⁻¹ < m + 1` for some `m`, i.e. `1/(m+1) < x - c`
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ne_of_lt (ENNReal.inv_lt_top.mpr hd))
    have hm1 : (x - c)⁻¹ < (m + 1 : ℝ≥0∞) :=
      lt_of_lt_of_le hm (by exact_mod_cast (Nat.le_succ m))
    have hlt : 1 / (m + 1 : ℝ≥0∞) < x - c := by
      rw [one_div]
      exact ENNReal.inv_lt_iff_inv_lt.mp hm1
    exact (not_lt_of_ge (hsub m)) hlt

/-- Continuity from above at a quantile threshold.

If `η < Q {f < c + 1/(n+1)}` for every `n`, then
`η ≤ Q {f ≤ c}`. -/
lemma le_measure_le_of_lt_thresholds {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ≥0∞) (η c : ℝ≥0∞)
    (hf : Measurable f)
    (h : ∀ n : ℕ, η < ν {x | f x < c + 1 / (n + 1 : ℝ≥0∞)}) :
    η ≤ ν {x | f x ≤ c} := by
  -- the decreasing sequence of level sets `A n = {f ≤ c + 1/(n+1)}`
  let A : ℕ → Set Ω := fun n => {x | f x ≤ c + 1 / (n + 1 : ℝ≥0∞)}
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n => measurableSet_le hf measurable_const
  have hA_anti : Antitone A := by
    intro m n hmn x hx
    have h1 : (m + 1 : ℝ≥0∞) ≤ (n + 1 : ℝ≥0∞) := by exact_mod_cast (Nat.add_le_add_right hmn 1)
    have h2 : 1 / (n + 1 : ℝ≥0∞) ≤ 1 / (m + 1 : ℝ≥0∞) := by
      rw [one_div, one_div]
      exact ENNReal.inv_le_inv' h1
    have h3 : c + 1 / (n + 1 : ℝ≥0∞) ≤ c + 1 / (m + 1 : ℝ≥0∞) := by gcongr
    exact le_trans hx h3
  have hA_gt : ∀ n, η < ν (A n) := by
    intro n
    have hsub : {x | f x < c + 1 / (n + 1 : ℝ≥0∞)} ⊆ A n := by
      intro x hx
      have hx' : f x < c + 1 / (n + 1 : ℝ≥0∞) := by simpa using hx
      exact le_of_lt hx'
    exact lt_of_lt_of_le (h n) (ν.mono hsub)
  -- `ν` is a probability measure, so no `A n` has infinite measure
  have hne : ∃ i, ν (A i) ≠ ∞ := by
    refine ⟨0, ?_⟩
    have h1 : ν (A 0) ≤ ν Set.univ := ν.mono (Set.subset_univ (A 0))
    have h2 : ν Set.univ = 1 := IsProbabilityMeasure.measure_univ
    exact ne_of_lt (lt_of_le_of_lt (h2 ▸ h1) ENNReal.one_lt_top)
  -- continuity from above
  have htend : Tendsto (fun n => ν (A n)) atTop (𝓝 (ν (⋂ n, A n))) :=
    tendsto_measure_iInter_atTop (μ := ν) (fun n => (hA_meas n).nullMeasurableSet) hA_anti hne
  have hlimit : η ≤ ν (⋂ n, A n) := by
    apply ge_of_tendsto' htend
    intro n
    exact le_of_lt (hA_gt n)
  -- `⋂ n, A n = {f ≤ c}`
  have hsubset : (⋂ n, A n) ⊆ {x | f x ≤ c} := by
    intro x hx
    refine le_of_le_add_one_div_nat ?_
    intro n
    exact Set.mem_iInter.1 hx n
  exact le_trans hlimit (ν.mono hsubset)

end Statlib.Contiguity
