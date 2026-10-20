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
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- Continuity from above at a quantile threshold.

If `η < Q {f < c + 1/(n+1)}` for every `n`, then
`η ≤ Q {f ≤ c}`. -/
lemma le_measure_le_of_lt_thresholds {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ≥0∞) (η c : ℝ≥0∞)
    (hf : Measurable f) (hc : c < ∞)
    (h : ∀ n : ℕ, η < ν {x | f x < c + 1 / (n + 1 : ℝ≥0∞)}) :
    η ≤ ν {x | f x ≤ c} := by
  let A : ℕ → Set Ω := fun n => {x | f x ≤ c + 1 / (n + 1 : ℝ≥0∞)}
  have hA_meas : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le hf measurable_const
  have hA_anti : Antitone A := by
    intro m n hmn x hx
    have h1 : (m + 1 : ℝ≥0∞) ≤ (n + 1 : ℝ≥0∞) := by exact_mod_cast (Nat.add_le_add_right hmn 1)
    have h2 : (n + 1 : ℝ≥0∞)⁻¹ ≤ (m + 1 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv' h1
    have h3 : (1 : ℝ≥0∞) / (n + 1 : ℝ≥0∞) ≤ (1 : ℝ≥0∞) / (m + 1 : ℝ≥0∞) := by
      simpa [one_div] using h2
    have h4 : c + 1 / (n + 1 : ℝ≥0∞) ≤ c + 1 / (m + 1 : ℝ≥0∞) := by gcongr
    exact le_trans hx h4
  have hA_gt : ∀ n, η < ν (A n) := by
    intro n
    have hlt : {x | f x < c + 1 / (n + 1 : ℝ≥0∞)} ⊆ A n := by
      intro x hx
      have hx' : f x < c + 1 / (n + 1 : ℝ≥0∞) := by simpa using hx
      exact le_of_lt hx'
    have hνlt : ν {x | f x < c + 1 / (n + 1 : ℝ≥0∞)} ≤ ν (A n) :=
      ν.mono hlt
    exact lt_of_lt_of_le (h n) hνlt
  have hne : ∃ i, ν (A i) ≠ ∞ := by
    refine ⟨0, ?_⟩
    have hle : ν (A 0) ≤ ν Set.univ := ν.mono (Set.subset_univ (A 0))
    have huniv : ν Set.univ = 1 := IsProbabilityMeasure.measure_univ
    have : ν (A 0) ≤ 1 := huniv ▸ hle
    exact ne_of_lt (lt_of_le_of_lt this ENNReal.one_lt_top)
  have htend : Tendsto (fun n => ν (A n)) atTop
      (𝓝 (ν (⋂ n, A n))) :=
    tendsto_measure_iInter_atTop (μ := ν) (fun n => (hA_meas n).nullMeasurableSet) hA_anti hne
  have hlimit : η ≤ ν (⋂ n, A n) := by
    apply ge_of_tendsto' htend
    intro n
    exact le_of_lt (hA_gt n)
  have hsubset : (⋂ n, A n) ⊆ {x | f x ≤ c} := by
    intro x hx
    by_contra hgt
    have hcx : c < f x := lt_of_not_ge hgt
    -- if f x = ∞, then x ∉ A 0
    by_cases hfx : f x = ∞
    · have : x ∉ A 0 := by
        simp [A, hfx]
        -- c + 1 ≤ ∞ is true, so f x ≤ c+1 is ∞ ≤ c+1 which is false
        have : ¬ (∞ ≤ c + 1) := by
          -- c finite (hc), so c+1 < ∞
          have hc1 : c + 1 < ∞ := ENNReal.add_lt_top.mpr ⟨hc, ENNReal.one_lt_top⟩
          exact not_le_of_gt hc1
        simpa [hfx] using this
      exact this (Set.mem_iInter.1 hx 0)
    · -- f x finite > c: use exists_nat_gt
      have hd : 0 < f x - c := tsub_pos_iff_lt.mpr hcx
      have hd_finite : f x - c ≠ ∞ := by
        exact ne_of_lt (lt_of_le_of_lt tsub_le_self (lt_top_iff_ne_top.mpr hfx))
      obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.inv_ne_top.mpr (ne_of_gt hd))
      -- hm : (f x - c)⁻¹ < m, so 1/m < f x - c, so 1/(m+1) < f x - c
      have h1 : (m + 1 : ℝ≥0∞)⁻¹ < f x - c := by
        have hm' : (f x - c)⁻¹ < (m + 1 : ℝ≥0∞) :=
          lt_of_lt_of_le hm (by exact_mod_cast (Nat.le_succ m))
        exact ENNReal.inv_lt_iff_inv_lt.mp hm'
      have h2 : f x > c + (m + 1 : ℝ≥0∞)⁻¹ := by
        exact (lt_tsub_iff_left).mp h1
      have : x ∉ A m := by
        simp only [one_div, mem_ofPred_eq, not_le, A]
        exact h2
      exact this (Set.mem_iInter.1 hx m)
  exact le_trans hlimit (ν.mono hsubset)

end Statlib.Contiguity
