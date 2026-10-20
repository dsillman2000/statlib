/-
Copyright (c) 2026 Statlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlib contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Portmanteau-type lower bounds for weak limits

If `μs → L` weakly and `η < L {0}`, then eventually `η < μs a (Iio ε)` for every `ε > 0`.

This is the open-set case of the portmanteau theorem: `Iio ε` is open and contains `{0}`, so
`L {0} ≤ L (Iio ε) ≤ liminfᵢ μsᵢ (Iio ε)`, and a strictly smaller threshold is therefore
eventually exceeded.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- Weak-limit lower bound on `μs a s` for an open set `s`: if `η < L s`, then eventually
`η < μs a s`.  This is the open-set case of the portmanteau theorem. -/
lemma eventually_gt_measure_open_of_tendsto {α : Type*} {h : Filter α}
    (L : ProbabilityMeasure (ℝ≥0∞)) (μs : α → ProbabilityMeasure (ℝ≥0∞))
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (s : Set ℝ≥0∞) (hs : IsOpen s)
    (hη : η < L s) :
    ∀ᶠ a in h, η < μs a s := by
  -- Portmanteau, open sets: `L s ≤ liminf (μs a s)`.
  have hlim : (L : Measure ℝ≥0∞) s ≤ h.liminf (fun a ↦ (μs a : Measure ℝ≥0∞) s) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμs hs
  have hη' : η < (L : Measure ℝ≥0∞) s := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact hη
  -- `η < liminf (μs a s)` forces `η < μs a s` eventually.
  have hev : ∀ᶠ a in h, η < (μs a : Measure ℝ≥0∞) s :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hη' hlim)
  filter_upwards [hev] with a ha
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at ha
  exact ha

/-- Weak-limit lower bound on `μ (Iio ε)` for any threshold `ε > 0`. -/
lemma eventually_gt_measure_Iio_of_tendsto {α : Type*} {h : Filter α}
    (L : ProbabilityMeasure (ℝ≥0∞)) (μs : α → ProbabilityMeasure (ℝ≥0∞))
    (hμs : Tendsto μs h (𝓝 L)) (η : ℝ≥0∞) (hη : η < L {0})
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∀ᶠ a in h, η < μs a (Iio ε) := by
  -- `{0} ⊆ Iio ε`, hence `L {0} ≤ L (Iio ε)`.
  have hL0 : L {0} ≤ L (Iio ε) := ProbabilityMeasure.apply_mono L (fun x hx => hx ▸ hε)
  refine eventually_gt_measure_open_of_tendsto L μs hμs η (Iio ε) isOpen_Iio ?_
  exact lt_of_lt_of_le hη (ENNReal.coe_le_coe.mpr hL0)

end Statlib.Contiguity
