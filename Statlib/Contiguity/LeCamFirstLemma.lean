/-
Copyright (c) 2026 Statlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Statlib contributors
-/
module

public import Statlib.Contiguity.Def
public import Statlib.Contiguity.LikelihoodRatio
public import Statlib.Contiguity.PortmanteauBound
public import Statlib.Contiguity.QuantileThreshold

/-!
# Le Cam's first lemma: `Contiguous1 → Contiguous2`

Contrapositive proof assembled from the portmanteau, likelihood-ratio and quantile lemmas.
-/

@[expose] public section

open scoped Topology NNReal ENNReal
open Filter MeasureTheory Set ProbabilityMeasure

namespace Statlib.Contiguity

/-- `Contiguous1 → Contiguous2` (Le Cam's first lemma, contrapositive form). -/
theorem Contiguous1.contiguous2 {α : Type*} {Ω : α → Type*}
    [∀ a, MeasurableSpace (Ω a)] (l : Filter α)
    (P Q : ∀ a, ProbabilityMeasure (Ω a)) (hPQ : Contiguous1 l P Q) :
    Contiguous2 l P Q := by
  intro L h hle hne htend
  by_contra hL0
  -- η : ℝ≥0 with 0 < η < L {0}
  obtain ⟨η, hη0, hηL⟩ := exists_between (pos_iff_ne_zero.mpr hL0)
  -- Write `f a = dP a / dQ a`.
  set f : ∀ a, Ω a → ℝ≥0∞ := fun a => (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a))
  -- Lower bound transported to the `Q`-side: for every `ε > 0`, eventually `η < Q {f < ε}`.
  have hB : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ a in h,
      (η : ℝ≥0∞) < (Q a : Measure (Ω a)) {x | f a x < ε} := by
    intro ε hε
    filter_upwards [eventually_gt_measure_Iio_of_tendsto L _ htend (η : ℝ≥0∞)
      (ENNReal.coe_lt_coe.mpr hηL) ε hε] with a ha
    rwa [pushforward_rnDeriv_apply_Iio, ennreal_coeFn_eq_coeFn_toMeasure] at ha
  -- Quantile `c a` of the likelihood ratio at level `η`
  let c : α → ℝ≥0∞ := fun a => sInf {ε | (η : ℝ≥0∞) < (Q a : Measure (Ω a)) {x | f a x < ε}}
  -- `c a → 0` along `h`
  have hc_tend : Tendsto c h (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [hB ε hε] with a ha
    exact sInf_le ha
  -- Continuity from above: `η ≤ Q a {f a ≤ c a}`, eventually
  have hD : ∀ᶠ a in h, (η : ℝ≥0∞) ≤ (Q a : Measure (Ω a)) {x | f a x ≤ c a} := by
    filter_upwards [hB 1 one_pos] with a ha1
    exact le_measure_le_sInf (Q a : Measure (Ω a)) (f a) (η : ℝ≥0∞)
      (Measure.measurable_rnDeriv _ _) ⟨1, ha1⟩
  -- Neyman–Pearson sets `s a`: `P a (s a) ≤ c a` and `Q a (s a) = Q a {f a ≤ c a}`
  choose s hs_meas hs_P hs_Q using fun a =>
    exists_neymanPearson_set (P a : Measure (Ω a)) (Q a) (c a)
  -- `c a → 0` ⇒ `P a (s a) → 0` (in `ℝ≥0`)
  have hP_tend : Tendsto (fun a => (P a) (s a)) h (𝓝 0) := by
    rw [← ENNReal.tendsto_coe, ENNReal.coe_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc_tend
      (Eventually.of_forall (fun _ => (bot_le : (0 : ℝ≥0∞) ≤ _))) ?_
    exact Eventually.of_forall fun a => by
      rw [ennreal_coeFn_eq_coeFn_toMeasure]
      exact hs_P a
  -- `Contiguous1` (with the same `h ≤ l`) gives `Q a (s a) → 0` ...
  have hQ_tend := hPQ (s := s) (h := h) hs_meas hle hP_tend
  rw [← ENNReal.tendsto_coe, ENNReal.coe_zero] at hQ_tend
  -- ... but `Q a (s a) ≥ η > 0` eventually, which is incompatible with convergence to `0`.
  obtain ⟨a, ha_lt, ha_le⟩ :=
    ((hQ_tend.eventually (Iio_mem_nhds (ENNReal.coe_pos.mpr hη0))).and hD).exists
  rw [ennreal_coeFn_eq_coeFn_toMeasure, hs_Q] at ha_lt
  exact ha_le.not_gt ha_lt

end Statlib.Contiguity
