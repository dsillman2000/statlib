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
  have hL0pos : 0 < L {0} := pos_iff_ne_zero.mpr hL0
  let η : ℝ≥0 := L {0} / 2
  have hη0 : 0 < η := half_pos hL0pos
  have hηL : η < L {0} := half_lt_self hL0pos
  -- Lower bound transported to the `Q`-side: for every `ε > 0`, eventually `η < Q {f < ε}`.
  let μs : α → ProbabilityMeasure (ℝ≥0∞) := fun a =>
    (Q a).map (fun x => (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a)) x)
  have hB : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ a in h,
      (η : ℝ≥0∞) < (Q a) {x | (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a)) x < ε} := by
    intro ε hε
    filter_upwards [eventually_gt_measure_Iio_of_tendsto L μs htend (η : ℝ≥0∞)
      (ENNReal.coe_lt_coe.mpr hηL) ε hε] with a ha
    rw [pushforward_rnDeriv_apply_Iio (P a) (Q a) ε hε] at ha
    exact ha
  -- Quantile c a
  let c : α → ℝ≥0∞ := fun a =>
    sInf {ε : ℝ≥0∞ | 0 < ε ∧
      (η : ℝ≥0∞) < (Q a) {x | (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a)) x < ε}}
  -- c a → 0 along h
  have hc_tend : Tendsto c h (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [hB ε hε] with a ha
    exact sInf_le ⟨hε, ha⟩
  -- Continuity from above: η ≤ Q a {f a ≤ c a}, eventually
  have hD : ∀ᶠ a in h, (η : ℝ≥0∞) ≤
      (Q a : Measure (Ω a)) {x | (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a)) x ≤ c a} := by
    filter_upwards [hB 1 one_pos] with a ha1
    have hcfin : c a < ∞ := lt_of_le_of_lt (sInf_le ⟨one_pos, ha1⟩) ENNReal.one_lt_top
    refine le_measure_le_of_lt_thresholds (Q a : Measure (Ω a)) _ (η : ℝ≥0∞) (c a)
      (Measure.measurable_rnDeriv _ _) hcfin fun n => ?_
    have hlt : c a < c a + 1 / (n + 1 : ℝ≥0∞) :=
      ENNReal.lt_add_right hcfin.ne (by simp)
    obtain ⟨ε, ⟨-, hεη⟩, hεlt⟩ := sInf_lt_iff.1 hlt
    have hcoerce : (η : ℝ≥0∞) <
        (Q a : Measure (Ω a)) {x | (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a)) x < ε} := by
      rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hεη
      exact hεη
    exact hcoerce.trans_le ((Q a : Measure (Ω a)).mono (fun x (hx : _ < ε) => hx.trans hεlt))
  -- Neyman–Pearson sets s a
  let s : ∀ a, Set (Ω a) := fun a =>
    (exists_neymanPearson_set_prob (P a) (Q a) (c a)).choose
  have hs_meas : ∀ a, MeasurableSet (s a) := fun a =>
    (exists_neymanPearson_set_prob (P a) (Q a) (c a)).choose_spec.1
  have hs_P : ∀ᶠ a in h, (P a : Measure (Ω a)) (s a) ≤ c a :=
    Eventually.of_forall fun a =>
      (exists_neymanPearson_set_prob (P a) (Q a) (c a)).choose_spec.2.1
  have hs_Q : ∀ a, (Q a : Measure (Ω a)) (s a) =
      (Q a : Measure (Ω a)) {x | (P a : Measure (Ω a)).rnDeriv (Q a : Measure (Ω a)) x ≤ c a} :=
    fun a => (exists_neymanPearson_set_prob (P a) (Q a) (c a)).choose_spec.2.2
  -- Lower bound, measure level, then transported to ℝ≥0
  have hs_Q_eta : ∀ᶠ a in h, (η : ℝ≥0∞) ≤ (Q a : Measure (Ω a)) (s a) := by
    filter_upwards [hD] with a ha
    rw [hs_Q a]
    exact ha
  have hs_Q_nn : ∀ᶠ a in h, η ≤ (Q a) (s a) := by
    filter_upwards [hs_Q_eta] with a ha
    apply ENNReal.coe_le_coe.mp
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ha
  -- c a → 0 ⇒ P s a → 0 (in ℝ≥0)
  have hP_tend : Tendsto (fun a => (P a) (s a)) h (𝓝 0) := by
    rw [← ENNReal.tendsto_coe, ENNReal.coe_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc_tend
      (Eventually.of_forall (fun _ => (bot_le : (0 : ℝ≥0∞) ≤ _))) ?_
    filter_upwards [hs_P] with a ha
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ha
  -- Contiguous1 (with the same h ≤ l) gives Q s a → 0
  have hQ_tend : Tendsto (fun a => (Q a) (s a)) h (𝓝 0) :=
    hPQ (s := s) (h := h) hs_meas hle hP_tend
  -- But Q s a ≥ η > 0 eventually, which is incompatible with convergence to 0
  have hcontra : ¬ Tendsto (fun a => (Q a) (s a)) h (𝓝 0) := by
    intro hT
    obtain ⟨a, ha_lt, ha_le⟩ :=
      ((hT.eventually (Iio_mem_nhds hη0)).and hs_Q_nn).exists
    exact lt_irrefl _ (ha_le.trans_lt ha_lt)
  exact hcontra hQ_tend

end Statlib.Contiguity
