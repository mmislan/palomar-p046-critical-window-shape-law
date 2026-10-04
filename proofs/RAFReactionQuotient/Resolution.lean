module

public import proofs.RAFReactionQuotient.CriticalLimit
public import proofs.RAFReactionQuotient.SourceParameters
public import proofs.RAFReactionQuotient.CatalogueBridge
public import proofs.RAFReactionQuotient.SurvivalPositive
public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayConditionedBulk

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source OverlapCorrectedRAF.Asymptotic
open scoped ENNReal Topology

noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩

/-- Probability of infinite ordinary reversible closure in the canonical
repository-channel iid field, with all six food molecules. -/
noncomputable def quotientTransitionLimit (lambda : ℝ) (hlambda : 0 < lambda) : ℝ :=
  (quotientSurvival (criticalOpenness lambda hlambda)).toReal

theorem repository_critical_window {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (repositoryRAFBernoulliProbability f) atTop (𝓝 (quotientTransitionLimit lambda hlambda)) := by
  obtain ⟨hp,hm⟩ := quotientParameter_limits f hlambda hf
  have ht := quotient_critical_limit (quotientParameter f) hlambda hp hm (criticalOpenness lambda hlambda) rfl
  have hfinite : quotientSurvival (criticalOpenness lambda hlambda) ≠ ⊤ := by
    unfold quotientSurvival
    exact measure_ne_top _ _
  have hr := (ENNReal.tendsto_toReal hfinite).comp ht
  apply hr.congr'
  filter_upwards [quotientParameter_eventually_exact f hlambda hf] with n hn
  dsimp only [Function.comp_def]
  rw [quotient_probability_eq_catalogue,hn]
  rfl

theorem repository_gateway_critical_window {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => repositoryGatewayOpenProbability (repositoryCatalysisP (f n) n) n)
      atTop (𝓝 (1-Real.exp (-34*lambda))) := by
  obtain ⟨hp,hm⟩ := quotientParameter_limits f hlambda hf
  have hmass : Tendsto (fun n => (quotientParameter f n : ℝ)*repositoryGatewayCoordinateCount n)
      atTop (𝓝 (34*lambda)) := by
    have ht := hm.const_mul 34
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    simp only [repositoryGatewayCoordinateCount,card_repository_gateway_binary_t2,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have ht := generic_pool_limit (quotientParameter f) repositoryGatewayCoordinateCount hp
    (generic_pool_nonzero _ hlambda hm) hmass
  rw [neg_mul]
  apply ht.congr'
  filter_upwards [quotientParameter_eventually_exact f hlambda hf] with n hn
  simp only [fixedPoolParameter_coe,hn,repositoryGatewayOpenProbability,
    RAF.Corrected.atLeastOneProbability,RAF.Probability.allAbsentProbability_eq_pow]

theorem repository_bulk_factor_critical_window {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => repositoryGatewayConditionedBulkProbability (repositoryCatalysisP (f n) n) n)
      atTop (𝓝 (quotientTransitionLimit lambda hlambda/(1-Real.exp (-34*lambda)))) := by
  have hden : 1-Real.exp (-34*lambda) ≠ 0 := by
    have he := Real.exp_lt_one_iff.mpr (show -34*lambda < 0 by linarith)
    linarith
  exact (repository_critical_window hlambda hf).div (repository_gateway_critical_window hlambda hf) hden

theorem quotientTransitionLimit_positive {lambda : ℝ} (hlambda : 0 < lambda) :
    0 < quotientTransitionLimit lambda hlambda := by
  apply ENNReal.toReal_pos
  · exact ne_of_gt (quotientSurvival_pos _ (by
      change 0 < 1-Real.exp (-lambda)
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))))
  · unfold quotientSurvival
    exact measure_ne_top _ _

/-- Source-facing resolution. The only assumptions are the positive limiting
intensity and f_n/n convergence. The finite RAF catalogue, canonical infinite
survival law, and gateway-conditioned factor are the actual source objects. -/
theorem reaction_quotient_critical_window_resolution {f : ℕ → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hf : Tendsto (fun n => f n/(n : ℝ)) atTop (𝓝 lambda)) :
    (∀ᶠ n in atTop, (quotientParameter f n : ℝ) = f n/Fintype.card (RepositoryChannel n)) ∧
    Tendsto (repositoryRAFBernoulliProbability f) atTop (𝓝 (quotientTransitionLimit lambda hlambda)) ∧
    0 < quotientTransitionLimit lambda hlambda ∧
    Tendsto (fun n => repositoryGatewayConditionedBulkProbability (repositoryCatalysisP (f n) n) n)
      atTop (𝓝 (quotientTransitionLimit lambda hlambda/(1-Real.exp (-34*lambda)))) := by
  exact ⟨quotientParameter_eventually_exact f hlambda hf,repository_critical_window hlambda hf,
    quotientTransitionLimit_positive hlambda,repository_bulk_factor_critical_window hlambda hf⟩

end RAFReactionQuotient
