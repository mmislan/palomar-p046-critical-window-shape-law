module

public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayProbability
public import proofs.OverlapCorrectedRAF.Source.ChannelLowerBound
public import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

@[expose] public section

namespace OverlapCorrectedRAF.Asymptotic

open Filter Topology
open RAF.Polymer
open OverlapCorrectedRAF.Source

/-- The source simulation's uniform catalysis parameter: expected catalysis
`f` per molecule divided by the number of reversible repository channels. -/
noncomputable def repositoryCatalysisP (f : ℝ) (n : Nat) : ℝ :=
  f / Fintype.card (RepositoryChannel n)

/-- The literal Bernoulli probability of an actual repository RAF, obtained
from the exhaustive finite support catalogue rather than introduced as an
unconstrained probability sequence. -/
noncomputable def repositoryRAFBernoulliProbability
    (f : Nat → ℝ) (n : Nat) : ℝ :=
  Overlap.rafBernoulliProbability (repositoryCatalysisP (f n) n)
    Finset.univ (repositoryCoreSupports n 2) (repositorySupportRequirements n 2)

theorem repositoryCatalysisP_nonneg {f : ℝ} (hf : 0 ≤ f) (n : Nat) :
    0 ≤ repositoryCatalysisP f n := by
  exact div_nonneg hf (by positivity)

theorem repositoryCatalysisP_le_one
    {n : Nat} (hn : 3 ≤ n) {f : ℝ}
    (hfChannels : f ≤ Fintype.card (RepositoryChannel n)) :
    repositoryCatalysisP f n ≤ 1 := by
  have hmNat : 0 < (n - 1) / 2 := by omega
  have hJposNat : 0 < Fintype.card (RepositoryChannel n) :=
    lt_of_lt_of_le (Nat.mul_pos hmNat (pow_pos (by norm_num) _))
      (repositoryChannel_card_lower hn)
  have hJpos : (0 : ℝ) < Fintype.card (RepositoryChannel n) := by
    exact_mod_cast hJposNat
  rw [repositoryCatalysisP, div_le_one hJpos]
  exact_mod_cast hfChannels

theorem repositoryRAFBernoulliProbability_nonneg
    (f : Nat → ℝ) {n : Nat} (hf : 0 ≤ f n) (hn : 3 ≤ n)
    (hfChannels : f n ≤ Fintype.card (RepositoryChannel n)) :
    0 ≤ repositoryRAFBernoulliProbability f n := by
  rw [repositoryRAFBernoulliProbability,
    repository_rafBernoulliProbability_eq_actual_raf_mass]
  exact Finset.sum_nonneg fun config _ =>
    jointFibreBernoulliWeight_nonneg (repositoryCatalysisP_nonneg hf n)
      (repositoryCatalysisP_le_one hn hfChannels) Finset.univ config

theorem repositoryRAFBernoulliProbability_le_gateway
    (f : Nat → ℝ) {n : Nat} (hf : 0 ≤ f n) (hn : 3 ≤ n)
    (hfChannels : f n ≤ Fintype.card (RepositoryChannel n)) :
    repositoryRAFBernoulliProbability f n ≤
      repositoryGatewayOpenProbability (repositoryCatalysisP (f n) n) n := by
  exact Source.repositoryRAFBernoulliProbability_le_gateway
    (repositoryCatalysisP_nonneg hf n)
    (repositoryCatalysisP_le_one hn hfChannels) (by omega)

/-- Quantitative source-specific gateway estimate.  The constant is deliberately
coarse: the proof uses only the direct strict-left channel family, not the full
primitive-root correction formula. -/
theorem repositoryGatewayOpenProbability_le_sublinearScale
    {n : Nat} (hn : 3 ≤ n) {f : ℝ} (hf : 0 ≤ f)
    (hfChannels : f ≤ Fintype.card (RepositoryChannel n)) :
    repositoryGatewayOpenProbability (repositoryCatalysisP f n) n ≤
      272 * (f / n) := by
  let X : ℝ := (2 ^ (n + 1) - 2 : Nat)
  let J : ℝ := Fintype.card (RepositoryChannel n)
  let m : ℝ := ((n - 1) / 2 : Nat)
  let P : ℝ := (2 ^ n : Nat)
  have hmNat : 0 < (n - 1) / 2 := by omega
  have hJnat := repositoryChannel_card_lower hn
  have hJposNat : 0 < Fintype.card (RepositoryChannel n) :=
    lt_of_lt_of_le (Nat.mul_pos hmNat (pow_pos (by norm_num) _)) hJnat
  have hJpos : 0 < J := by
    dsimp [J]
    exact_mod_cast hJposNat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hJlower : m * P ≤ J := by
    dsimp [m, P, J]
    exact_mod_cast hJnat
  have hXnat : 2 ^ (n + 1) - 2 ≤ 2 * 2 ^ n := by
    rw [pow_succ]
    omega
  have hX : X ≤ 2 * P := by
    dsimp [X, P]
    exact_mod_cast hXnat
  have hnmNat : n ≤ 4 * ((n - 1) / 2) := by omega
  have hnm : (n : ℝ) ≤ 4 * m := by
    dsimp [m]
    exact_mod_cast hnmNat
  have hnx : (n : ℝ) * X ≤ 8 * J := by
    calc
      (n : ℝ) * X ≤ (n : ℝ) * (2 * P) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      _ ≤ (4 * m) * (2 * P) :=
        mul_le_mul_of_nonneg_right hnm (by positivity)
      _ = 8 * (m * P) := by ring
      _ ≤ 8 * J := mul_le_mul_of_nonneg_left hJlower (by norm_num)
  have hratio : X / J ≤ 8 / (n : ℝ) := by
    rw [div_le_div_iff₀ hJpos hnpos]
    nlinarith
  have hp_le : repositoryCatalysisP f n ≤ 1 := by
    rw [repositoryCatalysisP, div_le_one hJpos]
    simpa [J] using hfChannels
  have hcap := repositoryGatewayOpenProbability_le hp_le n
  calc
    repositoryGatewayOpenProbability (repositoryCatalysisP f n) n ≤
        ((2 ^ (n + 1) - 2) * 34 : Nat) * repositoryCatalysisP f n := hcap
    _ = 34 * f * (X / J) := by
      simp only [repositoryCatalysisP, X, J, Nat.cast_mul, Nat.cast_ofNat]
      ring
    _ ≤ 34 * f * (8 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 272 * (f / n) := by ring

/-- Source-faithful negative resolution of a constant-`f` asymptotic threshold:
whenever `f_n = o(n)`, any RAF probability dominated by the literal repository
gateway event tends to zero. -/
theorem sublinear_catalysis_forces_raf_vanishing
    (f rafProbability : Nat → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hfChannels : ∀ n, f n ≤ Fintype.card (RepositoryChannel n))
    (hsublinear : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0))
    (hrafNonneg : ∀ n, 0 ≤ rafProbability n)
    (hcontain : ∀ n, rafProbability n ≤
      repositoryGatewayOpenProbability (repositoryCatalysisP (f n) n) n) :
    Tendsto rafProbability atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall hrafNonneg)
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact (hcontain n).trans
      (repositoryGatewayOpenProbability_le_sublinearScale hn (hf n) (hfChannels n))
  · simpa using tendsto_const_nhds.mul hsublinear

/-- Fully instantiated source theorem: sublinear expected catalysis forces the
actual, exhaustively enumerated repository RAF probability to vanish. -/
theorem sublinear_catalysis_forces_actual_repository_raf_vanishing
    (f : Nat → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hfChannels : ∀ n, f n ≤ Fintype.card (RepositoryChannel n))
    (hsublinear : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (repositoryRAFBernoulliProbability f) atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact repositoryRAFBernoulliProbability_nonneg f (hf n) hn (hfChannels n)
  · filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact (repositoryRAFBernoulliProbability_le_gateway f (hf n) hn
      (hfChannels n)).trans
        (repositoryGatewayOpenProbability_le_sublinearScale hn (hf n)
          (hfChannels n))
  · simpa using tendsto_const_nhds.mul hsublinear

end OverlapCorrectedRAF.Asymptotic
