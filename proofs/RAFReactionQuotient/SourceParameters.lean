module

public import proofs.RAFReactionQuotient.PoolLimits
public import proofs.OverlapCorrectedRAF.Asymptotic.SublinearCatalysis

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter unitInterval HordijkSteelThreshold RAF.Polymer OverlapCorrectedRAF.Source
open OverlapCorrectedRAF.Asymptotic
open scoped Topology

noncomputable def quotientParameter (f : ℕ → ℝ) (n : ℕ) : I :=
  ⟨min 1 (max 0 (repositoryCatalysisP (f n) n)), by
    exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩⟩

theorem repository_raw_mass (f : ℕ → ℝ) {lambda : ℝ}
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => repositoryCatalysisP (f n) n * Fintype.card (Molecule n)) atTop (𝓝 lambda) := by
  have ht := hf.mul quotient_normalization
  simp only [mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  dsimp only [repositoryCatalysisP]
  field_simp

theorem repository_raw_zero (f : ℕ → ℝ) {lambda : ℝ}
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => repositoryCatalysisP (f n) n) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (Fintype.card (Molecule n) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp card_molecule_tendsto_atTop)
  have ht := (repository_raw_mass f hf).mul hi
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [card_molecule_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hU : (Fintype.card (Molecule n) : ℝ) ≠ 0 := by exact_mod_cast (by omega : Fintype.card (Molecule n) ≠ 0)
  field_simp

theorem quotientParameter_eventually_exact (f : ℕ → ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 lambda)) :
    ∀ᶠ n in atTop, (quotientParameter f n : ℝ) = repositoryCatalysisP (f n) n := by
  filter_upwards [(repository_raw_mass f hf).eventually_const_lt hlambda,
    (repository_raw_zero f hf).eventually_lt_const zero_lt_one] with n hpos hlt
  have hn : 0 ≤ repositoryCatalysisP (f n) n := by
    have hc : (0 : ℝ) ≤ Fintype.card (Molecule n) := Nat.cast_nonneg _
    by_contra h
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge h)) hc
    exact (not_lt_of_ge hh) hpos
  simp [quotientParameter,max_eq_right hn,min_eq_right hlt.le]

theorem quotientParameter_limits (f : ℕ → ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (hf : Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 lambda)) :
    Tendsto (fun n => (quotientParameter f n : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n => (quotientParameter f n : ℝ)*Fintype.card (Molecule n)) atTop (𝓝 lambda) := by
  have he := quotientParameter_eventually_exact f hlambda hf
  constructor
  · apply (repository_raw_zero f hf).congr'
    filter_upwards [he] with n hn
    exact hn.symm
  · apply (repository_raw_mass f hf).congr'
    filter_upwards [he] with n hn
    rw [hn]

end RAFReactionQuotient
