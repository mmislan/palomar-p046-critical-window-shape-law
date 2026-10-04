module

public import proofs.RAFReactionQuotient.CountLoss
public import proofs.HordijkSteelThreshold.GatewayProbability

@[expose] public section

namespace RAFReactionQuotient
open Classical Filter RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold
open scoped Topology

theorem short_count_scaled_le {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card (Molecule ((n-1)/2))*2^((n-1)/2) ≤ Fintype.card (Molecule n) := by
  let h := (n-1)/2
  have hexp : 2*h+1 ≤ n := by dsimp [h]; omega
  have hp : 2 ≤ 2^n := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    simpa using hh
  rw [card_molecules_exact,card_molecules_exact]
  calc
    (2^(h+1)-2)*2^h ≤ 2^(h+1)*2^h := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = 2^(2*h+1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < 2) hexp
    _ ≤ 2^(n+1)-2 := by rw [pow_succ]; omega

theorem loss_scaled_le (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (DeletedChannel n)*2^((n-1)/2) ≤ n*Fintype.card (Molecule n) := by
  have hd : Fintype.card (DeletedChannel n) ≤ n*Fintype.card (Molecule ((n-1)/2)) := by
    simpa only [card_molecules_exact] using deleted_card_bound n
  calc
    _ ≤ (n*Fintype.card (Molecule ((n-1)/2)))*2^((n-1)/2) := Nat.mul_le_mul_right _ hd
    _ = n*(Fintype.card (Molecule ((n-1)/2))*2^((n-1)/2)) := Nat.mul_assoc _ _ _
    _ ≤ _ := Nat.mul_le_mul_left n (short_count_scaled_le hn)

theorem loss_ratio_tendsto_zero :
    Tendsto (fun n => (Fintype.card (DeletedChannel n) : ℝ)/
      ((n : ℝ)*Fintype.card (Molecule n))) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => (n-1)/2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2*b+1)] with n hn
    omega
  have hg : Tendsto (fun n : ℕ => (1/2 : ℝ)^((n-1)/2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num)).comp hh
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hg
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hU : 0 < Fintype.card (Molecule n) := by
    rw [card_molecules_exact]
    have hp : 2 ≤ 2^n := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn
    rw [pow_succ]
    omega
  have hden : 0 < (n : ℝ)*Fintype.card (Molecule n) := by positivity
  have hp : 0 < (2 : ℝ)^((n-1)/2) := by positivity
  rw [one_div_pow]
  apply (div_le_div_iff₀ hden hp).mpr
  simpa only [one_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    (show (Fintype.card (DeletedChannel n) : ℝ)*(2 : ℝ)^((n-1)/2) ≤
      (n : ℝ)*Fintype.card (Molecule n) by exact_mod_cast loss_scaled_le n hn)

theorem quotient_normalization :
    Tendsto (fun n : ℕ => (n : ℝ)*Fintype.card (Molecule n)/Fintype.card (RepositoryChannel n))
      atTop (𝓝 1) := by
  have hr : Tendsto (fun n => (Fintype.card (Reaction n) : ℝ)/
      ((n : ℝ)*Fintype.card (Molecule n))) atTop (𝓝 1) := by
    have ht := (rawCatalysisP_mul_card_molecule_tendsto 1).inv₀ (by norm_num)
    simpa [rawCatalysisP,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using ht
  have hj : Tendsto (fun n => (Fintype.card (RepositoryChannel n) : ℝ)/
      ((n : ℝ)*Fintype.card (Molecule n))) atTop (𝓝 1) := by
    have ht := hr.sub loss_ratio_tendsto_zero
    simp only [sub_zero] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    have hle : Fintype.card (RepositoryChannel n) ≤ Fintype.card (Reaction n) :=
      Fintype.card_le_of_surjective _ (splitToQuotient_surjective n)
    have he : (Fintype.card (DeletedChannel n) : ℝ) =
        (Fintype.card (Reaction n) : ℝ)-Fintype.card (RepositoryChannel n) := by
      rw [deleted_card_eq_loss,Nat.cast_sub hle]
    dsimp only
    rw [he,sub_div]
    ring
  have ht := hj.inv₀ (by norm_num)
  simpa only [inv_div,inv_one] using ht

end RAFReactionQuotient
