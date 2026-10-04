module

public import proofs.RAFReactionQuotient.Counts
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter unitInterval HordijkSteelThreshold RAF.Polymer
open scoped Topology

theorem log_one_sub_ratio : Tendsto (fun x : ℝ => Real.log (1-x)/x)
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 (-1)) := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (1-x)) (-1) 0 := by
    have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
    have hi : HasDerivAt (fun x : ℝ => 1-x) (-1) 0 := by
      have hfun : (fun x : ℝ => 1-x) = (fun x => 1) - id := by
        funext x
        rfl
      rw [hfun]
      simpa using (hasDerivAt_const (x := (0 : ℝ)) 1).sub (hasDerivAt_id (x := (0 : ℝ)))
    have hlog' : HasDerivAt Real.log 1 (1-(0 : ℝ)) := by simpa using hlog
    simpa [Function.comp_def] using hlog'.comp 0 hi
  simpa [div_eq_inv_mul,mul_comm] using hd.tendsto_slope_zero

theorem generic_pool_limit (p : ℕ → I) (k : ℕ → ℕ) {b : ℝ}
    (hp : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop, (p n : ℝ) ≠ 0)
    (hmass : Tendsto (fun n => (p n : ℝ)*(k n : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun n => (fixedPoolParameter (p n) (k n) : ℝ)) atTop (𝓝 (1-Real.exp (-b))) := by
  have hw : Tendsto (fun n => (p n : ℝ)) atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hp
      (hne.mono (fun n hn => by simpa using hn))
  have ht := hmass.mul (log_one_sub_ratio.comp hw)
  have hl : Tendsto (fun n => (k n : ℝ)*Real.log (1-(p n : ℝ))) atTop (𝓝 (-b)) := by
    apply (show Tendsto (fun n => ((p n : ℝ)*(k n : ℝ)) *
      (Real.log (1-(p n : ℝ))/(p n : ℝ))) atTop (𝓝 (-b)) by simpa using ht).congr'
    filter_upwards [hne] with n hn
    field_simp
  have he := (Real.continuous_exp.tendsto (-b)).comp hl
  have hclosed : Tendsto (fun n => (1-(p n : ℝ))^(k n)) atTop (𝓝 (Real.exp (-b))) := by
    apply he.congr'
    filter_upwards [hp.eventually_lt_const zero_lt_one] with n hn
    rw [← Real.exp_log (sub_pos.mpr hn),← Real.exp_nat_mul]
    rfl
  simpa only [fixedPoolParameter_coe] using tendsto_const_nhds.sub hclosed

theorem generic_near_pool_mass (p : ℕ → I) {lambda : ℝ}
    (hp : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0))
    (hmass : Tendsto (fun n => (p n : ℝ)*Fintype.card (Molecule n)) atTop (𝓝 lambda))
    (m : ℕ) (hm : 0 < m) :
    Tendsto (fun n => (p n : ℝ)*nearFullPoolSize n m) atTop (𝓝 (lambda*(1-1/(m : ℝ)))) := by
  have hrem : Tendsto (fun n => (p n : ℝ)*((Fintype.card (Molecule n)%m : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun n => (p n : ℝ)*(m : ℝ))
    · intro n; exact mul_nonneg (p n).property.1 (Nat.cast_nonneg _)
    · intro n
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt (Fintype.card (Molecule n)) hm).le)
        (p n).property.1
    · simpa using hp.mul_const (m : ℝ)
  have ht := (((hmass.sub hrem).div_const (m : ℝ)).mul_const ((m-1 : ℕ) : ℝ))
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have he : ((lambda-0)/(m : ℝ))*((m-1 : ℕ) : ℝ) = lambda*(1-1/(m : ℝ)) := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    field_simp
    ring
  rw [he] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  have hd : ((Fintype.card (Molecule n)/m : ℕ) : ℝ)*(m : ℝ) +
      (Fintype.card (Molecule n)%m : ℕ) = (Fintype.card (Molecule n) : ℝ) := by
    exact_mod_cast (show (Fintype.card (Molecule n)/m)*m + Fintype.card (Molecule n)%m =
      Fintype.card (Molecule n) from by simpa [Nat.mul_comm] using Nat.div_add_mod (Fintype.card (Molecule n)) m)
  dsimp only
  simp only [nearFullPoolSize,Nat.cast_mul]
  rw [← hd]
  field_simp
  ring

theorem generic_pool_nonzero (p : ℕ → I) {lambda : ℝ} (hlambda : 0 < lambda)
    (hmass : Tendsto (fun n => (p n : ℝ)*Fintype.card (Molecule n)) atTop (𝓝 lambda)) :
    ∀ᶠ n in atTop, (p n : ℝ) ≠ 0 := by
  filter_upwards [hmass.eventually_ne (ne_of_gt hlambda)] with n hn hp
  apply hn
  rw [hp,zero_mul]

end RAFReactionQuotient
