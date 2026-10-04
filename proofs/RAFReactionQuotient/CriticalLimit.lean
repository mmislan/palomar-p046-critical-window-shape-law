module

public import proofs.RAFReactionQuotient.SourceBounds
public import proofs.RAFReactionQuotient.PoolLimits
public import proofs.RAFReactionQuotient.SurvivalContinuity
public import proofs.HordijkSteelThreshold.StaticSurvivalLeftContinuity

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open scoped ENNReal Topology

theorem quotient_static_mass_eventually (q : I) (hq : 0 < (q : ℝ))
    (m : ℕ) (hm : 0 < m) (c : ENNReal) (hc : c < quotientSurvival q) :
    ∀ᶠ n in atTop, c ≤ quotientStaticMeasure n q
      {ω | (m-1)*Fintype.card (Molecule n) ≤ m*(quotientClosure n 2 (quotientOpen ω)).card} +
        (m : ENNReal)⁻¹ := by
  obtain ⟨L,_,hbulk⟩ := quotient_supplied_seed_bulk q hq m hm
  have hs := quotientSurvival_le_seed q hq (actualBinaryWords L)
    (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)
  have ht := (quotient_finite_seed_tendsto 2 q (actualBinaryWords L)).eventually_const_lt (hc.trans_le hs)
  filter_upwards [ht,eventually_ge_atTop 1] with n hn hpos
  exact hn.le.trans ((quotient_same_field_seed_mass n L m q).trans
    (add_le_add le_rfl (hbulk q le_rfl n (by omega))))

theorem quotient_critical_limit (p : ℕ → I) {lambda : ℝ} (hlambda : 0 < lambda)
    (hp : Tendsto (fun n => (p n : ℝ)) atTop (𝓝 0))
    (hmass : Tendsto (fun n => (p n : ℝ)*Fintype.card (Molecule n)) atTop (𝓝 lambda))
    (a : I) (ha : (a : ℝ) = 1-Real.exp (-lambda)) :
    Tendsto (fun n => quotientRAFProbability n (p n)) atTop (𝓝 (quotientSurvival a)) := by
  have hapos : 0 < (a : ℝ) := by rw [ha]; exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hpne := generic_pool_nonzero p hlambda hmass
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hleft := quotientSurvival_tendsto hapos (lowerOpenness_tendsto a)
    obtain ⟨i,hi⟩ := (hleft.eventually_const_lt hc).exists
    let q := lowerOpenness a i
    have hq : 0 < (q : ℝ) := (show 0 < (a : ℝ)/2 by positivity).trans_le (half_le_lowerOpenness a i)
    have hqa : (q : ℝ) < 1-Real.exp (-lambda) := by rw [← ha]; exact lowerOpenness_lt a hapos i
    obtain ⟨d,hcd,hds⟩ := exists_between hi
    have herr : Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 c) := by
      simpa using (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero :
        Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 (c+0)))
    obtain ⟨m,hqm,hem,hm⟩ := ((nearFullPool_limit_tendsto lambda).eventually_const_lt hqa |>.and
      ((herr.eventually_lt_const hcd).and (eventually_ge_atTop 2))).exists
    have ht := generic_pool_limit p (fun n => nearFullPoolSize n m) hp hpne
      (generic_near_pool_mass p hp hmass m (by omega))
    filter_upwards [ht.eventually_const_lt hqm,nearFullPoolSize_eventually_nonfood m hm,
      quotient_static_mass_eventually q hq m (by omega) d hds] with n hparam hsize hstatic
    have hr := quotient_near_full_lower n m (p n) q (by omega) hsize hparam.le
    exact lt_of_add_lt_add_right (hem.trans_le (hstatic.trans (add_le_add hr le_rfl)))
  · intro c hc
    obtain ⟨K,hK⟩ := ((quotient_escape_tendsto a).eventually_lt_const hc).exists
    have hfull : Tendsto (fun n => fixedPoolParameter (p n) (Fintype.card (Molecule n))) atTop (𝓝 a) := by
      apply tendsto_subtype_rng.mpr
      rw [ha]
      exact generic_pool_limit p _ hp hpne hmass
    have hfinite := ((continuous_quotient_event_probability (2*(K+2)) (quotientEscapeEvent 2 K)).tendsto a).comp hfull
    have hpE : Tendsto (fun n => (toNNReal (p n) : ENNReal)) atTop (𝓝 0) := by
      have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp
      simpa only [Function.comp_def,← coe_toNNReal,ENNReal.ofReal_zero,ENNReal.ofReal_coe_nnreal] using ht
    have herr := ENNReal.Tendsto.const_mul hpE
      (Or.inr (by finiteness : (Fintype.card (Molecule (K+2)) : ENNReal)*34 ≠ ⊤))
    have hsum := hfinite.add herr
    simp only [mul_zero,add_zero] at hsum
    exact (hsum.eventually_lt_const hK).mono (fun n hn => (quotient_raf_upper n K (p n)).trans_lt hn)

end RAFReactionQuotient
