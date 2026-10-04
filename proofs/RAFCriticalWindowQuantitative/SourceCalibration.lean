module

public import proofs.RAFCriticalWindowQuantitative.SourceContract

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open Filter
open scoped Topology

theorem splitCatalyticProbability_normalization (n : ℕ) (hn : 2 ≤ n) (lam : ℝ) :
    splitCatalyticProbability n (catalysisP n lam) = uniformCatalysisMeasure n lam (HasRAFEvent n) := by
  unfold splitCatalyticProbability uniformCatalysisMeasure
  rw [RAFEmergenceApprox.catalysisP_covers_probability n hn]

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) (profile.2-source.1)

theorem split_source_profile_error (n m K : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m))
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ) := by
  have hP := splitSourceInterval_correct n m K hn hm p hp hp1 q hq hq1 hk hpool
  have hS := splitTotalInterval_correct s hs hs1 ε hε
  have h := interval_comparison_error _ _ _ _ _ _ hP ⟨hS.1,hS.2.1⟩
  simpa [rationalIntervalError] using h

theorem quotient_source_profile_error (n m K : ℕ) (hn : 0 < n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m))
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ) := by
  have hP := quotientSourceInterval_correct n m K hn hm p hp hp1 q hq hq1 hk hpool
  have hS := quotientTotalInterval_correct s hs hs1 ε hε
  have h := interval_comparison_error _ _ _ _ _ _ hP ⟨hS.1,hS.2.1⟩
  simpa [rationalIntervalError] using h

/-- Convergence of an unspecified input sequence cannot give an input-free tail rate. -/
theorem delayed_input_drift (N : ℕ) (lam : ℝ) :
    ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 lam) ∧ u N = lam+1 := by
  let u : ℕ → ℝ := fun n => if n ≤ N then lam+1 else lam
  refine ⟨u,?_,by simp [u]⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop N] with n hn
  simp [u,not_le.mpr hn]

end RAFCriticalWindowQuantitative
