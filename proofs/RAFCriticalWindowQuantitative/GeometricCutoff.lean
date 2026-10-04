module

public import proofs.RAFCriticalWindowQuantitative.EffectiveSeed

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Filter
open scoped Topology

def geometricTest (t c ε : ℚ) (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε

instance (t c ε : ℚ) (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem geometricTest_exists (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ r, geometricTest t c ε r := by
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have ht1R : (t : ℝ) < 1 := by exact_mod_cast ht1
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hs := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0R ht1R).const_mul (c : ℝ)
  simp only [mul_zero] at hs
  obtain ⟨r,hr,hv⟩ := ((eventually_ge_atTop 1).and (hs.eventually_lt_const hεR)).exists
  exact ⟨r,by omega,by exact_mod_cast hv.le⟩

def geometricIndex (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)

theorem geometricIndex_spec (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    geometricTest t c ε (geometricIndex t c ε ht0 ht1 hε) :=
  Nat.find_spec (geometricTest_exists t c ε ht0 ht1 hε)

/-- The repair-failure ratio is a genuine geometric ratio at every positive openness. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 := by
  have hp := pow_pos hq (L+1)
  have hu := pow_le_one₀ hq.le hq1 (n := L+1)
  constructor <;> linarith

end RAFCriticalWindowQuantitative
