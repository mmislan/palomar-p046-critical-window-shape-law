module

public import proofs.HordijkSteelThreshold.StaticClosureMass
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Filter HordijkSteelThreshold
open scoped Topology

/-- A decidable rational test, using the source's literal contour constant. -/
def seedTest (b : ℚ) (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1

instance (b : ℚ) (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem seedTest_exists (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    ∃ k, seedTest b m k := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbR1 : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hq0 : (0 : ℝ) ≤ 1 - (b : ℝ)^2 := by nlinarith
  have hq1 : 1 - (b : ℝ)^2 < 1 := by nlinarith
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hs := (ht.const_mul (molecularContourConstant : ℝ)).mul_const
    ((m : ℝ) * (m+1) + 1)
  simp only [mul_zero, zero_mul] at hs
  obtain ⟨k, hk, hv⟩ := ((eventually_ge_atTop 1).and
    (hs.eventually_lt_const (show (0 : ℝ) < 1 by norm_num))).exists
  refine ⟨k, by omega, ?_⟩
  exact_mod_cast hv.le

/-- Executable unbounded search; termination is proved from geometric decay. -/
def seedIndex (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)

theorem seedIndex_spec (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    seedTest b m (seedIndex b hb hb1 m) := Nat.find_spec (seedTest_exists b hb hb1 m)

/-- The exact rational comparison gives the deficit needed by the mass proof. -/
theorem rational_deficit_bound (b : ℚ) (m k : ℕ) (hm : 0 < m)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (ht : seedTest b m k) :
    let h := (molecularContourConstant : ℚ) * (1-b^2)^k
    h < 1 ∧ h / (1-h) ≤ 1 / ((m : ℚ)*(m+1)) := by
  dsimp
  have hmR : (0 : ℚ) < m := by exact_mod_cast hm
  have hd : (0 : ℚ) < (m : ℚ)*(m+1) := by positivity
  have hh0 : (0 : ℚ) ≤ (molecularContourConstant : ℚ) * (1-b^2)^k := by
    apply mul_nonneg (Nat.cast_nonneg _)
    apply pow_nonneg
    nlinarith
  have hh := ht.2
  have hh1 : (molecularContourConstant : ℚ) * (1-b^2)^k < 1 := by nlinarith
  refine ⟨hh1, ?_⟩
  apply (div_le_div_iff₀ (sub_pos.mpr hh1) hd).mpr
  nlinarith

end RAFCriticalWindowQuantitative
