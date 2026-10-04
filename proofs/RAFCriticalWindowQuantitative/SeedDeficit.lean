module

public import proofs.RAFCriticalWindowQuantitative.EffectiveSeed

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval
open scoped ENNReal

def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩

theorem contourBudget_finite (a : I) (k : ℕ) : contourBudget a k ≠ ∞ := by
  unfold contourBudget
  finiteness

theorem contourBudget_real (a : I) (k : ℕ) :
    (contourBudget a k).toReal = (molecularContourConstant : ℝ) * (1-(a : ℝ)^2)^k := by
  have ha : (toNNReal a : ENNReal)^2 ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  rw [contourBudget, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le ha (by simp)]
  simp

theorem selected_contour_deficit (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    contourBudget a k / (1-contourBudget a k) ≤
      1 / ((m : ENNReal)*(m+1)) := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let k := seedIndex b hb hb1 m
  have hq := rational_deficit_bound b m k hm hb.le hb1 (seedIndex_spec b hb hb1 m)
  have hr : (contourBudget a k).toReal < 1 := by
    rw [contourBudget_real]
    change (molecularContourConstant : ℝ) * (1-(b : ℝ)^2)^k < 1
    exact_mod_cast hq.1
  have he : contourBudget a k < 1 := by
    exact (ENNReal.toReal_lt_toReal (contourBudget_finite a k) (by simp)).mp (by simpa using hr)
  have hn : 1-contourBudget a k ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr he)
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (contourBudget_finite a k) hn)
    (by finiteness)).mp
  rw [ENNReal.toReal_div, ENNReal.toReal_sub_of_le he.le (by simp), contourBudget_real]
  simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_natCast]
  change (molecularContourConstant : ℝ) * (1-(b : ℝ)^2)^k /
    (1-(molecularContourConstant : ℝ) * (1-(b : ℝ)^2)^k) ≤ 1/((m : ℝ)*(m+1))
  have hcast := (Rat.cast_le (K := ℝ)).mpr hq.2
  push_cast at hcast
  exact hcast

end RAFCriticalWindowQuantitative
