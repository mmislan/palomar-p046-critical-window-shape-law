module

public import proofs.RAFCriticalWindowQuantitative.GeometricCutoff

@[expose] public section

namespace RAFCriticalWindowQuantitative

theorem rationalHalf_pos (q : ℚ) (hq : 0 < q) : 0 < q/2 :=
  div_pos hq zero_lt_two

theorem rationalHalf_le_one (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

def precisionIndex (ε : ℚ) : ℕ := ⌈4/ε⌉₊+2

theorem precisionIndex_ge_two (ε : ℚ) : 2 ≤ precisionIndex ε := by
  unfold precisionIndex
  omega

theorem precisionIndex_error (ε : ℚ) (hε : 0 < ε) :
    1/(precisionIndex ε : ℚ) ≤ ε/4 := by
  have hc := Nat.le_ceil (4/ε : ℚ)
  have hm : (0 : ℚ) < precisionIndex ε := by
    exact_mod_cast (show 0 < precisionIndex ε from lt_of_lt_of_le (by omega) (precisionIndex_ge_two ε))
  have hbig : (4 : ℚ)/ε ≤ precisionIndex ε := by
    exact hc.trans (by simp [precisionIndex])
  have hx := (div_le_iff₀ hε).mp hbig
  apply (div_le_iff₀ hm).mpr
  nlinarith

def recordIndex (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)

theorem recordIndex_error (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) :
    0 < recordIndex q hq hq1 L ε hε ∧
      (2 : ℚ)^(L+1)*(1-q^(L+1))^(recordIndex q hq hq1 L ε hε) ≤ ε/4 :=
  geometricIndex_spec _ _ _ _ _ _

end RAFCriticalWindowQuantitative
