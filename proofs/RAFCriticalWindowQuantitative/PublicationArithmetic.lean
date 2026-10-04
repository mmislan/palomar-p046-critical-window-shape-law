module

public import proofs.RAFCriticalWindowQuantitative.HistoryLengthBudget

@[expose] public section

set_option maxRecDepth 4000
set_option exponentiation.threshold 2000

namespace RAFCriticalWindowQuantitative

theorem split_history_coefficient_two : historyCoefficient 32 2 = 2272 := by
  norm_num [historyCoefficient,historyBudget]

theorem quotient_history_coefficient_two : historyCoefficient 30 2 = 2130 := by
  norm_num [historyCoefficient,historyBudget]

theorem split_finite_example_arithmetic :
    let p : ℚ := 16/(10000*1835012)
    (216 : ℚ)/10^9 < 248*p-(248*247/2)*p^2 ∧
      2272*(131070*p)^2+36*510*p < (457 : ℚ)/10^7 := by
  norm_num

theorem quotient_finite_example_arithmetic :
    let p : ℚ := 16/(10000*1834798)
    (204 : ℚ)/10^9 < 234*p-(234*233/2)*p^2 ∧
      2130*(131070*p)^2+34*510*p < (431 : ℚ)/10^7 := by
  norm_num

theorem history_certificate_003 : (historyCoefficient 32 8 : ℚ)*(1/10^3)^8 < 1/10^5 := by
  norm_num [historyCoefficient,historyBudget]

theorem history_certificate_004 : (historyCoefficient 32 12 : ℚ)*(1/10^4)^12 < 1/10^15 := by
  norm_num [historyCoefficient,historyBudget]

theorem history_certificate_006 : (historyCoefficient 32 18 : ℚ)*(1/10^6)^18 < 1/10^45 := by
  norm_num [historyCoefficient,historyBudget]

/-- Integer cross-product form of C_65 * 10^(-1300) < 10^(-629). -/
theorem history_certificate_020 : historyCoefficient 32 65 < 10^671 := by
  norm_num [historyCoefficient,historyBudget]

end RAFCriticalWindowQuantitative
