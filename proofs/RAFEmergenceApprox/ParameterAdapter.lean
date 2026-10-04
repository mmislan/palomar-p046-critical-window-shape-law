module

public import proofs.HordijkSteelThreshold.PolymerCounts
public import proofs.RAF.Concrete.UniformModel

@[expose] public section

namespace RAFEmergenceApprox
open RAF.Polymer RAF.Concrete HordijkSteelThreshold unitInterval

/-- The inherited lambda parametrization covers every homogeneous probability
at every nontrivial finite source size. -/
theorem catalysisP_covers_probability (n : ℕ) (hn : 2 ≤ n) (p : I) :
    catalysisP n ((p:ℝ) * Fintype.card (Reaction n) / n) = p := by
  have hnR : (n:ℝ) ≠ 0 := by positivity
  have hj : 0 < Fintype.card (Reaction n) := by rw [card_reactions_exact hn]; omega
  have hjR : (Fintype.card (Reaction n):ℝ) ≠ 0 := by positivity
  apply Subtype.ext
  have he : rawCatalysisP n ((p:ℝ) * Fintype.card (Reaction n) / n) = p := by
    unfold rawCatalysisP
    field_simp
  change min 1 (max 0 (rawCatalysisP n _)) = (p:ℝ)
  rw [he,max_eq_right p.property.1,min_eq_right p.property.2]

end RAFEmergenceApprox
