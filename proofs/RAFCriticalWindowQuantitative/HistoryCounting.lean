module

public import proofs.RAFCriticalWindowQuantitative.HistoryLengthBudget
public import proofs.RAFCriticalWindowQuantitative.FiniteOpenCount

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

/-- The probabilistic step uses a deterministic family of distinct-coordinate supports.
The polymer census is a separate semantic obligation, not an independence assumption. -/
theorem history_support_union_bound (J : Type*) [Fintype J] (a : I)
    (H : Finset (Finset J)) (r C : ℕ) (hcard : ∀ T ∈ H, T.card=r) (hcount : H.card ≤ C)
    (E : Set (J → Prop)) (hcover : E ⊆ ⋃ T ∈ H, {ω | ∀ j ∈ T, ω j}) :
    (Measure.pi (fun _ : J => ambientCoordLaw a)) E ≤ (C : ENNReal)*(toNNReal a : ENNReal)^r := by
  let μ := Measure.pi (fun _ : J => ambientCoordLaw a)
  calc
    _ ≤ μ (⋃ T ∈ H, {ω | ∀ j ∈ T, ω j}) := measure_mono hcover
    _ ≤ ∑ T ∈ H, μ {ω | ∀ j ∈ T, ω j} := measure_biUnion_finset_le _ _
    _ = (H.card : ENNReal)*(toNNReal a : ENNReal)^r := by
      have he : ∀ T ∈ H, μ {ω | ∀ j ∈ T, ω j} = (toNNReal a : ENNReal)^r := by
        intro T hT
        rw [finite_support_open_probability,hcard T hT]
      rw [Finset.sum_congr rfl he]
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := by
      gcongr

end RAFCriticalWindowQuantitative
