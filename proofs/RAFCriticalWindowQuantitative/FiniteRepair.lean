module

public import proofs.HordijkSteelThreshold.RecordCylinderDeficit

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval
open scoped ENNReal

/-- The record repair finishes inside its explicitly bounded cap. -/
theorem finite_record_support (w v : List Bool) (hw : 0 < w.length) (hv : 0 < v.length) :
    ∃ T : Finset (List Bool × ℕ), T.card ≤ v.length+1 ∧
      Disjoint (splitPrefixCoordinates w.length) T ∧
      ∀ field : InfiniteSplitEnvironment,
        FiniteReversibleGenerated w.length 2 field w →
        (∀ z ∈ T, field z.1 z.2) →
          FiniteReversibleGenerated (w.length+v.length) 2 field v := by
  let N := w.length+v.length
  obtain ⟨S,hsize,hband,hgen⟩ := target_trial_support (N := N) w v hw hv le_rfl
  let T := S.image literalSplitCoordinate
  refine ⟨T,(Finset.card_image_le).trans hsize,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hz ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    have hl := (mem_splitPrefixCoordinates w.length (literalSplitCoordinate r)).mp hz
    have hb := (hband r hr).1
    change (moleculeWord (reactionProduct r)).length ≤ w.length ∧ _ at hl
    rw [moleculeWord_length] at hl
    omega
  · intro field hrecord hopen
    have hgN := finiteReversibleGenerated_mono_cap (show w.length ≤ N by dsimp [N]; omega) hrecord
    obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgN
    have hs : S ⊆ restrictedSplitReactions N field := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hopen (literalSplitCoordinate r)
        (Finset.mem_image.mpr ⟨r,hr,rfl⟩)⟩
    obtain ⟨y,hy,hev⟩ := hgen (restrictedSplitReactions N field) hs x hx he
    simpa only [hev] using literalClosure_to_finiteReversible field y hy

theorem finite_record_failure_bound (a : I) (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length) (N : ℕ) (hN : w.length+v.length ≤ N)
    (E : Set SplitField) (hE : SplitPrefixDetermined (splitPrefixCoordinates w.length) E)
    (hrecord : ∀ ω ∈ E, FiniteReversibleGenerated w.length 2 (currySplitField ω) w) :
    infiniteSplitPi a (E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (currySplitField ω) v}) ≤
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  obtain ⟨T,hsize,hdis,hgen⟩ := finite_record_support w v hw hv
  have hs : E ∩ {ω | ¬ FiniteReversibleGenerated N 2 (currySplitField ω) v} ⊆
      E ∩ {ω | ¬ ∀ z ∈ T, ω z} := by
    intro ω hω
    refine ⟨hω.1,?_⟩
    intro hopen
    exact hω.2 (finiteReversibleGenerated_mono_cap hN
      (hgen (currySplitField ω) (hrecord ω hω.1) hopen))
  apply (measure_mono hs).trans
  rw [split_prefix_failure_measure a _ T hdis E hE]
  have hpow : (toNNReal a : ENNReal)^(v.length+1) ≤ (toNNReal a : ENNReal)^T.card := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · exact hsize
  exact mul_le_mul_right (tsub_le_tsub_left hpow 1) _

end RAFCriticalWindowQuantitative
