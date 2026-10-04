module

public import proofs.RAFCriticalWindowQuantitative.RecordContraction
public import proofs.RAFCriticalWindowQuantitative.QuotientFiniteRepair

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval
open scoped ENNReal

def quotientEscapedMissing (B : ℕ) (v : List Bool) : Set SplitField :=
  {ω | (∃ w, B < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w) ∧
    ¬ FiniteReversibleGenerated B 2 (quotientField ω) v}

theorem quotient_finite_missing_determined (B : ℕ) (v : List Bool) :
    SplitPrefixDetermined (splitPrefixCoordinates B)
      {ω | ¬ FiniteReversibleGenerated B 2 (quotientField ω) v} := by
  intro ω η he
  apply finite_missing_determined B v (fun z => ω (canonicalIndex z))
    (fun z => η (canonicalIndex z))
  intro z hz
  exact he (canonicalIndex z) (canonicalIndex_prefix hz)

/-- The deterministic-cap contraction; no conditioning on future escape. -/
theorem quotient_escaped_missing_contraction (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (hB : 2 ≤ B) :
    infiniteSplitPi a (quotientEscapedMissing (2*B+v.length) v) ≤
      infiniteSplitPi a (quotientEscapedMissing B v) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  let C : Set SplitField := {ω | ¬ FiniteReversibleGenerated B 2 (quotientField ω) v}
  let D : RecordPrefixIndex → Set SplitField := fun i => C ∩ quotientRecordAtom B i
  have hC := quotient_finite_missing_determined B v
  have hmeasC := measurableSet_of_splitPrefixDetermined _ C hC
  have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
    hmeasC.inter (measurableSet_of_splitPrefixDetermined _ _ (quotientRecordAtom_determined B i))
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact (quotientRecordAtoms_disjoint B hij).mono Set.inter_subset_right Set.inter_subset_right
  have hpiece (i : RecordPrefixIndex) :
      infiniteSplitPi a (quotientEscapedMissing (2*B+v.length) v ∩ D i) ≤
        infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
    by_cases hn : (D i).Nonempty
    · obtain ⟨ω,hω⟩ := hn
      have hBM : B < i.1 := hω.2.1.1
      have hMB := first_record_cap (ω := fun z => ω (canonicalIndex z)) hB hω.2.1
      obtain ⟨w,hw,hBw,hrecord⟩ := recordPrefixAtom_word B i ⟨(fun z => ω (canonicalIndex z)),hω.2⟩
      have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
        rw [hw]
        intro η ξ he
        apply and_congr
        · apply hC
          intro z hz
          have hz' := (mem_splitPrefixCoordinates B z).mp hz
          exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega,by omega⟩)
        · exact quotientRecordAtom_determined B i η ξ he
      apply (measure_mono (show quotientEscapedMissing (2*B+v.length) v ∩ D i ⊆
        D i ∩ {η | ¬ FiniteReversibleGenerated (2*B+v.length) 2 (quotientField η) v}
        from fun η hη => ⟨hη.2,hη.1.2⟩)).trans
      exact quotient_finite_record_failure_bound a w v (by omega) hv (2*B+v.length)
        (by omega) (D i) hd (fun η hη => hrecord (fun z => η (canonicalIndex z)) hη.2)
    · have he : D i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he]
  have hcover : quotientEscapedMissing (2*B+v.length) v ⊆
      ⋃ i : RecordPrefixIndex, quotientEscapedMissing (2*B+v.length) v ∩ D i := by
    intro ω hω
    obtain ⟨w,hw,hg⟩ := hω.1
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (escape_mem_record_atoms (ω := fun z => ω (canonicalIndex z)) hB ⟨w,by omega,hg⟩)
    exact Set.mem_iUnion.mpr ⟨i,hω,
      (fun hgen => hω.2 (finiteReversibleGenerated_mono_cap (by omega) hgen)),hi⟩
  have hsub : (⋃ i : RecordPrefixIndex, D i) ⊆ quotientEscapedMissing B v := by
    intro ω hω
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hω
    obtain ⟨w,hw,hg⟩ := hi.2.1.2.1
    exact ⟨⟨w,by have hb := hi.2.1.1; omega,finiteReversibleGenerated_to_infinite hg⟩,hi.1⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ i : RecordPrefixIndex, quotientEscapedMissing (2*B+v.length) v ∩ D i) := measure_mono hcover
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (quotientEscapedMissing (2*B+v.length) v ∩ D i) := measure_iUnion_le _
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
    _ = infiniteSplitPi a (⋃ i : RecordPrefixIndex, D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := by
      rw [ENNReal.tsum_mul_right,measure_iUnion hdis hmeas]
    _ ≤ _ := mul_le_mul_left (measure_mono hsub) _

end RAFCriticalWindowQuantitative
