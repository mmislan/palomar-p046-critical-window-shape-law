module

public import proofs.RAFReactionQuotient.InfiniteSource
public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.SplitCylinderNull

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold
open scoped ENNReal

def quotientRecordAtom (B : ℕ) (i : RecordPrefixIndex) : Set SplitField :=
  {ω | (fun z => ω (canonicalIndex z)) ∈ recordPrefixAtom B i}

theorem quotientRecordAtom_determined (B : ℕ) (i : RecordPrefixIndex) :
    SplitPrefixDetermined (splitPrefixCoordinates i.1) (quotientRecordAtom B i) := by
  intro ω η he
  apply recordPrefixAtom_determined B i
  intro z hz
  exact he (canonicalIndex z) (canonicalIndex_prefix hz)

theorem quotientRecordAtoms_disjoint (B : ℕ) {i j : RecordPrefixIndex} (hij : i ≠ j) :
    Disjoint (quotientRecordAtom B i) (quotientRecordAtom B j) := by
  apply Set.disjoint_left.mpr
  intro ω hi hj
  exact Set.disjoint_left.mp (recordPrefixAtoms_disjoint B hij) hi hj

def quotientMissingTarget (v : List Bool) : Set SplitField :=
  {ω | ReversibleUnbounded 2 (quotientField ω) ∧
    ¬ InfiniteReversibleGenerated 2 (quotientField ω) v}

theorem quotient_record_failure (a : I) (w v : List Bool)
    (hw : 0 < w.length) (hv : 0 < v.length)
    (E : Set SplitField) (hE : SplitPrefixDetermined (splitPrefixCoordinates w.length) E)
    (hrecord : ∀ ω ∈ E, FiniteReversibleGenerated w.length 2 (quotientField ω) w) :
    infiniteSplitPi a (E ∩ {ω | ¬ InfiniteReversibleGenerated 2 (quotientField ω) v}) ≤
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  obtain ⟨T,hsize,hdis,hgen⟩ := quotient_record_support w v hw hv
  have hs : E ∩ {ω | ¬ InfiniteReversibleGenerated 2 (quotientField ω) v} ⊆
      E ∩ {ω | ¬ ∀ z ∈ T, ω z} := by
    intro ω hω
    refine ⟨hω.1,?_⟩
    intro hopen
    exact hω.2 (hgen ω (hrecord ω hω.1) hopen)
  apply (measure_mono hs).trans
  rw [split_prefix_failure_measure a _ T hdis E hE]
  have hpow : (toNNReal a : ENNReal)^(v.length+1) ≤ (toNNReal a : ENNReal)^T.card := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · exact hsize
  exact mul_le_mul_right (tsub_le_tsub_left hpow 1) _

theorem quotient_cylinder_deficit (a : I) (v : List Bool) (hv : 0 < v.length)
    (B : ℕ) (C : Set SplitField) (hC : SplitPrefixDetermined (splitPrefixCoordinates B) C) :
    infiniteSplitPi a (quotientMissingTarget v ∩ C) ≤
      infiniteSplitPi a C * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
  let D : RecordPrefixIndex → Set SplitField := fun i => C ∩ quotientRecordAtom B i
  have hmeasC := measurableSet_of_splitPrefixDetermined _ C hC
  have hmeas (i : RecordPrefixIndex) : MeasurableSet (D i) :=
    hmeasC.inter (measurableSet_of_splitPrefixDetermined _ _ (quotientRecordAtom_determined B i))
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact (quotientRecordAtoms_disjoint B hij).mono Set.inter_subset_right Set.inter_subset_right
  have hpiece (i : RecordPrefixIndex) :
      infiniteSplitPi a (quotientMissingTarget v ∩ D i) ≤
        infiniteSplitPi a (D i) * (1-(toNNReal a : ENNReal)^(v.length+1)) := by
    by_cases hn : (D i).Nonempty
    · obtain ⟨ω,hω⟩ := hn
      have hBM : B < i.1 := hω.2.1.1
      obtain ⟨w,hw,hBw,hrecord⟩ := recordPrefixAtom_word B i
        ⟨(fun z => ω (canonicalIndex z)),hω.2⟩
      have hd : SplitPrefixDetermined (splitPrefixCoordinates w.length) (D i) := by
        rw [hw]
        intro η ξ he
        apply and_congr
        · apply hC
          intro z hz
          have hz' := (mem_splitPrefixCoordinates B z).mp hz
          exact he z ((mem_splitPrefixCoordinates i.1 z).mpr ⟨by omega,by omega⟩)
        · exact quotientRecordAtom_determined B i η ξ he
      apply (measure_mono (show quotientMissingTarget v ∩ D i ⊆
        D i ∩ {η | ¬ InfiniteReversibleGenerated 2 (quotientField η) v}
        from fun η hη => ⟨hη.2,hη.1.2⟩)).trans
      exact quotient_record_failure a w v (by omega) hv (D i) hd
        (fun η hη => hrecord (fun z => η (canonicalIndex z)) hη.2)
    · have he : D i = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
      simp [he]
  have hcover : quotientMissingTarget v ∩ C ⊆
      ⋃ i : RecordPrefixIndex, quotientMissingTarget v ∩ D i := by
    intro ω hω
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (unbounded_mem_recordPrefixAtoms
      (ω := fun z => ω (canonicalIndex z)) hω.1.1 B)
    exact Set.mem_iUnion.mpr ⟨i,hω.1,hω.2,hi⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ i : RecordPrefixIndex, quotientMissingTarget v ∩ D i) := measure_mono hcover
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (quotientMissingTarget v ∩ D i) := measure_iUnion_le _
    _ ≤ ∑' i : RecordPrefixIndex, infiniteSplitPi a (D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := ENNReal.tsum_le_tsum hpiece
    _ = infiniteSplitPi a (⋃ i : RecordPrefixIndex, D i) *
        (1-(toNNReal a : ENNReal)^(v.length+1)) := by
      rw [ENNReal.tsum_mul_right,measure_iUnion hdis hmeas]
    _ ≤ _ := mul_le_mul_left (measure_mono (Set.iUnion_subset (fun _ => Set.inter_subset_left))) _

theorem quotient_missing_target_null (a : I) (ha : 0 < (a : ℝ))
    (v : List Bool) (hv : 0 < v.length) : infiniteSplitPi a (quotientMissingTarget v) = 0 := by
  have hm : MeasurableSet (quotientMissingTarget v) :=
    ((measurableSet_reversibleUnbounded 2).inter
      (measurableSet_infiniteReversibleGenerated 2 v).compl).preimage quotientField_measurable
  have hapos : 0 < (toNNReal a : ENNReal) := by exact_mod_cast ha
  apply split_cylinder_deficit_null (infiniteSplitPi a) (quotientMissingTarget v) hm
    (1-(toNNReal a : ENNReal)^(v.length+1))
  · exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero
      (pow_ne_zero _ (ne_of_gt hapos))
  · exact quotient_cylinder_deficit a v hv

end RAFReactionQuotient
