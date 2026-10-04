module

public import proofs.RAFReactionQuotient.InfiniteSource
public import proofs.RAFReactionQuotient.Surjectivity
public import proofs.RAFReactionQuotient.CommutingUniqueness
public import proofs.RAFReactionQuotient.SeedBulk

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def orderedCoordinate {n : ℕ} (r : OrderedChannel n) : List Bool × ℕ :=
  (moleculeWord r.val.1 ++ moleculeWord r.val.2, molLength r.val.1)

theorem orderedCoordinate_split {n : ℕ} (r : Reaction n) :
    orderedCoordinate (splitToOrdered r) = literalSplitCoordinate r := by
  apply Prod.ext
  · exact reaction_words_append r
  · exact molLength_reactionLeft r

theorem orderedCoordinate_injective (n : ℕ) : Function.Injective (@orderedCoordinate n) := by
  intro q j he
  obtain ⟨r,rfl⟩ := splitToOrdered_surjective n q
  obtain ⟨s,rfl⟩ := splitToOrdered_surjective n j
  rw [orderedCoordinate_split,orderedCoordinate_split] at he
  exact congrArg splitToOrdered (literalSplitCoordinate_injective n he)

noncomputable def quotientCoordinate {n : ℕ} (j : RepositoryChannel n) : List Bool × ℕ :=
  orderedCoordinate ⟨j.val,j.property.1⟩

theorem quotientCoordinate_injective (n : ℕ) : Function.Injective (@quotientCoordinate n) := by
  intro j k he
  exact Subtype.ext (congrArg (fun q : OrderedChannel n => q.val)
    (orderedCoordinate_injective n he))

theorem word_comm_iff {n : ℕ} (u v : Molecule n) :
    moleculeWord u ++ moleculeWord v = moleculeWord v ++ moleculeWord u ↔
      displayedConcat u v = displayedConcat v u := by
  constructor
  · intro he
    have hc := congrArg binaryWordCode he
    simpa only [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,
      displayedConcat] using hc
  · intro hc
    apply binaryWordCode_injective_length (by simp [Nat.add_comm])
    simpa only [binaryWordCode_append,binaryWordCode_moleculeWord,moleculeWord_length,
      displayedConcat] using hc

theorem canonicalIndex_ordered {n : ℕ} (r : OrderedChannel n) :
    canonicalIndex (orderedCoordinate r) = quotientCoordinate (canonical r) := by
  have hu : 0 < molLength r.val.1 := Nat.succ_pos _
  have hv : 0 < molLength r.val.2 := Nat.succ_pos _
  have ht : (moleculeWord r.val.1 ++ moleculeWord r.val.2).take (molLength r.val.1) =
      moleculeWord r.val.1 := by rw [← moleculeWord_length r.val.1]; simp
  have hd : (moleculeWord r.val.1 ++ moleculeWord r.val.2).drop (molLength r.val.1) =
      moleculeWord r.val.2 := by rw [← moleculeWord_length r.val.1]; simp
  unfold canonical
  split
  · rename_i h
    have hn : ¬ (molLength r.val.2 < molLength r.val.1 ∧
        moleculeWord r.val.1 ++ moleculeWord r.val.2 =
          moleculeWord r.val.2 ++ moleculeWord r.val.1) := by
      rintro ⟨hl,hc⟩
      rcases h with h | h
      · exact h ((word_comm_iff _ _).mp hc)
      · unfold moleculePrecedes at h
        omega
    simp only [canonicalIndex,orderedCoordinate,ht,hd,List.length_append,moleculeWord_length]
    simp only [Nat.add_sub_cancel_left]
    rw [ite_eq_right (by intro h; exact hn ⟨h.2.2.1,h.2.2.2⟩)]
    rfl
  · rename_i h
    have hl := noncanonical_strict_lengths r h
    have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 :=
      Classical.byContradiction (fun hn => h (Or.inl hn))
    have hw := (word_comm_iff _ _).mpr hc
    simp only [canonicalIndex,orderedCoordinate,ht,hd,List.length_append,moleculeWord_length]
    simp only [Nat.add_sub_cancel_left]
    rw [ite_eq_left ⟨hu,by omega,hl,hw⟩]
    exact Prod.ext hw rfl

theorem canonicalIndex_split {n : ℕ} (r : Reaction n) :
    canonicalIndex (literalSplitCoordinate r) = quotientCoordinate (splitToQuotient r) := by
  rw [← orderedCoordinate_split]
  exact canonicalIndex_ordered _

theorem infinite_quotient_restriction_map (n : ℕ) (a : I) :
    (infiniteSplitPi a).map (fun ω j => ω (quotientCoordinate j)) = quotientStaticMeasure n a := by
  have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (quotientCoordinate_injective n)
  rw [hs.map_fun_eq_pi_map (fun j => (measurable_pi_apply (quotientCoordinate j)).aemeasurable)]
  have he (j : RepositoryChannel n) : (infiniteSplitPi a).map (fun ω => ω (quotientCoordinate j)) =
      ambientCoordLaw a := by rw [infiniteSplitPi,Measure.infinitePi_map_eval]
  simp_rw [he]
  rfl

end RAFReactionQuotient
