module

public import proofs.RAFCriticalWindowQuantitative.HistoryLengthBudget
public import proofs.RAFCriticalWindowQuantitative.BoundedRecords
public import proofs.RAFReactionQuotient.FiniteApproximation

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source

inductive LegalOrder {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : List R → Prop
  | nil : LegalOrder Q S []
  | snoc {l r} : LegalOrder Q S l → r ∈ S → r ∉ l →
      revClosureStep Q {r} (fullClosure Q l.toFinset) ≠ fullClosure Q l.toFinset →
      LegalOrder Q S (l++[r])

theorem productive_history_ordered {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) {k T} (h : ProductiveHistory Q S k T) :
    ∃ l : List R, LegalOrder Q S l ∧ l.toFinset=T ∧ l.length=k ∧ l.Nodup := by
  induction h with
  | nil => exact ⟨[],LegalOrder.nil,rfl,rfl,List.nodup_nil⟩
  | @step k T r h hr hrT hg ih =>
    obtain ⟨l,hl,he,hlen,hd⟩ := ih
    have hn : r ∉ l := by simpa only [← he,List.mem_toFinset] using hrT
    refine ⟨l++[r],LegalOrder.snoc hl hr hn (by simpa only [he] using hg),?_,?_,?_⟩
    · simp [he]
    · simp [hlen]
    · simp [List.nodup_append,hd]
      intro a ha heq
      subst a
      exact hn ha

theorem split_unbounded_histories (field : InfiniteSplitEnvironment)
    (h : ReversibleUnbounded 2 field) (r : ℕ) :
    ∃ N T, ProductiveHistory (binaryPolymerCRS N 2) (restrictedSplitReactions N field) r T ∧
      T.card=r ∧ T ⊆ restrictedSplitReactions N field := by
  have hB : 2 ≤ 2^(r+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ r+1 by omega)
  obtain ⟨v,hv,_,hgen⟩ := escape_has_bounded_record hB (h (2^(r+1)))
  obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgen
  have heL := congrArg List.length he
  rw [moleculeWord_length] at heL
  obtain ⟨T,hT,hcard,hsub⟩ := split_long_target_history v.length r _ x hx (by omega)
  exact ⟨v.length,T,hT,hcard,hsub⟩

theorem quotient_unbounded_histories (ω : SplitField)
    (h : ReversibleUnbounded 2 (quotientField ω)) (r : ℕ) :
    ∃ N T, ProductiveHistory (repositoryCRS N 2)
        (quotientOpen (fun j => ω (quotientCoordinate j))) r T ∧
      T.card=r ∧ T ⊆ quotientOpen (fun j => ω (quotientCoordinate j)) := by
  have hB : 2 ≤ 2^(r+1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) (show 1 ≤ r+1 by omega)
  obtain ⟨v,hv,_,hgen⟩ := escape_has_bounded_record hB (h (2^(r+1)))
  obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hgen
  rw [← quotientClosure_restriction] at hx
  have heL := congrArg List.length he
  rw [moleculeWord_length] at heL
  obtain ⟨T,hT,hcard,hsub⟩ := quotient_long_target_history v.length r _ x hx (by omega)
  exact ⟨v.length,T,hT,hcard,hsub⟩

end RAFCriticalWindowQuantitative
