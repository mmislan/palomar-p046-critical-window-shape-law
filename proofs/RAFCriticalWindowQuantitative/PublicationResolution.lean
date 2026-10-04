module

public import proofs.RAFCriticalWindowQuantitative.Resolution
public import proofs.RAFCriticalWindowQuantitative.OrderedHistories
public import proofs.RAFCriticalWindowQuantitative.HistoryCounting
public import proofs.RAFCriticalWindowQuantitative.PublicationArithmetic

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient
  OverlapCorrectedRAF.Source

/-- Actual source ordered-history bridges. This does not assert that the complete
sharper polymer census or singleton semantics have been formalized. -/
theorem publication_history_resolution :
    (∀ field : InfiniteSplitEnvironment, ReversibleUnbounded 2 field → ∀ r : ℕ,
      ∃ N l, LegalOrder (binaryPolymerCRS N 2) (restrictedSplitReactions N field) l ∧
        l.length = r ∧ l.Nodup) ∧
    (∀ ω : SplitField, ReversibleUnbounded 2 (quotientField ω) → ∀ r : ℕ,
      ∃ N l, LegalOrder (repositoryCRS N 2)
        (quotientOpen (fun j => ω (quotientCoordinate j))) l ∧ l.length = r ∧ l.Nodup) := by
  constructor
  · intro field h r
    obtain ⟨N,T,hT,_,_⟩ := split_unbounded_histories field h r
    obtain ⟨l,hl,_,hlen,hd⟩ := productive_history_ordered _ _ hT
    exact ⟨N,l,hl,hlen,hd⟩
  · intro ω h r
    obtain ⟨N,T,hT,_,_⟩ := quotient_unbounded_histories ω h r
    obtain ⟨l,hl,_,hlen,hd⟩ := productive_history_ordered _ _ hT
    exact ⟨N,l,hl,hlen,hd⟩

theorem publication_small_openness_arithmetic :
    (historyCoefficient 32 8 : ℚ)*(1/10^3)^8 < 1/10^5 ∧
    (historyCoefficient 32 12 : ℚ)*(1/10^4)^12 < 1/10^15 ∧
    (historyCoefficient 32 18 : ℚ)*(1/10^6)^18 < 1/10^45 ∧
    historyCoefficient 32 65 < 10^671 :=
  ⟨history_certificate_003,history_certificate_004,history_certificate_006,
    history_certificate_020⟩

end RAFCriticalWindowQuantitative
