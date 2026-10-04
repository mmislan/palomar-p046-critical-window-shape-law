module

public import proofs.RAFReactionQuotient.Fibres
public import proofs.HordijkSteelThreshold.TargetTrials

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold

theorem splitToOrdered_surjective (n : ℕ) : Function.Surjective (@splitToOrdered n) := by
  intro q
  obtain ⟨r,hl,hr,_⟩ := source_append_split
    (moleculeWord q.val.1) (moleculeWord q.val.2)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by rw [moleculeWord_length]; exact Nat.succ_pos _)
    (by simpa only [moleculeWord_length] using q.property)
  refine ⟨r, Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact moleculeWord_injective hl
  · exact moleculeWord_injective hr

theorem splitToQuotient_surjective (n : ℕ) : Function.Surjective (@splitToQuotient n) :=
  (canonical_surjective n).comp (splitToOrdered_surjective n)

theorem quotient_mark_pullback_OR {n : ℕ} (ω : RepositoryChannel n → Prop) (j : RepositoryChannel n) :
    (∃ r : Reaction n, splitToQuotient r = j ∧ ω (splitToQuotient r)) ↔ ω j := by
  constructor
  · rintro ⟨r, rfl, hr⟩
    exact hr
  · intro hj
    obtain ⟨r,hr⟩ := splitToQuotient_surjective n j
    exact ⟨r,hr,hr.symm ▸ hj⟩

end RAFReactionQuotient
