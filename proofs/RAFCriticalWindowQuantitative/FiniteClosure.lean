module

public import proofs.HordijkSteelThreshold.TemporaryReactionClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Polymer RAF.Concrete

/-- A finite executable evaluator, using the literal source's closure iteration. -/
def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

theorem closure_growth_or_stable {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (k : ℕ) :
    k ≤ (revClosureAt Q S k).card ∨ revClosureAt Q S (k+1) = revClosureAt Q S k := by
  induction k with
  | zero => exact Or.inl (Nat.zero_le _)
  | succ k ih =>
    rcases ih with hg | he
    · by_cases he : revClosureAt Q S (k+1) = revClosureAt Q S k
      · right
        change revClosureStep Q S (revClosureAt Q S (k+1)) = _
        rw [he]
        exact he
      · left
        have hs := revClosureAt_mono_stage Q S (Nat.le_succ k)
        have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs,Ne.symm he⟩)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt hg hcard)
    · right
      change revClosureStep Q S (revClosureAt Q S (k+1)) = _
      rw [he]
      exact he

theorem closure_stable_at_card {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) :
    revClosureAt Q S (Fintype.card M+1) = revClosureAt Q S (Fintype.card M) := by
  rcases closure_growth_or_stable Q S (Fintype.card M) with hg | he
  · have hu := Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hg)
    apply Finset.Subset.antisymm
    · rw [hu]
      exact Finset.subset_univ _
    · exact revClosureAt_mono_stage Q S (Nat.le_succ _)
  · exact he

theorem closure_stable_after_card {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (j : ℕ) :
    revClosureAt Q S (Fintype.card M+j) = revClosureAt Q S (Fintype.card M) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.add_succ, revClosureAt, ih]
    exact closure_stable_at_card Q S

/-- Exact semantics: the executable finite iteration equals the existing closure. -/
theorem computedClosure_eq (N L : ℕ) (S : Finset (Reaction N)) :
    computedClosure N L S = temporaryReactionClosure L S := by
  ext x
  rw [mem_temporaryReactionClosure]
  constructor
  · intro hx
    exact ⟨Fintype.card (Molecule N),hx⟩
  · rintro ⟨k,hk⟩
    by_cases h : k ≤ Fintype.card (Molecule N)
    · exact revClosureAt_mono_stage _ _ h hk
    · have he : k = Fintype.card (Molecule N)+(k-Fintype.card (Molecule N)) := by omega
      rw [he,closure_stable_after_card] at hk
      exact hk

end RAFCriticalWindowQuantitative
