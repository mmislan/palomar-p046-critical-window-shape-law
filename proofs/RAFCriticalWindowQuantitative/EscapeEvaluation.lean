module

public import proofs.RAFCriticalWindowQuantitative.FiniteEventProbability
public import proofs.RAFCriticalWindowQuantitative.FiniteEscapeAdapters

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open MeasureTheory

def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))

def splitEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))

def quotientEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))

theorem splitEscapeEval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (splitEscapeEval q K : ℝ) =
      (staticReactionMeasure (2*(K+2)) (rationalParameter q hq hq1) (staticEscapeEvent 2 K)).toReal := by
  classical
  have h := rationalEventProbability_correct (Reaction (2*(K+2))) q hq hq1 (splitEscapeBool _ (K+2))
  have he : {ω : Reaction (2*(K+2)) → Prop | splitEscapeBool _ (K+2) (fun r => decide (ω r))} =
      staticEscapeEvent 2 K := by
    ext ω
    simp [splitEscapeBool,computedClosure_eq,staticEscapeEvent,staticOpenReactions,moleculeWord_length]
  rw [he] at h
  simpa only [splitEscapeEval,staticReactionMeasure,Measure.infinitePi_eq_pi] using h.symm

theorem quotientEscapeEval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) :
    (quotientEscapeEval q K : ℝ) =
      (quotientStaticMeasure (2*(K+2)) (rationalParameter q hq hq1) (quotientEscapeEvent 2 K)).toReal := by
  classical
  have h := rationalEventProbability_correct (RepositoryChannel (2*(K+2))) q hq hq1
    (quotientEscapeBool _ (K+2))
  have he : {ω : RepositoryChannel (2*(K+2)) → Prop |
      quotientEscapeBool _ (K+2) (fun r => decide (ω r))} = quotientEscapeEvent 2 K := by
    ext ω
    simp only [Set.mem_ofPred_eq,quotientEscapeBool,splitEscapeBool,decide_eq_true_eq,
      computedClosure_eq]
    change (∃ x ∈ temporaryReactionClosure 2 (staticOpenReactions (fun r => ω (splitToQuotient r))),
      K+2 < molLength x) ↔ _
    rw [← quotientClosure_pullback]
    simp only [quotientEscapeEvent,Set.mem_ofPred_eq,moleculeWord_length]
  rw [he] at h
  exact h.symm

end RAFCriticalWindowQuantitative
