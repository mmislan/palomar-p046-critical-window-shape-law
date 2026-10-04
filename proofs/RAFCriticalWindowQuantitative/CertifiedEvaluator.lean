module

public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
public import proofs.RAFCriticalWindowQuantitative.RealErrorBudget

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory

def splitEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def splitCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

/-- An executable terminating rational enclosure for the actual split survival profile. -/
theorem splitCertifiedInterval_correct (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) :
    let interval := splitCertifiedInterval q hq hq1 ε hε
    (interval.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq.le hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq.le hq1)).toReal ≤ (interval.2 : ℝ) ∧
      interval.2-interval.1 < ε := by
  let m := precisionIndex ε
  let L := 10*seedIndex q hq hq1 m
  let r := recordIndex q hq hq1 L ε hε
  let K := recordCap L r
  let a := rationalParameter q hq.le hq1
  let e := splitEscapeEval q (K-2)
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hK : 2 ≤ K := recordCap_ge_two L r
  have hS : staticSurvival a ≠ ⊤ := by
    unfold staticSurvival
    exact measure_ne_top _ _
  have ht := real_error_of_bound (splitEscapeProbability a K) (staticSurvival a) hS m L r
    (by omega) a (explicit_split_truncation q hq hq1 m hm a le_rfl r)
  have he : (e : ℝ) = (splitEscapeProbability a K).toReal :=
    (splitEscapeEval_correct q hq.le hq1 (K-2)).trans
      (congrArg ENNReal.toReal (split_escape_finite a K hK).symm)
  have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast
    exact hcast
  have hr := real_record_budget q hq hq1 L ε hε
  change (splitEscapeProbability a K).toReal ≤ (staticSurvival a).toReal+1/(m : ℝ)+
    ((actualBinaryWords L).card : ℝ)*(1-(q : ℝ)^(L+1))^r at ht
  have hu : (e : ℝ) ≤ (staticSurvival a).toReal+(ε : ℝ)/2 := by
    rw [he]
    linarith
  have hl : (staticSurvival a).toReal ≤ (e : ℝ) := by
    rw [he]
    apply ENNReal.toReal_mono _ (split_survival_le_escape a K)
    unfold splitEscapeProbability
    exact measure_ne_top _ _
  change ((e-ε/2 : ℚ) : ℝ) ≤ (staticSurvival a).toReal ∧
    (staticSurvival a).toReal ≤ (e : ℝ) ∧ e-(e-ε/2) < ε
  refine ⟨?_,hl,?_⟩
  · push_cast
    linarith
  · linarith

end RAFCriticalWindowQuantitative
