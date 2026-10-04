module

public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
public import proofs.RAFCriticalWindowQuantitative.RealErrorBudget

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory

def quotientEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def quotientCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

/-- An executable terminating rational enclosure for the actual quotient survival profile. -/
theorem quotientCertifiedInterval_correct (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) :
    let interval := quotientCertifiedInterval q hq hq1 ε hε
    (interval.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq.le hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq.le hq1)).toReal ≤ (interval.2 : ℝ) ∧
      interval.2-interval.1 < ε := by
  let m := precisionIndex ε
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  let r := recordIndex q hq hq1 L ε hε
  let K := recordCap L r
  let a := rationalParameter q hq.le hq1
  let e := quotientEscapeEval q (K-2)
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hK : 2 ≤ K := recordCap_ge_two L r
  have hS : quotientSurvival a ≠ ⊤ := by
    unfold quotientSurvival
    exact measure_ne_top _ _
  have ht := real_error_of_bound (quotientEscapeProbability a K) (quotientSurvival a) hS m L r
    (by omega) a (explicit_quotient_truncation q hq hq1 m hm a le_rfl r)
  have he : (e : ℝ) = (quotientEscapeProbability a K).toReal :=
    (quotientEscapeEval_correct q hq.le hq1 (K-2)).trans
      (congrArg ENNReal.toReal (quotient_escape_finite a K hK).symm)
  have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast
    exact hcast
  have hr := real_record_budget q hq hq1 L ε hε
  change (quotientEscapeProbability a K).toReal ≤ (quotientSurvival a).toReal+1/(m : ℝ)+
    ((actualBinaryWords L).card : ℝ)*(1-(q : ℝ)^(L+1))^r at ht
  have hu : (e : ℝ) ≤ (quotientSurvival a).toReal+(ε : ℝ)/2 := by
    rw [he]
    linarith
  have hl : (quotientSurvival a).toReal ≤ (e : ℝ) := by
    rw [he]
    apply ENNReal.toReal_mono _ (quotient_survival_le_escape a K)
    unfold quotientEscapeProbability
    exact measure_ne_top _ _
  change ((e-ε/2 : ℚ) : ℝ) ≤ (quotientSurvival a).toReal ∧
    (quotientSurvival a).toReal ≤ (e : ℝ) ∧ e-(e-ε/2) < ε
  refine ⟨?_,hl,?_⟩
  · push_cast
    linarith
  · linarith

end RAFCriticalWindowQuantitative
