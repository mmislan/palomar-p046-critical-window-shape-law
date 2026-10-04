module

public import proofs.RAFCriticalWindowQuantitative.RationalPool
public import proofs.RAFCriticalWindowQuantitative.Endpoints

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open scoped ENNReal

noncomputable def splitCatalyticProbability (n : ℕ) (p : I) : ENNReal :=
  uniformCatalysisMeasure n ((p : ℝ)*Fintype.card (Reaction n)/n) (HasRAFEvent n)

def splitSourceInterval (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : ℚ × ℚ :=
  (splitSeedEval n (10*seedIndex q hq hq1 m) q - 1/m,
    splitEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*36*p)

def quotientSourceInterval (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : ℚ × ℚ :=
  let hh : 0 < q/2 := rationalHalf_pos q hq
  let hh1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  (quotientSeedEval n (10*seedIndex (q/2) hh hh1 m) q - 1/m,
    quotientEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*34*p)

theorem splitSourceInterval_correct (n m K : ℕ) (hn : 4 ≤ n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m)) :
    let v := splitSourceInterval n m K p q hq hq1
    (v.1 : ℝ) ≤ (splitCatalyticProbability n (rationalParameter p hp hp1)).toReal ∧
      (splitCatalyticProbability n (rationalParameter p hp hp1)).toReal ≤ (v.2 : ℝ) := by
  let a := rationalParameter p hp hp1
  let lam : ℝ := (a : ℝ)*Fintype.card (Reaction n)/n
  have he : catalysisP n lam = a := RAFEmergenceApprox.catalysisP_covers_probability n (by omega) a
  have hqpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
    rw [← rationalPool_correct p hp hp1]
    exact (Rat.cast_le (K := ℝ)).mpr hpool
  have hl := split_finite_source_lower q hq hq1 m n hm (by omega) lam hk (by rwa [he])
  have hu := canonical_raf_le_finite_escape_36 n K hn lam
  rw [he] at hu
  have hP : uniformCatalysisMeasure n lam (HasRAFEvent n) ≠ ⊤ := measure_ne_top _ _
  have hi : (m : ENNReal)⁻¹ ≠ ⊤ := by simp [Nat.ne_of_gt hm]
  have hlow := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hP,hi⟩) hl
  rw [ENNReal.toReal_add hP hi, ← splitSeedEval_correct n _ q hq.le hq1] at hlow
  have hE : staticReactionMeasure (2*(K+2)) (fixedPoolParameter a (Fintype.card (Molecule n)))
      (staticEscapeEvent 2 K) ≠ ⊤ := measure_ne_top _ _
  have ht : (Fintype.card (Molecule (K+2)) : ENNReal)*36*(toNNReal a : ENNReal) ≠ ⊤ := by finiteness
  have hupp := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hE,ht⟩) hu
  rw [ENNReal.toReal_add hE ht, ← rationalPool_correct p hp hp1,
    ← splitEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K] at hupp
  rw [ENNReal.toReal_inv,ENNReal.toReal_natCast] at hlow
  simp only [← one_div] at hlow
  dsimp only [a] at hlow hupp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.coe_toReal,coe_toNNReal] at hupp
  dsimp only [splitSourceInterval,splitCatalyticProbability,Prod.fst,Prod.snd]
  push_cast
  constructor
  · change _ ≤ (uniformCatalysisMeasure n lam (HasRAFEvent n)).toReal
    linarith
  · exact hupp

theorem quotientSourceInterval_correct (n m K : ℕ) (hn : 0 < n) (hm : 0 < m)
    (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ rationalPool p (nearFullPoolSize n m)) :
    let v := quotientSourceInterval n m K p q hq hq1
    (v.1 : ℝ) ≤ (quotientRAFProbability n (rationalParameter p hp hp1)).toReal ∧
      (quotientRAFProbability n (rationalParameter p hp hp1)).toReal ≤ (v.2 : ℝ) := by
  let a := rationalParameter p hp hp1
  have hqpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
    rw [← rationalPool_correct p hp hp1]
    exact (Rat.cast_le (K := ℝ)).mpr hpool
  have hl := quotient_finite_source_lower q hq hq1 m n hm hn a hk hqpool
  have hu := quotient_raf_upper n K a
  have hP : quotientRAFProbability n a ≠ ⊤ := by unfold quotientRAFProbability quotientCatalyticLaw; exact measure_ne_top _ _
  have hi : (m : ENNReal)⁻¹ ≠ ⊤ := by simp [Nat.ne_of_gt hm]
  have hlow := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hP,hi⟩) hl
  rw [ENNReal.toReal_add hP hi, ← quotientSeedEval_correct n _ q hq.le hq1] at hlow
  have hE : quotientStaticMeasure (2*(K+2)) (fixedPoolParameter a (Fintype.card (Molecule n)))
      (quotientEscapeEvent 2 K) ≠ ⊤ := by unfold quotientStaticMeasure; exact measure_ne_top _ _
  have ht : (Fintype.card (Molecule (K+2)) : ENNReal)*34*(toNNReal a : ENNReal) ≠ ⊤ := by finiteness
  have hupp := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hE,ht⟩) hu
  rw [ENNReal.toReal_add hE ht, ← rationalPool_correct p hp hp1,
    ← quotientEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K] at hupp
  rw [ENNReal.toReal_inv,ENNReal.toReal_natCast] at hlow
  simp only [← one_div] at hlow
  dsimp only [a] at hlow hupp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.coe_toReal,coe_toNNReal] at hupp
  dsimp only [quotientSourceInterval,Prod.fst,Prod.snd]
  push_cast
  constructor
  · linarith
  · exact hupp

theorem interval_comparison_error (P S lP uP lS uS : ℝ)
    (hP : lP ≤ P ∧ P ≤ uP) (hS : lS ≤ S ∧ S ≤ uS) :
    |P-S| ≤ max (uP-lS) (uS-lP) := by
  apply abs_le.mpr
  constructor
  · have h := le_max_right (uP-lS) (uS-lP)
    linarith [hP.1,hS.2]
  · have h := le_max_left (uP-lS) (uS-lP)
    linarith [hP.2,hS.1]

end RAFCriticalWindowQuantitative
