module

public import proofs.RAFCriticalWindowQuantitative.FiniteOpenCount
public import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure
public import proofs.HordijkSteelThreshold.StaticSurvivalContinuity
public import proofs.RAFReactionQuotient.SurvivalContinuity

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory unitInterval
open scoped ENNReal

def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)

def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r

def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

theorem split_sparse_probability (a : I) (r : ℕ) :
    staticSurvival a ≤ (splitSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let K := 2^(r+1)
  let N := 2*(K+2)
  have hs : staticEscapeEvent 2 K ⊆
      {ω | r ≤ (Finset.univ.filter (fun j : Reaction N => ω j)).card} := by
    intro ω hω
    obtain ⟨x,hx,hlen⟩ := hω
    by_contra hn
    have hcard : (staticOpenReactions ω).card < r := by
      exact lt_of_not_ge hn
    have hb := sparse_closure_length N (staticOpenReactions ω) x hx
    have hp : 2^((staticOpenReactions ω).card+1) ≤ 2^(r+1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [moleculeWord_length] at hlen
    dsimp [K] at hlen
    omega
  apply (staticSurvival_le_finite_escape a K).trans
  apply (measure_mono hs).trans
  simpa +instances only [staticReactionMeasure,Measure.infinitePi_eq_pi,
    splitSparseCoefficient,sparseWitnessCap,N,K,ENNReal.instLE,ENNReal.instPartialOrder] using
    finite_many_open_probability (Reaction N) a r

theorem quotient_sparse_probability (a : I) (r : ℕ) :
    quotientSurvival a ≤ (quotientSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r := by
  let K := 2^(r+1)
  let N := 2*(K+2)
  have hs : quotientEscapeEvent 2 K ⊆
      {ω | r ≤ (Finset.univ.filter (fun j : RepositoryChannel N => ω j)).card} := by
    intro ω hω
    obtain ⟨x,hx,hlen⟩ := hω
    by_contra hn
    have hcard : (quotientOpen ω).card < r := by
      exact lt_of_not_ge hn
    have hb := quotient_sparse_closure_length N (quotientOpen ω) x hx
    have hp : 2^((quotientOpen ω).card+1) ≤ 2^(r+1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [moleculeWord_length] at hlen
    dsimp [K] at hlen
    omega
  apply (quotientSurvival_le_finite_escape a K).trans
  exact (measure_mono hs).trans (finite_many_open_probability (RepositoryChannel N) a r)

theorem split_sparse_real (a : I) (r : ℕ) :
    (staticSurvival a).toReal ≤ (splitSparseCoefficient r : ℝ)*(a : ℝ)^r := by
  have h := ENNReal.toReal_mono (by finiteness) (split_sparse_probability a r)
  simpa using h

theorem quotient_sparse_real (a : I) (r : ℕ) :
    (quotientSurvival a).toReal ≤ (quotientSparseCoefficient r : ℝ)*(a : ℝ)^r := by
  have h := ENNReal.toReal_mono (by finiteness) (quotient_sparse_probability a r)
  simpa using h

/-- Epsilon-delta flatness: smaller than every fixed power at zero. -/
theorem power_bound_implies_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : I, 0 < (a : ℝ) → (a : ℝ) < δ → S a < ε*(a : ℝ)^d := by
  let c : ℝ := C (d+1)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  refine ⟨ε/(c+1),by positivity,?_⟩
  intro a ha haδ
  have hx := (lt_div_iff₀ (show 0 < c+1 by positivity)).mp haδ
  have hca : c*(a : ℝ) < ε := by nlinarith
  have hp := mul_lt_mul_of_pos_right hca (pow_pos ha d)
  have hb := hbound a (d+1)
  rw [pow_succ] at hb
  dsimp [c] at hp
  nlinarith

theorem split_low_openness_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : I, 0 < (a : ℝ) → (a : ℝ) < δ →
      (staticSurvival a).toReal < ε*(a : ℝ)^d :=
  power_bound_implies_flatness (fun a => (staticSurvival a).toReal) splitSparseCoefficient split_sparse_real d ε hε

theorem quotient_low_openness_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : I, 0 < (a : ℝ) → (a : ℝ) < δ →
      (quotientSurvival a).toReal < ε*(a : ℝ)^d :=
  power_bound_implies_flatness (fun a => (quotientSurvival a).toReal) quotientSparseCoefficient quotient_sparse_real d ε hε

end RAFCriticalWindowQuantitative
