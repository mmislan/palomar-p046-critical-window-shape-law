module

public import proofs.HordijkSteelThreshold.CanonicalEscapeUpper
public import proofs.HordijkSteelThreshold.Gateway

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory RAF RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

theorem bounded_seed_probability_le_36 (n K : ℕ) (hn : 4 ≤ n) (lambda : ℝ) :
    ambientPiMeasure n lambda (boundedSeedCatalystEvent n K) ≤
      (Fintype.card (Molecule K) : ENNReal) * 36 *
        (toNNReal (catalysisP n lambda) : ENNReal) := by
  let J := ↥(binaryFood n K) × PolymerSeedReaction n 2
  let E : J → Set (AmbientCoord n → Prop) := fun j => {ω | ω (j.1.val,j.2.val)}
  have he : boundedSeedCatalystEvent n K = ⋃ j : J, E j := by
    ext ω
    simp only [boundedSeedCatalystEvent, Set.mem_ofPred_eq, Set.mem_iUnion, E]
    constructor
    · rintro ⟨x,r,hx,hr,hω⟩
      exact ⟨(⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩,⟨r,hr⟩),hω⟩
    · rintro ⟨⟨x,r⟩,hω⟩
      exact ⟨x.val,r.val,(Finset.mem_filter.mp x.property).2,r.property,hω⟩
  rw [he]
  calc
    _ ≤ ∑ j : J, ambientPiMeasure n lambda (E j) := measure_iUnion_fintype_le _ _
    _ = (Fintype.card J : ENNReal) * (toNNReal (catalysisP n lambda) : ENNReal) := by
      simp only [E, ambient_coordinate_probability, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_left
      have hc : Fintype.card J ≤ Fintype.card (Molecule K) * 36 := by
        dsimp [J]
        rw [Fintype.card_prod, Fintype.card_coe]
        exact Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (le_of_eq (card_concrete_gateway_binary_t2 hn))
      exact_mod_cast hc

theorem ambient_raf_le_escape_add_seed_36 (n K : ℕ) (hn : 4 ≤ n) (lambda : ℝ) :
    ambientPiMeasure n lambda {ω | ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} ≤
    ambientPiMeasure n lambda {ω | ∃ x ∈
      temporaryReactionClosure 2 (catalystActive ω Finset.univ), K < molLength x} +
      (Fintype.card (Molecule K) : ENNReal) * 36 *
        (toNNReal (catalysisP n lambda) : ENNReal) := by
  let E : Set (AmbientCoord n → Prop) := {ω | ∃ x ∈
    temporaryReactionClosure 2 (catalystActive ω Finset.univ), K < molLength x}
  have hs : {ω | ∃ S : Finset (Reaction n),
      IsRevRAF (binaryPolymerCRS n 2) (fun x r => ω (x,r)) S} ⊆
      E ∪ boundedSeedCatalystEvent n K := by
    intro ω hraf
    by_cases he : ω ∈ E
    · exact Or.inl he
    · right
      apply bounded_raf_has_seed_catalyst ω ?_ hraf
      intro x hx
      exact Nat.le_of_not_gt (fun h => he ⟨x,hx,h⟩)
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add_right (bounded_seed_probability_le_36 n K hn lambda) _))


theorem canonical_raf_le_finite_escape_36 (n K : ℕ) (hn : 4 ≤ n) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda (HasRAFEvent n) ≤
      staticReactionMeasure (2*(K+2))
        (fixedPoolParameter (catalysisP n lambda) (Fintype.card (Molecule n)))
        (staticEscapeEvent 2 K) +
      (Fintype.card (Molecule (K+2)) : ENNReal)*36*(toNNReal (catalysisP n lambda) : ENNReal) := by
  rw [canonical_raf_measure_eq_ambient]
  exact (ambient_raf_le_escape_add_seed_36 n (K+2) hn lambda).trans
    (add_le_add_left (ambient_escape_le_finite_static n K lambda) _)

end RAFCriticalWindowQuantitative
