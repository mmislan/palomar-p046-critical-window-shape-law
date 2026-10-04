module

public import proofs.RAFCriticalWindowQuantitative.SeedDeficit

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete unitInterval
open scoped ENNReal

/-- Uniform finite closure deficit at the executable seed cutoff. -/
theorem effective_closure_deficit (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (d : ℕ) (hd : 0 < d) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    let η := (m : ENNReal)⁻¹/(m+1)
    staticReactionMeasure N a {ω |
      (temporaryReactionClosure (10*k) (staticOpenReactions ω)).card+d ≤ Fintype.card (Molecule N)} ≤
      η + (Fintype.card (Molecule N) : ENNReal)*η/d := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let k := seedIndex b hb hb1 m
  have hk : 0 < k := (seedIndex_spec b hb hb1 m).1
  have hbound := selected_contour_deficit b hb hb1 m hm
  have hηeq : 1 / ((m : ENNReal)*(m+1)) = (m : ENNReal)⁻¹/(m+1) := by
    simp [div_eq_mul_inv, ENNReal.mul_inv]
  change contourBudget a k / (1-contourBudget a k) ≤ _ at hbound
  rw [hηeq] at hbound
  apply (measure_temporaryClosure_deficit (w := 5*k) (k := k)
    (by omega : 2*(5*k) ≤ 10*k) (by omega) (by omega) hN a d hd).trans
  gcongr


/-- The computed cutoff gives the literal uniform supplied-seed mass guarantee. -/
theorem effective_static_bulk (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let a := rationalParameter b hb.le hb1
    let k := seedIndex b hb hb1 m
    ∀ N : ℕ, 0 < N →
      staticReactionMeasure N a {ω |
        m*(temporaryReactionClosure (10*k) (staticOpenReactions ω)).card <
          (m-1)*Fintype.card (Molecule N)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  let a := rationalParameter b hb.le hb1
  let η : ENNReal := (m : ENNReal)⁻¹/(m+1)
  let k := seedIndex b hb hb1 m
  let L := 10*k
  have hbulk := effective_closure_deficit b hb hb1 m hm
  intro N hN
  let U := Fintype.card (Molecule N)
  let d := U/m+1
  have hd : 0 < d := Nat.succ_pos _
  have hUd : U ≤ m*d := by
    have ht : U/m < U/m+1 := by omega
    have hh := (Nat.div_lt_iff_lt_mul hm).mp ht
    dsimp [d]
    nlinarith
  have hsub : {ω : Reaction N → Prop |
      m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*U} ⊆
      {ω | (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := by
    intro ω hω
    have hdiv := Nat.div_mul_le_self U m
    have hm1 : m-1+1 = m := by omega
    dsimp [d]
    change m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*U at hω
    nlinarith
  have hcast : (U : ENNReal) ≤ (m : ENNReal)*d := by exact_mod_cast hUd
  have hratio : (U : ENNReal)*η/d ≤ (m : ENNReal)*η := by
    calc
      _ ≤ ((m : ENNReal)*d)*η/d := by gcongr
      _ = (m : ENNReal)*η := by
        rw [mul_right_comm, ENNReal.mul_div_cancel_right (by exact_mod_cast Nat.ne_of_gt hd) (by simp)]
  have htotal : η+(m : ENNReal)*η = (m : ENNReal)⁻¹ := by
    calc
      η+(m : ENNReal)*η = (1+(m : ENNReal))*η := by rw [add_mul, one_mul]
      _ = _ := ?_
    have he : (1 : ENNReal)+m = m+1 := add_comm _ _
    rw [he]
    exact ENNReal.mul_div_cancel (by simp) (by simp)
  calc
    _ ≤ staticReactionMeasure N a {ω |
      (temporaryReactionClosure L (staticOpenReactions ω)).card+d ≤ U} := measure_mono hsub
    _ ≤ η+(U : ENNReal)*η/d := hbulk N hN d hd
    _ ≤ η+(m : ENNReal)*η := add_le_add le_rfl hratio
    _ = _ := htotal

end RAFCriticalWindowQuantitative
