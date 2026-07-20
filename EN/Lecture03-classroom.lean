/-!
# Lecture 3: From Natural Deduction to Proofs in Lean

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Date: 20 July 2026.
Duration: 2 hours.
-/

namespace Course.Shared.Lecture03.EN.Classroom

-- Every example follows the same path: a natural-deduction rule, its reading
-- in natural language, a concrete instance, and a term built in the proof state.

-- ============================================================
-- IMPLICATION: A → B
-- ============================================================

-- Implication introduction, →I.
-- To prove `A → B`, we introduce the temporary assumption `A` and construct `B`.
-- Example: if it rains and it is cold, then it rains.
theorem lecture03_imp_intro
    (Rains IsCold : Prop) :
    Rains ∧ IsCold → Rains := by
  intro hRainsAndIsCold
  have hRains := hRainsAndIsCold.left
  exact hRains

-- Implication elimination, →E: modus ponens.
-- From `A → B` and `A`, we obtain `B`.
-- Example: if it rains, I take the umbrella; it rains; therefore I take it.
theorem lecture03_imp_elim
    (Rains TakeUmbrella : Prop)
    (hRainsUmbrella : Rains → TakeUmbrella)
    (hRains : Rains) :
    TakeUmbrella := by
  have hTakeUmbrella := hRainsUmbrella hRains
  exact hTakeUmbrella

-- ============================================================
-- CONJUNCTION: A ∧ B
-- ============================================================

-- Conjunction introduction, ∧I.
-- From a proof of A and a proof of B, we construct a proof of A ∧ B.
theorem lecture03_and_intro
    (Rains IsCold : Prop)
    (hRains : Rains)
    (hIsCold : IsCold) :
    Rains ∧ IsCold := by
  apply And.intro
  · exact hRains
  · exact hIsCold

-- Left conjunction elimination, ∧Eₗ.
theorem lecture03_and_elim_left
    (Rains IsCold : Prop)
    (hRainsAndIsCold : Rains ∧ IsCold) :
    Rains := by
  have hRains := hRainsAndIsCold.left
  exact hRains

-- Right conjunction elimination, ∧Eᵣ.
theorem lecture03_and_elim_right
    (Rains IsCold : Prop)
    (hRainsAndIsCold : Rains ∧ IsCold) :
    IsCold := by
  have hIsCold := hRainsAndIsCold.right
  exact hIsCold

-- ============================================================
-- DISJUNCTION: A ∨ B
-- ============================================================

-- Left disjunction introduction, ∨Iₗ.
theorem lecture03_or_intro_left
    (Rains Snows : Prop)
    (hRains : Rains) :
    Rains ∨ Snows := by
  apply Or.inl
  exact hRains

-- Right disjunction introduction, ∨Iᵣ.
theorem lecture03_or_intro_right
    (Rains Snows : Prop)
    (hSnows : Snows) :
    Rains ∨ Snows := by
  apply Or.inr
  exact hSnows

-- Disjunction elimination, ∨E.
-- From `A ∨ B`, `A → C`, and `B → C`, we obtain C by cases.
theorem lecture03_or_elim
    (Rains Snows TakeUmbrella : Prop)
    (hRainsOrSnows : Rains ∨ Snows)
    (hRainsUmbrella : Rains → TakeUmbrella)
    (hSnowsUmbrella : Snows → TakeUmbrella) :
    TakeUmbrella := by
  cases hRainsOrSnows with
  | inl hRains =>
      have hTakeUmbrella := hRainsUmbrella hRains
      exact hTakeUmbrella
  | inr hSnows =>
      have hTakeUmbrella := hSnowsUmbrella hSnows
      exact hTakeUmbrella

-- ============================================================
-- NEGATION AND FALSITY
-- ============================================================

-- Negation introduction, ¬I.
-- To prove `¬A`, we introduce A and derive False.
theorem lecture03_not_intro
    (DrinkCoffee StayAwake : Prop)
    (hCoffeeAwake : DrinkCoffee → StayAwake)
    (hNotAwake : ¬StayAwake) :
    ¬DrinkCoffee := by
  intro hDrinkCoffee
  have hStayAwake := hCoffeeAwake hDrinkCoffee
  have hContradiction : False := hNotAwake hStayAwake
  exact hContradiction

-- Negation elimination, ¬E.
-- From ¬A and A, we obtain False.
theorem lecture03_not_elim
    (LabOpen : Prop)
    (hLabOpen : LabOpen)
    (hLabNotOpen : ¬LabOpen) :
    False := by
  have hContradiction := hLabNotOpen hLabOpen
  exact hContradiction

-- Truth introduction, ⊤I.
theorem lecture03_true_intro : True := by
  exact True.intro -- Alternatively: trivial

-- Falsity elimination, ⊥E.
theorem lecture03_false_elim
    (Rains : Prop)
    (hContradiction : False) :
    Rains := by
  apply False.elim -- Alternatively: exfalso
  exact hContradiction

-- ============================================================
-- BICONDITIONAL: A ↔ B
-- ============================================================

-- Biconditional introduction, ↔I: construct both directions.
theorem lecture03_iff_intro
    (Rains IsCold : Prop) :
    Rains ∧ IsCold ↔ IsCold ∧ Rains := by
  apply Iff.intro
  · intro hRainsAndIsCold
    apply And.intro
    · exact hRainsAndIsCold.right
    · exact hRainsAndIsCold.left
  · intro hIsColdAndRains
    apply And.intro
    · exact hIsColdAndRains.right
    · exact hIsColdAndRains.left

-- Left-to-right biconditional elimination, ↔Eₗ.
theorem lecture03_iff_elim_left
    (EvenNumber DivisibleByTwo : Prop)
    (hEquivalence : EvenNumber ↔ DivisibleByTwo)
    (hEvenNumber : EvenNumber) :
    DivisibleByTwo := by
  have hDirection := Iff.mp hEquivalence
  have hDivisibleByTwo := hDirection hEvenNumber
  exact hDivisibleByTwo

-- Right-to-left biconditional elimination, ↔Eᵣ.
theorem lecture03_iff_elim_right
    (EvenNumber DivisibleByTwo : Prop)
    (hEquivalence : EvenNumber ↔ DivisibleByTwo)
    (hDivisibleByTwo : DivisibleByTwo) :
    EvenNumber := by
  have hDirection := Iff.mpr hEquivalence
  have hEvenNumber := hDirection hDivisibleByTwo
  exact hEvenNumber

end Course.Shared.Lecture03.EN.Classroom
