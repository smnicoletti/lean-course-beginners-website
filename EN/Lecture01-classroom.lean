/-!
# Lecture 1: What Is a Theorem Prover?

Author: Stefano M. Nicoletti
Website: https://stefanonicoletti.com/

Date: June 22, 2026.
Duration: 2 hours.

-/

namespace Course.Shared.Lecture01.EN.Classroom

-- Types, #check, #eval

#check Prop
#check Nat
#check Float

--variable(a : Nat)
--#check a

#eval 3 + 1
#eval 3.5 + 2

-- Natural language: if we assume that it rains, then we can conclude that it rains.
example (Rains : Prop) (hRains : Rains) : Rains := by
  sorry

-- Natural language: if we assume that it rains, then we can conclude that it rains.
example (Rains : Prop) (hRains : Rains) : Rains := by
  exact hRains

-- Natural language: if it rains, then it rains.
example (Rains : Prop) : Rains → Rains := by
  intro h -- intro informativeName, any name that helps us remember the hypothesis
  exact h

-- Natural language: if it rains then I take the umbrella, and it rains, then
-- this implies that I take the umbrella.
example (Rains TakeUmbrella : Prop) :
    ((Rains → TakeUmbrella) ∧ Rains) → TakeUmbrella := by
  intro hypotheses
  have hRainsUmbrella := hypotheses.left
  have hRains := hypotheses.right
  have hTakeUmbrella := hRainsUmbrella hRains
  exact hTakeUmbrella

-- Shorter proof
example (Rains TakeUmbrella : Prop) :
    ((Rains → TakeUmbrella) ∧ Rains) → TakeUmbrella := by
  intro h
  exact h.left h.right

-- We declare the assumptions explicitly in the preamble of the example.
-- Natural language: assume that, if it rains, then I take the umbrella;
-- assume also that it rains; therefore I take the umbrella.
example (Rains TakeUmbrella : Prop)
    (hRainsUmbrella : Rains → TakeUmbrella) (hRains : Rains) :
    TakeUmbrella := by
  exact hRainsUmbrella hRains

-- We encode, verify, and use the valid reasoning schema. Braces mark implicit
-- arguments: Lean can often infer them from the type of the hypotheses.
-- Natural language: if P is true and Q follows from P, then Q is true.
theorem lecture01_modus_ponens
    {P Q : Prop}
    (hP : P) (hPQ : P → Q) :
    Q := by
  exact hPQ hP

example (Rains TakeUmbrella : Prop)
    (hRainsUmbrella : Rains → TakeUmbrella) (hRains : Rains) :
    TakeUmbrella := by
  exact lecture01_modus_ponens hRains hRainsUmbrella

-- Natural language: if we have an assumption, if a consequence follows from
-- the assumption, and if a conclusion follows from the consequence, then we
-- have the conclusion.
theorem lecture01_informal_argument_schema
    (Assumption Consequence Conclusion : Prop) :
    (Assumption ∧ (Assumption → Consequence)) ∧
      (Consequence → Conclusion) →
    Conclusion := by
  intro hArgument
  have hFirstStep := hArgument.left
  have hAssumption := hFirstStep.left
  have hStep1 := hFirstStep.right
  have hStep2 := hArgument.right
  have hConsequence := hStep1 hAssumption
  have hConclusion := hStep2 hConsequence
  exact hConclusion

-- Natural language: if I drink wine then I get drunk; but I am not drunk;
-- therefore I did not drink wine.
theorem lecture01_wine_example
    (DrinkWine Drunk : Prop) :
    ((DrinkWine → Drunk) ∧ ¬Drunk) → ¬DrinkWine := by
  intro hArgument
  have hRule := hArgument.left
  have hNotDrunk := hArgument.right
  intro hDrinkWine
  have hDrunk := hRule hDrinkWine
  exact hNotDrunk hDrunk

-- Natural language: if it rains or it snows, and in each of the two cases I
-- take the umbrella, then I take the umbrella.
example (Rains Snows TakeUmbrella : Prop) :
    ((Rains → TakeUmbrella) ∧
      (Snows → TakeUmbrella)) ∧
    (Rains ∨ Snows) →
    TakeUmbrella := by
  intro hArgument
  have hRules := hArgument.left
  have hRainsOrSnows := hArgument.right
  have hRainsUmbrella := hRules.left
  have hSnowsUmbrella := hRules.right
  -- We do not know which side of the `∨` is valid, so we consider both cases.
  cases hRainsOrSnows with
  -- First case: `Rains ∨ Snows` is true because `Rains` holds; prove `TakeUmbrella`.
  | inl hRains =>
      exact hRainsUmbrella hRains
  -- Second case: `Rains ∨ Snows` is true because `Snows` holds; prove `TakeUmbrella`.
  | inr hSnows =>
      exact hSnowsUmbrella hSnows

-- The same proof, using `Or.elim` directly.
example (Rains Snows TakeUmbrella : Prop) :
    ((Rains → TakeUmbrella) ∧
      (Snows → TakeUmbrella)) ∧
    (Rains ∨ Snows) →
    TakeUmbrella := by
  intro hArgument
  have hRules := hArgument.left
  have hRainsOrSnows := hArgument.right
  have hRainsUmbrella := hRules.left
  have hSnowsUmbrella := hRules.right
  apply Or.elim hRainsOrSnows
  -- If the left side of the `∨` holds, namely `Rains`,
  -- we use the rule `Rains → TakeUmbrella`.
  · intro hRains
    exact hRainsUmbrella hRains
  -- If the right side of the `∨` holds, namely `Snows`,
  -- we use the rule `Snows → TakeUmbrella`.
  · intro hSnows
    exact hSnowsUmbrella hSnows

-- Natural language: if the source is authentic or the data are coherent, and
-- each of the two cases supports the thesis, and if a supported thesis makes
-- the conclusion plausible, then the conclusion is plausible.
theorem lecture01_history_of_science_example
    (AuthenticSource CoherentData SupportedThesis PlausibleConclusion : Prop) :
    ((AuthenticSource ∨ CoherentData) ∧
      ((AuthenticSource → SupportedThesis) ∧
        (CoherentData → SupportedThesis))) ∧
    (SupportedThesis → PlausibleConclusion) →
    PlausibleConclusion := by
  intro hArgument
  have hFirstStep := hArgument.left
  have hSourceOrData := hFirstStep.left
  have hSupportRules := hFirstStep.right
  have hSourceSupports := hSupportRules.left
  have hDataSupport := hSupportRules.right
  have hSupportConcludes := hArgument.right
  have hThesis :=
    Or.elim hSourceOrData hSourceSupports hDataSupport
  have hConclusion := hSupportConcludes hThesis
  exact hConclusion

end Course.Shared.Lecture01.EN.Classroom
