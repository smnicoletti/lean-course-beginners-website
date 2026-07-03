import Course.Shared.Lecture02.Common.Classroom

/-!
# Lecture 2: Introduction and Elimination Rules

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/

Date: July 6, 2026.
Duration: 2 hours.

-/

namespace Course.Shared.Lecture02.EN.Classroom

open Course.Shared.Lecture02.Common.Classroom

-- Read connectives through their introduction and elimination rules.

-- ============================================================
-- IMPLICATION: P -> Q
-- ============================================================

-- Implication introduction.
-- To prove `P -> Q`, we temporarily assume `P` and construct `Q`.
-- Rule: if, assuming P, we can prove Q, then we have P -> Q.
theorem lecture02_imp_intro (P Q : Prop) (hQ : Q) :
    P → Q := by
  intro hP
  -- hP : P is the temporary assumption introduced by the rule.
  exact hQ

-- Implication elimination.
-- Rule: from P -> Q and P we obtain Q. This is modus ponens.
theorem lecture02_imp_elim (P Q : Prop) :
    (P → Q) → P → Q := by
  intro hPQ
  intro hP
  have hQ := hPQ hP
  exact hQ

-- ============================================================
-- CONJUNCTION: P /\ Q
-- ============================================================

theorem lecture02_and_intro (P Q : Prop) (hP : P) (hQ : Q) :
    P ∧ Q := by
  -- Introduction rule: from P and Q we obtain P /\ Q.
  have hPAndQ := And.intro hP hQ
  exact hPAndQ

theorem lecture02_and_intro_with_apply (P Q : Prop) (hP : P) (hQ : Q) :
    P ∧ Q := by
  -- Same rule, using the constructor explicitly as a tactic. Notice the creation of multiple subgoals.
  apply And.intro
  · exact hP
  · exact hQ

theorem lecture02_and_elim_left (P Q : Prop) :
    P ∧ Q → P := by
  intro hPAndQ
  -- Left elimination rule: from P /\ Q we obtain P.
  exact hPAndQ.left

theorem lecture02_and_elim_right (P Q : Prop) :
    P ∧ Q → Q := by
  intro hPAndQ
  -- Right elimination rule: from P /\ Q we obtain Q.
  exact hPAndQ.right

-- ============================================================
-- DISJUNCTION: P \/ Q
-- ============================================================

theorem lecture02_or_intro_left (P Q : Prop) :
    P → P ∨ Q := by
  intro hP
  -- Left introduction rule: from P we obtain P \/ Q.
  exact Or.inl hP

theorem lecture02_or_intro_left_with_apply (P Q : Prop) :
    P → P ∨ Q := by
  intro hP
  -- Same rule, using the left constructor explicitly.
  apply Or.inl
  exact hP

theorem lecture02_or_intro_right (P Q : Prop) :
    Q → P ∨ Q := by
  intro hQ
  -- Right introduction rule: from Q we obtain P \/ Q.
  exact Or.inr hQ

theorem lecture02_or_intro_right_with_apply (P Q : Prop) :
    Q → P ∨ Q := by
  intro hQ
  -- Same rule, using the right constructor explicitly.
  apply Or.inr
  exact hQ

theorem lecture02_or_elim (P Q : Prop) :
    P ∨ Q → Q ∨ P := by
  intro hPOrQ
  -- Elimination rule: from P \/ Q we must treat the P case and the Q case.
  -- In both cases we must prove the same goal, here Q \/ P.
  cases hPOrQ with
  | inl hP =>
      -- Case 1: we have a proof of P.
      exact Or.inr hP
  | inr hQ =>
      -- Case 2: we have a proof of Q.
      exact Or.inl hQ

theorem lecture02_or_elim_with_or_elim (P Q : Prop) :
    P ∨ Q → Q ∨ P := by
  intro hPOrQ
  -- `Or.elim` is the same rule: one proof for the P case and one for the Q case.
  apply Or.elim hPOrQ
  · intro hP
    exact Or.inr hP
  · intro hQ
    exact Or.inl hQ

-- ============================================================
-- FALSE AND NEGATION
-- ============================================================

theorem lecture02_false_elim_with_apply (P : Prop) :
    False → P := by
  intro hFalse
  -- Elimination rule: from False we can obtain any proposition P.
  apply False.elim -- exfalso
  exact hFalse

theorem lecture02_false_elim (P : Prop) :
    False → P := by
  intro hFalse
  -- Same rule, using `exact`.
  exact False.elim hFalse

-- Now we look at the shape negation has in Lean.
-- How do we show that P and its negation produce a contradiction?
theorem lecture02_not_elim (P : Prop) :
    P → ¬P → False := by
  intro hP
  intro hNotP
  -- Elimination rule: P and not P produce False.
  exact hNotP hP

-- What is not P? It is P -> False. Here is an example:
theorem lecture02_not_intro (P Q : Prop) :
    (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hNotQ
  -- Introduction rule: to prove not P, assume P and derive False.
  -- Observe how the goal changes.
  intro hP
  have hQ := hPQ hP
  exact hNotQ hQ

theorem lecture02_wine_modus_tollens
    (DrinkWine Drunk : Prop) :
    ((DrinkWine → Drunk) ∧ ¬Drunk) → ¬DrinkWine := by
  intro assumption
  have hDrinkDrunk := assumption.left
  have hNotDrunk := assumption.right
  intro hDrinkWine
  have hDrunk := hDrinkDrunk hDrinkWine
  exact hNotDrunk hDrunk

-- ============================================================
-- BICONDITIONAL: P <-> Q
-- ============================================================

theorem lecture02_iff_intro (P Q : Prop) :
    (P → Q) → (Q → P) → (P ↔ Q) := by
  intro hPQ
  intro hQP
  -- Introduction rule: from P -> Q and Q -> P we obtain P <-> Q.
  apply Iff.intro
  · exact hPQ
  · exact hQP
  -- Or simply: exact Iff.intro hPQ hQP

theorem lecture02_iff_elim_left (P Q : Prop) :
    (P ↔ Q) → P → Q := by
  intro hIff
  intro hP
  -- Left-to-right elimination rule: `Iff.mp` extracts the direction P -> Q.
  exact Iff.mp hIff hP

theorem lecture02_iff_elim_right (P Q : Prop) :
    (P ↔ Q) → Q → P := by
  intro hIff
  intro hQ
  -- Right-to-left elimination rule: `Iff.mpr` extracts the direction Q -> P.
  exact Iff.mpr hIff hQ

-- ============================================================
-- CONTRAPOSITION
-- ============================================================

theorem lecture02_contraposition_forward (P Q : Prop) :
    (P → Q) → (¬Q → ¬P) := by
  intro hPQ
  intro hNotQ
  -- Goal: not P, that is P -> False.
  intro hP
  have hQ := hPQ hP
  exact hNotQ hQ

theorem lecture02_contraposition_classical (P Q : Prop) :
    (¬Q → ¬P) → (P → Q) := by
  intro hContrap
  intro hP
  -- Goal: Q.
  -- Constructively we do not know how to build Q directly from these data.
  -- We therefore use excluded middle on Q.
  cases Classical.em Q with
  | inl hQ =>
      -- Case Q: we have exactly the goal.
      exact hQ
  | inr hNotQ =>
      -- Case not Q: hContrap gives not P, contradicting hP.
      have hNotP := hContrap hNotQ
      exfalso
      exact hNotP hP

theorem lecture02_contraposition_full (P Q : Prop) :
    (P → Q) ↔ (¬Q → ¬P) := by
  apply Iff.intro
  · -- Constructive direction.
    exact lecture02_contraposition_forward P Q
  · -- Classical direction.
    exact lecture02_contraposition_classical P Q

-- ============================================================
-- PROOF BY CONTRADICTION
-- ============================================================

theorem lecture02_proof_by_contradiction (P : Prop) :
    (¬P → False) → P := by
  intro hContradiction
  -- Proof by contradiction:
  -- assuming not P leads to False, so classically we conclude P. We use excluded middle on P:
  cases Classical.em P with
  | inl hP =>
      exact hP
  | inr hNotP =>
      exfalso
      exact hContradiction hNotP

theorem lecture02_by_contradiction_classical (P : Prop) :
    (¬P → False) → P := by
  intro hContradiction
  -- The same classical proof, using the dedicated principle directly.
  exact Classical.byContradiction hContradiction

-- ============================================================
-- MORE DEVELOPED EXAMPLES
-- ============================================================

-- Natural language: if we have an assumption, if a consequence follows from
-- the assumption, and if a conclusion follows from the consequence, then we
-- have the conclusion.
example (Assumption Consequence Conclusion : Prop) :
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
  -- We do not know which side of the `\/` is valid, so we consider both cases.
  cases hRainsOrSnows with
  | inl hRains =>
      exact hRainsUmbrella hRains
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
  · intro hRains
    exact hRainsUmbrella hRains
  · intro hSnows
    exact hSnowsUmbrella hSnows

-- Natural language: if the source is authentic or the data are coherent, and
-- each of the two cases supports the thesis, and if a supported thesis makes
-- the conclusion plausible, then the conclusion is plausible.
example (AuthenticSource CoherentData SupportedThesis PlausibleConclusion : Prop) :
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

-- Now we look at a classical proof involving double negation.
theorem lecture02_double_negation_classical (P : Prop) :
    ¬¬P → P := by
  intro hNotNotP
  -- We use excluded middle: either P, or not P.
  cases Classical.em P with
  | inl hP =>
      exact hP
  | inr hNotP =>
      -- In the not P case, hNotNotP produces a contradiction.
      exfalso -- apply False.elim
      exact hNotNotP hNotP

end Course.Shared.Lecture02.EN.Classroom
