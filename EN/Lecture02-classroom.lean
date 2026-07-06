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

end Course.Shared.Lecture02.EN.Classroom
