/-!
# Shared Classroom Examples, Lecture 2

Author: Stefano M. Nicoletti
Website: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture02.Common.Classroom

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  -- Goal: P ∧ Q.
  -- To prove a conjunction, provide a proof of the left side and a proof of
  -- the right side.
  have hPAndQ := And.intro hP hQ
  -- hPAndQ : P ∧ Q, so it closes the goal.
  exact hPAndQ

example (P Q R : Prop) :
    (P ∧ (P → Q)) ∧ (Q → R) → R := by
  intro hArgument
  -- hArgument packages the first step and the rule from Q to R.
  have hFirstStep := hArgument.left
  -- hFirstStep : P ∧ (P → Q)
  have hP := hFirstStep.left
  -- hP : P
  have hPQ := hFirstStep.right
  -- hPQ : P → Q
  have hQR := hArgument.right
  -- hQR : Q → R
  have hQ := hPQ hP
  -- hQ : Q, by applying hPQ to hP.
  have hR := hQR hQ
  -- hR : R, by applying hQR to hQ.
  exact hR

example (P Q R : Prop) :
    ((P → R) ∧ (Q → R)) ∧ (P ∨ Q) →
    R := by
  intro hArgument
  -- hArgument contains two rules and a disjunction.
  have hRules := hArgument.left
  -- hRules : (P → R) ∧ (Q → R)
  have hPQ := hArgument.right
  -- hPQ : P ∨ Q
  have hPR := hRules.left
  -- hPR : P → R
  have hQR := hRules.right
  -- hQR : Q → R
  -- To use P ∨ Q, we must handle both cases.
  apply Or.elim hPQ
  · intro hP
    -- Case P: use hPR to produce R.
    have hR := hPR hP
    exact hR
  · intro hQ
    -- Case Q: use hQR to produce R.
    have hR := hQR hQ
    exact hR

-- ============================================================
-- CONTRAPPOSITION: (P → Q) ↔ (¬Q → ¬P)
-- ============================================================
--
-- WHAT IS CONTRAPPOSITION?
-- ========================
-- Contraposition is a logical principle stating that an implication
-- P → Q is logically equivalent to its CONTRAPOSITIVE ¬Q → ¬P.
--
-- Intuitively: "If P implies Q, then not-Q implies not-P."
-- Example: "If it rains, the ground is wet" ≡ "If the ground is not wet, it didn't rain."
--
--
-- WHY DOES THE REVERSE DIRECTION NEED CLASSICAL LOGIC?
-- ====================================================
-- FORWARD direction (P → Q) → (¬Q → ¬P):
--   This is INTUITIONISTICALLY VALID. In constructive logic, if you have
--   a proof of P → Q and a proof of P, you can CONSTRUCT a proof of Q
--   by simply applying the function hPQ to hP. The forward direction
--   works the same way in both classical and constructive logic.
--
-- REVERSE direction (¬Q → ¬P) → (P → Q):
--   This is NOT intuitionistically valid. In constructive logic, knowing
--   "not-Q implies not-P" does NOT give you a way to CONSTRUCT a proof
--   of Q from a proof of P. Constructive logic requires you to actually
--   produce a witness/proof -- you can't just say "Q must be true because
--   its negation leads to a contradiction."
--
--   The reverse direction requires some form of CLASSICAL AXIOM. All of
--   the following are equivalent in classical logic, and any one of them
--   suffices to prove contraposition:
--
--   1. Law of Excluded Middle (LEM):      ∀ P, P ∨ ¬P
--      "Every proposition is either true or false."
--
--   2. Double Negation Elimination (DNE): ∀ P, ¬¬P → P
--      "If not-not-P, then P."
--
--   3. Peirce's Law:                      ∀ P Q, ((P → Q) → P) → P
--      A deeper classical principle from which LEM and DNE can be derived.
--
--   4. Proof by Contradiction:            If (¬P → ⊥), then P
--      "If assuming not-P leads to contradiction, then P."
--
--
-- STRATEGIES FOR PROVING THE REVERSE DIRECTION
-- ============================================
-- All strategies below prove: (¬Q → ¬P) → (P → Q)
-- Given: hContrap : ¬Q → ¬P, and hP : P
-- Goal:  Q
--
-- The key insight: We have P but want Q. We can't derive Q directly from
-- the contraposition hypothesis. Instead, we use classical logic to either
-- (a) case-split on Q or (b) assume ¬Q and derive a contradiction.
-- ============================================================


-- ============================================================
-- FORWARD DIRECTION: (P → Q) → (¬Q → ¬P)
-- INTUITIONISTICALLY VALID -- no classical logic needed!
-- ============================================================
--
-- Proof explanation:
--   We are given three hypotheses:
--     hPQ   : P → Q       (P implies Q)
--     hNotQ : ¬Q          (Q is false, i.e., Q → False)
--     hP    : P           (P is true)
--   We need to prove: ¬P, which means P → False.
--
--   Proof: Apply hPQ to hP to get Q. Then apply hNotQ to that Q.
--   Since hNotQ : ¬Q = Q → False, this gives us False.
--
--   So we assume hP and derive False:
--     hPQ hP : Q
--     hNotQ (hPQ hP) : False
--   Therefore, from hP we derived False, which is ¬P.
-- ============================================================

theorem contraposition_forward (P Q : Prop) :
    (P → Q) → (¬Q → ¬P) := by
  intro hPQ hNotQ hP
  -- hPQ : P → Q, hNotQ : ¬Q, hP : P
  -- Apply hPQ to hP to get Q.
  have hQ : Q := hPQ hP
  -- Now apply hNotQ (which is Q → False) to hQ.
  -- This gives us False, which is what ¬P = P → False needs.
  exact hNotQ hQ


-- ============================================================
-- STRATEGY 1: EXCLUDED MIDDLE (LEM) -- CASE SPLIT ON Q
-- ============================================================
--
-- Core idea: Use the law of excluded middle to say "either Q is true,
-- or Q is false." Then handle each case separately.
--
-- Why this works:
--   - Case Q: Q is already true, so we're done immediately.
--   - Case ¬Q: If Q is false, then by the contraposition hypothesis
--     (¬Q → ¬P), we get ¬P. But we also have hP : P. This is a
--     contradiction (P and ¬P together give False). From False,
--     we can derive anything (ex falso quodlibet), including Q.
--
-- Why is this CLASSICAL?
--   The law of excluded middle (Q ∨ ¬Q) is not valid in constructive
--   logic. A constructive mathematician would say: "You haven't shown
--   me HOW to prove Q -- you've just said Q must be true because the
--   alternative leads to contradiction." Constructive logic requires
--   you to actually produce the proof, not just rule out the negation.
--
-- Step-by-step breakdown:
--   1. cases Classical.em Q         → splits into two subgoals
--   2. Case inl hQ : Q              → Q is true, return hQ
--   3. Case inr hNotQ : ¬Q          → Q is false
--      → hContrap hNotQ : ¬P        → by contraposition
--      → hContrap hNotQ hP : False  → contradiction with hP
--      → exfalso                    → change goal to False
--      → exact hContrap hNotQ hP    → discharge the contradiction
-- ============================================================

theorem contraposition_from_excluded_middle (P Q : Prop) :
    (¬Q → ¬P) → (P → Q) := by
  intro hContrap hP
  -- hContrap : ¬Q → ¬P, hP : P
  -- Goal: Q
  --
  -- Apply the law of excluded middle to Q.
  -- This gives us Q ∨ ¬Q; we case-split on this disjunction.
  cases Classical.em Q with
  | inl hQ =>
    -- CASE 1: Q is true.
    -- We're done immediately since our goal is Q.
    exact hQ
  | inr hNotQ =>
    -- CASE 2: ¬Q is true (i.e., Q → False).
    --
    -- From hNotQ (¬Q) and hContrap (¬Q → ¬P), we get ¬P.
    have hNotP : ¬P := hContrap hNotQ
    --
    -- Now we have both hP : P and hNotP : ¬P = P → False.
    -- Applying hNotP to hP gives us False (a contradiction).
    --
    -- Our current goal is Q, but we have a contradiction.
    -- By "ex falso quodlibet" (from false, anything follows),
    -- we can change our goal from Q to False, then close it.
    exfalso
    exact hNotP hP


-- ============================================================
-- STRATEGY 2: DOUBLE NEGATION ELIMINATION (DNE)
-- ============================================================
--
-- Core idea: Instead of directly proving Q, first prove ¬¬Q (not-not-Q).
-- Then eliminate the double negation to get Q.
--
-- Why proving ¬¬Q is easier:
--   ¬¬Q means (Q → False) → False, i.e., "it's not the case that Q is false."
--   To prove ¬¬Q, assume ¬Q (i.e., assume hNotQ : Q → False), and derive False.
--   From ¬Q and hContrap (¬Q → ¬P), we get ¬P.
--   From ¬P and hP (P), we get False.
--   So ¬¬Q is proved.
--
-- Now we have ¬¬Q but need Q. In classical logic, ¬¬Q → Q (double negation
-- elimination). We implement this by case-splitting on Q ∨ ¬Q:
--   - If Q, done.
--   - If ¬Q, apply our ¬¬Q to it to get False, then ex falso gives Q.
--
-- Note: In a full mathlib setup, you could use Classical.byContra or
-- Classical.notNotElim. Here we manually use LEM to do the elimination.
--
-- Step-by-step breakdown:
--   1. Assume hNotQ : ¬Q
--   2. Derive hNotP : ¬P from hContrap hNotQ
--   3. Derive False from hNotP hP
--   4. Thus ¬¬Q (since assuming ¬Q gave False)
--   5. Case-split on Q ∨ ¬Q
--   6. Case Q: return the proof
--   7. Case ¬Q: apply ¬¬Q to get False, then ex falso to get Q
-- ============================================================

theorem contraposition_by_double_negation (P Q : Prop) :
    (¬Q → ¬P) → (P → Q) := by
  intro hContrap hP
  -- hContrap : ¬Q → ¬P, hP : P
  -- Goal: Q
  --
  -- STEP 1: Prove ¬¬Q (double negation of Q).
  -- To prove ¬¬Q, assume ¬Q and derive False.
  have hNotNotQ : ¬¬Q := by
    intro hNotQ                         -- Assume ¬Q (i.e., Q → False).
    have hNotP : ¬P := hContrap hNotQ   -- Apply contraposition: get ¬P.
    exact hNotP hP                      -- ¬P applied to P gives False.
    --
    -- So we've proved ¬¬Q: assuming ¬Q leads to contradiction.

  -- STEP 2: Eliminate double negation to get Q.
  -- We use excluded middle on Q to case-split.
  cases Classical.em Q with
  | inl hQ =>
    -- CASE Q: Q is true. Done.
    exact hQ
  | inr hNotQ =>
    -- CASE ¬Q: We have ¬Q, and we also have hNotNotQ : ¬¬Q = (¬Q → False).
    -- Applying hNotNotQ to hNotQ gives False.
    exfalso
    exact hNotNotQ hNotQ
    --
    -- From False, anything follows, including our goal Q.


-- ============================================================
-- STRATEGY 3: PROOF BY CONTRADICTION (DIRECT)
-- ============================================================
--
-- Core idea: Assume the opposite of what you want to prove, then
-- derive a contradiction. This is the most common mathematical
-- proof technique.
--
-- We want to prove Q. So we assume ¬Q and try to derive False.
-- From ¬Q and hContrap (¬Q → ¬P), we get ¬P.
-- From ¬P and hP (P), we get False.
--
-- In Lean, `exfalso` changes the current goal from anything to False.
-- Then `exact` discharges False by providing the contradiction.
--
-- This is essentially Strategy 1 but written more directly:
-- instead of explicitly case-splitting and handling the Q case
-- separately, we just assume ¬Q and derive contradiction.
-- The Q case is handled by the excluded-middle split.
--
-- Step-by-step breakdown:
--   1. Assume hNotQ : ¬Q
--   2. Derive hNotP : ¬P from hContrap hNotQ
--   3. Derive False from hNotP hP
--   4. By ex falso, conclude Q
-- ============================================================

theorem contraposition_classical (P Q : Prop) :
    (¬Q → ¬P) → (P → Q) := by
  intro hContrap hP
  -- hContrap : ¬Q → ¬P, hP : P
  -- Goal: Q
  --
  -- Use proof by contradiction: assume ¬Q and derive False.
  -- If we can show that ¬Q leads to a contradiction, then Q must be true.
  --
  -- We use excluded middle to case-split on Q. This is the same reasoning as
  -- above, just written as a separate theorem for comparison.
  cases Classical.em Q with
  | inl hQ =>
    -- Case Q: Q is true. Done immediately.
    exact hQ
  | inr hNotQ =>
    -- Case ¬Q: assume ¬Q and derive contradiction.
    have hNotP : ¬P := hContrap hNotQ   -- From ¬Q, contraposition gives ¬P.
    exfalso                             -- Change goal to False.
    exact hNotP hP                      -- ¬P applied to P gives False.
    --
    -- The contradiction in the ¬Q case shows that ¬Q cannot hold.
    -- Therefore, Q must be true by excluded middle.


-- ============================================================
-- FULL CONTRAPOSITION EQUIVALENCE: (P → Q) ↔ (¬Q → ¬P)
-- ============================================================
--
-- This combines both directions into a single equivalence.
-- The forward direction uses intuitionistic reasoning.
-- The reverse direction uses classical reasoning (excluded middle).
-- ============================================================

theorem contraposition (P Q : Prop) :
    (P → Q) ↔ (¬Q → ¬P) := by
  apply Iff.intro
  · -- FORWARD DIRECTION: (P → Q) → (¬Q → ¬P)
    -- Intuitionistically valid: works in both classical and constructive logic.
    exact contraposition_forward P Q
  · -- REVERSE DIRECTION: (¬Q → ¬P) → (P → Q)
    -- Requires classical logic (excluded middle).
    exact contraposition_from_excluded_middle P Q


-- ============================================================
-- UNIVERSAL FORM: ∀ (P Q : Prop), (P → Q) ↔ (¬Q → ¬P)
-- ============================================================
--
-- The same theorem but quantified over all propositions P and Q.
-- This is the most general form of contraposition.
-- ============================================================

theorem forall_contraposition :
    ∀ (P Q : Prop), (P → Q) ↔ (¬Q → ¬P) := by
  intro P Q
  -- Now P and Q are arbitrary propositions.
  exact contraposition P Q


-- ============================================================
-- MODUS TOLLENS: (P → Q) → ¬Q → ¬P
-- ============================================================
--
-- Modus tollens is the forward direction of contraposition when we keep
-- `(P → Q)` and `¬Q` as separate hypotheses.
--
-- "If P implies Q, and Q is false, then P is false."
--
-- Example: "If it rains, the ground is wet." (P → Q)
--          "The ground is not wet." (¬Q)
--          Therefore: "It didn't rain." (¬P)
-- ============================================================

theorem modus_tollens (P Q : Prop) :
    (P → Q) → ¬Q → ¬P := by
  intro hPQ hNotQ hP
  -- hPQ : P → Q, hNotQ : ¬Q, hP : P
  -- Goal: False
  exact hNotQ (hPQ hP)

end Course.Shared.Lecture02.Common.Classroom
