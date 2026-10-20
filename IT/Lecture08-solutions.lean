/-!
# Soluzioni, Lezione 8: verifica del software, automazione e LLM in Lean

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture08.IT.Solutions

-- 1. Una dimostrazione diretta. Il suggerimento di `exact?` può essere diverso.
example (P Q : Prop) (hPQ : P ∧ Q) : Q := by
  exact hPQ.right

-- 2. In questo caso `apply?` trova una dimostrazione completa.
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q ∧ P := by
  exact ⟨hPQ hP, hP⟩

-- 3. `simp? [hP]` propone queste regole per la semplificazione.
example (P Q : Prop) (hP : P) : (P ∧ Q) ↔ Q := by
  simp only [hP, true_and]

-- 4. `grind?` trova la dimostrazione usando le assunzioni locali.
example (P Q R S : Prop) (hPQ : P ∨ Q)
    (hPR : P → R) (hQS : Q → S) : R ∨ S := by
  grind only

-- ============================================================
-- VERIFICA DI UN PROGRAMMA SU LISTE
-- ============================================================

inductive Lista (α : Type) where
  | vuota
  | cons (testa : α) (coda : Lista α)

open Lista

def mappa {α β : Type} (f : α → β) (xs : Lista α) : Lista β :=
  match xs with
  | vuota => vuota
  | cons x xs => cons (f x) (mappa f xs)

theorem mappa_identita {α : Type} (xs : Lista α) :
    mappa (fun x => x) xs = xs := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [mappa, ih]

theorem mappa_composizione
    {α β γ : Type} (f : α → β) (g : β → γ) (xs : Lista α) :
    mappa g (mappa f xs) = mappa (fun x => g (f x)) xs := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [mappa, ih]

def concatena {α : Type} (xs ys : Lista α) : Lista α :=
  match xs with
  | vuota => ys
  | cons x xs => cons x (concatena xs ys)

-- 8. La concatenazione analizza la prima lista, quindi facciamo induzione su xs.
theorem mappa_concatena {α β : Type} (f : α → β) (xs ys : Lista α) :
    mappa f (concatena xs ys) = concatena (mappa f xs) (mappa f ys) := by
  induction xs with
  | vuota =>
      rfl
  | cons x xs ih =>
      simp [concatena, mappa, ih]

-- 9. Il calcolo verifica queste liste concrete, non tutte le liste possibili.
example : ([1, 3] ++ [5, 7] : List Nat) = [1, 3, 5, 7] := by
  decide

-- 10. I due limiti implicano il limite richiesto, per qualunque numero di pagine.
example (pagineEva pagineMarta : Nat)
    (hEva : 12 ≤ pagineEva) (hMarta : pagineEva + 5 ≤ pagineMarta) :
    17 ≤ pagineMarta := by
  omega

end Course.Shared.Lecture08.IT.Solutions
