/-!
# Esercizi, Lezione 8: verifica del software, automazione e LLM in Lean

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture08.IT.Exercises

-- AUTOMAZIONE E SUGGERIMENTI
-- Nei prossimi quattro esercizi provare la tattica indicata, leggere il
-- suggerimento e sostituire la ricerca con il comando proposto da Lean.

-- 1. Ricavare Q dalla congiunzione. Chiedere un suggerimento a `exact?`.
example (P Q : Prop) (hPQ : P ∧ Q) : Q := by
  sorry

-- 2. Chiedere un suggerimento a `apply?`. In questo caso lascia goal aperti
-- oppure trova una dimostrazione completa?
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q ∧ P := by
  sorry

-- 3. Semplificare la proposizione con `simp?`.
-- Leggere le regole elencate nel suggerimento.
example (P Q : Prop) (hP : P) : (P ∧ Q) ↔ Q := by
  sorry

-- 4. Sappiamo che vale P oppure Q. Da P segue R e da Q segue S.
-- Dimostrare R ∨ S con l'aiuto di `grind?`.
example (P Q R S : Prop) (hPQ : P ∨ Q)
    (hPR : P → R) (hQS : Q → S) : R ∨ S := by
  sorry

-- ============================================================
-- VERIFICA DI UN PROGRAMMA SU LISTE
-- ============================================================

inductive Lista (α : Type) where
  | vuota
  | cons (testa : α) (coda : Lista α)

open Lista

-- 5. Definire `mappa`: deve applicare `f` a ogni elemento della lista,
-- conservando la stessa struttura.
-- Per esempio, applicando `Nat.succ` alla lista `cons 0 (cons 1 vuota)`
-- dobbiamo ottenere `cons 1 (cons 2 vuota)`.
def mappa {α β : Type} (f : α → β) (xs : Lista α) : Lista β :=
  sorry

-- 6. Verificare che applicare la funzione identità a ogni elemento non
-- modifichi la lista. Usare l'induzione e `simp` con la definizione di `mappa`.
theorem mappa_identita {α : Type} (xs : Lista α) :
    mappa (fun x => x) xs = xs := by
  sorry

-- 7. Verificare che due applicazioni successive di `mappa` equivalgano a una
-- sola applicazione con la funzione composta. Anche qui usare induzione e
-- `simp`.
theorem mappa_composizione
    {α β γ : Type} (f : α → β) (g : β → γ) (xs : Lista α) :
    mappa g (mappa f xs) = mappa (fun x => g (f x)) xs := by
  sorry

-- Riprendiamo la concatenazione definita in Classroom.
def concatena {α : Type} (xs ys : Lista α) : Lista α :=
  match xs with
  | vuota => ys
  | cons x xs => cons x (concatena xs ys)

-- 8. Applicare `f` dopo aver concatenato due liste dà lo stesso risultato
-- che applicarla separatamente alle due liste e poi concatenarle.
-- Scegliere su quale lista fare induzione.
theorem mappa_concatena {α β : Type} (f : α → β) (xs ys : Lista α) :
    mappa f (concatena xs ys) = concatena (mappa f xs) (mappa f ys) := by
  sorry

-- CALCOLO E ARITMETICA

-- 9. Qui usiamo le liste e i naturali della libreria standard.
-- Verificare con `decide` questa uguaglianza fra liste concrete.
-- Che cosa cambia rispetto alla proprietà generale dell'esercizio 8?
example : ([1, 3] ++ [5, 7] : List Nat) = [1, 3, 5, 7] := by
  sorry

-- 10. Eva ha letto almeno 12 pagine. Marta ne ha lette almeno 5 più di Eva. Quale tattica/automazione può aiutarci qui?
example (pagineEva pagineMarta : Nat)
    (hEva : 12 ≤ pagineEva) (hMarta : pagineEva + 5 ≤ pagineMarta) :
    17 ≤ pagineMarta := by
  sorry

end Course.Shared.Lecture08.IT.Exercises
