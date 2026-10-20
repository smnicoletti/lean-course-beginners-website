/-!
# Esercizi, Lezione 7: induzione e semplificazione

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture07.IT.Exercises

inductive Naturale where
  | zero
  | succ (n : Naturale)

open Naturale

def uno : Naturale := succ zero
def due : Naturale := succ uno

def somma (m n : Naturale) : Naturale :=
  match n with
  | zero => m
  | succ n => succ (somma m n)

def doppio (n : Naturale) : Naturale :=
  match n with
  | zero => zero
  | succ n => succ (succ (doppio n))

-- 1. Definire ricorsivamente il prodotto di due naturali. La definizione deve
-- analizzare il secondo argomento, come fa `somma`.
def prodotto (m n : Naturale) : Naturale := by
  sorry

-- Un risultato visto nella Lezione 6.
theorem somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  rfl

-- Riprendiamo inoltre un risultato proposto negli esercizi della Lezione 6.
theorem somma_uno_sinistra (n : Naturale) :
    somma uno n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rw [ih]

-- 2. Dimostrare per induzione l'analogo risultato per due.
theorem somma_due_sinistra (n : Naturale) :
    somma due n = succ (succ n) := by
  sorry

-- 3. Dimostrare questa particolare forma di associatività. Scegliere la
-- variabile d'induzione guardando le somme che devono ridursi.
theorem somma_con_uno_assoc (m n : Naturale) :
    somma (somma m uno) n = somma m (somma uno n) := by
  sorry

-- 4. Combinare somma e doppio in una dimostrazione per induzione.
theorem doppio_somma_uno (n : Naturale) :
    doppio (somma uno n) = somma due (doppio n) := by
  sorry

-- 5. Dimostrare per induzione che uno moltiplicato per ogni naturale
-- restituisce quel naturale.
theorem prodotto_uno_sinistra (n : Naturale) :
    prodotto uno n = n := by
  sorry

-- 6. Rendere `somma_uno_sinistra` disponibile nel simp-set soltanto dentro
-- questa sezione. Chiudere poi il goal usando `simp`, senza nominare il lemma.
section SemplificazioneLocale

example (n : Naturale) : somma uno n = succ n := by
  sorry

end SemplificazioneLocale

-- 7. Dimostrare l'associatività della somma. Scegliere la variabile
-- d'induzione osservando quale argomento viene analizzato da `somma`.
theorem somma_assoc (a b c : Naturale) :
    somma (somma a b) c = somma a (somma b c) := by
  sorry

-- I due risultati seguenti permettono di trattare `zero` e `succ` quando
-- compaiono nel primo argomento della somma.
theorem zero_somma (n : Naturale) : somma zero n = n := by
  sorry

theorem succ_somma (m n : Naturale) :
    somma (succ m) n = succ (somma m n) := by
  sorry

-- 8. Dimostrare la commutatività combinando le equazioni disponibili sui due
-- argomenti della somma.
theorem somma_comm (a b : Naturale) :
    somma a b = somma b a := by
  sorry

theorem doppio_succ (n : Naturale) :
    doppio (succ n) = succ (succ (doppio n)) := by
  rfl

-- 9. Dimostrazione conclusiva: il doppio di una somma è la somma dei doppi.
theorem doppio_somma (m n : Naturale) :
    doppio (somma m n) = somma (doppio m) (doppio n) := by
  sorry

end Course.Shared.Lecture07.IT.Exercises
