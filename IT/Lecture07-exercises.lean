/-!
# Esercizi, Lezione 7: induzione, semplificazione e verifica del software

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

def prodotto (m n : Naturale) : Naturale :=
  match n with
  | zero => zero
  | succ n => somma m (prodotto m n)

-- Risultati già ottenuti nella Lezione 6.
theorem somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  rfl

theorem somma_uno_sinistra (n : Naturale) :
    somma uno n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rw [ih]

-- 1. Dimostrare per induzione l'analogo risultato per due.
theorem somma_due_sinistra (n : Naturale) :
    somma due n = succ (succ n) := by
  sorry

-- 2. Dimostrare questa particolare forma di associatività. Scegliere la
-- variabile d'induzione guardando le somme che devono ridursi.
theorem somma_con_uno_assoc (m n : Naturale) :
    somma (somma m uno) n = somma m (somma uno n) := by
  sorry

-- 3. Combinare somma e doppio in una dimostrazione per induzione.
theorem doppio_somma_uno (n : Naturale) :
    doppio (somma uno n) = somma due (doppio n) := by
  sorry

-- 4. Dimostrare per induzione che uno moltiplicato per ogni naturale
-- restituisce quel naturale.
theorem prodotto_uno_sinistra (n : Naturale) :
    prodotto uno n = n := by
  sorry

-- 5. Rendere `somma_uno_sinistra` disponibile nel simp-set soltanto dentro
-- questa sezione. Chiudere poi il goal usando `simp`, senza nominare il lemma.
section SemplificazioneLocale

example (n : Naturale) : somma uno n = succ n := by
  sorry

end SemplificazioneLocale

-- ============================================================
-- VERIFICA DI UN PROGRAMMA SU LISTE
-- ============================================================

inductive Lista (α : Type) where
  | vuota
  | cons (testa : α) (coda : Lista α)

open Lista

-- 6. Definire `mappa`: deve applicare `f` a ogni elemento della lista,
-- conservando la stessa struttura.
-- Per esempio, applicando `succ` alla lista `cons zero (cons uno vuota)`
-- dobbiamo ottenere `cons uno (cons due vuota)`.
def mappa {α β : Type} (f : α → β) (xs : Lista α) : Lista β :=
  sorry

-- 7. Verificare che applicare la funzione identità a ogni elemento non
-- modifichi la lista. Usare l'induzione e `simp` con la definizione di `mappa`.
theorem mappa_identita {α : Type} (xs : Lista α) :
    mappa (fun x => x) xs = xs := by
  sorry

-- 8. Verificare che due applicazioni successive di `mappa` equivalgano a una
-- sola applicazione con la funzione composta. Anche qui usare induzione e
-- `simp`.
theorem mappa_composizione
    {α β γ : Type} (f : α → β) (g : β → γ) (xs : Lista α) :
    mappa g (mappa f xs) = mappa (fun x => g (f x)) xs := by
  sorry

end Course.Shared.Lecture07.IT.Exercises
