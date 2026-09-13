/-!
# Soluzioni, Lezione 6

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.IT.Solutions

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

-- La moltiplicazione ripete `m` tante volte quanto indica il secondo argomento.
def prodotto (m n : Naturale) : Naturale :=
  match n with
  | zero => zero
  | succ n => somma m (prodotto m n)

theorem prodotto_zero_destra (m : Naturale) :
    prodotto m zero = zero := by
  rfl

theorem prodotto_succ_destra (m n : Naturale) :
    prodotto m (succ n) = somma m (prodotto m n) := by
  rfl

theorem somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  rfl

theorem riscrivi_primo_argomento
    (a b : Naturale)
    (h : a = b) :
    somma a zero = b := by
  rw [h]
  rfl

theorem somma_uno_sinistra (n : Naturale) :
    somma uno n = succ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rw [ih]

theorem somma_due_sinistra (n : Naturale) :
    somma due n = succ (succ n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rw [ih]

theorem somma_con_uno_assoc (m n : Naturale) :
    somma (somma m uno) n = somma m (somma uno n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [somma_succ_destra (somma m uno) n]
      rw [somma_succ_destra uno n]
      rw [somma_succ_destra m (somma uno n)]
      rw [ih]

theorem doppio_somma_uno (n : Naturale) :
    doppio (somma uno n) = somma due (doppio n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [somma_succ_destra]
      rw [doppio]
      rw [doppio]
      rw [somma_succ_destra]
      rw [somma_succ_destra]
      rw [ih]

theorem prodotto_uno_sinistra (n : Naturale) :
    prodotto uno n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold prodotto
      rw [ih]
      rw [somma_uno_sinistra]

example (n : Naturale) : somma uno n = succ n := by
  simp only [somma_uno_sinistra]

end Course.Shared.Lecture06.IT.Solutions
