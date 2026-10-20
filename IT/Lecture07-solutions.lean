/-!
# Soluzioni, Lezione 7: induzione e semplificazione

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture07.IT.Solutions

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

section SemplificazioneLocale

attribute [local simp] somma_uno_sinistra

example (n : Naturale) : somma uno n = succ n := by
  simp

end SemplificazioneLocale

theorem somma_assoc (a b c : Naturale) :
    somma (somma a b) c = somma a (somma b c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      rw [somma_succ_destra]
      rw [somma_succ_destra]
      rw [somma_succ_destra]
      rw [ih]

theorem zero_somma (n : Naturale) : somma zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rw [ih]

theorem succ_somma (m n : Naturale) :
    somma (succ m) n = succ (somma m n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      unfold somma
      rw [ih]

theorem somma_comm (a b : Naturale) :
    somma a b = somma b a := by
  induction b with
  | zero =>
      rw [zero_somma]
      rfl
  | succ b ih =>
      rw [somma_succ_destra]
      rw [succ_somma]
      rw [ih]

theorem doppio_succ (n : Naturale) :
    doppio (succ n) = succ (succ (doppio n)) := by
  rfl

theorem doppio_somma (m n : Naturale) :
    doppio (somma m n) = somma (doppio m) (doppio n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [somma_succ_destra]
      rw [doppio_succ]
      rw [doppio_succ]
      rw [somma_succ_destra]
      rw [somma_succ_destra]
      rw [ih]

end Course.Shared.Lecture07.IT.Solutions
