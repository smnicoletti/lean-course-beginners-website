/-!
# Soluzioni, Lezione 7: induzione, semplificazione e verifica del software

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

end Course.Shared.Lecture07.IT.Solutions
