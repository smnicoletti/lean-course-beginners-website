/-!
# Esercizi, Lezione 6

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.IT.Exercises

-- ============================================================
-- IL TIPO DEI NATURALI E LA SOMMA
-- ============================================================

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

-- ============================================================
-- DEFINIRE LA MOLTIPLICAZIONE
-- ============================================================

-- 1. Definire `prodotto` per ricorsione sul secondo argomento.
-- Scegliere le due righe della definizione guardando al significato della
-- moltiplicazione come somma ripetuta.
def prodotto (m n : Naturale) : Naturale :=
  match n with
  | zero => sorry
  | succ n => sorry

-- 2. Dopo avere definito `prodotto`, queste due uguaglianze devono chiudersi
-- con `rfl`.
theorem prodotto_zero_destra (m : Naturale) :
    prodotto m zero = zero := by
  sorry

theorem prodotto_succ_destra (m n : Naturale) :
    prodotto m (succ n) = somma m (prodotto m n) := by
  sorry

-- ============================================================
-- COMPUTAZIONE E RISCRITTURA
-- ============================================================

-- 3. Dimostrare il seguente enunciato.
theorem somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  sorry

-- 4. Data un'uguaglianza `h : a = b`, riscrivere il primo argomento della
-- somma e concludere per computazione.
theorem riscrivi_primo_argomento
    (a b : Naturale)
    (h : a = b) :
    somma a zero = b := by
  sorry

-- ============================================================
-- INDUZIONE SULLA SOMMA
-- ============================================================

-- 5. Dimostrare per induzione che aggiungere uno a sinistra produce il
-- successore del naturale dato.
theorem somma_uno_sinistra (n : Naturale) :
    somma uno n = succ n := by
  sorry

-- 6. Dimostrare per induzione l'analogo risultato per due.
theorem somma_due_sinistra (n : Naturale) :
    somma due n = succ (succ n) := by
  sorry

-- 7. Dimostrare questa particolare forma di associatività. Scegliere la
-- variabile d'induzione guardando le somme che devono ridursi.
theorem somma_con_uno_assoc (m n : Naturale) :
    somma (somma m uno) n = somma m (somma uno n) := by
  sorry

-- 8. Combinare somma e doppio in una dimostrazione per induzione.
theorem doppio_somma_uno (n : Naturale) :
    doppio (somma uno n) = somma due (doppio n) := by
  sorry

-- ============================================================
-- INDUZIONE SULLA MOLTIPLICAZIONE E SEMPLIFICAZIONE
-- ============================================================

-- 9. Dopo avere completato `prodotto`, dimostrare per induzione che uno
-- moltiplicato per ogni naturale restituisce quel naturale.
theorem prodotto_uno_sinistra (n : Naturale) :
    prodotto uno n = n := by
  sorry

-- 10. Usare `simp only` per chiudere il goal seguente.
example (n : Naturale) : somma uno n = succ n := by
  sorry

end Course.Shared.Lecture06.IT.Exercises
