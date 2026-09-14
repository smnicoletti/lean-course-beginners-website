/-!
# Lezione 6: Tipi induttivi, ricorsione e induzione

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/
-/

namespace Course.Shared.Lecture06.IT.Classroom

-- ============================================================
-- DAI TIPI ASTRATTI AI TIPI INDUTTIVI
-- ============================================================

-- Nelle lezioni precedenti dichiaravamo `Cosa : Type`, senza specificare
-- quali valori appartenessero al tipo o come fossero costruiti.
-- Un tipo induttivo elenca invece tutti i modi in cui possiamo costruire
-- i suoi valori. Questi modi si chiamano costruttori.
inductive Semaforo where
  | rosso
  | giallo
  | verde

#check Semaforo
#check Semaforo.rosso
#check Semaforo.giallo
#check Semaforo.verde

-- Il pattern matching definisce separatamente il risultato della funzione
-- per ciascun costruttore. Qui recuperiamo anche l'idea di predicato:
-- `SiDeveFermare s` è una proposizione che dipende dal semaforo `s`.
def SiDeveFermare : Semaforo → Prop
  | .rosso => True
  | .giallo => True
  | .verde => False


-- Vogliamo dimostrare che ogni semaforo ha uno dei tre colori dichiarati.
-- `cases s` considera tutti i modi in cui `s` può essere stato costruito.
theorem lecture06_semaforo_ha_un_colore (s : Semaforo) :
    s = .rosso ∨ s = .giallo ∨ s = .verde := by
  cases s with
  | rosso =>
      apply Or.inl
      rfl
  | giallo =>
      apply Or.inr
      apply Or.inl
      rfl
  | verde =>
      apply Or.inr
      apply Or.inr
      rfl

-- ============================================================
-- COSTRUIAMO I NOSTRI NUMERI NATURALI
-- ============================================================

-- `zero` costruisce un naturale senza richiedere argomenti.
-- `succ` costruisce un nuovo naturale a partire da un naturale già costruito.
-- Non esistono altri modi di costruire un valore di tipo `Naturale`.
inductive Naturale where
  | zero
  | succ (n : Naturale)

open Naturale

-- Costruiamo i primi naturali senza usare i numerali di Lean.
def uno : Naturale := succ zero
def due : Naturale := succ uno
def tre : Naturale := succ due

#check zero
#check succ
#check uno
#check due
#check tre

-- ============================================================
-- DEFINIZIONI RICORSIVE
-- ============================================================

-- Una definizione ricorsiva segue i costruttori del dato.
-- La somma ricorre sul secondo argomento:
-- aggiungere zero non cambia il primo argomento.
-- aggiungere un successore produce il successore della somma precedente.
-- Una formulazione equivalente mette in evidenza prima il solo argomento fisso:
--
-- def somma (m : Naturale) : Naturale → Naturale
--   | zero => m
--   | succ n => succ (somma m n)
--
-- Qui preferiamo nominare subito entrambi gli argomenti e usare `match n with`
-- per mostrare separatamente che la ricorsione avviene sul secondo.
def somma (m n : Naturale) : Naturale :=
  match n with
  | zero => m
  | succ n => succ (somma m n)

-- Anche `doppio` segue i due costruttori di `Naturale`.
-- Nel secondo caso la chiamata ricorsiva usa il naturale più piccolo `n`.
def doppio (n : Naturale) : Naturale :=
  match n with
  | zero => zero
  | succ n => succ (succ (doppio n))

-- Verifichiamo due computazioni concrete.
example : somma uno uno = due := by
  rfl

example : doppio uno = due := by
  rfl

-- ============================================================
-- UGUAGLIANZA DEFINIZIONALE: RFL E UNFOLD
-- ============================================================

-- Queste uguaglianze seguono direttamente dalle equazioni con cui abbiamo
-- definito `somma` e `doppio`. Lean calcola entrambi i lati fino alla stessa
-- espressione. Per questo `rfl` è sufficiente.

theorem lecture06_somma_zero_destra (m : Naturale) :
    somma m zero = m := by
  rfl

theorem lecture06_somma_succ_destra (m n : Naturale) :
    somma m (succ n) = succ (somma m n) := by
  rfl

-- Nei primi due nomi, "destra" indica che `zero` o `succ n` compaiono come
-- secondo argomento di `somma`, cioè a destra. È proprio l'argomento analizzato
-- da `match n with`, quindi queste uguaglianze seguono subito dalla definizione.
-- Le corrispondenti proprietà con `zero` o `succ` a sinistra non si riducono
-- direttamente: le dimostreremo più avanti per induzione.

theorem lecture06_doppio_succ (n : Naturale) :
    doppio (succ n) = succ (succ (doppio n)) := by
  rfl

-- `unfold` apre esplicitamente una definizione nel goal.
-- È utile per vedere la computazione che `rfl` può eseguire automaticamente.
example : doppio uno = due := by
  unfold doppio
  unfold uno due
  rfl

-- ============================================================
-- RISCRIVERE CON UN'UGUAGLIANZA
-- ============================================================

-- Vogliamo dimostrare `somma a zero = b`, data l'assunzione `h : a = b`.
-- `rw [h]` sostituisce `a` con `b`. Poi il lato sinistro si riduce a `b`.
theorem lecture06_rw_avanti
    (a b : Naturale)
    (h : a = b) :
    somma a zero = b := by
  -- Sostituiamo `a` con `b`. Il goal diventa `somma b zero = b`.
  rw [h]
  -- La definizione di `somma` riduce ora il lato sinistro a `b`.
  rfl

-- La freccia verso sinistra usa l'uguaglianza nella direzione opposta:
-- sostituisce `b` con `a`.
theorem lecture06_rw_indietro
    (a b : Naturale)
    (h : a = b) :
    somma b zero = a := by
  -- Usiamo `h` al contrario: sostituiamo `b` con `a`.
  rw [← h]
  -- Rimane `somma a zero = a`, che segue dalla definizione.
  rfl

-- ============================================================
-- INDUZIONE
-- ============================================================

-- `somma m zero = m` si riduce perché `somma` ricorre sul secondo argomento.
-- `somma zero n = n` non può invece ridursi finché `n` è sconosciuto.
-- Dimostriamo il secondo enunciato per induzione su `n`.
--
-- Come scegliamo la variabile d'induzione?
-- 1. Guardiamo quale definizione non permette ancora di ridurre il goal: qui `somma`.
-- 2. Guardiamo quale argomento viene analizzato dai casi della definizione:
--    `somma` distingue `zero` e `succ n` nel secondo argomento.
-- 3. Facciamo induzione sulla variabile che occupa quella posizione: qui `n`.
-- Nel passo `succ`, l'ipotesi induttiva riguarderà così la chiamata
-- ricorsiva `somma zero n` che compare dopo avere aperto la definizione.
--
-- Nel caso base dimostriamo la proprietà per `zero`.
-- Nel passo induttivo `ih` assume la proprietà per `n`. Dobbiamo dimostrarla
-- per `succ n`. Usiamo esplicitamente `rw [ih]`.
theorem lecture06_zero_somma (n : Naturale) :
    somma zero n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      -- Apriamo il caso successore: il goal contiene `somma zero n`.
      unfold somma
      -- Sostituiamo `somma zero n` con `n` usando l'ipotesi induttiva.
      rewrite [ih] -- Vediamo l'effetto esplicitamente
      rfl

end Course.Shared.Lecture06.IT.Classroom
