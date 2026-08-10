/-!
# Esercizi, Lezione 4

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Sostituire ogni `sorry` con una proposizione o una prova.
-/

namespace Course.Shared.Lecture04.IT.Exercises

section RiduzioneAllAssurdo

example (Studio SuperoEsame : Prop)
    (hNonStudioNonSupero : ¬Studio → ¬SuperoEsame)
    (hSuperoEsame : SuperoEsame) :
    Studio := by
  sorry

end RiduzioneAllAssurdo

section FormalizzazioneConVocabolario

variable (Cosa : Type)
variable (Poetessa Musicista Curiosa Studiosa Stanca : Cosa → Prop)
variable (Scrive Suona Ascolta : Cosa → Prop)

-- 1. Ogni poetessa scrive.
#check sorry
-- 2. Qualche musicista suona.
#check sorry
-- 3. Ogni musicista curiosa ascolta.
#check sorry
-- 4. Esiste una poetessa che scrive e ascolta.
#check sorry
-- 5. Ogni studiosa scrive oppure ascolta.
#check sorry
-- 6. Nessuna musicista stanca suona.
#check sorry
-- 7. Esiste una poetessa che non è stanca.
#check sorry
-- 8. Ogni poetessa scrive se e solo se ascolta.
#check sorry

end FormalizzazioneConVocabolario

section FormalizzazioneAutonoma

-- Per ogni enunciato, dichiarare `Cosa`, i predicati unari necessari e la
-- formalizzazione con `#check`.
-- 1. Ogni astronoma osserva.
-- 2. Qualche cuoca sperimenta e assaggia.
-- 3. Ogni atleta si allena oppure riposa.
-- 4. Nessuna bibliotecaria distratta cataloga.
-- 5. Esiste una pittrice che espone ma non vende.
-- 6. Ogni botanica classifica se e solo se studia.

end FormalizzazioneAutonoma

end Course.Shared.Lecture04.IT.Exercises
