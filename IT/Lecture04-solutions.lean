/-!
# Soluzioni, Lezione 4

Autore: Stefano M. Nicoletti
Sito web: https://leancourse.stefanonicoletti.com/

Sostituire ogni `sorry` con una proposizione o una prova.
-/

namespace Course.Shared.Lecture04.IT.Solutions

section RiduzioneAllAssurdo

example (Studio SuperoEsame : Prop)
    (hNonStudioNonSupero : ¬Studio → ¬SuperoEsame)
    (hSuperoEsame : SuperoEsame) :
    Studio := by
  apply Classical.byContradiction
  intro hNonStudio
  have hNonSuperoEsame := hNonStudioNonSupero hNonStudio
  exact hNonSuperoEsame hSuperoEsame

end RiduzioneAllAssurdo

section FormalizzazioneConVocabolario

variable (Cosa : Type)
variable (Poetessa Musicista Curiosa Studiosa Stanca : Cosa → Prop)
variable (Scrive Suona Ascolta : Cosa → Prop)

-- 1. Ogni poetessa scrive.
#check ∀ x : Cosa, Poetessa x → Scrive x
-- 2. Qualche musicista suona.
#check ∃ x : Cosa, Musicista x ∧ Suona x
-- 3. Ogni musicista curiosa ascolta.
#check ∀ x : Cosa, Musicista x → Curiosa x → Ascolta x
-- 4. Esiste una poetessa che scrive e ascolta.
#check ∃ x : Cosa, Poetessa x ∧ Scrive x ∧ Ascolta x
-- 5. Ogni studiosa scrive oppure ascolta.
#check ∀ x : Cosa, Studiosa x → Scrive x ∨ Ascolta x
-- 6. Nessuna musicista stanca suona.
#check ∀ x : Cosa, Musicista x → Stanca x → ¬Suona x
-- 7. Esiste una poetessa che non è stanca.
#check ∃ x : Cosa, Poetessa x ∧ ¬Stanca x
-- 8. Ogni poetessa scrive se e solo se ascolta.
#check ∀ x : Cosa, Poetessa x → (Scrive x ↔ Ascolta x)

end FormalizzazioneConVocabolario

section FormalizzazioneAutonoma

variable (Cosa : Type)
variable (Astronoma Osserva Cuoca Sperimenta Assaggia : Cosa → Prop)
variable (Atleta SiAllena Riposa Bibliotecaria Distratta Cataloga : Cosa → Prop)
variable (Pittrice Espone Vende Botanica Classifica Studia : Cosa → Prop)
-- 1. Ogni astronoma osserva.
#check ∀ x : Cosa, Astronoma x → Osserva x
-- 2. Qualche cuoca sperimenta e assaggia.
#check ∃ x : Cosa, Cuoca x ∧ Sperimenta x ∧ Assaggia x
-- 3. Ogni atleta si allena oppure riposa.
#check ∀ x : Cosa, Atleta x → SiAllena x ∨ Riposa x
-- 4. Nessuna bibliotecaria distratta cataloga.
#check ∀ x : Cosa, Bibliotecaria x → Distratta x → ¬Cataloga x
-- 5. Esiste una pittrice che espone ma non vende.
#check ∃ x : Cosa, Pittrice x ∧ Espone x ∧ ¬Vende x
-- 6. Ogni botanica classifica se e solo se studia.
#check ∀ x : Cosa, Botanica x → (Classifica x ↔ Studia x)

end FormalizzazioneAutonoma

end Course.Shared.Lecture04.IT.Solutions
